// mergeq.ts: the merge queue of the redesign's prover lanes (P3). Runs on Windows (bun + git.exe: the
// worktrees' .git files hold Windows paths, and WSL's interop is off), and runs the gate steps in WSL
// (wsl.exe: g1.sh, g3.sh, heavy.sh). Its state is files in reports/redesign/mergeq/, so a lost context
// loses nothing: `status` tells what is queued, running, passed and failed.
//
//   bun mergeq.ts add <branch> [--owner [--g4-done]]   queue a lane (owner: a statement owner's branch:
//                                                      no prover-rule check, G3 always)
//   bun mergeq.ts lane <branch> <file> [<file> ...]    register a lane's own files (paths under src/)
//   bun mergeq.ts check <branch>                       the prover-rule check only (no merge, no gate)
//   bun mergeq.ts run [--dry-run] [--g3 auto|force|skip] [--ff-checked-out] [--target B]
//                                                      gate and land one batch: every queued lane
//   bun mergeq.ts land                                 land the last batch that passed but was not
//                                                      landed (the target was checked out), if the
//                                                      target has not moved since
//   bun mergeq.ts status | result <branch> | drop <branch>
//
// A batch (redesign-plan §5.0, with the coordinator's incremental policy of 2026-11-04):
//   1. per lane: the prover rules (below) on the lane's own changes (from its merge base with the
//      target), then a --no-ff merge into a scratch worktree (bb-wt/mergeq, detached; never a
//      worktree that has the target checked out);
//   2. G1 on each changed .bend file, in parallel (heavy.sh's 3 slots): bend2 on the file, lower, and
//      the kernel (kdiag3) on the changed or added defs only, by name (g1.sh). Results are cached by
//      the text of the file, its import closure and the names, so a rerun gates only what changed;
//   3. G5: no def/law/type name defined in two files of the closure of main.bend and of every .bend
//      under src/Compiler/Machine/ (lane files may be outside main's closure until S4 imports them;
//      only clashes that touch a changed file count); no import of a missing file;
//   a lane that fails 1-3 is dropped (its result file says why) and the batch is merged again
//   without it; then once per batch:
//   4. G2: `bend2 --check-only src/main.bend` loads, and its TODO count equals the ?TODO count of
//      main.bend's import closure (the ledger's count; the result prints the change);
//   5. G3 (milestones, ~12 min) only when the batch can affect them: a lane that is not proof-only,
//      or --g3 force (phase boundaries), or 10 batches / 24 h since the last G3 (safety net). Proof-
//      only: a prover lane that passed the rules and changed only .bend files under
//      src/Compiler/Machine/ other than Machine/impl.bend and */spec.bend;
//   6. land: the target ref moves to the batch's last merge (compare-and-swap on the tip that the
//      batch started from). If a worktree has the target checked out: with --ff-checked-out and that
//      worktree clean, `git merge --ff-only` there; else not landed (`land` later).
// Prover rules (a lane changes only its own files; adapted from deepseek.ts's violation()): no
// deleted file; every item (def, law, type) of the base keeps its header; an item with no ?TODO keeps
// its whole text; no import removed; no new law; no new @unsafe. New defs (and types) may be added
// anywhere; an open def's body may change.

import * as fs from "node:fs";
import * as path from "node:path";
import * as crypto from "node:crypto";

// ---- types ----
type Item = { kind: string; name: string; header: string; text: string; open: boolean };
type Entry = { branch: string; owner: boolean; g4: boolean };
type Change = { status: string; file: string };
type LaneRes = { branch: string; ok: boolean; reasons: string[]; logs: string[]; files: Change[]; proofOnly: boolean; sha: string };
type State = { batch: number; lastG3Batch: number; lastG3At: string; lastG3Commit: string; pending?: { batch: number; target: string; from: string; to: string; lanes: string[] } };

// ---- constants ----
const REPO = "C:/Users/mathe/source/repos/bend-bootstrap";
const SCRATCH = "C:/Users/mathe/source/repos/bb-wt/mergeq";
const BEND = REPO + "/bend";
const TOOLS = path.dirname(import.meta.path).split(path.sep).join("/");
const Q = path.join(TOOLS, "..", "mergeq").split(path.sep).join("/");
const DISTRO = "Ubuntu-24.04";
const G3_EVERY = 10;
const G3_HOURS = 24;
const TODO_LINE = (l: string) => l.includes("?TODO") && !l.trim().startsWith("#");
const ITEM = /^(?:@unsafe\s+)?(def|law|type)\s+([A-Za-z0-9_.]+)/;

// ---- process helpers ----
const sh = (cmd: string[], cwd = REPO): { code: number; out: string } => {
  const p = Bun.spawnSync(cmd, { cwd, stdout: "pipe", stderr: "pipe" });
  return { code: p.exitCode ?? 1, out: p.stdout.toString() + p.stderr.toString() };
};
const git = (args: string[], cwd = REPO) => sh(["git", "-c", "core.autocrlf=false", ...args], cwd);
const gitOk = (args: string[], cwd = REPO): string => {
  const r = git(args, cwd);
  if (r.code !== 0) throw new Error("git " + args.join(" ") + ": " + r.out.trim());
  return r.out.trim();
};
const show = (rev: string, file: string): string | null => {
  const r = git(["show", rev + ":" + file]);
  return r.code === 0 ? r.out : null;
};
const toWsl = (p: string) => p.replace(/\\/g, "/").replace(/^([A-Za-z]):/, (_, d) => "/mnt/" + d.toLowerCase());
const wsl = async (args: string[]): Promise<number> => {
  const p = Bun.spawn(["wsl.exe", "-d", DISTRO, "-e", ...args], { stdout: "ignore", stderr: "ignore" });
  return await p.exited;
};
const now = () => new Date().toISOString().replace("T", " ").slice(0, 19);
const safe = (b: string) => b.replace(/[^A-Za-z0-9._-]/g, "_");

// ---- files of the queue ----
const qf = (n: string) => path.join(Q, n);
const readLines = (n: string) => (fs.existsSync(qf(n)) ? fs.readFileSync(qf(n), "utf8").split("\n").map((l) => l.replace(/#.*$/, "").trim()).filter(Boolean) : []);
const log = (s: string) => fs.appendFileSync(qf("log.txt"), now() + " " + s + "\n");
const getQueue = (): Entry[] => readLines("queue.txt").map((l) => { const [branch, ...fl] = l.split(/\s+/); return { branch: branch!, owner: fl.includes("owner"), g4: fl.includes("g4-done") }; });
const writeQueue = (es: Entry[]) => fs.writeFileSync(qf("queue.txt"), "# pending lanes: <branch> [owner] [g4-done] (mergeq.ts add)\n" + es.map((e) => [e.branch, e.owner ? "owner" : "", e.g4 ? "g4-done" : ""].filter(Boolean).join(" ") + "\n").join(""));
const getLanes = (): Map<string, string[]> => new Map(readLines("lanes.txt").map((l) => { const [b, ...fs_] = l.split(/\s+/); return [b!, fs_.map((f) => "src/" + f.replace(/^src\//, ""))]; }));
const getState = (): State => (fs.existsSync(qf("state.json")) ? JSON.parse(fs.readFileSync(qf("state.json"), "utf8")) : { batch: 0, lastG3Batch: 0, lastG3At: "", lastG3Commit: "" });
const putState = (s: State) => fs.writeFileSync(qf("state.json"), JSON.stringify(s, null, 1) + "\n");

// ---- source items ----
const getItems = (text: string): Map<string, Item> => {
  const lines = text.split("\n");
  const starts = lines.flatMap((l, i) => { const m = ITEM.exec(l); return m ? [{ i, kind: m[1]!, name: m[2]! }] : []; });
  return new Map(starts.map((s, n) => {
    let e = n + 1 < starts.length ? starts[n + 1]!.i : lines.length;
    while (e > s.i + 1 && (lines[e - 1]!.trim() === "" || lines[e - 1]!.startsWith("#"))) e--;
    const body = lines.slice(s.i, e);
    let j = 0;
    if (s.kind === "law") { while (j + 1 < body.length && body[j + 1]!.trim() !== "") j++; }
    else {
      for (let d = 0; j < body.length; j++) {
        const l = body[j]!.replace(/#.*$/, "");
        for (const ch of l) { if ("([{".includes(ch)) d++; else if (")]}".includes(ch)) d--; }
        if (d <= 0 && /:\s*$/.test(l)) break;
      }
    }
    const strip = (xs: string[]) => xs.map((l) => l.replace(/\s+$/, "")).join("\n");
    return [s.kind + " " + s.name, { kind: s.kind, name: s.name, header: strip(body.slice(0, j + 1)), text: strip(body), open: body.some(TODO_LINE) }];
  }));
};
const getImports = (text: string): { path: string; alias: string }[] => {
  const out: { path: string; alias: string }[] = [];
  for (const line of text.split("\n")) {
    const l = line.trim();
    if (l === "" || l.startsWith("#")) continue;
    const m = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?/.exec(l);
    if (!m) break;
    if (m[2]) out.push({ path: m[1]!, alias: m[2] });
  }
  return out;
};

// ---- prover rules ----
const getViolations = (file: string, base: string | null, next: string | null): string[] => {
  if (next === null) return [file + ": deleted (a lane never deletes a file)"];
  const b = getItems(base ?? ""), n = getItems(next), out: string[] = [];
  for (const [k, it] of b) {
    const m = n.get(k);
    if (!m) out.push(file + ": " + k + " is gone (statements are frozen)");
    else if (m.header !== it.header) out.push(file + ": the statement (header) of " + k + " changed");
    else if (!it.open && m.text !== it.text) out.push(file + ": " + k + " has no ?TODO, so it is frozen (body included); add a new def instead");
  }
  for (const [k, it] of n) if (!b.has(k) && it.kind === "law") out.push(file + ": new law " + it.name + " (a law is a claim without proof; provers add defs only)");
  const im = new Set(getImports(next).map((i) => i.path + " as " + i.alias));
  for (const i of getImports(base ?? "")) if (!im.has(i.path + " as " + i.alias)) out.push(file + ": the import " + i.path + " as " + i.alias + " was removed");
  const unsafe = (t: string) => (t.match(/@unsafe/g) ?? []).length;
  if (unsafe(next) > unsafe(base ?? "")) out.push(file + ": new @unsafe");
  return out;
};
const isProofFile = (f: string) => f.startsWith("src/Compiler/Machine/") && f.endsWith(".bend") && f !== "src/Compiler/Machine/impl.bend" && !f.endsWith("/spec.bend");
const getChanges = (from: string, to: string): Change[] =>
  gitOk(["diff", "--no-renames", "--name-status", from, to]).split("\n").filter(Boolean).map((l) => { const [status, file] = l.split("\t"); return { status: status!, file: file! }; });
const checkLane = (e: Entry, target: string): LaneRes => {
  const res: LaneRes = { branch: e.branch, ok: true, reasons: [], logs: [], files: [], proofOnly: false, sha: "" };
  const sha = git(["rev-parse", "--verify", "-q", e.branch + "^{commit}"]);
  if (sha.code !== 0) return { ...res, ok: false, reasons: ["no branch " + e.branch] };
  res.sha = sha.out.trim();
  const base = gitOk(["merge-base", res.sha, target]);
  res.files = getChanges(base, res.sha);
  if (res.files.length === 0) return { ...res, ok: false, reasons: ["nothing to merge (the lane has no change of its own)"] };
  if (e.owner) {
    const impl = res.files.some((c) => c.file === "src/Compiler/Machine/impl.bend");
    if (impl && !e.g4) return { ...res, ok: false, reasons: ["changes Machine/impl.bend: G4 (run.ts TRUSTED=1 FRESH=1, the layer-A checks) first, by hand; then add with --owner --g4-done"] };
    return res;
  }
  const own = getLanes().get(e.branch);
  const others = new Map([...getLanes()].filter(([b]) => b !== e.branch).flatMap(([b, fs_]) => fs_.map((f) => [f, b] as const)));
  for (const c of res.files) {
    if (own ? !own.includes(c.file) : !isProofFile(c.file)) res.reasons.push(c.file + ": not one of the lane's own files (" + (own ? own.join(", ") : "unregistered lane: only proof files under src/Compiler/Machine/, not impl.bend or a spec.bend") + ")");
    else if (!own && others.has(c.file)) res.reasons.push(c.file + ": registered to lane " + others.get(c.file));
    else if (c.file.endsWith(".bend")) res.reasons.push(...getViolations(c.file, show(base, c.file), c.status === "D" ? null : show(res.sha, c.file)));
  }
  if (!own) res.logs.push("note: lane not registered in lanes.txt (mergeq.ts lane " + e.branch + " <files>)");
  res.ok = res.reasons.length === 0;
  res.proofOnly = res.ok && res.files.every((c) => isProofFile(c.file));
  return res;
};

// ---- closures, names, holes ----
type Reader = (f: string) => string | null;
const resolveImport = (from: string, imp: string) => path.posix.normalize(path.posix.join(path.posix.dirname(from), imp));
const getClosure = (roots: string[], read: Reader): Map<string, string | null> => {
  const seen = new Map<string, string | null>();
  const go = (f: string) => {
    if (seen.has(f)) return;
    const t = read(f);
    seen.set(f, t);
    if (t !== null) for (const i of getImports(t)) if (i.path.endsWith(".bend")) go(resolveImport(f, i.path));
  };
  roots.forEach(go);
  return seen;
};
const countTodos = (cl: Map<string, string | null>) => [...cl.values()].reduce((n, t) => n + (t ? t.split("\n").filter(TODO_LINE).length : 0), 0);
// the names a file defines (not its law fills: `def A.x` with A an import's alias)
const getDefined = (t: string): string[] => {
  const al = new Set(getImports(t).map((i) => i.alias));
  return [...getItems(t).values()].filter((it) => !(it.kind === "def" && al.has(it.name.split(".")[0]!) && it.name.includes("."))).map((it) => it.name);
};
const getG5 = (cl: Map<string, string | null>, changed: Set<string>): { file: string; msg: string }[] => {
  const out: { file: string; msg: string }[] = [];
  const where = new Map<string, string[]>();
  for (const [f, t] of cl) {
    if (t === null) continue;
    for (const nm of getDefined(t)) where.set(nm, [...(where.get(nm) ?? []), f]);
    for (const i of getImports(t)) if (i.path.endsWith(".bend") && cl.get(resolveImport(f, i.path)) === null) out.push({ file: f, msg: f + " imports a missing file: " + i.path });
  }
  for (const [nm, fs_] of where) if (fs_.length > 1 && fs_.some((f) => changed.has(f))) for (const f of fs_.filter((f) => changed.has(f))) out.push({ file: f, msg: "the name " + nm + " is defined in " + fs_.join(" and ") });
  return out;
};
// the defs of a file to kernel-check: changed or added since the base, as g1.sh names them
const getKernelNames = (file: string, base: string | null, next: string): string => {
  const b = getItems(base ?? ""), al = new Map(getImports(next).map((i) => [i.alias, i.path.replace(/\.bend$/, "")] as const));
  return [...getItems(next).values()].filter((it) => it.kind === "def" && b.get("def " + it.name)?.text !== it.text).map((it) => {
    const a = it.name.split(".")[0]!;
    const head = it.name.includes(".") && al.has(a) ? "fill " + path.posix.normalize(al.get(a)!) + " " + it.name.slice(a.length + 1) : "own " + it.name;
    return head + (it.open ? " open" : "") + "\n";
  }).join("");
};

// ---- the scratch worktree ----
const prepareScratch = (target: string) => {
  if (!fs.existsSync(SCRATCH + "/.git")) {
    gitOk(["worktree", "add", "--detach", SCRATCH, target]);
    fs.rmSync(SCRATCH + "/bend", { recursive: true, force: true });
    sh(["cmd", "/c", "mklink", "/J", SCRATCH.replace(/\//g, "\\") + "\\bend", BEND.replace(/\//g, "\\")]);
  }
  gitOk(["checkout", "-q", "--detach", "-f", target], SCRATCH);
  gitOk(["reset", "-q", "--hard", target], SCRATCH);
  gitOk(["clean", "-fdq", "-e", "bend"], SCRATCH);
};
const mergeLanes = (lanes: LaneRes[], batch: number): LaneRes[] => lanes.filter((l) => {
  const r = git(["-c", "user.email=mpereira@blueboltsolutions.com", "merge", "--no-ff", "--no-edit", "-m", "Merge " + l.branch + " (mergeq batch " + batch + ")", l.sha], SCRATCH);
  if (r.code === 0) return true;
  git(["merge", "--abort"], SCRATCH);
  l.ok = false; l.reasons.push("merge conflict with the target or an earlier lane of the batch:\n" + r.out.trim().slice(0, 2000));
  return false;
});

// ---- gates ----
const g1Cache = (): Record<string, string> => (fs.existsSync(qf("work/g1-cache.json")) ? JSON.parse(fs.readFileSync(qf("work/g1-cache.json"), "utf8")) : {});
const runG1 = async (files: string[], target: string, read: Reader): Promise<Map<string, { ok: boolean; log: string }>> => {
  fs.mkdirSync(qf("work"), { recursive: true });
  const cache = g1Cache(), out = new Map<string, { ok: boolean; log: string }>();
  await Promise.all(files.map(async (f) => {
    const text = read(f)!, names = getKernelNames(f, show(target, f), text);
    const cl = getClosure([f], read);
    const key = crypto.createHash("sha256").update(names + [...cl].map(([k, v]) => k + "\0" + v).join("\0")).digest("hex");
    if (cache[key]) { out.set(f, { ok: true, log: cache[key] + " (cached)" }); return; }
    const tag = safe(f), nf = qf("work/" + tag + ".names"), lf = qf("work/" + tag + ".g1.log");
    fs.writeFileSync(nf, names);
    fs.rmSync(lf, { force: true });
    const code = await wsl([toWsl(TOOLS + "/g1.sh"), toWsl(SCRATCH), f.replace(/^src\//, ""), toWsl(nf), toWsl(lf)]);
    const lg = fs.existsSync(lf) ? fs.readFileSync(lf, "utf8") : "g1.sh wrote no log (exit " + code + ")";
    const ok = code === 0 && /\nG1 PASS/.test("\n" + lg);
    if (ok) cache[key] = lg.trim().split("\n").at(-1)!;
    out.set(f, { ok, log: lg });
  }));
  fs.writeFileSync(qf("work/g1-cache.json"), JSON.stringify(cache));
  return out;
};
const runG2 = async (expect: number): Promise<{ ok: boolean; log: string }> => {
  const lf = qf("work/g2.log");
  fs.rmSync(lf, { force: true });
  const cmd = "export PATH=$HOME/.bun/bin:$PATH; cd " + toWsl(SCRATCH) + "/src && ~/lead/heavy.sh timeout 3600 bun ../bend/bend2/main.ts main.bend --check-only 2>&1 | grep -v '^\\s*$' | cut -c1-400 | head -60 > " + toWsl(lf);
  await wsl(["bash", "-c", cmd]);
  const lg = fs.existsSync(lf) ? fs.readFileSync(lf, "utf8") : "";
  const other = lg.split("\n").filter((l) => l && !/^(SOME PROOFS FAIL|ALL PROOFS CHECK|Error: \d+ TODOs? found\.|The code is incomplete, and not a valid proof yet\.)$/.test(l));
  const n = +(/Error: (\d+) TODOs? found/.exec(lg)?.[1] ?? (/ALL PROOFS CHECK/.test(lg) ? "0" : "-1"));
  const ok = other.length === 0 && n === expect;
  return { ok, log: lg + (ok ? "G2 PASS: main.bend loads, " + n + " TODOs (= the closure's ?TODO count)" : "G2 FAIL: " + (other.length ? "bend2 reports an error" : n + " TODOs, the closure has " + expect)) + "\n" };
};
const runG3 = async (sha: string): Promise<{ ok: boolean; log: string }> => {
  gitOk(["update-ref", "refs/mergeq/candidate", sha]);
  const lf = qf("work/g3.log");
  fs.rmSync(lf, { force: true });
  await wsl([toWsl(TOOLS + "/g3.sh"), "refs/mergeq/candidate", toWsl(lf)]);
  const lg = fs.existsSync(lf) ? fs.readFileSync(lf, "utf8") : "g3.sh wrote no log\n";
  return { ok: /\nG3 PASS\s*$/.test("\n" + lg), log: lg };
};

// ---- landing ----
const checkedOutIn = (branch: string): string | undefined => {
  const wt = gitOk(["worktree", "list", "--porcelain"]).split("\n\n").find((b) => b.includes("\nbranch refs/heads/" + branch));
  return wt ? /^worktree (.*)$/m.exec(wt)?.[1] : undefined;
};
const tryLand = (target: string, from: string, to: string, ffCheckedOut: boolean): string => {
  const wt = checkedOutIn(target);
  if (wt) {
    if (!ffCheckedOut) return "NOT LANDED: " + target + " is checked out in " + wt + " (run `mergeq.ts land` once it is not, or with --ff-checked-out when that worktree is clean)";
    const dirty = gitOk(["status", "--porcelain", "--ignore-submodules=all", "--untracked-files=no"], wt);
    if (dirty) return "NOT LANDED: " + wt + " (which has " + target + ") has uncommitted changes";
    const r = git(["merge", "-q", "--ff-only", to], wt);
    return r.code === 0 ? "LANDED (fast-forward in " + wt + ")" : "NOT LANDED: ff in " + wt + " failed: " + r.out.trim();
  }
  const r = git(["update-ref", "refs/heads/" + target, to, from]);
  return r.code === 0 ? "LANDED" : "NOT LANDED: " + target + " moved during the batch (" + r.out.trim() + "): run again";
};

// ---- commands ----
const writeResult = (l: LaneRes, batch: number, verdict: string, extra: string[]) => {
  fs.mkdirSync(qf("results"), { recursive: true });
  fs.writeFileSync(qf("results/" + safe(l.branch) + ".txt"), ["lane: " + l.branch + " (" + l.sha.slice(0, 10) + ")", "batch: " + batch + " at " + now(), "verdict: " + verdict, "files: " + l.files.map((c) => c.status + " " + c.file).join(", "), "proof-only: " + l.proofOnly, ...(l.reasons.length ? ["", "WHY:", ...l.reasons.map((r) => "- " + r)] : []), ...l.logs, ...extra].join("\n") + "\n");
};
const lock = (): (() => void) => {
  const lf = qf("run.lock");
  if (fs.existsSync(lf)) {
    const o = JSON.parse(fs.readFileSync(lf, "utf8"));
    let alive = false;
    try { process.kill(o.pid, 0); alive = true; } catch {}
    if (alive) { console.error("mergeq: a run is going on (pid " + o.pid + ", since " + o.started + "); see mergeq/log.txt"); process.exit(1); }
    log("stale lock of pid " + o.pid + " removed");
  }
  fs.writeFileSync(lf, JSON.stringify({ pid: process.pid, started: now() }));
  return () => fs.rmSync(lf, { force: true });
};
const commitQueue = (msg: string) => {
  const d = path.join(TOOLS, "..");
  git(["add", "-A", "mergeq"], d);
  git(["-c", "user.email=mpereira@blueboltsolutions.com", "commit", "-qm", "mergeq: " + msg, "--", "mergeq"], d);
};

const run = async (opts: { dry: boolean; g3: string; ff: boolean; target: string }) => {
  const queue = getQueue();
  if (queue.length === 0) { console.log("mergeq: the queue is empty"); return; }
  const unlock = lock();
  try {
    const st = getState(), batch = st.batch + 1, target = opts.target;
    const T = gitOk(["rev-parse", target]);
    const out: string[] = [];
    const say = (s: string) => { out.push(s); console.log(s); };
    say("batch " + batch + " at " + now() + ": " + queue.map((e) => e.branch).join(" ") + " onto " + target + " " + T.slice(0, 10) + (opts.dry ? " (dry run)" : ""));
    log("batch " + batch + " start: " + queue.map((e) => e.branch).join(" "));
    const lanes = queue.map((e) => checkLane(e, T));
    for (const l of lanes) say("rules " + l.branch + ": " + (l.ok ? "ok" + (l.proofOnly ? " (proof-only)" : "") : "FAIL\n  " + l.reasons.join("\n  ")));
    const g1Logs = new Map<string, string>();
    let live = lanes.filter((l) => l.ok), merged: LaneRes[] = [], files: Change[] = [];
    const readHead: Reader = (f) => { const p = path.join(SCRATCH, f); return fs.existsSync(p) ? fs.readFileSync(p, "utf8") : null; };
    for (;;) {
      prepareScratch(T);
      merged = mergeLanes(live, batch);
      for (const l of live.filter((x) => !merged.includes(x))) say("merge " + l.branch + ": CONFLICT");
      if (merged.length === 0) break;
      files = getChanges(T, gitOk(["rev-parse", "HEAD"], SCRATCH));
      const bend = files.filter((c) => c.status !== "D" && c.file.startsWith("src/") && c.file.endsWith(".bend")).map((c) => c.file);
      const owner = (f: string) => merged.filter((l) => l.files.some((c) => c.file === f));
      say("G1 on " + bend.length + " file(s): " + bend.join(" "));
      const g1 = await runG1(bend, T, readHead);
      for (const [f, r] of g1) {
        g1Logs.set(f, r.log);
        say("  " + (r.log.trim().split("\n").at(-1) ?? f));
        if (!r.ok) for (const l of owner(f)) { l.ok = false; l.reasons.push("G1 failed on " + f + " (log below)"); l.logs.push("", "== G1 " + f, r.log); }
      }
      const changed = new Set(files.map((c) => c.file));
      const tree = gitOk(["ls-files", "src/Compiler/Machine"], SCRATCH).split("\n").filter((f) => f.endsWith(".bend"));
      const g5 = getG5(getClosure(["src/main.bend", ...tree, ...bend], readHead), changed);
      for (const p of g5) { say("G5: " + p.msg); for (const l of owner(p.file)) { l.ok = false; l.reasons.push("G5: " + p.msg); } }
      if (g5.length === 0) say("G5 PASS");
      const bad = merged.filter((l) => !l.ok);
      if (bad.length === 0) break;
      say("dropping " + bad.map((l) => l.branch).join(" ") + "; merging the batch again");
      live = merged.filter((l) => l.ok);
    }
    const head = merged.length ? gitOk(["rev-parse", "HEAD"], SCRATCH) : T;
    let landed = "", batchFail = "";
    if (merged.length) {
      const exp = countTodos(getClosure(["src/main.bend"], readHead)), was = countTodos(getClosure(["src/main.bend"], (f) => show(T, f)));
      const g2 = await runG2(exp);
      say(g2.log.trim().split("\n").at(-1)! + " (was " + was + " at " + T.slice(0, 10) + "; update holes.md)");
      if (!g2.ok) { batchFail = "G2 failed"; out.push(g2.log); }
      const proofOnly = merged.every((l) => l.proofOnly);
      const since = st.lastG3At ? (Date.now() - Date.parse(st.lastG3At)) / 36e5 : Infinity;
      const due = batch - st.lastG3Batch >= G3_EVERY || since >= G3_HOURS;
      const g3 = opts.g3 === "force" || (opts.g3 === "auto" && (!proofOnly || due));
      if (!batchFail && g3) {
        say("G3 (" + (opts.g3 === "force" ? "forced" : !proofOnly ? "a lane is not proof-only: " + merged.filter((l) => !l.proofOnly).map((l) => l.branch).join(" ") : "safety net: " + (batch - st.lastG3Batch) + " batches / " + since.toFixed(0) + " h since the last") + "), ~12 min ...");
        const r = await runG3(head);
        say(r.ok ? "G3 PASS" : "G3 FAIL");
        out.push(r.log);
        if (r.ok) Object.assign(st, { lastG3Batch: batch, lastG3At: new Date().toISOString(), lastG3Commit: head });
        else batchFail = "G3 failed";
      } else if (!batchFail) say("G3 skipped (" + (opts.g3 === "skip" ? "--g3 skip" : "proof-only batch; last G3 " + (batch - st.lastG3Batch) + " batches ago") + ")");
      if (!batchFail && !opts.dry) {
        landed = tryLand(target, T, head, opts.ff);
        if (landed.startsWith("NOT")) st.pending = { batch, target, from: T, to: head, lanes: merged.map((l) => l.branch) };
        else delete st.pending;
      } else if (opts.dry) landed = "NOT LANDED: dry run (passing head " + head.slice(0, 10) + ")";
      say(batchFail ? "BATCH FAILED: " + batchFail + " (the merged lanes stay queued; see batches/" + batch + ".txt)" : landed + " " + head.slice(0, 10));
    }
    // results; the queue keeps the lanes of a failed batch (G2/G3 cannot name a lane) and the ones not landed
    const keep = new Set<string>();
    for (const l of lanes) {
      const inBatch = merged.includes(l);
      const verdict = !l.ok ? "FAIL" : batchFail ? "HELD (batch " + batchFail + ")" : inBatch ? (landed.startsWith("LANDED") ? "PASS, LANDED in " + target + " at " + head.slice(0, 10) : "PASS, " + landed) : "FAIL";
      if (l.ok && (batchFail || !landed.startsWith("LANDED"))) keep.add(l.branch);
      writeResult(l, batch, verdict, l.ok ? l.files.filter((c) => g1Logs.has(c.file)).map((c) => "G1 " + c.file + ": " + g1Logs.get(c.file)!.trim().split("\n").at(-1)) : []);
    }
    if (!opts.dry) writeQueue(getQueue().filter((e) => keep.has(e.branch) || !lanes.some((l) => l.branch === e.branch)));
    st.batch = batch;
    putState(st);
    fs.mkdirSync(qf("batches"), { recursive: true });
    fs.writeFileSync(qf("batches/" + String(batch).padStart(4, "0") + ".txt"), out.join("\n") + "\n");
    log("batch " + batch + " end: " + (batchFail || landed || "nothing merged"));
    commitQueue("batch " + batch + ": " + (batchFail || landed.split(" (")[0] || "nothing merged"));
  } finally { unlock(); }
};

const status = () => {
  const st = getState();
  console.log("queue (" + qf("queue.txt") + "):\n" + (getQueue().map((e) => "  " + e.branch + (e.owner ? " [owner]" : "")).join("\n") || "  (empty)"));
  if (fs.existsSync(qf("run.lock"))) console.log("RUNNING: " + fs.readFileSync(qf("run.lock"), "utf8"));
  console.log("last batch: " + st.batch + "; last G3: batch " + st.lastG3Batch + " " + st.lastG3At + " " + st.lastG3Commit.slice(0, 10));
  if (st.pending) console.log("PASSED, NOT LANDED: batch " + st.pending.batch + " " + st.pending.to.slice(0, 10) + " (" + st.pending.lanes.join(" ") + "): mergeq.ts land");
  if (fs.existsSync(qf("results"))) for (const f of fs.readdirSync(qf("results")).sort()) { const t = fs.readFileSync(qf("results/" + f), "utf8"); console.log("  " + f.replace(/\.txt$/, "").padEnd(28) + " " + (/^verdict: (.*)$/m.exec(t)?.[1] ?? "?") + "  [" + (/^batch: (\d+)/m.exec(t)?.[1] ?? "") + "]"); }
  console.log("recent log:\n" + (fs.existsSync(qf("log.txt")) ? fs.readFileSync(qf("log.txt"), "utf8").trim().split("\n").slice(-8).map((l) => "  " + l).join("\n") : ""));
};

// ---- side effects ----
fs.mkdirSync(qf("work"), { recursive: true });
if (!fs.existsSync(qf(".gitignore"))) fs.writeFileSync(qf(".gitignore"), "work/\nrun.lock\n");
const [cmd, ...rest] = process.argv.slice(2);
const flagOf = (k: string) => rest.includes("--" + k);
const optOf = (k: string, d: string) => { const i = rest.indexOf("--" + k); return i >= 0 ? rest[i + 1]! : d; };
if (cmd === "add" && rest[0]) {
  if (git(["rev-parse", "--verify", "-q", rest[0] + "^{commit}"]).code !== 0) { console.error("mergeq: no branch " + rest[0]); process.exit(1); }
  writeQueue([...getQueue().filter((e) => e.branch !== rest[0]), { branch: rest[0], owner: flagOf("owner"), g4: flagOf("g4-done") }]);
  log("add " + rest.join(" "));
  console.log("queued " + rest[0] + " (" + getQueue().length + " in the queue)");
} else if (cmd === "drop" && rest[0]) {
  writeQueue(getQueue().filter((e) => e.branch !== rest[0]));
  log("drop " + rest[0]);
} else if (cmd === "lane" && rest.length >= 2) {
  const ls = getLanes();
  ls.set(rest[0]!, rest.slice(1).map((f) => "src/" + f.replace(/^src\//, "")));
  fs.writeFileSync(qf("lanes.txt"), "# <branch> <file under src/> ...: the files a prover lane may change (mergeq.ts lane)\n" + [...ls].map(([b, fs_]) => b + " " + fs_.map((f) => f.replace(/^src\//, "")).join(" ") + "\n").join(""));
  log("lane " + rest.join(" "));
} else if (cmd === "check" && rest[0]) {
  const e = getQueue().find((x) => x.branch === rest[0]) ?? { branch: rest[0], owner: false, g4: false };
  const r = checkLane(e, gitOk(["rev-parse", optOf("target", "feature/redesign")]));
  console.log((r.ok ? "rules ok" + (r.proofOnly ? " (proof-only)" : "") : "RULES FAIL:\n- " + r.reasons.join("\n- ")) + "\nfiles: " + r.files.map((c) => c.status + " " + c.file).join(", ") + (r.logs.length ? "\n" + r.logs.join("\n") : ""));
  process.exit(r.ok ? 0 : 2);
} else if (cmd === "run") {
  await run({ dry: flagOf("dry-run"), g3: optOf("g3", "auto"), ff: flagOf("ff-checked-out"), target: optOf("target", "feature/redesign") });
} else if (cmd === "land") {
  const st = getState();
  if (!st.pending) { console.log("mergeq: nothing to land"); process.exit(0); }
  const unlock = lock();
  try {
    const r = tryLand(st.pending.target, st.pending.from, st.pending.to, flagOf("ff-checked-out"));
    console.log(r);
    log("land batch " + st.pending.batch + ": " + r);
    if (r.startsWith("LANDED")) {
      const done = new Set(st.pending.lanes);
      writeQueue(getQueue().filter((e) => !done.has(e.branch)));
      for (const b of done) { const f = qf("results/" + safe(b) + ".txt"); if (fs.existsSync(f)) fs.writeFileSync(f, fs.readFileSync(f, "utf8").replace(/^verdict: .*$/m, "verdict: PASS, LANDED in " + st.pending.target + " at " + st.pending.to.slice(0, 10))); }
      delete st.pending;
      putState(st);
      commitQueue("land");
    }
  } finally { unlock(); }
} else if (cmd === "status") {
  status();
} else if (cmd === "result" && rest[0]) {
  const f = qf("results/" + safe(rest[0]) + ".txt");
  console.log(fs.existsSync(f) ? fs.readFileSync(f, "utf8") : "no result for " + rest[0]);
} else {
  console.log(fs.readFileSync(import.meta.path, "utf8").split("\n").slice(0, 41).join("\n"));
  process.exit(2);
}
