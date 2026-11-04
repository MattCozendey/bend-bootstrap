# S2 handoff: heap (B3), image, routines (B4), Inv

Branch `w/s2` off `feature/redesign` 9daf8f5, with `w/s1` merged (final head 4f3ddcc, merge e90ef57).
Worktree `C:\Users\mathe\source\repos\bb-wt\s2`. Not pushed, not merged. Statement decisions and the
smoke results: `s2-notes.md`. WSL mirror for checks: `~/wt/s2` (`~/wt/s2gate.sh [-c] NAME...`
rsyncs the worktree, then gates `Compiler/Machine/NAME.bend`; `-c`: bend2 only).

## Files (src/Compiler/Machine/)

| File | What | Holes |
|---|---|---|
| `heap/spec.bend` | Cx, Rt{c,d,t}, Ch; Fd/Tg/Qn/Fl/Fv; Ptrs; V.tm (checked view), V.at, V.cells, V.kid, V.tag, V.chk; Agree; ImgOK; Part, Fix, Room, Cnt, Clo, Rts, Frs, Chs, Cov, H; V.Live, V.Held; 16 laws | (laws) |
| `heap/view.bend` | view.* and agree.* | 14 `?TODO` |
| `heap/count.bend` | h.set, h.live | 2 |
| `image/spec.bend` | Cx.of (Cx.terms, Cx.pre), Cells.bytes, St0, Start (Bool), ImgOK.agree/out/tbl/ref; 6 laws | (laws) |
| `image/impl.bend` | img.* | 6 |
| `routines/spec.bend` | Same, Kept, Shrunk, Ev/Evs, Alloc.st, Make.st, Release.st, Nth/Nth.st, Fr.header, Push.rts, Swap.ok, Arg.header, Node.ok, Copy.src/depth/budget, Walk.budget/res/post, Out.end/budget, Input.budget, Mode0, **Inv**; 18 laws | (laws) |
| `routines/prims.bend` | alloc, make, release, inc, push, pop, swap, one, h.node, h.arg | 10 |
| `routines/nth.bend`, `dec.bend`, `copy.bend`, `walk.bend`, `out.bend`, `input.bend` | nth; dec, release_arg, release_all; copy; walk; out; input | 1, 3, 1, 1, 1, 1 |
| `s2_smoke.bend` | computed checks (outside main's closure; delete in P5) | 0 |

Total: 40 law holes (one `?TODO` def each). Nothing proven yet. Proof files import logic/impl,
header/impl, canon/impl, am/impl and the S2 proof files below them (bend2 rejects a use of an
unfilled law). `s1stub/` was replaced by S1's files (deleted).

## Law headers (bodies in the spec files)

heap/spec.bend (alias `Hp`; defs `Hp.V.tm`, `Hp.H`, ...):
- `view.frame` (g,x,m,m2,c,d; Agree(V.cells(g,m,c),m,m2)) ⊢ V.tm(g,x,m2,c,d) = V.tm(g,x,m,c,d)
- `view.more` (g,h,..; V.tm(g..)=Some t) ⊢ V.tm(g+h..) = Some t
- `view.deeper` (fv < 524287, fv ≤ d, V.tm(..,d)=Some t) ⊢ V.tm(..,d+k) = Some(shift(t,k,d))
- `view.static` (STATIC c, V.tm(..,d)=Some t) ⊢ V.tm(..,e) = Some t
- `view.canon` (fv < max, fv ≤ d, read t at d) ⊢ Canon.is_at(t,d)
- `view.closed` (STATIC, fv < max, fv ≤ k, read t) ⊢ Term.closed(t,k)
- `view.chk` (read t at d) ⊢ V.chk(x,m,c,d,t); `view.tag` ⊢ Tg(m,c) = V.tag(t)
- `view.kid` (V.tm(1+g..)=Some t, field k in Tbl.mask(tag)) ⊢ V.tm(g,x,m,Fd(k,m,c), d+Tbl.bind(tag,k)) = V.kid(t,k)
- `agree.store` (o ∉ cs), `agree.store1` (field 1), `agree.put` (whole cell, o ∉ cs), `agree.refl`, `agree.trans`
- `h.set` (H, r < 53, r ∉ {free, sp}) ⊢ H after St.set(st,r,v)
- `h.live` (H(x,st,L,..)) ⊢ H(x,st,V.Live(st),..)

image/spec.bend (alias `I`): `img.start` (Book.read p = ds, Img.small, Start) ⊢ ImgOK(Cx.of(ds,k,first), loaded image);
`img.frame` (ImgOK m, ImgOK.agree(x,m,m2)) ⊢ ImgOK m2; `img.store` (ImgOK.out(x,o,k)) and `img.put` (o > im) ⊢ ImgOK.agree after the store;
`img.table` (ImgOK, t < 19) ⊢ ImgOK.tbl(m,t); `img.ref` (ImgOK) ⊢ ImgOK.ref(x,m,k).

routines/spec.bend (alias `R`), each `Lg.Tot(code, st, budget, Q, Lg.No)`:
- exact: `alloc.spec` ⊢ st2 = Alloc.st(st,r); `make.spec` (Evs([h,a,b,c],..,[r,free]) = [hv,av,bv,cv]) ⊢ st2 = Make.st(st,r,Cell{hv,1,av,bv,cv});
  `release.spec` ⊢ Release.st(st,c); `nth.spec` (Chs([Ch{ce,as}]), t2 = ce, t1 = j < |as|) ⊢ Nth.st(st, Nth(j,m,ce))
- H-level: `inc.spec` (Held c at d, fv ≤ d) ⊢ H with Rt{c,d,t} more ∧ Kept(L,[]);
  `dec.spec` (H with Rt{c,d,t} first, r ∉ dec.scr) ⊢ ∃L2. H without it ∧ Kept(L2, dec.scr) ∧ Shrunk(L2,L);
  `push.spec` (H with Push.rts(fr,ca,cb,rs), Evs([h,a,b]) = [Fr.header(fr),ca,cb]) ⊢ ∃L2. H with fr on top;
  `pop.spec` (H with fr on top) ⊢ ∃L2. H with Push.rts(fr, old fields 2/3 of sp, rs);
  `swap.spec` (focus root v, top fr, h = sp, h's value Fr.header(fr2), Swap.ok) ⊢ H with fr2 on top, focus = old field 2, mode 0;
  `one.spec` (root Rt{c,0,t}) ⊢ ∃n L2. wa = cenv = n, clen = 1, chain Ch{n,[Ag{Q0,False,t}]} first;
  `release_arg.spec` (chain Ch{c, ag::as} first, a holds c) ⊢ ∃L2. chain Ch{old Fd1(c), as};
  `release_all.spec` (chain Ch{c,as} first, l holds c) ⊢ ∃L2. chain gone, l = 0;
  `copy.spec` (chain Ch{ce,es} first, src = Copy.src(wt) holds c, Held(c, Copy.depth(wt), t), |es| ≤ depth or STATIC c, cenv = ce, clen = |es|) ⊢
  ∃n L2. reg n = n, H with Rt{n,0,AM.copy(t,es)}, Kept(L, n::copy.scr), |L2| ≤ |L| + size;
  `walk.spec` (chain Ch{ca,xs} first, wt = tc STATIC image cell reading tt, wargs = ca) ⊢ ∃L2 e2 ys2. Walk.post(.., AM.walk(ds,tt,[],xs));
  `out.spec` (Inv(x,st,AS{True,v,[]})) ⊢ no next; halt k with Out.end(v,k,st2);
  `input.spec` (Book.read, Img.small, Start) ⊢ from St0: Inv(Cx.of(ds,k,first), Mode0(st), AS{False, Program.start(i), []}).
- heap lemmas: `h.node` (new term node over roots ps) and `h.arg` (new argument cell at a chain's head), on Make.st.
- `Inv(x, st, s)` = mode register ∧ H(x, st, V.Live(st), [Rt{focus, 0, s.focus}], s.fs, []).

## For S4 (moves, memory, assembly)

- `round.sim`'s Next(x, AO.next{s2}) can be `R.Inv(x, st2, s2) == True`; Vb(st) = the focus' VALUE flag
  (`Hp.Fl(Lg.St.cells(st), Hp.V.reg(st, Mc.R.focus()), Mc.F.value())`), as s2_smoke's runner uses.
- M.call has no routine law: its loop that moves the arguments left into frames (push the term, release the
  cell) and `release.all(wenv)` are proven inside the call moves; walk.spec gives the chains in front.
- Register writes keep H (`h.set`, not free or sp); routine posts carry `Same`/`Kept` and |L2| bounds.
- Halt 2 posts carry out = [] only for AM; compare output only for status 0 (S3).

## Gates run

- G1: `gate.sh` on heap/spec, image/spec, routines/spec: bend2 only the TODO count; kernel (kdiag3)
  101, 14 and 44 defs, 0 FAIL. Proof files: bend2 only the TODO count (their defs are holes, so no
  kernel check). s2_smoke: bend2 passes (2m20s); kernel run: see the end of this file.
- G5: no lowered def/law/type name of S2's files (basename prefix; all spec.bend files share `spec.`)
  is defined twice in src/ (incl. canon/, am/, S1's shared, logic, header).
- G2/G3: not run (files outside main's closure until S4 imports them).
- s2_smoke kernel run (kdiag3, 57 defs): the 45 small checks (views, refs, table, Start) pass; 12 fail
  with "out of fuel" only (ImgOK on a whole image and the 11 whole runs exceed kdiag3's reduction
  fuel: no verdict, not a refutation). Those 12 stand on bend2's evaluation (2m20s, all pass, and the
  negative controls fail as they should).
