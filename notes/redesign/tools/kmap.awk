# kmap.awk: the lowered (BendTT) names of defs, for kdiag3. Used by g1.sh and gate.sh.
#   awk -f kmap.awk LOWERED_NAMES NAMES
# LOWERED_NAMES: one lowered name per line (`grep -o '^[^ ]* :' X.bendtt | sed 's/ :$//'`).
# NAMES: lines `own <name>` (a def of the lowered file, as written) or `fill <ns> <name>` (a def that
# fills the law <name> of the import <ns>: a path relative to the lowered file's dir, no .bend; the
# lowering renames it to <ns escaped>.<name>, '.' as _2e_ and '/' as _2f_ in the path), each with an
# optional last word `open` (the def still has a ?TODO).
# Prints `<lowered name> <1 if open, else 0>` per line, or `MISSING <name>`.
NR == FNR { L[$0] = 1; n++; all[n] = $0; next }
{
  open = ($NF == "open") ? 1 : 0
  if ($1 == "own") { if ($2 in L) print $2, open; else print "MISSING " $2; next }
  ns = $2; nm = $3; hit = ""
  q = ns; sub(/^\.\//, "", q)
  for (i = 1; i <= n; i++) {
    x = all[i]
    if (length(x) <= length(nm) + 1 || substr(x, length(x) - length(nm)) != "." nm) continue
    p = substr(x, 1, length(x) - length(nm) - 1); gsub(/_2e_/, ".", p); gsub(/_2f_/, "/", p); sub(/^\.\//, "", p)
    if (p == q) { hit = x; break }
  }
  if (hit != "") print hit, open; else print "MISSING " ns "." nm
}
