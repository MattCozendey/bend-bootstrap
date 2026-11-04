#!/bin/bash
# g1.sh WT FILE NAMES LOG: gate G1 (redesign-plan §5.0) on one file, incremental, for mergeq.ts.
#   1. bend2 --check-only FILE: only the TODO count, no other error;
#   2. lower FILE (Shared/lower.ts, holes read as calls);
#   3. kdiag3 (the kernel) on the named defs only: NAMES is a file of lines `own <name>` (a def of
#      FILE) or `fill <ns> <name>` (a def of FILE that fills the law <name> of the import <ns>, a path
#      relative to FILE's dir without .bend; lowered as <ns, escaped>.<name>); `open` at the end of a
#      line: the def still has a ?TODO, so its FAIL is expected. Every name must be found.
# Each heavy step runs through heavy.sh (3 shared slots). Writes LOG; its last line is
# `G1 PASS ...` or `G1 FAIL ...`. Exit 0 on pass, 1 on fail.
export PATH=$HOME/.bun/bin:/usr/local/bin:/usr/bin:/bin
H=~/lead/heavy.sh; WT=$1; F=$2; NAMES=$3; LOG=$4
cd "$WT/src" || { echo "G1 FAIL no $WT/src" > "$LOG"; exit 1; }
tag=$(echo "$WT:$F" | md5sum | cut -c1-12); out=/tmp/g1-$tag.bendtt
exec > "$LOG" 2>&1
fail() { echo "G1 FAIL $F: $*"; rm -f "$out"; exit 1; }
echo "== bend2 --check-only $F"
b=$($H timeout 3600 bun ../bend/bend2/main.ts "$F" --check-only 2>&1 | grep -v '^\s*$' | cut -c1-400)
echo "$b" | head -60
other=$(echo "$b" | grep -v -E '^(SOME PROOFS FAIL|ALL PROOFS CHECK|Error: [0-9]+ TODOs? found\.|The code is incomplete, and not a valid proof yet\.)$')
[ -n "$other" ] && fail "bend2 reports an error (above)"
todos=$(echo "$b" | sed -n 's/^Error: \([0-9]*\) TODOs\{0,1\} found\./\1/p'); todos=${todos:-0}
echo "== lower $F"
$H timeout 3600 bun Shared/lower.ts "$F" "$out" 2>&1 | tail -4
[ -s "$out" ] || fail "lower wrote nothing"
grep -v '^\s*$' "$NAMES" > /dev/null 2>&1 || { echo "G1 PASS $F: bend2 ok ($todos TODOs), no def to kernel-check"; rm -f "$out"; exit 0; }
# map each name to its lowered name
grep -o '^[^ ]* :' "$out" | sed 's/ :$//' > "$out.names"
mapped=$(awk -f "$(dirname "$(readlink -f "$0")")/kmap.awk" "$out.names" "$NAMES")
echo "== names"; echo "$mapped"
miss=$(echo "$mapped" | grep '^MISSING')
[ -n "$miss" ] && fail "not in the lowered book: $(echo $miss)"
names=$(echo "$mapped" | awk '{print $1}'); want=$(echo "$names" | wc -w)
echo "== kernel: $want defs"
k=$($H env LEAN_STACK_SIZE_KB=4194304 ~/kdiag/kdiag3 "$out" $names 2>&1 | grep -E '^(FAIL|DONE|SLOW|PARSE)' | cut -c1-400)
echo "$k"
rm -f "$out" "$out.names"
done=$(echo "$k" | sed -n 's/^DONE \([0-9]*\) checked.*/\1/p')
[ "$done" = "$want" ] || fail "kdiag3 checked ${done:-no} defs of $want"
openset=$(echo "$mapped" | awk '$2 == 1 {print $1}')
bad=$(echo "$k" | sed -n 's/^FAIL \([^:]*\):.*/\1/p' | grep -v -x -F "$openset")
[ -n "$bad" ] && fail "kernel FAIL on hole-free defs: $(echo $bad)"
echo "G1 PASS $F: bend2 ok ($todos TODOs), kernel $want defs ($(echo "$openset" | grep -c .) open)"
