#!/bin/bash
# gate.sh WT FILE [HOST]: the two checkers on FILE (path under src/, e.g. Compiler/Machine/heap_ops.bend)
# in worktree WT. 1) bend2 --check-only FILE: must print only a TODO count (holes), no other error.
# 2) lower HOST (default FILE; use Compiler/Machine/moves.bend for a file that cannot be lowered alone)
# and kernel-check FILE`s defs by name (kdiag3): prints FAIL lines and DONE n checked, k fail.
# Every heavy step runs through heavy.sh.
# Installed as ~/lead/gate.sh (a symlink to reports/redesign/tools/gate.sh; the original is
# ~/lead/gate.sh.orig-g2pool). Changes of 2026-11-04 (g2pool), same verdict: the lowered file is named
# by the worktree and HOST's whole path (two files with one basename, gated at once, no longer share
# it); a def that fills a law of an import (`def Lg.x(..)`: lowered as <import's path>.x, e.g.
# spec.x) is kernel-checked under that name (kmap.awk), as is every def of FILE; a name that is not in
# the lowered book prints `MISSING <name>` (kdiag3 skips unknown names silently: compare DONE's count).
H=~/lead/heavy.sh; WT=$1; F=$2; HOST=${3:-$2}
TOOLS=$(dirname "$(readlink -f "$0")")
cd $WT/src || exit 2
tag=$(echo "$WT:$HOST" | md5sum | cut -c1-12); out=/tmp/gate-$(basename $WT)-$(basename $HOST .bend)-$tag.bendtt
echo "== bend2 $F"
$H timeout 3600 bun ../bend/bend2/main.ts $F --check-only 2>&1 | grep -v "^\s*$" | head -40 | cut -c1-400
echo "== lower $HOST"
$H timeout 3600 bun Shared/lower.ts $HOST $out 2>&1 | tail -4
# FILE's defs as kmap.awk reads them: a def whose first segment is an import alias of FILE fills that
# import's law (its path made relative to HOST's dir); the others are FILE's own, under FILE's path
# relative to HOST's dir when HOST is another file
fdir=$(dirname $F); hdir=$(dirname $HOST)
names=$out.want
sed -n 's/^import[ \t]\{1,\}\([^ \t]*\.bend\)[ \t]\{1,\}as[ \t]\{1,\}\([A-Za-z_][A-Za-z0-9_]*\).*/\2 \1/p' $F > $out.al
grep -o '^\(@unsafe \)\{0,1\}def [A-Za-z0-9_.]*' $F | sed 's/^@unsafe //; s/^def //' | sort -u | while read -r d; do
  a=${d%%.*}; p=$(awk -v a="$a" '$1 == a { print $2; exit }' $out.al)
  if [ -n "$p" ] && [ "$a" != "$d" ]; then
    echo "fill $(realpath -m --relative-to="$hdir" "$fdir/${p%.bend}") ${d#"$a".}"
  elif [ "$F" != "$HOST" ]; then
    echo "fill $(realpath -m --relative-to="$hdir" "${F%.bend}") $d"
  else
    echo "own $d"
  fi
done > $names
grep -o '^[^ ]* :' $out | sed 's/ :$//' > $out.names
mapped=$(awk -f "$TOOLS/kmap.awk" $out.names $names)
echo "$mapped" | grep '^MISSING'
ks=$(echo "$mapped" | grep -v '^MISSING' | awk '{print $1}')
echo "== kernel: $(echo $ks | wc -w) defs of $F"
$H env LEAN_STACK_SIZE_KB=4194304 ~/kdiag/kdiag3 $out $ks 2>&1 | grep -E "^(FAIL|DONE|SLOW|PARSE)" | cut -c1-300
rm -f $out.al $out.names $names
