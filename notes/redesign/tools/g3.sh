#!/bin/bash
# g3.sh REF LOG: gate G3 (the milestones, src/milestones.ts steps 1-5) on the commit that REF names in
# the main repository, for mergeq.ts. Runs in ~/bb (the lead's WSL clone with the Lean build and the
# wasm-spec opam switch), as run-milestones.sh does for main: fetch REF, check it out detached, run
# milestones.sh through heavy.sh. One run at a time in ~/bb (lock ~/lead/locks/bb; it also waits for
# a milestones run that someone started without the lock); ~/bb's checkout is restored after. LOG's
# last line: `G3 PASS` or `G3 FAIL`.
export PATH=$HOME/.bun/bin:$HOME/.local/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin
REF=$1; LOG=$2; REPO=/mnt/c/Users/mathe/source/repos/bend-bootstrap
exec 7> ~/lead/locks/bb; flock 7
while pgrep -f "milestones.ts" > /dev/null; do sleep 20; done
cd ~/bb || { echo "G3 FAIL no ~/bb" > "$LOG"; exit 1; }
was=$(git rev-parse HEAD); trap 'git -C ~/bb checkout -q --detach "$was"' EXIT # ~/bb as it was
git fetch -q "$REPO" "$REF" && git checkout -q --detach FETCH_HEAD || { echo "G3 FAIL cannot fetch $REF" > "$LOG"; exit 1; }
echo "commit: $(git log --oneline -1 | cut -c1-80)" > "$LOG"
work=~/lead/g3-work; rm -rf "$work"
~/lead/heavy.sh timeout 14400 ~/lead/milestones.sh "$work" "$LOG.run"
cat "$LOG.run" >> "$LOG"
if grep -q '^EXIT 0$' "$LOG.run"; then echo "G3 PASS" >> "$LOG"; exit 0; fi
echo "G3 FAIL (milestones.ts exit: $(grep '^EXIT' "$LOG.run"))" >> "$LOG"; exit 1
