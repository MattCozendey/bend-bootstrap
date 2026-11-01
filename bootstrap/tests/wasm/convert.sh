#!/bin/bash
# convert.sh WORK: the binary scripts of the official WebAssembly tests that
# the Bend version of WASM is tested with (AGENTS.md 3.7.1.3), made by cut.ml, which reads each
# test script with the spec's own reference interpreter, keeps in each module
# that a command defines only its functions inside the subset, and writes the
# script as wasm -d x.wast -o x.bin.wast does. The spec's commit is pinned:
# the script refuses any other. It needs ocaml, dune and menhir. WORK is a
# folder for the spec's clone and the build. The license, the tests (wast/), and their binary scripts and
# lists of pure exports (bin/) go next to this script.
set -euo pipefail

SPEC=https://github.com/WebAssembly/spec.git
COMMIT=6057acdb1a213f85369c64454c078a15f11ac4b1
TESTS=(binary binary-leb128 i32 int_exprs address align endianness load store memory memory_grow
  memory_size memory_trap data block loop br br_if br_table labels local_get local_set local_tee
  exports unreached-invalid)

here=$(cd "$(dirname "$0")" && pwd)
work=${1:?usage: convert.sh WORK}

for t in ocaml dune menhir; do
  command -v "$t" > /dev/null || { echo "convert.sh needs $t" >&2; exit 1; }
done

mkdir -p "$work"
cd "$work"
[ -d spec/.git ] || git init -q spec
git -C spec fetch -q --depth 1 "$SPEC" "$COMMIT"
git -C spec checkout -q --detach FETCH_HEAD
if [ "$(git -C spec rev-parse HEAD)" != "$COMMIT" ]; then
  echo "convert.sh: the spec is not at $COMMIT" >&2
  exit 1
fi

# a dune workspace of the interpreter's library and cut.ml alone
rm -rf cut
mkdir -p cut/cut
cp -r spec/interpreter cut/interpreter
rm -rf cut/interpreter/_build
printf '(lang dune 3.14)\n' > cut/dune-workspace
printf '(lang dune 3.14)\n' > cut/cut/dune-project
printf '(executable\n  (name cut)\n  (libraries wasm)\n  (flags (:standard -open Wasm)))\n' > cut/cut/dune
cp "$here/cut.ml" cut/cut/cut.ml
(cd cut && dune build ./cut/cut.exe)

rm -rf "$here/wast" "$here/bin"
mkdir -p "$here/wast" "$here/bin"
cp spec/test/LICENSE "$here/LICENSE"
for t in "${TESTS[@]}"; do
  cp "spec/test/core/$t.wast" "$here/wast/$t.wast"
  cut/_build/default/cut/cut.exe "spec/test/core/$t.wast" "$here/bin/$t.pure" > "$here/bin/$t.bin.wast"
done
