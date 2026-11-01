# compiler: the program that the interpreter runs (AGENTS.md 3.6.6)
# =================================================================
#
# main is our own compiler: it takes the bytes of a book, as the Lean writer
# writes them, and gives the bytes of its WASM module. The laws of Compiler/spec.bend
# and their proofs (Compiler/proof.bend) are in this file's book, so that a book that
# --verdict accepts for this file holds them.

import Base
import ./Compiler/impl.bend as C
import ./Compiler/proof.bend as P

def main(+p: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  C.Compiler.compile(p)
