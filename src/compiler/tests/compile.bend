# the compiler of AGENTS.md 3.7.4 as a program: the bytes of a book in, the bytes of its
# module out
import Base
import ../../bend/src/compiler/impl.bend as C

def main(+p: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  C.Compiler.compile(p)
