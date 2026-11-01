import Base
import ../book/impl.bend as Bk
import ./cir/impl.bend as Cr
import ./machine/impl.bend as Mc

# Compiler
# ========
#
# The compiler of AGENTS.md 3.8.4: a fixed machine (Machine, below) with the
# program's book as the data of its memory. The machine is written in
# Cir, a small language of memory cells, which Cir.module translates to a
# module of the subset of WASM that the Bend version of WASM models.

# Compile
# -------

# a module whose run ends at once with the status s
def Compiler.halt(s: U32) -> List<&2, Word(8n)>:
  Cr.Wasm.encode(Cr.Cir.module(Cr.Cir.Stmt.halt{s}, 0n, []))

# the module of the machine with the image's cells
def Compiler.module(cells: List<&2, Cr.Cir.Cell>) -> List<&2, Word(8n)>:
  Cr.Wasm.encode(Cr.Cir.module(Mc.Mach.code(), Mc.Mach.regs(), cells))

# the module of the book that Book.read reads, r, by the cases of the
# compiler; machine makes the machine's module of an image
def Compiler.compile.of(machine: List<&2, Cr.Cir.Cell> -> List<&2, Word(8n)>, small: Bool, r: Maybe<List<&2, Bk.Def>>) ->
  List<&2, Word(8n)>:
  match small r:
    case False{} _:
      Compiler.halt(1)
    case True{} None{}:
      Compiler.halt(2)
    case True{} Some{+ds}:
      machine(Mc.Img.cells(ds))

# the compiler of AGENTS.md 3.8.4: the bytes of the module of the program whose
# book has the bytes p (3.6.4). A book of 2^26 bytes or more needs more memory
# than a module can have (Img.small): its module runs out of memory at once. Bytes that
# are no book give a module that gives no result
def Compiler.compile(+p: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  Compiler.compile.of(Compiler.module, Mc.Img.small(p, 0), Bk.Book.read(p))
