# compiler: layer B3, the proofs of image/spec.bend
# =================================================
#
# One def per law (the image at the start (port img_ok, image_*,
# first_cell_past_table and read_var_bound from 4ebef88), its frame, table and
# Refs). A body that is ?TODO is open.

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../../../Wasm/impl.bend as Wa
import ../../Cir/impl.bend as Cr
import ../impl.bend as Mc
import ../shared.bend as K
import ../logic/spec.bend as Lg
import ../header/spec.bend as Hs
import ../heap/spec.bend as Hp
import ./spec.bend as I
import ../logic/impl.bend as LgP
import ../header/impl.bend as HsP
import ../canon/impl.bend as CP
import ../am/impl.bend as AP
import ../heap/view.bend as HpV
import ../heap/count.bend as HpC

def I.img.start(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO

def I.img.frame(x, m, m2, h, a):
  ?TODO

def I.img.store(x, m, o, k, v, n):
  ?TODO

def I.img.put(x, m, o, v, n):
  ?TODO

def I.img.table(x, m, t, h, ht):
  ?TODO

def I.img.ref(x, m, k, h):
  ?TODO

# n registers of 0
def img.rep_len(n: Nat) -> {List.length(&2, U32, List.replicate(U32, n, 0)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      %img.rep_len(np) : {1n+List.length(&2, U32, List.replicate(U32, np, 0)) == 1n+_ : Nat}
      {==}

# each of them 0
def img.rep_get(n: Nat, q: Nat, +h: {Nat.is_lt(q, n) == True{} : Bool}) ->
  {List.get(&2, U32, List.replicate(U32, n, 0), q) == Some{0} : Maybe<&2, U32>}:
  match n q:
    case 0n 0n:
      K.bool.ff({List.get(&2, U32, List.replicate(U32, 0n, 0), 0n) == Some{0} : Maybe<&2, U32>}, h)
    case 0n 1n+qp:
      K.bool.ff({List.get(&2, U32, List.replicate(U32, 0n, 0), 1n+qp) == Some{0} : Maybe<&2, U32>}, h)
    case 1n+np 0n:
      {==}
    case 1n+np 1n+qp:
      img.rep_get(np, qp, h)

def I.st0.nregs(n, cells, first, k, p, lim, i):
  img.rep_len(n)

def I.st0.reg(n, cells, first, k, p, lim, i, q, hq):
  img.rep_get(n, q, hq)
