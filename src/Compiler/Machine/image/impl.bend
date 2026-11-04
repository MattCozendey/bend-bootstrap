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
