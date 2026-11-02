# compiler: layer B, the move of the output (U9)
# ==============================================
#
# mv.out of move_kit.bend: M.out from out_bytes.bend (out.post, out.done below), in PostB form
# with the output's budget.
# Filled by U9; U0 left each as ?TODO.

import Base
import ../../Book/impl.bend as Bk
import ../Cir/impl.bend as Cr
import ./impl.bend as Mc
import ./definitions.bend as D
import ./cell_stands_for.bend as PI
import ./out_bytes_from_is.bend as OI
import ./move_kit.bend as K

# M.out, as out_bytes_from_is.bend proves it (from moves.bend)
def out.post(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32,
  +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +v: Bk.Term, +ks2: List<&2, List<&2, Word(8n)>>,
  +hv: D.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}) ->
  D.OutPost(f, ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk):
  OI.out.post(f, ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk,
    PI.is.tm(ds, m, im, fi, nx, ks, img, foc, v, hv))


def out.done(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32,
  +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +v: Bk.Term, +ks2: List<&2, List<&2, Word(8n)>>,
  +hv: D.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}) ->
  D.OutDone(ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk):
  OI.out.done(ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk,
    PI.is.tm(ds, m, im, fi, nx, ks, img, foc, v, hv))


def K.mv.out(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv):
  ?TODO
