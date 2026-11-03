# compiler: every Var index of a read book is below |p|, from the reader's G
# ========================================================================
#
# VB(t, B) (read_var_bound.bend) holds for every body of a book that Book.read
# reads from p, at one B: Gt(t, 0) bounds every Var index of t (a Var's index is
# below its own Gn), Gt(t, 0) is at most Gd(ds, 0) for every body v of ds, and
# Gd(ds, 0) is at most |p| (Rb.Gx.read.le), so B = |p| works. Img.small keeps
# |p| below 2^26 (Rb.Gx.bound.small, at to_nat(67108863)), which is the bound a
# Var's U32 index needs (MO.tofrom).

import Base
import ../../Book/impl.bend as Bk
import ../need_big.bend as N
import ./definitions.bend as D
import ../img_small.bend as I
import ./read_bound.bend as Rb
import ./read_var_bound.bend as RV

# G bounds every Var index of its term
# ------------------------------------

# each part's G, at no addend, is at most the whole's
def Gt.vb(t: Bk.Term, +B: Nat, +h: N.Le(N.Gt(t, 0n), B)) -> {RV.VB(t, B) == True{} : Bool}:
  match t:
    case Bk.Term.Var{+i}:
      I.lt_nat(i, B, N.le_trans(1n+i, 2n+N.Gn(i, 0n), B, Rb.Gx.lt.gn(i), h))
    case Bk.Term.Ref{_}:
      {==}
    case Bk.Term.Ann{+x, +y}:
      +gx = N.Gt(x, 0n)
      +hx = N.le_trans(gx, 2n+N.Gt(y, gx), B, Rb.Gx.to2(x, y, gx, Rb.Gx.Gt.ge(y, gx)), h)
      +hy = N.le_trans(N.Gt(y, 0n), 2n+N.Gt(y, gx), B, Rb.Gx.to2(y, y, gx, Rb.Gx.mono0(y, gx)), h)
      D.and.i(RV.VB(x, B), RV.VB(y, B), Gt.vb(x, B, hx), Gt.vb(y, B, hy))
    case Bk.Term.Let{_, +v, +f}:
      +gv = N.Gt(v, 0n)
      +gv2 = N.Gt(v, 2n)
      +g = N.Gt(f, gv2)
      +gp = {2n+g : Nat}
      +hv = N.le_trans(gv, gp, B,
        Rb.Gx.to2(v, f, gv2, N.le_trans(gv, gv2, g, Rb.Gx.mono0(v, 2n), Rb.Gx.Gt.ge(f, gv2))), h)
      +hf = N.le_trans(N.Gt(f, 0n), gp, B, Rb.Gx.to2(f, f, gv2, Rb.Gx.mono0(f, gv2)), h)
      D.and.i(RV.VB(v, B), RV.VB(f, B), Gt.vb(v, B, hv), Gt.vb(f, B, hf))
    case Bk.Term.Typ{+q}:
      Gt.vb(q, B, N.le_trans(N.Gt(q, 0n), 2n+N.Gt(q, 0n), B, N.le_add_l(2n, N.Gt(q, 0n)), h))
    case Bk.Term.Min{+x, +y}:
      +gx = N.Gt(x, 0n)
      +hx = N.le_trans(gx, 2n+N.Gt(y, gx), B, Rb.Gx.to2(x, y, gx, Rb.Gx.Gt.ge(y, gx)), h)
      +hy = N.le_trans(N.Gt(y, 0n), 2n+N.Gt(y, gx), B, Rb.Gx.to2(y, y, gx, Rb.Gx.mono0(y, gx)), h)
      D.and.i(RV.VB(x, B), RV.VB(y, B), Gt.vb(x, B, hx), Gt.vb(y, B, hy))
    case Bk.Term.All{_, +x, +y}:
      +gx = N.Gt(x, 0n)
      +gx2 = N.Gt(x, 2n)
      +g = N.Gt(y, gx2)
      +gp = {2n+g : Nat}
      +hx = N.le_trans(gx, gp, B,
        Rb.Gx.to2(x, y, gx2, N.le_trans(gx, gx2, g, Rb.Gx.mono0(x, 2n), Rb.Gx.Gt.ge(y, gx2))), h)
      +hy = N.le_trans(N.Gt(y, 0n), gp, B, Rb.Gx.to2(y, y, gx2, Rb.Gx.mono0(y, gx2)), h)
      D.and.i(RV.VB(x, B), RV.VB(y, B), Gt.vb(x, B, hx), Gt.vb(y, B, hy))
    case Bk.Term.Lam{_, +f}:
      +hf = N.le_trans(N.Gt(f, 0n), 2n+N.Gt(f, 2n), B, Rb.Gx.to2(f, f, 2n, Rb.Gx.mono0(f, 2n)), h)
      Gt.vb(f, B, hf)
    case Bk.Term.App{_, +f, +x}:
      +gf = N.Gt(f, 2n)
      +gfx = N.Gt(x, gf)
      +hf = N.le_trans(N.Gt(f, 0n), 2n+gfx, B,
        Rb.Gx.to2(f, x, gf, N.le_trans(N.Gt(f, 0n), gf, gfx, Rb.Gx.mono0(f, 2n), Rb.Gx.Gt.ge(x, gf))), h)
      +hx = N.le_trans(N.Gt(x, 0n), 2n+gfx, B, Rb.Gx.to2(x, x, gf, Rb.Gx.mono0(x, gf)), h)
      D.and.i(RV.VB(f, B), RV.VB(x, B), Gt.vb(f, B, hf), Gt.vb(x, B, hx))
    case Bk.Term.Sig{_, +x, +y}:
      +gx = N.Gt(x, 0n)
      +gx2 = N.Gt(x, 2n)
      +g = N.Gt(y, gx2)
      +gp = {2n+g : Nat}
      +hx = N.le_trans(gx, gp, B,
        Rb.Gx.to2(x, y, gx2, N.le_trans(gx, gx2, g, Rb.Gx.mono0(x, 2n), Rb.Gx.Gt.ge(y, gx2))), h)
      +hy = N.le_trans(N.Gt(y, 0n), gp, B, Rb.Gx.to2(y, y, gx2, Rb.Gx.mono0(y, gx2)), h)
      D.and.i(RV.VB(x, B), RV.VB(y, B), Gt.vb(x, B, hx), Gt.vb(y, B, hy))
    case Bk.Term.Tup{_, +x, +y}:
      +gx = N.Gt(x, 2n)
      +gxy = N.Gt(y, gx)
      +hx = N.le_trans(N.Gt(x, 0n), 2n+gxy, B,
        Rb.Gx.to2(x, y, gx, N.le_trans(N.Gt(x, 0n), gx, gxy, Rb.Gx.mono0(x, 2n), Rb.Gx.Gt.ge(y, gx))), h)
      +hy = N.le_trans(N.Gt(y, 0n), 2n+gxy, B, Rb.Gx.to2(y, y, gx, Rb.Gx.mono0(y, gx)), h)
      D.and.i(RV.VB(x, B), RV.VB(y, B), Gt.vb(x, B, hx), Gt.vb(y, B, hy))
    case Bk.Term.Prj{+h0}:
      Gt.vb(h0, B, N.le_trans(N.Gt(h0, 0n), 2n+N.Gt(h0, 0n), B, N.le_add_l(2n, N.Gt(h0, 0n)), h))
    case Bk.Term.Enu{_}:
      {==}
    case Bk.Term.Lab{_}:
      {==}
    case Bk.Term.Mat{+k, +h0, +m}:
      +gk = N.Gk(k, 0n)
      +gh = N.Gt(h0, gk)
      +gm = N.Gt(m, gh)
      +hh = N.le_trans(N.Gt(h0, 0n), 2n+gm, B,
        Rb.Gx.to2(h0, m, gh, N.le_trans(N.Gt(h0, 0n), gh, gm, Rb.Gx.mono0(h0, gk), Rb.Gx.Gt.ge(m, gh))), h)
      +hm = N.le_trans(N.Gt(m, 0n), 2n+gm, B, Rb.Gx.to2(m, m, gh, Rb.Gx.mono0(m, gh)), h)
      D.and.i(RV.VB(h0, B), RV.VB(m, B), Gt.vb(h0, B, hh), Gt.vb(m, B, hm))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{+x, +y, +T}:
      +gx = N.Gt(x, 0n)
      +gyx = N.Gt(y, gx)
      +g = N.Gt(T, gyx)
      +hx = N.le_trans(gx, 2n+g, B,
        Rb.Gx.to2(x, T, gyx, N.le_trans(gx, gyx, g, Rb.Gx.Gt.ge(y, gx), Rb.Gx.Gt.ge(T, gyx))), h)
      +hy = N.le_trans(N.Gt(y, 0n), 2n+g, B,
        Rb.Gx.to2(y, T, gyx, N.le_trans(N.Gt(y, 0n), gyx, g, Rb.Gx.mono0(y, gx), Rb.Gx.Gt.ge(T, gyx))), h)
      +hT = N.le_trans(N.Gt(T, 0n), 2n+g, B, Rb.Gx.to2(T, T, gyx, Rb.Gx.mono0(T, gyx)), h)
      D.and.i(RV.VB(x, B), Bool.and(RV.VB(y, B), RV.VB(T, B)), Gt.vb(x, B, hx),
        D.and.i(RV.VB(y, B), RV.VB(T, B), Gt.vb(y, B, hy), Gt.vb(T, B, hT)))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{+e, +p, +f}:
      +ge = N.Gt(e, 0n)
      +gpe = N.Gt(p, ge)
      +g = N.Gt(f, gpe)
      +he = N.le_trans(ge, 2n+g, B,
        Rb.Gx.to2(e, f, gpe, N.le_trans(ge, gpe, g, Rb.Gx.Gt.ge(p, ge), Rb.Gx.Gt.ge(f, gpe))), h)
      +hp = N.le_trans(N.Gt(p, 0n), 2n+g, B,
        Rb.Gx.to2(p, f, gpe, N.le_trans(N.Gt(p, 0n), gpe, g, Rb.Gx.mono0(p, ge), Rb.Gx.Gt.ge(f, gpe))), h)
      +hf = N.le_trans(N.Gt(f, 0n), 2n+g, B, Rb.Gx.to2(f, f, gpe, Rb.Gx.mono0(f, gpe)), h)
      D.and.i(RV.VB(e, B), Bool.and(RV.VB(p, B), RV.VB(f, B)), Gt.vb(e, B, he),
        D.and.i(RV.VB(p, B), RV.VB(f, B), Gt.vb(p, B, hp), Gt.vb(f, B, hf)))

# every body's G is below the book's
# ----------------------------------

# the bound of every body of ds
def DB(ds: List<&2, Bk.Def>, +B: Nat) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{Bk.Def{_, _, +v, _}, +rest}:
      D.P2(N.Le(N.Gt(v, 0n), B), DB(rest, B))

def db.of(ds: List<&2, Bk.Def>, +B: Nat, +h: N.Le(N.Gd(ds, 0n), B)) -> DB(ds, B):
  match ds:
    case Nil{}:
      Unit{}
    case Con{Bk.Def{+k, +ty, +v, +o}, +rest}:
      +grest = N.Gd(rest, 0n)
      +x = N.Gt(ty, N.Gk(k, grest))
      +gdef = N.Gdef(Bk.Def{k, ty, v, o}, grest)
      +gpar = {2n+gdef : Nat}
      +hv = N.le_trans(N.Gt(v, 0n), gpar, B,
        N.le_trans(N.Gt(v, 0n), gdef, gpar,
          N.le_trans(N.Gt(v, 0n), N.Gt(v, x), gdef, Rb.Gx.mono0(v, x), N.le_add_l(4n, N.Gt(v, x))),
          N.le_add_l(2n, gdef)),
        h)
      +hrest = N.le_trans(grest, gpar, B, Rb.Gx.Gd.tail(Bk.Def{k, ty, v, o}, rest), h)
      Tuple{hv, db.of(rest, B, hrest)}
