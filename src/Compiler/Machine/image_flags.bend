# compiler: the VALUE and DATA flags of a node of the image (layer B)
# =================================================================
#
# Img.node writes Img.header(tg, q, fl, fv) as field 0 of a node's cell. NdK
# (definitions.bend) reads bit 256, VALUE, and bit 512, DATA, and asks: if
# VALUE, the term is a value (Eval.vals); if DATA, it is Data (Term.is_data).
# This file gives those two clauses of each node form that Img.go builds.
#
# The header is lo(tg, q, fl) | fv << 13, with lo in its 13 low bits; hdr
# (image_header_bits.bend) gives the flag bits of lo as the header's (hd.vd).
# A node whose flag bit is clear needs nothing of the term (fl.off256,
# fl.off512); a node whose flag bit is set needs the term to be a value or
# Data (D.or.r); and a pair takes both bits from its parts (tup.vd).

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ./impl.bend as Mc
import ./definitions.bend as D
import ./image_header_bits.bend as IH
import ../need_big.bend as N

# The low part
# ------------

# the 13 low bits of a header: its tag tg, its quantity q and its flags fl
def ig.lo(+tg: U32, +q: U32, +fl: U32) -> U32:
  U32.or(U32.or(tg, U32.shln(q, 6n)), fl)

# A clear flag bit
# ----------------

# the VALUE clause of a node whose flag bit 256 is clear, from the header r
def ig.fl.off256.of(+lo: U32, +fv: U32, +P: Bool, r: IH.Hdr(lo, fv), e: {D.FlW(lo, 256) == False{} : Bool}) ->
  {Bool.or(Bool.not(D.FlW(U32.or(lo, U32.shln(fv, 13n)), 256)), P) == True{} : Bool}:
  match r:
    case Tuple{_, Tuple{_, Tuple{e3, _}}}:
      %Equal.sym(Bool, D.FlW(U32.or(lo, U32.shln(fv, 13n)), 256), False{},
        Equal.trans(Bool, D.FlW(U32.or(lo, U32.shln(fv, 13n)), 256), D.FlW(lo, 256), False{}, e3, e)) :
        {Bool.or(Bool.not(_), P) == True{} : Bool}
      {==}

def ig.fl.off256(+lo: U32, +fv: U32, +P: Bool, +h: {U32.and(lo, 8191) == lo : U32}, e: {D.FlW(lo, 256) == False{} : Bool}) ->
  {Bool.or(Bool.not(D.FlW(U32.or(lo, U32.shln(fv, 13n)), 256)), P) == True{} : Bool}:
  ig.fl.off256.of(lo, fv, P, IH.hdr(lo, fv, h), e)

# the DATA clause of a node whose flag bit 512 is clear
def ig.fl.off512.of(+lo: U32, +fv: U32, +P: Bool, r: IH.Hdr(lo, fv), e: {D.FlW(lo, 512) == False{} : Bool}) ->
  {Bool.or(Bool.not(D.FlW(U32.or(lo, U32.shln(fv, 13n)), 512)), P) == True{} : Bool}:
  match r:
    case Tuple{_, Tuple{_, Tuple{_, Tuple{e4, _}}}}:
      %Equal.sym(Bool, D.FlW(U32.or(lo, U32.shln(fv, 13n)), 512), False{},
        Equal.trans(Bool, D.FlW(U32.or(lo, U32.shln(fv, 13n)), 512), D.FlW(lo, 512), False{}, e4, e)) :
        {Bool.or(Bool.not(_), P) == True{} : Bool}
      {==}

def ig.fl.off512(+lo: U32, +fv: U32, +P: Bool, +h: {U32.and(lo, 8191) == lo : U32}, e: {D.FlW(lo, 512) == False{} : Bool}) ->
  {Bool.or(Bool.not(D.FlW(U32.or(lo, U32.shln(fv, 13n)), 512)), P) == True{} : Bool}:
  ig.fl.off512.of(lo, fv, P, IH.hdr(lo, fv, h), e)

# Bool kit
# --------

# P holds, from or(not b, P) and b
def ig.or.t(+b: Bool, +P: Bool, h: {Bool.or(Bool.not(b), P) == True{} : Bool}, hb: {b == True{} : Bool}) ->
  {P == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({P == True{} : Bool}, N.false_ne_true(hb))

# or(dead, P) holds, from or(dead, vx) and or(not vx, P)
def ig.or.sub(+dead: Bool, +vx: Bool, +P: Bool, hd: {Bool.or(dead, vx) == True{} : Bool},
  hp: {Bool.or(Bool.not(vx), P) == True{} : Bool}) -> {Bool.or(dead, P) == True{} : Bool}:
  match dead:
    case True{}:
      {==}
    case False{}:
      ig.or.t(vx, P, hp, hd)

# The nodes
# ---------

# a Var node: not a value, not Data
def ig.var.vd(+ds: List<&2, Bk.Def>, +i: Nat, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Var{i}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.var(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Var{i})) == True{} : Bool}):
  (ig.fl.off256(ig.lo(Mc.T.var(), 0, 1024), fv, El.Eval.vals(ds, Bk.Term.Var{i}, False{}), {==}, {==}),
   ig.fl.off512(ig.lo(Mc.T.var(), 0, 1024), fv, El.Term.is_data(Bk.Term.Var{i}), {==}, {==}))

# a Ref node: not a value, not Data
def ig.ref.vd(+ds: List<&2, Bk.Def>, +k: List<&2, Word(8n)>, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.ref(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Ref{k}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.ref(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Ref{k})) == True{} : Bool}):
  (ig.fl.off256(ig.lo(Mc.T.ref(), 0, 1024), fv, El.Eval.vals(ds, Bk.Term.Ref{k}, False{}), {==}, {==}),
   ig.fl.off512(ig.lo(Mc.T.ref(), 0, 1024), fv, El.Term.is_data(Bk.Term.Ref{k}), {==}, {==}))

# an Ann node: not a value, not Data
def ig.ann.vd(+ds: List<&2, Bk.Def>, +y: Bk.Term, +z: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.ann(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Ann{y, z}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.ann(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Ann{y, z})) == True{} : Bool}):
  (ig.fl.off256(ig.lo(Mc.T.ann(), 0, 1024), fv, El.Eval.vals(ds, Bk.Term.Ann{y, z}, False{}), {==}, {==}),
   ig.fl.off512(ig.lo(Mc.T.ann(), 0, 1024), fv, El.Term.is_data(Bk.Term.Ann{y, z}), {==}, {==}))

# a Let node: not a value, not Data
def ig.let.vd(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +v: Bk.Term, +f: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.let(), Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Let{q, v, f}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.let(), Mc.Img.quan(q), 1024, fv), 512)), El.Term.is_data(Bk.Term.Let{q, v, f})) == True{} : Bool}):
  match q:
    case Bk.Quan.Q0{}:
      (ig.fl.off256(ig.lo(Mc.T.let(), Mc.Img.quan(q), 1024), fv, El.Eval.vals(ds, Bk.Term.Let{q, v, f}, False{}), {==}, {==}),
       ig.fl.off512(ig.lo(Mc.T.let(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Let{q, v, f}), {==}, {==}))
    case Bk.Quan.Q1{}:
      (ig.fl.off256(ig.lo(Mc.T.let(), Mc.Img.quan(q), 1024), fv, El.Eval.vals(ds, Bk.Term.Let{q, v, f}, False{}), {==}, {==}),
       ig.fl.off512(ig.lo(Mc.T.let(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Let{q, v, f}), {==}, {==}))
    case Bk.Quan.Q2{}:
      (ig.fl.off256(ig.lo(Mc.T.let(), Mc.Img.quan(q), 1024), fv, El.Eval.vals(ds, Bk.Term.Let{q, v, f}, False{}), {==}, {==}),
       ig.fl.off512(ig.lo(Mc.T.let(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Let{q, v, f}), {==}, {==}))

# a Typ node: a former, not Data
def ig.typ.vd(+ds: List<&2, Bk.Def>, +y: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(4, 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Typ{y}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(4, 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Typ{y})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(4, 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Typ{y}, False{}), {==}),
   ig.fl.off512(ig.lo(4, 0, 1024), fv, El.Term.is_data(Bk.Term.Typ{y}), {==}, {==}))

# a Min node: not a value, not Data
def ig.min.vd(+ds: List<&2, Bk.Def>, +a: Bk.Term, +b: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.min(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Min{a, b}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.min(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Min{a, b})) == True{} : Bool}):
  (ig.fl.off256(ig.lo(Mc.T.min(), 0, 1024), fv, El.Eval.vals(ds, Bk.Term.Min{a, b}, False{}), {==}, {==}),
   ig.fl.off512(ig.lo(Mc.T.min(), 0, 1024), fv, El.Term.is_data(Bk.Term.Min{a, b}), {==}, {==}))

# an All node: a former, not Data
def ig.all.vd(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +A: Bk.Term, +B: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(6, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.All{q, A, B}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(6, Mc.Img.quan(q), 1024, fv), 512)), El.Term.is_data(Bk.Term.All{q, A, B})) == True{} : Bool}):
  match q:
    case Bk.Quan.Q0{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(6, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.All{q, A, B}, False{}), {==}),
       ig.fl.off512(ig.lo(6, Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.All{q, A, B}), {==}, {==}))
    case Bk.Quan.Q1{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(6, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.All{q, A, B}, False{}), {==}),
       ig.fl.off512(ig.lo(6, Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.All{q, A, B}), {==}, {==}))
    case Bk.Quan.Q2{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(6, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.All{q, A, B}, False{}), {==}),
       ig.fl.off512(ig.lo(6, Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.All{q, A, B}), {==}, {==}))

# a Lam node: a former, not Data
def ig.lam.vd(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +f: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.lam(), Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Lam{q, f}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.lam(), Mc.Img.quan(q), 1024, fv), 512)), El.Term.is_data(Bk.Term.Lam{q, f})) == True{} : Bool}):
  match q:
    case Bk.Quan.Q0{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.lam(), Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Lam{q, f}, False{}), {==}),
       ig.fl.off512(ig.lo(Mc.T.lam(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Lam{q, f}), {==}, {==}))
    case Bk.Quan.Q1{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.lam(), Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Lam{q, f}, False{}), {==}),
       ig.fl.off512(ig.lo(Mc.T.lam(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Lam{q, f}), {==}, {==}))
    case Bk.Quan.Q2{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.lam(), Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Lam{q, f}, False{}), {==}),
       ig.fl.off512(ig.lo(Mc.T.lam(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Lam{q, f}), {==}, {==}))

# an App node: not a value, not Data
def ig.app.vd(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +f: Bk.Term, +x: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.app(), Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.App{q, f, x}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.app(), Mc.Img.quan(q), 1024, fv), 512)), El.Term.is_data(Bk.Term.App{q, f, x})) == True{} : Bool}):
  match q:
    case Bk.Quan.Q0{}:
      (ig.fl.off256(ig.lo(Mc.T.app(), Mc.Img.quan(q), 1024), fv, El.Eval.vals(ds, Bk.Term.App{q, f, x}, False{}), {==}, {==}),
       ig.fl.off512(ig.lo(Mc.T.app(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.App{q, f, x}), {==}, {==}))
    case Bk.Quan.Q1{}:
      (ig.fl.off256(ig.lo(Mc.T.app(), Mc.Img.quan(q), 1024), fv, El.Eval.vals(ds, Bk.Term.App{q, f, x}, False{}), {==}, {==}),
       ig.fl.off512(ig.lo(Mc.T.app(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.App{q, f, x}), {==}, {==}))
    case Bk.Quan.Q2{}:
      (ig.fl.off256(ig.lo(Mc.T.app(), Mc.Img.quan(q), 1024), fv, El.Eval.vals(ds, Bk.Term.App{q, f, x}, False{}), {==}, {==}),
       ig.fl.off512(ig.lo(Mc.T.app(), Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.App{q, f, x}), {==}, {==}))

# a Sig node: a former, not Data
def ig.sig.vd(+ds: List<&2, Bk.Def>, +q: Bk.Quan, +A: Bk.Term, +B: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(9, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Sig{q, A, B}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(9, Mc.Img.quan(q), 1024, fv), 512)), El.Term.is_data(Bk.Term.Sig{q, A, B})) == True{} : Bool}):
  match q:
    case Bk.Quan.Q0{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(9, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Sig{q, A, B}, False{}), {==}),
       ig.fl.off512(ig.lo(9, Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Sig{q, A, B}), {==}, {==}))
    case Bk.Quan.Q1{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(9, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Sig{q, A, B}, False{}), {==}),
       ig.fl.off512(ig.lo(9, Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Sig{q, A, B}), {==}, {==}))
    case Bk.Quan.Q2{}:
      (D.or.r(Bool.not(D.FlW(Mc.Img.header(9, Mc.Img.quan(q), 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Sig{q, A, B}, False{}), {==}),
       ig.fl.off512(ig.lo(9, Mc.Img.quan(q), 1024), fv, El.Term.is_data(Bk.Term.Sig{q, A, B}), {==}, {==}))

# a Prj node: a former, not Data
def ig.prj.vd(+ds: List<&2, Bk.Def>, +h: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.prj(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Prj{h}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.prj(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Prj{h})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.prj(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Prj{h}, False{}), {==}),
   ig.fl.off512(ig.lo(Mc.T.prj(), 0, 1024), fv, El.Term.is_data(Bk.Term.Prj{h}), {==}, {==}))

# an Enu node: a former, not Data
def ig.enu.vd(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(12, 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Enu{ks}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(12, 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Enu{ks})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(12, 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Enu{ks}, False{}), {==}),
   ig.fl.off512(ig.lo(12, 0, 1024), fv, El.Term.is_data(Bk.Term.Enu{ks}), {==}, {==}))

# a Lab node: a former, and Data
def ig.lab.vd(+ds: List<&2, Bk.Def>, +k: List<&2, Word(8n)>, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.lab(), 0, 1536, fv), 256)), El.Eval.vals(ds, Bk.Term.Lab{k}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.lab(), 0, 1536, fv), 512)), El.Term.is_data(Bk.Term.Lab{k})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.lab(), 0, 1536, fv), 256)), El.Eval.vals(ds, Bk.Term.Lab{k}, False{}), {==}),
   D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.lab(), 0, 1536, fv), 512)), El.Term.is_data(Bk.Term.Lab{k}), {==}))

# a Mat node: a former, not Data
def ig.mat.vd(+ds: List<&2, Bk.Def>, +k: List<&2, Word(8n)>, +h: Bk.Term, +m: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.mat(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Mat{k, h, m}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.mat(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Mat{k, h, m})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.mat(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Mat{k, h, m}, False{}), {==}),
   ig.fl.off512(ig.lo(Mc.T.mat(), 0, 1024), fv, El.Term.is_data(Bk.Term.Mat{k, h, m}), {==}, {==}))

# an Efq node: a former, not Data
def ig.efq.vd(+ds: List<&2, Bk.Def>, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.efq(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Efq{}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.efq(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Efq{})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.efq(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Efq{}, False{}), {==}),
   ig.fl.off512(ig.lo(Mc.T.efq(), 0, 1024), fv, El.Term.is_data(Bk.Term.Efq{}), {==}, {==}))

# an Eql node: a former, not Data
def ig.eql.vd(+ds: List<&2, Bk.Def>, +a: Bk.Term, +b: Bk.Term, +T: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(16, 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Eql{a, b, T}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(16, 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Eql{a, b, T})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(16, 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Eql{a, b, T}, False{}), {==}),
   ig.fl.off512(ig.lo(16, 0, 1024), fv, El.Term.is_data(Bk.Term.Eql{a, b, T}), {==}, {==}))

# an Rfl node: a former, and Data
def ig.rfl.vd(+ds: List<&2, Bk.Def>, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.rfl(), 0, 1536, fv), 256)), El.Eval.vals(ds, Bk.Term.Rfl{}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.rfl(), 0, 1536, fv), 512)), El.Term.is_data(Bk.Term.Rfl{})) == True{} : Bool}):
  (D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.rfl(), 0, 1536, fv), 256)), El.Eval.vals(ds, Bk.Term.Rfl{}, False{}), {==}),
   D.or.r(Bool.not(D.FlW(Mc.Img.header(Mc.T.rfl(), 0, 1536, fv), 512)), El.Term.is_data(Bk.Term.Rfl{}), {==}))

# an Rwt node: not a value, not Data
def ig.rwt.vd(+ds: List<&2, Bk.Def>, +e: Bk.Term, +P: Bk.Term, +f: Bk.Term, +fv: U32) ->
  D.P2({Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.rwt(), 0, 1024, fv), 256)), El.Eval.vals(ds, Bk.Term.Rwt{e, P, f}, False{})) == True{} : Bool},
       {Bool.or(Bool.not(D.FlW(Mc.Img.header(Mc.T.rwt(), 0, 1024, fv), 512)), El.Term.is_data(Bk.Term.Rwt{e, P, f})) == True{} : Bool}):
  (ig.fl.off256(ig.lo(Mc.T.rwt(), 0, 1024), fv, El.Eval.vals(ds, Bk.Term.Rwt{e, P, f}, False{}), {==}, {==}),
   ig.fl.off512(ig.lo(Mc.T.rwt(), 0, 1024), fv, El.Term.is_data(Bk.Term.Rwt{e, P, f}), {==}, {==}))
