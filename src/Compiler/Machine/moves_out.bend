# compiler: layer B, the move of the output (U9)
# ==============================================
#
# mv.out of move_kit.bend: M.out from out_bytes.bend (out.postb, out.done below), in PostB form:
# it runs out of memory only when the limit has fewer bytes than 20 nx + |v| (out.postb), at
# most Budget, whose output part is 20 next + |t| (out.mv).

import Base
import ../../Book/impl.bend as Bk
import ../../Eval/impl.bend as El
import ../../Program/impl.bend as Pg
import ../Cir/impl.bend as Cr
import ../need_big.bend as N
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


# M.out, with its budget, as out_bytes_from_is.bend proves it
def out.postb(+f: Nat, +ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32,
  +pend: U32, +rest: D.R59, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +v: Bk.Term, +ks2: List<&2, List<&2, Word(8n)>>,
  +hv: D.Is(ds, m, im, fi, nx, ks, img, foc, v),
  +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}) ->
  D.PostB(False{}, Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, rest, m, nx, fi, im, pg, lim, inp)), st => Empty,
    s => st2 => D.OutH(v, s, st2), Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(v)), lim):
  OI.out.postb(f, ds, ks, img, foc, pend, rest, m, nx, fi, im, pg, lim, inp, v, ks2, hv, hk,
    PI.is.tm(ds, m, im, fi, nx, ks, img, foc, v, hv))

# PostB, with a weaker next and halt
def postb.map(dn: Bool, o: Cr.Cir.Out, -Q1: Cr.Cir.State -> Type, -Q2: Cr.Cir.State -> Type, -H1: U32 -> Cr.Cir.State -> Type,
  -H2: U32 -> Cr.Cir.State -> Type, -B: Nat, -lim: U32, h: D.PostB(dn, o, Q1, H1, B, lim), q: @st: Cr.Cir.State -> Q1(st) -> Q2(st),
  hh: @s: U32 -> @st: Cr.Cir.State -> H1(s, st) -> H2(s, st)) -> D.PostB(dn, o, Q2, H2, B, lim):
  match o:
    case Cr.Cir.Out.next{st}:
      q(st, h)
    case Cr.Cir.Out.halt{s, st}:
      hh(s, st, h)
    case Cr.Cir.Out.out_of_memory{}:
      h
    case Cr.Cir.Out.trap{}:
      h
    case Cr.Cir.Out.not_done{}:
      h

# b <= max(a, b)
def le_max_r(+a: Nat, +b: Nat) -> N.Le(b, Nat.max(a, b)):
  match a b:
    case 0n _:
      N.le_refl(b)
    case 1n+(+ap) 0n:
      N.le_zero(1n+ap)
    case 1n+(+ap) 1n+(+bp):
      le_max_r(ap, bp)

# the output's budget is within Budget, whose output part is 20 next + |t|
def out.budget(+ds: List<&2, Bk.Def>, +st: Cr.Cir.State, +nx: U32, +t: Bk.Term, +v: Bk.Term, en: {D.St.next(st) == nx : U32}, et: {v == t : Bk.Term}) ->
  N.Le(Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(v)), D.Budget(ds, st, t)):
  +A = Nat.add(Nat.mul(20n, U32.to_nat(D.St.next(st))), Pg.Term.size(t))
  N.le_rw_l(A, Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(v)), D.Budget(ds, st, t),
    Equal.trans(Nat, A, Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(t)), Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(v)),
      Equal.cong(U32, Nat, x => Nat.add(Nat.mul(20n, U32.to_nat(x)), Pg.Term.size(t)), D.St.next(st), nx, en),
      Equal.cong(Bk.Term, Nat, u => Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(u)), t, v, Equal.sym(Bk.Term, v, t, et))),
    le_max_r(D.Need.bytes(ds, st, t), A))

# mode 1, no frame, the focus' value v the whole term t: M.out halts as HR
# says, or runs out of memory within the output's budget; with some fuel it
# ends
def out.mv(+ds: List<&2, Bk.Def>, +ks: List<&2, List<&2, Word(8n)>>, +img: List<&2, Bk.Term>, +foc: U32, +pend: U32,
  +r4: U32, +r5: U32, +r6: U32, +r7: U32, +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32, +r14: U32, +r15: U32, +r16: U32, +r17: U32, +r18: U32, +r19: U32, +r20: U32, +r21: U32, +r22: U32, +r23: U32, +r24: U32, +r25: U32, +r26: U32, +r27: U32, +r28: U32, +r29: U32, +r30: U32, +r31: U32, +r32: U32, +r33: U32, +r34: U32, +r35: U32, +r36: U32, +r37: U32, +r38: U32, +r39: U32, +r40: U32, +r41: U32, +r42: U32, +r43: U32, +r44: U32, +r45: U32, +r46: U32, +r47: U32, +r48: U32, +r49: U32, +r50: U32, +r51: U32, +r52: U32, +r53: U32, +r54: U32, +r55: U32, +r56: U32, +r57: U32, +r58: U32, +r59: U32, +r60: U32, +r61: U32, +r62: U32, +m: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lim: U32, +inp: List<&2, Word(8n)>,
  +t: Bk.Term, +w: Nat, +focus: Bk.Term, +et: {focus == t : Bk.Term},
  +ev: {El.Eval.vals(ds, focus, False{}) == True{} : Bool}, +isf: D.Is(ds, m, im, fi, nx, ks, img, foc, focus),
  +ks2: List<&2, List<&2, Word(8n)>>, +hk: {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}) ->
  K.MV(ds, ks, img, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w):
  +od = out.done(ds, ks, img, foc, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk)
  +f1 = D.Ex.fst(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))), od)
  +hb = out.budget(ds, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), nx, t, focus, {==}, et)
  (+f => (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
      K.out.E(f, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) :
      D.PostB(False{}, _, s => K.MV.next(ds, ks, img, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2), D.Budget(ds, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), D.St.lim(D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)));
      D.postb.wk(False{}, Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), s => K.MV.next(ds, ks, img, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s), s => st2 => D.HR(ds, t, s, st2),
        Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(focus)), D.Budget(ds, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t), lim,
        postb.map(False{}, Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), st => Empty, s => K.MV.next(ds, ks, img, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, s),
          s => st2 => D.OutH(focus, s, st2), s => st2 => D.HR(ds, t, s, st2), Nat.add(Nat.mul(20n, U32.to_nat(nx)), Pg.Term.size(focus)), lim,
          out.postb(f, ds, ks, img, foc, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp, focus, ks2, isf, hk),
          st => h => Empty.absurd(K.MV.next(ds, ks, img, D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w, st), h),
          s => st2 => h => K.hr.eq(ds, focus, t, s, st2, et, K.out.hr(ds, focus, ev, s, st2, h))),
        hb)),
   (f1, (%Equal.sym(Cr.Cir.Out, Cr.Cir.exec(f1, D.B.body(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)), Cr.Cir.exec(f1, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp)),
      K.out.E(f1, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp)) : D.Ends(_);
      D.Ex.snd(Nat, f => D.Ends(Cr.Cir.exec(f, Mc.M.out(), D.S(foc, 1, 0, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp))), od))))

def K.mv.out(ds, ks, img, foc, sp, pend, rest, m, nx, fi, im, pg, lim, inp, t, w, fs, ps, focus, iv):
  match rest:
    case D.R59{+r4, +r5, +r6, +r7, +r8, +r9, +r10, +r11, +r12, +r13, +r14, +r15, +r16, +r17, +r18, +r19, +r20, +r21, +r22, +r23, +r24, +r25, +r26, +r27, +r28, +r29, +r30, +r31, +r32, +r33, +r34, +r35, +r36, +r37, +r38, +r39, +r40, +r41, +r42, +r43, +r44, +r45, +r46, +r47, +r48, +r49, +r50, +r51, +r52, +r53, +r54, +r55, +r56, +r57, +r58, +r59, +r60, +r61, +r62}:
      match iv:
        case Tuple{Tuple{+et, Tuple{_, Tuple{+evv, Tuple{_, Tuple{_, Tuple{+isf, Tuple{+frs, Tuple{_, Tuple{+io, Tuple{_, _}}}}}}}}}}, _}:
          +k = K.img.ks(ds, ks, img, m, im, fi, nx, io)
          %Equal.sym(U32, sp, 0, frs) : K.MV(ds, ks, img, D.S(foc, 1, _, pend, D.R59{r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62}, m, nx, fi, im, pg, lim, inp), t, w)
          out.mv(ds, ks, img, foc, pend, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, m, nx, fi, im, pg, lim, inp, t, w, focus, et, evv, isf,
            D.Ex.fst(List<&2, List<&2, Word(8n)>>, ks2 => {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}, k),
            D.Ex.snd(List<&2, List<&2, Word(8n)>>, ks2 => {ks == Mc.Img.known(ks2) : List<&2, List<&2, Word(8n)>>}, k))
