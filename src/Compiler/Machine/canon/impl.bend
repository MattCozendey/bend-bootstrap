# compiler: layer B5, the proofs of canon/spec.bend
# =================================================
#
# One def per law of canon/spec.bend. The route for the open ones: a relation
# Rel(d, t, u) (the same shape; a variable bound below d + e is the same in
# both; above, both are free), kept by Term.shift, Term.subst, Env.sub,
# Eval.walk, Eval.vals, Eval.callWalk, Eval.redex and Eval.step; and
# Canon.term(t, d) = Canon.term(u, d) iff Rel(d, t, u).

import Base
import ../../../Shared/shared.bend as Sd
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ./spec.bend as C

# Kit
# ---

def canon.bool.t(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def canon.ff(-G: Type, e: {False{} == True{} : Bool}) -> G:
  Empty.absurd(G, (%e : canon.bool.t(_); Unit{}))

def canon.and.l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def canon.and.r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      canon.ff({b == True{} : Bool}, h)

def canon.nat.is_eq.ok(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      canon.ff({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      canon.ff({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, canon.nat.is_eq.ok(p, q, e))

def canon.quan.is_eq.ok(p: Bk.Quan, q: Bk.Quan, e: {C.Quan.is_eq(p, q) == True{} : Bool}) -> {p == q : Bk.Quan}:
  match p q:
    case Bk.Quan.Q0{} Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{} Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{} Bk.Quan.Q2{}:
      {==}
    case Bk.Quan.Q0{} Bk.Quan.Q1{}:
      canon.ff({Bk.Quan.Q0{} == Bk.Quan.Q1{} : Bk.Quan}, e)
    case Bk.Quan.Q0{} Bk.Quan.Q2{}:
      canon.ff({Bk.Quan.Q0{} == Bk.Quan.Q2{} : Bk.Quan}, e)
    case Bk.Quan.Q1{} Bk.Quan.Q0{}:
      canon.ff({Bk.Quan.Q1{} == Bk.Quan.Q0{} : Bk.Quan}, e)
    case Bk.Quan.Q1{} Bk.Quan.Q2{}:
      canon.ff({Bk.Quan.Q1{} == Bk.Quan.Q2{} : Bk.Quan}, e)
    case Bk.Quan.Q2{} Bk.Quan.Q0{}:
      canon.ff({Bk.Quan.Q2{} == Bk.Quan.Q0{} : Bk.Quan}, e)
    case Bk.Quan.Q2{} Bk.Quan.Q1{}:
      canon.ff({Bk.Quan.Q2{} == Bk.Quan.Q1{} : Bk.Quan}, e)

def canon.fin.ft(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, True{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def canon.fin.tf(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def canon.fin.ff(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def canon.fin.tt(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, True{}, c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def canon.word.cmp.ok(+n: Nat, +a: Word(n), +b: Word(n), e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          +ht = Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
            True{}, Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))), Cmp.is_eq(Word.cmp(p, at, bt)),
              canon.fin.ff(Word.cmp(p, at, bt))), e)
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, at, bt, canon.word.cmp.ok(p, at, bt, ht))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          canon.ff({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)},
            Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), False{},
              Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), True{}, e), canon.fin.ft(Word.cmp(p, at, bt)))))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          canon.ff({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)},
            Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), False{},
              Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), True{}, e), canon.fin.tf(Word.cmp(p, at, bt)))))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          +ht = Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            True{}, Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))), Cmp.is_eq(Word.cmp(p, at, bt)),
              canon.fin.tt(Word.cmp(p, at, bt))), e)
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, at, bt, canon.word.cmp.ok(p, at, bt, ht))

def canon.word.cmp.refl(+n: Nat, +w: Word(n)) -> {Cmp.is_eq(Word.cmp(n, w, w)) == True{} : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, t))),
            Cmp.is_eq(Word.cmp(p, t, t)), True{}, canon.fin.ff(Word.cmp(p, t, t)), canon.word.cmp.refl(p, t))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, t, t))),
            Cmp.is_eq(Word.cmp(p, t, t)), True{}, canon.fin.tt(Word.cmp(p, t, t)), canon.word.cmp.refl(p, t))

def canon.name.is_eq.ok(+a: List<&2, Word(8n)>, +b: List<&2, Word(8n)>, +e: {Sd.Name.is_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Word(8n)>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      +hx = canon.and.l(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), e)
      +hxs = canon.and.r(Sd.Byte.is_eq(x, y), Sd.Name.is_eq(xs, ys), e)
      +ex = canon.word.cmp.ok(8n, x, y, hx)
      +hrest = canon.name.is_eq.ok(xs, ys, hxs)
      Equal.trans(List<&2, Word(8n)>, Con{x, xs}, Con{y, xs}, Con{y, ys},
        Equal.cong(Word(8n), List<&2, Word(8n)>, z => Con{z, xs}, x, y, ex),
        Equal.cong(List<&2, Word(8n)>, List<&2, Word(8n)>, z => Con{y, z}, xs, ys, hrest))
    case Nil{} Con{y, ys}:
      canon.ff({Nil{} == Con{y, ys} : List<&2, Word(8n)>}, e)
    case Con{x, xs} Nil{}:
      canon.ff({Con{x, xs} == Nil{} : List<&2, Word(8n)>}, e)

def canon.names.is_eq.ok(+a: List<&2, List<&2, Word(8n)>>, +b: List<&2, List<&2, Word(8n)>>,
  +e: {C.Names.is_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, List<&2, Word(8n)>>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      +hx = canon.and.l(Sd.Name.is_eq(x, y), C.Names.is_eq(xs, ys), e)
      +hxs = canon.and.r(Sd.Name.is_eq(x, y), C.Names.is_eq(xs, ys), e)
      +ex = canon.name.is_eq.ok(x, y, hx)
      +hrest = canon.names.is_eq.ok(xs, ys, hxs)
      Equal.trans(List<&2, List<&2, Word(8n)>>, Con{x, xs}, Con{y, xs}, Con{y, ys},
        Equal.cong(List<&2, Word(8n)>, List<&2, List<&2, Word(8n)>>, z => Con{z, xs}, x, y, ex),
        Equal.cong(List<&2, List<&2, Word(8n)>>, List<&2, List<&2, Word(8n)>>, z => Con{y, z}, xs, ys, hrest))
    case Nil{} Con{y, ys}:
      canon.ff({Nil{} == Con{y, ys} : List<&2, List<&2, Word(8n)>>}, e)
    case Con{x, xs} Nil{}:
      canon.ff({Con{x, xs} == Nil{} : List<&2, List<&2, Word(8n)>>}, e)

def C.term.is_eq_ok(a: Bk.Term, b: Bk.Term, +e: {C.Term.is_eq(a, b) == True{} : Bool}):
  match a b:
    case Bk.Term.Var{i} Bk.Term.Var{j}:
      Equal.cong(Nat, Bk.Term, z => Bk.Term.Var{z}, i, j, canon.nat.is_eq.ok(i, j, e))
    case Bk.Term.Ref{k} Bk.Term.Ref{j}:
      Equal.cong(List<&2, Word(8n)>, Bk.Term, z => Bk.Term.Ref{z}, k, j, canon.name.is_eq.ok(k, j, e))
    case Bk.Term.Ann{x, T} Bk.Term.Ann{y, U}:
      hx = canon.and.l(C.Term.is_eq(x, y), C.Term.is_eq(T, U), e)
      hT = canon.and.r(C.Term.is_eq(x, y), C.Term.is_eq(T, U), e)
      Equal.trans(Bk.Term, Bk.Term.Ann{x, T}, Bk.Term.Ann{y, T}, Bk.Term.Ann{y, U},
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Ann{z, T}, x, y, C.term.is_eq_ok(x, y, hx)),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Ann{y, z}, T, U, C.term.is_eq_ok(T, U, hT)))
    case Bk.Term.Let{q, v, f} Bk.Term.Let{p, w, g}:
      hq = canon.and.l(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(v, w), C.Term.is_eq(f, g)), e)
      hrest = canon.and.r(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(v, w), C.Term.is_eq(f, g)), e)
      hv = canon.and.l(C.Term.is_eq(v, w), C.Term.is_eq(f, g), hrest)
      hf = canon.and.r(C.Term.is_eq(v, w), C.Term.is_eq(f, g), hrest)
      +eqQ = canon.quan.is_eq.ok(q, p, hq)
      +eqV = C.term.is_eq_ok(v, w, hv)
      +eqF = C.term.is_eq_ok(f, g, hf)
      Equal.trans(Bk.Term, Bk.Term.Let{q, v, f}, Bk.Term.Let{p, v, f}, Bk.Term.Let{p, w, f},
        Equal.trans(Bk.Term, Bk.Term.Let{p, v, f}, Bk.Term.Let{p, w, f}, Bk.Term.Let{p, w, g},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Let{z, v, f}, q, p, eqQ),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Let{p, z, f}, v, w, eqV)),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Let{p, w, z}, f, g, eqF))
    case Bk.Term.Typ{q} Bk.Term.Typ{p}:
      Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Typ{z}, q, p, C.term.is_eq_ok(q, p, e))
    case Bk.Term.Min{a1, b1} Bk.Term.Min{a2, b2}:
      ha = canon.and.l(C.Term.is_eq(a1, a2), C.Term.is_eq(b1, b2), e)
      hb = canon.and.r(C.Term.is_eq(a1, a2), C.Term.is_eq(b1, b2), e)
      Equal.trans(Bk.Term, Bk.Term.Min{a1, b1}, Bk.Term.Min{a2, b1}, Bk.Term.Min{a2, b2},
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Min{z, b1}, a1, a2, C.term.is_eq_ok(a1, a2, ha)),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Min{a2, z}, b1, b2, C.term.is_eq_ok(b1, b2, hb)))
    case Bk.Term.All{q, A1, B1} Bk.Term.All{p, A2, B2}:
      hq = canon.and.l(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2)), e)
      hrest = canon.and.r(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2)), e)
      hA = canon.and.l(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2), hrest)
      hB = canon.and.r(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2), hrest)
      Equal.trans(Bk.Term, Bk.Term.All{q, A1, B1}, Bk.Term.All{p, A1, B1}, Bk.Term.All{p, A2, B1},
        Equal.trans(Bk.Term, Bk.Term.All{p, A1, B1}, Bk.Term.All{p, A2, B1}, Bk.Term.All{p, A2, B2},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.All{z, A1, B1}, q, p, canon.quan.is_eq.ok(q, p, hq)),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.All{p, z, B1}, A1, A2, C.term.is_eq_ok(A1, A2, hA))),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.All{p, A2, z}, B1, B2, C.term.is_eq_ok(B1, B2, hB)))
    case Bk.Term.Lam{q, f} Bk.Term.Lam{p, g}:
      hq = canon.and.l(C.Quan.is_eq(q, p), C.Term.is_eq(f, g), e)
      hf = canon.and.r(C.Quan.is_eq(q, p), C.Term.is_eq(f, g), e)
      Equal.trans(Bk.Term, Bk.Term.Lam{q, f}, Bk.Term.Lam{p, f}, Bk.Term.Lam{p, g},
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Lam{z, f}, q, p, canon.quan.is_eq.ok(q, p, hq)),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Lam{p, z}, f, g, C.term.is_eq_ok(f, g, hf)))
    case Bk.Term.App{q, f, x} Bk.Term.App{p, g, y}:
      hq = canon.and.l(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(f, g), C.Term.is_eq(x, y)), e)
      hrest = canon.and.r(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(f, g), C.Term.is_eq(x, y)), e)
      hf = canon.and.l(C.Term.is_eq(f, g), C.Term.is_eq(x, y), hrest)
      hx = canon.and.r(C.Term.is_eq(f, g), C.Term.is_eq(x, y), hrest)
      Equal.trans(Bk.Term, Bk.Term.App{q, f, x}, Bk.Term.App{p, f, x}, Bk.Term.App{p, g, x},
        Equal.trans(Bk.Term, Bk.Term.App{p, f, x}, Bk.Term.App{p, g, x}, Bk.Term.App{p, g, y},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.App{z, f, x}, q, p, canon.quan.is_eq.ok(q, p, hq)),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.App{p, z, x}, f, g, C.term.is_eq_ok(f, g, hf))),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.App{p, g, z}, x, y, C.term.is_eq_ok(x, y, hx)))
    case Bk.Term.Sig{q, A1, B1} Bk.Term.Sig{p, A2, B2}:
      hq = canon.and.l(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2)), e)
      hrest = canon.and.r(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2)), e)
      hA = canon.and.l(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2), hrest)
      hB = canon.and.r(C.Term.is_eq(A1, A2), C.Term.is_eq(B1, B2), hrest)
      Equal.trans(Bk.Term, Bk.Term.Sig{q, A1, B1}, Bk.Term.Sig{p, A1, B1}, Bk.Term.Sig{p, A2, B1},
        Equal.trans(Bk.Term, Bk.Term.Sig{p, A1, B1}, Bk.Term.Sig{p, A2, B1}, Bk.Term.Sig{p, A2, B2},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Sig{z, A1, B1}, q, p, canon.quan.is_eq.ok(q, p, hq)),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Sig{p, z, B1}, A1, A2, C.term.is_eq_ok(A1, A2, hA))),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Sig{p, A2, z}, B1, B2, C.term.is_eq_ok(B1, B2, hB)))
    case Bk.Term.Tup{q, a1, b1} Bk.Term.Tup{p, a2, b2}:
      hq = canon.and.l(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(a1, a2), C.Term.is_eq(b1, b2)), e)
      hrest = canon.and.r(C.Quan.is_eq(q, p), Bool.and(C.Term.is_eq(a1, a2), C.Term.is_eq(b1, b2)), e)
      ha = canon.and.l(C.Term.is_eq(a1, a2), C.Term.is_eq(b1, b2), hrest)
      hb = canon.and.r(C.Term.is_eq(a1, a2), C.Term.is_eq(b1, b2), hrest)
      Equal.trans(Bk.Term, Bk.Term.Tup{q, a1, b1}, Bk.Term.Tup{p, a1, b1}, Bk.Term.Tup{p, a2, b1},
        Equal.trans(Bk.Term, Bk.Term.Tup{p, a1, b1}, Bk.Term.Tup{p, a2, b1}, Bk.Term.Tup{p, a2, b2},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Tup{z, a1, b1}, q, p, canon.quan.is_eq.ok(q, p, hq)),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Tup{p, z, b1}, a1, a2, C.term.is_eq_ok(a1, a2, ha))),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Tup{p, a2, z}, b1, b2, C.term.is_eq_ok(b1, b2, hb)))
    case Bk.Term.Prj{h} Bk.Term.Prj{g}:
      Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Prj{z}, h, g, C.term.is_eq_ok(h, g, e))
    case Bk.Term.Enu{ks} Bk.Term.Enu{js}:
      canon.names.is_eq.ok(ks, js, e)
    case Bk.Term.Lab{k} Bk.Term.Lab{j}:
      canon.name.is_eq.ok(k, j, e)
    case Bk.Term.Mat{k, h1, m1} Bk.Term.Mat{j, h2, m2}:
      hk = canon.and.l(Sd.Name.is_eq(k, j), Bool.and(C.Term.is_eq(h1, h2), C.Term.is_eq(m1, m2)), e)
      hrest = canon.and.r(Sd.Name.is_eq(k, j), Bool.and(C.Term.is_eq(h1, h2), C.Term.is_eq(m1, m2)), e)
      hh = canon.and.l(C.Term.is_eq(h1, h2), C.Term.is_eq(m1, m2), hrest)
      hm = canon.and.r(C.Term.is_eq(h1, h2), C.Term.is_eq(m1, m2), hrest)
      Equal.trans(Bk.Term, Bk.Term.Mat{k, h1, m1}, Bk.Term.Mat{j, h1, m1}, Bk.Term.Mat{j, h2, m1},
        Equal.trans(Bk.Term, Bk.Term.Mat{j, h1, m1}, Bk.Term.Mat{j, h2, m1}, Bk.Term.Mat{j, h2, m2},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Mat{z, h1, m1}, k, j, canon.name.is_eq.ok(k, j, hk)),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Mat{j, z, m1}, h1, h2, C.term.is_eq_ok(h1, h2, hh))),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Mat{j, h2, z}, m1, m2, C.term.is_eq_ok(m1, m2, hm)))
    case Bk.Term.Efq{} Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a1, b1, T1} Bk.Term.Eql{a2, b2, T2}:
      hab = canon.and.l(C.Term.is_eq(a1, a2), Bool.and(C.Term.is_eq(b1, b2), C.Term.is_eq(T1, T2)), e)
      hrest = canon.and.r(C.Term.is_eq(a1, a2), Bool.and(C.Term.is_eq(b1, b2), C.Term.is_eq(T1, T2)), e)
      hb = canon.and.l(C.Term.is_eq(b1, b2), C.Term.is_eq(T1, T2), hrest)
      hT = canon.and.r(C.Term.is_eq(b1, b2), C.Term.is_eq(T1, T2), hrest)
      Equal.trans(Bk.Term, Bk.Term.Eql{a1, b1, T1}, Bk.Term.Eql{a2, b1, T1}, Bk.Term.Eql{a2, b2, T1},
        Equal.trans(Bk.Term, Bk.Term.Eql{a2, b1, T1}, Bk.Term.Eql{a2, b2, T1}, Bk.Term.Eql{a2, b2, T2},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Eql{z, b1, T1}, a1, a2, C.term.is_eq_ok(a1, a2, hab)),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Eql{a2, z, T1}, b1, b2, C.term.is_eq_ok(b1, b2, hb))),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Eql{a2, b2, z}, T1, T2, C.term.is_eq_ok(T1, T2, hT)))
    case Bk.Term.Rfl{} Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e1, P1, f1} Bk.Term.Rwt{e2, P2, f2}:
      ha = canon.and.l(C.Term.is_eq(e1, e2), Bool.and(C.Term.is_eq(P1, P2), C.Term.is_eq(f1, f2)), e)
      hrest = canon.and.r(C.Term.is_eq(e1, e2), Bool.and(C.Term.is_eq(P1, P2), C.Term.is_eq(f1, f2)), e)
      hP = canon.and.l(C.Term.is_eq(P1, P2), C.Term.is_eq(f1, f2), hrest)
      hf = canon.and.r(C.Term.is_eq(P1, P2), C.Term.is_eq(f1, f2), hrest)
      Equal.trans(Bk.Term, Bk.Term.Rwt{e1, P1, f1}, Bk.Term.Rwt{e2, P1, f1}, Bk.Term.Rwt{e2, P2, f1},
        Equal.trans(Bk.Term, Bk.Term.Rwt{e2, P1, f1}, Bk.Term.Rwt{e2, P2, f1}, Bk.Term.Rwt{e2, P2, f2},
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Rwt{z, P1, f1}, e1, e2, C.term.is_eq_ok(e1, e2, ha)),
          Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Rwt{e2, z, f1}, P1, P2, C.term.is_eq_ok(P1, P2, hP))),
        Equal.cong(Bk.Term, Bk.Term, z => Bk.Term.Rwt{e2, P2, z}, f1, f2, C.term.is_eq_ok(f1, f2, hf)))
    case _ _:
      ?TODO

def canon.and.i(a: Bool, -b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      canon.ff({Bool.and(False{}, b) == True{} : Bool}, ha)

def canon.byte.is_eq.refl(+b: Word(8n)) -> {Sd.Byte.is_eq(b, b) == True{} : Bool}:
  canon.word.cmp.refl(8n, b)

def canon.name.is_eq.refl(+ks: List<&2, Word(8n)>) -> {Sd.Name.is_eq(ks, ks) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, rest}:
      canon.and.i(Sd.Byte.is_eq(k, k), Sd.Name.is_eq(rest, rest), canon.byte.is_eq.refl(k), canon.name.is_eq.refl(rest))

def canon.names.is_eq.refl(+ks: List<&2, List<&2, Word(8n)>>) -> {C.Names.is_eq(ks, ks) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, rest}:
      canon.and.i(Sd.Name.is_eq(k, k), C.Names.is_eq(rest, rest), canon.name.is_eq.refl(k), canon.names.is_eq.refl(rest))

def canon.quan.is_eq.refl(q: Bk.Quan) -> {C.Quan.is_eq(q, q) == True{} : Bool}:
  match q:
    case Bk.Quan.Q0{}:
      {==}
    case Bk.Quan.Q1{}:
      {==}
    case Bk.Quan.Q2{}:
      {==}

def canon.nat.is_eq.refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      canon.nat.is_eq.refl(p)

def canon.and3(+a: Bool, +b: Bool, -c: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}, +hc: {c == True{} : Bool}) ->
  {Bool.and(Bool.and(a, b), c) == True{} : Bool}:
  +hab = canon.and.i(a, b, ha, hb)
  canon.and.i(Bool.and(a, b), c, hab, hc)

def C.term.is_eq_refl(a):
  match a:
    case Bk.Term.Var{i}:
      canon.nat.is_eq.refl(i)
    case Bk.Term.Ref{k}:
      canon.name.is_eq.refl(k)
    case Bk.Term.Ann{x, T}:
      canon.and.i(C.Term.is_eq(x, x), C.Term.is_eq(T, T), C.term.is_eq_refl(x), C.term.is_eq_refl(T))
    case Bk.Term.Let{q, v, f}:
      canon.and3(C.Quan.is_eq(q, q), C.Term.is_eq(v, v), C.Term.is_eq(f, f), canon.quan.is_eq.refl(q),
        C.term.is_eq_refl(v), C.term.is_eq_refl(f))
    case Bk.Term.Typ{q}:
      C.term.is_eq_refl(q)
    case Bk.Term.Min{a, b}:
      canon.and.i(C.Term.is_eq(a, a), C.Term.is_eq(b, b), C.term.is_eq_refl(a), C.term.is_eq_refl(b))
    case Bk.Term.All{q, A, B}:
      canon.and3(C.Quan.is_eq(q, q), C.Term.is_eq(A, A), C.Term.is_eq(B, B), canon.quan.is_eq.refl(q),
        C.term.is_eq_refl(A), C.term.is_eq_refl(B))
    case Bk.Term.Lam{q, f}:
      canon.and.i(C.Quan.is_eq(q, q), C.Term.is_eq(f, f), canon.quan.is_eq.refl(q), C.term.is_eq_refl(f))
    case Bk.Term.App{q, f, x}:
      canon.and3(C.Quan.is_eq(q, q), C.Term.is_eq(f, f), C.Term.is_eq(x, x), canon.quan.is_eq.refl(q),
        C.term.is_eq_refl(f), C.term.is_eq_refl(x))
    case Bk.Term.Sig{q, A, B}:
      canon.and3(C.Quan.is_eq(q, q), C.Term.is_eq(A, A), C.Term.is_eq(B, B), canon.quan.is_eq.refl(q),
        C.term.is_eq_refl(A), C.term.is_eq_refl(B))
    case Bk.Term.Tup{q, a, b}:
      canon.and3(C.Quan.is_eq(q, q), C.Term.is_eq(a, a), C.Term.is_eq(b, b), canon.quan.is_eq.refl(q),
        C.term.is_eq_refl(a), C.term.is_eq_refl(b))
    case Bk.Term.Prj{h}:
      C.term.is_eq_refl(h)
    case Bk.Term.Enu{ks}:
      canon.names.is_eq.refl(ks)
    case Bk.Term.Lab{k}:
      canon.name.is_eq.refl(k)
    case Bk.Term.Mat{k, h, m}:
      canon.and3(Sd.Name.is_eq(k, k), C.Term.is_eq(h, h), C.Term.is_eq(m, m), canon.name.is_eq.refl(k),
        C.term.is_eq_refl(h), C.term.is_eq_refl(m))
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      canon.and3(C.Term.is_eq(a, a), C.Term.is_eq(b, b), C.Term.is_eq(T, T), C.term.is_eq_refl(a),
        C.term.is_eq_refl(b), C.term.is_eq_refl(T))
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      canon.and3(C.Term.is_eq(e, e), C.Term.is_eq(P, P), C.Term.is_eq(f, f), C.term.is_eq_refl(e),
        C.term.is_eq_refl(P), C.term.is_eq_refl(f))

def C.canon.step(ds, t):
  ?TODO

# CSteps follows Eval.run, from any start, by canon.step at each step
def canon.steps.go(m: Nat, +ds: List<&2, Bk.Def>, r: Maybe<Bk.Term>) ->
  {C.CSteps(m, ds, C.Canon.opt(r)) == C.Canon.opt(El.Eval.run(m, ds, r)) : Maybe<Bk.Term>}:
  match m r:
    case 0n _:
      {==}
    case 1n+k None{}:
      {==}
    case 1n+k Some{+t}:
      %Equal.sym(Maybe<Bk.Term>, C.CStep(ds, C.Canon.term(t, 0n)), C.CStep(ds, t), C.canon.step(ds, t)) :
        {C.CSteps(k, ds, _) == C.Canon.opt(El.Eval.run(k, ds, El.Eval.step(ds, t))) : Maybe<Bk.Term>}
      canon.steps.go(k, ds, El.Eval.step(ds, t))

def C.canon.steps(n, ds, t):
  canon.steps.go(n, ds, Some{t})

def C.canon.result(ds, r):
  ?TODO

def C.canon.size(t, d):
  match t:
    case Bk.Term.Var{i}:
      {==}
    case Bk.Term.Ref{k}:
      {==}
    case Bk.Term.Ann{x, T}:
      %C.canon.size(x, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(x, d)), Pg.Term.size(C.Canon.term(T, d))) == 1n+Nat.add(_, Pg.Term.size(T)) : Nat}
      %C.canon.size(T, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(x, d)), Pg.Term.size(C.Canon.term(T, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(x, d)), _) : Nat}
      {==}
    case Bk.Term.Let{q, v, f}:
      %C.canon.size(v, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(v, d)), Pg.Term.size(C.Canon.term(f, 1n+d))) == 1n+Nat.add(_, Pg.Term.size(f)) : Nat}
      %C.canon.size(f, 1n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(v, d)), Pg.Term.size(C.Canon.term(f, 1n+d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(v, d)), _) : Nat}
      {==}
    case Bk.Term.Typ{q}:
      %C.canon.size(q, d) : {1n+Pg.Term.size(C.Canon.term(q, d)) == 1n+_ : Nat}
      {==}
    case Bk.Term.Min{a, b}:
      %C.canon.size(a, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(_, Pg.Term.size(b)) : Nat}
      %C.canon.size(b, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), _) : Nat}
      {==}
    case Bk.Term.All{q, A, B}:
      %C.canon.size(A, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(_, Pg.Term.size(B)) : Nat}
      %C.canon.size(B, 1n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), _) : Nat}
      {==}
    case Bk.Term.Lam{q, f}:
      %C.canon.size(f, 1n+d) : {1n+Pg.Term.size(C.Canon.term(f, 1n+d)) == 1n+_ : Nat}
      {==}
    case Bk.Term.App{q, f, x}:
      %C.canon.size(f, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(f, d)), Pg.Term.size(C.Canon.term(x, d))) == 1n+Nat.add(_, Pg.Term.size(x)) : Nat}
      %C.canon.size(x, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(f, d)), Pg.Term.size(C.Canon.term(x, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(f, d)), _) : Nat}
      {==}
    case Bk.Term.Sig{q, A, B}:
      %C.canon.size(A, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(_, Pg.Term.size(B)) : Nat}
      %C.canon.size(B, 1n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), Pg.Term.size(C.Canon.term(B, 1n+d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(A, d)), _) : Nat}
      {==}
    case Bk.Term.Tup{q, a, b}:
      %C.canon.size(a, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(_, Pg.Term.size(b)) : Nat}
      %C.canon.size(b, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Pg.Term.size(C.Canon.term(b, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), _) : Nat}
      {==}
    case Bk.Term.Prj{h}:
      %C.canon.size(h, d) : {1n+Pg.Term.size(C.Canon.term(h, d)) == 1n+_ : Nat}
      {==}
    case Bk.Term.Enu{ks}:
      {==}
    case Bk.Term.Lab{k}:
      {==}
    case Bk.Term.Mat{k, h, m}:
      %C.canon.size(h, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(h, d)), Pg.Term.size(C.Canon.term(m, d))) == 1n+Nat.add(_, Pg.Term.size(m)) : Nat}
      %C.canon.size(m, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(h, d)), Pg.Term.size(C.Canon.term(m, d))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(h, d)), _) : Nat}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      %C.canon.size(a, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), Pg.Term.size(C.Canon.term(T, d)))) == 1n+Nat.add(_, Nat.add(Pg.Term.size(b), Pg.Term.size(T))) : Nat}
      %C.canon.size(b, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), Pg.Term.size(C.Canon.term(T, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(_, Pg.Term.size(T))) : Nat}
      %C.canon.size(T, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), Pg.Term.size(C.Canon.term(T, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(a, d)), Nat.add(Pg.Term.size(C.Canon.term(b, d)), _)) : Nat}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      %C.canon.size(e, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), Pg.Term.size(C.Canon.term(f, d)))) == 1n+Nat.add(_, Nat.add(Pg.Term.size(P), Pg.Term.size(f))) : Nat}
      %C.canon.size(P, 2n+d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), Pg.Term.size(C.Canon.term(f, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(_, Pg.Term.size(f))) : Nat}
      %C.canon.size(f, d) : {1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), Pg.Term.size(C.Canon.term(f, d)))) == 1n+Nat.add(Pg.Term.size(C.Canon.term(e, d)), Nat.add(Pg.Term.size(C.Canon.term(P, 2n+d)), _)) : Nat}
      {==}

def C.canon.vals(ds, t, d, a):
  ?TODO

def C.canon.data(t, d):
  match t:
    case Bk.Term.Var{i}:
      {==}
    case Bk.Term.Ref{k}:
      {==}
    case Bk.Term.Ann{x, T}:
      {==}
    case Bk.Term.Let{q, v, f}:
      {==}
    case Bk.Term.Typ{q}:
      {==}
    case Bk.Term.Min{a, b}:
      {==}
    case Bk.Term.All{q, A, B}:
      {==}
    case Bk.Term.Lam{q, f}:
      {==}
    case Bk.Term.App{q, f, x}:
      {==}
    case Bk.Term.Sig{q, A, B}:
      {==}
    case Bk.Term.Tup{q, a, b}:
      %C.canon.data(a, d) : {(Bool.not(El.Quan.live(q)) || El.Term.is_data(C.Canon.term(a, d))) && El.Term.is_data(C.Canon.term(b, d)) == (Bool.not(El.Quan.live(q)) || _) && El.Term.is_data(b) : Bool}
      %C.canon.data(b, d) : {(Bool.not(El.Quan.live(q)) || El.Term.is_data(C.Canon.term(a, d))) && El.Term.is_data(C.Canon.term(b, d)) == (Bool.not(El.Quan.live(q)) || El.Term.is_data(C.Canon.term(a, d))) && _ : Bool}
      {==}
    case Bk.Term.Prj{h}:
      {==}
    case Bk.Term.Enu{ks}:
      {==}
    case Bk.Term.Lab{k}:
      {==}
    case Bk.Term.Mat{k, h, m}:
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      {==}

# Canon.var is its own canonical form
def canon.var.dd(b: Bool, +d: Nat) -> {C.Canon.var(b, d, d) == d : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def canon.var.idem(lt: Bool, +i: Nat, +d: Nat, e: {Nat.is_lt(i, d) == lt : Bool}) ->
  {C.Canon.var(Nat.is_lt(C.Canon.var(lt, i, d), d), C.Canon.var(lt, i, d), d) == C.Canon.var(lt, i, d) : Nat}:
  match lt:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(i, d), True{}, e) : {C.Canon.var(_, i, d) == i : Nat}
      {==}
    case False{}:
      canon.var.dd(Nat.is_lt(d, d), d)

def C.canon.idem(t, d):
  match t:
    case Bk.Term.Var{+i}:
      Equal.cong(Nat, Bk.Term, n => Bk.Term.Var{n}, C.Canon.var(Nat.is_lt(C.Canon.var(Nat.is_lt(i, d), i, d), d), C.Canon.var(Nat.is_lt(i, d), i, d), d),
        C.Canon.var(Nat.is_lt(i, d), i, d), canon.var.idem(Nat.is_lt(i, d), i, d, {==}))
    case Bk.Term.Ref{k}:
      {==}
    case Bk.Term.Ann{x, T}:
      %C.canon.idem(x, d) : {Bk.Term.Ann{C.Canon.term(C.Canon.term(x, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Ann{_, C.Canon.term(T, d)} : Bk.Term}
      %C.canon.idem(T, d) : {Bk.Term.Ann{C.Canon.term(C.Canon.term(x, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Ann{C.Canon.term(C.Canon.term(x, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Let{q, v, f}:
      %C.canon.idem(v, d) : {Bk.Term.Let{q, C.Canon.term(C.Canon.term(v, d), d), C.Canon.term(C.Canon.term(f, 1n+d), 1n+d)} == Bk.Term.Let{q, _, C.Canon.term(f, 1n+d)} : Bk.Term}
      %C.canon.idem(f, 1n+d) : {Bk.Term.Let{q, C.Canon.term(C.Canon.term(v, d), d), C.Canon.term(C.Canon.term(f, 1n+d), 1n+d)} == Bk.Term.Let{q, C.Canon.term(C.Canon.term(v, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Typ{q}:
      %C.canon.idem(q, d) : {Bk.Term.Typ{C.Canon.term(C.Canon.term(q, d), d)} == Bk.Term.Typ{_} : Bk.Term}
      {==}
    case Bk.Term.Min{a, b}:
      %C.canon.idem(a, d) : {Bk.Term.Min{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Min{_, C.Canon.term(b, d)} : Bk.Term}
      %C.canon.idem(b, d) : {Bk.Term.Min{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Min{C.Canon.term(C.Canon.term(a, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.All{q, A, B}:
      %C.canon.idem(A, d) : {Bk.Term.All{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.All{q, _, C.Canon.term(B, 1n+d)} : Bk.Term}
      %C.canon.idem(B, 1n+d) : {Bk.Term.All{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.All{q, C.Canon.term(C.Canon.term(A, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Lam{q, f}:
      %C.canon.idem(f, 1n+d) : {Bk.Term.Lam{q, C.Canon.term(C.Canon.term(f, 1n+d), 1n+d)} == Bk.Term.Lam{q, _} : Bk.Term}
      {==}
    case Bk.Term.App{q, f, x}:
      %C.canon.idem(f, d) : {Bk.Term.App{q, C.Canon.term(C.Canon.term(f, d), d), C.Canon.term(C.Canon.term(x, d), d)} == Bk.Term.App{q, _, C.Canon.term(x, d)} : Bk.Term}
      %C.canon.idem(x, d) : {Bk.Term.App{q, C.Canon.term(C.Canon.term(f, d), d), C.Canon.term(C.Canon.term(x, d), d)} == Bk.Term.App{q, C.Canon.term(C.Canon.term(f, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Sig{q, A, B}:
      %C.canon.idem(A, d) : {Bk.Term.Sig{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.Sig{q, _, C.Canon.term(B, 1n+d)} : Bk.Term}
      %C.canon.idem(B, 1n+d) : {Bk.Term.Sig{q, C.Canon.term(C.Canon.term(A, d), d), C.Canon.term(C.Canon.term(B, 1n+d), 1n+d)} == Bk.Term.Sig{q, C.Canon.term(C.Canon.term(A, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Tup{q, a, b}:
      %C.canon.idem(a, d) : {Bk.Term.Tup{q, C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Tup{q, _, C.Canon.term(b, d)} : Bk.Term}
      %C.canon.idem(b, d) : {Bk.Term.Tup{q, C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d)} == Bk.Term.Tup{q, C.Canon.term(C.Canon.term(a, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Prj{h}:
      %C.canon.idem(h, d) : {Bk.Term.Prj{C.Canon.term(C.Canon.term(h, d), d)} == Bk.Term.Prj{_} : Bk.Term}
      {==}
    case Bk.Term.Enu{ks}:
      {==}
    case Bk.Term.Lab{k}:
      {==}
    case Bk.Term.Mat{k, h, m}:
      %C.canon.idem(h, d) : {Bk.Term.Mat{k, C.Canon.term(C.Canon.term(h, d), d), C.Canon.term(C.Canon.term(m, d), d)} == Bk.Term.Mat{k, _, C.Canon.term(m, d)} : Bk.Term}
      %C.canon.idem(m, d) : {Bk.Term.Mat{k, C.Canon.term(C.Canon.term(h, d), d), C.Canon.term(C.Canon.term(m, d), d)} == Bk.Term.Mat{k, C.Canon.term(C.Canon.term(h, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      %C.canon.idem(a, d) : {Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Eql{_, C.Canon.term(b, d), C.Canon.term(T, d)} : Bk.Term}
      %C.canon.idem(b, d) : {Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), _, C.Canon.term(T, d)} : Bk.Term}
      %C.canon.idem(T, d) : {Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), C.Canon.term(C.Canon.term(T, d), d)} == Bk.Term.Eql{C.Canon.term(C.Canon.term(a, d), d), C.Canon.term(C.Canon.term(b, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      %C.canon.idem(e, d) : {Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), C.Canon.term(C.Canon.term(f, d), d)} == Bk.Term.Rwt{_, C.Canon.term(P, 2n+d), C.Canon.term(f, d)} : Bk.Term}
      %C.canon.idem(P, 2n+d) : {Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), C.Canon.term(C.Canon.term(f, d), d)} == Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), _, C.Canon.term(f, d)} : Bk.Term}
      %C.canon.idem(f, d) : {Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), C.Canon.term(C.Canon.term(f, d), d)} == Bk.Term.Rwt{C.Canon.term(C.Canon.term(e, d), d), C.Canon.term(C.Canon.term(P, 2n+d), 2n+d), _} : Bk.Term}
      {==}

def C.canon.start(i):
  ?TODO

def C.canon.subst(t, es, d):
  ?TODO

def C.canon.subst_below(t, es, n, d, hc, hn):
  ?TODO

# a variable below d: the substitution keeps it, and so does the canonical form
def canon.lift.closed(+es: List<&2, Bk.Term>, +d: Nat, +i: Nat, +hc: {Nat.is_lt(i, d) == True{} : Bool}) ->
  {C.Canon.term(El.Term.lift(es, d, i), d) == Bk.Term.Var{i} : Bk.Term}:
  match d:
    case 0n:
      match i:
        case 0n:
          canon.ff({C.Canon.term(El.Term.lift(es, 0n, 0n), 0n) == Bk.Term.Var{0n} : Bk.Term}, hc)
        case 1n+k:
          canon.ff({C.Canon.term(El.Term.lift(es, 0n, 1n+k), 0n) == Bk.Term.Var{1n+k} : Bk.Term}, hc)
    case 1n+p:
      %Equal.sym(Bool, Nat.is_lt(i, 1n+p), True{}, hc) :
        {C.Canon.term(El.Term.lift.at(_, i, El.Term.shift(El.Env.sub(es, Nat.sub(i, 1n+p)), 1n+p, 0n)), 1n+p) == Bk.Term.Var{i} : Bk.Term}
      %Equal.sym(Bool, Nat.is_lt(i, 1n+p), True{}, hc) : {Bk.Term.Var{C.Canon.var(_, i, 1n+p)} == Bk.Term.Var{i} : Bk.Term}
      {==}

def canon.subst_closed.go(+t: Bk.Term, +es: List<&2, Bk.Term>, +d: Nat, +hc: {C.Term.closed(t, d) == True{} : Bool}) ->
  {C.Canon.term(El.Term.subst(t, es, d), d) == t : Bk.Term}:
  match t:
    case Bk.Term.Var{i}:
      canon.lift.closed(es, d, i, hc)
    case Bk.Term.Ref{k}:
      {==}
    case Bk.Term.Ann{x, T}:
      %canon.subst_closed.go(x, es, d, canon.and.l(C.Term.closed(x, d), C.Term.closed(T, d), hc)) : {Bk.Term.Ann{C.Canon.term(El.Term.subst(x, es, d), d), C.Canon.term(El.Term.subst(T, es, d), d)} == Bk.Term.Ann{_, T} : Bk.Term}
      %canon.subst_closed.go(T, es, d, canon.and.r(C.Term.closed(x, d), C.Term.closed(T, d), hc)) : {Bk.Term.Ann{C.Canon.term(El.Term.subst(x, es, d), d), C.Canon.term(El.Term.subst(T, es, d), d)} == Bk.Term.Ann{C.Canon.term(El.Term.subst(x, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Let{q, v, f}:
      %canon.subst_closed.go(v, es, d, canon.and.l(C.Term.closed(v, d), C.Term.closed(f, 1n+d), hc)) : {Bk.Term.Let{q, C.Canon.term(El.Term.subst(v, es, d), d), C.Canon.term(El.Term.subst(f, es, 1n+d), 1n+d)} == Bk.Term.Let{q, _, f} : Bk.Term}
      %canon.subst_closed.go(f, es, 1n+d, canon.and.r(C.Term.closed(v, d), C.Term.closed(f, 1n+d), hc)) : {Bk.Term.Let{q, C.Canon.term(El.Term.subst(v, es, d), d), C.Canon.term(El.Term.subst(f, es, 1n+d), 1n+d)} == Bk.Term.Let{q, C.Canon.term(El.Term.subst(v, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Typ{q}:
      %canon.subst_closed.go(q, es, d, hc) : {Bk.Term.Typ{C.Canon.term(El.Term.subst(q, es, d), d)} == Bk.Term.Typ{_} : Bk.Term}
      {==}
    case Bk.Term.Min{a, b}:
      %canon.subst_closed.go(a, es, d, canon.and.l(C.Term.closed(a, d), C.Term.closed(b, d), hc)) : {Bk.Term.Min{C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d)} == Bk.Term.Min{_, b} : Bk.Term}
      %canon.subst_closed.go(b, es, d, canon.and.r(C.Term.closed(a, d), C.Term.closed(b, d), hc)) : {Bk.Term.Min{C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d)} == Bk.Term.Min{C.Canon.term(El.Term.subst(a, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.All{q, A, B}:
      %canon.subst_closed.go(A, es, d, canon.and.l(C.Term.closed(A, d), C.Term.closed(B, 1n+d), hc)) : {Bk.Term.All{q, C.Canon.term(El.Term.subst(A, es, d), d), C.Canon.term(El.Term.subst(B, es, 1n+d), 1n+d)} == Bk.Term.All{q, _, B} : Bk.Term}
      %canon.subst_closed.go(B, es, 1n+d, canon.and.r(C.Term.closed(A, d), C.Term.closed(B, 1n+d), hc)) : {Bk.Term.All{q, C.Canon.term(El.Term.subst(A, es, d), d), C.Canon.term(El.Term.subst(B, es, 1n+d), 1n+d)} == Bk.Term.All{q, C.Canon.term(El.Term.subst(A, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Lam{q, f}:
      %canon.subst_closed.go(f, es, 1n+d, hc) : {Bk.Term.Lam{q, C.Canon.term(El.Term.subst(f, es, 1n+d), 1n+d)} == Bk.Term.Lam{q, _} : Bk.Term}
      {==}
    case Bk.Term.App{q, f, x}:
      %canon.subst_closed.go(f, es, d, canon.and.l(C.Term.closed(f, d), C.Term.closed(x, d), hc)) : {Bk.Term.App{q, C.Canon.term(El.Term.subst(f, es, d), d), C.Canon.term(El.Term.subst(x, es, d), d)} == Bk.Term.App{q, _, x} : Bk.Term}
      %canon.subst_closed.go(x, es, d, canon.and.r(C.Term.closed(f, d), C.Term.closed(x, d), hc)) : {Bk.Term.App{q, C.Canon.term(El.Term.subst(f, es, d), d), C.Canon.term(El.Term.subst(x, es, d), d)} == Bk.Term.App{q, C.Canon.term(El.Term.subst(f, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Sig{q, A, B}:
      %canon.subst_closed.go(A, es, d, canon.and.l(C.Term.closed(A, d), C.Term.closed(B, 1n+d), hc)) : {Bk.Term.Sig{q, C.Canon.term(El.Term.subst(A, es, d), d), C.Canon.term(El.Term.subst(B, es, 1n+d), 1n+d)} == Bk.Term.Sig{q, _, B} : Bk.Term}
      %canon.subst_closed.go(B, es, 1n+d, canon.and.r(C.Term.closed(A, d), C.Term.closed(B, 1n+d), hc)) : {Bk.Term.Sig{q, C.Canon.term(El.Term.subst(A, es, d), d), C.Canon.term(El.Term.subst(B, es, 1n+d), 1n+d)} == Bk.Term.Sig{q, C.Canon.term(El.Term.subst(A, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Tup{q, a, b}:
      %canon.subst_closed.go(a, es, d, canon.and.l(C.Term.closed(a, d), C.Term.closed(b, d), hc)) : {Bk.Term.Tup{q, C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d)} == Bk.Term.Tup{q, _, b} : Bk.Term}
      %canon.subst_closed.go(b, es, d, canon.and.r(C.Term.closed(a, d), C.Term.closed(b, d), hc)) : {Bk.Term.Tup{q, C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d)} == Bk.Term.Tup{q, C.Canon.term(El.Term.subst(a, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Prj{h}:
      %canon.subst_closed.go(h, es, d, hc) : {Bk.Term.Prj{C.Canon.term(El.Term.subst(h, es, d), d)} == Bk.Term.Prj{_} : Bk.Term}
      {==}
    case Bk.Term.Enu{ks}:
      {==}
    case Bk.Term.Lab{k}:
      {==}
    case Bk.Term.Mat{k, h, m}:
      %canon.subst_closed.go(h, es, d, canon.and.l(C.Term.closed(h, d), C.Term.closed(m, d), hc)) : {Bk.Term.Mat{k, C.Canon.term(El.Term.subst(h, es, d), d), C.Canon.term(El.Term.subst(m, es, d), d)} == Bk.Term.Mat{k, _, m} : Bk.Term}
      %canon.subst_closed.go(m, es, d, canon.and.r(C.Term.closed(h, d), C.Term.closed(m, d), hc)) : {Bk.Term.Mat{k, C.Canon.term(El.Term.subst(h, es, d), d), C.Canon.term(El.Term.subst(m, es, d), d)} == Bk.Term.Mat{k, C.Canon.term(El.Term.subst(h, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Efq{}:
      {==}
    case Bk.Term.Eql{a, b, T}:
      %canon.subst_closed.go(a, es, d, canon.and.l(C.Term.closed(a, d), C.Term.closed(b, d), canon.and.l(Bool.and(C.Term.closed(a, d), C.Term.closed(b, d)), C.Term.closed(T, d), hc))) : {Bk.Term.Eql{C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d), C.Canon.term(El.Term.subst(T, es, d), d)} == Bk.Term.Eql{_, b, T} : Bk.Term}
      %canon.subst_closed.go(b, es, d, canon.and.r(C.Term.closed(a, d), C.Term.closed(b, d), canon.and.l(Bool.and(C.Term.closed(a, d), C.Term.closed(b, d)), C.Term.closed(T, d), hc))) : {Bk.Term.Eql{C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d), C.Canon.term(El.Term.subst(T, es, d), d)} == Bk.Term.Eql{C.Canon.term(El.Term.subst(a, es, d), d), _, T} : Bk.Term}
      %canon.subst_closed.go(T, es, d, canon.and.r(Bool.and(C.Term.closed(a, d), C.Term.closed(b, d)), C.Term.closed(T, d), hc)) : {Bk.Term.Eql{C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d), C.Canon.term(El.Term.subst(T, es, d), d)} == Bk.Term.Eql{C.Canon.term(El.Term.subst(a, es, d), d), C.Canon.term(El.Term.subst(b, es, d), d), _} : Bk.Term}
      {==}
    case Bk.Term.Rfl{}:
      {==}
    case Bk.Term.Rwt{e, P, f}:
      %canon.subst_closed.go(e, es, d, canon.and.l(C.Term.closed(e, d), C.Term.closed(P, 2n+d), canon.and.l(Bool.and(C.Term.closed(e, d), C.Term.closed(P, 2n+d)), C.Term.closed(f, d), hc))) : {Bk.Term.Rwt{C.Canon.term(El.Term.subst(e, es, d), d), C.Canon.term(El.Term.subst(P, es, 2n+d), 2n+d), C.Canon.term(El.Term.subst(f, es, d), d)} == Bk.Term.Rwt{_, P, f} : Bk.Term}
      %canon.subst_closed.go(P, es, 2n+d, canon.and.r(C.Term.closed(e, d), C.Term.closed(P, 2n+d), canon.and.l(Bool.and(C.Term.closed(e, d), C.Term.closed(P, 2n+d)), C.Term.closed(f, d), hc))) : {Bk.Term.Rwt{C.Canon.term(El.Term.subst(e, es, d), d), C.Canon.term(El.Term.subst(P, es, 2n+d), 2n+d), C.Canon.term(El.Term.subst(f, es, d), d)} == Bk.Term.Rwt{C.Canon.term(El.Term.subst(e, es, d), d), _, f} : Bk.Term}
      %canon.subst_closed.go(f, es, d, canon.and.r(Bool.and(C.Term.closed(e, d), C.Term.closed(P, 2n+d)), C.Term.closed(f, d), hc)) : {Bk.Term.Rwt{C.Canon.term(El.Term.subst(e, es, d), d), C.Canon.term(El.Term.subst(P, es, 2n+d), 2n+d), C.Canon.term(El.Term.subst(f, es, d), d)} == Bk.Term.Rwt{C.Canon.term(El.Term.subst(e, es, d), d), C.Canon.term(El.Term.subst(P, es, 2n+d), 2n+d), _} : Bk.Term}
      {==}

def C.canon.subst_closed(t, es, d, hc):
  canon.subst_closed.go(t, es, d, hc)

def C.canon.lift(es, k, j, hc):
  ?TODO
