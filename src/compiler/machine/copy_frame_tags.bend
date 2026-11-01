# compiler: the copy's frames, tag by tag
# =======================================
#
# A frame of the walk (proof_copy_walk.bend) copies a source cell of the tag
# tg, of the term T0 (Fr.src: T.tm.cell with its parts' terms t2, t3, t4).
# Once each part k is copied to Mo.F of its term at the depth d + Tg.b(tg, k),
# the new cell, of the same tag, quantity and name, holds Mo.F(T0, d)
# (Tg.cg). Mo.F commutes with each former by its definition (F.*).
import Base
import ../../book/impl.bend as Bk
import ./cell_terms.bend as T
import ../need_big.bend as N
import ./copy_substitution.bend as D
import ./copy_kit.bend as K
import ./copy_walk.bend as W

def Tg.some(-a: Bk.Term, -b: Bk.Term, e: {Some{a} == Some{b}: Maybe<&2, Bk.Term>}) -> {a == b: Bk.Term}:
  Equal.cong(Maybe<&2, Bk.Term>, Bk.Term, x => Maybe.default(&2, Bk.Term, x, a), Some{a}, Some{b}, e)

def Tg.ns(-b: Bk.Term, -G: Type, e: {None{} == Some{b}: Maybe<&2, Bk.Term>}) -> G:
  Empty.absurd(
    G,
    N.true_ne_false(
      Equal.cong(Maybe<&2, Bk.Term>, Bool, x => Maybe.is_none(&2, Bk.Term, x), None{}, Some{b}, e)
    )
  )

def Tg.add1(d: Nat) -> {Nat.add(d, 1n) == 1n+d: Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, Tg.add1(p)): {1n+_ == 2n+p: Nat}
      {==}

def Tg.add2(d: Nat) -> {Nat.add(d, 2n) == 2n+d: Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 2n), 2n+p, Tg.add2(p)): {1n+_ == 3n+p: Nat}
      {==}

# Mo.F of each former
def F.Ann(
  mo: D.Mo,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(mo, Bk.Term.Ann{a2, a3}, d) == Bk.Term.Ann{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Let(
  mo: D.Mo,
  +q: Bk.Quan,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.Let{q, a2, a3},
    d
  )
    == Bk.Term.Let{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 1n+d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Typ(
  mo: D.Mo,
  +a2: Bk.Term,
  +d: Nat
) -> {D.Mo.F(mo, Bk.Term.Typ{a2}, d) == Bk.Term.Typ{D.Mo.F(mo, a2, d)}: Bk.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Min(
  mo: D.Mo,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(mo, Bk.Term.Min{a2, a3}, d) == Bk.Term.Min{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.All(
  mo: D.Mo,
  +q: Bk.Quan,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.All{q, a2, a3},
    d
  )
    == Bk.Term.All{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 1n+d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Lam(
  mo: D.Mo,
  +q: Bk.Quan,
  +a2: Bk.Term,
  +d: Nat
) -> {D.Mo.F(mo, Bk.Term.Lam{q, a2}, d) == Bk.Term.Lam{q, D.Mo.F(mo, a2, 1n+d)}: Bk.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.App(
  mo: D.Mo,
  +q: Bk.Quan,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.App{q, a2, a3},
    d
  )
    == Bk.Term.App{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Sig(
  mo: D.Mo,
  +q: Bk.Quan,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.Sig{q, a2, a3},
    d
  )
    == Bk.Term.Sig{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 1n+d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Tup(
  mo: D.Mo,
  +q: Bk.Quan,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.Tup{q, a2, a3},
    d
  )
    == Bk.Term.Tup{q, D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Prj(
  mo: D.Mo,
  +a2: Bk.Term,
  +d: Nat
) -> {D.Mo.F(mo, Bk.Term.Prj{a2}, d) == Bk.Term.Prj{D.Mo.F(mo, a2, d)}: Bk.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Eql(
  mo: D.Mo,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +a4: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.Eql{a2, a3, a4},
    d
  )
    == Bk.Term.Eql{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, d), D.Mo.F(mo, a4, d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.Rwt(
  mo: D.Mo,
  +a2: Bk.Term,
  +a3: Bk.Term,
  +a4: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.Rwt{a2, a3, a4},
    d
  )
    == Bk.Term.Rwt{D.Mo.F(mo, a2, d), D.Mo.F(mo, a3, 2n+d), D.Mo.F(mo, a4, d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.mat(
  mo: D.Mo,
  +k: List<&2, Word(8n)>,
  +a3: Bk.Term,
  +a4: Bk.Term,
  +d: Nat
) -> {
  D.Mo.F(
    mo,
    Bk.Term.Mat{k, a3, a4},
    d
  )
    == Bk.Term.Mat{k, D.Mo.F(mo, a3, d), D.Mo.F(mo, a4, d)}: Bk.Term
}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.lab(
  mo: D.Mo,
  +k: List<&2, Word(8n)>,
  +d: Nat
) -> {D.Mo.F(mo, Bk.Term.Lab{k}, d) == Bk.Term.Lab{k}: Bk.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.efq(mo: D.Mo, +d: Nat) -> {D.Mo.F(mo, Bk.Term.Efq{}, d) == Bk.Term.Efq{}: Bk.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

def F.rfl(mo: D.Mo, +d: Nat) -> {D.Mo.F(mo, Bk.Term.Rfl{}, d) == Bk.Term.Rfl{}: Bk.Term}:
  match mo:
    case D.Mo.shift{_}:
      {==}
    case D.Mo.subst{_}:
      {==}

# the frames by tag
def Tg.c2(
  +mo: D.Mo,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Ann{t2, t3} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Ann{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Ann{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Ann{t2, t3}, d),
    Bk.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.Ann(mo, t2, t3, d)
  ): {
    Some{
      Bk.Term.Ann{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Ann{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{Bk.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{Bk.Term.Ann{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c3(
  +mo: D.Mo,
  +q: Bk.Quan,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Let{q, t2, t3} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Let{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Let{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Let{q, t2, t3}, d),
    Bk.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)},
    F.Let(mo, q, t2, t3, d)
  ): {
    Some{
      Bk.Term.Let{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Let{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{Bk.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      Bk.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{Bk.Term.Let{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c4(
  +mo: D.Mo,
  +t2: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Typ{t2} == T0: Bk.Term}
) -> {
  Some{Bk.Term.Typ{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{Bk.Term.Typ{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Typ{t2}, d),
    Bk.Term.Typ{D.Mo.F(mo, t2, d)},
    F.Typ(mo, t2, d)
  ): {Some{Bk.Term.Typ{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{_}: Maybe<&2, Bk.Term>}
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {Some{Bk.Term.Typ{D.Mo.F(mo, t2, _)}} == Some{Bk.Term.Typ{D.Mo.F(mo, t2, d)}}: Maybe<&2, Bk.Term>}
  {==}

def Tg.c5(
  +mo: D.Mo,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Min{t2, t3} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Min{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Min{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Min{t2, t3}, d),
    Bk.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.Min(mo, t2, t3, d)
  ): {
    Some{
      Bk.Term.Min{D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Min{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{Bk.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{Bk.Term.Min{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c6(
  +mo: D.Mo,
  +q: Bk.Quan,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.All{q, t2, t3} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.All{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.All{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.All{q, t2, t3}, d),
    Bk.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)},
    F.All(mo, q, t2, t3, d)
  ): {
    Some{
      Bk.Term.All{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.All{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{Bk.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      Bk.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{Bk.Term.All{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c7(
  +mo: D.Mo,
  +q: Bk.Quan,
  +t2: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Lam{q, t2} == T0: Bk.Term}
) -> {
  Some{Bk.Term.Lam{q, D.Mo.F(mo, t2, Nat.add(d, 1n))}} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{Bk.Term.Lam{q, D.Mo.F(mo, t2, Nat.add(d, 1n))}} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Lam{q, t2}, d),
    Bk.Term.Lam{q, D.Mo.F(mo, t2, 1n+d)},
    F.Lam(mo, q, t2, d)
  ): {Some{Bk.Term.Lam{q, D.Mo.F(mo, t2, Nat.add(d, 1n))}} == Some{_}: Maybe<&2, Bk.Term>}
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      Bk.Term.Lam{q, D.Mo.F(mo, t2, _)}
    }
      == Some{Bk.Term.Lam{q, D.Mo.F(mo, t2, 1n+d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c8(
  +mo: D.Mo,
  +q: Bk.Quan,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.App{q, t2, t3} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.App{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.App{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.App{q, t2, t3}, d),
    Bk.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.App(mo, q, t2, t3, d)
  ): {
    Some{
      Bk.Term.App{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.App{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{Bk.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{Bk.Term.App{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c9(
  +mo: D.Mo,
  +q: Bk.Quan,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Sig{q, t2, t3} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Sig{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Sig{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Sig{q, t2, t3}, d),
    Bk.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)},
    F.Sig(mo, q, t2, t3, d)
  ): {
    Some{
      Bk.Term.Sig{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Sig{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 1n))}
    }
      == Some{Bk.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 1n),
    1n+d,
    Tg.add1(d)
  ): {
    Some{
      Bk.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{Bk.Term.Sig{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 1n+d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c10(
  +mo: D.Mo,
  +q: Bk.Quan,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Tup{q, t2, t3} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Tup{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Tup{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Tup{q, t2, t3}, d),
    Bk.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)},
    F.Tup(mo, q, t2, t3, d)
  ): {
    Some{
      Bk.Term.Tup{q, D.Mo.F(mo, t2, Nat.add(d, 0n)), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Tup{q, D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n))}
    }
      == Some{Bk.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _)}
    }
      == Some{Bk.Term.Tup{q, D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d)}}: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c11(
  +mo: D.Mo,
  +t2: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Prj{t2} == T0: Bk.Term}
) -> {
  Some{Bk.Term.Prj{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{Bk.Term.Prj{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Prj{t2}, d),
    Bk.Term.Prj{D.Mo.F(mo, t2, d)},
    F.Prj(mo, t2, d)
  ): {Some{Bk.Term.Prj{D.Mo.F(mo, t2, Nat.add(d, 0n))}} == Some{_}: Maybe<&2, Bk.Term>}
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {Some{Bk.Term.Prj{D.Mo.F(mo, t2, _)}} == Some{Bk.Term.Prj{D.Mo.F(mo, t2, d)}}: Maybe<&2, Bk.Term>}
  {==}

def Tg.c16(
  +mo: D.Mo,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +t4: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Eql{t2, t3, t4} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Eql{
      D.Mo.F(mo, t2, Nat.add(d, 0n)),
      D.Mo.F(mo, t3, Nat.add(d, 0n)),
      D.Mo.F(mo, t4, Nat.add(d, 0n))
    }
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Eql{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 0n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Eql{t2, t3, t4}, d),
    Bk.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)},
    F.Eql(mo, t2, t3, t4, d)
  ): {
    Some{
      Bk.Term.Eql{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 0n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Eql{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        Bk.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        Bk.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, _)}
    }
      == Some{
        Bk.Term.Eql{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c18(
  +mo: D.Mo,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +t4: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Rwt{t2, t3, t4} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Rwt{
      D.Mo.F(mo, t2, Nat.add(d, 0n)),
      D.Mo.F(mo, t3, Nat.add(d, 2n)),
      D.Mo.F(mo, t4, Nat.add(d, 0n))
    }
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Rwt{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 2n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Rwt{t2, t3, t4}, d),
    Bk.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)},
    F.Rwt(mo, t2, t3, t4, d)
  ): {
    Some{
      Bk.Term.Rwt{
        D.Mo.F(mo, t2, Nat.add(d, 0n)),
        D.Mo.F(mo, t3, Nat.add(d, 2n)),
        D.Mo.F(mo, t4, Nat.add(d, 0n))
      }
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Rwt{D.Mo.F(mo, t2, _), D.Mo.F(mo, t3, Nat.add(d, 2n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        Bk.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 2n),
    2n+d,
    Tg.add2(d)
  ): {
    Some{
      Bk.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, _), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{
        Bk.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, _)}
    }
      == Some{
        Bk.Term.Rwt{D.Mo.F(mo, t2, d), D.Mo.F(mo, t3, 2n+d), D.Mo.F(mo, t4, d)}
      }: Maybe<&2, Bk.Term>
  }
  {==}

def Tg.c0(
  +mo: D.Mo,
  +d: Nat,
  -T0: Bk.Term,
  +a: Bk.Term,
  ea: {D.Mo.F(mo, a, d) == a: Bk.Term},
  e: {a == T0: Bk.Term}
) -> {Some{a} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>}:
  %e: {Some{a} == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>}
  %Equal.sym(Bk.Term, D.Mo.F(mo, a, d), a, ea): {Some{a} == Some{_}: Maybe<&2, Bk.Term>}
  {==}

def Tg.c14(
  +mo: D.Mo,
  +k: List<&2, Word(8n)>,
  +t3: Bk.Term,
  +t4: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  e: {Bk.Term.Mat{k, t3, t4} == T0: Bk.Term}
) -> {
  Some{
    Bk.Term.Mat{k, D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
  }
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  %e: {
    Some{
      Bk.Term.Mat{k, D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{D.Mo.F(mo, _, d)}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Bk.Term,
    D.Mo.F(mo, Bk.Term.Mat{k, t3, t4}, d),
    Bk.Term.Mat{k, D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)},
    F.mat(mo, k, t3, t4, d)
  ): {
    Some{
      Bk.Term.Mat{k, D.Mo.F(mo, t3, Nat.add(d, 0n)), D.Mo.F(mo, t4, Nat.add(d, 0n))}
    }
      == Some{_}: Maybe<&2, Bk.Term>
  }
  %Equal.sym(
    Nat,
    Nat.add(d, 0n),
    d,
    N.add_zero(d)
  ): {
    Some{
      Bk.Term.Mat{k, D.Mo.F(mo, t3, _), D.Mo.F(mo, t4, _)}
    }
      == Some{Bk.Term.Mat{k, D.Mo.F(mo, t3, d), D.Mo.F(mo, t4, d)}}: Maybe<&2, Bk.Term>
  }
  {==}

# a label: its name, from field 2
def Tg.lab(
  nm: Maybe<&2, List<&2, Word(8n)>>,
  +mo: D.Mo,
  +d: Nat,
  -T0: Bk.Term,
  h: {T.tm.named(nm, k => Bk.Term.Lab{k}) == Some{T0}: Maybe<&2, Bk.Term>}
) -> {T.tm.named(nm, k => Bk.Term.Lab{k}) == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>}:
  match nm:
    case None{}:
      Tg.ns(T0, {None{} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>}, h)
    case Some{+k}:
      Tg.c0(mo, d, T0, Bk.Term.Lab{k}, F.lab(mo, k, d), Tg.some(Bk.Term.Lab{k}, T0, h))

# a λ-match of labels: its name, from field 2, and its parts in fields 3, 4
def Tg.mat(
  nm: Maybe<&2, List<&2, Word(8n)>>,
  +mo: D.Mo,
  +t3: Bk.Term,
  +t4: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  h: {T.tm.mat(nm, Some{t3}, Some{t4}) == Some{T0}: Maybe<&2, Bk.Term>}
) -> {
  T.tm.mat(
    nm,
    Some{D.Mo.F(mo, t3, Nat.add(d, 0n))},
    Some{D.Mo.F(mo, t4, Nat.add(d, 0n))}
  )
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  match nm:
    case None{}:
      Tg.ns(T0, {None{} == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>}, h)
    case Some{+k}:
      Tg.c14(mo, k, t3, t4, d, T0, Tg.some(Bk.Term.Mat{k, t3, t4}, T0, h))

# The claim
# ---------

# the copy of a frame's source cell, of the term T0, with each part k copied
# at the depth d + Tg.b(tg, k): the same tag and quantity, and the same name
# (field 2) for Lab and Mat, give Mo.F(T0, d)
def Tg.cg(
  +mo: D.Mo,
  tg: Nat,
  +q: Bk.Quan,
  +n: U32,
  +n2: U32,
  +x2: U32,
  +z2: U32,
  +ks: List<&2, List<&2, Word(8n)>>,
  +img: List<&2, Bk.Term>,
  +t2: Bk.Term,
  +t3: Bk.Term,
  +t4: Bk.Term,
  +d: Nat,
  -T0: Bk.Term,
  ho: {W.Tg.ok(tg) == True{}: Bool},
  hz: {
    Bool.or(Bool.and(Nat.is_ne(tg, 13n), Nat.is_ne(tg, 14n)), U32.is_eq(z2, x2)) == True{}: Bool
  },
  h: {
    T.tm.cell(
      tg,
      q,
      n,
      x2,
      ks,
      img,
      u => Some{t2},
      u => Some{t3},
      u => Some{t4}
    )
      == Some{T0}: Maybe<&2, Bk.Term>
  }
) -> {
  T.tm.cell(
    tg,
    q,
    n2,
    z2,
    ks,
    img,
    u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(tg, 2n)))},
    u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(tg, 3n)))},
    u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(tg, 4n)))}
  )
    == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
}:
  match tg:
    case 0n:
      K.Bo.tf(
        {
          T.tm.cell(
            0n,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(0n, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(0n, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(0n, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
        },
        ho
      )
    case 1n:
      K.Bo.tf(
        {
          T.tm.cell(
            1n,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(1n, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(1n, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(1n, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
        },
        ho
      )
    case 2n:
      Tg.c2(mo, t2, t3, d, T0, Tg.some(Bk.Term.Ann{t2, t3}, T0, h))
    case 3n:
      Tg.c3(mo, q, t2, t3, d, T0, Tg.some(Bk.Term.Let{q, t2, t3}, T0, h))
    case 4n:
      Tg.c4(mo, t2, d, T0, Tg.some(Bk.Term.Typ{t2}, T0, h))
    case 5n:
      Tg.c5(mo, t2, t3, d, T0, Tg.some(Bk.Term.Min{t2, t3}, T0, h))
    case 6n:
      Tg.c6(mo, q, t2, t3, d, T0, Tg.some(Bk.Term.All{q, t2, t3}, T0, h))
    case 7n:
      Tg.c7(mo, q, t2, d, T0, Tg.some(Bk.Term.Lam{q, t2}, T0, h))
    case 8n:
      Tg.c8(mo, q, t2, t3, d, T0, Tg.some(Bk.Term.App{q, t2, t3}, T0, h))
    case 9n:
      Tg.c9(mo, q, t2, t3, d, T0, Tg.some(Bk.Term.Sig{q, t2, t3}, T0, h))
    case 10n:
      Tg.c10(mo, q, t2, t3, d, T0, Tg.some(Bk.Term.Tup{q, t2, t3}, T0, h))
    case 11n:
      Tg.c11(mo, t2, d, T0, Tg.some(Bk.Term.Prj{t2}, T0, h))
    case 12n:
      K.Bo.tf(
        {
          T.tm.cell(
            12n,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(12n, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(12n, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(12n, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
        },
        ho
      )
    case 13n:
      %Equal.sym(
        U32,
        z2,
        x2,
        K.U.eq(z2, x2, hz)
      ): {
        T.tm.named(
          T.tm.name(ks, _),
          k => Bk.Term.Lab{k}
        )
          == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
      }
      Tg.lab(T.tm.name(ks, x2), mo, d, T0, h)
    case 14n:
      %Equal.sym(
        U32,
        z2,
        x2,
        K.U.eq(z2, x2, hz)
      ): {
        T.tm.mat(
          T.tm.name(ks, _),
          Some{D.Mo.F(mo, t3, Nat.add(d, 0n))},
          Some{D.Mo.F(mo, t4, Nat.add(d, 0n))}
        )
          == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
      }
      Tg.mat(T.tm.name(ks, x2), mo, t3, t4, d, T0, h)
    case 15n:
      Tg.c0(mo, d, T0, Bk.Term.Efq{}, F.efq(mo, d), Tg.some(Bk.Term.Efq{}, T0, h))
    case 16n:
      Tg.c16(mo, t2, t3, t4, d, T0, Tg.some(Bk.Term.Eql{t2, t3, t4}, T0, h))
    case 17n:
      Tg.c0(mo, d, T0, Bk.Term.Rfl{}, F.rfl(mo, d), Tg.some(Bk.Term.Rfl{}, T0, h))
    case 18n:
      Tg.c18(mo, t2, t3, t4, d, T0, Tg.some(Bk.Term.Rwt{t2, t3, t4}, T0, h))
    case 19n+r:
      K.Bo.tf(
        {
          T.tm.cell(
            19n+r,
            q,
            n2,
            z2,
            ks,
            img,
            u => Some{D.Mo.F(mo, t2, Nat.add(d, W.Tg.b(19n+r, 2n)))},
            u => Some{D.Mo.F(mo, t3, Nat.add(d, W.Tg.b(19n+r, 3n)))},
            u => Some{D.Mo.F(mo, t4, Nat.add(d, W.Tg.b(19n+r, 4n)))}
          )
            == Some{D.Mo.F(mo, T0, d)}: Maybe<&2, Bk.Term>
        },
        ho
      )
