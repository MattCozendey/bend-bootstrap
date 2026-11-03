# compiler: the simulation of Cir's statements
# ============================================
#
# SPost(o, fu, X, K, ls, ...) says what the code X, run from the state that
# holds st (simulation_relation.bend), does when Cir.exec, with the fuel fu,
# gives o, on an engine whose answers to the grows are gs:
#
#   next{st2}  it reaches the code K, with the labels ls again, an empty
#              stack and a state that holds st2, whose answers are gs2;
#   halt{s}    it ends run with the results [s], with a memory from which
#              the host reads what Cir.ended says (HaltOK);
#   out_of_memory  it ends run with [1];
#   trap       nothing;
#   not_done   it goes on for fu steps: each unit of fuel that a loop takes
#              is paid by a round of at least 4 steps.
#
# GPost covers the engine's refusals: either SPost, with the answers that
# remain after k grows, or run ends with [1] after an answer that refuses a
# grow (OOM). With no answers (gs = []) no grow is refused, so SPost holds.
# post.wrap.to and post.pre.to prefix and suffix steps to an SPost; gpost.wrap,
# gpost.pre and gpost.then do it for a GPost (gpost.then composes
# Cir.exec.then). sim.stmt, at the end, is the simulation of statements, by
# induction on the fuel and on the statement.

import Base
import ../../Shared/shared.bend as Sd
import ../../Wasm/impl.bend as Wa
import ./impl.bend as Cr
import ../need_big.bend as N
import ./instrs_round_trip.bend as I
import ./halt.bend as PH
import ./module_round_trip.bend as M
import ./module_valid.bend as V
import ./simulation_steps.bend as S
import ./simulation_memory_bytes.bend as Y
import ./simulation_numbers.bend as Z
import ./simulation_relation.bend as Q
import ./simulation_expr.bend as E
import ./simulation_write_frame.bend as F
import ./simulation_alloc_emit.bend as A

# Kit
# ---

def EXB(-B: Wa.Wasm.Bytes -> Data) -> Data:
  Sigma<&2, &2, Wa.Wasm.Bytes, x => B(x)>

def EXM(-B: Wa.Wasm.Memory -> Data) -> Data:
  Sigma<&2, &2, Wa.Wasm.Memory, x => B(x)>

# the label of run's block: after it, run gives its status
def RL() -> Wa.Wasm.Label:
  Wa.Wasm.Label{0n, None{}, [Wa.Wasm.Instr.local_get{2}], 0n}

# a configuration of run at a statement: an empty stack, the status 2
def Cf(+X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32,
  +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes) -> Wa.Wasm.Step:
  Q.Cfg(X, ls, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})

# Posts
# -----

# the outcome that the host reads at the end of run, for the status s0: what
# Cir.ended says, of the output ou of on bytes at 20 × nx in pg pages
def HaltOK(+s0: U32, +nx: U32, +pg: U32, +on: U32, +ou: List<&2, Word(8n)>, +mem: Wa.Wasm.Memory) -> Data:
  {Wa.Wasm.run.status(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), mem) ==
    Cr.Cir.ended.halt(U32.is_eq(s0, 0), U32.is_eq(s0, 1), U32.is_eq(s0, 2), Wa.Wasm.fits(pg, Cr.Cir.at(nx), on), ou) : Wa.Wasm.Outcome}

def SPost.next(st2: Cr.Cir.State, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat) -> Data:
  match st2:
    case Cr.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
      S.EX(N2 => Q.EXU(t2 => Q.EXU(nd2 => Q.EXU(ad2 => EXB(m2 =>
        S.P2({PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
          Cf(K, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs2, m2) : Wa.Wasm.Step},
          Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2)))))))

def SPost.halt(+s0: U32, st2: Cr.Cir.State, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes) -> Data:
  match st2:
    case Cr.Cir.State{_, _, +nx2, _, _, +pg2, _, _, +ou2, +on2}:
      S.EX(N2 => EXM(mm => S.P2({PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
        Wa.Wasm.Step.done{[s0], mm} : Wa.Wasm.Step}, HaltOK(s0, nx2, pg2, on2, ou2, mm))))

# SPost.to also records the answers gs2 left at a next state
def SPost.to(o: Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat) -> Data:
  match o:
    case Cr.Cir.Out.next{st2}:
      SPost.next(st2, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G)
    case Cr.Cir.Out.halt{+s0, st2}:
      SPost.halt(s0, st2, X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
    case Cr.Cir.Out.out_of_memory{}:
      S.EX(N2 => EXM(mm => {PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
        Wa.Wasm.Step.done{[1], mm} : Wa.Wasm.Step}))
    case Cr.Cir.Out.trap{}:
      Unit
    case Cr.Cir.Out.not_done{}:
      S.is.next(PH.H.steps(fu, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)))

# what the code X does in the labels ls, from a state that holds st, when
# Cir.exec gives o; a next state is at the code K in the labels ls1
def SPost(o: Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat) -> Data:
  SPost.to(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs, m, P, G)

# an engine refusal ends run with 1; k is the answer that refused it
def OOM(+X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes) -> Data:
  S.EX(N2 => EXM(mm => S.EX(k => S.P2({List.get(&2, Bool, gs, k) == Some{False{}} : Maybe<&2, Bool>},
    {PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) == Wa.Wasm.Step.done{[1], mm} : Wa.Wasm.Step}))))

# either the exact simulation, with the answers left at a next state, or an
# out of memory caused by an engine refusal
def GPost(o: Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat) -> Data:
  S.OR(S.EX(k => SPost.to(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, S.Drop(k, gs), m, P, G)),
    OOM(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m))

# Composing posts
# ---------------

# prefix and suffix steps to an SPost
def post.wrap.to(o: Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +gs1: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes, +P: Nat, +G: Nat,
  +Xi: List<&2, Wa.Wasm.Instr>, +lsi: List<&2, Wa.Wasm.Label>, +Ki: List<&2, Wa.Wasm.Instr>, +lsi1: List<&2, Wa.Wasm.Label>,
  +ti: U32, +ndi: U32, +adi: U32, +rgi: List<&2, U32>, +nxi: U32, +oni: U32, +pgi: U32, +lmi: U32, +mi: Wa.Wasm.Bytes, +N0: Nat,
  +e0: {PH.H.steps(N0, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) == Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, mi) : Wa.Wasm.Step},
  +fui: Nat, hf: N.Le(fu, Nat.add(N0, fui)),
  +N1: Nat, suf: @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @rg2: List<&2, U32> -> @nx2: U32 -> @on2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @m2: Wa.Wasm.Bytes -> {PH.H.steps(N1, Cf(Ki, lsi1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs2, m2)) ==
      Cf(K, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs2, m2) : Wa.Wasm.Step},
  p: SPost.to(o, fui, Xi, lsi, Ki, lsi1, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, gs2, mi, P, G)) -> SPost.to(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G):
  match o:
    case Cr.Cir.Out.next{st2}:
      match st2:
        case Cr.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
          (+N2, p1) = p
          (+t2, p2) = p1
          (+nd2, p3) = p2
          (+ad2, p4) = p3
          (+m2, p5) = p4
          (eq, hI) = p5
          +C0 = Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
          +C1 = Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, mi)
          +C2 = Cf(Ki, lsi1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs2, m2)
          +C3 = Cf(K, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs2, m2)
          (Nat.add(N0, Nat.add(N2, N1)), (t2, (nd2, (ad2, (m2, (S.steps.then(N0, Nat.add(N2, N1), C0, C1, C3, e0,
            S.steps.then(N2, N1, C1, C2, C3, eq, suf(t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2))), hI))))))
    case Cr.Cir.Out.halt{+s0, st2}:
      match st2:
        case Cr.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
          (+N2, p1) = p
          (+mm, p2) = p1
          (eq, ok) = p2
          (Nat.add(N0, N2), (mm, (S.steps.then(N0, N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, mi), Wa.Wasm.Step.done{[s0], mm}, e0, eq), ok)))
    case Cr.Cir.Out.out_of_memory{}:
      (+N2, p1) = p
      (+mm, eq) = p1
      (Nat.add(N0, N2), (mm, S.steps.then(N0, N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, mi), Wa.Wasm.Step.done{[1], mm}, e0, eq)))
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      S.next.wrap(fu, fui, N0, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, mi), hf, e0, p)

# prefix steps to an SPost
def post.pre.to(o: Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +gs1: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes, +P: Nat, +G: Nat, +Xi: List<&2, Wa.Wasm.Instr>, +lsi: List<&2, Wa.Wasm.Label>,
  +ti: U32, +ndi: U32, +adi: U32, +rgi: List<&2, U32>, +nxi: U32, +oni: U32, +pgi: U32, +lmi: U32, +mi: Wa.Wasm.Bytes, +N0: Nat,
  +e0: {PH.H.steps(N0, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) == Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, mi) : Wa.Wasm.Step},
  p: SPost.to(o, fu, Xi, lsi, K, ls1, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs1, gs2, mi, P, G)) -> SPost.to(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G):
  post.wrap.to(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs1, gs2, m, P, G, Xi, lsi, K, ls1, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi, N0, e0, fu, N.le_add_l(N0, fu), 0n,
    t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => m2 => {==}, p)

# prefix and suffix steps of a generalized post
def gpost.wrap(o: Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, +P: Nat, +G: Nat,
  +Xi: List<&2, Wa.Wasm.Instr>, +lsi: List<&2, Wa.Wasm.Label>, +Ki: List<&2, Wa.Wasm.Instr>, +lsi1: List<&2, Wa.Wasm.Label>,
  +ti: U32, +ndi: U32, +adi: U32, +rgi: List<&2, U32>, +nxi: U32, +oni: U32, +pgi: U32, +lmi: U32, +mi: Wa.Wasm.Bytes, +N0: Nat,
  +e0: {PH.H.steps(N0, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) == Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs, mi) : Wa.Wasm.Step},
  +fui: Nat, hf: N.Le(fu, Nat.add(N0, fui)),
  +N1: Nat, suf: @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @rg2: List<&2, U32> -> @nx2: U32 -> @on2: U32 -> @pg2: U32 -> @lm2: U32 -> @gs2: List<&2, Bool> ->
    @m2: Wa.Wasm.Bytes -> {PH.H.steps(N1, Cf(Ki, lsi1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs2, m2)) ==
      Cf(K, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs2, m2) : Wa.Wasm.Step},
  p: GPost(o, fui, Xi, lsi, Ki, lsi1, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs, mi, P, G)) -> GPost(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match p:
    case Inl{q}:
      (+k, r) = q
      Inl{(k, post.wrap.to(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs, S.Drop(k, gs), m, P, G,
        Xi, lsi, Ki, lsi1, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi, N0, e0, fui, hf, N1,
        t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => m2 => suf(t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, S.Drop(k, gs), m2), r))}
    case Inr{q}:
      (+N2, q1) = q
      (+mm, q2) = q1
      (+k, q3) = q2
      (hg, eq) = q3
      Inr{(Nat.add(N0, N2), (mm, (k, (hg, S.steps.then(N0, N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m),
        Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs, mi), Wa.Wasm.Step.done{[1], mm}, e0, eq)))))}

# prefix steps of a generalized post
def gpost.pre(o: Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, +P: Nat, +G: Nat, +Xi: List<&2, Wa.Wasm.Instr>, +lsi: List<&2, Wa.Wasm.Label>,
  +ti: U32, +ndi: U32, +adi: U32, +rgi: List<&2, U32>, +nxi: U32, +oni: U32, +pgi: U32, +lmi: U32, +mi: Wa.Wasm.Bytes, +N0: Nat,
  +e0: {PH.H.steps(N0, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) == Cf(Xi, lsi, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs, mi) : Wa.Wasm.Step},
  +fui: Nat, hf: N.Le(fu, Nat.add(N0, fui)),
  p: GPost(o, fui, Xi, lsi, K, ls1, a, n, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, gs, mi, P, G)) -> GPost(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  gpost.wrap(o, fu, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G, Xi, lsi, K, ls1, ti, ndi, adi, rgi, nxi, oni, pgi, lmi, mi, N0, e0, fui, hf, 0n,
    t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => gs2 => m2 => {==}, p)

# the continuation of an exact next state, with its remaining answers
def gpost.then.next(more: Cr.Cir.State -> Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>,
  +K1: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls2: List<&2, Wa.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, +P: Nat, +G: Nat,
  +rg2: List<&2, U32>, +cl2: Cr.Cir.Cells, +nx2: U32, +fi2: U32, +im2: U32, +pg2: U32, +lm2: U32, +inp2: List<&2, Word(8n)>, +ou2: List<&2, Word(8n)>, +on2: U32,
  +t2: U32, +nd2: U32, +ad2: U32, +m2: Wa.Wasm.Bytes, +k1: Nat, +N2: Nat,
  +eq: {PH.H.steps(N2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) == Cf(K1, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, S.Drop(k1, gs), m2) : Wa.Wasm.Step},
  rnext: GPost(more(Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), fu, K1, ls1, K, ls2, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, S.Drop(k1, gs), m2, P, G)) ->
  GPost(more(Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), fu, X, ls, K, ls2, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match rnext:
    case Inl{q2}:
      (+k2, r2) = q2
      Inl{(Nat.add(k1, k2), (%Equal.sym(List<&2, Bool>, S.Drop(Nat.add(k1, k2), gs), S.Drop(k2, S.Drop(k1, gs)), S.drop.add(k1, gs, k2)) :
        SPost.to(more(Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), fu, X, ls, K, ls2, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, _, m, P, G);
        post.pre.to(more(Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), fu, X, ls, K, ls2, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, S.Drop(k1, gs), S.Drop(k2, S.Drop(k1, gs)), m, P, G, K1, ls1,
          t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, m2, N2, eq, r2)))}
    case Inr{q2}:
      (+N3, q3) = q2
      (+mm, q4) = q3
      (+k2, q5) = q4
      (hg, eq2) = q5
      Inr{(Nat.add(N2, N3), (mm, (Nat.add(k1, k2), (Equal.trans(Maybe<&2, Bool>, List.get(&2, Bool, gs, Nat.add(k1, k2)),
        List.get(&2, Bool, S.Drop(k1, gs), k2), Some{False{}}, S.get.add(k1, gs, k2), hg),
        S.steps.then(N2, N3, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m),
          Cf(K1, ls1, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, S.Drop(k1, gs), m2), Wa.Wasm.Step.done{[1], mm}, eq, eq2)))))}

# Cir.exec.then for generalized posts, passing on the answers that remain
def gpost.then(o1: Cr.Cir.Out, more: Cr.Cir.State -> Cr.Cir.Out, +fu: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>,
  +K1: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls2: List<&2, Wa.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, +P: Nat, +G: Nat,
  p: GPost(o1, fu, X, ls, K1, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G),
  kont: @rg2: List<&2, U32> -> @cl2: Cr.Cir.Cells -> @nx2: U32 -> @fi2: U32 -> @im2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @inp2: List<&2, Word(8n)> -> @ou2: List<&2, Word(8n)> -> @on2: U32 -> @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @m2: Wa.Wasm.Bytes -> @gs1: List<&2, Bool> ->
    Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2) ->
    GPost(more(Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), fu, K1, ls1, K, ls2, a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs1, m2, P, G)) ->
  GPost(Cr.Cir.exec.then(o1, more), fu, X, ls, K, ls2, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match o1:
    case Cr.Cir.Out.next{st2}:
      match st2:
        case Cr.Cir.State{+rg2, +cl2, +nx2, +fi2, +im2, +pg2, +lm2, +inp2, +ou2, +on2}:
          match p:
            case Inl{q}:
              (+k1, r) = q
              (+N2, p1) = r
              (+t2, p2) = p1
              (+nd2, p3) = p2
              (+ad2, p4) = p3
              (+m2, p5) = p4
              (+eq, +hI) = p5
              gpost.then.next(more, fu, X, ls, K1, ls1, K, ls2, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G,
                rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, t2, nd2, ad2, m2, k1, N2, eq,
                kont(rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, t2, nd2, ad2, m2, S.Drop(k1, gs), hI))
            case Inr{q}:
              Inr{q}
    case Cr.Cir.Out.halt{+s0, st2}:
      p
    case Cr.Cir.Out.out_of_memory{}:
      p
    case Cr.Cir.Out.trap{}:
      p
    case Cr.Cir.Out.not_done{}:
      p

# The depth of the labels of a statement's code: the branches out of run
# from it are at most d + dep(s) levels inside run's block
def dep(s: Cr.Cir.Stmt) -> Nat:
  match s:
    case Cr.Cir.Stmt.nop{}:
      0n
    case Cr.Cir.Stmt.set{_, _}:
      0n
    case Cr.Cir.Stmt.store{_, _, _}:
      0n
    case Cr.Cir.Stmt.alloc{_}:
      4n
    case Cr.Cir.Stmt.emit{_}:
      4n
    case Cr.Cir.Stmt.seq{a, b}:
      Nat.add(dep(a), dep(b))
    case Cr.Cir.Stmt.if{_, t, e}:
      2n+Nat.add(dep(t), dep(e))
    case Cr.Cir.Stmt.while{_, body}:
      2n+dep(body)
    case Cr.Cir.Stmt.halt{_}:
      2n

# The statements that touch the memory
# ------------------------------------
#
# Each lemma is the simulation of one statement, from a state that holds st.

# store{k, c, v}, when c gives the cell i and v the value x: the cell is one
# that the machine may use (b)
def store.if(+fu: Nat, b: Bool, +k: Nat, +c: Cr.Cir.Expr, +v: Cr.Cir.Expr, +i: U32, +x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lm: U32, +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)),
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hk: {Nat.is_le(k, 4n) == True{} : Bool},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, +okv: {V.ok.expr(v, R) == True{} : Bool},
  +evc: {Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{i} : Maybe<&2, U32>},
  +evv: {Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{x} : Maybe<&2, U32>},
  +eb: {Cr.Cir.is_cell(i, im, fi, nx) == b : Bool}) ->
  SPost(Cr.Cir.exec.store.if(b, k, i, x, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.store{k, c, v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +o = U32.shln(U32.from_nat(k), 2n)
      +St = Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)
      +Ks = {Con{Wa.Wasm.Instr.store{o}, K} : List<&2, Wa.Wasm.Instr>}
      +Kv = Cr.Cir.code.expr(v, Ks)
      +Ka = Cr.Cir.code.at(Kv)
      +tc = E.tmpE(c, t, St)
      +tv = E.tmpE(v, i, St)
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +L3 = Q.Loc(a, n, 2, nx, on, tv, nd, ad, rg)
      +C0 = Cf(Cr.Cir.code.expr(c, Ka), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C1 = Q.Cfg(Ka, ls, [i], Q.Loc(a, n, 2, nx, on, tc, nd, ad, rg), M0)
      +C2 = Q.Cfg(Kv, ls, [Cr.Cir.at(i)], Q.Loc(a, n, 2, nx, on, i, nd, ad, rg), M0)
      +C3 = Q.Cfg(Ks, ls, [x, Cr.Cir.at(i)], L3, M0)
      +m2 = Wa.Wasm.write32(m, Q.at.f(i, k), x)
      +C4 = Cf(K, ls, a, n, tv, nd, ad, rg, nx, on, pg, lm, gs, m2)
      +e1 = E.sim.expr(c, rg, cl, nx, fi, im, pg, lm, inp, ou, on, i, evc, R, MX, okc, hR, Ka, ls, [], P, G, a, n, 2, t, nd, ad, gs, m, hI, W, hW, hP, hG)
      +e2 = E.at.steps(i, Kv, ls, [], a, n, 2, nx, on, tc, nd, ad, rg, M0)
      +e3 = E.sim.expr(v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, x, evv, R, MX, okv, hR, Ks, ls, [Cr.Cir.at(i)], P, G, a, n, 2, i, nd, ad, gs, m, hI, W, hW, hP, hG)
      +hin = Q.q.field.in(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, W, hW, hP, hG, i, k, eb, hk)
      +e4 = F.store.step(o, Cr.Cir.at(i), x, K, ls, [], L3, pg, lm, gs, m, hin)
      +e34 = S.steps.then(E.cost(v), 1n, C2, C3, C4, e3, e4)
      +e24 = S.steps.then(7n, Nat.add(E.cost(v), 1n), C1, C2, C4, e2, e34)
      +e14 = S.steps.then(E.cost(c), Nat.add(7n, Nat.add(E.cost(v), 1n)), C0, C1, C4, e1, e24)
      (Nat.add(E.cost(c), Nat.add(7n, Nat.add(E.cost(v), 1n))), (tv, (nd, (ad, (m2, (e14,
        F.inv.store(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI, W, hW, hP, hG, i, k, x, hk, eb)))))))

# store{k, c, v}, by the values of c and v
def store.of(+fu: Nat, mc: Maybe<&2, U32>, mv: Maybe<&2, U32>, +k: Nat, +c: Cr.Cir.Expr, +v: Cr.Cir.Expr, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32,
  +pg: U32, +lm: U32, +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)),
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hk: {Nat.is_le(k, 4n) == True{} : Bool},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, +okv: {V.ok.expr(v, R) == True{} : Bool},
  +evc: {Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mc : Maybe<&2, U32>},
  +evv: {Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>}) ->
  SPost(Cr.Cir.exec.store(k, mc, mv, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.store{k, c, v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match mc mv:
    case Some{+i} Some{+x}:
      store.if(fu, Cr.Cir.is_cell(i, im, fi, nx), k, c, v, i, x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, R, MX, hR, P, G, a, n, t, nd, ad, gs, m, hI,
        W, hW, hP, hG, hk, okc, okv, evc, evv, {==})
    case Some{i} None{}:
      Unit{}
    case None{} _:
      Unit{}

# store{k, c, v}
def sim.store(+fu: Nat, +k: Nat, +c: Cr.Cir.Expr, +v: Cr.Cir.Expr, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(Cr.Cir.Stmt.store{k, c, v}, R) == True{} : Bool}) ->
  GPost(Cr.Cir.exec.store(k, Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.store{k, c, v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  +ok01 = I.and.l(Bool.and(Nat.is_le(k, 4n), V.ok.expr(c, R)), V.ok.expr(v, R), ok)
  Inl{(0n, store.of(fu, Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)),
    k, c, v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, R, MX, hR, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG,
    I.and.l(Nat.is_le(k, 4n), V.ok.expr(c, R), ok01), I.and.r(Nat.is_le(k, 4n), V.ok.expr(c, R), ok01),
    I.and.r(Bool.and(Nat.is_le(k, 4n), V.ok.expr(c, R)), V.ok.expr(v, R), ok), {==}, {==}))}

# alloc{r}, once the memory holds the cell next in p2 pages: register r gets
# it, when there is a register r (b4)
def alloc.reg(+fu: Nat, b4: Bool, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +p2: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)),
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +ok: {V.ok.stmt(Cr.Cir.Stmt.alloc{r}, R) == True{} : Bool},
  +e4: {Nat.is_lt(r, List.length(&2, U32, rg)) == b4 : Bool}, +N0: Nat,
  +pre: {PH.H.steps(N0, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
    Q.Cfg(A.ax2(Cr.Cir.l.reg(r), K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), Wa.Wasm.Memory{p2, lm, gs2, m}) : Wa.Wasm.Step},
  +hon: {U32.to_nat(on) == 0n : Nat}, +hnx: N.Le(1n+U32.to_nat(nx), P), +hpp: N.Le(U32.to_nat(A.nc(nx)), U32.to_nat(p2)),
  +hp: N.Le(U32.to_nat(pg), U32.to_nat(p2)), +hpl: N.Le(U32.to_nat(p2), U32.to_nat(lm))) ->
  SPost.to(Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(b4, rg, r, nx), Cr.Cir.State{rg, Cr.Cir.Cells.set(cl, nx, Cr.Cir.Cell.zero()), U32.inc(nx), fi, im, p2, lm, inp, ou, on}), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G):
  match b4:
    case False{}:
      Unit{}
    case True{}:
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +X = PH.H.t20(U32.to_nat(nx))
      +rg2 = List.set(&2, U32, rg, r, nx)
      +eT = F.at.nat(nx, P, hP, N.weaken(U32.to_nat(nx), P, hnx))
      +hroom = A.room.pb(nx, p2, P, hP, W, hW, hnx, hpp)
      +hb = A.pb2.le(p2, lm, G, W, hG, hpl, Q.b.lm(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
      +C0 = Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +CD = Q.Cfg(A.ax2(Cr.Cir.l.reg(r), K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), Wa.Wasm.Memory{p2, lm, gs2, m})
      +CE = Q.Cfg(K, ls, [], Q.Loc(a, n, 2, U32.add(nx, 1), on, nx, A.nc(nx), Cr.Cir.at(nx), rg2), Wa.Wasm.Memory{p2, lm, gs2, A.z5(m, nx)})
      +eD = A.alloc.D(r, K, ls, a, n, 2, nx, on, nx, A.nc(nx), ad, rg, p2, lm, gs2, m, A.reg.nat(r, R, MX, ok, hR), e4, X, eT, W, hW, hroom, hb)
      +eq0 = S.steps.then(N0, 30n, C0, CD, CE, pre, eD)
      +eq = {(%F.inc.add1(nx) : {PH.H.steps(Nat.add(N0, 30n), C0) == Cf(K, ls, a, n, nx, A.nc(nx), Cr.Cir.at(nx), rg2, _, on, p2, lm, gs2, A.z5(m, nx)) : Wa.Wasm.Step};
          eq0) : {PH.H.steps(Nat.add(N0, 30n), C0) == Cf(K, ls, a, n, nx, A.nc(nx), Cr.Cir.at(nx), rg2, U32.inc(nx), on, p2, lm, gs2, A.z5(m, nx)) : Wa.Wasm.Step}}
      (Nat.add(N0, 30n), (nx, (A.nc(nx), (Cr.Cir.at(nx), (A.z5(m, nx), (eq,
        A.inv.alloc(P, G, a, n, cl, nx, fi, im, pg, p2, lm, inp, ou, on, m, hI, W, hW, hP, hG, hon, hnx, hroom, hp, hpl)))))))

# the steps of alloc's code to the growth, with the pages as Cir has them
def alloc.AB(+r: Nat, +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32,
  +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, e1: {U32.is_lt(nx, 214748364) == True{} : Bool}) ->
  {PH.H.steps(20n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
    Q.Cfg(Cr.Cir.code.grow(d, A.ax2(Cr.Cir.l.reg(r), K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}) : Wa.Wasm.Step}:
  +rr = Cr.Cir.l.reg(r)
  +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
  +L0 = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
  +eB = A.alloc.B(rr, d, K, ls, a, n, 2, nx, on, t, nd, ad, rg, M0)
  +eB2 = {(%A.andw.nc(nx) : {PH.H.steps(15n, Q.Cfg(A.ax1(rr, d, K), ls, [], L0, M0)) ==
      Q.Cfg(Cr.Cir.code.grow(d, A.ax2(rr, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, _, ad, rg), M0) : Wa.Wasm.Step}; eB) :
    {PH.H.steps(15n, Q.Cfg(A.ax1(rr, d, K), ls, [], L0, M0)) ==
      Q.Cfg(Cr.Cir.code.grow(d, A.ax2(rr, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), M0) : Wa.Wasm.Step}}
  S.steps.then(5n, 15n, Q.Cfg(Cr.Cir.code.alloc(rr, d, K), ls, [], L0, M0), Q.Cfg(A.ax1(rr, d, K), ls, [], L0, M0),
    Q.Cfg(Cr.Cir.code.grow(d, A.ax2(rr, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), M0),
    A.alloc.A(rr, d, K, ls, a, n, 2, nx, on, t, nd, ad, rg, M0, e1), eB2)

# alloc{r} whose memory must grow: within the limit (b3), or out of memory
def alloc.grow(+fu: Nat, b3: Bool, gr: Bool, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +ok: {V.ok.stmt(Cr.Cir.Stmt.alloc{r}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +hon: {U32.to_nat(on) == 0n : Nat}, +e1: {U32.is_lt(nx, 214748364) == True{} : Bool}, +hnx: N.Le(1n+U32.to_nat(nx), P),
  +e2: {U32.is_le(A.nc(nx), pg) == False{} : Bool}, +e3: {U32.is_le(A.nc(nx), lm) == b3 : Bool}, +egr: {Wa.Wasm.grants(gs) == gr : Bool}) ->
  GPost(Cr.Cir.exec.bump.of(r, nx, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on), Cr.Cir.room.if(False{}, b3, pg, A.nc(nx))), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b3 gr:
    case False{} _:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +CC = Q.Cfg(Cr.Cir.code.grow(d, A.ax2(Cr.Cir.l.reg(r), K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), M0)
      +hge = A.ge.of(A.nc(nx), pg, N.weaken(U32.to_nat(pg), U32.to_nat(A.nc(nx)), A.nle.u32(A.nc(nx), pg, e2)))
      +eC = A.grow.fail(A.nc(nx), d, A.ax2(Cr.Cir.l.reg(r), K), ls, hL, A.dep.n(d, 3n, MD, Unit{}, hd), a, n, 2, nx, on, nx, ad, rg, pg, lm, gs, m, e2, e3, hge)
      Inl{(0n, (Nat.add(20n, 19n), (M0, S.steps.then(20n, 19n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), CC,
        Wa.Wasm.Step.done{[1], M0}, alloc.AB(r, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, e1), eC))))}
    case True{} False{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +hb = Q.pb.le(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG)
      +CC = Q.Cfg(Cr.Cir.code.grow(d, A.ax2(Cr.Cir.l.reg(r), K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), M0)
      +hlt = A.nle.u32(A.nc(nx), pg, e2)
      +hge = A.ge.of(A.nc(nx), pg, N.weaken(U32.to_nat(pg), U32.to_nat(A.nc(nx)), hlt))
      +M1 = {Wa.Wasm.Memory{pg, lm, List.drop(&2, Bool, gs, 1n), m} : Wa.Wasm.Memory}
      +eC = A.grow.refused(A.nc(nx), d, A.ax2(Cr.Cir.l.reg(r), K), ls, hL, A.dep.n(d, 3n, MD, Unit{}, hd), a, n, 2, nx, on, nx, ad, rg, pg, lm, gs, m, e2, e3, hge, egr)
      Inr{(Nat.add(20n, 19n), (M1, (0n, (S.grants.false(gs, egr), S.steps.then(20n, 19n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), CC,
        Wa.Wasm.Step.done{[1], M1}, alloc.AB(r, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, e1), eC)))))}
    case True{} True{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +hb = Q.pb.le(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG)
      +CC = Q.Cfg(Cr.Cir.code.grow(d, A.ax2(Cr.Cir.l.reg(r), K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), M0)
      +hlt = A.nle.u32(A.nc(nx), pg, e2)
      +hge = A.ge.of(A.nc(nx), pg, N.weaken(U32.to_nat(pg), U32.to_nat(A.nc(nx)), hlt))
      +hpg = A.pg.ne(pg, W, hW, hb, A.pos.of.D(U32.to_nat(pg), F.b.pb20(P, G, a, nx, fi, im, pg, lm, inp, on, hB)))
      +gs1 = List.drop(&2, Bool, gs, 1n)
      +CD = Q.Cfg(A.ax2(Cr.Cir.l.reg(r), K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), Wa.Wasm.Memory{A.nc(nx), lm, gs1, m})
      +eC = A.grow.ok(A.nc(nx), d, A.ax2(Cr.Cir.l.reg(r), K), ls, a, n, 2, nx, on, nx, ad, rg, pg, lm, gs, m, e2, e3, hge, hpg, egr)
      Inl{(1n, alloc.reg(fu, Nat.is_lt(r, List.length(&2, U32, rg)), r, rg, cl, nx, fi, im, pg, A.nc(nx), lm, inp, ou, on, d, K, ls, R, MX, hR,
        P, G, a, n, t, nd, ad, gs, gs1, m, hI, W, hW, hP, hG, ok, {==}, Nat.add(20n, 14n),
        S.steps.then(20n, 14n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), CC, CD,
          alloc.AB(r, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, e1), eC),
        hon, hnx, N.le_refl(U32.to_nat(A.nc(nx))), N.weaken(U32.to_nat(pg), U32.to_nat(A.nc(nx)), hlt), Z.le.of(A.nc(nx), lm, e3)))}

# alloc{r}: the memory holds the cell next already (b2), or must grow
def alloc.room(+fu: Nat, b2: Bool, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +ok: {V.ok.stmt(Cr.Cir.Stmt.alloc{r}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +hon: {U32.to_nat(on) == 0n : Nat}, +e1: {U32.is_lt(nx, 214748364) == True{} : Bool}, +hnx: N.Le(1n+U32.to_nat(nx), P),
  +e2: {U32.is_le(A.nc(nx), pg) == b2 : Bool}) ->
  GPost(Cr.Cir.exec.bump.of(r, nx, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on), Cr.Cir.room.if(b2, U32.is_le(A.nc(nx), lm), pg, A.nc(nx))), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b2:
    case True{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +CC = Q.Cfg(Cr.Cir.code.grow(d, A.ax2(Cr.Cir.l.reg(r), K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), M0)
      +CD = Q.Cfg(A.ax2(Cr.Cir.l.reg(r), K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nc(nx), ad, rg), M0)
      +eC = A.grow.skip(A.nc(nx), d, A.ax2(Cr.Cir.l.reg(r), K), ls, a, n, 2, nx, on, nx, ad, rg, pg, lm, gs, m, e2)
      Inl{(0n, alloc.reg(fu, Nat.is_lt(r, List.length(&2, U32, rg)), r, rg, cl, nx, fi, im, pg, pg, lm, inp, ou, on, d, K, ls, R, MX, hR,
        P, G, a, n, t, nd, ad, gs, gs, m, hI, W, hW, hP, hG, ok, {==}, Nat.add(20n, 5n),
        S.steps.then(20n, 5n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), CC, CD,
          alloc.AB(r, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, e1), eC),
        hon, hnx, Z.le.of(A.nc(nx), pg, e2), N.le_refl(U32.to_nat(pg)), Q.b.pg(P, G, a, nx, fi, im, pg, lm, inp, on, hB)))}
    case False{}:
      alloc.grow(fu, U32.is_le(A.nc(nx), lm), Wa.Wasm.grants(gs), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI,
        W, hW, hP, hG, ok, hd, hon, e1, hnx, e2, {==}, {==})

# alloc{r}: next below 214748364 (b1), or out of memory
def alloc.lt(+fu: Nat, b1: Bool, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +ok: {V.ok.stmt(Cr.Cir.Stmt.alloc{r}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +hon: {U32.to_nat(on) == 0n : Nat}, +e1: {U32.is_lt(nx, 214748364) == b1 : Bool}) ->
  GPost(Cr.Cir.exec.bump.if(b1, r, nx, pg, lm, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b1:
    case False{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      Inl{(0n, (11n, (M0, A.alloc.Af(Cr.Cir.l.reg(r), d, K, ls, hL, A.dep.n(d, 2n, MD, Unit{}, hd), a, n, 2, nx, on, t, nd, ad, rg, M0, e1))))}
    case True{}:
      +hnx = N.le_rw_r(1n+U32.to_nat(nx), U32.to_nat(214748364), P, A.lit.P(P, hP), Z.lt.of(nx, 214748364, e1))
      alloc.room(fu, U32.is_le(A.nc(nx), pg), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI,
        W, hW, hP, hG, ok, hd, hon, e1, hnx, {==})

# alloc{r}: no output yet (b0), or a trap
def alloc.on(+fu: Nat, b0: Bool, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +ok: {V.ok.stmt(Cr.Cir.Stmt.alloc{r}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +e0: {U32.is_zero(on) == b0 : Bool}) ->
  GPost(Cr.Cir.exec.alloc.if(b0, r, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b0:
    case False{}:
      Inl{(0n, Unit{})}
    case True{}:
      +hon = Equal.cong(U32, Nat, z => U32.to_nat(z), on, 0, Y.U32.eq(on, 0, e0))
      alloc.lt(fu, U32.is_lt(nx, 214748364), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI,
        W, hW, hP, hG, ok, hd, hon, {==})

# alloc{r}
def sim.alloc(+fu: Nat, +r: Nat, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(Cr.Cir.Stmt.alloc{r}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD))) ->
  GPost(Cr.Cir.exec.alloc(r, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.alloc{r}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  alloc.on(fu, U32.is_zero(on), r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI,
    W, hW, hP, hG, ok, hd, {==})

# emit{v}, once the memory holds the byte in p2 pages: the byte goes out
def emit.fin(+fu: Nat, +v: Cr.Cir.Expr, +x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +p2: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)),
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +okv: {V.ok.expr(v, R) == True{} : Bool},
  +ev: {Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{x} : Maybe<&2, U32>}, +N0: Nat,
  +pre: {PH.H.steps(N0, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
    Q.Cfg(A.ex2(v, K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), Wa.Wasm.Memory{p2, lm, gs2, m}) : Wa.Wasm.Step},
  +hpp: N.Le(U32.to_nat(A.nce(nx, on)), U32.to_nat(p2)), +hp: N.Le(U32.to_nat(pg), U32.to_nat(p2)), +hpl: N.Le(U32.to_nat(p2), U32.to_nat(lm)),
  +ecc: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on)) == True{} : Bool}) ->
  SPost.to(Cr.Cir.Out.next{Cr.Cir.State{rg, cl, nx, fi, im, p2, lm, inp, Con{Sd.Byte.from_u32(x), ou}, U32.inc(on)}}, fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G):
  +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +hI2 = A.inv.pg(P, G, a, n, cl, nx, fi, im, pg, p2, lm, inp, ou, on, m, hI, hp, hpl)
  +hroom = A.room.of(A.eb(nx, on), p2, W, hW, F.w16(P, hP, W, hW), hpp)
  +hb = A.pb2.le(p2, lm, G, W, hG, hpl, Q.b.lm(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  +ev2 = Equal.trans(Maybe<&2, U32>, Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, p2, lm, inp, ou, on)), Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Some{x},
    Equal.sym(Maybe<&2, U32>, Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, p2, lm, inp, ou, on)),
      A.eval.pg(v, rg, cl, nx, fi, im, pg, p2, lm, inp, ou, on)), ev)
  +eE = A.emit.E5(v, K, ls, rg, cl, nx, fi, im, p2, lm, inp, ou, on, x, ev2, R, MX, okv, hR, P, G, a, n, nx, A.nce(nx, on), gs2, m, hI2, W, hW, hP, hG, hroom, hb)
  +b = A.eb(nx, on)
  +y = Sd.Byte.from_u32(x)
  +tv = E.tmpE(v, nx, Q.St(rg, cl, nx, fi, im, p2, lm, inp, ou, on))
  +C0 = Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
  +CD = Q.Cfg(A.ex2(v, K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), b, rg), Wa.Wasm.Memory{p2, lm, gs2, m})
  +CE = Q.Cfg(K, ls, [], Q.Loc(a, n, 2, nx, U32.add(on, 1), tv, A.nce(nx, on), b, rg), Wa.Wasm.Memory{p2, lm, gs2, Wa.Wasm.write8(m, U32.add(b, 0), y)})
  +Nt = Nat.add(N0, Nat.add(1n, Nat.add(E.cost(v), 5n)))
  +eq0 = S.steps.then(N0, Nat.add(1n, Nat.add(E.cost(v), 5n)), C0, CD, CE, pre, eE)
  +eq = {(%F.inc.add1(on) : {PH.H.steps(Nt, C0) == Cf(K, ls, a, n, tv, A.nce(nx, on), b, rg, nx, _, p2, lm, gs2, Wa.Wasm.write8(m, b, y)) : Wa.Wasm.Step};
      %Y.U32.add_zero(b) : {PH.H.steps(Nt, C0) == Cf(K, ls, a, n, tv, A.nce(nx, on), b, rg, nx, U32.add(on, 1), p2, lm, gs2, Wa.Wasm.write8(m, _, y)) : Wa.Wasm.Step};
      eq0) : {PH.H.steps(Nt, C0) == Cf(K, ls, a, n, tv, A.nce(nx, on), b, rg, nx, U32.inc(on), p2, lm, gs2, Wa.Wasm.write8(m, b, y)) : Wa.Wasm.Step}}
  (Nt, (tv, (A.nce(nx, on), (b, (Wa.Wasm.write8(m, b, y), (eq,
    A.inv.emit(P, G, a, n, cl, nx, fi, im, pg, p2, lm, inp, ou, on, m, hI, W, hW, hP, hG, x, hp, hpl, hroom,
      I.and.r(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on), ecc))))))))

# the steps of emit's code to the growth
def emit.AB(+v: Cr.Cir.Expr, +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32,
  +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  ecc: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on)) == True{} : Bool}) ->
  {PH.H.steps(26n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
    Q.Cfg(Cr.Cir.code.grow(d, A.ex2(v, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), Wa.Wasm.Memory{pg, lm, gs, m}) : Wa.Wasm.Step}:
  +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
  +L1 = Q.Loc(a, n, 2, nx, on, nx, nd, A.eb(nx, on), rg)
  +vv = U32.and(Bool.to_u32(U32.is_lt(nx, 214748365)), Bool.to_u32(U32.is_ge(A.eb(nx, on), on)))
  +C0 = Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
  +Cb = Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, [Cr.Cir.code.exit(1, 1n+d)]}, Con{Wa.Wasm.Label{0n, None{}, A.ex1(v, d, K), 0n}, ls}, [vv], L1, M0)
  +C1 = Q.Cfg(A.ex1(v, d, K), ls, [], L1, M0)
  +C2 = Q.Cfg(Cr.Cir.code.grow(d, A.ex2(v, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), M0)
  S.steps.then(19n, 7n, C0, Cb, C2, A.emit.E1(v, d, K, ls, a, n, 2, nx, on, t, nd, ad, rg, M0),
    S.steps.then(1n, 6n, Cb, C1, C2, A.un.ok(vv, A.and.ok(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on), ecc), d, A.ex1(v, d, K), ls, L1, M0),
      A.emit.E3(v, d, K, ls, a, n, 2, nx, on, nx, nd, rg, M0)))

# emit{v} whose memory must grow: within the limit (b3), or out of memory
def emit.grow(+fu: Nat, b3: Bool, gr: Bool, +v: Cr.Cir.Expr, +x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +okv: {V.ok.expr(v, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +ev: {Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{x} : Maybe<&2, U32>},
  +ecc: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on)) == True{} : Bool},
  +e2: {U32.is_le(A.nce(nx, on), pg) == False{} : Bool}, +e3: {U32.is_le(A.nce(nx, on), lm) == b3 : Bool}, +egr: {Wa.Wasm.grants(gs) == gr : Bool}) ->
  GPost(Cr.Cir.exec.emit.of(Cr.Cir.room.if(False{}, b3, pg, A.nce(nx, on)), x, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b3 gr:
    case False{} _:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +C2 = Q.Cfg(Cr.Cir.code.grow(d, A.ex2(v, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), M0)
      +hge = A.ge.of(A.nce(nx, on), pg, N.weaken(U32.to_nat(pg), U32.to_nat(A.nce(nx, on)), A.nle.u32(A.nce(nx, on), pg, e2)))
      +eC = A.grow.fail(A.nce(nx, on), d, A.ex2(v, K), ls, hL, A.dep.n(d, 3n, MD, Unit{}, hd), a, n, 2, nx, on, nx, A.eb(nx, on), rg, pg, lm, gs, m, e2, e3, hge)
      Inl{(0n, (Nat.add(26n, 19n), (M0, S.steps.then(26n, 19n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), C2,
        Wa.Wasm.Step.done{[1], M0}, emit.AB(v, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, ecc), eC))))}
    case True{} False{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +C2 = Q.Cfg(Cr.Cir.code.grow(d, A.ex2(v, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), M0)
      +hge = A.ge.of(A.nce(nx, on), pg, N.weaken(U32.to_nat(pg), U32.to_nat(A.nce(nx, on)), A.nle.u32(A.nce(nx, on), pg, e2)))
      +M1 = {Wa.Wasm.Memory{pg, lm, List.drop(&2, Bool, gs, 1n), m} : Wa.Wasm.Memory}
      +eC = A.grow.refused(A.nce(nx, on), d, A.ex2(v, K), ls, hL, A.dep.n(d, 3n, MD, Unit{}, hd), a, n, 2, nx, on, nx, A.eb(nx, on), rg, pg, lm, gs, m, e2, e3, hge, egr)
      Inr{(Nat.add(26n, 19n), (M1, (0n, (S.grants.false(gs, egr), S.steps.then(26n, 19n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), C2,
        Wa.Wasm.Step.done{[1], M1}, emit.AB(v, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, ecc), eC)))))}
    case True{} True{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +hb = Q.pb.le(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG)
      +C2 = Q.Cfg(Cr.Cir.code.grow(d, A.ex2(v, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), M0)
      +hpg = A.pg.ne(pg, W, hW, hb, A.pos.of.D(U32.to_nat(pg), F.b.pb20(P, G, a, nx, fi, im, pg, lm, inp, on, hB)))
      +gs1 = List.drop(&2, Bool, gs, 1n)
      +CD = Q.Cfg(A.ex2(v, K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), Wa.Wasm.Memory{A.nce(nx, on), lm, gs1, m})
      +hlt = A.nle.u32(A.nce(nx, on), pg, e2)
      +hge = A.ge.of(A.nce(nx, on), pg, N.weaken(U32.to_nat(pg), U32.to_nat(A.nce(nx, on)), hlt))
      +eC = A.grow.ok(A.nce(nx, on), d, A.ex2(v, K), ls, a, n, 2, nx, on, nx, A.eb(nx, on), rg, pg, lm, gs, m, e2, e3, hge, hpg, egr)
      Inl{(1n, emit.fin(fu, v, x, rg, cl, nx, fi, im, pg, A.nce(nx, on), lm, inp, ou, on, d, K, ls, R, MX, hR, P, G, a, n, t, nd, ad, gs, gs1, m, hI, W, hW, hP, hG, okv, ev,
        Nat.add(26n, 14n), S.steps.then(26n, 14n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), C2, CD,
          emit.AB(v, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, ecc), eC),
        N.le_refl(U32.to_nat(A.nce(nx, on))), N.weaken(U32.to_nat(pg), U32.to_nat(A.nce(nx, on)), hlt), Z.le.of(A.nce(nx, on), lm, e3), ecc))}

# emit{v}: the memory holds the byte already (b2), or must grow
def emit.room(+fu: Nat, b2: Bool, +v: Cr.Cir.Expr, +x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +okv: {V.ok.expr(v, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +ev: {Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{x} : Maybe<&2, U32>},
  +ecc: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on)) == True{} : Bool},
  +e2: {U32.is_le(A.nce(nx, on), pg) == b2 : Bool}) ->
  GPost(Cr.Cir.exec.emit.of(Cr.Cir.room.if(b2, U32.is_le(A.nce(nx, on), lm), pg, A.nce(nx, on)), x, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b2:
    case True{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +C2 = Q.Cfg(Cr.Cir.code.grow(d, A.ex2(v, K)), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), M0)
      +CD = Q.Cfg(A.ex2(v, K), ls, [], Q.Loc(a, n, 2, nx, on, nx, A.nce(nx, on), A.eb(nx, on), rg), M0)
      +eC = A.grow.skip(A.nce(nx, on), d, A.ex2(v, K), ls, a, n, 2, nx, on, nx, A.eb(nx, on), rg, pg, lm, gs, m, e2)
      Inl{(0n, emit.fin(fu, v, x, rg, cl, nx, fi, im, pg, pg, lm, inp, ou, on, d, K, ls, R, MX, hR, P, G, a, n, t, nd, ad, gs, gs, m, hI, W, hW, hP, hG, okv, ev,
        Nat.add(26n, 5n), S.steps.then(26n, 5n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), C2, CD,
          emit.AB(v, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, ecc), eC),
        Z.le.of(A.nce(nx, on), pg, e2), N.le_refl(U32.to_nat(pg)), Q.b.pg(P, G, a, nx, fi, im, pg, lm, inp, on, hB), ecc))}
    case False{}:
      emit.grow(fu, U32.is_le(A.nce(nx, on), lm), Wa.Wasm.grants(gs), v, x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI,
        W, hW, hP, hG, okv, hd, ev, ecc, e2, {==}, {==})

# emit{v}: the byte's place fits (cc), or out of memory
def emit.ok(+fu: Nat, cc: Bool, +v: Cr.Cir.Expr, +x: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +okv: {V.ok.expr(v, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +ev: {Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == Some{x} : Maybe<&2, U32>},
  +ecc: {Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on)) == cc : Bool}) ->
  GPost(Cr.Cir.exec.emit.if(cc, A.eb(nx, on), x, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match cc:
    case False{}:
      +M0 = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +L1 = Q.Loc(a, n, 2, nx, on, nx, nd, A.eb(nx, on), rg)
      +vv = U32.and(Bool.to_u32(U32.is_lt(nx, 214748365)), Bool.to_u32(U32.is_ge(A.eb(nx, on), on)))
      +Cb = Q.Cfg(Con{Wa.Wasm.Instr.br_if{0}, [Cr.Cir.code.exit(1, 1n+d)]}, Con{Wa.Wasm.Label{0n, None{}, A.ex1(v, d, K), 0n}, ls}, [vv], L1, M0)
      Inl{(0n, (Nat.add(19n, 7n), (M0, S.steps.then(19n, 7n, Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), Cb,
        Wa.Wasm.Step.done{[1], M0}, A.emit.E1(v, d, K, ls, a, n, 2, nx, on, t, nd, ad, rg, M0),
        A.un.fail(vv, A.and.fail(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on), ecc), d, A.ex1(v, d, K), ls, hL, A.dep.n(d, 2n, MD, Unit{}, hd),
          a, n, 2, nx, on, nx, nd, A.eb(nx, on), rg, M0)))))}
    case True{}:
      emit.room(fu, U32.is_le(A.nce(nx, on), pg), v, x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI,
        W, hW, hP, hG, okv, hd, ev, ecc, {==})

# emit{v}, by the value of v
def emit.of0(+fu: Nat, mv: Maybe<&2, U32>, +v: Cr.Cir.Expr, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +okv: {V.ok.expr(v, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD)),
  +ev: {Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>}) ->
  GPost(Cr.Cir.exec.emit(mv, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match mv:
    case None{}:
      Inl{(0n, Unit{})}
    case Some{+x}:
      emit.ok(fu, Bool.and(U32.is_lt(nx, 214748365), U32.is_ge(A.eb(nx, on), on)), v, x, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD,
        P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, okv, hd, ev, {==})

# emit{v}
def sim.emit(+fu: Nat, +v: Cr.Cir.Expr, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(Cr.Cir.Stmt.emit{v}, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, 4n), U32.to_nat(MD))) ->
  GPost(Cr.Cir.exec.emit(Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.emit{v}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  emit.of0(fu, Cr.Cir.eval(v, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD,
    P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, ok, hd, {==})

# The halt
# --------

# the branch out of run from j labels inside it: run gives its status
def exit.steps(+j: Nat, +ls2: List<&2, Wa.Wasm.Label>, +hj: {List.drop(&2, Wa.Wasm.Label, ls2, j) == [RL()] : List<&2, Wa.Wasm.Label>},
  +ej: {U32.to_nat(U32.from_nat(j)) == j : Nat}, +L: List<&2, U32>, +M: Wa.Wasm.Memory) ->
  {PH.H.steps(3n, Q.Cfg([Wa.Wasm.Instr.br{U32.from_nat(j)}], ls2, [], L, M)) ==
    Wa.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : Wa.Wasm.Step}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, ej) :
    {PH.H.steps(2n, Wa.Wasm.step.br(List.drop(&2, Wa.Wasm.Label, ls2, _), 1n, [], L, M)) ==
      Wa.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : Wa.Wasm.Step}
  %Equal.sym(List<&2, Wa.Wasm.Label>, List.drop(&2, Wa.Wasm.Label, ls2, j), [RL()], hj) :
    {PH.H.steps(2n, Wa.Wasm.step.br(_, 1n, [], L, M)) ==
      Wa.Wasm.Step.done{[Maybe.default(&2, U32, List.get(&2, U32, L, 2n), 0)], M} : Wa.Wasm.Step}
  {==}

# a status other than 0 needs no output
def status.nz(b1: Bool, b2: Bool, +mem: Wa.Wasm.Memory, +f: Bool, +ou: List<&2, Word(8n)>) ->
  {Wa.Wasm.run.status(False{}, b1, b2, mem) == Cr.Cir.ended.halt(False{}, b1, b2, f, ou) : Wa.Wasm.Outcome}:
  match b1 b2:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the host reads the output at A0, of on bytes, when it fits: what Cir.ended
# says
def hok.if(b: Bool, +m2: Wa.Wasm.Bytes, +A0: U32, +on: U32, +ou: List<&2, Word(8n)>,
  rb: {Q.RB(U32.to_nat(on), m2, A0) == List.reverse(&2, Word(8n), ou) : List<&2, Word(8n)>}) ->
  {Wa.Wasm.run.output.if(b, m2, A0, on) == Cr.Cir.ended.output(b, ou) : Wa.Wasm.Outcome}:
  match b:
    case True{}:
      Equal.cong(List<&2, Word(8n)>, Wa.Wasm.Outcome, l => Wa.Wasm.Outcome.result{l}, Wa.Wasm.read.bytes(U32.to_nat(on), m2, A0),
        List.reverse(&2, Word(8n), ou),
        Equal.trans(List<&2, Word(8n)>, Wa.Wasm.read.bytes(U32.to_nat(on), m2, A0), Q.RB(U32.to_nat(on), m2, A0), List.reverse(&2, Word(8n), ou),
          F.rb.read(U32.to_nat(on), m2, A0), rb))
    case False{}:
      {==}

# the host reads the output from the address A0 at byte 0, of the length on
# at byte 4
def hok.fin(+pg: U32, +lm: U32, +gs: List<&2, Bool>, +m2: Wa.Wasm.Bytes, +A0: U32, +on: U32, +ou: List<&2, Word(8n)>,
  f8: {Wa.Wasm.fits(pg, 0, 8) == True{} : Bool}, v0: {Y.V32(m2, 0) == A0 : U32}, v4: {Y.V32(m2, 4) == on : U32},
  rb: {Q.RB(U32.to_nat(on), m2, A0) == List.reverse(&2, Word(8n), ou) : List<&2, Word(8n)>}) ->
  {Wa.Wasm.run.output(Wa.Wasm.Memory{pg, lm, gs, m2}) == Cr.Cir.ended.output(Wa.Wasm.fits(pg, A0, on), ou) : Wa.Wasm.Outcome}:
  +R = Cr.Cir.ended.output(Wa.Wasm.fits(pg, A0, on), ou)
  %Equal.sym(Bool, Wa.Wasm.fits(pg, 0, 8), True{}, f8) : {Wa.Wasm.run.output.at(_, pg, m2) == R : Wa.Wasm.Outcome}
  %Equal.sym(Wa.Wasm.Peek<U32>, Wa.Wasm.read32(m2, 0), Wa.Wasm.Peek{Y.V32(m2, 0), m2}, Y.read32.eq(m2, 0)) :
    {Wa.Wasm.run.output.a(pg, _) == R : Wa.Wasm.Outcome}
  %Equal.sym(U32, Y.V32(m2, 0), A0, v0) : {Wa.Wasm.run.output.n(pg, _, Wa.Wasm.read32(m2, 4)) == R : Wa.Wasm.Outcome}
  %Equal.sym(Wa.Wasm.Peek<U32>, Wa.Wasm.read32(m2, 4), Wa.Wasm.Peek{Y.V32(m2, 4), m2}, Y.read32.eq(m2, 4)) :
    {Wa.Wasm.run.output.n(pg, A0, _) == R : Wa.Wasm.Outcome}
  %Equal.sym(U32, Y.V32(m2, 4), on, v4) : {Wa.Wasm.run.output.if(Wa.Wasm.fits(pg, A0, _), m2, A0, _) == R : Wa.Wasm.Outcome}
  hok.if(Wa.Wasm.fits(pg, A0, on), m2, A0, on, ou, rb)

# the output after the writes of its place at bytes 0 to 7
def hok.rb(+m: Wa.Wasm.Bytes, +A0: U32, +on: U32, +X: Nat, +ex: {U32.to_nat(A0) == X : Nat}, +ou: List<&2, Word(8n)>,
  +P: Nat, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat}, +W: Nat, +hW: {W == PH.H.W(32n) : Nat},
  +h8: N.Le(8n, X), +hx: N.Le(Nat.add(U32.to_nat(on), X), W),
  ro: {Q.RB(U32.to_nat(on), m, A0) == List.reverse(&2, Word(8n), ou) : List<&2, Word(8n)>}) ->
  {Q.RB(U32.to_nat(on), Wa.Wasm.write32(Wa.Wasm.write32(m, 0, A0), 4, on), A0) == List.reverse(&2, Word(8n), ou) : List<&2, Word(8n)>}:
  +m1 = Wa.Wasm.write32(m, 0, A0)
  +ON = U32.to_nat(on)
  +h16 = F.w16(P, hP, W, hW)
  Equal.trans(List<&2, Word(8n)>, Q.RB(ON, Wa.Wasm.write32(m1, 4, on), A0), Q.RB(ON, m1, A0), List.reverse(&2, Word(8n), ou),
    F.RB.w32(ON, m1, 4, on, A0, X, ex, W, hW, N.le_trans(8n, 16n, W, Unit{}, h16), hx, Inr{h8}),
    Equal.trans(List<&2, Word(8n)>, Q.RB(ON, m1, A0), Q.RB(ON, m, A0), List.reverse(&2, Word(8n), ou),
      F.RB.w32(ON, m, 0, A0, A0, X, ex, W, hW, N.le_trans(4n, 16n, W, Unit{}, h16), hx, Inr{N.le_trans(4n, 8n, X, Unit{}, h8)}), ro))

# the output of ON = on bytes at X = 20 × nx ends by 2^32: it is empty, or
# it ends within the memory
def hok.hx(ON: Nat, +pg: U32, +nx: U32, +on: U32, +X: Nat,
  +ex: {U32.to_nat(Cr.Cir.at(nx)) == X : Nat}, +eX: {X == PH.H.t20(U32.to_nat(nx)) : Nat}, +eon: {U32.to_nat(on) == ON : Nat},
  +W: Nat, +hxw: N.Le(1n+X, W), +hb: N.Le(Q.PB(pg), W), +hof: Q.OF(ON, U32.to_nat(nx), Q.PB(pg))) ->
  N.Le(Nat.add(U32.to_nat(on), X), W):
  match ON:
    case 0n:
      {(%Equal.sym(Nat, U32.to_nat(on), 0n, eon) : N.Le(Nat.add(_, X), W); N.weaken(X, W, hxw)) : N.Le(Nat.add(U32.to_nat(on), X), W)}
    case 1n+q:
      +A0 = Cr.Cir.at(nx)
      +hend = N.le_rw_l(Nat.add(PH.H.t20(U32.to_nat(nx)), 1n+q), Nat.add(U32.to_nat(A0), U32.to_nat(on)), Q.PB(pg),
        Equal.trans(Nat, Nat.add(PH.H.t20(U32.to_nat(nx)), 1n+q), Nat.add(X, 1n+q), Nat.add(U32.to_nat(A0), U32.to_nat(on)),
          Equal.cong(Nat, Nat, z => Nat.add(z, 1n+q), PH.H.t20(U32.to_nat(nx)), X, Equal.sym(Nat, X, PH.H.t20(U32.to_nat(nx)), eX)),
          Equal.trans(Nat, Nat.add(X, 1n+q), Nat.add(U32.to_nat(A0), 1n+q), Nat.add(U32.to_nat(A0), U32.to_nat(on)),
            Equal.cong(Nat, Nat, z => Nat.add(z, 1n+q), X, U32.to_nat(A0), Equal.sym(Nat, U32.to_nat(A0), X, ex)),
            Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(A0), z), 1n+q, U32.to_nat(on), Equal.sym(Nat, U32.to_nat(on), 1n+q, eon)))), hof)
      N.le_trans(Nat.add(U32.to_nat(on), X), Q.PB(pg), W,
        N.le_rw_l(Nat.add(U32.to_nat(A0), U32.to_nat(on)), Nat.add(U32.to_nat(on), X), Q.PB(pg),
          Equal.trans(Nat, Nat.add(U32.to_nat(A0), U32.to_nat(on)), Nat.add(X, U32.to_nat(on)), Nat.add(U32.to_nat(on), X),
            Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(on)), U32.to_nat(A0), X, ex), Z.add.comm(X, U32.to_nat(on))), hend), hb)

# a halt with the status 0: the host reads the output as Cir.ended says, or
# traps where it says so
def haltok0(+P: Nat, +G: Nat, +a: U32, +n: U32, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}) ->
  HaltOK(0, nx, pg, on, ou, Wa.Wasm.Memory{pg, lm, gs, Wa.Wasm.write32(Wa.Wasm.write32(m, 0, Cr.Cir.at(nx)), 4, on)}):
  +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +NX = U32.to_nat(nx)
  +X = PH.H.t20(NX)
  +A0 = Cr.Cir.at(nx)
  +m1 = Wa.Wasm.write32(m, 0, A0)
  +m2 = Wa.Wasm.write32(m1, 4, on)
  +hb = Q.pb.le(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG)
  +ex = F.at.nat(nx, P, hP, Q.b.nx(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  +h20 = F.inv.x20(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
  +f8 = F.fits.ok(pg, 0, 8, W, hW, Unit{}, N.le_trans(8n, 20n, Q.PB(pg), Unit{}, F.b.pb20(P, G, a, nx, fi, im, pg, lm, inp, on, hB)), hb)
  +v0 = Equal.trans(U32, Y.V32(m2, 0), Y.V32(m1, 0), A0, Y.V32.out32(m1, 4, on, 0, F.d04()), Y.V32.same(m, 0, A0))
  +v4 = Y.V32.same(m1, 4, on)
  +hx = hok.hx(U32.to_nat(on), pg, nx, on, X, ex, {==}, {==}, W, F.b.xw(G, a, nx, fi, im, pg, lm, inp, on, P, hP, W, hW, hB), hb,
    Q.b.of(P, G, a, nx, fi, im, pg, lm, inp, on, hB))
  hok.fin(pg, lm, gs, m2, A0, on, ou, f8, v0, v4,
    hok.rb(m, A0, on, X, ex, ou, P, hP, W, hW, N.le_trans(8n, 20n, X, Unit{}, h20), hx,
      Q.inv.out(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)))

# halt{s0}, by the code of its result (z = s0 is 0)
def halt.z(z: Bool, +s0: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +MD: U32, +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hd: N.Le(Nat.add(d, 2n), U32.to_nat(MD)), +ez: {U32.is_zero(s0) == z : Bool}) ->
  SPost.halt(s0, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on), Con{Cr.Cir.i.block(Con{Cr.Cir.i.const(s0), Con{Cr.Cir.i.set(Cr.Cir.l.status()),
    List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(z), [Wa.Wasm.Instr.br{U32.from_nat(1n+d)}])}}), K}, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m):
  match z:
    case False{}:
      +ej = M.tofrom(1n+d, MD, N.le_trans(1n+d, Nat.add(d, 2n), U32.to_nat(MD), N.lt_add(d, 1n), hd))
      +LS = {Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls} : List<&2, Wa.Wasm.Label>}
      +BR = {[Wa.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, Wa.Wasm.Instr>}
      +L1 = Q.Loc(a, n, s0, nx, on, t, nd, ad, rg)
      +X = {Con{Cr.Cir.i.block(Con{Cr.Cir.i.const(s0), Con{Cr.Cir.i.set(Cr.Cir.l.status()), List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(False{}), BR)}}), K} : List<&2, Wa.Wasm.Instr>}
      +C0 = Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C1 = Q.Cfg(BR, LS, [], L1, Wa.Wasm.Memory{pg, lm, gs, m})
      +mm = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +fo = Wa.Wasm.fits(pg, Cr.Cir.at(nx), on)
      +ok = {(%Equal.sym(Bool, U32.is_zero(s0), False{}, ez) :
          {Wa.Wasm.run.status(_, U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm) == Cr.Cir.ended.halt(_, U32.is_eq(s0, 1), U32.is_eq(s0, 2), fo, ou) : Wa.Wasm.Outcome};
          status.nz(U32.is_eq(s0, 1), U32.is_eq(s0, 2), mm, fo, ou)) : HaltOK(s0, nx, pg, on, ou, mm)}
      (6n, (mm, (S.steps.then(3n, 3n, C0, C1, Wa.Wasm.Step.done{[s0], mm}, {==}, exit.steps(1n+d, LS, hL, ej, L1, mm)), ok)))
    case True{}:
      +ej = M.tofrom(1n+d, MD, N.le_trans(1n+d, Nat.add(d, 2n), U32.to_nat(MD), N.lt_add(d, 1n), hd))
      +LS = {Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls} : List<&2, Wa.Wasm.Label>}
      +BR = {[Wa.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, Wa.Wasm.Instr>}
      +L1 = Q.Loc(a, n, s0, nx, on, t, nd, ad, rg)
      +hB = Q.inv.bounds(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m, hI)
      +hb = Q.pb.le(P, G, a, nx, fi, im, pg, lm, inp, on, hB, W, hG)
      +p20 = F.b.pb20(P, G, a, nx, fi, im, pg, lm, inp, on, hB)
      +A0 = Cr.Cir.at(nx)
      +R2 = {[Cr.Cir.i.const(0), Cr.Cir.i.get(Cr.Cir.l.outn()), Wa.Wasm.Instr.store{4}, Wa.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, Wa.Wasm.Instr>}
      +R3 = {[Wa.Wasm.Instr.store{4}, Wa.Wasm.Instr.br{U32.from_nat(1n+d)}] : List<&2, Wa.Wasm.Instr>}
      +L2 = Q.Loc(a, n, s0, nx, on, nx, nd, ad, rg)
      +m1 = Wa.Wasm.write32(m, 0, A0)
      +m2 = Wa.Wasm.write32(m1, 4, on)
      +X = {Con{Cr.Cir.i.block(Con{Cr.Cir.i.const(s0), Con{Cr.Cir.i.set(Cr.Cir.l.status()), List.append(&2, Wa.Wasm.Instr, Cr.Cir.code.result(True{}), BR)}}), K} : List<&2, Wa.Wasm.Instr>}
      +C0 = Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C1 = Q.Cfg(Con{Wa.Wasm.Instr.store{0}, R2}, LS, [A0, 0], L2, Wa.Wasm.Memory{pg, lm, gs, m})
      +C2 = Q.Cfg(R2, LS, [], L2, Wa.Wasm.Memory{pg, lm, gs, m1})
      +C3 = Q.Cfg(R3, LS, [on, 0], L2, Wa.Wasm.Memory{pg, lm, gs, m1})
      +C4 = Q.Cfg(BR, LS, [], L2, Wa.Wasm.Memory{pg, lm, gs, m2})
      +mm = {Wa.Wasm.Memory{pg, lm, gs, m2} : Wa.Wasm.Memory}
      +hin0 = Z.inside.le(pg, 0, 0, 4, W, hW, Unit{}, N.le_trans(4n, 20n, Q.PB(pg), Unit{}, p20), hb)
      +hin4 = Z.inside.le(pg, 0, 4, 4, W, hW, Unit{}, N.le_trans(8n, 20n, Q.PB(pg), Unit{}, p20), hb)
      +e1 = {{==} : {PH.H.steps(12n, C0) == C1 : Wa.Wasm.Step}}
      +e2 = F.store.step(0, 0, A0, R2, LS, [], L2, pg, lm, gs, m, hin0)
      +e3 = {{==} : {PH.H.steps(2n, C2) == C3 : Wa.Wasm.Step}}
      +e4 = F.store.step(4, 0, on, BR, LS, [], L2, pg, lm, gs, m1, hin4)
      +e5 = exit.steps(1n+d, LS, hL, ej, L2, mm)
      +e45 = S.steps.then(1n, 3n, C3, C4, Wa.Wasm.Step.done{[s0], mm}, e4, e5)
      +e35 = S.steps.then(2n, 4n, C2, C3, Wa.Wasm.Step.done{[s0], mm}, e3, e45)
      +e25 = S.steps.then(1n, 6n, C1, C2, Wa.Wasm.Step.done{[s0], mm}, e2, e35)
      +e15 = S.steps.then(12n, 7n, C0, C1, Wa.Wasm.Step.done{[s0], mm}, e1, e25)
      +es0 = Y.U32.eq(s0, 0, ez)
      +ok = {(%Equal.sym(U32, s0, 0, es0) : HaltOK(_, nx, pg, on, ou, mm);
          haltok0(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, gs, m, hI, W, hW, hP, hG)) : HaltOK(s0, nx, pg, on, ou, mm)}
      (19n, (mm, (e15, ok)))

# halt{s}
def sim.halt(+fu: Nat, +s0: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +hd: N.Le(Nat.add(d, 2n), U32.to_nat(MD))) ->
  GPost(Cr.Cir.Out.halt{s0, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)}, fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.halt{s0}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  Inl{(0n, halt.z(U32.is_zero(s0), s0, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, hd, {==}))}

# Steps of the control
# --------------------

# eqz, then br_if l, of a value that is not 0: no branch
def brif.go(+vc: U32, ez: {U32.is_zero(vc) == False{} : Bool}, +l: U32, +rest: List<&2, Wa.Wasm.Instr>,
  +ls: List<&2, Wa.Wasm.Label>, +L: List<&2, U32>, +M: Wa.Wasm.Memory) ->
  {PH.H.steps(2n, Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{l}, rest}}, ls, [vc], L, M)) == Q.Cfg(rest, ls, [], L, M) : Wa.Wasm.Step}:
  %Equal.sym(Bool, U32.is_zero(vc), False{}, ez) :
    {Wa.Wasm.step.br_if.if(U32.is_zero(Bool.to_u32(_)), l, rest, ls, 1n, [], L, M) == Q.Cfg(rest, ls, [], L, M) : Wa.Wasm.Step}
  {==}

# eqz, then br_if 0, of 0: a branch to the end of the block
def brif.br0(+vc: U32, ez: {U32.is_zero(vc) == True{} : Bool}, +rest: List<&2, Wa.Wasm.Instr>, +after: List<&2, Wa.Wasm.Instr>,
  +outer: List<&2, Wa.Wasm.Label>, +L: List<&2, U32>, +M: Wa.Wasm.Memory) ->
  {PH.H.steps(2n, Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, rest}}, Con{Wa.Wasm.Label{0n, None{}, after, 0n}, outer}, [vc], L, M)) ==
    Q.Cfg(after, outer, [], L, M) : Wa.Wasm.Step}:
  %Equal.sym(Bool, U32.is_zero(vc), True{}, ez) :
    {Wa.Wasm.step.br_if.if(U32.is_zero(Bool.to_u32(_)), 0, rest, Con{Wa.Wasm.Label{0n, None{}, after, 0n}, outer}, 1n, [], L, M) ==
      Q.Cfg(after, outer, [], L, M) : Wa.Wasm.Step}
  {==}

# eqz, then br_if 1, of 0: a branch to the end of the outer block
def brif.br1(+vc: U32, ez: {U32.is_zero(vc) == True{} : Bool}, +rest: List<&2, Wa.Wasm.Instr>, +l0: Wa.Wasm.Label,
  +after: List<&2, Wa.Wasm.Instr>, +outer: List<&2, Wa.Wasm.Label>, +L: List<&2, U32>, +M: Wa.Wasm.Memory) ->
  {PH.H.steps(2n, Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, rest}}, Con{l0, Con{Wa.Wasm.Label{0n, None{}, after, 0n}, outer}}, [vc], L, M)) ==
    Q.Cfg(after, outer, [], L, M) : Wa.Wasm.Step}:
  %Equal.sym(Bool, U32.is_zero(vc), True{}, ez) :
    {Wa.Wasm.step.br_if.if(U32.is_zero(Bool.to_u32(_)), 1, rest, Con{l0, Con{Wa.Wasm.Label{0n, None{}, after, 0n}, outer}}, 1n, [], L, M) ==
      Q.Cfg(after, outer, [], L, M) : Wa.Wasm.Step}
  {==}

# register r is local 8 + r
def reg.nat(+r: Nat, +R: Nat, +MX: U32, ok: {Nat.is_lt(r, R) == True{} : Bool}, hR: N.Le(8n+R, U32.to_nat(MX))) ->
  {U32.to_nat(Cr.Cir.l.reg(r)) == 8n+r : Nat}:
  +le = N.le_trans(8n+r, 8n+R, U32.to_nat(MX), N.weaken(r, R, M.lt_le(r, R, ok)), hR)
  Equal.trans(Nat, U32.to_nat(Cr.Cir.l.reg(r)), U32.to_nat(U32.from_nat(8n+r)), 8n+r,
    Equal.cong(U32, Nat, z => U32.to_nat(z), Cr.Cir.l.reg(r), U32.from_nat(8n+r), V.add8(r)), M.tofrom(8n+r, MX, le))

# local.set of register r
def set.step(+r: Nat, +v: U32, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32,
  +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes, hr: {U32.to_nat(Cr.Cir.l.reg(r)) == 8n+r : Nat}) ->
  {PH.H.steps(1n, Q.Cfg(Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), K}, ls, [v], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})) ==
    Cf(K, ls, a, n, t, nd, ad, List.set(&2, U32, rg, r, v), nx, on, pg, lm, gs, m) : Wa.Wasm.Step}:
  %Equal.sym(Nat, U32.to_nat(Cr.Cir.l.reg(r)), 8n+r, hr) :
    {Wa.Wasm.Step.next{Wa.Wasm.Frame{K, ls, 1n, [], List.set(&2, U32, Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), _, v)}, Wa.Wasm.Memory{pg, lm, gs, m}} ==
      Cf(K, ls, a, n, t, nd, ad, List.set(&2, U32, rg, r, v), nx, on, pg, lm, gs, m) : Wa.Wasm.Step}
  {==}

# The code of a frame, and its labels
def st.code(st: Wa.Wasm.Step) -> List<&2, Wa.Wasm.Instr>:
  match st:
    case Wa.Wasm.Step.next{Wa.Wasm.Frame{code, _, _, _, _}, _}:
      code
    case _:
      []

def st.labels(st: Wa.Wasm.Step) -> List<&2, Wa.Wasm.Label>:
  match st:
    case Wa.Wasm.Step.next{Wa.Wasm.Frame{_, ls, _, _, _}, _}:
      ls
    case _:
      []

def ne.len(+x: Nat, e: {1n+x == x : Nat}) -> Empty:
  N.not_succ_le(x, N.le_rw_l(x, 1n+x, x, Equal.sym(Nat, 1n+x, x, e), N.le_refl(x)))

# a code is not its own tail
def code.ne(+i: Wa.Wasm.Instr, +K: List<&2, Wa.Wasm.Instr>, e: {Con{i, K} == K : List<&2, Wa.Wasm.Instr>}) -> Empty:
  ne.len(List.length(&2, Wa.Wasm.Instr, K),
    Equal.cong(List<&2, Wa.Wasm.Instr>, Nat, l => List.length(&2, Wa.Wasm.Instr, l), Con{i, K}, K, e))

def labels.ne(+l: Wa.Wasm.Label, +ls: List<&2, Wa.Wasm.Label>, e: {Con{l, ls} == ls : List<&2, Wa.Wasm.Label>}) -> Empty:
  ne.len(List.length(&2, Wa.Wasm.Label, ls),
    Equal.cong(List<&2, Wa.Wasm.Label>, Nat, z => List.length(&2, Wa.Wasm.Label, z), Con{l, ls}, ls, e))

# n steps from x, whose first two steps reach y, and that reach z, which is
# neither x nor the step after it, are n - 2 steps from y
def skip2(+N0: Nat, +fr: Wa.Wasm.Frame, +mm: Wa.Wasm.Memory, +fr1: Wa.Wasm.Frame, +m1: Wa.Wasm.Memory, +Yv: Wa.Wasm.Step, -Zv: Wa.Wasm.Step,
  e: {PH.H.steps(N0, Wa.Wasm.Step.next{fr, mm}) == Zv : Wa.Wasm.Step},
  h1: {Wa.Wasm.step(PH.H.TS(), fr, mm) == Wa.Wasm.Step.next{fr1, m1} : Wa.Wasm.Step},
  h2: {Wa.Wasm.step(PH.H.TS(), fr1, m1) == Yv : Wa.Wasm.Step},
  ne0: {Wa.Wasm.Step.next{fr, mm} == Zv : Wa.Wasm.Step} -> Empty,
  ne1: {Wa.Wasm.Step.next{fr1, m1} == Zv : Wa.Wasm.Step} -> Empty) ->
  {PH.H.steps(Nat.sub(N0, 2n), Yv) == Zv : Wa.Wasm.Step}:
  match N0:
    case 0n:
      Empty.absurd({PH.H.steps(0n, Yv) == Zv : Wa.Wasm.Step}, ne0(e))
    case 1n+N1:
      match N1:
        case 0n:
          Empty.absurd({PH.H.steps(0n, Yv) == Zv : Wa.Wasm.Step}, ne1(Equal.trans(Wa.Wasm.Step, Wa.Wasm.Step.next{fr1, m1}, Wa.Wasm.step(PH.H.TS(), fr, mm), Zv,
            Equal.sym(Wa.Wasm.Step, Wa.Wasm.step(PH.H.TS(), fr, mm), Wa.Wasm.Step.next{fr1, m1}, h1), e)))
        case 1n+N2:
          +e1 = Equal.trans(Wa.Wasm.Step, PH.H.steps(1n+N2, Wa.Wasm.Step.next{fr1, m1}), PH.H.steps(1n+N2, Wa.Wasm.step(PH.H.TS(), fr, mm)), Zv,
            Equal.cong(Wa.Wasm.Step, Wa.Wasm.Step, x => PH.H.steps(1n+N2, x), Wa.Wasm.Step.next{fr1, m1}, Wa.Wasm.step(PH.H.TS(), fr, mm),
              Equal.sym(Wa.Wasm.Step, Wa.Wasm.step(PH.H.TS(), fr, mm), Wa.Wasm.Step.next{fr1, m1}, h1)), e)
          %Equal.sym(Nat, Nat.sub(N2, 0n), N2, Q.sub0(N2)) : {PH.H.steps(_, Yv) == Zv : Wa.Wasm.Step}
          Equal.trans(Wa.Wasm.Step, PH.H.steps(N2, Yv), PH.H.steps(N2, Wa.Wasm.step(PH.H.TS(), fr1, m1)), Zv,
            Equal.cong(Wa.Wasm.Step, Wa.Wasm.Step, x => PH.H.steps(N2, x), Yv, Wa.Wasm.step(PH.H.TS(), fr1, m1), Equal.sym(Wa.Wasm.Step, Wa.Wasm.step(PH.H.TS(), fr1, m1), Yv, h2)), e1)

# Depths
# ------

def dep.seq.l(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(d, x), U32.to_nat(MD)):
  N.le_trans(Nat.add(d, x), Nat.add(Nat.add(d, x), y), U32.to_nat(MD), N.le_add_r(Nat.add(d, x), y),
    N.le_rw_l(Nat.add(d, Nat.add(x, y)), Nat.add(Nat.add(d, x), y), U32.to_nat(MD),
      Equal.sym(Nat, Nat.add(Nat.add(d, x), y), Nat.add(d, Nat.add(x, y)), Z.add.assoc(d, x, y)), h))

def dep.seq.r(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(d, y), U32.to_nat(MD)):
  dep.seq.l(d, y, x, MD, N.le_rw_l(Nat.add(d, Nat.add(x, y)), Nat.add(d, Nat.add(y, x)), U32.to_nat(MD),
    Equal.cong(Nat, Nat, z => Nat.add(d, z), Nat.add(x, y), Nat.add(y, x), Z.add.comm(x, y)), h))

def dep.two(+d: Nat, +x: Nat, +MD: U32, h: N.Le(Nat.add(d, 2n+x), U32.to_nat(MD))) -> N.Le(Nat.add(2n+d, x), U32.to_nat(MD)):
  N.le_rw_l(Nat.add(d, 2n+x), 2n+Nat.add(d, x), U32.to_nat(MD),
    Equal.trans(Nat, Nat.add(d, 2n+x), 1n+Nat.add(d, 1n+x), 2n+Nat.add(d, x), N.add_succ_r(d, 1n+x),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(d, 1n+x), 1n+Nat.add(d, x), N.add_succ_r(d, x))), h)

def dep.if.t(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, 2n+Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(2n+d, x), U32.to_nat(MD)):
  dep.seq.l(2n+d, x, y, MD, dep.two(d, Nat.add(x, y), MD, h))

def dep.if.e(+d: Nat, +x: Nat, +y: Nat, +MD: U32, h: N.Le(Nat.add(d, 2n+Nat.add(x, y)), U32.to_nat(MD))) -> N.Le(Nat.add(1n+d, y), U32.to_nat(MD)):
  N.weaken(Nat.add(1n+d, y), U32.to_nat(MD), dep.seq.r(2n+d, x, y, MD, dep.two(d, Nat.add(x, y), MD, h)))

# The statements of control
# -------------------------

def set.if(+fu: Nat, b: Bool, +r: Nat, +v: U32, +e: Cr.Cir.Expr, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat}, +tE: U32,
  ex: {PH.H.steps(E.cost(e), Cf(Cr.Cir.code.expr(e, Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), K}), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)) ==
    Q.Cfg(Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), K}, ls, [v], Q.Loc(a, n, 2, nx, on, tE, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}) : Wa.Wasm.Step},
  hr: {U32.to_nat(Cr.Cir.l.reg(r)) == 8n+r : Nat}) ->
  SPost(Cr.Cir.exec.set.of(Cr.Cir.regs.set.if(b, rg, r, v), Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.set{r, e}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match b:
    case True{}:
      +C0 = Cf(Cr.Cir.code.expr(e, Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), K}), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C1 = Q.Cfg(Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), K}, ls, [v], Q.Loc(a, n, 2, nx, on, tE, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})
      +C2 = Cf(K, ls, a, n, tE, nd, ad, List.set(&2, U32, rg, r, v), nx, on, pg, lm, gs, m)
      (Nat.add(E.cost(e), 1n), (tE, (nd, (ad, (m, (S.steps.then(E.cost(e), 1n, C0, C1, C2, ex,
        set.step(r, v, K, ls, a, n, tE, nd, ad, rg, nx, on, pg, lm, gs, m, hr)), hI))))))
    case False{}:
      Unit{}

def set.of(+fu: Nat, mv: Maybe<&2, U32>, +r: Nat, +e: Cr.Cir.Expr, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(Cr.Cir.Stmt.set{r, e}, R) == True{} : Bool}, ev: {Cr.Cir.eval(e, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>}) ->
  GPost(Cr.Cir.exec.set(r, mv, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.set{r, e}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match mv:
    case None{}:
      Inl{(0n, Unit{})}
    case Some{+v}:
      Inl{(0n, set.if(fu, Nat.is_lt(r, List.length(&2, U32, rg)), r, v, e, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, E.tmpE(e, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)),
        E.sim.expr(e, rg, cl, nx, fi, im, pg, lm, inp, ou, on, v, ev, R, MX, I.and.r(Nat.is_lt(r, R), V.ok.expr(e, R), ok), hR,
          Con{Cr.Cir.i.set(Cr.Cir.l.reg(r)), K}, ls, [], P, G, a, n, 2, t, nd, ad, gs, m, hI, W, hW, hP, hG),
        reg.nat(r, R, MX, I.and.l(Nat.is_lt(r, R), V.ok.expr(e, R), ok), hR)))}

def if.z(z: Bool, +fuel: Nat, +c: Cr.Cir.Expr, +te: Cr.Cir.Stmt, +ee: Cr.Cir.Stmt, +vc: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ez: {U32.is_zero(vc) == z : Bool},
  +ex: {PH.H.steps(E.cost(c), Q.Cfg(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}])}}), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})) ==
    Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}])}}, Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}) : Wa.Wasm.Step},
  pt: GPost(Cr.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}]), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [Wa.Wasm.Instr.br{1}], Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G),
  pe: GPost(Cr.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, Cr.Cir.code.stmt(ee, 1n+d, []), Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, [], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G)) ->
  GPost(Cr.Cir.exec.if.of(z, u => Cr.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), u => Cr.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on))), fuel,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match z:
    case False{}:
      +C0 = Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.if{c, te, ee}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C1 = Q.Cfg(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}])}}), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})
      +C2 = Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}])}}, Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})
      +C3 = Cf(Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}]), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m)
      gpost.wrap(Cr.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, Cr.Cir.code.stmt(Cr.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G,
        Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}]), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [Wa.Wasm.Instr.br{1}], Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, Nat.add(2n, Nat.add(E.cost(c), 2n)),
        S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, C1, C3, {==}, S.steps.then(E.cost(c), 2n, C1, C2, C3, ex,
          brif.go(vc, ez, 0, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}]), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}))),
        fuel, N.le_add_l(Nat.add(2n, Nat.add(E.cost(c), 2n)), fuel), 1n, t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => gs2 => m2 => {==}, pt)
    case True{}:
      +C0 = Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.if{c, te, ee}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C1 = Q.Cfg(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}])}}), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})
      +C2 = Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}])}}, Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})
      +C3 = Cf(Cr.Cir.code.stmt(ee, 1n+d, []), Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m)
      gpost.wrap(Cr.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, Cr.Cir.code.stmt(Cr.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G,
        Cr.Cir.code.stmt(ee, 1n+d, []), Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, [], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, Nat.add(2n, Nat.add(E.cost(c), 2n)),
        S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, C1, C3, {==}, S.steps.then(E.cost(c), 2n, C1, C2, C3, ex,
          brif.br0(vc, ez, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}]), Cr.Cir.code.stmt(ee, 1n+d, []), Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}))),
        fuel, N.le_add_l(Nat.add(2n, Nat.add(E.cost(c), 2n)), fuel), 1n, t2 => nd2 => ad2 => rg2 => nx2 => on2 => pg2 => lm2 => gs2 => m2 => {==}, pe)

def if.of(mv: Maybe<&2, U32>, +fuel: Nat, +c: Cr.Cir.Expr, +te: Cr.Cir.Stmt, +ee: Cr.Cir.Stmt, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, ev: {Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>},
  pt: GPost(Cr.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}]), Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [Wa.Wasm.Instr.br{1}], Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G),
  pe: GPost(Cr.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, Cr.Cir.code.stmt(ee, 1n+d, []), Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, [], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G)) ->
  GPost(Cr.Cir.exec.if(mv, u => Cr.Cir.exec(fuel, te, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), u => Cr.Cir.exec(fuel, ee, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on))), fuel,
    Cr.Cir.code.stmt(Cr.Cir.Stmt.if{c, te, ee}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match mv:
    case None{}:
      Inl{(0n, Unit{})}
    case Some{+vc}:
      if.z(U32.is_zero(vc), fuel, c, te, ee, vc, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, {==},
        E.sim.expr(c, rg, cl, nx, fi, im, pg, lm, inp, ou, on, vc, ev, R, MX, okc, hR, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{0}, Cr.Cir.code.stmt(te, 2n+d, [Wa.Wasm.Instr.br{1}])}}, Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [], P, G, a, n, 2, t, nd, ad, gs, m, hI, W, hW, hP, hG),
        pt, pe)

# a run of the loop from its start, seen from the branch back to it
def post.skip.to(o: Cr.Cir.Out, +fu: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat, p: SPost.to(o, fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G)) ->
  SPost.to(o, Nat.sub(fu, 1n), [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G):
  match o:
    case Cr.Cir.Out.next{st2}:
      match st2:
        case Cr.Cir.State{+rg3, +cl3, +nx3, +fi3, +im3, +pg3, +lm3, +inp3, +ou3, +on3}:
          (+N2, p1) = p
          (+t3, p2) = p1
          (+nd3, p3) = p2
          (+ad3, p4) = p3
          (+m3, p5) = p4
          (eq, hI) = p5
          +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
          +mm = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
          +fr = {Wa.Wasm.Frame{Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : Wa.Wasm.Frame}
          +fr1 = {Wa.Wasm.Frame{[Cr.Cir.i.loop(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}))], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, 1n, [], L} : Wa.Wasm.Frame}
          +Yv = Cf(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
          +Cb = Cf([Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
          +END = Cf(K, ls, a, n, t3, nd3, ad3, rg3, nx3, on3, pg3, lm3, gs2, m3)
          +sk = skip2(N2, fr, mm, fr1, mm, Yv, END, eq, {==}, {==},
            e => code.ne(Cr.Cir.i.block([Cr.Cir.i.loop(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}))]), K,
              Equal.cong(Wa.Wasm.Step, List<&2, Wa.Wasm.Instr>, x => st.code(x), Wa.Wasm.Step.next{fr, mm}, END, e)),
            e => labels.ne(Wa.Wasm.Label{0n, None{}, K, 0n}, ls, Equal.cong(Wa.Wasm.Step, List<&2, Wa.Wasm.Label>, x => st.labels(x), Wa.Wasm.Step.next{fr1, mm}, END, e)))
          (Nat.add(1n, Nat.sub(N2, 2n)), (t3, (nd3, (ad3, (m3, (S.steps.then(1n, Nat.sub(N2, 2n), Cb, Yv, END, {==}, sk), hI))))))
    case Cr.Cir.Out.halt{+s0, st2}:
      match st2:
        case Cr.Cir.State{+rg3, +cl3, +nx3, +fi3, +im3, +pg3, +lm3, +inp3, +ou3, +on3}:
          (+N2, p1) = p
          (+mm2, p2) = p1
          (eq, ok) = p2
          +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
          +mm = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
          +fr = {Wa.Wasm.Frame{Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : Wa.Wasm.Frame}
          +fr1 = {Wa.Wasm.Frame{[Cr.Cir.i.loop(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}))], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, 1n, [], L} : Wa.Wasm.Frame}
          +Yv = Cf(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
          +Cb = Cf([Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
          +END = {Wa.Wasm.Step.done{[s0], mm2} : Wa.Wasm.Step}
          +sk = skip2(N2, fr, mm, fr1, mm, Yv, END, eq, {==}, {==}, e => S.next.not_done(fr, mm, [s0], mm2, e),
            e => S.next.not_done(fr1, mm, [s0], mm2, e))
          (Nat.add(1n, Nat.sub(N2, 2n)), (mm2, (S.steps.then(1n, Nat.sub(N2, 2n), Cb, Yv, END, {==}, sk), ok)))
    case Cr.Cir.Out.out_of_memory{}:
      (+N2, p1) = p
      (+mm2, eq) = p1
      +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
      +mm = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +fr = {Wa.Wasm.Frame{Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : Wa.Wasm.Frame}
      +fr1 = {Wa.Wasm.Frame{[Cr.Cir.i.loop(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}))], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, 1n, [], L} : Wa.Wasm.Frame}
      +Yv = Cf(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +Cb = Cf([Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +END = {Wa.Wasm.Step.done{[1], mm2} : Wa.Wasm.Step}
      +sk = skip2(N2, fr, mm, fr1, mm, Yv, END, eq, {==}, {==}, e => S.next.not_done(fr, mm, [1], mm2, e),
        e => S.next.not_done(fr1, mm, [1], mm2, e))
      (Nat.add(1n, Nat.sub(N2, 2n)), (mm2, S.steps.then(1n, Nat.sub(N2, 2n), Cb, Yv, END, {==}, sk)))
    case Cr.Cir.Out.trap{}:
      Unit{}
    case Cr.Cir.Out.not_done{}:
      +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
      +mm = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +fr = {Wa.Wasm.Frame{Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : Wa.Wasm.Frame}
      +fr1 = {Wa.Wasm.Frame{[Cr.Cir.i.loop(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}))], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, 1n, [], L} : Wa.Wasm.Frame}
      +Yv = Cf(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +fb = {Wa.Wasm.Frame{[Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, 1n, [], L} : Wa.Wasm.Frame}
      S.next.skip(fu, fr, mm, fr1, mm, Yv, fb, mm, {==}, {==}, {==}, p)

# a generalized run of the loop from its start, seen from the branch back to it
def gpost.skip(o: Cr.Cir.Out, +fu: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat, p: GPost(o, fu, Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G)) ->
  GPost(o, Nat.sub(fu, 1n), [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match p:
    case Inl{q}:
      (+k, r) = q
      Inl{(k, post.skip.to(o, fu, c, body, d, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, S.Drop(k, gs), m, P, G, r))}
    case Inr{q}:
      (+N2, q1) = q
      (+mm2, q2) = q1
      (+k, q3) = q2
      (hg, eq) = q3
      +L = Q.Loc(a, n, 2, nx, on, t, nd, ad, rg)
      +mm = {Wa.Wasm.Memory{pg, lm, gs, m} : Wa.Wasm.Memory}
      +fr = {Wa.Wasm.Frame{Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, 1n, [], L} : Wa.Wasm.Frame}
      +fr1 = {Wa.Wasm.Frame{[Cr.Cir.i.loop(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}))], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, 1n, [], L} : Wa.Wasm.Frame}
      +Yv = Cf(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +Cb = Cf([Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +END = {Wa.Wasm.Step.done{[1], mm2} : Wa.Wasm.Step}
      +sk = skip2(N2, fr, mm, fr1, mm, Yv, END, eq, {==}, {==}, e => S.next.not_done(fr, mm, [1], mm2, e),
        e => S.next.not_done(fr1, mm, [1], mm2, e))
      Inr{(Nat.add(1n, Nat.sub(N2, 2n)), (mm2, (k, (hg, S.steps.then(1n, Nat.sub(N2, 2n), Cb, Yv, END, {==}, sk)))))}

# a post for a fuel is one for a smaller fuel
def spost.le(o: Cr.Cir.Out, +fu1: Nat, +fu2: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +gs2: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat, h: N.Le(fu2, fu1),
  p: SPost.to(o, fu1, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G)) -> SPost.to(o, fu2, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, gs2, m, P, G):
  match o:
    case Cr.Cir.Out.next{st2}:
      p
    case Cr.Cir.Out.halt{+s0, st2}:
      p
    case Cr.Cir.Out.out_of_memory{}:
      p
    case Cr.Cir.Out.trap{}:
      p
    case Cr.Cir.Out.not_done{}:
      S.next.mono(fu1, fu2, Cf(X, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m), h, p)

# a generalized post for a fuel is one for a smaller fuel
def gpost.le(o: Cr.Cir.Out, +fu1: Nat, +fu2: Nat, +X: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +K: List<&2, Wa.Wasm.Instr>, +ls1: List<&2, Wa.Wasm.Label>,
  +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +rg: List<&2, U32>, +nx: U32, +on: U32, +pg: U32, +lm: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +P: Nat, +G: Nat, h: N.Le(fu2, fu1),
  p: GPost(o, fu1, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G)) -> GPost(o, fu2, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match p:
    case Inl{q}:
      (+k, r) = q
      Inl{(k, spost.le(o, fu1, fu2, X, ls, K, ls1, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, S.Drop(k, gs), m, P, G, h, r))}
    case Inr{q}:
      Inr{q}

# the fuel of a loop's body, f - 1, is at most f
def sub1.le(+f: Nat) -> N.Le(Nat.sub(f, 1n), f):
  match f:
    case 0n:
      Unit{}
    case 1n+f1:
      match f1:
        case 0n:
          Unit{}
        case 1n+f2:
          N.le_succ(1n+f2, 1n+f2, N.le_refl(1n+f2))

# a round of a loop takes at least 4 steps, which pay for the unit of fuel that it takes
def loop.fuel(+f: Nat, +k: Nat) -> N.Le(1n+f, Nat.add(Nat.add(2n, Nat.add(k, 2n)), Nat.sub(f, 1n))):
  match f:
    case 0n:
      Unit{}
    case 1n+f1:
      match f1:
        case 0n:
          N.le_zero(Nat.add(Nat.add(k, 2n), 0n))
        case 1n+f2:
          N.le_add_l(Nat.add(k, 2n), 1n+f2)

def while.z(z: Bool, +f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +vc: U32, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ez: {U32.is_zero(vc) == z : Bool},
  +ex: {PH.H.steps(E.cost(c), Q.Cfg(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [], Q.Loc(a, n, 2, nx, on, t, nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})) ==
    Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}, Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}) : Wa.Wasm.Step},
  pb: GPost(Cr.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), f, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G),
  kont: @rg2: List<&2, U32> -> @cl2: Cr.Cir.Cells -> @nx2: U32 -> @fi2: U32 -> @im2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @inp2: List<&2, Word(8n)> -> @ou2: List<&2, Word(8n)> -> @on2: U32 -> @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @m2: Wa.Wasm.Bytes -> @gs1: List<&2, Bool> ->
    Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2) ->
    GPost(Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), Nat.sub(f, 1n), [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, K, ls,
      a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs1, m2, P, G)) ->
  GPost(Cr.Cir.exec.if.of(z, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, tt)),
    u => Cr.Cir.Out.next{Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)}), 1n+f, Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match z:
    case True{}:
      +C0 = Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +Ch = Cf(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C2 = Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}, Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})
      +C3 = Cf(K, ls, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m)
      Inl{(0n, (Nat.add(2n, Nat.add(E.cost(c), 2n)), (E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), (nd, (ad, (m, (S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, Ch, C3, {==},
        S.steps.then(E.cost(c), 2n, Ch, C2, C3, ex,
          brif.br1(vc, ez, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, K, ls, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}))), hI)))))))}
    case False{}:
      +C0 = Cf(Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +Ch = Cf(Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m)
      +C2 = Q.Cfg(Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}, Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [vc], Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m})
      +C3 = Cf(Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m)
      gpost.pre(Cr.Cir.exec.then(Cr.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, tt)), 1n+f, Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G,
        Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, m, Nat.add(2n, Nat.add(E.cost(c), 2n)),
        S.steps.then(2n, Nat.add(E.cost(c), 2n), C0, Ch, C3, {==}, S.steps.then(E.cost(c), 2n, Ch, C2, C3, ex,
          brif.go(vc, ez, 1, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, Q.Loc(a, n, 2, nx, on, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg), Wa.Wasm.Memory{pg, lm, gs, m}))),
        Nat.sub(f, 1n), loop.fuel(f, E.cost(c)),
        gpost.then(Cr.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, tt), Nat.sub(f, 1n), Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}},
          K, ls, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G, gpost.le(Cr.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), f, Nat.sub(f, 1n), Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G, sub1.le(f), pb), kont))

def while.of(mv: Maybe<&2, U32>, +f: Nat, +c: Cr.Cir.Expr, +body: Cr.Cir.Stmt, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +okc: {V.ok.expr(c, R) == True{} : Bool}, ev: {Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)) == mv : Maybe<&2, U32>},
  pb: GPost(Cr.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), f, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}]), Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, rg, nx, on, pg, lm, gs, m, P, G),
  kont: @rg2: List<&2, U32> -> @cl2: Cr.Cir.Cells -> @nx2: U32 -> @fi2: U32 -> @im2: U32 -> @pg2: U32 -> @lm2: U32 ->
    @inp2: List<&2, Word(8n)> -> @ou2: List<&2, Word(8n)> -> @on2: U32 -> @t2: U32 -> @nd2: U32 -> @ad2: U32 -> @m2: Wa.Wasm.Bytes -> @gs1: List<&2, Bool> ->
    Q.Inv(P, G, a, n, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, m2) ->
    GPost(Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), Nat.sub(f, 1n), [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, K, ls,
      a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs1, m2, P, G)) ->
  GPost(Cr.Cir.exec.if(mv, u => Cr.Cir.exec.then(Cr.Cir.exec(f, body, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, tt)),
    u => Cr.Cir.Out.next{Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)}), 1n+f, Cr.Cir.code.stmt(Cr.Cir.Stmt.while{c, body}, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match mv:
    case None{}:
      Inl{(0n, Unit{})}
    case Some{+vc}:
      while.z(U32.is_zero(vc), f, c, body, vc, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, {==},
        E.sim.expr(c, rg, cl, nx, fi, im, pg, lm, inp, ou, on, vc, ev, R, MX, okc, hR, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}}, Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, [], P, G, a, n, 2, t, nd, ad, gs, m, hI, W, hW, hP, hG),
        pb, kont)

# The simulation of statements
# ----------------------------

# when the run holds st at the code of s, d levels inside run's block (hL),
# the code does what Cir.exec says (SPost), when every register of s is
# below R (ok) and its branches out of run below MD (hd)
def sim.stmt(+fuel: Nat, s: Cr.Cir.Stmt, +rg: List<&2, U32>, +cl: Cr.Cir.Cells, +nx: U32, +fi: U32, +im: U32, +pg: U32, +lm: U32,
  +inp: List<&2, Word(8n)>, +ou: List<&2, Word(8n)>, +on: U32,
  +d: Nat, +K: List<&2, Wa.Wasm.Instr>, +ls: List<&2, Wa.Wasm.Label>, +hL: {List.drop(&2, Wa.Wasm.Label, ls, d) == [RL()] : List<&2, Wa.Wasm.Label>},
  +R: Nat, +MX: U32, +hR: N.Le(8n+R, U32.to_nat(MX)), +MD: U32,
  +P: Nat, +G: Nat, +a: U32, +n: U32, +t: U32, +nd: U32, +ad: U32, +gs: List<&2, Bool>, +m: Wa.Wasm.Bytes,
  +hI: Q.Inv(P, G, a, n, cl, nx, fi, im, pg, lm, inp, ou, on, m),
  +W: Nat, +hW: {W == PH.H.W(32n) : Nat}, +hP: {Nat.add(PH.H.W(4n), PH.H.t20(P)) == PH.H.W(32n) : Nat},
  +hG: {N.D(16n, G) == W : Nat},
  +ok: {V.ok.stmt(s, R) == True{} : Bool}, +hd: N.Le(Nat.add(d, dep(s)), U32.to_nat(MD))) ->
  GPost(Cr.Cir.exec(fuel, s, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, Cr.Cir.code.stmt(s, d, K), ls, K, ls, a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G):
  match fuel s:
    case _ Cr.Cir.Stmt.nop{}:
      Inl{(0n, (0n, (t, (nd, (ad, (m, ({==}, hI)))))))}
    case _ Cr.Cir.Stmt.set{+r, +e}:
      set.of(fuel, Cr.Cir.eval(e, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), r, e, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, ok, {==})
    case _ Cr.Cir.Stmt.store{+k, +c, +v}:
      sim.store(fuel, k, c, v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, ok)
    case _ Cr.Cir.Stmt.alloc{+r}:
      sim.alloc(fuel, r, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, ok, hd)
    case _ Cr.Cir.Stmt.emit{+v}:
      sim.emit(fuel, v, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, ok, hd)
    case _ Cr.Cir.Stmt.seq{+sa, +sb}:
      +Kb = Cr.Cir.code.stmt(sb, d, K)
      +oka = I.and.l(V.ok.stmt(sa, R), V.ok.stmt(sb, R), ok)
      +okb = I.and.r(V.ok.stmt(sa, R), V.ok.stmt(sb, R), ok)
      gpost.then(Cr.Cir.exec(fuel, sa, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), tt => Cr.Cir.exec(fuel, sb, tt), fuel, Cr.Cir.code.stmt(sa, d, Kb), ls, Kb, ls, K, ls,
        a, n, t, nd, ad, rg, nx, on, pg, lm, gs, m, P, G,
        sim.stmt(fuel, sa, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, Kb, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG,
          oka, dep.seq.l(d, dep(sa), dep(sb), MD, hd)),
        rg2 => cl2 => nx2 => fi2 => im2 => pg2 => lm2 => inp2 => ou2 => on2 => t2 => nd2 => ad2 => m2 => gs1 => hI2 =>
          sim.stmt(fuel, sb, rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t2, nd2, ad2, gs1, m2, hI2,
            W, hW, hP, hG, okb, dep.seq.r(d, dep(sa), dep(sb), MD, hd)))
    case _ Cr.Cir.Stmt.if{+c, +te, +ee}:
      +c01 = I.and.l(Bool.and(V.ok.expr(c, R), V.ok.stmt(te, R)), V.ok.stmt(ee, R), ok)
      +okc = I.and.l(V.ok.expr(c, R), V.ok.stmt(te, R), c01)
      +okt = I.and.r(V.ok.expr(c, R), V.ok.stmt(te, R), c01)
      +oke = I.and.r(Bool.and(V.ok.expr(c, R), V.ok.stmt(te, R)), V.ok.stmt(ee, R), ok)
      if.of(Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), fuel, c, te, ee, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, okc, {==},
        sim.stmt(fuel, te, rg, cl, nx, fi, im, pg, lm, inp, ou, on, 2n+d, [Wa.Wasm.Instr.br{1}], Con{Wa.Wasm.Label{0n, None{}, Cr.Cir.code.stmt(ee, 1n+d, []), 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, hL, R, MX, hR, MD, P, G,
          a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, gs, m, hI, W, hW, hP, hG, okt, dep.if.t(d, dep(te), dep(ee), MD, hd)),
        sim.stmt(fuel, ee, rg, cl, nx, fi, im, pg, lm, inp, ou, on, 1n+d, [], Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}, hL, R, MX, hR, MD, P, G,
          a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, gs, m, hI, W, hW, hP, hG, oke, dep.if.e(d, dep(te), dep(ee), MD, hd)))
    case 0n Cr.Cir.Stmt.while{_, _}:
      Inl{(0n, Unit{})}
    case 1n+f Cr.Cir.Stmt.while{+c, +body}:
      +okc = I.and.l(V.ok.expr(c, R), V.ok.stmt(body, R), ok)
      +okb = I.and.r(V.ok.expr(c, R), V.ok.stmt(body, R), ok)
      while.of(Cr.Cir.eval(c, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), f, c, body, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, okc, {==},
        sim.stmt(f, body, rg, cl, nx, fi, im, pg, lm, inp, ou, on, 2n+d, [Wa.Wasm.Instr.br{0}], Con{Wa.Wasm.Label{0n, Some{Cr.Cir.code.expr(c, Con{Wa.Wasm.Instr.eqz{}, Con{Wa.Wasm.Instr.br_if{1}, Cr.Cir.code.stmt(body, 2n+d, [Wa.Wasm.Instr.br{0}])}})}, [], 0n}, Con{Wa.Wasm.Label{0n, None{}, K, 0n}, ls}}, hL, R, MX, hR, MD, P, G,
          a, n, E.tmpE(c, t, Q.St(rg, cl, nx, fi, im, pg, lm, inp, ou, on)), nd, ad, gs, m, hI, W, hW, hP, hG, okb, dep.two(d, dep(body), MD, hd)),
        +rg2 => +cl2 => +nx2 => +fi2 => +im2 => +pg2 => +lm2 => +inp2 => +ou2 => +on2 => +t2 => +nd2 => +ad2 => +m2 => +gs1 => hI2 =>
          gpost.skip(Cr.Cir.exec(f, Cr.Cir.Stmt.while{c, body}, Cr.Cir.State{rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2}), f, c, body, d, K, ls,
            a, n, t2, nd2, ad2, rg2, nx2, on2, pg2, lm2, gs1, m2, P, G,
            sim.stmt(f, Cr.Cir.Stmt.while{c, body}, rg2, cl2, nx2, fi2, im2, pg2, lm2, inp2, ou2, on2, d, K, ls, hL, R, MX, hR, MD, P, G,
              a, n, t2, nd2, ad2, gs1, m2, hI2, W, hW, hP, hG, ok, hd)))
    case _ Cr.Cir.Stmt.halt{+s0}:
      sim.halt(fuel, s0, rg, cl, nx, fi, im, pg, lm, inp, ou, on, d, K, ls, hL, R, MX, hR, MD, P, G, a, n, t, nd, ad, gs, m, hI, W, hW, hP, hG, hd)
