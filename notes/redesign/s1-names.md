# S1 names: shared kit (B0), logic (B1), header (B2)

**Changes at f28882f (w/s1 = feature/redesign 9dd2ced + this commit):**
- `Lg.wp.alloc`, `Lg.wp.emit`: the page binder is reusable, `for q: @+p: U32 -> K(H, ..)` (was `@p`);
  same meaning (gen2 --wp's stepped proofs need it).
- kit `K.u32.is_zero_t(+x: U32, +h: {U32.is_zero(x) == True{} : Bool}) -> {x == 0 : U32}` (proven),
  with `K.word.zero(n)`, `K.word.cmp_zero`, `K.cmp.fin_ff`, `K.cmp.fin_tf`.

**Additions at 8b21a13 (w/s1 merged with feature/redesign 015dba0; all proven, kernel 0 fail):**
- `K.bool.case(+b, -G, t: @+h: {b == True{} : Bool} -> G, f: @+h: {b == False{} : Bool} -> G) -> G`:
  a split on a Bool (the --wp stepper's if split; text as gen2-wp-notes.md proposed).
- `Lg.St.reg(st, r) -> U32`: the value of register r (`Maybe.default(Reg(st, r), 0)`; 0 for none).
- law `Lg.reg.some` (+st, +q, +hq: `{Nat.is_lt(q, St.nregs(st)) == True{}}`) ⊢
  `{Lg.Reg(st, q) == Some{Lg.St.reg(st, q)}}`: every register below the count can be read.
- law `Lg.reg.lt` (+st, +q, +c, +hq: `{Lg.Reg(st, q) == Some{c}}`) ⊢ `{Nat.is_lt(q, St.nregs(st)) == True{}}`.
- kit `K.maybe.T`, `K.list.get_lt`, `K.list.lt_get` (List.get below the length is Some; Some means below).

**Changes since the first publication (949139d), as of 4f3ddcc** (no def or law was renamed):
- **Import `logic/impl.bend` (and `header/impl.bend`) in any book whose proofs use S1's laws**:
  bend2 rejects a use of a law that has no fill in the book ("an unfilled law is a dead claim").
- Predicate parameters of the laws are erased (`for -Q`, `-H`, `-K`, `-I`; a5ff23e), so a caller
  may name H twice (`x => K(H, x)` and `H`). `Lg.Tot(s, st, b, -Q, -H)` too.
- Every Data parameter of a law is reusable (`for +s: Cr.Cir.Stmt`, ...).
- Proven: the kit; logic's tot.seq/if/wk, tot.of_wp, wp.of_tot, wp.wk, exec.more/set/store,
  wp.set/store and the accessor rewrites (see s1-handoff.md for the open ones).
- `Lg.Lim(st)` is now `N.D(16n, U32.to_nat(Wa.Wasm.min(St.limit(st), 65536)))` (N = Compiler/need_big.bend):
  the same number as `Program.memory`, but `Nat.mul(65536n, x)` on a symbolic x overflows the
  checker's stack. `N.mul_D(16n, b)` relates the two (65536n is `N.D(16n, 1n)` by computation).
- Every equation hypothesis of a law is now reusable (`for +h: {...}`): proofs are affine too.
- Kit lemmas added: `K.bool.tf`, `K.bool.tf2`, `K.bool.or_f`, `K.has.ne`. The kit is proven.

Lane S1 of P2, branch `w/s1` (worktree `bb-wt/s1`). First published 2026-11-04 from commit `949139d`.
All statements below typecheck with bend2 (`--check-only`: only TODO counts). Bodies of laws are
`?TODO` in `logic/impl.bend` and `header/impl.bend` until proven. I avoid renames from here on; any
change is listed at the top of this file.

## How to import

```
import ../shared.bend as K            # from Machine/<layer>/x.bend
import ../logic/spec.bend as Lg
import ../header/spec.bend as Hs      # NOTE: header defs are named Hd.* and Tbl.*, so: Hs.Hd.tag, Hs.Tbl.mask
```

(Bend needs an alias on every import, so a def named `Hd.tag` is `Hs.Hd.tag` to a caller, as S3's
`C.Canon.term` and `A.AM.move`. Logic's defs carry no layer prefix: `Lg.Tot`, `Lg.WP`, `Lg.Reg`,
`Lg.St.set`, `Lg.Cir.writes`. The kit's: `K.Has`, `K.Mem`, `K.Disj`, `K.Sub`.)

## Differences from the plan's text (§4.1, §4.2) that S2 must know

1. **No `K.P2`.** Facts join with Bend's product `A & B` (works for Types and equations), a
   witness with `&x:T -> P`. (`P2` is already defined twice in layer A; a third would break G5.)
2. **`Lg.Tot(s, st, b, Q, H)`** as the plan (Q, H are erased parameters: use them freely).
3. **`Lg.WP(s, b, K, H, st)`**: the computed WP. Its post `K` takes the halt post first:
   `K: (U32 -> State -> Type) -> State -> Type`, used as `K(H, st2)` (Bend's affinity needs it).
   For a post `Q` that ignores halts write `h => x => Q(x)`. `Lg.tot.of_wp` (WP gives
   `Tot(s, st, b, x => K(H, x), H)`) and `Lg.wp.of_tot` (the converse) bridge: a goal
   `Tot(code, ...)` becomes `WP(code, ...)` (closed code unfolds by evaluation); a routine call
   inside it (a `WP(Mc.M.dec(r), b, K2, H, st2)` subgoal) closes with `wp.of_tot` + the routine's
   Tot law + `tot.wk`. A while is `Tot` inside WP; `tot.while` opens it.
4. **`Lg.Loop`** (the while rule's round) uses WP for the body (not Tot), and `&` not P2.
5. **`Lg.No(s, st)`**: no erased parameters (so it has type `U32 -> State -> Type`).
6. **`Lg.Lim(st)` = 2^16 × min(limit, 65536)** (written `N.D(16n, ..)`, see the top): the number
   of `mach.memory`'s `Program.memory(m)` at the start, and at most 2^32, so an alloc past
   cell 214748364 is out of memory below the budget too. No premise on the limit is needed.
7. **Register count**: premises are `Nat.is_lt(r, Lg.St.nregs(st)) == True` (not `Mc.Mach.regs()`):
   logic does not import the machine. `Base`/`Inv` should state `St.nregs(st) == Mc.Mach.regs()`.
8. **Primitive steps as apply rules**: `wp.set`, `wp.store`, `wp.alloc`, `wp.emit` (the WP of the
   primitive from its next state's post) and the rewrites `exec.set`, `exec.store`, `exec.alloc`.
   `wp.alloc` asks `St.outn(st) == 0` (Cir traps an alloc once output began) and a budget
   `20 (next + 1) <= b`; its post holds for every page count p. `wp.emit`'s budget:
   `20 next + outn + 1 <= b`.
9. **Frame**: `Lg.tot.frame` adds `St.kept(st, x, Cir.writes(s))` (registers outside the writes
   equal, the same count, next not smaller) and `St.fixed(x) == St.fixed(st)` (limit, input,
   first, image) to a Tot's post; `tot.frame_out` (no emit: `Cir.emits(s) == False`) adds out and
   outn equal. `frame.regs` / `frame.fixed` are the plan's exec-level forms. S2's `Same` can be
   `Lg.St.kept(st, st2, ws) && ...` with `Lg.St.fixed` as an equation. "Writes only these
   registers": `{K.Sub(Lg.Cir.writes(<code>), <list>) == True{} : Bool}`, closed by `{==}`
   (a symbolic target register r needs `K.nat.is_eq_refl`).
10. **Accessors** (Bend makes none): `Lg.St.regs/nregs/cells/next/first/image/pages/limit/input/
    out/outn`, `Lg.St.fd(st, k, c)` (field k of cell c), `Lg.St.is_cell(st, c)` (Cir.is_cell),
    updaters `Lg.St.set/store/alloc/emit`. Accessor-after-updater rewrites: `reg.*`, `nregs.*`,
    `cells.*`, `next.*`, `outn.*`, `fixed.*`, `lim.*` (`<accessor>.<updater>`), and
    `cells.get_set`, `cell.get_set`. A proof may instead `match st` at its start: then all of
    them compute.
11. **Table**: `Hd.Tbl.mask(t)` covers every tag (terms from the image's table; frames 32 to 40 and
    `K.arg` 41: field 2, Rwt's frame 38: fields 2 and 3; FREE and others: 0). `Hd.Tbl.bind(t, k)`
    and `Hd.Tbl.former(t)` read the image's table for term tags (0 for others). `Hd.Tbl.cell(t)` is
    the image's table cell itself (`Mc.Img.table`), so ImgOK's table clause can be
    `Cells.get(m, 272 + t) == Hd.Tbl.cell(t)` for t < 19.
12. **Header**: `Hd.tag/q/has/fv/todo/fits/flag_bit`; laws `hd.tag_of/q_of/fv_of/has_of/todo_of`
    on `Mc.Img.header`; mask algebra `mask.and_or/and_and/and_shl/shr_or/shr_and/shr_shl/
    or_zero/zero_or/and_zero/zero_and/and_low/shr_low/sub_bit` (sub_bit: the copy's todo clear).
    The machine's `M.header(k, q, fl)` is `Img.header(k, q, fl, 0)` up to `mask.or_zero`.

## Naming convention (rewrite set)

`exec.*` (a primitive's run), `wp.*` (WP rules), `tot.*` (Tot rules), `reg.* nregs.* cells.*
cell.* next.* outn.* fixed.* lim.*` (accessor after updater), `frame.*`, `hd.*`, `mask.*`; kit:
`bool.* nat.* disj.* sub.* list.*`. Every equation's left side is the term to rewrite.

## Exact headers

### s1/src/Compiler/Machine/shared.bend

```
def Has(xs: List<&2, Nat>, +r: Nat) -> Bool
def Mem(xs: List<&2, U32>, +c: U32) -> Bool
def Disj(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool
def Sub(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool
def bool.T(b: Bool) -> Type
def bool.ff(-G: Type, +e: {False{} == True{} : Bool}) -> G
def bool.tf(-G: Type, +e: {True{} == False{} : Bool}) -> G
def bool.tf2(-G: Type, -b: Bool, +ht: {b == True{} : Bool}, +hf: {b == False{} : Bool}) -> G
def bool.or_f(a: Bool, -b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}
def bool.and_l(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}
def bool.and_r(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}
def bool.and_i(a: Bool, -b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}
def bool.or_l(a: Bool, -b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}
def bool.or_r(a: Bool, -b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}
def bool.not_t(a: Bool, +h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}
def bool.not_f(a: Bool, +h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}
def bool.case(+b: Bool, -G: Type, t: @+h: {b == True{} : Bool} -> G, f: @+h: {b == False{} : Bool} -> G) -> G
def nat.is_eq_ok(+a: Nat, +b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}
def nat.is_eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}
def nat.is_eq_sym(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}
def has.ne(e: Bool, +x: Nat, +ys: List<&2, Nat>, +r: Nat, +he: {Nat.is_eq(x, r) == e : Bool},
  +hx: {Has(ys, x) == False{} : Bool}, +h: {Has(ys, r) == True{} : Bool}) -> {e == False{} : Bool}
def disj.has(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +r: Nat, +d: {Disj(xs, ys) == True{} : Bool},
  +h: {Has(ys, r) == True{} : Bool}) -> {Has(xs, r) == False{} : Bool}
def sub.has(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +r: Nat, +s: {Sub(xs, ys) == True{} : Bool},
  +h: {Has(ys, r) == False{} : Bool}) -> {Has(xs, r) == False{} : Bool}
def sub.con(+xs: List<&2, Nat>, +y: Nat, +ys: List<&2, Nat>, +s: {Sub(xs, ys) == True{} : Bool}) ->
  {Sub(xs, Con{y, ys}) == True{} : Bool}
def list.length_set(-A: Data, xs: List<&2, A>, n: Nat, x: A) ->
  {List.length(&2, A, List.set(&2, A, xs, n, x)) == List.length(&2, A, xs) : Nat}
def list.get_set(-A: Data, +xs: List<&2, A>, +n: Nat, +x: A, +j: Nat,
  +h: {Nat.is_lt(n, List.length(&2, A, xs)) == True{} : Bool}) ->
  {List.get(&2, A, List.set(&2, A, xs, n, x), j) == Bool.pick(Maybe<&2, A>, Nat.is_eq(n, j), Some{x}, List.get(&2, A, xs, j)) : Maybe<&2, A>}
def maybe.T(-A: Data, m: Maybe<&2, A>) -> Type
def list.get_lt(-A: Data, +xs: List<&2, A>, +n: Nat, +d: A, +h: {Nat.is_lt(n, List.length(&2, A, xs)) == True{} : Bool}) ->
  {List.get(&2, A, xs, n) == Some{Maybe.default(&2, A, List.get(&2, A, xs, n), d)} : Maybe<&2, A>}
def list.lt_get(-A: Data, +xs: List<&2, A>, +n: Nat, +c: A, +e: {List.get(&2, A, xs, n) == Some{c} : Maybe<&2, A>}) ->
  {Nat.is_lt(n, List.length(&2, A, xs)) == True{} : Bool}
def word.zero(n: Nat) -> Word(n)
def cmp.fin_ff(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_eq(c) : Bool}
def cmp.fin_tf(c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) == False{} : Bool}
def word.cmp_zero(+n: Nat, +w: Word(n), +h: {Cmp.is_eq(Word.cmp(n, w, word.zero(n))) == True{} : Bool}) ->
  {w == word.zero(n) : Word(n)}
def u32.is_zero_t(+x: U32, +h: {U32.is_zero(x) == True{} : Bool}) -> {x == 0 : U32}
```

### s1/src/Compiler/Machine/logic/spec.bend

```
def Reg(st: Cr.Cir.State, +r: Nat) -> Maybe<&2, U32>
def St.reg(st: Cr.Cir.State, +r: Nat) -> U32
def St.regs(st: Cr.Cir.State) -> List<&2, U32>
def St.nregs(st: Cr.Cir.State) -> Nat
def St.cells(st: Cr.Cir.State) -> Cr.Cir.Cells
def St.next(st: Cr.Cir.State) -> U32
def St.first(st: Cr.Cir.State) -> U32
def St.image(st: Cr.Cir.State) -> U32
def St.pages(st: Cr.Cir.State) -> U32
def St.limit(st: Cr.Cir.State) -> U32
def St.input(st: Cr.Cir.State) -> List<&2, Word(8n)>
def St.out(st: Cr.Cir.State) -> List<&2, Word(8n)>
def St.outn(st: Cr.Cir.State) -> U32
def St.fd(st: Cr.Cir.State, +k: Nat, +c: U32) -> U32
def St.is_cell(+st: Cr.Cir.State, +c: U32) -> Bool
def Lim(st: Cr.Cir.State) -> Nat
type St.Fixed is Data:
  St.Fixed{limit: U32, input: List<&2, Word(8n)>, first: U32, image: U32}
def St.fixed(st: Cr.Cir.State) -> St.Fixed
def St.set(st: Cr.Cir.State, +r: Nat, v: U32) -> Cr.Cir.State
def St.store(st: Cr.Cir.State, +k: Nat, +c: U32, v: U32) -> Cr.Cir.State
def St.alloc(st: Cr.Cir.State, +r: Nat, p: U32) -> Cr.Cir.State
def St.emit(st: Cr.Cir.State, v: U32, p: U32) -> Cr.Cir.State
def Out.done(o: Cr.Cir.Out) -> Bool
def Ok(o: Cr.Cir.Out, +lim: Nat, +b: Nat, Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type
def Tot(s: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, -Q: Cr.Cir.State -> Type, -H: U32 -> Cr.Cir.State -> Type) -> Type
def No(s: U32, st: Cr.Cir.State) -> Type
def WP.ok(o: Cr.Cir.Out, +lim: Nat, +b: Nat, K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type,
  H: U32 -> Cr.Cir.State -> Type) -> Type
def WP.pick(z: Bool,
  yes: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  no: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type
def WP.if(v: Maybe<&2, U32>,
  yes: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  no: ((U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type) -> (U32 -> Cr.Cir.State -> Type) -> Type,
  K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type
def WP(s: Cr.Cir.Stmt, +b: Nat, K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type,
  H: U32 -> Cr.Cir.State -> Type, +st: Cr.Cir.State) -> Type
def Loop.pick(z: Bool, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type
def Loop.of(v: Maybe<&2, U32>, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type
def Loop(c: Cr.Cir.Expr, body: Cr.Cir.Stmt, +st: Cr.Cir.State, +b: Nat, +n: Nat, I: Nat -> Cr.Cir.State -> Type,
  Q: Cr.Cir.State -> Type, H: U32 -> Cr.Cir.State -> Type) -> Type
def Cir.writes(s: Cr.Cir.Stmt) -> List<&2, Nat>
def Cir.emits(s: Cr.Cir.Stmt) -> Bool
def Regs.kept(rs: List<&2, U32>, +rs2: List<&2, U32>, +ws: List<&2, Nat>, +i: Nat) -> Bool
def St.kept(+st: Cr.Cir.State, +st2: Cr.Cir.State, +ws: List<&2, Nat>) -> Bool
law exec.more:
  for +f: Nat
  for +g: Nat
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +d: {Out.done(Cr.Cir.exec(f, s, st)) == True{} : Bool}
  {Cr.Cir.exec(Nat.add(f, g), s, st) == Cr.Cir.exec(f, s, st) : Cr.Cir.Out}
law tot.any:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(s, st, b, Q, H)
  for +g: Nat
  Or({Cr.Cir.exec(g, s, st) == Cr.Cir.Out.not_done{} : Cr.Cir.Out}, Ok(Cr.Cir.exec(g, s, st), Lim(st), b, Q, H))
law tot.seq:
  for +a: Cr.Cir.Stmt
  for +c: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(a, st, b, x => Tot(c, x, b, Q, H), H)
  Tot(Cr.Cir.Stmt.seq{a, c}, st, b, Q, H)
law tot.if:
  for +c: Cr.Cir.Expr
  for +y: Cr.Cir.Stmt
  for +n: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +v: U32
  for +e: {Cr.Cir.eval(c, st) == Some{v} : Maybe<&2, U32>}
  for t: Tot(Bool.pick(Cr.Cir.Stmt, U32.is_zero(v), n, y), st, b, Q, H)
  Tot(Cr.Cir.Stmt.if{c, y, n}, st, b, Q, H)
law tot.while:
  for +c: Cr.Cir.Expr
  for +body: Cr.Cir.Stmt
  for +b: Nat
  for -I: Nat -> Cr.Cir.State -> Type
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for r: @n: Nat -> @st: Cr.Cir.State -> I(n, st) -> Loop(c, body, st, b, n, I, Q, H)
  for +n: Nat
  for +st: Cr.Cir.State
  for i: I(n, st)
  Tot(Cr.Cir.Stmt.while{c, body}, st, b, Q, H)
law tot.wk:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for +b2: Nat
  for -Q: Cr.Cir.State -> Type
  for -Q2: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for -H2: U32 -> Cr.Cir.State -> Type
  for +hb: {Nat.is_le(b, b2) == True{} : Bool}
  for hq: @x: Cr.Cir.State -> Q(x) -> Q2(x)
  for hh: @k: U32 -> @x: Cr.Cir.State -> H(k, x) -> H2(k, x)
  for t: Tot(s, st, b, Q, H)
  Tot(s, st, b2, Q2, H2)
law tot.of_wp:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for w: WP(s, b, K, H, st)
  Tot(s, st, b, x => K(H, x), H)
law wp.of_tot:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(s, st, b, x => K(H, x), H)
  WP(s, b, K, H, st)
law wp.wk:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for +b2: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -K2: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for -H2: U32 -> Cr.Cir.State -> Type
  for +hb: {Nat.is_le(b, b2) == True{} : Bool}
  for hk: @x: Cr.Cir.State -> K(H, x) -> K2(H2, x)
  for hh: @k: U32 -> @x: Cr.Cir.State -> H(k, x) -> H2(k, x)
  for w: WP(s, b, K, H, st)
  WP(s, b2, K2, H2, st)
law exec.set:
  for +f: Nat
  for +r: Nat
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +v: U32
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  {Cr.Cir.exec(f, Cr.Cir.Stmt.set{r, e}, st) == Cr.Cir.Out.next{St.set(st, r, v)} : Cr.Cir.Out}
law exec.store:
  for +f: Nat
  for +k: Nat
  for +c: Cr.Cir.Expr
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +i: U32
  for +v: U32
  for +hc: {Cr.Cir.eval(c, st) == Some{i} : Maybe<&2, U32>}
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hi: {St.is_cell(st, i) == True{} : Bool}
  {Cr.Cir.exec(f, Cr.Cir.Stmt.store{k, c, e}, st) == Cr.Cir.Out.next{St.store(st, k, i, v)} : Cr.Cir.Out}
law exec.alloc:
  for +f: Nat
  for +r: Nat
  for +st: Cr.Cir.State
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  for +ho: {St.outn(st) == 0 : U32}
  Or(&p:U32 -> {Cr.Cir.exec(f, Cr.Cir.Stmt.alloc{r}, st) == Cr.Cir.Out.next{St.alloc(st, r, p)} : Cr.Cir.Out},
    {Cr.Cir.exec(f, Cr.Cir.Stmt.alloc{r}, st) == Cr.Cir.Out.out_of_memory{} : Cr.Cir.Out} &
    {Nat.is_lt(Lim(st), Nat.mul(20n, Nat.add(U32.to_nat(St.next(st)), 1n))) == True{} : Bool})
law wp.set:
  for +r: Nat
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +v: U32
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  for q: K(H, St.set(st, r, v))
  WP(Cr.Cir.Stmt.set{r, e}, b, K, H, st)
law wp.store:
  for +k: Nat
  for +c: Cr.Cir.Expr
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +i: U32
  for +v: U32
  for +hc: {Cr.Cir.eval(c, st) == Some{i} : Maybe<&2, U32>}
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hi: {St.is_cell(st, i) == True{} : Bool}
  for q: K(H, St.store(st, k, i, v))
  WP(Cr.Cir.Stmt.store{k, c, e}, b, K, H, st)
law wp.alloc:
  for +r: Nat
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  for +ho: {St.outn(st) == 0 : U32}
  for +hb: {Nat.is_le(Nat.mul(20n, Nat.add(U32.to_nat(St.next(st)), 1n)), b) == True{} : Bool}
  for q: @+p: U32 -> K(H, St.alloc(st, r, p))
  WP(Cr.Cir.Stmt.alloc{r}, b, K, H, st)
law wp.emit:
  for +e: Cr.Cir.Expr
  for +st: Cr.Cir.State
  for +b: Nat
  for -K: (U32 -> Cr.Cir.State -> Type) -> Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +v: U32
  for +he: {Cr.Cir.eval(e, st) == Some{v} : Maybe<&2, U32>}
  for +hb: {Nat.is_le(Nat.add(Nat.mul(20n, U32.to_nat(St.next(st))), Nat.add(U32.to_nat(St.outn(st)), 1n)), b) == True{} : Bool}
  for q: @+p: U32 -> K(H, St.emit(st, v, p))
  WP(Cr.Cir.Stmt.emit{e}, b, K, H, st)
law reg.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  for +q: Nat
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  {Reg(St.set(st, r, v), q) == Bool.pick(Maybe<&2, U32>, Nat.is_eq(r, q), Some{v}, Reg(st, q)) : Maybe<&2, U32>}
law reg.some:
  for +st: Cr.Cir.State
  for +q: Nat
  for +hq: {Nat.is_lt(q, St.nregs(st)) == True{} : Bool}
  {Reg(st, q) == Some{St.reg(st, q)} : Maybe<&2, U32>}
law reg.lt:
  for +st: Cr.Cir.State
  for +q: Nat
  for +c: U32
  for +hq: {Reg(st, q) == Some{c} : Maybe<&2, U32>}
  {Nat.is_lt(q, St.nregs(st)) == True{} : Bool}
law reg.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  for +q: Nat
  {Reg(St.store(st, k, c, v), q) == Reg(st, q) : Maybe<&2, U32>}
law reg.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  for +q: Nat
  for +hr: {Nat.is_lt(r, St.nregs(st)) == True{} : Bool}
  {Reg(St.alloc(st, r, p), q) == Bool.pick(Maybe<&2, U32>, Nat.is_eq(r, q), Some{St.next(st)}, Reg(st, q)) : Maybe<&2, U32>}
law reg.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  for +q: Nat
  {Reg(St.emit(st, v, p), q) == Reg(st, q) : Maybe<&2, U32>}
law nregs.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.nregs(St.set(st, r, v)) == St.nregs(st) : Nat}
law nregs.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.nregs(St.store(st, k, c, v)) == St.nregs(st) : Nat}
law nregs.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.nregs(St.alloc(st, r, p)) == St.nregs(st) : Nat}
law nregs.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.nregs(St.emit(st, v, p)) == St.nregs(st) : Nat}
law cells.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.cells(St.set(st, r, v)) == St.cells(st) : Cr.Cir.Cells}
law cells.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.cells(St.store(st, k, c, v)) ==
    Cr.Cir.Cells.set(St.cells(st), c, Cr.Cir.Cell.set(k, Cr.Cir.Cells.get(St.cells(st), c), v)) : Cr.Cir.Cells}
law cells.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.cells(St.alloc(st, r, p)) == Cr.Cir.Cells.set(St.cells(st), St.next(st), Cr.Cir.Cell.zero()) : Cr.Cir.Cells}
law cells.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.cells(St.emit(st, v, p)) == St.cells(st) : Cr.Cir.Cells}
law cells.get_set:
  for +m: Cr.Cir.Cells
  for +i: U32
  for +x: Cr.Cir.Cell
  for +j: U32
  {Cr.Cir.Cells.get(Cr.Cir.Cells.set(m, i, x), j) == Bool.pick(Cr.Cir.Cell, U32.is_eq(i, j), x, Cr.Cir.Cells.get(m, j)) : Cr.Cir.Cell}
law cell.get_set:
  for +k: Nat
  for +x: Cr.Cir.Cell
  for +v: U32
  for +j: Nat
  for +hk: {Nat.is_le(k, 4n) == True{} : Bool}
  for +hj: {Nat.is_le(j, 4n) == True{} : Bool}
  {Cr.Cir.Cell.get(j, Cr.Cir.Cell.set(k, x, v)) == Bool.pick(U32, Nat.is_eq(k, j), v, Cr.Cir.Cell.get(j, x)) : U32}
law next.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.next(St.set(st, r, v)) == St.next(st) : U32}
law next.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.next(St.store(st, k, c, v)) == St.next(st) : U32}
law next.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.next(St.alloc(st, r, p)) == U32.inc(St.next(st)) : U32}
law next.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.next(St.emit(st, v, p)) == St.next(st) : U32}
law outn.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.outn(St.set(st, r, v)) == St.outn(st) : U32}
law outn.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.outn(St.store(st, k, c, v)) == St.outn(st) : U32}
law outn.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.outn(St.alloc(st, r, p)) == St.outn(st) : U32}
law outn.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.outn(St.emit(st, v, p)) == U32.inc(St.outn(st)) : U32}
law fixed.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {St.fixed(St.set(st, r, v)) == St.fixed(st) : St.Fixed}
law fixed.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {St.fixed(St.store(st, k, c, v)) == St.fixed(st) : St.Fixed}
law fixed.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {St.fixed(St.alloc(st, r, p)) == St.fixed(st) : St.Fixed}
law fixed.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {St.fixed(St.emit(st, v, p)) == St.fixed(st) : St.Fixed}
law lim.set:
  for +st: Cr.Cir.State
  for +r: Nat
  for +v: U32
  {Lim(St.set(st, r, v)) == Lim(st) : Nat}
law lim.store:
  for +st: Cr.Cir.State
  for +k: Nat
  for +c: U32
  for +v: U32
  {Lim(St.store(st, k, c, v)) == Lim(st) : Nat}
law lim.alloc:
  for +st: Cr.Cir.State
  for +r: Nat
  for +p: U32
  {Lim(St.alloc(st, r, p)) == Lim(st) : Nat}
law lim.emit:
  for +st: Cr.Cir.State
  for +v: U32
  for +p: U32
  {Lim(St.emit(st, v, p)) == Lim(st) : Nat}
law frame.regs:
  for +f: Nat
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +st2: Cr.Cir.State
  for +r: Nat
  for +e: {Cr.Cir.exec(f, s, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}
  for +w: {K.Has(Cir.writes(s), r) == False{} : Bool}
  {Reg(st2, r) == Reg(st, r) : Maybe<&2, U32>}
law frame.fixed:
  for +f: Nat
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +st2: Cr.Cir.State
  for +e: {Cr.Cir.exec(f, s, st) == Cr.Cir.Out.next{st2} : Cr.Cir.Out}
  {St.fixed(st2) == St.fixed(st) : St.Fixed}
law tot.frame:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for t: Tot(s, st, b, Q, H)
  Tot(s, st, b, x => Q(x) & ({St.kept(st, x, Cir.writes(s)) == True{} : Bool} & {St.fixed(x) == St.fixed(st) : St.Fixed}), H)
law tot.frame_out:
  for +s: Cr.Cir.Stmt
  for +st: Cr.Cir.State
  for +b: Nat
  for -Q: Cr.Cir.State -> Type
  for -H: U32 -> Cr.Cir.State -> Type
  for +ne: {Cir.emits(s) == False{} : Bool}
  for t: Tot(s, st, b, Q, H)
  Tot(s, st, b, x => Q(x) & ({St.out(x) == St.out(st) : List<&2, Word(8n)>} & {St.outn(x) == St.outn(st) : U32}), H)
```

### s1/src/Compiler/Machine/header/spec.bend

```
def Hd.tag(h: U32) -> U32
def Hd.q(h: U32) -> U32
def Hd.has(h: U32, +bit: U32) -> Bool
def Hd.fv(h: U32) -> U32
def Hd.todo(h: U32) -> U32
def Hd.flag_bit(+bit: U32) -> Bool
def Hd.fits(+t: U32, +q: U32, +fl: U32, +fv: U32) -> Bool
def Tbl.cell(+t: U32) -> Cr.Cir.Cell
def Tbl.mask(+t: U32) -> U32
def Tbl.bind(+t: U32, +k: Nat) -> Nat
def Tbl.former(+t: U32) -> Bool
law hd.tag_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for +h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.tag(Mc.Img.header(t, q, fl, fv)) == t : U32}
law hd.q_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for +h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.q(Mc.Img.header(t, q, fl, fv)) == q : U32}
law hd.fv_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for +h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.fv(Mc.Img.header(t, q, fl, fv)) == fv : U32}
law hd.has_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for +bit: U32
  for +h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  for +hb: {Hd.flag_bit(bit) == True{} : Bool}
  {Hd.has(Mc.Img.header(t, q, fl, fv), bit) == Hd.has(fl, bit) : Bool}
law hd.todo_of:
  for +t: U32
  for +q: U32
  for +fl: U32
  for +fv: U32
  for +h: {Hd.fits(t, q, fl, fv) == True{} : Bool}
  {Hd.todo(Mc.Img.header(t, q, fl, fv)) == U32.shln(U32.and(fv, 7), 13n) : U32}
law mask.and_or:
  for +a: U32
  for +b: U32
  for +m: U32
  {U32.and(U32.or(a, b), m) == U32.or(U32.and(a, m), U32.and(b, m)) : U32}
law mask.and_and:
  for +a: U32
  for +b: U32
  for +c: U32
  {U32.and(U32.and(a, b), c) == U32.and(a, U32.and(b, c)) : U32}
law mask.and_shl:
  for +a: U32
  for +n: Nat
  for +m: U32
  {U32.and(U32.shln(a, n), m) == U32.shln(U32.and(a, U32.shrn(m, n)), n) : U32}
law mask.shr_or:
  for +a: U32
  for +b: U32
  for +n: Nat
  {U32.shrn(U32.or(a, b), n) == U32.or(U32.shrn(a, n), U32.shrn(b, n)) : U32}
law mask.shr_and:
  for +a: U32
  for +m: U32
  for +n: Nat
  {U32.shrn(U32.and(a, m), n) == U32.and(U32.shrn(a, n), U32.shrn(m, n)) : U32}
law mask.shr_shl:
  for +a: U32
  for +n: Nat
  {U32.shrn(U32.shln(a, n), n) == U32.and(a, U32.shrn(4294967295, n)) : U32}
law mask.or_zero:
  for +a: U32
  {U32.or(a, 0) == a : U32}
law mask.zero_or:
  for +a: U32
  {U32.or(0, a) == a : U32}
law mask.and_zero:
  for +a: U32
  {U32.and(a, 0) == 0 : U32}
law mask.zero_and:
  for +a: U32
  {U32.and(0, a) == 0 : U32}
law mask.and_low:
  for +a: U32
  for +k: Nat
  for +h: {U32.is_lt(a, U32.shln(1, k)) == True{} : Bool}
  {U32.and(a, U32.sub(U32.shln(1, k), 1)) == a : U32}
law mask.shr_low:
  for +a: U32
  for +k: Nat
  for +h: {U32.is_lt(a, U32.shln(1, k)) == True{} : Bool}
  {U32.shrn(a, k) == 0 : U32}
law mask.sub_bit:
  for +h: U32
  for +b: U32
  for +e: {U32.and(h, b) == b : U32}
  {U32.sub(h, b) == U32.and(h, U32.not(b)) : U32}
```

