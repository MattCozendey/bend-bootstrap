import Interpreter.Run
import Shared.DataForm
import Shared.Script
import Std.Data.HashSet

-- WasmTests
-- =========
--
-- A test of kind b (bend2 skill): the Bend version of WASM (the section Wasm of
-- src/Wasm/impl.bend) against the official WebAssembly
-- tests of src/Wasm/tests (AGENTS.md 3.9.1.3), run by the Lean interpreter that the
-- plan trusts (src/Interpreter/Run.lean), not by the TypeScript compiler.
--
--   bend src/Wasm/impl.bend -o <file.bendtt>
--   BOOK=<file.bendtt> TESTS=src/Wasm/tests/bin ONLY=<test>,... \
--     OUT=<file.log> lake lean src/Wasm/scripts/WasmTests.lean
--
-- It runs each command of a binary script (spec interpreter README: Binary
-- Scripts) as the spec's harness does, and counts each assertion as passed,
-- failed, unsupported (the module or the values leave the subset, or an
-- earlier action left the instance in a state that the script does not
-- expect: St.after) or not done (the model's fuel ran out). It reads x.facts
-- next to each x.bin.wast (cut.ml), which says why a module, or an export
-- that cut.ml took away, is outside the subset. assert_invalid and
-- assert_malformed pass only when the model refuses the module: it may never
-- accept a module that the spec rejects. A command that instantiates a module
-- fails when the model does not, unless the module is outside the subset: the
-- spec's harness stops there. Each unsupported assertion has a cause, which
-- the lines UNSUPPORTED n: cause count: cut.ml's reason (for an instruction
-- that it names, whether the compiler emits it), or why the model or this
-- harness does not run it.
--
-- With MAIN=<file.bendtt>, the book of src/main.bend (src/Shared/lower.ts), it
-- also writes a line FORMS: the forms that the compiler emits and that no
-- passing assertion runs (AGENTS.md 3.9.1.3.2), which must be none. They are
-- the forms of the instructions, of the module's parts and of their encodings
-- (Parts and encodings) in the compiler's modules (compilerModules), where an
-- LEB128 whose value the program's image decides takes each width that one of
-- 32 bits can have; a passing assertion runs those of its module and of the
-- function that it invokes.

open Quan Term

-- S-expressions
-- -------------

inductive Sexp where
  | atom : String → Sexp
  | str : List UInt8 → Sexp
  | list : List Sexp → Sexp
  deriving Inhabited

partial def Sexp.show : Sexp → String
  | .atom a => a
  | .str bs => "\"" ++ String.join (bs.map fun b => s!"\\{(Nat.toDigits 16 b.toNat).asString}") ++ "\""
  | .list xs => "(" ++ " ".intercalate (xs.map Sexp.show) ++ ")"

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

-- the UTF-8 bytes of the code point c
def utf8 (c : Nat) : List UInt8 := (String.singleton (Char.ofNat c)).toUTF8.toList

-- the bytes of a string's body, up to its closing quote, and the rest
partial def strBody (cs : List Char) (acc : Array UInt8) : Except String (List UInt8 × List Char) :=
  match cs with
  | [] => .error "unclosed string"
  | '"' :: rest => .ok (acc.toList, rest)
  | '\\' :: 'n' :: rest => strBody rest (acc.push 10)
  | '\\' :: 't' :: rest => strBody rest (acc.push 9)
  | '\\' :: 'r' :: rest => strBody rest (acc.push 13)
  | '\\' :: '\\' :: rest => strBody rest (acc.push 92)
  | '\\' :: '\'' :: rest => strBody rest (acc.push 39)
  | '\\' :: '"' :: rest => strBody rest (acc.push 34)
  | '\\' :: 'u' :: '{' :: rest =>
    let digits := rest.takeWhile (· ≠ '}')
    let v := digits.foldl (fun n c => n * 16 + (hexVal c).getD 0) 0
    strBody ((rest.dropWhile (· ≠ '}')).drop 1) (acc ++ (utf8 v).toArray)
  | '\\' :: a :: b :: rest =>
    match hexVal a, hexVal b with
    | some x, some y => strBody rest (acc.push (x * 16 + y).toUInt8)
    | _, _ => .error s!"bad escape \\{a}{b}"
  | c :: rest => strBody rest (acc ++ (utf8 c.toNat).toArray)

def isAtomChar (c : Char) : Bool := !(c.isWhitespace || c == '(' || c == ')' || c == '"' || c == ';')

-- the characters after a block comment (; ... ;), which may nest
partial def skipBlock (cs : List Char) (depth : Nat) : List Char :=
  match cs with
  | [] => []
  | ';' :: ')' :: rest => if depth = 0 then rest else skipBlock rest (depth - 1)
  | '(' :: ';' :: rest => skipBlock rest (depth + 1)
  | _ :: rest => skipBlock rest depth

-- the S-expressions of cs, up to a closing parenthesis (when inner) or the end
partial def parseSeq (cs : List Char) (inner : Bool) (acc : Array Sexp) :
    Except String (List Sexp × List Char) :=
  match cs with
  | [] => if inner then .error "unclosed (" else .ok (acc.toList, [])
  | ';' :: ';' :: rest => parseSeq (rest.dropWhile (· ≠ '\n')) inner acc
  | '(' :: ';' :: rest => parseSeq (skipBlock rest 0) inner acc
  | ')' :: rest => if inner then .ok (acc.toList, rest) else .error "unexpected )"
  | '(' :: rest => do
    let (xs, rest) ← parseSeq rest true #[]
    parseSeq rest inner (acc.push (.list xs))
  | '"' :: rest => do
    let (bs, rest) ← strBody rest #[]
    parseSeq rest inner (acc.push (.str bs))
  | c :: rest =>
    if c.isWhitespace then parseSeq rest inner acc
    else
      let a := (c :: rest).takeWhile isAtomChar
      parseSeq ((c :: rest).dropWhile isAtomChar) inner (acc.push (.atom (String.mk a)))

-- Values
-- ------

-- a U32, as Base's U32
def u32 (v : Nat) : Term := ctor "U32" [bits 32 v]

-- the constructor and fields of a value in the `bend -o` form (Shared/Bytes.lean)
partial def unctor : Term → Option (String × List Term)
  | Tup Q1 (Lab k) rest =>
    let rec fields : Term → Option (List Term)
      | Lab "()" => some []
      | Tup Q1 x r => (fields r).map (x :: ·)
      | _ => none
    (fields rest).map (k, ·)
  | _ => none

def unU32 (t : Term) : Option Nat :=
  match unctor t with
  | some ("U32", [w]) => unbits 32 w
  | _ => none

partial def unlist (t : Term) : Option (List Term) :=
  match unctor t with
  | some ("Nil", []) => some []
  | some ("Con", [x, xs]) => (unlist xs).map (x :: ·)
  | _ => none

-- an i32 literal of a binary script: hex, maybe negative, with _ between digits
def i32Lit (s : String) : Option Nat :=
  let (neg, cs) := match s.toList with
    | '-' :: rest => (true, rest)
    | cs => (false, cs)
  match cs with
  | '0' :: 'x' :: ds =>
    let ds := ds.filter (· ≠ '_')
    if ds.isEmpty then none else
      (ds.foldlM (fun n c => (hexVal c).map (n * 16 + ·)) 0).map fun v =>
        if neg then (2 ^ 32 - v % 2 ^ 32) % 2 ^ 32 else v % 2 ^ 32
  | _ => none

-- the i32 value of (i32.const n); None for any other value
def constOf : Sexp → Option Nat
  | .list [.atom "i32.const", .atom n] => i32Lit n
  | _ => none

-- Running
-- -------

structure Cfg where
  B : Book
  fuel : Term
  limit : Term
  -- the names of the instructions that the compiler emits, when MAIN gives them
  emits : Option (List String) := none

-- the value that t runs to, by the trusted interpreter
def evalTerm (c : Cfg) (t : Term) : Option Term :=
  let (v, _) := steps c.B 4000000000 t 0
  if value c.B v then some v else none

-- how an instantiation ends
inductive Made where
  | inst : Term → Made
  | unsupported | out_of_memory | trap | stuck

def instantiate (c : Cfg) (w : List UInt8) : Made :=
  match (evalTerm c (App Q1 (App Q1 (App Q1 (Ref "Wasm.instantiate") (bytes w)) c.limit) (ctor "Nil" []))).bind unctor with
  | some ("Wasm.Made.instance", [i]) => .inst i
  | some ("Wasm.Made.unsupported", []) => .unsupported
  | some ("Wasm.Made.out_of_memory", []) => .out_of_memory
  | some ("Wasm.Made.trap", []) => .trap
  | _ => .stuck

-- how an invocation ends
inductive Invoked where
  | values : List Nat → Term → Invoked
  | trap : Term → Invoked
  | not_done | unsupported | stuck

def invoke (c : Cfg) (i : Term) (name : List UInt8) (args : List Nat) : Invoked :=
  let t := App Q1 (App Q1 (App Q1 (App Q1 (Ref "Wasm.invoke") c.fuel) i) (bytes name)) (list (args.map u32))
  match (evalTerm c t).bind unctor with
  | some ("Wasm.Invoked.values", [vs, i', _]) =>
    match (unlist vs).bind (·.mapM unU32) with
    | some ns => .values ns i'
    | none => .stuck
  | some ("Wasm.Invoked.trap", [i']) => .trap i'
  | some ("Wasm.Invoked.not_done", []) => .not_done
  | some ("Wasm.Invoked.unsupported", []) => .unsupported
  | _ => .stuck

-- Forms
-- -----
--
-- The form of an instruction, as AGENTS.md 3.9.1.3.2 counts them: its kind; a
-- load's or store's offset; an op's operator; for a branch, whether it leaves
-- its innermost label (depth 0) or more, and the kind of the label that it
-- goes to. The instructions are terms of the model's Wasm.Instr.
-- A block's or loop's form, and so its label's kind, holds its block type.

-- the forms of the instructions xs, inside labels of the kinds ks, innermost
-- first
partial def instrForms (ks : List String) (xs : Term) : List String :=
  ((unlist xs).getD []).flatMap fun x =>
    match unctor x with
    | some (k, fs) =>
      let kind := String.ofList (k.toList.drop "Wasm.Instr.".length)
      match kind, fs with
      | "block", [t, b] | "loop", [t, b] =>
        let f := s!"{kind} {((unctor t).map fun (c, _) => String.ofList (c.toList.drop "Wasm.Blocktype.".length)).getD "?"}"
        f :: instrForms (f :: ks) b
      | "br", [l] | "br_if", [l] =>
        let d := (unU32 l).getD 0
        [s!"{kind} depth {if d == 0 then "0" else ">0"} to {ks.getD d "?"}"]
      | "load", [o] | "load8_u", [o] | "store", [o] | "store8", [o] =>
        [s!"{kind} offset {(unU32 o).getD 0}"]
      | "op", [o] => [s!"op {((unctor o).map (·.1)).getD "?"}"]
      | _, _ => [kind]
    | none => ["?"]

-- the forms of each function of the module m (a Wasm.Module term)
def Module.forms (m : Term) : List (List String) :=
  match unctor m with
  | some ("Wasm.Module", [_, fs, _, _, _]) => ((unlist fs).getD []).map fun f =>
    match unctor f with
    | some ("Wasm.Func", [_, _, b]) => instrForms ["function"] b
    | _ => ["?"]
  | _ => [["?"]]

-- the forms of the function that the instance i (a Wasm.Instance term) exports
-- as name
def exportForms (i : Term) (name : List UInt8) : List String :=
  match unctor i with
  | some ("Wasm.Instance", [m, _]) =>
    match unctor m with
    | some ("Wasm.Module", [_, _, _, es, _]) =>
      let j := ((unlist es).getD []).findSome? fun e => match unctor e with
        | some ("Wasm.Export.func", [n, j]) => if unbytes n == some name then unU32 j else none
        | _ => none
      (j.bind ((Module.forms m)[·]?)).getD []
    | _ => []
  | _ => []

-- Parts and encodings
-- -------------------
--
-- The forms of a module's parts and of their encodings (AGENTS.md 3.9.1.3.2),
-- read from its bytes as the binary format lays them out (spec 5): each part
-- of a section, and each LEB128 number in it, whose form is its field and its
-- width (the compiler writes each number in its fewest bytes, the spec's
-- reference encoder each size in 5). They cover the subset's sections and
-- instructions; for any other byte, a module has none.

-- a form of a module's part or encoding: a part, by name, or an LEB128 number
-- of a field, with its value and its width
inductive Form where
  | part (name : String)
  | leb (field : String) (value width : Nat)

def Form.show : Form → String
  | .part p => p
  | .leb f _ w => s!"{f}: {w}-byte LEB128"

-- what a module's bytes say: its forms, in order, but those of each
-- function's code (by the function's index), the index of the function that
-- each export names, and the names of its instructions
structure Coded where
  module : List Form := []
  funcs : List (List Form) := []
  exports : List (List UInt8 × Nat) := []
  instrs : List String := []

-- the forms that a passing assertion on the export name runs: the module's,
-- and its function's
def Coded.run (k : Coded) (name : List UInt8) : List String :=
  ((k.module ++ (((List.lookup name k.exports).bind (k.funcs[·]?)).getD [])).map Form.show).eraseDups

-- an LEB128 number of the field at the start of bs (spec 5.2.2), of 7 bits a
-- byte, the lowest first, and at most 10 bytes; and the bytes after it
def leb (field : String) (bs : List UInt8) : Option (Form × List UInt8) :=
  (go bs 10).map fun (v, w, rest) => (.leb field v w, rest)
where
  go : List UInt8 → Nat → Option (Nat × Nat × List UInt8)
  | b :: rest, k + 1 =>
    if b < 128 then some (b.toNat, 1, rest)
    else (go rest k).map fun (v, w, r) => (b.toNat - 128 + 128 * v, w + 1, r)
  | _, _ => none

-- the value of an LEB128 number's form
def Form.value : Form → Nat
  | .leb _ v _ => v
  | .part _ => 0

-- n items at the start of bs, each read by item, and the bytes after them
def items (n : Nat) (bs : List UInt8) (item : List UInt8 → Option (α × List UInt8)) :
    Option (List α × List UInt8) :=
  match n with
  | 0 => some ([], bs)
  | m + 1 => do
    let (x, bs) ← item bs
    let (xs, bs) ← items m bs item
    pure (x :: xs, bs)

-- a vector (spec 5.1.3) of the section what: its length's form, and its items
def vec (what : String) (bs : List UInt8) (item : List UInt8 → Option (α × List UInt8)) :
    Option (Form × List α) := do
  let (n, bs) ← leb s!"{what} section count" bs
  let (xs, []) ← items n.value bs item | none
  pure (n, xs)

-- the immediates of an instruction of the subset (spec 5.4)
inductive Imm where
  | none | index (what : String) | value | memarg | memory | blocktype

-- the instructions of the subset, by opcode
def opcodes : List (UInt8 × String × Imm) := [
  (0x02, "block", .blocktype), (0x03, "loop", .blocktype),
  (0x0C, "br", .index "label"), (0x0D, "br_if", .index "label"),
  (0x20, "local.get", .index "index"), (0x21, "local.set", .index "index"),
  (0x22, "local.tee", .index "index"),
  (0x28, "i32.load", .memarg), (0x2D, "i32.load8_u", .memarg),
  (0x36, "i32.store", .memarg), (0x3A, "i32.store8", .memarg),
  (0x3F, "memory.size", .memory), (0x40, "memory.grow", .memory),
  (0x41, "i32.const", .value), (0x45, "i32.eqz", .none),
  (0x46, "i32.eq", .none), (0x47, "i32.ne", .none), (0x49, "i32.lt_u", .none),
  (0x4B, "i32.gt_u", .none), (0x4D, "i32.le_u", .none), (0x4F, "i32.ge_u", .none),
  (0x6A, "i32.add", .none), (0x6B, "i32.sub", .none), (0x71, "i32.and", .none),
  (0x72, "i32.or", .none), (0x74, "i32.shl", .none), (0x76, "i32.shr_u", .none)]

-- the forms of an immediate of the instruction x, and the bytes after it; a
-- memarg's alignment of 2^6 or more names another memory
def immForms (x : String) (bs : List UInt8) : Imm → Option (List Form × List UInt8)
  | .none => some ([], bs)
  | .index what => (leb s!"{x} {what}" bs).map fun (f, bs) => ([f], bs)
  | .value => (leb s!"{x} immediate" bs).map fun (f, bs) => ([f], bs)
  | .memory => (leb s!"{x} memory index" bs).map fun (f, bs) => ([f], bs)
  | .memarg => do
    let (a, bs) ← leb s!"{x} alignment" bs
    guard (a.value < 64)
    let (o, bs) ← leb s!"{x} offset" bs
    pure ([.part s!"{x} alignment: {a.value}", o], bs)
  | .blocktype =>
    match bs with
    | 0x40 :: bs => some ([.part s!"{x} type: empty"], bs)
    | 0x7F :: bs => some ([.part s!"{x} type: i32"], bs)
    | b :: _ =>
      if 0x40 ≤ b ∧ b < 0x80 then none
      else (leb s!"{x} type index" bs).map fun (f, bs) => ([f], bs)
    | [] => none

-- the forms of the instructions at the start of bs, up to the end of the
-- block that holds them, inside depth more blocks, after the forms fs and the
-- names ns; and the bytes after it
partial def instrsForms (bs : List UInt8) (depth : Nat) (fs : Array Form) (ns : Array String) :
    Option (Array Form × Array String × List UInt8) :=
  match bs with
  | 0x0B :: bs => if depth == 0 then some (fs, ns, bs) else instrsForms bs (depth - 1) fs ns
  | op :: bs => do
    let (_, x, imm) ← opcodes.find? (·.1 == op)
    let (f, bs) ← immForms x bs imm
    let depth := if op == 0x02 || op == 0x03 then depth + 1 else depth
    instrsForms bs depth (fs ++ f.toArray) (if ns.contains x then ns else ns.push x)
  | [] => none

-- a group of locals (spec 5.5.13), of i32
def localsForm (bs : List UInt8) : Option (Form × List UInt8) := do
  let (n, 0x7F :: bs) ← leb "local group size" bs | none
  pure (n, bs)

-- a function's code (spec 5.5.13): the forms of its size, locals and body,
-- and the names of its instructions
def codeForms (bs : List UInt8) : Option ((List Form × List String) × List UInt8) := do
  let (n, bs) ← leb "code size" bs
  guard (n.value ≤ bs.length)
  let (g, c) ← leb "local groups count" (bs.take n.value)
  let (ls, c) ← items g.value c localsForm
  let (fs, ns, []) ← instrsForms c 0 #[] #[] | none
  let groups := match g.value with
    | 0 => "no locals" | 1 => "one group of locals" | _ => "groups of locals"
  pure ((n :: g :: .part groups :: ls ++ fs.toList, ns.toList), bs.drop n.value)

-- n bytes at the start of bs, and the bytes after them
def bytesOf (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bs.length then some (bs.take n, bs.drop n) else none

-- a function type (spec 5.3.6), of i32 parameters and results
def typeForms (bs : List UInt8) : Option (List Form × List UInt8) := do
  let 0x60 :: bs := bs | none
  let (p, bs) ← leb "type parameters count" bs
  let (ps, bs) ← bytesOf p.value bs
  let (q, bs) ← leb "type results count" bs
  let (qs, bs) ← bytesOf q.value bs
  guard ((ps ++ qs).all (· == 0x7F))
  pure ([.part s!"type [{p.value} -> {q.value}]", p, q], bs)

-- an export (spec 5.5.10): its forms, and a function's name and index
def exportPartForms (bs : List UInt8) : Option ((List Form × Option (List UInt8 × Nat)) × List UInt8) := do
  let (n, bs) ← leb "export name length" bs
  let (name, bs) ← bytesOf n.value bs
  let (kind, func, bs) ← match bs with
    | 0x00 :: bs => some ("export of a function", true, bs)
    | 0x02 :: bs => some ("export of the memory", false, bs)
    | _ => none
  let (i, bs) ← leb "export index" bs
  pure (([n, .part kind, i], if func then some (name, i.value) else none), bs)

-- a memory (spec 5.3.7) of a minimum only
def memoryForms : List UInt8 → Option (List Form × List UInt8)
  | 0x00 :: bs => (leb "memory minimum" bs).map fun (m, bs) => ([.part "memory limits: a minimum only", m], bs)
  | _ => none

-- an active data segment of memory 0 (spec 5.5.14), whose offset is
-- i32.const n end
def dataForms (bs : List UInt8) : Option (List Form × List UInt8) := do
  let (f, 0x41 :: bs) ← leb "data segment flag" bs | none
  guard (f.value == 0)
  let (o, 0x0B :: bs) ← leb "data offset i32.const immediate" bs | none
  let (n, bs) ← leb "data length" bs
  let (_, bs) ← bytesOf n.value bs
  pure ([f, .part "active data segment of memory 0", o, n], bs)

-- the section of the id (spec 5.5.2), whose content is c, in k
def sectionForms (k : Coded) (id : UInt8) (c : List UInt8) : Option Coded :=
  let forms (fs : List Form) := { k with module := k.module ++ fs }
  match id with
  | 1 => (vec "type" c typeForms).map fun (f, fs) => forms (f :: fs.flatten)
  | 3 => (vec "function" c fun bs => (leb "function type index" bs)).map fun (f, fs) => forms (f :: fs)
  | 5 => (vec "memory" c memoryForms).map fun (f, fs) => forms (f :: fs.flatten)
  | 7 => (vec "export" c exportPartForms).map fun (f, es) =>
    { forms (f :: (es.map (·.1)).flatten) with exports := es.filterMap (·.2) }
  | 10 => (vec "code" c codeForms).map fun (f, cs) =>
    { forms [f] with funcs := cs.map (·.1), instrs := (cs.map (·.2)).flatten.eraseDups }
  | 11 => (vec "data" c dataForms).map fun (f, fs) => forms (f :: fs.flatten)
  | _ => none

def sectionName : UInt8 → String
  | 1 => "type" | 3 => "function" | 5 => "memory" | 7 => "export" | 10 => "code" | 11 => "data"
  | _ => "?"

-- the forms of the sections at the start of bs, in k
partial def sectionsForms (k : Coded) : List UInt8 → Option Coded
  | [] => some k
  | id :: bs => do
    let (n, bs) ← leb s!"{sectionName id} section size" bs
    let (c, bs) ← bytesOf n.value bs
    sectionsForms (← sectionForms { k with module := k.module ++ [n] } id c) bs

-- what the bytes of a module of the subset say (spec 5.5.16): its header,
-- then its sections; nothing for bytes that are not one
def coded (w : List UInt8) : Coded :=
  match w with
  | 0x00 :: 0x61 :: 0x73 :: 0x6D :: 0x01 :: 0x00 :: 0x00 :: 0x00 :: bs => (sectionsForms {} bs).getD {}
  | _ => {}

-- the fields of the LEB128 numbers whose values differ between two modules of
-- the same layout, each once; none when their layouts differ
def Coded.changed (a b : Coded) : Option (List String) :=
  let fa := a.module ++ a.funcs.flatten
  let fb := b.module ++ b.funcs.flatten
  if fa.length != fb.length then none else
  (fa.zip fb).foldlM (init := []) fun fields (x, y) =>
    match x, y with
    | .leb f v _, .leb g u _ =>
      if f != g then none else some (if v == u || fields.contains f then fields else fields ++ [f])
    | .part p, .part q => if p == q then some fields else none
    | _, _ => none

-- the widths of an LEB128 number of 32 bits: 1 to ⌈32/7⌉ bytes
def u32Widths : List Nat := List.range' 1 ((32 + 6) / 7)

-- Scripts
-- -------

-- what cut.ml says of the module that a command of the script defines
-- (x.facts): why it is outside the subset (none: it is inside), why each
-- export that cut.ml took away is, and its exports that change nothing in an
-- instance
structure Facts where
  outside : List String := []
  cut : List (List UInt8 × List String) := []
  pure : List (List UInt8) := []

-- an instance, with the facts and what the bytes of its module say, or why
-- there is none
inductive Inst where
  | ok : Term → Facts → Coded → Inst
  | none : String → Inst

structure St where
  -- the modules that the script defines: each with its name if it has one,
  -- its bytes, and its facts
  defs : List (Option String × List UInt8 × Facts) := []
  -- the instances, the newest first, each with its name if it has one
  insts : List (Option String × Inst) := []
  pass : Nat := 0
  fail : Nat := 0
  unsupported : Nat := 0
  notDone : Nat := 0
  failures : Array String := #[]
  -- the causes of the unsupported assertions, each with how many it has
  causes : List (String × Nat) := []
  -- the forms that passing assertions ran
  forms : List String := []

-- the counts cs, with one more for k
def bump (cs : List (String × Nat)) (k : String) (n : Nat := 1) : List (String × Nat) :=
  if cs.any (·.1 == k) then cs.map fun (j, m) => (j, if j == k then m + n else m) else cs ++ [(k, n)]

-- the cause that a reason of cut.ml's gives: an instruction that it names is
-- one that the compiler does not emit, as the compiler's own modules show
def Cfg.cause (c : Cfg) (why : String) : String :=
  let x := String.ofList (why.toList.drop "instruction ".length)
  match c.emits with
  | some es =>
    if !why.startsWith "instruction " then why
    else if es.contains x then s!"an instruction that the compiler emits: {x}"
    else "instructions that the compiler does not emit"
  | none => why

-- why the model refuses a module of these facts: the first reason of cut.ml's,
-- when cut.ml finds it outside the subset
def Facts.why (c : Cfg) (f : Facts) : Option String := f.outside.head?.map c.cause

def St.add (s : St) (n : Option String) (i : Inst) : St := { s with insts := (n, i) :: s.insts }

-- the position of the instance of the name, or of the newest
def St.find (s : St) : Option String → Option Nat
  | none => if s.insts.isEmpty then none else some 0
  | some k => s.insts.findIdx? (·.1 == some k)

def St.get (s : St) (n : Option String) : Option Inst :=
  (s.find n).bind fun j => s.insts[j]?.map (·.2)

def St.defn (s : St) (n : Option String) : Option (List UInt8 × Facts) :=
  match n with
  | none => s.defs.head?.map (·.2)
  | some k => (s.defs.find? (·.1 == some k)).map (·.2)

def St.passed (s : St) : St := { s with pass := s.pass + 1 }
def St.unsup (s : St) (why : String) : St :=
  { s with unsupported := s.unsupported + 1, causes := bump s.causes why }

-- s after a passing assertion on the export name of the instance n
def St.ran (s : St) (n : Option String) (name : List UInt8) : St :=
  match s.get n with
  | some (.ok i _ k) => { s.passed with forms := (s.forms ++ exportForms i name ++ k.run name).eraseDups }
  | _ => s.passed
def St.notdone (s : St) : St := { s with notDone := s.notDone + 1 }
def St.failed (s : St) (why : String) (e : Sexp) : St :=
  { s with fail := s.fail + 1, failures := s.failures.push s!"{why}: {(e.show).take 300}" }

def strOf : Sexp → Option (List UInt8)
  | .str b => some b
  | _ => none

-- a module of the script: its name and bytes
def moduleOf : List Sexp → Option (Option String × List UInt8)
  | .atom "binary" :: ss => (ss.mapM strOf).map fun bs => (none, bs.flatten)
  | .atom n :: .atom "binary" :: ss =>
    if n.startsWith "$" then (ss.mapM strOf).map fun bs => (some n, bs.flatten) else none
  | _ => none

-- the names in (module instance $i? $d?): the instance's, and the definition's
def instanceNames : List Sexp → Option String × Option String
  | [.atom i, .atom d] => (some i, some d)
  | [.atom i] => (some i, none)
  | _ => (none, none)

-- s with the instance n of the module of the bytes w and the facts f. The
-- model must instantiate it, unless it is outside the subset: then there is
-- no instance, and the reason is why
def St.instance (s : St) (c : Cfg) (n : Option String) (w : List UInt8) (f : Facts) : St :=
  let failed (why : String) :=
    (s.failed why (.list [.atom "module", .atom "binary", .str w])).add n (.none why)
  match instantiate c w, f.why c with
  | .inst i, _ => s.add n (.ok i f (coded w))
  | .unsupported, some why => s.add n (.none why)
  | .unsupported, none => failed "a module of the subset that the model refuses"
  | .out_of_memory, _ => failed "a module that runs out of memory at instantiation"
  | .trap, _ => failed "a module that traps at instantiation"
  | .stuck, _ => failed "a module that gets stuck at instantiation"

-- (assert_trap (module ...) _): the module of the bytes w, of the facts f,
-- traps when it is instantiated
def St.assertTrap (s : St) (c : Cfg) (e : Sexp) : Option (List UInt8 × Facts) → St
  | none => s.unsup "no module"
  | some (w, f) =>
    match instantiate c w, f.why c with
    | .trap, _ => s.passed
    | .unsupported, some why => s.unsup why
    | .unsupported, none => s.failed "refused a module of the subset" e
    | _, _ => s.failed "did not trap at instantiation" e

-- the instance and the export that an action, (invoke $i? "name" consts*),
-- names
def target : Sexp → Option (Option String × List UInt8)
  | .list (.atom "invoke" :: .atom n :: .str name :: _) => some (some n, name)
  | .list (.atom "invoke" :: .str name :: _) => some (none, name)
  | _ => none

-- why an action on the export name of the instance n is outside the subset,
-- when cut.ml or the instance say it is
def St.why (s : St) (c : Cfg) (n : Option String) (name : List UInt8) : Option String :=
  match s.get n with
  | some (.ok _ f _) => ((List.lookup name f.cut).bind (·.head?)).map c.cause
  | some (.none why) => some why
  | none => some "no module"

-- an action: the instance and the export it names, what the model gives,
-- which is unsupported when the instance or the values are not of the subset,
-- and then why
def action (c : Cfg) (s : St) (e : Sexp) : Option (Option String × List UInt8 × Invoked × String) :=
  let run (n : Option String) (name : List UInt8) (args : List Sexp) :=
    let why := (s.why c n name).getD "an export of the subset that the model does not run"
    some (n, name, match s.get n, args.mapM constOf with
      | some (.ok i _ _), some ns => (invoke c i name ns, why)
      | some (.ok _ _ _), none => (.unsupported, "non-i32 values")
      | _, _ => (.unsupported, why))
  match e with
  | .list (.atom "invoke" :: .atom n :: .str name :: args) => run (some n) name args
  | .list (.atom "invoke" :: .str name :: args) => run none name args
  | _ => none

-- the instance after an action on its export. When the model does not run the
-- action to its end, and the export may change the instance, the instance is
-- not in the state that the script expects after it, so the commands on it
-- after that are unsupported, for the reason why.
def St.after (s : St) (n : Option String) (name : List UInt8) (r : Invoked) (why : String) : St :=
  match (s.find n).bind fun j => s.insts[j]?.map (j, ·) with
  | some (j, k, .ok i f m) =>
    let lost (why : String) : Inst := if f.pure.contains name then .ok i f m else .none why
    let i' : Inst := match r with
      | .values _ i' | .trap i' => .ok i' f m
      | .unsupported => lost why
      | .not_done => lost "an action that ran out of fuel"
      | .stuck => lost "an action that got stuck"
    { s with insts := s.insts.set j (k, i') }
  | _ => s

-- a result pattern holds for the value v
def patOk (p : Sexp) (v : Nat) : Option Bool :=
  match p with
  | .list (.atom "either" :: ps) => (ps.mapM fun q => constOf q).map fun ns => ns.contains v
  | _ => (constOf p).map (· == v)

-- the command e of the script, its k-th; facts gives cut.ml's facts of the
-- module that a command defines
def command (c : Cfg) (facts : Nat → Facts) (k : Nat) (s : St) (e : Sexp) : St :=
  match e with
  | .list (.atom "module" :: .atom "definition" :: rest) =>
    match moduleOf rest with
    | some (n, w) => { s with defs := (n, w, facts k) :: s.defs }
    | none => s
  | .list (.atom "module" :: .atom "instance" :: rest) =>
    let (n, d) := instanceNames rest
    match s.defn d with
    | some (w, f) => s.instance c n w f
    | none => s.add n (.none "no module")
  | .list (.atom "module" :: rest) =>
    match moduleOf rest with
    | some (n, w) => s.instance c n w (facts k)
    | none =>
      let n := match rest with | .atom n :: _ => if n.startsWith "$" then some n else none | _ => none
      s.add n (.none "a module of the text format")
  | .list [.atom "register", _] | .list [.atom "register", _, _] => s
  | .list (.atom "invoke" :: _) =>
    match action c s e with
    | some (n, name, r, why) => s.after n name r why
    | none => s
  | .list (.atom "assert_return" :: .list (.atom "get" :: _) :: _) => s.unsup "globals"
  | .list (.atom "assert_return" :: a :: pats) =>
    match action c s a with
    | none => s.unsup "actions of another kind"
    | some (n, name, r, why) =>
      let s := s.after n name r why
      match r with
      | .values vs _ =>
        if vs.length != pats.length then s.failed s!"gave {vs}" e else
        match (pats.zip vs).mapM fun (p, v) => patOk p v with
        | none => s.unsup "non-i32 values"
        | some oks => if oks.all id then s.ran n name else s.failed s!"gave {vs}" e
      | .trap _ => s.failed "trapped" e
      | .not_done => s.notdone
      | .unsupported => s.unsup why
      | .stuck => s.failed "stuck" e
  | .list [.atom "assert_trap", .list (.atom "module" :: .atom "instance" :: rest), _] =>
    s.assertTrap c e (s.defn (instanceNames rest).2)
  | .list [.atom "assert_trap", .list (.atom "module" :: rest), _] =>
    s.assertTrap c e ((moduleOf rest).map fun (_, w) => (w, facts k))
  | .list [.atom "assert_trap", a, _] =>
    match action c s a with
    | none => s.unsup "actions of another kind"
    | some (n, name, r, why) =>
      let s := s.after n name r why
      match r with
      | .trap _ => s.ran n name
      | .not_done => s.notdone
      | .unsupported => s.unsup why
      | .values vs _ => s.failed s!"gave {vs}" e
      | .stuck => s.failed "stuck" e
  | .list [.atom kind, .list (.atom "module" :: rest), _] =>
    if kind == "assert_invalid" || kind == "assert_malformed" then
      match moduleOf rest with
      | none => s.unsup "modules of the text format"
      | some (_, w) =>
        match instantiate c w with
        | .unsupported => s.passed
        | .stuck => s.failed "stuck" e
        | _ => s.failed "accepted" e
    else s.unsup s!"{kind} assertions"
  -- another assertion on an action: the model does not check it, but the
  -- spec's harness runs the action
  | .list (.atom kind :: a :: _) =>
    match target a with
    | some (n, name) =>
      let why := (s.why c n name).getD s!"{kind} assertions"
      (s.after n name .unsupported why).unsup why
    | none => s.unsup s!"{kind} assertions"
  | _ => s.unsup "commands of another kind"

-- cut.ml's facts of the module that each command defines: x.facts, which
-- cut.ml writes next to the binary script x.bin.wast
def factsOf (path : String) : IO (Nat → Facts) := do
  let p := String.ofList (path.toList.take (path.length - ".bin.wast".length)) ++ ".facts"
  match parseSeq (← IO.FS.readFile p).toList false #[] with
  | .error msg => throw (IO.userError s!"{p}: {msg}")
  | .ok (es, _) =>
    let text (bs : List UInt8) : String := String.ofList (bs.map fun b => Char.ofNat b.toNat)
    let lines := es.filterMap fun e => match e with
      | .list (.atom kind :: .atom i :: xs) => i.toNat?.map ((kind, ·, xs.filterMap strOf))
      | _ => none
    return fun k => lines.foldl (init := {}) fun (f : Facts) (kind, i, xs) =>
      if i != k then f else match kind, xs with
        | "outside", whys => { f with outside := whys.map text }
        | "cut", name :: whys => { f with cut := f.cut ++ [(name, whys.map text)] }
        | "pure", names => { f with pure := names }
        | _, _ => f

def runFile (c : Cfg) (h : IO.FS.Handle) (path : String) : IO St := do
  let text ← IO.FS.readFile path
  let facts ← factsOf path
  match parseSeq text.toList false #[] with
  | .error msg => throw (IO.userError s!"{path}: {msg}")
  | .ok (cmds, _) =>
    let mut s : St := {}
    let mut k := 0
    for e in cmds do
      s := command c facts k s e
      k := k + 1
      if k % 10 == 0 then
        h.putStrLn s!"  {path}: {k}/{cmds.length} commands, {s.pass} passed, {s.fail} failed"
        h.flush
    pure s

-- the modules that the compiler emits: the machine's for no cells and for a
-- page of them (2^16 / 20 cells of 20 bytes, so that the input starts past
-- the first page), and those that end at once with the status 1 or 2. The
-- machine's code is the same for every program: the first two differ only
-- where the program's image decides
def compilerModules (M : Book) : List (List UInt8) :=
  let cells (k : Nat) := list (List.replicate k (Ref "Compiler_2f_Cir_2f_impl.Cir.Cell.zero"))
  [App Q1 (Ref "Compiler_2f_impl.Compiler.module") (cells 0),
   App Q1 (Ref "Compiler_2f_impl.Compiler.module") (cells (2 ^ 16 / 20)),
   App Q1 (Ref "Compiler_2f_impl.Compiler.halt") (u32 1),
   App Q1 (Ref "Compiler_2f_impl.Compiler.halt") (u32 2)].map fun t =>
    let (w, _) := steps M 4000000000 t 0
    (unbytes w).getD []

-- the strings xs, each once, in order
def once (xs : List String) : List String :=
  (xs.foldl (init := (({} : Std.HashSet String), #[])) fun (seen, out) x =>
    if seen.contains x then (seen, out) else (seen.insert x, out.push x)).2.toList

def main' : IO Unit := do
  let B ← Script.book
  let dir ← Script.env "TESTS"
  let only := (← IO.getEnv "ONLY").map (·.splitOn ",")
  let h ← IO.FS.Handle.mk (← Script.env "OUT") .write
  -- the model's fuel per invocation, enough for a loop over a page's 2^16
  -- bytes (memory_grow.wast), and its memory limit: 2^16 pages, the spec's own
  -- limit for 32-bit memories; the engine refuses no grow within it (no
  -- answers), as the spec's interpreter does
  let c : Cfg := { B, fuel := Form.nat 2000000, limit := u32 65536 }
  let compiled ← (← IO.getEnv "MAIN").mapM fun main => do pure (compilerModules (← Script.bookAt main))
  let c := { c with emits := compiled.map fun ws => once (ws.flatMap (coded · |>.instrs)) }
  let files := ((← System.FilePath.readDir dir).map (·.path.toString)).qsort (· < ·) |>.toList.filter fun p =>
    p.endsWith ".bin.wast" && (only.map fun ks => ks.any fun k => p.endsWith s!"/{k}.bin.wast").getD true
  let mut total : St := {}
  for p in files do
    let t0 ← IO.monoMsNow
    let s ← runFile c h p
    let t1 ← IO.monoMsNow
    h.putStrLn s!"{p}: {s.pass} passed, {s.fail} failed, {s.unsupported} unsupported, {s.notDone} not done, {(t1 - t0) / 1000} s"
    for f in s.failures do h.putStrLn s!"  FAIL {f}"
    for (why, n) in s.causes do h.putStrLn s!"  {n} unsupported: {why}"
    h.flush
    total := { total with pass := total.pass + s.pass, fail := total.fail + s.fail,
                          unsupported := total.unsupported + s.unsupported, notDone := total.notDone + s.notDone,
                          causes := s.causes.foldl (fun cs (why, n) => bump cs why n) total.causes,
                          forms := (total.forms ++ s.forms).eraseDups }
  h.putStrLn s!"ALL: {total.pass} passed, {total.fail} failed, {total.unsupported} unsupported, {total.notDone} not done"
  for (why, n) in total.causes do h.putStrLn s!"UNSUPPORTED {n}: {why}"
  -- the forms of the compiler's modules, as the model decodes them and as
  -- their bytes say; a field that the program's image decides takes each width
  -- that its LEB128, of 32 bits, can have
  if let some ws := compiled then
    let ks := ws.map coded
    let fields := match ks with
      | a :: b :: _ => (a.changed b).getD ["?"]
      | _ => ["?"]
    h.putStrLn s!"IMAGE: the fields that the program's image decides: {fields}"
    let image := fields.flatMap fun f => u32Widths.map fun w => (Form.leb f 0 w).show
    let emitted := once ((ws.zip ks).flatMap fun (w, k) =>
      let instrs := match (evalTerm c (App Q1 (Ref "Wasm.decode.module") (bytes w))).bind unctor with
        | some ("Some", [m]) => (Module.forms m).flatten
        | _ => ["?"]
      instrs ++ (if k.funcs.isEmpty then ["?"] else (k.module ++ k.funcs.flatten).map Form.show)) ++ image
    let notRun := emitted.filter (!total.forms.contains ·)
    h.putStrLn s!"FORMS: {emitted.length} that the compiler emits, not run by a passing test: {notRun}"
  h.flush

#eval main'
