(* Cut
   ===

   cut.exe x.wast x.facts: the binary script of the test script x.wast, as
   wasm -d x.wast -o x.bin.wast writes it, except that each module that a
   command defines in the text format keeps only its functions and exports
   inside the subset of the Bend version of WASM (AGENTS.md 3.9.1.2), with the
   types they use; the other functions and exports go, and so do its tables,
   elements and globals, which no function of the subset uses. A module with
   imports, tags, a start function or a data offset that reads a global stays
   whole, as do the modules of assertions. So the model refuses only what is
   outside the subset, and the official results still hold for the functions
   that a module keeps. A module that a command defines in the binary format
   keeps its own bytes, which wasm -d would encode again. For each command of
   the binary script that defines a module, x.facts says (by the command's
   index in the binary script, which drops the quoted modules of
   assert_malformed):
     (outside i "why" ...): why the module, as the binary script defines it,
       is outside the subset, if it is;
     (cut i "name" "why" ...): why an export that the cut took away is;
     (pure i "name" ...): the exports of the module's functions that change
       nothing in its instance (pure_exports).
   WasmTests.lean reads them. A why is one of the reasons below; an
   instruction outside the subset is named. It uses the spec's own parser,
   syntax, encoder and printer (convert.ts builds it with them). *)

open Types
open Ast
open Source

let is_i32 (t : valtype) = t = NumT I32T

let is_ascii (n : name) = List.for_all (fun c -> c < 128) n

let export_names (m : module_) =
  List.map (fun (e : export) -> let Export (n, _) = e.it in n) m.it.exports

(* the items of a list, each once, where it first comes *)
let rec distinct = function
  | [] -> []
  | x :: rest -> x :: distinct (List.filter (( <> ) x) rest)

(* the defined types, one per subtype of each recursion group *)
let subtypes (m : module_) =
  List.concat_map (fun (t : type_) -> let RecT sts = t.it in sts) m.it.types

(* the type x, when it is of the subset: i32 parameters and results *)
let functype (m : module_) (x : idx) =
  match List.nth_opt (subtypes m) (Int32.to_int x.it) with
  | Some (SubT (_, _, FuncT (ins, outs)))
    when List.for_all is_i32 ins && List.for_all is_i32 outs ->
    Some (ins, outs)
  | _ -> None

(* the name of an instruction, as the text format writes it *)
let mnemonic (e : instr) =
  match Arrange.instr e with
  | Sexpr.Node (head, _) | Sexpr.Atom head -> List.hd (String.split_on_char ' ' head)

let memory_why (x : idx) = if x.it = 0l then [] else ["more than one memory"]

(* a block type of the subset: no values, an i32, or a type of the subset *)
let blocktype_why (m : module_) = function
  | ValBlockType None -> []
  | ValBlockType (Some t) -> if is_i32 t then [] else ["non-i32 values"]
  | VarBlockType x -> if functype m x = None then ["non-i32 values"] else []

(* why the instructions of a block are outside the subset, which has none
   after a br *)
let rec instrs_why m es =
  match es with
  | [] -> []
  | e :: rest ->
    instr_why m e
    @ (match e.it, rest with
       | Br _, _ :: _ -> ["an instruction after br"]
       | _ -> instrs_why m rest)

(* why an instruction is outside the subset: the instructions that the
   compiler emits take these forms *)
and instr_why m (e : instr) =
  match e.it with
  | Block (bt, es) | Loop (bt, es) -> blocktype_why m bt @ instrs_why m es
  | Br _ | BrIf _ | LocalGet _ | LocalSet _ | LocalTee _ -> []
  | Load (x, {ty = I32T; pack = None | Some (Pack.Pack8, Pack.U); _})
  | Store (x, {ty = I32T; pack = None | Some Pack.Pack8; _})
  | MemorySize x | MemoryGrow x -> memory_why x
  | Const {it = Value.I32 _; _} -> []
  | Test (Value.I32 I32Op.Eqz) -> []
  | Compare (Value.I32 (I32Op.Eq | I32Op.Ne | I32Op.Lt Pack.U | I32Op.Gt Pack.U
                       | I32Op.Le Pack.U | I32Op.Ge Pack.U)) -> []
  | Binary (Value.I32 (I32Op.Add | I32Op.Sub | I32Op.And | I32Op.Or | I32Op.Shl
                      | I32Op.Shr Pack.U)) -> []
  | _ -> ["instruction " ^ mnemonic e]

(* why a function is outside the subset *)
let func_why (m : module_) (f : func) =
  let Func (x, ls, body) = f.it in
  distinct
    ((if functype m x = None
      || not (List.for_all (fun (l : local) -> let Local t = l.it in is_i32 t) ls)
      then ["non-i32 values"] else [])
     @ instrs_why m body)

(* why an export is outside the subset *)
let export_why (m : module_) (e : export) =
  let Export (n, xx) = e.it in
  if not (is_ascii n) then ["non-ASCII names"] else
  match xx.it with
  | FuncX x -> func_why m (List.nth m.it.funcs (Int32.to_int x.it))
  | MemoryX _ -> []
  | TableX _ -> ["tables"]
  | GlobalX _ -> ["globals"]
  | TagX _ -> ["tags"]

(* a data segment's offset reads a global, so the module needs its globals *)
let reads_global (d : data) =
  match d.it with
  | Data (_, {it = Active (_, offset); _}) ->
    List.exists (fun (e : instr) -> match e.it with GlobalGet _ -> true | _ -> false) offset.it
  | _ -> false

let is_whole (m : module_) =
  m.it.imports <> [] || m.it.tags <> [] || m.it.start <> None || List.exists reads_global m.it.datas

let memory_type_why (mem : memory) =
  let Memory (MemoryT (at, lim)) = mem.it in
  (if at = I32AT then [] else ["64-bit memories"])
  @ (if lim.max = None then [] else ["a memory maximum"])

let data_why (d : data) =
  match d.it with
  | Data (_, {it = Active (x, {it = [{it = Const {it = Value.I32 _; _}; _}]; _}); _}) ->
    memory_why x
  | Data (_, {it = Active (x, _); _}) -> memory_why x @ ["data offsets other than i32.const"]
  | Data (_, {it = Passive | Declarative; _}) -> ["passive data segments"]

(* a type of the subset is a function type of i32 values, alone in its
   recursion group *)
let type_why (t : type_) =
  match t.it with
  | RecT [SubT (Final, [], FuncT (ins, outs))] ->
    if List.for_all is_i32 ins && List.for_all is_i32 outs then [] else ["non-i32 values"]
  | _ -> ["GC types"]

(* why a module is outside the subset *)
let module_why (m : module_) =
  let m' = m.it in
  let given b why = if b then [why] else [] in
  distinct
    (List.concat
       [ given (m'.imports <> []) "imports";
         given (m'.tags <> []) "tags";
         given (m'.start <> None) "a start function";
         given (m'.globals <> []) "globals";
         given (m'.tables <> [] || m'.elems <> []) "tables";
         given (List.length m'.memories > 1) "more than one memory";
         List.concat_map memory_type_why m'.memories;
         given (List.length m'.datas > 1) "more than one data segment";
         List.concat_map data_why m'.datas;
         List.concat_map type_why m'.types;
         given (List.exists (fun n -> not (is_ascii n)) (export_names m)) "non-ASCII names";
         List.concat_map (func_why m) m'.funcs ])

let index_of x xs =
  let rec go i = function [] -> None | y :: ys -> if y = x then Some i else go (i + 1) ys in
  go 0 xs

(* the indices of the types of the blocks of es *)
let rec block_types es =
  List.concat_map (fun (e : instr) ->
      match e.it with
      | Block (bt, es) | Loop (bt, es) ->
        (match bt with VarBlockType x -> [x] | ValBlockType _ -> []) @ block_types es
      | _ -> []) es

let cut (m : module_) : module_ =
  if is_whole m then m else
  let kept =
    List.filter (fun (_, f) -> func_why m f = []) (List.mapi (fun i f -> (i, f)) m.it.funcs) in
  let used = List.concat_map (fun (_, (f : func)) ->
      let Func (x, _, body) = f.it in x :: block_types body) kept in
  let tys = List.sort_uniq compare (List.filter_map (functype m) used) in
  let types = List.map (fun t -> RecT [SubT (Final, [], FuncT t)] @@ no_region) tys in
  let retype (x : idx) =
    Int32.of_int (Option.get (index_of (Option.get (functype m x)) tys)) @@ x.at in
  let rec reblock es = List.map (fun (e : instr) ->
      match e.it with
      | Block (bt, es) -> Block (reblocktype bt, reblock es) @@ e.at
      | Loop (bt, es) -> Loop (reblocktype bt, reblock es) @@ e.at
      | _ -> e) es
  and reblocktype = function VarBlockType x -> VarBlockType (retype x) | bt -> bt in
  let funcs = List.map (fun (_, (f : func)) ->
      let Func (x, ls, body) = f.it in
      Func (retype x, ls, reblock body) @@ f.at) kept in
  let exports = List.filter_map (fun (e : export) ->
      let Export (n, xx) = e.it in
      match xx.it, export_why m e with
      | FuncX x, [] ->
        Option.map (fun j -> Export (n, FuncX (Int32.of_int j @@ x.at) @@ xx.at) @@ e.at)
          (index_of (Int32.to_int x.it) (List.map fst kept))
      | MemoryX _, [] -> Some e
      | _ -> None) m.it.exports in
  {m with it = {m.it with types; funcs; exports; tables = []; elems = []; globals = []}}

(* each command, and the command that the binary script prints for it: each
   module cut, but the module of (assert_trap (module ...)) or
   (assert_unlinkable (module ...)), which the parser puts just before the
   assertion, stays whole: the assertion is about all of it *)
let rec commands = function
  | c :: ({it = Script.Assertion
              {it = Script.AssertUninstantiable _ | Script.AssertUnlinkable _; _}; _} as a) :: rest ->
    (c, c) :: (a, a) :: commands rest
  | ({it = Script.Module (x, {it = Script.Textual (m, _); at}); _} as c) :: rest ->
    (c, {c with it = Script.Module (x, {it = Script.Textual (cut m, []); at})}) :: commands rest
  | c :: rest -> (c, c) :: commands rest
  | [] -> []

(* an instruction that changes nothing in the instance: it writes no memory,
   table or global, drops no segment, and calls only functions i that are
   pure i, or through a table only when the functions that the table may hold
   are (indirect); any instruction not listed here counts as a change *)
let rec instrs_pure pure indirect es = List.for_all (instr_pure pure indirect) es

and instr_pure pure indirect (e : instr) =
  match e.it with
  | Block (_, es) | Loop (_, es) -> instrs_pure pure indirect es
  | If (_, es1, es2) -> instrs_pure pure indirect es1 && instrs_pure pure indirect es2
  | Call x | ReturnCall x -> pure (Int32.to_int x.it)
  | CallIndirect _ | ReturnCallIndirect _ -> indirect
  | Unreachable | Nop | Drop | Select _ | Br _ | BrIf _ | BrTable _ | BrOnNull _
  | BrOnNonNull _ | BrOnCast _ | BrOnCastFail _ | Return | LocalGet _ | LocalSet _
  | LocalTee _ | GlobalGet _ | TableGet _ | TableSize _ | Load _ | VecLoad _
  | VecLoadLane _ | MemorySize _ | RefNull _ | RefFunc _ | RefIsNull | RefAsNonNull
  | RefTest _ | RefCast _ | RefEq | RefI31 | I31Get _ | StructGet _ | ArrayGet _
  | ArrayLen | ExternConvert _ | Const _ | Test _ | Compare _ | Unary _ | Binary _
  | Convert _ | VecConst _ | VecTest _ | VecCompare _ | VecUnary _ | VecBinary _
  | VecTernary _ | VecConvert _ | VecShift _ | VecBitmask _ | VecTestBits _
  | VecUnaryBits _ | VecBinaryBits _ | VecTernaryBits _ | VecSplat _ | VecExtract _
  | VecReplace _ -> true
  | _ -> false

(* the functions whose references the module takes (ref.func, which element
   segments are made of too): only these can be in a table that the module
   does not export *)
let referenced (m : module_) =
  let rec refs es = List.concat_map (fun (e : instr) ->
      match e.it with
      | RefFunc x -> [Int32.to_int x.it]
      | Block (_, es) | Loop (_, es) | TryTable (_, _, es) -> refs es
      | If (_, es1, es2) -> refs es1 @ refs es2
      | _ -> []) es in
  let const (c : const) = refs c.it in
  List.concat
    [ List.concat_map (fun (f : func) -> let Func (_, _, body) = f.it in refs body) m.it.funcs;
      List.concat_map (fun (g : global) -> let Global (_, c) = g.it in const c) m.it.globals;
      List.concat_map (fun (t : table) -> let Table (_, c) = t.it in const c) m.it.tables;
      List.concat_map (fun (e : elem) ->
          let Elem (_, cs, mode) = e.it in
          List.concat_map const cs @ (match mode.it with Active (_, c) -> const c | _ -> []))
        m.it.elems ]

(* the exports of the functions of a module that change nothing in its
   instance: an action on one that the model does not run to its end leaves
   the instance as the script expects (WasmTests.lean). A function is pure
   when its body is, with the functions it calls; a module that stays whole
   has none, as its imports could do anything, and a call through a table
   that the module exports may call anything *)
let pure_exports (m : module_) : name list =
  if is_whole m then [] else
  let fs = Array.of_list m.it.funcs in
  let pure = Array.make (Array.length fs) true in
  let is_pure j = j < Array.length fs && pure.(j) in
  let exported_table = List.exists (fun (e : export) ->
      let Export (_, xx) = e.it in match xx.it with TableX _ -> true | _ -> false) m.it.exports in
  let refs = referenced m in
  let changed = ref true in
  while !changed do
    changed := false;
    let indirect = not exported_table && List.for_all is_pure refs in
    Array.iteri (fun i (f : func) ->
        let Func (_, _, body) = f.it in
        if pure.(i) && not (instrs_pure is_pure indirect body) then begin
          pure.(i) <- false;
          changed := true
        end) fs
  done;
  List.filter_map (fun (e : export) ->
      let Export (n, xx) = e.it in
      match xx.it with
      | FuncX x when pure.(Int32.to_int x.it) -> Some n
      | _ -> None) m.it.exports

(* why the sections of a module's bytes, which the syntax does not keep, are
   outside the subset: its sections are 1 type, 3 function, 5 memory, 7
   export, 10 code and 11 data, as the compiler writes them *)
let sections_why (bs : string) =
  let rec leb i shift v =
    if i >= String.length bs then None else
    let b = Char.code bs.[i] in
    let v = v lor ((b land 127) lsl shift) in
    if b < 128 then Some (v, i + 1) else leb (i + 1) (shift + 7) v in
  let rec go i =
    if i >= String.length bs then [] else
    match leb (i + 1) 0 0 with
    | None -> []
    | Some (size, j) ->
      (match Char.code bs.[i] with
       | 1 | 3 | 5 | 7 | 10 | 11 -> []
       | 0 -> ["custom sections"]
       | 2 -> ["imports"]
       | 4 | 9 -> ["tables"]
       | 6 -> ["globals"]
       | 8 -> ["a start function"]
       | 12 -> ["a data count section"]
       | 13 -> ["tags"]
       | _ -> ["sections of another kind"])
      @ go (j + size) in
  go 8

(* the module that a definition defines, and its bytes (in the binary script,
   for its own); None when it is malformed *)
let rec module_of (def : Script.definition) =
  try
    match def.it with
    | Script.Textual (m, cs) -> Some (m, lazy (Encode.encode_with_custom (m, cs)))
    | Script.Encoded (name, bs) -> Some (Decode.decode name bs.it, lazy bs.it)
    | Script.Quoted (_, s) -> module_of (snd (Parse.Module.parse_string ~offset:s.at s.it))
  with Decode.Code _ | Parse.Syntax _ -> None

(* a string of the binary script: each of its bytes escaped *)
let quoted (s : string) =
  "\"" ^ String.concat ""
    (List.map (fun c -> Printf.sprintf "\\%02x" (Char.code c)) (List.of_seq (String.to_seq s)))
  ^ "\""

(* a line of x.facts: its kind, the command's index, then the names (escaped)
   and the reasons (as they are: ASCII, with no quote or backslash) *)
let line oc kind i names whys =
  Printf.fprintf oc "(%s %d%s%s)\n" kind i
    (String.concat "" (List.map (fun n -> " " ^ quoted (Utf8.encode n)) names))
    (String.concat "" (List.map (fun w -> " \"" ^ w ^ "\"") whys))

(* the facts of the module of the command c, whose binary script defines the
   module of def as its i-th command *)
let facts oc i (c : Script.command) (def : Script.definition) =
  match c.it, module_of def with
  | Script.Module (_, orig), Some (m, bs) ->
    let why = distinct (sections_why (Lazy.force bs) @ module_why m) in
    if why <> [] then line oc "outside" i [] why;
    Option.iter (fun (m0, _) ->
        List.iter (fun (e : export) ->
            let Export (n, _) = e.it in
            if not (List.mem n (export_names m)) then
              line oc "cut" i [n] (export_why m0 e))
          m0.it.exports;
        line oc "pure" i (pure_exports m0) [])
      (module_of orig)
  | _ -> ()

(* the commands of the binary script for the command p: a module of the
   binary format with its own bytes, as wasm -d prints a module definition *)
let print (p : Script.command) =
  match p.it with
  | Script.Module (x, {it = Script.Encoded (_, bs); _}) ->
    let var = match x with
      | None -> ""
      | Some x when String.for_all (fun c -> Lib.Char.is_alphanum_ascii c || c = '_') x.it ->
        " $" ^ x.it
      | Some x -> " $" ^ Arrange.name (Utf8.decode x.it) in
    [Sexpr.Node ("module definition" ^ var ^ " binary", Arrange.break_bytes bs.it)]
  | _ -> Arrange.script `Binary [p]

let () =
  set_binary_mode_out stdout true;
  let scr = Parse.Script.parse_file Sys.argv.(1) in
  let oc = open_out_bin Sys.argv.(2) in
  let printed = List.map (fun (c, p) -> (c, p, print p)) (commands scr) in
  ignore (List.fold_left (fun i (c, (p : Script.command), ss) ->
      (match p.it, ss with
       | Script.Module (_, def), [_] -> facts oc i c def
       | _ -> ());
      i + List.length ss) 0 printed);
  close_out oc;
  List.iter (fun (_, _, ss) -> List.iter (Sexpr.output stdout 80) ss) printed
