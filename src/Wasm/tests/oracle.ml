(* Oracle
   ======

   oracle.exe < paths: what the spec's reference interpreter gives for the
   commands of each script whose path is a line of the input, whose modules
   are of the binary format and whose actions invoke exports with i32
   arguments (differential.ts writes them). For each script it prints a line
   "script x.wast", then a line for each command, in order:
     (module ...)        valid, invalid or malformed
     (module instance)   instance, or trap when it traps (the parser makes
                         this command of each (module ...))
     (invoke ...)        values v ... (each a 32-bit hex number), or trap
   A command on no module gives none. It uses the spec's own decoder,
   validator and evaluator (spec.ts builds it with them). *)

open Source

let hex (v : Value.value) =
  match v with
  | Value.Num (Value.I32 n) -> Printf.sprintf "%lx" n
  | _ -> "?"

let run (path : string) =
  Printf.printf "script %s\n" path;
  let defined = ref None in
  let instance = ref None in
  List.iter (fun (c : Script.command) ->
      match c.it with
      | Script.Module (_, {it = Script.Encoded (name, bs); _}) ->
        instance := None;
        (match Decode.decode name bs.it with
         | exception Decode.Code _ -> defined := None; print_endline "malformed"
         | m ->
           match Valid.check_module m with
           | exception Valid.Invalid _ -> defined := None; print_endline "invalid"
           | _ -> defined := Some m; print_endline "valid")
      | Script.Instance _ ->
        (match Option.map (fun m -> Eval.init m []) !defined with
         | exception Eval.Trap _ -> instance := None; print_endline "trap"
         | None -> instance := None; print_endline "none"
         | i -> instance := i; print_endline "instance")
      | Script.Action {it = Script.Invoke (_, name, lits); _} ->
        let args = List.map (fun (l : Script.literal) ->
            match l.it with Script.ValLit v -> v | Script.NullLit _ -> failwith "null") lits in
        (match Option.bind !instance (fun i -> Instance.export i name) with
         | Some (Instance.ExternFunc f) ->
           (match Eval.invoke f args with
            | exception Eval.Trap _ -> print_endline "trap"
            | vs -> print_endline (String.concat " " ("values" :: List.map hex vs)))
         | _ -> print_endline "none")
      | _ -> print_endline "other") (Parse.Script.parse_file path)

let () =
  set_binary_mode_out stdout true;
  In_channel.fold_lines (fun () path -> if path <> "" then run path) () stdin
