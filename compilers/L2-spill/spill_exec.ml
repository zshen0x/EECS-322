open SExpr
open Spill

let () =
  let func = read_line () in
  let var = read_line () in
  let prefix = read_line () in
  match parse_string func with
  | [func_lst] -> print_sexpr [spill func_lst var prefix]
  | _ -> failwith "spill_reader: error: not a valid "
