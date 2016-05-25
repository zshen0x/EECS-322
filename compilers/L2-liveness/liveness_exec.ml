open SExpr
open Liveness

let () =
  let iteration f = print_two_sests (liveness_analysis f) "in" "out" in
  match Sys.argv with
  | [|_; filename|] ->
    List.iter iteration (parse_file filename)
  | _ ->
    let func = read_line () in
    List.iter iteration (parse_string func)
