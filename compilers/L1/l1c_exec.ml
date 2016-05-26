open SExpr
open L1c

let () =
  let len = Array.length Sys.argv in
  match len with
  | 2 -> output_file (compile (parse_file Sys.argv.(1))) "prog.S"
  | _ -> ()
