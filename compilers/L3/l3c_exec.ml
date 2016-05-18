open SExpr
open L3c
open Parser_l3

let () =
  match Sys.argv with
  | [|_; filename|] ->
    let simple_compiler filename =
      let parse_and_complie p = compile_l3_p (parse_l3_program p) in
      let progs = List.map parse_and_complie (parse_file filename) in
      SExpr.print_sexpr_indent progs
    in
    simple_compiler filename
  | _ -> ()
