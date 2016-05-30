open SExpr
open Parser_l5
open L5c
open Fmt_l4


let () =
  match Sys.argv with
  | [|_; filename|] ->
    let l5_compiler filename =
      let parse_and_complie p = fmt_l4_p @@ compile_l5 @@ parse_l5_e p in
      let progs = List.map parse_and_complie (parse_file filename) in
      print_sexpr_indent progs
    in
    l5_compiler filename
  | _ -> ()


