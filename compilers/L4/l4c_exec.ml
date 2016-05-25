open SExpr
open Parser_l4
open Fmt_l3
open L4c

let () =
  match Sys.argv with
  | [|_; filename|] ->
    let simple_compiler filename =
      let parse_and_complie p = fmt_l3_p @@ compile_l4_p @@ parse_l4_p p in
      let progs = List.map parse_and_complie (parse_file filename) in
      print_sexpr_indent progs
    in
    simple_compiler filename
  | _ -> ()
