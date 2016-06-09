open SExpr
open Parser_l5
open Fmt_l3
open L5c
open L4c
open L3c
open L2c
open L1c


let () =
  match Sys.argv with
  | [|_; filename|] ->
    let lc_compiler filename =
      let compile_chain p =
        L1c.compile_l1_prog @@
        L2c.compile_l2 @@
        L3c.compile_l3_p @@
        L4c.compile_l4_p @@
        L5c.compile_l5 @@
        parse_l5_e p in
      let asm = List.map compile_chain (parse_file filename) in
      (* print_sexpr_indent asm *)
      match asm with
      | hd :: [] -> output_file hd "prog.S"
      | _ -> failwith "lc: wrong program: too many"
    in
    lc_compiler filename
  | _ -> ()
