open SExpr
open L2c

let () =
  match Sys.argv with
  | [|_; filename|] ->
    let print_result = function
      | Some l2_prog -> SExpr.print_sexpr_indent [l2_prog]
      | None -> print_endline "\"could not register allocate\""
    in
    List.iter (fun p -> print_result @@ compile_l2_prog p) (parse_file filename)
  | _ -> ()
