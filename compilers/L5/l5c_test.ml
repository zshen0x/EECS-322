open SExpr
open Parser_l5
open AST_l5

let run_parser_tests () =
  let t0 = Atom "+"
  and t1 = Atom "-"
      and t2 = Expr [Atom "lambda"; Expr [Atom "x"; Atom "y"; Atom "z"]; Expr [Atom "new-tuple"; Atom "x"; Atom "y"; Atom "z"]]
  in
  begin
    assert (parse_l5_e t0 = Prim Add);
    assert (parse_l5_e t1 = Prim Sub);
    assert (parse_l5_e t2 = Fn (["x"; "y"; "z"], NewTuple [X "x"; X "y"; X "z"]));
    print_endline "pass parser tests!"
  end


let run_tests () =
  begin
    run_parser_tests ()
  end


let () =
  run_tests ()
