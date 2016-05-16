open Parser_l3
open AST_l3
open SExpr

let parser_test () =
  let test_parse_prog () =
    let f str = List.map parse_l3_program (parse_string str) in
    let prog0 = "((:fib 18)
                 (:fib (x)
                 (let ([xlt2 (< x 2)])
                 (if xlt2
                     1
                     0))))"
    and prog0_exp = [Prog ((D (App (Label ":fib", [Num (Int64.of_int 18)]))),
                           [Fun (Label ":fib", [Var "x"],
                                 Let ((Var "xlt2", Less (Var "x", Num (Int64.of_int 2))),
                                     If (Var "xlt2", D (V (Num Int64.one)), D (V (Num Int64.zero)))))])]
    in
    assert ((f prog0) = prog0_exp)
  in
  let test_parse_l3_v () =
    let f = function
      | Expr lst ->
        List.map parse_l3_v lst
      | _ -> failwith "test fails"
    in
    let ff str = List.map f (parse_string str) in
    let v0 = "(8 sksk rsp rax :facebook :l 233405233432)"
    and v0_exp = [[Num (Int64.of_int 8); Var "sksk"; Var "rsp"; Var "rax";
                  Label ":facebook"; Label ":l";
                  Num (Int64.of_string "233405233432")]]
    in
    assert ((ff v0) = v0_exp);
    print_endline "pass parse_l3_v test !"
  in
  let test_parse_l3_d () =
    let f = function
      | Expr lst ->
        List.map parse_l3_d lst
      | _ -> failwith "test fails"
    in
    let ff str = List.map f (parse_string str) in
    let d0 = "((+ 1 2) (- s k) (number? k) (a? arr) (:fib a b) \
              (new-array s v) (new-tuple k d j) (aref 123456 var)\
              (aset k k k) (read) (print sklkk) 10)"
    and d0_exp = [[Add (Num (Int64.of_string "1"), Num (Int64.of_string "2"));
                   Sub (Var "s", Var "k"); NumberQo (Var "k"); AQo (Var "arr");
                   App (Label ":fib", [Var "a"; Var "b"]); NewArray (Var "s", Var "v");
                   NewTuple [Var "k"; Var "d"; Var "j"]; Aref (Num (Int64.of_string "123456"), Var "var");
                   Aset (Var "k", Var "k", Var "k"); Read; Print (Var "sklkk"); V (Num (Int64.of_int 10))]]
    and d1 = "((make-closure :sdf fs) (closure-proc myvar) (closure-vars 3423))"
    and d1_exp = [[NewTuple [Label ":sdf"; Var "fs"]; Aref (Var "myvar", Num Int64.zero);
                   Aref (Num (Int64.of_string "3423"), Num Int64.one)]]
    in
    assert ((ff d0) = d0_exp);
    assert ((ff d1) = d1_exp);
    print_endline "pass parse_l3_d tests !"
  in
  let test_parse_l3_e () =
    let f = function
      | Expr lst ->
        List.map parse_l3_e lst
      | _ -> failwith "test_parse_l3_e: test fails"
    in
    let ff str = List.map f (parse_string str) in
    let e0 = "((let ([myvar (+ 1 0)])\
                (+ myvar myvar))\
               (if s s (if s s s))\
              ok)"
    and e0_exp = [[Let ((Var "myvar", Add (Num Int64.one, Num Int64.zero)), (D (Add (Var "myvar", Var "myvar"))));
                   If (Var "s", D (V (Var "s")), If (Var "s", D (V (Var "s")), D (V (Var "s")))); D (V (Var "ok"))]]
    in
    assert ((ff e0) = e0_exp);
    print_endline "pass parse_l3_e tests !"
  in
  test_parse_l3_v ();
  test_parse_l3_d ();
  test_parse_l3_e ();
  test_parse_prog ();
  print_endline "all parser test passed !"

let () =
  parser_test ()
