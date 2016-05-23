open AST_l3
open AST_l4
open L4c

let test_compile_l4_e () =
  let l4_e0 = L4Var "myVar"
  and l4_e1 = L4Label ":main"
  and l4_e2 = L4Add (L4Var "myVar", L4Var "myVar")
  and l4_e3 = L4NumberQo (L4Num Int64.zero)
  and l4_e4 = L4Aset (L4Label ":go", L4Num Int64.one, L4Var "tmp")
  and l4_e5 = L4If (L4Read, L4Num Int64.zero, L4Num Int64.one)
  and l4_e6 = L4Begin (L4Read, L4Print (L4Num Int64.one))
  and l4_e7 = L4Let (("myVar", L4Num Int64.zero),
                     L4Add (L4Var "myVar", L4Var "myVar"))
  and l4_e8 = L4Let (("myVar", L4Num Int64.zero),
                     L4Num Int64.zero)
  and l4_e9 = L4Begin (L4Num Int64.zero, L4Num Int64.one)
  and l4_e10 = L4Let (("tmp", L4Num Int64.zero), L4Print (L4Num Int64.one))
  in
  begin
    assert (compile_l4_e l4_e0 = L3D (L3V (L3Var "l4_myVar")));
    assert (compile_l4_e l4_e1 = L3D (L3V (L3Label ":main")));
    assert (compile_l4_e l4_e2 = L3D (L3Add (L3Var "l4_myVar", L3Var "l4_myVar")));
    assert (compile_l4_e l4_e3 = L3D (L3NumberQo (L3Num Int64.zero))); 
    assert (compile_l4_e l4_e4 = L3D (L3Aset (L3Label ":go", L3Num Int64.one, L3Var "l4_tmp")));
    assert (compile_l4_e l4_e5 = L3Let (("l3_var0", L3Read),
                                        L3If (L3Var "l3_var0",
                                              L3D (L3V (L3Num Int64.zero)),
                                              L3D (L3V (L3Num Int64.one)))));
    assert (compile_l4_e l4_e6 = L3Let (("l3_var0", L3Read),
                                        L3D (L3Print (L3Num Int64.one))));
    assert (compile_l4_e l4_e7 = L3Let (("l4_myVar", L3V (L3Num (Int64.zero))),
                                        L3D (L3Add (L3Var "l4_myVar", L3Var "l4_myVar"))));
    assert (compile_l4_e l4_e8 = L3Let (("l4_myVar", L3V (L3Num Int64.zero)),
                                        L3D (L3V (L3Num Int64.zero))));
    assert (compile_l4_e l4_e9 = L3Let (("l3_var0", L3V (L3Num Int64.zero)),
                                        L3D (L3V (L3Num Int64.one))));
    assert (compile_l4_e l4_e10 = L3Let (("l4_tmp", L3V (L3Num Int64.zero)),
                                         L3D (L3Print (L3Num Int64.one))));
    print_endline "pass compile_l4_e tests"
  end


let run_tests () =
  begin
    test_compile_l4_e ();
  end

let () =
  run_tests ()
