open SExpr
open AST_l4

let rec fmt_l4_e = function
  | L4Var v -> Atom v
  | L4Label l -> Atom l
  | L4Num n -> Atom (Int64.to_string n)
  | L4Let ((var, e1), e2) ->
    Expr [Atom "let"; Expr [Expr[Atom var; fmt_l4_e e1]]; fmt_l4_e e2]
  | L4If (e1, e2, e3) ->
    Expr [Atom "if"; fmt_l4_e e1; fmt_l4_e e2; fmt_l4_e e3]
  | L4Add (e1, e2) ->
    Expr [Atom "+"; fmt_l4_e e1; fmt_l4_e e2] 
  | L4Sub (e1, e2) ->
    Expr [Atom "-"; fmt_l4_e e1; fmt_l4_e e2]
  | L4Mul (e1, e2) ->
    Expr [Atom "*"; fmt_l4_e e1; fmt_l4_e e2]
  | L4Less (e1, e2) ->
    Expr [Atom "<"; fmt_l4_e e1; fmt_l4_e e2]
  | L4LessEq (e1, e2) ->
    Expr [Atom "<="; fmt_l4_e e1; fmt_l4_e e2]
  | L4Equal (e1, e2) ->
    Expr [Atom "="; fmt_l4_e e1; fmt_l4_e e2]
  | L4NumberQo e ->
    Expr [Atom "number?"; fmt_l4_e e]
  | L4AQo e ->
    Expr [Atom "a?"; fmt_l4_e e]
  | L4App (f, args_e) ->
    Expr (fmt_l4_e f :: (List.map fmt_l4_e args_e))
  | L4NewArray (e1, e2) ->
    Expr [Atom "new-array"; fmt_l4_e e1; fmt_l4_e e2]
  | L4NewTuple es ->
    Expr (Atom "new-tuple" :: (List.map fmt_l4_e es))
  | L4Aref (e1, e2) ->
    Expr [Atom "aref"; fmt_l4_e e1; fmt_l4_e e2]
  | L4Aset (e1, e2, e3) ->
    Expr [Atom "aset"; fmt_l4_e e1; fmt_l4_e e2; fmt_l4_e e3]
  | L4Alen e ->
    Expr [Atom "alen"; fmt_l4_e e]
  | L4Begin (e1, e2) ->
    Expr [Atom "begin"; fmt_l4_e e1; fmt_l4_e e2]
  | L4MakeClosure (labl, e) ->
    Expr [Atom "make-closure"; Atom labl; fmt_l4_e e]
  | L4ClosureProc e ->
    Expr [Atom "closure-proc"; fmt_l4_e e]
  | L4ClosureVars e ->
    Expr [Atom "closure-vars"; fmt_l4_e e]
  | L4Print e ->
    Expr [Atom "print"; fmt_l4_e e]
  | L4Read ->
    Expr [Atom "read"]

let fmt_l4_f = function
  | L4Fun (labl, args, e) ->
    Expr [Atom labl;
          Expr (List.map (fun arg -> Atom arg) args);
          fmt_l4_e e]

let fmt_l4_p = function
  | L4Prog (e, fundefs) ->
    Expr (fmt_l4_e e :: (List.map fmt_l4_f fundefs))
