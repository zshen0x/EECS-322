open SExpr
open AST_l3

let fmt_l3_v = function
  | L3Var v -> Atom v
  | L3Label l -> Atom l
  | L3Num n -> Atom (Int64.to_string n)

let fmt_l3_d d =
  let fmt_d_help op operands =
    Expr (op :: List.map fmt_l3_v operands)
  in
  match d with
  | L3Add (lhs, rhs) -> fmt_d_help (Atom "+") [lhs; rhs]
  | L3Sub (lhs, rhs) -> fmt_d_help (Atom "-") [lhs; rhs]
  | L3Mul (lhs, rhs) -> fmt_d_help (Atom "*") [lhs; rhs]
  | L3Less (lhs, rhs) -> fmt_d_help (Atom "<") [lhs; rhs]
  | L3LessEq (lhs, rhs) -> fmt_d_help (Atom "<=") [lhs; rhs]
  | L3Equal (lhs, rhs) -> fmt_d_help (Atom "=") [lhs; rhs]
  | L3NumberQo any_v -> fmt_d_help (Atom "number?") [any_v]
  | L3AQo any_v -> fmt_d_help (Atom "a?") [any_v]
  | L3App (f_v, args) -> fmt_d_help (fmt_l3_v f_v) args
  | L3NewArray (lhs, rhs) -> fmt_d_help (Atom "new-array") [lhs; rhs]
  | L3NewTuple (vals) -> fmt_d_help (Atom "new-tuple") vals
  | L3Aref (lhs, rhs) -> fmt_d_help (Atom "aref") [lhs; rhs]
  | L3Aset (fst, snd, thd) -> fmt_d_help (Atom "aset") [fst; snd; thd]
  | L3Alen (arr_v) -> fmt_d_help (Atom "alen") [arr_v]
  | L3MakeClosure (labl, v) -> fmt_d_help (Atom "make-closure") [L3Label labl; v]
  | L3ClosureProc v -> fmt_d_help (Atom "closure-proc") [v]
  | L3ClosureVars v -> fmt_d_help (Atom "closure-vars") [v]
  | L3Print v -> fmt_d_help (Atom "print") [v]
  | L3Read -> Expr [Atom "read"]
  | L3V v -> fmt_l3_v v

let rec fmt_l3_e = function
  | L3Let ((var, d), e) ->
    Expr [Atom "let"; Expr [Expr [Atom var; fmt_l3_d d]]; fmt_l3_e e]
  | L3If (cond, thn, els) ->
    Expr [Atom "if"; fmt_l3_v cond; fmt_l3_e thn; fmt_l3_e els]
  | L3D d ->
    fmt_l3_d d

let fmt_l3_f = function
  | L3Fun (l, vars, body_e) ->
    let fmt_vars vars = Expr (List.map (fun v -> Atom v) vars) in
    Expr [Atom l; fmt_vars vars; fmt_l3_e body_e]

let fmt_l3_p = function
  | L3Prog (prog_e, fundefs) ->
    Expr ((fmt_l3_e prog_e) :: (List.map fmt_l3_f fundefs))

