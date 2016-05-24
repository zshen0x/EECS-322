open SExpr
open AST_l3
open FrontEndUtils

let parse_l3_v = function
  | Atom v when is_var v -> L3Var v
  | Atom l when is_label l -> L3Label l
  | Atom n when is_num n -> L3Num (Int64.of_string n)
  | _ -> failwith "l3c: parse_l3_v: not a valid l3 v expr"


let rec parse_l3_d = function
  | Expr [Atom op; lhs; rhs] when is_biop op ->
    let create_biop_d l r =
      let l = parse_l3_v l and r = parse_l3_v r in
      begin match op with
        | "+" -> L3Add (l, r)
        | "-" -> L3Sub (l, r)
        | "*" -> L3Mul (l, r)
        | "<" -> L3Less (l, r)
        | "<=" -> L3LessEq (l, r)
        | "=" -> L3Equal (l, r)
        | _ -> failwith "l3c: parse_l3_d: create_biop_d should never reach here"
      end
    in
    create_biop_d lhs rhs
  | Expr [Atom "number?"; v] ->
    L3NumberQo (parse_l3_v v)
  | Expr [Atom "a?"; v] ->
    L3AQo (parse_l3_v v)
  | Expr [Atom "new-array"; size; init] ->
    L3NewArray (parse_l3_v size, parse_l3_v init)
  | Expr (Atom "new-tuple" :: vals) ->
    L3NewTuple (List.map parse_l3_v vals)
  | Expr [Atom "aref"; arr; pos] ->
    L3Aref (parse_l3_v arr, parse_l3_v pos)
  | Expr [Atom "aset"; arr; pos; v] ->
    L3Aset (parse_l3_v arr, parse_l3_v pos, parse_l3_v v)
  | Expr [Atom "alen"; arr] ->
    L3Alen (parse_l3_v arr)
  | Expr [Atom "read"] -> L3Read
  | Expr [Atom "print"; v] ->
    L3Print (parse_l3_v v)
  | Expr [Atom "make-closure"; Atom labl; v] when is_label labl ->
    L3MakeClosure (labl, parse_l3_v v)
  | Expr [Atom "closure-proc"; v] ->
    L3ClosureProc (parse_l3_v v)
  | Expr [Atom "closure-vars"; v] ->
    L3ClosureVars (parse_l3_v v)
  | Expr (f :: args_sexpr) ->
    (* all other case will fall into function but may fail when it is not valid function *)
    L3App (parse_l3_v f, (List.map parse_l3_v args_sexpr))
  | Atom _ as v -> L3V (parse_l3_v v)
  | _ -> failwith "l3c: parse_l3_d: not a valid l3 e"


let rec parse_l3_e = function
  | Expr [Atom "let"; Expr [Expr [Atom var; d]]; e] when is_var var ->
    L3Let ((var, parse_l3_d d), parse_l3_e e)
  | Expr [Atom "if"; test; thn; ele] ->
    L3If (parse_l3_v test, parse_l3_e thn, parse_l3_e ele )
  | d -> L3D (parse_l3_d d)


let parse_l3_function = function
  (* minimal sanity check *)
  | Expr [Atom labl ; Expr vars; e] when is_label labl ->
    L3Fun (labl,
           List.map
             (function
               | Atom v when is_var v -> v
               | _ -> failwith "l3c: parse_l3_function: invalid arguments ") vars,
           parse_l3_e e)
  | _ -> failwith "l3c: parse_l3_function: not a valid l3 function"


let parse_l3_program = function
  | Expr (e :: flst) ->
    L3Prog (parse_l3_e e, (List.map parse_l3_function flst))
  | _ -> failwith "l3: parse_l3_prog: not a valid l3 program"
