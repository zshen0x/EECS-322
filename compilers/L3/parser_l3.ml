open SExpr
open AST_l3
open Utils_l3

let parse_l3_v = function
  | Atom v when is_var v -> Var v
  | Atom l when is_label l -> Label l
  | Atom n when is_num n -> Num (Int64.of_string n)
  | _ -> failwith "l3c: parse_l3_v: not a valid l3 v expr"


let rec parse_l3_d = function
  | Expr [Atom op; lhs; rhs] when is_biop op ->
    let create_biop_d l r =
      let l = parse_l3_v l and r = parse_l3_v r in
      begin match op with
        | "+" -> Add (l, r)
        | "-" -> Sub (l, r)
        | "*" -> Mul (l, r)
        | "<" -> Less (l, r)
        | "<=" -> LessEq (l, r)
        | "=" -> Equal (l, r)
        | _ -> failwith "l3c: parse_l3_d: create_biop_d should never reach here"
      end
    in
    create_biop_d lhs rhs
  | Expr [Atom "number?"; v] ->
    NumberQo (parse_l3_v v)
  | Expr [Atom "a?"; v] ->
    AQo (parse_l3_v v)
  | Expr [Atom "new-array"; size; init] ->
    NewArray (parse_l3_v size, parse_l3_v init)
  | Expr (Atom "new-tuple" :: initials) ->
    NewTuple (List.map parse_l3_v initials)
  | Expr [Atom "aref"; arr; pos] ->
    Aref (parse_l3_v arr, parse_l3_v pos)
  | Expr [Atom "aset"; arr; pos; v] ->
    Aset (parse_l3_v arr, parse_l3_v pos, parse_l3_v v)
  | Expr [Atom "alen"; arr] ->
    Alen (parse_l3_v arr)
  | Expr [Atom "read"] -> Read
  | Expr [Atom "print"; v] ->
    Print (parse_l3_v v)
  | Expr [Atom "make-closure"; Atom l as labl; v] when is_label l ->
    parse_l3_d (Expr [Atom "new-tuple"; labl; v])
  | Expr [Atom "closure-proc"; v] ->
    parse_l3_d (Expr [Atom "aref"; v; Atom "0"])
  | Expr [Atom "closure-vars"; v] ->
    parse_l3_d (Expr [Atom "aref"; v; Atom "1"])
  | Expr vlst ->
    (* all other case will fall into function but may fail when it is not valid function *)
    App (List.map parse_l3_v vlst)
  | Atom _ as v-> V (parse_l3_v v)
(* | _ -> failwith "l3c: parse_l3_d: not a valid l3 e " *)


let rec parse_l3_e = function
  | Expr [Atom "let"; Expr [Expr [var; d]]; e] ->
    Let ((parse_l3_v var, parse_l3_d d), parse_l3_e e)
  | Expr [Atom "if"; test; thn; ele] ->
    If (parse_l3_v test, parse_l3_e thn, parse_l3_e ele )
  | d -> D (parse_l3_d d)


let parse_l3_function = function
  (* minimal sanity check *)
  | Expr [Atom l as labl; Expr vars; e] when is_label l ->
    Fun (parse_l3_v labl, (List.map parse_l3_v vars), parse_l3_e e)
  | _ -> failwith "l3c: parse_l3_function: not a valid l3 function"


let parse_l3_program = function
  | Expr (e :: flst) ->
    Prog (parse_l3_e e, (List.map parse_l3_function flst))
  | _ -> failwith "l3: parse_l3_prog: not a valid l3 program"
