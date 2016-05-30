open SExpr
open AST_l5
open FrontEndUtils


(* basic grammar check and parsing here *)

let parse_l5_prim = function
  | "+" -> Add
  | "-" -> Sub
  | "*" -> Mul
  | "<" -> Less
  | "<=" -> LessEq
  | "=" -> Equal
  | "number?" -> NumberQo
  | "a?" -> AQo
  | "print" -> Print
  | "read" -> Read
  | "new-array" -> NewArray
  | "aref" -> Aref
  | "aset" -> Aset
  | "alen" -> Alen
  | _ as p -> invalid_arg ("l5c: parse prim: not a prim " ^ p)

let rec parse_l5_e = function
  | Atom p when is_prim p -> Prim (parse_l5_prim p)
  | Atom v when is_var v -> X v
  | Atom n when is_num n -> Num (Int64.of_string n)
  | Expr [Atom "lambda"; Expr vars; e] ->
    Fn ((List.map get_var vars), parse_l5_e e)
  | Expr [Atom "let"; Expr [Expr [x; e1]]; e2] ->
    Let ((get_var x, parse_l5_e e1), parse_l5_e e2)
  | Expr [Atom "letrec"; Expr [Expr [x; e1]]; e2] ->
    LetRec ((get_var x, parse_l5_e e1), parse_l5_e e2)
  | Expr [Atom "if"; e1; e2; e3] ->
    If (parse_l5_e e1, parse_l5_e e2, parse_l5_e e3)
  | Expr (Atom "new-tuple" :: args) ->
    NewTuple (List.map parse_l5_e args)
  | Expr [Atom "begin"; e1; e2] ->
    Begin (parse_l5_e e1, parse_l5_e e2)
  | Expr (f :: args) ->
    App (parse_l5_e f, List.map parse_l5_e args)
  | _ -> failwith "l5c: not a valid l5 programe"
and get_var = function
  | Atom v when is_var v -> v
  | _ -> failwith "l5c: expected to be a variable"
