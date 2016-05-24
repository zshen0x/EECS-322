open SExpr
open AST_l4
open FrontEndUtils

let rec parse_l4_e = function
  | Atom var when is_var var -> L4Var var
  | Atom labl when is_label labl -> L4Label labl
  | Atom num when is_num num -> L4Num (Int64.of_string num)
  | Expr [Atom "let"; Expr [Expr [Atom var; e1]]; e2] ->
    L4Let ((var, parse_l4_e e1), parse_l4_e e2)
  | Expr [Atom "if"; e1; e2; e3] ->
    L4If (parse_l4_e e1, parse_l4_e e2, parse_l4_e e3)
  | Expr [Atom "+"; lhs; rhs] ->
    L4Add (parse_l4_e lhs, parse_l4_e rhs)
  | Expr [Atom "-"; lhs; rhs] ->
    L4Sub (parse_l4_e lhs, parse_l4_e rhs)
  | Expr [Atom "*"; lhs; rhs] ->
    L4Mul (parse_l4_e lhs, parse_l4_e rhs)
  | Expr [Atom "<"; lhs; rhs] ->
    L4Less (parse_l4_e lhs, parse_l4_e rhs)
  | Expr [Atom "<="; lhs; rhs] ->
    L4LessEq (parse_l4_e lhs, parse_l4_e rhs) 
  | Expr [Atom "="; lhs; rhs] ->
    L4Equal (parse_l4_e lhs, parse_l4_e rhs)
  | Expr [Atom "number?"; any] ->
    L4NumberQo (parse_l4_e any)
  | Expr [Atom "a?"; any] ->
    L4AQo (parse_l4_e any)
  | Expr [Atom "new-array"; lhs; rhs] ->
    L4NewArray (parse_l4_e lhs, parse_l4_e rhs)
  | Expr (Atom "new-tuple":: vals) ->
    L4NewTuple (List.map parse_l4_e vals)
  | Expr [Atom "aref"; lhs; rhs] ->
    L4Aref (parse_l4_e lhs, parse_l4_e rhs) 
  | Expr [Atom "aset"; fst; snd; thd] ->
                  L4Aset (parse_l4_e fst, parse_l4_e snd, parse_l4_e thd)
  | Expr [Atom "alen"; arr] ->
    L4Alen (parse_l4_e arr)
  | Expr [Atom "begin"; fst; snd] ->
    L4Begin (parse_l4_e fst, parse_l4_e snd)
  | Expr [Atom "read"] ->
    L4Read
  | Expr [Atom "print"; e] ->
    L4Print (parse_l4_e e)
  | Expr [Atom "make-closure"; Atom labl; e] ->
    L4MakeClosure (labl, parse_l4_e e)
  | Expr [Atom "closure-proc"; e] ->
    L4ClosureProc (parse_l4_e e)
  | Expr [Atom "closure-vars"; e] ->
    L4ClosureVars (parse_l4_e e)
  | Expr (f :: args) ->
    L4App (parse_l4_e f, List.map parse_l4_e args)
  | _ -> failwith "l4c: parse_l4_e not a valid l4 e"

let parse_l4_f = function
  | Expr [Atom labl; Expr vars; e] when is_label labl ->
    L4Fun (labl,
           List.map
             (function
               | Atom v when is_var v -> v
               | _ -> failwith "l4c: parse_l3_f: not a valid l4 function ") vars,
           parse_l4_e e)
  | _ -> failwith "l4c: parse_l4_f: not a valid l4 function"

let parse_l4_p = function
  | Expr (e :: fundefs) ->
    L4Prog (parse_l4_e e, List.map parse_l4_f fundefs)
  | _ -> failwith "l4c: parse_l4_prog: not a valid l4 program"
