

(*
e ::= (lambda (x ...) e)
    | x
    | (let ([x e]) e)
    | (letrec ([x e]) e)
    | (if e e e)
    | (new-tuple e ...)
    | (begin e e)
    | (e e ...) ;; application expression
    | prim
    | num

prim ::= biop
       | pred
       | read
       | print
       | new-array
       | aref
       | aset
       | alen

biop ::= + | - | * | < | <= | =
pred ::= number? | a?

*)

type prim = Add | Sub | Mul | Less | LessEq | Equal | NumberQo | AQo | Print | Read | NewArray | Aref | Aset | Alen

type e = Fn of string list * e
       | X of string
       | Num of int64
       | Let of (string * e) * e
       | LetRec of (string * e) * e
       | If of e * e * e
       | NewTuple of e list
       | Begin of e * e
       | App of e * e list
       | Prim of prim

