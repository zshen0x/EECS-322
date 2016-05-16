
type v = Var of string | Label of string | Num of int64

type d = Add of v * v
       | Sub of v * v
       | Mul of v * v
       | Less of v * v
       | LessEq of v * v
       | Equal of v * v
       | NumberQo of v
       | AQo of v
       | App of v * v list
       | NewArray of v * v
       | NewTuple of v list
       | Aref of v * v
       | Aset of v * v * v
       | Alen of v
       | Print of v
       | V of v
       | Read

type e = Let of (v * d) * e
       | If of v * e * e
       | D of d

type f = Fun of v * v list * e

type p = Prog of e * f list
