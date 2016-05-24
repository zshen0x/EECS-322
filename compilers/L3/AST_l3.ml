
type v = L3Var of string | L3Label of string | L3Num of int64

type d = L3Add of v * v
       | L3Sub of v * v
       | L3Mul of v * v
       | L3Less of v * v
       | L3LessEq of v * v
       | L3Equal of v * v
       | L3NumberQo of v
       | L3AQo of v
       | L3App of v * v list
       | L3NewArray of v * v
       | L3NewTuple of v list
       | L3Aref of v * v
       | L3Aset of v * v * v
       | L3Alen of v
       | L3MakeClosure of string * v
       | L3ClosureProc of v
       | L3ClosureVars of v
       | L3Print of v
       | L3V of v
       | L3Read

type e = L3Let of (string * d) * e
       | L3If of v * e * e
       | L3D of d

type f = L3Fun of string * string list * e

type p = L3Prog of e * f list
