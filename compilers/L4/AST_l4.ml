
type e = L4Var of string
       | L4Label of string
       | L4Num of int64
       | L4Let of (string * e) * e
       | L4If of e * e * e
       | L4Add of e * e
       | L4Sub of e * e
       | L4Mul of e * e
       | L4Less of e * e
       | L4LessEq of e * e
       | L4Equal of e * e
       | L4NumberQo of e
       | L4AQo of e
       | L4App of e * e list
       | L4NewArray of e * e
       | L4NewTuple of e list
       | L4Aref of e * e
       | L4Aset of e * e * e
       | L4Alen of e
       | L4Begin of e * e
       | L4MakeClosure of string * e
       | L4ClosureProc of e
       | L4ClosureVars of e
       | L4Print of e
       | L4Read

type f = L4Fun of string * string list * e

type p = L4Prog of e * f list
