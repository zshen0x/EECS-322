
let is_num s =
  try ignore(Int64.of_string s); true with Failure _ -> false;;

let is_biop = function
    "+" | "-" | "*" | "<" | "<=" | "=" -> true
  | _ -> false

let is_pred = function
    "number?" | "a" -> true
  | _ -> false

let is_label s =
  let r = Str.regexp "^:[a-zA-Z_][a-zA-Z_0-9]*$" in
  Str.string_match r s 0

let is_var s =
  let r = Str.regexp "^[a-zA-Z_][a-zA-Z_0-9-]*$" in
  Str.string_match r s 0

let args = ["rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9"]
