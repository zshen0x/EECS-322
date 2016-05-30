

let is_biop = function
    "+" | "-" | "*" | "<" | "<=" | "=" -> true
  | _ -> false

let is_pred = function
    "number?" | "a?" -> true
  | _ -> false

let is_prim = function
  "read" | "print" | "new-array" | "aref" | "aset" | "alen" -> true
  | p -> is_biop p || is_pred p

let is_num s =
  try ignore(Int64.of_string s); true with Failure _ -> false;;

let is_label s =
  let r = Str.regexp "^:[a-zA-Z_][a-zA-Z_0-9]*$" in
  Str.string_match r s 0

let is_var s =
  let r = Str.regexp "^[a-zA-Z_][a-zA-Z_0-9-]*$" in
  Str.string_match r s 0

let args = ["rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9"]

let get_unique_str_generator prefix =
  let var_cnt = ref 0 in
  fun () ->
    let l3_var = prefix ^ string_of_int !var_cnt in
    begin
      incr var_cnt;
      l3_var
    end
