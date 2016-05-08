

let compose f g x = f (g x)

let is_integer s =
  try ignore(Int64.of_string s); true with Failure _ -> false;;

let is_aop = function
    "+=" | "-=" | "*=" | "&=" -> true
  | _ -> false

let is_sop = function
    "<<=" | ">>=" -> true
  | _ -> false

let is_cmp = function
    "<" | "<=" |"=" -> true
  | _ -> false

let is_label s =
  let r = Str.regexp "^:[a-zA-Z_][a-zA-Z_0-9]*$" in
  Str.string_match r s 0

let is_var = function
  | "rsp" | "rcx" | "rdi" | "rsi" | "rdx" | "r8"
  | "r9" | "rax" | "rbx" | "rbp" | "r10" | "r11"
  | "r12" | "r13" | "r14" | "r15" -> false
  | _ as s -> let r = Str.regexp "^[a-zA-Z_][a-zA-Z_0-9-]*$" in
    Str.string_match r s 0

let is_sx s =
  s = "rcx" || is_var s

let is_a = function
    "rdi" | "rsi" | "rdx" | "r8" | "r9" -> true
  | _ as s -> is_sx s

let is_w = function
    "rax" | "rbx" | "rbp" | "r10" | "r11" | "r12" | "r13" | "r14" | "r15" -> true
  | _ as s -> is_a s

let is_x s = is_w s || s = "rsp";;
let is_u s = is_w s || is_label s;;
let is_t s = is_x s || is_integer s;;
let is_s s = is_x s || is_integer s || is_label s;;

