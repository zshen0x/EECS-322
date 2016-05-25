
let compose f g x = f (g x)

let is_runtime_calls = function
    "print" | "allocate" | "array-error" | "read" -> true
  | _ -> false

let is_integer s =
  try ignore(Int64.of_string s); true with Failure _ -> false;;

let is_aop = function
    "+=" | "-=" | "*=" | "&=" -> true
  | _ -> false

let is_sop = function
    "<<=" | ">>=" -> true
  | _ -> false

let is_op s = is_aop s || is_sop s

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


let caller_save = ["r10"; "r11"; "r8"; "r9"; "rax"; "rcx"; "rdi"; "rdx"; "rsi"]
let args = ["rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9"]
let callee_save = ["r12"; "r13"; "r14"; "r15"; "rbp"; "rbx"]
let result = ["rax"]

let all_registers = ["r10"; "r11"; "r12"; "r13"; "r14"; "r15"; "r8";
                     "r9"; "rax"; "rbp"; "rbx"; "rcx"; "rdi"; "rdx"; 
                     "rsi"]

let all_registers_except_rcx = ["r10"; "r11"; "r12"; "r13"; "r14"; "r15"; "r8";
                                "r9"; "rax"; "rbp"; "rbx"; "rdi"; "rdx"; "rsi"]


