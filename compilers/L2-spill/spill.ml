open SExpr;;
open Str;;
open Int64;;

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

let is_var s =
  let r = Str.regexp "^[a-zA-Z_][a-zA-Z_0-9-]*$" in
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


(* f : list sexpr, var : string, prefix : string *)
let spill_in_function f var prefix =
  begin match f with
  | l :: ag :: Atom spills :: rest ->
    let spills = int_of_string spills in
    let spills_n8 = string_of_int (spills * 8) in
    let is_var_to_spill s = (s = var) in
    let counter = ref 0 in
    let spill_instruction = function
      | Expr [Atom w; Atom "<-"; Atom s] as inst ->
        if (is_var_to_spill w && is_var_to_spill s) then
          []
        else if is_var_to_spill w then
          Expr [Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]; Atom "<-"; Atom s] :: []
        else if is_var_to_spill s then
          Expr [Atom w; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] :: []
        else
          [inst]
      | Expr [Atom w; Atom "<-"; Expr mem as mem_acc] when is_var_to_spill w ->
        (* conbined with w <- mem and w <- stack*)
        let suffix = string_of_int !counter in
        let var_after_spill = prefix ^ suffix in
        incr counter;
        Expr [Atom var_after_spill; Atom "<-"; mem_acc] ::
        Expr [Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]; Atom "<-"; Atom var_after_spill] :: []
      (*
      | Expr [Atom w; Atom "<-"; Expr [Atom "stack-args"; Atom n8] as stack_acc] when is_var_to_spill w ->
        let suffix = string_of_int !counter in
        let var_after_spill = prefix ^ suffix in
        incr counter;
        Expr [Atom var_after_spill; Atom "<-"; stack_acc] ::
        Expr [Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]; Atom "<-"; Atom var_after_spill] :: []
      *)
      | Expr [Expr [(Atom "mem"); Atom x; Atom n8] as mem; Atom "<-"; Atom s] when is_var_to_spill s ->
        let suffix = string_of_int !counter in
        let var_after_spill = prefix ^ suffix in
        incr counter;
        Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
        Expr [mem; Atom "<-"; Atom var_after_spill] :: []
      | Expr [Atom w; Atom op; Atom t] as inst when (is_aop op || is_sop op) ->
        (* combined with sop and aop *)
        (* assume no invalid input here *)
        if is_var_to_spill w && is_var_to_spill t then
          let suffix = string_of_int !counter in
          let var_after_spill = prefix ^ suffix in
          incr counter;
          Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
          Expr [Atom var_after_spill; Atom op; Atom var_after_spill] ::
          Expr [Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]; Atom "<-"; Atom var_after_spill] :: []
        else if is_var_to_spill w then
          let suffix = string_of_int !counter in
          let var_after_spill = prefix ^ suffix in
          incr counter;
          Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
          Expr [Atom var_after_spill; Atom op; Atom t] ::
          Expr [Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]; Atom "<-"; Atom var_after_spill] :: []
        else if is_var_to_spill t then
          let suffix = string_of_int !counter in
          let var_after_spill = prefix ^ suffix in
          incr counter;
          Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
          Expr [Atom w; Atom op; Atom var_after_spill] :: []
        else
          [inst]
      | Expr [Atom w; Atom "<-"; Atom t1; Atom cmp; Atom t2] as inst ->
        let suffix = string_of_int !counter in
        let var_after_spill = prefix ^ suffix in
        if is_var_to_spill w || is_var_to_spill t1 || is_var_to_spill t2 then begin
          incr counter;
          let mread = Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]]
          and mwrite = Expr [Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]; Atom "<-"; Atom var_after_spill]
          in
          if is_var_to_spill w then
            let tmp = Expr [Atom var_after_spill;
                            Atom "<-";
                            if is_var_to_spill t1 then Atom var_after_spill else Atom t1;
                            if is_var_to_spill t2 then Atom var_after_spill else Atom t2
                           ] ::
                      mwrite :: []
            in
            if is_var_to_spill t1 || is_var_to_spill t2 then
              mread :: tmp
            else
              tmp
          else
            mread ::
            Expr [Atom var_after_spill;
                  Atom "<-";
                  if is_var_to_spill t1 then Atom var_after_spill else Atom t1;
                  if is_var_to_spill t2 then Atom var_after_spill else Atom t2
                 ] :: []
        end
        else
          [inst]
      | Expr [Atom "cjump"; Atom t1; Atom cmp; Atom t2; label1; label2] as inst ->
        if is_var_to_spill t1 && is_var_to_spill t2 then
          let suffix = string_of_int !counter in
          let var_after_spill = prefix ^ suffix in
          incr counter;
          Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
          Expr [Atom "cjump"; Atom var_after_spill; Atom cmp; Atom var_after_spill; label1; label2] :: []
        else if is_var_to_spill t1 then
          let suffix = string_of_int !counter in
          let var_after_spill = prefix ^ suffix in
          incr counter;
          Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
          Expr [Atom "cjump"; Atom var_after_spill; Atom cmp; Atom t2; label1; label2] :: []
        else if is_var_to_spill t2 then
          let suffix = string_of_int !counter in
          let var_after_spill = prefix ^ suffix in
          incr counter;
          Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
          Expr [Atom "cjump"; Atom t1; Atom cmp; Atom var_after_spill; label1; label2] :: []
        else
          [inst]
      | Expr [Atom c as call; Atom u; Atom nat]
        when ((c = "call" || c = "tail-call") && is_var_to_spill u) ->
        let suffix = string_of_int !counter in
        let var_after_spill = prefix ^ suffix in
        incr counter;
        Expr [Atom var_after_spill; Atom "<-"; Expr [Atom "mem"; Atom "rsp"; Atom spills_n8]] ::
        Expr [call; Atom var_after_spill; Atom nat] :: []
      | _ as inst -> [inst]
                     (* assume no invalid input here*)
        (*
        begin match inst with
        | Expr (Atom "return" :: []) -> inst :: []
        | Atom labl when (is_label labl) -> inst :: []
        | Expr (Atom "goto" :: Atom labl :: []) when (is_label labl) -> inst :: []
        | Expr (Atom "call" :: Atom "print" :: Atom "1" :: []) -> inst :: []
        | Expr (Atom "call" :: Atom func :: Atom "2" :: [])
          when (func = "allocate" || func = "array-error") -> inst :: []
        | _ -> failwith (Printf.sprintf "unable to spill instruction:\n %s" (string_of_sexpr (inst::[])))
        end
        *)
    in
    l :: ag :: Atom (string_of_int (spills + 1))
    :: List.fold_left List.append [] (List.map spill_instruction rest)
  | _ -> failwith "l2-spill: error: not a valid function"
  end

let test0 () =
  let func0 = "(:f 0 0 (k <- 0) (rax <- 0) (rbx <- 1) (rax += k))"
  in
  match (List.hd (parse_string func0)) with
  | Expr fl -> print_sexpr (spill_in_function fl "k" "p_")
  | _ -> failwith "test0: invalid input"

let run_tests () =
  test0 ()

let () =
  let len = Array.length Sys.argv in
  match len with
  | 2
  | _ -> run_tests ()
