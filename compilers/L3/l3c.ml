open SExpr
open Parser_l3
open AST_l3
open Utils_l3

module List = struct
    include List
    let rec take n lst = match n with
    | 0 -> []
    | _ ->
      match lst with
      | [] -> []
      | hd :: rst -> hd :: take (n-1) rst
  end

(*

   ;; labels are globally unique
   ;; vars are local to function
p ::= (e
       (label (var ...) e)
       ...)
;; note that functions have arguments now(!)

                                                 ;; nested thing happens here 
e ::= (let ([var d]) e)                          ;; attention there are 3 cases in compiling e    #(if genereate new labels)#
    | (if v e e)                                 ;; have have impact to tail-call or call in later compile
    | d                                          ;; use compile_d may with additional parameter

d ::= (biop v v)                                 ;;  (+ - "*" <<= >>=) -> (tmp <- a) (tmp biop= b), (< <= = use (w <- t cmp t))
      (pred v)                                   ;; &=
      (v v ...) ;; fn call with explicit args    ;; result in rax; tail call or call and calling convention !!!!!
      (new-array v v)                            ;; (call allocate 2) calling convention !!!!!
      (new-tuple v ...)                          ;; (call allocate 2), then gen a loop to assign value
      (aref v v)                                 ;; (w <- (mem x n8))
      (aset v v v)                               ;; ((mem x n8) <- w)
      (alen v)                                   ;; attention to how array is organized in l1
      (read)                                     ;;
      (print v)                                  ;; (call print 1) calling canvention
      (make-closure label v)                     ;; no such in AST     deal that with in parser
      (closure-proc v)                           ;; no such in AST     syntax sugar
      (closure-vars v)                           ;; no such in AST     syntax sugar
      v                                          ;; add prefix since you have to add your variale/label here

v :: = var | label | num                         ;; careful about data encoding

biop ::= + | - | * | < | <= | =
pred ::= number? | a?

Other non-terminals (e.g., label, var) are given in lecture02 and lecture04.
*)


let l3_prefix = "l3_"
and l3_entry = ":main"
and l3_new_var_prefix = "tmp"
and l3_new_label_prefix = ":labl"
and result_reg = Atom "rax"

(* encoding number *)
let encode_l3_v = function
  | Num n -> Num (Int64.shift_left n 1)
  | els -> els

(* v -> expr (Atom ...) *)
let compile_l3_v label_prefixer var_prefixer = function
  | Var v -> Atom (var_prefixer v)
  | Label l -> Atom (label_prefixer l)
  | Num n -> Atom (Int64.to_string n)

(* d -> expr list *)
let compile_l3_d label_prefixer var_prefixer get_new_label get_new_var dst inst_d =
  let encode_and_compile_l3_v v_v =
    encode_l3_v v_v
    |> compile_l3_v label_prefixer var_prefixer
  and compile_l3_v_only = compile_l3_v label_prefixer var_prefixer
  and ending = if dst = result_reg then [Expr [Atom "return"]] else []
  in
  let add_sub_insts lhs_v rhs_v op amend =
    let lhs = encode_and_compile_l3_v lhs_v
    and rhs = encode_and_compile_l3_v rhs_v in
    Expr [dst; Atom "<-"; lhs] ::
    Expr [dst; op; rhs] ::
    Expr [dst; amend; Atom "1"] ::
    ending
  in
  let cmp_insts lhs_v rhs_v sop =
    (* comparison no need of encoding, but result are encoded*)
    let lhs = compile_l3_v_only lhs_v
    and rhs = compile_l3_v_only rhs_v in
    Expr [dst; Atom "<-"; lhs; sop; rhs] ::
    Expr [dst; Atom "<<="; Atom "1"] ::
    Expr [dst; Atom "+="; Atom "1"] ::
    ending
  in
  let bounds_checking_insts arr_sexpr pos_sexpr = 
    let bounds_pass_label = Atom (get_new_label ())
    and bounds_fail_label = Atom (get_new_label ())
    and tmp = Atom (get_new_var ()) in
    Expr [dst; Atom "<-"; pos_sexpr] ::
    Expr [dst; Atom ">>="; Atom "1"] ::
    Expr [tmp; Atom "<-"; Expr [Atom "mem"; arr_sexpr; Atom "0"]] ::
    Expr [Atom "cjump"; dst; Atom "<"; tmp; bounds_pass_label; bounds_fail_label] ::
    bounds_fail_label ::
    Expr [Atom "rdi"; Atom "<-"; arr_sexpr] ::
    Expr [Atom "rsi"; Atom "<-"; pos_sexpr] ::
    Expr [Atom "call"; Atom "array-error"; Atom "2"] ::
    bounds_pass_label  :: []
  in
  begin match inst_d with
    | Add (lhs_v, rhs_v) ->
      add_sub_insts lhs_v rhs_v (Atom "+=") (Atom "-=")
    | Sub (lhs_v, rhs_v) ->
      add_sub_insts lhs_v rhs_v (Atom "-=") (Atom "+=")
    | Mul (lhs_v, rhs_v) ->
      let lhs = encode_and_compile_l3_v lhs_v
      and rhs = encode_and_compile_l3_v rhs_v
      and tmp = Atom (get_new_var ()) in
      Expr [tmp; Atom "<-"; lhs] ::
      Expr [tmp; Atom ">>="; Atom "1"] ::
      Expr [dst; Atom "<-"; rhs] ::
      Expr [dst; Atom ">>="; Atom "1"] ::
      Expr [dst; Atom "*="; tmp] ::
      Expr [dst; Atom "<<="; Atom "1"] :: (* equaivalent to dst *= 2 *)
      Expr [dst; Atom "+="; Atom "1"] ::
      ending
    | Less (lhs_v, rhs_v) ->
      cmp_insts lhs_v rhs_v (Atom "<")
    | LessEq (lhs_v, rhs_v) ->
      cmp_insts lhs_v rhs_v (Atom "<=")
    | Equal (lhs_v, rhs_v) ->
      cmp_insts lhs_v rhs_v (Atom "=")
    | NumberQo any_v ->
      let any_sexpr = encode_and_compile_l3_v any_v in
      Expr [dst; Atom "<-"; any_sexpr] ::
      Expr [dst; Atom "&="; Atom "1"] ::
      Expr [dst; Atom "<<="; Atom "1"] ::
      Expr [dst; Atom "+="; Atom "1"] ::
      ending
    | AQo any_v ->
      let any_sexpr = encode_and_compile_l3_v any_v in
      Expr [dst; Atom "<-"; any_sexpr] ::
      Expr [dst; Atom "&="; Atom "1"] ::
      Expr [dst; Atom "*="; Atom "-2"] ::
      Expr [dst; Atom "+="; Atom "3"] ::
      ending
    | App (fun_v, args_v) ->
      ending
    | NewArray (size_v, init_v) ->
      (* call to allocate *)
      let size_sexpr = encode_and_compile_l3_v size_v
      and init_sexpr = encode_and_compile_l3_v init_v in
      Expr [Atom "rsi"; Atom "<-"; size_sexpr] ::
      Expr [Atom "rdi"; Atom "<-"; init_sexpr] ::
      Expr [Atom "call"; Atom "allocate"; Atom "2"] ::
      Expr [dst; Atom "<-"; result_reg] ::
    | newTuple vals_vst ->
      (* call to allocate *)
      ending
    | Aref (arr_v, pos_v) ->
      let arr_sexpr = compile_l3_v_only arr_v
      and pos_sexpr = encode_and_compile_l3_v pos_v in
      bounds_checking_insts arr_sexpr pos_sexpr @
      (Expr [dst; Atom "<<="; Atom "3"] ::
       Expr [dst; Atom "+="; arr_sexpr] ::
       Expr [dst; Atom "<-"; Expr [Atom "mem"; dst; Atom "8"]] ::
       ending)
    | Aset (arr_v, pos_v, val_v) ->
      (* associate with boundry checking *)
      let arr_sexpr = compile_l3_v_only arr_v
      and pos_sexpr = encode_and_compile_l3_v pos_v
      and val_sexpr = encode_and_compile_l3_v val_v in
      bounds_checking_insts arr_sexpr pos_sexpr @
      (Expr [dst; Atom "<<="; Atom "3"] :: (* equaivalent to dst *= 8 *)
       Expr [dst; Atom "+="; arr_sexpr] ::
       Expr [Expr [Atom "mem"; dst; Atom "8"]; Atom "<-"; val_sexpr] ::
       Expr [dst; Atom "<-"; Atom "1"] ::
       ending)
    | Alen arr_v ->
      (* arr_v can not be constant *)
      let arr_sexpr = compile_l3_v_only arr_v in
      let mem_sexpr = Expr [Atom "mem"; arr_sexpr; Atom "0"] in
      Expr [dst; Atom "<-"; mem_sexpr] ::
      Expr [dst; Atom "<<="; Atom "1"] ::
      Expr [dst; Atom "+="; Atom "1"] ::
      ending
    | Print val_v ->
      (* call to print *)
      let val_sexpr = encode_and_compile_l3_v val_v in
      Expr [Atom "rdi"; Atom "<-"; val_sexpr] ::
      Expr [Atom "call"; Atom "print"; Atom "1"] ::
      Expr [dst; Atom "<-"; result_reg] ::
      ending
    | V v_v ->
      let var_expr = encode_and_compile_l3_v v_v in
      Expr [dst; Atom "<-"; var_expr]
    | Read ->
  end


(* e -> expr list *)
let rec compile_l3_e label_prefixer var_prefixer get_new_label get_new_var = function
  | Let ((dst_v, inst_d), body_e) ->
    (* binding not in tail position *)
    (* dst_v must be a var *)
    let dst = compile_l3_v label_prefixer var_prefixer dst_v in
    compile_l3_d label_prefixer var_prefixer get_new_label get_new_var dst inst_d
    @ compile_l3_e label_prefixer var_prefixer get_new_label get_new_var body_e
  | If (test_v, thn_e, els_e) ->
    (* if sematics everythin is not number zero is true *)
    let then_label = Atom (get_new_label ())
    and else_label = Atom (get_new_label ())
    and test = compile_l3_v label_prefixer var_prefixer (encode_l3_v test_v) (* need to encode v could be any v *)
    and then_insts = compile_l3_e label_prefixer var_prefixer get_new_label get_new_var thn_e
    and else_insts = compile_l3_e label_prefixer var_prefixer get_new_label get_new_var els_e
    in
    Expr [Atom"cjump"; test; Atom "="; Atom "2"; else_label; then_label] ::
    then_label :: then_insts @ else_label :: else_insts
  | D inst_d ->
    (* nested e's tail position store result to result register *)
    (* return or tail-call should be determined in compile_l3_d with info of dst *)
    compile_l3_d label_prefixer var_prefixer
                 get_new_label get_new_var
                 result_reg inst_d


(* rename vars during compile function with prefix and generate new local vars *)
(* f -> expr *)
let compile_l3_f fun_label_prefixer label_prefixer get_new_label = function
  | Fun (fun_labl, vars_v, body_e) ->
    let var_cnt = ref 0 in
    let get_new_var () =
      (* variable local to function *)
      let var = l3_new_var_prefix ^ string_of_int !var_cnt in
      (incr var_cnt;
      var)
    and var_prefixer id = l3_prefix ^ id in
    let assign_args_to_vars vars_v =
      let args_len = List.length args
      and args_arr = Array.of_list args
      and vars_len = List.length vars_v
      and vars_v_arr = Array.of_list vars_v in (* vars must all be vars but no checks *)
      let assign_insts = Array.make vars_len (Atom "") in
      for i = 0 to vars_len-1 do
        let v_sexpr = compile_l3_v label_prefixer var_prefixer vars_v_arr.(i) in
        if i < args_len then
          assign_insts.(i) <- Expr [v_sexpr; Atom "<-"; Atom args_arr.(i)]
        else
          let n8 = Atom (string_of_int (8 * (vars_len - 1 - i))) in
          assign_insts.(i) <- Expr [v_sexpr; Atom "<-"; Expr [Atom "stack-arg"; n8]]
      done;
      Array.to_list assign_insts
    in
    let labl = compile_l3_v fun_label_prefixer var_prefixer fun_labl (* fun_labl must be label check during parser *)
    and vars = Atom (string_of_int (List.length vars_v))
    and spills = Atom "0"
    and insts = assign_args_to_vars vars_v
                @ compile_l3_e label_prefixer var_prefixer get_new_label get_new_var body_e in
    Expr ([labl; vars; spills] @ insts)

(* all other label (labels are global unique ) except :main should be renamed with prefix*)
let compile_l3_p = function
  | Prog (entry_e, fundefs) ->
    let label_cnt = ref 0 in
    let get_new_label () =
      (* label global to program *)
      let labl = l3_new_label_prefix ^ string_of_int !label_cnt in
      (incr label_cnt;
      labl)
    and label_prefixer labl =
      ":" ^ l3_prefix ^ String.sub labl 1 ((String.length labl) - 1)
    and identical_label l = l
    in
    let entry_fun = Fun (Label l3_entry, [], entry_e)
    and fs = List.map (compile_l3_f identical_label label_prefixer get_new_label) fundefs in
    Expr (Atom l3_entry :: (compile_l3_f label_prefixer label_prefixer get_new_label entry_fun) :: fs)
