open SExpr
open AST_l3
open FrontEndUtils

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

let l3_var_prefix = "l3_var"
and l3_label_prefix = "l3_label_"
and l3_entry = ":main"
and fresh_l2_label_prefix = ":l2_label"
and result_reg = Atom "rax"
and tmp_var = Atom "tmp" (* only used in bounds check and must init every usssage and could be used multiple times *)

(* encoding number *)
let encode_l3_v = function
  | L3Num n -> L3Num (Int64.add Int64.one (Int64.shift_left n 1))
  | els -> els

(* v -> expr (Atom ...) *)
let compile_l3_v_generator l3_label_prefixer l3_var_rename = function
  | L3Var v -> Atom (l3_var_rename v)
  | L3Label l -> Atom (l3_label_prefixer l)
  | L3Num n -> Atom (Int64.to_string n)

(* d -> sexpr list *)
let rec compile_l3_d get_fresh_l2_label my_compile_l3_v dst inst_d =
  let ending = if dst = result_reg then [Expr [Atom "return"]] else [] in
  let add_sub_insts lhs_v rhs_v op amend =
    let lhs = my_compile_l3_v (encode_l3_v lhs_v)
    and rhs = my_compile_l3_v (encode_l3_v rhs_v) in
    Expr [dst; Atom "<-"; lhs] ::
    Expr [dst; op; rhs] ::
    Expr [dst; amend; Atom "1"] ::
    ending
  in
  let cmp_insts lhs_v rhs_v sop =
    (* comparison no need of encoding, but result are encoded*)
    let lhs = my_compile_l3_v (encode_l3_v lhs_v)
    and rhs = my_compile_l3_v (encode_l3_v rhs_v) in
    Expr [dst; Atom "<-"; lhs; sop; rhs] ::
    Expr [dst; Atom "<<="; Atom "1"] ::
    Expr [dst; Atom "+="; Atom "1"] ::
    ending
  in
  let bounds_checking_insts arr_sexpr pos_sexpr =
    let non_negtive_label = Atom (get_fresh_l2_label ())
    and bounds_pass_label = Atom (get_fresh_l2_label ())
    and bounds_fail_label = Atom (get_fresh_l2_label ()) in
    Expr [dst; Atom "<-"; pos_sexpr] ::
    Expr [dst; Atom ">>="; Atom "1"] ::
    Expr [Atom "cjump"; dst; Atom "<"; Atom "0"; bounds_fail_label; non_negtive_label] ::
    non_negtive_label ::
    Expr [tmp_var; Atom "<-"; Expr [Atom "mem"; arr_sexpr; Atom "0"]] ::
    Expr [Atom "cjump"; dst; Atom "<"; tmp_var; bounds_pass_label; bounds_fail_label] ::
    bounds_fail_label ::
    Expr [tmp_var; Atom "<-"; Atom "1"] :: (* garbeage collection *)
    Expr [Atom "rdi"; Atom "<-"; arr_sexpr] ::
    Expr [Atom "rsi"; Atom "<-"; pos_sexpr] ::
    Expr [Atom "call"; Atom "array-error"; Atom "2"] ::
    bounds_pass_label :: 
    Expr [tmp_var; Atom "<-"; Atom "1"] :: (* garbeage collection *)
    []
  in
  let assign_vars_to_args vars_sexprs vars_len args_len =
    let vars_arr = Array.of_list vars_sexprs
    and args_arr = Array.of_list args in
    let insts_arr = Array.make vars_len (Atom "") in
    begin
      for i = 0 to vars_len - 1 do
        if i < args_len then
          insts_arr.(i) <- Expr [Atom args_arr.(i); Atom "<-"; vars_arr.(i)]
        else
          let n8 = Atom (string_of_int (8 * (args_len - i - 2))) in
          insts_arr.(i) <- Expr [Expr [Atom "mem"; Atom "rsp"; n8]; Atom "<-"; vars_arr.(i)]
      done;
      Array.to_list insts_arr
    end
  in
  let function_call_insts f_sexpr vars_sexprs =
    let vars_len = List.length vars_sexprs
    and args_len = List.length args in
    let call_inst call = Expr [call; f_sexpr; Atom (string_of_int vars_len)]
    and sto_res_inst = Expr [dst; Atom "<-"; result_reg]
    and vars2args_insts = assign_vars_to_args vars_sexprs vars_len args_len in
    if dst = result_reg && vars_len <= args_len then begin
      (* tail call *)
      vars2args_insts @
      [call_inst (Atom "tail-call")]
    end
    else begin
      (* normal calls *)
      let return_label = Atom (get_fresh_l2_label ()) in
      Expr [Expr [Atom "mem"; Atom "rsp"; Atom "-8"]; Atom "<-"; return_label] ::
      vars2args_insts @
      (call_inst (Atom "call") ::
       return_label ::
       sto_res_inst ::
       ending)
    end
  in
  let system_call_insts ?(extras=[]) f_sexpr vars_sexpr =
    let vars_len = List.length vars_sexpr
    and args_len = List.length args in
    let call_inst call = Expr [call; f_sexpr; Atom (string_of_int vars_len)]
    and sto_res_inst = Expr [dst; Atom "<-"; result_reg]
    and vars2args_insts = assign_vars_to_args vars_sexpr vars_len args_len in
    (* system_calls calls *)
    vars2args_insts @
    (call_inst (Atom "call") ::
     sto_res_inst :: extras
     @ ending)
  in
  begin match inst_d with
    | L3Add (lhs_v, rhs_v) ->
      add_sub_insts lhs_v rhs_v (Atom "+=") (Atom "-=")
    | L3Sub (lhs_v, rhs_v) ->
      add_sub_insts lhs_v rhs_v (Atom "-=") (Atom "+=")
    | L3Mul (lhs_v, rhs_v) ->
      let lhs = my_compile_l3_v (encode_l3_v lhs_v)
      and rhs = my_compile_l3_v (encode_l3_v rhs_v) in
      Expr [tmp_var; Atom "<-"; lhs] ::
      Expr [tmp_var; Atom ">>="; Atom "1"] ::
      Expr [dst; Atom "<-"; rhs] ::
      Expr [dst; Atom ">>="; Atom "1"] ::
      Expr [dst; Atom "*="; tmp_var] ::
      Expr [dst; Atom "<<="; Atom "1"] :: (* equaivalent to dst *= 2 *)
      Expr [dst; Atom "+="; Atom "1"] ::
      Expr [tmp_var; Atom "<-"; Atom "1"] ::
      ending
    | L3Less (lhs_v, rhs_v) ->
      cmp_insts lhs_v rhs_v (Atom "<")
    | L3LessEq (lhs_v, rhs_v) ->
      cmp_insts lhs_v rhs_v (Atom "<=")
    | L3Equal (lhs_v, rhs_v) ->
      cmp_insts lhs_v rhs_v (Atom "=")
    | L3NumberQo any_v ->
      let any_sexpr = my_compile_l3_v (encode_l3_v any_v) in
      Expr [dst; Atom "<-"; any_sexpr] ::
      Expr [dst; Atom "&="; Atom "1"] ::
      Expr [dst; Atom "<<="; Atom "1"] ::
      Expr [dst; Atom "+="; Atom "1"] ::
      ending
    | L3AQo any_v ->
      let any_sexpr = my_compile_l3_v (encode_l3_v any_v) in
      Expr [dst; Atom "<-"; any_sexpr] ::
      Expr [dst; Atom "&="; Atom "1"] ::
      Expr [dst; Atom "*="; Atom "-2"] ::
      Expr [dst; Atom "+="; Atom "3"] ::
      ending
    | L3App (fun_v, args_v) ->
      let fun_sexpr = my_compile_l3_v fun_v
      and arg_sexprs = List.map (fun arg_v -> my_compile_l3_v @@ encode_l3_v arg_v) args_v in
      function_call_insts fun_sexpr arg_sexprs
    | L3NewArray (size_v, init_v) ->
      (* call to allocate *)
      (* size of the array is not encoded specified in L1 definition *)
      let size_sexpr = my_compile_l3_v (encode_l3_v size_v)
      and init_sexpr = my_compile_l3_v (encode_l3_v init_v) in
      system_call_insts (Atom "allocate") [size_sexpr; init_sexpr]
    | L3NewTuple vals_v ->
      let loc = ref 0 in
      let val_assign val_sexpr =
        let n8 = Atom (string_of_int (8 * (!loc + 1))) in
        begin
          incr loc;
          Expr [Expr [Atom "mem"; result_reg; n8]; Atom "<-"; val_sexpr]
        end
      in
      let size_sexpr = my_compile_l3_v (encode_l3_v (L3Num (Int64.of_int (List.length vals_v))))
      and init_sexpr = Atom "1"
      and initials_sexprs = List.map (fun arg_v -> my_compile_l3_v @@ encode_l3_v arg_v) vals_v in
      let assign_initals_insts = List.map val_assign initials_sexprs in
      system_call_insts (Atom "allocate") [size_sexpr; init_sexpr] ~extras: assign_initals_insts
    | L3Aref (arr_v, pos_v) ->
      let arr_sexpr = my_compile_l3_v arr_v
      and pos_sexpr = my_compile_l3_v (encode_l3_v pos_v) in
      bounds_checking_insts arr_sexpr pos_sexpr @
      (Expr [dst; Atom "<<="; Atom "3"] ::
       Expr [dst; Atom "+="; arr_sexpr] ::
       Expr [dst; Atom "<-"; Expr [Atom "mem"; dst; Atom "8"]] ::
       ending)
    | L3Aset (arr_v, pos_v, val_v) ->
      (* associate with boundry checking *)
      let arr_sexpr = my_compile_l3_v arr_v
      and pos_sexpr = my_compile_l3_v (encode_l3_v pos_v)
      and val_sexpr = my_compile_l3_v (encode_l3_v val_v) in
      bounds_checking_insts arr_sexpr pos_sexpr @
      (Expr [dst; Atom "<<="; Atom "3"] :: (* equaivalent to dst *= 8 *)
       Expr [dst; Atom "+="; arr_sexpr] ::
       Expr [Expr [Atom "mem"; dst; Atom "8"]; Atom "<-"; val_sexpr] ::
       Expr [dst; Atom "<-"; Atom "1"] ::
       ending)
    | L3Alen arr_v ->
      (* arr_v can not be constant *)
      let arr_sexpr = my_compile_l3_v arr_v in
      let mem_sexpr = Expr [Atom "mem"; arr_sexpr; Atom "0"] in
      Expr [dst; Atom "<-"; mem_sexpr] ::
      Expr [dst; Atom "<<="; Atom "1"] ::
      Expr [dst; Atom "+="; Atom "1"] ::
      ending
    | L3Print val_v ->
      (* call to print *)
      let arg_sexprs = [my_compile_l3_v (encode_l3_v val_v)] in
      system_call_insts (Atom "print") arg_sexprs
    | L3V v_v ->
      let var_expr = my_compile_l3_v (encode_l3_v v_v) in
      Expr [dst; Atom "<-"; var_expr] :: ending
    | L3MakeClosure (l, v_v) ->
      compile_l3_d get_fresh_l2_label my_compile_l3_v dst (L3NewTuple [L3Label l; v_v])
    | L3ClosureProc arr_v ->
      compile_l3_d get_fresh_l2_label my_compile_l3_v dst (L3Aref (arr_v, L3Num (Int64.zero)))
    | L3ClosureVars arr_v ->
      compile_l3_d get_fresh_l2_label my_compile_l3_v dst (L3Aref (arr_v, L3Num (Int64.one)))
    | L3Read -> system_call_insts (Atom "read") []
  end

(* important now evaluation order matters since passing mutable hashtable around *)
(* e -> expr list *)
let rec compile_l3_e l3_label_prefixer get_fresh_l2_label l3_var_map get_fresh_l2_var l3_e =
  let my_compile_l3_v =
    compile_l3_v_generator l3_label_prefixer (fun v -> try Hashtbl.find l3_var_map v with Not_found -> failwith (v ^ " is not found"))
  in
  match l3_e with
  | L3Let ((var_str, inst_d), body_e) when is_var var_str ->
    (* binding not in tail position *)
    (* dst_v must be a var *)
    let l3_dst = var_str
    and l2_dst = get_fresh_l2_var () in
    let bind_insts = compile_l3_d get_fresh_l2_label my_compile_l3_v (Atom l2_dst) inst_d in
    begin
      Hashtbl.add l3_var_map l3_dst l2_dst; (** add new binding to shadow when evaluate body_e *)
      let body_insts =
        compile_l3_e l3_label_prefixer get_fresh_l2_label l3_var_map get_fresh_l2_var body_e in
      begin
        (* to avoid copy hashtable in restore the mapping *)
        Hashtbl.remove l3_var_map l3_dst;
        bind_insts @ body_insts
      end
    end
  | L3If (test_v, thn_e, els_e) ->
    (* if sematics everythin is not number zero is true *)
    let encoded_false = Atom "1" in
    let then_label = Atom (get_fresh_l2_label ())
    and else_label = Atom (get_fresh_l2_label ())
    and test = my_compile_l3_v (encode_l3_v test_v) (* need to encode v could be any v *)
    and then_insts = compile_l3_e l3_label_prefixer get_fresh_l2_label l3_var_map get_fresh_l2_var thn_e
    and else_insts = compile_l3_e l3_label_prefixer get_fresh_l2_label l3_var_map get_fresh_l2_var els_e
    in
    Expr [Atom "cjump"; test; Atom "="; encoded_false; else_label; then_label] ::
    then_label :: then_insts
    @ else_label :: else_insts
  | L3D inst_d ->
    (* nested e's tail position store result to result register *)
    (* return or tail-call should be determined in compile_l3_d with info of dst *)
    compile_l3_d get_fresh_l2_label my_compile_l3_v result_reg inst_d
  | _ -> failwith "l3c: invalid l3_e"


(* rename variables during compile function with prefix *)
(* f -> expr *)
let compile_l3_f l3_fun_label_prefixer l3_label_prefixer get_fresh_l2_label = function
  | L3Fun (fun_labl, vars, body_e) when (is_label fun_labl && List.for_all is_var vars) ->
    let l2_var_cnt = ref 0 in
    let get_fresh_l2_var () = (* prefix means this var stems from l3 *)
      let l2_var = l3_var_prefix ^ string_of_int !l2_var_cnt in
      begin
        incr l2_var_cnt;
        l2_var
      end
    in
    let l3_var_map = Hashtbl.create (List.length vars) in
    let rename_l3_args l3_var =
      try
        Hashtbl.find l3_var_map l3_var
      with Not_found ->
        let l2_var = get_fresh_l2_var () in
        begin
          Hashtbl.add l3_var_map l3_var l2_var;
          l2_var
        end
    in
    let my_compile_l3_v = compile_l3_v_generator l3_label_prefixer rename_l3_args in
    let assign_args_to_vars vars =
      let args_len = List.length args
      and args_arr = Array.of_list args
      and vars_len = List.length vars
      and vars_arr = Array.of_list vars in (* vars must all be vars but no checks *)
      let assign_insts = Array.make vars_len (Atom "") in
      for i = 0 to vars_len-1 do
        let v_sexpr = my_compile_l3_v (L3Var (vars_arr.(i))) in
        if i < args_len then
          assign_insts.(i) <- Expr [v_sexpr; Atom "<-"; Atom args_arr.(i)]
        else
          let n8 = Atom (string_of_int (8 * (vars_len - 1 - i))) in
          assign_insts.(i) <- Expr [v_sexpr; Atom "<-"; Expr [Atom "stack-arg"; n8]]
      done;
      Array.to_list assign_insts
    in
    let labl = compile_l3_v_generator l3_fun_label_prefixer rename_l3_args (L3Label fun_labl) (* fun_labl must be label check during parser *)
    and num_vars = Atom (string_of_int (List.length vars))
    and spills = Atom "0" in
    let insts =
      (* ensure that assign_insts eval before body_insts *)
      let assign_insts = assign_args_to_vars vars in
      let body_insts = compile_l3_e l3_label_prefixer get_fresh_l2_label l3_var_map get_fresh_l2_var body_e in
      assign_insts @ body_insts
    in
    Expr ([labl; num_vars; spills] @ insts)
  | _ -> failwith "l3c: invalid l3 function"

(** all other label (labels are global unique ) except :main should be renamed with prefix *)
let compile_l3_p = function
  | L3Prog (entry_e, fundefs) ->
    let get_fresh_l2_label = get_unique_str_generator fresh_l2_label_prefix
    and l3_label_prefixer labl =
      ":" ^ l3_label_prefix ^ String.sub labl 1 ((String.length labl) - 1)
    and identical i = i in
    let entry_fun = L3Fun (l3_entry, [], entry_e)
    and fs = List.map (compile_l3_f l3_label_prefixer l3_label_prefixer get_fresh_l2_label) fundefs in
    Expr (Atom l3_entry :: (compile_l3_f identical l3_label_prefixer get_fresh_l2_label entry_fun) :: fs)
