open AST_l4
open AST_l3
open FrontEndUtils

(* let's try to compile with continuation *)

let l3_var_prefix = "l3_var"
and l4_var_prefix = "l4_"

(* top-level function *)

let get_fresh_l3_var =
  let l3_var_cnt = ref 0 in
  fun () ->
    let l3_var = l3_var_prefix ^ string_of_int !l3_var_cnt in
    begin
      incr l3_var_cnt;
      l3_var
    end

let l4_var_prefixer l4_var = l4_var_prefix ^ l4_var

let is_l3_val = function
  | L3V _ -> true
  | _ -> false

let maybe_let d f =
  match d with
  | L3V v -> f d
  | _ ->
    let x = get_fresh_l3_var () in
    L3Let ((x, d), (f (L3V (L3Var x))))

(* l4_e k -> l3_e *)
(* fill d k = k d so eliminate fill*)
let rec norm_rec l4_e k =
  match l4_e with
  | L4Var id -> k (L3D (L3V (L3Var (l4_var_prefixer id)))) (* variable renaming *)
  | L4Label id -> k (L3D (L3V (L3Label id)))
  | L4Num n -> k (L3D (L3V (L3Num n)))
  | L4Let ((var_str, bind_e), body_e) ->
    norm_rec bind_e
      (function
        | L3D d ->
          maybe_let d
            (fun d -> L3Let ((var_str, d), norm_rec body_e k))
        | _ -> invalid_arg "bind expected to be a d")
  | L4If (cond_e, thn_e, els_e) ->
    norm_rec cond_e
      (function
        | L3D d ->
          maybe_let d
            (function
              | L3V cond_v -> L3If (cond_v, (norm_rec thn_e k), (norm_rec els_e k))
              | _ -> invalid_arg "cond expected to be a v")
        | _ -> invalid_arg "cond expected to be a d")
  | L4Add (lhs_e, rhs_e) -> norm_biop_k lhs_e rhs_e k (fun l r -> L3Add (l, r))
  | L4Sub (lhs_e, rhs_e) -> norm_biop_k lhs_e rhs_e k (fun l r -> L3Sub (l, r))
  | L4Mul (lhs_e, rhs_e) -> norm_biop_k lhs_e rhs_e k (fun l r -> L3Mul (l, r))
  | L4Less (lhs_e, rhs_e) -> norm_biop_k lhs_e rhs_e k (fun l r -> L3Less (l, r))
  | L4LessEq (lhs_e, rhs_e) -> norm_biop_k lhs_e rhs_e k (fun l r -> L3LessEq (l, r))
  | L4Equal (lhs_e, rhs_e) -> norm_biop_k lhs_e rhs_e k (fun l r -> L3Equal (l, r))
  | L4NumberQo any_e -> norm_unary_k any_e k (fun v -> L3NumberQo v)
  | L4AQo any_e -> norm_unary_k any_e k (fun v -> L3AQo v)
  | L4App (fun_e, args_es) -> L3D (L3V (L3Label "to do arbitray args"))
  | L4NewArray (size_e, init_e) -> norm_biop_k size_e init_e k (fun l r -> L3NewArray (l, r))
  | L4NewTuple vals_es -> L3D (L3V (L3Label "to do arbitray args"))
  | L4Aref (arr_e, pos_e) -> norm_biop_k arr_e pos_e k (fun l r -> L3Aref (l, r))
  | L4Aset (arr_e, pos_e, val_e) -> norm_ternary_k arr_e pos_e val_e k (fun x y z -> L3Aset (x, y, z))
  | L4Begin (fst_e, snd_e) -> norm_rec (L4Let ((get_fresh_l3_var (), fst_e), snd_e)) k
  | L4MakeClosure (labl, v_e) -> norm_unary_k v_e k (fun v -> L3MakeClosure (labl, v))
  | L4ClosureProc arr_e -> norm_unary_k arr_e k (fun v -> L3ClosureProc v)
  | L4ClosureVars arr_e -> norm_unary_k arr_e k (fun v -> L3ClosureVars v)
  | L4Print v_e -> norm_unary_k v_e k (fun v -> L3Print v)
  | L4Read -> k (L3D L3Read)
(*
and norm_biop_k lhs_e rhs_e k what =
    norm_rec lhs_e
      (function
        | L3D d ->
          maybe_let d             (* lift lhs *)
            (function
              | L3V lhs_v ->
                begin norm_rec rhs_e
                    (function
                      | L3D d ->
                        maybe_let d   (* lift rhs *)
                          (function
                            | L3V rhs_v -> k (L3D (what lhs_v rhs_v))
                            | _ -> invalid_arg "rhs expected to be a v")
                      | _ -> invalid_arg "rhs expected to be a d")
                end
              | _ -> invalid_arg "lhs expected to be a v")
        | _ -> invalid_arg "lhs expected to be a d")
*)
and norm_unary_k any_e k what =
    norm_rec any_e
      (function
        | L3D d ->
          maybe_let d
            (function
              | L3V v -> k (L3D (what v))
              | _ -> invalid_arg "expected to be a v")
        | _ -> invalid_arg "expected to be a d")
and norm_biop_k lhs_e rhs_e k what =
  norm_rec lhs_e
    (function
      | L3D d ->
        maybe_let d
          (function
            | L3V v -> norm_unary_k rhs_e k (what v)
            | _ -> invalid_arg "expected to be a v")
      | _ -> invalid_arg "expected to be a d")
and norm_ternary_k fst snd thd k what =
  norm_rec fst
    (function
      | L3D d ->
        maybe_let d
          (function
            | L3V v -> norm_biop_k snd thd k (what v)
            | _ -> invalid_arg "expected to v")
      | _ -> invalid_arg "exptected to be a d")


(* l3_d context -> l3_e *)

let compile_l4_e l4_e =
  let norm e = norm_rec e (fun e -> e) in
  norm l4_e

let compile_l4_f = function
  | L4Fun (label, args, body_e) ->
    L3Fun (label, args, compile_l4_e body_e)

let compile_l4_p = function
  | L4Prog (prog_e, fundefs) ->
    L3Prog (compile_l4_e prog_e, List.map compile_l4_f fundefs)


