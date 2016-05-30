open AST_l4
open AST_l3
open FrontEndUtils

(* let's try to compile with continuation *)

let l3_var_prefix = "l3_var"
and l4_var_prefix = "l4_var"

(* top-level function *)
let is_l3_val = function
  | L3V _ -> true
  | _ -> false

(* l4_e k -> l3_e *)
(* fill d k = k d so eliminate fill *)
let compile_l4_e l4_e =
  let get_fresh_l3_var = get_unique_str_generator l3_var_prefix in
  let maybe_let d f =
    match d with
    | L3V v -> f d
    | _ ->
      let x = get_fresh_l3_var () in
      L3Let ((x, d), (f (L3V (L3Var x))))
  in
  let rec norm_rec l4_e k =
    match l4_e with
    | L4Var id -> k (L3D (L3V (L3Var id))) (* variable renaming *)
    | L4Label id -> k (L3D (L3V (L3Label id)))
    | L4Num n -> k (L3D (L3V (L3Num n)))
    | L4Let ((var_str, bind_e), body_e) ->
      norm_let_k var_str bind_e body_e k
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
    | L4App (fun_e, args_es) -> norm_rec fun_e
                                  (function
                                    | L3D d ->
                                      maybe_let d
                                        (function
                                          | L3V fun_v ->
                                            norm_arbitray_k args_es k (fun arg_vs -> L3App (fun_v, arg_vs))
                                          | _ -> invalid_arg "expected to be a v")
                                    | _ -> invalid_arg "expected to be a d")
    | L4NewArray (size_e, init_e) -> norm_biop_k size_e init_e k (fun l r -> L3NewArray (l, r))
    | L4NewTuple vals_es -> norm_arbitray_k vals_es k (fun x -> L3NewTuple x)
    | L4Aref (arr_e, pos_e) -> norm_biop_k arr_e pos_e k (fun l r -> L3Aref (l, r))
    | L4Aset (arr_e, pos_e, val_e) -> norm_ternary_k arr_e pos_e val_e k (fun x y z -> L3Aset (x, y, z))
    | L4Alen (arr_e) -> norm_unary_k arr_e k (fun x -> L3Alen x)
    | L4Begin (fst_e, snd_e) -> norm_let_k (get_fresh_l3_var ()) fst_e snd_e k
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
  and norm_let_k var_str bind_e body_e k =
    norm_rec bind_e
      (function
        | L3D d ->
          L3Let ((var_str, d), norm_rec body_e k)
        | _ -> invalid_arg "bind expected to be a d")
  and norm_arbitray_k to_lift k what =
    let rec norm_arbitrary_k_rec to_lift acc k =
      match to_lift with
      | [] -> k (List.rev acc)
      | hd :: rst ->
        norm_rec hd
          (function
            | L3D d ->
              maybe_let d
                (function
                  | L3V v -> norm_arbitrary_k_rec rst (v :: acc) k
                  | _ -> invalid_arg "expected to be a v")
          | _ -> invalid_arg "expected to be a d")
    in
    norm_arbitrary_k_rec to_lift [] (fun res -> k (L3D (what res)))
  in
  let norm e = norm_rec e (fun e -> e) in
  norm l4_e

let compile_l4_f = function
  | L4Fun (labl, args, body_e) ->
    (* rename pass happen here *)
    L3Fun (labl, args, compile_l4_e body_e)


let rename_var_l4_e get_fresh_l4_var l4_var_map l4_e =
  let rec rename_var_e = function
    | L4Var v -> L4Var (Hashtbl.find l4_var_map v)
    | L4Add (l, r) -> L4Add (rename_var_e l, rename_var_e r)
    | L4Sub (l, r) -> L4Sub (rename_var_e l, rename_var_e r)
    | L4Mul (l, r) -> L4Mul (rename_var_e l, rename_var_e r)
    | L4Less (l, r) -> L4Less (rename_var_e l, rename_var_e r)
    | L4LessEq (l, r) -> L4LessEq (rename_var_e l, rename_var_e r)
    | L4Equal (l, r) -> L4Equal (rename_var_e l, rename_var_e r)
    | L4NumberQo e -> L4NumberQo (rename_var_e e)
    | L4AQo e -> L4AQo (rename_var_e e)
    | L4App (f, args) -> L4App (rename_var_e f, (List.map rename_var_e args))
    | L4NewArray (l, r) -> L4NewArray (rename_var_e l, rename_var_e r)
    | L4NewTuple vals -> L4NewTuple (List.map rename_var_e vals)
    | L4Aref (l, r) -> L4Aref (rename_var_e l, rename_var_e r)
    | L4Aset (e1, e2, e3) -> L4Aset (rename_var_e e1, rename_var_e e2, rename_var_e e3)
    | L4Alen e -> L4Alen (rename_var_e e)
    | L4Begin (e1, e2) -> L4Begin (rename_var_e e1, rename_var_e e2)
    | L4Print e -> L4Print (rename_var_e e)
    | L4MakeClosure (labl, e) -> L4MakeClosure (labl, rename_var_e e)
    | L4ClosureProc e -> L4ClosureProc (rename_var_e e)
    | L4ClosureVars e -> L4ClosureVars (rename_var_e e)
    | L4If (e1, e2, e3) -> L4If (rename_var_e e1, rename_var_e e2, rename_var_e e3)
    | L4Let ((var, e1), e2) ->
      let new_l4_var = get_fresh_l4_var () in
        let renamed_e1 = rename_var_e e1 in
        begin
          Hashtbl.add l4_var_map var new_l4_var;
          let renamed_e2 = rename_var_e e2 in
          begin
            Hashtbl.remove l4_var_map var;
            L4Let ((new_l4_var, renamed_e1), renamed_e2)
          end

        end
    | _ as e -> e
  in
  rename_var_e l4_e

let rename_var_l4_f = function
  | L4Fun (labl, args, body_e) ->
    let get_fresh_l4_var = get_unique_str_generator l4_var_prefix in
    let l4_var_map = Hashtbl.create (List.length args) in
    let rename_l4_args l4_var =
      try
        Hashtbl.find l4_var_map l4_var
      with Not_found ->
        let new_l4_var = get_fresh_l4_var () in
        begin
          Hashtbl.add l4_var_map l4_var new_l4_var;
          new_l4_var
        end
    in
    let renamed_args = List.map rename_l4_args args in
    let renamed_body_e = rename_var_l4_e get_fresh_l4_var l4_var_map body_e in
    L4Fun (labl, renamed_args, renamed_body_e)

let compile_l4_p = function
  | L4Prog (prog_e, fundefs) ->
    (* preprocessing happen here *)
    let processed_prog_e =
      rename_var_l4_e (get_unique_str_generator l4_var_prefix) (Hashtbl.create 0) prog_e in
    let processed_fundefs = List.map rename_var_l4_f fundefs in
    L3Prog (compile_l4_e processed_prog_e,
            List.map compile_l4_f processed_fundefs)
