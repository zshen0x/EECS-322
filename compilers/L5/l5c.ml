open AST_l5
open AST_l4
open FrontEndUtils

module SS = Set.Make(String)
module StrMap = Map.Make(String)

let l5_var_prefix = "l5_var"
and l4_var_prefix = "l4_var"
and fn_prefix = ":fn"
and vars_tup = "vars_tups"

(* AST_l5_e -> AST_l4_prog *)

(*
  TODO 1. grammar check for prime not enough argument
*)

let alpha_renaming =
  let get_fresh_l5_var = get_unique_str_generator l5_var_prefix in
  let lookup v mapping =
    try StrMap.find v mapping
    with Not_found -> failwith "unbound variable: " ^ v
  in
  let rec alpha_renaming_recr mapping = function
    | X x -> X (lookup x mapping)
  | Let ((var, e1), e2) ->
    let alpha = get_fresh_l5_var () in
    Let ((alpha, alpha_renaming_recr mapping e1),
         alpha_renaming_recr (StrMap.add var alpha mapping) e2)
  | LetRec ((var, e1), e2) ->
    let alpha = get_fresh_l5_var () in
    let mapping = StrMap.add var alpha mapping in
    LetRec ((alpha, alpha_renaming_recr mapping e1),
        alpha_renaming_recr mapping e2)
  | If (e1, e2, e3) ->
    If (alpha_renaming_recr mapping e1,
        alpha_renaming_recr mapping e2,
        alpha_renaming_recr mapping e3)
  | Begin (e1, e2) ->
    Begin (alpha_renaming_recr mapping e1,
           alpha_renaming_recr mapping e2)
  | NewTuple initials ->
    NewTuple (List.map (alpha_renaming_recr mapping) initials)
  | App (f, l5_args) ->
    App (alpha_renaming_recr mapping f,
         List.map (alpha_renaming_recr mapping) l5_args)
  | Fn (vars, e) ->
    let rev_vars, mapping =
      List.fold_left
        (fun acc v ->
           let alpha_vars, mapping = acc in
           let alpha = get_fresh_l5_var () in
           (alpha :: alpha_vars, StrMap.add v alpha mapping)) ([], mapping) vars
    in
    let alpha_vars = List.rev rev_vars in
    Fn (alpha_vars, alpha_renaming_recr mapping e)
  | els -> els
  in
  alpha_renaming_recr StrMap.empty

let compile_l5 e =
  (* let get_fresh_l5_var = get_unique_str_generator l5_var_prefix in *)
  let get_fresh_l4_var = get_unique_str_generator l4_var_prefix
  and get_fresh_fn_label = get_unique_str_generator fn_prefix
  and l5_zero = Num Int64.zero in
  let rec compile_l5_e_recr l4_fundefs = function
    | X x -> (L4Var x, l4_fundefs)
    | Num n -> (L4Num n, l4_fundefs)
    | Let ((var, e1), e2) ->
      let l4_e1, e1_fs = compile_l5_e_recr [] e1 in
      let l4_e2, e2_fs = compile_l5_e_recr [] e2 in
      (L4Let ((var, l4_e1), l4_e2), e1_fs @ (e2_fs @ l4_fundefs))
    | LetRec ((var, e1), e2) ->
      let l5_var = X var in
      let replacement = App (Prim Aref, [l5_var; l5_zero]) in
      compile_l5_e_recr
      (* NB this is a L5 -> L5 transformation *)
      l4_fundefs
      (Let ((var, NewTuple [l5_zero]),
            Begin (App (Prim Aset, [l5_var; l5_zero; replace_l5_e l5_var replacement e1]),
                   replace_l5_e l5_var replacement e2)))
    | If (e1, e2, e3) ->
      let l4_e1, e1_fs = compile_l5_e_recr [] e1 in
      let l4_e2, e2_fs = compile_l5_e_recr [] e2 in
      let l4_e3, e3_fs = compile_l5_e_recr [] e3 in
      (L4If (l4_e1, l4_e2, l4_e3), e1_fs @ (e2_fs @ (e3_fs @ l4_fundefs)))
    | Begin (e1, e2) ->
      let l4_e1, e1_fs = compile_l5_e_recr [] e1 in
      let l4_e2, e2_fs = compile_l5_e_recr [] e2 in
      (L4Begin (l4_e1, l4_e2), e1_fs @ (e2_fs @ l4_fundefs))
    | NewTuple init_vals ->
      let l4_initvals, fs = collect_l4_e_lst init_vals in
      (L4NewTuple l4_initvals, fs @ l4_fundefs)
    | App (Prim p, l5_args) ->
      compile_l5_app_prim p l5_args l4_fundefs
    | App (X x, l5_args) ->
      let l4_x = L4Var x in
      let l4_args, l4_args_fs = collect_l4_e_lst l5_args in
      (L4App ((L4ClosureProc l4_x), (L4ClosureVars l4_x) :: l4_args),
       l4_args_fs @ l4_fundefs)
    | App (l5_f, l5_args) ->
      let l4_f, l4_f_fs = compile_l5_e_recr [] l5_f in
      let l4_args, l4_args_fs = collect_l4_e_lst l5_args in
      let l4_id = get_fresh_l4_var () in
      let l4_var = L4Var l4_id in
      (L4Let ((l4_id, l4_f),
              L4App (L4ClosureProc l4_var, L4ClosureVars l4_var :: l4_args)),
       l4_f_fs @ (l4_args_fs @ l4_fundefs))
    | Prim p' as p ->
      begin match p' with
        Add | Sub | Mul | Less | LessEq | Equal | NewArray | Aref ->
        compile_l5_e_recr l4_fundefs (Fn (["x"; "y"], App (p, [X "x"; X "y"])))
      | NumberQo | AQo | Alen | Print ->
        compile_l5_e_recr l4_fundefs (Fn (["x"], App (p, [X "x"])))
      | Aset ->
        compile_l5_e_recr l4_fundefs (Fn (["x"; "y"; "z"], App (p, [X "x"; X "y"; X "z"])))
      | Read -> compile_l5_e_recr l4_fundefs (Fn ([], App (p, [])))
      end
    | lambda ->
      lift_lambda l4_fundefs lambda
  and lift_lambda l4_fundefs = function
    | Fn (vars, e) as fn ->
      let free_variables = SS.elements (get_free_variables fn) in
      let cnt = ref 0 in
      let rec add_bounds l4_e = function
        | [] -> l4_e
        | hd :: rst ->
          let pos = L4Num (Int64.of_int !cnt) in
          begin
            incr cnt;
            L4Let ((hd, L4Aref (L4Var vars_tup, pos)),
                   add_bounds l4_e rst)
          end
      in
      let l4_body_e, l4_fs = compile_l5_e_recr [] e in
      let fn_labl = get_fresh_fn_label () in
      (
        L4MakeClosure (fn_labl, (L4NewTuple (List.map (fun v -> L4Var v) free_variables))),
        L4Fun (fn_labl, vars_tup :: vars, add_bounds l4_body_e free_variables)
        :: (l4_fs @ l4_fundefs)
      )
    | _ -> invalid_arg "l5c: lift_lambda: must be a l5 Fn"
  and get_free_variables expr =
    let accmulate_lst =
      List.fold_left (fun acc e -> SS.union acc (get_free_variables e)) SS.empty
    in
    match expr with
    | X x -> SS.singleton x
    | Let ((var, e1), e2) ->
      SS.union (get_free_variables e1) (SS.diff (get_free_variables e2) (SS.singleton var))
    | LetRec ((var, e1), e2) ->
      SS.diff (SS.union (get_free_variables e1) (get_free_variables e2)) (SS.singleton var)
    | If (e1, e2, e3) ->
      SS.union (get_free_variables e1) (SS.union (get_free_variables e2) (get_free_variables e3))
    | NewTuple initvals ->
      accmulate_lst initvals
    | Begin (e1, e2) ->
      SS.union (get_free_variables e1) (get_free_variables e2)
    | App (f, args) ->
      SS.union (get_free_variables f) (accmulate_lst args)
    | Fn (vars, e) ->
      SS.diff (get_free_variables e) (SS.of_list vars)
    | _ -> SS.empty (* we assume program are correct and thus we ignore free variables in labmda body *)
  and replace_l5_e target replacement expr =
    let replace_e = replace_l5_e target replacement in
    begin match expr with
      | any when any = target ->
        replacement
      | Fn (vars, e) ->
        (* make sure x is not shadowed *)
        Fn (vars,
            begin match target with
              | X x when not (List.mem x vars) ->
                replace_e e
              | _ -> e
            end)
      | Let ((var, e1), e2) ->
        Let ((var, replace_e e1),
             begin match target with
               | X x when var <> x ->
                 replace_e e2
               | _ -> e2
             end)
      | LetRec ((var, e1), e2) ->
        LetRec ((var, replace_e e1),
                begin match target with
                  | X x when var <> x ->
                    replace_e e2
                  | _ -> e2
                end)
      | If (e1, e2, e3) ->
        If (replace_e e1,
            replace_e e2,
            replace_e e3)
      | NewTuple inits ->
        NewTuple (List.map replace_e inits)
      | Begin (e1, e2) ->
        Begin (replace_e e1, replace_e e2)
      | App (f, args) ->
        App (replace_e f, List.map replace_e args)
      | _ -> expr (* dont change *)
    end
  and collect_l4_e_lst exprs =
    let args, fundefs = List.fold_left
        (fun acc e ->
           let l4_e, l4_fs = compile_l5_e_recr [] e in
           (l4_e :: (fst acc), l4_fs @ (snd acc)))
        ([], [])
        exprs
    in
    (List.rev args, fundefs)
  and compile_l5_app_prim p l5_args l4_fundefs =
    let l4_args, fs = collect_l4_e_lst l5_args in
    let l4_app_expr =
      begin match p with
        | Add ->
          begin match l4_args with
            | [lhs; rhs] -> L4Add (lhs, rhs)
            | _ -> failwith "l5c: biop require 2 operand"
          end
        | Sub ->
          begin match l4_args with
            | [lhs; rhs] -> L4Sub (lhs, rhs)
            | _ -> failwith "l5c: biop require 2 operand"
          end
        | Mul ->
          begin match l4_args with
            | [lhs; rhs] -> L4Mul (lhs, rhs)
            | _ -> failwith "l5c: biop require 2 operand"
          end
        | Less ->
          begin match l4_args with
            | [lhs; rhs] -> L4Less (lhs, rhs)
            | _ -> failwith "l5c: biop require 2 operand"
          end
        | LessEq ->
          begin match l4_args with
            | [lhs; rhs] -> L4LessEq (lhs, rhs)
            | _ -> failwith "l5c: biop require 2 operand"
          end
        | Equal ->
          begin match l4_args with
            | [lhs; rhs] -> L4Equal (lhs, rhs)
            | _ -> failwith "l5c: biop require 2 operand"
          end
        | NumberQo ->
          begin match l4_args with
            | [any] -> L4NumberQo any
            | _ -> failwith "l5c: pred require 1 operand"
          end
        | AQo ->
          begin match l4_args with
            | [any] -> L4AQo any
            | _ -> failwith "l5c: pred require 1 operand"
          end
        | Print ->
          begin match l4_args with
            | [any] -> L4Print any
            | _ -> failwith "l5c: print require 1 operand"
          end
        | Read ->
          begin match l4_args with
            | [] -> L4Read
            | _ -> failwith "l5c: read require no operand"
          end
        | NewArray ->
          begin match l4_args with
            | [size; init] -> L4NewArray (size, init)
            | _ -> failwith "l5c: new-array require 2 operand"
          end
        | Aref ->
          begin match l4_args with
            | [arr; pos] -> L4Aref (arr, pos)
            | _ -> failwith "l5c: aref require 2 operand"
          end
        | Aset ->
          begin match l4_args with
            | [arr; pos; value] -> L4Aset (arr, pos, value)
            | _ -> failwith "l5c: aset require 3 operand"
          end
        | Alen ->
          begin match l4_args with
            | [arr] -> L4Alen arr
            | _ -> failwith "l5c: alen require 1 operand"
          end
      end
    in
    (l4_app_expr, fs @ l4_fundefs)
  in
  let prog_e, fundefs =
    compile_l5_e_recr [] (alpha_renaming e)
  in
  L4Prog (prog_e, fundefs)
