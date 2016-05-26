open SExpr
open Spill
open Liveness
open Graph_color
open Utils_l2


let compile_inst spills replace = function
  | Expr [Atom w; Atom "<-"; Atom s] ->
    Expr [Atom (replace w); Atom "<-"; Atom (replace s)]
  | Expr [Atom w; Atom "<-"; Expr [Atom "mem"; Atom x; Atom n8]] ->
    Expr [Atom (replace w); Atom "<-"; Expr [Atom "mem"; Atom (replace x); Atom n8]]
  | Expr [Expr [Atom "mem"; Atom x; Atom n8]; Atom "<-"; Atom s] ->
    Expr [Expr [Atom "mem"; Atom (replace x); Atom n8]; Atom "<-"; Atom (replace s)]
  | Expr [Atom w; Atom op; Atom t] when (is_aop op || is_sop op) ->
    Expr [Atom (replace w); Atom op; Atom (replace t)]
  | Expr [Atom w; Atom "<-"; Atom t1; Atom cmp; Atom t2] ->
    Expr [Atom (replace w); Atom "<-"; Atom (replace t1); Atom cmp; Atom (replace t2)]
  | Expr [Atom "cjump"; Atom t1; Atom cmp; Atom t2; Atom l1; Atom l2] ->
    Expr [Atom "cjump"; Atom (replace t1); Atom cmp; Atom (replace t2); Atom l1; Atom l2]
  | Expr [Atom call; Atom u; Atom nat]
    when (call = "call" || call = "tail-call") ->
    (* be careful with other calls *)
    Expr [Atom call; Atom (replace u); Atom nat]
  | Expr [Atom w; Atom "<-"; Expr [Atom "stack-arg"; Atom n8]] ->
    let n8 = int_of_string n8 in
    Expr [Atom (replace w); Atom "<-";
          Expr [Atom "mem"; Atom "rsp";
                Atom (string_of_int (8 * spills + n8))]]
  | _ as i -> i


(* register allocation work here *)
let compile_function prefix f_expr =
  match f_expr with
  | Expr (f_label :: vars :: Atom spills_str :: insts) ->
    let ig, my_vars = build_interference_graph (Array.of_list insts) in
    let var_to_spill a_ig =
      (* don't mut ig *)
      let fold_f v res =
        if SS.mem v my_vars then begin
          let d = G.out_degree a_ig v in
          match res with
          | Some (_, res_d) ->
            if d > res_d then Some (v, d) else res
          | None -> Some (v, d)
        end
        else res
      in
      G.fold_vertex fold_f a_ig None
    in
    let replace_f_gen mapping v =
      try StrMap.find v mapping
      with Not_found -> v
    in
    let rec coloring_spill_loop f_expr a_ig vars spills_str insts =
      let spills = int_of_string spills_str in
      begin match graph_color a_ig with
      | Some var2reg ->
        Some (Expr (f_label :: vars :: Atom spills_str
              :: List.map (compile_inst spills (replace_f_gen var2reg)) insts))
      | None ->
        begin match var_to_spill a_ig with
        | Some (to_spill, _) ->
          let nf_expr = Spill.spill f_expr to_spill prefix in
          begin match nf_expr with
          | Expr (_ :: nvars :: Atom nspills_str :: ninsts) ->
            begin let n_ig, _ = build_interference_graph (Array.of_list ninsts) in
            coloring_spill_loop nf_expr n_ig nvars nspills_str ninsts
            end
          | _ -> failwith "l2c: register allocation: not a valid function expression"
          end
        | None -> None
        end
      end
    in
    coloring_spill_loop f_expr ig vars spills_str insts
  | _ -> failwith "l2c: register allocation: not a valid function expression"

let compile_program = function
  | Expr (p_label :: f_lst) ->
    let rec fold_left_until_none f lst acc =
      begin match lst with
        | hd :: tl ->
          begin match f hd acc with
            | Some _ as nacc -> fold_left_until_none f tl nacc
            | None -> None
          end
        | [] -> acc
      end
    in
    let prefix = "l2_" in
    let fold_functions f_expr = function
      | Some acc ->
          begin match compile_function prefix f_expr with
            | Some nf_expr -> Some (nf_expr :: acc)
            | None -> None
          end
      | None -> None
    in
    begin match fold_left_until_none fold_functions f_lst (Some []) with
    | Some rev_nfs -> Some (Expr (p_label :: List.rev rev_nfs))
    | None -> None
    end
  | _ -> failwith "l2c: Program is not well formed"
