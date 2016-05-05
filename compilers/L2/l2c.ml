open SExpr
open Spill
open Liveness
open Graph_color


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


let compile_function prefix f_expr =
  let my_vars =
    match f_expr with
    | Expr (f_label :: vars :: Atom spills_str :: insts) ->
      let gen_and_kill_sets = calc_gen_and_kill (Array.of_list insts) in
      let gen_sets = gen_and_kill_sets.first
      and kill_sets = gen_and_kill_sets.second in
      SS.filter is_var (Array.fold_left (fun acc s -> SS.union acc s) SS.empty (Array.append gen_sets kill_sets))
    | _ -> failwith "l2c: compile function: function is not well formed"
  in
  let var_to_spill a_ig =
    (* don't mut ig *)
    let fold_f v res =
      if SS.mem v my_vars then begin
        let d = G.out_degree a_ig v in
        match res with
        | Some (_, res_d) as old ->
          if d > res_d then Some (v, d) else old
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
  let rec coloring_spill_loop = function
    | Some f_expr ->
      begin match f_expr with
        | Expr (f_label :: vars :: Atom spills_str :: insts) ->
          begin let ig = build_interference_graph (Array.of_list insts) in
            (* ig should not be mut ( graph_color implementation it copy a ig ) *)
            let spills = int_of_string spills_str in
            (* careful there lacks the sanity check here,
               assume mapping have all vars to reg allocation
               and that all not in mapping are not vars
            *)
            begin match graph_color ig with
              | Some var2reg ->
                Some (Expr (f_label :: vars :: Atom spills_str
                            :: List.map (compile_inst spills (replace_f_gen var2reg)) insts))
              | None ->
                begin match var_to_spill ig with
                  | Some (to_spill, _) ->
                    coloring_spill_loop (Some (Spill.spill f_expr to_spill prefix))
                  | None -> None
                end
            end
          end
        | _ -> failwith "l2c: compile function: function is not well formed"
      end
    | None -> None
  in
  coloring_spill_loop (Some f_expr)


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

let () =
  match Sys.argv with
  | [|_; filename|] ->
    let print_result = function
      | Some l2_prog -> SExpr.print_sexpr_indent [l2_prog]
      | None -> print_endline "\"could not register allocate main\""
    in
    List.iter (fun p -> print_result @@ compile_program p) (parse_file filename)
  | _ -> ()
