open SExpr
open Graph
open Liveness
open Utils_l2

module G = Graph.Imperative.Graph.Concrete
    (struct
      type t = string
      let compare = Pervasives.compare
      let hash = Hashtbl.hash
      let equal = (=)
    end)

module StrMap = Map.Make(String)


let color_map_to_list map =
  StrMap.fold (fun k v acc -> (k, v) :: acc) map []
  |> List.rev
  |> List.map (fun (k, v) -> "(" ^ k ^ " " ^ v ^ ")")

let print_graph ig =
  let acc v lst =
    ("(" ^ String.concat " " (v :: (G.succ ig v)) ^ ")") :: lst in
  let g_sort_lst = G.fold_vertex acc ig [] |> List.sort G.V.compare in
  "(" ^ String.concat "\n" g_sort_lst ^ ")"
  |> print_endline


let build_interference_graph inst_arr =
  let gen_and_kill_sets = calc_gen_and_kill inst_arr in
  let in_and_out_sets = calc_in_and_out inst_arr in
  let gen_arr = gen_and_kill_sets.first
  and kill_arr = gen_and_kill_sets.second
  and in_arr = in_and_out_sets.first
  and out_arr = in_and_out_sets.second
  and size = in_and_out_sets.size in
  let all_vars =
    let combine_sets = Array.fold_left (fun acc s -> SS.union acc s) SS.empty in
    let combine_two_sets_arr lhs rhs = SS.union (combine_sets lhs) (combine_sets rhs) in
    SS.filter is_var (combine_two_sets_arr gen_arr kill_arr) in
  let add_edges_from_list ig lst1 lst2 except =
    let arr1 = Array.of_list lst1
    and arr2 = Array.of_list lst2 in
    let len1 = Array.length arr1
    and len2 = Array.length arr2 in
    for i=0 to len1-1 do
      for j=0 to len2-1 do
        if arr1.(i) <> arr2.(j) then
          if not (List.mem (arr1.(i), arr2.(j)) except)
          then G.add_edge ig arr1.(i) arr2.(j)
      done
    done
  in
  let add_edges_from_sets ig set1 set2 =
    add_edges_from_list ig (SS.elements set1) (SS.elements set2) in
  let add_edges_per_inst ig inst lives k o =
    let add_lives_and_kill_out ig lives k o except = begin
      add_edges_from_sets ig lives lives except;
      add_edges_from_sets ig k o except
    end in
    match inst with
    | Expr [Atom w; Atom "<-"; Atom s] when is_w w && is_w s ->
      let expt = [(w, s); (s, w)] in
      add_lives_and_kill_out ig lives k o expt
    | Expr [Atom w; Atom sop; Atom sx_or_num] when (is_sop sop && is_var sx_or_num) ->
      begin
        add_lives_and_kill_out ig lives k o [];
        add_edges_from_list ig [sx_or_num] all_registers_except_rcx []
      end
    | _ -> add_lives_and_kill_out ig lives k o []
  in
  let ig = G.create () in begin
    (* add all registers and all vars as nodes *)
    begin SS.iter (fun v -> G.add_vertex ig v) all_vars;
      add_edges_from_list ig all_registers all_registers []
    end;
    (* add interperece graph from in and out and kill *)
    begin add_edges_per_inst ig inst_arr.(0) in_arr.(0) kill_arr.(0) out_arr.(0);
      for i=1 to size-1 do
        add_edges_per_inst ig inst_arr.(i) out_arr.(i) kill_arr.(i) out_arr.(i)
      done
    end;
    (ig, all_vars)
  end


let graph_color original_ig =
  let nb_colors = List.length all_registers in
  let vertex_to_remove a_ig =
    let fold_f v res =
      if is_var v then
      let degree = G.out_degree a_ig v in
      match res with
      | Some (_, res_degree) ->
        if degree < nb_colors && degree > res_degree then Some (v, degree) else res
      | None ->
        if degree < nb_colors then Some (v, degree) else res
      else
        res
    in
    G.fold_vertex fold_f a_ig None
  in
  (* generate nodes serials *)
  let rec pick_nodes_recr mut_ig a_stack =
    (* try to remove all the nodes *)
    if G.nb_vertex mut_ig = List.length all_registers then
      Some a_stack
    else begin
      match vertex_to_remove mut_ig with
      | Some (v, d) -> begin
          (* print_endline ("node: " ^ v ^ " degree: " ^ string_of_int d);
          List.iter (fun s -> print_string (s ^ " ")) (G.succ original_ig v);
          print_newline ();
          List.iter (fun s -> print_string (s ^ " ")) (G.succ mut_ig v);
             print_newline (); *)
          Stack.push (v, G.succ mut_ig v) a_stack;
          G.remove_vertex mut_ig v;
          pick_nodes_recr mut_ig a_stack
        end
      | None -> None
    end
  in
  let rec generate_mapping_recr reg_m a_stack =
    if Stack.is_empty a_stack then
      StrMap.filter (fun k v -> is_var k) reg_m
    else begin
      let v, succs = Stack.pop a_stack in
      if is_var v then begin
        let pred e =
          let f acc e =
            try SS.add (StrMap.find e reg_m) acc
            with Not_found -> failwith ("graph_color: generate_mapping_recr: error " ^ e ^ " not found")
          in
          let assigned_colors = List.fold_left f SS.empty succs in
          not (SS.mem e assigned_colors)
        in
        let color =
          try List.find pred all_registers
          with Not_found ->
            begin
              print_graph original_ig;
              failwith ("graph_color: generate_mapping_recr: " ^ "error: when mapping variable: " ^ v)
            end
        in
        let nreg_m = StrMap.add v color reg_m in
        begin
          (* print_endline ("assign variable: " ^ v ^ " to register: " ^ color); *)
          generate_mapping_recr nreg_m a_stack
        end
      end
      else
        generate_mapping_recr (StrMap.add v v reg_m) a_stack
    end
  in
  (* for sanity  check*)
  let mut_ig = G.copy original_ig in
  let init_mapping = List.fold_left (fun acc e -> StrMap.add e e acc) StrMap.empty all_registers in
  match pick_nodes_recr mut_ig (Stack.create ()) with
  | Some a_stack -> Some (generate_mapping_recr init_mapping a_stack)
  | None -> None


(*
let run_test () =
  let test = function
    | Expr (Atom l :: Atom vars :: Atom spill :: insts) ->
      print_graph (build_interference_graph (Array.of_list insts))
    | _ -> failwith "run test not a function"
  in
  let t0 = parse_string "(:f 0 0 (x <- 1) (rax += x) (return))"
  in
  List.iter test t0

let () = match Sys.argv with
  | [|_; filename|] ->
    let foo = function
    | Expr (Atom l :: Atom vars :: Atom spill :: insts) ->
      let ig = build_interference_graph (Array.of_list insts) in
      let mapping = graph_color ig in begin
        print_graph ig;
        print_newline (
          print_string (
            match mapping with
            | Some color_mapping -> "(" ^ String.concat " " (color_map_to_list color_mapping) ^ ")"
            | None -> "#f"
          ))
      end
    | _ -> failwith "run test not a function"
    in
    let func = parse_file filename in
    List.iter foo func
  | _ -> run_test ()
*)
