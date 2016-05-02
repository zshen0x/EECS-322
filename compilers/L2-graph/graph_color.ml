open SExpr
open Graph
open Liveness

module G = Graph.Imperative.Graph.Concrete
    (struct
      type t = string
      let compare = Pervasives.compare
      let hash = Hashtbl.hash
      let equal = (=)
    end)

module StrMap = Map.Make(String)

let args = ["rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9"]
let result = ["rax"]
let caller_save = ["r10"; "r11"; "r8"; "r9"; "rax"; "rcx"; "rdi"; "rdx"; "rsi"]
let calee_save = ["r12"; "r13"; "r14"; "r15"; "rbp"; "rbx"]
let all_registers = ["r10"; "r11"; "r12"; "r13"; "r14"; "r15"; "r8";
                     "r9"; "rax"; "rbp"; "rbx"; "rcx"; "rdi"; "rdx"; "rsi"]
let all_registers_except_rcx = ["r10"; "r11"; "r12"; "r13"; "r14"; "r15"; "r8";
                                "r9"; "rax"; "rbp"; "rbx"; "rdi"; "rdx"; "rsi"]


let build_interference_graph inst_arr =
  let gen_and_kill_sets = calc_gen_and_kill inst_arr in
  let in_and_out_sets = calc_in_and_out inst_arr in
  let kill_arr = gen_and_kill_sets.second
  and in_arr = in_and_out_sets.first
  and out_arr = in_and_out_sets.second
  and size = in_and_out_sets.size in
  (*
  let add_full_graph_from_list ig lst =
    let arr = Array.of_list lst in 
    let s = Array.length arr in
    for i=0 to s-1 do
      for j=i+1 to s-1 do
        G.add_edge ig arr.(i) arr.(j)
      done
    done
  in
  let add_full_graph ig set =
    add_full_graph_from_list ig (Liveness.SS.elements set)
  in
  *)
  let add_graph_from_list ig lst1 lst2 except =
    let arr1 = Array.of_list lst1
    and arr2 = Array.of_list lst2 in
    let s1 = Array.length arr1
    and s2 = Array.length arr2 in
    for i=0 to s1-1 do begin
      G.add_vertex ig arr1.(i);
      for j=0 to s2-1 do begin
        (* first add all vertex *)
        G.add_vertex ig arr2.(j);
        match except with
        | Some expt ->
          if (arr1.(i) <> arr2.(j)) && expt <> (arr1.(i), arr2.(j)) && expt <> (arr2.(j), arr1.(i))
          then G.add_edge ig arr1.(i) arr2.(j)
        | None -> if arr1.(i) <> arr2.(j) then G.add_edge ig arr1.(i) arr2.(j)
      end
      done
    end
    done
  in
  let add_graph ig set1 set2 =
    add_graph_from_list ig (SS.elements set1) (SS.elements set2)
  in
  let add_graph_per_insts ig inst lives k o =
    match inst with
    | Expr [Atom w; Atom "<-"; Atom s] when is_w w && is_w s ->
      let excpet = Some (w, s) in
      begin
        add_graph ig lives lives excpet;
        add_graph ig k o excpet
      end
    | Expr [Atom w; Atom sop; Atom sx_or_num] when (is_sop sop && is_var sx_or_num) ->
      begin
        add_graph ig lives lives None;
        add_graph ig k o None;
        add_graph_from_list ig [sx_or_num] all_registers_except_rcx None
      end
    | _ -> begin
        add_graph ig lives lives None;
        add_graph ig k o None
      end
  in
  let ig = G.create () in begin
    (* register are against each othter *)
    add_graph_from_list ig all_registers all_registers None;
    (* for first instruction 
    add_graph ig in_arr.(0) in_arr.(0);
    add_graph ig kill_arr.(0) out_arr.(0);
    deal_special_case ig inst_arr.(0);
    *)
    add_graph_per_insts ig inst_arr.(0) in_arr.(0) kill_arr.(0) out_arr.(0);
    for i=1 to size-1 do
      (*
      begin
      add_graph ig out_arr.(i) out_arr.(i);
      add_graph ig kill_arr.(i) out_arr.(i);
      deal_special_case ig inst_arr.(i)
      end
      *)
      add_graph_per_insts ig inst_arr.(i) out_arr.(i) kill_arr.(i) out_arr.(i)
    done;
      ig
  end

let graph_color ig =
  let nb_colors = List.length all_registers in
  let vertex_to_remove a_ig =
    let fold_f v res =
      if is_var v then begin
        let degree = G.out_degree a_ig v in
        match res with
        | Some (_, res_degree) ->
          if degree < nb_colors && degree > res_degree then Some (v, degree) else res
        | None ->
          if degree < nb_colors then Some (v, degree) else res
      end
      else res
    in
    G.fold_vertex fold_f a_ig None
  in
  (* generate nodes serials *)
  let rec pick_nodes_recr a_ig a_stack =
    (* always take variables in vertex_to_remove, if only regs left stop *)
    if G.nb_vertex a_ig = nb_colors then Some a_stack
    else begin
      match vertex_to_remove a_ig with
      | Some (v, _) -> begin
          Stack.push (v, G.succ a_ig v) a_stack;
          G.remove_vertex a_ig v;
          pick_nodes_recr a_ig a_stack
        end
      | None -> None
    end
  in
  let rec generate_mapping_rec var_mapping all_mapping a_stack =
    if Stack.is_empty a_stack then var_mapping
    else begin let v, succs = Stack.pop a_stack in
      let pred e =
        let f acc e =
          try SS.add (StrMap.find e all_mapping) acc
          with Not_found -> acc
        in
        let assigned_colors = List.fold_left f SS.empty succs in
        not (SS.mem e assigned_colors)
      in
      let color = List.find pred all_registers in
      let new_var_mapping = StrMap.add v color var_mapping
      and new_all_mapping = StrMap.add v color all_mapping in
      generate_mapping_rec new_var_mapping new_all_mapping a_stack
    end
  in
  (* sanity for check*)
  let ig_copy = G.copy ig in
  let init_mapping = List.fold_left (fun acc e -> StrMap.add e e acc) StrMap.empty all_registers in
  begin match pick_nodes_recr ig_copy (Stack.create ()) with
    | Some a_stack -> Some (generate_mapping_rec StrMap.empty init_mapping a_stack)
    | None -> None
  end

let color_map_to_list map =
  StrMap.fold (fun k v acc -> (k, v) :: acc) map []
  |> List.rev
  |> List.map (fun (k, v) -> "(" ^ k ^ " " ^ v ^ ")")

let print_graph ig =
  let acc v lst =
    ("(" ^ String.concat " " (v :: (G.succ ig v)) ^ ")") :: lst
  in
  let g_sort_lst = G.fold_vertex acc ig [] |> List.sort G.V.compare in
  "(" ^ String.concat "\n" g_sort_lst ^ ")"
  |> print_endline

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
      print_graph (build_interference_graph (Array.of_list insts));
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
