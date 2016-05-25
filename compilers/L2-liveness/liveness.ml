open SExpr
open Utils_l2

module SS = Set.Make(String)

module List = struct
    include List
    let rec take n lst = match n with
    | 0 -> []
    | _ ->
      match lst with
      | [] -> []
      | hd :: rst -> hd :: take (n-1) rst
  end;;

(* type gen_and_kill = {size : int; gens : SS.t array; kills : SS.t array} *)
type two_sets = {size : int; first : SS.t array; second : SS.t array}

let calc_gen_and_kill insts_arr =
  (* exclude rsp *)
  let foo s = if not (is_runtime_calls s) && is_w s then [s] else [] in
  let gen_and_kill_each_inst = function
    | Expr [Atom w; Atom "<-"; Atom s] ->
      let gen = foo s and kill = [w] in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom w; Atom "<-"; Expr [Atom "mem"; Atom x; Atom n8]] ->
      let gen = foo x and kill = [w] in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Expr [Atom "mem"; Atom x; Atom n8]; Atom "<-"; Atom s] ->
      let gen = foo x @foo s and kill = [] in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom w; Atom op; Atom t_sx_num] when is_op op ->
      let gen = [w] @foo t_sx_num and kill = [w] in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom w; Atom "<-"; Atom t1; Atom cmp; Atom t2] ->
      let gen = foo t1 @foo t2 and kill = [w] in
      (SS.of_list gen, SS.of_list kill)
    | Atom labl
    | Expr [Atom "goto"; Atom labl] ->
      (SS.empty, SS.empty)
    | Expr [Atom "cjump"; Atom t1; Atom cmp; Atom t2; Atom lable1; Atom lable2] ->
      let gen = foo t1 @foo t2 and kill = [] in
      (SS.of_list gen, SS.of_list kill)
  (*
    | Expr [Atom "call"; Atom "print"; Atom "1"] ->
      let gen = List.take 1 args and kill = caller_save @result in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom "call"; Atom "allocate"; Atom "2"] ->
      let gen = List.take 2 args and kill = caller_save @result in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom "call"; Atom "array-error"; Atom "2"] ->
      let gen = List.take 2 args and kill = caller_save @result in
      (SS.of_list gen, SS.of_list kill)
  *)
    | Expr [Atom "call"; Atom u; Atom nat] ->
      let n = min (int_of_string nat) 6 in
      let gen = List.take n args @foo u and kill = caller_save @result in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom "tail-call"; Atom u; Atom nat] ->
      let n = min (int_of_string nat) 6 in
      let gen = List.take n args @foo u @callee_save and kill = [] in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom "return"] ->
      let gen = result @callee_save and kill = [] in
      (SS.of_list gen, SS.of_list kill)
    | Expr [Atom w; Atom "<-"; Expr [Atom "stack-arg"; Atom n8]] ->
      let kill = [w] in
      (SS.empty, SS.of_list kill)
    | _ -> failwith "liveness error: not a valid instruction"
  in
  let len = Array.length insts_arr in
  let gen_and_kill_sets = {size=len; first=Array.make len SS.empty; second=Array.make len SS.empty} in
  begin
    for i = 0 to len - 1 do
      let sets = gen_and_kill_each_inst insts_arr.(i) in
      let gen = fst sets and kill = snd sets in
      begin
        gen_and_kill_sets.first.(i) <- gen;
        gen_and_kill_sets.second.(i) <- kill
      end
    done;
    gen_and_kill_sets
  end

let calc_label_table insts_arr =
  let s = Array.length insts_arr in
  let label_tbl = Hashtbl.create s in
  for i=0 to s-1 do
    match insts_arr.(i) with
    | Atom labl when is_label labl -> Hashtbl.add label_tbl labl i
    | _ -> ()
  done;
  label_tbl

let calc_in_and_out insts_arr =
  let gen_and_kill_sets = calc_gen_and_kill insts_arr in
  let s = gen_and_kill_sets.size
  and gen_arr = gen_and_kill_sets.first
  and kill_arr = gen_and_kill_sets.second in
  let lable_tbl = calc_label_table insts_arr in
  (* redundant dummy node in the end of in and out array for convience*)
  let in_arr = Array.make (s+1) SS.empty and out_arr = Array.make (s+1) SS.empty in
  let rec fix_point () =
    let union_of_succ i =
      match insts_arr.(i) with
      (* jmp direct to lable one successful *)
      | Expr [Atom "goto"; Atom labl] -> in_arr.(Hashtbl.find lable_tbl labl)
      (* conditioncal jump 2 successor *)
      | Expr [Atom "cjump"; Atom t1; Atom cmp; Atom t2; Atom lable1; Atom lable2] ->
        SS.union in_arr.(Hashtbl.find lable_tbl lable1) in_arr.(Hashtbl.find lable_tbl lable2)
      (* return and tail-call end of control flow *)
      | Expr [Atom "return"]
      | Expr [Atom "call"; Atom "array-error"; Atom "2"]
      | Expr [Atom "tail-call"; _; _] -> SS.empty
      (* regular one, successor are next *)
      | _ -> in_arr.(i+1) in
    let iteration () =
      let is_changed = ref false in
      for i=s-1 downto 0 do
        let in_prime = in_arr.(i) and out_prime = out_arr.(i) in
        out_arr.(i) <- union_of_succ i;
        in_arr.(i) <- SS.union gen_arr.(i) (SS.diff out_arr.(i) kill_arr.(i));
        if not ((SS.equal in_arr.(i) in_prime) && (SS.equal out_arr.(i) out_prime)) then is_changed := true
      done;
      !is_changed
    in
    if iteration () then
      fix_point ()
    else
      {size=s; first=Array.sub in_arr 0 s; second=Array.sub out_arr 0 s}
  in
  fix_point ()

let liveness_analysis = function
  | Expr (n :: vars :: spills :: insts) ->
    let insts_arr = Array.of_list insts in
    calc_in_and_out insts_arr
  | _ -> failwith "liveness: liveness_anaylysis: input not a valid function expr"

let print_sets set_arr name =
  let set_lst = Array.to_list set_arr in
  let str_lst = List.map (fun ss -> "(" ^ (String.concat " " (SS.elements ss)) ^ ")") set_lst in
  let output = String.concat "\n" str_lst in
  print_endline ("(" ^ name);
  print_string (output ^ ")")

let print_two_sests {size; first; second} n1 n2 =
  begin
  print_string "(";
  print_newline (print_sets first n1);
  print_sets second n2;
  print_endline ")"
  end

(* 
let run_test () =
  let in_and_outs s = List.iter (fun f -> print_two_sests (liveness_analysis f) "in" "out") (parse_string s) in
  let f0 = "(:f 0 0
            (x2 <- rdi)
            (x2 *= x2)
            (dx2 <- x2)
            (dx2 *= 2)
            (tx <- rdi)
            (tx *= 3)
            (rax <- dx2)
            (rax += tx)
            (rax += 4)
            (return))"
  in
  print_newline (in_and_outs f0)

let () =
  let iteration f = print_two_sests (liveness_analysis f) "in" "out" in
  match Sys.argv with
  | [|_; filename|] ->
    List.iter iteration (parse_file filename)
  | _ ->
    let func = read_line () in
    List.iter iteration (parse_string func)
    (* default input from stdin*)
*)
