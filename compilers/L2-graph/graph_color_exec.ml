open SExpr
open Graph_color

let () = match Sys.argv with
  | [|_; filename|] ->
    let foo = function
    | Expr (Atom l :: Atom vars :: Atom spill :: insts) ->
      let ig, _ = build_interference_graph (Array.of_list insts) in
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
  | _ -> ()
