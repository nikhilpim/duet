open Arrayify
open Boogie_driver  (* your parser entry point *)
open Boogieir
let numeric_test () = (
  let module T = Srk.Transition.Make(Global.Ctx)(Variable.Var) in 
  print_string "\n\n Pipelining file into srk: test/files/boogie/numeric1.bpl \n\n\n";
  let filename = "/Users/np6641/dev/duet/arrayify/test/files/boogie/numeric1.bpl" in
  let prog = parse filename in 
  let g = build_graph prog in 

  let ts = graph_to_transition_system g in 
  Srk.WeightedGraph.iter_edges (fun (v, w, v') -> 
      let weight_string = match w with
        | Srk.TransitionSystem.Weight t ->  Format.asprintf "%a" T.pp t
        | Srk.TransitionSystem.Call _ -> failwith "Unexpected call transition in numeric test" in 
      print_string (Printf.sprintf "Edge from %d to %d with weight %s\n" v v' weight_string)
    ) ts 
)  


let () = (
   let _ = numeric_test in
   numeric_test ();
)

