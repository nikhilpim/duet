open Syntax
module IntPair = SrkUtil.IntPair
module WG = WeightedGraph
module M = BatMap.Make(IntPair)
module V = Linear.QQVector

let bounding_model context 
    rg algebra symbol_pairs gen_pair formula_to_transition transition_to_formula is_upper_bound start_call = 
  let connected_component = start_call :: (WG.RecGraph.scc_calls rg start_call |> List.filter (fun c -> c != start_call)) in
  let call_edges = WG.RecGraph.call_edges rg in 

  let sym_one = gen_pair "one" in 
  let counter = gen_pair "ctr" in 
  let flag = gen_pair "flag" in 
  let symbol_pairs = sym_one :: symbol_pairs in 
  let deltas = List.map (fun call ->
      List.mapi (fun i _ ->
          let var_name = (string_of_int i) ^ "_delta_" ^ (IntPair.show call) in 
          gen_pair var_name
        ) symbol_pairs
    ) connected_component in 

  let algebra' bounded_call x = 
    match x with 
      | `Edge e -> if M.mem e call_edges 
          then (
            let queried_call = M.find e call_edges in 
            let update_formulas = List.fold_left2 
              (fun acc call call_deltas -> 
                  let detract = List.map2 (fun (delta, delta') (x, _) -> 
                      mk_eq context (mk_const context delta') 
                        (mk_add context [mk_const context delta; mk_neg context (mk_const context x)])
                    ) call_deltas symbol_pairs |> mk_and context in
                  let donothing = List.map (fun (delta, delta') ->
                    mk_eq context (mk_const context delta) (mk_const context delta'))
                    call_deltas |> mk_and context in 
                  (if (call = queried_call) 
                    then (if is_upper_bound then mk_or context [detract; donothing] else detract)
                    else donothing) :: acc
                ) 
              [] connected_component deltas in
            let aux_update = if (queried_call = bounded_call)
              then [mk_eq context (mk_const context (snd counter)) (mk_add context [mk_const context (fst counter); mk_one context]);
             mk_eq context (mk_const context (snd flag)) (mk_one context)]
              else [mk_eq context (mk_const context (fst counter)) (mk_const context (snd counter));
              mk_eq context (mk_const context (fst flag)) (mk_const context (snd flag))] in 
            formula_to_transition (counter :: flag :: (List.flatten deltas @ symbol_pairs)) (mk_and context (aux_update @ update_formulas))
          )
          else algebra x
      | _ -> algebra x in
    
    let intra_summaries = List.map (fun bounded_call ->
      List.map (fun current_call -> 
        let path = WG.path_weight (WG.RecGraph.path_graph rg) (fst current_call) (snd current_call) in 
        let summary = Pathexpr.eval ~algebra:(algebra' bounded_call) path |> transition_to_formula in
        let delta_init = List.fold_left2 (fun acc call call_deltas -> 
            (if (call = current_call)
              then List.map2 (fun (delta, _) (x, _) -> mk_eq context (mk_const context delta) (mk_const context x)) call_deltas symbol_pairs
              else List.map (fun (delta, _) -> mk_eq context (mk_const context delta) (mk_zero context)) call_deltas)
          :: acc) [] connected_component deltas |> List.flatten in
        let aux_init = [mk_eq context (mk_const context (fst sym_one)) (mk_one context);
                        mk_eq context (mk_const context (fst counter)) (mk_zero context);
                        mk_eq context (mk_const context (fst flag)) (mk_zero context);
                        if is_upper_bound then mk_or context  [mk_eq context (mk_const context (snd flag)) (mk_one context); mk_lt context (mk_zero context) (mk_const context (snd counter))] else mk_true context;
                        ] in 
        mk_and context (summary :: (delta_init @ aux_init))
        ) connected_component |> mk_or context (* note: instead of computing individual UB_p and intersecting them, we "or" each F and compute UB directly. *)
      ) connected_component in
    
    let polyhedron_basis = (snd counter) :: (List.flatten deltas |> List.map snd) in let polyhedra = List.map (fun summary -> let basis_array = Array.of_list (List.map (mk_const context) polyhedron_basis) in 
    let summary = summary |> Nonlinear.linearize context |> rewrite context ~down:(pos_rewriter context) |> Syntax.eliminate_floor_mod_div context in 
        let hull = Abstract.conv_hull context summary basis_array |> Polyhedron.of_dd in
        let cs = CoordinateSystem.mk_empty context in 
        List.iter (fun sym -> CoordinateSystem.admit_cs_term cs (`App (sym, []))) polyhedron_basis; 
        let poly = Polyhedron.dual_cone (List.length polyhedron_basis) hull in 
        Polyhedron.meet 
          (Polyhedron.of_formula cs (mk_eq context (mk_const context (snd counter)) 
            (if is_upper_bound then (mk_neg context (mk_one context)) else (mk_one context)))) 
          poly  
      ) intra_summaries in

    (* List.iter (fun (s, _) -> print_string (SrkUtil.mk_show (Syntax.pp_expr_unnumbered context) (Syntax.mk_const context s))) symbol_pairs; *)
    let vec_to_term v = V.fold (fun ind v acc -> 
      (
      let value = match ind with 
      | 0 -> mk_zero context
      | 1 -> mk_real context v
      | _ -> if ind < (1 + List.length symbol_pairs) 
        then (mk_mul context [mk_real context v; mk_const context (List.nth symbol_pairs (ind - 1) |> fst)])
        else mk_zero context in 
      if is_upper_bound then (value) else (mk_neg context value)) :: acc
      ) v [] |> mk_add context in 
  
    let bound_formulas = List.map (fun ub ->
        let guard, lims = BatEnum.fold (fun (guard, lims) (typ, v) ->
            match typ with 
              | `Vertex ->
                guard, (vec_to_term v) :: lims
              | `Ray ->
                if (is_upper_bound) then
                mk_leq context (mk_zero context) (vec_to_term v) :: guard, lims 
                else mk_leq context (vec_to_term v) (mk_zero context) :: guard, lims
              | `Line -> 
                mk_eq context (mk_zero context) (vec_to_term v) :: guard, lims
          ) ([], []) (DD.enum_generators (Polyhedron.dd_of (List.length polyhedron_basis) ub)) in 
        mk_and context guard, lims
      ) polyhedra in 
    
    List.combine connected_component bound_formulas

    
