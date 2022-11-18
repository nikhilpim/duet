open Syntax 

module WG = WeightedGraph
module L = Linear
module Q = L.QQMatrix
module V = L.QQVector
module VS = L.QQVectorSpace
module P = Pathexpr
module A = Abstract
module TF = TransitionFormula

module IntPair = WG.IntPair

module IS = Set.Make(IntPair)
module M = BatMap.Make(IntPair)
module N = IntPair
module T = IntPair
module CFG = Grammar.MakeCFG(N)(T)

type 'a label =
  | Weight of 'a
  | Call of int * int

module CfgSummarizer 
  (C : sig
    type t
    val context : t context
  end)
  (Var : sig 
    type t
    val fresh : string -> t
    val compare : t -> t -> int
    val of_symbol : symbol -> t option
    val is_global : t -> bool
  end)
  (T : sig 
    type t
    type var = Var.t
    val transform : t -> (var * C.t arith_term) BatEnum.t
    val symbol_pair: var -> symbol * symbol 
    val mem_transform : var -> t -> bool
    val construct: C.t formula -> (var * C.t arith_term) list -> t
    val to_transition_formula : t -> C.t TF.t
    val mul : t -> t -> t
    val add : t -> t -> t
    val zero : t
    val one : t
    val star : t -> t
    val exists : (var -> bool) -> t -> t
  end) 
  (G : sig
    val graph : T.t label WG.weighted_graph
    val src : int
    val path_graph : WG.RecGraph.t -> P.simple P.t WG.weighted_graph
    val call_edges : WG.RecGraph.t -> IntPair.t M.t
    val context : WG.RecGraph.t -> P.context 
    val fold_reachable_edges : (int -> int -> 'a -> 'a) -> 'b WG.weighted_graph -> int -> 'a -> 'a
    val scc : IntPair.t -> WG.RecGraph.t -> IntPair.t list
  end
  ) = struct 

  module S = Set.Make(Var)
  let srk = C.context
  let const = mk_const srk
  let real = mk_real srk 
  let add = mk_add srk
  let sub = mk_sub srk
  let mul = mk_mul srk 
  let neg = mk_neg srk
  let eq = mk_eq srk
  let and1 = mk_and srk 
  let or1 = mk_or srk
  let if1 = mk_if srk
  let leq = mk_leq srk
  let lt = mk_lt srk
  let zero = mk_zero srk
  let one = mk_one srk

  let _print_formula form = print_string"\n\n"; print_string (SrkUtil.mk_show (Syntax.pp_expr_unnumbered srk) form)
  let cut_first_term v = BatEnum.filter_map ((fun (e, d) -> if (d >= 1) then Some (e, d-1) else None)) 
    (V.enum v) |> V.of_enum 

  (* Generates the recursive graph model to be analyzed *)
  let rg = WG.fold_vertex
    (fun v rg -> WG.RecGraph.add_vertex rg v)
      G.graph
      (WG.RecGraph.empty ())
    |> WG.fold_edges (fun (u, w, v) rg ->
        match w with
        | Call (en,ex) ->
            WG.RecGraph.add_call_edge rg u (en,ex) v
        | Weight _ -> WG.RecGraph.add_edge rg u v)
      G.graph

  let call_edges = G.call_edges rg

  let algebra = function
    | `Edge (u,v) ->
       begin match WG.edge_weight G.graph u v with
       | Weight w -> w
       | Call _ -> assert false
       end
    | `Add (x, y) -> T.add x y
    | `Mul (x, y) -> T.mul x y
    | `Star x -> T.star x
    | `Segment x -> T.exists Var.is_global x
    | `Zero -> T.zero
    | `One -> T.one

    (* All global variables in the input graph *)
  let global_variables = WG.fold_edges (fun (_, w, _) s -> 
    match w with 
      | Weight t -> BatEnum.fold (fun s (var, _) -> if Var.is_global var then (S.add var s) else s) s (T.transform t)
      | Call _ -> s
    ) G.graph S.empty 

  let transition_to_formula t = 
    let tf = T.to_transition_formula t in 
    let unincluded_globals = S.filter (fun var -> not (T.mem_transform var t)) global_variables in 
    (S.fold (fun v ls -> 
      let (pre, post) = T.symbol_pair v in
      (eq (const pre) (const post)) :: ls) unincluded_globals []) 
      |> List.cons (TF.formula tf)
      |>  and1
  
  let formula_to_transition formula transform_symbols = 
    List.map (fun (pre, post) -> 
      match Var.of_symbol pre with 
      | Some var -> (var, const post)
      | None -> assert false) transform_symbols
    |> T.construct formula

  let symbol_pairs = List.map T.symbol_pair (S.elements global_variables)
  let dim = (List.length symbol_pairs) + 1

  (* To get more descriptive VASR summaries, we use a simplified version of the normal path graph in we only 
  consider the start vertices and vertices belonging to calls.  *)
  let path_graph = WG.cut_graph (G.path_graph rg) 
  (G.src::M.fold (fun (v1, v2) (e1, e2) ls -> v1 :: v2 :: e1 :: e2 :: ls) call_edges []
  |> List.fold_left (fun acc item -> if List.mem item acc then acc else item :: acc) [])
  let path_graph = WG.fold_edges (fun (v1, e, v2) g -> 
    if not (M.mem (v1, v2) call_edges) && Syntax.is_false (P.eval ~algebra e |> transition_to_formula) then (WG.remove_edge g v1 v2) else g
    ) path_graph path_graph
  

  (* ===================== RECURSIVE GRAPH -> VASR-WEIGHTED CFG ===================== *)
  (* Uses vanishing space algorithm to compute VASR transitions simulating each edge in the graph *)
  let generate_vas_transforms () = 
    let addition_basis = mk_one srk
    :: List.map (fun (pre, post) -> sub (const pre) (const post)) symbol_pairs in 
    let reset_basis = mk_one srk 
    :: List.map (fun (_, post) -> neg (const post)) symbol_pairs in

    WG.fold_edges (fun (v_1, edge, v_2) (add_summaries, reset_summaries, to_align) ->
      if not (M.mem (v_1, v_2) call_edges) then 
      let formula = P.eval ~algebra edge |> transition_to_formula in 
      _print_formula formula; print_string (" belongs to "^IntPair.show (v_1, v_2));
      let aff = A.vanishing_space srk formula (Array.of_list (addition_basis)) in
      let res = A.vanishing_space srk formula (Array.of_list (reset_basis)) in
      let ali_aff, ali_res = List.map cut_first_term aff, List.map cut_first_term res in
      let e = (v_1, v_2) in
      (M.add e (VS.matrix_of aff) add_summaries,
      M.add e (VS.matrix_of res) reset_summaries,
      M.add e (VS.matrix_of ali_aff, VS.matrix_of ali_res) to_align) 
    else (add_summaries, reset_summaries, to_align)
    ) path_graph (M.empty, M.empty, M.empty)

  (* Given a list of edges to compute consistent summaries for, does a binary search over all combinations of resets
  and additions per edge to compute a best consistent transform. *)
  let rec binary_coproduct edges current_abstraction tracking rectified_summaries 
    (add_summaries, reset_summaries, to_align) = 
    if Q.equal current_abstraction Q.zero then (rectified_summaries) else 
    match edges with 
    | [] -> 
      (* Once we are out of edges, add the consistent summaries to rectified_summaries *)
      List.fold_left (fun rectified_summaries (is_reset, edge, matrix) ->
        let rows = BatEnum.fold (fun ls (_, r) -> (r, is_reset) :: ls) [] (Q.rowsi matrix) in 
        if M.mem edge rectified_summaries then M.update edge edge (rows @ M.find edge rectified_summaries) rectified_summaries else
          M.add edge rows rectified_summaries
      ) rectified_summaries tracking
    | edge :: tl ->
      (* If there is still an edge, recursively compute summaries that are consistent 
    with the resets of the edge and with the additions of the edge *)
      let (aff, res) = M.find edge to_align in

      let c, d = L.pushout aff current_abstraction in 
      let new_tracking = List.map (fun (is_reset, edge, matrix) -> (is_reset, edge, Q.mul d matrix)) tracking in 
      let rectified_summaries = binary_coproduct tl (Q.mul d current_abstraction)
        ((0, edge, Q.mul c (M.find edge add_summaries)) :: new_tracking) 
        rectified_summaries (add_summaries, reset_summaries, to_align) in 

      let c, d = L.pushout res current_abstraction in 
      let new_tracking = List.map (fun (is_reset, edge, matrix) -> (is_reset, edge, Q.mul d matrix)) tracking in 
      binary_coproduct tl (Q.mul d current_abstraction) 
      ((1, edge, Q.mul c (M.find edge reset_summaries)) :: new_tracking)
      rectified_summaries (add_summaries, reset_summaries, to_align)

  let get_rectified_summaries edges summaries = 
    let initialized = List.fold_left (fun acc e -> M.add e [] acc) M.empty edges in 
    binary_coproduct edges (Q.identity (List.init dim (fun v -> v))) []
      initialized summaries

  (* ===================== LINEAR BOUNDS ON CALL TREES ===================== *)
  (* Base case model of program in which all recursive calls are false *)
  let base_case_model = WG.map_weights (fun v1 weight v2 ->
      if M.mem (v1, v2) call_edges then P.mk_zero (G.context rg) 
      else weight
    ) path_graph

  let base_case (call_start, call_end) = 
    let path = WG.path_weight base_case_model call_start call_end in 
    P.eval ~algebra path |> transition_to_formula
  
  (* Recursive case model of a program. Creates dummy entry and exit nodes and delta variables for each global variable. 
  Each call edge is replaced by two edges, one going to the next node and one going directly to the exit. In either case, 
  the edge is weighted by a formula decrementing each delta variable by its associated global.  *)
  let rec_case_model connected_component with_noop = 
    let symbol_pairs = (T.symbol_pair (Var.fresh "symbolic_one")) :: symbol_pairs in 
    let delta_vars = List.map (fun call -> 
      List.mapi (fun i _ ->
        let name = (string_of_int i) ^ "_delta_" ^ (IntPair.show call) in 
        T.symbol_pair (Var.fresh name)) symbol_pairs
      ) connected_component in 
    let call_to_delta = List.fold_left2 (fun d call delta -> M.add call delta d)
     M.empty connected_component delta_vars in
    
    let (graph, summaries, dummies, _) = List.fold_left (fun (graph, summaries, dummies, i) (en, ex) ->
      let setting_formula = List.mapi (fun index ls ->
        if index = i then 
          List.map2 (fun (_, delta_p) (sym, _) ->
            eq (const delta_p) (const sym)) ls symbol_pairs
          else List.map (fun (_, delta_p) -> 
            eq (const delta_p) (zero)) ls
        ) delta_vars 
      |> List.flatten |> and1 in
      let setting_transition = formula_to_transition setting_formula (List.flatten delta_vars) in
      let detracting_transition call = 
        print_string "\ndetracting!!!"; print_string (IntPair.show call);
        let detracting_formula = List.map2 (fun (delta, delta_p) (pre, _) ->
          or1 ([eq (const delta_p) (add [const delta; neg (const pre)])] 
            @ (if with_noop then [eq (const delta_p) (const delta)] else []))
          ) (M.find call call_to_delta) symbol_pairs |> and1 in 
        formula_to_transition detracting_formula (M.find call call_to_delta)
      in

      let maxv = WG.max_vertex graph in 
      let dummy_entry, dummy_exit = maxv + 1, maxv + 2 in 
      let dummies = M.add (en, ex) (dummy_entry, dummy_exit) dummies in 

      let graph = WG.add_vertex graph dummy_entry in 
      let graph = WG.add_vertex graph dummy_exit in 
      let graph = WG.add_edge graph dummy_entry (P.mk_edge (G.context rg) dummy_entry en) en in 
      let summaries = M.add (dummy_entry, en) setting_transition summaries in 
      print_string "\n rec case : ";M.iter (fun call _ -> print_string (IntPair.show call)) call_edges; print_string "\n";
      let (graph, summaries) = G.fold_reachable_edges (fun v1 v2 (graph, summaries) ->
        if (M.mem (v1, v2) call_edges) then (
          print_string (IntPair.show (v1, v2));
          let transition = detracting_transition (M.find (v1, v2) call_edges) in 
          let summaries = M.add (v1, v2) transition summaries in 
          let summaries = M.add (v1, dummy_exit) transition summaries in 
          (WG.add_edge graph v1 (P.mk_edge (G.context rg) v1 dummy_exit) dummy_exit, summaries)
        ) 
        else (graph, summaries)
        ) path_graph en (graph, summaries) in 
      (graph, summaries, dummies, i+1)
      ) (path_graph, M.empty, M.empty, 0) connected_component in 
      (graph, summaries, dummies, delta_vars)
  
  let recursive_case component with_noop = 
    let rec_model, summaries, dummies, deltas = rec_case_model component with_noop in 
    let modified_algebra x = 
      match x with 
      | `Edge e -> if M.mem e summaries 
        then M.find e summaries
        else algebra x
      | _ -> algebra x 
    in
    List.map2 (fun call delta_call -> 
      let (en, ex) = M.find call dummies in 
      let path = WG.path_weight rec_model en ex in 
      let path_formula = P.eval ~algebra:modified_algebra path |> transition_to_formula in 
      and1 [path_formula; eq (const (fst (List.hd delta_call))) one]) component deltas, deltas

  (* Generates upper bounds for calls. Returns a guard and a set of limits. The way to apply the bound is 
  (guard /\ for all lim in lims #(call) <= lim) \/ #(call) <= 1 *)
  let generate_upper_bounds call = 
    let component = call :: ((G.scc call rg) |> List.filter (fun e -> not (e = call))) in 
    let r, deltas = recursive_case component true in 
    let all_deltas = List.flatten deltas in 
    let delta_hulls = List.map (fun formula -> 
        let poly, csd = Abstract.convex_hull srk formula (List.map snd all_deltas) in 
        csd, poly
      ) r in 
    let common_hulls = List.map (fun i ->
      let current_call_hull = (List.nth delta_hulls i |> snd 
      |> Polyhedron.constrained_dual_cone (List.length all_deltas) ) 1 in 
      let other_hulls = List.filteri (fun j _ -> not (j = i)) delta_hulls
      |> List.map (fun (_, hull) -> Polyhedron.constrained_dual_cone (List.length all_deltas) hull 0) in 
      List.fold_left Polyhedron.meet current_call_hull other_hulls
      ) (List.init (List.length delta_hulls) (fun v -> v)) in 
    let deltas_per_call = List.length (List.hd deltas) in 
    let dot_symbols v = V.fold (fun dim v acc ->
      (if dim >= deltas_per_call then zero else 
        if dim = 0 then one else mul [real v; const (fst (List.nth symbol_pairs (dim - 1)))]) :: acc
      ) v [] |> add in 
    let bounds = List.map (fun hull ->
      let guard, lims = BatEnum.fold (fun (guard, lims) (typ, v) ->
        match typ with 
        | `Vertex -> guard, dot_symbols v :: lims
        | `Ray -> leq zero (dot_symbols v) :: guard, lims
        | `Line -> eq zero (dot_symbols v) :: guard, lims
        ) ([], []) (Polyhedron.enum_generators (List.length all_deltas) hull)
      in
      and1 guard, lims
      ) common_hulls in 
    List.combine component bounds 

  let generate_lower_bounds call = 
    let component = call :: ((G.scc call rg) |> List.filter (fun e -> not (e = call))) in 
    (* print_string "\n component "; List.iter (fun e -> print_string (IntPair.show e)) component;  *)
    let r, deltas = recursive_case component false in 
    let b = List.map (fun call -> base_case call) component in 
    let all_deltas = List.flatten deltas in 
    let delta_hulls = List.map (fun formula -> 
      let poly, csd = Abstract.convex_hull srk formula (List.map snd all_deltas) in 
      csd, poly
    ) r in 
    let csd, _poly = List.hd delta_hulls in 
    _print_formula (Polyhedron.to_formula csd _poly);
    let deltas_per_call = List.length (List.hd deltas) in 
    let input_hulls = List.mapi (fun i formula -> 
        let fresh = mk_symbol srk `TyReal in 
        let pad = List.fold_left (fun acc _ -> fresh :: acc) [] (List.init deltas_per_call (fun v -> v)) in 
        let left_pad = List.fold_left (fun acc _ -> pad @ acc) [] (List.init i (fun v -> v)) in 
        let right_pad = List.fold_left (fun acc _ -> pad @ acc) [] (List.init ((List.length component) - i - 1) (fun v -> v)) in 
        Abstract.convex_hull srk formula (left_pad @ (fresh :: (List.map fst symbol_pairs)) @ right_pad)
        |> fst 
      ) b in 
    (* _print_formula (Polyhedron.to_formula csd i); *)
    let common_hulls = List.map (fun i -> 
      let current_call_hull = (List.nth delta_hulls i 
      |> snd |> Polyhedron.constrained_dual_cone (List.length all_deltas)) (-1)
      in 
      let other_hulls = ((List.filteri (fun j _ -> not (j = i)) delta_hulls |> List.map snd) @ input_hulls)
        |> List.map (fun hull -> Polyhedron.constrained_dual_cone (List.length all_deltas) hull 0) in
      List.fold_left Polyhedron.meet current_call_hull other_hulls
      ) (List.init (List.length delta_hulls) (fun v -> v)) in 
    (* _print_formula (Polyhedron.to_formula csd c); *)
    let dot_symbols v = V.fold (fun dim v acc -> 
      (if dim >= deltas_per_call then zero else 
        if dim = 0 then one else mul [neg one; real v; const (fst (List.nth symbol_pairs (dim - 1)))]) :: acc
      ) v [] |> add in 
    let bounds = List.map (fun hull -> 
        let guard, lims = BatEnum.fold (fun (guard, lims) (typ, v) ->
          match typ with 
          | `Vertex -> print_string "\nvertex"; print_string (SrkUtil.mk_show V.pp v); guard, (dot_symbols v) :: lims
          | `Ray -> print_string "\nray"; print_string (SrkUtil.mk_show V.pp v); leq zero (dot_symbols v) :: guard, lims
          | `Line -> print_string "\nline"; print_string (SrkUtil.mk_show V.pp v); eq zero (dot_symbols v) :: guard, lims
        ) ([], []) (Polyhedron.enum_generators (List.length all_deltas) hull) in 
      and1 guard, lims
      ) common_hulls in 
    List.combine component bounds
    (* let symbolic_one = fst (List.hd deltas) in 
    let symbols_with_one = ((symbolic_one, symbolic_one) :: symbol_pairs) in
    let delta_hull, csd = Abstract.convex_hull srk r (List.map snd deltas) in 
    let input_hull, _ = Abstract.convex_hull srk (and1 [b; eq (const symbolic_one) one]) (List.map fst symbols_with_one) in 
    let common_hull, _ = Abstract.convex_hull srk (or1 [Polyhedron.to_formula csd delta_hull; Polyhedron.to_formula csd input_hull]) (List.map snd deltas) in 
    let lb_hull = Polyhedron.constrained_dual_cone (List.length deltas) common_hull (-1) in 
    let dot_symbols v = V.fold (fun dim v acc -> mul [neg one; real v; const (fst (List.nth symbols_with_one dim))] :: acc) v [] |> add in 
    let guard, lims = BatEnum.fold (fun (guard, lims) (typ, v) ->
      match typ with 
      | `Vertex -> guard, dot_symbols v :: lims 
      | `Ray -> leq (dot_symbols v) zero :: guard, lims
      | `Line -> eq zero (dot_symbols v) :: guard, lims
      ) ([], []) (Polyhedron.enum_generators (List.length deltas) lb_hull) in
    and1 ((eq (const symbolic_one) one) :: guard), lims *)

(* ===================== INTERVAL GRAMMAR ===================== *)
(* Generates a CFG model for the graph inputted to the module *)
  let gen_cfg src = 
    let cfg = CFG.empty (src, src) in 
    let wg = path_graph in 
    let nt_ends = M.fold (fun _ (_, call_end) acc -> call_end :: acc) call_edges [] in 

    (* To be applied to every edge (v_1, v_2) in the weighted graph. If the edge is a call edge, 
    adds N(v_1, end) -> N(call) N(v_2, end) where call is the call of (v_1, v_2) and end
    is every possible nonterminal target. If the edge is not a call edge, adds
    N(v_1, end) -> T(v_1, v_2) N(v_2)  *)
    let helper (v_1, _,  v_2) acc = 
      if M.mem (v_1, v_2) call_edges then
        let call = M.find (v_1, v_2) call_edges in
        List.fold_left (fun cfg e -> CFG.add_production cfg (v_1, e) [N call ; N (v_2, e)]) acc nt_ends
      else
        List.fold_left (fun cfg e -> CFG.add_production cfg (v_1, e) [T (v_1, v_2) ; N (v_2, e)]) acc nt_ends
    in 

    let cfg = WG.fold_edges helper wg cfg in
    (* Once we have reached the target of a particular nonterminal, that symbol is allowed 
    to go to null *)
    let cfg = List.fold_left (fun cfg e -> CFG.add_production cfg (e, e) []) cfg nt_ends in
    cfg 
  
  let get_coherence_classes rectified_summaries = 
    let reset_vectors = M.fold (fun _ summary ls -> List.map snd summary :: ls) rectified_summaries [] in 
    List.fold_left (fun classes reset_vector ->
      List.concat (List.map (fun cl ->
        let reset_dimensions = List.filter (fun index -> (List.nth reset_vector index) = 1) cl in 
        let unreset_dimensions = List.filter (fun index -> (List.nth reset_vector index) = 0) cl in 
        [reset_dimensions; unreset_dimensions]
        ) classes
        ) 
        |> List.filter (fun ls -> List.length ls > 0)
    ) [List.init (List.length (List.hd reset_vectors)) (fun v -> v)] reset_vectors

  let get_strong_labeling_constraints edges coherence_classes class_to_symbol edge_to_terminal rectified_summaries get_ith ind = 
    let num_classes = mk_int srk (List.length coherence_classes) in 
    List.map (fun cl ->
      let hd = List.hd cl in
      let reset_edges = List.filter (fun edge ->
        let summary = M.find edge rectified_summaries in 
        snd (List.nth summary hd) = 1
        ) edges in 
      let unreset_edges = List.filter (fun edge ->
        let summary = M.find edge rectified_summaries in 
        snd (List.nth summary hd) = 0) edges in 
      let permutation_symbol = class_to_symbol cl in 
      let valid_permutation = [leq zero permutation_symbol; lt permutation_symbol num_classes] in 
      let perm_must_reset = List.map (fun edge ->
        List.map (fun index ->
            let jth_term = get_ith (ind index index) edge |> edge_to_terminal in
            if1 (eq permutation_symbol (mk_int srk index))
              (eq jth_term zero)
          ) 
        (List.init (List.length coherence_classes) (fun v -> v))
      ) unreset_edges |> List.concat in 
      let no_resets_after_perm = List.map (fun edge ->
        List.map (fun index ->
          if1 (lt permutation_symbol (mk_int srk index))
            (and1 [eq zero (edge_to_terminal (get_ith index edge));
              if index < List.length coherence_classes then eq zero (edge_to_terminal (get_ith (ind index index) edge)) else mk_true srk
          ])
          ) (List.init (List.length coherence_classes + 1) (fun v -> v))
        ) reset_edges |> List.concat in 
      valid_permutation @ perm_must_reset @ no_resets_after_perm
      ) coherence_classes
    |> List.concat |> and1

  let row_to_formula index row rectified_summaries edge_to_terminal get_ith ind coherence_classes class_to_symbol = 
    let num_classes = List.length coherence_classes in 
    let reset_edges = M.map (fun summary -> snd (List.nth summary index)) rectified_summaries  
      |> M.filter (fun _ is_reset -> is_reset = 1) in 
    let offsets = M.map (fun summary ->
        List.nth summary index
        |> fst
        |> V.coeff 0
        |> mk_real srk
      ) rectified_summaries in 

    let all_adds_after i = 
      let words_after_i = List.init (num_classes - i) (fun v -> v + i + 1) in 
      let marked_after_i = List.init (num_classes - i - 1) (fun v -> v + i + 1) in
      M.fold (fun edge _ ls ->
        let offset = M.find edge offsets in 
        let words_sum = List.fold_left (fun acc word_num ->
          mul [edge_to_terminal (get_ith word_num edge); offset] :: acc
          ) [] words_after_i in 
        let marked_sum = List.fold_left (fun acc marked_num -> 
          mul [edge_to_terminal (get_ith (ind marked_num marked_num) edge); offset] :: acc
          ) [] marked_after_i in
        words_sum @ marked_sum @ ls
        ) (M.filter (fun edge _ -> not (M.mem edge reset_edges)) rectified_summaries) [] 
        |> add
      in
    
      let (pre_terms, post_terms) = BatEnum.fold (fun (pre_terms, post_terms) (value, i) -> 
          if i == 0 then (pre_terms, post_terms) else (
            let pre, post = List.nth symbol_pairs (i - 1) in 
            let pre = mul [const pre; mk_real srk value] in
            let post = mul [const post; mk_real srk value] in 
            (pre :: pre_terms, post :: post_terms)
          ) 
        ) ([], []) (V.enum row) in 
      let x = add pre_terms in 
      let x' = add post_terms in 
      let cl = List.filter (List.mem index) coherence_classes |> List.hd in 
      let permutation_symbol = (class_to_symbol cl) in 
      let form = if M.is_empty reset_edges then eq x' (add [x; all_adds_after (-1)]) else
      List.map (fun last_reset ->
        let is_eq = eq permutation_symbol (mk_int srk last_reset) in 
        let reset_cases = M.fold (fun edge _ acc -> 
          let was_reset = eq (edge_to_terminal (get_ith (ind last_reset last_reset) edge)) (one) in 
          let resulting_transorm = eq x' (add [M.find edge offsets; all_adds_after last_reset]) in 
          (and1 [was_reset; resulting_transorm]) :: acc
          ) reset_edges [] in 
          let all_edges_zero = M.fold (fun edge _ acc -> 
            eq (edge_to_terminal (get_ith (ind last_reset last_reset) edge)) (zero) :: acc
            ) reset_edges [] |> and1 in
          let unreset_case = and1 [all_edges_zero; eq x' (add [x; all_adds_after (-1)])] in  
          if1 is_eq (or1 (unreset_case :: reset_cases))
        ) (List.init num_classes (fun v -> v))
      |> and1 in form

  let summary_dicts = generate_vas_transforms ()
  let original_cfg = gen_cfg G.src

  let summarize call = 
    let cfg = CFG.set_start original_cfg call |> CFG.prune in
    let reachable = CFG.terminals cfg in 
    if List.length reachable = 0 then (algebra `One) else  
    let rectified_summaries = get_rectified_summaries reachable summary_dicts in 
    let coherence_classes = get_coherence_classes rectified_summaries in 
    let num_classes = List.length coherence_classes in 
    let ctr = ref 0 in 
    let ind i j = (i * num_classes) + j + (num_classes + 1) in 
    let edge_to_ind = Memo.memo (fun (_: IntPair.t) -> incr ctr; !ctr) in 
    let get_ith = (fun (i:int) e -> (i, edge_to_ind e)) in     

    print_string (SrkUtil.mk_show (CFG.pp) cfg);
    M.iter (fun edge ls ->
      print_string ("\n Summary of "^IntPair.show edge); 
      List.iter (fun (vec, reset) -> print_string (SrkUtil.mk_show V.pp vec); print_string " is reset? "; print_int reset;) ls;
      
      ) rectified_summaries;
    print_string ("\n\n"^(IntPair.show call));
    let class_to_symbol = Memo.memo (fun cl -> mk_symbol srk ~name:("perm"^(string_of_int (List.hd cl))) `TyInt |> const) in 

    let int_cfg = CFG.weak_labeled cfg get_ith get_ith ind num_classes in 
    let int_cfg = CFG.set_start int_cfg (get_ith (-1) call) |> CFG.prune in 
    
    let edge_to_terminal_dict = List.fold_left (fun dict edge -> M.add edge (mk_symbol srk ~name:("T"^IntPair.show edge) `TyInt) dict) M.empty (CFG.terminals int_cfg) in 
    let edge_to_terminal e = match M.find_opt e edge_to_terminal_dict with | Some v -> const v | None -> zero in 
    let call_to_nonterminal_dict = List.fold_left (fun dict edge -> M.add edge (mk_symbol srk ~name:("N"^IntPair.show edge) `TyInt) dict) M.empty (CFG.nonterminals int_cfg) in 
    let call_to_nonterminal e = match M.find_opt e call_to_nonterminal_dict with | Some v -> const v | None -> zero in 
    (* _print_formula (CFG.parikh srk cfg edge_to_terminal call_to_nonterminal); *)

    let call_count call = (
    (* partial words *)
    List.fold_left (fun acc it -> 
      call_to_nonterminal (get_ith it call) :: 
      neg (edge_to_terminal (get_ith it call)) :: acc) [] (List.init (num_classes+1) (fun v -> v))
    (* marked symbols *)
    @ List.fold_left (fun acc i -> 
      List.fold_left (fun acc j -> call_to_nonterminal (get_ith (ind i j) call) :: 
      neg (edge_to_terminal (get_ith (ind i j) call)) :: acc) acc (List.init (num_classes - i) (fun v -> i + v))) 
      [] (List.init num_classes (fun v -> v)) 
    ) |> add in 

    let call_and_ubs = generate_upper_bounds call in 
    let call_and_lbs = generate_lower_bounds call in 
    let upper_bound = List.map (fun (call, (guard, lims)) -> 
        print_string "\ncall: "; print_string (IntPair.show call);
        _print_formula guard; print_string "lims"; List.iter (fun e -> _print_formula e) lims;
        let cc = call_count call in 
        or1 [and1 (guard :: List.map (fun lim -> leq cc lim) lims); leq cc zero]
      ) call_and_ubs |> and1 in 
    let lower_bound = List.map (fun (call, (guard, lims)) ->
      let cc = call_count call in 
      and1 (guard :: List.map (fun lim -> leq lim cc) lims)
      ) call_and_lbs |> and1 in 
    print_string "CHECK THIS OUT"; _print_formula lower_bound;

    (* let lower_bound = and1 (lb_guard :: List.fold_left (fun acc lim -> leq lim call_count :: acc) [] lb_lims) in  *)
    
    List.iter (fun cl -> print_string "\n class: "; List.iter (fun num -> print_string " "; print_int num) cl) coherence_classes;

    let parikh = CFG.parikh srk int_cfg edge_to_terminal call_to_nonterminal in 
    let strong_label_constraints = get_strong_labeling_constraints 
      reachable coherence_classes class_to_symbol edge_to_terminal rectified_summaries get_ith ind in 
    let transform = M.find (List.hd reachable) rectified_summaries 
      |> List.map fst |> VS.matrix_of |> Q.rowsi
      |> BatEnum.fold (fun ls (index, row) -> 
        (row_to_formula index row rectified_summaries edge_to_terminal get_ith ind coherence_classes class_to_symbol) :: ls) []
      |> and1 in 
      (* _print_formula parikh; *)
      (* _print_formula strong_label_constraints; *)
      _print_formula transform;
      print_string "upperbound"; _print_formula upper_bound;
      (* _print_formula lower_bound; *)
      (* print_string "\n\n\n\n\n"; print_string (SrkUtil.mk_show (CFG.pp) cfg);
      print_string "\n\n\n\n\n"; print_string (SrkUtil.mk_show (CFG.pp) int_cfg); *)
      print_int num_classes;
      (* _print_formula (and1 [parikh; strong_label_constraints; transform; upper_bound; lower_bound]); *)
      List.iter (fun edge -> print_string ("\n"^IntPair.show edge)) reachable;
      print_string (IntPair.show call);
      (* let pre = List.fold_left (fun acc sym -> const (fst sym) :: acc) [] symbol_pairs |> and1 in  *)
      (* let ret, param = snd (List.nth symbol_pairs 0), fst (List.nth symbol_pairs 1) in 
      let pre = eq (const param) (add [one; one; one]) in 
      _print_formula pre;
      let formula = and1 [parikh; strong_label_constraints; transform; upper_bound; lower_bound] in
      (* _print_formula lower_bound;
      _print_formula (call_count call);
      _print_formula parikh; *)
      let post = eq (const ret) (add [zero]) in 
      let model = Smt.get_model srk (and1 [pre; formula; post]) in 
      _print_formula pre; _print_formula post;

      let _call_count call = (
    (* partial words *)
    List.fold_left (fun acc it -> 
      call_to_nonterminal (get_ith it call) :: 
      neg (edge_to_terminal (get_ith it call)) :: acc) [] (List.init (num_classes+1) (fun v -> v))
    (* marked symbols *)
    @ List.fold_left (fun acc i -> 
      List.fold_left (fun acc j -> call_to_nonterminal (get_ith (ind i j) call) :: 
      neg (edge_to_terminal (get_ith (ind i j) call)) :: acc) acc (List.init (num_classes - i) (fun v -> i + v))) 
      [] (List.init num_classes (fun v -> v)) 
      ) in 


      (match model with 
      | `Sat i -> 
          print_string "\n\n TERMINALS: \n\n"; 
          M.iter (fun edge sym -> print_string ("\nEdge "^IntPair.show edge); print_string " Value: "; print_string (SrkUtil.mk_show Mpqf.print (Interpretation.evaluate_term i (const sym)))) edge_to_terminal_dict;

          print_string "\n\n NONTERMINALS: \n\n";
          M.iter (fun edge sym -> print_string ("\nCall "^IntPair.show edge); print_string " formula "; print_string (SrkUtil.mk_show (Syntax.pp_expr_unnumbered srk) (const sym)); print_string " Value: "; print_string (SrkUtil.mk_show Mpqf.print (Interpretation.evaluate_term i (const sym)))) call_to_nonterminal_dict;

          print_string "\n param0? "; print_string (SrkUtil.mk_show Mpqf.print (Interpretation.evaluate_term i (const param)));
      | `Unsat -> print_string "\n\nUNSAT???"
      | _ -> ()); *)
      formula_to_transition (and1 [parikh; strong_label_constraints; transform; upper_bound; lower_bound]) (symbol_pairs)



  end