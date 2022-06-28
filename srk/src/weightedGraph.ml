open Pathexpr

include Log.Make(struct let name = "srk.weightedGraph" end)

module U = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)
module L = Loop.Make(U)
module D = Graph.Dominator.Make(U)
module C = Graph.Components.Make(U)

module IntPair = struct
  type t = int * int [@@deriving ord, eq]
  let hash = Hashtbl.hash
  let str (i, j : t)  = "(" ^ (string_of_int i) ^ ", " ^ (string_of_int j) ^ ")"
end

module N = IntPair  
module T = IntPair
module CFG = Grammar.MakeCFG(N)(T)

module M = BatMap.Make(IntPair)

type 'a algebra =
  { mul : 'a -> 'a -> 'a;
    add : 'a -> 'a -> 'a;
    star : 'a -> 'a;
    zero : 'a;
    one : 'a }

type ('a,'b) omega_algebra =
  { omega : 'a -> 'b;
    omega_add : 'b -> 'b -> 'b;
    omega_mul : 'a -> 'b -> 'b }

type 'a weighted_graph =
  { graph : U.t;
    labels : 'a M.t;
    algebra : 'a algebra }

type 'a t = 'a weighted_graph

type vertex = int

let omega_trivial =
  { omega = (fun _ -> ());
    omega_add = (fun _ _ -> ());
    omega_mul = (fun _ _ -> ()) }

(* Check invariant: 1-to-1 correspondence between labels & edges *)
let _sat_inv wg =
  (M.for_all (fun (u,v) _ -> U.mem_edge wg.graph u v) wg.labels)
  && U.fold_edges (fun u v b -> b && M.mem (u,v) wg.labels) wg.graph true

let empty algebra =
  { graph = U.empty;
    labels = M.empty;
    algebra = algebra }

let add_vertex wg vertex =
  { wg with graph = U.add_vertex wg.graph vertex }

let edge_weight wg u v =
  try M.find (u, v) wg.labels
  with Not_found -> wg.algebra.zero

let add_edge wg u weight v =
  if M.mem (u, v) wg.labels then
    let labels' = M.modify (u, v) (wg.algebra.add weight) wg.labels in
    { wg with labels = labels' }
  else
    { wg with graph = U.add_edge wg.graph u v;
              labels = M.add (u, v) weight wg.labels }

let remove_vertex wg u =
  let labels =
    U.fold_succ
      (fun v labels -> M.remove (u, v) labels)
      wg.graph
      u
      (U.fold_pred
         (fun v labels -> M.remove (v, u) labels)
         wg.graph
         u
         wg.labels)
  in
  { wg with graph = U.remove_vertex wg.graph u;
            labels = labels }

let remove_edge wg u v =
  { wg with graph = U.remove_edge wg.graph u v;
            labels = M.remove (u, v) wg.labels }

let fold_incident_edges f graph v acc =
  U.fold_succ
    (fun u acc -> f (v, u) acc)
    graph
    v
    (U.fold_pred
       (fun u acc -> if u == v then acc else f (u, v) acc)
       graph
       v
       acc)

(* Rename vertex u to w.  If w already exists in the graph, then all
   of the incident edges of u become incident to w instead (and u is
   removed). *)
let _rename_vertex wg u w =
  let g' = U.add_vertex (U.remove_vertex wg.graph u) w in
  let rename v = if v = u then w else v in
  fold_incident_edges (fun (v,v') wg ->
      let (weight, labels) = M.extract (v, v') wg.labels in
      let graph' =
        U.add_edge wg.graph (rename v) (rename v')
      in
      let labels' =
        M.add (rename v, rename v') weight labels
      in
        { wg with graph = graph'; labels = labels' })
    wg.graph
    u
    { wg with graph = g' }

let contract_vertex wg v =
  (* List of all { (s, w(v,v)*w(v,s)) : (v,s) in E } *)
  let star x = wg.algebra.star x in
  let mul x y = wg.algebra.mul x y in
  let loop_succ =
    let loop =
      try star (M.find (v, v) wg.labels)
      with Not_found -> wg.algebra.one
    in
    U.fold_succ (fun u succs ->
        if u = v then
          succs
        else
          (u, mul loop (M.find (v, u) wg.labels))::succs)
      wg.graph
      v
      []
  in
  U.fold_pred (fun pred wg' ->
      if pred = v then
        wg'
      else
        let pw = edge_weight wg pred v in
        List.fold_left (fun wg' (succ, sw) ->
            add_edge wg' pred (mul pw sw) succ)
          wg'
          loop_succ)
    wg.graph
    v
    (remove_vertex wg v)

let max_vertex wg = U.fold_vertex max wg.graph 0

(* Contract edges in the graph, preserving path weight from src to
   every other vertex.  Remaining edges start at src or are a
   self-loop. *)
let _solve_dense (wg : 'a weighted_graph) (src : vertex) =
  let mul = wg.algebra.mul in
  (* Contract the successor edges of a vertex, except self-loops. *)
  let bypass_vertex wg v =
    if v = src then
      wg
    else
      let predecessors =
        let mul_loop =
          if M.mem (v, v) wg.labels then
            let loop = wg.algebra.star (M.find (v,v) wg.labels) in
            (fun x -> mul x loop)
          else
            (fun x -> x)
        in
        BatList.filter_map (fun p ->
            if p = v then None
            else Some (p, mul_loop (edge_weight wg p v)))
          (U.pred wg.graph v)
      in
      (* For each succesor s of v, connect s to all predecessors of v
         and remove the s->v edge *)
      U.fold_succ (fun s wg ->
          if s = v then
            wg
          else
            let v_to_s = edge_weight wg v s in
            List.fold_left (fun wg (p, p_to_v) ->
                add_edge wg p (mul p_to_v v_to_s) s)
              (remove_edge wg v s)
              predecessors)
        wg.graph
        v
        wg
  in
  let rec go wg elt =
    match elt with
    | `Vertex v -> bypass_vertex wg v
    | `Loop loop ->
       let wg = List.fold_left go wg (L.children loop) in
       bypass_vertex wg (L.header loop)
  in
  List.fold_left go wg (L.loop_nest wg.graph)

(* Main logic for single-source multi-target path weights and omega
   path weights.  The algorithm is a variation of Tarjan's algorithm
   from "Fast Algorithms for Solving Path Problems", JACM '81.
   Returns a triple (omega_weight, path_weight, reachable), where
   omega_weight is the sum of weights of all omega paths starting at
   src, path_weight v is the sum of weights of all paths from src to
   v, and reachable is an enumeration of the vertices reachable from
   src.  *)
let _path_weight
      (wg : 'a t)
      (omega : ('a, 'b) omega_algebra)
      (src : vertex) =
  (* Ensure that src has no incoming edges *)
  let (wg, src) =
    let start = max_vertex wg + 1 in
    (add_edge (add_vertex wg start) start wg.algebra.one src, start)
  in

  let module F = CompressedWeightedForest in
  let mul = wg.algebra.mul in
  let one = wg.algebra.one in
  let star = wg.algebra.star in
  let forest =
    F.create ~mul:(fun x y -> mul y x) ~one
  in
  let wg_to_forest = BatHashtbl.create 97 in
  let forest_to_wg = BatHashtbl.create 97 in
  let to_forest v =
    if BatHashtbl.mem wg_to_forest v then
      BatHashtbl.find wg_to_forest v
    else begin
        let r = F.root forest in
        BatHashtbl.add wg_to_forest v r;
        BatHashtbl.add forest_to_wg r v;
        r
      end
  in
  let find v =
    BatHashtbl.find forest_to_wg (F.find forest (to_forest v))
  in
  let link u weight v =
    F.link forest ~child:(to_forest u) weight ~parent:(to_forest v)
  in
  let eval v = F.eval forest (to_forest v) in
  let idom = D.compute_idom wg.graph src in
  let children = D.idom_to_dom_tree wg.graph idom in
  let rec solve (v : vertex) =
    let children_omega = List.map solve (children v) in

    (* Graph where vertices are children of v, and there is an edge u
       -> w iff there is a path from u to w consisting only of
       vertices strictly dominated by v *)
    let sibling_graph =
      List.fold_left
        (fun sg child ->
          U.fold_pred (fun pred sg ->
              let pred = find pred in
              if pred = v then sg
              else U.add_edge sg pred child)
            wg.graph
            child
            (U.add_vertex sg child))
        U.empty
        (children v)
    in
    (* Traverse SCCs in topological order *)
    let omega_weight =
      List.fold_right
        (fun component omega_weight ->
          let component_wg =
            List.fold_left (fun component_wg v ->
                U.fold_pred (fun p component_wg ->
                    let weight = mul (eval p) (edge_weight wg p v) in
                    add_edge component_wg (find p) weight v)
                  wg.graph
                  v
                  component_wg)
              (empty wg.algebra)
              component
          in
          let reduced = _solve_dense component_wg v in
          List.fold_left (fun omega_weight c ->
              let v_to_c = edge_weight reduced v c in
              let (omega_weight, weight) =
                if U.mem_edge reduced.graph c c then
                  let c_to_c = edge_weight reduced c c in
                  let v_c_omega = omega.omega_mul v_to_c (omega.omega c_to_c) in
                  (omega.omega_add omega_weight v_c_omega,
                   mul v_to_c (star c_to_c))
                else (omega_weight, v_to_c)
              in
              link c weight v;
              omega_weight)
            omega_weight
            component)
        (C.scc_list sibling_graph)
        (omega.omega wg.algebra.zero)
    in
    BatList.fold_left2 (fun v_omega c c_omega ->
        omega.omega_add v_omega (omega.omega_mul (eval c) c_omega))
      omega_weight
      (children v)
      children_omega
  in
  let omega_weight = solve src in
  (* src is an artificial start node -- it's not reachable and its
     path weight 0 *)
  let path_weight x =
    if Hashtbl.mem wg_to_forest x && find x = src && x != src then eval x
    else wg.algebra.zero
  in
  let reachable =
    BatEnum.filter (fun x -> x != src && find x = src) (BatHashtbl.keys wg_to_forest)
  in
  (omega_weight, path_weight, reachable)

let path_weight wg src =
  let (_, path_weight, _) = (_path_weight wg omega_trivial src) in
  path_weight

let omega_path_weight wg omega src =
  let (omega_weight, _, _) = _path_weight wg omega src in
  omega_weight

let msat_path_weight wg sources =
  List.fold_left (fun g src ->
      let (_, path_weight, reachable) = _path_weight wg omega_trivial src in
      BatEnum.fold
        (fun g v -> add_edge g src (path_weight v) v)
        (add_vertex g src)
        reachable)
    (empty wg.algebra)
    sources

let split_vertex wg u weight v =
  U.fold_succ (fun w wg ->
      let (uw, labels) = M.extract (u, w) wg.labels in
      { wg with graph = U.add_edge (U.remove_edge wg.graph u w) v w;
                labels = M.add (v, w) uw labels })
    wg.graph
    u
    { wg with graph = U.add_edge wg.graph u v;
              labels = M.add (u, v) weight wg.labels }

let forget_weights wg = wg.graph

let map_weights f wg =
  { wg with labels = M.mapi (fun (u,v) w -> f u w v) wg.labels }

let fold_edges f wg acc =
  M.fold (fun (u,v) w acc ->
      f (u, w, v) acc)
    wg.labels
    acc

let iter_edges f wg =
  M.iter (fun (u, v) w -> f (u, w, v)) wg.labels

let fold_pred_e f wg v =
  U.fold_pred
    (fun u acc -> f (u, edge_weight wg u v, v) acc)
    wg.graph
    v

let fold_succ_e f wg u =
  U.fold_succ
    (fun v acc -> f (u, edge_weight wg u v, v) acc)
    wg.graph
    u

let iter_pred_e f wg v =
  U.iter_pred
    (fun u -> f (u, edge_weight wg u v, v))
    wg.graph
    v

let iter_succ_e f wg u =
  U.iter_succ
    (fun v -> f (u, edge_weight wg u v, v))
    wg.graph
    u

let fold_vertex f wg = U.fold_vertex f wg.graph
let iter_vertex f wg = U.iter_vertex f wg.graph
let mem_edge wg u v = M.mem (u, v) wg.labels

(* Cut graph reduces a weighted graph to only those vertices in c, while preserving all weighted paths between pairs of vertices in c *)
let cut_graph wg c =
  let module Set = SrkUtil.Int.Set in
  let cut_set = Set.of_list c in
  let pre_vertex v = v in
  let post_vertex =
     let max = Set.fold max cut_set (max_vertex wg) + 1 in
     Memo.memo (fun v -> if Set.mem v cut_set then v + max else v)
  in
  let path_graph =
    let pg = Set.fold (fun v pg -> add_vertex (add_vertex pg (pre_vertex v)) (post_vertex v)) cut_set (empty wg.algebra) in
    let pg = fold_vertex (fun v pg -> add_vertex pg v) wg pg in
    fold_edges (fun (u, w, v) pg -> add_edge pg (pre_vertex u) w (post_vertex v)) wg pg
  in
  Set.fold (fun u cg ->
    Set.fold (fun v cg ->
      add_edge (add_vertex cg v) u (path_weight path_graph (pre_vertex u) (post_vertex v)) v
    ) cut_set (add_vertex cg u)
  ) cut_set (empty wg.algebra)

(* Line graphs swaps vertices and edges *)
module LineGraph = struct
  type t = U.t
  module V = IntPair
  let iter_vertex f graph = U.iter_edges (fun x y -> f (x, y)) graph
  let iter_succ f graph (_, dst) =
    U.iter_succ
      (fun succ -> f (dst, succ))
      graph
      dst
end
module LGLoop = Loop.Make(LineGraph)

let forward_analysis wg ~entry ~update ~init =
  let data_table = Hashtbl.create 991 in
  let get_data v =
    try Hashtbl.find data_table v
    with Not_found ->
      let data = init v in
      Hashtbl.add data_table v data;
      data
  in
  let set_data v data =
    Hashtbl.replace data_table v data;
  in

  let module ESet = LGLoop.VertexSet in
  let update_edge work ((src, dst) as e) =
    if ESet.mem e work then
      let work = ESet.remove e work in
      let weight = edge_weight wg src dst in
      match update ~pre:(get_data src) weight ~post:(get_data dst) with
      | Some data ->
        set_data dst data;
        U.fold_succ_e ESet.add wg.graph dst work
      | None -> work
    else
      work
  in
  let rec solve work loop_nest =
    match loop_nest with
    | `Vertex e -> update_edge work e
    | `Loop loop ->
      let cmp_edges = LGLoop.body loop in
      let rec fix work =
        let work =
          List.fold_left
            solve
            (update_edge work (LGLoop.header loop))
            (LGLoop.children loop)
        in
        if ESet.exists (fun e -> ESet.mem e work) cmp_edges then
          fix work
        else
          work
      in
      fix work
  in

  (* Add an artificial edge to act as the entry point to the line
     graph of graph. Don't add to the initial worklist, so update will
     never be called on the artifical edge.  *)
  let init_vertex = max_vertex wg + 1 in
  let graph' = U.add_edge wg.graph init_vertex entry in

  ignore (List.fold_left
            solve
            (U.fold_succ_e ESet.add wg.graph entry ESet.empty)
            (LGLoop.loop_nest graph'));

  get_data

module type AbstractWeight = sig
  type weight
  type abstract_weight
  val abstract : weight -> abstract_weight
  val concretize : abstract_weight -> weight
  val equal : abstract_weight -> abstract_weight -> bool
  val widen : abstract_weight -> abstract_weight -> abstract_weight
end

module RecGraph = struct
  module HT = BatHashtbl.Make(IntPair)
  module CallSet = BatSet.Make(IntPair)
  module VertexSet = SrkUtil.Int.Set
  module CallGraph = struct
    type t = CallSet.t M.t
    module V = IntPair
    let iter_vertex f callgraph =
      M.iter (fun k _ -> f k) callgraph
    let iter_succ f callgraph v =
      CallSet.iter f (M.find v callgraph)
    let add_vertex callgraph v =
      if M.mem v callgraph then
        callgraph
      else
        M.add v CallSet.empty callgraph
    let add_edge callgraph u v =
      let callgraph = add_vertex callgraph v in
      if M.mem u callgraph then
        M.add u (CallSet.add v (M.find u callgraph)) callgraph
      else
        M.add u (CallSet.singleton v) callgraph
    let empty = M.empty
  end
  module CallGraphLoop = Loop.Make(CallGraph)

  type call = vertex * vertex

  type t =
    { path_graph : Pathexpr.simple Pathexpr.t weighted_graph;
      call_edges : call M.t;
      context : Pathexpr.context }

  type query =
    { recgraph : t;

      (* The intraprocedural path graph has an edge u->v for
         each entry vertex u and each vertex v reachable from u,
         weighted with a path expression for the paths from u to v. *)
      intraproc_paths : Pathexpr.simple Pathexpr.t weighted_graph;

      (* The interprocedural graph has entries as vertices, and each
         edge u->v is weighted by a path expression recognizing all
         paths from u to an call edge (v, _) *)
      interproc : Pathexpr.nested Pathexpr.t weighted_graph;

      (* The interprocedural path graph has an edge src->v for each
         entry vertex v weighted by a path expression for the paths in
         the interprocedural graph from src to v *)
      interproc_paths : Pathexpr.nested Pathexpr.t weighted_graph;

      src : vertex (* designated source vertex *) }

  (* The memo table and algebra of a weighted query should not be
     accessed directly -- the memo table becomes stale when summaries
     are updated.  Use the "prepare" function to fix the memo table
     and get an algebra that also provides an interpretation for call
     edges. *)
  type 'a weight_query =
    { query : query;
      summaries : 'a HT.t; (* Map calls to their summaries *)

      (* Memo table mapping path expressions to their weights *)
      table : 'a Pathexpr.table;

      (* Calls whose summaries have changed since they were last
         evaluated *)
      changed : CallSet.t ref;

      (* An algebra for assigning weights to non-call edges and *)
      algebra : 'a Pathexpr.nested_algebra }

  let pathexpr_algebra context =
    { mul = mk_mul context;
      add = mk_add context;
      star = mk_star context;
      zero = mk_zero context;
      one = mk_one context }

  let fold_reachable_edges f g v acc =
    let visited = ref VertexSet.empty in
    let rec go u acc =
      U.fold_succ (fun v acc ->
          let acc = f u v acc in
          if not (VertexSet.mem v !visited) then begin
              visited := VertexSet.add v (!visited);
              go v acc
            end
          else acc)
        g.graph
        u
        acc
    in
    go v acc

  let mk_query rg src =
    (* All calls that appear on a call edge *)
    let callset =
      M.fold (fun _ call callset ->
          CallSet.add call callset)
        rg.call_edges
        CallSet.empty
    in
    let sources =
      CallSet.fold (fun (src, _) -> VertexSet.add src) callset VertexSet.empty
      |> VertexSet.add src
      |> VertexSet.elements
    in
    let intraproc_paths = msat_path_weight rg.path_graph sources in
    let interproc =
      let intraproc_paths = edge_weight intraproc_paths in
      List.fold_left (fun interproc_graph src ->
          fold_reachable_edges (fun u v interproc_graph ->
              try
                let (en,_) = M.find (u,v) rg.call_edges in
                let pathexpr =
                  mk_segment rg.context (intraproc_paths src u)
                in
                add_edge interproc_graph src pathexpr en
              with Not_found -> interproc_graph)
            rg.path_graph
            src
            (add_vertex interproc_graph src))
        (empty (pathexpr_algebra rg.context))
        sources
    in
    { recgraph = rg;
      intraproc_paths = intraproc_paths;
      interproc = interproc;
      interproc_paths = msat_path_weight interproc [src];
      src = src }

  let call_pathexpr query (src, tgt) =
    (* intraproc_paths is only set when src is an entry vertex *)
    if not (U.mem_vertex query.interproc.graph src) then
      invalid_arg "call_weight: unknown call";
    edge_weight query.intraproc_paths src tgt

  let mk_callgraph query =
    (* If there is a call to (s,t) between s' and t', add a dependence
       edge from (s',t') to (s,t) *)
    let callset =
      (* All calls that appear on a call edge *)
      M.fold
        (fun _ call callset -> CallSet.add call callset)
        query.recgraph.call_edges
        CallSet.empty
    in
    (* Collect the set of calls that appear in a path expression *)
    let callset_algebra = function
      | `Edge e ->
         begin try
             CallSet.singleton (M.find e query.recgraph.call_edges)
           with Not_found -> CallSet.empty
         end
      | `Mul (x, y) | `Add (x, y) -> CallSet.union x y
      | `Star x -> x
      | `Zero | `One -> CallSet.empty
    in
    let table = mk_table () in
    CallSet.fold (fun call callgraph ->
          CallGraph.add_vertex callgraph call)
        callset
        CallGraph.empty
    |> CallSet.fold (fun (en, ex) callgraph ->
           let pathexpr = edge_weight query.intraproc_paths en ex in
           CallSet.fold (fun target callgraph ->
               CallGraph.add_edge callgraph target (en, ex))
             (eval ~table ~algebra:callset_algebra pathexpr)
             callgraph)
         callset

  let mk_omega_algebra context =
    { omega = mk_omega context;
      omega_add = mk_omega_add context;
      omega_mul = mk_omega_mul context }

  let omega_pathexpr (query : query) =
    let context = query.recgraph.context in
    let omega_algebra =mk_omega_algebra context in
    let omega_inter_algebra = mk_omega_algebra context in
    fold_vertex (fun entry w ->
        let src_entry =
          edge_weight query.interproc_paths query.src entry
        in
        let entry_omega =
          omega_path_weight query.recgraph.path_graph omega_algebra entry
          |> Pathexpr.promote_omega
        in
        let src_entry_omega =
          Pathexpr.mk_omega_mul query.recgraph.context src_entry entry_omega
        in
        Pathexpr.mk_omega_add context w src_entry_omega)
      query.interproc_paths
      (omega_path_weight query.interproc omega_inter_algebra query.src)

  let pathexpr query tgt =
    (* The interprocedural path weight to tgt is the sum over all
       entries of an interprocedural path from src to entry * an
       intraprocedural path from entry to tgt *)
    let context = query.recgraph.context in
    U.fold_pred (fun entry w ->
        if U.mem_edge query.interproc_paths.graph query.src entry then
          let src_entry_tgt =
            Pathexpr.mk_mul
              context
              (edge_weight query.interproc_paths query.src entry)
              (Pathexpr.promote (edge_weight query.intraproc_paths entry tgt))
          in
          Pathexpr.mk_add context w src_entry_tgt
        else w)
      query.intraproc_paths.graph tgt (Pathexpr.mk_zero context)

  exception No_summary of call

  (* Prepare memo table & algebra for a weight query *)
  let prepare (q : 'a weight_query) =
    let call_edges = q.query.recgraph.call_edges in
    let changed = !(q.changed) in
    let algebra = function
      | `Edge (s, t) when M.mem (s, t) call_edges ->
         let call = M.find (s, t) call_edges in
         (try HT.find q.summaries call
          with Not_found -> raise (No_summary call))
      | e -> q.algebra e
    in
    if not (CallSet.is_empty changed) then begin
        forget q.table (fun s t ->
            try not (CallSet.mem (M.find (s, t) call_edges) changed)
            with Not_found -> true);
        q.changed := CallSet.empty
      end;
    (q.table, algebra)

  let get_summary query call =
    try HT.find query.summaries call
    with Not_found -> raise (No_summary call)

  let set_summary query call weight =
    query.changed := CallSet.add call !(query.changed);
    HT.replace query.summaries call weight

  let mk_weight_query query algebra =
    { query = query;
      summaries = HT.create 991;
      changed = ref CallSet.empty;
      table = Pathexpr.mk_table ();
      algebra = algebra }

  let path_weight query tgt =
    let (table, algebra) = prepare query in
    Pathexpr.eval_nested ~table ~algebra (pathexpr query.query tgt)

  let call_weight query (src, tgt) =
    let (table, algebra) = prepare query in
    Pathexpr.eval ~table ~algebra (call_pathexpr query.query (src, tgt))

  let omega_path_weight query omega_algebra =
    let (table, algebra) = prepare query in
    let omega_table = Pathexpr.mk_omega_table table in
    let paths = omega_pathexpr query.query in
    Pathexpr.eval_omega ~table:omega_table ~algebra ~omega_algebra paths

(** Generate a CFG representing the possible runs of query *)
  let gen_cfg query = 
    let cfg = CFG.empty (query.src, query.src) in 
    let wg = query.recgraph.path_graph in
    let ce = query.recgraph.call_edges in 

    let nt_ends = M.fold (fun _ (_, call_end) acc -> call_end :: acc) ce [] in 

    (* To be applied to every edge (v_1, v_2) in the weighted graph. If the edge is a call edge, 
    adds N(v_1, end) -> N(call) N(v_2, end) where call is the call of (v_1, v_2) and end
    is every possible nonterminal target. If the edge is not a call edge, adds
    N(v_1, end) -> T(v_1, v_2) N(v_2)  *)
    let helper (v_1, _,  v_2) acc = 
      if M.mem (v_1, v_2) ce then
        let call = M.find (v_1, v_2) ce in
        List.fold_left (fun cfg e -> CFG.add_production cfg (v_1, e) [N call ; N (v_2, e)]) acc nt_ends
      else
        List.fold_left (fun cfg e -> CFG.add_production cfg (v_1, e) [T (v_1, v_2) ; N (v_2, e)]) acc nt_ends
    in 

    let cfg = fold_edges helper wg cfg in
    (* Once we have reached the target of a particular nonterminal, that symbol is allowed 
    to go to null *)
    let cfg = List.fold_left (fun cfg e -> CFG.add_production cfg (e, e) []) cfg nt_ends in
    cfg 

    let summarize_cfg
          path_query
          algebra
          get_tf
          context
          symbol_pairs
          construct 
           =
      let module Ab = Abstract in
      let module L = Linear in 
      let module Q = L.QQMatrix in 
      let module S = Syntax in 
      
      let weight_query = mk_weight_query path_query algebra in
      let callgraph = mk_callgraph path_query in
      let add_summaries = HT.create 991 in
      let reset_summaries = HT.create 991 in
      let rectified_summaries = HT.create 991 in 
      let to_align = HT.create 991 in 
      let parikh_terms = HT.create 991 in 
      let perm_symbols = HT.create 991 in 
      let edge_to_ind = HT.create 991 in 
      let call_edges = path_query.recgraph.call_edges in 
      let cfg = gen_cfg path_query in

      (* 1. For each non-loop edge, compute the affine hull of the weight of the edge. *)
      let addition_basis = (S.mk_one context) :: List.map (fun (pre, post) -> S.mk_sub context (S.mk_const context pre) (S.mk_const context post)) symbol_pairs in
      let reset_basis = (S.mk_one context) :: List.map (fun (_, post) -> (S.mk_const context post)) symbol_pairs in
      let cut_const_term v = L.QQVector.of_enum (BatEnum.filter_map (fun (e, d) -> if (d >= 1) then Option.some (e, d-1) else Option.none) (L.QQVector.enum v)) in
      let basis_dim = List.length addition_basis in  

      iter_edges (fun (v_1, p, v_2)  -> 
        if not (M.mem (v_1, v_2) call_edges) then 
          let f = Pathexpr.eval ~algebra p in 
          let aff = Ab.vanishing_space context (get_tf f) (Array.of_list (addition_basis)) in
          let res = Ab.vanishing_space context (get_tf f) (Array.of_list (reset_basis)) in
          let ali_aff = List.map cut_const_term aff in 
          let ali_res = List.map cut_const_term res in 
          HT.add add_summaries (v_1, v_2) (L.QQVectorSpace.matrix_of aff);
          HT.add reset_summaries (v_1, v_2) (L.QQVectorSpace.matrix_of res);
          HT.add to_align (v_1, v_2) (L.QQVectorSpace.matrix_of ali_aff, L.QQVectorSpace.matrix_of ali_res);
        else ()
        ) path_query.recgraph.path_graph; 

      (* Populates rectified_summaries with common abstraction
      curr contains the current common abstraction, shared by all elements of bs *)
      let rec binary_coproduct lst curr bs = 
        if Q.equal curr Q.zero then () else
        match lst with 
        | [] -> List.iter (fun (ind, edge, mat) -> 
          let rows = BatEnum.fold (fun ls (_, r) -> (r, ind) :: ls) [] (Q.rowsi mat) in
          if HT.mem rectified_summaries edge then 
            (HT.replace rectified_summaries edge (rows @ HT.find rectified_summaries edge)) 
          else HT.add rectified_summaries edge rows
          ) bs
        | hd :: rst -> 
          let e, (aff, res) = hd in 
          let c, d = L.pushout aff curr in 
          let new_bs = List.map (fun (ind, edge, mat) -> (ind, edge, Q.mul d mat)) bs in 
          binary_coproduct rst (Q.mul d curr) ((1, e, Q.mul c (HT.find add_summaries e)) :: new_bs);

          let c, d = L.pushout res curr in 
          let new_bs = List.map (fun (ind, edge, mat) -> (ind, edge, Q.mul d mat)) bs in 
          binary_coproduct rst (Q.mul d curr) ((0, e, Q.mul c (HT.find reset_summaries e)) :: new_bs); 
      in 
      
      (* 3. For each non-loop edge, use the normal summary. If not, use the CFG to compute a parikh image based on the start and 
      update variables based on the resulting arithmetic terms. *)
      let build t = 
        let call = match t with  
      | `Vertex call -> call
      | `Loop loop -> CallGraphLoop.header loop in 
        HT.clear rectified_summaries;
        HT.clear parikh_terms;
        HT.clear perm_symbols;
        HT.clear edge_to_ind;
        
        let cfg = CFG.set_start cfg call |> CFG.prune in 
        let reachable = CallSet.of_list (CFG.terminals cfg) in 
        binary_coproduct (List.map (fun e -> (e, HT.find to_align e)) (CallSet.elements reachable)) 
        (Q.identity (List.init basis_dim (fun v -> v))) [];

        let num_edges = CallSet.cardinal reachable in
        let ctr = ref 0 in 
        let ind i j = (i * num_edges) + j + (num_edges+1) in 
        let get_ith = (fun (i:int) e -> if HT.mem edge_to_ind e then (i, HT.find edge_to_ind e) else (incr ctr; HT.add edge_to_ind e !ctr; (i, !ctr))) in 

        let int_cfg = CFG.weak_labeled cfg get_ith get_ith ind in 
        let int_cfg = CFG.set_start int_cfg (get_ith (-1) call) |> CFG.prune in 

        let parikh = CFG.parikh context int_cfg 
        (fun t -> (
          if not (HT.mem parikh_terms t) then 
            HT.add parikh_terms t (Syntax.mk_const context (Syntax.mk_symbol context ~name:("T"^IntPair.str t) `TyInt)));
          HT.find parikh_terms t) in

        CallSet.iter (fun e -> 
          let sym = Syntax.mk_symbol context ~name:("perm"^IntPair.str e) `TyInt
           |> Syntax.mk_const context in 
           HT.add perm_symbols e sym
           ) reachable;  
           
        let strong_constraints = HT.map (fun edge sym -> 
          (* valid permutation constraints *)
          [Syntax.mk_leq context (Syntax.mk_zero context) sym;
            Syntax.mk_lt context sym (Syntax.mk_int context (HT.length add_summaries))] @
          (HT.map (fun other_edge other_symbol -> if edge != other_edge then Syntax.mk_not context (Syntax.mk_eq context sym other_symbol) else Syntax.mk_true context) perm_symbols
          |> HT.values
          |> BatEnum.fold (fun ls i -> i :: ls) []) @
          (* unique final appearances *)
          List.filter_map (fun j -> 
            if HT.mem parikh_terms (get_ith (ind j j) edge) then 
              let jth_term = HT.find parikh_terms (get_ith (ind j j) edge) in 
              Some (Syntax.mk_if context (Syntax.mk_not context (Syntax.mk_eq context sym (Syntax.mk_int context j))) 
              (Syntax.mk_eq context (Syntax.mk_zero context) jth_term))
            else None) (List.init num_edges (fun v -> v)) @
          (* word constraints *)
          List.filter_map (fun j -> 
            if HT.mem parikh_terms (get_ith j edge) 
              then Some (Syntax.mk_if context (Syntax.mk_lt context sym (Syntax.mk_int context j)) 
                (Syntax.mk_eq context (Syntax.mk_zero context) (HT.find parikh_terms (get_ith j edge))))
              else None
            ) (List.init (num_edges+1) (fun v-> v))
          ) perm_symbols 
        |> HT.values |> BatEnum.fold (fun ls expr -> expr @ ls) [] |> Syntax.mk_and context in 
        
        let resolve_row rowi row = 
          let edge_summaries = HT.fold (fun edge summary acc -> (edge, snd (List.nth summary rowi)) :: acc) rectified_summaries [] in
          let reset_edges = List.filter (fun (_, ind) -> ind == 0) edge_summaries
          |> List.map fst 
          in
          let offsets = HT.map (fun _ summary -> 
              List.nth summary rowi 
              |> fst 
              |> L.QQVector.coeff 0
              |> S.mk_real context
            ) rectified_summaries in 
          (* Term representing the sum of all additions occuring in w_{i+1} t_{i+1} ... *)
          let alpha i = 
            HT.fold (fun edge _ ls ->
              let offset = HT.find offsets edge in 
              let from_word = List.fold_left (fun acc j ->
                  S.mk_mul context [
                    HT.find parikh_terms (get_ith j edge); 
                    offset
                  ] :: acc
                ) [] (List.filter (fun j -> HT.mem parikh_terms (get_ith j edge)) (List.init (num_edges - i) (fun z -> z + i + 1))) in 
              let from_marked = List.fold_left (fun acc j -> 
                  S.mk_mul context [
                    HT.find parikh_terms (get_ith (ind j j) edge);
                    offset
                  ] :: acc
                ) [] (List.filter (fun j -> HT.mem parikh_terms (get_ith (ind j j) edge)) (List.init (num_edges - i - 1) (fun z -> z + i + 1))) in 
                from_word @ from_marked @ ls
              ) rectified_summaries [] 
              |> S.mk_add context 
          in
          let (pre_terms, post_terms) = BatEnum.fold (fun (pre_terms, post_terms) (v, i) -> 
            if i == 0 then (pre_terms, post_terms) else 
            let (pre_term, post_term) = List.nth symbol_pairs (i-1) in 
            let pre = S.mk_mul context [(S.mk_const context pre_term); (S.mk_real context v)] in 
            let post = S.mk_mul context [(S.mk_const context post_term); (S.mk_real context v)] in 
            (pre :: pre_terms, post :: post_terms)
            ) ([], []) (L.QQVector.enum row) in 
          let x = S.mk_add context pre_terms in 
          let x' = S.mk_add context post_terms in 
          let reset_permutations = List.map (fun edge -> edge, HT.find perm_symbols edge) reset_edges in 
          let formula = 
            if List.length reset_permutations == 0 
              then S.mk_eq context x' (S.mk_add context [x; alpha (-1)])
              else
              List.fold_left (fun ls (edge, perm_sym) ->
              let is_max = List.fold_left (fun acc (_, other_perm_sym) -> S.mk_leq context other_perm_sym perm_sym :: acc) [] reset_permutations  
              |> S.mk_and context in
              let last_reset_at = List.map (fun i ->
                let is_eq = S.mk_eq context perm_sym (S.mk_int context i) in
                let was_reset = S.mk_eq context (HT.find parikh_terms (get_ith (ind i i) edge)) (S.mk_one context) in
                let offset = HT.find offsets edge in 
                let reset_case = S.mk_and context [was_reset; S.mk_eq context x' (S.mk_add context [offset; alpha i])] in 
                let unreset_case = S.mk_and context [S.mk_not context was_reset; S.mk_eq context x' (S.mk_add context [x; alpha i])] in 
                S.mk_if context is_eq (S.mk_or context [reset_case; unreset_case])
                ) (List.init (num_edges) (fun z -> z)) in 
              S.mk_if context is_max (S.mk_and context last_reset_at) :: ls
              ) [] reset_permutations
              |> S.mk_and context 
          in
          formula
        in 
        let some_mat = HT.keys rectified_summaries
        |> BatEnum.find (fun _ -> true) 
        |> HT.find rectified_summaries |> List.map fst in 
        let row_enum = Q.rowsi (L.QQVectorSpace.matrix_of some_mat) in    

        let transform = BatEnum.fold (fun ls (i, r) -> (resolve_row i r) :: ls) [] row_enum 
        |> S.mk_and context in 
        let formula = S.mk_and context [parikh ; strong_constraints; transform] in
        let transition = construct formula symbol_pairs in 
        set_summary weight_query call transition;
      in 
      List.iter build (CallGraphLoop.loop_nest callgraph);
      weight_query

  let summarize_iterative
        (type a)
        path_query
        algebra
        ?(delay=1)
        (module A : AbstractWeight with type weight = a) =
    let weight_query = mk_weight_query path_query algebra in
    let callgraph = mk_callgraph path_query in
    let project x = algebra (`Segment x) in
    let abstract_summaries = HT.create 991 in
    (* stabilize summaries within a WTO component, and add to unstable
       all calls whose summary (may have) changed as a result. *)
    let rec fix = function
      | `Vertex call ->
         call_weight weight_query call
         |> project
         |> set_summary weight_query call

      | `Loop loop ->
         let header = CallGraphLoop.header loop in
         let rec fix_component delay =
           let old_abs_weight = HT.find abstract_summaries header in
           let (new_abs_weight, new_weight) =
             let new_weight =
               project (call_weight weight_query header)
             in
             let new_abs_weight = A.abstract new_weight in
             if delay > 0 then
               (new_abs_weight, new_weight)
             else
               let new_abs_weight = A.widen old_abs_weight new_abs_weight in
               let new_weight = A.concretize new_abs_weight in
               (new_abs_weight, new_weight)
           in
           HT.replace abstract_summaries header new_abs_weight;
           set_summary weight_query header new_weight;
           List.iter fix (CallGraphLoop.children loop);
           if not (A.equal old_abs_weight new_abs_weight)
           then fix_component (delay - 1)
         in
         fix_component delay
    in
    let zero = algebra `Zero in
    let abstract_zero = A.abstract zero in
    callgraph
    |> CallGraph.iter_vertex (fun call ->
           set_summary weight_query call zero;
           HT.add abstract_summaries call abstract_zero);
    List.iter fix (CallGraphLoop.loop_nest callgraph);
    weight_query

  let empty () =
    let context = mk_context () in
    let algebra =
      { mul = mk_mul context;
        add = mk_add context;
        star = mk_star context;
        zero = mk_zero context;
        one = mk_one context }
    in
    { path_graph = empty algebra;
      call_edges = M.empty;
      context = context }

  let add_call_edge rg u call v =
    { rg with path_graph = add_edge rg.path_graph u (mk_edge rg.context u v) v;
              call_edges = M.add (u,v) call rg.call_edges }

  let add_edge rg u v =
    { rg with path_graph = add_edge rg.path_graph u (mk_edge rg.context u v) v }

  let add_vertex rg v =
    { rg with path_graph = add_vertex rg.path_graph v }
end
