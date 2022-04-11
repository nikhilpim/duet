open Syntax

module MakeCFG (N : Map.OrderedType) (T : Map.OrderedType) = struct
  type nonterminal = N.t [@@deriving ord]
  type terminal = T.t [@@deriving ord]
  (* [@@deriving ord] *)
  type gsymbol = T of terminal | N of nonterminal[@@deriving ord]
  
  type production = (nonterminal * (gsymbol list)) [@@deriving ord]


  module NMap = Map.Make(N)
  module TMap = Map.Make(T)
  module PMap = Map.Make(struct type t = production let compare = compare_production end)

  type t = {
    start: nonterminal;
    productions: production list;
    terminals: terminal list;
    nonterminals: nonterminal list;
  }

  let empty (s: nonterminal) = {
    start = s;
    productions = [];
    terminals = [];
    nonterminals = [];
  }

  let add_terminal cfg t = { cfg with terminals = t :: cfg.terminals}
  let add_nonterminal cfg n = { cfg with nonterminals = n :: cfg.nonterminals}
  let add_production cfg nt out = { cfg with productions = (nt, out) :: cfg.productions}
  let set_start cfg s = { cfg with start = s}

  let gen_nt_symbols context nonterminals prefix = 
    let m = NMap.empty in 
    let consts = List.mapi (fun ind _ -> mk_const context (mk_symbol context ~name:(prefix^(string_of_int ind)) `TyInt)) nonterminals in
    let rec gen_map ls1 ls2 m = 
      match (ls1, ls2) with 
      | (h1::t1), (h2::t2) -> gen_map t1 t2 (NMap.add h1 h2 m)
      | [], [] -> m
      | _, _ -> m
    in
    gen_map nonterminals consts m 

  let gen_p_symbols context productions prefix = 
    let m = PMap.empty in 
    let consts = List.mapi (fun ind _ -> mk_const context (mk_symbol context ~name:(prefix^(string_of_int ind)) `TyInt)) productions in 
    let rec gen_map ls1 ls2 m = 
      match (ls1, ls2) with 
      | (h1::t1), (h2::t2) -> gen_map t1 t2 (PMap.add h1 h2 m)
      | [], [] -> m
      | _, _ -> m
    in
    gen_map productions consts m

  (* Computes the expression describing the parikh image of the curent CFG *)
  let parikh context grammar mapping = 

    (* Generate flow variables for each nonterminal and terminal, as well as
    a "distance" from the start nonterminal. mapping binds terminals to flow variables. *)
    let nmapping = gen_nt_symbols context grammar.nonterminals "N" in 
    let pmapping = gen_p_symbols context grammar.productions "P" in
    let dmapping = gen_nt_symbols context grammar.nonterminals "D" in 

    (* For all nonterminals, f(nt) = /sum_{nt->w} f(nt->w) *)
    let outgoing_sum_helper nt = 
      let curr_prods = List.filter (fun (n, _) -> nt = n ) grammar.productions in 
      let prod_symbols = List.map (fun prod -> PMap.find prod pmapping) curr_prods in 
      mk_eq context (NMap.find nt nmapping) (mk_add context prod_symbols)
    in

    (* For all symbols, nonterminal and terminals,
    f(s) = \sum_{nt->w} #_s(w) * f(nt->) + \delta_s
    where #_s(w) is the number of appearances of s in w and \delta_s = 1 iff s is the start *)
    let incoming_sum_helper s = 
      (* Counts occurrences of s in w where prod = n->w *)
      let count prod =
        let (_, out) = prod in 
        List.length (List.filter (fun e -> e = s) out) 
      in
      let prod_sum = mk_add context (List.map (fun p -> (mk_mul context [(mk_int context (count p)); (PMap.find p pmapping)])) grammar.productions) in 
      match s with
      | N s when s = grammar.start -> mk_eq context (NMap.find s nmapping) (mk_add context [(mk_int context 1); prod_sum])
      | N s -> mk_eq context (NMap.find s nmapping) prod_sum
      | T s -> mk_eq context (mapping s) prod_sum
      in
  
    (* In order to ensure connectedness, all nonterminals must have a valid distance from the start vertex 
    in the induced graph with only edges with nonzero flow. Our constraint ensures that if a nonterminal nt has nonzero
    flow, amongst all used productions n-> w leading to it, for at least one f(nt) = f(n) + 1
    For all nonterminals nt != s, (f(nt) > 0) -> (Or_{j->w, nt \in w} (f(j->w) > 0 And d(nt) = d(j) + 1))
    Obviously, d(s) = 0 *)
    let dist_helper nt = 
      (* Condition that a production n-> w is used and d(nt) = d(n) + 1 *)
      let dist_cond prod = 
        let (from, _) = prod in 
        let prod_used = mk_lt context (mk_zero context) (PMap.find prod pmapping) in
        let dist_constr = mk_eq context (NMap.find nt dmapping) (mk_add context [(NMap.find from dmapping); (mk_int context 1)]) in
        mk_and context [prod_used; dist_constr]
      in
      match nt with 
      | z when z = grammar.start -> mk_eq context (NMap.find nt dmapping) (mk_zero context)
      | _ -> 
        let prods = List.filter (fun (_, lst) -> List.mem (N nt) lst) grammar.productions in
        let if_dist = mk_or context (List.map dist_cond prods) in
        mk_if context (mk_lt context (mk_zero context) (NMap.find nt nmapping)) if_dist 
    in

    let all_symbols = (List.map (fun t -> T t) grammar.terminals) @ (List.map (fun n -> N n) grammar.nonterminals) in 

    let outgoing = mk_and context (List.map outgoing_sum_helper grammar.nonterminals) in
    let incoming = mk_and context (List.map incoming_sum_helper all_symbols) in
    let dist = mk_and context (List.map dist_helper grammar.nonterminals) in 
    mk_and context [outgoing; incoming; dist]
    
end

