open Syntax
open Batteries 

module type Symbol = sig 
  type t
  val compare : t -> t -> int
  val show: t -> string
end

module MakeCFG (N : Symbol) (T : Symbol) = struct
  type nonterminal = N.t [@@deriving ord]
  type terminal = T.t [@@deriving ord]
  type gsymbol = T of terminal | N of nonterminal[@@deriving ord]
  
  type production = (nonterminal * (gsymbol list)) [@@deriving ord]


  module NMap = Map.Make(N)
  module TMap = Map.Make(T)
  module PMap = Map.Make(struct type t = production let compare = compare_production end)
  module NSet = Set.Make(N)
  module TSet = Set.Make(T)
  module PSet = Set.Make (struct type t = production let compare = compare_production end)
  module GSet = Set.Make(struct type t = gsymbol let compare = compare_gsymbol end)

  type t = {
    start: nonterminal;
    productions: PSet.t;
    terminals: TSet.t;
    nonterminals: NSet.t;
  }

  let size = fun t -> PSet.cardinal t.productions, TSet.cardinal t.terminals, NSet.cardinal t.nonterminals

  let empty (s: nonterminal) = {
    start = s;
    productions = PSet.empty;
    terminals = TSet.empty;
    nonterminals = NSet.singleton(s);
  }

  let add_production cfg nt out = { cfg with
    productions = PSet.add (nt, out) cfg.productions; 
    terminals = List.fold_left (fun s o -> match o with | T o -> (TSet.add o s) | _ -> s) cfg.terminals out; 
    nonterminals = List.fold_left (fun s o -> match o with | N o -> (NSet.add o s) | _ -> s) cfg.nonterminals (N nt :: out); 
    }
  let set_start cfg s = { cfg with start = s}

  let nonterminals cfg = NSet.elements cfg.nonterminals
  let terminals cfg  = TSet.elements cfg.terminals

  let nname n = "N" ^ (N.show n)
  let tname t = "T" ^ (T.show t)
  let pname p = 
    let (nt, out) = p in
    "P " ^ (nname nt) ^ " -> " ^ (List.fold_left (fun str sym -> str ^ " " ^ (match sym with | T t -> (tname t) | N n -> (nname n))) "" out)

  (* Eliminates all useless symbols from grammar. L(prune(G)) = L(G) *)
  let prune grammar = 
    (* A nonterminal is generating if it derives some terminal string *)
    let rec find_generating g_nts = 
      let generating = function 
        | T _ -> true
        | N n -> (NSet.mem n g_nts)
      in 
      let size = NSet.cardinal g_nts in 
      let g_nts = PSet.fold (fun (n, ls) g_nts -> 
        if (not (NSet.mem n g_nts) && List.for_all generating ls) 
          then (NSet.add n g_nts)
          else g_nts
        ) grammar.productions g_nts in 
      if (NSet.cardinal g_nts > size) then find_generating g_nts else g_nts
    in 
    (* A symbol is reachable if there is a derivation from the start symbol to some word which uses the symbol *)
    let rec find_reachable reachable = 
      let size = GSet.cardinal reachable in 
      let reachable = PSet.fold (fun (n, ls) reachable ->
        if (GSet.mem (N n) reachable) 
          then GSet.add_seq (List.to_seq ls) reachable
          else reachable
        ) grammar.productions reachable in 
      if (GSet.cardinal reachable > size) then find_reachable reachable else reachable 
    in
    let generating = find_generating NSet.empty in 
    let reachable = find_reachable (GSet.singleton (N grammar.start)) in 
    
    let pruned_prods = PSet.filter (fun (n, ls) ->
      let ls = (N n) :: ls in 
      List.for_all (function 
      | N n -> (NSet.mem n generating) && (GSet.mem (N n) reachable)
      | T t -> (GSet.mem (T t) reachable) 
      ) ls
      ) grammar.productions in 
    empty grammar.start 
    |> PSet.fold (fun (n, ls) g -> add_production g n ls) pruned_prods

  let gen_nt_symbols context nonterminals prefix = 
    let m = NMap.empty in 
    let consts = List.map (fun n -> mk_const context (mk_symbol context ~name:(prefix^(nname n)) `TyInt)) nonterminals in
    let rec gen_map ls1 ls2 m = 
      match (ls1, ls2) with 
      | (h1::t1), (h2::t2) -> gen_map t1 t2 (NMap.add h1 h2 m)
      | [], [] -> m
      | _, _ -> m
    in
    gen_map nonterminals consts m 

  let gen_p_symbols context productions = 
    let m = PMap.empty in 
    let consts = List.map (fun p -> mk_const context (mk_symbol context ~name:(pname p) `TyInt)) productions in 
    let rec gen_map ls1 ls2 m = 
      match (ls1, ls2) with 
      | (h1::t1), (h2::t2) -> gen_map t1 t2 (PMap.add h1 h2 m)
      | [], [] -> m
      | _, _ -> m
    in
    gen_map productions consts m

  (* Computes the expression describing the parikh image of the curent CFG *)
  let parikh context grammar mapping nmapping = 
    (* Generate flow variables for each nonterminal and terminal, as well as
    a "distance" from the start nonterminal. mapping binds terminals to flow variables. *)
    let nts = NSet.elements grammar.nonterminals in
    let ts = TSet.elements grammar.terminals in
    let ps = PSet.elements grammar.productions in 

    let pmapping = gen_p_symbols context ps in
    let dmapping = gen_nt_symbols context nts "D" in 

    (* For all nonterminals, f(nt) = /sum_{nt->w} f(nt->w) *)
    let outgoing_sum_helper nt = 
      let curr_prods = List.filter (fun (n, _) -> nt = n ) ps in 
      let prod_symbols = List.map (fun prod -> PMap.find prod pmapping) curr_prods in 
      mk_eq context (nmapping nt) (mk_add context prod_symbols)
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
      let prod_sum = mk_add context (List.map (fun p -> (mk_mul context [(mk_int context (count p)); (PMap.find p pmapping)])) ps) in
      match s with
      | N s when s = grammar.start -> mk_eq context (nmapping s) (mk_add context [(mk_one context); prod_sum])
      | N s -> mk_eq context (nmapping s) prod_sum
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
        let prods = List.filter (fun (_, lst) -> List.mem (N nt) lst) ps in
        let if_dist = mk_or context (List.map dist_cond prods) in
        mk_if context (mk_lt context (mk_zero context) (nmapping nt)) if_dist 
    in

    let all_symbols = (List.map (fun t -> T t) ts) @ (List.map (fun n -> N n) nts) in 

    let outgoing = mk_and context (List.map outgoing_sum_helper nts) in
    let incoming = mk_and context (List.map incoming_sum_helper all_symbols) in
    let nonneg = List.map (fun t -> mk_leq context (mk_zero context) (mapping t)) ts 
    @ List.map (fun n -> mk_leq context (mk_zero context) (nmapping n)) nts
    @ List.map (fun p -> mk_leq context (mk_zero context) (PMap.find p pmapping)) ps
    |> mk_and context in
    let dist = mk_and context (List.map dist_helper nts) in 
    mk_and context [outgoing; incoming; dist; nonneg]
    
  let is_weak_labelable grammar = 
    PSet.fold (fun (_, out) b  -> b && (List.length out <= 2)) grammar.productions true
    
  (* Generates grammar to produce "weak labelings" of input grammar, marking n symbols in each word
  Any word w in the language of the original grammar will be decomposed as follows:
  w -> w_0 t_0 w_1 t_1 ... t_k w_k for some 0 <= k <= |T|
  get_ith_nt and get_ith_t need to return unique nonterminals and terminals per natural
  ind needs to return a unique natural per natural pair.
  (get_ith_t i t) generates a terminal in w_i.
  (get_ith_t (ind i i) t) generates t_i.
  (get_ith_nt i nt) should derive w_i
  (get_ith_nt (ind i j) nt) should derive w_i t_i ... t_j w_{j+1} 
  (get_ith (-1) nt) is a special dummy node for if we wish to set nt to be the start symbol*)
  let weak_labeled grammar get_ith_nt get_ith_t ind n = 
    assert (is_weak_labelable grammar);

    (* Productions for subgrammars generating w_i *)
    let all_prods = BatEnum.fold (fun ls index -> 
      List.map (fun (nt, out) -> 
        ((get_ith_nt index nt), List.map (fun s -> 
          match s with 
          | T t -> T (get_ith_t index t)
          | N n -> N (get_ith_nt index n)
          ) out)) (PSet.elements grammar.productions) @ ls
      ) [] (0--n) in 
    
    let all_prods = List.fold_left (fun ls prod ->
      let pairs = BatEnum.fold (fun ls i -> 
        BatEnum.fold (fun ls j -> (i, j) :: ls) ls (i--^n)
        ) [] (0--^n) in 
      match prod with
      | (_, []) -> ls 
      | (nt, [N out]) -> List.fold_left (fun ls (i, j) -> ((get_ith_nt (ind i j) nt), [N (get_ith_nt (ind i j) out)]) :: ls ) ls pairs
      | (nt, [T out]) -> List.fold_left (fun ls (i, j) -> if i == j then ((get_ith_nt (ind i j) nt), [T (get_ith_t (ind i j) out)]) :: ls else ls) ls pairs
      | (nt, [T out; N out2]) -> List.fold_left (fun ls (i, j) -> 
        let ls = ((get_ith_nt (ind i j) nt), [T (get_ith_t i out); N (get_ith_nt (ind i j) out2)]) :: ls in 
        if i == j then ((get_ith_nt (ind i j) nt), [T (get_ith_t (ind i j) out) ; N (get_ith_nt (j+1) out2)]) :: ls 
        else ((get_ith_nt (ind i j) nt), [T (get_ith_t (ind i i) out); N (get_ith_nt (ind (i+1) j) out2)]) :: ls
        ) ls pairs
      | (nt, [N out; T out2]) -> List.fold_left (fun ls (i, j) -> 
        let ls = ((get_ith_nt (ind i j) nt), [N (get_ith_nt (ind i j) out); T (get_ith_t (j+1) out2)]) :: ls in 
        if i==j then ((get_ith_nt (ind i j) nt), [N (get_ith_nt i out); T (get_ith_t (ind i j) out2)]) :: ls 
        else ((get_ith_nt (ind i j) nt), [N (get_ith_nt (ind i (j-1)) out); T (get_ith_t (ind j j) out2)]) :: ls
        ) ls pairs
      | (nt, [N out; N out2]) -> List.fold_left (fun ls (i, j) -> 
        let ls = ((get_ith_nt (ind i j) nt), [N (get_ith_nt (ind i j) out); N (get_ith_nt (j+1) out2)]) :: ls in 
        let ls = ((get_ith_nt (ind i j) nt), [N (get_ith_nt i out); N (get_ith_nt (ind i j) out2)]) :: ls in 
        BatEnum.fold (fun ls k -> ((get_ith_nt (ind i j) nt), [N (get_ith_nt (ind i k) out); N (get_ith_nt (ind (k+1) j) out2)]) :: ls) ls (i--^j)
        ) ls pairs
      | _ -> assert false
      ) all_prods (PSet.elements grammar.productions) in 

    let all_prods = BatEnum.fold (fun ls i -> (List.map (fun nt -> (get_ith_nt (-1) nt), [N (get_ith_nt (ind i (n-1)) nt)]) (NSet.elements grammar.nonterminals)) @ ls) all_prods (0--^n) in 
    let all_prods = (List.map (fun nt -> (get_ith_nt (-1) nt), [N (get_ith_nt n nt)]) (NSet.elements grammar.nonterminals)) @ all_prods in  
    List.fold_left (fun cfg (nt, out) -> add_production cfg nt out) (empty (get_ith_nt (-1) grammar.start)) all_prods

  let pp (fmt : Format.formatter) (grammar: t) = 
    SrkUtil.pp_print_list (fun fmt prod ->
      Format.fprintf fmt "@[%s @]@." (pname prod) 
      ) fmt (PSet.to_list grammar.productions)
end

