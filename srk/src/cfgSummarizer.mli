open Syntax 
module WG = WeightedGraph
module TF = TransitionFormula
module P = Pathexpr


module IntPair = WG.IntPair

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
        val call_edges : WG.RecGraph.t -> IntPair.t BatMap.Make(IntPair).t
        val context : WG.RecGraph.t -> P.context 
        val fold_reachable_edges : (int -> int -> 'a -> 'a) -> 'b WG.weighted_graph -> int -> 'a -> 'a
        val scc : IntPair.t -> WG.RecGraph.t -> IntPair.t list
    end
    )
: (sig 
    val rg : WG.RecGraph.t
    val algebra : T.t Pathexpr.nested_algebra
    val summarize : IntPair.t -> T.t
end)