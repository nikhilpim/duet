open Syntax 
module WG = WeightedGraph
module TF = TransitionFormula
module P = Pathexpr


module IntPair = SrkUtil.IntPair

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
    (Input : sig
        val graph : T.t label WG.weighted_graph
        val src : int
        val lossy : bool
        val split_disjuncts : bool
        val ind_bounds : bool
    end
    )
: (sig 
    val rg : WG.RecGraph.t
    val algebra : T.t Pathexpr.nested_algebra
    val summarize : IntPair.t -> T.t
end)