(* Context Free Grammars *)



module MakeCFG (N : Map.OrderedType) (T : Map.OrderedType) : (sig
  type terminal = T.t
  type nonterminal = N.t
  type gsymbol = T of terminal | N of nonterminal
  type production
  type t
  val empty: nonterminal -> t
  val add_production: t -> nonterminal -> gsymbol list -> t
  val set_start: t -> nonterminal -> t
  val parikh: 'a Syntax.context -> t -> (terminal -> 'a Syntax.arith_term) -> 'a Syntax.formula
end)
