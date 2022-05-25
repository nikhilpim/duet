(* Context Free Grammars *)

module type Symbol = sig 
  type t
  val compare : t -> t -> int
  val str: t -> string
end

module MakeCFG (N : Symbol) (T : Symbol) : (sig
  type terminal = T.t
  type nonterminal = N.t
  type gsymbol = T of terminal | N of nonterminal
  type production
  type t
  val empty: nonterminal -> t
  val add_production: t -> nonterminal -> gsymbol list -> t
  val set_start: t -> nonterminal -> t
  val parikh: 'a Syntax.context -> t -> (terminal -> 'a Syntax.arith_term) -> 'a Syntax.formula
  val weak_labeled: t -> (int -> nonterminal -> nonterminal) -> (int -> terminal -> terminal) -> t
  end)
