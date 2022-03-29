(* Context Free Grammars *)

module type CFG = sig
  type terminal
  type nonterminal
  type gsymbol = T of terminal | N of nonterminal
  type production
end

module MakeCFG (N : Map.OrderedType) (T : Map.OrderedType) : (CFG)
