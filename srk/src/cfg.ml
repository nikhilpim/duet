open Pathexpr

module type SyntaxSpec = sig
  type terminal
  type nonterminal
  type production

  type symbol = T of terminal | N of nonterminal

  val start : nonterminal
  val term_eq : terminal -> terminal -> int
  val nonterm_eq : nonterminal -> nonterminal -> int
  val prod_eq : production -> production -> int
end


module type CFG = sig
  module Syntax : SyntaxSpec
  open Syntax

  module Terminals : (Set.S with type elt = terminal)
  module Nonterminals : (Set.S with type elt = nonterminal)
  module Productions : (Set.S with type elt = production)
  
  module PMap : (Map.S with type key = production)

end

module MakeCFG (S : SyntaxSpec) : (CFG with module Syntax = S) = struct
  module Syntax = S
  open Syntax

  module Terminals = Set.Make (struct type t = Syntax.terminal let compare = term_eq end)
  module Nonterminals = Set.Make (struct type t = Syntax.nonterminal let compare = nonterm_eq end)
  module Productions = Set.Make (struct type t = Syntax.production let compare = prod_eq end )

  module PMap = Map.Make (struct type t = Syntax.production let compare = prod_eq end)

end