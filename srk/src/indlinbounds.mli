module IntPair = SrkUtil.IntPair
module WG = WeightedGraph

val bounding_model :
  'a Syntax.context ->
  WG.RecGraph.t ->
  'b Pathexpr.nested_algebra ->
  (Syntax.symbol * Syntax.symbol) list ->
  (string -> Syntax.symbol * Syntax.symbol) ->
  ((Syntax.symbol * Syntax.symbol) list -> 'a Syntax.formula -> 'b) ->
  ('b -> 'a Syntax.formula) ->
  bool ->
  IntPair.t ->
  (IntPair.t * ('a Syntax.formula * 'a Syntax.arith_term list)) list
