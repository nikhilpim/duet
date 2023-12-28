open Syntax
module L = Linear
module Q = L.QQMatrix
module V = L.QQVector
module A = Abstract

type vector = int * V.t
type matrix = (int * int) * Q.t
type vasr_transform = (vector * bool) list 
type vasr_var_id = int * int
type coherent_linear_map = (matrix * int) list
type vasr = (vasr_transform list) BatMap.Make(SrkUtil.IntPair).t

val dim : vasr -> int
val abstract_single_tf : 'a context -> (symbol * symbol) list -> 'a formula 
    -> coherent_linear_map * vasr_transform

val sep_comp : coherent_linear_map -> coherent_linear_map -> coherent_linear_map
val sep_image_vasr : coherent_linear_map -> vasr_transform -> vasr_transform

val sep_pushout : coherent_linear_map -> coherent_linear_map -> 
    coherent_linear_map * coherent_linear_map

val genVASR : 'a context -> (symbol * symbol) list -> 'a formula BatMap.Make(SrkUtil.IntPair).t 
    -> coherent_linear_map * vasr

val transition : 'a context -> (symbol * symbol) list -> 
    (SrkUtil.IntQuad.t -> 'a Syntax.arith_term) -> vasr -> coherent_linear_map ->
    'a formula

val well_formed : 'a context -> (SrkUtil.IntQuad.t -> 'a Syntax.arith_term)
        -> vasr -> 'a formula

val get_supp_var_map : 'a context -> vasr -> (SrkUtil.IntTriple.t -> 'a Syntax.arith_term)
        -> SrkUtil.IntPair.t list -> (SrkUtil.IntQuad.t -> 'a Syntax.arith_term) * 'a Syntax.formula