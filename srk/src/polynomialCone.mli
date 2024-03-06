(** Polynomial cone abstract domain. A polynomial cone corresponds to a set of
    polynomials.  It is used to maintain a maximal set of non-negative
    polynomials w.r.t. the theory of LIRR. *)
open Polynomial
open Syntax

type t

val pp : (Format.formatter -> int -> unit) -> Format.formatter -> t -> unit

(** Compute the intersection of two polynomial cones. Intersection of
    polynomial cones A, B corresponds to the join of their corresponding
    polynomial equations and inequalities. *)
val intersection : t -> t -> t

(** Compute the projection of a polynomial cone, given what dimensions to
    keep. *)
val project : t -> (int -> bool) -> t

(** [inverse_homomorphism C [(y1, fn) ..., (yn, fn)]] computes the inverse image
    F^{-1}(C), where F : QQ[y1, ..., yn] -> QQ[xs] is the ring homomorphism sending
    [yi] to [fi].
    It is assumed that the variables [y1, ..., yn] are all distinct from [xs].

    TODO: [QQXs.dim] is currently [Monomial.t], but the [QQXs] interface also
    mentions [int] as dimension.
*)
val inverse_homomorphism : t -> (Monomial.dim * QQXs.t) list -> t

(** [inverse_linear_map C [(y1, fn) ..., (yn, fn)]] = (lines, rays)
    computes the inverse image F^{-1}(C), where F : QQ[y1, ..., yn]^1 -> QQ[xs]
    is the linear map sending [yi] to [fi].
    This inverse image is a convex cone in the vector space QQ[y1, ..., yn]^1
    of linear polynomials in [ys], and is thus presented as a set of
    lines (two-sided generators) and a set of rays.

    It is assumed that the variables [y1, ..., yn] are all distinct from [xs].
*)
val inverse_linear_map : t -> (Monomial.dim * QQXs.t) list -> (QQXs.t list * QQXs.t list)

(** [inverse_image C f] computes [f^{-1}(C)], where the array [f =
   [f_0,...,f_n]] is regarded as the homomorphism Q[x_0,...,x_n] -> Q[X] that
   sends [x_i -> f_i]. *)
val inverse_image : t -> QQXs.t array -> t

(** Get the ideal part of a polynomial cone. *)
val get_ideal : t -> Rewrite.t

(** Get the cone part of a polynomial cone. *)
val get_cone_generators : t -> (QQXs.t BatList.t)

(** Change the monomial ordering of a polynomial cone. *)
val change_monomial_ordering: t ->
  (Monomial.t -> Monomial.t -> [ `Eq | `Lt | `Gt  ]) -> t

(** A polynomial cone that corresponds to the empty set of polynomials. *)
val top : t

val make_cone : Polynomial.Rewrite.t -> QQXs.t BatList.t -> t

(** Compute the least regular polynomial cone that contains the given one. *)
val regularize : t -> t

(** Add a list of zero polynomials and a list of nonnegative polynomials to
    the set represented by an existing cone. *)
val add_generators: ?zeros:(QQXs.t BatList.t) -> ?nonnegatives:(QQXs.t BatList.t) -> t -> t

(** Test if a polynomial is contained in the cone. *)
val mem : QQXs.t -> t -> bool

(** Test if a polynomial cone is proper. This is equivalent to querying if -1 belongs to this cone. *)
val is_proper: t -> bool

(** Test if two polynomial cones are equal. *)
val equal: t -> t -> bool

(** Compute a (finite) formula representation of a polynomial cone. *)
val to_formula : 'a context -> (int -> 'a arith_term) -> t -> 'a formula

val leq : t -> t -> bool

(** Intersect the cone with the linear span of the monomials satisfying the
    given predicate.  Assumes that the set of monomials satisfying the given
    predicate is downwards-closed w.r.t. the monomial ordering of the cone. *)
val restrict : (Monomial.t -> bool) -> t -> t
