(* XXX: Test not_bound and test mod_lsb *)

(* A simple datatype for representing clockbounds *)
signature INT_REP = sig
    datatype t = LT of int | LTE of int | Inf
end

structure IntRep = struct
datatype t = LT of int | LTE of int | Inf
end

(* A dbm entry without serialization *)
signature PROTO_ENTRY =
sig
    type t

    val from_int: IntRep.t -> t
    (* Constructors for bounds: *)
    val =< : int -> t
    val ==< : int -> t
    val inf: t

    (* Special constant bounds *)
    val zero: t

    (* modifies LSB according to the first argument *)
    val mod_lsb: bool -> t -> t
    val add: t -> t -> t
    val |+| : t * t -> t
    val min: t -> t -> t
    val max: t -> t -> t

    (* Maximum used for ceilings since they treat an oo differently *)
    (* than normal max and min operations *)
    val max_ceil: t -> t -> t

    val |<=| : t * t -> bool
    val |<| : t * t -> bool
    val |>| : t * t -> bool
    val == : t * t -> bool

    val cmp: t -> t -> order

    (* negates only the value inside of the bound: *)
    (* |~| LT x ==> LT (~ x) *)
    val |~| : t -> t

    (* negating a bound as a whole:*)
    (* not_bound LT x ==> LTE (~ x)*)
    val not_bound: t -> t

    (* checks whether a bound is negative *)
    val check_neg: t -> bool

    val to_string: t -> string
end

(* The whole needed dbm_entry signature *)
signature DBM_ENTRY = sig
  include PROTO_ENTRY
  include BINARY where type from = t
end
