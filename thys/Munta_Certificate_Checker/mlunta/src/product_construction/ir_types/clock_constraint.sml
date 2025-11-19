signature CLOCK_CONSTRAINT = sig
  datatype t =
           Lt of int * int * int |
           Le of int * int * int

  val from_guard: (int, int) Syntax.diff_constraint list -> t list
  val from_invar:  (int, int) Syntax.constraint -> t list
end

structure ClockConstraint : CLOCK_CONSTRAINT  = struct
datatype t =
             Lt of int * int * int |
             Le of int * int * int


  fun eq_triple (l, r, m) =
      [Le (l, r, m), Le (r, l, ~m)]

  fun gte_triple c (l, r, m) =
      single (c (r, l, ~m))

  fun lte_triple constr =
      constr #> single

  local
    open Syntax
  in
  fun from_bexp_constraint c m =
      case c of
              Difference.Single x => (x, 0, m) |
              Difference.Diff (l, r) => (l, r, m)

  fun from_invar e =
      case e of
              Constraint.Lt (l, v) => (l, 0, v) |> lte_triple Lt |
              Constraint.Le (l, v) => (l, 0, v) |> lte_triple Le |
              Constraint.Eq (l, v) => (l, 0, v) |> eq_triple |
              Constraint.Ge (l, v) => (l, 0, v) |> gte_triple Le |
              Constraint.Gt (l, v) => (l, 0, v) |> gte_triple Lt
  fun from_constraint e =
      case e of
              Constraint.Lt (l, v) => (from_bexp_constraint l v) |> lte_triple Lt |
              Constraint.Le (l, v) => (from_bexp_constraint l v) |> lte_triple Le |
              Constraint.Eq (l, v) => (from_bexp_constraint l v) |> eq_triple |
              Constraint.Ge (l, v) => (from_bexp_constraint l v) |> gte_triple Le |
              Constraint.Gt (l, v) => (from_bexp_constraint l v) |> gte_triple Lt


  end
  fun from_guard e = map from_constraint e |> flat
end

local
  open ClockConstraint
  fun ord (c, c') =
      let
            fun int_trip_ord trip trip' =
                trip_ord Int.compare Int.compare Int.compare (trip, trip')
      in
            case (c, c') of
                (Lt trip, Lt trip') =>  int_trip_ord trip trip' |
                (Le trip, Le trip') =>  int_trip_ord trip trip' |
                (Lt _, Le _) => LESS |
                (Le _, Lt _) => GREATER
      end
in
structure ConstraintSet = Table (type key = t val ord = ord)
end
