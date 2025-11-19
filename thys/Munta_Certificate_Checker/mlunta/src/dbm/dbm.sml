(* Module for the DBMs and the corresponding functor *)

(* Conventions for DBMs: variables which are DBMs are written as a capital D. *)
(* Functions that copy DBMs: *)
(* + copy *)
(* + split *)
(* + convex_hull *)

(* Signature for the basic DBM traits needed only for model checking: *)
signature DBM_ALG =
sig
  structure Entry : DBM_ENTRY
  type t
  type bound
  type clock = int
  type extrapolation = (clock -> Entry.t) -> (clock -> Entry.t) -> t -> t

  (* Creating DBMs: *)
  (* XXX: What from list should exist  *)
  val from_list : Entry.t list list -> t
  val from_int_rep_list : IntRep.t list list -> t
  val init: int -> t
  (* Copies DBM array: *)
  val copy: t -> t

  (* DBM operations: *)
  val close : t -> t
  val subsumption : t -> t -> bool
  val up : t -> t
  val And : bound -> t -> t
  val free : clock -> t -> t
  val reset : clock -> int -> t -> t
  (* copies clocks: copy_clock x y sets x to the value of y: *)
  val copy_clock :  clock -> clock -> t -> t
  val shift : clock -> int -> t -> t
  val empty: t -> bool

  (* Extrapolations: *)
  (* Without Lower/Upper Bounds: *)
  val norm_k : extrapolation
  (* With Lower and Upper Bounds: *)
  val extra_lu: extrapolation

  (* Convex Hull: *)
  val or: t -> t -> t
  val convex_hull: t list -> t


  (* Normalization for Timed Automata with Difference Constraints: *)
  val core_norm : extrapolation
                  -> (clock -> Entry.t) * (clock -> Entry.t)
                  -> bound list
                  -> t
                  -> t
  val split : bound list -> t -> t list
  val norm_k_G : extrapolation
                 -> (clock -> Entry.t) * (clock -> Entry.t)
                 -> bound list
                 -> t
                 -> t list
end


(* Overall DBM signature for testing and serializing DBMs: *)
signature DBM = sig
  include DBM_ALG
  type zone = t
  include BINARY where type from = t
  val equal: t -> t -> bool
  val to_string: t -> string
end

functor DBM(structure E : DBM_ENTRY structure M : MATRIX) : DBM =
struct
open Iter
structure Entry = E
structure DIter = DBMIter(M)
open Entry
type bound = int * int * Entry.t
type t = Entry.t M.matrix
type clock = int
type zone = t
type from = t
type to = Word8Vector.vector
type extrapolation = (clock -> Entry.t) -> (clock -> Entry.t) -> t -> t

val inf = E.inf
val toElem = E.from_int

fun init n_clocks =
    let
      val z = E.==< 0
    in
      M.create n_clocks z
    end

val copy = M.copy
val from_list = M.fromList

fun empty D =
    let
      val n = M.dim D
      fun empty' i =
              if i >= n then false
              else if M.sub i i D |<| (E.==< 0) then true
              else empty' (i + 1)
    in
      empty' 0
    end

fun from_int_rep_list ls =
    List.map (fn elem => List.map (fn x => toElem x) elem) ls
    |> from_list

fun iter comb body D = for (comb D) (body D)
fun iter_return comb body D = iter comb body </ tap \> D

fun close_loop D =
          fn (k, i, j, D_ij) =>
             let
                   val D_ik = M.sub i k D
                   val D_kj = M.sub k j D
                   val minimum = E.min D_ij (D_ik |+| D_kj)
             in
                   M.update i j minimum D
             end

fun close D = iter_return DIter.close close_loop D

fun subsumption l r =
    M.cmp (op |<=|) l r

fun up D = iter_return DIter.up
                   (fn D => fn i => M.update i 0 E.inf D)
                   D

fun add_and_update i j clock D =
    let
          val addition =
              M.sub i clock D |+| M.sub clock j D
    in
          if addition |<| M.sub i j D
          then M.update i j addition D
          else ()
    end

fun and_loop x y D = for (DIter.And D)
                                   (
                                     fn (i, j) =>
                                        (
                                          add_and_update i j x D;
                                          add_and_update i j y D
                                        )
                                   )

fun And (x, y, b) D =
    let
        val smaller_z = (M.sub y x D |+| b) |<| (E.==< 0)
        val bound_smaller = b |<| M.sub x y D
        fun else_clause x y b f D =
            ( M.update x y b D;
              f x y D
            )
    in
          case (smaller_z, bound_smaller) of
              (true, _) => tap (M.update 0 0 (E.==< (~1)))
                                      D
            | (false , true) => tap (else_clause x y b and_loop) D
            | _ => D
    end

(**
* Compute convex union of D1 and D2.
* D1 will be updated.
* XXX Could be implemented slightly more efficiently.
*)
fun or' D1 D2 =
        (M.appij
                (fn (i, j, a) =>
                    if a |>| M.sub i j D1 then M.update i j a D1
                    else ())
                D2;
         D1)

fun or D1 D2 = or' D1 D2 |> close

(**
* Compute the convex hull of the list of dbms.
* Precondition: the input list is not empty.
*)
fun convex_hull (x :: xs) = fold (flip or') xs (M.copy x) (*|> close*)

fun free x D =
    let
        fun free_body D (x, i, D_i0) =
            (
              M.update x i E.inf D;
              M.update i x (D_i0) D
            )
    in
      iter_return (DIter.free x) free_body D
    end

fun reset x value D =
    let
        val m = E.==< value
        val m_neg = E.==< (~value)
        fun reset_body D (x, i, D_0i, D_i0) =
            (
              M.update x i (m |+| D_0i) D;
              M.update i x (D_i0 |+| m_neg) D
            )
    in
      iter_return (DIter.reset x) reset_body D
    end

fun copy_clock x y D =
    let
        fun copy_body D (x, i, D_yi, D_iy) =
            (
              M.update x i D_yi D;
              M.update i x D_iy D
            )
    in
        (
          iter (DIter.copy_clock x y) copy_body D;
          M.update x y E.zero D;
          M.update y x E.zero D;
          D
        )
    end

fun shift_body value D (x, i, D_xi, D_ix) =
    let val m = E.==< value in
        (
          M.update x i (D_xi |+| m) D;
          M.update i x (D_ix |+| E.|~| m) D
        )
    end

fun shift x value D =
    (
      iter (DIter.shift x) (shift_body value) D;
      M.update x 0 (E.max (M.sub x 0 D) (E.==< 0)) D;
      M.update 0 x (E.min (M.sub 0 x D) (E.==< 0)) D;
      D
    )

fun norm_k_body k_pos k_neg D =
    fn (i, j, D_ij) =>
       let
             open E
             val small_inf = D_ij == inf
             val k_i = k_pos i
             val smaller_ki = D_ij |>| k_i
             val neg_k_j = k_neg j
             val smaller_kj =
                 D_ij |<| neg_k_j
       in
             case (small_inf, smaller_ki, smaller_kj) of
                 (false, true, _) => M.update i j inf D
               | (false, _, true) => M.update i j neg_k_j D
               | _  => ()
       end

fun norm_k_loop k_pos k_neg D =
    iter (DIter.norm_k)
          (norm_k_body k_pos k_neg) D

fun norm_k k_pos k_neg D =
    (
      norm_k_loop k_pos k_neg D;
      close D
    )

fun satisfied (x, y, m) D =
    E.check_neg (m |+| M.sub y x D)

fun not_constraint (x, y, m) = (y, x, E.not_bound m)

fun core_norm extra (k_pos, k_neg) G_ds D =
    let
      fun inner G_ds G_unsat =
          case G_ds of
              [] => G_unsat |
              (g::gs) => let val not_g = not_constraint g in
                          (case (not (satisfied g D), not (satisfied not_g D)) of
                               (true, true) => inner gs (g::not_g::G_unsat) |
                               (true, _) => inner gs (g::G_unsat) |
                               (_, true) => inner gs (not_g::G_unsat) |
                               (_, _) => inner gs G_unsat
                          )
                        end
    in
      D
      |> extra k_pos k_neg
      |> flip (foldl (fn ((x, y, m), D') => And (y, x, E.not_bound m) D'))
              (inner G_ds [])
    end

fun split G_ds D = let
  fun copy_and g D = D |> copy |> And g
  fun inner1 Q Q' G_ds = let
    fun inner2 Q Q' g =
        case Q of
            [] => Q' |
            (d::ds) => inner2 ds (let val not_g = not_constraint g in
                                   if satisfied g d andalso
                                      satisfied (not_constraint g) d
                                   then copy_and g d :: copy_and not_g d:: Q'
                                   else copy d :: Q' end) g
  in
    case G_ds of
        [] => Q |
        (g::gs) => inner1 (inner2 Q Q' g) [] gs
  end
in inner1 (single D) [] G_ds end

fun norm_k_G extra k G_ds D =
    let val core_norm = core_norm extra k G_ds in
      foldl (fn (D', Q) => core_norm D' :: Q) [] (split G_ds D)
    end

(* upper is -u(j) and LT lower is  l(j)*)
fun extra_lu lower upper D =
    (
      for (DIter.norm_k D)
          (fn (i, j, D_ij) =>
            let
              open E
              val is_unbound = D_ij == inf
              val l_i = lower i
              val bigger_li = D_ij |>| l_i
              val u_j = upper j
              val smaller_uj =
                  D_ij |<| u_j
            in
              case (is_unbound, bigger_li, smaller_uj) of
                  (false, true, _) => M.update i j inf D
                | (false, _, true) => M.update i j u_j D
                | _  => ()
            end
          );
      close D
    )

fun serialize D =
    M.foldl (fn (x, acc) => Entry.serialize x :: acc) [] D
    |> rev
    |> Word8Vector.concat

fun equal D D' =
    case (subsumption D D', subsumption D' D) of
        (true, true) => true |
        _ => false

fun to_string D =
    let
      val len = M.dim D
        val last_idx = len * len - 1
        val print_elem =
         fn (i, elem, acc) =>
            let
              val smaller = i < last_idx
              val new_line = i mod len = 0
              val brk = if new_line then "\n" else ""
              val eq_z = i = 0
            in
                (case (eq_z, smaller) of
                     (true, _) => acc ^ brk ^ (E.to_string elem)
                   | (false, true) => acc ^ ", " ^ brk ^ (E.to_string elem)
                   | (false, false)  => acc ^ ", " ^ brk ^ (E.to_string elem) ^ "]")
            end
    in
        M.foldli print_elem "[" D
    end

end




functor MakeLinDBM(Entry : DBM_ENTRY) = DBM(structure E = Entry and
                                                      M = LnLayoutMatrix)

structure LnDBM8Bit = MakeLinDBM(Entry8Bit)
structure LnDBM32Bit = MakeLinDBM(Entry8Bit)
structure LnDBM64Bit = MakeLinDBM(Entry64Bit)
structure LnDBMInt = MakeLinDBM(Entry)
