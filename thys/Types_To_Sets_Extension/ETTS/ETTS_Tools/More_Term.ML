(* Title: ETTS/ETTS_Tools/More_Term.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Term from the standard library of 
Isabelle/Pure.
*)

signature TERM =
sig
  include TERM
  val is_cv : term -> bool
  val sort_eqT : theory -> typ * typ -> bool
end;

structure Term: TERM  =
struct

open Term;

fun is_cv t = is_Const t orelse is_Var t

fun sort_eqT thy (T, U) =
  let val algebra = Sign.classes_of thy
  in Sorts.sort_eq algebra (Term.dest_atyp_sort T, Term.dest_atyp_sort U) end;

end;