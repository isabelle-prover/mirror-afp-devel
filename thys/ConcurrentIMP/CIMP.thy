(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP
imports
  CIMP_pred
  CIMP_lang
  CIMP_vcg
  "HOL-Library.Sublist"
begin

ML_file \<open>mkterm_antiquote.ML\<close>

text\<open>

Infrastructure for reasoning about CIMP programs. See AFP entry \<open>ConcurrentGC\<close> for examples
of use.

\<close>

named_theorems com "Command definitions"
named_theorems loc "Location set membership cache"

ML\<open>

signature CIMP =
sig
    val com_locs_fold : (term -> 'b -> 'b) -> 'b -> term -> 'b
    val com_locs_map : (term -> 'b) -> term -> 'b list
    val locset : thm -> local_theory -> local_theory
end;

structure Cimp : CIMP =
struct

fun com_locs_fold f x (Const (@{const_name Request}, _) $ l $ _ $ _ )    = f l x
  | com_locs_fold f x (Const (@{const_name Response}, _) $ l $ _)        = f l x
  | com_locs_fold f x (Const (@{const_name LocalOp}, _) $ l $ _)         = f l x
  | com_locs_fold f x (Const (@{const_name Cond1}, _) $ l $ _ $ c)       = com_locs_fold f (f l x) c
  | com_locs_fold f x (Const (@{const_name Cond2}, _) $ l $ _ $ c1 $ c2) = com_locs_fold f (com_locs_fold f (f l x) c1) c2
  | com_locs_fold f x (Const (@{const_name Loop}, _) $ c)                = com_locs_fold f x c
  | com_locs_fold f x (Const (@{const_name While}, _) $ l $ _ $ c)       = com_locs_fold f (f l x) c
  | com_locs_fold f x (Const (@{const_name Seq}, _) $ c1 $ c2)           = com_locs_fold f (com_locs_fold f x c1) c2
  | com_locs_fold f x (Const (@{const_name Choose}, _) $ c1 $ c2)        = com_locs_fold f (com_locs_fold f x c1) c2
  | com_locs_fold _ x _ = x;

fun com_locs_map f com = com_locs_fold (fn l => fn acc => f l :: acc) [] com

(* Cache location set membership facts.

For each label, decide membership in the given set. We'd like an
attribute to do this (for syntactic convenience) but these get
executed multiple times. Solution: just invoke some ML to do the job.

If the label set and com types differ, we probably get a nasty error.

No need to consider locations of @{const "Response"}s; could tweak
@{text "com_locs_fold"} to reflect this.

*)

fun locset thm ctxt =
  let
    val set_name = thm |> Thm.cprop_of |> Thm.dest_equals |> fst
    val thm_name =
      set_name |> Thm.term_of |> dest_Const |> fst
      |> Long_Name.base_name |> (fn def => def ^ "_membs")
    fun mk_memb_term lthy l =
      Thm.cterm_of lthy (@{mk_term "?x : ?S" (x, S)} (l, Thm.term_of set_name))
    val coms = Named_Theorems.get ctxt @{named_theorems "com"} |> map (Thm.cprop_of #> Thm.dest_equals #> snd #> Thm.term_of)
    val memb_terms = maps (com_locs_map (mk_memb_term ctxt)) coms
    val thms =
      Par_List.map (Simplifier.rewrite (ctxt addsimps ([thm] @ Named_Theorems.get ctxt @{named_theorems "loc"}))) (* probably want the ambient simpset + some stuff *)
        memb_terms
    fun define_lemmas name attrs thm_list = Local_Theory.note ((Binding.name name, attrs), thm_list) #>> snd;
  in
    ctxt
    |> define_lemmas thm_name
        [(* Attrib.internal (K (Clasimp.iff_add)), *) Attrib.internal (K (Named_Theorems.add @{named_theorems "loc"}))] thms
    |> snd
  end;

end;

\<close>

end
(*>*)
