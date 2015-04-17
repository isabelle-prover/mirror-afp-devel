(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure Com = Named_Thms
  (val name = @{binding "com"}
   val description = "Command definitions")

structure Loc = Named_Thms
  (val name = @{binding "loc"}
   val description = "Location set membership cache")

signature CIMP =
sig
    val com_locs_fold : (term -> 'b -> 'b) -> 'b -> term -> 'b
    val com_locs_map : (term -> 'b) -> term -> 'b list
    val locset_seq : thm -> local_theory -> local_theory
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

(* Clag from autocorres *)

(* Define lemmas into the local theory. *)  (* FIXME !? *)
fun define_lemmas name attrs thm_list lthy =
  let
    val ((_, thms), lthy) = Local_Theory.note ((Binding.name name, attrs), thm_list) lthy
    (*
     * Restore the theory; not entirely sure why this is needed, but prevents
     * definitions from taking O(n^2) time (where "n" is the number of
     * definitions previously made).
     *)
    val lthy' = Local_Theory.restore lthy  (* FIXME !? *)
    val thms' = map (Morphism.thm (Local_Theory.target_morphism lthy)) thms
  in
    (thms', lthy')
  end

(* Cache location set membership facts.

For each label, decide membership in the given set. We'd like an
attribute to do this (for syntactic convenience) but these get
executed multiple times. Solution: just invoke some ML to do the job.

If the label set and com types differ, we probably get a nasty error.

No need to consider locations of @{const "Response"}s; could tweak
@{text "com_locs_fold"} to reflect this.

*)

(* Sequential, possibly space-efficient. *)
fun locset_seq thm lthy =
  let
    val set_name = thm |> Thm.cprop_of |> Thm.dest_equals |> fst
    val thm_name =
      set_name |> Thm.term_of |> dest_Const |> fst
      |> Long_Name.base_name |> (fn def => def ^ "_membs")
    fun mk_memb_term lthy l =
      Thm.cterm_of lthy (@{mk_term "?x : ?S" (x, S)} (l, Thm.term_of set_name))
    fun mk_mthm lthy l thms =
      mk_memb_term lthy l
       |> Simplifier.rewrite (lthy addsimps [thm]) (* probably want the ambient simpset + some stuff *)
       |> (fn thm => thm :: thms)
    val coms = Com.get lthy |> map (Thm.cprop_of #> Thm.dest_equals #> snd #> Thm.term_of)
    val thms = List.foldl (fn (c, thms) => c |> com_locs_fold (mk_mthm lthy) thms) [] coms
  in
    lthy
    |> define_lemmas thm_name
        [Attrib.internal (K (Clasimp.iff_add)), Attrib.internal (K (Loc.add))] thms
    |> snd
  end;

(* Parallel, fast. *)
fun locset thm lthy =
  let
    val set_name = thm |> Thm.cprop_of |> Thm.dest_equals |> fst
    val thm_name =
      set_name |> Thm.term_of |> dest_Const |> fst
      |> Long_Name.base_name |> (fn def => def ^ "_membs")
    fun mk_memb_term lthy l =
      Thm.cterm_of lthy (@{mk_term "?x : ?S" (x, S)} (l, Thm.term_of set_name))
    val coms = Com.get lthy |> map (Thm.cprop_of #> Thm.dest_equals #> snd #> Thm.term_of)
    val memb_terms = maps (com_locs_map (mk_memb_term lthy)) coms
    val thms =
      Par_List.map (Simplifier.rewrite (lthy addsimps ([thm] @ Loc.get lthy))) (* probably want the ambient simpset + some stuff *)
        memb_terms
  in
    lthy
    |> define_lemmas thm_name
        [(* Attrib.internal (K (Clasimp.iff_add)), *) Attrib.internal (K (Loc.add))] thms
    |> snd
  end;

(*

Example use:

definition no_pending_phase_locs :: "location set" where
  "no_pending_phase_locs \<equiv>
       (prefixed ''idle'' - {''idle gc loop'', ''idle_noop_mfence''})
     \<union> (prefixed ''init'' - {''init_noop_mfence''})
     \<union> (prefixed ''mark'' - {''mark_read_fM'', ''mark_write_fA'', ''mark_noop_mfence''})"

local_setup {* locset @{thm "no_pending_phase_locs_def"} *}

lemma "''idle gc loop'' \<notin> no_pending_phase_locs"
by (simp add: loc)

lemma "''idle gc loop'' \<notin> no_pending_phase_locs"
by (simp add: loc)

*)

end
