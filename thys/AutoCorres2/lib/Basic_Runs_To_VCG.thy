(*
 * Copyright (c) 2022-2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
Basic setup for
verification condition generator (VCG) for the runs_to predicate.

Includes also automation to add assumptions marked with SIMP_ASSM, LINARITH_ASSM etc to the
corresponding databases.
*)

chapter \<open>Verification Condition Generator \<open>runs_to_vcg\<close>\<close>
theory Basic_Runs_To_VCG
  imports
    Named_Rules
    "HOL-Eisbach.Eisbach_Tools"
    Tagging
begin

section \<open> Marked Assumptions \<close>

ML \<open>

structure Marked_Assumptions =
struct

structure Data = Theory_Data
(
  type T = (thm -> Proof.context -> Proof.context) Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

fun import_assm ctxt thm =
  ( case head_of (HOLogic.dest_Trueprop (Thm.prop_of thm)) of
      Const (name, _) =>
        (case Symtab.lookup (Data.get (Proof_Context.theory_of ctxt)) name of
          SOME add_thm => SOME (add_thm thm ctxt)
        | NONE => NONE)
    | _ => NONE )
  handle TERM _ => NONE

fun with_assms ctxt old_prems tac =
  Subgoal.FOCUS (fn { context = ctxt1, prems, ... } =>
    let
      val (ctxt4, prems') = (ctxt1, old_prems) |> fold (fn thm => fn (ctxt2, prems') =>
        case import_assm ctxt2 thm of
          SOME ctxt3 => (ctxt3, prems')
        | NONE => (ctxt2, thm::prems')) prems
    in
      tac ctxt4 prems'
    end) ctxt 1

fun add_marker name f = Data.map (Symtab.update (name, f))

end ;

\<close>

attribute_setup parse_ASSMs =
  \<open>Scan.succeed (Thm.declaration_attribute (fn thm => Context.map_proof (fn ctxt =>
    case Marked_Assumptions.import_assm ctxt thm of SOME ctxt => ctxt | NONE => ctxt)))\<close>

named_theorems remove_ASSMs "Remove the markers for marked assumptions"

method cleanup_ASSMs = simp_all only: remove_ASSMs

definition SIMP_ASSM :: "bool \<Rightarrow> bool" where [remove_ASSMs]: "SIMP_ASSM P \<longleftrightarrow> P"
lemma SIMP_ASSM_D: "SIMP_ASSM P \<Longrightarrow> P" by (simp add: SIMP_ASSM_def)
setup \<open> Marked_Assumptions.add_marker @{const_name SIMP_ASSM} (fn thm => fn ctxt =>
  ctxt addsimps [thm RS @{thm SIMP_ASSM_D}]) \<close>

section \<open>\<open>THEN_ALL_NEW_FORWARD\<close>\<close>

ML \<open>

fun each_protected (t : int -> tactic) : tactic =
  let
    fun work_at i st =
      if Thm.nprems_of st = i then Seq.single st
      else
        rotate_prems i st
        |> Goal.protect 1
        |> t i
        |> Seq.maps (fn st =>
            Goal.conclude st
            |> rotate_prems (~ i)
            |> work_at (i + Thm.nprems_of st) )

  in work_at 0 end

(* THEN_ALL_NEW_FORWARD m1 m2, applies first m1 and then all all new subgoals m2 is applied.

m1 THEN_ALL_NEW m2 (i.e. m1; m2) applies m2 in the reverse order. This is a problem when schematic
variables need to be resolved *)

fun THEN_ALL_NEW_FORWARD' (t1 : tactic) (t2 : int -> tactic) (st : thm) =
  Goal.protect 1 st
  |> t1
  |> Seq.maps (each_protected t2)
  |> Seq.map Goal.conclude

fun THEN_ALL_NEW_FORWARD (t1 : tactic) (t2 : tactic) =
  THEN_ALL_NEW_FORWARD' t1 (K t2)

\<close>

method_setup all_new = \<open>
(Method.text_closure -- Method.text_closure) >> (fn (m1, m2) => fn ctxt => fn facts =>
  let
    val tac1 = method_evaluate m1 ctxt facts
    val tac2 = method_evaluate m2 ctxt facts
  in Method.RUNTIME (SIMPLE_METHOD (THEN_ALL_NEW_FORWARD tac1 tac2) facts) end)
\<close>

section \<open>Basic VCG\<close>

named_theorems runs_to_vcg_cong_state_only
named_theorems runs_to_vcg_weaken
named_theorems runs_to_vcg_cong_program_only
named_rules (intro) runs_to_vcg

named_theorems runs_to_vcg_post_elims
named_theorems runs_to_vcg_post_intros

declare conjI[runs_to_vcg_post_intros]
declare disjE[runs_to_vcg_post_elims]

ML \<open>
signature RUNS_TO_VCG =
sig
  val apply_runs_to:
     (Proof.context -> int -> tactic) option ->
       (Proof.context -> (unit -> string) -> tactic) ->
         term -> Proof.context -> tactic
  val prepare:
     {do_nosplit: bool, no_unsafe_hyp_subst: bool} -> Proof.context -> tactic
  val runs_to_vcg_tac:
     (Proof.context -> int -> tactic) option ->
       int -> (Proof.context -> (unit -> string) -> tactic) ->
           {do_nosplit: bool, no_unsafe_hyp_subst: bool} ->
             (Proof.context -> tactic) -> Proof.context -> tactic
  val split_paired_all: Proof.context -> int -> tactic
  val trace_tac: 'a -> (unit -> string) -> 'b -> 'b Seq.seq
  val no_trace_tac: Proof.context -> (unit -> string) -> tactic
  val trace_print_tac: Proof.context -> (unit -> string) -> thm -> thm Seq.seq
end

structure Runs_To_VCG : RUNS_TO_VCG =
struct

(*Print the current proof state and pass it on.*)
fun trace_tac _ msg st = (tracing (msg ()); Seq.single st);
fun trace_print_tac ctxt msg st = print_tac ctxt (msg ()) st;
val no_trace_tac = K (K (all_tac)):  Proof.context -> (unit -> string) -> tactic

fun split_paired_all ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms split_paired_all})

fun prepare {do_nosplit, no_unsafe_hyp_subst} ctxt =
let
  val post_intros = Named_Theorems.get ctxt @{named_theorems runs_to_vcg_post_intros}
  val post_elims = Named_Theorems.get ctxt @{named_theorems runs_to_vcg_post_elims}
in
  REPEAT_DETERM_FIRST (fn n =>
    CHANGED (split_paired_all ctxt n)
    ORELSE
    CHANGED (eresolve_tac ctxt @{thms exE bexE conjE} n)
    ORELSE
    CHANGED (resolve_tac ctxt @{thms allI ballI impI} n)
    ORELSE
    CHANGED (full_simp_tac
      ((fold Simplifier.add_cong
        (Named_Theorems.get ctxt @{named_theorems runs_to_vcg_cong_state_only}) ctxt)) n)
    ORELSE
    (if no_unsafe_hyp_subst
      then CHANGED (asm_full_simp_tac (put_simpset HOL_basic_ss ctxt) n)
      else CHANGED (bound_hyp_subst_tac ctxt n))
    ORELSE
    (if do_nosplit then no_tac else CHANGED (eresolve_tac ctxt post_elims n))
    ORELSE
    CHANGED (resolve_tac ctxt post_intros n))
  ORELSE
  all_tac
end

local
fun parse_program1 ctxt g cong_program_thm =
  let
    fun lhs t = t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> #1
    val pat = Thm.concl_of cong_program_thm |> lhs
    val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl g)
    val (key, _) = case Thm.prems_of cong_program_thm of [prem] =>
          lhs prem |> Term.dest_Var 
      | _ => error "Runs_To_VCG parse_program: wrong format of rule"
  in
    case Unify.unifiers (Context.Proof ctxt, Envir.init, [(pat, concl)]) |> Seq.pull
    of SOME ((env,_), _) =>
      (case Vartab.lookup (Envir.term_env env) key of NONE => NONE
          | SOME (_, t) => SOME t)
    | NONE => NONE
  end
in
fun parse_program ctxt t = get_first (parse_program1 ctxt t)
  (Named_Theorems.get ctxt @{named_theorems runs_to_vcg_cong_program_only})
end

fun with_rules tac ctxt = 
  let
    fun tac' ctxt thms i = tac ctxt thms
  in
    Named_Rules.with_rules @{named_rules runs_to_vcg} tac' ctxt 1
  end 

fun apply_runs_to splitter_opt trace prg = with_rules (fn ctxt => fn rules => 
  let
    val n = length rules
    fun t i thm msg () =
      let
        val d = Thm_Name.print (Thm.derivation_name thm)
      in
        "At " ^ Syntax.string_of_term ctxt (head_of prg) ^ " apply " ^ msg ^ ": " ^
          space_implode " " [d, "(" ^ string_of_int (i + 1) ^ " of " ^ string_of_int n ^ ")"] 
     end
    fun MAP f = FIRST (map_index f rules)
  in
    TRY (DETERM (
      MAP (fn (i, thm) => resolve_tac ctxt [thm] 1 THEN trace ctxt (t i thm "rule"))
      ORELSE (case splitter_opt of 
          SOME splitter => 
            trace ctxt (fn () => "Trying splitter on " ^ Syntax.string_of_term ctxt prg) THEN 
            splitter ctxt 1
          | _ => no_tac)
      ORELSE
      MAP (fn (i, thm) =>
        resolve_tac ctxt
          (Named_Theorems.get ctxt @{named_theorems Basic_Runs_To_VCG.runs_to_vcg_weaken}) 1 THEN
        resolve_tac ctxt [thm] 1 THEN
        trace ctxt (t i thm "weakened rule"))))
  end)

fun runs_to_vcg_tac splitter_opt n trace options solver ctxt =
let
  fun flat_trace f () = "  " ^ f ()
  fun runs_to_vcg_loop n trace ctxt prems =
    if n = 0 then all_tac else
    SUBGOAL (fn (g, _) =>
      case parse_program ctxt g of
        SOME prg => 
          THEN_ALL_NEW_FORWARD
            (CHANGED (apply_runs_to splitter_opt trace prg ctxt))
            (THEN_ALL_NEW_FORWARD
              (prepare options ctxt)
              (Marked_Assumptions.with_assms ctxt prems
                (runs_to_vcg_loop (n - 1) (fn ctxt => fn f => trace ctxt (flat_trace f)))))
          ORELSE trace ctxt (fn () => "No rule applicable for " ^ Syntax.string_of_term ctxt prg)
      | NONE =>
        TRY (SOLVED' (Method.insert_tac ctxt prems THEN'
          (K (solver ctxt) ORELSE' assume_tac ctxt)) 1))
      1
in
  runs_to_vcg_loop n trace ctxt []
end

end
\<close>

method_setup runs_to_vcg =
\<open> (Scan.lift (Args.mode "trace") --
    Scan.lift (Args.mode "nosplit") --
    Scan.lift (Args.mode "no_unsafe_hyp_subst") --
    Scan.optional (Scan.lift (Args.parens Parse.nat)) (~1) --
    Scan.option Method.text_closure) >>
    (fn ((((do_trace, do_nosplit), do_no_unsafe_hyp_subst), n), text) => fn ctxt =>
      let val tac = (case text of
          NONE => (fn _ => no_tac)
        | SOME txt => fn ctxt => NO_CONTEXT_TACTIC ctxt (Method.evaluate txt ctxt []))
      in SIMPLE_METHOD (Runs_To_VCG.runs_to_vcg_tac NONE n
        (if do_trace then Runs_To_VCG.trace_tac else Runs_To_VCG.no_trace_tac)
        {do_nosplit=do_nosplit, no_unsafe_hyp_subst=do_no_unsafe_hyp_subst}
        tac ctxt) end) \<close>

section \<open>Setup for Tagging\<close>

lemma push_tag_to_assm:
  "t \<bar> P" if "\<paragraph> t \<Longrightarrow> P"
  using that unfolding ASM_TAG_def TAG_def by simp

lemma tagE:
  "tag \<bar> Q \<Longrightarrow> (Q \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: TAG_def)

bundle basic_vcg_tagging_setup
begin

lemmas [runs_to_vcg_post_intros] = push_tag_to_assm TAG_TrueI ASM_TAG_I
lemmas [runs_to_vcg_post_elims]  = tagE

end

end