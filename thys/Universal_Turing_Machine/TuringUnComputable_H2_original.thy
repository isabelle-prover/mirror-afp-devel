(* Title: thys/TuringUnComputable_H2_original.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten

   Further contributions by Franz Regensburger (FABR) 02/2022:
   * Re-ordering of sections
   * Added comments

   Editorial note FABR:
   this file was part of the theory file Uncomputable.thy
   in the original AFP entry. 
   
 *)

subsubsection \<open>Undecidability of the General Halting Problem H, Variant 2, original version\<close>

theory TuringUnComputable_H2_original
  imports
    DitherTM
    CopyTM

begin

(*
declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]
*)

(* Cleanup the global simpset for proofs of several theorems about tm_dither *)

(*
declare adjust.simps[simp del]
*)

text \<open>The diagonal argument below shows the undecidability of a variant of the
 General Halting Problem. Implicitly, we thus show that the General Halting Function
 (the characteristic function of the Halting Problem) is not Turing computable.\<close>

(*

Turing_HaltingConditions.thy:

definition TMC_has_num_res :: "tprog0 \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "TMC_has_num_res p ns \<equiv>
     \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"

DitherTM.thy:

lemma composable_tm0_tm_dither[intro, simp]: "composable_tm0 tm_dither"
  by (auto simp: composable_tm.simps tm_dither_def)

CopyTM.thy:

lemma composable_tm0_tm_copy[intro, simp]: "composable_tm0 tm_copy"
  by (auto simp: tm_copy_def)

*)

text \<open>
  The following locale specifies that some TM \<open>H\<close> can be used to decide 
  the {\em General Halting Problem} and \<open>False\<close> is going to be derived 
  under this locale. Therefore, the undecidability of the  {\em  General Halting Problem}
  is established.

  The proof makes use of the TMs \<open>tm_copy\<close> and \<open>tm_dither\<close>.
\<close>

locale uncomputable = 
  (* Interestingly, the detailed definition of the coding function @{text "code"} for Turing machines
     does not affect the final result. In the proof there is no need to appeal on properties of the coding function
     like e.g. injectivity! *)

fixes code :: "instr list \<Rightarrow> nat" 
  (* 
   * The TM "H" is the one which is assumed being able to solve the general Halting problem.
   *)
  and H :: "instr list"

  (* FABR Note:
   * The next axiom states that the Turing machine H is well-formed (composable).
   * However, this manifests a bug in the modelling of this locale!
   *
   * Due to this local axiom, we only prove that there exists no composable TM H
   * that is able to decide the Halting problem 'TMC_has_num_res M ns'
   *
   * See theories composableTMs and HaltingProblem_K for a fix by FABR.
   *
   *)

assumes h_composable[intro]: "composable_tm0 H"


  (*
   * The following two local axioms specify (claim) that the Turing Machine H
   * is able to decide the general Halting problem H2.
   *)

and h_case:
"\<And> M ns.  TMC_has_num_res M ns \<Longrightarrow> \<lbrace>(\<lambda>tap. tap = ([Bk], <(code M, ns)>))\<rbrace> H \<lbrace>(\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>))\<rbrace>"
and nh_case: 
"\<And> M ns. \<not>  TMC_has_num_res M ns \<Longrightarrow> \<lbrace>(\<lambda>tap. tap = ([Bk], <(code M, ns)>))\<rbrace> H \<lbrace>(\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>))\<rbrace>"
begin

(* Assertions for the Turing Machine H *)
abbreviation (input)
  "pre_H_ass M ns \<equiv> \<lambda>tap. tap = ([Bk], <(code M, ns::nat list)>)"

abbreviation (input)
  "post_H_halt_ass \<equiv> \<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)"

abbreviation (input)
  "post_H_unhalt_ass \<equiv> \<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)"


lemma H_halt:
  assumes "\<not>  TMC_has_num_res M ns" 
  shows "\<lbrace>pre_H_ass M ns\<rbrace> H \<lbrace>post_H_halt_ass\<rbrace>"
  using assms nh_case by auto

lemma H_unhalt:
  assumes " TMC_has_num_res M ns" 
  shows "\<lbrace>pre_H_ass M ns\<rbrace> H \<lbrace>post_H_unhalt_ass\<rbrace>"
  using assms h_case by auto

(* The TM tcontra is the culprit that is used to derive a contradiction *)

definition
  "tcontra \<equiv> (tm_copy |+| H) |+| tm_dither"
abbreviation
  "code_tcontra \<equiv> code tcontra"

(* assume tcontra does not halt on its code *)
lemma tcontra_unhalt: 
  assumes "\<not>  TMC_has_num_res tcontra [code tcontra]"
  shows "False"
proof -
  (* invariants *)
  define P1 where "P1 \<equiv> \<lambda>tap. tap = ([]::cell list, <code_tcontra>)"
  define P2 where "P2 \<equiv> \<lambda>tap. tap = ([Bk], <(code_tcontra, code_tcontra)>)"
  define P3 where "P3 \<equiv> \<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>)"

(*
  \<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>  \<lbrace>P2\<rbrace> H \<lbrace>P3\<rbrace> 
  ----------------------------
     \<lbrace>P1\<rbrace> (tm_copy |+| H) \<lbrace>P3\<rbrace>     \<lbrace>P3\<rbrace> tm_dither \<lbrace>P3\<rbrace>
  ------------------------------------------------
                 \<lbrace>P1\<rbrace> tcontra \<lbrace>P3\<rbrace>
  *)

  have H_composable: "composable_tm0 (tm_copy |+| H)" by auto

(* \<lbrace>P1\<rbrace> (tm_copy |+| H) \<lbrace>P3\<rbrace> *)
  have first: "\<lbrace>P1\<rbrace> (tm_copy |+| H) \<lbrace>P3\<rbrace>" 
  proof (cases rule: Hoare_plus_halt)
    case A_halt (* of tm_copy *)
    show "\<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>" unfolding P1_def P2_def tape_of_nat_def
      by (rule tm_copy_correct)
  next
    case B_halt (* of H *)
    show "\<lbrace>P2\<rbrace> H \<lbrace>P3\<rbrace>"
      unfolding P2_def P3_def 
      using H_halt[OF assms]
      by (simp add: tape_of_prod_def tape_of_list_def)
  qed (simp)

(* \<lbrace>P3\<rbrace> tm_dither \<lbrace>P3\<rbrace> *)
  have second: "\<lbrace>P3\<rbrace> tm_dither \<lbrace>P3\<rbrace>" unfolding P3_def 
    by (rule tm_dither_halts)

(* \<lbrace>P1\<rbrace> tcontra \<lbrace>P3\<rbrace> *)
  have "\<lbrace>P1\<rbrace> tcontra \<lbrace>P3\<rbrace>" 
    unfolding tcontra_def
    by (rule Hoare_plus_halt[OF first second H_composable])

  with assms show "False"
    unfolding P1_def P3_def
    unfolding  TMC_has_num_res_def
    unfolding Hoare_halt_def 
    apply(auto) apply(rename_tac n)
    apply(drule_tac x = n in spec)
    apply(case_tac "steps0 (Suc 0, [], <code tcontra>) tcontra n")
    apply(auto simp add: tape_of_list_def)
    by (metis append_Nil2 replicate_0)
qed

(* asumme tcontra halts on its code *)
lemma tcontra_halt: 
  assumes " TMC_has_num_res tcontra [code tcontra]"
  shows "False"
proof - 
  (* invariants *)
  define P1 where "P1 \<equiv> \<lambda>tap. tap = ([]::cell list, <code_tcontra>)"
  define P2 where "P2 \<equiv> \<lambda>tap. tap = ([Bk], <(code_tcontra, code_tcontra)>)"
  define Q3 where "Q3 \<equiv> \<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>)"

(*
  \<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>  \<lbrace>P2\<rbrace> H \<lbrace>Q3\<rbrace> 
  ----------------------------
     \<lbrace>P1\<rbrace> (tm_copy |+| H) \<lbrace>Q3\<rbrace>     \<lbrace>Q3\<rbrace> tm_dither loops
  ------------------------------------------------
               \<lbrace>P1\<rbrace> tcontra loops
  *)

  have H_composable: "composable_tm0 (tm_copy |+| H)" by auto

(* \<lbrace>P1\<rbrace> (tm_copy |+| H) \<lbrace>Q3\<rbrace> *)
  have first: "\<lbrace>P1\<rbrace> (tm_copy |+| H) \<lbrace>Q3\<rbrace>" 
  proof (cases rule: Hoare_plus_halt)
    case A_halt (* of tm_copy *)
    show "\<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>" unfolding P1_def P2_def tape_of_nat_def
      by (rule tm_copy_correct)
  next
    case B_halt (* of H *)
    then show "\<lbrace>P2\<rbrace> H \<lbrace>Q3\<rbrace>"
      unfolding P2_def Q3_def using H_unhalt[OF assms]
      by(simp add: tape_of_prod_def tape_of_list_def)
  qed (simp)

(* \<lbrace>P3\<rbrace> tm_dither loops *)
  have second: "\<lbrace>Q3\<rbrace> tm_dither \<up>" unfolding Q3_def 
    by (rule tm_dither_loops)

(* \<lbrace>P1\<rbrace> tcontra loops *)
  have "\<lbrace>P1\<rbrace> tcontra \<up>" 
    unfolding tcontra_def
    by (rule Hoare_plus_unhalt[OF first second H_composable])

  with assms show "False"
    unfolding P1_def
    unfolding  TMC_has_num_res_def
    unfolding Hoare_halt_def Hoare_unhalt_def
    by (auto simp add: tape_of_list_def)
qed

text \<open>
  Thus \<open>False\<close> is derivable.
\<close>

lemma false: "False"
  using tcontra_halt tcontra_unhalt 
  by auto

end (* locale uncomputable *)

end

