(* Title: thys/HaltingProblems_K_H.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

subsection \<open>Undecidability of Halting Problems\<close>

theory HaltingProblems_K_H
  imports
    SimpleGoedelEncoding
    SemiIdTM
    TuringReducible

begin

(* -------------------------------------------------------------------------- *)

(*
declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]
*)

subsubsection \<open>A locale for variations of the Halting Problem\<close>

text \<open>
  The following locale assumes that there is an injective coding function \<open>t2c\<close>
  from Turing machines to natural numbers. In this locale, we will show that the
  Special Halting Problem K1 and the General Halting Problem H1 are not Turing decidable.
\<close>

locale hpk = 
  fixes t2c :: "tprog0 \<Rightarrow> nat"
  assumes
    t2c_inj: "inj t2c"

begin

text \<open>The function @{term tm_to_nat} is a witness that the locale hpk is inhabited.\<close>

interpretation tm_to_nat: hpk "tm_to_nat :: tprog0 \<Rightarrow> nat"
proof unfold_locales
  show "inj tm_to_nat" by (rule inj_tm_to_nat)
qed

text \<open>We define the function @{term c2t} as the unique inverse of the
injective function  @{term t2c}.
\<close>

(* Note 1:
 * It does not matter how we define c2t n if \<not>(\<exists>p. t2c p = n).
 * We never need to know that value
 * since we are only interested in the equation
 *
 *   "c2t (t2c p) = p"
 *)

(* Note 1:
   * We use Hilbert' non-constructive operators for
   *   definite   choice \<iota> (iota)     (THE in  Isabelle/HOL)
   *   indefinite choice \<epsilon> (epsilon)  (SOME in Isabelle/HOL)
   *)

definition c2t :: "nat \<Rightarrow> instr list"
  where
    "c2t = (\<lambda>n. if (\<exists>p. t2c p = n)
                 then (THE  p. t2c p = n)
                 else (SOME p. True) )"

lemma t2c_inj': "inj_on t2c {x. True}"
  by (auto simp add: t2c_inj )

lemma c2t_comp_t2c_eq: "c2t (t2c p) = p"
proof -
  have "\<forall>p\<in>{x. True}. c2t (t2c p) = p"
  proof (rule encode_decode_A_eq[OF t2c_inj'])
    show "c2t = (\<lambda>w. if \<exists>t\<in>{x. True}. t2c t = w then THE t. t \<in> {x. True} \<and> t2c t = w else SOME t. t \<in> {x. True})"
      by (auto simp add: c2t_def)
  qed
  then show ?thesis by auto
qed

subsubsection \<open>Undecidability of the Special Halting Problem K1\<close>

(* Just as a reminder:

    definition TMC_has_num_res :: "tprog0 \<Rightarrow> nat list \<Rightarrow> bool"

      where
        "TMC_has_num_res p ns \<equiv>
         \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"


    lemma TMC_yields_num_res_unfolded_into_Hoare_halt:

      "TMC_yields_num_res tm ns n \<equiv>
         \<lbrace>(\<lambda>tap. tap = ([], <ns>))\<rbrace> tm \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk\<up> l))\<rbrace>"

*)

definition K1 :: "(nat list) set"
  where
     "K1 \<equiv> {nl. (\<exists>n. nl = [n] \<and> TMC_has_num_res (c2t n) [n]) }"

text \<open>Assuming the existence of a Turing Machine K1D1, which is able to decide the set K1,
 we derive a contradiction using the machine @{term "tm_semi_id_eq0"}.
 Thus, we show that the {\em Special Halting Problem K1} is not Turing decidable.
\label{sec_K1_H1}
 The proof uses a diagonal argument.
\<close>

(* some convenience lemmas will keep the main proof quit neat *)

lemma mk_composable_decider_K1D1:
  assumes "\<exists>K1D1'. (\<forall>nl.
          (nl \<in> K1 \<longrightarrow>TMC_yields_num_res K1D1' nl (1::nat))
       \<and>  (nl \<notin> K1 \<longrightarrow>TMC_yields_num_res K1D1' nl (0::nat) ))"

  shows  "\<exists>K1D1'. (\<forall>nl. composable_tm0 K1D1' \<and>
          (nl \<in> K1 \<longrightarrow>TMC_yields_num_res K1D1' nl (1::nat))
       \<and>  (nl \<notin> K1 \<longrightarrow>TMC_yields_num_res K1D1' nl (0::nat) ))"
proof -
  from assms have
    "\<exists>K1D1'. (\<forall>nl.
          (nl \<in> K1 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc,Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K1 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>) )"
    unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
    by (simp add: tape_of_nat_def)

    (* create a composable version of the potentially non-composable machine K1D1' *)

  then obtain K1D1' where
    "(\<forall>nl.
          (nl \<in> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  then have "composable_tm0 (mk_composable0 K1D1') \<and> (\<forall>nl.
          (nl \<in> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K1D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K1D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>))"
    using Hoare_halt_tm_impl_Hoare_halt_mk_composable0 composable_tm0_mk_composable0 by blast 

  then have "composable_tm0 (mk_composable0 K1D1') \<and> (\<forall>nl.
          (nl \<in> K1 \<longrightarrow> TMC_yields_num_res (mk_composable0 K1D1') nl (1::nat) )
       \<and>  (nl \<notin> K1 \<longrightarrow> TMC_yields_num_res (mk_composable0 K1D1') nl (0::nat) ))"
    unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
    by (simp add: tape_of_nat_def)

  then show ?thesis by auto
qed

lemma res_1_fed_into_tm_semi_id_eq0_loops:
  assumes "composable_tm0 D"
    and   "TMC_yields_num_res D nl (1::nat)"
  shows   "TMC_loops (D |+| tm_semi_id_eq0) nl"
  unfolding TMC_loops_def
proof 
  fix stp
  show "\<not> is_final (steps0 (1, [], <nl::nat list>) (D |+| tm_semi_id_eq0) stp)"
    using assms tm_semi_id_eq0_loops''        
      Hoare_plus_unhalt Hoare_unhalt_def 
      tape_of_nat_def tape_of_list_def
      TMC_yields_num_res_unfolded_into_Hoare_halt
    by simp
qed

lemma loops_imp_has_no_res: "TMC_loops tm [n] \<Longrightarrow> \<not> TMC_has_num_res tm [n]"
proof -
  assume "TMC_loops tm [n]"
  then show "\<not> TMC_has_num_res tm [n]"
    using TMC_has_num_res_iff TMC_loops_def
    by blast
qed

lemma yields_res_imp_has_res: "TMC_yields_num_res tm [n] (m::nat) \<Longrightarrow> TMC_has_num_res tm [n]"
proof -
  assume "TMC_yields_num_res tm [n] (m::nat)"
  then show "TMC_has_num_res tm [n]"
    by (metis TMC_has_num_res_iff TMC_yields_num_res_def is_finalI)
qed

lemma res_0_fed_into_tm_semi_id_eq0_yields_0:
  assumes "composable_tm0 D"
    and   "TMC_yields_num_res D nl (0::nat)"
  shows   "TMC_yields_num_res (D |+| tm_semi_id_eq0) nl 0"
  unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
  using assms Hoare_plus_halt tm_semi_id_eq0_halts''
    tape_of_nat_def tape_of_list_def
    TMC_yields_num_res_unfolded_into_Hoare_halt
  by simp
  
(* here is the main lemma about the Halting problem K1 *)

lemma existence_of_decider_K1D1_for_K1_imp_False:
  assumes major: "\<exists>K1D1'. (\<forall>nl.
            (nl \<in> K1 \<longrightarrow>TMC_yields_num_res K1D1' nl (1::nat))
         \<and>  (nl \<notin> K1 \<longrightarrow>TMC_yields_num_res K1D1' nl (0::nat) ))"
  shows False
proof -
  (* first, create a composable version of the potentially non-composable machine K1D1' *)

  from major have
    "\<exists>K1D1'. (\<forall>nl. composable_tm0 K1D1' \<and>
            (nl \<in> K1 \<longrightarrow> TMC_yields_num_res K1D1' nl (1::nat))
         \<and>  (nl \<notin> K1 \<longrightarrow> TMC_yields_num_res K1D1' nl (0::nat) ))"
    by (rule mk_composable_decider_K1D1)

  then obtain K1D1 where
    w_K1D1: "\<forall>nl. composable_tm0 K1D1 \<and>
            (nl \<in> K1 \<longrightarrow> TMC_yields_num_res K1D1 nl (1::nat))
         \<and>  (nl \<notin> K1 \<longrightarrow> TMC_yields_num_res K1D1 nl (0::nat) )"
    by blast

  (* second, using our composable decider K1D1 we construct a machine tm_contra that will
     contradict our major assumption using a diagonal argument *)

  define tm_contra where "tm_contra = K1D1 |+| tm_semi_id_eq0"

  (* third, we derive the crucial lemma "c2t (t2c tm_contra) = tm_contra" *)
  have c2t_comp_t2c_eq_for_tm_contra: "c2t (t2c tm_contra) = tm_contra"
    by (auto simp add: c2t_comp_t2c_eq)

  (* now, we derive the contradiction *)
  show False
    (* using the classical axiom TND: A \<or> \<not>A,
   * we proof by cases: [t2c tm_contra] \<in> K1 \<or> [t2c tm_contra] \<notin> K1 *)

  proof (cases "[t2c tm_contra] \<in> K1")
    case True
    from \<open>[t2c tm_contra] \<in> K1\<close> and w_K1D1
    have "TMC_yields_num_res K1D1 [t2c tm_contra] (1::nat)"
      by auto

    then have "TMC_loops tm_contra [t2c tm_contra]"
      using res_1_fed_into_tm_semi_id_eq0_loops w_K1D1 tm_contra_def
      by blast

    then have "\<not>(TMC_has_num_res tm_contra [t2c tm_contra])"
      using loops_imp_has_no_res by blast

    then have "\<not>(TMC_has_num_res (c2t (t2c tm_contra))) [t2c tm_contra]"
      by (auto simp add: c2t_comp_t2c_eq_for_tm_contra)

    then have "[t2c tm_contra] \<notin> K1"
      by (auto simp add: K1_def)

    with  \<open>[t2c tm_contra] \<in> K1\<close> show False by auto

  next
    case False
    from \<open>[t2c tm_contra] \<notin> K1\<close> and w_K1D1
    have "TMC_yields_num_res K1D1 [t2c tm_contra] (0::nat)"
      by auto

    then have "TMC_yields_num_res tm_contra [t2c tm_contra] (0::nat)"
      using res_0_fed_into_tm_semi_id_eq0_yields_0 w_K1D1 tm_contra_def
      by auto

    then have "TMC_has_num_res tm_contra [t2c tm_contra]"
      using yields_res_imp_has_res by blast

    then have "TMC_has_num_res (c2t (t2c tm_contra)) [t2c tm_contra]"
      by (auto simp add: c2t_comp_t2c_eq_for_tm_contra)

    then have "[t2c tm_contra] \<in> K1"
      by (auto simp add: K1_def)

    with \<open>[t2c tm_contra] \<notin> K1\<close> show False by auto
  qed
qed

(* FABR NOTE:
 
   We are not able to show a result like "\<not>(turing_decidable H2)"
   
   Reason:
   Our notion of Turing decidability is based on: turing_decidable :: "(nat list) set \<Rightarrow> bool"

   The lemma of theory TuringUnComputable_H2

      lemma existence_of_decider_H2D0_for_H2_imp_False:
        assumes "\<exists>H2D0'. (\<forall>nl (tm::instr list).
                ((tm,nl) \<in> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk\<up>l)\<rbrace>)
             \<and>  ((tm,nl) \<notin> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>) )"
        shows False

   is about pairs (tm,nl) :: ((instr list) \<times> (nat list)) set

    definition H2 :: "((instr list) \<times> (nat list)) set"
      where
         "H2 \<equiv> {(tm,nl). TMC_has_num_res tm nl }"

   We need to derive a variation of this result
   where we use a set of lists [code tm, nl] :: (nat list) set
   that fits into our setting.

    definition H1 :: "(nat list) set"
      where
         "H1 \<equiv> {nl. (\<exists>n m. nl = [n,m] \<and> TMC_has_num_res (c2t n) [m]) }"

*)

subsubsection \<open>The Special Halting Problem K1 is reducible to the General Halting Problem H1\<close>

text \<open>The proof is  by reduction of \<open>K1\<close> to \<open>H1\<close>.
\<close>

(* Convenience lemmas for the reduction of K1 to H1 *)

definition H1 :: "(nat list) set"
  where
    "H1 \<equiv> {nl. (\<exists>n m. nl = [n,m] \<and> TMC_has_num_res (c2t n) [m]) }"

lemma NilNotIn_K1: "[] \<notin> K1"
  unfolding K1_def
  using CollectD list.simps(3) by auto

lemma NilNotIn_H1: "[] \<notin> H1"
  unfolding H1_def
  using CollectD list.simps(3) by auto

lemma tm_strong_copy_total_correctness_Nil':
  "length nl = 0 \<Longrightarrow> TMC_yields_num_list_res tm_strong_copy nl []"
  unfolding TMC_yields_num_list_res_unfolded_into_Hoare_halt
proof -
  assume "length nl = 0"
  then have "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace> tm_strong_copy \<lbrace>\<lambda>tap. tap = ([Bk,Bk,Bk,Bk],[]) \<rbrace>"
    using tm_strong_copy_total_correctness_Nil by simp
  then have F1: "\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm_strong_copy \<lbrace>\<lambda>tap. tap = (Bk \<up> 4, <[]> @ Bk \<up> 0)\<rbrace>"
    by (metis One_nat_def Suc_1 \<open>length nl = 0\<close>
        append_Nil length_0_conv numeral_4_eq_4 numeral_eqs_upto_12(2)
        replicate_0 replicate_Suc tape_of_list_empty)
  show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace>
              tm_strong_copy
            \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[]::nat list> @ Bk \<up> l)\<rbrace>"
  proof (rule Hoare_haltI)
    fix l::"cell list"
    fix r::"cell list"
    assume "(l, r) = ([], <nl::nat list>)"
    show "\<exists>n. is_final (steps0 (1, l, r) tm_strong_copy n) \<and>
                 (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[]::nat list> @ Bk \<up> l)) holds_for steps0 (1, l, r) tm_strong_copy n"
      by (smt F1 Hoare_haltE \<open>(l, r) = ([], <nl>)\<close> holds_for.elims(2) holds_for.simps)
  qed
qed

lemma tm_strong_copy_total_correctness_len_eq_1':
  "length nl = 1 \<Longrightarrow> TMC_yields_num_list_res tm_strong_copy nl [hd nl, hd nl]"
  unfolding TMC_yields_num_list_res_unfolded_into_Hoare_halt
proof -
  assume "length nl = 1"
  then show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
                     tm_strong_copy
                   \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd nl, hd nl]> @ Bk \<up> l) \<rbrace>"
    using tm_strong_copy_total_correctness_len_eq_1 by simp
qed

lemma tm_strong_copy_total_correctness_len_gt_1':
  "1 < length nl \<Longrightarrow> TMC_yields_num_list_res tm_strong_copy nl [hd nl]"
  unfolding TMC_yields_num_list_res_unfolded_into_Hoare_halt
proof -
  assume "1 < length nl"
  then have "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
                     tm_strong_copy
                   \<lbrace> \<lambda>tap. \<exists>l. tap = ([Bk,Bk], <[hd nl]> @ Bk \<up> l) \<rbrace>"
    using tm_strong_copy_total_correctness_len_gt_1 by simp
  then show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>) \<rbrace>
                     tm_strong_copy
                   \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <[hd nl]> @ Bk \<up> l) \<rbrace>"
    by (smt Hoare_haltE Hoare_haltI One_nat_def Pair_inject Pair_inject holds_for.elims(2)
        holds_for.simps is_final.elims(2) replicate.simps(1) replicate.simps(2))
qed

(* --- *)

theorem turing_reducible_K1_H1: "turing_reducible K1 H1"
  unfolding turing_reducible_unfolded_into_TMC_yields_condition
proof -
  have "\<forall>nl::nat list. \<exists>ml::nat list.
              TMC_yields_num_list_res tm_strong_copy nl ml \<and> (nl \<in> K1 \<longleftrightarrow> ml \<in> H1)"
  proof
    fix nl::"nat list"
    have "length nl = 0 \<or> length nl = 1 \<or> 1 < length nl"
      by arith
    then
    show "\<exists>ml. TMC_yields_num_list_res tm_strong_copy nl ml \<and> (nl \<in> K1) = (ml \<in> H1)"
    proof
      assume "length nl = 0"
      then have "TMC_yields_num_list_res tm_strong_copy nl []"
        by (rule tm_strong_copy_total_correctness_Nil')
      moreover have "(nl \<in> K1) = ([] \<in> H1)"
        using NilNotIn_H1 NilNotIn_K1 \<open>length nl = 0\<close> length_0_conv by blast
      ultimately
      show "\<exists>ml. TMC_yields_num_list_res tm_strong_copy nl ml \<and> (nl \<in> K1) = (ml \<in> H1)" by blast
    next
      assume "length nl = 1 \<or> 1 < length nl"
      then show "\<exists>ml. TMC_yields_num_list_res tm_strong_copy nl ml \<and> (nl \<in> K1) = (ml \<in> H1)"
      proof
        assume "1 < length nl"
        then have "TMC_yields_num_list_res tm_strong_copy nl [hd nl]"
          by (rule tm_strong_copy_total_correctness_len_gt_1')
        moreover have "(nl \<in> K1) = ([hd nl] \<in> H1)"
          using H1_def K1_def \<open>1 < length nl\<close> by auto
        ultimately
        show "\<exists>ml. TMC_yields_num_list_res tm_strong_copy nl ml \<and> (nl \<in> K1) = (ml \<in> H1)" by blast
      next
        assume "length nl = 1"
        then have "TMC_yields_num_list_res tm_strong_copy nl [hd nl, hd nl]"
          by (rule tm_strong_copy_total_correctness_len_eq_1')
        moreover have "(nl \<in> K1) = ([hd nl, hd nl] \<in> H1)"
          by (smt CollectD Cons_eq_append_conv H1_def K1_def One_nat_def \<open>length nl = 1\<close>
              append_Cons diff_Suc_1 hd_Cons_tl length_0_conv length_tl list.inject
              mem_Collect_eq not_Cons_self2  self_append_conv2 zero_neq_one)
        ultimately
        show "\<exists>ml. TMC_yields_num_list_res tm_strong_copy nl ml \<and> (nl \<in> K1) = (ml \<in> H1)" by blast
      qed
    qed
  qed
  then show "\<exists>tm. \<forall>nl. \<exists>ml. TMC_yields_num_list_res tm nl ml \<and> (nl \<in> K1) = (ml \<in> H1)"
    by auto
qed

(* --------------------------------------------------------------------------------------------- *)

subsubsection \<open>Corollaries about the undecidable sets K1 and H1\<close>

corollary not_Turing_decidable_K1: "\<not>(turing_decidable K1)"
proof
  assume "turing_decidable K1"
  then have "(\<exists>D. (\<forall>nl.
            (nl \<in> K1 \<longrightarrow>TMC_yields_num_res D nl (1::nat))
         \<and>  (nl \<notin> K1 \<longrightarrow>TMC_yields_num_res D nl (0::nat) )))"
    by (auto simp add: turing_decidable_unfolded_into_TMC_yields_conditions
        tape_of_nat_def)
  with existence_of_decider_K1D1_for_K1_imp_False show False
    by blast
qed

corollary not_Turing_decidable_H1: "\<not>turing_decidable H1"
proof (rule turing_reducible_AB_and_non_decA_imp_non_decB)
  show "turing_reducible K1 H1"
    by (rule turing_reducible_K1_H1)
next
  show "\<not> turing_decidable K1"
    by (rule not_Turing_decidable_K1)
qed

(* --------------------------------------------------------------------------------------------- *)

subsubsection \<open>Proof variant: The special Halting Problem K1 is not Turing Decidable\<close>

text\<open>Assuming the existence of a Turing Machine K1D0, which is able to decide the set K1,
 we derive a contradiction using the machine @{term "tm_semi_id_gt0"}.
 Thus, we show that the {\em Special Halting Problem K1} is not Turing decidable.
 The proof uses a diagonal argument.
\label{sec_K1_v}\<close>

lemma existence_of_decider_K1D0_for_K1_imp_False:
  assumes "\<exists>K1D0'. (\<forall>nl.
          (nl \<in> K1 \<longrightarrow>TMC_yields_num_res K1D0' nl (0::nat))
       \<and>  (nl \<notin> K1 \<longrightarrow>TMC_yields_num_res K1D0' nl (1::nat) ))"
  shows False
proof -
  from assms have
    "\<exists>K1D0'. (\<forall>nl.
          (nl \<in> K1 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K1 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>) )"
    unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
    by (simp add: tape_of_nat_def)
  then obtain K1D0' where
    "(\<forall>nl.
          (nl \<in> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  (* first, create a composable version of the potentially non-composable machine K1D0' *)

  then have "composable_tm0 (mk_composable0 K1D0') \<and> (\<forall>nl.
          (nl \<in> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K1D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>) 
       \<and>  (nl \<notin> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K1D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>))"
    using Hoare_halt_tm_impl_Hoare_halt_mk_composable0 composable_tm0_mk_composable0 by blast

  then have "\<exists>K1D0. composable_tm0 K1D0 \<and> (\<forall>nl.
          (nl \<in> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  then obtain K1D0 where w_K1D0: "composable_tm0 K1D0 \<and> (\<forall>nl.
          (nl \<in> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K1 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K1D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  define tm_contra where "tm_contra = K1D0 |+| tm_semi_id_gt0"

  (* second, we derive some theorems from our assumptions *)
  then have c2t_comp_t2c_TM_eq_for_tm_contra: "c2t (t2c tm_contra) = tm_contra"
    by (auto simp add: c2t_comp_t2c_eq)

  (* now, we derive the contradiction *)
  show False 
  proof (cases "[t2c tm_contra] \<in> K1")
    case True
    from \<open>[t2c tm_contra] \<in> K1\<close> and w_K1D0 have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> K1D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>"
      by auto

    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> tm_contra \<up>"
      unfolding tm_contra_def
    proof (rule Hoare_plus_unhalt)
      show "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace> tm_semi_id_gt0 \<up>"
        by (rule tm_semi_id_gt0_loops'')
    next
      from w_K1D0 show "composable_tm0 K1D0" by auto
    qed

    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> c2t (t2c tm_contra) \<up>"
      by (auto simp add: c2t_comp_t2c_TM_eq_for_tm_contra)

    then have "\<not>\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> c2t (t2c tm_contra) \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"   
      using Hoare_halt_impl_not_Hoare_unhalt by blast

    then have "\<not>( TMC_has_num_res (c2t (t2c tm_contra)) [t2c tm_contra])"
      by (auto simp add:  TMC_has_num_res_def)

    then have "[t2c tm_contra] \<notin> K1"
      by (auto simp add: K1_def)

    with  \<open>[t2c tm_contra] \<in> K1\<close> show False by auto
  next
    case False
    from \<open>[t2c tm_contra] \<notin> K1\<close> and w_K1D0 have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> K1D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
      by auto

    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> tm_contra \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
      unfolding tm_contra_def
    proof (rule Hoare_plus_halt)
      show "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace> tm_semi_id_gt0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
        by (rule  tm_semi_id_gt0_halts'')
    next
      from w_K1D0 show "composable_tm0 K1D0" by auto
    qed

    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> c2t (t2c tm_contra) \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
      by (auto simp add: c2t_comp_t2c_TM_eq_for_tm_contra)

    then have
      " TMC_has_num_res (c2t (t2c tm_contra)) [t2c tm_contra]"
      
      by (auto simp add: Hoare_halt_with_OcOc_imp_std_tap tape_of_nat_def)

    then have "[t2c tm_contra] \<in> K1"
      by (auto simp add: K1_def)

    with \<open>[t2c tm_contra] \<notin> K1\<close> show False by auto
  qed
qed

end (* locale hpk *)

end
