(* Title: thys/HaltingProblem_K_aux.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

subsubsection \<open>K0: A Variant of the Special Halting Problem K1\<close>

theory HaltingProblems_K_aux
  imports
    HaltingProblems_K_H

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

context hpk
begin

definition K0 :: "(nat list) set"
  where
     "K0 \<equiv> {nl. (\<exists>n. nl = [n] \<and> reaches_final (c2t n) [n]) }"


text\<open>Assuming the existence of a Turing Machine K0D0, which is able to decide the set K0,
 we derive a contradiction using the machine @{term "tm_semi_id_gt0"}.
 Thus, we show that the {\em Special Halting Problem K0} is not Turing decidable.
 The proof uses a diagonal argument.
\<close>

lemma existence_of_decider_K0D0_for_K0_imp_False:
  assumes "\<exists>K0D0'. (\<forall>nl.
          (nl \<in> K0 \<longrightarrow>TMC_yields_num_res K0D0' nl (0::nat))
       \<and>  (nl \<notin> K0 \<longrightarrow>TMC_yields_num_res K0D0' nl (1::nat) ))"
  shows False
proof -
  from assms have
    "\<exists>K0D0'. (\<forall>nl.
          (nl \<in> K0 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>) )"
    unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
    by (simp add: tape_of_nat_def)
  then obtain K0D0' where
    "(\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>) )"
    by blast

(* first, create a composable version of the potentially non-composable machine K0D0' *)

  then have "composable_tm0 (mk_composable0 K0D0') \<and> (\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K0D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K0D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>))"
    using Hoare_halt_tm_impl_Hoare_halt_mk_composable0 composable_tm0_mk_composable0 by blast

  then have "\<exists>K0D0. composable_tm0 K0D0 \<and> (\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  then obtain K0D0 where w_K0D0: "composable_tm0 K0D0 \<and> (\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  define tm_contra where "tm_contra = K0D0 |+| tm_semi_id_gt0"

(* second, we derive some theorems from our assumptions *)
  have c2t_comp_t2c_TM_eq_for_tm_contra: "c2t (t2c tm_contra) = tm_contra"
    by (auto simp add: c2t_comp_t2c_eq)

(* now, we derive the contradiction *)
  show False 
  proof (cases "[t2c tm_contra] \<in> K0")
    case True
    from \<open>[t2c tm_contra] \<in> K0\<close> and w_K0D0 have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> K0D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>"
      by auto

    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> tm_contra \<up>"
      unfolding tm_contra_def

    proof (rule Hoare_plus_unhalt)
      from tm_semi_id_gt0_loops' show "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace> tm_semi_id_gt0 \<up>"
        using Hoare_unhalt_add_Bks_left_tape_L1 Hoare_unhalt_def assms
        by auto
    next
      from w_K0D0 show "composable_tm0 K0D0" by auto
    qed
    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> c2t (t2c tm_contra) \<up>"
      by (auto simp add: c2t_comp_t2c_TM_eq_for_tm_contra)

    then have "\<not>(reaches_final (c2t (t2c tm_contra)) [t2c tm_contra])"
      by (simp add: Hoare_unhalt_def Hoare_unhalt_impl_not_reaches_final)

    then have "[t2c tm_contra] \<notin> K0"
      by (auto simp add: K0_def)

    with  \<open>[t2c tm_contra] \<in> K0\<close> show False by auto
  next  

    case False
    from \<open>[t2c tm_contra] \<notin> K0\<close> and w_K0D0 have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> K0D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
      by auto
    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> tm_contra \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
      unfolding tm_contra_def

    proof (rule Hoare_plus_halt)
      from tm_semi_id_gt0_halts''
      show "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace> tm_semi_id_gt0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
        by auto
    next
      from w_K0D0 show "composable_tm0 K0D0" by auto
    qed

    then have
      "\<lbrace>\<lambda>tap. tap = ([], <[t2c tm_contra]>)\<rbrace> c2t (t2c tm_contra) \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
      by (auto simp add: c2t_comp_t2c_TM_eq_for_tm_contra)

    then have
      "reaches_final (c2t (t2c tm_contra)) [t2c tm_contra]"
      by (metis (mono_tags, lifting) Hoare_haltE reaches_final_iff)

    then have "[t2c tm_contra] \<in> K0"
      by (auto simp add: K0_def)

    with \<open>[t2c tm_contra] \<notin> K0\<close> show False by auto
  qed
qed

text\<open>Assuming the existence of a Turing Machine K0D1, which is able to decide the set K0,
 we derive a contradiction using the machine @{term "tm_semi_id_eq0"}.
 Thus, we show that the {\em Special Halting Problem K0} is not Turing decidable.
 The proof uses a diagonal argument.
\<close>

lemma existence_of_decider_K0D1_for_K0_imp_False:
  assumes "\<exists>K0D1'. (\<forall>nl.
          (nl \<in> K0 \<longrightarrow>TMC_yields_num_res K0D1' nl (1::nat))
       \<and>  (nl \<notin> K0 \<longrightarrow>TMC_yields_num_res K0D1' nl (0::nat) ))"
  shows False
proof -
  from assms have
    "\<exists>K0D1'. (\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>))"
  unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
  by (simp add: tape_of_nat_def)
  then obtain K0D1' where
     "(\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

(* first, create a composable version of the potentially non-composable machine K0D1' *)

  then have "composable_tm0 (mk_composable0 K0D1') \<and> (\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K0D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> mk_composable0 K0D1' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>))"
    using Hoare_halt_tm_impl_Hoare_halt_mk_composable0 composable_tm0_mk_composable0 by blast

  then have "\<exists>K0D1. composable_tm0 K0D1 \<and> (\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  then obtain K0D1 where w_K0D1: "composable_tm0 K0D1 \<and> (\<forall>nl.
          (nl \<in> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>)
       \<and>  (nl \<notin> K0 \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> K0D1 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>))"
    by blast

  define tm_contra where "tm_contra = K0D1 |+| tm_semi_id_eq0"

(* second, we derive some theorems from our assumptions *)
  have c2t_comp_t2c_TM_eq_for_tm_contra: "c2t (t2c tm_contra) = tm_contra"
    by (auto simp add: c2t_comp_t2c_eq)

(* now, we derive the contradiction *)
  show False 
  proof (cases "[t2c tm_contra] \<in> K0")
    case True
    from \<open>[t2c tm_contra] \<in> K0\<close> and w_K0D1 have
      "\<lbrace>\<lambda>tap.\<exists>z. tap = ([], <[t2c tm_contra]>)\<rbrace> K0D1 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
      by auto

    then have
      "\<lbrace>\<lambda>tap.\<exists>z. tap = ([], <[t2c tm_contra]>)\<rbrace> tm_contra \<up>"
      unfolding tm_contra_def
    proof (rule Hoare_plus_unhalt)
      from tm_semi_id_eq0_loops' show "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace> tm_semi_id_eq0 \<up>"
        using Hoare_unhalt_add_Bks_left_tape_L1 Hoare_unhalt_def assms
        by auto
    next
      from w_K0D1 show "composable_tm0 K0D1" by auto
    qed

    then have
      "\<lbrace>\<lambda>tap.\<exists>z. tap = ([], <[t2c tm_contra]>)\<rbrace> c2t (t2c tm_contra) \<up>"
      by (auto simp add: c2t_comp_t2c_TM_eq_for_tm_contra)

    then have "\<not>(reaches_final (c2t (t2c tm_contra)) [t2c tm_contra])"
      by (simp add: Hoare_unhalt_def Hoare_unhalt_impl_not_reaches_final)

    then have "[t2c tm_contra] \<notin> K0"
      by (auto simp add: K0_def)

    with  \<open>[t2c tm_contra] \<in> K0\<close> show False by auto
  next    
    case False
    from \<open>[t2c tm_contra] \<notin> K0\<close> and w_K0D1 have
      "\<lbrace>\<lambda>tap.\<exists>z. tap = ([], <[t2c tm_contra]>)\<rbrace> K0D1 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>"
      by auto
    then have
      "\<lbrace>\<lambda>tap.\<exists>z. tap = ([], <[t2c tm_contra]>)\<rbrace> tm_contra \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>"
      unfolding tm_contra_def
    proof (rule Hoare_plus_halt)
      from tm_semi_id_eq0_halts'' show "\<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace> tm_semi_id_eq0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>"
        by auto
    next
      from w_K0D1 show "composable_tm0 K0D1" by auto
    qed

    then have
      "\<lbrace>\<lambda>tap.\<exists>z. tap = ([], <[t2c tm_contra]>)\<rbrace> c2t (t2c tm_contra) \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>"
      by (auto simp add: c2t_comp_t2c_TM_eq_for_tm_contra)

    then have
      "reaches_final (c2t (t2c tm_contra)) [t2c tm_contra]"
      by (metis (mono_tags, lifting) Hoare_halt_def reaches_final_iff)

    then have "[t2c tm_contra] \<in> K0"
      by (auto simp add: K0_def)

    with \<open>[t2c tm_contra] \<notin> K0\<close> show False by auto
  qed
qed

corollary not_Turing_decidable_K0: "\<not>(turing_decidable K0)"
proof
  assume "turing_decidable K0"
  then have "(\<exists>D. (\<forall>nl.
          (nl \<in> K0 \<longrightarrow>TMC_yields_num_res D nl (1::nat))
       \<and>  (nl \<notin> K0 \<longrightarrow>TMC_yields_num_res D nl (0::nat) )))"
    by (auto simp add: turing_decidable_unfolded_into_TMC_yields_conditions tape_of_nat_def)
  with existence_of_decider_K0D1_for_K0_imp_False show False
    by blast
qed


end (* locale hpk *)

end
