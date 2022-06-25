section \<open>Confluence related rewriting properties\<close>
theory Rewriting_Properties
  imports Rewriting
    "Abstract-Rewriting.Abstract_Rewriting"
begin

subsection \<open>Confluence related ARS properties\<close>
definition "SCR_on r A \<equiv> (\<forall>a \<in> A. \<forall> b c. (a, b) \<in> r \<and> (a, c) \<in> r \<longrightarrow>
  (\<exists> d. (b, d) \<in> r\<^sup>= \<and>  (c, d) \<in> r\<^sup>*))"

abbreviation SCR :: "'a rel \<Rightarrow> bool" where "SCR r \<equiv> SCR_on r UNIV"

definition NFP_on :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "NFP_on r A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b c. (a, b) \<in> r\<^sup>* \<and> (a, c) \<in> r\<^sup>! \<longrightarrow> (b, c) \<in> r\<^sup>*)"

abbreviation NFP :: "'a rel \<Rightarrow> bool" where "NFP r \<equiv> NFP_on r UNIV"

definition CE_on :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "CE_on r s A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b. (a, b) \<in> r\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> (a, b) \<in> s\<^sup>\<leftrightarrow>\<^sup>*)"

abbreviation CE :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool" where "CE r s \<equiv> CE_on r s UNIV"

definition NE_on :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "NE_on r s A \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b. (a, b) \<in> r\<^sup>! \<longleftrightarrow> (a, b) \<in> s\<^sup>!)"

abbreviation NE :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool" where "NE r s \<equiv> NE_on r s UNIV"

subsection \<open>Signature closure of relation to model multihole context closure\<close>

(* AUX lemmas *)

lemma all_ctxt_closed_sig_rsteps [intro]:
  fixes \<R> :: "('f,'v) term rel"
  shows "all_ctxt_closed \<F> ((srstep \<F> \<R>)\<^sup>*)" (is "all_ctxt_closed _ (?R\<^sup>*)")
proof (rule trans_ctxt_sig_imp_all_ctxt_closed)
  fix C :: "('f,'v) ctxt" and s t :: "('f,'v)term"
  assume C: "funas_ctxt C \<subseteq> \<F>"
  and s: "funas_term s \<subseteq> \<F>"
  and t: "funas_term t \<subseteq> \<F>"
  and steps: "(s,t) \<in> ?R\<^sup>*"
  from steps
  show "(C \<langle> s \<rangle>, C \<langle> t \<rangle>) \<in> ?R\<^sup>*"
  proof (induct)
    case (step t u)
    from step(2) have tu: "(t,u) \<in> rstep \<R>" and t: "funas_term t \<subseteq> \<F>" and u: "funas_term u \<subseteq> \<F>"
      by (auto dest: srstepD)
    have "(C \<langle> t \<rangle>, C \<langle> u \<rangle>) \<in> ?R" by (rule sig_stepI[OF _ _ rstep_ctxtI[OF tu]], insert C t u, auto)
    with step(3) show ?case by auto
  qed auto
qed (auto intro: trans_rtrancl)

lemma sigstep_trancl_funas:
  "(s, t) \<in> (srstep \<F> \<S>)\<^sup>* \<Longrightarrow> s \<noteq> t \<Longrightarrow> funas_term s \<subseteq> \<F>"
  "(s, t) \<in> (srstep \<F> \<S>)\<^sup>* \<Longrightarrow> s \<noteq> t \<Longrightarrow> funas_term t \<subseteq> \<F>"
  by (auto simp: rtrancl_eq_or_trancl dest: srstepsD)

lemma srrstep_to_srestep:
  "(s, t) \<in> srrstep \<F> \<R> \<Longrightarrow> (s, t) \<in> srstep \<F> \<R>"
  by (meson in_mono rrstep_rstep_mono sig_step_mono2)

lemma srsteps_with_root_step_srstepsD:
  "(s, t) \<in> srsteps_with_root_step \<F> \<R> \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  by (auto dest: srrstep_to_srestep simp: srsteps_with_root_step_def)

lemma srsteps_with_root_step_sresteps_eqD:
  "(s, t) \<in> srsteps_with_root_step \<F> \<R> \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  by (auto dest: srrstep_to_srestep simp: srsteps_with_root_step_def)

lemma symcl_srstep_conversion:
  "(s, t) \<in> srstep \<F> (\<R>\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
  by (simp add: conversion_def rstep_converse_dist srstep_symcl_dist)

lemma symcl_srsteps_conversion:
  "(s, t) \<in> (srstep \<F> (\<R>\<^sup>\<leftrightarrow>))\<^sup>* \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
  by (simp add: conversion_def rstep_converse_dist srstep_symcl_dist)



lemma NF_srstep_args:
  assumes "Fun f ss \<in> NF (srstep \<F> \<R>)" "funas_term (Fun f ss) \<subseteq> \<F>" "i < length ss"
  shows "ss ! i \<in> NF (srstep \<F> \<R>)"
proof (rule ccontr)
  assume "ss ! i \<notin> NF (srstep \<F> \<R>)"
  then obtain t where step: "(ss ! i, t) \<in> rstep \<R>" "funas_term t \<subseteq> \<F>"
    by (auto simp: NF_def sig_step_def)
  from assms(3) have [simp]: "Suc (length ss - Suc 0) = length ss" by auto
  from rstep_ctxtI[OF step(1), where ?C = "ctxt_at_pos (Fun f ss)[i]"]  
  have "(Fun f ss, Fun f (ss[i := t])) \<in> srstep \<F> \<R>" using step(2) assms(2, 3)
    by (auto simp: sig_step_def upd_conv_take_nth_drop min_def UN_subset_iff
             dest: in_set_takeD in_set_dropD simp flip: id_take_nth_drop)
  then show False using assms(1)
    by (auto simp: NF_def)
qed

lemma all_ctxt_closed_srstep_conversions [simp]:
  "all_ctxt_closed \<F> ((srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*)"
  by (simp add: all_ctxt_closed_sig_rsteps sig_step_conversion_dist)

(* END AUX *)

lemma NFP_stepD:
  "NFP r \<Longrightarrow> (a, b) \<in> r\<^sup>* \<Longrightarrow> (a, c) \<in> r\<^sup>* \<Longrightarrow> c \<in> NF r \<Longrightarrow> (b, c) \<in> r\<^sup>*"
  by (auto simp: NFP_on_def)
  
lemma NE_symmetric: "NE r s \<Longrightarrow> NE s r"
  unfolding NE_on_def by auto

lemma CE_symmetric: "CE r s \<Longrightarrow> CE s r"
  unfolding CE_on_def by auto

text \<open>Reducing the quantification over rewrite sequences for properties @{const CR} ... to
rewrite sequences containing at least one root step\<close>
lemma all_ctxt_closed_sig_reflE:
  "all_ctxt_closed \<F> \<R> \<Longrightarrow> funas_term t \<subseteq> \<F> \<Longrightarrow> (t, t) \<in> \<R>"
proof (induct t)
  case (Fun f ts)
  from Fun(1)[OF nth_mem  Fun(2)] Fun(3)
  have "i < length ts \<Longrightarrow> funas_term (ts ! i) \<subseteq> \<F>" "i < length ts \<Longrightarrow> (ts ! i, ts ! i) \<in> \<R>" for i
    by (auto simp: SUP_le_iff)
  then show ?case using all_ctxt_closedD[OF Fun(2)] Fun(3)
    by simp
qed (simp add: all_ctxt_closed_def)


lemma all_ctxt_closed_relcomp [intro]:
  "(\<And> s t. (s, t) \<in> \<R> \<Longrightarrow> s \<noteq> t \<Longrightarrow> funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F>) \<Longrightarrow>
   (\<And> s t. (s, t) \<in> \<S> \<Longrightarrow> s \<noteq> t \<Longrightarrow> funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F>) \<Longrightarrow>
   all_ctxt_closed \<F> \<R> \<Longrightarrow> all_ctxt_closed \<F> \<S> \<Longrightarrow> all_ctxt_closed \<F> (\<R> O \<S>)"
proof -
  assume funas:"(\<And> s t. (s, t) \<in> \<R> \<Longrightarrow> s \<noteq> t \<Longrightarrow> funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F>)"
    "(\<And> s t. (s, t) \<in> \<S> \<Longrightarrow> s \<noteq> t \<Longrightarrow> funas_term s \<subseteq> \<F> \<and> funas_term t \<subseteq> \<F>)"
    and ctxt_cl: "all_ctxt_closed \<F> \<R>" "all_ctxt_closed \<F> \<S>"
  {fix f ss ts assume ass: "(f, length ss) \<in> \<F>" "length ss = length ts" "\<And> i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> (\<R> O \<S>)"
    "\<And> i . i < length ts \<Longrightarrow> funas_term (ts ! i) \<subseteq> \<F>" "\<And>i. i < length ts \<Longrightarrow> funas_term (ss ! i) \<subseteq> \<F>"
    from ass(2, 3) obtain us where us: "length us = length ts" "\<And> i. i < length ts \<Longrightarrow> (ss ! i, us ! i) \<in> \<R>"
      "\<And> i. i < length ts \<Longrightarrow> (us ! i, ts ! i) \<in> \<S>"
      using Ex_list_of_length_P[of "length ts" "\<lambda> x i. (ss ! i, x) \<in> \<R> \<and> (x, ts ! i) \<in> \<S>"]
      by auto
    from funas have fu: "\<And> i . i < length us \<Longrightarrow> funas_term (us ! i) \<subseteq> \<F>" using us ass(4, 5)
      by (auto simp: funas_rel_def) (metis in_mono)
    have "(Fun f ss, Fun f us) \<in> \<R>" using ass(1, 2, 5) us(1, 2) fu
      by (intro all_ctxt_closedD[OF ctxt_cl(1), of f]) auto
    moreover have "(Fun f us, Fun f ts) \<in> \<S>"  using ass(1, 2, 4) us(1, 3) fu
      by (intro all_ctxt_closedD[OF ctxt_cl(2), of f]) auto
    ultimately have "(Fun f ss, Fun f ts) \<in> \<R> O \<S>" by auto}
  moreover
  {fix x have "(Var x, Var x) \<in> \<R>" "(Var x, Var x) \<in> \<S>" using ctxt_cl
      by (auto simp: all_ctxt_closed_def)
    then have "(Var x, Var x) \<in> \<R> O \<S>" by auto}
  ultimately show ?thesis by (auto simp: all_ctxt_closed_def)
qed


abbreviation "prop_to_rel P \<equiv> {(s, t)| s t. P s t}"

abbreviation "prop_mctxt_cl \<F> P \<equiv> all_ctxt_closed \<F> (prop_to_rel P)"

lemma prop_mctxt_cl_Var:
  "prop_mctxt_cl \<F> P \<Longrightarrow> P (Var x) (Var x)"
  by (simp add: all_ctxt_closed_def)

lemma prop_mctxt_cl_refl_on:
  "prop_mctxt_cl \<F> P \<Longrightarrow> funas_term t \<subseteq> \<F> \<Longrightarrow> P t t"
  using all_ctxt_closed_sig_reflE by blast

lemma prop_mctxt_cl_reflcl_on:
  "prop_mctxt_cl \<F> P \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> P s s"
  using all_ctxt_closed_sig_reflE by blast

lemma reduction_relations_to_root_step:
  assumes "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> \<R> \<Longrightarrow> P s t"
    and cl: "prop_mctxt_cl \<F> P"
    and well: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
    and steps: "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  shows "P s t" using steps well
proof (induct s arbitrary: t)
  case (Var x)
  have "(Var x, t) \<in> (srstep \<F> \<R>)\<^sup>+ \<Longrightarrow> (Var x, t) \<in> srsteps_with_root_step \<F> \<R>"
    using nsrsteps_with_root_step_step_on_args by blast
  from assms(1)[OF this] show ?case using Var cl
    by (auto simp: rtrancl_eq_or_trancl dest: all_ctxt_closed_sig_reflE)
next
  case (Fun f ss) note IH = this show ?case
  proof (cases "Fun f ss = t")
    case True show ?thesis using IH(2, 4) unfolding True
      by (intro prop_mctxt_cl_reflcl_on[OF cl]) auto      
  next
    case False
    then have step: "(Fun f ss, t) \<in> (srstep \<F> \<R>)\<^sup>+" using IH(2)
      by (auto simp: refl rtrancl_eq_or_trancl)
    show ?thesis
    proof (cases "(Fun f ss, t) \<in> srsteps_with_root_step \<F> \<R>")
      case False
      from nsrsteps_with_root_step_step_on_args[OF step this] obtain ts
        where *[simp]: "t = Fun f ts" and inv: "length ss = length ts"
          "\<forall> i < length ts. (ss ! i, ts ! i) \<in> (srstep \<F> \<R>)\<^sup>*"
        by auto
      have funas: "(f, length ts) \<in> \<F>" "\<forall>i<length ts. funas_term (ss ! i) \<subseteq> \<F> \<and> funas_term (ts ! i) \<subseteq> \<F>"
        using IH(3, 4) step inv(1) by (auto simp: UN_subset_iff)
      then have t: "\<forall> i < length ts. P (ss ! i) (ts ! i)"
        using prop_mctxt_cl_reflcl_on[OF cl]  IH(1) inv
        by (auto simp: rtrancl_eq_or_trancl)
      then show ?thesis unfolding * using funas inv(1) all_ctxt_closedD[OF cl]
        by auto
    qed (auto simp add: assms(1))
  qed
qed



abbreviation "comp_rrstep_rel \<F> \<R> \<S> \<equiv> srsteps_with_root_step \<F> \<R> O (srstep \<F> \<S>)\<^sup>* \<union>
  (srstep \<F> \<R>)\<^sup>* O srsteps_with_root_step \<F> \<S>"

abbreviation "comp_rrstep_rel' \<F> \<R> \<S> \<equiv> srsteps_with_root_step \<F> \<R> O (srstep \<F> \<S>)\<^sup>+ \<union>
  (srstep \<F> \<R>)\<^sup>+ O srsteps_with_root_step \<F> \<S>"

lemma reduction_join_relations_to_root_step:
  assumes "\<And> s t. (s, t) \<in> comp_rrstep_rel \<F> \<R> \<S> \<Longrightarrow> P s t"
    and cl: "prop_mctxt_cl \<F> P"
    and well: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>"
    and steps: "(s, t) \<in> (srstep \<F> \<R>)\<^sup>* O (srstep \<F> \<S>)\<^sup>*"
  shows "P s t" using steps well
proof (induct s arbitrary: t)
  case (Var x)
  have f: "(Var x, t) \<in> (srstep \<F> \<R>)\<^sup>+ \<Longrightarrow> (Var x, t) \<in> comp_rrstep_rel \<F> \<R> \<S>"
    using nsrsteps_with_root_step_step_on_args[of "Var x" _ \<F> \<R>] unfolding srsteps_with_root_step_def
    by (metis (no_types, lifting) Term.term.simps(4) UnI1 relcomp.relcompI rtrancl_eq_or_trancl)
  have s: "(Var x, t) \<in> (srstep \<F> \<S>)\<^sup>+ \<Longrightarrow> (Var x, t) \<in> comp_rrstep_rel \<F> \<R> \<S>"
    using nsrsteps_with_root_step_step_on_args[of "Var x" _ \<F> \<S>] unfolding srsteps_with_root_step_def
    by (metis (no_types, lifting) Term.term.simps(4) UnI2 relcomp.simps rtrancl.simps)
  have t: "(Var x, u) \<in> (srstep \<F> \<R>)\<^sup>+ \<Longrightarrow> (u, t) \<in> (srstep \<F> \<S>)\<^sup>+ \<Longrightarrow> (Var x, t) \<in> comp_rrstep_rel \<F> \<R> \<S>" for u
    using nsrsteps_with_root_step_step_on_args[of "Var x" u \<F> \<R>] unfolding srsteps_with_root_step_def
    by auto (meson relcomp.simps trancl_into_rtrancl)
  show ?case using Var f[THEN assms(1)] s[THEN assms(1)] t[THEN assms(1)] cl
    by (auto simp: rtrancl_eq_or_trancl prop_mctxt_cl_Var)
next
  case (Fun f ss) note IH = this show ?case
  proof (cases "Fun f ss = t")
    case True show ?thesis using IH(2, 3, 4) cl
      by (auto simp: True prop_mctxt_cl_refl_on)
  next
    case False
    obtain u where u: "(Fun f ss, u) \<in> (srstep \<F> \<R>)\<^sup>*" "(u, t) \<in> (srstep \<F> \<S>)\<^sup>*" using IH(2) by auto
    show ?thesis
    proof (cases "(Fun f ss, u) \<in> srsteps_with_root_step \<F> \<R>")
      case True
      then have "(Fun f ss, t) \<in> comp_rrstep_rel \<F> \<R> \<S>" using u
        by (auto simp: srsteps_with_root_step_def)
      from assms(1)[OF this] show ?thesis by simp
    next
      case False note nt_fst = this show ?thesis
      proof (cases "(u, t) \<in> srsteps_with_root_step \<F> \<S>")
        case True
        then have "(Fun f ss, t) \<in> comp_rrstep_rel \<F> \<R> \<S>" using u unfolding srsteps_with_root_step_def
          by blast
        from assms(1)[OF this] show ?thesis by simp
      next
        case False note no_root = False nt_fst
        show ?thesis
        proof (cases "Fun f ss = u \<or> u = t")
          case True
          from assms(1) have f: "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> \<R> \<Longrightarrow> P s t"
            and s: "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> \<S> \<Longrightarrow> P s t" unfolding srsteps_with_root_step_def
            by blast+
          have "u = t \<Longrightarrow> ?thesis" using u cl IH(3, 4)
            by (intro reduction_relations_to_root_step[OF f]) auto
          moreover have "Fun f ss = u \<Longrightarrow> ?thesis" using u cl IH(3, 4)
            by (intro reduction_relations_to_root_step[OF s]) auto
          ultimately show ?thesis using True by auto
        next
          case False
          then have steps: "(Fun f ss, u) \<in> (srstep \<F> \<R>)\<^sup>+" "(u, t) \<in> (srstep \<F> \<S>)\<^sup>+" using u
            by (auto simp: rtrancl_eq_or_trancl)
          obtain ts us
            where [simp]: "u = Fun f us" and inv_u: "length ss = length us" "\<forall> i < length ts. (ss ! i, us ! i) \<in> (srstep \<F> \<R>)\<^sup>*"
              and [simp]: "t = Fun f ts" and inv_t: "length us = length ts" "\<forall> i < length ts. (us ! i, ts ! i) \<in> (srstep \<F> \<S>)\<^sup>*"
            using nsrsteps_with_root_step_step_on_args[OF steps(1) no_root(2)]
            using nsrsteps_with_root_step_step_on_args[OF steps(2) no_root(1)]
            by auto
          from inv_u inv_t cl IH(3, 4) have t: "\<forall> i < length ts. P (ss ! i) (ts ! i)"
            by (auto simp: UN_subset_iff intro!: IH(1)[OF nth_mem, of i "ts ! i" for i])
          moreover have "(f, length ts) \<in> \<F>" using IH(4) by auto 
          ultimately show ?thesis using IH(3, 4) inv_u inv_t all_ctxt_closedD[OF cl]
            by (auto simp: UN_subset_iff)
        qed
      qed
    qed
  qed
qed

\<comment> \<open>Reducing search space for @{const commute} to conversions involving root steps\<close>

definition "commute_redp \<F> \<R> \<S> s t \<longleftrightarrow> (s, t) \<in> ((srstep \<F> \<S>)\<^sup>* O ((srstep \<F> \<R>)\<inverse>)\<^sup>*)"

declare subsetI[rule del]
lemma commute_redp_mctxt_cl:
  "prop_mctxt_cl \<F> (commute_redp \<F> \<R> \<S>)"
  by (auto simp: commute_redp_def rew_converse_inwards
    dest: sigstep_trancl_funas intro!: all_ctxt_closed_relcomp)
declare subsetI[intro!]

lemma commute_rrstep_intro:
  assumes "\<And> s t. (s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<S> \<Longrightarrow> commute_redp \<F> \<R> \<S> s t"
  shows "commute (srstep \<F> \<R>) (srstep \<F> \<S>)"
proof -
  have [simp]: "x \<in> srsteps_with_root_step \<F> \<U> \<Longrightarrow> x \<in> (srstep \<F> \<U>)\<^sup>* O \<L>\<^sup>*" for x \<U> \<L>
    by (cases x) (auto dest!: srsteps_with_root_step_sresteps_eqD)
  have [simp]: "x \<in> srsteps_with_root_step \<F> \<U> \<Longrightarrow> x \<in> \<L>\<^sup>* O (srstep \<F> \<U>)\<^sup>*" for x \<U> \<L>
    by (cases x) (auto dest!: srsteps_with_root_step_sresteps_eqD)
  have red: "\<And> s t. (s, t) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<S> \<Longrightarrow> commute_redp \<F> \<R> \<S> s t" using assms
    unfolding commute_redp_def srstep_converse_dist
    by (auto simp: rtrancl_eq_or_trancl) blast+
  have comI: "(\<And> s t. (s, t) \<in> ((srstep \<F> (\<R>\<inverse>))\<^sup>*) O (srstep \<F> \<S>)\<^sup>* \<Longrightarrow> commute_redp \<F> \<R> \<S> s t) \<Longrightarrow>
    commute (srstep \<F> \<R>) (srstep \<F> \<S>)"
    by (auto simp: commute_redp_def commute_def subsetD rew_converse_inwards)
  show ?thesis
    using reduction_join_relations_to_root_step[OF red commute_redp_mctxt_cl, of "\<R>\<inverse>" \<S>]
    by (intro comI, auto) (metis (no_types, lifting) commute_redp_def relcompI rew_converse_inwards sigstep_trancl_funas srstep_converse_dist)
qed

lemma commute_to_rrstep:
  assumes "commute (srstep \<F> \<R>) (srstep \<F> \<S>)"
  shows "\<And> s t. (s, t) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<S> \<Longrightarrow> commute_redp \<F> \<R> \<S> s t" using assms
  unfolding commute_def commute_redp_def srstep_converse_dist
  by (auto simp: srstep_converse_dist dest: srsteps_with_root_step_sresteps_eqD)

\<comment> \<open>Reducing search space for @{const CR} to conversions involving root steps\<close>

lemma CR_Aux:
  assumes "\<And> s t. (s, t) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>* O srsteps_with_root_step \<F> \<R> \<Longrightarrow> commute_redp \<F> \<R> \<R> s t"
  shows "\<And> s t. (s, t) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<R> \<Longrightarrow> commute_redp \<F> \<R> \<R> s t"
proof -
  have sym: "commute_redp \<F> \<R> \<R> s t \<Longrightarrow> commute_redp \<F> \<R> \<R> t s" for s t
    by (auto simp: commute_redp_def) (metis converseI relcomp.relcompI rtrancl_converse rtrancl_converseD)
  {fix s t assume "(s, t) \<in> (srstep \<F> \<R>)\<^sup>* O srsteps_with_root_step \<F> (\<R>\<inverse>)"
    then have "commute_redp \<F> \<R> \<R> s t"  unfolding commute_redp_def
      by (auto simp: srsteps_with_root_step_def rew_converse_inwards dest!: srrstep_to_srestep)}
  note * = this
  {fix s t assume ass: "(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<inverse>) O (srstep \<F> \<R>)\<^sup>*"
    have [dest!]: "(u, t) \<in> (srstep \<F> \<R>)\<^sup>* \<Longrightarrow> (t, u) \<in> (sig_step \<F> ((rstep \<R>)\<inverse>))\<^sup>*" for u
      by (metis rew_converse_outwards rtrancl_converseI srstep_converse_dist)
    from ass have "(t, s) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>* O srsteps_with_root_step \<F> \<R>"
      unfolding srsteps_with_root_step_def rstep_converse_dist
      by (metis (mono_tags, lifting) O_assoc converse.simps converse_converse converse_inward(1) converse_relcomp rew_converse_outwards(1, 2) sig_step_converse_rstep)
  from assms[OF this] have "commute_redp \<F> \<R> \<R> s t" using sym by blast}
  then show "\<And> s t. (s, t) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<R> \<Longrightarrow> commute_redp \<F> \<R> \<R> s t" unfolding srsteps_with_root_step_def
    by (metis UnE assms srsteps_with_root_step_def)
qed

lemma CR_rrstep_intro:
  assumes "\<And> s t. (s, t) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>+ O srsteps_with_root_step \<F> \<R> \<Longrightarrow> commute_redp \<F> \<R> \<R> s t"
  shows "CR (srstep \<F> \<R>)"
proof -
  {fix s u assume "(s, u) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>* O srsteps_with_root_step \<F> \<R>"
    then obtain t where a: "(s, t) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>*" "(t, u) \<in> srsteps_with_root_step \<F> \<R>" by blast
    have "commute_redp \<F> \<R> \<R> s u"
    proof (cases "s = t")
      case [simp]: True
      from srsteps_with_root_step_srstepsD[OF a(2)] show ?thesis
        by (auto simp: commute_redp_def)
    next
      case False
      then have "(s, t) \<in> (srstep \<F> (\<R>\<inverse>))\<^sup>+" using a(1) unfolding rtrancl_eq_or_trancl
        by simp
      then show ?thesis using assms a(2) by blast
    qed}
  from commute_rrstep_intro[OF CR_Aux[OF this]]
  show ?thesis unfolding CR_iff_self_commute
    by (metis Un_iff reflcl_trancl relcomp_distrib relcomp_distrib2)
qed

lemma CR_to_rrstep:
  assumes "CR (srstep \<F> \<R>)"
  shows "\<And> s t. (s, t) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<R> \<Longrightarrow> commute_redp \<F> \<R> \<R> s t" using assms
  using commute_to_rrstep[OF assms[unfolded CR_iff_self_commute]]
  by simp

\<comment> \<open>Reducing search space for @{const NFP} to conversions involving root steps\<close>

definition NFP_redp where
  "NFP_redp \<F> \<R> s t \<longleftrightarrow> t \<in> NF (srstep \<F> \<R>) \<longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>*"

lemma prop_mctxt_cl_NFP_redp:
  "prop_mctxt_cl \<F> (NFP_redp \<F> \<R>)"
proof -
  {fix f ts ss assume sig: "(f, length ss) \<in> \<F>" "length ts = length ss"
      and steps: "\<forall> i < length ss. ss ! i \<in> NF (srstep \<F> \<R>) \<longrightarrow> (ts ! i, ss ! i) \<in> (srstep \<F> \<R>)\<^sup>*"
      and funas: "\<forall> i < length ss. funas_term (ts ! i) \<subseteq> \<F> \<and> funas_term (ss ! i) \<subseteq> \<F>"
      and NF: "Fun f ss \<in> NF (srstep \<F> \<R>)"
    from steps have steps:  "i < length ss \<Longrightarrow> (ts ! i, ss ! i) \<in> (srstep \<F> \<R>)\<^sup>*" for i
      using sig funas NF_srstep_args[OF NF]
      by (auto simp: UN_subset_iff) (metis in_set_idx)
    then have "(Fun f ts, Fun f ss) \<in> (srstep \<F> \<R>)\<^sup>*" using sig
      by (metis all_ctxt_closed_def all_ctxt_closed_sig_rsteps funas le_sup_iff)}
  then show ?thesis
    by (auto simp: NFP_redp_def all_ctxt_closed_def)
qed

lemma NFP_rrstep_intro:
  assumes "\<And> s t. (s, t) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R>\<Longrightarrow> NFP_redp \<F> \<R> s t"
  shows "NFP (srstep \<F> \<R>)"
proof -
  from assms have red: "\<And> t u. (t, u) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<R> \<Longrightarrow> NFP_redp \<F> \<R> t u"
    apply (auto simp: NFP_redp_def rtrancl_eq_or_trancl)
    apply (metis NF_no_trancl_step converseD srstep_converse_dist srsteps_with_root_step_srstepsD trancl_converse)
    apply blast
    apply (meson NF_no_trancl_step srsteps_with_root_step_srstepsD)
    by blast
  have "\<And> s t. (s, t) \<in> (sig_step \<F> ((rstep \<R>)\<inverse>))\<^sup>* O (srstep \<F> \<R>)\<^sup>* \<Longrightarrow> NFP_redp \<F> \<R> s t"
    using reduction_join_relations_to_root_step[OF red prop_mctxt_cl_NFP_redp, of "\<R>\<inverse>" \<R>]
    by (auto simp: NFP_redp_def) (metis (no_types, lifting) relcomp.relcompI rstep_converse_dist rtranclD srstepsD)
  then show ?thesis unfolding NFP_on_def NFP_redp_def
    by (auto simp: normalizability_def) (metis meetI meet_def rstep_converse_dist srstep_converse_dist)
qed

lemma NFP_lift_to_conversion:
  assumes "NFP r" "(s, t) \<in> (r\<^sup>\<leftrightarrow>)\<^sup>*" and "t \<in> NF r"
  shows "(s, t) \<in> r\<^sup>*" using assms(2, 3)
proof (induct rule: converse_rtrancl_induct)
  case (step s u)
  then have "(u, t) \<in> r\<^sup>!" by auto
  then show ?case using assms(1) step(1) unfolding NFP_on_def
    by auto
qed simp

lemma NFP_to_rrstep:
  assumes "NFP (srstep \<F> \<R>)"
  shows "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>) \<Longrightarrow> NFP_redp \<F> \<R> s t" using assms
  using NFP_lift_to_conversion[OF assms] unfolding NFP_redp_def srsteps_with_root_step_def
  by auto (metis (no_types, lifting) r_into_rtrancl rstep_converse_dist rtrancl_trans srrstep_to_srestep srstep_symcl_dist)


\<comment> \<open>Reducing search space for @{const UNC} to conversions involving root steps\<close>

definition "UN_redp \<F> \<R> s t \<longleftrightarrow> s \<in> NF (srstep \<F> \<R>) \<and> t \<in> NF (srstep \<F> \<R>) \<longrightarrow> s = t"

lemma prop_mctxt_cl_UN_redp:
  "prop_mctxt_cl \<F> (UN_redp \<F> \<R>)"
proof -
  {fix f ts ss assume sig: "(f, length ss) \<in> \<F>" "length ts = length ss"
      and steps: "\<forall> i < length ss. ts ! i \<in> NF (srstep \<F> \<R>) \<and> ss ! i \<in> NF (srstep \<F> \<R>) \<longrightarrow> ts ! i = ss ! i"
      and funas: "\<forall> i < length ss. funas_term (ts ! i) \<subseteq> \<F> \<and> funas_term (ss ! i) \<subseteq> \<F>"
      and NF: "Fun f ts \<in> NF (srstep \<F> \<R>)" "Fun f ss \<in> NF (srstep \<F> \<R>)"
    from steps have steps: "i < length ss \<Longrightarrow> ts ! i = ss ! i" for i
      using sig funas NF_srstep_args[OF NF(1)] NF_srstep_args[OF NF(2)]
      by (auto simp: UN_subset_iff) (metis in_set_idx)
    then have "Fun f ts = Fun f ss" using sig(2)
      by (simp add: nth_equalityI)}
  then show ?thesis
    by (auto simp: UN_redp_def all_ctxt_closed_def)
qed

lemma UNC_rrstep_intro:
  assumes"\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>) \<Longrightarrow> UN_redp \<F> \<R> s t"
  shows "UNC (srstep \<F> \<R>)"
proof -
  have "\<And> s t. (s, t) \<in> (srstep \<F> (\<R>\<^sup>\<leftrightarrow>))\<^sup>* \<Longrightarrow> UN_redp \<F> \<R> s t"
    using reduction_relations_to_root_step[OF assms(1) prop_mctxt_cl_UN_redp, of "\<R>\<^sup>\<leftrightarrow>"]
    by (auto simp: UN_redp_def) (meson rtranclD srstepsD)
  then show ?thesis unfolding UNC_def UN_redp_def
    by (auto simp: sig_step_conversion_dist)
qed

lemma UNC_to_rrstep:
  assumes "UNC (srstep \<F> \<R>)"
  shows "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>) \<Longrightarrow> UN_redp \<F> \<R> s t"
  using assms unfolding UNC_def UN_redp_def srsteps_with_root_step_def
  by (auto dest!: srrstep_to_srestep symcl_srstep_conversion symcl_srsteps_conversion)
     (metis (no_types, opaque_lifting) conversion_def rtrancl_trans)


\<comment> \<open>Reducing search space for @{const UNF} to conversions involving root steps\<close>

lemma UNF_rrstep_intro:
  assumes "\<And> t u. (t, u) \<in> comp_rrstep_rel' \<F> (\<R>\<inverse>) \<R> \<Longrightarrow> UN_redp \<F> \<R> t u"
  shows "UNF (srstep \<F> \<R>)"
proof -
  from assms have red: "\<And> t u. (t, u) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<R> \<Longrightarrow> UN_redp \<F> \<R> t u"
    apply (auto simp: UN_redp_def rtrancl_eq_or_trancl)
    apply (metis NF_no_trancl_step converseD srstep_converse_dist srsteps_with_root_step_srstepsD trancl_converse)
    apply blast
    apply (meson NF_no_trancl_step srsteps_with_root_step_srstepsD)
    by blast
  have "\<And> s t. (s, t) \<in> (sig_step \<F> ((rstep \<R>)\<inverse>))\<^sup>* O (srstep \<F> \<R>)\<^sup>* \<Longrightarrow> UN_redp \<F> \<R> s t"
    using reduction_join_relations_to_root_step[OF red prop_mctxt_cl_UN_redp, of "\<R>\<inverse>" \<R>]
    by (auto simp: UN_redp_def) (metis (no_types, lifting) relcomp.relcompI rstep_converse_dist rtranclD srstepsD)
  then show ?thesis unfolding UNF_on_def UN_redp_def
    by (auto simp: normalizability_def) (metis meetI meet_def rstep_converse_dist srstep_converse_dist)
qed

lemma UNF_to_rrstep:
  assumes "UNF (srstep \<F> \<R>)"
  shows "\<And> s t. (s, t) \<in> comp_rrstep_rel \<F> (\<R>\<inverse>) \<R> \<Longrightarrow> UN_redp \<F> \<R> s t"
  using assms unfolding UNF_on_def UN_redp_def normalizability_def srsteps_with_root_step_def
  by (auto simp flip: srstep_converse_dist dest!: srrstep_to_srestep)
   (metis (no_types, lifting) rstep_converse_dist rtrancl.rtrancl_into_rtrancl rtrancl_converseD rtrancl_idemp srstep_converse_dist)+

\<comment> \<open>Reducing search space for @{const CE} to conversions involving root steps\<close>

lemma CE_rrstep_intro:
  assumes "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
    and "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> (\<S>\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "CE (srstep \<F> \<R>) (srstep \<F> \<S>)"
  using reduction_relations_to_root_step[OF assms(1), where ?s1 = "\<lambda> s t. s" and ?t1 = "\<lambda> s t. t", of \<F> "\<R>\<^sup>\<leftrightarrow>"]
  using reduction_relations_to_root_step[OF assms(2), where ?s1 = "\<lambda> s t. s" and ?t1 = "\<lambda> s t. t", of \<F> "\<S>\<^sup>\<leftrightarrow>"]
  by (auto simp: CE_on_def)
     (metis converseI conversion_converse rtrancl_eq_or_trancl sig_step_conversion_dist sigstep_trancl_funas(1, 2))+

lemma CE_to_rrstep:
  assumes "CE (srstep \<F> \<R>) (srstep \<F> \<S>)"
  shows "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> (\<R>\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, t) \<in> (srstep \<F> \<S>)\<^sup>\<leftrightarrow>\<^sup>*"
        "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> (\<S>\<^sup>\<leftrightarrow>) \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>\<leftrightarrow>\<^sup>*"
  using assms unfolding CE_on_def srsteps_with_root_step_def
  by (auto simp flip: srstep_converse_dist dest!: srrstep_to_srestep symcl_srsteps_conversion symcl_srstep_conversion)
     (metis converse_rtrancl_into_rtrancl conversion_rtrancl)+


\<comment> \<open>Reducing search space for @{const NE} to conversions involving root steps\<close>

definition NE_redp where
  "NE_redp \<F> \<R> \<S> s t \<longleftrightarrow> t \<in> NF (srstep \<F> \<R>) \<longrightarrow> t \<in> NF (srstep \<F> \<R>) \<longrightarrow> (s, t) \<in> (srstep \<F> \<S>)\<^sup>*"

lemma prop_mctxt_cl_NE_redp:
  "prop_mctxt_cl \<F> (NE_redp \<F> \<R> \<S>)"
proof -
  {fix f ts ss assume sig: "(f, length ss) \<in> \<F>" "length ts = length ss"
      and steps: "\<forall> i < length ss. ss ! i \<in> NF (srstep \<F> \<R>) \<longrightarrow> (ts ! i, ss ! i) \<in> (srstep \<F> \<S>)\<^sup>*"
      and funas: "\<forall> i < length ss. funas_term (ts ! i) \<subseteq> \<F> \<and> funas_term (ss ! i) \<subseteq> \<F>"
      and NF: "Fun f ss \<in> NF (srstep \<F> \<R>)"
    from steps have steps:  "i < length ss \<Longrightarrow> (ts ! i, ss ! i) \<in> (srstep \<F> \<S>)\<^sup>*" for i
      using sig funas NF_srstep_args[OF NF]
      by (auto simp: UN_subset_iff) (metis in_set_idx)
    then have "(Fun f ts, Fun f ss) \<in> (srstep \<F> \<S>)\<^sup>*" using sig
      by (metis all_ctxt_closed_def all_ctxt_closed_sig_rsteps funas le_sup_iff)}
  then show ?thesis
    by (auto simp: all_ctxt_closed_def NE_redp_def)
qed

lemma NE_rrstep_intro:
  assumes "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> \<R> \<Longrightarrow> NE_redp \<F> \<R> \<S> s t"
    and "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> \<S> \<Longrightarrow> NE_redp \<F> \<S> \<R> s t"
    and "NF (srstep \<F> \<R>) = NF (srstep \<F> \<S>)"
  shows "NE (srstep \<F> \<R>) (srstep \<F> \<S>)"
  using assms(3)
  using reduction_relations_to_root_step[OF assms(1) prop_mctxt_cl_NE_redp, of \<R>]
  using reduction_relations_to_root_step[OF assms(2) prop_mctxt_cl_NE_redp, of \<S>]
  by (auto simp: NE_on_def NE_redp_def normalizability_def)
     (metis rtrancl.rtrancl_refl sigstep_trancl_funas)+


lemma NE_to_rrstep:
  assumes "NE (srstep \<F> \<R>) (srstep \<F> \<S>)"
  shows  "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> \<R> \<Longrightarrow> NE_redp \<F> \<R> \<S> s t"
         "\<And> s t. (s, t) \<in> srsteps_with_root_step \<F> \<S> \<Longrightarrow> NE_redp \<F> \<S> \<R> s t"
  using assms unfolding NE_on_def NE_redp_def srsteps_with_root_step_def
  by (auto simp: normalizability_def simp flip: srstep_converse_dist
     dest!: srrstep_to_srestep) (meson converse_rtrancl_into_rtrancl rtrancl_trans)+

lemma NE_NF_eq:
  "NE \<R> \<S> \<Longrightarrow> NF \<R> = NF \<S>"
  by (auto simp: NE_on_def NF_def normalizability_def)

\<comment> \<open>Reducing search space for @{const SCR} and @{const WCR} involving root steps\<close>
(*Brute forced proofs could be done nicer with more lemmas related to positions *)

abbreviation "SCRp \<F> \<R> t u \<equiv> \<exists>v. (t, v) \<in> (srstep \<F> \<R>)\<^sup>= \<and> (u, v) \<in> (srstep \<F> \<R>)\<^sup>*"
lemma SCR_rrstep_intro:
  assumes "\<And> s t u. (s, t) \<in> sig_step \<F> (rrstep \<R>) \<Longrightarrow> (s, u) \<in> srstep \<F> \<R> \<Longrightarrow> SCRp \<F> \<R> t u"
    and "\<And> s t u. (s, t) \<in> srstep \<F> \<R> \<Longrightarrow> (s, u) \<in> sig_step \<F> (rrstep \<R>) \<Longrightarrow> SCRp \<F> \<R> t u"
  shows "SCR (srstep \<F> \<R>)"
proof -
  {fix s t u assume step: "(s, t) \<in> srstep \<F> \<R>" "(s, u) \<in> srstep \<F> \<R>"
    from step(1) obtain p l r \<sigma> where st: "p \<in> poss s" "(l, r) \<in> \<R>" "s |_ p = l \<cdot> \<sigma>" "t = s[p \<leftarrow> r \<cdot> \<sigma>]"
      using rstep_to_pos_replace[of s t \<R>] unfolding sig_step_def by blast
    from step(2) obtain q l2 r2 \<sigma>2 where su: "q \<in> poss s" "(l2, r2) \<in> \<R>" "s |_ q = l2 \<cdot> \<sigma>2" "u = s[q \<leftarrow> r2 \<cdot> \<sigma>2]"
      using rstep_to_pos_replace[of s u \<R>] unfolding sig_step_def by blast
    from step st su have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>"
      by (auto dest: srstepD)
    have funas2 :"funas_term (r2 \<cdot> \<sigma>2) \<subseteq> \<F>" using funas_term_replace_at_lower[OF su(1)]
      using funas(3) unfolding su(4) by blast
    consider (a) "p \<le>\<^sub>p q" | (b) "q \<le>\<^sub>p p" | (c) "p \<bottom> q"
      using position_par_def by blast
    then have "SCRp \<F> \<R> t u"
    proof cases
      case a
      from a have up: "p \<in> poss u" using st(1) su(1) unfolding st(4) su(4)
        by (metis pos_replace_at_pres position_less_eq_def poss_append_poss)
      let ?C = "ctxt_at_pos s p" have fc: "funas_ctxt ?C \<subseteq> \<F>" using funas(1) st(1)
        by (metis ctxt_at_pos_subt_at_id funas_ctxt_apply le_sup_iff)
      from funas have funas: "funas_term (s |_ p) \<subseteq> \<F>" "funas_term (t |_ p) \<subseteq> \<F>" "funas_term (u |_ p) \<subseteq> \<F>"
        using a st(1) pos_replace_at_pres[OF st(1)] up unfolding st(4) su(4)
        by (intro funas_term_subterm_atI, blast+)+
      have "(s |_ p, t |_ p) \<in> sig_step \<F> (rrstep \<R>)" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (metis poss_of_termE poss_of_term_replace_term_at rrstep.intros sig_stepI st(4))
      moreover have "(s |_ p, u |_ p) \<in> srstep \<F> \<R>" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (smt (verit, best) a ctxt_at_pos_subt_at_pos ctxt_of_pos_term_apply_replace_at_ident position_less_eq_def
            poss_append_poss replace_subterm_at_itself replace_term_at_subt_at_id rstepI sig_stepI su(4))
      ultimately obtain v where "(t |_ p, v) \<in> (srstep \<F> \<R>)\<^sup>=" "(u |_ p, v) \<in> (srstep \<F> \<R>)\<^sup>*"
        using assms(1) by blast
      from this(1) srsteps_eq_ctxt_closed[OF fc this(2)]
      show ?thesis using a st(1) su(1) srsteps_eq_ctxt_closed[OF fc] unfolding st(4) su(4)
        apply (intro exI[of _ "?C\<langle>v\<rangle>"])
        apply (auto simp: ctxt_of_pos_term_apply_replace_at_ident less_eq_subt_at_replace)
        apply (metis ctxt_of_pos_term_apply_replace_at_ident fc srstep_ctxt_closed)
        done
    next
      case b
      then have up: "q \<in> poss t" using st(1) su(1) unfolding st(4) su(4)
        by (metis pos_replace_at_pres position_less_eq_def poss_append_poss)
      let ?C = "ctxt_at_pos s q" have fc: "funas_ctxt ?C \<subseteq> \<F>" using funas(1) su(1)
        by (metis Un_subset_iff ctxt_at_pos_subt_at_id funas_ctxt_apply)
      from funas have funas: "funas_term (s |_ q) \<subseteq> \<F>" "funas_term (t |_ q) \<subseteq> \<F>" "funas_term (u |_ q) \<subseteq> \<F>"
        using su(1) pos_replace_at_pres[OF su(1)] up unfolding st(4) su(4)
        by (intro funas_term_subterm_atI, blast+)+
      have "(s |_ q, t |_ q) \<in> srstep \<F> \<R>" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (smt (verit, del_insts) b ctxt_at_pos_subt_at_pos ctxt_of_pos_term_apply_replace_at_ident
            position_less_eq_def poss_append_poss replace_subterm_at_itself replace_term_at_subt_at_id rstepI sig_stepI st(4))
      moreover have "(s |_ q, u |_ q) \<in> sig_step \<F> (rrstep \<R>)" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (metis poss_of_termE poss_of_term_replace_term_at rrstep.intros sig_stepI su(4))
      ultimately obtain v where "(t |_ q, v) \<in> (srstep \<F> \<R>)\<^sup>=" "(u |_ q, v) \<in> (srstep \<F> \<R>)\<^sup>*"
        using assms(2) by blast
      from this(1) srsteps_eq_ctxt_closed[OF fc this(2)]
      show ?thesis using b st(1) su(1) srsteps_eq_ctxt_closed[OF fc] unfolding st(4) su(4)
        apply (intro exI[of _ "?C\<langle>v\<rangle>"])
        apply (auto simp: ctxt_of_pos_term_apply_replace_at_ident less_eq_subt_at_replace)
        apply (smt (verit, best) ctxt_of_pos_term_apply_replace_at_ident fc less_eq_subt_at_replace replace_term_at_above replace_term_at_subt_at_id srstep_ctxt_closed)
        done
    next
      case c
      define v where "v = t[q \<leftarrow> r2 \<cdot> \<sigma>2]"
      have funasv: "funas_term v \<subseteq> \<F>" using funas su(1) unfolding v_def su(4)
        using funas_term_replace_at_upper funas2 by blast
      from c have *: "v = u[p \<leftarrow> r \<cdot> \<sigma>]" unfolding v_def st(4) su(4) using st(1) su(1)
        using parallel_replace_term_commute by blast
      from c have "(t, v) \<in> rstep \<R>" unfolding st(4) v_def
        using su(1 - 3) par_pos_replace_pres[OF su(1)]
        by (metis par_pos_replace_term_at pos_replace_to_rstep position_par_def)
      moreover from c have "(u, v) \<in> rstep \<R>" unfolding su(4) *
        using st(1 - 3) par_pos_replace_pres[OF st(1)]
        by (intro pos_replace_to_rstep[of _ _ l]) (auto simp: par_pos_replace_term_at)
      ultimately show ?thesis using funas(2-) funasv
        by auto
    qed}
  then show ?thesis unfolding SCR_on_def
    by blast
qed

lemma SCE_to_rrstep:
  assumes "SCR (srstep \<F> \<R>)"
  shows "\<And> s t u. (s, t) \<in> sig_step \<F> (rrstep \<R>) \<Longrightarrow> (s, u) \<in> srstep \<F> \<R> \<Longrightarrow> SCRp \<F> \<R> t u"
        "\<And> s t u. (s, t) \<in> srstep \<F> \<R> \<Longrightarrow> (s, u) \<in> sig_step \<F> (rrstep \<R>) \<Longrightarrow> SCRp \<F> \<R> t u"
  using assms unfolding SCR_on_def srsteps_with_root_step_def
  by (auto simp flip: srstep_converse_dist dest!: srrstep_to_srestep symcl_srsteps_conversion symcl_srstep_conversion)

lemma WCR_rrstep_intro:
  assumes "\<And> s t u. (s, t) \<in> sig_step \<F> (rrstep \<R>) \<Longrightarrow> (s, u) \<in> srstep \<F> \<R> \<Longrightarrow> (t, u) \<in> (srstep \<F> \<R>)\<^sup>\<down>"
  shows "WCR (srstep \<F> \<R>)"
proof -
  {fix s t u assume step: "(s, t) \<in> srstep \<F> \<R>" "(s, u) \<in> srstep \<F> \<R>"
    from step(1) obtain p l r \<sigma> where st: "p \<in> poss s" "(l, r) \<in> \<R>" "s |_ p = l \<cdot> \<sigma>" "t = s[p \<leftarrow> r \<cdot> \<sigma>]"
      using rstep_to_pos_replace[of s t \<R>] unfolding sig_step_def by blast
    from step(2) obtain q l2 r2 \<sigma>2 where su: "q \<in> poss s" "(l2, r2) \<in> \<R>" "s |_ q = l2 \<cdot> \<sigma>2" "u = s[q \<leftarrow> r2 \<cdot> \<sigma>2]"
      using rstep_to_pos_replace[of s u \<R>] unfolding sig_step_def by blast
    from step st su have funas: "funas_term s \<subseteq> \<F>" "funas_term t \<subseteq> \<F>" "funas_term u \<subseteq> \<F>"
      by (auto dest: srstepD)
    have funas2 :"funas_term (r2 \<cdot> \<sigma>2) \<subseteq> \<F>" using funas_term_replace_at_lower[OF su(1)]
      using funas(3) unfolding su(4) by blast
    consider (a) "p \<le>\<^sub>p q" | (b) "q \<le>\<^sub>p p" | (c) "p \<bottom> q"
      using position_par_def by blast
    then have "(t, u) \<in> (srstep \<F> \<R>)\<^sup>\<down>"
    proof cases
      case a
      then have up: "p \<in> poss u" using st(1) su(1) unfolding st(4) su(4)
        by (metis pos_replace_at_pres position_less_eq_def poss_append_poss)
      let ?C = "ctxt_at_pos s p" have fc: "funas_ctxt ?C \<subseteq> \<F>" using funas(1) st(1)
        by (metis Un_subset_iff ctxt_at_pos_subt_at_id funas_ctxt_apply)
      from funas have funas: "funas_term (s |_ p) \<subseteq> \<F>" "funas_term (t |_ p) \<subseteq> \<F>" "funas_term (u |_ p) \<subseteq> \<F>"
        using a st(1) pos_replace_at_pres[OF st(1)] up unfolding st(4) su(4)
        by (intro funas_term_subterm_atI, blast+)+
      have "(s |_ p, t |_ p) \<in> sig_step \<F> (rrstep \<R>)" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (metis poss_of_termE poss_of_term_replace_term_at rrstep.intros sig_stepI st(4))
      moreover have "(s |_ p, u |_ p) \<in> srstep \<F> \<R>" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (smt (verit, ccfv_threshold) a greater_eq_subt_at_replace less_eq_subt_at_replace pos_diff_append_itself
            pos_replace_to_rstep position_less_eq_def poss_append_poss replace_term_at_subt_at_id sig_stepI su(4))
      ultimately have "(t |_ p, u |_ p) \<in> (srstep \<F> \<R>)\<^sup>\<down>"
        using assms(1) by blast
      from sig_steps_join_ctxt_closed[OF fc this(1)]
      show ?thesis using a st(1) su(1) srstep_ctxt_closed[OF fc] unfolding st(4) su(4)
        by (auto simp: ctxt_of_pos_term_apply_replace_at_ident less_eq_subt_at_replace)
    next
      case b
      then have up: "q \<in> poss t" using st(1) su(1) unfolding st(4) su(4)
        by (metis pos_les_eq_append_diff pos_replace_at_pres poss_append_poss)
      let ?C = "ctxt_at_pos s q" have fc: "funas_ctxt ?C \<subseteq> \<F>" using funas(1) su(1)
        by (metis Un_subset_iff ctxt_at_pos_subt_at_id funas_ctxt_apply)
      from funas have funas: "funas_term (s |_ q) \<subseteq> \<F>" "funas_term (t |_ q) \<subseteq> \<F>" "funas_term (u |_ q) \<subseteq> \<F>"
        using su(1) pos_replace_at_pres[OF su(1)] up unfolding st(4) su(4)
        by (intro funas_term_subterm_atI, blast+)+
      have "(s |_ q, t |_ q) \<in> srstep \<F> \<R>" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (smt (verit, ccfv_SIG) b greater_eq_subt_at_replace less_eq_subt_at_replace pos_diff_append_itself
            pos_replace_to_rstep position_less_eq_def poss_append_poss replace_term_at_subt_at_id sig_stepI st(4))
      moreover have "(s |_ q, u |_ q) \<in> sig_step \<F> (rrstep \<R>)" unfolding st(4) su(4) using st(1 - 3) su(1 - 3) funas
        by (metis poss_of_termE poss_of_term_replace_term_at rrstep.intros sig_stepI su(4))
      ultimately have "(t |_ q, u |_ q) \<in> (srstep \<F> \<R>)\<^sup>\<down>"
        using assms(1) by blast
      from sig_steps_join_ctxt_closed[OF fc this(1)]
      show ?thesis using b st(1) su(1) srstep_ctxt_closed[OF fc] unfolding st(4) su(4)
        by (auto simp: ctxt_of_pos_term_apply_replace_at_ident less_eq_subt_at_replace)
    next
      case c
      define v where "v = t[q \<leftarrow> r2 \<cdot> \<sigma>2]"
      have funasv: "funas_term v \<subseteq> \<F>" using funas su(1) unfolding v_def su(4)
        using funas_term_replace_at_upper funas2 by blast
      from c have *: "v = u[p \<leftarrow> r \<cdot> \<sigma>]" unfolding v_def st(4) su(4) using st(1) su(1)
        using parallel_replace_term_commute by blast
      from c have "(t, v) \<in> rstep \<R>" unfolding st(4) v_def
        using su(1 - 3) par_pos_replace_pres[OF su(1)]
        by (metis par_pos_replace_term_at pos_replace_to_rstep position_par_def)
      moreover from c have "(u, v) \<in> rstep \<R>" unfolding su(4) *
        using st(1 - 3) par_pos_replace_pres[OF st(1)]
        by (metis par_pos_replace_term_at pos_replace_to_rstep)
      ultimately show ?thesis using funas(2-) funasv
        by auto
    qed}
  then show ?thesis unfolding WCR_on_def
    by blast
qed

end