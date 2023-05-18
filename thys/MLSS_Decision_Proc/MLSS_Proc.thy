theory MLSS_Proc                
  imports MLSS_Realisation MLSS_HF_Extras MLSS_Semantics MLSS_Typing
begin

section \<open>A Decision Procedure for MLSS\<close>
text \<open>
  This theory proves the soundness and completeness of the
  tableau calculus defined in \<^file>\<open>./MLSS_Calculus.thy\<close>
  It then lifts those properties to a recursive procedure
  that applies the rules of the calculus exhaustively.
  To obtain a decision procedure, we also prove termination.
\<close>

subsection \<open>Basic Definitions\<close>

definition "lin_sat b \<equiv> \<forall>b'. lexpands b' b \<longrightarrow> set b' \<subseteq> set b"

lemma lin_satD:
  assumes "lin_sat b"
  assumes "lexpands b' b"
  assumes "x \<in> set b'"
  shows "x \<in> set b"
  using assms unfolding lin_sat_def by auto

lemma not_lin_satD: "\<not> lin_sat b \<Longrightarrow> \<exists>b'. lexpands b' b \<and> set b \<subset> set (b' @ b)"
  unfolding lin_sat_def by auto

definition "sat b \<equiv> lin_sat b \<and> (\<nexists>bs'. bexpands bs' b)"

lemma satD:
  assumes "sat b"
  shows "lin_sat b" "\<nexists>bs'. bexpands bs' b"
  using assms unfolding sat_def by auto
                            
definition wits :: "'a branch \<Rightarrow> 'a set" where
  "wits b \<equiv> vars b - vars (last b)"

definition pwits :: "'a branch \<Rightarrow> 'a set" where
  "pwits b \<equiv> {c \<in> wits b. \<forall>t \<in> subterms (last b).
                  AT (Var c =\<^sub>s t) \<notin> set b \<and> AT (t =\<^sub>s Var c) \<notin> set b}"

lemma wits_singleton[simp]: "wits [\<phi>] = {}"
  unfolding wits_def vars_branch_simps by simp

lemma pwits_singleton[simp]: "pwits [\<phi>] = {}"
  unfolding pwits_def by auto

lemma pwitsD:
  assumes "c \<in> pwits b"
  shows "c \<in> wits b"
        "t \<in> subterms (last b) \<Longrightarrow> AT (Var c =\<^sub>s t) \<notin> set b"
        "t \<in> subterms (last b) \<Longrightarrow> AT (t =\<^sub>s Var c) \<notin> set b"
  using assms unfolding pwits_def by auto

lemma pwitsI:
  assumes "c \<in> wits b"
  assumes "\<And>t. t \<in> subterms (last b) \<Longrightarrow> AT (Var c =\<^sub>s t) \<notin> set b"
  assumes "\<And>t. t \<in> subterms (last b) \<Longrightarrow> AT (t =\<^sub>s Var c) \<notin> set b"
  shows "c \<in> pwits b"
  using assms unfolding pwits_def by blast

lemma finite_wits: "finite (wits b)"
  unfolding wits_def using finite_vars_branch by auto

lemma finite_pwits: "finite (pwits b)"
proof -
  have "pwits b \<subseteq> wits b"
    unfolding pwits_def by simp
  then show ?thesis using finite_wits finite_subset by blast
qed

lemma lexpands_subterms_branch_eq:
  "lexpands b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> subterms (b' @ b) = subterms b"
proof(induction rule: lexpands.induct)
  case (1 b' b)
  then show ?case
    apply(induction rule: lexpands_fm.induct)
         apply(auto simp: subterms_branch_def)
    done
next
  case (2 b' b)
  then show ?case
    apply(induction rule: lexpands_un.induct)
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_term_subterms_branch_trans
          dest: subterms_branchD AT_mem_subterms_branchD AF_mem_subterms_branchD)
    done
next
  case (3 b' b)
  then show ?case
    apply(induction rule: lexpands_int.induct)
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_term_subterms_branch_trans
          dest: subterms_branchD AT_mem_subterms_branchD AF_mem_subterms_branchD)
    done
next
  case (4 b' b)
  then show ?case
    apply(induction rule: lexpands_diff.induct)
    using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
         apply(auto simp: subterms_branch_simps 
          intro: subterms_term_subterms_branch_trans
          dest: subterms_branchD AT_mem_subterms_branchD AF_mem_subterms_branchD)
    done
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lexpands_single.induct)
    case (1 t1 b)
    then show ?case
      using subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]
      apply(auto simp: subterms_branch_simps
            dest: subterms_fmD intro: subterms_term_subterms_branch_trans)
      done
  qed (auto simp: subterms_branch_simps subterms_term_subterms_atom_Atom_trans
       dest: subterms_branchD AF_mem_subterms_branchD 
       intro: subterms_term_subterms_branch_trans)
next
  case (6 b' b)
  have *: "subterms_atom (subst_tlvl t1 t2 a) \<subseteq> subterms t2 \<union> subterms_atom a"
    for t1 t2 and a :: "'a pset_atom"
    by (cases "(t1, t2, a)" rule: subst_tlvl.cases) auto
  from 6 show ?case
  by (induction rule: lexpands_eq.induct)
     (auto simp: subterms_branch_def subterms_term_subterms_atom_Atom_trans
            dest!: subsetD[OF *])
qed

lemma lexpands_vars_branch_eq:
  "lexpands b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> vars (b' @ b) = vars b"
  using lexpands_subterms_branch_eq subterms_branch_eq_if_vars_branch_eq by metis

lemma bexpands_nowit_subterms_branch_eq:
  "bexpands_nowit bs' b \<Longrightarrow> b' \<in> bs' \<Longrightarrow> b \<noteq> [] \<Longrightarrow> subterms (b' @ b) = subterms b"
proof(induction rule: bexpands_nowit.induct)
  case (3 s t1 t2 b)
  then show ?case
    by (auto simp: subterms_term_subterms_atom_Atom_trans subterms_branch_simps)
next
  case (4 s t1 b t2)
  then show ?case
    using subterms_branch_subterms_subterms_fm_trans[OF _ _ "4"(2)]
    by (auto simp: subterms_term_subterms_atom_Atom_trans subterms_branch_simps)
next
  case (5 s t1 b t2)
  then show ?case
    using subterms_branch_subterms_subterms_fm_trans[OF _ _ "5"(2)]
    by (auto simp: subterms_term_subterms_atom_Atom_trans subterms_branch_simps)
qed (use subterms_branch_def in \<open>(fastforce simp: subterms_branch_simps)+\<close>)


lemma bexpands_nowit_vars_branch_eq:
  "bexpands_nowit bs' b \<Longrightarrow> b' \<in> bs' \<Longrightarrow> b \<noteq> [] \<Longrightarrow> vars (b' @ b) = vars b"
  using bexpands_nowit_subterms_branch_eq subterms_branch_eq_if_vars_branch_eq by metis

lemma lexpands_wits_eq:
  "lexpands b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> wits (b' @ b) = wits b"
  using lexpands_vars_branch_eq unfolding wits_def by force

lemma bexpands_nowit_wits_eq:
  assumes "bexpands_nowit bs' b" "b' \<in> bs'" "b \<noteq> []" 
  shows "wits (b' @ b) = wits b"
  using bexpands_nowit_vars_branch_eq[OF assms] assms(3)
  unfolding wits_def by simp

lemma bexpands_wit_vars_branch_eq:
  assumes "bexpands_wit t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  shows "vars (b' @ b) = insert x (vars b)"
  using assms bexpands_witD[OF assms(1)]
  by (auto simp: mem_vars_fm_if_mem_subterms_fm vars_branch_simps vars_fm_vars_branchI)

lemma bexpands_wit_wits_eq:
  assumes "bexpands_wit t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  shows "wits (b' @ b) = insert x (wits b)"
  using assms bexpands_witD[OF assms(1)]
  unfolding wits_def
  by (auto simp: mem_vars_fm_if_mem_subterms_fm vars_branch_simps vars_branch_def)

lemma lexpands_pwits_subs:
  assumes "lexpands b' b" "b \<noteq> []"
  shows "pwits (b' @ b) \<subseteq> pwits b"
  using assms lexpands_wits_eq[OF assms]
  by (induction rule: lexpands_induct) (auto simp: pwits_def)

subsubsection \<open>\<open>no_new_subterms\<close>\<close>

definition "no_new_subterms b \<equiv>
   \<forall>t \<in> subterms b. t \<notin> Var ` wits b \<longrightarrow> t \<in> subterms (last b)"

lemma no_new_subtermsI:
  assumes "\<And>t. t \<in> subterms b \<Longrightarrow> t \<notin> Var ` wits b \<Longrightarrow> t \<in> subterms (last b)"
  shows "no_new_subterms b"
  using assms unfolding no_new_subterms_def by blast

lemma Var_mem_subterms_branch_and_not_in_wits:
  assumes "Var v \<in> subterms b" "v \<notin> wits b"
  shows "v \<in> vars (last b)"
  using assms unfolding wits_def no_new_subterms_def
  by (auto simp: image_set_diff[unfolded inj_on_def] image_UN
                 Un_vars_term_subterms_branch_eq_vars_branch[symmetric])

lemma subterms_branch_cases:
  assumes "t \<in> subterms b" "t \<notin> Var ` wits b"
  obtains
    (Empty) n where "t = \<emptyset> n"
  | (Union) t1 t2 where "t = t1 \<squnion>\<^sub>s t2"
  | (Inter) t1 t2 where "t = t1 \<sqinter>\<^sub>s t2"
  | (Diff) t1 t2 where "t = t1 -\<^sub>s t2"
  | (Single) t1 where "t = Single t1"
  | (Var) v where "t = Var v" "v \<in> vars (last b)"
proof(cases t)
  case (Var x)
  with assms have "x \<in> vars (last b)"
    using Var_mem_subterms_branch_and_not_in_wits by (metis imageI)
  with Var that show ?thesis by blast
qed (use assms that in auto)

lemma no_new_subterms_casesI[case_names Empty Union Inter Diff Single]:
  assumes "\<And>n. \<emptyset> n \<in> subterms b \<Longrightarrow> \<emptyset> n \<in> subterms (last b)"
  assumes "\<And>t1 t2. t1 \<squnion>\<^sub>s t2 \<in> subterms b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms (last b)"
  assumes "\<And>t1 t2. t1 \<sqinter>\<^sub>s t2 \<in> subterms b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b)"
  assumes "\<And>t1 t2. t1 -\<^sub>s t2 \<in> subterms b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms (last b)"
  assumes "\<And>t. Single t \<in> subterms b \<Longrightarrow> Single t \<in> subterms (last b)"
  shows "no_new_subterms b"
proof(intro no_new_subtermsI)
  fix t assume "t \<in> subterms b" "t \<notin> Var ` wits b"
  with this assms show "t \<in> subterms (last b)"
    by (cases t rule: subterms_branch_cases) (auto simp: vars_fm_subs_subterms_fm)
qed

lemma no_new_subtermsD:
  assumes "no_new_subterms b"
  shows "\<And>n. \<emptyset> n \<in> subterms b \<Longrightarrow> \<emptyset> n \<in> subterms (last b)"
        "\<And>t1 t2. t1 \<squnion>\<^sub>s t2 \<in> subterms b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms (last b)"
        "\<And>t1 t2. t1 \<sqinter>\<^sub>s t2 \<in> subterms b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b)"
        "\<And>t1 t2. t1 -\<^sub>s t2 \<in> subterms b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms (last b)"
        "\<And>t. Single t \<in> subterms b \<Longrightarrow> Single t \<in> subterms (last b)"
  using assms unfolding no_new_subterms_def by auto

lemma lexpands_no_new_subterms:
  assumes "lexpands b' b" "b \<noteq> []"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms unfolding no_new_subterms_def
  by (simp add: lexpands_wits_eq lexpands_subterms_branch_eq[OF assms(1,2)])

lemma subterms_branch_subterms_atomI:
  assumes "Atom l \<in> set b" "t \<in> subterms_atom l"
  shows "t \<in> subterms_branch b"
  using assms unfolding subterms_branch_def  
  apply (cases l rule: subterms_atom.cases)
   apply (metis subterms_branch_def subterms_term_subterms_atom_Atom_trans subterms_refl)+
  done
  
lemma bexpands_nowit_no_new_subterms:
  assumes "bexpands_nowit bs' b" "b' \<in> bs'" "b \<noteq> []" 
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms unfolding no_new_subterms_def
  by (simp add: bexpands_nowit_wits_eq bexpands_nowit_subterms_branch_eq[OF assms(1,2)])

lemma bexpands_wit_no_new_subterms:
  assumes "bexpands_wit t1 t2 x bs' b" "b \<noteq> []" "b' \<in> bs'"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms
  apply(induction rule: bexpands_wit.induct)
  apply(auto simp: subterms_branch_simps
                   subterms_term_subterms_atom_trans subterms_term_subterms_fm_trans
             elim: no_new_subtermsD
             intro!: no_new_subterms_casesI)
  done

lemma bexpands_no_new_subterms:
  assumes "bexpands bs' b" "b \<noteq> []" "b' \<in> bs'"
  assumes "no_new_subterms b"
  shows "no_new_subterms (b' @ b)"
  using assms
  apply(cases rule: bexpands.cases)
  using bexpands_nowit_no_new_subterms bexpands_wit_no_new_subterms by metis+

lemma expandss_no_new_subterms:
  assumes "expandss b' b" "b \<noteq> []" "no_new_subterms b"
  shows "no_new_subterms b'"
  using assms
  apply(induction b' b rule: expandss.induct)
  using expandss_suffix suffix_bot.extremum_uniqueI
  using lexpands_no_new_subterms bexpands_no_new_subterms
  by blast+

lemmas subterms_branch_subterms_fm_lastI =
  subterms_branch_subterms_subterms_fm_trans[OF _ subterms_refl]


subsubsection \<open>\<open>wits_subterms\<close>\<close>

definition wits_subterms :: "'a branch \<Rightarrow> 'a pset_term set" where
  "wits_subterms b \<equiv> Var ` wits b \<union> subterms (last b)"

lemma subterms_branch_eq_if_no_new_subterms:
  assumes "no_new_subterms b" "b \<noteq> []"
  shows "subterms_branch b = wits_subterms b"
  using assms no_new_subtermsD[OF assms(1)]
proof -
  note simps = wits_def no_new_subterms_def wits_subterms_def
    subterms_branch_simps vars_branch_simps
  with assms show ?thesis
    by (auto simp: simps vars_fm_subs_subterms_fm
                   vars_branch_subs_subterms_branch[unfolded image_subset_iff]
             intro: subterms_branch_subterms_fm_lastI)
qed

lemma wits_subterms_last_disjnt: "Var ` wits b \<inter> subterms (last b) = {}"
  by (auto simp: wits_def intro!: mem_vars_fm_if_mem_subterms_fm)

subsection \<open>Completeness of the Calculus\<close>

subsubsection \<open>Proof of Lemma 2\<close>

fun is_literal :: "'a fm \<Rightarrow> bool" where
  "is_literal (Atom _) = True"
| "is_literal (Neg (Atom _)) = True"
| "is_literal _ = False"

lemma lexpands_no_wits_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {})"
  assumes "lexpands b' b" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-) lexpands_wits_eq[OF assms(2,3)]
  by (induction rule: lexpands_induct) (auto simp: disjoint_iff P_def)

lemma bexpands_nowit_no_wits_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {})"
  assumes "bexpands_nowit bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  by (induction rule: bexpands_nowit.induct)
     (auto simp: Int_def P_def wits_def vars_fm_vars_branchI)

lemma bexpands_wit_no_wits_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {})"
  assumes "bexpands_wit t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  by (induction rule: bexpands_wit.induct)
     (auto simp: Int_def P_def wits_def vars_fm_vars_branchI)

lemma bexpands_no_wits_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {})"
  assumes "bexpands bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  apply(cases bs' b rule: bexpands_cases)
  using bexpands_wit_no_wits_if_not_literal bexpands_nowit_no_wits_if_not_literal
  using P_def by fast+

lemma expandss_no_wits_if_not_literal:
  defines "P \<equiv> (\<lambda>b. \<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {})"
  assumes "expandss b' b" "b \<noteq> []"
  assumes "P b"
  shows "P b'"
  using assms(2-)
  apply (induction rule: expandss.induct)
  using lexpands_no_wits_if_not_literal bexpands_no_wits_if_not_literal
     apply (metis P_def expandss_suffix suffix_bot.extremum_uniqueI)+
  done

lemma lexpands_fm_pwits_eq:
  assumes "lexpands_fm b' b" "b \<noteq> []"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {}"
  shows "pwits (b' @ b) = pwits b"
  using assms
  apply(induction rule: lexpands_fm.induct)
       apply(fastforce simp: pwits_def wits_def vars_branch_def)+
  done

lemma lexpands_un_pwits_eq:
  assumes "lexpands_un b' b" "b \<noteq> []"
  assumes "\<forall>c \<in> pwits b. \<forall>t \<in> wits_subterms b.
    AT (Var c =\<^sub>s t) \<notin> set b \<and> AT (t =\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
  shows "pwits (b' @ b) = pwits b"
proof -
  note lexpands.intros(2)[OF assms(1)]
  note lexpands_wits_eq[OF this \<open>b \<noteq> []\<close>] 
  from assms this have "x \<in> pwits (b' @ b)" if "x \<in> pwits b" for x
    using that
    by (induction rule: lexpands_un.induct)
       (auto simp: wits_subterms_def pwitsD intro!: pwitsI)
  with lexpands_pwits_subs[OF \<open>lexpands b' b\<close> \<open>b \<noteq> []\<close>] show ?thesis
    by auto
qed

lemma lexpands_int_pwits_eq:
  assumes "lexpands_int b' b" "b \<noteq> []"
  assumes "\<forall>c \<in> pwits b. \<forall>t \<in> wits_subterms b.
    AT (Var c =\<^sub>s t) \<notin> set b \<and> AT (t =\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
  shows "pwits (b' @ b) = pwits b"
proof -
  note lexpands.intros(3)[OF assms(1)]
  note lexpands_wits_eq[OF this \<open>b \<noteq> []\<close>] 
  from assms this have "x \<in> pwits (b' @ b)" if "x \<in> pwits b" for x
    using that
    by (induction rule: lexpands_int.induct)
       (auto simp: wits_subterms_def pwitsD intro!: pwitsI)
  with lexpands_pwits_subs[OF \<open>lexpands b' b\<close> \<open>b \<noteq> []\<close>] show ?thesis
    by auto
qed

lemma lexpands_diff_pwits_eq:
  assumes "lexpands_diff b' b" "b \<noteq> []"
  assumes "\<forall>c \<in> pwits b. \<forall>t \<in> wits_subterms b.
    AT (Var c =\<^sub>s t) \<notin> set b \<and> AT (t =\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
  shows "pwits (b' @ b) = pwits b"
proof -
  note lexpands.intros(4)[OF assms(1)]
  note lexpands_wits_eq[OF this \<open>b \<noteq> []\<close>] 
  from assms this have "x \<in> pwits (b' @ b)" if "x \<in> pwits b" for x
    using that
    by (induction rule: lexpands_diff.induct)
       (auto simp: wits_subterms_def pwitsD intro!: pwitsI)
  with lexpands_pwits_subs[OF \<open>lexpands b' b\<close> \<open>b \<noteq> []\<close>] show ?thesis
    by auto
qed

lemma bexpands_nowit_pwits_eq:
  assumes "bexpands_nowit bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {}"
  shows "pwits (b' @ b) = pwits b"
  using assms
proof -
  from assms have "x \<in> pwits (b' @ b)" if "x \<in> pwits b" for x
    using that bexpands_nowit_wits_eq[OF assms(1-3)]
    by (induction rule: bexpands_nowit.induct)
       (intro pwitsI; fastforce simp: pwitsD)+
  moreover from assms have "pwits (b' @ b) \<subseteq> pwits b"
    unfolding pwits_def
    using bexpands_nowit_wits_eq by fastforce
  ultimately show ?thesis by blast
qed

lemma bexpands_wit_pwits_eq:
  assumes "bexpands_wit t1 t2 x bs' b" "b' \<in> bs'" "b \<noteq> []"
  shows "pwits (b' @ b) = insert x (pwits b)"
  using assms(2,3) bexpands_witD[OF assms(1)]
  unfolding pwits_def bexpands_wit_wits_eq[OF assms] 
  by (auto simp: vars_fm_vars_branchI)

lemma lemma_2_lexpands:
  defines "P \<equiv> (\<lambda>b c t. AT (Var c =\<^sub>s t) \<notin> set b \<and> AT (t =\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b)"
  assumes "lexpands b' b" "b \<noteq> []"
  assumes "no_new_subterms b"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {}"
  assumes "\<forall>c \<in> pwits b. \<forall>t \<in> wits_subterms b. P b c t"
  shows "\<forall>c \<in> pwits (b' @ b). \<forall>t \<in> wits_subterms (b' @ b). P (b' @ b) c t"
  using assms(2-6)
  using lexpands_wits_eq[OF assms(2,3)]
        lexpands_pwits_subs[OF assms(2,3)]
proof(induction rule: lexpands.induct)
  case (1 b' b)

  have "P (b' @ b) c t"
    if "\<forall>\<phi> \<in> set b'. vars \<phi> \<inter> wits (b' @ b) = {}"
    and "c \<in> pwits b" "t \<in> wits_subterms (b' @ b)" for c t
  proof -
    from that "1.prems"(5)
    have "\<forall>\<phi> \<in> set b'. \<phi> \<noteq> AT (Var c =\<^sub>s t) \<and> \<phi> \<noteq> AT (t =\<^sub>s Var c) \<and> \<phi> \<noteq> AT (t \<in>\<^sub>s Var c)"
      by (auto simp: pwits_def disjoint_iff)
    with 1 that show ?thesis
      unfolding P_def wits_subterms_def
      by (metis Un_iff last_appendR set_append)
  qed
  moreover from "1"(1,4,6) have "\<forall>\<phi> \<in> set b'. vars \<phi> \<inter> wits (b' @ b) = {}"
    by (induction rule: lexpands_fm.induct) (auto simp: disjoint_iff)
  ultimately show ?case
    using 1 lexpands_fm_pwits_eq by blast
next
  case (2 b' b)
  then show ?case
    using lexpands_un_pwits_eq[OF "2"(1,2,5)[unfolded P_def]]
  proof(induction rule: lexpands_un.induct)
    case (4 s t1 t2 b)
    then have "t1 \<squnion>\<^sub>s t2 \<in> subterms b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 \<squnion>\<^sub>s t2 \<in> subterms (last b)"
      using no_new_subtermsD by blast
    then have "t1 \<notin> Var ` wits b" "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      by (auto simp: wits_subterms_def P_def subterms_branch_simps pwitsD(1))
  next
    case (5 s t1 t2 b)
    then have "t1 \<squnion>\<^sub>s t2 \<in> subterms b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 \<squnion>\<^sub>s t2 \<in> subterms (last b)"
      using no_new_subtermsD by blast
    then have "t1 \<notin> Var ` wits b" "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 5 show ?case
      by (auto simp: wits_subterms_def P_def subterms_branch_simps pwitsD(1))
  qed (auto simp: wits_subterms_def P_def)
next
  case (3 b' b)
  then show ?case
    using lexpands_int_pwits_eq[OF "3"(1,2,5)[unfolded P_def]]
  proof(induction rule: lexpands_int.induct)
    case (1 s t1 t2 b)
    then have "t1 \<sqinter>\<^sub>s t2 \<in> subterms b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b)"
      using no_new_subtermsD by blast
    then have "t1 \<notin> Var ` wits b" "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 1 show ?case
      by (auto simp: wits_subterms_def P_def subterms_branch_simps pwitsD(1))
  next
    case (6 s t1 b t2)
    then have "t1 \<notin> Var ` wits b" "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 6 show ?case
      by (auto simp: wits_subterms_def P_def subterms_branch_simps pwitsD(1))
  qed (auto simp: wits_subterms_def P_def)
next
  case (4 b' b)
  then show ?case
    using lexpands_diff_pwits_eq[OF "4"(1,2,5)[unfolded P_def]]
  proof(induction rule: lexpands_diff.induct)
    case (1 s t1 t2 b)
    then have "t1 -\<^sub>s t2 \<in> subterms b"
      unfolding subterms_branch_def
      by (metis UN_iff UnI2 subterms_fm_simps(1) subterms_atom.simps(1) subterms_refl)
    with \<open>no_new_subterms b\<close> have "t1 -\<^sub>s t2 \<in> subterms (last b)"
      using no_new_subtermsD by blast
    then have "t1 \<notin> Var ` wits b" "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 1 show ?case
      by (auto simp: wits_subterms_def P_def subterms_branch_simps dest: pwitsD(1))
  next
    case (4 s t1 t2 b)
    then have "t1 -\<^sub>s t2 \<in> subterms b"
      unfolding subterms_branch_def
      by (metis AF_mem_subterms_branchD(2) subterms_branch_def)
    with \<open>no_new_subterms b\<close> have "t1 -\<^sub>s t2 \<in> subterms (last b)"
      using no_new_subtermsD by blast
    then have "t1 \<notin> Var ` wits b" "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      by (auto simp: wits_subterms_def P_def subterms_branch_simps dest: pwitsD(1))
  qed (auto simp: wits_subterms_def P_def)
next
  case (5 b' b)
  then show ?case
  proof(induction rule: lexpands_single.induct)
    case (2 s t b)
    then have "Single t \<in> subterms b"
      by (auto intro: subterms_branch_subterms_atomI)
    with 2 have "t \<in> subterms (last b)"
      by (metis subterms_fmD(7) no_new_subtermsD(5))
    then have "\<forall>c \<in> pwits b. Var c \<noteq> t"
      unfolding pwits_def wits_def
      using wits_def wits_subterms_last_disjnt by fastforce
    with \<open>t \<in> subterms (last b)\<close> show ?case
      using 2
      unfolding P_def
      by (auto simp: wits_subterms_last_disjnt[unfolded disjoint_iff] wits_subterms_def subsetD
               dest: pwitsD(2))
  qed (auto simp: wits_subterms_def P_def)
next
  case (6 b' b)
  then have "no_new_subterms (b' @ b)" "b' @ b \<noteq> []"
    using lexpands_no_new_subterms[OF lexpands.intros(6)] by blast+
  note subterms_branch_eq_if_no_new_subterms[OF this]
  with 6 show ?case
  proof(induction rule: lexpands_eq_induct')
    case (subst t1 t2 t1' t2' p l b)
    then have "t1' \<in> subterms b"
      using AT_eq_subterms_branchD by blast
    then show ?case unfolding P_def
    proof(safe, goal_cases)
      case (1 c x)
      with subst have [simp]: "p"
        by (cases p) (simp add: P_def wits_subterms_def; blast)+
      from 1 subst have "(Var c =\<^sub>s x) = subst_tlvl t1' t2' l"
        by (simp add: P_def wits_subterms_def; blast)
      with 1 subst consider
        (refl) "l = (t1' =\<^sub>s t1')" "t2' = Var c" "x = Var c"
        | (t1'_left) "l = (Var c =\<^sub>s t1')" "t2' = x"
        | (t1'_right) "l = (t1' =\<^sub>s x)" "t2' = Var c"
        apply(cases "(t1', t2', l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        by (use 1 subst subterms_branch_eq_if_no_new_subterms in \<open>(simp add: P_def; blast)+\<close>)
    next
      case (2 c x)
      with subst have [simp]: "p"
        by (cases p) (simp add: P_def wits_subterms_def; blast)+
      from 2 subst have "(x =\<^sub>s Var c) = subst_tlvl t1' t2' l"
        by (simp add: P_def wits_subterms_def; blast)
      with 2 subst consider
        (refl) "l = (t1' =\<^sub>s t1')" "t2' = Var c" "x = Var c"
        | (t1_left) "l = (t1' =\<^sub>s Var c)" "t2' = x"
        | (t1_right) "l = (x =\<^sub>s t1')" "t2' = Var c"
        apply(cases "(t1', t2', l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        by (use 2 subst subterms_branch_eq_if_no_new_subterms in \<open>(simp add: P_def; blast)+\<close>)
    next
      case (3 c x)
      with subst have [simp]: "p"
        by (cases p) (simp add: P_def wits_subterms_def; blast)+
      from 3 subst have "(x \<in>\<^sub>s Var c) = subst_tlvl t1' t2' l"
        by (simp add: P_def wits_subterms_def; blast)
      with 3 subst consider
        (refl) "l = (t1' \<in>\<^sub>s t1')" "t2' = Var c" "x = Var c"
        | (t1_left) "l = (t1' \<in>\<^sub>s Var c)" "t2' = x"
        | (t1_right) "l = (x \<in>\<^sub>s t1')" "t2' = Var c"
        apply(cases "(t1', t2', l)" rule: subst_tlvl.cases)
        by (auto split: if_splits)
      then show ?case
        apply(cases)
        by (use 3 subst subterms_branch_eq_if_no_new_subterms in \<open>(simp add: P_def; blast)+\<close>)
    qed
  next
    case (neq s t s' b)
    then show ?case
      using P_def by (simp add: wits_subterms_def) blast
  qed
qed

lemma lemma_2_bexpands:
  defines "P \<equiv> (\<lambda>b c t. AT (Var c =\<^sub>s t) \<notin> set b \<and> AT (t =\<^sub>s Var c) \<notin> set b
                      \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b)"
  assumes "bexpands bs' b" "b' \<in> bs'" "b \<noteq> []"
  assumes "no_new_subterms b"
  assumes "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {}"
  assumes "\<forall>c \<in> pwits b. \<forall>t \<in> wits_subterms b. P b c t"
  shows "\<forall>c \<in> pwits (b' @ b). \<forall>t \<in> wits_subterms (b' @ b). P (b' @ b) c t"
  using assms(2-) bexpands_no_new_subterms[OF assms(2,4,3,5)]
proof(induction rule: bexpands.induct)
  case (1 bs' b)
  then show ?case
    using bexpands_nowit_wits_eq[OF "1"(1-3)] bexpands_nowit_pwits_eq[OF "1"(1-3,5)]
  proof(induction rule: bexpands_nowit.induct)
    case (1 p q b)
    then show ?case
      unfolding P_def wits_subterms_def
      by (fastforce dest: pwitsD)
  next
    case (2 p q b)
    then show ?case
      unfolding P_def wits_subterms_def
      by (fastforce dest: pwitsD)
  next
    case (3 s t1 t2 b)
    then have "t1 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 3 show ?case
      unfolding P_def wits_subterms_def
      by (fastforce simp: vars_branch_simps dest: pwitsD)
  next
    case (4 s t1 b t2)
    then have "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 4 show ?case
      unfolding P_def wits_subterms_def
      by (fastforce simp: vars_branch_simps dest: pwitsD)
  next
    case (5 s t1 b t2)
    then have "t2 \<notin> Var ` wits b"
      by (meson disjoint_iff wits_subterms_last_disjnt subterms_fmD)+
    with 5 show ?case
      unfolding P_def wits_subterms_def
      by (fastforce simp: vars_branch_simps dest: pwitsD)
  qed
next
  case (2 t1 t2 x bs b)
  from bexpands_witD[OF "2"(1)] have "t1 \<notin> Var ` wits b" "t2 \<notin> Var ` wits b"
    by (meson disjoint_iff_not_equal wits_subterms_last_disjnt)+
  then have not_in_pwits: "t1 \<notin> Var ` pwits b" "t2 \<notin> Var ` pwits b"
    unfolding pwits_def by auto
  with bexpands_witD[OF "2"(1)] "2"(2-) show ?case
    unfolding P_def wits_subterms_def
    unfolding bexpands_wit_pwits_eq[OF "2"(1-3)] bexpands_wit_wits_eq[OF "2"(1-3)]
    by safe (auto simp: vars_fm_vars_branchI[where ?x=x and ?b=b])
qed

lemma subterms_branch_eq_if_wf_branch:
  assumes "wf_branch b"
  shows "subterms_branch b = wits_subterms b"
proof -
  from assms obtain \<phi> where "expandss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have "no_new_subterms [\<phi>]"
    unfolding no_new_subterms_def wits_def
    by (simp add: subterms_branch_simps)
  with \<open>expandss b [\<phi>]\<close> have "no_new_subterms b"
    using expandss_no_new_subterms by blast
  with \<open>expandss b [\<phi>]\<close> assms show ?thesis
    by (intro subterms_branch_eq_if_no_new_subterms) simp_all
qed

lemma
  assumes "wf_branch b"
  shows no_new_subterms_if_wf_branch: "no_new_subterms b"
    and no_wits_if_not_literal_if_wf_branch:
          "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {}"
proof -
  from assms obtain \<phi> where "expandss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have "no_new_subterms [\<phi>]"
    by (auto simp: no_new_subterms_def wits_def vars_branch_simps subterms_branch_simps)
  from expandss_no_new_subterms[OF \<open>expandss b [\<phi>]\<close> _ this] show "no_new_subterms b"
    by simp
  from expandss_no_wits_if_not_literal[OF \<open>expandss b [\<phi>]\<close>]
  show "\<forall>\<phi> \<in> set b. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b = {}"
    unfolding wits_def by simp
qed

lemma lemma_2:
  assumes "wf_branch b"
  assumes "c \<in> pwits b"
  shows "AT (Var c =\<^sub>s t) \<notin> set b" "AT (t =\<^sub>s Var c) \<notin> set b" "AT (t \<in>\<^sub>s Var c) \<notin> set b"
proof -
  from \<open>wf_branch b\<close> obtain \<phi> where "expandss b [\<phi>]"
    using wf_branch_def by blast
  have no_wits_if_not_literal: "\<forall>\<phi> \<in> set b'. \<not> is_literal \<phi> \<longrightarrow> vars \<phi> \<inter> wits b' = {}"
    if "expandss b' [\<phi>]" for b'
    using no_wits_if_not_literal_if_wf_branch that unfolding wf_branch_def by blast
  have no_new_subterms: "no_new_subterms b'" if "expandss b' [\<phi>]" for b'
    using no_new_subterms_if_wf_branch that unfolding wf_branch_def by blast
  have "AT (Var c =\<^sub>s t) \<notin> set b \<and> AT (t =\<^sub>s Var c) \<notin> set b \<and> AT (t \<in>\<^sub>s Var c) \<notin> set b"
    using \<open>expandss b [\<phi>]\<close> assms(2)
  proof(induction b "[\<phi>]" arbitrary: c t rule: expandss.induct)
    case 1
    then show ?case by simp
  next
    case (2 b1 b2)
    note lemma_2_lexpands[OF this(1) _
        no_new_subterms[OF this(3)] no_wits_if_not_literal[OF this(3)]]
    with 2 show ?case
      using wf_branch_def wf_branch_not_Nil subterms_branch_eq_if_wf_branch
      by (metis AT_eq_subterms_branchD(1,2) AT_mem_subterms_branchD(1) expandss.intros(2))
  next
    case (3 bs b2 b1)
    note lemma_2_bexpands[OF "3"(1) _ _
        no_new_subterms[OF "3"(3)] no_wits_if_not_literal[OF "3"(3)]]
    with 3 show ?case
      using wf_branch_def wf_branch_not_Nil subterms_branch_eq_if_wf_branch
      by (metis AT_eq_subterms_branchD(1,2) AT_mem_subterms_branchD(1) expandss.intros(3))
  qed
  then show "AT (Var c =\<^sub>s t) \<notin> set b" "AT (t =\<^sub>s Var c) \<notin> set b" "AT (t \<in>\<^sub>s Var c) \<notin> set b"
    by safe
qed

subsubsection \<open>Urelements\<close>
  
definition "urelems b \<equiv> {x \<in> subterms b. \<exists>v. \<forall>\<phi> \<in> set b. urelem' v \<phi> x}"

lemma finite_urelems: "finite (urelems b)"
proof -
  have "urelems b \<subseteq> subterms b"
    unfolding urelems_def urelem_def by blast
  with finite_subset finite_subterms_branch show ?thesis
    by blast
qed

lemma urelems_subs_subterms: "urelems b \<subseteq> subterms b"
  unfolding urelems_def by blast

lemma is_Var_if_mem_urelems: "t \<in> urelems b \<Longrightarrow> is_Var t"
  unfolding urelems_def subterms_branch_def
  using is_Var_if_urelem' by auto

lemma urelems_subs_vars: "urelems b \<subseteq> Var ` vars b"
proof
  fix t assume "t \<in> urelems b"
  with urelems_subs_subterms have "t \<in> subterms b"
    by blast
  moreover note is_Var_if_mem_urelems[OF \<open>t \<in> urelems b\<close>]
  then obtain x where "t = Var x"
    by (meson is_Var_def)
  ultimately have "x \<in> vars b"
    unfolding Un_vars_term_subterms_branch_eq_vars_branch[symmetric]
    by force
  with \<open>t = Var x\<close> show "t \<in> Var ` vars b"
    by blast
qed

lemma types_term_inf:
  includes Set_member_no_ascii_notation
  assumes "v1 \<turnstile> t : l1" "v2 \<turnstile> t : l2"
  shows "inf v1 v2 \<turnstile> t : inf l1 l2"
  using assms
  apply(induction t arbitrary: l1 l2)
       apply(auto simp: inf_min elim!: types_pset_term_cases
                  intro: types_pset_term_intros' types_pset_term.intros(4-))
  done

lemma types_pset_atom_inf:
  fixes a :: "'a pset_atom"
  assumes "v1 \<turnstile> a" "v2 \<turnstile> a"
  shows "inf v1 v2 \<turnstile> a"
  using assms
  by (auto simp: types_pset_atom.simps) (metis inf_min min_Suc_Suc types_term_inf)+

lemma types_pset_fm_inf:
  fixes \<phi> :: "'a pset_fm"
  assumes "v1 \<turnstile> \<phi>" "v2 \<turnstile> \<phi>"
  shows "inf v1 v2 \<turnstile> \<phi>"
  using assms types_pset_atom_inf
  unfolding types_pset_fm_def by blast

lemma types_urelems:
  includes Set_member_no_ascii_notation
  fixes b :: "'a branch"
  assumes "wf_branch b" "v \<turnstile> last b"
  obtains v' where "\<forall>\<phi> \<in> set b. v' \<turnstile> \<phi>" "\<forall>u \<in> urelems b. v' \<turnstile> u : 0"
proof -
  from assms have "expandss b [last b]"
    unfolding wf_branch_def by force

  define V where "V \<equiv> {v. (\<forall>\<phi> \<in> set b. v \<turnstile> \<phi>) \<and> (\<forall>x. x \<notin> vars b \<longrightarrow> v x = 0)}"
  have "V \<noteq> {}"
  proof -
    from types_expandss[OF \<open>expandss b [last b]\<close>, simplified] \<open>v \<turnstile> last b\<close>
    obtain v where v: "\<forall>\<phi> \<in> set b. v \<turnstile> \<phi>"
      unfolding vars_branch_simps by metis
    define v' where "v' \<equiv> \<lambda>x. if x \<in> vars b then v x else 0"
    have "v' \<turnstile> \<phi> \<longleftrightarrow> v \<turnstile> \<phi>" if "\<phi> \<in> set b" for \<phi> :: "'a pset_fm"
      apply(intro types_pset_fm_if_on_vars_eq)
      using that vars_fm_vars_branchI unfolding v'_def by metis
    with v have "\<forall>\<phi> \<in> set b. v' \<turnstile> \<phi>"
      by blast
    then have "v' \<in> V"
      unfolding V_def v'_def by simp
    then show ?thesis
      by blast
  qed
    
  define m_x where "m_x \<equiv> \<lambda>x. ARG_MIN (\<lambda>v. v x) v. v \<in> V"
  with \<open>V \<noteq> {}\<close> have m_x: "\<forall>v \<in> V. m_x x x \<le> v x" "m_x x \<in> V" for x
    using arg_min_nat_le arg_min_natI by (metis ex_in_conv)+

  define M where "M \<equiv> Finite_Set.fold inf (SOME v. v \<in> V) (m_x ` vars b)"
  note finite_imageI[where ?h=m_x, OF finite_vars_branch[of b]]
  note M_inf_eq = Inf_fin.eq_fold[symmetric, OF this, of "SOME v. v \<in> V"]
  have M_leq: "M x \<le> v x" if "x \<in> vars b" "v \<in> V" for x v
  proof -
    from that have "m_x x \<in> m_x ` vars b"
      by blast
    then have "M = inf (m_x x) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n insert (SOME v. v \<in> V) (m_x ` vars b))"
      unfolding M_def M_inf_eq
      by (simp add: Inf_fin.in_idem finite_vars_branch)
    with m_x that show ?thesis
      by (simp add: inf.coboundedI1)
  qed
  moreover have "M \<in> V"
    unfolding M_def M_inf_eq using finite_vars_branch[of b]
  proof(induction rule: finite_induct)
    case empty
    with \<open>V \<noteq> {}\<close> show ?case
      by (simp add: some_in_eq)
  next
    case (insert x F)
    then have M'_eq: "\<Sqinter>\<^sub>f\<^sub>i\<^sub>n insert (SOME v. v \<in> V) (m_x ` insert x F)
      = inf (m_x x) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n insert (SOME v. v \<in> V) (m_x ` F))" (is "_ = ?M'")
      by (simp add: insert_commute)
    from types_pset_fm_inf insert have "\<forall>\<phi> \<in> set b. ?M' \<turnstile> \<phi>"
      using V_def m_x(2) by blast
    moreover have "(inf w v) x = 0" if "x \<notin> vars b" "w \<in> V" "v \<in> V" for w v
      using that by (simp add: V_def)
    with "insert.IH" m_x(2) have "\<forall>x. x \<notin> vars b \<longrightarrow> ?M' x = 0"
      by (simp add: V_def)
    ultimately have "?M' \<in> V"
      using V_def by blast
    with M'_eq show ?case
      by metis
  qed
  moreover have "M \<turnstile> u : 0" if "u \<in> urelems b" for u
  proof -
    from that obtain v where v: "\<forall>\<phi> \<in> set b. urelem' v \<phi> u"
      unfolding urelems_def by blast
    define v' where "v' \<equiv> \<lambda>x. if x \<in> vars b then v x else 0"
    have "v' \<turnstile> \<phi> \<longleftrightarrow> v \<turnstile> \<phi>" if "\<phi> \<in> set b" for \<phi> :: "'a pset_fm"
      apply(intro types_pset_fm_if_on_vars_eq)
      using that vars_fm_vars_branchI unfolding v'_def by metis
    with v have "\<forall>\<phi> \<in> set b. v' \<turnstile> \<phi>"
      by blast
    then have "v' \<in> V"
      unfolding V_def v'_def by auto
    moreover obtain uv where uv: "u = Var uv"
      using v is_Var_if_urelem' wf_branch_not_Nil[OF \<open>wf_branch b\<close>]
      by (metis is_Var_def last_in_set)
    then have "v' \<turnstile> u : 0"
      using v  wf_branch_not_Nil[OF \<open>wf_branch b\<close>, THEN last_in_set]
      unfolding v'_def
      by (auto elim!: types_pset_term_cases(2) intro!: types_pset_term_intros'(2))
    ultimately show "M \<turnstile> u : 0"
      using M_leq[where ?v=v'] \<open>M \<in> V\<close>[unfolded V_def] unfolding uv
      by (fastforce elim!: types_pset_term_cases(2) intro!: types_pset_term_intros'(2))
  qed
  ultimately show ?thesis
    using that unfolding V_def by auto
qed

lemma mem_urelems_if_urelem_last:
  assumes "wf_branch b"
  assumes "urelem (last b) x" "x \<in> subterms (last b)"
  shows "x \<in> urelems b"
proof -
  from assms have "x \<in> subterms b"
    unfolding subterms_branch_def by auto
  moreover note urelem_invar_if_wf_branch[OF assms]
  ultimately show ?thesis
    unfolding urelems_def urelem_def by blast
qed

lemma not_urelem_comps_if_compound:
  assumes "f t1 t2 \<in> subterms b" "f \<in> {(\<sqinter>\<^sub>s), (\<squnion>\<^sub>s), (-\<^sub>s)}"
  shows "t1 \<notin> urelems b" "t2 \<notin> urelems b"
proof -
  from assms obtain \<phi> where "\<phi> \<in> set b" "f t1 t2 \<in> subterms \<phi>"
    unfolding subterms_branch_def by auto
  note not_urelem_comps_if_compound[of f t1 t2, OF this(2) assms(2)]
  with \<open>\<phi> \<in> set b\<close> show "t1 \<notin> urelems b" "t2 \<notin> urelems b"
    unfolding urelems_def urelem_def by auto
qed

subsubsection \<open>Realization of an Open Branch\<close>

definition "base_vars b \<equiv> Var ` pwits b \<union> urelems b"

lemma finite_base_vars: "finite (base_vars b)"
  unfolding base_vars_def finite_Un
  using finite_pwits[THEN finite_imageI] finite_urelems by blast

lemma pwits_subs_base_vars:
  shows "Var ` pwits b \<subseteq> base_vars b"
  unfolding base_vars_def
  by blast

lemma base_vars_subs_vars: "base_vars b \<subseteq> Var ` vars b"
  unfolding base_vars_def pwits_def wits_def
  using urelems_subs_vars by blast

definition subterms' :: "'a branch \<Rightarrow> 'a pset_term set" where
  "subterms' b \<equiv> subterms b - base_vars b"

definition bgraph :: "'a branch \<Rightarrow> ('a pset_term, 'a pset_term \<times> 'a pset_term) pre_digraph" where
  "bgraph b \<equiv>
    let
      vs = base_vars b \<union> subterms' b
    in
      \<lparr> verts = vs,
        arcs = {(s, t). AT (s \<in>\<^sub>s t) \<in> set b},
        tail = fst,
        head = snd \<rparr>"

lemma base_vars_Un_subterms'_eq_subterms:
  "base_vars b \<union> subterms' b = subterms b"
  unfolding subterms'_def
  using base_vars_subs_vars vars_branch_subs_subterms_branch by fastforce

lemma finite_base_vars_Un_subterms': "finite (base_vars b \<union> subterms' b)"
  unfolding base_vars_Un_subterms'_eq_subterms
  using finite_subterms_branch .

lemma verts_bgraph: "verts (bgraph b) = base_vars b \<union> subterms' b"
  unfolding bgraph_def Let_def by simp

lemma verts_bgraph_eq_subterms: "verts (bgraph b) = subterms b"
  unfolding verts_bgraph base_vars_Un_subterms'_eq_subterms ..

lemma finite_subterms': "finite (subterms' b)"
  unfolding subterms'_def using finite_base_vars finite_subterms_branch
  by auto

lemma base_vars_subterms'_disjnt: "base_vars b \<inter> subterms' b = {}"
  unfolding subterms'_def by fastforce

lemma wits_subterms_eq_base_vars_Un_subterms':
  assumes "wf_branch b"
  shows "wits_subterms b = base_vars b \<union> subterms' b"
  unfolding subterms_branch_eq_if_wf_branch[OF assms, symmetric] subterms'_def
  using base_vars_subs_vars vars_branch_subs_subterms_branch
  by fastforce

lemma in_subterms'_if_AT_mem_in_branch:
  assumes "wf_branch b"
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> base_vars b \<union> subterms' b"
    and "t \<in> base_vars b \<union> subterms' b"
  using assms
  using wits_subterms_eq_base_vars_Un_subterms' AT_mem_subterms_branchD
  using subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms'_if_AF_mem_in_branch:
  assumes "wf_branch b"
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> base_vars b \<union> subterms' b"
    and "t \<in> base_vars b \<union> subterms' b"
  using assms
  using wits_subterms_eq_base_vars_Un_subterms' AF_mem_subterms_branchD
  using subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms'_if_AT_eq_in_branch:
  assumes "wf_branch b"
  assumes "AT (s =\<^sub>s t) \<in> set b"
  shows "s \<in> base_vars b \<union> subterms' b"
    and "t \<in> base_vars b \<union> subterms' b"
  using assms
  using wits_subterms_eq_base_vars_Un_subterms' AT_eq_subterms_branchD
  using subterms_branch_eq_if_wf_branch
  by blast+

lemma in_subterms'_if_AF_eq_in_branch:
  assumes "wf_branch b"
  assumes "AF (s =\<^sub>s t) \<in> set b"
  shows "s \<in> base_vars b \<union> subterms' b"
    and "t \<in> base_vars b \<union> subterms' b"
  using assms
  using wits_subterms_eq_base_vars_Un_subterms' AF_eq_subterms_branchD
  using subterms_branch_eq_if_wf_branch
  by blast+

lemma mem_subterms_fm_last_if_mem_subterms_branch:
  assumes "wf_branch b"
  assumes "t \<in> subterms b" "\<not> is_Var t"
  shows "t \<in> subterms (last b)"
  using assms
  unfolding subterms_branch_eq_if_wf_branch[OF \<open>wf_branch b\<close>]
  unfolding subterms'_def wits_subterms_def by force

locale open_branch =
  fixes b :: "'a branch"
  assumes wf_branch: "wf_branch b" and bopen: "bopen b" and types: "\<exists>v. v \<turnstile> last b"
      and infinite_vars: "infinite (UNIV :: 'a set)"
begin

sublocale fin_digraph_bgraph: fin_digraph "bgraph b"
proof
  show "finite (verts (bgraph b))"
    using finite_base_vars finite_subterms'
    by (auto simp: bgraph_def Let_def)

  show "finite (arcs (bgraph b))"
    using [[simproc add: finite_Collect]]
    by (auto simp: bgraph_def Let_def inj_on_def intro!: finite_vimageI)

qed (use in_subterms'_if_AT_mem_in_branch[OF wf_branch]
      in \<open>(fastforce simp: bgraph_def Let_def)+\<close>)

lemma member_seq_if_cas:
  "fin_digraph_bgraph.cas t1 is t2
  \<Longrightarrow> member_seq t1 (map (\<lambda>e. tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e) is) t2"
  by (induction "is" arbitrary: t1 t2) auto

lemma member_cycle_if_cycle:
  "fin_digraph_bgraph.cycle c
  \<Longrightarrow> member_cycle (map (\<lambda>e. tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e) c)"
  unfolding pre_digraph.cycle_def
  by (cases c) (auto simp: member_seq_if_cas)

sublocale dag_bgraph: dag "bgraph b"
proof(unfold_locales, goal_cases)
  case (1 e)
  show ?case
  proof
    assume "tail (bgraph b) e = head (bgraph b) e"
    then obtain t where "AT (t \<in>\<^sub>s t) \<in> set b"
      using 1 unfolding bgraph_def Let_def by auto
    then have "member_cycle [(t \<in>\<^sub>s t)]" "(t \<in>\<^sub>s t) \<in> Atoms (set b)"
      by (auto simp: Atoms_def)
    then have "bclosed b"
      using memberCycle by (metis empty_iff empty_set set_ConsD subsetI)
    with bopen show "False"
      by blast
  qed
next
  case (2 e1 e2)
  then show ?case
    by (auto simp: bgraph_def Let_def arc_to_ends_def)
next
  case 3
  show ?case
  proof
    assume "\<exists>c. fin_digraph_bgraph.cycle c"
    then obtain c where "fin_digraph_bgraph.cycle c"
      by blast
    then have "member_cycle (map (\<lambda>e. (tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e)) c)"
      using member_cycle_if_cycle by blast
    moreover
    from \<open>fin_digraph_bgraph.cycle c\<close> have "set c \<subseteq> arcs (bgraph b)"
      by (meson fin_digraph_bgraph.cycle_def pre_digraph.awalk_def)
    then have "set (map (\<lambda>e. (tail (bgraph b) e \<in>\<^sub>s head (bgraph b) e)) c) \<subseteq> Atoms (set b)"
      unfolding bgraph_def Let_def Atoms_def by auto
    ultimately have "bclosed b"
      using memberCycle by blast
    with bopen show False by blast
  qed
qed

definition I :: "'a pset_term \<Rightarrow> hf" where
  "I \<equiv> SOME f. inj_on f (subterms b)
             \<and> (\<forall>p. hcard (f p) > 2 * card (base_vars b \<union> subterms' b))"


lemma (in -) Ex_set_family:
  assumes "finite P"
  shows "\<exists>I. inj_on I P \<and> (\<forall>p. hcard (I p) \<ge> n)"
proof -
  from \<open>finite P\<close> obtain ip where ip: "bij_betw ip P {..<card P}"
    using to_nat_on_finite by blast
  let ?I = "ord_of o ((+) n) o ip"
  from ip have "inj_on ?I P"
    by (auto simp: inj_on_def bij_betw_def)
  moreover have "hcard (?I p) \<ge> n" for p
    by simp
  ultimately show ?thesis
    by auto
qed

lemma
  shows inj_on_I: "inj_on I (subterms b)"
    and card_I: "hcard (I p) > 2 * card (base_vars b \<union> subterms' b)"
proof -
  have "\<exists>f. inj_on f (subterms b)
    \<and> (\<forall>p. hcard (f p) > 2 * card (base_vars b \<union> subterms' b))"
    using Ex_set_family finite_subterms_branch by (metis less_eq_Suc_le)
  from someI_ex[OF this]
  show "inj_on I (subterms b)"
       "hcard (I p) > 2 * card (base_vars b \<union> subterms' b)"
    unfolding I_def by blast+
qed

lemma
  shows inj_on_base_vars_I: "inj_on I (base_vars b)"
    and inj_on_subterms'_I: "inj_on I (subterms' b)"
proof -
  from base_vars_Un_subterms'_eq_subterms have
    "base_vars b \<subseteq> subterms b" "subterms' b \<subseteq> subterms b"
    using wf_branch_not_Nil[OF wf_branch] by blast+
  with inj_on_I show "inj_on I (base_vars b)" "inj_on I (subterms' b)"
    unfolding inj_on_def by blast+
qed

definition "eq \<equiv> symcl ({(s, t). AT (s =\<^sub>s t) \<in> set b}\<^sup>=)"

lemma refl_eq: "refl eq"
  unfolding eq_def symcl_def refl_on_def by auto

lemma trans_eq:
  assumes "lin_sat b" shows "trans eq"
proof
  fix s t u assume assms: "(s, t) \<in> eq" "(t, u) \<in> eq"
  have "(s, u) \<in> eq" if "s \<noteq> t" "t \<noteq> u"
  proof -
    from that assms have
      s_t: "AT (s =\<^sub>s t) \<in> set b \<or> AT (t =\<^sub>s s) \<in> set b" and
      t_u: "AT (t =\<^sub>s u) \<in> set b \<or> AT (u =\<^sub>s t) \<in> set b"
      unfolding eq_def symcl_def by fastforce+
    note intros = lexpands_eq.intros(1,3)[
        THEN lexpands.intros(6), THEN \<open>lin_sat b\<close>[THEN lin_satD]]
    note intros' = intros[where ?x="AT (s =\<^sub>s u)"] intros[where ?x="AT (u =\<^sub>s s)"]
    from s_t t_u that have "AT (s =\<^sub>s u) \<in> set b \<or> AT (u =\<^sub>s s) \<in> set b"
      by safe (simp_all add: intros')
    then show ?thesis
      unfolding eq_def symcl_def by auto
  qed
  with assms show "(s, u) \<in> eq"
    by (cases "s \<noteq> t \<and> t \<noteq> u") (auto simp: eq_def)
qed

lemma sym_eq: "sym eq"
  unfolding eq_def symcl_def sym_def by auto

lemma equiv_eq: "lin_sat b \<Longrightarrow> equiv UNIV eq"
  by (rule equivI) (use refl_eq trans_eq sym_eq in safe)

lemma not_dominated_if_pwits:
  assumes "x \<in> Var ` pwits b" shows "\<not> s \<rightarrow>\<^bsub>bgraph b\<^esub> x"
proof -
  from assms obtain x' where "x = Var x'" "x' \<in> pwits b"
    by blast
  from lemma_2(3)[OF wf_branch this(2)] this(1) show "\<not> s \<rightarrow>\<^bsub>bgraph b\<^esub> x"
    unfolding arcs_ends_def arc_to_ends_def by (auto simp: bgraph_def)
qed

lemma parents_empty_if_pwits:
  assumes "x \<in> Var ` pwits b" shows "parents (bgraph b) x = {}"
  using not_dominated_if_pwits[OF assms] unfolding bgraph_def by simp

lemma not_AT_mem_if_urelem:
  assumes "t \<in> urelems b"
  shows "AT (s \<in>\<^sub>s t) \<notin> set b"
proof
  assume "AT (s \<in>\<^sub>s t) \<in> set b"
  with assms urelem_invar_if_wf_branch[OF wf_branch] have "urelem (AT (s \<in>\<^sub>s t)) t"
    by (meson types types_urelems urelem_def wf_branch)
  then show False
    unfolding urelem_def
    by (auto dest!: types_fmD simp: types_pset_atom.simps dest: types_term_unique)
qed

lemma not_dominated_if_urelems:
  assumes "t \<in> urelems b"
  shows "\<not> s \<rightarrow>\<^bsub>bgraph b\<^esub> t"
  using not_AT_mem_if_urelem[OF assms] unfolding bgraph_def by auto

lemma parents_empty_if_urelems:
  assumes "t \<in> urelems b"
  shows "parents (bgraph b) t = {}"
  using not_dominated_if_urelems[OF assms] by simp

lemma not_dominated_if_base_vars:
  assumes "x \<in> base_vars b"
  shows "\<not> s \<rightarrow>\<^bsub>bgraph b\<^esub> x"
  using assms not_dominated_if_urelems not_dominated_if_pwits
  unfolding base_vars_def by blast

lemma parents_empty_if_base_vars:
  assumes "x \<in> base_vars b"
  shows "parents (bgraph b) x = {}"
  using not_dominated_if_base_vars[OF assms] by blast

lemma eq_class_subs_subterms: "eq `` {t} \<subseteq> {t} \<union> subterms b"
proof -
  have "eq - Id \<subseteq> subterms b \<times> subterms b"
    by (auto simp: AT_eq_subterms_branchD eq_def symcl_def)
  then show "eq `` {t} \<subseteq> {t} \<union> subterms b"
    by blast
qed

lemma finite_eq_class: "finite (eq `` {x})"
  using eq_class_subs_subterms finite_subterms_branch
  using finite_subset by fastforce

lemma finite_I_image_eq_class: "finite (I ` eq `` {x})"
  using finite_eq_class by blast

context
begin

interpretation realisation "bgraph b" "base_vars b" "subterms' b" I eq
proof(unfold_locales)
  from base_vars_subterms'_disjnt show "base_vars b \<inter> subterms' b = {}" .

  show "verts (bgraph b) = base_vars b \<union> subterms' b"
    unfolding bgraph_def by simp

  from not_dominated_if_base_vars show "\<And>p t. p \<in> base_vars b \<Longrightarrow> \<not> t \<rightarrow>\<^bsub>bgraph b\<^esub> p" .
qed

lemmas realisation = realisation_axioms

lemma card_realisation:
  "hcard (realise t) \<le> 2 * card (subterms b)"
proof(induction t rule: realise.induct)
  case (1 x)
  then have "hcard (realise x) = card (realise ` parents (bgraph b) x \<union> I ` eq_class x)"
    using hcard_HF Zero_hf_def parents_empty_if_base_vars
    using finite_I_image_eq_class by force
  also have "\<dots> \<le> card (realise ` parents (bgraph b) x) + card (I ` eq_class x)"
    using card_Un_le by blast
  also have "\<dots> \<le> card (parents (bgraph b) x) + card (eq_class x)"
    using card_image_le[OF fin_digraph_bgraph.finite_parents]
    using card_image_le[OF finite_eq_class]
    by (metis add_le_mono)
  also have "\<dots> \<le> card (subterms b) + card (eq_class x)"
    using fin_digraph_bgraph.parents_subs_verts[unfolded verts_bgraph_eq_subterms]
    using card_mono[OF finite_subterms_branch]
    by (simp add: "1.hyps" not_dominated_if_base_vars)
  also have "\<dots> \<le> card (subterms b) + card ({x} \<union> subterms b)"
    apply (intro add_le_mono card_mono[where ?B="{x} \<union> subterms b"])
    using eq_class_subs_subterms finite_subterms_branch by auto
  also have "\<dots> \<le> 2 * card (subterms b)"
  proof -
    from 1 have "x \<in> subterms b"
      using "1.prems" verts_bgraph verts_bgraph_eq_subterms wf_branch_not_Nil[OF wf_branch]
      by blast
    then show ?thesis
      unfolding mult_2 by (metis insert_absorb insert_is_Un order_refl)
  qed
  finally show ?case .
next
  case (2 t)
  then have "hcard (realise t) = card (realise ` parents (bgraph b) t)"
    using hcard_HF[OF finite_realisation_parents] by simp
  also have "\<dots> \<le> card (parents (bgraph b) t)"
    using card_image_le by blast
  also have "\<dots> \<le> card (subterms b)"
    using fin_digraph_bgraph.parents_subs_verts wf_branch_not_Nil[OF wf_branch]
    unfolding verts_bgraph_eq_subterms
    by (metis card_mono fin_digraph_bgraph.finite_verts verts_bgraph_eq_subterms)
  finally show ?case
    unfolding base_vars_Un_subterms'_eq_subterms by auto
next
  case (3 t)
  then show ?case by simp
qed

lemma I_neq_realise: "I x \<noteq> realise y"
proof -
  note card_realisation[of y]
  moreover have "hcard (I x) > 2 * card (subterms b)"
    using card_I wf_branch
    by (simp add: subterms_branch_eq_if_wf_branch wits_subterms_eq_base_vars_Un_subterms')
  ultimately show ?thesis
    by (metis linorder_not_le)
qed

end

sublocale realisation "bgraph b" "base_vars b" "subterms' b" I eq
  rewrites "(\<And>x y. I x \<noteq> realise y) \<equiv> Trueprop True"
       and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
       and "\<And>P Q. (True \<Longrightarrow> PROP P \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> True \<Longrightarrow> PROP Q)"
  using realisation I_neq_realise by simp_all

lemma eq_class_singleton_if_pwits:
  assumes "x \<in> Var ` pwits b" shows "eq_class x = {x}"
proof -
  from assms obtain x' where "x = Var x'" "x' \<in> pwits b"
    by blast
  have False if "eq_class x \<noteq> {x}"
  proof -
    have "x \<in> eq_class x"
      by (simp add: eq_def symcl_def)
    with that obtain y where "y \<in> eq_class x" "y \<noteq> x"
      by auto
    then have "AT (y =\<^sub>s x) \<in> set b \<or> AT (x =\<^sub>s y) \<in> set b"
      unfolding eq_def symcl_def by auto
    with lemma_2(1,2)[OF wf_branch \<open>x' \<in> pwits b\<close>] \<open>x = Var x'\<close> show False
      by blast
  qed
  with assms show ?thesis by blast
qed

lemma realise_pwits:
  "x \<in> Var ` pwits b \<Longrightarrow> realise x = HF {I x}"
  unfolding realise.simps(1)[OF pwits_subs_base_vars[THEN subsetD]]
  by (auto simp: eq_class_singleton_if_pwits parents_empty_if_pwits)

lemma I_in_realise_if_base_vars[simp]:
  "s \<in> base_vars b \<Longrightarrow> I s \<^bold>\<in> realise s"
  using refl_eq by (simp add: finite_I_image_eq_class refl_on_def)

lemma realise_neq_if_base_vars_and_subterms':
  assumes "s \<in> base_vars b" "t \<in> subterms' b"
  shows "realise s \<noteq> realise t"
proof -
  from assms have "I s \<^bold>\<notin> realise t"
    using I_neq_realise by auto
  with I_in_realise_if_base_vars assms(1) show ?thesis
    by metis
qed

lemma AT_mem_branch_wits_subtermsD:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> wits_subterms b" "t \<in> wits_subterms b"
  using assms AT_mem_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma AF_mem_branch_wits_subtermsD:
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "s \<in> wits_subterms b" "t \<in> wits_subterms b"
  using assms AF_mem_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma AT_eq_branch_wits_subtermsD:
  assumes "AT (s =\<^sub>s t) \<in> set b"
  shows "s \<in> wits_subterms b" "t \<in> wits_subterms b"
  using assms AT_eq_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma AF_eq_branch_wits_subtermsD:
  assumes "AF (s =\<^sub>s t) \<in> set b"
  shows "s \<in> wits_subterms b" "t \<in> wits_subterms b"
  using assms AF_eq_subterms_branchD subterms_branch_eq_if_wf_branch wf_branch by blast+

lemma realisation_if_AT_mem:
  assumes "AT (s \<in>\<^sub>s t) \<in> set b"
  shows "realise s \<^bold>\<in> realise t"
proof -
  from assms have "t \<in> base_vars b \<union> subterms' b"
    using in_subterms'_if_AT_mem_in_branch(2) wf_branch by blast
  moreover from assms have "s \<rightarrow>\<^bsub>bgraph b\<^esub> t"
    unfolding arcs_ends_def arc_to_ends_def by (simp add: bgraph_def)
  ultimately show ?thesis
    by (cases t rule: realise.cases) auto
qed

lemma AT_eq_urelems_subterms'_cases:
  includes Set_member_no_ascii_notation
  assumes "AT (s =\<^sub>s t) \<in> set b"
  obtains (urelems) "s \<in> urelems b" "t \<in> urelems b" |
          (subterms') "s \<in> subterms' b" "t \<in> subterms' b"
proof -
  from types obtain v where "v \<turnstile> last b"
    by blast
  with types_urelems wf_branch obtain v'
    where v': "\<forall>\<phi> \<in> set b. v' \<turnstile> \<phi>" "\<forall>u \<in> urelems b. v' \<turnstile> u : 0"
    by blast
  with assms have "v' \<turnstile> AT (s =\<^sub>s t)"
    by blast
  then obtain lst where lst: "v' \<turnstile> s : lst" "v' \<turnstile> t : lst"
    by (auto dest!: types_fmD(6) simp: types_pset_atom.simps)
  note mem_subterms = AT_eq_subterms_branchD[OF assms]
  with v' have "t \<in> urelems b" if "s \<in> urelems b"
    using that lst types_term_unique urelems_def by fastforce
  moreover from assms have "s \<notin> Var ` pwits b" "t \<notin> Var ` pwits b"
    using lemma_2(1,2)[OF wf_branch] by blast+
  moreover have "t \<in> subterms' b" if "s \<in> subterms' b"
  proof -
    have "s \<notin> urelems b"
      using that B_T_partition_verts(1) unfolding base_vars_def by blast
    with v'(1) mem_subterms(1) have "\<not> v' \<turnstile> s : 0"
      using urelems_def by blast
    with lst v'(2) have "t \<notin> urelems b"
      using types_term_unique by metis
    with \<open>t \<notin> Var ` pwits b\<close> \<open>t \<in> subterms b\<close> show "t \<in> subterms' b"
      by (simp add: base_vars_def subterms'_def)
  qed
  ultimately show ?thesis
    using that mem_subterms
    by (cases "s \<in> subterms' b") (auto simp: base_vars_def subterms'_def)
qed

lemma realisation_if_AT_eq:
  assumes "lin_sat b"
  assumes "AT (s =\<^sub>s t) \<in> set b"
  shows "realise s = realise t"
proof -
  from assms(2) show ?thesis
  proof(cases rule: AT_eq_urelems_subterms'_cases)
    case urelems
    then have "s \<in> base_vars b" "t \<in> base_vars b"
      by (simp_all add: base_vars_def)
    moreover from assms have "(s, t) \<in> eq"
      unfolding eq_def symcl_def by blast
    then have "I ` eq_class s = I ` eq_class t"
      using equiv_eq[OF assms(1)] by (simp add: equiv_class_eq_iff)
    ultimately show ?thesis 
      using urelems by (simp add: parents_empty_if_urelems)
  next
    case subterms'
    have "False" if "realise s \<noteq> realise t"
    proof -
      from that have "hfset (realise s) \<noteq> hfset (realise t)"
        by (metis HF_hfset)
      then obtain a s' t' where
        a: "a \<in> realise ` parents (bgraph b) s'"
           "a \<notin> realise ` parents (bgraph b) t'"
        and s'_t': "s' = s \<and> t' = t \<or> s' = t \<and> t' = s"
        using subterms' by auto blast+
      with subterms' have "s' \<in> subterms' b" "t' \<in> subterms' b"
        by auto
      with a obtain u where u: "a = realise u" "u \<rightarrow>\<^bsub>bgraph b\<^esub> s'"
        using subterms' dominates_if_mem_realisation by auto
      then have "u \<noteq> s'"
        using dag_bgraph.adj_not_same by blast
      from u have "AT (u \<in>\<^sub>s s') \<in> set b"
        unfolding bgraph_def Let_def using dag_bgraph.adj_not_same by auto
      note lexpands_eq.intros(1,3)[OF assms(2) this, THEN lexpands.intros(6)]
      with \<open>lin_sat b\<close> s'_t' \<open>u \<noteq> s'\<close> have "AT (u \<in>\<^sub>s t') \<in> set b"
        unfolding lin_sat_def by (auto split: if_splits)
      from realisation_if_AT_mem[OF this] \<open>a = realise u\<close> have "a \<^bold>\<in> realise t'"
        by blast
      with a show False
        using \<open>t' \<in> subterms' b\<close> by simp
    qed
    then show ?thesis by blast
  qed
qed

lemma realise_base_vars_if_AF_eq:
  assumes "sat b"
  assumes "AF (x =\<^sub>s y) \<in> set b"
  assumes "x \<in> base_vars b \<or> y \<in> base_vars b"
  shows "realise x \<noteq> realise y"
proof(cases "x \<in> base_vars b \<and> y \<in> base_vars b")
  case False
  with assms(3) show ?thesis
    using realise_neq_if_base_vars_and_subterms' I_in_realise_if_base_vars
    by (metis hempty_iff realise.elims)
next
  case True
  from assms bopen have "x \<noteq> y"
    using neqSelf by blast
  moreover from assms bopen have "AT (x =\<^sub>s y) \<notin> set b"
    using contr by blast
  moreover have "AT (y =\<^sub>s x) \<notin> set b"
  proof 
    assume "AT (y =\<^sub>s x) \<in> set b"
    note lexpands_eq.intros(2)[OF this assms(2), THEN lexpands.intros(6)]
    with \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "AF (x =\<^sub>s x) \<in> set b"
      by auto
    with bopen neqSelf show False
      by blast
  qed
  ultimately have "(x, y) \<notin> eq"
    unfolding eq_def symcl_def by auto

  then have "x \<notin> eq_class y"
    by (meson Image_singleton_iff symE sym_eq)
  then have "I x \<notin> I ` eq_class y"
    using inj_on_I AF_eq_subterms_branchD[OF assms(2)]
    using eq_class_subs_subterms inj_onD by fastforce
  then have "I ` eq_class x \<noteq> I ` eq_class y"
    using refl_eq
    by (metis Image_singleton_iff UNIV_I imageI refl_onD)

  with \<open>x \<in> base_vars b \<and> y \<in> base_vars b\<close> show "realise x \<noteq> realise y"
    using hunion_hempty_left[unfolded Zero_hf_def]
    using inj_on_HF[THEN inj_onD] finite_I_image_eq_class
    by (force simp: parents_empty_if_base_vars)
qed

lemma Ex_AT_eq_mem_subterms_last_if_subterms':
  assumes "t \<in> subterms' b"
  obtains "t \<in> subterms (last b) - base_vars b"
  | t' where "t' \<in> subterms (last b) - base_vars b"
             "AT (t =\<^sub>s t') \<in> set b \<or> AT (t' =\<^sub>s t) \<in> set b"
proof(cases "t \<in> subterms (last b) - base_vars b")
  case False
  from assms have "t \<in> subterms b"
    using base_vars_Un_subterms'_eq_subterms by auto
  with False consider (t_base_vars) "t \<in> base_vars b" | (t_wits) "t \<in> Var ` wits b"
    using no_new_subterms_if_wf_branch[OF wf_branch]
    by (meson DiffI no_new_subterms_def)
  then show ?thesis
  proof cases
    case t_wits
    with \<open>t \<in> subterms' b\<close> have "t \<notin> Var ` pwits b"
      unfolding subterms'_def base_vars_def by blast
    with t_wits obtain t' where t': "t' \<in> subterms (last b)"
      "AT (t =\<^sub>s t') \<in> set b \<or> AT (t' =\<^sub>s t) \<in> set b"
      unfolding pwits_def by blast
    with \<open>t \<in> subterms' b\<close> have "t' \<notin> base_vars b"
      using AT_eq_urelems_subterms'_cases B_T_partition_verts(1)
      by (metis Un_iff base_vars_def disjoint_iff)
    with t' that show ?thesis
      by blast
  qed (use assms[unfolded subterms'_def] in blast)
qed
  

lemma realisation_if_AF_eq:
  assumes "sat b"
  assumes "AF (t1 =\<^sub>s t2) \<in> set b"
  shows "realise t1 \<noteq> realise t2"
proof -
  note AF_eq_branch_wits_subtermsD[OF assms(2)]
  then consider
    (t1_base_vars) "t1 \<in> base_vars b" |
    (t2_base_vars) "t2 \<in> base_vars b" "t1 \<in> base_vars b \<union> subterms' b" |
    (subterms) "t1 \<in> subterms' b" "t2 \<in> subterms' b"
    by (metis UnE wf_branch wits_subterms_eq_base_vars_Un_subterms')
  then show ?thesis
  proof cases
    case t1_base_vars
    with assms show ?thesis
      using realise_base_vars_if_AF_eq by blast
  next
    case t2_base_vars
    with assms show ?thesis
      using realise_base_vars_if_AF_eq by blast
  next
    case subterms
    define \<Delta> where "\<Delta> \<equiv> {(t1, t2) \<in> subterms' b \<times> subterms' b.
                            AF (t1 =\<^sub>s t2) \<in> set b \<and> realise t1 = realise t2}"
    have "finite \<Delta>"
    proof -
      have "\<Delta> \<subseteq> subterms' b \<times> subterms' b"
        unfolding \<Delta>_def by auto
      moreover note finite_cartesian_product[OF finite_subterms' finite_subterms']
      ultimately show ?thesis
        using finite_subset by blast
    qed
    let ?h = "\<lambda>(t1, t2). min (height t1) (height t2)"
    have False if "\<Delta> \<noteq> {}"
    proof -
      obtain t1 t2 where t1_t2: "(t1, t2) = arg_min_on ?h \<Delta>"
        by (metis surj_pair)
      have "(t1, t2) \<in> \<Delta>" "?h (t1, t2) = Min (?h ` \<Delta>)"
      proof -
        from arg_min_if_finite(1)[OF \<open>finite \<Delta>\<close> that] t1_t2 show "(t1, t2) \<in> \<Delta>"
          by metis

        have "f (arg_min_on f S) = Min (f ` S)" if "finite S" "S \<noteq> {}"
          for f :: "('a pset_term \<times> 'a pset_term) \<Rightarrow> nat" and S
          using arg_min_least[OF that] that
          by (auto intro!: Min_eqI[symmetric] intro: arg_min_if_finite(1)[OF that])
        from this[OF \<open>finite \<Delta>\<close> that] t1_t2 show "?h (t1, t2) = Min (?h ` \<Delta>)"
          by auto
      qed
      then have *: "t1 \<in> subterms' b" "t2 \<in> subterms' b"
        "AF (t1 =\<^sub>s t2) \<in> set b" "realise t1 = realise t2"
        unfolding \<Delta>_def by auto
      obtain t1' t2' where t1'_t2':
        "t1' \<in> subterms (last b) - base_vars b" "t2' \<in> subterms (last b) - base_vars b"
        "AF (t1' =\<^sub>s t2') \<in> set b"
        "realise t1' = realise t1" "realise t2' = realise t2"
      proof -
        note Ex_AT_eq_mem_subterms_last_if_subterms'[OF \<open>t1 \<in> subterms' b\<close>]
        then obtain t1'' where
          "t1'' \<in> subterms (last b) - base_vars b" "AF (t1'' =\<^sub>s t2) \<in> set b"
          "realise t1'' = realise t1"
        proof cases
          case (2 t1')
          from bopen neqSelf \<open>AF (t1 =\<^sub>s t2) \<in> set b\<close> have "t1 \<noteq> t2"
            by blast
          with 2 \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "AF (t1' =\<^sub>s t2) \<in> set b"
            using lexpands_eq.intros(2,4)[OF _ \<open>AF (t1 =\<^sub>s t2) \<in> set b\<close>, THEN lexpands.intros(6)]
            by fastforce
          with that[OF _ this] "2"(1) \<open>sat b\<close>[unfolded sat_def] show ?thesis
            using realisation_if_AT_eq 2 by metis
        qed (use * that[of t1] in blast)
        moreover
        note Ex_AT_eq_mem_subterms_last_if_subterms'[OF \<open>t2 \<in> subterms' b\<close>]
        then obtain t2'' where
          "t2'' \<in> subterms (last b) - base_vars b" "AF (t1'' =\<^sub>s t2'') \<in> set b"
          "realise t2'' = realise t2"
        proof cases
          case (2 t2')
          from bopen neqSelf \<open>AF (t1'' =\<^sub>s t2) \<in> set b\<close> have "t1'' \<noteq> t2"
            by blast
          with 2 \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "AF (t1'' =\<^sub>s t2') \<in> set b"
            using lexpands_eq.intros(2,4)[OF _ \<open>AF (t1'' =\<^sub>s t2) \<in> set b\<close>, THEN lexpands.intros(6)]
            by fastforce
          with that[OF _ this] "2"(1) \<open>sat b\<close>[unfolded sat_def] show ?thesis
            using realisation_if_AT_eq 2 by metis
        qed (use \<open>AF (t1'' =\<^sub>s t2) \<in> set b\<close> that[of t2] in blast)
        ultimately show ?thesis
          using that * by metis
      qed
      with \<open>realise t1 = realise t2\<close> have "(t1', t2') \<in> \<Delta>"
        unfolding \<Delta>_def subterms'_def
        by (simp add: AF_eq_subterms_branchD(1,2))
      then have t1'_t2'_subterms: "t1' \<in> subterms' b" "t2' \<in> subterms' b"
        unfolding \<Delta>_def by blast+
      
      from t1'_t2' lemma1_2 "*"(3) have "?h (t1', t2') = ?h (t1, t2)"
        by (metis in_subterms'_if_AF_eq_in_branch(1,2)[OF wf_branch] case_prod_conv)

      from mem_urelems_if_urelem_last[OF wf_branch] t1'_t2'(1,2)
      have not_urelem: "\<not> urelem (last b) t1'" "\<not> urelem (last b) t2'"
        unfolding base_vars_def by auto
      from finite_vars_branch infinite_vars obtain x where "x \<notin> vars b"
        using ex_new_if_finite by blast
      from bexpands_wit.intros[OF t1'_t2'(3) _ _ _ _ this not_urelem]
           t1'_t2'(1,2) \<open>sat b\<close>[unfolded sat_def] consider
        s1 where "AT (s1 \<in>\<^sub>s t1') \<in> set b" "AF (s1 \<in>\<^sub>s t2') \<in> set b" |
        s2 where "AF (s2 \<in>\<^sub>s t1') \<in> set b" "AT (s2 \<in>\<^sub>s t2') \<in> set b"
        using bexpands.intros(2-) by (metis Diff_iff)
      then show ?thesis
      proof cases
        case 1
        then have "realise s1 \<^bold>\<in> realise t2'"
          using realisation_if_AT_mem
          by (metis "*"(4) t1'_t2'(4) t1'_t2'(5))
        with 1 t1'_t2'(3,4) obtain s2 where
          "s2 \<rightarrow>\<^bsub>bgraph b\<^esub> t2'" "realise s1 = realise s2"
          using dominates_if_mem_realisation in_subterms'_if_AT_mem_in_branch(1)[OF wf_branch] 
          by metis
        then have "AT (s2 \<in>\<^sub>s t2') \<in> set b"
          unfolding bgraph_def Let_def by auto
        with \<open>AF (s1 \<in>\<^sub>s t2') \<in> set b\<close> \<open>sat b\<close>[THEN satD(1), THEN lin_satD]
        have "AF (s2 =\<^sub>s s1) \<in> set b"
          using lexpands_eq.intros(5)[THEN lexpands.intros(6)] by fastforce
        then have "s1 \<noteq> s2"
          using neqSelf bopen by blast
        from realise_base_vars_if_AF_eq[OF \<open>sat b\<close> \<open>AF (s2 =\<^sub>s s1) \<in> set b\<close>]
             \<open>realise s1 = realise s2\<close>
        have "s1 \<in> subterms' b" "s2 \<in> subterms' b"
          by (metis Un_iff \<open>AF (s2 =\<^sub>s s1) \<in> set b\<close> in_subterms'_if_AF_eq_in_branch wf_branch)+
   
        with \<open>realise s1 = realise s2\<close> have "(s2, s1) \<in> \<Delta>"
          unfolding \<Delta>_def using \<open>AF (s2 =\<^sub>s s1) \<in> set b\<close> by auto
        moreover
        have "realise s1 \<^bold>\<in> realise t1'" "realise s2 \<^bold>\<in> realise t1'"
             "realise s1 \<^bold>\<in> realise t2'" "realise s2 \<^bold>\<in> realise t2'"
          using \<open>realise s1 \<^bold>\<in> realise t2'\<close> \<open>realise s1 = realise s2\<close>
          using "*"(4) t1'_t2'(4,5) by auto
        with lemma1_3 have "?h (s2, s1) < ?h (t1', t2')"
          using \<open>s1 \<in> subterms' b\<close> \<open>s2 \<in> subterms' b\<close> t1'_t2'_subterms
          by (auto simp: min_def)
        ultimately show ?thesis
          using arg_min_least[OF \<open>finite \<Delta>\<close> \<open>\<Delta> \<noteq> {}\<close>]
          using \<open>(t1', t2') \<in> \<Delta>\<close> \<open>?h (t1', t2') = ?h (t1, t2)\<close> t1_t2
          by (metis (mono_tags, lifting) le_antisym le_eq_less_or_eq nat_neq_iff)
      next
        case 2
        then have "realise s2 \<^bold>\<in> realise t1'"
          using realisation_if_AT_mem
          by (metis "*"(4) t1'_t2'(4) t1'_t2'(5))
        with 2 t1'_t2'(3,4) obtain s1 where
          "s1 \<rightarrow>\<^bsub>bgraph b\<^esub> t1'" "realise s1 = realise s2"
          using dominates_if_mem_realisation by metis
        then have "AT (s1 \<in>\<^sub>s t1') \<in> set b"
          unfolding bgraph_def Let_def by auto
        with \<open>AF (s2 \<in>\<^sub>s t1') \<in> set b\<close> \<open>sat b\<close>[unfolded sat_def]
        have "AF (s1 =\<^sub>s s2) \<in> set b"
          using lexpands_eq.intros(5)[THEN lexpands.intros(6)]
          using lin_satD by fastforce
        then have "s1 \<noteq> s2"
          using neqSelf bopen by blast           
        from realise_base_vars_if_AF_eq[OF \<open>sat b\<close> \<open>AF (s1 =\<^sub>s s2) \<in> set b\<close>]
             \<open>realise s1 = realise s2\<close>
        have "s1 \<in> subterms' b" "s2 \<in> subterms' b"
          by (metis Un_iff \<open>AF (s1 =\<^sub>s s2) \<in> set b\<close> in_subterms'_if_AF_eq_in_branch wf_branch)+

        with \<open>realise s1 = realise s2\<close> have "(s1, s2) \<in> \<Delta>"
          unfolding \<Delta>_def using \<open>AF (s1 =\<^sub>s s2) \<in> set b\<close> by auto
        moreover
        have "realise s1 \<^bold>\<in> realise t1'" "realise s2 \<^bold>\<in> realise t1'"
             "realise s1 \<^bold>\<in> realise t2'" "realise s2 \<^bold>\<in> realise t2'"
          using \<open>realise s2 \<^bold>\<in> realise t1'\<close> \<open>realise s1 = realise s2\<close>
          using "*"(4) t1'_t2'(4,5) by auto
        with lemma1_3 have "?h (s1, s2) < ?h (t1', t2')"
          using \<open>s1 \<in> subterms' b\<close> \<open>s2 \<in> subterms' b\<close> t1'_t2'_subterms
          by (auto simp: min_def)
        ultimately show ?thesis
          using arg_min_least[OF \<open>finite \<Delta>\<close> \<open>\<Delta> \<noteq> {}\<close>]
          using \<open>(t1', t2') \<in> \<Delta>\<close> \<open>?h (t1', t2') = ?h (t1, t2)\<close> t1_t2
          by (metis (mono_tags, lifting) le_antisym le_eq_less_or_eq nat_neq_iff)
      qed
    qed
    with assms subterms show ?thesis
      unfolding \<Delta>_def by blast
  qed
qed

lemma realisation_if_AF_mem:
  assumes "sat b"
  assumes "AF (s \<in>\<^sub>s t) \<in> set b"
  shows "realise s \<^bold>\<notin> realise t"
proof
  assume "realise s \<^bold>\<in> realise t"
  from assms have "s \<in> base_vars b \<union> subterms' b"
                  "t \<in> base_vars b \<union> subterms' b"
    using in_subterms'_if_AF_mem_in_branch[OF wf_branch] by blast+
  from dominates_if_mem_realisation[OF \<open>realise s \<^bold>\<in> realise t\<close>]
  obtain s' where "s' \<rightarrow>\<^bsub>bgraph b\<^esub> t" "realise s = realise s'"
    by blast
  then have "AT (s' \<in>\<^sub>s t) \<in> set b"
    unfolding bgraph_def Let_def by auto
  with assms lexpands_eq.intros(5)[THEN lexpands.intros(6)] have "AF (s' =\<^sub>s s) \<in> set b"
    unfolding sat_def using lin_satD by fastforce
  from realisation_if_AF_eq[OF \<open>sat b\<close> this] \<open>realise s = realise s'\<close> show False
    by simp
qed

lemma realisation_Empty: "realise (\<emptyset> n) = 0"
proof -
  from bopen have "AT (s \<in>\<^sub>s \<emptyset> n) \<notin> set b" for s
    using bclosed.intros by blast
  then have "parents (bgraph b) (\<emptyset> n) = {}"
    unfolding bgraph_def Let_def by auto
  moreover
  have "(\<emptyset> n) \<notin> base_vars b"
  proof -
    have "(\<emptyset> n) \<notin> Var ` pwits b"
      using pwits_def wits_def by blast
    moreover have "(\<emptyset> n) \<notin> urelems b"
      unfolding urelems_def using wf_branch[THEN wf_branch_not_Nil] last_in_set
      using is_Var_if_urelem' by fastforce
    ultimately show ?thesis
      unfolding base_vars_def by blast
  qed
  then have "(\<emptyset> n) \<in> subterms' b \<or> (\<emptyset> n) \<notin> verts (bgraph b)"
    by (simp add: verts_bgraph)
  ultimately show "realise (\<emptyset> n) = 0"
    by (auto simp: verts_bgraph)
qed

lemma realisation_Union:
  assumes "sat b"
  assumes "t1 \<squnion>\<^sub>s t2 \<in> subterms b"
  shows "realise (t1 \<squnion>\<^sub>s t2) = realise t1 \<squnion> realise t2"
  using assms
proof -
  from assms have mem_subterms_last: "t1 \<squnion>\<^sub>s t2 \<in> subterms (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  note not_urelem_comps_if_compound[where ?f="(\<squnion>\<^sub>s)", OF assms(2), simplified]
  moreover note subterms_fmD(1,2)[OF mem_subterms_last]
  then have "t1 \<notin> Var ` pwits b" "t2 \<notin> Var ` pwits b"
    unfolding pwits_def wits_def 
    using pset_term.set_intros(1) mem_vars_fm_if_mem_subterms_fm by fastforce+
  ultimately have "t1 \<in> subterms' b" "t2 \<in> subterms' b"
    unfolding subterms'_def base_vars_def
    using assms(2) by (auto dest: subterms_branchD)

  from assms(2) have "t1 \<squnion>\<^sub>s t2 \<in> subterms' b"
    using base_vars_subs_vars base_vars_Un_subterms'_eq_subterms by blast

  have "realise (t1 \<squnion>\<^sub>s t2) \<le> realise t1 \<squnion> realise t2"
  proof
    fix e assume "e \<^bold>\<in> realise (t1 \<squnion>\<^sub>s t2)"
    then obtain s where s: "e = realise s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> (t1 \<squnion>\<^sub>s t2)"
      using dominates_if_mem_realisation \<open>t1 \<squnion>\<^sub>s t2 \<in> subterms' b\<close>
      by auto
    then have "AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> consider "AT (s \<in>\<^sub>s t1) \<in> set b" | "AF (s \<in>\<^sub>s t1) \<in> set b"
      unfolding sat_def using bexpands_nowit.intros(3)[OF _ mem_subterms_last, THEN bexpands.intros(1)]
      by blast
    then show "e \<^bold>\<in> realise t1 \<squnion> realise t2"
    proof(cases)
      case 1
      with s show ?thesis using realisation_if_AT_mem by auto
    next
      case 2
      from \<open>sat b\<close> lexpands_un.intros(4)[OF \<open>AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b\<close> this]
      have "AT (s \<in>\<^sub>s t2) \<in> set b"
        unfolding sat_def using lin_satD lexpands.intros(2) by force
      with s show ?thesis using realisation_if_AT_mem by auto
    qed
  qed
  moreover have "realise t1 \<squnion> realise t2 \<le> realise (t1 \<squnion>\<^sub>s t2)"
  proof
    fix e assume "e \<^bold>\<in> realise t1 \<squnion> realise t2"
    with \<open>t1 \<in> subterms' b\<close> \<open>t2 \<in> subterms' b\<close> consider
      s1 where "e = realise s1" "s1 \<rightarrow>\<^bsub>bgraph b\<^esub> t1" |
      s2 where "e = realise s2" "s2 \<rightarrow>\<^bsub>bgraph b\<^esub> t2"
      using dominates_if_mem_realisation by force
    then show "e \<^bold>\<in> realise (t1 \<squnion>\<^sub>s t2)"
    proof(cases)
      case 1
      then have "AT (s1 \<in>\<^sub>s t1) \<in> set b"
        unfolding bgraph_def Let_def by auto
      from \<open>sat b\<close> lexpands_un.intros(2)[OF this mem_subterms_last, THEN lexpands.intros(2)]
      have "AT (s1 \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b"
        unfolding sat_def using lin_satD by force
      with 1 realisation_if_AT_mem[OF this] show ?thesis
        by blast
    next
      case 2
      then have "AT (s2 \<in>\<^sub>s t2) \<in> set b"
        unfolding bgraph_def Let_def by auto
      from \<open>sat b\<close> lexpands_un.intros(3)[OF this mem_subterms_last, THEN lexpands.intros(2)]
      have "AT (s2 \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b"
        unfolding sat_def using lin_satD by force
      with 2 realisation_if_AT_mem[OF this] show ?thesis
        by blast
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma realisation_Inter:
  assumes "sat b"
  assumes "t1 \<sqinter>\<^sub>s t2 \<in> subterms b"
  shows "realise (t1 \<sqinter>\<^sub>s t2) = realise t1 \<sqinter> realise t2"
  using assms
proof -
  from assms have mem_subterms_last: "t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  note not_urelem_comps_if_compound[where ?f="(\<sqinter>\<^sub>s)", OF assms(2), simplified]
  moreover note subterms_fmD(3,4)[OF mem_subterms_last]
  then have "t1 \<notin> Var ` pwits b" "t2 \<notin> Var ` pwits b"
    unfolding pwits_def wits_def 
    using pset_term.set_intros(1) mem_vars_fm_if_mem_subterms_fm by fastforce+
  ultimately have t1_t2_subterms': "t1 \<in> subterms' b" "t2 \<in> subterms' b"
    unfolding subterms'_def base_vars_def
    using assms(2) by (auto dest: subterms_branchD)

  from assms(2) have "t1 \<sqinter>\<^sub>s t2 \<in> subterms' b"
    using base_vars_subs_vars base_vars_Un_subterms'_eq_subterms by blast

  have "realise (t1 \<sqinter>\<^sub>s t2) \<le> realise t1 \<sqinter> realise t2"
  proof
    fix e assume "e \<^bold>\<in> realise (t1 \<sqinter>\<^sub>s t2)"
    with \<open>t1 \<sqinter>\<^sub>s t2 \<in> subterms' b\<close> obtain s
      where s: "e = realise s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> (t1 \<sqinter>\<^sub>s t2)"
      using dominates_if_mem_realisation by auto
    then have "AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> lexpands_int.intros(1)[OF this, THEN lexpands.intros(3)]
    have "AT (s \<in>\<^sub>s t1) \<in> set b" "AT (s \<in>\<^sub>s t2) \<in> set b"
      unfolding sat_def using lin_satD by force+
    from this[THEN realisation_if_AT_mem] s show "e \<^bold>\<in> realise t1 \<sqinter> realise t2"
      by auto
  qed
  moreover have "realise t1 \<sqinter> realise t2 \<le> realise (t1 \<sqinter>\<^sub>s t2)"
  proof
    fix e assume "e \<^bold>\<in> realise t1 \<sqinter> realise t2"
    with \<open>t1 \<in> subterms' b\<close> \<open>t2 \<in> subterms' b\<close> obtain s1 s2 where s1_s2:
      "e = realise s1" "s1 \<rightarrow>\<^bsub>bgraph b\<^esub> t1"
      "e = realise s2" "s2 \<rightarrow>\<^bsub>bgraph b\<^esub> t2"
      using dominates_if_mem_realisation by auto metis
    then have "AT (s1 \<in>\<^sub>s t1) \<in> set b" "AT (s2 \<in>\<^sub>s t2) \<in> set b"
      unfolding bgraph_def Let_def by auto
    moreover have "AT (s1 \<in>\<^sub>s t2) \<in> set b"
    proof -
      from \<open>sat b\<close> have "AT (s1 \<in>\<^sub>s t2) \<in> set b \<or> AF (s1 \<in>\<^sub>s t2) \<in> set b"
        unfolding sat_def
        using bexpands_nowit.intros(4)[OF \<open>AT (s1 \<in>\<^sub>s t1) \<in> set b\<close> mem_subterms_last]
        using bexpands.intros(1) by blast
      moreover from \<open>sat b\<close> s1_s2 have False if "AF (s1 \<in>\<^sub>s t2) \<in> set b"
      proof -
        note lexpands_eq.intros(5)[OF \<open>AT (s2 \<in>\<^sub>s t2) \<in> set b\<close> that, THEN lexpands.intros(6)]
        with realisation_if_AF_eq[OF \<open>sat b\<close>, of s2 s1] have "realise s2 \<noteq> realise s1"
          using \<open>sat b\<close> by (auto simp: sat_def lin_satD)
        with \<open>e = realise s1\<close> \<open>e = realise s2\<close> show False by simp
      qed
      ultimately show "AT (s1 \<in>\<^sub>s t2) \<in> set b" by blast
    qed
    ultimately have "AT (s1 \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b"
      using \<open>sat b\<close> lexpands_int.intros(6)[OF _ _ mem_subterms_last, THEN lexpands.intros(3)]
      unfolding sat_def by (fastforce simp: lin_satD)
    from realisation_if_AT_mem[OF this] show "e \<^bold>\<in> realise (t1 \<sqinter>\<^sub>s t2)"
      unfolding \<open>e = realise s1\<close>
      by simp
  qed
  ultimately show ?thesis by blast
qed

lemma realisation_Diff:
  assumes "sat b"
  assumes "s -\<^sub>s t \<in> subterms b"
  shows "realise (s -\<^sub>s t) = realise s - realise t"
  using assms
proof -
  from assms have mem_subterms_last: "s -\<^sub>s t \<in> subterms (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  note not_urelem_comps_if_compound[where ?f="(-\<^sub>s)", OF assms(2), simplified]
  moreover note subterms_fmD(5,6)[OF mem_subterms_last]
  then have "s \<notin> Var ` pwits b" "t \<notin> Var ` pwits b"
    unfolding pwits_def wits_def 
    using pset_term.set_intros(1) mem_vars_fm_if_mem_subterms_fm by fastforce+
  ultimately have "s \<in> subterms' b" "t \<in> subterms' b"
    unfolding subterms'_def base_vars_def
    using assms(2) by (auto dest: subterms_branchD)

  from assms(2) have "s -\<^sub>s t \<in> subterms' b"
    using base_vars_subs_vars base_vars_Un_subterms'_eq_subterms by blast

  have "realise (s -\<^sub>s t) \<le> realise s - realise t"
  proof
    fix e assume "e \<^bold>\<in> realise (s -\<^sub>s t)"
    then obtain u where u: "e = realise u" "u \<rightarrow>\<^bsub>bgraph b\<^esub> (s -\<^sub>s t)"
      using dominates_if_mem_realisation \<open>s -\<^sub>s t \<in> subterms' b\<close> by auto
    then have "AT (u \<in>\<^sub>s s -\<^sub>s t) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> lexpands_diff.intros(1)[OF this, THEN lexpands.intros(4)]
    have "AT (u \<in>\<^sub>s s) \<in> set b" "AF (u \<in>\<^sub>s t) \<in> set b"
      unfolding sat_def using lin_satD by force+
    with u show "e \<^bold>\<in> realise s - realise t"
      using \<open>sat b\<close> realisation_if_AT_mem realisation_if_AF_mem
      by auto
  qed
  moreover have "realise s - realise t \<le> realise (s -\<^sub>s t)"
  proof
    fix e assume "e \<^bold>\<in> realise s - realise t"
    then obtain u where u:
      "e = realise u" "u \<rightarrow>\<^bsub>bgraph b\<^esub> s" "\<not> u \<rightarrow>\<^bsub>bgraph b\<^esub> t"
      using dominates_if_mem_realisation \<open>s \<in> subterms' b\<close> \<open>t \<in> subterms' b\<close> by auto
    then have "AT (u \<in>\<^sub>s s) \<in> set b"
      unfolding bgraph_def Let_def by auto
    moreover have "AF (u \<in>\<^sub>s t) \<in> set b"
    proof -
      from \<open>sat b\<close> have "AT (u \<in>\<^sub>s t) \<in> set b \<or> AF (u \<in>\<^sub>s t) \<in> set b"
        unfolding sat_def using bexpands_nowit.intros(5)[OF \<open>AT (u \<in>\<^sub>s s) \<in> set b\<close> mem_subterms_last]
        using bexpands.intros(1) by blast
      moreover from u(3) have False if "AT (u \<in>\<^sub>s t) \<in> set b"
        using that unfolding Let_def bgraph_def by (auto simp: arcs_ends_def arc_to_ends_def)
      ultimately show "AF (u \<in>\<^sub>s t) \<in> set b"
        by blast
    qed
    ultimately have "AT (u \<in>\<^sub>s s -\<^sub>s t) \<in> set b"
      using \<open>sat b\<close> lexpands_diff.intros(6)[OF _ _ mem_subterms_last, THEN lexpands.intros(4)]
      unfolding sat_def by (fastforce simp: lin_satD)
    from realisation_if_AT_mem[OF this] show "e \<^bold>\<in> realise (s -\<^sub>s t)"
      unfolding \<open>e = realise u\<close>
      by simp
  qed
  ultimately show ?thesis by blast
qed

lemma realisation_Single:
  assumes "sat b"
  assumes "Single t \<in> subterms b"
  shows "realise (Single t) = HF {realise t}"
  using assms
proof -
  from assms have mem_subterms_last: "Single t \<in> subterms (last b)"
    using mem_subterms_fm_last_if_mem_subterms_branch[OF wf_branch]
    by simp
  have "Single t \<in> subterms' b"
    proof -
    from urelems_subs_vars have "Single t \<notin> base_vars b"
      unfolding base_vars_def by blast
    then show ?thesis
      by (simp add: assms(2) subterms'_def)
  qed

  have "realise (Single t) \<le> HF {realise t}"
  proof
    fix e assume "e \<^bold>\<in> realise (Single t)"
    then obtain s where s: "e = realise s" "s \<rightarrow>\<^bsub>bgraph b\<^esub> Single t"
      using dominates_if_mem_realisation \<open>Single t \<in> subterms' b\<close> by auto
    then have "AT (s \<in>\<^sub>s Single t) \<in> set b"
      unfolding bgraph_def Let_def by auto
    with \<open>sat b\<close> lexpands_single.intros(2)[OF this, THEN lexpands.intros(5)]
    have "AT (s =\<^sub>s t) \<in> set b"
      unfolding sat_def using lin_satD by fastforce
    with s show "e \<^bold>\<in> HF {realise t}"
      using realisation_if_AT_eq \<open>sat b\<close>[unfolded sat_def]
      by auto
  qed
  moreover have "HF {realise t} \<le> realise (Single t)"
  proof
    fix e assume "e \<^bold>\<in> HF {realise t}"
    then have "e = realise t"
      by simp
    from lexpands_single.intros(1)[OF mem_subterms_last, THEN lexpands.intros(5)] \<open>sat b\<close>
    have "AT (t \<in>\<^sub>s Single t) \<in> set b"
      unfolding sat_def using lin_satD by fastforce
    from realisation_if_AT_mem[OF this] \<open>e = realise t\<close>
    show "e \<^bold>\<in> realise (Single t)"
      by simp
  qed
  ultimately show ?thesis by blast
qed

lemmas realisation_simps =
  realisation_Empty realisation_Union realisation_Inter realisation_Diff realisation_Single

end

subsubsection \<open>Coherence\<close>

lemma (in open_branch) I\<^sub>s\<^sub>t_realisation_eq_realisation:
  assumes "sat b" "t \<in> subterms b"
  shows "I\<^sub>s\<^sub>t (\<lambda>x. realise (Var x)) t = realise t"
  using assms
  by (induction t) (force simp: realisation_simps dest: subterms_branchD)+

lemma (in open_branch) coherence:
  assumes "sat b" "\<phi> \<in> set b"
  shows "interp I\<^sub>s\<^sub>a (\<lambda>x. realise (Var x)) \<phi>"
  using assms
proof(induction "size \<phi>" arbitrary: \<phi> rule: less_induct)
  case less
  then show ?case
  proof(cases \<phi>)
    case (Atom a)
    then show ?thesis
    proof(cases a)
      case (Elem s t)
      with Atom less have "s \<in> subterms b" "t \<in> subterms b"
        using AT_mem_subterms_branchD by blast+
      with Atom Elem less show ?thesis
        using I\<^sub>s\<^sub>t_realisation_eq_realisation[OF \<open>sat b\<close>] realisation_if_AT_mem by auto
    next
      case (Equal s t)
      with Atom less have "s \<in> subterms b" "t \<in> subterms b"
        using AT_eq_subterms_branchD by blast+
      with Atom Equal less satD(1)[OF \<open>sat b\<close>] show ?thesis
        using I\<^sub>s\<^sub>t_realisation_eq_realisation[OF \<open>sat b\<close>] realisation_if_AT_eq by auto
    qed
  next
    case (And \<phi>1 \<phi>2)
    with \<open>\<phi> \<in> set b\<close> \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "\<phi>1 \<in> set b" "\<phi>2 \<in> set b"
      using lexpands_fm.intros(1)[THEN lexpands.intros(1)] by fastforce+
    with And less show ?thesis by simp
  next
    case (Or \<phi>1 \<phi>2)
    with \<open>\<phi> \<in> set b\<close> \<open>sat b\<close>[THEN satD(2)] have "\<phi>1 \<in> set b \<or> Neg \<phi>1 \<in> set b"
      using bexpands_nowit.intros(1)[THEN bexpands.intros(1)]
      by blast
    with less Or \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "\<phi>1 \<in> set b \<or> \<phi>2 \<in> set b"
      using lexpands_fm.intros(3)[THEN lexpands.intros(1)] by fastforce
    with Or less show ?thesis
      by force
  next
    case (Neg \<phi>')
    show ?thesis
    proof(cases \<phi>')
      case (Atom a)
      then show ?thesis
      proof(cases a)
        case (Elem s t)
        with Atom Neg less have "s \<in> subterms b" "t \<in> subterms b"
          using AF_mem_subterms_branchD by blast+
        with Neg Atom Elem less show ?thesis
          using I\<^sub>s\<^sub>t_realisation_eq_realisation realisation_if_AF_mem \<open>sat b\<close> by auto
      next
        case (Equal s t)
        with Atom Neg less have "s \<in> subterms b" "t \<in> subterms b"
          using AF_eq_subterms_branchD by blast+
        with Neg Atom Equal less show ?thesis
          using I\<^sub>s\<^sub>t_realisation_eq_realisation realisation_if_AF_eq \<open>sat b\<close> by auto
      qed
    next
      case (And \<phi>1 \<phi>2)
      with Neg \<open>sat b\<close>[THEN satD(2)] less have "\<phi>1 \<in> set b \<or> Neg \<phi>1 \<in> set b"
        using bexpands_nowit.intros(2)[THEN bexpands.intros(1)] by blast
      with \<open>sat b\<close>[THEN satD(1), THEN lin_satD] Neg And less
      have "Neg \<phi>2 \<in> set b \<or> Neg \<phi>1 \<in> set b"
        using lexpands_fm.intros(5)[THEN lexpands.intros(1)] by fastforce
      with Neg And less show ?thesis by force
    next
      case (Or \<phi>1 \<phi>2)
      with \<open>\<phi> \<in> set b\<close> Neg \<open>sat b\<close>[THEN satD(1), THEN lin_satD]
      have "Neg \<phi>1 \<in> set b" "Neg \<phi>2 \<in> set b"
        using lexpands_fm.intros(2)[THEN lexpands.intros(1)] by fastforce+
      moreover have "size (Neg \<phi>1) < size \<phi>" "size (Neg \<phi>2) < size \<phi>"
        using Neg Or by simp_all
      ultimately show ?thesis using Neg Or less by force
    next
      case Neg': (Neg \<phi>'')
      with \<open>\<phi> \<in> set b\<close> Neg \<open>sat b\<close>[THEN satD(1), THEN lin_satD] have "\<phi>'' \<in> set b"
        using lexpands_fm.intros(7)[THEN lexpands.intros(1)] by fastforce+
      with Neg Neg' less show ?thesis by simp
    qed
  qed
qed


subsection \<open>Soundness of the Calculus\<close>

subsubsection \<open>Soundness of Closedness\<close>

lemmas wf_trancl_hmem_rel = wf_trancl[OF wf_hmem_rel]

lemma trancl_hmem_rel_not_refl: "(x, x) \<notin> hmem_rel\<^sup>+"
  using wf_trancl_hmem_rel by simp

lemma mem_trancl_elts_rel_if_member_seq:
  assumes "member_seq s cs t"
  assumes "cs \<noteq> []"
  assumes "\<forall>a \<in> set cs. I\<^sub>s\<^sub>a M a"
  shows "(I\<^sub>s\<^sub>t M s, I\<^sub>s\<^sub>t M t) \<in> hmem_rel\<^sup>+"
  using assms
proof(induction rule: member_seq.induct)
  case (2 s s' u cs t)
  show ?case
  proof(cases cs)
    case Nil
    with 2 show ?thesis
      unfolding hmem_rel_def by auto
  next
    case (Cons c cs')
    with 2 have "(I\<^sub>s\<^sub>t M u, I\<^sub>s\<^sub>t M t) \<in> hmem_rel\<^sup>+"
      by simp
    moreover from 2 have "I\<^sub>s\<^sub>a M (s \<in>\<^sub>s u)"
      by simp
    ultimately show ?thesis
      unfolding hmem_rel_def by (simp add: trancl_into_trancl2)
  qed
qed simp_all

lemma bclosed_sound:
  assumes "bclosed b"
  shows "\<exists>\<phi> \<in> set b. \<not> interp I\<^sub>s\<^sub>a M \<phi>"
  using assms
proof -
  have False if "\<forall>\<phi> \<in> set b. interp I\<^sub>s\<^sub>a M \<phi>"
    using assms that
  proof(induction rule: bclosed.induct)
    case (memberCycle cs b)
    then have "\<forall>a \<in> set cs. I\<^sub>s\<^sub>a M a"
      unfolding Atoms_def by fastforce
    from memberCycle obtain s where "member_seq s cs s"
      using member_cycle.elims(2) by blast
    with memberCycle \<open>\<forall>a \<in> set cs. I\<^sub>s\<^sub>a M a\<close> have "(I\<^sub>s\<^sub>t M s, I\<^sub>s\<^sub>t M s) \<in> hmem_rel\<^sup>+"
      using mem_trancl_elts_rel_if_member_seq member_cycle.simps(2) by blast  
    with trancl_hmem_rel_not_refl show ?case
      by blast
  qed (use interp.simps(4) in \<open>fastforce+\<close>)
  then show ?thesis
    by blast
qed

lemma types_term_lt_if_member_seq:
  includes Set_member_no_ascii_notation
  fixes cs :: "'a pset_atom list"
  assumes "\<forall>a \<in> set cs. v \<turnstile> a"
  assumes "member_seq s cs t" "cs \<noteq> []"
  shows "\<exists>ls lt. v \<turnstile> s : ls \<and> v \<turnstile> t : lt \<and> ls < lt"
  using assms
proof(induction s cs t rule: member_seq.induct)
  case (2 s s' u cs t)
  then show ?case
  proof(cases cs)
    case (Cons c cs')
    with 2 obtain lu lt where "v \<turnstile> u : lu" "v \<turnstile> t : lt" "lu < lt"
      by auto
    moreover from 2 obtain ls where "v \<turnstile> s : ls" "ls < lu"
      using \<open>v \<turnstile> u : lu\<close> by (auto simp: types_pset_atom.simps dest: types_term_unique)
    ultimately show ?thesis
      by fastforce
  qed (fastforce simp: types_pset_atom.simps)
qed auto

lemma no_member_cycle_if_types_last:
  fixes b :: "'a branch"
  assumes "wf_branch b"
  assumes "\<exists>v. v \<turnstile> last b"
  shows "\<not> (member_cycle cs \<and> set cs \<subseteq> Atoms (set b))"
proof
  presume "member_cycle cs" "set cs \<subseteq> Atoms (set b)"
  then obtain s where "member_seq s cs s" "cs \<noteq> []"
    using member_cycle.elims(2) by blast
  moreover from assms obtain v where "\<forall>\<phi> \<in> set b. v \<turnstile> \<phi>"
    using types_urelems by blast
  with \<open>set cs \<subseteq> Atoms (set b)\<close> have "\<forall>a \<in> set cs. v \<turnstile> a"
    unfolding Atoms_def by (auto dest!: types_fmD(6))
  ultimately show False
    using types_term_lt_if_member_seq types_term_unique by blast
qed simp_all

subsubsection \<open>Soundness of the Expansion Rules\<close>

lemma lexpands_sound:
  assumes "lexpands b' b"
  assumes "\<phi> \<in> set b'"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "interp I\<^sub>s\<^sub>a M \<phi>"
  using assms
proof(induction rule: lexpands.induct)
  case (1 b' b)
  then show ?case
    by (induction rule: lexpands_fm.induct)
       (metis empty_iff empty_set interp.simps(2,3,4) set_ConsD)+
next
  case (2 b' b)
  then show ?case
  proof(induction rule: lexpands_un.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  qed force+
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lexpands_int.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case
      by force
  qed force+
next
  case (4 b' b)
  then show ?case
  proof(induction rule: lexpands_diff.induct)
    case (4 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case by force
  next
    case (5 s t1 t2 branch)
    with this(1)[THEN this(4)] show ?case by force
  qed force+
next
  case (5 b' b)
  then show ?case
    by (induction rule: lexpands_single.induct) force+
next
  case (6 b' b)
  then show ?case
  proof(induction rule: lexpands_eq_induct')
    case (subst t1 t2 t1' t2' p l b)
    with this(1,2)[THEN this(6)] show ?case
      by (cases l; cases p) auto
  next
    case (neq s t s' b)
    with this(1,2)[THEN this(4)] show ?case by force
  qed
qed

lemma bexpands_nowit_sound:
  assumes "bexpands_nowit bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>b' \<in> bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
  by (induction rule: bexpands_nowit.induct) force+

lemma I\<^sub>s\<^sub>t_upd_eq_if_not_mem_vars_term:
  assumes "x \<notin> vars t"
  shows "I\<^sub>s\<^sub>t (M(x := y)) t = I\<^sub>s\<^sub>t M t"
  using assms by (induction t) auto

lemma I\<^sub>s\<^sub>a_upd_eq_if_not_mem_vars_atom:
  assumes "x \<notin> vars a"
  shows "I\<^sub>s\<^sub>a (M(x := y)) a = I\<^sub>s\<^sub>a M a"
  using assms
  by (cases a) (auto simp: I\<^sub>s\<^sub>t_upd_eq_if_not_mem_vars_term)

lemma interp_upd_eq_if_not_mem_vars_fm:
  assumes "x \<notin> vars \<phi>"
  shows "interp I\<^sub>s\<^sub>a (M(x := y)) \<phi> = interp I\<^sub>s\<^sub>a M \<phi>"
  using assms
  by (induction \<phi>) (auto simp: I\<^sub>s\<^sub>a_upd_eq_if_not_mem_vars_atom)

lemma bexpands_wit_sound:
  assumes "bexpands_wit s t x bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>M. \<exists>b' \<in> bs'. \<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
proof (induction rule: bexpands_wit.induct)
  let ?bs'="{[AT (Var x \<in>\<^sub>s s), AF (Var x \<in>\<^sub>s t)],
             [AT (Var x \<in>\<^sub>s t), AF (Var x \<in>\<^sub>s s)]}"
  case (1 b)
  with this(1)[THEN this(9)] have "I\<^sub>s\<^sub>t M s \<noteq> I\<^sub>s\<^sub>t M t"
    by auto
  then obtain y where y:
    "y \<^bold>\<in> I\<^sub>s\<^sub>t M s \<and> y \<^bold>\<notin> I\<^sub>s\<^sub>t M t \<or>
     y \<^bold>\<in> I\<^sub>s\<^sub>t M t \<and> y \<^bold>\<notin> I\<^sub>s\<^sub>t M s"
    by auto
  have "x \<notin> vars s" "x \<notin> vars t"
    using 1 by (auto simp: vars_fm_vars_branchI)
  then have "I\<^sub>s\<^sub>t (M(x := y)) s = I\<^sub>s\<^sub>t M s" "I\<^sub>s\<^sub>t (M(x := y)) t = I\<^sub>s\<^sub>t M t"
    using I\<^sub>s\<^sub>t_upd_eq_if_not_mem_vars_term by metis+
  then have "\<exists>b' \<in> ?bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a (M(x := y)) \<psi>"
    using 1 y by auto
  moreover have "\<forall>\<psi> \<in> set b. interp I\<^sub>s\<^sub>a (M(x := y)) \<psi>"
    using "1"(9) \<open>x \<notin> vars b\<close> interp_upd_eq_if_not_mem_vars_fm
    by (metis vars_fm_vars_branchI)
  ultimately show ?case
    by auto (metis fun_upd_same)+
qed

lemma bexpands_sound:
  assumes "bexpands bs' b"
  assumes "\<And>\<psi>. \<psi> \<in> set b \<Longrightarrow> interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<exists>M. \<exists>b' \<in> bs'. \<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M \<psi>"
  using assms
proof(induction rule: bexpands.induct)
  case (1 bs' b)
  with bexpands_nowit_sound[OF this(1)] have "\<exists>b' \<in> bs'. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>"
    by blast
  with 1 show ?case
    by auto
next
  case (2 t1 t2 x bs b)
  then show ?case using bexpands_wit_sound by metis
qed


subsection \<open>Upper Bounding the Cardinality of a Branch\<close>

lemma Ex_bexpands_wits_if_in_wits:
  assumes "wf_branch b"
  assumes "x \<in> wits b"
  obtains t1 t2 bs b2 b1 where
    "expandss b (b2 @ b1)" "bexpands_wit t1 t2 x bs b1" "b2 \<in> bs" "expandss b1 [last b]"
    "x \<notin> wits b1" "wits (b2 @ b1) = insert x (wits b1)"
proof -
  from assms obtain \<phi> where "expandss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have "last b = \<phi>"
    by simp
  from \<open>expandss b [\<phi>]\<close> \<open>x \<in> wits b\<close> that show ?thesis
    unfolding \<open>last b = \<phi>\<close>
  proof(induction b "[\<phi>]" rule: expandss.induct)
    case 1
    then show ?case by simp
  next
    case (2 b2 b1)
    with expandss_mono have "b1 \<noteq> []"
      by fastforce
    with lexpands_wits_eq[OF \<open>lexpands b2 b1\<close> this] 2 show ?case
      by (metis (no_types, lifting) expandss.intros(2))
  next
    case (3 bs _ b2)
    then show ?case
    proof(induction rule: bexpands.induct)
      case (1 bs b1)
      with expandss_mono have "b1 \<noteq> []"
        by fastforce
      with bexpands_nowit_wits_eq[OF \<open>bexpands_nowit bs b1\<close> \<open>b2 \<in> bs\<close> this] 1 show ?case
        by (metis bexpands.intros(1) expandss.intros(3))
    next
      case (2 t1 t2 y bs b1)
      show ?case
      proof(cases "x \<in> wits b1")
        case True
        from 2 have "expandss (b2 @ b1) b1"
          using expandss.intros(3)[OF _ "2.prems"(1)] bexpands.intros(2)[OF "2.hyps"]
          by (metis expandss.intros(1))
        with True 2 show ?thesis
          using expandss_trans by blast
      next
        case False
        from 2 have "b1 \<noteq> []"
          using expandss_mono by fastforce
        with bexpands_witD[OF "2"(1)] "2"(2-) have "wits (b2 @ b1) = insert y (wits b1)"
          unfolding wits_def
          by (metis "2.hyps" bexpands_wit_wits_eq wits_def)
        moreover from \<open>y \<notin> vars_branch b1\<close> have "y \<notin> wits b1"
          unfolding wits_def by simp
        moreover from calculation have "y = x"
          using False 2 by simp
        ultimately show ?thesis
          using 2 by (metis expandss.intros(1))
      qed
    qed
  qed
qed

lemma card_wits_ub_if_wf_branch:
  assumes "wf_branch b"
  shows "card (wits b) \<le> (card (subterms (last b)))\<^sup>2"
proof -
  from assms obtain \<phi> where "expandss b [\<phi>]"
    unfolding wf_branch_def by blast
  with wf_branch_not_Nil[OF assms] have [simp]: "last b = \<phi>"
    using expandss_last_eq by force
  have False if card_gt: "card (wits b) > (card (subterms \<phi>))\<^sup>2"
  proof -
    define ts where "ts \<equiv> (\<lambda>x. SOME t1_t2. \<exists>bs b2 b1.
       expandss b (b2 @ b1) \<and> b2 \<in> bs \<and> bexpands_wit (fst t1_t2) (snd t1_t2) x bs b1  \<and> expandss b1 [\<phi>])"
    from \<open>expandss b [\<phi>]\<close> \<open>last b = \<phi>\<close>
    have *: "\<exists>t1_t2 bs b2 b1.
      expandss b (b2 @ b1) \<and> b2 \<in> bs \<and> bexpands_wit (fst t1_t2) (snd t1_t2) x bs b1 \<and> expandss b1 [\<phi>]"
      if "x \<in> wits b" for x
      using that Ex_bexpands_wits_if_in_wits[OF \<open>wf_branch b\<close> that] by (metis fst_conv snd_conv)
    have ts_wd:
      "\<exists>bs b2 b1. expandss b (b2 @ b1) \<and> b2 \<in> bs \<and> bexpands_wit t1 t2 x bs b1 \<and> expandss b1 [\<phi>]"
      if "ts x = (t1, t2)" "x \<in> wits b" for t1 t2 x
      using exE_some[OF * that(1)[THEN eq_reflection, symmetric, unfolded ts_def], OF that(2)]
      by simp
    with \<open>last b = \<phi>\<close> \<open>expandss b [\<phi>]\<close> have in_subterms_fm:
      "t1 \<in> subterms \<phi>" "t2 \<in> subterms \<phi>"
      if "ts x = (t1, t2)" "x \<in> wits b" for t1 t2 x
      using that bexpands_witD
      by (metis expandss_last_eq list.discI)+
    have "\<not> inj_on ts (wits b)"
    proof -
      from in_subterms_fm have "ts ` wits b \<subseteq> subterms \<phi> \<times> subterms \<phi>"
        by (intro subrelI) (metis imageE mem_Sigma_iff)
      then have "card (ts ` wits b) \<le> card (subterms \<phi> \<times> subterms \<phi>)"
        by (intro card_mono) (simp_all add: finite_subterms_fm)
      moreover have "card (subterms \<phi> \<times> subterms \<phi>) = (card (subterms \<phi>))\<^sup>2"
        unfolding card_cartesian_product by algebra
      ultimately show "\<not> inj_on ts (wits b)"
        using card_gt by (metis card_image linorder_not_less)
    qed
  
    from \<open>\<not> inj_on ts (wits b)\<close> obtain x t1 t2 xb1 xbs2 xb2 y yb1 ybs2 yb2 where x_y:
      "x \<noteq> y" "x \<in> wits b" "y \<in> wits b"
      "expandss xb1 [\<phi>]" "bexpands_wit t1 t2 x xbs2 xb1" "xb2 \<in> xbs2" "expandss b (xb2 @ xb1)"
      "expandss yb1 [\<phi>]" "bexpands_wit t1 t2 y ybs2 yb1" "yb2 \<in> ybs2" "expandss b (yb2 @ yb1)"
      unfolding inj_on_def by (metis ts_wd prod.exhaust)
    have "xb2 \<noteq> yb2"
      using x_y(5)[THEN bexpands_witD(1)] x_y(9)[THEN bexpands_witD(1)] x_y(1,6,10) 
      by auto
    moreover from x_y have "suffix (xb2 @ xb1) (yb2 @ yb1) \<or> suffix (yb2 @ yb1) (xb2 @ xb1)"
      using expandss_suffix suffix_same_cases by blast 
    then have "suffix (xb2 @ xb1) yb1 \<or> suffix (yb2 @ yb1) xb1"
      using x_y(5)[THEN bexpands_witD(1)] x_y(9)[THEN bexpands_witD(1)] x_y(1,6,10)
      by (auto simp: suffix_Cons)
    ultimately show False
      using bexpands_witD(1,5,6)[OF x_y(5)] bexpands_witD(1,5,6)[OF x_y(9)] x_y(6,10)
      by (auto dest!: set_mono_suffix)
  qed
  then show ?thesis
    using linorder_not_le \<open>last b = \<phi>\<close> by blast
qed

lemma card_subterms_branch_ub_if_wf_branch:
  assumes "wf_branch b"
  shows "card (subterms b) \<le> card (subterms (last b)) + card (wits b)"
  unfolding subterms_branch_eq_if_wf_branch[OF assms, unfolded wits_subterms_def]
  by (simp add: assms card_Un_disjoint card_image_le finite_wits finite_subterms_fm
                wits_subterms_last_disjnt)

lemma card_literals_branch_if_wf_branch:
  assumes "wf_branch b"
  shows "card {a \<in> set b. is_literal a}
       \<le> 2 * (2 * (card (subterms (last b)) + card (wits b))\<^sup>2)"
proof -
  have "card {a \<in> set b. is_literal a}
      \<le> card (pset_atoms_branch b) + card (pset_atoms_branch b)" (is "card ?A \<le> _")
  proof -
    have "?A = {AT a |a. AT a \<in> set b}
             \<union> {AF a |a. AF a \<in> set b}" (is "_ = ?ATs \<union> ?AFs")
      by auto (metis is_literal.elims(2))
    moreover have
      "?ATs \<subseteq> AT ` pset_atoms_branch b" "?AFs \<subseteq> AF ` pset_atoms_branch b"
      by force+
    moreover from calculation have "finite ?ATs" "finite ?AFs"
      by (simp_all add: finite_surj[OF finite_pset_atoms_branch])
    moreover have "?ATs \<inter> ?AFs = {}"
      by auto
    ultimately show ?thesis
      by (simp add: add_mono card_Un_disjoint finite_pset_atoms_branch surj_card_le)
  qed
  then have "card ?A \<le> 2 * card (pset_atoms_branch b)"
    by simp
  moreover
  have "atoms \<phi> \<subseteq>
    case_prod Elem ` (subterms \<phi> \<times> subterms \<phi>)
    \<union> case_prod Equal ` (subterms \<phi> \<times> subterms \<phi>)" for \<phi> :: "'a pset_fm"
  proof(induction \<phi>)
    case (Atom x)
    then show ?case by (cases x) auto
  qed auto
  then have "pset_atoms_branch b \<subseteq>
    case_prod Elem ` (subterms b \<times> subterms b)
    \<union> case_prod Equal ` (subterms b \<times> subterms b)" (is "_ \<subseteq> ?Els \<union> ?Eqs")
    unfolding subterms_branch_def
    by force
  have "card (pset_atoms_branch b)
    \<le> (card (subterms b))\<^sup>2 + (card (subterms b))\<^sup>2"
  proof -
    from finite_subterms_branch have "finite (subterms b \<times> subterms b)"
      using finite_cartesian_product by auto
    then have "finite ?Els" "finite ?Eqs"
      by blast+
    moreover have "inj_on (case_prod Elem) A" "inj_on (case_prod Equal) A"
      for A :: "('a pset_term \<times> 'a pset_term) set"
      unfolding inj_on_def by auto
    ultimately have "card ?Els = (card (subterms b))\<^sup>2" "card ?Eqs = (card (subterms b))\<^sup>2"
      using card_image[where ?A="subterms b \<times> subterms b"] card_cartesian_product
      unfolding power2_eq_square by metis+
    with card_mono[OF _ \<open>pset_atoms_branch b \<subseteq> ?Els \<union> ?Eqs\<close>] show ?thesis
      using \<open>finite ?Els\<close> \<open>finite ?Eqs\<close>
      by (metis card_Un_le finite_UnI sup.boundedE sup_absorb2)
  qed
  then have "card (pset_atoms_branch b) \<le> 2 * (card (subterms b))\<^sup>2"
    by simp
  ultimately show ?thesis
    using card_subterms_branch_ub_if_wf_branch[OF assms]
    by (meson dual_order.trans mult_le_mono2 power2_nat_le_eq_le)
qed

lemma lexpands_not_literal_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi> \<in> set b. \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "lexpands b' b" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
  by (induction b' b rule: lexpands_induct) (fastforce simp: P_def dest: subfmsD)+

lemma bexpands_not_literal_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi> \<in> set b. \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "bexpands bs b" "b' \<in> bs" "b \<noteq> []"
  assumes "P b"
  shows "P (b' @ b)"
  using assms(2-)
proof(induction bs b rule: bexpands.induct)
  case (1 bs' b)
  then show ?case
    apply(induction rule: bexpands_nowit.induct)
        apply(fastforce simp: P_def dest: subfmsD)+
    done
next
  case (2 t1 t2 x bs' b)
  then show ?case
    apply(induction rule: bexpands_wit.induct)
    apply(fastforce simp: P_def dest: subfmsD)+
    done
qed

lemma expandss_not_literal_mem_subfms_last:
  defines "P \<equiv> (\<lambda>b. \<forall>\<psi> \<in> set b. \<not> is_literal \<psi>
                          \<longrightarrow> \<psi> \<in> subfms (last b) \<or> \<psi> \<in> Neg ` subfms (last b))"
  assumes "expandss b' b" "b \<noteq> []"
  assumes "P b"
  shows "P b'"
  using assms(2-)
proof(induction b' b rule: expandss.induct)
  case (2 b3 b2 b1)
  then have "b2 \<noteq> []"
    using expandss_suffix suffix_bot.extremum_uniqueI by blast
  with 2 show ?case
    using lexpands_not_literal_mem_subfms_last unfolding P_def by blast
next
  case (3 bs b2 b3 b1)
  then have "b2 \<noteq> []"
    using expandss_suffix suffix_bot.extremum_uniqueI by blast
  with 3 show ?case
    using bexpands_not_literal_mem_subfms_last unfolding P_def by blast
qed simp

lemma card_not_literal_branch_if_wf_branch:
  assumes "wf_branch b"
  shows "card {\<phi> \<in> set b. \<not> is_literal \<phi>} \<le> 2 * card (subfms (last b))"
proof -
  from assms obtain \<phi> where "expandss b [\<phi>]"
    unfolding wf_branch_def by blast
  then have [simp]: "last b = \<phi>"
    by simp
  have "{\<psi> \<in> set b. \<not> is_literal \<psi>} \<subseteq> subfms \<phi> \<union> Neg ` subfms \<phi>"
    using expandss_not_literal_mem_subfms_last[OF \<open>expandss b [\<phi>]\<close>]
    by auto
  from card_mono[OF _ this] have
    "card {\<psi> \<in> set b. \<not> is_literal \<psi>} \<le> card (subfms \<phi> \<union> Neg ` subfms \<phi>)"
    using finite_subfms finite_imageI by fast
  also have "\<dots> \<le> card (subfms \<phi>) + card (Neg ` subfms \<phi>)"
    using card_Un_le by blast
  also have "\<dots> \<le> 2 * card (subfms \<phi>)"
    unfolding mult_2 by (simp add: card_image_le finite_subfms)
  finally show ?thesis
    by simp
qed

lemma card_wf_branch_ub:
  assumes "wf_branch b"
  shows "card (set b)
      \<le> 2 * card (subfms (last b)) + 16 * (card (subterms (last b)))^4"
proof -
  let ?csts = "card (subterms (last b))"
  have "set b = {\<psi> \<in> set b. \<not> is_literal \<psi>} \<union> {\<psi> \<in> set b. is_literal \<psi>}"
    by auto
  then have "card (set b)
    = card ({\<psi> \<in> set b. \<not> is_literal \<psi>}) + card ({\<psi> \<in> set b. is_literal \<psi>})"
    using card_Un_disjoint finite_Un
    by (metis (no_types, lifting) List.finite_set disjoint_iff mem_Collect_eq)
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 4 * (?csts + card (wits b))\<^sup>2"
    using assms card_literals_branch_if_wf_branch card_not_literal_branch_if_wf_branch
    by fastforce
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 4 * (?csts + ?csts\<^sup>2)\<^sup>2"
    using assms card_wits_ub_if_wf_branch by auto
  also have "\<dots> \<le> 2 * card (subfms (last b)) + 16 * ?csts^4"
  proof -
    have "1 \<le> ?csts"
      using finite_subterms_fm[THEN card_0_eq]
      by (auto intro: Suc_leI)
    then have "(?csts + ?csts\<^sup>2)\<^sup>2 = ?csts\<^sup>2 + 2 * ?csts^3 + ?csts^4"
      by algebra
    also have "\<dots> \<le> ?csts\<^sup>2 + 2 * ?csts^4 + ?csts^4"
      using power_increasing[OF _ \<open>1 \<le> ?csts\<close>] by simp
    also have "\<dots> \<le> ?csts^4 + 2 * ?csts^4 + ?csts^4"
      using power_increasing[OF _ \<open>1 \<le> ?csts\<close>] by simp
    also have "\<dots> \<le> 4 * ?csts^4"
      by simp
    finally show ?thesis
      by simp
  qed
  finally show ?thesis .
qed


subsection \<open>The Decision Procedure\<close>

locale mlss_proc =
  fixes lexpand :: "'a branch \<Rightarrow> 'a branch"
  assumes lexpands_lexpand:
    "\<not> lin_sat b \<Longrightarrow> lexpands (lexpand b) b \<and> set b \<subset> set (lexpand b @ b)"
  fixes bexpand :: "'a branch \<Rightarrow> 'a branch set"
  assumes bexpands_bexpand:
    "\<not> sat b \<Longrightarrow> lin_sat b \<Longrightarrow> bexpands (bexpand b) b"
begin

function (domintros) mlss_proc_branch :: "'a branch \<Rightarrow> bool" where
  "\<not> lin_sat b
  \<Longrightarrow> mlss_proc_branch b = mlss_proc_branch (lexpand b @ b)"
| "\<lbrakk> lin_sat b; bclosed b \<rbrakk> \<Longrightarrow> mlss_proc_branch b = True"
| "\<lbrakk> \<not> sat b; bopen b; lin_sat b \<rbrakk>
  \<Longrightarrow> mlss_proc_branch b = (\<forall>b' \<in> bexpand b. mlss_proc_branch (b' @ b))"
| "\<lbrakk> lin_sat b; sat b \<rbrakk> \<Longrightarrow> mlss_proc_branch b = bclosed b"
  by auto

lemma mlss_proc_branch_dom_if_wf_branch:
  assumes "wf_branch b"
  shows "mlss_proc_branch_dom b"
proof -
  define card_ub :: "'a branch \<Rightarrow> nat" where
    "card_ub \<equiv> \<lambda>b. 2 * card (subfms (last b)) + 16 * (card (subterms (last b)))^4"
  from assms show ?thesis
  proof(induction "card_ub b - card (set b)"
      arbitrary: b rule: less_induct)
    case less
    have less': "mlss_proc_branch_dom b'" if "set b \<subset> set b'" "expandss b' b" for b'
    proof -
      note expandss_last_eq[OF \<open>expandss b' b\<close> wf_branch_not_Nil[OF \<open>wf_branch b\<close>]] 
      then have "card_ub b' = card_ub b"
        unfolding card_ub_def by simp
      moreover from that \<open>wf_branch b\<close> have "wf_branch b'"
        by (meson expandss_trans wf_branch_def)
      ultimately have "mlss_proc_branch_dom b'" if "card (set b') > card (set b)"
        using less(1)[OF _ \<open>wf_branch b'\<close>] card_wf_branch_ub that
        by (metis (no_types, lifting) card_ub_def diff_less_mono2 order_less_le_trans)
      with that show ?thesis
        by (simp add: psubset_card_mono)
    qed
    then show ?case
    proof(cases "sat b")
      case False
      then consider
        b' where  "\<not> lin_sat b" "lexpands b' b" "set b \<subset> set (b' @ b)" |
        bs' where "lin_sat b" "\<not> sat b" "bexpands bs' b" "bs' \<noteq> {}"
                  "\<forall>b' \<in> bs'. set b \<subset> set (b' @ b)"
        unfolding sat_def lin_sat_def
        using bexpands_strict_mono bexpands_nonempty
        by (metis (no_types, opaque_lifting) inf_sup_aci(5) psubsetI set_append sup_ge1)
      then show ?thesis
      proof(cases)
        case 1
        with less' show ?thesis 
          using mlss_proc_branch.domintros(1)
          by (metis expandss.intros(1,2) lexpands_lexpand)
      next
        case 2
        then show ?thesis
          using less' bexpands_bexpand mlss_proc_branch.domintros(2,3)
          by (metis bexpands_strict_mono expandss.intros(1,3))
      qed
    qed (use mlss_proc_branch.domintros(4) sat_def in metis)
  qed
qed

definition mlss_proc :: "'a pset_fm \<Rightarrow> bool" where
  "mlss_proc \<phi> \<equiv> mlss_proc_branch [\<phi>]"

lemma mlss_proc_branch_complete:
  fixes b :: "'a branch"
  assumes "wf_branch b" "\<exists>v. v \<turnstile> last b"
  assumes "\<not> mlss_proc_branch b"
  assumes "infinite (UNIV :: 'a set)"
  shows "\<exists>M. interp I\<^sub>s\<^sub>a M (last b)"
proof -
  from mlss_proc_branch_dom_if_wf_branch[OF assms(1)] assms(1,2,3)
  show ?thesis
  proof(induction rule: mlss_proc_branch.pinduct)
    case (1 b)
    let ?b' = "lexpand b"
    from 1 lexpands_lexpand have "wf_branch (?b' @ b)"
      using wf_branch_lexpands by blast
    moreover from 1 lexpands_lexpand have "\<not> mlss_proc_branch (?b' @ b)"
      by (simp add: mlss_proc_branch.psimps)
    ultimately obtain M where "interp I\<^sub>s\<^sub>a M (last (?b' @ b))"
      using 1 by auto
    with 1 show ?case
      using wf_branch_not_Nil by auto
  next
    case (2 b)
    then show ?case by (simp add: mlss_proc_branch.psimps)
  next
    case (3 b)
    let ?bs' = "bexpand b"
    from 3 bexpands_bexpand obtain b' where b': "b' \<in> ?bs'" "\<not> mlss_proc_branch (b' @ b)"
      using mlss_proc_branch.psimps(3) by metis
    with 3 bexpands_bexpand have "wf_branch (b' @ b)"
      using wf_branch_expandss[OF \<open>wf_branch b\<close> expandss.intros(3)]
      using expandss.intros(1) by blast
    with 3 b' obtain M where "interp I\<^sub>s\<^sub>a M (last (b' @ b))"
      by auto
    with 3 show ?case
      by auto
  next
    case (4 b)
    then have "bopen b"
      by (simp add: mlss_proc_branch.psimps)
    interpret open_branch b
      using \<open>wf_branch b\<close> \<open>\<exists>v. v \<turnstile> last b\<close> \<open>bopen b\<close> \<open>infinite UNIV\<close>
      by unfold_locales assumption+
    from coherence[OF \<open>sat b\<close> last_in_set] show ?case
      using wf_branch wf_branch_not_Nil by blast
  qed
qed

lemma mlss_proc_branch_sound:
  assumes "wf_branch b"
  assumes "\<forall>\<psi> \<in> set b. interp I\<^sub>s\<^sub>a M \<psi>"
  shows "\<not> mlss_proc_branch b"
proof
  assume "mlss_proc_branch b"
  with mlss_proc_branch_dom_if_wf_branch[OF \<open>wf_branch b\<close>]
  have "\<exists>b'. expandss b' b \<and> (\<exists>M. \<forall>\<psi> \<in> set b'. interp I\<^sub>s\<^sub>a M \<psi>) \<and> bclosed b'"
    using assms
  proof(induction arbitrary: M rule: mlss_proc_branch.pinduct)
    case (1 b)
    let ?b' = "lexpand b"
    from 1 lexpands_lexpand \<open>wf_branch b\<close> have "wf_branch (?b' @ b)"
      using wf_branch_lexpands by metis
    with 1 lexpands_sound lexpands_lexpand obtain b'' where
      "expandss b'' (?b' @ b)" "\<exists>M. \<forall>\<psi> \<in> set b''. interp I\<^sub>s\<^sub>a M \<psi>" "bclosed b''"
      by (fastforce simp: mlss_proc_branch.psimps)
    with 1 lexpands_lexpand show ?case
      using expandss_trans expandss.intros(1,2) by meson
  next
    case (3 b)
    let ?bs' = "bexpand b"
    from 3 \<open>wf_branch b\<close> bexpands_bexpand have wf_branch_b':
      "wf_branch (b' @ b)" if "b' \<in> ?bs'" for b'
      using that expandss.intros(3) wf_branch_def by metis
    from bexpands_sound bexpands_bexpand 3 obtain M' b' where
      "b' \<in> ?bs'" "\<forall>\<psi> \<in> set (b' @ b). interp I\<^sub>s\<^sub>a M' \<psi>"
      by metis
    with "3.IH" \<open>mlss_proc_branch b\<close> wf_branch_b' obtain b'' where
      "b' \<in> ?bs'" "expandss b'' (b' @ b)"
      "\<exists>M. \<forall>\<psi> \<in> set b''. interp I\<^sub>s\<^sub>a M \<psi>" "bclosed b''"
      using mlss_proc_branch.psimps(3)[OF "3.hyps"(2-4,1)] by blast
    with 3 bexpands_bexpand show ?case
      using expandss_trans expandss.intros(1,3) by metis
  qed (use expandss.intros(1) mlss_proc_branch.psimps(4) in \<open>blast+\<close>)
  with bclosed_sound show False by blast
qed

theorem mlss_proc_complete:
  fixes \<phi> :: "'a pset_fm"
  assumes "\<not> mlss_proc \<phi>"
  assumes "\<exists>v. v \<turnstile> \<phi>"
  assumes "infinite (UNIV :: 'a set)"
  shows "\<exists>M. interp I\<^sub>s\<^sub>a M \<phi>"
  using assms mlss_proc_branch_complete[of "[\<phi>]"]
  unfolding mlss_proc_def by simp

theorem mlss_proc_sound:
  assumes "interp I\<^sub>s\<^sub>a M \<phi>"
  shows "\<not> mlss_proc \<phi>"
  using assms mlss_proc_branch_sound[of "[\<phi>]"]
  unfolding mlss_proc_def by simp

end

end
