theory MLSS_Typing
  imports MLSS_Calculus
begin

section \<open>Typing and Branch Expansion\<close>
text \<open>
  In this theory, we prove that the branch expansion rules
  preserve well-typedness.
\<close>

context includes Set_member_no_ascii_notation
begin

lemma types_term_unique:
  shows "v \<turnstile> t : l1 \<Longrightarrow> v \<turnstile> t : l2 \<Longrightarrow> l2 = l1"
  apply(induction arbitrary: l2 rule: types_pset_term.induct)
       apply (metis types_pset_term_cases)+
  done

lemma type_of_term_if_types_term:
  shows "v \<turnstile> t : l \<Longrightarrow> type_of_term v t = l"
  using types_term_unique unfolding type_of_term_def by blast

lemma types_term_if_mem_subterms_term:
  assumes "s \<in> subterms t"
  assumes "v \<turnstile> t : lt"
  shows "\<exists>ls. v \<turnstile> s : ls"
  using assms
  by (induction t arbitrary: s lt) (auto elim: types_pset_term_cases)

lemma is_Var_if_types_term_0:
  shows "v \<turnstile> t : 0 \<Longrightarrow> is_Var t"
  by (induction t) (auto elim: types_pset_term_cases)

lemma is_Var_if_urelem': "urelem' v \<phi> t \<Longrightarrow> is_Var t"
  using is_Var_if_types_term_0 by blast

lemma is_Var_if_urelem: "urelem \<phi> t \<Longrightarrow> is_Var t"
  unfolding urelem_def using is_Var_if_urelem' by blast

lemma types_fmD:
  "v \<turnstile> And p q \<Longrightarrow> v \<turnstile> p"
  "v \<turnstile> And p q \<Longrightarrow> v \<turnstile> q"
  "v \<turnstile> Or p q \<Longrightarrow> v \<turnstile> p"
  "v \<turnstile> Or p q \<Longrightarrow> v \<turnstile> q"
  "v \<turnstile> Neg p \<Longrightarrow> v \<turnstile> p"
  "v \<turnstile> Atom a \<Longrightarrow> v \<turnstile> a"
  unfolding types_pset_fm_def using fm.set_intros by auto

lemma types_fmI:
  "v \<turnstile> p \<Longrightarrow> v \<turnstile> q \<Longrightarrow> v \<turnstile> And p q"
  "v \<turnstile> p \<Longrightarrow> v \<turnstile> q \<Longrightarrow> v \<turnstile> Or p q"
  "v \<turnstile> p \<Longrightarrow> v \<turnstile> Neg p"
  "v \<turnstile> a \<Longrightarrow> v \<turnstile> Atom a"
  unfolding types_pset_fm_def using fm.set_intros by auto

lemma types_pset_atom_Member_D:
  includes Set_member_no_ascii_notation
  assumes "v \<turnstile> s \<in>\<^sub>s f t1 t2" "f \<in> {(\<squnion>\<^sub>s), (\<sqinter>\<^sub>s), (-\<^sub>s)}"
  shows "v \<turnstile> s \<in>\<^sub>s t1" "v \<turnstile> s \<in>\<^sub>s t2"
proof -
  from assms obtain ls where
    "v \<turnstile> s : ls" "v \<turnstile> f t1 t2 : Suc ls"
    using types_pset_atom.simps by fastforce
  with assms have "v \<turnstile> s \<in>\<^sub>s t1 \<and> v \<turnstile> s \<in>\<^sub>s t2"
    by (auto simp: types_pset_atom.simps elim: types_pset_term_cases)
  then show "v \<turnstile> s \<in>\<^sub>s t1" "v \<turnstile> s \<in>\<^sub>s t2"
    by blast+
qed

lemmas types_pset_atom_Member_Union_D = types_pset_atom_Member_D[where ?f="(\<squnion>\<^sub>s)", simplified]
   and types_pset_atom_Member_Inter_D = types_pset_atom_Member_D[where ?f="(\<sqinter>\<^sub>s)", simplified]
   and types_pset_atom_Member_Diff_D = types_pset_atom_Member_D[where ?f="(-\<^sub>s)", simplified]

lemma types_term_if_mem_subterms:
  includes Set_member_no_ascii_notation
  fixes \<phi> :: "'a pset_fm"
  assumes "v \<turnstile> \<phi>"
  assumes "f t1 t2 \<in> subterms \<phi>" "f \<in> {(\<squnion>\<^sub>s), (\<sqinter>\<^sub>s), (-\<^sub>s)}"
  obtains lt where "v \<turnstile> t1 : lt" "v \<turnstile> t2 : lt"
proof -
  from assms obtain a :: "'a pset_atom" where atom: "v \<turnstile> a" "f t1 t2 \<in> subterms a"
    unfolding types_pset_fm_def by (induction \<phi>) auto
  obtain t' l where "v \<turnstile> t' : l" "f t1 t2 \<in> subterms t'"
    apply(rule types_pset_atom.cases[OF \<open>v \<turnstile> a\<close>])
    using atom(2) by auto
  then obtain lt where "v \<turnstile> t1 : lt \<and> v \<turnstile> t2 : lt"
    by (induction t' arbitrary: l)
       (use assms(3) in \<open>auto elim: types_pset_term_cases\<close>)
  with that show ?thesis
    by blast
qed

lemma types_if_types_Member_and_subterms:
  fixes \<phi> :: "'a pset_fm"
  assumes "v \<turnstile> s \<in>\<^sub>s t1 \<or> v \<turnstile> s \<in>\<^sub>s t2" "v \<turnstile> \<phi>"
  assumes "f t1 t2 \<in> subterms \<phi>" "f \<in> {(\<squnion>\<^sub>s), (\<sqinter>\<^sub>s), (-\<^sub>s)}"
  shows "v \<turnstile> s \<in>\<^sub>s f t1 t2"
proof -
  from types_term_if_mem_subterms[OF assms(2-)] obtain lt where lt:
    "v \<turnstile> t1 : lt" "v \<turnstile> t2 : lt"
    by blast
  moreover from assms(1) lt(1,2) obtain ls where "v \<turnstile> s : ls" "lt = Suc ls"
    by (auto simp: types_pset_atom.simps dest: types_term_unique)
  ultimately show ?thesis
    using assms
    by (auto simp: types_pset_term.intros types_pset_atom.simps)
qed

lemma types_subst_tlvl:
  includes Set_member_no_ascii_notation
  fixes l :: "'a pset_atom"
  assumes "v \<turnstile> AT (t1 =\<^sub>s t2)" "v \<turnstile> l"
  shows "v \<turnstile> subst_tlvl t1 t2 l"
proof -
  from assms obtain lt where "v \<turnstile> t1 : lt" "v \<turnstile> t2 : lt"
    by (auto simp: types_pset_atom.simps dest!: types_fmD(6))
  with assms(2) show ?thesis
    by (cases "(t1, t2, l)" rule: subst_tlvl.cases)
       (auto simp: types_pset_atom.simps dest: types_term_unique)
qed

lemma types_sym_Equal:
  assumes "v \<turnstile> t1 =\<^sub>s t2"
  shows "v \<turnstile> t2 =\<^sub>s t1"
  using assms by (auto simp: types_pset_atom.simps)

lemma types_lexpands:
  fixes \<phi> :: "'a pset_fm"
  assumes "lexpands b' b" "b \<noteq> []" "\<phi> \<in> set b'"
  assumes "\<And>(\<phi> :: 'a pset_fm). \<phi> \<in> set b \<Longrightarrow> v \<turnstile> \<phi>"
  shows "v \<turnstile> \<phi>"
  using assms
proof(induction rule: lexpands.induct)
  case (1 b' b)
  then show ?case
    apply(induction rule: lexpands_fm.induct)
          apply(force dest: types_fmD intro: types_fmI(3))+
    done
next
  case (2 b' b)
  then show ?case
  proof(induction rule: lexpands_un.induct)
    case (1 s t1 t2 b)
    then show ?thesis
      by (auto dest!: types_fmD(5,6) "1"(4) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Union_D)
  next
    case (2 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 2 show ?case
      by (auto dest!: "2"(5) types_fmD(6) intro: types_fmI(4))
  next
    case (3 s t2 b t1)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 3 show ?case
      by (auto dest!: "3"(5) types_fmD(6) intro: types_fmI(4))
  next
    case (4 s t1 t2 b)
    then show ?case
      by (auto dest!: types_fmD(5,6) "4"(5) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Union_D)
  next
    case (5 s t1 t2 b)
    then show ?case
      by (auto dest!: types_fmD(5,6) "5"(5) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Union_D)
  next
    case (6 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    note types_if_types_Member_and_subterms[where ?f="(\<squnion>\<^sub>s)", OF _ this "6"(3), simplified]
    with 6 show ?case
      by (auto dest!: types_fmD(5,6) "6"(6) intro!: types_fmI(2,3,4))
  qed
next
  case (3 b' b)
  then show ?case
  proof(induction rule: lexpands_int.induct)
    case (1 s t1 t2 b)
    then show ?thesis
      by (auto dest!: types_fmD(5,6) "1"(4) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Inter_D)
  next
    case (2 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 2 show ?case
      by (auto dest!: "2"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (3 s t2 b t1)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 3 show ?case
      by (auto dest!: "3"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (4 s t1 t2 b)
    then show ?case
      by (auto dest!: types_fmD(5,6) "4"(5) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Inter_D)
  next
    case (5 s t1 t2 b)
    then show ?case
      by (auto dest!: types_fmD(5,6) "5"(5) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Inter_D)
  next
    case (6 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    note types_if_types_Member_and_subterms[where ?f="(\<sqinter>\<^sub>s)", OF _ this "6"(3), simplified]
    with 6 show ?case
      by (auto dest!: types_fmD(5,6) "6"(6) intro!: types_fmI(2,3,4))
  qed
next
  case (4 b' b)
  then show ?case
    proof(induction rule: lexpands_diff.induct)
    case (1 s t1 t2 b)
    then show ?thesis
      by (auto dest!: types_fmD(5,6) "1"(4) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Diff_D)
  next
    case (2 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 2 show ?case
      by (auto dest!: "2"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (3 s t2 b t1)
    then have "v \<turnstile> last b"
      by auto
    from types_if_types_Member_and_subterms[OF _ this] 3 show ?case
      by (auto dest!: "3"(5) types_fmD(5,6) intro!: types_fmI(3,4))
  next
    case (4 s t1 t2 b)
    then show ?case
      by (auto dest!: types_fmD(5,6) "4"(5) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Diff_D)
  next
    case (5 s t1 t2 b)
    then show ?case
      by (auto dest!: types_fmD(5,6) "5"(5) intro!: types_fmI(2,3,4)
               intro: types_pset_atom_Member_Diff_D)
  next
    case (6 s t1 b t2)
    then have "v \<turnstile> last b"
      by auto
    note types_if_types_Member_and_subterms[where ?f="(-\<^sub>s)", OF _ this "6"(3), simplified]
    with 6 show ?case
      by (auto dest!: types_fmD(5,6) "6"(6) intro!: types_fmI(2,3,4))
  qed
next
  case (5 b' b)
  then show ?case
  proof(cases rule: lexpands_single.cases)
    case (1 t1)
    with 5 have "v \<turnstile> last b"
      by auto
    with \<open>Single t1 \<in> subterms (last b)\<close> obtain a :: "'a pset_atom"
      where atom: "a \<in> atoms (last b)" "Single t1 \<in> subterms a" "v \<turnstile> a"
      unfolding types_pset_fm_def by (metis UN_E subterms_fm_def)
    obtain t' l where "Single t1 \<in> subterms t'" "v \<turnstile> t' : l" 
      apply(rule types_pset_atom.cases[OF \<open>v \<turnstile> a\<close>])
      using atom(2) by auto
    note types_term_if_mem_subterms_term[OF this]
    then obtain lt1 where "v \<turnstile> t1 : lt1" "v \<turnstile> Single t1 : Suc lt1"
      by (metis types_pset_term_cases(3))
    with 5 1 show ?thesis
      using types_pset_atom.intros(2) types_pset_fm_def by fastforce
  qed (auto simp: types_pset_atom.simps elim!: types_pset_term_cases
            dest!: types_fmD(5,6) "5"(4) intro!: types_fmI(3,4))
next
  case (6 b' b)
  then show ?case
  proof(cases rule: lexpands_eq.cases)
    case (5 s t s')
    with 6 show ?thesis
      by (auto 0 3 dest!: "6"(4) types_fmD(5,6) dest: types_term_unique
                   simp: types_pset_atom.simps types_term_unique intro!: types_fmI(3,4))
  qed (auto simp: types_sym_Equal dest!: "6"(4) types_fmD(5,6)
            intro!: types_fmI(3,4) types_subst_tlvl)
qed

lemma types_bexpands_nowit:
  fixes \<phi> :: "'a pset_fm"
  assumes "bexpands_nowit bs' b" "b' \<in> bs'" "\<phi> \<in> set b'"
  assumes "\<And>(\<phi> :: 'a pset_fm). \<phi> \<in> set b \<Longrightarrow> v \<turnstile> \<phi>"
  shows "v \<turnstile> \<phi>"
  using assms(1)
proof(cases rule: bexpands_nowit.cases)
  case (1 p q)
  from assms "1"(2) show ?thesis
    unfolding "1"(1)
    by (auto dest!: assms(4) types_fmD(3) intro!: types_fmI(3))
next
  case (2 p q)
  from assms "2"(2) show ?thesis
    unfolding "2"(1)
    by (auto dest!: assms(4) types_fmD(5) dest: types_fmD(1,2) intro!: types_fmI(3))
next
  case (3 s t1 t2)
  from assms "3"(2,3) show ?thesis
    unfolding "3"(1) using types_pset_atom_Member_Union_D(1)[of v s t1 t2]
    by (auto dest!: types_fmD(6) assms(4) intro!: types_fmI(3,4))
next
  case (4 s t1 t2)
  with assms have "v \<turnstile> last b"
    by (metis empty_iff empty_set last_in_set)
  from assms "4"(2,3) show ?thesis
    unfolding "4"(1)
    using types_if_types_Member_and_subterms[where ?f="(\<sqinter>\<^sub>s)", OF _ \<open>v \<turnstile> last b\<close> "4"(3),
                                             THEN types_pset_atom_Member_Inter_D(2)]
    by (force dest!: types_fmD(6) assms(4) intro!: types_fmI(3,4))
next
  case (5 s t1 t2)
  with assms have "v \<turnstile> last b"
    by (metis empty_iff empty_set last_in_set)
  from assms "5"(2,3) show ?thesis
    unfolding "5"(1)
    using types_if_types_Member_and_subterms[where ?f="(-\<^sub>s)", OF _ \<open>v \<turnstile> last b\<close> "5"(3),
                                             THEN types_pset_atom_Member_Diff_D(2)]
    by (force dest!: types_fmD(6) assms(4) intro!: types_fmI(3,4))
qed

lemma types_term_if_on_vars_eq:
  assumes "\<forall>x \<in> vars t. v' x = v x"
  shows "v' \<turnstile> t : l \<longleftrightarrow> v \<turnstile> t : l"
  using assms
  apply(induction t arbitrary: l)
       apply(auto intro!: types_pset_term_intros' types_pset_term.intros(4-) 
                  elim!: types_pset_term_cases) 
  done

lemma types_pset_atom_if_on_vars_eq:
  fixes a :: "'a pset_atom"
  assumes "\<forall>x \<in> vars a. v' x = v x"
  shows "v' \<turnstile> a \<longleftrightarrow> v \<turnstile> a"
  using assms
  by (auto simp: ball_Un types_pset_atom.simps dest!: types_term_if_on_vars_eq)

lemma types_pset_fm_if_on_vars_eq:
  fixes \<phi> :: "'a pset_fm"
  assumes "\<forall>x \<in> vars \<phi>. v' x = v x"
  shows "v' \<turnstile> \<phi> \<longleftrightarrow> v \<turnstile> \<phi>"
  using assms types_pset_atom_if_on_vars_eq
  unfolding types_pset_fm_def vars_fm_def by fastforce

lemma types_term_fun_upd:
  assumes "x \<notin> vars t"
  shows "v(x := l) \<turnstile> t : l \<longleftrightarrow> v \<turnstile> t : l"
  using assms types_term_if_on_vars_eq by (metis fun_upd_other)

lemma types_pset_atom_fun_upd:
  fixes a :: "'a pset_atom"
  assumes "x \<notin> vars a"
  shows "v(x := l) \<turnstile> a \<longleftrightarrow> v \<turnstile> a"
  using assms types_pset_atom_if_on_vars_eq by (metis fun_upd_other)

lemma types_pset_fm_fun_upd:
  fixes \<phi> :: "'a pset_fm"
  assumes "x \<notin> vars \<phi>"
  shows "v(x := l) \<turnstile> \<phi> \<longleftrightarrow> v \<turnstile> \<phi>"
  using assms types_pset_fm_if_on_vars_eq by (metis fun_upd_other)

lemma types_bexpands_wit:
  fixes b :: "'a branch" and bs' :: "'a branch set"
  assumes "bexpands_wit t1 t2 x bs' b" "b \<noteq> []"
  assumes "\<And>(\<phi> :: 'a pset_fm). \<phi> \<in> set b \<Longrightarrow> v \<turnstile> \<phi>"
  obtains l where "\<forall>\<phi> \<in> set b. v(x := l) \<turnstile> \<phi>"
                  "\<forall>b' \<in> bs'. \<forall>\<phi> \<in> set b'. v(x := l) \<turnstile> \<phi>"
  using assms(1)
proof(cases rule: bexpands_wit.cases)
  case 1
  from assms(3)[OF "1"(2)] obtain lt where lt: "v \<turnstile> t1 : lt" "v \<turnstile> t2 : lt"
    by (auto dest!: types_fmD simp: types_pset_atom.simps)
  with 1 assms(2,3) have "lt \<noteq> 0"
    unfolding urelem_def using last_in_set by metis
  with lt obtain ltp where ltp: "v \<turnstile> t1 : Suc ltp" "v \<turnstile> t2 : Suc ltp"
    using not0_implies_Suc by blast
  with assms(3) have "\<forall>\<phi> \<in> set b. v(x := ltp) \<turnstile> \<phi>"
    using types_pset_fm_fun_upd \<open>x \<notin> vars b\<close> by (metis vars_fm_vars_branchI)
  moreover from \<open>x \<notin> vars b\<close> \<open>AF (t1 =\<^sub>s t2) \<in> set b\<close> have not_in_vars: "x \<notin> vars t1" "x \<notin> vars t2"
    using assms(2) by (auto simp: vars_fm_vars_branchI)
  from this[THEN types_term_fun_upd] have "\<forall>b' \<in> bs'. \<forall>\<phi> \<in> set b'. v(x := ltp) \<turnstile> \<phi>"
    using ltp unfolding "1"(1) 
    apply(auto intro!: types_fmI types_pset_term_intros'(2) simp: types_pset_atom.simps)
    apply (metis fun_upd_same fun_upd_upd types_pset_term.intros(2))+
    done
  ultimately show ?thesis
    using that by blast
qed

lemma types_expandss:
  fixes b b' :: "'a branch"
  assumes "expandss b' b" "b \<noteq> []"
  assumes "\<And>\<phi>. \<phi> \<in> set b \<Longrightarrow> v \<turnstile> \<phi>"
  obtains v' where "\<forall>x \<in> vars b. v' x = v x" "\<forall>\<phi> \<in> set b'. v' \<turnstile> \<phi>"
  using assms
proof(induction b' b arbitrary: thesis rule: expandss.induct)
  case (1 b)
  then show ?case by blast
next
  case (2 b3 b2 b1)
  then obtain v' where v': "\<forall>x \<in> vars b1. v' x = v x" "\<forall>\<phi> \<in> set b2. v' \<turnstile> \<phi>"
    by blast
  with types_lexpands[OF \<open>lexpands b3 b2\<close>] have "\<forall>\<phi> \<in> set b3. v' \<turnstile> \<phi>"
    using expandss_not_Nil[OF \<open>expandss b2 b1\<close> \<open>b1 \<noteq> []\<close>] by blast
  with v' "2.prems" show ?case
    by force
next
  case (3 bs b2 b3 b1)
  then obtain v' where v': "\<forall>x \<in> vars b1. v' x = v x" "\<forall>\<phi> \<in> set b2. v' \<turnstile> \<phi>"
    by blast
  from \<open>bexpands bs b2\<close> show ?case
  proof(cases rule: bexpands.cases)
    case 1
    from types_bexpands_nowit[OF this] v' \<open>b3 \<in> bs\<close> have "\<forall>\<phi> \<in> set b3. v' \<turnstile> \<phi>"
      by blast
    with v' "3.prems" show ?thesis
      by force
  next
    case (2 t1 t2 x)
    from types_bexpands_wit[OF this] v' \<open>b3 \<in> bs\<close> obtain l
      where "\<forall>\<phi> \<in> set b3. v'(x := l) \<turnstile> \<phi>"
      using expandss_not_Nil[OF \<open>expandss b2 b1\<close> \<open>b1 \<noteq> []\<close>] by metis
    moreover from bexpands_witD(9)[OF 2] have "x \<notin> vars b1"
      using expandss_mono[OF \<open>expandss b2 b1\<close>] unfolding vars_branch_def by blast
    then have "\<forall>y \<in> vars b1. (v'(x := l)) y = v y"
      using v'(1) by simp
    moreover from \<open>x \<notin> vars b2\<close> v'(2) have "\<forall>\<phi> \<in> set b2. v'(x := l) \<turnstile> \<phi>"
      by (meson types_pset_fm_fun_upd vars_fm_vars_branchI)
    ultimately show ?thesis
      using v' "3.prems"(1)[where ?v'="v'(x := l)"] by fastforce
  qed
qed

lemma urelem_invar_if_wf_branch:
  assumes "wf_branch b"
  assumes "urelem (last b) x" "x \<in> subterms (last b)"
  shows "\<exists>v. \<forall>\<phi> \<in> set b. urelem' v \<phi> x"
proof -
  from assms obtain v where v: "v \<turnstile> last b" "v \<turnstile> x : 0"
    unfolding urelem_def by blast
  moreover from assms have "expandss b [last b]"
    by (metis expandss_last_eq last.simps list.distinct(1) wf_branch_def)
  from types_expandss[OF this, simplified] v obtain v' where
    "\<forall>x \<in> vars (last b). v' x = v x" "\<forall>\<phi> \<in> set b. v' \<turnstile> \<phi>"
    by (metis list.set_intros(1) vars_fm_vars_branchI)
  ultimately show ?thesis
    unfolding urelem_def using assms
    by (metis mem_vars_fm_if_mem_subterms_fm types_term_if_on_vars_eq)
qed

lemma not_types_term_0_if_types_term:
  fixes s :: "'a pset_term"
  assumes "f t1 t2 \<in> subterms s" "f \<in> {(\<sqinter>\<^sub>s), (\<squnion>\<^sub>s), (-\<^sub>s)}"
  assumes "v \<turnstile> f t1 t2 : l"
  shows "\<not> v \<turnstile> t1 : 0" "\<not> v \<turnstile> t2 : 0"
  using assms
  by (induction s arbitrary: l)
     (auto elim: types_pset_term_cases dest: types_term_unique)

lemma types_term_subterms:
  assumes "t \<in> subterms s"
  assumes "v \<turnstile> s : ls"
  obtains lt where "v \<turnstile> t : lt"
  using assms
  by (induction s arbitrary: ls) (auto elim: types_pset_term_cases dest: types_term_unique)

lemma types_atom_subterms:
  fixes a :: "'a pset_atom"
  assumes "t \<in> subterms a"
  assumes "v \<turnstile> a"
  obtains lt where "v \<turnstile> t : lt"
  using assms
  by (cases a) (fastforce elim: types_term_subterms simp: types_pset_atom.simps)+

lemma subterms_type_pset_fm_not_None:
  fixes \<phi> :: "'a pset_fm"
  assumes "t \<in> subterms \<phi>"
  assumes "v \<turnstile> \<phi>"
  obtains lt where "v \<turnstile> t : lt"
  using assms 
  by (induction \<phi>) (auto elim: types_atom_subterms dest: types_fmD(1-5) dest!: types_fmD(6))

lemma not_urelem_comps_if_compound:
  assumes "f t1 t2 \<in> subterms \<phi>" "f \<in> {(\<sqinter>\<^sub>s), (\<squnion>\<^sub>s), (-\<^sub>s)}"
  shows "\<not> urelem \<phi> t1" "\<not> urelem \<phi> t2"
proof -
  from assms have "\<not> v \<turnstile> t1 : 0" "\<not> v \<turnstile> t2 : 0" if "v \<turnstile> \<phi>" for v
    using that not_types_term_0_if_types_term[OF _ _ subterms_type_pset_fm_not_None]
    using subterms_refl by metis+
  then show "\<not> urelem \<phi> t1" "\<not> urelem \<phi> t2"
    unfolding urelem_def by blast+
qed

end

end