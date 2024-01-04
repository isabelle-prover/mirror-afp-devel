section \<open>Proof System\<close>

theory Proof_System
  imports
    Syntax
begin

subsection \<open>Axioms\<close>

inductive_set
  axioms :: "form set"
where
  axiom_1:
    "\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<in> axioms"
| axiom_2:
    "(\<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<alpha>\<^esub> \<yy>\<^bsub>\<alpha>\<^esub>) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<equiv>\<^sup>\<Q> \<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>) \<in> axioms"
| axiom_3:
    "(\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<in> axioms"
| axiom_4_1_con:
    "(\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> \<in> axioms" if "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
| axiom_4_1_var:
    "(\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub> \<in> axioms" if "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "y\<^bsub>\<beta>\<^esub> \<noteq> x\<^bsub>\<alpha>\<^esub>"
| axiom_4_2:
    "(\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A \<in> axioms" if "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
| axiom_4_3:
    "(\<lambda>x\<^bsub>\<alpha>\<^esub>. B \<sqdot> C) \<sqdot> A =\<^bsub>\<beta>\<^esub> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) \<sqdot> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A) \<in> axioms"
      if "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>" and "C \<in> wffs\<^bsub>\<gamma>\<^esub>"
| axiom_4_4:
    "(\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. B) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> (\<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) \<in> axioms"
      if "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<delta>\<^esub>" and "(y, \<gamma>) \<notin> {(x, \<alpha>)} \<union> vars A"
| axiom_4_5:
    "(\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<alpha>\<rightarrow>\<delta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<in> axioms" if "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<delta>\<^esub>"
| axiom_5:
    "\<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>) =\<^bsub>i\<^esub> \<yy>\<^bsub>i\<^esub> \<in> axioms"

lemma axioms_are_wffs_of_type_o:
  shows "axioms \<subseteq> wffs\<^bsub>o\<^esub>"
  by (intro subsetI, cases rule: axioms.cases) auto

subsection \<open>Inference rule R\<close>

definition is_rule_R_app :: "position \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_rule_R_app p D C E \<longleftrightarrow>
    (
      \<exists>\<alpha> A B.
        E = A =\<^bsub>\<alpha>\<^esub> B \<and> A \<in> wffs\<^bsub>\<alpha>\<^esub> \<and> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<and> \<comment> \<open>\<^term>\<open>E\<close> is a well-formed equality\<close>
        A \<preceq>\<^bsub>p\<^esub> C \<and>
        D \<in> wffs\<^bsub>o\<^esub> \<and>
        C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D
    )"

lemma rule_R_original_form_is_wffo:
  assumes "is_rule_R_app p D C E"
  shows "C \<in> wffs\<^bsub>o\<^esub>"
  using assms and replacement_preserves_typing by fastforce

subsection \<open>Proof and derivability\<close>

inductive is_derivable :: "form \<Rightarrow> bool" where
  dv_axiom: "is_derivable A" if "A \<in> axioms"
| dv_rule_R: "is_derivable D" if "is_derivable C" and "is_derivable E" and "is_rule_R_app p D C E"

lemma derivable_form_is_wffso:
  assumes "is_derivable A"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms and axioms_are_wffs_of_type_o by (fastforce elim: is_derivable.cases)

definition is_proof_step :: "form list \<Rightarrow> nat \<Rightarrow> bool" where
  [iff]: "is_proof_step \<S> i' \<longleftrightarrow>
    \<S> ! i' \<in> axioms \<or>
    (\<exists>p j k. {j, k} \<subseteq> {0..<i'} \<and> is_rule_R_app p (\<S> ! i') (\<S> ! j) (\<S> ! k))"

definition is_proof :: "form list \<Rightarrow> bool" where
  [iff]: "is_proof \<S> \<longleftrightarrow> (\<forall>i' < length \<S>. is_proof_step \<S> i')"

lemma common_prefix_is_subproof:
  assumes "is_proof (\<S> @ \<S>\<^sub>1)"
  and "i' < length \<S>"
  shows "is_proof_step (\<S> @ \<S>\<^sub>2) i'"
proof -
  from assms(2) have *: "(\<S> @ \<S>\<^sub>1) ! i' = (\<S> @ \<S>\<^sub>2) ! i'"
    by (simp add: nth_append)
  moreover from assms(2) have "i' < length (\<S> @ \<S>\<^sub>1)"
    by simp
  ultimately obtain p and j and k where **:
    "(\<S> @ \<S>\<^sub>1) ! i' \<in> axioms \<or>
    {j, k} \<subseteq> {0..<i'} \<and> is_rule_R_app p ((\<S> @ \<S>\<^sub>1) ! i') ((\<S> @ \<S>\<^sub>1) ! j) ((\<S> @ \<S>\<^sub>1) ! k)"
    using assms(1) by fastforce
  then consider
    (axiom) "(\<S> @ \<S>\<^sub>1) ! i' \<in> axioms"
  | (rule_R) "{j, k} \<subseteq> {0..<i'} \<and> is_rule_R_app p ((\<S> @ \<S>\<^sub>1) ! i') ((\<S> @ \<S>\<^sub>1) ! j) ((\<S> @ \<S>\<^sub>1) ! k)"
    by blast
  then have "
    (\<S> @ \<S>\<^sub>2) ! i' \<in> axioms \<or>
    ({j, k} \<subseteq> {0..<i'} \<and> is_rule_R_app p ((\<S> @ \<S>\<^sub>2) ! i') ((\<S> @ \<S>\<^sub>2) ! j) ((\<S> @ \<S>\<^sub>2) ! k))"
  proof cases
    case axiom
    with * have "(\<S> @ \<S>\<^sub>2) ! i' \<in> axioms"
      by (simp only:)
    then show ?thesis ..
  next
    case rule_R
    with assms(2) have "(\<S> @ \<S>\<^sub>1) ! j = (\<S> @ \<S>\<^sub>2) ! j" and "(\<S> @ \<S>\<^sub>1) ! k = (\<S> @ \<S>\<^sub>2) ! k"
      by (simp_all add: nth_append)
    then have "{j, k} \<subseteq> {0..<i'} \<and> is_rule_R_app p ((\<S> @ \<S>\<^sub>2) ! i') ((\<S> @ \<S>\<^sub>2) ! j) ((\<S> @ \<S>\<^sub>2) ! k)"
      using * and rule_R by simp
    then show ?thesis ..
  qed
  with ** show ?thesis
    by fastforce
qed

lemma added_suffix_proof_preservation:
  assumes "is_proof \<S>"
  and "i' < length (\<S> @ \<S>') - length \<S>'"
  shows "is_proof_step (\<S> @ \<S>') i'"
  using assms and common_prefix_is_subproof[where \<S>\<^sub>1 = "[]"] by simp

lemma append_proof_step_is_proof:
  assumes "is_proof \<S>"
  and "is_proof_step (\<S> @ [A]) (length (\<S> @ [A]) - 1)"
  shows "is_proof (\<S> @ [A])"
  using assms and added_suffix_proof_preservation by (simp add: All_less_Suc)

lemma added_prefix_proof_preservation:
  assumes "is_proof \<S>'"
  and "i' \<in> {length \<S>..<length (\<S> @ \<S>')}"
  shows "is_proof_step (\<S> @ \<S>') i'"
proof -
  let ?\<S> = "\<S> @ \<S>'"
  let ?i = "i' - length \<S>"
  from assms(2) have "?\<S> ! i' = \<S>' ! ?i" and "?i < length \<S>'"
    by (simp_all add: nth_append less_diff_conv2)
  then have "is_proof_step ?\<S> i' = is_proof_step \<S>' ?i"
  proof -
    from assms(1) and \<open>?i < length \<S>'\<close> obtain j and k and p where *:
      "\<S>' ! ?i \<in> axioms \<or> ({j, k} \<subseteq> {0..<?i} \<and> is_rule_R_app p (\<S>' ! ?i) (\<S>' ! j) (\<S>' ! k))"
      by fastforce
    then consider
      (axiom) "\<S>' ! ?i \<in> axioms"
    | (rule_R) "{j, k} \<subseteq> {0..<?i} \<and> is_rule_R_app p (\<S>' ! ?i) (\<S>' ! j) (\<S>' ! k)"
      by blast
    then have "
      ?\<S> ! i' \<in> axioms \<or>
      (
        {j + length \<S>, k + length \<S>} \<subseteq> {0..<i'} \<and>
        is_rule_R_app p (?\<S> ! i') (?\<S> ! (j + length \<S>)) (?\<S> ! (k + length \<S>))
      )"
    proof cases
      case axiom
      with \<open>?\<S> ! i' = \<S>' ! ?i\<close> have "?\<S> ! i' \<in> axioms"
        by (simp only:)
      then show ?thesis ..
    next
      case rule_R
      with assms(2) have "?\<S> ! (j + length \<S>) = \<S>' ! j" and "?\<S> ! (k + length \<S>) = \<S>' ! k"
        by (simp_all add: nth_append)
      with \<open>?\<S> ! i' = \<S>' ! ?i\<close> and rule_R have "
        {j + length \<S>, k + length \<S>} \<subseteq> {0..<i'} \<and>
        is_rule_R_app p (?\<S> ! i') (?\<S> ! (j + length \<S>)) (?\<S> ! (k + length \<S>))"
        by auto
      then show ?thesis ..
    qed
    with * show ?thesis
      by fastforce
  qed
  with assms(1) and \<open>?i < length \<S>'\<close> show ?thesis
    by simp
qed

lemma proof_but_last_is_proof:
  assumes "is_proof (\<S> @ [A])"
  shows "is_proof \<S>"
  using assms and common_prefix_is_subproof[where \<S>\<^sub>1 = "[A]" and \<S>\<^sub>2 = "[]"] by simp

lemma proof_prefix_is_proof:
  assumes "is_proof (\<S>\<^sub>1 @ \<S>\<^sub>2)"
  shows "is_proof \<S>\<^sub>1"
  using assms and proof_but_last_is_proof
  by (induction \<S>\<^sub>2 arbitrary: \<S>\<^sub>1 rule: rev_induct) (simp, metis append.assoc)

lemma single_axiom_is_proof:
  assumes "A \<in> axioms"
  shows "is_proof [A]"
  using assms by fastforce

lemma proofs_concatenation_is_proof:
  assumes "is_proof \<S>\<^sub>1" and "is_proof \<S>\<^sub>2"
  shows "is_proof (\<S>\<^sub>1 @ \<S>\<^sub>2)"
proof -
  from assms(1) have "\<forall>i' < length \<S>\<^sub>1. is_proof_step (\<S>\<^sub>1 @ \<S>\<^sub>2) i'"
    using added_suffix_proof_preservation by auto
  moreover from assms(2) have "\<forall>i' \<in> {length \<S>\<^sub>1..<length (\<S>\<^sub>1 @ \<S>\<^sub>2)}. is_proof_step (\<S>\<^sub>1 @ \<S>\<^sub>2) i'"
    using added_prefix_proof_preservation by auto
  ultimately show ?thesis
    unfolding is_proof_def by (meson atLeastLessThan_iff linorder_not_le)
qed

lemma elem_of_proof_is_wffo:
  assumes "is_proof \<S>" and "A \<in> lset \<S>"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms and axioms_are_wffs_of_type_o
  unfolding is_rule_R_app_def and is_proof_step_def and is_proof_def
  by (induction \<S>) (simp, metis (full_types) in_mono in_set_conv_nth)

lemma axiom_prepended_to_proof_is_proof:
  assumes "is_proof \<S>"
  and "A \<in> axioms"
  shows "is_proof ([A] @ \<S>)"
  using proofs_concatenation_is_proof[OF single_axiom_is_proof[OF assms(2)] assms(1)] .

lemma axiom_appended_to_proof_is_proof:
  assumes "is_proof \<S>"
  and "A \<in> axioms"
  shows "is_proof (\<S> @ [A])"
  using proofs_concatenation_is_proof[OF assms(1) single_axiom_is_proof[OF assms(2)]] .

lemma rule_R_app_appended_to_proof_is_proof:
  assumes "is_proof \<S>"
  and "i\<^sub>C < length \<S>" and "\<S> ! i\<^sub>C = C"
  and "i\<^sub>E < length \<S>" and "\<S> ! i\<^sub>E = E"
  and "is_rule_R_app p D C E"
  shows "is_proof (\<S> @ [D])"
proof -
  let ?\<S> = "\<S> @ [D]"
  let ?i\<^sub>D = "length \<S>"
  from assms(2,4) have "i\<^sub>C < ?i\<^sub>D" and "i\<^sub>E < ?i\<^sub>D"
    by fastforce+
  with assms(3,5,6) have "is_rule_R_app p (?\<S> ! ?i\<^sub>D) (?\<S> ! i\<^sub>C) (?\<S> ! i\<^sub>E)"
    by (simp add: nth_append)
  with assms(2,4) have "\<exists>p j k. {j, k} \<subseteq> {0..<?i\<^sub>D} \<and> is_rule_R_app p (?\<S> ! ?i\<^sub>D) (?\<S> ! j) (?\<S> ! k)"
    by fastforce
  then have "is_proof_step ?\<S> (length ?\<S> - 1)"
    by simp
  moreover from assms(1) have "\<forall>i' < length ?\<S> - 1. is_proof_step ?\<S> i'"
    using added_suffix_proof_preservation by auto
  ultimately show ?thesis
    using less_Suc_eq by auto
qed

definition is_proof_of :: "form list \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_proof_of \<S> A \<longleftrightarrow> \<S> \<noteq> [] \<and> is_proof \<S> \<and> last \<S> = A"

lemma proof_prefix_is_proof_of_last:
  assumes "is_proof (\<S> @ \<S>')" and "\<S> \<noteq> []"
  shows "is_proof_of \<S> (last \<S>)"
proof -
  from assms(1) have "is_proof \<S>"
    by (fact proof_prefix_is_proof)
  with assms(2) show ?thesis
    by fastforce
qed

definition is_theorem :: "form \<Rightarrow> bool" where
  [iff]: "is_theorem A \<longleftrightarrow> (\<exists>\<S>. is_proof_of \<S> A)"

lemma proof_form_is_wffo:
  assumes "is_proof_of \<S> A"
  and "B \<in> lset \<S>"
  shows "B \<in> wffs\<^bsub>o\<^esub>"
  using assms and elem_of_proof_is_wffo by blast

lemma proof_form_is_theorem:
  assumes "is_proof \<S>" and "\<S> \<noteq> []"
  and "i' < length \<S>"
  shows "is_theorem (\<S> ! i')"
proof -
  let ?\<S>\<^sub>1 = "take (Suc i') \<S>"
  from assms(1) obtain \<S>\<^sub>2 where "is_proof (?\<S>\<^sub>1 @ \<S>\<^sub>2)"
    by (metis append_take_drop_id)
  then have "is_proof ?\<S>\<^sub>1"
    by (fact proof_prefix_is_proof)
  moreover from assms(3) have "last ?\<S>\<^sub>1 = \<S> ! i'"
    by (simp add: take_Suc_conv_app_nth)
  ultimately show ?thesis
    using assms(2) unfolding is_proof_of_def and is_theorem_def by (metis Zero_neq_Suc take_eq_Nil2)
qed

theorem derivable_form_is_theorem:
  assumes "is_derivable A"
  shows "is_theorem A"
using assms proof (induction rule: is_derivable.induct)
  case (dv_axiom A)
  then have "is_proof [A]"
    by (fact single_axiom_is_proof)
  moreover have "last [A] = A"
    by simp
  ultimately show ?case
    by blast
next
  case (dv_rule_R C E p D)
  obtain \<S>\<^sub>C and \<S>\<^sub>E where
    "is_proof \<S>\<^sub>C" and "\<S>\<^sub>C \<noteq> []" and "last \<S>\<^sub>C = C" and
    "is_proof \<S>\<^sub>E" and "\<S>\<^sub>E \<noteq> []" and "last \<S>\<^sub>E = E"
    using dv_rule_R.IH by fastforce
  let ?i\<^sub>C = "length \<S>\<^sub>C - 1" and ?i\<^sub>E = "length \<S>\<^sub>C + length \<S>\<^sub>E - 1" and ?i\<^sub>D = "length \<S>\<^sub>C + length \<S>\<^sub>E"
  let ?\<S> = "\<S>\<^sub>C @ \<S>\<^sub>E @ [D]"
  from \<open>\<S>\<^sub>C \<noteq> []\<close> have "?i\<^sub>C < length (\<S>\<^sub>C @ \<S>\<^sub>E)" and "?i\<^sub>E < length (\<S>\<^sub>C @ \<S>\<^sub>E)"
    using linorder_not_le by fastforce+
  moreover have "(\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>C = C" and "(\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>E = E"
    using \<open>\<S>\<^sub>C \<noteq> []\<close> and \<open>last \<S>\<^sub>C = C\<close>
    by
      (
        simp add: last_conv_nth nth_append,
        metis \<open>last \<S>\<^sub>E = E\<close> \<open>\<S>\<^sub>E \<noteq> []\<close> append_is_Nil_conv last_appendR last_conv_nth length_append
      )
  with \<open>is_rule_R_app p D C E\<close> have "is_rule_R_app p D ((\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>C) ((\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>E)"
    using \<open>(\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>C = C\<close> by fastforce
  moreover from \<open>is_proof \<S>\<^sub>C\<close> and \<open>is_proof \<S>\<^sub>E\<close> have "is_proof (\<S>\<^sub>C @ \<S>\<^sub>E)"
    by (fact proofs_concatenation_is_proof)
  ultimately have "is_proof ((\<S>\<^sub>C @ \<S>\<^sub>E) @ [D])"
    using rule_R_app_appended_to_proof_is_proof by presburger
  with \<open>\<S>\<^sub>C \<noteq> []\<close> show ?case
    unfolding is_proof_of_def and is_theorem_def by (metis snoc_eq_iff_butlast)
qed

theorem theorem_is_derivable_form:
  assumes "is_theorem A"
  shows "is_derivable A"
proof -
  from assms obtain \<S> where "is_proof \<S>" and "\<S> \<noteq> []" and "last \<S> = A"
    by fastforce
  then show ?thesis
  proof (induction "length \<S>" arbitrary: \<S> A rule: less_induct)
    case less
    let ?i' = "length \<S> - 1"
    from \<open>\<S> \<noteq> []\<close> and \<open>last \<S> = A\<close> have "\<S> ! ?i' = A"
      by (simp add: last_conv_nth)
    from \<open>is_proof \<S>\<close> and \<open>\<S> \<noteq> []\<close> and \<open>last \<S> = A\<close> have "is_proof_step \<S> ?i'"
      using added_suffix_proof_preservation[where \<S>' = "[]"] by simp
    then consider
      (axiom) "\<S> ! ?i' \<in> axioms"
    | (rule_R) "\<exists>p j k. {j, k} \<subseteq> {0..<?i'} \<and> is_rule_R_app p (\<S> ! ?i') (\<S> ! j) (\<S> ! k)"
      by fastforce
    then show ?case
    proof cases
      case axiom
      with \<open>\<S> ! ?i' = A\<close> show ?thesis
        by (fastforce intro: dv_axiom)
    next
      case rule_R
      then obtain p and j and k
        where "{j, k} \<subseteq> {0..<?i'}" and "is_rule_R_app p (\<S> ! ?i') (\<S> ! j) (\<S> ! k)"
        by force
      let ?\<S>\<^sub>j = "take (Suc j) \<S>"
      let ?\<S>\<^sub>k = "take (Suc k) \<S>"
      obtain \<S>\<^sub>j' and \<S>\<^sub>k' where "\<S> = ?\<S>\<^sub>j @ \<S>\<^sub>j'" and "\<S> = ?\<S>\<^sub>k @ \<S>\<^sub>k'"
        by (metis append_take_drop_id)
      with \<open>is_proof \<S>\<close> have "is_proof (?\<S>\<^sub>j @ \<S>\<^sub>j')" and "is_proof (?\<S>\<^sub>k @ \<S>\<^sub>k')"
        by (simp_all only:)
      moreover
      from \<open>\<S> = ?\<S>\<^sub>j @ \<S>\<^sub>j'\<close> and \<open>\<S> = ?\<S>\<^sub>k @ \<S>\<^sub>k'\<close> and \<open>last \<S> = A\<close> and \<open>{j, k} \<subseteq> {0..<length \<S> - 1}\<close>
      have "last \<S>\<^sub>j' = A" and "last \<S>\<^sub>k' = A"
        using length_Cons and less_le_not_le and take_Suc and take_tl and append.right_neutral
        by (metis atLeastLessThan_iff diff_Suc_1 insert_subset last_appendR take_all_iff)+
      moreover from \<open>\<S> \<noteq> []\<close> have "?\<S>\<^sub>j \<noteq> []" and "?\<S>\<^sub>k \<noteq> []"
        by simp_all
      ultimately have "is_proof_of ?\<S>\<^sub>j (last ?\<S>\<^sub>j)" and "is_proof_of ?\<S>\<^sub>k (last ?\<S>\<^sub>k)"
        using proof_prefix_is_proof_of_last [where \<S> = ?\<S>\<^sub>j and \<S>' = \<S>\<^sub>j']
        and proof_prefix_is_proof_of_last [where \<S> = ?\<S>\<^sub>k and \<S>' = \<S>\<^sub>k']
        by fastforce+
      moreover from \<open>last \<S>\<^sub>j' = A\<close> and \<open>last \<S>\<^sub>k' = A\<close>
      have "length ?\<S>\<^sub>j < length \<S>" and "length ?\<S>\<^sub>k < length \<S>"
        using \<open>{j, k} \<subseteq> {0..<length \<S> - 1}\<close> by force+
      moreover from calculation(3,4) have "last ?\<S>\<^sub>j = \<S> ! j" and "last ?\<S>\<^sub>k = \<S> ! k"
        by (metis Suc_lessD last_snoc linorder_not_le nat_neq_iff take_Suc_conv_app_nth take_all_iff)+
      ultimately have "is_derivable (\<S> ! j)" and "is_derivable (\<S> ! k)"
        using \<open>?\<S>\<^sub>j \<noteq> []\<close> and \<open>?\<S>\<^sub>k \<noteq> []\<close> and less(1) by blast+
      with \<open>is_rule_R_app p (\<S> ! ?i') (\<S> ! j) (\<S> ! k)\<close> and \<open>\<S> ! ?i' = A\<close> show ?thesis
        by (blast intro: dv_rule_R)
    qed
  qed
qed

theorem theoremhood_derivability_equivalence:
  shows "is_theorem A \<longleftrightarrow> is_derivable A"
  using derivable_form_is_theorem and theorem_is_derivable_form by blast

lemma theorem_is_wffo:
  assumes "is_theorem A"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
proof -
  from assms obtain \<S> where "is_proof_of \<S> A"
    by blast
  then have "A \<in> lset \<S>"
    by auto
  with \<open>is_proof_of \<S> A\<close> show ?thesis
    using proof_form_is_wffo by blast
qed

lemma equality_reflexivity:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "is_theorem (A =\<^bsub>\<alpha>\<^esub> A)" (is "is_theorem ?A\<^sub>2")
proof -
  let ?A\<^sub>1 = "(\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A"
  let ?\<S> = "[?A\<^sub>1, ?A\<^sub>2]"
  \<comment> \<open> (.1) Axiom 4.2 \<close>
  have "is_proof_step ?\<S> 0"
  proof -
    from assms have "?A\<^sub>1 \<in> axioms"
      by (intro axiom_4_2)
    then show ?thesis
      by simp
  qed
  \<comment> \<open> (.2) Rule R: .1,.1 \<close>
  moreover have "is_proof_step ?\<S> 1"
  proof -
    let ?p = "[\<guillemotleft>, \<guillemotright>]"
    have "\<exists>p j k. {j::nat, k} \<subseteq> {0..<1} \<and> is_rule_R_app ?p ?A\<^sub>2 (?\<S> ! j) (?\<S> ! k)"
    proof -
      let ?D = "?A\<^sub>2" and ?j = "0::nat" and ?k = "0"
      have "{?j, ?k} \<subseteq> {0..<1}"
        by simp
      moreover have "is_rule_R_app ?p ?A\<^sub>2 (?\<S> ! ?j) (?\<S> ! ?k)"
      proof -
        have "(\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> A \<preceq>\<^bsub>?p\<^esub> (?\<S> ! ?j)"
          by force
        moreover have "(?\<S> ! ?j)\<lblot>?p \<leftarrow> A\<rblot> \<rhd> ?D"
          by force
        moreover from \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> have "?D \<in> wffs\<^bsub>o\<^esub>"
          by (intro equality_wff)
        moreover from \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> have "(\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> A \<in> wffs\<^bsub>\<alpha>\<^esub>"
          by (meson wffs_of_type_simps)
        ultimately show ?thesis
          using \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> by simp
      qed
      ultimately show ?thesis
        by meson
    qed
    then show ?thesis
      by auto
  qed
  moreover have "last ?\<S> = ?A\<^sub>2"
    by simp
  moreover have "{0..<length ?\<S>} = {0, 1}"
    by (simp add: atLeast0_lessThan_Suc insert_commute)
  ultimately show ?thesis
    unfolding is_theorem_def and is_proof_def and is_proof_of_def
    by (metis One_nat_def Suc_1 length_Cons less_2_cases list.distinct(1) list.size(3))
qed

lemma equality_reflexivity':
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "is_theorem (A =\<^bsub>\<alpha>\<^esub> A)" (is "is_theorem ?A\<^sub>2")
proof (intro derivable_form_is_theorem)
  let ?A\<^sub>1 = "(\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A"
  \<comment> \<open> (.1) Axiom 4.2 \<close>
  from assms have "?A\<^sub>1 \<in> axioms"
    by (intro axiom_4_2)
  then have step_1: "is_derivable ?A\<^sub>1"
    by (intro dv_axiom)
  \<comment> \<open> (.2) Rule R: .1,.1 \<close>
  then show "is_derivable ?A\<^sub>2"
  proof -
    let ?p = "[\<guillemotleft>, \<guillemotright>]" and ?C = "?A\<^sub>1" and ?E = "?A\<^sub>1" and ?D = "?A\<^sub>2"
    have "is_rule_R_app ?p ?D ?C ?E"
    proof -
      have "(\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> A \<preceq>\<^bsub>?p\<^esub> ?C"
        by force
      moreover have "?C\<lblot>?p \<leftarrow> A\<rblot> \<rhd> ?D"
        by force
      moreover from \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> have "?D \<in> wffs\<^bsub>o\<^esub>"
        by (intro equality_wff)
      moreover from \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> have "(\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. \<xx>\<^bsub>\<alpha>\<^esub>) \<sqdot> A \<in> wffs\<^bsub>\<alpha>\<^esub>"
        by (meson wffs_of_type_simps)
      ultimately show ?thesis
        using \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> by simp
    qed
    with step_1 show ?thesis
      by (blast intro: dv_rule_R)
  qed
qed

subsection \<open>Hypothetical proof and derivability\<close>

text \<open>The set of free variables in \<open>\<X>\<close> that are exposed to capture at position \<open>p\<close> in \<open>A\<close>:\<close>

definition capture_exposed_vars_at :: "position \<Rightarrow> form \<Rightarrow> 'a \<Rightarrow> var set" where
  [simp]: "capture_exposed_vars_at p A \<X> =
    {(x, \<beta>) | x \<beta> p' E. strict_prefix p' p \<and> \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> A \<and> (x, \<beta>) \<in> free_vars \<X>}"

lemma capture_exposed_vars_at_alt_def:
  assumes "p \<in> positions A"
  shows "capture_exposed_vars_at p A \<X> = binders_at A p \<inter> free_vars \<X>"
  unfolding binders_at_alt_def[OF assms] and in_scope_of_abs_alt_def
  using is_subform_implies_in_positions by auto

text \<open>Inference rule R$'$:\<close>

definition rule_R'_side_condition :: "form set \<Rightarrow> position \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "rule_R'_side_condition \<H> p D C E \<longleftrightarrow>
    capture_exposed_vars_at p C E \<inter> capture_exposed_vars_at p C \<H> = {}"

lemma rule_R'_side_condition_alt_def:
  fixes \<H> :: "form set"
  assumes "C \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "
    rule_R'_side_condition \<H> p D C (A =\<^bsub>\<alpha>\<^esub> B)
    \<longleftrightarrow>
    (
      \<nexists>x \<beta> E p'.
        strict_prefix p' p \<and>
        \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and>
        (x, \<beta>) \<in> free_vars (A =\<^bsub>\<alpha>\<^esub> B) \<and>
        (\<exists>H \<in> \<H>. (x, \<beta>) \<in> free_vars H)
    )"
proof -
  have "
    capture_exposed_vars_at p C (A =\<^bsub>\<alpha>\<^esub> B)
    =
    {(x, \<beta>) | x \<beta> p' E. strict_prefix p' p \<and> \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and> (x, \<beta>) \<in> free_vars (A =\<^bsub>\<alpha>\<^esub> B)}"
    using assms and capture_exposed_vars_at_alt_def unfolding capture_exposed_vars_at_def by fast
  moreover have "
    capture_exposed_vars_at p C \<H>
    =
    {(x, \<beta>) | x \<beta> p' E. strict_prefix p' p \<and> \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and> (x, \<beta>) \<in> free_vars \<H>}"
    using assms and capture_exposed_vars_at_alt_def unfolding capture_exposed_vars_at_def by fast
  ultimately have "
    capture_exposed_vars_at p C (A =\<^bsub>\<alpha>\<^esub> B) \<inter> capture_exposed_vars_at p C \<H>
    =
    {(x, \<beta>) | x \<beta> p' E. strict_prefix p' p \<and> \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and> (x, \<beta>) \<in> free_vars (A =\<^bsub>\<alpha>\<^esub> B) \<and>
      (x, \<beta>) \<in> free_vars \<H>}"
    by auto
  also have "
    \<dots>
    =
    {(x, \<beta>) | x \<beta> p' E. strict_prefix p' p \<and> \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and> (x, \<beta>) \<in> free_vars (A =\<^bsub>\<alpha>\<^esub> B) \<and>
      (\<exists>H \<in> \<H>. (x, \<beta>) \<in> free_vars H)}"
    by auto
  finally show ?thesis
    by fast
qed

definition is_rule_R'_app :: "form set \<Rightarrow> position \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_rule_R'_app \<H> p D C E \<longleftrightarrow> is_rule_R_app p D C E \<and> rule_R'_side_condition \<H> p D C E"

lemma is_rule_R'_app_alt_def:
  shows "
    is_rule_R'_app \<H> p D C E
    \<longleftrightarrow>
    (
      \<exists>\<alpha> A B.
        E = A =\<^bsub>\<alpha>\<^esub> B \<and> A \<in> wffs\<^bsub>\<alpha>\<^esub> \<and> B \<in> wffs\<^bsub>\<alpha>\<^esub> \<and> \<comment> \<open>\<^term>\<open>E\<close> is a well-formed equality\<close>
        A \<preceq>\<^bsub>p\<^esub> C \<and> D \<in> wffs\<^bsub>o\<^esub> \<and>
        C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D \<and>
        (
          \<nexists>x \<beta> E p'.
            strict_prefix p' p \<and>
            \<lambda>x\<^bsub>\<beta>\<^esub>. E \<preceq>\<^bsub>p'\<^esub> C \<and>
            (x, \<beta>) \<in> free_vars (A =\<^bsub>\<alpha>\<^esub> B) \<and>
            (\<exists>H \<in> \<H>. (x, \<beta>) \<in> free_vars H)
        )
    )"
  using rule_R'_side_condition_alt_def by fastforce

lemma rule_R'_preserves_typing:
  assumes "is_rule_R'_app \<H> p D C E"
  shows "C \<in> wffs\<^bsub>o\<^esub> \<longleftrightarrow> D \<in> wffs\<^bsub>o\<^esub>"
  using assms and replacement_preserves_typing unfolding is_rule_R_app_def and is_rule_R'_app_def
  by meson

abbreviation is_hyps :: "form set \<Rightarrow> bool" where
  "is_hyps \<H> \<equiv> \<H> \<subseteq> wffs\<^bsub>o\<^esub> \<and> finite \<H>"

inductive is_derivable_from_hyps :: "form set \<Rightarrow> form \<Rightarrow> bool" ("_ \<turnstile> _" [50, 50] 50) for \<H> where
  dv_hyp: "\<H> \<turnstile> A" if "A \<in> \<H>" and "is_hyps \<H>"
| dv_thm: "\<H> \<turnstile> A" if "is_theorem A" and "is_hyps \<H>"
| dv_rule_R': "\<H> \<turnstile> D" if "\<H> \<turnstile> C" and "\<H> \<turnstile> E" and "is_rule_R'_app \<H> p D C E" and "is_hyps \<H>"

lemma hyp_derivable_form_is_wffso:
  assumes "is_derivable_from_hyps \<H> A"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms and theorem_is_wffo by (cases rule: is_derivable_from_hyps.cases) auto

definition is_hyp_proof_step :: "form set \<Rightarrow> form list \<Rightarrow> form list \<Rightarrow> nat \<Rightarrow> bool" where
  [iff]: "is_hyp_proof_step \<H> \<S>\<^sub>1 \<S>\<^sub>2 i' \<longleftrightarrow>
    \<S>\<^sub>2 ! i' \<in> \<H> \<or>
    \<S>\<^sub>2 ! i' \<in> lset \<S>\<^sub>1 \<or>
    (\<exists>p j k. {j, k} \<subseteq> {0..<i'} \<and> is_rule_R'_app \<H> p (\<S>\<^sub>2 ! i') (\<S>\<^sub>2 ! j) (\<S>\<^sub>2 ! k))"

type_synonym hyp_proof = "form list \<times> form list"

definition is_hyp_proof :: "form set \<Rightarrow> form list \<Rightarrow> form list \<Rightarrow> bool" where
  [iff]: "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2 \<longleftrightarrow> (\<forall>i' < length \<S>\<^sub>2. is_hyp_proof_step \<H> \<S>\<^sub>1 \<S>\<^sub>2 i')"

lemma common_prefix_is_hyp_subproof_from:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ \<S>\<^sub>2')"
  and "i' < length \<S>\<^sub>2"
  shows "is_hyp_proof_step \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ \<S>\<^sub>2'') i'"
proof -
  let ?\<S> = "\<S>\<^sub>2 @ \<S>\<^sub>2'"
  from assms(2) have "?\<S> ! i' = (\<S>\<^sub>2 @ \<S>\<^sub>2'') ! i'"
    by (simp add: nth_append)
  moreover from assms(2) have "i' < length ?\<S>"
    by simp
  ultimately obtain p and j and k where "
    ?\<S> ! i' \<in> \<H> \<or>
    ?\<S> ! i' \<in> lset \<S>\<^sub>1 \<or>
    {j, k} \<subseteq> {0..<i'} \<and> is_rule_R'_app \<H> p (?\<S> ! i') (?\<S> ! j) (?\<S> ! k)"
    using assms(1) unfolding is_hyp_proof_def and is_hyp_proof_step_def by meson
  then consider
    (hyp) "?\<S> ! i' \<in> \<H>"
  | (seq) "?\<S> ! i' \<in> lset \<S>\<^sub>1"
  | (rule_R') "{j, k} \<subseteq> {0..<i'} \<and> is_rule_R'_app \<H> p (?\<S> ! i') (?\<S> ! j) (?\<S> ! k)"
    by blast
  then have "
    (\<S>\<^sub>2 @ \<S>\<^sub>2'') ! i' \<in> \<H> \<or>
    (\<S>\<^sub>2 @ \<S>\<^sub>2'') ! i' \<in> lset \<S>\<^sub>1 \<or>
    ({j, k} \<subseteq> {0..<i'} \<and> is_rule_R'_app \<H> p ((\<S>\<^sub>2 @ \<S>\<^sub>2'') ! i') ((\<S>\<^sub>2 @ \<S>\<^sub>2'') ! j) ((\<S>\<^sub>2 @ \<S>\<^sub>2'') ! k))"
  proof cases
    case hyp
    with assms(2) have "(\<S>\<^sub>2 @ \<S>\<^sub>2'') ! i' \<in> \<H>"
      by (simp add: nth_append)
    then show ?thesis ..
  next
    case seq
    with assms(2) have "(\<S>\<^sub>2 @ \<S>\<^sub>2'') ! i' \<in> lset \<S>\<^sub>1"
      by (simp add: nth_append)
    then show ?thesis
      by (intro disjI1 disjI2)
  next
    case rule_R'
    with assms(2) have "?\<S> ! j = (\<S>\<^sub>2 @ \<S>\<^sub>2'') ! j" and "?\<S> ! k = (\<S>\<^sub>2 @ \<S>\<^sub>2'') ! k"
      by (simp_all add: nth_append)
    with assms(2) and rule_R' have "
      {j, k} \<subseteq> {0..<i'} \<and> is_rule_R'_app \<H> p ((\<S>\<^sub>2 @ \<S>\<^sub>2'') ! i') ((\<S>\<^sub>2 @ \<S>\<^sub>2'') ! j) ((\<S>\<^sub>2 @ \<S>\<^sub>2'') ! k)"
      by (metis nth_append)
    then show ?thesis
      by (intro disjI2)
  qed
  then show ?thesis
    unfolding is_hyp_proof_step_def by meson
qed

lemma added_suffix_thms_hyp_proof_preservation:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  shows "is_hyp_proof \<H> (\<S>\<^sub>1 @ \<S>\<^sub>1') \<S>\<^sub>2"
  using assms by auto

lemma added_suffix_hyp_proof_preservation:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  and "i' < length (\<S>\<^sub>2 @ \<S>\<^sub>2') - length \<S>\<^sub>2'"
  shows "is_hyp_proof_step \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ \<S>\<^sub>2') i'"
  using assms and common_prefix_is_hyp_subproof_from[where \<S>\<^sub>2' = "[]"] by auto

lemma appended_hyp_proof_step_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  and "is_hyp_proof_step \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ [A]) (length (\<S>\<^sub>2 @ [A]) - 1)"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ [A])"
proof (standard, intro allI impI)
  fix i'
  assume "i' < length (\<S>\<^sub>2 @ [A])"
  then consider (a) "i' < length \<S>\<^sub>2" | (b) "i' = length \<S>\<^sub>2"
    by fastforce
  then show "is_hyp_proof_step \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ [A]) i'"
  proof cases
    case a
    with assms(1) show ?thesis
      using added_suffix_hyp_proof_preservation by simp
  next
    case b
    with assms(2) show ?thesis
      by simp
  qed
qed

lemma added_prefix_hyp_proof_preservation:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2'"
  and "i' \<in> {length \<S>\<^sub>2..<length (\<S>\<^sub>2 @ \<S>\<^sub>2')}"
  shows "is_hyp_proof_step \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ \<S>\<^sub>2') i'"
proof -
  let ?\<S> = "\<S>\<^sub>2 @ \<S>\<^sub>2'"
  let ?i = "i' - length \<S>\<^sub>2"
  from assms(2) have "?\<S> ! i' = \<S>\<^sub>2' ! ?i" and "?i < length \<S>\<^sub>2'"
    by (simp_all add: nth_append less_diff_conv2)
  then have "is_hyp_proof_step \<H> \<S>\<^sub>1 ?\<S> i' = is_hyp_proof_step \<H> \<S>\<^sub>1 \<S>\<^sub>2' ?i"
  proof -
    from assms(1) and \<open>?i < length \<S>\<^sub>2'\<close> obtain j and k and p where "
      \<S>\<^sub>2' ! ?i \<in> \<H> \<or>
      \<S>\<^sub>2' ! ?i \<in> lset \<S>\<^sub>1 \<or>
      ({j, k} \<subseteq> {0..<?i} \<and> is_rule_R'_app \<H> p (\<S>\<^sub>2' ! ?i) (\<S>\<^sub>2' ! j) (\<S>\<^sub>2' ! k))"
      unfolding is_hyp_proof_def and is_hyp_proof_step_def by meson
    then consider
      (hyp) "\<S>\<^sub>2' ! ?i \<in> \<H>"
    | (seq) "\<S>\<^sub>2' ! ?i \<in> lset \<S>\<^sub>1"
    | (rule_R') "{j, k} \<subseteq> {0..<?i} \<and> is_rule_R'_app \<H> p (\<S>\<^sub>2' ! ?i) (\<S>\<^sub>2' ! j) (\<S>\<^sub>2' ! k)"
      by blast
    then have "
      ?\<S> ! i' \<in> \<H> \<or>
      ?\<S> ! i' \<in> lset \<S>\<^sub>1 \<or>
      ({j + length \<S>\<^sub>2, k + length \<S>\<^sub>2} \<subseteq> {0..<i'} \<and>
        is_rule_R'_app \<H> p (?\<S> ! i') (?\<S> ! (j + length \<S>\<^sub>2)) (?\<S> ! (k + length \<S>\<^sub>2)))"
    proof cases
      case hyp
      with \<open>?\<S> ! i' = \<S>\<^sub>2' ! ?i\<close> have "?\<S> ! i' \<in> \<H>"
        by (simp only:)
      then show ?thesis ..
    next
      case seq
      with \<open>?\<S> ! i' = \<S>\<^sub>2' ! ?i\<close> have "?\<S> ! i' \<in> lset \<S>\<^sub>1"
        by (simp only:)
      then show ?thesis
        by (intro disjI1 disjI2)
    next
      case rule_R'
      with assms(2) have "?\<S> ! (j + length \<S>\<^sub>2) = \<S>\<^sub>2' ! j" and "?\<S> ! (k + length \<S>\<^sub>2) = \<S>\<^sub>2' ! k"
        by (simp_all add: nth_append)
      with \<open>?\<S> ! i' = \<S>\<^sub>2' ! ?i\<close> and rule_R' have "
        {j + length \<S>\<^sub>2, k + length \<S>\<^sub>2} \<subseteq> {0..<i'} \<and>
        is_rule_R'_app \<H> p (?\<S> ! i') (?\<S> ! (j + length \<S>\<^sub>2)) (?\<S> ! (k + length \<S>\<^sub>2))"
        by auto
      then show ?thesis
        by (intro disjI2)
    qed
    with assms(1) and \<open>?i < length \<S>\<^sub>2'\<close> show ?thesis
      unfolding is_hyp_proof_def and is_hyp_proof_step_def by meson
  qed
  with assms(1) and \<open>?i < length \<S>\<^sub>2'\<close> show ?thesis
    by simp
qed

lemma hyp_proof_but_last_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ [A])"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  using assms and common_prefix_is_hyp_subproof_from[where \<S>\<^sub>2' = "[A]" and \<S>\<^sub>2'' = "[]"]
  by simp

lemma hyp_proof_prefix_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ \<S>\<^sub>2')"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  using assms and hyp_proof_but_last_is_hyp_proof
  by (induction \<S>\<^sub>2' arbitrary: \<S>\<^sub>2 rule: rev_induct) (simp, metis append.assoc)

lemma single_hyp_is_hyp_proof:
  assumes "A \<in> \<H>"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 [A]"
  using assms by fastforce

lemma single_thm_is_hyp_proof:
  assumes "A \<in> lset \<S>\<^sub>1"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 [A]"
  using assms by fastforce

lemma hyp_proofs_from_concatenation_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>1'" and "is_hyp_proof \<H> \<S>\<^sub>2 \<S>\<^sub>2'"
  shows "is_hyp_proof \<H> (\<S>\<^sub>1 @ \<S>\<^sub>2) (\<S>\<^sub>1' @ \<S>\<^sub>2')"
proof (standard, intro allI impI)
  let ?\<S> = "\<S>\<^sub>1 @ \<S>\<^sub>2" and ?\<S>' = "\<S>\<^sub>1' @ \<S>\<^sub>2'"
  fix i'
  assume "i' < length ?\<S>'"
  then consider (a) "i' < length \<S>\<^sub>1'" | (b) "i' \<in> {length \<S>\<^sub>1'..<length ?\<S>'}"
    by fastforce
  then show "is_hyp_proof_step \<H> ?\<S> ?\<S>' i'"
  proof cases
    case a
    from \<open>is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>1'\<close> have "is_hyp_proof \<H> (\<S>\<^sub>1 @ \<S>\<^sub>2) \<S>\<^sub>1'"
      by auto
    with assms(1) and a show ?thesis
      using added_suffix_hyp_proof_preservation[where \<S>\<^sub>1 = "\<S>\<^sub>1 @ \<S>\<^sub>2"] by auto
  next
    case b
    from assms(2) have "is_hyp_proof \<H> (\<S>\<^sub>1 @ \<S>\<^sub>2) \<S>\<^sub>2'"
      by auto
    with b show ?thesis
      using added_prefix_hyp_proof_preservation[where \<S>\<^sub>1 = "\<S>\<^sub>1 @ \<S>\<^sub>2"] by auto
  qed
qed

lemma elem_of_hyp_proof_is_wffo:
  assumes "is_hyps \<H>"
  and "lset \<S>\<^sub>1 \<subseteq> wffs\<^bsub>o\<^esub>"
  and "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  and "A \<in> lset \<S>\<^sub>2"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
using assms proof (induction \<S>\<^sub>2 rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc A' \<S>\<^sub>2)
  from \<open>is_hyp_proof \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ [A'])\<close> have "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
    using hyp_proof_prefix_is_hyp_proof[where \<S>\<^sub>2' = "[A']"] by presburger
  then show ?case
  proof (cases "A \<in> lset \<S>\<^sub>2")
    case True
    with snoc.prems(1,2) and \<open>is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2\<close> show ?thesis
      by (fact snoc.IH)
  next
    case False
    with snoc.prems(4) have "A' = A"
      by simp
    with snoc.prems(3) have "
      (\<S>\<^sub>2 @ [A]) ! i' \<in> \<H> \<or>
      (\<S>\<^sub>2 @ [A]) ! i' \<in> lset \<S>\<^sub>1 \<or>
      (\<S>\<^sub>2 @ [A]) ! i' \<in> wffs\<^bsub>o\<^esub>" if "i' \<in> {0..<length (\<S>\<^sub>2 @ [A])}" for i'
      using that by auto
    then have "A \<in> wffs\<^bsub>o\<^esub> \<or> A \<in> \<H> \<or> A \<in> lset \<S>\<^sub>1 \<or> length \<S>\<^sub>2 \<notin> {0..<Suc (length \<S>\<^sub>2)}"
      by (metis (no_types) length_append_singleton nth_append_length)
    with assms(1) and \<open>lset \<S>\<^sub>1 \<subseteq> wffs\<^bsub>o\<^esub>\<close> show ?thesis
      using atLeast0_lessThan_Suc by blast
  qed
qed

lemma hyp_prepended_to_hyp_proof_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  and "A \<in> \<H>"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 ([A] @ \<S>\<^sub>2)"
  using
    hyp_proofs_from_concatenation_is_hyp_proof
    [
      OF single_hyp_is_hyp_proof[OF assms(2)] assms(1),
      where \<S>\<^sub>1 = "[]"
    ]
  by simp

lemma hyp_appended_to_hyp_proof_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  and "A \<in> \<H>"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ [A])"
  using
    hyp_proofs_from_concatenation_is_hyp_proof
    [
      OF assms(1) single_hyp_is_hyp_proof[OF assms(2)],
      where \<S>\<^sub>2 = "[]"
    ]
  by simp

lemma dropped_duplicated_thm_in_hyp_proof_is_hyp_proof:
  assumes "is_hyp_proof \<H> (A # \<S>\<^sub>1) \<S>\<^sub>2"
  and "A \<in> lset \<S>\<^sub>1"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  using assms by auto

lemma thm_prepended_to_hyp_proof_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  and "A \<in> lset \<S>\<^sub>1"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 ([A] @ \<S>\<^sub>2)"
  using hyp_proofs_from_concatenation_is_hyp_proof[OF single_thm_is_hyp_proof[OF assms(2)] assms(1)]
  and dropped_duplicated_thm_in_hyp_proof_is_hyp_proof by simp

lemma thm_appended_to_hyp_proof_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2"
  and "A \<in> lset \<S>\<^sub>1"
  shows "is_hyp_proof \<H> \<S>\<^sub>1 (\<S>\<^sub>2 @ [A])"
  using hyp_proofs_from_concatenation_is_hyp_proof[OF assms(1) single_thm_is_hyp_proof[OF assms(2)]]
  and dropped_duplicated_thm_in_hyp_proof_is_hyp_proof by simp

lemma rule_R'_app_appended_to_hyp_proof_is_hyp_proof:
  assumes "is_hyp_proof \<H> \<S>' \<S>"
  and "i\<^sub>C < length \<S>" and "\<S> ! i\<^sub>C = C"
  and "i\<^sub>E < length \<S>" and "\<S> ! i\<^sub>E = E"
  and "is_rule_R'_app \<H> p D C E"
  shows "is_hyp_proof \<H> \<S>' (\<S> @ [D])"
proof (standard, intro allI impI)
  let ?\<S> = "\<S> @ [D]"
  fix i'
  assume "i' < length ?\<S>"
  then consider (a) "i' < length \<S>" | (b) "i' = length \<S>"
    by fastforce
  then show "is_hyp_proof_step \<H> \<S>' (\<S> @ [D]) i'"
  proof cases
    case a
    with assms(1) show ?thesis
      using added_suffix_hyp_proof_preservation by auto
  next
    case b
    let ?i\<^sub>D = "length \<S>"
    from assms(2,4) have "i\<^sub>C < ?i\<^sub>D" and "i\<^sub>E < ?i\<^sub>D"
      by fastforce+
    with assms(3,5,6) have "is_rule_R'_app \<H> p (?\<S> ! ?i\<^sub>D) (?\<S> ! i\<^sub>C) (?\<S> ! i\<^sub>E)"
      by (simp add: nth_append)
    with assms(2,4) have "
      \<exists>p j k. {j, k} \<subseteq> {0..<?i\<^sub>D} \<and> is_rule_R'_app \<H> p (?\<S> ! ?i\<^sub>D) (?\<S> ! j) (?\<S> ! k)"
      by (intro exI)+ auto
    then have "is_hyp_proof_step \<H> \<S>' ?\<S> (length ?\<S> - 1)"
      by simp
    moreover from b have "i' = length ?\<S> - 1"
      by simp
    ultimately show ?thesis
      by fast
  qed
qed

definition is_hyp_proof_of :: "form set \<Rightarrow> form list \<Rightarrow> form list \<Rightarrow> form \<Rightarrow> bool" where
  [iff]: "is_hyp_proof_of \<H> \<S>\<^sub>1 \<S>\<^sub>2 A \<longleftrightarrow>
    is_hyps \<H> \<and>
    is_proof \<S>\<^sub>1 \<and>
    \<S>\<^sub>2 \<noteq> [] \<and>
    is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2 \<and>
    last \<S>\<^sub>2 = A"

lemma hyp_proof_prefix_is_hyp_proof_of_last:
  assumes "is_hyps \<H>"
  and "is_proof \<S>''"
  and "is_hyp_proof \<H> \<S>'' (\<S> @ \<S>')" and "\<S> \<noteq> []"
  shows "is_hyp_proof_of \<H> \<S>'' \<S> (last \<S>)"
  using assms and hyp_proof_prefix_is_hyp_proof by simp

theorem hyp_derivability_implies_hyp_proof_existence:
  assumes "\<H> \<turnstile> A"
  shows "\<exists>\<S>\<^sub>1 \<S>\<^sub>2. is_hyp_proof_of \<H> \<S>\<^sub>1 \<S>\<^sub>2 A"
using assms proof (induction rule: is_derivable_from_hyps.induct)
  case (dv_hyp A)
  from \<open>A \<in> \<H>\<close> have "is_hyp_proof \<H> [] [A]"
    by (fact single_hyp_is_hyp_proof)
  moreover have "last [A] = A"
    by simp
  moreover have "is_proof []"
    by simp
  ultimately show ?case
    using \<open>is_hyps \<H>\<close> unfolding is_hyp_proof_of_def by (meson list.discI)
next
  case (dv_thm A)
  then obtain \<S> where "is_proof \<S>" and "\<S> \<noteq> []" and "last \<S> = A"
    by fastforce
  then have "is_hyp_proof \<H> \<S> [A]"
    using single_thm_is_hyp_proof by auto
  with \<open>is_hyps \<H>\<close> and \<open>is_proof \<S>\<close> have "is_hyp_proof_of \<H> \<S> [A] A"
    by fastforce
  then show ?case
    by (intro exI)
next
  case (dv_rule_R' C E p D)
  from dv_rule_R'.IH obtain \<S>\<^sub>C and \<S>\<^sub>C' and \<S>\<^sub>E and \<S>\<^sub>E' where
    "is_hyp_proof \<H> \<S>\<^sub>C' \<S>\<^sub>C" and "is_proof \<S>\<^sub>C'" and "\<S>\<^sub>C \<noteq> []" and "last \<S>\<^sub>C = C" and
    "is_hyp_proof \<H> \<S>\<^sub>E' \<S>\<^sub>E" and "is_proof \<S>\<^sub>E'" and "\<S>\<^sub>E \<noteq> []" and "last \<S>\<^sub>E = E"
    by auto
  let ?i\<^sub>C = "length \<S>\<^sub>C - 1" and ?i\<^sub>E = "length \<S>\<^sub>C + length \<S>\<^sub>E - 1" and ?i\<^sub>D = "length \<S>\<^sub>C + length \<S>\<^sub>E"
  let ?\<S> = "\<S>\<^sub>C @ \<S>\<^sub>E @ [D]"
  from \<open>\<S>\<^sub>C \<noteq> []\<close> have "?i\<^sub>C < length (\<S>\<^sub>C @ \<S>\<^sub>E)" and "?i\<^sub>E < length (\<S>\<^sub>C @ \<S>\<^sub>E)"
    using linorder_not_le by fastforce+
  moreover have "(\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>C = C" and "(\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>E = E"
    using \<open>\<S>\<^sub>C \<noteq> []\<close> and \<open>last \<S>\<^sub>C = C\<close> and \<open>\<S>\<^sub>E \<noteq> []\<close> and \<open>last \<S>\<^sub>E = E\<close>
    by
      (
        simp add: last_conv_nth nth_append,
        metis append_is_Nil_conv last_appendR last_conv_nth length_append
      )
  with \<open>is_rule_R'_app \<H> p D C E\<close> have "is_rule_R'_app \<H> p D ((\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>C) ((\<S>\<^sub>C @ \<S>\<^sub>E) ! ?i\<^sub>E)"
    by fastforce
  moreover from \<open>is_hyp_proof \<H> \<S>\<^sub>C' \<S>\<^sub>C\<close> and \<open>is_hyp_proof \<H> \<S>\<^sub>E' \<S>\<^sub>E\<close>
  have "is_hyp_proof \<H> (\<S>\<^sub>C' @ \<S>\<^sub>E') (\<S>\<^sub>C @ \<S>\<^sub>E)"
    by (fact hyp_proofs_from_concatenation_is_hyp_proof)
  ultimately have "is_hyp_proof \<H> (\<S>\<^sub>C' @ \<S>\<^sub>E') ((\<S>\<^sub>C @ \<S>\<^sub>E) @ [D])"
    using rule_R'_app_appended_to_hyp_proof_is_hyp_proof
    by presburger
  moreover from \<open>is_proof \<S>\<^sub>C'\<close> and \<open>is_proof \<S>\<^sub>E'\<close> have "is_proof (\<S>\<^sub>C' @ \<S>\<^sub>E')"
    by (fact proofs_concatenation_is_proof)
  ultimately have "is_hyp_proof_of \<H> (\<S>\<^sub>C' @ \<S>\<^sub>E') ((\<S>\<^sub>C @ \<S>\<^sub>E) @ [D]) D"
    using \<open>is_hyps \<H>\<close> by fastforce
  then show ?case
    by (intro exI)
qed

theorem hyp_proof_existence_implies_hyp_derivability:
  assumes "\<exists>\<S>\<^sub>1 \<S>\<^sub>2. is_hyp_proof_of \<H> \<S>\<^sub>1 \<S>\<^sub>2 A"
  shows "\<H> \<turnstile> A"
proof -
  from assms obtain \<S>\<^sub>1 and \<S>\<^sub>2
    where "is_hyps \<H>" and "is_proof \<S>\<^sub>1" and "\<S>\<^sub>2 \<noteq> []" and "is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2" and "last \<S>\<^sub>2 = A"
    by fastforce
  then show ?thesis
  proof (induction "length \<S>\<^sub>2" arbitrary: \<S>\<^sub>2 A rule: less_induct)
    case less
    let ?i' = "length \<S>\<^sub>2 - 1"
    from \<open>\<S>\<^sub>2 \<noteq> []\<close> and \<open>last \<S>\<^sub>2 = A\<close> have "\<S>\<^sub>2 ! ?i' = A"
      by (simp add: last_conv_nth)
    from \<open>is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2\<close> and \<open>\<S>\<^sub>2 \<noteq> []\<close> have "is_hyp_proof_step \<H> \<S>\<^sub>1 \<S>\<^sub>2 ?i'"
      by simp
    then consider
      (hyp) "\<S>\<^sub>2 ! ?i' \<in> \<H>"
    | (seq) "\<S>\<^sub>2 ! ?i' \<in> lset \<S>\<^sub>1"
    | (rule_R') "\<exists>p j k. {j, k} \<subseteq> {0..<?i'} \<and> is_rule_R'_app \<H> p (\<S>\<^sub>2 ! ?i') (\<S>\<^sub>2 ! j) (\<S>\<^sub>2 ! k)"
      by force
    then show ?case
    proof cases
      case hyp
      with \<open>\<S>\<^sub>2 ! ?i' = A\<close> and \<open>is_hyps \<H>\<close> show ?thesis
        by (fastforce intro: dv_hyp)
    next
      case seq
      from \<open>\<S>\<^sub>2 ! ?i' \<in> lset \<S>\<^sub>1\<close> and \<open>\<S>\<^sub>2 ! ?i' = A\<close>
      obtain j where "\<S>\<^sub>1 ! j = A" and "\<S>\<^sub>1 \<noteq> []" and "j < length \<S>\<^sub>1"
        by (metis empty_iff in_set_conv_nth list.set(1))
      with \<open>is_proof \<S>\<^sub>1\<close> have "is_proof (take (Suc j) \<S>\<^sub>1)" and "take (Suc j) \<S>\<^sub>1 \<noteq> []"
        using proof_prefix_is_proof[where \<S>\<^sub>1 = "take (Suc j) \<S>\<^sub>1" and \<S>\<^sub>2 = "drop (Suc j) \<S>\<^sub>1"]
        by simp_all
      moreover from \<open>\<S>\<^sub>1 ! j = A\<close> and \<open>j < length \<S>\<^sub>1\<close> have "last (take (Suc j) \<S>\<^sub>1) = A"
        by (simp add: take_Suc_conv_app_nth)
      ultimately have "is_proof_of (take (Suc j) \<S>\<^sub>1) A"
        by fastforce
      then have "is_theorem A"
        using is_theorem_def by blast
      with \<open>is_hyps \<H>\<close> show ?thesis
        by (intro dv_thm)
    next
      case rule_R'
      then obtain p and j and k
        where "{j, k} \<subseteq> {0..<?i'}" and "is_rule_R'_app \<H> p (\<S>\<^sub>2 ! ?i') (\<S>\<^sub>2 ! j) (\<S>\<^sub>2 ! k)"
        by force
      let ?\<S>\<^sub>j = "take (Suc j) \<S>\<^sub>2" and ?\<S>\<^sub>k = "take (Suc k) \<S>\<^sub>2"
      obtain \<S>\<^sub>j' and \<S>\<^sub>k' where "\<S>\<^sub>2 = ?\<S>\<^sub>j @ \<S>\<^sub>j'" and "\<S>\<^sub>2 = ?\<S>\<^sub>k @ \<S>\<^sub>k'"
        by (metis append_take_drop_id)
      then have "is_hyp_proof \<H> \<S>\<^sub>1 (?\<S>\<^sub>j @ \<S>\<^sub>j')" and "is_hyp_proof \<H> \<S>\<^sub>1 (?\<S>\<^sub>k @ \<S>\<^sub>k')"
        by (simp_all only: \<open>is_hyp_proof \<H> \<S>\<^sub>1 \<S>\<^sub>2\<close>)
      moreover from \<open>\<S>\<^sub>2 \<noteq> []\<close> and \<open>\<S>\<^sub>2 = ?\<S>\<^sub>j @ \<S>\<^sub>j'\<close> and \<open>\<S>\<^sub>2 = ?\<S>\<^sub>k @ \<S>\<^sub>k'\<close> and \<open>last \<S>\<^sub>2 = A\<close>
      have "last \<S>\<^sub>j' = A" and "last \<S>\<^sub>k' = A"
        using \<open>{j, k} \<subseteq> {0..<length \<S>\<^sub>2 - 1}\<close> and take_tl and less_le_not_le and append.right_neutral
        by (metis atLeastLessThan_iff insert_subset last_appendR length_tl take_all_iff)+
      moreover from \<open>\<S>\<^sub>2 \<noteq> []\<close> have "?\<S>\<^sub>j \<noteq> []" and "?\<S>\<^sub>k \<noteq> []"
        by simp_all
      ultimately have "is_hyp_proof_of \<H> \<S>\<^sub>1 ?\<S>\<^sub>j (last ?\<S>\<^sub>j)" and "is_hyp_proof_of \<H> \<S>\<^sub>1 ?\<S>\<^sub>k (last ?\<S>\<^sub>k)"
        using hyp_proof_prefix_is_hyp_proof_of_last
          [OF \<open>is_hyps \<H>\<close> \<open>is_proof \<S>\<^sub>1\<close> \<open>is_hyp_proof \<H> \<S>\<^sub>1 (?\<S>\<^sub>j @ \<S>\<^sub>j')\<close> \<open>?\<S>\<^sub>j \<noteq> []\<close>]
        and hyp_proof_prefix_is_hyp_proof_of_last
          [OF \<open>is_hyps \<H>\<close> \<open>is_proof \<S>\<^sub>1\<close> \<open>is_hyp_proof \<H> \<S>\<^sub>1 (?\<S>\<^sub>k @ \<S>\<^sub>k')\<close> \<open>?\<S>\<^sub>k \<noteq> []\<close>]
        by fastforce+
      moreover from \<open>last \<S>\<^sub>j' = A\<close> and \<open>last \<S>\<^sub>k' = A\<close>
      have "length ?\<S>\<^sub>j < length \<S>\<^sub>2" and "length ?\<S>\<^sub>k < length \<S>\<^sub>2"
        using \<open>{j, k} \<subseteq> {0..<length \<S>\<^sub>2 - 1}\<close> by force+
      moreover from calculation(3,4) have "last ?\<S>\<^sub>j = \<S>\<^sub>2 ! j" and "last ?\<S>\<^sub>k = \<S>\<^sub>2 ! k"
        by (metis Suc_lessD last_snoc linorder_not_le nat_neq_iff take_Suc_conv_app_nth take_all_iff)+
      ultimately have "\<H> \<turnstile> \<S>\<^sub>2 ! j" and "\<H> \<turnstile> \<S>\<^sub>2 ! k"
        using \<open>is_hyps \<H>\<close>
        and less(1)[OF \<open>length ?\<S>\<^sub>j < length \<S>\<^sub>2\<close>] and less(1)[OF \<open>length ?\<S>\<^sub>k < length \<S>\<^sub>2\<close>]
        by fast+
      with \<open>is_hyps \<H>\<close> and \<open>\<S>\<^sub>2 ! ?i' = A\<close> show ?thesis
        using \<open>is_rule_R'_app \<H> p (\<S>\<^sub>2 ! ?i') (\<S>\<^sub>2 ! j) (\<S>\<^sub>2 ! k)\<close> by (blast intro: dv_rule_R')
    qed
  qed
qed

theorem hypothetical_derivability_proof_existence_equivalence:
  shows "\<H> \<turnstile> A \<longleftrightarrow> (\<exists>\<S>\<^sub>1 \<S>\<^sub>2. is_hyp_proof_of \<H> \<S>\<^sub>1 \<S>\<^sub>2 A)"
  using hyp_derivability_implies_hyp_proof_existence and hyp_proof_existence_implies_hyp_derivability ..

proposition derivability_from_no_hyps_theoremhood_equivalence:
  shows "{} \<turnstile> A \<longleftrightarrow> is_theorem A"
proof
  assume "{} \<turnstile> A"
  then show "is_theorem A"
  proof (induction rule: is_derivable_from_hyps.induct)
    case (dv_rule_R' C E p D)
    from \<open>is_rule_R'_app {} p D C E\<close> have "is_rule_R_app p D C E"
      by simp
    moreover from \<open>is_theorem C\<close> and \<open>is_theorem E\<close> have "is_derivable C" and "is_derivable E"
      using theoremhood_derivability_equivalence by (simp_all only:)
    ultimately have "is_derivable D"
      by (fastforce intro: dv_rule_R)
    then show ?case
      using theoremhood_derivability_equivalence by (simp only:)
  qed simp
next
  assume "is_theorem A"
  then show "{} \<turnstile> A"
    by (blast intro: dv_thm)
qed

abbreviation is_derivable_from_no_hyps ("\<turnstile> _" [50] 50) where
  "\<turnstile> A \<equiv> {} \<turnstile> A"

corollary derivability_implies_hyp_derivability:
  assumes "\<turnstile> A" and "is_hyps \<H>"
  shows "\<H> \<turnstile> A"
  using assms and derivability_from_no_hyps_theoremhood_equivalence and dv_thm by simp

lemma axiom_is_derivable_from_no_hyps:
  assumes "A \<in> axioms"
  shows "\<turnstile> A"
  using derivability_from_no_hyps_theoremhood_equivalence
  and derivable_form_is_theorem[OF dv_axiom[OF assms]] by (simp only:)

lemma axiom_is_derivable_from_hyps:
  assumes "A \<in> axioms" and "is_hyps \<H>"
  shows "\<H> \<turnstile> A"
  using assms and axiom_is_derivable_from_no_hyps and derivability_implies_hyp_derivability by blast

lemma rule_R [consumes 2, case_names occ_subform replacement]:
  assumes "\<turnstile> C" and "\<turnstile> A =\<^bsub>\<alpha>\<^esub> B"
  and "A \<preceq>\<^bsub>p\<^esub> C" and "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D"
  shows "\<turnstile> D"
proof -
  from assms(1,2) have "is_derivable C" and "is_derivable (A =\<^bsub>\<alpha>\<^esub> B)"
    using derivability_from_no_hyps_theoremhood_equivalence
    and theoremhood_derivability_equivalence by blast+
  moreover have "is_rule_R_app p D C (A =\<^bsub>\<alpha>\<^esub> B)"
  proof -
    from assms(1-4) have "D \<in> wffs\<^bsub>o\<^esub>" and "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
      by (meson hyp_derivable_form_is_wffso replacement_preserves_typing wffs_from_equality)+
    with assms(3,4) show ?thesis
      by fastforce
  qed
  ultimately have "is_derivable D"
    by (rule dv_rule_R)
  then show ?thesis
    using derivability_from_no_hyps_theoremhood_equivalence and derivable_form_is_theorem by simp
qed

lemma rule_R' [consumes 2, case_names occ_subform replacement no_capture]:
  assumes "\<H> \<turnstile> C" and "\<H> \<turnstile> A =\<^bsub>\<alpha>\<^esub> B"
  and "A \<preceq>\<^bsub>p\<^esub> C" and "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> D"
  and "rule_R'_side_condition \<H> p D C (A =\<^bsub>\<alpha>\<^esub> B)"
  shows "\<H> \<turnstile> D"
using assms(1,2) proof (rule dv_rule_R')
  from assms(1) show "is_hyps \<H>"
    by (blast elim: is_derivable_from_hyps.cases)
  moreover from assms(1-4) have "D \<in> wffs\<^bsub>o\<^esub>"
    by (meson hyp_derivable_form_is_wffso replacement_preserves_typing wffs_from_equality)
  ultimately show "is_rule_R'_app \<H> p D C (A =\<^bsub>\<alpha>\<^esub> B)"
    using assms(2-5) and hyp_derivable_form_is_wffso and wffs_from_equality
    unfolding is_rule_R_app_def and is_rule_R'_app_def by metis
qed

end
