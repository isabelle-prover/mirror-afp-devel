theory MLSS_Typing_Urelems
  imports MLSS_Suc_Theory MLSS_Typing
begin

section \<open>Typing the Urelements\<close>
text \<open>
  In this theory, we define a recursive procedure that generates Typing
  constraints. We then prove that the constraints can be solved with
  \<^const>\<open>MLSS_Suc_Theory.assign\<close>. The solution then gives us the urelements.
\<close>

abbreviation (input) "SVar \<equiv> MLSS_Suc_Theory.Var"
abbreviation (input) "SEq \<equiv> MLSS_Suc_Theory.Eq"
abbreviation (input) "SNEq \<equiv> MLSS_Suc_Theory.NEq"
abbreviation (input) "ssolve \<equiv> MLSS_Suc_Theory.solve"
abbreviation (input) "sassign \<equiv> MLSS_Suc_Theory.assign"

fun constrs_term :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_term \<Rightarrow> 'b suc_atom list" where
  "constrs_term n (Var x) = [SEq (SVar (n (Var x))) (SVar (n (Var x)))]"
| "constrs_term n (\<emptyset> k) = [SEq (SVar (n (\<emptyset> k))) (Succ (Suc k) Zero)]"
| "constrs_term n (t1 \<squnion>\<^sub>s t2) =
    [SEq (SVar (n (t1 \<squnion>\<^sub>s t2))) (SVar (n t1)), SEq (SVar (n t1)) (SVar (n t2)), SNEq (SVar (n t1)) Zero]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_term n (t1 \<sqinter>\<^sub>s t2) =
    [SEq (SVar (n (t1 \<sqinter>\<^sub>s t2))) (SVar (n t1)), SEq (SVar (n t1)) (SVar (n t2)), SNEq (SVar (n t1)) Zero]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_term n (t1 -\<^sub>s t2) =
    [SEq (SVar (n (t1 -\<^sub>s t2))) (SVar (n t1)), SEq (SVar (n t1)) (SVar (n t2)), SNEq (SVar (n t1)) Zero]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_term n (Single t) =
    [SEq (SVar (n (Single t))) (Succ 1 (SVar (n t)))]
    @ constrs_term n t"
      
fun constrs_atom :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_atom \<Rightarrow> 'b suc_atom list" where
  "constrs_atom n (t1 =\<^sub>s t2) =
    [SEq (SVar (n t1)) (SVar (n t2))]
    @ constrs_term n t1 @ constrs_term n t2"
| "constrs_atom n (t1 \<in>\<^sub>s t2) =
    [SEq (SVar (n t2)) (Succ 1 (SVar (n t1)))]
    @ constrs_term n t1 @ constrs_term n t2"

fun constrs_fm :: "('a pset_term \<Rightarrow> 'b) \<Rightarrow> 'a pset_fm \<Rightarrow> 'b suc_atom list" where
  "constrs_fm n (Atom a) = constrs_atom n a"
| "constrs_fm n (And p q) = constrs_fm n p @ constrs_fm n q"
| "constrs_fm n (Or p q) = constrs_fm n p @ constrs_fm n q"
| "constrs_fm n (Neg p) = constrs_fm n p"

lemma is_Succ_normal_constrs_term:
  "\<forall>a \<in> set (constrs_term n t). MLSS_Suc_Theory.is_Eq a \<longrightarrow> is_Succ_normal a"
  by (induction t) auto

lemma is_Succ_normal_constrs_atom:
  "\<forall>a \<in> set (constrs_atom n a). MLSS_Suc_Theory.is_Eq a \<longrightarrow> is_Succ_normal a"
  by (cases a) (use is_Succ_normal_constrs_term in auto)

lemma is_Succ_normal_constrs_fm:
  "\<forall>a \<in> set (constrs_fm n \<phi>). MLSS_Suc_Theory.is_Eq a \<longrightarrow> is_Succ_normal a"
  by (induction \<phi>) (use is_Succ_normal_constrs_atom in auto)

lemma is_Var_Eq_Zero_if_is_NEq_constrs_term:
  "\<forall>a \<in> set (constrs_term n t). MLSS_Suc_Theory.is_NEq a \<longrightarrow> (\<exists>x. a = SNEq (SVar x) Zero)"
  by (induction t) auto

lemma is_Var_Eq_Zero_if_is_NEq_constrs_atom:
  "\<forall>a \<in> set (constrs_atom n a). MLSS_Suc_Theory.is_NEq a \<longrightarrow> (\<exists>x. a = SNEq (SVar x) Zero)"
  by (cases a) (use is_Var_Eq_Zero_if_is_NEq_constrs_term in auto)

lemma is_Var_Eq_Zero_if_is_NEq_constrs_fm:
  "\<forall>a \<in> set (constrs_fm n \<phi>). MLSS_Suc_Theory.is_NEq a \<longrightarrow> (\<exists>x. a = SNEq (SVar x) Zero)"
  by (induction \<phi>) (use is_Var_Eq_Zero_if_is_NEq_constrs_atom in auto)

lemma types_term_if_I_atom_constrs_term:
  includes Set_member_no_ascii_notation
  assumes "(\<forall>e \<in> set (constrs_term n t). MLSS_Suc_Theory.I_atom v e)"
  shows "(\<lambda>x. v (n (Var x))) \<turnstile> t : v (n t)"
  using assms
  by (induction t) (auto intro: types_pset_term.intros)

lemma types_pset_atom_if_I_atom_constrs_atom:
  fixes a :: "'a pset_atom"
  assumes "(\<forall>e \<in> set (constrs_atom n a). MLSS_Suc_Theory.I_atom v e)"
  shows "(\<lambda>x. v (n (Var x))) \<turnstile> a"
  using assms
  by (cases a)
     (auto simp: types_pset_atom.simps ball_Un dest!: types_term_if_I_atom_constrs_term)

lemma types_pset_fm_if_I_atom_constrs_fm:
  fixes \<phi> :: "'a pset_fm"
  assumes "(\<forall>e \<in> set (constrs_fm n \<phi>). MLSS_Suc_Theory.I_atom v e)"
  shows "(\<lambda>x. v (n (Var x))) \<turnstile> \<phi>"
  using assms
  by (induction \<phi>)
     (auto intro: types_fmI types_pset_atom_if_I_atom_constrs_atom)

lemma I_atom_constrs_term_if_types_term:
  includes Set_member_no_ascii_notation
  assumes "inj_on n T" "subterms t \<subseteq> T"
  assumes "v \<turnstile> t : k"
  shows "(\<forall>e \<in> set (constrs_term n t).
    MLSS_Suc_Theory.I_atom (\<lambda>x. type_of_term v (inv_into T n x)) e)"
  using assms inv_into_f_f[OF assms(1) subsetD[OF assms(2)]]
  by (induction t arbitrary: T k)
     (auto elim!: types_pset_term_cases intro!: type_of_term_if_types_term
           simp: type_of_term_if_types_term)

lemma I_atom_constrs_atom_if_types_pset_atom:
  fixes a :: "'a pset_atom"
  assumes "inj_on n T" "subterms a \<subseteq> T"
  assumes "v \<turnstile> a"
  shows "(\<forall>e \<in> set (constrs_atom n a).
    MLSS_Suc_Theory.I_atom (\<lambda>x. type_of_term v (inv_into T n x)) e)"
  using assms I_atom_constrs_term_if_types_term
  by (cases a)
     (force simp: types_pset_atom.simps type_of_term_if_types_term subsetD)+

lemma I_atom_constrs_fm_if_types_pset_fm:
  fixes \<phi> :: "'a pset_fm"
  assumes "inj_on n T" "subterms \<phi> \<subseteq> T"
  assumes "v \<turnstile> \<phi>"
  shows "(\<forall>e \<in> set (constrs_fm n \<phi>).
    MLSS_Suc_Theory.I_atom (\<lambda>x. type_of_term v (inv_into T n x)) e)"
  using assms
  by (induction \<phi>)
     (auto dest: types_fmD simp: I_atom_constrs_atom_if_types_pset_atom)

lemma inv_into_f_eq_if_subs:
  assumes "inj_on f B" "A \<subseteq> B" "y \<in> f ` A"
  shows "inv_into B f y = inv_into A f y"
  using assms inv_into_f_eq
  by (metis f_inv_into_f inv_into_into subset_eq)

lemma UN_set_suc_atom_constrs_term_eq_image_subterms:
  "\<Union>(set_suc_atom ` set (constrs_term n t)) = n ` subterms t"
  by (induction t) auto

lemma UN_set_suc_atom_constrs_atom_eq_image_subterms:
  "\<Union>(set_suc_atom ` set (constrs_atom n a)) = n ` subterms a"
  by (induction a) (auto simp: UN_set_suc_atom_constrs_term_eq_image_subterms)

lemma UN_set_suc_atom_constrs_fm_eq_image_subterms:
  "\<Union>(set_suc_atom ` set (constrs_fm n \<phi>)) = n ` subterms \<phi>"
  by (induction \<phi>) (auto simp: UN_set_suc_atom_constrs_atom_eq_image_subterms)

lemma
  fixes \<phi> :: "'a pset_fm"
  assumes "inj_on n (subterms \<phi>)"
  assumes "ssolve (MLSS_Suc_Theory.elim_NEq_Zero (constrs_fm n \<phi>)) = Some ss"
  shows types_pset_fm_assign_solve: "(\<lambda>x. sassign ss (n (Var x))) \<turnstile> \<phi>"
    and minimal_assign_solve: "\<lbrakk> v \<turnstile> \<phi>; z \<in> vars \<phi> \<rbrakk> \<Longrightarrow> sassign ss (n (Var z)) \<le> v z"
proof -
  note I_atom_assign_if_solve_elim_NEq_Zero_Some[OF _ _ assms(2)]
  then have "\<forall>e \<in> set (constrs_fm n \<phi>). MLSS_Suc_Theory.I_atom (sassign ss) e"
    using is_Succ_normal_constrs_fm is_Var_Eq_Zero_if_is_NEq_constrs_fm by blast
  note types_pset_fm_if_I_atom_constrs_fm[OF this]
  then show "(\<lambda>x. sassign ss (n (Var x))) \<turnstile> \<phi>" .

  let ?v' = "\<lambda>x. type_of_term v (inv_into (subterms \<phi>) n x)"
  note I_atom_assign_minimal_if_solve_elim_NEq_Zero_Some[OF _ _ assms(2)]
  then have assign_leq: "sassign ss z \<le> v z"
    if "\<forall>a \<in> set (constrs_fm n \<phi>). MLSS_Suc_Theory.I_atom v a"
       "z \<in> \<Union> (set_suc_atom ` set (constrs_fm n \<phi>))" for v z
    using that is_Succ_normal_constrs_fm is_Var_Eq_Zero_if_is_NEq_constrs_fm
    by blast
  show "sassign ss (n (Var z)) \<le> v z" if "v \<turnstile> \<phi>" "z \<in> vars \<phi>"
  proof -
    note assign_leq[unfolded UN_set_suc_atom_constrs_fm_eq_image_subterms, where ?v="?v'"]
    note assign_leq' = this[OF I_atom_constrs_fm_if_types_pset_fm[OF assms(1) _ \<open>v \<turnstile> \<phi>\<close>, simplified]]

    from \<open>z \<in> vars \<phi>\<close> have "n (Var z) \<in> n ` subterms \<phi>"
      by (simp add: vars_fm_subs_subterms_fm)
    from assign_leq'[OF this] \<open>inj_on n (subterms \<phi>)\<close> \<open>z \<in> vars \<phi>\<close> show ?thesis
      using vars_fm_subs_subterms_fm
      by (metis inv_into_f_f type_of_term_if_types_term types_pset_term.intros(2))
  qed
qed

  
lemma types_term_minimal:
  includes Set_member_no_ascii_notation
  assumes "\<And>z. z \<in> vars t \<Longrightarrow> v_min z \<le> v z"
  assumes "v_min \<turnstile> t : k'" "v \<turnstile> t : k"
  shows "k' \<le> k"
  using assms
  by (induction t arbitrary: k' k) (auto elim!: types_pset_term_cases)

lemma constrs_term_subs_constrs_term:
  assumes "s \<in> subterms t"
  shows "set (constrs_term n s) \<subseteq> set (constrs_term n t)"
  using assms
  by (induction t) auto

lemma constrs_term_subs_constrs_atom:
  assumes "t \<in> subterms a"
  shows "set (constrs_term n t) \<subseteq> set (constrs_atom n a)"
  using assms constrs_term_subs_constrs_term by (cases a) force+

lemma constrs_term_subs_constrs_fm:
  assumes "t \<in> subterms \<phi>"
  shows "set (constrs_term n t) \<subseteq> set (constrs_fm n \<phi>)"
  using assms
  by (induction \<phi>) (auto simp: constrs_term_subs_constrs_atom)

lemma urelem_iff_assign_eq_0:
  includes Set_member_no_ascii_notation
  assumes "inj_on n (subterms \<phi>)"
  assumes "t \<in> subterms \<phi>"
  assumes "ssolve (MLSS_Suc_Theory.elim_NEq_Zero (constrs_fm n \<phi>)) = Some ss"
  shows "urelem \<phi> t \<longleftrightarrow> sassign ss (n t) = 0"
proof -
  note types = types_pset_fm_assign_solve[OF assms(1,3)]

  note I_atom_assign_if_solve_elim_NEq_Zero_Some[OF _ _ assms(3)]
  then have "\<forall>e \<in> set (constrs_fm n \<phi>). MLSS_Suc_Theory.I_atom (sassign ss) e"
    using is_Succ_normal_constrs_fm is_Var_Eq_Zero_if_is_NEq_constrs_fm by blast
  then have "\<forall>e \<in> set (constrs_term n t). MLSS_Suc_Theory.I_atom (sassign ss) e"
    using constrs_term_subs_constrs_fm[OF \<open>t \<in> subterms \<phi>\<close>] by blast
  note type_term_t = types_term_if_I_atom_constrs_term[OF this]

  note minimal = minimal_assign_solve[OF assms(1,3)]
  have "\<exists>lt'. v \<turnstile> t : lt' \<and> sassign ss (n t) \<le> lt'"
    if "v \<turnstile> \<phi>" for v
  proof -
    from that obtain lt' where "v \<turnstile> t : lt'"
      using \<open>t \<in> subterms \<phi>\<close>
      by (meson not_Some_eq subterms_type_pset_fm_not_None)
    moreover note minimal[OF that] types_term_minimal[OF _ type_term_t]
    ultimately show ?thesis
      by (metis assms(2) mem_vars_fm_if_mem_subterms_fm)
  qed
  
  then show "urelem \<phi> t \<longleftrightarrow> sassign ss (n t) = 0"
    using types type_term_t types_term_unique unfolding urelem_def
    by (metis le_zero_eq)
qed

lemma not_types_fm_if_solve_eq_None:
  fixes \<phi> :: "'a pset_fm"
  assumes "inj_on n (subterms \<phi>)"
  assumes "ssolve (MLSS_Suc_Theory.elim_NEq_Zero (constrs_fm n \<phi>)) = None"
  shows "\<not> v \<turnstile> \<phi>"
proof
  assume "v \<turnstile> \<phi>"
  note I_atom_constrs_fm_if_types_pset_fm[OF assms(1) _ this]
  moreover
  note not_I_atom_if_solve_elim_NEq_Zero_None[OF _ _ assms(2)]
  then have "\<exists>a\<in>set (constrs_fm n \<phi>). \<not> MLSS_Suc_Theory.I_atom v a" for v
    using is_Succ_normal_constrs_fm is_Var_Eq_Zero_if_is_NEq_constrs_fm by blast
  ultimately show False
    by blast
qed

end