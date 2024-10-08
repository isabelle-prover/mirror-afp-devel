(*  Title:       Integration of IsaFoR Terms and the Knuth-Bendix Order
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Integration of \textsf{IsaFoR} Terms and the Knuth--Bendix Order\<close>

text \<open>
This theory implements the abstract interface for atoms and substitutions using
the \textsf{IsaFoR} library.
\<close>

theory IsaFoR_Term
  imports
    Deriving.Derive
    Ordered_Resolution_Prover.Abstract_Substitution
    First_Order_Terms.Unification
    First_Order_Terms.Subsumption
    "HOL-Cardinals.Wellorder_Extension"
    Open_Induction.Restricted_Predicates
    Knuth_Bendix_Order.KBO
begin

hide_const (open) mgu

abbreviation subst_apply_literal ::
  "('f, 'v) term literal \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term literal" (infixl \<open>\<cdot>lit\<close> 60) where
  "L \<cdot>lit \<sigma> \<equiv> map_literal (\<lambda>A. A \<cdot> \<sigma>) L"

definition subst_apply_clause ::
  "('f, 'v) term clause \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term clause" (infixl \<open>\<cdot>cls\<close> 60) where
  "C \<cdot>cls \<sigma> = image_mset (\<lambda>L. L \<cdot>lit \<sigma>) C"

abbreviation vars_lit :: "('f, 'v) term literal \<Rightarrow> 'v set" where
  "vars_lit L \<equiv> vars_term (atm_of L)"

definition vars_clause :: "('f, 'v) term clause \<Rightarrow> 'v set" where
  "vars_clause C = Union (set_mset (image_mset vars_lit C))"

definition vars_clause_list :: "('f, 'v) term clause list \<Rightarrow> 'v set" where
  "vars_clause_list Cs = Union (vars_clause ` set Cs) "

definition vars_partitioned :: "('f,'v) term clause list \<Rightarrow> bool" where
  "vars_partitioned Cs \<longleftrightarrow>
   (\<forall>i < length Cs. \<forall>j < length Cs. i \<noteq> j \<longrightarrow> (vars_clause (Cs ! i) \<inter> vars_clause (Cs ! j)) = {})"

lemma vars_clause_mono: "S \<subseteq># C \<Longrightarrow> vars_clause S \<subseteq> vars_clause C"
  unfolding vars_clause_def by auto

interpretation substitution_ops "(\<cdot>)" Var "(\<circ>\<^sub>s)" .

lemma is_ground_atm_is_ground_on_var:
  assumes "is_ground_atm (A \<cdot> \<sigma>)" and "v \<in> vars_term A"
  shows "is_ground_atm (\<sigma> v)"
using assms proof (induction A)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ts)
  then show ?case unfolding is_ground_atm_def
    by auto
qed

lemma is_ground_lit_is_ground_on_var:
  assumes ground_lit: "is_ground_lit (subst_lit L \<sigma>)" and v_in_L: "v \<in> vars_lit L"
  shows "is_ground_atm (\<sigma> v)"
proof -
  let ?A = "atm_of L"
  from v_in_L have A_p: "v \<in> vars_term ?A"
    by auto
  then have "is_ground_atm (?A \<cdot> \<sigma>)"
    using ground_lit unfolding is_ground_lit_def by auto
  then show ?thesis
    using A_p is_ground_atm_is_ground_on_var by metis
qed

lemma is_ground_cls_is_ground_on_var:
  assumes
    ground_clause: "is_ground_cls (subst_cls C \<sigma>)" and
    v_in_C: "v \<in> vars_clause C"
  shows "is_ground_atm (\<sigma> v)"
proof -
  from v_in_C obtain L where L_p: "L \<in># C" "v \<in> vars_lit L"
    unfolding vars_clause_def by auto
  then have "is_ground_lit (subst_lit L \<sigma>)"
    using ground_clause unfolding is_ground_cls_def subst_cls_def by auto
  then show ?thesis
    using L_p is_ground_lit_is_ground_on_var by metis
qed

lemma is_ground_cls_list_is_ground_on_var:
  assumes ground_list: "is_ground_cls_list (subst_cls_list Cs \<sigma>)"
    and v_in_Cs: "v \<in> vars_clause_list Cs"
  shows "is_ground_atm (\<sigma> v)"
proof -
  from v_in_Cs obtain C where C_p: "C \<in> set Cs" "v \<in> vars_clause C"
    unfolding vars_clause_list_def by auto
  then have "is_ground_cls (subst_cls C \<sigma>)"
    using ground_list unfolding is_ground_cls_list_def subst_cls_list_def by auto
  then show ?thesis
    using C_p is_ground_cls_is_ground_on_var by metis
qed

lemma same_on_vars_lit:
  assumes "\<forall>v \<in> vars_lit L. \<sigma> v = \<tau> v"
  shows "subst_lit L \<sigma> = subst_lit L \<tau>"
  using assms
proof (induction L)
  case (Pos x)
  then have "\<forall>v \<in> vars_term x. \<sigma> v = \<tau> v \<Longrightarrow> subst_atm_abbrev x \<sigma> = subst_atm_abbrev x \<tau>"
    using term_subst_eq by metis+
  then show ?case
    unfolding subst_lit_def using Pos by auto
next
  case (Neg x)
  then have "\<forall>v \<in> vars_term x. \<sigma> v = \<tau> v \<Longrightarrow> subst_atm_abbrev x \<sigma> = subst_atm_abbrev x \<tau>"
    using term_subst_eq by metis+
  then show ?case
    unfolding subst_lit_def using Neg by auto
qed

lemma in_list_of_mset_in_S:
  assumes "i < length (list_of_mset S)"
  shows "list_of_mset S ! i \<in># S"
proof -
  from assms have "list_of_mset S ! i \<in> set (list_of_mset S)"
    by auto
  then have "list_of_mset S ! i \<in># mset (list_of_mset S)"
    by (meson in_multiset_in_set)
  then show ?thesis
    by auto
qed

lemma same_on_vars_clause:
  assumes "\<forall>v \<in> vars_clause S. \<sigma> v = \<tau> v"
  shows "subst_cls S \<sigma> = subst_cls S \<tau>"
  by (smt assms image_eqI image_mset_cong2 mem_simps(9) same_on_vars_lit set_image_mset
      subst_cls_def vars_clause_def)

interpretation substitution "(\<cdot>)" "Var :: _ \<Rightarrow> ('f, nat) term" "(\<circ>\<^sub>s)"
proof unfold_locales
  show "\<And>A. A \<cdot> Var = A"
    by auto
next
  show "\<And>A \<tau> \<sigma>. A \<cdot> \<tau> \<circ>\<^sub>s \<sigma> = A \<cdot> \<tau> \<cdot> \<sigma>"
    by auto
next
  show "\<And>\<sigma> \<tau>. (\<And>A. A \<cdot> \<sigma> = A \<cdot> \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    by (simp add: subst_term_eqI)
next
  fix C :: "('f, nat) term clause"
  fix \<sigma>
  assume "is_ground_cls (subst_cls C \<sigma>)"
  then have ground_atms_\<sigma>: "\<And>v. v \<in> vars_clause C \<Longrightarrow> is_ground_atm (\<sigma> v)"
    by (meson is_ground_cls_is_ground_on_var)

  define some_ground_trm :: "('f, nat) term" where "some_ground_trm = (Fun undefined [])"
  have ground_trm: "is_ground_atm some_ground_trm"
    unfolding is_ground_atm_def some_ground_trm_def by auto
  define \<tau> where "\<tau> = (\<lambda>v. if v \<in> vars_clause C then \<sigma> v else some_ground_trm)"
  then have \<tau>_\<sigma>: "\<forall>v \<in> vars_clause C. \<sigma> v = \<tau> v"
    unfolding \<tau>_def by auto

  have all_ground_\<tau>: "is_ground_atm (\<tau> v)" for v
  proof (cases "v \<in> vars_clause C")
    case True
    then show ?thesis
      using ground_atms_\<sigma> \<tau>_\<sigma> by auto
  next
    case False
    then show ?thesis
      unfolding \<tau>_def using ground_trm by auto
  qed
  have "is_ground_subst \<tau>"
    unfolding is_ground_subst_def
  proof
    fix A
    show "is_ground_atm (subst_atm_abbrev A \<tau>)"
    proof (induction A)
      case (Var v)
      then show ?case using all_ground_\<tau> by auto
    next
      case (Fun f As)
      then show ?case using all_ground_\<tau>
        by (simp add: is_ground_atm_def)
    qed
  qed
  moreover have "\<forall>v \<in> vars_clause C. \<sigma> v = \<tau> v"
    using \<tau>_\<sigma> unfolding vars_clause_list_def
    by blast
  then have "subst_cls C \<sigma> = subst_cls C \<tau>"
    using same_on_vars_clause by auto
  ultimately show "\<exists>\<tau>. is_ground_subst \<tau> \<and> subst_cls C \<tau> = subst_cls C \<sigma>"
    by auto
next
  show "wfP (strictly_generalizes_atm :: ('f, 'v) term \<Rightarrow> _ \<Rightarrow> _)"
    unfolding wfp_def
    by (rule wf_subset[OF wf_subsumes])
      (auto simp: strictly_generalizes_atm_def generalizes_atm_def term_subsumable.subsumes_def
        subsumeseq_term.simps)
qed

lemma vars_partitioned_var_disjoint:
  assumes "vars_partitioned Cs"
  shows "var_disjoint Cs"
  unfolding var_disjoint_def
proof (intro allI impI)
  fix \<sigma>s :: \<open>('b \<Rightarrow> ('a, 'b) term) list\<close>
  assume "length \<sigma>s = length Cs"
  with assms[unfolded vars_partitioned_def] Fun_More.fun_merge[of "map vars_clause Cs" "nth \<sigma>s"]
  obtain \<sigma> where
    \<sigma>_p: "\<forall>i < length (map vars_clause Cs). \<forall>x \<in> map vars_clause Cs ! i. \<sigma> x = (\<sigma>s ! i) x"
    by auto
  have "\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> subst_cls S (\<sigma>s ! i) = subst_cls S \<sigma>"
  proof (rule, rule, rule, rule)
    fix i :: nat and S :: "('a, 'b) term literal multiset"
    assume
      "i < length Cs" and
      "S \<subseteq># Cs ! i"
    then have "\<forall>v \<in> vars_clause S. (\<sigma>s ! i) v = \<sigma> v"
      using vars_clause_mono[of S "Cs ! i"] \<sigma>_p by auto
    then show "subst_cls S (\<sigma>s ! i) = subst_cls S \<sigma>"
      using same_on_vars_clause by auto
  qed
  then show "\<exists>\<tau>. \<forall>i<length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> subst_cls S (\<sigma>s ! i) = subst_cls S \<tau>"
    by auto
qed

lemma vars_in_instance_in_range_term:
  "vars_term (subst_atm_abbrev A \<sigma>) \<subseteq> Union (image vars_term (range \<sigma>))"
  by (induction A) auto

lemma vars_in_instance_in_range_lit: "vars_lit (subst_lit L \<sigma>) \<subseteq> Union (image vars_term (range \<sigma>))"
proof (induction L)
  case (Pos A)
  have "vars_term (A \<cdot> \<sigma>) \<subseteq> Union (image vars_term (range \<sigma>))"
    using vars_in_instance_in_range_term[of A \<sigma>] by blast
  then show ?case by auto
next
  case (Neg A)
  have "vars_term (A \<cdot> \<sigma>) \<subseteq> Union (image vars_term (range \<sigma>))"
    using vars_in_instance_in_range_term[of A \<sigma>] by blast
  then show ?case by auto
qed

lemma vars_in_instance_in_range_cls:
  "vars_clause (subst_cls C \<sigma>) \<subseteq> Union (image vars_term (range \<sigma>))"
  unfolding vars_clause_def subst_cls_def using vars_in_instance_in_range_lit[of _ \<sigma>] by auto

primrec renamings_apart :: "('f, nat) term clause list \<Rightarrow> (('f, nat) subst) list" where
  "renamings_apart [] = []"
| "renamings_apart (C # Cs) =
   (let \<sigma>s = renamings_apart Cs in
      (\<lambda>v. Var (v + Max (vars_clause_list (subst_cls_lists Cs \<sigma>s) \<union> {0}) + 1)) # \<sigma>s)"

definition var_map_of_subst :: "('f, nat) subst \<Rightarrow> nat \<Rightarrow> nat" where
  "var_map_of_subst \<sigma> v = the_Var (\<sigma> v)"

lemma len_renamings_apart: "length (renamings_apart Cs) = length Cs"
  by (induction Cs) (auto simp: Let_def)

lemma renamings_apart_is_Var: "\<forall>\<sigma> \<in> set (renamings_apart Cs). \<forall>x. is_Var (\<sigma> x)"
  by (induction Cs) (auto simp: Let_def)

lemma renamings_apart_inj: "\<forall>\<sigma> \<in> set (renamings_apart Cs). inj \<sigma>"
proof (induction Cs)
  case (Cons a Cs)
  then have "inj (\<lambda>v. Var (Suc (v + Max (vars_clause_list
               (subst_cls_lists Cs (renamings_apart Cs)) \<union> {0}))))"
    by (meson add_right_imp_eq injI nat.inject term.inject(1))
  then show ?case
    using Cons by (auto simp: Let_def)
qed auto

lemma finite_vars_clause[simp]: "finite (vars_clause x)"
  unfolding vars_clause_def by auto

lemma finite_vars_clause_list[simp]: "finite (vars_clause_list Cs)"
  unfolding vars_clause_list_def by (induction Cs) auto

lemma Suc_Max_notin_set: "finite X \<Longrightarrow> Suc (v + Max (insert 0 X)) \<notin> X"
  by (metis Max.boundedE Suc_n_not_le_n empty_iff finite.insertI le_add2 vimageE vimageI
      vimage_Suc_insert_0)

lemma vars_partitioned_Nil[simp]: "vars_partitioned []"
  unfolding vars_partitioned_def by auto

lemma subst_cls_lists_Nil[simp]: "subst_cls_lists Cs [] = []"
  unfolding subst_cls_lists_def by auto

lemma vars_clause_hd_partitioned_from_tl:
  assumes "Cs \<noteq>[]"
  shows "vars_clause (hd (subst_cls_lists Cs (renamings_apart Cs)))
    \<inter> vars_clause_list (tl (subst_cls_lists Cs (renamings_apart Cs))) = {}"
  using assms
proof (induction Cs)
  case (Cons C Cs)
  define \<sigma>' :: "nat \<Rightarrow> nat"
    where "\<sigma>' = (\<lambda>v. (Suc (v + Max ((vars_clause_list (subst_cls_lists Cs
                        (renamings_apart Cs))) \<union> {0}))))"
  define \<sigma> :: "nat \<Rightarrow> ('a, nat) term"
    where "\<sigma> = (\<lambda>v. Var (\<sigma>' v))"

  have "vars_clause (subst_cls C \<sigma>) \<subseteq> \<Union> (vars_term ` range \<sigma>)"
    using vars_in_instance_in_range_cls[of C "hd (renamings_apart (C # Cs))"] \<sigma>_def \<sigma>'_def
    by (auto simp: Let_def)
  moreover have "\<Union> (vars_term ` range \<sigma>)
    \<inter> vars_clause_list (subst_cls_lists Cs (renamings_apart Cs)) = {}"
  proof -
    have "range \<sigma>' \<inter> vars_clause_list (subst_cls_lists Cs (renamings_apart Cs)) = {}"
      unfolding \<sigma>'_def using Suc_Max_notin_set by auto
    then show ?thesis
      unfolding \<sigma>_def \<sigma>'_def by auto
  qed
  ultimately have "vars_clause (subst_cls C \<sigma>)
     \<inter> vars_clause_list (subst_cls_lists Cs (renamings_apart Cs)) = {}"
    by auto
  then show ?case
    unfolding \<sigma>_def \<sigma>'_def unfolding subst_cls_lists_def
    by (simp add: Let_def subst_cls_lists_def)
qed auto

lemma vars_partitioned_renamings_apart: "vars_partitioned (subst_cls_lists Cs (renamings_apart Cs))"
proof (induction Cs)
  case (Cons C Cs)
  {
    fix i :: nat and j :: nat
    assume ij:
      "i < Suc (length Cs)"
      "j < i"
    have "vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! i) \<inter>
        vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! j) =
        {}"
    proof (cases i; cases j)
      fix j' :: nat
      assume i'j':
        "i = 0"
        "j = Suc j'"
      then show "vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! i) \<inter>
        vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! j) =
        {}"
        using ij by auto
    next
      fix i' :: nat
      assume i'j':
        "i = Suc i'"
        "j = 0"
      have disjoin_C_Cs: "vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! 0) \<inter>
        vars_clause_list ((subst_cls_lists Cs (renamings_apart Cs))) = {}"
        using vars_clause_hd_partitioned_from_tl[of "C # Cs"]
        by (simp add: Let_def subst_cls_lists_def)
      {
        fix x
        assume asm: "x \<in> vars_clause (subst_cls_lists Cs (renamings_apart Cs) ! i')"
        then have "(subst_cls_lists Cs (renamings_apart Cs) ! i')
          \<in> set (subst_cls_lists Cs (renamings_apart Cs))"
          using i'j' ij unfolding subst_cls_lists_def
          by (metis Suc_less_SucD length_map len_renamings_apart length_zip min_less_iff_conj
              nth_mem)
        moreover from asm have
          "x \<in> vars_clause (subst_cls_lists Cs (renamings_apart Cs) ! i')"
          using i'j' ij
          unfolding subst_cls_lists_def by simp
        ultimately have "\<exists>D \<in> set (subst_cls_lists Cs (renamings_apart Cs)). x \<in> vars_clause D"
            by auto
      }
      then have "vars_clause (subst_cls_lists Cs (renamings_apart Cs) ! i')
        \<subseteq> Union (set (map vars_clause ((subst_cls_lists Cs (renamings_apart Cs)))))"
        by auto
      then have "vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! 0) \<inter>
        vars_clause (subst_cls_lists Cs (renamings_apart Cs) ! i') =
        {}" using disjoin_C_Cs unfolding vars_clause_list_def by auto
      moreover
      have "subst_cls_lists Cs (renamings_apart Cs) ! i' =
        subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! i"
        using i'j' ij unfolding subst_cls_lists_def by (simp add: Let_def)
      ultimately
      show "vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! i) \<inter>
        vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! j) =
        {}"
        using i'j' by (simp add: Int_commute)
    next
      fix i' :: nat and j' :: nat
      assume i'j':
        "i = Suc i'"
        "j = Suc j'"
      have "i'<length (subst_cls_lists Cs (renamings_apart Cs))"
        using ij i'j' unfolding subst_cls_lists_def by (auto simp: len_renamings_apart)
      moreover
      have "j'<length (subst_cls_lists Cs (renamings_apart Cs))"
        using ij i'j' unfolding subst_cls_lists_def by (auto simp: len_renamings_apart)
      moreover
      have "i' \<noteq> j'"
        using \<open>i = Suc i'\<close> \<open>j = Suc j'\<close> ij by blast
      ultimately
      have "vars_clause (subst_cls_lists Cs (renamings_apart Cs) ! i') \<inter>
          vars_clause (subst_cls_lists Cs (renamings_apart Cs) ! j') =
          {}"
        using Cons unfolding vars_partitioned_def by auto
      then show "vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! i) \<inter>
        vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! j) =
        {}"
        unfolding i'j'
        by (simp add: subst_cls_lists_def Let_def)
    next
      assume
        \<open>i = 0\<close> and
        \<open>j = 0\<close>
      then show \<open>vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! i) \<inter>
        vars_clause (subst_cls_lists (C # Cs) (renamings_apart (C # Cs)) ! j) =
        {}\<close> using ij by auto
    qed
  }
  then show ?case
    unfolding vars_partitioned_def
    by (metis (no_types, lifting) Int_commute Suc_lessI len_renamings_apart length_map
        length_nth_simps(2) length_zip min.idem nat.inject not_less_eq subst_cls_lists_def)
qed auto

interpretation substitution_renamings "(\<cdot>)" "Var :: _ \<Rightarrow> ('f, nat) term" "(\<circ>\<^sub>s)" renamings_apart "Fun undefined"
proof unfold_locales
  fix Cs :: "('f, nat) term clause list"
  show "length (renamings_apart Cs) = length Cs"
    using len_renamings_apart by auto
next
  fix Cs :: "('f, nat) term clause list"
  fix \<rho> ::  "nat \<Rightarrow> ('f, nat) Term.term"
  assume \<rho>_renaming: "\<rho> \<in> set (renamings_apart Cs)"
  {
    have inj_is_renaming:
      "\<And>\<sigma> :: ('f, nat) subst. (\<And>x. is_Var (\<sigma> x)) \<Longrightarrow> inj \<sigma> \<Longrightarrow> is_renaming \<sigma>"
    proof -
      fix \<sigma> :: "('f, nat) subst"
      fix x
      assume is_var_\<sigma>: "\<And>x. is_Var (\<sigma> x)"
      assume inj_\<sigma>: "inj \<sigma>"
      define \<sigma>' where "\<sigma>' = var_map_of_subst \<sigma>"
      have \<sigma>: "\<sigma> = Var \<circ> \<sigma>'"
        unfolding \<sigma>'_def var_map_of_subst_def using is_var_\<sigma> by auto

      from is_var_\<sigma> inj_\<sigma> have "inj \<sigma>'"
        unfolding is_renaming_def unfolding subst_domain_def inj_on_def \<sigma>'_def var_map_of_subst_def
         by (metis term.collapse(1))
      then have "inv \<sigma>' \<circ> \<sigma>' = id"
        using inv_o_cancel[of \<sigma>'] by simp
      then have "Var \<circ> (inv \<sigma>' \<circ> \<sigma>') = Var"
        by simp
      then have "\<forall>x. (Var \<circ> (inv \<sigma>' \<circ> \<sigma>')) x = Var x"
        by metis
      then have "\<forall>x. ((Var \<circ> \<sigma>') \<circ>\<^sub>s (Var \<circ> (inv \<sigma>'))) x = Var x"
        unfolding subst_compose_def by auto
      then have "\<sigma> \<circ>\<^sub>s (Var \<circ> (inv \<sigma>')) = Var"
        using \<sigma> by auto
      then show "is_renaming \<sigma>"
        unfolding is_renaming_def by blast
    qed
    then have "\<forall>\<sigma> \<in> (set (renamings_apart Cs)). is_renaming \<sigma>"
      using renamings_apart_is_Var renamings_apart_inj by blast
  }
  then show "is_renaming \<rho>"
    using \<rho>_renaming by auto
next
  fix Cs :: "('f, nat) term clause list"
  have "vars_partitioned (subst_cls_lists Cs (renamings_apart Cs))"
    using vars_partitioned_renamings_apart by auto
  then show "var_disjoint (subst_cls_lists Cs (renamings_apart Cs))"
    using vars_partitioned_var_disjoint by auto
next
  show "\<And>\<sigma> As Bs. Fun undefined As \<cdot> \<sigma> = Fun undefined Bs \<longleftrightarrow> map (\<lambda>A. A \<cdot> \<sigma>) As = Bs"
    by simp
qed

fun pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "pairs (x # y # xs) = (x, y) # pairs (y # xs)" |
  "pairs _ = []"

derive compare "term"
derive compare "literal"

lemma class_linorder_compare: "class.linorder (le_of_comp compare) (lt_of_comp compare)"
  apply standard
      apply (simp_all add: lt_of_comp_def le_of_comp_def split: order.splits)
     apply (metis comparator.sym comparator_compare invert_order.simps(1) order.distinct(5))
    apply (metis comparator_compare comparator_def order.distinct(5))
   apply (metis comparator.sym comparator_compare invert_order.simps(1) order.distinct(5))
  by (metis comparator.sym comparator_compare invert_order.simps(2) order.distinct(5))

context begin
interpretation compare_linorder: linorder
  "le_of_comp compare"
  "lt_of_comp compare"
  by (rule class_linorder_compare)

definition Pairs where
  "Pairs AAA = concat (compare_linorder.sorted_list_of_set
     ((pairs \<circ> compare_linorder.sorted_list_of_set) ` AAA))"

lemma unifies_all_pairs_iff:
  "(\<forall>p \<in> set (pairs xs). fst p \<cdot> \<sigma> = snd p \<cdot> \<sigma>) \<longleftrightarrow> (\<forall>a \<in> set xs. \<forall>b \<in> set xs. a \<cdot> \<sigma> = b \<cdot> \<sigma>)"
proof (induct xs rule: pairs.induct)
  case (1 x y xs)
  then show ?case
    unfolding pairs.simps list.set ball_Un ball_simps simp_thms fst_conv snd_conv by metis
qed simp_all

lemma in_pair_in_set:
  assumes "(A,B) \<in> set ((pairs As))"
  shows "A \<in> set As \<and> B \<in> set As"
  using assms
proof (induction As)
  case (Cons A As)
  note Cons_outer = this
  show ?case
  proof (cases As)
    case Nil
    then show ?thesis
      using Cons_outer by auto
  next
    case (Cons B As')
    then show ?thesis using Cons_outer by auto
  qed
qed auto

lemma in_pairs_sorted_list_of_set_in_set:
  assumes
    "finite AAA"
    "\<forall>AA \<in> AAA. finite AA"
    "AB_pairs \<in> (pairs \<circ> compare_linorder.sorted_list_of_set) ` AAA" and
    "(A :: _ :: compare, B) \<in> set AB_pairs"
  shows "\<exists>AA. AA \<in> AAA \<and> A \<in> AA \<and> B \<in> AA"
proof -
  from assms have "AB_pairs \<in> (pairs \<circ> compare_linorder.sorted_list_of_set) ` AAA"
    by auto
  then obtain AA where
    AA_p: "AA \<in> AAA \<and> (pairs \<circ> compare_linorder.sorted_list_of_set) AA = AB_pairs"
    by auto
  have "(A, B) \<in> set (pairs (compare_linorder.sorted_list_of_set AA))"
    using AA_p[] assms(4) by auto
  then have "A \<in> set (compare_linorder.sorted_list_of_set AA)" and
    "B \<in> set (compare_linorder.sorted_list_of_set AA)"
    using in_pair_in_set[of A] by auto
  then show ?thesis
    using assms(2) AA_p by auto
qed

lemma unifiers_Pairs:
  assumes
    "finite AAA" and
    "\<forall>AA \<in> AAA. finite AA"
  shows "unifiers (set (Pairs AAA)) = {\<sigma>. is_unifiers \<sigma> AAA}"
proof (rule; rule)
  fix \<sigma> :: "('a, 'b) subst"
  assume asm: "\<sigma> \<in> unifiers (set (Pairs AAA))"
  have "\<And>AA. AA \<in> AAA \<Longrightarrow> card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<le> Suc 0"
  proof -
    fix AA :: "('a, 'b) term set"
    assume asm': "AA \<in> AAA"
    then have "\<forall>p \<in> set (pairs (compare_linorder.sorted_list_of_set AA)).
      subst_atm_abbrev (fst p) \<sigma> = subst_atm_abbrev (snd p) \<sigma>"
      using assms asm unfolding Pairs_def by auto
    then have "\<forall>A \<in> AA. \<forall>B \<in> AA. subst_atm_abbrev A \<sigma> = subst_atm_abbrev B \<sigma>"
      using assms asm' unfolding unifies_all_pairs_iff
      using compare_linorder.sorted_list_of_set by blast
    then show "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<le> Suc 0"
      by (smt imageE card.empty card_Suc_eq card_mono finite.intros(1) finite_insert le_SucI
           singletonI subsetI)
  qed
  then show "\<sigma> \<in> {\<sigma>. is_unifiers \<sigma> AAA}"
    using assms by (auto simp: is_unifiers_def is_unifier_def subst_atms_def)
next
  fix \<sigma> :: "('a, 'b) subst"
  assume asm: "\<sigma> \<in> {\<sigma>. is_unifiers \<sigma> AAA}"

  {
    fix AB_pairs A B
    assume
      "AB_pairs \<in> set (compare_linorder.sorted_list_of_set
         ((pairs \<circ> compare_linorder.sorted_list_of_set) ` AAA))" and
      "(A, B) \<in> set AB_pairs"
    then have "\<exists>AA. AA \<in> AAA \<and> A \<in> AA \<and> B \<in> AA"
      using assms by (simp add: in_pairs_sorted_list_of_set_in_set)
    then obtain AA where
     a: "AA \<in> AAA" "A \<in> AA" "B \<in> AA"
      by blast
    from a assms asm have card_AA_\<sigma>: "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) \<le> Suc 0"
      unfolding is_unifiers_def is_unifier_def subst_atms_def by auto
    have "subst_atm_abbrev A \<sigma> = subst_atm_abbrev B \<sigma>"
    proof (cases "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) = Suc 0")
      case True
      moreover
      have "subst_atm_abbrev A \<sigma> \<in> AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
        using a assms asm card_AA_\<sigma> by auto
      moreover
      have "subst_atm_abbrev B \<sigma> \<in> AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>"
        using a assms asm card_AA_\<sigma> by auto
      ultimately
      show ?thesis
        using a assms asm card_AA_\<sigma> by (metis (no_types, lifting) card_Suc_eq singletonD)
    next
      case False
      then have "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>) = 0"
        using a assms asm card_AA_\<sigma>
        by arith
      then show ?thesis
        using a assms asm card_AA_\<sigma> by auto
    qed
  }
  then show "\<sigma> \<in> unifiers (set (Pairs AAA))"
    unfolding Pairs_def unifiers_def by auto
qed

end

definition "mgu_sets AAA = map_option subst_of (unify (Pairs AAA) [])"

lemma mgu_sets_is_imgu:
  fixes AAA :: "('a :: compare, nat) term set set" and \<sigma> :: "('a, nat) subst"
  assumes fin: "finite AAA" "\<forall>AA \<in> AAA. finite AA" and "mgu_sets AAA = Some \<sigma>"
  shows "is_imgu \<sigma> AAA"
proof -
  have "Unifiers.is_imgu \<sigma> (set (Pairs AAA))"
    using assms unify_sound unfolding mgu_sets_def by blast
  thus ?thesis
    unfolding Unifiers.is_imgu_def is_imgu_def unifiers_Pairs[OF fin]
    by simp
qed

interpretation mgu "(\<cdot>)" "Var :: _ \<Rightarrow> ('f :: compare, nat) term" "(\<circ>\<^sub>s)" renamings_apart
  "Fun undefined" mgu_sets
proof unfold_locales
  fix AAA :: "('a :: compare, nat) term set set" and \<sigma> :: "('a, nat) subst"
  assume fin: "finite AAA" "\<forall>AA \<in> AAA. finite AA" and "mgu_sets AAA = Some \<sigma>"
  thus "is_mgu \<sigma> AAA"
    using mgu_sets_is_imgu by auto
next
  fix AAA :: "('a :: compare, nat) term set set" and \<sigma> :: "('a, nat) subst"
  assume fin: "finite AAA" "\<forall>AA \<in> AAA. finite AA" and "is_unifiers \<sigma> AAA"
  then have "\<sigma> \<in> unifiers (set (Pairs AAA))"
    unfolding is_mgu_def unifiers_Pairs[OF fin] by auto
  then show "\<exists>\<tau>. mgu_sets AAA = Some \<tau>"
    using unify_complete unfolding mgu_sets_def by blast
qed

interpretation imgu "(\<cdot>)" "Var :: _ \<Rightarrow> ('f :: compare, nat) term" "(\<circ>\<^sub>s)" renamings_apart
  "Fun undefined" mgu_sets
proof unfold_locales
  fix AAA :: "('a :: compare, nat) term set set" and \<sigma> :: "('a, nat) subst"
  assume fin: "finite AAA" "\<forall>AA \<in> AAA. finite AA" and "mgu_sets AAA = Some \<sigma>"
  thus "is_imgu \<sigma> AAA"
    by (rule mgu_sets_is_imgu)
qed

derive linorder prod
derive linorder list

text \<open>
This part extends and integrates and the Knuth--Bendix order defined in
\textsf{IsaFoR}.
\<close>

record 'f weights =
  w :: "'f \<times> nat \<Rightarrow> nat"
  w0 :: nat
  pr_strict :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
  least :: "'f \<Rightarrow> bool"
  scf :: "'f \<times> nat \<Rightarrow> nat \<Rightarrow> nat"

class weighted =
  fixes weights :: "'a weights"
  assumes weights_adm:
    "admissible_kbo
       (w weights) (w0 weights) (pr_strict weights) ((pr_strict weights)\<^sup>=\<^sup>=) (least weights) (scf weights)"
  and pr_strict_total: "fi = gj \<or> pr_strict weights fi gj \<or> pr_strict weights gj fi"
  and pr_strict_asymp: "asymp (pr_strict weights)"
  and scf_ok: "i < n \<Longrightarrow> scf weights (f, n) i \<le> 1"

instantiation unit :: weighted begin

definition weights_unit :: "unit weights" where "weights_unit =
  \<lparr>w = Suc \<circ> snd, w0 = 1, pr_strict = \<lambda>(_, n) (_, m). n > m, least = \<lambda>_. True, scf = \<lambda>_ _. 1\<rparr>"

instance
  by (intro_classes, unfold_locales) (auto simp: weights_unit_def SN_iff_wf irreflp_def
      intro: asympI intro!: wf_subset[OF wf_inv_image[OF wf], of _ snd])
end

global_interpretation KBO:
  admissible_kbo
    "w (weights :: 'f :: weighted weights)" "w0 (weights :: 'f :: weighted weights)"
    "pr_strict weights" "((pr_strict weights)\<^sup>=\<^sup>=)" "least weights" "scf weights"
    defines weight = KBO.weight
    and kbo = KBO.kbo
  by (simp add: weights_adm)

lemma kbo_code[code]: "kbo s t =
  (let wt = weight t; ws = weight s in
  if vars_term_ms (KBO.SCF t) \<subseteq># vars_term_ms (KBO.SCF s) \<and> wt \<le> ws
  then
    (if wt < ws then (True, True)
    else
      (case s of
        Var y \<Rightarrow> (False, case t of Var x \<Rightarrow> True | Fun g ts \<Rightarrow> ts = [] \<and> least weights g)
      | Fun f ss \<Rightarrow>
          (case t of
            Var x \<Rightarrow> (True, True)
          | Fun g ts \<Rightarrow>
              if pr_strict weights (f, length ss) (g, length ts) then (True, True)
              else if (f, length ss) = (g, length ts) then lex_ext_unbounded kbo ss ts
              else (False, False))))
  else (False, False))"
  by (subst KBO.kbo.simps) (auto simp: Let_def split: term.splits)

definition "less_kbo s t = fst (kbo t s)"

lemma less_kbo_gtotal: "ground s \<Longrightarrow> ground t \<Longrightarrow> s = t \<or> less_kbo s t \<or> less_kbo t s"
  unfolding less_kbo_def using KBO.S_ground_total by (metis pr_strict_total subset_UNIV)

lemma less_kbo_subst:
  fixes \<sigma> :: "('f :: weighted, 'v) subst"
  shows "less_kbo s t \<Longrightarrow> less_kbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  unfolding less_kbo_def by (rule KBO.S_subst)

lemma wfP_less_kbo: "wfP less_kbo"
proof -
  have "SN {(x, y). fst (kbo x y)}"
    using pr_strict_asymp by (fastforce simp: asympI irreflp_def intro!: KBO.S_SN scf_ok)
  then show ?thesis
    unfolding SN_iff_wf wfp_def by (rule wf_subset) (auto simp: less_kbo_def)
qed

instantiation "term" :: (weighted, type) linorder begin

definition "leq_term = (SOME leq. {(s,t). less_kbo s t} \<subseteq> leq \<and> Well_order leq \<and> Field leq = UNIV)"

lemma less_trm_extension: "{(s,t). less_kbo s t} \<subseteq> leq_term"
  unfolding leq_term_def
  by (rule someI2_ex[OF total_well_order_extension[OF wfP_less_kbo[unfolded wfp_def]]]) auto

lemma less_trm_well_order: "well_order leq_term"
  unfolding leq_term_def
  by (rule someI2_ex[OF total_well_order_extension[OF wfP_less_kbo[unfolded wfp_def]]]) auto

definition less_eq_term :: "('a :: weighted, 'b) term \<Rightarrow> _ \<Rightarrow> bool" where
  "less_eq_term = in_rel leq_term"
definition less_term :: "('a :: weighted, 'b) term \<Rightarrow> _ \<Rightarrow> bool" where
  "less_term s t = strict (\<le>) s t"

lemma leq_term_minus_Id: "leq_term - Id = {(x,y). x < y}"
  using less_trm_well_order
  unfolding well_order_on_def linear_order_on_def partial_order_on_def antisym_def less_term_def less_eq_term_def
  by auto

lemma less_term_alt: "(<) = in_rel (leq_term - Id)"
  by (simp add: in_rel_Collect_case_prod_eq leq_term_minus_Id)

instance
proof (standard, goal_cases less_less_eq refl trans antisym total)
  case (less_less_eq x y)
  then show ?case unfolding less_term_def ..
next
case (refl x)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      less_eq_term_def by auto
next
case (trans x y z)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def trans_def
      less_eq_term_def by auto
next
  case (antisym x y)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def antisym_def
      less_eq_term_def by auto
next
  case (total x y)
  then show ?case using less_trm_well_order
    unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
      Relation.total_on_def less_eq_term_def by (cases "x = y") auto
qed

end

instantiation "term" :: (weighted, type) wellorder begin
instance
  using less_trm_well_order[unfolded well_order_on_def wf_def leq_term_minus_Id, THEN conjunct2]
  by intro_classes (atomize, auto)
end

lemma ground_less_less_kbo: "ground s \<Longrightarrow> ground t \<Longrightarrow> s < t \<Longrightarrow> less_kbo s t"
  using less_kbo_gtotal[of s t] less_trm_extension
  by (auto simp: less_term_def less_eq_term_def)

lemma less_kbo_less: "less_kbo s t \<Longrightarrow> s < t"
  using less_trm_extension
  by (auto simp: less_term_alt less_kbo_def KBO.S_irrefl)

lemma is_ground_atm_ground: "is_ground_atm t \<longleftrightarrow> ground t"
  unfolding is_ground_atm_def
  by (induct t) (fastforce simp: in_set_conv_nth list_eq_iff_nth_eq)+

end
