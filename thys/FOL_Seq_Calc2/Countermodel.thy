section \<open>Countermodels from Hintikka sets\<close>

theory Countermodel
  imports Hintikka Usemantics ProverLemmas
begin

text \<open>In this theory, we will construct a countermodel in the bounded semantics from a Hintikka
  set. This will allow us to prove completeness of the prover.\<close>

text \<open>A predicate is satisfied in the model based on a set of formulas S when its negation is in S.\<close>
abbreviation (input)
  \<open>G S n ts \<equiv> Neg (Pre n ts) \<in> S\<close>

text \<open>Alternate interpretation for environments: if a variable is not present, we interpret it as
  some existing term.\<close>
abbreviation
  \<open>E S n \<equiv> if Var n \<in> terms S then Var n else SOME t. t \<in> terms S\<close>

text \<open>Alternate interpretation for functions: if a function application is not present, we interpret
  it as some existing term.\<close>
abbreviation
  \<open>F S i l \<equiv> if Fun i l \<in> terms S then Fun i l else SOME t. t \<in> terms S\<close>

text \<open>The terms function never returns the empty set (because it will add \<open>Fun 0 []\<close> if that is the
  case).\<close>
lemma terms_ne [simp]: \<open>terms S \<noteq> {}\<close>
  unfolding terms_def by simp

text \<open>If a term is in the set of terms, it is either the default term or a subterm of some formula
  in the set.\<close>
lemma terms_cases: \<open>t \<in> terms S \<Longrightarrow> t = Fun 0 [] \<or> (\<exists>p \<in> S. t \<in> set (subtermFm p))\<close>
  unfolding terms_def by (simp split: if_splits)

text \<open>The set of terms is downwards closed under the subterm function.\<close>
lemma terms_downwards_closed: \<open>t \<in> terms S \<Longrightarrow> set (subtermTm t) \<subseteq> terms S\<close>
proof (induct t)
  case (Fun n ts)
  moreover have \<open>\<forall>t \<in> set ts. t \<in> set ts\<close>
    by simp
  moreover have \<open>\<forall>t \<in> set ts. t \<in> terms S\<close>
  proof
    fix t
    assume *: \<open>t \<in> set ts\<close>
    then show \<open>t \<in> terms S\<close>
    proof (cases \<open>terms S = {Fun 0 []}\<close>)
      case True
      then show ?thesis
        using Fun * by simp
    next
      case False
      moreover obtain p where p: \<open>p \<in> S\<close> \<open>Fun n ts \<in> set (subtermFm p)\<close>
        using Fun(2) terms_cases * by fastforce
      then have \<open>set ts \<subseteq> set (subtermFm p)\<close>
        using fun_arguments_subterm by blast
      ultimately show \<open>t \<in> terms S\<close>
        unfolding terms_def using * p(1) by (metis UN_iff in_mono)
    qed
  qed
  ultimately have \<open>\<forall>t \<in> set ts. set (subtermTm t) \<subseteq> terms S\<close>
    using Fun by meson
  moreover note \<open>Fun n ts \<in> terms S\<close>
  ultimately show ?case
    by auto
next
  case (Var x)
  then show ?case
    by simp
qed

text \<open>If terms are actually in a set of formulas, interpreting the environment over these formulas
allows for a Herbrand interpretation.\<close>
lemma usemantics_E:
    \<open>t \<in> terms S \<Longrightarrow> semantics_term (E S) (F S) t = t\<close>
    \<open>list_all (\<lambda>t. t \<in> terms S) ts \<Longrightarrow> semantics_list (E S) (F S) ts = ts\<close>
proof (induct t and ts arbitrary: ts rule: semantics_term.induct semantics_list.induct)
  case (Fun i ts')
  moreover have \<open>\<forall>t' \<in> set ts'. t' \<in> set (subtermTm (Fun i ts'))\<close>
    using subterm_Fun_refl by blast
  ultimately have \<open>list_all (\<lambda>t. t \<in> terms S) ts'\<close>
    using terms_downwards_closed unfolding list_all_def by (metis (no_types, lifting) subsetD)
  then show ?case
    using Fun by simp
qed simp_all

text \<open>Our alternate interpretation of environments is well-formed for the terms function.\<close>
lemma is_env_E:
  \<open>is_env (terms S) (E S)\<close>
  unfolding is_env_def
proof
  fix n
  show \<open>E S n \<in> terms S\<close>
    by (cases \<open>Var n \<in> terms S\<close>) (simp_all add: some_in_eq)
qed

text \<open>Our alternate function interpretation is well-formed for the terms function.\<close>
lemma is_fdenot_F:
  \<open>is_fdenot (terms S) (F S)\<close>
  unfolding is_fdenot_def
proof (intro allI impI)
  fix i l
  assume \<open>list_all (\<lambda>x. x \<in> terms S) l\<close>
  then show \<open>F S i l \<in> terms S\<close>
    by (cases \<open>\<forall>n. Var n \<in> terms S\<close>) (simp_all add: some_in_eq)
qed

abbreviation
  \<open>M S \<equiv> usemantics (terms S) (E S) (F S) (G S)\<close>

text \<open>If S is a Hintikka set, then we can construct a countermodel for any formula using our
  bounded semantics and a Herbrand interpretation.\<close>
theorem Hintikka_counter_model:
  assumes \<open>Hintikka S\<close>
  shows \<open>(p \<in> S \<longrightarrow> \<not> M S p) \<and> (Neg p \<in> S \<longrightarrow> M S p)\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size\<close>])
  case 1
  then show ?case ..
next
  fix x
  assume wf: \<open>\<forall>q. (q, x) \<in> measure size \<longrightarrow>
    (q \<in> S \<longrightarrow> \<not> M S q) \<and> (Neg q \<in> S \<longrightarrow> M S q)\<close>
  show \<open>(x \<in> S \<longrightarrow> \<not> M S x) \<and> (Neg x \<in> S \<longrightarrow> M S x)\<close>
  proof (cases x)
    case (Pre n ts)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg (Pre n ts) \<notin> S\<close>
        using assms Pre Hintikka.Basic by blast
      moreover have \<open>list_all (\<lambda>t. t \<in> terms S) ts\<close>
        using \<open>x \<in> S\<close> Pre subterm_Pre_refl unfolding terms_def list_all_def by force
      ultimately show \<open>\<not> M S x\<close>
        using Pre usemantics_E
        by (metis (no_types, lifting) usemantics.simps(1))
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>G S n ts\<close>
        using assms Pre Hintikka.Basic by blast
      moreover have \<open>list_all (\<lambda>t. t \<in> terms S) ts\<close>
        using \<open>Neg x \<in> S\<close> Pre subterm_Pre_refl unfolding terms_def list_all_def by force
      ultimately show \<open>M S x\<close>
        using Pre usemantics_E
        by (metis (no_types, lifting) usemantics.simps(1))
    qed
  next
    case (Imp p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>q \<in> S\<close>
        using Imp assms Hintikka.AlphaImp by blast+
      then show \<open>\<not> M S x\<close>
        using wf Imp by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S \<or> Neg q \<in> S\<close>
        using Imp assms Hintikka.BetaImp by blast
      then show \<open>M S x\<close>
        using wf Imp by fastforce
    qed
  next
    case (Dis p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S\<close> \<open>q \<in> S\<close>
        using Dis assms Hintikka.AlphaDis by blast+
      then show \<open>\<not> M S x\<close>
        using wf Dis by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S \<or> Neg q \<in> S\<close>
        using Dis assms Hintikka.BetaDis by blast
      then show \<open>M S x\<close>
        using wf Dis by fastforce
    qed
  next
    case (Con p q)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>p \<in> S \<or> q \<in> S\<close>
        using Con assms Hintikka.BetaCon by blast
      then show \<open>\<not> M S x\<close>
        using wf Con by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>Neg p \<in> S\<close> \<open>Neg q \<in> S\<close>
        using Con assms Hintikka.AlphaCon by blast+
      then show \<open>M S x\<close>
        using wf Con by fastforce
    qed
  next
    case (Exi p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then have \<open>\<forall>t \<in> terms S. sub 0 t p \<in> S\<close>
        using Exi assms Hintikka.GammaExi by blast
      then have \<open>\<forall>t \<in> terms S. \<not> M S (sub 0 t p)\<close>
        using wf Exi size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(12) in_measure lessI)
      moreover have \<open>\<forall>t \<in> terms S. semantics_term (E S) (F S) t = t\<close>
        using usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
      ultimately have \<open>\<forall>t \<in> terms S. \<not> usemantics (terms S) (SeCaV.shift (E S) 0 t) (F S) (G S) p\<close>
        by simp
      then show \<open>\<not> M S x\<close>
        using Exi by simp
    next
      assume \<open>Neg x \<in> S\<close>
      then obtain t where \<open>t \<in> terms S\<close> \<open>Neg (sub 0 t p) \<in> S\<close>
        using Exi assms Hintikka.DeltaExi by metis
      then have \<open>M S (sub 0 t p)\<close>
        using wf Exi size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(12) in_measure lessI)
      moreover have \<open>semantics_term (E S) (F S) t = t\<close>
        using \<open>t \<in> terms S\<close> usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
      ultimately show \<open>M S x\<close>
        using Exi \<open>t \<in> terms S\<close> by auto
    qed
  next
    case (Uni p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then obtain t where \<open>t \<in> terms S\<close> \<open>sub 0 t p \<in> S\<close>
        using Uni assms Hintikka.DeltaUni by metis
      then have \<open>\<not> M S (sub 0 t p)\<close>
        using wf Uni size_sub
        by (metis (no_types, lifting) add.right_neutral add_Suc_right fm.size(13) in_measure lessI)
      moreover have \<open>semantics_term (E S) (F S) t = t\<close>
        using \<open>t \<in> terms S\<close> usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
      ultimately show \<open>\<not> M S x\<close>
        using Uni \<open>t \<in> terms S\<close> by auto
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>\<forall>t \<in> terms S. Neg (sub 0 t p) \<in> S\<close>
        using Uni assms Hintikka.GammaUni by blast
      then have \<open>\<forall>t \<in> terms S. M S (sub 0 t p)\<close>
        using wf Uni size_sub
        by (metis (no_types, lifting) Nat.add_0_right add_Suc_right fm.size(13) in_measure lessI)
      moreover have \<open>\<forall>t \<in> terms S. semantics_term (E S) (F S) t = t\<close>
        using usemantics_E(1) terms_downwards_closed unfolding list_all_def by blast
      ultimately have \<open>\<forall>t \<in> terms S. \<not> usemantics (terms S) (SeCaV.shift (E S) 0 t) (F S) (G S) (Neg p)\<close>
        by simp
      then show \<open>M S x\<close>
        using Uni by simp
    qed
  next
    case (Neg p)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> S\<close>
      then show \<open>\<not> M S x\<close>
        using wf Neg by fastforce
    next
      assume \<open>Neg x \<in> S\<close>
      then have \<open>p \<in> S\<close>
        using Neg assms Hintikka.Neg by blast
      then show \<open>M S x\<close>
        using wf Neg by fastforce
    qed
  qed
qed

end
