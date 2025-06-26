theory Reduced_MLSS_Formula_Singleton_Model_Property
  imports Syntactic_Description Place_Realisation MLSSmf_to_MLSS
begin

locale satisfiable_normalized_MLSS_clause_with_vars_for_proper_Venn_regions =
  satisfiable_normalized_MLSS_clause \<C> \<A> for \<C> \<A> +
    fixes U :: "'a set"
    \<comment>\<open>The collection of variables representing
       the proper Venn regions of the "original" variable set of the MLSSmf clause\<close>
  assumes U_subset_V: "U \<subseteq> V"
      and no_overlap_within_U: "\<lbrakk>u\<^sub>1 \<in> U; u\<^sub>2 \<in> U; u\<^sub>1 \<noteq> u\<^sub>2\<rbrakk> \<Longrightarrow> \<A> u\<^sub>1 \<sqinter> \<A> u\<^sub>2 = 0"
      and U_collect_places_neq: "AF (Var x =\<^sub>s Var y) \<in> \<C> \<Longrightarrow>
          \<exists>L M. L \<subseteq> U \<and> M \<subseteq> U \<and> \<A> x = \<Squnion>HF (\<A> ` L) \<and> \<A> y = \<Squnion>HF (\<A> ` M)"
      and U_collect_places_single: "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C> \<Longrightarrow>
          \<exists>L M. L \<subseteq> U \<and> M \<subseteq> U \<and> \<A> x = \<Squnion>HF (\<A> ` L) \<and> \<A> y = \<Squnion>HF (\<A> ` M)"
begin

interpretation \<BB>: adequate_place_framework \<C> PI at\<^sub>p
  using syntactic_description_is_adequate by blast

lemma fact_1:
  assumes "u\<^sub>1 \<in> U"
      and "u\<^sub>2 \<in> U"
      and "u\<^sub>1 \<noteq> u\<^sub>2"
      and "\<pi> \<in> PI"
    shows "\<not> (\<pi> u\<^sub>1 \<and> \<pi> u\<^sub>2)"
proof (rule ccontr)
  assume "\<not> \<not> (\<pi> u\<^sub>1 \<and> \<pi> u\<^sub>2)"
  then have "\<pi> u\<^sub>1" "\<pi> u\<^sub>2" by blast+
  from \<open>\<pi> \<in> PI\<close> obtain \<sigma> where "\<sigma> \<in> \<Sigma>" "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" by auto
  then have "\<sigma> \<noteq> 0" by fastforce
  from \<open>\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>\<close> \<open>\<pi> u\<^sub>1\<close> \<open>\<pi> u\<^sub>2\<close> have "\<sigma> \<le> \<A> u\<^sub>1" "\<sigma> \<le> \<A> u\<^sub>2" by simp+
  with \<open>\<sigma> \<noteq> 0\<close> have "\<A> u\<^sub>1 \<sqinter> \<A> u\<^sub>2 \<noteq> 0" by blast
  with no_overlap_within_U show False
    using \<open>u\<^sub>1 \<in> U\<close> \<open>u\<^sub>2 \<in> U\<close> \<open>u\<^sub>1 \<noteq> u\<^sub>2\<close> by blast
qed

fun place_eq :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "place_eq \<pi>\<^sub>1 \<pi>\<^sub>2 \<longleftrightarrow> (\<forall>x \<in> V. \<pi>\<^sub>1 x = \<pi>\<^sub>2 x)"

fun place_sim :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" (infixl "\<sim>" 50) where
  "place_sim \<pi>\<^sub>1 \<pi>\<^sub>2 \<longleftrightarrow> place_eq \<pi>\<^sub>1 \<pi>\<^sub>2 \<or> (\<exists>u \<in> U. \<pi>\<^sub>1 u \<and> \<pi>\<^sub>2 u)"

abbreviation "rel_place_sim \<equiv> {(\<pi>\<^sub>1, \<pi>\<^sub>2) \<in> PI \<times> PI. \<pi>\<^sub>1 \<sim> \<pi>\<^sub>2}"

lemma place_sim_rel_equiv_on_PI: "equiv PI rel_place_sim"
proof (rule equivI)
  have "rel_place_sim \<subseteq> PI \<times> PI" by blast
  moreover
  have "(\<pi>, \<pi>) \<in> rel_place_sim" if "\<pi> \<in> PI" for \<pi>
    using that by fastforce
  ultimately
  show "refl_on PI rel_place_sim" using refl_onI by blast
  
  show "sym rel_place_sim"
  proof (rule symI)
    fix \<pi>\<^sub>1 \<pi>\<^sub>2 assume "(\<pi>\<^sub>1, \<pi>\<^sub>2) \<in> rel_place_sim"
    then have "\<pi>\<^sub>1 \<in> PI" "\<pi>\<^sub>2 \<in> PI" "\<pi>\<^sub>1 \<sim> \<pi>\<^sub>2" by blast+
    then show "(\<pi>\<^sub>2, \<pi>\<^sub>1) \<in> rel_place_sim" by auto
  qed
  
  show "trans rel_place_sim"
  proof (rule transI)
    fix \<pi>\<^sub>1 \<pi>\<^sub>2 \<pi>\<^sub>3
    assume "(\<pi>\<^sub>1, \<pi>\<^sub>2) \<in> rel_place_sim" "(\<pi>\<^sub>2, \<pi>\<^sub>3) \<in> rel_place_sim"
    then have "\<pi>\<^sub>1 \<in> PI" "\<pi>\<^sub>2 \<in> PI" "\<pi>\<^sub>3 \<in> PI" "\<pi>\<^sub>1 \<sim> \<pi>\<^sub>2" "\<pi>\<^sub>2 \<sim> \<pi>\<^sub>3" by blast+
    then consider "place_eq \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> place_eq \<pi>\<^sub>2 \<pi>\<^sub>3" | "place_eq \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> (\<exists>u \<in> U. \<pi>\<^sub>2 u \<and> \<pi>\<^sub>3 u)"
      | "(\<exists>u \<in> U. \<pi>\<^sub>1 u \<and> \<pi>\<^sub>2 u) \<and> place_eq \<pi>\<^sub>2 \<pi>\<^sub>3" | "(\<exists>u \<in> U. \<pi>\<^sub>1 u \<and> \<pi>\<^sub>2 u) \<and> (\<exists>u \<in> U. \<pi>\<^sub>2 u \<and> \<pi>\<^sub>3 u)"
      by auto
    then have "\<pi>\<^sub>1 \<sim> \<pi>\<^sub>3"
    proof (cases)
      case 1
      then have "place_eq \<pi>\<^sub>1 \<pi>\<^sub>3" by auto
      then show ?thesis by auto
    next
      case 2
      then obtain u where "u \<in> U" "\<pi>\<^sub>2 u" "\<pi>\<^sub>3 u" by blast
      with U_subset_V have "u \<in> V" by blast
      with 2 have "\<pi>\<^sub>1 u \<longleftrightarrow> \<pi>\<^sub>2 u" by force
      with \<open>\<pi>\<^sub>2 u\<close> have "\<pi>\<^sub>1 u" by blast
      with \<open>u \<in> U\<close> \<open>\<pi>\<^sub>3 u\<close>
      show ?thesis by auto
    next
      case 3
      then obtain u where "u \<in> U" "\<pi>\<^sub>1 u" "\<pi>\<^sub>2 u" by blast
      with U_subset_V have "u \<in> V" by blast
      with 3 have "\<pi>\<^sub>2 u \<longleftrightarrow> \<pi>\<^sub>3 u" by force
      with \<open>\<pi>\<^sub>2 u\<close> have "\<pi>\<^sub>3 u" by blast
      with \<open>u \<in> U\<close> \<open>\<pi>\<^sub>1 u\<close>
      show ?thesis by auto
    next
      case 4
      then obtain u\<^sub>1 u\<^sub>2 where "u\<^sub>1 \<in> U" "\<pi>\<^sub>1 u\<^sub>1" "\<pi>\<^sub>2 u\<^sub>1" and "u\<^sub>2 \<in> U" "\<pi>\<^sub>2 u\<^sub>2" "\<pi>\<^sub>3 u\<^sub>2"
        by blast
      with fact_1 have "u\<^sub>1 = u\<^sub>2"
        using \<open>\<pi>\<^sub>2 \<in> PI\<close> by blast
      with \<open>\<pi>\<^sub>3 u\<^sub>2\<close> have "\<pi>\<^sub>3 u\<^sub>1" by blast
      with \<open>\<pi>\<^sub>1 u\<^sub>1\<close> \<open>u\<^sub>1 \<in> U\<close> show ?thesis
        by auto
    qed
    with \<open>\<pi>\<^sub>1 \<in> PI\<close> \<open>\<pi>\<^sub>2 \<in> PI\<close> \<open>\<pi>\<^sub>3 \<in> PI\<close>
    show "(\<pi>\<^sub>1, \<pi>\<^sub>3) \<in> rel_place_sim" by blast
  qed
qed

lemma refl_sim:
  assumes "a \<in> PI"
      and "b \<in> PI"
      and "a \<sim> b"
    shows "b \<sim> a"
  using assms by auto

lemma trans_sim:
  assumes "a \<in> PI"
      and "b \<in> PI"
      and "c \<in> PI"
      and "a \<sim> b"
      and "b \<sim> c"
    shows "a \<sim> c"
proof -
  from assms have "(a, b) \<in> rel_place_sim" "(b, c) \<in> rel_place_sim"
    by blast+
  with place_sim_rel_equiv_on_PI have "(a, c) \<in> rel_place_sim"
    using equivE transE
    by (smt (verit, ccfv_SIG))
  then show "a \<sim> c" by blast
qed

lemma fact_2:
  assumes "x \<in> V"
      and exL: "\<exists>L \<subseteq> U. \<A> x = \<Squnion>HF (\<A> ` L)"
      and "\<pi>\<^sub>1 \<in> PI"
      and "\<pi>\<^sub>2 \<in> PI"
      and "\<pi>\<^sub>1 \<sim> \<pi>\<^sub>2"
    shows "\<pi>\<^sub>1 x \<longleftrightarrow> \<pi>\<^sub>2 x"
proof (cases "place_eq \<pi>\<^sub>1 \<pi>\<^sub>2")
  case True
  with \<open>x \<in> V\<close> show ?thesis by force
next
  case False
  with \<open>\<pi>\<^sub>1 \<sim> \<pi>\<^sub>2\<close> obtain u where "u \<in> U" "\<pi>\<^sub>1 u" "\<pi>\<^sub>2 u" by auto
  from exL obtain L where "L \<subseteq> U" "\<A> x = \<Squnion>HF (\<A> ` L)" by blast
  from \<open>L \<subseteq> U\<close> U_subset_V finite_V have "finite L"
    by (simp add: finite_subset)

  have "\<pi> x \<longleftrightarrow> u \<in> L" if "\<pi> u" "\<pi> \<in> PI" for \<pi>
  proof -
    from \<open>\<pi> \<in> PI\<close> obtain \<sigma> where "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" "\<sigma> \<in> \<Sigma>" by auto
    with \<open>\<pi> u\<close> have "\<sigma> \<le> \<A> u"
      using \<open>u \<in> U\<close> U_subset_V by auto
    have "\<sigma> \<le> \<A> x \<longleftrightarrow> u \<in> L"
    proof (standard)
      assume "\<sigma> \<le> \<A> x"
      {assume "u \<notin> L"
        then have "\<forall>v \<in> L. v \<noteq> u" by blast
        with no_overlap_within_U have "\<forall>v \<in> L. \<A> v \<sqinter> \<A> u = 0"
          using \<open>L \<subseteq> U\<close> \<open>u \<in> U\<close> by auto
        with \<open>\<sigma> \<le> \<A> u\<close> have "\<forall>v \<in> L. \<A> v \<sqinter> \<sigma> = 0" by blast
        then have "\<Squnion>HF (\<A> ` L) \<sqinter> \<sigma> = 0"
          using finite_V U_subset_V \<open>L \<subseteq> U\<close> by auto
        with \<open>\<A> x = \<Squnion>HF (\<A> ` L)\<close> have "\<A> x \<sqinter> \<sigma> = 0" by argo
        with \<open>\<sigma> \<le> \<A> x\<close> have False
          using \<open>\<sigma> \<in> \<Sigma>\<close> mem_\<Sigma>_not_empty by blast
      }
      then show "u \<in> L" by blast
    next
      assume "u \<in> L"
      with \<open>\<sigma> \<le> \<A> u\<close> have "\<sigma> \<le> \<Squnion>HF (\<A> ` L)"
        using \<open>finite L\<close> by force
      with \<open>\<A> x = \<Squnion>HF (\<A> ` L)\<close> show "\<sigma> \<le> \<A> x" by simp
    qed
    with \<open>\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>\<close> show "\<pi> x \<longleftrightarrow> u \<in> L"
      using \<open>x \<in> V\<close> associated_place.simps by blast
  qed
  with \<open>\<pi>\<^sub>1 \<in> PI\<close> \<open>\<pi>\<^sub>1 u\<close> \<open>\<pi>\<^sub>2 \<in> PI\<close> \<open>\<pi>\<^sub>2 u\<close>
  have "\<pi>\<^sub>1 x \<longleftrightarrow> u \<in> L" "\<pi>\<^sub>2 x \<longleftrightarrow> u \<in> L" by blast+
  then show ?thesis by blast
qed

lemma U_collect_places_single': "y \<in> W \<Longrightarrow> \<exists>L. L \<subseteq> U \<and> \<A> y = \<Squnion>HF (\<A> ` L)"
  using U_collect_places_single
  by (meson memW_E)

definition PI' :: "('a \<Rightarrow> bool) set" where
  "PI' \<equiv> (\<lambda>\<pi>s. SOME \<pi>. \<pi> \<in> \<pi>s) ` (PI // rel_place_sim)"

definition rep :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "rep \<pi> = (SOME \<pi>'. \<pi>' \<in> rel_place_sim `` {\<pi>})"

lemma range_rep:
  assumes "\<pi> \<in> PI"
    shows "rep \<pi> \<in> PI'"
  using assms
  unfolding PI'_def rep_def
  using quotientI[where ?x = \<pi> and ?A = PI and ?r = rel_place_sim]
  by blast

lemma PI'_eq_image_of_rep_on_PI: "PI' = rep ` PI"
proof (standard; standard)
  fix \<pi> assume "\<pi> \<in> PI'"
  then obtain \<pi>s where "\<pi>s \<in> PI // rel_place_sim" "\<pi> = (SOME \<pi>. \<pi> \<in> \<pi>s)"
    unfolding PI'_def by blast
  then obtain \<pi>\<^sub>0 where "\<pi>s = rel_place_sim `` {\<pi>\<^sub>0}" "\<pi>\<^sub>0 \<in> PI"
    using quotientE[where ?A = PI and ?r = rel_place_sim and ?X = \<pi>s]
    by blast
  with \<open>\<pi> = (SOME \<pi>. \<pi> \<in> \<pi>s)\<close> have "\<pi> = rep \<pi>\<^sub>0"
    unfolding rep_def by blast
 with \<open>\<pi>\<^sub>0 \<in> PI\<close> show "\<pi> \<in> rep ` PI" by blast
next
  fix \<pi> assume "\<pi> \<in> rep ` PI"
  then obtain \<pi>\<^sub>0 where "\<pi>\<^sub>0 \<in> PI" "\<pi> = rep \<pi>\<^sub>0" by blast
  then show "\<pi> \<in> PI'" using range_rep by blast
qed

lemma rep_sim:
  assumes "\<pi> \<in> PI"
    shows "\<pi> \<sim> rep \<pi>"
      and "rep \<pi> \<sim> \<pi>"
proof -
  from \<open>\<pi> \<in> PI\<close> have "\<pi> \<in> rel_place_sim `` {\<pi>}" by fastforce
  then obtain \<pi>' where "\<pi>' = rep \<pi>" by blast
  with someI[of "\<lambda>x. x \<in> rel_place_sim `` {\<pi>}"] have "\<pi>' \<in> rel_place_sim `` {\<pi>}"
    using \<open>\<pi> \<in> rel_place_sim `` {\<pi>}\<close>
    unfolding rep_def by fast
  with \<open>\<pi>' = rep \<pi>\<close> show "\<pi> \<sim> rep \<pi>" by fast
  with place_sim_rel_equiv_on_PI show "rep \<pi> \<sim> \<pi>"
    by (metis (full_types) place_eq.simps place_sim.elims(1))
qed

lemma PI'_subset_PI: "PI' \<subseteq> PI"
  unfolding PI'_def
  using equiv_Eps_preserves place_sim_rel_equiv_on_PI by blast

lemma sim_self:
  assumes "\<pi> \<in> PI'"
      and "\<pi>' \<in> PI'"
      and "\<pi> \<sim> \<pi>'"
    shows "\<pi>' = \<pi>"
proof -
  from \<open>\<pi> \<sim> \<pi>'\<close> have "(\<pi>, \<pi>') \<in> rel_place_sim"
    using \<open>\<pi> \<in> PI'\<close> \<open>\<pi>' \<in> PI'\<close> PI'_subset_PI by blast
  from \<open>\<pi> \<in> PI'\<close> obtain \<pi>s where "\<pi>s \<in> PI // rel_place_sim" "\<pi> = (SOME \<pi>. \<pi> \<in> \<pi>s)"
    unfolding PI'_def by blast
  then have "\<pi> \<in> \<pi>s"
    using equiv_Eps_in place_sim_rel_equiv_on_PI by blast
  from \<open>\<pi>' \<in> PI'\<close> obtain \<pi>s' where "\<pi>s' \<in> PI // rel_place_sim" "\<pi>' = (SOME \<pi>. \<pi> \<in> \<pi>s')"
    unfolding PI'_def by blast
  then have "\<pi>' \<in> \<pi>s'"
    using equiv_Eps_in place_sim_rel_equiv_on_PI by blast
  from place_sim_rel_equiv_on_PI \<open>\<pi>s \<in> PI // rel_place_sim\<close> \<open>\<pi>s' \<in> PI // rel_place_sim\<close>
       \<open>\<pi> \<in> \<pi>s\<close> \<open>\<pi>' \<in> \<pi>s'\<close> \<open>(\<pi>, \<pi>') \<in> rel_place_sim\<close>
  have "\<pi>s = \<pi>s'"
    using quotient_eqI[where ?A = PI and ?r = rel_place_sim and ?x = \<pi> and ?X = \<pi>s and ?y = \<pi>' and ?Y = \<pi>s']
    by fast
  with \<open>\<pi> = (SOME \<pi>. \<pi> \<in> \<pi>s)\<close> \<open>\<pi>' = (SOME \<pi>. \<pi> \<in> \<pi>s')\<close> show "\<pi>' = \<pi>"
    by auto
qed

fun at\<^sub>p_f' :: "'a \<Rightarrow> ('a \<Rightarrow> bool)" where
  "at\<^sub>p_f' w = rep (at\<^sub>p_f w)"

definition "at\<^sub>p' = {(y, at\<^sub>p_f' y)|y. y \<in> W}"
declare at\<^sub>p'_def [simp]

lemma range_at\<^sub>p_f':
  assumes "w \<in> W"
  shows "at\<^sub>p_f' w \<in> PI'"
proof -
  from \<open>w \<in> W\<close> range_at\<^sub>p_f have "at\<^sub>p_f w \<in> PI" by blast
  then have "rel_place_sim `` {at\<^sub>p_f w} \<in> PI // rel_place_sim"
    using quotientI by fast
  then show ?thesis unfolding PI'_def
    apply (simp only: at\<^sub>p_f'.simps rep_def)
    by (smt (verit, best) Eps_cong at\<^sub>p_f'.elims image_insert insert_iff mk_disjoint_insert)
qed

lemma rep_at:
  assumes "\<pi> \<in> PI"
      and "(y, \<pi>) \<in> at\<^sub>p"
    shows "(y, rep \<pi>) \<in> at\<^sub>p'"
proof -
  from \<open>(y, \<pi>) \<in> at\<^sub>p\<close> have "at\<^sub>p_f y = \<pi>" by auto
  from \<open>(y, \<pi>) \<in> at\<^sub>p\<close> have "y \<in> W" by auto
  with W_subset_V have "y \<in> V" by fast
  from \<open>(y, \<pi>) \<in> at\<^sub>p\<close> obtain x where "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>" "x \<in> V"
    using memW_E by fastforce
  with U_collect_places_single have "\<exists>L. L \<subseteq> U \<and> \<A> x = \<Squnion>HF (\<A> ` L)" by meson
  with fact_2 have "\<pi>\<^sub>1 x \<longleftrightarrow> \<pi>\<^sub>2 x" if "\<pi>\<^sub>1 \<sim> \<pi>\<^sub>2" "\<pi>\<^sub>1 \<in> PI" "\<pi>\<^sub>2 \<in> PI" for \<pi>\<^sub>1 \<pi>\<^sub>2
    using \<open>x \<in> V\<close> that by blast
  with rep_sim have "(rep \<pi>) x \<longleftrightarrow> \<pi> x"
    using PI'_subset_PI \<open>\<pi> \<in> PI\<close> range_rep by blast
  
  from \<BB>.C5_1[where ?x = x and ?y = y] have "\<pi> x" "\<forall>\<pi>'\<in>PI. \<pi>' \<noteq> \<pi> \<longrightarrow> \<not> \<pi>' x"
    using \<open>AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>\<close> \<open>(y, \<pi>) \<in> at\<^sub>p\<close> by fastforce+
  
  from \<open>\<pi> x\<close> \<open>(rep \<pi>) x \<longleftrightarrow> \<pi> x\<close> have "(rep \<pi>) x" by blast
  with \<open>\<forall>\<pi>'\<in>PI. \<pi>' \<noteq> \<pi> \<longrightarrow> \<not> \<pi>' x\<close> have "rep \<pi> = \<pi>"
    using range_rep PI'_subset_PI \<open>\<pi> \<in> PI\<close> by blast
  then have "at\<^sub>p_f' y = rep \<pi>"
    using \<open>at\<^sub>p_f y = \<pi>\<close> by (simp only: at\<^sub>p_f'.simps)
  then show "(y, rep \<pi>) \<in> at\<^sub>p'"
    using \<open>y \<in> W\<close>
    by (metis (mono_tags, lifting) at\<^sub>p'_def mem_Collect_eq)
qed

interpretation \<BB>': adequate_place_framework \<C> PI' at\<^sub>p'
proof -
  from PI'_subset_PI \<BB>.PI_subset_places_V
  have PI'_subset_places_V: "PI' \<subseteq> places V" by blast

  have dom_at\<^sub>p': "Domain at\<^sub>p' = W" by auto
  have range_at\<^sub>p': "Range at\<^sub>p' \<subseteq> PI'"
  proof -
    {fix y lt assume "lt \<in> \<C>" "y \<in> singleton_vars lt"
      then have "rep (at\<^sub>p_f y) \<in> PI'"
        using range_at\<^sub>p_f[of y] range_rep[of "at\<^sub>p_f y"]
        by blast
    }
    then show ?thesis by auto
  qed

  from \<BB>.single_valued_at\<^sub>p
  have single_valued_at\<^sub>p': "single_valued at\<^sub>p'"
    unfolding single_valued_def at\<^sub>p'_def
    apply (simp only: at\<^sub>p_f'.simps)
    by blast

  from PI'_subset_PI have "place_membership \<C> PI' \<subseteq> place_membership \<C> PI" by auto
  with \<BB>.membership_irreflexive have membership_irreflexive:
    "(\<pi>, \<pi>) \<notin> place_membership \<C> PI'" for \<pi>
    by blast

  from PI'_subset_PI have subgraph: "subgraph (place_mem_graph \<C> PI') (place_mem_graph \<C> PI)"
  proof -
    have "verts (place_mem_graph \<C> PI') = PI'" by simp
    moreover
    have "verts (place_mem_graph \<C> PI) = PI" by simp
    ultimately
    have verts: "verts (place_mem_graph \<C> PI') \<subseteq> verts (place_mem_graph \<C> PI)"
      using PI'_subset_PI by presburger

    have "arcs (place_mem_graph \<C> PI') = place_membership \<C> PI'" by simp
    moreover
    have "arcs (place_mem_graph \<C> PI) = place_membership \<C> PI" by simp
    moreover
    have "place_membership \<C> PI' \<subseteq> place_membership \<C> PI"
      using PI'_subset_PI by auto
    ultimately
    have arcs: "arcs (place_mem_graph \<C> PI') \<subseteq> arcs (place_mem_graph \<C> PI)" by blast

    have "compatible (place_mem_graph \<C> PI) (place_mem_graph \<C> PI')"
      unfolding compatible_def by simp
    with verts arcs show "subgraph (place_mem_graph \<C> PI') (place_mem_graph \<C> PI)"
      unfolding subgraph_def
      using place_mem_graph_wf_digraph
      by blast
  qed

  from \<BB>.C6 have "\<nexists>c. pre_digraph.cycle (place_mem_graph \<C> PI) c"
    using dag.acyclic by blast
  then have "\<nexists>c. pre_digraph.cycle (place_mem_graph \<C> PI') c"
    using subgraph wf_digraph.subgraph_cycle by blast
  then have C6: "dag (place_mem_graph \<C> PI')"
    using \<open>dag (place_mem_graph \<C> PI)\<close> dag_axioms_def dag_def digraph.digraph_subgraph subgraph
    by blast

  from \<BB>.C1_1 PI'_subset_PI
  have C1_1: "\<exists>n. AT (Var x =\<^sub>s \<emptyset> n) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI'. \<not> \<pi> x" for x
    by fast

  from \<BB>.C1_2 PI'_subset_PI
  have C1_2: "AT (Var x =\<^sub>s Var y) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI'. \<pi> x \<longleftrightarrow> \<pi> y" for x y
    by fast

  from \<BB>.C2 PI'_subset_PI
  have C2: "AT (Var x =\<^sub>s Var y \<squnion>\<^sub>s Var z) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI'. \<pi> x \<longleftrightarrow> \<pi> y \<or> \<pi> z" for x y z
    by fast

  from \<BB>.C3 PI'_subset_PI
  have C3: "AT (Var x =\<^sub>s Var y -\<^sub>s Var z) \<in> \<C> \<Longrightarrow> \<forall>\<pi> \<in> PI'. \<pi> x \<longleftrightarrow> \<pi> y \<and> \<not> \<pi> z" for x y z
    by fast

  have C4: "AF (Var x =\<^sub>s Var y) \<in> \<C> \<Longrightarrow> \<exists>\<pi> \<in> PI'. \<pi> x \<longleftrightarrow> \<not> \<pi> y" for x y
  proof -
    assume neq: "AF (Var x =\<^sub>s Var y) \<in> \<C>"
    with \<BB>.C4 obtain \<pi> where "\<pi> \<in> PI" "\<pi> x \<longleftrightarrow> \<not> \<pi> y" by blast
    from neq have "x \<in> V" "y \<in> V" by fastforce+
    from neq U_collect_places_neq[where ?x = x and ?y = y] fact_2[of x]
    have sim_\<pi>_x: "\<pi>\<^sub>1 x = \<pi>\<^sub>2 x" if "\<pi>\<^sub>1 \<in> PI" "\<pi>\<^sub>2 \<in> PI" "\<pi>\<^sub>1 \<sim> \<pi>\<^sub>2" for \<pi>\<^sub>1 \<pi>\<^sub>2
      using that \<open>x \<in> V\<close> by blast
    from neq U_collect_places_neq[where ?x = x and ?y = y] fact_2[of y]
    have sim_\<pi>_y: "\<pi>\<^sub>1 y = \<pi>\<^sub>2 y" if "\<pi>\<^sub>1 \<in> PI" "\<pi>\<^sub>2 \<in> PI" "\<pi>\<^sub>1 \<sim> \<pi>\<^sub>2" for \<pi>\<^sub>1 \<pi>\<^sub>2
      using that \<open>y \<in> V\<close> by blast
    from \<open>\<pi> \<in> PI\<close> have "rep \<pi> \<in> PI'" using range_rep by blast
    then have "rep \<pi> \<in> PI" using PI'_subset_PI by blast

    from rep_sim sim_\<pi>_x have "(rep \<pi>) x \<longleftrightarrow> \<pi> x"
      using \<open>rep \<pi> \<in> PI\<close> \<open>\<pi> \<in> PI\<close> by blast
    moreover
    from rep_sim sim_\<pi>_y have "\<pi> y \<longleftrightarrow> (rep \<pi>) y"
      using \<open>rep \<pi> \<in> PI\<close> \<open>\<pi> \<in> PI\<close> by blast
    ultimately
    have "(rep \<pi>) x \<longleftrightarrow> \<not> (rep \<pi>) y"
      using \<open>\<pi> x \<longleftrightarrow> \<not> \<pi> y\<close> by blast
    with \<open>rep \<pi> \<in> PI'\<close> show ?thesis by blast
  qed

  have C5_1: "\<exists>\<pi>. (y, \<pi>) \<in> at\<^sub>p' \<and> \<pi> x \<and> (\<forall>\<pi>' \<in> PI'. \<pi>' \<noteq> \<pi> \<longrightarrow> \<not> \<pi>' x)"
    if "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>" for x y
  proof -
    from that have "y \<in> W" "x \<in> V" "y \<in> V" by fastforce+
    from that \<BB>.C5_1[where ?y = y and ?x = x]
    obtain \<pi> where \<pi>: "(y, \<pi>) \<in> at\<^sub>p" "\<pi> x" "\<forall>\<pi>' \<in> PI. \<pi>' \<noteq> \<pi> \<longrightarrow> \<not> \<pi>' x"
      by blast
    with \<BB>.range_at\<^sub>p have "\<pi> \<in> PI" by fast
    then have "rep \<pi> \<in> PI'" using range_rep by blast
    from rep_sim have "rep \<pi> \<sim> \<pi>" using \<open>\<pi> \<in> PI\<close> by fast
    with U_collect_places_single \<open>\<pi> x\<close> fact_2 have "(rep \<pi>) x"
      using \<open>x \<in> V\<close> \<open>\<pi> \<in> PI\<close> \<open>rep \<pi> \<in> PI'\<close> PI'_subset_PI that
      by blast
    with \<pi> have "rep \<pi> = \<pi>"
      using \<open>rep \<pi> \<in> PI'\<close> PI'_subset_PI by blast
    with \<pi> show ?thesis
      using \<open>rep \<pi> \<in> PI'\<close> PI'_subset_PI
      by (metis rep_at subset_iff)
  qed

  have C5_2: "\<forall>\<pi> \<in> PI'. \<pi> y \<longleftrightarrow> \<pi> z" if "y \<in> W" "z \<in> W" and at'_eq: "\<exists>\<pi>. (y, \<pi>) \<in> at\<^sub>p' \<and> (z, \<pi>) \<in> at\<^sub>p'" for y z
  proof
    fix \<pi> assume "\<pi> \<in> PI'"
    from at'_eq obtain \<pi>' where \<pi>': "at\<^sub>p_f' y = \<pi>'" "at\<^sub>p_f' z = \<pi>'"
      by (simp only: at\<^sub>p'_def) fast
    with range_at\<^sub>p_f' \<open>y \<in> W\<close> have "\<pi>' \<in> PI'" by blast
    from \<pi>' have "at\<^sub>p_f' y \<sim> at\<^sub>p_f' z"
      apply (simp only: at\<^sub>p_f'.simps place_sim.simps place_eq.simps)
      by blast
    moreover
    from rep_sim have "at\<^sub>p_f' y \<sim> at\<^sub>p_f y"
      using at\<^sub>p_f'.simps range_at\<^sub>p_f that(1) by presburger
    moreover
    from rep_sim have "at\<^sub>p_f' z \<sim> at\<^sub>p_f z"
      using at\<^sub>p_f'.simps range_at\<^sub>p_f that(2) by presburger
    ultimately
    have "at\<^sub>p_f y \<sim> at\<^sub>p_f z"
      using trans_sim[of "at\<^sub>p_f y" "at\<^sub>p_f' y" "at\<^sub>p_f' z"]
      using trans_sim[of "at\<^sub>p_f y" "at\<^sub>p_f' z" "at\<^sub>p_f z"]
      using refl_sim[of "at\<^sub>p_f' y" "at\<^sub>p_f y"]
      using range_at\<^sub>p_f[of y] range_at\<^sub>p_f[of z] range_at\<^sub>p_f' PI'_subset_PI that(1-2)
      by (meson subset_iff)
    then consider "at\<^sub>p_f y = at\<^sub>p_f z" | "\<exists>u \<in> U. at\<^sub>p_f y u \<and> at\<^sub>p_f z u"
      by force
    then show "\<pi> y \<longleftrightarrow> \<pi> z"
    proof (cases)
      case 1
      then have "\<exists>\<pi>. (y, \<pi>) \<in> at\<^sub>p \<and> (z, \<pi>) \<in> at\<^sub>p"
        using at\<^sub>p_def \<open>y \<in> W\<close> \<open>z \<in> W\<close> by blast
      with \<BB>.C5_2 have "\<forall>\<pi> \<in> PI. \<pi> y \<longleftrightarrow> \<pi> z"
        using \<open>y \<in> W\<close> \<open>z \<in> W\<close> by presburger
      with \<open>\<pi> \<in> PI'\<close> PI'_subset_PI show "\<pi> y \<longleftrightarrow> \<pi> z"
        by fast
    next
      case 2
      then obtain u where "u \<in> U" "at\<^sub>p_f y u" "at\<^sub>p_f z u" by blast
      then have "\<A> y \<^bold>\<in> \<A> u" "\<A> z \<^bold>\<in> \<A> u"
        by (simp add: less_eq_hf_def)+
      from \<open>y \<in> W\<close> obtain x\<^sub>1 where x\<^sub>1_single_y: "AT (Var x\<^sub>1 =\<^sub>s Single (Var y)) \<in> \<C>"
        using memW_E by blast
      with \<A>_sat_\<C> have "\<A> x\<^sub>1 = HF {\<A> y}" by fastforce
      then have "\<A> y \<^bold>\<in> \<A> x\<^sub>1" by simp      
      from x\<^sub>1_single_y U_collect_places_single obtain L where "L \<subseteq> U" "\<A> x\<^sub>1 = \<Squnion>HF (\<A> ` L)"
        by meson
      with \<open>\<A> y \<^bold>\<in> \<A> x\<^sub>1\<close> obtain u' where "u' \<in> L" "\<A> y \<^bold>\<in> \<A> u'" by auto
      from \<open>\<A> x\<^sub>1 = \<Squnion>HF (\<A> ` L)\<close> \<open>u' \<in> L\<close> have "\<A> u' \<le> \<A> x\<^sub>1"
        using \<open>\<A> y \<^bold>\<in> \<A> x\<^sub>1\<close> by auto
      with \<open>\<A> x\<^sub>1 = HF {\<A> y}\<close> \<open>\<A> y \<^bold>\<in> \<A> u'\<close> have "\<A> u' = HF {\<A> y}" by auto
      with \<open>\<A> y \<^bold>\<in> \<A> u\<close> \<open>u \<in> U\<close> \<open>u' \<in> L\<close> \<open>L \<subseteq> U\<close> no_overlap_within_U
      have "u' = u" by fastforce
      with \<open>\<A> u' = HF {\<A> y}\<close> \<open>\<A> z \<^bold>\<in> \<A> u\<close> have "\<A> y = \<A> z" by simp
      with realise_same_implies_eq_under_all_\<pi>[of y z \<pi>] show ?thesis
        using \<open>y \<in> W\<close> \<open>z \<in> W\<close> W_subset_V \<open>\<pi> \<in> PI'\<close> PI'_subset_PI by blast
    qed
  qed

  have C5_3: "\<exists>\<pi>. (y, \<pi>) \<in> at\<^sub>p' \<and> (y', \<pi>) \<in> at\<^sub>p'"
    if "y \<in> W" "y' \<in> W" "\<forall>\<pi>' \<in> PI'. \<pi>' y' \<longleftrightarrow> \<pi>' y" for y' y
  proof -
    from \<open>\<forall>\<pi>' \<in> PI'. \<pi>' y' \<longleftrightarrow> \<pi>' y\<close> have "\<forall>\<pi> \<in> PI. rep \<pi> y' \<longleftrightarrow> rep \<pi> y"
      by (metis range_rep)
    {fix \<pi> assume "\<pi> \<in> PI"
      with \<open>\<forall>\<pi>' \<in> PI'. \<pi>' y' \<longleftrightarrow> \<pi>' y\<close> have "rep \<pi> y' \<longleftrightarrow> rep \<pi> y"
        using range_rep by fast
      from \<open>\<pi> \<in> PI\<close> PI'_subset_PI range_rep have "rep \<pi> \<in> PI" by blast
      from U_collect_places_single'[of y'] fact_2[of y' "rep \<pi>" \<pi>] rep_sim[of \<pi>]
      have "rep \<pi> y' \<longleftrightarrow> \<pi> y'"
        using \<open>y' \<in> W\<close> W_subset_V \<open>\<pi> \<in> PI\<close> \<open>rep \<pi> \<in> PI\<close>
        by blast
      from U_collect_places_single'[of y] fact_2[of y "rep \<pi>" \<pi>] rep_sim[of \<pi>]
      have "rep \<pi> y \<longleftrightarrow> \<pi> y"
        using \<open>y \<in> W\<close> W_subset_V \<open>\<pi> \<in> PI\<close> \<open>rep \<pi> \<in> PI\<close>
        by blast
      from \<open>rep \<pi> y' \<longleftrightarrow> rep \<pi> y\<close> \<open>rep \<pi> y' \<longleftrightarrow> \<pi> y'\<close> \<open>rep \<pi> y \<longleftrightarrow> \<pi> y\<close>
      have "\<pi> y \<longleftrightarrow> \<pi> y'" by blast
    }
    with \<BB>.C5_3 obtain \<pi> where "(y, \<pi>) \<in> at\<^sub>p" "(y', \<pi>) \<in> at\<^sub>p"
      using \<open>y \<in> W\<close> \<open>y' \<in> W\<close> by blast
    then have "(y, rep \<pi>) \<in> at\<^sub>p'" "(y', rep \<pi>) \<in> at\<^sub>p'"
      by (meson Range_iff \<BB>.range_at\<^sub>p rep_at subset_iff)+
    then show ?thesis by fast
  qed

  have "\<pi> = \<pi>\<^bsub>HF {0}\<^esub>" if "\<pi> \<in> Range at\<^sub>p' - Range (place_membership \<C> PI')" for \<pi>
  proof -
    from that obtain y where "(y, \<pi>) \<in> at\<^sub>p'" by blast
    then have "y \<in> W" "\<pi> \<in> PI'"
      using dom_at\<^sub>p' range_at\<^sub>p' by blast+
    from \<open>(y, \<pi>) \<in> at\<^sub>p'\<close> have "\<pi> = rep (at\<^sub>p_f y)" by simp
    from \<open>y \<in> W\<close> obtain x where lt_in_\<C>: "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>"
      using memW_E by blast
    with \<A>_sat_\<C> have "\<A> x = HF {\<A> y}" by fastforce
    then have "\<sigma>\<^bsub>y\<^esub> \<le> \<A> x" by simp
    with lt_in_\<C> have "at\<^sub>p_f y x" by force
    with \<open>\<pi> = rep (at\<^sub>p_f y)\<close> fact_2[of x] rep_sim[of "at\<^sub>p_f y"] U_collect_places_single[of x y]
    have "\<pi> x"
      using lt_in_\<C> \<open>\<pi> \<in> PI'\<close> PI'_subset_PI \<open>y \<in> W\<close>
      by (smt (verit, best) \<BB>.PI_subset_places_V places_domain range_at\<^sub>p_f rev_contra_hsubsetD)

    have "\<forall>\<pi> \<in> PI. \<not> \<pi> y"
    proof (rule ccontr)
      assume "\<not> (\<forall>\<pi>\<in>PI. \<not> \<pi> y)"
      then obtain \<pi>' where "\<pi>' \<in> PI" "\<pi>' y" by blast
      with U_collect_places_single'[of y] fact_2[of y "rep \<pi>'" \<pi>'] rep_sim[of \<pi>']
      have "rep \<pi>' y"
        using \<open>y \<in> W\<close> PI'_subset_PI W_subset_V range_rep by blast
      with \<open>AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>\<close> \<open>\<pi> x\<close>
      have "(rep \<pi>', \<pi>) \<in> place_membership \<C> PI'"
        using \<open>\<pi> \<in> PI'\<close> \<open>\<pi>' \<in> PI\<close> range_rep
        by (simp only: place_membership.simps) blast
      then have "\<pi> \<in> Range (place_membership \<C> PI')" by blast
      with that show False by blast
    qed
    have "\<forall>\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0"
    proof (rule ccontr)
      assume "\<not> (\<forall>\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0)"
      then obtain \<alpha> where \<alpha>: "\<alpha> \<in> \<L> V y" "proper_Venn_region \<alpha> \<noteq> 0" by blast
      then have "y \<in> \<alpha>" "\<alpha> \<in> P\<^sup>+ V" by auto
      with \<open>proper_Venn_region \<alpha> \<noteq> 0\<close> have "proper_Venn_region \<alpha> \<le> \<A> y"
        using proper_Venn_region_subset_variable_iff
        by (meson mem_P_plus_subset subset_iff)
      then have "\<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> y"
        using W_subset_V \<open>y \<in> W\<close> by auto
      with \<open>\<forall>\<pi> \<in> PI. \<not> \<pi> y\<close> show False
        using \<alpha> by auto
    qed
    then have "\<Squnion>HF (proper_Venn_region ` \<L> V y) = 0"
      by fastforce
    with variable_as_composition_of_proper_Venn_regions[of y]
    have "\<A> y = 0"
      using \<open>y \<in> W\<close> W_subset_V by auto
    with \<open>\<A> x = HF {\<A> y}\<close> have "\<A> x = HF {0}" by argo

    from \<open>\<pi> \<in> PI'\<close> PI'_subset_PI obtain \<sigma> where "\<sigma> \<in> \<Sigma>" "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>"
      by (metis PI_def image_iff in_mono)
    with \<open>\<pi> x\<close> have "\<sigma> \<noteq> 0" "\<sigma> \<le> \<A> x" by simp+
    with \<open>\<A> x = HF {0}\<close> have "\<sigma> = HF {0}" by fastforce
    with \<open>\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>\<close> show "\<pi> = \<pi>\<^bsub>HF {0}\<^esub>" by blast
  qed
  then have C7:
    "\<lbrakk>\<pi>\<^sub>1 \<in> Range at\<^sub>p' - Range (place_membership \<C> PI');
      \<pi>\<^sub>2 \<in> Range at\<^sub>p' - Range (place_membership \<C> PI')\<rbrakk> \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2" for \<pi>\<^sub>1 \<pi>\<^sub>2
    by blast

  from PI'_subset_places_V dom_at\<^sub>p' range_at\<^sub>p' single_valued_at\<^sub>p'
       membership_irreflexive C6
       C1_1 C1_2 C2 C3 C4 C5_1 C5_2 C5_3 C7
  show "adequate_place_framework \<C> PI' at\<^sub>p'"
    apply intro_locales
    unfolding adequate_place_framework_axioms_def
    by blast
qed

lemma singleton_model_for_normalized_reduced_literals:
  "\<exists>\<M>. \<forall>lt \<in> \<C>. interp I\<^sub>s\<^sub>a \<M> lt \<and> (\<forall>u \<in> U. hcard (\<M> u) \<le> 1)"
proof -
  from \<BB>'.finite_PI have "finite (PI' - Range at\<^sub>p')" by blast
  with u_exists[of "PI' - Range at\<^sub>p'" "card PI'"] obtain u where
    "\<lbrakk>\<pi>\<^sub>1 \<in> PI' - Range at\<^sub>p'; \<pi>\<^sub>2 \<in> PI' - Range at\<^sub>p'; \<pi>\<^sub>1 \<noteq> \<pi>\<^sub>2\<rbrakk> \<Longrightarrow> u \<pi>\<^sub>1 \<noteq> u \<pi>\<^sub>2"
    "\<pi> \<in> PI' - Range at\<^sub>p' \<Longrightarrow> hcard (u \<pi>) \<ge> card PI'"
  for \<pi>\<^sub>1 \<pi>\<^sub>2 \<pi>
    by blast
  then have "place_realization \<C> PI' at\<^sub>p' u"
    by unfold_locales blast+
  
  {fix x assume "x \<in> U"
    then have "\<pi>\<^sub>1 = \<pi>\<^sub>2" if "\<pi>\<^sub>1 x" "\<pi>\<^sub>2 x" "\<pi>\<^sub>1 \<in> PI'" "\<pi>\<^sub>2 \<in> PI'" for \<pi>\<^sub>1 \<pi>\<^sub>2
      using sim_self that by auto
    then consider "{\<pi> \<in> PI'. \<pi> x} = {}" | "(\<exists>\<pi>. {\<pi> \<in> PI'. \<pi> x} = {\<pi>})"
      by blast
    then have "hcard (place_realization.\<M> \<C> PI' at\<^sub>p' u x) \<le> 1"
    proof (cases)
      case 1
      then have "place_realization.\<M> \<C> PI' at\<^sub>p' u x = 0"
        using \<open>place_realization \<C> PI' at\<^sub>p' u\<close> "place_realization.\<M>.simps"
        by fastforce
      then show ?thesis by simp
    next
      case 2
      then obtain \<pi> where "{\<pi> \<in> PI'. \<pi> x} = {\<pi>}" "\<pi> \<in> PI'" by auto
      then have "place_realization.\<M> \<C> PI' at\<^sub>p' u x = \<Squnion>HF (place_realization.place_realise \<C> PI' at\<^sub>p' u ` {\<pi>})"
        using \<open>place_realization \<C> PI' at\<^sub>p' u\<close> "place_realization.\<M>.simps"
        by fastforce
      also have "... = \<Squnion>HF {place_realization.place_realise \<C> PI' at\<^sub>p' u \<pi>}"
        by simp
      finally have "place_realization.\<M> \<C> PI' at\<^sub>p' u x = \<Squnion>HF {place_realization.place_realise \<C> PI' at\<^sub>p' u \<pi>}" .
      moreover
      from place_realization.place_realise_singleton[of \<C> PI' at\<^sub>p' u]
      have "hcard (place_realization.place_realise \<C> PI' at\<^sub>p' u \<pi>) = 1"
        using \<open>place_realization \<C> PI' at\<^sub>p' u\<close> \<open>\<pi> \<in> PI'\<close> by blast
      then obtain c where "place_realization.place_realise \<C> PI' at\<^sub>p' u \<pi> = HF {c}"
        using hcard_1E[of "place_realization.place_realise \<C> PI' at\<^sub>p' u \<pi>"]
        by fastforce
      ultimately
      have "place_realization.\<M> \<C> PI' at\<^sub>p' u x = \<Squnion>HF {HF {c}}"
        by presburger
      also have "... = HF {c}" by fastforce
      also have "hcard ... = 1"
        by (simp add: hcard_def)
      finally show ?thesis by linarith
    qed
  }
  moreover
  from place_realization.\<M>_sat_\<C>
  have "\<forall>lt \<in> \<C>. interp I\<^sub>s\<^sub>a (place_realization.\<M> \<C> PI' at\<^sub>p' u) lt"
    using \<open>place_realization \<C> PI' at\<^sub>p' u\<close> by fastforce
  ultimately
  show ?thesis by blast
qed

end

theorem singleton_model_for_reduced_MLSS_clause:
  assumes norm_\<C>: "normalized_MLSSmf_clause \<C>"
      and V: "V = vars\<^sub>m \<C>"
      and \<A>_model: "normalized_MLSSmf_clause.is_model_for_reduced_dnf \<C> \<A>"
    shows "\<exists>\<M>. normalized_MLSSmf_clause.is_model_for_reduced_dnf \<C> \<M> \<and>
                (\<forall>\<alpha> \<in> P\<^sup>+ V. hcard (\<M> v\<^bsub>\<alpha>\<^esub>) \<le> 1)"
proof -
  from norm_\<C> interpret normalized_MLSSmf_clause \<C> by blast
  interpret proper_Venn_regions V "\<A> \<circ> Solo"
    using V by unfold_locales blast

  from \<A>_model have "\<forall>fm\<in>introduce_v. interp I\<^sub>s\<^sub>a \<A> fm"
    unfolding is_model_for_reduced_dnf_def reduced_dnf_def
    by blast
  with eval_v have \<A>_v: "\<forall>\<alpha> \<in> P\<^sup>+ V. \<A> v\<^bsub>\<alpha>\<^esub> = proper_Venn_region \<alpha>"
    using V V_def proper_Venn_region.simps by auto

  from \<A>_model have "\<forall>lt \<in> introduce_UnionOfVennRegions. interp I\<^sub>s\<^sub>a \<A> lt"
    unfolding is_model_for_reduced_dnf_def reduced_dnf_def by blast
  then have "\<forall>a \<in> restriction_on_UnionOfVennRegions \<alpha>s. I\<^sub>s\<^sub>a \<A> a"
    if "\<alpha>s \<in> set all_V_set_lists" for \<alpha>s
    unfolding introduce_UnionOfVennRegions_def
    using that by simp
  with eval_UnionOfVennRegions have \<A>_UnionOfVennRegions:
    "\<A> (UnionOfVennRegions \<alpha>s) = \<Squnion>HF (\<A> ` VennRegion ` set \<alpha>s)"
    if "\<alpha>s \<in> set all_V_set_lists" for \<alpha>s
    using that by (simp add: Sup.SUP_image)

  have Solo_variable_as_composition_of_v:
    "\<exists>L \<subseteq> {v\<^bsub>\<alpha>\<^esub> |\<alpha>. \<alpha> \<in> P\<^sup>+ V}. \<A> z = \<Squnion>HF (\<A> ` L)" if "\<exists>z' \<in> V. z = Solo z'" for z
  proof -
    from that obtain z' where "z' \<in> V" "z = Solo z'" by blast
    then have "VennRegion ` \<L> V z' \<subseteq> {v\<^bsub>\<alpha>\<^esub> |\<alpha>. \<alpha> \<in> P\<^sup>+ V}" by fastforce
    moreover
    from \<A>_v have "\<forall>\<alpha> \<in> \<L> V z'. \<A> v\<^bsub>\<alpha>\<^esub> = proper_Venn_region \<alpha>"
      using \<L>_subset_P_plus finite_V by fast
    then have "\<Squnion>HF (\<A> ` (VennRegion ` \<L> V z')) = \<Squnion>HF (proper_Venn_region ` \<L> V z')"
      using HUnion_eq[where ?S = "\<L> V z'" and ?f = "\<A> \<circ> VennRegion" and ?g = proper_Venn_region]
      by (simp add: image_comp)
    moreover
    from variable_as_composition_of_proper_Venn_regions
    have "(\<A> \<circ> Solo) z' = \<Squnion>HF (proper_Venn_region ` \<L> V z')"
      using \<open>z' \<in> V\<close> by presburger
    with \<open>z = Solo z'\<close> have "\<A> z = \<Squnion>HF (proper_Venn_region ` \<L> V z')" by simp
    ultimately
    have "VennRegion ` \<L> V z' \<subseteq> {v\<^bsub>\<alpha>\<^esub> |\<alpha>. \<alpha> \<in> P\<^sup>+ V} \<and> \<A> z = \<Squnion>HF (\<A> ` VennRegion ` \<L> V z')"
      by simp
    then show ?thesis by blast
  qed

  from \<A>_model obtain clause where clause:
    "clause \<in> reduced_dnf" "\<forall>lt \<in> clause. interp I\<^sub>s\<^sub>a \<A> lt"
    unfolding is_model_for_reduced_dnf_def by blast
  with reduced_dnf_normalized have "normalized_MLSS_clause clause" by blast
  with clause
  have "satisfiable_normalized_MLSS_clause_with_vars_for_proper_Venn_regions clause \<A> {v\<^bsub>\<alpha>\<^esub> |\<alpha>. \<alpha> \<in> P\<^sup>+ V}"
  proof (unfold_locales, goal_cases)
    case 1
    then show ?case
      using normalized_MLSS_clause.norm_\<C> by blast
  next
    case 2
    then show ?case
      by (simp add: normalized_MLSS_clause.finite_\<C>)
  next
    case 3
    then show ?case
      by (simp add: finite_vars_fm normalized_MLSS_clause.finite_\<C>)
  next
    case 4
    then show ?case by simp
  next
    case 5
    from \<open>clause \<in> reduced_dnf\<close> normalized_clause_contains_all_v_\<alpha>
    have "\<forall>\<alpha>\<in>P\<^sup>+ V. v\<^bsub>\<alpha>\<^esub> \<in> \<Union> (vars ` clause)"
      using V V_def by simp
    then show ?case by blast      
  next
    case (6 x y)
    then obtain \<alpha> \<beta> where \<alpha>\<beta>: "\<alpha> \<in> P\<^sup>+ V" "\<beta> \<in> P\<^sup>+ V" "x = v\<^bsub>\<alpha>\<^esub>" "y = v\<^bsub>\<beta>\<^esub>"
      by blast
    with \<open>x \<noteq> y\<close> have "\<alpha> \<noteq> \<beta>" by blast

    from \<alpha>\<beta> have "\<alpha> \<subseteq> V" "\<beta> \<subseteq> V" by auto

    from \<A>_model have "\<forall>fm\<in>introduce_v. interp I\<^sub>s\<^sub>a \<A> fm"
      unfolding is_model_for_reduced_dnf_def reduced_dnf_def by blast
    with \<alpha>\<beta> eval_v have "\<A> x = proper_Venn_region \<alpha>" "\<A> y = proper_Venn_region \<beta>"
      using V V_def proper_Venn_region.simps by auto
    with proper_Venn_region_disjoint \<open>\<alpha> \<noteq> \<beta>\<close>
    show ?case
      using \<open>\<alpha> \<subseteq> V\<close> \<open>\<beta> \<subseteq> V\<close> by presburger
  next
    case (7 x y)
    from \<open>AF (Var x =\<^sub>s Var y) \<in> clause\<close> \<open>clause \<in> reduced_dnf\<close>
    consider "AF (Var x =\<^sub>s Var y) \<in> reduce_clause" | "\<exists>clause \<in> introduce_w. AF (Var x =\<^sub>s Var y) \<in> clause"
      unfolding reduced_dnf_def introduce_v_def introduce_UnionOfVennRegions_def by blast
    then show ?case
    proof (cases)
      case 1
      then obtain lt where lt: "lt \<in> set \<C>" "AF (Var x =\<^sub>s Var y) \<in> reduce_literal lt"
        unfolding reduce_clause_def by blast
      then obtain a where "lt = AF\<^sub>m a"
        by (cases lt rule: reduce_literal.cases) auto
      from \<open>lt \<in> set \<C>\<close> norm_\<C> have "norm_literal lt" by blast
      with \<open>lt = AF\<^sub>m a\<close> norm_literal_neq
      obtain x' y' where lt: "lt = AF\<^sub>m (Var\<^sub>m x' =\<^sub>m Var\<^sub>m y')" by blast
      then have "reduce_literal lt = {AF (Var (Solo x') =\<^sub>s Var (Solo y'))}"
        by simp
      with \<open>AF (Var x =\<^sub>s Var y) \<in> reduce_literal lt\<close> have "x = Solo x'" "y = Solo y'"
        by simp+
      from lt \<open>lt \<in> set \<C>\<close> have "x' \<in> V" "y' \<in> V"
        using V by fastforce+

      from Solo_variable_as_composition_of_v show ?thesis
        using \<open>x = Solo x'\<close> \<open>y = Solo y'\<close> \<open>x' \<in> V\<close> \<open>y' \<in> V\<close>
        by (smt (verit, best))
    next
      case 2
      with lt_in_clause_in_introduce_w_E obtain l' m' f
        where l': "l' \<in> set all_V_set_lists"
          and m': "m' \<in> set all_V_set_lists"
          and f: "f \<in> set F_list"
          and "AF (Var x =\<^sub>s Var y) \<in> set (restriction_on_FunOfUnionOfVennRegions l' m' f)"
        by blast
      then have "AF (Var x =\<^sub>s Var y) = AF (Var (UnionOfVennRegions l') =\<^sub>s Var (UnionOfVennRegions m'))"
        by auto
      then have "x = UnionOfVennRegions l'" "y = UnionOfVennRegions m'" by blast+
      with \<A>_UnionOfVennRegions l' m'
      have "\<A> x = \<Squnion>HF (\<A> ` VennRegion ` set l')" "\<A> y = \<Squnion>HF (\<A> ` VennRegion ` set m')"
        by blast+
      moreover
      from l' set_all_V_set_lists have "set l' \<subseteq> P\<^sup>+ V"
        using V V_def by auto
      then have "VennRegion ` set l' \<subseteq> {v\<^bsub>\<alpha>\<^esub> |\<alpha>. \<alpha> \<in> P\<^sup>+ V}"
        by blast
      moreover
      from m' set_all_V_set_lists have "set m' \<subseteq> P\<^sup>+ V"
        using V V_def by auto
      then have "VennRegion ` set m' \<subseteq> {v\<^bsub>\<alpha>\<^esub> |\<alpha>. \<alpha> \<in> P\<^sup>+ V}"
        by blast
      ultimately
      show ?thesis by blast
    qed
  next
    case (8 x y)
    then consider "AT (Var x =\<^sub>s Single (Var y)) \<in> introduce_v"
      | "\<exists>clause \<in> introduce_w. AT (Var x =\<^sub>s Single (Var y)) \<in> clause"
      | "AT (Var x =\<^sub>s Single (Var y)) \<in> introduce_UnionOfVennRegions"
      | "AT (Var x =\<^sub>s Single (Var y)) \<in> reduce_clause"
      unfolding reduced_dnf_def by blast
    then show ?case
    proof (cases)
      case 1
      have "Var x =\<^sub>s Single (Var y) \<noteq> restriction_on_v \<alpha>" for \<alpha>
        by simp
      moreover
      have "Var x =\<^sub>s Single (Var y) \<notin> restriction_on_InterOfVars xs" for xs
        by (induction xs rule: restriction_on_InterOfVars.induct) auto
      then have "Var x =\<^sub>s Single (Var y) \<notin> (restriction_on_InterOfVars \<circ> var_set_to_list) \<alpha>" for \<alpha>
        by simp
      moreover
      have "Var x =\<^sub>s Single (Var y) \<notin> restriction_on_UnionOfVars xs" for xs
        by (induction xs rule: restriction_on_UnionOfVars.induct) auto
      then have "Var x =\<^sub>s Single (Var y) \<notin> (restriction_on_UnionOfVars \<circ> var_set_to_list) \<alpha>" for \<alpha>
        by simp
      ultimately
      have "AT (Var x =\<^sub>s Single (Var y)) \<notin> introduce_v"
        unfolding introduce_v_def by blast
      with 1 show ?thesis by blast
    next
      case 2
      with lt_in_clause_in_introduce_w_E obtain l' m' f
        where "AT (Var x =\<^sub>s Single (Var y)) \<in> set (restriction_on_FunOfUnionOfVennRegions l' m' f)"
        by blast
      moreover
      have "AT (Var x =\<^sub>s Single (Var y)) \<notin> set (restriction_on_FunOfUnionOfVennRegions l' m' f)"
        by simp
      ultimately
      show ?thesis by blast
    next
      case 3
      have "Var x =\<^sub>s Single (Var y) \<notin> restriction_on_UnionOfVennRegions \<alpha>s" for \<alpha>s
        by (induction \<alpha>s rule: restriction_on_UnionOfVennRegions.induct) auto
      then have "AT (Var x =\<^sub>s Single (Var y)) \<notin> introduce_UnionOfVennRegions"
        unfolding introduce_UnionOfVennRegions_def by blast
      with 3 show ?thesis by blast
    next
      case 4
      then obtain lt where "lt \<in> set \<C>" and reduce_lt: "AT (Var x =\<^sub>s Single (Var y)) \<in> reduce_literal lt"
        unfolding reduce_clause_def by blast
      with norm_\<C> have "norm_literal lt" by blast
      then have "\<exists>x' y'. lt = AT\<^sub>m (Var\<^sub>m x' =\<^sub>m Single\<^sub>m (Var\<^sub>m y'))"
        apply (cases lt rule: norm_literal.cases)
        using reduce_lt by auto
      then obtain x' y' where lt: "lt = AT\<^sub>m (Var\<^sub>m x' =\<^sub>m Single\<^sub>m (Var\<^sub>m y'))" by blast
      with reduce_lt have "x = Solo x'" "y = Solo y'" by simp+
      from \<open>lt \<in> set \<C>\<close> lt have "x' \<in> V" "y' \<in> V"
        using V by fastforce+
      from Solo_variable_as_composition_of_v show ?thesis
        using \<open>x = Solo x'\<close> \<open>y = Solo y'\<close> \<open>x' \<in> V\<close> \<open>y' \<in> V\<close>
        by (smt (verit, best))
    qed
  qed
  then show ?thesis
    using satisfiable_normalized_MLSS_clause_with_vars_for_proper_Venn_regions.singleton_model_for_normalized_reduced_literals
    unfolding is_model_for_reduced_dnf_def
    by (smt (verit) V V_def clause(1) introduce_v_subset_reduced_fms mem_Collect_eq subset_iff v_\<alpha>_in_vars_introduce_v)
qed

end