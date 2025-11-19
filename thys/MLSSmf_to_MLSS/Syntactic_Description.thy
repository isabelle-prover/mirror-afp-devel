theory Syntactic_Description
imports Place_Framework Proper_Venn_Regions "HereditarilyFinite.Rank"
begin

locale satisfiable_normalized_MLSS_clause = ATOM I\<^sub>s\<^sub>a +
  normalized_MLSS_clause \<C> +
  proper_Venn_regions V \<A>
  for \<C> :: "'a pset_fm set" and \<A> :: "'a \<Rightarrow> hf" +
  assumes \<A>_sat_\<C>: "\<forall>lt \<in> \<C>. I \<A> lt"
begin

\<comment>\<open>The collection of the non-empty proper regions of the Venn diagram of V under \<A>\<close>

definition \<Sigma> :: "hf set" where
  "\<Sigma> \<equiv> proper_Venn_regions.proper_Venn_region V \<A> ` (P\<^sup>+ V) - {0}"
declare \<Sigma>_def [simp]

lemma mem_\<Sigma>_not_empty: "\<sigma> \<in> \<Sigma> \<Longrightarrow> \<sigma> \<noteq> 0" by simp

fun associated_place :: "hf \<Rightarrow> ('a \<Rightarrow> bool)"  (\<open>\<pi>\<^bsub>_\<^esub>\<close>) where
  "\<pi>\<^bsub>\<sigma>\<^esub> x \<longleftrightarrow> x \<in> V \<and> \<sigma> \<le> \<A> x"

definition PI :: "('a \<Rightarrow> bool) set" where
  "PI \<equiv> associated_place ` \<Sigma>"
declare PI_def [simp]

fun containing_region :: "'a \<Rightarrow> hf" (\<open>\<sigma>\<^bsub>_\<^esub>\<close>) where
  "\<sigma>\<^bsub>x\<^esub> = HF {\<A> x}"

lemma containing_region_in_\<Sigma>:
  assumes "x \<in> W"
    shows "\<sigma>\<^bsub>x\<^esub> \<in> \<Sigma>"
proof -
  from \<open>x \<in> W\<close> obtain y where y: "AT (Var y =\<^sub>s Single (Var x)) \<in> \<C>"
    using memW_E by blast
  then have "y \<in> V" by fastforce

  from y \<A>_sat_\<C> have "\<A> y = HF {\<A> x}" by auto
  then have "\<A> y = \<sigma>\<^bsub>x\<^esub>" by simp
  moreover
  from variable_as_composition_of_proper_Venn_regions \<open>y \<in> V\<close> have "\<A> y = \<Squnion>HF (proper_Venn_region ` \<L> V y)"
    by presburger
  ultimately
  have "\<sigma>\<^bsub>x\<^esub> = \<Squnion>HF (proper_Venn_region ` \<L> V y)" by argo
  then have "\<exists>\<alpha> \<in> P\<^sup>+ V. \<A> y = proper_Venn_region \<alpha>"
  proof -
    let ?l = "{\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> \<noteq> 0}"

    have "?l \<noteq> {}"
    proof (rule ccontr)
      assume "\<not> ?l \<noteq> {}"
      then have "\<Squnion>HF (proper_Venn_region ` \<L> V y) = 0"
        using HUnion_empty[where ?f = proper_Venn_region and ?S = "\<L> V y"]
        by blast
      with \<open>\<A> y = HF {\<A> x}\<close> \<open>\<A> y = \<Squnion>HF (proper_Venn_region ` \<L> V y)\<close> show False
        by (metis Int_lower1 equals0I finite_Int finite_V finite_imageI finite_insert hemptyE hmem_HF_iff insert_not_empty subset_empty) 
    qed
    then obtain \<alpha> where "\<alpha> \<in> ?l" by blast
    moreover
    have "\<beta> = \<alpha>" if "\<beta> \<in> ?l" for \<beta>
    proof (rule ccontr)
      assume "\<beta> \<noteq> \<alpha>"

      from \<open>\<alpha> \<in> ?l\<close> \<open>y \<in> V\<close>
      have "proper_Venn_region \<alpha> \<le> \<A> y"
        by (metis (mono_tags, lifting) \<L>.elims mem_Collect_eq mem_P_plus_subset proper_Venn_region_subset_variable_iff)
      with \<open>\<alpha> \<in> ?l\<close> have "proper_Venn_region \<alpha> = \<A> y"
        using \<open>\<A> y = HF {\<A> x}\<close>
        using singleton_nonempty_subset[where ?s = "\<A> y" and ?c = "\<A> x" and ?t = "proper_Venn_region \<alpha>"]
        by fastforce

      from \<open>\<beta> \<in> ?l\<close> \<open>y \<in> V\<close>
      have "proper_Venn_region \<beta> \<le> \<A> y"
        by (metis (mono_tags, lifting) \<L>.elims mem_Collect_eq mem_P_plus_subset proper_Venn_region_subset_variable_iff)
      with \<open>\<beta> \<in> ?l\<close> have "proper_Venn_region \<beta> = \<A> y"
        using \<open>\<A> y = HF {\<A> x}\<close>
        using singleton_nonempty_subset[where ?s = "\<A> y" and ?c = "\<A> x" and ?t = "proper_Venn_region \<beta>"]
        by fastforce

      from \<open>\<beta> \<noteq> \<alpha>\<close> \<open>proper_Venn_region \<alpha> = \<A> y\<close> \<open>proper_Venn_region \<beta> = \<A> y\<close> \<open>\<A> y = HF {\<A> x}\<close> \<open>x \<in> W\<close>
      show False using proper_Venn_region_strongly_injective[where ?\<alpha> = \<alpha> and ?\<beta> = \<beta>]
        using calculation that by auto
    qed
    ultimately
    have "?l = {\<alpha>}" by blast

    have Ly_minus_l: "\<L> V y - ?l = {\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0}" by auto

    have "?l \<subseteq> \<L> V y" by blast
    then have "?l \<union> (\<L> V y - ?l) = \<L> V y" by blast
    then have "\<Squnion>HF (proper_Venn_region ` \<L> V y) = \<Squnion>HF (proper_Venn_region ` (?l \<union> (\<L> V y - ?l)))" by argo
    also have "... = \<Squnion>HF (proper_Venn_region ` (?l \<union> {\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0}))"
      using Ly_minus_l by argo
    also have "... = \<Squnion>HF (proper_Venn_region ` ?l) \<squnion> \<Squnion>HF (proper_Venn_region ` {\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0})"
      using HUnion_proper_Venn_region_union[where ?l = ?l and ?m = "{\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0}"]
      using finite_V \<open>y \<in> V\<close>
      by auto
    also have "... = \<Squnion>HF (proper_Venn_region ` ?l)"
      using finite_V \<open>y \<in> V\<close> by auto
    also have "... = \<Squnion>HF (proper_Venn_region ` {\<alpha>})"
      using \<open>?l = {\<alpha>}\<close> by argo
    also have "... = proper_Venn_region \<alpha>" by fastforce
    finally have "\<Squnion>HF (proper_Venn_region ` \<L> V y) = proper_Venn_region \<alpha>" .

    with \<open>\<A> y = \<Squnion>HF (proper_Venn_region ` (\<L> V y))\<close> \<open>\<alpha> \<in> ?l\<close> show ?thesis by auto
  qed
  moreover
  from \<open>\<A> y = HF {\<A> x}\<close> \<open>\<A> y = \<sigma>\<^bsub>x\<^esub>\<close> have "\<sigma>\<^bsub>x\<^esub> \<noteq> 0"
    by (metis finite.emptyI finite_insert hfset_0 hfset_HF insert_not_empty)
  ultimately
  show ?thesis
    by (metis Diff_iff \<Sigma>_def \<open>\<A> y = \<sigma>\<^bsub>x\<^esub>\<close> empty_iff imageI insert_iff)
qed

fun at\<^sub>p_f :: "'a \<Rightarrow> ('a \<Rightarrow> bool)" where
  "at\<^sub>p_f w = \<pi>\<^bsub>\<sigma>\<^bsub>w\<^esub>\<^esub>"

lemma range_at\<^sub>p_f: "w \<in> W \<Longrightarrow> at\<^sub>p_f w \<in> PI"
  using at\<^sub>p_f.simps containing_region_in_\<Sigma> PI_def by blast

lemma \<pi>_\<sigma>_\<alpha>:
  assumes "\<pi> \<in> PI"
    shows "\<exists>\<alpha> \<in> P\<^sup>+ V. \<pi> = (\<lambda>x. x \<in> \<alpha>) \<and> \<pi> = \<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> \<and> proper_Venn_region \<alpha> \<noteq> 0"
proof -
  from \<open>\<pi> \<in> PI\<close> obtain \<alpha> where \<alpha>:
    "\<pi> = \<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub>" "proper_Venn_region \<alpha> \<noteq> 0" "\<alpha> \<in> P\<^sup>+ V"
    by auto
  have "\<pi> x \<longleftrightarrow> x \<in> \<alpha>" for x
  proof (cases "x \<in> V")
    case True
    with \<alpha> proper_Venn_region_subset_variable_iff
    have "x \<in> \<alpha> \<longleftrightarrow> proper_Venn_region \<alpha> \<le> \<A> x" by simp
    with \<open>\<pi> = \<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub>\<close> True
    show ?thesis by simp
  next
    case False
    with \<open>\<pi> = \<pi>\<^bsub>(proper_Venn_region \<alpha>)\<^esub>\<close> have "\<not> \<pi> x" by auto
    from False \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "x \<notin> \<alpha>" by auto
    from \<open>\<not> \<pi> x\<close> \<open>x \<notin> \<alpha>\<close> show ?thesis by blast
  qed
  with \<alpha> show ?thesis by blast
qed

lemma \<pi>_\<sigma>_\<alpha>':
  assumes "\<sigma> \<in> \<Sigma>"
  shows "\<exists>\<alpha> \<in> P\<^sup>+ V. \<pi>\<^bsub>\<sigma>\<^esub> = (\<lambda>x. x \<in> \<alpha>) \<and> \<sigma> = proper_Venn_region \<alpha>"
proof -
  from \<open>\<sigma> \<in> \<Sigma>\<close> obtain \<alpha> where \<alpha>: "\<alpha> \<in> P\<^sup>+ V" "\<sigma> = proper_Venn_region \<alpha>" "proper_Venn_region \<alpha> \<noteq> 0"
    by auto
  have "\<pi>\<^bsub>\<sigma>\<^esub> x \<longleftrightarrow> x \<in> \<alpha>" for x
  proof (cases "x \<in> V")
    case True
    with \<alpha> proper_Venn_region_subset_variable_iff
    have "x \<in> \<alpha> \<longleftrightarrow> proper_Venn_region \<alpha> \<le> \<A> x" by simp
    with \<open>\<sigma> = proper_Venn_region \<alpha>\<close> True
    show ?thesis by simp
  next
    case False
    with \<open>\<sigma> = proper_Venn_region \<alpha>\<close> have "\<not> \<pi>\<^bsub>\<sigma>\<^esub> x" by auto
    from False \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "x \<notin> \<alpha>" by auto
    from \<open>\<not> \<pi>\<^bsub>\<sigma>\<^esub> x\<close> \<open>x \<notin> \<alpha>\<close> show ?thesis by blast
  qed
  with \<alpha> show ?thesis by blast
qed

lemma realise_same_implies_eq_under_all_\<pi>:
  assumes "x \<in> V"
      and "y \<in> V"
      and "\<A> x = \<A> y"
      and "\<pi> \<in> PI"
    shows "\<pi> x \<longleftrightarrow> \<pi> y"
  by (metis \<pi>_\<sigma>_\<alpha> assms associated_place.elims(2) associated_place.elims(3))

definition "rel_PI \<equiv> place_membership \<C> PI"
declare rel_PI_def [simp]

definition "G_PI \<equiv> place_mem_graph \<C> PI"
declare G_PI_def [simp]

lemma arcs_G_PI[simp]: "arcs G_PI = rel_PI" by simp
lemma arcs_ends_G_PI[simp]: "arcs_ends G_PI = rel_PI"
  unfolding arcs_ends_def arc_to_ends_def by auto
lemma verts_G_PI[simp]: "verts G_PI = PI" by simp

lemma rel_PI_head_tail:
  assumes "e \<in> rel_PI"
    shows "e = (tail G_PI e, head G_PI e)"
proof -
  from assms arcs_ends_G_PI have "e \<in> arcs_ends G_PI" 
    by blast
  then show ?thesis
    unfolding arcs_ends_def arc_to_ends_def
    by simp
qed

lemma place_membership_irreflexive: "(\<pi>, \<pi>) \<notin> rel_PI"
proof (rule ccontr)
  assume "\<not> (\<pi>, \<pi>) \<notin> rel_PI"
  then have "(\<pi>, \<pi>) \<in> rel_PI" by blast
  then obtain x y where xy: "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>" "\<pi> x" "\<pi> y" by auto
  with \<A>_sat_\<C> have "\<A> x = HF {\<A> y}" by fastforce
  then have "\<A> x \<sqinter> \<A> y = 0" by (simp add: hmem_not_refl)

  from \<open>(\<pi>, \<pi>) \<in> rel_PI\<close> have "\<pi> \<in> PI" by auto
  then obtain \<sigma> where \<sigma>: "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" "\<sigma> \<in> \<Sigma>" by auto
  then obtain \<alpha> where \<alpha>: "\<sigma> = proper_Venn_region \<alpha>" "\<alpha> \<in> P\<^sup>+ V" by auto
  with \<sigma> xy \<open>\<A> x \<sqinter> \<A> y = 0\<close>
  show False
    by (metis \<Sigma>_def DiffD2 associated_place.elims(2) insertCI le_inf_iff less_eq_hempty)
qed

interpretation pre_digraph G_PI .

lemma rel_PI_implies_rank_lt:
  assumes \<pi>_lt: "(\<pi>\<^bsub>\<sigma>\<^esub>, \<pi>\<^bsub>\<sigma>'\<^esub>) \<in> rel_PI"
      and "\<sigma> \<in> \<Sigma>"
      and "\<sigma>' \<in> \<Sigma>"
    shows "rank \<sigma> < rank \<sigma>'"
proof -
  from \<open>\<sigma>' \<in> \<Sigma>\<close> have "\<sigma>' \<noteq> 0" by auto

  from \<pi>_lt obtain x y where xy: "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>"
                         and "\<pi>\<^bsub>\<sigma>\<^esub> y" and "\<pi>\<^bsub>\<sigma>'\<^esub> x"
    by auto
  with \<A>_sat_\<C> have "\<A> x = HF {\<A> y}" by auto
  with \<open>\<pi>\<^bsub>\<sigma>'\<^esub> x\<close> \<open>\<sigma>' \<noteq> 0\<close> have "\<sigma>' = \<A> x"
    by (metis associated_place.simps singleton_nonempty_subset)
  then have "rank \<sigma>' = rank (\<A> x)" by blast
  moreover
  from \<open>\<pi>\<^bsub>\<sigma>\<^esub> y\<close> have "\<sigma> \<le> \<A> y" by simp
  then have "rank \<sigma> \<le> rank (\<A> y)"
    by (simp add: rank_mono) 
  moreover
  from \<open>\<A> x = HF {\<A> y}\<close> have "rank (\<A> y) < rank (\<A> x)"
    by (simp add: rank_lt)
  ultimately
  show ?thesis by order
qed

lemma awalk_in_G_PI_rank_lt:
  assumes "awalk \<pi>\<^bsub>\<sigma>\<^esub> p \<pi>\<^bsub>\<sigma>'\<^esub>"
      and "\<sigma> \<noteq> \<sigma>'"
      and "\<sigma> \<in> \<Sigma>"
      and "\<sigma>' \<in> \<Sigma>"
    shows "rank \<sigma> < rank \<sigma>'"
  using assms unfolding awalk_def
proof (induction "\<pi>\<^bsub>\<sigma>\<^esub>" p "\<pi>\<^bsub>\<sigma>'\<^esub>" arbitrary: \<sigma> \<sigma>' rule: cas.induct)
  case 1
  then have "\<pi>\<^bsub>\<sigma>\<^esub> = \<pi>\<^bsub>\<sigma>'\<^esub>" using cas.simps(1) by blast
  then have "\<sigma> = \<sigma>'"
    by (smt (verit) "1.prems"(3) "1.prems"(4) Collect_mem_eq \<pi>_\<sigma>_\<alpha>')
  with \<open>\<sigma> \<noteq> \<sigma>'\<close> have False by blast
  then show ?case ..
next
  case (2 e es)
  then have e_es_in_arcs: "set (e # es) \<subseteq> arcs G_PI"
                 and cas_e_es: "cas \<pi>\<^bsub>\<sigma>\<^esub> (e # es) \<pi>\<^bsub>\<sigma>'\<^esub>"
    by argo+
  from e_es_in_arcs have "e \<in> rel_PI"
    by (metis arcs_G_PI in_mono list.set_intros(1))
  then obtain \<pi>\<^sub>1 \<pi>\<^sub>2 where "e = (\<pi>\<^sub>1, \<pi>\<^sub>2)" "\<pi>\<^sub>1 \<in> PI" "\<pi>\<^sub>2 \<in> PI" by auto
  then have e_\<pi>12: "\<pi>\<^sub>1 = tail G_PI e" "\<pi>\<^sub>2 = head G_PI e" by simp+
  with cas_e_es have "\<pi>\<^sub>1 = \<pi>\<^bsub>\<sigma>\<^esub>" by (meson pre_digraph.cas.simps(2))
  from \<open>\<pi>\<^sub>2 \<in> PI\<close> obtain \<sigma>'' where "\<sigma>'' \<in> \<Sigma>" "\<pi>\<^sub>2 = \<pi>\<^bsub>\<sigma>''\<^esub>" by auto
  with cas_e_es e_\<pi>12 have "cas \<pi>\<^bsub>\<sigma>''\<^esub> es \<pi>\<^bsub>\<sigma>'\<^esub>"
    by (metis cas.simps(2))

  from \<open>\<pi>\<^sub>1 = \<pi>\<^bsub>\<sigma>\<^esub>\<close> \<open>\<pi>\<^sub>2 = \<pi>\<^bsub>\<sigma>''\<^esub>\<close> \<open>e = (\<pi>\<^sub>1, \<pi>\<^sub>2)\<close> have "e = (\<pi>\<^bsub>\<sigma>\<^esub>, \<pi>\<^bsub>\<sigma>''\<^esub>)"
    by simp
  with \<open>e \<in> rel_PI\<close> rel_PI_implies_rank_lt have "rank \<sigma> < rank \<sigma>''"
    using \<open>\<sigma> \<in> \<Sigma>\<close> \<open>\<sigma>'' \<in> \<Sigma>\<close> by blast

  show ?case
  proof (cases "\<sigma>'' = \<sigma>'")
    case True
    with \<open>rank \<sigma> < rank \<sigma>''\<close> show ?thesis by blast
  next
    case False
    with "2.hyps" have "rank \<sigma>'' < rank \<sigma>'"
      using "2.prems"(1) "2.prems"(4) \<open>\<pi>\<^sub>2 = \<pi>\<^bsub>\<sigma>''\<^esub>\<close> \<open>\<pi>\<^sub>2 \<in> PI\<close> \<open>\<sigma>'' \<in> \<Sigma>\<close> \<open>cas \<pi>\<^bsub>\<sigma>''\<^esub> es \<pi>\<^bsub>\<sigma>'\<^esub>\<close> e_\<pi>12(2)
      by (metis insert_subset list.simps(15) verts_G_PI)
    with \<open>rank \<sigma> < rank \<sigma>''\<close> show ?thesis by order
  qed
qed

lemma all_places_same_implies_assignment_equal:
  assumes "x \<in> V"
      and "y \<in> V"
      and \<pi>_eq: "\<forall>\<pi> \<in> PI. \<pi> x \<longleftrightarrow> \<pi> y"
    shows "\<A> x = \<A> y"
proof -
  let ?\<L>_x' = "{\<alpha> \<in> \<L> V x. proper_Venn_region \<alpha> \<noteq> 0}"
  let ?\<L>_y' = "{\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> \<noteq> 0}"

  have proper_Venn_region_\<L>_x': "proper_Venn_region ` ?\<L>_x' = {s \<in> proper_Venn_region ` \<L> V x. s \<noteq> 0}"
    by fast
  have proper_Venn_region_\<L>_y': "proper_Venn_region ` ?\<L>_y' = {s \<in> proper_Venn_region ` \<L> V y. s \<noteq> 0}"
    by fast

  from finite_V have "finite (\<L> V x)" by blast
  then have "finite (proper_Venn_region ` \<L> V x)" by blast
  from finite_V have "finite (\<L> V y)" by blast
  then have "finite (proper_Venn_region ` \<L> V y)" by blast

  have \<pi>_eq': "\<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> x = \<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> y"
    if "\<alpha> \<in> ?\<L>_x' \<or> \<alpha> \<in> ?\<L>_y'" for \<alpha>
  proof -
    from that have "x \<in> \<alpha> \<or> y \<in> \<alpha>" by fastforce
    from that have "\<alpha> \<in> P\<^sup>+ V" by fastforce
    with that have "\<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> \<in> PI" by fastforce
    with \<pi>_eq show ?thesis by fast
  qed

  have "?\<L>_x' = ?\<L>_y'"
  proof (standard; standard)
    fix \<alpha> assume "\<alpha> \<in> ?\<L>_x'"
    then have "x \<in> \<alpha>" by fastforce
    with \<open>\<alpha> \<in> ?\<L>_x'\<close> \<open>x \<in> V\<close> have "\<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> x"
      using proper_Venn_region_subset_variable_iff by auto
    with \<pi>_eq' \<open>\<alpha> \<in> ?\<L>_x'\<close> have "\<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> y" by blast
    with \<open>\<alpha> \<in> ?\<L>_x'\<close> \<open>y \<in> V\<close> have "y \<in> \<alpha>"
      using proper_Venn_region_subset_variable_iff by auto
    with \<open>\<alpha> \<in> ?\<L>_x'\<close> show "\<alpha> \<in> ?\<L>_y'" by fastforce
  next
    fix \<alpha> assume "\<alpha> \<in> ?\<L>_y'"
    then have "y \<in> \<alpha>" by fastforce
    with \<open>\<alpha> \<in> ?\<L>_y'\<close> \<open>y \<in> V\<close> have "\<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> y"
      using proper_Venn_region_subset_variable_iff by auto
    with \<pi>_eq' \<open>\<alpha> \<in> ?\<L>_y'\<close> have "\<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub> x" by blast
    with \<open>\<alpha> \<in> ?\<L>_y'\<close> \<open>x \<in> V\<close> have "x \<in> \<alpha>"
      using proper_Venn_region_subset_variable_iff by auto
    with \<open>\<alpha> \<in> ?\<L>_y'\<close> show "\<alpha> \<in> ?\<L>_x'" by fastforce
  qed

  from \<open>x \<in> V\<close> have "\<A> x = \<Squnion>HF (proper_Venn_region ` \<L> V x)"
    using variable_as_composition_of_proper_Venn_regions by presburger
  also have "... = \<Squnion>HF (proper_Venn_region ` ?\<L>_x')"
    using Hunion_nonempty[where ?S = "proper_Venn_region ` \<L> V x"]
    using \<open>finite (proper_Venn_region ` \<L> V x)\<close> proper_Venn_region_\<L>_x'
    by argo
  also have "... = \<Squnion>HF (proper_Venn_region ` ?\<L>_y')"
    using \<open>?\<L>_x' = ?\<L>_y'\<close> by argo
  also have "... = \<Squnion>HF (proper_Venn_region ` \<L> V y)"
    using Hunion_nonempty[where ?S = "proper_Venn_region ` \<L> V y"]
    using \<open>finite (proper_Venn_region ` \<L> V y)\<close> proper_Venn_region_\<L>_y'
    by argo
  also have "... = \<A> y"
    using \<open>y \<in> V\<close> variable_as_composition_of_proper_Venn_regions
    by presburger
  finally show "\<A> x = \<A> y" .
qed

definition "at\<^sub>p \<equiv> {(y, at\<^sub>p_f y)|y. y \<in> W}"
declare at\<^sub>p_def [simp]

(* Lemma 27 *)
theorem syntactic_description_is_adequate:
  "adequate_place_framework \<C> PI at\<^sub>p"
proof (unfold_locales, goal_cases)
  case 1
  then show ?case
  proof
    fix \<pi> assume "\<pi> \<in> PI"
    then obtain \<sigma> where "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" "\<sigma> \<in> \<Sigma>" by auto
    then obtain \<alpha> where "\<sigma> = proper_Venn_region \<alpha>" "\<alpha> \<in> P\<^sup>+ V" by auto
    with \<open>\<sigma> \<in> \<Sigma>\<close> have "\<sigma> \<noteq> 0" "proper_Venn_region \<alpha> \<noteq> 0" by auto
    from \<open>\<alpha> \<in> P\<^sup>+ V\<close> have "\<alpha> \<subseteq> V" by simp

    from proper_Venn_region_subset_variable_iff
    have \<alpha>_\<sigma>: "x \<in> \<alpha> \<longleftrightarrow> \<sigma> \<le> \<A> x" if "x \<in> V" for x
      using \<open>\<alpha> \<subseteq> V\<close> \<open>x \<in> V\<close> \<open>proper_Venn_region \<alpha> \<noteq> 0\<close> \<open>\<sigma> = proper_Venn_region \<alpha>\<close>
      by presburger

    from \<open>\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>\<close> \<open>\<sigma> = proper_Venn_region \<alpha>\<close> have "\<pi> = (\<lambda>x. x \<in> V \<and> proper_Venn_region \<alpha> \<le> \<A> x)"
      by (meson associated_place.elims(2) associated_place.elims(3))
    also have "... = (\<lambda>x. x \<in> \<alpha>)"
      using \<alpha>_\<sigma> \<open>\<alpha> \<subseteq> V\<close> \<open>\<sigma> = proper_Venn_region \<alpha>\<close> by (metis rev_contra_hsubsetD)
    also have "... \<in> places V"
      unfolding places_def using \<open>\<alpha> \<subseteq> V\<close> by blast
    finally show "\<pi> \<in> places V" .
  qed
next
  case 2
  then show ?case using at\<^sub>p_f.simps by auto
next
  case 3
  then show ?case using range_at\<^sub>p_f by fastforce
next
  case 4
  then show ?case by (simp add: single_valued_def)
next
  case (5 \<pi>)
  from place_membership_irreflexive show ?case by auto
next
  case (6 e)
  obtain \<pi> \<pi>' where "e = (\<pi>, \<pi>')" by fastforce
  with 6 have "\<pi> \<in> PI" by simp
  with \<open>e = (\<pi>, \<pi>')\<close> show ?case by simp
next
  case (7 e)
  obtain \<pi> \<pi>' where "e = (\<pi>, \<pi>')" by fastforce
  with 7 have "\<pi>' \<in> PI" by simp
  with \<open>e = (\<pi>, \<pi>')\<close> show ?case by simp
next
  case 8
  from finite_V have "finite \<Sigma>" by auto
  then show ?case by auto
next
  case 9
  from finite_V have "finite PI" by auto
  then have "finite (PI \<times> PI)" by auto
  moreover
  have "rel_PI \<subseteq> PI \<times> PI" by auto
  ultimately
  have "finite rel_PI" by (simp add: finite_subset) 
  then show ?case by auto
next
  case (10 e)
  then have "e \<in> rel_PI" by force
  with place_membership_irreflexive have "fst e \<noteq> snd e"
    by (metis prod.collapse)
  with rel_PI_head_tail show ?case by auto
next
  case (11 e\<^sub>1 e\<^sub>2)
  then show ?case
    unfolding arc_to_ends_def by simp
next
  case 12
  show ?case
  proof (rule ccontr)
    assume "\<not>(\<nexists>c. pre_digraph.cycle (place_mem_graph \<C> PI) c)"
    then obtain c where "cycle c"
      by fastforce
    then obtain e es \<pi> where e_es: "c = e # es" "awalk \<pi> (e # es) \<pi>"
      by (metis awalk_def cas.elims(2) cycle_def)
    then obtain \<pi>' where "e = (\<pi>, \<pi>')"
      by (metis arcs_G_PI awalk_def cas.simps(2) insert_subset list.simps(15) rel_PI_head_tail) 
    then show False
    proof (cases "es = []")
      case True
      with e_es have "e = (\<pi>, \<pi>)"
        by (metis arcs_G_PI awalk_def cas.simps(1) cas.simps(2) list.set_intros(1) rel_PI_head_tail subset_code(1))
      then have "(\<pi>, \<pi>) \<in> rel_PI"
        by (metis arcs_G_PI e_es(2) insert_subset list.simps(15) pre_digraph.awalk_def)
      with place_membership_irreflexive show False by blast
    next
      case False
      with e_es \<open>cycle c\<close> \<open>e = (\<pi>, \<pi>')\<close> have "\<pi>' \<noteq> \<pi>"
        by (metis arcs_G_PI awalk_def list.set_intros(1) place_membership_irreflexive subset_code(1))
      from e_es \<open>e = (\<pi>, \<pi>')\<close> have "\<pi> \<in> PI" "\<pi>' \<in> PI"
        unfolding awalk_def by simp+
      then obtain \<sigma> \<sigma>' where \<sigma>_\<sigma>': "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" "\<pi>' = \<pi>\<^bsub>\<sigma>'\<^esub>" "\<sigma> \<in> \<Sigma>" "\<sigma>' \<in> \<Sigma>" by auto
      from e_es \<open>e = (\<pi>, \<pi>')\<close> have "awalk \<pi>' es \<pi>"
        unfolding awalk_def
        by (metis Pair_inject \<open>\<pi>' \<in> PI\<close> arcs_G_PI cas.simps(2) insert_subset list.simps(15) rel_PI_head_tail verts_G_PI)
      with awalk_in_G_PI_rank_lt have "rank \<sigma>' < rank \<sigma>"
        using \<open>\<pi>' \<noteq> \<pi>\<close> \<sigma>_\<sigma>' by blast
      moreover
      from rel_PI_implies_rank_lt have "rank \<sigma> < rank \<sigma>'"
        using \<open>e = (\<pi>, \<pi>')\<close> \<sigma>_\<sigma>'
        by (metis e_es arcs_G_PI e_es(1) list.set_intros(1) pre_digraph.awalk_def subset_code(1))
      ultimately
      show False by simp
    qed
  qed
next
  case (13 x)
  with \<A>_sat_\<C> have "\<A> x = 0" by fastforce
  from 13 have "x \<in> V" by force
  have "\<not> \<pi> x" if "\<pi> \<in> PI" for \<pi>
  proof -
    from that obtain \<sigma> where "\<sigma> \<in> \<Sigma>" "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" by auto
    then have "\<pi> x \<longleftrightarrow> x \<in> V \<and> \<sigma> \<le> \<A> x" "\<sigma> \<noteq> 0" by simp+
    with \<open>x \<in> V\<close> have "\<pi> x \<longleftrightarrow> \<sigma> \<le> \<A> x" by argo
    with \<open>\<sigma> \<noteq> 0\<close> \<open>\<A> x = 0\<close> show "\<not> \<pi> x" by simp
  qed
  then show ?case unfolding PI_def by blast
next
  case (14 x y)
  with \<A>_sat_\<C> have "\<A> x = \<A> y" by fastforce
  from \<open>AT (Var x =\<^sub>s Var y) \<in> \<C>\<close> have "x \<in> V" "y \<in> V" by force+
  have "\<pi> x = \<pi> y" if "\<pi> \<in> PI" for \<pi>
  proof -
    from that obtain \<sigma> where "\<sigma> \<in> \<Sigma>" "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" by auto
    then have "\<pi> x \<longleftrightarrow> x \<in> V \<and> \<sigma> \<le> \<A> x" "\<pi> y \<longleftrightarrow> y \<in> V \<and> \<sigma> \<le> \<A> y" by simp+
    with \<open>x \<in> V\<close> \<open>y \<in> V\<close> have "\<pi> x \<longleftrightarrow> \<sigma> \<le> \<A> x" "\<pi> y \<longleftrightarrow> \<sigma> \<le> \<A> y" by argo+
    with \<open>\<A> x = \<A> y\<close> show "\<pi> x = \<pi> y" by simp
  qed
  then show ?case unfolding PI_def by blast
next
  case (15 x y z)
  with \<A>_sat_\<C> have "\<A> x = \<A> y \<squnion> \<A> z" by fastforce
  from 15 have "x \<in> V" "y \<in> V" "z \<in> V" by force+
  have "\<pi> x \<longleftrightarrow> \<pi> y \<or> \<pi> z" if "\<pi> \<in> PI" for \<pi>
  proof -
    from that \<pi>_\<sigma>_\<alpha> obtain \<alpha> where \<alpha>:
      "\<alpha> \<in> P\<^sup>+ V" "\<pi> = \<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub>" "\<pi> = (\<lambda>v. v \<in> \<alpha>)" "proper_Venn_region \<alpha> \<noteq> 0"
      by blast
    have "\<pi> y \<or> \<pi> z" if "\<pi> x"
    proof -
      from \<open>\<pi> x\<close> \<alpha> have "x \<in> \<alpha>" by metis
      from \<open>\<pi> x\<close> \<alpha> have "proper_Venn_region \<alpha> \<le> \<A> x" by simp
      with \<open>proper_Venn_region \<alpha> \<noteq> 0\<close> have "\<A> x \<noteq> 0" by fastforce
      {assume "y \<notin> \<alpha>" "z \<notin> \<alpha>"
        from \<open>y \<notin> \<alpha>\<close> \<open>y \<in> V\<close> have "\<A> y \<sqinter> proper_Venn_region \<alpha> = 0"
          using finite_V by fastforce
        moreover
        from \<open>z \<notin> \<alpha>\<close> \<open>z \<in> V\<close> have "\<A> z \<sqinter> proper_Venn_region \<alpha> = 0"
          using finite_V by fastforce
        ultimately
        have "\<A> x \<sqinter> proper_Venn_region \<alpha> = 0"
          using \<open>\<A> x = \<A> y \<squnion> \<A> z\<close> by simp
        from \<open>x \<in> \<alpha>\<close> have "proper_Venn_region \<alpha> \<le> \<A> x"
          using \<alpha> by (meson associated_place.elims(2))
        with \<open>\<A> x \<noteq> 0\<close> \<open>\<A> x \<sqinter> proper_Venn_region \<alpha> = 0\<close>
        have "proper_Venn_region \<alpha> = 0" by blast
        with \<open>proper_Venn_region \<alpha> \<noteq> 0\<close> have False by blast}
      then have "y \<in> \<alpha> \<or> z \<in> \<alpha>" by blast
      then show "\<pi> y \<or> \<pi> z" by (simp add: \<open>\<pi> = (\<lambda>v. v \<in> \<alpha>)\<close>) 
    qed
    have "\<pi> x" if "\<pi> y \<or> \<pi> z"
    proof -
      from \<open>\<pi> y \<or> \<pi> z\<close> \<alpha> have "proper_Venn_region \<alpha> \<le> \<A> y \<or> proper_Venn_region \<alpha> \<le> \<A> z"
        by auto
      with \<open>\<A> x = \<A> y \<squnion> \<A> z\<close> have "proper_Venn_region \<alpha> \<le> \<A> x" by auto
      with \<alpha> \<open>x \<in> V\<close> show "\<pi> x" by simp
    qed
    from \<open>\<pi> x \<Longrightarrow> \<pi> y \<or> \<pi> z\<close> \<open>\<pi> y \<or> \<pi> z \<Longrightarrow> \<pi> x\<close> 
    show ?thesis by blast
  qed
  then show ?case unfolding PI_def by blast
next
  case (16 x y z)
  with \<A>_sat_\<C> have "\<A> x = \<A> y - \<A> z" by fastforce
  from \<open>AT (Var x =\<^sub>s Var y -\<^sub>s Var z) \<in> \<C>\<close> have "x \<in> V" "y \<in> V" "z \<in> V" by force+
  have "\<pi> x \<longleftrightarrow> \<pi> y \<and> \<not> \<pi> z" if "\<pi> \<in> PI" for \<pi>
  proof -
    from that \<pi>_\<sigma>_\<alpha> obtain \<alpha> where \<alpha>:
      "\<alpha> \<in> P\<^sup>+ V" "\<pi> = \<pi>\<^bsub>proper_Venn_region \<alpha>\<^esub>" "\<pi> = (\<lambda>v. v \<in> \<alpha>)" "proper_Venn_region \<alpha> \<noteq> 0"
      by blast
    with finite_V have "finite \<alpha>" by blast
    have "\<pi> x" if "\<pi> y" "\<not> \<pi> z"
    proof -
      have "proper_Venn_region \<alpha> \<le> \<A> y"
        by (metis \<alpha>(2) associated_place.elims(2) \<open>\<pi> y\<close>)
      moreover
      from \<open>\<not> \<pi> z\<close> \<open>z \<in> V\<close> have "z \<in> V - \<alpha>"
        using \<alpha> by (metis DiffI) 
      then have "\<A> z \<le> \<Squnion>HF (\<A> ` (V - \<alpha>))"
        by (meson finite_Diff finite_V finite_imageI image_eqI mem_hsubset_HUnion)
      then have "\<A> z \<sqinter> proper_Venn_region \<alpha> = 0"
        by (simp add: hinter_hdiff_hempty)
      ultimately
      have "proper_Venn_region \<alpha> \<le> \<A> y - \<A> z" by blast
      with \<open>\<A> x = \<A> y - \<A> z\<close> have "proper_Venn_region \<alpha> \<le> \<A> x" by argo
      with \<alpha> \<open>x \<in> V\<close> show ?thesis by auto
    qed
    have "\<pi> y \<and> \<not> \<pi> z" if "\<pi> x"
    proof -
      from \<open>\<pi> x\<close> \<alpha> have "proper_Venn_region \<alpha> \<le> \<A> x"
        by auto
      with \<open>\<A> x = \<A> y - \<A> z\<close> have "proper_Venn_region \<alpha> \<le> \<A> y" "\<not> proper_Venn_region \<alpha> \<le> \<A> z"
        apply simp_all
         apply auto[1]
        by (metis (no_types, lifting) \<alpha>(4) hdiff_iff hdisjoint_iff inf.orderE proper_Venn_region.elims rev_hsubsetD)
      with \<alpha> \<open>y \<in> V\<close> \<open>z \<in> V\<close> show "\<pi> y \<and> \<not> \<pi> z" by simp
    qed
    from \<open>\<pi> x \<Longrightarrow> \<pi> y \<and> \<not> \<pi> z\<close> \<open>\<pi> y \<Longrightarrow> \<not> \<pi> z \<Longrightarrow> \<pi> x\<close> 
    show ?thesis by blast
  qed
  then show ?case unfolding PI_def by blast
next
  case (17 x y)
  with \<A>_sat_\<C> have "\<A> x \<noteq> \<A> y" by fastforce
  from 17 have "x \<in> V" "y \<in> V" by fastforce+
  with \<open>\<A> x \<noteq> \<A> y\<close> all_places_same_implies_assignment_equal
  show ?case by metis
next
  case (18 x y)
  then have "y \<in> W" by fastforce
  from 18 have "x \<in> V" "y \<in> V" by fastforce+
  from 18 \<A>_sat_\<C> have "\<A> x = HF{\<A> y}" by fastforce
  then have "\<sigma>\<^bsub>y\<^esub> \<le> \<A> x" by simp
  with \<open>x \<in> V\<close> have "at\<^sub>p_f y x" by (simp only: at\<^sub>p_f.simps) simp
  moreover
  {fix \<pi> assume "\<pi> \<in> PI" "\<pi> x"
    then obtain \<sigma> where "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" "\<sigma> \<le> \<A> x" "\<sigma> \<noteq> 0" by fastforce
    with \<open>\<A> x = HF{\<A> y}\<close> have "\<sigma> = HF{\<A> y}" by fastforce
    with \<open>\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>\<close> have "\<pi> = at\<^sub>p_f y" by simp
  }
  then have "\<forall>\<pi>'\<in>PI. \<pi>' \<noteq> at\<^sub>p_f y \<longrightarrow> \<not> \<pi>' x"
    by blast
  ultimately
  show ?case using \<open>y \<in> W\<close> by simp
next
  case (19 y z)
  then obtain \<pi> where "\<pi> = at\<^sub>p_f z" "\<pi> = at\<^sub>p_f y" by simp
  then have "at\<^sub>p_f z = at\<^sub>p_f y" by blast
  from \<open>y \<in> W\<close> obtain x where x: "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>"
    using memW_E by blast
  with \<A>_sat_\<C> have "\<A> x = HF{\<A> y}" by fastforce
  from 19 x have "x \<in> V" "y \<in> V" by fastforce+
  from 19 have "z \<in> V" using W_subset_V by blast

  from \<open>\<A> x = HF{\<A> y}\<close> have "\<sigma>\<^bsub>y\<^esub> \<le> \<A> x" by simp
  with \<open>x \<in> V\<close> have "at\<^sub>p_f y x" by auto
  with \<open>at\<^sub>p_f z = at\<^sub>p_f y\<close> have "at\<^sub>p_f z x" by argo
  then have "\<sigma>\<^bsub>z\<^esub> \<le> \<A> x" by simp
  with \<open>\<A> x = HF{\<A> y}\<close> have "\<sigma>\<^bsub>z\<^esub> = HF{\<A> y}" by force
  then have "\<A> z = \<A> y"
    by (metis finite.emptyI finite_insert hfset_HF containing_region.elims singleton_insert_inj_eq)

  {fix \<pi> assume "\<pi> \<in> PI"
    then obtain \<sigma> where "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" "\<sigma> \<noteq> 0" by auto
    with \<open>y \<in> V\<close> have "\<pi> y \<longleftrightarrow> \<sigma> \<le> \<A> y" by fastforce
    also have "... \<longleftrightarrow> \<sigma> \<le> \<A> z"
      using \<open>\<A> z = \<A> y\<close> by auto
    also have "... \<longleftrightarrow> \<pi> z"
      using \<open>\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>\<close> \<open>z \<in> V\<close> by simp
    finally have "\<pi> y = \<pi> z" .
  }
  then show ?case by blast
next
  case (20 y y')
  then have "y \<in> V" "y' \<in> V" by (metis W_subset_V subsetD)+
  with \<open>\<forall>\<pi>\<in>PI. \<pi> y' = \<pi> y\<close> all_places_same_implies_assignment_equal
  have "\<A> y = \<A> y'" by presburger
  then have "at\<^sub>p_f y = at\<^sub>p_f y'" by simp
  with \<open>y \<in> W\<close> \<open>y' \<in> W\<close> show ?case by simp
next
  case (21 \<pi>\<^sub>1 \<pi>\<^sub>2)
  have "\<pi> = \<pi>\<^bsub>HF {0}\<^esub>" if "\<pi> \<in> Range at\<^sub>p - Range (place_membership \<C> PI)" for \<pi>
  proof -
    from that obtain y where y: "y \<in> W" "at\<^sub>p_f y = \<pi>"
    by (simp only: at\<^sub>p_def) blast
    with range_at\<^sub>p_f have "\<pi> \<in> PI" by blast
    from \<open>y \<in> W\<close> obtain x where lt_in_\<C>:
      "AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>"
      using memW_E by presburger
    with \<A>_sat_\<C> have "\<A> x = HF {\<A> y}" by fastforce
    then have "\<sigma>\<^bsub>y\<^esub> \<le> \<A> x" by simp
    with lt_in_\<C> have "at\<^sub>p_f y x" by force
    with \<open>at\<^sub>p_f y = \<pi>\<close> have "\<pi> x" by blast
  
    have "\<forall>\<pi> \<in> PI. \<not> \<pi> y"
    proof (rule ccontr)
      assume "\<not> (\<forall>\<pi>\<in>PI. \<not> \<pi> y)"
      then obtain \<pi>' where "\<pi>' \<in> PI" "\<pi>' y" by blast
      with \<open>AT (Var x =\<^sub>s Single (Var y)) \<in> \<C>\<close> \<open>\<pi> x\<close>
      have "(\<pi>', \<pi>) \<in> place_membership \<C> PI"
        using \<open>\<pi> \<in> PI\<close>
        by (simp only: place_membership.simps) blast
      then have "\<pi> \<in> Range (place_membership \<C> PI)" by blast
      with that show False by blast
    qed
    have "\<forall>\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0"
    proof (rule ccontr)
      assume "\<not> (\<forall>\<alpha> \<in> \<L> V y. proper_Venn_region \<alpha> = 0)"
      then obtain \<alpha> where \<alpha>: "\<alpha> \<in> \<L> V y" "proper_Venn_region \<alpha> \<noteq> 0" by blast
      then have "proper_Venn_region \<alpha> \<le> \<A> y"
        using variable_as_composition_of_proper_Venn_regions \<L>_finite finite_V
        by (smt (verit, ccfv_threshold) W_subset_V finite_imageI image_eqI mem_hsubset_HUnion subset_iff y(1))
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

    from \<open>\<pi> \<in> PI\<close> obtain \<sigma> where "\<sigma> \<in> \<Sigma>" "\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>" by auto
    with \<open>\<pi> x\<close> have "\<sigma> \<noteq> 0" "\<sigma> \<le> \<A> x" by simp+
    with \<open>\<A> x = HF {0}\<close> have "\<sigma> = HF {0}" by fastforce
    with \<open>\<pi> = \<pi>\<^bsub>\<sigma>\<^esub>\<close> show "\<pi> = \<pi>\<^bsub>HF {0}\<^esub>" by blast
  qed
  with 21 show ?case by blast
qed

end

end