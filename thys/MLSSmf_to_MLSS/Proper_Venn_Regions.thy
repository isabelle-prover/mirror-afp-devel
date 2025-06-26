theory Proper_Venn_Regions
  imports MLSSmf_Semantics MLSSmf_to_MLSS MLSSmf_HF_Extras
begin

locale proper_Venn_regions =
    fixes V :: "'a set"
      and \<A> :: "'a \<Rightarrow> hf"
  assumes finite_V: "finite V"
begin

fun proper_Venn_region :: "'a set \<Rightarrow> hf" where
  "proper_Venn_region \<alpha> = \<Sqinter>HF (\<A> ` \<alpha>) - \<Squnion>HF (\<A> ` (V - \<alpha>))"

lemma proper_Venn_region_nonempty_iff[iff]:
  "c \<^bold>\<in> proper_Venn_region \<alpha> \<and> \<alpha> \<subseteq> V \<longleftrightarrow> \<alpha> = {x \<in> V. c \<^bold>\<in> \<A> x} \<and> \<alpha> \<noteq> {}"
proof(standard, goal_cases)
  case 1
  then have "c \<^bold>\<in> proper_Venn_region \<alpha>" "\<alpha> \<subseteq> V" by blast+
  show ?case
  proof(standard, standard, goal_cases)
    case 1
    then show ?case
    proof
      fix x assume "x \<in> \<alpha>"
      have "c \<^bold>\<in> \<Sqinter>HF (\<A> ` \<alpha>)"
        using \<open>c \<^bold>\<in> proper_Venn_region \<alpha>\<close> by auto
      then have "c \<^bold>\<in> \<A> x"
        using \<open>x \<in> \<alpha>\<close>
        by (metis (mono_tags, opaque_lifting) HInter_hempty HInter_iff hempty_iff hmem_HF_iff imageI)
      then show "x \<in> {x \<in> V. c \<^bold>\<in> \<A> x}"
        using \<open>\<alpha> \<subseteq> V\<close> \<open>x \<in> \<alpha>\<close> by blast
    qed
  next
    case 2
    then show ?case
    proof
      fix x assume "x \<in> {x \<in> V. c \<^bold>\<in> \<A> x}"
      then have "x \<in> V" "c \<^bold>\<in> \<A> x" by blast+
      show "x \<in> \<alpha>"
      proof (rule ccontr)
        assume "x \<notin> \<alpha>"
        then have "x \<in> V - \<alpha>"
          using \<open>\<alpha> \<subseteq> V\<close> \<open>x \<in> V\<close> by blast
        then have "c \<^bold>\<in> \<Squnion>HF (\<A> ` (V - \<alpha>))"
          using \<open>c \<^bold>\<in> \<A> x\<close> finite_V by auto
        then have "c \<^bold>\<notin> proper_Venn_region \<alpha>" by simp
        then show False
          using \<open>c \<^bold>\<in> proper_Venn_region \<alpha>\<close> by blast
      qed
    qed
  next
    case 3
    then show ?case
    proof (rule ccontr)
      assume "\<not> \<alpha> \<noteq> {}"
      then have "\<alpha> = {}" by fast
      then have "proper_Venn_region \<alpha> = 0"
        using Zero_hf_def by auto
      then show False
        using \<open>c \<^bold>\<in> proper_Venn_region \<alpha>\<close> by simp
    qed
  qed
next
  case 2
  then have "\<alpha> = {x \<in> V. c \<^bold>\<in> \<A> x}" "\<alpha> \<noteq> {}" by simp+
  then have "\<alpha> \<subseteq> V" by blast
  moreover
  from 2 finite_V have "finite \<alpha>" by force
  then have "finite (\<A> ` \<alpha>)" by blast
  then have "finite (\<A> ` (V - \<alpha>))"
    using finite_V by fast
  from \<open>\<alpha> \<noteq> {}\<close> have "\<A> ` \<alpha> \<noteq> {}" by blast
  from 2 have "\<forall>x \<in> \<alpha>. c \<^bold>\<in> \<A> x" by simp
  then have "\<forall>x \<in> \<A> ` \<alpha>. c \<^bold>\<in> x" by blast
  then have "c \<^bold>\<in> \<Sqinter>HF (\<A> ` \<alpha>)"
    using \<open>finite (\<A> ` \<alpha>)\<close> \<open>\<A> ` \<alpha> \<noteq> {}\<close>
    by (metis HInter_iff hfset_0 hfset_HF hmem_HF_iff)
  moreover
  have "c \<^bold>\<notin> \<Squnion>HF (\<A> ` (V - \<alpha>))"
  proof
    assume "c \<^bold>\<in> \<Squnion>HF (\<A> ` (V - \<alpha>))"
    then obtain x where "c \<^bold>\<in> x" "x \<in> \<A> ` (V - \<alpha>)" by auto
    then have "x \<in> \<A> ` (V) - \<A> ` \<alpha>"
      using 2 by fastforce
    then have "x \<notin> \<A> ` \<alpha>" by blast
    then show False
      using \<open>c \<^bold>\<in> x\<close> 2 \<open>x \<in> \<A> ` (V - \<alpha>)\<close> by blast 
  qed
  ultimately show ?case by auto
qed

lemma proper_Venn_region_strongly_injective:
  assumes "proper_Venn_region \<alpha> \<sqinter> proper_Venn_region \<beta> \<noteq> 0"
      and "\<alpha> \<subseteq> V"
      and "\<beta> \<subseteq> V"
    shows "\<alpha> = \<beta>"
proof -
  from \<open>proper_Venn_region \<alpha> \<sqinter> proper_Venn_region \<beta> \<noteq> 0\<close>
  obtain c where c: "c \<^bold>\<in> proper_Venn_region \<alpha>" "c \<^bold>\<in> proper_Venn_region \<beta>"
    by blast
  then have "\<alpha> = {x \<in> V. c \<^bold>\<in> \<A> x}" "\<beta> = {x \<in> V. c \<^bold>\<in> \<A> x}"
    using \<open>\<alpha> \<subseteq> V\<close> \<open>\<beta> \<subseteq> V\<close>
    using proper_Venn_region_nonempty_iff by (metis (mono_tags, lifting))+
  then show "\<alpha> = \<beta>" by presburger
qed

lemma proper_Venn_region_disjoint:
  "\<alpha> \<noteq> \<beta> \<Longrightarrow> \<alpha> \<subseteq> V \<Longrightarrow> \<beta> \<subseteq> V \<Longrightarrow> proper_Venn_region \<alpha> \<sqinter> proper_Venn_region \<beta> = 0"
  using proper_Venn_region_strongly_injective by meson

lemma HUnion_proper_Venn_region_union:
  assumes "l \<subseteq> P\<^sup>+ V"
      and "m \<subseteq> P\<^sup>+ V"
    shows "\<Squnion>HF (proper_Venn_region ` (l \<union> m)) = \<Squnion>HF (proper_Venn_region ` l) \<squnion> \<Squnion>HF(proper_Venn_region ` m)"
  by (metis HUnion_hunion P_plus_finite assms(1) assms(2) finite_V finite_imageI finite_subset image_Un union_hunion)

lemma HUnion_proper_Venn_region_inter:
  assumes "l \<subseteq> P\<^sup>+ V"
      and "m \<subseteq> P\<^sup>+ V"
    shows "\<Squnion>HF (proper_Venn_region ` (l \<inter> m)) = \<Squnion>HF (proper_Venn_region ` l) \<sqinter> \<Squnion>HF(proper_Venn_region ` m)"
proof -
  from \<open>l \<subseteq> P\<^sup>+ V\<close> have "finite l"
    using finite_V P_plus_finite by (metis finite_subset)
  from \<open>m \<subseteq> P\<^sup>+ V\<close> have "finite m"
    using finite_V P_plus_finite by (metis finite_subset)
  
  have "\<Squnion>HF (proper_Venn_region ` (l \<inter> m)) \<le> \<Squnion>HF (proper_Venn_region ` l) \<sqinter> \<Squnion>HF (proper_Venn_region ` m)"
    using proper_Venn_region_disjoint \<open>finite l\<close> \<open>finite m\<close>
    by auto
  moreover
  have "c \<^bold>\<in> \<Squnion>HF (proper_Venn_region ` (l \<inter> m))" if "c \<^bold>\<in> \<Squnion>HF (proper_Venn_region ` l) \<sqinter> \<Squnion>HF (proper_Venn_region ` m)" for c
  proof -
    from that have "c \<^bold>\<in> \<Squnion>HF (proper_Venn_region ` l)" "c \<^bold>\<in> \<Squnion>HF (proper_Venn_region ` m)" by blast+
    then obtain \<alpha> \<beta> where "\<alpha> \<in> l" "\<beta> \<in> m" and c_mem: "c \<^bold>\<in> proper_Venn_region \<alpha>" "c \<^bold>\<in> proper_Venn_region \<beta>" by auto
    with \<open>l \<subseteq> P\<^sup>+ V\<close> \<open>m \<subseteq> P\<^sup>+ V\<close> finite_V have "\<alpha> \<subseteq> V" "\<beta> \<subseteq> V" by auto
    with proper_Venn_region_strongly_injective c_mem have "\<alpha> = \<beta>" by blast
    with \<open>\<alpha> \<in> l\<close> \<open>\<beta> \<in> m\<close> have "\<alpha> \<in> l \<inter> m" by blast
    with c_mem show ?thesis
      using HUnion_iff \<open>finite l\<close> hmem_def by auto 
  qed
  then have "\<Squnion>HF (proper_Venn_region ` l) \<sqinter> \<Squnion>HF (proper_Venn_region ` m) \<le> \<Squnion>HF (proper_Venn_region ` (l \<inter> m))" by blast
  ultimately show ?thesis by order
qed

text \<open>\<Union>_{\<alpha>\<in>L_y} v_\<alpha> = y\<close>
lemma variable_as_composition_of_proper_Venn_regions:
  assumes "y \<in> V"
    shows "\<Squnion>HF (proper_Venn_region ` \<L> V y) = \<A> y"
proof(standard; standard)
  fix c assume c: "c \<^bold>\<in> \<Squnion>HF (proper_Venn_region ` (\<L> V y))"
  then obtain \<alpha> where \<alpha>: "\<alpha> \<in> \<L> V y" "c \<^bold>\<in> proper_Venn_region \<alpha>"
    by auto
  then have "y \<in> \<alpha>" using \<open>y \<in> V\<close> by fastforce
  then have "\<A> y \<in> \<A> ` \<alpha>" by blast
  from finite_V \<open>\<alpha> \<in> \<L> V y\<close> \<open>y \<in> V\<close> have "finite \<alpha>" "\<alpha> \<noteq> {}" by auto
  then have "finite (\<A> ` \<alpha>)" "\<A> ` \<alpha> \<noteq> {}" by simp+
  with \<open>\<A> y \<in> \<A> ` \<alpha>\<close> have "\<Sqinter>(HF (\<A> ` \<alpha>)) \<le> \<A> y"
    by (metis HInter_iff hfset_0 hfset_HF hmem_HF_iff hsubsetI)
  then show "c \<^bold>\<in> \<A> y"
    using \<alpha> by fastforce
next
  fix c assume "c \<^bold>\<in> \<A> y"
  let ?\<alpha> = "{x \<in> V. c \<^bold>\<in> \<A> x}"
  from \<open>c \<^bold>\<in> \<A> y\<close> \<open>y \<in> V\<close> have "y \<in> ?\<alpha>" by blast
  then have "?\<alpha> \<in> \<L> V y" by auto
  then have "?\<alpha> \<noteq> {}" by auto
  then have "c \<^bold>\<in> proper_Venn_region ?\<alpha>"
    using proper_Venn_region_nonempty_iff
    by (metis (mono_tags, lifting))
  moreover
  from \<open>?\<alpha> \<in> \<L> V y\<close> have "proper_Venn_region ?\<alpha> \<in> proper_Venn_region ` \<L> V y" by fast
  moreover
  have "finite (\<L> V y)" using finite_V by simp
  ultimately
  show "c \<^bold>\<in> \<Squnion>HF (proper_Venn_region ` (\<L> V y))"
    by (smt (verit, best) HUnion_iff finite_imageI hmem_HF_iff)
qed

lemma proper_Venn_region_subset_variable_iff:
  assumes "\<alpha> \<subseteq> V"
      and "x \<in> V"
      and "proper_Venn_region \<alpha> \<noteq> 0"
    shows "x \<in> \<alpha> \<longleftrightarrow> proper_Venn_region \<alpha> \<le> \<A> x"
proof
  assume "x \<in> \<alpha>"
  then have "\<Sqinter>HF (\<A> ` \<alpha>) \<le> \<A> x" using \<open>\<alpha> \<subseteq> V\<close> finite_V
    by (smt (verit, ccfv_SIG) HInter_iff ball_imageD finite_imageI hemptyE hmem_HF_iff hsubsetI rev_finite_subset)
  then show "proper_Venn_region \<alpha> \<le> \<A> x" by auto
next
  assume "proper_Venn_region \<alpha> \<le> \<A> x"
  moreover
  from variable_as_composition_of_proper_Venn_regions \<open>x \<in> V\<close>
  have "\<A> x = \<Squnion>HF (proper_Venn_region ` \<L> V x)"
    by presburger
  ultimately
  have "proper_Venn_region \<alpha> \<le> \<Squnion>HF (proper_Venn_region ` \<L> V x)"
    by argo
  show "x \<in> \<alpha>"
  proof (rule ccontr)
    assume "x \<notin> \<alpha>"
    then have "\<alpha> \<notin> \<L> V x" by simp
    moreover
    from \<open>proper_Venn_region \<alpha> \<le> \<Squnion>HF (proper_Venn_region ` \<L> V x)\<close> \<open>proper_Venn_region \<alpha> \<noteq> 0\<close>
    have "proper_Venn_region \<alpha> \<sqinter> \<Squnion>HF (proper_Venn_region ` \<L> V x) \<noteq> 0" by fast
    then obtain \<beta> where "\<beta> \<in> \<L> V x" "proper_Venn_region \<alpha> \<sqinter> proper_Venn_region \<beta> \<noteq> 0"
      by auto
    with proper_Venn_region_strongly_injective have "\<alpha> = \<beta>"
      using \<open>\<beta> \<in> \<L> V x\<close> \<open>\<alpha> \<subseteq> V\<close> by auto
    with \<open>\<beta> \<in> \<L> V x\<close> have "\<alpha> \<in> \<L> V x" by blast
    ultimately
    show False by blast
  qed
qed

end

end