\<^marker>\<open>creator "Niklas Krofta"\<close>
section \<open>Uniform spaces\<close>
theory Uniform_Structure
  imports "HOL-Analysis.Abstract_Topology" "HOL-Analysis.Abstract_Metric_Spaces"
begin

paragraph \<open>Summary\<close>
text \<open>
  This section introduces a set-based notion of uniformities and connects it to the
  @{class "uniform_space"} type class.
\<close>

subsection \<open>Definitions and basic results\<close>

definition uniformity_on :: "'a set \<Rightarrow> (('a \<times> 'a) set \<Rightarrow> bool) \<Rightarrow> bool" where
"uniformity_on X \<E> \<longleftrightarrow> 
  (\<exists>E. \<E> E) \<and> 
  (\<forall>E. \<E> E \<longrightarrow> E \<subseteq> X \<times> X \<and> Id_on X \<subseteq> E \<and> \<E> (E\<inverse>) \<and> (\<exists>F. \<E> F \<and> F O F \<subseteq> E) \<and> 
    (\<forall>F. E \<subseteq> F \<and> F \<subseteq> X \<times> X \<longrightarrow> \<E> F)) \<and>
  (\<forall>E F. \<E> E \<longrightarrow> \<E> F \<longrightarrow> \<E> (E \<inter> F))"

typedef 'a uniformity = "{(X :: 'a set, \<E>). uniformity_on X \<E>}"
  morphisms uniformity_rep uniformity
proof -
  have "uniformity_on UNIV (\<lambda>E. E = UNIV \<times> UNIV)" 
    unfolding uniformity_on_def Id_on_def relcomp_def by auto
  then show ?thesis by fast
qed

definition uspace :: "'a uniformity \<Rightarrow> 'a set" where
"uspace \<Phi> = (let (X, \<E>) = uniformity_rep \<Phi> in X)"

definition entourage_in :: "'a uniformity \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
"entourage_in \<Phi> = (let (X, \<E>) = uniformity_rep \<Phi> in \<E>)"

lemma uniformity_inverse'[simp]:
  assumes "uniformity_on X \<E>"
  shows "uspace (uniformity (X, \<E>)) = X \<and> entourage_in (uniformity (X, \<E>)) = \<E>"
proof -
  from assms have "uniformity_rep (uniformity (X, \<E>)) = (X, \<E>)" 
    using uniformity_inverse by blast
  then show ?thesis by (auto simp: prod.splits uspace_def entourage_in_def)
qed

lemma uniformity_entourages:
  shows "uniformity_on (uspace \<Phi>) (entourage_in \<Phi>)"
  by (metis Product_Type.Collect_case_prodD entourage_in_def split_beta uspace_def uniformity_rep)

lemma entourages_exist: "\<exists>E. entourage_in \<Phi> E"
  using uniformity_entourages unfolding uniformity_on_def by blast

lemma entourage_in_space[elim]: "entourage_in \<Phi> E \<Longrightarrow> E \<subseteq> uspace \<Phi> \<times> uspace \<Phi>"
  using uniformity_entourages unfolding uniformity_on_def by metis

lemma entourage_superset[intro]: 
  "entourage_in \<Phi> E \<Longrightarrow> E \<subseteq> F \<Longrightarrow> F \<subseteq> uspace \<Phi> \<times> uspace \<Phi> \<Longrightarrow> entourage_in \<Phi> F"
  using uniformity_entourages unfolding uniformity_on_def by blast

lemma entourage_intersection[intro]: "entourage_in \<Phi> E \<Longrightarrow> entourage_in \<Phi> F \<Longrightarrow> entourage_in \<Phi> (E \<inter> F)"
  using uniformity_entourages unfolding uniformity_on_def by metis

lemma entourage_converse[intro]: "entourage_in \<Phi> E \<Longrightarrow> entourage_in \<Phi> (E\<inverse>)"
  using uniformity_entourages unfolding uniformity_on_def by fast

lemma entourage_diagonal[dest]:
  assumes entourage: "entourage_in \<Phi> E" and in_space: "x \<in> uspace \<Phi>"
  shows "(x,x) \<in> E"
proof -
  have "Id_on (uspace \<Phi>) \<subseteq> E" 
    using uniformity_entourages entourage unfolding uniformity_on_def by fast
  then show ?thesis using Id_onI[OF in_space] by blast
qed

lemma smaller_entourage:
  assumes entourage: "entourage_in \<Phi> E"
  shows "\<exists>F. entourage_in \<Phi> F \<and> (\<forall>x y z. (x,y) \<in> F \<and> (y,z) \<in> F \<longrightarrow> (x,z) \<in> E)"
proof -
  from entourage obtain F where "entourage_in \<Phi> F \<and> F O F \<subseteq> E"
    using uniformity_entourages entourage unfolding uniformity_on_def by meson
  moreover from this have "(x,z) \<in> E" if "(x,y) \<in> F \<and> (y,z) \<in> F" for x y z using that by blast
  ultimately show ?thesis by blast
qed

lemma entire_space_entourage: "entourage_in \<Phi> (uspace \<Phi> \<times> uspace \<Phi>)"
  by (metis entourages_exist entourage_in_space entourage_superset subset_refl)

definition utopology :: "'a uniformity \<Rightarrow> 'a topology" where
"utopology \<Phi> = topology (\<lambda>U. U \<subseteq> uspace \<Phi> \<and> (\<forall>x\<in>U. \<exists>E. entourage_in \<Phi> E \<and> E``{x} \<subseteq> U))"

lemma openin_utopology [iff]:
  fixes \<Phi> :: "'a uniformity"
  defines "uopen U \<equiv> U \<subseteq> uspace \<Phi> \<and> (\<forall>x\<in>U. \<exists>E. entourage_in \<Phi> E \<and> E``{x} \<subseteq> U)"
  shows "openin (utopology \<Phi>) = uopen"
proof -
  have "uopen (U \<inter> V)" if hUV: "uopen U \<and> uopen V" for U V
  proof -
    have "\<exists>E. entourage_in \<Phi> E \<and> E``{x} \<subseteq> U \<inter> V" if hx: "x \<in> U \<inter> V" for x 
    proof -
      from hUV hx obtain E\<^sub>1 E\<^sub>2 where 
        "entourage_in \<Phi> E\<^sub>1 \<and> entourage_in \<Phi> E\<^sub>2 \<and> E\<^sub>1``{x} \<subseteq> U \<and> E\<^sub>2``{x} \<subseteq> V" unfolding uopen_def by blast
      then have "entourage_in \<Phi> (E\<^sub>1 \<inter> E\<^sub>2) \<and> (E\<^sub>1 \<inter> E\<^sub>2)``{x} \<subseteq> U \<inter> V" by blast
      then show ?thesis by fast
    qed
    then show ?thesis using le_infI1 hUV unfolding uopen_def by auto
  qed
  moreover have "uopen (\<Union>\<U>)" if h\<U>: "\<forall>U\<in>\<U>. uopen U" for \<U>
  proof -
    have "\<exists>E. entourage_in \<Phi> E \<and> E``{x} \<subseteq> \<Union>\<U>" if hx: "x \<in> \<Union>\<U>" for x
    proof -
      from hx obtain U where hU: "U \<in> \<U> \<and> x \<in> U" by blast
      from this h\<U> obtain E where "entourage_in \<Phi> E \<and> E``{x} \<subseteq> U" unfolding uopen_def by fast
      moreover from this hU have "E``{x} \<subseteq> \<Union>\<U>" by fast
      ultimately show ?thesis by blast
    qed
    then show ?thesis using Union_least h\<U> unfolding uopen_def by auto
  qed
  ultimately have "istopology uopen" unfolding istopology_def by presburger
  from topology_inverse'[OF this] show ?thesis unfolding utopology_def uopen_def by blast
qed

lemma topspace_utopology[simp]:
  shows "topspace (utopology \<Phi>) = uspace \<Phi>"
proof -
  let ?T = "utopology \<Phi>"
  have "topspace ?T \<subseteq> uspace \<Phi>"
    using openin_topspace openin_utopology by meson
  moreover have "openin ?T (uspace \<Phi>)" 
    unfolding openin_utopology by (auto intro: entire_space_entourage)
  ultimately show ?thesis using topspace_def by fast
qed

definition ucontinuous :: "'a uniformity \<Rightarrow> 'b uniformity \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"ucontinuous \<Phi> \<Psi> f \<longleftrightarrow> 
  f \<in> uspace \<Phi> \<rightarrow> uspace \<Psi> \<and>
  (\<forall>E. entourage_in \<Psi> E \<longrightarrow> entourage_in \<Phi> {(x, y) \<in> uspace \<Phi> \<times> uspace \<Phi>. (f x, f y) \<in> E})"

lemma ucontinuous_image_subset [dest]: "ucontinuous \<Phi> \<Psi> f \<Longrightarrow> f`(uspace \<Phi>) \<subseteq> uspace \<Psi>"
  unfolding ucontinuous_def by blast

lemma entourage_preimage_ucontinuous [dest]: 
  assumes "ucontinuous \<Phi> \<Psi> f" and "entourage_in \<Psi> E" 
  shows "entourage_in \<Phi> {(x, y) \<in> uspace \<Phi> \<times> uspace \<Phi>. (f x, f y) \<in> E}"
  using assms unfolding ucontinuous_def by blast

lemma ucontinuous_imp_continuous:
  assumes "ucontinuous \<Phi> \<Psi> f"
  shows "continuous_map (utopology \<Phi>) (utopology \<Psi>) f"
proof (unfold continuous_map_def, intro conjI allI impI)
  show "f \<in> topspace (utopology \<Phi>) \<rightarrow> topspace (utopology \<Psi>)"
    using assms unfolding ucontinuous_def by auto
next
  fix U assume hU: "openin (utopology \<Psi>) U"
  let ?V = "{x \<in> topspace (utopology \<Phi>). f x \<in> U}"
  have "\<exists>F. entourage_in \<Phi> F \<and> F``{x} \<subseteq> ?V" if hx: "x \<in> uspace \<Phi> \<and> f x \<in> U" for x
  proof -
    from that hU obtain E where hE: "entourage_in \<Psi> E \<and> E``{f x} \<subseteq> U"
      unfolding openin_utopology by blast
    let ?F = "{(x, y) \<in> uspace \<Phi> \<times> uspace \<Phi>. (f x, f y) \<in> E}"
    have "?F``{x} = {y \<in> uspace \<Phi>. f y \<in> E``{f x}}" unfolding Image_def using hx by auto
    then have "?F``{x} \<subseteq> ?V" using hE by auto
    moreover have "entourage_in \<Phi> ?F" 
      using assms entourage_preimage_ucontinuous hE unfolding topspace_utopology by blast
    ultimately show ?thesis by blast
  qed
  then show "openin (utopology \<Phi>) ?V" unfolding openin_utopology by force
qed

subsection \<open>Metric spaces as uniform spaces\<close>

context Metric_space 
begin 

abbreviation mentourage :: "real \<Rightarrow> ('a \<times> 'a) set" where
"mentourage \<epsilon> \<equiv> {(x,y) \<in> M \<times> M. d x y < \<epsilon>}"

definition muniformity :: "'a uniformity" where
"muniformity = uniformity (M, \<lambda>E. E \<subseteq> M \<times> M \<and> (\<exists>\<epsilon> > 0. mentourage \<epsilon> \<subseteq> E))"

lemma
  uspace_muniformity[simp]: "uspace muniformity = M" and 
  entourage_muniformity: "entourage_in muniformity = (\<lambda>E. E \<subseteq> M \<times> M \<and> (\<exists>\<epsilon> > 0. mentourage \<epsilon> \<subseteq> E))"
proof -
  have "uniformity_on M (\<lambda>E. E \<subseteq> M \<times> M \<and> (\<exists>\<epsilon> > 0. mentourage \<epsilon> \<subseteq> E))" 
    unfolding uniformity_on_def Id_on_def converse_def
  proof (intro conjI allI impI, goal_cases)
    case 1
    then show ?case by (rule exI[of _ "mentourage 1"]) force
  next
    case (5 E)
    then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0 \<and> mentourage \<epsilon> \<subseteq> E" by blast
    then have "{(y, x). (x, y) \<in> mentourage \<epsilon>} \<subseteq> E" using commute by auto
    then have "mentourage \<epsilon> \<subseteq> E\<inverse>" by blast
    then show ?case using h\<epsilon> by auto
  next
    case (6 E)
    then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0 \<and> mentourage \<epsilon> \<subseteq> E" by blast
    let ?F = "mentourage (\<epsilon>/2)"
    have "(x,z) \<in> E" if "(x,y) \<in> ?F \<and> (y,z) \<in> ?F" for x y z
    proof -
      have "d x z < \<epsilon>" using that triangle by fastforce
      then show ?thesis using that h\<epsilon> by blast
    qed
    then have "?F \<subseteq> M \<times> M \<and> ?F O ?F \<subseteq> E" by blast 
    then show ?case by (meson h\<epsilon> order_refl zero_less_divide_iff zero_less_numeral)
  next
    case (8 E F)
    then show ?case by fast
  next
    case (10 E F)
    then obtain \<epsilon> \<delta> where
      "\<epsilon> > 0 \<and> mentourage \<epsilon> \<subseteq> E" and
      "\<delta> > 0 \<and> mentourage \<delta> \<subseteq> F" by presburger
    then have "min \<epsilon> \<delta> > 0 \<and> mentourage (min \<epsilon> \<delta>) \<subseteq> E \<inter> F" by auto
    then show ?case by blast
  qed (auto)
  then show 
    "uspace muniformity = M" and 
    "entourage_in muniformity = (\<lambda>E. E \<subseteq> M \<times> M \<and> (\<exists>\<epsilon> > 0. mentourage \<epsilon> \<subseteq> E))"
    unfolding muniformity_def using uniformity_inverse' by auto
qed

lemma uniformity_induces_mtopology [simp]: "utopology muniformity = mtopology"
proof -
  have mentourage_image: "mball x \<epsilon> = (mentourage \<epsilon>)``{x}" for x \<epsilon> unfolding mball_def by auto
  have "openin (utopology muniformity) U \<longleftrightarrow> openin mtopology U" for U
  proof
    assume hU: "openin (utopology muniformity) U"
    have "\<exists>\<epsilon> > 0. mball x \<epsilon> \<subseteq> U" if "x \<in> U" for x
    proof -
      from hU that obtain E where hE: "entourage_in muniformity E \<and> E``{x} \<subseteq> U" unfolding openin_utopology by blast
      then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0 \<and> mentourage \<epsilon> \<subseteq> E" unfolding entourage_muniformity by presburger
      then have "(mentourage \<epsilon>)``{x} \<subseteq> U" using hE by fast
      then show ?thesis using mentourage_image h\<epsilon> by auto
    qed
    then show "openin mtopology U" unfolding openin_mtopology using hU openin_subset by fastforce
  next
    assume hU: "openin mtopology U"
    have "\<exists>E. entourage_in muniformity E \<and> E``{x} \<subseteq> U" if "x \<in> U" for x
    proof -
      from hU that obtain \<epsilon> where "\<epsilon> > 0 \<and> mball x \<epsilon> \<subseteq> U" unfolding openin_mtopology by blast
      then show ?thesis unfolding mentourage_image entourage_muniformity by auto
    qed
    then show "openin (utopology muniformity) U" unfolding openin_utopology using hU openin_subset by fastforce
  qed
  then show ?thesis using topology_eq by blast
qed

subsection \<open>Connection to type class\<close>

end

text \<open>The following connects the @{class "uniform_space"} class to the set based notion 
@{term "uniformity_on"}.

Given a type @{typ "'a"} which is an instance of the class @{class "uniform_space"}, it is possible
to introduce an @{typ "'a uniformity"} on the entire universe: @{term "UNIV"}:\<close>

definition uniformity_of_space :: "('a :: uniform_space) uniformity" where
  "uniformity_of_space = uniformity (UNIV :: 'a set, (\<lambda>S. \<forall>\<^sub>F x in uniformity_class.uniformity. x\<in>S))"

text \<open>The induced uniformity fulfills the required conditions, i.e., the class based notion implies 
the set-based notion.\<close>

lemma uniformity_on_uniformity_of_space_aux:
  "uniformity_on (UNIV :: ('a :: uniform_space) set) (\<lambda>S. \<forall>\<^sub>F x in uniformity_class.uniformity. x\<in>S)"
proof -
  let ?u = " uniformity_class.uniformity :: ('a \<times> 'a) filter"

  have "\<exists>S. (\<forall>\<^sub>F x in ?u.x \<in> S)" by (intro exI[where x="UNIV \<times> UNIV"]) simp
  moreover have "(\<forall>\<^sub>F x in ?u.x \<in> E \<inter> F)" if "(\<forall>\<^sub>F x in ?u.x \<in> E)" "(\<forall>\<^sub>F x in ?u.x \<in> F)" for E F
    using that eventually_conj by auto
  moreover have "Id_on UNIV \<subseteq> E" if "\<forall>\<^sub>F x in ?u. x \<in> E" for E
  proof -
    have "(x,x) \<in> E" for x using uniformity_refl[OF that] by auto
    thus ?thesis unfolding Id_on_def by auto
  qed
  moreover have "(\<forall>\<^sub>F x in ?u. x \<in> E\<inverse>)" if "\<forall>\<^sub>F x in ?u. x \<in> E" for E 
    using uniformity_sym[OF that] by (simp add: converse_unfold)
  moreover have "\<exists>F. (\<forall>\<^sub>F x in ?u. x \<in> F) \<and> F O F \<subseteq> E" if "\<forall>\<^sub>F x in ?u. x \<in> E" for E
  proof -
    from uniformity_trans[OF that]
    obtain D where "eventually D ?u" "(\<forall>x y z. D (x, y) \<longrightarrow> D (y, z) \<longrightarrow> (x, z) \<in> E)" by auto
    thus ?thesis by (intro exI[where x="Collect D"]) auto
  qed
  moreover have "\<forall>\<^sub>F x in ?u. x \<in> F" if "\<forall>\<^sub>F x in ?u. x \<in> E" "E \<subseteq> F" for E F
    using that(2) by (intro eventually_mono[OF that(1)]) auto
  ultimately show ?thesis
    unfolding uniformity_on_def by auto
qed

lemma uniformity_rep_uniformity_of_space:
  "uniformity_rep uniformity_of_space = (UNIV, (\<lambda>S. \<forall>\<^sub>F x in uniformity_class.uniformity. x \<in> S))"
  unfolding uniformity_of_space_def using uniformity_on_uniformity_of_space_aux
  by (intro uniformity_inverse) auto

lemma uspace_uniformity_space [simp, iff]:
  "uspace uniformity_of_space = UNIV"
  unfolding uspace_def uniformity_rep_uniformity_of_space by simp

lemma entourage_in_uniformity_space:
  "entourage_in uniformity_of_space S =(\<forall>\<^sub>F x in uniformity_class.uniformity. x \<in> S)"
  unfolding entourage_in_def uniformity_rep_uniformity_of_space by simp

text \<open>Compatibility of the @{term "Metric_space.muniformity"} with the uniformity based on
the class based hierarchy.\<close>

lemma "(uniformity_of_space :: ('a :: metric_space) uniformity) = Met_TC.muniformity"
proof -
  have "(\<forall>x y. dist x y < \<epsilon> \<longrightarrow> (x, y) \<in> E) = ({(x, y). dist x y < \<epsilon>} \<subseteq> E)" 
    for \<epsilon> and E :: "('a \<times> 'a) set" 
    by auto
  thus ?thesis
    unfolding Met_TC.muniformity_def uniformity_of_space_def eventually_uniformity_metric by simp
qed

end
