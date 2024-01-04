(* Theory: Basic_Bounds_Application.thy
   Author: Chelsea Edmonds
*)

section \<open>Basic Probabilistic Method Application\<close>
text \<open>This section establishes step (1) of the basic framework for incidence set systems, 
as well as some basic bounds on hypergraph colourings \<close>
theory Basic_Bounds_Application imports "Lovasz_Local.Basic_Method" Hypergraph_Colourings
begin

subsection \<open>Probability Spaces for Incidence Set Systems \<close>
text \<open>This is effectively step (1) of the formal framework for probabilistic method. Unlike stages (3) 
and (4), which were formalised in the Lovasz\_Local\_Lemma AFP entry, this stage required a 
formalisation of incidence set systems as well as the background probability space locales \<close>

text \<open>A basic probability space for a point measure on a non-trivial structure \<close>
locale vertex_fn_space = fin_hypersystem_vne +
  fixes F :: "'a set \<Rightarrow> 'b set"
  fixes p :: "'b \<Rightarrow> real"
  assumes ne: "F \<V> \<noteq> {}"
  assumes fin: "finite (F \<V>)"
  assumes pgte0: "\<And> fv . fv \<in> F \<V> \<Longrightarrow> p fv \<ge> 0"
  assumes sump: "(\<Sum>x \<in> (F \<V>) . p x) = 1"
begin

definition "\<Omega> \<equiv> F \<V>" (* model space *)

lemma fin_\<Omega>: "finite \<Omega>"
  unfolding \<Omega>_def using fin by auto

lemma ne_\<Omega>: "\<Omega> \<noteq> {}"
  unfolding \<Omega>_def using ne by simp

definition "M = point_measure \<Omega> p"

lemma space_eq: "space M = \<Omega>"
  unfolding M_def \<Omega>_def by (simp add: space_point_measure)

lemma sets_eq: "sets M =  Pow (\<Omega>)"
  unfolding M_def by (simp add: sets_point_measure)

lemma finite_event: "A \<subseteq> \<Omega> \<Longrightarrow> finite A"
  by (simp add: finite_subset fin_\<Omega>)

lemma emeasure_eq: "emeasure M A = (if (A \<subseteq> \<Omega>) then (\<Sum>a\<in>A. p a) else 0)"
proof (cases "A \<subseteq> \<Omega>")
  case True
  then have "finite A" using finite_event by auto
  moreover have "ennreal (sum p A) = (\<Sum>a\<in>A. ennreal (p a))" 
    using sum_ennreal pgte0 True by (simp add: subset_iff \<Omega>_def) 
  ultimately have "emeasure M A = (\<Sum>a\<in>A. p a)" 
    using emeasure_point_measure_finite2[of A \<Omega> p] M_def
    using True by presburger 
  then show ?thesis using True by auto
next
  case False
  then show ?thesis using emeasure_notin_sets sets_eq by auto
qed

lemma integrable_M[intro, simp]: "integrable M (f::_ \<Rightarrow> real)"
  using fin_\<Omega> by (simp add: integrable_point_measure_finite M_def)

lemma borel_measurable_M[measurable]: "f \<in> borel_measurable M"
  unfolding M_def by simp

lemma prob_space_M: "prob_space M"
  unfolding M_def using fin_\<Omega> ne_\<Omega> pgte0 sump \<Omega>_def
  by (intro prob_space_point_measure) (simp_all)

end

sublocale vertex_fn_space \<subseteq> prob_space M
  using prob_space_M .

text \<open>A uniform variation of the space \<close>
locale vertex_fn_space_uniform = fin_hypersystem_vne +
  fixes F :: "'a set \<Rightarrow> 'b set"
  assumes ne: "F \<V> \<noteq> {}"
  assumes fin: "finite (F \<V>)"
begin

definition "\<Omega>U \<equiv> F \<V>"

definition "MU \<equiv> uniform_count_measure \<Omega>U"

end

sublocale vertex_fn_space_uniform \<subseteq> vertex_fn_space \<V> E F "(\<lambda>x. 1 / card \<Omega>U)"
  rewrites  "\<Omega> = \<Omega>U" and "M = MU"
proof (unfold_locales )
  show 1: "F \<V> \<noteq> {}" and 2: "finite (F \<V>)" by (simp_all add: fin ne)
  show 3: "\<And>fv. fv \<in> F \<V> \<Longrightarrow> 0 \<le> 1 / real (card (\<Omega>U))" by auto
  show 4: "(\<Sum>x\<in>F \<V>. 1 / real (card \<Omega>U)) = 1"
    using sum_constant ne fin \<Omega>U_def by auto
  interpret vf: vertex_fn_space \<V> E F "(\<lambda>x. 1 / card (\<Omega>U))"
    using 1 2 3 4 by (unfold_locales)
  show "vf.\<Omega> = \<Omega>U" unfolding vf.\<Omega>_def \<Omega>U_def by simp
  show "vf.M = MU"  unfolding vf.M_def vf.\<Omega>_def MU_def uniform_count_measure_def using \<Omega>U_def by auto
qed

context vertex_fn_space_uniform
begin

lemma emeasure_eq: "emeasure MU A = (if (A \<subseteq> \<Omega>U) then ((card A)/card (\<Omega>U)) else 0)"
  using fin_\<Omega> MU_def emeasure_uniform_count_measure[of "\<Omega>U" "A"]
    sets_uniform_count_measure emeasure_notin_sets Pow_iff ennreal_0 by (metis (full_types))

lemma measure_eq_valid: "A \<in> events \<Longrightarrow> measure MU A = (card A)/card (\<Omega>U)"
  using sets_eq by (simp add: MU_def \<Omega>U_def fin measure_uniform_count_measure) 

lemma expectation_eq:
  shows "expectation f = (\<Sum> x \<in> \<Omega>U. f x) / card \<Omega>U"
proof-
  have "(\<And>a. a \<in> \<Omega>U \<Longrightarrow> 0 \<le> 1 / real (card \<Omega>U))"
    using fin_\<Omega> ne_\<Omega> by auto
  moreover have "\<And> a. a\<in>\<Omega>U \<Longrightarrow> (1 / real (card \<Omega>U)) *\<^sub>R f a = 1 / (card \<Omega>U) * f a"
    using real_scaleR_def by simp
  ultimately have "expectation f = (\<Sum> x \<in> \<Omega>U. f x * (1 / (card \<Omega>U)))" 
    using uniform_count_measure_def[of \<Omega>U] lebesgue_integral_point_measure_finite[of \<Omega>U "(\<lambda> x. 1 / card \<Omega>U)" "f"] 
      MU_def fin_\<Omega> by auto
  then show ?thesis using sum_distrib_right[symmetric, of f "1 / (card \<Omega>U)" \<Omega>U] by auto
qed

end

text \<open>A probability space over the full vertex set \<close>
locale vertex_space = fin_hypersystem_vne +
  fixes p :: "'a \<Rightarrow> real"
  assumes pgte0: "\<And> fv . fv \<in> \<V> \<Longrightarrow> p fv \<ge> 0"
  assumes sump: "(\<Sum>x \<in> (\<V>) . p x) = 1"


sublocale vertex_space \<subseteq> vertex_fn_space \<V> E "\<lambda> i . i" p
  rewrites "\<Omega> = \<V>"
proof (unfold_locales)
  interpret vertex_fn_space \<V> E "\<lambda> i . i" p
    by unfold_locales (simp_all add: pgte0 sump V_nempty finite_sets)
  show "\<Omega> = \<V>"
    using \<Omega>_def by simp
qed (simp_all add: pgte0 sump V_nempty finite_sets)

text \<open>A uniform variation of the probability space over the vertex set \<close>
locale vertex_space_uniform = fin_hypersystem_vne

sublocale vertex_space_uniform \<subseteq> vertex_fn_space_uniform \<V> E "\<lambda> i . i"
  rewrites "\<Omega>U = \<V>"
proof (unfold_locales)
 interpret vertex_fn_space_uniform \<V> E "\<lambda> i . i"
   by unfold_locales (simp_all add: V_nempty finite_sets)
  show "\<Omega>U = \<V>" unfolding \<Omega>U_def by simp
qed (simp_all add: V_nempty finite_sets)

text \<open>A uniform probability space over a vertex subset \<close>
locale vertex_ss_space_uniform = fin_hypersystem_vne + 
  fixes VS 
  assumes vs_ss: "VS \<subseteq> \<V>"
  assumes ne_vs: "VS \<noteq> {}"
begin

lemma finite_vs: "finite VS"
  using vs_ss finite_subset finite_sets by auto

end

sublocale vertex_ss_space_uniform \<subseteq> vertex_fn_space_uniform \<V> E "\<lambda> i. VS"
  rewrites "\<Omega> = VS" 
proof (unfold_locales)
  interpret vertex_fn_space_uniform \<V> E "\<lambda> i . VS" 
    by unfold_locales (simp_all add: ne_vs finite_vs)
  show "\<Omega> = VS"
    using \<Omega>_def by simp
qed (simp_all add: ne_vs finite_vs)

text \<open>A non-uniform prob space over a vertex subset \<close>
locale vertex_ss_space = fin_hypersystem_vne +
  fixes VS
  assumes vs_ss: "VS \<subseteq> \<V>"
  assumes ne_vs: "VS \<noteq> {}"
  fixes p :: "'a \<Rightarrow> real"
  assumes pgte0: "\<And> fv . fv \<in> VS \<Longrightarrow> p fv \<ge> 0"
  assumes sump: "(\<Sum>x \<in> (VS) . p x) = 1"
begin

lemma finite_vs: "finite VS"
  using vs_ss finite_subset finite_sets by auto

end

sublocale vertex_ss_space \<subseteq> vertex_fn_space \<V> E "\<lambda> i . VS" p
  rewrites "\<Omega> = VS"
proof (unfold_locales)
  interpret vertex_fn_space \<V> E "\<lambda> i . VS" p
    by unfold_locales (simp_all add: pgte0 sump ne_vs finite_vs)
  show "\<Omega> = VS"
    using \<Omega>_def by simp
qed (simp_all add: pgte0 sump ne_vs finite_vs)

text \<open>A uniform probability space over a property on the vertex set \<close>
locale vertex_prop_space = fin_hypersystem_vne + 
  fixes P :: "'b set" (* property *)
  assumes finP: "finite P"
  assumes nempty_P: "P \<noteq> {}"

sublocale vertex_prop_space \<subseteq> vertex_fn_space_uniform \<V> E "\<lambda> V. V \<rightarrow>\<^sub>E P"
rewrites "\<Omega>U = \<V> \<rightarrow>\<^sub>E P" 
proof -
  interpret vertex_fn_space_uniform \<V> E "\<lambda> V. V \<rightarrow>\<^sub>E P"
  proof (unfold_locales)
    show "\<V> \<rightarrow>\<^sub>E P \<noteq> {}" using finP V_nempty PiE_eq_empty_iff nempty_P by meson
    show "finite (\<V> \<rightarrow>\<^sub>E P)" using finP finite_PiE finite_sets by meson
  qed 
  show "vertex_fn_space_uniform \<V> E (\<lambda>V. V \<rightarrow>\<^sub>E P)" by unfold_locales
  show "\<Omega>U = \<V> \<rightarrow>\<^sub>E P "unfolding \<Omega>U_def by simp
qed

context vertex_prop_space
begin

lemma prob_uniform_vertex_subset: 
  assumes "b \<in> P"
  assumes "d \<subseteq> \<V>"
  shows "prob  {f \<in> \<Omega> . (\<forall> v \<in> d .f v = b)} = 1/((card P) powi (card d))"
  using finP nempty_P V_nempty finite_sets MU_def \<Omega>U_def
  by (simp add: assms(1) assms(2) prob_uniform_ex_fun_space) 

lemma prob_uniform_vertex: 
  assumes "b \<in> P"
  assumes "v \<in> \<V>"
  shows "prob  {f \<in> \<Omega>U . f v = b} = 1/(card P)"
proof -
  have "prob {f \<in> \<Omega>U . f v = b} = card {f \<in> \<Omega>U . f v = b}/card \<Omega>U"
    using measure_eq_valid sets_eq by auto
  then show ?thesis 
    using card_PiE_val_indiv_eq[of "\<V>" b P v] \<Omega>_def finite_sets finP nempty_P assms by auto
qed

end

text \<open>A uniform vertex colouring space \<close>
locale vertex_colour_space = fin_hypergraph_nt +
  fixes n :: nat (*Number of colours *)
  assumes n_lt_order: "n \<le> horder"
  assumes n_not_zero: "n \<noteq> 0"


sublocale vertex_colour_space \<subseteq> vertex_prop_space \<V> E "{0..<n}"
  rewrites "\<Omega>U = \<C>\<^sup>n" 
proof -
  have "{0..<n} \<noteq> {}" using n_not_zero by simp
  then interpret vertex_prop_space \<V> E "{0..<n}"
    by (unfold_locales) (simp_all)
  show "vertex_prop_space \<V> E {0..<n}" by (unfold_locales)
  show "\<Omega>U = \<C>\<^sup>n"
    using \<Omega>_def all_n_vertex_colourings_alt by auto
qed

text \<open>This probability space contains several useful lemmas on basic vertex colouring probabilities
(and monochromatic edges), which are facts that are typically either not proven, or have very short
proofs on paper \<close>
context vertex_colour_space
begin

lemma colour_set_event: "{f \<in> \<C>\<^sup>n. mono_edge_col f e c} \<in> events"
  using sets_eq by simp

lemma colour_functions_event: "(\<lambda> c. {f \<in> \<C>\<^sup>n . mono_edge_col f e c}) ` {0..<n} \<subseteq> events"
  using sets_eq by blast

lemma prob_vertex_colour: "v \<in> \<V> \<Longrightarrow> c \<in> {0..<n} \<Longrightarrow> prob {f \<in> \<C>\<^sup>n . f v = c} = 1/n"
  using prob_uniform_vertex by simp

lemma prob_edge_colour: 
  assumes "e \<in># E" "c \<in> {0..<n}"
  shows "prob {f \<in> \<C>\<^sup>n . mono_edge_col f e c} = 1/(n powi (card e))"
proof -
  have "card {0..<n} = n" by simp
  moreover have "\<C>\<^sup>n = \<V> \<rightarrow>\<^sub>E {0..<n}" using all_n_vertex_colourings_alt by blast
  moreover have "{0..<n} \<noteq> {}" using n_not_zero by simp
  ultimately show ?thesis using prob_uniform_ex_fun_space[of \<V> _ "{0..<n}" e] n_not_zero 
      finite_sets wellformed assms by (simp add: MU_def V_nempty mono_edge_col_def)
qed

lemma prob_monochromatic_edge_inv: 
  assumes "e \<in># E"
  shows "prob{f \<in> \<C>\<^sup>n . mono_edge f e} = 1/(n powi (int (card e) - 1))"
proof -
  have "finite {0..<n}"by auto
  then have "prob {f \<in> \<C>\<^sup>n . mono_edge f e} = (\<Sum>c \<in> {0..<n} . prob {f \<in> \<C>\<^sup>n . mono_edge_col f e c})"
    using finite_measure_finite_Union[of "{0..<n}" "(\<lambda> c . {f \<in> \<C>\<^sup>n .  mono_edge_col f e c})" ] 
      disjoint_family_on_colourings colour_functions_event mono_edge_set_union assms by auto
  also have "... = n/(n powi (int (card e)))" using prob_edge_colour assms by simp
  also have "... = n/(n* (n powi ((int (card e)) - 1)))" using n_not_zero 
      power_int_commutes power_int_minus_mult by (metis of_nat_0_eq_iff) 
  finally show ?thesis using n_not_zero by simp 
qed

lemma prob_monochromatic_edge: 
  assumes "e \<in># E"
  shows "prob{f \<in> \<C>\<^sup>n . mono_edge f e} = n powi (1 - int (card e))"
  using prob_monochromatic_edge_inv assms n_not_zero by (simp add: power_int_diff) 

lemma prob_monochromatic_edge_bound: 
  assumes "e \<in># E"
  assumes "\<And> e. e \<in>#E \<Longrightarrow> card e \<ge> k"
  assumes "k > 0"
  shows "prob{f \<in> \<C>\<^sup>n . mono_edge f e} \<le> 1/((real n) powi (k-1))" 
proof -
  have "(int (card (e)) - 1) \<ge> k - 1" using assms(3) assms(1)
    using assms(2) int_ops(6) of_nat_0_less_iff of_nat_mono by fastforce
  then have "((n :: real) powi (int (card (e)) - 1)) \<ge> (n powi (k - 1))" 
    using power_int_increasing[of "k - 1" "(int (card (e)) - 1)" n] n_not_zero by linarith 
  moreover have "prob({f \<in> \<C>\<^sup>n . mono_edge f e}) = 1/(n powi (int (card (e)) - 1))"
    using prob_monochromatic_edge_inv assms(1) by simp
  ultimately show ?thesis using frac_le zero_less_power_int n_not_zero 
    by (smt (verit) less_imp_of_nat_less of_nat_0_eq_iff of_nat_0_le_iff of_nat_1 of_nat_diff zle_int)
qed

end

subsection \<open>More Hypergraph Colouring Results \<close>

context fin_hypergraph_nt
begin

lemma not_proper_colouring_edge_mono: "{f \<in> \<C>\<^sup>n . \<not> is_proper_colouring f n} = (\<Union>e \<in> (set_mset E). {f \<in> \<C>\<^sup>n . mono_edge f e})"
proof -
  have "{f \<in> \<C>\<^sup>n . \<not> is_proper_colouring f n} = {f \<in> \<C>\<^sup>n . \<exists> e \<in> set_mset E . mono_edge f e}"
    using ex_monochomatic_not_colouring no_monochomatic_is_colouring 
    by (metis (mono_tags, lifting) all_n_vertex_colourings_alt)
  then show ?thesis using Union_exists by simp
qed

lemma proper_colouring_edge_mono: "{f \<in> \<C>\<^sup>n . is_proper_colouring f n} = (\<Inter>e \<in> (set_mset E). {f \<in> \<C>\<^sup>n . \<not> mono_edge f e})"
proof -
  have "{f \<in> \<C>\<^sup>n . is_proper_colouring f n} = {f \<in> \<C>\<^sup>n . \<forall> e \<in> set_mset E . \<not> mono_edge f e}"
    using is_proper_colouring_alt2 all_n_vertex_colourings_alt by auto
  moreover have "set_mset E \<noteq> {}" using E_nempty by simp
  ultimately show ?thesis using Inter_forall by auto
qed

lemma proper_colouring_edge_mono_compl: "{f \<in> \<C>\<^sup>n . is_proper_colouring f n} = (\<Inter>e \<in> (set_mset E). \<C>\<^sup>n - {f \<in> \<C>\<^sup>n . mono_edge f e})"
  using proper_colouring_edge_mono by auto

lemma event_is_proper_colouring: 
  assumes "g \<in> \<C>\<^sup>n"
  assumes "g \<notin>(\<Union>e \<in> (set_mset E). {f \<in> \<C>\<^sup>n . mono_edge f e})"
  shows "is_proper_colouring g n"
proof -
  have "\<And> e. e \<in># E \<Longrightarrow> \<not> mono_edge g e" using assms
    by blast
  then show ?thesis using assms(1) all_n_vertex_colourings_def by (auto)
qed


end

subsection \<open>The Basic Application \<close>
text \<open>The comments below show the basic framework steps \<close>

context fin_kuniform_hypergraph_nt
begin
proposition erdos_propertyB:  
  assumes "size E < (2^(k - 1))"
  assumes "k > 0"
  shows "has_property_B"
proof -
  \<comment> \<open>(1) Set up the probability space: "Colour V randomly with two colours" \<close>
  interpret P: vertex_colour_space \<V> E 2 
    by unfold_locales (auto simp add: order_ge_two)
  \<comment> \<open>(2) define the event to avoid - monochromatic edges \<close>
  define A where "A \<equiv>(\<lambda> e. {f \<in> \<C>\<^sup>2 . mono_edge f e})"
  \<comment> \<open>(3) Calculation 2: Have Pr (of Ae for any e) \le Sum over e (Pr (A e)) < 1 \<close>
  have "(\<Sum>e \<in> set_mset E. P.prob (A e)) < 1"
  proof -
    have "int k - 1 = int (k - 1)" using assms by linarith 
    then have "card (set_mset E) < 2 powi (int k - 1)" using card_size_set_mset[of E] assms by simp
    then have "(\<Sum>e \<in> (set_mset E). P.prob (A e)) < 2 powi (int k - 1) * 2 powi (1 - int k)"
      unfolding A_def using P.prob_monochromatic_edge uniform assms(1) by simp
    moreover have "((2 :: real) powi ((int k) - 1)) * (2 powi (1 - (int k))) = 1" 
      using power_int_add[of 2 "int k - 1" "1- int k"] by force 
    ultimately show ?thesis using power_int_add[of 2 "int k - 1" "1- int k"] by simp
  qed
  moreover have "A ` (set_mset E) \<subseteq> P.events" unfolding A_def P.sets_eq by blast
  \<comment> \<open>(4) obtain a colouring avoiding bad events \<close>
  ultimately obtain f where "f \<in> \<C>\<^sup>2" and "f \<notin> \<Union>(A `(set_mset E))" 
    using P.Union_bound_obtain_fun[of "set_mset E" A] finite_set_mset P.space_eq by auto 
  thus ?thesis using event_is_proper_colouring A_def is_n_colourable_def by auto 
qed

end

corollary erdos_propertyB_min: 
  fixes z :: "'a itself"
  assumes "n > 0"
  shows "(min_edges_colouring n z) \<ge> 2^(n - 1)"      
proof (rule ccontr)
  assume "\<not> 2 ^ (n - 1) \<le> min_edges_colouring n z"
  then have "min_edges_colouring n z < 2^(n - 1)" by simp
  then obtain h :: "'a hyp_graph" where hin: " h \<in> not_col_n_uni_hyps n" and 
    "enat (size (hyp_edges h)) < 2^(n-1)"
    using obtains_min_edge_colouring by blast 
  then have lt: " size (hyp_edges h) < 2^(n -1)"
    by (metis of_nat_eq_enat of_nat_less_imp_less of_nat_numeral of_nat_power)  
  then interpret kuf: fin_kuniform_hypergraph_nt "(hyp_verts h)" "hyp_edges h" n 
    using not_col_n_uni_hyps_def hin by auto 
  have "kuf.has_property_B" using kuf.erdos_propertyB lt assms by simp
  then show False using hin not_col_n_uni_hyps_def by auto 
qed

end
