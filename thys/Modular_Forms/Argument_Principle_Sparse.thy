(*<*)
section \<open>A more convenient Argument Principle\<close>
theory Argument_Principle_Sparse
imports "HOL-Complex_Analysis.Complex_Analysis" "Detour_Calculus.Detour_Calculus"
begin

(*TODO: most of the lemmas here should move to HOL-Complex_Analysis*)

text \<open>TODO: replace the @{thm isolated_zeros} in the library; 
    optimise the proof of @{thm non_zero_neighbour_alt}\<close>
proposition isolated_zeros:
  assumes holf: "f holomorphic_on S"
      and "open S" "connected S" "\<xi> \<in> S" "\<beta> \<in> S" "f \<beta> \<noteq> 0"
    obtains r where "0 < r" and "ball \<xi> r \<subseteq> S" and
        "\<And>z. z \<in> ball \<xi> r - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
proof (cases "f \<xi> = 0")
  case True
  obtain r where "0 < r" and r: "ball \<xi> r \<subseteq> S"
    using \<open>open S\<close> \<open>\<xi> \<in> S\<close> open_contains_ball_eq by blast
  have powf: "((\<lambda>n. (deriv ^^ n) f \<xi> / (fact n) * (z - \<xi>)^n) sums f z)" if "z \<in> ball \<xi> r" for z
    by (intro holomorphic_power_series [OF _ that] holomorphic_on_subset [OF holf r])
  obtain m where m: "(deriv ^^ m) f \<xi> / (fact m) \<noteq> 0"
    using holomorphic_fun_eq_0_on_connected [OF holf \<open>open S\<close> \<open>connected S\<close> _ \<open>\<xi> \<in> S\<close> \<open>\<beta> \<in> S\<close>] \<open>f \<beta> \<noteq> 0\<close>
    by auto
  then have "m \<noteq> 0" using True funpow_0 by fastforce
  obtain s where "0 < s" and s: "\<And>z. z \<in> cball \<xi> s - {\<xi>} \<Longrightarrow> f z \<noteq> 0"
    using powser_0_nonzero [OF \<open>0 < r\<close> powf \<open>f \<xi> = 0\<close> m]
    by (metis \<open>m \<noteq> 0\<close> dist_norm mem_ball norm_minus_commute not_gr_zero)
  have "0 < min r s"  by (simp add: \<open>0 < r\<close> \<open>0 < s\<close>)
  then show thesis
    apply (rule that)
    using r s by auto
next
  case False
  moreover have "isCont f \<xi>"
    using assms(2) assms(4) field_differentiable_imp_continuous_at holf 
      holomorphic_on_imp_differentiable_at 
    by blast
  ultimately obtain e1 where "e1>0" "\<forall>y. dist \<xi> y < e1 \<longrightarrow> f y \<noteq> 0"
    using continuous_at_avoid by blast
  obtain e2 where "e2>0" "ball \<xi> e2 \<subseteq> S"
    using assms(2) assms(4) openE by auto
  define e where "e = min e1 e2"
  have "e>0" by (simp add: \<open>0 < e1\<close> \<open>0 < e2\<close> e_def)
  moreover have "\<forall>y. dist \<xi> y < e \<longrightarrow> f y \<noteq> 0" 
    by (simp add: \<open>\<forall>y. dist \<xi> y < e1 \<longrightarrow> f y \<noteq> 0\<close> e_def)
  moreover have "ball \<xi> e \<subseteq> S" 
    using \<open>ball \<xi> e2 \<subseteq> S\<close> e_def by fastforce
  ultimately show thesis
    using that by auto
qed

(* TODO: refactor using sparseness? *)
lemma holomorphic_compact_finite_zeros':
  assumes S: "f holomorphic_on S" "open S" "connected S"
      and "compact K" "K \<subseteq> S"
      and "\<beta> \<in> S" "f \<beta> \<noteq>0"
    shows "finite {z\<in>K. f z = 0}"
proof (rule ccontr)
  assume "infinite {z\<in>K. f z = 0}"
  then obtain z where "z \<in> K" and z: "z islimpt {z\<in>K. f z = 0}"
    using \<open>compact K\<close> by (auto simp: compact_eq_Bolzano_Weierstrass)
  moreover have "{z\<in>K. f z = 0} \<subseteq> S"
    using \<open>K \<subseteq> S\<close> by blast
  ultimately show False
    using assms analytic_continuation [OF S] by blast
qed

lemma holomorphic_imp_sparse_zeros:
  assumes f_holo: "f holomorphic_on D" and "open D" and "connected D"
    and f_nconst: "\<beta> \<in> D" "f \<beta> \<noteq> 0"
  shows "{x. f x = 0} sparse_in D" 
unfolding sparse_in_open[OF \<open>open D\<close>]
proof 
  fix y assume "y \<in> D"
  from isolated_zeros[OF f_holo \<open>open D\<close> \<open>connected D\<close> \<open>y \<in> D\<close> \<open>\<beta> \<in> D\<close> \<open>f \<beta>\<noteq>0\<close>]
  obtain r where "0 < r" "ball y r \<subseteq> D" 
      "(\<And>z. z \<in> ball y r - {y} \<Longrightarrow> f z \<noteq> 0)"
    by auto
  then show "\<not> y islimpt {x. f x = 0}"
    by (smt (verit) Elementary_Metric_Spaces.open_ball centre_in_ball 
        insert_Diff insert_iff islimpt_def mem_Collect_eq)
qed

lemma sparse_in_imp_isolated_singularity:
  assumes "pts sparse_in D" and f_ana: "f analytic_on D - pts" 
    and "z \<in> D" and "open D" 
  shows "isolated_singularity_at f z"
proof -
  have "open (D - (pts-{z}))"
    by (meson Diff_subset assms(1) assms(4) 
        open_diff_sparse_pts sparse_in_subset2)
  then obtain e1 where "e1>0" "ball z e1 \<subseteq> D - (pts-{z})"
    by (metis Diff_iff assms(3) insertCI openE)
  then have "f analytic_on ball z e1 - {z}"
    using \<open>f analytic_on D - pts\<close> 
    by (smt (verit, ccfv_threshold) Diff_eq_empty_iff Diff_iff 
        analytic_on_analytic_at insert_absorb insert_not_empty)
  with \<open>e1>0\<close> 
  show ?thesis unfolding isolated_singularity_at_def by auto
qed

lemma nconst_sparse_imp_nzero_neighbour:
  assumes f_holo: "f holomorphic_on D - pts" 
    and "open D" and "connected D" and "pts sparse_in D"
    and f_nconst: "\<not>(\<forall>w\<in>D-pts. f w=0)"
    and "z\<in>D"and "not_essential f z"
  shows "(\<forall>\<^sub>F w in at z. f w \<noteq> 0 \<and> w \<in> D - pts)"
proof -
  obtain \<beta> where \<beta>: "\<beta> \<in> D - pts" "f \<beta>\<noteq>0"
    using f_nconst by auto

  have ?thesis if "z\<notin>pts" 
  proof -
    have "\<forall>\<^sub>F w in at z. f w \<noteq> 0 \<and> w \<in> D - pts"
      apply (rule non_zero_neighbour_alt[of f "D-pts" z  \<beta>])
      subgoal by fact
      subgoal by (simp add: assms(2) assms(4) open_diff_sparse_pts)
      subgoal using sparse_imp_connected 
        by (metis DIM_complex assms(2) assms(3) assms(4) dual_order.refl)
      subgoal by (simp add: assms(6) that)
      using \<beta> by auto
    then show ?thesis by (auto elim:eventually_mono)
  qed
  moreover have ?thesis if "z\<in>pts" "\<not> f \<midarrow>z\<rightarrow> 0" 
  proof -
    have "\<forall>\<^sub>F w in at z. w \<in> D - pts"
      by (smt (verit, del_insts) Diff_iff assms(2) assms(4) assms(6) 
          at_within_open eventually_at_topological sparse_in_not_in)
    moreover have "\<forall>\<^sub>F w in at z. f w \<noteq> 0" 
    proof (cases  "is_pole f z")
      case True
      then show ?thesis using non_zero_neighbour_pole by auto
    next
      case False
      moreover have "not_essential f z" by fact
      ultimately obtain c where "c\<noteq>0" "f \<midarrow>z\<rightarrow> c"
        by (metis \<open>\<not> f \<midarrow>z\<rightarrow> 0\<close> not_essential_def)
      then show ?thesis 
        using tendsto_imp_eventually_ne by auto
    qed
    ultimately show ?thesis by eventually_elim auto
  qed
  moreover have ?thesis if "z\<in>pts" "f \<midarrow>z\<rightarrow> 0" 
  proof -
    define ff where "ff=(\<lambda>x. if x=z then 0 else f x)"
    define A where "A=D - (pts - {z})"

    have "f holomorphic_on A - {z}"
      using A_def f_holo by fastforce
    moreover have "open A"  
      by (smt (verit, del_insts) A_def DiffE assms(2) assms(4) 
          islimpt_def open_diff_sparse_pts sparse_in_def)
    ultimately have "ff holomorphic_on A" 
      using \<open>f \<midarrow>z\<rightarrow> 0\<close> unfolding ff_def
      by (rule removable_singularity)
    moreover have "connected A"
    proof -
      have "connected (D - pts)"
        by (simp add: assms(2) assms(3) assms(4) sparse_imp_connected)
      moreover have "D - pts \<subseteq> A"
        unfolding A_def by auto
      moreover have "A \<subseteq> closure (D - pts)" unfolding A_def
        by (metis A_def Diff_empty Diff_insert Diff_insert0 
            \<open>open A\<close> at_within_open closure_subset insert_Diff 
            insert_subset not_trivial_limit_within trivial_limit_at)
      ultimately show ?thesis using connected_intermediate_closure 
        by auto
    qed
    moreover have "z \<in> A" using A_def assms(6) by blast
    moreover have "ff z = 0" unfolding ff_def by auto
    moreover have "\<beta> \<in> A " using A_def \<beta>(1) by blast
    moreover have "ff \<beta> \<noteq> 0" using \<beta>(1) \<beta>(2) ff_def that(1) by auto
    ultimately obtain r where "0 < r" 
        "ball z r \<subseteq> A" "\<And>x. x \<in> ball z r - {z} \<Longrightarrow> ff x \<noteq> 0"
      using \<open>open A\<close> isolated_zeros[of ff A z \<beta>] by auto
    then show ?thesis unfolding eventually_at ff_def
      by (intro exI[of _ r]) (auto simp: A_def dist_commute ball_def)
  qed
  ultimately show ?thesis by auto
qed

subsection \<open>Argument principle\<close>

lemma get_analytic_cover_path:
  fixes f :: "complex \<Rightarrow> complex" and A pts :: "complex set"
  assumes f_analytic: "f analytic_on (path_image \<gamma>)" and
          \<gamma>: "path \<gamma>" (*"pathfinish \<gamma> = pathstart \<gamma>" *)
  obtains e where "e > 0" "f analytic_on (\<Union>x\<in>path_image \<gamma>. ball x e)"
proof -
  obtain get_e where get_e: "get_e x>0" "f holomorphic_on ball x (get_e x)"
    if "x\<in>path_image \<gamma>" for x
    using f_analytic by (metis analytic_at_ball analytic_on_analytic_at)
  
  obtain e where "e>0"
      and "(\<Union>x\<in>path_image \<gamma>. ball x e) 
              \<subseteq> (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))"
  proof -
    have "compact (path_image \<gamma>)" 
      using \<open>path \<gamma>\<close> by blast
    moreover have "open (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))" 
      by blast
    moreover have "path_image \<gamma> \<subseteq> (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))" 
      using get_e(1) by auto
    ultimately show ?thesis
      using compact_subset_open_imp_ball_epsilon_subset that by blast
  qed
  then have "f analytic_on (\<Union>x\<in>path_image \<gamma>. ball x e)"
    using get_e(2) 
    by (smt (verit) open_ball analytic_on_UN analytic_on_open 
        analytic_on_subset)
  then show ?thesis using that \<open>e>0\<close> by auto
qed

lemma get_sparse_cover_path:
  assumes sparse: "pts sparse_in (path_image \<gamma>)" and "path \<gamma>" 
  obtains e where "e > 0" "\<forall>z\<in> (\<Union>x\<in>path_image \<gamma>. ball x e). \<not>z islimpt pts"
proof -
  obtain get_e where get_e: "get_e x>0"
      "(\<forall>y\<in>(ball x (get_e x)). \<not> y islimpt pts)" 
    if "x\<in>path_image \<gamma>" for x
    using sparse unfolding sparse_in_ball_def by metis

  obtain e where "e>0"
      and "(\<Union>x\<in>path_image \<gamma>. ball x e) 
              \<subseteq> (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))"
  proof -
    have "compact (path_image \<gamma>)" 
      using \<open>path \<gamma>\<close> by blast
    moreover have "open (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))" 
      by blast
    moreover have "path_image \<gamma> \<subseteq> (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))" 
      using get_e(1) by auto
    ultimately show ?thesis
      using compact_subset_open_imp_ball_epsilon_subset that by blast
  qed
  then have "\<forall>z\<in> (\<Union>x\<in>path_image \<gamma>. ball x e). \<not> z islimpt pts"
    using get_e(2) by blast
  then show ?thesis using that \<open>e>0\<close> by auto
qed

theorem argument_principle_sparse:
  fixes f:: "complex \<Rightarrow> complex"
  assumes f_analytic: "f analytic_on A - pts" and
          \<gamma>: "valid_path \<gamma>" "pathfinish \<gamma> = pathstart \<gamma>" "path_image \<gamma> \<subseteq> A - pts" and
          inside_subset: "inside (path_image \<gamma>) \<subseteq> A" and
          not_essential: "\<forall>p\<in>pts. not_essential f p" and 
          sparse: "pts sparse_in A" and
          f_nz: "\<And>z. z \<in> A - pts \<Longrightarrow> f z \<noteq> 0" 
  shows "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) = 2 * pi * \<i> *
          (\<Sum>\<^sub>\<infinity> z\<in>pts. winding_number \<gamma> z * zorder f z)"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  define B1 where "B1 = path_image \<gamma> \<union> inside (path_image \<gamma>)"
  have "compact B1"
  proof -
    have "closed B1" unfolding B1_def 
      apply (rule closed_path_image_Un_inside)
      by (simp add: \<gamma>(1) valid_path_imp_path)
    moreover have "bounded B1" unfolding B1_def 
      by (simp add: \<gamma>(1) bounded_inside bounded_path_image valid_path_imp_path)
    ultimately show ?thesis using compact_eq_bounded_closed by auto
  qed
  have "connected B1" 
  proof -
    have "closed (path_image \<gamma>)"
      by (simp add: assms(2) closed_valid_path_image)
    moreover have "connected (path_image \<gamma>)" 
      by (simp add: assms(2) connected_valid_path_image)
    ultimately show ?thesis
      unfolding B1_def using connected_with_inside by auto
  qed

  have "finite (B1 \<inter> pts)"
  proof (rule sparse_in_compact_finite)
    have "B1 \<subseteq> A" using B1_def assms(4) local.inside_subset by auto
    then show "pts sparse_in B1" 
      using sparse_in_subset sparse by auto
  qed fact
  
  obtain get_e where get_e: "get_e x>0" "f holomorphic_on ball x (get_e x)"
    if "x\<in>A - pts" for x
    using f_analytic by (metis analytic_at_ball analytic_on_analytic_at)
  obtain get_b where get_b: "get_b x>0"
      "(\<forall>y\<in>(ball x (get_b x)). \<not> y islimpt pts)" if "x\<in>A" for x
    using sparse unfolding sparse_in_ball_def by metis


  define g_eb where "g_eb = (\<lambda>x. ball x (min (get_e x) (get_b x)))"
  have open_g_eb: "open (\<Union>x\<in>path_image \<gamma>. g_eb x)" 
    unfolding g_eb_def using assms(4) get_b(2) by auto
  have g_eb_path_image: "path_image \<gamma> \<subseteq> \<Union> (g_eb ` path_image \<gamma>)"
    unfolding g_eb_def 
    using assms(4) get_b(1) get_e(1) by force

  define B2 where "B2 = (\<Union>x\<in>path_image \<gamma>. g_eb x) \<union> inside (path_image \<gamma>)"
  have not_islimpt_B2: "\<not> z islimpt pts" if "z\<in>B2" for z
  proof -
    have ?thesis if "z\<in>(\<Union>x\<in>path_image \<gamma>. g_eb x)"
    proof -
      from that
      obtain x where "x\<in>path_image \<gamma>" "z\<in>g_eb x" 
        using get_b(2) unfolding B2_def by auto
      from \<open>x\<in>path_image \<gamma>\<close> have "x\<in>A" 
        using assms(4) by auto
      moreover have "z\<in>ball x (get_b x)" 
        using \<open>z\<in>g_eb x\<close> unfolding g_eb_def by auto
      ultimately show ?thesis using get_b(2) by auto
    qed
    moreover have ?thesis if "z\<in>inside (path_image \<gamma>)"
      using get_b(1) get_b(2) local.inside_subset that by auto
    ultimately show ?thesis using that unfolding B2_def by auto
  qed  
  have f_B2_holo: "f holomorphic_on B2 - (B1\<inter> pts)"
  proof -
    have "f holomorphic_on (\<Union>x\<in>path_image \<gamma>. g_eb x) - B1 \<inter> pts" 
    proof -
      have "(\<Union>x\<in>path_image \<gamma>. g_eb x) - B1 \<inter> pts 
              \<subseteq> (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))"
        unfolding g_eb_def by auto
      moreover have "f holomorphic_on (\<Union>x\<in>path_image \<gamma>. ball x (get_e x))"
        using assms(4) get_e(2) 
        by (meson Elementary_Metric_Spaces.open_ball holomorphic_on_UN_open subsetD)
      ultimately show ?thesis by auto
    qed
    moreover have "f holomorphic_on (inside (path_image \<gamma>) - B1 \<inter> pts)" 
      by (smt (verit, best) B1_def Diff_Int2 Diff_eq Un_Int_eq(4)
          analytic_imp_holomorphic f_analytic holomorphic_on_subset inf_commute 
          inf_sup_distrib2 local.inside_subset sup.absorb_iff2)
    moreover have "open (\<Union> (g_eb ` path_image \<gamma>) - B1 \<inter> pts)"
      apply (rule open_Diff)
      using open_g_eb \<open>finite (B1 \<inter> pts)\<close>[THEN finite_imp_closed] by auto
    moreover have "open (inside (path_image \<gamma>) - B1 \<inter> pts)" 
      by (simp add: \<gamma>(1) \<open>finite (B1 \<inter> pts)\<close> closed_valid_path_image 
          finite_imp_closed open_Diff open_inside)
    ultimately show ?thesis
      unfolding B2_def Un_Diff by (rule holomorphic_on_Un)
  qed
  have "open B2" 
  proof -
    have "open (inside (path_image \<gamma>))" 
      by (simp add: \<gamma>(1) closed_valid_path_image open_inside)
    with open_g_eb show ?thesis unfolding B2_def by auto
  qed
  moreover have "B1 \<subseteq> B2" 
    using g_eb_path_image unfolding B1_def B2_def by auto
  ultimately obtain e0 where e0: "e0 > 0"  "(\<Union>x\<in>B1. cball x e0) \<subseteq> B2" 
    using compact_subset_open_imp_cball_epsilon_subset[OF \<open>compact B1\<close>] that 
    by auto
  define e where "e = e0 / 2" 
  have "e>0" unfolding e_def using \<open>e0>0\<close> by auto

  have B1_e_open: "open (\<Union>x\<in>B1. ball x e)" by blast
  have connected_B1_ball: "connected (\<Union>x\<in>B1. ball x e)" if "e>0" for e
  proof -
    have "connected (B1 \<union> (\<Union>x\<in>B1. ball x e))"
      apply (rule connected_Un_UN)
      subgoal by fact
      subgoal by blast
      subgoal using \<open>0 < e\<close> imageE by auto
      done
    moreover have "B1 \<union> (\<Union>x\<in>B1. ball x e) = (\<Union>x\<in>B1. ball x e)"
      using \<open>0 < e\<close> by auto
    ultimately show "connected (\<Union>x\<in>B1. ball x e)" by simp
  qed

  have "compact (\<Union>x\<in>B1. cball x e)"
    apply (rule compact_minkowski_sum_cball)
    by fact

  \<comment>\<open>To show f is non-vanishing\<close>
  obtain \<beta> where "\<beta> \<in> path_image \<gamma>" by auto
  then have "\<beta> \<in> B1" "\<beta> \<notin> pts" "f \<beta> \<noteq> 0" 
    unfolding B1_def using assms(4) f_nz by auto

  define B3 where "B3 = (\<Union>x\<in>B1. ball x e)"
  define pz where "pz = B3 \<inter> (pts \<union> {x. f x =0})"
  have "open B3" using B3_def by blast
  have "finite pz" 
  proof -
    have "pz = (B3 \<inter> pts) \<union> ((B3-B1) \<inter> -pts \<inter> {x. f x =0})
                            \<union> (B1 \<inter> -pts \<inter> {x. f x =0})"
    proof -
      have "B1 \<subseteq> B3" unfolding B1_def B3_def using \<open>e>0\<close> by auto
      then show ?thesis unfolding pz_def by fast
    qed
    moreover have "(B1 \<inter> -pts \<inter> {x. f x =0}) = {}"
    proof -
      have "B1 \<subseteq> A" unfolding B1_def 
        using assms(4) local.inside_subset by auto
      with f_nz show ?thesis by blast
    qed
    moreover have "finite ((B3-B1) \<inter> -pts \<inter> {x. f x =0})" 
    proof -
      have "finite {z \<in> (\<Union>x\<in>B1. cball x e) - inside (path_image \<gamma>). f z = 0}"
      proof (rule holomorphic_compact_finite_zeros')
        from f_B2_holo
        show "f holomorphic_on (\<Union>x\<in>B1. ball x e0) - B1 \<inter> pts"
          apply (elim holomorphic_on_subset)
          using e0(2) by force
        show "open ((\<Union>x\<in>B1. ball x e0) - B1 \<inter> pts)"
          by (simp add: \<open>finite (B1 \<inter> pts)\<close> 
              finite_imp_sparse open_UN open_diff_sparse_pts)
        show "connected ((\<Union>x\<in>B1. ball x e0) - B1 \<inter> pts)"
        proof (rule connected_open_delete_finite)
          show "connected (\<Union>x\<in>B1. ball x e0)"
            using connected_B1_ball[OF \<open>e0>0\<close>] .
        qed (use \<open>finite (B1 \<inter> pts)\<close> in auto)

        show "compact ((\<Union>x\<in>B1. cball x e) - inside (path_image \<gamma>))"
          using \<open>compact (\<Union>x\<in>B1. cball x e)\<close> assms(2) 
            closed_valid_path_image compact_diff open_inside 
          by blast
        
        have "(\<Union>x\<in>B1. cball x e) \<subseteq> (\<Union>x\<in>B1. ball x e0)" 
          unfolding e_def using \<open>e0>0\<close> by force
        moreover have " B1 \<inter> pts \<subseteq> inside (path_image \<gamma>)" 
          unfolding B1_def using DiffE UnE assms(4) by auto
        ultimately show "(\<Union>x\<in>B1. cball x e) - inside (path_image \<gamma>)
            \<subseteq> (\<Union>x\<in>B1. ball x e0) - B1 \<inter> pts"
          by auto
        show "\<beta> \<in> (\<Union>x\<in>B1. ball x e0) - B1 \<inter> pts"
          by (metis Diff_iff IntD2 UN_iff \<open>\<beta> \<in> B1\<close> \<open>\<beta> \<notin> pts\<close> centre_in_ball e0(1))
        show "f \<beta> \<noteq> 0" by fact
      qed
      moreover have "((B3-B1) \<inter> -pts \<inter> {x. f x =0})
          \<subseteq> {z \<in> (\<Union>x\<in>B1. cball x e) - inside (path_image \<gamma>). f z = 0}"
        unfolding B3_def B1_def using \<open>e>0\<close> by force
      ultimately show ?thesis by (elim rev_finite_subset)
    qed
    moreover have "finite (B3 \<inter> pts)" 
    proof -
      have "finite ((\<Union>x\<in>B1. cball x e) \<inter> pts)"
      proof (rule finite_not_islimpt_in_compact)
        show "\<not> z islimpt pts" if "z \<in> (\<Union>x\<in>B1. cball x e)" for z 
        proof -
          have "z\<in>B2" using e0(2) that \<open>e0>0\<close> unfolding e_def by force
          then show ?thesis by (simp add: not_islimpt_B2)
        qed
      qed fact
      moreover have "(B3 \<inter> pts) \<subseteq> ((\<Union>x\<in>B1. cball x e) \<inter> pts)"
        unfolding pz_def B3_def by auto
      ultimately show ?thesis by (elim finite_subset)
    qed
    ultimately show ?thesis by auto
  qed
  have f_holo: "f holomorphic_on B3 - (B1 \<inter> pts)" 
  proof -
    have "B3 - (B1 \<inter> pts) \<subseteq> B2 - (B1\<inter> pts)"
      using e0 unfolding B3_def e_def by force
    then show ?thesis using f_B2_holo by fast
  qed
  have "connected B3" 
    by (simp add: B3_def \<open>0 < e\<close> connected_B1_ball)

  define c where "c \<equiv> 2 * complex_of_real pi * \<i> "
  define ff where "ff \<equiv> (\<lambda>x. deriv f x / f x)"
  define cont where "cont \<equiv> \<lambda>ff p e. (ff has_contour_integral c * zorder f p) (circlepath p e)"
  define avoid where "avoid \<equiv> \<lambda>p e. \<forall>w\<in>cball p e. w \<in> B3 \<and> (w \<noteq> p \<longrightarrow> w \<notin> pz)"

  have "\<exists>e>0. avoid p e \<and> (p\<in>pz \<longrightarrow> cont ff p e)" when "p\<in>B3" for p
  proof -
    obtain e1 where "e1>0" and e1_avoid: "avoid p e1"
      using finite_cball_avoid[OF \<open>open B3\<close> \<open>finite pz\<close>] \<open>p\<in>B3\<close> unfolding avoid_def by auto
    have "\<exists>e2>0. cball p e2 \<subseteq> ball p e1 \<and> cont ff p e2" when "p\<in>pz"
    proof -
      define po where "po \<equiv> zorder f p"
      define pp where "pp \<equiv> zor_poly f p"
      define f' where "f' \<equiv> \<lambda>w. pp w * (w - p) powi po"
      define ff' where "ff' \<equiv> (\<lambda>x. deriv f' x / f' x)"
      obtain r where "pp p\<noteq>0" "r>0" and
          "r<e1" and
          pp_holo: "pp holomorphic_on cball p r" and
          pp_po: "(\<forall>w\<in>cball p r-{p}. f w = pp w * (w - p) powi po \<and> pp w \<noteq> 0)"
      proof -
        have "isolated_singularity_at f p"
        proof -
          have "f holomorphic_on ball p e1 - {p}"
            apply (intro holomorphic_on_subset[OF f_holo])
            using e1_avoid \<open>p\<in>pz\<close> unfolding avoid_def pz_def by force
          then show ?thesis unfolding isolated_singularity_at_def
            using \<open>e1>0\<close> analytic_on_open open_delete by blast
        qed
        moreover have "not_essential f p" 
          using \<open>p \<in> pz\<close> not_essential pz_def 
          by (meson DiffI IntD2 \<open>finite (B1 \<inter> pts)\<close> \<open>open B3\<close> \<open>p \<in> B3\<close> 
              f_holo finite_imp_closed not_essential_holomorphic open_Diff)
        moreover have "\<exists>\<^sub>F w in at p. f w \<noteq> 0"
        proof (rule ccontr)
          assume "\<not> (\<exists>\<^sub>F w in at p. f w \<noteq> 0)"
          then have "\<forall>\<^sub>F w in at p. f w= 0" unfolding frequently_def by auto

          have "\<forall>\<^sub>F w in at p. f w \<noteq> 0 \<and> w \<in> B3 - B1 \<inter> pts"
          proof (rule nconst_sparse_imp_nzero_neighbour)
            have "\<beta> \<in> B3 - B1 \<inter> pts" 
              by  (metis B3_def Diff_iff IntE SUP_upper 
                  \<open>0 < e\<close> \<open>\<beta> \<in> B1\<close> \<open>\<beta> \<notin> pts\<close> \<open>open B3\<close> open_contains_ball_eq)
            then show " \<not> (\<forall>w\<in>B3 - B1 \<inter> pts. f w = 0)"
              using \<open>f \<beta>\<noteq>0\<close> by blast
            show "B1 \<inter> pts sparse_in B3"
              by (simp add: \<open>finite (B1 \<inter> pts)\<close> finite_imp_sparse)
          qed fact+
          then have "\<forall>\<^sub>F w in at p. False" using \<open>\<forall>\<^sub>F w in at p. f w= 0\<close>
            by eventually_elim simp
          then show False by simp
        qed
        ultimately obtain r where "pp p \<noteq> 0" and r: "r>0" "pp holomorphic_on cball p r"
                  "(\<forall>w\<in>cball p r - {p}. f w = pp w * (w - p) powi po \<and> pp w \<noteq> 0)"
          using zorder_exist[of f p,folded po_def pp_def] by auto
        define r1 where "r1=min r e1 / 2"
        have "r1<e1" unfolding r1_def using \<open>e1>0\<close> \<open>r>0\<close> by auto
        moreover have "r1>0" "pp holomorphic_on cball p r1"
                  "(\<forall>w\<in>cball p r1 - {p}. f w = pp w * (w - p) powi po \<and> pp w \<noteq> 0)"
          unfolding r1_def using \<open>e1>0\<close> r by auto
        ultimately show ?thesis using that \<open>pp p\<noteq>0\<close> by auto
      qed

      define e2 where "e2 \<equiv> r/2"
      have "e2>0" using \<open>r>0\<close> unfolding e2_def by auto
      define anal where "anal \<equiv> \<lambda>w. deriv pp w/ pp w"
      define prin where "prin \<equiv> \<lambda>w. po/ (w - p)"
      have "((\<lambda>w.  prin w + anal w) has_contour_integral c * po) (circlepath p e2)"
      proof (rule has_contour_integral_add[of _ _ _ _ 0,simplified])
        have "ball p r \<subseteq> B3"
          using \<open>r<e1\<close> avoid_def ball_subset_cball e1_avoid by (simp add: subset_eq)
        then have "cball p e2 \<subseteq> B3"
          using \<open>r>0\<close> unfolding e2_def by auto
        then show "(prin has_contour_integral c * po) (circlepath p e2)"
          unfolding prin_def
          apply (intro Cauchy_integral_circlepath_simple[folded c_def])
          using \<open>e2>0\<close> by auto
        have "anal holomorphic_on ball p r" unfolding anal_def
          using pp_holo pp_po \<open>ball p r \<subseteq> B3\<close> \<open>pp p\<noteq>0\<close>
          by (auto intro!: holomorphic_intros)
        then show "(anal has_contour_integral 0) (circlepath p e2)"
          using e2_def \<open>r>0\<close>
          by (auto elim!: Cauchy_theorem_disc_simple)
      qed
      then have "cont ff' p e2" unfolding cont_def po_def
      proof (elim has_contour_integral_eq)
        fix w assume "w \<in> path_image (circlepath p e2)"
        then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
        define wp where "wp \<equiv> w-p"
        have "wp\<noteq>0" and "pp w \<noteq>0"
          unfolding wp_def using \<open>w\<noteq>p\<close> \<open>w\<in>ball p r\<close> pp_po by auto
        moreover have der_f': "deriv f' w = po * pp w * (w-p) powi (po - 1) + deriv pp w * (w-p) powi po"
        proof (rule DERIV_imp_deriv)
          have "(pp has_field_derivative (deriv pp w)) (at w)"
            using DERIV_deriv_iff_has_field_derivative pp_holo \<open>w\<noteq>p\<close>
            by (meson open_ball \<open>w \<in> ball p r\<close> ball_subset_cball holomorphic_derivI holomorphic_on_subset)
          then show " (f' has_field_derivative of_int po * pp w * (w - p) powi (po - 1)
                  + deriv pp w * (w - p) powi po) (at w)"
            unfolding f'_def using \<open>w\<noteq>p\<close>
            by (auto intro!: derivative_eq_intros DERIV_cong[OF has_field_derivative_powr_of_int])
        qed
        ultimately show "prin w + anal w = ff' w"
          unfolding ff'_def prin_def anal_def
          apply simp
          apply (unfold f'_def)
          apply (fold wp_def)
          apply (auto simp add:field_simps)
          by (metis (no_types, lifting) mult.commute power_int_minus_mult)
      qed
      then have "cont ff p e2" unfolding cont_def
      proof (elim has_contour_integral_eq)
        fix w assume "w \<in> path_image (circlepath p e2)"
        then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
        have "deriv f' w =  deriv f w"
        proof (rule complex_derivative_transform_within_open[where s="ball p r - {p}"])
          show "f' holomorphic_on ball p r - {p}" unfolding f'_def using pp_holo
            by (auto intro!: holomorphic_intros)
        next
          have "ball p e1 - {p} \<subseteq> B3 - pts"
            using ball_subset_cball e1_avoid[unfolded avoid_def] unfolding pz_def
            by auto
          then have "ball p r - {p} \<subseteq> B3 - pts"
            apply (elim dual_order.trans)
            using \<open>r<e1\<close> by auto
          then show "f holomorphic_on ball p r - {p}" 
            using f_holo by auto
        next
          show "open (ball p r - {p})" by auto
          show "w \<in> ball p r - {p}" using \<open>w\<in>ball p r\<close> \<open>w\<noteq>p\<close> by auto
        next
          fix x assume "x \<in> ball p r - {p}"
          then show "f' x = f x"
            using pp_po unfolding f'_def by auto
        qed
        moreover have " f' w  =  f w "
          using \<open>w \<in> ball p r\<close> ball_subset_cball subset_iff pp_po \<open>w\<noteq>p\<close>
          unfolding f'_def by auto
        ultimately show "ff' w = ff w"
          unfolding ff'_def ff_def by simp
      qed
      moreover have "cball p e2 \<subseteq> ball p e1"
        using \<open>0 < r\<close> \<open>r<e1\<close> e2_def by auto
      ultimately show ?thesis using \<open>e2>0\<close> by auto
    qed
    then obtain e2 where e2: "p\<in>pz \<longrightarrow> e2>0 \<and> cball p e2 \<subseteq> ball p e1 \<and> cont ff p e2"
      by auto
    define e4 where "e4 \<equiv> if p\<in>pz then e2 else  e1"
    have "e4>0" using e2 \<open>e1>0\<close> unfolding e4_def by auto
    moreover have "avoid p e4" using e2 \<open>e1>0\<close> e1_avoid unfolding e4_def avoid_def by auto
    moreover have "p\<in>pz \<longrightarrow> cont ff p e4"
      by (auto simp add: e2 e4_def)
    ultimately show ?thesis by auto
  qed
  then obtain get_e where get_e: "\<forall>p\<in>B3. get_e p>0 \<and> avoid p (get_e p)
      \<and> (p\<in>pz \<longrightarrow> cont ff p (get_e p))"
    by metis
  define ci where "ci \<equiv> \<lambda>p. contour_integral (circlepath p (get_e p)) ff"
  define w where "w \<equiv> \<lambda>p. winding_number \<gamma> p"
  have "contour_integral \<gamma> ff = (\<Sum>p\<in>pz. w p * ci p)" unfolding ci_def w_def
  proof (rule Cauchy_theorem_singularities)
    have "open (B3 - pz)" using open_Diff[OF _ finite_imp_closed[OF \<open>finite pz\<close>]] \<open>open B3\<close> 
      by auto
    then show "ff holomorphic_on B3 - pz" unfolding ff_def using f_holo 
      by (auto intro!: holomorphic_intros simp add:pz_def)
    show "\<forall>p\<in>B3. 0 < get_e p \<and> (\<forall>w\<in>cball p (get_e p). w \<in> B3 \<and> (w \<noteq> p \<longrightarrow> w \<notin> pz))"
      using get_e using avoid_def by blast
    show "open B3" "connected B3" "finite pz" "valid_path \<gamma>" "pathfinish \<gamma> = pathstart \<gamma>"
      by fact+

    show "path_image \<gamma> \<subseteq> B3 - pz" 
    proof -
      have "path_image \<gamma> \<subseteq> B3" 
        unfolding B3_def B1_def  using \<open>e>0\<close> by auto
      moreover have "path_image \<gamma> \<subseteq> - pts" 
        using ComplI assms(4) by auto
      moreover have "path_image \<gamma> \<subseteq> - {x. f x = 0}" 
        using assms(4) f_nz by auto
      ultimately show ?thesis unfolding pz_def by auto
    qed

    have "winding_number \<gamma> z = 0" if "z \<notin> B3" for z
    proof (rule winding_number_zero_in_outside)
      show "z \<in> outside (path_image \<gamma>)"
        by (metis B1_def B3_def ComplI SUP_upper \<open>0 < e\<close> \<open>open B3\<close> 
            open_contains_ball_eq that union_with_inside)
      show "path \<gamma>" by (simp add: assms(2) valid_path_imp_path)
    qed fact
    then show " \<forall>z. z \<notin> B3 \<longrightarrow> winding_number \<gamma> z = 0" by simp
  qed
  also have "... = (\<Sum>p\<in>pz. c * w p * zorder f p)"
  proof (rule sum.cong[of pz pz,simplified])
    fix p assume "p \<in> pz"
    show "w p * ci p = c * w p * (zorder f p)"
    proof (cases "p\<in>B3")
      assume "p \<in> B3"
      have "ci p = c * (zorder f p)" unfolding ci_def
        apply (rule contour_integral_unique)
        using get_e \<open>p\<in>B3\<close> \<open>p\<in>pz\<close> unfolding cont_def by metis
      thus ?thesis by auto
    next (*TODO: simplify*)
      assume "p\<notin>B3"
      then have "w p=0" unfolding w_def 
        using \<open>p \<in> pz\<close> pz_def by auto
      then show ?thesis by auto
    qed
  qed
  also have "... = c*(\<Sum>p\<in>pz. w p * zorder f p)"
    unfolding sum_distrib_left by (simp add:algebra_simps)
  also have "... = c*(\<Sum>p\<in>(pz\<inter>B1). w p * zorder f p)"
  proof -
    have "(\<Sum>p\<in>pz. w p * zorder f p) 
            = (\<Sum>p\<in>(pz\<inter>B1). w p * zorder f p)"
    proof (rule sum.mono_neutral_right)
      show "\<forall>x\<in>pz - pz \<inter> B1. w x * complex_of_int (zorder f x) = 0"
      proof 
        fix x assume "x \<in> pz - pz \<inter> B1"
        then have "x \<in> outside (path_image \<gamma>)" unfolding B1_def
          by (auto simp add:  union_with_inside)
        then have "w x = 0"
          unfolding w_def using winding_number_zero_in_outside
          by (simp add: assms(2) assms(3) valid_path_imp_path)
        then show "w x * complex_of_int (zorder f x) = 0" by simp
      qed
      show "finite pz" by fact
      show "pz \<inter> B1 \<subseteq> pz" by simp
    qed
    then show ?thesis by simp
  qed
  also have "... = c*(\<Sum>p\<in>(B1 \<inter> pts). w p * zorder f p)"
  proof -
    have "B1 \<subseteq> B3" unfolding B3_def using \<open>e>0\<close> by auto
    moreover have "{x. f x = 0}\<inter>B1 \<subseteq> pts \<inter> B1 " 
      using f_nz unfolding B1_def 
      by (smt (verit, del_insts) Diff_iff Int_iff UnE assms(4)
          local.inside_subset mem_Collect_eq subset_eq)
    ultimately have "pz\<inter>B1 = (B1 \<inter> pts)" unfolding pz_def by auto
    then show ?thesis by auto
  qed
  also have "... = c*(\<Sum>\<^sub>\<infinity>p\<in>(B1 \<inter> pts). w p * zorder f p)"
    using \<open>finite (B1 \<inter> pts)\<close> by auto
  also have "... = c*(\<Sum>\<^sub>\<infinity>p\<in>pts. w p * zorder f p)"
  proof -
    have "(\<Sum>\<^sub>\<infinity>p\<in>(B1 \<inter> pts). w p * zorder f p) 
              = (\<Sum>\<^sub>\<infinity>p\<in>pts. w p * zorder f p)"
    proof (rule infsum_cong_neutral)
      fix x assume "x \<in> pts - B1 \<inter> pts" 
      then have "x \<in> outside (path_image \<gamma>)" unfolding B1_def
        by (auto simp add:  union_with_inside)
      then have "w x = 0"
        unfolding w_def using winding_number_zero_in_outside
        by (simp add: assms(2) assms(3) valid_path_imp_path)
      then show "w x * complex_of_int (zorder f x) = 0" by simp
    qed auto
    then show ?thesis by simp
  qed
  finally show ?thesis unfolding ff_def c_def w_def by simp
qed

corollary argument_principle_finite:
  fixes f:: "complex \<Rightarrow> complex"
  assumes f_analytic: "f analytic_on A - pts" and
          \<gamma>: "valid_path \<gamma>" "pathfinish \<gamma> = pathstart \<gamma>" "path_image \<gamma> \<subseteq> A - pts" and
          inside_subset: "inside (path_image \<gamma>) \<subseteq> A" and
          not_essential: "\<forall>p\<in>pts. not_essential f p" and 
          sparse: "finite pts" and
          f_nz: "\<And>z. z \<in> A - pts \<Longrightarrow> f z \<noteq> 0" 
  shows "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) = 2 * pi * \<i> *
          (\<Sum>z\<in>pts. winding_number \<gamma> z * zorder f z)"
proof -
  have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) = 2 * pi * \<i> *
          (\<Sum>\<^sub>\<infinity> z\<in>pts. winding_number \<gamma> z * zorder f z)"
  proof (rule argument_principle_sparse)
    show " pts sparse_in A" 
      by (simp add: finite_imp_sparse \<open>finite pts\<close>)
  qed fact+
  moreover have "(\<Sum>\<^sub>\<infinity> z\<in>pts. winding_number \<gamma> z * zorder f z)
    = (\<Sum>z\<in>pts. winding_number \<gamma> z * zorder f z)"
    by (rule infsum_finite) fact
  ultimately show ?thesis by simp
qed

corollary argument_principle_ccw_analytic:
  fixes f:: "complex \<Rightarrow> complex"
  assumes f_analytic: "f analytic_on A - pts" and
          \<gamma>: "valid_path \<gamma>" "simple_loop_ccw \<gamma>" "path_image \<gamma> \<subseteq> A - pts" and
          inside_subset: "inside (path_image \<gamma>) \<subseteq> A" and
          not_essential: "\<forall>p\<in>pts. not_essential f p" and 
          sparse: "pts sparse_in A" and
          f_nz: "\<And>z. z \<in> A - pts \<Longrightarrow> f z \<noteq> 0" 
  shows "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) = 2 * pi * \<i> *
          (\<Sum>z\<in>pts\<inter>inside (path_image \<gamma>). zorder f z)"
proof -
  have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) =
          2 * pi * \<i> * (\<Sum>\<^sub>\<infinity>z\<in>pts. winding_number \<gamma> z * (zorder f z))"   
  proof (rule argument_principle_sparse)
    show "pathfinish \<gamma> = pathstart \<gamma>" 
      by (metis \<gamma>(2) simple_loop_ccw_def simple_loop_def)
  qed fact+

  moreover have "(\<Sum>\<^sub>\<infinity>z\<in>pts. winding_number \<gamma> z * (zorder f z))
    = (\<Sum>z\<in>pts\<inter>inside (path_image \<gamma>). complex_of_int (zorder f z))" (is "?L=?R")
  proof - 
    have "?L = (\<Sum>\<^sub>\<infinity>z\<in>pts \<inter> inside (path_image \<gamma>). 
                winding_number \<gamma> z * (zorder f z))"
    proof (rule infsum_cong_neutral)
      fix x assume "x \<in> pts - pts \<inter> inside (path_image \<gamma>)"
      then have "x \<in> outside (path_image \<gamma>)"
        using \<gamma>(2) \<gamma>(3)
        by (metis DiffE Int_iff Set.basic_monos(7)
            inside_simple_loop_iff outside_simple_loop_iff simple_loop_ccw_def)
      then have "winding_number \<gamma> x =0" 
        using \<gamma>(2) outside_simple_loop_iff simple_loop_ccw_def by blast
      then show "winding_number \<gamma> x * complex_of_int (zorder f x) = 0" 
        by simp
    qed auto
    also have "... = (\<Sum>z\<in>pts \<inter> inside (path_image \<gamma>). 
                  winding_number \<gamma> z * (zorder f z))"
    proof (rule infsum_finite)
      define B1 where "B1 = path_image \<gamma> \<union> inside (path_image \<gamma>)"
      have "compact B1"
      proof -
        have "closed B1" unfolding B1_def 
          apply (rule closed_path_image_Un_inside)
          by (simp add: \<gamma>(1) valid_path_imp_path)
        moreover have "bounded B1" unfolding B1_def 
          by (simp add: \<gamma>(1) bounded_inside bounded_path_image valid_path_imp_path)
        ultimately show ?thesis using compact_eq_bounded_closed by auto
      qed
      moreover have "pts sparse_in B1" 
        unfolding B1_def using assms(4) assms(5) assms(7) 
        by (meson Diff_subset dual_order.trans sparse_in_subset sup_least)
      ultimately have "finite (B1 \<inter> pts)"
        using sparse_in_compact_finite by auto
      then show "finite (pts \<inter> inside (path_image \<gamma>))" 
        apply (elim rev_finite_subset)
        unfolding B1_def by auto
    qed
    also have "... = ?R" 
    proof (rule sum.cong)
      fix x assume "x \<in> pts \<inter> inside (path_image \<gamma>)"
      then have "winding_number \<gamma> x = 1" 
        by (metis IntD2 \<gamma>(2) inside_simple_loop_iff 
            simple_closed_path_winding_number_inside 
            simple_loop_ccw_def simple_loop_cw_def simple_loop_def
            simple_path_not_cw_and_ccw)
      then show "winding_number \<gamma> x *  zorder f x = zorder f x" by simp
    qed simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed

end
(*>*)