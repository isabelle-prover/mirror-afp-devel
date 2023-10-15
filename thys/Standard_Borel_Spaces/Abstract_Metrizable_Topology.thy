(*  Title:   Abstract_Metrizable_Topology.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Abstract Metrizable Topology\<close>
theory Abstract_Metrizable_Topology
  imports "Set_Based_Metric_Product"
begin

subsection \<open> Metrizable Spaces \<close>
locale metrizable =
  fixes S :: "'a topology"
  assumes ex_metric:"\<exists>\<rho>. metric_set (topspace S) \<rho> \<and> S = metric_set.mtopology (topspace S) \<rho>"
begin

lemma metric:
  obtains \<rho> where "metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
  using ex_metric by metis

lemma bounded_metric:
  obtains \<rho> where "metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
                  "\<And>x y. \<rho> x y < 1"
proof -
  obtain \<rho> where "metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
    by(rule metric)
  then have "\<exists>\<rho>. metric_set (topspace S) \<rho> \<and> metric_set.mtopology (topspace S) \<rho> = S \<and> (\<forall>x y. \<rho> x y < 1)"
    using metric_set.bounded_dist_dist(1) metric_set.bounded_dist_dist(2) metric_set.bounded_dist_generate_same_topology
    by(fastforce intro!: exI[where x="bounded_dist \<rho>"])
  thus ?thesis
    using that by auto
qed

lemma second_countable_if_separable:
  assumes "separable S"
  shows "second_countable S"
proof -
  obtain d where hd:"metric_set (topspace S) d" "S = metric_set.mtopology (topspace S) d"
    using ex_metric by(auto simp: metrizable_def)
  then interpret m: separable_metric_set "topspace S" d
    using metric_set.separable_iff_topological_separable[of "topspace S" d] assms
    by auto
  show "second_countable S"
    using m.second_countable \<open>S = m.mtopology\<close> by simp
qed

corollary second_countable_iff_separable: "second_countable S \<longleftrightarrow> separable S"
  using second_countable_if_separable separable_if_second_countable
  by auto

lemma Hausdorff: "Hausdorff_space S"
  using ex_metric metric_set.mtopology_Hausdorff by fastforce

lemma subtopology: "metrizable (subtopology S X)"
proof -
  obtain \<rho> where h:"metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
    by(rule metric)
  then show ?thesis
    using metric_set.submetric_subtopology[OF h(1),of "topspace S \<inter> X"]
    by(auto intro!: exI[where x="submetric (topspace S \<inter> X) \<rho>"] simp: metrizable_def subtopology_restrict metric_set.mtopology_topspace metric_set.submetric_metric_set)
qed

lemma g_delta_of_closedin:
  assumes "closedin S X"
  shows "g_delta_of S X"
  using assms ex_metric metric_set.g_delta_of_closed by fastforce

lemma closedin_singleton:
  assumes "s \<in> topspace S"
  shows "closedin S {s}"
proof -
  obtain \<rho> where h:"metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
    by(rule metric)
  then show ?thesis
    using metric_set.closedin_closed_ball[OF h(1),of s 0]
    by(simp add: metric_set.closed_ball_0[OF h(1) assms])
qed

lemma dense_of_infinite:
  assumes "infinite (topspace S)" "dense_of S U"
  shows "infinite U"
proof -
  obtain \<rho> where h:"metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
    by(rule metric)
  show ?thesis
    by(rule metric_set.dense_set_infinite[OF h(1),simplified h(2),OF assms])
qed

lemma homeomorphic_metrizable:
  assumes "S homeomorphic_space S'"
  shows "metrizable S'"
proof(rule metric)
  fix d
  assume h: "metric_set (topspace S) d" "metric_set.mtopology (topspace S) d = S"
  then interpret m: metric_set "topspace S" d by simp
  from assms obtain f g where fg: "homeomorphic_maps S S' f g"
    by(auto simp: homeomorphic_space_def)
  hence g: "g \<in> topspace S' \<rightarrow> topspace S" "inj_on g (topspace S')" "g ` (topspace S') = topspace S"
    by (auto simp: homeomorphic_eq_injective_perfect_map homeomorphic_maps_map perfect_map_def)
  have f: "f \<in> topspace S \<rightarrow> topspace S'" "inj_on f (topspace S)" "f ` (topspace S) = topspace S'"
    using fg  by (auto simp: homeomorphic_eq_injective_perfect_map homeomorphic_maps_map perfect_map_def)
  interpret m': metric_set "topspace S'" "m.ed g (topspace S')"
    by(simp add:  m.embed_dist_dist[OF g(1,2)])
  show "metrizable S'"
    unfolding metrizable_def
  proof(safe intro!: exI[where x="m.ed g (topspace S')"])
    have [simp]:"m'.ed f (topspace S) = d"
      by standard+ (insert f g fg m.dist_notin m.dist_notin',auto simp: m'.embed_dist_on_def m.embed_dist_on_def homeomorphic_maps_def)
    have [simp]:"((`) f ` {m.open_ball a \<epsilon> |a \<epsilon>. a \<in> topspace S \<and> 0 < \<epsilon>}) = {m'.open_ball a \<epsilon> |a \<epsilon>. a \<in> topspace S' \<and> 0 < \<epsilon>}"
    proof safe
      fix a and e :: real
      assume "a \<in> topspace S" "0 < e"
      then show "\<exists>b e'. f ` m.open_ball a e = m'.open_ball b e' \<and> b \<in> topspace S' \<and> 0 < e'"
        using f g fg by(auto simp: m.open_ball_def m'.open_ball_def m.embed_dist_on_def homeomorphic_maps_def intro!: exI[where x="f a"] exI[where x=e])  (metis (no_types, lifting) image_eqI mem_Collect_eq)
    next
      fix a and e :: real
      assume "a \<in> topspace S'" "0 < e"
      then show "m'.open_ball a e \<in> (`) f ` {m.open_ball a \<epsilon> |a \<epsilon>. a \<in> topspace S \<and> 0 < \<epsilon>}"
        using m'.embed_dist_open_ball[OF f(1,2),simplified,of "g a" e] f g fg m'.open_ballD'(1)
        by(auto simp:  m.embed_dist_on_def homeomorphic_maps_def image_def intro!: exI[where x="g a"] exI[where x=e] exI[where x="m.open_ball (g a) e"]) blast
    qed
    show "S' = m'.mtopology"
      using topology_generated_by_homeomorphic_spaces[OF homeomorphic_maps_imp_map[OF fg] h(2)[symmetric,simplified m.mtopology_def2]]
      by(simp add: m'.mtopology_def2)
  qed(rule m'.metric_set_axioms)
qed

end

lemma euclidean_metrizable: "metrizable (euclidean :: ('a ::metric_space) topology)"
  by (metis euclidean_mtopology metric_class_metric_set metrizable.intro topspace_euclidean)

sublocale metric_set \<subseteq> metrizable "mtopology"
  using metric_set_axioms metrizable_def mtopology_topspace by fastforce

lemma metrizable_prod:
  assumes "metrizable X" "metrizable Y"
  shows "metrizable (prod_topology X Y)"
proof
  obtain dx dy where "metric_set (topspace X) dx" "metric_set.mtopology (topspace X) dx = X" "metric_set (topspace Y) dy" "metric_set.mtopology (topspace Y) dy = Y"
    using metrizable.metric[OF assms(2)] metrizable.metric[OF assms(1)] by metis
  then show "\<exists>\<rho>. metric_set (topspace (prod_topology X Y)) \<rho> \<and> prod_topology X Y = metric_set.mtopology (topspace (prod_topology X Y)) \<rho>"
    by(auto intro!: exI[where x="binary_distance (topspace X) dx (topspace Y) dy"] simp: binary_metric_set binary_distance_mtopology)
qed

lemma metrizable_product:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> metrizable (X i)"
  shows "metrizable (product_topology X I)"
proof -
  obtain d where hd:"\<And>i. i \<in> I \<Longrightarrow> metric_set (topspace (X i)) (d i)" "\<And>i. i \<in> I \<Longrightarrow> X i = metric_set.mtopology (topspace (X i)) (d i)"
    using assms(2) by(auto simp: metrizable_def) metis
  from product_metricI'[of "1/2" _ _ d,OF _ _ assms(1) this(1)]
  interpret pd: product_metric "1 / 2" I "to_nat_on I" "from_nat_into I" "\<lambda>i. topspace (X i)" "\<lambda>i x y. if i \<in> I then bounded_dist (d i) x y else 0" 1
    by simp
  show ?thesis
    using hd(2) by(auto simp: metrizable_def pd.product_dist_distance pd.product_dist_mtopology[symmetric] hd(1) metric_set.bounded_dist_generate_same_topology intro!: exI[where x=pd.product_dist] product_topology_cong)
qed

subsection \<open> Complete Metrizable Spaces \<close>
locale complete_metrizable =
  fixes S :: "'a topology"
  assumes ex_cmetric: "\<exists>\<rho>. complete_metric_set (topspace S) \<rho> \<and> S = metric_set.mtopology (topspace S) \<rho>"
begin

lemma cmetric:
  obtains \<rho> where "complete_metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
  using ex_cmetric by metis

lemma bounded_cmetric:
  obtains \<rho> where "complete_metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
                  "\<And>x y. \<rho> x y < 1"
proof -
  obtain \<rho> where "complete_metric_set (topspace S) \<rho>" "metric_set.mtopology (topspace S) \<rho> = S"
    by(rule cmetric)
  then have "\<exists>\<rho>. complete_metric_set (topspace S) \<rho> \<and> metric_set.mtopology (topspace S) \<rho> = S \<and> (\<forall>x y. \<rho> x y < 1)"
    using metric_set.bounded_dist_dist(1) metric_set.bounded_dist_dist(2) metric_set.bounded_dist_generate_same_topology complete_metric_set.bounded_dist_complete complete_metric_set_def
    by(fastforce intro!: exI[where x="bounded_dist \<rho>"])
  thus ?thesis
    using that by auto
qed

lemma metrizable: "metrizable S"
  using complete_metric_set_def complete_metrizable_axioms complete_metrizable_def metrizable_def by blast

sublocale metrizable
  by(rule metrizable)

lemma closedin_complete_metrizable:
  assumes "closedin S A"
  shows "complete_metrizable (subtopology S A)"
  by (metis assms closedin_def complete_metric_set.submetric_complete_iff complete_metric_set_def complete_metrizable_axioms complete_metrizable_def metric_set.submetric_subtopology topspace_subtopology_subset)

lemma homeomorphic_complete_metrizable:
  assumes "S homeomorphic_space S'"
  shows "complete_metrizable S'"
proof(rule cmetric)
  fix d
  assume h: "complete_metric_set (topspace S) d" "metric_set.mtopology (topspace S) d = S"
  then interpret m: complete_metric_set "topspace S" d by simp
  from assms obtain f g where fg: "homeomorphic_maps S S' f g"
    by(auto simp: homeomorphic_space_def)
  hence g: "g \<in> topspace S' \<rightarrow> topspace S" "inj_on g (topspace S')" "g ` (topspace S') = topspace S"
    by (auto simp: homeomorphic_eq_injective_perfect_map homeomorphic_maps_map perfect_map_def)
  have f: "f \<in> topspace S \<rightarrow> topspace S'" "inj_on f (topspace S)" "f ` (topspace S) = topspace S'"
    using fg  by (auto simp: homeomorphic_eq_injective_perfect_map homeomorphic_maps_map perfect_map_def)
  interpret m': complete_metric_set "topspace S'" "m.ed g (topspace S')"
    by(auto intro!: m.embed_dist_complete[OF g(1,2)] simp: h(2) g(3))
  show "complete_metrizable S'"
    unfolding complete_metrizable_def
  proof(safe intro!: exI[where x="m.ed g (topspace S')"])
    have [simp]:"m'.ed f (topspace S) = d"
      by standard+ (insert f g fg m.dist_notin m.dist_notin',auto simp: m'.embed_dist_on_def m.embed_dist_on_def homeomorphic_maps_def)
    have [simp]:"((`) f ` {m.open_ball a \<epsilon> |a \<epsilon>. a \<in> topspace S \<and> 0 < \<epsilon>}) = {m'.open_ball a \<epsilon> |a \<epsilon>. a \<in> topspace S' \<and> 0 < \<epsilon>}"
    proof safe
      fix a and e :: real
      assume "a \<in> topspace S" "0 < e"
      then show "\<exists>b e'. f ` m.open_ball a e = m'.open_ball b e' \<and> b \<in> topspace S' \<and> 0 < e'"
        using f g fg by(auto simp: m.open_ball_def m'.open_ball_def m.embed_dist_on_def homeomorphic_maps_def intro!: exI[where x="f a"] exI[where x=e])  (metis (no_types, lifting) image_eqI mem_Collect_eq)
    next
      fix a and e :: real
      assume "a \<in> topspace S'" "0 < e"
      then show "m'.open_ball a e \<in> (`) f ` {m.open_ball a \<epsilon> |a \<epsilon>. a \<in> topspace S \<and> 0 < \<epsilon>}"
        using m'.embed_dist_open_ball[OF f(1,2),simplified,of "g a" e] f g fg m'.open_ballD'(1)
        by(auto simp:  m.embed_dist_on_def homeomorphic_maps_def image_def intro!: exI[where x="g a"] exI[where x=e] exI[where x="m.open_ball (g a) e"]) blast
    qed
    show "S' = m'.mtopology"
      using topology_generated_by_homeomorphic_spaces[OF homeomorphic_maps_imp_map[OF fg] h(2)[symmetric,simplified m.mtopology_def2]]
      by(simp add: m'.mtopology_def2)
  qed(rule m'.complete_metric_set_axioms)
qed

end

lemma euclidean_complete_metrizable[simp]:
 "complete_metrizable (euclidean :: ('a ::complete_space) topology)"
  by (metis complete_metrizable.intro complete_space_complete_metric_set euclidean_mtopology topspace_euclidean)

sublocale complete_metric_set \<subseteq> complete_metrizable "mtopology"
  using complete_metric_set_axioms complete_metrizable_def mtopology_topspace by fastforce

lemma complete_metrizable_prod:
  assumes "complete_metrizable X" "complete_metrizable Y"
  shows "complete_metrizable (prod_topology X Y)"
proof
  obtain dx dy where "complete_metric_set (topspace X) dx" "metric_set.mtopology (topspace X) dx = X" "complete_metric_set (topspace Y) dy" "metric_set.mtopology (topspace Y) dy = Y"
    using complete_metrizable.cmetric[OF assms(2)] complete_metrizable.cmetric[OF assms(1)] by metis
  then show "\<exists>\<rho>. complete_metric_set (topspace (prod_topology X Y)) \<rho> \<and> prod_topology X Y = metric_set.mtopology (topspace (prod_topology X Y)) \<rho>"
    using binary_distance_complete by(auto intro!: exI[where x="binary_distance (topspace X) dx (topspace Y) dy"] simp:  binary_distance_mtopology complete_metric_set_def)
qed

lemma complete_metrizable_product:
  assumes "countable I" "\<And>i. i \<in> I \<Longrightarrow> complete_metrizable (X i)"
  shows "complete_metrizable (product_topology X I)"
proof -
  obtain d where hd:"\<And>i. i \<in> I \<Longrightarrow> complete_metric_set (topspace (X i)) (d i)" "\<And>i. i \<in> I \<Longrightarrow> X i = metric_set.mtopology (topspace (X i)) (d i)"
    using assms(2) by(auto simp: complete_metrizable_def) metis
  from product_complete_metricI'[of "1/2" _ _ d,OF _ _ assms(1) this(1)]
  interpret pd: product_complete_metric "1 / 2" I "to_nat_on I" "from_nat_into I" "\<lambda>i. topspace (X i)" "\<lambda>i x y. if i \<in> I then bounded_dist (d i) x y else 0" 1
    by simp
  show ?thesis
    using hd(2) by(auto simp: complete_metrizable_def pd.product_dist_distance pd.product_dist_mtopology[symmetric] hd(1) complete_metric_set.axioms(1) metric_set.bounded_dist_generate_same_topology pd.complete_metric_set_axioms intro!: exI[where x=pd.product_dist] product_topology_cong)
qed

lemma(in complete_metrizable) g_delta_of_complete_metrizable:
  assumes "g_delta_of S B"
  shows "complete_metrizable (subtopology S B)"
proof -
  obtain d where d:"complete_metric_set (topspace S) d" "metric_set.mtopology (topspace S) d = S"
    by(rule cmetric)
  interpret m: complete_metric_set "topspace S" d by fact
  obtain U :: "nat \<Rightarrow> _" where U: "\<And>n. openin S (U n)" "B = \<Inter> (range U)"
    using g_delta_ofD'[OF assms] by metis
  consider "topspace (subtopology S B) = {}" | "topspace (subtopology S B) = topspace S" | "topspace (subtopology S B) \<noteq> {}" "topspace (subtopology S B) \<subset> topspace S"
    by (metis assms g_delta_of_subset order_le_less topspace_subtopology_subset)
  then show ?thesis
  proof cases
    case 1
    with empty_metric_polish show ?thesis
      by(auto intro!: exI[where x="\<lambda>x y. 0"] simp: complete_metrizable_def polish_metric_set_def separable_metric_set_def Int_absorb1 assms empty_metric_mtopology g_delta_of_subset subtopology_eq_discrete_topology_eq)
  next
    case 2
    then have "B = topspace S"
      using g_delta_of_subset[OF assms] by auto
    thus ?thesis
      by(simp add: complete_metrizable_axioms)
  next
    case 3
    then have h: "B \<noteq> {}" "\<And>n. U n \<noteq> {}" by(auto simp: U(2))
    define f where "f \<equiv> (\<lambda>x. (x, (\<lambda>i. 1 / m.dist_set (topspace S - (U i)) x)))"
    have f_inj:"inj f"
      by(auto simp: inj_def f_def)
    have f_inv: "\<And>x. x \<in> f ` B \<Longrightarrow> f (fst x) = x" "\<And>x. fst (f x) = x"
      by(auto simp: f_def)
    have "continuous_map (subtopology S B) (prod_topology S (powertop_real UNIV)) f"
      unfolding continuous_map_pairwise continuous_map_componentwise_UNIV
    proof safe
      have [simp]:"fst \<circ> f = id"
        by(auto simp: f_def)
      show "continuous_map (subtopology S B) S (fst \<circ> f)"
        by simp
    next
      fix k
      show "continuous_map (subtopology S B) euclideanreal (\<lambda>x. (snd \<circ> f) x k)"
      proof(cases "U k = topspace S")
        case True
        then show ?thesis
          by(simp add: f_def)
      next
        case False
        then have [simp]:"(\<lambda>x. snd (f x) k) = (\<lambda>x. 1 / m.dist_set (topspace S - (U k)) x)"
          by(simp add: f_def)
        have "continuous_map (subtopology S B) euclideanreal ..."
        proof(rule continuous_map_real_divide)
          show "continuous_map (subtopology S B) euclideanreal (m.dist_set (topspace S - U k))"
            using m.dist_set_continuous[simplified d(2),of "topspace S - U k"]
            by (simp add: continuous_map_from_subtopology)
        next
          fix x
          assume "x \<in> topspace (subtopology S B)"
          then have h':"x \<in> topspace S" "x \<in> B" by auto
          have 1: "closedin S (topspace S - U k)" "topspace S - U k \<noteq> {}"
            using U(1) d(2) m.mtopology_openin_iff2 False by auto 
          with h'(2) m.dist_set_closed_ge0[simplified d(2),OF 1 h'(1)]
          show "m.dist_set (topspace S - U k) x \<noteq> 0"
           by(auto simp: U(2))
        qed simp
        thus ?thesis by simp
      qed
    qed
    hence f_cont: "continuous_map (subtopology S B) (subtopology (prod_topology S (powertop_real UNIV)) (f ` B)) f"
      using g_delta_of_subset[OF assms] by(auto simp: continuous_map_in_subtopology)
    have f_invcont: "continuous_map (subtopology (prod_topology S (powertop_real UNIV)) (f ` B)) (subtopology S B) fst"
      by(auto intro!: continuous_map_into_subtopology simp: continuous_map_subtopology_fst f_def)

    have homeo: "subtopology (prod_topology S (powertop_real UNIV)) (f ` B) homeomorphic_space subtopology S B"
      using f_inv(2) by(auto simp: homeomorphic_space_def homeomorphic_maps_def f_cont f_invcont intro!: exI[where x=f] exI[where x=fst])

    show ?thesis
    proof(safe intro!: complete_metrizable.homeomorphic_complete_metrizable[OF _ homeo] complete_metrizable.closedin_complete_metrizable[of _ "f ` B"] complete_metrizable_prod complete_metrizable_product complete_metrizable_axioms)
      interpret r: polish_metric_set UNIV "dist :: real \<Rightarrow> _" by simp
      interpret pd: product_complete_metric "1/2" UNIV id id "\<lambda>n. UNIV" "\<lambda>n. bounded_dist (dist :: real \<Rightarrow> _)" 1
        by(auto intro!: product_complete_metric_natI' simp: r.complete_metric_set_axioms)
      interpret bpd: complete_metric_set "topspace S \<times> (\<Pi>\<^sub>E x\<in>(UNIV::nat set). (UNIV::real set))" "binary_distance (topspace S) d (\<Pi>\<^sub>E x\<in>(UNIV::nat set). (UNIV::real set)) pd.product_dist"
        using pd.complete_metric_set_axioms by(auto intro!: binary_distance_complete d(1))

      have "closedin bpd.mtopology (f ` B)"
      proof -
        { fix a b and zn :: "nat \<Rightarrow> _"
          assume h':"zn \<in> UNIV \<rightarrow> f ` B" "m.converge_to_inS (\<lambda>n. fst (zn n)) a" "\<forall>i. r.converge_to_inS (\<lambda>n. snd (zn n) i) (b i)"
          then obtain xn where xn: "\<And>n. xn n \<in> B" "\<And>n. zn n = f (xn n)"
            by (metis PiE UNIV_I f_inv(2) imageE)

          have h: "m.converge_to_inS xn a" "\<And>i. r.converge_to_inS (\<lambda>n. 1 / m.dist_set (topspace S - U i) (xn n)) (b i)"
          proof -
            {
              fix i
              have "(\<lambda>n. snd (zn n) i) = (\<lambda>n. 1 / m.dist_set (topspace S - U i) (xn n))"
                by standard (simp add: xn(2) f_def)
            }
            thus "m.converge_to_inS xn a" "\<And>i. r.converge_to_inS (\<lambda>n. 1 / m.dist_set (topspace S - U i) (xn n)) (b i)"
              using h' by(auto simp: xn(2) f_def)
          qed
          have conv1: "r.converge_to_inS (\<lambda>n. m.dist_set (topspace S - U i) (xn n)) (m.dist_set (topspace S - U i) a)" for i
            using m.dist_set_continuous h(1) by(simp add: metric_set_continuous_map_eq'[OF m.metric_set_axioms r.metric_set_axioms,simplified euclidean_mtopology])
          have dista_n0:"m.dist_set (topspace S - U i) a \<noteq> 0" if "U i \<noteq> topspace S" for i
          proof(rule LIMSEQ_inverse_not0[OF _ conv1[simplified converge_to_def_set[symmetric]] h(2)[simplified converge_to_def_set[symmetric]]])
            fix n
            have "0 < m.dist_set (topspace S - U i) (xn n)"
              using xn(1) U(1)[of i] by(auto intro!: m.dist_set_closed_ge0 simp: U(2) d(2) in_mono openin_subset) (use openin_subset that in blast)+
            thus "m.dist_set (topspace S - U i) (xn n) \<noteq> 0" by simp
          qed
          from tendsto_inverse_real[OF conv1[simplified converge_to_def_set[symmetric]] this]
          have conv1':"r.converge_to_inS (\<lambda>n. 1 / m.dist_set (topspace S - U i) (xn n)) (1 / m.dist_set (topspace S - U i) a)" if "U i \<noteq> topspace S" for i
            by(simp add: that converge_to_def_set)   
          have "a \<in> U n" for n
          proof(cases "U n = topspace S")
            case True
            then show ?thesis
              using h'(2) by(auto simp: m.converge_to_inS_def)
          next
            case False
            with m.dist_set_nzeroD(2)[OF dista_n0[OF this]] dista_n0
            show ?thesis
              by fastforce
          qed
          hence "a \<in> B"
            by(auto simp: U(2))
          moreover have "b n = 1 / m.dist_set (topspace S - (U n)) a" for n
          proof(cases "U n = topspace S")
            case True
            then show ?thesis
              using h(2)[of n,simplified converge_to_def_set[symmetric]]
              by (simp add: LIMSEQ_const_iff)
          next
            case False
            from conv1'[OF this] h(2)[of n]
            show ?thesis
              by(simp add: r.converge_to_inS_unique)
          qed
          ultimately have "(a, b) \<in> f ` B"
            by(auto simp: f_def image_def)
        }
        thus ?thesis
          unfolding bpd.mtopology_closedin_iff binary_distance_converge_to_inS_iff'[OF m.metric_set_axioms pd.metric_set_axioms]
          using pd.converge_to_iff[simplified r.bounded_dist_converge_to_inS_iff[symmetric]] g_delta_of_subset[OF assms] f_def
          by auto
      qed
     thus "closedin (prod_topology S (powertop_real UNIV)) (f ` B)"
        by(simp only: binary_distance_mtopology[OF m.metric_set_axioms pd.metric_set_axioms] pd.product_dist_mtopology[symmetric] r.bounded_dist_generate_same_topology[symmetric] euclidean_mtopology d(2))
    qed simp_all
  qed
qed

corollary(in complete_metrizable) openin_complete_metrizable:
  assumes "openin S u"
  shows "complete_metrizable (subtopology S u)"
  using assms by(auto intro!: g_delta_of_complete_metrizable )

subsection \<open> Polish Spaces \<close>
locale polish_topology = complete_metrizable +
  assumes S_separable:"separable S"
begin

lemma S_second_countable: "second_countable S"
  by(rule second_countable_if_separable[OF S_separable])

lemma closedin_polish:
  assumes "closedin S A"
  shows "polish_topology (subtopology S A)"
  by (simp add: S_second_countable assms closedin_complete_metrizable polish_topology_axioms_def polish_topology_def second_countable_subtopology separable_if_second_countable)

lemma g_delta_of_polish:
  assumes "g_delta_of S A"
  shows "polish_topology (subtopology S A)"
  by(simp add: polish_topology_def g_delta_of_complete_metrizable[OF assms] polish_topology_axioms_def S_second_countable second_countable_subtopology separable_if_second_countable)

corollary openin_polish:
  assumes "openin S A"
  shows "polish_topology (subtopology S A)"
  by (simp add: assms g_delta_of_polish)

lemma homeomorphic_polish_topology:
  assumes "S homeomorphic_space S'"
  shows "polish_topology S'"
  by(simp add: polish_topology_def homeomorphic_complete_metrizable[OF assms] homeomorphic_separable[OF S_separable assms] polish_topology_axioms_def)

end

lemma polish_topology_def2:
 "polish_topology S \<longleftrightarrow> (\<exists>\<rho>. polish_metric_set (topspace S) \<rho> \<and> S = metric_set.mtopology (topspace S) \<rho>)"
  by (metis complete_metric_set.axioms(1) complete_metrizable_def metric_set.separable_iff_topological_separable polish_metric_set.axioms(1) polish_metric_set.axioms(2) polish_metric_set.intro polish_topology_axioms_def polish_topology_def)

lemma(in polish_topology) polish_metric:
  obtains d where "polish_metric_set (topspace S) d"
              and "S = metric_set.mtopology (topspace S) d"
  using polish_topology_axioms by(auto simp: polish_topology_def2)

lemma(in polish_topology) bounded_polish_metric:
  obtains d where "polish_metric_set (topspace S) d"
              and "S = metric_set.mtopology (topspace S) d"
              and  "\<And>x y. d x y < 1"
proof -
  obtain d where d:"polish_metric_set (topspace S) d" "S = metric_set.mtopology (topspace S) d"
    by(rule polish_metric)
  interpret d: polish_metric_set "topspace S" d by fact
  have "\<exists>d'. polish_metric_set (topspace S) d' \<and> S = metric_set.mtopology (topspace S) d' \<and> (\<forall>x y. d' x y < 1)"
    using d  by(auto intro!: exI[where x="bounded_dist d"] polish_metric_set.bounded_dist_polish simp:d.bounded_dist_generate_same_topology d.bounded_dist_dist)
  with that show ?thesis
    by auto
qed

sublocale polish_metric_set \<subseteq> polish_topology mtopology
  using mtopology_topspace by(auto simp: polish_topology_def2 polish_metric_set_axioms intro!: exI[where x=dist])

lemma polish_topology_euclidean[simp]: "polish_topology (euclidean :: ('a :: polish_space) topology)"
  using polish_class_polish_set
  by(auto simp: polish_topology_def2 intro!: exI[where x=dist]) (use open_openin open_openin_set topology_eq in blast)

lemma polish_topology_countable[simp]:
  "polish_topology (euclidean :: 'a :: {countable,discrete_topology} topology)"
proof -
  interpret polish_metric_set "UNIV :: 'a set" "discrete_dist UNIV"
    by(simp add: discrete_dist_polish_iff)
  show ?thesis
    unfolding polish_topology_def2
    by(auto intro!: exI[where x="discrete_dist UNIV"] simp: topology_eq polish_metric_set_axioms discrete_dist_topology[of "UNIV :: 'a set"] discrete_topology_class.open_discrete)
qed

lemma polish_topology_prod:
  assumes "polish_topology S" and "polish_topology S'"
  shows "polish_topology (prod_topology S S')"
proof -
  obtain \<rho> \<rho>' where hr:
   "polish_metric_set (topspace S) \<rho>" "S = metric_set.mtopology (topspace S) \<rho>"
   "polish_metric_set (topspace S') \<rho>'" "S' = metric_set.mtopology (topspace S') \<rho>'"
    using assms by(auto simp: polish_topology_def2)
  interpret m1:polish_metric_set "topspace S" \<rho> by fact
  interpret m2:polish_metric_set "topspace S'" \<rho>' by fact
  interpret m: polish_metric_set "topspace S \<times> topspace S'" "binary_distance (topspace S) \<rho> (topspace S') \<rho>'"
    by(auto intro!: binary_distance_polish simp: m1.polish_metric_set_axioms m2.polish_metric_set_axioms)
  show ?thesis
    unfolding polish_topology_def2
    using binary_distance_mtopology[OF m1.metric_set_axioms m2.metric_set_axioms,simplified space_pair_measure[symmetric]] hr(2,4)
    by(auto intro!: exI[where x="binary_distance (topspace S) \<rho> (topspace S') \<rho>'"] m.polish_metric_set_axioms)
qed

lemma polish_topology_product:
  assumes "countable I" and "\<And>i. i \<in> I \<Longrightarrow> polish_topology (S i)"
  shows "polish_topology (product_topology S I)"
proof -
  obtain \<rho> where hr:
   "\<And>i. i \<in> I \<Longrightarrow> polish_metric_set (topspace (S i)) (\<rho> i)" "\<And>i. i \<in> I \<Longrightarrow> S i = metric_set.mtopology (topspace (S i)) (\<rho> i)"
    using assms(2) by(auto simp: polish_topology_def2) metis
  define \<rho>' where "\<rho>' \<equiv> (\<lambda>i x y. if i \<in> I then bounded_dist (\<rho> i) x y else 0)"
  interpret pd: product_polish_metric "1/2" I "to_nat_on I" "from_nat_into I" "\<lambda>i. topspace (S i)" \<rho>' 1
    using assms hr by(auto intro!: product_polish_metricI' simp: \<rho>'_def)
  have "product_topology S I = product_topology (\<lambda>i. metric_set.mtopology (topspace (S i)) (\<rho> i)) I"
    by(auto intro!: product_topology_cong hr(2))
  also have "... = product_topology (\<lambda>i. metric_set.mtopology (topspace (S i)) (\<rho>' i)) I"
    by(auto intro!: product_topology_cong simp: \<rho>'_def)
      (use hr(1) metric_set.bounded_dist_generate_same_topology polish_metric_set.axioms(2) separable_metric_set_def in blast)
  also have "... = pd.mtopology"
    by(rule pd.product_dist_mtopology)
  finally have "product_topology S I = pd.mtopology" .
  show ?thesis
    unfolding polish_topology_def2
    by(auto intro!: exI[where x="pd.product_dist"] simp: pd.polish_metric_set_axioms) fact
qed

lemma polish_topology_closedin_polish:
  assumes "polish_topology S" and "closedin S U"
  shows "polish_topology (subtopology S U)"
proof -
  obtain \<rho> where *:
   "polish_metric_set (topspace S) \<rho>" "S = metric_set.mtopology (topspace S) \<rho>"
    using assms by(auto simp: polish_topology_def2)
  interpret m:polish_metric_set "topspace S" \<rho> by fact
  interpret m':polish_metric_set U "submetric U \<rho>"
    using m.submetric_complete_iff[OF closedin_subset[OF assms(2)]] m.submetric_separable[OF closedin_subset[OF assms(2)]] assms(2) *
    by(simp add: polish_metric_set_def)
  have "subtopology S U = m'.mtopology"
    using m.submetric_subtopology[OF closedin_subset[OF assms(2)]] * by simp
  thus ?thesis
    using m'.mtopology_topspace
    by(auto simp: polish_topology_def2 m'.polish_metric_set_axioms intro!: exI[where x="submetric U \<rho>"])
qed

subsection \<open> Compact Metrizable Spaces \<close>
locale compact_metrizable = metrizable +
  assumes compact: "compact_space S"
begin

sublocale polish_topology
proof -
  obtain d where "compact_metric_set (topspace S) d" "metric_set.mtopology (topspace S) d = S"
    using metric compact by(auto simp: compact_metric_set_def compact_metric_set_axioms.intro)
  then interpret m: polish_metric_set "topspace S" d
    by(simp add: compact_metric_set.polish)
  show "polish_topology S"
    using \<open>m.mtopology = S\<close> m.polish_topology_axioms by simp
qed

lemma compact_metric:
  obtains d where "compact_metric_set (topspace S) d" "metric_set.mtopology (topspace S) d = S"
  by (metis metric compact compact_metric_set.intro compact_metric_set_axioms.intro)

end

subsection \<open>Continuous Embddings\<close>
abbreviation Hilbert_cube_as_topology :: "(nat \<Rightarrow> real) topology" where
"Hilbert_cube_as_topology \<equiv> (product_topology (\<lambda>n. top_of_set {0..1}) UNIV)"

lemma topspace_Hilbert_cube: "topspace Hilbert_cube_as_topology = (\<Pi>\<^sub>E x\<in>UNIV. {0..1})"
  by simp

lemma Hilbert_cube_Polish_topology: "polish_topology Hilbert_cube_as_topology"
  by(auto intro!: polish_topology_closedin_polish polish_topology_product)

abbreviation Cantor_space_as_topology :: "(nat \<Rightarrow> real) topology" where
"Cantor_space_as_topology \<equiv> (product_topology (\<lambda>n. top_of_set {0,1}) UNIV)"

lemma topspace_Cantor_space:
 "topspace Cantor_space_as_topology = (\<Pi>\<^sub>E x\<in>UNIV. {0,1})"
  by simp

lemma Cantor_space_Polish_topology:
 "polish_topology Cantor_space_as_topology"
  by(auto intro!: polish_topology_closedin_polish polish_topology_product)

text \<open> Proposition 2.2.3 in \cite{borelsets} \<close>
lemma continuous_map_metrizable_extension:
  assumes "A \<subseteq> topspace W" "metrizable W" "complete_metrizable Z" "continuous_map (subtopology W A) Z f"
  shows "\<exists>h gd. g_delta_of W gd \<and> (\<forall>a\<in>A. f a = h a) \<and> A \<subseteq> gd \<and> continuous_map (subtopology W gd) Z h"
proof -
  obtain dz where hdz: "complete_metric_set (topspace Z) dz" "metric_set.mtopology (topspace Z) dz = Z" "\<And>x y. dz x y < 1"
    using complete_metrizable.bounded_cmetric[OF assms(3)] by auto
  interpret dz: complete_metric_set "topspace Z" dz by fact
  obtain dw where hdw: "metric_set (topspace W) dw" "metric_set.mtopology (topspace W) dw = W"
    using metrizable.metric[OF assms(2)] by auto
  interpret dw: metric_set "topspace W" dw by fact
  interpret subd: metric_set A "submetric A dw"
    using assms by(auto intro!: dw.submetric_metric_set)
  have "subd.mtopology = subtopology W A"
    using assms(1) dw.submetric_subtopology hdw(2) by auto
  let ?oscf = "dz.osc_on A W f"
  define gd where "gd \<equiv> {x\<in>W closure_of A. ?oscf x = 0}"
  have g_delta: "g_delta_of W gd"
  proof -
    have *:"{x\<in>W closure_of A. ?oscf x < t} = \<Union> {V \<inter> (W closure_of A)| V. openin W V \<and> dz.diam (f ` (A \<inter> V)) < t}" for t
      by(auto simp: dz.osc_on_less_iff)
    have 1:"gd = \<Inter> {{x\<in>W closure_of A. ?oscf x < 1 / real n}|n. n \<in> {0<..}}"
    proof -
      have "x \<in> gd" if h:"\<And>n. n \<in> {0<..} \<Longrightarrow> x \<in> {x\<in>W closure_of A. ?oscf x < 1 / real n}" for x
      proof -
        have "?oscf x < \<epsilon>" if he:"\<epsilon>>0" for \<epsilon>
        proof -
          obtain n where  "1 / real (Suc n) < \<epsilon>"
            by (meson enn2real_le_iff enn2real_positive_iff ennreal_less_top ennreal_less_zero_iff he linorder_not_le nat_approx_posE order_le_less_trans)
          thus ?thesis
            using h[of "Suc n"] by auto
        qed
        hence "?oscf x = 0"
          using not_gr_zero by blast
        thus ?thesis
          using that by(auto simp: gd_def)
      qed
      thus ?thesis
        by (auto simp: gd_def)
    qed
    also have "... = \<Inter> {\<Union> {V \<inter> (W closure_of A)| V. openin W V \<and> dz.diam (f ` (A \<inter> V)) < 1 / real n}|n. n \<in> {0<..}}"
      using * by auto
    also have "... = W closure_of A \<inter> \<Inter> {\<Union> {V. openin W V \<and> dz.diam (f ` (A \<inter> V)) < 1 / real n}|n. n \<in> {0<..}}"
      by blast
    also have "g_delta_of W ..."
    proof -
      have "{\<Union> {V. openin W V \<and> dz.diam (f ` (A \<inter> V)) < ennreal (1 / real n)} | n. 0 < n} = (\<lambda>n. \<Union> {V. openin W V \<and> dz.diam (f ` (A \<inter> V)) < ennreal (1 / real n)}) ` {0<..}" by auto
      also have "countable ..." by auto
      finally show ?thesis
        by(auto intro!: dw.g_delta_of_closed[simplified hdw(2),of "W closure_of A"] g_delta_of_inter[OF _ g_delta_ofI[of "{\<Union> {V. openin W V \<and> dz.diam (f ` (A \<inter> V)) < ennreal (1 / real n)} | n. n \<in> {0<..}}" _ "\<Inter> {\<Union> {V. openin W V \<and> dz.diam (f ` (A \<inter> V)) < 1 / real n}|n. 0 < n}"]] )
    qed
    finally show ?thesis .
  qed
  have oscf0: "?oscf a = 0" if "a \<in> A" for a
    using assms that by(auto intro!: osc_on_inA_0[OF dw.metric_set_axioms dz.metric_set_axioms,simplified \<open>dz.mtopology = Z\<close> \<open>dw.mtopology = W\<close>] simp: le_iff_inf)
  hence A_subst_of_gd: "A \<subseteq> gd"
    using closure_of_subset[OF assms(1)] by(auto simp add: gd_def)
  define h where "h x \<equiv> let xn = (SOME an. an \<in> UNIV \<rightarrow> A \<and> dw.converge_to_inS an x) in dz.the_limit_of (\<lambda>n. f (xn n))" for x
  have h_extends:"f a = h a" if "a \<in> A" for a
  proof -
    obtain an where han: "an \<in> UNIV \<rightarrow> A" "dw.converge_to_inS an a"
      using dw.closure_of_mtopology_an[of a A] A_subst_of_gd \<open>a \<in> A\<close> gd_def hdw(2) by auto
    show ?thesis
      unfolding h_def Let_def
    proof(rule someI2[of _ an "\<lambda>t. f a = dz.the_limit_of (\<lambda>n. f (t n))"])
      fix bn
      assume h:"bn \<in> UNIV \<rightarrow> A \<and> dw.converge_to_inS bn a"
      hence "subd.converge_to_inS bn a"
        using assms(1) dw.convergent_insubmetric that by fastforce
      hence "dz.converge_to_inS (\<lambda>n. f (bn n)) (f a)"
        using metric_set_continuous_map_eq'[OF subd.metric_set_axioms dz.metric_set_axioms,of f,simplified \<open>subd.mtopology = subtopology W A\<close> \<open>dz.mtopology = Z\<close> assms(4)]
        by auto
      thus "f a = dz.the_limit_of (\<lambda>n. f (bn n))"
        by(simp add: dz.the_limit_of_eq)
    qed(use han in auto)
  qed
  have "gd \<subseteq> topspace W"
    by(simp add: gd_def in_closure_of)
  then interpret subd_on_gd: metric_set gd "submetric gd dw"
    by(auto intro!: dw.submetric_metric_set)
  have "subtopology W gd = subd_on_gd.mtopology"
    using \<open>gd \<subseteq> topspace W\<close> dw.submetric_subtopology hdw(2) by auto
  have Cauchyf:"dz.Cauchy_inS (\<lambda>n. f (an n))" if "subd.Cauchy_inS an" "dw.converge_to_inS an a" "?oscf a = 0" for an a
  proof -
    have "{dz.diam (f ` (A \<inter> U)) |U. a \<in> U \<and> openin W U} = (\<lambda>U. dz.diam (f ` (A \<inter> U))) ` {U. a \<in> U \<and> openin W U}"
      by auto
    hence "(\<Sqinter>i\<in>{U. a \<in> U \<and> openin W U}. dz.diam (f ` (A \<inter> i))) = \<bottom>"
      using that(3) by(auto simp: dz.osc_on_def bot_ennreal)
    from this[simplified INF_eq_bot_iff]
    have "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>u\<in>{U. a \<in> U \<and> openin W U}. dz.diam (f ` (A \<inter> u)) < \<epsilon>"
      by(simp add: bot_ennreal)
    hence he:"\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>u\<in>{U. a \<in> U \<and> openin W U}. dz.diam (f ` (A \<inter> u)) < ennreal \<epsilon>"
      by auto
    show ?thesis
      unfolding dz.Cauchy_inS_def
    proof safe
      show "\<And>x. f (an x) \<in> topspace Z"
        using assms(1,4) subd.Cauchy_inS_dest1[OF that(1)] by(auto simp: continuous_map_def)
    next
      fix \<epsilon>
      assume "(0 :: real) < \<epsilon>"
      from he[OF this] obtain U where hu:"a \<in> U" "openin W U" "dz.diam (f ` (A \<inter> U)) < ennreal \<epsilon>"
        by auto
      then obtain e where he:"e > 0" "a \<in> dw.open_ball a e" "dw.open_ball a e \<subseteq> U"
        by (metis \<open>dw.converge_to_inS an a\<close> dw.metric_set_axioms dw.mtopology_openin_iff dw.open_ball_ina hdw(2) metric_set.converge_to_inS_def2')
      then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> an n \<in> dw.open_ball a e"
        using \<open>dw.converge_to_inS an a\<close> dw.converge_to_inS_def2' by blast
      hence hn: "\<And>n. n \<ge> N \<Longrightarrow> an n \<in> A \<inter> U"
        using he(3) that(1) by(auto simp: subd.Cauchy_inS_def)
      show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dz (f (an n)) (f (an m)) < \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n m
        assume "N \<le> n" "N \<le> m"
        then have "an n \<in> A \<inter> U" "an m \<in> A \<inter> U"
          using hn by auto
        hence "f (an n) \<in> f ` (A \<inter> U)" "f (an m) \<in> f ` (A \<inter> U)"
          by auto
        then have "ennreal (dz (f (an n)) (f (an m))) \<le> dz.diam (f ` (A \<inter> U))"
          using assms(4) subd.mtopology_topspace by(auto intro!: dz.diam_is_sup simp:\<open>subd.mtopology = subtopology W A\<close> continuous_map_def)
        also have "... < ennreal \<epsilon>" by fact
        finally show "dz (f (an n)) (f (an m)) < \<epsilon>"
          using dz.dist_geq0 by (simp add: ennreal_less_iff)
      qed
    qed
  qed
  have "continuous_map (subtopology W gd) Z h"
  proof -
    have h_image:"h \<in> gd \<rightarrow> topspace Z"
    proof
      fix x
      assume "x \<in> gd"
      then obtain xn where hxn: "xn \<in> UNIV \<rightarrow> A" "dw.converge_to_inS xn x"
        using dw.closure_of_mtopology_an[of x A] by(auto simp: gd_def hdw(2))
      show "h x \<in> topspace Z"
        unfolding h_def Let_def
      proof(rule someI2[of _ xn "\<lambda>t. dz.the_limit_of (\<lambda>n. f (t n)) \<in> topspace Z"])
        fix an
        assume "an \<in> subd.sequence \<and> dw.converge_to_inS an x"
        then have h:"an \<in> subd.sequence" "dw.converge_to_inS an x" by auto
        then have "dz.Cauchy_inS (\<lambda>n. f (an n))"
          using \<open>x \<in> gd\<close> by(auto intro!: Cauchyf[OF dw.Cauchy_insub_Cauchy_inverse[OF assms(1) h(1) dw.Cauchy_if_convergent_inS] h(2)] simp: gd_def dw.convergent_inS_def)
        thus "dz.the_limit_of (\<lambda>n. f (an n)) \<in> topspace Z"
          by(simp add: dz.convergence dz.the_limit_of_inS)
      qed(use hxn in auto)
    qed
    show ?thesis
      unfolding metric_set_continuous_map_eq[OF subd_on_gd.metric_set_axioms dz.metric_set_axioms,simplified \<open>subtopology W gd = subd_on_gd.mtopology\<close>[symmetric] \<open>dz.mtopology = Z\<close>]
    proof safe
      fix x and \<epsilon> :: real
      assume "x \<in> gd" "0 < \<epsilon>"
      then have "?oscf x < \<epsilon> / 3"
        by(auto simp: gd_def)
      then obtain u where hu: "openin W u" "x \<in> u" "dz.diam (f ` (A \<inter> u)) < \<epsilon> / 3"
        by(auto simp: dz.osc_on_def Inf_less_iff)
      hence "openin subd_on_gd.mtopology (u \<inter> gd)"
        by(auto simp : \<open>subtopology W gd = subd_on_gd.mtopology\<close>[symmetric] openin_subtopology)
      then obtain \<delta> where hd: "\<delta> > 0" "subd_on_gd.open_ball x \<delta> \<subseteq> u \<inter> gd" "x \<in> subd_on_gd.open_ball x \<delta>"
        by (metis Int_iff \<open>x \<in> gd\<close> hu(2) subd_on_gd.mtopology_openin_iff subd_on_gd.open_ball_ina)
      show "\<exists>\<delta>>0. \<forall>y\<in>gd. submetric gd dw x y < \<delta> \<longrightarrow> dz (h x) (h y) < \<epsilon>"
      proof(safe intro!: exI[where x=\<delta>] \<open>\<delta> > 0\<close>)
        fix y
        assume h':"y \<in> gd" "submetric gd dw x y < \<delta>"
        then have "y \<in> subd_on_gd.open_ball x \<delta>"
          by(simp add: \<open>x \<in> gd\<close> subd_on_gd.open_ball_def)
        then obtain \<delta>y where hdy: "\<delta>y > 0" "subd_on_gd.open_ball y \<delta>y \<subseteq> subd_on_gd.open_ball x \<delta>" "y \<in> subd_on_gd.open_ball y \<delta>y"
          using h'(1) subd_on_gd.mtopology_open_ball_in' subd_on_gd.open_ball_ina by blast
        obtain xn' yn' where hxyn':"xn' \<in> UNIV \<rightarrow> A" "dw.converge_to_inS xn' x" "yn' \<in> UNIV \<rightarrow> A" "dw.converge_to_inS yn' y"
          using dw.closure_of_mtopology_an[of _ A] \<open>y \<in> gd\<close> \<open>x \<in> gd\<close> by(simp add: gd_def hdw(2)) metis
        show "dz (h x) (h y) < \<epsilon>"
        proof -
          { fix xn yn
            assume hxyn:"xn \<in> subd.sequence" "dw.converge_to_inS xn x"
                        "yn \<in> subd.sequence" "dw.converge_to_inS yn y"
            then have Cauchyxyn: "dz.Cauchy_inS (\<lambda>n. f (xn n))" "dz.Cauchy_inS (\<lambda>n. f (yn n))"
              using Cauchyf[OF dw.Cauchy_insub_Cauchy_inverse[OF assms(1) hxyn(1) dw.Cauchy_if_convergent_inS] hxyn(2)] Cauchyf[OF dw.Cauchy_insub_Cauchy_inverse[OF assms(1) hxyn(3) dw.Cauchy_if_convergent_inS] hxyn(4)] \<open>x \<in> gd\<close> \<open>y \<in> gd\<close>
              by(auto simp: gd_def dw.convergent_inS_def)
            have convxyn:"subd_on_gd.converge_to_inS xn x" "subd_on_gd.converge_to_inS yn y"
              using hxyn \<open>x \<in> gd\<close> \<open>y \<in> gd\<close> \<open>A \<subseteq> gd\<close> by(auto intro!: dw.convergent_insubmetric \<open>gd \<subseteq> topspace W\<close>)
            then obtain Nx Ny where hnxy: "\<And>n. n \<ge> Nx \<Longrightarrow> xn n \<in> subd_on_gd.open_ball x \<delta>" "\<And>n. n \<ge> Ny \<Longrightarrow> yn n \<in> subd_on_gd.open_ball y \<delta>y"
              using hd(1) hdy(1) subd_on_gd.converge_to_inS_def2' by blast
            have "0 < \<epsilon> / 3" using \<open>0 < \<epsilon>\<close> by simp
            obtain Nfx Nfy where hnfxy: "\<And>n. n \<ge> Nfx \<Longrightarrow> dz (f (xn n)) (dz.the_limit_of (\<lambda>n. f (xn n))) < \<epsilon> / 3" "\<And>n. n \<ge> Nfy \<Longrightarrow> dz (f (yn n)) (dz.the_limit_of (\<lambda>n. f (yn n))) < \<epsilon> / 3"
              using dz.the_limit_if_converge[OF dz.convergence[OF Cauchyxyn(1)]] dz.the_limit_if_converge[OF dz.convergence[OF Cauchyxyn(2)]]
              by(auto simp: dz.converge_to_inS_def2) (meson \<open>0 < \<epsilon> / 3\<close> less_divide_eq_numeral1(1)) 
            define N where "N \<equiv> Max {Nx,Ny,Nfx,Nfy}"
            have N:"N \<ge> Nx" "N \<ge> Ny" "N \<ge> Nfx" "N \<ge> Nfy"
              by(simp_all add: N_def)
            have "dz (dz.the_limit_of (\<lambda>n. f (xn n))) (dz.the_limit_of (\<lambda>n. f (yn n))) < \<epsilon>"
                 (is "?lhs < _")
            proof -
              have "?lhs \<le> dz (dz.the_limit_of (\<lambda>n. f (xn n))) (f (xn N)) + dz (f (xn N)) (dz.the_limit_of (\<lambda>n. f (yn n)))"
                using dz.dist_tr[OF dz.the_limit_of_inS[OF dz.convergence[OF Cauchyxyn(1)]] _ dz.the_limit_of_inS[OF dz.convergence[OF Cauchyxyn(2)]],of \<open>f (xn N)\<close>] dz.Cauchy_inS_dest1[OF Cauchyxyn(1)]
                by simp
              also have "... \<le> dz (dz.the_limit_of (\<lambda>n. f (xn n))) (f (xn N)) + dz (f (xn N)) (f (yn N)) + dz (f (yn N)) (dz.the_limit_of (\<lambda>n. f (yn n)))"
                using dz.dist_tr[OF _ _ dz.the_limit_of_inS[OF dz.convergence[OF Cauchyxyn(2)]],of "f (xn N)" "f (yn N)"] dz.Cauchy_inS_dest1[OF Cauchyxyn(1)] dz.Cauchy_inS_dest1[OF Cauchyxyn(2)]
                by simp
              also have "... < \<epsilon> / 3 + dz (f (xn N)) (f (yn N)) + \<epsilon> / 3"
                using hnfxy[of N] N by(simp add: dz.dist_sym[of "dz.the_limit_of (\<lambda>n. f (xn n))"])
              also have "... < \<epsilon>"
              proof -
                have "xn N \<in> A \<inter> u" "yn N \<in> A \<inter> u"
                  using hdy(2) hd(2) hnxy[of N] N hxyn(1,3) by auto
                hence "ennreal (dz (f (xn N)) (f (yn N))) \<le> dz.diam (f ` (A \<inter> u))"
                  by(auto intro!: dz.diam_is_sup dz.Cauchy_inS_dest1[OF Cauchyxyn(1)] dz.Cauchy_inS_dest1[OF Cauchyxyn(2)])
                also have "... < ennreal (\<epsilon> / 3)" by fact
                finally have "dz (f (xn N)) (f (yn N)) < \<epsilon> / 3"
                  using dz.dist_geq0 ennreal_less_iff by blast
                thus ?thesis by simp
              qed
              finally show ?thesis .
            qed
          }
          note h = this
          show ?thesis
            apply(simp only: h_def[of x] Let_def)
            apply(rule someI2[of "\<lambda>k. k \<in> subd.sequence \<and> dw.converge_to_inS k x" xn',OF conjI[OF hxyn'(1,2)]])
            apply(simp only: h_def[of y] Let_def)
            apply(rule someI2[of "\<lambda>k. k \<in> subd.sequence \<and> dw.converge_to_inS k y" yn',OF conjI[OF hxyn'(3,4)]])
            using h by auto
        qed
      qed
    qed(use h_image in auto)
  qed

  with h_extends g_delta A_subst_of_gd
  show ?thesis by auto
qed

lemma Lavrentiev_theorem:
  assumes "complete_metrizable X" "complete_metrizable Y" "A \<subseteq> topspace X" "B \<subseteq> topspace Y" "homeomorphic_map (subtopology X A) (subtopology Y B) f"
  shows "\<exists>h gda gdb. g_delta_of X gda \<and> g_delta_of Y gdb \<and> A \<subseteq> gda \<and> B \<subseteq> gdb \<and> (\<forall>x\<in>A. f x = h x) \<and> homeomorphic_map (subtopology X gda) (subtopology Y gdb) h"
proof -
  interpret cmx: complete_metrizable X by fact
  interpret cmy: complete_metrizable Y by fact
  interpret mxy: metrizable "prod_topology X Y"
    by(auto intro!: metrizable_prod cmx.metrizable cmy.metrizable)
  obtain g where "homeomorphic_maps (subtopology X A) (subtopology Y B) f g"
    using assms(5) homeomorphic_map_maps by blast
  then have hfg: "continuous_map (subtopology X A) (subtopology Y B) f" "continuous_map (subtopology Y B) (subtopology X A) g"
                 "\<And>x. x \<in> A \<Longrightarrow> g (f x) = x" "\<And>y. y \<in> B \<Longrightarrow> f (g y) = y"
    using assms(3,4)  by(auto simp: homeomorphic_maps_def)
  obtain f' g' gda gdb where h:
   "g_delta_of X gda" "\<And>a. a \<in> A \<Longrightarrow> f a = f' a" "A \<subseteq> gda" "continuous_map (subtopology X gda) Y f'"
   "g_delta_of Y gdb" "\<And>b. b \<in> B \<Longrightarrow> g b = g' b" "B \<subseteq> gdb" "continuous_map (subtopology Y gdb) X g'"
    using continuous_map_metrizable_extension[OF assms(3) cmx.metrizable assms(2) continuous_map_into_fulltopology[OF hfg(1)]]
          continuous_map_metrizable_extension[OF assms(4) cmy.metrizable assms(1) continuous_map_into_fulltopology[OF hfg(2)]]
    by auto
  define H where "H \<equiv> SIGMA x:gda. {f' x}"
  have Heq:"H = {(x,y). x \<in> gda \<and> y \<in> topspace Y \<and> y = f' x}"
    using g_delta_of_subset[OF h(1)] h(4) by(auto simp: continuous_map_def H_def)
  define K where Keq:"K = {(x,y). x \<in> topspace X \<and> y \<in> gdb \<and> x = g' y}"
  define A' where "A' \<equiv> fst ` (H \<inter> K)"
  define B' where "B' \<equiv> snd ` (H \<inter> K)"
  have A'eq: "A' = {x \<in> gda. (x, f' x) \<in> K}"    
    using h(4)
    by (auto simp: A'_def Keq Heq image_def continuous_map_def Pi_def)
       (metis (mono_tags, lifting) IntI case_prod_conv fst_conv mem_Collect_eq)
  have B'eq: "B' = {y \<in> gdb. (g' y, y) \<in> H}"
    using h(8)
    by (auto simp: B'_def Keq Heq image_def continuous_map_def Pi_def)
       (metis (mono_tags, lifting) IntI case_prod_conv snd_conv mem_Collect_eq)
  have A'_gd: "g_delta_of X A'"
  proof -
    have K_gd:"g_delta_of (prod_topology X Y) K"
    proof - 
      have "closedin (subtopology (prod_topology X Y) (topspace X \<times> gdb)) K"
      proof -
        have "K = ((\<lambda>y. (g' y, y)) ` topspace (subtopology Y gdb))"
          using h(8) g_delta_of_subset[OF h(5)] by(auto simp add: Keq continuous_map_def)
        thus ?thesis
          using cmx.Hausdorff continuous_map_imp_closed_graph'[OF h(8)]
          by(auto simp: prod_topology_subtopology(2))
      qed
      then obtain T where hT:"closedin (prod_topology X Y) T" "K = T \<inter> (topspace X \<times> gdb)"
        using closedin_subtopology by metis
      thus ?thesis
        by(auto intro!: g_delta_of_inter g_delta_of_prod simp: h(5) mxy.g_delta_of_closedin)
    qed
    have "A' = ((\<lambda>x. (x,f' x)) -` K  \<inter> topspace (subtopology X gda))"
      by(auto simp add: A'eq Keq)
    also have "g_delta_of X ..."
      by(rule g_delta_of_subtopology_inverse[OF g_delta_of_continuous_map[OF _ K_gd] h(1)]) (auto intro!: continuous_map_pairedI h(4))
    finally show ?thesis .
  qed
  have A_subst_A': "A \<subseteq> A'"
  proof
    fix a
    assume 0:"a \<in> A"
    then have "f' a = f a" "f' a \<in> B"
      using h(2)[OF 0,symmetric] hfg(1) assms(3) by(auto simp: continuous_map_def)
    thus "a \<in> A'"
      using h(6)[OF \<open>f' a \<in> B\<close>,symmetric] hfg(3)[OF 0] 0 assms(3) h(3) h(7)
      by(auto simp: A'eq Keq)
  qed
  have B'_gd: "g_delta_of Y B'"
  proof -
    have H_gd:"g_delta_of (prod_topology X Y) H"
    proof - 
      have "closedin (subtopology (prod_topology X Y) (gda \<times> topspace Y)) H"
      proof -
        have "H = ((\<lambda>y. (y, f' y)) ` topspace (subtopology X gda))"
          using h(4) g_delta_of_subset[OF h(1)] by(auto simp add: Heq continuous_map_def)
        thus ?thesis
          using cmy.Hausdorff continuous_map_imp_closed_graph[OF h(4)]
          by(auto simp: prod_topology_subtopology(1))
      qed
      then obtain T where hT:"closedin (prod_topology X Y) T" "H = T \<inter> (gda \<times> topspace Y)"
        using closedin_subtopology by metis
      thus ?thesis
        by(auto intro!: g_delta_of_inter g_delta_of_prod simp: h(1) mxy.g_delta_of_closedin)
    qed
    have "B' = ((\<lambda>x. (g' x,x)) -` H  \<inter> topspace (subtopology Y gdb))"
      by(auto simp add: B'eq Heq)
    also have "g_delta_of Y ..."
      by(rule g_delta_of_subtopology_inverse[OF g_delta_of_continuous_map[OF _ H_gd] h(5)]) (auto intro!: continuous_map_pairedI h(8))
    finally show ?thesis .
  qed
  have B_subst_B': "B \<subseteq> B'"
  proof
    fix b
    assume 0:"b \<in> B"
    then have "g' b = g b" "g' b \<in> A"
      using h(6)[OF 0,symmetric] hfg(2) assms(4) by(auto simp: continuous_map_def)
    thus "b \<in> B'"
      using h(2)[OF \<open>g' b \<in> A\<close>,symmetric] hfg(4)[OF 0] 0 assms(4) h(3) h(7)
      by(auto simp: B'eq Heq)
  qed
  have "homeomorphic_map (subtopology X A') (subtopology Y B') f'"
  proof(rule homeomorphic_maps_imp_map[where g=g'])
    show "homeomorphic_maps (subtopology X A') (subtopology Y B')
     f' g'"
      unfolding homeomorphic_maps_def
    proof safe
      show "continuous_map (subtopology X A') (subtopology Y B') f'"
        using g_delta_of_subset[OF h(5)]
        by(auto intro!: continuous_map_into_subtopology continuous_map_from_subtopology_mono[OF h(4)] simp: A'eq B'eq Heq Keq)
    next
      show "continuous_map (subtopology Y B') (subtopology X A') g'"
        using g_delta_of_subset[OF h(1)]
        by(auto intro!: continuous_map_into_subtopology continuous_map_from_subtopology_mono[OF h(8)] simp: A'eq B'eq Heq Keq)
    qed(auto simp: A'eq B'eq Keq Heq)
  qed

  with A'_gd B'_gd A_subst_A' B_subst_B' h(2)
  show ?thesis by auto
qed

corollary(in complete_metrizable) complete_metrizable_subtopology_is_g_delta:
  assumes "A \<subseteq> topspace S" "complete_metrizable (subtopology S A)"
  shows "g_delta_of S A"
proof -
  obtain h gda gdb where h:
   "g_delta_of S gda" "g_delta_of (subtopology S A) gdb" "A \<subseteq> gda" "A \<subseteq> gdb" "\<forall>x\<in>A. x = h x" "homeomorphic_map (subtopology (subtopology S A) gdb) (subtopology S gda) h"
    using Lavrentiev_theorem[OF assms(2) complete_metrizable_axioms _ assms(1),of A id] assms(1)
    by simp (metis subtopology_topspace topspace_subtopology_subset)
  have "gdb = A"
    using g_delta_of_subset[OF h(2)] h(4) assms(1) by auto
  hence "homeomorphic_map (subtopology S A) (subtopology S gda) h"
    using h(6) by (simp add: subtopology_subtopology)
  hence "homeomorphic_map (subtopology S A) (subtopology S gda) id"
    by(rule homeomorphic_map_eq) (use assms(1) h(5) in auto)
  hence "subtopology S A = subtopology S gda" by simp
  hence "A = gda"
    by (metis assms(1) g_delta_of_subset h(1) topspace_subtopology_subset)
  thus ?thesis
    by(simp add: h(1))
qed

corollary(in complete_metrizable) subtopology_complete_metrizable_iff:
  assumes "A \<subseteq> topspace S"
  shows "complete_metrizable (subtopology S A) \<longleftrightarrow> g_delta_of S A"
  by(auto simp : g_delta_of_complete_metrizable complete_metrizable_subtopology_is_g_delta[OF assms])

corollary complete_metrizable_homeo_image_g_delta:
  assumes "complete_metrizable X" "complete_metrizable Y" "B \<subseteq> topspace Y" "X homeomorphic_space subtopology Y B"
  shows "g_delta_of Y B"
proof -
  obtain f where f:"homeomorphic_map X (subtopology Y B) f"
    using assms(4) homeomorphic_space by blast
  obtain h gda gdb where h:
   "g_delta_of X gda" "g_delta_of Y gdb" "topspace X \<subseteq> gda" "B \<subseteq> gdb" "\<forall>x\<in>topspace X. f x = h x" "homeomorphic_map (subtopology X gda) (subtopology Y gdb) h"
    using Lavrentiev_theorem[OF assms(1,2) subset_refl assms(3),simplified,OF f] by metis
  hence [simp]: "gda = topspace X"
    using g_delta_of_subset by blast
  have "homeomorphic_map X (subtopology Y gdb) f"
    using h(5,6) by(auto intro!: homeomorphic_map_eq[where f=h])
  hence "f ` topspace X = B" "f ` topspace X = gdb"
    using homeomorphic_imp_surjective_map[OF f] assms(3) g_delta_of_subset[OF h(2)] h(4) homeomorphic_imp_surjective_map[OF \<open>homeomorphic_map X (subtopology Y gdb) f\<close>]
    by auto
  with h(2) show ?thesis by auto
qed

lemma(in metrizable) embedding_into_Hilbert_cube:
  assumes "separable S"
  shows "\<exists>A \<subseteq> topspace Hilbert_cube_as_topology. S homeomorphic_space (subtopology Hilbert_cube_as_topology A)"
proof -
  consider "topspace S = {}" | "topspace S \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(auto intro!: exI[where x="{}"] simp: homeomorphic_empty_space_eq)
  next
    case S_ne:2
    then obtain U where U:"countable U" "dense_of S U" "U \<noteq> {}"
      using assms(1) by(auto simp: separable_def dense_of_nonempty)
    obtain xn where xn:"\<And>n::nat. xn n \<in> U" "U = range xn"
      by (metis U(1) U(3) from_nat_into range_from_nat_into)
    then have xns:"xn n \<in> topspace S" for n
      using dense_of_subset[OF U(2)] by auto
    obtain d where d:"metric_set (topspace S) d" "metric_set.mtopology (topspace S) d = S" "\<And>x y. d x y < 1"
      using bounded_metric by auto
    interpret ms: metric_set "topspace S" d by fact
    define f where "f \<equiv> (\<lambda>x n. d x (xn n))"
    have f_inj:"inj_on f (topspace S)"
    proof
      fix x y
      assume xy:"x \<in> topspace S" "y \<in> topspace S" "f x = f y"
      then have "\<And>n. d x (xn n) = d y (xn n)" by(auto simp: f_def dest: fun_cong)
      hence d2:"d x y \<le> 2 * d x (xn n)" for n
        using ms.dist_tr[OF xy(1) _ xy(2),of "xn n",simplified ms.dist_sym[of "xn n" y]] dense_of_subset[OF U(2)] xn(1)[of n]
        by auto
      have "d x y < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
      proof -
        have "0 < \<epsilon> / 2" using that by simp
        then obtain n where "d x (xn n) < \<epsilon> / 2"
          using ms.dense_set_def2[of U,simplified d(2)] U(2) xy(1) xn(2) by blast
        with d2[of n] show ?thesis by simp
      qed
      hence "d x y = 0"
        using ms.dist_geq0[of x y]
        by (metis dual_order.irrefl order_neq_le_trans)
      thus "x = y"
        using ms.dist_0[OF xy(1,2)] by simp
    qed
    have f_img: "f ` topspace S \<subseteq> topspace Hilbert_cube_as_topology"
      using d(3) ms.dist_geq0 by(auto simp: topspace_Hilbert_cube f_def less_le_not_le)
    have f_cont: "continuous_map S Hilbert_cube_as_topology f"
      unfolding continuous_map_componentwise_UNIV f_def continuous_map_in_subtopology
    proof safe
      show "continuous_map S euclideanreal (\<lambda>x. d x (xn k))" for k
        using ms.dist_set_continuous[of "{xn k}"] by(simp add: d(2))
    next
      show "d x (xn k) \<in> {0..1}" for x k
        using d(3) ms.dist_geq0 by(auto simp: less_le_not_le)
    qed
    hence f_cont': "continuous_map S (subtopology Hilbert_cube_as_topology (f ` topspace S)) f"
      using continuous_map_into_subtopology by blast
    obtain g where g: "g ` (f ` topspace S) = topspace S" "\<And>x. x \<in> topspace S \<Longrightarrow> g (f x) = x" "\<And>x. x \<in> f ` topspace S \<Longrightarrow> f (g x) = x"
      by (meson f_inj f_the_inv_into_f the_inv_into_f_eq the_inv_into_onto)
    have g_cont: "continuous_map (subtopology Hilbert_cube_as_topology (f ` topspace S)) S g"    
    proof -
      interpret m01: polish_metric_set "{0..1::real}" "submetric {0..1} dist"
        by (metis closed_atLeastAtMost closed_closedin euclidean_mtopology polish_class_polish_set polish_metric_set.submetric_polish subset_UNIV)
      have m01_eq: "m01.mtopology = top_of_set {0..1}"
        by(rule submetric_of_euclidean(2)[of "{0..1::real}"])
      have "submetric {0..1::real} dist x y \<le> 1" "submetric {0..1::real} dist x y \<ge> 0" for x y
        using dist_real_def by(auto simp: submetric_def)
      then interpret ppm: product_polish_metric "1/2" "UNIV :: nat set" id id "\<lambda>_. {0..1}" "\<lambda>_. submetric {0..1::real} dist" 1
        by(auto intro!: product_polish_metric_natI m01.polish_metric_set_axioms)
      have Hilbert_cube_eq: "ppm.mtopology = Hilbert_cube_as_topology"
        by(simp add: ppm.product_dist_mtopology[symmetric] m01_eq)
      interpret f_S: metric_set "f ` topspace S" "submetric (f ` topspace S) ppm.product_dist"
        using f_img by(auto intro!: ppm.submetric_metric_set)
      have 1:"subtopology Hilbert_cube_as_topology (f ` topspace S) = f_S.mtopology"
        using ppm.submetric_subtopology[of "f ` topspace S"] f_img by(simp add: Hilbert_cube_eq)
      have "continuous_map f_S.mtopology ms.mtopology g"
        unfolding metric_set_continuous_map_eq'[OF f_S.metric_set_axioms ms.metric_set_axioms]
      proof safe
        show "x \<in> topspace S \<Longrightarrow> g (f x) \<in> topspace S" for x
          by(simp add: g(2))
      next
        fix yn y
        assume h:"f_S.converge_to_inS yn y"
        have "ppm.converge_to_inS yn y"
          using ppm.converge_to_insub_converge_to_inS[OF _ h] f_img by auto
        hence  m01_conv:"\<And>n. m01.converge_to_inS (\<lambda>i. yn i n) (y n)"
          using ppm.converge_to_iff[of yn y] by(auto simp: ppm.converge_to_inS_def)
        have "\<And>n. \<exists>zn. yn n = f zn \<and> zn \<in> topspace S"
          using h by(auto simp: f_S.converge_to_inS_def)
        then obtain zn where zn:"\<And>n. f (zn n) = yn n" "\<And>n. zn n \<in> topspace S"
          by metis
        obtain z where z:"f z = y" "z \<in> topspace S"
          using h by(auto simp: f_S.converge_to_inS_def)
        show "ms.converge_to_inS (\<lambda>n. g (yn n)) (g y)"
          unfolding ms.converge_to_inS_def2
        proof safe
          show "g (yn n) \<in> topspace S" "g y \<in> topspace S" for n
            using g(2)[of z] g(2)[of "zn n"] zn[of n] z by simp_all
        next
          fix \<epsilon> :: real
          assume he: "0 < \<epsilon>"
          then have "0 < \<epsilon> / 3" by simp
          then obtain m where m:"d z (xn m) < \<epsilon> / 3"
            using ms.dense_set_def2[of U,simplified d(2)] U(2) z(2) xn(2) by blast
          obtain N where "\<And>n. n \<ge> N \<Longrightarrow> \<bar>yn n m - y m \<bar> < \<epsilon> / 3"
            using m01_conv[of m,simplified m01.converge_to_inS_def2] \<open>0 < \<epsilon> / 3\<close>
            by(simp only: submetric_def dist_real_def) (metis (full_types, lifting) PiE UNIV_I)
          hence N:"\<And>n. n \<ge> N \<Longrightarrow> yn n m < \<epsilon> / 3 + y m"
            by (metis abs_diff_less_iff add.commute)
          have "\<exists>N. \<forall>n\<ge>N. d (zn n) z < \<epsilon>"
          proof(safe intro!: exI[where x=N])
            fix n
            assume "N \<le> n"
            have "d (zn n) z \<le> f (zn n) m + d z (xn m)"
              using ms.dist_tr[OF zn(2)[of n] xns[of m] z(2),simplified ms.dist_sym[of "xn m" z]]
              by(auto simp: f_def)
            also have "... < \<epsilon> / 3 + y m + d z (xn m)"
              using N[OF \<open>N\<le>n\<close>] zn(1)[of n] by simp
            also have "... =  \<epsilon> / 3 + d z (xn m) + d z (xn m)"
              by(simp add: z(1)[symmetric] f_def)
            also have "... < \<epsilon>"
              using m by auto
            finally show "d (zn n) z < \<epsilon>" .
          qed
          thus "\<exists>N. \<forall>n\<ge>N. d (g (yn n)) (g y) < \<epsilon>"
            using zn(1) z(1) g(2)[OF z(2)] g(2)[OF zn(2)] by auto
        qed
      qed
      thus ?thesis
        by(simp add: d(2) 1)
    qed
    show ?thesis
      using f_img g(2,3) f_cont' g_cont
      by(auto intro!: exI[where x="f ` topspace S"] homeomorphic_maps_imp_homeomorphic_space[where f=f and g=g] simp: homeomorphic_maps_def)
  qed
qed

corollary(in complete_metrizable) embedding_into_Hilbert_cube_g_delta_of:
  assumes "separable S"
  shows "\<exists>A. g_delta_of Hilbert_cube_as_topology A \<and> S homeomorphic_space (subtopology Hilbert_cube_as_topology A)"
proof -
  obtain A where h:"A \<subseteq> topspace Hilbert_cube_as_topology" "S homeomorphic_space subtopology Hilbert_cube_as_topology A"
    using embedding_into_Hilbert_cube[OF assms(1)] by blast
  with complete_metrizable_homeo_image_g_delta[OF complete_metrizable_axioms polish_topology.axioms(1)[OF Hilbert_cube_Polish_topology] h(1,2)]
  show ?thesis
    by(auto intro!: exI[where x=A])
qed

corollary(in polish_topology) embedding_into_Hilbert_cube_g_delta_of:
 "\<exists>A. g_delta_of Hilbert_cube_as_topology A \<and> S homeomorphic_space (subtopology Hilbert_cube_as_topology A)"
  by(rule embedding_into_Hilbert_cube_g_delta_of[OF S_separable])

lemma(in polish_topology) uncountable_contains_Cantor_space':
  assumes "uncountable (topspace S)"
  shows "\<exists>A\<subseteq> topspace S. Cantor_space_as_topology homeomorphic_space (subtopology S A)"
proof -
  obtain U P where up: "countable U" "openin S U" "perfect_set S P""U \<union> P = topspace S" "U \<inter> P = {}" "\<And>a. a \<noteq> {} \<Longrightarrow> openin (subtopology S P) a \<Longrightarrow> uncountable a"
    using Cantor_Bendixon[OF S_second_countable] by auto
  have P: "closedin S P" "P \<subseteq> topspace S" "uncountable P"
    using countable_Un_iff[of U P] up(1) assms up(4)
    by(simp_all add: perfect_setD[OF up(3)])
  then interpret pp: polish_topology "subtopology S P"
    by(simp add: closedin_polish)
  have Ptop: "topspace (subtopology S P) = P"
    using P(2) by auto
  obtain U where U: "countable U" "dense_of (subtopology S P) U"
    using pp.S_separable separable_def by blast
  with uncountable_infinite[OF P(3)] pp.dense_of_infinite P(2)
  have "infinite U" by (metis topspace_subtopology_subset)
  obtain d where "complete_metric_set P d" and d:"metric_set.mtopology P d = subtopology S P"
    using pp.cmetric by(simp only: Ptop,auto)
  interpret md: complete_metric_set P d by fact
  define xn where "xn \<equiv> from_nat_into U"
  have xn: "bij_betw xn UNIV U" "\<And>n m. n \<noteq> m \<Longrightarrow> xn n \<noteq> xn m" "\<And>n. xn n \<in> U" "\<And>n. xn n \<in> P" "md.dense_set (range xn)"
    using bij_betw_from_nat_into[OF U(1) \<open>infinite U\<close>] dense_of_subset[OF U(2)] d U(2) range_from_nat_into[OF infinite_imp_nonempty[OF \<open>infinite U\<close>] U(1)]
    by(auto simp add: xn_def  U(1) \<open>infinite U\<close> from_nat_into[OF infinite_imp_nonempty[OF \<open>infinite U\<close>]])
  have [simp]:"topspace md.mtopology = P"
    using Ptop by(simp add: md.mtopology_topspace)
  have perfect:"perfect_space md.mtopology"
    using d perfect_set_subtopology up(3) by simp
  define jn where "jn \<equiv> (\<lambda>n. LEAST i. i > n \<and> md.closed_ball (xn i) ((1/2)^i) \<subseteq> md.open_ball (xn n) ((1/2)^n) - md.open_ball (xn n) ((1/2)^i))"
  define kn where "kn \<equiv> (\<lambda>n. LEAST k. k > jn n \<and> md.closed_ball (xn k) ((1/2)^k) \<subseteq> md.open_ball (xn n) ((1/2)^jn n))"
  have dxmxn: "\<forall>n n'. \<exists>m. m > n \<and> m > n' \<and> (1/2)^(m-1) < d (xn n) (xn m) \<and> d (xn n) (xn m) < (1/2)^(Suc n')"
  proof safe
    fix n n'
    have hinfin':"infinite (md.open_ball x e \<inter> (range xn))" if "x \<in> P" "e > 0" for x e
    proof
      assume h_fin:"finite (md.open_ball x e \<inter> range xn)"
      have h_nen:"md.open_ball x e \<inter> range xn \<noteq> {}"
        using xn(5) that by(auto simp: md.dense_set_def)
      have infin: "infinite (md.open_ball x e)"
        using md.perfect_set_open_ball_infinite[OF perfect] that by simp
      then obtain y where y:"y \<in> md.open_ball x e" "y \<notin> range xn"
        using h_fin by(metis inf.absorb_iff2 inf_commute subsetI)
      define e' where "e' = Min {d y xk |xk. xk \<in> md.open_ball x e \<inter> range xn}"
      have fin: "finite  {d y xk |xk. xk \<in> md.open_ball x e \<inter> range xn}"
        using finite_imageI[OF h_fin,of "d y"] by (metis Setcompr_eq_image)
      have nen: "{d y xk |xk. xk \<in> md.open_ball x e \<inter> range xn} \<noteq> {}"
        using h_nen by auto
      have "e' > 0"
        unfolding e'_def Min_gr_iff[OF fin nen]
      proof safe
        fix l
        assume "xn l \<in> md.open_ball x e"
        from y(2) md.dist_0[OF md.open_ballD'(1)[OF y(1)] md.open_ballD'(1)[OF this]] md.dist_geq0[of y "xn l"]
        show "0 < d y (xn l)"
          by auto
      qed
      obtain e'' where e'': "e'' > 0" "md.open_ball y e'' \<subseteq> md.open_ball x e" "y \<in> md.open_ball y e''"
        by (meson md.mtopology_open_ball_in' md.open_ballD'(1) md.open_ball_ina y(1))
      define \<epsilon> where "\<epsilon> \<equiv> min e' e''"
      have "\<epsilon> > 0"
        using e''(1) \<open>e' > 0\<close> by(simp add: \<epsilon>_def)
      then obtain m where m: "d y (xn m) < \<epsilon>"
        using md.dense_set_def2[of "range xn"] xn(5) md.open_ballD'(1)[OF y(1)] by blast
      consider "xn m \<in> md.open_ball x e" | "xn m \<in> P - md.open_ball x e"
        using xn(4) by auto
      then show False
      proof cases
        case 1
        then have "e' \<le> d y (xn m)"
          using Min_le_iff[OF fin nen] by(auto simp: e'_def)
        thus ?thesis
          using m by(simp add: \<epsilon>_def)
      next
        case 2
        then have "xn m \<notin> md.open_ball y e''"
          using e''(2) by auto
        hence "e'' \<le> d y (xn m)"
          by(rule md.open_ball_nin_le[OF md.open_ballD'(1)[OF y(1)] e''(1) xn(4)[of m]])
        thus ?thesis
          using m by(simp add: \<epsilon>_def)
      qed
    qed
    have hinfin:"infinite (md.open_ball x e \<inter> (xn ` {l<..}))" if "x \<in> P" "e > 0" for x e l
    proof
      assume "finite (md.open_ball x e \<inter> xn ` {l<..})"
      moreover have "finite (md.open_ball x e \<inter> xn ` {..l})" by simp
      moreover have "(md.open_ball x e \<inter> (range xn)) = (md.open_ball x e \<inter> xn ` {l<..}) \<union> (md.open_ball x e \<inter> xn ` {..l})"
        by fastforce
      ultimately have "finite (md.open_ball x e \<inter> (range xn))"
        by auto
      with hinfin'[OF that] show False ..
    qed
    have "infinite (md.open_ball (xn n) ((1/2)^Suc n'))"
      using md.perfect_set_open_ball_infinite[OF perfect] xn(4)[of n] by simp
    then obtain x where x: "x \<in> md.open_ball (xn n) ((1/2)^Suc n')" "x \<noteq> xn n"
      by (metis finite_insert finite_subset infinite_imp_nonempty singletonI subsetI)
    then obtain e where e: "e > 0" "md.open_ball x e \<subseteq> md.open_ball (xn n) ((1/2)^Suc n')" "x \<in> md.open_ball x e"
      by (meson md.mtopology_open_ball_in' md.open_ballD'(1) md.open_ball_ina)
    have "d (xn n) x > 0"
      using md.dist_geq0[of "xn n" x] md.dist_0[OF xn(4)[of n] md.open_ballD'(1)[OF x(1)]] x(2) by simp
    then obtain m' where m': "m' - 1 > 0" "(1/2)^(m' - 1) < d (xn n) x"
      by (metis One_nat_def diff_Suc_Suc diff_zero one_less_numeral_iff reals_power_lt_ex semiring_norm(76))
    define m where "m \<equiv> max m' (max n' (Suc n))"
    then have "m \<ge> m'" "m \<ge> n'" "m \<ge> Suc n" by simp_all
    hence m: "m - 1 > 0" "(1/2)^(m - 1) < d (xn n) x" "m > n"
      using m' less_trans[OF _ m'(2),of "(1 / 2) ^ (m - 1)"]
      by auto (metis diff_less_mono le_eq_less_or_eq)
    define \<epsilon> where "\<epsilon> \<equiv> min e (d (xn n) x - (1/2)^(m - 1))"
    have "\<epsilon> > 0"
      using e m by(simp add: \<epsilon>_def)
    have ball_le:"md.open_ball x \<epsilon> \<subseteq> md.open_ball (xn n) ((1 / 2) ^ Suc n')"
      using md.open_ball_le[of \<epsilon> e x] e(2) by(simp add: \<epsilon>_def)
    obtain k where k: "xn k \<in> md.open_ball x \<epsilon>" "k > m"
      using infinite_imp_nonempty[OF hinfin[OF md.open_ballD'(1)[OF x(1)] \<open>\<epsilon> > 0\<close>,of m]] by auto
    show "\<exists>m>n. n' < m \<and> (1 / 2) ^ (m - 1) < d (xn n) (xn m) \<and> d (xn n) (xn m) < (1 / 2) ^ Suc n'"
    proof(intro exI[where x=k] conjI)
      have "(1 / 2) ^ (k - 1) < (1 / (2 :: real)) ^ (m - 1)"
        using k(2) m(3) by simp
      also have "... = d (xn n) x + ((1/2)^ (m - 1) - d (xn n) x)" by simp
      also have "... < d (xn n) x - d (xn k) x"
        using md.open_ballD[OF k(1)] by(simp add: \<epsilon>_def md.dist_sym[of x _])
      also have "... \<le> d (xn n) (xn k)"
        using  md.dist_tr[OF xn(4)[of n] xn(4)[of k] md.open_ballD'(1)[OF x(1)]] by simp
      finally show "(1 / 2) ^ (k - 1) < d (xn n) (xn k)" .
    qed(use \<open>m \<ge> n'\<close> k ball_le md.open_ballD[of "xn k" "xn n" "(1 / 2) ^ Suc n'"] m(3) in auto)
  qed
  have "jn n > n \<and> md.closed_ball (xn (jn n)) ((1/2)^(jn n)) \<subseteq> md.open_ball (xn n) ((1/2)^n) - md.open_ball (xn n) ((1/2)^(jn n))" for n
    unfolding jn_def
  proof(rule LeastI_ex)
    obtain m where m:"m > n" "(1 / 2) ^ (m - 1) < d (xn n) (xn m)" "d (xn n) (xn m) < (1 / 2) ^ Suc n"
      using dxmxn by auto
    show "\<exists>x>n. md.closed_ball (xn x) ((1 / 2) ^ x) \<subseteq> md.open_ball (xn n) ((1 / 2) ^ n) - md.open_ball (xn n) ((1 / 2) ^ x)"
    proof(safe intro!: exI[where x=m] m(1))
      fix x
      assume h:"x \<in> md.closed_ball (xn m) ((1 / 2) ^ m)"
      have 1:"d (xn n) x < (1 / 2) ^ n"
      proof -
        have "d (xn n) x < (1 / 2) ^ Suc n + (1 / 2) ^ m"
          using m(3) md.dist_tr[OF xn(4)[of n] xn(4)[of m] md.closed_ballD'(1)[OF h]] md.closed_ballD[OF h]
          by simp
        also have "... \<le> (1 / 2) ^ Suc n + (1 / 2) ^ Suc n"
          by (metis Suc_lessI add_mono divide_less_eq_1_pos divide_pos_pos less_eq_real_def m(1) one_less_numeral_iff power_strict_decreasing_iff semiring_norm(76) zero_less_numeral zero_less_one)
        finally show ?thesis by simp
      qed
      have 2:"(1 / 2) ^ m \<le> d (xn n) x"
      proof -
        have "(1 / 2) ^ (m - 1) < d (xn n) x + (1 / 2) ^ m"
          using order.strict_trans2[OF m(2) md.dist_tr[OF xn(4)[of n] md.closed_ballD'(1)[OF h] xn(4)[of m]]] md.closed_ballD(1)[OF h]
          by(simp add: md.dist_sym)
        hence "(1 / 2) ^ (m - 1) - (1 / 2) ^ m \<le> d (xn n) x"
          by simp
        thus ?thesis
          using not0_implies_Suc[OF gr_implies_not0[OF m(1)]] by auto
      qed
      show "x \<in> md.open_ball (xn n) ((1 / 2) ^ n)"
           "x \<in> md.open_ball (xn n) ((1 / 2) ^ m) \<Longrightarrow> False"
        using xn(4)[of n] md.closed_ballD'(1)[OF h] 1 2 by(auto simp: md.open_ball_def)
    qed
  qed
  hence jn: "\<And>n. jn n > n" "\<And>n. md.closed_ball (xn (jn n)) ((1/2)^(jn n)) \<subseteq> md.open_ball (xn n) ((1/2)^n) - md.open_ball (xn n) ((1/2)^(jn n))"
    by simp_all
  have "kn n > jn n \<and> md.closed_ball (xn (kn n)) ((1/2)^(kn n)) \<subseteq> md.open_ball (xn n) ((1/2)^jn n)" for n
    unfolding kn_def
  proof(rule LeastI_ex)
    obtain m where m:"m > jn n" "d (xn n) (xn m) < (1 / 2) ^ Suc (jn n)"
      using dxmxn by blast 
    show "\<exists>x>jn n. md.closed_ball (xn x) ((1 / 2) ^ x) \<subseteq> md.open_ball (xn n) ((1 / 2) ^ jn n)"
    proof(intro exI[where x=m] conjI)
      show "md.closed_ball (xn m) ((1 / 2) ^ m) \<subseteq> md.open_ball (xn n) ((1 / 2) ^ jn n)"
      proof
        fix x
        assume h:"x \<in> md.closed_ball (xn m) ((1 / 2) ^ m)"
        have "d (xn n) x < (1 / 2)^ Suc (jn n) + (1 / 2) ^ m"
          using md.dist_tr[OF xn(4)[of n] xn(4)[of m] md.closed_ballD'(1)[OF h]] m(2) md.closed_ballD[OF h]
          by simp
        also have "... \<le> (1 / 2)^ Suc (jn n) + (1 / 2)^ Suc (jn n)"
          by (metis Suc_le_eq add_mono dual_order.refl less_divide_eq_1_pos linorder_not_less m(1) not_numeral_less_one power_decreasing zero_le_divide_1_iff zero_le_numeral zero_less_numeral)
        finally show "x \<in> md.open_ball (xn n) ((1 / 2) ^ jn n)"
          by(simp add: xn(4)[of n] md.closed_ballD'(1)[OF h] md.open_ball_def)
      qed
    qed(use m(1) in auto)
  qed
  hence kn: "\<And>n. kn n > jn n" "\<And>n. md.closed_ball (xn (kn n)) ((1/2)^(kn n)) \<subseteq> md.open_ball (xn n) ((1/2)^(jn n))"
    by simp_all
  have jnkn_pos: "jn n > 0" "kn n > 0" for n
    using not0_implies_Suc[OF gr_implies_not0[OF jn(1)[of n]]] kn(1)[of n] by auto

  define bn :: "real list \<Rightarrow> nat"
    where "bn \<equiv> rec_list 1 (\<lambda>a l t. if a = 0 then jn t else kn t)"
  have bn_simp: "bn [] = 1" "bn (a # l) = (if a = 0 then jn (bn l) else kn (bn l))" for a l
    by(simp_all add: bn_def)
  define to_listn :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real list"
    where "to_listn \<equiv> (\<lambda>x . rec_nat [] (\<lambda>n t. x n # t))"
  have to_listn_simp: "to_listn x 0 = []" "to_listn x (Suc n) = x n # to_listn x n" for x n
    by(simp_all add: to_listn_def)
  have to_listn_eq: "(\<And>m. m < n \<Longrightarrow> x m = y m) \<Longrightarrow> to_listn x n = to_listn y n" for x y n
    by(induction n) (auto simp: to_listn_simp)
  have bn_gtn: "bn (to_listn x n) > n" for x n
    apply(induction n arbitrary: x)
    using jn(1) kn(1) by(auto simp: bn_simp to_listn_simp) (meson Suc_le_eq le_less less_trans_Suc)+
  define rn where "rn \<equiv> (\<lambda>n. Min (range (\<lambda>x. (1 / 2 :: real) ^ bn (to_listn x n))))"
  have rn_fin: "finite (range (\<lambda>x. (1 / 2 :: real) ^ bn (to_listn x n)))" for n
  proof -
    have "finite (range (\<lambda>x. bn (to_listn x n)))"
    proof(induction n)
      case ih:(Suc n)
      have "(range (\<lambda>x. bn (to_listn x (Suc n)))) \<subseteq> (range (\<lambda>x. jn (bn (to_listn x n)))) \<union> (range (\<lambda>x. kn (bn (to_listn x n))))"
        by(auto simp: to_listn_simp bn_simp)
      moreover have "finite ..."
        using ih finite_range_imageI by auto
      ultimately show ?case by(rule finite_subset)
    qed(simp add: to_listn_simp)
    thus ?thesis
      using finite_range_imageI by blast
  qed
  have rn_nen: "(range (\<lambda>x. (1 / 2 :: real) ^ bn (to_listn x n))) \<noteq> {}" for n
    by simp
  have rn_pos: "0 < rn n" for n
    by(simp add: Min_gr_iff[OF rn_fin rn_nen] rn_def)
  have rn_less: "rn n < (1/2)^n" for n
    using bn_gtn[of n] by(auto simp: rn_def Min_less_iff[OF rn_fin rn_nen])
  have cball_le_ball:"md.closed_ball (xn (bn (a#l))) ((1/2)^(bn (a#l))) \<subseteq> md.open_ball (xn (bn l)) ((1/2) ^ (bn l))" for a l
    using kn(2)[of "bn l"] md.open_ball_le[of  "(1 / 2) ^ jn (bn l)" "(1 / 2) ^ bn l" "xn (bn l)"] less_imp_le [OF jn(1)] jn(2)
    by(simp add: bn_simp) blast
  hence cball_le:"md.closed_ball (xn (bn (a#l))) ((1/2)^(bn (a#l))) \<subseteq> md.closed_ball (xn (bn l)) ((1/2) ^ (bn l))" for a l
    using md.open_ball_closed_ball by blast
  have cball_disj: "md.closed_ball (xn (bn (0#l))) ((1/2)^(bn (0#l))) \<inter> md.closed_ball (xn (bn (1#l))) ((1/2)^(bn (1#l))) = {}" for l
    using jn(2) kn(2) by(auto simp: bn_simp)
  have "\<forall>x. \<exists>xa\<in>P. (\<Inter>n. md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) = {xa}"
  proof
    fix x
    show "\<exists>xa\<in>P. (\<Inter>n. md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) = {xa}"
    proof(rule md.closed_decseq_Inter)
      show "md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n)) \<noteq> {}" for n
        using md.closed_ball_ina[OF xn(4)[of "bn (to_listn x n)"],of "(1 / 2) ^ bn (to_listn x n)"] by auto
    next
      show "decseq (\<lambda>n. md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n)))"
        by(intro decseq_SucI,simp add: to_listn_simp cball_le)
    next
      fix \<epsilon> :: real
      assume "0 < \<epsilon>"
      then obtain N where N: "(1 / 2) ^ N < (1/2) * \<epsilon>"
        by (metis divide_pos_pos mult.commute mult.right_neutral one_less_numeral_iff reals_power_lt_ex semiring_norm(76) times_divide_eq_right zero_less_numeral)
      show "\<exists>N. \<forall>n\<ge>N. md.diam (md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) < \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n
        assume "N \<le> n"
        have "md.diam (md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) \<le> md.diam (md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ n))"
          using bn_gtn[of n x] by(auto intro!: md.diam_subset md.closed_ball_le)
        also have "... \<le> ennreal (2 * (1 / 2) ^ n)"
          by(simp add: md.diam_cball_leq)
        also have "... \<le> ennreal (2 * (1 / 2) ^ N)"
          using \<open>N \<le> n\<close> by (simp add: numeral_mult_ennreal)
        also have "... < ennreal (2 *(1/2) * \<epsilon>)"
          using N by (simp add: \<open>0 < \<epsilon>\<close> ennreal_lessI le_less numeral_mult_ennreal)
        also have "... = ennreal \<epsilon>"
          by (simp add: \<open>0 < \<epsilon>\<close> le_less numeral_mult_ennreal)
        finally show "md.diam (md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) < ennreal \<epsilon>" .
      qed
    qed(rule md.closedin_closed_ball)
  qed
  then obtain f where f:"\<And>x. f x \<in> P" "\<And>x. (\<Inter>n. md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))) = {f x}"
    by metis
  hence f': "\<And>n x. f x \<in> md.closed_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))"
    by blast
  have f'': "f x \<in> md.open_ball (xn (bn (to_listn x n))) ((1 / 2) ^ bn (to_listn x n))" for n x
    using f'[of x "Suc n"] cball_le_ball[of _ "to_listn x n"] by(auto simp: to_listn_simp)
  from f interpret bdmd: metric_set "f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "submetric (f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1})) d"
    by(auto intro!: md.submetric_metric_set)
  have bdmd_top: "bdmd.mtopology = subtopology md.mtopology (f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1}))"
    by (simp add: f(1) image_subset_iff md.submetric_subtopology)
  have bdmd_sub: "bdmd.mtopology = subtopology S (f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1}))"
    using f(1) Int_absorb1[of "f ` (UNIV \<rightarrow>\<^sub>E {0, 1})" P] by(fastforce simp: bdmd_top d subtopology_subtopology)
  interpret d01: polish_metric_set "{0,1::real}" "submetric {0,1::real} dist"
    by(auto intro!: polish_metric_set.submetric_polish[OF polish_class_polish_set] simp: euclidean_mtopology)
  interpret pd: product_polish_metric "1/2" UNIV id id "\<lambda>_. {0,1::real}" "\<lambda>_. submetric {0,1::real} dist" 1
    by(auto intro!: product_polish_metric_natI simp: d01.polish_metric_set_axioms) (auto simp: submetric_def)
  have mpd_top: "pd.mtopology = Cantor_space_as_topology"
    by(auto simp: pd.product_dist_mtopology[symmetric] submetric_of_euclidean(2) intro!: product_topology_cong)

  define def_at where "def_at x y \<equiv> LEAST n. x n \<noteq> y n" for x y :: "nat \<Rightarrow> real"
  have def_atxy: "\<And>n. n < def_at x y \<Longrightarrow> x n = y n" "x (def_at x y) \<noteq> y (def_at x y)" if "x \<noteq> y" for x y
  proof -
    have "\<exists>n. x n \<noteq> y n"
      using that by auto
    from LeastI_ex[OF this]
    show "\<And>n. n < def_at x y \<Longrightarrow> x n = y n" "x (def_at x y) \<noteq> y (def_at x y)"
      using not_less_Least by(auto simp: def_at_def)
  qed
  have def_at_le_if: "pd.product_dist x y \<le> (1/2)^n \<Longrightarrow> n \<le> def_at x y" if assm:"x \<noteq> y" "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x y n
  proof -
    assume h:"pd.product_dist x y \<le> (1 / 2) ^ n"
    have "x m = y m" if m_less_n: "m < n" for m
    proof(rule ccontr)
      assume nen: "x m \<noteq> y m"
      then have "submetric {0, 1} dist (x m) (y m) = 1"
        using assm(2,3) by(auto simp: submetric_def)
      hence "1 \<le> 2 ^ m * pd.product_dist x y"
        using pd.product_dist_geq[of m m,simplified,OF assm(2,3)] by simp
      hence "(1/2)^m \<le> 2^m * (1/2)^m * pd.product_dist x y" by simp
      hence "(1/2)^m \<le> pd.product_dist x y" by (simp add: power_one_over)
      also have "... \<le> (1 / 2) ^ n"
        by(simp add: h)
      finally show False
        using that by auto
    qed
    thus "n \<le> def_at x y"
      by (meson def_atxy(2) linorder_not_le that(1))
  qed
  have def_at_le_then: "pd.product_dist x y \<le> 2 * (1/2)^n" if assm:"x \<noteq> y" "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "n \<le> def_at x y" for x y n
  proof -
    have "\<And>m. m < n \<Longrightarrow> x m = y m"
      by (metis def_atxy(1) order_less_le_trans that(4))
    hence 1:"\<And>m. m < n \<Longrightarrow> submetric {0, 1} dist (x m) (y m) = 0"
      by (simp add: submetric_def)
    have "pd.product_dist x y = (\<Sum>i. (1/2)^(i + n) * (submetric  {0, 1} dist (x (i + n)) (y (i + n)))) + (\<Sum>i<n. (1/2)^i * (submetric  {0, 1} dist (x i) (y i)))"
      using assm pd.product_dist_summable'[simplified] by(auto intro!: suminf_split_initial_segment simp: product_dist_def)
    also have "... = (\<Sum>i. (1/2)^(i + n) * (submetric  {0, 1} dist (x (i + n)) (y (i + n))))"
      by(simp add: 1)
    also have "... \<le> (\<Sum>i. (1/2)^(i + n))"
      using pd.product_dist_summable'[simplified] pd.d_bound by(auto intro!: suminf_le summable_ignore_initial_segment)
    finally show ?thesis
      using pd.nsum_of_rK[of n] by simp
  qed
  have d_le_def: "d (f x) (f y) \<le> (1/2)^(def_at x y)" if assm:"x \<noteq> y" "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x y
  proof -
    have 1:"to_listn x n = to_listn y n" if "n \<le> def_at x y" for n
    proof -
      have "\<And>m. m < n \<Longrightarrow> x m = y m"
        by (metis def_atxy(1) order_less_le_trans that)
      then show ?thesis
        by(auto intro!: to_listn_eq)
    qed
    have "f x \<in> md.closed_ball (xn (bn (to_listn x (def_at x y)))) ((1 / 2) ^ bn (to_listn x (def_at x y)))"
         "f y \<in> md.closed_ball (xn (bn (to_listn x (def_at x y)))) ((1 / 2) ^ bn (to_listn x (def_at x y)))"
      using f'[of x "def_at x y"] f'[of y "def_at x y"] by(auto simp: 1[OF order_refl])
    hence "d (f x) (f y) \<le> 2 * (1 / 2) ^ bn (to_listn x (def_at x y))"
      using f(1) by(auto intro!: md.diam_is_sup'[OF _ _ md.diam_cball_leq])
    also have "... \<le> (1/2)^(def_at x y)"
    proof -
      have "Suc (def_at x y) \<le> bn (to_listn x (def_at x y))"
        using bn_gtn[of "def_at x y" x] by simp
      hence "(1 / 2) ^ bn (to_listn x (def_at x y)) \<le> (1 / 2 :: real) ^ Suc (def_at x y)"
        using power_decreasing_iff[OF pd.r] by blast
      thus ?thesis
        by simp
    qed
    finally show "d (f x) (f y) \<le> (1/2)^(def_at x y)" .
  qed
  have fy_in:"f y \<in> md.closed_ball (xn (bn (to_listn x m))) ((1/2)^bn (to_listn x m)) \<Longrightarrow> \<forall>l<m. x l = y l" if assm:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x y m
  proof(induction m)
    case ih:(Suc m)
    have "f y \<in> md.closed_ball (xn (bn (to_listn x m))) ((1 / 2) ^ bn (to_listn x m))"
      using ih(2) cball_le by(auto simp: to_listn_simp)
    with ih(1) have k:"k < m \<Longrightarrow> x k = y k" for k by simp
    show ?case
    proof safe
      fix l
      assume "l < Suc m"
      then consider "l < m" | "l = m"
        using \<open>l < Suc m\<close> by fastforce
      thus "x l = y l"
      proof cases
        case 2
        have 3:"f y \<in> md.closed_ball (xn (bn (y l # to_listn y l))) ((1 / 2) ^ bn (y l # to_listn y l))"
          using f'[of y "Suc l"] by(simp add: to_listn_simp)
        have 4:"f y \<in> md.closed_ball (xn (bn (x l # to_listn y l))) ((1 / 2) ^ bn (x l # to_listn y l))"
          using ih(2) to_listn_eq[of m x y,OF k] by(simp add: to_listn_simp 2)
        show ?thesis
        proof(rule ccontr)
          assume "x l \<noteq> y l"
          then consider "x l = 0" "y l = 1" | "x l = 1" "y l = 0"
            using assm(1,2) by(auto simp: PiE_def Pi_def) metis
          thus False
            by cases (use cball_disj[of "to_listn y l"] 3 4 in auto)
        qed
      qed(simp add: k)
    qed
  qed simp
  have d_le_rn_then: "\<exists>e>0. \<forall>y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1}). x \<noteq> y \<longrightarrow> d (f x) (f y) < e \<longrightarrow> n \<le> def_at x y" if assm: "x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" for x n
  proof(safe intro!: exI[where x="(1/2)^bn (to_listn x n) - d (xn (bn (to_listn x n))) (f x)"])
    show "0 < (1 / 2) ^ bn (to_listn x n) - d (xn (bn (to_listn x n))) (f x)"
      using md.open_ballD[OF f''] by auto
  next
    fix y
    assume h:"y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "d (f x) (f y) < (1 / 2) ^ bn (to_listn x n) - d (xn (bn (to_listn x n))) (f x)" "x \<noteq> y"
    then have "f y \<in> md.closed_ball (xn (bn (to_listn x n))) ((1/2)^bn (to_listn x n))"
      using md.dist_tr[OF xn(4)[of "bn (to_listn x n)"] f(1)[of x] f(1)[of y]]
      by(simp add: xn(4)[of "bn (to_listn x n)"] f(1)[of y] md.closed_ball_def)
    with fy_in[OF assm h(1)] have "\<forall>m < n. x m = y m"
      by simp
    thus "n \<le> def_at x y"
      by (meson def_atxy(2) linorder_not_le h(3))
  qed
  have 0: "f ` (\<Pi>\<^sub>E i\<in>UNIV. {0,1}) \<subseteq> topspace S"
    using f(1) P(2) by auto
  have 1: "continuous_map pd.mtopology bdmd.mtopology f"
    unfolding metric_set_continuous_map_eq[OF pd.metric_set_axioms bdmd.metric_set_axioms]
  proof safe
    fix x :: "nat \<Rightarrow> real" and \<epsilon> :: real
    assume h:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "0 < \<epsilon>"
    then obtain n where n:"(1/2)^n < \<epsilon>"
      using real_arch_pow_inv[OF _ pd.r(2)] by auto
    show "\<exists>\<delta>>0. \<forall>y\<in>UNIV \<rightarrow>\<^sub>E {0, 1}. pd.product_dist x y < \<delta> \<longrightarrow> submetric (f ` (UNIV \<rightarrow>\<^sub>E {0, 1})) d (f x) (f y) < \<epsilon>"
    proof(safe intro!: exI[where x="(1/2)^n"])
      fix y
      assume y:"y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "pd.product_dist x y < (1 / 2) ^ n"
      consider "x = y" | "x \<noteq> y" by auto
      thus "submetric (f ` (UNIV \<rightarrow>\<^sub>E {0, 1})) d (f x) (f y) < \<epsilon>"
      proof cases
        case 1
        with y(1) h md.dist_0[OF f(1)[of y] f(1)[of y]]
        show ?thesis by(auto simp add: submetric_def)
      next
        case 2
        then have "n \<le> def_at x y"
          using h(1) y by(auto intro!: def_at_le_if)
        have "submetric (f ` (UNIV \<rightarrow>\<^sub>E {0, 1})) d (f x) (f y) \<le> (1/2)^(def_at x y)"
          using h(1) y(1) by(auto simp: d_le_def[OF 2 h(1) y(1)] submetric_def)
        also have "... \<le> (1/2)^n"
          using \<open>n \<le> def_at x y\<close> by simp
        finally show ?thesis
          using n by simp
      qed
    qed simp
  qed simp
  have 2: "open_map pd.mtopology bdmd.mtopology f"
  proof(rule metric_set_opem_map_from_dist[OF pd.metric_set_axioms bdmd.metric_set_axioms,of f,simplified subtopology_topspace[of bdmd.mtopology,simplified bdmd.mtopology_topspace]])
    fix x :: "nat \<Rightarrow> real" and \<epsilon> :: real
    assume h:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "0 < \<epsilon>"
    then obtain n where n: "(1/2)^n < \<epsilon>"
      using real_arch_pow_inv[OF _ pd.r(2)] by auto
    obtain e where e: "e > 0" "\<And>y. y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1}) \<Longrightarrow> x \<noteq> y \<Longrightarrow> d (f x) (f y) < e \<Longrightarrow> Suc n \<le> def_at x y"
      using d_le_rn_then[OF h(1),of "Suc n"] by auto
    show "\<exists>\<delta>>0. \<forall>y\<in>UNIV \<rightarrow>\<^sub>E {0, 1}. submetric (f ` (UNIV \<rightarrow>\<^sub>E {0, 1})) d (f x) (f y) < \<delta> \<longrightarrow> pd.product_dist x y < \<epsilon>"
    proof(safe intro!: exI[where x=e])
      fix y
      assume y:"y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" and "submetric (f ` (UNIV \<rightarrow>\<^sub>E {0, 1})) d (f x) (f y) < e"
      then have d':"d (f x) (f y) < e"
        using h(1) by(simp add: submetric_def)
      consider "x = y" | "x \<noteq> y" by auto
      thus "pd.product_dist x y < \<epsilon>"
        by cases (use pd.dist_0[OF y y] h(2) def_at_le_then[OF _ h(1) y e(2)[OF y _ d']] n in auto)
    qed(use e(1) in auto)
  qed simp
  have 3: "f ` (topspace pd.mtopology) = topspace bdmd.mtopology"
    by(simp add: bdmd.mtopology_topspace pd.mtopology_topspace)
  have 4: "inj_on f (topspace pd.mtopology)"
    unfolding  pd.mtopology_topspace
  proof
    fix x y
    assume h:"x \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "y \<in> (\<Pi>\<^sub>E i\<in>UNIV. {0,1})" "f x = f y"
    show "x = y"
    proof
      fix n
      have "f y \<in> md.closed_ball (xn (bn (to_listn x (Suc n)))) ((1/2)^bn (to_listn x (Suc n)))"
        using f'[of x "Suc n"] by(simp add: h)
      thus "x n = y n"
        using fy_in[OF h(1,2),of "Suc n"] by simp
    qed
  qed
  show ?thesis
    using homeomorphic_map_imp_homeomorphic_space[OF bijective_open_imp_homeomorphic_map[OF 1 2 3 4]] 0
    by(auto simp: bdmd_sub mpd_top)
qed

lemma(in polish_topology) uncountable_contains_Cantor_space:
  assumes "uncountable (topspace S)"
  shows "\<exists>A. g_delta_of S A \<and> Cantor_space_as_topology homeomorphic_space (subtopology S A)"
proof -
  obtain A where A:"A \<subseteq> topspace S" "Cantor_space_as_topology homeomorphic_space (subtopology S A)"
    using uncountable_contains_Cantor_space'[OF assms] by auto
  then have "g_delta_of S A"
    using Cantor_space_Polish_topology
    by(auto intro!: complete_metrizable_homeo_image_g_delta simp: polish_topology_def complete_metrizable_axioms)
  thus ?thesis
    by(auto intro!: exI[where x=A] A(2))
qed

subsection \<open>Borel Spaces\<close>
text \<open> Borel spaces generated from abstract topology \<close>
definition borel_of :: "'a topology \<Rightarrow> 'a measure" where
"borel_of S \<equiv> sigma (topspace S) {U. openin S U}"

lemma emeasure_borel_of: "emeasure (borel_of S) A = 0"
  by (simp add: borel_of_def emeasure_sigma)

lemma borel_of_euclidean: "borel_of euclidean = borel"
  by(simp add: borel_of_def borel_def)

lemma space_borel_of: "space (borel_of S) = topspace S"
  by(simp add: space_measure_of_conv borel_of_def)

lemma sets_borel_of: "sets (borel_of S) = sigma_sets (topspace S) {U. openin S U}"
  by (simp add: subset_Pow_Union topspace_def borel_of_def)

lemma sets_borel_of_closed: "sets (borel_of S) = sigma_sets (topspace S) {U. closedin S U}"
  unfolding sets_borel_of
proof(safe intro!: sigma_sets_eqI)
  fix a
  assume a:"openin S a"
  have "topspace S - (topspace S - a) \<in> sigma_sets (topspace S) {U. closedin S U}"
    by(rule sigma_sets.Compl) (use a in auto)
  thus "a \<in> sigma_sets (topspace S) {U. closedin S U}"
    using openin_subset[OF a] by (simp add: Diff_Diff_Int inf.absorb_iff2) 
next
  fix b
  assume b:"closedin S b"
  have "topspace S - (topspace S - b) \<in> sigma_sets (topspace S) {U. openin S U}"
    by(rule sigma_sets.Compl) (use b in auto)
  thus "b \<in> sigma_sets (topspace S) {U. openin S U}"
    using closedin_subset[OF b] by (simp add: Diff_Diff_Int inf.absorb_iff2) 
qed

lemma borel_of_open:
  assumes "openin S U"
  shows "U \<in> sets (borel_of S)"
  using assms by (simp add: subset_Pow_Union topspace_def borel_of_def)

lemma borel_of_closed:
  assumes "closedin S U"
  shows "U \<in> sets (borel_of S)"
  using assms sigma_sets.Compl[of "topspace S - U" "topspace S"]
  by (simp add: closedin_def double_diff sets_borel_of)

lemma(in metric_set) nbh_sets[measurable]: "(\<Union>a\<in>A. open_ball a e) \<in> sets (borel_of mtopology)"
  by(auto intro!: borel_of_open openin_clauses(3) openin_open_ball)

lemma borel_of_g_delta_of:
  assumes "g_delta_of S U"
  shows "U \<in> sets (borel_of S)"
  using g_delta_ofD[OF assms] borel_of_open
  by(auto intro!: sets.countable_INT'[of _ id,simplified])

lemma borel_of_subtopology:
 "borel_of (subtopology S U) = restrict_space (borel_of S) U"
proof(rule measure_eqI)
  show "sets (borel_of (subtopology S U)) = sets (restrict_space (borel_of S) U)"
    unfolding restrict_space_eq_vimage_algebra' sets_vimage_algebra sets_borel_of topspace_subtopology space_borel_of Int_commute[of U]
  proof(rule sigma_sets_eqI)
    fix a
    assume "a \<in> Collect (openin (subtopology S U))"
    then obtain T where "openin S T" "a = T \<inter> U"
      by(auto simp: openin_subtopology)
    show "a \<in> sigma_sets (topspace S \<inter> U) {(\<lambda>x. x) -` A \<inter> (topspace S \<inter> U) |A. A \<in> sigma_sets (topspace S) (Collect (openin S))}"
      using openin_subset[OF \<open>openin S T\<close>] \<open>a = T \<inter> U\<close> by(auto intro!: exI[where x=T] \<open>openin S T\<close>)
  next
    fix b
    assume "b \<in> {(\<lambda>x. x) -` A \<inter> (topspace S \<inter> U) |A. A \<in> sigma_sets (topspace S) (Collect (openin S))}"
    then obtain T where ht:"b = T \<inter> (topspace S \<inter> U)" "T \<in> sigma_sets (topspace S) (Collect (openin S))"
      by auto
    hence "b = T \<inter> U"
    proof -
      have "T \<subseteq> topspace S"
        by(rule sigma_sets_into_sp[OF _ ht(2)]) (simp add: subset_Pow_Union topspace_def)
      thus ?thesis
        by(auto simp: ht(1))
    qed
    with ht(2) show "b \<in> sigma_sets (topspace S \<inter> U) (Collect (openin (subtopology S U)))"
    proof(induction arbitrary: b U)
      case (Basic a)
      then show ?case
        by(auto simp: openin_subtopology)
    next
      case Empty
      then show ?case by simp
    next
      case ih:(Compl a)
      then show ?case
        by (simp add: Diff_Int_distrib2 sigma_sets.Compl)
    next
      case (Union a)
      then show ?case
        by (metis UN_extend_simps(4) sigma_sets.Union)
    qed
  qed
qed(simp add: emeasure_borel_of restrict_space_def emeasure_measure_of_conv)


lemma(in metrizable) sigma_sets_eq_cinter_dunion:
 "sigma_sets (topspace S) {U. openin S U} = sigma_sets_cinter_dunion (topspace S) {U. openin S U}"
proof safe
  fix a
  interpret sa: sigma_algebra "topspace S" "sigma_sets (topspace S) {U. openin S U}"
    by(auto intro!: sigma_algebra_sigma_sets openin_subset)
  assume "a \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}"
  then show "a \<in> sigma_sets (topspace S) {U. openin S U}"
    by induction auto
next
  have c:"sigma_sets_cinter_dunion (topspace S) {U. openin S U} \<subseteq> {U\<in>sigma_sets_cinter_dunion (topspace S) {U. openin S U}. topspace S - U \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}}"
  proof
    fix a
    assume a: "a \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}"
    then show "a \<in> {U \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}. topspace S - U \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}}"
    proof induction
      case a:(Basic_cd a)
      then have "g_delta_of S (topspace S - a)"
        by(auto intro!: g_delta_of_closedin)
      from g_delta_ofD'[OF this] obtain U where U:
       "\<And>n :: nat. openin S (U n)" "topspace S - a = \<Inter> (range U)" by auto
      show ?case
        using a U(1) by(auto simp: U(2) intro!: Inter_cd)
    next
      case Top_cd
      then show ?case by auto
    next
      case ca:(Inter_cd a)
      define b where "b \<equiv> (\<lambda>n. (topspace S - a n) \<inter> (\<Inter>i. if i < n then a i else topspace S))"
      have bd:"disjoint_family b"
        using nat_neq_iff by(fastforce simp: disjoint_family_on_def b_def)
      have bin:"b i \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}" for i
        unfolding b_def
        apply(rule sigma_sets_cinter_dunion_int)
        using ca(2)[of i]
         apply auto[1]
        apply(rule Inter_cd) using ca by auto
      have bun:"topspace S - (\<Inter> (range a)) = (\<Union>i. b i)" (is "?lhs = ?rhs")
      proof -
        { fix x
          have "x \<in> ?lhs \<longleftrightarrow> x \<in> topspace S \<and> x \<in> (\<Union>i. topspace S - a i)"
            by auto
          also have "... \<longleftrightarrow> x \<in> topspace S \<and> (\<exists>n. x \<in> topspace S - a n)"
            by auto
          also have "... \<longleftrightarrow> x \<in> topspace S \<and> (\<exists>n. x \<in> topspace S - a n \<and> (\<forall>i<n. x \<in> a i))"
          proof safe
            fix n
            assume 1:"x \<notin> a n" "x \<in> topspace S"
            define N where "N \<equiv> Min {m. m \<le> n \<and> x \<notin> a m}"
            have N:"x \<notin> a N" "N \<le> n"
              using linorder_class.Min_in[of "{m. m \<le> n \<and> x \<notin> a m}"] 1
              by(auto simp: N_def)
            have N':"x \<in> a i" if "i < N" for i
            proof(rule ccontr)
              assume "x \<notin> a i"
              then have "N \<le> i"
                using linorder_class.Min_le[of "{m. m \<le> n \<and> x \<notin> a m}" i] that N(2)
                by(auto simp: N_def)
              with that show False by auto
            qed
            show "\<exists>n. x \<in> topspace S - a n \<and> (\<forall>i<n. x \<in> a i)"
              using N N' by(auto intro!: exI[where x=N] 1)
          qed auto
          also have "... \<longleftrightarrow> x \<in> ?rhs"
            by(auto simp: b_def)
          finally have "x \<in> ?lhs \<longleftrightarrow> x \<in> ?rhs" . }
        thus ?thesis by auto
      qed
      have "... \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}"
        by(rule Union_cd) (use bin bd in auto)
      thus ?case
        using Inter_cd[of a,OF ca(1)] by(auto simp: bun)
    next
      case ca:(Union_cd a)
      have "topspace S - (\<Union> (range a)) = (\<Inter>i. (topspace S - a i))"
        by simp
      have "... \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}"
        by(rule Inter_cd) (use ca in auto)
      then show ?case
        using Union_cd[of a,OF ca(1,2)] by auto 
    qed
  qed
  fix a
  assume "a \<in> sigma_sets (topspace S) {U. openin S U}"
  then show "a \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}"
  proof induction
    case a:(Union a)
    define b where "b \<equiv> (\<lambda>n. a n \<inter>  (\<Inter>i. if i < n then topspace S - a i else topspace S))"
    have bd:"disjoint_family b"
      by(auto simp: disjoint_family_on_def b_def) (metis Diff_iff UnCI image_eqI linorder_neqE_nat mem_Collect_eq)
    have bin:"b i \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}" for i
      unfolding b_def
      apply(rule sigma_sets_cinter_dunion_int)
      using a(2)[of i]
       apply auto[1]
      apply(rule Inter_cd) using c a by auto
    have bun:"(\<Union>i. a i) = (\<Union>i. b i)" (is "?lhs = ?rhs")
    proof -
      {
        fix x
        have "x \<in> ?lhs \<longleftrightarrow> x \<in> topspace S \<and> x \<in> ?lhs"
          using sigma_sets_cinter_dunion_into_sp[OF _ a(2)]
          by (metis UN_iff subsetD subset_Pow_Union topspace_def)
        also have "... \<longleftrightarrow> x \<in> topspace S \<and> (\<exists>n. x \<in> a n)" by auto
        also have "... \<longleftrightarrow> x \<in> topspace S \<and> (\<exists>n. x \<in> a n \<and> (\<forall>i<n. x \<in> topspace S - a i))"
        proof safe
          fix n
          assume 1:"x \<in> topspace S" "x \<in> a n"
          define N where "N \<equiv> Min {m. m \<le> n \<and> x \<in> a m}"
          have N:"x \<in> a N" "N \<le> n"
            using linorder_class.Min_in[of "{m. m \<le> n \<and> x \<in> a m}"] 1
            by(auto simp: N_def)
          have N':"x \<notin> a i" if "i < N" for i
          proof(rule ccontr)
            assume "\<not> x \<notin> a i"
            then have "N \<le> i"
              using linorder_class.Min_le[of "{m. m \<le> n \<and> x \<in> a m}" i] that N(2)
              by(auto simp: N_def)
            with that show False by auto
          qed
          show "\<exists>n. x \<in> a n \<and> (\<forall>i<n. x \<in> topspace S - a i)"
            using N N' 1 by(auto intro!: exI[where x=N])
        qed auto
        also have "... \<longleftrightarrow> x \<in> ?rhs"
        proof safe
          fix m
          assume "x \<in> b m"
          then show "x \<in> topspace S" "\<exists>n. x \<in> a n \<and> (\<forall>i<n. x \<in> topspace S - a i)"
            by(auto intro!: exI[where x=m] simp: b_def)
        qed(auto simp: b_def)
        finally have "x \<in> ?lhs \<longleftrightarrow> x \<in> ?rhs" . }
      thus ?thesis by auto
    qed
    have "... \<in> sigma_sets_cinter_dunion (topspace S) {U. openin S U}"
      by(rule Union_cd) (use bin bd in auto)
    thus ?case
      by(auto simp: bun)
  qed(use c in auto)
qed

lemma(in metrizable) sigma_sets_eq_cinter:
 "sigma_sets (topspace S) {U. openin S U} = sigma_sets_cinter (topspace S) {U. openin S U}"
proof safe
  fix a
  interpret sa: sigma_algebra "topspace S" "sigma_sets (topspace S) {U. openin S U}"
    by(auto intro!: sigma_algebra_sigma_sets openin_subset)
  assume "a \<in> sigma_sets_cinter (topspace S) {U. openin S U}"
  then show "a \<in> sigma_sets (topspace S) {U. openin S U}"
    by induction auto
qed (use sigma_sets_cinter_dunion_subset sigma_sets_eq_cinter_dunion in auto)


lemma continuous_map_measurable:
  assumes "continuous_map X Y f"
  shows "f \<in> borel_of X \<rightarrow>\<^sub>M borel_of Y"
proof(rule measurable_sigma_sets[OF sets_borel_of[of Y]])
  show "{U. openin Y U} \<subseteq> Pow (topspace Y)"
    by (simp add: subset_Pow_Union topspace_def)
next
  show "f \<in> space (borel_of X) \<rightarrow> topspace Y"
    using continuous_map_image_subset_topspace[OF assms]
    by(auto simp: space_borel_of)
next
  fix U
  assume "U \<in> {U. openin Y U}"
  then have "openin X (f -` U \<inter> topspace X)"
    using continuous_map[of X Y f] assms by auto
  thus "f -` U \<inter> space (borel_of X) \<in> sets (borel_of X)"
    by(simp add: space_borel_of sets_borel_of)
qed

lemma open_map_preserves_sets:
  assumes "open_map S T f" "inj_on f (topspace S)" "A \<in> sets (borel_of S)"
  shows "f ` A \<in> sets (borel_of T)"
  using assms(3)[simplified sets_borel_of]
proof(induction)
  case (Basic a)
  with assms(1) show ?case
    by(auto simp: sets_borel_of open_map_def)
next
  case Empty
  show ?case by simp
next
  case (Compl a)
  moreover have "f ` (topspace S - a) = f ` (topspace S) - f ` a"
    by (metis Diff_subset assms(2) calculation(1) inj_on_image_set_diff sigma_sets_into_sp subset_Pow_Union topspace_def)
  moreover have "f ` (topspace S) \<in> sets (borel_of T)"
    by (meson assms(1) borel_of_open open_map_def openin_topspace)
  ultimately show ?case
    by auto
next
  case (Union a)
  then show ?case
    by (simp add: image_UN)
qed

lemma open_map_preserves_sets':
  assumes "open_map S (subtopology T (f ` (topspace S))) f" "inj_on f (topspace S)" "f ` (topspace S) \<in> sets (borel_of T)" "A \<in> sets (borel_of S)"
  shows "f ` A \<in> sets (borel_of T)"
  using assms(4)[simplified sets_borel_of]
proof(induction)
  case (Basic a)
  then have "openin (subtopology T (f ` (topspace S))) (f ` a)"
    using assms(1) by(auto simp: open_map_def)
  hence "f ` a \<in> sets (borel_of (subtopology T (f ` (topspace S))))"
    by(simp add: sets_borel_of)
  hence "f ` a \<in> sets (restrict_space (borel_of T) (f ` (topspace S)))"
    by(simp add: borel_of_subtopology)
  thus ?case
    by (metis sets_restrict_space_iff assms(3) sets.Int_space_eq2)
next
  case Empty
  show ?case by simp
next
  case (Compl a)
  moreover have "f ` (topspace S - a) = f ` (topspace S) - f ` a"
    by (metis Diff_subset assms(2) calculation(1) inj_on_image_set_diff sigma_sets_into_sp subset_Pow_Union topspace_def)
  ultimately show ?case
    using assms(3) by auto
next
  case (Union a)
  then show ?case
    by (simp add: image_UN)
qed


text \<open> Abstract topology version of @{thm second_countable_borel_measurable}. \<close>
lemma borel_of_second_countable':
  assumes "second_countable S" and "subbase_of S \<U>"
  shows "borel_of S = sigma (topspace S) \<U>"
  unfolding borel_of_def
proof(rule sigma_eqI)
  show "{U. openin S U} \<subseteq> Pow (topspace S)"
    by (simp add: subset_Pow_Union topspace_def)
next
  show "\<U> \<subseteq> Pow (topspace S)"
    using subbase_of_subset[OF assms(2)] by auto
next
  interpret s: sigma_algebra "topspace S" "sigma_sets (topspace S) \<U>"
    using subbase_of_subset[OF assms(2)] by(auto intro!: sigma_algebra_sigma_sets)
  obtain \<O> where ho: "countable \<O>" "base_of S \<O>"
    using assms(1) by(auto simp: second_countable_def)
  show "sigma_sets (topspace S) {U. openin S U} = sigma_sets (topspace S) \<U>"
  proof(rule sigma_sets_eqI)
    fix U
    assume "U \<in> {U. openin S U}"
    then have "generate_topology_on \<U> U"
      using assms(2) by(simp add: subbase_of_def openin_topology_generated_by_iff)
    thus "U \<in> sigma_sets (topspace S) \<U>"
    proof induction
      case (UN K)
      with ho(2) obtain V where hv:
       "\<And>k. k \<in> K \<Longrightarrow> V k \<subseteq> \<O>" "\<And>k. k \<in> K \<Longrightarrow> \<Union> (V k) = k"
        by(simp add: base_of_def openin_topology_generated_by_iff[symmetric] assms(2)[simplified subbase_of_def,symmetric]) metis
      define \<U>k where "\<U>k = (\<Union>k\<in>K. V k)"
      have 0:"countable \<U>k"
        using hv by(auto intro!: countable_subset[OF _ ho(1)] simp: \<U>k_def)
      have "\<Union> \<U>k = (\<Union>A\<in>\<U>k. A)" by auto
      also have "... = \<Union> K"
        unfolding \<U>k_def UN_simps by(simp add: hv(2))
      finally have 1:"\<Union> \<U>k = \<Union> K" .
      have "\<forall>b\<in>\<U>k. \<exists>k\<in>K. b \<subseteq> k"
        using hv by (auto simp: \<U>k_def)
      then obtain V' where hv': "\<And>b. b \<in> \<U>k \<Longrightarrow> V' b \<in> K" and "\<And>b. b \<in> \<U>k \<Longrightarrow> b \<subseteq> V' b"
        by metis
      then have "(\<Union>b\<in>\<U>k. V' b) \<subseteq> \<Union>K" "\<Union>\<U>k \<subseteq> (\<Union>b\<in>\<U>k. V' b)"
        by auto
      then have "\<Union>K = (\<Union>b\<in>\<U>k. V' b)"
        unfolding 1 by auto
      also have "\<dots> \<in> sigma_sets (topspace S) \<U>"
        using hv' UN by(auto intro!: s.countable_UN' simp: 0)
      finally show "\<Union>K \<in> sigma_sets (topspace S) \<U>" .
    qed auto
  next
    fix U
    assume "U \<in> \<U>"
    from assms(2)[simplified subbase_of_def] openin_topology_generated_by_iff generate_topology_on.Basis[OF this]
    show "U \<in> sigma_sets (topspace S) {U. openin S U}"
      by auto
  qed
qed

text \<open> Abstract topology version @{thm borel_prod}.\<close>
lemma borel_of_prod:
  assumes "second_countable S" and "second_countable S'"
  shows "borel_of S \<Otimes>\<^sub>M borel_of S' = borel_of (prod_topology S S')"
proof -
  have "borel_of S \<Otimes>\<^sub>M borel_of S' = sigma (topspace S \<times> topspace S') {a \<times> b |a b. a \<in> {a. openin S a} \<and> b \<in> {b. openin S' b}}"
  proof -
    obtain \<O> \<O>' where ho:
    "countable \<O>" "base_of S \<O>" "countable \<O>'" "base_of S' \<O>'"
      using assms by(auto simp: second_countable_def)
    show ?thesis
      unfolding borel_of_def
      apply(rule sigma_prod)
      using topology_generated_by_topspace[of \<O>,simplified base_is_subbase[OF ho(2),simplified subbase_of_def,symmetric]] topology_generated_by_topspace[of \<O>',simplified base_is_subbase[OF ho(4),simplified subbase_of_def,symmetric]]
              base_of_openin[OF ho(2)] base_of_openin[OF ho(4)]
      by(auto intro!: exI[where x=\<O>] exI[where x=\<O>'] simp: ho subset_Pow_Union topspace_def)
  qed
  also have "... = borel_of (prod_topology S S')"
    using borel_of_second_countable'[OF prod_topology_second_countable[OF assms],simplified subbase_of_def,OF prod_topology_generated_by_open]
    by simp
  finally show ?thesis .
qed

lemma product_borel_of_measurable:
  assumes "i \<in> I"
  shows "(\<lambda>x. x i) \<in> (borel_of (product_topology S I)) \<rightarrow>\<^sub>M borel_of (S i)"
  by(auto intro!: continuous_map_measurable simp: assms)


text \<open> Abstract topology version of @{thm sets_PiM_subset_borel} \<close>
lemma sets_PiM_subset_borel_of:
  "sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i)) \<subseteq> sets (borel_of (product_topology S I))"
proof -
  have *: "(\<Pi>\<^sub>E i\<in>I. X i) \<in> sets (borel_of (product_topology S I))" if [measurable]:"\<And>i. X i \<in> sets (borel_of (S i))" "finite {i. X i \<noteq> topspace (S i)}" for X
  proof -
    note [measurable] = product_borel_of_measurable
    define I' where "I' = {i. X i \<noteq> topspace (S i)} \<inter> I"
    have "finite I'" unfolding I'_def using that by simp
    have "(\<Pi>\<^sub>E i\<in>I. X i) = (\<Inter>i\<in>I'. (\<lambda>x. x i)-`(X i) \<inter> space (borel_of (product_topology S I))) \<inter> space (borel_of (product_topology S I))"
    proof(standard;standard)
      fix x
      assume "x \<in> Pi\<^sub>E I X"
      then show "x \<in> (\<Inter>i\<in>I'. (\<lambda>x. x i) -` X i \<inter> space (borel_of (product_topology S I))) \<inter> space (borel_of (product_topology S I))"
        using sets.sets_into_space[OF that(1)] by(auto simp: PiE_def I'_def Pi_def space_borel_of)
    next
      fix x
      assume 1:"x \<in> (\<Inter>i\<in>I'. (\<lambda>x. x i) -` X i \<inter> space (borel_of (product_topology S I))) \<inter> space (borel_of (product_topology S I))"
      have "x i \<in> X i" if hi:"i \<in> I" for i
      proof -
        consider "i \<in> I' \<and> I' \<noteq> {}" | "i \<notin> I' \<and> I' = {}" | "i \<notin> I' \<and> I' \<noteq> {}" by auto
        then show ?thesis
          apply cases
          using sets.sets_into_space[OF \<open>\<And>i. X i \<in> sets (borel_of (S i))\<close>] 1 that
          by(auto simp: space_borel_of I'_def)
      qed
      then show "x \<in> Pi\<^sub>E I X"
        using 1 by(auto simp: space_borel_of)
    qed
    also have "... \<in> sets (borel_of (product_topology S I))"
     using that \<open>finite I'\<close> by(auto simp: I'_def)
    finally show ?thesis .
  qed
  then have "{Pi\<^sub>E I X |X. (\<forall>i. X i \<in> sets (borel_of (S i))) \<and> finite {i. X i \<noteq> space (borel_of (S i))}} \<subseteq> sets (borel_of (product_topology S I))"
    by(auto simp: space_borel_of)
  show ?thesis unfolding sets_PiM_finite
    by(rule sets.sigma_sets_subset',fact) (simp add: borel_of_open[OF openin_topspace, of "product_topology S I",simplified] space_borel_of)
qed

text \<open> Abstract topology version of @{thm sets_PiM_equal_borel}.\<close>
lemma sets_PiM_equal_borel_of:
  assumes "countable I" and "\<And>i. i \<in> I \<Longrightarrow> second_countable (S i)"
  shows "sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i)) = sets (borel_of (product_topology S I))"
proof
  obtain K where hk:
  "countable K" "base_of (product_topology S I) K"
  "\<And>k. k \<in> K \<Longrightarrow> \<exists>X. (k = (\<Pi>\<^sub>E i\<in>I. X i)) \<and> (\<forall>i. openin (S i) (X i)) \<and> finite {i. X i \<noteq> topspace (S i)} \<and> {i. X i \<noteq> topspace (S i)} \<subseteq> I"
    using product_topology_countable_base_of[OF assms(1)] assms(2)
    by force
  have *:"k \<in> sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i))" if "k \<in> K" for k
  proof -
    obtain X where H: "k = (\<Pi>\<^sub>E i\<in>I. X i)" "\<And>i. openin (S i) (X i)" "finite {i. X i \<noteq> topspace (S i)}" "{i. X i \<noteq> topspace (S i)} \<subseteq> I"
      using hk(3)[OF \<open>k \<in> K\<close>] by blast
    show ?thesis unfolding H(1) sets_PiM_finite
      using borel_of_open[OF H(2)] H(3) by(auto simp: space_borel_of)
  qed
  have **: "U \<in> sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i))" if "openin (product_topology S I) U" for U
  proof -
    obtain B where "B \<subseteq> K" "U = (\<Union>B)"
      using \<open>openin (product_topology S I) U\<close> \<open>base_of (product_topology S I) K\<close> by (metis base_of_def)
    have "countable B" using \<open>B \<subseteq> K\<close> \<open>countable K\<close> countable_subset by blast
    moreover have "k \<in> sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i))" if "k \<in> B" for k
      using \<open>B \<subseteq> K\<close> * that by auto
    ultimately show ?thesis unfolding \<open>U = (\<Union>B)\<close> by auto
  qed
  have "sigma_sets (topspace (product_topology S I)) {U. openin (product_topology S I) U} \<subseteq> sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i))"
    apply (rule sets.sigma_sets_subset') using ** by(auto intro!: sets_PiM_I_countable[OF assms(1)] simp: borel_of_open[OF openin_topspace])
  thus " sets (borel_of (product_topology S I)) \<subseteq> sets (\<Pi>\<^sub>M i\<in>I. borel_of (S i))"
    by (simp add: subset_Pow_Union topspace_def borel_of_def) 
qed(rule sets_PiM_subset_borel_of)



lemma homeomorphic_map_borel_isomorphic:
  assumes "homeomorphic_map X Y f"
  shows "measurable_isomorphic_map (borel_of X) (borel_of Y) f"
proof -
  obtain g where "homeomorphic_maps X Y f g"
    using assms by(auto simp: homeomorphic_map_maps)
  hence "continuous_map X Y f" "continuous_map Y X g"
        "\<And>x. x \<in> topspace X \<Longrightarrow> g (f x) = x"
        "\<And>y. y \<in> topspace Y \<Longrightarrow> f (g y) = y"
    by(auto simp: homeomorphic_maps_def)
  thus ?thesis
    by(auto intro!: measurable_isomorphic_map_byWitness dest: continuous_map_measurable simp: space_borel_of)
qed

lemma homeomorphic_space_measurable_isomorphic:
  assumes "S homeomorphic_space T"
  shows "borel_of S measurable_isomorphic borel_of T"
  using homeomorphic_map_borel_isomorphic[of S T] assms by(auto simp: measurable_isomorphic_def homeomorphic_space)


lemma measurable_isomorphic_borel_map:
  assumes "sets M = sets (borel_of S)" and f: "measurable_isomorphic_map M N f"
  shows "\<exists>S'. homeomorphic_map S S' f \<and> sets N = sets (borel_of S')"
proof -
  obtain g where fg:"f \<in> M \<rightarrow>\<^sub>M N" "g \<in> N \<rightarrow>\<^sub>M M" "\<And>x. x\<in>space M \<Longrightarrow> g (f x) = x" "\<And>y. y\<in>space N \<Longrightarrow> f (g y) = y" "\<And>A. A\<in>sets M \<Longrightarrow> f ` A \<in> sets N" "\<And>A. A\<in>sets N \<Longrightarrow> g ` A \<in> sets M" "bij_betw g (space N) (space M)"
    using measurable_isomorphic_mapD'[OF f] by metis
  have g:"measurable_isomorphic_map N M g"
    by(auto intro!: measurable_isomorphic_map_byWitness fg)
  have g':"bij_betw g (space N) (topspace S)"
    using fg(7) sets_eq_imp_space_eq[OF assms(1)] by(auto simp: space_borel_of)
  show ?thesis
  proof(intro exI[where x="pullback_topology (space N) g S"] conjI)
    have [simp]: "{U. openin (pullback_topology (space N) g S) U} = (`) f ` {U. openin S U}"
      unfolding openin_pullback_topology'[OF g']
    proof safe
      fix u
      assume u:"openin S u"
      then have 1:"u \<subseteq> space M"
        by(simp add: sets_eq_imp_space_eq[OF assms(1)] space_borel_of openin_subset)
      with fg(3) have "g ` f ` u = u"
        by(fastforce simp: image_def)
      with u show "openin S (g ` f ` u)" by simp
      fix x
      assume "x \<in> u"
      with 1 fg(1) show "f x \<in> space N" by(auto simp: measurable_space)
    next
      fix u
      assume "openin S (g ` u)" "u \<subseteq> space N"
      with fg(4) show "u \<in> (`) f ` {U. openin S U}"
        by(auto simp: image_def intro!: exI[where x="g ` u"]) (metis in_mono)
    qed
    have [simp]:"g -` topspace S \<inter> space N = space N"
      using bij_betw_imp_surj_on g' by blast
    show "sets N = sets (borel_of (pullback_topology (space N) g S))"
      by(auto simp: sets_borel_of topspace_pullback_topology intro!: measurable_isomorphic_map_sigma_sets[OF assms(1)[simplified sets_borel_of space_borel_of[symmetric] sets_eq_imp_space_eq[OF assms(1),symmetric]] f])
  next
    show "homeomorphic_map S (pullback_topology (space N) g S) f"
    proof(rule homeomorphic_maps_imp_map[where g=g])
      obtain f' where f':"homeomorphic_maps (pullback_topology (space N) g S) S g f'"
        using topology_from_bij(1)[OF g'] homeomorphic_map_maps by blast
      have f'2:"f' y = f y" if y:"y \<in> topspace S" for y
      proof -
        have [simp]:"g -` topspace S \<inter> space N = space N"
          using bij_betw_imp_surj_on g' by blast
        obtain x where "x \<in> space N" "y = g x"
          using g' y by(auto simp: bij_betw_def image_def)
        thus ?thesis
          using fg(4) f' by(auto simp: homeomorphic_maps_def topspace_pullback_topology)
      qed
      thus "homeomorphic_maps S (pullback_topology (space N) g S) f g"
        by(auto intro!: homeomorphic_maps_eq[OF f'] simp: homeomorphic_maps_sym[of S])
    qed
  qed
qed

lemma measurable_isomorphic_borels:
  assumes "sets M = sets (borel_of S)" "M measurable_isomorphic N"
  shows "\<exists>S'. S homeomorphic_space S' \<and> sets N = sets (borel_of S')"
  using measurable_isomorphic_borel_map[OF assms(1)] assms(2) homeomorphic_map_maps
  by(fastforce simp: measurable_isomorphic_def homeomorphic_space_def )

lemma(in polish_topology) closedin_clopen_topology:
  assumes "closedin S a"
  shows "\<exists>S'. polish_topology S' \<and> (\<forall>u. openin S u \<longrightarrow> openin S' u) \<and> topspace S = topspace S' \<and> sets (borel_of S) = sets (borel_of S') \<and> openin S' a \<and> closedin S' a"
proof -
  have "polish_topology (subtopology S a)"
    by(rule closedin_polish[OF assms])
  from polish_topology.bounded_polish_metric[OF this] obtain da where da:
    "polish_metric_set a da" "subtopology S a = metric_set.mtopology a da" "\<And>x y. da x y < 1"
    by (metis topspace_subtopology_subset closedin_subset[OF assms])
  interpret pa: polish_metric_set a da by fact
  have "polish_topology (subtopology S (topspace S - a))"
    using assms by(auto intro!: openin_polish)
  from polish_topology.bounded_polish_metric[OF this]
  obtain db where db: "polish_metric_set (topspace S - a) db" "subtopology S (topspace S - a) = metric_set.mtopology (topspace S - a) db" "\<And>x y. db x y < 1"
    by (metis Diff_subset topspace_subtopology_subset)
  interpret pb: polish_metric_set "topspace S - a" db by fact
  interpret p: sum_polish_metric UNIV "\<lambda>b. if b then a else topspace S - a" "\<lambda>b. if b then da else db"
    using da db by(auto intro!: sum_polish_metricI simp: disjoint_family_on_def)
  have 0: "(\<Union>i. if i then a else topspace S - a) = topspace S"
    using closedin_subset assms by auto

  have 1: "sets (borel_of S) = sets (borel_of p.mtopology)"
  proof -
    have "sigma_sets (topspace S) (Collect (openin S)) = sigma_sets (topspace S) (Collect (openin p.mtopology))"
    proof(rule sigma_sets_eqI)
      fix a
      assume "a \<in> Collect (openin S)"
      then have "openin p.mtopology a"
        by(simp only: p.openin_sum_mtopology_iff) (auto simp: 0 da(2)[symmetric] db(2)[symmetric] openin_subtopology dest:openin_subset)
      thus "a \<in> sigma_sets (topspace S) (Collect (openin p.mtopology))"
        by auto
    next
      interpret s: sigma_algebra "topspace S" "sigma_sets (topspace S) (Collect (openin S))"
        by(auto intro!: sigma_algebra_sigma_sets openin_subset)
      fix b
      assume "b \<in> Collect (openin p.mtopology)"
      then have "openin p.mtopology b" by auto
      then have b:"b \<subseteq> topspace S" "openin (subtopology S a) (b \<inter> a)" "openin (subtopology S (topspace S - a)) (b \<inter> (topspace S - a))"
        by(simp_all only: p.openin_sum_mtopology_iff,insert 0 da(2) db(2)) (auto simp: all_bool_eq)
      have [simp]: "(b \<inter> a) \<union> (b \<inter> (topspace S - a)) = b"
        using Diff_partition b(1) by blast
      have "(b \<inter> a) \<union> (b \<inter> (topspace S - a)) \<in> sigma_sets (topspace S) (Collect (openin S))"
      proof(rule sigma_sets_Un)
        have [simp]:"a \<in> sigma_sets (topspace S) (Collect (openin S))"
        proof -
          have "topspace S - (topspace S - a) \<in> sigma_sets (topspace S) (Collect (openin S))"
            by(rule sigma_sets.Compl) (use assms in auto)
          thus ?thesis
            using double_diff[OF closedin_subset[OF assms]] by simp
        qed            
        from b(2,3) obtain T T' where T:"openin S T" "openin S T'" and [simp]:"b \<inter> a = T \<inter> a" "b \<inter> (topspace S - a) = T' \<inter> (topspace S - a)"
          by(auto simp: openin_subtopology)
        show "b \<inter> a \<in> sigma_sets (topspace S) (Collect (openin S))"
             "b \<inter> (topspace S - a) \<in> sigma_sets (topspace S) (Collect (openin S))"
          using T assms by auto
      qed
      thus "b \<in> sigma_sets (topspace S) (Collect (openin S))"
        by simp
    qed
    thus ?thesis
      by(simp only: sets_borel_of p.mtopology_topspace) (use 0 in auto)
  qed
  have 2:"\<And>u. openin S u \<Longrightarrow> openin p.mtopology u"
    by(simp only: p.openin_sum_mtopology_iff) (auto simp: all_bool_eq da(2)[symmetric] db(2)[symmetric] openin_subtopology dest:openin_subset)
  have 3:"openin p.mtopology a"
    by(simp only: p.openin_sum_mtopology_iff) (auto simp: all_bool_eq)
  have 4:"closedin p.mtopology a"
    by (metis 0 2 assms closedin_def p.mtopology_topspace)
  have 5: "topspace S = topspace p.mtopology"
    by(simp only: p.mtopology_topspace) (simp only: 0)
  have 6: "polish_topology p.mtopology"
    using p.polish_topology_axioms by blast
  show ?thesis
    by(rule exI[where x=p.mtopology]) (insert 5 2 6, simp only: 1 3 4 ,auto)
qed

lemma polish_topology_union_polish:
  fixes X :: "nat \<Rightarrow> 'a topology"
  assumes "\<And>n. polish_topology (X n)" "\<And>n. topspace (X n) = Xt" "\<And>x y. x \<in> Xt \<Longrightarrow> y \<in> Xt \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>Ox Oy. (\<forall>n. openin (X n) Ox) \<and> (\<forall>n. openin (X n) Oy) \<and> x \<in> Ox \<and> y \<in> Oy \<and> disjnt Ox Oy"
  defines "Xun \<equiv> topology_generated_by (\<Union>n. {u. openin (X n) u})"
  shows "polish_topology Xun"
proof -
  have topsXun:"topspace Xun = Xt"
    using assms(2) by(auto simp: Xun_def dest:openin_subset)
  define f :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where "f \<equiv> (\<lambda>x n. x)"
  have "continuous_map Xun (product_topology X UNIV) f"
    by(auto simp: assms(2) topsXun f_def continuous_map_componentwise, auto simp: Xun_def openin_topology_generated_by_iff continuous_map_def assms(2) dest:openin_subset[of "X _",simplified assms(2)] )
      (insert openin_subopen, fastforce intro!: generate_topology_on.Basis)
  hence 1: "continuous_map Xun (subtopology (product_topology X UNIV) (f ` (topspace Xun))) f"
    by(auto simp: continuous_map_in_subtopology)
  have 2: "inj_on f (topspace Xun)"
    by(auto simp: inj_on_def f_def dest:fun_cong)
  have 3: "f ` (topspace Xun) = topspace (subtopology (product_topology X UNIV) (f ` (topspace Xun)))"
    by(auto simp: topsXun assms(2) f_def)
  have 4: "open_map Xun (subtopology (product_topology X UNIV) (f ` (topspace Xun))) f"
  proof(safe intro!: open_map_generated_topo[OF _ 2[simplified Xun_def],simplified Xun_def[symmetric]])
    fix u n
    assume u:"openin (X n) u"
    show "openin (subtopology (product_topology X UNIV) (f ` topspace Xun)) (f ` u)"
      unfolding openin_subtopology
    proof(safe intro!: exI[where x="{ \<lambda>i. if i = n then a else b i |a b. a \<in>u \<and> b \<in> UNIV \<rightarrow> Xt}"])
      show "openin (product_topology X UNIV) {\<lambda>i. if i = n then a else b i |a b. a \<in>u \<and> b \<in> UNIV \<rightarrow> Xt}"
        by(auto simp: openin_product_topology_alt u assms(2) openin_topspace[of "X _",simplified assms(2)] intro!: exI[where x="\<lambda>i. if i = n then u else Xt"])
          (auto simp: PiE_def Pi_def, metis openin_subset[OF u,simplified assms(2)] in_mono)
    next
      show "\<And>y. y \<in> u \<Longrightarrow> \<exists>a b. f y = (\<lambda>i. if i = n then a else b i) \<and> a \<in> u \<and> b \<in> UNIV \<rightarrow> Xt"
        using assms(2) f_def openin_subset u by fastforce
    next
      show "\<And>y. y \<in> u \<Longrightarrow> f y \<in> f ` topspace Xun"
        using openin_subset[OF u] by(auto simp: assms(2) topsXun)
    next
      show "\<And>x xa a b. xa \<in> topspace Xun \<Longrightarrow> f xa = (\<lambda>i. if i = n then a else b i) \<Longrightarrow> a \<in> u \<Longrightarrow> b \<in> UNIV \<rightarrow> Xt \<Longrightarrow> f xa \<in> f ` u"
        using openin_subset[OF u] by(auto simp: topsXun assms(2)) (metis f_def imageI)
    qed
  qed
  have 5:"(subtopology (product_topology X UNIV) (f ` topspace Xun)) homeomorphic_space Xun"
    using homeomorphic_map_imp_homeomorphic_space[OF bijective_open_imp_homeomorphic_map[OF 1 4 3 2]]
    by(simp add: homeomorphic_space_sym[of Xun])
  show ?thesis
  proof(safe intro!: polish_topology.homeomorphic_polish_topology[OF polish_topology.closedin_polish[OF polish_topology_product] 5] assms)
    show "closedin (product_topology X UNIV) (f ` topspace Xun)"
    proof -
      have 1: "openin (product_topology X UNIV) ((UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt)"
      proof(rule openin_subopen[THEN iffD2])
        show "\<forall>x\<in>(UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt. \<exists>T. openin (product_topology X UNIV) T \<and> x \<in> T \<and> T \<subseteq> (UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt"
        proof safe
          fix x
          assume x:"x \<in> UNIV \<rightarrow>\<^sub>E Xt" "x \<notin> f ` Xt"
          have "\<exists>n. x n \<noteq> x 0"
          proof(rule ccontr)
            assume " \<nexists>n. x n \<noteq> x 0"
            then have "\<forall>n. x n = x 0" by auto
            hence "x = (\<lambda>_. x 0)" by auto
            thus False
              using x by(auto simp: f_def topsXun assms(2))
          qed
          then obtain n where n: "n \<noteq> 0" "x n \<noteq> x 0"
            by metis
          from assms(3)[OF _ _ this(2)] x
          obtain On O0 where h:"\<And>n. openin (X n) On" "\<And>n. openin (X n) O0" "x n \<in> On" "x 0 \<in> O0" "disjnt On O0"
            by fastforce
          have "openin (product_topology X UNIV) ((\<lambda>x. x 0) -` O0 \<inter> topspace (product_topology X UNIV))"
            using continuous_map_product_coordinates[of 0 UNIV X] h(2)[of 0] by blast
          moreover have "openin (product_topology X UNIV) ((\<lambda>x. x n) -` On \<inter> topspace (product_topology X UNIV))"
            using continuous_map_product_coordinates[of n UNIV X] h(1)[of n] by blast
          ultimately have op: "openin (product_topology X UNIV) ((\<lambda>T. T 0) -` O0 \<inter> topspace (product_topology X UNIV) \<inter> ((\<lambda>T. T n) -` On \<inter> topspace (product_topology X UNIV)))"
            by auto
          have xin:"x \<in> (\<lambda>T. T 0) -` O0 \<inter> topspace (product_topology X UNIV) \<inter> ((\<lambda>T. T n) -` On \<inter> topspace (product_topology X UNIV))"
            using x h(3,4) by(auto simp: assms(2))
          have subset:"(\<lambda>T. T 0) -` O0 \<inter> topspace (product_topology X UNIV) \<inter> ((\<lambda>T. T n) -` On \<inter> topspace (product_topology X UNIV)) \<subseteq> (UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt"
            using h(5) by(auto simp: assms(2) disjnt_def f_def)

          show "\<exists>T. openin (product_topology X UNIV) T \<and> x \<in> T \<and> T \<subseteq> (UNIV \<rightarrow>\<^sub>E Xt) - f ` Xt"
            by(rule exI[where x="((\<lambda>x. x 0) -` O0 \<inter> topspace (product_topology X UNIV)) \<inter> ((\<lambda>x. x n) -` On \<inter> topspace (product_topology X UNIV))"]) (use op xin subset in auto)
        qed
      qed

      thus ?thesis
        by(auto simp: closedin_def assms(2) topsXun f_def)
    qed
  qed(simp add: f_def)
qed

lemma(in polish_topology) sets_clopen_topology:
  assumes "a \<in> sets (borel_of S)"
  shows "\<exists>S'. polish_topology S' \<and> (\<forall>u. openin S u \<longrightarrow> openin S' u) \<and> topspace S = topspace S' \<and> sets (borel_of S) = sets (borel_of S') \<and> openin S' a \<and> closedin S' a"
proof -
  have "a \<in> sigma_sets (topspace S) {U. closedin S U}"
    using assms by(simp add: sets_borel_of_closed)
  thus ?thesis
  proof induction
    case (Basic a)
    then show ?case
      by(simp add: closedin_clopen_topology)
  next
    case Empty
    with polish_topology_axioms show ?case
      by auto
  next
    case (Compl a)
    then obtain S' where S':"polish_topology S'" "(\<forall>u. openin S u \<longrightarrow> openin S' u)" "topspace S = topspace S'" "sets (borel_of S) = sets (borel_of S')" "openin S' a" "closedin S' a"
      by auto
    from polish_topology.closedin_clopen_topology[OF S'(1) S'(6)] S'
    show ?case by auto
  next
    case ih:(Union a)
    then obtain Si where Si:
    "\<And>i. polish_topology (Si i)" "\<And>u i. openin S u \<Longrightarrow> openin (Si i) u" "\<And>i::nat. topspace S = topspace (Si i)" "\<And>i. sets (borel_of S) = sets (borel_of (Si i))" "\<And>i. openin (Si i) (a i)" "\<And>i. closedin (Si i) (a i)"
      by metis
    define Sun where "Sun \<equiv> topology_generated_by (\<Union>n. {u. openin (Si n) u})"
    have Sun1: "polish_topology Sun"
      unfolding Sun_def 
    proof(safe intro!: polish_topology_union_polish[where Xt="topspace S"])
      fix x y
      assume xy:"x \<in> topspace S" "y \<in> topspace S" "x \<noteq> y"
      then obtain Ox Oy where Oxy: "x \<in> Ox" "y \<in> Oy" "openin S Ox" "openin S Oy" "disjnt Ox Oy"
        using Hausdorff by(auto simp: Hausdorff_space_def) metis
      show "\<exists>Ox Oy. (\<forall>x. openin (Si x) Ox) \<and> (\<forall>x. openin (Si x) Oy) \<and> x \<in> Ox \<and> y \<in> Oy \<and> disjnt Ox Oy"
        by(rule exI[where x=Ox],insert Si(2) Oxy, auto intro!: exI[where x=Oy])
    qed (use Si in auto)
    have Suntop:"topspace S = topspace Sun"
      using Si(3) by(auto simp: Sun_def dest: openin_subset)
    have Sunsets: "sets (borel_of S) = sets (borel_of Sun)" (is "?lhs = ?rhs")
    proof -
      have "?lhs = sigma_sets (topspace S) (\<Union>n. {u. openin (Si n) u})"
      proof
        show "sets (borel_of S) \<subseteq> sigma_sets (topspace S) (\<Union>n. {u. openin (Si n) u})"
          using Si(2) by(auto simp: sets_borel_of intro!: sigma_sets_mono')
      next
        show "sigma_sets (topspace S) (\<Union>n. {u. openin (Si n) u}) \<subseteq> sets (borel_of S)"
          by(simp add: sigma_sets_le_sets_iff[of "borel_of S" "\<Union>n. {u. openin (Si n) u}",simplified space_borel_of]) (use Si(4) sets_borel_of in fastforce)
      qed
      also have "... = ?rhs"
        using borel_of_second_countable'[OF polish_topology.S_second_countable[OF Sun1],of "\<Union>n. {u. openin (Si n) u}"]
        by (simp add: Sun_def Suntop subbase_of_def subset_Pow_Union)
      finally show ?thesis .
    qed
    have Sun_open: "\<And>u i. openin (Si i) u \<Longrightarrow> openin Sun u"
      by(auto simp: Sun_def openin_topology_generated_by_iff intro!: generate_topology_on.Basis)
    have Sun_opena: "openin Sun (\<Union>i. a i)"
      using Sun_open[OF Si(5),simplified Sun_def] by(auto simp: Sun_def openin_topology_generated_by_iff intro!: generate_topology_on.UN)
    hence "closedin Sun (topspace Sun - (\<Union>i. a i))"
      by auto
    from polish_topology.closedin_clopen_topology[OF Sun1 this]
    show ?case
      using Suntop Sunsets Sun_open[OF Si(2)] Sun_opena
      by (metis closedin_def openin_closedin_eq)
  qed
qed

end