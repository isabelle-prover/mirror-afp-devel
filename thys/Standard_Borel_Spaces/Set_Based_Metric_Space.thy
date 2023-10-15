(*  Title:   Set_Based_Metric_Space.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

section  \<open>Set-Based Metric Spaces\<close>
theory Set_Based_Metric_Space
  imports Lemmas_StandardBorel
begin

subsection \<open>Set-Based Metric Spaces \<close>
locale metric_set =
  fixes S :: "'a set"
    and dist :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes dist_geq0: "\<And>x y. dist x y \<ge> 0"
      and dist_notin: "\<And>x y. x \<notin> S \<Longrightarrow> dist x y = 0"
      and dist_0: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> (x = y) = (dist x y = 0)"
      and dist_sym: "\<And>x y. dist x y = dist y x"
      and dist_tr: "\<And>x y z. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> z \<in> S \<Longrightarrow> dist x z \<le> dist x y + dist y z"

lemma metric_class_metric_set[simp]: "metric_set UNIV dist"
  by standard (auto simp: dist_commute dist_triangle)

context metric_set
begin

abbreviation "dist_typeclass \<equiv> Real_Vector_Spaces.dist"

lemma dist_notin':
  assumes "y \<notin> S"
  shows "dist x y = 0"
  by(auto simp: dist_sym[of x y] intro!: dist_notin assms)

lemma dist_ge0:
  assumes "x \<in> S" "y \<in> S"
  shows "x \<noteq> y \<longleftrightarrow> dist x y > 0"
  using dist_0[OF assms] dist_geq0[of x y] by auto

lemma dist_0'[simp]: "dist x x = 0"
  by(cases "x \<in> S") (use dist_notin dist_0 in auto)

lemma dist_tr_abs:
  assumes "x \<in> S" "y \<in> S" "z \<in> S"
  shows "\<bar>dist x y - dist y z\<bar> \<le> dist x z"
  using dist_tr[OF assms(1,3,2),simplified dist_sym[of z]] dist_tr[OF assms(2,1,3),simplified dist_sym[of _ x]]
  by auto

text \<open> Ball \<close>
definition open_ball :: "'a \<Rightarrow> real \<Rightarrow> 'a set" where
"open_ball a r \<equiv> if a \<in> S then {x \<in> S. dist a x < r} else {}"

lemma open_ball_subset_ofS: "open_ball a \<epsilon> \<subseteq> S"
  by(auto simp: open_ball_def)

lemma open_ballD:
  assumes "x \<in> open_ball a \<epsilon>"
  shows "dist a x < \<epsilon>"
proof -
  have [simp]:"a \<in> S"
    apply(rule ccontr) using assms by(simp add: open_ball_def)
  show ?thesis
    using assms by(simp add: open_ball_def)
qed

lemma open_ballD':
  assumes "x \<in> open_ball a \<epsilon>"
  shows "x \<in> S" "a \<in> S" "\<epsilon> > 0"
proof -
  have 1:"a \<in> S"
    apply(rule ccontr)
    using assms by(auto simp: open_ball_def)
  have 2:"x \<in> S"
    apply(rule ccontr)
    using assms 1 by(auto simp: open_ball_def)
  have 3: "dist a x < \<epsilon>"
    using assms by(simp add: 1 2 open_ball_def)
  show "\<epsilon> > 0"
    apply(rule ccontr)
    using 3 dist_geq0[of a x] by auto
  show "x \<in> S" "a \<in> S"
    by fact+
qed

lemma open_ball_inverse:
 "x \<in> open_ball y \<epsilon> \<longleftrightarrow> y \<in> open_ball x \<epsilon>"
proof -
  have 0:"\<And>x y. x \<in> open_ball y \<epsilon> \<Longrightarrow> y \<in> open_ball x \<epsilon>"
  proof -
    fix x y
    assume 1:"x \<in> open_ball y \<epsilon>"
    show "y \<in> open_ball x \<epsilon>"
      using open_ballD'[OF 1] dist_sym[of y x] 1 by(simp add: open_ball_def)
  qed
  show ?thesis
    using 0[of x y] 0[of y x] by auto
qed

lemma open_ball_ina[simp]:
  assumes "a \<in> S" and "\<epsilon> > 0"
  shows "a \<in> open_ball a \<epsilon>"
  using assms dist_0[of a a] by(simp add: open_ball_def)

lemma open_ball_nin_le:
  assumes "a \<in> S" "\<epsilon> > 0" "b \<in> S" "b \<notin> open_ball a \<epsilon>"
  shows "\<epsilon> \<le> dist a b"
  using assms by(simp add: open_ball_def)

lemma open_ball_le:
  assumes "r \<le> l"
  shows "open_ball a r \<subseteq> open_ball a l"
  using assms by(auto simp: open_ball_def)

lemma open_ball_le_0:
  assumes "\<epsilon> \<le> 0"
  shows "open_ball a \<epsilon> = {}"
  using assms dist_geq0[of a]
  by(auto simp: open_ball_def) (meson linorder_not_less order_trans)

lemma open_ball_nin:
  assumes "a \<notin> S"
  shows "open_ball a \<epsilon> = {}"
  by(simp add: open_ball_def assms)

definition closed_ball :: "'a \<Rightarrow> real \<Rightarrow> 'a set" where
"closed_ball a r \<equiv> if a \<in> S then {x \<in> S. dist a x \<le> r} else {}"

lemma closed_ball_subset_ofS:
 "closed_ball a \<epsilon> \<subseteq> S"
  by(auto simp: closed_ball_def)

lemma closed_ballD:
  assumes "x \<in> closed_ball a \<epsilon>"
  shows "dist a x \<le> \<epsilon>"
proof -
  have [simp]:"a \<in> S"
    apply(rule ccontr) using assms by(simp add: closed_ball_def)
  show ?thesis
    using assms by(simp add: closed_ball_def)
qed

lemma closed_ballD':
  assumes "x \<in> closed_ball a \<epsilon>"
  shows "x \<in> S" "a \<in> S" "\<epsilon> \<ge> 0"
proof -
  have 1:"a \<in> S"
    apply(rule ccontr)
    using assms by(auto simp: closed_ball_def)
  have 2:"x \<in> S"
    apply(rule ccontr)
    using assms 1 by(auto simp: closed_ball_def)
  have 3: "dist a x \<le> \<epsilon>"
    using assms by(simp add: 1 2 closed_ball_def)
  show "\<epsilon> \<ge> 0"
    apply(rule ccontr)
    using 3 dist_geq0[of a x] by auto
  show "x \<in> S" "a \<in> S"
    by fact+
qed

lemma closed_ball_ina[simp]:
  assumes "a \<in> S" and "\<epsilon> \<ge> 0"
  shows "a \<in> closed_ball a \<epsilon>"
  using assms dist_0[of a a] by(simp add: closed_ball_def)

lemma closed_ball_le:
  assumes "r \<le> l"
  shows "closed_ball a r \<subseteq> closed_ball a l"
  using closed_ballD'[of _ a r] closed_ballD[of _ a r] assms
  by(fastforce simp: closed_ball_def[of _ l])

lemma closed_ball_le_0:
  assumes "\<epsilon> < 0"
  shows "closed_ball a \<epsilon> = {}"
  using assms dist_geq0[of a]
  by(auto simp: closed_ball_def) (meson linorder_not_less order_trans)

lemma closed_ball_0:
  assumes "a \<in> S"
  shows "closed_ball a 0 = {a}"
  using assms dist_0[OF assms assms] dist_0[OF assms] dist_geq0[of a] order_antisym_conv
  by(auto simp: closed_ball_def)

lemma closed_ball_nin:
  assumes "a \<notin> S"
  shows "closed_ball a \<epsilon> = {}"
  by(simp add: closed_ball_def assms)

lemma open_ball_closed_ball:
 "open_ball a \<epsilon> \<subseteq> closed_ball a \<epsilon>"
  using open_ballD'[of _ a \<epsilon>] open_ballD[of _ a \<epsilon>]
  by(fastforce simp: closed_ball_def)

lemma closed_ball_open_ball:
  assumes "e < f"
  shows "closed_ball a e \<subseteq> open_ball a f"
  using closed_ballD'[of _ a e] closed_ballD[of _ a e] assms
  by(fastforce simp: open_ball_def)

lemma closed_ball_open_ball_un1:
  assumes "e > 0"
  shows "open_ball a e \<union> {x\<in>S. dist a x = e} = closed_ball a e"
  using assms dist_notin by(auto simp: open_ball_def closed_ball_def)

lemma closed_ball_open_ball_un2:
  assumes "a \<in> S"
  shows "open_ball a e \<union> {x\<in>S. dist a x = e} = closed_ball a e"
  using assms by(auto simp: open_ball_def closed_ball_def)

definition mtopology :: "'a topology" where
"mtopology = topology (\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U))"

lemma mtopology_istopology:
 "istopology (\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U))"
  unfolding istopology_def
proof safe
  fix U1 U2 x
  assume h1: "U1 \<subseteq> S" "\<forall>y\<in>U1. \<exists>\<epsilon>>0. open_ball y \<epsilon> \<subseteq> U1"
     and h2: "U2 \<subseteq> S" "\<forall>y\<in>U2. \<exists>\<epsilon>>0. open_ball y \<epsilon> \<subseteq> U2"
     and hx: "x \<in> U1" "x \<in> U2"
  obtain \<epsilon>1 \<epsilon>2 where
   "\<epsilon>1 > 0" "\<epsilon>2 > 0""open_ball x \<epsilon>1 \<subseteq> U1" "open_ball x \<epsilon>2 \<subseteq> U2"
    using h1 h2 hx by blast
  thus "\<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U1 \<inter> U2"
    using open_ball_le[of "min \<epsilon>1 \<epsilon>2" \<epsilon>1 x] open_ball_le[of "min \<epsilon>1 \<epsilon>2" \<epsilon>2 x]
    by(auto intro!: exI[where x="min \<epsilon>1 \<epsilon>2"])
next
  fix \<K> U x
  assume h:"\<forall>K\<in>\<K>. K \<subseteq> S \<and> (\<forall>x\<in>K. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> K)"
           "U \<in> \<K>" "x \<in> U"
  then obtain \<epsilon> where 
   "\<epsilon> > 0" "open_ball x \<epsilon> \<subseteq> U"
    by blast
  thus "\<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> \<Union> \<K>"
    using h(2) by(auto intro!: exI[where x=\<epsilon>])
qed auto

lemma mtopology_openin_iff:
 "openin mtopology U \<longleftrightarrow> U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U)"
  by (simp add: mtopology_def mtopology_istopology)

lemma mtopology_topspace: "topspace mtopology = S"
  unfolding topspace_def mtopology_def topology_inverse'[OF mtopology_istopology]
proof -
  have "\<forall>x\<in>S. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> S"
    by(auto intro!: exI[where x=1] simp: open_ball_def)
  thus "\<Union> {U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U)} = S"
    by auto
qed

lemma openin_S[simp]: "openin mtopology S"
  by (metis openin_topspace mtopology_topspace)

lemma mtopology_open_ball_in':
  assumes "x \<in> open_ball a \<epsilon>"
  shows "\<exists>\<epsilon>'>0. open_ball x \<epsilon>' \<subseteq> open_ball a \<epsilon>"
proof -
  show "\<exists>\<epsilon>'>0. open_ball x \<epsilon>' \<subseteq> open_ball a \<epsilon>"
  proof(intro exI[where x="\<epsilon> - dist a x"] conjI)
    show "0 < \<epsilon> - dist a x"
      using open_ballD'[OF assms] open_ballD[OF assms] by auto
  next
    show "open_ball x (\<epsilon> - dist a x) \<subseteq> open_ball a \<epsilon>"
    proof
      fix y
      assume hy:"y \<in> open_ball x (\<epsilon> - dist a x)"
      show "y \<in> open_ball a \<epsilon>"        
        using open_ballD[OF hy] open_ballD[OF assms] open_ballD'(2)[OF assms] dist_tr[OF open_ballD'(2)[OF assms] open_ballD'(1)[OF assms] open_ballD'(1)[OF hy]]
        by(auto simp: open_ball_def assms(1) open_ballD'[OF hy])
    qed
  qed
qed

lemma mtopology_open_ball_in:
  assumes "a \<in> S" and "\<epsilon> > 0"
  shows "openin mtopology (open_ball a \<epsilon>)"
  using mtopology_open_ball_in' topology_inverse'[OF mtopology_istopology] open_ball_subset_ofS mtopology_def
  by auto

lemma openin_open_ball: "openin mtopology (open_ball a \<epsilon>)"
proof -
  consider "a \<in> S \<and> \<epsilon> > 0" | "a \<notin> S" | "\<epsilon> \<le> 0" by fastforce
  thus ?thesis
    by cases (simp_all add: mtopology_open_ball_in open_ball_le_0 open_ball_nin)
qed

lemma closedin_closed_ball: "closedin mtopology (closed_ball a \<epsilon>)"
  unfolding closedin_def mtopology_topspace mtopology_openin_iff
proof safe
  fix x
  assume h:"x \<in> S" "x \<notin> closed_ball a \<epsilon>"
  consider "a \<notin> S" | "\<epsilon> < 0" | "a \<in> S" "\<epsilon> \<ge> 0"  by fastforce
  thus "\<exists>\<epsilon>'>0. open_ball x \<epsilon>' \<subseteq> S - closed_ball a \<epsilon>"
  proof cases
    case 3
    then have "dist a x > \<epsilon>"
      using h by(auto simp: closed_ball_def)
    show ?thesis
    proof(intro exI[where x="dist a x - \<epsilon>"] conjI)
      show "open_ball x (dist a x - \<epsilon>) \<subseteq> S - closed_ball a \<epsilon>"
      proof safe
        fix z
        assume h':"z \<in> open_ball x (dist a x - \<epsilon>)" "z \<in> closed_ball a \<epsilon>"
        have "dist a x \<le> dist a z + dist z x"
          by(auto intro!: dist_tr 3 open_ballD'[OF h'(1)])
        also have "... \<le> \<epsilon> + dist z x"
          using closed_ballD[OF h'(2)] by simp
        also have "... < dist a x"
          using open_ballD[OF h'(1),simplified dist_sym[of x]] by auto
        finally show False ..
      qed(use open_ball_subset_ofS \<open>dist a x > \<epsilon>\<close> in auto)
    qed(use open_ball_subset_ofS \<open>dist a x > \<epsilon>\<close> in auto)
  qed(auto simp: closed_ball_nin closed_ball_le_0 open_ball_subset_ofS intro!: exI[where x=1])
qed(use closed_ball_subset_ofS in auto)

lemma mtopology_def2:
 "mtopology = topology_generated_by {open_ball a \<epsilon> | a \<epsilon>. a \<in> S \<and> \<epsilon> > 0}"
  (is "?lhs = ?rhs")
proof -
  have "\<And>U. openin ?lhs U = openin ?rhs U"
  proof
    fix U
    assume h:"openin mtopology U"
    then have "\<forall>x\<in> U. \<exists>\<epsilon> > 0. open_ball x \<epsilon> \<subseteq> U"
      using topology_inverse'[OF mtopology_istopology]
      by(simp add: mtopology_def)
    then obtain \<epsilon> where he:
      "\<And>x. x \<in> U \<Longrightarrow> \<epsilon> x > 0 \<and> open_ball x (\<epsilon> x) \<subseteq> U"
      using bchoice[of U "\<lambda>x \<epsilon>.  \<epsilon> > 0  \<and> open_ball x \<epsilon> \<subseteq> U"]
      by blast
    have "U = \<Union>{open_ball x (\<epsilon> x)|x. x\<in> U}"
    proof
      show "\<Union> {open_ball x (\<epsilon> x) |x. x \<in> U} \<subseteq> U"
        using he by auto
    next
      show "U \<subseteq> \<Union> {open_ball x (\<epsilon> x) |x. x \<in> U}"
      proof
        fix a
        assume ha:"a \<in> U"
        then have "a \<in> open_ball a (\<epsilon> a)"
          using he[of a] open_ball_ina[of a "\<epsilon> a"] openin_subset[OF h,simplified]
          by(auto simp: mtopology_topspace)
        thus "a \<in> \<Union> {open_ball x (\<epsilon> x) |x. x \<in> U}"
          using ha by auto
      qed
    qed
    also have "generate_topology_on {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>} ..."
      apply(rule generate_topology_on.UN)
      apply(rule generate_topology_on.Basis)
      using he openin_subset[OF h,simplified]
      by(fastforce simp: mtopology_topspace)
    finally show "openin (topology_generated_by {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}) U"
      by (simp add: openin_topology_generated_by_iff)
  next
    fix U
    assume "openin (topology_generated_by {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}) U"
    then have "generate_topology_on {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>} U"
      by (simp add: openin_topology_generated_by_iff)
    thus "openin mtopology U"
      apply induction
      using mtopology_open_ball_in
      by auto
  qed
  thus ?thesis
    by(simp add: topology_eq)
qed

abbreviation mtopology_subbasis :: "'a set set \<Rightarrow> bool" where
"mtopology_subbasis \<O> \<equiv> subbase_of mtopology  \<O>"

lemma mtopology_subbasis1:
 "mtopology_subbasis {open_ball a \<epsilon> | a \<epsilon>. a \<in> S \<and> \<epsilon> > 0}"
  by(simp add: mtopology_def2 subbase_of_def)

abbreviation mtopology_basis :: "'a set set \<Rightarrow> bool" where
"mtopology_basis \<O> \<equiv> base_of mtopology \<O>"

lemma mtopology_basis_ball:
 "mtopology_basis {open_ball a \<epsilon> | a \<epsilon>. a \<in> S \<and> \<epsilon> > 0}"
  unfolding base_of_def
proof -
  show "\<forall>U. openin mtopology U = (\<exists>\<U>. U = \<Union> \<U> \<and> \<U> \<subseteq> {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>})"
  proof safe
    fix U
    assume "openin mtopology U"
    then have "U \<subseteq> S" "\<And>x. x\<in>U \<Longrightarrow> \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U"
      by(auto simp: mtopology_openin_iff)
    then obtain \<epsilon> where he:
      "\<And>x. x \<in> U \<Longrightarrow> \<epsilon> x > 0" "\<And>x. x \<in> U \<Longrightarrow> open_ball x (\<epsilon> x) \<subseteq> U"
      by metis
    hence "(\<Union> { open_ball x (\<epsilon> x) | x. x \<in> U}) = U"
      using \<open>U \<subseteq> S\<close> open_ball_ina[of _ "\<epsilon> _"] by fastforce
    thus "\<exists>\<U>. U = \<Union> \<U> \<and> \<U> \<subseteq> {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}"
      using he(1) \<open>U \<subseteq> S\<close> by(fastforce intro!: exI[where x="{ open_ball x (\<epsilon> x) | x. x \<in> U}"])
  qed(use mtopology_open_ball_in in blast)
qed

abbreviation sequence :: "(nat \<Rightarrow> 'a) set" where
"sequence \<equiv> UNIV \<rightarrow> S"

lemma sequence_comp:
 "xn \<in> sequence \<Longrightarrow> (\<lambda>n. (xn (a n))) \<in> sequence"
 "xn \<in> sequence \<Longrightarrow> xn \<circ> an \<in> sequence"
  by auto

definition converge_to_inS :: "[nat \<Rightarrow> 'a, 'a] \<Rightarrow> bool" where
"converge_to_inS f s \<equiv> f \<in> sequence \<and> s \<in> S \<and> (\<lambda>n. dist (f n) s) \<longlonglongrightarrow> 0"

lemma converge_to_inS_const:
  assumes "x \<in> S"
  shows "converge_to_inS (\<lambda>n. x) x"
  using assms dist_0[of x x] by(simp add: converge_to_inS_def)

lemma converge_to_inS_subseq:
  assumes "strict_mono a" "converge_to_inS f s"
  shows "converge_to_inS (f \<circ> a) s"
proof -
  have "((\<lambda>n. dist (f n) s) \<circ> a) \<longlonglongrightarrow> 0"
    using assms by(auto intro!: LIMSEQ_subseq_LIMSEQ simp: converge_to_inS_def)
  thus ?thesis
    using assms by(auto simp: converge_to_inS_def comp_def)
qed

lemma converge_to_inS_ignore_initial:
  assumes "converge_to_inS xn x"
  shows "converge_to_inS (\<lambda>n. xn (n + k)) x"
  using LIMSEQ_ignore_initial_segment[of "\<lambda>n. dist (xn n) x" 0 k] assms
  by(auto simp: converge_to_inS_def)

lemma converge_to_inS_offset:
  assumes "converge_to_inS (\<lambda>n. xn (n + k)) x" "xn \<in> sequence"
  shows "converge_to_inS xn x"
  using LIMSEQ_offset[of "\<lambda>n. dist (xn n) x" k] assms
  by(auto simp: converge_to_inS_def)

lemma converge_to_inS_def2:
 "converge_to_inS f s \<longleftrightarrow> (f \<in> sequence \<and> s \<in> S \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (f n) s < \<epsilon>))"
proof
  assume h:"converge_to_inS f s "
  show "f \<in> sequence \<and> s \<in> S \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (f n) s < \<epsilon>)"
  proof safe
    fix \<epsilon> :: real
    assume he:"0 < \<epsilon>"
    have hs:"\<And>S. open S \<Longrightarrow> 0 \<in> S \<Longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n) s \<in> S)"
      using h lim_explicit[of "\<lambda>n. dist (f n) s" 0]
      by(simp add: converge_to_inS_def)
    then obtain N where
     "\<forall>n\<ge>N. dist (f n) s \<in> {-1<..<\<epsilon>}"
      using hs[of "{-1<..<\<epsilon>}"] he by fastforce
    thus "\<exists>N. \<forall>n\<ge>N. dist (f n) s < \<epsilon>"
      by(auto intro!: exI[where x=N])
  qed(use h[simplified converge_to_inS_def] in auto)
next
  assume h:"f \<in> sequence \<and> s \<in> S \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (f n) s < \<epsilon>)"
  have "\<forall>S. open S \<longrightarrow> 0 \<in> S \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n) s \<in> S)"
  proof safe
    fix S :: "real set"
    assume hs:"open S" "0 \<in> S"
    then obtain \<epsilon> where he:
      "\<epsilon> > 0" "ball 0 \<epsilon> \<subseteq> S"
      using open_contains_ball[of S] by fastforce
    then obtain N where
     "\<forall>n\<ge>N. dist (f n) s < \<epsilon>"
      using h by auto
    thus "\<exists>N. \<forall>n\<ge>N. dist (f n) s \<in> S"
      using he dist_geq0 by(auto intro!: exI[where x=N])
  qed
  thus "converge_to_inS f s "
    using lim_explicit[of "\<lambda>n. dist (f n) s" 0] h
    by(simp add: converge_to_inS_def)
qed

lemma converge_to_inS_def2':
 "converge_to_inS f s \<longleftrightarrow> (f \<in> sequence \<and> s \<in> S \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. (f n) \<in> open_ball s \<epsilon>))"
  unfolding converge_to_inS_def2 open_ball_def dist_sym[of s]
  by fastforce

lemma converge_to_inS_unique:
  assumes "converge_to_inS f x" "converge_to_inS f y"
  shows "x = y"
proof -
  have inS:"\<And>n. f n \<in> S" "x \<in> S" "y \<in> S"
    using assms by(auto simp: converge_to_inS_def)
  have "\<bar>dist x y\<bar> < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
  proof -
    have "0 < \<epsilon> / 2" using that by simp
    then obtain N1 N2 where hn:
     "\<And>n. n \<ge> N1 \<Longrightarrow> dist (f n) x < \<epsilon> / 2" "\<And>n. n \<ge> N2 \<Longrightarrow> dist (f n) y < \<epsilon> / 2"
      using assms converge_to_inS_def2 by blast
    have "dist x y \<le> dist (f (max N1 N2)) x + dist (f (max N1 N2)) y"
      unfolding dist_sym[of "f (max N1 N2)" x] by(rule dist_tr[OF inS(2) inS(1)[of "max N1 N2"] inS(3)])
    also have "... < \<epsilon> / 2 + \<epsilon> / 2"
      by(rule add_strict_mono) (use hn[of "max N1 N2"] in auto)
    finally show ?thesis
      using dist_geq0[of x y] by simp
  qed
  hence "dist x y = 0"
    using zero_less_abs_iff by blast
  thus ?thesis
    using dist_0[OF inS(2,3)] by simp
qed

lemma mtopology_closedin_iff: "closedin mtopology M \<longleftrightarrow> M \<subseteq> S \<and> (\<forall>f\<in>(UNIV \<rightarrow> M). \<forall>s. converge_to_inS f s \<longrightarrow> s \<in> M)"
proof
  assume "closedin mtopology M"
  then have h:"\<forall>x\<in>S - M. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> S - M"
    by (simp add: closedin_def mtopology_openin_iff mtopology_topspace)
  show "M \<subseteq> S \<and> (\<forall>f\<in>UNIV \<rightarrow> M. \<forall>s. converge_to_inS f s \<longrightarrow> s \<in> M)"
  proof safe
    fix f :: "nat \<Rightarrow> 'a" and s
    assume hf:"f \<in> UNIV \<rightarrow> M" "converge_to_inS f s"
    show "s \<in> M"
    proof(rule ccontr)
      assume "s \<notin> M"
      then have "s \<in> S - M"
        using hf(2) by(auto simp: converge_to_inS_def)
      then obtain \<epsilon> where "\<epsilon> > 0" "open_ball s \<epsilon> \<subseteq> S - M"
        using h by auto
      then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> open_ball s \<epsilon>"
        using hf(2) by(auto simp: converge_to_inS_def2') metis
      from \<open>open_ball s \<epsilon> \<subseteq> S - M\<close> this[of N] hf(1)
      show False by auto
    qed
  qed(rule subsetD[OF closedin_subset[OF \<open>closedin mtopology M\<close>,simplified mtopology_topspace]])
next
  assume h:"M \<subseteq> S \<and> (\<forall>f\<in>UNIV \<rightarrow> M. \<forall>s. converge_to_inS f s \<longrightarrow> s \<in> M)"
  show "closedin mtopology M"
    unfolding closedin_def mtopology_openin_iff mtopology_topspace
  proof safe
    fix x
    assume "x \<in> S" "x \<notin> M"
    show "\<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> S - M"
    proof(rule ccontr)
      assume "\<not> (\<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> S - M)"
      then have "\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> M \<noteq> {}"
        by (metis Diff_mono Diff_triv open_ball_subset_ofS subset_refl)
      hence "\<forall>n. \<exists>a. a \<in> open_ball x (1 / real (Suc n)) \<inter> M"
        by (meson of_nat_0_less_iff subsetI subset_empty zero_less_Suc zero_less_divide_1_iff)
      then obtain f where hf:"\<And>n. f n \<in> open_ball x (1 / (Suc n)) \<inter> M" by metis
      hence "f \<in> UNIV \<rightarrow> M" by auto
      moreover have "converge_to_inS f x"
        unfolding converge_to_inS_def2'
      proof safe
        show "f x \<in> S" for x
          using h hf by auto
      next
        fix \<epsilon>
        assume "(0::real) < \<epsilon>"
        then obtain N where "1 / real (Suc N) < \<epsilon>"
          using nat_approx_posE by blast
        show "\<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>"
        proof(rule exI[where x=N])
          show "\<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>"
          proof safe
            fix n
            assume "N \<le> n"
            then have "1 / real (Suc n) \<le> 1 / real (Suc N)"
              by (simp add: frac_le)
            also have "... \<le> \<epsilon>"
              using \<open>1 / real (Suc N) < \<epsilon>\<close> by simp
            finally show "f n \<in> open_ball x \<epsilon>"
              using open_ball_le[of "1 / real (Suc n)" \<epsilon> x] hf by auto
          qed
        qed
      qed fact
      ultimately show False
        using h \<open>x \<notin> M\<close> by blast
    qed
  qed(use h in auto)
qed

lemma mtopology_closedin_iff2: "closedin mtopology M \<longleftrightarrow> M \<subseteq> S \<and> (\<forall>x. x \<in> M \<longleftrightarrow> (\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> M \<noteq> {}))"
proof
  assume h:"closedin mtopology M"
  have 1: "M \<subseteq> S"
    using h by(auto simp add: mtopology_closedin_iff)
  show "M \<subseteq> S \<and> (\<forall>x. (x \<in> M) = (\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> M \<noteq> {}))"
  proof safe
    fix \<epsilon> x
    assume "x \<in> M" "(0 :: real) < \<epsilon>" "open_ball x \<epsilon> \<inter> M = {}"
    thus False
      using open_ball_ina[of x \<epsilon>] 1 by blast
  next
    fix x
    assume "\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> M \<noteq> {}"
    hence "\<exists>f. f \<in> open_ball x (1 / real (Suc n)) \<inter> M" for n
      by (meson all_not_in_conv divide_pos_pos of_nat_0_less_iff zero_less_Suc zero_less_one)
    then obtain f where hf:"\<And>n. f n \<in> open_ball x (1 / real (Suc n)) \<inter> M"
      by metis
    hence "x \<in> S" "f \<in> UNIV \<rightarrow> M"
      using open_ballD'(2)[of "f 0" x] by auto
    have "converge_to_inS f x"
      unfolding converge_to_inS_def2'
    proof safe
      show "\<And>x. f x \<in> S"
        using 1 \<open>f \<in> UNIV \<rightarrow> M\<close> by auto
    next
      fix \<epsilon>
      assume "(0 :: real) < \<epsilon>"
      then obtain N where hN: "1 / real (Suc N) < \<epsilon>"
        using nat_approx_posE by blast
      show "\<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>"
      proof(rule exI[where x="N"])
        show "\<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>"
        proof safe
          fix n
          assume "N \<le> n"
          then have "1 / real (Suc n) \<le> 1 / real (Suc N)"
            using inverse_of_nat_le by blast
          thus "f n \<in> open_ball x \<epsilon> "
            using hf[of n] open_ball_le[of "1 / real (Suc n)" "\<epsilon>" x] hN
            by auto
        qed
      qed
    qed fact
    with \<open>f \<in> UNIV \<rightarrow> M\<close> show "x \<in> M"
      using h[simplified mtopology_closedin_iff] by simp
  qed(use 1 in auto)
next
  assume"M \<subseteq> S \<and> (\<forall>x. (x \<in> M) \<longleftrightarrow> (\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> M \<noteq> {}))"
  hence h:"M \<subseteq> S" "\<And>x. (x \<in> M) \<longleftrightarrow> (\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> M \<noteq> {})"
    by simp_all
  show "closedin mtopology M"
    unfolding mtopology_closedin_iff
  proof safe
    fix f s
    assume h':"f \<in> UNIV \<rightarrow> M" "converge_to_inS f s"
    hence "s \<in> S" by(simp add: converge_to_inS_def)
    have "open_ball s \<epsilon> \<inter> M \<noteq> {}" if "\<epsilon> > 0" for \<epsilon>
    proof -
      obtain N where hN:"\<And>n. n \<ge> N \<Longrightarrow> dist (f n) s < \<epsilon>"
        using h'(2) \<open>\<epsilon> > 0\<close> by(auto simp: converge_to_inS_def2) metis
      have "f N \<in> open_ball s \<epsilon> \<inter> M"
        using \<open>f \<in> UNIV \<rightarrow> M\<close> \<open>s \<in> S\<close> hN[of N] that open_ball_def[of s \<epsilon>] h(1) dist_sym[of s]
        by auto
      thus "open_ball s \<epsilon> \<inter> M \<noteq> {}" by auto
    qed
    with h(2)[of s] show "s \<in> M" by simp
  qed(use h(1) in auto)
qed

lemma mtopology_openin_iff2:
 "openin mtopology A \<longleftrightarrow> A \<subseteq> S \<and> (\<forall>f x. converge_to_inS f x \<and> x \<in> A \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> A))"
proof
  show "openin mtopology A \<Longrightarrow> A \<subseteq> S \<and> (\<forall>f x. converge_to_inS f x \<and> x \<in> A \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> A))"
    unfolding mtopology_openin_iff
  proof safe
    fix f x
    assume "\<forall>x\<in>A. \<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> A" "converge_to_inS f x" "x \<in> A"
    then obtain \<epsilon> where "\<epsilon> > 0" "open_ball x \<epsilon> \<subseteq> A"
      by auto
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> dist (f n) x < \<epsilon>"
      using \<open>converge_to_inS f x\<close> by(fastforce simp: converge_to_inS_def2)
    hence "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> open_ball x \<epsilon>"
      using \<open>converge_to_inS f x\<close> by(auto simp: dist_sym[of _ x] open_ball_def converge_to_inS_def)
    with \<open>open_ball x \<epsilon> \<subseteq> A\<close> show "\<exists>N. \<forall>n\<ge>N. f n \<in> A"
      by(auto intro!: exI[where x=N])
  qed
next
  assume "A \<subseteq> S \<and> (\<forall>f x. converge_to_inS f x \<and> x \<in> A \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<in> A))"
  hence h:"A \<subseteq> S" "\<And>f x. converge_to_inS f x \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. f n \<in> A"
    by auto
  have "closedin mtopology (S - A)"
    unfolding mtopology_closedin_iff
  proof safe
    fix f s
    assume hf:"f \<in> UNIV \<rightarrow> S - A"
              "converge_to_inS f s"
    have False if "s \<in> A"
    proof -
      from h(2)[OF hf(2) that]
      obtain N where "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> A" by auto
      from hf (1) this[of N] show False by auto
    qed
    thus "s \<in> S" "s \<in> A \<Longrightarrow> False"
      using hf(2) by (auto simp: converge_to_inS_def)
  qed
  thus "openin mtopology A"
    using h(1) mtopology_topspace by(simp add: openin_closedin_eq)
qed

lemma closure_of_mtopology: "mtopology closure_of A = {a. \<forall>\<epsilon>>0. open_ball a \<epsilon> \<inter> A \<noteq> {}}"
proof safe
  fix x \<epsilon>
  assume "x \<in> mtopology closure_of A" "(0 :: real) < \<epsilon>" "open_ball x \<epsilon> \<inter> A = {}"
  then show False
    using mtopology_closedin_iff2[of "mtopology closure_of A",simplified]
    by (simp add: mtopology_open_ball_in' mtopology_openin_iff open_ball_subset_ofS openin_Int_closure_of_eq_empty)
next
  fix x
  assume "\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> A \<noteq> {}"
  then have "\<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> mtopology closure_of A \<noteq> {}"
    by (simp add: mtopology_open_ball_in' mtopology_openin_iff open_ball_subset_ofS openin_Int_closure_of_eq_empty)
  thus "x \<in> mtopology closure_of A"
    using mtopology_closedin_iff2[of "mtopology closure_of A",simplified]
    by auto
qed

lemma closure_of_mtopology':
 "mtopology closure_of A = {a. \<exists>an\<in>UNIV \<rightarrow> A. converge_to_inS an a}"
proof safe
  fix a
  assume "a \<in> mtopology closure_of A"
  then have "\<forall>\<epsilon>>0. open_ball a \<epsilon> \<inter> A \<noteq> {}"
    by(simp add: closure_of_mtopology)
  hence "\<And>n. \<exists>an. an \<in> open_ball a (1/real (Suc n)) \<inter> A"
    by (meson all_not_in_conv divide_pos_pos of_nat_0_less_iff zero_less_Suc zero_less_one)
  then obtain an where han:"\<And>n. an n \<in> open_ball a (1/real (Suc n)) \<inter> A" by metis
  hence "an \<in> UNIV \<rightarrow> A" by auto
  show "\<exists>an\<in>UNIV \<rightarrow> A. converge_to_inS an a"
  proof(safe intro!: bexI[where x=an] \<open>an \<in> UNIV \<rightarrow> A\<close>)
    show "converge_to_inS an a"
      unfolding converge_to_inS_def2'
    proof safe
      show "an n \<in> S" "a \<in> S" for n
        using open_ballD'(2)[of "an 0" a] open_ballD'(1)[of "an n"] han by auto
    next
      fix \<epsilon>
      assume "(0 :: real) < \<epsilon>"
      then obtain N where "1 / real (Suc N) \<le> \<epsilon>"
        by (meson less_eq_real_def nat_approx_posE)
      show "\<exists>N. \<forall>n\<ge>N. an n \<in> open_ball a \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n
        assume "N \<le> n"
        then have "1 / real (Suc n) \<le> 1 / real (Suc N)"
          by (simp add: frac_le)
        from open_ball_le[OF order_trans[OF this \<open>1 / real (Suc N) \<le> \<epsilon>\<close>]]
        show "an n \<in> open_ball a \<epsilon>"
          using han by auto
      qed
    qed
  qed
next
  fix a an
  assume h:"an \<in> UNIV \<rightarrow> A" "converge_to_inS an a"
  have "\<forall>\<epsilon>>0. open_ball a \<epsilon> \<inter> A \<noteq> {}"
  proof safe
    fix \<epsilon>
    assume "(0 :: real) < \<epsilon>" "open_ball a \<epsilon> \<inter> A = {}"
    then obtain N where "an N \<in> open_ball a \<epsilon>"
      using h(2) converge_to_inS_def2' by blast
    with \<open>open_ball a \<epsilon> \<inter> A = {}\<close> h(1) show False by auto
  qed
  thus "a \<in> mtopology closure_of A"
    by(simp add: closure_of_mtopology)
qed

lemma closure_of_mtopology_an:
  assumes "a \<in> mtopology closure_of A"
  obtains an where "an\<in>UNIV \<rightarrow> A" "converge_to_inS an a"
  using assms by(auto simp: closure_of_mtopology')

lemma closure_of_open_ball: "mtopology closure_of open_ball a \<epsilon> \<subseteq> closed_ball a \<epsilon>"
  by(rule closure_of_minimal_eq[THEN iffD2]) (auto simp: open_ball_subset_ofS mtopology_topspace closedin_closed_ball open_ball_closed_ball)

lemma interior_of_closed_ball: "open_ball a e \<subseteq> mtopology interior_of closed_ball a e"
  by(auto simp: interior_of_maximal_eq openin_open_ball open_ball_closed_ball)

lemma derived_set_of_mtopology:
 "mtopology derived_set_of A = {a. \<exists>an\<in>UNIV \<rightarrow> A. (\<forall>n. an n \<noteq> a) \<and> converge_to_inS an a}"
proof safe
  fix a
  assume "a \<in> mtopology derived_set_of A"
  then have h:"a \<in> S" "\<And>v. a \<in> v \<Longrightarrow> openin mtopology v \<Longrightarrow> \<exists>y. y \<noteq> a \<and> y \<in> v \<and> y \<in> A"
    by(auto simp: in_derived_set_of mtopology_topspace)
  hence "a \<in> open_ball a (1 / real (Suc n))" for n
    by(auto intro!: open_ball_ina)
  from h(2)[OF this openin_open_ball[of a]]
  obtain an where an:"\<And>n. an n \<noteq> a" "\<And>n. an n \<in> open_ball a (1 / real (Suc n))" "\<And>n. an n \<in> A"
    by metis
  show "\<exists>an\<in>UNIV \<rightarrow> A. (\<forall>n. an n \<noteq> a) \<and> converge_to_inS an a"
  proof(safe intro!: bexI[where x=an] an(1))
    show "converge_to_inS an a"
      unfolding converge_to_inS_def2'
    proof safe
      show "\<And>x. an x \<in> S"
        using an(2) open_ball_subset_ofS by auto
    next
      fix \<epsilon>
      assume "(0 :: real) < \<epsilon>"
      then obtain N where hN:"1 / real (Suc N) < \<epsilon>"
        using nat_approx_posE by blast
      show "\<exists>N. \<forall>n\<ge>N. an n \<in> open_ball a \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n
        assume "N \<le> n"
        then have "1 / real (Suc n) \<le> 1 / real (Suc N)"
          by (simp add: frac_le)
        from order.strict_trans1[OF this hN] open_ball_le[of _ \<epsilon> a] an(2)[of n]
        show "an n \<in> open_ball a \<epsilon>" by(auto simp: less_le)
      qed
    qed(use h in auto)
  qed(use an in auto)
next
  fix a an
  assume h:"an \<in> UNIV \<rightarrow> A" "\<forall>n. an n \<noteq> a" "converge_to_inS an a"
  have "\<exists>y. y \<noteq> a \<and> y \<in> v \<and> y \<in> A" if "a \<in> v" "openin mtopology v" for v
  proof -
    obtain \<epsilon> where he:"\<epsilon> > 0" "a \<in> open_ball a \<epsilon>" "open_ball a \<epsilon> \<subseteq> v"
      by (meson \<open>a \<in> v\<close> \<open>openin mtopology v\<close> converge_to_inS_def2 h(3) mtopology_openin_iff open_ball_ina)
    then obtain N where hn:"\<And>n. n \<ge> N \<Longrightarrow> an n \<in> open_ball a \<epsilon>"
      using h(3) by(fastforce simp: converge_to_inS_def2')
    show " \<exists>y. y \<noteq> a \<and> y \<in> v \<and> y \<in> A"
      using h(1,2) he hn by(auto intro!: exI[where x="an N"])
  qed
  thus "a \<in> mtopology derived_set_of A"
    using h(3) by(auto simp: in_derived_set_of converge_to_inS_def mtopology_topspace)
qed

lemma isolated_points_of_mtopology:
 "mtopology isolated_points_of A = {a\<in>S\<inter>A. \<forall>an\<in>UNIV \<rightarrow> A. converge_to_inS an a \<longrightarrow> (\<exists>no. \<forall>n\<ge>no. an n = a)}"
proof safe
  fix a an
  assume h:"a \<in> mtopology isolated_points_of A" "converge_to_inS an a" "an \<in> UNIV \<rightarrow> A"
  then have ha:"a \<in> topspace mtopology" "a \<in> A" "\<exists>U. a \<in> U \<and> openin mtopology U \<and> U \<inter> (A - {a}) = {}"
    by(simp_all add: in_isolated_points_of)
  then obtain U where u:"a \<in> U" "openin mtopology U" "U \<inter> (A - {a}) = {}"
    by auto
  then obtain \<epsilon> where e: "\<epsilon> > 0" "open_ball a \<epsilon> \<subseteq> U"
    by(auto simp: mtopology_openin_iff)
  then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> an n \<in> open_ball a \<epsilon>"
    using h(2) by(fastforce simp: converge_to_inS_def2')
  thus "\<exists>no. \<forall>n\<ge>no. an n = a"
    using h(3) e(2) u(3) by(auto intro!: exI[where x=N])
qed (auto simp: derived_set_of_mtopology isolated_points_of_def mtopology_topspace)

lemma perfect_set_open_ball_infinite:
  assumes "perfect_set mtopology A"
  shows "closedin mtopology A \<and> (\<forall>a\<in>A. \<forall>\<epsilon>>0. infinite (open_ball a \<epsilon>))"
proof safe
  fix a \<epsilon>
  assume h: "a \<in> A" "0 < \<epsilon>" "finite (open_ball a \<epsilon>)"
  then have "a \<in> S"
    using open_ball_ina[OF _ \<open>0 < \<epsilon>\<close>,of a] perfect_setD(2)[OF assms]
    by(auto simp: mtopology_topspace)
  have "\<exists>e > 0. open_ball a e = {a}"
  proof -
    consider "open_ball a \<epsilon> = {a}" | "{a} \<subset> open_ball a \<epsilon>"
      using open_ball_ina[OF \<open>a \<in> S\<close> h(2)] by blast
    thus ?thesis
    proof cases
      case 1
      with h(2) show ?thesis by auto
    next
      case 2
      then have nen:"{dist a b |b. b \<in> open_ball a \<epsilon> \<and> a \<noteq> b} \<noteq> {}"
        by auto
      have fin: "finite {dist a b |b. b \<in> open_ball a \<epsilon> \<and> a \<noteq> b}"
        using h(3) by auto
      define e where "e \<equiv> Min {dist a b |b. b \<in> open_ball a \<epsilon> \<and> a \<noteq> b}"
      have "e > 0"
        using dist_0[OF \<open>a \<in> S\<close> open_ballD'(1)[of _ a \<epsilon>]] dist_geq0[of a]
        by(auto simp: e_def Min_gr_iff[OF fin nen] order_neq_le_trans)
      have bd:"\<And>b. b \<in> open_ball a \<epsilon> \<Longrightarrow> a \<noteq> b \<Longrightarrow> e \<le> dist a b"
        by(auto simp: e_def Min_le_iff[OF fin nen])
      have "e \<le> \<epsilon>"
        using nen open_ballD[of _ a \<epsilon>]
        by(fastforce simp add: e_def Min_le_iff[OF fin nen])
      show ?thesis
      proof(safe intro!: exI[where x=e])
        fix x
        assume x:"x \<in> open_ball a e"
        then show "x = a"
          using open_ball_le[OF \<open>e \<le> \<epsilon>\<close>,of a] open_ballD[OF x] bd[of x]
          by auto
      qed (simp_all add: open_ball_ina[OF \<open>a \<in> S\<close> \<open>e > 0\<close>] \<open>0 < e\<close>)
    qed
  qed
  then obtain e where e:"e > 0" "open_ball a e = {a}" by auto
  show False
    using perfect_setD(3)[OF assms h(1) open_ball_ina[OF \<open>a \<in> S\<close> \<open>e > 0\<close>]]
    by(auto simp: openin_open_ball) (use e(2) in auto)
qed(use perfect_setD[OF assms] in simp)

lemma nbh_subset:
  assumes A: "A \<subseteq> S" and e: "e > 0"
  shows "A \<subseteq> (\<Union>a\<in>A. open_ball a e)"
  using A open_ball_ina[OF _ e] by auto

lemma nbh_decseq:
  assumes "decseq an"
  shows "decseq (\<lambda>n. \<Union>a\<in>A. open_ball a (an n))"
proof(safe intro!: decseq_SucI)
  fix n a b
  assume "a \<in> A" "b \<in> open_ball a (an (Suc n))"
  with open_ball_le[OF decseq_SucD[OF assms]] show "b \<in> (\<Union>c\<in>A. open_ball c (an n))"
    by(auto intro!: bexI[where x=a] simp: frac_le)
qed

lemma nbh_Int:
  assumes A: "A \<noteq> {}" "A \<subseteq> S"
      and an:"\<And>n. an n > 0" "decseq an" "an \<longlonglongrightarrow> 0"
  shows "(\<Inter>n. \<Union>a\<in>A. open_ball a (an n)) = mtopology closure_of A"
proof safe
  fix x
  assume "x \<in> (\<Inter>n. \<Union>a\<in>A. open_ball a (an n))"
  then have h:"\<forall>n. \<exists>a\<in>A. x \<in> open_ball a (an n)"
    by auto
  hence x:"x \<in> S"
    using open_ball_subset_ofS by auto
  show "x \<in> mtopology closure_of A"
    unfolding closure_of_mtopology
  proof safe
    fix e :: real
    assume h':"e > 0" "open_ball x e \<inter> A = {}"
    then obtain n where n:"an n < e"
      using an(1,3) by(auto simp: LIMSEQ_def abs_of_pos) (metis dual_order.refl)
    from h obtain a where "a \<in> A" "x \<in> open_ball a (an n)"
      by auto
    with h'(2) open_ball_le[of "an n" e x] n
    show False
      by(auto simp: open_ball_inverse[of x])
  qed
next
  fix x n
  assume "x \<in> mtopology closure_of A"
  with an(1) have "open_ball x (an n) \<inter> A \<noteq> {}"
    by(auto simp: closure_of_mtopology)
  thus "x \<in> (\<Union>a\<in>A. open_ball a (an n))"
    by(auto simp: open_ball_inverse[of x])
qed

lemma nbh_add: "(\<Union>b\<in>(\<Union>a\<in>A. open_ball a e). open_ball b f) \<subseteq> (\<Union>a\<in>A. open_ball a (e + f))"
proof safe
  fix a x b
  assume h:"a \<in> A" "b \<in> open_ball a e" "x \<in> open_ball b f"
  show "x \<in> (\<Union>a\<in>A. open_ball a (e + f))"
  proof(rule UN_I[OF h(1)])
    have "dist a x \<le> dist a b + dist b x"
      by(auto intro!: dist_tr open_ballD'(2)[OF h(2)] open_ballD'[OF h(3)])
    also have "... < e + f"
      using  open_ballD[OF h(2)] open_ballD[OF h(3)] by auto
    finally show "x \<in> open_ball a (e + f)"
      using open_ballD'[OF h(2)] open_ballD'[OF h(3)]
      by(auto simp: open_ball_def)
  qed
qed

definition convergent_inS :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"convergent_inS f \<equiv> \<exists>s. converge_to_inS f s"

lemma convergent_inS_const:
  assumes "x \<in> S"
  shows "convergent_inS (\<lambda>n. x)"
  using converge_to_inS_const[OF assms] by(auto simp: convergent_inS_def)

lemma convergent_inS_ignore_initial:
  assumes "convergent_inS xn"
  shows "convergent_inS (\<lambda>n. xn (n + k))"
  using converge_to_inS_ignore_initial[of xn] assms
  by(auto simp: convergent_inS_def)

lemma convergent_inS_offset:
  assumes "convergent_inS (\<lambda>n. xn (n + k))" "xn \<in> sequence"
  shows "convergent_inS xn"
  using converge_to_inS_offset[of xn k] assms
  by(auto simp: convergent_inS_def)

definition the_limit_of :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
"the_limit_of xn \<equiv> THE x. converge_to_inS xn x"

lemma the_limit_if_converge:
  assumes "convergent_inS xn"
  shows "converge_to_inS xn (the_limit_of xn)"
  unfolding the_limit_of_def
  by(rule theI') (auto simp: assms[simplified convergent_inS_def] converge_to_inS_unique)

lemma the_limit_of_eq:
  assumes "converge_to_inS xn x"
  shows "the_limit_of xn = x"
  using assms converge_to_inS_unique the_limit_of_def by auto

lemma the_limit_of_inS:
  assumes "convergent_inS xn"
  shows "the_limit_of xn \<in> S"
  using the_limit_if_converge[OF assms] by(simp add:converge_to_inS_def)

lemma the_limit_of_const:
  assumes "x \<in> S"
  shows "the_limit_of (\<lambda>n. x) = x"
  by(rule the_limit_of_eq[OF converge_to_inS_const[OF assms]])

lemma convergent_inS_dest1:
  assumes "convergent_inS f"
  shows "f n \<in> S"
  using assms by(auto simp: convergent_inS_def converge_to_inS_def2)

definition Cauchy_inS:: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"Cauchy_inS f \<equiv> f \<in> sequence \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (f n) (f m) < \<epsilon>)"

lemma Cauchy_inS_def2:
 "Cauchy_inS f \<longleftrightarrow> f \<in> sequence \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball (f N) \<epsilon>)"
  unfolding Cauchy_inS_def
proof safe
  fix \<epsilon> :: real
  assume h:"f \<in> sequence" " \<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (f n) (f m) < \<epsilon>" "0 < \<epsilon>"
  then obtain N where hn:
     "\<And>n m. n \<ge> N \<Longrightarrow>  m\<ge>N \<Longrightarrow> dist (f n) (f m) < \<epsilon>"
    by fastforce
  show "\<exists>N. \<forall>n\<ge>N. f n \<in> open_ball (f N) \<epsilon>"
  proof(safe intro!: exI[where x=N])
    fix n
    assume "N \<le> n"
    then show "f n \<in> open_ball (f N) \<epsilon>"
      using h(1) hn[of N n] by(auto simp: open_ball_def)
  qed
next
  fix \<epsilon> :: real
  assume h:"f \<in> sequence" "\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball (f N) \<epsilon>" "0 < \<epsilon>"
  then obtain N where hn:
   "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> open_ball (f N) (\<epsilon>/2)"
    using linordered_field_class.half_gt_zero[OF h(3)] by blast
  show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (f n) (f m) < \<epsilon>"
  proof(safe intro!: exI[where x=N])
    fix n m
    assume "N \<le> n" "N \<le> m"
    from order.strict_trans1[OF dist_tr [of "f n" "f N" "f m"] strict_ordered_ab_semigroup_add_class.add_strict_mono[OF open_ballD[OF hn[OF this(1)],simplified dist_sym[of _ "f n"]] open_ballD[OF hn[OF this(2)]],simplified]]
    show "dist (f n) (f m) < \<epsilon>"
      using h(1) by auto
  qed
qed

lemma Cauchy_inS_def2':
 "Cauchy_inS f \<longleftrightarrow> f \<in> sequence \<and> (\<forall>\<epsilon>>0. \<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>)"
  unfolding Cauchy_inS_def2
proof safe
  fix \<epsilon> :: real
  assume h:"f \<in> sequence" "\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball (f N) \<epsilon>" "0 < \<epsilon>"
  then obtain N where "\<forall>n\<ge>N. f n \<in> open_ball (f N) \<epsilon>" by auto
  thus "\<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>"
    using h(1) by(auto intro!: exI[where x=N] bexI[where x="f N"])
next
  fix \<epsilon> :: real
  assume h:"f \<in> sequence" "\<forall>\<epsilon>>0. \<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>" "0 < \<epsilon>"
  then obtain x N where hxn:
   "x \<in> S" "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> open_ball x (\<epsilon>/2)"
    using linordered_field_class.half_gt_zero[OF h(3)] by blast
  show "\<exists>N. \<forall>n\<ge>N. f n \<in> open_ball (f N) \<epsilon>"
  proof(safe intro!: exI[where x=N])
    fix n
    assume "N \<le> n"
    from order.strict_trans1[OF dist_tr strict_ordered_ab_semigroup_add_class.add_strict_mono[OF open_ballD[OF hxn(2)[OF order.refl],simplified dist_sym[of x]] open_ballD[OF hxn(2)[OF this]],simplified]]
    show "f n \<in> open_ball (f N) \<epsilon>"
      using hxn(1) h(1) by(auto simp: open_ball_def)
  qed
qed

lemma Cauchy_inS_def2'':
 "Cauchy_inS f \<longleftrightarrow> f \<in> sequence \<and> (\<forall>\<epsilon>>0. \<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. dist x (f n) < \<epsilon>)"
  unfolding Cauchy_inS_def2'
proof safe
  fix \<epsilon> :: real
  assume h:"f \<in> sequence" "\<forall>\<epsilon>>0. \<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>" "0 < \<epsilon>"
  then obtain x N where
   "x \<in> S" "\<And>n. n \<ge> N \<Longrightarrow> f n \<in> open_ball x \<epsilon>"
    by blast
  then show "\<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. dist x (f n) < \<epsilon>"
    by(auto intro!: bexI[where x=x] exI[where x=N] simp: open_ballD[of _ x \<epsilon>])
next
  fix \<epsilon> :: real
  assume h:"f \<in> sequence" "\<forall>\<epsilon>>0. \<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. dist x (f n) < \<epsilon>" "0 < \<epsilon>"
  then obtain x N where 
   "x \<in> S" "\<And>n. n \<ge> N \<Longrightarrow> dist x (f n) < \<epsilon>" by blast
  then show "\<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> open_ball x \<epsilon>"
    using h(1) by(auto intro!: bexI[where x=x] exI[where x=N] simp: open_ball_def)
qed

lemma Cauchy_inS_dest1:
  assumes "Cauchy_inS f"
  shows "f n \<in> S"
  using assms by(auto simp: Cauchy_inS_def)

lemma Cauchy_if_convergent_inS:
  assumes "convergent_inS f"
  shows "Cauchy_inS f"
  unfolding Cauchy_inS_def
proof safe
  fix \<epsilon> :: real
  assume h:"0 < \<epsilon>"
  obtain s where hs:
   "s \<in> S" "\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. dist (f n) s < \<epsilon>"
    using assms by(auto simp: convergent_inS_def converge_to_inS_def2)
  then obtain N where hn:
    "\<And>n. n\<ge>N \<Longrightarrow> dist (f n) s < \<epsilon>/2"
    using half_gt_zero[OF h] by blast
  show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (f n) (f m) < \<epsilon>"
  proof(safe intro!: exI[where x=N])
    fix n m
    assume hnm:"N \<le> n" "N \<le> m"
    have "dist (f n) (f m) \<le> dist (f n) s + dist s (f m)"
      using convergent_inS_dest1[OF assms] hs
      by(auto intro!: dist_tr)
    also have "... = dist (f n) s + dist (f m) s"
      by(simp add: dist_sym[of s])
    also have "... < \<epsilon>"
      using hn[OF hnm(1)] hn[OF hnm(2)] by auto
    finally show "dist (f n) (f m) < \<epsilon>" .
  qed
next
  show "\<And>x. f x \<in> S"
    using assms[simplified convergent_inS_def converge_to_inS_def]
    by auto
qed

corollary Cauchy_inS_const: "a \<in> S \<Longrightarrow> Cauchy_inS (\<lambda>n. a)"
  by(auto intro!: Cauchy_if_convergent_inS convergent_inS_const)

lemma converge_if_Cauchy_and_subconverge:
  assumes "strict_mono a" "converge_to_inS (f \<circ> a) s" "Cauchy_inS f"
  shows "converge_to_inS f s"
  unfolding  converge_to_inS_def2
proof safe
  fix \<epsilon>
  assume "(0 :: real) < \<epsilon>"
  then have 1:"0 < \<epsilon>/2" by auto
  then obtain N where hn:"\<And>n. n \<ge> N \<Longrightarrow> dist (f (a n)) s < \<epsilon>/2"
    using assms(2) by(simp only: comp_def converge_to_inS_def2) metis
  obtain N' where hn':"\<And>n m. n \<ge> N' \<Longrightarrow> m \<ge> N' \<Longrightarrow> dist (f n) (f m) < \<epsilon>/2"
    using assms(3) 1 by(simp only: Cauchy_inS_def) metis
  show "\<exists>N. \<forall>n\<ge>N. dist (f n) s < \<epsilon>"
  proof(safe intro!: exI[where x="max N N'"])
    fix n
    assume "max N N' \<le> n"
    then have "N \<le> n" "N' \<le> n" by auto
    show "dist (f n) s < \<epsilon>"
      using add_strict_mono[OF hn'[OF \<open>N' \<le> n\<close> order_trans[OF \<open>N' \<le> n\<close> seq_suble[OF assms(1),of n]]] hn[OF \<open>N \<le> n\<close>]]  assms(2)
      by(auto simp: converge_to_inS_def intro!: order.strict_trans1[OF dist_tr[OF Cauchy_inS_dest1[OF assms(3),of n] Cauchy_inS_dest1[OF assms(3),of "a n"],of s],of \<epsilon>])
  qed
qed(auto simp: Cauchy_inS_dest1[OF assms(3)] assms(2)[simplified converge_to_inS_def])

lemma subCauchy_Cahcuy:
  assumes "Cauchy_inS xn" "strict_mono a"
  shows "Cauchy_inS (xn \<circ> a)"
  unfolding Cauchy_inS_def
proof safe
  show "\<And>x. (xn \<circ> a) x \<in> S"
    using assms(1) by(simp add: Cauchy_inS_dest1)
next
  fix \<epsilon>
  assume "(0 :: real) < \<epsilon>"
  then obtain N where "\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> dist (xn n) (xn m) < \<epsilon>"
    using assms(1) by(auto simp: Cauchy_inS_def) metis
  thus "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist ((xn \<circ> a) n) ((xn \<circ> a) m) < \<epsilon>"
    by(auto intro!: exI[where x=N] dest: order_trans[OF seq_suble[OF assms(2)] strict_mono_leD[OF assms(2)]])
qed

corollary Cauchy_inS_ignore_initial:
  assumes "Cauchy_inS xn"
  shows "Cauchy_inS (\<lambda>n. xn (n + k))"
  using subCauchy_Cahcuy[OF assms,of "\<lambda>n. n + k"]
  by(auto simp: comp_def strict_monoI)

(* TODO: offset *)

lemma Cauchy_inS_dist_Cauchy:
  assumes "Cauchy_inS xn" "Cauchy_inS yn"
  shows "Cauchy (\<lambda>n. dist (xn n) (yn n))"
  unfolding metric_space_class.Cauchy_altdef2 dist_real_def
proof safe
  have h:"\<And>n. xn n \<in> S" "\<And>n. yn n \<in> S"
    using assms by(auto simp: Cauchy_inS_dest1)
  fix e :: real
  assume e:"0 < e"
  with assms obtain N1 N2 where N: "\<And>n m. n \<ge> N1 \<Longrightarrow> m \<ge> N1 \<Longrightarrow> dist (xn n) (xn m) < e / 2" "\<And>n m. n \<ge> N2 \<Longrightarrow> m \<ge> N2 \<Longrightarrow> dist (yn n) (yn m) < e / 2"
    by (metis Cauchy_inS_def zero_less_divide_iff zero_less_numeral)
  define N where "N \<equiv> max N1 N2"
  then have N': "N \<ge> N1" "N \<ge> N2" by auto
  show "\<exists>N. \<forall>n\<ge>N. \<bar>dist (xn n) (yn n) - dist (xn N) (yn N)\<bar> < e"
  proof(safe intro!: exI[where x=N])
    fix n
    assume n:"N \<le> n"
    have "dist (xn n) (yn n) \<le> dist (xn n) (xn N) + dist (xn N) (yn N) + dist (yn N) (yn n)"
         "dist (xn N) (yn N) \<le> dist (xn N) (xn n) + dist (xn n) (yn n) + dist (yn n) (yn N)"
      using dist_tr[OF h(1)[of n] h(1)[of N] h(2)[of n]] dist_tr[OF h(1)[of N] h(2)[of N] h(2)[of n]]
            dist_tr[OF h(1)[of N] h(2)[of n] h(2)[of N]] dist_tr[OF h(1)[of N] h(1)[of n] h(2)[of n]] by auto
    thus "\<bar>dist (xn n) (yn n) - dist (xn N) (yn N)\<bar> < e"
      using N(1)[OF N'(1) order.trans[OF N'(1) n]] N(2)[OF N'(2) order.trans[OF N'(2) n]] N(1)[OF order.trans[OF N'(1) n] N'(1)] N(2)[OF order.trans[OF N'(2) n] N'(2)]
      by auto
  qed
qed

corollary Cauchy_inS_dist_convergent:
  assumes "Cauchy_inS xn" "Cauchy_inS yn"
  shows "convergent (\<lambda>n. dist (xn n) (yn n))"
  using Cauchy_inS_dist_Cauchy[OF assms] Cauchy_convergent_iff by blast

text \<open>\<^url>\<open>https://people.bath.ac.uk/mw2319/ma30252/sec-dense.html.\<close>\<close>
abbreviation "dense_set \<equiv> dense_of mtopology"

lemma dense_set_def:
 "dense_set U \<longleftrightarrow> U \<subseteq> S \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {})"
proof
  assume h:" U \<subseteq> S \<and>(\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {})"
  show "dense_of mtopology U"
  proof(rule dense_ofI)
    fix V
    assume h':"openin mtopology V" "V \<noteq> {}"
    then obtain x where 1:"x \<in> V" by auto
    then obtain \<epsilon> where 2:"\<epsilon>>0" "open_ball x \<epsilon> \<subseteq> V"
      using h' mtopology_openin_iff[of V] by blast
    have "open_ball x \<epsilon> \<inter> U \<noteq> {}"
      using h 1 2 openin_subset[OF h'(1), simplified mtopology_topspace]
      by auto
    thus "U \<inter> V \<noteq> {}" using 2 by auto
  next
    show "U \<subseteq> topspace mtopology"
      using h mtopology_topspace by auto
  qed 
next
  assume h:"dense_of mtopology U"
  have "\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {}"
  proof safe
    fix x \<epsilon>
    assume "x \<in> S" "(0 :: real) < \<epsilon>" "open_ball x \<epsilon> \<inter> U = {}"
    then have "open_ball x \<epsilon> \<noteq> {}" "openin mtopology (open_ball x \<epsilon>)"
      using open_ball_ina[of x \<epsilon>] mtopology_open_ball_in[of x \<epsilon>]
      by blast+
    thus False
      using h \<open>open_ball x \<epsilon> \<inter> U = {}\<close> by(auto simp: dense_of_def)
  qed
  thus "U \<subseteq> S \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {})"
    using h mtopology_topspace by(auto simp: dense_of_def)
qed

corollary dense_set_balls_cover:
  assumes "dense_set U" and "e > 0"
  shows "(\<Union>u\<in>U. open_ball u e) = S"
  using assms open_ball_subset_ofS by(auto simp: dense_set_def) (meson Int_emptyI open_ball_inverse)

lemma dense_set_empty_iff: "dense_set {} \<longleftrightarrow> S = {}"
  by(auto simp: dense_set_def ) (use zero_less_one in blast)

lemma dense_set_S: "dense_set S"
  using open_ball_ina dense_set_def by blast

lemma dense_set_def2:
 "dense_set U \<longleftrightarrow> U \<subseteq> S \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0.\<exists>y\<in>U. dist x y < \<epsilon>)"
proof
  assume h: "dense_set U"
  show "U \<subseteq> S \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0. \<exists>y\<in>U. dist x y < \<epsilon>)"
  proof safe
    fix x \<epsilon>
    assume hxe: "x \<in> S" "(0 :: real) < \<epsilon>"
    then obtain z where
      "z \<in> open_ball x \<epsilon> \<inter> U"
      using h by(fastforce simp: dense_set_def)
    thus "\<exists>y\<in>U. dist x y < \<epsilon>"
      by(auto intro!: bexI[where x=z] simp: open_ball_def hxe)
  qed(use h[simplified dense_set_def] in auto)
next
  assume h:"U \<subseteq> S \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0. \<exists>y\<in>U. dist x y < \<epsilon>)"
  show "dense_set U"
    unfolding dense_set_def
  proof safe
    fix x \<epsilon>
    assume hxe: "x \<in> S" "(0 :: real) < \<epsilon>" "open_ball x \<epsilon> \<inter> U = {}"
    then obtain y where
      "y \<in> U" "y \<in> S" "dist x y < \<epsilon>"
      using h by blast
    hence "y \<in> open_ball x \<epsilon> \<inter> U"
      by(auto simp: open_ball_def hxe)
    thus False
      using hxe(3) by auto
  qed(use h in auto)
qed

lemma dense_set_def2':
 "dense_set U \<longleftrightarrow> U \<subseteq> S \<and> (\<forall>x\<in>S. \<exists>f\<in>UNIV \<rightarrow> U. converge_to_inS f x)"
  unfolding dense_set_def
proof
  show "U \<subseteq> S \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {}) \<Longrightarrow> U \<subseteq> S \<and> (\<forall>x\<in>S. \<exists>f\<in>UNIV \<rightarrow> U. converge_to_inS f x)"
  proof safe
    fix x
    assume h: "U \<subseteq> S" "\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {}" "x \<in> S"
    then have "\<And>n::nat. open_ball x (1 / (real n + 1)) \<inter> U \<noteq> {}"
      by auto
    hence "\<forall>n. \<exists>k. k \<in> open_ball x (1 / (real n + 1)) \<inter> U" by auto
    hence "\<exists>a. \<forall>n. a n \<in> open_ball x (1 / (real n + 1)) \<inter> U" by(rule choice)
    then obtain a where hf: "\<And>n :: nat. a n \<in> open_ball x (1 / (real n + 1)) \<inter> U"
      by auto
    show "\<exists>f\<in>UNIV \<rightarrow> U. converge_to_inS f x"
      unfolding converge_to_inS_def2'
    proof(safe intro!: bexI[where x=a])
      fix \<epsilon> :: real
      assume he:"0 < \<epsilon>"
      then obtain N where hn: "1 / \<epsilon> < real N"
        using reals_Archimedean2 by blast
      have hn': "0 < real N"
        by(rule ccontr) (use hn he in fastforce)
      hence "1 / real N < \<epsilon>"
        using he hn by (metis divide_less_eq mult.commute)
      hence hn'':"1 / (real N + 1) < \<epsilon>"
        using hn' by(auto intro!: order.strict_trans[OF linordered_field_class.divide_strict_left_mono[of "real N" "real N + 1" 1]])
      show "\<exists>N. \<forall>n\<ge>N. a n \<in> open_ball x \<epsilon>"
      proof(safe intro!: exI[where x="N"])
        fix n
        assume "N \<le> n"
        then have 1:"1 / (real n + 1) \<le> 1 / (real N + 1)"
          using hn' by(auto intro!: linordered_field_class.divide_left_mono)
        show "a n \<in> open_ball x \<epsilon>"
          using open_ball_le[OF 1,of x] open_ball_le[OF order.strict_implies_order[OF hn''],of x] hf[of n]
          by auto
      qed
    next
      show "\<And>x. a x \<in> S" "x \<in> S" "\<And>x. a x \<in> U"
        using h(1,3) hf by auto
    qed
  qed
next
  assume h:"U \<subseteq> S \<and> (\<forall>x\<in>S. \<exists>f\<in>UNIV \<rightarrow> U. converge_to_inS f x)"
  have "\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {}"
  proof safe
    fix x \<epsilon>
    assume hxe:"x \<in> S" "(0 :: real) < \<epsilon>" "open_ball x \<epsilon> \<inter> U = {}"
    then obtain f N where
     "f\<in>UNIV \<rightarrow> U" "\<forall>n\<ge>N :: nat. f n \<in> open_ball x \<epsilon>"
      using h[simplified converge_to_inS_def2'] by blast
    hence "f N \<in> open_ball x \<epsilon> \<inter> U"
      by auto
    thus False using hxe by auto
  qed
  thus "U \<subseteq> S \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0. open_ball x \<epsilon> \<inter> U \<noteq> {})"
    using h by auto
qed

lemma dense_set_infinite:
  assumes "infinite S" "dense_set U"
  shows "infinite U"
proof
  assume finu:"finite U"
  with assms(1) obtain x where x:"x \<in> S" "x \<notin> U"
    by (meson finite_subset subset_iff)
  define e where "e \<equiv> Min {dist x y |y. y \<in> U}"
  have nen: "{dist x y |y. y \<in> U} \<noteq> {}"
    using dense_set_empty_iff assms by auto
  have fin: "finite {dist x y |y. y \<in> U}"
    using finu by auto
  have epos: "0 < e"
    unfolding Min_gr_iff[OF fin nen] e_def
  proof safe
    fix y
    assume "y \<in> U"
    then have "y \<in> S" "x \<noteq> y"
      using assms(2) x(2) by(auto simp: dense_set_def)
    thus "0 < dist x y"
      using dist_0[OF x(1),of y] dist_geq0[of x y] by auto
  qed
  then obtain y where y:"y\<in>U" "dist x y < e"
    using assms(2) x(1) by(fastforce simp: dense_set_def2)
  thus False
    using Min_le[OF fin,of "dist x y"] by(auto simp: e_def)
qed

lemma mtopology_Hausdorff: "Hausdorff_space mtopology"
  unfolding Hausdorff_space_def
proof safe
  fix x y
  assume "x \<in> topspace mtopology" "y \<in> topspace mtopology" "x \<noteq> y"
  then have [simp]:"x \<in> S" "y \<in> S"
    using mtopology_topspace by auto
  with \<open>x \<noteq> y\<close> have 1:"dist x y > 0"
    using dist_0[of x y] dist_geq0[of x y] by auto
  show "\<exists>U V. openin mtopology U \<and> openin mtopology V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V"
  proof(rule exI[where x="open_ball x (dist x y/2)"])
    show "\<exists>V. openin mtopology (open_ball x (dist x y / 2)) \<and> openin mtopology V \<and> x \<in> open_ball x (dist x y / 2) \<and> y \<in> V \<and> disjnt (open_ball x (dist x y / 2)) V"
    proof(safe intro!: exI[where x="open_ball y (dist x y/2)"])
      show "disjnt (open_ball x (dist x y / 2)) (open_ball y (dist x y / 2))"
        unfolding disjnt_iff
      proof safe
        fix z
        assume h:"z \<in> open_ball x (dist x y / 2)" "z \<in> open_ball y (dist x y / 2)"
        show False
          using dist_tr[OF \<open>x \<in> S\<close> open_ballD'(1)[OF h(1)] \<open>y \<in> S\<close>] open_ballD[OF h(1)] open_ballD[OF h(2)]
          by (simp add: dist_sym)
      qed
    qed(auto intro!: mtopology_open_ball_in 1 open_ball_ina)
  qed
qed

text \<open> Diameter\<close>
definition diam :: "'a set \<Rightarrow> ennreal" where
"diam A \<equiv> \<Squnion> {ennreal (dist x y) | x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S}"

lemma diam_empty[simp]:
 "diam {} = 0"
  by(simp add: diam_def bot_ennreal)

lemma diam_def2:
  assumes "A \<subseteq> S"
  shows "diam A = \<Squnion> {ennreal (dist x y) | x y. x \<in> A \<and> y \<in> A}"
  using assms by(auto simp: diam_def) (meson subset_eq)

lemma diam_subset:
  assumes "A \<subseteq> B"
  shows "diam A \<le> diam B"
  unfolding diam_def using assms by(auto intro!: Sup_subset_mono)

lemma diam_cball_leq: "diam (closed_ball a \<epsilon>) \<le> ennreal (2 * \<epsilon>)"
  unfolding Sup_le_iff diam_def
proof safe
  fix x y
  assume h:"x \<in> closed_ball a \<epsilon>" "y \<in> closed_ball a \<epsilon>" "x \<in> S" "y \<in> S"
  have "dist x y \<le> 2 * \<epsilon>"
    using dist_tr[OF h(3) closed_ballD'(2)[OF h(1)] h(4)] closed_ballD[OF h(1),simplified dist_sym[of a x]] closed_ballD[OF h(2)]
    by auto
  thus "ennreal (dist x y) \<le> ennreal (2 * \<epsilon>)"
    using dist_geq0[of x y] ennreal_leI[of _ "2*\<epsilon>"] by simp
qed

lemma diam_ball_leq:
 "diam (open_ball a \<epsilon>) \<le> ennreal (2 * \<epsilon>)"
  using diam_subset[OF open_ball_closed_ball[of a \<epsilon>]] diam_cball_leq[of a \<epsilon>]
  by auto

lemma diam_is_sup:
  assumes "x \<in> A \<inter> S" "y \<in> A \<inter> S"
  shows "dist x y \<le> diam A"
  using assms by(auto simp: diam_def intro!:Sup_upper)

lemma diam_is_sup':
  assumes "x \<in> A \<inter> S" "y \<in> A \<inter> S" "diam A \<le> ennreal r" "r \<ge> 0"
  shows "dist x y \<le> r"
  using order.trans[OF diam_is_sup[OF assms(1,2)] assms(3)] assms(4) by simp

lemma diam_le:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> dist x y \<le> r"
  shows "diam A \<le> r"
  using assms by(auto simp: diam_def Sup_le_iff ennreal_leI)

lemma diam_eq_closure: "diam (mtopology closure_of A) = diam A"
proof(rule antisym)
  show "diam A \<le> diam (mtopology closure_of A)"
    by(auto intro!: Sup_subset_mono simp: diam_def) (metis in_closure_of mtopology_topspace)
next
  have "{ennreal (dist x y) |x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S} = ennreal ` {dist x y |x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S}"
    by auto
  also have "diam (mtopology closure_of A) \<le> \<Squnion> ..."
    unfolding le_Sup_iff_less
  proof safe
    fix r
    assume "r < diam (mtopology closure_of A)"
    then obtain x y where xy:"x \<in> mtopology closure_of A" "x \<in> S" "y \<in> mtopology closure_of A" "y \<in> S" "r < ennreal (dist x y)"
      by(auto simp: diam_def less_Sup_iff)
    hence "r < \<top>"
      using dual_order.strict_trans ennreal_less_top by blast
    define e where "e \<equiv> (dist x y - enn2real r)/2"
    have "e > 0"
      using xy(5) \<open>r < \<top>\<close> by(simp add: e_def)
    then obtain x' y' where xy':"x' \<in> open_ball x e" "x'\<in> A" "y' \<in> open_ball y e" "y'\<in> A"
      using xy by(fastforce simp: closure_of_mtopology)
    show "\<exists>i\<in>{dist x y |x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S}. r \<le> ennreal i"
    proof(safe intro!: bexI[where x="dist x' y'"])
      have "dist x y \<le> dist x x' + dist x' y' + dist y y'"
        using dist_tr[OF xy(2) open_ballD'(1)[OF xy'(1)] xy(4)] dist_tr[OF open_ballD'(1)[OF xy'(1)] open_ballD'(1)[OF xy'(3)] xy(4)]
        by(simp add: dist_sym)
      also have "... < dist x y - enn2real r + dist x' y'"
        using open_ballD[OF xy'(1)] open_ballD[OF xy'(3)]
        by(simp add: e_def)
      finally have "enn2real r < dist x' y'" by simp
      thus "r \<le> ennreal (dist x' y')"
        by (simp add: \<open>r < \<top>\<close>)
    qed(use open_ballD'(1)[OF xy'(1)] open_ballD'(1)[OF xy'(3)] xy'(2,4) in auto)
  qed
  finally show "diam (mtopology closure_of A) \<le> diam A"
    by(simp add: diam_def)
qed

definition bounded_set :: "'a set \<Rightarrow> bool" where
"bounded_set A \<longleftrightarrow> diam A < \<infinity>"

lemma bounded_set_def2': "bounded_set A \<longleftrightarrow> (\<exists>e. \<forall>x\<in>A\<inter>S. \<forall>y\<in>A\<inter>S. dist x y < e)"
proof
  assume "bounded_set A"
  consider "A \<inter> S = {}" | "A \<inter> S \<noteq> {}" by auto
  then show " \<exists>e. \<forall>x\<in>A \<inter> S. \<forall>y\<in>A \<inter> S. dist x y < e"
  proof cases
    case h:2
    then have 1:"{dist x y |x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S} \<noteq> {}" by auto
    have eq:"{ennreal (dist x y) | x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S} = ennreal ` {dist x y | x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S}"
      by auto
    hence 2:"diam A = \<Squnion> (ennreal ` {dist x y | x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S})"
      by(simp add: diam_def)
    obtain x y where hxy:
     "x \<in> A \<inter> S" "y \<in> A \<inter> S" "diam A < ennreal (dist x y) + ennreal 1"
      using SUP_approx_ennreal[OF _ 1 2,of 1] \<open>bounded_set A\<close>
      by(fastforce simp: bounded_set_def)
    hence "diam A < ennreal (dist x y + 1)"
      using dist_geq0 by simp
    from SUP_lessD[OF this[simplified 2]]
    have "\<And>w z. w \<in> A \<inter> S \<Longrightarrow> z \<in> A \<inter> S \<Longrightarrow> ennreal (dist w z) < ennreal (dist x y + 1)"
      by blast
    thus "\<exists>e. \<forall>x\<in>A \<inter> S. \<forall>y\<in>A \<inter> S. dist x y < e"
      by(auto intro!: exI[where x="dist x y + 1"] simp: ennreal_less_iff[OF dist_geq0])
  qed simp
next
  assume "\<exists>e. \<forall>x\<in>A\<inter>S. \<forall>y\<in>A\<inter>S. dist x y < e"
  then obtain e where he: "\<And>x y. x \<in> A \<inter> S \<Longrightarrow> y \<in> A \<inter> S \<Longrightarrow> dist x y < e"
    by auto
  hence "\<And>z. z \<in> {ennreal (dist x y) | x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S} \<Longrightarrow> z < ennreal e"
    using ennreal_less_iff[OF dist_geq0] by auto
  hence "\<Squnion> {ennreal (dist x y) | x y. x \<in> A \<inter> S \<and> y \<in> A \<inter> S} \<le> ennreal e"
    by (meson Sup_least order_less_le)
  thus "bounded_set A"
    by(simp add: bounded_set_def diam_def order_le_less_trans[OF _  ennreal_less_top])
qed

lemma bounded_set_def2:
  assumes "A \<subseteq> S"
  shows "bounded_set A \<longleftrightarrow> (\<exists>e. \<forall>x\<in>A. \<forall>y\<in>A. dist x y < e)"
  using assms by(fastforce simp: bounded_set_def2')

lemma bounded_set_def3':
  assumes "S \<noteq> {}"
  shows "bounded_set A \<longleftrightarrow> (\<exists>e. \<exists>x\<in>S. \<forall>y\<in>A\<inter>S. dist x y < e)"
  unfolding bounded_set_def2'
proof
  assume h:"\<exists>e. \<forall>x\<in>A \<inter> S. \<forall>y\<in>A \<inter> S. dist x y < e"
  obtain s where [simp]:"s \<in> S" using assms by auto
  consider "A \<inter> S = {}" | "A \<inter> S \<noteq> {}" by auto
  then show "\<exists>e. \<exists>x\<in>S. \<forall>y\<in>A \<inter> S. dist x y < e"
  proof cases
    case 1
    then show ?thesis
      by(auto intro!: exI[where x=0] exI[where x=s])
  next
    case 2
    then obtain sa where [simp]:"sa \<in> A" "sa \<in> S" by auto
    obtain e where "\<forall>x\<in>A \<inter> S. \<forall>y\<in>A \<inter> S. dist x y < e"
      using h by auto
    then show ?thesis
      by(auto intro!: exI[where x=e] bexI[where x=sa])
  qed
next
  assume "\<exists>e. \<exists>x\<in>S. \<forall>y\<in>A \<inter> S. dist x y < e"
  then obtain e a where
   [simp]:"a \<in> S" and hea:"\<And>y. y \<in> A \<Longrightarrow> y \<in> S \<Longrightarrow> dist a y < e" by auto
  show "\<exists>e. \<forall>x\<in>A \<inter> S. \<forall>y\<in>A \<inter> S. dist x y < e"
  proof(safe intro!: exI[where x="2*e"])
    fix x y
    assume [simp]:"x \<in> A" "x \<in> S" "y \<in> A" "y \<in> S"
    show "dist x y < 2 * e"
      using dist_tr[of x a y] hea[of x] hea[of y]
      by(simp add: dist_sym[of x a])
  qed
qed

lemma bounded_set_def4':
 "bounded_set A \<longleftrightarrow> (\<exists>x e. A \<inter> S \<subseteq> open_ball x e)"
proof
  assume h:"bounded_set A"
  consider "A \<inter> S = {}" | "A \<inter> S \<noteq> {}" by auto
  then show "\<exists>x e. A \<inter> S \<subseteq> open_ball x e"
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2
    then have "\<exists>e. \<exists>x\<in>S. \<forall>y\<in>A\<inter>S. dist x y < e"
      using bounded_set_def3' h by blast
    then obtain e x where
     [simp]: "x \<in> S" and hex: "\<And>y. y \<in> A \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < e"
      by auto
    thus ?thesis
      by(auto intro!: exI[where x=x] exI[where x=e] simp:open_ball_def)
  qed
next
  assume "\<exists>x e. A \<inter> S \<subseteq> open_ball x e"
  then obtain a e where hxe:"A \<inter> S \<subseteq> open_ball a e" by auto
  show "bounded_set A"
    unfolding bounded_set_def2'
  proof(safe intro!: exI[where x="2*e"])
    fix x y
    assume [simp]:"x \<in> A" "x \<in> S" "y \<in> A" "y \<in> S"
    then have "x \<in> open_ball a e" "y \<in> open_ball a e"
      using hxe by auto
    hence "dist a x < e" "dist a y < e" "a \<in> S"
      by(auto dest: open_ballD open_ballD')
    thus "dist x y < 2 * e"
      using dist_tr[of x a y] by(simp add: dist_sym[of x a])
  qed
qed

lemma bounded_set_def4:
  assumes "A \<subseteq> S"
  shows "bounded_set A \<longleftrightarrow> (\<exists>x e. A \<subseteq> open_ball x e)"
  using bounded_set_def4'[of A] assms by blast


text \<open> Distance between a point and a set. \<close>
definition dist_set :: "'a set \<Rightarrow> 'a \<Rightarrow> real" where
"dist_set A \<equiv> (\<lambda>x. if A = {} then 0 else Inf {dist x y |y. y \<in> A})"

lemma dist_set_geq0:
 "dist_set A x \<ge> 0"
proof -
  have "{dist x y |y. y \<in> A} = dist x ` A" by auto
  thus ?thesis
    using dist_geq0[of x] by(auto simp: dist_set_def intro!: cINF_greatest[of _ _ "dist x"])
qed

lemma dist_set_bdd_below[simp]:
 "bdd_below {dist x y |y. y \<in> A}"
  by(auto simp: bdd_below_def dist_geq0 intro!: exI[where x=0])

lemma dist_set_singleton[simp]:
  "dist_set {y} x = dist x y"
  by(auto simp: dist_set_def)

lemma dist_set_singleton'[simp]:
  "dist_set {y} = (\<lambda>x. dist x y)"
  by auto

lemma dist_set_empty[simp]:
 "dist_set {} x = 0"
  by(simp add: dist_set_def)

lemma dist_set_nsubset0[simp]:
  assumes "\<not> (A \<subseteq> S)"
  shows "dist_set A x = 0"
proof -
  obtain a where "a \<in> A" "a \<notin> S"
    using assms by auto
  hence "A \<noteq> {}" "0 \<in> {dist x y |y. y \<in> A}"
    using dist_notin'[of a x] by auto
  thus ?thesis
    using \<open>A \<noteq> {}\<close> dist_set_geq0[of A x] cInf_lower[OF \<open>0 \<in> {dist x y |y. y \<in> A}\<close>]
    by(auto simp: dist_set_def)
qed

lemma dist_set_notin[simp]:
  assumes "x \<notin> S"
  shows "dist_set A x = 0"
proof -
  have "A \<noteq> {} \<Longrightarrow> {dist x y |y. y \<in> A} = {0}"
    using dist_notin[OF \<open>x \<notin> S\<close>] by auto
  thus ?thesis
    by(simp add: dist_set_def)
qed

lemma dist_set_inA:
  assumes "x \<in> A"
  shows "dist_set A x = 0"
proof(cases "A \<subseteq> S")
  case h:True
  hence "A \<noteq> {}" "0 \<in> {dist x y |y. y \<in> A}"
    using dist_0[of x x] assms by force+
  thus ?thesis
    using cInf_lower[OF \<open>0 \<in> {dist x y |y. y \<in> A}\<close>] dist_set_geq0[of A x]
    by(auto simp: dist_set_def)
qed (simp add: dist_geq0)

lemma dist_set_nzeroD:
  assumes "dist_set A x \<noteq> 0"
  shows "A \<subseteq> S" "x \<notin> A"
  by(rule ccontr, use assms dist_set_inA in auto)

lemma dist_set_antimono:
  assumes "A \<subseteq> B" "A \<noteq> {}"
  shows "dist_set B x \<le> dist_set A x"
proof(cases "B = {}")
  case h:False
  with assms have "{dist x y |y. y \<in> B} \<noteq> {}" "{dist x y |y. y \<in> A} \<subseteq> {dist x y |y. y \<in> B}"
    by auto
  thus ?thesis
    by(simp add: dist_set_def cInf_superset_mono assms(2))
qed(use assms in simp)

lemma dist_set_bounded:
  assumes "\<And>y. y \<in> A \<Longrightarrow> dist x y < K" "K > 0"
  shows "dist_set A x < K"
proof(cases "A = {}")
  case True
  then show ?thesis
    by(simp add: assms)
next
  case 1:False
  then have 2:"{dist x y |y. y \<in> A} \<noteq> {}" by auto
  show ?thesis
    using assms by (auto simp add: dist_set_def cInf_lessD[OF 2]  cInf_less_iff[OF 2])
qed

lemma dist_set_tr:
  assumes "x \<in> S" "y \<in> S"
  shows "dist_set A x \<le> dist x y + dist_set A y"
proof(cases "A \<subseteq> S")
  case h:True
  consider "A = {}" | "A \<noteq> {}" by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by(simp add: dist_set_def dist_geq0)
  next
    case 2
    have "dist_set A x \<le> Inf {dist x y + dist y a |a. a\<in>A}"
    proof -
      have "\<Sqinter> {dist x y |y. y \<in> A} \<le> \<Sqinter> {dist x y + dist y a |a. a \<in> A}"
      proof(rule cInf_mono)
        fix b
        assume "b \<in> {dist x y + dist y a |a. a \<in> A}"
        then obtain a where "a \<in> A" "b = dist x y + dist y a"
          by auto
        thus "\<exists>a\<in>{dist x y |y. y \<in> A}. a \<le> b"
          using h assms by(auto intro!: exI[where x="dist x a"] dist_tr)
      qed(simp_all add: 2)
      thus ?thesis
        by(simp add: dist_set_def 2)
    qed
    also have "... = dist x y + Inf {dist y a |a. a\<in>A}"
    proof -
      have "ereal (Inf {dist x y + dist y a |a. a\<in>A}) = ereal (dist x y + Inf {dist y a |a. a\<in>A})"
           (is "?lhs = ?rhs")
      proof -
        have "?lhs = Inf (ereal ` {(dist x y + dist y a) |a. a\<in>A})"
          using dist_geq0 by(auto intro!: ereal_Inf' bdd_belowI[where m=0] simp: 2)
        also have "... = Inf {ereal (dist x y + dist y a) |a. a\<in>A}"
        proof -
          have "ereal ` {(dist x y + dist y a) |a. a\<in>A} = {ereal (dist x y + dist y a) |a. a\<in>A}"
            by auto
          thus ?thesis by simp
        qed
        also have "... = (\<Sqinter>a\<in>A. ereal (dist x y) + ereal (dist y a))"
          by (simp add: Setcompr_eq_image)
        also have "... = ereal (dist x y) + (\<Sqinter>a\<in>A. ereal (dist y a))"
          by(rule INF_ereal_add_right) (use 2 dist_geq0 in auto)
        also have "... = ereal (dist x y) + (\<Sqinter> (ereal ` {dist y a | a. a \<in> A}))"
          by (simp add: Setcompr_eq_image image_image)
        also have "... = ereal (dist x y) + ereal (Inf {dist y a |a. a\<in>A})"
        proof -
          have "ereal (Inf {dist y a |a. a\<in>A}) = (\<Sqinter> (ereal ` {dist y a | a. a \<in> A}))"
            using dist_geq0 by(auto intro!: ereal_Inf' simp: 2)
          thus ?thesis by simp
        qed
        also have "... = ?rhs" by simp
        finally show ?thesis .
      qed
      thus ?thesis by simp
    qed
    also have "... = dist x y + dist_set A y"
      by(simp add: 2 dist_set_def)
    finally show ?thesis .
  qed
qed (simp add: dist_geq0)

lemma dist_set_abs_le:
  assumes "x \<in> S" "y \<in> S"
  shows "\<bar>dist_set A x - dist_set A y\<bar> \<le> dist x y"
  using dist_set_tr[OF assms,of A] dist_set_tr[OF assms(2,1),of A,simplified dist_sym[of y x]]
  by auto

lemma dist_set_inA_le:
  assumes "y \<in> A"
  shows "dist_set A x \<le> dist x y"
proof -
  consider "x \<notin> S \<or> y \<notin> S" | "x \<in> S \<and> y \<in> S" by auto
  thus ?thesis
  proof cases
    case 1
    have "y \<notin> S \<Longrightarrow> \<not> (A \<subseteq> S)"
      using assms by auto
    with 1 dist_geq0 show ?thesis
      by auto
  next
    case 2
    with dist_set_tr[of x y A] dist_set_inA[OF assms]
    show ?thesis by simp
  qed
qed

lemma dist_set_ball_open:
 "openin mtopology {x\<in>S. dist_set A x < \<epsilon>}"
  unfolding mtopology_openin_iff
proof safe
  fix x
  assume h:"x \<in> S" "dist_set A x < \<epsilon>"
  show "\<exists>\<epsilon>'>0. open_ball x \<epsilon>' \<subseteq> {x \<in> S. dist_set A x < \<epsilon>}"
  proof(safe intro!: exI[where x="\<epsilon> - dist_set A x"])
    fix y
    assume h':"y \<in> open_ball x (\<epsilon> - dist_set A x)"
    have "dist_set A y \<le> dist x y + dist_set A x"
      by(rule dist_set_tr[OF open_ballD'(1)[OF h'] h(1),simplified dist_sym[of y x]])
    also have "... < \<epsilon>"
      using open_ballD[OF h'] by auto
    finally show "dist_set A y < \<epsilon>" .
  qed(use h open_ballD'(1) in auto)
qed

lemma dist_set_ball_empty:
  assumes "A \<noteq> {}" "A \<subseteq> S" "e > 0" "x \<in> S" "open_ball x e \<inter> A = {}"
  shows "dist_set A x \<ge> e"
  using assms by(auto simp: dist_set_def assms(1) le_cInf_iff intro!: open_ball_nin_le[OF assms(4,3)])

lemma dist_set_closed_ge0:
  assumes "closedin mtopology A" "A \<noteq> {}" "x \<in> S" "x \<notin> A"
  shows "dist_set A x > 0"
proof -
  have a:"A \<subseteq> S" "openin mtopology (S - A)"
    using closedin_subset[OF assms(1)] assms(1)
    by(auto simp: closedin_def mtopology_topspace)
  with assms(3,4) obtain e where e: "e > 0" "open_ball x e \<subseteq> S - A"
    by(auto simp: mtopology_openin_iff) (meson Diff_iff)
  thus ?thesis
    by(auto intro!: order.strict_trans2[OF e(1) dist_set_ball_empty[OF assms(2) a(1) e(1) assms(3)]])
qed

lemma g_delta_of_closed:
  assumes "closedin mtopology M"
  shows "g_delta_of mtopology M"
proof(cases "M = {}")
  case True
  then show ?thesis by simp
next
  case M_ne:False
  have "M \<subseteq> S"
    using assms mtopology_topspace by (simp add: closedin_def)
  define U where "U \<equiv> (\<lambda>n. {x\<in>S. dist_set M x < 1 / real n})"
  define \<U> where "\<U> \<equiv> {U n| n. n > 0}"
  have mun:"M \<subseteq> U n" if "n > 0" for n
    using dist_set_inA[of _ M] that \<open>M \<subseteq> S\<close> by(auto simp: U_def)
  show ?thesis
  proof(rule g_delta_ofI[of "\<U>"])
    show "\<U> \<noteq> {}"
      by(auto simp: \<U>_def)
  next
    have "\<U> = U ` {0<..}" by(auto simp: \<U>_def)
    thus "countable \<U>" by simp
  next
    fix b
    assume "b \<in> \<U>"
    then show "openin mtopology b"
      using dist_set_ball_open by(auto simp: \<U>_def U_def)
  next
    show "M = \<Inter> \<U>"
    proof(standard;standard)
      fix x
      assume "x \<in> M"
      with mun
      show "x \<in> \<Inter> \<U>"
        by(auto simp: \<U>_def)
    next
      fix x
      assume "x \<in> \<Inter> \<U>"
      then have "Inf {dist x m|m. m\<in>M} < 1 / real n" if "n > 0" for n
        using that by(auto simp: \<U>_def U_def M_ne dist_set_def)
      hence 1:"Inf {dist x m|m. m\<in>M} < 1 / real (Suc n)" for n
        by blast
      have "\<exists>m\<in>M. dist x m < 1 / real (Suc n)" for n
        using 1[of n] cInf_less_iff[of "{dist x m |m. m \<in> M}" "1 / real (Suc n)"] M_ne
        by auto
      then obtain m where hm: "\<And>n. m n \<in> M" "\<And>n. dist x (m n) < 1 / real (Suc n)"
        by metis
      hence "m \<in> UNIV \<rightarrow> M" by auto
      have "converge_to_inS m x"
        unfolding converge_to_inS_def2
      proof safe
        show "\<And>x. m x \<in> S" "x \<in> S"
          using \<open>x \<in> \<Inter> \<U>\<close> \<open>m \<in> UNIV \<rightarrow> M\<close> \<open>M \<subseteq> S\<close>
          by(auto simp: \<U>_def U_def)
      next
        fix \<epsilon>
        assume "(0 :: real) < \<epsilon>"
        then obtain N where hN: "1 / real (Suc N) < \<epsilon>"
          using nat_approx_posE by blast
        show "\<exists>N. \<forall>n\<ge>N. dist (m n) x < \<epsilon>"
        proof(safe intro!: exI[where x=N])
          fix n
          assume "N \<le> n"
          then have "1 / real (Suc n) \<le> 1 / real (Suc N)"
            by (simp add: frac_le)
          from  order.strict_trans1[OF this hN] hm(2)[of n]
          show "dist (m n) x < \<epsilon>"
            by(simp add: dist_sym[of x])
        qed
      qed
      thus "x \<in> M"
        using assms[simplified mtopology_closedin_iff] \<open>m \<in> UNIV \<rightarrow> M\<close>
        by simp
    qed
  qed
qed

text \<open> Oscillation\<close>
definition osc_on :: "['b set, 'b topology, 'b \<Rightarrow> 'a, 'b] \<Rightarrow> ennreal" where
"osc_on A X f \<equiv> (\<lambda>y. \<Sqinter> {diam (f ` (A \<inter> U)) |U. y \<in> U \<and> openin X U})"

abbreviation "osc X \<equiv> osc_on (topspace X) X"

lemma osc_def: "osc X f = (\<lambda>y. \<Sqinter> {diam (f ` U) |U. y \<in> U \<and> openin X U})"
  by(standard,auto simp: osc_on_def) (metis (no_types, opaque_lifting) inf.absorb2 openin_subset)

lemma osc_on_less_iff:
 "osc_on A X f x < t \<longleftrightarrow> (\<exists>v. x \<in> v \<and> openin X v \<and> diam (f ` (A \<inter> v)) < t)"
  by(auto simp add: osc_on_def Inf_less_iff)

lemma osc_less_iff:
 "osc X f x < t \<longleftrightarrow> (\<exists>v. x \<in> v \<and> openin X v \<and> diam (f ` v) < t)"
  by(auto simp add: osc_def Inf_less_iff)

definition sequentially_compact :: bool where
"sequentially_compact \<longleftrightarrow> (\<forall>xn\<in>sequence. \<exists>a. strict_mono a \<and> convergent_inS (xn \<circ> a))"

definition eps_net_on :: "'a set \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> bool" where
"eps_net_on B \<epsilon> A \<longleftrightarrow> \<epsilon> > 0 \<and> finite A \<and> A \<subseteq> S \<and> B \<subseteq> (\<Union>a\<in>A. open_ball a \<epsilon>)"

abbreviation "eps_net \<equiv> eps_net_on S"

lemma eps_net_def: "eps_net \<epsilon> A \<longleftrightarrow> \<epsilon> > 0 \<and> finite A \<and> A \<subseteq> S \<and> S = \<Union> ((\<lambda>a. open_ball a \<epsilon>) ` A)"
  using open_ball_subset_ofS by(auto simp: eps_net_on_def)

lemma eps_net_onD:
  assumes "eps_net_on B e A"
  shows "e > 0" "finite A" "A \<subseteq> S" "B \<subseteq> (\<Union>a\<in>A. open_ball a e)" "B \<subseteq> S"
  using assms open_ball_subset_ofS by(auto simp: eps_net_on_def) blast

lemma eps_netD:
  assumes "eps_net \<epsilon> A"
  shows "\<epsilon> > 0" "finite A" "A \<subseteq> S" "S = \<Union> ((\<lambda>a. open_ball a \<epsilon>) ` A)"
  using assms by(auto simp: eps_net_def)

lemma eps_net_le:
  assumes "eps_net e A" "e \<le> e'"
  shows "eps_net e' A"
  using assms open_ball_le[OF assms(2)] open_ballD'(1)
  by(auto simp: eps_net_def) blast

definition totally_bounded_on :: "'a set \<Rightarrow> bool" where
"totally_bounded_on B \<longleftrightarrow> (\<forall>e>0. \<exists>A. eps_net_on B e A)"

abbreviation "totally_boundedS \<equiv> totally_bounded_on S"

lemma totally_boundedS_def: "totally_boundedS \<longleftrightarrow> (\<forall>e>0. \<exists>A. eps_net e A)"
  by(auto simp: totally_bounded_on_def)

lemma totally_bounded_onD_sub:
  assumes "totally_bounded_on B"
  shows "B \<subseteq> S"
  by (meson assms eps_net_onD(5) gt_ex totally_bounded_on_def)

lemma totally_bounded_onD:
  assumes "totally_bounded_on B" "e > 0"
  obtains A where "finite A" "A \<subseteq> S" "B \<subseteq> (\<Union>a\<in>A. open_ball a e)"
  by (metis assms that eps_net_on_def totally_bounded_on_def)

lemma totally_boundedSD:
  assumes totally_boundedS "e > 0"
  obtains A where "finite A" "A \<subseteq> S" "S = (\<Union>a\<in>A. open_ball a e)"
  by (metis assms that eps_net_def totally_boundedS_def)

lemma totally_bounded_on_iff:
"totally_bounded_on B \<longleftrightarrow> B \<subseteq> S \<and> (\<forall>xn\<in>(UNIV :: nat set) \<rightarrow> B. \<exists>a. strict_mono a \<and> Cauchy_inS (xn \<circ> a))"
proof safe
  fix xn :: "nat \<Rightarrow> 'a"
  assume h:"totally_bounded_on B" "xn \<in> UNIV \<rightarrow> B"
  then have h': "B \<subseteq> S"
    by (auto dest: totally_bounded_onD_sub)
  have 1: "\<exists>b::nat \<Rightarrow> nat. strict_mono b \<and> (\<forall>n m. dist (yn (b n)) (yn (b m)) < e)" if "yn \<in> UNIV \<rightarrow> B" "e > 0" for e yn
  proof -
    obtain A where A: "finite A" "A \<subseteq> S" "B \<subseteq> (\<Union>a\<in>A. open_ball a (e/2))"
      using totally_bounded_onD[OF h(1) half_gt_zero[OF \<open>e > 0\<close>]] by metis
    have "\<not> (\<forall>a\<in>A. finite {n. yn n \<in> open_ball a (e/2)})"
    proof
      assume "\<forall>a\<in>A. finite {n. yn n \<in> open_ball a (e/2)}"
      then have "finite (\<Union>a\<in>A. {n. yn n \<in> open_ball a (e/2)})"
        using A by auto
      moreover have "UNIV = (\<Union>a\<in>A. {n. yn n \<in> open_ball a (e/2)})"
        using that(1) A(3) by auto
      ultimately show False by simp
    qed
    then obtain a where a:"a \<in> A" "infinite {n. yn n \<in> open_ball a (e/2)}"
      by auto
    then obtain b where b:"strict_mono b" "\<And>n::nat. yn (b n) \<in> open_ball a (e/2)"
      using obtain_subsequence[of "\<lambda>_ ynn. ynn \<in> open_ball a (e/2)" yn] by auto
    show ?thesis
      using a A by(auto intro!: exI[where x=b] b order.strict_trans1[OF dist_tr[OF open_ballD'(1)[OF b(2)] _ open_ballD'(1)[OF b(2)],of a] add_strict_mono[OF open_ballD[OF b(2),simplified dist_sym[of a]] open_ballD[OF b(2)]],simplified])
  qed

  define anm where "anm \<equiv> rec_nat (xn \<circ> (SOME b::nat \<Rightarrow> nat. strict_mono b \<and> (\<forall>n m. dist (xn (b n)) (xn (b m)) < 1))) (\<lambda>n an. an \<circ> (SOME b. strict_mono b \<and> (\<forall>l k. dist (an (b l)) (an (b k)) < 1 / Suc (Suc n))))"
  have anm_Suc:"anm (Suc n) = anm n \<circ> (SOME b. strict_mono b \<and> (\<forall>l k. dist (anm n (b l)) (anm n (b k)) < 1 / Suc (Suc n)))" for n
    by(simp add: anm_def)
  have anm1:"anm n \<in> UNIV \<rightarrow> B \<and> (\<forall>l k. dist (anm n l) (anm n k) < 1 / Suc n)" for n
  proof(induction n)
    case 0
    obtain b ::"nat \<Rightarrow> nat" where b:"strict_mono b" "\<forall>l k. dist (xn (b l)) (xn (b k)) < 1"
      using 1[OF h(2),of 1] by auto
    show ?case
      by(simp add: anm_def,rule someI2[where a=b]) (use b h(2) in auto)
  next
    case ih:(Suc n')
    obtain b ::"nat \<Rightarrow> nat" where b:"strict_mono b" "\<forall>l k. dist (anm n' (b l)) (anm n' (b k)) < 1 / real (Suc (Suc n'))"
      using 1[of "anm n'" "1 / Suc (Suc n')"] ih by auto 
    show ?case
      by(simp only: anm_Suc,rule someI2[where a=b]) (use ih b in auto)
  qed

  define bnm :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "bnm \<equiv> rec_nat (SOME b. strict_mono b \<and> anm 0 = xn \<circ> b) (\<lambda>n bn. SOME b. strict_mono b \<and> anm (Suc n) = anm n \<circ> b)"
  have bnm_Suc:"bnm (Suc n) = (SOME b. strict_mono b \<and> anm (Suc n) = anm n \<circ> b)" for n
    by(simp add: bnm_def)
  have bnm0:"strict_mono (bnm 0) \<and> anm 0 = xn \<circ> (bnm 0)"
  proof -
    have b0:"\<exists>b::nat \<Rightarrow> nat. strict_mono b \<and> anm 0 = xn \<circ> b"
    proof -
      obtain b ::"nat \<Rightarrow> nat" where b:"strict_mono b" "\<forall>l k. dist (xn (b l)) (xn (b k)) < 1"
        using 1[OF h(2),of 1] by auto
      show ?thesis
        by(simp add: anm_def,rule someI2[where a=b],auto simp: b)
    qed
    thus ?thesis
      unfolding bnm_def by(simp,rule someI_ex)
  qed
  have bnm_S: "strict_mono (bnm (Suc n)) \<and> anm (Suc n) = anm n \<circ> (bnm (Suc n))" for n
  proof -
    have bn:"\<exists>b::nat \<Rightarrow> nat. strict_mono b \<and> anm (Suc m) = anm m \<circ> b" for m
    proof -
      obtain b ::"nat \<Rightarrow> nat" where b:"strict_mono b" "\<forall>l k. dist (anm m (b l)) (anm m (b k)) < 1 / real (Suc (Suc m))"
        using 1[of "anm m" "1 / Suc (Suc m)"] anm1 by auto
      show ?thesis
        by(simp only: anm_Suc,rule someI2[where a=b]) (auto simp: b[simplified])
    qed
    thus ?thesis
      by(simp add: bnm_Suc, rule someI_ex)
  qed
  define bnm_r where "bnm_r \<equiv> rec_nat (bnm 0) (\<lambda>n bn. bn \<circ> (bnm (Suc n)))"
  have bnm_r_Suc: "bnm_r (Suc n) = bnm_r n \<circ> (bnm (Suc n))" for n
    by(simp add: bnm_r_def)
  have anm_bnm_r:"anm n = xn \<circ> (bnm_r n)" for n
    by(induction n,simp add: bnm0 bnm_r_def) (auto simp: bnm_S bnm_r_Suc)
  have bnm_r_sm:"strict_mono (bnm_r n)" for n
    by(induction n, simp add: bnm0 bnm_r_def) (insert bnm_S, auto simp: bnm_r_Suc strict_mono_def)
  have bnm_r_Suc_le:"bnm_r n l \<le> bnm_r (Suc n) l" for l n
    using bnm_S bnm_r_sm by(auto simp: bnm_r_Suc strict_mono_imp_increasing strict_mono_leD)
  have sm:"strict_mono (\<lambda>n. bnm_r n n)"
    by(auto simp add: strict_mono_Suc_iff) (meson lessI order_le_less_trans strict_monoD bnm_r_sm bnm_r_Suc_le)
  have bnm_r_de:"\<exists>l. bnm_r (n + k) = bnm_r n \<circ> l" for n k
    by(induction k) (auto simp: bnm_r_Suc)
  show "\<exists>a::nat \<Rightarrow> nat. strict_mono a \<and> Cauchy_inS (xn \<circ> a)"
    unfolding Cauchy_inS_def
  proof(safe intro!: exI[where x="\<lambda>n. bnm_r n n"] sm)
    fix e :: real
    assume "e > 0"
    then obtain N where N:"1 / Suc N < e"
      using nat_approx_posE by blast
    show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist ((xn \<circ> (\<lambda>n. bnm_r n n)) n) ((xn \<circ> (\<lambda>n. bnm_r n n)) m) < e"
    proof(safe intro!: exI[where x=N])
      fix n m
      assume "N \<le> n" "N \<le> m"
      then have "n = N + (n - N)" "m = N + (m - N)" by auto
      then obtain l1 l2 where l:"bnm_r n = bnm_r N \<circ> l1" "bnm_r m = bnm_r N \<circ> l2"
        by (metis bnm_r_de)  
      have "dist (xn (bnm_r n n)) (xn (bnm_r m m)) = dist (anm N (l1 n)) (anm N (l2 m))"
        by(simp add: l anm_bnm_r)
      also have "... < 1 / Suc N"
        using anm1 by auto
      finally show "dist ((xn \<circ> (\<lambda>n. bnm_r n n)) n) ((xn \<circ> (\<lambda>n. bnm_r n n)) m) < e"
        using N by simp
    qed
  qed(use h h' in auto)
next
  assume h:"\<forall>xn\<in>(UNIV :: nat set) \<rightarrow> B. \<exists>a. strict_mono a \<and> Cauchy_inS (xn \<circ> a)" "B \<subseteq> S"
  show "totally_bounded_on B"
  proof(rule ccontr)
    assume "\<not> totally_bounded_on B"
    then obtain e where e:"e > 0" "\<And>A. \<not> eps_net_on B e A"
      by(auto simp: totally_bounded_on_def)
    have A:"\<not> B \<subseteq> (\<Union>a\<in>A. open_ball a e)" if "finite A" for A
    proof -
      have [simp]:"(\<Union>a\<in>A. open_ball a e) = (\<Union>a\<in>A\<inter> S. open_ball a e)"
        using Collect_cong IntD1 IntI Sup_set_def UN_iff open_ballD'(2) by auto
      have "finite (A \<inter> S)" using that by auto
      thus ?thesis
        using e by(auto simp: eps_net_on_def)
    qed
    obtain a0 where a0:"a0 \<in> B"
      using A by fastforce
    define xnl where "xnl \<equiv> rec_nat [a0] (\<lambda>n ln. (SOME x. x \<in> B \<and> x \<notin> (\<Union>a\<in>set ln. open_ball a e)) # ln)"
    have xnl_Suc:"xnl (Suc n) = (SOME x. x \<in> B \<and> x \<notin> (\<Union>a\<in>set (xnl n). open_ball a e)) # xnl n" for n
      by(simp add: xnl_def)
    define xn where "xn = (\<lambda>n. (xnl n) ! 0)"
    have xn:"xn (Suc n) \<in> B \<and> xn (Suc n) \<notin> (\<Union>a\<in>set (xnl n). open_ball a e)" for n
    proof -
      have "\<exists>y. y \<in> B \<and> (\<forall>x\<in>set (xnl n). y \<notin> open_ball x e)"
        using A[OF finite_set] by fastforce
      thus ?thesis
        by(simp add: xn_def xnl_Suc,rule someI_ex)
    qed
    have xn0:"xn 0 \<in> B"
      by(auto simp: xnl_def xn_def a0)
    with xn have xns:"xn \<in> UNIV \<rightarrow> B"
      by auto (metis old.nat.exhaust)
    have xnll:"length (xnl n) = Suc n" for n
      by(induction n) (simp add: xnl_def, auto simp: xnl_Suc)
    have xnin:"xn m \<in> set (xnl (m + k))" for m k
      by(induction k) (auto simp: xn_def xnl_Suc xnll intro!: nth_mem)
    obtain a where a:"strict_mono a" "Cauchy_inS (xn \<circ> a)"
      using h xns by auto
    then obtain N where "\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> dist (xn (a n)) (xn (a m)) < e"
      using e Cauchy_inS_def by fastforce
    hence e1:"dist (xn (a N)) (xn (a (Suc N))) < e"
      by auto
    have "xn (a (Suc N)) \<notin> (\<Union>a\<in>set (xnl (a (Suc N) - 1)). open_ball a e)"
      by (metis a(1) diff_Suc_1 le_0_eq not0_implies_Suc strict_mono_less_eq xn zero_le)
    moreover have "xn (a N) \<in> set (xnl (a (Suc N) - 1))"
      using a(1)[simplified strict_mono_Suc_iff] xnin[of "a N" "a (Suc N) - a N - 1"]
      by (simp add: Suc_leI)
    ultimately have "xn (a (Suc N)) \<notin> open_ball (xn (a N)) e"
      by auto
    from open_ball_nin_le[OF _ e(1) _ this] xns e1 h(2)
    show False by auto
  qed
qed(auto dest: totally_bounded_onD_sub)

corollary totally_boundedS_iff: "totally_boundedS \<longleftrightarrow> (\<forall>xn\<in>sequence. \<exists>a. strict_mono a \<and> Cauchy_inS (xn \<circ> a))"
  by(auto simp: totally_bounded_on_iff)

text \<open> Metric embedding\<close>
definition embed_dist_on :: "['b set, 'b \<Rightarrow> 'a, 'b, 'b] \<Rightarrow> real" where
"embed_dist_on B f a b \<equiv> (if a \<in> B \<and> b \<in> B then dist (f a) (f b) else 0)"

context
  fixes f B
  assumes f: "f \<in> B \<rightarrow> S" "inj_on f B"
begin

abbreviation "ed \<equiv> embed_dist_on B f"

lemma embed_dist_dist: "metric_set B (embed_dist_on B f)"
proof
  fix x y
  assume "x \<in> B" "y \<in> B"
  then show "x = y \<longleftrightarrow> embed_dist_on B f x y = 0"
    using inj_onD[OF f(2)] dist_0[of "f x" "f y"] f(1)
    by(auto simp: embed_dist_on_def)
next
  fix x y
  show "embed_dist_on B f x y = embed_dist_on B f y x"
    by(simp add: embed_dist_on_def dist_sym[of "f x" "f y"])
next
  fix x y z
  assume "x \<in> B" "y \<in> B" "z \<in> B"
  then show "embed_dist_on B f x z \<le> embed_dist_on B f x y + embed_dist_on B f y z"
    using dist_tr[of "f x" "f y" "f z"] f(1) by(auto simp: embed_dist_on_def)
qed(simp_all add: embed_dist_on_def  dist_geq0)

interpretation ed : metric_set B ed
  by(rule embed_dist_dist)

lemma embed_dist_open_ball: 
  assumes "a \<in> B"
  shows"f ` (ed.open_ball a e) = open_ball (f a) e \<inter> f ` B"
  using assms f by(auto simp: ed.open_ball_def open_ball_def embed_dist_on_def)

lemma embed_dist_closed_ball:
  assumes "a \<in> B"
  shows"f ` (ed.closed_ball a e) = closed_ball (f a) e \<inter> f ` B"
  using assms f by(auto simp: ed.closed_ball_def closed_ball_def embed_dist_on_def)

lemma embed_dist_topology_homeomorphic_maps:
  assumes g1:"\<And>x. x \<in> B \<Longrightarrow> g (f x) = x"
  shows "homeomorphic_maps ed.mtopology (subtopology mtopology (f ` B)) f g"
proof -
  have g2: "\<And>x. x \<in> f ` B \<Longrightarrow> f (g x) = x" "g \<in> (f ` B) \<rightarrow> B"
    by(auto simp: g1)
  show ?thesis
    unfolding homeomorphic_maps_def mtopology_topspace ed.mtopology_topspace
  proof safe
    show "continuous_map ed.mtopology (subtopology mtopology (f ` B)) f"
      unfolding mtopology_def2 subtopology_generated_by
    proof(rule continuous_on_generated_topo)
      show "\<And>U. U \<in> {f ` B \<inter> U |U. U \<in> {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}} \<Longrightarrow> openin ed.mtopology (f -` U \<inter> topspace ed.mtopology)"
        unfolding ed.mtopology_topspace
      proof safe
        fix a and e :: real
        assume h:"a \<in> S" "0 < e"
        have 1:"(f -` (f ` B \<inter> open_ball a e) \<inter> B) = f -` open_ball a e \<inter> B" by blast
        show "openin ed.mtopology (f -` (f ` B \<inter> open_ball a e) \<inter> B)"
          unfolding 1 ed.mtopology_openin_iff
        proof safe
          fix x
          assume h':"x \<in> B" "f x \<in> open_ball a e"
          then obtain e' where e':"e' > 0" "open_ball (f x) e' \<subseteq> open_ball a e"
            using mtopology_open_ball_in' by blast
          show "\<exists>\<epsilon>>0. ed.open_ball x \<epsilon> \<subseteq> f -` open_ball a e \<inter> B"
          proof(safe intro!: exI[where x=e'])
            fix y
            assume "y \<in> ed.open_ball x e'"
            with e'(2) show "y \<in> f -` open_ball a e"
              using embed_dist_open_ball[OF h'(1),of e'] by blast
          qed(use e' ed.open_ball_subset_ofS in auto)
        qed
      qed
    next
      show "f ` topspace ed.mtopology \<subseteq> \<Union> {f ` B \<inter> U |U. U \<in> {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}} "
        by(auto simp: ed.mtopology_topspace) (metis (mono_tags, opaque_lifting) IntE IntI closed_ball_def ed.closed_ball_ina ed.dist_set_geq0 ed.dist_set_inA embed_dist_closed_ball ennreal_le_epsilon ennreal_zero_less_top image_eqI le_zero_eq not_gr_zero open_ballD'(2) open_ball_ina open_ball_le_0)
    qed
  next
    show "continuous_map (subtopology mtopology (f ` B)) ed.mtopology g"
      unfolding ed.mtopology_def2
    proof(rule continuous_on_generated_topo)
      show "\<And>U. U \<in> {ed.open_ball a \<epsilon> |a \<epsilon>. a \<in> B \<and> 0 < \<epsilon>} \<Longrightarrow> openin (subtopology mtopology (f ` B)) (g -` U \<inter> topspace (subtopology mtopology (f ` B)))"
      proof safe
        fix a and e :: real
        assume h: "a \<in> B" "0 < e"
        then have 1: "g -` ed.open_ball a e \<inter> (S \<inter> f ` B) = open_ball (f a) e \<inter> f ` B"
          using f(1) g1 g2 by(auto simp: ed.open_ball_def open_ball_def embed_dist_on_def)
        show "openin (subtopology mtopology (f ` B)) (g -` ed.open_ball a e \<inter> (topspace (subtopology mtopology (f ` B))))"
          by(auto simp: 1 openin_subtopology openin_open_ball mtopology_topspace intro!: exI[where x="open_ball (f a) e"])
      qed
      show "g ` topspace (subtopology mtopology (f ` B)) \<subseteq> \<Union> {ed.open_ball a \<epsilon> |a \<epsilon>. a \<in> B \<and> 0 < \<epsilon>}"
        by(auto simp: mtopology_topspace) (metis ed.mtopology_openin_iff ed.open_ball_ina ed.openin_S g1)
    qed
  qed(use g1 g2 in auto)
qed

lemma embed_dist_topology_homeomorphic_map:
 "homeomorphic_map ed.mtopology (subtopology mtopology (f ` B)) f"
proof -
  define g where "g \<equiv> (\<lambda>y. THE x. x \<in> B \<and> f x = y)"
  have g1: "g (f b) = b" if "b \<in> B" for b
    unfolding g_def by(rule theI2[of _ b]) (insert that f(2), auto simp: inj_on_def)
  thus ?thesis
    using embed_dist_topology_homeomorphic_maps homeomorphic_map_maps by blast
qed

corollary embed_dist_topology_homeomorphic:
 "ed.mtopology homeomorphic_space (subtopology mtopology (f ` B))"
  using embed_dist_topology_homeomorphic_map
  by(rule homeomorphic_map_imp_homeomorphic_space)

corollary embed_dist_topology_homeomorphic_map':
  assumes "f ` B = S"
  shows "homeomorphic_map ed.mtopology mtopology f"
  using embed_dist_topology_homeomorphic_map[simplified assms]
  by(simp add:subtopology_topspace[of mtopology, simplified mtopology_topspace])

corollary embed_dist_topology_homeomorphic':
  assumes "f ` B = S"
  shows "ed.mtopology homeomorphic_space mtopology"
  using embed_dist_topology_homeomorphic_map'[OF assms]
  by(rule homeomorphic_map_imp_homeomorphic_space)

lemma embed_dist_converge_to_inS_iff:
 "ed.converge_to_inS xn x \<longleftrightarrow> xn \<in> ed.sequence \<and> x \<in> B \<and> converge_to_inS (\<lambda>n. f (xn n)) (f x)"
proof safe
  assume h:"ed.converge_to_inS xn x"
  then show h':"x \<in> B" "\<And>n. xn n \<in> B"
    by(auto simp: ed.converge_to_inS_def)
  thus "converge_to_inS (\<lambda>n. f (xn n)) (f x)"
    using h f by(auto simp: converge_to_inS_def2 ed.converge_to_inS_def2 embed_dist_on_def)
next
  assume h:"xn \<in> ed.sequence" "x \<in> B" "converge_to_inS (\<lambda>n. f (xn n)) (f x)"
  show "ed.converge_to_inS xn x"
    using h f by(fastforce simp: ed.converge_to_inS_def2 h embed_dist_on_def converge_to_inS_def2)
qed

lemma embed_dist_convergent_inS_iff:
  assumes "closedin mtopology (f ` B)"
  shows "ed.convergent_inS xn \<longleftrightarrow> xn \<in> ed.sequence \<and> convergent_inS (\<lambda>n. f (xn n))"
proof -
  {
    fix s
    assume h:"xn \<in> ed.sequence" "converge_to_inS (\<lambda>n. f (xn n)) s"
    with f have "(\<lambda>n. f (xn n)) \<in> UNIV \<rightarrow> f ` B" by auto
    hence "s \<in> f ` B"
      using assms h(2) by(auto simp: mtopology_closedin_iff)
    hence "\<exists>b \<in> B. s = f b" by auto
  }
  thus ?thesis
    using embed_dist_converge_to_inS_iff[of xn] f(1)
    by(fastforce simp: ed.convergent_inS_def convergent_inS_def)
qed

lemma embed_dist_Cauchy_inS_iff:
 "ed.Cauchy_inS xn \<longleftrightarrow> xn \<in> ed.sequence \<and> Cauchy_inS (\<lambda>n. f (xn n))"
  using f(1) by(auto simp: ed.Cauchy_inS_def Cauchy_inS_def embed_dist_on_def; meson PiE UNIV_I)

end

end

text \<open> Relations to elementary topology. \<close>
lemma ball_def_set: "ball a \<epsilon> = metric_set.open_ball UNIV dist a \<epsilon>"
  using metric_set.open_ball_def metric_class_metric_set
  by fastforce

lemma converge_to_def_set:
  fixes xn :: "nat \<Rightarrow> ('a::metric_space)"
  shows "xn \<longlonglongrightarrow> x \<longleftrightarrow> metric_set.converge_to_inS UNIV dist xn x"
proof -
  interpret m: metric_set UNIV dist
    by simp
  show ?thesis
    by(simp add: lim_sequentially m.converge_to_inS_def)
qed

lemma the_limit_of_limit:
  fixes xn :: "nat \<Rightarrow> ('a::metric_space)"
  shows "metric_set.the_limit_of UNIV dist xn = lim xn"
  by(simp add: metric_set.the_limit_of_def lim_def converge_to_def_set)

lemma convergent_def_set:
  fixes f :: "nat \<Rightarrow> ('a::metric_space)"
  shows "convergent f \<longleftrightarrow> metric_set.convergent_inS UNIV dist f"
proof -
  interpret m: metric_set UNIV dist
    by(rule metric_class_metric_set)
  show "convergent f \<longleftrightarrow> m.convergent_inS f"
    using converge_to_def_set[of f]
    by(auto simp: convergent_def m.convergent_inS_def)
qed

lemma Cahuchy_def_set: "Cauchy f \<longleftrightarrow> metric_set.Cauchy_inS UNIV dist f"
proof -
  interpret m: metric_set UNIV dist
    by(rule metric_class_metric_set)
  show "Cauchy f = m.Cauchy_inS f"
    by(simp add: Cauchy_def m.Cauchy_inS_def dist_real_def)
qed

lemma open_openin_set: "open U \<longleftrightarrow> openin (metric_set.mtopology UNIV dist) U"
 (is "?LHS \<longleftrightarrow> ?RHS")
proof -
  interpret m: metric_set UNIV dist
    by(rule metric_class_metric_set)
  have "?LHS \<longleftrightarrow> (\<forall>x\<in>U. \<exists>e>0. ball x e \<subseteq> U)"
    by(simp add: open_contains_ball)
  also have "... \<longleftrightarrow> (\<forall>x\<in>U. \<exists>e>0. m.open_ball x e \<subseteq> U)"
    by(simp add: ball_def_set)
  also have "... \<longleftrightarrow> ?RHS"
    by(simp add: m.mtopology_openin_iff[of U])
  finally show ?thesis .
qed

lemma topological_basis_set: "topological_basis \<O> \<longleftrightarrow> metric_set.mtopology_basis UNIV dist \<O>"
  (is "?LHS = ?RHS")
proof -
  interpret m: metric_set UNIV dist
    by(rule metric_class_metric_set)
  have "?LHS \<longleftrightarrow> (\<forall>b\<in>\<O>. open b) \<and> (\<forall>x. open x \<longrightarrow> (\<exists>B'\<subseteq>\<O>. \<Union> B' = x))"
    by(simp add: topological_basis_def)
  also have "... \<longleftrightarrow> (\<forall>b\<in>\<O>. openin m.mtopology b) \<and> (\<forall>x. openin m.mtopology x \<longrightarrow> (\<exists>B'\<subseteq>\<O>. \<Union> B' = x))"
    by(simp add: open_openin_set)
  also have "... \<longleftrightarrow> ?RHS"
    by(simp add: base_of_def2')
  finally show ?thesis .
qed

lemma euclidean_mtopology: "metric_set.mtopology UNIV dist = euclidean"
  using open_openin open_openin_set topology_eq by blast

text \<open> Distances generate the same topological space.\<close>
lemma metric_generates_same_topology:
  assumes "metric_set S d" "metric_set S d'"
          "\<And>x U. U \<subseteq> S \<Longrightarrow> (\<forall>y\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball S d y \<epsilon> \<subseteq> U) \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>\<epsilon>>0. metric_set.open_ball S d' x \<epsilon> \<subseteq> U"
      and "\<And>x U. U \<subseteq> S \<Longrightarrow> (\<forall>y\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball S d' y \<epsilon> \<subseteq> U) \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>\<epsilon>>0. metric_set.open_ball S d x \<epsilon> \<subseteq> U"
    shows "metric_set.mtopology S d = metric_set.mtopology S d'"
proof -
  interpret m1: metric_set S d by fact
  interpret m2: metric_set S d' by fact
  have "(\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. m1.open_ball x \<epsilon> \<subseteq> U)) = (\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. m2.open_ball x \<epsilon> \<subseteq> U))"
    by standard (use assms(3,4) in auto)
  thus ?thesis
    using topology.topology_inject m1.mtopology_istopology m2.mtopology_istopology
    by(simp add: m2.mtopology_def m1.mtopology_def)
qed

lemma metric_generates_same_topology_inverse:
  assumes "metric_set S d" "metric_set S d'"
      and "metric_set.mtopology S d = metric_set.mtopology S d'"
    shows "U \<subseteq> S \<Longrightarrow> (\<forall>y\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball S d y \<epsilon> \<subseteq> U) \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>\<epsilon>>0. metric_set.open_ball S d' x \<epsilon> \<subseteq> U"
      and "U \<subseteq> S \<Longrightarrow> (\<forall>y\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball S d' y \<epsilon> \<subseteq> U) \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>\<epsilon>>0. metric_set.open_ball S d x \<epsilon> \<subseteq> U"
proof -
  interpret m1: metric_set S d by fact
  interpret m2: metric_set S d' by fact
  have "(\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. m1.open_ball x \<epsilon> \<subseteq> U)) = (\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. m2.open_ball x \<epsilon> \<subseteq> U))"
    using topology.topology_inject[of "\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. m1.open_ball x \<epsilon> \<subseteq> U)" "\<lambda>U. U \<subseteq> S \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. m2.open_ball x \<epsilon> \<subseteq> U)"] m1.mtopology_istopology m2.mtopology_istopology assms(3)
    by(auto simp: m2.mtopology_def m1.mtopology_def)
  thus "U \<subseteq> S \<Longrightarrow> \<forall>y\<in>U. \<exists>\<epsilon>>0. m1.open_ball y \<epsilon> \<subseteq> U \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>\<epsilon>>0. m2.open_ball x \<epsilon> \<subseteq> U"
       "U \<subseteq> S \<Longrightarrow> \<forall>y\<in>U. \<exists>\<epsilon>>0. m2.open_ball y \<epsilon> \<subseteq> U \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>\<epsilon>>0. m1.open_ball x \<epsilon> \<subseteq> U"
    by(auto dest: fun_cong[where x=U])
qed

lemma metric_generates_same_topology_converges':
  assumes "metric_set S d" "metric_set S d'"
          "metric_set.mtopology S d = metric_set.mtopology S d'"
      and "metric_set.converge_to_inS S d f x"
    shows "metric_set.converge_to_inS S d' f x"
proof -
  interpret m1: metric_set S d by fact
  interpret m2: metric_set S d' by fact
  show ?thesis
    unfolding m2.converge_to_inS_def2'
  proof safe
    fix \<epsilon> :: real
    assume h:"0 < \<epsilon>"
    obtain \<epsilon>' where he:
    "\<epsilon>'>0" "m1.open_ball x \<epsilon>' \<subseteq> m2.open_ball x \<epsilon>"
      using m2.mtopology_open_ball_in'[of _ x]  assms(4)[simplified m1.converge_to_inS_def2'] metric_generates_same_topology_inverse(2)[OF assms(1-3) m2.open_ball_subset_ofS, of x \<epsilon>,OF _ m2.open_ball_ina[OF _ h,of x]]
      by auto
    then obtain N where hn:
    "\<forall>n\<ge>N. f n \<in> m1.open_ball x \<epsilon>'"
      using assms(4)[simplified m1.converge_to_inS_def2'] by auto
    show "\<exists>N. \<forall>n\<ge>N. f n \<in> m2.open_ball x \<epsilon>"
      using hn he(2) by(auto intro!: exI[where x=N])
  next
    show "\<And>x. f x \<in> S" "x \<in> S"
      using assms(4)[simplified m1.converge_to_inS_def2'] by auto
  qed
qed

lemma metric_generates_same_topology_converges:
  assumes "metric_set S d" "metric_set S d'"
      and "metric_set.mtopology S d = metric_set.mtopology S d'"
    shows "metric_set.converge_to_inS S d f x \<longleftrightarrow> metric_set.converge_to_inS S d' f x"
  using metric_generates_same_topology_converges'[OF assms(2,1) assms(3)[symmetric]] metric_generates_same_topology_converges'[OF assms(1-3)]
  by auto

lemma metric_generates_same_topology_convergent:
  assumes "metric_set S d" "metric_set S d'"
      and "metric_set.mtopology S d = metric_set.mtopology S d'"
    shows "metric_set.convergent_inS S d f \<longleftrightarrow> metric_set.convergent_inS S d' f"
  using metric_generates_same_topology_converges[OF assms,of f]
  by (simp add: assms(1) assms(2) metric_set.convergent_inS_def)

subsubsection \<open> Sub-Metric Spaces\<close>
definition submetric :: "['a set, 'a \<Rightarrow> 'a \<Rightarrow> real] \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
"submetric S' d \<equiv> (\<lambda>x y. if x \<in> S' \<and> y \<in> S' then d x y else 0)"

lemma(in metric_set) submetric_metric_set:
  assumes "S' \<subseteq> S"
  shows "metric_set S' (submetric S' dist)"
proof
  show "\<And>x y. 0 \<le> submetric S' dist x y"
       "\<And>x y. x \<notin> S' \<Longrightarrow> submetric S' dist x y = 0"
       "\<And>x y. x \<in> S' \<Longrightarrow> y \<in> S' \<Longrightarrow> (x = y) = (submetric S' dist x y = 0)"
       "\<And>x y. submetric S' dist x y = submetric S' dist y x" 
    using assms dist_geq0 dist_tr dist_0 dist_sym
    by(fastforce simp: submetric_def)+
next
  show "\<And>x y z. x \<in> S' \<Longrightarrow> y \<in> S' \<Longrightarrow> z \<in> S' \<Longrightarrow> submetric S' dist x z \<le> submetric S' dist x y + submetric S' dist y z"
    by (metis assms dist_tr submetric_def subset_iff)
qed

lemma(in metric_set) submetric_open_ball:
  assumes "S' \<subseteq> S" and "a \<in> S'"
  shows "open_ball a \<epsilon> \<inter> S' = metric_set.open_ball S' (submetric S' dist) a \<epsilon>"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms(1)])
  show ?thesis
    using assms by(auto simp: open_ball_def m.open_ball_def,simp_all add: submetric_def)
qed

lemma(in metric_set) submetric_open_ball_subset:
  assumes "S' \<subseteq> S"
  shows "metric_set.open_ball S' (submetric S' dist) a \<epsilon> \<subseteq> open_ball a \<epsilon>"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms(1)])
  show ?thesis
    by (metis assms empty_subsetI inf_commute inf_sup_ord(2) m.open_ball_nin submetric_open_ball)
qed

lemma(in metric_set) submetric_subtopology:
  assumes "S' \<subseteq> S"
  shows "subtopology mtopology S' = metric_set.mtopology S' (submetric S' dist)"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms(1)])
  show ?thesis
    unfolding topology_eq
  proof safe
    fix U
    assume "openin (subtopology mtopology S') U"
    then obtain T where ht: "openin mtopology T" "U = T \<inter> S'"
      by(auto simp: openin_subtopology)
    have "U \<subseteq> S'"
      by (simp add: ht(2))
    show "openin m.mtopology U"
      unfolding m.mtopology_openin_iff
    proof safe
      fix x
      assume "x \<in> U"
      then obtain \<epsilon> where he: "\<epsilon> > 0" "open_ball x \<epsilon> \<subseteq> T"
        using ht by(auto simp: mtopology_openin_iff)
      thus "\<exists>\<epsilon>>0. m.open_ball x \<epsilon> \<subseteq> U"
        using ht(2) \<open>x \<in> U\<close> submetric_open_ball[OF assms(1),of x \<epsilon>]
        by(auto intro!: exI[where x=\<epsilon>])
    qed(use \<open>U \<subseteq> S'\<close> in auto)
  next
    fix U
    assume "openin m.mtopology U"
    then have "\<forall>x\<in>U. \<exists>\<epsilon>>0. m.open_ball x \<epsilon> \<subseteq> U"
      by(simp add: m.mtopology_openin_iff)
    then obtain \<epsilon> where he:
     "\<And>x. x \<in> U \<Longrightarrow> \<epsilon> x > 0" "\<And>x. x \<in> U \<Longrightarrow> m.open_ball x (\<epsilon> x) \<subseteq> U"
      by metis
    have "U \<subseteq> S'"
      using \<open>openin m.mtopology U\<close> m.mtopology_openin_iff by auto

    show "openin (subtopology mtopology S') U"
      unfolding openin_subtopology
    proof(intro exI[where x="\<Union> { open_ball x (\<epsilon> x) | x. x\<in>U}"] conjI)
      show "openin mtopology (\<Union> { open_ball x (\<epsilon> x) | x. x\<in>U})"
        by(rule openin_Union) (use he(1) open_ball_def mtopology_open_ball_in in fastforce)
    next
      have *:"U = (\<Union> { m.open_ball x (\<epsilon> x) | x. x\<in>U})"
        using he m.open_ball_ina \<open>U \<subseteq> S'\<close> by fastforce
      also have "... = (\<Union> { open_ball x (\<epsilon> x)  \<inter> S' | x. x\<in>U})"
        using submetric_open_ball[OF assms(1)] \<open>U \<subseteq> S'\<close> by auto
      also have "... = (\<Union> { open_ball x (\<epsilon> x) | x. x\<in>U}) \<inter> S'"
        by auto
      finally show "U = \<Union> {open_ball x (\<epsilon> x) |x. x \<in> U} \<inter> S' " .
    qed
  qed
qed

lemma(in metric_set) converge_to_insub_converge_to_inS:
  assumes "S' \<subseteq> S" and "metric_set.converge_to_inS S' (submetric S' dist) f x"
  shows "converge_to_inS f x"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms(1)])
  have *:"f \<in> m.sequence" "x \<in> S'"
    using assms(2) by(auto simp: m.converge_to_inS_def)
  show ?thesis
    unfolding converge_to_inS_def2 using * assms[simplified  m.converge_to_inS_def2]
    by(auto simp: submetric_def funcset_mem)
qed

lemma(in metric_set) convergent_insub_convergent_inS:
  assumes "S' \<subseteq> S" and "metric_set.convergent_inS S' (submetric S' dist) f"
  shows "convergent_inS f"
  by (meson assms(1) assms(2) converge_to_insub_converge_to_inS convergent_inS_def in_mono metric_set.convergent_inS_def submetric_metric_set)

lemma(in metric_set) Cauchy_insub_Cauchy:
  assumes "S' \<subseteq> S" and "metric_set.Cauchy_inS S' (submetric S' dist) f"
  shows "Cauchy_inS f"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms(1)])
  have *:"f \<in> m.sequence"
    using assms(2) by(auto simp: m.Cauchy_inS_def)
  show ?thesis
    unfolding Cauchy_inS_def using * assms[simplified m.Cauchy_inS_def]
    by(auto simp: submetric_def funcset_mem[OF *])
qed

lemma(in metric_set) Cauchy_insub_Cauchy_inverse:
  assumes "S' \<subseteq> S" "f \<in> UNIV \<rightarrow> S'" "Cauchy_inS f"
  shows "metric_set.Cauchy_inS S' (submetric S' dist) f"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms(1)])
  show ?thesis
    using assms by(auto simp: m.Cauchy_inS_def Cauchy_inS_def,simp add: submetric_def) metis
qed

lemma(in metric_set) convergent_insubmetric:
  assumes "S' \<subseteq> S" "f \<in> UNIV \<rightarrow> S'" "x \<in> S'" "converge_to_inS f x"
  shows "metric_set.converge_to_inS S' (submetric S' dist) f x"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms(1)])
  show ?thesis
    unfolding m.converge_to_inS_def using assms
    by(auto simp: converge_to_inS_def funcset_mem[OF assms(2)] submetric_def)
qed

lemma(in metric_set) the_limit_of_submetric_eq:
  assumes "S' \<subseteq> S" "metric_set.convergent_inS S' (submetric S' dist) f"
  shows "metric_set.the_limit_of S' (submetric S' dist) f = the_limit_of f"
  by (meson assms(1) assms(2) converge_to_insub_converge_to_inS convergent_insub_convergent_inS metric_set.converge_to_inS_unique metric_set.the_limit_if_converge metric_set_axioms submetric_metric_set)

lemma submetric_of_euclidean:
 "metric_set A (submetric A dist)" "metric_set.mtopology A (submetric A dist) = top_of_set A"
  using metric_set.submetric_metric_set[OF metric_class_metric_set,of A] metric_set.submetric_subtopology[OF metric_class_metric_set,of A]
  by(auto simp: euclidean_mtopology)

lemma(in metric_set)
  assumes "B \<subseteq> S"
  shows totally_bounded_on_submetric: "totally_bounded_on B \<longleftrightarrow> metric_set.totally_boundedS B (submetric B dist)"
proof -
  interpret m: metric_set B "submetric B dist"
    by(rule submetric_metric_set[OF assms(1)])
  show ?thesis
    unfolding totally_bounded_on_def m.totally_boundedS_def
  proof safe
    fix e :: real
    assume h:"\<forall>e>0. \<exists>A. eps_net_on B e A" "e > 0"
    then obtain A where A:"eps_net_on B (e / 2) A"
      by fastforce
    define A' where "A' \<equiv> A \<inter> {z.  open_ball z (e / 2) \<inter> B \<noteq> {}}"
    have A': "eps_net_on B (e / 2) A'"
      unfolding eps_net_on_def
    proof safe
      fix x
      assume x:"x \<in> B"
      then obtain a where a:"a \<in> A" "x \<in> open_ball a (e / 2)"
        using A by(auto dest: eps_net_onD)
      with x have "a \<in> A'"
        by(auto simp: A'_def)
      with a show "x \<in> (\<Union>a\<in>A'. open_ball a (e / 2))" by auto
    qed(use h eps_net_on_def A'_def A in auto)
    define b where "b \<equiv> (\<lambda>a. SOME b. b \<in> B \<and> b \<in> open_ball a (e / 2))"
    have b:"b a \<in> B" "b a \<in> open_ball a (e / 2)" if a: "a \<in> A'" for a
    proof -
      have "b a \<in> B \<and> b a \<in> open_ball a (e / 2)"
        unfolding b_def by(rule someI_ex) (insert that, auto simp: A'_def)
      thus "b a \<in> B" "b a \<in> open_ball a (e / 2)" by auto
    qed
    show "\<exists>A. m.eps_net e A"
      unfolding m.eps_net_on_def
    proof(safe intro!: exI[where x="b ` A'"])
      fix x
      assume "x \<in> B"
      then obtain a where a: "a \<in> A'" "x \<in> open_ball a (e / 2)"
        using A' by(auto simp: eps_net_on_def)
      show "x \<in> (\<Union>a\<in>b ` A'. m.open_ball a e)"
      proof
        show "b a \<in> b ` A'"
          using a by auto
      next
        have [simp]: "b a \<in> S" "x \<in> S" "b a \<in> B" "x \<in> B" "a \<in> S"
          using b(1)[OF a(1)] assms \<open>x \<in> B\<close> a  A' by (auto simp: eps_net_on_def)
        note order.strict_trans1[OF dist_tr add_strict_mono[OF open_ballD[OF a(2),simplified dist_sym[of a]] open_ballD[OF b(2)[OF a(1)]]],simplified]
        hence "submetric B dist x (b a) < e"
          by(auto simp: submetric_def)
        thus "x \<in> m.open_ball (b a) e"
          by(auto simp: m.open_ball_def m.dist_sym)
      qed
    qed(insert h(2) A' b, auto simp: eps_net_on_def)
  next
    fix e :: real
    assume "\<forall>e>0. \<exists>A. m.eps_net e A" "e > 0"
    then obtain A where A: "m.eps_net e A" by auto
    thus "\<exists>A. eps_net_on B e A"
      using assms submetric_open_ball_subset[OF assms] by(auto intro!: exI[where x=A] simp: eps_net_on_def m.eps_net_def) blast
  qed
qed
    
text \<open> Continuous functions \<close>
context
  fixes S :: "'a set" and d
    and S':: "'b set" and d'
  assumes "metric_set S d" "metric_set S' d'"
begin

interpretation m1: metric_set S d by fact
interpretation m2: metric_set S' d' by fact

lemma metric_set_continuous_map_eq:
  shows "continuous_map m1.mtopology m2.mtopology f
         \<longleftrightarrow> f \<in> S \<rightarrow> S' \<and> (\<forall>x\<in>S. \<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y\<in>S. d x y < \<delta> \<longrightarrow> d' (f x) (f y) < \<epsilon>)"
proof safe
  show "\<And>x. continuous_map m1.mtopology m2.mtopology f \<Longrightarrow> x \<in> S \<Longrightarrow> f x \<in> S'"
    using m1.mtopology_topspace m2.mtopology_topspace by(auto dest: continuous_map_image_subset_topspace)
next
  fix x \<epsilon>
  assume "continuous_map m1.mtopology m2.mtopology f"
           "x \<in> S" "(0 :: real) < \<epsilon>"
  then have "openin m1.mtopology {z \<in> S. f z \<in> m2.open_ball (f x) \<epsilon>}" "f x \<in> S'"
    using openin_continuous_map_preimage[OF \<open>continuous_map m1.mtopology m2.mtopology f\<close>]  m2.mtopology_open_ball_in[of "f x",OF _ \<open>0 < \<epsilon>\<close>] continuous_map_image_subset_topspace[OF \<open>continuous_map m1.mtopology m2.mtopology f\<close>] m1.mtopology_topspace m2.mtopology_topspace
    by auto
  moreover have "x \<in> {z \<in> S. f z \<in> m2.open_ball (f x) \<epsilon>}"
    using \<open>x \<in> S\<close> \<open>0 < \<epsilon>\<close> continuous_map_image_subset_topspace[OF \<open>continuous_map m1.mtopology m2.mtopology f\<close>] m1.mtopology_topspace  m2.mtopology_topspace m2.dist_0[of "f x" "f x"]
    by(auto simp: m2.open_ball_def)
  ultimately obtain \<delta> where
   "\<delta>>0" "m1.open_ball x \<delta> \<subseteq> {z \<in> S. f z \<in> m2.open_ball (f x) \<epsilon>}"
    by (auto simp: m1.mtopology_openin_iff)
  thus "\<exists>\<delta>>0. \<forall>y\<in>S. d x y < \<delta> \<longrightarrow> d' (f x) (f y) < \<epsilon>"
    using  \<open>x \<in> S\<close> \<open>f x \<in> S'\<close> by(auto intro!: exI[where x=\<delta>] simp: m1.open_ball_def m2.open_ball_def)
next
  assume  "f \<in> S \<rightarrow> S'"
    and h:"\<forall>x\<in>S. \<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y\<in>S. d x y < \<delta> \<longrightarrow> d' (f x) (f y) < \<epsilon>"
  show "continuous_map m1.mtopology m2.mtopology f"
    unfolding continuous_map
  proof safe
    show "\<And>x. x \<in> topspace m1.mtopology \<Longrightarrow> f x \<in> topspace m2.mtopology"
      using \<open>f \<in> S \<rightarrow> S'\<close> m1.mtopology_topspace m2.mtopology_topspace by auto
  next
    fix U
    assume "openin m2.mtopology U"
    show "openin m1.mtopology {x \<in> topspace m1.mtopology. f x \<in> U}"
      unfolding m1.mtopology_openin_iff
    proof safe
      show "\<And>x. x \<in> topspace m1.mtopology \<Longrightarrow> f x \<in> U \<Longrightarrow> x \<in> S"
        using \<open>f \<in> S \<rightarrow> S'\<close> m1.mtopology_topspace m2.mtopology_topspace by auto
    next
      fix x
      assume "x \<in> topspace m1.mtopology" "f x \<in> U"
      then obtain \<epsilon> where he:
       "\<epsilon> > 0" "m2.open_ball (f x) \<epsilon> \<subseteq> U"
        using \<open>openin m2.mtopology U\<close> by(auto simp: m2.mtopology_openin_iff)
      then obtain \<delta> where hd:
       "\<delta> > 0" "\<And>y. y \<in> S \<Longrightarrow> d x y < \<delta> \<Longrightarrow> d' (f x) (f y) < \<epsilon>"
        using \<open>x \<in> topspace m1.mtopology\<close> m1.mtopology_topspace h by metis
      thus "\<exists>\<epsilon>>0. m1.open_ball x \<epsilon> \<subseteq> {x \<in> topspace m1.mtopology. f x \<in> U}"
        using m1.open_ballD m1.open_ballD' m1.mtopology_topspace he(2) \<open>f \<in> S \<rightarrow> S'\<close>
        by(auto intro!: exI[where x=\<delta>] simp: m2.open_ball_def) fastforce
    qed
  qed
qed

lemma metric_set_continuous_map_eq':
  shows "continuous_map m1.mtopology m2.mtopology f
         \<longleftrightarrow> f \<in> S \<rightarrow> S' \<and> (\<forall>x z. m1.converge_to_inS x z \<longrightarrow> m2.converge_to_inS (\<lambda>n. f (x n)) (f z))"
proof
  show "continuous_map m1.mtopology m2.mtopology f \<Longrightarrow> f \<in> S \<rightarrow> S' \<and> (\<forall>x z. m1.converge_to_inS x z \<longrightarrow> m2.converge_to_inS (\<lambda>n. f (x n)) (f z))"
    unfolding metric_set_continuous_map_eq
  proof safe
    fix x z
    assume h:"f \<in> S \<rightarrow> S'" "\<forall>x\<in>S. \<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y\<in>S. d x y < \<delta> \<longrightarrow> d' (f x) (f y) < \<epsilon>" "m1.converge_to_inS x z"
    hence h':"x \<in> m1.sequence" "z \<in> S" "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. d (x n) z < \<epsilon>"
      by(auto simp: m1.converge_to_inS_def2)
    show "m2.converge_to_inS (\<lambda>n. f (x n)) (f z)"
      unfolding m2.converge_to_inS_def2
    proof safe
      show "f (x n) \<in> S'" "f z \<in> S'" for n
        using h'(1,2) h(1) by auto
    next
      fix \<epsilon>
      assume he:"(0 :: real) < \<epsilon>"
      then obtain \<delta> where hd:"\<delta> > 0" "\<And>y. y \<in> S \<Longrightarrow> d z y < \<delta> \<Longrightarrow> d' (f z) (f y) < \<epsilon>"
        using h(2) h'(2) by metis
      obtain N where hn: "\<And>n. n \<ge> N \<Longrightarrow> d z (x n) < \<delta>"
        using h'(3)[OF hd(1),simplified m1.dist_sym[of _ z]] by auto
      show "\<exists>N. \<forall>n\<ge>N. d' (f (x n)) (f z) < \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n
        assume "n \<ge> N"
        then have "x n \<in> S" "d z (x n) < \<delta>"
          using hn[OF \<open>n \<ge> N\<close>] h'(1) by auto
        thus "d' (f (x n)) (f z) < \<epsilon>"
          by(auto intro!: hd(2) simp: m2.dist_sym[of _ "f z"])
      qed
    qed
  qed
next
  assume "f \<in> S \<rightarrow> S' \<and> (\<forall>x z. m1.converge_to_inS x z \<longrightarrow> m2.converge_to_inS (\<lambda>n. f (x n)) (f z))"
  hence h:"f \<in> S \<rightarrow> S'" "\<And>x z. m1.converge_to_inS x z \<Longrightarrow> m2.converge_to_inS (\<lambda>n. f (x n)) (f z)" by auto
  show "continuous_map m1.mtopology m2.mtopology f"
    unfolding continuous_map_closedin
  proof safe
    show "x \<in> topspace m1.mtopology \<Longrightarrow> f x \<in> topspace m2.mtopology" for x
      using m1.mtopology_topspace m2.mtopology_topspace h(1) by auto
  next
    fix C
    assume hcl:"closedin m2.mtopology C"
    show "closedin m1.mtopology {x \<in> topspace m1.mtopology. f x \<in> C}"
      unfolding m1.mtopology_closedin_iff
    proof safe
      fix y s
      assume hg:"y \<in> UNIV \<rightarrow> {x \<in> topspace m1.mtopology. f x \<in> C}" " m1.converge_to_inS y s"
      hence "(\<lambda>n. f (y n)) \<in> UNIV \<rightarrow> C"
        by auto
      thus "f s \<in> C" "s \<in> topspace m1.mtopology"
        using h(2)[OF hg(2)] hcl[simplified m2.mtopology_closedin_iff] hg(2)[simplified m1.converge_to_inS_def] m1.mtopology_topspace
        by auto
    qed(simp add: m1.mtopology_topspace)
  qed
qed

lemma continuous_map_limit_of:
  assumes "continuous_map m1.mtopology m2.mtopology f" "m1.convergent_inS xn"
  shows "m2.the_limit_of (\<lambda>n. f (xn n)) = f (m1.the_limit_of xn)"
  using assms  m1.the_limit_if_converge m2.the_limit_of_eq
  by(simp add: metric_set_continuous_map_eq')

text \<open> Uniform continuous functions. \<close>
definition uniform_continuous_map :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"uniform_continuous_map f \<longleftrightarrow> f \<in> S \<rightarrow> S' \<and> (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. d x y < \<delta> \<longrightarrow> d' (f x) (f y) < \<epsilon>)"

lemma uniform_continuous_map_const:
  assumes "y \<in> S'"
  shows "uniform_continuous_map (\<lambda>x. y)"
  using assms by(auto simp: uniform_continuous_map_def)

lemma continuous_if_uniform_continuous:
  assumes "uniform_continuous_map f"
  shows "continuous_map m1.mtopology m2.mtopology f"
  unfolding metric_set_continuous_map_eq
proof safe
  show "x \<in> S \<Longrightarrow> f x \<in> S'" for x
    using assms by(auto simp: uniform_continuous_map_def)
next
  fix x \<epsilon>
  assume [simp]:"x \<in> S" and "(0 :: real) < \<epsilon>"
  then obtain \<delta> where "\<delta> > 0" "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> d x y < \<delta> \<Longrightarrow> d' (f x) (f y) < \<epsilon>"
    using assms by(auto simp: uniform_continuous_map_def)
  thus "\<exists>\<delta>>0. \<forall>y\<in>S. d x y < \<delta> \<longrightarrow> d' (f x) (f y) < \<epsilon>"
    by(auto intro!: exI[where x=\<delta>])
qed

definition converges_uniformly :: "[nat \<Rightarrow> 'a \<Rightarrow> 'b, 'a \<Rightarrow> 'b] \<Rightarrow> bool" where
"converges_uniformly fn f \<longleftrightarrow> (\<forall>n. fn n \<in> S \<rightarrow> S') \<and> (f \<in> S \<rightarrow> S') \<and> (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>S. d' (fn n x) (f x) < e)"

lemma converges_uniformly_continuous:
  assumes "\<And>n. continuous_map m1.mtopology m2.mtopology (fn n)"
      and "converges_uniformly fn f"
    shows "continuous_map m1.mtopology m2.mtopology f"
  unfolding metric_set_continuous_map_eq
proof safe
  fix x e
  assume h:"x \<in> S" "e > (0 :: real)"
  then obtain N where N: "\<And>z n. n \<ge> N \<Longrightarrow> z \<in> S \<Longrightarrow> d' (fn n z) (f z) < e / 3"
    using assms(2) by(simp only: converges_uniformly_def) (meson zero_less_divide_iff zero_less_numeral)
  have f: "\<And>n x. x \<in> S \<Longrightarrow> fn n x \<in> S'" "\<And>x. x \<in> S \<Longrightarrow> f x \<in> S'"
    using assms(2) by(auto simp: converges_uniformly_def)
  from assms(1)[of N] h obtain \<delta> where h': "\<delta> > 0" "\<And>y. y \<in> S \<Longrightarrow> d x y < \<delta> \<Longrightarrow> d' (fn N x) (fn N y) < e / 3"
    by (metis metric_set_continuous_map_eq zero_less_divide_iff zero_less_numeral)
  show "\<exists>\<delta>>0. \<forall>y\<in>S. d x y < \<delta> \<longrightarrow> d' (f x) (f y) < e"
  proof(safe intro!: exI[where x=\<delta>])
    fix y
    assume y:"y \<in> S" "d x y < \<delta>"
    have "d' (f x) (f y) \<le> d' (f x) (fn N x) + d' (fn N x) (fn N y) + d' (fn N y) (f y)"
      using m2.dist_tr[of "f x" "fn N x" "f y"] m2.dist_tr[of "fn N x" "fn N y" "f y"] f[OF y(1)] f[OF h(1)]
      by auto
    also have "... < e"
      using N[OF order_refl h(1),simplified m2.dist_sym] N[OF order_refl y(1)] h'(2)[OF y]
      by auto
    finally show "d' (f x) (f y) < e" .
  qed(use h' in auto)
qed(use assms(2) converges_uniformly_def in auto)

text \<open> Lemma related @{term osc_on}.\<close>
lemma osc_on_inA_0:
  assumes "x \<in> A \<inter> S" "continuous_map (subtopology m1.mtopology (A \<inter> S)) m2.mtopology f"
  shows "m2.osc_on A m1.mtopology f x = 0"
proof -
  interpret subm1: metric_set "A \<inter> S" "submetric (A \<inter> S) d"
    by(auto intro!: m1.submetric_metric_set)
  have cont: "continuous_map subm1.mtopology m2.mtopology f"
    using assms(2) by (simp add: m1.submetric_subtopology)
  have "m2.osc_on A m1.mtopology f x < ennreal \<epsilon>" if e:"\<epsilon> > 0" for \<epsilon>
    unfolding m2.osc_on_less_iff
  proof -
    obtain \<epsilon>' where "\<epsilon>' > 0" "2*\<epsilon>' < \<epsilon>"
      using e field_lbound_gt_zero[of "\<epsilon>/2" "\<epsilon>/2"] by auto
    then obtain \<delta> where hd:"\<delta>>0" "\<And>y. y \<in> A \<Longrightarrow> y\<in>S \<Longrightarrow> d x y < \<delta> \<Longrightarrow> d' (f x) (f y) < \<epsilon>'"
      using assms(1) cont[simplified Set_Based_Metric_Space.metric_set_continuous_map_eq[OF subm1.metric_set_axioms m2.metric_set_axioms]]
      by(fastforce simp: submetric_def)
    show "\<exists>v. x \<in> v \<and> openin m1.mtopology v \<and> m2.diam (f ` (A \<inter> v)) < ennreal \<epsilon>"
    proof(safe intro!: exI[where x="m1.open_ball x \<delta>"] m1.open_ball_ina m1.mtopology_open_ball_in)
      have "m2.diam (f ` (A \<inter> m1.open_ball x \<delta>)) \<le> ennreal (2*\<epsilon>')"
        unfolding m2.diam_def Sup_le_iff
      proof safe
        fix a1 a2
        assume h:"a1 \<in> A" "a1 \<in> m1.open_ball x \<delta>" "f a1 \<in> S'"
                 "a2 \<in> A" "a2 \<in> m1.open_ball x \<delta>" "f a2 \<in> S'"
        have "f x \<in> S'"
          using cont assms(1) by(auto simp: Set_Based_Metric_Space.metric_set_continuous_map_eq[OF subm1.metric_set_axioms m2.metric_set_axioms])
        have "d' (f a1) (f a2) < 2*\<epsilon>'"
          using hd(2)[OF \<open>a1 \<in> A\<close> m1.open_ballD'(1)[OF h(2)] m1.open_ballD[OF h(2)]] hd(2)[OF \<open>a2 \<in> A\<close> m1.open_ballD'(1)[OF h(5)] m1.open_ballD[OF h(5)]] m2.dist_tr[OF \<open>f a1 \<in> S'\<close> \<open>f x \<in> S'\<close> \<open>f a2 \<in> S'\<close>,simplified m2.dist_sym[of "f a1" "f x"]]
          by auto
        thus "ennreal (d' (f a1) (f a2)) \<le> ennreal (2*\<epsilon>')"
          by (simp add: ennreal_leI)
      qed
      also have "... < ennreal \<epsilon>"
        using \<open>2*\<epsilon>' < \<epsilon>\<close> ennreal_lessI e by presburger 
      finally show "m2.diam (f ` (A \<inter> m1.open_ball x \<delta>)) < ennreal \<epsilon>" .
    qed(use hd(1) IntD2[OF assms(1)] in auto)
  qed
  hence "m2.osc_on A m1.mtopology f x < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
    by (metis ennreal_enn2real ennreal_le_epsilon ennreal_less_zero_iff linorder_not_le order_le_less_trans that)
  thus ?thesis
    by fastforce
qed

end

context metric_set
begin

interpretation rnv: metric_set "UNIV :: ('b :: real_normed_vector) set" dist_typeclass
  by simp

lemma dist_set_uniform_continuous:
 "uniform_continuous_map S dist UNIV dist_typeclass (dist_set A)"
  unfolding uniform_continuous_map_def[OF metric_set_axioms rnv.metric_set_axioms] dist_real_def
proof safe
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  then show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> \<bar>dist_set A x - dist_set A y\<bar> < \<epsilon>"
    using order.strict_trans1[OF dist_set_abs_le] by(auto intro!: exI[where x=\<epsilon>])
qed simp

lemma dist_set_continuous: "continuous_map mtopology euclideanreal (dist_set A)"
  unfolding euclidean_mtopology[symmetric]
  by(auto intro!: continuous_if_uniform_continuous simp: dist_set_uniform_continuous metric_set_axioms)


lemma uniform_continuous_map_add:
 fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
 assumes "uniform_continuous_map S dist UNIV dist_typeclass f" "uniform_continuous_map S dist UNIV dist_typeclass g"
 shows "uniform_continuous_map S dist UNIV dist_typeclass (\<lambda>x. f x + g x)"
  unfolding uniform_continuous_map_def[OF metric_set_axioms rnv.metric_set_axioms]
proof safe
  fix e :: real
  assume "e > 0"
  from half_gt_zero[OF this] assms obtain d1 d2 where d: "d1 > 0" "d2 > 0"
   "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < d1 \<Longrightarrow> dist_typeclass (f x) (f y) < e / 2"    "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < d2 \<Longrightarrow> dist_typeclass (g x) (g y) < e / 2"
    by(simp only: uniform_continuous_map_def[OF metric_set_axioms rnv.metric_set_axioms]) metis
  show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> dist_typeclass (f x + g x) (f y + g y) < e"
    using d by(fastforce intro!: exI[where x="min d1 d2"] order.strict_trans1[OF dist_triangle_add])
qed simp

lemma uniform_continuous_map_real_devide:
 fixes f :: "'a \<Rightarrow> real"
 assumes "uniform_continuous_map S dist UNIV dist_typeclass f" "uniform_continuous_map S dist UNIV dist_typeclass g"
     and "\<And>x. x \<in> S \<Longrightarrow> g x \<noteq> 0" "\<And>x. x \<in> S \<Longrightarrow> \<bar>g x\<bar> \<ge> a" "a > 0" "\<And>x. x \<in> S \<Longrightarrow> \<bar>g x\<bar> < Kg"
     and "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> < Kf"
   shows "uniform_continuous_map S dist UNIV dist_typeclass (\<lambda>x. f x / g x)"
  unfolding uniform_continuous_map_def[OF metric_set_axioms rnv.metric_set_axioms]
proof safe
  fix e :: real
  assume e[arith]:"e > 0"
  consider "S = {}" | "S \<noteq> {}" by auto
  then show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> dist_typeclass (f x / g x) (f y / g y) < e"
  proof cases
    case 1
    then show ?thesis by (auto intro!: exI[where x=1])
  next
    case S:2
    then have Kfg_pos[arith]: "Kg > 0" "Kf \<ge> 0"
      using assms(4-7) by auto fastforce+
    define e' where "e' \<equiv> a^2 / (Kf + Kg)  * e"
    have e':"e' > 0"
      using assms(5) by(auto simp: e'_def)
    with assms obtain d1 d2 where d: "d1 > 0" "d2 > 0"
    "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < d1 \<Longrightarrow> \<bar>f x - f y\<bar> < e'"    "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < d2 \<Longrightarrow> \<bar>g x - g y\<bar> < e'"
      by(auto simp: uniform_continuous_map_def[OF metric_set_axioms rnv.metric_set_axioms] dist_real_def) metis
    show ?thesis
      unfolding dist_real_def
    proof(safe intro!: exI[where x="min d1 d2"])
      fix x y
      assume x:"x \<in> S" and y:"y \<in> S" and "dist x y < min d1 d2"
      then have dist[arith]: "dist x y < d1" "dist x y < d2" by auto
      note [arith] = assms(3,4,6,7)[OF x] assms(3,4,6,7)[OF y]
      have "\<bar>f x / g x - f y / g y\<bar> = \<bar>(f x * g y - f y * g x) / (g x * g y)\<bar>"
        by(simp add: diff_frac_eq)
      also have "... = \<bar>(f x * g y - f x * g x + (f x * g x  - f y * g x)) / (g x * g y)\<bar>"
        by simp
      also have "... = \<bar>(f x - f y) * g x - f x * (g x - g y)\<bar> / (\<bar>g x\<bar> * \<bar>g y\<bar>)"
        by(simp add: left_diff_distrib right_diff_distrib abs_mult)
      also have "... \<le> (\<bar>f x - f y\<bar> * \<bar>g x\<bar> + \<bar>f x\<bar> * \<bar>g x - g y\<bar>) / (\<bar>g x\<bar> * \<bar>g y\<bar>)"
        by(rule divide_right_mono) (use abs_triangle_ineq4 abs_mult in metis,auto)
      also have "... < (e' * Kg + Kf * e') / (\<bar>g x\<bar> * \<bar>g y\<bar>)"
        by(rule divide_strict_right_mono[OF add_less_le_mono]) (auto intro!: mult_mono' mult_strict_mono, use  d(3,4)[OF x y] in auto)
      also have "... \<le> (e' * Kg + Kf * e') / a^2"
        by(auto intro!: divide_left_mono simp: power2_eq_square) (insert assms(5) e', auto simp: \<open>a \<le> \<bar>g x\<bar>\<close> mult_mono')
      also have "... = (Kf + Kg) / a^2 * e'"
        by (simp add: distrib_left mult.commute)
      also have "... = e"
        using assms(5) by(auto simp: e'_def)
      finally show " \<bar>f x / g x - f y / g y\<bar> < e" .
    qed(use d in auto)
  qed
qed simp

lemma the_limit_of_dist_converge:
  assumes "converge_to_inS xn x"
  shows "(\<lambda>n. dist (xn n) y) \<longlonglongrightarrow> dist (the_limit_of xn) y"
proof -
  have "continuous_map mtopology euclideanreal (\<lambda>z. dist z y)"
    using dist_set_continuous[of "{y}"] by simp
  hence "(\<lambda>n. dist (xn n) y) \<longlonglongrightarrow> dist x y"
    using assms
    by(auto simp: metric_set_continuous_map_eq'[OF metric_set_axioms rnv.metric_set_axioms,simplified euclidean_mtopology] converge_to_def_set)
  thus ?thesis
    by(simp add: the_limit_of_eq[OF assms])
qed

lemma the_limit_of_dist_converge':
  assumes "converge_to_inS xn x" "\<epsilon> > 0"
  shows "\<exists>N. \<forall>n\<ge>N. \<bar> dist (xn n) y - dist (the_limit_of xn) y \<bar> < \<epsilon>"
  using the_limit_of_dist_converge[OF assms(1)] assms(2) by(simp add: LIMSEQ_iff)

lemma the_limit_of_dist:
  assumes "converge_to_inS xn x"
  shows "lim (\<lambda>n. dist (xn n) y) = dist (the_limit_of xn) y"
  using the_limit_of_dist_converge[OF assms] limI by blast

text \<open> Upper-semicontinuous functions.\<close>
lemma upper_semicontinuous_map_def2:
  fixes f :: "'a \<Rightarrow> ('b :: {complete_linorder,linorder_topology})"
  shows "upper_semicontinuous_map mtopology f \<longleftrightarrow> (\<forall>x y. converge_to_inS x y \<longrightarrow> limsup (\<lambda>n. f (x n)) \<le> f y)"
proof
  show "upper_semicontinuous_map mtopology f \<Longrightarrow> \<forall>x y. converge_to_inS x y \<longrightarrow> limsup (\<lambda>n. f (x n)) \<le> f y"
    unfolding upper_semicontinuous_map_def
  proof safe
    fix x y
    assume h:"\<forall>a. openin mtopology {x \<in> topspace mtopology. f x < a}" "converge_to_inS x y"
    show "limsup (\<lambda>n. f (x n)) \<le> f y"
      unfolding Limsup_le_iff eventually_sequentially
    proof safe
      fix c
      assume "f y < c"
      show "\<exists>N. \<forall>n\<ge>N. f (x n) < c"
      proof(rule ccontr)
        assume "\<nexists>N. \<forall>n\<ge>N. f (x n) < c"
        then have hc:"\<And>N. \<exists>n\<ge>N. f (x n) \<ge> c"
          using linorder_not_less by blast
        define a :: "nat \<Rightarrow> nat" where "a \<equiv> rec_nat (SOME n. f (x n) \<ge> c) (\<lambda>n an. SOME m. m > an \<and> f (x m) \<ge> c)"
        have "strict_mono a"
        proof(rule strict_monoI_Suc)
          fix n
          have [simp]:"a (Suc n) = (SOME m. m > a n \<and> f (x m) \<ge> c)"
            by(auto simp: a_def)
          show "a n < a (Suc n)"
            by simp (metis (mono_tags, lifting) Suc_le_lessD hc someI)
        qed
        have *:"f (x (a n)) \<ge> c" for n
        proof(cases n)
          case 0
          then show ?thesis
            using hc[of 0] by(auto simp: a_def intro!: someI_ex)
        next
          case (Suc n')
          then show ?thesis
            by(simp add: a_def) (metis (mono_tags, lifting) Suc_le_lessD hc someI_ex)
        qed
        obtain N where "\<And>n. n \<ge> N \<Longrightarrow> x (a n) \<in> {x \<in> S. f x < c}"
          using converge_to_inS_subseq[OF \<open>strict_mono a\<close> h(2)] mtopology_openin_iff2[of "{x \<in> S. f x < c}"] h(2)[simplified converge_to_inS_def] mtopology_topspace \<open>f y < c\<close> h
          by fastforce
        from *[of N] this[of N] show False by auto
      qed
    qed
  qed
next
  assume h:"\<forall>x y. converge_to_inS x y \<longrightarrow> limsup (\<lambda>n. f (x n)) \<le> f y"
  show "upper_semicontinuous_map mtopology f"
    unfolding upper_semicontinuous_map_def mtopology_openin_iff2 mtopology_topspace
  proof safe
    fix a y s
    assume "converge_to_inS y s" "s \<in> S" "f s < a"
    then have "limsup (\<lambda>n. f (y n)) \<le> f s"
      using h by auto
    with \<open>f s < a\<close> obtain N where "\<And>n. n\<ge>N \<Longrightarrow> f (y n) < a"
      by(auto simp: Limsup_le_iff eventually_sequentially)
    thus "\<exists>N. \<forall>n\<ge>N. y n \<in> {x \<in> S. f x < a}"
      using \<open>converge_to_inS y s\<close> by(auto intro!: exI[where x=N] simp: converge_to_inS_def)
  qed
qed

lemma upper_semicontinuous_map_def2real:
  fixes f :: "'a \<Rightarrow> real"
  shows "upper_semicontinuous_map mtopology f \<longleftrightarrow> (\<forall>x y. converge_to_inS x y \<longrightarrow> limsup (\<lambda>n. f (x n)) \<le> f y)"
  unfolding upper_semicontinuous_map_real_iff upper_semicontinuous_map_def2
  by auto

lemma osc_upper_semicontinuous_map:
 "upper_semicontinuous_map X (osc X f)"
proof -
  have "{x \<in> topspace X. osc X f x < a} = \<Union> {V. openin X V \<and> diam (f ` V) < a}" for a
   using openin_subset by(auto simp add: osc_less_iff)
  thus ?thesis
    by(auto simp: upper_semicontinuous_map_def)
qed

end

text \<open> Open maps.\<close>
lemma metric_set_opem_map_from_dist:
  assumes "metric_set S d" "metric_set S' d'" "f \<in> S \<rightarrow> S'"
      and "\<And>x \<epsilon>. x \<in> S \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> \<exists>\<delta>>0. \<forall>y\<in>S. d' (f x) (f y) < \<delta> \<longrightarrow> d x y < \<epsilon>"
    shows "open_map (metric_set.mtopology S d) (subtopology (metric_set.mtopology S' d') (f ` S)) f"
proof -
  interpret m1: metric_set S d by fact
  interpret m2: metric_set S' d' by fact
  interpret m2': metric_set "f ` S" "submetric (f ` S) d'"
    using assms(3) by(auto intro!: m2.submetric_metric_set)
  show ?thesis
  proof(rule open_map_with_base[OF m1.mtopology_basis_ball])
    fix A
    assume "A \<in> {m1.open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}"
    then obtain a \<epsilon> where hae:
     "a \<in> S" "0 < \<epsilon>" "A = m1.open_ball a \<epsilon>" by auto
    show "openin (subtopology m2.mtopology (f ` S)) (f ` A)"
      unfolding m2.submetric_subtopology[OF funcset_image[OF assms(3)]]  m2'.mtopology_openin_iff
    proof
      show "f ` A \<subseteq> f ` S"
        using m1.open_ball_subset_ofS[of a \<epsilon>] by(auto simp: hae(3))
    next
      show "\<forall>x\<in>f ` A. \<exists>\<epsilon>>0. m2'.open_ball x \<epsilon> \<subseteq> f ` A"
      proof safe
        fix x
        assume "x \<in> A"
        hence "x \<in> S"
          using m1.open_ball_subset_ofS[of a \<epsilon>] by(auto simp: hae(3))
        moreover have "0 < \<epsilon> - d a x"
          using \<open>x \<in> A\<close> m1.open_ballD[of x a \<epsilon>] by(auto simp: hae(3))
        ultimately obtain \<delta> where hd:"\<delta> > 0" "\<And>y. y\<in>S \<Longrightarrow> d' (f x) (f y) < \<delta> \<Longrightarrow> d x y <  \<epsilon> - d a x"
          using assms(4) by metis
        show "\<exists>\<epsilon>>0. m2'.open_ball (f x) \<epsilon> \<subseteq> f ` A"
        proof(safe intro!: exI[where x=\<delta>])
          fix z
          assume "z \<in> m2'.open_ball (f x) \<delta>"
          note hz = m2'.open_ballD'[OF this]
          then obtain y where "y \<in> S" "z = f y" by auto
          hence "d' (f x) (f y) < \<delta>"
            using m2'.open_ballD[OF \<open>z \<in> m2'.open_ball (f x) \<delta>\<close>] \<open>x \<in> A\<close> m1.open_ball_subset_ofS[of a \<epsilon>]
            by(auto simp: submetric_def  hae(3))
          hence "d x y <  \<epsilon> - d a x"
            by(auto intro!: hd(2)[OF \<open>y \<in> S\<close>])
          hence "d a y < \<epsilon>"
            using m1.dist_tr[OF \<open>a \<in> S\<close> \<open>x \<in> S\<close> \<open>y \<in> S\<close>] by auto
          thus "z \<in> f ` A"
            by (simp add: \<open>y \<in> S\<close> \<open>z = f y\<close> hae(1) hae(3) m1.open_ball_def)
        qed(use hd in auto)
      qed
    qed
  qed
qed

subsubsection \<open> Complete Metric Spaces\<close>
locale complete_metric_set = metric_set +
  assumes convergence: "\<And>f. Cauchy_inS f \<Longrightarrow> convergent_inS f"

lemma complete_space_complete_metric_set:
 "complete_metric_set (UNIV :: 'a :: complete_space set) dist"
proof -
  interpret m: metric_set UNIV dist
    by(rule metric_class_metric_set)
  show ?thesis
    by standard (simp add: Cahuchy_def_set[symmetric] convergent_def_set[symmetric] Cauchy_convergent_iff)
qed

lemma(in complete_metric_set) submetric_complete_iff:
  assumes "M \<subseteq> S"
  shows "complete_metric_set M (submetric M dist) \<longleftrightarrow> closedin mtopology M"
proof
  assume "complete_metric_set M (submetric M dist)"
  then interpret m: complete_metric_set M "submetric M dist" .
  show "closedin mtopology M"
  proof(rule ccontr)
    assume "\<not> closedin mtopology M"
    then have "\<exists>f\<in>m.sequence. \<exists>s. converge_to_inS f s \<and> s \<notin> M"
      using assms mtopology_closedin_iff by auto
    then obtain f s where hfs:"f \<in> m.sequence" "converge_to_inS f s" "s \<notin> M"
      by auto
    hence "convergent_inS f"
      by(auto simp: convergent_inS_def converge_to_inS_def)
    have "m.Cauchy_inS f"
      using Cauchy_if_convergent_inS[OF \<open>convergent_inS f\<close>] hfs(1)
      by(auto simp: m.Cauchy_inS_def Cauchy_inS_def) (fastforce simp: submetric_def)
    then obtain s' where "s' \<in> M" "m.converge_to_inS f s'"
      using m.convergence by(auto simp: m.convergent_inS_def m.converge_to_inS_def)
    from converge_to_insub_converge_to_inS[OF assms this(2)] hfs(2)
    have "s' = s"
      by(rule converge_to_inS_unique)
    thus False
      using \<open>s' \<in> M\<close> \<open>s \<notin> M\<close> by simp
  qed
next
  interpret m: metric_set M "submetric M dist"
    by(rule submetric_metric_set[OF assms])
  assume cls:"closedin mtopology M"
  show "complete_metric_set M (submetric M dist)"
  proof
    fix f
    assume "m.Cauchy_inS f"
    then have "f \<in> m.sequence" by(simp add: m.Cauchy_inS_def)
    have "Cauchy_inS f"
      by(rule Cauchy_insub_Cauchy[OF assms \<open>m.Cauchy_inS f\<close>])
    then obtain x where hx:"x \<in> S" "converge_to_inS f x"
      using convergence by(auto simp: convergent_inS_def converge_to_inS_def)
    hence "x \<in> M"
      using cls[simplified mtopology_closedin_iff] \<open>f \<in> m.sequence\<close> assms
      by auto
    hence "m.converge_to_inS f x"
      using convergent_insubmetric[OF assms \<open>f \<in> m.sequence\<close>] hx by auto
    thus "m.convergent_inS f"
      using \<open>x \<in> M\<close> by(auto simp: m.convergent_inS_def)
  qed
qed

lemma(in complete_metric_set) embed_dist_complete:
  assumes "f \<in> B \<rightarrow> S" "inj_on f B" "closedin mtopology (f ` B)"
  shows "complete_metric_set B (embed_dist_on B f)"
proof -
  interpret m: metric_set B "embed_dist_on B f"
    by(rule embed_dist_dist[OF assms(1,2)])
  show ?thesis
  proof
    fix xn
    assume "m.Cauchy_inS xn"
    hence h:"xn \<in> m.sequence" "Cauchy_inS (\<lambda>n. f (xn n))"
      by(auto simp add: embed_dist_Cauchy_inS_iff[OF assms(1,2)])
    with convergence obtain x where x: "converge_to_inS (\<lambda>n. f (xn n)) x"
      by(auto simp: convergent_inS_def)
    have x': "x \<in> f ` B"
    proof -
      have "(\<lambda>n. f (xn n)) \<in> UNIV \<rightarrow> f ` B"
        using assms(1) h(1) by auto
      thus ?thesis
        using assms(3) x by(auto simp: mtopology_closedin_iff) 
    qed
    then obtain b where b: "b \<in> B" "f b = x" by auto
    show "m.convergent_inS xn"
      by(auto simp: m.convergent_inS_def embed_dist_converge_to_inS_iff[OF assms(1,2)] b x h intro!: exI[where x=b])
  qed
qed

lemma(in metric_set) Cantor_intersection_theorem:
 "complete_metric_set S dist \<longleftrightarrow> (\<forall>Fn. (\<forall>n. Fn n \<noteq> {}) \<and> (\<forall>n. closedin mtopology (Fn n)) \<and> decseq Fn \<and> (\<forall>\<epsilon> > 0. \<exists>N. \<forall>n\<ge>N. diam (Fn n) < \<epsilon>) \<longrightarrow> (\<exists>x\<in>S. \<Inter> (range Fn) = {x}))"
proof safe
  fix Fn
  assume "complete_metric_set S dist"
  interpret complete_metric_set S dist by fact
  assume h: "\<forall>n. Fn n \<noteq> {}" " \<forall>n. closedin mtopology (Fn n)" "decseq Fn" "\<forall>\<epsilon> > 0. \<exists>N. \<forall>n\<ge>N. diam (Fn n) < \<epsilon>"
  then obtain xn where xn1: "\<And>n. xn n \<in> Fn n"
    by (meson all_not_in_conv)
  hence xn2: "xn \<in> sequence"
    using closedin_subset[of mtopology] h(2) by(auto simp: mtopology_topspace)
  have "Cauchy_inS xn"
    unfolding Cauchy_inS_def
  proof safe
    fix \<epsilon> :: real
    assume "0 < \<epsilon>"
    then obtain N where N:"\<And>n. n\<ge>N \<Longrightarrow> diam (Fn n) < ennreal \<epsilon>"
      using h(4) ennreal_less_zero_iff by blast
    show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (xn n) (xn m) < \<epsilon>"
    proof(safe intro!: exI[where x=N])
      fix n m
      assume "n \<ge> N" "m \<ge> N"
      define nm where "nm = min m n"
      have "nm \<ge> N" "nm \<le> n" "nm \<le> m"
        using \<open>n \<ge> N\<close> \<open>m \<ge> N\<close> by(auto simp: nm_def)
      hence "xn n \<in> Fn nm" "xn m \<in> Fn nm"
        using decseqD[OF h(3)] xn1[of n] xn1[of m] by auto
      hence "ennreal (dist (xn n) (xn m)) \<le> diam (Fn nm)"
        using xn2 by(auto intro!: diam_is_sup  mtopology_topspace)
      also have "... < ennreal \<epsilon>"
        by(rule N[OF \<open>nm \<ge> N\<close>])
      finally show "dist (xn n) (xn m) < \<epsilon>"
        by (simp add: dist_geq0 ennreal_less_iff)
    qed
  qed(use xn2 in auto)
  then obtain x where x:"x \<in> S" "converge_to_inS xn x"
    using convergence[of xn] by(auto simp: convergent_inS_def converge_to_inS_def)
  show "\<exists>x\<in>S. \<Inter> (range Fn) = {x}"
  proof(safe intro!: bexI[where x=x])
    fix n
    show "x \<in> Fn n"
    proof(rule ccontr)
      assume "x \<notin> Fn n"
      moreover have "openin mtopology (S - Fn n)"
        using h(2) by (simp add: openin_diff)
      ultimately obtain \<epsilon> where e: "\<epsilon> > 0" "open_ball x \<epsilon> \<subseteq> S - Fn n"
        using x(1) by(auto simp: mtopology_openin_iff)
      then have "\<exists>N. \<forall>n\<ge>N. xn n \<in> open_ball x \<epsilon>"
        using mtopology_openin_iff2[of "open_ball x \<epsilon>"] open_ball_ina[OF x(1) e(1)] x(2)
        by(auto simp: openin_open_ball)
      then obtain N where N:"\<And>m. m \<ge> N \<Longrightarrow> xn m \<in> open_ball x \<epsilon>"
        by auto
      hence "xn m \<in> S - Fn m" if "m \<ge> N" "m \<ge> n" for m
        using e(2) decseqD[OF h(3) that(2)] using that(1) by blast
      from xn1[of "max N n"] this[of "max N n"]
      show False by auto
    qed
  next
    fix y
    assume "y \<in> \<Inter> (range Fn)"
    then have hy:"\<forall>n. y \<in> Fn n" by auto
    have "y \<in> S"
        using closedin_subset[of mtopology] h(2) hy mtopology_topspace by auto
    have "converge_to_inS xn y"
      unfolding converge_to_inS_def2
    proof safe
      fix \<epsilon> :: real
      assume "0 < \<epsilon>"
      then obtain N where N:"\<And>n. n \<ge> N \<Longrightarrow> diam (Fn n) < ennreal \<epsilon>"
        using ennreal_less_zero_iff h(4) by presburger
      show "\<exists>N. \<forall>n\<ge>N. dist (xn n) y < \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n
        assume "n \<ge> N"
        then have "ennreal (dist (xn n) y) < ennreal \<epsilon>"
          using \<open>y \<in> S\<close> hy xn1[of n] xn2
          by(auto intro!: order.strict_trans1[OF diam_is_sup[of "xn n" "Fn n" y] N[of n]])
        thus "dist (xn n) y < \<epsilon>"
          by (simp add: dist_geq0 ennreal_less_iff)
      qed
    qed(use xn2 \<open>y \<in> S\<close> in auto)
    with converge_to_inS_unique[OF x(2)]
    show "y = x" by simp
  qed(use x in auto)
next
  assume h:"\<forall>Fn. (\<forall>n. Fn n \<noteq> {}) \<and> (\<forall>n. closedin mtopology (Fn n)) \<and> decseq Fn \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. diam (Fn n) < \<epsilon>) \<longrightarrow> (\<exists>x\<in>S. \<Inter> (range Fn) = {x})"
  show "complete_metric_set S dist"
  proof
    fix xn
    assume cauchy:"Cauchy_inS xn"
    hence xn: "xn \<in> sequence"
      by (simp add: Cauchy_inS_dest1)
    define Fn where "Fn \<equiv> (\<lambda>n. mtopology closure_of {xn m|m. m \<ge> n})"
    have Fn0': "{xn m|m. m \<ge> n} \<subseteq> Fn n" for n
      using xn by(auto intro!: closure_of_subset simp: Fn_def mtopology_topspace)
    have Fn0: "\<And>n. Fn n \<subseteq> S"
      using xn by(auto simp: Fn_def in_closure_of metric_set.mtopology_topspace metric_set_axioms)
    have Fn1: "Fn n \<noteq> {}" for n
      using xn closure_of_eq_empty[of "{xn m|m. m \<ge> n}" mtopology,simplified mtopology_topspace]
      by(auto simp: Fn_def)
    have Fn2:"\<And>n. closedin mtopology (Fn n)"
      by(simp add: Fn_def)
    have Fn3: "decseq Fn"
      by standard (auto simp: Fn_def intro!: closure_of_mono)
    have Fn4:"\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. diam (Fn n) < \<epsilon>"
    proof safe
      fix \<epsilon> :: ennreal
      assume "0 < \<epsilon>"
      define e where "e \<equiv> min 1 \<epsilon>"
      have he: "e \<le> \<epsilon>" "enn2real e > 0" "ennreal (enn2real e) = e"
        using \<open>0 < \<epsilon>\<close> by(auto simp: e_def enn2real_positive_iff min_less_iff_disj)
      then obtain e' where e':"e' > 0" "e' < enn2real e"
        using field_lbound_gt_zero by auto
      then obtain N where N:"\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> dist (xn n) (xn m) \<le> e'"
        using cauchy by(fastforce simp: Cauchy_inS_def)
      show "\<exists>N. \<forall>n\<ge>N. diam (Fn n) < \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n
        assume "N \<le> n"
        then have "diam (Fn n) \<le> ennreal e'"
          by(auto intro!: diam_le N simp: Fn_def diam_eq_closure)
        also have "... < e"
          using e'(2) ennreal_lessI he(2) he(3) by fastforce
        finally show "diam (Fn n) < \<epsilon>"
          using he(1) by auto
      qed
    qed
    obtain x where x:"x\<in>S" "\<Inter> (range Fn) = {x}"
      using h Fn1 Fn2 Fn3 Fn4 by metis
    show "convergent_inS xn"
      unfolding convergent_inS_def converge_to_inS_def2
    proof(safe intro!: exI[where x=x])
      fix \<epsilon> :: real
      assume he:"0 < \<epsilon>"
      then have "0 < ennreal \<epsilon>" by simp
      then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> diam (Fn n) < ennreal \<epsilon>"
        using Fn4 by metis
      show "\<exists>N. \<forall>n\<ge>N. dist (xn n) x < \<epsilon>"
      proof(safe intro!: exI[where x=N])
        fix n
        assume "N \<le> n"
        then have "xn n \<in> Fn N" "x \<in> Fn N"
          using x(2) Fn0'[of N] by auto
        hence "ennreal (dist (xn n) x) \<le> diam (Fn N)"
          using Fn0 by(auto intro!: diam_is_sup)
        also have "... <  ennreal \<epsilon>"
          by(auto intro!: N)
        finally show "dist (xn n) x < \<epsilon>"
          by (simp add: dist_geq0 ennreal_less_iff)
      qed
    qed(use xn x in auto)
  qed
qed

lemma(in complete_metric_set) closed_decseq_Inter':
  assumes "\<And>n. Fn n \<noteq> {}" "\<And>n. closedin mtopology (Fn n)" "decseq Fn"
      and "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. diam (Fn n) < \<epsilon>"
    shows "\<exists>x\<in>S. \<Inter> (range Fn) = {x}"
  using assms Cantor_intersection_theorem by(simp add: complete_metric_set_axioms)

lemma(in complete_metric_set) closed_decseq_Inter:
  assumes "\<And>n. Fn n \<noteq> {}" "\<And>n. closedin mtopology (Fn n)" "decseq Fn"
      and "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. diam (Fn n) < ennreal \<epsilon>"
    shows "\<exists>x\<in>S. \<Inter> (range Fn) = {x}"
proof -
  have "\<exists>N. \<forall>n\<ge>N. diam (Fn n) < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
  proof -
    consider "\<epsilon> < \<infinity>" | "\<epsilon> = \<infinity>"
      using top.not_eq_extremum by fastforce
    then show ?thesis
    proof cases
      case 1
      with that have 2:"ennreal (enn2real \<epsilon>) = \<epsilon>"
        by simp
      have "0 < enn2real \<epsilon>"
        using 1 that by(simp add: enn2real_positive_iff)
      from assms(4)[OF this] show ?thesis
        by(simp add: 2)
    next
      case 2
      then show ?thesis
        by (metis assms(4) ennreal_less_top gt_ex infinity_ennreal_def order_less_imp_not_less top.not_eq_extremum)
    qed
  qed
  thus ?thesis
    using closed_decseq_Inter'[OF assms(1-3)] by simp
qed

subsubsection \<open> Separable Metric Spaces \<close>
locale separable_metric_set = metric_set +
  assumes separable: "\<exists>U. countable U \<and> dense_set U"

lemma(in metric_set) separable_if_countable:
  assumes "countable S"
  shows "separable_metric_set S dist"
  apply standard
  using assms by(auto intro!: exI[where x=S] simp: dense_set_S)

lemma(in metric_set) separable_iff_topological_separable:
 "separable_metric_set S dist \<longleftrightarrow> separable mtopology"
  by(simp add: separable_metric_set_def separable_metric_set_axioms_def separable_def metric_set_axioms)

lemma(in separable_metric_set) topological_separable_if_separable:
  "separable mtopology"
  using separable_iff_topological_separable
  by (simp add: separable_metric_set_axioms)

lemma separable_metric_setI:
  assumes "metric_set S d" "separable (metric_set.mtopology S d)"
  shows "separable_metric_set S d"
  by (simp add: assms(1) assms(2) metric_set.separable_iff_topological_separable)

text \<open> For a metric space $X$, $X$ is separable iff $X$ is second countable.\<close>
lemma(in metric_set) generated_by_countable_balls:
  assumes "countable U" and "dense_set U"
  shows "mtopology = topology_generated_by {open_ball y (1 / real n) | y n. y \<in> U}"
proof -
  have hu: "U \<subseteq> S" "\<And>x \<epsilon>. x \<in> S \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> open_ball x \<epsilon> \<inter> U \<noteq> {}"
    using assms by(auto simp: dense_set_def)
  show ?thesis
    unfolding mtopology_def2
  proof(rule topology_generated_by_eq)
    fix K
    assume "K \<in> {open_ball y (1 / real n) |y n. y \<in> U}"
    then obtain y n where hyn:
     "y \<in> U" "y \<in> S" "K = open_ball y (1 / real n)"
      using hu(1) by auto
    consider "n = 0" | "n > 0" by auto
    then show "openin (topology_generated_by {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}) K"
    proof cases
      case 1
      then have "K = {}"
        using hyn dist_geq0[of y] not_less by(auto simp: open_ball_def)
      thus ?thesis
        by auto
    next
      case 2
      then have "1 / real n > 0" by auto
      thus ?thesis
        using hyn mtopology_open_ball_in[simplified mtopology_def2] by auto
    qed
  next
    have h0:"\<And>x \<epsilon>. x \<in> S \<Longrightarrow> \<epsilon> > 0 \<Longrightarrow> \<exists>y\<in>U. \<exists>n. x \<in> open_ball y (1 / real n) \<and> open_ball y (1 / real n) \<subseteq> open_ball x \<epsilon>"
    proof -
      fix x \<epsilon>
      assume h: "x \<in> S" "(0 :: real) < \<epsilon>"
      then obtain N where hn: "1 / \<epsilon> < real N"
        using reals_Archimedean2 by blast
      have hn0: "0 < real N"
        by(rule ccontr) (use hn h in fastforce)
      hence hn':"1 / real N < \<epsilon>"
        using h hn by (metis divide_less_eq mult.commute)
      have "open_ball x (1 / (2 * real N)) \<inter> U \<noteq> {}"
        using dense_set_def[of U] assms(2) h(1) hn0 by fastforce
      then obtain y where hy:
        "y\<in>U" "y \<in> S" "y \<in> open_ball x (1 / (real (2 * N)))"
        using hu by auto
      show "\<exists>y\<in>U. \<exists>n. x \<in> open_ball y (1 / real n) \<and> open_ball y (1 / real n) \<subseteq> open_ball x \<epsilon>"
      proof(intro bexI[where x=y] exI[where x="2 * N"] conjI)
        show "x \<in> open_ball y (1 / real (2 * N))"
          using hy(3) by(simp add: open_ball_inverse[of x y])
      next
        show "open_ball y (1 / real (2 * N)) \<subseteq> open_ball x \<epsilon>"
        proof
          fix y'
          assume hy':"y' \<in> open_ball y (1 / real (2 * N))"
          have "dist x y' < \<epsilon>" (is "?lhs < ?rhs")
          proof -
            have "?lhs \<le> dist x y + dist y y'"
              using hy(2) open_ballD'(1)[OF hy'] h(1) by(auto intro!: dist_tr)
            also have "... < 1 / real (2 * N) + 1 / real (2 * N)"
              apply(rule strict_ordered_ab_semigroup_add_class.add_strict_mono)
              using hy(3) hy(2) open_ballD'(1)[OF hy'] h(1) hy' by(simp_all add: open_ball_def dist_sym[of x y])
            finally show ?thesis
              using hn' by auto
          qed
          thus "y' \<in> open_ball x \<epsilon>"
            using open_ballD'(1)[OF hy'] h(1) by(simp add: open_ball_def)
        qed
      qed fact
    qed
    fix K
    assume hk: "K \<in> {open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>}"
    then obtain x \<epsilon>x where hxe:
       "x \<in> S" "0 < \<epsilon>x" "K = open_ball x \<epsilon>x" by auto
    have gh:"K = (\<Union>{open_ball y (1 / real n) | y n. y \<in> U \<and> open_ball y (1 / real n) \<subseteq> K})"
    proof
      show "K \<subseteq> (\<Union> {open_ball y (1 / real n) |y n. y \<in> U \<and> open_ball y (1 / real n) \<subseteq> K})"
      proof
        fix k
        assume hkink:"k \<in> K"
        then have hkinS:"k \<in> S"
          using open_ballD'(1)[of k] by(simp add: hxe)
        obtain \<epsilon>k where hek:
          "\<epsilon>k > 0" "open_ball k \<epsilon>k \<subseteq> K"
          using mtopology_open_ball_in'[of k x] hkink
          by(auto simp: hxe)
        obtain y n where hyey:
          "y \<in> U" "k \<in> open_ball y (1 / real n)" "open_ball y (1 / real n) \<subseteq> open_ball k \<epsilon>k"
          using h0[OF hkinS hek(1)] by auto
        show "k \<in>  \<Union> {open_ball y (1 / real n) |y n. y \<in> U \<and> open_ball y (1 / real n) \<subseteq> K}"
          using hek(2) hyey by blast
      qed
    qed auto
    show "openin (topology_generated_by {open_ball y (1 / real n) |y n. y \<in> U}) K"
      unfolding openin_topology_generated_by_iff
      apply(rule generate_topology_on.UN[of "{open_ball y (1 / real n) |y n. y \<in> U \<and> open_ball y (1 / real n) \<subseteq> K}", simplified gh[symmetric]])
      apply(rule generate_topology_on.Basis) by auto
  qed
qed

lemma(in separable_metric_set) second_countable':
 "\<exists>\<O>. countable \<O> \<and> mtopology_basis \<O>"
proof -
  obtain U where hu:
   "countable U" "dense_set U"
    using separable by auto
  show ?thesis
  proof(rule countable_base_from_countable_subbase[where \<O>="{open_ball y (1 / real n) | y n. y \<in> U}",simplified second_countable_def])
    have "{open_ball y (1 / real n) |y n. y \<in> U} = (\<lambda>(y,n). open_ball y (1 / real n)) ` (U \<times> UNIV)"
      by auto
    also have "countable ..."
      using hu by auto
    finally show "countable {open_ball y (1 / real n) |y n. y \<in> U}" .
  qed (simp add: generated_by_countable_balls[OF hu] subbase_of_def)
qed

lemma(in separable_metric_set) second_countable: "second_countable mtopology"
  by(simp add: second_countable_def second_countable')

lemma(in metric_set) separable_if_second_countable:
  assumes "countable \<O>" and "mtopology_basis \<O>"
  shows "separable_metric_set S dist"
proof
  have 1:"mtopology = topology_generated_by {U \<in> \<O>. U \<noteq> {}}"
    by(simp add: topology_generated_by_without_empty[symmetric] base_is_subbase[OF assms(2),simplified subbase_of_def])
  have "\<forall>U \<in> {U \<in>\<O>. U \<noteq> {} }. \<exists>x. x \<in> U"
    by auto
  then have "\<exists>x. \<forall>U \<in> { U \<in> \<O>. U \<noteq> {} }. x U \<in> U"
    by(rule bchoice)
  then obtain x where hx:
    "\<forall>U \<in> { U \<in> \<O>. U \<noteq> {} }. x U \<in> U"
    by auto
  show "\<exists>U. countable U \<and> dense_set U"
  proof(intro exI[where x="{ x U | U.  U \<in> \<O> \<and> U \<noteq> {}}"] conjI)
    have "{x U |U. U \<in> \<O> \<and> U \<noteq> {}} = (\<lambda>U. x U) ` { U \<in> \<O>. U \<noteq> {} }"
      by auto
    also have "countable ..."
      using assms(1) by auto
    finally show "countable {x U |U. U \<in> \<O> \<and> U \<noteq> {}}" .
  next
    show "dense_set {x U |U. U \<in> \<O> \<and> U \<noteq> {}}"
      unfolding dense_set_def
    proof
      have "\<And>U. U \<in> \<O> \<Longrightarrow> U \<subseteq> topspace mtopology"
        using assms(2)[simplified base_of_def2']
        by(auto intro!: openin_subset)
      then show "{x U |U. U \<in> \<O> \<and> U \<noteq> {}} \<subseteq> S"
        using hx by(auto simp add: mtopology_topspace)
    next
      show "\<forall>xa\<in>S. \<forall>\<epsilon>>0. open_ball xa \<epsilon> \<inter> {x U |U. U \<in> \<O> \<and> U \<noteq> {}} \<noteq> {}"
      proof safe
        fix s \<epsilon>
        assume h:"s \<in> S" "(0::real) < \<epsilon>" "open_ball s \<epsilon> \<inter> {x U |U. U \<in> \<O> \<and> U \<noteq> {}} = {}"
        then have "openin mtopology (open_ball s \<epsilon>)"
          by(auto intro!: mtopology_open_ball_in)
        moreover have "open_ball s \<epsilon> \<noteq> {}"
          using h open_ball_ina by blast
        ultimately obtain U' where
          "U'\<in>\<O>" "U' \<noteq> {}" "U' \<subseteq> open_ball s \<epsilon>"
          using assms(2)[simplified base_of_def] by fastforce
        then have "x U' \<in> open_ball s \<epsilon> \<inter> {x U |U. U \<in> \<O> \<and> U \<noteq> {}}"
          using hx by blast
        with h show False
          by auto
      qed
    qed
  qed
qed

lemma metric_generates_same_topology_separable_if:
  assumes "metric_set S d" "metric_set S d'"
      and "metric_set.mtopology S d = metric_set.mtopology S d'"
      and "separable_metric_set S d"
    shows "separable_metric_set S d'"
proof -
  interpret m1: separable_metric_set S d by fact
  interpret m2: metric_set S d' by fact
  obtain \<O> where "countable \<O>" "m1.mtopology_basis \<O>"
    using m1.second_countable' by auto
  thus ?thesis
    by(auto intro!: m2.separable_if_second_countable simp: assms(3)[symmetric])
qed

lemma metric_generates_same_topology_separable:
  assumes "metric_set S d" "metric_set S d'"
      and "metric_set.mtopology S d = metric_set.mtopology S d'"
    shows "separable_metric_set S d \<longleftrightarrow> separable_metric_set S d'"
  using metric_generates_same_topology_separable_if[OF assms] metric_generates_same_topology_separable_if[OF assms(2,1) assms(3)[symmetric]]
  by auto

lemma(in metric_set) separable_if_totally_bounded:
  assumes totally_boundedS
  shows "separable_metric_set S dist"
  unfolding separable_iff_topological_separable
proof -
  have "\<exists>A. finite A \<and> A \<subseteq> S \<and> S = \<Union> ((\<lambda>a. open_ball a (1 / real (Suc n))) ` A)" for n
    using totally_boundedSD[OF assms,of "1 / Suc n"] by fastforce 
  then obtain A where A:"\<And>n. finite (A n)" "\<And>n. A n \<subseteq> S" "\<And>n. S =  \<Union> ((\<lambda>a. open_ball a (1 / real (Suc n))) ` (A n))"
    by metis
  define K where "K \<equiv> \<Union> (range A)"
  have 1: "countable K"
    using A(1) by(auto intro!: countable_UN[of _ id,simplified] simp: K_def countable_finite)
  show "separable mtopology"
    unfolding dense_set_def2 separable_def
  proof(safe intro!: exI[where x=K] 1)
    fix x and \<epsilon> :: real
    assume h: "x \<in> S" "0 < \<epsilon>"
    then obtain n where n:"1 / real (Suc n) \<le> \<epsilon>"
      by (meson nat_approx_posE order.strict_iff_not)
    then obtain y where y: "y \<in> A n" "x \<in> open_ball y (1 / real (Suc n))"
      using h(1) A(3)[of n] by auto
    then show "\<exists>y\<in>K. dist x y < \<epsilon>"
      using open_ballD[OF y(2)] n by(auto intro!: bexI[where x=y] simp: dist_sym[of y x] K_def)
  qed(use K_def A(2) in auto)
qed

lemma second_countable_metric_class_separable_set:
 "separable_metric_set (UNIV :: 'a ::{metric_space,second_countable_topology} set) dist"
proof -
  interpret m: metric_set UNIV dist
    by(rule metric_class_metric_set)
  obtain B :: "'a set set" where "countable B \<and> topological_basis B"
    using second_countable_topology_class.ex_countable_basis by auto
  then show ?thesis
    by(auto intro!: m.separable_if_second_countable[where \<O>=B] simp: topological_basis_set)
qed

lemma second_countable_euclidean[simp]:
 "second_countable (euclidean :: 'a :: {metric_space,second_countable_topology} topology)"
  by (metis euclidean_mtopology second_countable_metric_class_separable_set separable_metric_set.second_countable)

lemma separable_euclidean[simp]:
 "separable (euclidean :: 'a :: {metric_space,second_countable_topology} topology)"
  by(auto intro!: separable_if_second_countable)

lemma(in separable_metric_set) submetric_separable:
  assumes "S' \<subseteq> S"
  shows "separable_metric_set S' (submetric S' dist)"
proof -
  interpret m: metric_set S' "submetric S' dist"
    by(rule submetric_metric_set[OF assms])
  obtain \<O> where ho:"countable \<O>" "mtopology_basis \<O>"
    using second_countable' by auto
  show ?thesis
  proof(rule m.separable_if_second_countable[where \<O>="{S' \<inter> U | U. U\<in>\<O>}"])
    show "countable {S' \<inter> U |U. U \<in> \<O>}"
      using countable_image[where f="(\<inter>) S'",OF ho(1)]
      by (simp add: Setcompr_eq_image)
  next
    show "m.mtopology_basis {S' \<inter> U |U. U \<in> \<O>}"
      by(auto simp: submetric_subtopology[OF assms,symmetric] intro!: subtopology_base_of ho(2))
  qed
qed

lemma(in separable_metric_set) Lindelof_diam:
  assumes "0 < e"
  shows "\<exists>U. countable U \<and> \<Union> U = S \<and> (\<forall>u\<in>U. diam u < ennreal e)"
proof -
  have "(\<And>u. u \<in> {open_ball x (e / 3) |x. x \<in> S} \<Longrightarrow> openin mtopology u)"
    by(auto simp: openin_open_ball)
  moreover have "\<Union> {open_ball x (e / 3) |x. x \<in> S} = S"
    using open_ball_ina open_ball_subset_ofS assms by auto
  ultimately have "\<exists>U'. countable U' \<and> U' \<subseteq> {open_ball x (e / 3) |x. x \<in> S} \<and> \<Union> U' = S"
    by(rule Lindelof_of[OF second_countable,simplified mtopology_topspace]) auto
  then obtain U' where U': "countable U'" "U' \<subseteq> {open_ball x (e / 3) |x. x \<in> S}" "\<Union> U' = S"
    by auto
  show ?thesis
  proof(safe intro!: exI[where x=U'])
    fix u
    assume "u \<in> U'"
    then obtain x where u:"u = open_ball x (e / 3)"
      using U' by auto
    have "diam u \<le> ennreal (2 * (e / 3))"
      by(simp only: u diam_ball_leq)
    also have "... < ennreal e"
      by(auto intro!: ennreal_lessI assms)
    finally show "diam u < ennreal e" .
  qed(use U' in auto)
qed

subsubsection \<open> Polish Metric Spaces \<close>
locale polish_metric_set = complete_metric_set + separable_metric_set

lemma polish_class_polish_set[simp]:
 "polish_metric_set (UNIV :: 'a :: polish_space set) dist"
  using second_countable_metric_class_separable_set complete_space_complete_metric_set
  by(simp add: polish_metric_set_def)

lemma(in polish_metric_set) submetric_polish:
  assumes "M \<subseteq> S" and "closedin mtopology M"
  shows "polish_metric_set M (submetric M dist)"
  using submetric_separable[OF assms(1)] submetric_complete_iff[OF assms(1)]
  by(simp add: polish_metric_set_def assms(2))

lemma polish_metric_setI:
  assumes "complete_metric_set S d" "separable (metric_set.mtopology S d)"
  shows "polish_metric_set S d"
  using assms by(auto intro!: separable_metric_setI simp: polish_metric_set_def complete_metric_set_def)

subsubsection \<open> Compact Metric Spaces\<close>
locale compact_metric_set = metric_set +
  assumes mtopology_compact:"compact_space mtopology"
begin

context
  fixes S' :: "'b set" and dist'
  assumes S'_dist: "metric_set S' dist'"
begin

interpretation m': metric_set S' dist' by fact

lemma continuous_map_is_uniform:
  assumes "continuous_map mtopology m'.mtopology f"
  shows "uniform_continuous_map S dist S' dist' f"
  unfolding uniform_continuous_map_def[OF metric_set_axioms m'.metric_set_axioms]
proof safe
  show goal1:"\<And>x. x \<in> S \<Longrightarrow> f x \<in> S'"
    using assms by(auto simp: continuous_map_def mtopology_topspace m'.mtopology_topspace)
  fix e :: real
  assume e:"0 < e"
  { fix x
    assume x:"x \<in> S"
    then have "\<exists>\<delta>>0. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> dist' (f x) (f y) < e / 2"
      using assms(1)[simplified metric_set_continuous_map_eq[OF metric_set_axioms m'.metric_set_axioms]] half_gt_zero[OF e]
      by metis
  }
  then obtain \<delta> where delta:"\<And>x. x \<in> S \<Longrightarrow> \<delta> x > 0" "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < \<delta> x \<Longrightarrow> dist' (f x) (f y) < e / 2"
    by metis
  show "\<exists>\<delta>>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < \<delta> \<longrightarrow> dist' (f x) (f y) < e"
  proof(cases "S = {}")
    case True
    then show ?thesis
      by (auto intro!: exI[where x=1])
  next
    case nem:False
    have "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> {open_ball x (\<delta> x / 2)|x. x \<in> S} \<and> S \<subseteq> \<Union> \<F>"
      using open_ball_ina[OF _ half_gt_zero[OF delta(1)]] mtopology_compact
      by(auto intro!: compactinD simp: compact_space_def mtopology_topspace openin_open_ball)
    then obtain F where F: "finite F" "F \<subseteq> {open_ball x (\<delta> x / 2)|x. x \<in> S}" "S \<subseteq> \<Union> F"
      by auto
    have F_nem:"F \<noteq> {}"
      using nem F by auto
    have "a \<in> F \<Longrightarrow> (\<exists>x\<in>S. a = open_ball x (\<delta> x / 2))" for a
      using F(2) by auto
    then obtain xa where xa:"\<And>a. a \<in> F \<Longrightarrow> xa a \<in> S" "\<And>a. a \<in> F \<Longrightarrow> a = open_ball (xa a) (\<delta> (xa a) / 2)"
      by metis
    define \<delta>' where "\<delta>' \<equiv> (MIN a\<in>F. \<delta> (xa a) / 2)"
    have fin:"finite ((\<lambda>a. \<delta> (xa a)/ 2) ` F)"
      using F by auto
    have nemd: "((\<lambda>a. \<delta> (xa a)/ 2) ` F) \<noteq> {}"
      using F_nem by auto
    have d_pos: "\<delta>' > 0"
      by(auto simp: \<delta>'_def linorder_class.Min_gr_iff[OF fin nemd] intro!: delta(1) xa)
    show ?thesis
    proof(safe intro!: exI[where x=\<delta>'])
      fix x y
      assume h:"x \<in> S" "y \<in> S" "dist x y < \<delta>'"
      then obtain a where a:"x \<in> a" "a \<in> F"
        using F(3) by auto
      have "dist (xa a) y \<le> dist (xa a) x + dist x y"
        by(auto intro!: dist_tr xa a simp: h)
      also have "... < \<delta>' + \<delta> (xa a) / 2"
        using h xa(2)[OF a(2)] a(1) open_ballD[of x "xa a"] by fastforce
      also have "... \<le> \<delta> (xa a) / 2 + \<delta> (xa a) / 2"
      proof -
        have "\<delta>' \<le> \<delta> (xa a) / 2"
          by(simp only: \<delta>'_def,rule Min.coboundedI[OF fin]) (use a in auto)
        thus ?thesis by simp
      qed
      finally have 2:"dist (xa a) y < \<delta> (xa a)" by simp
      have "dist' (f x) (f y) \<le> dist' (f x) (f (xa a)) + dist' (f (xa a)) (f y)"
        by(auto intro!: m'.dist_tr goal1 h xa a)
      also have "... < e"
      proof -
        have [simp]:"dist (xa a) x < \<delta> (xa a)"
          using a(1) xa[OF a(2)] delta(1) open_ballD by fastforce
        have "dist' (f x) (f (xa a)) < e / 2"
          by(simp only: m'.dist_sym[where x="f x"],rule delta(2)) (auto intro!: xa a h)
        moreover have "dist' (f (xa a)) (f y) < e / 2"
          by(rule delta(2)[OF _ _ 2]) (auto intro!: h xa a)
        ultimately show ?thesis by simp
      qed
      finally show "dist' (f x) (f y) < e" .
    qed(rule d_pos)
  qed
qed

end


lemma totally_bounded: totally_boundedS
  unfolding totally_boundedS_def
proof safe
  fix \<epsilon> :: real
  assume "0 < \<epsilon>"
  define \<U> where "\<U> \<equiv> (\<lambda>a. open_ball a \<epsilon>) ` S"
  have 1: "\<And>U. U \<in> \<U> \<Longrightarrow> openin mtopology U"
    by(auto simp: \<U>_def openin_open_ball)
  have 2:"\<Union> \<U> = S"
    using open_ball_ina[OF _ \<open>0 < \<epsilon>\<close>] open_ball_subset_ofS
    by(auto simp: \<U>_def)
  obtain \<F> where "\<F> \<subseteq> \<U>" "finite \<F>" "\<Union> \<F> = S"
    using 1 2 compact_space[of mtopology,simplified mtopology_compact mtopology_topspace] by metis 
  then obtain A where "A \<subseteq> S" "finite A" "\<Union> ((\<lambda>a. open_ball a \<epsilon>) ` A) = S"
    by(simp add: \<U>_def) (metis finite_subset_image)
  thus "\<exists>A. eps_net \<epsilon> A"
    by(auto intro!: exI[where x=A] simp: eps_net_def \<open>0 < \<epsilon>\<close>)
qed

lemma sequentially_compact: sequentially_compact
  unfolding sequentially_compact_def
proof safe
  fix xn
  assume "xn \<in> sequence"
  then have xn:"\<And>n. xn n \<in> S" by auto
  have "\<not> (\<forall>x\<in>S. \<exists>e>0. finite {n. xn n \<in> open_ball x e})"
  proof
    assume contr:"\<forall>x\<in>S. \<exists>e>0. finite {n. xn n \<in> open_ball x e}"
    then obtain e where e: "\<And>x. x \<in> S \<Longrightarrow> e x > 0" "\<And>x. x \<in> S \<Longrightarrow> finite {n. xn n \<in> open_ball x (e x)}"
      by metis
    define U where "U \<equiv> {open_ball x (e x)|x. x \<in> S}"
    have "\<And>u. u \<in> U \<Longrightarrow> openin mtopology u" "topspace mtopology \<subseteq> \<Union>U"
      by(auto simp: U_def openin_open_ball mtopology_topspace open_ball_ina[OF _ e(1)])
    then obtain F where F: "finite F" "F \<subseteq> U" "S \<subseteq> \<Union> F"
      using mtopology_compact compactinD by (metis compact_space_def mtopology_topspace)
    then have "finite (\<Union>f\<in>F. {n. xn n \<in> f})"
      using e(2) by(auto simp: U_def)
    moreover have "UNIV = (\<Union>f\<in>F. {n. xn n \<in> f})"
      using F(3) xn by auto
    ultimately show False by simp
  qed
  then obtain x where x:"x \<in> S" "\<And>e. e > 0 \<Longrightarrow> infinite {n. xn n \<in> open_ball x e}"
    by metis
  have inf:"infinite {n. n > m \<and> xn n \<in> open_ball x e}" if "e > 0" for e m
  proof
    assume "finite {n. m < n \<and> xn n \<in> open_ball x e}"
    then have "finite ({..m} \<union> {n. m < n \<and> xn n \<in> open_ball x e})"
      by auto
    moreover have "{n. xn n \<in> open_ball x e} \<subseteq> {..m} \<union> {n. m < n \<and> xn n \<in> open_ball x e}"
      by auto
    ultimately show False
      using x(2)[OF that] finite_subset by blast
  qed
  define a where "a \<equiv> rec_nat (SOME n. xn n \<in> open_ball x 1) (\<lambda>n an. SOME m. m > an \<and> xn m \<in> open_ball x (1 / Suc n))"
  have an: "xn (a n) \<in> open_ball x (1 / n)" if "n > 0" for n
  proof(cases n)
    case 0
    with that show ?thesis by simp
  next
    case (Suc n)
    have [simp]:"a (Suc n) = (SOME m. m > a n \<and> xn m \<in> open_ball x (1 / Suc n))"
      by(auto simp: a_def)
    obtain m where m:"a n < m" "xn m \<in> open_ball x (1 / (Suc n))"
      using inf[of "1 / (real (Suc n))" "a n"] not_finite_existsD by auto
    have "a (Suc n) > a n \<and> xn (a (Suc n)) \<in> open_ball x (1 / (Suc n))"
      by(simp,rule someI2[of _ m]) (use m in auto)
    then show ?thesis
      by(simp only: Suc)
  qed
  have as:"strict_mono a"
    unfolding strict_mono_Suc_iff
  proof safe
    fix n
    have [simp]:"a (Suc n) = (SOME m. m > a n \<and> xn m \<in> open_ball x (1 / Suc n))"
      by(auto simp: a_def)
    obtain m where m:"a n < m" "xn m \<in> open_ball x (1 / (Suc n))"
      using inf[of "1 / (real (Suc n))" "a n"] not_finite_existsD by auto
    have "a (Suc n) > a n \<and> xn (a (Suc n)) \<in> open_ball x (1 / (Suc n))"
      by(simp,rule someI2[of _ m]) (use m in auto)
    thus "a n < a (Suc n)" by simp
  qed
  show "\<exists>a. strict_mono a \<and> convergent_inS (xn \<circ> a)"
    unfolding convergent_inS_def converge_to_inS_def2'
  proof(safe intro!: exI[where x=a] exI[where x=x])
    fix e :: real
    assume "0 < e"
    then obtain N ::nat where N: "N > 0" "1 / N < e"
      by (meson nat_approx_posE zero_less_Suc)
    show "\<exists>N. \<forall>n\<ge>N. (xn \<circ> a) n \<in> open_ball x e"
    proof(safe intro!: exI[where x=N])
      fix n
      assume n:"n \<ge> N"
      show "(xn \<circ> a) n \<in> open_ball x e"
        using order.trans[OF open_ball_le[of "1 / n"] open_ball_le[of "1 / N" e]] N n an[of n] inverse_of_nat_le
        by auto
    qed
  qed(auto simp: simp: as  x xn)
qed

lemma polish: "polish_metric_set S dist"
  using separable_if_totally_bounded[OF totally_bounded]
  by(simp add: polish_metric_set_def complete_metric_set_def complete_metric_set_axioms_def separable_metric_set_def)
    (meson Cauchy_inS_def converge_if_Cauchy_and_subconverge convergent_inS_def sequentially_compact sequentially_compact_def)

sublocale polish_metric_set
  by(rule polish)

end

lemma(in metric_set) ex_lebesgue_number:
  assumes "S \<noteq> {}" sequentially_compact "\<And>u. u \<in> U \<Longrightarrow> openin mtopology u" "S \<subseteq> \<Union> U"
  shows "\<exists>d>0. \<forall>a\<subseteq>S. diam a < ennreal d \<longrightarrow> (\<exists>u\<in>U. a \<subseteq> u)"
proof(rule ccontr)
  assume "\<not> (\<exists>d>0. \<forall>a\<subseteq>S. diam a < ennreal d \<longrightarrow> (\<exists>u\<in>U. a \<subseteq> u))"
  then have "\<And>n. \<exists>a\<subseteq>S. diam a < ennreal (1 / Suc n) \<and> (\<forall>x\<in>U. \<not> a \<subseteq> x)" by auto
  then obtain An where an: "\<And>n. An n \<subseteq> S" "\<And>n. diam (An n) < ennreal (1 / Suc n)" "\<And>n u. u \<in> U \<Longrightarrow> \<not> (An n) \<subseteq> u"
    by metis
  have "An n \<noteq> {}" for n
  proof
    assume "An n = {}"
    then have "U = {} \<or> (\<forall>u\<in>U. u = {})"
      using an(3)[of _ n] by auto
    thus False
      using assms(1,4) by blast
  qed
  then obtain xn where xn:"\<And>n. xn n \<in> An n"
    by (meson ex_in_conv)
  then have xn':"\<And>n. xn n \<in> S" using an by auto
  then obtain a x where ax:"strict_mono a" "converge_to_inS (xn \<circ> a) x"
    using assms(2) by(fastforce simp: sequentially_compact_def convergent_inS_def)
  then have x: "x \<in> S" by(auto simp: converge_to_inS_def)
  then obtain u where u:"x \<in> u" "u \<in> U"
    using assms(4) by auto
  obtain e where e:"e > 0" "open_ball x e \<subseteq> u"
    using assms(3)[OF u(2)] u(1) mtopology_openin_iff by fastforce
  obtain n ::nat where n: "1 / Suc n < e / 2"
    using e(1) half_gt_zero nat_approx_posE by blast
  obtain n' where n':"\<And>n. n \<ge> n' \<Longrightarrow> xn (a n) \<in> open_ball x (e / 2)"
    using e(1) ax(2) by(auto simp: converge_to_inS_def2') (meson half_gt_zero)
  define n0 where "n0 \<equiv> max (a (Suc n)) (a n')"
  have n0:"1 / Suc n0 < e / 2" "xn n0 \<in> open_ball x (e / 2)"
  proof -
    have "Suc n0 \<ge> Suc n"
      using seq_suble[OF ax(1),of "Suc n"]  by (simp add: n0_def)
    hence "1 / Suc n0 \<le> 1 / Suc n"
      using inverse_of_nat_le by blast
    thus "1 / Suc n0 < e / 2"
      using n by auto
    show "xn n0 \<in> open_ball x (e / 2)"
      by (cases "a (Suc n) \<le> a n'") (auto intro!: n' simp: n0_def ax(1) strict_mono_less_eq)
  qed
  have "An n0 \<subseteq> open_ball x e"
    unfolding open_ball_def
  proof safe
    fix y
    assume y:"y \<in> An n0"
    have "dist x y \<le> dist x (xn n0) + dist (xn n0) y"
      using y xn' an by(auto intro!: dist_tr simp: x)
    also have "... < e / 2 + dist (xn n0) y"
      using open_ballD[OF n0(2)] by auto
    also have "... \<le> e / 2 + 1 / Suc n0"
      using xn[of n0] xn' y an by(auto intro!: diam_is_sup'[OF _ _ order.strict_implies_order[OF an(2)[of n0]],simplified])
    also have "... < e"
      using n0(1) by auto
    finally show "y \<in> (if x \<in> S then {xa \<in> S. dist x xa < e} else {})"
      using an(1) x y by auto
  qed
  hence "An n0 \<subseteq> u"
    using e by auto
  with an(3)[OF u(2)] show False by auto
qed

lemma(in metric_set) sequentially_compact_iff1:
  "sequentially_compact \<longleftrightarrow> totally_boundedS \<and> complete_metric_set S dist"
proof safe
  assume h:sequentially_compact
  then show totally_boundedS
    using Cauchy_if_convergent_inS by(fastforce simp: totally_boundedS_iff sequentially_compact_def)
  show "complete_metric_set S dist"
  proof
    fix xn
    assume 1:"Cauchy_inS xn"
    with h obtain a x where 2:"strict_mono a" "converge_to_inS (xn \<circ> a) x"
      by(fastforce dest: Cauchy_inS_dest1 simp: sequentially_compact_def convergent_inS_def)
    thus "convergent_inS xn"
      by(auto simp: convergent_inS_def converge_if_Cauchy_and_subconverge[OF 2 1] intro!: exI[where x=x])
  qed
next
  assume h:"totally_boundedS" "complete_metric_set S dist"
  show sequentially_compact
    unfolding sequentially_compact_def
  proof safe
    fix xn
    assume "xn \<in> sequence"
    then obtain a where a:"strict_mono a" "Cauchy_inS (xn \<circ> a)"
      using h by(auto simp: totally_boundedS_iff) 
    thus "\<exists>a. strict_mono a \<and> convergent_inS (xn \<circ> a)"
      using h by(auto intro!: exI[where x=a] simp: complete_metric_set_def complete_metric_set_axioms_def)
  qed
qed

lemma(in metric_set) sequentially_compact_compact:
  assumes sequentially_compact
  shows "compact_metric_set S dist"
proof
  show "compact_space mtopology"
  proof(cases "S = {}")
    case True
    have [simp]:"topspace mtopology = {}"
      by(simp add: mtopology_topspace,fact)
    show ?thesis
      by(auto simp: compact_space intro!: exI[where x="{}"])
  next
    case 1:False
    {
      fix U
      assume h:"\<And>u. u \<in> U \<Longrightarrow> openin mtopology u" "S \<subseteq> \<Union> U"
      obtain d where d:"d > 0" "\<And>a. a \<subseteq> S \<Longrightarrow> diam a < ennreal d \<Longrightarrow> \<exists>u\<in>U. a \<subseteq> u"
        using ex_lebesgue_number[OF 1 assms h] by metis
      obtain B where B:"finite B" "B \<subseteq> S" "S = (\<Union>a\<in>B. open_ball a (d / 3))"
        using totally_boundedSD[of "d / 3"] d(1) assms
        by(auto simp: sequentially_compact_iff1)
      have "\<exists>u\<in>U. open_ball b (d / 3) \<subseteq> u" if "b \<in> B" for b
        using open_ballD' d(1) by(auto intro!: d(2) order.strict_trans1[OF diam_ball_leq[of b "d / 3"]] simp: ennreal_less_iff)
      then obtain u where u:"\<And>b. b \<in> B \<Longrightarrow> u b \<in> U" "\<And>b. b \<in> B \<Longrightarrow> open_ball b (d / 3) \<subseteq> u b"
        by metis
      have "\<exists>F. finite F \<and> F \<subseteq> U \<and> S \<subseteq> (\<Union> F)"
        using B u by(fastforce intro!: exI[where x="u ` B"])
    }
    thus ?thesis
      by (simp add: compact_space_alt mtopology_topspace)
  qed
qed

corollary(in metric_set) compact_iff_sequentially_compact:
"compact_space mtopology \<longleftrightarrow> sequentially_compact"
  using compact_metric_set.sequentially_compact sequentially_compact_compact compact_metric_set_axioms_def compact_metric_set_def metric_set_axioms
  by blast

corollary(in metric_set) compact_iff2:
"compact_space mtopology \<longleftrightarrow> totally_boundedS \<and> complete_metric_set S dist"
  by(simp add: compact_iff_sequentially_compact sequentially_compact_iff1)

corollary(in complete_metric_set) compactin_closed_iff:
  assumes "closedin mtopology C"
  shows "compactin mtopology C \<longleftrightarrow> totally_bounded_on C"
proof -
  from assms have C:"C \<subseteq> S"
    using mtopology_closedin_iff by blast
  then interpret C: complete_metric_set C "submetric C dist"
    by(auto simp: submetric_complete_iff assms)
  show ?thesis
    by(simp add: compactin_subspace submetric_subtopology[OF C] totally_bounded_on_submetric[OF C] mtopology_topspace C  C.compact_iff2 C.complete_metric_set_axioms)
qed

subsubsection \<open> Completion \<close>
context metric_set
begin

abbreviation "Cauchys \<equiv> Collect Cauchy_inS"

definition Cauchy_r :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set" where
"Cauchy_r \<equiv> {(xn,yn)|xn yn. Cauchy_inS xn \<and> Cauchy_inS yn \<and> (\<lambda>n. dist (xn n) (yn n)) \<longlonglongrightarrow> 0}"

lemma Cauchy_r_equiv[simp]: "equiv Cauchys Cauchy_r"
proof(rule equivI)
  show "refl_on Cauchys Cauchy_r"
    by(auto simp: refl_on_def Cauchy_r_def)
next
  show "sym Cauchy_r"
    using dist_sym by(auto simp: sym_def Cauchy_r_def)
next
  show "trans Cauchy_r"
  proof(rule transI)
    show "\<And>x y z. (x, y) \<in> Cauchy_r \<Longrightarrow> (y, z) \<in> Cauchy_r \<Longrightarrow> (x, z) \<in> Cauchy_r"
      unfolding Cauchy_r_def
    proof safe
      fix xn yn zn
      assume h:"Cauchy_inS xn" "Cauchy_inS yn" "Cauchy_inS zn"
               "(\<lambda>n. dist (xn n) (yn n)) \<longlonglongrightarrow> 0" "(\<lambda>n. dist (yn n) (zn n)) \<longlonglongrightarrow> 0"
      then show "\<exists>xn' yn'. (xn, zn) = (xn', yn') \<and> Cauchy_inS xn' \<and> Cauchy_inS yn' \<and> (\<lambda>n. dist (xn' n) (yn' n)) \<longlonglongrightarrow> 0"
        by(auto intro!: tendsto_0_le[OF tendsto_add_zero[OF h(4,5)],of _ 1] dist_tr eventuallyI simp: dist_geq0 Cauchy_inS_dest1)
    qed
  qed
qed

abbreviation S_completion :: "(nat \<Rightarrow> 'a) set set" ("S\<^sup>*") where
"S_completion \<equiv> Cauchys // Cauchy_r"

lemma S_c_represent:
  assumes "X \<in> S\<^sup>*"
  obtains xn where "xn \<in> X" "Cauchy_inS xn"
  using equiv_Eps_in[OF _ assms] equiv_Eps_preserves[OF _ assms] by auto

lemma Cauchy_inS_ignore_initial_eq:
  assumes "Cauchy_inS xn"
  shows "(xn, (\<lambda>n. xn (n + k))) \<in> Cauchy_r"
  by(auto simp: Cauchy_r_def Cauchy_inS_ignore_initial[OF assms] assms,insert assms)
    (auto simp: LIMSEQ_def dist_real_def dist_geq0 Cauchy_inS_def,metis add.commute trans_le_add2)

corollary Cauchy_inS_r: "a \<in> S \<Longrightarrow> (\<lambda>n. a, \<lambda>n. a) \<in> Cauchy_r"
  by(auto intro!: Cauchy_inS_ignore_initial_eq Cauchy_inS_const)

abbreviation dist_completion' :: "[nat \<Rightarrow> 'a, nat \<Rightarrow> 'a] \<Rightarrow> real" where
"dist_completion' xn yn \<equiv> lim (\<lambda>n. dist (xn n) (yn n))"

lemma dist_of_completion_congruent2: "dist_completion' respects2 Cauchy_r"
proof(safe intro!: congruent2_commuteI[OF Cauchy_r_equiv])
  fix xn yn zn
  assume h:"(xn,yn) \<in> Cauchy_r" "Cauchy_inS zn"
  then have h':"Cauchy_inS xn" "Cauchy_inS yn" "(\<lambda>n. dist (xn n) (yn n)) \<longlonglongrightarrow> 0"
    by(auto simp: Cauchy_r_def)
  have 1:"(\<lambda>n. dist (zn n) (xn n)) \<longlonglongrightarrow> lim (\<lambda>n. dist (zn n) (xn n))"
    using Cauchy_inS_dist_convergent[OF h(2) h'(1)] by(simp add: convergent_LIMSEQ_iff)
  have 2:"(\<lambda>n. dist (zn n) (yn n)) \<longlonglongrightarrow> lim (\<lambda>n. dist (zn n) (xn n))"
    using h(2) h'(1,2) dist_tr_abs[of "zn _" "xn _" "yn _",simplified abs_diff_le_iff]
    by(auto intro!: real_tendsto_sandwich[OF _ _ tendsto_diff[OF 1 h'(3),simplified] tendsto_add[OF 1 h'(3),simplified]] eventuallyI dist_tr dest: Cauchy_inS_dest1) (simp add: Cauchy_inS_dest1 add.commute diff_le_eq)
  show "dist_completion' zn xn = dist_completion' zn yn"
    using 1 2 by(auto dest: limI)
qed(auto simp: dist_sym)

definition dist_completion :: "[(nat \<Rightarrow> 'a) set, (nat \<Rightarrow> 'a) set] \<Rightarrow> real" ("dist\<^sup>*") where
"dist\<^sup>* X Y \<equiv> (if X \<in> S\<^sup>* \<and> Y \<in> S\<^sup>* then dist_completion' (SOME xn. xn \<in> X) (SOME yn. yn \<in> Y) else 0)"

lemma dist_c_def:
  assumes "xn \<in> X" "yn \<in> Y" "X \<in> S\<^sup>*" "Y \<in> S\<^sup>*"
  shows "dist\<^sup>* X Y = dist_completion' xn yn"
  by(auto simp: assms dist_completion_def,rule someI2[of "\<lambda>x. x \<in> X",OF assms(1)],rule someI2[of "\<lambda>x. x \<in> Y",OF assms(2)])
    (auto simp: congruent2D[OF dist_of_completion_congruent2 quotient_eq_iff[OF _ assms(3,3,1),simplified] quotient_eq_iff[OF _ assms(4,4,2),simplified]])


lemma completion_metric_set: "metric_set S\<^sup>* dist\<^sup>*"
proof
  fix X Y
  consider "X \<in> S\<^sup>*" "Y \<in> S\<^sup>*" | "X \<notin> S\<^sup>*" | "Y \<notin> S\<^sup>*" by blast
  then show "0 \<le> dist\<^sup>* X Y"
  proof cases
    case 1
    then obtain xn yn where h: "xn \<in> X" "yn \<in> Y" "Cauchy_inS xn" "Cauchy_inS yn"
      by (meson S_c_represent)
    with 1 show ?thesis
      by(auto simp: dist_c_def intro!: Lim_bounded2[OF Cauchy_inS_dist_convergent[OF h(3,4),simplified convergent_LIMSEQ_iff]] dist_geq0)
  qed(auto simp: dist_completion_def)
next
  fix X Y
  show "dist\<^sup>* X Y = dist\<^sup>* Y X"
    by(auto simp: dist_completion_def dist_sym)
next
  fix X Y
  assume h:"X \<in> S\<^sup>*" "Y \<in> S\<^sup>*"
  then obtain xn yn where h': "xn \<in> X" "yn \<in> Y" "Cauchy_inS xn" "Cauchy_inS yn"
    by (meson S_c_represent)
  show "X = Y \<longleftrightarrow> dist\<^sup>* X Y = 0"
  proof
    assume "X = Y"
    then show "dist\<^sup>* X Y = 0"
      using h' h by(auto simp: dist_c_def)
  next
    assume "dist\<^sup>* X Y = 0"
    then have "(xn, yn) \<in> Cauchy_r"
      using h h' convergent_LIMSEQ_iff[THEN iffD1,OF Cauchy_inS_dist_convergent[OF h'(3,4)]]
      by(auto simp: dist_c_def Cauchy_r_def)
    thus "X = Y"
      by(simp add: quotient_eq_iff[OF _ h h'(1,2)])
  qed
next
  fix X Y Z
  assume h:"X \<in> S\<^sup>*" "Y \<in> S\<^sup>*" "Z \<in> S\<^sup>*"
  then obtain xn yn zn where h': "xn \<in> X" "yn \<in> Y" "zn \<in> Z" "Cauchy_inS xn" "Cauchy_inS yn" "Cauchy_inS zn"
    by (meson S_c_represent)
  have "dist\<^sup>* X Z = dist_completion' xn zn"
    using h h' by(simp add: dist_c_def)
  also have "... \<le> lim (\<lambda>n. dist (xn n) (yn n) + dist (yn n) (zn n))"
    using h' by(auto intro!: lim_mono[OF _  convergent_LIMSEQ_iff[THEN iffD1,OF Cauchy_inS_dist_convergent[OF h'(4,6)]] convergent_LIMSEQ_iff[THEN iffD1,OF convergent_add[OF Cauchy_inS_dist_convergent[OF h'(4,5)] Cauchy_inS_dist_convergent[OF h'(5,6)]]]] dist_tr dest: Cauchy_inS_dest1)
  also have "... = dist_completion' xn yn + dist_completion' yn zn"
    using tendsto_add[OF convergent_LIMSEQ_iff[THEN iffD1,OF Cauchy_inS_dist_convergent[OF h'(4,5)]] convergent_LIMSEQ_iff[THEN iffD1,OF Cauchy_inS_dist_convergent[OF h'(5,6)]]]
    by(simp add: limI)
  also have "... = dist\<^sup>* X Y + dist\<^sup>* Y Z"
    using h h' by(simp add: dist_c_def)
  finally show "dist\<^sup>* X Z \<le> dist\<^sup>* X Y + dist\<^sup>* Y Z" .
qed(simp add: dist_completion_def)

interpretation c:metric_set "S\<^sup>*" "dist\<^sup>*"
  by(rule completion_metric_set)

definition into_S_c :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) set" where
"into_S_c a \<equiv> Cauchy_r `` {(\<lambda>n. a)}"

lemma into_S_c_in:
  assumes "a \<in> S"
  shows "(\<lambda>n. a) \<in> into_S_c a"
  using Cauchy_inS_const[OF assms] Cauchy_inS_r[OF assms]
  by(auto simp: into_S_c_def)

lemma into_S_c_into:
  assumes "a \<in> S"
  shows "into_S_c a \<in> S\<^sup>*"
  by(auto simp: into_S_c_def intro!: quotientI Cauchy_if_convergent_inS convergent_inS_const assms)

lemma into_S_inj: "inj_on into_S_c S"
proof
  fix x y
  assume "x \<in> S" "y \<in> S" "into_S_c x = into_S_c y"
  with eq_equiv_class_iff[THEN iffD1,OF Cauchy_r_equiv _ _ this(3)[simplified into_S_c_def]]
  have "(\<lambda>n. x, \<lambda>n. y) \<in> Cauchy_r"
    by(auto simp: Cauchy_if_convergent_inS convergent_inS_const)
  thus "x = y"
    using dist_0[OF \<open>x \<in> S\<close> \<open>y \<in> S\<close>]
    by(auto simp: Cauchy_r_def LIMSEQ_const_iff)
qed

lemma dist_into_S_c:
  assumes "x \<in> S" "y \<in> S"
  shows "dist\<^sup>* (into_S_c x) (into_S_c y) = dist x y"
  using into_S_c_in[OF assms(1)] into_S_c_in[OF assms(2)] into_S_c_into[OF assms(1)] into_S_c_into[OF assms(2)]
  by(simp add: dist_c_def)

lemma S_c_isometry:
 "c.ed into_S_c S = dist"
  by standard+ (auto simp: c.embed_dist_on_def dist_into_S_c dist_notin dist_notin')

corollary mtopology_embedding_S_c_map:
 "homeomorphic_map mtopology (subtopology c.mtopology (into_S_c ` S)) into_S_c"
  using into_S_c_into by(auto intro!: c.embed_dist_topology_homeomorphic_map[OF _ into_S_inj,simplified S_c_isometry])

corollary mtopology_embedding_S_c:
 "mtopology homeomorphic_space subtopology c.mtopology (into_S_c ` S)"
  using mtopology_embedding_S_c_map homeomorphic_space by blast

lemma into_S_c_image_dense: "c.dense_set (into_S_c ` S)"
  unfolding c.dense_set_def2'
proof safe
  fix X
  assume X:"X \<in> S\<^sup>*"
  from S_c_represent[OF this] obtain xn where xn:"xn \<in> X" "Cauchy_inS xn"
    by auto
  show "\<exists>f\<in>UNIV \<rightarrow> into_S_c ` S. c.converge_to_inS f X"
  proof(safe intro!: bexI[where x="\<lambda>n. into_S_c (xn n)"])
    show "c.converge_to_inS (\<lambda>n. into_S_c (xn n)) X"
      unfolding c.converge_to_inS_def2
    proof safe
      fix e :: real
      assume e:"e > 0"
      then obtain N where N:"\<And>n m. n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> dist (xn n) (xn m) < e / 2"
        using xn(2) by (meson Cauchy_inS_def half_gt_zero)
      show "\<exists>N. \<forall>n\<ge>N. dist\<^sup>* (into_S_c (xn n)) X < e"
      proof(safe intro!: exI[where x=N])
        fix n
        assume n:"N \<le> n"
        have "dist\<^sup>* (into_S_c (xn n)) X = dist_completion' (\<lambda>na. xn n) xn"
          by(rule dist_c_def[OF into_S_c_in[OF Cauchy_inS_dest1[OF xn(2),of n]] xn(1) into_S_c_into[OF Cauchy_inS_dest1[OF xn(2),of n]] X])
        also have "... \<le> e / 2"
          by(rule Lim_bounded[OF Cauchy_inS_dist_convergent[OF Cauchy_inS_const[OF  Cauchy_inS_dest1[OF xn(2),of n]] xn(2),simplified convergent_LIMSEQ_iff],of N "e/2"],auto dest: N[OF n])
        also have "... < e"
          using e by auto
        finally show "dist\<^sup>* (into_S_c (xn n)) X < e" .
      qed
    qed(auto simp: Cauchy_inS_dest1[OF xn(2)] into_S_c_into X)
  qed(auto simp: Cauchy_inS_dest1[OF xn(2)] into_S_c_into)
qed (use into_S_c_into in auto)

lemma completion_complete:"complete_metric_set S\<^sup>* dist\<^sup>*"
proof
  fix Xn
  assume h:"c.Cauchy_inS Xn"
  have "\<And>n. \<exists>xn\<in>S. dist\<^sup>* (Xn n) (into_S_c xn) < 1 / (Suc n)"
    using into_S_c_image_dense c.Cauchy_inS_dest1[OF h]
    by(auto simp: c.dense_set_def2)
  then obtain xn where xn: "\<And>n. xn n \<in> S" "\<And>n.  dist\<^sup>* (Xn n) (into_S_c (xn n)) < 1 / (Suc n)"
    by metis
  have xnC:"Cauchy_inS xn"
    unfolding Cauchy_inS_def
  proof safe
    fix e :: real
    assume e:"0 < e"
    then obtain N1 where N1: "1 / Suc N1 < e / 3"
      by (meson nat_approx_posE zero_less_divide_iff zero_less_numeral)
    obtain N2 where N2: "\<And>n m. n \<ge> N2 \<Longrightarrow> m \<ge> N2 \<Longrightarrow> dist\<^sup>* (Xn n) (Xn m) < e / 3"
      using e h by(simp only: c.Cauchy_inS_def) (meson zero_less_divide_iff zero_less_numeral)
    show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. dist (xn n) (xn m) < e"
    proof(safe intro!: exI[where x="max N1 N2"])
      fix n m
      assume "max N1 N2 \<le> n" "max N1 N2 \<le> m"
      hence n: "N1 \<le> n" "N2 \<le> n"
        and m: "N1 \<le> m" "N2 \<le> m" by auto
      have "dist (xn n) (xn m) = c.ed into_S_c S (xn n) (xn m)"
        by(simp add: S_c_isometry)
      also have "... = dist\<^sup>* (into_S_c (xn n)) (into_S_c (xn m))"
        using xn by(simp add: c.embed_dist_on_def)
      also have "... \<le> dist\<^sup>* (into_S_c (xn n)) (Xn n) + dist\<^sup>* (Xn n) (Xn m) + dist\<^sup>* (Xn m) (into_S_c (xn m))"
        using c.dist_tr[OF into_S_c_into[OF xn(1)[of n]] c.Cauchy_inS_dest1[OF h,of m] into_S_c_into[OF xn(1)[of m]]] c.dist_tr[OF into_S_c_into[OF xn(1)[of n]] c.Cauchy_inS_dest1[OF h,of n] c.Cauchy_inS_dest1[OF h,of m]]
        by simp
      also have "... < 1 / Suc n + e / 3 + 1 / Suc m"
        using N2[OF n(2) m(2)] xn(2)[of m] xn(2)[of n,simplified c.dist_sym[of "Xn n"]] by auto
      also have "... < e"
      proof -
        have "1 / Suc n \<le> 1 / Suc N1" "1 / Suc m \<le> 1 / Suc N1"
          using n m inverse_of_nat_le by blast+
        thus ?thesis
          using N1 by linarith
      qed
      finally show "dist (xn n) (xn m) < e" .
    qed
  qed(simp add: xn)
  show "c.convergent_inS Xn"
    unfolding c.convergent_inS_def c.converge_to_inS_def2
  proof(safe intro!:  exI[where x="Cauchy_r `` {xn}"] quotientI xnC)
    fix e :: real
    assume e:"0 < e"
    then obtain N1 where N1: "1 / Suc N1 < e / 2"
      by (meson nat_approx_posE zero_less_divide_iff zero_less_numeral)
    hence 1:"dist\<^sup>* (Xn n) (into_S_c (xn n)) < e / 2" if "n \<ge> N1" for n
    proof -
      have "1 / Suc n \<le> 1 / Suc N1"
        using that inverse_of_nat_le by blast
      thus ?thesis
        using xn(2)[of n] N1 by linarith
    qed
    then obtain N2 where N2:"\<And>n m. n \<ge> N2 \<Longrightarrow> m \<ge> N2 \<Longrightarrow> dist (xn n) (xn m) < e / 3"
      using xnC e by (meson Cauchy_inS_def zero_less_divide_iff zero_less_numeral) 
    have 2:"dist\<^sup>* (into_S_c (xn n)) (Cauchy_r `` {xn}) < e / 2" if "n \<ge> N2" for n
    proof -
      have "dist\<^sup>* (into_S_c (xn n)) (Cauchy_r `` {xn}) = dist_completion' (\<lambda>m. xn n) xn"
        using dist_c_def[OF into_S_c_in[OF Cauchy_inS_dest1[OF xnC,of n]] equiv_class_self[OF Cauchy_r_equiv,of xn] into_S_c_into[OF Cauchy_inS_dest1[OF xnC,of n]]] xnC
        by (simp add: quotientI)
      also have "... \<le> e / 3"
        by(rule Lim_bounded[OF Cauchy_inS_dist_convergent[OF Cauchy_inS_const[OF  Cauchy_inS_dest1[OF xnC,of n]] xnC,simplified convergent_LIMSEQ_iff],of N2 "e/3"], auto dest: N2[OF that])
      also have "... < e / 2" using e by simp
      finally show "dist\<^sup>* (into_S_c (xn n)) (Cauchy_r `` {xn}) < e / 2" .
    qed
    show "\<exists>N. \<forall>n\<ge>N. dist\<^sup>* (Xn n) (Cauchy_r `` {xn}) < e"
    proof(safe intro!: exI[where x="max N1 N2"])
      fix n
      assume "max N1 N2 \<le> n"
      then have n:"n \<ge> N1" "n \<ge> N2" by auto
      show "dist\<^sup>* (Xn n) (Cauchy_r `` {xn}) < e"
        using c.dist_tr[OF c.Cauchy_inS_dest1[OF h,of n] into_S_c_into[OF Cauchy_inS_dest1[OF xnC],of n] quotientI[of xn]] xnC 1[OF n(1)] 2[OF n(2)]
        by auto
    qed
  qed(use c.Cauchy_inS_dest1[OF h] in auto)
qed

lemma dense_set_c_dense:
  assumes "dense_set U"
  shows "c.dense_set (into_S_c ` U)"
  unfolding c.dense_set_def2
proof safe
  fix X and e :: real
  assume h:"X \<in> S\<^sup>*" "0 < e"
  then obtain xn where xn:"xn \<in> X" "Cauchy_inS xn"
    by(auto dest: S_c_represent)
  obtain y where y:"y \<in> S" "dist\<^sup>* X (into_S_c y) < e / 2"
    using h into_S_c_image_dense half_gt_zero[OF h(2)] by(simp only: c.dense_set_def2) blast
  obtain z where z:"z \<in> U" "dist y z < e / 2"
    using half_gt_zero[OF h(2)] y(1) assms by(simp only: dense_set_def2) blast
  show "\<exists>y\<in>into_S_c ` U. dist\<^sup>* X y < e"
  proof(rule bexI[OF _ imageI[OF z(1)]])
    have "dist\<^sup>* X (into_S_c z) \<le> dist\<^sup>* X (into_S_c y) + dist\<^sup>* (into_S_c y) (into_S_c z)"
      using z(1) assms by(auto intro!: c.dist_tr h into_S_c_into y simp: dense_set_def)
    also have "... =  dist\<^sup>* X (into_S_c y) + dist y z"
      using z(1) assms y(1) dist_into_S_c[of y z] by(auto simp: dense_set_def)
    also have "... < e"
      using y(2) z(2) by simp
    finally show "dist\<^sup>* X (into_S_c z) < e" .
  qed
qed(insert assms, auto simp: dense_set_def intro!: into_S_c_into)

end

lemma(in separable_metric_set) completion_polish: "polish_metric_set S\<^sup>* dist\<^sup>*"
proof -
  interpret c:complete_metric_set "S\<^sup>*" "dist\<^sup>*"
    by(rule completion_complete)
  show ?thesis
  proof
    obtain U where U: "countable U" "dense_set U"
      using separable by blast
    show "\<exists>U. countable U \<and> c.dense_set U"
      using U by(auto intro!: exI[where x="into_S_c ` U"] dense_set_c_dense)
  qed
qed

subsection  \<open>Discrete Distance\<close>
definition discrete_dist :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
"discrete_dist S \<equiv> (\<lambda>a b. if a \<in> S \<and> b \<in> S \<and> a \<noteq> b then 1 else 0)"

lemma
  assumes "a \<in> S" and "b \<in> S"
  shows discrete_dist_iff_1: "discrete_dist S a b = 1 \<longleftrightarrow> a \<noteq> b"
    and discrete_dist_iff_0: "discrete_dist S a b = 0 \<longleftrightarrow> a = b"
  using assms by(auto simp: discrete_dist_def)

lemma discrete_dist_metric:
 "metric_set S (discrete_dist S)"
  by(auto simp: discrete_dist_def metric_set_def)

lemma
 shows discrete_dist_ball_ge1: "x \<in> S \<Longrightarrow> 1 < \<epsilon> \<Longrightarrow> metric_set.open_ball S (discrete_dist S) x \<epsilon> = S"
 and discrete_dist_ball_leq1: "x \<in> S \<Longrightarrow> 0 < \<epsilon> \<Longrightarrow> \<epsilon> \<le> 1 \<Longrightarrow> metric_set.open_ball S (discrete_dist S) x \<epsilon> = {x}"
   apply(auto simp: metric_set.open_ball_def[OF discrete_dist_metric],simp_all add: discrete_dist_def)
  using less_le_not_le by fastforce
  

lemma discrete_dist_complete_metric:
 "complete_metric_set S (discrete_dist S)"
proof -
  interpret m: metric_set S "discrete_dist S"
    by(rule discrete_dist_metric)
  show ?thesis
  proof
    fix f
    assume h:"m.Cauchy_inS f"
    then have "\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. f n \<in> m.open_ball x \<epsilon>"
      by(auto simp: m.Cauchy_inS_def2')
    from this[of 1] obtain x N where hxn:
     "x \<in> S" "\<forall>n\<ge>N. f n \<in> m.open_ball x 1"
      by auto
    hence "\<And>n. n \<ge> N \<Longrightarrow> f n = x"
      using discrete_dist_ball_leq1[of x S 1] by auto
    thus "m.convergent_inS f"
      unfolding m.convergent_inS_def using h hxn(1)
      by(auto intro!: bexI[where x=x] exI[where x=N] simp:m.converge_to_inS_def2' m.Cauchy_inS_def)
  qed
qed

lemma discrete_dist_dense_set:
 "metric_set.dense_set S (discrete_dist S) U \<longleftrightarrow> S = U"
proof -
  interpret m: metric_set S "discrete_dist S"
    by(rule discrete_dist_metric)
  show ?thesis
  proof
    assume h:"m.dense_set U"
    show "S = U"
    proof safe
      fix x
      assume hx:"x \<in> S"
      then have "\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> m.open_ball x \<epsilon> \<inter> U \<noteq> {}"
        using h by(simp add: m.dense_set_def)
      hence "m.open_ball x 1 \<inter> U \<noteq> {}" by auto
      thus "x \<in> U"
        using discrete_dist_ball_leq1[OF hx,of 1]
        by auto
    next
      show "\<And>x. x \<in> U \<Longrightarrow> x \<in> S"
        using h by(auto simp: m.dense_set_def)
    qed
  next
    show "S = U \<Longrightarrow> m.dense_set U "
      using m.dense_set_S by auto
  qed
qed

lemma discrete_dist_separable_iff:
 "separable_metric_set S (discrete_dist S) \<longleftrightarrow> countable S"
proof -
  interpret m: metric_set S "discrete_dist S"
    by(rule discrete_dist_metric)
  show ?thesis
  proof
    assume "separable_metric_set S (discrete_dist S)"
    then obtain U where "countable U" "m.dense_set U"
      by(auto simp: separable_metric_set_def separable_metric_set_axioms_def)
    thus "countable S"
      using discrete_dist_dense_set[of S] by auto
  next
    assume "countable S"
    then show "separable_metric_set S (discrete_dist S)"
      by(auto simp: separable_metric_set_def separable_metric_set_axioms_def intro!:exI[where x=S] m.dense_set_S discrete_dist_metric)
  qed
qed

lemma discrete_dist_polish_iff: "polish_metric_set S (discrete_dist S) \<longleftrightarrow> countable S"
  using discrete_dist_separable_iff[of S] discrete_dist_complete_metric[of S]
  by(auto simp: polish_metric_set_def)


lemma discrete_dist_topology_x:
  assumes "x \<in> S"
  shows "openin (metric_set.mtopology S (discrete_dist S)) {x}"
proof -
  interpret m: metric_set S "discrete_dist S"
    by(rule discrete_dist_metric)
  show ?thesis
    by(auto simp: m.mtopology_open_ball_in[OF assms,of 1, simplified discrete_dist_ball_leq1[OF assms]])
qed

lemma discrete_dist_topology:
 "openin (metric_set.mtopology S (discrete_dist S)) U \<longleftrightarrow> U \<subseteq> S"
proof -
  interpret m: metric_set S "discrete_dist S"
    by(rule discrete_dist_metric)
  show ?thesis
  proof
    show "openin m.mtopology U \<Longrightarrow> U \<subseteq> S"
      using m.mtopology_topspace
      by(auto simp: topspace_def)
  next
    assume "U \<subseteq> S"
    then have "\<And>x. x \<in> U \<Longrightarrow> openin m.mtopology {x}"
      by(auto simp: discrete_dist_topology_x)
    hence "openin m.mtopology (\<Union>{{x} | x. x \<in> U})"
      by auto
    moreover have "\<Union>{{x} | x. x \<in> U} = U" by blast
    ultimately show "openin m.mtopology U"
      by simp
  qed
qed

lemma discrete_dist_topology':
 "metric_set.mtopology S (discrete_dist S) = discrete_topology S"
  by (simp add: discrete_dist_topology topology_eq)

text \<open> Empty space. \<close>
lemma empty_metric_compact: "compact_metric_set {} (\<lambda>x y. 0)"
proof -
  interpret metric_set "{}" "\<lambda>x y. 0"
    by(auto simp: metric_set_def)
  show ?thesis
    by standard (use Hausdorff_space_finite_topspace[OF mtopology_Hausdorff,simplified mtopology_topspace] in blast)
qed

corollary
  shows empty_metric_polish: "polish_metric_set {} (\<lambda>x y. 0)"
    and empty_metric_complete: "complete_metric_set {} (\<lambda>x y. 0)"
    and empty_metric_separable: "separable_metric_set {} (\<lambda>x y. 0)"
    and empty_metric: "metric_set {} (\<lambda>x y. 0)"
proof -
  interpret compact_metric_set "{}" "\<lambda>x y. 0"
    by(rule empty_metric_compact)
  show "polish_metric_set {} (\<lambda>x y. 0)" "complete_metric_set {} (\<lambda>x y. 0)"
       "separable_metric_set {} (\<lambda>x y. 0)" "metric_set {} (\<lambda>x y. 0)"
    using polish_metric_set_axioms complete_metric_set_axioms separable_metric_set_axioms metric_set_axioms
    by blast+
qed

lemma empty_metric_unique:
  assumes "metric_set {} d"
  shows "d = (\<lambda>x y. 0)"
  apply standard+
  using assms by(auto simp: metric_set_def)

lemma empty_metric_mtopology:
 "metric_set.mtopology {} (\<lambda>x y. 0) = discrete_topology {}"
proof -
  have 1:"(\<lambda>U. U = {} \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball {} (\<lambda>x y. 0) x \<epsilon> \<subseteq> U)) = (\<lambda>U. U = {})"
    by standard auto
  thus ?thesis
    using metric_set.mtopology_def[of "{}" "\<lambda>x y. 0"]
    by(simp add:  metric_set_def discrete_topology_def 1)
qed

text \<open> Singleton space \<close>
lemma singleton_metric_compact:
 "compact_metric_set {a} (\<lambda>x y. 0)"
proof -
  interpret metric_set "{a}" "\<lambda>x y. 0"
    by(auto simp: metric_set_def)
  show ?thesis
    by standard (use Hausdorff_space_finite_topspace[OF mtopology_Hausdorff,simplified mtopology_topspace] in blast)
qed

corollary
  shows singleton_metric_polish: "polish_metric_set {a} (\<lambda>x y. 0)"
    and singleton_metric_complete: "complete_metric_set {a} (\<lambda>x y. 0)"
    and singleton_metric_separable: "separable_metric_set {a} (\<lambda>x y. 0)"
    and singleton_metric: "metric_set {a} (\<lambda>x y. 0)"
proof -
  interpret compact_metric_set "{a}" "\<lambda>x y. 0"
    by(rule singleton_metric_compact)
  show "polish_metric_set {a} (\<lambda>x y. 0)" "complete_metric_set {a} (\<lambda>x y. 0)"
       "separable_metric_set {a} (\<lambda>x y. 0)" "metric_set {a} (\<lambda>x y. 0)"
    using polish_metric_set_axioms complete_metric_set_axioms separable_metric_set_axioms metric_set_axioms
    by blast+
qed

lemma singleton_metric_unique:
  assumes "metric_set {a} d"
  shows "d = (\<lambda>x y. 0)"
  by standard+ (insert assms,auto simp: metric_set_def, metis)

lemma singleton_metric_mtopology:
 "metric_set.mtopology {a} (\<lambda>x y. 0) = discrete_topology {a}"
proof -
  have "(\<lambda>U. U \<subseteq> {a} \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball {a} (\<lambda>x y. 0) x \<epsilon> \<subseteq> U)) = (\<lambda>U. U \<subseteq> {a})"
  proof
    fix U
    have "(U \<subseteq> {a} \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball {a} (\<lambda>x y. 0) x \<epsilon> \<subseteq> U))" if "U \<subseteq> {a}"
    proof safe
      fix x
      assume "x \<in> U"
      then have "x = a" using that by auto
      thus "\<exists>\<epsilon>>0. metric_set.open_ball {a} (\<lambda>x y. 0) x \<epsilon> \<subseteq> U"
        by(auto intro!: exI[where x=1]) (metis \<open>x \<in> U\<close> complete_metric_set_def empty_iff metric_set.open_ballD'(1) polish_metric_set_def singleton_metric_polish subset_singletonD that)
    qed(use that in auto)
    thus "(U \<subseteq> {a} \<and> (\<forall>x\<in>U. \<exists>\<epsilon>>0. metric_set.open_ball {a} (\<lambda>x y. 0) x \<epsilon> \<subseteq> U)) = (U \<subseteq> {a})"
      by auto
  qed
  thus ?thesis
    using metric_set.mtopology_def[of "{a}" "\<lambda>x y. 0"]
    by(simp add:  metric_set_def discrete_topology_def )
qed

subsection  \<open>Binary Product Metric Spaces\<close>
text \<open> We define the $L^{1}$-distance. $L^{1}$-distance and $L^{2}$ distance (Euclid distance)
       generate the same topological space.\<close>

definition binary_distance :: "['a set, 'a \<Rightarrow> 'a \<Rightarrow> real, 'b set, 'b \<Rightarrow> 'b \<Rightarrow> real] \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> real" where
"binary_distance S d S' d' \<equiv> (\<lambda>(x,x') (y,y'). if (x,x') \<in> S \<times> S' \<and> (y,y') \<in> S \<times> S' then d x y + d' x' y' else 0)"


context
  fixes S S' d d'
  assumes "metric_set S d" "metric_set S' d'"
begin

interpretation m1: metric_set S d by fact
interpretation m2: metric_set S' d' by fact

lemma binary_metric_set:
 "metric_set (S \<times> S') (binary_distance S d S' d')"
proof
  fix x y z
  assume "x \<in> S \<times> S'" "y \<in> S \<times> S'" "z \<in> S \<times> S'"
  then show "binary_distance S d S' d' x z \<le> binary_distance S d S' d' x y + binary_distance S d S' d' y z"
    using m1.dist_tr[of "fst x" "fst y" "fst z"] m2.dist_tr[of "snd x" "snd y" "snd z"]
    by(fastforce simp: binary_distance_def split_beta')
next
  show "\<And>x y. 0 \<le> binary_distance S d S' d' x y"
       "\<And>x y. x \<notin> S \<times> S' \<Longrightarrow> binary_distance S d S' d' x y = 0"
    using m1.dist_geq0 m2.dist_geq0 m1.dist_notin m2.dist_notin by(auto simp: binary_distance_def split_beta')
next
  fix x y
  assume "x \<in> S \<times> S'" "y \<in> S \<times> S'"
  then show "(x = y) = (binary_distance S d S' d' x y = 0)"
    using m1.dist_0[of "fst x" "fst y"] m2.dist_0[of "snd x" "snd y"] m1.dist_geq0[of "fst x" "fst y"] m2.dist_geq0[of "snd x" "snd y"]
    by(auto simp: binary_distance_def split_beta)
next
  show "\<And>x y. binary_distance S d S' d' x y = binary_distance S d S' d' y x"
    using m1.dist_sym m2.dist_sym by(auto simp: binary_distance_def split_beta')
qed

interpretation m: metric_set "S \<times> S'" "binary_distance S d S' d'"
  by (rule binary_metric_set)

lemma binary_distance_geq:
  assumes "x \<in> S" "y \<in> S" "x' \<in> S'" "y' \<in> S'"
  shows "d x y \<le> binary_distance S d S' d' (x,x') (y,y')"
        "d' x' y' \<le> binary_distance S d S' d' (x,x') (y,y')"
  using m1.dist_geq0 m2.dist_geq0 assms by(auto simp: binary_distance_def)


lemma binary_distance_ball:
  assumes "(x,x') \<in> m.open_ball (a,a') \<epsilon>"
    shows "x \<in> m1.open_ball a \<epsilon>"
      and "x' \<in> m2.open_ball a' \<epsilon>"
proof -
  have 1:"x \<in> S" "x' \<in> S'" "\<epsilon> > 0" "a \<in> S" "a' \<in> S'"
    using m.open_ballD'[OF assms(1)] by auto
  thus "x \<in> metric_set.open_ball S d a \<epsilon>"
   and "x' \<in> metric_set.open_ball S' d' a' \<epsilon>"
    using m.open_ballD[OF assms(1)] binary_distance_geq[OF 1(4,1,5,2)] 1
    by(auto simp: m1.open_ball_def m2.open_ball_def)
qed

lemma binary_distance_ball':
  assumes "z \<in> m.open_ball a \<epsilon>"
    shows "fst z \<in> m1.open_ball (fst a) \<epsilon>"
      and "snd z \<in> m2.open_ball (snd a) \<epsilon>"
  using binary_distance_ball[of "fst z" "snd z" "fst a" "snd a" \<epsilon>] assms by auto

lemma binary_distance_ball1':
  assumes "a \<in> S" "\<epsilon> > 0" "a'\<in> S'" "\<epsilon>' > 0"
    shows "\<exists>\<epsilon>''>0. m.open_ball (a,a') \<epsilon>'' \<subseteq> m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>'"
proof(rule exI[where x="min \<epsilon> \<epsilon>'"])
  show "0 < min \<epsilon> \<epsilon>' \<and> m.open_ball (a, a') (min \<epsilon> \<epsilon>') \<subseteq> m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>'"
  proof 
    show "0 < min \<epsilon> \<epsilon>'"
      using assms by auto
  next
    show "m.open_ball (a, a') (min \<epsilon> \<epsilon>') \<subseteq> m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>'"
    proof safe
      fix x x'
      assume h:"(x,x') \<in> m.open_ball (a, a') (min \<epsilon> \<epsilon>')"
      then have hx:"x \<in> S" "x' \<in> S'"
        using m.open_ballD'(1)[of "(x,x')" "(a, a')" "min \<epsilon> \<epsilon>'"] by auto
      hence "d a x + d' a' x' < min \<epsilon> \<epsilon>'"
        using h assms by(auto simp: m.open_ball_def,auto simp: binary_distance_def)
      thus "x \<in> m1.open_ball a \<epsilon>" "x' \<in> m2.open_ball a' \<epsilon>'"
        using m1.dist_geq0[of a x] m2.dist_geq0[of a' x'] assms hx
        by(auto simp: m1.open_ball_def m2.open_ball_def)
    qed
  qed
qed

lemma binary_distance_ball1:
  assumes "b \<in> m1.open_ball a \<epsilon>" "b' \<in> m2.open_ball a' \<epsilon>'"
    shows "\<exists>\<epsilon>''>0. m.open_ball (b,b') \<epsilon>'' \<subseteq> m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>'"
proof -
  obtain \<epsilon>a \<epsilon>a' where he:
    "\<epsilon>a > 0" "\<epsilon>a' > 0" "m1.open_ball b \<epsilon>a \<subseteq> m1.open_ball a \<epsilon>" "m2.open_ball b' \<epsilon>a' \<subseteq> m2.open_ball a' \<epsilon>'"
    using m1.mtopology_open_ball_in'[OF assms(1)] m2.mtopology_open_ball_in'[OF assms(2)] by auto
  thus ?thesis
    using binary_distance_ball1'[OF m1.open_ballD'(1)[OF assms(1)] he(1) m2.open_ballD'(1)[OF assms(2)] he(2)]
    by blast
qed


lemma binary_distance_ball2':
  assumes "a \<in> S" "\<epsilon>'' > 0" "a'\<in> S'"
  shows "\<exists>\<epsilon>>0. \<exists>\<epsilon>'>0. m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>' \<subseteq> m.open_ball (a,a') \<epsilon>''"
proof(safe intro!: exI[where x="\<epsilon>''/2"])
  fix x x'
  assume "x \<in> m1.open_ball a (\<epsilon>'' / 2)" "x' \<in> m2.open_ball a' (\<epsilon>'' / 2)"
  then have "x \<in> S" "x' \<in> S'" "d a x < \<epsilon>'' / 2" "d' a' x' < \<epsilon>'' / 2"
    using assms by(auto simp: m1.open_ball_def m2.open_ball_def)
  thus "(x,x') \<in> m.open_ball (a, a') \<epsilon>''"
    using assms by(auto simp: m.open_ball_def,auto simp: binary_distance_def)
qed (use assms in auto)

lemma binary_distance_ball2:
  assumes "(b,b') \<in> m.open_ball (a,a') \<epsilon>''"
    shows "\<exists>\<epsilon>>0. \<exists>\<epsilon>'>0. m1.open_ball b \<epsilon> \<times> m2.open_ball b' \<epsilon>' \<subseteq> m.open_ball (a,a') \<epsilon>''"
proof -
  obtain \<epsilon>''' where "\<epsilon>''' > 0" "m.open_ball (b,b') \<epsilon>''' \<subseteq> m.open_ball (a,a') \<epsilon>''"
    using m.mtopology_open_ball_in'[OF assms(1)] by blast
  thus ?thesis
    using binary_distance_ball2'[of b \<epsilon>''' b'] m.open_ballD'[OF assms(1),simplified]
    by blast
qed

lemma binary_distance_mtopology:
  "m.mtopology = prod_topology m1.mtopology m2.mtopology"
proof -
  have "m.mtopology = topology_generated_by { m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>' | a a' \<epsilon> \<epsilon>'. a \<in> S \<and> a' \<in> S' \<and> \<epsilon> > 0 \<and> \<epsilon>' > 0}"
    unfolding m.mtopology_def2
  proof(rule topology_generated_by_eq)
    fix U
    assume "U \<in> {m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>' |a a' \<epsilon> \<epsilon>'. a \<in> S \<and> a' \<in> S' \<and> 0 < \<epsilon> \<and> 0 < \<epsilon>'}"
    then obtain a \<epsilon> a' \<epsilon>' where hae:
    "U = m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>'" "a \<in> S" "a' \<in> S'" "0 < \<epsilon>" "0 < \<epsilon>'"
      by auto
    show "openin (topology_generated_by {m.open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<times> S' \<and> 0 < \<epsilon>}) U"
      unfolding m.mtopology_def2[symmetric] m.mtopology_openin_iff hae(1)
      using binary_distance_ball1[of _ a \<epsilon> _ a' \<epsilon>'] m1.open_ball_subset_ofS m2.open_ball_subset_ofS
      by fastforce
  next
    fix U
    assume "U \<in> {m.open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<times> S' \<and> 0 < \<epsilon>}"
    then obtain a a' \<epsilon> where hae:
    "U = m.open_ball (a,a') \<epsilon>" "a \<in> S" "a' \<in> S'" "0 < \<epsilon>"
      by auto
    show "openin (topology_generated_by {m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>' |a a' \<epsilon> \<epsilon>'. a \<in> S \<and> a' \<in> S' \<and> 0 < \<epsilon> \<and> 0 < \<epsilon>'}) U"
      unfolding openin_subopen[of _ " m.open_ball (a,a') \<epsilon>"] hae(1)
    proof
      fix x
      assume h:"x \<in> m.open_ball (a, a') \<epsilon>"
      with binary_distance_ball2[of "fst x" "snd x" a a' \<epsilon>]
      obtain \<epsilon>' \<epsilon>'' where he:
        "\<epsilon>' > 0" "\<epsilon>'' > 0" "m1.open_ball (fst x) \<epsilon>' \<times> m2.open_ball (snd x) \<epsilon>'' \<subseteq> m.open_ball (a, a') \<epsilon>"
        by auto
      show "\<exists>T. openin (topology_generated_by {m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>' |a a' \<epsilon> \<epsilon>'. a \<in> S \<and> a' \<in> S' \<and> 0 < \<epsilon> \<and> 0 < \<epsilon>'}) T \<and> x \<in> T \<and> T \<subseteq> m.open_ball (a, a') \<epsilon>"
        unfolding openin_topology_generated_by_iff
        using he m1.open_ball_ina[of "fst x",OF _ he(1)] m.open_ballD'(1,2)[OF h] m2.open_ball_ina[of "snd x",OF _ he(2)]
        by(fastforce intro!: generate_topology_on.Basis exI[where x="m1.open_ball (fst x) \<epsilon>' \<times> m2.open_ball (snd x) \<epsilon>''"] exI[where x="fst x"] exI[where x="snd x"])
    qed
  qed
  also have "... = prod_topology m1.mtopology m2.mtopology"
  proof -
    have "{m1.open_ball a \<epsilon> \<times> m2.open_ball a' \<epsilon>' |a a' \<epsilon> \<epsilon>'. a \<in> S \<and> a' \<in> S' \<and> 0 < \<epsilon> \<and> 0 < \<epsilon>'} = {U \<times> V |U V. U \<in> {m1.open_ball a \<epsilon> |a \<epsilon>. a \<in> S \<and> 0 < \<epsilon>} \<and> V \<in> {m2.open_ball a \<epsilon> |a \<epsilon>. a \<in> S' \<and> 0 < \<epsilon>}}"
      by blast
    thus ?thesis
      unfolding m1.mtopology_def2 m2.mtopology_def2
      by(simp only: prod_topology_generated_by[symmetric])
  qed
  finally show ?thesis .
qed

lemma binary_distance_converge_to_inS_iff:
 "m.converge_to_inS zn (x,y) \<longleftrightarrow> m1.converge_to_inS (\<lambda>n. fst (zn n)) x \<and> m2.converge_to_inS (\<lambda>n. snd (zn n)) y"
proof safe
  assume "m.converge_to_inS zn (x, y)"
  then have h:"zn \<in> UNIV \<rightarrow> S \<times> S'" "x \<in> S" "y \<in> S'" "\<And>e. e>0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. zn n \<in> m.open_ball (x, y) e"
    by(auto simp: m.converge_to_inS_def2')
  show "m1.converge_to_inS (\<lambda>n. fst (zn n)) x"
       "m2.converge_to_inS (\<lambda>n. snd (zn n)) y"
    unfolding m1.converge_to_inS_def2' m2.converge_to_inS_def2'
  proof safe
    fix e :: real
    assume "e > 0"
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> zn n \<in> m.open_ball (x, y) e"
      using h(4) by auto
    thus "\<exists>N. \<forall>n\<ge>N. fst (zn n) \<in> m1.open_ball x e"
         "\<exists>N. \<forall>n\<ge>N. snd (zn n) \<in> m2.open_ball y e"
      using binary_distance_ball'[of "zn _" "(x,y)"]
      by(auto intro!: exI[where x=N])
  qed(insert h(1-3),simp_all add: Pi_iff mem_Times_iff)
next
  assume h:"m1.converge_to_inS (\<lambda>n. fst (zn n)) x" "m2.converge_to_inS (\<lambda>n. snd (zn n)) y"
  show "m.converge_to_inS zn (x, y)"
    unfolding m.converge_to_inS_def2'
  proof safe
    show goal1:"x \<in> S" "y \<in> S'" "zn n \<in> S \<times> S'" for n
      using h by(auto simp: m1.converge_to_inS_def m2.converge_to_inS_def Pi_iff mem_Times_iff)
    fix e :: real
    assume "e > 0"
    from binary_distance_ball2'[OF goal1(1) this goal1(2)]
    obtain e1 e2 where e12:"e1 > 0" "e2 > 0" "m1.open_ball x e1 \<times> m2.open_ball y e2 \<subseteq> m.open_ball (x, y) e " by auto
    then obtain N1 N2 where N12: "\<And>n. n \<ge> N1 \<Longrightarrow> fst (zn n) \<in> m1.open_ball x e1" "\<And>n. n \<ge> N2 \<Longrightarrow> snd (zn n) \<in> m2.open_ball y e2"
      using h by(auto simp: m1.converge_to_inS_def2' m2.converge_to_inS_def2') metis
    with e12 have "\<And>n. n \<ge> max N1 N2 \<Longrightarrow> zn n \<in> m1.open_ball x e1 \<times> m2.open_ball y e2"
      by (simp add: mem_Times_iff)
    with e12(3) show "\<exists>N. \<forall>n\<ge>N. zn n \<in> m.open_ball (x, y) e"
      by(auto intro!: exI[where x="max N1 N2"])
  qed
qed

lemma binary_distance_converge_to_inS_iff':
 "m.converge_to_inS zn z \<longleftrightarrow> m1.converge_to_inS (\<lambda>n. fst (zn n)) (fst z) \<and> m2.converge_to_inS (\<lambda>n. snd (zn n)) (snd z)"
  using binary_distance_converge_to_inS_iff[of _ "fst z" "snd z"] by simp

corollary binary_distance_convergent_inS_iff:
 "m.convergent_inS zn \<longleftrightarrow> m1.convergent_inS (\<lambda>n. fst (zn n)) \<and> m2.convergent_inS (\<lambda>n. snd (zn n))"
  by(auto simp: m.convergent_inS_def m1.convergent_inS_def m2.convergent_inS_def binary_distance_converge_to_inS_iff)

lemma binary_distance_Cauchy_inS_iff:
 "m.Cauchy_inS zn \<longleftrightarrow> m1.Cauchy_inS (\<lambda>n. fst (zn n)) \<and> m2.Cauchy_inS (\<lambda>n. snd (zn n))"
proof safe
  assume h:"m.Cauchy_inS zn"
  show "m1.Cauchy_inS (\<lambda>n. fst (zn n))" "m2.Cauchy_inS (\<lambda>n. snd (zn n))"
    unfolding m1.Cauchy_inS_def2' m2.Cauchy_inS_def2'
  proof safe
    fix e :: real
    assume "e > 0"
    then obtain x y N where "x \<in> S" "y \<in> S'" "\<And>n. n \<ge> N \<Longrightarrow> zn n \<in> m.open_ball (x,y) e"
      using h by(auto simp: m.Cauchy_inS_def2') metis
    thus "\<exists>x\<in>S. \<exists>N. \<forall>n\<ge>N. fst (zn n) \<in> m1.open_ball x e"
         "\<exists>y\<in>S'. \<exists>N. \<forall>n\<ge>N. snd (zn n) \<in> m2.open_ball y e"
      using binary_distance_ball'[of "zn _" "(x,y)"]
      by(auto intro!: exI[where x=x] exI[where x=y] exI[where x=N]) blast
  qed(insert h, simp_all add: m.Cauchy_inS_def Pi_iff mem_Times_iff)
next
  assume h: "m1.Cauchy_inS (\<lambda>n. fst (zn n))" "m2.Cauchy_inS (\<lambda>n. snd (zn n))"
  show "m.Cauchy_inS zn"
    unfolding m.Cauchy_inS_def
  proof safe
    show 1:"zn n \<in> S \<times> S'" for n
      using h(1,2) m1.Cauchy_inS_dest1 m2.Cauchy_inS_dest1 mem_Times_iff by blast
    fix e :: real
    assume "e > 0"
    then obtain N1 N2 where N:"\<And>n m. n \<ge> N1 \<Longrightarrow> m \<ge> N1 \<Longrightarrow> d (fst (zn n)) (fst (zn m)) < e / 2" "\<And>n m. n \<ge> N2 \<Longrightarrow> m \<ge> N2 \<Longrightarrow> d' (snd (zn n)) (snd (zn m)) < e / 2"
      by (metis h(1) h(2) less_divide_eq_numeral1(1) m1.Cauchy_inS_def m2.Cauchy_inS_def mult_zero_left)
    show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. binary_distance S d S' d' (zn n) (zn m) < e"
    proof(safe intro!: exI[where x="max N1 N2"])
      fix n m
      assume "max N1 N2 \<le> n" "max N1 N2 \<le> m"
      then have le:"N1 \<le> n" "N1 \<le> m" "N2 \<le> n" "N2 \<le> m" by auto
      show "binary_distance S d S' d' (zn n) (zn m) < e"
        using N(1)[OF le(1,2)] N(2)[OF le(3,4)] \<open>e > 0\<close>
        by(auto simp: binary_distance_def split_beta')
    qed
  qed
qed

end

lemma binary_distance_separable:
  assumes "separable_metric_set S d" "separable_metric_set S' d'"
  shows "separable_metric_set (S \<times> S') (binary_distance S d S' d')"
proof -
  interpret m1:separable_metric_set S d by fact
  interpret m2:separable_metric_set S' d' by fact
  interpret m : metric_set "S \<times> S'" "binary_distance S d S' d'"
    by(auto intro!: binary_metric_set m1.metric_set_axioms m2.metric_set_axioms)
  show ?thesis
    using m.separable_iff_topological_separable separable_prod[OF m1.topological_separable_if_separable m2.topological_separable_if_separable] binary_distance_mtopology[OF m1.metric_set_axioms m2.metric_set_axioms]
    by auto
qed

lemma binary_distance_complete:
  assumes "complete_metric_set S d" "complete_metric_set S' d'"
  shows "complete_metric_set (S \<times> S') (binary_distance S d S' d')"
proof -
  interpret m1:complete_metric_set S d by fact
  interpret m2:complete_metric_set S' d' by fact
  interpret m : metric_set "S \<times> S'" "binary_distance S d S' d'"
    by(auto intro!: binary_metric_set m1.metric_set_axioms m2.metric_set_axioms)
  show ?thesis
    by standard (simp add: binary_distance_Cauchy_inS_iff[OF m1.metric_set_axioms m2.metric_set_axioms] binary_distance_convergent_inS_iff[OF m1.metric_set_axioms m2.metric_set_axioms] m1.convergence m2.convergence)
qed

lemma binary_distance_polish:
  assumes "polish_metric_set S d" and "polish_metric_set S' d'"
  shows "polish_metric_set (S\<times>S') (binary_distance S d S' d')"
  using assms by(simp add: polish_metric_set_def binary_distance_separable binary_distance_complete)

subsection  \<open>Sum Metric Spaces\<close>

locale sum_metric =
  fixes I :: "'i set"
    and Si :: "'i \<Rightarrow> 'a set"
    and di :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes disj_fam: "disjoint_family_on Si I"
      and d_nonneg: "\<And>i x y. 0 \<le> di i x y"
      and d_bounded: "\<And>i x y. di i x y < 1"
      and sd_metric: "\<And>i. i \<in> I \<Longrightarrow> metric_set (Si i) (di i)"
begin

abbreviation "S \<equiv> \<Union>i\<in>I. Si i"

lemma Si_inj_on:
  assumes "i \<in> I" "j \<in> I" "a \<in> Si i" "a \<in> Si j"
  shows "i = j"
  using disj_fam assms by(auto simp: disjoint_family_on_def)

definition sum_dist :: "['a, 'a] \<Rightarrow> real" where
"sum_dist x y \<equiv> (if x \<in> S \<and> y \<in> S then (if \<exists>i\<in>I. x \<in> Si i \<and> y \<in> Si i then di (THE i. i \<in> I \<and> x \<in> Si i \<and> y \<in> Si i) x y else 1) else 0)"

lemma sum_dist_simps:
  shows "\<And>i. \<lbrakk>i \<in> I; x \<in> Si i; y \<in> Si i\<rbrakk> \<Longrightarrow> sum_dist x y = di i x y"
    and "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i \<noteq> j; x \<in> Si i; y \<in> Si j\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
    and "\<And>i. \<lbrakk>i \<in> I; y \<in> S; x \<in> Si i; y \<notin> Si i\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
    and "\<And>i. \<lbrakk>i \<in> I; x \<in> S; y \<in> Si i; x \<notin> Si i\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
    and "x \<notin> S \<Longrightarrow> sum_dist x y = 0"
proof -
  { fix i
    assume h:"i \<in> I" "x \<in> Si i" "y \<in> Si i"
    then have "sum_dist x y = di (THE i. i \<in> I \<and> x \<in> Si i \<and> y \<in> Si i) x y"
      by(auto simp: sum_dist_def)
    also have "... = di i x y"
    proof -
      have "(THE i. i \<in> I \<and> x \<in> Si i \<and> y \<in> Si i) = i"
        using disj_fam h by(auto intro!: the1_equality simp: disjoint_family_on_def)
      thus ?thesis by simp
    qed
    finally show "sum_dist x y = di i x y" . }
  show "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i \<noteq> j; x \<in> Si i; y \<in> Si j\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
       "\<And>i. \<lbrakk>i \<in> I; y \<in> S; x \<in> Si i; y \<notin> Si i\<rbrakk> \<Longrightarrow> sum_dist x y = 1" "\<And>i. \<lbrakk>i \<in> I; x \<in> S; y \<in> Si i; x \<notin> Si i\<rbrakk> \<Longrightarrow> sum_dist x y = 1"
       "x \<notin> S \<Longrightarrow> sum_dist x y = 0"
    using disj_fam by(auto simp: sum_dist_def disjoint_family_on_def dest:Si_inj_on)
qed

lemma sum_dist_if_less1:
  assumes "i \<in> I" "x \<in> Si i" "y \<in> S" "sum_dist x y < 1"
  shows "y \<in> Si i"
  using assms sum_dist_simps(3) by fastforce

lemma inS_cases:
  assumes "x \<in> S" "y \<in> S"
      and "\<And>i. \<lbrakk>i \<in> I; x \<in> Si i; y \<in> Si i\<rbrakk> \<Longrightarrow> P x y"
      and "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i \<noteq> j; x \<in> Si i; y \<in> Si j; x \<noteq> y\<rbrakk> \<Longrightarrow> P x y"
    shows "P x y" using assms by auto

sublocale metric_set S sum_dist
proof
  fix x y
  assume "x \<in> S" "y \<in> S"
  then show "x = y \<longleftrightarrow> sum_dist x y = 0"
    by(rule inS_cases, insert sd_metric) (auto simp: sum_dist_simps metric_set_def)
next
  { fix i x y
    assume h: "i \<in> I" "x \<in> Si i" "y \<in> Si i"
    then have "sum_dist x y = di i x y"
              "sum_dist y x = di i x y"
      using sd_metric by(auto simp: sum_dist_simps metric_set_def) }
  thus "\<And>x y. sum_dist x y = sum_dist y x"
    by (metis (no_types, lifting) sum_dist_def)
next
  show 1:"\<And>x y. 0 \<le> sum_dist x y"
    using d_nonneg by(simp add: sum_dist_def)
  fix x y z
  assume h: "x \<in> S" "y \<in> S" "z \<in> S"
  show "sum_dist x z \<le> sum_dist x y + sum_dist y z" (is "?lhs \<le> ?rhs")
  proof(rule inS_cases[OF h(1,3)])
    fix i
    assume h':"i \<in> I" "x \<in> Si i" "z \<in> Si i"
    consider "y \<in> Si i" | "y \<notin> Si i" by auto
    thus "?lhs \<le> ?rhs"
    proof cases
      case 1
      with h' sd_metric [OF h'(1)]show ?thesis
        by(simp add: sum_dist_simps metric_set_def)
    next
      case 2
      with h' h(2) d_bounded[of i x z] 1[of y z]
      show ?thesis
        by(auto simp: sum_dist_simps)
    qed
  next
    fix i j
    assume h': "i \<in> I" "j \<in> I" "i \<noteq> j" "x \<in> Si i" "z \<in> Si j"
    consider "y \<notin> Si i" | "y \<notin> Si j"
      using h' h(2) disj_fam by(auto simp: disjoint_family_on_def)
    thus "?lhs \<le> ?rhs"
      by (cases, insert 1[of x y] 1[of y z] h' h(2)) (auto simp: sum_dist_simps)
  qed
qed(simp add: sum_dist_simps)

lemma sum_dist_le1: "sum_dist x y \<le> 1"
  using d_bounded[of _ x y] by(auto simp: sum_dist_def less_eq_real_def)


lemma sum_dist_ball_eq_ball:
  assumes "i \<in> I" "e \<le> 1" "x \<in> Si i"
  shows "metric_set.open_ball (Si i) (di i) x e = open_ball x e"
proof -
  interpret m: metric_set "Si i" "di i"
    by(simp add: assms sd_metric)
  show ?thesis
    using assms sum_dist_simps(1)[OF assms(1) assms(3)] sum_dist_if_less1[OF assms(1,3)]
    by(auto simp: m.open_ball_def open_ball_def) fastforce+
qed

lemma ball_le_sum_dist_ball:
  assumes "i \<in> I"
  shows "metric_set.open_ball (Si i) (di i) x e \<subseteq> open_ball x e"
proof -
  interpret m: metric_set "Si i" "di i"
    by(simp add: assms sd_metric)
  show ?thesis
  proof safe
    fix y
    assume y: "y \<in> m.open_ball x e"
    show "y \<in> open_ball x e"
      using m.open_ballD[OF y] m.open_ballD'[OF y] assms
      by(auto simp: open_ball_def sum_dist_simps)
  qed
qed

lemma openin_sum_mtopology_iff:
 "openin mtopology U \<longleftrightarrow> U \<subseteq> S \<and> (\<forall>i\<in>I. openin (metric_set.mtopology (Si i) (di i)) (U \<inter> Si i))"
proof safe
  fix i
  assume h:"openin mtopology U" "i \<in> I"
  then interpret m: metric_set "Si i" "di i"
    using sd_metric by simp
  show "openin m.mtopology (U \<inter> Si i)"
    unfolding m.mtopology_openin_iff
  proof safe
    fix x
    assume x:"x \<in> U" "x \<in> Si i"
    with h obtain e where e: "e > 0" "open_ball x e \<subseteq> U"
      by(auto simp: mtopology_openin_iff)
    show "\<exists>\<epsilon>>0. m.open_ball x \<epsilon> \<subseteq> U \<inter> Si i"
    proof(safe intro!: exI[where x=e])
      fix y
      assume "y \<in> m.open_ball x e"
      from m.open_ballD[OF this] x(2)  m.open_ballD'(1)[OF this] h(2)
      have "y \<in> open_ball x e"
        by(auto simp: open_ball_def sum_dist_simps)
      with e show "y \<in> U" by auto
    qed(use e m.open_ball_subset_ofS in auto)
  qed
next
  show "\<And>x. openin mtopology U \<Longrightarrow> x \<in> U \<Longrightarrow> x \<in> S"
    by(auto simp: mtopology_openin_iff)
next
  assume h: "U \<subseteq> S" "\<forall>i\<in>I. openin (metric_set.mtopology (Si i) (di i)) (U \<inter> Si i)"
  show "openin mtopology U"
    unfolding mtopology_openin_iff
  proof safe
    fix x
    assume x: "x \<in> U"
    then obtain i where i: "i \<in> I" "x \<in> Si i"
      using h(1) by auto
    then interpret m: metric_set "Si i" "di i"
      using sd_metric by simp
    obtain e where e: "e > 0" "m.open_ball x e \<subseteq> U \<inter> Si i"
      using i h(2) by (meson IntI m.mtopology_openin_iff x)
    show "\<exists>\<epsilon>>0. open_ball x \<epsilon> \<subseteq> U"
    proof(safe intro!: exI[where x="min e 1"])
      fix y
      assume y:"y \<in> open_ball x (min e 1)"
      then show "y \<in> U"
        using sum_dist_ball_eq_ball[OF i(1) _ i(2),of "min e 1"] e m.open_ball_le[of "min e 1" e x]
        by auto 
    qed(simp add: e)
  qed(use h(1) in auto)
qed

corollary openin_sum_mtopology_Si:
  assumes "i \<in> I"
  shows "openin mtopology (Si i)"
  unfolding openin_sum_mtopology_iff
proof safe
  fix j
  assume j:"j \<in> I"
  then interpret m: metric_set "Si j" "di j"
    by(simp add: sd_metric)
  show "openin m.mtopology (Si i \<inter> Si j)"
    by (cases "i = j", insert assms disj_fam j) (auto simp: disjoint_family_on_def)
qed(use assms in auto)

lemma converge_to_inSi_converge_to_inS:
  assumes "i \<in> I" "metric_set.converge_to_inS (Si i) (di i) xn x"
  shows "converge_to_inS xn x"
proof -
  interpret m: metric_set "Si i" "di i"
    by(simp add: assms sd_metric)
  {
    fix e :: real
    assume "e > 0"
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> xn n \<in> m.open_ball x e"
      using assms(2) by(auto simp: m.converge_to_inS_def2') metis
    hence "\<exists>N. \<forall>n\<ge>N. xn n \<in> open_ball x e"
      using ball_le_sum_dist_ball[OF assms(1),of x e]
      by(auto intro!: exI[where x=N]) }
  thus ?thesis
    using assms by(auto simp: m.converge_to_inS_def2' converge_to_inS_def2')
qed

corollary convergent_inSi_convergent_inS:
  assumes "i \<in> I" "metric_set.convergent_inS (Si i) (di i) xn"
  shows "convergent_inS xn"
  using converge_to_inSi_converge_to_inS[OF assms(1)] assms(1) assms(2) convergent_inS_def metric_set.the_limit_if_converge sd_metric
  by blast

lemma converge_to_inS_converge_to_inSi_off_set:
  assumes "converge_to_inS xn x"
  shows "\<exists>n. \<exists>j\<in>I. metric_set.converge_to_inS (Si j) (di j) (\<lambda>i. xn (i + n)) x"
proof -
  obtain i where i: "i \<in> I" "x \<in> Si i"
    using assms by(auto simp: converge_to_inS_def)
  then interpret m: metric_set "Si i" "di i"
    by(simp add: sd_metric)
  obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> sum_dist (xn n) x < 1"
    using assms by(fastforce simp: converge_to_inS_def2)
  hence N': "n \<ge> N \<Longrightarrow> xn n \<in> Si i" for n
    using assms by(auto intro!: sum_dist_if_less1[OF i,of "xn n"] simp: dist_sym[of _ x] converge_to_inS_def)
  show ?thesis
  proof(safe intro!: exI[where x=N] bexI[OF _ i(1)])
    show "m.converge_to_inS (\<lambda>i. xn (i + N)) x"
      unfolding m.converge_to_inS_def2
    proof(safe intro!: N' i(2))
      fix e :: real
      assume "0 < e"
      then obtain M where M: "\<And>n. n \<ge> M \<Longrightarrow> sum_dist (xn n) x < e"
        using assms by(fastforce simp: converge_to_inS_def2)
      hence "n \<ge> max N M \<Longrightarrow> di i (xn n) x < e" for n
        using sum_dist_simps(1)[OF i(1) N'[of n] i(2),symmetric] by auto        
      thus "\<exists>M. \<forall>n\<ge>M. di i (xn (n + N)) x < e"
        by(auto intro!: exI[where x=M])
    qed simp
  qed
qed

corollary convergent_inS_convergent_inSi_off_set:
  assumes "convergent_inS xn"
  shows "\<exists>n. \<exists>j\<in>I. metric_set.convergent_inS (Si j) (di j) (\<lambda>i. xn (i + n))"
  using converge_to_inS_converge_to_inSi_off_set
  by (meson assms metric_set.convergent_inS_def metric_set_axioms sd_metric)


lemma Cauchy_inSi_Cauchy_inS:
  assumes "i \<in> I" "metric_set.Cauchy_inS (Si i) (di i)xn"
  shows "Cauchy_inS xn"
proof -
  interpret m: metric_set "Si i" "di i"
    by(simp add: assms sd_metric)
  have [simp]:"sum_dist (xn n) (xn m) = di i (xn n) (xn m)" for n m
    using assms sum_dist_simps(1)[OF assms(1)]
    by(auto simp: m.Cauchy_inS_def Cauchy_inS_def)
  show ?thesis
    using assms by(auto simp: m.Cauchy_inS_def Cauchy_inS_def)
qed

lemma Cauchy_inS_Cauchy_inSi:
  assumes "Cauchy_inS xn"
  shows "\<exists>n. \<exists>j\<in>I. metric_set.Cauchy_inS (Si j) (di j) (\<lambda>i. xn (i + n))"
proof -
  obtain x i N where xiN: "i \<in> I" "x \<in> Si i" "\<And>n. n \<ge> N \<Longrightarrow> xn n \<in> open_ball x 1"
    using assms by(auto simp: Cauchy_inS_def2') (metis UNION_empty_conv(2) d_bounded d_nonneg dist_0 empty_subsetI less_eq_real_def open_ball_le_0 subsetI subset_antisym sum_dist_le1) 
  then interpret m: metric_set "Si i" "di i"
    by(simp add: sd_metric)
  have xn: "n \<ge> N \<Longrightarrow> xn n \<in> Si i" for n
    using xiN(3)[of n] by(auto simp: sum_dist_ball_eq_ball[OF xiN(1) order_refl xiN(2),symmetric] dest: m.open_ballD')
  show ?thesis
  proof(safe intro!: exI[where x=N] bexI[OF _ xiN(1)])
    show "m.Cauchy_inS (\<lambda>i. xn (i + N))"
      unfolding m.Cauchy_inS_def
    proof safe
      fix e :: real
      assume "0 < e"
      then obtain M where M: "\<And>n m. n \<ge> M \<Longrightarrow> m \<ge> M \<Longrightarrow> sum_dist (xn n) (xn m) < e"
        using assms by(auto simp: Cauchy_inS_def) metis
      have [simp]: "n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> di i (xn n) (xn m) = sum_dist (xn n) (xn m)" for n m
        using xn sum_dist_simps(1)[OF xiN(1) xn[of n] xn[of m]] by simp
      show "\<exists>N'. \<forall>n\<ge>N'. \<forall>m\<ge>N'. di i (xn (n + N)) (xn (m + N)) < e"
        using M by(auto intro!: exI[where x="max N M"])
    qed(use xn in auto)
  qed
qed

end

lemma sum_metricI:
  fixes Si
  assumes "disjoint_family_on Si I"
      and "\<And>i x y. i \<notin> I \<Longrightarrow> 0 \<le> di i x y"
      and "\<And>i x y. di i x y < 1"
      and "\<And>i. i \<in> I \<Longrightarrow> metric_set (Si i) (di i)"
    shows "sum_metric I Si di"
  using assms by(auto simp: sum_metric_def) (meson metric_set.dist_geq0)

locale sum_separable_metric = sum_metric +
  assumes I: "countable I"
      and sd_separable_metric: "\<And>i. i \<in> I \<Longrightarrow> separable_metric_set (Si i) (di i)"
begin

sublocale separable_metric_set S sum_dist
proof
  obtain Ui where Ui: "\<And>i. i \<in> I \<Longrightarrow> countable (Ui i)" "\<And>i. i \<in> I \<Longrightarrow> metric_set.dense_set (Si i) (di i) (Ui i)" 
    using sd_separable_metric by(auto simp: separable_metric_set_def separable_metric_set_axioms_def) metis
  define U where "U \<equiv> \<Union>i\<in>I. Ui i"
  show "\<exists>U. countable U \<and> dense_set U"
  proof(safe intro!: exI[where x=U])
    show "countable U"
      using Ui(1) I by(auto simp: U_def)
  next
    show "dense_set U"
      unfolding dense_set_def U_def
    proof safe
      fix i x
      assume "i \<in> I" "x \<in> Ui i"
      then show "x \<in> S"
        using sd_separable_metric Ui by(auto intro!: bexI[where x=i] simp: separable_metric_set_def metric_set.dense_set_def)
    next
      fix i x e
      assume h:"i \<in> I" "x \<in> Si i" "(0 :: real) < e" "open_ball x e \<inter> \<Union> (Ui ` I) = {}"
      then interpret sd: separable_metric_set "Si i" "di i"
        by(simp add: sd_separable_metric)
      have "sd.open_ball x e \<inter> Ui i \<noteq> {}"
        using Ui(2)[OF h(1)] h(1-3) by(auto simp: U_def sd.dense_set_def)
      hence "sd.open_ball x e \<inter> \<Union> (Ui ` I) \<noteq> {}"
        using h(1) by blast
      thus False
        using ball_le_sum_dist_ball[OF \<open>i \<in> I\<close>,of x e] h(4) by blast
    qed
  qed
qed

end

locale sum_complete_metric = sum_metric +
  assumes sd_complete_metric: "\<And>i. i \<in> I \<Longrightarrow> complete_metric_set (Si i) (di i)"
begin

sublocale complete_metric_set S sum_dist
proof
  fix xn
  assume 1:"Cauchy_inS xn"
  from Cauchy_inS_Cauchy_inSi[OF this] obtain n j where h: "j \<in> I"  "metric_set.Cauchy_inS (Si j) (di j) (\<lambda>i. xn (i + n))"
    by auto
  then have "metric_set.convergent_inS (Si j) (di j) (\<lambda>i. xn (i + n))"
    by (simp add: complete_metric_set.convergence sd_complete_metric)
  from convergent_inS_offset[OF convergent_inSi_convergent_inS[OF h(1) this]] 1
  show "convergent_inS xn"
    by(simp add: Cauchy_inS_def)
qed

end

locale sum_polish_metric = sum_complete_metric + sum_separable_metric
begin

sublocale polish_metric_set S sum_dist
  by (simp add: complete_metric_set_axioms polish_metric_set_def separable_metric_set_axioms)

end

lemma sum_polish_metricI:
  fixes Si
  assumes "countable I"
      and "disjoint_family_on Si I"
      and "\<And>i x y. i \<notin> I \<Longrightarrow> 0 \<le> di i x y"
      and "\<And>i x y. di i x y < 1"
      and "\<And>i. i \<in> I \<Longrightarrow> polish_metric_set (Si i) (di i)"
    shows "sum_polish_metric I Si di"
  using assms by(auto simp: sum_polish_metric_def sum_complete_metric_def sum_separable_metric_def sum_complete_metric_axioms_def sum_separable_metric_axioms_def polish_metric_set_def complete_metric_set_def sum_metricI)

end