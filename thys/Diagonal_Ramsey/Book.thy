section \<open>The book algorithm\<close>

theory Book imports
  Neighbours
  "HOL-Library.Disjoint_Sets"  "HOL-Decision_Procs.Approximation" 
  "HOL-Real_Asymp.Real_Asymp" 

begin

hide_const Bseq

subsection \<open>Locales for the parameters of the construction\<close>

type_synonym 'a config = "'a set \<times> 'a set \<times> 'a set \<times> 'a set"

locale P0_min =   
  fixes p0_min :: real
  assumes p0_min: "0 < p0_min" "p0_min < 1"

locale Book_Basis = fin_sgraph + P0_min + \<comment> \<open>building on finite simple graphs (no loops)\<close>
  assumes complete: "E = all_edges V"
  assumes infinite_UNIV: "infinite (UNIV::'a set)"
begin

abbreviation "nV \<equiv> card V"

lemma graph_size: "graph_size = (nV choose 2)"
  using card_all_edges complete finV by blast

lemma in_E_iff [iff]: "{v,w} \<in> E \<longleftrightarrow> v\<in>V \<and> w\<in>V \<and> v\<noteq>w"
  by (auto simp: complete all_edges_alt doubleton_eq_iff)

lemma all_edges_betw_un_iff_clique: "K \<subseteq> V \<Longrightarrow> all_edges_betw_un K K \<subseteq> F \<longleftrightarrow> clique K F"
  unfolding clique_def all_edges_betw_un_def doubleton_eq_iff subset_iff
  by blast

lemma clique_Un:
  assumes "clique A F" "clique B F" "all_edges_betw_un A B \<subseteq> F" "A \<subseteq> V" "B \<subseteq> V"
  shows "clique (A \<union> B) F"
  using assms by (simp add: all_uedges_betw_I clique_Un subset_iff)

lemma clique_insert:
  assumes "clique A F" "all_edges_betw_un {x} A \<subseteq> F" "A \<subseteq> V" "x \<in> V"
  shows "clique (insert x A) F"
  using assms
  by (metis Un_subset_iff clique_def insert_is_Un insert_subset clique_Un singletonD)

lemma less_RN_Red_Blue:
  fixes l k
  assumes nV: "nV < RN k l"
  obtains Red Blue :: "'a set set"
  where "Red \<subseteq> E" "Blue = E\<setminus>Red" "\<not> (\<exists>K. size_clique k K Red)" "\<not> (\<exists>K. size_clique l K Blue)" 
proof -
  have "\<not> is_Ramsey_number k l nV"
    using RN_le assms leD by blast
  then obtain f where f: "f \<in> nsets {..<nV} 2 \<rightarrow> {..<2}" 
            and noclique: "\<And>i. i<2 \<Longrightarrow> \<not> monochromatic {..<nV} ([k,l] ! i) 2 f i"
    by (auto simp: partn_lst_def eval_nat_numeral)
  obtain \<phi> where \<phi>: "bij_betw \<phi> {..<nV} V"
    using bij_betw_from_nat_into_finite finV by blast
  define \<theta> where "\<theta> \<equiv> inv_into {..<nV} \<phi>"
  have \<theta>: "bij_betw \<theta> V {..<nV}"
    using \<phi> \<theta>_def bij_betw_inv_into by blast
  have emap: "bij_betw (\<lambda>e. \<phi>`e) (nsets {..<nV} 2) E"
    by (metis \<phi> bij_betw_nsets complete nsets2_eq_all_edges)
  define Red  where "Red \<equiv>  (\<lambda>e. \<phi>`e) ` ((f -` {0}) \<inter> nsets {..<nV} 2)"
  define Blue where "Blue \<equiv> (\<lambda>e. \<phi>`e) ` ((f -` {1}) \<inter> nsets {..<nV} 2)"
  have f0: "f (\<theta>`e) = 0" if "e \<in> Red" for e
    using that \<phi> by (auto simp add: Red_def image_iff \<theta>_def bij_betw_def nsets_def)
  have f1: "f (\<theta>`e) = 1" if "e \<in> Blue" for e
    using that \<phi> by (auto simp add: Blue_def image_iff \<theta>_def bij_betw_def nsets_def)
  have "Red \<subseteq> E"
    using bij_betw_imp_surj_on[OF emap] by (auto simp: Red_def)
  have "Blue = E-Red"
    using emap f
    by (auto simp: Red_def Blue_def bij_betw_def inj_on_eq_iff image_iff Pi_iff)
  have no_Red_K: False if "size_clique k K Red" for K
  proof -
    have "clique K Red" and Kk: "card K = k" and "K\<subseteq>V"
      using that by (auto simp: size_clique_def)
    then have "f ` [\<theta>`K]\<^bsup>2\<^esup> \<subseteq> {0}"
      unfolding clique_def image_subset_iff
      by (smt (verit, ccfv_SIG) f0 image_empty image_iff image_insert nsets2_E singleton_iff)
    moreover have "\<theta>`K \<in> [{..<nV}]\<^bsup>card K\<^esup>"
      by (smt (verit) \<open>K\<subseteq>V\<close> \<theta> bij_betwE bij_betw_nsets finV mem_Collect_eq nsets_def finite_subset)
    ultimately show False
      using noclique [of 0] Kk by (simp add: size_clique_def monochromatic_def)
  qed
  have no_Blue_K: False if "size_clique l K Blue" for K
  proof -
    have "clique K Blue" and Kl: "card K = l" and "K\<subseteq>V"
      using that by (auto simp: size_clique_def)
    then have "f ` [\<theta>`K]\<^bsup>2\<^esup> \<subseteq> {1}"
      unfolding clique_def image_subset_iff
      by (smt (verit, ccfv_SIG) f1 image_empty image_iff image_insert nsets2_E singleton_iff)
    moreover have "\<theta>`K \<in> [{..<nV}]\<^bsup>card K\<^esup>"
      using bij_betw_nsets [OF \<theta>] \<open>K \<subseteq> V\<close> bij_betwE finV infinite_super nsets_def by fastforce
    ultimately show False
      using noclique [of 1] Kl by (simp add: size_clique_def monochromatic_def)
  qed
  show thesis
    using \<open>Blue = E \<setminus> Red\<close> \<open>Red \<subseteq> E\<close> no_Blue_K no_Red_K that by presburger
qed

end

locale No_Cliques = Book_Basis +
  fixes Red Blue :: "'a set set"
  assumes Red_E: "Red \<subseteq> E"
  assumes Blue_def: "Blue = E-Red"
  \<comment> \<open>the following are local to the program\<close>
  fixes l::nat       \<comment> \<open>blue limit\<close>
  fixes k::nat       \<comment> \<open>red limit\<close>
  assumes l_le_k: "l \<le> k" \<comment> \<open>they should be "sufficiently large"\<close>
  assumes no_Red_clique: "\<not> (\<exists>K. size_clique k K Red)"
  assumes no_Blue_clique: "\<not> (\<exists>K. size_clique l K Blue)"

locale Book = Book_Basis + No_Cliques +
  fixes \<mu>::real      \<comment> \<open>governs the big blue steps\<close>
  assumes \<mu>01: "0 < \<mu>" "\<mu> < 1"
  fixes X0 :: "'a set" and Y0 :: "'a set"    \<comment> \<open>initial values\<close>
  assumes XY0: "disjnt X0 Y0" "X0 \<subseteq> V" "Y0 \<subseteq> V"
  assumes density_ge_p0_min: "gen_density Red X0 Y0 \<ge> p0_min"

locale Book' = Book_Basis + No_Cliques +
  fixes \<gamma>::real      \<comment> \<open>governs the big blue steps\<close>
  assumes \<gamma>_def: "\<gamma> = real l / (real k + real l)"
  fixes X0 :: "'a set" and Y0 :: "'a set"    \<comment> \<open>initial values\<close>
  assumes XY0: "disjnt X0 Y0" "X0 \<subseteq> V" "Y0 \<subseteq> V"
  assumes density_ge_p0_min: "gen_density Red X0 Y0 \<ge> p0_min"

definition "epsilon \<equiv> \<lambda>k. real k powr (-1/4)"

definition qfun_base :: "[nat, nat] \<Rightarrow> real"
  where "qfun_base \<equiv> \<lambda>k h. ((1 + epsilon k)^h - 1) / k"

definition "hgt_maximum \<equiv> \<lambda>k. 2 * ln (real k) / epsilon k"

text \<open>The first of many "bigness assumptions"\<close>
definition "Big_height_upper_bound \<equiv> \<lambda>k. qfun_base k (nat \<lfloor>hgt_maximum k\<rfloor>) > 1"

lemma Big_height_upper_bound:
  shows "\<forall>\<^sup>\<infinity>k. Big_height_upper_bound k"
  unfolding Big_height_upper_bound_def hgt_maximum_def epsilon_def qfun_base_def
  by real_asymp

context No_Cliques
begin

abbreviation "eps \<equiv> epsilon k"

lemma eps_eq_sqrt: "eps = 1 / sqrt (sqrt (real k))"
  by (simp add: epsilon_def powr_minus_divide powr_powr flip: powr_half_sqrt)

lemma eps_ge0: "eps \<ge> 0"
  by (simp add: epsilon_def)

lemma ln0: "l>0"
  using no_Blue_clique by (force simp: size_clique_def clique_def)

lemma kn0: "k > 0"
  using  l_le_k ln0 by auto

lemma eps_gt0: "eps > 0"
  by (simp add: epsilon_def kn0)

lemma eps_le1: "eps \<le> 1"
  using kn0 ge_one_powr_ge_zero
  by (simp add: epsilon_def powr_minus powr_mono2 divide_simps)

lemma eps_less1:
  assumes "k>1" shows "eps < 1"
  by (smt (verit) assms epsilon_def less_imp_of_nat_less of_nat_1 powr_less_one zero_le_divide_iff)

lemma Blue_E: "Blue \<subseteq> E"
  by (simp add: Blue_def) 

lemma disjnt_Red_Blue: "disjnt Red Blue"
  by (simp add: Blue_def disjnt_def)

lemma Red_Blue_all: "Red \<union> Blue = all_edges V"
  using Blue_def Red_E complete by blast

lemma Blue_eq: "Blue = all_edges V - Red"
  using Blue_def complete by auto

lemma Red_eq: "Red = all_edges V - Blue"
  using Blue_eq Red_Blue_all by blast

lemma disjnt_Red_Blue_Neighbours: "disjnt (Neighbours Red x \<inter> X) (Neighbours Blue x \<inter> X')"
  using disjnt_Red_Blue by (auto simp: disjnt_def Neighbours_def)

lemma indep_Red_iff_clique_Blue: "K \<subseteq> V \<Longrightarrow> indep K Red \<longleftrightarrow> clique K Blue"
  using Blue_eq by auto

lemma Red_Blue_RN:
  fixes X :: "'a set"
  assumes "card X \<ge> RN m n" "X\<subseteq>V"
  shows "\<exists>K \<subseteq> X. size_clique m K Red \<or> size_clique n K Blue"
  using partn_lst_imp_is_clique_RN [OF is_Ramsey_number_RN [of m n]]  assms indep_Red_iff_clique_Blue 
  unfolding is_clique_RN_def size_clique_def clique_indep_def
  by (metis finV finite_subset subset_eq)

end

context Book
begin

lemma Red_edges_XY0: "Red \<inter> all_edges_betw_un X0 Y0 \<noteq> {}" 
  using density_ge_p0_min p0_min
  by (auto simp: gen_density_def edge_card_def)

lemma finite_X0: "finite X0" and finite_Y0: "finite Y0"
  using XY0 finV finite_subset by blast+

lemma Red_nonempty: "Red \<noteq> {}"
  using Red_edges_XY0 by blast

lemma gorder_ge2: "gorder \<ge> 2"
  using Red_nonempty
  by (metis Red_E card_mono equals0I finV subset_empty two_edges wellformed)

lemma nontriv: "E \<noteq> {}"
  using Red_E Red_nonempty by force

lemma no_singleton_Blue [simp]: "{a} \<notin> Blue"
  using Blue_E by auto

lemma no_singleton_Red [simp]: "{a} \<notin> Red"
  using Red_E by auto

lemma not_Red_Neighbour [simp]: "x \<notin> Neighbours Red x" and not_Blue_Neighbour [simp]: "x \<notin> Neighbours Blue x"
  using Red_E Blue_E not_own_Neighbour by auto

lemma Neighbours_RB:
  assumes "a \<in> V" "X\<subseteq>V"
  shows "Neighbours Red a \<inter> X \<union> Neighbours Blue a \<inter> X = X - {a}"
  using assms Red_Blue_all complete singleton_not_edge
  by (fastforce simp: Neighbours_def)

lemma Neighbours_Red_Blue: 
  assumes "x \<in> V" 
  shows "Neighbours Red x = V - insert x (Neighbours Blue x)"
  using Red_E assms by (auto simp: Blue_eq Neighbours_def complete all_edges_def)

abbreviation "red_density X Y \<equiv> gen_density Red X Y"
abbreviation "blue_density X Y \<equiv> gen_density Blue X Y"

definition Weight :: "['a set, 'a set, 'a, 'a] \<Rightarrow> real" where
  "Weight \<equiv> \<lambda>X Y x y. inverse (card Y) * (card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y)
                      - red_density X Y * card (Neighbours Red x \<inter> Y))"

definition weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "weight \<equiv> \<lambda>X Y x. \<Sum>y \<in> X-{x}. Weight X Y x y"

definition p0 :: "real"
  where "p0 \<equiv> red_density X0 Y0"

definition qfun :: "nat \<Rightarrow> real"
  where "qfun \<equiv> \<lambda>h. p0 + qfun_base k h"

lemma qfun_eq: "qfun \<equiv> \<lambda>h. p0 + ((1 + eps)^h - 1) / k"
  by (simp add: qfun_def qfun_base_def epsilon_def epsilon_def)

definition hgt :: "real \<Rightarrow> nat"
  where "hgt \<equiv> \<lambda>p. LEAST h. p \<le> qfun h \<and> h>0"

lemma qfun0 [simp]: "qfun 0 = p0"
  by (simp add: qfun_eq)

lemma p0_ge: "p0 \<ge> p0_min" 
  using density_ge_p0_min by (simp add: p0_def)

lemma card_XY0: "card X0 > 0" "card Y0 > 0"
  using Red_edges_XY0 finite_X0 finite_Y0 by force+

lemma finite_Red [simp]: "finite Red"
  by (metis Red_Blue_all complete fin_edges finite_Un)

lemma finite_Blue [simp]: "finite Blue"
  using Blue_E fin_edges finite_subset by blast

lemma Red_edges_nonzero: "edge_card Red X0 Y0 > 0"
  using Red_edges_XY0
  using Red_E edge_card_def fin_edges finite_subset by fastforce

lemma p0_01: "0 < p0" "p0 \<le> 1"
proof -
  show "0 < p0"
    using Red_edges_nonzero card_XY0
    by (auto simp: p0_def gen_density_def divide_simps mult_less_0_iff)
  show "p0 \<le> 1"
    by (simp add: gen_density_le1 p0_def)
qed

lemma qfun_strict_mono: "h'<h \<Longrightarrow> qfun h' < qfun h"
  by (simp add: divide_strict_right_mono eps_gt0 kn0 qfun_eq)

lemma qfun_mono: "h'\<le>h \<Longrightarrow> qfun h' \<le> qfun h"
  by (metis less_eq_real_def nat_less_le qfun_strict_mono)

lemma q_Suc_diff: "qfun (Suc h) - qfun h = eps * (1 + eps)^h / k"
  by (simp add: qfun_eq field_split_simps)

lemma height_exists':
  obtains h where "p \<le> qfun_base k h \<and> h>0"
proof -
  have 1: "1 + eps \<ge> 1"
    by (auto simp: epsilon_def)
  have "\<forall>\<^sup>\<infinity>h. p \<le> real h * eps / real k"
    using p0_01 kn0 unfolding epsilon_def by real_asymp
  then obtain h where "p \<le> real h * eps / real k"
    by (meson eventually_sequentially order.refl)
  also have "\<dots> \<le> ((1 + eps) ^ h - 1) / real k"
    using linear_plus_1_le_power [of "eps" h]
    by (intro divide_right_mono add_mono) (auto simp: epsilon_def add_ac)
  also have "\<dots> \<le> ((1 + eps) ^ Suc h - 1) / real k"
    using power_increasing [OF le_SucI [OF order_refl] 1]
    by (simp add: divide_right_mono)
  finally have "p \<le> qfun_base k (Suc h)"
    unfolding qfun_base_def epsilon_def epsilon_def using p0_01 by blast
  then show thesis
    using that by blast 
qed


lemma height_exists:
  obtains h where "p \<le> qfun h" "h>0"
proof -
  obtain h' where "p \<le> qfun_base k h' \<and> h'>0"
    using height_exists' by blast
  then show thesis
    using p0_01 qfun_def that
    by (metis add_strict_increasing less_eq_real_def)
qed

lemma hgt_gt0: "hgt p > 0"
  unfolding hgt_def
  by (smt (verit, best) LeastI height_exists kn0)

lemma hgt_works: "p \<le> qfun (hgt p)"
  by (metis (no_types, lifting) LeastI height_exists hgt_def)

lemma hgt_Least:
  assumes "0<h" "p \<le> qfun h"
  shows "hgt p \<le> h"
  by (simp add: Suc_leI assms hgt_def Least_le)

lemma real_hgt_Least:
  assumes "real h \<le> r" "0<h" "p \<le> qfun h"
  shows "real (hgt p) \<le> r"
  using assms by (meson assms order.trans hgt_Least of_nat_mono)

lemma hgt_greater:
  assumes "p > qfun h"
  shows "hgt p > h"
  by (meson assms hgt_works kn0 not_less order.trans qfun_mono)

lemma hgt_less_imp_qfun_less:
  assumes "0<h" "h < hgt p"
  shows "p > qfun h"
  by (metis assms hgt_Least not_le)  

lemma hgt_le_imp_qfun_ge:
  assumes "hgt p \<le> h"
  shows "p \<le> qfun h"
  by (meson assms hgt_greater not_less)

text \<open>This gives us an upper bound for heights, namely @{term "hgt 1"}, but it's not explicit.\<close>
lemma hgt_mono:
  assumes "p \<le> q"
  shows "hgt p \<le> hgt q"
  by (meson assms order.trans hgt_Least hgt_gt0 hgt_works)

lemma hgt_mono':
  assumes "hgt p < hgt q"
  shows "p < q"
  by (smt (verit) assms hgt_mono leD)

text \<open>The upper bound of the height $h(p)$ appears just below (5) on page 9.
  Although we can bound all Heights by monotonicity (since @{term "p\<le>1"}), 
  we need to exhibit a specific $o(k)$ function.\<close>
lemma height_upper_bound:
  assumes "p \<le> 1" and big: "Big_height_upper_bound k"
  shows "hgt p \<le> 2 * ln k / eps"
  using assms real_hgt_Least big nat_floor_neg not_gr0 of_nat_floor
  unfolding Big_height_upper_bound_def hgt_maximum_def
  by (smt (verit) epsilon_def hgt_Least of_nat_mono p0_01(1) qfun0 qfun_def)

definition alpha :: "nat \<Rightarrow> real" where "alpha \<equiv> \<lambda>h. qfun h - qfun (h-1)"

lemma alpha_ge0: "alpha h \<ge> 0"
  by (simp add: alpha_def qfun_eq divide_le_cancel eps_gt0)

lemma alpha_Suc_ge: "alpha (Suc h) \<ge> eps / k"
proof -
  have "(1 + eps) ^ h \<ge> 1"
    by (simp add: epsilon_def)
  then show ?thesis
    by (simp add: alpha_def qfun_eq eps_gt0 field_split_simps)
qed

lemma alpha_ge: "h>0 \<Longrightarrow> alpha h \<ge> eps / k"
  by (metis Suc_pred alpha_Suc_ge)

lemma alpha_gt0: "h>0 \<Longrightarrow> alpha h > 0"
  by (metis alpha_ge alpha_ge0 eps_gt0 kn0 nle_le not_le of_nat_0_less_iff zero_less_divide_iff)

lemma alpha_Suc_eq: "alpha (Suc h) = eps * (1 + eps) ^ h / k"
  by (simp add: alpha_def q_Suc_diff)

lemma alpha_eq: 
  assumes "h>0" shows "alpha h = eps * (1 + eps) ^ (h-1) / k"
  by (metis Suc_pred' alpha_Suc_eq assms)

lemma alpha_hgt_eq: "alpha (hgt p) = eps * (1 + eps) ^ (hgt p -1) / k"
  using alpha_eq hgt_gt0 by presburger

lemma alpha_mono: "\<lbrakk>h' \<le> h; 0 < h'\<rbrakk> \<Longrightarrow> alpha h' \<le> alpha h"
  by (simp add: alpha_eq eps_ge0 divide_right_mono mult_left_mono power_increasing)

definition all_incident_edges :: "'a set \<Rightarrow> 'a set set" where
    "all_incident_edges \<equiv> \<lambda>A. \<Union>v\<in>A. incident_edges v"

lemma all_incident_edges_Un [simp]: "all_incident_edges (A\<union>B) = all_incident_edges A \<union> all_incident_edges B"
  by (auto simp: all_incident_edges_def)

end

context Book
begin

subsection \<open>State invariants\<close>

definition "V_state \<equiv> \<lambda>(X,Y,A,B). X\<subseteq>V \<and> Y\<subseteq>V \<and> A\<subseteq>V \<and> B\<subseteq>V"

definition "disjoint_state \<equiv> \<lambda>(X,Y,A,B). disjnt X Y \<and> disjnt X A \<and> disjnt X B \<and> disjnt Y A \<and> disjnt Y B \<and> disjnt A B"

text \<open>previously had all edges incident to A, B\<close>
definition "RB_state \<equiv> \<lambda>(X,Y,A,B). all_edges_betw_un A A \<subseteq> Red \<and> all_edges_betw_un A (X \<union> Y) \<subseteq> Red
             \<and> all_edges_betw_un B (B \<union> X) \<subseteq> Blue"

definition "valid_state \<equiv> \<lambda>U. V_state U \<and> disjoint_state U \<and> RB_state U"

definition "termination_condition \<equiv> \<lambda>X Y. card X \<le> RN k (nat \<lceil>real l powr (3/4)\<rceil>) \<or> red_density X Y \<le> 1/k"

lemma 
  assumes "V_state(X,Y,A,B)" 
  shows finX: "finite X" and finY: "finite Y" and finA: "finite A" and finB: "finite B"
  using V_state_def assms finV finite_subset by auto

lemma 
  assumes "valid_state(X,Y,A,B)" 
  shows A_Red_clique: "clique A Red" and B_Blue_clique: "clique B Blue"
  using assms
  by (auto simp: valid_state_def V_state_def RB_state_def all_edges_betw_un_iff_clique all_edges_betw_un_Un2)

lemma A_less_k:
  assumes valid: "valid_state(X,Y,A,B)" 
  shows "card A < k"
  using assms A_Red_clique[OF valid] no_Red_clique unfolding valid_state_def V_state_def
  by (metis nat_neq_iff prod.case size_clique_def size_clique_smaller)

lemma B_less_l:
  assumes valid: "valid_state(X,Y,A,B)"
  shows "card B < l"
  using assms B_Blue_clique[OF valid] no_Blue_clique unfolding valid_state_def V_state_def
  by (metis nat_neq_iff prod.case size_clique_def size_clique_smaller)


subsection \<open>Degree regularisation\<close>

definition "red_dense \<equiv> \<lambda>Y p x. card (Neighbours Red x \<inter> Y) \<ge> (p - eps powr (-1/2) * alpha (hgt p)) * card Y"

definition "X_degree_reg \<equiv> \<lambda>X Y. {x \<in> X. red_dense Y (red_density X Y) x}"

definition "degree_reg \<equiv> \<lambda>(X,Y,A,B). (X_degree_reg X Y, Y, A, B)"

lemma X_degree_reg_subset: "X_degree_reg X Y \<subseteq> X"
  by (auto simp: X_degree_reg_def)

lemma degree_reg_V_state: "V_state U \<Longrightarrow> V_state (degree_reg U)"
  by (auto simp: degree_reg_def X_degree_reg_def V_state_def)

lemma degree_reg_disjoint_state: "disjoint_state U \<Longrightarrow> disjoint_state (degree_reg U)"
  by (auto simp: degree_reg_def X_degree_reg_def disjoint_state_def disjnt_iff)

lemma degree_reg_RB_state: "RB_state U \<Longrightarrow> RB_state (degree_reg U)"
  apply (simp add: degree_reg_def RB_state_def all_edges_betw_un_Un2 split: prod.split prod.split_asm)
  by (meson X_degree_reg_subset all_edges_betw_un_mono2 order.trans)

lemma degree_reg_valid_state: "valid_state U \<Longrightarrow> valid_state (degree_reg U)"
  by (simp add: degree_reg_RB_state degree_reg_V_state degree_reg_disjoint_state valid_state_def)

lemma not_red_dense_sum_less:
  assumes "\<And>x. x \<in> X \<Longrightarrow> \<not> red_dense Y p x" and "X\<noteq>{}" "finite X"
  shows "(\<Sum>x\<in>X. card (Neighbours Red x \<inter> Y)) < p * real (card Y) * card X"
proof -
  have "\<And>x. x \<in> X \<Longrightarrow> card (Neighbours Red x \<inter> Y) < p * real (card Y)"
    using assms
    unfolding red_dense_def
    by (smt (verit) alpha_ge0 mult_right_mono of_nat_0_le_iff powr_ge_zero zero_le_mult_iff)
  with \<open>X\<noteq>{}\<close> show ?thesis
    by (smt (verit) \<open>finite X\<close> of_nat_sum sum_strict_mono mult_of_nat_commute sum_constant)
qed

lemma red_density_X_degree_reg_ge:
  assumes "disjnt X Y"
  shows "red_density (X_degree_reg X Y) Y \<ge> red_density X Y"
proof (cases "X={} \<or> infinite X \<or> infinite Y")
  case True
  then show ?thesis
    by (force simp: gen_density_def X_degree_reg_def)
next
  case False
  then have "finite X" "finite Y"
    by auto
  { assume "\<And>x. x \<in> X \<Longrightarrow> \<not> red_dense Y (red_density X Y) x"
    with False have "(\<Sum>x\<in>X. card (Neighbours Red x \<inter> Y)) < red_density X Y * real (card Y) * card X"
      using \<open>finite X\<close> not_red_dense_sum_less by blast
    with Red_E have "edge_card Red Y X < (red_density X Y * real (card Y)) * card X"
      by (metis False assms disjnt_sym edge_card_eq_sum_Neighbours)
    then have False
      by (simp add: gen_density_def edge_card_commute split: if_split_asm)
  }
  then obtain x where x: "x \<in> X" "red_dense Y (red_density X Y) x"
    by blast
  define X' where "X' \<equiv> {x \<in> X. \<not> red_dense Y (red_density X Y) x}"
  have X': "finite X'" "disjnt Y X'"
    using assms \<open>finite X\<close> by (auto simp: X'_def disjnt_iff)
  have eq: "X_degree_reg X Y = X - X'"
    by (auto simp: X_degree_reg_def X'_def)
  show ?thesis
  proof (cases "X'={}")
    case True
    then show ?thesis
      by (simp add: eq)
  next
    case False
    show ?thesis 
      unfolding eq
    proof (rule gen_density_below_avg_ge)
      have "(\<Sum>x\<in>X'. card (Neighbours Red x \<inter> Y)) < red_density X Y * real (card Y) * card X'"
      proof (intro not_red_dense_sum_less)
        fix x
        assume "x \<in> X'"
        show "\<not> red_dense Y (red_density X Y) x"
          using \<open>x \<in> X'\<close> by (simp add: X'_def)
      qed (use False X' in auto)
      then have "card X * (\<Sum>x\<in>X'. card (Neighbours Red x \<inter> Y)) < card X' * edge_card Red Y X"
        by (simp add: gen_density_def mult.commute divide_simps edge_card_commute
            flip: of_nat_sum of_nat_mult split: if_split_asm)
      then have "card X * (\<Sum>x\<in>X'. card (Neighbours Red x \<inter> Y)) \<le> card X' * (\<Sum>x\<in>X. card (Neighbours Red x \<inter> Y))"
        using assms Red_E
        by (metis \<open>finite X\<close> disjnt_sym edge_card_eq_sum_Neighbours nless_le)
      then have "red_density Y X' \<le> red_density Y X"
        using assms X' False \<open>finite X\<close>
        apply (simp add: gen_density_def edge_card_eq_sum_Neighbours disjnt_commute Red_E)
        apply (simp add: X'_def field_split_simps flip: of_nat_sum of_nat_mult)
        done
      then show "red_density X' Y \<le> red_density X Y"
        by (simp add: X'_def gen_density_commute)
    qed (use assms x \<open>finite X\<close> \<open>finite Y\<close> X'_def in auto)
  qed
qed

subsection \<open>Big blue steps: code\<close>

definition bluish :: "['a set,'a] \<Rightarrow> bool" where
  "bluish \<equiv> \<lambda>X x. card (Neighbours Blue x \<inter> X) \<ge> \<mu> * real (card X)"

definition many_bluish :: "'a set \<Rightarrow> bool" where
  "many_bluish \<equiv> \<lambda>X. card {x\<in>X. bluish X x} \<ge> RN k (nat \<lceil>l powr (2/3)\<rceil>)"

definition good_blue_book :: "['a set, 'a set \<times> 'a set] \<Rightarrow> bool" where
 "good_blue_book \<equiv> \<lambda>X. \<lambda>(S,T). book S T Blue \<and> S\<subseteq>X \<and> T\<subseteq>X \<and> card T \<ge> (\<mu> ^ card S) * card X / 2"

lemma ex_good_blue_book: "good_blue_book X ({}, X)"
  by (simp add: good_blue_book_def book_def)

lemma bounded_good_blue_book: "\<lbrakk>good_blue_book X (S,T); finite X\<rbrakk> \<Longrightarrow> card S \<le> card X"
  by (simp add: card_mono finX good_blue_book_def)

definition best_blue_book_card :: "'a set \<Rightarrow> nat" where
  "best_blue_book_card \<equiv> \<lambda>X. GREATEST s. \<exists>S T. good_blue_book X (S,T) \<and> s = card S"

lemma best_blue_book_is_best: "\<lbrakk>good_blue_book X (S,T); finite X\<rbrakk> \<Longrightarrow> card S \<le> best_blue_book_card X"
  unfolding best_blue_book_card_def
  by (smt (verit) Greatest_le_nat bounded_good_blue_book)

lemma ex_best_blue_book: "finite X \<Longrightarrow> \<exists>S T. good_blue_book X (S,T) \<and> card S = best_blue_book_card X"
  unfolding best_blue_book_card_def
  by (smt (verit) GreatestI_ex_nat bounded_good_blue_book ex_good_blue_book)

definition "choose_blue_book \<equiv> \<lambda>(X,Y,A,B). @(S,T). good_blue_book X (S,T) \<and> card S = best_blue_book_card X"

lemma choose_blue_book_works: 
  "\<lbrakk>finite X; (S,T) = choose_blue_book (X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> good_blue_book X (S,T) \<and> card S = best_blue_book_card X"
  unfolding choose_blue_book_def
  using someI_ex [OF ex_best_blue_book]
  by (metis (mono_tags, lifting) case_prod_conv someI_ex)

lemma choose_blue_book_subset: 
  "\<lbrakk>finite X; (S,T) = choose_blue_book (X,Y,A,B)\<rbrakk> \<Longrightarrow> S \<subseteq> X \<and> T \<subseteq> X \<and> disjnt S T"
  using choose_blue_book_works good_blue_book_def book_def by fastforce


text \<open>expressing the complicated preconditions inductively\<close>
inductive big_blue
  where "\<lbrakk>many_bluish X; good_blue_book X (S,T); card S = best_blue_book_card X\<rbrakk> \<Longrightarrow> big_blue (X,Y,A,B) (T, Y, A, B\<union>S)"

lemma big_blue_V_state: "\<lbrakk>big_blue U U'; V_state U\<rbrakk> \<Longrightarrow> V_state U'"
  by (force simp: good_blue_book_def V_state_def elim!: big_blue.cases)

lemma big_blue_disjoint_state: "\<lbrakk>big_blue U U'; disjoint_state U\<rbrakk> \<Longrightarrow> disjoint_state U'"
  by (force simp: book_def disjnt_iff good_blue_book_def disjoint_state_def elim!: big_blue.cases)

lemma big_blue_RB_state: "\<lbrakk>big_blue U U'; RB_state U\<rbrakk> \<Longrightarrow> RB_state U'"
  apply (clarsimp simp add: good_blue_book_def book_def RB_state_def all_edges_betw_un_Un1 all_edges_betw_un_Un2 elim!: big_blue.cases)
  by (metis all_edges_betw_un_commute all_edges_betw_un_mono1 le_supI2 sup.orderE)

lemma big_blue_valid_state: "\<lbrakk>big_blue U U'; valid_state U\<rbrakk> \<Longrightarrow> valid_state U'"
  by (meson big_blue_RB_state big_blue_V_state big_blue_disjoint_state valid_state_def)

subsection \<open>The central vertex\<close>

definition central_vertex :: "['a set,'a] \<Rightarrow> bool" where
  "central_vertex \<equiv> \<lambda>X x. x \<in> X \<and> card (Neighbours Blue x \<inter> X) \<le> \<mu> * real (card X)"

lemma ex_central_vertex:
  assumes "\<not> termination_condition X Y" "\<not> many_bluish X"
  shows "\<exists>x. central_vertex X x"
proof -
  have "l \<noteq> 0"
    using linorder_not_less assms unfolding many_bluish_def by force
  then have *: "real l powr (2/3) \<le> real l powr (3/4)"
    using powr_mono by force
  then have "card {x \<in> X. bluish X x} < card X"
    using assms RN_mono
    unfolding termination_condition_def many_bluish_def not_le
    by (smt (verit, ccfv_SIG) linorder_not_le nat_ceiling_le_eq of_nat_le_iff)
  then obtain x where "x \<in> X" "\<not> bluish X x"
    by (metis (mono_tags, lifting) mem_Collect_eq nat_neq_iff subsetI subset_antisym)
  then show ?thesis
    by (meson bluish_def central_vertex_def linorder_linear)
qed

lemma finite_central_vertex_set: "finite X \<Longrightarrow> finite {x. central_vertex X x}"
  by (simp add: central_vertex_def)

definition max_central_vx :: "['a set,'a set] \<Rightarrow> real" where
  "max_central_vx \<equiv> \<lambda>X Y. Max (weight X Y ` {x. central_vertex X x})"

lemma central_vx_is_best: 
  "\<lbrakk>central_vertex X x; finite X\<rbrakk> \<Longrightarrow> weight X Y x \<le> max_central_vx X Y"
  unfolding max_central_vx_def by (simp add: finite_central_vertex_set)

lemma ex_best_central_vx: 
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish X; finite X\<rbrakk> 
  \<Longrightarrow> \<exists>x. central_vertex X x \<and> weight X Y x = max_central_vx X Y"
  unfolding max_central_vx_def
  by (metis empty_iff ex_central_vertex finite_central_vertex_set mem_Collect_eq obtains_MAX)

text \<open>it's necessary to make a specific choice; a relational treatment might allow different vertices 
  to be chosen, making a nonsense of the choice between steps 4 and 5\<close>
definition "choose_central_vx \<equiv> \<lambda>(X,Y,A,B). @x. central_vertex X x \<and> weight X Y x = max_central_vx X Y"

lemma choose_central_vx_works: 
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish X; finite X\<rbrakk> 
  \<Longrightarrow> central_vertex X (choose_central_vx (X,Y,A,B)) \<and> weight X Y (choose_central_vx (X,Y,A,B)) = max_central_vx X Y"
  unfolding choose_central_vx_def
  using someI_ex [OF ex_best_central_vx] by force

lemma choose_central_vx_X: 
  "\<lbrakk>\<not> many_bluish X; \<not> termination_condition X Y; finite X\<rbrakk> \<Longrightarrow> choose_central_vx (X,Y,A,B) \<in> X"
  using central_vertex_def choose_central_vx_works by fastforce

subsection \<open>Red step\<close>

definition "reddish \<equiv> \<lambda>k X Y p x. red_density (Neighbours Red x \<inter> X) (Neighbours Red x \<inter> Y) \<ge> p - alpha (hgt p)"

inductive red_step 
  where "\<lbrakk>reddish k X Y (red_density X Y) x; x = choose_central_vx (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> red_step (X,Y,A,B) (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)"

lemma red_step_V_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" 
          "\<not> many_bluish X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "X \<subseteq> V"
    using assms by (auto simp: V_state_def)
  then have "choose_central_vx (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X by (fastforce simp: finX)
  with assms show ?thesis
    by (auto simp: V_state_def elim!: red_step.cases)
qed

lemma red_step_disjoint_state:
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" 
          "\<not> many_bluish X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> X"
    using assms by (metis choose_central_vx_X finX)
  with assms show ?thesis
    by (auto simp: disjoint_state_def disjnt_iff not_own_Neighbour elim!: red_step.cases)
qed

lemma red_step_RB_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y"
          "\<not> many_bluish X" "V_state (X,Y,A,B)" "RB_state (X,Y,A,B)"
  shows "RB_state U'"
proof -
  define x where "x \<equiv> choose_central_vx (X, Y, A, B)"
  have [simp]: "finite X"
    using assms by (simp add: finX)
  have "x \<in> X"
    using assms choose_central_vx_X by (metis \<open>finite X\<close> x_def)
  have A: "all_edges_betw_un (insert x A) (insert x A) \<subseteq> Red"
    if "all_edges_betw_un A A \<subseteq> Red" "all_edges_betw_un A (X \<union> Y) \<subseteq> Red"
    using that \<open>x \<in> X\<close> all_edges_betw_un_commute 
    by (auto simp: all_edges_betw_un_insert2 all_edges_betw_un_Un2 intro!: all_uedges_betw_I)
  have B1: "all_edges_betw_un (insert x A) (Neighbours Red x \<inter> X) \<subseteq> Red"
    if "all_edges_betw_un A X \<subseteq> Red"
    using that \<open>x \<in> X\<close> by (force simp: all_edges_betw_un_def in_Neighbours_iff)
  have B2: "all_edges_betw_un (insert x A) (Neighbours Red x \<inter> Y) \<subseteq> Red"
    if "all_edges_betw_un A Y \<subseteq> Red"
    using that \<open>x \<in> X\<close> by (force simp: all_edges_betw_un_def in_Neighbours_iff)
  from assms A B1 B2 show ?thesis
    apply (clarsimp simp: RB_state_def simp flip: x_def elim!: red_step.cases)
    by (metis Int_Un_eq(2) Un_subset_iff all_edges_betw_un_Un2)
qed

lemma red_step_valid_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" 
          "\<not> many_bluish X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms red_step_RB_state red_step_V_state red_step_disjoint_state valid_state_def)

subsection \<open>Density-boost step\<close>

inductive density_boost
  where "\<lbrakk>\<not> reddish k X Y (red_density X Y) x; x = choose_central_vx (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> density_boost (X,Y,A,B) (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"

lemma density_boost_V_state: 
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" 
          "\<not> many_bluish X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "X \<subseteq> V"
    using assms by (auto simp: V_state_def)
  then have "choose_central_vx (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X finX by fastforce 
  with assms show ?thesis
    by (auto simp: V_state_def elim!: density_boost.cases)
qed

lemma density_boost_disjoint_state:
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y"  
          "\<not> many_bluish X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "X \<subseteq> V"
    using assms by (auto simp: V_state_def)
  then have "choose_central_vx (X, Y, A, B) \<in> X"
    using assms by (metis choose_central_vx_X finX)
  with assms show ?thesis
    by (auto simp: disjoint_state_def disjnt_iff not_own_Neighbour elim!: density_boost.cases)
qed

lemma density_boost_RB_state: 
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "V_state (X,Y,A,B)" 
    and rb: "RB_state (X,Y,A,B)"
  shows "RB_state U'"
proof -
  define x where "x \<equiv> choose_central_vx (X, Y, A, B)"
  have "x \<in> X"
    using assms by (metis choose_central_vx_X finX x_def)
  have "all_edges_betw_un A (Neighbours Blue x \<inter> X \<union> Neighbours Red x \<inter> Y) \<subseteq> Red"
    if "all_edges_betw_un A (X \<union> Y) \<subseteq> Red"
    using that by (metis Int_Un_eq(4) Un_subset_iff all_edges_betw_un_Un2)
  moreover
  have "all_edges_betw_un (insert x B) (insert x B) \<subseteq> Blue"
    if "all_edges_betw_un B (B \<union> X) \<subseteq> Blue"
    using that \<open>x \<in> X\<close> by (auto simp: subset_iff set_eq_iff all_edges_betw_un_def)
  moreover
  have "all_edges_betw_un (insert x B) (Neighbours Blue x \<inter> X) \<subseteq> Blue"
    if "all_edges_betw_un B (B \<union> X) \<subseteq> Blue"
    using \<open>x \<in> X\<close> that  by (auto simp: all_edges_betw_un_def subset_iff in_Neighbours_iff)
  ultimately show ?thesis
    using assms
    by (auto simp: RB_state_def all_edges_betw_un_Un2 x_def [symmetric]  elim!: density_boost.cases)
qed

lemma density_boost_valid_state:
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms density_boost_RB_state density_boost_V_state density_boost_disjoint_state valid_state_def)

subsection \<open>Execution steps 2--5 as a function\<close>

definition next_state :: "'a config \<Rightarrow> 'a config" where
  "next_state \<equiv> \<lambda>(X,Y,A,B). 
       if many_bluish X 
       then let (S,T) = choose_blue_book (X,Y,A,B) in (T, Y, A, B\<union>S) 
       else let x = choose_central_vx (X,Y,A,B) in
            if reddish k X Y (red_density X Y) x 
            then (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)
            else (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"

lemma next_state_valid:
  assumes "valid_state (X,Y,A,B)" "\<not> termination_condition X Y"
  shows "valid_state (next_state (X,Y,A,B))"
proof (cases "many_bluish X")
  case True
  with finX have "big_blue (X,Y,A,B) (next_state (X,Y,A,B))"
    apply (simp add: next_state_def split: prod.split)
    by (metis assms(1) big_blue.intros choose_blue_book_works valid_state_def)
  then show ?thesis
    using assms big_blue_valid_state by blast
next
  case non_bluish: False
  define x where "x = choose_central_vx (X,Y,A,B)"
  show ?thesis
  proof (cases "reddish k X Y (red_density X Y) x")
    case True
    with non_bluish have "red_step (X,Y,A,B) (next_state (X,Y,A,B))"
      by (simp add: next_state_def Let_def x_def red_step.intros split: prod.split)
    then show ?thesis
      using assms non_bluish red_step_valid_state by blast      
  next
    case False
    with non_bluish have "density_boost (X,Y,A,B) (next_state (X,Y,A,B))"
      by (simp add: next_state_def Let_def x_def density_boost.intros split: prod.split)
    then show ?thesis
      using assms density_boost_valid_state non_bluish by blast
  qed
qed

primrec stepper :: "nat \<Rightarrow> 'a config" where
  "stepper 0 = (X0,Y0,{},{})"
| "stepper (Suc n) = 
     (let (X,Y,A,B) = stepper n in 
      if termination_condition X Y then (X,Y,A,B) 
      else if even n then degree_reg (X,Y,A,B) else next_state (X,Y,A,B))"

lemma degree_reg_subset:
  assumes "degree_reg (X,Y,A,B) = (X',Y',A',B')" 
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms by (auto simp: degree_reg_def X_degree_reg_def)

lemma next_state_subset:
  assumes "next_state (X,Y,A,B) = (X',Y',A',B')" "finite X"
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms choose_blue_book_subset
  apply (clarsimp simp: next_state_def valid_state_def Let_def split: if_split_asm prod.split_asm)
  by (smt (verit) choose_blue_book_subset subset_eq)

lemma valid_state0: "valid_state (X0, Y0, {}, {})"
  using XY0 by (simp add: valid_state_def V_state_def disjoint_state_def RB_state_def)

lemma valid_state_stepper [simp]: "valid_state (stepper n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: stepper_def valid_state0)
next
  case (Suc n)
  then show ?case
    by (force simp: next_state_valid degree_reg_valid_state split: prod.split)
qed

lemma V_state_stepper: "V_state (stepper n)"
  using valid_state_def valid_state_stepper by force

lemma RB_state_stepper: "RB_state (stepper n)"
  using valid_state_def valid_state_stepper by force

lemma
  assumes "stepper n = (X,Y,A,B)"
  shows stepper_A: "clique A Red \<and> A\<subseteq>V" and stepper_B: "clique B Blue \<and> B\<subseteq>V"
proof -
  have "A\<subseteq>V" "B\<subseteq>V"
    using V_state_stepper[of n] assms by (auto simp: V_state_def)
  moreover
  have "all_edges_betw_un A A \<subseteq> Red" "all_edges_betw_un B B \<subseteq> Blue"
    using RB_state_stepper[of n] assms by (auto simp: RB_state_def all_edges_betw_un_Un2)
  ultimately show "clique A Red \<and> A\<subseteq>V" "clique B Blue \<and> B\<subseteq>V"
    using all_edges_betw_un_iff_clique by auto
qed

lemma card_B_limit:
  assumes "stepper n = (X,Y,A,B)" shows "card B < l"
  by (metis B_less_l assms valid_state_stepper)

definition "Xseq \<equiv> (\<lambda>(X,Y,A,B). X) \<circ> stepper"
definition "Yseq \<equiv> (\<lambda>(X,Y,A,B). Y) \<circ> stepper"
definition "Aseq \<equiv> (\<lambda>(X,Y,A,B). A) \<circ> stepper"
definition "Bseq \<equiv> (\<lambda>(X,Y,A,B). B) \<circ> stepper"
definition "pseq \<equiv> \<lambda>n. red_density (Xseq n) (Yseq n)"

definition "pee \<equiv> \<lambda>i. red_density (Xseq i) (Yseq i)"

lemma Xseq_0 [simp]: "Xseq 0 = X0"
  by (simp add: Xseq_def)

lemma Xseq_Suc_subset: "Xseq (Suc i) \<subseteq> Xseq i" and  Yseq_Suc_subset: "Yseq (Suc i) \<subseteq> Yseq i"
   apply (simp_all add: Xseq_def Yseq_def split: if_split_asm prod.split)
  by (metis V_state_stepper degree_reg_subset finX next_state_subset)+

lemma Xseq_antimono: "j \<le> i \<Longrightarrow> Xseq i \<subseteq> Xseq j"
  by (simp add: Xseq_Suc_subset lift_Suc_antimono_le)

lemma Xseq_subset_V: "Xseq i \<subseteq> V"
  using XY0 Xseq_0 Xseq_antimono by blast

lemma finite_Xseq: "finite (Xseq i)"
  by (meson Xseq_subset_V finV finite_subset)

lemma Yseq_0 [simp]: "Yseq 0 = Y0"
  by (simp add: Yseq_def)

lemma Yseq_antimono: "j \<le> i \<Longrightarrow> Yseq i \<subseteq> Yseq j"
  by (simp add: Yseq_Suc_subset lift_Suc_antimono_le)

lemma Yseq_subset_V: "Yseq i \<subseteq> V"
  using XY0 Yseq_0 Yseq_antimono by blast

lemma finite_Yseq: "finite (Yseq i)"
  by (meson Yseq_subset_V finV finite_subset)

lemma Xseq_Yseq_disjnt: "disjnt (Xseq i) (Yseq i)"
  by (metis XY0(1) Xseq_0 Xseq_antimono Yseq_0 Yseq_antimono disjnt_subset1 disjnt_sym zero_le)

lemma edge_card_eq_pee: 
  "edge_card Red (Xseq i) (Yseq i) = pee i * card (Xseq i) * card (Yseq i)"
  by (simp add: pee_def gen_density_def finite_Xseq finite_Yseq)

lemma valid_state_seq: "valid_state(Xseq i, Yseq i, Aseq i, Bseq i)"
  using valid_state_stepper[of i]
  by (force simp: Xseq_def Yseq_def Aseq_def Bseq_def simp del: valid_state_stepper split: prod.split)

lemma Aseq_less_k: "card (Aseq i) < k"
  by (meson A_less_k valid_state_seq)

lemma Aseq_0 [simp]: "Aseq 0 = {}"
  by (simp add: Aseq_def)

lemma Aseq_Suc_subset: "Aseq i \<subseteq> Aseq (Suc i)" and Bseq_Suc_subset: "Bseq i \<subseteq> Bseq (Suc i)"
  by (auto simp: Aseq_def Bseq_def next_state_def degree_reg_def Let_def split: prod.split)

lemma
  assumes "j \<le> i"
  shows Aseq_mono: "Aseq j \<subseteq> Aseq i" and Bseq_mono: "Bseq j \<subseteq> Bseq i"
  using assms by (auto simp: Aseq_Suc_subset Bseq_Suc_subset lift_Suc_mono_le)

lemma Aseq_subset_V: "Aseq i \<subseteq> V"
  using stepper_A[of i] by (simp add: Aseq_def split: prod.split) 

lemma Bseq_subset_V: "Bseq i \<subseteq> V"
  using stepper_B[of i] by (simp add: Bseq_def split: prod.split) 

lemma finite_Aseq: "finite (Aseq i)" and finite_Bseq: "finite (Bseq i)"
  by (meson Aseq_subset_V Bseq_subset_V finV finite_subset)+

lemma Bseq_less_l: "card (Bseq i) < l"
  by (meson B_less_l valid_state_seq)

lemma Bseq_0 [simp]: "Bseq 0 = {}"
  by (simp add: Bseq_def)

lemma pee_eq_p0: "pee 0 = p0"
  by (simp add: pee_def p0_def)

lemma pee_ge0: "pee i \<ge> 0"
  by (simp add: gen_density_ge0 pee_def)

lemma pee_le1: "pee i \<le> 1"
  using gen_density_le1 pee_def by presburger

lemma pseq_0: "p0 = pseq 0"
  by (simp add: p0_def pseq_def Xseq_def Yseq_def)

text \<open>The central vertex at each step (though only defined in some cases), 
  @{term "x_i"} in the paper\<close>
definition "cvx \<equiv> \<lambda>i. choose_central_vx (stepper i)"

text \<open>the indexing of @{term beta} is as in the paper --- and different from that of @{term Xseq}\<close>
definition 
  "beta \<equiv> \<lambda>i. let (X,Y,A,B) = stepper i in card(Neighbours Blue (cvx i) \<inter> X) / card X"

lemma beta_eq: "beta i = card(Neighbours Blue (cvx i) \<inter> Xseq i) / card (Xseq i)"
  by (simp add: beta_def cvx_def Xseq_def split: prod.split)

lemma beta_ge0: "beta i \<ge> 0"
  by (simp add: beta_eq)


subsection \<open>The classes of execution steps\<close>

text \<open>For R, B, S, D\<close>
datatype stepkind = red_step | bblue_step | dboost_step | dreg_step | halted

definition next_state_kind :: "'a config \<Rightarrow> stepkind" where
  "next_state_kind \<equiv> \<lambda>(X,Y,A,B). 
       if many_bluish X then bblue_step 
       else let x = choose_central_vx (X,Y,A,B) in
            if reddish k X Y (red_density X Y) x then red_step
            else dboost_step"

definition stepper_kind :: "nat \<Rightarrow> stepkind" where
  "stepper_kind i = 
     (let (X,Y,A,B) = stepper i in 
      if termination_condition X Y then halted 
      else if even i then dreg_step else next_state_kind (X,Y,A,B))"

definition "Step_class \<equiv> \<lambda>knd. {n. stepper_kind n \<in> knd}"

lemma subset_Step_class: "\<lbrakk>i \<in> Step_class K'; K' \<subseteq> K\<rbrakk> \<Longrightarrow> i \<in> Step_class K"
  by (auto simp: Step_class_def)

lemma Step_class_Un: "Step_class (K' \<union> K) = Step_class K' \<union> Step_class K"
  by (auto simp: Step_class_def)

lemma Step_class_insert: "Step_class (insert knd K) = (Step_class {knd}) \<union> (Step_class K)"
  by (auto simp: Step_class_def)

lemma Step_class_insert_NO_MATCH:
  "NO_MATCH {} K \<Longrightarrow> Step_class (insert knd K) = (Step_class {knd}) \<union> (Step_class K)"
  by (auto simp: Step_class_def)

lemma Step_class_UNIV: "Step_class {red_step,bblue_step,dboost_step,dreg_step,halted} = UNIV"
  using Step_class_def stepkind.exhaust by auto

lemma Step_class_cases:
   "i \<in> Step_class {stepkind.red_step} \<or> i \<in> Step_class {bblue_step} \<or>
    i \<in> Step_class {dboost_step} \<or> i \<in> Step_class {dreg_step} \<or>
    i \<in> Step_class {halted}"
  using Step_class_def stepkind.exhaust by auto

lemmas step_kind_defs = Step_class_def stepper_kind_def next_state_kind_def
                        Xseq_def Yseq_def Aseq_def Bseq_def cvx_def Let_def

lemma disjnt_Step_class: 
  "disjnt knd knd' \<Longrightarrow> disjnt (Step_class knd) (Step_class knd')"
  by (auto simp: Step_class_def disjnt_iff)

lemma halted_imp_next_halted: "stepper_kind i = halted \<Longrightarrow> stepper_kind (Suc i) = halted"
  by (auto simp: step_kind_defs split: prod.split if_split_asm)

lemma halted_imp_ge_halted: "stepper_kind i = halted \<Longrightarrow> stepper_kind (i+n) = halted"
  by (induction n) (auto simp: halted_imp_next_halted)

lemma Step_class_halted_forever: "\<lbrakk>i \<in> Step_class {halted}; i\<le>j\<rbrakk> \<Longrightarrow> j \<in> Step_class {halted}"
  by (simp add: Step_class_def) (metis halted_imp_ge_halted le_iff_add)

lemma Step_class_not_halted: "\<lbrakk>i \<notin> Step_class {halted}; i\<ge>j\<rbrakk> \<Longrightarrow> j \<notin> Step_class {halted}"
  using Step_class_halted_forever by blast

lemma
  assumes "i \<notin> Step_class {halted}" 
  shows not_halted_pee_gt: "pee i > 1/k"
    and Xseq_gt0: "card (Xseq i) > 0"
    and Xseq_gt_RN: "card (Xseq i) > RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
    and not_termination_condition: "\<not> termination_condition (Xseq i) (Yseq i)"
  using assms
  by (auto simp: step_kind_defs termination_condition_def pee_def split: if_split_asm prod.split_asm)

lemma not_halted_pee_gt0:
  assumes "i \<notin> Step_class {halted}" 
  shows "pee i > 0" 
  using not_halted_pee_gt [OF assms] linorder_not_le order_less_le_trans by fastforce

lemma Yseq_gt0:
  assumes "i \<notin> Step_class {halted}"
  shows "card (Yseq i) > 0"
  using not_halted_pee_gt [OF assms]
  using card_gt_0_iff finite_Yseq pee_def by fastforce 

lemma step_odd: "i \<in> Step_class {red_step,bblue_step,dboost_step} \<Longrightarrow> odd i" 
  by (auto simp: Step_class_def stepper_kind_def split: if_split_asm prod.split_asm)

lemma step_even: "i \<in> Step_class {dreg_step} \<Longrightarrow> even i" 
  by (auto simp: Step_class_def stepper_kind_def next_state_kind_def split: if_split_asm prod.split_asm)

lemma not_halted_odd_RBS: "\<lbrakk>i \<notin> Step_class {halted}; odd i\<rbrakk> \<Longrightarrow> i \<in> Step_class {red_step,bblue_step,dboost_step}" 
  by (auto simp: Step_class_def stepper_kind_def next_state_kind_def split: prod.split_asm)

lemma not_halted_even_dreg: "\<lbrakk>i \<notin> Step_class {halted}; even i\<rbrakk> \<Longrightarrow> i \<in> Step_class {dreg_step}" 
  by (auto simp: Step_class_def stepper_kind_def next_state_kind_def split: prod.split_asm)

lemma step_before_dreg:
  assumes "Suc i \<in> Step_class {dreg_step}"
  shows "i \<in> Step_class {red_step,bblue_step,dboost_step}"
  using assms by (auto simp: step_kind_defs split: if_split_asm prod.split_asm)

lemma dreg_before_step:
  assumes "Suc i \<in> Step_class {red_step,bblue_step,dboost_step}" 
  shows "i \<in> Step_class {dreg_step}"
  using assms by (auto simp: Step_class_def stepper_kind_def split: if_split_asm prod.split_asm)

lemma 
  assumes "i \<in> Step_class {red_step,bblue_step,dboost_step}" 
  shows dreg_before_step': "i - Suc 0 \<in> Step_class {dreg_step}" 
    and dreg_before_gt0: "i>0"
proof -
  show "i>0"
    using assms gr0I step_odd by force
  then show "i - Suc 0 \<in> Step_class {dreg_step}"
    using assms dreg_before_step Suc_pred by force
qed

lemma dreg_before_step1:
  assumes "i \<in> Step_class {red_step,bblue_step,dboost_step}" 
  shows "i-1 \<in> Step_class {dreg_step}" 
  using dreg_before_step' [OF assms] by auto

lemma step_odd_minus2: 
  assumes "i \<in> Step_class {red_step,bblue_step,dboost_step}" "i>1"
  shows "i-2 \<in> Step_class {red_step,bblue_step,dboost_step}"
  by (metis Suc_1 Suc_diff_Suc assms dreg_before_step1 step_before_dreg) 

lemma Step_class_iterates:
  assumes "finite (Step_class {knd})"
  obtains n where "Step_class {knd} = {m. m<n \<and> stepper_kind m = knd}"
proof -
  have eq: "(Step_class {knd}) = (\<Union>i. {m. m<i \<and> stepper_kind m = knd})"
    by (auto simp: Step_class_def)
  then obtain n where n: "(Step_class {knd}) = (\<Union>i<n. {m. m<i \<and> stepper_kind m = knd})"
    using finite_countable_equals[OF assms] by blast
  with Step_class_def 
  have "{m. m<n \<and> stepper_kind m = knd} = (\<Union>i<n. {m. m<i \<and> stepper_kind m = knd})"
    by auto
  then show ?thesis
    by (metis n that)
qed

lemma step_non_terminating_iff:
     "i \<in> Step_class {red_step,bblue_step,dboost_step,dreg_step} 
     \<longleftrightarrow> \<not> termination_condition (Xseq i) (Yseq i)"
  by (auto simp: step_kind_defs split: if_split_asm prod.split_asm)

lemma step_terminating_iff:
  "i \<in> Step_class {halted} \<longleftrightarrow> termination_condition (Xseq i) (Yseq i)"
  by (auto simp: step_kind_defs split: if_split_asm prod.split_asm)

lemma not_many_bluish:
  assumes "i \<in> Step_class {red_step,dboost_step}"
  shows "\<not> many_bluish (Xseq i)"
  using assms
  by (simp add: step_kind_defs split: if_split_asm prod.split_asm)

lemma stepper_XYseq: "stepper i = (X,Y,A,B) \<Longrightarrow> X = Xseq i \<and> Y = Yseq i"
  using Xseq_def Yseq_def by fastforce

lemma cvx_works:
  assumes "i \<in> Step_class {red_step,dboost_step}"
  shows "central_vertex (Xseq i) (cvx i)
       \<and> weight (Xseq i) (Yseq i) (cvx i) = max_central_vx (Xseq i) (Yseq i)"
proof -
  have "\<not> termination_condition (Xseq i) (Yseq i)"
    using Step_class_def assms step_non_terminating_iff by fastforce
  then show ?thesis
    using assms not_many_bluish[OF assms] 
    apply (simp add: Step_class_def Xseq_def cvx_def Yseq_def split: prod.split prod.split_asm)
    by (metis V_state_stepper choose_central_vx_works finX)
qed

lemma cvx_in_Xseq:
  assumes "i \<in> Step_class {red_step,dboost_step}"
  shows "cvx i \<in> Xseq i"
  using assms cvx_works[OF assms] 
  by (simp add: Xseq_def central_vertex_def cvx_def split: prod.split_asm)

lemma card_Xseq_pos:
  assumes "i \<in> Step_class {red_step,dboost_step}"
  shows "card (Xseq i) > 0"
  by (metis assms card_0_eq cvx_in_Xseq empty_iff finite_Xseq gr0I)

lemma beta_le:
  assumes "i \<in> Step_class {red_step,dboost_step}"
  shows "beta i \<le> \<mu>"
  using assms cvx_works[OF assms] \<mu>01
  by (simp add: beta_def central_vertex_def Xseq_def divide_simps split: prod.split_asm)

subsection \<open>Termination proof\<close>

text \<open>Each step decreases the size of @{term X}\<close>

lemma ex_nonempty_blue_book:
  assumes mb: "many_bluish X"
    shows "\<exists>x\<in>X. good_blue_book X ({x}, Neighbours Blue x \<inter> X)"
proof -
  have "RN k (nat \<lceil>real l powr (2 / 3)\<rceil>) > 0"
    by (metis kn0 ln0 RN_eq_0_iff gr0I of_nat_ceiling of_nat_eq_0_iff powr_nonneg_iff)
  then obtain x where "x\<in>X" and x: "bluish X x"
    using mb unfolding many_bluish_def
    by (smt (verit) card_eq_0_iff empty_iff equalityI less_le_not_le mem_Collect_eq subset_iff)
  have "book {x} (Neighbours Blue x \<inter> X) Blue"
    by (force simp: book_def all_edges_betw_un_def in_Neighbours_iff)
  with x show ?thesis
    by (auto simp: bluish_def good_blue_book_def \<open>x \<in> X\<close>)
qed

lemma choose_blue_book_psubset: 
  assumes "many_bluish X" and ST: "choose_blue_book (X,Y,A,B) = (S,T)"
    and "finite X"
    shows "T \<noteq> X"
proof -
  obtain x where "x\<in>X" and x: "good_blue_book X ({x}, Neighbours Blue x \<inter> X)"
    using ex_nonempty_blue_book assms by blast
  with \<open>finite X\<close> have "best_blue_book_card X \<noteq> 0"
    unfolding valid_state_def
    by (metis best_blue_book_is_best card.empty card_seteq empty_not_insert finite.intros singleton_insert_inj_eq)
  then have "S \<noteq> {}"
    by (metis \<open>finite X\<close> ST choose_blue_book_works card.empty)
  with \<open>finite X\<close> ST show ?thesis
    by (metis (no_types, opaque_lifting) choose_blue_book_subset disjnt_iff empty_subsetI equalityI subset_eq)
qed

lemma next_state_smaller:
  assumes "next_state (X,Y,A,B) = (X',Y',A',B')" 
    and "finite X" and nont: "\<not> termination_condition X Y"  
  shows "X' \<subset> X"
proof -
  have "X' \<subseteq> X"
    using assms next_state_subset by auto
  moreover have "X' \<noteq> X"
  proof -
    have *: "\<not> X \<subseteq> Neighbours rb x \<inter> X" if "x \<in> X" "rb \<subseteq> E" for x rb
      using that by (auto simp: Neighbours_def subset_iff)
    show ?thesis
    proof (cases "many_bluish X")
      case True
      with assms show ?thesis 
        by (auto simp: next_state_def split: if_split_asm prod.split_asm
            dest!:  choose_blue_book_psubset [OF True])
    next
      case False
      then have "choose_central_vx (X,Y,A,B) \<in> X"
        by (simp add: \<open>finite X\<close> choose_central_vx_X nont)
      with assms *[of _ Red] *[of _ Blue] \<open>X' \<subseteq> X\<close> Red_E Blue_E False
      choose_central_vx_X [OF False nont]
      show ?thesis
        by (fastforce simp: next_state_def Let_def split: if_split_asm prod.split_asm)
    qed
  qed
  ultimately show ?thesis
    by auto
qed

lemma do_next_state:
  assumes "odd i" "\<not> termination_condition (Xseq i) (Yseq i)"
  obtains A B A' B' where "next_state (Xseq i, Yseq i, A, B) 
                        = (Xseq (Suc i), Yseq (Suc i), A',B')"
  using assms
  by (force simp: Xseq_def Yseq_def split: if_split_asm prod.split_asm prod.split)

lemma step_bound: 
  assumes i: "Suc (2*i) \<in> Step_class {red_step,bblue_step,dboost_step}"
  shows "card (Xseq (Suc (2*i))) + i \<le> card X0"
  using i
proof (induction i)
  case 0
  then show ?case
    by (metis Xseq_0 Xseq_Suc_subset add_0_right mult_0_right card_mono finite_X0)
next
  case (Suc i)
  then have nt: "\<not> termination_condition (Xseq (Suc (2*i))) (Yseq (Suc (2*i)))"  
    unfolding step_non_terminating_iff [symmetric]
    by (metis Step_class_insert Suc_1 Un_iff dreg_before_step mult_Suc_right plus_1_eq_Suc plus_nat.simps(2) step_before_dreg)
  obtain A B A' B' where 2:
    "next_state (Xseq (Suc (2*i)), Yseq (Suc (2*i)), A, B) = (Xseq (Suc (Suc (2*i))), Yseq (Suc (Suc (2*i))), A',B')"
    by (meson "nt" Suc_double_not_eq_double do_next_state evenE)
  have "Xseq (Suc (Suc (2*i))) \<subset> Xseq (Suc (2*i))"
    by (meson "2" finite_Xseq assms next_state_smaller nt)
  then have "card (Xseq (Suc (Suc (Suc (2*i))))) < card (Xseq (Suc (2*i)))"
    by (smt (verit, best) Xseq_Suc_subset card_seteq order.trans finite_Xseq leD not_le)
  moreover have "card (Xseq (Suc (2*i))) + i \<le> card X0"
    using Suc dreg_before_step step_before_dreg by force
  ultimately show ?case by auto
qed

lemma Step_class_halted_nonempty: "Step_class {halted} \<noteq> {}"
proof -
  define i where "i \<equiv> Suc (2 * Suc (card X0))" 
  have "odd i"
    by (auto simp: i_def)
  then have "i \<notin> Step_class {dreg_step}"
    using step_even by blast
  moreover have "i \<notin> Step_class {red_step,bblue_step,dboost_step}"
    unfolding i_def using step_bound le_add2 not_less_eq_eq by blast
  ultimately show ?thesis
    using \<open>odd i\<close> not_halted_odd_RBS by blast
qed

definition "halted_point \<equiv> Inf (Step_class {halted})"

lemma halted_point_halted: "halted_point \<in> Step_class {halted}"
  using Step_class_halted_nonempty  Inf_nat_def1 
  by (auto simp: halted_point_def)

lemma halted_point_minimal:
  shows "i \<notin> Step_class {halted} \<longleftrightarrow> i < halted_point"
  using Step_class_halted_nonempty  
  by (metis wellorder_Inf_le1 Inf_nat_def1 Step_class_not_halted halted_point_def less_le_not_le nle_le) 

lemma halted_point_minimal': "stepper_kind i \<noteq> halted \<longleftrightarrow> i < halted_point"
  by (simp add: Step_class_def flip: halted_point_minimal)

lemma halted_eq_Compl:
  "Step_class {dreg_step,red_step,bblue_step,dboost_step} = - Step_class {halted}"
  using Step_class_UNIV [of] by (auto simp: Step_class_def)

lemma before_halted_eq:
  shows "{..<halted_point} = Step_class {dreg_step,red_step,bblue_step,dboost_step}"
  using halted_point_minimal by (force simp: halted_eq_Compl)

lemma finite_components:
  shows "finite (Step_class {dreg_step,red_step,bblue_step,dboost_step})"
  by (metis before_halted_eq finite_lessThan)

lemma
  shows dreg_step_finite  [simp]: "finite (Step_class {dreg_step})"
    and red_step_finite   [simp]: "finite (Step_class {red_step})"
    and bblue_step_finite [simp]: "finite (Step_class {bblue_step})"
    and dboost_step_finite[simp]: "finite (Step_class {dboost_step})"
  using finite_components by (auto simp: Step_class_insert_NO_MATCH)

lemma halted_stepper_add_eq: "stepper (halted_point + i) = stepper (halted_point)"
proof (induction i)
  case 0
  then show ?case
    by auto
next
  case (Suc i)
  have hlt: "stepper_kind (halted_point) = halted"
    using Step_class_def halted_point_halted by force
  obtain X Y A B where *: "stepper (halted_point) = (X, Y, A, B)"
    by (metis surj_pair)
  with hlt have "termination_condition X Y"
    by (simp add: stepper_kind_def next_state_kind_def split: if_split_asm)
  with * show ?case
    by (simp add: Suc)
qed

lemma halted_stepper_eq:
  assumes i: "i \<ge> halted_point"
  shows "stepper i = stepper (halted_point)"
  using \<mu>01 by (metis assms halted_stepper_add_eq le_iff_add)

lemma below_halted_point_cardX:
  assumes "i < halted_point"
  shows  "card (Xseq i) > 0"
  using Xseq_gt0 assms halted_point_minimal halted_stepper_eq \<mu>01 
  by blast

end

sublocale Book' \<subseteq> Book where \<mu>=\<gamma>
proof
  show "0 < \<gamma>" "\<gamma> < 1"
    using ln0 kn0 by (auto simp: \<gamma>_def)
qed (use XY0 density_ge_p0_min in auto)

lemma (in Book) Book':
  assumes "\<gamma> = real l / (real k + real l)"
  shows "Book' V E p0_min Red Blue l k \<gamma> X0 Y0"
proof qed (use assms XY0 density_ge_p0_min in auto)

end
