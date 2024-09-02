section \<open>Lower bounds for Ramsey numbers\<close>

text \<open>Probabilistic proofs of lower bounds for Ramsey numbers. Variations and strengthenings of 
the classical Erdős--Szekeres upper bound, which is proved in the original Ramsey theory
 Also a number of simple properties of Ramsey numbers, including the equivalence of the clique/anticlique 
 and edge colouring definitions.\<close>


theory Ramsey_Bounds 
  imports 
    "HOL-Library.Ramsey" 
    "HOL-Library.Infinite_Typeclass" 
    "HOL-Probability.Probability"
    "Undirected_Graph_Theory.Undirected_Graph_Basics" 
begin

subsection \<open>Preliminaries\<close>

text \<open>Elementary facts involving binomial coefficients\<close>

lemma choose_two_real: "of_nat (n choose 2) = real n * (real n - 1) / 2"
proof (cases "even n")
  case True
  then show ?thesis
    by (auto simp: choose_two dvd_def)
next
  case False
  then have "even (n-1)"
    by simp
  then show ?thesis
    by (auto simp: choose_two dvd_def)
qed

lemma add_choose_le_power: "(n + k) choose n \<le> Suc k ^ n"
proof -
  have *: "(\<Prod>i<n. of_nat (n+k - i) / of_nat (n - i)) \<le> (\<Prod>i<n. real (Suc k))"
  proof (intro prod_mono conjI)
    fix i
    assume i: "i \<in> {..<n}"
    then have "real (n + k - i) / real (n - i) = 1 + k/real(n-i)"
      by (auto simp: divide_simps)
    also have "\<dots> \<le> 1 + real k"
      using i by (simp add: divide_inverse inverse_le_1_iff mult_left_le)
    finally show "real (n + k - i) / real (n - i) \<le> real (Suc k)" 
      by simp
  qed auto
  then have "real((n + k) choose n) \<le> real (Suc k ^ n)"
    by (simp add: binomial_altdef_of_nat lessThan_atLeast0)
  then show ?thesis
    by linarith
qed

lemma choose_le_power: "m choose k \<le> (Suc m - k) ^ k"
  by (metis Suc_diff_le add_choose_le_power add_diff_inverse_nat binomial_eq_0_iff less_le_not_le nle_le zero_le)

lemma sum_nsets_one: "(\<Sum>U\<in>[V]\<^bsup>Suc 0\<^esup>. f U) = (\<Sum>x\<in>V. f {x})"
proof -
  have bij: "bij_betw (\<lambda>x. {x}) V ([V]\<^bsup>Suc 0\<^esup>)"
    by (auto simp: inj_on_def bij_betw_def nsets_one)
  show ?thesis
    using sum.reindex_bij_betw [OF bij] by (metis (no_types, lifting) sum.cong)
qed

subsection \<open>Relating cliques to graphs; Ramsey numbers\<close>

text \<open>When talking about Ramsey numbers, sometimes cliques are best, sometimes colour maps\<close>

lemma nsets2_eq_all_edges: "[A]\<^bsup>2\<^esup> = all_edges A"
  using card_2_iff' unfolding nsets_def all_edges_def
  by fastforce

lemma indep_eq_clique_compl: "indep R E = clique R (all_edges R - E)"
  by (auto simp: indep_def clique_def all_edges_def)

lemma all_edges_subset_iff_clique: "all_edges K \<subseteq> E \<longleftrightarrow> clique K E"
  by (fastforce simp: card_2_iff clique_def all_edges_def)

definition "clique_indep \<equiv> \<lambda>m n K E. card K = m \<and> clique K E \<or> card K = n \<and> indep K E"

lemma clique_all_edges_iff: "clique K (E \<inter> all_edges K) \<longleftrightarrow> clique K E"
  by (simp add: clique_def all_edges_def)

lemma indep_all_edges_iff: "indep K (E \<inter> all_edges K) \<longleftrightarrow> indep K E"
  by (simp add: indep_def all_edges_def)

lemma clique_indep_all_edges_iff: "clique_indep s t K (E \<inter> all_edges K) = clique_indep s t K E"
  by (simp add: clique_all_edges_iff clique_indep_def indep_all_edges_iff)

text \<open>identifying Ramsey numbers (possibly not the minimum) for a given type and pair of integers\<close>
definition is_clique_RN where
  "is_clique_RN \<equiv> \<lambda>U::'a itself. \<lambda>m n r. 
       (\<forall>V::'a set. \<forall>E. finite V \<longrightarrow> card V \<ge> r \<longrightarrow> (\<exists>K\<subseteq>V. clique_indep m n K E))"

text \<open>could be generalised to allow e.g. any hereditarily finite set\<close>
abbreviation is_Ramsey_number :: "[nat,nat,nat] \<Rightarrow> bool" where 
  "is_Ramsey_number m n r \<equiv> partn_lst {..<r} [m,n] 2"

lemma is_clique_RN_imp_partn_lst:  
  fixes U :: "'a itself"
  assumes r: "is_clique_RN U m n r" and inf: "infinite (UNIV::'a set)"
  shows "partn_lst {..<r} [m,n] 2"
  unfolding partn_lst_def
proof (intro strip)
  fix f
  assume f: "f \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<length [m,n]}"
  obtain V::"'a set" where "finite V" and V: "card V = r"
    by (metis inf infinite_arbitrarily_large)
  then obtain \<phi> where \<phi>: "bij_betw \<phi> V {..<r}"
    using to_nat_on_finite by blast
  have \<phi>_iff: "\<phi> v = \<phi> w \<longleftrightarrow> v=w" if "v\<in>V" "w\<in>V" for v w
    by (metis \<phi> bij_betw_inv_into_left that)
  define E where "E \<equiv> {e. \<exists>x\<in>V. \<exists>y\<in>V. e = {x,y} \<and> x \<noteq> y \<and> f {\<phi> x, \<phi> y} = 0}"
  obtain K where "K\<subseteq>V" and K: "clique_indep m n K E"
    by (metis r V \<open>finite V\<close> is_clique_RN_def nle_le)
  then consider (0) "card K = m" "clique K E" | (1) "card K = n" "indep K E"
    by (meson clique_indep_def)
  then have "\<exists>i<2. monochromatic {..<r} ([m, n] ! i) 2 f i"
  proof cases
    case 0
    have "f e = 0"
      if e: "e \<subseteq> \<phi> ` K" "finite e" "card e = 2" for e :: "nat set"
    proof -
      obtain x y where "x\<in>V" "y\<in>V" "e = {\<phi> x, \<phi> y} \<and> x \<noteq> y"
        using e \<open>K\<subseteq>V\<close> \<phi> by (fastforce simp: card_2_iff)
      then show ?thesis
        using e 0 
        apply (simp add: \<phi>_iff clique_def E_def doubleton_eq_iff image_iff)
        by (metis \<phi>_iff insert_commute)
    qed
    moreover have "\<phi> ` K \<in> [{..<r}]\<^bsup>m\<^esup>"
      unfolding nsets_def
    proof (intro conjI CollectI)
      show "\<phi> ` K \<subseteq> {..<r}"
        by (metis \<open>K \<subseteq> V\<close> \<phi> bij_betw_def image_mono)
      show "finite (\<phi> ` K)"
        using \<open>\<phi> ` K \<subseteq> {..<r}\<close> finite_nat_iff_bounded by auto
      show "card (\<phi> ` K) = m"
        by (metis "0"(1) \<open>K \<subseteq> V\<close> \<phi> bij_betw_same_card bij_betw_subset)
    qed
    ultimately show ?thesis
      apply (simp add: image_subset_iff monochromatic_def)
      by (metis (mono_tags, lifting) mem_Collect_eq nsets_def nth_Cons_0 pos2)
  next
    case 1
   have "f e = Suc 0"
      if e: "e \<subseteq> \<phi> ` K" "finite e" "card e = 2" for e :: "nat set"
    proof -
      obtain x y where "x\<in>V" "y\<in>V" "e = {\<phi> x, \<phi> y} \<and> x \<noteq> y"
        using e \<open>K\<subseteq>V\<close> \<phi> by (fastforce simp: card_2_iff)
      then show ?thesis
        using e 1 f bij_betw_imp_surj_on [OF \<phi>] 
        apply (simp add: indep_def E_def card_2_iff Pi_iff doubleton_eq_iff image_iff)
        by (metis \<open>K \<subseteq> V\<close> doubleton_in_nsets_2 imageI in_mono less_2_cases_iff less_irrefl numeral_2_eq_2)
    qed
    then have "f ` [\<phi> ` K]\<^bsup>2\<^esup> \<subseteq> {Suc 0}"
      by (simp add: image_subset_iff nsets_def)
    moreover have "\<phi> ` K \<in> [{..<r}]\<^bsup>n\<^esup>"
      unfolding nsets_def
    proof (intro conjI CollectI)
      show "\<phi> ` K \<subseteq> {..<r}"
        by (metis \<open>K \<subseteq> V\<close> \<phi> bij_betw_def image_mono)
      show "finite (\<phi> ` K)"
        using \<open>\<phi> ` K \<subseteq> {..<r}\<close> finite_nat_iff_bounded by auto
      show "card (\<phi> ` K) = n"
        by (metis "1"(1) \<open>K \<subseteq> V\<close> \<phi> bij_betw_same_card bij_betw_subset)
    qed 
    ultimately show ?thesis
      by (metis less_2_cases_iff monochromatic_def nth_Cons_0 nth_Cons_Suc)
  qed
  then show "\<exists>i<length [m,n]. monochromatic {..<r} ([m, n] ! i) 2 f i"
    by (simp add: numeral_2_eq_2)
qed

lemma partn_lst_imp_is_clique_RN: 
  fixes U :: "'a itself"
  assumes "partn_lst {..<r} [m,n] 2"
  shows "is_clique_RN U m n r"
  unfolding is_clique_RN_def
proof (intro strip)
  fix V::"'a set" and E ::"'a set set"
  assume V: "finite V" "r \<le> card V"
  obtain \<phi> where \<phi>: "bij_betw \<phi> {..<card V} V"
    using \<open>finite V\<close> bij_betw_from_nat_into_finite by blast
  define f :: "nat set \<Rightarrow> nat" where "f \<equiv> \<lambda>e. if \<phi>`e \<in> E then 0 else 1"
  have f: "f \<in> nsets {..<r} 2 \<rightarrow> {..<2}"
    by (simp add: f_def)
  obtain i H where "i<2" and H: "H \<subseteq> {..<r}" "finite H" "card H = [m,n] ! i" 
    and mono: "f ` (nsets H 2) \<subseteq> {i}"
    using partn_lstE [OF assms f]
    by (metis (mono_tags, lifting) length_Cons list.size(3) mem_Collect_eq nsets_def numeral_2_eq_2)
  have [simp]: "\<And>v w. \<lbrakk>v \<in> H; w \<in> H\<rbrakk> \<Longrightarrow> \<phi> v = \<phi> w \<longleftrightarrow> v=w"
    using bij_betw_imp_inj_on [OF \<phi>] H
    by (meson V(2) inj_on_def inj_on_subset lessThan_subset_iff)
  define K where "K \<equiv> \<phi> ` H"
  have [simp]: "\<And>v w. \<lbrakk>v \<in> K; w \<in> K\<rbrakk> \<Longrightarrow> inv_into {..<card V} \<phi> v = inv_into {..<card V} \<phi> w \<longleftrightarrow> v=w"
    using bij_betw_inv_into_right [OF \<phi>] H V \<phi>
    by (metis K_def image_mono inv_into_injective lessThan_subset_iff subset_iff)
  have "K \<subseteq> V"
    using H \<phi> V bij_betw_imp_surj_on by (fastforce simp: K_def nsets_def)
  have [simp]: "card (\<phi> ` H) = card H"
    using H by (metis V(2) \<phi> bij_betw_same_card bij_betw_subset lessThan_subset_iff)
  consider (0) "i=0" | (1) "i=1"
    using \<open>i<2\<close> by linarith
  then have "clique_indep m n K E"
  proof cases
    case 0 
    have "{v, w} \<in> E" if "v \<in> K" and "w \<in> K" and "v \<noteq> w"  for v w
    proof -
      have *: "{inv_into {..<card V} \<phi> v, inv_into {..<card V} \<phi> w} \<in> [H]\<^bsup>2\<^esup>"
        using that bij_betw_inv_into_left [OF \<phi>] H(1) V(2)
        by (auto simp: nsets_def card_insert_if K_def)
      show ?thesis
        using 0 \<open>K \<subseteq> V\<close> mono bij_betw_inv_into_right[OF \<phi>] that
        apply (simp add: f_def image_subset_iff)
        by (metis "*" image_empty image_insert subsetD)
    qed
    then show ?thesis 
      unfolding clique_indep_def clique_def
      by (simp add: "0" H(3) K_def)
  next
    case 1
    have "{v, w} \<notin> E" if "v \<in> K" and "w \<in> K" and "v \<noteq> w"  for v w
    proof -
      have *: "{inv_into {..<card V} \<phi> v, inv_into {..<card V} \<phi> w} \<in> [H]\<^bsup>2\<^esup>"
        using that bij_betw_inv_into_left [OF \<phi>] H(1) V(2)
        by (auto simp: nsets_def card_insert_if K_def)
      show ?thesis
        using 1 \<open>K \<subseteq> V\<close> mono bij_betw_inv_into_right[OF \<phi>] that
        apply (simp add: f_def image_subset_iff)
        by (metis "*" image_empty image_insert subsetD)
    qed
    then show ?thesis 
      unfolding clique_indep_def indep_def
      by (simp add: "1" H(3) K_def)
  qed
  with \<open>K \<subseteq> V\<close> show "\<exists>K. K \<subseteq> V \<and> clique_indep m n K E" by blast
qed

text \<open>All complete graphs of a given cardinality are the same\<close>
lemma is_clique_RN_any_type:
  assumes "is_clique_RN (U::'a itself) m n r" "infinite (UNIV::'a set)" 
  shows "is_clique_RN (V::'b::infinite itself) m n r"
  by (metis partn_lst_imp_is_clique_RN is_clique_RN_imp_partn_lst assms)

lemma is_Ramsey_number_le:
  assumes "is_Ramsey_number m n r" and le: "m' \<le> m" "n' \<le> n"
  shows "is_Ramsey_number m' n' r"
  using partn_lst_less [where \<alpha> = "[m,n]" and \<alpha>' = "[m',n']"] assms
  by (force simp: less_Suc_eq)

definition RN where
  "RN \<equiv> \<lambda>m n. LEAST r. is_Ramsey_number m n r"

lemma is_Ramsey_number_RN: "partn_lst {..< (RN m n)} [m,n] 2"
  by (metis LeastI_ex RN_def ramsey2_full)

lemma RN_le: "\<lbrakk>is_Ramsey_number m n r\<rbrakk> \<Longrightarrow> RN m n \<le> r"
  by (simp add: Least_le RN_def)

lemma RN_le_ES: "RN i j \<le> ES 2 i j"
  by (simp add: RN_le ramsey2_full)

lemma RN_mono:
  assumes "m' \<le> m" "n' \<le> n"
  shows "RN m' n' \<le> RN m n"
  by (meson RN_le assms is_Ramsey_number_RN is_Ramsey_number_le)

lemma indep_iff_clique [simp]: "K \<subseteq> V \<Longrightarrow> indep K (all_edges V - E) \<longleftrightarrow> clique K E"
  by (auto simp: clique_def indep_def all_edges_def)

lemma clique_iff_indep [simp]: "K \<subseteq> V \<Longrightarrow> clique K (all_edges V - E) \<longleftrightarrow> indep K E"
  by (auto simp: clique_def indep_def all_edges_def)

lemma is_Ramsey_number_commute_aux:
  assumes "is_Ramsey_number m n r"
  shows "is_Ramsey_number n m r"
  unfolding partn_lst_def
proof (intro strip)
  fix f 
  assume f: "f \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<length [n, m]}"
  define f' where "f' \<equiv> \<lambda>A. 1 - f A"
  then have "f' \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
    by (auto simp: f'_def)
  then obtain i H where "i<2" and H: "H \<in> [{..<r}]\<^bsup>([m,n] ! i)\<^esup>" "f' ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
    using assms by (auto simp: partn_lst_def monochromatic_def numeral_2_eq_2)
  then have "H \<subseteq> {..<r}"
    by (auto simp: nsets_def)
  then have fless2: "\<forall>x\<in>[H]\<^bsup>2\<^esup>. f x < Suc (Suc 0)"
    using funcset_mem [OF f] nsets_mono by force
  show "\<exists>i<length [n, m]. monochromatic {..<r} ([n,m] ! i) 2 f i"
    unfolding monochromatic_def
  proof (intro exI bexI conjI)
    show "f ` [H]\<^bsup>2\<^esup> \<subseteq> {1-i}"
      using H fless2 by (fastforce simp: f'_def)
    show "H \<in> [{..<r}]\<^bsup>([n, m] ! (1-i))\<^esup>"
      using \<open>i<2\<close> H by (fastforce simp: less_2_cases_iff f'_def image_subset_iff)
  qed auto
qed

subsection \<open>Elementary properties of Ramsey numbers\<close>

lemma is_Ramsey_number_commute: "is_Ramsey_number m n r \<longleftrightarrow> is_Ramsey_number n m r"
  by (meson is_Ramsey_number_commute_aux)

lemma RN_commute_aux: "RN n m \<le> RN m n"
  using RN_le is_Ramsey_number_RN is_Ramsey_number_commute by blast

lemma RN_commute: "RN m n = RN n m"
  by (simp add: RN_commute_aux le_antisym)

lemma RN_le_choose: "RN k l \<le> (k+l choose k)"
  by (metis ES2_choose ramsey2_full RN_le)

lemma RN_le_choose': "RN k l \<le> (k+l choose l)"
  by (metis RN_commute RN_le_choose add.commute)


lemma RN_0 [simp]: "RN 0 m = 0"
  unfolding RN_def
proof (intro Least_equality)
  show "is_Ramsey_number 0 m 0"
    by (auto simp: partn_lst_def monochromatic_def nsets_def)
qed auto

lemma RN_1 [simp]: 
  assumes "m>0" shows "RN (Suc 0) m = Suc 0"
  unfolding RN_def
proof (intro Least_equality)
  have [simp]: "[{..<Suc 0}]\<^bsup>2\<^esup> = {}" "[{}]\<^bsup>2\<^esup> = {}"
    by (auto simp: nsets_def card_2_iff)
  show "is_Ramsey_number (Suc 0) m (Suc 0)"
    by (auto simp: partn_lst_def monochromatic_def)
  fix i
  assume i: "is_Ramsey_number (Suc 0) m i"
  show "i \<ge> Suc 0"
  proof (cases "i=0")
    case True
    with i assms show ?thesis
      by (auto simp: partn_lst_def monochromatic_def nsets_empty_iff less_Suc_eq)
  qed auto
qed

lemma RN_0' [simp]: "RN m 0 = 0" and RN_1' [simp]: "m>0 \<Longrightarrow> RN m (Suc 0) = Suc 0"
  using RN_1 RN_commute by auto

lemma is_clique_RN_2: "is_clique_RN TYPE(nat) 2 m m"
  unfolding is_clique_RN_def
proof (intro strip)
  fix V :: "'a set" and E
  assume "finite V"
    and "m \<le> card V"
  show "\<exists>K. K \<subseteq> V \<and> clique_indep 2 m K E"
  proof (cases "\<exists>K. K \<subseteq> V \<and> card K = 2 \<and> clique K E")
    case False
    then have "indep V E"
      apply (clarsimp simp: clique_def indep_def card_2_iff)
      by (smt (verit, best) doubleton_eq_iff insert_absorb insert_iff subset_iff)
    then show ?thesis
      unfolding clique_indep_def
      by (meson \<open>m \<le> card V\<close> card_Ex_subset smaller_indep)
  qed (metis clique_indep_def)
qed

lemma RN_2 [simp]: 
  shows "RN 2 m = m"
proof (cases  "m>1")
  case True
  show ?thesis 
    unfolding RN_def
  proof (intro Least_equality)
    show "is_Ramsey_number 2 m m"
      using is_clique_RN_imp_partn_lst is_clique_RN_2 by blast
    fix i
    assume "is_Ramsey_number 2 m i"
    then have i: "is_clique_RN TYPE(nat) 2 m i"
      using partn_lst_imp_is_clique_RN by blast
    obtain V :: "nat set" where V: "card V = i" "finite V"
      by force
    show "i \<ge> m"
    proof (cases "i<m")
      case True
      then have "\<not> (\<exists>K\<subseteq>V. card K = 2 \<and> clique K {})"
        by (auto simp: clique_def card_2_iff')
      with i V True show ?thesis
        unfolding is_clique_RN_def clique_indep_def by (metis card_mono dual_order.refl)
    qed auto
  qed
next
  case False
  then show ?thesis
    by (metis RN_0' RN_1' Suc_1 less_2_cases_iff not_less_eq)
qed

lemma RN_2' [simp]: 
  shows "RN m 2 = m"
  using RN_2 RN_commute by force

lemma RN_3plus: 
  assumes "k \<ge> 3"
  shows "RN k m \<ge> m"
proof -
  have "RN 2 m = m"
    using assms by auto
  with RN_mono[of 2 k m m] assms show ?thesis
    by force
qed

lemma RN_3plus': 
  assumes "k \<ge> 3"
  shows "RN m k \<ge> m"
  using RN_3plus RN_commute assms by presburger

lemma clique_iff: "F \<subseteq> all_edges K \<Longrightarrow> clique K F \<longleftrightarrow> F = all_edges K"
  by (auto simp: clique_def all_edges_def card_2_iff)

lemma indep_iff: "F \<subseteq> all_edges K \<Longrightarrow> indep K F \<longleftrightarrow> F = {}"
  by (auto simp: indep_def all_edges_def card_2_iff)

lemma all_edges_empty_iff: "all_edges K = {} \<longleftrightarrow> (\<exists>v. K \<subseteq> {v})"
  using clique_iff [OF empty_subsetI] by (metis clique_def empty_iff singleton_iff subset_iff)

lemma Ramsey_number_zero: "\<not> is_Ramsey_number (Suc m) (Suc n) 0"
  by (metis RN_1 RN_le is_Ramsey_number_le not_one_le_zero Suc_le_eq One_nat_def zero_less_Suc)

subsection \<open>The product lower bound\<close>

lemma Ramsey_number_times_lower: "\<not> is_clique_RN (TYPE(nat*nat)) (Suc m) (Suc n) (m*n)"
proof
  define edges where "edges \<equiv> {{(x,y),(x',y)}| x x' y. x<m \<and> x'<m \<and> y<n}"
  assume "is_clique_RN (TYPE(nat*nat)) (Suc m) (Suc n) (m*n)"
  then obtain K where K: "K \<subseteq> {..<m} \<times> {..<n}" and "clique_indep (Suc m) (Suc n) K edges"
    unfolding is_clique_RN_def
    by (metis card_cartesian_product card_lessThan finite_cartesian_product finite_lessThan le_refl)
  then consider "card K = Suc m \<and> clique K edges" | "card K = Suc n \<and> indep K edges"
    by (meson clique_indep_def)
  then show False
  proof cases
    case 1
    then have "inj_on fst K" "fst ` K \<subseteq> {..<m}"
      using K by (auto simp: inj_on_def clique_def edges_def doubleton_eq_iff)
    then have "card K \<le> m"
      by (metis card_image card_lessThan card_mono finite_lessThan)
    then show False
      by (simp add: "1")
  next
    case 2
    then have snd_eq: "snd u \<noteq> snd v" if "u \<in> K" "v \<in> K" "u \<noteq> v" for u v
      using that K unfolding edges_def indep_def
      by (smt (verit, best) lessThan_iff mem_Collect_eq mem_Sigma_iff prod.exhaust_sel subsetD)
    then have "inj_on snd K"
      by (meson inj_onI)
    moreover have "snd ` K \<subseteq> {..<n}"
      using comp_sgraph.wellformed K by auto
    ultimately show False
      by (metis "2" Suc_n_not_le_n card_inj_on_le card_lessThan finite_lessThan)
  qed
qed

theorem RN_times_lower:
  shows "RN (Suc m) (Suc n) > m*n"                              
  by (metis partn_lst_imp_is_clique_RN Ramsey_number_times_lower is_Ramsey_number_RN 
            partn_lst_greater_resource linorder_le_less_linear)

corollary RN_times_lower':
  shows "\<lbrakk>m>0; n>0\<rbrakk> \<Longrightarrow> RN m n > (m-1)*(n-1)"
  using RN_times_lower gr0_conv_Suc by force                              

lemma RN_eq_0_iff: "RN m n = 0 \<longleftrightarrow> m=0 \<or> n=0"
  by (metis RN_0 RN_0' RN_times_lower' gr0I not_less_zero)

lemma RN_gt1:
  assumes "2 \<le> k" "3 \<le> l" shows "k < RN k l"
  using RN_times_lower' [of k l] RN_3plus'[of l k] assms  
  apply (simp add: eval_nat_numeral)
  by (metis Suc_le_eq Suc_pred leD n_less_n_mult_m nat_less_le zero_less_diff)

lemma RN_gt2:
  assumes "2 \<le> k" "3 \<le> l" shows "k < RN l k"
  by (simp add: RN_commute assms RN_gt1)

subsection \<open>A variety of upper bounds, including a stronger Erdős--Szekeres\<close>

lemma RN_1_le: "RN (Suc 0) l \<le> Suc 0"
  by (metis RN_0' RN_1 gr_zeroI le_cases less_imp_le)

lemma is_Ramsey_number_add:
  assumes "i>1" "j>1" 
    and n1: "is_Ramsey_number (i - 1) j n1"
    and n2: "is_Ramsey_number i (j - 1) n2"
  shows "is_Ramsey_number i j (n1+n2)"
proof -
  have "partn_lst {..<Suc (n1 + n2 - 1)} [i, j] (Suc (Suc 0))"
    using ramsey_induction_step [of n1 i j 1 n2 "n1+n2-1"] ramsey1_explicit assms
    by (simp add: numeral_2_eq_2)
  moreover have "n1>0"
    using assms
    by (metis Ramsey_number_zero Suc_pred' gr0I not_less_iff_gr_or_eq zero_less_diff)
  ultimately show ?thesis
    by (metis One_nat_def Suc_1 Suc_pred' add_gr_0)
qed

lemma RN_le_add_RN_RN:
  assumes "i>1" "j>1" 
  shows "RN i j \<le> RN (i - Suc 0) j + RN i (j - Suc 0)"
  using is_Ramsey_number_add RN_le assms is_Ramsey_number_RN
  by simp


text \<open>Cribbed from Bhavik Mehta\<close>
lemma RN_le_choose_strong: "RN k l \<le> (k + l - 2) choose (k - 1)"
proof (induction n \<equiv> "k+l" arbitrary: k l)
  case 0
  then show ?case
    by simp    
next
  case (Suc n)
  have *: "RN k l \<le> k + l - 2 choose (k - 1)" if "k \<le> Suc 0"
    using that by (metis One_nat_def RN_1_le RN_le_choose Suc_pred binomial_n_0 neq0_conv diff_is_0_eq')
  show ?case 
  proof (cases "k \<le> Suc 0 \<or> l \<le> Suc 0")
    case True
    with * show ?thesis
      using le_Suc_eq by fastforce
  next
    case False
    then have 2: "k > 1" "l > 1"
      by auto
    have "RN (k - Suc 0) l \<le> k - Suc 0 + l - 2 choose (k - Suc 0 - Suc 0)"
      by (metis False Nat.add_diff_assoc2 One_nat_def Suc diff_Suc_1 nat_le_linear)
    moreover
    have "RN k (l - Suc 0) \<le> k - Suc 0 + l - 2 choose (k - Suc 0)"
      by (metis False Nat.diff_add_assoc2 Suc diff_Suc_1 nat_le_linear One_nat_def diff_add_assoc)
    ultimately 
    show ?thesis
      using RN_le_add_RN_RN [OF 2] 2 by (simp add: choose_reduce_nat eval_nat_numeral)
  qed
qed

lemma RN_le_power2: "RN i j \<le> 2 ^ (i+j-2)"
  by (meson RN_le_choose_strong binomial_le_pow2 le_trans)

lemma RN_le_power4: "RN i i \<le> 4 ^ (i-1)"
proof -
  have "(i + i - 2) = 2 * (i-1)"
    by simp
  then show ?thesis
    using RN_le_power2 [of i i] by (simp add: power_mult)
qed

text \<open>Bhavik Mehta again\<close>
lemma RN_le_argpower: "RN i j \<le> j ^ (i-1)"
proof (cases "i=0 \<or> j=0")
  case True
  then show ?thesis
    by auto
next
  case False
  then show ?thesis
    using RN_le_choose_strong [of i j] add_choose_le_power[of "i-1" "j-1"]
    by (simp add: numeral_2_eq_2)
qed

lemma RN_le_argpower': "RN j i \<le> j ^ (i-1)"
  using RN_commute RN_le_argpower by presburger

subsection \<open>Probabilistic lower bounds: the main  theorem and applications\<close>

text \<open>General probabilistic setup, omitting the actual probability calculation.
  Andrew Thomason's proof (private communication)\<close> 
theorem Ramsey_number_lower_gen:  
  fixes n k::nat and p::real
  assumes n: "(n choose k) * p ^ (k choose 2) + (n choose l) * (1 - p) ^ (l choose 2) < 1"
  assumes p01: "0<p" "p<1"
  shows "\<not> is_Ramsey_number k l n"
proof
  assume con: "is_Ramsey_number k l n"
  define W where "W \<equiv> {..<n}"      
  have "finite W" and cardW: "card W = n"
    by (auto simp: W_def)
  \<comment> \<open>Easier to represent the state as maps from edges to colours, not sets of coloured edges\<close>
   \<comment>\<open>colour the edges randomly\<close>
  define \<Omega> :: "(nat set \<Rightarrow> nat) set" where "\<Omega> \<equiv> (all_edges W) \<rightarrow>\<^sub>E {..<2}"
  have card\<Omega>: "card \<Omega> = 2 ^ (n choose 2)"
    by (simp add: \<Omega>_def \<open>finite W\<close> W_def card_all_edges card_funcsetE finite_all_edges)
  define coloured where "coloured \<equiv> \<lambda>F. \<lambda>f::nat set \<Rightarrow> nat. \<lambda>c. {e \<in> F. f e = c}"
  have finite_coloured[simp]: "finite (coloured F f c)" if "finite F" for f c F
    using coloured_def that by auto
  define pr where "pr \<equiv> \<lambda>F f. p ^ card (coloured F f 0) * (1-p) ^ card (coloured F f 1)"
  have pr01: "0 < pr U f" "pr U f \<le> 1" for U f \<comment> \<open>the inequality could be strict\<close>
    using \<open>0<p\<close> \<open>p<1\<close> by (auto simp: mult_le_one power_le_one pr_def card\<Omega>)
  define M where "M \<equiv> point_measure \<Omega> (pr (all_edges W))"
  have space_eq: "space M = \<Omega>"
    by (simp add: M_def space_point_measure)
  have sets_eq: "sets M = Pow \<Omega>"
    by (simp add: M_def sets_point_measure)
  have fin_\<Omega>[simp]: "finite \<Omega>"
    by (simp add: \<Omega>_def finite_PiE \<open>finite W\<close> finite_all_edges)
  have coloured_insert: 
    "coloured (insert e F) f c = (if f e = c then insert e (coloured F f c) else coloured F f c)"  
    for f e c F
    by (auto simp: coloured_def)
  have eq2: "{..<2} = {0, Suc 0}"
    by (simp add: insert_commute lessThan_Suc numeral_2_eq_2)
  have sum_pr_1 [simp]: "sum (pr U) (U \<rightarrow>\<^sub>E {..<2}) = 1" if "finite U" for U
    using that
  proof (induction U)
    case empty
    then show ?case
      by (simp add: pr_def coloured_def)
  next
    case (insert e F)
    then have [simp]: "e \<notin> coloured F f c" "coloured F (f(e := c)) c' = coloured F f c'" for f c c'
      by (auto simp: coloured_def)
    have inj: "inj_on (\<lambda>(y, g). g(e := y)) ({..<2} \<times> (F \<rightarrow>\<^sub>E {..<2}))"
      using \<open>e \<notin> F\<close> by (fastforce simp: inj_on_def fun_eq_iff)
    show ?case
      using insert
      apply (simp add: pr_def coloured_insert PiE_insert_eq sum.reindex [OF inj] sum.cartesian_product')
      apply (simp add: eq2 mult_ac flip: sum_distrib_left)
      done
  qed

  interpret P: prob_space M
  proof
    have "sum (pr (all_edges W)) \<Omega> = 1"
      using \<Omega>_def sum_pr_1 \<open>finite W\<close> finite_all_edges by blast
    with pr01 show "emeasure M (space M) = 1" 
      unfolding M_def
      by (metis fin_\<Omega> prob_space.emeasure_space_1 prob_space_point_measure zero_le
       ennreal_1 linorder_not_less nle_le sum_ennreal)
  qed
  \<comment>\<open>the event to avoid: monochromatic cliques, given @{term "K \<subseteq> W"};
      we are considering edges over the entire graph @{term W}\<close>
  define mono where "mono \<equiv> \<lambda>c K. {f \<in> \<Omega>. all_edges K \<subseteq> coloured (all_edges W) f c}"
  have mono_ev: "mono c K \<in> P.events" if "c<2" for K c
    by (auto simp: sets_eq mono_def \<Omega>_def)
  have mono_sub_\<Omega>: "mono c K \<subseteq> \<Omega>" if "c<2" for K c
    using mono_ev sets_eq that by auto

  have emeasure_eq: "emeasure M C = (if C \<subseteq> \<Omega> then (\<Sum>a\<in>C. ennreal (pr (all_edges W) a)) else 0)" for C
    by (simp add: M_def emeasure_notin_sets emeasure_point_measure_finite sets_point_measure)
  define pc where "pc \<equiv> \<lambda>c::nat. if c=0 then p else 1-p"
  have pc0: "0 \<le> pc c" for c
    using p01 pc_def by auto
  have coloured_upd: "coloured F (\<lambda>l\<in>F. if l \<in> G then c else f l) c' 
        = (if c=c' then G \<union> coloured (F-G) f c' else coloured (F-G) f c')" if "G \<subseteq> F" for F G f c c'
    using that by (auto simp: coloured_def)

  have prob_mono: "P.prob (mono c K) = pc c ^ (r choose 2)"  
    if "K \<in> nsets W r" "c<2" for r K c
  proof -
    let ?EWK = "all_edges W - all_edges K"
    have \<section>: "K \<subseteq> W" "finite K" "card K = r"
      using that by (auto simp: nsets_def)
    have *: "{f \<in> \<Omega>. all_edges K \<subseteq> coloured (all_edges W) f c} = 
          (\<Union>g \<in> ?EWK \<rightarrow>\<^sub>E {..<2}. {\<lambda>l \<in> all_edges W. if l \<in> all_edges K then c else g l})"
      (is "?L = ?R")
    proof
      have  "\<exists>g\<in>?EWK \<rightarrow>\<^sub>E {..<2}. f = (\<lambda>l\<in>all_edges W. if l \<in> all_edges K then c else g l)"
        if f: "f \<in> \<Omega>" and c: "all_edges K \<subseteq> coloured (all_edges W) f c" for f
        using that
        apply (intro bexI [where x="restrict f ?EWK"])
         apply (force simp: \<Omega>_def coloured_def subset_iff)+
        done
      then show "?L \<subseteq> ?R" by auto
      show "?R \<subseteq> ?L"
        using that all_edges_mono[OF \<open>K \<subseteq> W\<close>] by (auto simp: coloured_def \<Omega>_def nsets_def PiE_iff)
    qed

    have [simp]: "card (all_edges K \<union> coloured ?EWK f c)
                = (r choose 2) + card (coloured ?EWK f c)" for f c
      using \<section> \<open>finite W\<close>
      by (subst card_Un_disjoint) (auto simp: finite_all_edges coloured_def card_all_edges)
    have pr_upd: "pr (all_edges W) (\<lambda>l \<in> all_edges W. if l \<in> all_edges K then c else f l) 
        = pc c ^ (r choose 2) * pr ?EWK f" 
      if "f \<in> ?EWK \<rightarrow>\<^sub>E {..<2}" for f
      using that all_edges_mono[OF \<open>K \<subseteq> W\<close>] p01 \<open>c<2\<close> \<section>
      by (simp add: pr_def coloured_upd pc_def power_add)
    have "emeasure M (mono c K) = (\<Sum>f \<in> mono c K. ennreal (pr (all_edges W) f))"
      using that by (simp add: emeasure_eq mono_sub_\<Omega>)
    also have "\<dots> = (\<Sum>f\<in>(\<Union>g\<in>?EWK \<rightarrow>\<^sub>E {..<2}.
                            {\<lambda>e\<in>all_edges W. if e \<in> all_edges K then c else g e}). 
                      ennreal (pr (all_edges W) f))" 
      by (simp add: mono_def *)
    also have "\<dots> = (\<Sum>g\<in>?EWK \<rightarrow>\<^sub>E {..<2}. 
                        \<Sum>f\<in>{\<lambda>e\<in>all_edges W. if e \<in> all_edges K then c else g e}. 
                           ennreal (pr (all_edges W) f))"
    proof (rule sum.UNION_disjoint_family)
      show "finite (?EWK \<rightarrow>\<^sub>E {..<2::nat})"
        by (simp add: \<open>finite W\<close> finite_PiE finite_all_edges)
      show "disjoint_family_on (\<lambda>g. {\<lambda>e\<in>all_edges W. if e \<in> all_edges K then c else g e}) (?EWK \<rightarrow>\<^sub>E {..<2})"
        apply (simp add: disjoint_family_on_def fun_eq_iff)
        by (metis DiffE PiE_E)
    qed auto
    also have "\<dots> = (\<Sum>x\<in>?EWK \<rightarrow>\<^sub>E {..<2}. ennreal (pc c ^ (r choose 2) * pr ?EWK x))"
      by (simp add: pr_upd)
    also have "\<dots> = ennreal (\<Sum>f\<in>?EWK \<rightarrow>\<^sub>E {..<2}. 
                                pc c ^ (r choose 2) * pr ?EWK f)"
      using pr01 pc0 sum.cong sum_ennreal by (smt (verit) mult_nonneg_nonneg zero_le_power)
    also have "\<dots> = ennreal (pc c ^ (r choose 2))"
      by (simp add: \<open>finite W\<close> finite_all_edges flip: sum_distrib_left)
    finally have "emeasure M (mono c K) = ennreal (pc c ^ (r choose 2))" .
    then show ?thesis 
      using p01 that by (simp add: measure_eq_emeasure_eq_ennreal pc_def)
  qed
  define Reds where "Reds \<equiv> (\<Union>K \<in> nsets W k. mono 0 K)"
  define Blues where "Blues \<equiv> (\<Union>K \<in> nsets W l. mono 1 K)"
  have Uev: "\<Union> (mono c ` [W]\<^bsup>r\<^esup>) \<in> P.events" for c r
    by (simp add: local.mono_def sets_eq subset_iff)
  then have "Reds \<in> P.events" "Blues \<in> P.events"
    by (auto simp: Reds_def Blues_def)
  have prob_0: "P.prob Reds \<le> (n choose k) * (p ^ (k choose 2))" 
  proof -
    have "P.prob Reds \<le> (\<Sum>K \<in> nsets W k. P.prob (mono 0 K))"
      by (simp add: Reds_def \<open>finite W\<close> finite_imp_finite_nsets measure_UNION_le mono_ev)
    also have "\<dots> \<le> (n choose k) * (p ^ (k choose 2))"
      by (simp add: prob_mono pc_def cardW)
    finally show ?thesis .
  qed
  moreover
  have prob_1: "P.prob Blues \<le> (n choose l) * ((1-p) ^ (l choose 2))" 
  proof -
    have "P.prob Blues \<le> (\<Sum>K \<in> nsets W l. P.prob (mono 1 K))"
      by (simp add: Blues_def \<open>finite W\<close> finite_imp_finite_nsets measure_UNION_le mono_ev)
    also have "\<dots> \<le> (n choose l) * ((1-p) ^ (l choose 2))"
      by (simp add: prob_mono pc_def cardW)
    finally show ?thesis .
  qed
  ultimately have "P.prob (Reds \<union> Blues) < 1"
    using P.finite_measure_subadditive \<open>Blues \<in> P.events\<close> \<open>Reds \<in> P.events\<close> n
    by fastforce
  with P.prob_space Uev sets_eq obtain F where F: "F \<in> \<Omega> - (Reds \<union> Blues)"
    unfolding Reds_def Blues_def space_eq
    by (smt (verit, del_insts) Pow_iff Un_subset_iff equalityI Diff_iff subset_iff)
  have False if "i < 2" "H \<in> [W]\<^bsup>([k, l] ! i)\<^esup>" "F ` [H]\<^bsup>2\<^esup> \<subseteq> {i}" for i H
  proof -
    have "\<not> all_edges H \<subseteq> {e \<in> all_edges W. F e = 0}" "\<not> all_edges H \<subseteq> {e \<in> all_edges W. F e = 1}"
      using F that
      by (auto simp: less_2_cases_iff nsets2_eq_all_edges \<Omega>_def Reds_def Blues_def mono_def coloured_def image_subset_iff)
    moreover have "H \<subseteq> W"
      using that by (auto simp: nsets_def)
    ultimately show False
      using that all_edges_mono [OF \<open>H \<subseteq> W\<close>] by (auto simp: less_2_cases_iff nsets2_eq_all_edges)
  qed
  moreover have "F \<in> [{..<n}]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
    using F by (auto simp: W_def \<Omega>_def nsets2_eq_all_edges)
  ultimately show False
    using con by (force simp: W_def partn_lst_def monochromatic_def numeral_2_eq_2)
qed

text \<open>Andrew's calculation for the Ramsey lower bound. Symmetric, so works for both colours\<close>
lemma Ramsey_lower_calc:
  fixes s::nat and t::nat and p::real
  assumes "s \<ge> 3" "t \<ge> 3" "n > 4"
    and n: "real n \<le> exp ((real s - 1) * (real t - 1) / (2*(s+t)))"
  defines "p \<equiv> real s / (real s + real t)"
  shows "(n choose s) * p ^ (s choose 2) < 1/2"
proof -
  have p01: "0<p" "p<1"
    using assms by (auto simp: p_def)
  have "exp ((real s - 1) * (real t - 1) / (2*(s+t))) \<le> exp (t / (s+t)) powr ((s-1)/2)"
    using \<open>s \<ge> 3\<close> by (simp add: mult_ac divide_simps of_nat_diff exp_powr_real)
  with assms p01 have "n \<le> exp (t / (s+t)) powr ((s-1)/2)"
    by linarith
  then have "n * p powr ((s-1)/2) \<le> (exp (t / (s+t)) * p) powr ((s-1)/2)"
    using \<open>0<p\<close> by (simp add: powr_mult)
  also have "\<dots> < 1"
  proof -
    have "exp (real t / real (s+t)) * p < 1"
    proof -
      have "p = 1 - t / (s+t)"
        using assms by (simp add: p_def divide_simps)
      also have "\<dots> < exp (- real t / real (s+t))"
        using assms by (simp add: exp_minus_greater)
      finally show ?thesis
        by (simp add: exp_minus divide_simps mult.commute)
    qed
    then show ?thesis
      using powr01_less_one assms(1) p01(1) by auto
  qed
  finally have "n * p powr ((s-1)/2) < 1" .
  then have "(n * p powr ((s-1)/2)) ^ s < 1"
    using \<open>s \<ge> 3\<close> by (simp add: power_less_one_iff)
  then have B: "n^s * p ^ (s choose 2) < 1"
    using \<open>0<p\<close> \<open>4 < n\<close> \<open>s \<ge> 3\<close>
    by (simp add: choose_two_real powr_powr powr_mult of_nat_diff mult.commute flip: powr_realpow)
  have "(n choose s) * p ^ (s choose 2) \<le> n^s / fact s * p ^ (s choose 2)"
  proof (intro mult_right_mono)
    show "real (n choose s) \<le> real (n ^ s) / fact s"
      using binomial_fact_pow[of n s] of_nat_mono
      by (fastforce simp: divide_simps mult.commute)
  qed (use p01 in auto)
  also have "\<dots> < 1 / fact s"
    using B by (simp add: divide_simps)
  also have "\<dots> \<le> 1/2"
    by (smt (verit, best) One_nat_def Suc_1 Suc_leD assms fact_2 fact_mono frac_less2 numeral_3_eq_3)
  finally show ?thesis .
qed

text \<open>Andrew Thomason's specific example\<close> 
corollary Ramsey_number_lower_off_diag:  
  fixes n k::nat  
  assumes "k \<ge> 3" "l \<ge> 3" and n: "real n \<le> exp ((real k - 1) * (real l - 1) / (2*(k+l)))"
  shows "\<not> is_Ramsey_number k l n"
proof
  assume con: "is_Ramsey_number k l n"
  then have "(k - 1) * (l - 1) < n"
    using RN_times_lower' [of k l] assms by (metis RN_le numeral_3_eq_3 order_less_le_trans zero_less_Suc)
  moreover have "2*2 \<le> (k - 1) * (l - 1)"
    using assms by (intro mult_mono) auto
  ultimately have "n > 4"
    by simp
  define p where "p \<equiv> k / (k+l)"
  have p01: "0<p" "p<1"
    using assms by (auto simp: p_def)
  have "real (n choose k) * p ^ (k choose 2) < 1/2"
    using Ramsey_lower_calc \<open>4 < n\<close> assms n p_def by auto
  moreover
  have "1-p = real l / (real l + real k)"
    using \<open>k \<ge> 3\<close> by (simp add: p_def divide_simps)
  with assms have "(n choose l) * (1-p) ^ (l choose 2) < 1/2"
    by (metis Ramsey_lower_calc add.commute mult.commute \<open>4 < n\<close>) 
  ultimately show False
    using con Ramsey_number_lower_gen p01 by force
qed

theorem RN_lower_off_diag:
  assumes "s \<ge> 3" "t \<ge> 3"
  shows "RN s t > exp ((real s - 1) * (real t - 1) / (2*(s+t)))"            
  using Ramsey_number_lower_off_diag [OF assms] is_Ramsey_number_RN by force

text \<open>The original Ramsey number lower bound, by Erdős\<close>
proposition Ramsey_number_lower:  
  fixes n s::nat
  assumes "s \<ge> 3" and n: "real n \<le> 2 powr (s/2)"
  shows "\<not> is_Ramsey_number s s n"
proof 
  assume con: "is_Ramsey_number s s n"
  then have "s \<le> n"
    using RN_3plus' RN_le assms(1) le_trans by blast
  have "s > 1" using assms by arith
  have "n>0"
    using \<open>1 < s\<close> \<open>s \<le> n\<close> by linarith
  have "(n choose s) \<le> n^s / fact s"  \<comment> \<open>probability calculation\<close>
    using binomial_fact_pow[of n s]
    by (smt (verit) fact_gt_zero of_nat_fact of_nat_mono of_nat_mult pos_divide_less_eq)  
  then have "(n choose s) * (2 / 2^(s choose 2)) \<le> 2 * n^s / (fact s * 2 ^ (s * (s-1) div 2))"
    by (simp add: choose_two divide_simps)
  also have "\<dots> \<le> 2 powr (1 + s/2) / fact s" 
  proof -
    have [simp]: "real (s * (s - Suc 0) div 2) = real s * (real s - 1) / 2"
      by (subst real_of_nat_div) auto
    have "n powr s \<le> (2 powr (s/2)) powr s"
      using n by (simp add: powr_mono2)
    then have "n powr s \<le> 2 powr (s * s / 2)"
      using \<open>n>0\<close> assms by (simp add: power2_eq_square powr_powr)
    then have "2 * n powr s \<le> 2 powr ((2 + s * s) / 2)"
      by (simp add: add_divide_distrib powr_add)
    then show ?thesis
      using n \<open>n>0\<close> by (simp add: divide_simps flip: powr_realpow powr_add) argo
  qed
  also have "\<dots> < 1"
  proof -
    have "2 powr (1 + (k+3)/2) < fact (k+3)" for k
    proof (induction k)
      case 0
      have "2 powr (5/2) = sqrt (2^5)"
        by (simp add: powr_half_sqrt_powr)
      also have "\<dots> < sqrt 36"
        by (intro real_sqrt_less_mono) auto
      finally show ?case
        by (simp add: eval_nat_numeral)
    next
      case (Suc k)
      have "2 powr (1 + real (Suc k + 3) / 2) = 2 powr (1/2) * 2 powr (1 + (k+3)/2)"
        by (simp add: powr_add powr_half_sqrt_powr flip: real_sqrt_mult)
      also have "\<dots> \<le> sqrt 2 * fact (k+3)"
        using Suc.IH by (simp add: powr_half_sqrt)
      also have "\<dots> < real(k + 4) * fact (k + 3)"
        using sqrt2_less_2 by simp
      also have "\<dots> = fact (Suc (k + 3))"
        unfolding fact_Suc by simp
      finally show ?case by simp
    qed
    then have "2 powr (1 + s/2) < fact s"
      by (metis add.commute \<open>s\<ge>3\<close> le_Suc_ex)
    then show ?thesis
      by (simp add: divide_simps)
  qed
  finally have less_1: "real (n choose s) * (2 / 2 ^ (s choose 2)) < 1" .
  then have "\<not> is_Ramsey_number s s n"
    by (intro Ramsey_number_lower_gen [where p="1/2"]) (auto simp: power_one_over)
  with con show False by blast
qed

theorem RN_lower:
  assumes "k \<ge> 3"
  shows "RN k k > 2 powr (k/2)"
  using Ramsey_number_lower assms is_Ramsey_number_RN by force                              

text \<open>and trivially, off the diagonal too\<close>
corollary RN_lower_nodiag:
  assumes "k \<ge> 3" "l \<ge> k"
  shows "RN k l > 2 powr (k/2)"
  by (meson RN_lower RN_mono assms less_le_trans le_refl of_nat_mono)                       

lemma powr_half_ge:
  fixes x::real
  assumes "x\<ge>4"
  shows "x \<le> 2 powr (x/2)"
proof -
  define f where "f \<equiv> \<lambda>x::real. 2 powr (x/2) - x"
  have "f 4 \<le> f x"
  proof (intro DERIV_nonneg_imp_nondecreasing[of concl: f] exI conjI assms)
    show "(f has_real_derivative ln 2 * (2 powr (y/2 - 1)) - 1) (at y)" for y
      unfolding f_def by (rule derivative_eq_intros refl | simp add: powr_diff)+
    show "ln 2 * (2 powr (y/2 - 1)) - 1 \<ge> 0" if "4 \<le> y" for y::real
    proof -
      have "1 \<le> ln 2 * 2 powr ((4 - 2) / (2::real))"
        using ln2_ge_two_thirds by simp
      also have "\<dots> \<le> ln 2 * (2 powr (y/2 - 1))"
        using that by (intro mult_left_mono powr_mono) auto
      finally show ?thesis by simp
    qed
  qed
  moreover have "f 4 = 0" by (simp add: f_def)
  ultimately show ?thesis
    by (simp add: f_def)
qed

corollary RN_lower_self:
  assumes "k \<ge> 3"
  shows "RN k k > k"
proof (cases "k=3")
  case False
  with assms have "k\<ge>4" by linarith
  then have "k \<le> 2 powr (k/2)"
    using powr_half_ge numeral_le_real_of_nat_iff by blast
  also have "\<dots> < RN k k"
    using assms by (intro RN_lower) auto
  finally show ?thesis
    by fastforce
qed (simp add: RN_gt2)

end
