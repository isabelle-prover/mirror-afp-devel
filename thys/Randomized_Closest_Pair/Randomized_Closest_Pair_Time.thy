section \<open>Speed\<close>

text \<open>In this section, we verify that the running time of the algorithm is linear with respect
to the length of the point sequence $p_1,\ldots,p_n$.

\emph{Proof:}
It is easy to see that the first phase and construction of the grid requires time proportional to
$n$. It is also easy to see that the number of point-comparisons is a bound for the number of
operations in the second phase. It is also possible to observe that the algorithm never compares a
point pair if they are in non-adjacent cells, i.e., if their distance is at least $2 d \sqrt{2}$.

This means we need to show that the expectation of $N(2 d \sqrt{2})$ is proportional to $n$
when $d$ is chosen according to the algorithm in the first phase. Because of the observation
from the last section, i.e., $N(2 d \sqrt{2}) \leq 11^2 N(d)$, it is enough to verify that the
expectation of $N(d)$ is linear.

Let us consider all pair distances:
$d_1 := d(p_1,p_2)$, $d_2 := d(p_1,p_3)$, \ldots, $d_m := d(p_{n-1},p_n)$ where
$m= \frac{n(n-1)}{2}$.

Then we can find a permutation $\sigma : \{1,\ldots,m\} \rightarrow \{1,\ldots,m\}$, s.t., the
distances are ordered, i.e.,
$d_{\sigma(i)} \leq d_{\sigma(j)}$ if $1 \leq i \leq j \leq m$.

The key observation is that $N(d_\sigma(i)) \leq i-1$, because $N$ counts the number of point pairs
which are closer than $d_{\sigma(i)}$, which can only be those corresponding to $d_{\sigma(1)},
d_{\sigma(2)}, \ldots, d_{\sigma(i-1)}$.

On the other hand the algorithm chooses the smallest of $n$ random samples from $d_1,\ldots,d_m$.
So the problem reduces to the computation of the expectation of the smallest element from $n$
random samples from ${1,\ldots,m}$. The mean of this can be estimated to be $\frac{m+1}{n+1}$
which is in $\mathcal O(n)$. \qed\<close>

theory Randomized_Closest_Pair_Time
  imports
    Randomized_Closest_Pair_Growth
    Approximate_Model_Counting.ApproxMCAnalysis
    Distributed_Distinct_Elements.Distributed_Distinct_Elements_Balls_and_Bins
begin

lemma time_sample_distance: "map_pmf time (sample_distance ps) = return_pmf 1"
  unfolding sample_distance_def time_bind_tpmf
  by (simp add:return_tpmf_def bind_return_pmf) (simp add:map_pmf_def[symmetric] time_lift_pmf)

lemma time_first_phase:
  assumes "length ps \<ge> 2"
  shows "map_pmf time (first_phase ps) = return_pmf (2*length ps)" (is "?L = ?R")
proof -
  let ?m = "replicate_tpmf (length ps) (sample_distance ps)"

  have ps_ne: "ps \<noteq> []" using assms by auto

  have "?L = bind_pmf ?m (\<lambda>x. lift_tm (min_list_tm (val x)) \<bind> (\<lambda>y. return_pmf (time x + time y)))"
    unfolding first_phase_def time_bind_tpmf by simp
  also have "\<dots> = bind_pmf ?m (\<lambda>x. return_pmf (time x + time (min_list_tm (val x))))"
    unfolding lift_tm_def bind_return_pmf by simp
  also have "\<dots> = bind_pmf ?m (\<lambda>x. return_pmf (time x + length (val x)))"
    using ps_ne set_val_replicate_tpmf(1) by (intro bind_pmf_cong refl
        arg_cong[where f="return_pmf"] arg_cong2[where f="(+)"] time_min_list) fastforce
  also have "\<dots> = bind_pmf ?m (\<lambda>x. return_pmf (time x + length ps))"
    using set_val_replicate_tpmf(1)
    by (intro bind_pmf_cong refl arg_cong[where f="return_pmf"] arg_cong2[where f="(+)"]) auto
  also have "\<dots> = map_pmf (\<lambda>x. x + length ps) (map_pmf time ?m)"
    unfolding map_pmf_def[symmetric] map_pmf_comp by simp
  also have "\<dots> =  return_pmf (2 * length ps)"
    unfolding time_replicate_tpmf time_sample_distance by (simp add:sum_list_replicate)
  finally show ?thesis by simp
qed

lemma time_build_grid: "time (build_grid ps d) = length ps"
  unfolding build_grid_def by (simp add:time_custom_tick)

lemma time_lookup_neighborhood:
  "time (lookup_neighborhood (grid ps d) p) \<le> 39+3*(length(val(lookup_neighborhood (grid ps d) p)))"
  (is "?L \<le> ?R")
proof -
  define s where "s = [(0, 0), (0, 1), (1, - 1), (1, 0), (1::int, 1::int)]"
  define t where "t = concat (map (\<lambda>x. filter (\<lambda>y. to_grid d y = x + to_grid d p) ps) s)"
  define u where "u = time (remove1_tm p t)"

  have t_eq: "length t+length s=(\<Sum>x\<leftarrow>s. Suc (length (filter (\<lambda>y. to_grid d y=x+to_grid d p) ps)))"
    unfolding t_def by (induction s) auto

  have a:"u \<le> 1 + length t" unfolding u_def using time_remove1 by auto

  have "?L = 5+5*length s + length t + (length t + length s) + u"
    unfolding lookup_neighborhood_def s_def[symmetric] t_eq u_def
    by (simp add:time_map_tm comp_def grid_def sum_list_triv t_def)
  also have "\<dots> = 5+6*length s + 2*length t + u" by simp
  also have "\<dots> \<le> 5+6*length s + 2*length t + (1+length t)" using a by simp
  also have "\<dots> = 36 + 3*length t" unfolding s_def by simp
  also have "\<dots> \<le> 36 + 3 * (1+length (remove1 p t))"
    by (intro add_mono mult_left_mono) (auto simp:length_remove1)
  also have "\<dots> = 39 + 3*(length (val (lookup_neighborhood (grid ps d) p)))"
    unfolding lookup_neighborhood_def s_def[symmetric] t_def
    by (simp add:val_remove1 comp_def grid_def)
  finally show ?thesis by simp
qed

lemma time_calc_dists_neighborhood:
  "time (calc_dists_neighborhood (grid ps d) p) \<le>
  40 + 5 * (length (val (lookup_neighborhood (grid ps d) p)))" (is "?L \<le> ?R")
proof -
  let ?g = "grid ps d"
  have "?L = 2* (length (val (lookup_neighborhood ?g p))) + 1 + time (lookup_neighborhood ?g p)"
    unfolding calc_dists_neighborhood_def by (simp add:time_map_tm sum_list_triv)
  also have "\<dots> \<le> 2* (length (val (lookup_neighborhood ?g p))) +1 +
    (39 + 3* (length (val (lookup_neighborhood ?g p))))"
    by (intro add_mono mult_right_mono time_lookup_neighborhood) auto
  also have "\<dots> = 40 + 5 * (length (val (lookup_neighborhood ?g p)))" by simp
  finally show ?thesis by simp
qed

lemma time_second_phase:
  fixes ps :: "point list"
  assumes "d > 0" "min_dist ps \<le> d" "length ps \<ge> 2"
  shows "time (second_phase d ps) \<le> 2 + 44 * length ps + 7 * close_point_size ps (2 * sqrt 2 * d)"
    (is "?L \<le> ?R")
proof -
  define s where "s = concat (map (\<lambda>x. val (calc_dists_neighborhood (val (build_grid ps d)) x)) ps)"

  have len_s: "length s = (\<Sum>x\<leftarrow>ps. length (val (lookup_neighborhood (grid ps d) x)))"
    unfolding s_def by (simp add:calc_dists_neighborhood_def build_grid_val length_concat comp_def)
  also have "\<dots> = (\<Sum>x\<leftarrow>ps. size (mset (val (lookup_neighborhood (grid ps d) x))))"
    by simp
  also have "\<dots> \<le>
    (\<Sum>x\<leftarrow>ps. size({#y\<in># mset ps. to_grid d y-to_grid d x\<in>{(0,0),(0,1),(1,-1),(1,0),(1,1)}#}))"
    unfolding lookup_neighborhood by (intro sum_list_mono size_mset_mono) simp
  also have "\<dots> \<le> (\<Sum>x\<leftarrow>ps. size({#y\<in># mset ps. \<forall>k\<in>{1,2}. \<bar>\<lfloor>y$k/d\<rfloor>-\<lfloor>x$k/d\<rfloor>\<bar>\<le>1 #}))"
    unfolding to_grid_def by (intro sum_list_mono size_mset_mono multiset_filter_mono_2) auto
  also have "\<dots> \<le> (\<Sum>x\<leftarrow>ps. size({#y\<in># mset ps. dist y x < d * real_of_int (1 + 1) * sqrt 2#}))"
    using exhaust_2
    by (intro sum_list_mono size_mset_mono multiset_filter_mono_2 grid_dist_upperI[OF assms(1)])
      blast
  also have "\<dots> = (\<Sum>x\<leftarrow>ps. length (filter (\<lambda>y. dist x y < 2 * sqrt 2 * d) ps))"
    by (simp add:dist_commute ac_simps) (metis mset_filter size_mset)
  also have "\<dots> = close_point_size ps ((2* sqrt 2)*d)"
    unfolding close_point_size_def product_concat_map filter_concat length_concat
    by (simp add:comp_def)
  finally have len_s_bound: "length s \<le> close_point_size ps (2* sqrt 2*d)" by simp

  obtain u v where "u \<in> set ps" "v \<in> set (val (lookup_neighborhood (grid ps d) u))"
    using second_phase_aux[OF assms] that by metis
  hence "False" if "length s = 0"
    using that unfolding len_s sum_list_eq_0_iff by simp
  hence s_ne: "s \<noteq> []" by auto

  have "?L = 2 + 4*length ps + (length s + time (min_list_tm s)) +
    (\<Sum>i\<leftarrow>ps. time (calc_dists_neighborhood (val (build_grid ps d)) i))"
    unfolding second_phase_def by (simp add:time_map_tm s_def[symmetric] time_build_grid)
  also have "\<dots> \<le> 2 + 4*length ps + (length s + time (min_list_tm s)) +
    (\<Sum>i\<leftarrow>ps. 40+5* length (val (lookup_neighborhood (grid ps d) i)))"
    unfolding build_grid_val by (intro add_mono sum_list_mono time_calc_dists_neighborhood) auto
  also have "\<dots> = 2 + 44*length ps + (length s + time (min_list_tm s)) +
    (\<Sum>i\<leftarrow>ps. 5* length (val (lookup_neighborhood (grid ps d) i)))"
    by (simp add:sum_list_addf sum_list_triv)
  also have "\<dots> = 2 + 44*length ps + 7*(length s)"
    unfolding time_min_list[OF s_ne] len_s by (simp add:sum_list_const_mult)
  also have "\<dots> \<le> 2 + 44* length ps + 7 * close_point_size ps (2* sqrt 2*d)"
    by (intro add_mono mult_left_mono len_s_bound) auto
  finally show  ?thesis by simp
qed

lemma mono_close_point_size: "mono (close_point_size ps)"
  unfolding close_point_size_def by (intro monoI length_filter_P_impl_Q) auto

lemma close_point_size_bound: "close_point_size ps x \<le> length ps^2"
  unfolding close_point_size_def power2_eq_square using length_filter_le length_product by metis

lemma map_product: "map (map_prod f g) (List.product xs ys) = List.product (map f xs) (map g ys)"
  unfolding product_concat_map by (simp add:map_concat comp_def)

lemma close_point_size_bound_2:
  "close_point_size ps d \<le> length ps + 2 * card {(u,v). dist (ps!u) (ps!v)<d \<and> u<v \<and> v<length ps}"
  (is "?L \<le> ?R")
proof -
  let ?n = "length ps"
  let ?h = "\<lambda>x. dist (ps ! fst x) (ps ! snd x) < d"
  have e : "List.product ps ps = map (map_prod ((!)ps) ((!) ps)) (List.product [0..<?n] [0..<?n])"
    unfolding map_product by (simp add:map_nth)

  have "?L = length (filter (\<lambda>x. dist (ps ! fst x) (ps ! snd x) < d) (List.product[0..<?n][0..<?n]))"
    unfolding close_point_size_def e by (simp add:comp_def case_prod_beta')
  also have "\<dots> = card {x. ?h x \<and> fst x < ?n \<and> snd x < ?n}"
    by (subst distinct_length_filter) (simp_all add:distinct_product Int_def mem_Times_iff)
  also have "\<dots> = card ({x. ?h x\<and>fst x<?n\<and>snd x<?n\<and>fst x \<noteq> snd x}\<union>{x. ?h x\<and>fst x=snd x\<and>snd x<?n})"
    by (intro arg_cong[where f="card"]) auto
  also have "\<dots> \<le> card{x. ?h x\<and>fst x<?n\<and>snd x<?n\<and>fst x \<noteq> snd x}+card{x. ?h x\<and>fst x=snd x\<and>snd x<?n}"
    by (intro card_Un_le)
  also have "\<dots> \<le> card{x. ?h x\<and>fst x<?n\<and>snd x<?n\<and>fst x \<noteq> snd x}+card((\<lambda>x. (x,x))`{k. k<?n})"
    by (intro add_mono order.refl card_mono finite_imageI) auto
  also have "\<dots> \<le> card{x. ?h x\<and>fst x<?n\<and>snd x<?n\<and>fst x \<noteq> snd x}+?n"
    by (subst card_image) (auto intro:inj_onI)
  also have "\<dots> =card ({x. ?h x\<and>fst x<snd x\<and>snd x<?n}\<union>{x. ?h x\<and>snd x<fst x\<and>fst x<?n})+?n"
    by (intro arg_cong2[where f="(+)"] arg_cong[where f="card"]) auto
  also have "\<dots> \<le> (card {x. ?h x\<and>fst x<snd x\<and>snd x<?n} + card {x. ?h x\<and>snd x<fst x\<and>fst x<?n})+?n"
    by (intro add_mono card_Un_le order.refl)
  also have
    "\<dots>=(card{x. ?h x\<and>fst x<snd x\<and>snd x<?n}+card (prod.swap`{x. ?h x\<and>snd x<fst x\<and>fst x<?n}))+?n"
    by (subst card_image) auto
  also have "\<dots> = (card{x. ?h x\<and>fst x<snd x\<and>snd x<?n}+card ({x. ?h x\<and>fst x<snd x\<and>snd x<?n}))+?n"
    by (intro arg_cong2[where f="(+)"] arg_cong[where f="card"]) (auto simp:dist_commute)
  also have "\<dots> = ?R" by (simp add:case_prod_beta')
  finally show ?thesis by simp
qed

lemma card_card_estimate:
  fixes f :: "'a \<Rightarrow> ('b :: linorder)"
  assumes "finite S"
  shows "card {x \<in> S. a \<le> card {y \<in> S. f y < f x }} \<le> card S - a" (is "?L \<le> ?R")
proof -
  define T where "T = {x \<in> S. card {y \<in> S. f y < f x} < a}"

  have T_range: "T \<subseteq> S" unfolding T_def by auto
  hence fin_T: "finite T" using assms finite_subset by auto

  have d:"a \<le> card T \<or> T= S"
  proof (rule ccontr)
    define x where "x = arg_min_on f (S-T)"

    assume a:"\<not>(a \<le> card T \<or> T=S)"
    hence c:"S - T \<noteq> {}" using T_range by auto
    hence b:"x \<in> S-T" using assms unfolding x_def by (intro arg_min_if_finite) auto

    have "False" if "y \<in> S-T" "f y < f x" for y
      using arg_min_if_finite[OF _ c] that assms unfolding x_def by auto
    hence "card {y \<in> S. f y < f x} \<le> card T" by (intro card_mono fin_T) auto
    also have "\<dots> < a" using a by simp
    finally have "card {y \<in> S. f y < f x} < a" by simp
    thus "False" using b unfolding T_def by simp
  qed
  have "?L = card (S - T)" unfolding T_def by (intro arg_cong[where f="card"]) auto
  also have "\<dots> = card S - card T" using fin_T T_range by (intro card_Diff_subset) auto
  also have "\<dots> \<le> card S - a" using d by auto
  finally show ?thesis by simp
qed

lemma finite_map_pmf:
  assumes "finite (set_pmf S)"
  shows "finite (set_pmf (map_pmf f S))"
  using assms by simp

lemma finite_replicate_pmf:
  assumes "finite (set_pmf S)"
  shows "finite (set_pmf (replicate_pmf n S))"
  using assms unfolding set_replicate_pmf lists_eq_set
  by (simp add:finite_lists_length_eq)

lemma power_sum_approx: "(\<Sum>k<m. (real k)^n) \<le> m^(n+1)/real (n+1)"
proof (induction m)
  case 0 thus ?case by simp
next
  case (Suc m)
  have "(\<Sum>k<Suc m. real k ^ n) = (\<Sum>k<m. real k ^ n) + real m ^ n" by simp
  also have "... \<le> real m ^ (n+1) / real (n+1) + real m^n" by (intro add_mono Suc order.refl)
  also have "... = (real m^(n+1)+(real (m+1)-m)*real (n+1)*real m^((n+1)-1)) / real (n+1)"
    by (simp add:field_simps)
  also have "\<dots> \<le> (real m^(n+1)+(real (m+1)^(n+1)-real m^(n+1))) / real (n+1)"
    by (intro divide_right_mono add_mono order.refl power_diff_est_2) simp_all
  also have "\<dots> = real (Suc m) ^ (n + 1) / real (n + 1)" by simp
  finally show ?case by simp
qed

lemma exp_close_point_size:
  assumes "length ps \<ge> 2"
  shows "(\<integral>d. real (close_point_size ps d) \<partial>(map_pmf val (first_phase ps))) \<le> 2* real (length ps)"
    (is "?L \<le> ?R")
proof -
  let ?n = "length ps"
  define T where "T = {i. fst i<snd i\<and>snd i<?n}"
  let ?I = "{..<?n}"
  let ?dpmf = "map_pmf (\<lambda>i. dist (ps!fst i) (ps!snd i)) (pmf_of_set T)"
  let ?q = "prod_pmf {..<?n} (\<lambda>_. ?dpmf)"
  let ?h = "\<lambda>x. dist (ps ! fst x) (ps ! snd x)"
  let ?cps = "\<lambda>d. card {(u,v). dist (ps!u) (ps!v)<d \<and> u<v \<and> v<length ps}"
  let ?m = "?n * (?n - 1) div 2"

  have card_T: "card T = ?m"
  proof -
    have "2 * card T = 2 * card {(x,y) \<in> {..<?n}\<times>{..<?n}. x < y}"
      unfolding T_def by (intro arg_cong[where f="card"] arg_cong2[where f="(*)"]) auto
    also have "\<dots> = card {..<?n} * (card {..<?n}-1)" by (intro card_ordered_pairs) simp
    also have "\<dots> = ?n * (?n-1)" by simp
    finally have " 2 * card T= ?n * (?n-1)" by simp
    thus ?thesis by simp
  qed

  have "2 * 1 \<le> ?n * (?n-1)" using assms by (intro mult_mono) auto
  hence "card T > 0" unfolding card_T using assms by (intro div_2_gt_zero) simp
  hence T_fin_ne: "finite T" "T \<noteq> {}" by (auto simp: card_ge_0_finite)

  have x_neI:"x \<noteq> []" if "x \<in> set_pmf (replicate_pmf ?n ?dpmf)" for x
    using that assms by (auto simp:set_replicate_pmf)

  have a:"map_pmf val (first_phase ps) = map_pmf min_list (replicate_pmf ?n ?dpmf)"
    unfolding first_phase_def val_tpmf_simps val_replicate_tpmf val_sample_distance
      T_def[symmetric] map_pmf_def[symmetric] by (intro map_pmf_cong val_min_list x_neI) auto

  hence b: "{x. t < ?cps x} = {}" if "t \<notin> {..<?m}" for t
  proof -
    have "?cps x \<le> card T" for x
      using T_fin_ne(1) unfolding T_def by (intro card_mono) auto
    moreover have "card T \<le> t" using that unfolding card_T by (simp add:not_less)
    ultimately have "?cps x \<le> t" for x using order.trans by auto
    thus ?thesis using not_less by auto
  qed

  have d: "{y. t< ?cps (min_list (map y [0..<?n]))} = {..<?n}\<rightarrow>{y. t < ?cps y}" (is "?L2=?R2") for t
  proof (rule Set.set_eqI)
    fix x
    have "x \<in> ?L2 \<longleftrightarrow> (t < ?cps (min_list (map x [0..<?n])))" by simp
    also have "\<dots> \<longleftrightarrow> (t < ?cps (Min (x ` {0..<?n})))"
      using assms by (subst min_list_Min) auto
    also have "\<dots> \<longleftrightarrow> (t < Min (?cps ` x ` {0..<?n}))"
      using assms by (intro arg_cong2[where f="(<)"] mono_Min_commute refl finite_imageI monoI
          card_mono finite_subset[OF _ T_fin_ne(1)]) (auto simp:T_def)
    also have "\<dots> \<longleftrightarrow> (\<forall>i\<in>{0..<?n}. t < ?cps (x i))"
      using assms by (subst Min_gr_iff) auto
    also have "\<dots> \<longleftrightarrow> x \<in> ?R2" by auto
    finally show "x \<in> ?L2 \<longleftrightarrow> x \<in> ?R2" by simp
  qed

  have c: "measure (replicate_pmf ?n ?dpmf) {x. t<?cps(min_list x)}\<le>(real (?m-(t+1))/real ?m)^?n"
    (is "?L1 \<le> ?R1") for t
  proof -
    have "?L1 = measure(replicate_pmf(length [0..<?n]) ?dpmf) {x. t < ?cps (min_list x)}"
      by simp
    also have "\<dots> = measure (map_pmf (\<lambda>f. map f [0..<?n]) (prod_pmf(set[0..<?n])(\<lambda>_.?dpmf)))
      {x. t<?cps(min_list x)}"
      by (intro arg_cong2[where f="\<lambda>x. measure (measure_pmf x)"] replicate_pmf_Pi_pmf) auto
    also have "\<dots> = measure ?q {y. t < ?cps (min_list (map y [0..<?n]))}"
      by (simp add:atLeast0LessThan)
    also have "\<dots> = measure (prod_pmf {..<?n} (\<lambda>_. ?dpmf)) ({..<?n} \<rightarrow> {y. t < ?cps y})"
      unfolding d by simp
    also have "\<dots> = measure ?dpmf {y. t < ?cps y}^?n"
      by (subst measure_Pi_pmf_Pi) simp_all
    also have "\<dots> = measure ?dpmf {y. t+1 \<le> ?cps y}^?n"
      by (intro measure_pmf_cong arg_cong2[where f="(\<lambda>x y. x^y)"] refl) auto
    also have "\<dots> \<le> measure (pmf_of_set T) {y. t+1\<le> card {x \<in> T. ?h x<?h y}}^?n"
      unfolding T_def by (auto simp:case_prod_beta' conj_commute)
    also have "\<dots> = (real (card {y\<in>T. t+1\<le> card {x \<in> T. ?h x<?h y}})/real (card T))^?n"
      unfolding measure_pmf_of_set[OF T_fin_ne(2,1)] Int_def by simp
    also have "\<dots> \<le> (real (card T - (t+1))/real (card T))^?n"
      by (intro power_mono divide_right_mono of_nat_mono card_card_estimate T_fin_ne) auto
    also have "... = (real (?m - (t+1))/real ?m)^?n"
      unfolding card_T by auto
    finally show ?thesis by simp
  qed

  have "ennreal ?L = (\<integral>ds. real (close_point_size ps (min_list ds)) \<partial>replicate_pmf ?n ?dpmf)"
    unfolding a by simp
  also have "\<dots> \<le> (\<integral>ds. real (?n + 2*?cps (min_list ds)) \<partial>replicate_pmf ?n ?dpmf)" using T_fin_ne
    by (intro integral_mono_AE ennreal_leI AE_pmfI close_point_size_bound_2 of_nat_mono
          integrable_measure_pmf_finite finite_replicate_pmf) auto
  also have "\<dots> = ennreal ?n + 2*ennreal(\<integral>ds. real (?cps (min_list ds)) \<partial>replicate_pmf ?n ?dpmf)"
    by (simp add:ennreal_mult' integrable_measure_pmf_finite finite_replicate_pmf T_fin_ne)
  also have "\<dots> = ennreal ?n + 2*\<integral>\<^sup>+ x. ennreal (real (?cps (min_list x))) \<partial>replicate_pmf ?n ?dpmf"
    by (intro arg_cong2[where f="(+)"]  arg_cong2[where f="(*)"] finite_replicate_pmf
        nn_integral_eq_integral[symmetric] integrable_measure_pmf_finite) (auto simp:T_fin_ne)
  also have "\<dots> = ennreal ?n +2*\<integral>\<^sup>+ x. ennreal_of_enat (?cps (min_list x)) \<partial>replicate_pmf ?n ?dpmf"
    by (intro nn_integral_cong arg_cong2[where f="(+)"]  arg_cong2[where f="(*)"] refl)
      (simp add: ennreal_of_nat_eq_real_of_nat)
  also have "\<dots> = ennreal ?n +2*(\<Sum>t. emeasure (replicate_pmf ?n ?dpmf) {x. t<?cps (min_list x)})"
    by (subst nn_integral_enat_function) simp_all
  also have "\<dots> =ennreal ?n+2*(\<Sum>t<?m. emeasure(replicate_pmf ?n ?dpmf){x. t<?cps (min_list x)})"
    using b by (intro arg_cong2[where f="(+)"] arg_cong2[where f="(*)"] suminf_finite) auto
  also have "\<dots> =ennreal ?n+2*ennreal(\<Sum>t<?m. measure(replicate_pmf ?n ?dpmf){x. t<?cps(min_list x)})"
    unfolding measure_pmf.emeasure_eq_measure by simp
  also have "\<dots> \<le> ennreal ?n+2*ennreal (\<Sum>t<?m. (real (?m - (t+1))/real ?m)^?n)"
    by (intro add_mono order.refl iffD2[OF ennreal_mult_le_mult_iff] ennreal_leI sum_mono c) auto
  also have "\<dots> = ennreal ?n+ennreal (2*(\<Sum>t<?m. (real (?m - (t+1))^?n/real ?m^?n)))"
    using ennreal_mult' by (auto simp:algebra_simps power_divide)
  also have "\<dots> = ennreal (real ?n + (2*(\<Sum>t<?m. (real (?m - (t+1))^?n/real ?m^?n))))"
    by (intro ennreal_plus[symmetric] mult_nonneg_nonneg sum_nonneg) simp_all
  also have "\<dots> = ennreal (real ?n + (2*(\<Sum>t<?m. (real (?m - (t+1))^?n))/real ?m^?n))"
    by (simp add:sum_divide_distrib[symmetric])
  also have "\<dots> = ennreal (real ?n + (2*(\<Sum>t<?m. (real t^?n))/real ?m^?n))"
    by (intro arg_cong[where f="ennreal"] arg_cong2[where f="(+)"] arg_cong2[where f="(*)"]
         arg_cong2[where f="(/)"] refl sum.reindex_bij_betw bij_betwI[where g="\<lambda>x. ?m - (x+1)"])
       auto
  also have "\<dots> \<le> ennreal (real ?n + (2 * (real ?m^(?n+1)/real (?n +1)))/real ?m^?n)"
    by (intro ennreal_leI add_mono divide_right_mono mult_left_mono power_sum_approx) auto
  also have "\<dots> = ennreal (real ?n + (2 * (real ?m^(?n+1)/real ?m^?n)/ real (?n +1)))"
    by simp
  also have "\<dots> = ennreal (real ?n + ((2 * ?m)/ real (?n+1)))" by (simp add:field_simps)
  also have "\<dots> = ennreal (real ?n + (?n*(?n-1)/ real (?n+1)))"
    by (metis even_mult_iff even_numeral even_two_times_div_two odd_two_times_div_two_nat)
  also have "\<dots> = ennreal ((real ?n*(real ?n+1) +real ?n * (real ?n-real 1)) / real (?n+1))"
    using assms by (subst of_nat_diff[symmetric]) (auto simp:field_simps)
  also have "\<dots> = ennreal (2*real ?n * real ?n / real (?n+1))"
    using assms by (simp add:field_simps)
  also have "\<dots> \<le> ennreal (2*real ?n * real ?n / real ?n)"
    using assms by (intro ennreal_leI mult_right_mono divide_left_mono mult_pos_pos) auto
  also have "\<dots> = ennreal (2*real ?n)" by simp
  finally have "ennreal ?L \<le> ennreal (2*real ?n)" by simp
  thus "?L \<le> 2*real ?n" by simp
qed

definition time_closest_pair :: "real \<Rightarrow> real"
  where "time_closest_pair n = 2 + 1740 * n"

text \<open>Main results of this section:\<close>

theorem time_closest_pair:
  assumes "length ps \<ge> 2"
  shows "(\<integral>x. real (time x) \<partial>closest_pair ps) \<le> time_closest_pair (length ps)" (is "?L \<le> ?R")
proof -
  let ?n = "length ps"
  let ?cps = "close_point_size ps"
  let ?p = "map_pmf val (first_phase ps)"

  have "(0,1) \<in> {i. fst i < snd i \<and> snd i < length ps}" using assms by auto
  hence a:"finite {i. fst i < snd i \<and> snd i < length ps}" "{i. fst i<snd i \<and> snd i<length ps} \<noteq> {}"
    using fin_nat_pairs[where n="length ps"] by (auto simp:case_prod_beta')

  have "finite (set_pmf (map_pmf val (sample_distance ps)))"
    unfolding sample_distance_def val_tpmf_simps map_pmf_def[symmetric] using a
    by (intro finite_map_pmf) auto

  hence int[simp]: "integrable (measure_pmf (map_pmf val (first_phase ps))) f" for f :: "real \<Rightarrow> real"
    unfolding first_phase_def val_tpmf_simps val_replicate_tpmf unfolding map_pmf_def[symmetric]
    by (metis integrable_measure_pmf_finite finite_replicate_pmf finite_map_pmf)

  have "map_pmf time (closest_pair ps) = first_phase ps \<bind>
    (\<lambda>x. return_pmf (if  val x = 0 then (tick 0) else second_phase (val x) ps) \<bind>
    (\<lambda>y. return_pmf (time x + time y)))"
    using time_first_phase[OF assms]
    unfolding closest_pair_def time_bind_tpmf lift_tm_def if_distrib if_distribR by simp
  also have "... = map_pmf (\<lambda>x. time x + (if val x = 0 then 1 else time (second_phase (val x) ps)))
    (first_phase ps)"
    unfolding bind_return_pmf map_pmf_def by (simp cong:if_cong)
  also have "... =  map_pmf (\<lambda>x. 2*length ps +
    (if val x = 0 then 1 else time (second_phase (val x) ps))) (first_phase ps)"
    using time_first_phase[OF assms] unfolding map_pmf_eq_return_pmf_iff
    by (intro map_pmf_cong refl arg_cong2[where f="(+)"]) simp
  also have "... = map_pmf (\<lambda>x. 2*length ps + (if x=0 then 1 else time (second_phase x ps))) ?p"
    unfolding map_pmf_comp by simp
  finally have a:"map_pmf time (closest_pair ps) =
    map_pmf (\<lambda>x. 2*length ps + (if x=0 then 1 else time (second_phase x ps))) ?p" by simp

  have "(\<integral>x. real (time x) \<partial>closest_pair ps) = (\<integral>x. real x \<partial>map_pmf time (closest_pair ps))"
    by simp
  also have "\<dots> = (\<integral>d. 2 * real ?n + (if d=0 then 1 else time (second_phase d ps)) \<partial>?p)"
    unfolding a by simp
  also have "\<dots> \<le> (\<integral>d. 2 * real ?n + (if d\<le>0 then 1 else 2+44*?n+7*?cps ((2* sqrt 2)*d)) \<partial>?p)"
    using first_phase[OF assms] min_dist_nonneg[OF assms] order.trans unfolding AE_measure_pmf_iff
    by (intro integral_mono_AE int AE_pmfI of_nat_mono mono_intros
        time_second_phase[OF _ _ assms(1)] refl dual_order.not_eq_order_implies_strict) auto
  also have "\<dots> = (\<integral>d. 2*real ?n+(if d\<le>0 then 1 else 2+44*real ?n+7*real(?cps ((2* sqrt 2)*d))) \<partial>?p)"
    by (intro integral_cong_AE) simp_all
  also have "\<dots> \<le> (\<integral>d. 2 * real ?n +
    (if d\<le>0 then 1 else 2+44*real ?n+7*((2* sqrt 2 * (2* sqrt 2)+3)^2 * real (?cps d))) \<partial>?p)"
    using  growth_lemma[where a="2* sqrt 2"]
    by (intro integral_mono_AE int AE_pmfI mono_intros mult_right_mono) auto
  also have "\<dots> \<le>
    (\<integral>d. 2 * real ?n + (2+44*real ?n+7*((2* sqrt 2 * (2* sqrt 2)+3)^2 * real (?cps d))) \<partial>?p)"
    by (intro integral_mono_AE int AE_pmfI mono_intros mult_right_mono) simp
  also have "\<dots> = (\<integral>d. (2+46*real ?n)+847 * real (?cps d) \<partial>?p)" by (simp add:algebra_simps)
  also have "\<dots> = (\<integral>d. 2+46*real ?n \<partial>?p)+(\<integral>d. 847* real (?cps d) \<partial>?p)"
    by (intro Bochner_Integration.integral_add int)
  also have "\<dots> = (2+46*real ?n)+847*(\<integral>d. real (?cps d) \<partial>?p)"
    by (intro arg_cong2[where f="(+)"]) simp_all
  also have "\<dots> \<le> (2+46*real ?n)+847*(2 * real ?n)"
    by (intro mono_intros mult_left_mono exp_close_point_size assms) simp
  also have "\<dots>  = 2+1740* real ?n" by simp
  finally show ?thesis unfolding time_closest_pair_def by simp
qed

theorem asymptotic_time_closest_pair:
  "time_closest_pair \<in> O(\<lambda>x. x)"
  unfolding time_closest_pair_def by simp

end