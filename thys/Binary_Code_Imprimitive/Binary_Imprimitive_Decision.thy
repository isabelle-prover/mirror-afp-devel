(*  Title:      Binary_Imprimitive_Decision
    File:       Binary_Code_Imprimitive.Binary_Imprimitive_Decision
    Author:     Martin Raška, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Binary_Imprimitive_Decision
  imports
    "Binary_Code_Imprimitive.Binary_Code_Imprimitive"

begin

section \<open>Upper bound of the power exponent in the canonical imprimitivity witness\<close>

lemma LS_power_len_ge:
  assumes "y \<^sup>@ k \<cdot> x = z \<^sup>@ l"
    and "k * \<^bold>|y\<^bold>| \<ge> \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| - 1"
  shows "x \<cdot> y = y \<cdot> x"
proof (rule nemp_comm)
  assume "y \<noteq> \<epsilon>"
  have "y \<^sup>@ k \<le>p z \<cdot> y \<^sup>@ k"
    using \<open>y \<^sup>@ k \<cdot> x = z \<^sup>@ l\<close>
    by (blast intro!: pref_prod_root)
  moreover have "y \<^sup>@ k \<le>p y \<cdot> y \<^sup>@ k"
    by (blast intro!: pref_pow_ext')
  moreover have "1 \<le> gcd \<^bold>|z\<^bold>| \<^bold>|y\<^bold>|"
    using \<open>y \<noteq> \<epsilon>\<close>
    by (simp flip: less_eq_Suc_le)
  from this \<open>k * \<^bold>|y\<^bold>| \<ge> \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| - 1\<close>
  have "\<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| - (gcd \<^bold>|z\<^bold>| \<^bold>|y\<^bold>|) \<le> k * \<^bold>|y\<^bold>|"
    by (rule le_trans[OF diff_le_mono2])
  ultimately have "z \<cdot> y = y \<cdot> z"
    unfolding pow_len[symmetric] by (fact per_lemma_comm)
  with \<open>y \<^sup>@ k \<cdot> x = z \<^sup>@ l\<close>
  show "x \<cdot> y = y \<cdot> x"
    by (fact LS_comm)
qed

lemma LS_root_len_ge:
  assumes "y \<^sup>@ k \<cdot> x = z \<^sup>@ l"
    and "1 \<le> k" and "2 \<le> l"
    and "x \<cdot> y \<noteq> y \<cdot> x"
  shows "(k - 1) * \<^bold>|y\<^bold>| + 2 \<le> \<^bold>|z\<^bold>|"
proof (intro leI notI)
  assume "\<^bold>|z\<^bold>| < (k - 1) * \<^bold>|y\<^bold>| + 2"
  then have "\<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| \<le> Suc (k - 1) * \<^bold>|y\<^bold>| + 1"
    by simp
  also have "\<dots> = k * \<^bold>|y\<^bold>| + 1"
    using \<open>1 \<le> k\<close> by simp
  finally have "k * \<^bold>|y\<^bold>| \<ge> \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| - 1"
    unfolding le_diff_conv.
  from \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> LS_power_len_ge[OF \<open>y \<^sup>@ k \<cdot> x = z \<^sup>@ l\<close> this]
  show False..
qed

lemma LS_root_len_le:
  assumes "y \<^sup>@ k \<cdot> x = z \<^sup>@ l"
    and "1 \<le> k" and "2 \<le> l"
    and "x \<cdot> y \<noteq> y \<cdot> x"
  shows "\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| - 2"
proof -
  have "\<^bold>|x\<^bold>| + k * \<^bold>|y\<^bold>| = l * \<^bold>|z\<^bold>|"
    using lenarg[OF \<open>y \<^sup>@ k \<cdot> x = z \<^sup>@ l\<close>]
    by (simp only: pow_len lenmorph add.commute[of "\<^bold>|x\<^bold>|"])
  have "\<^bold>|z\<^bold>| \<le> (l - 1) * \<^bold>|z\<^bold>|"
    using diff_le_mono[OF \<open>2 \<le> l\<close>, of 1] by simp
  also have "\<dots> = \<^bold>|x\<^bold>| + k * \<^bold>|y\<^bold>| - \<^bold>|z\<^bold>|"
    unfolding diff_mult_distrib \<open>\<^bold>|x\<^bold>| + k * \<^bold>|y\<^bold>| = l * \<^bold>|z\<^bold>|\<close>[symmetric] by simp
  also have "\<dots> \<le> \<^bold>|x\<^bold>| + k * \<^bold>|y\<^bold>| - ((k - 1) * \<^bold>|y\<^bold>| + 2)"
    using LS_root_len_ge[OF assms]
    by (rule diff_le_mono2)
  also have "\<dots> \<le> \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| - 2"
    using \<open>1 \<le> k\<close> unfolding diff_diff_eq[symmetric]
    by (intro diff_le_mono) (simp add: le_diff_conv add.assoc diff_mult_distrib)
  finally show "\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| - 2".
qed

lemma LS_exp_le':
  assumes "y \<^sup>@ k \<cdot> x = z \<^sup>@ l"
    and "2 \<le> l"
    and "x \<cdot> y \<noteq> y \<cdot> x"
  shows "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
proof (cases "1 \<le> k")
  assume "1 \<le> k"
  have "\<^bold>|y\<^bold>| > 0"
    using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by blast
  have "(k - 1) * \<^bold>|y\<^bold>| + 2 \<le> \<^bold>|z\<^bold>|"
    using LS_root_len_ge \<open>y \<^sup>@ k \<cdot> x = z \<^sup>@ l\<close> \<open>1 \<le> k\<close> \<open>2 \<le> l\<close> \<open>x \<cdot> y \<noteq> y \<cdot> x\<close>.
  also have "\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| - 2"
    using LS_root_len_le \<open>y \<^sup>@ k \<cdot> x = z \<^sup>@ l\<close> \<open>1 \<le> k\<close> \<open>2 \<le> l\<close> \<open>x \<cdot> y \<noteq> y \<cdot> x\<close>.
  finally have "(k - 1) * \<^bold>|y\<^bold>| + 2 \<le> \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| - 2".
  then have "(k - 1) * \<^bold>|y\<^bold>| + 2 - \<^bold>|y\<^bold>| - 2 \<le> \<^bold>|x\<^bold>| + \<^bold>|y\<^bold>| - 2 - \<^bold>|y\<^bold>| - 2"
    by (intro diff_le_mono)
  then have "(k - 1) * \<^bold>|y\<^bold>| + 2 - 2 - \<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>| - (2 + 2)"
    unfolding diff_commute[of _ 2 "\<^bold>|y\<^bold>|"] unfolding diff_add_inverse2 diff_diff_eq.
  then have "(k - (1 + 1)) * \<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>| - 4"
    unfolding diff_add_inverse2 nat_distrib diff_diff_eq mult_1
    by presburger
  then show "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
    using \<open>\<^bold>|y\<^bold>| > 0\<close>
    by (simp only: less_eq_div_iff_mult_less_eq one_add_one flip: le_diff_conv)
qed (simp add: trans_le_add2)

lemma LS_exp_le:
  assumes "x \<cdot> y \<^sup>@ k = z \<^sup>@ l"
    and "2 \<le> l"
    and "x \<cdot> y \<noteq> y \<cdot> x"
  shows "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
  using LS_exp_le'[reversed, OF \<open>x \<cdot> y \<^sup>@ k = z \<^sup>@ l\<close> \<open>2 \<le> l\<close> \<open>x \<cdot> y \<noteq> y \<cdot> x\<close>[symmetric]].

thm bin_imprim_expsE
lemma bin_imprim_code_witnessE:
  assumes "x \<cdot> y \<noteq> y \<cdot> x" and "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
    and "ws \<in> lists {x,y}" and "2 \<le> \<^bold>|ws\<^bold>|"
    and "primitive ws" and  "\<not> primitive (concat ws)"
  obtains   "ws \<sim> [x, x, y]"
  | k where "1 \<le> k" and "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
    and "ws \<sim> [x] \<cdot> [y] \<^sup>@ k"
proof -
  obtain j k
    where "1 \<le> j" and "1 \<le> k" and "j = 1 \<or> k = 1"
      and witness_iff: "\<And>ws. ws \<in> lists {x,y} \<Longrightarrow>  2 \<le> \<^bold>|ws\<^bold>| \<Longrightarrow>
          (primitive ws \<and> \<not> primitive (concat ws) \<longleftrightarrow> ws \<sim> [x] \<^sup>@ j \<cdot> [y] \<^sup>@ k)"
      and
      j_ge: "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>| \<Longrightarrow> 2 \<le> j \<Longrightarrow> j = 2 \<and> primitive x \<and> primitive y" and
      k_ge: "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>| \<Longrightarrow> 2 \<le> k \<Longrightarrow> j = 1 \<and> primitive x"
    by (fact bin_imprim_code[OF assms(1, 3 - 6)])
  have "ws \<sim> [x] \<^sup>@ j \<cdot> [y] \<^sup>@ k"
    using witness_iff[OF \<open>ws \<in> lists {x, y}\<close> \<open>2 \<le> \<^bold>|ws\<^bold>|\<close>] \<open>primitive ws\<close> \<open>\<not> primitive (concat ws)\<close>
    by simp
  show thesis
  proof (cases)
    assume "2 \<le> j"
    from j_ge[OF \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close> this] \<open>j = 1 \<or> k = 1\<close>
    have "j = 2" and "k = 1"
      by simp_all
    then have "ws \<sim> [x, x, y]"
      using \<open>ws \<sim> [x] \<^sup>@ j \<cdot> [y] \<^sup>@ k\<close> by simp
    then show thesis..
  next
    assume "\<not> 2 \<le> j"
    with \<open>1 \<le> j\<close> have "j = 1"
      by simp
    then have "ws \<sim> [x] \<cdot> [y] \<^sup>@ k"
      using \<open>ws \<sim> [x] \<^sup>@ j \<cdot> [y] \<^sup>@ k\<close> by simp
    then have "\<not> primitive (x \<cdot> y \<^sup>@ k)"
      using \<open>\<not> primitive (concat ws)\<close> unfolding conjug_concat_prim_iff[OF \<open>ws \<sim> [x] \<cdot> [y] \<^sup>@ k\<close>]
      by simp
    moreover have "x \<cdot> y \<^sup>@ k \<noteq> \<epsilon>"
      using \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> by (intro notI) simp
    ultimately obtain z l
      where "2 \<le> l" and "z \<^sup>@ l = x \<cdot> y \<^sup>@ k"
      by (elim not_prim_expE)
    have "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
      using LS_exp_le[OF \<open>z \<^sup>@ l = x \<cdot> y \<^sup>@ k\<close>[symmetric] \<open>2 \<le> l\<close> \<open>x \<cdot> y \<noteq> y \<cdot> x\<close>].
    from \<open>1 \<le> k\<close> this \<open>ws \<sim> [x] \<cdot> [y] \<^sup>@ k\<close>
    show thesis..
  qed
qed

subsection \<open>Optimality of the exponent upper bound\<close>

lemma examples_bound_optimality:
  fixes m k and x y z :: "binA list"
  assumes "1 \<le> m" and "k' = 0 \<Longrightarrow> m = 1"
  defines "x \<equiv> \<aa> \<cdot> \<bb> \<cdot> (\<bb> \<cdot> (\<aa> \<cdot> \<bb>) \<^sup>@ m) \<^sup>@ k' \<cdot> \<bb> \<cdot> \<aa>"
    and "y \<equiv> \<bb> \<cdot> (\<aa> \<cdot> \<bb>) \<^sup>@ m"
    and "z \<equiv> \<aa> \<cdot> \<bb> \<cdot> (\<bb> \<cdot> (\<aa> \<cdot> \<bb>) \<^sup>@ m) \<^sup>@ (k' + 1)"
    and "k \<equiv> k' + 2"
  shows "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|" and "x \<cdot> y \<^sup>@ k = z \<cdot> z" and "k = (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
proof -
  obtain m' where m: "m = m' + 1"
    using \<open>1 \<le> m\<close> using add.commute le_Suc_ex by blast
  have x_len: "\<^bold>|x\<^bold>| = k' * (2 * m + 1) + 4"
    unfolding x_def by (simp add: pow_len)
  have y_len: "\<^bold>|y\<^bold>| = 2 * m + 1"
    unfolding y_def by (simp add: pow_len)
  have z_len: "\<^bold>|z\<^bold>| = (k' + 1) * (2 * m + 1) + 2"
    unfolding z_def by (simp add: pow_len)
  show "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
    using \<open>k' = 0 \<Longrightarrow> m = 1\<close> unfolding x_len y_len
    by (cases k') (simp_all add: pow_len)
  show "x \<cdot> y \<^sup>@ k = z \<cdot> z"
    unfolding x_def y_def z_def k_def
    by comparison
  show "k = (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
  proof -
    have "\<^bold>|x\<^bold>| - 4 = k' * \<^bold>|y\<^bold>|"
      unfolding x_len y_len by simp
    have "\<^bold>|y\<^bold>| \<noteq> 0"
      unfolding y_def by blast
    have "k' = (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>|"
      unfolding \<open>\<^bold>|x\<^bold>| - 4 = k' * \<^bold>|y\<^bold>|\<close> nonzero_mult_div_cancel_right[OF \<open>\<^bold>|y\<^bold>| \<noteq> 0\<close>]..
    then show "k = (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
      unfolding k_def by blast
  qed
qed

section \<open>Characterization of binary primitivity preserving morphisms given by a pair of words\<close>

lemma len_le_not_bin_primE:
  assumes "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
    and "\<not> bin_prim x y"
  obtains  "\<not> primitive (x \<cdot> x \<cdot> y)"
  | k where "1 \<le> k" and "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
    and "\<not> primitive (x \<cdot> y \<^sup>@ k)"
proof (cases)
  assume "x \<cdot> y = y \<cdot> x"
  have "\<not> primitive (x \<cdot> x \<cdot> y)"
    using \<open>x \<cdot> y = y \<cdot> x\<close> \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>
    by (cases "x \<noteq> \<epsilon>") (intro comm_not_prim, simp_all)
  then show thesis..
next
  assume "x \<cdot> y \<noteq> y \<cdot> x"
  then have "x \<noteq> y"
    by blast
  obtain ws where
      "ws \<in> lists {x, y}" and "2 \<le> \<^bold>|ws\<^bold>|" and "primitive ws" and "\<not> primitive (concat ws)"
    using \<open>\<not> bin_prim x y\<close> unfolding bin_prim_concat_prim_pres_conv[OF \<open>x \<noteq> y\<close>]
    by blast
  then consider "ws \<sim> [x, x, y]"
    | k where "1 \<le> k" and "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
      and   "ws \<sim> [x] \<cdot> [y] \<^sup>@ k"
    by (rule bin_imprim_code_witnessE[OF \<open>x \<cdot> y \<noteq> y \<cdot> x\<close> \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>])
  then show thesis
  proof (cases)
    assume "ws \<sim> [x, x, y]"
    then have "\<not> primitive (x \<cdot> x \<cdot> y)"
      using \<open>\<not> primitive (concat ws)\<close>
      by (simp add: conjug_concat_prim_iff)
    then show thesis..
  next
    fix k
    assume "1 \<le> k" and "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2" and "ws \<sim> [x] \<cdot> [y] \<^sup>@ k"
    have "\<not> primitive (x \<cdot> y \<^sup>@ k)"
      using \<open>ws \<sim> [x] \<cdot> [y] \<^sup>@ k\<close> \<open>\<not> primitive (concat ws)\<close>
      by (simp add: conjug_concat_prim_iff)
    from \<open>1 \<le> k\<close> \<open>k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2\<close> this
    show thesis..
  qed
qed

lemma bin_prim_xyk:
  assumes "bin_prim x y" and "0 < k"
  shows "primitive (x \<cdot> y \<^sup>@ k)"
proof -
  have "primitive ([x] \<cdot> [y] \<^sup>@ k)"
    using bin_prim_code[OF \<open>bin_prim x y\<close>]
    by (intro prim_abk) blast
  from bin_prim_concat_prim_pres[OF \<open>bin_prim x y\<close> _ _ this] \<open>0 < k\<close>
  show "primitive (x \<cdot> y \<^sup>@ k)"
    by (simp add: pow_in_lists)
qed

lemma len_le_bin_prim_iff:
  assumes "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|"
  shows
    "bin_prim x y \<longleftrightarrow> primitive (x \<cdot> x \<cdot> y) \<and> (\<forall>k. 1 \<le> k \<and> k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2 \<longrightarrow> primitive (x \<cdot> y \<^sup>@ k))"
    (is "bin_prim x y \<longleftrightarrow> (?xxy \<and> ?xyk)")
proof (intro iffI[OF _ contrapos_pp])
  assume "bin_prim x y"
  show "?xxy \<and> ?xyk"
  proof (intro conjI allI impI)
    show "primitive (x \<cdot> x \<cdot> y)"
      using bin_prim_xyk[OF \<open>bin_prim x y\<close>[symmetric], of 2] conjug_prim_iff'
      by (simp add: conjug_prim_iff'[of y])
    show "primitive (x \<cdot> y \<^sup>@ k)" if "1 \<le> k \<and> k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2" for k
      using bin_prim_xyk[OF \<open>bin_prim x y\<close>, of k] conjunct1[OF that]
      by fastforce
  qed
next
  assume "\<not> bin_prim x y"
  then consider "\<not> primitive (x \<cdot> x \<cdot> y)"
  | k where "1 \<le> k" and "k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2"
    and "\<not> primitive (x \<cdot> y \<^sup>@ k)"
  by (elim len_le_not_bin_primE[OF \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close>])
  then show "\<not> (?xxy \<and> ?xyk)"
    by (cases) blast+
qed

lemma len_eq_bin_prim_iff:
  assumes "\<^bold>|x\<^bold>| = \<^bold>|y\<^bold>|"
  shows "bin_prim x y \<longleftrightarrow> primitive (x \<cdot> y)"
proof
  show "bin_prim x y \<Longrightarrow> primitive (x \<cdot> y)"
    using bin_prim_xyk[of _ _ 1]
    by simp
  assume "primitive (x \<cdot> y)"
  then have "x \<cdot> y \<noteq> y \<cdot> x"
    using assms eq_append_not_prim by auto
  from this bin_uniform_prim_morph[OF this \<open>\<^bold>|x\<^bold>| = \<^bold>|y\<^bold>|\<close> \<open>primitive (x \<cdot> y)\<close>]
  show "bin_prim x y"
    unfolding bin_prim_altdef2
    by simp
qed

theorem bin_prim_iff:
  "bin_prim x y \<longleftrightarrow>
    (if \<^bold>|y\<^bold>| < \<^bold>|x\<^bold>|
      then primitive (x \<cdot> x \<cdot> y) \<and> (\<forall>k. 1 \<le> k \<and> k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2 \<longrightarrow> primitive (x \<cdot> y \<^sup>@ k))
    else if \<^bold>|x\<^bold>| < \<^bold>|y\<^bold>|
      then primitive (y \<cdot> y \<cdot> x) \<and> (\<forall>k. 1 \<le> k \<and> k \<le> (\<^bold>|y\<^bold>| - 4) div \<^bold>|x\<^bold>| + 2 \<longrightarrow> primitive (y \<cdot> x \<^sup>@ k))
    else primitive (x \<cdot> y)
    )"
proof (cases rule: linorder_cases)
  assume "\<^bold>|x\<^bold>| < \<^bold>|y\<^bold>|"
  then show ?thesis
    unfolding bin_prim_commutes[of x y]
    unfolding len_le_bin_prim_iff[OF less_imp_le[OF \<open>\<^bold>|x\<^bold>| < \<^bold>|y\<^bold>|\<close>]]
    by (simp only: if_not_P[OF less_not_sym] if_P)
next
  assume "\<^bold>|y\<^bold>| < \<^bold>|x\<^bold>|"
  then show ?thesis
    unfolding len_le_bin_prim_iff[OF less_imp_le[OF \<open>\<^bold>|y\<^bold>| < \<^bold>|x\<^bold>|\<close>]]
    by (simp only: if_P)
next
  assume "\<^bold>|x\<^bold>| = \<^bold>|y\<^bold>|"
  then show ?thesis
    unfolding len_eq_bin_prim_iff[OF \<open>\<^bold>|x\<^bold>| = \<^bold>|y\<^bold>|\<close>]
    by simp
qed

subsection \<open>Code equation for @{term bin_prim} predicate\<close>

context
begin

private lemma all_less_Suc_conv: "(\<forall>k < n. P (Suc k)) \<longleftrightarrow> (\<forall>k \<le> n. k \<ge> 1 \<longrightarrow> P k)"
proof (intro iffI allI impI)
  fix k
  assume "\<forall>k<n. P (Suc k)" and "k \<le> n" and "1 \<le> k"
  then show "P k"
    by (elim allE[of _ "k - 1"]) (simp only: Suc_diff_1)
qed simp

lemma bin_prim_iff' [code]:
  "bin_prim x y \<longleftrightarrow>
    (if \<^bold>|y\<^bold>| < \<^bold>|x\<^bold>|
      then primitive (x \<cdot> x \<cdot> y) \<and> (\<forall>k < (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2. primitive (x \<cdot> y \<^sup>@ (Suc k)))
    else if \<^bold>|x\<^bold>| < \<^bold>|y\<^bold>|
      then bin_prim y x
    else primitive (x \<cdot> y)
    )"
proof (cases rule: linorder_cases)
  show "\<^bold>|x\<^bold>| < \<^bold>|y\<^bold>| \<Longrightarrow> ?thesis"
    unfolding bin_prim_commutes[of x y]
    by simp
next
  assume "\<^bold>|y\<^bold>| < \<^bold>|x\<^bold>|"
  then show ?thesis
    using len_le_bin_prim_iff[OF less_imp_le[OF \<open>\<^bold>|y\<^bold>| < \<^bold>|x\<^bold>|\<close>]]
    unfolding all_less_Suc_conv[where P = "\<lambda>k. primitive (_ \<cdot> _ \<^sup>@ k)"]
    unfolding conj_comms[of "1 \<le> _"] imp_conjL
    by (simp only: if_P)
next
  assume "\<^bold>|x\<^bold>| = \<^bold>|y\<^bold>|"
  then show ?thesis
    unfolding len_eq_bin_prim_iff[OF \<open>\<^bold>|x\<^bold>| = \<^bold>|y\<^bold>|\<close>]
    by simp
qed

end
value "bin_prim (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<aa>) \<bb>" \<comment> \<open>True\<close>
value "bin_prim (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>) \<bb>" \<comment> \<open>False\<close>
value "bin_prim (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>) (\<bb>\<cdot>\<aa>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<bb>)" \<comment> \<open>False\<close>
value "bin_prim (\<aa>\<cdot>\<bb>) (\<aa>\<cdot>\<bb>)" \<comment> \<open>False\<close>
value "bin_prim (\<aa>\<cdot>\<bb>) (\<aa>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<bb>)" \<comment> \<open>False\<close>
value "bin_prim (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<aa>) (\<bb>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<bb>)" \<comment> \<open>True\<close>

section \<open>Characterization of binary imprimitivity codes\<close>

theorem bin_imprim_code_iff:
  "bin_imprim_code x y \<longleftrightarrow> x \<cdot> y \<noteq> y \<cdot> x \<and>
    (if \<^bold>|y\<^bold>| < \<^bold>|x\<^bold>|
      then \<not> primitive (x \<cdot> x \<cdot> y) \<or> (\<exists>k. 1 \<le> k \<and> k \<le> (\<^bold>|x\<^bold>| - 4) div \<^bold>|y\<^bold>| + 2 \<and> \<not> primitive (x \<cdot> y \<^sup>@ k))
    else if \<^bold>|x\<^bold>| < \<^bold>|y\<^bold>|
      then \<not> primitive (y \<cdot> y \<cdot> x) \<or> (\<exists>k. 1 \<le> k \<and> k \<le> (\<^bold>|y\<^bold>| - 4) div \<^bold>|x\<^bold>| + 2 \<and> \<not> primitive (y \<cdot> x \<^sup>@ k))
    else \<not> primitive (x \<cdot> y)
    )"
  unfolding bin_imprim_code_def bin_prim_iff
  by (simp only: de_Morgan_conj not_all not_imp conj_assoc flip: if_image[of _ Not])

value "bin_imprim_code (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<aa>) \<bb>" \<comment> \<open>False\<close>
value "bin_imprim_code  (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>) \<bb>" \<comment> \<open>True\<close>
value "bin_imprim_code  (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>) (\<bb>\<cdot>\<aa>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<bb>)" \<comment> \<open>True\<close>
value "bin_imprim_code  (\<aa>\<cdot>\<bb>) (\<aa>\<cdot>\<bb>)" \<comment> \<open>False\<close>
value "bin_imprim_code  (\<aa>\<cdot>\<bb>) (\<aa>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<bb>)" \<comment> \<open>False\<close>
value "bin_imprim_code  (\<aa>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<aa>\<cdot>\<aa>) (\<bb>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<bb>\<cdot>\<bb>)" \<comment> \<open>False\<close>


end
