
(* Author: Benoît Ballenghien, Université Paris-Saclay, CNRS, ENS Paris-Saclay, LMF
   Author: Benjamin Puyobro, Université Paris-Saclay, IRT SystemX, CNRS, ENS Paris-Saclay, LMF
   Author: Burkhart Wolff, Université Paris-Saclay, CNRS, ENS Paris-Saclay, LMF *)

(*<*)
theory Elementary_Ultrametric_Spaces
  imports "HOL-Analysis.Elementary_Metric_Spaces"
begin
  (*>*)


section \<open>Definition\<close>

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, NONE)\<close>
  \<comment> \<open>To be able to use \<^const>\<open>dist\<close> out of the \<^class>\<open>metric_space\<close> class.\<close>

class ultrametric_space = uniformity_dist + open_uniformity +
  assumes dist_eq_0_iff [simp]: \<open>dist x y = 0 \<longleftrightarrow> x = y\<close>
    and ultrametric_dist_triangle2: \<open>dist x y \<le> max (dist x z) (dist y z)\<close>
begin

subclass metric_space
proof (unfold_locales)
  show \<open>dist x y = 0 \<longleftrightarrow> x = y\<close> for x y by simp
next
  show \<open>dist x y \<le> dist x z + dist y z\<close> for x y z
    by (rule order_trans[OF ultrametric_dist_triangle2, of _ z], simp)
      (metis local.dist_eq_0_iff ultrametric_dist_triangle2 max.idem)
qed

end

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a :: metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>
  \<comment> \<open>Back to normal.\<close>


class complete_ultrametric_space = ultrametric_space +
  assumes Cauchy_convergent: \<open>Cauchy X \<Longrightarrow> convergent X\<close>
begin

subclass complete_space by unfold_locales (fact Cauchy_convergent)

end



section \<open>Properties on Balls\<close>

text \<open>In ultrametric space, balls satisfy very strong properties.\<close>

context ultrametric_space begin

lemma ultrametric_dist_triangle: \<open>dist x z \<le> max (dist x y) (dist y z)\<close>
  using ultrametric_dist_triangle2 [of x z y] by (simp add: dist_commute)

lemma ultrametric_dist_triangle3: \<open>dist x y \<le> max (dist a x) (dist a y)\<close>
  using ultrametric_dist_triangle2 [of x y a] by (simp add: dist_commute)

end



subsection \<open>Balls are centered everywhere\<close>

context fixes x :: \<open>'a :: ultrametric_space\<close> begin

text \<open>The best way to do this would be to work in the context \<^locale>\<open>ultrametric_space\<close>.
      Unfortunately, \<^const>\<open>ball\<close>, \<^const>\<open>cball\<close>, etc. are not defined inside
      the context \<^locale>\<open>metric_space\<close> but through a sort constraint.\<close>

lemma ultrametric_every_point_of_ball_is_centre :
  \<open>ball y r = ball x r\<close> if \<open>y \<in> ball x r\<close> 
proof (unfold set_eq_iff, rule allI)
  from \<open>y \<in> ball x r\<close> have * : \<open>dist x y < r\<close> by simp
  show \<open>z \<in> ball y r \<longleftrightarrow> z \<in> ball x r\<close> for z
    using ultrametric_dist_triangle[of x z y]
      "*" ultrametric_dist_triangle[of y z x]
    by (intro iffI) (simp_all add: dist_commute)
qed


lemma ultrametric_every_point_of_cball_is_centre :
  \<open>cball y r = cball x r\<close> if \<open>y \<in> cball x r\<close>
proof (unfold set_eq_iff, rule allI)
  from \<open>y \<in> cball x r\<close> have * : \<open>dist x y \<le> r\<close> by simp
  show \<open>z \<in> cball y r \<longleftrightarrow> z \<in> cball x r\<close> for z
    using ultrametric_dist_triangle[of x z y]
      "*" ultrametric_dist_triangle[of y z x]
    by (intro iffI) (simp_all add: dist_commute)
qed

end



subsection \<open>Balls are ``clopen''\<close>

text \<open>Balls are both open and closed.\<close>

context fixes x :: \<open>'a :: ultrametric_space\<close> begin

lemma ultrametric_open_cball [intro, simp] : \<open>open (cball x r)\<close> if \<open>0 < r\<close>
proof (rule openI) 
  fix y assume \<open>y \<in> cball x r\<close>
  hence \<open>cball y r = cball x r\<close>
    by (rule ultrametric_every_point_of_cball_is_centre)
  hence \<open>ball y (r / 2) \<subseteq> cball x r\<close>
    by (metis ball_subset_cball cball_divide_subset_numeral subset_trans)
  moreover have \<open>0 < r / 2\<close> by (simp add: \<open>0 < r\<close>)
  ultimately show \<open>\<exists>e>0. ball y e \<subseteq> cball x r\<close> by blast
qed

lemma \<open>closed (cball y r)\<close> by (fact closed_cball)


lemma ultrametric_closed_ball [intro, simp]: \<open>closed (ball x r)\<close> if \<open>0 \<le> r\<close>
proof (cases \<open>r = 0\<close>)
  show \<open>r = 0 \<Longrightarrow> closed (ball x r)\<close> by simp
next
  assume \<open>r \<noteq> 0\<close>
  with \<open>0 \<le> r\<close> have \<open>0 < r\<close> by simp
  show \<open>closed (ball x r)\<close>
  proof (unfold closed_def)
    have \<open>- ball x r = (\<Union>z \<in> - ball x r. ball z r)\<close>
    proof (intro subset_antisym subsetI)
      from \<open>0 < r\<close> show \<open>z \<in> - ball x r \<Longrightarrow> z \<in> (\<Union>z\<in>- ball x r. ball z r)\<close> for z
        by (meson UN_iff centre_in_ball)
    next
      show \<open>z \<in> (\<Union>z \<in> - ball x r. ball z r) \<Longrightarrow> z \<in> - ball x r\<close> for z
        by simp (metis ComplD dist_commute mem_ball
            ultrametric_every_point_of_ball_is_centre)
    qed
    show \<open>open (- ball x r)\<close> by (subst \<open>?this\<close>, rule open_Union, simp)
  qed
qed

lemma ultrametric_open_sphere [intro, simp] : \<open>0 < r \<Longrightarrow> open (sphere x r)\<close>
  by (fold cball_diff_eq_sphere) (simp add: open_Diff order_le_less)

lemma closed_sphere [intro, simp] : \<open>closed (sphere y r)\<close>
  by (metis open_ball cball_diff_eq_sphere closed_Diff closed_cball)

end



subsection \<open>Balls are disjoint or contained\<close>

context fixes x :: \<open>'a :: ultrametric_space\<close> begin

lemma ultrametric_ball_ball_disjoint_or_subset:
  \<open>ball x r \<inter> ball y s = {} \<or> ball x r \<subseteq> ball y s \<or>
   ball y s \<subseteq> ball x r\<close>
proof (unfold disj_imp, intro impI)
  assume \<open>ball x r \<inter> ball y s \<noteq> {}\<close> \<open>\<not> ball x r \<subseteq> ball y s\<close>
  from \<open>ball x r \<inter> ball y s \<noteq> {}\<close>
  obtain z where \<open>z \<in> ball x r\<close> and \<open>z \<in> ball y s\<close> by blast
  with ultrametric_every_point_of_ball_is_centre
  have \<open>ball x r = ball z r\<close> and \<open>ball y s = ball z s\<close> by auto
  with \<open>\<not> ball x r \<subseteq> ball y s\<close> have \<open>s < r\<close> by auto
  with \<open>ball x r = ball z r\<close> and \<open>ball y s = ball z s\<close>
  show \<open>ball y s \<subseteq> ball x r\<close> by auto
qed

lemma ultrametric_ball_cball_disjoint_or_subset:
  \<open>ball x r \<inter> cball y s = {} \<or> ball x r \<subseteq> cball y s \<or>
   cball y s \<subseteq> ball x r\<close>
proof (unfold disj_imp, intro impI)
  assume \<open>ball x r \<inter> cball y s \<noteq> {}\<close> \<open>\<not> ball x r \<subseteq> cball y s\<close>
  from \<open>ball x r \<inter> cball y s \<noteq> {}\<close>
  obtain z where \<open>z \<in> ball x r\<close> and \<open>z \<in> cball y s\<close> by blast
  with ultrametric_every_point_of_ball_is_centre
    ultrametric_every_point_of_cball_is_centre
  have \<open>ball x r = ball z r\<close> \<open>cball y s = cball z s\<close> by blast+
  with \<open>\<not> ball x r \<subseteq> cball y s\<close> have \<open>s < r\<close> by auto
  with \<open>ball x r = ball z r\<close> and \<open>cball y s = cball z s\<close>
  show \<open>cball y s \<subseteq> ball x r\<close> by auto
qed

corollary ultrametric_cball_ball_disjoint_or_subset:
  \<open>cball x r \<inter> ball y s = {} \<or> cball x r \<subseteq> ball y s \<or>
   ball y s \<subseteq> cball x r\<close>
  using Elementary_Ultrametric_Spaces.ultrametric_ball_cball_disjoint_or_subset by blast

lemma ultrametric_cball_cball_disjoint_or_subset:
  \<open>cball x r \<inter> cball y s = {} \<or> cball x r \<subseteq> cball y s \<or>
   cball y s \<subseteq> cball x r\<close>
proof (unfold disj_imp, intro impI)
  assume \<open>cball x r \<inter> cball y s \<noteq> {}\<close> \<open>\<not> cball x r \<subseteq> cball y s\<close>
  from \<open>cball x r \<inter> cball y s \<noteq> {}\<close>
  obtain z where \<open>z \<in> cball x r\<close> and \<open>z \<in> cball y s\<close> by blast
  with ultrametric_every_point_of_cball_is_centre
  have \<open>cball x r = cball z r\<close> \<open>cball y s = cball z s\<close> by auto
  with \<open>\<not> cball x r \<subseteq> cball y s\<close> have \<open>s < r\<close> by auto
  with \<open>cball x r = cball z r\<close> and \<open>cball y s = cball z s\<close>
  show \<open>cball y s \<subseteq> cball x r\<close> by auto
qed

end



subsection \<open>Distance to a Ball\<close>

context fixes a :: \<open>'a :: ultrametric_space\<close> begin

lemma ultrametric_equal_distance_to_ball:
  \<open>dist a y = dist a z\<close> if \<open>a \<notin> ball x r\<close> \<open>y \<in> ball x r\<close> \<open>z \<in> ball x r\<close>
proof (rule order_antisym)
  show \<open>dist a y \<le> dist a z\<close>
    by (rule order_trans[OF ultrametric_dist_triangle[of a y z]], simp)
      (metis dist_commute dual_order.strict_trans2 linorder_linear
        mem_ball that ultrametric_every_point_of_ball_is_centre)
next
  show \<open>dist a z \<le> dist a y\<close>
    by (rule order_trans[OF ultrametric_dist_triangle[of a z y]], simp)
      (metis dist_commute dual_order.strict_trans2 linorder_linear
        mem_ball that ultrametric_every_point_of_ball_is_centre)
qed


lemma ultrametric_equal_distance_to_cball:
  \<open>dist a y = dist a z\<close> if \<open>a \<notin> cball x r\<close> \<open>y \<in> cball x r\<close> \<open>z \<in> cball x r\<close>
proof (rule order_antisym)
  show \<open>dist a y \<le> dist a z\<close>
    by (rule order_trans[OF ultrametric_dist_triangle[of a y z]], simp)
      (metis dist_commute dual_order.trans linorder_linear mem_cball
        that ultrametric_every_point_of_cball_is_centre)
next
  show \<open>dist a z \<le> dist a y\<close>
    by (rule order_trans[OF ultrametric_dist_triangle[of a z y]], simp)
      (metis dist_commute dual_order.trans linorder_linear mem_cball
        that ultrametric_every_point_of_cball_is_centre)
qed

end


context fixes x :: \<open>'a :: ultrametric_space\<close> begin

lemma ultrametric_equal_distance_between_ball_ball:
  \<open>ball x r \<inter> ball y s = {} \<Longrightarrow>
   \<exists>d. \<forall>a \<in> ball x r. \<forall>b \<in> ball y s. dist a b = d\<close>
  by (metis disjoint_iff dist_commute ultrametric_equal_distance_to_ball)          

lemma ultrametric_equal_distance_between_ball_cball:
  \<open>ball x r \<inter> cball y s = {} \<Longrightarrow>
   \<exists>d. \<forall>a \<in> ball x r. \<forall>b \<in> cball y s. dist a b = d\<close>
  by (metis disjoint_iff dist_commute ultrametric_equal_distance_to_ball
      ultrametric_equal_distance_to_cball)

lemma ultrametric_equal_distance_between_cball_ball:
  \<open>cball x r \<inter> ball y s = {} \<Longrightarrow>
   \<exists>d. \<forall>a \<in> cball x r. \<forall>b \<in> ball y s. dist a b = d\<close>
  by (metis disjoint_iff_not_equal dist_commute ultrametric_equal_distance_to_ball
      ultrametric_equal_distance_to_cball)

lemma ultrametric_equal_distance_between_cball_cball:
  \<open>cball x r \<inter> cball y s = {} \<Longrightarrow>
   \<exists>d. \<forall>a \<in> cball x r. \<forall>b \<in> cball y s. dist a b = d\<close>
  by (metis disjoint_iff dist_commute ultrametric_equal_distance_to_cball)

end



section \<open>Additional Properties\<close>

text \<open>Here are a few other interesting properties.\<close>

subsection \<open>Cauchy Sequences\<close>

lemma (in ultrametric_space) ultrametric_dist_triangle_generalized:
  \<open>n < m \<Longrightarrow> dist (\<sigma> n) (\<sigma> m) \<le> (MAX l \<in> {n..m - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))\<close>
proof (induct m)
  show \<open>n < 0 \<Longrightarrow> dist (\<sigma> n) (\<sigma> 0) \<le> (MAX l\<in>{n..0 - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))\<close> by simp
next
  case (Suc m)
  show \<open>dist (\<sigma> n) (\<sigma> (Suc m)) \<le> (MAX l\<in>{n..Suc m - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))\<close>
  proof (cases \<open>n = m\<close>)
    show \<open>n = m \<Longrightarrow> dist (\<sigma> n) (\<sigma> (Suc m)) \<le> (MAX l\<in>{n..Suc m - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))\<close>
      by simp
  next
    assume \<open>n \<noteq> m\<close>
    with \<open>n < Suc m\<close> obtain m' where \<open>m = Suc m'\<close> \<open>n \<le> m'\<close> 
      by (metis le_add1 less_Suc_eq less_imp_Suc_add)
    have \<open>{n..Suc m'} = {n..m-1} \<union> {m}\<close>
      by (simp add: \<open>m = Suc m'\<close> \<open>n \<le> m'\<close> atLeastAtMostSuc_conv le_Suc_eq)
    have \<open>dist (\<sigma> n) (\<sigma> (Suc m)) \<le> max (dist (\<sigma> n) (\<sigma> m)) (dist (\<sigma> m) (\<sigma> (Suc m)))\<close>
      by (simp add: ultrametric_dist_triangle)
    also have \<open>\<dots> \<le> max ((MAX l\<in>{n..m - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))) (dist (\<sigma> m) (\<sigma> (Suc m)))\<close>
      using Suc.hyps Suc.prems \<open>n \<noteq> m\<close> by linarith
    also have \<open>\<dots> = (MAX l\<in>{n..Suc m - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))\<close>
      by (subst Max_Un[of _ \<open>((\<lambda>l. dist (\<sigma> l) (\<sigma> (Suc l))) ` {m})\<close>, simplified, symmetric])
        (simp_all add: \<open>m = Suc m'\<close> \<open>n \<le> m'\<close> \<open>{n..Suc m'} = {n..m-1} \<union> {m}\<close>)
    finally show \<open>dist (\<sigma> n) (\<sigma> (Suc m)) \<le> (MAX l\<in>{n..Suc m - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))\<close> .
  qed
qed


lemma (in ultrametric_space) ultrametric_Cauchy_iff:
  \<open>Cauchy \<sigma> \<longleftrightarrow> (\<lambda>n. dist (\<sigma> (Suc n)) (\<sigma> n)) \<longlonglongrightarrow> 0\<close>
proof (rule iffI)
  assume \<open>Cauchy \<sigma>\<close>
  show \<open>(\<lambda>n. dist (\<sigma> (Suc n)) (\<sigma> n)) \<longlonglongrightarrow> 0\<close>
  proof (unfold lim_sequentially, intro allI impI)
    fix \<epsilon> :: real
    assume \<open>0 < \<epsilon>\<close>
    from \<open>Cauchy \<sigma>\<close>[unfolded Cauchy_altdef, rule_format, OF \<open>0 < \<epsilon>\<close>]
    show \<open>\<exists>N. \<forall>n\<ge>N. dist (dist (\<sigma> (Suc n)) (\<sigma> n)) 0 < \<epsilon>\<close>
      by (auto simp add: dist_commute)
  qed
next
  assume convergent : \<open>(\<lambda>n. dist (\<sigma> (Suc n)) (\<sigma> n)) \<longlonglongrightarrow> 0\<close>
  show \<open>Cauchy \<sigma>\<close>
  proof (unfold Cauchy_altdef2, intro allI impI)
    fix \<epsilon> :: real
    assume \<open>0 < \<epsilon>\<close>
    from convergent[unfolded lim_sequentially, rule_format, OF \<open>0 < \<epsilon>\<close>]
    obtain N where * : \<open>N \<le> n \<Longrightarrow> dist (\<sigma> (Suc n)) (\<sigma> n) < \<epsilon>\<close> for n
      by (simp add: dist_real_def) blast

    have \<open>N < n \<Longrightarrow> dist (\<sigma> n) (\<sigma> N) < \<epsilon>\<close> for n
    proof (subst dist_commute, rule le_less_trans)
      show \<open>N < n \<Longrightarrow> dist (\<sigma> N) (\<sigma> n) \<le> (MAX l\<in>{N..n - 1}. dist (\<sigma> l) (\<sigma> (Suc l)))\<close>
        by (fact ultrametric_dist_triangle_generalized)
    next
      show \<open>N < n \<Longrightarrow> (MAX l\<in>{N..n - 1}. dist (\<sigma> l) (\<sigma> (Suc l))) < \<epsilon>\<close>
        by simp (metis "*" atLeastAtMost_iff dist_commute)
    qed
    with \<open>0 < \<epsilon>\<close> have \<open>N \<le> n \<Longrightarrow> dist (\<sigma> n) (\<sigma> N) < \<epsilon>\<close> for n
      by (cases \<open>N = n\<close>) simp_all 
    thus \<open>\<exists>N. \<forall>n\<ge>N. dist (\<sigma> n) (\<sigma> N) < \<epsilon>\<close> by blast
  qed
qed



subsection \<open>Isosceles Triangle Principle\<close>

lemma (in ultrametric_space) ultrametric_isosceles_triangle_principle : 
  \<open>dist x z = max (dist x y) (dist y z)\<close> if \<open>dist x y \<noteq> dist y z\<close>
proof (rule order_antisym)
  show \<open>dist x z \<le> max (dist x y) (dist y z)\<close>
    by (fact ultrametric_dist_triangle)
next
  from \<open>dist x y \<noteq> dist y z\<close> linorder_less_linear
  have \<open>dist x y < dist y z \<or> dist y z < dist x y\<close> by blast
  with ultrametric_dist_triangle[of y z x]
    ultrametric_dist_triangle[of x y z]
  show \<open>max (dist x y) (dist y z) \<le> dist x z\<close>
    by (elim disjE) (simp_all add: dist_commute)
qed



subsection \<open>Distance to a convergent Sequence\<close>

lemma ultrametric_dist_to_convergent_sequence_is_eventually_const :
  fixes \<sigma> :: \<open>nat \<Rightarrow> 'a :: ultrametric_space\<close>
  assumes \<open>\<sigma> \<longlonglongrightarrow> \<Sigma>\<close> and \<open>x \<noteq> \<Sigma>\<close>
  shows \<open>\<exists>N. \<forall>n\<ge>N. dist (\<sigma> n) x = dist \<Sigma> x\<close>
proof -
  from \<open>x \<noteq> \<Sigma>\<close> have \<open>0 < dist x \<Sigma>\<close> by simp
  then obtain \<epsilon> where \<open>0 < \<epsilon>\<close> \<open>ball x \<epsilon> \<inter> ball \<Sigma> \<epsilon> = {}\<close>
    by (metis centre_in_ball disjoint_iff mem_ball order_less_le
        ultrametric_every_point_of_ball_is_centre)

  from \<open>\<sigma> \<longlonglongrightarrow> \<Sigma>\<close> \<open>0 < \<epsilon>\<close> obtain N where \<open>N \<le> n \<Longrightarrow> \<sigma> n \<in> ball \<Sigma> \<epsilon>\<close> for n
    by (auto simp add: dist_commute lim_sequentially)
  with \<open>0 < \<epsilon>\<close> \<open>ball x \<epsilon> \<inter> ball \<Sigma> \<epsilon> = {}\<close> have \<open>N \<le> n \<Longrightarrow> dist (\<sigma> n) x = dist \<Sigma> x\<close> for n
    by (metis centre_in_ball dist_commute ultrametric_equal_distance_between_ball_ball)
  thus \<open>\<exists>N. \<forall>n\<ge>N. dist (\<sigma> n) x = dist \<Sigma> x\<close> by blast
qed



subsection \<open>Diameter\<close>

lemma ultrametric_diameter : \<open>diameter S = (SUP y \<in> S. dist x y)\<close>
  if \<open>bounded S\<close> and \<open>x \<in> S\<close> for x :: \<open>'a :: ultrametric_space\<close>
proof -
  from \<open>x \<in> S\<close> have \<open>S \<noteq> {}\<close> by blast
  show \<open>diameter S = (SUP y \<in> S. dist x y)\<close>
  proof (rule order_antisym)
    from diameter_bounded_bound[OF \<open>bounded S\<close> \<open>x \<in> S\<close>]
    have \<open>y \<in> S \<Longrightarrow> dist x y \<le> diameter S\<close> for y .
    thus \<open>(SUP y \<in> S. dist x y) \<le> diameter S\<close>
      by (rule cSUP_least[OF \<open>S \<noteq> {}\<close>])
  next
    have \<open>bdd_above (dist x ` S)\<close>
      by (meson bdd_above.I2 bounded_any_center \<open>bounded S\<close>)
    have \<open>y \<in> S \<Longrightarrow> z \<in> S \<Longrightarrow> dist y z \<le> max (dist x y) (dist x z)\<close> for y z
      by (metis dist_commute ultrametric_dist_triangle)
    also have \<open>y \<in> S \<Longrightarrow> z \<in> S \<Longrightarrow>
               max (dist x y) (dist x z) \<le> (SUP y \<in> S. dist x y)\<close> for y z
      by (cases \<open>dist x y \<le> dist x z\<close>)
        (simp_all add: cSUP_upper2[OF \<open>bdd_above (dist x ` S)\<close>])
    finally have * : \<open>y \<in> S \<Longrightarrow> z \<in> S \<Longrightarrow> dist y z \<le> (SUP y \<in> S. dist x y)\<close> for y z .
    have \<open>(SUP (y, z) \<in> S \<times> S. dist y z) \<le> (SUP y \<in> S. dist x y)\<close>
      by (rule cSUP_least) (use "*" in \<open>auto simp add: \<open>S \<noteq> {}\<close>\<close>)
    thus \<open>diameter S \<le> Sup (dist x ` S)\<close>
      by (simp add: diameter_def \<open>S \<noteq> {}\<close>)
  qed
qed



subsection \<open>Totally disconnected\<close>

lemma ultrametric_totally_disconnected :
  \<open>\<exists>x. S = {x}\<close> if \<open>S \<noteq> {}\<close> \<open>connected S\<close>
for S :: \<open>'a :: ultrametric_space set\<close>
proof -
  from \<open>S \<noteq> {}\<close> obtain x where \<open>x \<in> S\<close> by blast
  have \<open>ball x r \<inter> S = {} \<or> - ball x r \<inter> S = {}\<close> if \<open>0 < r\<close> for r
    by (rule \<open>connected S\<close>[unfolded connected_def, simplified, rule_format])
      (simp_all, use order_less_imp_le that ultrametric_closed_ball in blast)
  with \<open>x \<in> S\<close> have \<open>0 < r \<Longrightarrow> - ball x r \<inter> S = {}\<close> for r
    by (metis centre_in_ball disjoint_iff)
  hence \<open>0 < r \<Longrightarrow> y \<in> S \<Longrightarrow> dist x y < r\<close> for r y
    by (auto simp add: disjoint_iff)
  hence \<open>y \<in> S \<Longrightarrow> dist x y = 0\<close> for y
    by (metis dist_self order_less_irrefl zero_less_dist_iff)
  hence \<open>y \<in> S \<Longrightarrow> y = x\<close> for y by simp
  with \<open>x \<in> S\<close> show \<open>\<exists>x. S = {x}\<close> by blast
qed



(*<*)
end
  (*>*)