(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Abstract Multivariate Polynomials\<close>

theory Abstract_Multivariate_Polynomials
  imports
    Substitutions
    "HOL-Analysis.Finite_Cartesian_Product"
begin

text \<open>Multivariate polynomials, abstractly\<close>

locale multi_variate_polynomial = 
  fixes vars :: \<open>'p :: comm_monoid_add \<Rightarrow> 'v set\<close>
  and deg :: \<open>'p \<Rightarrow> nat\<close>
  and eval :: \<open>'p \<Rightarrow> ('v, 'a::finite) subst \<Rightarrow> 'b :: comm_monoid_add\<close>
  and inst :: \<open>'p \<Rightarrow> ('v, 'a) subst \<Rightarrow> 'p\<close>
assumes
  \<comment> \<open>vars\<close>
  vars_finite: \<open>finite (vars p)\<close> and 
  vars_zero: \<open>vars 0 = {}\<close> and 
  vars_add: \<open>vars (p + q) \<subseteq> vars p \<union> vars q\<close> and
  vars_inst: \<open>vars (inst p \<sigma>) \<subseteq> vars p - dom \<sigma>\<close> and 

  \<comment> \<open>degree\<close>
  deg_zero: \<open>deg 0 = 0\<close> and 
  deg_add: \<open>deg (p + q) \<le> max (deg p) (deg q)\<close> and 
  deg_inst: \<open>deg (inst p \<rho>) \<le> deg p\<close> and 

  \<comment> \<open>eval\<close>
  eval_zero: \<open>eval 0 \<sigma> = 0\<close> and
  eval_add: \<open>vars p \<union> vars q \<subseteq> dom \<sigma> \<Longrightarrow> eval (p + q) \<sigma> = eval p \<sigma> + eval q \<sigma>\<close> and
  eval_inst: \<open>vars p \<subseteq> dom \<sigma> \<union> dom \<rho> \<Longrightarrow> eval (inst p \<sigma>) \<rho> = eval p (\<rho> ++ \<sigma>)\<close> and

  \<comment> \<open>small number of roots (variant for two polynomials)\<close>
  roots: \<open>card {r. deg p \<le> d \<and> vars p \<subseteq> {x} \<and> deg q \<le> d \<and> vars q \<subseteq> {x} \<and> 
                   p \<noteq> q \<and> eval p [x \<mapsto> r] = eval q [x \<mapsto> r]} \<le> d\<close>
begin

lemmas vars_addD = vars_add[THEN subsetD]


subsection \<open>Arity: definition and some lemmas\<close>

definition arity :: \<open>'p \<Rightarrow> nat\<close> where
  \<open>arity p = card (vars p)\<close>

lemma arity_zero: \<open>arity 0 = 0\<close> 
  by (simp add: arity_def vars_zero)

lemma arity_add: \<open>arity (p + q) \<le> arity p + arity q\<close> 
proof - 
  have \<open>card (vars (p + q)) \<le> card (vars p \<union> vars q)\<close> 
    by (intro card_mono) (auto simp add: vars_add vars_finite) 
  also have \<open>... \<le> card (vars p) + card (vars q)\<close> by (simp add: card_Un_le)
  finally show ?thesis by (simp add: arity_def)
qed

lemma arity_inst: 
  assumes \<open>dom \<sigma> \<subseteq> vars p\<close> 
  shows \<open>arity (inst p \<sigma>) \<le> arity p - card (dom \<sigma>)\<close>
proof -
  have \<open>card (vars (inst p \<sigma>)) \<le> card (vars p - dom \<sigma>)\<close>
    by (auto simp add: vars_finite vars_inst card_mono)
  also have \<open>\<dots> = card (vars p) - card (dom \<sigma>)\<close> using assms 
    by (simp add: card_Diff_subset finite_subset vars_finite)
  finally show ?thesis by (simp add: arity_def)
qed

subsection \<open>Lemmas about evaluation, degree, and variables of finite sums\<close>

lemma eval_sum: 
  assumes \<open>finite I\<close> \<open>\<And>i. i \<in> I \<Longrightarrow> vars (pp i) \<subseteq> dom \<sigma>\<close>
  shows \<open>eval (\<Sum>i\<in>I. pp i) \<sigma> = (\<Sum>i\<in>I. eval (pp i) \<sigma>)\<close>
proof - 
  have \<open>eval (\<Sum>i\<in>I. pp i) \<sigma> = (\<Sum>i\<in>I. eval (pp i) \<sigma>) \<and> vars (\<Sum>i\<in>I. pp i) \<subseteq> dom \<sigma>\<close> using assms
  proof (induction rule: finite.induct)
    case emptyI
    then show ?case by (simp add: eval_zero vars_zero)
  next
    case (insertI A a)
    then show ?case 
      by (auto simp add: eval_add vars_add sum.insert_if dest!: vars_addD)
  qed
  then show ?thesis ..
qed

lemma vars_sum: 
  assumes \<open>finite I\<close>  
  shows \<open>vars (\<Sum>i\<in>I. pp i) \<subseteq> (\<Union>i\<in>I. vars (pp i))\<close>
  using assms
proof (induction rule: finite.induct)
  case emptyI
  then show ?case by(auto simp add: vars_zero)
next
  case (insertI A a)
  then show ?case using insertI by(auto simp add: sum.insert_if dest: vars_addD)
qed

lemma deg_sum:
  assumes \<open>finite I\<close>  and "I \<noteq> {}"
  shows \<open>deg (\<Sum>i\<in>I. pp i) \<le> Max {deg (pp i) | i. i \<in> I}\<close> 
  using assms 
proof (induction rule: finite.induct)
  case emptyI
  then show ?case by(auto simp add: deg_zero)
next
  case (insertI A a)
  show ?case 
  proof(cases "A = {}")
    assume \<open>A = {}\<close>
    then show ?thesis by(simp)
  next
    assume \<open>A \<noteq> {}\<close>
    then have *: \<open>Max {deg (pp i) |i. i \<in> A} \<le> Max {deg (pp i) |i. i = a \<or> i \<in> A}\<close> using \<open>finite A\<close>
      by (intro Max_mono) auto
    show ?thesis using insertI \<open>A \<noteq> {}\<close> 
      by (auto 4 4 simp add: sum.insert_if intro: Max_ge *[THEN [2] le_trans] deg_add[THEN le_trans])
  qed
qed
     
subsection \<open>Lemmas combining eval, sum, and inst\<close>

lemma eval_sum_inst: 
  assumes \<open>vars p \<subseteq> V \<union> dom \<rho>\<close> \<open>finite V\<close>
  shows \<open>eval (\<Sum>\<sigma> \<in> substs V H. inst p \<sigma>) \<rho> = (\<Sum>\<sigma> \<in> substs V H. eval p (\<rho> ++ \<sigma>))\<close> 
proof - 
  have A1: \<open>\<And>\<sigma>. \<sigma> \<in> substs V H \<Longrightarrow> vars (inst p \<sigma>) \<subseteq> dom \<rho>\<close> using assms(1) vars_inst by blast
  have A2: \<open>\<And>\<sigma>. \<sigma> \<in> substs V H \<Longrightarrow> vars p \<subseteq> dom \<sigma> \<union> dom \<rho>\<close> using assms(1) by (auto)

  have \<open>eval (\<Sum>\<sigma> \<in> substs V H. inst p \<sigma>) \<rho> = (\<Sum>\<sigma>\<in>substs V H. eval (inst p \<sigma>) \<rho>)\<close> using A1 assms(2)
    by (simp add: eval_sum substs_finite)    \<comment> \<open>requires @{term "finite H"}\<close>
  also have \<open>... = (\<Sum>\<sigma> \<in> substs V H. eval p (\<rho> ++ \<sigma>))\<close> using A2 
    by (simp add: eval_inst)
  finally show ?thesis .
qed

lemma  eval_sum_inst_commute:
  assumes \<open>vars p \<subseteq> insert x V\<close> \<open>x \<notin> V\<close> \<open>finite V\<close>
  shows \<open>eval (\<Sum>\<sigma>\<in>substs V H. inst p \<sigma>) [x \<mapsto> r]
         = (\<Sum>\<sigma>\<in>substs V H. eval (inst p [x \<mapsto> r]) \<sigma>)\<close>
proof -
  have \<open>eval (sum (inst p) (substs V H)) [x \<mapsto> r] = 
        (\<Sum>\<sigma>\<in>substs V H. eval p ([x \<mapsto> r] ++ \<sigma>))\<close> using \<open>vars p \<subseteq> insert x V\<close> \<open>finite V\<close>
    by (simp add: eval_sum_inst)
  also have \<open>... = (\<Sum>\<sigma>\<in>substs V H. eval p (\<sigma>(x \<mapsto> r)))\<close> using \<open>x \<notin> V\<close>
    by (intro Finite_Cartesian_Product.sum_cong_aux) 
       (auto simp add: map_add_comm subst_dom)
  also have \<open>... = (\<Sum>\<sigma>\<in>substs V H. eval (inst p [x \<mapsto> r]) \<sigma>)\<close> using \<open>vars p \<subseteq> insert x V\<close>
    by (intro Finite_Cartesian_Product.sum_cong_aux)
       (auto simp add: eval_inst)
  finally show ?thesis .
qed

subsection \<open>Merging sums over substitutions\<close>

lemma sum_merge:
  assumes \<open>x \<notin> V\<close>   
  shows "(\<Sum>h\<in>H. (\<Sum>\<sigma> \<in> substs V H. eval p ([x \<mapsto> h] ++ \<sigma>)))
          = (\<Sum>\<sigma>\<in>substs (insert x V) H. eval p \<sigma>)"
proof -
  have  "\<And>h \<sigma>. (h,\<sigma>) \<in> H \<times> substs V H \<Longrightarrow> dom [x \<mapsto> h] \<inter> dom \<sigma> = {}" using \<open>x \<notin> V\<close> 
    by(auto simp add: substs_def)
  then have *: "\<And>h \<sigma>. (h,\<sigma>) \<in> H \<times> substs V H \<Longrightarrow> [x \<mapsto> h] ++ \<sigma> = \<sigma>(x \<mapsto> h)" 
    by(auto simp add: map_add_comm)

  have "(\<Sum>h\<in>H. (\<Sum>\<sigma> \<in> substs V H. eval p ([x \<mapsto> h] ++ \<sigma>))) =
        (\<Sum>(h,\<sigma>) \<in> H \<times> substs V H. eval p ([x \<mapsto> h] ++ \<sigma>))"
    by(auto simp add: sum.cartesian_product)
  also have "\<dots> = (\<Sum>(h,\<sigma>) \<in> H \<times> substs V H. eval p (\<sigma>(x \<mapsto> h)))" using *  
    by (intro Finite_Cartesian_Product.sum_cong_aux) (auto)
  also have "\<dots> =  (\<Sum>\<sigma>\<in>substs (insert x V) H. eval p \<sigma>)" using \<open>x \<notin> V\<close> 
    by(auto simp add: sum.reindex_bij_betw[OF bij_betw_set_substs, 
              where V1 = "insert x V" and x1 = "x" and H1 = "H" and g = "\<lambda>\<sigma>. eval p \<sigma>", symmetric]
            intro: Finite_Cartesian_Product.sum_cong_aux)
  finally show ?thesis .
qed

end

end
