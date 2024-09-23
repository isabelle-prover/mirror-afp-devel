section \<open>Definition of Monotone Algebras and Polynomial Interpretations\<close>

theory Polynomial_Interpretation
  imports 
    Preliminaries_on_Polynomials_1
    First_Order_Terms.Term
    First_Order_Terms.Subterm_and_Context
begin
abbreviation "PVar \<equiv> MPoly_Type.Var" 
abbreviation "TVar \<equiv> Term.Var" 
 
type_synonym ('f,'v)rule = "('f,'v)term \<times> ('f,'v)term" 

text \<open>We fix the domain to the set of nonnegative numbers\<close>

lemma subterm_size[termination_simp]: "x < length ts \<Longrightarrow> size (ts ! x) < Suc (size_list size ts)" 
  by (meson Suc_n_not_le_n less_eq_Suc_le not_less_eq nth_mem size_list_estimation)

definition assignment :: "(var \<Rightarrow> 'a :: {ord,zero}) \<Rightarrow> bool" where
  "assignment \<alpha> = (\<forall> x. \<alpha> x \<ge> 0)"

lemma assignmentD: assumes "assignment \<alpha>" 
  shows "\<alpha> x \<ge> 0" 
  using assms unfolding assignment_def by auto

definition monotone_fun_wrt :: "('a :: {zero,ord} \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a) \<Rightarrow> bool" where
  "monotone_fun_wrt gt n f = (\<forall> v' i vs. length vs = n \<longrightarrow> (\<forall> v \<in> set vs. v \<ge> 0) 
     \<longrightarrow> i < n \<longrightarrow> gt v' (vs ! i) \<longrightarrow> 
     gt (f (vs [ i := v'])) (f vs))" 

definition valid_fun :: "nat \<Rightarrow> ('a list \<Rightarrow> 'a :: {zero,ord}) \<Rightarrow> bool" where
  "valid_fun n f = (\<forall> vs. length vs = n \<longrightarrow> (\<forall> v \<in> set vs. v \<ge> 0) \<longrightarrow> f vs \<ge> 0)"

definition monotone_poly_wrt :: "('a :: {comm_semiring_1,zero,ord} \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> var set \<Rightarrow> 'a mpoly \<Rightarrow> bool" where
  "monotone_poly_wrt gt V p = (\<forall> \<alpha> x v. assignment \<alpha> \<longrightarrow> x \<in> V \<longrightarrow> gt v (\<alpha> x) \<longrightarrow> 
     gt (insertion (\<alpha>(x := v)) p) (insertion \<alpha> p))" 

definition valid_poly :: "'a :: {ord,comm_semiring_1} mpoly \<Rightarrow> bool" where
  "valid_poly p = (\<forall> \<alpha>. assignment \<alpha> \<longrightarrow> insertion \<alpha> p \<ge> 0)"


locale term_algebra = 
  fixes F :: "('f \<times> nat) set" 
  and I :: "'f \<Rightarrow> ('a :: {ord,zero} list) \<Rightarrow> 'a" 
  and gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

abbreviation monotone_fun where "monotone_fun \<equiv> monotone_fun_wrt gt" 

definition valid_monotone_fun :: "('f \<times> nat) \<Rightarrow> bool" where
  "valid_monotone_fun fn = (\<forall> f n p. fn = (f,n) \<longrightarrow> p = I f
      \<longrightarrow> valid_fun n p \<and> monotone_fun n p)"

definition valid_monotone_inter where "valid_monotone_inter = Ball F valid_monotone_fun" 

definition orient_rule :: "('f,var)rule \<Rightarrow> bool" where
  "orient_rule rule = (case rule of (l,r) \<Rightarrow> (\<forall> \<alpha>. assignment \<alpha> \<longrightarrow> gt (I\<lbrakk>l\<rbrakk>\<alpha>) (I\<lbrakk>r\<rbrakk>\<alpha>)))"
end

locale omega_term_algebra = term_algebra F I "(>) :: int \<Rightarrow> int \<Rightarrow> bool" for F and I :: "'f \<Rightarrow> _" +
  assumes vm_inter: valid_monotone_inter
begin
definition termination_by_interpretation :: "('f,var) rule set \<Rightarrow> bool" where
  "termination_by_interpretation R = (\<forall> (l,r) \<in> R. orient_rule (l,r) \<and> funas_term l \<union> funas_term r \<subseteq> F)"
end

locale poly_inter =
  fixes F :: "('f \<times> nat) set" 
  and   I :: "'f \<Rightarrow> 'a :: linordered_idom mpoly" 
  and   gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open>\<succ>\<close> 50) 
begin

definition I' where "I' f vs = insertion (\<lambda> i. if i < length vs then vs ! i else 0) (I f)" 
sublocale term_algebra F I' gt .

abbreviation monotone_poly where "monotone_poly \<equiv> monotone_poly_wrt gt"

abbreviation weakly_monotone_poly where "weakly_monotone_poly \<equiv> monotone_poly_wrt (\<ge>)" 

definition gt_poly :: "'a mpoly \<Rightarrow> 'a mpoly \<Rightarrow> bool" (infix \<open>\<succ>\<^sub>p\<close> 50) where
  "(p \<succ>\<^sub>p q) = (\<forall> \<alpha>. assignment \<alpha> \<longrightarrow> insertion \<alpha> p \<succ> insertion \<alpha> q)" 

definition valid_monotone_poly :: "('f \<times> nat) \<Rightarrow> bool" where
  "valid_monotone_poly fn = (\<forall> f n p. fn = (f,n) \<longrightarrow> p = I f
      \<longrightarrow> valid_poly p \<and> monotone_poly {..<n} p \<and> vars p = {..<n})"

definition valid_weakly_monotone_poly :: "('f \<times> nat) \<Rightarrow> bool" where
  "valid_weakly_monotone_poly fn = (\<forall> f n p. fn = (f,n) \<longrightarrow> p = I f
      \<longrightarrow> valid_poly p \<and> weakly_monotone_poly {..<n} p \<and> vars p \<subseteq> {..<n})"

definition valid_monotone_poly_inter where "valid_monotone_poly_inter = Ball F valid_monotone_poly" 
definition valid_weakly_monotone_inter where "valid_weakly_monotone_inter = Ball F valid_weakly_monotone_poly" 

fun eval :: "('f,var)term \<Rightarrow> 'a mpoly" where
  "eval (TVar x) = PVar x" 
| "eval (Fun f ts) = substitute (\<lambda> i. if i < length ts then eval (ts ! i) else 0) (I f)" 

lemma I'_is_insertion_eval: "I' \<lbrakk>t\<rbrakk> \<alpha> = insertion \<alpha> (eval t)" 
proof (induct t)
  case (Var x)
  then show ?case by (simp add: insertion_Var)
next
  case (Fun f ts)
  then show ?case 
    apply (simp add: insertion_substitute I'_def[of f])
    apply (intro arg_cong[of _ _ "\<lambda> \<alpha>. insertion \<alpha> (I f)"] ext)
    subgoal for i by (cases "i < length ts", auto)
    done
qed

lemma orient_rule: "orient_rule (l,r) = (eval l \<succ>\<^sub>p eval r)" 
  unfolding orient_rule_def split I'_is_insertion_eval gt_poly_def ..

lemma vars_eval: "vars (eval t) \<subseteq> vars_term t" 
proof (induct t)
  case (Fun f ts)
  define V where "V = vars_term (Fun f ts)" 
  define \<sigma> where "\<sigma> = (\<lambda>i. if i < length ts then eval (ts ! i) else 0)" 
  {
    fix i  
    have IH: "vars (\<sigma> i) \<subseteq> V" 
    proof (cases "i < length ts")
      case False
      thus ?thesis unfolding \<sigma>_def by auto
    next
      case True
      hence "ts ! i \<in> set ts" by auto
      with Fun(1)[OF this] have "vars (eval (ts ! i)) \<subseteq> V" by (auto simp: V_def)
      thus ?thesis unfolding \<sigma>_def using True by auto
    qed
  } note \<sigma>_vars = this
  define p where "p = (I f)" 
  show ?case unfolding eval.simps \<sigma>_def[symmetric] V_def[symmetric] p_def[symmetric] using \<sigma>_vars
    vars_substitute[of \<sigma>] by auto
qed auto

lemma monotone_imp_weakly_monotone: assumes valid: "valid_monotone_poly p"
  and gt: "\<And> x y. (x \<succ> y) = (x > y)" 
  shows "valid_weakly_monotone_poly p" 
  unfolding valid_weakly_monotone_poly_def
proof (intro allI impI, clarify, intro conjI)
  fix f n
  assume "p = (f,n)" 
  note * = valid[unfolded valid_monotone_poly_def, rule_format, OF this refl]
  from * show "valid_poly (I f)" by auto
  from * show "vars (I f) \<subseteq> {..<n}" by auto
  show "weakly_monotone_poly {..<n} (I f)" 
    unfolding monotone_poly_wrt_def
  proof (intro allI impI, goal_cases)
    case (1 \<alpha> x a)
    from * have "monotone_poly {..<n} (I f)" by auto
    from this[unfolded monotone_poly_wrt_def, rule_format, OF 1(1-2), of a]
    show ?case unfolding gt using 1(3) by force
  qed
qed

lemma valid_imp_insertion_eval_pos: assumes valid: valid_monotone_poly_inter 
  and "funas_term t \<subseteq> F"
  and "assignment \<alpha>" 
shows "insertion \<alpha> (eval t) \<ge> 0"  
  using assms(2-3)
proof (induct t arbitrary: \<alpha>)
  case (Var x)
  thus ?case by (auto simp: assignment_def insertion_Var)
next
  case (Fun f ts)
  let ?n = "length ts" 
  let ?f = "(f,?n)"
  let ?p = "I f" 
  from Fun have "?f \<in> F" by auto
  from valid[unfolded valid_monotone_poly_inter_def, rule_format, OF this, unfolded valid_monotone_poly_def]
  have valid: "valid_poly ?p" and "vars ?p = {..<?n}" by auto
  from valid[unfolded valid_poly_def]
  have ins: "assignment \<alpha> \<Longrightarrow> 0 \<le> insertion \<alpha> (I f)" for \<alpha> by auto
  {
    fix i
    assume "i < ?n" 
    hence "ts ! i \<in> set ts" by auto
    with Fun(1)[OF this _ Fun(3)] Fun(2) have "0 \<le> insertion \<alpha> (eval (ts ! i))" by auto
  }
  note IH = this
  show ?case 
    apply (simp add: insertion_substitute)
    apply (intro ins, unfold assignment_def, intro allI)
    subgoal for i using IH[of i] by auto
    done
qed

end

locale delta_poly_inter = poly_inter F I "(\<lambda> x y. x \<ge> y + \<delta>)" for F :: "('f \<times> nat) set" and I and 
  \<delta> :: "'a :: {floor_ceiling,linordered_field}" +
  assumes valid: valid_monotone_poly_inter 
  and \<delta>0: "\<delta> > 0" 
begin
definition termination_by_delta_interpretation :: "('f,var) rule set \<Rightarrow> bool" where
  "termination_by_delta_interpretation R = (\<forall> (l,r) \<in> R. orient_rule (l,r) \<and> funas_term l \<union> funas_term r \<subseteq> F)"
end

locale int_poly_inter = poly_inter F I "(>) :: int \<Rightarrow> int \<Rightarrow> bool" for F :: "('f \<times> nat) set" and I +
  assumes valid: valid_monotone_poly_inter 
begin

sublocale omega_term_algebra F I'
proof (unfold_locales, unfold valid_monotone_inter_def, intro ballI)
  fix fn
  assume "fn \<in> F" 
  from valid[unfolded valid_monotone_poly_inter_def, rule_format, OF this]
  have valid: "valid_monotone_poly fn" .
  show "valid_monotone_fun fn" unfolding valid_monotone_fun_def
  proof (intro allI impI conjI)
    fix f n p
    assume fn: "fn = (f,n)" and p: "p = I' f" 
    from valid[unfolded valid_monotone_poly_def, rule_format, OF fn refl]
    have valid: "valid_poly (I f)" and mono: "monotone_poly {..<n} (I f)" by auto
    
    show "valid_fun n p" unfolding valid_fun_def
    proof (intro allI impI)
      fix vs
      assume "length vs = n" and vs: "Ball (set vs) ((\<le>) (0 :: int))" 
      show "0 \<le> p vs" unfolding p I'_def 
        by (rule valid[unfolded valid_poly_def, rule_format], insert vs, auto simp: assignment_def)
    qed

    show "monotone_fun n p" unfolding monotone_fun_wrt_def
    proof (intro allI impI)
      fix v' i vs
      assume *: "length vs = n" "Ball (set vs) ((\<le>) (0 :: int))" "i < n" "vs ! i < v'" 
      show "p vs < p (vs[i := v'])" unfolding p I'_def 
        by (rule ord_less_eq_trans[OF mono[unfolded monotone_poly_wrt_def, rule_format, of _ i v'] 
            insertion_irrelevant_vars], insert *, auto simp: assignment_def)
    qed
  qed
qed

  
definition termination_by_poly_interpretation :: "('f,var) rule set \<Rightarrow> bool" where
  "termination_by_poly_interpretation = termination_by_interpretation"
end

locale wm_int_poly_inter = poly_inter F I "(>) :: int \<Rightarrow> int \<Rightarrow> bool" for F :: "('f \<times> nat) set" and I +
  assumes valid: valid_weakly_monotone_inter 
begin
definition oriented_by_interpretation :: "('f,var) rule set \<Rightarrow> bool" where
  "oriented_by_interpretation R = (\<forall> (l,r) \<in> R. orient_rule (l,r) \<and> funas_term l \<union> funas_term r \<subseteq> F)"
end

locale linear_poly_inter = poly_inter F I gt for F I gt + 
  assumes linear: "\<And> f n. (f,n) \<in> F \<Longrightarrow> total_degree (I f) \<le> 1" 

locale linear_int_poly_inter = int_poly_inter F I + linear_poly_inter F I "(>)"
  for F :: "('f \<times> nat) set" and I

locale linear_wm_int_poly_inter = wm_int_poly_inter F I + linear_poly_inter F I "(>)"
  for F :: "('f \<times> nat) set" and I

definition termination_by_linear_int_poly_interpretation :: "('f \<times> nat)set \<Rightarrow> ('f,var)rule set \<Rightarrow> bool" where
  "termination_by_linear_int_poly_interpretation F R = (\<exists> I. linear_int_poly_inter F I \<and> 
     int_poly_inter.termination_by_poly_interpretation F I R)" 

definition omega_termination :: "('f \<times> nat)set \<Rightarrow> ('f,var)rule set \<Rightarrow> bool" where
  "omega_termination F R = (\<exists> I. omega_term_algebra F I \<and> 
     omega_term_algebra.termination_by_interpretation F I R)" 

definition termination_by_int_poly_interpretation :: "('f \<times> nat)set \<Rightarrow> ('f,var)rule set \<Rightarrow> bool" where
  "termination_by_int_poly_interpretation F R = (\<exists> I. int_poly_inter F I \<and> 
     int_poly_inter.termination_by_poly_interpretation F I R)" 

definition termination_by_delta_poly_interpretation :: "'a :: {floor_ceiling,linordered_field} itself \<Rightarrow> ('f \<times> nat)set \<Rightarrow> ('f,var)rule set \<Rightarrow> bool" where
  "termination_by_delta_poly_interpretation TYPE('a) F R = (\<exists> I \<delta>. delta_poly_inter F I (\<delta> :: 'a) \<and> 
     delta_poly_inter.termination_by_delta_interpretation F I \<delta> R)" 

definition orientation_by_linear_wm_int_poly_interpretation :: "('f \<times> nat)set \<Rightarrow> ('f,var)rule set \<Rightarrow> bool" where
  "orientation_by_linear_wm_int_poly_interpretation F R = (\<exists> I. linear_wm_int_poly_inter F I \<and> 
     wm_int_poly_inter.oriented_by_interpretation F I R)" 

end
