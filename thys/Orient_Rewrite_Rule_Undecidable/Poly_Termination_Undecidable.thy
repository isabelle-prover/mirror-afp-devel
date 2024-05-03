section \<open>Undecidability of Polynomial Termination over Integers\<close>

theory Poly_Termination_Undecidable
  imports 
    Linear_Poly_Termination_Undecidable
    Preliminaries_on_Polynomials_2
begin

context poly_input
begin

definition y4 :: var where "y4 = 3" 
definition y5 :: var where "y5 = 4" 
definition y6 :: var where "y6 = 5" 
definition y7 :: var where "y7 = 6" 

abbreviation q_t where "q_t t \<equiv> Fun q_sym [t]" 
abbreviation h_t where "h_t t \<equiv> Fun h_sym [t]" 
abbreviation g_t where "g_t t1 t2 \<equiv> Fun g_sym [t1, t2]" 

text \<open>Definition 5.1\<close>

definition "lhs_S = Fun f_sym [
  Var y1, 
  Var y2,
  a_t (encode_poly y3 p) (Var y3),
  q_t (h_t (Var y4)),
  h_t (Var y5),
  h_t (Var y6), 
  g_t (Var y7) o_t]"

definition "rhs_S = Fun f_sym [
  a_t (Var y1) z_t,
  a_t z_t (Var y2),
  a_t (encode_poly y3 q) (Var y3),
  h_t (h_t (q_t (Var y4))),
  foldr v_t V_list (a_t (Var y5) (Var y5)),
  Fun f_sym (replicate 7 (Var y6)),
  g_t (Var y7) z_t]"

definition S where "S = {(lhs_S, rhs_S)}" 

definition F_S where "F_S = {(f_sym,7), (h_sym,1), (g_sym,2), (o_sym,0), (q_sym,1)} \<union> F" 

lemma lhs_S_F: "funas_term lhs_S \<subseteq> F_S" 
proof - 
  from funas_encode_poly_p
  show "funas_term lhs_S \<subseteq> F_S" unfolding lhs_S_def by (auto simp: F_S_def F_def)
qed

lemma funas_fold_vs[simp]: "funas_term (foldr v_t V_list t) = (\<lambda> i. (v_sym i,1)) ` V \<union> funas_term t" 
proof -
  have id: "funas_term (foldr v_t xs t) = (\<lambda> i. (v_sym i,1)) ` set xs \<union> funas_term t" for xs
    by (induct xs, auto)
  show ?thesis unfolding id
    by (auto simp: V_list)
qed
  
lemma vars_fold_vs[simp]: "vars_term (foldr v_t vs t) = vars_term t" 
  by (induct vs, auto)

lemma funas_term_r5: "funas_term (foldr v_t V_list (a_t (Var y5) (Var y5))) \<subseteq> F_S" 
  by (auto simp: F_S_def F_def)

lemma rhs_S_F: "funas_term rhs_S \<subseteq> F_S" 
proof - 
  from funas_encode_poly_q funas_term_r5
  show "funas_term rhs_S \<subseteq> F_S" unfolding rhs_S_def by (auto simp: F_S_def F_def)
qed
end

lemma poly_inter_eval_cong: assumes "\<And> f a. (f,a) \<in> funas_term t \<Longrightarrow> I f = I' f" 
  shows "poly_inter.eval I t = poly_inter.eval I' t" 
  using assms
proof (induct t)
  case (Var x)
  show ?case by (simp add: poly_inter.eval.simps) 
next
  case (Fun f ts)
  {
    fix i
    assume "i < length ts" 
    hence "ts ! i \<in> set ts"
      by auto
    with Fun(1)[OF this Fun(2)]
    have "poly_inter.eval I (ts ! i) = poly_inter.eval I' (ts ! i)" by force
  } note IH = this
  from Fun(2) have "I f = I' f" by auto
  thus ?case using IH 
    by (auto simp: poly_inter.eval.simps insertion_substitute intro!: mpoly_extI insertion_irrelevant_vars)
qed


text \<open>The easy direction of Theorem 5.4\<close>

context solvable_poly_problem
begin

definition c_S where "c_S = max 7 (2 * prod_list (map \<alpha> V_list))" 

lemma c_S: "c_S > 0" unfolding c_S_def by auto

fun I_S :: "symbol \<Rightarrow> int mpoly" where 
  "I_S f_sym = PVar 0 + PVar 1 + PVar 2 + PVar 3 + PVar 4 + PVar 5 + PVar 6" 
| "I_S a_sym = PVar 0 + PVar 1"
| "I_S z_sym = 0" 
| "I_S o_sym = 1" 
| "I_S (v_sym i) = Const (\<alpha> i) * PVar 0" 
| "I_S q_sym = mmonom (monomial 2 0) c_S" \<comment> \<open>@{term "c * (PVar 0)^2"}\<close>
| "I_S g_sym = PVar 0 + PVar 1" 
| "I_S h_sym = mmonom (monomial 1 0) c_S" \<comment> \<open>@{term "c * PVar 0"}\<close>

declare single_numeral[simp del] (* this converts monom (monomial 2 0) c to monom 2 c,
  and then certain other rules are no longer applicable *) 
declare insertion_monom[simp del]

interpretation inter_S: poly_inter F_S I_S "(>)" .

lemma inter_S_encode_poly: assumes "positive_poly r" 
  shows "inter_S.eval (encode_poly x r) = Const (insertion \<alpha> r) * PVar x" 
  by (rule inter_encode_poly_generic[OF _ _ _ _ assms], auto)

lemma valid_monotone_inter_S: "inter_S.valid_monotone_poly_inter" 
  unfolding inter_S.valid_monotone_poly_inter_def 
proof (intro ballI)
  fix fn
  assume f: "fn \<in> F_S" 
  show "inter_S.valid_monotone_poly fn"
  proof (cases "fn \<in> F")
    case True
    show "inter_S.valid_monotone_poly fn" 
      by (rule valid_monotone_inter_F[OF _ _ _ _ \<alpha>(1) True], auto)
  next
    case False
    with f have f: "fn \<in> F_S - F" by auto
    have [simp]: "vars ((PVar 0 :: int mpoly) + PVar (Suc 0) + PVar 2 + PVar 3 + PVar 4 + PVar 5 + PVar 6) = {0,1,2,3,4,5,6}" 
      unfolding vars_def apply (transfer', simp add: Var\<^sub>0_def image_comp) by code_simp
    have [simp]: "vars ((PVar 0 :: int mpoly) + PVar (Suc 0)) = {0,1}" 
      unfolding vars_def apply (transfer', simp add: Var\<^sub>0_def image_comp) by code_simp
    show ?thesis unfolding inter_S.valid_monotone_poly_def using f
    proof (intro ballI impI allI, clarify, intro conjI) 
      fix f n
      assume f: "(f,n) \<in> F_S" "(f,n) \<notin> F" 
      from f show "vars (I_S f) = {..< n}" unfolding F_S_def using c_S
        by (auto simp: vars_monom_single_cases)
      from f c_S show "valid_poly (I_S f)" unfolding F_S_def
        by (auto simp: valid_poly_def insertion_add assignment_def)
      have x2: "x < 2 \<Longrightarrow> x = 0 \<or> x = Suc 0" for x by linarith
      have x7: "x < 7 \<Longrightarrow> x = 0 \<or> x = Suc 0 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 \<or> x = 6" for x by linarith
      from f c_S show "inter_S.monotone_poly {..<n} (I_S f)" unfolding F_S_def
        by (auto simp: monotone_poly_wrt_def insertion_add assignment_def power_strict_mono
            dest: x2 x7)
    qed
  qed
qed

interpretation inter_S: int_poly_inter F_S I_S
proof 
  show inter_S.valid_monotone_poly_inter by (rule valid_monotone_inter_S)
qed

lemma orient_trs: "inter_S.termination_by_poly_interpretation S" 
  unfolding inter_S.termination_by_poly_interpretation_def 
    inter_S.termination_by_interpretation_def S_def inter_S.orient_rule
proof (clarify, intro conjI)
  have lhs_S: "inter_S.eval lhs_S = 
     (PVar y1 + 
     PVar y2 + 
     (Const (insertion \<alpha> p) + 1) * PVar y3 +  
     (Const c_S)^3 * (PVar y4)^2 + 
     Const c_S * PVar y5 + 
     Const c_S * PVar y6 + 
     PVar y7) + 
     1" 
    unfolding lhs_S_def by (simp add: inter_S_encode_poly[OF pq(1)] 
        power2_eq_square power3_eq_cube algebra_simps)
  have foldr: "inter_S.eval (foldr (\<lambda>i t. Fun (v_sym i) [t]) V_list (Fun a_sym [TVar y5, TVar y5])) = 
    Const (prod_list (map \<alpha> V_list)) * 2 * PVar y5" 
    by (subst inter_foldr_v_t, auto)
  have rhs_S: "inter_S.eval rhs_S = 
     (PVar y1 + 
     PVar y2 + 
     (Const (insertion \<alpha> q) + 1) * PVar y3 +
     (Const c_S)^3 * (PVar y4)\<^sup>2 +
     Const (prod_list (map \<alpha> V_list)) * 2 * PVar y5 +
     7 * PVar y6 +
     PVar y7) + 
     0" 
    unfolding rhs_S_def by (simp add: inter_S_encode_poly[OF pq(2)] Const_add 
        power2_eq_square power3_eq_cube algebra_simps foldr)
  show "inter_S.gt_poly (inter_S.eval lhs_S) (inter_S.eval rhs_S)" 
    unfolding inter_S.gt_poly_def
  proof (intro allI impI)
    fix \<beta> :: "var \<Rightarrow> int" 
    assume ass: "assignment \<beta>"
    hence \<beta>: "\<And> x. \<beta> x \<ge> 0" unfolding assignment_def by auto
    have \<alpha>0: "\<alpha> x \<ge> 0" for x using \<alpha>(1)[unfolded positive_interpr_def, rule_format, of x] by auto
    from c_S have c0: "c_S \<ge> 0" by simp
    have 7: "7 = (Const 7 :: int mpoly)" by code_simp 
    have 2: "2 = (Const 2 :: int mpoly)" by code_simp 
    have ins7: "insertion \<beta> 7 = (7 :: int)" unfolding 7 insertion_Const by simp
    have ins2: "insertion \<beta> 2 = (2 :: int)" unfolding 2 insertion_Const by simp
    show "insertion \<beta> (inter_S.eval lhs_S) > insertion \<beta> (inter_S.eval rhs_S)"
      unfolding lhs_S rhs_S insertion_add ins7 ins2 insertion_mult insertion_Var insertion_Const insertion_Const insertion_power
    proof (intro add_le_less_mono add_mono mult_mono add_nonneg_nonneg zero_le_power \<alpha>(2) \<beta> c0)
      show "0 \<le> insertion \<alpha> p" by (intro insertion_positive_poly[OF \<alpha>0 pq(1)])
      show "7 \<le> c_S" unfolding c_S_def by auto
      show "prod_list (map \<alpha> V_list) * 2 \<le> c_S" unfolding c_S_def by simp
    qed (force+)
  qed
qed (insert lhs_S_F rhs_S_F, auto)

lemma solution_imp_poly_termination: "termination_by_int_poly_interpretation F_S S" 
  unfolding termination_by_int_poly_interpretation_def
  by (intro exI, rule conjI[OF _ orient_trs], unfold_locales)

end

text \<open>Towards Lemma 5.2\<close>

(* we do not need the interpretation of int_poly_inter, but just the int-monotonicity definition *)
lemma (in int_poly_inter) monotone_imp_weakly_monotone: assumes "monotone_poly xs p"
  shows "weakly_monotone_poly xs p" 
  unfolding monotone_poly_wrt_def
proof (intro allI impI)
  fix \<alpha> :: "var \<Rightarrow> int" and x v
  assume "assignment \<alpha>" "x \<in> xs" "\<alpha> x \<le> v" 
  from assms[unfolded monotone_poly_wrt_def, rule_format, OF this(1-2), of v] this(3)
  show "insertion \<alpha> p \<le> insertion (\<alpha>(x := v)) p" 
    by (cases "\<alpha> x < v", auto)
qed

context 
  fixes gt :: "'a :: linordered_idom \<Rightarrow> 'a \<Rightarrow> bool"
  assumes trans_gt: "transp gt" 
  and gt_imp_ge: "\<And> x y. gt x y \<Longrightarrow> x \<ge> y" 
begin

lemma monotone_poly_wrt_insertion_main: assumes "monotone_poly_wrt gt xs p"
  and a: "assignment (a :: var \<Rightarrow> 'a :: linordered_idom)" 
  and b: "\<And> x. x \<in> xs \<Longrightarrow> gt\<^sup>=\<^sup>= (b x) (a x)"
         "\<And> x. x \<notin> xs \<Longrightarrow> a x = b x" 
  shows "gt\<^sup>=\<^sup>= (insertion b p) (insertion a p)" 
proof -
  from sorted_list_of_set(1)[OF vars_finite[of p]] sorted_list_of_set[of "vars p"] obtain ys where 
    ysp: "set ys = vars p" and dist: "distinct ys" by auto
  define c where "c ys = (\<lambda> x. if x \<in> set ys then a x else b x)" for ys
  have ass: "assignment (c ys)" for ys unfolding assignment_def 
  proof
    fix x
    show "0 \<le> c ys x" using b[of x] a[unfolded assignment_def, rule_format, of x] gt_imp_ge[of "b x" "a x"]
      unfolding c_def by auto linarith
  qed
  have id: "insertion a p = insertion (c ys) p" unfolding c_def ysp
    by (rule insertion_irrelevant_vars, auto)
  also have "gt^== (insertion b p) (insertion (c ys) p)" using dist
  proof (induct ys)
    case Nil
    show ?case unfolding c_def by auto
  next
    case (Cons x ys)
    show ?case
    proof (cases "x \<in> xs")
      case False
      from b(2)[OF this] have "c (Cons x ys) = c ys" 
        unfolding c_def by auto
      thus ?thesis using Cons by auto
    next
      case True
      from b(1)[OF this] have ab: "gt^== (b x) (a x)" by auto
      let ?c = "c (Cons x ys)" 
      have id1: "c ys = ?c(x := b x)" 
        using Cons(2) unfolding c_def by auto
      have id2: "c (x # ys) x = a x" using True unfolding c_def by auto
      have IH: "gt^== (insertion b p) (insertion (c ys) p)" using Cons by auto
      have "gt^== (insertion (?c(x := b x)) p) (insertion ?c p)" 
      proof (cases "b x = a x")
        case True
        hence "?c(x := b x) = ?c" using id1 id2
          by (intro ext, auto)
        thus ?thesis by simp
      next
        case False
        with ab have ab: "gt (b x) (a x)" by auto
        have "gt(insertion (?c(x := b x)) p) (insertion ?c p)" 
        proof (rule assms(1)[unfolded monotone_poly_wrt_def, rule_format, OF ass True])
          show "gt (b x) (c (x # ys) x)" unfolding id2 by fact
        qed
        thus ?thesis by auto
      qed
      also have "insertion (?c(x := b x)) p = insertion (c ys) p" unfolding id1 ..
      finally have "gt^== (insertion (c ys) p) (insertion (c (x # ys)) p)" .
      from transpE[OF trans_gt] IH this
      show ?thesis by auto
    qed
  qed
  finally show ?thesis .   
qed

lemma monotone_poly_wrt_insertion: assumes "monotone_poly_wrt gt (vars p) p"
  and a: "assignment (a :: var \<Rightarrow> 'a :: linordered_idom)" 
  and b: "\<And> x. x \<in> vars p \<Longrightarrow> gt\<^sup>=\<^sup>= (b x) (a x)"
shows "gt\<^sup>=\<^sup>= (insertion b p) (insertion a p)" 
proof -
  define b' where "b' x = (if x \<in> vars p then b x else a x)" for x
  have "gt^== (insertion b' p) (insertion a p)" 
    by (rule monotone_poly_wrt_insertion_main[OF assms(1-2)], insert b, auto simp: b'_def)
  also have "insertion b' p = insertion b p" 
    by (rule insertion_irrelevant_vars, auto simp: b'_def)
  finally show ?thesis .
qed

lemma partial_insertion_mono_wrt: assumes mono: "monotone_poly_wrt gt (vars p) p"
  and a: "assignment a" 
  and b: "\<And> y. y \<noteq> x \<Longrightarrow> gt\<^sup>=\<^sup>= (b y) (a y)" 
  and d: "\<And> y. y \<ge> d \<Longrightarrow> gt\<^sup>=\<^sup>= y 0" 
  shows "\<exists> c. \<forall> y. y \<ge> d \<longrightarrow> c \<le> poly (partial_insertion a x p) y 
     \<and> poly (partial_insertion a x p) y \<le> poly (partial_insertion b x p) y" 
proof -
  define pa where "pa = partial_insertion a x p" 
  define pb where "pb = partial_insertion b x p" 
  define c where "c = insertion (a(x := 0)) p" 
  {
    fix y :: 'a
    assume y: "y \<ge> d" 
    with d have gty: "gt\<^sup>=\<^sup>= y 0" by auto
    from a have ass: "assignment (a(x := 0))" unfolding assignment_def by auto
    from monotone_poly_wrt_insertion[OF mono ass, of "a(x := y)"]
    have "gt\<^sup>=\<^sup>= (insertion (a(x := y)) p) (insertion (a(x := 0)) p)" using gty by auto
    from this[folded c_def] gt_imp_ge[of _ c]
    have "c \<le> insertion (a(x := y)) p" by auto
  } note le_c = this
  {
    fix y :: 'a
    assume y: "y \<ge> d" 
    with d have gty: "gt\<^sup>=\<^sup>= y 0" by auto
    from y a gty gt_imp_ge[of y] have ass: "assignment (a(x := y))" unfolding assignment_def by auto
    from monotone_poly_wrt_insertion[OF mono this, of "b(x := y)"]
    have "gt\<^sup>=\<^sup>= (insertion (b(x := y)) p) (insertion (a(x := y)) p)" 
      using b by auto
    with gt_imp_ge
    have "insertion (a(x := y)) p \<le> insertion (b(x := y)) p" by auto
  } note le_ab = this
  have id: "poly (partial_insertion a x p) y = insertion (a(x := y)) p" for a  y
    using insertion_partial_insertion[of x a "a(x := y)" p] by auto
  {
    fix y :: 'a
    assume y: "y \<ge> d"
    from le_ab[OF y, folded id, folded pa_def pb_def]
    have "poly pa y \<le> poly pb y" by auto
  } note le1 = this
  show ?thesis
  proof (intro exI[of _ c], intro allI impI conjI le1[unfolded pa_def pb_def])
    fix y :: 'a
    assume y: "y \<ge> d" 
    show "c \<le> poly (partial_insertion a x p) y" using le_c[OF y] unfolding id .
  qed
qed

context
  assumes poly_pinfty_ge: "\<And> p b. 0 < lead_coeff (p :: 'a poly) \<Longrightarrow> degree p \<noteq> 0 \<Longrightarrow> \<exists>n. \<forall>x\<ge>n. b \<le> poly p x"
begin

context 
  fixes p d
  assumes mono: "monotone_poly_wrt gt (vars p) p" 
  and d: "\<And> y. y \<ge> d \<Longrightarrow> gt\<^sup>=\<^sup>= y 0" 
begin

lemma degree_partial_insertion_mono_generic: assumes 
      a: "assignment a" 
  and b: "\<And> y. y \<noteq> x \<Longrightarrow> gt\<^sup>=\<^sup>= (b y) (a y)" 
  shows "degree (partial_insertion a x p) \<le> degree (partial_insertion b x p)" 
proof -
  define qa where "qa = partial_insertion a x p" 
  define qb where "qb = partial_insertion b x p" 
  from partial_insertion_mono_wrt[OF mono a b d, of x d]
  obtain c where c: "\<And> y. y \<ge> d \<Longrightarrow> c \<le> poly qa y" 
    and ab: "\<And> y. y \<ge> d \<Longrightarrow> poly qa y \<le> poly qb y" 
    by (auto simp: qa_def qb_def)
  show ?thesis
  proof (cases "degree qa = 0")
    case True
    thus ?thesis unfolding qa_def by auto
  next
    case False
    let ?lc = lead_coeff
    have lc_pos: "?lc qa > 0" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      with False have "?lc qa < 0" using leading_coeff_neq_0 by force
      hence "?lc (-qa) > 0" by simp
      from poly_pinfty_ge[OF this, of "- c + 2"] False
      obtain n where le: "\<And> x. x \<ge> n \<Longrightarrow> - c + 2 \<le> - poly qa x" by auto
      from le[of "max n d"] c[of "max n d"] show False by auto
    qed
    from this ab have "degree qa \<le> degree qb" by (intro degree_mono_generic[OF poly_pinfty_ge], auto)
    thus ?thesis unfolding qa_def qb_def by auto
  qed
qed

lemma degree_partial_insertion_stays_constant_generic:  
  "\<exists> a. assignment a \<and> 
  (\<forall> b. (\<forall> y. gt\<^sup>=\<^sup>= (b y) (a y)) \<longrightarrow> degree (partial_insertion a x p) = degree (partial_insertion b x p))" 
proof - 
  define n where "n = mdegree p x" 
  define pi where "pi a = partial_insertion a x p" for a
  have n: "assignment a \<Longrightarrow> degree (pi a) \<le> n" for a unfolding n_def pi_def
    by (rule degree_partial_insertion_bound)
  thus ?thesis unfolding pi_def[symmetric]
  proof (induct n rule: less_induct)
    case (less n)
    show ?case
    proof (cases "\<exists> a. assignment a \<and> degree (pi a) = n")
      case True
      then obtain a where a: "assignment a" and deg: "degree (pi a) = n" by auto
      show ?thesis 
      proof (intro exI[of _ a] conjI a allI impI)
        fix b
        assume ge: "\<forall>y. gt\<^sup>=\<^sup>= (b y) (a y)" 
        with a gt_imp_ge[of "b y" "a y" for y] have b: "assignment b" unfolding assignment_def
          using order_trans[of 0 "a y" for y] by fastforce
        have "degree (pi a) \<le> degree (pi b)" 
          by (rule degree_partial_insertion_mono_generic[OF a, of x b, folded pi_def], insert ge, auto)
        with less(2)[of b] deg b
        show "degree (pi a) = degree (pi b)" by simp
      qed
    next
      case False
      with less(2) have deg: "assignment b \<Longrightarrow> degree (pi b) < n" for b by fastforce
      have ass: "assignment (\<lambda> _. 0 :: 'a)" unfolding assignment_def by auto
      define m where "m = n - 1" 
      from deg[OF ass] have mn: "m < n" and less_id: "x < n \<longleftrightarrow> x \<le> m" for x unfolding m_def by auto      
      from less(1)[OF mn deg[unfolded less_id]] show ?thesis by auto
    qed
  qed
qed
end

lemma monotone_poly_partial_insertion_generic: 
  assumes delta_order: "\<And> x y. gt y x \<longleftrightarrow> y \<ge> x + \<delta>" 
    and delta: "\<delta> > 0" 
    and eps_delta: "\<epsilon> * \<delta> \<ge> 1" 
    and ceil_nat: "\<And> x :: 'a. of_nat (ceil_nat x) \<ge> x" 
  assumes x: "x \<in> xs" 
  and mono: "monotone_poly_wrt gt xs p"
  and ass: "assignment a" 
shows "0 < degree (partial_insertion a x p)" 
   "lead_coeff (partial_insertion a x p) > 0"
   "valid_poly p \<Longrightarrow> poly (partial_insertion a x p) (\<delta> * of_nat y) \<ge> \<delta> * of_nat y" 
proof -
  define q where "q = partial_insertion a x p" 
  {
    fix w1 w2:: 'a
    assume w: "0 \<le> w1" "gt w2 w1" 
    from gt_imp_ge[OF w(2)] w have w2: "w2 \<ge> 0" by auto
    have assw: "assignment (a (x := w1))" using ass w(1) w2 unfolding assignment_def by auto
    note main = insertion_partial_insertion[of x _ _ p, symmetric]
    have "gt (insertion (a(x := w2)) p) (insertion (a(x := w1)) p)"
      using mono[unfolded monotone_poly_wrt_def, rule_format, OF assw x, of w2] by (auto simp: w)
    also have "insertion (a(x := w2)) p = poly (partial_insertion a x p) w2" using main[of a "a(x := w2)"] by auto
    also have "insertion (a(x := w1)) p = poly (partial_insertion a x p) w1" using main[of a "a(x := w1)"] by auto
    finally have "gt (poly q w2) (poly q w1)" by (auto simp: q_def)
  } note gt = this
  have "0 \<le> a x" using ass unfolding assignment_def by auto
  from gt[OF this, of "a x + \<delta>"] have "poly q (a x) \<noteq> poly q (a x + \<delta>)" unfolding delta_order using delta by auto
  hence deg: "degree q > 0" 
    using degree0_coeffs[of q] by force
  show "0 < degree (partial_insertion a x p)" unfolding q_def[symmetric] by fact

  have unbounded: "poly q (\<delta> * of_nat n) \<ge> poly q 0 + \<delta> * of_nat n" for n
  proof (induct n)
    case (Suc n)
    have "poly q 0 + \<delta> * of_nat (Suc n) = (poly q 0 + \<delta> * of_nat n) + \<delta>" by (simp add: algebra_simps)
    also have "\<dots> \<le> poly q (\<delta> * of_nat n) + \<delta>" using Suc by simp
    also have "\<dots> \<le> poly q (\<delta> * of_nat n + \<delta>)" 
      by (rule gt[unfolded delta_order], insert delta, auto)
    finally show ?case by (simp add: algebra_simps)
  qed force
  let ?lc = lead_coeff
  have "?lc q > 0" 
  proof (rule ccontr)
    define d where "d = poly q 0" 
    assume "\<not> ?thesis" 
    hence "?lc q \<le> 0" by auto
    moreover have "?lc q \<noteq> 0" using deg by auto
    ultimately have "?lc q < 0" by auto
    hence "?lc (-q) > 0" by auto
    from poly_pinfty_ge[OF this, of "-d"] deg obtain n where le: "\<And> x. x \<ge> n \<Longrightarrow> - d \<le> - poly q x" by auto        
    have d: "x \<ge> n \<Longrightarrow> d \<ge> poly q x" for x using le[of x] by linarith
    define m where "m = \<epsilon> * (max n 0 + 1)"   
    from eps_delta delta have eps: "\<epsilon> > 0"
      by (metis mult.commute order_less_le_trans zero_less_mult_pos zero_less_one)
    hence m: "m > 0" unfolding m_def by auto
    from ceil_nat[of m] m have cm: "ceil_nat m > 0"
      using linorder_not_less by force
    have "poly q (\<delta> * of_nat (ceil_nat m)) \<le> d" 
    proof (rule d)
      have "n \<le> max n 0 * 1" by simp
      also have "\<dots> \<le> max n 0 * (\<epsilon> * \<delta>)" using eps_delta
        by (simp add: max_def)
      also have "\<dots> = \<delta> * m - \<delta> * \<epsilon>" unfolding m_def by (simp add: field_simps)
      also have "\<dots> \<le> \<delta> * m" using eps_delta by (auto simp: ac_simps)
      also have "\<dots> \<le> \<delta> * of_nat (ceil_nat m)" 
        by (rule mult_left_mono[OF ceil_nat], insert delta, auto)
      finally show "n \<le> \<delta> * of_nat (ceil_nat m)" .
    qed
    also have "\<dots> < poly q 0 + \<delta> * of_nat (ceil_nat m)" unfolding d_def using delta cm by auto
    also have "\<dots> \<le> poly q (\<delta> * of_nat (ceil_nat m))" by (rule unbounded)
    finally show False by simp
  qed
  thus "lead_coeff q > 0" unfolding q_def .

  assume valid: "valid_poly p" 
  {
    fix y :: nat
    let ?y = "\<delta> * of_nat y" 
    from unbounded[of y]
    have "poly q ?y \<ge> poly q 0 + ?y" .
    moreover have "poly q 0 = insertion (a(x := 0)) p" unfolding q_def  
      using insertion_partial_insertion[of x a "a(x := 0)" p] by auto
    moreover have "\<dots> \<ge> 0" 
      by (intro valid[unfolded valid_poly_def, rule_format], insert ass, auto simp: assignment_def)
    ultimately have "poly q ?y \<ge> ?y" by auto
    thus "poly (partial_insertion a x p) ?y \<ge> ?y" unfolding q_def .
  } note ge = this
qed
end
end

context poly_inter
begin

lemma monotone_poly_eval_generic:
  assumes valid: "valid_monotone_poly_inter" 
    and trans_gt: "transp (\<succ>)" 
    and gt_imp_ge: "\<And>x y. x \<succ> y \<Longrightarrow> y \<le> x" 
    and gt_exists: "\<And> x. x \<ge> 0 \<Longrightarrow> \<exists> y. y \<succ> x" 
    and gt_irrefl: "\<And> x. \<not> (x \<succ> x)" 
    and tF: "funas_term t \<subseteq> F" 
  shows "monotone_poly (vars_term t) (eval t)" "vars (eval t) = vars_term t" 
proof - 
  have "monotone_poly (vars_term t) (eval t) \<and> vars (eval t) = vars_term t" using tF
  proof (induct t)
    case (Var x)
    show ?case by (auto simp: monotone_poly_wrt_def)
  next
    case (Fun f ts)
    {
      fix t
      assume "t \<in> set ts" 
      with Fun(1)[OF this] Fun(2) 
      have "monotone_poly (vars_term t) (eval t)" 
           "vars (eval t) = vars_term t" 
        by auto
    } note IH = this
    let ?n = "length ts" 
    let ?f = "(f,?n)" 
    define p where "p = I f" 
    from Fun have "?f \<in> F" by auto
    from valid[unfolded valid_monotone_poly_inter_def, rule_format, OF this, unfolded valid_monotone_poly_def]
    have valid: "valid_poly p" and mono: "monotone_poly (vars p) p" and vars: "vars p = {..<?n}" 
      unfolding p_def by auto
    have wm: "assignment b \<Longrightarrow> (\<And>x. x \<in> vars p \<Longrightarrow> (\<succ>)\<^sup>=\<^sup>= (a x) (b x)) \<Longrightarrow> (\<succ>)\<^sup>=\<^sup>= (insertion a p) (insertion b p)" 
      for b a using monotone_poly_wrt_insertion[OF trans_gt gt_imp_ge mono] by auto
    have id: "eval (Fun f ts) = substitute (\<lambda>i. if i < length ts then eval (ts ! i) else 0) p" 
      unfolding eval.simps p_def[symmetric] id by simp

    have mono: "monotone_poly (vars_term (Fun f ts)) (eval (Fun f ts))" 
      unfolding monotone_poly_wrt_def
    proof (intro allI impI)
      fix \<alpha> :: "_ \<Rightarrow> 'a" and x v
      assume \<alpha>: "assignment \<alpha>" 
        and x: "x \<in> vars_term (Fun f ts)" 
        and v: "v \<succ> \<alpha> x " 
      define \<beta> where "\<beta> = \<alpha>(x := v)" 
      define \<alpha>' where "\<alpha>' = (\<lambda> i. if i < ?n then insertion \<alpha> (eval (ts ! i)) else 0)" 
      define \<beta>' where "\<beta>' = (\<lambda> i. if i < ?n then insertion \<beta> (eval (ts ! i)) else 0)" 
      {
        fix i
        assume n: "i < ?n" 
        hence tsi: "ts ! i \<in> set ts" by auto
        {
          assume "x \<in> vars_term (ts ! i)" 
          from IH(1)[OF tsi, unfolded monotone_poly_wrt_def, rule_format, OF \<alpha> this v] 
          have ins: "\<beta>' i \<succ> \<alpha>' i" unfolding \<beta>_def \<alpha>'_def \<beta>'_def using n by auto
        } note gt = this
        {
          assume "x \<notin> vars_term (ts ! i)" 
          with IH(2)[OF tsi] have x: "x \<notin> vars (eval (ts ! i))" by auto
          hence "\<alpha>' i = \<beta>' i" unfolding \<alpha>'_def \<beta>'_def using n 
            by (auto simp: \<beta>_def intro: insertion_irrelevant_vars)
        }
        with gt have "gt^== (\<beta>' i) (\<alpha>' i)" by fastforce
        note gt this
      } note gt_le = this

      have \<alpha>': "assignment \<alpha>'" unfolding \<alpha>'_def assignment_def using Fun(2)
        by (force intro!: valid_imp_insertion_eval_pos[OF assms(1) _ \<alpha>] set_conv_nth)

      define \<gamma> where "\<gamma> n i = (if i < n then \<beta>' i else \<alpha>' i)" for n i
      have \<gamma>: "n < ?n \<Longrightarrow> assignment (\<gamma> n)" for n unfolding \<gamma>_def using gt_le(2) \<alpha>' gt_imp_ge
        unfolding assignment_def using order.trans[of 0 "\<alpha> x" "\<beta> x" for x] 
        by (smt (verit, best) dual_order.strict_trans dual_order.trans sup2E)

      from x obtain i where x: "x \<in> vars_term (ts ! i)" and i: "i < ?n" by (auto simp: set_conv_nth)
      from i vars have iv: "i \<in> vars p" by auto
      have \<gamma>i: "(\<gamma> (Suc i)) = (\<gamma> i)( i := \<beta>' i)" unfolding \<gamma>_def using i by (intro ext, auto)
      have 1: "gt^== (insertion (\<gamma> i) p) (insertion \<alpha>' p)" 
        by (rule monotone_poly_wrt_insertion[OF trans_gt gt_imp_ge mono \<alpha>'], insert  gt_le i, auto simp: \<gamma>_def)
      have 2: "gt (insertion (\<gamma> (Suc i)) p) (insertion (\<gamma> i) p)" 
        using mono[unfolded monotone_poly_wrt_def, rule_format, OF \<gamma>[OF i] iv, of "\<beta>' i"] gt_le(1)[OF i x]
        unfolding \<gamma>i by (auto simp: \<gamma>_def)
      have 3: "gt^== (insertion (\<gamma> ?n) p) (insertion (\<gamma> (Suc i)) p)" 
      proof (cases "Suc i < ?n")
        case True
        show ?thesis 
          by (rule monotone_poly_wrt_insertion[OF trans_gt gt_imp_ge mono \<gamma>[OF True]], insert gt_le True, auto simp: \<gamma>_def)
      next
        case False
        with i have "Suc i = ?n" by auto
        thus ?thesis by simp
      qed
      have 4: "insertion \<beta>' p = (insertion (\<gamma> ?n) p)" 
        unfolding \<gamma>_def by (rule insertion_irrelevant_vars, insert vars, auto)
      from 1 2 3
      have "gt (insertion \<beta>' p) (insertion \<alpha>' p)" using trans_gt unfolding 4
        by (metis (full_types) sup2E transp_def)
      moreover have "insertion \<alpha>' p = insertion \<alpha> (eval (Fun f ts)) \<and>
        insertion \<beta>' p = insertion (\<alpha>(x := v)) (eval (Fun f ts))" 
        unfolding id insertion_substitute 
        unfolding \<beta>'_def \<alpha>'_def if_distrib \<beta>_def[symmetric]
        by (auto intro: insertion_irrelevant_vars)
      ultimately show "gt (insertion (\<alpha>(x := v)) (eval (Fun f ts))) (insertion \<alpha> (eval (Fun f ts)))" by auto
    qed
    define t' where "t' = Fun f ts"
    define \<alpha> where "\<alpha> = (\<lambda> _ :: nat. 0 :: 'a)" 
    have ass: "assignment \<alpha>" by (auto simp: assignment_def \<alpha>_def)
    show ?case
    proof (intro conjI mono, unfold t'_def[symmetric])
      have "vars (eval t') \<subseteq> vars_term t'" by (rule vars_eval)
      moreover have "vars_term t' \<subseteq> vars (eval t')" 
      proof (rule ccontr)
        assume "\<not> ?thesis" 
        then obtain x where xt: "x \<in> vars_term t'" and x: "x \<notin> vars (eval t')" by auto
        from gt_exists[of "\<alpha> x"] obtain l where l: "l \<succ> \<alpha> x" unfolding \<alpha>_def by auto 

        from mono[folded t'_def, unfolded monotone_poly_wrt_def, rule_format, OF ass xt l]
        have "insertion (\<alpha>(x := l)) (eval t') \<succ> insertion \<alpha> (eval t')" by auto
        also have "insertion (\<alpha>(x := l)) (eval t') = insertion \<alpha> (eval t')" 
          by (rule insertion_irrelevant_vars, insert x, auto)
        finally show False using gt_irrefl by auto
      qed
      ultimately show "vars (eval t') = vars_term t'" by auto
    qed
  qed
  thus "monotone_poly (vars_term t) (eval t)" "vars (eval t) = vars_term t" by auto
qed  
end


context int_poly_inter
begin

lemma degree_mono: assumes pos: "lead_coeff p \<ge> (0 :: int)"
  and le: "\<And> x. x \<ge> c \<Longrightarrow> poly p x \<le> poly q x"
shows "degree p \<le> degree q" 
  by (rule degree_mono_generic[OF poly_pinfty_ge_int assms])

lemma degree_mono': assumes "\<And> x. x \<ge> c \<Longrightarrow> (bnd :: int) \<le> poly p x \<and> poly p x \<le> poly q x" 
  shows "degree p \<le> degree q" 
  by (rule degree_mono'_generic[OF poly_pinfty_ge_int assms])

lemma weakly_monotone_insertion: assumes "weakly_monotone_poly (vars p) p"
  and "assignment (a :: _ \<Rightarrow> int)" 
  and "\<And> x. x \<in> vars p \<Longrightarrow> a x \<le> b x"
shows "insertion a p \<le> insertion b p" 
proof -
  from monotone_poly_wrt_insertion[OF _ _ assms(1,2), of b] assms(3)
  show ?thesis by auto
qed

text \<open>Lemma 5.2\<close>

lemma degree_partial_insertion_stays_constant: assumes mono: "monotone_poly (vars p) p" 
  shows "\<exists> a. assignment (a :: _ \<Rightarrow> int) \<and> 
  (\<forall> b. (\<forall> y. a y \<le> b y) \<longrightarrow> degree (partial_insertion a x p) = degree (partial_insertion b x p))" 
  using degree_partial_insertion_stays_constant_generic[OF _ _ poly_pinfty_ge_int mono, of 0 x]
  by (simp, metis le_less)

lemma degree_partial_insertion_stays_constant_wm: assumes wm: "weakly_monotone_poly (vars p) p" 
  shows "\<exists> a. assignment (a :: _ \<Rightarrow> int) \<and> 
  (\<forall> b. (\<forall> y. a y \<le> b y) \<longrightarrow> degree (partial_insertion a x p) = degree (partial_insertion b x p))" 
  using degree_partial_insertion_stays_constant_generic[OF _ _ poly_pinfty_ge_int wm, of 0 x]
  by auto

text \<open>Lemma 5.3\<close>

lemma subst_same_var_weakly_monotone_imp_same_degree: 
  assumes wm: "weakly_monotone_poly (vars p) (p :: int mpoly)" 
    and dq: "degree q = d" 
    and d0: "d \<noteq> 0" 
    and qp: "poly_to_mpoly x q = substitute (\<lambda>i. PVar x) p" 
  shows "total_degree p = d" 
proof -
  let ?mc = "(\<lambda> m. mmonom m (mcoeff p m))" 
  let ?cfs = "{m . mcoeff p m \<noteq> 0}" 
  let ?lc = "lead_coeff" 
  note fin = finite_coeff_support[of p]
  from poly_to_mpoly_substitute_same[OF qp] d0[folded dq] have p0: "p \<noteq> 0"
    by (metis degree_0 insertion_zero poly_all_0_iff_0)
  define M where "M = total_degree p" 
  from degree_monom_eq_total_degree[OF p0]
  obtain mM where mM: "mcoeff p mM \<noteq> 0" "degree_monom mM = M" unfolding M_def by blast
  from degree_substitute_same_var[of x p, folded M_def qp]
  have dM: "d \<le> M" unfolding dq degree_poly_to_mpoly .
  with d0 have M1: "M \<ge> 1" by auto
  define p1 where "p1 = sum ?mc (?cfs \<inter> {m. degree_monom m = M})" 
  define p2 where "p2 = sum ?mc (?cfs \<inter> {m. degree_monom m < M})" 
  have "p = sum ?mc ?cfs" 
    by (rule mpoly_as_sum)
  also have "?cfs = ?cfs \<inter> {m. degree_monom m = M}
     \<union> ?cfs \<inter> {m. degree_monom m \<noteq> M}" by auto
  also have "?cfs \<inter> {m. degree_monom m \<noteq> M} = ?cfs \<inter> {m. degree_monom m < M}" 
    using degree_monon_le_total_degree[of p, folded M_def] by force
  also have "sum ?mc (?cfs \<inter> {m. degree_monom m = M} \<union> \<dots>) = p1 + p2" unfolding p1_def p2_def
    using fin by (intro sum.union_disjoint, auto)
  finally have p_split: "p = p1 + p2" .
  have "total_degree p2 \<le> M - 1" unfolding p2_def
    by (intro total_degree_sum_leI, subst total_degree_monom, auto)
  also have "\<dots> < M" using M1 by auto
  finally have deg_p': "total_degree p2 < M" by auto
  have "p1 \<noteq> 0" 
  proof
    assume "p1 = 0" 
    hence "p = p2" unfolding p_split by auto
    hence "M = total_degree p2" unfolding M_def by simp
    with deg_p' show False by auto
  qed
  with mpoly_ext_bounded_int[of 0 p1 0] obtain b
    where b: "\<And> v. b v \<ge> 0" and bpm0: "insertion b p1 \<noteq> 0" by auto
  define B where "B = Max (insert 1 (b ` vars p))" 
  define X where "X = (0 :: nat)" 
  define pb where "pb p = mpoly_to_poly X (substitute (\<lambda> v. Const (b v) * PVar X) p)" for p
  have varsX: "vars (substitute (\<lambda> v. Const (b v) * PVar X) p) \<subseteq> {X}" for p
    by (intro vars_substitute order.trans[OF vars_mult], auto)
  have pb: "substitute (\<lambda> v. Const (b v) * PVar X) p = poly_to_mpoly X (pb p)" for p
    unfolding pb_def
    by (rule mpoly_to_poly_inverse[symmetric, OF varsX])    
  have poly_pb: "poly (pb p) x = insertion (\<lambda>v. b v * x) p" for x p
    using arg_cong[OF pb, of "insertion (\<lambda> _. x)", 
        unfolded insertion_poly_to_mpoly]
    by (auto simp: insertion_substitute insertion_mult)
  define lb where "lb = insertion (\<lambda> _. 0) p" 
  {
    fix x
    have "poly (pb p) x = insertion (\<lambda>v. b v * x) p" by fact
    also have "\<dots> = insertion (\<lambda>v. b v * x) p1 + insertion (\<lambda>v. b v * x) p2" unfolding p_split
      by (simp add: insertion_add)
    also have "insertion (\<lambda>v. b v * x) p1 = insertion b p1 * x^M" 
      unfolding p1_def insertion_sum insertion_mult insertion_monom sum_distrib_right 
        power_mult_distrib
    proof (intro sum.cong[OF refl], goal_cases)
      case (1 m)
      from 1 have M: "M = degree_monom m" by auto
      have "{ v. lookup m v \<noteq> 0} \<subseteq> keys m"
        by (simp add: keys.rep_eq)
      from finite_subset[OF this] have fin: "finite { v. lookup m v \<noteq> 0}" by auto
      have "(\<Prod>v. b v ^ lookup m v * x ^ lookup m v) 
          = (\<Prod>v. b v ^ lookup m v) * (\<Prod>v. x ^ lookup m v)" 
        by (subst (1 2 3) Prod_any.expand_superset[OF fin]) 
          (insert zero_less_iff_neq_zero, force simp: prod.distrib)+
      also have "(\<Prod>v. x ^ lookup m v) = x ^ M" unfolding M degree_monom_def
        by (smt (verit) Prod_any.conditionalize Prod_any.cong finite_keys in_keys_iff power_0 power_sum)
      finally show ?case by simp
    qed
    also have "insertion (\<lambda>v. b v * x) p2 = poly (pb p2) x" unfolding poly_pb ..
    finally have "poly (pb p) x = poly (monom (insertion b p1) M + pb p2) x" by (simp add: poly_monom)
  } 
  hence pbp_split: "pb p = monom (insertion b p1) M + pb p2" by blast
  have "degree (pb p2) \<le> total_degree p2" unfolding pb_def 
    apply (subst degree_mpoly_to_poly) 
     apply (simp add: varsX)
    by (rule degree_substitute_const_same_var)
  also have "\<dots> < M" by fact
  finally have deg_pbp2: "degree (pb p2) < M" .
  have "degree (monom (insertion b p1) M) = M" using bpm0 by (rule degree_monom_eq)
  with deg_pbp2 pbp_split have deg_pbp: "degree (pb p) = M" unfolding pbp_split 
    by (subst degree_add_eq_left, auto)
  have "?lc (pb p) = insertion b p1"  unfolding pbp_split 
    using deg_pbp2 bpm0 coeff_eq_0 deg_pbp pbp_split by auto
  define bnd where "bnd = insertion (\<lambda> _. 0) p" 

  {
    fix x :: int
    assume x: "x \<ge> 0" 
    have ass: "assignment (\<lambda> v. b v * x)" unfolding assignment_def using x b by auto
    have "poly (pb p) x = insertion (\<lambda>v. b v * x) p" by fact
    also have "insertion (\<lambda> v. b v * x) p \<le> insertion (\<lambda> v. B * x) p"
    proof (rule weakly_monotone_insertion[OF wm ass])
      fix v
      show "v \<in> vars p \<Longrightarrow> b v * x \<le> B * x" using b[of v] x unfolding B_def 
        by (intro mult_right_mono, auto intro!: Max_ge vars_finite)
    qed
    also have "\<dots> = poly q (B * x)" unfolding poly_to_mpoly_substitute_same[OF qp] ..
    also have "\<dots> = poly (q \<circ>\<^sub>p [:0, B:]) x" by (simp add: poly_pcompose ac_simps)
    finally have ineq: "poly (pb p) x \<le> poly (q \<circ>\<^sub>p [:0, B:]) x" .
    have "bnd \<le> insertion (\<lambda>v. b v * x) p" unfolding bnd_def
      by (intro weakly_monotone_insertion[OF wm], insert b x, auto simp: assignment_def)
    also have "\<dots> = poly (pb p) x" using poly_pb by auto
    finally have "bnd \<le> poly (pb p) x" by auto 
    note this ineq
  } note pb_approx = this
  have "M = degree (pb p)" unfolding deg_pbp ..
  also have "\<dots> \<le> degree (q \<circ>\<^sub>p [:0, B:])"
    by (intro degree_mono'[of 0 bnd], insert pb_approx, auto)
  also have "\<dots> \<le> d" by (simp add: dq)
  finally have deg_pbp: "M \<le> d" .
  with dM have "M = d" by auto
  thus ?thesis unfolding M_def .
qed

lemma monotone_poly_partial_insertion: 
  assumes x: "x \<in> xs" 
  and mono: "monotone_poly xs p"
  and ass: "assignment a" 
shows "0 < degree (partial_insertion a x p)" 
   "lead_coeff (partial_insertion a x p) > 0"
   "valid_poly p \<Longrightarrow> y \<ge> 0 \<Longrightarrow> poly (partial_insertion a x p) y \<ge> y" 
   "valid_poly p \<Longrightarrow> insertion a p \<ge> a x" 
proof -
  have 0: "transp ((>) :: int \<Rightarrow> _)" by auto
  have 1: "(x < y) = (x + 1 \<le> y)" for x y :: int by auto 
  have 2: "x \<le> int (nat x)" for x by auto
  note main = monotone_poly_partial_insertion_generic[of "(>)" 1 1 nat, OF 0 _ poly_pinfty_ge_int 1 _ _ 2 x mono ass, simplified]
  show "0 < degree (partial_insertion a x p)" "0 < lead_coeff (partial_insertion a x p)" 
    using main by auto
  assume valid: "valid_poly p" 
  {
    fix y :: int
    assume "y \<ge> 0" 
    then obtain n where y: "y = int n"
      by (metis int_nat_eq)
    from main(3)[OF valid, of n, folded y] 
    show "y \<le> poly (partial_insertion a x p) y" by auto
  } note estimation = this
  from ass have "a x \<ge> 0" unfolding assignment_def by auto
  from estimation[OF this] show "insertion a p \<ge> a x" 
    using insertion_partial_insertion[of x a a p] by auto
qed  

end

context int_poly_inter
begin

lemma insertion_eval_pos: assumes "funas_term t \<subseteq> F"
  and "assignment \<alpha>" 
shows "insertion \<alpha> (eval t) \<ge> 0" 
  by (rule valid_imp_insertion_eval_pos[OF valid assms]) 

lemma monotone_poly_eval: assumes "funas_term t \<subseteq> F" 
  shows "monotone_poly (vars_term t) (eval t)" "vars (eval t) = vars_term t" 
proof -
  have "\<exists>y. x < y" for x :: int by (intro exI[of _ "x + 1"], auto)
  from monotone_poly_eval_generic[OF valid _ _ this _ assms]
  show "monotone_poly (vars_term t) (eval t)" "vars (eval t) = vars_term t" by auto
qed
end


locale term_poly_input = poly_input p q for p q +
  assumes terminating_poly: "termination_by_int_poly_interpretation F_S S" 
begin

definition I where "I = (SOME I. int_poly_inter F_S I \<and> int_poly_inter.termination_by_poly_interpretation F_S I S)" 

lemma I: "int_poly_inter F_S I" "int_poly_inter.termination_by_poly_interpretation F_S I S" 
  using someI_ex[OF terminating_poly[unfolded termination_by_int_poly_interpretation_def], folded I_def] by auto

sublocale int_poly_inter F_S I by (rule I(1))

lemma orient: "orient_rule (lhs_S,rhs_S)" 
  using I(2)[unfolded termination_by_interpretation_def termination_by_poly_interpretation_def] unfolding S_def by auto

lemma solution: "positive_poly_problem p q"
proof -
  from orient[unfolded orient_rule]
  have gt: "gt_poly (eval lhs_S) (eval rhs_S)" by auto
  from valid[unfolded valid_monotone_poly_inter_def]
  have valid: "\<And> f. f \<in> F_S \<Longrightarrow> valid_monotone_poly f" by auto
  let ?lc = "lead_coeff" 
  let ?f = "(f_sym,7)" 
  have "?f \<in> F_S" unfolding F_S_def by auto
  from valid[OF this, unfolded valid_monotone_poly_def] obtain f where
    If: "I f_sym = f" and f: "valid_poly f" "monotone_poly (vars f) f" "vars f = {..< 7}" by auto
  from f(2) have wmf: "weakly_monotone_poly (vars f) f" by (rule monotone_imp_weakly_monotone)
  define l where "l i = args (lhs_S) ! i" for i
  define r where "r i = args (rhs_S) ! i" for i
  have list: "[0..<7] = [0,1,2,3,4,5,6 :: nat]" by code_simp
  have lhs_S: "lhs_S = Fun f_sym (map l [0..<7])" unfolding lhs_S_def l_def by (auto simp: list)
  have rhs_S: "rhs_S = Fun f_sym (map r [0..<7])" unfolding rhs_S_def r_def by (auto simp: list)
  {
    fix i :: var
    define vs where "vs = V_list" 
    assume "i < 7" 
    hence choice: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i = 6" by linarith
    have set: "{0..<7 :: nat} = {0,1,2,3,4,5,6}" by code_simp
    from choice have vars: "vars_term (l i) = {i}" "vars_term (r i) = {i}" unfolding l_def lhs_S_def r_def rhs_S_def 
      using vars_encode_poly[of 2 p] vars_encode_poly[of 2 q] 
      by (auto simp: y1_def y2_def y3_def y4_def y5_def y6_def y7_def vs_def[symmetric])
    from choice set have funs: "funas_term (l i) \<union> funas_term (r i) \<subseteq> F_S" using rhs_S_F lhs_S_F unfolding lhs_S rhs_S
      by auto
    have "lr \<in> {l,r} \<Longrightarrow> vars_term (lr i) = {i}" "lr \<in> {l,r} \<Longrightarrow> funas_term (lr i) \<subseteq> F_S" for lr
      by (insert vars funs, force)+
  } note signature_l_r = this  
  {
    fix i :: var and lr
    assume i: "i < 7" and lr: "lr \<in> {l,r}" 
    from signature_l_r[OF i lr] monotone_poly_eval[of "lr i"] 
    have vars: "vars (eval (lr i)) = {i}"  
      and mono: "monotone_poly {i} (eval (lr i))" by auto
  } note eval_l_r = this

  define upoly where "upoly l_or_r i = mpoly_to_poly i (eval (l_or_r i))" for l_or_r :: "var \<Rightarrow> (_,_)term" and i

  {
    fix lr and i :: nat and a :: "_ \<Rightarrow> int" 
    assume a: "assignment a" and i: "i < 7" and lr: "lr \<in> {l,r}"  
    with eval_l_r[OF i] signature_l_r[OF i]
    have vars: "vars (eval (lr i)) = {i}" and mono: "monotone_poly {i} (eval (lr i))"
      and funs: "funas_term (lr i) \<subseteq> F_S" by auto
    from insertion_eval_pos[OF funs] 
    have valid: "valid_poly (eval (lr i))" unfolding valid_poly_def by auto
    from monotone_poly_partial_insertion[OF _ mono a, of i] valid
    have deg: "degree (partial_insertion a i (eval (lr i))) > 0" 
      and lc: "?lc (partial_insertion a i (eval (lr i))) > 0" 
      and ineq: "insertion a (eval (lr i)) \<ge> a i" by auto
    moreover have "partial_insertion a i (eval (lr i)) = upoly lr i" unfolding upoly_def
      using vars eval_l_r[OF i, of r, simplified]
      by (intro poly_ext)
        (metis i insertion_partial_insertion_vars poly_eq_insertion poly_inter.vars_eval signature_l_r(1)[of _ r, simplified] singletonD)
    ultimately 
    have "degree (upoly lr i) > 0" "?lc (upoly lr i) > 0" 
      "insertion a (eval (lr i)) \<ge> a i" by auto
  } note upoly_pos_subterm = this


  {
    fix i :: var
    assume i: "i < 7" 
    from degree_partial_insertion_stays_constant[OF f(2), of i] obtain a where
      a: "assignment a" and
      deg_a: "\<And> b. (\<And> y. a y \<le> b y) \<Longrightarrow> degree (partial_insertion a i f) = degree (partial_insertion b i f)" 
      by auto
    define c where "c j = (if j < 7 then insertion a (eval (l j)) else a j)" for j
    define e where "e j = (if j < 7 then insertion a (eval (r j)) else a j)" for j
    {
      fix x :: int
      assume x: "x \<ge> 0" 
      have ass: "assignment (a (i := x))" using x a unfolding assignment_def by auto
      from gt[unfolded gt_poly_def, rule_format, OF ass, unfolded rhs_S lhs_S]
      have "insertion (a(i := x)) (eval (Fun f_sym (map r [0..<7])))
        < insertion (a(i := x)) (eval (Fun f_sym (map l [0..<7])))" by simp
      also have "insertion (a(i := x)) (eval (Fun f_sym (map r [0..<7]))) = 
        insertion (\<lambda>j. insertion (a(i := x)) (eval (r j))) f" 
        by (simp add: If insertion_substitute, intro insertion_irrelevant_vars, auto simp: f)
      also have "\<dots> = poly (partial_insertion e i f) (poly (upoly r i) x)" 
      proof -
        let ?\<alpha> = "(\<lambda>j. insertion (a(i := x)) (eval (r j)))" 
        have insi: "poly (upoly r i) x = insertion (a(i := x)) (eval (r i))" 
          unfolding upoly_def using eval_l_r(1)[OF i, of r]
          by (subst poly_eq_insertion, force)
            (intro insertion_irrelevant_vars, auto)
        show ?thesis unfolding insi
        proof (rule insertion_partial_insertion_vars[of i f e ?\<alpha>, symmetric])
          fix j
          show "j \<noteq> i \<Longrightarrow> j \<in> vars f \<Longrightarrow> e j = insertion (a(i := x)) (eval (r j))" 
            unfolding e_def f using eval_l_r[of j] f by (auto intro!: insertion_irrelevant_vars)
        qed
      qed
      also have "insertion (a(i := x)) (eval (Fun f_sym (map l [0..<7]))) = 
        insertion (\<lambda>j. insertion (a(i := x)) (eval (l j))) f" 
        by (simp add: If insertion_substitute, intro insertion_irrelevant_vars, auto simp: f)
      also have "\<dots> = poly (partial_insertion c i f) (poly (upoly l i) x)" 
      proof -
        let ?\<alpha> = "(\<lambda>j. insertion (a(i := x)) (eval (l j)))" 
        have insi: "poly (upoly l i) x = insertion (a(i := x)) (eval (l i))" 
          unfolding upoly_def using eval_l_r[OF i]
          by (subst poly_eq_insertion, force)
            (intro insertion_irrelevant_vars, auto)
        show ?thesis unfolding insi
        proof (rule insertion_partial_insertion_vars[of i f c ?\<alpha>, symmetric])
          fix j
          show "j \<noteq> i \<Longrightarrow> j \<in> vars f \<Longrightarrow> c j = insertion (a(i := x)) (eval (l j))" 
            unfolding c_def f using eval_l_r[of j] f by (auto intro!: insertion_irrelevant_vars)
        qed
      qed

      finally have "poly (partial_insertion c i f) (poly (upoly l i) x) 
        > poly (partial_insertion e i f) (poly (upoly r i) x)" .
    } note 1 = this (* equation (1) in paper *)

    define er where "er = partial_insertion e i f \<circ>\<^sub>p upoly r i"
    define cl where "cl = partial_insertion c i f \<circ>\<^sub>p upoly l i"
    define d where "d = degree (partial_insertion e i f)" 
    {
      fix x
      have "a x \<le> c x \<and> a x \<le> e x" 
      proof (cases "x \<in> vars f")
        case False
        thus ?thesis unfolding c_def e_def f by auto
      next
        case True
        hence id: "(x < 7) = True" and x: "x < 7" unfolding f by auto
        show ?thesis unfolding c_def e_def id if_True using upoly_pos_subterm(3)[OF a x] by auto
      qed
      hence "a x \<le> c x" "a x \<le> e x" by auto
    } note a_ce = this

    have d_eq: "d = degree (partial_insertion c i f)" unfolding d_def
      by (subst (1 2) deg_a[symmetric], insert a_ce, auto)

    have e: "assignment e" using a a_ce(2) unfolding assignment_def
      by (smt (verit, del_insts))

    have d_pos: "d > 0" unfolding d_def
      by (intro monotone_poly_partial_insertion[OF _ f(2) e], insert f i, auto)
    have lc_e_pos: "?lc (partial_insertion e i f) > 0"
      by (intro monotone_poly_partial_insertion[OF _ f(2) e], insert f i, auto)

    have lc_r_pos: "?lc (upoly r i) > 0" by (intro upoly_pos_subterm[OF a i], auto)
    have deg_r: "0 < degree (upoly r i)" by (intro upoly_pos_subterm[OF a i], auto)
    have lc_er_pos: "?lc er > 0" unfolding er_def
      by (subst lead_coeff_comp[OF deg_r], insert lc_e_pos deg_r lc_r_pos, auto)

    from 1[folded poly_pcompose, folded er_def cl_def]  
    have er_cl_poly: "0 \<le> x \<Longrightarrow> poly er x < poly cl x" for x by auto
    have "degree er \<le> degree cl"
    proof (intro degree_mono[of _ 0])
      show "0 \<le> ?lc er" using lc_er_pos by auto
      show "0 \<le> x \<Longrightarrow> poly er x \<le> poly cl x" for x using er_cl_poly[of x] by auto
    qed 
    also have "degree er = d * degree (upoly r i)" 
      unfolding er_def d_def by simp
    also have "degree cl = d * degree (upoly l i)" 
      unfolding cl_def d_eq by simp
    finally have "degree (upoly l i) \<ge> degree (upoly r i)" using d_pos by auto
  } note deg_inequality = this

  {
    fix p :: "int mpoly" and x
    assume p: "monotone_poly {x} p" "vars p = {x}"
    define q where "q = mpoly_to_poly x p" 
    from mpoly_to_poly_inverse[of p x] 
    have pq: "p = poly_to_mpoly x q" using p unfolding q_def by auto
    from pq p(2) have deg: "degree q > 0"
      by (simp add: degree_mpoly_to_poly degree_pos_iff q_def)
    from deg pq have "\<exists> q. p = poly_to_mpoly x q \<and> degree q > 0" unfolding q_def by auto
  } note mono_unary_poly = this

  {
    fix f
    assume "f \<in> {q_sym, h_sym} \<union> v_sym ` V" 
    hence "(f, 1) \<in> F_S" unfolding F_S_def F_def by auto
    from valid[OF this, unfolded valid_monotone_poly_def] obtain p 
      where p: "p = I f" "monotone_poly {..<1} p" "vars p = {0}" by auto  
    have id: "{..< (1 :: nat)} = {0}" by auto
    have "\<exists> q. I f = poly_to_mpoly 0 q \<and> degree q > 0" unfolding p(1)[symmetric]
      by (intro mono_unary_poly, insert p(2-3)[unfolded id], auto)
  } note unary_symbol = this

  {
    fix f and n :: nat and x :: var
    assume "f \<in> {f_sym,a_sym}" "f = f_sym \<Longrightarrow> n = 7" "f = a_sym \<Longrightarrow> n = 2" 
    hence n: "n > 1" and f: "(f,n) \<in> F_S" unfolding F_def F_S_def by force+
    define p where "p = I f" 
    from valid[OF f, unfolded valid_monotone_poly_def, rule_format, OF refl p_def]
    have mono: "monotone_poly (vars p) p" and vars: "vars p = {..<n}" and valid: "valid_poly p" by auto 
    let ?t = "Fun f (replicate n (TVar x))" 
    have t_F: "funas_term ?t \<subseteq> F_S" using f by auto
    have vt: "vars_term ?t = {x}" using n by auto
    define q where "q = eval ?t" 
    from monotone_poly_eval[OF t_F, unfolded vt, folded q_def]
    have "monotone_poly {x} q" "vars q = {x}" by auto
    from mono_unary_poly[OF this] obtain q' where 
      qq': "q = poly_to_mpoly x q'" and dq': "degree q' > 0" by auto
    have q't: "poly_to_mpoly x q' = eval ?t" unfolding qq'[symmetric] q_def by simp
    also have "\<dots> = substitute (\<lambda>i. if i < n then eval (replicate n (TVar x) ! i) else 0) p" 
      by (simp add: p_def[symmetric])
    also have "(\<lambda>i. if i < n then eval (replicate n (TVar x) ! i) else 0) = (\<lambda>i. if i < n then PVar x else 0)" 
      by (intro ext, auto)
    also have "substitute \<dots> p = substitute (\<lambda> i. PVar x) p" using vars
      unfolding substitute_def using vars_replace_coeff[of Const, OF Const_0] 
      by (intro insertion_irrelevant_vars, auto)
    finally have eq: "poly_to_mpoly x q' = substitute (\<lambda>i. PVar x) p" .
    have "\<exists> p q. I f = p \<and> eval ?t = poly_to_mpoly x q \<and> poly_to_mpoly x q = substitute (\<lambda>i. PVar x) p \<and> degree q > 0
      \<and> vars p = {..<n} \<and> monotone_poly (vars p) p" 
      by (intro exI[of _ p] exI[of _ q'] conjI valid eq dq' p_def[symmetric] q't[symmetric] mono vars)
  } note f_a_sym = this      

  from unary_symbol[of q_sym] obtain q where Iq: "I q_sym = poly_to_mpoly 0 q" and dq: "degree q > 0" by auto
  from unary_symbol[of h_sym] obtain h where Ih: "I h_sym = poly_to_mpoly 0 h" and dh: "degree h > 0" by auto

  from unary_symbol[of "v_sym i" for i] have "\<forall> i. \<exists> q. i \<in> V \<longrightarrow> I (v_sym i) = poly_to_mpoly 0 q \<and> 0 < degree q" by auto
  from choice[OF this] obtain v where 
    Iv: "i \<in> V \<Longrightarrow> I (v_sym i) = poly_to_mpoly 0 (v i)" and 
    dv: "i \<in> V \<Longrightarrow> degree (v i) > 0" 
  for i by auto

  have eval_pm_Var: "eval (TVar y) = poly_to_mpoly y [:0,1:]" for y
    unfolding eval.simps mpoly_of_poly_is_poly_to_mpoly[symmetric] by simp
  have id: "(if 0 = (0 :: nat) then eval ([t] ! 0) else 0) = eval t" for t by simp
  {
    have y: "eval (TVar y4) = poly_to_mpoly y4 [:0,1:]" (is "_ = poly_to_mpoly _ ?poly1") by fact  
    have hy: "eval (Fun h_sym [TVar y4]) = poly_to_mpoly y4 h" using Ih
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y4 ?poly1])
       apply (unfold id, intro y)
      by simp
    have qhy: "eval (Fun q_sym [Fun h_sym [TVar y4]]) = poly_to_mpoly y4 (pcompose q h)" using Iq
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y4 h])
       apply (unfold id, intro hy)
      by simp
    hence l3: "eval (l 3) = poly_to_mpoly y4 (pcompose q h)" unfolding l_def lhs_S_def by simp

    have qy: "eval (Fun q_sym [TVar y4]) = poly_to_mpoly y4 q" using Iq
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y4 ?poly1])
       apply (unfold id, intro y)
      by simp
    have hqy: "eval (Fun h_sym [Fun q_sym [TVar y4]]) = poly_to_mpoly y4 (pcompose h q)" using Ih
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y4 q])
       apply (unfold id, intro qy)
      by simp
    have hhqy: "eval (Fun h_sym [Fun h_sym [Fun q_sym [TVar y4]]]) = poly_to_mpoly y4 (pcompose h (pcompose h q))" using Ih
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y4 "pcompose h q"])
       apply (unfold id, intro hqy)
      by simp
    hence r3: "eval (r 3) = poly_to_mpoly y4 (pcompose h (pcompose h q))" unfolding r_def rhs_S_def by simp

    from deg_inequality[of 3] have deg: "degree (upoly r 3) \<le> degree (upoly l 3)" by simp
    hence "degree h * (degree h * degree q) \<le> degree q * degree h" 
      unfolding upoly_def l3 r3 y4_def poly_to_mpoly_inverse by simp
    with dq have "degree h * degree h \<le> degree h" by simp
    with dh have "degree h = 1" by auto
  } note dh = this

  define tayy where "tayy = Fun a_sym (replicate 2 (TVar y5))" 
  from f_a_sym[of a_sym 2 y5, folded tayy_def] obtain a ayy where 
    Ia: "I a_sym = a" 
    and eval_ayy: "eval tayy = poly_to_mpoly y5 ayy" 
    and dayy: "degree ayy > 0" and payy: "poly_to_mpoly y5 ayy = substitute (\<lambda>i. PVar y5) a"
    and monoa: "monotone_poly (vars a) a" and varsa: "vars a = {..<2}" by blast

  {
    define vs where "vs = V_list" 
    have vs: "set vs \<subseteq> V" unfolding vs_def V_list by auto
    have "r 4 = foldr (\<lambda>i t. Fun (v_sym i) [t]) vs tayy" unfolding tayy_def r_def rhs_S_def sub_def vs_def 
      by (simp add: numeral_eq_Suc)
    also have "\<exists> q. eval \<dots> = poly_to_mpoly y5 q \<and> degree q = prod_list (map (\<lambda> i. degree (v i)) vs) * degree ayy" 
      using vs
    proof (induct vs)
      case Nil
      show ?case using eval_ayy by auto
    next
      case (Cons x vs)
      from Cons obtain q where IH1: "eval (foldr (\<lambda>i t. Fun (v_sym i) [t]) vs tayy) = poly_to_mpoly y5 q"
        and IH2: "degree q = (\<Prod>i\<leftarrow>vs. degree (v i)) * degree ayy" by auto
      from Cons have x: "x \<in> V" by auto
      have eval: "eval (foldr (\<lambda>i t. Fun (v_sym i) [t]) (x # vs) tayy) = poly_to_mpoly y5 (v x \<circ>\<^sub>p q)" using Iv[OF x]
        apply simp
        apply (subst substitute_poly_to_mpoly[of _ _ y5 q])
         apply (unfold id, intro IH1)
        by simp
      show ?case unfolding eval by (intro exI[of _ "v x \<circ>\<^sub>p q"], auto simp: IH2)
    qed
    finally obtain q where 
      r4: "eval (r 4) = poly_to_mpoly y5 q" and 
      q: "degree q = prod_list (map (\<lambda> i. degree (v i)) vs) * degree ayy" 
      by auto

    have y: "eval (TVar y5) = poly_to_mpoly y5 [:0,1:]" (is "_ = poly_to_mpoly _ ?poly1") by fact  
    have hy: "eval (Fun h_sym [TVar y5]) = poly_to_mpoly y5 h" using Ih
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y5 ?poly1])
       apply (unfold id, intro y)
      by simp

    hence l4: "eval (l 4) = poly_to_mpoly y5 h" unfolding l_def lhs_S_def by simp

    from deg_inequality[of 4] have deg: "degree (upoly r 4) \<le> degree (upoly l 4)" by simp
    hence "degree q \<le> degree h" 
      unfolding upoly_def l4 r4 y5_def poly_to_mpoly_inverse by simp
    hence degq: "degree q \<le> 1" unfolding dh by simp
    hence "(\<forall> x \<in> set vs. degree (v x) = 1) \<and> degree ayy = 1 \<and> degree q = 1" using vs unfolding q
    proof (induct vs)
      case Nil
      thus ?case using dayy by auto
    next
      case (Cons x vs)
      define rec where "rec = (\<Prod>i\<leftarrow>vs. degree (v i)) * degree ayy" 
      have id: "(\<Prod>i\<leftarrow>x # vs. degree (v i)) * degree ayy = degree (v x) * rec" 
        unfolding rec_def by auto
      from Cons(2)[unfolded id] have prems: "degree (v x) * rec \<le> 1" by auto      
      from Cons(3) have x: "x \<in> V" and sub: "set vs \<subseteq> V" by auto
      from dv[OF x] have dv: "degree (v x) \<ge> 1" by auto
      from dv prems have "rec \<le> 1"
        by (metis dual_order.trans mult.commute mult.right_neutral mult_le_mono2)
      from Cons(1)[folded rec_def, OF this sub]
      have IH: "(\<forall>x\<in>set vs. degree (v x) = 1)" "degree ayy = 1" "rec = 1" by auto
      from IH(3) dv prems have dvx: "degree (v x) = 1" by simp
      show ?case unfolding id using dvx IH by auto
    qed
    from this[unfolded vs_def V_list]
    have dv: "\<And> x. x \<in> V \<Longrightarrow> degree (v x) = 1" and dayy: "degree ayy = 1" by auto
  } 
  hence dv: "\<And> x. x \<in> V \<Longrightarrow> degree (v x) = 1" and dayy: "degree ayy = 1" by auto

  define tfyy where "tfyy = Fun f_sym (replicate 7 (TVar y6))" 
  from f_a_sym[of f_sym 7 y6, folded tfyy_def] obtain f fyy where 
    If: "I f_sym = f" 
    and eval_fyy: "eval tfyy = poly_to_mpoly y6 fyy" 
    and dfyy: "degree fyy > 0" and pfyy: "poly_to_mpoly y6 fyy = substitute (\<lambda>i. PVar y6) f"
    and monof: "monotone_poly (vars f) f" and varsf: "vars f = {..<7}" by blast

  {
    have y: "eval (TVar y6) = poly_to_mpoly y6 [:0,1:]" (is "_ = poly_to_mpoly _ ?poly1") by fact  
    have hy: "eval (Fun h_sym [TVar y6]) = poly_to_mpoly y6 h" using Ih
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y6 ?poly1])
       apply (unfold id, intro y)
      by simp

    hence l5: "eval (l 5) = poly_to_mpoly y6 h" unfolding l_def lhs_S_def by simp
    have "r 5 = tfyy" unfolding tfyy_def r_def rhs_S_def by simp
    hence r5: "eval (r 5) = poly_to_mpoly y6 fyy" using eval_fyy by simp  

    from deg_inequality[of 5] have deg: "degree (upoly r 5) \<le> degree (upoly l 5)" by simp
    from this[unfolded upoly_def l5 r5 y6_def poly_to_mpoly_inverse dh]
    have "degree fyy \<le> 1" .
  }
  with dfyy 
  have dfyy: "degree fyy = 1" by auto

  note lemma_5_3 = subst_same_var_weakly_monotone_imp_same_degree[OF monotone_imp_weakly_monotone]
  from lemma_5_3[OF monof dfyy _ pfyy] have df: "total_degree f = 1" by auto
  from lemma_5_3[OF monoa dayy _ payy] have da: "total_degree a = 1" by auto

  let ?argsL = "[q_t (h_t (Var y4)),
    h_t (Var y5),
    h_t (Var y6), 
    g_t (Var y7) o_t]" 
  let ?argsR = "[h_t (h_t (q_t (Var y4))),
    foldr v_t V_list (a_t (Var y5) (Var y5)),
    Fun f_sym (replicate 7 (Var y6)),
    g_t (Var y7) z_t]" 

  show ?thesis
    apply (rule poly_input_to_solution_common.solution[of _ _ I F_S ?argsL ?argsR])
    apply (unfold_locales)
    subgoal using orient unfolding lhs_S_def rhs_S_def by simp
    subgoal by simp
    subgoal using signature_l_r(1)[of 4 r]   
      by (auto simp: y1_def y2_def y3_def y4_def y5_def y6_def y7_def r_def rhs_S_def)
    subgoal unfolding F_S_def by auto
    subgoal for g n
    proof (goal_cases)
      case 1
      hence ch: "(g,n) = (f_sym,7) \<or> (g,n) \<in> F" by auto
      hence "(g,n) \<in> F_S" unfolding F_S_def by auto
      from valid[rule_format, OF this, unfolded valid_monotone_poly_def, rule_format, OF refl refl]
      have *: "valid_poly (I g)" "monotone_poly {..<n} (I g)" "vars (I g) = {..<n}" 
        by auto
      show ?case
      proof (intro monotone_linear_poly_to_coeffs *)
        show "total_degree (I g) \<le> 1" 
        proof (rule ccontr)
          assume not: "\<not> ?thesis" 
          with ch df da If Ia have "(g,n) \<in> F - {(a_sym,2)}" by auto
          then consider (V) i where "i \<in> V" "g = v_sym i" "n = 1" | (z) "g = z_sym" "n = 0" 
            unfolding F_def by auto
          thus False
          proof cases
            case V
            have "total_degree (I g) = 1"
            proof (rule lemma_5_3[OF *(2)[folded *(3)] dv[OF V(1)]])
              show "poly_to_mpoly 0 (v i) = substitute (\<lambda>i. PVar 0) (I g)" 
                unfolding V Iv[OF V(1)] 
                by (intro mpoly_extI, auto simp: insertion_substitute)
            qed force
            with not show False by auto
          next
            case z
            with * have "vars (I g) = {}" by auto
            from vars_empty_Const[OF this] obtain c where "I g = Const c" by auto
            hence "total_degree (I g) = 0" by simp
            with not show False by auto
          qed
        qed
      qed
    qed
    done
qed
end

context poly_input
begin
text \<open>Theorem 5.4 in paper\<close>
theorem polynomial_termination_with_natural_numbers_undecidable: 
  "positive_poly_problem p q \<longleftrightarrow> termination_by_int_poly_interpretation F_S S"
proof
  assume "positive_poly_problem p q" 
  interpret solvable_poly_problem
    by (unfold_locales, fact)
  from solution_imp_poly_termination
  show "termination_by_int_poly_interpretation F_S S" .
next
  assume "termination_by_int_poly_interpretation F_S S" 
  interpret term_poly_input
    by (unfold_locales, fact)
  from solution show "positive_poly_problem p q" .
qed

end

text \<open>Now head for Lemma 5.6\<close>

locale poly_input_omega_solution = poly_input 
begin

fun I :: "symbol \<Rightarrow> int list \<Rightarrow> int" where
  "I o_sym xs = insertion (\<lambda> _. 1) q" 
| "I z_sym xs = 0" 
| "I a_sym xs = xs ! 0 + xs ! 1" 
| "I g_sym xs = (xs ! 1 + 1) * xs ! 0 + xs ! 1" 
| "I h_sym xs = (xs ! 0)^2 + 7 * (xs ! 0) + 4"
| "I f_sym xs = xs ! 2 * xs ! 6 + sum_list xs"  
| "I q_sym xs = 5^(nat (xs ! 0))" 
| "I (v_sym i) xs = xs ! 0" 

lemma I_encode_num: assumes "c \<ge> 0" 
  shows "I\<lbrakk>encode_num x c\<rbrakk>\<alpha> = c * \<alpha> x" 
proof -
  from assms obtain n where cn: "c = int n" by (metis nonneg_eq_int)
  hence natc: "nat c = n" by auto
  show ?thesis unfolding encode_num_def natc unfolding cn
    by (induct n, auto simp: algebra_simps)
qed

lemma I_v_pow_e: "I \<lbrakk>(v_t x ^^ e) t\<rbrakk>\<alpha> = I \<lbrakk>t\<rbrakk>\<alpha>" 
  by (induct e, auto)

lemma I_encode_monom: assumes c: "c \<ge> 0" 
  shows "I\<lbrakk>encode_monom x m c\<rbrakk>\<alpha> = c * \<alpha> x" 
proof -
  define xes where "xes = var_list m" 
  from var_list[of m c] 
  have monom: "mmonom m c = Const c * (\<Prod>(x, e)\<leftarrow> xes . PVar x ^ e) " unfolding xes_def .
  show ?thesis unfolding encode_monom_def monom xes_def[symmetric]
    by (induct xes, auto simp: I_encode_num[OF c] I_v_pow_e)
qed

lemma I_encode_poly: assumes "positive_poly r" 
  shows "I \<lbrakk>encode_poly x r\<rbrakk>\<alpha> = insertion (\<lambda> _. 1) r * \<alpha> x" 
proof -
  define mcs where "mcs = monom_list r" 
  from monom_list[of r] have r: "r = (\<Sum>(m, c)\<leftarrow> mcs. mmonom m c)" unfolding mcs_def by auto
  have mcs: "(m,c) \<in> set mcs \<Longrightarrow> c \<ge> 0" for m c 
    using monom_list_coeff assms unfolding mcs_def positive_poly_def by auto
  show ?thesis unfolding encode_poly_def mcs_def[symmetric] unfolding r insertion_sum_list map_map o_def
    using mcs
  proof (induct mcs)
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    from Cons(2) mc have c: "c \<ge> 0" by auto
    note monom = I_encode_monom[OF this, of x m]
    show ?case
      by (simp add: mc monom algebra_simps, subst Cons(1), insert Cons(2), auto simp: Const_add algebra_simps)
  qed simp
qed
end

lemma length2_cases: "length xs = 2 \<Longrightarrow> \<exists> x y. xs = [x,y]"
  by (cases xs; cases "tl xs", auto)

lemma length7_cases: "length xs = 7 \<Longrightarrow> \<exists> x1 x2 x3 x4 x5 x6 x7. xs = [x1,x2,x3,x4,x5,x6,x7]"
  apply (cases xs, force)
  apply (cases "drop 1 xs", force)
  apply (cases "drop 2 xs", force)
  apply (cases "drop 3 xs", force)
  apply (cases "drop 4 xs", force)
  apply (cases "drop 5 xs", force)
  by (cases "drop 6 xs", force+)

lemma length1_cases: "length xs = Suc 0 \<Longrightarrow> \<exists> x. xs = [x]"
  by (cases xs; auto)

lemma less2_cases: "i < 2 \<Longrightarrow> i = 0 \<or> (i :: nat) = 1" 
  by auto

lemma less7_cases: "i < 7 \<Longrightarrow> i = 0 \<or> (i :: nat) = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i = 6" 
  by auto

context poly_input_omega_solution
begin

sublocale inter_S: term_algebra F_S I "(>)" .
sublocale inter_S: omega_term_algebra F_S I
proof (unfold_locales, unfold inter_S.valid_monotone_inter_def, intro ballI)
  fix fn
  assume "fn \<in> F_S"
  note F = this[unfolded F_S_def F_def]
  show "inter_S.valid_monotone_fun fn" 
    unfolding inter_S.valid_monotone_fun_def
  proof (intro allI impI, clarify)
    fix f n
    assume fn: "fn = (f,n)" 
    note defs = valid_fun_def monotone_fun_wrt_def
    show "valid_fun n (I f) \<and> inter_S.monotone_fun n (I f)"
    proof (cases f)
      case f: a_sym
      with F fn have n: "n = 2" by auto
      show ?thesis unfolding f n
        by (auto simp: defs dest!: length2_cases less2_cases)
    next
      case f: g_sym
      with F fn have n: "n = 2" by auto
      show ?thesis unfolding f n
        by (auto simp: defs dest!: length2_cases less2_cases)
          (smt (verit, ccfv_SIG) mult_mono')
    next
      case f: z_sym
      with F fn have n: "n = 0" by auto
      show ?thesis unfolding f n
        by (auto simp: defs)
    next
      case f: o_sym
      with F fn have n: "n = 0" by auto
      show ?thesis unfolding f n
        by (auto simp: defs intro!: insertion_positive_poly pq)
    next
      case f: f_sym
      with F fn have n: "n = 7" by auto
      show ?thesis unfolding f n
        by (auto simp: defs intro!: add_le_less_mono mult_mono 
            dest!: length7_cases less7_cases)
    next
      case f: (v_sym i)
      with F fn have n: "n = 1" by auto
      show ?thesis unfolding f n
        by (auto simp: defs)
    next
      case f: q_sym
      with F fn have n: "n = 1" by auto
      show ?thesis unfolding f n
        by (auto simp: defs dest: length1_cases)
    next
      case f: h_sym
      with F fn have n: "n = 1" by auto
      show ?thesis unfolding f n
        by (auto simp: defs power2_eq_square dest!: length1_cases)
          (insert mult_strict_mono', fastforce)
    qed
  qed
qed

text \<open>Lemma 5.6\<close>
lemma S_is_omega_terminating: "omega_termination F_S S" 
  unfolding omega_termination_def
proof (intro exI[of _ I] conjI)
  show "omega_term_algebra F_S I" ..
  show "inter_S.termination_by_interpretation S" 
    unfolding inter_S.termination_by_interpretation_def S_def
  proof (clarify, intro conjI)
    show "funas_term lhs_S \<union> funas_term rhs_S \<subseteq> F_S" using lhs_S_F rhs_S_F by auto
    show "inter_S.orient_rule (lhs_S, rhs_S)" unfolding inter_S.orient_rule_def split
    proof (intro allI impI)
      fix \<alpha> :: "var \<Rightarrow> int" 
      assume "assignment \<alpha>" 
      hence \<alpha>: "\<alpha> x \<ge> 0" for x unfolding assignment_def by auto
      from \<alpha>[of y4] obtain n4 where n4: "\<alpha> y4 = int n4"
        using nonneg_int_cases by blast
      define q1 where "q1 = insertion (\<lambda>_. 1) q" 
      have q1: "q1 \<ge> 0" unfolding q1_def using pq(2)
        by (simp add: insertion_positive_poly)
      define p1 where "p1 = insertion (\<lambda>_. 1) p" 
      have p1: "p1 \<ge> 0" unfolding p1_def using pq(1)
        by (simp add: insertion_positive_poly)
      have [simp]: "I\<lbrakk>foldr (\<lambda>i t. Fun (v_sym i) [t]) xs t\<rbrakk>\<alpha> = I\<lbrakk>t\<rbrakk>\<alpha>" for xs t
        by (induct xs, auto)
      define l where "l i = args (lhs_S) ! i" for i
      define r where "r i = args (rhs_S) ! i" for i
      note defs = l_def r_def lhs_S_def rhs_S_def
      have 1: "I\<lbrakk>l 0\<rbrakk>\<alpha> \<ge> I\<lbrakk>r 0\<rbrakk>\<alpha>" unfolding defs by auto
      have 2: "I\<lbrakk>l 1\<rbrakk>\<alpha> \<ge> I\<lbrakk>r 1\<rbrakk>\<alpha>" unfolding defs by auto
      have 5: "I\<lbrakk>l 4\<rbrakk>\<alpha> \<ge> I\<lbrakk>r 4\<rbrakk>\<alpha>" unfolding defs using \<alpha>[of y5] by auto
      have 6: "I\<lbrakk>l 5\<rbrakk>\<alpha> > I\<lbrakk>r 5\<rbrakk>\<alpha>" unfolding defs using \<alpha>[of y6] by (auto simp: power2_eq_square)
      have 7: "I\<lbrakk>l 6\<rbrakk>\<alpha> \<ge> I\<lbrakk>r 6\<rbrakk>\<alpha>" unfolding defs using \<alpha>[of y7] q1 
        by (auto simp: q1_def[symmetric] field_simps)

      have n44: "n4 * 4 = n4 + n4 + n4 + n4" by simp
      have r3: "I\<lbrakk>r 3\<rbrakk>\<alpha> = 1 * 5^(4 * n4) + 14 * 5^(3 * n4) + 64 * 5^(2 * n4) + 105 * 5^n4 + 48 * 5^0" 
        unfolding defs by (simp add: n4 field_simps power_mult power2_eq_square)
         (simp flip: power_add power_mult add: field_simps n44)
      let ?large = "125 * 5^(n4^2 + 7 * n4)" 
      have l3: "I\<lbrakk>l 3\<rbrakk>\<alpha> = ?large + ?large + ?large + ?large + ?large" 
        unfolding defs by (simp add: n4 power2_eq_square nat_add_distrib nat_mult_distrib power_add)
      have 4: "I\<lbrakk>l 3\<rbrakk>\<alpha> \<ge> I\<lbrakk>r 3\<rbrakk>\<alpha>" unfolding l3 r3
        by (intro add_mono mult_mono power_increasing, auto)
 
      have "I\<lbrakk>r 2\<rbrakk>\<alpha> * I\<lbrakk>r 6\<rbrakk>\<alpha> + I\<lbrakk>r 2\<rbrakk>\<alpha>
        = ((q1 + 1) * \<alpha> y7 + q1 + 1) * \<alpha> y3" 
        unfolding defs by (simp add: I_encode_poly[OF pq(2)] q1_def field_simps)
      also have "\<dots> \<le> ((q1 + 1) * \<alpha> y7 + q1 + 1) * ((p1 + 1) * \<alpha> y3)" 
        by (rule mult_left_mono, insert p1 q1 \<alpha>, auto simp: field_simps)
      also have "\<dots> = I\<lbrakk>l 2\<rbrakk>\<alpha> * I\<lbrakk>l 6\<rbrakk>\<alpha> + I\<lbrakk>l 2\<rbrakk>\<alpha>" 
        unfolding defs by (simp add: I_encode_poly[OF pq(1)] q1_def p1_def field_simps)
      finally have 37: "I\<lbrakk>l 2\<rbrakk>\<alpha> * I\<lbrakk>l 6\<rbrakk>\<alpha> + I\<lbrakk>l 2\<rbrakk>\<alpha> \<ge> I\<lbrakk>r 2\<rbrakk>\<alpha> * I\<lbrakk>r 6\<rbrakk>\<alpha> + I\<lbrakk>r 2\<rbrakk>\<alpha>" .

      have lhs: "lhs_S = Fun f_sym (map l [0,1,2,3,4,5,6])" unfolding lhs_S_def l_def by simp
      have rhs: "rhs_S = Fun f_sym (map r [0,1,2,3,4,5,6])" unfolding rhs_S_def r_def by simp
      have "I\<lbrakk>rhs_S\<rbrakk>\<alpha> = (I\<lbrakk>r 2\<rbrakk>\<alpha> * I\<lbrakk>r 6\<rbrakk>\<alpha> + I\<lbrakk>r 2\<rbrakk>\<alpha>) + 
           (I\<lbrakk>r 0\<rbrakk>\<alpha> + I\<lbrakk>r 1\<rbrakk>\<alpha> + I\<lbrakk>r 3\<rbrakk>\<alpha> + I\<lbrakk>r 4\<rbrakk>\<alpha> + I\<lbrakk>r 6\<rbrakk>\<alpha>) + I\<lbrakk>r 5\<rbrakk>\<alpha>" 
        unfolding rhs by simp
      also have "\<dots> < (I\<lbrakk>l 2\<rbrakk>\<alpha> * I\<lbrakk>l 6\<rbrakk>\<alpha> + I\<lbrakk>l 2\<rbrakk>\<alpha>) + 
           (I\<lbrakk>l 0\<rbrakk>\<alpha> + I\<lbrakk>l 1\<rbrakk>\<alpha> + I\<lbrakk>l 3\<rbrakk>\<alpha> + I\<lbrakk>l 4\<rbrakk>\<alpha> + I\<lbrakk>l 6\<rbrakk>\<alpha>) + I\<lbrakk>l 5\<rbrakk>\<alpha>" 
        apply (rule add_le_less_mono[OF _ 6])
        apply (rule add_mono[OF 37])
        by (intro add_mono 1 2 4 5 7)
      also have "\<dots> = I\<lbrakk>lhs_S\<rbrakk>\<alpha>" unfolding lhs by simp
      finally show "I\<lbrakk>lhs_S\<rbrakk>\<alpha> > I\<lbrakk>rhs_S\<rbrakk>\<alpha>" .
    qed
  qed
qed  
end

end