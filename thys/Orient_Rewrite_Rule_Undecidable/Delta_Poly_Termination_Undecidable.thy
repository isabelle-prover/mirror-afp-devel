section \<open>Undecidability of Polynomial Termination using \<open>\<delta>\<close>-Orders\<close>

theory Delta_Poly_Termination_Undecidable
  imports 
    Poly_Termination_Undecidable
begin

context poly_input
begin

definition y8 :: var where "y8 = 7" 
definition y9 :: var where "y9 = 8" 

text \<open>Definition 6.3\<close>

definition "lhs_Q = Fun f_sym [
  q_t (h_t (Var y1)), 
  h_t (Var y2),
  h_t (Var y3),
  g_t (q_t (Var y4)) (h_t (h_t (h_t (Var y4)))),
  q_t (Var y5),
  a_t (Var y6) (Var y6),
  Var y7,
  Var y8,
  h_t (a_t (encode_poly y9 p) (Var y9))]"

fun g_list :: "_ \<Rightarrow> (symbol,var)term" where 
  "g_list [] = z_t" 
| "g_list ((f,n) # fs) = g_t (Fun f (replicate n z_t)) (g_list fs)" 

definition symbol_list where "symbol_list = [(f_sym,9),(q_sym,1),(h_sym,1),(a_sym,2)] @ map (\<lambda> i. (v_sym i, 1)) V_list" 

definition t_t :: "(symbol,var)term" where "t_t = (g_list ((z_sym,0) # symbol_list))"

definition "rhs_Q = Fun f_sym [
  h_t (h_t (q_t (Var y1))),
  g_t (Var y2) (Var y2),
  Fun f_sym (replicate 9 (Var y3)),
  q_t (g_t (Var y4) t_t),
  a_t (Var y5) (Var y5),
  q_t (Var y6),
  a_t z_t (Var y7),
  a_t (Var y8) z_t,
  a_t (encode_poly y9 q) (Var y9)]"

definition Q where "Q = {(lhs_Q, rhs_Q)}" 

definition F_Q where "F_Q = {(f_sym,9), (h_sym,1), (g_sym,2), (q_sym,1)} \<union> F" 

lemma lhs_Q_F: "funas_term lhs_Q \<subseteq> F_Q" 
proof - 
  from funas_encode_poly_p
  show "funas_term lhs_Q \<subseteq> F_Q" unfolding lhs_Q_def by (auto simp: F_Q_def F_def)
qed

lemma g_list_F: "set zs \<subseteq> F_Q \<Longrightarrow> funas_term (g_list zs) \<subseteq> F_Q" 
proof (induct zs)
  case Nil
  thus ?case by (auto simp: F_Q_def F_def)
next
  case (Cons fa ts)
  then obtain f a where fa: "fa = (f,a)" and inF: "(f,a) \<in> F_Q" by (cases fa, auto)
  have "{(g_sym,Suc (Suc 0)),(z_sym,0)} \<subseteq> F_Q" by (auto simp: F_Q_def F_def)
  with Cons fa inF show ?case by auto
qed

lemma symbol_list: "set symbol_list \<subseteq> F_Q" unfolding symbol_list_def F_Q_def F_def using V_list by auto

lemma t_F: "funas_term t_t \<subseteq> F_Q" 
  unfolding t_t_def using g_list_F[OF symbol_list] 
  by (auto simp: F_Q_def F_def)

lemma vars_g_list[simp]: "vars_term (g_list zs) = {}" 
  by (induct zs, auto)

lemma vars_t: "vars_term t_t = {}" 
  unfolding t_t_def by simp


lemma rhs_Q_F: "funas_term rhs_Q \<subseteq> F_Q" 
proof - 
  from funas_encode_poly_q
  show "funas_term rhs_Q \<subseteq> F_Q" unfolding rhs_Q_def using t_F by (auto simp: F_Q_def F_def)
qed

context
  fixes I :: "symbol \<Rightarrow> 'a :: linordered_field mpoly" and \<delta> :: 'a and a3 a2 a1 a0 z0 v
  assumes I: "I a_sym = Const a3 * PVar 0 * PVar 1 + Const a2 * PVar 0 + Const a1 * PVar 1 + Const a0" 
    "I z_sym = Const z0" 
    "I (v_sym i) = mpoly_of_poly 0 (v i)"
  and a: "a3 > 0" "a2 > 0" "a1 > 0" "a0 \<ge> 0" 
  and z: "z0 \<ge> 0" 
  and v: "nneg_poly (v i)" "degree (v i) > 0" 
begin

lemma nneg_combination: assumes "nneg_poly r" 
  shows "nneg_poly ([:a1, a3:] * r + [:a0, a2:])" 
  by (intro nneg_poly_add nneg_poly_mult assms, insert a, auto)

lemma degree_combination: assumes "nneg_poly r"
  shows "degree ([:a1, a3:] * r + [:a0, a2:]) = Suc (degree r)"
  using nneg_poly_degree_add_1[OF assms, OF a(1) a(2)] by auto

lemma degree_eval_encode_num: assumes c: "c \<ge> 0" 
  shows "\<exists> p. mpoly_of_poly x p = poly_inter.eval I (encode_num x c) \<and> nneg_poly p \<and> int (degree p) = c"
proof -
  interpret poly_inter UNIV I . 
  from assms obtain n where cn: "c = int n" by (metis nonneg_eq_int)
  hence natc: "nat c = n" by auto
  note [simp] = I
  show ?thesis unfolding encode_num_def natc unfolding cn int_int_eq 
  proof (induct n)
    case 0
    show ?case using z by (auto simp: intro!: exI[of _ "[:z0:]"])
  next
    case (Suc n)
    define t where "t = (((\<lambda>t. Fun a_sym [TVar x, t]) ^^ n) (Fun z_sym []))" 
    from Suc obtain p where mp: "mpoly_of_poly x p = eval t" 
      and deg: "degree p = n" and p: "nneg_poly p" by (auto simp: t_def)
    show ?case apply (simp add: t_def[symmetric])
      apply (unfold deg[symmetric])
      apply (intro exI[of _ "[: a1, a3:] * p + [:a0, a2:]"] conjI mpoly_extI degree_combination p nneg_combination)
      by (simp add: mp insertion_add insertion_mult field_simps)
  qed
qed

lemma degree_eval_encode_monom: assumes c: "c > 0"
  and \<alpha>: "\<alpha> = (\<lambda> i. int (degree (v i)))" 
shows "\<exists> p. mpoly_of_poly y p = poly_inter.eval I (encode_monom y m c) \<and> nneg_poly p \<and> 
     int (degree p) = insertion \<alpha> (mmonom m c) \<and> degree p > 0" 
proof -
  interpret poly_inter UNIV I . 
  define xes where "xes = var_list m" 
  from var_list[of m c]
  have monom: "mmonom m c = Const c * (\<Prod>(x, e)\<leftarrow> xes . PVar x ^ e) " unfolding xes_def .
  show ?thesis unfolding encode_monom_def monom xes_def[symmetric]
  proof (induct xes)
    case Nil
    show ?case using degree_eval_encode_num[of c y] c by auto
  next
    case (Cons xe xes)
    obtain x e where xe: "xe = (x,e)" by force
    define expr where "expr = rec_list (encode_num y c) (\<lambda>a. case a of (i, e) \<Rightarrow> \<lambda>_. (\<lambda>t. Fun (v_sym i) [t]) ^^ e)" 
    define exes where "exes = expr xes" 
    define ixes where "ixes = insertion \<alpha> (Const c * (\<Prod>a\<leftarrow> xes. case a of (x, a) \<Rightarrow> PVar x ^ a))" 
    have step: "expr (xe # xes) = ((\<lambda>t. Fun (v_sym x) [t]) ^^ e) (exes)" 
      unfolding xe expr_def exes_def by auto
    have step': "insertion \<alpha> (Const c * (\<Prod>a\<leftarrow>xe # xes. case a of (x, a) \<Rightarrow> PVar x ^ a))
      = (\<alpha> x)^e * ixes" 
      unfolding xe ixes_def by (simp add: insertion_mult insertion_power)
    from Cons(1)[folded expr_def exes_def ixes_def] obtain p where
      IH: "mpoly_of_poly y p = eval exes" "nneg_poly p" 
      "int (degree p) = ixes" "degree p > 0" 
      by auto
    show ?case 
      unfolding expr_def[symmetric] 
      unfolding step step'
    proof (induct e)
      case 0
      thus ?case using IH by auto
    next
      case (Suc e)
      define rec where "rec = ((\<lambda>t. Fun (v_sym x) [t]) ^^ e) exes" 
      from Suc[folded rec_def] obtain p where
        IH: "mpoly_of_poly y p = eval rec" "nneg_poly p" "int (degree p) = \<alpha> x ^ e * ixes" "degree p > 0" by auto
      have "((\<lambda>t. Fun (v_sym x) [t]) ^^ Suc e) exes = Fun (v_sym x) [rec]" 
        unfolding rec_def by simp
      also have "eval \<dots> = substitute (\<lambda>i. if i = 0 then eval ([rec] ! i) else 0) (poly_to_mpoly 0 (v x))" 
        by (simp add: I mpoly_of_poly_is_poly_to_mpoly)
      also have "\<dots> = poly_to_mpoly y (v x \<circ>\<^sub>p p)" 
        by (rule substitute_poly_to_mpoly, auto simp: IH(1)[symmetric] mpoly_of_poly_is_poly_to_mpoly)
      finally have id: "eval (((\<lambda>t. Fun (v_sym x) [t]) ^^ Suc e) exes) = poly_to_mpoly y (v x \<circ>\<^sub>p p)" .
      show ?case unfolding id mpoly_of_poly_is_poly_to_mpoly
      proof (intro exI[of _ "v x \<circ>\<^sub>p p"] conjI refl)
        show "int (degree (v x \<circ>\<^sub>p p)) = \<alpha> x ^ Suc e * ixes" 
          unfolding degree_pcompose using IH(3) by (auto simp: \<alpha>)
        show "nneg_poly (v x \<circ>\<^sub>p p)" using IH(2) v[of x]
          by (intro nneg_poly_pcompose, insert IH, auto)
        show "0 < degree (v x \<circ>\<^sub>p p)" unfolding degree_pcompose using IH(4) v[of x] by auto
      qed
    qed
  qed
qed

text \<open>Lemma 6.2\<close>
lemma degree_eval_encode_poly_generic: assumes "positive_poly r" 
  and \<alpha>: "\<alpha> = (\<lambda> i. int (degree (v i)))" 
shows "\<exists> p. poly_to_mpoly x p = poly_inter.eval I (encode_poly x r) \<and> nneg_poly p \<and> 
     int (degree p) = insertion \<alpha> r" 
proof -
  interpret poly_inter UNIV I . 
  define mcs where "mcs = monom_list r" 
  from monom_list[of r] have r: "r = (\<Sum>(m, c)\<leftarrow> mcs. mmonom m c)" unfolding mcs_def by auto
  {
    fix m c
    assume mc: "(m,c) \<in> set mcs" 
    hence "c \<ge> 0"  
      using monom_list_coeff assms unfolding mcs_def positive_poly_def by auto
    moreover from mc have "c \<noteq> 0" unfolding mcs_def
      by (transfer, auto)
    ultimately have "c > 0" by auto
  } note mcs = this
  note [simp] = I
  show ?thesis unfolding encode_poly_def mcs_def[symmetric] unfolding r insertion_sum_list map_map o_def
    unfolding mpoly_of_poly_is_poly_to_mpoly[symmetric]
    using mcs
  proof (induct mcs)
    case Nil
    show ?case by (rule exI[of _ "[:z0:]"], insert z, auto)
  next
    case (Cons mc mcs)
    define trm where "trm = rec_list (Fun z_sym []) (\<lambda>a. case a of (m, c) \<Rightarrow> \<lambda>_ t. Fun a_sym [encode_monom x m c, t])" 
    define expr where "expr mcs = (\<Sum>x\<leftarrow>mcs. insertion \<alpha> (case x of (x, xa) \<Rightarrow> mmonom x xa))" for mcs
    obtain m c where mc: "mc = (m,c)" by force
    from Cons(2) mc have c: "c > 0" by auto
    from degree_eval_encode_monom[OF this \<alpha>, of x m]
    obtain q where monom: "mpoly_of_poly x q = eval (encode_monom x m c)"
       "nneg_poly q" "int (degree q) = insertion \<alpha> (mmonom m c)" 
       and dq: "degree q > 0" by auto 
    from Cons(1)[folded trm_def expr_def, OF Cons(2)]
    obtain p where IH: "mpoly_of_poly x p = eval (trm mcs)" "nneg_poly p" "int (degree p) = expr mcs" by force
    have step: "trm (mc # mcs) = Fun a_sym [encode_monom x m c, trm mcs]" 
      unfolding mc trm_def by simp
    have step': "expr (mc # mcs) = insertion \<alpha> (mmonom m c) + expr mcs" unfolding mc expr_def by simp 
    have deg: "degree ([:a3:] * q * p + ([:a2:] * q + [:a1:] * p + [:a0:])) = degree p + degree q" 
      by (rule nneg_poly_degree_add, insert a IH monom, auto)
    show ?case unfolding expr_def[symmetric] trm_def[symmetric]
      unfolding step step'
      unfolding IH(3)[symmetric] monom(3)[symmetric]
      apply (intro exI[of _ "[:a3:] * q * p + [:a2:] * q + [:a1:] * p + [:a0:]"] conjI)
      subgoal by (intro mpoly_extI, simp add: IH(1)[symmetric] monom(1)[symmetric] insertion_mult insertion_add)
      subgoal by (intro nneg_poly_mult nneg_poly_add IH monom, insert a, auto)
      subgoal using deg by (auto simp: ac_simps)
      done
  qed
qed
end
end

context delta_poly_inter
begin

lemma transp_gt_delta: "transp (\<lambda> x y. x \<ge> y + \<delta>)" using \<delta>0
  by (auto simp: transp_def)

lemma gt_delta_imp_ge: "y + \<delta> \<le> x \<Longrightarrow> y \<le> x" using \<delta>0 by auto

lemma weakly_monotone_insertion: assumes mono: "monotone_poly (vars p) p"
  and a: "assignment (a :: _ \<Rightarrow> 'a)" 
  and gt: "\<And> x. x \<in> vars p \<Longrightarrow> a x + \<delta> \<le> b x"
shows "insertion a p \<le> insertion b p" 
  using monotone_poly_wrt_insertion[OF transp_gt_delta gt_delta_imp_ge mono a, of b] gt \<delta>0 by auto

text \<open>Lemma 6.5\<close>
lemma degree_partial_insertion_stays_constant: assumes mono: "monotone_poly (vars p) p" 
  shows "\<exists> a. assignment a \<and> 
  (\<forall> b. (\<forall> y. a y + \<delta> \<le> b y) \<longrightarrow> degree (partial_insertion a x p) = degree (partial_insertion b x p))" 
  using degree_partial_insertion_stays_constant_generic
    [OF transp_gt_delta gt_delta_imp_ge poly_pinfty_ge mono, of \<delta> x, simplified]
  by metis

lemma degree_mono: assumes pos: "lead_coeff p \<ge> (0 :: 'a)"
  and le: "\<And> x. x \<ge> c \<Longrightarrow> poly p x \<le> poly q x"
shows "degree p \<le> degree q" 
  by (rule degree_mono_generic[OF poly_pinfty_ge assms])

lemma degree_mono': assumes "\<And> x. x \<ge> c \<Longrightarrow> (bnd :: 'a) \<le> poly p x \<and> poly p x \<le> poly q x" 
  shows "degree p \<le> degree q" 
  by (rule degree_mono'_generic[OF poly_pinfty_ge assms])


text \<open>Lemma 6.6\<close>
lemma subst_same_var_monotone_imp_same_degree: 
  assumes mono: "monotone_poly (vars p) (p :: 'a mpoly)" 
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
  with mpoly_ext_bounded_field[of "max 1 \<delta>" p1 0] obtain b
    where b: "\<And> v. b v \<ge> max 1 \<delta>" and bpm0: "insertion b p1 \<noteq> 0" by auto
  from b have b1: "\<And> v. b v \<ge> 1" and b\<delta>: "\<And> v. b v \<ge> \<delta>" by auto
  define c where "c = Max (insert 1 (b ` vars p)) + \<delta>" 
  define X where "X = (0 :: nat)" 
  define pb where "pb p = mpoly_to_poly X (substitute (\<lambda> v. Const (b v) * PVar X) p)" for p
  have c1: "c \<ge> 1" unfolding c_def using vars_finite[of p] \<delta>0 Max_ge[of _ "1 :: 'a"]
    by (meson add_increasing2 finite.insertI finite_imageI insertI1 nless_le)
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
    fix x :: 'a
    assume x1: "x \<ge> 1" 
    hence x: "x \<ge> 0" by simp
    have ass: "assignment (\<lambda> v. b v * x)" unfolding assignment_def using x b1
      by (meson linorder_not_le mult_le_cancel_right1 order_trans)
    have "poly (pb p) x = insertion (\<lambda>v. b v * x) p" by fact
    also have "insertion (\<lambda> v. b v * x) p \<le> insertion (\<lambda> v. c * x) p"
    proof (rule weakly_monotone_insertion[OF mono ass])
      fix v
      assume v: "v \<in> vars p" 
      have "b v + \<delta> \<le> c" unfolding c_def using vars_finite[of p] v Max_ge[of _ "b v"] by auto
      thus "b v * x + \<delta> \<le> c * x" using b[of v] x1 c1 \<delta>0
        by (smt (verit) c_def add_le_imp_le_right add_mono comm_semiring_class.distrib mult.commute mult_le_cancel_right1 mult_right_mono order.asym x)
    qed
    also have "\<dots> = poly q (c * x)" unfolding poly_to_mpoly_substitute_same[OF qp] ..
    also have "\<dots> = poly (q \<circ>\<^sub>p [:0, c:]) x" by (simp add: poly_pcompose ac_simps)
    finally have ineq: "poly (pb p) x \<le> poly (q \<circ>\<^sub>p [:0, c:]) x" .
    have "bnd \<le> insertion (\<lambda>v. b v * x) p" unfolding bnd_def
      apply (intro weakly_monotone_insertion[OF mono])
      subgoal by (simp add: assignment_def)
      subgoal for v using b\<delta>[of v] x1 \<delta>0 
        by simp (metis dual_order.trans less_le_not_le mult_le_cancel_left1)
      done
    also have "\<dots> = poly (pb p) x" using poly_pb by auto
    finally have "bnd \<le> poly (pb p) x" by auto 
    note this ineq
  } note pb_approx = this
  have "M = degree (pb p)" unfolding deg_pbp ..
  also have "\<dots> \<le> degree (q \<circ>\<^sub>p [:0, c:])"
    by (intro degree_mono'[of 1 bnd], insert pb_approx, auto)
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
   "valid_poly p \<Longrightarrow> y \<ge> 0 \<Longrightarrow> poly (partial_insertion a x p) y \<ge> y - \<delta>" 
   "valid_poly p \<Longrightarrow> insertion a p \<ge> a x - \<delta>" 
proof - 
  have 0: "1 \<le> inverse \<delta> * \<delta>" using \<delta>0 by auto
  define ceil_nat :: "'a \<Rightarrow> nat" where "ceil_nat x = nat (ceiling x)" for x
  have 1: "x \<le> of_nat (ceil_nat x)" for x unfolding ceil_nat_def
    by (simp add: of_nat_ceiling)
  note main = monotone_poly_partial_insertion_generic[OF transp_gt_delta gt_delta_imp_ge poly_pinfty_ge refl \<delta>0 0 1 x mono ass, simplified]
  show "0 < degree (partial_insertion a x p)" "0 < lead_coeff (partial_insertion a x p)" 
    using main by auto
  assume valid: "valid_poly p" 
  from main(3)[OF this] have estimation: "\<delta> * of_nat y \<le> poly (partial_insertion a x p) (\<delta> * of_nat y)" for y by auto
  {
    fix y :: 'a
    assume y: "y \<ge> 0" 
    with ass have ass': "assignment (a(x := y))" unfolding assignment_def by auto
    from valid[unfolded valid_poly_def, rule_format, OF ass']
    have ge0: "insertion (a(x := y)) p \<ge> 0" by auto
    have id: "poly (partial_insertion a x p) y = insertion (a(x := y)) p" 
      using insertion_partial_insertion[of x a "a(x:=y)" p] by auto
    show "y - \<delta> \<le> poly (partial_insertion a x p) y" 
    proof (cases "y \<ge> \<delta>")
      case False
      with ge0[folded id] y show ?thesis by auto
    next
      case True
      define z where "z = y - \<delta>" 
      from True have z0: "z \<ge> 0" unfolding z_def by auto
      define n where "n = nat (floor (z * inverse \<delta>))"
      have "\<delta> * of_nat n \<le> z" unfolding n_def using \<delta>0 z0
        by (metis field_class.field_divide_inverse mult_of_nat_commute mult_zero_left of_nat_floor pos_le_divide_eq)
      hence gt: "\<delta> * of_nat n + \<delta> \<le> y" unfolding z_def by auto

      define b where "b = a(x := \<delta> * of_nat n)"
      have ass_b: "assignment b" using \<delta>0 ass unfolding b_def assignment_def by auto
      from mono[unfolded monotone_poly_wrt_def, rule_format, OF ass_b x, of y] gt
      have gt: "insertion b p \<le> insertion (b(x := y)) p - \<delta>" by (auto simp: b_def)
      
      have "\<delta> * of_nat n + \<delta> \<ge> z" unfolding n_def using \<delta>0 z0
        by (smt (verit, del_insts) comm_semiring_class.distrib field_class.field_divide_inverse floor_divide_upper inverse_nonnegative_iff_nonnegative mult.commute mult_cancel_left2 mult_nonneg_nonneg of_nat_nat order_less_le z_def z_def z_def zero_le_floor)  
      hence "y - 2 * \<delta> \<le> \<delta> * of_nat n" unfolding z_def by auto
      also have "\<delta> * of_nat n \<le> poly (partial_insertion a x p) (\<delta> * of_nat n)" 
        by fact
      also have "\<dots> = insertion b p" using insertion_partial_insertion[of x a b p]
        by (auto simp: b_def)
      also have "\<dots> \<le> insertion (b(x := y)) p - \<delta>" by fact
      also have "insertion (b(x := y)) p = poly (partial_insertion a x p) y" 
        using insertion_partial_insertion[of x a "b(x := y)" p] 
        by (auto simp: b_def)
      finally show ?thesis by simp
    qed
  } note estimation = this
  from ass have "a x \<ge> 0" unfolding assignment_def by auto
  from estimation[OF this] show "insertion a p \<ge> a x - \<delta>" 
    using insertion_partial_insertion[of x a a p] by auto
qed
end

context solvable_poly_problem
begin

context 
  assumes "SORT_CONSTRAINT('a :: floor_ceiling)" 
begin

context
  fixes h :: 'a
begin

fun IQ :: "symbol \<Rightarrow> 'a mpoly" where 
  "IQ f_sym = PVar 0 + PVar 1 + PVar 2 + PVar 3 + PVar 4 + PVar 5 + PVar 6 + PVar 7 + PVar 8" 
| "IQ a_sym = PVar 0 * PVar 1 + PVar 0 + PVar 1"
| "IQ z_sym = 0" 
| "IQ (v_sym i) = PVar 0 ^ (nat (\<alpha> i))" 
| "IQ q_sym = PVar 0 * PVar 0 + Const 2 * PVar 0" 
| "IQ g_sym = PVar 0 + PVar 1" 
| "IQ h_sym = Const h * PVar 0 + Const h" 
| "IQ o_sym = 0" 

interpretation interQ: poly_inter F_Q IQ "(\<lambda>x y. x \<ge> y + (1 :: 'a))" .

text \<open>Lemma 6.2 specialized for this interpretation\<close>
lemma degree_eval_encode_poly: assumes "positive_poly r" 
  shows "\<exists>p. poly_to_mpoly y9 p = interQ.eval (encode_poly y9 r) \<and> nneg_poly p \<and> int (degree p) = insertion \<alpha> r" 
proof -
  define v where "v i = (monom 1 (nat (\<alpha> i)) :: 'a poly)" for i
  define \<gamma> where "\<gamma> = (\<lambda>i. int (degree (v i)))"
  have nneg_v: "nneg_poly (v i)" "0 < degree (v i)" for i unfolding v_def using \<alpha>1[of i] 
    by (auto simp: nneg_poly_def degree_monom_eq poly_monom)
  have id: "int (Polynomial.degree (v i)) = \<alpha> i" for i unfolding v_def 
    using \<alpha>1[of i] by (auto simp: nneg_poly_def degree_monom_eq)
  have "IQ (v_sym i) = mpoly_of_poly 0 (v i)" for i
    unfolding v_def by (intro mpoly_extI, simp add: insertion_power poly_monom)
  from degree_eval_encode_poly_generic[of IQ 1 1 1 0 0 v _ \<gamma>, OF _ _ this, simplified, OF nneg_v assms \<gamma>_def, 
      unfolded id]
  show ?thesis by auto
qed

definition pp where "pp = (SOME pp. poly_to_mpoly y9 pp = interQ.eval (encode_poly y9 p) \<and> nneg_poly pp \<and> int (degree pp) = insertion \<alpha> p)" 

lemma pp: "interQ.eval (encode_poly y9 p) = poly_to_mpoly y9 pp" 
  "nneg_poly pp" "int (degree pp) = insertion \<alpha> p" 
  using someI_ex[OF degree_eval_encode_poly[OF pq(1)], folded pp_def] by auto

definition qq where "qq = (SOME qq. poly_to_mpoly y9 qq = interQ.eval (encode_poly y9 q) \<and> nneg_poly qq \<and> int (degree qq) = insertion \<alpha> q)" 

lemma qq: "interQ.eval (encode_poly y9 q) = poly_to_mpoly y9 qq" 
  "nneg_poly qq" "int (degree qq) = insertion \<alpha> q" 
  using someI_ex[OF degree_eval_encode_poly[OF pq(2)], folded qq_def] by auto

definition "ppp = pp * [:1,1:] + [:0,1:]" 
definition "qqq = qq * [:1,1:] + [:0,1:]" 

lemma degree_ppp: "int (degree ppp) = 1 + insertion \<alpha> p" 
  unfolding ppp_def pp(3)[symmetric] 
  using nneg_poly_degree_add_1[OF pp(2), of 1 1 1 0] by simp

lemma degree_qqq: "int (degree qqq) = 1 + insertion \<alpha> q" 
  unfolding qqq_def qq(3)[symmetric] 
  using nneg_poly_degree_add_1[OF qq(2), of 1 1 1 0] by simp

lemma ppp_qqq: "degree ppp \<ge> degree qqq" 
  using degree_ppp degree_qqq \<alpha>(2) by auto

lemma nneg_ppp: "nneg_poly ppp" 
  unfolding ppp_def
  by (intro nneg_poly_add nneg_poly_mult pp, auto)

definition H where "H = (SOME H. \<forall> h \<ge> H. \<forall>x\<ge>0. poly qqq x \<le> h * poly ppp x + h)" 

lemma H: "h \<ge> H \<Longrightarrow> x \<ge> 0 \<Longrightarrow> poly qqq x \<le> h * poly ppp x + h" 
proof -
  from poly_degree_le_large_const[OF ppp_qqq nneg_poly_nneg[OF nneg_ppp]]
  have "\<exists>H. \<forall>h\<ge>H. \<forall>x\<ge>0. poly qqq x \<le> h * poly ppp x + h" by auto
  from someI_ex[OF this, folded H_def]
  show "h \<ge> H \<Longrightarrow> x \<ge> 0 \<Longrightarrow> poly qqq x \<le> h * poly ppp x + h" by auto
qed
end

definition h where "h = max 9 (H 1)" 

lemma h: "h \<ge> 1" unfolding h_def by auto

abbreviation I_Q where "I_Q \<equiv> IQ h" 

interpretation inter_Q: poly_inter F_Q I_Q "(\<lambda>x y. x \<ge> y + (1 :: 'a))" .

text \<open>Well-definedness of Interpretation in Theorem 6.4\<close>

lemma valid_monotone_inter_Q: 
  "inter_Q.valid_monotone_poly_inter" 
  unfolding inter_Q.valid_monotone_poly_inter_def 
proof (intro ballI)
  note [simp] = insertion_add insertion_mult
  fix fn
  assume f: "fn \<in> F_Q" 
  then consider 
    (a) "fn = (a_sym,2)" 
    | (g) "fn = (g_sym,2)" 
    | (h) "fn = (h_sym,1)" 
    | (q) "fn = (q_sym,1)" 
    | (f) "fn = (f_sym,9)" 
    | (z) "fn = (z_sym,0)" 
    | (v) i where "fn = (v_sym i, 1)" "i \<in> V" 
    unfolding F_Q_def F_def by auto    
  thus "inter_Q.valid_monotone_poly fn"
  proof cases
    case *: a
    have vars: "vars (PVar 0 * PVar 1 + PVar 0 + PVar 1 :: 'a mpoly) = {0,1}" 
      apply (intro vars_eqI)
      subgoal by (intro vars_mult_subI vars_add_subI, auto) 
      subgoal for v by (intro exI[of _ "\<lambda> _. 1"] exI[of _ 0], auto)
      done
    show ?thesis unfolding inter_Q.valid_monotone_poly_def *
      apply (intro allI impI, clarify, unfold IQ.simps vars valid_poly_def
          monotone_poly_wrt_def 
          insertion_mult insertion_add insertion_Var,
          intro conjI allI impI)
      subgoal for \<alpha> unfolding assignment_def by simp
      subgoal for _ _ _ \<alpha> x v 
      proof goal_cases 
        case 1
        from assignmentD[OF 1(1)] have 0: "\<alpha> 0 \<ge> 0" "\<alpha> 1 \<ge> 0" by auto
        from 1 have "x = 0 \<or> x = 1" by auto
        thus ?case using 0 1(3) mult_right_mono[OF 1(3), of "\<alpha> (x - 1)"] 
          by (auto simp: field_simps)
            (smt (verit, ccfv_threshold) "1"(3) add.assoc add.commute add_increasing add_le_imp_le_right add_right_mono diff_ge_0_iff_ge le_add_diff_inverse2 mult_right_mono zero_less_one_class.zero_le_one)
      qed
      subgoal by auto
      done
  next
    case *: f
    have vars: "vars (PVar 0 + PVar 1 + PVar 2 + PVar 3 + PVar 4 + PVar 5 + PVar 6 + PVar 7 + PVar 8 :: 'a mpoly) = {0,1,2,3,4,5,6,7,8}" 
      apply (intro vars_eqI)
      subgoal by (intro vars_mult_subI vars_add_subI, auto) 
      subgoal for v by (intro exI[of _ "\<lambda> _. 1"] exI[of _ 0], auto)
      done
    show ?thesis unfolding inter_Q.valid_monotone_poly_def *
      apply (intro allI impI, clarify, unfold IQ.simps vars valid_poly_def
          monotone_poly_wrt_def 
          insertion_mult insertion_add insertion_Var,
          intro conjI allI impI)
      subgoal for \<alpha> unfolding assignment_def by simp
      subgoal for _ _ _ \<alpha> x v 
      proof goal_cases 
        case 1
        hence "x \<in> {0,1,2,3,4,5,6,7,8}" by auto
        thus ?case using 1(3) by auto
      qed
      subgoal by auto
      done
  next
    case *: h
    have vars: "vars (Const h * PVar 0 + Const h :: 'a mpoly) = {0}" 
      apply (intro vars_eqI)
      subgoal by (intro vars_mult_subI vars_add_subI, auto) 
      subgoal for v using h by (intro exI[of _ "\<lambda> _. 1"] exI[of _ 0], auto)
      done
    show ?thesis unfolding inter_Q.valid_monotone_poly_def *
      apply (intro allI impI, clarify, unfold IQ.simps vars valid_poly_def
          monotone_poly_wrt_def 
          insertion_mult insertion_add insertion_Var,
          intro conjI allI impI)
      subgoal for \<alpha> using h unfolding assignment_def by simp
      subgoal for _ _ _ \<alpha> x v 
      proof goal_cases 
        case 1
        from assignmentD[OF 1(1), of 0]
        show ?case using 1 h 
          by (auto simp: field_simps)
            (smt (verit, ccfv_threshold) add.commute add_le_cancel_left distrib_left linordered_nonzero_semiring_class.zero_le_one mult.commute mult_cancel_left1 mult_left_mono nle_le order_trans)
      qed
      subgoal by auto
      done
  next
    case z
    thus ?thesis by (auto simp: inter_Q.valid_monotone_poly_def valid_poly_def monotone_poly_wrt_def)
  next
    case *: g
    have vars: "vars (PVar 0 + PVar 1 :: 'a mpoly) = {0,1}" 
      apply (intro vars_eqI)
      subgoal by (intro vars_mult_subI vars_add_subI, auto) 
      subgoal for v by (intro exI[of _ "\<lambda> _. 1"] exI[of _ 0], auto)
      done
    show ?thesis unfolding inter_Q.valid_monotone_poly_def *
      apply (intro allI impI, clarify, unfold IQ.simps vars valid_poly_def
          monotone_poly_wrt_def 
          insertion_mult insertion_add insertion_Var,
          intro conjI allI impI)
      subgoal for \<alpha> unfolding assignment_def by simp
      subgoal for _ _ _ \<alpha> x v 
      proof goal_cases 
        case 1
        hence "x \<in> {0,1}" by auto
        thus ?case using 1(3) by auto
      qed
      subgoal by auto
      done
  next
    case *: q
    have vars: "vars (PVar 0 * PVar 0 + Const 2 * PVar 0 :: 'a mpoly) = {0}" 
      apply (intro vars_eqI)
      subgoal by (intro vars_mult_subI vars_add_subI, auto) 
      subgoal for v by (intro exI[of _ "\<lambda> _. 1"] exI[of _ 2], auto)
      done
    show ?thesis unfolding inter_Q.valid_monotone_poly_def *
      apply (intro allI impI, clarify, unfold IQ.simps vars valid_poly_def
          monotone_poly_wrt_def 
          insertion_mult insertion_add insertion_Var,
          intro conjI allI impI)
      subgoal for \<alpha> unfolding assignment_def by simp
      subgoal for _ _ _ \<alpha> x v 
      proof goal_cases 
        case 1
        hence [simp]: "x = 0" by auto
        from 1(1) have "\<alpha> 0 \<ge> 0" unfolding assignment_def by simp
        thus ?case using 1(3) 
          by auto
            (metis (no_types, opaque_lifting) add.assoc add_mono le_add_same_cancel1 mult_2 mult_mono order_trans zero_less_one_class.zero_le_one)
      qed
      subgoal by auto
      done
  next
    case *: (v i)
    from \<alpha>[unfolded positive_interpr_def] have pos: "\<alpha> i > 0" by auto
    have vars: "vars ((PVar 0)^(nat (\<alpha> i)):: 'a mpoly) = {0}" 
      apply (intro vars_eqI)
      subgoal by (metis Preliminaries_on_Polynomials_1.vars_Var vars_power) 
      subgoal for v using pos apply (intro exI[of _ "\<lambda> _. 2"] exI[of _ 1])
        by (auto simp: insertion_power)
          (metis less_numeral_extra(4) one_less_numeral_iff one_less_power semiring_norm(76) zero_less_nat_eq)
      done
    show ?thesis unfolding inter_Q.valid_monotone_poly_def *
      apply (intro allI impI, clarify, unfold IQ.simps vars valid_poly_def
          monotone_poly_wrt_def 
          insertion_Var insertion_power,
          intro conjI allI impI)
      subgoal for _ _ _ \<beta> using pos unfolding assignment_def by simp
      subgoal for _ _ _ \<beta> x v 
      proof goal_cases 
        case 1
        hence [simp]: "x = 0" by auto
        from 1(1) have b0: "\<beta> 0 \<ge> 0" unfolding assignment_def by simp
        from pos obtain k where nik: "nat (\<alpha> i) = Suc k" 
          using gr0_implies_Suc zero_less_nat_eq by presburger
        define b0 where "b0 = \<beta> 0" 
        have "\<beta> 0 ^ nat (\<alpha> i) + 1 \<le> (\<beta> 0 + 1) ^ nat (\<alpha> i)" using b0 unfolding nik b0_def[symmetric] 
        proof (induct k)
          case (Suc k)
          define sk where "sk = Suc k" 
          from Suc show ?case unfolding sk_def[symmetric]
            by (auto simp: field_simps add_mono ordered_comm_semiring_class.comm_mult_left_mono)
        qed auto
        also have "\<dots> \<le> v ^ nat (\<alpha> i)" using 1(3) by (simp add: b0 power_mono)
        finally show ?case by simp
      qed
      subgoal by auto
      done
  qed
qed

lemma I_Q_delta_poly_inter: "delta_poly_inter F_Q I_Q (1 :: 'a)"  
  by (unfold_locales, rule valid_monotone_inter_Q, auto)

interpretation inter_Q: delta_poly_inter F_Q I_Q "1 :: 'a" by (rule I_Q_delta_poly_inter)

text \<open>Orientation part of Theorem 6.4\<close>

lemma orient_Q: "inter_Q.orient_rule (lhs_Q, rhs_Q)" 
  unfolding inter_Q.orient_rule_def split inter_Q.I'_is_insertion_eval
proof (intro allI impI)
  fix x :: "_ \<Rightarrow> 'a" 
  assume "assignment x" 
  hence x: "x i \<ge> 0" for i unfolding assignment_def by auto
  have h9: "h \<ge> 9" unfolding h_def by auto
  define l where "l i = args (lhs_Q) ! i" for i
  define r where "r i = args (rhs_Q) ! i" for i
  let ?e = "inter_Q.eval" 
  let ?poly = "\<lambda> t. insertion x (?e t)"  
  note defs = l_def r_def lhs_Q_def rhs_Q_def
  let ?nums = "[0,1,2,3,4,5,6,7,8] :: nat list" 
  note [simp] = insertion_add insertion_mult y1_def y2_def y3_def y4_def y5_def y6_def y7_def y8_def y9_def
  
  have e_lhs: "?e lhs_Q = sum_list (map (\<lambda> i. (?e (l i))) ?nums)"
    unfolding defs by simp
  have e_rhs: "?e rhs_Q = sum_list (map (\<lambda> i. (?e (r i))) ?nums)" 
    unfolding defs by simp

  have [simp]: "2 = (Const (2 :: 'a))"
    by (metis mpoly_Const_1 mpoly_Const_add one_add_one)

  have "?poly (r 0) = h^2 * ((x 0)^2 + 2 * x 0) + h^2 + h"
    by (simp add: field_simps power2_eq_square defs)
  also have "\<dots> \<le> (h * x 0 + h)^2 + 2 * (h * x 0 + h)" using h x[of 0]
    by (simp add: field_simps power2_eq_square)
  also have "\<dots> = ?poly (l 0)" 
    by (simp add: field_simps power2_eq_square defs)
  finally have 1: "?poly (l 0) \<ge> ?poly (r 0)" .

  from h9 have h2: "h \<ge> 2" by auto
  have "?poly (r 1) = 2 * x 1"
    by (simp add: field_simps defs)
  also have "\<dots> \<le> h * x 1 + h" using mult_right_mono[OF h2 x[of 1]] h
    by auto
  also have "\<dots> = ?poly (l 1)" 
    by (simp add: field_simps power2_eq_square defs)
  finally have 2: "?poly (l 1) \<ge> ?poly (r 1)" .

  have "?poly (r 2) + 1 = 9 * x 2 + 1" unfolding defs by simp
  also have "\<dots> \<le> h * x 2 + h" 
    by (intro add_mono h mult_right_mono h9 x)
  also have "\<dots> = ?poly (l 2)" unfolding defs by simp
  finally have 3: "?poly (l 2) \<ge> ?poly (r 2) + 1" .

  have eval_vs: "insertion x (inter_Q.eval (g_list (map (\<lambda>i. (v_sym i, Suc 0)) xs))) = 0"  
    for xs by (induct xs, auto simp: insertion_power \<alpha>1)
  have [simp]: "insertion x (inter_Q.eval t_t) = h" unfolding t_t_def symbol_list_def
    by (simp add: eval_vs)
  have "?poly (r 3) = (x 3 + h)^2 + 2 * (x 3 + h)"
    by (simp add: field_simps power2_eq_square defs)
  also have "\<dots> \<le> (x 3)^2 + 2 * x 3 + h^3*x 3 + h^3 + h^2 + h" (is "?l \<le> ?r")
  proof -
    have "2 * 1 \<le> h * h" 
      by (intro mult_mono, insert h2, auto)
    hence hh: "h * h \<ge> 2" by auto
    have "?l \<le> ?r \<longleftrightarrow> 1 * h + (2 * h) * x 3 \<le> (h * h) * h + ((h * h) * h) * x 3" 
      by (auto simp: field_simps power2_eq_square defs power3_eq_cube) 
    also have "\<dots>"
      by (intro add_mono mult_right_mono x, insert h hh, auto)
    finally show ?thesis .
  qed
  also have "\<dots> = ?poly (l 3)" 
    by (simp add: field_simps power2_eq_square defs power3_eq_cube)
  finally have 4: "?poly (l 3) \<ge> ?poly (r 3)" .

  have "?poly (r 4) = ((x 4)^2 + 2 * x 4)"
    by (simp add: field_simps power2_eq_square defs)
  also have "\<dots> = ?poly (l 4)" 
    by (simp add: field_simps power2_eq_square defs)
  finally have 5: "?poly (l 4) \<ge> ?poly (r 4)" by simp

  have "?poly (r 5) = (x 5)^2 + 2 * x 5"
    by (simp add: field_simps power2_eq_square defs)
  also have "\<dots> = ?poly (l 5)" 
    by (simp add: field_simps power2_eq_square defs)
  finally have 6: "?poly (l 5) \<ge> ?poly (r 5)" by simp

  have 7: "?poly (l 6) \<ge> ?poly (r 6)" unfolding defs using h x[of 6]
    by (simp add: add_increasing2 linorder_not_le mult_le_cancel_right1)
  have 8: "?poly (l 7) \<ge> ?poly (r 7)" unfolding defs using h x[of 7]
    by (simp add: add_increasing2 linorder_not_le mult_le_cancel_right1)

  have 9: "?poly (l 8) \<ge> ?poly (r 8)"
  proof - 
    have r: "?e (r 8) = poly_to_mpoly 8 (qqq h)" 
      unfolding defs qqq_def 
      by (simp add: qq[unfolded y9_def] algebra_simps smult_conv_mult_Const Const_mult flip: mpoly_of_poly_is_poly_to_mpoly)
    have l: "?e (l 8) = poly_to_mpoly 8 ([:h:] * (ppp h) + [:h:])" 
      unfolding defs ppp_def
      by (simp add: pp[unfolded y9_def] algebra_simps smult_conv_mult_Const Const_mult flip: mpoly_of_poly_is_poly_to_mpoly)
    {
      fix r
      assume r: "r \<in> {p,q}" 
      with funas_encode_poly_p funas_encode_poly_q 
      have funas: "funas_term (encode_poly y9 r) \<subseteq> F" by auto
      have "poly_inter.eval (IQ 1) (encode_poly y9 r) = inter_Q.eval (encode_poly y9 r)" 
        by (rule poly_inter_eval_cong, insert funas, auto simp: F_def)
    } note encode_eq = this
    have pp_eq: "pp h = pp 1" unfolding pp_def using encode_eq[of p] by auto
    have qq_eq: "qq h = qq 1" unfolding qq_def using encode_eq[of q] by auto
    have ppp_eq: "ppp h = ppp 1" unfolding ppp_def pp_eq ..
    have qqq_eq: "qqq h = qqq 1" unfolding qqq_def qq_eq ..
    have "H h = H 1" unfolding H_def ppp_eq qqq_eq ..
    also have "\<dots> \<le> h" unfolding h_def by auto
    finally have h: "h \<ge> H h" .    
    show ?thesis unfolding l r using H[OF h x[of 8]] by simp
  qed

  have "?poly rhs_Q + 1 = 
     ?poly (r 0) + ?poly (r 1) + (?poly (r 2) + 1) + ?poly (r 3) + ?poly (r 4) + ?poly (r 5) + ?poly (r 6) + ?poly (r 7) + ?poly (r 8)"
    unfolding e_rhs by simp
  also have "\<dots> \<le> ?poly (l 0) + ?poly (l 1) + ?poly (l 2) + ?poly (l 3) + ?poly (l 4) + ?poly (l 5) + ?poly (l 6) + ?poly (l 7) + ?poly (l 8)" 
    by (intro add_mono 1 2 3 4 5 6 7 8 9)
  also have "\<dots> = ?poly lhs_Q" 
    unfolding e_lhs by simp

  finally show "?poly rhs_Q + 1 \<le> ?poly lhs_Q" by auto
qed
end  
end

context poly_input
begin

text \<open>Theorem 6.4\<close>
theorem solution_impl_delta_termination_of_Q: 
  assumes "positive_poly_problem p q"
  shows "termination_by_delta_poly_interpretation (TYPE('a :: floor_ceiling)) F_Q Q" 
proof -
  interpret solvable_poly_problem
    by (unfold_locales, fact)
  interpret I: delta_poly_inter F_Q I_Q "(1 :: 'a)" by (rule I_Q_delta_poly_inter)
  show ?thesis 
    unfolding termination_by_delta_poly_interpretation_def
  proof (intro exI[of _ "1 :: 'a"] exI[of _ I_Q] conjI I_Q_delta_poly_inter)
    show "I.termination_by_delta_interpretation Q" 
      unfolding I.termination_by_delta_interpretation_def Q_def 
    proof (clarify, intro conjI)
      show "funas_term lhs_Q \<union> funas_term rhs_Q \<subseteq> F_Q" using lhs_Q_F rhs_Q_F by auto
      show "I.orient_rule (lhs_Q, rhs_Q)" using orient_Q by simp
    qed
  qed
qed

end

context delta_poly_inter
begin

lemma insertion_eval_pos: assumes "funas_term t \<subseteq> F"
  and "assignment \<alpha>" 
shows "insertion \<alpha> (eval t) \<ge> 0" 
  by (rule valid_imp_insertion_eval_pos[OF valid assms]) 

lemma monotone_poly_eval: assumes "funas_term t \<subseteq> F" 
  shows "monotone_poly (vars_term t) (eval t)" "vars (eval t) = vars_term t" 
proof -
  have "\<exists>y. x + \<delta> \<le> y" for x :: 'a by (intro exI[of _ "x + \<delta>"], auto)
  from monotone_poly_eval_generic[OF valid transp_gt_delta gt_delta_imp_ge this _ assms] \<delta>0
  show "monotone_poly (vars_term t) (eval t)" "vars (eval t) = vars_term t" by auto
qed

lemma monotone_linear_poly_to_coeffs: fixes p :: "'a mpoly" 
  assumes linear: "total_degree p \<le> 1" 
    and poly: "valid_poly p" 
    and mono: "monotone_poly {..<n} p" 
    and vars: "vars p = {..<n}" 
shows "\<exists> c a. p = Const c + (\<Sum>i\<leftarrow>[0..<n]. Const (a i) * PVar i)
     \<and> c \<ge> 0 \<and> (\<forall> i < n. a i \<ge> 1)" 
proof -
  have sum_zero: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list (xs :: int list) = 0" for xs by (induct xs, auto)
  from coefficients_of_linear_poly[OF linear] obtain c a vs 
    where p: "p = Const c + (\<Sum>i\<leftarrow>vs. Const (a i) * PVar i)"
     and vsd: "distinct vs" "set vs = vars p" "sorted_list_of_set (vars p) = vs"
     and nz: "\<And> v. v \<in> set vs \<Longrightarrow> a v \<noteq> 0"
     and c: "c = mcoeff p 0" 
     and a: "\<And> i. a i = mcoeff p (monomial 1 i)" by blast
  have vs: "vs = [0..<n]" unfolding vsd(3)[symmetric] unfolding vars
    by (simp add: lessThan_atLeast0)
  show ?thesis unfolding p vs
  proof (intro exI conjI allI impI, rule refl)
    show c: "c \<ge> 0" using poly[unfolded valid_poly_def, rule_format, of "\<lambda> _. 0", unfolded p]
      by (auto simp: coeff_add[symmetric] coeff_Const coeff_sum_list o_def coeff_Const_mult 
        coeff_Var monomial_0_iff assignment_def)
    fix i
    assume "i < n" 
    hence i: "i \<in> set vs" unfolding vs by auto
    from nz[OF i] have a0: "a i \<noteq> 0" by auto    
    from split_list[OF i] obtain bef aft where vsi: "vs = bef @ [i] @ aft" by auto
    with vsd(1) have i: "i \<notin> set (bef @ aft)" by auto
    define \<alpha> where "\<alpha> = (\<lambda> x :: var. 0 :: 'a)" 
    have "assignment \<alpha>" unfolding assignment_def \<alpha>_def using c by auto
    from mono[unfolded monotone_poly_wrt_def, rule_format, OF this, of i \<delta>] \<open>i < n\<close>
    have "insertion \<alpha> p + \<delta> \<le> insertion (\<alpha>(i := \<delta>)) p" by (auto simp: \<alpha>_def)
    from this[unfolded p vsi insertion_add insertion_sum_list insertion_Const map_map o_def insertion_mult insertion_Var]
    have "(\<Sum>x\<leftarrow> bef @ aft. a x * \<alpha> x) + \<delta> \<le> (\<Sum>x\<leftarrow>bef @ aft. a x * (\<alpha>(i := \<delta>)) x) + a i * \<delta>" 
      by (auto simp: \<alpha>_def)
    also have "(\<Sum>x\<leftarrow>bef @ aft. a x * (\<alpha>(i := \<delta>)) x) = (\<Sum>x\<leftarrow>bef @ aft. a x * \<alpha> x)" 
      by (subst map_cong[OF refl, of _ _ "\<lambda> x. a x * \<alpha> x"], insert i, auto simp: \<alpha>_def)
    finally have "\<delta> \<le> a i * \<delta>" by auto
    with \<delta>0 show "a i \<ge> 1" by simp
  qed
qed


end

text \<open>Lemma 6.7\<close>
lemma criterion_for_degree_2: assumes qq_def: "qq = q \<circ>\<^sub>p [:c, a:] - smult a q" 
  and dq: "degree q \<ge> 2" 
  and ineq: "\<And> x :: 'a :: linordered_field. x \<ge> 0 \<Longrightarrow> poly qq x \<le> poly p x" 
  and dp: "degree p \<le> 1" 
  and a1: "a \<ge> 1" 
  and lq0: "lead_coeff q > 0" 
  and c: "c > 0" 
shows "degree q = 2" "a = 1" 
proof -
  have deg: "degree (q \<circ>\<^sub>p [:c, a:]) = degree q"
    unfolding degree_pcompose using a1 by simp
  have coeff_dq: "coeff qq (degree q) = lead_coeff q * (a ^ degree q - a)" 
    apply (simp add: qq_def)
    apply (subst deg[symmetric])
    apply (subst lead_coeff_comp)
    subgoal using a1 by simp
    subgoal using a1 by (simp add: field_simps)
    done
  have deg_qq: "degree qq \<le> degree q" using deg
    by (simp add: degree_diff_le qq_def)

  {
    assume "a \<noteq> 1" 
    with a1 have a1: "a > 1" by auto
    hence "a ^ degree q > a ^ 1" using dq
      by (metis add_strict_increasing linorder_not_less one_add_one power_le_imp_le_exp zero_less_one)
    hence coeff: "coeff qq (degree q) > 0" 
      unfolding coeff_dq using dq by (auto intro!: mult_pos_pos lq0)
    hence "degree qq \<ge> degree q" 
      by (simp add: le_degree)
    with deg_qq have eq: "degree qq = degree q" by auto  
    from coeff[folded eq] have lcqq: "lead_coeff qq > 0" by auto
    from dq[folded eq] have "2 \<le> degree qq" by auto
    also have "degree qq \<le> degree p" using ineq lcqq
      by (metis Preliminaries_on_Polynomials_2.poly_pinfty_ge degree_mono_generic linorder_le_less_linear order_less_not_sym) 
    also have "\<dots> \<le> 1" by fact
    finally have False by simp
  }
  thus a1: "a = 1" by auto  
  hence qq: "qq = q \<circ>\<^sub>p [:c, 1:] - q" unfolding qq_def by auto
  from coeff_dq[unfolded a1] have "coeff qq (degree q) = 0" by simp
  with deg_qq dq have deq_qq: "degree qq < degree q"
    using degree_less_if_less_eqI by fastforce
  define m where "m = degree q" 
  define m1 where "m1 = m - 1" 
  from dq have mm1: "m = Suc m1" unfolding m1_def m_def by auto 
  define qi where "qi = coeff q" 
  define cf where "cf k i = (qi k * of_nat (k choose i) * c ^ (k - i))" for i k
  define inner where "inner k = (\<Sum>i<k.  monom (cf k i) i)" for k
  define rem where "rem = (\<Sum>i< m1. monom (cf m i) i) + sum inner {..<m}" 
  {
    fix x 
    define e where "e i k = of_nat (k choose i) * x ^ i * c ^ (k - i)" for k i
    have "poly qq x = poly (q \<circ>\<^sub>p [:c, 1:]) x - poly q x" unfolding qq by simp
    also have "\<dots> = (\<Sum>k\<le>m. qi k * (x + c) ^ k) - (\<Sum>k\<le>m. qi k * x ^ k)" unfolding qi_def
      by (subst (1 2) poly_as_sum_of_monoms[of q, symmetric, folded m_def])
        (simp add: poly_sum poly_pcompose poly_monom ac_simps)
    also have "\<dots> = (\<Sum>k\<le>m. qi k * (\<Sum>i\<le>k. e i k)) - (\<Sum>k\<le>m. qi k * x ^ k)"
      by (subst binomial_ring, auto simp: e_def)
    also have "\<dots> = (\<Sum>k\<le>m. qi k * (e k k + (\<Sum>i<k. e i k))) - (\<Sum>k\<le>m. qi k * x ^ k)"
      by (intro arg_cong[of _ _ "\<lambda> x. x - _"] sum.cong refl arg_cong2[of _ _ _ _ "(*)"])
        (metis add.commute lessThan_Suc_atMost sum.lessThan_Suc)
    also have "\<dots> = (\<Sum>k\<le>m. qi k * e k k) + (\<Sum>k\<le>m. qi k * (\<Sum>i<k. e i k)) - (\<Sum>k\<le>m. qi k * x ^ k)" 
      by (simp add: field_simps sum.distrib)
    also have "\<dots> = (\<Sum>k\<le>m. qi k * (\<Sum>i<k. e i k))" 
      unfolding e_def by simp
    also have "\<dots> = poly (\<Sum>k\<le>m. inner k) x" unfolding e_def inner_def cf_def
      by (simp add: poly_sum poly_monom ac_simps sum_distrib_left)
    finally have "poly qq x = poly (sum inner {..m}) x" .
  }
  hence "qq = sum inner {..m}" by (intro poly_ext, auto)
  also have "\<dots> = inner m + sum inner {..<m}"
    by (metis add.commute lessThan_Suc_atMost sum.lessThan_Suc)
  also have "inner m = monom (cf m m1) m1 + (\<Sum>i< m1. monom (cf m i) i)" 
    unfolding inner_def mm1 by simp
  finally have qq: "qq = monom (cf m m1) m1 + rem" by (simp add: rem_def)
  have cf_mm1: "cf m m1 > 0" unfolding cf_def
  proof (intro mult_pos_pos)
    show "0 < qi m" unfolding qi_def m_def by fact
    show "0 < (of_nat (m choose m1) :: 'a)" unfolding mm1 
      by (simp add: add_strict_increasing)
    show "0 < c ^ (m - m1)" using c by simp
  qed
  {
    fix k
    assume k: "k \<ge> m1" 
    have "coeff rem k = (\<Sum>i<m. coeff (inner i) k)" using k 
      by (simp add: rem_def Polynomial.coeff_sum)
    also have "\<dots> = 0" 
    proof (intro sum.neutral ballI)
      fix i
      show "i \<in> {..<m} \<Longrightarrow> coeff (inner i) k = 0" 
        unfolding inner_def Polynomial.coeff_sum using k mm1
        by auto
    qed
    finally have "coeff rem k = 0" .
  } note zero = this
  from cf_mm1 zero[of m1]
  have qq_m1: "coeff qq m1 > 0" unfolding qq by auto
  {
    fix k
    assume "k > m1" 
    with zero[of k] have "coeff qq k = 0" unfolding qq by auto
  }
  with qq_m1 have deg_qq: "degree qq = m1"
    by (metis coeff_0 le_degree leading_coeff_0_iff order_less_le)
  with qq_m1 have lc_qq: "lead_coeff qq > 0" by auto

  from ineq lc_qq have "degree qq \<le> degree p"
    by (metis Preliminaries_on_Polynomials_2.poly_pinfty_ge degree_mono_generic linorder_le_less_linear order_less_not_sym) 
  also have "\<dots> \<le> 1" by fact
  finally have "m1 \<le> 1" unfolding deg_qq by simp
  with mm1 have "m \<le> 2" by auto
  hence "degree q \<le> 2" unfolding m_def by auto
  with dq show "degree q = 2" by auto
qed

  
(* on the way to Theorem 6.8 *)
locale term_delta_poly_input = poly_input p q for p q +
  fixes type_of_field :: "'a :: floor_ceiling itself" 
  assumes terminating_delta_poly: "termination_by_delta_poly_interpretation TYPE('a) F_Q Q" 
begin

definition I where "I = (SOME I. \<exists> \<delta>. delta_poly_inter F_Q I (\<delta> :: 'a) \<and> 
     delta_poly_inter.termination_by_delta_interpretation F_Q I \<delta> Q)" 

definition \<delta> where "\<delta> = (SOME \<delta>. delta_poly_inter F_Q I (\<delta> :: 'a) \<and> 
     delta_poly_inter.termination_by_delta_interpretation F_Q I \<delta> Q)" 

lemma I: "delta_poly_inter F_Q I \<delta>" "delta_poly_inter.termination_by_delta_interpretation F_Q I \<delta> Q" 
  using someI_ex[OF someI_ex[OF terminating_delta_poly[unfolded termination_by_delta_poly_interpretation_def],
      folded I_def], folded \<delta>_def]
  by auto
  
sublocale delta_poly_inter F_Q I \<delta> by (rule I(1))

lemma orient: "orient_rule (lhs_Q,rhs_Q)" 
  using I(2)[unfolded termination_by_delta_interpretation_def] unfolding Q_def by auto

lemma eval_t_t_gt_0: assumes Ig: "I g_sym = Const g0 + Const g1 * PVar 0 + Const g2 * PVar 1" 
  and Iz: "I z_sym = Const z0" 
  and z0: "z0 \<ge> 0" 
  and g0: "g0 \<ge> 0" 
  and g12: "g1 > 0" "g2 > 0" 
shows "insertion \<beta> (eval t_t) > 0"   
proof -
  define \<alpha> where "\<alpha> = (\<lambda> _ :: var. 0 :: 'a)" 
  have \<alpha>: "assignment \<alpha>" by (auto simp: assignment_def \<alpha>_def)
  have id: "insertion \<beta> (eval t_t) = insertion \<alpha> (eval t_t)" 
    by (rule insertion_irrelevant_vars, insert vars_t vars_eval, auto)
  note pos = insertion_eval_pos[OF _ \<alpha>]
  show ?thesis 
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    from this[unfolded id] have "insertion \<alpha> (eval t_t) \<le> 0" by auto
    with pos[OF t_F] have 0: "insertion \<alpha> (eval t_t) = 0" by auto
    note [simp] = insertion_add insertion_mult insertion_substitute


    define IA where "IA t = insertion \<alpha> (eval t)" for t
    note pos = pos[folded IA_def]
    let ?zz = "g_list symbol_list" 
    from pos[OF g_list_F[OF symbol_list]]
    have zz: "0 \<le> IA ?zz" by auto
    have 0: "0 = IA t_t" using 0 by (auto simp: IA_def)
    also have "\<dots> = g0 + g1 * z0 + g2 * IA ?zz" unfolding t_t_def by (simp add: Ig IA_def Iz)
    finally have g0: "g0 = 0" and "g1 * z0 = 0" "g2 * IA ?zz = 0" 
      using g0 z0 g12 zz mult_nonneg_nonneg[of g1 z0] mult_nonneg_nonneg[of g2 "IA ?zz"]
      by linarith+
    with g12 have z0: "z0 = 0" and 0: "IA ?zz = 0" by auto
    from Ig g0 have Ig: "I g_sym = Const g1 * PVar 0 + Const g2 * PVar 1" by simp
    from z0 Iz have Iz: "I z_sym = 0" by auto

    {
      fix fs f a
      assume "set fs \<subseteq> F_Q" and "IA (g_list fs) = 0" 
        and "(f,a) \<in> set fs" 
      hence "mcoeff (I f) 0 = 0" 
      proof (induct fs)
        case (Cons kb fs)
        obtain k b where kb: "kb = (k,b)" by force
        let ?t = "Fun k (replicate b z_t) :: (symbol,var)term" 
        from Cons(3)[unfolded kb]
        have 0: "g1 * IA ?t + g2 * IA (g_list fs) = 0" 
          by (simp add: IA_def Ig)
        from Cons(2)[unfolded kb] have "(k,b) \<in> F_Q" by auto
        hence "funas_term ?t \<subseteq> F_Q" by (force simp: F_Q_def F_def)
        from pos[OF this] have pos1: "0 \<le> IA ?t" by auto
        from Cons(2) have fs: "set fs \<subseteq> F_Q" by auto
        from pos[OF g_list_F[OF this]] have pos2: "0 \<le> IA (g_list fs)" by auto
        from 0 g12 pos1 pos2 mult_nonneg_nonneg[of g1 "IA ?t"] 
          mult_nonneg_nonneg[of g2 "IA (g_list fs)"]
        have "g1 * IA ?t = 0" "g2 * IA (g_list fs) = 0" 
          by linarith+
        with g12 have t: "IA ?t = 0" and 0: "IA (g_list fs) = 0" by auto
        from Cons(1)[OF fs 0] have IH: "(f, a) \<in> set fs \<Longrightarrow> mcoeff (I f) 0 = 0" by auto
        show ?case 
        proof (cases "(f,a) = (k,b)")
          case False
          with IH Cons(4) kb show ?thesis by auto
        next
          case True
          have "0 = IA ?t" using t by simp
          also have "\<dots> = insertion \<alpha> (I k)" 
            apply (simp add: IA_def)
            apply (rule insertion_irrelevant_vars)
            subgoal for v by (auto simp: Iz \<alpha>_def)
            done
          also have "\<dots> = mcoeff (I k) 0" unfolding \<alpha>_def by simp
          finally show ?thesis using True by simp
        qed
      qed auto
    } note main = this

    {
      fix k ka
      assume "(k,ka) \<in> F_Q" 
      then consider (z) "(k,ka) = (z_sym,0)" | (g) "(k,ka) = (g_sym,2)" | (zl) "(k,ka) \<in> set symbol_list" 
        unfolding symbol_list_def F_Q_def F_def using V_list by auto
      hence "mcoeff (I k) 0 = 0" 
      proof cases
        case (zl)
        from main[OF symbol_list 0 zl] show ?thesis .
      next
        case z
        thus ?thesis using Iz by simp
      next
        case g
        thus ?thesis using Ig by (simp add: coeff_Const_mult coeff_Var)
      qed
    } note coeff_0 = this
  

    have ins_0: "funas_term t \<subseteq> F_Q \<Longrightarrow> insertion \<alpha> (eval t) = 0" for t
    proof (induct t)
      case (Var x)
      show ?case by (auto simp: \<alpha>_def coeff_Var)
    next
      case (Fun f ts)
      {
        fix i
        assume "i < length ts" 
        hence "ts ! i \<in> set ts" by auto
        from Fun(1)[OF this] Fun(2) this 
        have "insertion \<alpha> (eval (ts ! i)) = 0" by auto
      } note IH = this
      have "insertion \<alpha> (eval (Fun f ts)) = insertion \<alpha> (I f)" 
        apply (simp)
        apply (intro insertion_irrelevant_vars)
        subgoal for v using IH[of v] by (auto simp: \<alpha>_def)
        done
      also have "\<dots> = mcoeff (I f) 0" unfolding \<alpha>_def by simp
      also have "\<dots> = 0" using Fun(2) coeff_0 by auto
      finally show ?case by simp
    qed

    from orient[unfolded orient_rule gt_poly_def, rule_format, OF \<alpha>] ins_0[OF lhs_Q_F] ins_0[OF rhs_Q_F]
    show False using \<delta>0 by auto
  qed
qed


text \<open>Theorem 6.8\<close>
theorem solution: "positive_poly_problem p q"
proof -
  let ?q = q
  from orient[unfolded orient_rule]
  have gt: "gt_poly (eval lhs_Q) (eval rhs_Q)" by auto
  from valid[unfolded valid_monotone_poly_inter_def]
  have valid: "\<And> f. f \<in> F_Q \<Longrightarrow> valid_monotone_poly f" by auto
  let ?lc = "lead_coeff" 
  let ?f = "(f_sym,9)" 
  have "?f \<in> F_Q" unfolding F_Q_def by auto
  from valid[OF this, unfolded valid_monotone_poly_def] obtain f where
    If: "I f_sym = f" and f: "valid_poly f" "monotone_poly (vars f) f" "vars f = {..< 9}" by auto
  note mono = f(2)
  define l where "l i = args (lhs_Q) ! i" for i
  define r where "r i = args (rhs_Q) ! i" for i
  have list: "[0..<9] = [0,1,2,3,4,5,6,7,8 :: nat]" by code_simp
  have lhs_Q: "lhs_Q = Fun f_sym (map l [0..<9])" unfolding lhs_Q_def l_def by (auto simp: list)
  have rhs_Q: "rhs_Q = Fun f_sym (map r [0..<9])" unfolding rhs_Q_def r_def by (auto simp: list)
  {
    fix i :: var
    define vs where "vs = V_list" 
    assume "i < 9" 
    hence choice: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i = 6 \<or> i = 7 \<or> i = 8" by linarith
    have set: "{0..<9 :: nat} = {0,1,2,3,4,5,6,7,8}" by code_simp
    from choice have vars: "vars_term (l i) = {i}" "vars_term (r i) = {i}" unfolding l_def lhs_Q_def r_def rhs_Q_def 
      using vars_encode_poly[of 8 p] vars_encode_poly[of 8 q] vars_t
      by (auto simp: y1_def y2_def y3_def y4_def y5_def y6_def y7_def y8_def y9_def vs_def[symmetric])
    from choice set have funs: "funas_term (l i) \<union> funas_term (r i) \<subseteq> F_Q" using rhs_Q_F lhs_Q_F unfolding lhs_Q rhs_Q
      by auto
    have "lr \<in> {l,r} \<Longrightarrow> vars_term (lr i) = {i}" "lr \<in> {l,r} \<Longrightarrow> funas_term (lr i) \<subseteq> F_Q" for lr
      by (insert vars funs, force)+
  } note signature_l_r = this  
  {
    fix i :: var and lr
    assume i: "i < 9" and lr: "lr \<in> {l,r}" 
    from signature_l_r[OF i lr] monotone_poly_eval[of "lr i"]
    have vars: "vars (eval (lr i)) = {i}"  
      and mono: "monotone_poly {i} (eval (lr i))" by auto
  } note eval_l_r = this

  define upoly where "upoly l_or_r i = mpoly_to_poly i (eval (l_or_r i))" for l_or_r :: "var \<Rightarrow> (_,_)term" and i

  {
    fix lr and i :: nat and a :: "_ \<Rightarrow> 'a" 
    assume a: "assignment a" and i: "i < 9" and lr: "lr \<in> {l,r}"  
    with eval_l_r[OF i] signature_l_r[OF i]
    have vars: "vars (eval (lr i)) = {i}" and mono: "monotone_poly {i} (eval (lr i))"
      and funs: "funas_term (lr i) \<subseteq> F_Q" by auto
    from insertion_eval_pos[OF funs] 
    have valid: "valid_poly (eval (lr i))" unfolding valid_poly_def by auto
    from monotone_poly_partial_insertion[OF _ mono a, of i] valid
    have deg: "degree (partial_insertion a i (eval (lr i))) > 0" 
      and lc: "?lc (partial_insertion a i (eval (lr i))) > 0" 
      and ineq: "insertion a (eval (lr i)) \<ge> a i - \<delta>" by auto
    moreover have "partial_insertion a i (eval (lr i)) = upoly lr i" unfolding upoly_def
      using vars eval_l_r[OF i, of r, simplified]
      by (intro poly_ext)
        (metis i insertion_partial_insertion_vars poly_eq_insertion poly_inter.vars_eval signature_l_r(1)[of _ r, simplified] singletonD)
    ultimately 
    have "degree (upoly lr i) > 0" "?lc (upoly lr i) > 0" 
      "insertion a (eval (lr i)) \<ge> a i - \<delta>" by auto
  } note upoly_pos_subterm = this


  {
    fix i :: var
    assume i: "i < 9" 
    from degree_partial_insertion_stays_constant[OF f(2), of i] obtain a' where
      a': "assignment a'" and
      deg_a': "\<And> b. (\<And> y. a' y + \<delta> \<le> b y) \<Longrightarrow> degree (partial_insertion a' i f) = degree (partial_insertion b i f)" 
      by auto
    define a where "a j = a' j + 2 * \<delta>" for j
    from a' have a: "assignment a" unfolding assignment_def a_def using \<delta>0 by auto
    {
      fix b
      assume le: "\<And> y. a y - \<delta> \<le> b y" 
      have "a' y + \<delta> \<le> b y" for y using le[of y] unfolding a_def by auto
      from deg_a'[OF this]
      have 1: "degree (partial_insertion a' i f) = degree (partial_insertion b i f)" by auto
      have "a' y + \<delta> \<le> a y" for y unfolding a_def using \<delta>0 by auto
      from deg_a'[OF this] 1
      have "degree (partial_insertion a i f) = degree (partial_insertion b i f)" by auto
    } note deg_a = this
       
    define c where "c j = (if j < 9 then insertion a (eval (l j)) else a j)" for j
    define e where "e j = (if j < 9 then insertion a (eval (r j)) else a j)" for j
    {
      fix x :: 'a
      assume x: "x \<ge> 0" 
      have ass: "assignment (a (i := x))" using x a unfolding assignment_def by auto
      from gt[unfolded gt_poly_def, rule_format, OF ass, unfolded rhs_Q lhs_Q]
      have "insertion (a(i := x)) (eval (Fun f_sym (map r [0..<9]))) + \<delta>
        \<le> insertion (a(i := x)) (eval (Fun f_sym (map l [0..<9])))" by simp
      also have "insertion (a(i := x)) (eval (Fun f_sym (map r [0..<9]))) = 
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
      also have "insertion (a(i := x)) (eval (Fun f_sym (map l [0..<9]))) = 
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
        \<ge> poly (partial_insertion e i f) (poly (upoly r i) x) + \<delta>" .
    } note 1 = this 

    define er where "er = partial_insertion e i f \<circ>\<^sub>p upoly r i"
    define cl where "cl = partial_insertion c i f \<circ>\<^sub>p upoly l i"
    define d where "d = degree (partial_insertion e i f)" 
    {
      fix x
      have "a x - \<delta> \<le> c x \<and> a x - \<delta> \<le> e x" 
      proof (cases "x \<in> vars f")
        case False
        thus ?thesis unfolding c_def e_def f using \<delta>0 by auto
      next
        case True
        hence id: "(x < 9) = True" and x: "x < 9" unfolding f by auto
        show ?thesis unfolding c_def e_def id if_True using upoly_pos_subterm(3)[OF a x]
          by auto
      qed
      hence "a x - \<delta> \<le> c x" "a x - \<delta> \<le> e x" by auto
    } note a_ce = this

    have d_eq: "d = degree (partial_insertion c i f)" unfolding d_def
      by (subst (1 2) deg_a[symmetric], insert a_ce, auto)

    have e: "assignment e" using a' a_ce(2) \<delta>0 unfolding assignment_def a_def
      by (metis (no_types, lifting) diff_ge_0_iff_ge gt_delta_imp_ge le_add_same_cancel2 linorder_not_less mult_2 order_le_less_trans)

    have d_pos: "d > 0" unfolding d_def 
      by (intro monotone_poly_partial_insertion[OF _ f(2) e], insert f i, auto)
    have lc_e_pos: "?lc (partial_insertion e i f) > 0" 
      by (intro monotone_poly_partial_insertion[OF _ f(2) e], insert f i, auto)

    have lc_r_pos: "?lc (upoly r i) > 0" by (intro upoly_pos_subterm[OF a i], auto)
    have deg_r: "0 < degree (upoly r i)" by (intro upoly_pos_subterm[OF a i], auto)
    have lc_er_pos: "?lc er > 0" unfolding er_def
      by (subst lead_coeff_comp[OF deg_r], insert lc_e_pos deg_r lc_r_pos, auto)

    from 1[folded poly_pcompose, folded er_def cl_def]  
    have er_cl_poly: "0 \<le> x \<Longrightarrow> poly er x + \<delta> \<le> poly cl x" for x by auto
    have "degree er \<le> degree cl"
    proof (intro degree_mono[of _ 0])
      show "0 \<le> ?lc er" using lc_er_pos by auto
      show "0 \<le> x \<Longrightarrow> poly er x \<le> poly cl x" for x using er_cl_poly[of x] \<delta>0 by auto
    qed 
    also have "degree er = d * degree (upoly r i)" 
      unfolding er_def d_def by simp
    also have "degree cl = d * degree (upoly l i)" 
      unfolding cl_def d_eq by simp
    finally have "degree (upoly l i) \<ge> degree (upoly r i)" using d_pos by auto
  } note deg_inequality = this

  {
    fix p :: "'a mpoly" and x
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
    hence "(f, 1) \<in> F_Q" unfolding F_Q_def F_def by auto
    from valid[OF this, unfolded valid_monotone_poly_def] obtain p 
      where p: "p = I f" "monotone_poly {..<1} p" "vars p = {0}" by auto  
    have id: "{..< (1 :: nat)} = {0}" by auto
    have "\<exists> q. I f = poly_to_mpoly 0 q \<and> degree q > 0" unfolding p(1)[symmetric]
      by (intro mono_unary_poly, insert p(2-3)[unfolded id], auto)
  } note unary_symbol = this

  {
    fix f and n :: nat and x :: var
    assume "f \<in> {g_sym, f_sym,a_sym}" "f = f_sym \<Longrightarrow> n = 9" "f \<in> {a_sym,g_sym} \<Longrightarrow> n = 2" 
    hence n: "n > 1" and f: "(f,n) \<in> F_Q" unfolding F_def F_Q_def by force+
    define p where "p = I f" 
    from valid[OF f, unfolded valid_monotone_poly_def, rule_format, OF refl p_def]
    have mono: "monotone_poly (vars p) p" and vars: "vars p = {..<n}" and valid: "valid_poly p" by auto 
    let ?t = "Fun f (replicate n (TVar x))" 
    have t_F: "funas_term ?t \<subseteq> F_Q" using f by auto
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
      \<and> vars p = {..<n} \<and> monotone_poly (vars p) p \<and> valid_poly p" 
      by (intro exI[of _ p] exI[of _ q'] conjI valid eq dq' p_def[symmetric] q't[symmetric] mono vars)
  } note g_f_a_sym = this

  from unary_symbol[of q_sym] obtain q where Iq: "I q_sym = poly_to_mpoly 0 q" and dq: "degree q > 0" by auto
  from unary_symbol[of h_sym] obtain h where Ih: "I h_sym = poly_to_mpoly 0 h" and dh: "degree h > 0" by auto

  from g_f_a_sym[of f_sym 9, of y3] obtain f fu where   
    If: "I f_sym = f" 
    and eval_fyy: "eval (Fun f_sym (replicate 9 (TVar y3))) = poly_to_mpoly y3 fu"
    and poly_f: "poly_to_mpoly y3 fu = substitute (\<lambda>i. PVar y3) f" 
    and df: "0 < degree fu"
    and vars_f: "vars f = {..<9}" 
    and mono_f: "monotone_poly (vars f) f" 
    and valid_f: "valid_poly f" by auto

  from g_f_a_sym[of a_sym 2, of y5] obtain a au where   
    Ia: "I a_sym = a" 
    and eval_ayy: "eval (Fun a_sym (replicate 2 (TVar y5))) = poly_to_mpoly y5 au"
    and poly_a: "poly_to_mpoly y5 au = substitute (\<lambda>i. PVar y5) a" 
    and da: "0 < degree au"
    and vars_a: "vars a = {..<2}" 
    and valid_a: "valid_poly a" 
    and mono_a: "monotone_poly (vars a) a" by auto

  with g_f_a_sym[of a_sym 2, of y6] obtain au' where   
     eval_ayy': "eval (Fun a_sym (replicate 2 (TVar y6))) = poly_to_mpoly y6 au'"
    and poly_a': "poly_to_mpoly y6 au' = substitute (\<lambda>i. PVar y6) a" 
    and da': "0 < degree au'"
     by auto

  from g_f_a_sym[of g_sym 2, of y2] obtain g gu where
    Ig: "I g_sym = g" 
    and eval_gyy: "eval (Fun g_sym (replicate 2 (TVar y2))) = poly_to_mpoly y2 gu"
    and poly_g: "poly_to_mpoly y2 gu = substitute (\<lambda>i. PVar y2) g" 
    and dg: "0 < degree gu"
    and vars_g: "vars g = {..<2}" 
    and valid_g: "valid_poly g" 
    and mono_g: "monotone_poly (vars g) g" by auto

  from unary_symbol[of "v_sym i" for i] have "\<forall> i. \<exists> q. i \<in> V \<longrightarrow> I (v_sym i) = poly_to_mpoly 0 q \<and> 0 < degree q" by auto
  from choice[OF this] obtain v where 
    Iv: "i \<in> V \<Longrightarrow> I (v_sym i) = poly_to_mpoly 0 (v i)" and 
    dv: "i \<in> V \<Longrightarrow> degree (v i) > 0" 
  for i by auto

  have eval_pm_Var: "eval (TVar y) = poly_to_mpoly y [:0,1:]" for y
    unfolding eval.simps mpoly_of_poly_is_poly_to_mpoly[symmetric] by simp
  have id: "(if 0 = (0 :: nat) then eval ([t] ! 0) else 0) = eval t" for t by simp

  { (* general terms *)
    fix y
    have y: "eval (TVar y) = poly_to_mpoly y [:0,1:]" (is "_ = poly_to_mpoly _ ?poly1") by fact  
    have hy: "eval (Fun h_sym [TVar y]) = poly_to_mpoly y h" using Ih
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y ?poly1])
       apply (unfold id, intro y)
      by simp
    have qy: "eval (Fun q_sym [TVar y]) = poly_to_mpoly y q" using Iq
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y ?poly1])
       apply (unfold id, intro y)
      by simp
    have qhy: "eval (Fun q_sym [Fun h_sym [TVar y]]) = poly_to_mpoly y (pcompose q h)" using Iq
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y h])
       apply (unfold id, intro hy)
      by simp
    have hqy: "eval (Fun h_sym [Fun q_sym [TVar y]]) = poly_to_mpoly y (pcompose h q)" using Ih
      apply (simp)
      apply (subst substitute_poly_to_mpoly[of _ _ y q])
       apply (unfold id, intro qy)
      by simp
    have hhqy: "eval (Fun h_sym [Fun h_sym [Fun q_sym [TVar y]]]) = poly_to_mpoly y (pcompose h (pcompose h q))" 
      apply (simp)
      apply (subst Ih)
      apply (subst substitute_poly_to_mpoly[of _ _ y "pcompose h q"])
       apply (unfold id, intro hqy)
      by simp
    { (* 1st pair of terms delivers degree h = 1 *)
      assume y: "y = 0"  
      have l: "eval (l 0) = poly_to_mpoly 0 (pcompose q h)" unfolding 
          l_def lhs_Q_def using y qhy by (simp add: Ih y1_def)
      have r: "eval (r 0) = poly_to_mpoly 0 (pcompose h (pcompose h q))" unfolding 
          r_def rhs_Q_def using y hhqy by (simp add: Ih y1_def)
      from deg_inequality[of 0, unfolded upoly_def l r poly_to_mpoly_inverse]
      have dh: "degree h = 1" using dq and dh by auto
    } note hy qy this
  }
  hence dh: "degree h = 1" 
    and hy: "\<And> y. eval (Fun h_sym [TVar y]) = poly_to_mpoly y h" 
    and qy: "\<And> y. eval (Fun q_sym [TVar y]) = poly_to_mpoly y q" 
    by auto

  { (* 2nd pair of terms for deg g = 1 *)
    have l: "eval (l 1) = poly_to_mpoly 1 h" unfolding 
        l_def lhs_Q_def using hy by (simp add: Ih y2_def)
    have "eval (r 1) = eval (Fun g_sym (replicate 2 (TVar y2)))" unfolding r_def rhs_Q_def
      apply (simp)
      apply (intro arg_cong[of _ _ "\<lambda> x. substitute x _"] ext)
      subgoal for i by (cases i; cases "i - 1"; auto)
      done
    also have "\<dots> = poly_to_mpoly y2 gu" by fact
    finally have r: "eval (r 1) = poly_to_mpoly 1 gu" by (auto simp: y2_def)
    from deg_inequality[of 1, unfolded upoly_def l r poly_to_mpoly_inverse] dh dg
    have "degree gu = 1" by auto
    from subst_same_var_monotone_imp_same_degree[OF mono_g this _ poly_g]
    have "total_degree g = 1" by auto
  } 
  hence dg: "total_degree g = 1" by auto
  
  { (* 3rd pair of terms for deg f = 1 *)
    have l: "eval (l 2) = poly_to_mpoly 2 h" unfolding 
        l_def lhs_Q_def using hy by (simp add: Ih y3_def)
    have "eval (r 2) = eval (Fun f_sym (replicate 9 (TVar y3)))" unfolding r_def rhs_Q_def
      by simp
    also have "\<dots> = poly_to_mpoly y3 fu" by fact
    finally have r: "eval (r 2) = poly_to_mpoly 2 fu" by (auto simp: y3_def)
    from deg_inequality[of 2, unfolded upoly_def l r poly_to_mpoly_inverse] df dh
    have "degree fu = 1" by auto
    from subst_same_var_monotone_imp_same_degree[OF mono_f this _ poly_f]
    have "total_degree f = 1" by auto
  } 
  hence df: "total_degree f = 1" by auto

  (* at this point we move on to coefficient level, e.g., 
     get all coefficient of the linear polynomials f, g and h *)

  {
    fix gs g
    assume gs: "(gs,1) \<in> F_Q" and I: "I gs = poly_to_mpoly 0 g" and dg: "degree g = 1" 
    from valid[OF gs, unfolded valid_monotone_poly_def, rule_format, OF refl I[symmetric]]
    have valid: "valid_poly (poly_to_mpoly 0 g)" "monotone_poly {..<1} (poly_to_mpoly 0 g)" 
      "vars (poly_to_mpoly 0 g) = {..<1}"
      by auto
    hence mono: "monotone_poly (vars (I gs)) (I gs)" unfolding I by auto
    have "total_degree (I gs) = 1" 
    proof (rule subst_same_var_monotone_imp_same_degree[OF mono dg, of 0], force)
      show "poly_to_mpoly 0 g = substitute (\<lambda>i. PVar 0) (I gs)" unfolding I
        by (intro mpoly_extI, auto simp: insertion_substitute)
    qed
    hence "total_degree (I gs) \<le> 1" by auto
    from monotone_linear_poly_to_coeffs[OF this valid[folded I]] 
    obtain c a where I': "I gs = Const c + Const a * PVar 0" and pos: "0 \<le> c" "1 \<le> a" 
      by auto
    from I' have "I gs = poly_to_mpoly 0 [:c, a:]" 
      unfolding mpoly_of_poly_is_poly_to_mpoly[symmetric] by simp
    from arg_cong[OF this[unfolded I], of "mpoly_to_poly 0"]
    have "g = [:c,a:]" by (simp add: poly_to_mpoly_inverse)
    with I' pos have "\<exists> c a. I gs = Const c + Const a * PVar 0 \<and> 0 \<le> c \<and> 1 \<le> a \<and> g = [:c,a:]" by auto
  } note unary_linear = this[unfolded F_Q_def F_def]

  from unary_linear[OF _ Ih dh] obtain h0 h1 where
    Ih': "I h_sym = Const h0 + Const h1 * PVar 0" 
    and h0: "0 \<le> h0" 
    and h1: "1 \<le> h1" 
    and h: "h = [:h0,h1:]" 
    by auto

  from df have "total_degree f \<le> 1" by auto
  from monotone_linear_poly_to_coeffs[OF this valid_f mono_f[unfolded vars_f] vars_f] 
  obtain f0 fi where f: "f = Const f0 + (\<Sum>i\<leftarrow>[0..<9]. Const (fi i) * PVar i)"
    and f0: "0 \<le> f0" and fi: "\<And> i. i<9 \<Longrightarrow> 1 \<le> fi i" 
    by auto

  from dg have "total_degree g \<le> 1" by auto
  from monotone_linear_poly_to_coeffs[OF this valid_g mono_g[unfolded vars_g] vars_g] 
  obtain g0 gi where g: "g = Const g0 + (\<Sum>i\<leftarrow>[0..<2]. Const (gi i) * PVar i)"
    and g0: "0 \<le> g0" and gi: "\<And> i. i<2 \<Longrightarrow> 1 \<le> gi i" 
    by auto
  define g1 where "g1 = gi 0" 
  define g2 where "g2 = gi 1" 
  have id2: "[0..<2] = [0,1 :: nat]" by code_simp
  from gi[of 0] gi[of 1] have g1: "g1 \<ge> 1" and g2: "g2 \<ge> 1" by (auto simp: g1_def g2_def)
  have g: "g = Const g0 + Const g1 * PVar 0 + Const g2 * PVar 1" 
    unfolding g g1_def g2_def by (auto simp: id2)

  define \<alpha> where "\<alpha> = (\<lambda> x :: var. 0 :: 'a)" 
  have \<alpha>: "assignment \<alpha>" unfolding \<alpha>_def assignment_def by auto
  {
    fix i :: nat 
    assume i: "i < 9"  
    from i have "i \<in> set [0..<9]" by auto
    from split_list[OF this] obtain bef aft where id: "[0..<9] = bef @ [i] @ aft" by auto
    define ba where "ba = bef @ aft"   
    have "distinct [0..<9]" by simp
    from this[unfolded id]
    have "i \<notin> set (bef @ aft)" by auto
    with id have iba: "set ba = {0..<9} - {i}" unfolding ba_def
      by (metis Diff_insert_absorb Un_insert_right append_Cons append_Nil list.simps(15) set_append set_upt)
    have len: "length [0..<9] = 9" by simp
    define diff where "diff = (\<Sum>x\<leftarrow>ba. fi x * insertion \<alpha> (eval (r x))) - (\<Sum>x\<leftarrow>ba. fi x * insertion \<alpha> (eval (l x))) + \<delta>" 
    {
      fix x :: 'a
      assume x: "x \<ge> 0"
      define a where "a = \<alpha>(i := x)" 
      have a: "assignment a" using \<alpha> unfolding a_def assignment_def using x by auto
      from gt[unfolded gt_poly_def, rule_format, OF this]
      have "insertion a (eval rhs_Q) + \<delta> \<le> insertion a (eval lhs_Q)" by auto
      also have "insertion a (eval lhs_Q) =  f0 + (\<Sum>x\<leftarrow>[0..<9]. fi x * insertion a (eval (l x)))" 
        unfolding lhs_Q eval.simps If f length_map len insertion_substitute insertion_add insertion_Const
          insertion_sum_list insertion_mult map_map o_def insertion_Var
        by (intro arg_cong[of _ _ "\<lambda> x. (+) _ (sum_list x)"] map_cong refl arg_cong[of _ _ "(*) _"], simp)
      also have "(\<Sum>x\<leftarrow>[0..<9]. fi x * insertion a (eval (l x))) = 
       (\<Sum>x\<leftarrow>ba. fi x * insertion a (eval (l x))) + fi i * insertion a (eval (l i))" 
        unfolding id ba_def by simp
      also have "(\<Sum>x\<leftarrow>ba. fi x * insertion a (eval (l x))) = (\<Sum>x\<leftarrow>ba. fi x * insertion \<alpha> (eval (l x)))" 
        apply (intro arg_cong[of _ _ sum_list] map_cong refl arg_cong[of _ _ "(*) _"] insertion_irrelevant_vars)
        subgoal for v j unfolding iba using eval_l_r[of v l] by (auto simp: a_def)      
        done
      also have "insertion a (eval rhs_Q) = f0 + (\<Sum>x\<leftarrow>[0..<9]. fi x * insertion a (eval (r x)))" 
        unfolding rhs_Q eval.simps If f length_map len insertion_substitute insertion_add insertion_Const
          insertion_sum_list insertion_mult map_map o_def insertion_Var
        by (intro arg_cong[of _ _ "\<lambda> x. (+) _ (sum_list x)"] map_cong refl arg_cong[of _ _ "(*) _"], simp)
      also have "(\<Sum>x\<leftarrow>[0..<9]. fi x * insertion a (eval (r x))) = 
       (\<Sum>x\<leftarrow>ba. fi x * insertion a (eval (r x))) + fi i * insertion a (eval (r i))" 
        unfolding id ba_def by simp
      also have "(\<Sum>x\<leftarrow>ba. fi x * insertion a (eval (r x))) = (\<Sum>x\<leftarrow>ba. fi x * insertion \<alpha> (eval (r x)))" 
        apply (intro arg_cong[of _ _ sum_list] map_cong refl arg_cong[of _ _ "(*) _"] insertion_irrelevant_vars)
        subgoal for v j unfolding iba using eval_l_r[of v r] by (auto simp: a_def)      
        done
      finally have ineq: "fi i * insertion a (eval (r i)) \<le> fi i * insertion a (eval (l i)) - diff" 
        unfolding diff_def by (simp add: algebra_simps)  
      from fi[OF i] have fi: "fi i \<noteq> 0" and inv: "inverse (fi i) \<ge> 0" by auto
      from mult_left_mono[OF ineq inv]
      have "insertion a (eval (r i)) \<le> insertion a (eval (l i)) + (- inverse (fi i) * diff)" 
        using fi by (simp add: field_simps)
    }
    hence "\<exists> diff. \<forall> x \<ge> 0. insertion (\<alpha>(i := x)) (eval (r i)) \<le> insertion (\<alpha>(i := x)) (eval (l i)) + diff" 
      by blast
  }
  hence "\<forall> i. \<exists> diff. i < 9 \<longrightarrow> (\<forall> x \<ge> 0. insertion (\<alpha>(i := x)) (eval (r i)) \<le> insertion (\<alpha>(i := x)) (eval (l i)) + diff)" 
    by auto
  from choice[OF this]

  text \<open>Inequality (2) in paper\<close>
  obtain diff where inequality2: "\<And> i x. i < 9 \<Longrightarrow> x \<ge> 0 \<Longrightarrow> 
    insertion (\<alpha>(i := x)) (eval (r i)) \<le> insertion (\<alpha>(i := x)) (eval (l i)) + diff i" 
    by auto

  note [simp] = insertion_mult insertion_add insertion_substitute

  define delt2 where "delt2 = h0 + diff 1 - g0" 
  { (* use pair 2 for h1 \<ge> 2 *)
    fix x
    assume "x \<ge> (0 :: 'a)" 
    from inequality2[of 1, OF _ this]
    have "insertion (\<alpha>(1 := x)) (eval (r 1)) \<le> insertion (\<alpha>(1 := x)) (eval (l 1)) + diff 1" by auto
    also have "insertion (\<alpha>(1 := x)) (eval (r 1)) = g0 + g1 * x + g2 * x" 
      by (simp add: r_def rhs_Q_def Ig g y2_def)
    also have "insertion (\<alpha>(1 := x)) (eval (l 1)) = h0 + x * h1" 
      by (simp add: l_def lhs_Q_def Ih h y2_def)
    finally have "(g1 + g2 - h1) * x \<le> delt2" unfolding delt2_def
      by (simp add: algebra_simps)
  } note ineq2 = this
  from bounded_negative_factor[OF this] have "g1 + g2 \<le> h1" by auto
  with g1 g2 have h1: "h1 \<ge> 2" by auto

  (* use pair 1 for deg(q) \<ge> 2 *)
  {
    assume "degree q = 1" 
    from unary_linear[OF _ Iq this]
    obtain q0 q1 where Iq': "I q_sym = Const q0 + Const q1 * PVar 0"
      and q0: "0 \<le> q0" and q1: "1 \<le> q1" and q: "q = [:q0, q1:]" 
      by auto
    define d1 where "d1 = h0 + h0 * h1 + h1 * h1 * q0" 
    define d2 where "d2 = q0 + h0 * q1" 
    define delt1 where "delt1 = d2 + diff 0 - d1" 
    define fact1 where "fact1 = (q1 * h1 * h1 - h1 * q1)" 
    {
      fix x :: 'a
      assume x: "x \<ge> 0" 
      from inequality2[of 0, OF _ this]
      have "insertion (\<alpha>(0 := x)) (eval (r 0)) \<le> insertion (\<alpha>(0 := x)) (eval (l 0)) + diff 0" by auto
      also have "insertion (\<alpha>(0 := x)) (eval (r 0)) = d1 + q1 * h1 * h1 * x" 
        by (simp add: r_def rhs_Q_def Ih h Iq q y1_def field_simps d1_def)
      also have "insertion (\<alpha>(0 := x)) (eval (l 0)) = d2 + h1 * q1 * x" 
        by (simp add: l_def lhs_Q_def Ih h Iq q y1_def field_simps d2_def)
      finally have "fact1 * x \<le> delt1" by (simp add: field_simps delt1_def fact1_def)
    } note ineq1 = this
    from bounded_negative_factor[OF this]
    have "fact1 \<le> 0" .
    from this[unfolded fact1_def] h1 q1 have False by auto
  }
  with dq have dq: "degree q \<ge> 2" by (cases "degree q"; cases "degree q - 1"; auto)

  have "(z_sym, 0) \<in> F_Q" unfolding F_def F_Q_def by auto
  from valid[OF this, unfolded valid_monotone_poly_def, rule_format, OF refl refl]
  obtain z where Iz: "I z_sym = z" and vars_z: "vars z = {}" and valid_z: "valid_poly z" by auto
  from vars_empty_Const[OF vars_z] obtain z0 where z: "z = Const z0" by auto
  from valid_z[unfolded valid_poly_def, rule_format, OF \<alpha>, unfolded z] have z0: "z0 \<ge> 0" by auto

  {
    fix i
    assume "i \<in> V" 
    hence "v_sym i \<in> {q_sym, h_sym} \<union> v_sym ` V" by auto
    note unary_symbol[OF this]
  }
  hence "\<forall> i. \<exists>q. i \<in> V \<longrightarrow> I (v_sym i) = poly_to_mpoly 0 q \<and> 0 < degree q" by auto
  from choice[OF this] obtain v where Iv: "\<And> i. i \<in> V \<Longrightarrow> I (v_sym i) = poly_to_mpoly 0 (v i)"
    and dv: "\<And> i. i \<in> V \<Longrightarrow> 0 < degree (v i)" 
    by auto
  

  define const_t where "const_t = insertion \<alpha> (eval t_t)"   
  have const_t: "const_t > 0" 
    unfolding const_t_def
    by (rule eval_t_t_gt_0[OF Ig[unfolded g] Iz[unfolded z]], insert z0 g0 g1 g2, auto)


  (* use pair 4 for deg q = 2 *)
  {
    define d1 where "d1 = g0 + g2 * h0 +  g2 * h1 * h0 + g2 * h1 * h1 * h0" 
    define c where "c = g0 + g2 * const_t" 
    define delt4 where "delt4 = d1 + diff 3" 
    have [simp]: "insertion a (eval t_t) = const_t" for a unfolding const_t_def
      by (rule insertion_irrelevant_vars, insert vars_t vars_eval, force) 
    let ?qq = "q \<circ>\<^sub>p [:c, g1:] - smult g1 q" 
    define qq where "qq = ?qq" 
    define hhh where "hhh = [:delt4, g2 * h1 * h1 * h1:]" 
    {
      fix x :: 'a
      assume x: "x \<ge> 0" 
      from inequality2[of 3, OF _ this]
      have "insertion (\<alpha>(3 := x)) (eval (r 3)) \<le> insertion (\<alpha>(3 := x)) (eval (l 3)) + diff 3" by auto
      also have "insertion (\<alpha>(3 := x)) (eval (r 3)) = poly q (g0 + g1 * x + g2 * const_t)" 
        by (simp add: r_def rhs_Q_def y4_def Iq Ig g)
      also have "insertion (\<alpha>(3 := x)) (eval (l 3)) = 
        g1 * poly q x + g2 * h1 * h1 * h1 * x + d1" 
        by (simp add: l_def lhs_Q_def y4_def Iq Ig g Ih h field_simps d1_def)
      finally have "poly q (g0 + g1 * x + g2 * const_t) - poly (smult g1 q) x - g2 * h1 * h1 * h1 * x \<le> delt4"
        by (simp add: delt4_def)
      also have "g2 * h1 * h1 * h1 * x = poly [:0, g2 * h1 * h1 * h1:] x" by simp
      also have "poly q (g0 + g1 * x + g2 * const_t) = poly (pcompose q [:c, g1 :]) x" 
        by (simp add: poly_pcompose ac_simps c_def)
      finally have "poly qq x \<le> poly hhh x" 
        by (simp add: qq_def hhh_def)
    } note ineq3 = this

    have lq0: "lead_coeff q > 0" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      with dq have lq: "lead_coeff (- q) > 0" by (cases "q = 0", auto)
      from poly_pinfty_ge[OF this, of 1] dq obtain n where "\<And> x. x \<ge> n \<Longrightarrow> poly q x \<le> -1" by auto
      from this[of "max n 0"] have 1: "poly q (max n 0) \<le> - 1" by auto
      let ?a = "\<lambda> x :: var. max n 0" 
      have a: "assignment ?a" unfolding assignment_def by auto
      have "(q_sym,1) \<in> F_Q" unfolding F_Q_def by auto
      from valid[OF this, unfolded valid_monotone_poly_def, rule_format, OF refl Iq[symmetric]]
      have "valid_poly (poly_to_mpoly 0 q)" by auto
      from this[unfolded valid_poly_def, rule_format, OF a]
      have "0 \<le> poly q (max n 0)" by auto
      with 1 show False by auto
    qed
        
    from const_t g0 g2 have c: "c > 0" unfolding c_def
      by (metis le_add_same_cancel2 linorder_not_le mult_less_cancel_right2 order_le_less_trans order_less_le)

    have "degree hhh \<le> 1" unfolding hhh_def by simp

    from criterion_for_degree_2[OF qq_def dq ineq3 this g1 lq0 c]
    have "degree q = 2" "g1 = 1" by auto
  }
  hence dq: "degree q = 2" and g1: "g1 = 1" by auto


  { (* 5th and 6th pairs of terms to get degree a = degree q = 2 *)
    have l: "eval (l 4) = poly_to_mpoly 4 q" unfolding 
        l_def lhs_Q_def using qy by (simp add: y5_def)
    have "eval (r 4) = eval (Fun a_sym (replicate 2 (TVar y5)))" unfolding r_def rhs_Q_def
      apply (simp)
      apply (intro arg_cong[of _ _ "\<lambda> x. substitute x _"] ext)
      subgoal for i by (cases i; cases "i - 1"; auto)
      done
    also have "\<dots> = poly_to_mpoly y5 au" by fact
    finally have r: "eval (r 4) = poly_to_mpoly 4 au" by (auto simp: y5_def)
    from deg_inequality[of 4, unfolded upoly_def l r poly_to_mpoly_inverse] 
    have "degree au \<le> degree q" by auto
    with subst_same_var_monotone_imp_same_degree[OF mono_a refl _ poly_a] da 
    have "total_degree a \<le> degree q" by auto
  } 
  hence d_aq: "total_degree a \<le> degree q" by auto

  { (* 6th pair of terms *)
    have r: "eval (r 5) = poly_to_mpoly 5 q" unfolding 
        r_def rhs_Q_def using qy by (simp add: y6_def)
    have "eval (l 5) = eval (Fun a_sym (replicate 2 (TVar y6)))" unfolding l_def lhs_Q_def
      apply (simp)
      apply (intro arg_cong[of _ _ "\<lambda> x. substitute x _"] ext)
      subgoal for i by (cases i; cases "i - 1"; auto)
      done
    also have "\<dots> = poly_to_mpoly y6 au'" by fact
    finally have l: "eval (l 5) = poly_to_mpoly 5 au'" by (auto simp: y6_def)
    from deg_inequality[of 5, unfolded upoly_def l r poly_to_mpoly_inverse] 
    have "degree q \<le> degree au'" by auto
    with subst_same_var_monotone_imp_same_degree[OF mono_a refl _ poly_a'] da'
    have "degree q \<le> total_degree a" by auto
  } 

  with d_aq
  have d_aq: "total_degree a = degree q" by auto

  with dq have da: "total_degree a = 2" by simp
  have "vars a = {0,1}" unfolding vars_a by code_simp

  from binary_degree_2_poly[OF _ this] da
  obtain a0 a1 a2 a3 a4 a5 where a: "a = Const a0 + Const a1 * PVar 0 + Const a2 * PVar 1 + 
     Const a3 * PVar 0 * PVar 0 + Const a4 * PVar 1 * PVar 1 +
     Const a5 * PVar 0 * PVar 1" by auto


  (* use inequality 7 to derive a4 = 0 *)
  define d1 where "d1 = a0 + a1 * z0 + a3 * z0 * z0" 
  define d2 where "d2 = (a2  + a5 * z0)" 
  define delt7 where "delt7 = diff 6 - d1" 
  { 
    fix x
    assume "x \<ge> (0 :: 'a)" 
    from inequality2[of 6, OF _ this]
    have "insertion (\<alpha>(6 := x)) (eval (r 6)) \<le> insertion (\<alpha>(6 := x)) (eval (l 6)) + diff 6" by auto
    also have "insertion (\<alpha>(6 := x)) (eval (r 6)) = a4 * x * x + d2 * x + d1" 
      by (simp add: r_def rhs_Q_def Ig g y7_def Ia a Iz z algebra_simps d1_def d2_def)
    also have "insertion (\<alpha>(6 := x)) (eval (l 6)) = x" 
      by (simp add: l_def lhs_Q_def Ih h y7_def)
    finally have "0 \<ge> poly [:-delt7,d2 - 1,a4:] x" unfolding delt7_def
      by (simp add: algebra_simps)
  } note ineq7 = this
  {
    define p where "p = [:-delt7,d2 - 1,a4:]" 
    assume "a4 > 0" 
    hence "lead_coeff p > 0" "degree p > 0" by (auto simp: p_def)
    with poly_pinfty_ge[OF this(1), of 1] obtain n where "\<And> x. x\<ge>n \<Longrightarrow> 1 \<le> poly p x" by blast
    from this[of "max n 0"] ineq7[of "max n 0"] have False unfolding p_def by auto
  } 
  hence a4: "a4 \<le> 0" by force

  note valid_a = valid_a[unfolded a valid_poly_def, rule_format]
  {
    define p where "p = [:-a0,-a2,-a4:]" 
    assume "a4 < 0" 
    hence p: "lead_coeff p > 0" "degree p \<noteq> 0" unfolding p_def by auto
    {
      fix x :: 'a
      assume "x \<ge> 0" 
      hence "assignment (\<lambda> v. if v = 1 then x else 0)" unfolding assignment_def by auto
      from valid_a[OF this]
      have "0 \<ge> poly p x" by (auto simp: algebra_simps p_def)
    }
    with poly_pinfty_ge[OF p] have False 
      by (metis (no_types, opaque_lifting) dual_order.trans nle_le not_one_le_zero)
  }
  with a4 have a4: "a4 = 0" by force

  (* use inequalities 8 to derive a3 = 0 *)
  define d1 where "d1 = a0 + a2 * z0" 
  define d2 where "d2 = (a5 * z0 + a1)" 
  define delt8 where "delt8 = diff 7 - d1" 
  { 
    fix x
    assume "x \<ge> (0 :: 'a)" 
    from inequality2[of 7, OF _ this]
    have "insertion (\<alpha>(7 := x)) (eval (r 7)) \<le> insertion (\<alpha>(7 := x)) (eval (l 7)) + diff 7" by auto
    also have "insertion (\<alpha>(7 := x)) (eval (r 7)) = d1 + a3 * (x * x) + d2 * x" 
      by (simp add: r_def rhs_Q_def Ig g y8_def Ia a a4 Iz z algebra_simps d1_def d2_def)
    also have "insertion (\<alpha>(7 := x)) (eval (l 7)) = x" 
      by (simp add: l_def lhs_Q_def Ih h y8_def)
    finally have "0 \<ge> poly [:-delt8,d2 - 1,a3:] x" unfolding delt8_def
      by (simp add: algebra_simps)
  } note ineq8 = this
  {
    define p where "p = [:-delt8,d2 - 1,a3:]" 
    assume "a3 > 0" 
    hence "lead_coeff p > 0" "degree p > 0" by (auto simp: p_def)
    with poly_pinfty_ge[OF this(1), of 1] obtain n where "\<And> x. x\<ge>n \<Longrightarrow> 1 \<le> poly p x" by blast
    from this[of "max n 0"] ineq8[of "max n 0"] have False unfolding p_def by auto
  } 
  hence a3: "a3 \<le> 0" by force
  {
    define p where "p = [:-a0,-a1,-a3:]" 
    assume "a3 < 0" 
    hence p: "lead_coeff p > 0" "degree p \<noteq> 0" unfolding p_def by auto
    {
      fix x :: 'a
      assume "x \<ge> 0" 
      hence "assignment (\<lambda> v. if v = 0 then x else 0)" unfolding assignment_def by auto
      from valid_a[OF this, simplified]
      have "0 \<ge> poly p x" by (auto simp: algebra_simps p_def)
    }
    with poly_pinfty_ge[OF p] have False 
      by (metis (no_types, opaque_lifting) dual_order.trans nle_le not_one_le_zero)
  }
  with a3 have a3: "a3 = 0" by force

  (* restrict shape of polynomial a further, so that we can access encoding results *)
  from a a3 a4 have a: "a = Const a5 * PVar 0 * PVar 1 + Const a1 * PVar 0 + Const a2 * PVar 1 + Const a0" by simp
  note valid_a = valid_a[unfolded a3 a4]
  from valid_a[OF \<alpha>, simplified, unfolded \<alpha>_def]
  have a0: "a0 \<ge> 0" by auto

  note mono_a' =  mono_a[unfolded monotone_poly_wrt_def, rule_format, unfolded vars_a, OF \<alpha>, unfolded a, simplified,
    unfolded \<alpha>_def, simplified]
  from mono_a'[of 0] have a1: "\<delta> \<le> x \<Longrightarrow> \<delta> \<le> a1 * x" for x by auto 
  from mono_a'[of 1] have a2: "\<delta> \<le> x \<Longrightarrow> \<delta> \<le> a2 * x" for x by auto
  {
    fix a 
    assume "a \<in> {a1,a2}" 
    with a1 a2 have "\<delta> \<le> x \<Longrightarrow> \<delta> \<le> a * x" for x by auto
    with \<delta>0 have "a \<ge> 1"
      using mult_le_cancel_right1 by auto
    hence "a > 0" by simp
  }
  hence a1: "a1 > 0" and a2: "a2 > 0" by auto

  {
    assume a5: "a5 = 0" 
    from da[unfolded a a5]
    have "2 = total_degree (Const a1 * PVar 0 + Const a2 * PVar (Suc 0) + Const a0)" by simp
    also have "\<dots> \<le> 1" 
      by (intro total_degree_add total_degree_Const_mult, auto)
    finally have False by simp
  }
  hence a5: "a5 \<noteq> 0" by force
  {
    define p where "p = [:-a0, -a1 -a2, - a5:]" 
    assume a5: "a5 < 0" 
    hence p: "lead_coeff p > 0" "degree p \<noteq> 0" by (auto simp: p_def)
    {
      fix x :: 'a
      assume "x \<ge> 0" 
      hence "assignment (\<lambda> _. x)" by (auto simp: assignment_def)
      from valid_a[OF this]
      have "0 \<ge> poly p x" by (simp add: p_def algebra_simps)
    }
    with poly_pinfty_ge[OF p] have False 
      by (metis (no_types, opaque_lifting) dual_order.trans nle_le not_one_le_zero)
  }
  with a5 have a5: "a5 > 0" by force

  define I' where "I' = (\<lambda> f. if f \<in> v_sym ` (UNIV - V) then PVar 0 else I f)"
  define v' where "v' = (\<lambda> i. if i \<in> V then v i else [:0,1:])"   
  have Iv': "I' (v_sym i) = poly_to_mpoly 0 (v' i)" for i
    unfolding I'_def v'_def using Iv by (auto simp: mpoly_of_poly_is_poly_to_mpoly[symmetric])
  have dv': "0 < degree (v' i)" for i  using dv[of i] by (auto simp: v'_def)
  have Ia': "I' a_sym = a" unfolding I'_def using Ia by auto
  have Iz': "I' z_sym = z" unfolding I'_def using Iz by auto
  {
    fix i
    have "nneg_poly (v' i)" 
    proof (cases "i \<in> V")
      case False
      thus ?thesis by (auto simp: v'_def)
    next
      case i: True
      hence id: "v' i = v i" by (auto simp: v'_def)
      from i have "(v_sym i, 1) \<in> F_Q" unfolding F_Q_def F_def by auto
      from valid[OF this, unfolded valid_monotone_poly_def] Iv[OF i]
      have valid: "valid_poly (poly_to_mpoly 0 (v i) )" by auto
      define p where "p = v i" 
      have valid: "0 \<le> x \<Longrightarrow> 0 \<le> poly p x" for x unfolding p_def
        using valid[unfolded valid_poly_def, rule_format, of "\<lambda> _. x"]
        by (auto simp: assignment_def)
      hence "nneg_poly p" by (intro nneg_polyI, auto) 
      thus ?thesis unfolding id p_def .
    qed
  } note nneg_v = this

  {
    fix r x
    assume "r \<in> {p,?q}"
    with pq funas_encode_poly_p[of x] funas_encode_poly_q[of x] 
    have pos: "positive_poly r" and inF: "funas_term (encode_poly x r) \<subseteq> F" by auto
    from degree_eval_encode_poly_generic[of I', unfolded mpoly_of_poly_is_poly_to_mpoly, 
        OF Ia'[unfolded a] Iz'[unfolded z] _ a5 a1 a2 a0 z0, of v', OF Iv' nneg_v dv' pos refl, of x]
    obtain rr where id: "poly_to_mpoly x rr = poly_inter.eval I' (encode_poly x r)" 
      and deg: "int (degree rr) = insertion (\<lambda>i. int (degree (v' i))) r" 
      and nneg: "nneg_poly rr" 
      by auto
    have "poly_to_mpoly x rr = poly_inter.eval I (encode_poly x r)" unfolding id
    proof (rule poly_inter_eval_cong)
      fix f a
      assume "(f,a) \<in> funas_term (encode_poly x r)" 
      hence "(f,a) \<in> F" using inF by auto
      thus "I' f = I f" unfolding F_def I'_def by auto
    qed
    with deg nneg have "\<exists>p. mpoly_of_poly x p = eval (encode_poly x r) \<and>
      int (degree p) = insertion (\<lambda>i. int (degree (v' i))) r \<and> nneg_poly p" 
      by (auto simp: mpoly_of_poly_is_poly_to_mpoly)
  } note encode = this
  from encode[of p y9]
  obtain pp where pp: "mpoly_of_poly y9 pp = eval (encode_poly y9 p)" 
       "int (degree pp) = insertion (\<lambda>i. int (degree (v' i))) p"
       "nneg_poly pp" by auto

  from encode[of ?q y9]
  obtain qq where qq: "mpoly_of_poly y9 qq = eval (encode_poly y9 ?q)" 
       "int (degree qq) = insertion (\<lambda>i. int (degree (v' i))) ?q"
       "nneg_poly qq" by auto

  (* use degree-inequality 9 for final solution *)
  define ppp where "ppp = (pp * [:a1, a5:] + [:a0, a2:])" 
  from deg_inequality[of 8]
  have "degree (upoly r 8) \<le> degree (upoly l 8)" by simp
  also have "upoly r 8 = mpoly_to_poly 8
     (mpoly_of_poly y9 [: a1, a5 :] * mpoly_of_poly y9 qq + mpoly_of_poly y9 [: a0, a2:])" 
    unfolding r_def rhs_Q_def by (simp add: upoly_def Ia a qq algebra_simps)
  also have "\<dots> = qq * [:a1, a5:] + [:a0, a2:]" unfolding mpoly_of_poly_add[symmetric] mpoly_of_poly_mult[symmetric] 
    unfolding mpoly_of_poly_is_poly_to_mpoly y9_def poly_to_mpoly_inverse by simp 
  also have "degree \<dots> = 1 + degree qq" 
    by (rule nneg_poly_degree_add_1[OF qq(3)], insert a5 a2, auto)
  also have "upoly l 8 = mpoly_to_poly 8
     (mpoly_of_poly y9 [: h0 :] + mpoly_of_poly y9 [: h1:] * (mpoly_of_poly y9 [: a1, a5 :] * mpoly_of_poly y9 pp + mpoly_of_poly y9 [: a0, a2:]))" 
    unfolding l_def lhs_Q_def by (simp add: upoly_def Ih h mpoly_of_poly_is_poly_to_mpoly[symmetric] Ia a pp algebra_simps)
  also have "\<dots> = [:h0:] + [: h1 :] * ppp" unfolding mpoly_of_poly_add[symmetric] mpoly_of_poly_mult[symmetric] ppp_def
    unfolding mpoly_of_poly_is_poly_to_mpoly y9_def poly_to_mpoly_inverse by simp 
  also have "degree \<dots> = degree ([:h1:] * ppp)"
    by (metis degree_add_eq_right degree_add_le degree_pCons_0 le_zero_eq zero_less_iff_neq_zero)
  also have "\<dots> = degree ppp" using h1 by simp
  also have "\<dots> = 1 + degree pp" unfolding ppp_def
    by (rule nneg_poly_degree_add_1[OF pp(3)], insert a5 a2, auto)
  finally have deg_qq_pp: "int (degree qq) \<le> int (degree pp)" by simp 

  show ?thesis unfolding positive_poly_problem_def[OF pq]
  proof (intro exI[of _ "(\<lambda>i. int (Polynomial.degree (v' i)))"] conjI deg_qq_pp[unfolded pp(2) qq(2)])
    show "positive_interpr (\<lambda>i. int (Polynomial.degree (v' i)))" 
      unfolding positive_interpr_def using dv' by auto
  qed
qed
end

context poly_input
begin
  
corollary polynomial_termination_with_delta_orders_undecidable: 
  "positive_poly_problem p q \<longleftrightarrow> 
   termination_by_delta_poly_interpretation (TYPE('a :: floor_ceiling)) F_Q Q"
proof
  show "positive_poly_problem p q \<Longrightarrow> termination_by_delta_poly_interpretation TYPE('a) F_Q Q"     
    using solution_impl_delta_termination_of_Q by blast
  assume "termination_by_delta_poly_interpretation TYPE('a) F_Q Q" 
  interpret term_delta_poly_input p q "TYPE('a)" 
    by (unfold_locales, fact)
  from solution show "positive_poly_problem p q" by auto
qed

end

end