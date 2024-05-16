section \<open>Undecidability of Linear Polynomial Termination\<close>

theory Linear_Poly_Termination_Undecidable
  imports 
    Hilbert10_to_Inequality
    Polynomial_Interpretation
begin

text \<open>Definition 3.1\<close>

locale poly_input = 
  fixes p q :: "int mpoly" 
  assumes pq: "positive_poly p" "positive_poly q" 
begin

datatype symbol = a_sym | z_sym | o_sym | f_sym | v_sym var | q_sym | h_sym | g_sym

abbreviation a_t where "a_t t1 t2 \<equiv> Fun a_sym [t1, t2]"
abbreviation z_t where "z_t \<equiv> Fun z_sym []" 
abbreviation o_t where "o_t \<equiv> Fun o_sym []" 
abbreviation f_t where "f_t t1 t2 t3 t4 \<equiv> Fun f_sym [t1,t2,t3,t4]" 
abbreviation v_t where "v_t i t \<equiv> Fun (v_sym i) [t]" 

definition encode_num :: "var \<Rightarrow> int \<Rightarrow> (symbol,var)term" where
  "encode_num x n = ((\<lambda> t. a_t (Var x) t)^^(nat n)) z_t" 

definition encode_monom :: "var \<Rightarrow> monom \<Rightarrow> int \<Rightarrow> (symbol,var)term" where
  "encode_monom x m c = rec_list (encode_num x c) (\<lambda> (i,e) _. (\<lambda> t. v_t i t)^^e) (var_list m)" 

definition encode_poly :: "var \<Rightarrow> int mpoly \<Rightarrow> (symbol,var)term" where
  "encode_poly x r = rec_list z_t (\<lambda> (m,c) _ t. a_t (encode_monom x m c) t) (monom_list r)" 

lemma vars_encode_num: "vars_term (encode_num x n) \<subseteq> {x}" 
proof -
  define m where "m = nat n" 
  show ?thesis
    unfolding encode_num_def m_def[symmetric]
    by (induct m, auto)
qed

lemma vars_encode_monom: "vars_term (encode_monom x m c) \<subseteq> {x}" 
proof -
  define xes where "xes = var_list m" 
  show ?thesis unfolding encode_monom_def xes_def[symmetric]
  proof (induct xes)
    case Nil
    thus ?case using vars_encode_num by auto
  next
    case (Cons ye xes)
    obtain y e where ye: "ye = (y,e)" by force
    have [simp]: "vars_term ((v_t y ^^ e) t) = vars_term t" for t :: "(symbol,var)term" 
      by (induct e arbitrary: t, auto)
    from Cons show ?case unfolding ye by auto
  qed
qed

lemma vars_encode_poly: "vars_term (encode_poly x r) \<subseteq> {x}" 
proof - 
  define mcs where "mcs = monom_list r" 
  show ?thesis unfolding encode_poly_def mcs_def[symmetric]
  proof (induct mcs)
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    from Cons show ?case unfolding mc using vars_encode_monom[of x m c] by auto
  qed auto
qed

definition V where "V = vars p \<union> vars q" 

definition y1 :: var where "y1 = 0" 
definition y2 :: var where "y2 = 1" 
definition y3 :: var where "y3 = 2" 

lemma y_vars: "y1 \<noteq> y2" "y2 \<noteq> y3" "y1 \<noteq> y3" 
  unfolding y1_def y2_def y3_def by auto


text \<open>Definition 3.3\<close>

definition "lhs_R = f_t (Var y1) (Var y2) (a_t (encode_poly y3 p) (Var y3)) o_t" 
definition "rhs_R = f_t (a_t (Var y1) z_t) (a_t z_t (Var y2)) (a_t (encode_poly y3 q) (Var y3)) z_t"

definition F where "F = {(a_sym, 2), (z_sym, 0)} \<union> (\<lambda> i. (v_sym i, 1 :: nat)) ` V" 
definition F_R where "F_R = {(f_sym,4), (o_sym, 0)} \<union> F"

definition R where "R = {(lhs_R,rhs_R)}" 

definition V_list where "V_list = sorted_list_of_set V" 
 
definition contexts :: "(symbol \<times> nat \<times> nat) list"
  where "contexts = [ 
  (a_sym, 2, 0), 
  (a_sym, 2, 1),
  (f_sym, 4, 0), 
  (f_sym, 4, 1),
  (f_sym, 4, 2), 
  (f_sym, 4, 3)] @ 
  map (\<lambda> i. (v_sym i, 1,0)) V_list"

text \<open>replace t by f(z,...z,t,z,...,z)\<close>
definition z_context :: "symbol \<times> nat \<times> nat \<Rightarrow> (symbol, var)term \<Rightarrow> (symbol, var) term" where
  "z_context c t = (case c of (f,n,i) \<Rightarrow> Fun f (replicate i z_t @ [t] @ replicate (n - i - 1) z_t))" 

definition z_contexts where 
  "z_contexts cs = foldr z_context cs" 

definition all_symbol_pos_ctxt :: "(symbol,var)term \<Rightarrow> (symbol,var)term" where
  "all_symbol_pos_ctxt = z_contexts contexts" 

definition "lhs_R' = all_symbol_pos_ctxt lhs_R" 
definition "rhs_R' = all_symbol_pos_ctxt rhs_R" 
definition R' where "R' = {( lhs_R', rhs_R' )}" 

lemma funas_encode_num: "funas_term (encode_num x n) \<subseteq> F" 
proof -
  define m where "m = nat n" 
  show ?thesis
    unfolding encode_num_def m_def[symmetric]
    by (induct m, auto simp: F_def)
qed

lemma funas_encode_monom: assumes "keys m \<subseteq> V"
  shows "funas_term (encode_monom x m c) \<subseteq> F"  
proof -
  define xes where "xes = var_list m" 
  show ?thesis using var_list_keys[of _ _ m] unfolding encode_monom_def xes_def[symmetric]
  proof (induct xes)
    case Nil
    thus ?case using funas_encode_num by auto
  next
    case (Cons ye xes)
    obtain y e where ye: "ye = (y,e)" by force
    have sub: "funas_term ((v_t y ^^ e) t) \<subseteq> insert (v_sym y, 1) (funas_term t)" for t :: "(symbol,var)term" 
      by (induct e arbitrary: t, auto)
    from Cons(2)[unfolded ye] assms have "y \<in> V" by auto
    hence inF: "(v_sym y, 1) \<in> F" unfolding F_def by auto
    from Cons sub inF show ?case unfolding ye by fastforce
  qed
qed

lemma funas_encode_poly: assumes "vars r \<subseteq> V" shows "funas_term (encode_poly x r) \<subseteq> F" 
proof - 
  define mcs where "mcs = monom_list r" 
  show ?thesis using monom_list_keys[of _ _ r] unfolding encode_poly_def mcs_def[symmetric]
  proof (induct mcs)
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    have a: "(a_sym, 2) \<in> F" unfolding F_def by auto
    from Cons(2)[unfolded mc] assms have "keys m \<subseteq> V" by auto
    from funas_encode_monom[OF this, of x c] Cons(1)[OF Cons(2)] a
    show ?case unfolding mc by (force simp: numeral_eq_Suc)
  qed (auto simp: F_def)
qed

lemma funas_encode_poly_p: "funas_term (encode_poly x p) \<subseteq> F" 
  by (rule funas_encode_poly, auto simp: V_def)

lemma funas_encode_poly_q: "funas_term (encode_poly x q) \<subseteq> F" 
  by (rule funas_encode_poly, auto simp: V_def)

lemma lhs_R_F: "funas_term lhs_R \<subseteq> F_R" 
proof - 
  from funas_encode_poly_p
  show "funas_term lhs_R \<subseteq> F_R" unfolding lhs_R_def by (auto simp: F_R_def F_def)
qed

lemma rhs_R_F: "funas_term rhs_R \<subseteq> F_R" 
proof -
  from funas_encode_poly_q
  show "funas_term rhs_R \<subseteq> F_R" unfolding rhs_R_def by (auto simp: F_R_def F_def)
qed


lemma finite_V: "finite V" unfolding V_def using vars_finite by auto

lemma V_list: "set V_list = V" unfolding V_list_def using finite_V by auto

lemma contexts: assumes "(f,n,i) \<in> set contexts"  
  shows "(f,n) \<in> F_R" "i < n" 
  using assms unfolding contexts_def F_R_def F_def by (auto simp: V_list)

lemma z_contexts_append: "z_contexts (cs @ ds) t = z_contexts cs (z_contexts ds t)" 
  unfolding z_contexts_def by (induct cs, auto)

lemma z_context: assumes "(f,n) \<in> F_R" "i < n" and "funas_term t \<subseteq> F_R" 
  shows "funas_term (z_context (f,n,i) t) \<subseteq> F_R" 
proof -
  have z: "(z_sym,0) \<in> F_R" unfolding F_R_def F_def by auto
  thus ?thesis unfolding z_context_def split using assms by auto
qed

lemma funas_all_symbol_pos_ctxt: assumes "funas_term t \<subseteq> F_R" 
  shows "funas_term (all_symbol_pos_ctxt t) \<subseteq> F_R" 
proof -
  define cs where "cs = contexts" 
  have sub: "set cs \<subseteq> set contexts" unfolding cs_def by auto
  have id: "all_symbol_pos_ctxt t = foldr z_context cs t" unfolding cs_def all_symbol_pos_ctxt_def  z_contexts_def
    by (auto simp: id_def)
  show ?thesis unfolding id using sub assms(1)
  proof (induct cs arbitrary: t)
    case (Cons c cs t)
    obtain f n i where c: "c = (f,n,i)" by (cases c, auto)
    from c Cons have "(f,n,i) \<in> set contexts" by auto
    from z_context[OF contexts[OF this], folded c] Cons
    show ?case by auto
  qed auto
qed 

lemma lhs_R'_F: "funas_term lhs_R' \<subseteq> F_R" 
  unfolding lhs_R'_def by (rule funas_all_symbol_pos_ctxt[OF lhs_R_F])

lemma rhs_R'_F: "funas_term rhs_R' \<subseteq> F_R" 
  unfolding rhs_R'_def by (rule funas_all_symbol_pos_ctxt[OF rhs_R_F])
end

lemma insertion_positive_poly: assumes "\<And> x. \<alpha> x \<ge> (0 :: 'a :: linordered_idom)" 
  and "positive_poly p"  
shows "insertion \<alpha> p \<ge> 0" 
  by (rule insertion_nonneg, insert assms[unfolded positive_poly_def], auto)

locale solvable_poly_problem = poly_input p q for p q + 
  assumes sol: "positive_poly_problem p q" 
begin

definition \<alpha> where "\<alpha> = (SOME \<alpha>. positive_interpr \<alpha> \<and> insertion \<alpha> q \<le> insertion \<alpha> p)" 

lemma \<alpha>: "positive_interpr \<alpha>" "insertion \<alpha> q \<le> insertion \<alpha> p" 
  using someI_ex[OF sol[unfolded positive_poly_problem_def[OF pq]], folded \<alpha>_def]
  by auto

lemma \<alpha>1: "\<alpha> x > 0" using \<alpha> unfolding positive_interpr_def by auto

context
  fixes I :: "symbol \<Rightarrow> int mpoly"  
  assumes inter: "I a_sym = PVar 0 + PVar 1"
    "I z_sym = 0" 
    "I o_sym = 1" 
    "I (v_sym i) = Const (\<alpha> i) * PVar 0" 
begin


lemma inter_encode_num: assumes "c \<ge> 0" 
  shows "poly_inter.eval I (encode_num x c) = Const c * PVar x" 
proof -
  from assms obtain n where cn: "c = int n" by (metis nonneg_eq_int)
  hence natc: "nat c = n" by auto
  show ?thesis unfolding encode_num_def natc unfolding cn
    by (induct n, auto simp: inter poly_inter.eval.simps Const_0 Const_1 algebra_simps Const_add)
qed

lemma inter_v_pow_e: "poly_inter.eval I ((v_t x ^^ e) t) = Const ((\<alpha> x)^e) * poly_inter.eval I t" 
  by (induct e, auto simp: Const_1 Const_mult inter poly_inter.eval.simps)

lemma inter_encode_monom: assumes c: "c \<ge> 0" 
  shows "poly_inter.eval I (encode_monom y m c) = Const (insertion \<alpha> (monom m c)) * PVar y" 
proof -
  define xes where "xes = var_list m" 
  from var_list[of m c] 
  have monom: "monom m c = Const c * (\<Prod>(x, e)\<leftarrow> xes . PVar x ^ e) " unfolding xes_def .
  show ?thesis unfolding encode_monom_def monom xes_def[symmetric]
  proof (induct xes)
    case Nil
    show ?case by (simp add: inter_encode_num[OF c] insertion_Const)
  next
    case (Cons xe xes)
    obtain x e where xe: "xe = (x,e)" by force
    show ?case by (simp add: xe inter_v_pow_e Cons Const_power 
          insertion_Const insertion_mult insertion_power insertion_Var Const_mult)
  qed
qed


lemma inter_foldr_v_t: 
  "poly_inter.eval I (foldr v_t xs t) = Const (prod_list (map \<alpha> xs)) * poly_inter.eval I t" 
  by (induct xs arbitrary: t, auto simp: Const_1 inter poly_inter.eval.simps Const_mult)

lemma inter_encode_poly_generic: assumes "positive_poly r" 
  shows "poly_inter.eval I (encode_poly x r) = Const (insertion \<alpha> r) * PVar x" 
proof -
  define mcs where "mcs = monom_list r" 
  from monom_list[of r] have r: "r = (\<Sum>(m, c)\<leftarrow> mcs. monom m c)" unfolding mcs_def by auto
  have mcs: "(m,c) \<in> set mcs \<Longrightarrow> c \<ge> 0" for m c 
    using monom_list_coeff assms unfolding mcs_def positive_poly_def by auto
  note [simp] = inter poly_inter.eval.simps
  show ?thesis unfolding encode_poly_def mcs_def[symmetric] unfolding r insertion_sum_list map_map o_def
    using mcs
  proof (induct mcs)
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    from Cons(2) mc have c: "c \<ge> 0" by auto
    note monom = inter_encode_monom[OF this, of x m]
    show ?case
      by (simp add: mc monom algebra_simps, subst Cons(1), insert Cons(2), auto simp: Const_add algebra_simps)
  qed simp
qed

lemma valid_monotone_inter_F: assumes "positive_interpr \<alpha>" 
  and inF: "fn \<in> F" 
shows "poly_inter.valid_monotone_poly I (>) fn" 
proof -
  obtain f n where fn: "fn = (f,n)" by force
  with inF have f: "(f,n) \<in> F" by auto
  show ?thesis unfolding poly_inter.valid_monotone_poly_def fn
  proof (intro allI impI, clarify, intro conjI)
    let ?valid = "valid_poly" 
    let ?mono = "poly_inter.monotone_poly (>)" 
    have [simp]: "vars ((PVar 0 :: int mpoly) + PVar (Suc 0) + PVar 2 + PVar 3) = {0,1,2,3}" 
      unfolding vars_def apply (transfer, simp add: Var\<^sub>0_def image_comp) by code_simp
    have [simp]: "vars ((PVar 0 :: int mpoly) + PVar (Suc 0)) = {0,1}" 
      unfolding vars_def apply (transfer, simp add: Var\<^sub>0_def image_comp) by code_simp
    note [simp] = inter poly_inter.eval.simps
    {
      fix i
      assume i: "i \<in> V" and "f = v_sym i" and n: "n = 1" 
      hence I: "I f = Const (\<alpha> i) * PVar 0" by simp
      from assms[unfolded positive_interpr_def] have alpha: "\<alpha> i > 0" by auto
      have valid: "?valid (I f)" 
        unfolding I valid_poly_def using alpha
        by (auto simp: insertion_mult insertion_Const insertion_Var assignment_def intro!: mult_nonneg_nonneg)
      have mono: "?mono {..<n} (I f)" 
        unfolding I unfolding n monotone_poly_wrt_def using alpha
        by (auto simp: insertion_Const insertion_mult insertion_Var)
      have "vars (I f) \<subseteq> {..<n}" unfolding I unfolding n
        by (rule order.trans[OF vars_mult], auto)
      moreover have "0 \<in> vars (I f)" 
        unfolding I unfolding n 
      proof (rule ccontr)
        let ?p = "Const (\<alpha> i) * PVar 0" 
        assume not: "0 \<notin> vars ?p" 
        define \<beta> :: "var \<Rightarrow> int" where "\<beta> x = 0" for x
        have "insertion \<beta> ?p = insertion (\<beta>(0 := 1)) ?p" 
          by (rule insertion_irrelevant_vars, insert not, auto)
        thus False using alpha by (simp add: \<beta>_def insertion_mult insertion_Const insertion_Var)
      qed
      ultimately have "vars (I f) = {..< n}" unfolding n by auto
      note this valid mono
    } note v_sym = this
    from f v_sym show "vars (I f) = {..< n}" unfolding F_def by auto
    from f v_sym show "?valid (I f)" unfolding F_def
      by (auto simp: valid_poly_def insertion_add assignment_def insertion_Var)
    have x4: "x < 4 \<Longrightarrow> x = 0 \<or> x = Suc 0 \<or> x = 2 \<or> x = 3" for x by linarith
    have x2: "x < 2 \<Longrightarrow> x = 0 \<or> x = Suc 0" for x by linarith
    from f v_sym show "?mono {..<n} (I f)" unfolding F_R_def F_def
      by (auto simp: monotone_poly_wrt_def insertion_add insertion_Var assignment_def
          dest: x4 x2)
  qed
qed

end

fun I_R :: "symbol \<Rightarrow> int mpoly" where 
  "I_R f_sym = PVar 0 + PVar 1 + PVar 2 + PVar 3" 
| "I_R a_sym = PVar 0 + PVar 1"
| "I_R z_sym = 0" 
| "I_R o_sym = 1" 
| "I_R (v_sym i) = Const (\<alpha> i) * PVar 0" 

interpretation inter_R: poly_inter F_R I_R "(>)" .

lemma inter_R_encode_poly: assumes "positive_poly r" 
  shows "inter_R.eval (encode_poly x r) = Const (insertion \<alpha> r) * PVar x" 
  by (rule inter_encode_poly_generic[OF _ _ _ _ assms], auto)

lemma valid_monotone_inter_R: "inter_R.valid_monotone_poly_inter" unfolding inter_R.valid_monotone_poly_inter_def 
proof (intro ballI)
  fix fn
  assume f: "fn \<in> F_R" 
  show "inter_R.valid_monotone_poly fn"
  proof (cases "fn \<in> F")
    case True
    show "inter_R.valid_monotone_poly fn" 
      by (rule valid_monotone_inter_F[OF _ _ _ _ \<alpha>(1) True], auto)
  next
    case False
    with f have f: "fn \<in> F_R - F" by auto
    have [simp]: "vars ((PVar 0 :: int mpoly) + PVar (Suc 0) + PVar 2 + PVar 3) = {0,1,2,3}" 
      unfolding vars_def apply (transfer, simp add: Var\<^sub>0_def image_comp) by code_simp
    show ?thesis unfolding inter_R.valid_monotone_poly_def using f
    proof (intro ballI impI allI, clarify, intro conjI) 
      fix f n
      assume f: "(f,n) \<in> F_R" "(f,n) \<notin> F" 
      from f show "vars (I_R f) = {..< n}" unfolding F_R_def by auto
      from f show "valid_poly (I_R f)" unfolding F_R_def
        by (auto simp: valid_poly_def insertion_add assignment_def insertion_Var)
      have x4: "x < 4 \<Longrightarrow> x = 0 \<or> x = Suc 0 \<or> x = 2 \<or> x = 3" for x by linarith
      from f show "inter_R.monotone_poly {..<n} (I_R f)" unfolding F_R_def
        by (auto simp: monotone_poly_wrt_def insertion_add insertion_Var assignment_def
            dest: x4)
    qed
  qed
qed

sublocale inter_R: linear_int_poly_inter F_R I_R
proof 
  show inter_R.valid_monotone_poly_inter by (rule valid_monotone_inter_R)
  fix f n
  assume "(f,n) \<in> F_R" 
  thus "total_degree (I_R f) \<le> 1" by (cases f, auto simp: F_R_def F_def intro!: total_degree_add total_degree_Const_mult)
qed

lemma orient_R_main: assumes "assignment \<beta>" 
  shows "insertion \<beta> (inter_R.eval lhs_R) > insertion \<beta> (inter_R.eval rhs_R)" 
proof -
  have lhs_R: "inter_R.eval lhs_R = PVar y1 + PVar y2 + Const (insertion \<alpha> p + 1) * PVar y3 + 1" 
    unfolding lhs_R_def by (simp add: inter_R_encode_poly[OF pq(1)] algebra_simps Const_add Const_1)
  have rhs_R: "inter_R.eval rhs_R = PVar y1 + PVar y2 + Const (insertion \<alpha> q + 1) * PVar y3" 
    unfolding rhs_R_def by (simp add: inter_R_encode_poly[OF pq(2)] algebra_simps Const_add Const_1)
  show ?thesis
    unfolding lhs_R rhs_R
    apply (simp add: insertion_add insertion_mult insertion_Var insertion_Const)
    apply (intro mult_right_mono)
    subgoal using \<alpha>(2) by simp
    subgoal using assms unfolding assignment_def by auto
    done
qed


text \<open>The easy direction of Theorem 3.4\<close>
lemma orient_R: "inter_R.termination_by_poly_interpretation R" 
  unfolding inter_R.termination_by_poly_interpretation_def inter_R.termination_by_interpretation_def R_def inter_R.orient_rule
proof (clarify, intro conjI)
  show "inter_R.gt_poly (inter_R.eval lhs_R) (inter_R.eval rhs_R)" 
    unfolding inter_R.gt_poly_def
    by (intro allI impI orient_R_main)
qed (insert lhs_R_F rhs_R_F, auto)

lemma solution_imp_linear_termination_R: "termination_by_linear_int_poly_interpretation F_R R" 
  unfolding termination_by_linear_int_poly_interpretation_def
  by (intro exI, rule conjI[OF _ orient_R], unfold_locales)
end

context poly_input
begin

lemma inter_z_context: 
  assumes i: "i < n" and I: "I f = Const c0 + (sum_list (map (\<lambda> j. Const (c j) * PVar j) [0..<n]))"  
    and Ize: "I z_sym = Const d0" 
  shows "\<exists> d. \<forall> t. poly_inter.eval I (z_context (f,n,i) t) = Const d + Const (c i) * poly_inter.eval I t"
proof -
  define d where "d = c0 + (\<Sum>x\<leftarrow>[0..<i]. c x * d0) + (\<Sum>x\<leftarrow>[Suc i..<n]. c x * d0)" 
  show ?thesis
  proof (intro exI[of _ d] allI)
    fix t :: "(symbol, nat) term" 
    define list where "list = replicate i (Fun z_sym []) @ [t] @ replicate (n - i - 1) (Fun z_sym [])" 
    have len: "length list = n" 
      using i unfolding list_def by auto
    have z[simp]: "poly_inter.eval I (Fun z_sym []) = Const d0" unfolding poly_inter.eval.simps using Ize by auto
    let ?xs1 = "[0 ..< i]" 
    let ?xs2 = "[Suc i ..< n]" 
    define ev where "ev = (\<lambda> x. Const (c x) * poly_inter.eval I (list ! x))" 
    have "poly_inter.eval I (z_context (f,n,i) t) = Const c0 +
    (\<Sum>x\<leftarrow>[0..<n]. ev x)" 
      unfolding z_context_def split list_def[symmetric]
      unfolding poly_inter.eval.simps len I ev_def
      unfolding substitute_add substitute_Const substitute_sum_list o_def substitute_mult substitute_Var
      apply (rule arg_cong[of _ _ "\<lambda> xs. (+) _ (sum_list xs)"])
      by (rule map_cong[OF refl], auto)
    also have "[0 ..< n] = ?xs1 @ i # ?xs2"  using i
      by (metis less_imp_add_positive upt_add_eq_append upt_rec zero_le)
    also have "sum_list (map ev \<dots>) = sum_list (map ev ?xs1) + sum_list (map ev ?xs2) + ev i" by simp
    also have "map ev ?xs1 = map (\<lambda> x. (Const (c x * d0))) ?xs1" 
      unfolding o_def by (intro map_cong, auto simp: ev_def list_def nth_append Const_mult)
    also have "sum_list \<dots> = Const (sum_list (map (\<lambda> x. c x * d0) ?xs1))" unfolding Const_sum_list o_def ..
    also have "map ev ?xs2 = map (\<lambda> x. (Const (c x * d0))) ?xs2" 
      unfolding o_def by (intro map_cong, auto simp: ev_def list_def nth_append Const_mult)
    also have "sum_list \<dots> = Const (sum_list (map (\<lambda> x. c x * d0) ?xs2))" unfolding Const_sum_list o_def ..
    also have "ev i = Const (c i) * poly_inter.eval I t" unfolding ev_def list_def by (auto simp: nth_append)
    finally show "poly_inter.eval I (z_context (f, n, i) t) = Const d + Const (c i) * poly_inter.eval I t" 
      unfolding add.assoc[symmetric] Const_add[symmetric] d_def by blast
  qed
qed

lemma inter_z_contexts: 
  assumes cs: "\<And> f n i. (f,n,i) \<in> set cs \<Longrightarrow> i < n \<and> I f = Const (c0 f) + (sum_list (map (\<lambda> j. Const (c f j) * PVar j) [0..<n]))"  
    and Ize: "I z_sym = Const d0" 
  shows "\<exists> d. \<forall> t. poly_inter.eval I (z_contexts cs t) = Const d + Const (prod_list (map (\<lambda> (f,n,i). c f i) cs)) * poly_inter.eval I t"
proof -
  define c' where "c' = (\<lambda> (f,n :: nat,i). c f i)" 
  have c': "c f i = c' (f,n,i)" for f i n unfolding c'_def split ..
  {
    fix fni 
    assume mem: "fni \<in> set cs" 
    obtain f n i where fni: "fni = (f,n,i)" by (cases fni, auto)
    from cs[OF mem[unfolded fni]]
    have i: "i < n" and "I f = Const (c0 f) + (\<Sum>j\<leftarrow>[0..<n]. Const (c f j) * PVar j)" by auto
    note inter_z_context[OF this Ize, unfolded c'[of _ _ n], folded fni]
  } note z_pre_ctxt = this
  define p where "p fni d t = (fni \<in> set cs \<longrightarrow> poly_inter.eval I (z_context fni t) = Const d + Const (c' fni) * poly_inter.eval I t)" 
    for fni d t
  from z_pre_ctxt 
  have "\<forall> fni. \<exists> d. \<forall> t. p fni d t" by (auto simp: p_def)
  from choice[OF this] obtain d' where "\<And> fni t. p fni (d' fni) t" by auto
  hence z_ctxt: "\<And> fni t. fni \<in> set cs \<Longrightarrow> poly_inter.eval I (z_context fni t) = Const (d' fni) + Const (c' fni) * poly_inter.eval I t"  
    unfolding p_def by auto
  define d where "d = foldr (\<lambda> fni c. d' fni + c' fni * c) cs 0" 
  show ?thesis
  proof (intro exI[of _ d] allI)
    fix t :: "(symbol,var)term" 
    show "poly_inter.eval I (z_contexts cs t) = Const d + Const (\<Prod>(f, n, i)\<leftarrow>cs. c f i) * poly_inter.eval I t" 
      unfolding d_def z_contexts_def using z_ctxt
    proof (induct cs)
      case Nil
      show ?case by (simp add: Const_0 Const_1)
    next
      case (Cons fni cs)
      from Cons(2)[of fni]
      have z_ctxt: "poly_inter.eval I (z_context fni t) = Const (d' fni) + Const (c' fni) * poly_inter.eval I t" for t by auto
      from Cons(1)[OF Cons(2)]
      have IH: "poly_inter.eval I (foldr z_context cs t) =
        Const (foldr (\<lambda>fni c. d' fni + c' fni * c) cs 0) + Const (\<Prod>(f, n, y)\<leftarrow>cs. c f y) * poly_inter.eval I t" 
        by auto
      have [simp]: "(case fni of (f, n, xa) \<Rightarrow> c f xa) = c' fni" unfolding c'_def ..
      show ?case 
        by (simp add: z_ctxt IH algebra_simps Const_mult)
          (simp add: Const_add[symmetric] Const_mult[symmetric])
    qed
  qed
qed

lemma inter_all_symbol_pos_ctxt_generic:
  assumes f: "I f_sym = Const fc + Const f0 * PVar 0 + Const f1 * PVar 1 + Const f2 * PVar 2 + Const f3 * PVar 3"
    and a: "I a_sym = Const ac + Const a0 * PVar 0 + Const a1 * PVar 1" 
    and v: "\<And> i. i \<in> V \<Longrightarrow> I (v_sym i) = Const (vc i) + Const (v0 i) * PVar 0" 
    and "I z_sym = Const zc" 
  shows "\<exists> d. \<forall> t. poly_inter.eval I (all_symbol_pos_ctxt t) = Const d + Const (prod_list ([a0, a1, f0, f1, f2, f3] @ map v0 V_list)) 
      * poly_inter.eval I t"
proof -
  define c where "c = (\<lambda> f i. case f of
    a_sym \<Rightarrow> if i = 0 then a0 else a1
  | v_sym x \<Rightarrow> v0 x
  | f_sym \<Rightarrow> if i = 0 then f0 else if i = Suc 0 then f1 else if i = 2 then f2 else f3)" 
  define c0 where "c0 = (\<lambda> f. case f of a_sym \<Rightarrow> ac | f_sym \<Rightarrow> fc | v_sym x \<Rightarrow> vc x)" 
  have id: "[a0, a1, f0, f1, f2, f3] @ map v0 V_list = map (\<lambda> (f,n,i). c f i) contexts"   
    unfolding contexts_def map_append
    by (auto simp: c_def)
  have lists: "[0..<2] = [0,Suc 0]" "[0 ..< 4] = [0,Suc 0, 2,3]" by code_simp+
  show ?thesis unfolding id all_symbol_pos_ctxt_def
  proof (rule inter_z_contexts[of _ _ c0 c zc])
    show "I z_sym = Const zc" by fact
    fix f n i
    assume "(f, n, i) \<in> set contexts" 
    thus "i < n \<and> I f = Const (c0 f) + (\<Sum>j\<leftarrow>[0..<n]. Const (c f j) * PVar j)" 
      unfolding contexts_def c0_def c_def by (auto simp: f a v V_list lists)
  qed
qed
end

context solvable_poly_problem
begin

lemma inter_all_symbol_pos_ctxt:
  "\<exists> d e. e \<ge> 1 \<and> (\<forall> t. inter_R.eval (all_symbol_pos_ctxt t) = Const d + Const e * inter_R.eval t)"
proof -                                    
  from inter_all_symbol_pos_ctxt_generic[of I_R 0 1 1 1 1 0 1 1 0 \<alpha> 0, unfolded Const_0 Const_1]
  obtain d where inter: "\<And> t. inter_R.eval (all_symbol_pos_ctxt t) = Const d + Const (prod_list (map \<alpha> V_list)) * inter_R.eval t" 
    by auto
  show ?thesis
  proof (rule exI[of _ d], rule exI[of _ "prod_list (map \<alpha> V_list)"], intro conjI allI inter)
    define vs where "vs = V_list" 
    show "1 \<le> prod_list (map \<alpha> V_list)" unfolding vs_def[symmetric]
    proof (induct vs)
      case (Cons v vs)
      from \<alpha>(1)[unfolded positive_interpr_def, rule_format, of v] have "1 \<le> \<alpha> v"  by auto
      with Cons show ?case by simp (smt (verit, ccfv_threshold) mult_pos_pos)
    qed auto
  qed
qed 


text \<open>The easy direction of Theorem 3.4 for R'\<close>
lemma orient_R': "inter_R.termination_by_poly_interpretation R'" 
  unfolding inter_R.termination_by_interpretation_def inter_R.termination_by_poly_interpretation_def R'_def inter_R.orient_rule
proof (clarify, intro conjI)
  from inter_all_symbol_pos_ctxt obtain d e where
    e: "e \<ge> 1" and
    ctxt: "\<And> t. inter_R.eval (all_symbol_pos_ctxt t) = Const d + Const e * inter_R.eval t" 
    by auto
  let ?ctxt = "\<lambda> f. Const d + Const e * f"   
  show "inter_R.gt_poly (inter_R.eval lhs_R') (inter_R.eval rhs_R')" 
    unfolding inter_R.gt_poly_def
  proof (intro allI impI)
    fix \<beta> :: "var \<Rightarrow> int" 
    assume ass: "assignment \<beta>" 
    have "insertion \<beta> (inter_R.eval lhs_R') > insertion \<beta> (inter_R.eval rhs_R')
     \<longleftrightarrow> insertion \<beta> (inter_R.eval lhs_R) > insertion \<beta> (inter_R.eval rhs_R)"
      unfolding lhs_R'_def rhs_R'_def ctxt using e
      by (simp add: insertion_add insertion_mult insertion_Var insertion_Const)
    also have \<dots> using orient_R_main[OF ass] .
    finally show "insertion \<beta> (inter_R.eval rhs_R') < insertion \<beta> (inter_R.eval lhs_R')" .
  qed
qed (insert lhs_R'_F rhs_R'_F, auto)

lemma solution_imp_linear_termination_R': "termination_by_linear_int_poly_interpretation F_R R'" 
  unfolding termination_by_linear_int_poly_interpretation_def
  by (intro exI, rule conjI[OF _ orient_R'], unfold_locales)
end

text \<open>Now for the other direction of Theorem 3.4\<close>

lemma monotone_linear_poly_to_coeffs: fixes p :: "int mpoly" 
  assumes linear: "total_degree p \<le> 1" 
    and poly: "valid_poly p" 
    and mono: "poly_inter.monotone_poly (>) {..<n} p" 
    and vars: "vars p = {..<n}" 
shows "\<exists> c a. p = Const c + (\<Sum>i\<leftarrow>[0..<n]. Const (a i) * PVar i)
     \<and> c \<ge> 0 \<and> (\<forall> i < n. a i > 0)" 
proof -
  have sum_zero: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list (xs :: int list) = 0" for xs by (induct xs, auto)
  interpret poly_inter undefined undefined "(>) :: int \<Rightarrow> _" .
  from coefficients_of_linear_poly[OF linear] obtain c a vs 
    where p: "p = Const c + (\<Sum>i\<leftarrow>vs. Const (a i) * PVar i)"
     and vsd: "distinct vs" "set vs = vars p" "sorted_list_of_set (vars p) = vs"
     and nz: "\<And> v. v \<in> set vs \<Longrightarrow> a v \<noteq> 0"
     and c: "c = coeff p 0" 
     and a: "\<And> i. a i = coeff p (monomial 1 i)" by blast
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
    from nz[OF this] have a0: "a i \<noteq> 0" by auto    
    from split_list[OF i] obtain bef aft where vsi: "vs = bef @ [i] @ aft" by auto
    with vsd(1) have i: "i \<notin> set (bef @ aft)" by auto
    define \<alpha> where "\<alpha> = (\<lambda> x. if x = i then c + 1 else 0)" 
    have "assignment \<alpha>" unfolding assignment_def \<alpha>_def using c by auto
    from poly[unfolded valid_poly_def, rule_format, OF this, unfolded p]
    have "0 \<le> c + (\<Sum>x\<leftarrow>bef @ aft. a x * \<alpha> x) + (a i * \<alpha> i)" 
      unfolding insertion_add vsi map_append sum_list_append insertion_Const insertion_sum_list
        map_map o_def insertion_mult insertion_Var
      by (simp add: algebra_simps)
    also have "(\<Sum>x\<leftarrow>bef @ aft. a x * \<alpha> x) = 0" by (rule sum_zero, insert i, auto simp: \<alpha>_def)
    also have "\<alpha> i = (c + 1)" unfolding \<alpha>_def by auto
    finally have le: "0 \<le> c * (a i + 1) + a i" by (simp add: algebra_simps)
    with c have "a i \<ge> 0"
      by (smt (verit, best) mult_le_0_iff)
    with a0 show "a i > 0" by simp
  qed
qed

locale poly_input_to_solution_common = poly_input p q +
  poly_inter F' I "(>) :: int \<Rightarrow> int \<Rightarrow> bool" for p q I and F' :: "(poly_input.symbol \<times> nat) set" and argsL argsR +
  assumes orient: 
    "orient_rule (Fun f_sym ([Var y1, Var y2, a_t (encode_poly y3 p) (Var y3)] @ argsL),
     Fun f_sym ([a_t (Var y1) z_t, a_t z_t (Var y2), a_t (encode_poly y3 q) (Var y3)] @ argsR))" 
  and len_args:"length argsL = length argsR" 
  and y123: "{y1,y2,y3} \<inter> (\<Union> (vars_term ` set (argsL @ argsR))) = {}" 
  and FF': "insert (f_sym, 3 + length argsR) F \<subseteq> F'"
  and linear_mono_interpretation: "(g,n) \<in> insert (f_sym, 3 + length argsR) F \<Longrightarrow> 
      \<exists> c a. I g = Const c + (\<Sum>i\<leftarrow>[0..<n]. Const (a i) * PVar i)
        \<and> c \<ge> 0 \<and> (\<forall> i < n. a i > 0)"
begin

abbreviation ff where "ff \<equiv> (f_sym, 3 + length argsR)" 
abbreviation args where "args \<equiv> [3..<length argsR + 3]" 

lemma extract_a_poly: "\<exists> a0 a1 a2. I a_sym = Const a0 + Const a1 * PVar 0 + Const a2 * PVar 1 
  \<and> a0 \<ge> 0 \<and> a1 > 0 \<and> a2 > 0"
proof -
  have [simp]: "[0 ..<2] = [0,1]" by code_simp
  have [simp]: "(\<forall>i<2. P i) = (P 0 \<and> P (1 :: nat))" for P by (auto simp add: numeral_eq_Suc less_Suc_eq) 
  have "(a_sym,2) \<in> insert ff F" unfolding F_def by auto
  from linear_mono_interpretation[OF this]
  show ?thesis by force 
qed

lemma extract_f_poly: "\<exists> f0 f1 f2 f3 f4. I f_sym = Const f0 + Const f1 * PVar 0 + Const f2 * PVar 1 
     + Const f3 * PVar 2 + (\<Sum>i\<leftarrow> args. Const (f4 i) * PVar i)
  \<and> f0 \<ge> 0 \<and> f1 > 0 \<and> f2 > 0 \<and> f3 > 0"
proof -
  have id: "[0..<3 + length argsR] = [0,1,2] @ args"
    by (simp add: numeral_3_eq_3 upt_rec)
  have "ff \<in> insert ff F" by auto
  from linear_mono_interpretation[OF this] obtain c a 
    where Iff: "I f_sym = Const c + (\<Sum>i\<leftarrow>[0..<3 + length argsR]. Const (a i) * PVar i)"
    and c: "0 \<le> c" and a: "\<And> i. i < 3 + length argsR \<Longrightarrow> 0 < a i" by blast
  show ?thesis 
    apply (rule exI[of _ c])
    apply (rule exI[of _ "a 0"])
    apply (rule exI[of _ "a 1"])
    apply (rule exI[of _ "a 2"]) 
    apply (rule exI[of _ a])
    using c a[of 0] a[of 1] a [of 2] Iff id by auto
qed

lemma extract_z_poly: "\<exists> ze0. I z_sym = Const ze0 \<and> ze0 \<ge> 0"
proof -
  have "(z_sym,0) \<in> insert ff F" unfolding F_def by auto
  from linear_mono_interpretation[OF this] show ?thesis by auto
qed

lemma solution: "positive_poly_problem p q"
proof -
  from extract_a_poly obtain a0 a1 a2 where
    Ia: "I a_sym = Const a0 + Const a1 * PVar 0 + Const a2 * PVar 1"
    and a: "0 \<le> a0" "0 < a1" "0 < a2" 
    by auto
  from extract_f_poly obtain f0 f1 f2 f3 f4 where
    If: "I f_sym = Const f0 + Const f1 * PVar 0 + Const f2 * PVar 1 + Const f3 * PVar 2 + (\<Sum>i\<leftarrow>args. Const (f4 i) * PVar i)"
    and f: "0 \<le> f0" "0 < f1" "0 < f2" "0 < f3" 
    by auto
  from extract_z_poly obtain ze0 where
    Iz: "I z_sym = Const ze0"
    and z: "0 \<le> ze0" 
    by auto
  {
    fix x
    assume "x \<in> V" 
    hence "(v_sym x, 1) \<in> insert ff F" unfolding F_def by auto
    from linear_mono_interpretation[OF this]
    have "\<exists>c a. I (v_sym x) = Const c + Const a * PVar 0 \<and> 0 < a" by auto
  }
  hence "\<forall> x. \<exists> c a. x \<in> V \<longrightarrow> I (v_sym x) = Const c + Const a * PVar 0 \<and> 0 < a" by auto
  from choice[OF this] obtain v0 where "\<forall> x. \<exists> a. x \<in> V \<longrightarrow> I (v_sym x) = Const (v0 x) + Const a * PVar 0 \<and> 0 < a" by auto
  from choice[OF this] obtain v1 where 
    Iv: "\<And> x. x \<in> V \<Longrightarrow> I (v_sym x) = Const (v0 x) + Const (v1 x) * PVar 0" and
    v: "\<And> x. x \<in> V \<Longrightarrow> 0 < v1 x" by auto

  let ?lhs = "Fun f_sym ([TVar y1, TVar y2, Fun a_sym [encode_poly y3 p, TVar y3]] @ argsL)"
  let ?rhs = "Fun f_sym
       ([Fun a_sym [TVar y1, Fun z_sym []], Fun a_sym [Fun z_sym [], TVar y2],
         Fun a_sym [encode_poly y3 q, TVar y3]] @
        argsR)"

  from orient[unfolded orient_rule]
  have gt: "gt_poly (eval ?lhs) (eval ?rhs)" by auto
  have [simp]: "Suc (Suc (Suc (Suc 0))) = 4" by simp
  have [simp]: "Suc (Suc 0) = 2" by simp
  define restL where "restL = substitute
     (\<lambda>i. if i < length argsR + 3
          then eval ((TVar y1 # TVar y2 # Fun a_sym [encode_poly y3 p, TVar y3] # argsL) ! i) else 0)
     (\<Sum>i\<leftarrow>local.args. PVar i * Const (f4 i))" 
  define b0 where "b0 = f3 * a0 + f0" 
  define b1 where "b1 = f3 * a0 + f0 + f1 * a0 + f1 * a2 * ze0 + f2 * a0 + f2 * a1 * ze0" 
  define b2 where "b2 = f3 * a1" 
  define b3 where "b3 = f3 * a2" 
  have b23: "b2 > 0" "b3 > 0" unfolding b2_def b3_def using a f by auto
  let ?pt = "encode_poly y3 p" 
  let ?qt = "encode_poly y3 q" 
  from vars_encode_poly[of y3] 
  have vars: "vars_term ?pt \<union> vars_term ?qt \<subseteq> {y3}" by auto
  from vars_eval vars
  have vars: "vars (eval ?pt) \<union> vars (eval ?qt) \<subseteq> {y3}" by auto
  have [simp]: "Suc (Suc (Suc (length argsR))) = length argsR + 3"
    by presburger

  have lhs: "eval ?lhs = Const b0 + 
    Const f1 * PVar y1 + 
    Const f2 * PVar y2 +
    Const b2 * eval ?pt + Const b3 * PVar y3 + restL" 
    using If Ia len_args by (simp add: algebra_simps Const_add Const_mult b0_def b2_def b3_def restL_def)  
  define \<beta> where "\<beta> z1 z2 z3 = (((\<lambda> x. 0 :: int) (y1 := z1)) (y2 := z2)) (y3 := z3)"  for z1 z2 z3
  have args: "args = map (\<lambda> z. z + 3) [0..<length argsR]"
    using map_add_upt by presburger
  define rl where "rl = insertion (\<beta> 0 0 0) restL" 
  {
    have insRestL: "insertion (\<beta> z1 z2 z3) restL = (\<Sum>x\<leftarrow>[0..<length
                argsR]. (insertion (\<beta> z1 z2 z3) (eval (argsL ! x)) * (f4 (x + 3))))" for z1 z2 z3
      unfolding restL_def insertion_substitute insertion_sum_list map_map o_def if_distrib args insertion_mult insertion_Var insertion_Const
      apply (rule arg_cong[of _ _ sum_list])
      apply (rule map_cong[OF refl]) by auto
    have insRestL: "insertion (\<beta> z1 z2 z3) restL = rl" for z1 z2 z3
      unfolding insRestL rl_def
      apply (rule arg_cong[of _ _ sum_list])
      apply (rule map_cong[OF refl])
      apply (rule arg_cong[of _ _ "\<lambda> x. x * _"])
      apply (rule insertion_irrelevant_vars)
      subgoal for v i unfolding len_args[symmetric] using y123 vars_eval[of "argsL ! v"]
        by (auto simp: \<beta>_def)
      done
  } note ins_restL = this 

  define restR where "restR = substitute
     (\<lambda>i. if i < length argsR + 3
          then eval
                ((Fun a_sym [TVar y1, Fun z_sym []] #
                  Fun a_sym [Fun z_sym [], TVar y2] # Fun a_sym [encode_poly y3 q, TVar y3] # argsR) !
                 i)
          else 0)
     (\<Sum>i\<leftarrow>args. PVar i * Const (f4 i))" 
  have rhs: "eval ?rhs = Const b1 +
    Const (f1 * a1) * PVar y1 + 
    Const (f2 * a2) * PVar y2 +
    Const b2 * eval ?qt + Const b3 * PVar y3 + restR" 
    unfolding restR_def using If Ia Iz by (simp add: algebra_simps Const_add Const_mult b1_def b2_def b3_def)
  define rr where "rr = insertion (\<beta> 0 0 0) restR" 
  {
    have insRestR: "insertion (\<beta> z1 z2 z3) restR = (\<Sum>x\<leftarrow>[0..<length
                argsR]. (insertion (\<beta> z1 z2 z3) (eval (argsR ! x)) * (f4 (x + 3))))" for z1 z2 z3
      unfolding restR_def insertion_substitute insertion_sum_list map_map o_def if_distrib args insertion_mult insertion_Var insertion_Const
      apply (rule arg_cong[of _ _ sum_list])
      apply (rule map_cong[OF refl]) by auto
    have insRestR: "insertion (\<beta> z1 z2 z3) restR = rr" for z1 z2 z3
      unfolding insRestR rr_def
      apply (rule arg_cong[of _ _ sum_list])
      apply (rule map_cong[OF refl])
      apply (rule arg_cong[of _ _ "\<lambda> x. x * _"])
      apply (rule insertion_irrelevant_vars)
      subgoal for v i using y123 vars_eval[of "argsR ! v"]
        by (auto simp: \<beta>_def)
      done
  } note ins_restR = this  

  have [simp]: "\<beta> z1 z2 z3 y1 = z1" for z1 z2 z3 unfolding \<beta>_def using y_vars by auto
  have [simp]: "\<beta> z1 z2 z3 y2 = z2" for z1 z2 z3 unfolding \<beta>_def using y_vars by auto
  have [simp]: "\<beta> z1 z2 z3 y3 = z3" for z1 z2 z3 unfolding \<beta>_def using y_vars by auto
  have \<beta>: "z1 \<ge> 0 \<Longrightarrow> z2 \<ge> 0 \<Longrightarrow> z3 \<ge> 0 \<Longrightarrow> assignment (\<beta> z1 z2 z3)" for z1 z2 z3 
    unfolding assignment_def \<beta>_def by auto
  define l1 where "l1 = insertion (\<beta> 0 0 0) (eval ?lhs)"
  have ins_lhs: "insertion (\<beta> z1 z2 0) (eval ?lhs) = f1 * z1 + f2 * z2 + l1" for z1 z2
    unfolding lhs l1_def 
    apply (simp add: insertion_add insertion_mult insertion_Const insertion_Var ins_restL)
    apply (rule disjI2)
    apply (rule insertion_irrelevant_vars)
    using vars by auto

  define l2 where "l2 = insertion (\<beta> 0 0 0) (eval ?rhs)"
  have ins_rhs: "insertion (\<beta> z1 z2 0) (eval ?rhs) = f1 * a1 * z1 + f2 * a2 * z2 + l2" for z1 z2
    unfolding rhs l2_def 
    apply (simp add: insertion_add insertion_mult insertion_Const insertion_Var ins_restR)
    apply (rule disjI2)
    apply (rule insertion_irrelevant_vars)
    using vars by auto
  define l where "l = l2 - l1"
  have gt_inst: "0 \<le> z1 \<Longrightarrow> 0 \<le> z2 \<Longrightarrow> f1 * a1 * z1 + f2 * a2 * z2 + l < f1 * z1 + f2 * z2" for z1 z2 
    using gt[unfolded gt_poly_def, rule_format, OF \<beta>, of z1 z2 0, unfolded ins_lhs ins_rhs] 
    by (auto simp: l_def)
  {
    define a1' where "a1' = a1 - 1" 
    define z where "z = f1 * a1'" 
    have a1: "a1 = 1 + a1'" unfolding a1'_def by auto
    have a1': "a1' \<ge> 0" using a unfolding a1 by auto
    from gt_inst[of "abs l" 0, unfolded a1] 
    have "z * \<bar>l\<bar> + l < 0" 
      by (simp add: algebra_simps z_def)
    hence "z \<le> 0"
      by (smt (verit) mult_le_cancel_right1)
    with \<open>0 < f1\<close> have "a1' \<le> 0" unfolding z_def
      by (simp add: mult_le_0_iff)
    with a1' a1 have "a1 = 1" by auto
  } note a1 = this
  {
    define a2' where "a2' = a2 - 1" 
    define z where "z = f2 * a2'" 
    have a2: "a2 = 1 + a2'" unfolding a2'_def by auto
    have a2': "a2' \<ge> 0" using a unfolding a2 by auto
    from gt_inst[of 0 "abs l", unfolded a2] 
    have "z * \<bar>l\<bar> + l < 0" 
      by (simp add: algebra_simps z_def)
    hence "z \<le> 0"
      by (smt (verit) mult_le_cancel_right1)
    with \<open>0 < f2\<close> have "a2' \<le> 0" unfolding z_def
      by (simp add: mult_le_0_iff)
    with a2' a2 have "a2 = 1" by auto
  } note a2 = this

  have Ia: "I a_sym = Const a0 + PVar 0 + PVar 1"
    unfolding Ia a1 a2 Const_1 by simp

  {
    fix c :: int
    assume "c \<ge> 0" 
    then obtain n where cn: "c = int n" by (metis nonneg_eq_int)
    hence natc: "nat c = n" by auto
    have "\<exists> d. eval (encode_num y3 c) = Const d + Const c * PVar y3" 
      unfolding encode_num_def natc unfolding cn
      by (induct n, auto simp: Iz Ia Const_0 Const_1 algebra_simps Const_add, auto simp: Const_add[symmetric])
  } note encode_num = this


  {
    fix x e f t
    assume x: "x \<in> V" and eval: "\<exists> c. eval t = Const c + Const f * PVar y3" 
    have "\<exists> d. eval ((v_t x ^^ e) t) = Const d + Const ((v1 x)^ e * f) * PVar y3"  
    proof (induct e)
      case 0
      show ?case using eval by auto
    next
      case (Suc e)
      then obtain d where IH: "eval ((v_t x ^^ e) t) = Const d + Const (v1 x ^ e * f) * PVar y3" by auto
      show ?case by (simp add: IH Iv[OF x] algebra_simps Const_mult)
          (auto simp: Const_mult[symmetric] Const_add[symmetric])
    qed
  } note v_pow_e = this

  {
    fix c :: int and m
    assume c: "c \<ge> 0" 
    define base where "base = encode_num y3 c" 
    define xes where "xes = var_list m" 
    assume keys: "keys m \<subseteq> V" 
    from encode_num[OF c] obtain d where base: "eval base = Const d + Const c * PVar y3" 
      by (auto simp: base_def)
    from var_list[of m c] 
    have monom: "monom m c = Const c * (\<Prod>(x, e)\<leftarrow> xes . PVar x ^ e) " unfolding xes_def .
    have "\<exists> d. eval (encode_monom y3 m c) = Const d + Const (insertion v1 (monom m c)) * PVar y3" 
      using var_list_keys[of _ _ m]
      unfolding encode_monom_def monom xes_def[symmetric] base_def[symmetric]
    proof (induct xes)
      case Nil
      show ?case by (auto simp: base insertion_Const)
    next
      case (Cons xe xes)
      obtain x e where xe: "xe = (x,e)" by force
      with Cons keys have x: "x \<in> V" by auto
      from Cons 
      have "\<exists> d. eval (rec_list base (\<lambda> (i, e) _. v_t i ^^ e) xes) =
        Const d + Const (c * insertion v1 (\<Prod>(x, y)\<leftarrow>xes. PVar x ^ y)) * PVar y3" 
        by (auto simp: insertion_mult insertion_Const)
      from v_pow_e[OF x this, of e] obtain d where
        id: "eval ((v_t x ^^ e) (rec_list base (\<lambda>(i, e) _. v_t i ^^ e) xes)) =
         Const d + Const (v1 x ^ e * (c * insertion v1 (\<Prod>(x, y)\<leftarrow>xes. PVar x ^ y))) * PVar y3" 
        by auto 
      show ?case by (intro exI[of _ d], simp add: xe id, 
            auto simp: Const_power Const_mult insertion_mult insertion_Const insertion_power insertion_Var)
    qed
  } note encode_monom = this

  {
    fix r :: "int mpoly" 
    assume vars: "vars r \<subseteq> V" and pos: "positive_poly r" 
    define mcs where "mcs = monom_list r" 
    from monom_list[of r] have r: "r = (\<Sum>(m, c)\<leftarrow> mcs. monom m c)" unfolding mcs_def by auto
    have mcs_pos: "(m,c) \<in> set mcs \<Longrightarrow> c \<ge> 0" for m c 
      using monom_list_coeff pos unfolding mcs_def positive_poly_def by auto
    from monom_list_keys[of _ _ r, folded mcs_def] vars 
    have mcs_V: "(m,c) \<in> set mcs \<Longrightarrow> keys m \<subseteq> V" for m c by auto
    have "\<exists> d. eval (encode_poly y3 r) = Const d + Const (insertion v1 r) * PVar y3"
      unfolding encode_poly_def mcs_def[symmetric] unfolding r using mcs_pos mcs_V
      unfolding insertion_sum_list map_map o_def
    proof (induct mcs)
      case Nil
      show ?case by (auto simp add: Iz Const_0)
    next
      case (Cons mc mcs)
      obtain m c where mc: "mc = (m,c)" by force
      from Cons(2) mc have c: "c \<ge> 0" by auto
      from Cons(3) mc have "keys m \<subseteq> V" by auto
      from encode_monom[OF c this]
      obtain d1 where m: "eval (encode_monom y3 m c) = Const d1 + Const (insertion v1 (monom m c)) * PVar y3" by auto
      from Cons(1)[OF Cons(2-3)]
      obtain d2 where IH: "eval (rec_list z_t (\<lambda> (m,c)_. a_t (encode_monom y3 m c)) mcs) =
        Const d2 + Const (\<Sum>mc\<leftarrow>mcs. insertion v1 (case mc of (m, c) \<Rightarrow> monom m c)) * PVar y3" 
        by force
      show ?case unfolding mc
        apply (simp add: Ia m IH)
        apply (simp add: Const_add algebra_simps)
        by (auto simp flip: Const_add)
    qed
  } note encode_poly = this

  from encode_poly[OF _ pq(1)] V_def 
  obtain d1 where p: "eval (encode_poly y3 p) = Const d1 + Const (insertion v1 p) * PVar y3" by auto

  from encode_poly[OF _ pq(2)] V_def
  obtain d2 where q: "eval (encode_poly y3 q) = Const d2 + Const (insertion v1 q) * PVar y3" by auto

  define d3 where "d3 = b0 + b2 * d1 + rl" 
  have ins_lhs: "insertion (\<beta> 0 0 z3) (eval ?lhs) = d3 + (b3 + b2 * insertion v1 p) * z3" for z3
    unfolding p d3_def lhs
    by (simp add: insertion_add insertion_mult insertion_Const insertion_Var algebra_simps ins_restL)

  define d4 where "d4 = b1 + b2 * d2 + rr" 
  have ins_rhs: "insertion (\<beta> 0 0 z3) (eval ?rhs) = d4 + (b3 + b2 * insertion v1 q) * z3" for z3
    unfolding q d4_def rhs
    by (simp add: insertion_add insertion_mult insertion_Const insertion_Var algebra_simps ins_restR)

  define d5 where "d5 = d4 - d3" 

  define left where "left = b3 + b2 * insertion v1 p" 
  define right where "right = b3 + b2 * insertion v1 q" 
  define diff where "diff = left - right" 

  have gt_inst: "z3 \<ge> 0 \<Longrightarrow> diff * z3 > d5" for z3
    using gt[unfolded gt_poly_def, rule_format, OF \<beta>, of 0 0 z3, unfolded ins_lhs ins_rhs] 
    by (auto simp: d5_def left_def right_def diff_def algebra_simps)
  from this[of "abs d5"]
  have "diff \<ge> 0"
    by (smt (verit) Groups.mult_ac(2) mult_le_cancel_right1 mult_minus_right)
  from this[unfolded diff_def left_def right_def]
  have "b2 * insertion v1 p \<ge> b2 * insertion v1 q" by auto
  with \<open>b2 > 0\<close> have solution: "insertion v1 p \<ge> insertion v1 q" by simp

  define \<alpha> where "\<alpha> x = (if x \<in> V then v1 x else 1)" for x
  from v have \<alpha>: "positive_interpr \<alpha>" unfolding positive_interpr_def \<alpha>_def by auto
  have "insertion \<alpha> q = insertion v1 q" 
    by (rule insertion_irrelevant_vars, auto simp: \<alpha>_def V_def)
  also have "\<dots> \<le> insertion v1 p" by fact
  also have "\<dots> = insertion \<alpha> p" 
    by (rule insertion_irrelevant_vars, auto simp: \<alpha>_def V_def)
  finally show "positive_poly_problem p q" 
    unfolding positive_poly_problem_def[OF pq] using \<alpha> by auto
qed
end

locale solution_poly_input_R = poly_input p q + poly_inter F_R I "(>) :: int \<Rightarrow> _" for p q I +
  assumes orient: "orient_rule (lhs_R,rhs_R)" 
    and linear_mono_interpretation: "(g,n) \<in> F_R \<Longrightarrow> 
      \<exists> c a. I g = Const c + (\<Sum>i\<leftarrow>[0..<n]. Const (a i) * PVar i)
        \<and> c \<ge> 0 \<and> (\<forall> i < n. a i > 0)" 
begin

lemma solution: "positive_poly_problem p q"
  apply (rule poly_input_to_solution_common.solution[of _ _ I F_R "[o_t]" "[z_t]"])
  apply (unfold_locales)
  subgoal using orient unfolding lhs_R_def rhs_R_def by simp
  subgoal by simp
  subgoal by simp
  subgoal unfolding F_R_def by auto
  subgoal for g n using linear_mono_interpretation[of g n] unfolding F_R_def by auto
  done
end  

locale lin_term_poly_input = poly_input p q for p q +
  assumes lin_term: "termination_by_linear_int_poly_interpretation F_R R" 
begin

definition I where "I = (SOME I. linear_int_poly_inter F_R I \<and> int_poly_inter.termination_by_poly_interpretation F_R I R)" 

lemma I: "linear_int_poly_inter F_R I" "int_poly_inter.termination_by_poly_interpretation F_R I R" 
  using someI_ex[OF lin_term[unfolded termination_by_linear_int_poly_interpretation_def], folded I_def] by auto

sublocale linear_int_poly_inter F_R I by (rule I(1))

lemma orient: "orient_rule (lhs_R,rhs_R)" 
  using I(2)[unfolded termination_by_interpretation_def termination_by_poly_interpretation_def] unfolding R_def by auto

lemma extract_linear_poly: assumes g: "(g,n) \<in> F_R" 
  shows "\<exists> c a. I g = Const c + (\<Sum>i\<leftarrow>[0..<n]. Const (a i) * PVar i)
     \<and> c \<ge> 0 \<and> (\<forall> i < n. a i > 0)" 
proof -
  define p where "p = I g" 
  have sum_zero: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list (xs :: int list) = 0" for xs by (induct xs, auto)
  from valid[unfolded valid_monotone_poly_inter_def, rule_format, OF g]
  have poly: "valid_poly p" 
    and mono: "monotone_poly {..<n} p" 
    and vars: "vars p = {..<n}" 
    by (auto simp: valid_monotone_poly_def p_def)
  from linear[OF g] p_def
  have linear: "total_degree p \<le> 1" by auto
  show ?thesis unfolding p_def[symmetric]
    by (rule monotone_linear_poly_to_coeffs[OF linear poly mono vars])
qed

lemma solution: "positive_poly_problem p q" 
  apply (rule solution_poly_input_R.solution[of _ _ I])
  apply (unfold_locales)
   apply (rule orient)
  apply (rule extract_linear_poly)
  by auto
end
  
locale wm_lin_orient_poly_input = poly_input p q for p q +
  assumes wm_orient: "orientation_by_linear_wm_int_poly_interpretation F_R R'" 
begin

definition I where "I = (SOME I. linear_wm_int_poly_inter F_R I \<and> wm_int_poly_inter.oriented_by_interpretation F_R I R')" 

lemma I: "linear_wm_int_poly_inter F_R I" "wm_int_poly_inter.oriented_by_interpretation F_R I R'" 
  using someI_ex[OF wm_orient[unfolded orientation_by_linear_wm_int_poly_interpretation_def], folded I_def] by auto

sublocale linear_wm_int_poly_inter F_R I by (rule I(1))

lemma orient_R': "orient_rule (lhs_R',rhs_R')" 
  using I(2)[unfolded oriented_by_interpretation_def] unfolding R'_def by auto

lemma extract_linear_poly: assumes g: "(g,n) \<in> F_R" 
  shows "\<exists> c a. I g = Const c + (\<Sum>i\<leftarrow>[0..<n]. Const (a i) * PVar i)
     \<and> c \<ge> 0 \<and> (\<forall> i < n. a i \<ge> 0)" 
proof -
  define p where "p = I g" 
  have sum_zero: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list (xs :: int list) = 0" for xs by (induct xs, auto)
  from valid[unfolded valid_weakly_monotone_inter_def valid_weakly_monotone_poly_def, rule_format, OF g refl p_def]
  have poly: "valid_poly p" 
    and mono: "weakly_monotone_poly {..<n} p" 
    and vars: "vars p \<subseteq> {..<n}" 
    by (auto simp: valid_monotone_poly_def p_def)
  from linear[OF g] p_def
  have linear: "total_degree p \<le> 1" by auto
  from coefficients_of_linear_poly[OF linear] obtain c b vs 
    where p: "p = Const c + (\<Sum>i\<leftarrow>vs. Const (b i) * PVar i)"
     and vsd: "distinct vs" "set vs = vars p" "sorted_list_of_set (vars p) = vs"
     and nz: "\<And> v. v \<in> set vs \<Longrightarrow> b v \<noteq> 0"
     and c: "c = coeff p 0"
     and b: "\<And> i. b i = coeff p (monomial 1 i)" by blast
  define a where "a x = (if x \<in> vars p then b x else 0)" for x
  have "p = Const c + (\<Sum>i\<leftarrow>vs. Const (b i) * PVar i)" by fact
  also have "(\<Sum>i\<leftarrow>vs. Const (b i) * PVar i) = (\<Sum>i \<in> set vs. Const (b i) * PVar i)" using vsd(1)
    by (rule sum_list_distinct_conv_sum_set)
  also have "\<dots> = (\<Sum>i \<in> set vs. Const (a i) * PVar i) + 0" by (subst sum.cong, auto simp: a_def vsd)
  also have "0 = (\<Sum>i \<in> {..<n} - set vs. Const (a i) * PVar i)"
    by (subst sum.neutral, auto simp: a_def vsd)
  also have "(\<Sum>i \<in> set vs. Const (a i) * PVar i) + \<dots> = (\<Sum>i \<in> set vs \<union> ({..<n} - set vs). Const (a i) * PVar i)"
    by (subst sum.union_inter[symmetric], auto)
  also have "set vs \<union> ({..<n} - set vs) = set [0..<n]" using vars vsd by auto
  finally have pca: "p = Const c + (\<Sum>i \<leftarrow> [0..<n]. Const (a i) * PVar i)" 
    by (subst sum_list_distinct_conv_sum_set, auto)

  show ?thesis unfolding p_def[symmetric] pca 
  proof (intro exI conjI allI impI, rule refl)
    show c: "c \<ge> 0" using poly[unfolded valid_poly_def, rule_format, of "\<lambda> _. 0", unfolded p]
      by (auto simp: coeff_add[symmetric] coeff_Const coeff_sum_list o_def coeff_Const_mult 
        coeff_Var monomial_0_iff assignment_def)
    fix i
    assume "i < n" 
    show "a i \<ge> 0" 
    proof (cases "i \<in> set vs")
      case False
      thus ?thesis unfolding a_def using vsd by auto
    next
      case i: True
      from nz[OF this] have a0: "a i \<noteq> 0" "b i = a i" using i by (auto simp: a_def vsd)
      from split_list[OF i] obtain bef aft where vsi: "vs = bef @ [i] @ aft" by auto
      with vsd(1) have i: "i \<notin> set (bef @ aft)" by auto
      define \<alpha> where "\<alpha> = (\<lambda> x. if x = i then c + 1 else 0)" 
      have "assignment \<alpha>" unfolding assignment_def \<alpha>_def using c by auto
      from poly[unfolded valid_poly_def, rule_format, OF this, unfolded p]
      have "0 \<le> c + (\<Sum>x\<leftarrow>bef @ aft. b x * \<alpha> x) + (b i * \<alpha> i)" 
        unfolding insertion_add vsi map_append sum_list_append insertion_Const insertion_sum_list
        map_map o_def insertion_mult insertion_Var
        by (simp add: algebra_simps)
      also have "(\<Sum>x\<leftarrow>bef @ aft. b x * \<alpha> x) = 0" by (rule sum_zero, insert i, auto simp: \<alpha>_def)
      also have "\<alpha> i = (c + 1)" unfolding \<alpha>_def by auto
      finally have le: "0 \<le> c * (a i + 1) + a i" using a0 by (simp add: algebra_simps)
      with c show "a i \<ge> 0"
        by (smt (verit, best) mult_le_0_iff)
    qed
  qed
qed

lemma extract_a_poly: "\<exists> a0 a1 a2. I a_sym = Const a0 + Const a1 * PVar 0 + Const a2 * PVar 1 
  \<and> a0 \<ge> 0 \<and> a1 \<ge> 0 \<and> a2 \<ge> 0"
proof -
  have [simp]: "[0 ..<2] = [0,1]" by code_simp
  have [simp]: "(\<forall>i<2. P i) = (P 0 \<and> P (1 :: nat))" for P by (auto simp add: numeral_eq_Suc less_Suc_eq) 
  have "(a_sym,2) \<in> F_R" unfolding F_R_def F_def by auto
  from extract_linear_poly[OF this]
  show ?thesis by force 
qed

lemma extract_f_poly: "\<exists> f0 f1 f2 f3 f4. I f_sym = Const f0 + Const f1 * PVar 0 + Const f2 * PVar 1 
     + Const f3 * PVar 2 + Const f4 * PVar 3
  \<and> f0 \<ge> 0 \<and> f1 \<ge> 0 \<and> f2 \<ge> 0 \<and> f3 \<ge> 0 \<and> f4 \<ge> 0"
proof -
  have [simp]: "[0 ..<4] = [0,1,2,3]" by code_simp
  have [simp]: "(\<forall>i<4. P i) = (P 0 \<and> P (1 :: nat) \<and> P 2 \<and> P 3)" for P 
    by (auto simp add: numeral_eq_Suc less_Suc_eq) 
  have "(f_sym,4) \<in> F_R" unfolding F_R_def by auto
  from extract_linear_poly[OF this] obtain c f where 
    main: "I f_sym = Const c + (\<Sum>i\<leftarrow>[0..<4]. Const (f i) * PVar i) \<and> 0 \<le> c \<and> (\<forall>i<4. 0 \<le> f i)" by auto
  show ?thesis 
    apply (rule exI[of _ c])
    apply (rule exI[of _ "f 0"])
    apply (rule exI[of _ "f 1"])
    apply (rule exI[of _ "f 2"])
    apply (rule exI[of _ "f 3"])
    by (insert main, auto)
qed


lemma solution: "positive_poly_problem p q" 
proof -
  from extract_f_poly obtain f0 f1 f2 f3 f4 where
    If: "I f_sym =
       Const f0 + Const f1 * PVar 0 + Const f2 * PVar 1 + Const f3 * PVar 2 + Const f4 * PVar 3" 
    and fpos: "0 \<le> f0" "0 \<le> f1" "0 \<le> f2" "0 \<le> f3" "0 \<le> f4" by auto
  from extract_a_poly obtain a0 a1 a2 where
    Ia: "I a_sym = Const a0 + Const a1 * PVar 0 + Const a2 * PVar 1"
    and apos: "0 \<le> a0" "0 \<le> a1" "0 \<le> a2" by auto
  {
    fix i
    assume "i \<in> V" 
    hence v: "(v_sym i, 1) \<in> F_R" unfolding F_R_def F_def by auto
    from extract_linear_poly[OF v] have "\<exists> v0 v1. I (v_sym i) = Const v0 + Const v1 * PVar 0 \<and> v0 \<ge> 0 \<and> v1 \<ge> 0"
      by auto
  }
  hence "\<forall> i. \<exists> v0 v1. i \<in> V \<longrightarrow> I (v_sym i) = Const v0 + Const v1 * PVar 0 \<and> v0 \<ge> 0 \<and> v1 \<ge> 0" by auto
  from choice[OF this] obtain v0 where "\<forall> i. \<exists> v1. i \<in> V \<longrightarrow> I (v_sym i) = Const (v0 i) + Const v1 * PVar 0 \<and> v0 i \<ge> 0 \<and> v1 \<ge> 0" by auto
  from choice[OF this] obtain v1 where Iv: "\<And> i. i \<in> V \<Longrightarrow> I (v_sym i) = Const (v0 i) + Const (v1 i) * PVar 0"
    and vpos: "\<And> i. i \<in> V \<Longrightarrow> v0 i \<ge> 0 \<and> v1 i \<ge> 0" by auto

  have "(z_sym,0) \<in> F_R" unfolding F_R_def F_def by auto
  from extract_linear_poly[OF this] obtain z0 where 
    Iz: "I z_sym = Const z0" 
    and zpos: "z0 \<ge> 0" by auto

  have "(o_sym,0) \<in> F_R" unfolding F_R_def F_def by auto
  from extract_linear_poly[OF this] obtain o0 where 
    Io: "I o_sym = Const o0" 
    and opos: "o0 \<ge> 0" by auto

  have prod_ge: "(\<And> x. x \<in> set xs \<Longrightarrow> x \<ge> 0) \<Longrightarrow> prod_list xs \<ge> 0" for xs :: "int list" by (induct xs, auto)
  define d1 where "d1 = prod_list ([a1, a2, f1, f2, f3, f4] @ map v1 V_list)" 
  have d1: "d1 \<ge> 0" unfolding d1_def using apos fpos vpos 
    by (intro prod_ge, auto simp: V_list)
  from inter_all_symbol_pos_ctxt_generic[of I, OF If Ia Iv Iz]
  obtain d where ctxt: "\<And> t. eval (all_symbol_pos_ctxt t) = 
    Const d + Const d1 * eval t" by (auto simp: d1_def)
  
  {
    fix \<beta> :: "var \<Rightarrow> int" 
    assume "assignment \<beta>" 
    from orient_R'[unfolded orient_rule split gt_poly_def, rule_format, OF this]
    have "insertion \<beta> (eval lhs_R') > insertion \<beta> (eval rhs_R')" (is ?A) by auto
    also have "?A \<longleftrightarrow> d1 * insertion \<beta> (eval lhs_R) > d1 * insertion \<beta> (eval rhs_R)" 
      unfolding lhs_R'_def rhs_R'_def ctxt
      insertion_add insertion_mult insertion_Const by auto
    also have "\<dots> \<longleftrightarrow> (d1 > 0 \<and> insertion \<beta> (eval lhs_R) > insertion \<beta> (eval rhs_R))" 
      using d1 by (simp add: mult_less_cancel_left_disj)
    finally have "d1 > 0" "insertion \<beta> (eval lhs_R) > insertion \<beta> (eval rhs_R)" by auto
  }
  from this(2) this(1)[of "\<lambda> _. 0"] 
  have d1: "d1 > 0" and gt: "gt_poly (eval lhs_R) (eval rhs_R)" 
    unfolding gt_poly_def by (auto simp: assignment_def)

  hence orient_R: "orient_rule (lhs_R, rhs_R)" unfolding orient_rule by auto

  from d1 have "d1 \<noteq> 0" by auto
  from this[unfolded d1_def, simplified] apos fpos
  have apos: "a0 \<ge> 0" "a1 > 0" "a2 > 0" 
    and fpos: "f0 \<ge> 0" "f1 > 0" "f2 > 0" "f3 > 0" "f4 > 0" 
    and prod: "prod_list (map v1 V_list) \<noteq> 0" by auto
  from prod have vpos1: "i \<in> V \<Longrightarrow> v0 i \<ge> 0 \<and> v1 i > 0" for i using vpos[of i]
    unfolding prod_list_zero_iff set_map V_list by auto

  {
    fix g n
    assume "(g,n) \<in> F_R" 
    then consider (f) "(g,n) = (f_sym,4)" | (a) "(g,n) = (a_sym,2)" | (z) "(g,n) = (z_sym,0)" 
      | (o) "(g,n) = (o_sym,0)" | (v) i where "(g,n) = (v_sym i, Suc 0)" "i \<in> V" 
      unfolding F_R_def F_def by auto
    hence "\<exists>c a. I g = Const c + (\<Sum>i\<leftarrow>[0..<n]. Const (a i) * PVar i) \<and> 0 \<le> c \<and> (\<forall>i<n. 0 < a i)" 
    proof cases
      case *: a
      have [simp]: "[0..<2] = [0,1]" by code_simp
      thus ?thesis using * apos Ia
        by (intro exI[of _ a0] exI[of _ "\<lambda> i. if i = 0 then a1 else a2"], auto)
    next
      case *: f
      have [simp]: "[0..<4] = [0,1,2,3]" by code_simp
      thus ?thesis using * If fpos 
        by (intro exI[of _ f0] 
            exI[of _ "\<lambda> i. if i = 0 then f1 else if i = 1 then f2 else if i = 2 then f3 else f4"], auto)
    next
      case *: z
      show ?thesis using * Iz zpos by auto
    next
      case *: o
      show ?thesis using * Io opos by auto
    next
      case *: (v i)
      show ?thesis using * Iv[OF *(2)] vpos1[OF *(2)] 
        by (intro exI[of _ "v0 i"] exI[of _ "\<lambda> _. v1 i"], auto)
    qed
  } note main = this

  show ?thesis
    apply (rule solution_poly_input_R.solution[of _ _ I])
    apply unfold_locales
    using orient_R main by auto
qed  
end

context poly_input
begin

text \<open>Theorem 3.4 in paper\<close>
theorem linear_polynomial_termination_with_natural_numbers_undecidable: 
  "positive_poly_problem p q \<longleftrightarrow> termination_by_linear_int_poly_interpretation F_R R"
proof
  assume "positive_poly_problem p q" 
  interpret solvable_poly_problem
    by (unfold_locales, fact)
  from solution_imp_linear_termination_R
  show "termination_by_linear_int_poly_interpretation F_R R" .
next
  assume "termination_by_linear_int_poly_interpretation F_R R" 
  interpret lin_term_poly_input
    by (unfold_locales, fact)
  from solution show "positive_poly_problem p q" .
qed

text \<open>Theorem 3.9\<close>
theorem orientation_by_linear_wm_int_poly_interpretation_undecidable: 
  "positive_poly_problem p q \<longleftrightarrow> orientation_by_linear_wm_int_poly_interpretation F_R R'"
proof
  assume "positive_poly_problem p q" 
  interpret solvable_poly_problem
    by (unfold_locales, fact)
  from solution_imp_linear_termination_R'
  have "termination_by_linear_int_poly_interpretation F_R R'" .
  from this[unfolded termination_by_linear_int_poly_interpretation_def] obtain I 
    where lin: "linear_int_poly_inter F_R I" and 
      R': "int_poly_inter.termination_by_poly_interpretation F_R I R'"
    by auto
  interpret linear_int_poly_inter F_R I by fact
  show "orientation_by_linear_wm_int_poly_interpretation F_R R'" 
    unfolding orientation_by_linear_wm_int_poly_interpretation_def
  proof (intro exI conjI)
    show "linear_wm_int_poly_inter F_R I" 
    proof
      show "valid_weakly_monotone_inter" unfolding valid_weakly_monotone_inter_def
      proof
        fix f 
        assume "f \<in> F_R" 
        from valid[unfolded valid_monotone_poly_inter_def, rule_format, OF this]
        have "valid_monotone_poly f" by auto
        thus "valid_weakly_monotone_poly f" 
          by (rule monotone_imp_weakly_monotone, auto)
      qed
    qed
    interpret linear_wm_int_poly_inter F_R I by fact
    show "oriented_by_interpretation R'" unfolding oriented_by_interpretation_def
      using R' unfolding termination_by_poly_interpretation_def termination_by_interpretation_def .
  qed
next
  assume "orientation_by_linear_wm_int_poly_interpretation F_R R'" 
  interpret wm_lin_orient_poly_input
    by (unfold_locales, fact)
  from solution show "positive_poly_problem p q" .
qed

end

text \<open>Separate locale to define another interpretation, i.e., the one of Lemma 3.6\<close>

locale poly_input_non_lin_solution = poly_input
begin

text \<open>Non-linear interpretation of Lemma 3.6\<close>

fun I :: "symbol \<Rightarrow> int mpoly" where 
  "I f_sym = PVar 2 * PVar 3 + PVar 0 + PVar 1 + PVar 2 + PVar 3" 
| "I a_sym = PVar 0 + PVar 1"
| "I z_sym = 0" 
| "I o_sym = Const (1 + insertion (\<lambda> _. 1) q)" 
| "I (v_sym i) = PVar 0" 

sublocale inter_R: poly_inter F_R I "(>)" .

lemma inter_encode_num: assumes "c \<ge> 0" 
  shows "inter_R.eval (encode_num x c) = Const c * PVar x" 
proof -
  from assms obtain n where cn: "c = int n" by (metis nonneg_eq_int)
  hence natc: "nat c = n" by auto
  show ?thesis unfolding encode_num_def natc unfolding cn
    by (induct n, auto simp: Const_0 Const_1 algebra_simps Const_add)
qed

lemma inter_v_pow_e: "inter_R.eval ((v_t x ^^ e) t) = inter_R.eval t" 
  by (induct e, auto)

lemma inter_encode_monom: assumes c: "c \<ge> 0" 
  shows "inter_R.eval (encode_monom y m c) = Const (insertion (\<lambda> _.1) (monom m c)) * PVar y" 
proof -
  define xes where "xes = var_list m" 
  from var_list[of m c] 
  have monom: "monom m c = Const c * (\<Prod>(x, e)\<leftarrow> xes . PVar x ^ e) " unfolding xes_def .
  show ?thesis unfolding encode_monom_def monom xes_def[symmetric]
  proof (induct xes)
    case Nil
    show ?case by (simp add: inter_encode_num[OF c] insertion_Const)
  next
    case (Cons xe xes)
    obtain x e where xe: "xe = (x,e)" by force
    show ?case by (simp add: xe inter_v_pow_e Cons Const_power 
          insertion_Const insertion_mult insertion_power insertion_Var Const_mult)
  qed
qed

lemma inter_encode_poly: assumes "positive_poly r" 
  shows "inter_R.eval (encode_poly x r) = Const (insertion (\<lambda> _.1) r) * PVar x" 
proof -
  define mcs where "mcs = monom_list r" 
  from monom_list[of r] have r: "r = (\<Sum>(m, c)\<leftarrow> mcs. monom m c)" unfolding mcs_def by auto
  have mcs: "(m,c) \<in> set mcs \<Longrightarrow> c \<ge> 0" for m c 
    using monom_list_coeff assms unfolding mcs_def positive_poly_def by auto
  show ?thesis unfolding encode_poly_def mcs_def[symmetric] unfolding r insertion_sum_list map_map o_def
    using mcs
  proof (induct mcs)
    case (Cons mc mcs)
    obtain m c where mc: "mc = (m,c)" by force
    from Cons(2) mc have c: "c \<ge> 0" by auto
    note monom = inter_encode_monom[OF this, of x m]
    show ?case
      by (simp add: mc monom algebra_simps, subst Cons(1), insert Cons(2), auto simp: Const_add algebra_simps)
  qed simp
qed

lemma valid_monotone_inter: "inter_R.valid_monotone_poly_inter" 
  unfolding inter_R.valid_monotone_poly_inter_def 
proof (intro ballI, unfold inter_R.valid_monotone_poly_def, clarify, intro conjI)
  fix f n
  assume f: "(f,n) \<in> F_R" 
  have [simp]: "vars (PVar 2 * PVar 3 + (PVar 0 :: int mpoly) + PVar (Suc 0) + PVar 2 + PVar 3) = {0,1,2,3}" 
    unfolding vars_def apply (transfer, simp add: Var\<^sub>0_def image_comp) by code_simp
  have [simp]: "vars ((PVar 0 :: int mpoly) + PVar (Suc 0)) = {0,1}" 
    unfolding vars_def apply (transfer, simp add: Var\<^sub>0_def image_comp) by code_simp
  from f show "vars (I f) = {..< n}" unfolding F_R_def F_def by auto
  have "insertion (\<lambda> _. 1) q \<ge> 0" 
    by (rule insertion_positive_poly[OF _ pq(2)], auto)
  with f show "valid_poly (I f)" unfolding F_R_def F_def
    by (auto simp: valid_poly_def insertion_add assignment_def insertion_Var insertion_mult insertion_Const)
  have x4: "x < 4 \<Longrightarrow> x = 0 \<or> x = Suc 0 \<or> x = 2 \<or> x = 3" for x by linarith
  have x2: "x < 2 \<Longrightarrow> x = 0 \<or> x = Suc 0" for x by linarith
  have tedious_case: "inter_R.monotone_poly {..<4} (I f_sym)" unfolding
    monotone_poly_wrt_def I.simps 
  proof (intro allI impI, goal_cases)
    case (1 \<alpha> x v)
    have manual: "(\<alpha>(x := v)) 2 * (\<alpha>(x := v)) 3 \<ge> \<alpha> 2 * \<alpha> 3" 
      by (intro mult_mono, insert 1, auto simp: assignment_def dest: spec[of _ 2])
    thus ?case unfolding insertion_add insertion_mult insertion_Var using 1 x4 by auto
  qed
  with f show "inter_R.monotone_poly {..<n} (I f)" unfolding F_R_def F_def
    by (auto simp: monotone_poly_wrt_def insertion_add insertion_mult insertion_Var assignment_def
        dest: x4 x2)
qed

text \<open>Lemma 3.6 in the paper\<close>

lemma orient_R_main: assumes "assignment \<beta>"
  shows "insertion \<beta> (inter_R.eval lhs_R) > insertion \<beta> (inter_R.eval rhs_R)" 
proof -
  let ?\<alpha> = "\<lambda> _. 1" 
  have reason: "insertion ?\<alpha> q + \<beta> y3 + insertion ?\<alpha> p * insertion ?\<alpha> q * \<beta> y3 + insertion ?\<alpha> p * 2 * \<beta> y3 \<ge> 0"
    by (intro add_nonneg_nonneg mult_nonneg_nonneg insertion_positive_poly pq,
        insert assms, auto simp: assignment_def)
  show "insertion \<beta> (inter_R.eval lhs_R) > insertion \<beta> (inter_R.eval rhs_R)"
    unfolding lhs_R_def rhs_R_def
    using reason
    by (simp add: inter_encode_poly[OF pq(1)] inter_encode_poly[OF pq(2)] 
        insertion_add insertion_mult insertion_Const insertion_Var algebra_simps)
qed

lemma polynomial_termination_R: "termination_by_int_poly_interpretation F_R R" 
  unfolding termination_by_int_poly_interpretation_def
proof (intro exI conjI)
  interpret int_poly_inter F_R I
    by (unfold_locales, rule valid_monotone_inter)
  show "int_poly_inter F_R I" ..
  show "termination_by_poly_interpretation R" 
    unfolding termination_by_interpretation_def termination_by_poly_interpretation_def R_def
  proof (clarify, intro conjI)
    show "inter_R.orient_rule (lhs_R,rhs_R)" 
      unfolding inter_R.gt_poly_def inter_R.orient_rule
      by (intro allI impI orient_R_main)
  qed (insert lhs_R_F rhs_R_F, auto)
qed

lemma polynomial_termination_R': "termination_by_int_poly_interpretation F_R R'" 
  unfolding termination_by_int_poly_interpretation_def
proof (intro exI conjI)
  interpret int_poly_inter F_R I
    by (unfold_locales, rule valid_monotone_inter)
  show "int_poly_inter F_R I" ..
  show "termination_by_poly_interpretation R'" 
    unfolding termination_by_poly_interpretation_def termination_by_interpretation_def R'_def
  proof (clarify, intro conjI)
    show "inter_R.orient_rule (lhs_R',rhs_R')" 
      unfolding inter_R.gt_poly_def inter_R.orient_rule
    proof (intro allI impI)
      fix \<beta> :: "var \<Rightarrow> int" 
      assume ass: "assignment \<beta>" 
      define zctxt where "zctxt vs = z_contexts (map (\<lambda>i. (v_sym i, 1, 0)) vs)" for vs
      have zctxt: "inter_R.eval (zctxt vs t) = inter_R.eval t" for vs t
        unfolding zctxt_def z_contexts_def z_context_def by (induct vs, auto)
      have "(insertion \<beta> (inter_R.eval lhs_R') > insertion \<beta> (inter_R.eval rhs_R'))
      \<longleftrightarrow> insertion \<beta> (inter_R.eval (zctxt V_list lhs_R)) > insertion \<beta> (inter_R.eval (zctxt V_list rhs_R))"
        unfolding lhs_R'_def rhs_R'_def
        unfolding all_symbol_pos_ctxt_def contexts_def
        unfolding z_contexts_append zctxt_def[symmetric]
        by (simp add: z_contexts_def z_context_def nth_append)
      also have "\<dots> \<longleftrightarrow> insertion \<beta> (inter_R.eval lhs_R) > insertion \<beta> (inter_R.eval rhs_R)" 
        unfolding zctxt ..
      also have "\<dots>" by (rule orient_R_main[OF ass]) 
      finally show "insertion \<beta> (inter_R.eval lhs_R') > insertion \<beta> (inter_R.eval rhs_R')" .
    qed
  qed (insert lhs_R'_F rhs_R'_F, auto)
qed

end
end