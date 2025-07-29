theory Algebra_Basics
  imports Main "../Lucas_Sequences/Lucas_Sequences"
          "HOL-Computational_Algebra.Primes" Complex_Main HOL.NthRoot
begin

section \<open>Relation Combining\<close>

text \<open>In this section the Matiyasevich-Robinson polynomial is formalized. The formal proof 
      follows their paper~\cite{MR75}: first, auxiliary polynomials $J_3$ and $\Pi$ are defined
      and then $M_3$ can be constructed from them.\<close>

subsection \<open>Algebra Preliminaries\<close>

lemma coercion_coherent: "complex_of_real (of_rat q) = of_rat q"
proof -
  obtain a b where q_def: "(a,b) = quotient_of q" by (metis small_lazy'.cases)
  hence eq1: "real_of_rat q = (of_int a) / (of_int b) \<and> of_rat q = (of_int a) / (of_int b)"
    by (metis of_rat_divide of_rat_of_int_eq quotient_of_div)
  hence eq: "of_real (of_rat q) = of_real ((of_int a) / (of_int b)) "
    by force
  have "b \<noteq> 0" using q_def by (smt (verit, best) quotient_of_denom_pos)
  hence "real_of_int b \<noteq> 0" using of_int_eq_0_iff by blast
  hence "complex_of_real (of_rat q) = (of_real (of_int a)) / (of_real (of_int b))" using eq 
nonzero_of_real_divide[of "of_int b" "of_int a"] by force
  hence "complex_of_real (of_rat q) = (of_int a) / (of_int b)" by simp
  thus ?thesis using eq1 by metis
qed

definition C::"complex set" where "C = {x. True}"
definition Q::"complex set" where "Q = {x. \<exists>q::rat. x = of_rat q}"
definition Qi::"complex set" where "Qi = {x. Re x \<in> Q \<and> Im x \<in> Q}"
 
definition cpx_sqrt:: "int \<Rightarrow> complex" where
"cpx_sqrt n = (if (n \<ge> 0) then (sqrt n) else (\<i> * sqrt (-n)))"

lemma norm_cpx_sqrt: "norm (cpx_sqrt x) = sqrt (norm x)"
  unfolding cpx_sqrt_def by (simp add: cmod_def)

lemma square_sqrt: "(cpx_sqrt n)^2 = n"
proof (cases "n\<ge>0")
  case True
  then show ?thesis unfolding cpx_sqrt_def apply simp
    by (metis of_int_nonneg of_real_of_int_eq of_real_power real_sqrt_pow2)
next
  case False
  then show ?thesis unfolding cpx_sqrt_def apply simp
    by (smt (verit, del_insts) i_squared i_times_eq_iff mult.assoc mult_minus_right of_int_0_le_iff 
        of_real_minus of_real_of_int_eq of_real_sqrt power2_csqrt power2_i power_mult_distrib)
qed

(* Iteratively constructs Q[sqrt(a_1), ..., sqrt(a_n)] *)
fun field:: "int list \<Rightarrow> complex set" where
"field [] = Q" |
"field (a # l) = {x. \<exists>q\<in>(field l). \<exists>r\<in>(field l). x = q + r*cpx_sqrt a}"

lemma Qi_is_m1: "Qi = field [-1]"
proof -
  have "x \<in> Qi \<Longrightarrow> x \<in> field [-1]" for x
  proof -
    assume hyp: "x \<in> Qi"
    have ecr_x: "x = Re x + Im x * \<i>" by (simp add: complex_eq mult.commute)
    have "Re x \<in> field [] \<and> Im x \<in> field []" using Qi_def hyp by force
    thus "x \<in> field [-1]" using cpx_sqrt_def ecr_x by fastforce
  qed
  hence inc1: "Qi \<subseteq> field [-1]" by blast
  have "x \<in> field [-1] \<Longrightarrow> x \<in> Qi" for x
  proof -
    assume hyp: "x \<in> field [-1]"
    then obtain q r where x_def1: "x = q + r * cpx_sqrt (-1) \<and> q \<in> Q \<and> r \<in> Q" by auto
    hence x_def: "x = q + r*\<i> \<and> q \<in> Q \<and> r \<in> Q" using cpx_sqrt_def by fastforce
    hence ReIm_x: "Re x = Re q - Im r \<and> Im x = Im q + Re r" by simp
    have ReIm_rat: "\<And>q. Im (of_rat q) = 0 \<and> complex_of_real (Re (of_rat q)) = of_rat q"
    proof -
      fix q::rat
      obtain a b where q_def: "(a,b) = quotient_of q" by (metis small_lazy'.cases)
      hence "Im (of_rat q) = Im (of_int a / (of_int b))"
        by (metis of_rat_divide of_rat_of_int_eq quotient_of_div)
      hence "Im (of_rat q) = Im (of_int a) / (of_int b)" by simp
      hence "Im (of_rat q) = 0" by simp
      thus "Im (of_rat q) = 0 \<and> complex_of_real (Re (of_rat q)) = of_rat q"
        by (simp add: complex_is_Real_iff)
    qed
    have "\<And>q. q \<in> Q \<Longrightarrow> Im q = 0 \<and> complex_of_real (Re q) = q"
    proof -
      fix q::complex
      assume hypo: "q \<in> Q"
      then obtain r where "q = of_rat r" using Q_def by force
      thus "Im q = 0 \<and> complex_of_real (Re q) = q" using ReIm_rat by simp
    qed
    hence "Re x = q \<and> Im x = r" using ReIm_x x_def1 by fastforce
    thus "x \<in> Qi" using Qi_def x_def1 by blast
  qed
  thus ?thesis using inc1 by fastforce
qed

lemma Zero_in_field: "0 \<in> field l"
proof (induction l)
  case Nil
  have "0 = of_rat 0" by simp
  then show ?case using Q_def by force
next
  case (Cons a l)
  note t = this
  have "0 = 0 + 0 * cpx_sqrt a" by simp
  then show ?case using t by force
qed

lemma field_incr: "field l \<subseteq> field (a#l)"
proof -
  have "x \<in> field l \<Longrightarrow> x \<in> field (a#l)" for x
  proof -
    assume hyp: "x \<in> field l"
    have "x = x + 0 * cpx_sqrt a" by simp
    thus "x \<in> field (a#l)" using Zero_in_field hyp by force
  qed
  thus ?thesis by blast
qed

lemma int_in_field: "\<And>x::int. of_int x \<in> field l"
proof (induction l)
  case Nil
  fix x::int
  have "x = rat_of_int x" by auto
  then show "of_int x \<in> field []" using Q_def by fastforce
next
  case (Cons a l)
  then show ?case using field_incr by blast
qed

lemma field_add_mult: "\<And>x y. x \<in> field l \<and> y \<in> field l \<Longrightarrow> (x + y \<in> field l \<and> x*y \<in> field l)"
proof (induction l)
  case Nil
  assume hyp: "x \<in> field [] \<and> y \<in> field []"
  then obtain q r where "x = of_rat q \<and> y = of_rat r" using Q_def by force
  hence "x + y = of_rat (q+r) \<and> x*y = of_rat (q*r)" by (simp add: of_rat_add of_rat_mult)
  then show "x + y \<in> field [] \<and> x*y \<in> field []" using Q_def by force
next
  case (Cons a l)
  note t = this
  assume hyp: "x \<in> field (a#l) \<and> y \<in> field (a#l)"
  have a_in_field: "a \<in> field l" using int_in_field by auto
  obtain x1 x2 where x_def: "x = x1 + x2 * cpx_sqrt a \<and> x1 \<in> field l \<and> x2 \<in> field l" using hyp by force
  obtain y1 y2 where y_def: "y = y1 + y2 * cpx_sqrt a \<and> y1 \<in> field l \<and> y2 \<in> field l" using hyp by force
  have in_field: "x1 + y1 \<in> field l \<and> x2 + y2 \<in> field l \<and> x1*y1 + a*x2*y2 \<in> field l \<and> x1*y2 + x2*y1 \<in> field l"
    using x_def y_def a_in_field by (auto simp add: t(1))
  have "x + y = (x1 + y1) + (x2 + y2)*cpx_sqrt a \<and> x*y = (x1*y1 + a*x2*y2) + (x1*y2 + x2*y1)*cpx_sqrt a"
    using power2_eq_square[of "cpx_sqrt a"] square_sqrt[of a] x_def y_def by algebra
  then show "x + y \<in> field (a#l) \<and> x*y \<in> field (a#l)" using in_field by force
qed

lemma field_square: "x \<in> field l \<Longrightarrow> x^2 \<in> field l" using power2_eq_square field_add_mult by metis

lemma field_opp: "x \<in> field l \<Longrightarrow> -x \<in> field l"
proof -
  assume hyp: "x \<in> field l"
  have "-1 = of_int (-1)" by auto
  hence "-1 \<in> field l \<and> -x = (-1)*x" using int_in_field by (smt (verit, best) mult_minus1)
  thus "-x \<in> field l" using hyp field_add_mult by force
qed

lemma field_inv_div: "\<And>x y. x \<in> field l \<and> y \<in> field l \<Longrightarrow> (1/x \<in> field l \<and> y/x \<in> field l)"
proof (induction l)
  case Nil
  assume hyp: "x \<in> field [] \<and> y \<in> field []"
  then obtain q where q_def: "x = of_rat q" using Q_def by force
  hence "inverse x = of_rat (inverse q)"
    using of_rat_inverse[of q] by (smt (verit, best))
  hence "1/x = of_rat (1/q)" by (simp add: inverse_eq_divide)
  hence inv: "1/x \<in> Q" using Q_def by force
  have "y/x = y*(1/x)" by auto
  then show "1/x \<in> field [] \<and> y/x \<in> field []" using hyp inv field_add_mult by fastforce
next
  case (Cons a l)
  note HR = this
  assume hyp: "x \<in> field (a#l) \<and> y \<in> field (a#l)"
  then obtain q r where x_def: "x = q + r * cpx_sqrt a \<and> q \<in> field l \<and> r \<in> field l" by force
  then show "1/x \<in> field (a#l) \<and> y/x \<in> field (a#l)"
  proof (cases "q - r * cpx_sqrt a = 0")
    case True
    note t = this
    then show ?thesis
    proof (cases "r = 0")
      case True
      hence "q = 0 \<and> r = 0" using t by simp
      hence "x = 0" using x_def by simp
      then show ?thesis using hyp by presburger
    next
      case False
      hence "cpx_sqrt a = q/r" using t by auto
      hence "cpx_sqrt a \<in> field l" using HR(1)[of r q] x_def by force
      hence "x \<in> field l" using x_def field_add_mult by auto
      hence "1/x \<in> field l" using HR by force
      hence "1/x \<in> field (a#l)" using field_incr by blast
      hence "1/x \<in> field (a#l) \<and> y/x = y*(1/x)" by simp
      then show ?thesis using hyp field_add_mult by metis
    qed
  next
    case False
    note t = this
    have a_in_field: "a \<in> field l" using int_in_field by auto
    have calc: "(q + r * cpx_sqrt a) * (q - r * cpx_sqrt a) = q*q - a*r*r" 
      using power2_eq_square[of "cpx_sqrt a"] square_sqrt[of a] by (auto simp add: algebra_simps)
    have "x = ((q + r * cpx_sqrt a) * (q - r * cpx_sqrt a))/(q - r* cpx_sqrt a)" using divide_self t
      by (simp add: x_def)
    hence "1/x = (q - r * cpx_sqrt a)/(q*q-a*r*r)" using calc by auto
    hence ecrx: "1/x = q/(q*q-a*r*r) + (-r)/(q*q-a*r*r)*cpx_sqrt a"
      by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus 
        add_divide_eq_if_simps(2) eq_divide_eq mult_minus_left times_divide_eq_left)
    have "q*q-a*r*r \<in> field l \<and> -r \<in> field l" using a_in_field x_def field_add_mult field_opp
      apply simp by (metis ab_group_add_class.ab_diff_conv_add_uminus)
    hence "q/(q*q-a*r*r) \<in> field l \<and> (-r)/(q*q-a*r*r) \<in> field l" using x_def HR(1) by blast
    hence "1/x \<in> field (a#l) \<and> y/x = y*(1/x)" using ecrx
      by (metis (mono_tags, lifting) field.simps(2) mem_Collect_eq mult.right_neutral times_divide_eq_right)
    thus "1/x \<in> field (a#l) \<and> y/x \<in> field (a#l)" using field_add_mult hyp by presburger
  qed
qed

lemma field_sum: "(\<forall>x\<in>S. f x\<in>field l) \<Longrightarrow> finite S \<Longrightarrow> (\<Sum>x\<in>S. f x) \<in> field l"
proof (induction "card S" arbitrary:S)
  case 0
  then show ?case using Zero_in_field by simp
next
  case (Suc n)
  assume assm: "(\<forall>x\<in>S. f x\<in>field l)"
  obtain y where y_prop: "y\<in>S" using Suc by fastforce
  define S' where "S' = S - {y}"
  hence card_S':"card S' = n" using Suc by (simp add: y_prop)
  have disj_un_S: "S = S'\<union>{y} \<and> S'\<inter>{y}={}\<and>finite S" using y_prop S'_def Suc by force
  hence "(\<Sum>x\<in>S. f x) = (\<Sum>x\<in>S'. f x) + f y"
    by (simp add: S'_def add.commute sum.remove y_prop)
  also have "... \<in> field l" using Suc(1)[of "S'"] card_S' assm field_add_mult disj_un_S by blast
  finally show "(\<Sum>x\<in>S. f x) \<in> field l" by simp
qed

lemma field_comm: "field (a#b#l) = field (b#a#l)"
proof -
  have "x \<in> field (c#d#l) \<Longrightarrow> x \<in> field (d#c#l)" for c d x
  proof -
    assume hyp: "x \<in> field (c#d#l)"
    then obtain q r where x_def: "x = q + r * cpx_sqrt c \<and> q \<in> field (d#l) \<and> r \<in> field (d#l)" by force
    obtain q1 q2 where q_def: "q = q1 + q2 * cpx_sqrt d \<and> q1 \<in> field l \<and> q2 \<in> field l" using x_def by force
    obtain r1 r2 where r_def: "r = r1 + r2 * cpx_sqrt d \<and> r1 \<in> field l \<and> r2 \<in> field l" using x_def by force
    define s where "s = q1 + r1 * cpx_sqrt c"
    define t where "t = q2 + r2 * cpx_sqrt c"
    have are_in: "s \<in> field (c#l) \<and> t \<in> field (c#l)" unfolding s_def t_def using q_def r_def by force
    have "x = s + t * cpx_sqrt d" unfolding s_def t_def using x_def q_def r_def by algebra
    thus "x \<in> field (d#c#l)" using are_in by force
  qed
  hence "field (c#d#l) \<subseteq> field (d#c#l)" for c d by blast
  thus ?thesis by blast
qed

lemma field_idempot1: "field (a#a#l) = field (a#l)"
proof -
  have inc1: "field (a#l) \<subseteq> field (a#a#l)" using field_incr by blast
  have "x \<in> field (a#a#l) \<Longrightarrow> x \<in> field (a#l)" for x
  proof -
    assume hyp: "x \<in> field (a#a#l)"
    then obtain q r where x_def: "x = q + r * cpx_sqrt a \<and> q \<in> field (a#l) \<and> r \<in> field (a#l)" by force
    obtain q1 q2 where q_def: "q = q1 + q2 * cpx_sqrt a \<and> q1 \<in> field l \<and> q2 \<in> field l" using x_def by force
    obtain r1 r2 where r_def: "r = r1 + r2 * cpx_sqrt a \<and> r1 \<in> field l \<and> r2 \<in> field l" using x_def by force
    define s where "s = q1 + a*r2"
    define t where "t = q2 + r1"
    have a_in: "a \<in> field l" using int_in_field by force
    hence are_in: "s \<in> field (l) \<and> t \<in> field (l)" unfolding s_def t_def using q_def r_def 
      field_add_mult by force
    have "x = s + t * cpx_sqrt a" unfolding s_def t_def using x_def q_def r_def
      power2_eq_square[of "cpx_sqrt a"] square_sqrt[of a] by algebra
    thus "x \<in> field (a#l)" using are_in by force
  qed
  hence "field (a#a#l) \<subseteq> field (a#l)" by blast
  thus ?thesis using inc1 by blast
qed

lemma field_idempot: "a \<in> set l \<Longrightarrow> field (a#l) = field l"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons b l)
  note HR = this
  then show ?case
  proof (cases "a=b")
    case True
    then show ?thesis using field_idempot1 by force
  next
    case False
    hence "field (a#l) = field l" using HR by simp
    hence "field (b#a#l) = field (b#l)" by simp
    then show ?thesis using field_comm by simp
  qed
qed

lemma disjoint_field_extensions_no_prime_roots:
  fixes p_l::"int list"
  shows "\<And>(q_s::int set). ((finite q_s \<and> q_s \<noteq> {} \<and> q_s\<inter>(set p_l) = {} \<and> (\<forall>q\<in>q_s. prime q)
 \<and> (\<forall>p\<in>(set p_l). prime p)) \<Longrightarrow> prod (\<lambda>x. cpx_sqrt x) q_s \<notin> field (p_l@[-1]))"
proof (induction p_l)
  case Nil
  note t=this
  hence "\<forall>q\<in>q_s. (cpx_sqrt q) \<in> \<real>" using t unfolding cpx_sqrt_def by (simp add: prime_ge_0_int)
  hence "Im (prod cpx_sqrt q_s) = 0"
    using Real_Vector_Spaces.prod_in_Reals[of q_s "\<lambda>x. cpx_sqrt x"] complex_is_Real_iff by blast
  hence implQ: "(prod cpx_sqrt q_s \<notin> Q) \<Longrightarrow> (prod (\<lambda>x. cpx_sqrt x) q_s \<notin> Qi)"
    using Qi_def complex_is_Real_iff by force
  have "(prod cpx_sqrt q_s)^2 = prod (\<lambda>x. (cpx_sqrt x)^2) q_s"
    using prod_power_distrib by blast 
  hence eq_square: "(prod cpx_sqrt q_s)^2 = prod (\<lambda>x. x) q_s" using square_sqrt by auto
  have "(prod cpx_sqrt q_s \<in> Q) \<Longrightarrow> False"
  proof -
    assume "prod cpx_sqrt q_s \<in> Q"
    then obtain r where r_def: "prod cpx_sqrt q_s = of_rat r" using Q_def by blast
    then obtain a b where ab_def: "(a,b) = quotient_of r" using quotient_of_def
      by (metis eq_snd_iff)
    then have "b * prod cpx_sqrt q_s = a" using r_def
      by (smt (verit) mult_of_int_commute nonzero_eq_divide_eq of_int_eq_0_iff of_rat_divide of_rat_of_int_eq quotient_of_denom_pos quotient_of_div)
    then have eq: "b^2 * prod (\<lambda>x. x) q_s = a^2" using eq_square
      by (metis (no_types, lifting) of_int_eq_iff of_int_mult of_int_power power_mult_distrib)
    obtain q where "q\<in>q_s" using t by blast
    then have "q dvd prod (\<lambda>x. x) q_s" using t by blast
    then have "q dvd a^2" using eq by algebra
    then have qdvda: "q dvd a" using t \<open>q \<in> q_s\<close> prime_dvd_power by blast
    then have "q^2 dvd a^2" by force
    then have q2dvd: "q^2 dvd b^2 * prod (\<lambda>x. x) q_s" using eq by simp
    have "prod (\<lambda>x. x) q_s = prod (\<lambda>x. x) (q_s - {q})*q" using t
      by (metis \<open>q \<in> q_s\<close> mult.commute prod.remove)
    then have eq2: "q*q dvd (b^2 * prod (\<lambda>x. x) (q_s - {q}))*q" using q2dvd by algebra
    have qB1: "q > 1" using t \<open>q\<in>q_s\<close> using prime_gt_1_int by blast
    then have eq3: "q dvd b^2 * prod (\<lambda>x. x) (q_s - {q})" using eq2 by force
    have "coprime q (prod (\<lambda>x. x) (q_s - {q}))" using t
      by (metis DiffD1 Diff_insert_absorb \<open>q \<in> q_s\<close> mk_disjoint_insert primes_coprime prod_coprime_right)
    then have "q dvd b^2" using eq3 coprime_dvd_mult_left_iff by blast
    then have qdvdb:"q dvd b" using t \<open>q \<in> q_s\<close> prime_dvd_power by blast 
    then show "False" using qdvda ab_def qB1 unfolding quotient_of_def
      by (metis ab_def coprime_def quotient_of_coprime zdvd_not_zless zero_less_one)
  qed
  then show ?case using implQ Qi_is_m1 by force
next
  case (Cons a p_l)
  note HR = this
  then show ?case
  proof (cases "a \<in> set p_l")
    case True
    then show ?thesis using field_idempot HR by auto
  next
    case False
    hence "{a} \<noteq> {} \<and> {a} \<inter> set p_l  = {} \<and> finite {a} \<and> (\<forall>x\<in>{a}. prime x) \<and> (\<forall>x\<in>set p_l. prime x)
      \<and> prod cpx_sqrt {a} = cpx_sqrt a" using HR by simp
    hence notin: "cpx_sqrt a \<notin> field (p_l@[-1])" using HR(1)[of "{a}"] by presburger
    have "prod cpx_sqrt q_s \<in> field (a#p_l@[-1]) \<Longrightarrow> False"
    proof -
      assume "prod cpx_sqrt q_s \<in> field (a#p_l@[-1])"
      then obtain x y where xy_def: "prod cpx_sqrt q_s = x + y * cpx_sqrt a \<and> x \<in> field (p_l@[-1]) 
        \<and> y \<in> field (p_l@[-1])" by force
      have sq1: "(prod cpx_sqrt q_s)^2 = prod (\<lambda>x. x) q_s" using square_sqrt
        by (smt (verit) of_int_prod prod.cong prod_power_distrib)
      have prod_in: "prod (\<lambda>x. x) q_s \<in> field (p_l@[-1])" using int_in_field by blast
      have sq2: "(x + y * cpx_sqrt a)^2 = x^2 + a*y^2 + 2*x*y*cpx_sqrt a" using square_sqrt 
        power2_sum[of x "y*cpx_sqrt a"] by (simp add: power_mult_distrib)
      have a_in: "a \<in> field (p_l@[-1]) \<and> 2 \<in> field (p_l@[-1])" using int_in_field by (metis of_int_numeral)
      hence "x^2 + a*y^2 \<in> field (p_l@[-1]) \<and> 2*x*y \<in> field (p_l@[-1])" using xy_def 
        field_square[of x "p_l@[-1]"] field_square[of y "p_l@[-1]"] field_add_mult by presburger
      hence "prod (\<lambda>x. x) q_s - x^2 - a*y^2 \<in> field (p_l@[-1]) \<and> 2*x*y \<in> field (p_l@[-1])"
        using prod_in field_add_mult field_opp apply simp
        by (metis int_in_field power2_eq_square uminus_add_conv_diff xy_def)
      hence coord_in: "(prod (\<lambda>x. x) q_s - x^2 - a*y^2)/(2*x*y) \<in> field (p_l@[-1])" 
        using field_inv_div by blast
      have "prod (\<lambda>x. x) q_s = x^2 + a*y^2 + 2*x*y*cpx_sqrt a" using sq1 sq2 xy_def by simp
      hence "(2*x*y)/(2*x*y) * cpx_sqrt a = (prod (\<lambda>x. x) q_s - x^2 - a*y^2)/(2*x*y)" by force
      hence ecr_cpx: "(2*x*y)/(2*x*y) * cpx_sqrt a \<in> field (p_l@[-1])" using coord_in by simp
      then show ?thesis
      proof (cases "2*x*y=0")
        case True
        note xy_0 = this
        then show ?thesis
        proof (cases "y=0")
          case True
          then show ?thesis using xy_def HR(1)[of q_s] HR(2) by force
        next
          case False
          hence "x = 0" using xy_0 by simp
          hence "prod cpx_sqrt q_s = y*cpx_sqrt a" using xy_def by force
          hence ecr1: "prod cpx_sqrt q_s * cpx_sqrt a = y * a" using square_sqrt[of a] power2_eq_square
            by (metis mult.assoc)
          have "q_s \<inter> {a} = {} \<and> finite q_s \<and> finite {a} \<and> prod cpx_sqrt {a} = cpx_sqrt a" using HR
            by simp
          hence "prod cpx_sqrt (q_s\<union>{a}) = y*a" using ecr1 prod.union_disjoint by metis
          hence in_field: "prod cpx_sqrt (q_s\<union>{a}) \<in> field (p_l@[-1])" using xy_def a_in field_add_mult by simp
          have "q_s\<union>{a} \<noteq> {} \<and> finite (q_s\<union>{a}) \<and> (q_s\<union>{a})\<inter>(set p_l) = {} \<and> (\<forall>z \<in> q_s\<union>{a}. prime z)"
            using HR \<open>{a} \<noteq> {} \<and> {a} \<inter> set p_l = {} \<and> finite {a} \<and> (\<forall>x\<in>{a}. prime x) 
            \<and> (\<forall>x\<in>set p_l. prime x) \<and> prod cpx_sqrt {a} = cpx_sqrt a\<close> by auto
          hence "prod cpx_sqrt (q_s\<union>{a}) \<notin> field (p_l@[-1])" using HR(1)[of "q_s\<union>{a}"] HR(2) by simp
          then show ?thesis using in_field by simp
        qed
      next
        case False
        then show ?thesis using notin ecr_cpx divide_self[of "2*x*y"] by simp
      qed
    qed
    then show ?thesis by (metis append_Cons)
  qed
qed

definition prime_list::"int \<Rightarrow> int list" 
  where "prime_list n = sorted_list_of_set ({p. prime p \<and> p dvd n})"

lemma correct_prime_list: "n \<noteq> 0 \<Longrightarrow> set (prime_list n) = {p. prime p \<and> p dvd n}" 
  unfolding prime_list_def using finite_prime_divisors by simp

lemma field_prod: "field ((a*b)#l) \<subseteq> field (a#b#l)"
proof -
  have "x \<in> field ((a*b)#l) \<Longrightarrow> x \<in> field (a#b#l)" for x
  proof -
    assume hyp: "x \<in> field ((a*b)#l)"
    then obtain q r where x_def: "x = q + r * cpx_sqrt (a*b) \<and> q \<in> field l \<and> r \<in> field l" by force
    consider (pp) "a\<ge>0 \<and> b\<ge>0" | (pm) "a\<ge>0 \<and> b<0" | (mp) "a<0 \<and> b\<ge>0" | (mm) "a<0 \<and> b<0" by linarith
    then show ?thesis
    proof (cases)
      case pp
      hence prod_sqrt: "cpx_sqrt (a*b) = cpx_sqrt a * cpx_sqrt b" unfolding cpx_sqrt_def
        using real_sqrt_mult by fastforce
      have fact: "r*cpx_sqrt b = 0 + r * cpx_sqrt b \<and> 0 \<in> field l \<and> r \<in> field l" 
        using x_def Zero_in_field by simp
      hence "x = q + (r*cpx_sqrt b)*cpx_sqrt a \<and> q \<in> field (b#l) \<and> r*cpx_sqrt b \<in> field (b#l)"
        using x_def field_incr prod_sqrt fact by (auto, blast+)
      then show ?thesis by auto
    next
      case pm
      hence prod_sqrt: "cpx_sqrt (a*b) = cpx_sqrt a * cpx_sqrt b" unfolding cpx_sqrt_def
        using real_sqrt_mult apply (simp add: zero_le_mult_iff)
        by (metis mult_minus_right of_real_mult real_sqrt_mult)
      have fact: "r*cpx_sqrt b = 0 + r * cpx_sqrt b \<and> 0 \<in> field l \<and> r \<in> field l" 
        using x_def Zero_in_field by simp
      hence "x = q + (r*cpx_sqrt b)*cpx_sqrt a \<and> q \<in> field (b#l) \<and> r*cpx_sqrt b \<in> field (b#l)"
        using x_def field_incr prod_sqrt fact by (auto, blast+)
      then show ?thesis by auto
    next
      case mp
      hence prod_sqrt: "cpx_sqrt (a*b) = cpx_sqrt a * cpx_sqrt b" unfolding cpx_sqrt_def
        using real_sqrt_mult apply (simp add: zero_le_mult_iff)
        by (metis mult_minus_left of_real_mult real_sqrt_mult)
      have fact: "r*cpx_sqrt b = 0 + r * cpx_sqrt b \<and> 0 \<in> field l \<and> r \<in> field l" 
        using x_def Zero_in_field by simp
      hence "x = q + (r*cpx_sqrt b)*cpx_sqrt a \<and> q \<in> field (b#l) \<and> r*cpx_sqrt b \<in> field (b#l)"
        using x_def field_incr prod_sqrt fact by (auto, blast+)
      then show ?thesis by auto
    next
      case mm
      hence prod_sqrt: "cpx_sqrt (a*b) = - cpx_sqrt a * cpx_sqrt b" unfolding cpx_sqrt_def
        using real_sqrt_mult apply (simp add: zero_le_mult_iff)
        by (simp add: mult.assoc mult.left_commute real_sqrt_minus)
      have in_field: "y \<in> field (t) \<and> z \<in> field (t) \<Longrightarrow> y + z * cpx_sqrt a \<in> field (a#t)" for y z t by force
      have fact: "-r*cpx_sqrt b = 0 +(-r) * cpx_sqrt b \<and> 0 \<in> field l \<and> r \<in> field l" 
        using x_def Zero_in_field by simp
      hence "x = q + (-r*cpx_sqrt b)*cpx_sqrt a \<and> q \<in> field (b#l) \<and> -r*cpx_sqrt b \<in> field (b#l)"
        using x_def field_incr prod_sqrt field_opp
        by (smt (verit, ccfv_threshold) add.right_neutral field.simps(2) mem_Collect_eq mult.commute
            mult.left_commute mult_minus_right mult_zero_left)
      then show ?thesis using in_field[of q "b#l" "-r*cpx_sqrt b"] by presburger
    qed
  qed
  thus ?thesis by blast
qed

lemma field_add_in: "cpx_sqrt a \<in> field l \<Longrightarrow> field (a#l) = field l"
proof -
  assume hyp: "cpx_sqrt a \<in> field l"
  have "x \<in> field (a#l) \<Longrightarrow> x \<in> field l" for x
  proof -
    assume x_def: "x \<in> field (a#l)"
    then obtain p q where "x = p + q*cpx_sqrt a \<and> p \<in> field l \<and> q \<in> field l" by force
    thus "x \<in> field l" using field_add_mult hyp by presburger
  qed
  thus ?thesis using field_incr by blast
qed

lemma field_add_0: "field (0#l) = field l"
  using field_add_in[of 0 l] Zero_in_field cpx_sqrt_def by force

lemma field_remove_zeros: "\<exists>l'::int list. set l' = set l - {0} \<and> field l' = field l"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  note IH=this
  then show ?case
  proof (cases "a=0")
    case True
    hence field_l: "field (a#l) = field l" using field_add_0 by blast
    obtain l' where "set l' = set l - {0} \<and> field l' = field l"
      using IH by blast
    hence "set l'=  set (a#l) - {0} \<and> field l' = field (a#l)" using True field_l by simp
    then show ?thesis by blast
  next
    case False
    obtain l' where l'_prop: "set l' = set l - {0} \<and> field l' = field l"
      using IH by blast
    hence f: "field (a#l') = field (a#l)" by simp
    have "set (a#l') = set (a#l) - {0}" using False l'_prop by force
    then show ?thesis using f by blast
  qed
qed

lemma sqrt_in_field: "x \<in> set l \<Longrightarrow> cpx_sqrt x \<in> field l"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  note t = this
  then show ?case
  proof (cases "x = a")
    case True
    hence "cpx_sqrt x = 0 + 1*cpx_sqrt a \<and> 0 \<in> field l \<and> 1 \<in> field l" 
      using int_in_field[of 1 l] Zero_in_field by force
    then show ?thesis by force
  next
    case False
    hence "cpx_sqrt x \<in> field l" using t by force
    then show ?thesis using field_incr by force
  qed
qed

lemma field_incr2: "field l \<subseteq> field m \<Longrightarrow> field (a#l) \<subseteq> field (a#m)"
proof -
  assume hyp: "field l \<subseteq> field m"
  have "x \<in> field (a#l) \<Longrightarrow> x \<in> field (a#m)" for x
  proof -
    assume "x \<in> field (a#l)"
    then obtain q r where x_def: "x = q + r * cpx_sqrt a \<and> q \<in> field l \<and> r \<in> field l" by force
    hence "q \<in> field m \<and> r \<in> field m" using hyp by force
    thus "x \<in> field (a#m)" using x_def by force
  qed
  thus "field (a#l) \<subseteq> field (a#m)" by blast
qed

lemma min_set_induct: "(P::int set \<Rightarrow> bool) {} 
  \<Longrightarrow> (\<And>X. \<And>x. finite X \<Longrightarrow> x = Min (X\<union>{x}) \<Longrightarrow> P X \<Longrightarrow> P (X\<union>{x})) \<Longrightarrow> (\<And>X. finite X \<Longrightarrow> P X)"
proof -
  assume empty: "P {}"
  assume induct: "\<And>X. \<And>x. finite X \<Longrightarrow> x = Min (X\<union>{x}) \<Longrightarrow> P X \<Longrightarrow> P (X\<union>{x})"
  have "\<And>X. card X = n \<and> finite X \<Longrightarrow> P X" for n
  proof (induction n)
    case 0
    fix X::"int set"
    assume "card X = 0 \<and> finite X"
    hence "X = {}" using card_0_eq by blast
    then show "P X" using empty by force
  next
    case (Suc n)
    note t = this
    fix X::"int set"
    assume hyp: "card X = Suc n \<and> finite X"
    define Y where "Y = X - {Min X}"
    hence eqX: "X = Y \<union> {Min X}" using hyp 
      by (metis Min_in Un_insert_right card_gt_0_iff insert_Diff sup_bot_right zero_less_Suc)
    hence eqMin: "Min X = Min (Y \<union> {Min X})" by simp
    have finY: "finite Y" using hyp by (simp add: Y_def)
    have "card Y = n" unfolding Y_def using hyp
      by (metis Min_in card_Diff_singleton_if card_gt_0_iff diff_Suc_1 zero_less_Suc)
    then show "P X" using induct[of Y "Min X"] t(1)[of Y] finY eqMin eqX by simp
  qed
  thus "\<And>X. finite X \<Longrightarrow> P X" by presburger
qed

text \<open>Sorting sets\<close>

lemma sorting_set1:
  fixes b::int and C::"int set"
  assumes "\<forall>c\<in>C. b < c" and "finite C"
  shows "sorted_list_of_set ({b}\<union>C) = b#(sorted_list_of_set C)"
  by (smt (verit, best) Diff_insert_absorb Min.union Min_in Min_singleton Un_insert_left assms(1) 
      assms(2) finite.emptyI finite.insertI insert_absorb insert_not_empty min.absorb3 
      sorted_list_of_set_nonempty sup_bot_left)

lemma sorting_set2:
  fixes B::"int set" and C::"int set"
  assumes "finite B"
  shows "(\<forall>b\<in>B. \<forall>c\<in>C. b < c) \<and> finite B \<and> finite C 
    \<Longrightarrow> sorted_list_of_set (B\<union>C) = (sorted_list_of_set B)@(sorted_list_of_set C)"
proof (induction B rule: min_set_induct)
  case 1
  then show ?case by simp
next
  case (2 B x)
  note t = this
  assume hyp: "(\<forall>b\<in>(B\<union>{x}). \<forall>c\<in>C. b < c) \<and> finite (B\<union>{x}) \<and> finite C"
  hence finB: "finite B" by blast
  have BlC: "\<forall>b\<in>B. \<forall>c\<in>C. b < c" using hyp by fast
  then show ?case
  proof (cases "x \<in> B")
    case True
    hence "B\<union>{x} = B" by blast
    then show ?thesis using t finB BlC by simp
  next
    case False
    hence xlB: "\<forall>b\<in>B. x < b" using t by (metis Un_insert_right eq_Min_iff insert_not_empty
          linorder_le_less_linear order_antisym_conv subset_iff subset_insertI sup_bot_right)
    hence xlBC: "\<forall>y\<in>B\<union>C. x < y" using t hyp by fast
    hence xMin: "x = Min (B\<union>{x}) \<and> x = Min (B\<union>{x}\<union>C)" using xlB
      by (metis Min.union Min_in Un_empty hyp insert_not_empty min.absorb3 sup_bot_right t(2))
    have "B = B\<union>{x} - {x} \<and> B\<union>C = B\<union>{x}\<union>C - {x}" using xlB xlBC by fast
    hence "sorted_list_of_set (B\<union>{x}) = x#(sorted_list_of_set B)
      \<and> sorted_list_of_set (B\<union>{x}\<union>C) = x#(sorted_list_of_set (B\<union>C))" using xMin
      by (metis hyp infinite_Un insert_not_empty sorted_list_of_set_nonempty sup_eq_bot_iff)
    then show ?thesis using t by simp
  qed
next
  case 3
  then show ?case using assms by simp
qed

corollary sorting_set3:
  fixes B::"int set" and C::"int set"
  assumes "\<forall>b\<in>B. \<forall>c\<in>C. b < c" and "finite B" and "finite C"
  shows "sorted_list_of_set (B\<union>C) = (sorted_list_of_set B)@(sorted_list_of_set C)"
  using sorting_set2 assms by blast

lemma min_mset_induct: "(P::int multiset \<Rightarrow> bool) {#} 
  \<Longrightarrow> (\<And>X. \<And>x. x = Min_mset (X + {#x#}) \<Longrightarrow> P X \<Longrightarrow> P (X + {#x#})) \<Longrightarrow> (\<And>X. P X)"
proof -
  assume empty: "P {#}"
  assume induct: "\<And>X. \<And>x. x = Min_mset (X + {#x#}) \<Longrightarrow> P X \<Longrightarrow> P (X + {#x#})"
  have "\<And>X. size X = n  \<Longrightarrow> P X" for n
  proof (induction n)
    case 0
    fix X::"int multiset"
    assume "size X = 0"
    hence "X = {#}" by blast
    then show "P X" using empty by force
  next
    case (Suc n)
    note t = this
    fix X::"int multiset"
    assume hyp: "size X = Suc n"
    hence "set_mset X \<noteq> {}" by force
    hence min_in: "Min_mset X \<in># X" by simp
    define Y where "Y = X - {#(Min_mset X)#}"
    hence eqX: "X = Y + {#(Min_mset X)#}" using min_in by force
    hence eqMin: "Min_mset X = Min_mset (Y + {#(Min_mset X)#})" by simp
    have "size Y = n" unfolding Y_def using hyp eqX
      by (metis Suc_inject min_in size_Suc_Diff1)
    then show "P X" using induct[of "Min_mset X" Y] t(1)[of Y] eqMin eqX by simp
  qed
  thus "\<And>X. P X" by presburger
qed

lemma field_prod2: "field ((prod_mset A)#l) \<subseteq> field ((sorted_list_of_set (set_mset A))@l)"
proof (induction A rule: min_mset_induct)
  case 1
  have "of_int 1 = 1" by simp
  hence one_in: "1 \<in> field l" using int_in_field by metis
  have "1 = cpx_sqrt 1" unfolding cpx_sqrt_def by fastforce
  hence "field (1#l) = field l" using one_in field_add_in by presburger
  then show ?case by fastforce
next
  case (2 A x)
  note HR = this
  then show ?case
  proof (cases "x \<in># A")
    case True
    hence eq1: "sorted_list_of_set (set_mset A) = sorted_list_of_set (set_mset (add_mset x A))"
      by (simp add: insert_absorb)
    have add_eq: "add_mset x A = A + {#x#}" by simp
    have "field ((prod_mset (add_mset x A))#l) \<subseteq> field (x#(prod_mset A)#l)" 
      using field_prod[of x "prod_mset A" l] by simp
    hence "field ((prod_mset (add_mset x A))#l) \<subseteq> field (x#(sorted_list_of_set (set_mset A))@l)"
      using field_incr2[of "(prod_mset A)#l" "(sorted_list_of_set (set_mset A))@l" x] HR by fast
    hence "field ((prod_mset (add_mset x A))#l) \<subseteq> field ((sorted_list_of_set (set_mset A))@l)"
      using field_idempot True by simp
    then show ?thesis using eq1 add_eq by argo
  next
    case False
    hence "x = Min_mset (A + {#x#}) \<and> x \<notin> set_mset A" using HR by linarith
    hence "set_mset A = set_mset (A + {#x#}) - {x} \<and> x = Min (set_mset (A + {#x#}))" by simp
    hence "sorted_list_of_set (set_mset (A + {#x#})) = x#(sorted_list_of_set (set_mset A))"
      by (metis finite_set_mset multi_self_add_other_not_self set_mset_eq_empty_iff 
         sorted_list_of_set_nonempty union_eq_empty)
    hence eq_sort: "sorted_list_of_set (set_mset (A + {#x#}))@l = x#(sorted_list_of_set (set_mset A))@l"
      by force
    have "prod_mset (A + {#x#}) = x * prod_mset A" by simp
    then show ?thesis using field_prod[of x "prod_mset A" l] eq_sort HR(2) 
      field_incr2[of "prod_mset A # l" "sorted_list_of_set (set_mset A) @ l" x] by simp
  qed
qed

lemma field_n_in_field_prime:
  fixes n::int and l::"int list"
  assumes "n \<noteq> 0"
  shows "field (n#l) \<subseteq> field ((-1)#(prime_list n)@l)"
proof -
  obtain A where A_def: "normalize (prod_mset A) = normalize n \<and> (\<forall>x\<in>#A. prime x)" 
    using assms  by (meson prime_factorization_exists')
  hence "abs (prod_mset A) = abs n" by simp
  then obtain s where s_def: "s \<in> {1,-1} \<and> n = s * prod_mset A"
    by (metis abs_eq_iff comm_monoid_mult_class.mult_1 insert_iff mult_minus1)
  hence "n = prod_mset (add_mset s A)" by simp
  hence "field (n#l) \<subseteq> field ((sorted_list_of_set (set_mset (add_mset s A)))@l)" 
    using field_prod2 by blast
  hence field_inc: "field (n#l) \<subseteq> field ((sorted_list_of_set ({s}\<union>(set_mset A)))@l)" by auto
  have all_fin: "finite {s} \<and> finite (set_mset A)" by fast
  have "\<forall>x \<in># A. x > s" using A_def s_def
    by (metis abs_if_raw abs_neg_one dual_order.strict_trans ex_in_conv 
       insert_iff prime_gt_0_int prime_gt_1_int)
  hence "\<forall>x \<in> set_mset A. \<forall>y \<in> {s}. x > y" by blast
  hence "sorted_list_of_set ({s}\<union>(set_mset A)) 
    = (sorted_list_of_set {s})@(sorted_list_of_set (set_mset A))" using all_fin sorting_set3 by metis
  hence "sorted_list_of_set ({s}\<union>(set_mset A)) = s#(sorted_list_of_set (set_mset A))" by simp
  hence "(sorted_list_of_set (set_mset (add_mset s A)))@l = s#(sorted_list_of_set (set_mset A))@l" 
    by simp
  hence field_inc2: "field (n#l) \<subseteq> field (s#(sorted_list_of_set (set_mset A))@l)" 
    using field_inc by simp
  have "set_mset A = {p. prime p \<and> p dvd n}"
  proof -
    have "p \<in> set_mset A \<Longrightarrow> p \<in> {p. prime p \<and> p dvd n}" for p
    proof -
      assume p_def: "p \<in> set_mset A"
      define B where "B = A - {#p#}"
      hence "A = B + {#p#}" using p_def by simp
      hence "prod_mset A = prod_mset B * p" by simp
      hence "n = s*prod_mset B * p" using s_def by simp
      hence "p dvd n \<and> prime p" using A_def p_def by simp
      thus "p \<in> {p. prime p \<and> p dvd n}" by blast
    qed
    hence inc1: "set_mset A \<subseteq> {p. prime p \<and> p dvd n}" by blast
    have "{p. prime p \<and> p dvd n} \<subseteq> set_mset A"
    proof safe
      fix p assume p: "prime p" and dvd: "p dvd n"
      from dvd have "p dvd normalize n" by simp
      also from A_def have "normalize n = normalize (prod_mset A)" by simp
      finally have "p dvd prod_mset A"
        by simp
      thus  "p \<in># A" using p A_def prime_dvd_prod_mset_primes_iff by blast
    qed
    thus ?thesis using inc1 by blast
  qed
  hence field_inc3: "field (n#l) \<subseteq> field (s#(prime_list n)@l)" using field_inc2 prime_list_def by simp
  thus ?thesis
  proof (cases "s = -1")
    case True
    then show ?thesis using field_inc3 by simp
  next
    case False
    have "of_int 1 = 1" by simp
    hence one_in: "1 \<in> field ((prime_list n)@l)" using int_in_field by metis
    have sqrt_1: "cpx_sqrt 1 = 1" using cpx_sqrt_def by force
    have "s = 1" using False s_def by simp
    hence "field (s#(prime_list n)@l) = field ((prime_list n)@l)" 
      using field_add_in one_in sqrt_1 by presburger
    then show ?thesis using field_incr field_inc3 by fast
  qed
qed

lemma field_n_in_field_prime2:
  fixes n::int and l::"int list"
  shows "field (n#l) \<subseteq> field ((-1)#(prime_list n)@l)"
proof (cases "n=0")
  case True
  hence eqn: "{p. prime p \<and> p dvd n} = {p. prime p}" by simp
  have "finite {p::int. prime p} \<Longrightarrow> False"
  proof -
    assume hyp: "finite {p::int. prime p}"
    define M where "M = Max {p::int. prime p}"
    hence "\<forall>p::int. prime p \<longrightarrow> p \<le> M" using hyp by fastforce
    hence "\<forall>p::nat. prime p \<longrightarrow> p \<le> nat M" using prime_int_nat_transfer
      by (metis dual_order.trans int_eq_iff le_nat_iff)
    hence "finite {p::nat. prime p}" using finite_nat_set_iff_bounded_le by auto
    then show ?thesis by (simp add: primes_infinite)
  qed
  hence "infinite {p. prime p \<and> p dvd n}" using eqn by presburger
  hence primen: "prime_list n = []" unfolding prime_list_def by fastforce
  have "cpx_sqrt n = 0" unfolding cpx_sqrt_def using True by simp
  hence "field (n#l) = field l" using Zero_in_field field_add_in by presburger
  thus ?thesis using field_incr primen by simp
next
  case False
  then show ?thesis using field_n_in_field_prime by simp
qed

fun prime_list_list::"int list \<Rightarrow> int list" where
"prime_list_list [] = []" |
"prime_list_list (a#l) = (prime_list a)@(prime_list_list l)"

lemma field_list_in_field_primes:
  fixes l::"int list"
  shows "field (l) \<subseteq> field ((prime_list_list l)@[-1])"
proof (induction l)
  case Nil
  then show ?case using field_incr by fastforce
next
  case (Cons a l)
  note t = this
  have "field ((-1)#prime_list a @ prime_list_list l@[-1])
     = field (prime_list a @ prime_list_list l@[-1])" using field_idempot by simp
  then show ?case using field_n_in_field_prime2[of a "prime_list_list l @ [-1]"]
      field_incr2[of l "prime_list_list l @ [-1]" a] t by simp
qed

text \<open>Corollary\<close>

corollary root_p_not_in_field_extension:
  fixes B::"int list" and p::int
  assumes "prime p" and "\<forall>b\<in>(set B). \<not> p dvd b"
  shows "cpx_sqrt p \<notin> field B"
proof -
  have "(\<forall>d\<in>(set D). \<not> p dvd d) \<Longrightarrow> p \<notin> set (prime_list_list D)" for D
  proof (induction D)
    case Nil
    then show ?case by simp
  next
    case (Cons a D)
    note t = this
    assume hyp: "\<forall>d\<in>(set (a#D)). \<not> p dvd d"
    hence hypD: "\<forall>d\<in>(set D). \<not> p dvd d" by simp
    have an0: "a \<noteq> 0" using hyp by force
    have "\<not> p dvd a" using hyp by simp
    hence "d dvd a \<Longrightarrow> \<not> p dvd d" for d by fastforce
    hence "d dvd a \<Longrightarrow> p \<noteq> d" for d by force
    hence "p \<notin> set (prime_list a)" using an0 correct_prime_list by blast
    then show ?case using hypD t by simp
  qed
  hence "p \<notin> set (prime_list_list B)" using assms by simp
  hence p_notin: "{p} \<inter> (set (prime_list_list B)) = {} \<and> {p} \<noteq> {} \<and> finite {p} \<and> (\<forall>q\<in>{p}. prime q)
    \<and> prod cpx_sqrt {p} = cpx_sqrt p" using assms by force
  have "\<forall>d\<in>(set (prime_list_list D)). prime d" for D
  proof (induction D)
    case Nil
    then show ?case by simp
  next
    case (Cons a D)
    have "set (prime_list_list (a#D)) = set (prime_list a) \<union> (set (prime_list_list D))" by simp
    then show ?case unfolding prime_list_def by (metis (no_types, lifting) Un_iff local.Cons 
      mem_Collect_eq self_append_conv2 set_append sorted_list_of_set.fold_insort_key.infinite 
      sorted_list_of_set.set_sorted_key_list_of_set)
  qed
  hence "\<forall>b\<in>(set (prime_list_list B)). prime b" by simp
  thus ?thesis 
    using disjoint_field_extensions_no_prime_roots[of "{p}" "prime_list_list B"] field_list_in_field_primes[of B] p_notin by auto
qed

lemma sqrt_int_smaller:
  fixes a::int assumes "a\<ge>0"
  shows "sqrt a \<le> a"
proof (cases "a=0")
  case True
  then show ?thesis by force
next
  case False
  hence "a\<ge>1" using assms by simp
  then show ?thesis by (simp add: power2_eq_square real_le_lsqrt)
qed

end
