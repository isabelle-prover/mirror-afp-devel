(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Application: Complexity of Matrix Orderings\<close>

text \<open>In this theory we provide executable tests which guarantee polynomial
  growth of powers of matrices, and moreover a degree of the polynomial is returned.

  We further provide various carriers which can be used for matrix interpretations.\<close>

theory Matrix_Complexity 
imports
  Jordan_Normal_Form_Triangular
  Matrix_Comparison
  Complexity_Carrier
  "../Matrix/Utility"
  Matrix_Show
  Arctic_Show
begin

subsection \<open>Locales for Carriers of Matrix Interpretations and Polynomial Orders\<close>

locale matrix_carrier = SN_one_mono_ordered_semiring_1 d gt
  for gt :: "'a :: {show,ordered_semiring_1} \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50) and d :: "'a"

locale mono_matrix_carrier = complexity_one_mono_ordered_semiring_1 gt d bound
  for gt :: "'a :: {show,large_real_ordered_semiring_1} \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50) and d :: 'a
  and bound :: "'a \<Rightarrow> nat" 
+ fixes mono :: "'a \<Rightarrow> bool"
  assumes mono: "\<And> x y z. mono x \<Longrightarrow> y \<succ> z \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x * y \<succ> x * z"


text \<open>The weak version make comparison with $>$ and then synthesize a suitable
  $\delta$-ordering by choosing the least difference in the finite set of
  comparisons.\<close>

locale weak_complexity_linear_poly_order_carrier = 
  fixes weak_gt :: "'a :: {large_real_ordered_semiring_1,show} \<Rightarrow> 'a \<Rightarrow> bool"
   and  default :: "'a"
   and  mono :: "'a \<Rightarrow> bool"
  assumes weak_gt_mono: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> weak_gt x y 
  \<Longrightarrow> \<exists> gt bound. mono_matrix_carrier gt default bound mono \<and> (\<forall> x y. (x,y) \<in> set xys \<longrightarrow> gt x y)"
begin

abbreviation weak_mat_gt :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "weak_mat_gt \<equiv> mat_gt weak_gt"

lemma weak_mat_gt_mono: assumes sd_n: "sd \<le> n" and
    orient: "\<And> A B. A \<in> carrier\<^sub>m n n \<Longrightarrow> B \<in> carrier\<^sub>m n n \<Longrightarrow> (A,B) \<in> set ABs \<Longrightarrow> weak_mat_gt sd A B"
   shows "\<exists> gt bound. mono_matrix_carrier gt default bound mono 
   \<and> (\<forall> A B. A \<in> carrier\<^sub>m n n \<longrightarrow> B \<in> carrier\<^sub>m n n \<longrightarrow> (A, B) \<in> set ABs \<longrightarrow> mat_gt gt sd A B)"
proof -
  let ?n = "[0 ..< n]"
  let ?m1x = "[ A $$ (i,j) . A <- map fst ABs, i <- ?n, j <- ?n]"
  let ?m2y = "[ B $$ (i,j) . B <- map snd ABs, i <- ?n, j <- ?n]"
  let ?pairs = "concat (map (\<lambda> x. map (\<lambda> y. (x,y)) ?m2y) ?m1x)"
  let ?strict = "filter (\<lambda> (x,y). weak_gt x y) ?pairs"
  have "\<forall> x y. (x,y) \<in> set ?strict \<longrightarrow> weak_gt x y" by auto
  from weak_gt_mono[OF this] obtain gt bound where order: "mono_matrix_carrier gt default bound mono" 
    and orient2: "\<And> x y. (x, y) \<in> set ?strict \<Longrightarrow> gt x y" by auto
  show ?thesis
  proof (intro exI allI conjI impI, rule order)
    fix A B
    assume A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n n"
      and AB: "(A, B) \<in> set ABs"          
    from orient[OF this] have "mat_gt weak_gt sd A B" by auto
    from mat_gtD[OF this] obtain i j where
      ge: "A \<ge>\<^sub>m B" and ij: "i < sd" "j < sd" and wgt: "weak_gt (A $$ (i,j)) (B $$ (i,j))"
      by auto
    from ij `sd \<le> n` have ij': "i < n" "j < n" by auto
    have gt: "gt (A $$ (i,j)) (B $$ (i,j))"
      by (rule orient2, insert ij' AB wgt, force)
    show "mat_gt gt sd A B" using ij gt ge by auto
  qed
qed
end

sublocale mono_matrix_carrier \<subseteq> SN_strict_mono_ordered_semiring_1 d gt mono
proof
  show "SN {(x,y). y \<ge> 0 \<and> x \<succ> y}" 
    unfolding SN_def
    by (intro allI deriv_bound_SN_on[OF bound])
qed (rule mono)

sublocale mono_matrix_carrier \<subseteq> matrix_carrier ..

subsection \<open>The Integers as Carrier\<close>

lemma int_complexity:
  "mono_matrix_carrier (op > :: int \<Rightarrow> int \<Rightarrow> bool) 1 nat int_mono"
proof (unfold_locales)
  fix x
  let ?R = "{(x, y). 0 \<le> (y :: int) \<and> y < x}" 
  show "deriv_bound ?R x (nat x)"
    unfolding deriv_bound_def
  proof
    assume "(\<exists> y. (x,y) \<in> ?R ^^ Suc (nat x))"
    then obtain y where xy: "(x,y) \<in> ?R ^^ Suc (nat x)" ..
    from xy have y: "0 \<le> y" by auto
    obtain n where n: "n = Suc (nat x)" by auto
    from xy[unfolded n[symmetric]]
    have "x \<ge> y + int n"
    proof (induct n arbitrary: x y)
      case 0 thus ?case by auto
    next
      case (Suc n)
      from Suc(2) obtain z where xz: "(x,z) \<in> ?R ^^ n" and zy: "(z,y) \<in> ?R"
        by auto
      from Suc(1)[OF xz] have le: "z + int n \<le> x" .
      from zy have le2: "y + 1 \<le> z" by simp
      with le show ?case by auto
    qed
    with y have nx: "int n \<le> x" by simp
    from nx have x0: "x \<ge> 0" by simp
    with nx n
    show False by simp
  qed      
qed (insert int_SN.mono, auto)

lemma int_weak_complexity:
  "weak_complexity_linear_poly_order_carrier op > 1 int_mono"
  by (unfold_locales, intro exI[of _ "op >"] exI[of _ nat] conjI, rule int_complexity, auto)

subsection \<open>The Rational and Real Numbers as Carrier\<close>

definition delta_bound :: "'a :: floor_ceiling \<Rightarrow> 'a \<Rightarrow> nat"
where
  "delta_bound d x = nat (ceiling (x * of_int (ceiling (1 / d))))"

lemma delta_complexity:
  assumes d0: "d > 0" and d1: "d \<le> def" 
  shows "mono_matrix_carrier (delta_gt d) def (delta_bound d) delta_mono"
proof -
  from d0 have d00: "0 \<le> d" by simp
  def N \<equiv> "ceiling (1 / d)"
  let ?N = "of_int N :: 'a"
  from d0 have "1 / d > 0" by (auto simp: field_simps)
  with ceiling_correct[of "1 / d"] have Nd: "1 / d \<le> ?N" and N: "N > 0" unfolding N_def by auto
  let ?nat = "\<lambda> x. nat (ceiling (x * ?N))"
  let ?gt = "delta_gt d"
  have nn: "delta_bound d = ?nat" unfolding fun_eq_iff N_def by (simp add: delta_bound_def)
  from delta_interpretation[OF d0 d1]
  interpret SN_strict_mono_ordered_semiring_1 "def" ?gt delta_mono .
  show ?thesis unfolding nn
  proof(unfold_locales)
    show "?nat 0 = 0" by auto
  next
    fix x y :: 'a
    assume xy: "x \<ge> y"
    show "?nat x \<ge> ?nat y" 
      by (rule nat_mono, rule ceiling_mono, insert xy N, auto simp: field_simps)
  next
    have "1 \<le> nat 1" by simp
    also have "... \<le> ?nat 1"
    proof (rule nat_mono)
      have "1 = ceiling (1 :: rat)" by simp
      also have "... \<le> ceiling (1 * ?N)" using N by simp
      finally show "1 \<le> ceiling (1 * ?N)" .
    qed
    finally show "1 \<le> ?nat 1" .
  next
    fix x y :: 'a
    have "ceiling ((x + y) * ?N) = ceiling (x * ?N + y * ?N)" by (simp add: field_simps)
    also have "... \<le> ceiling (x * ?N) + ceiling (y * ?N)" by (rule ceiling_add_le)
    finally show "?nat (x + y) \<le> ?nat x + ?nat y" by auto
  next
    fix x :: 'a and n :: nat
    assume x: "0 \<le> x" 
    interpret mono_matrix_carrier "op >" 1 nat int_mono by (rule int_complexity)
    have "?nat (x + of_nat n) = nat (ceiling (x * ?N + of_nat n * ?N))" 
      by (simp add: field_simps)
    also have id: "of_nat n * ?N = of_int (of_nat (n * nat N))" using N by (simp add: field_simps of_nat_mult)
    also have "ceiling (x * ?N + of_int (of_nat (n * nat N))) = ceiling (x * ?N) + of_nat (n * nat N)" unfolding ceiling_add_of_int ..
    also have "nat (ceiling (x * ?N) + of_nat (n * nat N)) = ?nat x + nat (int (n * nat N))"
    proof (rule bound_plus_of_nat)
      have "x * ?N \<ge> 0" 
        by (rule mult_nonneg_nonneg, insert x N, auto)
      thus "ceiling (x * ?N) \<ge> 0" by auto
    qed 
    also have "(nat (int (n * nat N))) = n * nat N" by (simp add: nat_mult_distrib)
    also have "n * nat N = ?nat (of_nat n)" using N by (metis id ceiling_of_int nat_int)
    finally
    show "?nat (x + of_nat n) = ?nat x + ?nat (of_nat n)" .
  next
    fix x y z :: 'a
    assume *: "delta_mono x" "delta_gt d y z" and x: "0 \<le> x"
    from mono[OF * x]
    show "delta_gt d (x * y) (x * z)" .
  next
    fix x :: 'a
    let ?R = "{(x,y). 0 \<le> y \<and> ?gt x y}"
    show "deriv_bound ?R x (?nat x)" unfolding deriv_bound_def
    proof
      assume "(\<exists> y. (x,y) \<in> ?R ^^ Suc (?nat x))"
      then obtain y where xy: "(x,y) \<in> ?R ^^ Suc (?nat x)" ..
      from xy have y: "0 \<le> y" by auto
      obtain n where n: "n = Suc (?nat x)" by auto
      from xy[unfolded n[symmetric]]
      have "x \<ge> y + d * of_nat n"
      proof (induct n arbitrary: x y)
        case 0 thus ?case by auto
      next
        case (Suc n)
        from Suc(2) obtain z where xz: "(x,z) \<in> ?R ^^ n" and zy: "(z,y) \<in> ?R"
          by auto
        from Suc(1)[OF xz] have le: "z + d * of_nat n \<le> x" .
        from zy[unfolded delta_gt_def] have le2: "y + d \<le> z" by simp
        with le show ?case by (auto simp: field_simps)
      qed
      with y have nx: "d * of_nat n \<le> x" by simp
      have "0 \<le> d * of_nat n" by (rule mult_nonneg_nonneg, insert d00, auto)
      with nx have x0: "x \<ge> 0" by auto
      have xd0: "0 \<le> x / d"
        by (rule divide_nonneg_pos[OF x0 d0])
      from nx[unfolded n]      
      have "d + d * of_nat (?nat x) \<le> x" by (simp add: field_simps)
      with d0 have less: "d * of_nat (?nat x) < x" by simp
      from Nd d0 have "1 \<le> d * ?N" by (auto simp: field_simps)
      from mult_left_mono[OF this x0]
      have "x \<le> d * (x * ?N)" by (simp add: ac_simps)
      also have "\<dots> \<le> d * of_nat (?nat x)"
      proof (rule mult_left_mono[OF _ d00])
        show "x * ?N \<le> of_nat (nat \<lceil>x * ?N\<rceil>)" using x0 ceiling_correct[of "x * ?N"] 
          by (metis int_nat_eq le_cases of_int_0_le_iff of_int_of_nat_eq order_trans)
      qed
      also have "\<dots> < x" using less .
      finally show False by simp
    qed
  qed 
qed


lemma delta_weak_complexity_carrier:
  assumes d0: "def > 0" 
  shows "weak_complexity_linear_poly_order_carrier op > def delta_mono"
proof
  fix xys :: "('a \<times> 'a) list"
  assume ass: "\<forall>x y. (x, y) \<in> set xys \<longrightarrow> y < x"
  let ?cs = "map (\<lambda> (x,y). x - y) xys"
  let ?ds = "def # ?cs"
  def d \<equiv> "Min (set ?ds)"
  have d: "d \<le> def" and dcs: "\<And> x. x \<in> set ?cs \<Longrightarrow> d \<le> x" unfolding d_def by auto
  have "d \<in> set ?ds" unfolding d_def by (rule Min_in, auto)
  hence "d = def \<or> d \<in> set ?cs" by auto
  hence d0: "d > 0"
    by (cases, insert d0 ass, auto simp: field_simps)
  show "\<exists>gt bound. mono_matrix_carrier gt def bound delta_mono \<and> (\<forall>x y. (x, y) \<in> set xys \<longrightarrow> gt x y)"
    by (intro exI conjI, rule delta_complexity[OF d0 d], insert dcs, force simp: delta_gt_def)
qed

subsection \<open>The Arctic Numbers as Carrier\<close>

lemma arctic_delta_weak_carrier:
  "weak_SN_both_mono_ordered_semiring_1 weak_gt_arctic_delta 1 pos_arctic_delta" ..

lemma arctic_weak_carrier:
  "weak_SN_both_mono_ordered_semiring_1 op > 1 pos_arctic"
proof -
  have SN: "SN_both_mono_ordered_semiring_1 1 (op >) pos_arctic" ..
  show ?thesis
    by (unfold_locales, intro conjI exI, rule SN, auto)
qed


subsection \<open>Estimations of Matrix Powers\<close>

text \<open>We connect the strict ordering @{const mat_gt} with @{const norm_bound} 
  where the latter can be approximated via @{thm [source] compute_jnf_complexity} and 
  @{thm [source] counting_ones_complexity}. Since @{thm [source] compute_jnf_complexity} provides sharper bounds,
  we only use this one.\<close>

definition mat_estimate_complexity :: "nat \<Rightarrow> 'a :: large_real_ordered_semiring_1 mat \<Rightarrow> nat option" where
  "mat_estimate_complexity n A = (let B = mat\<^sub>\<real> A in (if A \<in> carrier\<^sub>m n n \<and> upper_triangular A
     then let jnf = triangular_to_jnf_vector B
       in if (\<forall> na \<in> set jnf. norm (snd na) \<le> 1) then Some (max_list (map fst (filter (\<lambda> na. norm (snd na) = 1) jnf)) - 1) else None
     else None))"

lemma mat_estimate_complexity_norm_bound: assumes *: "mat_estimate_complexity n A = Some d"
  shows "\<exists> c1 c2. \<forall> k. norm_bound (mat\<^sub>\<real> A ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)"
proof -
  let ?B = "mat\<^sub>\<real> A"
  let ?jnf = "triangular_to_jnf_vector ?B"
  note * = *[unfolded mat_estimate_complexity_def Let_def]
  from * have B: "?B \<in> carrier\<^sub>m n n" and ut: "upper_triangular ?B" 
    and 1: "\<And> n a. (n,a) \<in> set ?jnf \<Longrightarrow> norm a \<le> 1"
    and d: "d = max_list (map fst (filter (\<lambda> na. norm (snd na) = 1) ?jnf)) - 1" 
    by (auto split: if_splits simp: Let_def real_zero upper_triangular_def)
  show ?thesis unfolding d
    by (rule compute_jnf_complexity[OF B ut 1 max_list], force+)
qed

context
  fixes A B C :: "'a :: large_real_ordered_semiring_1 mat" and n d :: nat
  assumes *: "mat_estimate_complexity n A = Some d"
  and A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n n" and C: "C \<in> carrier\<^sub>m n n"
begin

lemma mat_estimate_complexity_norm_bound_prod: 
  "\<exists> c. \<forall> k. k > 0 \<longrightarrow> norm_bound (mat\<^sub>\<real> B \<otimes>\<^sub>m (mat\<^sub>\<real> A ^\<^sub>m k \<otimes>\<^sub>m mat\<^sub>\<real> C)) (c * of_nat k ^ d)"
proof -
  let ?R = "mat\<^sub>\<real>"
  let ?A = "?R A"
  let ?B = "?R B"
  let ?C = "?R C"
  from mat_estimate_complexity_norm_bound[OF *]
  obtain c1 c2 where bnd: "\<And> k. norm_bound (?A ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)" by auto
  def c \<equiv> "(max c1 0) + (max c2 0)"
  from norm_bound_max[of ?B] obtain nb where nb: "norm_bound ?B nb" by auto
  from norm_bound_max[of ?C] obtain nc where nc: "norm_bound ?C nc" by auto
  let ?n = "of_nat n :: real"
  def b \<equiv> "nb * nc * ?n * ?n * c"
  {
    fix k
    assume "k > (0 :: nat)"
    let ?k = "of_nat k :: real"
    from bnd[of k] have "norm_bound (?A ^\<^sub>m k) (c1 + c2 * ?k ^ d)" .
    have "c1 \<le> (max c1 0) * 1 ^ d" by auto
    also have "\<dots> \<le> (max c1 0) * ?k ^ d"
      by (rule mult_left_mono, insert `k > 0`, auto)
    also have "\<dots> + c2 * ?k ^ d \<le> c * ?k ^ d"
      unfolding c_def by (auto simp: field_simps intro: mult_right_mono)
    finally have "c1 + c2 * of_nat k ^ d \<le> c * of_nat k ^ d" by auto
    with bnd[of k] have "norm_bound (?A ^\<^sub>m k) (c * of_nat k ^ d)"
      unfolding norm_bound_def by force
    from norm_bound_mult[OF mat_pow_closed _ this nc]
    have "norm_bound (?A ^\<^sub>m k \<otimes>\<^sub>m ?C) (c * ?k ^ d * nc * ?n)" using A C by auto
    from norm_bound_mult[OF _ mat_mult_mat_closed[OF mat_pow_closed] nb this]
    have "norm_bound (?B \<otimes>\<^sub>m (?A ^\<^sub>m k \<otimes>\<^sub>m ?C)) (b * ?k ^ d)" unfolding b_def using A B C
      by (auto simp: ac_simps)
  } note bnd = this
  thus ?thesis by auto
qed

text \<open>This is the main result for real valued matrices.\<close>

lemma mat_estimate_complexity_norm_mat_sum_prod: 
  "\<exists> c. \<forall> k. k > 0 \<longrightarrow> norm (mat_sum (mat\<^sub>\<real> B \<otimes>\<^sub>m (mat\<^sub>\<real> A ^\<^sub>m k \<otimes>\<^sub>m mat\<^sub>\<real> C))) \<le> (c * of_nat k ^ d)"
proof -
  let ?R = "mat\<^sub>\<real>"
  let ?A = "?R A"
  let ?B = "?R B"
  let ?C = "?R C"
  from mat_estimate_complexity_norm_bound_prod obtain c
  where bnd: "\<And> k. k > 0 \<Longrightarrow> norm_bound (?B \<otimes>\<^sub>m (?A ^\<^sub>m k \<otimes>\<^sub>m ?C)) (c * of_nat k ^ d)" by auto
  let ?n = "of_nat n :: real"
  def b \<equiv> "?n * ?n * c" 
  {
    fix k
    let ?nn = "{0 ..< n}"
    let ?g = "\<lambda> i. c * of_nat k ^ d"
    assume "k > (0 :: nat)"    
    from bnd[OF this] have bnd: "norm_bound (?B \<otimes>\<^sub>m (?A ^\<^sub>m k \<otimes>\<^sub>m ?C)) (c * of_nat k ^ d)" .
    have "norm (mat_sum (?B \<otimes>\<^sub>m (?A ^\<^sub>m k \<otimes>\<^sub>m ?C))) \<le> setsum ?g (?nn \<times> ?nn)"
      unfolding mat_sum_def
      by (rule order_trans[OF setsum_norm_le[of _ _ ?g]],
      insert bnd A B C, auto simp: norm_bound_def)
    also have "\<dots> = b * of_nat k ^ d" unfolding b_def setsum_constant
      by (simp add: ac_simps of_nat_mult)
    finally have "norm (mat_sum (?B \<otimes>\<^sub>m (?A ^\<^sub>m k \<otimes>\<^sub>m ?C))) \<le> b * of_nat k ^ d" by auto
  }
  thus ?thesis by auto
qed

text \<open>And via conversion, it also holds for matrices over the intended semiring.\<close>

lemma mat_estimate_complexity_mat_sum_prod: 
  "\<exists> c. \<forall> k. k > 0 \<longrightarrow> mat_sum (B \<otimes>\<^sub>m (A ^\<^sub>m k \<otimes>\<^sub>m C)) \<le> (c * of_nat k ^ d)"
proof -  
  from mat_estimate_complexity_norm_mat_sum_prod obtain c where 
    bnd: "\<And> k. k > 0 \<Longrightarrow> norm (mat_sum (mat\<^sub>\<real> B \<otimes>\<^sub>m (mat\<^sub>\<real> A ^\<^sub>m k \<otimes>\<^sub>m mat\<^sub>\<real> C))) \<le> (c * of_nat k ^ d)"
    by auto
  note mat_real_conv = 
    real_embedding.hom_mat_sum 
    real_embedding.mat_hom_pow [of _ n]
    real_embedding.mat_hom_mult[of _ n n]
  {
    fix k
    assume "k > (0 :: nat)"
    let ?sum = "mat_sum (B \<otimes>\<^sub>m (A ^\<^sub>m k \<otimes>\<^sub>m C))"
    have Ak: "A ^\<^sub>m k \<in> carrier\<^sub>m n n" using A by simp
    have AkC: "A ^\<^sub>m k \<otimes>\<^sub>m C \<in> carrier\<^sub>m n n" using Ak C by simp
    let ?ck = "c * of_nat k ^ d"
    let ?cck = "of_int \<lceil>c\<rceil> * of_nat k ^ d :: real"
    from bnd[OF `k > 0`] have "mat_sum (mat\<^sub>\<real> B \<otimes>\<^sub>m (mat\<^sub>\<real> A ^\<^sub>m k \<otimes>\<^sub>m mat\<^sub>\<real> C)) \<le> ?ck" by auto
    also have "mat_sum (mat\<^sub>\<real> B \<otimes>\<^sub>m (mat\<^sub>\<real> A ^\<^sub>m k \<otimes>\<^sub>m mat\<^sub>\<real> C)) = 
      real_of ?sum" 
      using Ak AkC A B C by (simp add: mat_real_conv)
    finally have "real_of ?sum \<le> ?ck" .
    from real_le[OF this] have le: "?sum \<le> of_int \<lceil>?ck\<rceil>" by auto
    have "?ck \<le> ?cck" by (simp add: times_left_mono)
    hence "\<lceil>?ck\<rceil> \<le> \<lceil>?cck\<rceil>" by linarith
    hence "of_int \<lceil>?ck\<rceil> \<le> ((of_int \<lceil>?cck\<rceil>) :: 'a)" 
      unfolding of_int_le_iff .
    with le have le: "?sum \<le> of_int \<lceil>?cck\<rceil>" by linarith
    also have "\<dots> = of_int \<lceil>c\<rceil> * of_nat k ^ d"
      by (metis (no_types, hide_lams) ceiling_of_int of_int_mult of_int_of_nat_eq of_nat_power)
    finally have "?sum \<le> of_int \<lceil>c\<rceil> * of_nat k ^ d" .
  }
  thus ?thesis by auto
qed
end


end