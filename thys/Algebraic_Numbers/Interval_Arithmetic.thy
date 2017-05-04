(*  
    Author:      Sebastiaan Joosten 
                 René Thiemann
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Interval Arithmetic\<close>

text \<open>We provide basic interval arithmetic operations for real and complex intervals.
  As application we prove that complex polynomial evaluation is continuous w.r.t.
  interval arithmetic. To be more precise, if an interval sequence converges to some 
  element $x$, then the interval polynomial evaluation of $f$ tends to $f(x)$.\<close>
  
theory Interval_Arithmetic
imports
  Algebraic_Numbers_Prelim (* for certain simp rules *)
begin

text \<open>Real Intervals\<close>
  
datatype real_itvl = Interval (lower_itvl: real) (upper_itvl: real)
 
definition in_real_itvl :: "real \<Rightarrow> real_itvl \<Rightarrow> bool" ("(_/ \<in>\<^sub>r _)" [51, 51] 50) where
  "y \<in>\<^sub>r x \<equiv> case x of Interval lx ux \<Rightarrow> lx \<le> y \<and> y \<le> ux" 

definition of_int_real_itvl :: "int \<Rightarrow> real_itvl" where
  "of_int_real_itvl x \<equiv> let y = of_int x in Interval y y" 

lemma of_int_itvl_real: "of_int i \<in>\<^sub>r of_int_real_itvl i" 
  unfolding in_real_itvl_def of_int_real_itvl_def by (auto simp: Let_def)

instantiation real_itvl :: comm_monoid_add begin

  definition zero_real_itvl where "0 \<equiv> Interval 0 0"

  fun plus_real_itvl :: "real_itvl \<Rightarrow> real_itvl \<Rightarrow> real_itvl" where
    "Interval lx ux + Interval ly uy = Interval (lx + ly) (ux + uy)" 

  instance
  proof 
    show "a + b + c = a + (b + c)" for a b c :: real_itvl by (cases a, cases b, cases c, auto)
    show "a + b = b + a" for a b :: real_itvl by (cases a, cases b, auto)
    show "0 + a = a" for a :: real_itvl by (cases a, auto simp: zero_real_itvl_def of_int_real_itvl_def)
  qed
end



lemma plus_itvl_real: "x \<in>\<^sub>r X \<Longrightarrow> y \<in>\<^sub>r Y \<Longrightarrow> x + y \<in>\<^sub>r X + Y"
  unfolding in_real_itvl_def by (cases X, cases Y, auto)

instantiation real_itvl :: minus begin

  fun minus_real_itvl :: "real_itvl \<Rightarrow> real_itvl \<Rightarrow> real_itvl" where
    "Interval lx ux - Interval ly uy = Interval (lx - uy) (ux - ly)" 

  instance..

end

lemma real_itvl_minus_0[simp]:
  fixes a :: real_itvl
  shows "a - 0 = a" by (cases a, simp add: zero_real_itvl_def)

lemma minus_itvl_real: "x \<in>\<^sub>r X \<Longrightarrow> y \<in>\<^sub>r Y \<Longrightarrow> x - y \<in>\<^sub>r X - Y"
  unfolding in_real_itvl_def by (cases X, cases Y, auto)

instantiation real_itvl :: times begin
  fun times_real_itvl where
  "Interval lx ux * Interval ly uy =
     (let x1 = lx * ly; x2 = lx * uy; x3 = ux * ly; x4 = ux * uy
      in Interval (min x1 (min x2 (min x3 x4))) (max x1 (max x2 (max x3 x4))))"
  instance..
end

instantiation real_itvl :: one begin
  definition "1 = Interval 1 1"
  instance..
end

lemma real_itvl_mult_0:
  fixes a :: real_itvl
  shows [simp]: "a * 0 = 0" by (cases a, auto simp: zero_real_itvl_def)

lemma times_itvl_real: assumes "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  shows "x * y \<in>\<^sub>r X * Y"
proof -
  obtain X1 X2 where X:"Interval X1 X2 = X" by (cases X,auto)
  obtain Y1 Y2 where Y:"Interval Y1 Y2 = Y" by (cases Y,auto)
  from assms X Y have assms:
    "X1 \<le> x" "x \<le> X2" "Y1 \<le> y" "y \<le> Y2"
    unfolding in_real_itvl_def by auto
  hence "X1 * Y1 \<le> x * y \<or> X1 * Y2 \<le> x * y \<or> X2 * Y1 \<le> x * y \<or> X2 * Y2 \<le> x * y"
    using mult_le_cancel_left mult_le_cancel_right
    by (metis (mono_tags, hide_lams) linear order_trans)
  hence min:"min (X1 * Y1) (min (X1 * Y2) (min (X2 * Y1) (X2 * Y2))) \<le> x * y" by auto
  have "X1 * Y1 \<ge> x * y \<or> X1 * Y2 \<ge> x * y \<or> X2 * Y1 \<ge> x * y \<or> X2 * Y2 \<ge> x * y"
    using assms mult_le_cancel_left mult_le_cancel_right
    by (metis (mono_tags, hide_lams) linear order_trans)
  hence max:"x * y \<le> max (X1 * Y1) (max (X1 * Y2) (max (X2 * Y1) (X2 * Y2)))" by auto
  show ?thesis using min max X Y unfolding in_real_itvl_def
    by (auto simp: Let_def)
qed
  
definition tends_to_real_itvl :: "(nat \<Rightarrow> real_itvl) \<Rightarrow> real \<Rightarrow> bool" (infixr "\<longlonglongrightarrow>\<^sub>r" 55) where
  "(X \<longlonglongrightarrow>\<^sub>r x) \<equiv> ((upper_itvl \<circ> X) \<longlonglongrightarrow> x) \<and> ((lower_itvl \<circ> X) \<longlonglongrightarrow> x)"

lemma tendsto_real_itvlI[intro]:
  assumes "(upper_itvl \<circ> X) \<longlonglongrightarrow> x" and "(lower_itvl \<circ> X) \<longlonglongrightarrow> x"
  shows "X \<longlonglongrightarrow>\<^sub>r x"
  using assms by (auto simp:tends_to_real_itvl_def)

lemma tendsto_real_itvl_plus: assumes "X \<longlonglongrightarrow>\<^sub>r x" "Y \<longlonglongrightarrow>\<^sub>r y"
  shows "(\<lambda> i. X i + Y i) \<longlonglongrightarrow>\<^sub>r x + y"
proof -
  have *: "X i + Y i = Interval (lower_itvl (X i) + lower_itvl (Y i)) (upper_itvl (X i) + upper_itvl (Y i))" for i
     by (cases "X i"; cases "Y i", auto)
  from assms show ?thesis unfolding * tends_to_real_itvl_def o_def by (auto intro: tendsto_intros)
qed

lemma tendsto_real_itvl_minus: assumes "X \<longlonglongrightarrow>\<^sub>r x" "Y \<longlonglongrightarrow>\<^sub>r y"
  shows "(\<lambda> i. X i - Y i) \<longlonglongrightarrow>\<^sub>r x - y"
proof -
  have *: "X i - Y i = Interval (lower_itvl (X i) - upper_itvl (Y i)) (upper_itvl (X i) - lower_itvl (Y i))" for i
    by (cases "X i"; cases "Y i", auto)
  from assms show ?thesis unfolding o_def * tends_to_real_itvl_def by (auto intro: tendsto_intros)
qed

lemma tendsto_real_itvl_times: assumes "X \<longlonglongrightarrow>\<^sub>r x" "Y \<longlonglongrightarrow>\<^sub>r y"
  shows "(\<lambda> i. X i * Y i) \<longlonglongrightarrow>\<^sub>r x * y"
proof -
  have *: "(lower_itvl (X i * Y i)) = (
    let lx = (lower_itvl (X i)); ux = (upper_itvl (X i));
        ly = (lower_itvl (Y i)); uy = (upper_itvl (Y i)); 
        x1 = lx * ly; x2 = lx * uy; x3 = ux * ly; x4 = ux * uy in 
      (min x1 (min x2 (min x3 x4))))" "(upper_itvl (X i * Y i)) = (
    let lx = (lower_itvl (X i)); ux = (upper_itvl (X i));
        ly = (lower_itvl (Y i)); uy = (upper_itvl (Y i)); 
      x1 = lx * ly; x2 = lx * uy; x3 = ux * ly; x4 = ux * uy in 
      (max x1 (max x2 (max x3 x4))))" for i
    by (cases "X i"; cases "Y i", auto simp: Let_def)+
  have "(\<lambda>i. (lower_itvl (X i * Y i))) \<longlonglongrightarrow> min (x * y) (min (x * y) (min (x * y) (x *y)))" 
    using assms unfolding tends_to_real_itvl_def * Let_def o_def
    by (intro tendsto_min tendsto_intros, auto)
  moreover 
  have "(\<lambda>i. (upper_itvl (X i * Y i))) \<longlonglongrightarrow> max (x * y) (max (x * y) (max (x * y) (x *y)))" 
    using assms unfolding tends_to_real_itvl_def * Let_def o_def
    by (intro tendsto_max tendsto_intros, auto)
  ultimately show ?thesis unfolding tends_to_real_itvl_def o_def by auto
qed

lemma tends_to_real_itvl_diff: assumes "(\<lambda> i. f i) \<longlonglongrightarrow>\<^sub>r a" 
  and "a \<noteq> b" 
shows "\<exists> n. \<not> b \<in>\<^sub>r f n" 
proof -
  let ?d = "abs (b - a) / 2" 
  from assms have d: "?d > 0" by auto
  from assms(1)[unfolded tends_to_real_itvl_def] 
  have cvg: "(lower_itvl o f) \<longlonglongrightarrow> a" "(upper_itvl o f) \<longlonglongrightarrow> a" by auto
  from LIMSEQ_D[OF cvg(1) d] obtain n1 where 
    n1: "\<And> n. n \<ge> n1 \<Longrightarrow> norm ((lower_itvl \<circ> f) n - a) < ?d " by auto
  from LIMSEQ_D[OF cvg(2) d] obtain n2 where
    n2: "\<And> n. n \<ge> n2 \<Longrightarrow> norm ((upper_itvl \<circ> f) n - a) < ?d " by auto
  define n where "n = max n1 n2"  
  from n1[of n] n2[of n] have bnd: 
    "norm ((lower_itvl \<circ> f) n - a) < ?d" 
    "norm ((upper_itvl \<circ> f) n - a) < ?d" 
    unfolding n_def by auto
  show ?thesis by (rule exI[of _ n], insert bnd, cases "f n", auto simp: in_real_itvl_def, argo) 
qed
  
text \<open>Complex Intervals\<close>
  
datatype complex_itvl = Complex_Interval (Re_itvl: real_itvl) (Im_itvl: real_itvl)

definition in_complex_itvl :: "complex \<Rightarrow> complex_itvl \<Rightarrow> bool" ("(_/ \<in>\<^sub>c _)" [51, 51] 50) where
  "y \<in>\<^sub>c x \<equiv> (case x of Complex_Interval r i \<Rightarrow> Re y \<in>\<^sub>r r \<and> Im y \<in>\<^sub>r i)" 
      
instantiation complex_itvl :: comm_monoid_add begin

  definition "0 \<equiv> Complex_Interval 0 0"

  fun plus_complex_itvl :: "complex_itvl \<Rightarrow> complex_itvl \<Rightarrow> complex_itvl" where
    "Complex_Interval rx ix + Complex_Interval ry iy = Complex_Interval (rx + ry) (ix + iy)" 

  instance
  proof
    fix a b c :: complex_itvl
    show "a + b + c = a + (b + c)" by (cases a, cases b, cases c, simp add: ac_simps)
    show "a + b = b + a" by (cases a, cases b, simp add: ac_simps)
    show "0 + a = a" by (cases a, simp add: ac_simps zero_complex_itvl_def)
  qed
end

lemma plus_complex_itvl: "x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> x + y \<in>\<^sub>c X + Y"
  unfolding in_complex_itvl_def using plus_itvl_real by (cases X, cases Y, auto)

definition of_int_complex_itvl :: "int \<Rightarrow> complex_itvl" where
  "of_int_complex_itvl x = Complex_Interval (of_int_real_itvl x) 0" 

lemma of_int_complex_itvl_0[simp]: "of_int_complex_itvl 0 = 0"
  by (simp add: of_int_complex_itvl_def zero_complex_itvl_def of_int_real_itvl_def zero_real_itvl_def)

lemma of_int_complex_itvl: "of_int i \<in>\<^sub>c of_int_complex_itvl i" 
  unfolding in_complex_itvl_def of_int_complex_itvl_def using of_int_itvl_real[of i] 
  by (auto simp: in_real_itvl_def zero_complex_itvl_def zero_real_itvl_def)

instantiation complex_itvl :: times begin

  fun times_complex_itvl :: "complex_itvl \<Rightarrow> complex_itvl \<Rightarrow> complex_itvl" where
    "Complex_Interval rx ix * Complex_Interval ry iy =
     Complex_Interval (rx * ry - ix * iy) (rx * iy + ix * ry)"

  instance ..

end

instantiation complex_itvl :: minus begin

  fun minus_complex_itvl where
    "Complex_Interval R I - Complex_Interval R' I' = Complex_Interval (R-R') (I-I')"

  instance..

end

lemma complex_itvl_mult_0[simp]:
  fixes a :: complex_itvl shows "a * 0 = 0" by (cases a, simp add: zero_complex_itvl_def)

lemma times_complex_itvl: "x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> x * y \<in>\<^sub>c X * Y"
  unfolding in_complex_itvl_def
  using times_itvl_real minus_itvl_real plus_itvl_real
  by (cases X, cases Y, auto)

definition ipoly_complex_itvl :: "int poly \<Rightarrow> complex_itvl \<Rightarrow> complex_itvl" where
  "ipoly_complex_itvl p x = fold_coeffs (\<lambda>a b. of_int_complex_itvl a + x * b) p 0" 

lemma ipoly_complex_itvl_0[simp]:
  "ipoly_complex_itvl 0 x = 0"
  by (auto simp: ipoly_complex_itvl_def)

lemma ipoly_complex_itvl_pCons[simp]:
  "ipoly_complex_itvl (pCons a p) x = of_int_complex_itvl a + x * (ipoly_complex_itvl p x)"
  by (cases "p = 0"; cases "a = 0", auto simp: ipoly_complex_itvl_def)

lemma ipoly_complex_itvl: assumes x: "x \<in>\<^sub>c X" 
  shows "ipoly p x \<in>\<^sub>c ipoly_complex_itvl p X" 
proof -
  define xs where "xs = coeffs p"
  have 0: "in_complex_itvl 0 0" (is "in_complex_itvl ?Z ?z")
    unfolding in_complex_itvl_def in_real_itvl_def zero_complex_itvl_def zero_real_itvl_def by auto
  define Z where "Z = ?Z" 
  define z where "z = ?z" 
  from 0 have 0: "in_complex_itvl Z z" unfolding Z_def z_def by auto
  note x = times_complex_itvl[OF x]
  show ?thesis 
    unfolding poly_map_poly_code ipoly_complex_itvl_def fold_coeffs_def 
      xs_def[symmetric] Z_def[symmetric] z_def[symmetric] using 0
    by (induct xs arbitrary: Z z, auto intro!: plus_complex_itvl of_int_complex_itvl x)
qed
  
definition tendsto_complex_itvl (infix "\<longlonglongrightarrow>\<^sub>c" 55) where
  "C \<longlonglongrightarrow>\<^sub>c c \<equiv> ((Re_itvl \<circ> C) \<longlonglongrightarrow>\<^sub>r Re c) \<and> ((Im_itvl \<circ> C) \<longlonglongrightarrow>\<^sub>r Im c)"

lemma tendsto_complex_itvlI[intro!]:
  "(Re_itvl \<circ> C) \<longlonglongrightarrow>\<^sub>r Re c \<Longrightarrow> (Im_itvl \<circ> C) \<longlonglongrightarrow>\<^sub>r Im c \<Longrightarrow> C \<longlonglongrightarrow>\<^sub>c c"
  by (simp add: tendsto_complex_itvl_def)

lemma real_itvl_tendsto_of_int: "(\<lambda>i. of_int_real_itvl n) \<longlonglongrightarrow>\<^sub>r of_int n"
  by (auto simp: o_def of_int_real_itvl_def Let_def)

lemma real_itvl_tendsto_0: "(\<lambda>i. 0) \<longlonglongrightarrow>\<^sub>r 0"
  using real_itvl_tendsto_of_int[of 0] by (simp add: zero_real_itvl_def of_int_real_itvl_def)

lemma complex_itvl_tendsto_of_int: "(\<lambda>i. of_int_complex_itvl n) \<longlonglongrightarrow>\<^sub>c of_int n"
  by (auto simp: o_def of_int_complex_itvl_def intro!:real_itvl_tendsto_of_int real_itvl_tendsto_0)

lemma Im_itvl_plus: "Im_itvl (A + B) = Im_itvl A + Im_itvl B" 
  by (cases A; cases B, auto)

lemma Re_itvl_plus: "Re_itvl (A + B) = Re_itvl A + Re_itvl B" 
  by (cases A; cases B, auto)

lemma Im_itvl_minus: "Im_itvl (A - B) = Im_itvl A - Im_itvl B" 
  by (cases A; cases B, auto)

lemma Re_itvl_minus: "Re_itvl (A - B) = Re_itvl A - Re_itvl B" 
  by (cases A; cases B, auto)
    
lemma Re_itvl_times: "Re_itvl (A * B) = Re_itvl A * Re_itvl B - Im_itvl A * Im_itvl B" 
  by (cases A; cases B, auto)

lemma Im_itvl_times: "Im_itvl (A * B) = Re_itvl A * Im_itvl B + Im_itvl A * Re_itvl B" 
  by (cases A; cases B, auto)

lemma tendsto_complex_itvl_plus:
  "A \<longlonglongrightarrow>\<^sub>c a \<Longrightarrow> B \<longlonglongrightarrow>\<^sub>c b \<Longrightarrow> (\<lambda>i. A i + B i) \<longlonglongrightarrow>\<^sub>c a + b" 
  unfolding tendsto_complex_itvl_def
  by (auto intro!: tendsto_real_itvl_plus simp: o_def Re_itvl_plus Im_itvl_plus)

lemma tendsto_complex_itvl_minus:
  "A \<longlonglongrightarrow>\<^sub>c a \<Longrightarrow> B \<longlonglongrightarrow>\<^sub>c b \<Longrightarrow> (\<lambda>i. A i - B i) \<longlonglongrightarrow>\<^sub>c a - b" 
  unfolding tendsto_complex_itvl_def
  by (auto intro!: tendsto_real_itvl_minus simp: o_def Re_itvl_minus Im_itvl_minus)

lemma tendsto_complex_itvl_times:
  "A \<longlonglongrightarrow>\<^sub>c a \<Longrightarrow> B \<longlonglongrightarrow>\<^sub>c b \<Longrightarrow> (\<lambda>i. A i * B i) \<longlonglongrightarrow>\<^sub>c a * b"
  unfolding tendsto_complex_itvl_def
  by (auto intro!: tendsto_real_itvl_minus tendsto_real_itvl_times tendsto_real_itvl_plus 
    simp: o_def Re_itvl_times Im_itvl_times)

lemma ipoly_complex_itvl_tendsto:
  assumes "C \<longlonglongrightarrow>\<^sub>c c"
  shows "(\<lambda>i. ipoly_complex_itvl p (C i)) \<longlonglongrightarrow>\<^sub>c ipoly p c"
proof(induct p)
  case 0
  show ?case by (auto simp: o_def zero_complex_itvl_def zero_real_itvl_def tendsto_complex_itvl_def)
next
  case (pCons a p)
  show ?case
    apply (unfold ipoly_complex_itvl_pCons of_int_hom.map_poly_pCons_hom poly_pCons)
    apply (intro tendsto_complex_itvl_plus tendsto_complex_itvl_times assms pCons complex_itvl_tendsto_of_int)
    done
qed

lemma tends_to_complex_itvl_diff: assumes "(\<lambda> i. f i) \<longlonglongrightarrow>\<^sub>c a" 
  and "a \<noteq> b" 
shows "\<exists> n. \<not> b \<in>\<^sub>c f n" 
proof -
  from assms(1)[unfolded tendsto_complex_itvl_def o_def]
  have cvg: "(\<lambda>x. Re_itvl (f x)) \<longlonglongrightarrow>\<^sub>r Re a" "(\<lambda>x. Im_itvl (f x)) \<longlonglongrightarrow>\<^sub>r Im a" by auto
  from assms(2) have "Re a \<noteq> Re b \<or> Im a \<noteq> Im b"
    using complex.expand by blast
  thus ?thesis
  proof
    assume "Re a \<noteq> Re b" 
    from tends_to_real_itvl_diff[OF cvg(1) this] show ?thesis
      unfolding in_complex_itvl_def by (metis (no_types, lifting) complex_itvl.case_eq_if)
  next
    assume "Im a \<noteq> Im b" 
    from tends_to_real_itvl_diff[OF cvg(2) this] show ?thesis
      unfolding in_complex_itvl_def by (metis (no_types, lifting) complex_itvl.case_eq_if)
  qed
qed
  
end
