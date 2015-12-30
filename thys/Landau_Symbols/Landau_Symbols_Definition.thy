(*
  File:   Landau_Symbols_Definition.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Landau symbols for reasoning about the asymptotic growth of functions. 
*)
section {* Definition of Landau symbols *}

theory Landau_Symbols_Definition
imports 
  Complex_Main
  "~~/src/HOL/Library/Function_Algebras" 
  "~~/src/HOL/Library/Set_Algebras"
  Landau_Library
begin

subsection {* Eventual non-negativity/non-zeroness *}

text {* 
  For certain transformations of Landau symbols, it is required that the functions involved 
  are eventually non-negative of non-zero. In the following, we set up a system to guide the 
  simplifier to discharge these requirements during simplification at least in obvious cases.
*}

definition "eventually_nonzero f \<longleftrightarrow> eventually (\<lambda>x. (f x :: _ :: linordered_field) \<noteq> 0) at_top"
definition "eventually_nonneg f \<longleftrightarrow> eventually (\<lambda>x. (f x :: _ :: linordered_field) \<ge> 0) at_top"

named_theorems eventually_nonzero_simps

lemmas [eventually_nonzero_simps] = eventually_not_equal eventually_ln_not_equal

lemma eventually_nonzeroD: "eventually_nonzero f \<Longrightarrow> eventually (\<lambda>x. f x \<noteq> 0) at_top"
  by (simp add: eventually_nonzero_def)

lemma eventually_nonzero_const [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>_::_::linorder. c) \<longleftrightarrow> c \<noteq> 0"
  unfolding eventually_nonzero_def 
  by (simp add: eventually_False trivial_limit_at_top_linorder)

lemma eventually_nonzero_inverse [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>x. inverse (f x)) \<longleftrightarrow> eventually_nonzero f"
  unfolding eventually_nonzero_def by simp

lemma eventually_nonzero_mult [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>x. f x * g x) \<longleftrightarrow> eventually_nonzero f \<and> eventually_nonzero g"
  unfolding eventually_nonzero_def by (simp_all add: eventually_conj_iff[symmetric])

lemma eventually_nonzero_pow [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>x::_::linorder. f x ^ n) \<longleftrightarrow> n = 0 \<or> eventually_nonzero f"
  by (induction n) (auto simp: eventually_nonzero_simps)

lemma eventually_nonzero_divide [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>x. f x / g x) \<longleftrightarrow> eventually_nonzero f \<and> eventually_nonzero g"
  unfolding eventually_nonzero_def by (simp_all add: eventually_conj_iff[symmetric])

lemma eventually_nonzero_ident [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>x. x)"
  unfolding eventually_nonzero_def by (simp add: eventually_not_equal)

lemma eventually_nonzero_ln [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>x::real. ln x)"
  unfolding eventually_nonzero_def by (subst eventually_ln_at_top) (rule eventually_not_equal)

lemma eventually_nonzero_ln_const [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonzero (\<lambda>x. ln (b * x :: real))"
  unfolding eventually_nonzero_def using eventually_gt_at_top[of "max 1 (inverse b)"]
  by (auto elim!: eventually_mono simp: field_simps)

lemma eventually_nonzero_ln_const' [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonzero (\<lambda>x. ln (x * b :: real))"
  using eventually_nonzero_ln_const[of b] by (simp add: mult.commute)

lemma eventually_nonzero_powr [eventually_nonzero_simps]:
  "eventually_nonzero (\<lambda>x. f x powr p) \<longleftrightarrow> eventually_nonzero f"
  unfolding eventually_nonzero_def by simp



lemma eventually_nonneg_const [eventually_nonzero_simps]:
  "eventually_nonneg (\<lambda>(_::_::linorder). c) \<longleftrightarrow> c \<ge> 0"
  unfolding eventually_nonneg_def by (auto simp: eventually_at_top_linorder)

lemma eventually_nonneg_inverse [eventually_nonzero_simps]:
  "eventually_nonneg (\<lambda>x. inverse (f x)) \<longleftrightarrow> eventually_nonneg f"
  unfolding eventually_nonneg_def by (intro eventually_subst) simp

lemma eventually_nonneg_add [eventually_nonzero_simps]:
  assumes "eventually_nonneg f" "eventually_nonneg g"
  shows   "eventually_nonneg (\<lambda>x. f x + g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim simp

lemma eventually_nonneg_mult [eventually_nonzero_simps]:
  assumes "eventually_nonneg f" "eventually_nonneg g"
  shows   "eventually_nonneg (\<lambda>x. f x * g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim simp

lemma eventually_nonneg_mult' [eventually_nonzero_simps]:
  assumes "eventually_nonneg (\<lambda>x. -f x)" "eventually_nonneg (\<lambda>x. - g x)"
  shows   "eventually_nonneg (\<lambda>x. f x * g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim (auto intro: mult_nonpos_nonpos)

lemma eventually_nonneg_divide [eventually_nonzero_simps]:
  assumes "eventually_nonneg f" "eventually_nonneg g"
  shows   "eventually_nonneg (\<lambda>x. f x / g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim simp

lemma eventually_nonneg_divide' [eventually_nonzero_simps]:
  assumes "eventually_nonneg (\<lambda>x. -f x)" "eventually_nonneg (\<lambda>x. - g x)"
  shows   "eventually_nonneg (\<lambda>x. f x / g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim (auto intro: divide_nonpos_nonpos)

lemma eventually_nonneg_ident [eventually_nonzero_simps]:
  "eventually_nonneg (\<lambda>x. x)" unfolding eventually_nonneg_def by (rule eventually_ge_at_top)

lemma eventually_nonneg_pow [eventually_nonzero_simps]:
  "eventually_nonneg f \<Longrightarrow> eventually_nonneg (\<lambda>x::_::linorder. f x ^ n)"
  by (induction n) (auto simp: eventually_nonzero_simps)

lemma eventually_nonneg_powr [eventually_nonzero_simps]:
  "eventually_nonneg (\<lambda>x. f x powr y :: real)" by (simp add: eventually_nonneg_def)

lemma eventually_nonneg_ln [eventually_nonzero_simps]:
  "eventually_nonneg (\<lambda>x. ln x :: real)" 
  by (simp add: eventually_nonneg_def eventually_ln_at_top eventually_ge_at_top)

lemma eventually_nonneg_ln_const [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonneg (\<lambda>x. ln (b*x) :: real)" 
  unfolding eventually_nonneg_def using eventually_ge_at_top[of "inverse b"]
  by eventually_elim (simp_all add: field_simps)

lemma eventually_nonneg_ln_const' [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonneg (\<lambda>x. ln (x*b) :: real)" 
  using eventually_nonneg_ln_const[of b] by (simp add: mult.commute)



subsection {* Definition of Landau symbols *}

text {*
  Our Landau symbols are sign-oblivious, i.e. any function always has the same growth 
  as its absolute. This has the advantage of making some cancelling rules for sums nicer, but 
  introduces some problems in other places. Nevertheless, we found this definition more convenient
  to work with.
*}

(* TODO: Generalise w.r.t. arbitrary filters? *)

definition bigo :: "(('a::order) \<Rightarrow> ('b :: linordered_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" ("(1O'(_'))") 
  where "O(g) = {f. (\<exists>c>0. eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>) at_top)}"  

definition smallo :: "(('a::order) \<Rightarrow> ('b :: linordered_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" ("(1o'(_'))") 
  where "o(g) = {f. (\<forall>c>0. eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>) at_top)}"

definition bigomega :: "(('a::order) \<Rightarrow> ('b :: linordered_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" ("(1\<Omega>'(_'))") 
  where "\<Omega>(g) = {f. (\<exists>c>0. eventually (\<lambda>x. \<bar>f x\<bar> \<ge> c * \<bar>g x\<bar>) at_top)}"  

definition smallomega :: "(('a::order) \<Rightarrow> ('b :: linordered_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" ("(1\<omega>'(_'))") 
  where "\<omega>(g) = {f. (\<forall>c>0. eventually (\<lambda>x. \<bar>f x\<bar> \<ge> c * \<bar>g x\<bar>) at_top)}"

definition bigtheta :: "(('a::order) \<Rightarrow> ('b :: linordered_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" ("(1\<Theta>'(_'))") 
  where "\<Theta>(g) = O(g) \<inter> \<Omega>(g)"

text {* The following is a set of properties that all Landau symbols satisfy. *}

locale landau_symbol =
  fixes L L' :: "(('a::order) \<Rightarrow> ('b :: linordered_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  assumes in_cong: "eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> f \<in> L(h) \<longleftrightarrow> g \<in> L(h)"
  assumes cong: "eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> L(f) = L(g)"
  assumes cong_bigtheta: "f \<in> \<Theta>(g) \<Longrightarrow> L(f) = L(g)"
  assumes in_cong_bigtheta: "f \<in> \<Theta>(g) \<Longrightarrow> f \<in> L(h) \<longleftrightarrow> g \<in> L(h)"
  assumes abs [simp]: "L(\<lambda>x. \<bar>f x\<bar>) = L(f)"
  assumes abs_in_iff [simp]: "(\<lambda>x. \<bar>f x\<bar>) \<in> L(g) \<longleftrightarrow> f \<in> L(g)"
  assumes cmult [simp]: "c \<noteq> 0 \<Longrightarrow> L(\<lambda>x. c * f x) = L(f)"
  assumes cmult_in_iff [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. c * f x) \<in> L(g) \<longleftrightarrow> f \<in> L(g)"
  assumes mult_left [simp]: "f \<in> L(g) \<Longrightarrow> (\<lambda>x. h x * f x) \<in> L(\<lambda>x. h x * g x)"
  assumes inverse: "eventually (\<lambda>x. f x \<noteq> 0) at_top \<Longrightarrow> eventually (\<lambda>x. g x \<noteq> 0) at_top \<Longrightarrow> 
                        f \<in> L(g) \<Longrightarrow> (\<lambda>x. inverse (g x)) \<in> L(\<lambda>x. inverse (f x))"
  assumes subsetI: "f \<in> L(g) \<Longrightarrow> L(f) \<subseteq> L(g)"
  assumes plus_subset1: "f \<in> o(g) \<Longrightarrow> L(g) \<subseteq> L(\<lambda>x. f x + g x)"
  assumes trans: "f \<in> L(g) \<Longrightarrow> g \<in> L(h) \<Longrightarrow> f \<in> L(h)"
begin

lemma cong_ex: 
  "eventually (\<lambda>x. f1 x = f2 x) at_top \<Longrightarrow> eventually (\<lambda>x. g1 x = g2 x) at_top \<Longrightarrow>
   f1 \<in> L(g1) \<longleftrightarrow> f2 \<in> L(g2)" by (subst cong, assumption, subst in_cong, assumption, rule refl)

lemma cong_ex_bigtheta: 
  "f1 \<in> \<Theta>(f2) \<Longrightarrow> g1 \<in> \<Theta>(g2) \<Longrightarrow> f1 \<in> L(g1) \<longleftrightarrow> f2 \<in> L(g2)" 
  by (subst cong_bigtheta, assumption, subst in_cong_bigtheta, assumption, rule refl)

lemma landau_symbol: "landau_symbol L"
  using cong abs abs_in_iff cmult cmult_in_iff plus_subset1 by unfold_locales

lemma bigtheta_trans1: 
  "f \<in> L(g) \<Longrightarrow> g \<in> \<Theta>(h) \<Longrightarrow> f \<in> L(h)"
  by (subst cong_bigtheta[symmetric])

lemma bigtheta_trans2: 
  "f \<in> \<Theta>(g) \<Longrightarrow> g \<in> L(h) \<Longrightarrow> f \<in> L(h)"
  by (subst in_cong_bigtheta)

lemma cmult' [simp]: "c \<noteq> 0 \<Longrightarrow> L(\<lambda>x. f x * c) = L(f)"
  by (subst mult.commute) (rule cmult)

lemma cmult_in_iff' [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. f x * c) \<in> L(g) \<longleftrightarrow> f \<in> L(g)"
  by (subst mult.commute) (rule cmult_in_iff)

lemma cdiv [simp]: "c \<noteq> 0 \<Longrightarrow> L(\<lambda>x. f x / c) = L(f)"
  using cmult'[of "inverse c" f] by (simp add: field_simps)

lemma cdiv_in_iff' [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. f x / c) \<in> L(g) \<longleftrightarrow> f \<in> L(g)"
  using cmult_in_iff'[of "inverse c" f] by (simp add: field_simps)
  
lemma uminus [simp]: "L(\<lambda>x. -g x) = L(g)" using cmult[of "-1"] by simp

lemma uminus_in_iff [simp]: "(\<lambda>x. -f x) \<in> L(g) \<longleftrightarrow> f \<in> L(g)"
  using cmult_in_iff[of "-1"] by simp

lemma const: "c \<noteq> 0 \<Longrightarrow> L(\<lambda>_. c) = L(\<lambda>_. 1)"
  by (subst (2) cmult[symmetric]) simp_all

(* Simplifier loops without the NO_MATCH *)
lemma const' [simp]: "NO_MATCH 1 c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> L(\<lambda>_. c) = L(\<lambda>_. 1)"
  by (rule const)

lemma const_in_iff: "c \<noteq> 0 \<Longrightarrow> (\<lambda>_. c) \<in> L(f) \<longleftrightarrow> (\<lambda>_. 1) \<in> L(f)"
  using cmult_in_iff'[of c "\<lambda>_. 1"] by simp

lemma const_in_iff' [simp]: "NO_MATCH 1 c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (\<lambda>_. c) \<in> L(f) \<longleftrightarrow> (\<lambda>_. 1) \<in> L(f)"
  by (rule const_in_iff)

lemma plus_subset2: "g \<in> o(f) \<Longrightarrow> L(f) \<subseteq> L(\<lambda>x. f x + g x)"
  by (subst add.commute) (rule plus_subset1)

lemma mult_right [simp]: "f \<in> L(g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L(\<lambda>x. g x * h x)"
  using mult_left by (simp add: mult.commute)

lemma mult: "f1 \<in> L(g1) \<Longrightarrow> f2 \<in> L(g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> L(\<lambda>x. g1 x * g2 x)"
  by (rule trans, erule mult_left, erule mult_right)

lemma inverse_cancel:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) at_top"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows   "(\<lambda>x. inverse (f x)) \<in> L(\<lambda>x. inverse (g x)) \<longleftrightarrow> g \<in> L(f)"
proof
  assume "(\<lambda>x. inverse (f x)) \<in> L(\<lambda>x. inverse (g x))"
  from inverse[OF _ _ this] assms show "g \<in> L(f)" by simp
qed (intro inverse assms)

lemma divide_right:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) at_top"
  assumes "f \<in> L(g)"
  shows   "(\<lambda>x. f x / h x) \<in> L(\<lambda>x. g x / h x)"
  by (subst (1 2) divide_inverse) (intro mult_right inverse assms)

lemma divide_right_iff:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) at_top"
  shows   "(\<lambda>x. f x / h x) \<in> L(\<lambda>x. g x / h x) \<longleftrightarrow> f \<in> L(g)"
proof
  assume "(\<lambda>x. f x / h x) \<in> L(\<lambda>x. g x / h x)"
  from mult_right[OF this, of h] assms show "f \<in> L(g)"
    by (subst (asm) cong_ex[of _ f _ g]) (auto elim!: eventually_mono)
qed (simp add: divide_right assms)

lemma divide_left:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) at_top"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  assumes "g \<in> L(f)"
  shows   "(\<lambda>x. h x / f x) \<in> L(\<lambda>x. h x / g x)"
  by (subst (1 2) divide_inverse) (intro mult_left inverse assms)

lemma divide_left_iff:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) at_top"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  assumes "eventually (\<lambda>x. h x \<noteq> 0) at_top"
  shows   "(\<lambda>x. h x / f x) \<in> L(\<lambda>x. h x / g x) \<longleftrightarrow> g \<in> L(f)"
proof
  assume A: "(\<lambda>x. h x / f x) \<in> L(\<lambda>x. h x / g x)"
  from assms have B: "eventually (\<lambda>x. h x / f x / h x = inverse (f x)) at_top"
    by eventually_elim (simp add: divide_inverse)
  from assms have C: "eventually (\<lambda>x. h x / g x / h x = inverse (g x)) at_top"
    by eventually_elim (simp add: divide_inverse)
  from divide_right[OF assms(3) A] assms show "g \<in> L(f)"
    by (subst (asm) cong_ex[OF B C]) (simp add: inverse_cancel)
qed (simp add: divide_left assms)

lemma divide:
  assumes "eventually (\<lambda>x. g1 x \<noteq> 0) at_top"
  assumes "eventually (\<lambda>x. g2 x \<noteq> 0) at_top"
  assumes "f1 \<in> L(f2)" "g2 \<in> L(g1)"
  shows   "(\<lambda>x. f1 x / g1 x) \<in> L(\<lambda>x. f2 x / g2 x)"
  by (subst (1 2) divide_inverse) (intro mult inverse assms)
  
lemma divide_eq1:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) at_top"
  shows   "f \<in> L(\<lambda>x. g x / h x) \<longleftrightarrow> (\<lambda>x. f x * h x) \<in> L(g)"
proof-
  have "f \<in> L(\<lambda>x. g x / h x) \<longleftrightarrow> (\<lambda>x. f x * h x / h x) \<in> L(\<lambda>x. g x / h x)"
    using assms by (intro in_cong) (auto elim: eventually_mono)
  thus ?thesis by (simp only: divide_right_iff assms)
qed

lemma divide_eq2:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) at_top"
  shows   "(\<lambda>x. f x / h x) \<in> L(\<lambda>x. g x) \<longleftrightarrow> f \<in> L(\<lambda>x. g x * h x)"
proof-
  have "L(\<lambda>x. g x) = L(\<lambda>x. g x * h x / h x)"
    using assms by (intro cong) (auto elim: eventually_mono)
  thus ?thesis by (simp only: divide_right_iff assms)
qed

lemma inverse_flip:
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  assumes "eventually (\<lambda>x. h x \<noteq> 0) at_top"
  assumes "(\<lambda>x. inverse (g x)) \<in> L(h)"
  shows   "(\<lambda>x. inverse (h x)) \<in> L(g)"
using assms by (simp add: divide_eq1 divide_eq2 inverse_eq_divide mult.commute)

lemma lift_trans:
  assumes "f \<in> L(g)"
  assumes "(\<lambda>x. t x (g x)) \<in> L(h)"
  assumes "\<And>f g. f \<in> L(g) \<Longrightarrow> (\<lambda>x. t x (f x)) \<in> L(\<lambda>x. t x (g x))"
  shows   "(\<lambda>x. t x (f x)) \<in> L(h)"
  by (rule trans[OF assms(3)[OF assms(1)] assms(2)])

lemma lift_trans':
  assumes "f \<in> L(\<lambda>x. t x (g x))"
  assumes "g \<in> L(h)"
  assumes "\<And>g h. g \<in> L(h) \<Longrightarrow> (\<lambda>x. t x (g x)) \<in> L(\<lambda>x. t x (h x))"
  shows   "f \<in> L(\<lambda>x. t x (h x))"
  by (rule trans[OF assms(1) assms(3)[OF assms(2)]])

lemma lift_trans_bigtheta:
  assumes "f \<in> L(g)"
  assumes "(\<lambda>x. t x (g x)) \<in> \<Theta>(h)"
  assumes "\<And>f g. f \<in> L(g) \<Longrightarrow> (\<lambda>x. t x (f x)) \<in> L(\<lambda>x. t x (g x))"
  shows   "(\<lambda>x. t x (f x)) \<in> L(h)"
  using cong_bigtheta[OF assms(2)] assms(3)[OF assms(1)] by simp

lemma lift_trans_bigtheta':
  assumes "f \<in> L(\<lambda>x. t x (g x))"
  assumes "g \<in> \<Theta>(h)"
  assumes "\<And>g h. g \<in> \<Theta>(h) \<Longrightarrow> (\<lambda>x. t x (g x)) \<in> \<Theta>(\<lambda>x. t x (h x))"
  shows   "f \<in> L(\<lambda>x. t x (h x))"
  using cong_bigtheta[OF assms(3)[OF assms(2)]] assms(1)  by simp

end


text {* 
  The symbols $O$ and $o$ and $\Omega$ and $\omega$ are dual, so for many rules, replacing $O$ with 
  $\Omega$, $o$ with $\omega$, and $\leq$ with $\geq$ in a theorem yields another valid theorem.
  The following locale captures this fact.
*}

locale landau_pair = 
  fixes L l :: "(('a::order) \<Rightarrow> ('b :: linordered_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  and   R :: "('b :: linordered_field) \<Rightarrow> 'b \<Rightarrow> bool"
  assumes L_def: "L g = {f. \<exists>c>0. eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>g x\<bar>)) at_top}"
  and     l_def: "l g = {f. \<forall>c>0. eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>g x\<bar>)) at_top}"
  and     R:     "R = op \<le> \<or> R = op \<ge>"

interpretation landau_o: landau_pair bigo smallo "op \<le>"
  by unfold_locales (auto simp: bigo_def smallo_def intro!: ext)

interpretation landau_omega: landau_pair bigomega smallomega "op \<ge>"
  by unfold_locales (auto simp: bigomega_def smallomega_def intro!: ext)


context landau_pair
begin

lemmas R_E = disjE[OF R]

lemma bigI:
  "c > 0 \<Longrightarrow> eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>g x\<bar>)) at_top \<Longrightarrow> f \<in> L(g)"
  unfolding L_def by blast

lemma bigE:
  assumes "f \<in> L(g)"
  obtains c where "c > 0" "eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>g x\<bar>)) at_top"
  using assms unfolding L_def by blast

lemma bigE_nonneg:
  assumes "f \<in> L(g)" "eventually (\<lambda>x. f x \<ge> 0) at_top"
  obtains c where "c > 0" "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) at_top"
proof-
  from assms(1) guess c by (rule bigE) note c = this
  from c(2) assms(2) have "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) at_top"
    by eventually_elim simp
  from c(1) and this show ?thesis by (rule that)
qed

lemma smallI:
  "(\<And>c. c > 0 \<Longrightarrow> eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>g x\<bar>)) at_top) \<Longrightarrow> f \<in> l(g)"
  unfolding l_def by blast

lemma smallD:
  "f \<in> l(g) \<Longrightarrow> c > 0 \<Longrightarrow> eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>g x\<bar>)) at_top"
  using assms unfolding l_def by blast

lemma smallD_nonneg:
  assumes "f \<in> l(g)" "eventually (\<lambda>x. f x \<ge> 0) at_top" "c > 0"
  shows   "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) at_top"
  using smallD[OF assms(1,3)] assms(2) by eventually_elim simp


lemma small_imp_big: "f \<in> l(g) \<Longrightarrow> f \<in> L(g)"
  by (rule bigI[OF _ smallD, of 1]) simp_all
  
lemma small_subset_big: "l(g) \<subseteq> L(g)"
  using small_imp_big by blast

lemma R_refl [simp]: "R x x" using R by auto

lemma R_linear: "\<not>R x y \<Longrightarrow> R y x"
  using R by auto

lemma R_trans [trans]: "R a b \<Longrightarrow> R b c \<Longrightarrow> R a c"
  using R by auto

lemma R_mult_left_mono: "R a b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> R (c*a) (c*b)"
  using R by (auto simp: mult_left_mono)

lemma R_mult_right_mono: "R a b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> R (a*c) (b*c)"
  using R by (auto simp: mult_right_mono)

lemma big_trans:
  assumes "f \<in> L(g)" "g \<in> L(h)"
  shows   "f \<in> L(h)"
proof-
  from assms(1) guess c by (elim bigE) note c = this
  from assms(2) guess d by (elim bigE) note d = this
  from c(2) d(2) have "eventually (\<lambda>x. R \<bar>f x\<bar> (c * d * \<bar>h x\<bar>)) at_top"
  proof eventually_elim
    fix x assume "R \<bar>f x\<bar> (c * \<bar>g x\<bar>)"
    also assume "R \<bar>g x\<bar> (d * \<bar>h x\<bar>)"
    with c(1) have "R (c * \<bar>g x\<bar>) (c * (d * \<bar>h x\<bar>))"
      by (intro R_mult_left_mono) simp_all
    finally show "R \<bar>f x\<bar> (c * d * \<bar>h x\<bar>)" by (simp add: algebra_simps)
  qed
  with c(1) d(1) show ?thesis by (intro bigI[of "c*d"]) simp_all
qed

lemma big_small_trans:
  assumes "f \<in> L(g)" "g \<in> l(h)"
  shows   "f \<in> l(h)"
proof (rule smallI)
  fix c :: 'b assume c: "c > 0"
  from assms(1) guess d by (elim bigE) note d = this
  note d(2)
  moreover from c d assms(2) have "eventually (\<lambda>x. R \<bar>g x\<bar> (c * inverse d * \<bar>h x\<bar>)) at_top" 
    by (intro smallD) simp_all
  ultimately show "eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>h x\<bar>)) at_top"
    by eventually_elim (erule R_trans, insert R d(1), auto simp: field_simps)
qed

lemma small_big_trans:
  assumes "f \<in> l(g)" "g \<in> L(h)"
  shows   "f \<in> l(h)"
proof (rule smallI)
  fix c :: 'b assume c: "c > 0"
  from assms(2) guess d by (elim bigE) note d = this
  note d(2)
  moreover from c d assms(1) have "eventually (\<lambda>x. R \<bar>f x\<bar> (c * inverse d * \<bar>g x\<bar>)) at_top" 
    by (intro smallD) simp_all
  ultimately show "eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>h x\<bar>)) at_top"
    by eventually_elim (rotate_tac 2, erule R_trans, insert R c d(1), auto simp: field_simps)
qed

lemma small_trans:
  "f \<in> l(g) \<Longrightarrow> g \<in> l(h) \<Longrightarrow> f \<in> l(h)"
  by (rule big_small_trans[OF small_imp_big])

lemma small_big_trans':
  "f \<in> l(g) \<Longrightarrow> g \<in> L(h) \<Longrightarrow> f \<in> L(h)"
  by (rule small_imp_big[OF small_big_trans])

lemma big_small_trans':
  "f \<in> L(g) \<Longrightarrow> g \<in> l(h) \<Longrightarrow> f \<in> L(h)"
  by (rule small_imp_big[OF big_small_trans])

lemma big_subsetI [intro]: "f \<in> L(g) \<Longrightarrow> L(f) \<subseteq> L(g)"
  by (intro subsetI) (drule (1) big_trans)

lemma small_subsetI [intro]: "f \<in> L(g) \<Longrightarrow> l(f) \<subseteq> l(g)"
  by (intro subsetI) (drule (1) small_big_trans)

lemma big_refl [simp]: "f \<in> L(f)"
  by (rule bigI[of 1]) simp_all

lemma small_refl_iff: "f \<in> l(f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
proof (rule iffI[OF _ smallI])
  assume f: "f \<in> l f"
  have "(1/2::'b) > 0" "(2::'b) > 0" by simp_all
  from smallD[OF f this(1)] smallD[OF f this(2)]
    show "eventually (\<lambda>x. f x = 0) at_top" by eventually_elim (insert R, auto)
next
  fix c :: 'b assume "c > 0" "eventually (\<lambda>x. f x = 0) at_top"
  from this(2) show "eventually (\<lambda>x. R \<bar>f x\<bar> (c * \<bar>f x\<bar>)) at_top"
    by eventually_elim simp_all
qed

lemma big_small_asymmetric: "f \<in> L(g) \<Longrightarrow> g \<in> l(f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) at_top"
  by (drule (1) big_small_trans) (simp add: small_refl_iff)

lemma small_big_asymmetric: "f \<in> l(g) \<Longrightarrow> g \<in> L(f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) at_top"
  by (drule (1) small_big_trans) (simp add: small_refl_iff)

lemma small_asymmetric: "f \<in> l(g) \<Longrightarrow> g \<in> l(f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) at_top"
  by (drule (1) small_trans) (simp add: small_refl_iff)


lemma plus_aux:
  assumes "f \<in> o(g)"
  shows "g \<in> L (\<lambda>x. f x + g x)"
proof (rule R_E)
  assume [simp]: "R = op \<le>"
  have A: "1/2 > (0::'b)" by simp
  {
    fix x assume "\<bar>f x\<bar> \<le> 1/2 * \<bar>g x\<bar>"
    hence "1/2 * \<bar>g x\<bar> \<le> \<bar>g x\<bar> - \<bar>f x\<bar>" by simp
    also have "\<bar>g x\<bar> - \<bar>f x\<bar> \<le> \<bar>f x + g x\<bar>" by simp
    finally have "1/2 * \<bar>g x\<bar> \<le> \<bar>f x + g x\<bar>" by simp
  } note B = this
  
  show "g \<in> L(\<lambda>x. f x + g x)"
    apply (rule bigI[of "2"], simp)
    using landau_o.smallD[OF assms A] apply eventually_elim
    using B apply (simp add: algebra_simps) 
    done
next
  assume [simp]: "R = (\<lambda>x y. x \<ge> y)"
  show "g \<in> L(\<lambda>x. f x + g x)"
  apply (rule bigI[of "1/2"], simp)
  using landau_o.smallD[OF assms zero_less_one] apply eventually_elim
  apply (auto simp: algebra_simps)
  done
qed

end



lemma bigomega_iff_bigo: "g \<in> \<Omega>(f) \<longleftrightarrow> f \<in> O(g)"
proof
  assume "f \<in> O(g)"
  then guess c by (elim landau_o.bigE)
  thus "g \<in> \<Omega>(f)" by (intro landau_omega.bigI[of "inverse c"]) (simp_all add: field_simps)
next
  assume "g \<in> \<Omega>(f)"
  then guess c by (elim landau_omega.bigE)
  thus "f \<in> O(g)" by (intro landau_o.bigI[of "inverse c"]) (simp_all add: field_simps)
qed

lemma smallomega_iff_smallo: "g \<in> \<omega>(f) \<longleftrightarrow> f \<in> o(g)"
proof
  assume "f \<in> o(g)"
  from landau_o.smallD[OF this, of "inverse c" for c]
    show "g \<in> \<omega>(f)" by (intro landau_omega.smallI) (simp_all add: field_simps)
next
  assume "g \<in> \<omega>(f)"
  from landau_omega.smallD[OF this, of "inverse c" for c]
    show "f \<in> o(g)" by (intro landau_o.smallI) (simp_all add: field_simps)
qed


context landau_pair
begin

lemma big_mono:
  "eventually (\<lambda>x. R \<bar>f x\<bar> \<bar>g x\<bar>) at_top \<Longrightarrow> f \<in> L(g)"
  by (rule bigI[OF zero_less_one]) simp

lemma big_mult:
  assumes "f1 \<in> L(g1)" "f2 \<in> L(g2)"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L(\<lambda>x. g1 x * g2 x)"
proof-
  from assms(1) guess c1 by (elim bigE) note c1 = this
  from assms(2) guess c2 by (elim bigE) note c2 = this
  
  from c1(1) and c2(1) have "c1 * c2 > 0" by simp
  moreover from c1(2) and c2(2) 
    have "eventually (\<lambda>x. R \<bar>f1 x * f2 x\<bar> (c1 * c2 * \<bar>g1 x * g2 x\<bar>)) at_top"
      apply (eventually_elim)
      apply (rule R_E)    
      apply (hypsubst, drule (1) mult_mono, insert c1(1) c2(1), 
             simp, simp, simp add: abs_mult algebra_simps)+
      done
  ultimately show ?thesis by (rule bigI)
qed

lemma small_big_mult:
  assumes "f1 \<in> l(g1)" "f2 \<in> L(g2)"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> l(\<lambda>x. g1 x * g2 x)"
proof (rule smallI)
  fix c1 :: 'b assume c1: "c1 > 0"
  from assms(2) guess c2 by (elim bigE) note c2 = this
  with c1 assms(1) have "eventually (\<lambda>x. R \<bar>f1 x\<bar> (c1 * inverse c2 * \<bar>g1 x\<bar>)) at_top"
    by (auto intro!: smallD)
  with c2(2) show "eventually (\<lambda>x. R \<bar>f1 x * f2 x\<bar> (c1 * \<bar>g1 x * g2 x\<bar>)) at_top"
    apply eventually_elim
    apply (rule R_E, insert c1(1) c2(1))
    apply (hypsubst, drule (1) mult_mono, simp, simp, simp add: abs_mult field_simps)+
    done
qed

lemma big_small_mult: "f1 \<in> L(g1) \<Longrightarrow> f2 \<in> l(g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> l(\<lambda>x. g1 x * g2 x)"
  by (subst (1 2) mult.commute) (rule small_big_mult)

lemma small_mult: "f1 \<in> l(g1) \<Longrightarrow> f2 \<in> l(g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> l(\<lambda>x. g1 x * g2 x)"
  by (rule small_big_mult, assumption, rule small_imp_big)

lemmas mult = big_mult small_big_mult big_small_mult small_mult


sublocale big: landau_symbol L
proof
  have L: "L = bigo \<or> L = bigomega"
    apply (rule R_E)
    apply (rule disjI1, rule ext, simp add: bigo_def L_def)
    apply (rule disjI2, rule ext, simp add: bigomega_def L_def)
    done
  {
    fix c :: 'b and f :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    hence "(\<lambda>x. c * f x) \<in> L f" by (intro bigI[of "\<bar>c\<bar>"]) (simp_all add: abs_mult)
  } note A = this
  {
    fix c :: 'b and f :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"] 
      show "L (\<lambda>x. c * f x) = L f" by (intro equalityI big_subsetI) (simp_all add: field_simps)
  }
  {
    fix c :: 'b and f g :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
      have "(\<lambda>x. c * f x) \<in> L f" "f \<in> L (\<lambda>x. c * f x)" by (simp_all add: field_simps)
    thus "((\<lambda>x. c * f x) \<in> L g) = (f \<in> L g)" by (intro iffI) (erule (1) big_trans)+
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "f \<in> L(g)"
    assume B: "eventually (\<lambda>x. f x \<noteq> 0) at_top" "eventually (\<lambda>x. g x \<noteq> 0) at_top"
    from A guess c by (elim bigE) note c = this
    from c(2) B have "eventually (\<lambda>x. R \<bar>inverse (g x)\<bar> (c * \<bar>inverse (f x)\<bar>)) at_top"
      by eventually_elim (rule R_E, insert c(1), simp_all add: field_simps)
    with c(1) show "(\<lambda>x. inverse (g x)) \<in> L(\<lambda>x. inverse (f x))" by (rule bigI)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume "f \<in> o(g)"
    with plus_aux show "L g \<subseteq> L (\<lambda>x. f x + g x)" by (blast intro!: big_subsetI) 
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "eventually (\<lambda>x. f x = g x) at_top"
    show "L(f) = L(g)" unfolding L_def by (subst eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" assume A: "eventually (\<lambda>x. f x = g x) at_top"
    show "f \<in> L(h) \<longleftrightarrow> g \<in> L(h)" unfolding L_def mem_Collect_eq
      by (subst (1) eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume "f \<in> L g" thus "L f \<subseteq> L g" by (rule big_subsetI)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "f \<in> \<Theta>(g)"
    with A L show "L(f) = L(g)" unfolding bigtheta_def
      by (intro equalityI big_subsetI) (auto simp: bigomega_iff_bigo)
    fix h:: "'a \<Rightarrow> 'b"
    show "f \<in> L(h) \<longleftrightarrow> g \<in> L(h)" by (rule disjE[OF L]) 
      (insert A, auto simp: bigtheta_def bigomega_iff_bigo intro: landau_o.big_trans)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" assume "f \<in> L g"
    thus "(\<lambda>x. h x * f x) \<in> L (\<lambda>x. h x * g x)" by (intro big_mult) simp
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" assume "f \<in> L g" "g \<in> L h"
    thus "f \<in> L(h)" by (rule big_trans)
  }
qed (auto simp: L_def)

sublocale small: landau_symbol l
proof
  {
    fix c :: 'b and f :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    hence "(\<lambda>x. c * f x) \<in> L f" by (intro bigI[of "\<bar>c\<bar>"]) (simp_all add: abs_mult)
  } note A = this
  {
    fix c :: 'b and f :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"] 
      show "l (\<lambda>x. c * f x) = l f" by (intro equalityI small_subsetI) (simp_all add: field_simps)
  }
  {
    fix c :: 'b and f g :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
      have "(\<lambda>x. c * f x) \<in> L f" "f \<in> L (\<lambda>x. c * f x)" by (simp_all add: field_simps)
    thus "((\<lambda>x. c * f x) \<in> l g) = (f \<in> l g)" by (intro iffI) (erule (1) big_small_trans)+
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume "f \<in> o(g)"
    with plus_aux show "l g \<subseteq> l (\<lambda>x. f x + g x)" by (blast intro!: small_subsetI) 
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "f \<in> l(g)"
    assume B: "eventually (\<lambda>x. f x \<noteq> 0) at_top" "eventually (\<lambda>x. g x \<noteq> 0) at_top"
    show "(\<lambda>x. inverse (g x)) \<in> l(\<lambda>x. inverse (f x))"
    proof (rule smallI)
      fix c :: 'b assume c: "c > 0"
      from B smallD[OF A c] show "eventually (\<lambda>x. R \<bar>inverse (g x)\<bar> (c * \<bar>inverse (f x)\<bar>)) at_top"
        by eventually_elim (rule R_E, simp_all add: field_simps)
    qed
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "eventually (\<lambda>x. f x = g x) at_top"
    show "l(f) = l(g)" unfolding l_def by (subst eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" assume A: "eventually (\<lambda>x. f x = g x) at_top"
    show "f \<in> l(h) \<longleftrightarrow> g \<in> l(h)" unfolding l_def mem_Collect_eq
      by (subst (1) eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume "f \<in> l g" thus "l f \<subseteq> l g" by (intro small_subsetI small_imp_big)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "f \<in> \<Theta>(g)"
    have "L = bigo \<or> L = bigomega"
      apply (rule R_E)
      apply (rule disjI1, rule ext, simp add: bigo_def L_def)
      apply (rule disjI2, rule ext, simp add: bigomega_def L_def)
      done
    with A show "l(f) = l(g)" unfolding bigtheta_def
      by (intro equalityI small_subsetI) (auto simp: bigomega_iff_bigo)
    have l: "l = smallo \<or> l = smallomega"
      apply (rule R_E)
      apply (rule disjI1, rule ext, simp add: smallo_def l_def)
      apply (rule disjI2, rule ext, simp add: smallomega_def l_def)
      done
    fix h:: "'a \<Rightarrow> 'b"
    show "f \<in> l(h) \<longleftrightarrow> g \<in> l(h)" by (rule disjE[OF l]) 
      (insert A, auto simp: bigtheta_def bigomega_iff_bigo smallomega_iff_smallo 
       intro: landau_o.big_small_trans landau_o.small_big_trans)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" assume "f \<in> l g"
    thus "(\<lambda>x. h x * f x) \<in> l (\<lambda>x. h x * g x)" by (intro big_small_mult) simp
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" assume "f \<in> l g" "g \<in> l h"
    thus "f \<in> l(h)" by (rule small_trans)
  }
qed (auto simp: l_def)


text {* These rules allow chaining of Landau symbol propositions in Isar with "also".*}

lemma big_mult_1:    "f \<in> L(g) \<Longrightarrow> (\<lambda>_. 1) \<in> L(h) \<Longrightarrow> f \<in> L(\<lambda>x. g x * h x)"
  and big_mult_1':   "(\<lambda>_. 1) \<in> L(g) \<Longrightarrow> f \<in> L(h) \<Longrightarrow> f \<in> L(\<lambda>x. g x * h x)"
  and small_mult_1:  "f \<in> l(g) \<Longrightarrow> (\<lambda>_. 1) \<in> L(h) \<Longrightarrow> f \<in> l(\<lambda>x. g x * h x)"
  and small_mult_1': "(\<lambda>_. 1) \<in> L(g) \<Longrightarrow> f \<in> l(h) \<Longrightarrow> f \<in> l(\<lambda>x. g x * h x)"
  and small_mult_1'':  "f \<in> L(g) \<Longrightarrow> (\<lambda>_. 1) \<in> l(h) \<Longrightarrow> f \<in> l(\<lambda>x. g x * h x)"
  and small_mult_1''': "(\<lambda>_. 1) \<in> l(g) \<Longrightarrow> f \<in> L(h) \<Longrightarrow> f \<in> l(\<lambda>x. g x * h x)"
  by (drule (1) big.mult big_small_mult small_big_mult, simp)+

lemma big_1_mult:    "f \<in> L(g) \<Longrightarrow> h \<in> L(\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L(g)"
  and big_1_mult':   "h \<in> L(\<lambda>_. 1) \<Longrightarrow> f \<in> L(g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L(g)"
  and small_1_mult:  "f \<in> l(g) \<Longrightarrow> h \<in> L(\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l(g)"
  and small_1_mult': "h \<in> L(\<lambda>_. 1) \<Longrightarrow> f \<in> l(g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l(g)"
  and small_1_mult'':  "f \<in> L(g) \<Longrightarrow> h \<in> l(\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l(g)"
  and small_1_mult''': "h \<in> l(\<lambda>_. 1) \<Longrightarrow> f \<in> L(g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l(g)"
  by (drule (1) big.mult big_small_mult small_big_mult, simp)+

lemmas mult_1_trans = 
  big_mult_1 big_mult_1' small_mult_1 small_mult_1' small_mult_1'' small_mult_1'''
  big_1_mult big_1_mult' small_1_mult small_1_mult' small_1_mult'' small_1_mult'''

lemma big_equal_iff_bigtheta: "L(f) = L(g) \<longleftrightarrow> f \<in> \<Theta>(g)"
proof
  have L: "L = bigo \<or> L = bigomega"
    apply (rule R_E)
    apply (rule disjI1, rule ext, simp add: bigo_def L_def)
    apply (rule disjI2, rule ext, simp add: bigomega_def L_def)
    done
  fix f g :: "'a \<Rightarrow> 'b" assume "L(f) = L(g)"
  with big_refl[of f] big_refl[of g] have "f \<in> L(g)" "g \<in> L(f)" by simp_all
  thus "f \<in> \<Theta>(g)" using L unfolding bigtheta_def by (auto simp: bigomega_iff_bigo)
qed (rule big.cong_bigtheta)

end


context landau_symbol
begin

lemma plus_absorb1:
  assumes "f \<in> o(g)"
  shows   "L(\<lambda>x. f x + g x) = L(g)"
proof (intro equalityI)
  from plus_subset1 and assms show "L g \<subseteq> L (\<lambda>x. f x + g x)" .
  from landau_o.small.plus_subset1[OF assms] and assms have "(\<lambda>x. -f x) \<in> o(\<lambda>x. f x + g x)"
    by (auto simp: landau_o.small.uminus_in_iff)
  from plus_subset1[OF this] show "L(\<lambda>x. f x + g x) \<subseteq> L(g)" by simp
qed

lemma plus_absorb2: "g \<in> o(f) \<Longrightarrow> L(\<lambda>x. f x + g x) = L(f)"
  using plus_absorb1[of g f] by (simp add: add.commute)

lemma diff_absorb1: "f \<in> o(g) \<Longrightarrow> L(\<lambda>x. f x - g x) = L(g)"
  by (simp only: diff_conv_add_uminus plus_absorb1 landau_o.small.uminus uminus)

lemma diff_absorb2: "g \<in> o(f) \<Longrightarrow> L(\<lambda>x. f x - g x) = L(f)"
  by (simp only: diff_conv_add_uminus plus_absorb2 landau_o.small.uminus_in_iff)

lemmas absorb = plus_absorb1 plus_absorb2 diff_absorb1 diff_absorb2

end


lemma bigthetaI [intro]: "f \<in> O(g) \<Longrightarrow> f \<in> \<Omega>(g) \<Longrightarrow> f \<in> \<Theta>(g)"
  unfolding bigtheta_def bigomega_def by blast

lemma bigthetaD1 [dest]: "f \<in> \<Theta>(g) \<Longrightarrow> f \<in> O(g)" and bigthetaD2 [dest]: "f \<in> \<Theta>(g) \<Longrightarrow> f \<in> \<Omega>(g)"
  unfolding bigtheta_def bigo_def bigomega_def by blast+

lemma bigtheta_refl [simp]: "f \<in> \<Theta>(f)"
  unfolding bigtheta_def by simp

lemma bigtheta_sym: "f \<in> \<Theta>(g) \<longleftrightarrow> g \<in> \<Theta>(f)"
  unfolding bigtheta_def by (auto simp: bigomega_iff_bigo)

lemmas landau_flip =
  bigomega_iff_bigo[symmetric] smallomega_iff_smallo[symmetric]
  bigomega_iff_bigo smallomega_iff_smallo bigtheta_sym


interpretation landau_theta: landau_symbol bigtheta
proof
  fix f g :: "'a \<Rightarrow> 'b"
  assume "f \<in> o(g)"
  hence "O(g) \<subseteq> O(\<lambda>x. f x + g x)" "\<Omega>(g) \<subseteq> \<Omega>(\<lambda>x. f x + g x)"
    by (rule landau_o.big.plus_subset1 landau_omega.big.plus_subset1)+
  thus "\<Theta>(g) \<subseteq> \<Theta>(\<lambda>x. f x + g x)" unfolding bigtheta_def by blast
next
  fix f g :: "'a \<Rightarrow> 'b"  
  assume "f \<in> \<Theta>(g)"
  thus A: "\<Theta>(f) = \<Theta>(g)" 
    apply (subst (1 2) bigtheta_def)
    apply (subst landau_o.big.cong_bigtheta landau_omega.big.cong_bigtheta, assumption)+
    apply (rule refl)
    done
  thus "\<Theta>(f) \<subseteq> \<Theta>(g)" by simp
  fix h :: "'a \<Rightarrow> 'b"
  show "f \<in> \<Theta>(h) \<longleftrightarrow> g \<in> \<Theta>(h)" by (subst (1 2) bigtheta_sym) (simp add: A)
next
  fix f g h :: "'a \<Rightarrow> 'b"
  assume "f \<in> \<Theta>(g)" "g \<in> \<Theta>(h)"
  thus "f \<in> \<Theta>(h)" unfolding bigtheta_def
    by (blast intro: landau_o.big.trans landau_omega.big.trans)
qed (simp_all add: bigtheta_def landau_o.big.abs landau_omega.big.abs 
       landau_o.big.abs_in_iff landau_omega.big.abs_in_iff 
       landau_o.big.cmult landau_omega.big.cmult 
       landau_o.big.cmult_in_iff landau_omega.big.cmult_in_iff 
       landau_o.big.cong landau_omega.big.cong
       landau_o.big.in_cong landau_omega.big.in_cong
       landau_o.big.mult landau_omega.big.mult
       landau_o.big.inverse landau_omega.big.inverse)

lemmas landau_symbols = 
  landau_o.big.landau_symbol landau_o.small.landau_symbol
  landau_omega.big.landau_symbol landau_omega.small.landau_symbol landau_theta.landau_symbol

lemma bigoI [intro]:
  assumes "eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>) at_top"
  shows   "f \<in> O(g)"
proof (rule landau_o.bigI)
  show "max 1 c > 0" by simp
  note assms
  moreover have "\<And>x. c * \<bar>g x\<bar> \<le> max 1 c * \<bar>g x\<bar>" by (simp add: mult_right_mono)
  ultimately show "eventually (\<lambda>x. \<bar>f x\<bar> \<le> max 1 c * \<bar>g x\<bar>) at_top"
    by (auto elim!: eventually_mono dest: order.trans)
qed

declare landau_o.smallI landau_omega.bigI landau_omega.smallI [intro]
declare landau_o.bigE landau_omega.bigE [elim]
declare landau_o.smallD landau_omega.smallD [dest]

lemma (in landau_symbol) bigtheta_trans1': 
  "f \<in> L(g) \<Longrightarrow> h \<in> \<Theta>(g) \<Longrightarrow> f \<in> L(h)"
  by (subst cong_bigtheta[symmetric]) (simp add: bigtheta_sym)

lemma (in landau_symbol) bigtheta_trans2': 
  "g \<in> \<Theta>(f) \<Longrightarrow> g \<in> L(h) \<Longrightarrow> f \<in> L(h)"
  by (rule bigtheta_trans2, subst bigtheta_sym)

lemma bigo_bigomega_trans:      "f \<in> O(g) \<Longrightarrow> h \<in> \<Omega>(g) \<Longrightarrow> f \<in> O(h)"
  and bigo_smallomega_trans:    "f \<in> O(g) \<Longrightarrow> h \<in> \<omega>(g) \<Longrightarrow> f \<in> o(h)"
  and smallo_bigomega_trans:    "f \<in> o(g) \<Longrightarrow> h \<in> \<Omega>(g) \<Longrightarrow> f \<in> o(h)"
  and smallo_smallomega_trans:  "f \<in> o(g) \<Longrightarrow> h \<in> \<omega>(g) \<Longrightarrow> f \<in> o(h)"
  and bigomega_bigo_trans:      "f \<in> \<Omega>(g) \<Longrightarrow> h \<in> O(g) \<Longrightarrow> f \<in> \<Omega>(h)"
  and bigomega_smallo_trans:    "f \<in> \<Omega>(g) \<Longrightarrow> h \<in> o(g) \<Longrightarrow> f \<in> \<omega>(h)"
  and smallomega_bigo_trans:    "f \<in> \<omega>(g) \<Longrightarrow> h \<in> O(g) \<Longrightarrow> f \<in> \<omega>(h)"
  and smallomega_smallo_trans:  "f \<in> \<omega>(g) \<Longrightarrow> h \<in> o(g) \<Longrightarrow> f \<in> \<omega>(h)"
  by (unfold bigomega_iff_bigo smallomega_iff_smallo)
     (erule (1) landau_o.big_trans landau_o.big_small_trans landau_o.small_big_trans 
                landau_o.big_trans landau_o.small_trans)+

lemmas landau_trans_lift [trans] =
  landau_symbols[THEN landau_symbol.lift_trans]
  landau_symbols[THEN landau_symbol.lift_trans']
  landau_symbols[THEN landau_symbol.lift_trans_bigtheta]
  landau_symbols[THEN landau_symbol.lift_trans_bigtheta']

lemmas landau_mult_1_trans [trans] =
  landau_o.mult_1_trans landau_omega.mult_1_trans

lemmas landau_trans [trans] = 
  landau_symbols[THEN landau_symbol.bigtheta_trans1]
  landau_symbols[THEN landau_symbol.bigtheta_trans2]
  landau_symbols[THEN landau_symbol.bigtheta_trans1']
  landau_symbols[THEN landau_symbol.bigtheta_trans2']

  landau_o.big_trans landau_o.small_trans landau_o.small_big_trans landau_o.big_small_trans
  landau_omega.big_trans landau_omega.small_trans 
    landau_omega.small_big_trans landau_omega.big_small_trans

  bigo_bigomega_trans bigo_smallomega_trans smallo_bigomega_trans smallo_smallomega_trans 
  bigomega_bigo_trans bigomega_smallo_trans smallomega_bigo_trans smallomega_smallo_trans



lemma bigtheta_inverse [simp]: 
  fixes  f g :: "('a :: order) \<Rightarrow> ('b :: linordered_field)"
  shows "(\<lambda>x. inverse (f x)) \<in> \<Theta>(\<lambda>x. inverse (g x)) \<longleftrightarrow> f \<in> \<Theta>(g)"
proof-
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "f \<in> \<Theta>(g)"
    then guess c1 c2 :: 'b unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
    note c = this
    from c(3) have "inverse c2 > 0" by simp
    moreover from c(2,4)
      have "eventually (\<lambda>x. \<bar>inverse (f x)\<bar> \<le> inverse c2 * \<bar>inverse (g x)\<bar>) at_top"
    proof eventually_elim
      fix x assume A: "\<bar>f x\<bar> \<le> c1 * \<bar>g x\<bar>" "c2 * \<bar>g x\<bar> \<le> \<bar>f x\<bar>"
      from A c(1,3) have "f x = 0 \<longleftrightarrow> g x = 0" by (auto simp: field_simps mult_le_0_iff)
      with A c(1,3) show "\<bar>inverse (f x)\<bar> \<le> inverse c2 * \<bar>inverse (g x)\<bar>"
        by (force simp: field_simps)
    qed
    ultimately have "(\<lambda>x. inverse (f x)) \<in> O(\<lambda>x. inverse (g x))" by (rule landau_o.bigI)
  }
  thus ?thesis using assms unfolding bigtheta_def 
    by (force simp: bigomega_iff_bigo bigtheta_sym)
qed

lemma bigtheta_divide:
  assumes "f1 \<in> \<Theta>(f2)" "g1 \<in> \<Theta>(g2)"
  shows   "(\<lambda>x. f1 x / g1 x) \<in> \<Theta>(\<lambda>x. f2 x / g2 x)"
  by (subst (1 2) divide_inverse, intro landau_theta.mult) (simp_all add: bigtheta_inverse assms)

lemma bigthetaI':
  assumes "c1 > 0" "c2 > 0"
  assumes "eventually (\<lambda>x. c1 * \<bar>g x\<bar> \<le> \<bar>f x\<bar> \<and> \<bar>f x\<bar> \<le> c2 * \<bar>g x\<bar>) at_top"
  shows   "f \<in> \<Theta>(g)"
apply (rule bigthetaI)
apply (rule landau_o.bigI[OF assms(2)]) using assms(3) apply (eventually_elim, simp)
apply (rule landau_omega.bigI[OF assms(1)]) using assms(3) apply (eventually_elim, simp)
done

lemma eventually_nonzero_bigtheta [simp]:
  assumes "(f :: ('a :: order \<Rightarrow> 'b :: linordered_field)) \<in> \<Theta>(g)"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) at_top \<longleftrightarrow> eventually (\<lambda>x. g x \<noteq> 0) at_top"
proof-
  {
    fix f g :: "'a \<Rightarrow> 'b" assume A: "f \<in> \<Theta>(g)" and B: "eventually (\<lambda>x. f x \<noteq> 0) at_top"
    from A guess c1 c2 unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
    from B this(2,4) have "eventually (\<lambda>x. g x \<noteq> 0) at_top" by eventually_elim auto
  }
  with assms show ?thesis by (force simp: bigtheta_sym)
qed

lemma eventually_nonzero_bigtheta':
  "f \<in> \<Theta>(g) \<Longrightarrow> eventually_nonzero f \<longleftrightarrow> eventually_nonzero g"
  unfolding eventually_nonzero_def by (rule eventually_nonzero_bigtheta)

lemma bigthetaI_cong: "eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> f \<in> \<Theta>(g)"
  by (intro bigthetaI'[of 1 1]) (auto elim!: eventually_mono)

lemma bigtheta_mult_eq:
  fixes f g :: "('a :: order) \<Rightarrow> ('b :: linordered_field)"
  shows "\<Theta>(\<lambda>x. f x * g x) = \<Theta>(f)*\<Theta>(g)"
proof (intro equalityI subsetI)
  fix h assume "h \<in> \<Theta>(f)*\<Theta>(g)"
  thus "h \<in> \<Theta>(\<lambda>x. f x * g x)"
    by (elim set_times_elim, hypsubst, unfold func_times) (erule (1) landau_theta.mult)
next
  fix h assume "h \<in> \<Theta>(\<lambda>x. f x * g x)"
  then guess c1 c2 :: 'b unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
  note c = this

  def h1 \<equiv> "\<lambda>x. if g x = 0 then if f x = 0 then if h x = 0 then h x else 1 else f x else h x / g x"
  def h2 \<equiv> "\<lambda>x. if g x = 0 then if f x = 0 then h x else h x / f x else g x" 

  have "h = h1 * h2" by (intro ext) (auto simp: h1_def h2_def field_simps)
  moreover have "h1 \<in> \<Theta>(f)"
  proof (rule bigthetaI')
    from c(3) show "min c2 1 > 0" by simp
    from c(1) show "max c1 1 > 0" by simp
    from c(2,4) 
      show "eventually (\<lambda>x. min c2 1 * \<bar>f x\<bar> \<le> \<bar>h1 x\<bar> \<and> \<bar>h1 x\<bar> \<le> max c1 1 * \<bar>f x\<bar>) at_top"
      apply eventually_elim
    proof (rule conjI)
      fix x assume A: "\<bar>h x\<bar> \<le> c1 * \<bar>f x * g x\<bar>" and B: "\<bar>h x\<bar> \<ge> c2 * \<bar>f x * g x\<bar>"
      have m: "min c2 1 * \<bar>f x\<bar> \<le> 1 * \<bar>f x\<bar>" by (rule mult_right_mono) simp_all
      have "min c2 1 * \<bar>f x * g x\<bar> \<le> c2 * \<bar>f x * g x\<bar>" by (intro mult_right_mono) simp_all
      also note B
      finally show "\<bar>h1 x\<bar> \<ge> min c2 1 * \<bar>f x\<bar>" using m A
        by (cases "g x = 0") (simp_all add: h1_def abs_mult field_simps)+

      have m: "1 * \<bar>f x\<bar> \<le> max c1 1 * \<bar>f x\<bar>" by (rule mult_right_mono) simp_all
      note A
      also have "c1 * \<bar>f x * g x\<bar> \<le> max c1 1 * \<bar>f x * g x\<bar>" by (intro mult_right_mono) simp_all
      finally show "\<bar>h1 x\<bar> \<le> max c1 1 * \<bar>f x\<bar>" using m A
        by (cases "g x = 0") (simp_all add: h1_def abs_mult field_simps)+
    qed
  qed
  moreover have "h2 \<in> \<Theta>(g)"
  proof (rule bigthetaI')
    from c(3) show "min c2 1 > 0" by simp
    from c(1) show "max c1 1 > 0" by simp
    from c(2,4) 
      show "eventually (\<lambda>x. min c2 1 * \<bar>g x\<bar> \<le> \<bar>h2 x\<bar> \<and> \<bar>h2 x\<bar> \<le> max c1 1 * \<bar>g x\<bar>) at_top"
      apply eventually_elim
    proof (rule conjI)
      fix x assume A: "\<bar>h x\<bar> \<le> c1 * \<bar>f x * g x\<bar>" and B: "\<bar>h x\<bar> \<ge> c2 * \<bar>f x * g x\<bar>"
      have m: "min c2 1 * \<bar>f x\<bar> \<le> 1 * \<bar>f x\<bar>" by (rule mult_right_mono) simp_all
      have "min c2 1 * \<bar>f x * g x\<bar> \<le> c2 * \<bar>f x * g x\<bar>" by (intro mult_right_mono) simp_all
      also note B
      finally show "\<bar>h2 x\<bar> \<ge> min c2 1 * \<bar>g x\<bar>" using m A B
        by (cases "g x = 0") (auto simp: h2_def abs_mult field_simps)+

      have m: "1 * \<bar>g x\<bar> \<le> max c1 1 * \<bar>g x\<bar>" by (rule mult_right_mono) simp_all
      note A
      also have "c1 * \<bar>f x * g x\<bar> \<le> max c1 1 * \<bar>f x * g x\<bar>" by (intro mult_right_mono) simp_all
      finally show "\<bar>h2 x\<bar> \<le> max c1 1 * \<bar>g x\<bar>" using m A
        by (cases "g x = 0") (simp_all add: h2_def abs_mult field_simps)+
    qed
  qed
  ultimately show "h \<in> \<Theta>(f)*\<Theta>(g)" by blast
qed



subsection {* Landau symbols and limits *}

lemma bigoI_tendsto_abs:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "((\<lambda>x. \<bar>f x / g x\<bar>) \<longlongrightarrow> c) at_top"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows   "f \<in> O(g)"
proof (rule bigoI)
  from assms have "eventually (\<lambda>x. dist \<bar>f x / g x\<bar> c < 1) at_top" 
    using tendstoD by force
  thus "eventually (\<lambda>x. \<bar>f x\<bar> \<le> (\<bar>c\<bar> + 1) * \<bar>g x\<bar>) at_top"
    unfolding dist_real_def using assms(2)
  proof eventually_elim
    fix x assume x: "\<bar>\<bar>f x / g x\<bar> - c\<bar> < 1" and g: "g x \<noteq> 0"
    have "\<bar>f x\<bar> - \<bar>c\<bar> * \<bar>g x\<bar> \<le> \<bar>\<bar>f x\<bar> - c * \<bar>g x\<bar>\<bar>"
      by (simp add: abs_mult[symmetric])
    also from g have "... = \<bar>\<bar>g x\<bar>\<bar> * \<bar>\<bar>f x / g x\<bar> - c\<bar>"
      by (subst abs_mult[symmetric]) (simp add: algebra_simps)
    also from x have "\<bar>\<bar>f x / g x\<bar> - c\<bar> \<le> 1" by simp
    hence "\<bar>\<bar>g x\<bar>\<bar> * \<bar>\<bar>f x / g x\<bar> - c\<bar> \<le> \<bar>\<bar>g x\<bar>\<bar> * 1" by (rule mult_left_mono) simp_all
    finally show "\<bar>f x\<bar> \<le> (\<bar>c\<bar> + 1) * \<bar>g x\<bar>" by (simp add: algebra_simps)
  qed
qed

lemma bigoI_tendsto:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> c) at_top"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows   "f \<in> O(g)"
using assms by (intro bigoI_tendsto_abs[of _ _ "\<bar>c\<bar>"] tendsto_rabs)


lemma bigomegaI_tendsto_abs:
  fixes f :: "('a::linorder) \<Rightarrow> real"
  assumes c_not_0:  "(c::real) \<noteq> 0"
  assumes lim:      "((\<lambda>x. \<bar>f x / g x\<bar>) \<longlongrightarrow> c) at_top"
  shows   "f \<in> \<Omega>(g)"
proof (rule landau_omega.bigI)
  from lim have "c \<ge> 0"
    by (rule tendsto_le_const[OF trivial_limit_at_top_linorder]) simp_all
  with c_not_0 have "c > 0" by simp
  with c_not_0 show "c/2 > 0" by simp
  from lim have ev: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> eventually (\<lambda>x. \<bar>\<bar>f x / g x\<bar> - c\<bar> < \<epsilon>) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  from ev[OF `c/2 > 0`] show "eventually (\<lambda>x. \<bar>f x\<bar> \<ge> c/2 * \<bar>g x\<bar>) at_top"
  proof (eventually_elim)
    fix x assume B: "\<bar>\<bar>f x / g x\<bar> - c\<bar> < c/2"
    from B have g: "g x \<noteq> 0" by auto
    from B have "-c/2 < -\<bar>\<bar>f x / g x\<bar> - c\<bar>" by simp
    also have "... \<le> \<bar>f x / g x\<bar> - c" by simp
    finally show "\<bar>f x\<bar> \<ge> c/2 * \<bar>g x\<bar>" using g by (simp add: field_simps abs_mult)
  qed
qed

lemma bigomegaI_tendsto:
  fixes f :: "('a::linorder) \<Rightarrow> real"
  assumes c_not_0:  "(c::real) \<noteq> 0"
  assumes lim:      "((\<lambda>x. f x / g x) \<longlongrightarrow> c) at_top"
  shows   "f \<in> \<Omega>(g)"
using assms by (intro bigomegaI_tendsto_abs[of "\<bar>c\<bar>"] tendsto_rabs) simp_all

lemma smallomegaI_filterlim_at_top:
  fixes f :: "_ \<Rightarrow> real"
  assumes lim: "LIM x at_top. \<bar>f x / g x\<bar> :> at_top"
  shows   "f \<in> \<omega>(g)"
proof (rule landau_omega.smallI)
  fix c :: real assume c_pos: "c > 0"
  from lim have ev: "eventually (\<lambda>x. \<bar>f x / g x\<bar> \<ge> c) at_top"
    by (subst (asm) filterlim_at_top) simp
  thus "eventually (\<lambda>x. \<bar>f x\<bar> \<ge> c * \<bar>g x\<bar>) at_top"
  proof eventually_elim
    fix x assume A: "\<bar>f x / g x\<bar> \<ge> c"
    from A c_pos have "g x \<noteq> 0" by auto
    with A show "\<bar>f x\<bar> \<ge> c * \<bar>g x\<bar>" by (simp add: field_simps)
  qed
qed


lemma smallomegaI_filterlim_at_top':
  fixes f :: "_ \<Rightarrow> real"
  assumes lim: "LIM x at_top. f x / g x :> at_top"
  shows   "f \<in> \<omega>(g)"
proof (rule smallomegaI_filterlim_at_top)
  from lim show "LIM x at_top. \<bar>f x / g x\<bar> :> at_top"
    by (rule filterlim_compose[OF filterlim_abs_real])
qed


lemma smallomegaD_filterlim_at_top:
  fixes f :: "_ \<Rightarrow> real"
  assumes "f \<in> \<omega>(g)"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows   "LIM x at_top. \<bar>f x / g x\<bar> :> at_top"
proof (subst filterlim_at_top_gt, clarify)
  fix c :: real assume c: "c > 0"
  from landau_omega.smallD[OF assms(1) this] assms(2) 
    show "eventually (\<lambda>x. \<bar>f x / g x\<bar> \<ge> c) at_top" by eventually_elim (simp add: field_simps)
qed

lemma smalloI_tendsto:
  fixes f g :: "_ \<Rightarrow> real"
  assumes lim: "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) at_top"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) at_top"
  shows   "f \<in> o(g)"
proof (rule landau_o.smallI)
  fix c :: real assume c_pos: "c > 0"
  from c_pos and lim have ev: "eventually (\<lambda>x. \<bar>f x / g x\<bar> < c) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  with assms(2) show "eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>) at_top"
    by eventually_elim (simp add: field_simps)
qed

lemma smalloD_tendsto:
  assumes "f \<in> o(g)"
  shows   "((\<lambda>x. f x / g x :: real) \<longlongrightarrow> 0) at_top"
unfolding tendsto_iff
proof clarify
  fix e :: real assume e: "e > 0"
  hence "e/2 > 0" by simp
  from landau_o.smallD[OF assms this] show "eventually (\<lambda>x. dist (f x / g x) 0 < e) at_top"
  proof eventually_elim
    fix x assume "\<bar>f x\<bar> \<le> e/2 * \<bar>g x\<bar>"
    with e have "dist (f x / g x) 0 \<le> e/2" 
      by (cases "g x = 0") (simp_all add: dist_real_def field_simps)
    also from e have "... < e" by simp
    finally show "dist (f x / g x) 0 < e" by simp
  qed
qed

lemma bigthetaI_tendsto_abs:
  fixes f g :: "('a::linorder) \<Rightarrow> real"
  assumes c_not_0: "(c::real) \<noteq> 0"
  assumes lim:     "((\<lambda>x. \<bar>f x / g x\<bar>) \<longlongrightarrow> c) at_top"
  shows   "f \<in> \<Theta>(g)"
proof (rule bigthetaI)
  from c_not_0 have "\<bar>c\<bar> > 0" by simp
  with lim have "eventually (\<lambda>x. \<bar>\<bar>f x / g x\<bar> - c\<bar> < \<bar>c\<bar>) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  hence g: "eventually (\<lambda>x. g x \<noteq> 0) at_top" by eventually_elim (auto simp add: field_simps)

  from lim g show "f \<in> O(g)" by (rule bigoI_tendsto_abs)
  from c_not_0 and lim show "f \<in> \<Omega>(g)" by (rule bigomegaI_tendsto_abs)
qed

lemma bigthetaI_tendsto:
  fixes f g :: "('a::linorder) \<Rightarrow> real"
  assumes c_not_0: "(c::real) \<noteq> 0"
  assumes lim:     "((\<lambda>x. f x / g x) \<longlongrightarrow> c) at_top"
  shows   "f \<in> \<Theta>(g)"
  using assms by (intro bigthetaI_tendsto_abs[of "\<bar>c\<bar>"] tendsto_rabs) simp_all

lemma tendsto_add_smallo:
  fixes f1 f2 :: "('a::order) \<Rightarrow> real"
  assumes "(f1 \<longlongrightarrow> a) at_top"
  assumes "f2 \<in> o(f1)"
  shows   "((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) at_top"
proof (subst filterlim_cong[OF refl refl])
  from landau_o.smallD[OF assms(2) zero_less_one] 
    have "eventually (\<lambda>x. \<bar>f2 x\<bar> \<le> \<bar>f1 x\<bar>) at_top" by simp
  thus "eventually (\<lambda>x. f1 x + f2 x = f1 x * (1 + f2 x / f1 x)) at_top"
    by eventually_elim (auto simp: field_simps)
next
  from assms(1) show "((\<lambda>x. f1 x * (1 + f2 x / f1 x)) \<longlongrightarrow> a) at_top"
    by (force intro: tendsto_eq_intros smalloD_tendsto[OF assms(2)])
qed

lemma tendsto_diff_smallo:
  fixes f1 f2 :: "('a::order) \<Rightarrow> real"
  shows "(f1 \<longlongrightarrow> a) at_top \<Longrightarrow> f2 \<in> o(f1) \<Longrightarrow> ((\<lambda>x. f1 x - f2 x) \<longlongrightarrow> a) at_top"
  using tendsto_add_smallo[of f1 a "\<lambda>x. -f2 x"] by simp

lemma tendsto_add_smallo_iff:
  fixes f1 f2 :: "('a::order) \<Rightarrow> real"
  assumes "f2 \<in> o(f1)"
  shows   "(f1 \<longlongrightarrow> a) at_top \<longleftrightarrow> ((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) at_top"
proof
  assume "((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) at_top"
  hence "((\<lambda>x. f1 x + f2 x - f2 x) \<longlongrightarrow> a) at_top"
    by (rule tendsto_diff_smallo) (simp add: landau_o.small.plus_absorb2 assms)
  thus "(f1 \<longlongrightarrow> a) at_top" by simp
qed (rule tendsto_add_smallo[OF _ assms])

lemma tendsto_diff_smallo_iff:
  fixes f1 f2 :: "('a::order) \<Rightarrow> real"
  shows "f2 \<in> o(f1) \<Longrightarrow> (f1 \<longlongrightarrow> a) at_top \<longleftrightarrow> ((\<lambda>x. f1 x - f2 x) \<longlongrightarrow> a) at_top"
  using tendsto_add_smallo_iff[of "\<lambda>x. -f2 x" f1 a] by simp

lemma tendsto_divide_smallo:
  fixes f1 f2 g1 g2 :: "('a::order) \<Rightarrow> real"
  assumes "((\<lambda>x. f1 x / g1 x) \<longlongrightarrow> a) at_top"
  assumes "f2 \<in> o(f1)" "g2 \<in> o(g1)"
  assumes "eventually (\<lambda>x. g1 x \<noteq> 0) at_top"
  shows   "((\<lambda>x. (f1 x + f2 x) / (g1 x + g2 x)) \<longlongrightarrow> a) at_top" (is "(?f \<longlongrightarrow> _) _")
proof (subst tendsto_cong)
  let ?f' = "\<lambda>x. (f1 x / g1 x) * (1 + f2 x / f1 x) / (1 + g2 x / g1 x)"

  have "(?f' \<longlongrightarrow> a * (1 + 0) / (1 + 0)) at_top"
  by (rule tendsto_mult tendsto_divide tendsto_add assms tendsto_const 
        smalloD_tendsto[OF assms(2)] smalloD_tendsto[OF assms(3)])+ simp_all
  thus "(?f' \<longlongrightarrow> a) at_top" by simp

  have "(1/2::real) > 0" by simp
  from landau_o.smallD[OF assms(2) this] landau_o.smallD[OF assms(3) this]
    have "eventually (\<lambda>x. \<bar>f2 x\<bar> \<le> \<bar>f1 x\<bar>/2) at_top"
         "eventually (\<lambda>x. \<bar>g2 x\<bar> \<le> \<bar>g1 x\<bar>/2) at_top" by simp_all
  with assms(4) show "eventually (\<lambda>x. ?f x = ?f' x) at_top"
  proof eventually_elim
    fix x assume A: "\<bar>f2 x\<bar> \<le> \<bar>f1 x\<bar>/2" and B: "\<bar>g2 x\<bar> \<le> \<bar>g1 x\<bar>/2" and C: "g1 x \<noteq> 0"
    show "?f x = ?f' x"
    proof (cases "f1 x = 0")
      assume D: "f1 x \<noteq> 0"
      from D have "f1 x + f2 x = f1 x * (1 + f2 x/f1 x)" by (simp add: field_simps)
      moreover from C have "g1 x + g2 x = g1 x * (1 + g2 x/g1 x)" by (simp add: field_simps)
      ultimately have "?f x = (f1 x * (1 + f2 x/f1 x)) / (g1 x * (1 + g2 x/g1 x))" by (simp only:)
      also have "... = ?f' x" by simp
      finally show ?thesis .
    qed (insert A, simp)
  qed
qed


lemma bigo_powr:
  fixes f :: "('a::order) \<Rightarrow> real"
  assumes "f \<in> O(g)" "p \<ge> 0"
  shows   "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O(\<lambda>x. \<bar>g x\<bar> powr p)"
proof-
  from assms(1) guess c by (elim landau_o.bigE landau_omega.bigE IntE)
  note c = this
  from c(2) assms(2) have "eventually (\<lambda>x. \<bar>f x\<bar> powr p \<le> (c * \<bar>g x\<bar>) powr p) at_top"
    by (auto elim!: eventually_mono intro!: powr_mono2_ex)
  thus "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O(\<lambda>x. \<bar>g x\<bar> powr p)" using c(1)
    by (intro bigoI[of _ "c powr p"]) (simp_all add: powr_mult)
qed

lemma smallo_powr:
  fixes f :: "('a::order) \<Rightarrow> real"
  assumes "f \<in> o(g)" "p > 0"
  shows   "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> o(\<lambda>x. \<bar>g x\<bar> powr p)"
proof (rule landau_o.smallI)
  fix c :: real assume c: "c > 0"
  hence "c powr (1/p) > 0" by simp
  from landau_o.smallD[OF assms(1) this] 
  show "eventually (\<lambda>x. \<bar>\<bar>f x\<bar> powr p\<bar> \<le> c * \<bar>\<bar>g x\<bar> powr p\<bar>) at_top"
  proof eventually_elim
    fix x assume "\<bar>f x\<bar> \<le> c powr (1 / p) * \<bar>g x\<bar>"
    with assms(2) have "\<bar>f x\<bar> powr p \<le> (c powr (1 / p) * \<bar>g x\<bar>) powr p"
      by (intro powr_mono2_ex) simp_all
    also from assms(2) c have "... = c * \<bar>g x\<bar> powr p"
      by (simp add: field_simps powr_mult powr_powr)
    finally show "\<bar>\<bar>f x\<bar> powr p\<bar> \<le> c * \<bar>\<bar>g x\<bar> powr p\<bar>" by simp
  qed
qed

lemma bigtheta_powr:
  fixes f :: "('a::order) \<Rightarrow> real"
  shows "f \<in> \<Theta>(g) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar> powr p) \<in> \<Theta>(\<lambda>x. \<bar>g x\<bar> powr p)"
apply (cases "p < 0")
apply (subst bigtheta_inverse[symmetric], subst (1 2) powr_minus[symmetric])
unfolding bigtheta_def apply (auto simp: bigomega_iff_bigo intro!: bigo_powr)
done

lemma zero_in_smallo [simp]: "(\<lambda>_. 0) \<in> o(f)"
  by (intro landau_o.smallI) simp_all

lemma zero_in_bigo [simp]: "(\<lambda>_. 0) \<in> O(f)"
  by (intro landau_o.bigI[of 1]) simp_all

lemma in_bigomega_zero [simp]: "f \<in> \<Omega>(\<lambda>x. 0)"
  by (rule landau_omega.bigI[of 1]) simp_all

lemma in_smallomega_zero [simp]: "f \<in> \<omega>(\<lambda>x. 0)"
  by (simp add: smallomega_iff_smallo)


lemma in_smallo_zero_iff [simp]: "f \<in> o(\<lambda>_. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
proof
  assume "f \<in> o(\<lambda>_. 0)"
  from landau_o.smallD[OF this, of 1] show "eventually (\<lambda>x. f x = 0) at_top" by simp
next
  assume "eventually (\<lambda>x. f x = 0) at_top"
  hence "\<forall>c>0. eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>0\<bar>) at_top" by simp
  thus "f \<in> o(\<lambda>_. 0)" unfolding smallo_def by simp
qed

lemma in_bigo_zero_iff [simp]: "f \<in> O(\<lambda>_. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
proof
  assume "f \<in> O(\<lambda>_. 0)"
  thus "eventually (\<lambda>x. f x = 0) at_top" by (elim landau_o.bigE) simp
next
  assume "eventually (\<lambda>x. f x = 0) at_top"
  hence "eventually (\<lambda>x. \<bar>f x\<bar> \<le> 1 * \<bar>0\<bar>) at_top" by simp
  thus "f \<in> O(\<lambda>_. 0)" by (intro landau_o.bigI[of 1]) simp_all
qed

lemma zero_in_smallomega_iff [simp]: "(\<lambda>_. 0) \<in> \<omega>(f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
  by (simp add: smallomega_iff_smallo)

lemma zero_in_bigomega_iff [simp]: "(\<lambda>_. 0) \<in> \<Omega>(f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
  by (simp add: bigomega_iff_bigo)

lemma zero_in_bigtheta_iff [simp]: "(\<lambda>_. 0) \<in> \<Theta>(f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
  unfolding bigtheta_def by simp

lemma in_bigtheta_zero_iff [simp]: "f \<in> \<Theta>(\<lambda>x. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) at_top"
  unfolding bigtheta_def by simp


lemma cmult_in_bigo_iff    [simp]:  "(\<lambda>x. c * f x) \<in> O(g) \<longleftrightarrow> c = 0 \<or> f \<in> O(g)"
  and cmult_in_bigo_iff'   [simp]:  "(\<lambda>x. f x * c) \<in> O(g) \<longleftrightarrow> c = 0 \<or> f \<in> O(g)"
  and cmult_in_smallo_iff  [simp]:  "(\<lambda>x. c * f x) \<in> o(g) \<longleftrightarrow> c = 0 \<or> f \<in> o(g)"
  and cmult_in_smallo_iff' [simp]: "(\<lambda>x. f x * c) \<in> o(g) \<longleftrightarrow> c = 0 \<or> f \<in> o(g)"
  by (cases "c = 0", simp, simp)+

lemma bigo_const [simp]: "(\<lambda>_. c) \<in> O(\<lambda>_. 1)" by (rule bigoI[of _ "\<bar>c\<bar>"]) simp

lemma bigo_const_iff [simp]: "(\<lambda>_::_::linorder. c1) \<in> O(\<lambda>_. c2) \<longleftrightarrow> c1 = 0 \<or> c2 \<noteq> 0"
  by (auto simp: eventually_at_top_linorder)

lemma bigomega_const_iff [simp]: "(\<lambda>_::_::linorder. c1) \<in> \<Omega>(\<lambda>_. c2) \<longleftrightarrow> c1 \<noteq> 0 \<or> c2 = 0"
  by (subst bigomega_iff_bigo, subst bigo_const_iff) blast


lemma smallo_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> o(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> o(\<lambda>x. g (real x))"
  by (force intro!: eventually_nat_real landau_o.smallI dest!: landau_o.smallD)

lemma bigo_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> O(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> O(\<lambda>x. g (real x))"
  by (elim landau_o.bigE, erule landau_o.bigI, erule eventually_nat_real)

lemma smallomega_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<omega>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<omega>(\<lambda>x. g (real x))"
  by (force intro!: eventually_nat_real landau_omega.smallI dest!: landau_omega.smallD)

lemma bigomega_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<Omega>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<Omega>(\<lambda>x. g (real x))"
  by (elim landau_omega.bigE, erule landau_omega.bigI, erule eventually_nat_real)

lemma bigtheta_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<Theta>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<Theta>(\<lambda>x. g (real x))"
  unfolding bigtheta_def using bigo_real_nat_transfer bigomega_real_nat_transfer by blast

lemmas landau_real_nat_transfer [intro] = 
  bigo_real_nat_transfer smallo_real_nat_transfer bigomega_real_nat_transfer 
  smallomega_real_nat_transfer bigtheta_real_nat_transfer


lemma landau_symbol_if_eq [simp]:
  assumes "landau_symbol L"
  shows   "L(\<lambda>x::'a::linordered_semidom. if x = a then f x else g x) = L(g)"
apply (rule landau_symbol.cong[OF assms])
using eventually_ge_at_top[of "a + 1"] less_add_one[of a] apply (auto elim!: eventually_mono)
done

lemmas landau_symbols_if_eq [simp] = landau_symbols[THEN landau_symbol_if_eq]



lemma sum_in_smallo:
  fixes f :: "_ \<Rightarrow> 'b :: linordered_field"
  assumes "f \<in> o(h)" "g \<in> o(h)"
  shows   "(\<lambda>x. f x + g x) \<in> o(h)" "(\<lambda>x. f x - g x) \<in> o(h)"
proof-
  {
    fix f g assume fg: "f \<in> o(h)" "g \<in> o(h)"
    have "(\<lambda>x. f x + g x) \<in> o(h)"
    proof (rule landau_o.smallI)
      fix c :: 'b assume "c > 0"
      hence "c/2 > 0" by simp
      from fg[THEN landau_o.smallD[OF _ this]]
        show "eventually (\<lambda>x. \<bar>f x + g x\<bar> \<le> c * \<bar>h x\<bar>) at_top" by eventually_elim simp_all
    qed
  }
  from this[of f g] this[of f "\<lambda>x. -g x"] assms
    show "(\<lambda>x. f x + g x) \<in> o(h)" "(\<lambda>x. f x - g x) \<in> o(h)" by simp_all
qed

lemma sum_in_bigo:
  fixes f :: "_ \<Rightarrow> 'b :: linordered_field"
  assumes "f \<in> O(h)" "g \<in> O(h)"
  shows   "(\<lambda>x. f x + g x) \<in> O(h)" "(\<lambda>x. f x - g x) \<in> O(h)"
proof-
  {
    fix f g assume fg: "f \<in> O(h)" "g \<in> O(h)"
    from fg(1) guess c1 by (elim landau_o.bigE) note c1 = this
    from fg(2) guess c2 by (elim landau_o.bigE) note c2 = this
    from c1(2) c2(2) have "eventually (\<lambda>x. \<bar>f x + g x\<bar> \<le> (c1 + c2) * \<bar>h x\<bar>) at_top"
      by eventually_elim (simp_all add: algebra_simps)
    hence "(\<lambda>x. f x + g x) \<in> O(h)" by (rule bigoI)
  }
  from this[of f g] this[of f "\<lambda>x. -g x"] assms
    show "(\<lambda>x. f x + g x) \<in> O(h)" "(\<lambda>x. f x - g x) \<in> O(h)" by simp_all
qed


lemma tendsto_ln_over_powr: 
  assumes "(a::real) > 0"
  shows   "((\<lambda>x. ln x / x powr a) \<longlongrightarrow> 0) at_top"
proof (rule lhospital_at_top_at_top)
  from assms show "LIM x at_top. x powr a :> at_top" by (rule powr_at_top)
  show "eventually (\<lambda>x. a * x powr (a - 1) \<noteq> 0) at_top"
    using eventually_gt_at_top[of "0::real"] by eventually_elim (insert assms, simp)
  show "eventually (\<lambda>x::real. (ln has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "0::real"] DERIV_ln by (elim eventually_mono) simp
  show "eventually (\<lambda>x. ((\<lambda>x. x powr a) has_real_derivative a * x powr (a - 1)) (at x)) at_top"
    using eventually_gt_at_top[of "0::real"] DERIV_powr by (elim eventually_mono) simp
  have "eventually (\<lambda>x. inverse a * x powr -a = inverse x / (a*x powr (a-1))) at_top"
    using eventually_gt_at_top[of "0::real"] 
    by (elim eventually_mono) (simp add: field_simps powr_divide2[symmetric] powr_minus)
  moreover from assms have "((\<lambda>x. inverse a * x powr -a) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_ident) simp_all
  ultimately show "((\<lambda>x. inverse x / (a * x powr (a - 1))) \<longlongrightarrow> 0) at_top"
    by (subst (asm) tendsto_cong) simp_all
qed

lemma tendsto_ln_powr_over_powr: 
  assumes "(a::real) > 0" "b > 0"
  shows   "((\<lambda>x. ln x powr a / x powr b) \<longlongrightarrow> 0) at_top"
proof-
  have "eventually (\<lambda>x. ln x powr a / x powr b = (ln x / x powr (b/a)) powr a) at_top"
    using assms eventually_gt_at_top[of "1::real"]
    by (elim eventually_mono) (simp add: powr_divide powr_powr)
  moreover have "eventually (\<lambda>x. 0 < ln x / x powr (b / a)) at_top"
    using eventually_gt_at_top[of "1::real"] by (elim eventually_mono) simp
  with assms have "((\<lambda>x. (ln x / x powr (b/a)) powr a) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_zero_powrI tendsto_ln_over_powr) (simp_all add: eventually_mono)
  ultimately show ?thesis by (subst tendsto_cong) simp_all
qed

lemma tendsto_ln_powr_over_powr': 
  assumes "b > 0"
  shows   "((\<lambda>x::real. ln x powr a / x powr b) \<longlongrightarrow> 0) at_top"
proof (cases "a \<le> 0")
  assume a: "a \<le> 0"
  show ?thesis
  proof (rule tendsto_sandwich[of "\<lambda>_::real. 0"])
    have "eventually (\<lambda>x. ln x powr a \<le> 1) at_top" unfolding eventually_at_top_linorder
    proof (intro allI exI impI)
      fix x :: real assume "x \<ge> exp 1"
      from ln_mono[OF _ less_le_trans[OF _ this] this] have "ln x \<ge> 1" by simp
      hence "ln x powr a \<le> ln (exp 1) powr a" using a by (intro powr_mono2') simp_all
      thus "ln x powr a \<le> 1" by simp
    qed
    thus "eventually (\<lambda>x. ln x powr a / x powr b \<le> x powr -b) at_top"
      by eventually_elim (insert a, simp add: field_simps powr_minus divide_right_mono)
  qed (auto intro!: filterlim_ident tendsto_neg_powr assms)
qed (intro tendsto_ln_powr_over_powr, simp_all add: assms)

lemma tendsto_ln_over_ln:
  assumes "(a::real) > 0" "c > 0"
  shows   "((\<lambda>x. ln (a*x) / ln (c*x)) \<longlongrightarrow> 1) at_top"
proof (rule lhospital_at_top_at_top)
  show "LIM x at_top. ln (c*x) :> at_top"
    by (intro filterlim_compose[OF ln_at_top] filterlim_tendsto_pos_mult_at_top[OF tendsto_const] 
              filterlim_ident assms(2))
  show "eventually (\<lambda>x. ((\<lambda>x. ln (a*x)) has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "inverse a"] assms
    by (auto elim!: eventually_mono intro!: derivative_eq_intros simp: field_simps)
  show "eventually (\<lambda>x. ((\<lambda>x. ln (c*x)) has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "inverse c"] assms
    by (auto elim!: eventually_mono intro!: derivative_eq_intros simp: field_simps)
  show "((\<lambda>x::real. inverse x / inverse x) \<longlongrightarrow> 1) at_top"
    by (subst tendsto_cong[of _ "\<lambda>_. 1"]) (simp_all add: eventually_not_equal)
qed (simp_all add: eventually_not_equal)

lemma tendsto_ln_powr_over_ln_powr:
  assumes "(a::real) > 0" "c > 0"
  shows   "((\<lambda>x. ln (a*x) powr d / ln (c*x) powr d) \<longlongrightarrow> 1) at_top"
proof-
  have "eventually (\<lambda>x. ln (a*x) powr d / ln (c*x) powr d = (ln (a*x) / ln (c*x)) powr d) at_top"
    using assms eventually_gt_at_top[of "max (inverse a) (inverse c)"]
    by (auto elim!: eventually_mono simp: powr_divide field_simps)
  moreover have "((\<lambda>x. (ln (a*x) / ln (c*x)) powr d) \<longlongrightarrow> 1) at_top" using assms
    by (intro tendsto_eq_rhs[OF tendsto_powr[OF tendsto_ln_over_ln tendsto_const]]) simp_all
  ultimately show ?thesis by (subst tendsto_cong)
qed

lemma tendsto_ln_powr_over_ln_powr': 
  "c > 0 \<Longrightarrow> ((\<lambda>x::real. ln x powr d / ln (c*x) powr d) \<longlongrightarrow> 1) at_top"
  using tendsto_ln_powr_over_ln_powr[of 1 c d] by simp

lemma tendsto_ln_powr_over_ln_powr'': 
  "a > 0 \<Longrightarrow> ((\<lambda>x::real. ln (a*x) powr d / ln x powr d) \<longlongrightarrow> 1) at_top"
  using tendsto_ln_powr_over_ln_powr[of _ 1] by simp

lemma bigtheta_const_ln_powr [simp]: "a > 0 \<Longrightarrow> (\<lambda>x::real. ln (a*x) powr d) \<in> \<Theta>(\<lambda>x. ln x powr d)"
  by (intro bigthetaI_tendsto[of 1] tendsto_ln_powr_over_ln_powr'') simp

lemma bigtheta_const_ln_pow [simp]: "a > 0 \<Longrightarrow> (\<lambda>x::real. ln (a*x) ^ d) \<in> \<Theta>(\<lambda>x. ln x ^ d)"
proof-
  assume A: "a > 0"
  hence "(\<lambda>x::real. ln (a*x) ^ d) \<in> \<Theta>(\<lambda>x. ln (a*x) powr real d)"
    by (subst bigtheta_sym, intro bigthetaI_cong powr_realpow_eventually 
         filterlim_compose[OF ln_at_top] 
         filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ filterlim_ident])
  also from A have "(\<lambda>x. ln (a*x) powr real d) \<in> \<Theta>(\<lambda>x. ln x powr real d)" by simp
  also have "(\<lambda>x. ln x powr real d) \<in> \<Theta>(\<lambda>x. ln x ^ d)"
    by (intro bigthetaI_cong powr_realpow_eventually filterlim_compose[OF ln_at_top] filterlim_ident)
  finally show ?thesis .
qed

lemma bigtheta_const_ln [simp]: "a > 0 \<Longrightarrow> (\<lambda>x::real. ln (a*x)) \<in> \<Theta>(\<lambda>x. ln x)"
  using tendsto_ln_over_ln[of a 1]  by (intro bigthetaI_tendsto[of 1]) simp_all



context landau_symbol
begin

lemma mult_cancel_left:
  assumes "f1 \<in> \<Theta>(g1)" and "eventually (\<lambda>x. g1 x \<noteq> 0) at_top"
  notes   [trans] = bigtheta_trans1 bigtheta_trans2
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L(\<lambda>x. g1 x * g2 x) \<longleftrightarrow> f2 \<in> L(g2)"
proof
  assume A: "(\<lambda>x. f1 x * f2 x) \<in> L (\<lambda>x. g1 x * g2 x)"
  from assms have "eventually (\<lambda>x. f1 x \<noteq> 0) at_top" by simp
  hence "f2 \<in> \<Theta>(\<lambda>x. f1 x * f2 x / f1 x)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also from A assms have "(\<lambda>x. f1 x * f2 x / f1 x) \<in> L(\<lambda>x. g1 x * g2 x / f1 x)" 
    by (intro divide_right) simp_all
  also from assms have "(\<lambda>x. g1 x * g2 x / f1 x) \<in> \<Theta>(\<lambda>x. g1 x * g2 x / g1 x)"
    by (intro landau_theta.mult landau_theta.divide) (simp_all add: bigtheta_sym)
  also from assms have "(\<lambda>x. g1 x * g2 x / g1 x) \<in> \<Theta>(g2)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally show "f2 \<in> L(g2)" .
next
  assume "f2 \<in> L(g2)"
  hence "(\<lambda>x. f1 x * f2 x) \<in> L(\<lambda>x. f1 x * g2 x)" by (rule mult_left)
  also have "(\<lambda>x. f1 x * g2 x) \<in> \<Theta>(\<lambda>x. g1 x * g2 x)"
    by (intro landau_theta.mult_right assms)
  finally show "(\<lambda>x. f1 x * f2 x) \<in> L(\<lambda>x. g1 x * g2 x)" .
qed

lemma mult_cancel_right:
  assumes "f2 \<in> \<Theta>(g2)" and "eventually (\<lambda>x. g2 x \<noteq> 0) at_top"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L(\<lambda>x. g1 x * g2 x) \<longleftrightarrow> f1 \<in> L(g1)"
  by (subst (1 2) mult.commute) (rule mult_cancel_left[OF assms])

lemma divide_cancel_right:
  assumes "f2 \<in> \<Theta>(g2)" and "eventually (\<lambda>x. g2 x \<noteq> 0) at_top"
  shows   "(\<lambda>x. f1 x / f2 x) \<in> L(\<lambda>x. g1 x / g2 x) \<longleftrightarrow> f1 \<in> L(g1)"
  by (subst (1 2) divide_inverse, intro mult_cancel_right bigtheta_inverse) (simp_all add: assms)

lemma divide_cancel_left:
  assumes "f1 \<in> \<Theta>(g1)" and "eventually (\<lambda>x. g1 x \<noteq> 0) at_top"
  shows   "(\<lambda>x. f1 x / f2 x) \<in> L(\<lambda>x. g1 x / g2 x) \<longleftrightarrow> (\<lambda>x. inverse (f2 x)) \<in> L(\<lambda>x. inverse (g2 x))"
  by (simp only: divide_inverse mult_cancel_left[OF assms])

end


lemma powr_smallo_iff:
  assumes "filterlim g at_top at_top"
  shows   "(\<lambda>x::'a::linorder. g x powr p :: real) \<in> o(\<lambda>x. g x powr q) \<longleftrightarrow> p < q"
proof-
  from assms have "eventually (\<lambda>x. g x \<ge> 1) at_top" by (force simp: filterlim_at_top)
  hence A: "eventually (\<lambda>x. g x \<noteq> 0) at_top" by eventually_elim simp
  have B: "(\<lambda>x. g x powr q) \<in> O(\<lambda>x. g x powr p) \<Longrightarrow> (\<lambda>x. g x powr p) \<notin> o(\<lambda>x. g x powr q)"
  proof
    assume "(\<lambda>x. g x powr q) \<in> O(\<lambda>x. g x powr p)" "(\<lambda>x. g x powr p) \<in> o(\<lambda>x. g x powr q)"
    from landau_o.big_small_asymmetric[OF this] have "eventually (\<lambda>x. g x = 0) at_top" by simp
    with A have "eventually (\<lambda>_::'a. False) at_top" by eventually_elim simp
    thus False by force
  qed
  show ?thesis
  proof (cases p q rule: linorder_cases)
    assume "p < q"
    hence "(\<lambda>x. g x powr p) \<in> o(\<lambda>x. g x powr q)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp: powr_divide2)
    with `p < q` show ?thesis by auto
  next
    assume "p = q"
    hence "(\<lambda>x. g x powr q) \<in> O(\<lambda>x. g x powr p)" by (auto intro!: bigthetaD1)
    with B `p = q` show ?thesis by auto
  next
    assume "p > q"
    hence "(\<lambda>x. g x powr q) \<in> O(\<lambda>x. g x powr p)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr landau_o.small_imp_big simp: powr_divide2)
    with B `p > q` show ?thesis by auto
  qed
qed

lemma powr_bigo_iff:
  assumes "filterlim g at_top at_top"
  shows   "(\<lambda>x::'a::linorder. g x powr p :: real) \<in> O(\<lambda>x. g x powr q) \<longleftrightarrow> p \<le> q"
proof-
  from assms have "eventually (\<lambda>x. g x \<ge> 1) at_top" by (force simp: filterlim_at_top)
  hence A: "eventually (\<lambda>x. g x \<noteq> 0) at_top" by eventually_elim simp
  have B: "(\<lambda>x. g x powr q) \<in> o(\<lambda>x. g x powr p) \<Longrightarrow> (\<lambda>x. g x powr p) \<notin> O(\<lambda>x. g x powr q)"
  proof
    assume "(\<lambda>x. g x powr q) \<in> o(\<lambda>x. g x powr p)" "(\<lambda>x. g x powr p) \<in> O(\<lambda>x. g x powr q)"
    from landau_o.small_big_asymmetric[OF this] have "eventually (\<lambda>x. g x = 0) at_top" by simp
    with A have "eventually (\<lambda>_::'a. False) at_top" by eventually_elim simp
    thus False by force
  qed
  show ?thesis
  proof (cases p q rule: linorder_cases)
    assume "p < q"
    hence "(\<lambda>x. g x powr p) \<in> o(\<lambda>x. g x powr q)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp: powr_divide2)
    with `p < q` show ?thesis by (auto intro: landau_o.small_imp_big)
  next
    assume "p = q"
    hence "(\<lambda>x. g x powr q) \<in> O(\<lambda>x. g x powr p)" by (auto intro!: bigthetaD1)
    with B `p = q` show ?thesis by auto
  next
    assume "p > q"
    hence "(\<lambda>x. g x powr q) \<in> o(\<lambda>x. g x powr p)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp: powr_divide2)
    with B `p > q` show ?thesis by (auto intro: landau_o.small_imp_big)
  qed
qed

lemma powr_bigtheta_iff: 
  assumes "filterlim g at_top at_top"
  shows   "(\<lambda>x::'a::linorder. g x powr p :: real) \<in> \<Theta>(\<lambda>x. g x powr q) \<longleftrightarrow> p = q"
  using assms unfolding bigtheta_def by (auto simp: bigomega_iff_bigo powr_bigo_iff)



subsection {* Rewriting Landau symbols *}

text {* 
  Since the simplifier does not currently rewriting with relations other than equality,
  but we want to rewrite terms like @{term "\<Theta>(\<lambda>x. log 2 x * x)"} to @{term "\<Theta>(\<lambda>x. ln x * x)"}, 
  we need to bring the term into something that contains @{term "\<Theta>(\<lambda>x. log 2 x)"} and 
  @{term "\<Theta>(\<lambda>x. x)"}, which can then be rewritten individually.
  For this, we introduce the following constants and rewrite rules. The rules are mainly used 
  by the simprocs, but may be useful for manual reasoning occasionally.
*}

definition "set_mult A B = {\<lambda>x. f x * g x |f g. f \<in> A \<and> g \<in> B}"
definition "set_inverse A = {\<lambda>x. inverse (f x) |f. f \<in> A}"
definition "set_divide A B = {\<lambda>x. f x / g x |f g. f \<in> A \<and> g \<in> B}"
definition "set_pow A n = {\<lambda>x. f x ^ n |f. f \<in> A}"
definition "set_powr A y = {\<lambda>x. f x powr y |f. f \<in> A}"

lemma bigtheta_mult_eq_set_mult:
  fixes f g :: "('a :: order) \<Rightarrow> ('b :: linordered_field)"
  shows "\<Theta>(\<lambda>x. f x * g x) = set_mult (\<Theta>(f)) (\<Theta>(g))"
  unfolding bigtheta_mult_eq set_mult_def set_times_def func_times by blast

lemma bigtheta_inverse_eq_set_inverse:
  fixes f :: "('a :: order) \<Rightarrow> ('b :: linordered_field)"
  shows "\<Theta>(\<lambda>x. inverse (f x)) = set_inverse (\<Theta>(f))"
proof (intro equalityI subsetI)
  fix g :: "'a \<Rightarrow> 'b" assume "g \<in> \<Theta>(\<lambda>x. inverse (f x))"
  hence "(\<lambda>x. inverse (g x)) \<in> \<Theta>(\<lambda>x. inverse (inverse (f x)))" by (subst bigtheta_inverse)
  also have "(\<lambda>x. inverse (inverse (f x))) = f" by (rule ext) simp
  finally show "g \<in> set_inverse (\<Theta>(f))" unfolding set_inverse_def by force
next
  fix g :: "'a \<Rightarrow> 'b" assume "g \<in> set_inverse (\<Theta>(f))"
  then obtain g' where "g = (\<lambda>x. inverse (g' x))" "g' \<in> \<Theta>(f)" unfolding set_inverse_def by blast
  hence "(\<lambda>x. inverse (g' x)) \<in> \<Theta>(\<lambda>x. inverse (f x))" by (subst bigtheta_inverse)
  also from `g = (\<lambda>x. inverse (g' x))` have "(\<lambda>x. inverse (g' x)) = g" by (intro ext) simp
  finally show "g \<in> \<Theta>(\<lambda>x. inverse (f x))" .
qed

lemma set_divide_inverse: 
  "set_divide (A :: (_ \<Rightarrow> (_ :: division_ring)) set) B = set_mult A (set_inverse B)"
proof (intro equalityI subsetI)
  fix f assume "f \<in> set_divide A B"
  then obtain g h where "f = (\<lambda>x. g x / h x)" "g \<in> A" "h \<in> B" unfolding set_divide_def by blast
  hence "f = g * (\<lambda>x. inverse (h x))" "(\<lambda>x. inverse (h x)) \<in> set_inverse B"
    unfolding set_inverse_def by (auto simp: divide_inverse)
  with `g \<in> A` show "f \<in> set_mult A (set_inverse B)" unfolding set_mult_def by force
next
  fix f assume "f \<in> set_mult A (set_inverse B)"
  then obtain g h where "f = g * (\<lambda>x. inverse (h x))" "g \<in> A" "h \<in> B"
    unfolding set_times_def set_inverse_def set_mult_def by force
  hence "f = (\<lambda>x. g x / h x)" by (intro ext) (simp add: divide_inverse)
  with `g \<in> A` `h \<in> B` show "f \<in> set_divide A B" unfolding set_divide_def by blast
qed

lemma bigtheta_divide_eq_set_divide:
  fixes f g :: "('a :: order) \<Rightarrow> ('b :: linordered_field)"
  shows "\<Theta>(\<lambda>x. f x / g x) = set_divide (\<Theta>(f)) (\<Theta>(g))"
  by (simp only: set_divide_inverse divide_inverse bigtheta_mult_eq_set_mult 
                 bigtheta_inverse_eq_set_inverse)

primrec bigtheta_pow where
  "bigtheta_pow A 0 = \<Theta>(\<lambda>_. 1)"
| "bigtheta_pow A (Suc n) = set_mult A (bigtheta_pow A n)"

lemma bigtheta_pow_eq_set_pow: "\<Theta>(\<lambda>x. f x ^ n) = bigtheta_pow (\<Theta>(f)) n"
  by (induction n) (simp_all add: bigtheta_mult_eq_set_mult)

definition bigtheta_powr where
  "bigtheta_powr A y = (if y = 0 then {f. \<exists>g\<in>A. eventually_nonneg g \<and> f \<in> \<Theta>(\<lambda>x. g x powr y)} 
     else {f. \<exists>g\<in>A. eventually_nonneg g \<and> (\<forall>x. \<bar>f x\<bar> = g x powr y)})"

lemma bigtheta_powr_eq_set_powr: 
  assumes "eventually_nonneg f"
  shows   "\<Theta>(\<lambda>x. f x powr (y::real)) = bigtheta_powr (\<Theta>(f)) y"
proof (cases "y = 0")
  assume [simp]: "y = 0"
  thus ?thesis
  proof (intro equalityI subsetI)
    fix h assume "h \<in> bigtheta_powr \<Theta>(f) y"
    then obtain g where g: "g \<in> \<Theta>(f)" "eventually_nonneg g" "h \<in> \<Theta>(\<lambda>x. g x powr 0)"
      unfolding bigtheta_powr_def by force
    note this(3)
    also have "(\<lambda>x. g x powr 0) \<in> \<Theta>(\<lambda>x. \<bar>g x\<bar> powr 0)" using assms unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    also from g(1) have "(\<lambda>x. \<bar>g x\<bar> powr 0) \<in> \<Theta>(\<lambda>x. \<bar>f x\<bar> powr 0)" by (rule bigtheta_powr)
    also from g(2) have "(\<lambda>x. f x powr 0) \<in> \<Theta>(\<lambda>x. \<bar>f x\<bar> powr 0)" unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    finally show "h \<in> \<Theta>(\<lambda>x. f x powr y)" by simp
  next
    fix h assume "h \<in> \<Theta>(\<lambda>x. f x powr y)"
    with assms have "\<exists>g\<in>\<Theta>(f). eventually_nonneg g \<and> h \<in> \<Theta>(\<lambda>x. g x powr 0)"
      by (intro bexI[of _ f] conjI) simp_all
    thus "h \<in> bigtheta_powr \<Theta>(f) y" unfolding bigtheta_powr_def by simp
  qed
next
  assume y: "y \<noteq> 0"
  show ?thesis
  proof (intro equalityI subsetI)
    fix h assume h: "h \<in> \<Theta>(\<lambda>x. f x powr y)"
    let ?h' = "\<lambda>x. \<bar>h x\<bar> powr inverse y"
    from bigtheta_powr[OF h, of "inverse y"] y
      have "?h' \<in> \<Theta>(\<lambda>x. f x powr 1)" by (simp add: powr_powr)
    also have "(\<lambda>x. f x powr 1) \<in> \<Theta>(f)" using assms unfolding eventually_nonneg_def 
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    finally have "?h' \<in> \<Theta>(f)" .
    with y have "\<exists>g\<in>\<Theta>(f). eventually_nonneg g \<and> (\<forall>x. \<bar>h x\<bar> = g x powr y)"
      by (intro bexI[of _ ?h']) (simp_all add: powr_powr eventually_nonneg_def)
    thus "h \<in> bigtheta_powr \<Theta>(f) y" using y unfolding bigtheta_powr_def by simp
  next
    fix h assume "h \<in> bigtheta_powr \<Theta>(f) y"
    with y obtain g where A: "g \<in> \<Theta>(f)" "\<And>x. \<bar>h x\<bar> = g x powr y" "eventually_nonneg g"
      unfolding bigtheta_powr_def by force
    from this(3) have "(\<lambda>x. g x powr y) \<in> \<Theta>(\<lambda>x. \<bar>g x\<bar> powr y)" unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    also from A(1) have "(\<lambda>x. \<bar>g x\<bar> powr y) \<in> \<Theta>(\<lambda>x. \<bar>f x\<bar> powr y)" by (rule bigtheta_powr)
    also have "(\<lambda>x. \<bar>f x\<bar> powr y) \<in> \<Theta>(\<lambda>x. f x powr y)" using assms unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    finally have "(\<lambda>x. \<bar>h x\<bar>) \<in> \<Theta>(\<lambda>x. f x powr y)" by (subst A(2))
    thus "(\<lambda>x. h x) \<in> \<Theta>(\<lambda>x. f x powr y)" by simp
  qed
qed


lemmas bigtheta_factors_eq = 
  bigtheta_mult_eq_set_mult bigtheta_inverse_eq_set_inverse bigtheta_divide_eq_set_divide 
  bigtheta_pow_eq_set_pow bigtheta_powr_eq_set_powr

lemmas landau_bigtheta_congs = landau_symbols[THEN landau_symbol.cong_bigtheta]

lemma (in landau_symbol) meta_cong_bigtheta: "\<Theta>(f) \<equiv> \<Theta>(g) \<Longrightarrow> L(f) \<equiv> L(g)"
  using bigtheta_refl[of f] by (intro eq_reflection cong_bigtheta) blast

lemmas landau_bigtheta_meta_congs = landau_symbols[THEN landau_symbol.meta_cong_bigtheta]

(* TODO: Make this work with bigtheta_powr_eq_set_powr *)

end