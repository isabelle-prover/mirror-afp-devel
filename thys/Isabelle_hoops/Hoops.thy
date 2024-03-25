section\<open>Hoops\<close>

text\<open>A @{text hoop} is a naturally ordered @{text "pocrim"} (i.e., a partially ordered commutative
 residuated integral monoid). This structures have been introduced by Büchi and Owens in \<^cite>\<open>"BUCHI1975"\<close>
and constitute the algebraic counterpart of fragments without negation and falsum of some nonclassical logics.\<close>

theory Hoops
  imports Posets
begin

subsection\<open>Definitions\<close>

locale hoop =
  fixes universe :: "'a set" ("A")
  and multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "*\<^sup>A" 60)
  and implication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<rightarrow>\<^sup>A" 60)
  and one :: 'a ("1\<^sup>A")
  assumes mult_closed: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x *\<^sup>A y \<in> A"
  and imp_closed: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<rightarrow>\<^sup>A y \<in> A"
  and one_closed [simp]: "1\<^sup>A \<in> A"
  and mult_comm:  "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x *\<^sup>A y = y *\<^sup>A x"
  and mult_assoc: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x *\<^sup>A (y *\<^sup>A z) = (x *\<^sup>A y) *\<^sup>A z"
  and mult_neutr [simp]: "x \<in> A \<Longrightarrow> x *\<^sup>A 1\<^sup>A = x" 
  and imp_reflex [simp]: "x \<in> A \<Longrightarrow> x \<rightarrow>\<^sup>A x = 1\<^sup>A" 
  and divisibility: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x *\<^sup>A (x \<rightarrow>\<^sup>A y) = y *\<^sup>A (y \<rightarrow>\<^sup>A x)" 
  and residuation: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow>
                    x \<rightarrow>\<^sup>A (y \<rightarrow>\<^sup>A z) = (x *\<^sup>A y) \<rightarrow>\<^sup>A z"
begin

definition hoop_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<le>\<^sup>A" 60)
  where "x \<le>\<^sup>A y \<equiv> (x \<rightarrow>\<^sup>A y = 1\<^sup>A)" 

definition hoop_order_strict :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "<\<^sup>A" 60)
  where "x <\<^sup>A y \<equiv> (x \<le>\<^sup>A y \<and> x \<noteq> y)"

definition hoop_inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<and>\<^sup>A" 60)
  where "x \<and>\<^sup>A y = x *\<^sup>A (x \<rightarrow>\<^sup>A y)"

definition hoop_pseudo_sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<or>\<^sup>*\<^sup>A" 60)
  where "x \<or>\<^sup>*\<^sup>A y = ((x \<rightarrow>\<^sup>A y) \<rightarrow>\<^sup>A y) \<and>\<^sup>A ((y \<rightarrow>\<^sup>A x) \<rightarrow>\<^sup>A x)" 

end

locale wajsberg_hoop = hoop +
  assumes T: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x \<rightarrow>\<^sup>A y) \<rightarrow>\<^sup>A y = (y \<rightarrow>\<^sup>A x) \<rightarrow>\<^sup>A x"
begin

definition wajsberg_hoop_sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<or>\<^sup>A" 60)
  where "x \<or>\<^sup>A y = (x \<rightarrow>\<^sup>A y) \<rightarrow>\<^sup>A y"

end

subsection\<open>Basic properties\<close>

context hoop
begin

lemma mult_neutr_2 [simp]: 
  assumes "a \<in> A"
  shows "1\<^sup>A *\<^sup>A a = a"
  using assms mult_comm by simp

lemma imp_one_A:
  assumes "a \<in> A"
  shows "(1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A 1\<^sup>A = 1\<^sup>A"
proof -
  have "(1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A 1\<^sup>A = (1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A (1\<^sup>A \<rightarrow>\<^sup>A 1\<^sup>A)"
    using assms by simp
  also
  have "\<dots> = ((1\<^sup>A \<rightarrow>\<^sup>A a) *\<^sup>A 1\<^sup>A) \<rightarrow>\<^sup>A 1\<^sup>A"
    using assms imp_closed residuation by simp
  also
  have "\<dots> = ((a \<rightarrow>\<^sup>A 1\<^sup>A) *\<^sup>A a) \<rightarrow>\<^sup>A 1\<^sup>A"
    using assms divisibility imp_closed mult_comm by simp
  also
  have "\<dots> = (a \<rightarrow>\<^sup>A 1\<^sup>A) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A 1\<^sup>A)"
    using assms imp_closed one_closed residuation by metis
  also
  have "\<dots> = 1\<^sup>A"
    using assms imp_closed by simp
  finally
  show ?thesis 
    by auto
qed

lemma imp_one_B:
  assumes "a \<in> A"
  shows "(1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a = 1\<^sup>A"
proof -
  have "(1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a = ((1\<^sup>A \<rightarrow>\<^sup>A a) *\<^sup>A 1\<^sup>A) \<rightarrow>\<^sup>A a"
    using assms imp_closed by simp
  also
  have "\<dots> = (1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A (1\<^sup>A \<rightarrow>\<^sup>A a)" 
    using assms imp_closed one_closed residuation by metis
  also
  have "\<dots> = 1\<^sup>A"
    using assms imp_closed by simp
  finally
  show ?thesis
    by auto
qed

lemma imp_one_C:
  assumes "a \<in> A"
  shows "1\<^sup>A \<rightarrow>\<^sup>A a = a" 
proof -
  have "1\<^sup>A \<rightarrow>\<^sup>A a = (1\<^sup>A \<rightarrow>\<^sup>A a) *\<^sup>A 1\<^sup>A" 
    using assms imp_closed by simp
  also
  have "\<dots> = (1\<^sup>A \<rightarrow>\<^sup>A a) *\<^sup>A ((1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a)" 
    using assms imp_one_B by simp
  also
  have "\<dots> = a *\<^sup>A (a \<rightarrow>\<^sup>A (1\<^sup>A \<rightarrow>\<^sup>A a))" 
    using assms divisibility imp_closed by simp
  also
  have "\<dots> = a" 
    using assms residuation by simp
  finally
  show ?thesis
    by auto
qed

lemma imp_one_top:
  assumes "a \<in> A"
  shows "a \<rightarrow>\<^sup>A 1\<^sup>A = 1\<^sup>A"
proof -
  have "a \<rightarrow>\<^sup>A 1\<^sup>A = (1\<^sup>A \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A 1\<^sup>A"
    using assms imp_one_C by auto
  also
  have "\<dots> = 1\<^sup>A"
    using assms imp_one_A by auto
  finally
  show ?thesis
    by auto
qed

text\<open>The proofs of @{thm [source] imp_one_A}, @{thm [source] imp_one_B}, @{thm [source] imp_one_C}
and  @{thm [source] imp_one_top} are based on proofs found in \<^cite>\<open>"BOSBACH1969"\<close>
 (see Section 1: (4), (6), (7) and (12)).\<close>
 
lemma swap: 
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "a \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A c) = b \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c)"
proof -
  have "a \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A c) = (a *\<^sup>A b) \<rightarrow>\<^sup>A c"
    using assms residuation by auto
  also
  have "\<dots> = (b *\<^sup>A a) \<rightarrow>\<^sup>A c"
    using assms mult_comm by auto
  also
  have "\<dots> = b \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c)"
    using assms residuation by auto
  finally
  show ?thesis
    by auto
qed

lemma imp_A:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a) = 1\<^sup>A"
proof -
  have "a \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a) = b \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A a)"
    using assms swap by blast
  then
  show ?thesis
    using assms imp_one_top by simp
qed

subsection\<open>Multiplication monotonicity\<close>

lemma mult_mono:
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A ((a *\<^sup>A c) \<rightarrow>\<^sup>A (b *\<^sup>A c)) = 1\<^sup>A"
proof -
  have "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A ((a *\<^sup>A c) \<rightarrow>\<^sup>A (b *\<^sup>A c)) =
        (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A (b *\<^sup>A c)))"
    using assms mult_closed residuation by auto
  also
  have "\<dots> = ((a \<rightarrow>\<^sup>A b) *\<^sup>A a) \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A (b *\<^sup>A c))"
    using assms imp_closed mult_closed residuation by metis
  also
  have "\<dots> = ((b \<rightarrow>\<^sup>A a) *\<^sup>A b) \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A (b *\<^sup>A c))"
    using assms divisibility imp_closed mult_comm by simp
  also
  have "\<dots> = (b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A (b *\<^sup>A c)))"
    using assms imp_closed mult_closed residuation by metis
  also
  have "\<dots> = (b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A ((b *\<^sup>A c) \<rightarrow>\<^sup>A (b *\<^sup>A c))" 
    using assms(2,3) mult_closed residuation by simp
  also
  have "\<dots> = 1\<^sup>A"
    using assms imp_closed imp_one_top mult_closed by simp
  finally
  show ?thesis
    by auto
qed

subsection\<open>Implication monotonicity and anti-monotonicity\<close>

lemma imp_mono:
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A ((c \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A b)) = 1\<^sup>A"
proof -
  have "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A ((c \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A b)) =
        (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (((c \<rightarrow>\<^sup>A a) *\<^sup>A c) \<rightarrow>\<^sup>A b)" 
    using assms imp_closed residuation by simp
  also
  have "\<dots> = (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (((a \<rightarrow>\<^sup>A c) *\<^sup>A a) \<rightarrow>\<^sup>A b)" 
    using assms divisibility imp_closed mult_comm by simp
  also
  have "\<dots> = (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A ((a \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A b))" 
    using assms imp_closed residuation by simp
  also
  have "\<dots> = 1\<^sup>A" 
    using assms imp_A imp_closed by simp
  finally
  show ?thesis
    by auto
qed

lemma imp_anti_mono:
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A ((b \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c)) = 1\<^sup>A"
  using assms imp_closed imp_mono swap by metis

subsection\<open>@{term hoop_order} defines a partial order over @{term A}\<close>

lemma ord_reflex: 
  assumes "a \<in> A"
  shows "a \<le>\<^sup>A a"
  using assms hoop_order_def by simp

lemma ord_trans:
  assumes "a \<in> A" "b \<in> A" "c \<in> A" "a \<le>\<^sup>A b" "b \<le>\<^sup>A c"
  shows "a \<le>\<^sup>A c"
proof -
  have "a \<rightarrow>\<^sup>A c = 1\<^sup>A \<rightarrow>\<^sup>A (1\<^sup>A \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c))"
    using assms(1,3) imp_closed imp_one_C by simp
  also
  have "\<dots> = (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A ((b \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c))"
    using assms(4,5) hoop_order_def by simp
  also
  have "\<dots> = 1\<^sup>A"
    using assms(1-3) imp_anti_mono by simp
  finally
  show ?thesis
    using hoop_order_def by auto
qed

lemma ord_antisymm:
  assumes "a \<in> A" "b \<in> A" "a \<le>\<^sup>A b" "b \<le>\<^sup>A a"
  shows "a = b"
proof -
  have "a = a *\<^sup>A (a \<rightarrow>\<^sup>A b)"
    using assms(1,3) hoop_order_def by simp
  also
  have "\<dots> = b *\<^sup>A (b \<rightarrow>\<^sup>A a)" 
    using assms(1,2) divisibility by simp
  also
  have "\<dots> = b"
    using assms(2,4) hoop_order_def by simp
  finally
  show ?thesis
    by auto
qed

lemma ord_antisymm_equiv:
  assumes "a \<in> A" "b \<in> A" "a \<rightarrow>\<^sup>A b = 1\<^sup>A" "b \<rightarrow>\<^sup>A a = 1\<^sup>A"
  shows "a = b"
  using assms hoop_order_def ord_antisymm by auto

lemma ord_top:
  assumes "a \<in> A"
  shows "a \<le>\<^sup>A 1\<^sup>A"
  using assms hoop_order_def imp_one_top by simp

sublocale top_poset_on "A" "(\<le>\<^sup>A)" "(<\<^sup>A)" "1\<^sup>A"
proof
  show "A \<noteq> \<emptyset>"
    using one_closed by blast
next
  show "reflp_on A (\<le>\<^sup>A)"
    using ord_reflex reflp_onI by blast
next
  show "antisymp_on A (\<le>\<^sup>A)"
    using antisymp_onI ord_antisymm by blast
next 
  show "transp_on A (\<le>\<^sup>A)"
    using ord_trans transp_onI by blast
next
  show "x <\<^sup>A y = (x \<le>\<^sup>A y \<and> x \<noteq> y)" if "x \<in> A" "y \<in> A" for x y
    using hoop_order_strict_def by blast
next
  show "1\<^sup>A \<in> A"
    by simp
next
  show "x \<le>\<^sup>A 1\<^sup>A" if "x \<in> A" for x
    using ord_top that by simp
qed
 
subsection\<open>Order properties\<close>

lemma ord_mult_mono_A:
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "(a \<rightarrow>\<^sup>A b) \<le>\<^sup>A ((a *\<^sup>A c) \<rightarrow>\<^sup>A (b *\<^sup>A c))"
  using assms hoop_order_def mult_mono by simp

lemma ord_mult_mono_B:
  assumes "a \<in> A" "b \<in> A" "c \<in> A" "a \<le>\<^sup>A b"
  shows "(a *\<^sup>A c) \<le>\<^sup>A (b *\<^sup>A c)"
  using assms hoop_order_def imp_one_C swap mult_closed mult_mono top_closed
  by metis

lemma ord_residuation:
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "(a *\<^sup>A b) \<le>\<^sup>A c \<longleftrightarrow> a \<le>\<^sup>A (b \<rightarrow>\<^sup>A c)"
  using assms hoop_order_def residuation by simp

lemma ord_imp_mono_A:
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "(a \<rightarrow>\<^sup>A b) \<le>\<^sup>A ((c \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A (c \<rightarrow>\<^sup>A b))"
  using assms hoop_order_def imp_mono by simp

lemma ord_imp_mono_B:
  assumes "a \<in> A" "b \<in> A" "c \<in> A" "a \<le>\<^sup>A b"
  shows "(c \<rightarrow>\<^sup>A a) \<le>\<^sup>A (c \<rightarrow>\<^sup>A b)"
  using assms imp_closed ord_trans ord_reflex ord_residuation mult_closed
  by metis

lemma ord_imp_anti_mono_A:
  assumes "a \<in> A" "b \<in> A" "c \<in> A"
  shows "(a \<rightarrow>\<^sup>A b) \<le>\<^sup>A ((b \<rightarrow>\<^sup>A c) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A c))"
  using assms hoop_order_def imp_anti_mono by simp

lemma ord_imp_anti_mono_B:
  assumes "a \<in> A" "b \<in> A" "c \<in> A" "a \<le>\<^sup>A b"
  shows "(b \<rightarrow>\<^sup>A c) \<le>\<^sup>A (a \<rightarrow>\<^sup>A c)"
  using assms hoop_order_def imp_one_C swap ord_imp_mono_A top_closed
  by metis

lemma ord_A:
  assumes "a \<in> A" "b \<in> A"
  shows "b \<le>\<^sup>A (a \<rightarrow>\<^sup>A b)"
  using assms hoop_order_def imp_A by simp

lemma ord_B:
  assumes "a \<in> A" "b \<in> A"
  shows "b \<le>\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b)"
  using assms imp_closed ord_A by simp

lemma ord_C:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<le>\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b)"
  using assms imp_one_C one_closed ord_imp_anti_mono_A by metis

lemma ord_D:
  assumes "a \<in> A" "b \<in> A" "a <\<^sup>A b"
  shows "b \<rightarrow>\<^sup>A a \<noteq> 1\<^sup>A"
  using assms hoop_order_def hoop_order_strict_def ord_antisymm by auto

subsection\<open>Additional multiplication properties\<close>

lemma mult_lesseq_inf:
  assumes "a \<in> A" "b \<in> A"
  shows "(a *\<^sup>A b) \<le>\<^sup>A (a \<and>\<^sup>A b)"
proof -
  have "b \<le>\<^sup>A (a \<rightarrow>\<^sup>A b)"
    using assms ord_A by simp
  then
  have "(a *\<^sup>A b) \<le>\<^sup>A (a *\<^sup>A (a \<rightarrow>\<^sup>A b))"
    using assms imp_closed ord_mult_mono_B mult_comm by metis
  then
  show ?thesis
    using hoop_inf_def by metis
qed

lemma mult_A:
  assumes "a \<in> A" "b \<in> A"
  shows "(a *\<^sup>A b) \<le>\<^sup>A a"
  using assms ord_A ord_residuation by simp

lemma mult_B:
  assumes "a \<in> A" "b \<in> A"
  shows "(a *\<^sup>A b) \<le>\<^sup>A b"
  using assms mult_A mult_comm by metis

lemma mult_C:
  assumes "a \<in> A-{1\<^sup>A}" "b \<in> A-{1\<^sup>A}"
  shows "a *\<^sup>A b \<in> A-{1\<^sup>A}"
  using assms ord_antisymm ord_top mult_A mult_closed by force

subsection\<open>Additional implication properties\<close>

lemma imp_B:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<rightarrow>\<^sup>A b = ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b"
proof -
  have "a \<le>\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b)"
    using assms ord_C by simp
  then 
  have "(((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b) \<le>\<^sup>A (a \<rightarrow>\<^sup>A b)"
    using assms imp_closed ord_imp_anti_mono_B by simp
  moreover
  have "(a \<rightarrow>\<^sup>A b) \<le>\<^sup>A (((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A b)"
    using assms imp_closed ord_C by simp
  ultimately
  show ?thesis
    using assms imp_closed ord_antisymm by simp
qed

text\<open>The following two results can be found in \<^cite>\<open>"BLOK2000"\<close> (see Proposition 1.7 and 2.2).\<close>

lemma imp_C:
  assumes "a \<in> A" "b \<in> A"
  shows "(a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a) = b \<rightarrow>\<^sup>A a"
proof -
  have "a \<le>\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a)"
    using assms imp_closed ord_A by simp
  then
  have "(((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) \<le>\<^sup>A (a \<rightarrow>\<^sup>A b)"
    using assms imp_closed ord_imp_anti_mono_B by simp
  moreover 
  have "(a \<rightarrow>\<^sup>A b) \<le>\<^sup>A (((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a)"
    using assms imp_closed ord_C by simp
  ultimately
  have "(((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) \<le>\<^sup>A (((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a)"
    using assms imp_closed ord_trans by meson
  then
  have "((((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) *\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a)) \<le>\<^sup>A a"
    using assms imp_closed ord_residuation by simp
  then
  have "((b \<rightarrow>\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a)) *\<^sup>A b) \<le>\<^sup>A a"
    using assms divisibility imp_closed mult_comm by simp
  then
  have "(b \<rightarrow>\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A a)) \<le>\<^sup>A (b \<rightarrow>\<^sup>A a)"
    using assms imp_closed ord_residuation by simp
  then 
  have "((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a)) \<le>\<^sup>A (b \<rightarrow>\<^sup>A a)"
    using assms imp_closed swap by simp
  moreover
  have "(b \<rightarrow>\<^sup>A a) \<le>\<^sup>A ((a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a))"
    using assms imp_closed ord_A by simp
  ultimately
  show ?thesis
    using assms imp_closed ord_antisymm by auto
qed

lemma imp_D:
  assumes "a \<in> A" "b \<in> A"
  shows "(((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a) = b \<rightarrow>\<^sup>A a"
proof -
  have "(((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (b \<rightarrow>\<^sup>A a) =
        (((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a)" 
    using assms imp_B by simp
  also
  have "\<dots> = ((((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A b) *\<^sup>A ((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a)) \<rightarrow>\<^sup>A a" 
    using assms imp_closed residuation by simp
  also
  have "\<dots> = ((b \<rightarrow>\<^sup>A ((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a)) *\<^sup>A b) \<rightarrow>\<^sup>A a" 
    using assms divisibility imp_closed mult_comm by simp
  also
  have "\<dots> = (1\<^sup>A *\<^sup>A b) \<rightarrow>\<^sup>A a"
    using assms hoop_order_def ord_C by simp
  also
  have "\<dots> = b \<rightarrow>\<^sup>A a"
    using assms(2) mult_neutr_2 by simp
  finally
  show ?thesis
    by auto
qed

subsection\<open>@{term hoop_inf} defines a semilattice over @{term A}\<close>

lemma inf_closed:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<and>\<^sup>A b \<in> A"
  using assms hoop_inf_def imp_closed mult_closed by simp

lemma inf_comm:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<and>\<^sup>A b = b \<and>\<^sup>A a"
  using assms divisibility hoop_inf_def by simp

lemma inf_A:
  assumes "a \<in> A" "b \<in> A"
  shows "(a \<and>\<^sup>A b) \<le>\<^sup>A a"
proof -
  have "(a \<and>\<^sup>A b) \<rightarrow>\<^sup>A a = (a *\<^sup>A (a \<rightarrow>\<^sup>A b)) \<rightarrow>\<^sup>A a"
    using hoop_inf_def by simp
  also
  have "\<dots> = (a \<rightarrow>\<^sup>A b) \<rightarrow>\<^sup>A (a \<rightarrow>\<^sup>A a)"
    using assms mult_comm imp_closed residuation by metis
  finally
  show ?thesis
    using assms hoop_order_def imp_closed imp_one_top by simp
qed

lemma inf_B:
  assumes "a \<in> A" "b \<in> A"
  shows "(a \<and>\<^sup>A b) \<le>\<^sup>A b" 
  using assms inf_comm inf_A by metis

lemma inf_C:
  assumes "a \<in> A" "b \<in> A" "c \<in> A" "a \<le>\<^sup>A b" "a \<le>\<^sup>A c"
  shows "a \<le>\<^sup>A (b \<and>\<^sup>A c)"
proof -
  have "(b \<rightarrow>\<^sup>A a) \<le>\<^sup>A (b \<rightarrow>\<^sup>A c)"
    using assms(1-3,5) ord_imp_mono_B by simp
  then
  have "(b *\<^sup>A (b \<rightarrow>\<^sup>A a)) \<le>\<^sup>A (b *\<^sup>A (b \<rightarrow>\<^sup>A c))"
    using assms imp_closed ord_mult_mono_B mult_comm by metis
  moreover
  have "a = b *\<^sup>A (b \<rightarrow>\<^sup>A a)"
    using assms(1-3,4) divisibility hoop_order_def mult_neutr by simp
  ultimately
  show ?thesis
    using hoop_inf_def by auto
qed

lemma inf_order: 
  assumes "a \<in> A" "b \<in> A"
  shows "a \<le>\<^sup>A b \<longleftrightarrow> (a \<and>\<^sup>A b = a)"
  using assms hoop_inf_def hoop_order_def inf_B mult_neutr by metis

subsection\<open>Properties of @{term hoop_pseudo_sup}\<close>

lemma pseudo_sup_closed:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<or>\<^sup>*\<^sup>A b \<in> A"
  using assms hoop_pseudo_sup_def imp_closed inf_closed by simp

lemma pseudo_sup_comm:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<or>\<^sup>*\<^sup>A b = b \<or>\<^sup>*\<^sup>A a"
  using assms hoop_pseudo_sup_def imp_closed inf_comm by auto

lemma pseudo_sup_A:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<le>\<^sup>A (a \<or>\<^sup>*\<^sup>A b)"
  using assms hoop_pseudo_sup_def imp_closed inf_C ord_B ord_C by simp

lemma pseudo_sup_B:
  assumes "a \<in> A" "b \<in> A"
  shows "b \<le>\<^sup>A (a \<or>\<^sup>*\<^sup>A b)"
  using assms pseudo_sup_A pseudo_sup_comm by metis

lemma pseudo_sup_order:
  assumes "a \<in> A" "b \<in> A"
  shows "a \<le>\<^sup>A b \<longleftrightarrow> a \<or>\<^sup>*\<^sup>A b = b"
proof
  assume "a \<le>\<^sup>A b"
  then 
  have "a \<or>\<^sup>*\<^sup>A b = b \<and>\<^sup>A ((b \<rightarrow>\<^sup>A a) \<rightarrow>\<^sup>A a)"
    using assms(2) hoop_order_def hoop_pseudo_sup_def imp_one_C by simp
  also
  have "\<dots> = b"
    using assms imp_closed inf_order ord_C by meson
  finally
  show "a \<or>\<^sup>*\<^sup>A b = b"
    by auto
next
  assume "a \<or>\<^sup>*\<^sup>A b = b"
  then
  show "a \<le>\<^sup>A b"
    using assms pseudo_sup_A by metis
qed

end

end