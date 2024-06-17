section \<open>Discrete Subdistributions and Distributions\<close>

text \<open>This theory defines countably discrete probability (sub)distributions and their monadic 
operators, namely:
\begin{itemize}
\item Kleisli extension, "ext" 
\item functorial action, the lifting operator "lift"
\item monad unit, the indicator function "ind" 
\item monad counit, the flattening operators "flat" for subdistributions and 
"dflat" for subdistributions
\end{itemize}
Basic facts about them are proved, including the monadic laws. 

In all operators except the monad counit (flattening/averaging), the operators for distributions 
are restrictions of those for subdistributions. For flattening, as explained later we must use 
two distinct operators "flat" and "dflat".

We also define the expectation operator, "expd", which is the Lebesgue integral 
for the discrete case. 
\<close>

(* 
As usual, we follow two principles: 
- Economy of hypotheses.  
For example, in lemma lift_ex, it turns out we don't need to assume "\<forall>a\<in>A. f a \<in> B"'
also the conclusion equality holds for all B, not just b \<in> B. This is the case 
in other lemmas as well. 
- Economy of structure. For example, the functorial action "lift" does not need to take  
as arguments both the domain A and the codomain B for its function argument f; 
the domain suffices. Also, the indicator function "ind" does not (need to) 
take the underlying set as argument.
*)

theory Discrete_Subdistributions_and_Distributions
  imports Infinite_Sums_of_Positive_Reals 
begin



subsection \<open>Definitions and Basic Properties\<close>

definition Subdis :: "'a set \<Rightarrow> ('a \<Rightarrow> real) set" where 
  "Subdis A \<equiv> {p. positive p A \<and> sbounded p A \<and> isum p A \<le> 1}"

definition Dis :: "'a set \<Rightarrow> ('a \<Rightarrow> real) set" where 
  "Dis A \<equiv> {p. p \<in> Subdis A \<and> isum p A \<ge> 1}"

lemma Dis_incl_Subdis: "Dis A \<subseteq> Subdis A" unfolding Dis_def by auto

lemma Subdis_mono: "p \<in> Subdis A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> p \<in> Subdis B"
  unfolding Subdis_def by simp (meson isum_mono' order_trans positive_mono sbounded_mono)

lemma Subdis_Dis2: "Subdis (Subdis A) \<subseteq> Subdis (Dis A)"
  by (meson Dis_incl_Subdis Subdis_mono subsetI) 

(* *) 

lemma Subdis_ge_0: "p \<in> Subdis A \<Longrightarrow> a \<in> A \<Longrightarrow> p a \<ge> 0"
  unfolding Subdis_def positive_def by auto

lemma Subdis_le_1: "p \<in> Subdis A \<Longrightarrow> a \<in> A \<Longrightarrow> p a \<le> 1"
  unfolding Subdis_def by simp (smt in_le_isum)

lemma Subdis_eq:
  assumes "p \<in> Subdis A" and "\<forall>a\<in>A. p1 a = p a"
  shows "p1 \<in> Subdis A"
  using Subdis_def assms isum_cong positive_eq sbounded_eq by fastforce

lemma Dis_Subdis_mono: "p \<in> Dis A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> p \<in> Subdis B"
  using Dis_def Subdis_mono by blast 

lemma Dis_zeros_mono: "p \<in> Dis A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> \<forall>a\<in>A-B. p a = 0 \<Longrightarrow> p \<in> Dis B"
  by (metis (no_types, lifting) Dis_Subdis_mono Dis_def Subdis_def isum_zeros_congL mem_Collect_eq)

lemma Dis_ge_0: "p \<in> Dis A \<Longrightarrow> a \<in> A \<Longrightarrow> p a \<ge> 0"
  using Dis_def Subdis_ge_0 by fastforce

lemma Dis_le_1: "p \<in> Dis A \<Longrightarrow> a \<in> A \<Longrightarrow> p a \<le> 1"
  using Dis_def Subdis_le_1 by fastforce

lemma Dis_isum_1: "p \<in> Dis A \<Longrightarrow> isum p A = 1"
  using Dis_def Subdis_def isum_eq_sum by fastforce

lemma Dis_sum_1: "p \<in> Dis A \<Longrightarrow> finite A \<Longrightarrow> sum p A = 1"
  using Dis_def Subdis_def isum_eq_sum by fastforce

lemma Dis_eq:
  assumes "p \<in> Dis A" and "\<forall>a\<in>A. p1 a = p a"
  shows "p1 \<in> Dis A"
  unfolding Dis_def
  using Dis_def Subdis_eq assms isum_cong by fastforce

lemma Subdis_le_1_eq_1: "p \<in> Subdis A \<Longrightarrow> 1 \<le> isum p A \<Longrightarrow> isum p A = 1"
  unfolding Subdis_def by auto

lemma Subdis_sum_le_1: "p \<in> Subdis A \<Longrightarrow> finite A \<Longrightarrow> sum p A \<le> 1"
  using Subdis_def isum_eq_sum by fastforce 

lemma Subdis_sum_ge_0: "p \<in> Subdis A \<Longrightarrow> finite A \<Longrightarrow> sum p A \<ge> 0"
  by (simp add: Subdis_ge_0 sum_nonneg) 

lemma Subdis_sum_ge_0_sub: "p \<in> Subdis A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> finite B \<Longrightarrow> sum p B \<ge> 0"
  using Subdis_mono Subdis_sum_ge_0 by blast 

lemma Subdis_sum_le_1_sub: "p \<in> Subdis A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> finite B \<Longrightarrow> sum p B \<le> 1"
  using Subdis_mono Subdis_sum_le_1 by blast

(* *)
lemma Subdis_sboundedL: 
  assumes "p \<in> Subdis A" "\<forall>a\<in>A. g a \<le> x" 
  shows "sbounded (\<lambda>a. p a * g a) A"
  using Subdis_def assms positive_sbounded_multL by fastforce

lemma Subdis_sboundedR: 
  assumes "p \<in> Subdis A" "\<forall>a\<in>A. g a \<le> x" 
  shows "sbounded (\<lambda>a. g a * p a) A"
  using Subdis_def assms positive_sbounded_multR by fastforce

lemma Subdis_isum_leL: 
  assumes p: "p \<in> Subdis A" and g: "positive g A" "\<forall>a\<in>A. g a \<le> x" and x: "x \<ge> 0" 
  shows "isum (\<lambda>a. p a * g a) A \<le> x"
  apply(rule order.trans[OF isum_mono[of "\<lambda>a. p a * x"]])
  subgoal apply(rule sbounded_multR) using x p unfolding Subdis_def by auto
  subgoal using x p g unfolding Subdis_def positive_def by (simp add: mult_mono)
  subgoal apply(subst isum_distribR[symmetric])
    using assms unfolding Subdis_def by (auto simp: mult.commute mult_left_le) .

lemma Subdis_isum_leR: 
  assumes p: "p \<in> Subdis A" and g: "positive g A" "\<forall>a\<in>A. g a \<le> x" and x: "x \<ge> 0" 
  shows "isum (\<lambda>a. g a * p a) A \<le> x"
proof-
  have 0: "(\<lambda>a. g a * p a) = (\<lambda>a. p a * g a)" unfolding fun_eq_iff by auto
  show ?thesis unfolding 0 using Subdis_isum_leL[OF assms] .
qed

lemma Subdis_sum_le_Max: 
  assumes "finite A" "p \<in> Subdis A" "positive g A" "A \<noteq> {}"
  shows "(\<Sum>a\<in>A. p a * g a) \<le> Max (g ` A)"
proof-
  have 0: "Max (g ` A) \<ge> 0" 
    by (metis positive_def Max_ge_iff assms(1,3,4) ex_in_conv finite_imageI image_eqI)
  have "(\<Sum>a\<in>A. p a * g a) \<le> (\<Sum>a\<in>A. p a * Max (g ` A))" 
    apply(rule sum_mono) using assms unfolding Subdis_def positive_def   
    by (simp add: mult_left_mono)
  also have "\<dots> = (\<Sum>a\<in>A. p a) * Max (g ` A)" 
    using sum_distrib_right[symmetric] .
  also have "\<dots> \<le> Max (g ` A)" using assms 
    using Subdis_sum_le_1[of p A] 0 Subdis_sum_ge_0 mult_left_le_one_le by blast
  finally show ?thesis .
qed

lemma Subdis_sum_le: 
  assumes "finite A" "p \<in> Subdis A" "positive g A" "A \<noteq> {}" "\<forall>a\<in>A. g a \<le> x"
  shows "(\<Sum>a\<in>A. p a * g a) \<le> x"
  using Subdis_sum_le_Max[OF assms(1-4)] 
  by (smt Max_in assms(1) assms(4) assms(5) finite_imageI imageE image_is_empty)


subsection \<open>Monadic structure\<close>

(* The indicator function (the monad's unit): *)

definition ind :: "'a \<Rightarrow> ('a \<Rightarrow> real)" where 
  "ind a \<equiv> \<lambda>a'. if a' = a then 1 else 0"

lemma ind_simps[simp]: "\<And>a. ind a a = 1"
  "\<And>a a'. a' \<noteq> a \<Longrightarrow> ind a' a = 0"
  unfolding ind_def by auto

lemma ind_eq_0_iff[simp]: "ind a a' = 0 \<longleftrightarrow> a \<noteq> a'"
  unfolding ind_def by auto

lemma ind_eq_1_iff[simp]: "ind a a' = 1 \<longleftrightarrow> a = a'"
  unfolding ind_def by auto

lemma ind_ge_0: "ind a a' \<ge> 0"
  unfolding ind_def by auto

lemma ind_le_1: "ind a a' \<le> 1"
  unfolding ind_def by auto

lemma positive_ind[simp]: "positive (ind a) A"
  unfolding ind_def positive_def by auto

lemma sbounded_ind[simp]: "sbounded (ind a) A"
  unfolding ind_def sbounded_def by auto

lemma sum_ind[simp]: "\<And>a B. finite B \<Longrightarrow> a \<in> B \<Longrightarrow> sum (ind a) B = 1"
  "\<And>a B. finite B \<Longrightarrow> a \<notin> B \<Longrightarrow> sum (ind a) B = 0"
  subgoal for a B
    unfolding ind_simps(1)[symmetric, of a] sum_singl[of "ind a" a, symmetric]
    apply(rule sum.mono_neutral_right) by auto
  subgoal by (metis ind_eq_0_iff sum.neutral) .

lemma isum_ind[simp]: "\<And>a A. a \<in> A \<Longrightarrow> isum (ind a) A = 1"
  "\<And>a A. a \<notin> A \<Longrightarrow> isum (ind a) A = 0"
  apply (simp add: ind_ge_0 isum_eq_singl)
  by (metis ind_simps(2) isum_const_zero')

lemma ind_Subdis[simp, intro!]: "ind a \<in> Subdis A" 
  unfolding Subdis_def by simp (smt isum_ind(1) isum_ind(2) positive_ind sbounded_ind)

lemma Dis_ind[simp, intro!]: "a \<in> A \<Longrightarrow> ind a \<in> Dis A" 
  unfolding Dis_def by simp

lemma ind_mult_SubdisL: 
  assumes p: "p \<in> Subdis A" 
  shows "(\<lambda>a. p a * ind (f a) a') \<in> Subdis A"
  unfolding Subdis_def  mem_Collect_eq using p apply safe
  subgoal by (simp add: positive_def Subdis_ge_0 ind_ge_0)
  subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) by (auto simp: ind_le_1)
  subgoal apply(rule order.trans[of _ "isum p A"])
     apply(rule isum_mono) unfolding Subdis_def using ind_le_1
    by (auto simp: positive_def ind_le_1 mult_left_le) .

lemma ind_mult_SubdisR: 
  assumes p: "p \<in> Subdis A" 
  shows "(\<lambda>a. ind (f a) a' * p a) \<in> Subdis A"
proof-
  have 0: "(\<lambda>a. ind (f a) a' * p a) = (\<lambda>a. p a * ind (f a) a')" by fastforce
  show ?thesis unfolding 0 using ind_mult_SubdisL[OF p] .
qed

lemma isum_ind_multL: "a' \<in> A \<Longrightarrow> f a' \<ge> 0 \<Longrightarrow> isum (\<lambda>a. f a * ind a' a) A = f a'"
  apply(rule isum_eq_singl[of _ a']) by auto

lemma isum_ind_multR: "a' \<in> A \<Longrightarrow> f a' \<ge> 0 \<Longrightarrow> isum (\<lambda>a. ind a' a * f a) A = f a'"
  apply(rule isum_eq_singl[of _ a']) by auto


(* Kleisli extension (of a function from A to Subdis A to a 
function from Subdis A t Subdis B) *)

definition ext :: "'a set \<Rightarrow> ('a \<Rightarrow> ('b \<Rightarrow> real)) \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> real))" where 
  "ext A f \<equiv> \<lambda>p b. isum (\<lambda>a. p a * f a b) A"

(* The well-definedness of ext: *)


lemma ext_ge_0: 
  assumes f: "\<forall>a\<in>A. f a \<in> Subdis B" and p: "p \<in> Subdis A" and b: "b \<in> B"
  shows "ext A f p b \<ge> 0"
  unfolding ext_def apply(rule isum_ge_0) 
  subgoal using assms unfolding Subdis_def positive_def by auto
  subgoal apply(rule positive_sbounded_multL[of _ _ _ 1]) 
    using assms unfolding Subdis_def  
    by auto (meson Subdis_le_1 f) .

lemma Subdis_sum_isum_le_1: 
  assumes B: "finite B" and f: "\<forall>a\<in>A. f a \<in> Subdis B" and p: "p \<in> Subdis A"
  shows "(\<Sum>b\<in>B. isum (\<lambda>a. p a * f a b) A) \<le> 1" 
proof-
  have 0: "(\<lambda>(b, a). p a * f a b) = (\<lambda>ba. p (snd ba) * f (snd ba) (fst ba))"
    unfolding fun_eq_iff by auto
  have 1: "(\<lambda>ba. p (snd ba)) = (\<lambda>(b,a). 1 * p a)"
    unfolding fun_eq_iff by auto 
  have 2: "\<And>AB. AB \<subseteq> A \<times> B \<Longrightarrow> fst ` AB \<subseteq> A" by auto 
  have 3: "\<And>AB. AB \<subseteq> A \<times> B \<Longrightarrow> finite AB \<Longrightarrow> sum p (fst ` AB) \<le> 1"
    using p unfolding Subdis_def sbounded_def  
    by (metis (mono_tags, lifting) "2" Subdis_sum_le_1_sub finite_imageI p)
  show ?thesis apply(subst isum_eq_sum[symmetric])
    subgoal unfolding Subdis_def positive_def apply safe
      subgoal for a apply(rule isum_ge_0)
        subgoal using f p unfolding Subdis_def positive_def by auto
        subgoal apply(rule Subdis_sboundedL[of _ _ _ 1])
          subgoal using p .
          subgoal using f by (meson Subdis_le_1) . . .
    subgoal by fact
    subgoal apply(subst isum_swap[symmetric])  
      subgoal unfolding sbounded_def apply(rule exI[of _ "real (card B)"]) apply safe
        subgoal for AB apply(rule order.trans[of _ "\<Sum>(a, b)\<in>(fst`AB)\<times>B. p a * 1"])      
          subgoal apply(rule sum_mono3)
            subgoal using B by auto
            subgoal by (smt SigmaE mem_Sigma_iff subsetD subsetI subset_fst_snd)
            subgoal for ab using p f unfolding Subdis_def positive_def by (cases ab, auto) 
            subgoal for ab using p f unfolding Subdis_def positive_def apply (cases ab, auto)  
              by (meson Subdis_le_1 f in_mono mem_Sigma_iff mult_left_le) . 
          subgoal apply(subst sum.cartesian_product[symmetric]) apply simp 
            apply(subst sum_distrib_left[symmetric])  
            by (metis "3" real_of_card sum_bounded_below) . .
      subgoal apply(subst order.trans[OF isum_mono[of p]])
        subgoal using Subdis_def p by blast
        subgoal for a apply(subst isum_distribL[symmetric]) 
          subgoal using Subdis_def f by blast
          subgoal using Subdis_def f by blast
          subgoal by (meson Subdis_ge_0 p)
          subgoal using Subdis_def p f mult_left_le unfolding Subdis_def positive_def by fastforce .
        subgoal using Subdis_def p by blast
        subgoal by simp . . . 
qed

lemma sbounded_prod_Subdis:
  assumes f: "\<forall>a\<in>A. f a \<in> Subdis B" and p: "p \<in> Subdis A"
  shows "sbounded (\<lambda>(a, b). p b * f b a) (B \<times> A)"
proof-
  have 0: "\<And>BA. BA \<subseteq> B \<times> A \<Longrightarrow> fst ` BA \<subseteq> B \<and> snd ` BA \<subseteq> A" by auto 
  show ?thesis
    unfolding sbounded_def apply(rule exI[of _ 1]) apply safe
    subgoal for BA apply(rule order.trans[OF sum_mono2[of "fst`BA \<times> snd`BA"]])
      subgoal by auto
      subgoal by (simp add: subset_fst_snd)
      subgoal for ab using assms unfolding Subdis_def positive_def 
        using in_mono by fastforce
      subgoal unfolding sum.cartesian_product[symmetric] (* apply(subst sum.swap) *)
        apply(rule order.trans[OF _ Subdis_sum_isum_le_1[of "fst`BA" "snd`BA" f p]])
        subgoal apply(rule sum_mono)
          subgoal for b apply(subst isum_eq_sum)
            subgoal using assms unfolding positive_def 
              by (metis "0" Subdis_ge_0 in_mono zero_le_mult_iff)  
            subgoal by auto
            subgoal by auto . .
        subgoal by auto
        subgoal using f by (metis "0" Subdis_mono in_mono)   
        subgoal using p using "0" Subdis_mono by force . . .
qed

(* Well-formedness of the Kleisli extension operator: It respects equality and 
does produce functions 
between (sub)distributions starting from a function returning (sub)distributions: *)

lemma ext_eq: "\<forall>a\<in>A. p1 a = p2 a \<Longrightarrow> \<forall>a\<in>A. \<forall>b\<in>B. f1 a b = f2 a b \<Longrightarrow> 
 b \<in> B \<Longrightarrow> ext A f1 p1 b = ext A f2 p2 b"
  by (metis (mono_tags, lifting) ext_def isum_cong) 

lemma ext_Subdis: 
  assumes f: "\<forall>a\<in>A. f a \<in> Subdis B" and p: "p \<in> Subdis A"
  shows "ext A f p \<in> Subdis B"
proof-
  have 0: "(\<lambda>(b, a). p a * f a b) = (\<lambda>ba. p (snd ba) * f (snd ba) (fst ba))"
    unfolding fun_eq_iff by auto
  have 1: "(\<lambda>ba. p (snd ba)) = (\<lambda>(b,a). 1 * p a)"
    unfolding fun_eq_iff by auto 
  show ?thesis 
    unfolding Subdis_def mem_Collect_eq apply safe
    subgoal using ext_ge_0[OF assms] unfolding positive_def by auto
    subgoal unfolding sbounded_def ext_def 
      apply(rule exI[of _ 1]) apply safe
      subgoal for Ba  
        apply(rule Subdis_sum_isum_le_1[of Ba])
        using assms Subdis_mono by force+ .
    subgoal unfolding ext_def apply(subst isum_swap) 
      subgoal using sbounded_prod_Subdis[OF assms] .
      subgoal apply(subst order.trans[OF isum_mono[of p]])
        subgoal using Subdis_def p by blast
        subgoal for a apply(subst isum_distribL[symmetric]) 
          subgoal using Subdis_def f by blast
          subgoal using Subdis_def f by blast
          subgoal by (meson Subdis_ge_0 p)
          subgoal using Subdis_def p f mult_left_le unfolding Subdis_def positive_def by fastforce .
        subgoal using Subdis_def p by blast
        subgoal by simp . . .
qed

lemma ext_Dis: 
  assumes f: "\<forall>a\<in>A. f a \<in> Dis B" and p: "p \<in> Dis A"
  shows "ext A f p \<in> Dis B"
proof-
  have "isum (ext A f p) B = 1" unfolding ext_def apply(subst isum_swap)
    subgoal apply(rule sbounded_prod_Subdis)
      using assms unfolding Dis_def by auto
    subgoal apply(rule trans[of _ "isum (\<lambda>b. p b * isum (f b) B) A"])
      subgoal apply(rule isum_cong, rule refl)
        apply(rule isum_distribL[symmetric])
        subgoal by (meson Dis_ge_0 positive_def f)
        subgoal using Dis_def Subdis_def f by blast 
        subgoal by (meson Dis_ge_0 p) .
      subgoal apply(rule trans[of _ "isum p A"])
        subgoal apply(rule isum_cong, rule refl)
          subgoal for a using f apply(subst Dis_isum_1) by auto .
        subgoal using p using Dis_isum_1 by auto . . . 
  thus ?thesis using assms unfolding Dis_def by (simp add: ext_Subdis)
qed

(* The extension of the indicator is the identity functions on A-subdistributions: *)
lemma ext_ind: "p \<in> Subdis A \<Longrightarrow> a \<in> A \<Longrightarrow> ext A ind p a = p a" 
  unfolding ext_def fun_eq_iff
  by (smt (verit) Subdis_ge_0 ind_simps isum_eq_singl mult_cancel_left2 mult_minus_right) 


(* The central Kleisli extension property, from which 
all other monad properties follow by "abstract nonsense": *)
lemma ext_o: 
  assumes f: "\<forall>a\<in>A. f a \<in> B" and gg: "\<forall>b\<in>B. gg b \<in> Subdis C" and p: "p \<in> Subdis A" and c: "c \<in> C"
  shows "ext A (gg o f) p c = ext B gg (ext A (ind o f) p) c"
proof-
  have 0: "\<And>a. a \<in> A \<Longrightarrow> positive (\<lambda>aa. ind (f a) aa * gg aa c) B \<and> 
                          sbounded (\<lambda>aa. ind (f a) aa * gg aa c) B"
    subgoal for a apply safe
      subgoal using assms unfolding positive_def apply safe
        subgoal for b by (cases "b = f a", auto dest: Subdis_ge_0) . 
      subgoal using assms by (metis Subdis_le_1 positive_ind positive_sbounded_multL sbounded_ind) . .

  show ?thesis  
    unfolding ext_def 
    apply(rule trans[of _ "isum (\<lambda>b. isum (\<lambda>a. p a * (ind (f a) b * gg b c)) A) B"])
    subgoal apply(subst isum_swap)
      subgoal apply(subst sbounded_prod_Subdis)
        subgoal unfolding Subdis_def mem_Collect_eq apply safe
          subgoal using 0 by auto
          subgoal using 0 by auto
          subgoal for a apply(rule isum_le_singl[of _ "f a"]) 
            using assms by (auto dest: Subdis_ge_0 Subdis_le_1) .
        subgoal by fact
        subgoal by simp .
      subgoal apply(rule isum_cong, rule refl)
        subgoal for a apply(subst isum_distribL[symmetric])
          subgoal using 0 by auto
          subgoal using 0 by auto
          subgoal by (meson Subdis_ge_0 p)
          subgoal unfolding mult_cancel_left apply(rule disjI2)
            unfolding o_def apply(subst isum_singl[of "\<lambda>b. gg b c" "f a", symmetric])
            subgoal by (meson Subdis_ge_0 c f gg)
            subgoal apply(rule isum_zeros_cong)
              subgoal using assms by auto
              subgoal by auto
              subgoal using f by auto
              subgoal by auto . . . . .
    subgoal apply(rule isum_cong, rule refl)
      apply(subst isum_distribR)
      subgoal by (smt positive_def Subdis_ge_0 comp_apply ind_eq_0_iff ind_simps(1) mult_nonneg_nonneg p)
      subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms  
        by (simp_all add: ind_le_1) 
      subgoal by (meson Subdis_ge_0 c gg)
      subgoal apply(rule isum_cong) by auto . . 
qed

(* The functorial action, lifting functions between elements to functions between (sub)distributions: *)

definition lift :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> real)" where 
  "lift A f p \<equiv> \<lambda>b. isum (\<lambda>a. p a) {a. a \<in> A \<and> f a = b}"

(* lift can be expresssed from ext: *)
lemma lift_ext:
  assumes p: "p \<in> Subdis A"  
  shows "lift A f p = ext A (ind o f) p"
  apply(rule ext) unfolding lift_def ext_def apply(rule isum_zeros_cong)
  subgoal by (metis (no_types, lifting) Subdis_def inf_le2 mem_Collect_eq p sbounded_mono)
  subgoal using assms by auto
  subgoal by auto
  subgoal using assms by auto .

(* Well-definedness of lift: *)

lemma lift_eq: 
  assumes f: "\<forall>a\<in>A. f1 a = f2 a" and p: "\<forall>a\<in>A. p1 a = p2 a" and b: "b \<in> B"
  shows "lift A f1 p1 b = lift A f2 p2 b"
  unfolding lift_def apply(rule isum_cong) using assms by auto

lemma lift_Subdis:
  assumes (* f: "\<forall>a\<in>A. f a \<in> B" and*) p: "p \<in> Subdis A" 
  shows "lift A f p \<in> Subdis B"
  by (simp add: ext_Subdis lift_ext p)

lemma lift_Dis: (* NB: Here the "f" hypotheses is needed: *)
  assumes f: "\<forall>a\<in>A. f a \<in> B" and p: "p \<in> Dis A" 
  shows "lift A f p \<in> Dis B"
  by (smt (verit, best) Dis_incl_Subdis Dis_ind comp_apply ext_Dis f lift_ext p subset_iff)

(* Functoriality of lift: *)

lemma lift_id[simp]: 
  assumes p: "p \<in> Subdis A" and "a\<in>A"
  shows "lift A id p a = p a" 
  unfolding lift_ext[OF p] using ext_ind[OF assms] by simp

lemma lift_o[simp]: 
  assumes f: "\<forall>a\<in>A. f a \<in> B" and g: "\<forall>b\<in>B. g b \<in> C" and p: "p \<in> Subdis A" and c: "c\<in>C"
  shows "lift A (g o f) p c = lift B g (lift A f p) c" 
  apply(subst lift_ext[OF p])
  apply(subst o_assoc)
  apply(subst ext_o[of A f B "ind \<circ> g" C])
  subgoal using f by auto
  subgoal using g by auto
  subgoal by fact
  subgoal by fact
  by (metis lift_Subdis lift_ext p)


(* Naturality of ind w.r.t. lift: *)
lemma lift_ind:
  assumes a: "a \<in> A"  
  shows "lift A f (ind a) = ind (f a)"
  apply(rule ext) 
  subgoal for b
    apply(cases "f a = b")
    subgoal using a unfolding lift_def by auto
    subgoal unfolding lift_def by auto . .

(* Since "lift A f p" creates a distribution on B by clustering p w.r.t. f's kernel, 
it follows that its sum over B is the same as p's sum over a: *)
lemma isum_lift: 
  assumes f: "\<forall>a\<in>A. f a \<in> B" and p: "p \<in> Subdis A" 
  shows "isum (lift A f p) B = isum p A"
proof-
  have A: "isum p A = isum p (\<Union> ((\<lambda>b. {a . a \<in> A \<and> f a = b}) ` B))"
    apply(rule arg_cong[of _ _ "isum p"]) using f by auto
  show ?thesis apply(subst A) apply(subst isum_UNION)
    subgoal by auto
    subgoal using p unfolding Subdis_def 
      by (metis (no_types, lifting) SUP_least mem_Collect_eq sbounded_mono subset_eq)
    subgoal unfolding lift_def .. .
qed

(*  The above immediately gives the property that lift (not only preserves 
but also) reflects distributions:  *)
lemma lift_reflects_Dis: 
  assumes f: "\<forall>a\<in>A. f a \<in> B" and p: "p \<in> Subdis A" 
  shows "lift A f p \<in> Dis B \<longleftrightarrow> p \<in> Dis A"
  by (metis (no_types, lifting) Dis_def f isum_lift lift_Dis mem_Collect_eq p)


(* The monad counit -- flattening *)

(* This is the first construction where the distinction between subdistributions 
and distributions shows up more sharply -- in the sense that defining an operator on 
distributions and then proving it closed for distributions no longer works and borrowing 
properties from subdistributions to distributions, no longer works. The main 
reason for this difficulty is the second-order nature of flattening: It returns an expected value of 
-- a subdistribution over subdistributions in one case
-- a distribution over distrubutions in the other
And the problem is that the sets Subdis (Subdis A) and Dis (Dis A) are incomparable (by inclusion); 
they are both included in Subdis (Dis A).
In fact, the associativity property of flattening is even third-order, bringing a problem 
of the same nature, since Subdis (Subdis (Subdis A)) and Dis (Dis (Dis A)) are incomparable. 

To capture the flattening operators for both distributions and subdistributions without duplication, we 
introduce parameterized flattening (over a an "intermediate set ba"), operating on 
parameter set "Ba \<subseteq> Subdis A". The monad-like properties will be proved for any Ba 
that is well-behaved, e.g., it is preserved by indP and liftP, and is reflected by liftP. In one case, 
monadic associativity, we additionally consider a third-order parameter "Baa \<subseteq> Subdis Ba". 

In particular, the monad-like properties will hold for the following instantiations: 
--(1) Ba = Subdis A and Baa = Subdis Ba = Subdis (Subdis A) 
--(2) Ba = Dis A and Baa = Dis Ba = Dis (Dis A)  
In case (1), we obtain immediately the monadic properties of the subdistrib monad counit; 
in case (2), we obtain properties working for "Subdis (Dis A)", which in particular give us 
properties for "Dis (Dis A)", i.e., the monadic properties of the distrib monad counit. 
*)

(* Parameterized flattening *)

definition flatP :: "('a \<Rightarrow> real) set \<Rightarrow> 
  (('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)" where 
  "flatP Da pp \<equiv> \<lambda>a. isum (\<lambda>p. pp p * p a) Da"

(* NB: A parameter A :: 'a set would be superfluous in flatP. *)

(* It is the Kleisli lifting of the identity function on Da: *)
lemma flatP_ext: "flatP Da = ext Da id"
  unfolding flatP_def ext_def by simp  

(* Well-definedness of flatP: *)
lemma flatP_eq: "\<forall>p\<in>Da. pp1 p = pp2 p \<Longrightarrow> a \<in> A \<Longrightarrow> flatP Da pp1 a = flatP Da pp2 a"
  unfolding flatP_ext apply(rule ext_eq[of _ _ _ A]) by auto

lemma flatP_Subdis: "Da \<subseteq> Subdis A \<Longrightarrow> 
 pp \<in> Subdis Da \<Longrightarrow> flatP Da pp \<in> Subdis A"
  unfolding flatP_ext apply(rule ext_Subdis) unfolding Dis_def by auto

(* thm ext_Dis  *)

(* A rather tautological, but useful consequence of flatP's definition: 
It preserves any Da that is preserved by identity extensions.  *)
lemma flatP_Da: "\<forall>pp\<in>Dis Da. ext Da id pp \<in> Da \<Longrightarrow> 
 pp \<in> Dis Da \<Longrightarrow> flatP Da pp \<in> Da"
  by (simp add: flatP_ext)

(* flatP inverse of ind *)
lemma flatP_lift_ind: 
  assumes Da: "Da \<subseteq> Subdis A" "ind ` A \<subseteq> Da"
    and p: "p \<in> Subdis A" and a: "a \<in> A"
  shows "flatP Da (lift A ind p) a = p a" 
  unfolding flatP_ext lift_ext[OF p]
  apply(subst ext_o[symmetric, of _ _ _ _ A]) 
  using assms by (auto simp: ext_ind)

(* flatP inverse of lifted ind *)
lemma flatP_ind: 
  assumes Da: "Da \<subseteq> Subdis A"
    and "p \<in> Da" and "a \<in> A"
  shows "flatP Da (ind p) a = p a"
  unfolding flatP_def apply(rule isum_eq_singl[of _ p "p a"]) using assms 
  by (auto simp: Subdis_ge_0)

(* flatP is a generalised natural transformation: *)
lemma flatP_lift:
  assumes Da: "Da \<subseteq> Subdis A" 
    and Db: "Db \<subseteq> Subdis B"
    and Dab: "\<forall>p\<in>Da. lift A f p \<in> Db"
  assumes f: "\<forall>a\<in>A. f a \<in> B" and pp: "pp \<in> Subdis Da" and b: "b \<in> B"
  shows "flatP Db (lift Da (lift A f) pp) b = lift A f (flatP Da pp) b"
proof-
  have 0: "\<And>p. p \<in> Subdis A \<Longrightarrow> positive (\<lambda>a. p a * ind (f a) b) A
               \<and> sbounded (\<lambda>a. p a * ind (f a) b) A"
    apply safe 
    subgoal using assms unfolding positive_def by (simp add: Subdis_ge_0)
    subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms  
      by (auto simp: ind_le_1) .
  show ?thesis 
    unfolding lift_ext[OF pp] unfolding ext_def flatP_def
    apply(subst lift_ext)
    subgoal unfolding Subdis_def apply(subst Subdis_def[symmetric])
      by (metis (no_types, lifting) Da Subdis_eq flatP_Subdis flatP_def isum_cong pp) 
    subgoal unfolding ext_def 
      subgoal 
        apply(rule trans[of _ "isum (\<lambda>p. isum (\<lambda>a. pp a * (ind \<circ> lift A f) a p * p b) 
              Da) Db"])
        subgoal apply(rule isum_cong)
          subgoal by simp
          subgoal for p apply(subst isum_distribR)
            subgoal using assms unfolding positive_def by (simp add: Subdis_ge_0)
            subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: ind_le_1) 
            subgoal by (meson Db Subdis_ge_0 b subsetD) 
            subgoal by simp . . 
        subgoal 
          apply(rule trans[of _ "isum (\<lambda>a. isum (\<lambda>p. pp p * p a * (ind \<circ> f) a b) Da) A"])
          subgoal apply(subst isum_swap[of _ _ Da]) 
            subgoal unfolding mult.assoc apply(rule sbounded_prod_Subdis)
              subgoal unfolding Subdis_def[of Db] mem_Collect_eq apply safe
                subgoal using assms unfolding positive_def 
                  by (metis Subdis_ge_0 comp_apply in_mono ind_ge_0 mult_nonneg_nonneg)
                subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1) 
                subgoal for p apply(rule isum_le_singl[of _ "lift A f p" _ Db]) 
                  subgoal by simp (meson Dab Db Subdis_le_1 b in_mono)
                  subgoal by simp
                  subgoal by simp (meson Dab Db Subdis_ge_0 b in_mono)
                  subgoal using Dab by simp . .
              subgoal by fact .
            subgoal apply(subst isum_swap[of _ _ Da]) 
              subgoal unfolding mult.assoc apply(rule sbounded_prod_Subdis)
                subgoal using Da by (auto intro!: ind_mult_SubdisL) 
                subgoal by fact .
              subgoal apply(rule isum_cong)
                subgoal by simp 
                subgoal for p unfolding o_def lift_def mult.assoc
                  subgoal apply(subst isum_distribL[symmetric])
                    subgoal using assms unfolding positive_def 
                      by (meson Subdis_ge_0 in_mono ind_ge_0 mult_nonneg_nonneg)
                    subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1) 
                    subgoal using Subdis_ge_0 pp by fastforce
                    subgoal apply(subst isum_distribL[symmetric])
                      subgoal using assms unfolding positive_def 
                        by (meson Subdis_ge_0 in_mono ind_ge_0 mult_nonneg_nonneg)
                      subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1) 
                      subgoal using Subdis_ge_0 pp by fastforce
                      subgoal unfolding mult_cancel_left apply(rule disjI2)  
                        apply(rule isum_eq_singl[of _ "\<lambda>b. isum p {a \<in> A. f a = b}"])
                        subgoal unfolding Subdis_def using Da  
                          by (fastforce intro: isum_zeros_cong sbounded_mono[of _ A p] simp: Subdis_def)                      
                        subgoal by simp
                        subgoal apply(rule isum_ge_0) using Da 0 by auto
                        subgoal unfolding lift_def[symmetric] by (simp add: Dab) . . . . . . .
          subgoal apply(rule isum_cong)
            subgoal by simp
            subgoal for p apply(subst isum_distribR)
              subgoal using assms unfolding positive_def 
                by (metis Subdis_ge_0 in_mono mult_nonneg_nonneg)  
              subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1)
              subgoal using assms by (simp add: ind_ge_0)
              subgoal by simp . . . . . . 
qed

(* Associativity of flatP: *) 
lemma flatP_flatP_lift: 
  assumes Da: "Da \<subseteq> Subdis A"  
    and fDa: "\<forall>pp \<in> Daa. flatP Da pp \<in> Da"
    and Daa: "Daa \<subseteq> Subdis Da"
  assumes ppp: "ppp \<in> Subdis Daa" and a: "a \<in> A"
  shows "flatP Da (flatP Daa ppp) a = flatP Da (lift Daa (flatP Da) ppp) a"
  unfolding flatP_def lift_ext[OF ppp] ext_def
  apply(rule trans[of _ "isum (\<lambda>p. isum (\<lambda>pp. ppp pp * pp p * p a) Daa) Da"])
  subgoal apply(rule isum_cong)
    subgoal by simp
    subgoal apply(rule isum_distribR)
      subgoal using assms unfolding Subdis_def[of Daa] positive_def
        by (metis (no_types, lifting) Subdis_ge_0 in_mono mult_nonneg_nonneg ppp)
      subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1) 
      subgoal by (meson Da Subdis_ge_0 a subsetD) . .
  subgoal apply(subst isum_swap)
    subgoal apply(subst mult.assoc) apply(rule sbounded_prod_Subdis)
      subgoal unfolding Subdis_def mem_Collect_eq apply safe unfolding Subdis_def[symmetric]
        subgoal using assms unfolding positive_def  
          by (metis Subdis_ge_0 split_mult_pos_le subset_iff)  
        subgoal apply(rule Subdis_sboundedL[of _ _ _ 1])  
          using assms Subdis_def by (auto simp: Subdis_le_1)
        subgoal by (metis (full_types) Da Daa Subdis_le_1 a flatP_Subdis flatP_def in_mono) .
      subgoal by fact .
        (*  *)
    subgoal apply(rule trans[of _ 
            "isum (\<lambda>p. isum (\<lambda>pp. ppp pp * (ind \<circ> (\<lambda>pp a. isum (\<lambda>p. pp p * p a) Da)) pp p * p a)
           Daa) Da"]) 
      subgoal apply(subst isum_swap[of _ Da])
        subgoal apply(subst mult.assoc) apply(rule sbounded_prod_Subdis)
          subgoal unfolding Subdis_def mem_Collect_eq apply safe unfolding Subdis_def[symmetric]
            subgoal using assms unfolding positive_def  
              by simp (meson Subdis_ge_0 in_mono ind_ge_0 mult_nonneg_nonneg)
            subgoal apply(rule Subdis_sboundedL[of _ _ _ 1])  
              using assms Subdis_def by (auto simp: Subdis_le_1)
            subgoal for p unfolding o_def  
              by (metis (no_types) Da Subdis_le_1 a flatP_Subdis flatP_def ind_Subdis) .
          subgoal by fact .
        subgoal apply(rule isum_cong)
          subgoal by simp
          subgoal for pp unfolding mult.assoc apply(subst isum_distribL[symmetric])
            subgoal using assms unfolding positive_def 
              by (metis Subdis_ge_0 mult_nonneg_nonneg subset_eq)
            subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1) 
            subgoal using Subdis_ge_0 ppp by fastforce
            subgoal apply(subst isum_distribL[symmetric])
              subgoal using assms unfolding positive_def 
                by (smt Subdis_ge_0 comp_apply in_mono ind_ge_0 mult_nonneg_nonneg)
              subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1) 
              subgoal using Subdis_ge_0 ppp by fastforce 
              subgoal unfolding mult_cancel_left apply(rule disjI2)
                unfolding o_def apply(subst isum_ind_multR) 
                subgoal unfolding flatP_def[symmetric] using Daa fDa by auto 
                subgoal apply(rule isum_ge_0)
                  subgoal using assms unfolding positive_def  
                    by (metis Subdis_ge_0 mult_nonneg_nonneg subset_iff) 
                  subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1) .
                subgoal by simp . . . . .
      subgoal apply(rule isum_cong)
        subgoal by auto
        apply(rule isum_distribR[symmetric])
        subgoal using assms unfolding positive_def by (simp add: Subdis_ge_0 ind_ge_0)
        subgoal apply(rule Subdis_sboundedL[of _ _ _ 1]) using assms by (auto simp: Subdis_le_1 ind_le_1) 
        subgoal using Da by (auto simp: Subdis_ge_0 a) . . . .


(* The subdistribution monad counit: flat *)

definition flat :: "'a set \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)" where 
  "flat A pp \<equiv> \<lambda>a. isum (\<lambda>p. pp p * p a) (Subdis A)"

(* It is the instance of flatP for Ba = Subdis A: *) 
lemma flat_flatP: "flat A = flatP (Subdis A)"
  by (auto simp: flat_def flatP_def)

(* Now we instantiate the monadic properties of flatP: *)
(* "flat" is the Kleisli lifting of the identity function on subdistributions: *)
lemma flat_ext: "flat A = ext (Subdis A) id"
  unfolding flat_flatP using flatP_ext .

(* Well-definedness of flat: *)
lemma flat_eq: "\<forall>p\<in>Subdis A. pp1 p = pp2 p \<Longrightarrow> a \<in> A \<Longrightarrow> flat A pp1 a = flat A pp2 a"
  by (simp add: flatP_eq flat_flatP)

lemma flat_Subdis: "pp \<in> Subdis (Subdis A) \<Longrightarrow> flat A pp \<in> Subdis A"
  unfolding flat_flatP apply(rule flatP_Subdis) by auto 

(* flat left inverse of lifted ind *)
lemma flat_lift_ind: 
  assumes p: "p \<in> Subdis A" and a: "a \<in> A"
  shows "flat A (lift A ind p) a = p a"
  by (simp add: a flatP_lift_ind flat_flatP image_subsetI p subset_eq) 

(* flat left inverse of ind *)
lemma flat_ind: 
  assumes "p \<in> Subdis A" and "a \<in> A"
  shows "flat A (ind p) a = p a"
  by (metis assms flatP_ind flat_flatP subset_iff)

(* flat natural transformation: *)
lemma flat_lift:
  assumes f: "\<forall>a\<in>A. f a \<in> B" and pp: "pp \<in> Subdis (Subdis A)" and b: "b \<in> B"
  shows "flat B (lift (Subdis A) (lift A f) pp) b = lift A f (flat A pp) b"
  unfolding flat_flatP apply(rule flatP_lift) 
  using assms using lift_Subdis by fastforce+

(* Associativity of flat: *)
lemma flat_flat_lift: 
  assumes ppp: "ppp \<in> Subdis (Subdis (Subdis A))" and a: "a \<in> A"
  shows "flat A (flat (Subdis A) ppp) a = flat A (lift (Subdis (Subdis A)) (flat A) ppp) a"
  unfolding flat_flatP apply(rule flatP_flatP_lift) 
  using assms by (auto intro: flatP_Subdis)


(* The distribution monad counit: dflat *)

definition dflat :: "'a set \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)" where 
  "dflat A pp \<equiv> \<lambda>a. isum (\<lambda>p. pp p * p a) (Dis A)"

(* It is the instance of flatP for Ba = Dis A: *) 
lemma dflat_flatP: "dflat A = flatP (Dis A)"
  by (auto simp: dflat_def flatP_def)

(* Now we instantiate the monadic properties of flatP: *)
(* "flat" is the Kleisli lifting of the identity function on subdistributions: *)
lemma dflat_ext: "dflat A = ext (Dis A) id"
  unfolding dflat_flatP using flatP_ext .

(* Well-definedness of dflat: *)
lemma dflat_eq: "\<forall>p\<in>Dis A. pp1 p = pp2 p \<Longrightarrow> a \<in> A \<Longrightarrow> dflat A pp1 a = dflat A pp2 a"
  by (metis dflat_flatP flatP_eq)

lemma dflat_Subdis: "pp \<in> Subdis (Dis A) \<Longrightarrow> dflat A pp \<in> Subdis A"
  by (simp add: Dis_incl_Subdis dflat_flatP flatP_Subdis)

lemma dflat_Dis: "pp \<in> Dis (Dis A) \<Longrightarrow> dflat A pp \<in> Dis A"
  by (simp add: dflat_ext ext_Dis) 

(* flat left inverse of lifted ind *)
lemma dflat_lift_ind: 
  assumes p: "p \<in> Dis A" and a: "a \<in> A"
  shows "dflat A (lift A ind p) a = p a"
  by (metis Dis_Subdis_mono Dis_ind a dflat_flatP flatP_lift_ind image_subsetI p subsetI)

(* flat left inverse of ind *)
lemma dflat_ind: 
  assumes "p \<in> Dis A" and "a \<in> A"
  shows "dflat A (ind p) a = p a"
  by (metis Dis_incl_Subdis assms dflat_flatP flatP_ind)

(* dflat natural transformation: *)
lemma dflat_lift_Subdis:
  assumes f: "\<forall>a\<in>A. f a \<in> B" and pp: "pp \<in> Subdis (Dis A)" and b: "b \<in> B"
  shows "dflat B (lift (Dis A) (lift A f) pp) b = lift A f (dflat A pp) b"
  unfolding dflat_flatP apply(rule flatP_lift) 
  using assms using lift_Subdis Dis_incl_Subdis by (fastforce simp: lift_Dis)+

corollary dflat_lift:
  assumes f: "\<forall>a\<in>A. f a \<in> B" and pp: "pp \<in> Dis (Dis A)" and b: "b \<in> B"
  shows "dflat B (lift (Dis A) (lift A f) pp) b = lift A f (dflat A pp) b"
  by (meson Dis_incl_Subdis b dflat_lift_Subdis f in_mono pp)

(* Associativity of dflat: *)
lemma dflat_dflat_lift_Subdis: 
  assumes ppp: "ppp \<in> Subdis (Dis (Dis A))" and a: "a \<in> A"
  shows "dflat A (dflat (Dis A) ppp) a = dflat A (lift (Dis (Dis A)) (dflat A) ppp) a"
  by (metis Dis_incl_Subdis Dis_incl_Subdis a dflat_Dis dflat_flatP dflat_flatP flatP_flatP_lift ppp)

corollary dflat_dflat_lift: 
  assumes ppp: "ppp \<in> Dis (Dis (Dis A))" and a: "a \<in> A"
  shows "dflat A (dflat (Dis A) ppp) a = dflat A (lift (Dis (Dis A)) (dflat A) ppp) a"
  by (meson Dis_incl_Subdis a dflat_dflat_lift_Subdis in_mono ppp)

(* Relationship between flat and dflat *)

(* As noted before, unlike for the other operators, we cannot use the same operator 
for flattening / averaging subdistributions and distributions -- hence we need both 
"flat" and "dflat". Yet, these operators are closely related, in particular they coincide 
on subdistributions for distributions pp that assign zero weight to all non-distributions 
subdistributions p. 
*)

lemma dflat_from_flat: 
  assumes pp: "pp \<in> Subdis (Dis A)" and a: "a \<in> A"
  shows "dflat A pp a = flat A (\<lambda>p. if p \<in> Dis A then pp p else 0) a" 
  using assms unfolding dflat_def flat_def apply(intro isum_zeros_cong)
  subgoal  apply(rule disjI1) apply(rule Subdis_sboundedL[of _ _ _ 1]) 
    by (auto simp: Subdis_mono Subdis_le_1)  
  subgoal by auto
  subgoal using Dis_incl_Subdis by auto
  subgoal by auto .

(* We'll use this lemma to let dflat borrow the monadic properties of flat: *)
lemma dflat_flat: 
  assumes pp: "pp \<in> Subdis (Dis A)" and a: "a \<in> A" and "\<forall>p\<in>Subdis A - Dis A. pp p = 0"
  shows "dflat A pp a = flat A pp a" 
  by (simp add: assms dflat_from_flat flat_eq)

lemma dflat_flat': 
  assumes pp: "pp \<in> Dis (Dis A)" and a: "a \<in> A" and "\<forall>p\<in>Subdis A - Dis A. pp p = 0"
  shows "dflat A pp a = flat A pp a" 
  by (meson assms Dis_incl_Subdis dflat_flat in_mono)



subsection \<open>Expectation\<close>


(* Expected value of a random variable w.r.t. a subdistribution *)

definition expd :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where 
  "expd A p X \<equiv> isum (\<lambda>a. p a * X a) A"

(* Extension expressed as an expectation: *)
lemma ext_expd: "ext A f p b = expd A p (\<lambda>a. f a b)"
  unfolding ext_def expd_def by auto

(* Basic properties of expectation *)

lemma expd_ge_0': 
  assumes "p \<in> Subdis A" and "positive f A" and "sbounded (\<lambda>a. p a * f a) A"
  shows "expd A p f \<ge> 0"
  by (metis (mono_tags, lifting) positive_def Subdis_def assms expd_def 
      isum_ge_0 mem_Collect_eq mult_nonneg_nonneg)

lemma expd_ge_0: 
  assumes p: "p \<in> Subdis A" and f: "positive f A" "\<forall>a\<in>A. f a \<le> x"
  shows "expd A p f \<ge> 0"
  by (meson Subdis_sboundedL expd_ge_0' assms)

lemma expd_le_upper: 
  assumes p: "p \<in> Subdis A" and f: "positive f A" "\<forall>a\<in>A. f a \<le> x" and x: "x \<ge> 0"
  shows "expd A p f \<le> x"
  unfolding expd_def apply(rule order.trans[of _ " isum (\<lambda>a. p a * x) A"])
  subgoal apply(rule isum_mono)
    subgoal apply(rule sbounded_multR)
      using x f(2) Subdis_def p by auto
    subgoal by (meson Subdis_ge_0 f(2) mult_left_mono p) . 
  subgoal apply(subst isum_distribR[symmetric])
    using assms x unfolding Subdis_def  
    by (auto simp: mult.commute mult_left_le) .

lemma expd_ge_lower_Subdis: 
  assumes p: "p \<in> Subdis A" and f: "\<forall>a\<in>A. f a \<ge> x" and x: "x \<ge> 0"
    and pf: "sbounded (\<lambda>a. p a * f a) A"
  shows "expd A p f \<ge> x * isum p A"
proof- 
  have f2: "positive f A" using f x unfolding positive_def by auto
  show ?thesis 
    unfolding expd_def apply(rule order.trans[of _ "isum (\<lambda>a. p a * x) A"])
    apply (smt (verit, best) Subdis_def isum_cong isum_distribL mem_Collect_eq mult_commute_abs p x)
    by (smt (verit) Subdis_ge_0 f isum_mono mult_mono p pf x)
qed 

lemma expd_ge_lower_Dis': 
  assumes p: "p \<in> Dis A" and f: "\<forall>a\<in>A. f a \<ge> x" and x: "x \<ge> 0"
    and pf: "sbounded (\<lambda>a. p a * f a) A"
  shows "expd A p f \<ge> x"
  apply(rule order.trans[OF _ expd_ge_lower_Subdis])
  using assms Dis_Subdis_mono by (auto simp: Dis_isum_1)

lemma expd_ge_lower_Dis:
  assumes p: "p \<in> Dis A" and f: "\<forall>a\<in>A. f a \<ge> x" "\<forall>a\<in>A. f a \<le> y" 
    and xy: "x \<ge> 0" "y \<ge> 0" 
  shows "expd A p f \<ge> x"
proof-
  have "sbounded (\<lambda>a. p a * f a) A" 
    using Dis_incl_Subdis Subdis_sboundedL f(2) p by blast
  thus ?thesis using assms apply(intro expd_ge_lower_Dis') by auto
qed

lemma expd_ge01:
  assumes p: "p \<in> Subdis A" and f: "\<forall>a\<in>A. f a \<ge> 0" "\<forall>a\<in>A. f a \<le> 1" 
  shows "expd A p f \<ge> 0"
  apply(rule order.trans[OF _ expd_ge_lower_Subdis])
  using assms Dis_Subdis_mono by (auto simp: Subdis_sboundedL)

lemma expd_le01:
  assumes p: "p \<in> Subdis A" and f: "\<forall>a\<in>A. f a \<ge> 0" "\<forall>a\<in>A. f a \<le> 1" 
  shows "expd A p f \<le> 1"
  by (simp add: positive_def expd_le_upper assms)

lemma expd_const_Subdis[simp]: 
  assumes p: "p \<in> Subdis A" and "c \<ge> 0"
  shows "expd A p (\<lambda>_. c) = c * isum p A"
  unfolding expd_def apply(subst isum_distribR[symmetric])
  using assms unfolding Subdis_def by auto

lemma expd_const_le: 
  assumes p: "p \<in> Subdis A" and "c \<ge> 0"
  shows "expd A p (\<lambda>_. c) \<le> c"
  apply(subst expd_const_Subdis[OF assms])
  using assms by (simp add: Subdis_def mult_left_le)

lemma expd_const_Dis[simp]: 
  assumes p: "p \<in> Dis A" and "c \<ge> 0"
  shows "expd A p (\<lambda>_. c) = c"
  apply(subst expd_const_Subdis)
  using assms unfolding Dis_def Subdis_def by auto

lemma expd_eq_ct_iff[simp]: 
  assumes "p \<in> Subdis A" "c > 0"
  shows "expd A p (\<lambda>_. c) = c \<longleftrightarrow> p \<in> Dis A"
proof -
  have "c = c * isum p A \<longrightarrow> p \<in> Dis A"
    using Dis_def assms by fastforce
  then show ?thesis
    by (metis (no_types) assms expd_const_Dis expd_const_Subdis less_le)
qed

lemma expd_0[simp]: "expd A p (\<lambda>_. 0) = 0"
  unfolding expd_def by simp

lemma expd_1_le_1: "p \<in> Subdis A \<Longrightarrow> expd A p (\<lambda>_. 1) \<le> 1"
  using expd_const_le zero_le_one by blast

lemma expd_1_eq_1[simp]: "p \<in> Dis A \<Longrightarrow> expd A p (\<lambda>_. 1) = 1"
  by simp

lemma expd_plus': 
  assumes p: "p \<in> Subdis A" 
    and f1: "positive f1 A" "sbounded (\<lambda>a. p a * f1 a) A" 
    and f2: "positive f2 A" "sbounded (\<lambda>a. p a * f2 a) A"
  shows "expd A p (\<lambda>a. f1 a + f2 a) = expd A p f1 + expd A p f2"
  unfolding expd_def apply(rule trans[of _ "isum (\<lambda>a. p a * f1 a + p a * f2 a) A"]) 
  subgoal apply(rule isum_cong) by (simp_all add: distrib_left)
  subgoal apply(subst isum_plus)
    using assms unfolding Subdis_def positive_def by auto .

lemma expd_plus: 
  assumes p: "p \<in> Subdis A" 
    and f1: "positive f1 A" "bdd_above (f1`A)" 
    and f2: "positive f2 A" "bdd_above (f2`A)" 
  shows "expd A p (\<lambda>a. f1 a + f2 a) = expd A p f1 + expd A p f2"
  apply(rule expd_plus')
  using assms unfolding bdd_above_def by (auto simp add: Subdis_sboundedL) 

lemma expd_mult': 
  assumes p: "p \<in> Subdis A"  
    and f: "positive f A" "sbounded (\<lambda>a. p a * f a) A" and c: "c \<ge> 0"
  shows "expd A p (\<lambda>a. c * f a) = c * expd A p f"
  unfolding expd_def unfolding mult.left_commute apply(rule isum_distribL[symmetric])
  using assms unfolding Subdis_def positive_def by auto

lemma expd_mult: 
  assumes p: "p \<in> Subdis A"  
    and f: "positive f A" "bdd_above (f`A)" and c: "c \<ge> 0"
  shows "expd A p (\<lambda>a. c * f a) = c * expd A p f"
  apply(rule expd_mult')
  using assms unfolding bdd_above_def by (auto simp: Subdis_sboundedL)


end