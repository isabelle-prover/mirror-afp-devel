section \<open>The FKG inequality\<close>

text \<open>The FKG inequality~\cite{fortuin1971} is a generalization of Chebyshev's less known other
inequality. It is sometimes referred to as Chebyshev's sum inequality. Although there is a also
a continuous version, which can be stated as:

\[
  E [ f g ] \geq E[f] E [g]
\]

where $f$, $g$ are continuous simultaneously monotone or simultaneously antimonotone
functions on the Lebesgue probability space $[a,b] \subseteq \mathbb R$. ($E f$ denotes the
expectation of the function.)

Note that the inequality is also true for totally ordered discrete probability spaces, for example:
$\{1,\ldots,n\}$ with uniform probabilities.

The FKG inequality is essentially a generalization of the above to not necessarily totally ordered
spaces, but finite distributive lattices.

The proof follows the derivation in the book by Alon and Spencer~\cite[Ch. 6]{alon2000}.\<close>

theory Negative_Association_FKG_Inequality
  imports
    Negative_Association_Util
    Birkhoff_Finite_Distributive_Lattices.Birkhoff_Finite_Distributive_Lattices
begin

theorem four_functions_helper:
  fixes \<phi> :: "nat \<Rightarrow> 'a set \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> {0..3} \<Longrightarrow> \<phi> i \<in> Pow I \<rightarrow> {0..}"
  assumes "\<And>A B. A \<subseteq> I \<Longrightarrow> B \<subseteq> I \<Longrightarrow> \<phi> 0 A * \<phi> 1 B \<le> \<phi> 2 (A \<union> B) * \<phi> 3 (A \<inter> B)"
  shows "(\<Sum>A\<in>Pow I. \<phi> 0 A)*(\<Sum>B\<in>Pow I. \<phi> 1 B) \<le> (\<Sum>C\<in>Pow I. \<phi> 2 C)*(\<Sum>D\<in>Pow I. \<phi> 3 D)"
  using assms
proof (induction I arbitrary:\<phi> rule:finite_induct)
  case empty
  then show ?case using empty by auto
next
  case (insert x I)
  define \<phi>' where "\<phi>' i A = \<phi> i A + \<phi> i (A \<union> {x})" for i A

  have a:"(\<Sum>A\<in>Pow (insert x I). \<phi> i A) = (\<Sum>A\<in>Pow I. \<phi>' i A)" (is "?L1 = ?R1") for i
  proof -
    have "?L1 = (\<Sum>A\<in>Pow I. \<phi> i A) + (\<Sum>A\<in>insert x ` Pow I. \<phi> i A)"
      using insert(1,2) unfolding Pow_insert by (intro sum.union_disjoint) auto
    also have "\<dots> = (\<Sum>A\<in>Pow I. \<phi> i A) + (\<Sum>A\<in>Pow I. \<phi> i (insert x A))"
      using insert(2) by (subst sum.reindex) (auto intro!:inj_onI)
    also have "\<dots> = ?R1" using insert(1) unfolding \<phi>'_def sum.distrib by simp
    finally show ?thesis by simp
  qed

  have \<phi>_int: "\<phi> 0 A * \<phi> 1 B \<le> \<phi> 2 C * \<phi> 3 D"
    if "C = A \<union> B" "D = A \<inter> B" "A \<subseteq> insert x I" "B \<subseteq> insert x I" for A B C D
    using that insert(5) by auto

  have \<phi>_nonneg: "\<phi> i A \<ge> 0" if "A \<subseteq> insert x I" "i \<in> {0..3}" for i A
    using that insert(4) by auto

  have "\<phi>' 0 A * \<phi>' 1 B \<le> \<phi>' 2 (A \<union> B) * \<phi>' 3 (A \<inter> B)" if "A \<subseteq> I" "B \<subseteq> I" for A B
  proof -
    define a0 a1 where a: "a0 = \<phi> 0 A" "a1 = \<phi> 0 (insert x A)"
    define b0 b1 where b: "b0 = \<phi> 1 B" "b1 = \<phi> 1 (insert x B)"
    define c0 c1 where c: "c0 = \<phi> 2 (A \<union> B)" "c1 = \<phi> 2 (insert x (A \<union> B))"
    define d0 d1 where d: "d0 = \<phi> 3 (A \<inter> B)" "d1 = \<phi> 3 (insert x (A \<inter> B))"

    have 0:"a0 * b0 \<le> c0 * d0" using that unfolding a b c d by (intro \<phi>_int) auto
    have 1:"a0 * b1 \<le> c1 * d0" using that insert(2) unfolding a b c d by (intro \<phi>_int) auto
    have 2:"a1 * b0 \<le> c1 * d0" using that insert(2) unfolding a b c d by (intro \<phi>_int) auto
    have 3:"a1 * b1 \<le> c1 * d1" using that insert(2) unfolding a b c d by (intro \<phi>_int) auto
    have 4:"a0 \<ge> 0" "a1 \<ge> 0" "b0 \<ge> 0" "b1 \<ge> 0" using that unfolding a b by (auto intro!: \<phi>_nonneg)
    have 5:"c0 \<ge> 0" "c1 \<ge> 0" "d0 \<ge> 0" "d1 \<ge> 0" using that unfolding c d by (auto intro!: \<phi>_nonneg)

    consider  (a) "c1 = 0" | (b) "d0 = 0" | (c) "c1 > 0" "d0 > 0" using 4 5 by argo

    then have "(a0 + a1) * (b0 + b1) \<le> (c0 + c1) * (d0 + d1)"
    proof (cases)
      case a
      hence "a0 * b1 = 0" "a1 * b0 = 0" "a1 * b1 = 0"
        using 1 2 3 by (intro order_antisym mult_nonneg_nonneg 4 5;simp_all)+
      then show ?thesis unfolding distrib_left distrib_right
        using 0 4 5 by (metis add_mono mult_nonneg_nonneg)
    next
      case b
      hence "a0 * b0 = 0" "a0 * b1 = 0" "a1 * b0 = 0"
        using 0 1 2 by (intro order_antisym mult_nonneg_nonneg 4 5;simp_all)+
      then show ?thesis unfolding distrib_left distrib_right
        using 3 4 5 by (metis add_mono mult_nonneg_nonneg)
    next
      case c
      have "0 \<le> (c1*d0-a0*b1) * (c1*d0 - a1*b0)"
        using 1 2 by (intro mult_nonneg_nonneg) auto
      hence "(a0 + a1) * (b0 + b1)*d0*c1 \<le> (a0*b0 + c1*d0) * (c1*d0 + a1*b1)"
        by (simp add:algebra_simps)
      hence "(a0 + a1) * (b0 + b1) \<le> ((a0*b0)/d0 + c1) * (d0 + (a1*b1)/c1)"
        using c 4 5 by (simp add:field_simps)
      also have "\<dots> \<le> (c0 + c1) * (d0 + d1)"
        using 0 3 c 4 5 by (intro mult_mono add_mono order.refl) (simp add:field_simps)+
      finally show ?thesis by simp
    qed

    thus ?thesis unfolding \<phi>'_def a b c d by auto
  qed

  moreover have "\<phi>' i \<in> Pow I \<rightarrow> {0..}" if "i \<in> {0..3}" for i
    using insert(4)[OF that] unfolding \<phi>'_def by (auto intro!:add_nonneg_nonneg)
  ultimately show ?case unfolding a by (intro insert(3)) auto
qed

text \<open>The following is the Ahlswede-Daykin inequality~\cite{ahlswede1978} also referred to by
Alon and Spencer as the four functions theorem~\cite[Th. 6.1.1]{alon2000}.\<close>

theorem four_functions:
  fixes \<alpha> \<beta> \<gamma> \<delta> :: "'a set \<Rightarrow> real"
  assumes "finite I"
  assumes "\<alpha> \<in> Pow I \<rightarrow> {0..}" "\<beta> \<in> Pow I \<rightarrow> {0..}" "\<gamma> \<in> Pow I \<rightarrow> {0..}" "\<delta> \<in> Pow I \<rightarrow> {0..}"
  assumes "\<And>A B. A \<subseteq> I \<Longrightarrow> B \<subseteq> I \<Longrightarrow> \<alpha> A * \<beta> B \<le> \<gamma> (A \<union> B) * \<delta> (A \<inter> B)"
  assumes "M \<subseteq> Pow I" "N \<subseteq> Pow I"
  shows "(\<Sum>A\<in>M. \<alpha> A)*(\<Sum>B\<in>N. \<beta> B) \<le> (\<Sum>C| \<exists>A\<in>M. \<exists>B\<in>N. C=A\<union>B. \<gamma> C)*(\<Sum>D| \<exists>A\<in>M. \<exists>B\<in>N. D=A\<inter>B. \<delta> D)"
    (is "?L \<le> ?R")
proof -
  define \<alpha>' where "\<alpha>' A = (if A \<in> M then \<alpha> A else 0)" for A
  define \<beta>' where "\<beta>' B = (if B \<in> N then \<beta> B else 0)" for B
  define \<gamma>' where "\<gamma>' C = (if \<exists>A\<in>M. \<exists>B\<in>N. C=A\<union>B then \<gamma> C else 0)" for C
  define \<delta>' where "\<delta>' D = (if \<exists>A\<in>M. \<exists>B\<in>N. D=A\<inter>B then \<delta> D else 0)" for D

  define \<phi> where "\<phi> i = [\<alpha>',\<beta>',\<gamma>',\<delta>'] ! i" for i

  have "list_all (\<lambda>i. \<phi> i \<in> Pow I \<rightarrow> {0..}) [0..<4]"
    unfolding \<phi>_def  \<alpha>'_def \<beta>'_def \<gamma>'_def \<delta>'_def using assms(2-5)
    by (auto simp add:numeral_eq_Suc)
  hence \<phi>_nonneg: "\<phi> i \<in> Pow I \<rightarrow> {0..}" if "i \<in> {0..3}" for i
    unfolding list.pred_set using that by auto

  have 0: "\<phi> 0 A * \<phi> 1 B \<le> \<phi> 2 (A \<union> B) * \<phi> 3 (A \<inter> B)" (is "?L1 \<le> ?R1") if "A \<subseteq> I" "B \<subseteq> I" for A B
  proof (cases "A \<in> M \<and> B \<in> N")
    case True
    have "?L1 = \<alpha> A * \<beta> B" using True unfolding \<phi>_def \<alpha>'_def \<beta>'_def by auto
    also have "\<dots> \<le> \<gamma> (A \<union> B) * \<delta> (A \<inter> B)" by(intro that assms(6))
    also have "\<dots> = ?R1" using True unfolding \<gamma>'_def \<delta>'_def \<phi>_def by auto
    finally show ?thesis by simp
  next
    case False
    hence "?L1 = 0" unfolding \<alpha>'_def \<beta>'_def \<phi>_def by auto
    also have "\<dots> \<le> ?R1" using \<phi>_nonneg[of "2"] \<phi>_nonneg[of "3"] that
      by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  have fin_pow: "finite (Pow I)" using assms(1) by simp

  have "?L = (\<Sum>A \<in> Pow I. \<alpha>' A) * (\<Sum>B \<in> Pow I. \<beta>' B)"
    unfolding \<alpha>'_def \<beta>'_def using assms(1,7,8) by (simp add: sum.If_cases Int_absorb1)
  also have "\<dots> = (\<Sum>A \<in> Pow I. \<phi> 0 A) * (\<Sum>A \<in> Pow I. \<phi> 1 A)" unfolding \<phi>_def by simp
  also have "\<dots> \<le> (\<Sum>A \<in> Pow I. \<phi> 2 A) * (\<Sum>A \<in> Pow I. \<phi> 3 A)"
    by (intro four_functions_helper assms(1) \<phi>_nonneg 0) auto
  also have "\<dots> = (\<Sum>A \<in> Pow I. \<gamma>' A) * (\<Sum>B \<in> Pow I. \<delta>' B)" unfolding \<phi>_def by simp
  also have "\<dots> = ?R"
    unfolding \<gamma>'_def \<delta>'_def sum.If_cases[OF fin_pow] sum.neutral_const add_0_right using assms(7,8)
    by (intro arg_cong2[where f="(*)"] sum.cong refl) auto
  finally show ?thesis by simp
qed

text \<open>Using Birkhoff's Representation
Theorem~\cite{birkhoff1967,Birkhoff_Finite_Distributive_Lattices-AFP} it is possible to generalize
the previous to finite distributive lattices~\cite[Cor. 6.1.2]{alon2000}.\<close>
lemma four_functions_in_lattice:
  fixes \<alpha> \<beta> \<gamma> \<delta> :: "'a :: finite_distrib_lattice  \<Rightarrow> real"
  assumes "range \<alpha> \<subseteq> {0..}" "range \<beta> \<subseteq> {0..}" "range \<gamma> \<subseteq> {0..}" "range \<delta> \<subseteq> {0..}"
  assumes "\<And>x y. \<alpha> x * \<beta> y \<le> \<gamma> (x \<squnion> y) * \<delta> (x \<sqinter> y)"
  shows "(\<Sum>x\<in>M. \<alpha> x)*(\<Sum>y\<in>N. \<beta> y) \<le> (\<Sum>c| \<exists>x\<in>M. \<exists>y\<in>N. c=x\<squnion>y. \<gamma> c)*(\<Sum>d| \<exists>x\<in>M. \<exists>y\<in>N. d=x\<sqinter>y. \<delta> d)"
    (is "?L \<le> ?R")
proof -
  let ?e = "\<lambda>x::'a. \<lbrace> x \<rbrace>"
  let ?f = "the_inv ?e"

  have ran_e: "range ?e = \<O>\<J>" by (rule bij_betw_imp_surj_on[OF birkhoffs_theorem])
  have inj_e: "inj ?e" by (rule bij_betw_imp_inj_on[OF birkhoffs_theorem])

  define conv :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real"
    where "conv \<phi> I = (if I \<in> \<O>\<J> then \<phi>(?f I) else 0)" for \<phi> I

  define \<alpha>' \<beta>' \<gamma>' \<delta>' where prime_def:"\<alpha>' = conv \<alpha>" "\<beta>' = conv \<beta>" "\<gamma>' = conv \<gamma>" "\<delta>' = conv \<delta>"

  have 1:"conv \<phi> \<in> Pow \<J> \<rightarrow> {0..}" if "range \<phi> \<subseteq> {(0::real)..}" for \<phi>
    using that unfolding conv_def by (intro Pi_I) auto

  have 0:"\<alpha>' A * \<beta>' B \<le> \<gamma>' (A \<union> B) * \<delta>' (A \<inter> B)" if "A \<subseteq> \<J>" "B \<subseteq> \<J>" for A B
  proof (cases "A \<in> \<O>\<J> \<and> B \<in> \<O>\<J>")
    case True
    define x y where xy: "x = ?f A" "y = ?f B"

    have p0:"?e (x \<squnion> y) = A \<union> B"
      using True ran_e unfolding join_irreducibles_join_homomorphism xy
      by (subst (1 2) f_the_inv_into_f[OF inj_e]) auto
    hence p1:"A \<union> B \<in> \<O>\<J>" using ran_e by auto

    have p2:"?e (x \<sqinter> y) = A \<inter> B"
      using True ran_e unfolding join_irreducibles_meet_homomorphism xy
      by (subst (1 2) f_the_inv_into_f[OF inj_e]) auto
    hence p3:"A \<inter> B \<in> \<O>\<J>" using ran_e by auto

    have "\<alpha>' A * \<beta>' B = \<alpha> (?f A) * \<beta> (?f B) " using True unfolding prime_def conv_def by simp
    also have "\<dots> \<le> \<gamma> (?f A \<squnion> ?f B) * \<delta> (?f A \<sqinter> ?f B)" by (intro assms(5))
    also have "\<dots> = \<gamma> (x \<squnion> y) * \<delta> (x \<sqinter> y)" unfolding xy by simp
    also have "\<dots> = \<gamma> (?f (?e (x \<squnion> y))) * \<delta> (?f (?e (x \<sqinter> y)))" by (simp add: the_inv_f_f[OF inj_e])
    also have "\<dots> = \<gamma> (?f (A \<union> B)) * \<delta> (?f (A \<inter> B))" unfolding p0 p2 by auto
    also have "\<dots> = \<gamma>' (A \<union> B) * \<delta>' (A \<inter> B)"  using p1 p3 unfolding prime_def conv_def by auto
    finally show ?thesis by simp
  next
    case False
    hence "\<alpha>' A * \<beta>' B = 0" unfolding prime_def conv_def by simp
    also have "\<dots> \<le> \<gamma>' (A \<union> B) * \<delta>' (A \<inter> B)" unfolding prime_def
      using 1 that assms(3,4) by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  define M' where "M' = (\<lambda>x. \<lbrace> x \<rbrace>) ` M"
  define N' where "N' = (\<lambda>x. \<lbrace> x \<rbrace>) ` N"

  have ran1: "M' \<subseteq> \<O>\<J>" "N' \<subseteq> \<O>\<J>" unfolding M'_def N'_def using ran_e by auto
  hence ran2: "M' \<subseteq> Pow \<J>" "N' \<subseteq> Pow \<J>" unfolding down_irreducibles_def by auto

  have "?f \<in> ?e ` S \<rightarrow> S" for S using inj_e by (simp add: Pi_iff the_inv_f_f)
  hence bij_betw: "bij_betw ?f (?e ` S) S" for S :: "'a set"
    by (intro bij_betwI[where g="?e"] the_inv_f_f f_the_inv_into_f inj_e) auto

  have a: "{C. \<exists>A\<in>M'. \<exists>B\<in>N'. C = A \<union> B} = ?e ` {c. \<exists>x\<in>M. \<exists>y\<in>N. c=x\<squnion>y}"
    unfolding M'_def N'_def Set.bex_simps join_irreducibles_join_homomorphism[symmetric] by auto
  have b: "{D. \<exists>A\<in>M'. \<exists>B\<in>N'. D = A \<inter> B} = ?e ` {c. \<exists>x\<in>M. \<exists>y\<in>N. c=x\<sqinter>y}"
    unfolding M'_def N'_def Set.bex_simps join_irreducibles_meet_homomorphism[symmetric] by auto

  have M'_N'_un_ran: "{C. \<exists>A\<in>M'. \<exists>B\<in>N'. C = A \<union> B} \<subseteq> \<O>\<J>"
    unfolding a using ran_e by auto
  have M'_N'_int_ran: "{C. \<exists>A\<in>M'. \<exists>B\<in>N'. C = A \<inter> B} \<subseteq> \<O>\<J>"
    unfolding b using ran_e by auto

  have "?L =(\<Sum>A\<in>M'. \<alpha> (?f A)) * (\<Sum>A\<in>N'. \<beta> (?f A))"
    unfolding M'_def N'_def
    by (intro arg_cong2[where f="(*)"] sum.reindex_bij_betw[symmetric] bij_betw)
  also have "\<dots> = (\<Sum>A\<in>M'. \<alpha>' A)*(\<Sum>A\<in>N'. \<beta>' A)"
    unfolding prime_def conv_def using ran1 by (intro arg_cong2[where f="(*)"] sum.cong refl) auto
  also have "\<dots> \<le> (\<Sum>C | \<exists>A\<in>M'. \<exists>B\<in>N'. C = A \<union> B. \<gamma>' C) * (\<Sum>D | \<exists>A\<in>M'. \<exists>B\<in>N'. D = A \<inter> B. \<delta>' D)"
    using ran2 by (intro four_functions[where I="\<J>"] 0) (auto intro!:1 assms simp:prime_def)
  also have "\<dots> = (\<Sum>C|\<exists>A\<in>M'. \<exists>B\<in>N'. C=A\<union>B. \<gamma>(?f C))*(\<Sum>D|\<exists>A\<in>M'.\<exists>B\<in>N'. D=A\<inter>B. \<delta>(?f D))"
    using M'_N'_un_ran M'_N'_int_ran unfolding prime_def conv_def
    by (intro arg_cong2[where f="(*)"] sum.cong refl) auto
  also have "\<dots> = ?R"
    unfolding a b by (intro arg_cong2[where f="(*)"] sum.reindex_bij_betw bij_betw)
  finally show ?thesis by simp
qed

theorem fkg_inequality:
  fixes \<mu> :: "'a :: finite_distrib_lattice \<Rightarrow> real"
  assumes "range \<mu> \<subseteq> {0..}" "range f \<subseteq> {0..}" "range g \<subseteq> {0..}"
  assumes "\<And>x y. \<mu> x * \<mu> y \<le> \<mu> (x \<squnion> y) * \<mu> (x \<sqinter> y)"
  assumes "mono f" "mono g"
  shows "(\<Sum>x\<in>UNIV. \<mu> x*f x) * (\<Sum>x\<in>UNIV. \<mu> x*g x) \<le> (\<Sum>x\<in>UNIV. \<mu> x*f x*g x) * sum \<mu> UNIV"
    (is "?L \<le> ?R")
proof -
  define \<alpha> where "\<alpha> x = \<mu> x * f x" for x
  define \<beta> where "\<beta> x = \<mu> x * g x" for x
  define \<gamma> where "\<gamma> x = \<mu> x * f x * g x" for x
  define \<delta> where "\<delta> x = \<mu> x" for x

  have 0:"f x \<ge> 0" if "range f \<subseteq> {0..}" for f :: "'a \<Rightarrow> real" and x
    using that by auto

  note \<mu>fg_nonneg = 0[OF assms(1)] 0[OF assms(2)] 0[OF assms(3)]

  have 1:"\<alpha> x * \<beta> y \<le> \<gamma> (x \<squnion> y) * \<delta> (x \<sqinter> y)" (is "?L1 \<le> ?R1") for x y
  proof -
    have "?L1 = (\<mu> x * \<mu> y) * (f x * g y)" unfolding \<alpha>_def \<beta>_def by (simp add:ac_simps)
    also have "\<dots> \<le> (\<mu> (x \<squnion> y) * \<mu> (x \<sqinter> y)) * (f x * g y)"
      using assms(2,3) by (intro mult_right_mono assms(4) mult_nonneg_nonneg) auto
    also have "\<dots> \<le> (\<mu> (x \<squnion> y) * \<mu> (x \<sqinter> y)) * (f (x \<squnion> y) * g (x \<squnion> y))"
      using \<mu>fg_nonneg
      by (intro mult_left_mono mult_mono monoD[OF assms(5)] monoD[OF assms(6)] mult_nonneg_nonneg)
       simp_all
    also have "\<dots> = ?R1" unfolding \<gamma>_def \<delta>_def by simp
    finally show ?thesis by simp
  qed

  have "?L = (\<Sum>x\<in>UNIV. \<alpha> x) * (\<Sum>y\<in>UNIV. \<beta> y)" unfolding \<alpha>_def \<beta>_def by simp
  also have "\<dots> \<le> (\<Sum>c| \<exists>x\<in>UNIV. \<exists>y\<in>UNIV. c=x\<squnion>y. \<gamma> c)*(\<Sum>d| \<exists>x\<in>UNIV. \<exists>y\<in>UNIV. d=x\<sqinter>y. \<delta> d)"
    using \<mu>fg_nonneg by (intro four_functions_in_lattice 1) (auto simp:\<alpha>_def \<beta>_def \<gamma>_def \<delta>_def)
  also have "\<dots> = (\<Sum>x\<in>UNIV. \<gamma> x) * (\<Sum>x\<in>UNIV. \<delta> x)"
    using sup.idem[where 'a='a] inf.idem[where 'a='a]
    by (intro arg_cong2[where f="(*)"] sum.cong refl UNIV_eq_I[symmetric] CollectI) (metis UNIV_I)+
  also have "\<dots> = ?R" unfolding \<gamma>_def \<delta>_def by simp
  finally show ?thesis by simp
qed

theorem fkg_inequality_gen:
  fixes \<mu> :: "'a :: finite_distrib_lattice \<Rightarrow> real"
  assumes "range \<mu> \<subseteq> {0..}"
  assumes "\<And>x y. \<mu> x * \<mu> y \<le> \<mu> (x \<squnion> y) * \<mu> (x \<sqinter> y)"
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<tau>\<^esub>) f" "monotone (\<le>) (\<le>\<ge>\<^bsub>\<sigma>\<^esub>) g"
  shows "(\<Sum>x\<in>UNIV. \<mu> x*f x) * (\<Sum>x\<in>UNIV. \<mu> x*g x) \<le>\<ge>\<^bsub>\<tau>*\<sigma>\<^esub> (\<Sum>x\<in>UNIV. \<mu> x*f x*g x) * sum \<mu> UNIV"
    (is "?L \<le>\<ge>\<^bsub>?x\<^esub> ?R")
proof -
  define a where "a = max (MAX x. -f x*(\<plusminus>\<^bsub>\<tau>\<^esub>)) (MAX x. -g x*(\<plusminus>\<^bsub>\<sigma>\<^esub>))"

  define f' where "f' x = a + f x*(\<plusminus>\<^bsub>\<tau>\<^esub>)" for x
  define g' where "g' x = a + g x*(\<plusminus>\<^bsub>\<sigma>\<^esub>)" for x

  have f'_mono: "mono f'" unfolding f'_def using monotoneD[OF assms(3)]
    by (intro monoI add_mono order.refl)  (cases \<tau>, auto simp:comp_def ac_simps)

  have g'_mono: "mono g'" unfolding g'_def using monotoneD[OF assms(4)]
    by (intro monoI add_mono order.refl) (cases \<sigma>, auto simp:comp_def ac_simps)

  have f'_nonneg: "f' x \<ge> 0" for x
    unfolding f'_def a_def max_add_distrib_left
    by (intro max.coboundedI1) (auto intro!:Max.coboundedI simp: algebra_simps real_0_le_add_iff)

  have g'_nonneg: "g' x \<ge> 0" for x
    unfolding g'_def a_def max_add_distrib_left
    by (intro max.coboundedI2) (auto intro!:Max.coboundedI simp: algebra_simps real_0_le_add_iff)

  let ?M = "(\<Sum>x \<in> UNIV. \<mu> x)"
  let ?sum = "(\<lambda>f. (\<Sum>x\<in>UNIV. \<mu> x * f x))"

  have "(\<plusminus>\<^bsub>\<tau>*\<sigma>\<^esub>) * ?L = ?sum (\<lambda>x. f x*(\<plusminus>\<^bsub>\<tau>\<^esub>)) * ?sum (\<lambda>x. g x*(\<plusminus>\<^bsub>\<sigma>\<^esub>))"
    by (simp add:ac_simps sum_distrib_left[symmetric] dir_mult_hom del:rel_dir_mult)
  also have "\<dots> = (?sum (\<lambda>x. (f x*(\<plusminus>\<^bsub>\<tau>\<^esub>)+a))-?M*a) * (?sum (\<lambda>x. (g x*(\<plusminus>\<^bsub>\<sigma>\<^esub>)+a))-?M*a)"
    by (simp add:algebra_simps sum.distrib sum_distrib_left)
  also have "\<dots> = (?sum f')*(?sum g') - ?M*a*?sum f'- ?M*a*?sum g' + ?M*?M*a*a"
    unfolding f'_def g'_def by (simp add:algebra_simps)
  also have "\<dots> \<le> ((\<Sum>x\<in>UNIV. \<mu> x*f' x*g' x)*?M) - ?M*a*?sum f'- ?M*a*?sum g' + ?M*?M*a*a"
    using f'_nonneg g'_nonneg
    by (intro diff_mono add_mono order.refl fkg_inequality assms(1,2) f'_mono g'_mono) auto
  also have "\<dots> = ?sum (\<lambda>x. (f x*(\<plusminus>\<^bsub>\<tau>\<^esub>))*(g x*(\<plusminus>\<^bsub>\<sigma>\<^esub>)))*?M"
    unfolding f'_def g'_def by (simp add:algebra_simps sum.distrib sum_distrib_left[symmetric])
  also have "\<dots> = (\<plusminus>\<^bsub>\<tau>*\<sigma>\<^esub>) * ?R"
    by (simp add:ac_simps sum.distrib sum_distrib_left[symmetric] dir_mult_hom del:rel_dir_mult)
  finally have " (\<plusminus>\<^bsub>\<tau>*\<sigma>\<^esub>) * ?L \<le> (\<plusminus>\<^bsub>\<tau>*\<sigma>\<^esub>) * ?R" by simp
  thus ?thesis by (cases "\<tau>*\<sigma>", auto)
qed

theorem fkg_inequality_pmf:
  fixes M :: "('a :: finite_distrib_lattice) pmf"
  fixes f g :: "'a \<Rightarrow> real"
  assumes "\<And>x y. pmf M x * pmf M y \<le> pmf M (x \<squnion> y) * pmf M (x \<sqinter> y)"
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<tau>\<^esub>) f" "monotone (\<le>) (\<le>\<ge>\<^bsub>\<sigma>\<^esub>) g"
  shows "(\<integral>x. f x \<partial>M) * (\<integral>x. g x \<partial>M) \<le>\<ge>\<^bsub>\<tau> * \<sigma>\<^esub> (\<integral>x. f x * g x \<partial>M)"
    (is "?L \<le>\<ge>\<^bsub>_\<^esub> ?R")
proof -
  have 0:"?L = (\<Sum>a\<in>UNIV. pmf M a * f a) * (\<Sum>a\<in>UNIV. pmf M a * g a)"
    by (subst (1 2) integral_measure_pmf_real[where A="UNIV"]) (auto simp:ac_simps)
  have "?R = ?R * (\<integral>x. 1 \<partial>M)" by simp
  also have "\<dots> = (\<Sum>a\<in>UNIV. pmf M a*f a*g a) * sum (pmf M) UNIV"
    by (subst (1 2) integral_measure_pmf_real[where A="UNIV"])  (auto simp:ac_simps)
  finally have 1: "?R = (\<Sum>a\<in>UNIV. pmf M a*f a*g a) * sum (pmf M) UNIV" by simp
  thus ?thesis unfolding 0 1
    by (intro fkg_inequality_gen assms) auto
qed

end