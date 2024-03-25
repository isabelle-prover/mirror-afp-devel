(*
  File:     Chebyshev_Polynomials/Chebyshev_Polynomials_Library.thy
  Author:   Manuel Eberl (University of Innsbruck)

  Various library to be moved to the distribution
*)
section \<open>Missing Library Material\<close>
theory Chebyshev_Polynomials_Library
  imports "HOL-Computational_Algebra.Polynomial" "HOL-Library.FuncSet"
begin

text \<open>
  The following two lemmas give a full characterisation of the \<^const>\<open>filter\<close> function:
  The list \<^term>\<open>filter P xs\<close> is the only list \<open>ys\<close> for which there exists a strictly increasing
  function $f : \{0,\ldots,|\text{ys}|-1\} \to \{0,\ldots,|\text{xs}|-1\}$ such that:

    \<^item> $\text{ys}_i = \text{xs}_{f(i)}$

    \<^item> $P(\text{xs}_i) \longleftrightarrow \exists j{<}n.\ f(j) = i$, i.e.\ the range of $f$
      are precisely the indices of the elements of \<open>xs\<close> that satisfy \<open>P\<close>.

\<close>
lemma filterE:
  fixes P :: "'a \<Rightarrow> bool" and xs :: "'a list"
  assumes "length (filter P xs) = n"
  obtains f :: "nat \<Rightarrow> nat" where
    "strict_mono_on {..<n} f"
    "\<And>i. i < n \<Longrightarrow> f i < length xs"
    "\<And>i. i < n \<Longrightarrow> filter P xs ! i = xs ! f i"
    "\<And>i. i < length xs \<Longrightarrow> P (xs ! i) \<longleftrightarrow> (\<exists>j. j < n \<and> f j = i)"
  using assms(1)
proof (induction xs arbitrary: n thesis)
  case Nil
  thus ?case
    using that[of "\<lambda>_. 0"] by auto
next
  case (Cons x xs)
  define n' where "n' = (if P x then n - 1 else n)"
  obtain f :: "nat \<Rightarrow> nat" where f:
    "strict_mono_on {..<n'} f"
    "\<And>i. i < n'\<Longrightarrow> f i < length xs"
    "\<And>i. i < n' \<Longrightarrow> filter P xs ! i = xs ! f i"
    "\<And>i. i < length xs \<Longrightarrow> P (xs ! i) \<longleftrightarrow> (\<exists>j. j < n' \<and> f j = i)"
  proof (rule Cons.IH[where n = n'])
    show "length (filter P xs) = n'"
      using Cons.prems(2) by (auto simp: n'_def)
  qed auto
  define f' where "f' = (\<lambda>i. if P x then case i of 0 \<Rightarrow> 0 | Suc j \<Rightarrow> Suc (f j) else Suc (f i))"

  show ?case
  proof (rule Cons.prems(1))
    show "strict_mono_on {..<n} f'"
      by (auto simp: f'_def strict_mono_on_def n'_def strict_mono_onD[OF f(1)] split: nat.splits)
    show "f' i < length (x # xs)" if "i < n" for i
      using that f(2) by (auto simp: f'_def n'_def split: nat.splits)
    show "filter P (x # xs) ! i = (x # xs) ! f' i" if "i < n" for i
      using that f(3) by (auto simp: f'_def n'_def split: nat.splits)
    show "P ((x # xs) ! i) \<longleftrightarrow> (\<exists>j<n. f' j = i)" if "i < length (x # xs)" for i
    proof (cases i)
      case [simp]: 0
      show ?thesis using that Cons.prems(2)
        by (auto simp: f'_def intro!: exI[of _ 0])
    next
      case [simp]: (Suc i')
      have "P ((x # xs) ! i) \<longleftrightarrow> P (xs ! i')"
        by simp
      also have "\<dots> \<longleftrightarrow> (\<exists>j<n'. f j = i')"
        using that by (subst f(4)) simp_all
      also have "\<dots> \<longleftrightarrow> {j\<in>{..<n'}. f j = i'} \<noteq> {}"
        by blast
      also have "bij_betw (\<lambda>j. if P x then j+1 else j) {j\<in>{..<n'}. f j = i'} {j\<in>{..<n}. f' j = i}"
      proof (intro bij_betwI[of _ _ _ "\<lambda>j. if P x then j-1 else j"], goal_cases)
        case 2
        have "(if P x then j - 1 else j) < n'"
          if "j < n" "f' j = i" for j 
          using that by (auto simp: n'_def f'_def split: nat.splits)
        moreover have "f (if P x then j - 1 else j) = i'" if "j < n" "f' j = i" for j
          using that by (auto simp: n'_def f'_def split: nat.splits if_splits)
        ultimately show ?case by auto
      qed (auto simp: n'_def f'_def split: nat.splits)
      hence "{j\<in>{..<n'}. f j = i'} \<noteq> {} \<longleftrightarrow> {j\<in>{..<n}. f' j = i} \<noteq> {}"
        unfolding bij_betw_def by blast
      also have "\<dots> \<longleftrightarrow> (\<exists>j<n. f' j = i)"
        by auto
      finally show ?thesis .
    qed
  qed
qed

text \<open>
  The following lemma shows the uniqueness of the above property.
  It is very useful for finding a ``closed form'' for \<^term>\<open>filter P xs\<close> in some concrete
  situation. 
  
  For example, if we know that exactly every other element of \<open>xs\<close> satisfies \<open>P\<close>, 
  we can use it to prove that
  \<^prop>\<open>filter P xs = map (\<lambda>i. 2 * i) [0..<length xs div 2]\<close>
\<close>
lemma filter_eqI:
  fixes f :: "nat \<Rightarrow> nat" and xs ys :: "'a list"
  defines "n \<equiv> length ys"
  assumes "strict_mono_on {..<n} f"
  assumes "\<And>i. i < n \<Longrightarrow> f i < length xs"
  assumes "\<And>i. i < n \<Longrightarrow> ys ! i = xs ! f i"
  assumes "\<And>i. i < length xs \<Longrightarrow> P (xs ! i) \<longleftrightarrow> (\<exists>j. j < n \<and> f j = i)"
  shows   "filter P xs = ys"
  using assms(2-) unfolding n_def
proof (induction xs arbitrary: ys f)
  case Nil
  thus ?case by auto
next
  case (Cons x xs ys f)
  show ?case
  proof (cases "P x")
    case False
    have "filter P xs = ys"
    proof (rule Cons.IH)
      have pos: "f i > 0" if "i < length ys" for i
        using Cons.prems(4)[of "f i"] Cons.prems(2,3)[of i] that False
        by (auto intro!: Nat.gr0I)
      show "strict_mono_on {..<length ys} ((\<lambda>x. x - 1) \<circ> f)"
      proof (intro strict_mono_onI)
        fix i j assume ij: "i \<in> {..<length ys}" "j \<in> {..<length ys}" "i < j"
        thus "((\<lambda>x. x - 1) \<circ> f) i < ((\<lambda>x. x - 1) \<circ> f) j"
          using Cons.prems(1) pos[of i] pos[of j] 
          by (auto simp: strict_mono_on_def diff_less_mono)
      qed
      show "((\<lambda>x. x - 1) \<circ> f) i < length xs" if "i < length ys" for i
        using Cons.prems(2)[of i] pos[of i] that by auto
      show "ys ! i = xs ! ((\<lambda>x. x - 1) \<circ> f) i" if "i < length ys" for i
        using Cons.prems(3)[of i] pos[of i] that by auto
      show "P (xs ! i) \<longleftrightarrow> (\<exists>j<length ys. ((\<lambda>x. x - 1) \<circ> f) j = i)" if "i < length xs" for i
        using Cons.prems(4)[of "Suc i"] that pos by (auto split: if_splits)
    qed
    thus ?thesis
      using False by simp
  next
    case True
    have "ys \<noteq> []"
      using Cons.prems(4)[of 0] True by auto
    have [simp]: "f 0 = 0"
    proof -
      obtain j where "j < length ys" "f j = 0"
        using Cons.prems(4)[of 0] True by auto
      with strict_mono_onD[OF Cons.prems(1)] have "j = 0"
        by (metis gr_implies_not_zero lessThan_iff less_antisym zero_less_Suc)
      with \<open>f j = 0\<close> show ?thesis
        by simp
    qed
    have pos: "f j > 0" if "j > 0" "j < length ys" for j
      using strict_mono_onD[OF Cons.prems(1), of 0 j] that \<open>ys \<noteq> []\<close> by auto
    have f_eq_Suc_imp_pos: "j > 0" if "f j = Suc k" for j k
      by (rule Nat.gr0I) (use that in auto)

    define f' where "f' = (\<lambda>n. f (Suc n) - 1)"
    have "filter P xs = tl ys"
    proof (rule Cons.IH)
      show "strict_mono_on {..<length (tl ys)} f'"
      proof (intro strict_mono_onI)
        fix i j assume ij: "i \<in> {..<length (tl ys)}" "j \<in> {..<length (tl ys)}" "i < j"
        from ij have "Suc i < length ys" "Suc j < length ys"
          by auto
        thus "f' i < f' j"
          using strict_mono_onD[OF Cons.prems(1), of "Suc i" "Suc j"]
                pos[of "Suc i"] pos[of "Suc j"] \<open>ys \<noteq> []\<close> \<open>i < j\<close>
          by (auto simp: strict_mono_on_def diff_less_mono f'_def)
      qed
      show "f' i < length xs" and "tl ys ! i = xs ! f' i" if "i < length (tl ys)" for i
      proof -
        have "Suc i < length ys"
          using that by auto
        thus "f' i < length xs"
          using Cons.prems(2)[of "Suc i"] pos[of "Suc i"] that by (auto simp: f'_def)
        show "tl ys ! i = xs ! f' i"
          using \<open>Suc i < length ys\<close> that Cons.prems(3)[of "Suc i"] pos[of "Suc i"]
          by (auto simp: nth_tl nth_Cons f'_def split: nat.splits)
      qed
      show "P (xs ! i) \<longleftrightarrow> (\<exists>j<length (tl ys). f' j = i)" if "i < length xs" for i
      proof -
        have "P (xs ! i) \<longleftrightarrow> P ((x # xs) ! Suc i)"
          by simp
        also have "\<dots> \<longleftrightarrow> {j \<in> {..<length ys}. f j = Suc i} \<noteq> {}"
          using that by (subst Cons.prems(4)) auto
        also have "bij_betw (\<lambda>x. x - 1) {j \<in> {..<length ys}. f j = Suc i}
                     {j \<in> {..<length (tl ys)}. f' j = i}"
          by (rule bij_betwI[of _ _ _ Suc])
             (auto simp: f'_def Suc_diff_Suc f_eq_Suc_imp_pos diff_less_mono Suc_leI pos)
        hence "{j \<in> {..<length ys}. f j = Suc i} \<noteq> {} \<longleftrightarrow> {j \<in> {..<length (tl ys)}. f' j = i} \<noteq> {}"
          unfolding bij_betw_def by blast
        also have "\<dots> \<longleftrightarrow> (\<exists>j<length (tl ys). f' j = i)"
          by blast
        finally show ?thesis .
      qed
    qed
    moreover have "hd ys = x"
      using True \<open>f 0 = 0\<close> \<open>ys \<noteq> []\<close> Cons.prems(3)[of 0] by (auto simp: hd_conv_nth)
    ultimately show ?thesis
      using \<open>ys \<noteq> []\<close> True by force
  qed
qed

lemma filter_eq_iff:
  "filter P xs = ys \<longleftrightarrow>
     (\<exists>f. strict_mono_on {..<length ys} f \<and> 
          (\<forall>i<length ys. f i < length xs \<and> ys ! i = xs ! f i) \<and> 
          (\<forall>i<length xs. P (xs ! i) \<longleftrightarrow> (\<exists>j. j < length ys \<and> f j = i)))"
  (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs
    unfolding that [symmetric] by (rule filterE[OF refl, of P xs]) blast
  show ?lhs if ?rhs
    using that filter_eqI[of ys _ xs P] by blast
qed
(* END TODO *)

end