section \<open>Infinite Sums of Positive Reals\<close>


text \<open>This is a theory of infinite sums of positive reals defined as limits of finite sums. 
The goal is to make reasoning about these infinite sums almost as easy as that about finite sums. 
\<close>


theory Infinite_Sums_of_Positive_Reals
imports Complex_Main "HOL-Library.Countable_Set" 
begin


subsection \<open>Preliminaries\<close>

lemma real_pm_iff: 
  "\<And>a b c. (a::real) + b \<le> c \<longleftrightarrow> a \<le> c - b"
  "\<And>a b c. (a::real) + b \<le> c \<longleftrightarrow> b \<le> c - a"
  "\<And>a b c. (a::real) \<le> b - c \<longleftrightarrow> c \<le> b - a"
  by auto

lemma real_md_iff: 
  "\<And>a b c. a \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow> (a::real) * b \<le> c \<longleftrightarrow> a \<le> c / b"
  "\<And>a b c. a > 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow> (a::real) * b \<le> c \<longleftrightarrow> b \<le> c / a"
  "\<And>a b c. a > 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> c > 0 \<Longrightarrow> (a::real) \<le> b / c \<longleftrightarrow> c \<le> b / a"
  by (auto simp: field_simps)

lemma disjoint_finite_aux: 
  "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {} \<Longrightarrow> B \<subseteq> \<Union> (A ` I) \<Longrightarrow> finite B \<Longrightarrow> finite {i \<in> I. B \<inter> A i \<noteq> {}}"
  apply(rule inj_on_finite[of "\<lambda>i. SOME b. b \<in> B \<inter> A i" _ B])
  subgoal unfolding inj_on_def by auto (metis (no_types, lifting) IntI empty_iff someI)
  subgoal by auto (metis (no_types, lifting) someI)
  subgoal by auto .

lemma incl_UNION_aux: "B \<subseteq> \<Union> (A ` I) \<Longrightarrow> B = \<Union> ((\<lambda>i. (B \<inter> A i)) ` {i \<in> I. B \<inter> A i \<noteq> {}})"
  by fastforce

lemma incl_UNION_aux2: "B \<subseteq> \<Union> (A ` I) \<longleftrightarrow> B = \<Union> ((\<lambda>i. (B \<inter> A i)) ` I)"
  by fastforce

(*  *)
lemma sum_singl[simp]: "sum f {a} = f a"  
  by simp

lemma sum_two[simp]: "a1 \<noteq> a2 \<Longrightarrow> sum f {a1,a2} = f a1 + f a2"  
  by simp

lemma sum_three[simp]: "a1 \<noteq> a2 \<Longrightarrow> a1 \<noteq> a3 \<Longrightarrow> a2 \<noteq> a3 \<Longrightarrow> 
 sum f {a1,a2,a3} = f a1 + f a2 + f a3"  
  by (simp add: add.assoc)

(*  *)

lemma Sup_leq: 
  "A \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (a::real) \<le> b \<Longrightarrow> bdd_above B \<Longrightarrow> Sup A \<le> Sup B"
  by (simp add: cSup_mono)

lemma Sup_image_leq: 
  "A \<noteq> {} \<Longrightarrow>  \<forall>a\<in>A. \<exists>b\<in>B. (f a::real) \<le> g b \<Longrightarrow> bdd_above (g ` B) \<Longrightarrow> 
 Sup (f ` A) \<le> Sup (g ` B)"
  by (rule Sup_leq) auto

lemma Sup_cong: 
  assumes "A \<noteq> {} \<or> B \<noteq> {}" "\<forall>a\<in>A. \<exists>b\<in>B. (a::real) \<le> b" "\<forall>b\<in>B. \<exists>a\<in>A. (b::real) \<le> a"
    "bdd_above A \<or> bdd_above B"
  shows "Sup A = Sup B" 
proof-
  have "A \<noteq> {} \<and> B \<noteq> {}" "bdd_above A \<and> bdd_above B"
    using assms unfolding bdd_above_def using order.trans by blast+
  thus ?thesis using assms by (smt Sup_leq)
qed

lemma Sup_image_cong: 
  "A \<noteq> {} \<or> B \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (f a::real) \<le> g b \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. (g b::real) \<le> f a \<Longrightarrow> 
 bdd_above (f ` A) \<or> bdd_above (g ` B) \<Longrightarrow> 
 Sup (f ` A) = Sup (g ` B)"
  by (rule Sup_cong) auto

lemma Sup_congL: 
  "A \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (a::real) \<le> b \<Longrightarrow> \<forall>b\<in>B. b \<le> Sup A \<Longrightarrow> Sup A = Sup B"
  by (metis Collect_empty_eq Collect_mem_eq Sup_leq bdd_aboveI cSup_least dual_order.antisym)

lemma Sup_image_congL: 
  "A \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. \<exists>b\<in>B. (f a::real) \<le> g b \<Longrightarrow> \<forall>b\<in>B. g b \<le> Sup (f ` A) \<Longrightarrow> Sup (f ` A) = Sup (g ` B)"
  by (rule Sup_congL) auto

lemma Sup_congR: 
  "B \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. a \<le> Sup B \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. (b::real) \<le> a \<Longrightarrow> Sup A = Sup B"
  by (metis Collect_empty_eq Collect_mem_eq Sup_leq bdd_aboveI cSup_least dual_order.antisym)

lemma Sup_image_congR: 
  "B \<noteq> {} \<Longrightarrow> \<forall>a\<in>A. f a \<le> Sup (g ` B) \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. (g b::real) \<le> f a \<Longrightarrow> Sup (f ` A) = Sup (g ` B)"
  by (rule Sup_congR) auto

(* *) 

lemma Sup_eq_0_iff: 
  assumes "A \<noteq> {}" "bdd_above A" "(\<forall>a\<in>A. (a::real) \<ge> 0)" 
  shows "Sup A = 0 \<longleftrightarrow> (\<forall>a\<in>A. a = 0)" 
  using assms by (metis all_not_in_conv cSup_eq_maximum cSup_upper leD less_eq_real_def)

lemma plus_Sup_commute:
  assumes f1: "{f1 b1 | b1. \<phi>1 b1} \<noteq> {}" "bdd_above {f1 b1 | b1. \<phi>1 b1}" and 
          f2: "{f2 b2 | b2. \<phi>2 b2} \<noteq> {}" "bdd_above {f2 b2 | b2. \<phi>2 b2}"
  shows 
    "Sup {(f1 b1::real) | b1 . \<phi>1 b1} + Sup {f2 b2 | b2 . \<phi>2 b2} = 
     Sup {f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}" (is "?L1 + ?L2 = ?R")
proof-
  have f: 
    "{f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2} \<noteq> {}"
    "bdd_above {f1 b1 + f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}"  
    subgoal using f1 f2 by auto
    subgoal using f1(2) f2(2) unfolding bdd_above_def apply safe 
      subgoal for M1 M2
        apply(rule exI[of _ "M1 + M2"]) using add_mono by blast . .
  show ?thesis proof(rule order.antisym)
    show "?L1 + ?L2 \<le> ?R" unfolding real_pm_iff(1) cSup_le_iff[OF f1] apply safe
      apply(subst real_pm_iff(3)) unfolding cSup_le_iff[OF f2] apply safe
      unfolding real_pm_iff(2)[symmetric] apply(rule cSup_upper[OF _ f(2)]) by auto
  next
    show "?R \<le> ?L1 + ?L2" unfolding cSup_le_iff[OF f] apply safe 
      subgoal for _ b1 b2
        using cSup_upper[OF _ f1(2), of "f1 b1"] cSup_upper[OF _ f2(2), of "f2 b2"] 
        by fastforce .
  qed
qed

lemma plus_Sup_commute':
  assumes f1: "A1 \<noteq> {}" "bdd_above A1" and 
    f2: "A2 \<noteq> {}" "bdd_above A2"
  shows "Sup A1 + Sup A2 = Sup {(a1::real) + a2 | a1 a2. a1 \<in> A1 \<and> a2 \<in> A2}"  
  using plus_Sup_commute[of id "\<lambda>a1. a1 \<in> A1" id "\<lambda>a2. a2 \<in> A2"] assms 
  by auto

lemma plus_SupR: "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> Sup A + (b::real) = Sup {a + b | a. a \<in> A}"
  apply(subst cSup_singleton[of b, symmetric])
  apply(subst plus_Sup_commute') by auto

lemma plus_SupL: "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> (b::real) + Sup A = Sup {b + a | a. a \<in> A}"
  apply(subst cSup_singleton[of b, symmetric])
  apply(subst plus_Sup_commute') by auto 

(* *)

lemma mult_Sup_commute:
  assumes f1: "{f1 b1 | b1. \<phi>1 b1} \<noteq> {}" "bdd_above {f1 b1 | b1. \<phi>1 b1}" "\<forall>b1. \<phi>1 b1 \<longrightarrow> f1 b1 \<ge> 0" and 
    f2: "{f2 b2 | b2. \<phi>2 b2} \<noteq> {}" "bdd_above {f2 b2 | b2. \<phi>2 b2}" "\<forall>b2. \<phi>2 b2 \<longrightarrow> f2 b2 \<ge> 0"
  shows 
    "Sup {(f1 b1::real) | b1 . \<phi>1 b1} * Sup {f2 b2 | b2 . \<phi>2 b2} = 
 Sup {f1 b1 * f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}" (is "?L1 * ?L2 = ?R")
proof-
  have f: 
    "{f1 b1 * f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2} \<noteq> {}"
    "bdd_above {f1 b1 * f2 b2 | b1 b2. \<phi>1 b1 \<and> \<phi>2 b2}" 
    "\<forall>b1 b2. \<phi>1 b1 \<and> \<phi>2 b2 \<longrightarrow> f1 b1 * f2 b2 \<ge> 0"
    subgoal using f1 f2 by auto
    subgoal using f1(2) f2(2) unfolding bdd_above_def apply safe 
      subgoal for M1 M2
        apply(rule exI[of _ "M1 * M2"]) using mult_mono f1(3) f2(3) by fastforce . 
    subgoal using f1(3) f2(3) by auto .
  show ?thesis
  proof(rule order.antisym)
    show "?L1 * ?L2 \<le> ?R" 
    proof(cases "?L1 = 0 \<or> ?L2 = 0")
      case True thus ?thesis using f 
        by (smt Collect_empty_eq cSup_upper mem_Collect_eq mult_not_zero) 
    next
      case False 
      have gez: "?L1 > 0" "?L2 > 0" "?R \<ge> 0"  
          apply (smt Collect_empty_eq False cSup_upper f1 mem_Collect_eq)
         apply (smt Collect_empty_eq False cSup_upper f2 mem_Collect_eq)
        by (smt Collect_empty_eq cSup_upper f(1) f(2) f(3) mem_Collect_eq)
      hence ggez: "?L1 \<ge> 0" "?L2 \<ge> 0" by linarith+
      show ?thesis 
        unfolding real_md_iff(1)[OF ggez(1) gez(2) gez(3)] 
        unfolding cSup_le_iff[OF f1(1,2)] apply safe
        subgoal for _ b1
          apply(cases "f1 b1 = 0")
          subgoal using divide_nonneg_pos gez(2) gez(3) by auto
          subgoal apply(subst real_md_iff(3)) 
            subgoal using f1(3) by auto
            subgoal using gez(3) by blast
            subgoal using gez(2) by blast
            subgoal unfolding cSup_le_iff[OF f2(1,2)] apply safe
              apply(subst real_md_iff(2)[symmetric]) 
              using f1(3) f2(3) gez(3) by (auto intro: cSup_upper[OF _ f(2)]) . . . 
    qed
  next
    show "?R \<le> ?L1 * ?L2" unfolding cSup_le_iff[OF f(1,2)] apply safe subgoal for _ b1 b2
        using cSup_upper[OF _ f1(2), of "f1 b1"] cSup_upper[OF _ f2(2), of "f2 b2"] 
        by (metis (mono_tags, lifting) f1(3) f2(3) mem_Collect_eq mult_mono') .
  qed
qed

lemma mult_Sup_commute':
  assumes "A1 \<noteq> {}" "bdd_above A1" "\<forall>a1\<in>A1. a1 \<ge> 0" and 
    "A2 \<noteq> {}" "bdd_above A2" "\<forall>a2\<in>A2. a2 \<ge> 0"
  shows "Sup A1 * Sup A2 = Sup {(a1::real) * a2 | a1 a2. a1 \<in> A1 \<and> a2 \<in> A2}"  
  using mult_Sup_commute[of id "\<lambda>a1. a1 \<in> A1" id "\<lambda>a2. a2 \<in> A2"] assms 
  by auto

lemma mult_SupR: "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> \<forall>a\<in>A. a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> 
  Sup A * (b::real) = Sup {a * b | a. a \<in> A}"
  apply(subst cSup_singleton[of b, symmetric])
  apply(subst mult_Sup_commute') by auto

lemma mult_SupL: "A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> \<forall>a\<in>A. a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> 
  (b::real) * Sup A = Sup {b * a | a. a \<in> A}"
  apply(subst cSup_singleton[of b, symmetric])
  apply(subst mult_Sup_commute') by auto 

(* *)

lemma sum_mono3: 
  "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>b. b \<in> B - A \<Longrightarrow> 0 \<le> g b) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (f a::real) \<le> g a) \<Longrightarrow> 
 sum f A \<le> sum g B"
  by (smt (verit, best) sum_mono sum_mono2)

lemma sum_Sup_commute: 
  fixes h :: "'a \<Rightarrow> real"
  assumes "finite J" and "\<forall>i\<in>J. {h b | b. \<phi> i b} \<noteq> {} \<and> bdd_above {h b | b. \<phi> i b}"
  shows "sum (\<lambda>i. Sup {h b | b. \<phi> i b}) J = 
       Sup {sum (\<lambda>i. h (b i)) J | b . \<forall>i\<in>J. \<phi> i (b i)}"
  using assms proof(induction J)
  case (insert j J)

  {assume "\<forall>i\<in>J. Ex (\<phi> i) \<and> bdd_above {h b |b. \<phi> i b}"
      and 0: "{\<Sum>i\<in>J. h (b2 i) |b2. \<forall>i\<in>J. \<phi> i (b2 i)} = {}"
    hence "\<forall>i\<in>J. \<exists>b. \<phi> i b" by auto
    hence "\<exists> b2. \<forall>i\<in>J. \<phi> i (b2 i)" 
      by (intro exI[of _ "\<lambda>i. SOME b. \<phi> i b"]) (simp add: some_eq_ex)
    hence False using 0 by blast } note 1 = this

  {assume "\<forall>i\<in>J. Ex (\<phi> i) \<and> (\<exists>M. \<forall>x\<in>{h b |b. \<phi> i b}. x \<le> M)"
    then obtain Ms where 0: "\<forall>i\<in>J. \<forall>b. \<phi> i b \<longrightarrow> h b \<le> Ms i" 
      by simp metis
    have "\<exists>M. \<forall>x\<in>{\<Sum>i\<in>J. h (b2 i) |b2. \<forall>i\<in>J. \<phi> i (b2 i)}. x \<le> M"
      apply(rule exI[of _ "sum Ms J"]) using insert 0 
      by (auto simp: sum_mono) 
  } note 2 = this

  show ?case apply(subst sum.insert)
    subgoal by fact
    subgoal by fact
    subgoal apply(subst sum.insert)
      subgoal by fact
      subgoal by fact
      subgoal apply(subst insert.IH) 
        subgoal using insert by auto
        subgoal using insert apply(subst plus_Sup_commute) 
          subgoal by auto
          subgoal by auto 
          subgoal using 1 by auto
          subgoal unfolding bdd_above_def using 2 by auto 
          subgoal apply(rule arg_cong[of _ _ Sup]) apply(rule Collect_eqI) apply safe 
            subgoal for _ b1 b2 apply(rule exI[of _ "\<lambda>j'. if j'=j then b1 else b2 j'"])  
              by (smt (verit, best) insertE sum.cong) 
            subgoal by auto . . . . .
qed auto


subsection \<open>Positivity, boundedness and infinite summation\<close>

definition positive :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "positive f A \<equiv> \<forall>a\<in>A. f a \<ge> 0"

(* sum-bounded: *)
definition sbounded :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "sbounded f A \<equiv> \<exists>r. \<forall>B. B \<subseteq> A \<and> finite B \<longrightarrow> sum f B \<le> r"

(* Infinite sums *)
definition isum :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where 
  "isum f A \<equiv> Sup (sum f  ` {B | B . B \<subseteq> A \<and> finite B})"

lemma positive_mono: "positive p A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> positive p B"
  unfolding positive_def by auto

lemma positive_eq:
  assumes "positive f A" and "\<forall>a\<in>A. f1 a = f a"
  shows "positive f1 A"
  using assms unfolding positive_def by auto

(* *)

lemma sbounded_eq:
  assumes "sbounded f A" and "\<forall>a\<in>A. f1 a = f a"
  shows "sbounded f1 A"
  using assms unfolding sbounded_def by (simp add: subset_eq) 

lemma finite_imp_sbounded: "positive f A \<Longrightarrow> finite A \<Longrightarrow> sbounded f A"
  unfolding sbounded_def positive_def apply(rule exI[of _ "sum f A"]) 
  by simp (meson DiffD1 sum_mono2) 

lemma sbounded_empty[simp,intro!]: "sbounded f {}"
  unfolding sbounded_def by auto

lemma sbounded_insert[simp]: "sbounded f (insert a A) \<longleftrightarrow> sbounded f A"
  unfolding sbounded_def apply safe 
	subgoal by (meson subset_insertI2) 
  subgoal for r apply(rule exI[of _ "r + max 0 (f a)"]) 
  	by simp (smt finite_Diff subset_insert_iff sum.remove) .

lemma sbounded_Un[simp]: "sbounded f (A1 \<union> A2) \<longleftrightarrow> sbounded f A1 \<and> sbounded f A2"
  unfolding sbounded_def apply safe
  subgoal by (meson sup.coboundedI1) 
  subgoal by (meson sup.coboundedI2) 
  subgoal for r1 r2 apply(rule exI[of _ "r1+r2"]) apply safe apply(elim subset_UnE) 
  	by simp (smt Diff_subset finite_Diff order.trans sum.union_diff2 sum.union_inter) .

lemma sbounded_UNION: 
  assumes "finite I" shows "sbounded f (\<Union>i\<in>I. A i) \<longleftrightarrow> (\<forall>i\<in>I. sbounded f (A i))" 
  using assms by (induction I) auto

lemma sbounded_mono: "A \<subseteq> B \<Longrightarrow> sbounded f B \<Longrightarrow> sbounded f A"
  unfolding sbounded_def by (meson order_trans)

lemma sbounded_reindex: "sbounded (f o u) A \<Longrightarrow> sbounded f (u ` A)"
  unfolding sbounded_def apply safe subgoal for r
    apply(rule exI[of _ r]) apply safe  
    by (metis finite_image_iff subset_image_inj sum.reindex) .

lemma sbounded_reindex_inj_on: "inj_on u A \<Longrightarrow> sbounded f (u ` A) \<longleftrightarrow> sbounded (f o u) A"
  by (smt (verit, best) comp_apply f_the_inv_into_f sbounded_eq sbounded_reindex the_inv_into_onto)

lemma sbounded_swap: 
  "sbounded (\<lambda>(a,b). f a b) (A \<times> B) \<longleftrightarrow> sbounded (\<lambda>(b,a). f a b) (B \<times> A)"
proof-
  have 0: "A \<times> B = (\<lambda>(a,b). (b,a)) ` (B \<times> A)" by auto
  show ?thesis unfolding 0 apply(subst sbounded_reindex_inj_on)  
    by (auto simp: o_def inj_on_def intro!: arg_cong2[of _ _ _ _ sbounded])
qed

lemma sbounded_constant_0: 
  assumes "\<forall>a\<in>A. f a = (0::real)"
  shows "sbounded f A"
  using assms unfolding sbounded_def  
  by (metis in_mono order_refl sum_nonpos)

lemma sbounded_setminus: 
  assumes "sbounded f A" and "\<forall>b\<in>B-A. f b = 0"
  shows "sbounded f B"
  by (metis Un_Diff_cancel2 assms sbounded_Un sbounded_constant_0)


(* isum versus sum *)
lemma isum_eq_sum:
  "positive f A \<Longrightarrow> finite A \<Longrightarrow> isum f A = sum f A"
  unfolding isum_def positive_def apply(subst cSup_eq_maximum[of "sum f A"]) 
  subgoal by simp   
  subgoal using sum_mono3 by fastforce  
  subgoal by simp .

(* Congruence and monotonicity *)
(* thm sum.cong *)
lemma isum_cong: 
  assumes "A = B" and "\<And>x. x \<in> B \<Longrightarrow> g x = h x" 
  shows "isum g A = isum h B"
  using assms unfolding isum_def 
  by (auto intro!: SUP_cong comm_monoid_add_class.sum.cong)

(* thm sum_mono *)
lemma isum_mono: 
  assumes "sbounded h A" and "\<And>x. x \<in> A \<Longrightarrow> g x \<le> h x" 
  shows "isum g A \<le> isum h A"
  using assms unfolding isum_def  
  apply(intro cSup_mono)
  subgoal by auto
  subgoal unfolding bdd_above_def sbounded_def by auto
  subgoal for r apply safe 
    subgoal for _ B apply(rule bexI[of _ "sum h B"]) apply (auto intro: sum_mono) . . .

lemma isum_mono': 
  assumes "sbounded g B" and "A \<subseteq> B" 
  shows "isum g A \<le> isum g B"
  using assms unfolding isum_def
  apply(intro cSup_subset_mono)
  unfolding bdd_above_def sbounded_def by auto

(* isum vs. 0 *)
(* thm comm_monoid_add_class.sum.empty *)
lemma isum_empty[simp]: "isum g {} = 0"
  unfolding isum_def by auto

(* thm comm_monoid_add_class.sum.neutral_const *)
lemma isum_const_zero[simp]: "isum (\<lambda>x. 0) A = 0"
  unfolding isum_def 
  by simp (metis cSUP_const empty_iff empty_subsetI finite.emptyI mem_Collect_eq)

(* thm sum.neutral  *)
lemma isum_const_zero': "\<forall>x\<in>A. g x = 0 \<Longrightarrow> isum g A = 0"
  by (simp add: isum_cong)

(* thm sum_eq_0_iff  *)
lemma isum_eq_0_iff: "positive f A \<Longrightarrow> sbounded f A \<Longrightarrow> isum f A = 0 \<longleftrightarrow> (\<forall>a\<in>A. f a = 0)"
  unfolding isum_def apply(subst Sup_eq_0_iff) 
  subgoal by auto
  subgoal unfolding bdd_above_def sbounded_def by auto   
  subgoal by (auto simp: positive_def in_mono sum_nonneg)
  subgoal by (auto simp: positive_def in_mono sum_nonneg) .

(* Reindexing: *)
(* thm sum.reindex *)
lemma isum_reindex: "inj_on h A \<Longrightarrow> isum g (h ` A) = isum (g \<circ> h) A"
  unfolding isum_def apply(rule arg_cong[of _ _ Sup]) 
  unfolding image_def[of "sum g"] image_def[of "sum (g \<circ> h)"] 
  apply(rule Collect_eqI) 
  by (smt (verit, del_insts) finite_image_iff inj_on_subset mem_Collect_eq subset_image_inj sum.reindex)

(* thm sum.reindex_cong *)
lemma isum_reindex_cong: "inj_on l B \<Longrightarrow> A = l ` B \<Longrightarrow> 
 (\<And>x. x \<in> B \<Longrightarrow> g (l x) = h x) \<Longrightarrow> isum g A = isum h B"
  by (metis isum_cong comp_def isum_reindex)

(* thm sum.reindex_nontrivial *)
lemma isum_reindex_cong': 
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> h x = h y \<Longrightarrow> g (h x) = 0) \<Longrightarrow> isum g (h ` A) = isum (g \<circ> h) A"
  unfolding isum_def apply(rule arg_cong[of _ _ Sup]) 
  unfolding image_def[of "sum g"] image_def[of "sum (g \<circ> h)"] apply(rule Collect_eqI)
  apply safe  
  subgoal by(metis (no_types, lifting) finite_image_iff mem_Collect_eq subset_image_inj sum.reindex)
  subgoal by (smt finite_imageI image_mono in_mono mem_Collect_eq sum.reindex_nontrivial) .

(* thm sum.mono_neutral_cong *)
lemma isum_zeros_cong:
  assumes "sbounded g (S \<inter> T) \<or> sbounded h (S \<inter> T)"
    and "(\<And>i. i \<in> T - S \<Longrightarrow> h i = 0)" and "(\<And>i. i \<in> S - T \<Longrightarrow> g i = 0)"
    and "(\<And>x. x \<in> S \<inter> T \<Longrightarrow> g x = h x)"
  shows "isum g S = isum h T"
proof-
  have 0: "sbounded g S \<or> sbounded h T" using assms  
    by (metis Diff_Int2 Int_absorb Int_commute sbounded_setminus)
  show ?thesis unfolding isum_def apply(rule Sup_image_cong)
    subgoal by auto
    subgoal apply safe
      subgoal for _ B
        apply(rule bexI[of _ "B \<inter> T"], rule order_eq_refl)
         apply(rule sum.mono_neutral_cong) using assms by auto .
    subgoal apply safe
      subgoal for _ B
        apply(rule bexI[of _ "B \<inter> S"], rule order_eq_refl)
         apply(rule sum.mono_neutral_cong) using assms by auto .
    subgoal using assms(2,3,4) 0 unfolding bdd_above_def sbounded_def apply (elim disjE exE)
      subgoal for r apply(rule disjI1) apply(rule exI[of _ r]) by auto
      subgoal for r apply(rule disjI2) apply(rule exI[of _ r]) by auto . .
qed

(* thm sum.mono_neutral_left *)
lemma isum_zeros_congL: 
  "sbounded g S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i\<in>T - S. g i = 0 \<Longrightarrow> isum g S = isum g T"
  by (metis Diff_eq_empty_iff emptyE isum_zeros_cong le_iff_inf)

(* thm sum.mono_neutral_right *)
lemma isum_zeros_congR:
  "sbounded g S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i\<in>T - S. g i = 0 \<Longrightarrow> isum g T = isum g S"
  by (simp add: isum_zeros_congL)

lemma isum_singl[simp]: "f a \<ge> (0::real) \<Longrightarrow> isum f {a} = f a"  
  by (simp add: positive_def isum_eq_sum)

lemma isum_two[simp]: "a1 \<noteq> a2 \<Longrightarrow> f a1 \<ge> (0::real) \<Longrightarrow> f a2 \<ge> 0 \<Longrightarrow> isum f {a1,a2} = f a1 + f a2"  
  by (simp add: positive_def isum_eq_sum)

lemma isum_three[simp]: "a1 \<noteq> a2 \<Longrightarrow> a1 \<noteq> a3 \<Longrightarrow> a2 \<noteq> a3 \<Longrightarrow> f a1 \<ge> 0 \<Longrightarrow> f a2 \<ge> (0::real) \<Longrightarrow> f a3 \<ge> 0 \<Longrightarrow> 
 isum f {a1,a2,a3} = f a1 + f a2 + f a3"  
  by (simp add: positive_def isum_eq_sum)

lemma isum_ge_0: "positive f A \<Longrightarrow> sbounded f A \<Longrightarrow> isum f A \<ge> 0"
  using isum_mono' by fastforce

lemma in_le_isum: "positive f A \<Longrightarrow> sbounded f A \<Longrightarrow> a \<in> A \<Longrightarrow> f a \<le> isum f A"
  by (metis (full_types) DiffE positive_def Set.set_insert equals0I 
      insert_mono isum_mono' isum_singl subsetI)

lemma isum_eq_singl: 
  assumes fx: "f a = x" and f: "\<forall>a'. a' \<noteq> a \<longrightarrow> f a' = 0" and x: "x \<ge> 0" and a: "a \<in> A"
  shows "isum f A = x"
  apply(subst fx[symmetric])
  apply(subst isum_singl[of f a, symmetric])
  subgoal using assms by simp
  subgoal apply(rule isum_zeros_cong) using assms by auto .

lemma isum_le_singl: 
  assumes fx: "f a \<le> x" and f: "\<forall>a'. a' \<noteq> a \<longrightarrow> f a' = 0" and x: "f a \<ge> 0" and a: "a \<in> A"
  shows "isum f A \<le> x"
  by (metis a f fx isum_eq_singl x)

lemma isum_insert[simp]: "a \<notin> A \<Longrightarrow> sbounded f A \<Longrightarrow> f a \<ge> 0 \<Longrightarrow> isum f (insert a A) = isum f A + f a"
  unfolding isum_def apply(subst plus_SupR)
  subgoal by auto
  subgoal unfolding sbounded_def bdd_above_def by auto
  subgoal apply(rule Sup_cong) 
    subgoal by auto
    subgoal apply safe subgoal for _ _ B   
      apply(rule bexI[of _ "sum f (B - {a}) + f a"]) 
      subgoal by (cases "a \<in> B") (auto simp: image_def sum.remove) 
      subgoal by blast . . 
  subgoal apply safe subgoal for _ _ _ B 
    apply(rule bexI[of _ "sum f (insert a B)"]) 
    subgoal by (cases "a \<in> B") (auto simp: image_def sum.remove) 
    subgoal by blast . .
  subgoal unfolding sbounded_def bdd_above_def apply (elim exE)
    subgoal for r apply(rule disjI2, rule exI[of _ "r + f a"]) by auto . . .

(* thm sum.UNION_disjoint *)
lemma isum_UNION: 
  assumes dsj: "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}" and sb: "sbounded g (\<Union> (A ` I))" 
  shows "isum g (\<Union> (A ` I)) = isum (\<lambda>i. isum g (A i)) I"
proof-
  {fix J assume J: "J \<subseteq> I" "finite J"
    have "sum (\<lambda>i. Sup {sum g B | B. B \<subseteq> A i \<and> finite B}) J = 
       Sup {sum (\<lambda>i. sum g (B i)) J | B . \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
      using J sb apply(subst sum_Sup_commute)
      subgoal by auto
      subgoal unfolding sbounded_def bdd_above_def  
        by simp (metis SUP_upper2 bot.extremum finite.emptyI in_mono)
      subgoal by auto .
    also have "\<dots> = 
       Sup {sum g (\<Union> (B ` J)) | B . \<forall>i\<in>J. B i \<subseteq> A i \<and> finite (B i)}"
      apply(rule arg_cong[of _ _ Sup]) apply(rule Collect_eqI) apply(rule ex_cong1) 
      apply safe
      subgoal 
        apply(rule sum.UNION_disjoint[symmetric])
        using J dsj by auto (metis IntI empty_iff subsetD)
      subgoal 
        apply(rule sum.UNION_disjoint)
        using J dsj by auto (metis IntI empty_iff subsetD) .
    also have "\<dots> =  
       Sup {sum g B | B . B \<subseteq> \<Union> (A ` J) \<and> finite B}"  
      apply(rule Sup_cong) apply safe
      subgoal by auto
      subgoal for _ B
        apply(rule bexI[of _ "sum g (\<Union> (B ` J))"]) using J by auto
      subgoal for _ B
        apply(rule bexI[of _ "sum g (\<Union> ((\<lambda>i. B \<inter> A i) ` J))"])
        subgoal using J unfolding incl_UNION_aux2 by auto
        subgoal by blast .
      subgoal using J sb unfolding bdd_above_def sbounded_def  
      	by simp (metis UN_mono finite_UN_I) .
    also have "\<dots> \<le> 
       Sup {sum g B | B . B \<subseteq> \<Union> (A ` I) \<and> finite B}" 
      apply(rule cSup_subset_mono) apply safe
      subgoal by auto
      subgoal using J sb unfolding sbounded_def bdd_above_def by auto
      subgoal for _ B apply(rule exI[of _ B]) using J by auto . 
    finally 
    have "(\<Sum>i\<in>J. Sup {y. \<exists>B\<subseteq>A i. finite B \<and> y = sum g B}) \<le> 
           Sup {y. \<exists>B\<subseteq>\<Union> (A ` I). finite B \<and> y = sum g B}" 
      by (smt Collect_cong sum_mono)
  } note 1 = this

  show ?thesis
    unfolding isum_def apply(rule Sup_image_congL)  
    unfolding image_def[of "sum g"] image_def[of "sum (\<lambda>i. Sup {y. \<exists>x\<in>{B |B. B \<subseteq> A i \<and> finite B}. y = sum g x})"] 
      apply safe
    subgoal by auto
    subgoal for _ B using assms  
      apply(intro bexI[of _ "{i. i \<in> I \<and> B \<inter> A i \<noteq> {}}"])
      subgoal apply(subst incl_UNION_aux[of B A I], assumption)
        apply(subst comm_monoid_add_class.sum.UNION_disjoint)
        subgoal by (simp add: disjoint_finite_aux)
        subgoal by auto
        subgoal by auto
        subgoal apply(rule sum_mono) 
          subgoal for i apply(rule cSup_upper) 
            subgoal by auto
            subgoal unfolding bdd_above_def sbounded_def by simp (metis UN_I in_mono subsetI) . . . 
      subgoal by (simp add: disjoint_finite_aux) . 
    subgoal using 1 by auto . 
qed

lemma isum_Un[simp]: 
  assumes "positive f A1" "sbounded f A1" "positive f A2" "sbounded f A2" "A1 \<inter> A2 = {}"
  shows "isum f (A1 \<union> A2) = isum f A1 + isum f A2"
proof-
  have [simp]: "isum (\<lambda>i. isum f (case i of 0 \<Rightarrow> A1 | Suc _ \<Rightarrow> A2)) {0, Suc 0} = isum f A1 + isum f A2"
    apply(subst isum_two) using assms by (auto intro!: isum_ge_0)
  show ?thesis using assms isum_UNION[of "{0,1::nat}" "\<lambda>i. case i of 0 \<Rightarrow> A1 |_ \<Rightarrow> A2" f] by auto
qed

(* thm sum.Sigma *)
lemma isum_Sigma: 
  assumes sbd: "sbounded (\<lambda>(a,b). f a b) (Sigma A Bs)"
  shows "isum (\<lambda>(a,b). f a b) (Sigma A Bs) = isum (\<lambda>a. isum (f a) (Bs a)) A"
proof-
  define g where "g \<equiv> \<lambda>(a,b). f a b"
  define Cs where "Cs \<equiv> \<lambda>a. {a} \<times> Bs a"
  have 1: "\<And>a. {a} \<times> Bs a = Pair a ` (Bs a)" by auto
  have 0: "Sigma A Bs = (\<Union>a\<in>A. Cs a)" unfolding Cs_def by auto
  show ?thesis unfolding 0 apply(subst isum_UNION)
    subgoal unfolding Cs_def by auto
    subgoal using sbd unfolding 0 .
    subgoal unfolding Cs_def apply(rule arg_cong2[of _ _ _ _ isum]) 
      subgoal unfolding 1  
        apply(subst isum_reindex_cong') by (auto simp: o_def) 
      subgoal .. . .
qed  

(* Redundant but visually useful: *)
(* thm sum.cartesian_product *)
lemma isum_Times: 
  assumes "sbounded (\<lambda>(a,b). f a b) (A \<times> B)"
  shows "isum (\<lambda>(a,b). f a b) (A \<times> B) = isum (\<lambda>a. isum (f a) B) A"
  using isum_Sigma[OF assms] .

(* thm sum.swap *)
lemma isum_swap: 
  assumes "sbounded (\<lambda>(a,b). f a b) (A \<times> B)"
  shows "isum (\<lambda>a. isum (f a) B) A = isum (\<lambda>b. isum (\<lambda>a. f a b) A) B" (is "?L = ?R")
proof-
  have 0: "A \<times> B = (\<lambda>(a,b). (b,a)) ` (B \<times> A)" by auto
  have "?L = isum (\<lambda>(a,b). f a b) (A \<times> B)" using isum_Times[OF assms] ..
  also have "\<dots> = isum (\<lambda>(b,a). f a b) (B \<times> A)" unfolding 0 apply(subst isum_reindex_cong') 
    by (auto simp: o_def intro!: arg_cong2[of _ _ _ _ isum])
  also have "\<dots> = ?R" apply(subst isum_Times) using assms sbounded_swap by auto
  finally show ?thesis .
qed

lemma isum_plus:
  assumes f1: "positive f1 A" "sbounded f1 A"
    and f2: "positive f2 A" "sbounded f2 A"
  shows "isum (\<lambda>a. f1 a + f2 a) A = isum f1 A + isum f2 A"
  unfolding isum_def apply(subst plus_Sup_commute')
  subgoal by auto
  subgoal using f1 unfolding sbounded_def bdd_above_def by auto
  subgoal by auto
  subgoal using f2 unfolding sbounded_def bdd_above_def by auto
  subgoal apply(rule Sup_cong)
    subgoal by auto
    subgoal apply safe 
      subgoal for _ _ B
        apply(rule bexI[of _ "\<Sum>a\<in>B. f1 a + f2 a"]) 
        subgoal by auto
        subgoal apply clarify apply(rule exI[of _ "sum f1 B"]) apply(rule exI[of _ "sum f2 B"])
          using sum.distrib by auto . .
    subgoal apply safe
      subgoal for _ _ _ _ _ B1 B2
        apply(rule bexI[of _ "\<Sum>a\<in>B1 \<union> B2. f1 a + f2 a"])
        subgoal apply(subst sum.distrib) apply(rule add_mono)
          subgoal apply(rule sum_mono2) using f1 unfolding positive_def by auto   
          subgoal apply(rule sum_mono2) using f2 unfolding positive_def by auto .
        subgoal by auto . . 
    subgoal apply(rule disjI2)
      using f1 f2 unfolding sbounded_def bdd_above_def apply (elim exE)
      subgoal for r1 r2 apply(rule exI[of _ "r1 + r2"]) apply safe
        by (auto simp: add_mono) . . .


(* Distributivity w.r.t. multiplication *) 

lemma sbounded_product:
  assumes f: "positive f A" "sbounded f A" and g: "positive g B" "sbounded g B"
  shows "sbounded (\<lambda>(a,b). f a * g b) (A \<times> B)"
  using assms unfolding sbounded_def positive_def apply safe
  subgoal for r1 r2
    apply(rule exI[of _ "r1*r2"]) apply safe subgoal for Ba 
      apply(rule order.trans[OF sum_mono2[of "fst`Ba \<times> snd`Ba" Ba "\<lambda>(a,b). f a * g b"]])
      subgoal by auto
      subgoal  by (simp add: subset_fst_snd)
      subgoal for ab apply(cases ab, simp) 
        by (metis (no_types, lifting) imageE mem_Sigma_iff mult_nonneg_nonneg prod.collapse subset_eq)
      subgoal apply(subst sum.cartesian_product[symmetric]) 
        apply(subst sum_product[symmetric])  
        by (smt finite_imageI imageE mem_Sigma_iff mult_mono prod.collapse subset_eq sum_nonneg) . . .

lemma sbounded_multL: "x \<ge> 0 \<Longrightarrow> sbounded f A \<Longrightarrow> sbounded (\<lambda>a. x * f a) A"
  unfolding sbounded_def apply safe 
  subgoal for r apply(rule exI[of _ "x * r"])
    by (metis mult.commute mult_right_mono sum_distrib_left) .

lemma sbounded_multL_strict[simp]: 
  assumes x: "x > 0"
  shows "sbounded (\<lambda>a. x * f a) A \<longleftrightarrow> sbounded f A"
proof-
  have 0: "f = (\<lambda>a. (1 / x) * (x * f a))" unfolding fun_eq_iff using x by auto
  show ?thesis apply safe
    subgoal apply(subst 0) apply(rule sbounded_multL) using x by auto
    subgoal apply(rule sbounded_multL) using x by auto . 
qed

lemma sbounded_multR: "x \<ge> 0 \<Longrightarrow> sbounded f A \<Longrightarrow> sbounded (\<lambda>a. f a * x) A"
  unfolding sbounded_def apply safe 
  subgoal for r apply(rule exI[of _ "r * x"])
    by (metis mult.commute mult_left_mono sum_distrib_right) .

lemma sbounded_multR_strict[simp]: 
  assumes x: "x > 0"
  shows "sbounded (\<lambda>a. f a * x) A \<longleftrightarrow> sbounded f A"
proof-
  have 0: "f = (\<lambda>a. (f a * x) * (1 / x))" unfolding fun_eq_iff using x by auto
  show ?thesis apply safe
    subgoal apply(subst 0) apply(rule sbounded_multR) using x by auto
    subgoal apply(rule sbounded_multR) using x by auto . 
qed

lemma positive_sbounded_multL: 
  assumes f: "positive f A" "sbounded f A" and g: "\<forall>a\<in>A. g a \<le> x" 
  shows "sbounded (\<lambda>a. f a * g a) A"
proof-
  define y where "y \<equiv> max x 0"
  have g: "\<forall>a\<in>A. g a \<le> y \<and> y \<ge> 0" using g unfolding y_def by auto
  show ?thesis using assms unfolding sbounded_def apply safe
    subgoal for r  apply(intro exI[of _ "r * y"]) apply safe
      subgoal for B 
        apply(rule order.trans[OF sum_mono[of B "\<lambda>a. f a * g a" "\<lambda>a. f a * y"]])
        subgoal unfolding positive_def  
          by (simp add: g in_mono mult_left_mono)
        subgoal apply(subst sum_distrib_right[symmetric]) 
          by (metis max.cobounded2 mult.commute mult_left_mono y_def) . . . 
qed

lemma positive_sbounded_multR: 
  assumes f: "positive f A" "sbounded f A" and g: "\<forall>a\<in>A. g a \<le> x" 
  shows "sbounded (\<lambda>a. g a * f a) A"
  using positive_sbounded_multL[OF assms]
  unfolding sbounded_def apply safe 
  subgoal for r apply(rule exI[of _ r]) apply safe 
    subgoal for B
      apply(subst sum.cong[of B B _ "\<lambda>a. f a * g a"]) by auto . .

(* *)
lemma isum_product_Times:
  assumes f: "positive f A" "sbounded f A" and g: "positive g B" "sbounded g B"
  shows "isum f A * isum g B = isum (\<lambda>(a,b). f a * g b) (A \<times> B)"
  unfolding isum_def apply(subst mult_Sup_commute')
  subgoal by auto
  subgoal using f(2) unfolding bdd_above_def sbounded_def by auto
  subgoal using f by (auto simp: positive_def subsetD sum_nonneg)
  subgoal by auto
  subgoal using g(2) unfolding bdd_above_def sbounded_def by auto
  subgoal using g by (auto simp: positive_def subsetD sum_nonneg)
  subgoal apply(rule Sup_cong)  
    subgoal by auto
    subgoal using f(2) g(2) unfolding sbounded_def apply safe
      subgoal for a r1 r2 a1 a2 x xa A1 B1
        apply(rule bexI[of _ "sum (\<lambda>(a, b). f a * g b) (A1 \<times> B1)"])
        subgoal apply(subst sum_product) 
          apply(subst sum.cartesian_product) 
          apply(subst sum_mono2) by auto 
        subgoal by (simp add: image_def) (metis Sigma_mono finite_SigmaI) . .
    subgoal using f(2) g(2) unfolding sbounded_def apply safe
      subgoal for b x r ra AB1
        apply(rule bexI[of _ "sum f (fst ` AB1) * sum g (snd ` AB1)"])
        subgoal apply(subst sum_product) 
          apply(subst sum.cartesian_product) 
          apply(subst sum_mono2) 
          subgoal by (simp_all add: subset_fst_snd)
          subgoal by (simp_all add: subset_fst_snd)
          subgoal for ab using f(1) g(1) unfolding positive_def apply(cases ab)
            by simp (metis (no_types, lifting) imageE mem_Sigma_iff mult_nonneg_nonneg prod.collapse subsetD)
          subgoal .. . 
        subgoal apply (simp add: image_def)  
          apply(rule exI[of _ "sum f (fst ` AB1)"], rule exI[of _ "sum g (snd ` AB1)"])
          apply (simp add: image_def) apply safe 
          subgoal apply(rule exI[of _ "fst ` AB1"]) by (fastforce simp: image_def) 
          subgoal apply(rule exI[of _ "snd ` AB1"]) by (fastforce simp: image_def) . . . 
    subgoal apply(rule disjI1) using sbounded_product[OF assms]
      unfolding sbounded_def bdd_above_def image_def apply safe
      subgoal for r apply(rule exI[of _ r]) 
        by simp (metis (no_types) Sigma_mono finite_cartesian_product sum.cartesian_product sum_product) 
      . . .

(* thm sum_product *)
lemma isum_product:
  assumes f: "positive f A" "sbounded f A" and g: "positive g B" "sbounded g B"
  shows "isum f A * isum g B = isum (\<lambda>a. isum (\<lambda>b. f a * g b) B) A"
  by (simp add: assms isum_Times isum_product_Times sbounded_product)

(* thm sum_distrib_right *)
lemma isum_distribR: 
  assumes f: "positive f (A::'a set)" "sbounded f A" and r: "r \<ge> 0"
  shows "isum f A * r = isum (\<lambda>a. f a * r) A"
proof-
  have 0: "A \<times> {0} = (\<lambda>a. (a, 0::nat)) ` A" by auto 
  show ?thesis
    apply(subst isum_singl[of "\<lambda>_. r" "0::nat",symmetric, OF r])
    apply(subst isum_product_Times)
    subgoal by fact
    subgoal by fact
    subgoal using r unfolding positive_def by auto
    subgoal by simp
    subgoal apply (subst 0) apply(subst isum_reindex) unfolding inj_on_def o_def by auto .
qed

(* thm sum_distrib_left *)
lemma isum_distribL: 
  assumes f: "positive f (A::'a set)" "sbounded f A" and r: "r \<ge> 0"
  shows "r * isum f A = isum (\<lambda>a. r * f a) A"
proof-
  have 0: "r * isum f A = isum f A * r"
    "(\<lambda>a. r * f a) = (\<lambda>a. f a * r)" unfolding fun_eq_iff by auto
  show ?thesis unfolding 0 using isum_distribR[OF assms] .
qed


end