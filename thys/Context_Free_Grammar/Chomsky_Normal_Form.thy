(*
Authors: August Martin Stimpfle, Tobias Nipkow
Based on HOL4 theories by Aditi Barthwal
*)

section \<open>Conversion to Chomsky Normal Form\<close>

theory Chomsky_Normal_Form
imports Unit_Elimination Epsilon_Elimination
begin

definition CNF :: "('n, 't) Prods \<Rightarrow> bool" where
"CNF P \<equiv> (\<forall>(A,\<alpha>) \<in> P. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>a. \<alpha> = [Tm a]))"

lemma Nts_correct: "A \<notin> Nts P \<Longrightarrow> (\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>))"
unfolding Nts_def Nts_syms_def by auto

(* Chomsky Normal Form *)

definition uniformize :: "'n::infinite \<Rightarrow> 't \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t) Prods \<Rightarrow> bool" where 
      "uniformize A t S P P' \<equiv> (
    \<exists> l r p s. (l,r) \<in> P \<and> (r = p@[Tm t]@s) 
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> A \<notin> Nts P \<union> {S}
    \<and> P' = P - {(l,r)} \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"

lemma uniformize_Eps_free:
  assumes "Eps_free P"
    and "uniformize A t S P P'"
  shows "Eps_free P'"
  using assms unfolding uniformize_def Eps_free_def by force

lemma uniformize_Unit_free:
  assumes "Unit_free P"
    and "uniformize A t S P P'"
  shows "Unit_free P'"
proof -
  have 1: "\<nexists>l A. (l,[Nt A]) \<in> P"
    using assms(1) unfolding Unit_free_def by simp
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> P' = ((P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(2) unfolding uniformize_def by blast
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A,[Tm t]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "P' = ((P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using lrps by simp
  ultimately show ?thesis unfolding Unit_free_def by simp
qed

definition prodTms :: "('n,'t) prod \<Rightarrow> nat" where
"prodTms p \<equiv> (if length (snd p) \<le> 1 then 0 else length (filter (isTm) (snd p)))"

definition prodNts :: "('n,'t) prod \<Rightarrow> nat" where
"prodNts p \<equiv> (if length (snd p) \<le> 2 then 0 else length (filter (isNt) (snd p)))"

fun badTmsCount :: "('n,'t) Prods \<Rightarrow> nat" where
  "badTmsCount P = sum prodTms P"

lemma badTmsCountSet: "finite P \<Longrightarrow> (\<forall>p \<in> P. prodTms p = 0) \<longleftrightarrow> badTmsCount P = 0"
by simp

fun badNtsCount :: "('n,'t) Prods \<Rightarrow> nat" where
  "badNtsCount P = sum prodNts P"

lemma badNtsCountSet: assumes "finite P"
  shows "(\<forall>p \<in> P. prodNts p = 0) \<longleftrightarrow> badNtsCount P = 0"
  using assms by simp

definition uniform :: "('n, 't) Prods \<Rightarrow> bool" where
  "uniform P \<equiv> \<forall>(A, \<alpha>) \<in> P. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"

lemma uniform_badTmsCount: assumes "finite P"
  shows "uniform P \<longleftrightarrow> badTmsCount P = 0"
proof 
  assume assm: "uniform P"
  have "\<forall>p \<in> P. prodTms p = 0"
  proof 
    fix p assume "p \<in> P"
    hence "(\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t])"
      using assm unfolding uniform_def by auto
    hence "length (snd p) \<le> 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      by auto
    hence "length (snd p) \<le> 1 \<or> length (filter (isTm) (snd p)) = 0"
      unfolding isTm_def by (auto simp: filter_empty_conv)
    thus "prodTms p = 0"
      unfolding prodTms_def by argo
   qed
   thus "badTmsCount P = 0"
     using badTmsCountSet assms by blast
next 
  assume assm: "badTmsCount P = 0"
  have "\<forall>p \<in> P. ((\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t]))"
  proof 
    fix p assume "p \<in> P"
    hence "prodTms p = 0"
      using assm badTmsCountSet assms by blast
    hence "length (snd p) \<le> 1 \<or> length (filter (isTm) (snd p)) = 0"
      unfolding prodTms_def by argo
    hence "length (snd p) \<le> 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      by (auto simp: isTm_def filter_empty_conv)
    hence "length (snd p) = 0 \<or> length (snd p) = 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      using order_neq_le_trans by blast
    thus "(\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t])"
      by (auto simp: length_Suc_conv)
  qed
  thus "uniform P"
    unfolding uniform_def by auto
qed

definition binary :: "('n, 't) Prods \<Rightarrow> bool" where
  "binary P \<equiv> \<forall>(A, \<alpha>) \<in> P. length \<alpha> \<le> 2"

lemma binary_badNtsCount:
  assumes "finite P" "uniform P" "badNtsCount P = 0"
  shows "binary P"
proof -
  have "\<forall>p \<in> P. length (snd p) \<le> 2"
  proof 
    fix p assume assm: "p \<in> P"
    obtain A \<alpha> where "(A, \<alpha>) = p"
      using prod.collapse by blast
    hence "((\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])) \<and> (prodNts (A, \<alpha>) = 0)"
      using assms badNtsCountSet assm unfolding uniform_def by auto
    hence "((\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])) \<and> (length \<alpha> \<le> 2 \<or> length (filter (isNt) \<alpha>) = 0)"
      unfolding prodNts_def by force
    hence "((\<nexists>t. Tm t \<in> set \<alpha>) \<or> (length \<alpha> \<le> 1)) \<and> (length \<alpha> \<le> 2 \<or> (\<nexists>N. Nt N \<in> set \<alpha>))"
      by (auto simp: filter_empty_conv[of isNt \<alpha>] isNt_def)
    hence "length \<alpha> \<le> 2"
      by (metis Suc_1 Suc_le_eq in_set_conv_nth le_Suc_eq nat_le_linear sym.exhaust)
    thus "length (snd p) \<le> 2"
      using \<open>(A, \<alpha>) = p\<close> by auto
  qed
  thus ?thesis
    by (auto simp: binary_def)
qed

lemma count_bin_un: assumes "finite P"
shows "(binary P \<and> uniform P) \<longleftrightarrow> (badTmsCount P = 0 \<and> badNtsCount P = 0)"
proof 
  assume "binary P \<and> uniform P"
  hence "badTmsCount P = 0 \<and> (\<forall>(A, \<alpha>) \<in> P. length \<alpha> \<le> 2)"
    unfolding binary_def using uniform_badTmsCount assms by blast
  thus "badTmsCount P = 0 \<and> badNtsCount P = 0"
    by (metis badNtsCountSet case_prodE prod.sel(2) prodNts_def assms)
next
  assume "badTmsCount P = 0 \<and> badNtsCount P = 0"
  thus "binary P \<and> uniform P"
    using binary_badNtsCount uniform_badTmsCount assms by blast 
qed


definition binarizeNt :: "'n::infinite \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods \<Rightarrow> bool" where
"binarizeNt A B\<^sub>1 B\<^sub>2 S P P' \<equiv> (
    \<exists>l r p s. (l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> (Nts P \<union> {S}))
    \<and> P' = P - {(l,r)} \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"

lemma binarizeNt_Eps_free:
  assumes "Eps_free P"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Eps_free P'"
  using assms unfolding binarizeNt_def Eps_free_def by force

lemma binarizeNt_Unit_free:
  assumes "Unit_free P"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Unit_free P'"
  proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> P)"
    using assms(1) unfolding Unit_free_def by simp
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> (P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(2) unfolding binarizeNt_def by blast
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using lrps by simp
  ultimately show ?thesis unfolding Unit_free_def by simp
qed

lemma binarizeNt_aux1:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "A \<noteq> B\<^sub>1 \<and> A \<noteq> B\<^sub>2"
using assms unfolding binarizeNt_def Nts_def Nts_syms_def by fastforce

lemma derives_sub:
  assumes "P \<turnstile> [Nt A] \<Rightarrow> u" and "P \<turnstile> xs \<Rightarrow> p @ [Nt A] @ s"
  shows "P \<turnstile> xs \<Rightarrow>* p @ u @ s"
proof -
  have "P \<turnstile> p @ [Nt A] @ s \<Rightarrow>* p @ u @ s"
    using assms derive_append derive_prepend by blast
  thus ?thesis
    using assms(2) by simp
qed

lemma cnf_r1Tm: 
  assumes "uniformize A t S P P'"
    and "P \<turnstile> lhs \<Rightarrow> rhs"
  shows "P' \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' B v where Bv: "lhs = p'@[Nt B]@s' \<and> rhs = p'@v@s' \<and> (B,v) \<in> P"
    using derive.cases[OF assms(2)] by fastforce
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts P)
      \<and> P' = ((P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(1) set_removeAll unfolding uniformize_def by fastforce
  thus ?thesis
  proof (cases "(B, v) \<in> P'")
    case True
    then show ?thesis
      using derive.intros[of B v] Bv by blast
  next
    case False
    hence "B = l \<and> v = p@[Tm t]@s"
      by (simp add: lrps Bv) 
    have 1: "P' \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
      using lrps by (simp add: derive_singleton)
    have "P' \<turnstile> [Nt A] \<Rightarrow> [Tm t]"
      using lrps by (simp add: derive_singleton)
    hence "P' \<turnstile> [Nt l] \<Rightarrow>* p@[Tm t]@s"
      using 1 derives_sub[of \<open>P'\<close>] by blast
    then show ?thesis 
      using False \<open>B = l \<and> v = p@[Tm t]@s\<close> Bv derives_append derives_prepend by blast
  qed
qed

lemma cnf_r1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
    and "P \<turnstile> lhs \<Rightarrow> rhs"
  shows "P' \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' C v where Cv: "lhs = p'@[Nt C]@s' \<and> rhs = p'@v@s' \<and> (C,v) \<in> P"
    using derive.cases[OF assms(2)] by fastforce
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts P)
    \<and> (P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(1) set_removeAll unfolding binarizeNt_def by fastforce
  thus ?thesis
  proof (cases "(C, v) \<in> P'")
    case True
    then show ?thesis
      using derive.intros[of C v] Cv by blast
  next
    case False
    hence "C = l \<and> v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s"
      by (simp add: lrps Cv)
    have 1: "P' \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
      using lrps by (simp add: derive_singleton)
    have "P' \<turnstile> [Nt A] \<Rightarrow> [Nt B\<^sub>1,Nt B\<^sub>2]"
      using lrps by (simp add: derive_singleton)
    hence "P' \<turnstile> [Nt l] \<Rightarrow>* p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" 
      using 1 derives_sub[of \<open>P'\<close>] by blast
    thus ?thesis 
      using False \<open>C = l \<and> v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s\<close> Cv derives_append derives_prepend by blast
  qed
qed

lemma slemma1_1: 
  assumes "uniformize A t S P P'"
    and "(A, \<alpha>) \<in> P'"
  shows "\<alpha> = [Tm t]"
proof -
  have "A \<notin> Nts P"
    using assms(1) unfolding uniformize_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> P"
    unfolding Nts_def by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Tm t] \<and> (A, \<alpha>) \<in> P'"
    using assms(1) unfolding uniformize_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma1_1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
    and "(A, \<alpha>) \<in> P'"
  shows "\<alpha> = [Nt B\<^sub>1,Nt B\<^sub>2]"
proof -
  have "A \<notin> Nts P"
    using assms(1) unfolding binarizeNt_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> P"
    unfolding Nts_def  by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Nt B\<^sub>1,Nt B\<^sub>2] \<and> (A, \<alpha>) \<in> P'"
    using assms(1) unfolding binarizeNt_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_1:
  assumes "Nt A \<notin> set rhs"
  shows "\<forall>\<alpha>. rhs = substsNt A \<alpha> rhs"
  using assms by (simp add: substs_skip)

lemma slemma4_3_1:
  assumes "lhs = A"
  shows "\<alpha> = substsNt A \<alpha> [Nt lhs]"
  using assms by simp

lemma slemma4_4:
  assumes "uniformize A t S P P'"
    and "(l,r) \<in> P"
  shows "Nt A \<notin> set r"
proof -
  have "A \<notin> Nts P"
    using assms(1) unfolding uniformize_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>P\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
    and "(l,r) \<in> P"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> Nts P"
    using assms(1) unfolding binarizeNt_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>P\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed


lemma lemma1:
  assumes "uniformize A t S P P'"
    and "P' \<turnstile> lhs \<Rightarrow> rhs"
  shows "substsNt A [Tm t] lhs = substsNt A [Tm t] rhs
    \<or> P \<turnstile> substsNt A [Tm t] lhs \<Rightarrow> substsNt A [Tm t] rhs"
proof -
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts P) 
      \<and> P' = ((P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(1) set_removeAll unfolding uniformize_def by fastforce
  obtain p' s' u v where uv: "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> P'"
    using derive.cases[OF assms(2)] by fastforce
  thus ?thesis
  proof (cases "u = A")
    case True
    then show ?thesis 
    proof (cases "v = [Tm t]")
      case True
      have "substsNt A [Tm t] lhs = substsNt A [Tm t] p' @ substsNt A [Tm t] ([Nt A]@s')"
        using uv \<open>u = A\<close> by simp
      hence "substsNt A [Tm t] lhs = substsNt A [Tm t] p' @ [Tm t] @ substsNt A [Tm t] s'"
        by simp
      then show ?thesis
        by (simp add: True uv) 
    next
      case False
      then show ?thesis 
        using True uv assms(1) slemma1_1 by fastforce 
    qed
  next
    case False
    then show ?thesis 
    proof (cases "(Nt A) \<in> set v")
      case True
      hence 1: "v = p@[Nt A]@s \<and> Nt A \<notin> set p \<and> Nt A \<notin> set s" 
        using lrps uv assms slemma4_4 by fastforce
      hence "substsNt A [Tm t] v = substsNt A [Tm t] p @ substsNt A [Tm t] ([Nt A]@s)"
        by simp
      hence "substsNt A [Tm t] v = p @ [Tm t] @ s"
        using 1 substs_append slemma4_1 slemma4_3_1 by metis
      hence 2: "(u, substsNt A [Tm t] v) \<in> P" using lrps
        using True uv assms(1) slemma4_4 by fastforce
      have "substsNt A [Tm t] lhs = substsNt A [Tm t] p' @ substsNt A [Tm t] ([Nt u]@s')"
        using uv by simp
      hence 3: "substsNt A [Tm t] lhs = substsNt A [Tm t] p' @ [Nt u] @ substsNt A [Tm t] s'" 
        using \<open>u \<noteq> A\<close> by simp
      have "substsNt A [Tm t] rhs = substsNt A [Tm t] p' @ substsNt A [Tm t] (v@s')"
        using uv by simp
      hence "substsNt A [Tm t] rhs = substsNt A [Tm t] p' @ substsNt A [Tm t] v @ substsNt A [Tm t] s'"
        by simp
      then show ?thesis 
        using 2 3 assms(2) uv derive.simps by fast
    next
      case False
      hence 1: "(u, v) \<in> P" 
        using assms(1) uv \<open>u \<noteq> A\<close> lrps by (simp add: in_set_conv_decomp)
       have "substsNt A [Tm t] lhs = substsNt A [Tm t] p' @ substsNt A [Tm t] ([Nt u]@s')"
         using uv by simp
       hence 2: "substsNt A [Tm t] lhs = substsNt A [Tm t] p' @ [Nt u] @ substsNt A [Tm t] s'"
         using \<open>u \<noteq> A\<close> by simp
       have "substsNt A [Tm t] rhs = substsNt A [Tm t] p' @ substsNt A [Tm t] (v@s')"
         using uv by simp
       hence "substsNt A [Tm t] rhs = substsNt A [Tm t] p' @ substsNt A [Tm t] v @ substsNt A [Tm t] s'"
         by simp
       hence "substsNt A [Tm t] rhs = substsNt A [Tm t] p' @ v @ substsNt A [Tm t] s'"
         using False slemma4_1 by fastforce
       thus ?thesis 
         using 1 2 assms(2) uv derive.simps by fast
    qed
  qed
qed

lemma lemma1Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
    and "P' \<turnstile> lhs \<Rightarrow> rhs"
  shows "(substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs) 
          \<or> (P \<turnstile> (substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs) \<Rightarrow> substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs)"
proof -
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts P)
    \<and> (P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(1) set_removeAll unfolding binarizeNt_def by fastforce
  obtain p' s' u v where uv: "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> P'"
    using derive.cases[OF assms(2)] by fastforce
  thus ?thesis
  proof (cases "u = A")
    case True
    then show ?thesis 
    proof (cases "v = [Nt B\<^sub>1,Nt B\<^sub>2]")
      case True
      have "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] ([Nt A]@s')"
        using uv \<open>u = A\<close> by simp
      hence 1: "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ [Nt B\<^sub>1,Nt B\<^sub>2] @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] s'"
        by simp
      have "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] ([Nt B\<^sub>1,Nt B\<^sub>2]@s')"
        using uv \<open>u = A\<close> True by simp
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ [Nt B\<^sub>1,Nt B\<^sub>2] @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] s'"
        using assms(1) binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 S P P'] by auto 
      then show ?thesis
        using 1 by simp
    next
      case False
      then show ?thesis
        using True uv assms(1) slemma1_1Nt by fastforce
    qed
  next
    case False
    then show ?thesis 
    proof (cases "(Nt A) \<in> set v")
      case True
      have "Nt A \<notin> set p \<and> Nt A \<notin> set s" 
        using lrps assms(1) by (metis UnI1 UnI2 set_append slemma4_4Nt)
      hence 1: "v = p@[Nt A]@s \<and> Nt A \<notin> set p \<and> Nt A \<notin> set s" 
        using True lrps uv assms slemma4_4Nt[of A B\<^sub>1 B\<^sub>2 S P P'] binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 S P P'] by auto
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] ([Nt A]@s)"
        by simp
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v = p @ [Nt B\<^sub>1,Nt B\<^sub>2] @ s"
        using 1 substs_append slemma4_1 slemma4_3_1 by metis
      hence 2: "(u, substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v) \<in> P" 
        using True lrps uv assms(1) slemma4_4Nt by fastforce
      have "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] ([Nt u]@s')"
        using uv by simp
      hence 3: "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ [Nt u] @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] s'" 
        using \<open>u \<noteq> A\<close> by simp
      have "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] (v@s')"
        using uv by simp
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] s'"
        by simp
      then show ?thesis 
        using 2 3 assms(2) uv derive.simps by fast
    next
      case False
      hence 1: "(u, v) \<in> P" 
        using assms(1) uv \<open>u \<noteq> A\<close> lrps by (simp add: in_set_conv_decomp)
       have "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] ([Nt u]@s')"
         using uv by simp
       hence 2: "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ [Nt u] @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] s'"
         using \<open>u \<noteq> A\<close> by simp
       have "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] (v@s')"
         using uv by simp
       hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] s'"
         by simp
       hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p' @ v @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] s'"
         using False slemma4_1 by fastforce
       thus ?thesis 
         using 1 2 assms(2) uv derive.simps by fast
    qed
  qed
qed

lemma lemma3:
  assumes "P' \<turnstile> lhs \<Rightarrow>* rhs"
    and "uniformize A t S P P'"
  shows "P \<turnstile> substsNt A [Tm t] lhs \<Rightarrow>* substsNt A [Tm t] rhs"
  using assms
proof (induction rhs rule: rtranclp_induct)
  case (step y z)
  then show ?case 
    using lemma1[of A t S P P' y z] by auto 
qed simp

lemma lemma3Nt:
  assumes "P' \<turnstile> lhs \<Rightarrow>* rhs"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "P \<turnstile> substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] lhs \<Rightarrow>* substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] rhs"
  using assms 
proof (induction rhs rule: rtranclp_induct)
  case (step y z)
  then show ?case 
    using lemma1Nt[of A B\<^sub>1 B\<^sub>2 S P P' y z] by auto
qed simp

lemma lemma4:
  assumes "uniformize A t S P P'" 
  shows "Lang P' S \<subseteq> Lang P S"
proof 
  fix w
  assume "w \<in> Lang P' S"
  hence "P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    unfolding Lang_def by simp
  hence "P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding uniformize_def by auto
  hence "P \<turnstile> substsNt A [Tm t] [Nt S] \<Rightarrow>* substsNt A [Tm t] (map Tm w)"
    using assms lemma3[of P' \<open>[Nt S]\<close> \<open>map Tm w\<close>] by blast
  moreover have "substsNt A [Tm t] [Nt S] = [Nt S]"
    using assms unfolding uniformize_def by auto
  moreover have "substsNt A [Tm t] (map Tm w) = map Tm w" 
    by simp
  ultimately show "w \<in> Lang P S" 
    by (simp add: Lang_def)
qed

lemma lemma4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Lang P' S \<subseteq> Lang P S"
proof
  fix w
  assume "w \<in> Lang P' S"
  hence "P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    by (simp add: Lang_def)
  hence "P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding binarizeNt_def by auto
  hence "P \<turnstile> substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] [Nt S] \<Rightarrow>*  substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] (map Tm w)"
    using assms lemma3Nt[of P' \<open>[Nt S]\<close> \<open>map Tm w\<close>] by blast
  moreover have "substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] [Nt S] = [Nt S]"
    using assms unfolding binarizeNt_def by auto
  moreover have "substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] (map Tm w) = map Tm w" by simp
  ultimately show "w \<in> Lang P S" using Lang_def
    by (metis (no_types, lifting) mem_Collect_eq)
qed

lemma slemma5_1:
  assumes "P \<turnstile> u \<Rightarrow>* v"
    and "uniformize A t S P P'"
  shows "P' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction v rule: rtranclp_induct) (auto simp: cnf_r1Tm rtranclp_trans)

lemma slemma5_1Nt:
  assumes "P \<turnstile> u \<Rightarrow>* v"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "P' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction v rule: rtranclp_induct) (auto simp: cnf_r1Nt rtranclp_trans)

lemma lemma5: 
  assumes "uniformize A t S P P'"
  shows "Lang P S \<subseteq> Lang P' S"
proof 
  fix w
  assume "w \<in> Lang P S"
  hence "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def uniformize_def by auto 
  thus "w \<in> Lang P' S" 
    using assms slemma5_1 Lang_def by fastforce
qed 

lemma lemma5Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Lang P S \<subseteq> Lang P' S"
proof 
  fix w
  assume "w \<in> Lang P S"
  hence "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def binarizeNt_def by auto 
  thus "w \<in> Lang P' S" 
    using assms slemma5_1Nt Lang_def by fast
qed 

lemma cnf_lemma1: "uniformize A t S P P' \<Longrightarrow> Lang P S = Lang P' S"
  using lemma4 lemma5 by fast

lemma cnf_lemma1Nt: "binarizeNt A B\<^sub>1 B\<^sub>2 S P P' \<Longrightarrow> Lang P S = Lang P' S"
  using lemma4Nt lemma5Nt by fast

lemma uniformizeRtc_Eps_free: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** P P'"
    and "Eps_free P"
  shows "Eps_free P'"
  using assms by (induction rule: rtranclp_induct) (auto simp: uniformize_Eps_free)

lemma binarizeNtRtc_Eps_free:
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** P P'"
    and "Eps_free P"
  shows "Eps_free P'"
  using assms by (induction rule: rtranclp_induct) (auto simp: binarizeNt_Eps_free)

lemma uniformizeRtc_Unit_free: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** P P'"
    and "Unit_free P"
  shows "Unit_free P'"
  using assms by (induction rule: rtranclp_induct) (auto simp: uniformize_Unit_free)

lemma binarizeNtRtc_Unit_free:
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** P P'"
    and "Unit_free P"
  shows "Unit_free P'"
  using assms by (induction rule: rtranclp_induct) (auto simp: binarizeNt_Unit_free)

(* proofs about Nts *)

lemma uniformize_Nts: 
  assumes "uniformize A t S P P'" "S \<in> Nts P"
  shows "S \<in> Nts P'"
proof -
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts P) 
      \<and> P' = ((P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(1) set_removeAll unfolding uniformize_def by fastforce
  thus ?thesis
  proof (cases "S \<in> Nts {(l,r)}")
    case True
    hence "S \<in> Nts {(A,[Tm t]), (l, p@[Nt A]@s)}"
      unfolding Nts_def Nts_syms_def using lrps by auto
    then show ?thesis using  lrps Nts_Un by (metis UnCI)
  next
    case False
    hence "S \<in> Nts (P - {(l,r)})"
      unfolding Nts_def using lrps 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) Nts_Un Nts_def)
    then show ?thesis 
      by (simp add: lrps Nts_def)
  qed
qed  

lemma uniformizeRtc_Nts: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** P P'" "S \<in> Nts P"
  shows "S \<in> Nts P'"
  using assms by (induction rule: rtranclp_induct) (auto simp: uniformize_Nts)

(* Termination *)

theorem cnf_lemma2: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** P P'"
  shows "Lang P S = Lang P' S"
  using assms by (induction rule: rtranclp_induct) (fastforce simp: cnf_lemma1)+ 

theorem cnf_lemma2Nt: 
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** P P'"
  shows "Lang P S = Lang P' S"
  using assms by (induction rule: rtranclp_induct) (fastforce simp: cnf_lemma1Nt)+

theorem cnf_lemma: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** P P'"
    and "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** P' P''"
  shows "Lang P S = Lang P'' S"
  using assms cnf_lemma2 cnf_lemma2Nt uniformizeRtc_Nts by fastforce

lemma lemma6_a:
  assumes "finite P" "uniformize A t S P P'" shows "badTmsCount P' < badTmsCount P"
proof -
  from assms obtain l r p s where lrps: "(l,r) \<in> P" "r = p@[Tm t]@s" "p \<noteq> [] \<or> s \<noteq> []" "A \<notin> Nts P" 
    "P' = P - {(l,r)} \<union> {(A,[Tm t]), (l, p@[Nt A]@s)}"
    unfolding uniformize_def by blast
  hence "prodTms (l,p@[Tm t]@s) = length (filter (isTm) (p@[Tm t]@s))"
    unfolding prodTms_def by auto
  hence 1: "prodTms (l,p@[Tm t]@s) = Suc (length (filter isTm (p@s)))"
    by (simp add: isTm_def)
  have "(A,[Tm t]) \<notin> P \<and> (l, p@[Nt A]@s) \<notin> P"
    using Nts_correct[OF \<open>A \<notin> Nts P\<close>] by fastforce
  then have "badTmsCount P' = badTmsCount (P - {(l,r)}) + badTmsCount {(A,[Tm t]), (l, p@[Nt A]@s)}"
    unfolding badTmsCount.simps \<open>P' = _\<close> by (simp add: assms(1) sum_Un_eq)
  also have "\<dots> = badTmsCount (P - {(l,r)}) + badTmsCount {(A,[Tm t])} + badTmsCount{(l, p@[Nt A]@s)}"
    using Nts_correct[OF  \<open>A \<notin> Nts P\<close>] lrps(1) by auto
  finally have 2: "badTmsCount P' = \<dots>" .
  have 3: "badTmsCount (P - {(l,r)}) < badTmsCount P" using 1 lrps(1,2)
    unfolding badTmsCount.simps by (simp add: assms(1) sum.remove)
  have "prodTms (l, p@[Nt A]@s) = length (filter isTm (p@[Nt A]@s)) \<or> prodTms (l, p@[Nt A]@s) = 0"
    unfolding prodTms_def using lrps by simp
  thus ?thesis
  proof 
    assume "prodTms (l, p@[Nt A]@s) = length (filter isTm (p@[Nt A]@s))"
    hence "badTmsCount P' = badTmsCount (P - {(l,r)}) + prodTms (l, p@[Nt A]@s)"
      using 2 by (simp add: prodTms_def)
    moreover have "prodTms (l,p@[Nt A]@s) < prodTms (l,p@[Tm t]@s)"
      using 1 \<open>prodTms (l, p @ [Nt A] @ s) = length (filter isTm (p @ [Nt A] @ s))\<close> isTm_def by auto 
    ultimately show "badTmsCount P' < badTmsCount P"
      by(simp add: sum.remove[OF assms(1) lrps(1)] \<open>r = _\<close>)
  next 
    assume "prodTms (l, p@[Nt A]@s) = 0"
    hence "badTmsCount P' = badTmsCount (P - {(l,r)})"
      using 2 by (simp add: prodTms_def)
    thus "badTmsCount P' < badTmsCount P" 
      using 3 by simp
  qed
qed

lemma lemma6_b:
  assumes "finite P" "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'" shows "badNtsCount P' < badNtsCount P"
proof -
  from assms(2) obtain l r p s where lrps: "(l,r) \<in> P" "r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" "p \<noteq> [] \<or> s \<noteq> []"
    "A \<notin> Nts P" "P' = P - {(l,r)} \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}"
    unfolding binarizeNt_def by auto
  let ?B12 = "[Nt B\<^sub>1,Nt B\<^sub>2]::('a,'b)syms"
  have "prodNts (l,p@?B12@s) = length (filter isNt (p@?B12@s))"
    using lrps unfolding prodNts_def by auto
  hence 1: "prodNts (l,p@?B12@s) = length (filter isNt (p@s)) + 2"
    by (simp add: isNt_def)
  have "(A,?B12) \<notin> P \<and> (l, p@[Nt A]@s) \<notin> P"
    using Nts_correct[OF \<open>A \<notin> Nts P\<close>] by fastforce
  then have "badNtsCount P' = badNtsCount (P - {(l,r)}) + badNtsCount {(A,?B12), (l, p@[Nt A]@s)}"
    unfolding badTmsCount.simps \<open>P' = _\<close> by (simp add: assms(1) sum_Un_eq)
  also have "\<dots> = badNtsCount (P - {(l,r)}) + badNtsCount {(A,?B12)} + badNtsCount{(l, p@[Nt A]@s)}"
    using Nts_correct[OF  \<open>A \<notin> Nts P\<close>] lrps(1) by simp
  finally have 2: "badNtsCount P' = \<dots>" .
  have 3: "badNtsCount (P - {(l,r)}) < badNtsCount P"
    using sum.remove[OF assms(1) lrps(1), of prodNts] lrps(2) 1 by (simp)
  have "prodNts (l, p@[Nt A]@s) = length (filter isNt (p@[Nt A]@s)) \<or> prodNts (l, p@[Nt A]@s) = 0"
    unfolding prodNts_def using lrps by simp
  thus ?thesis 
  proof 
    assume "prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))"
    hence "badNtsCount P' = badNtsCount (P - {(l,r)}) + badNtsCount {(l, (p@[Nt A]@s))}"
      using 2 by (simp add: prodNts_def)
    moreover have "prodNts (l, p@[Nt A]@s) < prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)"
      using 1 \<open>prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))\<close> isNt_def by simp
    ultimately show ?thesis 
      by(simp add: sum.remove[OF assms(1) lrps(1)] \<open>r = _\<close>)
  next 
    assume "prodNts (l, p@[Nt A]@s) = 0"
    hence "badNtsCount P' = badNtsCount (P - {(l,r)})"
      using 2 by (simp add: prodNts_def)
    thus ?thesis 
      using 3 by simp
  qed
qed

lemma slemma15_a:
  assumes "finite P" and "badTmsCount P = 0" "binarizeNt A B\<^sub>1 B\<^sub>2 S P P'"
  shows "finite P' \<and> badTmsCount P' = 0"
proof -
  from assms(3) obtain l r p s where lrps: "(l,r) \<in> P" "r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" "p \<noteq> [] \<or> s \<noteq> []"
    "A \<notin> Nts P" "P' = P - {(l,r)} \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}"
    unfolding binarizeNt_def by auto
  let ?B12 = "[Nt B\<^sub>1,Nt B\<^sub>2]::('a,'b)syms"
  have "(A,?B12) \<notin> P \<and> (l, p@[Nt A]@s) \<notin> P"
    using Nts_correct[OF \<open>A \<notin> Nts P\<close>] by fastforce
  then have "badTmsCount P' = badTmsCount (P - {(l,r)}) + badTmsCount {(A,?B12), (l, p@[Nt A]@s)}"
    unfolding badTmsCount.simps \<open>P' = _\<close> by (simp add: assms(1) sum_Un_eq)
  also have "\<dots> = badTmsCount (P - {(l,r)}) + badTmsCount{(l, p@[Nt A]@s)}"
    using Nts_correct[OF  \<open>A \<notin> Nts P\<close>] lrps(1) by (simp add: prodTms_def)
  finally have "badTmsCount P' = \<dots>" .
  moreover have "badTmsCount (P - {(l,r)}) = 0" using assms(2)
    by (simp add: sum_diff1_nat)
  moreover have "badTmsCount {(l, (p@[Nt A]@s))} = 0" 
  proof -
    have "prodTms (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = 0"
      using lrps(1,2) assms(1,2) badTmsCountSet by blast
    thus "badTmsCount {(l, (p@[Nt A]@s))} = 0"
      by (auto simp: isTm_def prodTms_def)
  qed
  ultimately show ?thesis
    using assms(1) lrps(5) by auto
qed

lemma lemma15_a:
  assumes "finite P" and "badTmsCount P = 0"
  and "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** P P'"
  shows "finite P' \<and> badTmsCount P' = 0"
  using assms(3) by (induction)(auto intro: assms(1,2) dest: slemma15_a simp del: badTmsCount.simps)
                                                        
lemma noTms_prodTms0:
  assumes "prodTms (l,r) = 0"
  shows "length r \<le> 1 \<or> (\<forall>a \<in> set r. isNt a)"
proof -
  have "length r \<le> 1 \<or> (\<nexists>a. a \<in> set r \<and> isTm a)"
    using assms unfolding prodTms_def using empty_filter_conv by fastforce
  thus ?thesis 
    by (metis isNt_def isTm_def sym.exhaust)
qed

lemma badTmsCountNot0:
  assumes "finite P" "badTmsCount P > 0"
  shows "\<exists>l r t. (l,r) \<in> P \<and> length r \<ge> 2 \<and> Tm t \<in> set r"
proof -
  have "\<exists>p \<in> P. prodTms p > 0"
    using assms badTmsCountSet not_gr0 by blast
  from this obtain l r where lr: "(l, r) \<in> P \<and> prodTms (l,r) > 0"
    by auto
  hence 1: "length r \<ge> 2"
    unfolding prodTms_def using not_le_imp_less by fastforce
  hence "prodTms (l,r) = length (filter (isTm) r)"
    unfolding prodTms_def by simp
  hence "\<exists>t. Tm t \<in> set r"
    by (metis lr empty_filter_conv isTm_def length_greater_0_conv)
  thus ?thesis using lr 1 by blast
qed

lemma badNtsCountNot0: 
  assumes "finite P" "badNtsCount P > 0" 
  shows "\<exists>l r. (l, r) \<in> P \<and> length r \<ge> 3"
proof -
  have "\<exists>p \<in> P. prodNts p > 0"
    using assms badNtsCountSet not_gr0 by blast
  from this obtain l r where lr: "(l, r) \<in> P \<and> prodNts (l,r) > 0"
    by auto
  hence "length r \<ge> 3"
    unfolding prodNts_def using not_le_imp_less by fastforce
  thus ?thesis using lr by auto
qed

lemma list_longer2: "length l \<ge> 2 \<and> x \<in> set l \<Longrightarrow> (\<exists>hd tl . l = hd@[x]@tl \<and> (hd \<noteq> [] \<or> tl \<noteq> []))"
  using split_list_last by fastforce 

lemma list_longer3: "length l \<ge> 3 \<Longrightarrow> (\<exists>hd tl x y. l = hd@[x]@[y]@tl \<and> (hd \<noteq> [] \<or> tl \<noteq> []))"
  by (metis Suc_le_length_iff append.left_neutral append_Cons neq_Nil_conv numeral_3_eq_3)

lemma lemma8_a:
assumes "finite P" "badTmsCount P > 0" shows "\<exists>P' A t. uniformize A t S P P' \<and> finite P'"
proof -
  obtain A where A: "A \<notin> Nts P \<union> {S}" using ex_new_if_finite[OF infinite_UNIV] finite_Nts[OF assms(1)]
    by blast
  then obtain l r t where lr: "(l,r) \<in> P \<and> length r \<ge> 2 \<and> Tm t \<in> set r"
    using assms badTmsCountNot0 by blast
  then obtain p s where ps: "r = p@[Tm t]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])"
    unfolding isTm_def using lr list_longer2[of r] by blast
  from this obtain P' where "P' = P - {(l, r)} \<union> {(A, [Tm t]), (l, p @ [Nt A] @ s)}" 
    by auto
  hence "uniformize A t S P P'"
    unfolding uniformize_def using lr ps A by auto
  thus ?thesis unfolding \<open>P' = _\<close> using assms(1) by blast
qed

lemma lemma8_b:
  assumes "finite P" "badTmsCount P = 0" and "badNtsCount P > 0"
  shows "\<exists>P' A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S P P' \<and> finite P'"
proof -
  obtain l r where lr: "(l, r) \<in> P \<and> length r \<ge> 3"
    using assms(1,3) badNtsCountNot0 by blast
  obtain A where A: "A \<notin> Nts P \<union> {S}" using ex_new_if_finite[OF infinite_UNIV] finite_Nts[OF assms(1)]
    by blast
  obtain p s X Y where psXY: "r = p@[X]@[Y]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])"
    using lr list_longer3[of r] by blast
  have "\<forall>a \<in> set r. isNt a"
    using lr assms(1,2) badTmsCountSet[of P] noTms_prodTms0[of l r] by fastforce
  from this obtain B\<^sub>1 B\<^sub>2 where "X = Nt B\<^sub>1 \<and> Y = Nt B\<^sub>2"
    using isNt_def psXY by fastforce
  hence B: "(r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> [])"
    using psXY by auto
  hence "binarizeNt A B\<^sub>1 B\<^sub>2 S P (P - {(l,r)} \<union> {(A, [Nt B\<^sub>1, Nt B\<^sub>2]), (l, p @ [Nt A] @ s)})"
    unfolding binarizeNt_def using A lr B by auto
  thus ?thesis using assms(1) by blast
qed

lemma uniformize_2:
  "finite P \<Longrightarrow> \<exists>P'. (\<lambda>x y. \<exists>A t. uniformize A t S x y)^** P P' \<and> finite P' \<and> badTmsCount P' = 0"
proof (induction "badTmsCount P" arbitrary: P rule: less_induct)
  case less
  then show ?case
  proof (cases "badTmsCount P = 0")
    case True then show ?thesis using less.prems by blast
  next
    case False
    from this obtain P' A t where g': "uniformize A t S P P' \<and> finite P'"
      using lemma8_a[OF less.prems] by blast
    hence "badTmsCount P' < badTmsCount P"
      using lemma6_a[of _ A t, OF less.prems] by blast
    from this obtain P'' where "(\<lambda>x y. \<exists>A t. uniformize A t S x y)\<^sup>*\<^sup>* P' P'' \<and> finite P'' \<and> badTmsCount P'' = 0"
      using less
      using g' by blast
    thus ?thesis 
      using g' converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A t. uniformize A t S x y)" P P' P''] by blast
  qed
qed

lemma binarizeNt_2: 
  assumes "finite P" "badTmsCount P = 0"
    shows "\<exists>P'. (\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** P P' \<and> finite P' \<and> badNtsCount P' = 0"
using assms proof (induction "badNtsCount P" arbitrary: P rule: less_induct)
  case less
  then show ?case 
  proof (cases "badNtsCount P = 0")
    case True thus ?thesis using less.prems(1) by blast
  next
    case False
    from this obtain P' A B\<^sub>1 B\<^sub>2 where g': "binarizeNt A B\<^sub>1 B\<^sub>2 S P P' \<and> finite P'"
      using assms lemma8_b[OF less.prems] by blast
    hence "badNtsCount P' < badNtsCount P"
      using lemma6_b[OF less.prems(1)] by blast
    from this obtain P'' where "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* P' P'' \<and> finite P'' \<and> badNtsCount P'' = 0"
      using less slemma15_a[of P A B\<^sub>1 B\<^sub>2 S P'] g' by blast
    then show ?thesis 
      using g' converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)" P P' P''] by blast
  qed
qed

theorem cnf_noe_nou:  fixes P :: "('n::infinite,'t)Prods"
  assumes "finite P" "Eps_free P" and "Unit_free P"
  shows "\<exists>P'::('n,'t)Prods. finite P' \<and> uniform P' \<and> binary P' \<and> Lang P S = Lang P' S \<and> Eps_free P' \<and> Unit_free P'"
proof -
  obtain P' where g': "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** P P' \<and> finite P' \<and> badTmsCount P' = 0 \<and> Eps_free P' \<and> Unit_free P'"
    using assms uniformize_2 uniformizeRtc_Eps_free uniformizeRtc_Unit_free
    by (metis (mono_tags, lifting))
  obtain P'' where g'': "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** P' P'' \<and> finite P'' \<and> badNtsCount P'' = 0 \<and> badTmsCount P'' = 0"
    using g' binarizeNt_2 lemma15_a by blast
  hence "uniform P'' \<and> binary P'' \<and> Eps_free P'' \<and> Unit_free P''"
    using g' count_bin_un binarizeNtRtc_Eps_free binarizeNtRtc_Unit_free by fastforce
  moreover have "Lang P S = Lang P'' S"
    using g' g'' cnf_lemma by blast
  ultimately show ?thesis using g'' by blast
qed

text \<open>Alternative form more similar to the one Jana Hofmann used:\<close>

lemma CNF_eq: "CNF P \<longleftrightarrow> (uniform P \<and> binary P \<and> Eps_free P \<and> Unit_free P)"
proof 
  assume "CNF P"
  hence "Eps_free P"
    unfolding CNF_def Eps_free_def by fastforce
  moreover have "Unit_free P"
    using \<open>CNF P\<close> unfolding CNF_def Unit_free_def isNt_def isTm_def by fastforce
  moreover have "uniform P"
  proof -
    have "\<forall>(A,\<alpha>) \<in> P. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t])"
      using \<open>CNF P\<close> unfolding CNF_def.
    hence "\<forall>(A, \<alpha>) \<in> P. (\<forall>N \<in> set \<alpha>. isNt N) \<or> (\<exists>t. \<alpha> = [Tm t])"
      unfolding isNt_def by fastforce
    hence "\<forall>(A, \<alpha>) \<in> P. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"
      by (auto simp: isNt_def)
    thus "uniform P"
      unfolding uniform_def.
  qed
  moreover have "binary P"
    using \<open>CNF P\<close> unfolding binary_def CNF_def by auto
  ultimately show "uniform P \<and> binary P \<and> Eps_free P \<and> Unit_free P"
    by blast
next 
  assume assm: "uniform P \<and> binary P \<and> Eps_free P \<and> Unit_free P"
  have"\<forall>p \<in> P. (\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. (snd p) = [Tm t])"
  proof
    fix p assume "p \<in> P"
    obtain A \<alpha> where A\<alpha>: "(A, \<alpha>) = p"
      by (metis prod.exhaust_sel)
    hence "length \<alpha> = 1 \<or> length \<alpha> = 2"
      using assm \<open>p \<in> P\<close> order_neq_le_trans unfolding binary_def Eps_free_def by fastforce
    hence "(\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t])"
    proof 
      assume "length \<alpha> = 1"
      hence "\<exists>S. \<alpha> = [S]"
        by (simp add: length_Suc_conv)
      moreover have "\<nexists>N. \<alpha> = [Nt N]"
        using assm A\<alpha> \<open>p \<in> P\<close> unfolding Unit_free_def by blast
      ultimately show ?thesis by (metis sym.exhaust)
    next
      assume "length \<alpha> = 2"
      obtain B C where BC: "\<alpha> = [B, C]"
        using \<open>length \<alpha> = 2\<close> by (metis One_nat_def Suc_1 diff_Suc_1 length_0_conv length_Cons neq_Nil_conv)
      have "(\<nexists>t. Tm t \<in> set \<alpha>)"
        using \<open>length \<alpha> = 2\<close> assm A\<alpha> \<open>p \<in> P\<close> unfolding uniform_def by auto
      hence "(\<forall>N \<in> set \<alpha>. \<exists>A. N = Nt A)"
        by (metis sym.exhaust)
      hence "\<exists>B' C'. B = Nt B' \<and> C = Nt C'" 
        using BC by simp
      thus ?thesis using A\<alpha> BC by auto
    qed
    thus "(\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. (snd p) = [Tm t])" using A\<alpha> by auto
  qed
  thus "CNF P" by (auto simp: CNF_def)
qed

text \<open>Main Theorem: existence of CNF with the same language except for the empty word \<open>[]\<close>:\<close>

theorem cnf_exists:
  fixes P :: "('n::infinite,'t) Prods"
  assumes "finite P"
  shows "\<exists>P'::('n,'t)Prods. finite P' \<and> CNF P' \<and> Lang P' S = Lang P S - {[]}"
proof -
  let ?P\<^sub>0 = "Eps_elim P"
  note fin0 = finite_Eps_elim[OF assms]
  obtain P\<^sub>u where P\<^sub>u: "unit_elim_rel ?P\<^sub>0 P\<^sub>u \<and> finite P\<^sub>u"
    using unit_elim_rel_exists finite_Eps_elim[OF assms] by blast
  hence 1: "Eps_free P\<^sub>u \<and> Unit_free P\<^sub>u"
    using P\<^sub>u Eps_free_Eps_elim Unit_free_if_unit_elim_rel unit_elim_rel_Eps_free by fastforce
  have 2: "Lang P\<^sub>u S = Lang P S - {[]}"
    using P\<^sub>u Lang_Eps_elim unit_elim_rel_Lang_eq by metis
  obtain P'::"('n,'t)Prods" where g': "finite P' \<and> uniform P' \<and> binary P' \<and> Lang P\<^sub>u S = Lang P' S \<and> Eps_free P' \<and> Unit_free P'"
    using 1 cnf_noe_nou P\<^sub>u by blast
  hence "CNF P'" 
    using g' CNF_eq by blast
  moreover have "Lang P' S = Lang P S - {[]}"
    using 2 g' by blast
  ultimately show ?thesis using g' by blast
qed


text \<open>Some helpful properties:\<close>

lemma cnf_length_derive: 
  assumes "CNF P" "P \<turnstile> [Nt S] \<Rightarrow>* \<alpha>"
  shows "length \<alpha> \<ge> 1"
  using assms CNF_eq Eps_free_derives_Nil length_greater_0_conv less_eq_Suc_le by auto

lemma cnf_length_derive2: 
  assumes "CNF P" "P \<turnstile> [Nt A, Nt B] \<Rightarrow>* \<alpha>"
  shows "length \<alpha> \<ge> 2"
proof -
  obtain u v where uv: "P \<turnstile> [Nt A] \<Rightarrow>* u \<and> P \<turnstile> [Nt B] \<Rightarrow>* v \<and> \<alpha> = u @ v"
    using assms(2) derives_append_decomp[of P \<open>[Nt A]\<close> \<open>[Nt B]\<close> \<alpha>] by auto
  hence "length u \<ge> 1 \<and> length v \<ge> 1" 
    using cnf_length_derive[OF assms(1)] by blast
  thus ?thesis
    using uv by simp
qed

lemma cnf_single_derive:
  assumes "CNF P" "P \<turnstile> [Nt S] \<Rightarrow>* [Tm t]"
  shows "(S, [Tm t]) \<in> P"
proof -
  obtain \<alpha> where \<alpha>: "P \<turnstile> [Nt S] \<Rightarrow> \<alpha> \<and> P \<turnstile> \<alpha> \<Rightarrow>* [Tm t]"
    using converse_rtranclpE[OF assms(2)] by auto
  hence 1: "(S, \<alpha>) \<in> P" 
    by (simp add: derive_singleton)
  have "\<nexists>A B. \<alpha> = [Nt A, Nt B]"
  proof (rule ccontr)
    assume "\<not> (\<nexists>A B. \<alpha> = [Nt A, Nt B])"
    from this obtain A B where AB: "\<alpha> = [Nt A, Nt B]"
      by blast
    have "\<forall>w. P \<turnstile> [Nt A, Nt B] \<Rightarrow>* w \<longrightarrow> length w \<ge> 2"
      using cnf_length_derive2[OF assms(1)] by simp
    moreover have "length [Tm t] = 1"
      by simp
    ultimately show False
      using \<alpha> AB by auto
  qed
  from this obtain a where "\<alpha> = [Tm a]"
    using 1 assms(1) unfolding CNF_def by auto
  hence "t = a"
    using \<alpha> by (simp add: derives_Tm_Cons)
  thus ?thesis 
    using 1 \<open>\<alpha> = [Tm a]\<close> by blast
qed

lemma cnf_word:
  assumes "CNF P" "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    and "length w \<ge> 2"
  shows "\<exists>A B u v. (S, [Nt A, Nt B]) \<in> P \<and> P \<turnstile> [Nt A] \<Rightarrow>* map Tm u \<and> P \<turnstile> [Nt B] \<Rightarrow>* map Tm v \<and> u@v = w \<and> u \<noteq> [] \<and> v \<noteq> []"
proof -
  have 1: "(S, map Tm w) \<notin> P"
    using assms(1) assms(3) unfolding CNF_def by auto
  have "\<exists>\<alpha>. P \<turnstile> [Nt S] \<Rightarrow> \<alpha> \<and> P \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
    using converse_rtranclpE[OF assms(2)] by auto
  from this obtain \<alpha> where \<alpha>: "(S, \<alpha>) \<in> P \<and> P \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
    by (auto simp: derive_singleton)
  hence "(\<nexists>t. \<alpha> = [Tm t])"
    using 1 derives_Tm_Cons[of P] derives_from_empty by auto
  hence "\<exists>A B. P \<turnstile> [Nt S] \<Rightarrow> [Nt A, Nt B] \<and> P \<turnstile> [Nt A, Nt B] \<Rightarrow>* map Tm w"
    using assms(1) \<alpha> derive_singleton[of P \<open>Nt S\<close> \<alpha>] unfolding CNF_def by fast
  from this obtain A B where AB: "(S, [Nt A, Nt B]) \<in> P \<and> P \<turnstile> [Nt A, Nt B] \<Rightarrow>* map Tm w"
    using derive_singleton[of P \<open>Nt S\<close>] by blast
  hence "\<not>(P \<turnstile> [Nt A] \<Rightarrow>* []) \<and> \<not>(P \<turnstile> [Nt B] \<Rightarrow>* [])"
    using assms(1) CNF_eq Eps_free_derives_Nil by blast
  from this obtain u v where uv: "P \<turnstile> [Nt A] \<Rightarrow>* u \<and> P \<turnstile> [Nt B] \<Rightarrow>* v \<and> u@v = map Tm w \<and> u \<noteq> [] \<and> v \<noteq> []"
    using AB derives_append_decomp[of P \<open>[Nt A]\<close> \<open>[Nt B]\<close> \<open>map Tm w\<close>] by force
  moreover have "\<exists>u' v'. u = map Tm u' \<and> v = map Tm v'"
    using uv map_eq_append_conv[of Tm w u v] by auto
  ultimately show ?thesis
    using AB append_eq_map_conv[of u v Tm w] list.simps(8)[of Tm] by fastforce
qed

end