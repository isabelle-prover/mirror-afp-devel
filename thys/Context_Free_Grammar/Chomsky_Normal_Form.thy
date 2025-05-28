(*
Authors: August Martin Stimpfle, Tobias Nipkow
Based on HOL4 theories by Aditi Barthwal
*)

section \<open>Conversion to Chomsky Normal Form\<close>

theory Chomsky_Normal_Form
imports Unit_Elimination Epsilon_Elimination
begin

definition CNF :: "('n, 't) Prods \<Rightarrow> bool" where
"CNF P \<equiv> (\<forall>(A,\<alpha>) \<in> P. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t]))"

lemma Nts_correct: "A \<notin> Nts P \<Longrightarrow> (\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>))"
unfolding Nts_def nts_syms_def by auto

(* Chomsky Normal Form *)

definition uniformize :: "'n::infinite \<Rightarrow> 't \<Rightarrow> 'n \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t) prods \<Rightarrow> bool" where 
      "uniformize A t S ps ps' \<equiv> (
    \<exists> l r p s. (l,r) \<in> set ps \<and> (r = p@[Tm t]@s) 
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> A = fresh(nts ps \<union> {S})
    \<and> ps' = ((removeAll (l,r) ps) @ [(A,[Tm t]), (l, p@[Nt A]@s)]))"

lemma uniformize_Eps_free:
  assumes "Eps_free (set ps)"
    and "uniformize A t S ps ps'"
  shows "Eps_free (set ps')"
  using assms unfolding uniformize_def Eps_free_def by force

lemma uniformize_Unit_free:
  assumes "Unit_free (set ps)"
    and "uniformize A t S ps ps'"
  shows "Unit_free (set ps')"
proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set ps))"
    using assms(1) unfolding Unit_free_def by simp
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> set ps' = ((set ps - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(2) set_removeAll unfolding uniformize_def by force
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A,[Tm t]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set ps - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set ps' = ((set ps - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using lrps by simp
  ultimately show ?thesis unfolding Unit_free_def by simp
qed

definition prodTms :: "('n,'t) prod \<Rightarrow> nat" where
"prodTms p \<equiv> (if length (snd p) \<le> 1 then 0 else length (filter (isTm) (snd p)))"

definition prodNts :: "('n,'t) prod \<Rightarrow> nat" where
"prodNts p \<equiv> (if length (snd p) \<le> 2 then 0 else length (filter (isNt) (snd p)))"

(* This definition can be reduced to badTmsCount ps \<equiv> fold (+) (map prodTms ps) 0. 
   However, the proofs turned out to be much nicer with this version  *)
fun badTmsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badTmsCount ps = sum_list(map prodTms ps)"

lemma badTmsCountSet: "(\<forall>p \<in> set ps. prodTms p = 0) \<longleftrightarrow> badTmsCount ps = 0"
by auto

fun badNtsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badNtsCount ps = sum_list(map prodNts ps)"

lemma badNtsCountSet: "(\<forall>p \<in> set ps. prodNts p = 0) \<longleftrightarrow> badNtsCount ps = 0"
  by auto

definition uniform :: "('n, 't) Prods \<Rightarrow> bool" where
  "uniform P \<equiv> \<forall>(A, \<alpha>) \<in> P. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"

lemma uniform_badTmsCount: 
  "uniform (set ps) \<longleftrightarrow> badTmsCount ps = 0"
proof 
  assume assm: "uniform (set ps)"
  have "\<forall>p \<in> set ps. prodTms p = 0"
  proof 
    fix p assume "p \<in> set ps"
    hence "(\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t])"
      using assm unfolding uniform_def by auto
    hence "length (snd p) \<le> 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      by auto
    hence "length (snd p) \<le> 1 \<or> length (filter (isTm) (snd p)) = 0"
      unfolding isTm_def by (auto simp: filter_empty_conv)
    thus "prodTms p = 0"
      unfolding prodTms_def by argo
   qed
   thus "badTmsCount ps = 0"
     using badTmsCountSet by blast
next 
  assume assm: "badTmsCount ps = 0"
  have "\<forall>p \<in> set ps. ((\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t]))"
  proof 
    fix p assume "p \<in> set ps"
    hence "prodTms p = 0"
      using assm badTmsCountSet by blast
    hence "length (snd p) \<le> 1 \<or> length (filter (isTm) (snd p)) = 0"
      unfolding prodTms_def by argo
    hence "length (snd p) \<le> 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      by (auto simp: isTm_def filter_empty_conv)
    hence "length (snd p) = 0 \<or> length (snd p) = 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      using order_neq_le_trans by blast
    thus "(\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t])"
      by (auto simp: length_Suc_conv)
  qed
  thus "uniform (set ps)"
    unfolding uniform_def by auto
qed

definition binary :: "('n, 't) Prods \<Rightarrow> bool" where
  "binary P \<equiv> \<forall>(A, \<alpha>) \<in> P. length \<alpha> \<le> 2"

lemma binary_badNtsCount:
  assumes "uniform (set ps)" "badNtsCount ps = 0"
  shows "binary (set ps)"
proof -
  have "\<forall>p \<in> set ps. length (snd p) \<le> 2"
  proof 
    fix p assume assm: "p \<in> set ps"
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

lemma count_bin_un: "(binary (set ps) \<and> uniform (set ps)) \<longleftrightarrow> (badTmsCount ps = 0 \<and> badNtsCount ps = 0)"
proof 
  assume "binary (set ps) \<and> uniform (set ps)"
  hence "badTmsCount ps = 0 \<and> (\<forall>(A, \<alpha>) \<in> set ps. length \<alpha> \<le> 2)"
    unfolding binary_def using uniform_badTmsCount by blast
  thus "badTmsCount ps = 0 \<and> badNtsCount ps = 0"
    by (metis badNtsCountSet case_prodE prod.sel(2) prodNts_def)
next
  assume "badTmsCount ps = 0 \<and> badNtsCount ps = 0"
  thus "binary (set ps) \<and> uniform (set ps)"
    using binary_badNtsCount uniform_badTmsCount by blast 
qed


definition binarizeNt :: "'n::infinite \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods \<Rightarrow> bool" where
"binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps' \<equiv> (
    \<exists>l r p s. (l,r) \<in> set ps \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A = fresh(nts ps \<union> {S}))
    \<and> ps' = ((removeAll (l,r) ps) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)]))"

lemma binarizeNt_Eps_free:
  assumes "Eps_free (set ps)"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
  shows "Eps_free (set ps')"
  using assms unfolding binarizeNt_def Eps_free_def by force

lemma binarizeNt_Unit_free:
  assumes "Unit_free (set ps)"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
  shows "Unit_free (set ps')"
  proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set ps))"
    using assms(1) unfolding Unit_free_def by simp
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> (set ps' = ((set ps - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(2) set_removeAll unfolding binarizeNt_def by force
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set ps - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set ps' = ((set ps - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using lrps by simp
  ultimately show ?thesis unfolding Unit_free_def by simp
qed

lemma fresh_nts_single: "fresh(nts ps \<union> {S}) \<notin> nts ps \<union> {S}"
by(rule fresh_finite) (simp add: finite_nts)

lemma binarizeNt_aux1:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
  shows "A \<noteq> B\<^sub>1 \<and> A \<noteq> B\<^sub>2"
using assms fresh_nts_single unfolding binarizeNt_def Nts_def nts_syms_def by fastforce

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
  assumes "uniformize A t S ps ps'"
    and "set ps \<turnstile> lhs \<Rightarrow> rhs"
  shows "set ps' \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' B v where Bv: "lhs = p'@[Nt B]@s' \<and> rhs = p'@v@s' \<and> (B,v) \<in> set ps"
    using derive.cases[OF assms(2)] by fastforce
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps))
      \<and> set ps' = ((set ps - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(1) set_removeAll fresh_nts_single[of ps S] unfolding uniformize_def by fastforce
  thus ?thesis
  proof (cases "(B, v) \<in> set ps'")
    case True
    then show ?thesis
      using derive.intros[of B v] Bv by blast
  next
    case False
    hence "B = l \<and> v = p@[Tm t]@s"
      by (simp add: lrps Bv) 
    have 1: "set ps' \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
      using lrps by (simp add: derive_singleton)
    have "set ps' \<turnstile> [Nt A] \<Rightarrow> [Tm t]"
      using lrps by (simp add: derive_singleton)
    hence "set ps' \<turnstile> [Nt l] \<Rightarrow>* p@[Tm t]@s"
      using 1 derives_sub[of \<open>set ps'\<close>] by blast
    then show ?thesis 
      using False \<open>B = l \<and> v = p@[Tm t]@s\<close> Bv derives_append derives_prepend by blast
  qed
qed

lemma cnf_r1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
    and "set ps \<turnstile> lhs \<Rightarrow> rhs"
  shows "set ps' \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' C v where Cv: "lhs = p'@[Nt C]@s' \<and> rhs = p'@v@s' \<and> (C,v) \<in> set ps"
    using derive.cases[OF assms(2)] by fastforce
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps))
    \<and> (set ps' = ((set ps - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(1) set_removeAll fresh_nts_single[of ps S] unfolding binarizeNt_def by fastforce
  thus ?thesis
  proof (cases "(C, v) \<in> set ps'")
    case True
    then show ?thesis
      using derive.intros[of C v] Cv by blast
  next
    case False
    hence "C = l \<and> v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s"
      by (simp add: lrps Cv)
    have 1: "set ps' \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
      using lrps by (simp add: derive_singleton)
    have "set ps' \<turnstile> [Nt A] \<Rightarrow> [Nt B\<^sub>1,Nt B\<^sub>2]"
      using lrps by (simp add: derive_singleton)
    hence "set ps' \<turnstile> [Nt l] \<Rightarrow>* p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" 
      using 1 derives_sub[of \<open>set ps'\<close>] by blast
    thus ?thesis 
      using False \<open>C = l \<and> v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s\<close> Cv derives_append derives_prepend by blast
  qed
qed

lemma slemma1_1: 
  assumes "uniformize A t S ps ps'"
    and "(A, \<alpha>) \<in> set ps'"
  shows "\<alpha> = [Tm t]"
proof -
  have "A \<notin> Nts (set ps)"
    using assms(1) fresh_nts_single unfolding uniformize_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set ps"
    unfolding Nts_def by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Tm t] \<and> (A, \<alpha>) \<in> set ps'"
    using assms(1) unfolding uniformize_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma1_1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
    and "(A, \<alpha>) \<in> set ps'"
  shows "\<alpha> = [Nt B\<^sub>1,Nt B\<^sub>2]"
proof -
  have "A \<notin> Nts (set ps)"
    using assms(1) fresh_nts_single unfolding binarizeNt_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set ps"
    unfolding Nts_def  by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Nt B\<^sub>1,Nt B\<^sub>2] \<and> (A, \<alpha>) \<in> set ps'"
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
  assumes "uniformize A t S ps ps'"
    and "(l,r) \<in> set ps"
  shows "Nt A \<notin> set r"
proof -
  have "A \<notin> Nts (set ps)"
    using assms(1) fresh_nts_single unfolding uniformize_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set ps \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>set ps\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
    and "(l,r) \<in> set ps"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> Nts (set ps)"
    using assms(1) fresh_nts_single unfolding binarizeNt_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set ps \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>set ps\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed


lemma lemma1:
  assumes "uniformize A t S ps ps'"
    and "set ps' \<turnstile> lhs \<Rightarrow> rhs"
  shows "substsNt A [Tm t] lhs = substsNt A [Tm t] rhs
    \<or> set ps \<turnstile> substsNt A [Tm t] lhs \<Rightarrow> substsNt A [Tm t] rhs"
proof -
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps)) 
      \<and> set ps' = ((set ps - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(1) set_removeAll fresh_nts_single[of ps S] unfolding uniformize_def by fastforce
  obtain p' s' u v where uv: "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set ps'"
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
      hence 2: "(u, substsNt A [Tm t] v) \<in> set ps" using lrps
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
      hence 1: "(u, v) \<in> set ps" 
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
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
    and "set ps' \<turnstile> lhs \<Rightarrow> rhs"
  shows "(substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs) 
          \<or> ((set ps) \<turnstile> (substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs) \<Rightarrow> substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs)"
proof -
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps))
    \<and> (set ps' = ((set ps - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(1) set_removeAll fresh_nts_single[of ps S] unfolding binarizeNt_def by fastforce
  obtain p' s' u v where uv: "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set ps'"
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
        using assms(1) binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 S ps ps'] by auto 
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
        using True lrps uv assms slemma4_4Nt[of A B\<^sub>1 B\<^sub>2 S ps ps'] binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 S ps ps'] by auto
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] ([Nt A]@s)"
        by simp
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v = p @ [Nt B\<^sub>1,Nt B\<^sub>2] @ s"
        using 1 substs_append slemma4_1 slemma4_3_1 by metis
      hence 2: "(u, substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v) \<in> set ps" 
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
      hence 1: "(u, v) \<in> set ps" 
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
  assumes "set ps' \<turnstile> lhs \<Rightarrow>* rhs"
    and "uniformize A t S ps ps'"
  shows "set ps \<turnstile> substsNt A [Tm t] lhs \<Rightarrow>* substsNt A [Tm t] rhs"
  using assms
proof (induction rhs rule: rtranclp_induct)
  case (step y z)
  then show ?case 
    using lemma1[of A t S ps ps' y z] by auto 
qed simp

lemma lemma3Nt:
  assumes "set ps' \<turnstile> lhs \<Rightarrow>* rhs"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
  shows "set ps \<turnstile> substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] lhs \<Rightarrow>* substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] rhs"
  using assms 
proof (induction rhs rule: rtranclp_induct)
  case (step y z)
  then show ?case 
    using lemma1Nt[of A B\<^sub>1 B\<^sub>2 S ps ps' y z] by auto
qed simp

lemma lemma4:
  assumes "uniformize A t S ps ps'" 
  shows "lang ps' S \<subseteq> lang ps S"
proof 
  fix w
  assume "w \<in> lang ps' S"
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    unfolding Lang_def by simp
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding uniformize_def by auto
  hence "set ps \<turnstile> substsNt A [Tm t] [Nt S] \<Rightarrow>* substsNt A [Tm t] (map Tm w)"
    using assms lemma3[of ps' \<open>[Nt S]\<close> \<open>map Tm w\<close>] by blast
  moreover have "substsNt A [Tm t] [Nt S] = [Nt S]"
    using assms fresh_nts_single[of ps S] unfolding uniformize_def by auto
  moreover have "substsNt A [Tm t] (map Tm w) = map Tm w" 
    by simp
  ultimately show "w \<in> lang ps S" 
    by (simp add: Lang_def)
qed

lemma lemma4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
  shows "lang ps' S \<subseteq> lang ps S"
proof
  fix w
  assume "w \<in> lang ps' S"
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    by (simp add: Lang_def)
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding binarizeNt_def by auto
  hence "set ps \<turnstile> substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] [Nt S] \<Rightarrow>*  substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] (map Tm w)"
    using assms lemma3Nt[of ps' \<open>[Nt S]\<close> \<open>map Tm w\<close>] by blast
  moreover have "substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] [Nt S] = [Nt S]"
    using assms fresh_nts_single[of ps S] unfolding binarizeNt_def by auto
  moreover have "substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] (map Tm w) = map Tm w" by simp
  ultimately show "w \<in> lang ps S" using Lang_def
    by (metis (no_types, lifting) mem_Collect_eq)
qed

lemma slemma5_1:
  assumes "set ps \<turnstile> u \<Rightarrow>* v"
    and "uniformize A t S ps ps'"
  shows "set ps' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction v rule: rtranclp_induct) (auto simp: cnf_r1Tm rtranclp_trans)

lemma slemma5_1Nt:
  assumes "set ps \<turnstile> u \<Rightarrow>* v"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
  shows "set ps' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction v rule: rtranclp_induct) (auto simp: cnf_r1Nt rtranclp_trans)

lemma lemma5: 
  assumes "uniformize A t S ps ps'"
  shows "lang ps S \<subseteq> lang ps' S"
proof 
  fix w
  assume "w \<in> lang ps S"
  hence "set ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def uniformize_def by auto 
  thus "w \<in> lang ps' S" 
    using assms slemma5_1 Lang_def by fastforce
qed 

lemma lemma5Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
  shows "lang ps S \<subseteq> lang ps' S"
proof 
  fix w
  assume "w \<in> lang ps S"
  hence "set ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def binarizeNt_def by auto 
  thus "w \<in> lang ps' S" 
    using assms slemma5_1Nt Lang_def by fast
qed 

lemma cnf_lemma1: "uniformize A t S ps ps' \<Longrightarrow> lang ps S = lang ps' S"
  using lemma4 lemma5 by fast

lemma cnf_lemma1Nt: "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps' \<Longrightarrow> lang ps S = lang ps' S"
  using lemma4Nt lemma5Nt by fast

lemma uniformizeRtc_Eps_free: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps ps'"
    and "Eps_free (set ps)"
  shows "Eps_free (set ps')"
  using assms by (induction rule: rtranclp_induct) (auto simp: uniformize_Eps_free)

lemma binarizeNtRtc_Eps_free:
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** ps ps'"
    and "Eps_free (set ps)"
  shows "Eps_free (set ps')"
  using assms by (induction rule: rtranclp_induct) (auto simp: binarizeNt_Eps_free)

lemma uniformizeRtc_Unit_free: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps ps'"
    and "Unit_free (set ps)"
  shows "Unit_free (set ps')"
  using assms by (induction rule: rtranclp_induct) (auto simp: uniformize_Unit_free)

lemma binarizeNtRtc_Unit_free:
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** ps ps'"
    and "Unit_free (set ps)"
  shows "Unit_free (set ps')"
  using assms by (induction rule: rtranclp_induct) (auto simp: binarizeNt_Unit_free)

(* proofs about Nts *)

lemma uniformize_Nts: 
  assumes "uniformize A t S ps ps'" "S \<in> Nts (set ps)"
  shows "S \<in> Nts (set ps')"
proof -
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps)) 
      \<and> set ps' = ((set ps - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using assms(1) set_removeAll fresh_nts_single[of ps S] unfolding uniformize_def by fastforce
  thus ?thesis
  proof (cases "S \<in> Nts {(l,r)}")
    case True
    hence "S \<in> Nts {(A,[Tm t]), (l, p@[Nt A]@s)}"
      unfolding Nts_def nts_syms_def using lrps by auto
    then show ?thesis using  lrps Nts_Un by (metis UnCI)
  next
    case False
    hence "S \<in> Nts (set ps - {(l,r)})"
      unfolding Nts_def using lrps 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) Nts_Un Nts_def)
    then show ?thesis 
      by (simp add: lrps Nts_def)
  qed
qed  

lemma uniformizeRtc_Nts: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps ps'" "S \<in> Nts (set ps)"
  shows "S \<in> Nts (set ps')"
  using assms by (induction rule: rtranclp_induct) (auto simp: uniformize_Nts)

(* Termination *)

theorem cnf_lemma2: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps ps'"
  shows "lang ps S = lang ps' S"
  using assms by (induction rule: rtranclp_induct) (fastforce simp: cnf_lemma1)+ 

theorem cnf_lemma2Nt: 
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** ps ps'"
  shows "lang ps S = lang ps' S"
  using assms by (induction rule: rtranclp_induct) (fastforce simp: cnf_lemma1Nt)+

theorem cnf_lemma: 
  assumes "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps ps'"
    and "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** ps' ps''"
  shows "lang ps S = lang ps'' S"
  using assms cnf_lemma2 cnf_lemma2Nt uniformizeRtc_Nts by fastforce

(* Part 2 *)
lemma badTmsCount_append: "badTmsCount (ps@ps') = badTmsCount ps + badTmsCount ps'"
by auto

lemma badNtsCount_append: "badNtsCount (ps@ps') = badNtsCount ps + badNtsCount ps'"
by auto

lemma badTmsCount_removeAll: 
  assumes "prodTms p > 0" "p \<in> set ps"
  shows "badTmsCount (removeAll p ps) < badTmsCount ps"
  using assms by (induction ps) fastforce+

lemma badNtsCount_removeAll: 
  assumes "prodNts p > 0" "p \<in> set ps"
  shows "badNtsCount (removeAll p ps) < badNtsCount ps"
  using assms by (induction ps) fastforce+

lemma badTmsCount_removeAll2:
  assumes "prodTms p > 0" "p \<in> set ps" "prodTms p' < prodTms p"
  shows "badTmsCount (removeAll p ps) + prodTms p' < badTmsCount ps"
  using assms by (induction ps) fastforce+

lemma badNtsCount_removeAll2:
  assumes "prodNts p > 0" "p \<in> set ps" "prodNts p' < prodNts p"
  shows "badNtsCount (removeAll p ps) + prodNts p' < badNtsCount ps"
  using assms by (induction ps) fastforce+

lemma lemma6_a:
  assumes "uniformize A t S ps ps'" shows "badTmsCount (ps') < badTmsCount ps"
proof -
  from assms obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps)) 
      \<and> ps' = ((removeAll (l,r) ps) @ [(A,[Tm t]), (l, p@[Nt A]@s)])"
    using fresh_nts_single[of ps S] unfolding uniformize_def by auto
  hence "prodTms (l,p@[Tm t]@s) = length (filter (isTm) (p@[Tm t]@s))"
    unfolding prodTms_def by auto
  hence 1: "prodTms (l,p@[Tm t]@s) = Suc (length (filter (isTm) (p@s)))"
    by (simp add: isTm_def)
  have 2: "badTmsCount ps' = badTmsCount (removeAll (l,r) ps) + badTmsCount [(A,[Tm t])] + badTmsCount [(l, p@[Nt A]@s)]"
    using lrps by (auto simp: badTmsCount_append)
  have 3: "badTmsCount (removeAll (l,r) ps) < badTmsCount ps"
    using 1 badTmsCount_removeAll lrps gr0_conv_Suc by blast
  have "prodTms (l, p@[Nt A]@s) = (length (filter (isTm) (p@[Nt A]@s))) \<or> prodTms (l, p@[Nt A]@s) = 0"
    unfolding prodTms_def using lrps by simp
  thus ?thesis
  proof 
    assume "prodTms (l, p@[Nt A]@s) = (length (filter (isTm) (p@[Nt A]@s)))"
    hence "badTmsCount ps' = badTmsCount (removeAll (l,r) ps) + prodTms (l, p@[Nt A]@s)"
      using 2 by (simp add: prodTms_def)
    moreover have "prodTms (l,p@[Nt A]@s) < prodTms (l,p@[Tm t]@s)"
      using 1 \<open>prodTms (l, p @ [Nt A] @ s) = length (filter isTm (p @ [Nt A] @ s))\<close> isTm_def by force 
    ultimately show "badTmsCount ps' < badTmsCount ps" 
      using badTmsCount_removeAll2[of "(l,r)" ps "(l,p @[Nt A]@s)"] lrps 1 by auto
  next 
    assume "prodTms (l, p@[Nt A]@s) = 0"
    hence "badTmsCount ps' = badTmsCount (removeAll (l,r) ps)"
      using 2 by (simp add: prodTms_def)
    thus "badTmsCount ps' < badTmsCount ps" 
      using 3 by simp
  qed
qed

lemma lemma6_b:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'" shows "badNtsCount ps' < badNtsCount ps"
proof -
  from assms obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps))
    \<and> ps' = ((removeAll (l,r) ps) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)])"
    using fresh_nts_single[of ps S] unfolding binarizeNt_def by auto
  hence "prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = length (filter (isNt) (p@[Nt B\<^sub>1,Nt B\<^sub>2]@s))"
    unfolding prodNts_def by auto
  hence 1: "prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = Suc (Suc (length (filter (isNt) (p@s))))"
    by (simp add: isNt_def)
  have 2: "badNtsCount ps' = badNtsCount (removeAll (l,r) ps) + badNtsCount [(A, [Nt B\<^sub>1,Nt B\<^sub>2])] + badNtsCount [(l, (p@[Nt A]@s))]"
    using lrps by (auto simp: badNtsCount_append prodNts_def)
  have 3: "badNtsCount (removeAll (l,r) ps) < badNtsCount ps"
    using lrps badNtsCount_removeAll 1 by force
  have "prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s)) \<or> prodNts (l, p@[Nt A]@s) = 0"
    unfolding prodNts_def using lrps by simp
  thus ?thesis 
  proof 
    assume "prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))"
    hence "badNtsCount ps' = badNtsCount (removeAll (l,r) ps) + badNtsCount [(l, (p@[Nt A]@s))]"
      using 2 by (simp add: prodNts_def)
    moreover have "prodNts (l, p@[Nt A]@s) < prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)"
      using 1 \<open>prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))\<close> isNt_def by simp
    ultimately show ?thesis 
      using badNtsCount_removeAll2[of "(l,r)" ps "(l, (p@[Nt A]@s))"] 1 lrps by auto
  next 
    assume "prodNts (l, p@[Nt A]@s) = 0"
    hence "badNtsCount ps' = badNtsCount (removeAll (l,r) ps)"
      using 2 by (simp add: prodNts_def)
    thus ?thesis 
      using 3 by simp
  qed
qed

lemma badTmsCount0_removeAll: "badTmsCount ps = 0 \<Longrightarrow> badTmsCount (removeAll (l,r) ps) = 0" 
by auto 

lemma slemma15_a:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
    and "badTmsCount ps = 0"
  shows "badTmsCount ps' = 0"
proof -
  obtain l r p s where lrps: "(l,r) \<in> set ps \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set ps))
    \<and> (ps' = ((removeAll (l,r) ps) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)]))"
    using assms(1) fresh_nts_single[of ps S] unfolding binarizeNt_def by auto
  hence "badTmsCount ps' = badTmsCount (removeAll (l,r) ps) + badTmsCount [(l, (p@[Nt A]@s))]"
    by (auto simp: badTmsCount_append prodTms_def isTm_def)
  moreover have "badTmsCount (removeAll (l,r) ps) = 0"
    using badTmsCount0_removeAll[of ps l r] assms(2) by simp
  moreover have "badTmsCount [(l, (p@[Nt A]@s))] = 0" 
  proof -
    have "prodTms (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = 0"
      using lrps assms(2) badTmsCountSet by auto
    thus "badTmsCount [(l, (p@[Nt A]@s))] = 0"
      by (auto simp: isTm_def prodTms_def)
  qed
  ultimately show ?thesis 
    by simp
qed

lemma lemma15_a:
  assumes "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** ps ps'"
    and "badTmsCount ps = 0"
  shows "badTmsCount ps' = 0"
  using assms by (induction) (auto simp: slemma15_a simp del: badTmsCount.simps)

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
  assumes "badTmsCount ps > 0"
  shows "\<exists>l r t. (l,r) \<in> set ps \<and> length r \<ge> 2 \<and> Tm t \<in> set r"
proof -
  have "\<exists>p \<in> set ps. prodTms p > 0"
    using assms badTmsCountSet not_gr0 by blast
  from this obtain l r where lr: "(l, r) \<in> set ps \<and> prodTms (l,r) > 0"
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
  assumes "badNtsCount ps > 0" 
  shows "\<exists>l r. (l, r) \<in> set ps \<and> length r \<ge> 3"
proof -
  have "\<exists>p \<in> set ps. prodNts p > 0"
    using assms badNtsCountSet not_gr0 by blast
  from this obtain l r where lr: "(l, r) \<in> set ps \<and> prodNts (l,r) > 0"
    by auto
  hence "length r \<ge> 3"
    unfolding prodNts_def using not_le_imp_less by fastforce
  thus ?thesis using lr by auto
qed

lemma list_longer2: "length l \<ge> 2 \<and> x \<in> set l \<Longrightarrow> (\<exists>hd tl . l = hd@[x]@tl \<and> (hd \<noteq> [] \<or> tl \<noteq> []))"
  using split_list_last by fastforce 

lemma list_longer3: "length l \<ge> 3 \<Longrightarrow> (\<exists>hd tl x y. l = hd@[x]@[y]@tl \<and> (hd \<noteq> [] \<or> tl \<noteq> []))"
  by (metis Suc_le_length_iff append.left_neutral append_Cons neq_Nil_conv numeral_3_eq_3)

lemma lemma8_a: "badTmsCount ps > 0 \<Longrightarrow> \<exists>ps' A t. uniformize A t S ps ps'"
proof -
  assume "badTmsCount ps > 0"
  then obtain l r t where lr: "(l,r) \<in> set ps \<and> length r \<ge> 2 \<and> Tm t \<in> set r"
    using badTmsCountNot0 by blast
  from this obtain p s where ps: "r = p@[Tm t]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])"
    unfolding isTm_def using lr list_longer2[of r] by blast
  from this obtain A ps' where "A = fresh(nts ps \<union> {S}) \<and> ps' = removeAll (l, r) ps @ [(A, [Tm t]), (l, p @ [Nt A] @ s)]" 
    by auto
  hence "uniformize A t S ps ps'"
    unfolding uniformize_def using lr ps by auto
  thus ?thesis by blast
qed

lemma lemma8_b:
  assumes "badTmsCount ps = 0" and "badNtsCount ps > 0"
  shows "\<exists>ps' A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
proof -
  obtain l r where lr: "(l, r) \<in> set ps \<and> length r \<ge> 3"
    using assms(2) badNtsCountNot0 by blast
  obtain p s X Y where psXY: "r = p@[X]@[Y]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])"
    using lr list_longer3[of r] by blast
  have "(\<forall>a \<in> set r. isNt a)"
    using lr assms(1) badTmsCountSet[of ps] noTms_prodTms0[of l r] by fastforce
  from this obtain B\<^sub>1 B\<^sub>2 where "X = Nt B\<^sub>1 \<and> Y = Nt B\<^sub>2"
    using isNt_def psXY by fastforce
  hence B: "(r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> [])"
    using psXY by auto
  from this obtain A ps' where "A = fresh(nts ps \<union> {S}) \<and> ps' = removeAll (l, r) ps @ [(A, [Nt B\<^sub>1, Nt B\<^sub>2]), (l, p @ [Nt A] @ s)]"
    by simp
  hence "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
    unfolding binarizeNt_def using lr B by auto
  thus ?thesis by blast
qed

lemma uniformize_2: "\<exists>ps'. (\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps ps' \<and> (badTmsCount ps' = 0)"
proof (induction "badTmsCount ps" arbitrary: ps rule: less_induct)
  case less
  then show ?case
  proof (cases "badTmsCount ps = 0")
    case False
    from this obtain ps' A t where g': "uniformize A t S ps ps'"
      using lemma8_a by blast
    hence "badTmsCount ps' < badTmsCount ps"
      using lemma6_a[of A t] by blast
    from this obtain ps'' where "(\<lambda>x y. \<exists>A t. uniformize A t S x y)\<^sup>*\<^sup>* ps' ps'' \<and> badTmsCount ps'' = 0"
      using less by blast
    thus ?thesis 
      using g' converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A t. uniformize A t S x y)" ps ps' ps''] by blast
  qed blast
qed

lemma binarizeNt_2: 
  assumes "badTmsCount ps = 0"
    shows "\<exists>ps'. (\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** ps ps' \<and> (badNtsCount ps' = 0)"
using assms proof (induction "badNtsCount ps" arbitrary: ps rule: less_induct)
  case less
  then show ?case 
  proof (cases "badNtsCount ps = 0")
    case False
    from this obtain ps' A B\<^sub>1 B\<^sub>2 where g': "binarizeNt A B\<^sub>1 B\<^sub>2 S ps ps'"
      using assms lemma8_b less(2) by blast
    hence "badNtsCount ps' < badNtsCount ps"
      using lemma6_b by blast
    from this obtain ps'' where "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* ps' ps'' \<and> badNtsCount ps'' = 0"
      using less slemma15_a[of A B\<^sub>1 B\<^sub>2 S ps ps'] g' by blast
    then show ?thesis 
      using g' converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)" ps ps' ps''] by blast
  qed blast
qed

theorem cnf_noe_nou:  fixes ps :: "('n::infinite,'t)prods"
  assumes "Eps_free (set ps)" and "Unit_free (set ps)"
  shows "\<exists>ps'::('n,'t)prods. uniform (set ps') \<and> binary (set ps') \<and> lang ps S = lang ps' S \<and> Eps_free (set ps') \<and> Unit_free (set ps')"
proof -
  obtain ps' where g': "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps ps' \<and> badTmsCount ps' = 0 \<and> Eps_free (set ps') \<and> Unit_free (set ps')"
    using assms uniformize_2 uniformizeRtc_Eps_free uniformizeRtc_Unit_free by blast
  obtain ps'' where g'': "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)^** ps' ps'' \<and> (badNtsCount ps'' = 0) \<and> (badTmsCount ps'' = 0)"
    using g' binarizeNt_2 lemma15_a by blast
  hence "uniform (set ps'') \<and> binary (set ps'') \<and> Eps_free (set ps'') \<and> Unit_free (set ps'')"
    using g' count_bin_un binarizeNtRtc_Eps_free binarizeNtRtc_Unit_free by fastforce
  moreover have "lang ps S = lang ps'' S"
    using g' g'' cnf_lemma by blast
  ultimately show ?thesis by blast
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
  fixes ps :: "('n::infinite,'t) prods"
  shows "\<exists>ps'::('n,'t)prods. CNF(set ps') \<and> lang ps' S = lang ps S - {[]}"
proof -
  obtain ps\<^sub>0 where ps\<^sub>0: "eps_elim_rel ps ps\<^sub>0"
    using eps_elim_rel_exists by blast
  obtain ps\<^sub>u where ps\<^sub>u: "unit_elim_rel ps\<^sub>0 ps\<^sub>u"
    using unit_elim_rel_exists by blast
  hence 1: "Eps_free (set ps\<^sub>u) \<and> Unit_free (set ps\<^sub>u)"
    using ps\<^sub>0 ps\<^sub>u Eps_free_if_eps_elim_rel Unit_free_if_unit_elim_rel unit_elim_rel_Eps_free by fastforce
  have 2: "lang ps\<^sub>u S = lang ps S - {[]}"
    using ps\<^sub>u eps_elim_rel_lang_eq[OF ps\<^sub>0] unit_elim_rel_lang_eq[OF ps\<^sub>u] by (simp add: eps_elim_rel_lang_eq)
  obtain ps'::"('n,'t)prods" where g': "uniform (set ps') \<and> binary (set ps') \<and> lang ps\<^sub>u S = lang ps' S \<and> Eps_free (set ps') \<and> Unit_free (set ps')"
    using 1 cnf_noe_nou by blast
  hence "CNF (set ps')" 
    using g' CNF_eq by blast
  moreover have "lang ps' S = lang ps S - {[]}"
    using 2 g' by blast
  ultimately show ?thesis by blast
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