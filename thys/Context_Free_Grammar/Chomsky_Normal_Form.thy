(*
Authors: August Martin Stimpfle, Tobias Nipkow, Felipe Escallon
Partly based on HOL4 theories by Aditi Barthwal
*)

(* TODO Uniform etc *)

section \<open>Conversion to Chomsky Normal Form\<close>

theory Chomsky_Normal_Form
imports
  Unit_Elimination
  Epsilon_Elimination
  Replace_Terminals
begin

text \<open>The conversion to Chomsky Normal Form (CNF) is achieved by, in that order,
epsilon and unit elimination, uniformization and binarization.
A production \<open>A \<rightarrow> \<alpha>\<close> is
\<^descr> uniform if \<open>\<alpha>\<close> contains no terminal unless it is of length 1,
\<^descr> binary if \<^prop>\<open>length \<alpha> \<le> 2\<close>.
\<close>

definition CNF :: "('n, 't) Prods \<Rightarrow> bool" where
"CNF P = (\<forall>(A,\<alpha>) \<in> P. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>a. \<alpha> = [Tm a]))"


subsection \<open>Uniformization\<close>

definition uniform :: "('n, 't) Prods \<Rightarrow> bool" where
  "uniform P \<equiv> \<forall>(A, \<alpha>) \<in> P. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"

definition Bad_tms :: "('n,'t) Prods \<Rightarrow> 't set" where
"Bad_tms P = (\<Union>(A,\<alpha>) \<in> P. if length \<alpha> \<ge> 2 then Tms_syms \<alpha> else {})"

definition bad_tms :: "('n,'t) prods \<Rightarrow> 't list" where
"bad_tms ps = remdups(concat ((map tms_syms o filter (\<lambda>u. length u \<ge> 2) o map snd) ps))"

lemma set_bad_tms: "set(bad_tms ps) = Bad_tms (set ps)"
unfolding Bad_tms_def bad_tms_def
by (auto simp: set_tms_syms split: if_splits)

definition replace_Tm_2_syms where
"replace_Tm_2_syms f xs = (if length xs < 2 then xs else map (replace_Tm_sym f) xs)"

abbreviation Replace_Tm_2_old where
"Replace_Tm_2_old f P \<equiv> {(A, replace_Tm_2_syms f \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P}"

definition Replace_Tm_2 where
"Replace_Tm_2 f P = Replace_Tm_2_old f P \<union> Replace_Tm_new f (Bad_tms P)"

definition replace_Tm_2 where
"replace_Tm_2 f P = [(A, replace_Tm_2_syms f \<alpha>). (A,\<alpha>) \<leftarrow> P] @ [(f a, [Tm a]). a \<leftarrow> bad_tms P]"

lemma set_replace_Tm_2: "set (replace_Tm_2 f ps) = Replace_Tm_2 f (set ps)"
by (auto simp add: replace_Tm_2_def Replace_Tm_2_def set_bad_tms)

lemma Expand_all_syms_Replace_Tm_2:
  assumes inj: "inj_on f as" and L: "L \<inter> f ` as = {}"
    and \<alpha>: "length \<alpha> \<ge> 2 \<Longrightarrow> Tms_syms \<alpha> \<subseteq> as" "Nts_syms \<alpha> \<subseteq> L"
  shows "Expand_all_syms (Replace_Tm_new f as) L (replace_Tm_2_syms f \<alpha>) = {\<alpha>}"
proof (cases "length \<alpha> < 2")
  case False
  thus ?thesis using assms
    by (simp add: replace_Tm_2_syms_def Expand_all_syms_Replace_Tm_ops map_replace_Tm_sym_ops)
next
  case True
  thus ?thesis using assms
    by(cases \<alpha>)
      (auto simp: replace_Tm_2_syms_def Expand_sym_Replace_Tm_Tm Expand_sym_Replace_Tm_Nt
            split: sym.splits)
qed

lemma Expand_all_Replace_Tm_2:
  assumes inj: "inj_on f as" and L: "L \<inter> f ` as = {}"
    and P: "Bad_tms P \<subseteq> as" "Rhs_Nts P \<subseteq> L"
  shows "Expand_all (Replace_Tm_new f as) L (Replace_Tm_2_old f P) = P"
proof-
  have *: "(A,\<alpha>) \<in> P \<Longrightarrow> Expand_all_syms (Replace_Tm_new f as) L (replace_Tm_2_syms f \<alpha>) = {\<alpha>}" for A \<alpha>
    apply (rule Expand_all_syms_Replace_Tm_2[OF inj L])
    using P by (force simp: Bad_tms_def Rhs_Nts_def)+
  then show ?thesis by (force simp: Expand_def)
qed

lemma Lang_Replace_Tm_2:
  assumes inj: "inj_on f (Bad_tms P)"
    and disj: "Nts P \<inter> f ` Bad_tms P = {}"
    and A: "A \<notin> f ` Bad_tms P"
  shows "Lang (Replace_Tm_2 f P) A = Lang P A"
    (is "?l = ?r")
proof-
  let ?B = "Bad_tms P"
  from disj have L: "Lhss P \<inter> f ` ?B = {}" and R: "Rhs_Nts P \<inter> f ` ?B = {}"
    by (auto simp: Nts_Lhss_Rhs_Nts)
  have "?l = Lang (Replace_Tm_2_old f P \<union> Replace_Tm_new f ?B) A"
    by (simp add: Replace_Tm_2_def)
  also have "\<dots> = Lang (Expand_all (Replace_Tm_new f ?B) (Nts P)
                         (Replace_Tm_2_old f P) \<union> Replace_Tm_new f ?B) A"
    apply (subst Lang_Expand_all)
    by (auto simp: Nts_def Lhss_def)
  also have "\<dots> = Lang (P \<union> Replace_Tm_new f ?B) A"
    using Expand_all_Replace_Tm_2[OF inj disj]
    by (simp add: Nts_Lhss_Rhs_Nts)
  also have "\<dots> = ?r"
    apply (rule Lang_Un_disj_Lhss) using disj A by (auto simp: Lhss_image_Pair)
  finally show ?thesis.
qed

corollary lang_replace_Tm_2:
  assumes inj: "inj_on f (Bad_tms (set ps))" and disj: "Nts(set ps) \<inter> f ` Bad_tms(set ps) = {}"
    and A: "A \<notin> f ` Bad_tms (set ps)"
  shows "lang (replace_Tm_2 f ps) A = lang ps A"
using Lang_Replace_Tm_2[OF assms] by(simp add: set_replace_Tm_2)

lemma map_replace_Tm_sym_id: "\<alpha> = map (replace_Tm_sym f) \<alpha> \<longleftrightarrow> Tms_syms \<alpha> = {}"
by(induction \<alpha>)(auto simp: replace_Tm_sym_def split: sym.split)

lemma uniform_Replace_Tm: "uniform (Replace_Tm_2 f P)"
unfolding Replace_Tm_2_def uniform_def replace_Tm_2_syms_def
by(auto simp: replace_Tm_sym_def map_replace_Tm_sym_id Tms_syms_def
              numeral_2_eq_2 less_Suc_eq_le le_Suc_eq length_Suc_conv
        split: sym.splits)

definition uniformize :: "('n::fresh0) \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
"uniformize S ps =
  (let ts = bad_tms ps;
       tmap = fresh_fun (insert S (Nts(set ps))) ts
   in replace_Tm_2 tmap ps)"

lemma "uniformize 0 [(0::nat, [Tm 1, Tm (2::int)])] =
  [(0, [Nt 1, Nt 2]), (1, [Tm 1]), (2, [Tm 2])]"
by eval

lemma uniform_uniformize: "uniform (set (uniformize S ps))"
unfolding uniformize_def by (simp add: set_replace_Tm_2 uniform_Replace_Tm)

lemma lang_uniformize: "A \<in> Nts(set ps) \<union> {S} \<Longrightarrow> lang (uniformize S ps) A = lang ps A"
apply (simp add: uniformize_def)
apply(rule lang_replace_Tm_2)
  apply (metis finite_insert finite_nts fresh_fun_inj_on set_bad_tms)
 apply (simp add: finite_nts fresh_fun_disj set_bad_tms subset_insertI)
using finite_nts fresh_fun_notIn set_bad_tms
  by (smt (verit, best) finite_insert imageE insert_iff)

lemma eps_free_uniformize: "eps_free ps \<Longrightarrow> eps_free (uniformize S ps)"
unfolding uniformize_def Eps_free_def
by (auto simp add: set_replace_Tm_2 Replace_Tm_2_def replace_Tm_2_syms_def)

lemma Unit_free_uniformize: "Unit_free (set ps) \<Longrightarrow> Unit_free (set(uniformize S ps))"
unfolding uniformize_def Unit_free_def
by (auto simp add: set_replace_Tm_2 Replace_Tm_2_def replace_Tm_2_syms_def)

text \<open>The following is used to prove that binarization preserves uniformity.
The latter is characterized in terms of \<open>badTmsCount = 0\<close>.\<close>

lemma Nts_correct: "A \<notin> Nts P \<Longrightarrow> (\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>))"
unfolding Nts_def Nts_syms_def by auto

definition prodTms :: "('n,'t) prod \<Rightarrow> nat" where
"prodTms p \<equiv> (if length (snd p) \<le> 1 then 0 else length (filter (isTm) (snd p)))"

definition prodNts :: "('n,'t) prod \<Rightarrow> nat" where
"prodNts p \<equiv> (if length (snd p) \<le> 2 then 0 else length (filter (isNt) (snd p)))"

fun badTmsCount :: "('n,'t) Prods \<Rightarrow> nat" where
  "badTmsCount P = sum prodTms P"

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
     using assms by auto
next 
  assume assm: "badTmsCount P = 0"
  have "\<forall>p \<in> P. ((\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t]))"
  proof 
    fix p assume "p \<in> P"
    hence "prodTms p = 0"
      using assm assms by auto
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


subsection \<open>Binarization\<close>

text \<open>Binarization has two parts: a relational specification of what a single step in
the conversion should do and an executable function that performs the transitive-reflexive
closure of a single step. This way multiple functional implementations can be proved
correct more easily. The relational part is inherited from Aditi Barthwal's work.\<close>

definition binary :: "('n, 't) Prods \<Rightarrow> bool" where
  "binary P \<equiv> \<forall>(A, \<alpha>) \<in> P. length \<alpha> \<le> 2"

fun badNtsCount :: "('n,'t) Prods \<Rightarrow> nat" where
  "badNtsCount P = sum prodNts P"

lemma badNtsCountSet: assumes "finite P"
  shows "(\<forall>p \<in> P. prodNts p = 0) \<longleftrightarrow> badNtsCount P = 0"
  using assms by simp

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


subsubsection \<open>Specification of a Single Binarization Step\<close>

definition binarizeStep :: "'n::infinite \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods \<Rightarrow> bool" where
"binarizeStep A B\<^sub>1 B\<^sub>2 S P P' \<equiv> (
    \<exists>l r p s. (l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> (Nts P \<union> {S}))
    \<and> P' = P - {(l,r)} \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"

lemma binarizeStep_Eps_free:
  assumes "Eps_free P"
    and "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Eps_free P'"
  using assms unfolding binarizeStep_def Eps_free_def by force

lemma binarizeStep_Unit_free:
  assumes "Unit_free P"
    and "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Unit_free P'"
  proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> P)"
    using assms(1) unfolding Unit_free_def by simp
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> (P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(2) unfolding binarizeStep_def by blast
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using lrps by simp
  ultimately show ?thesis unfolding Unit_free_def by simp
qed

lemma cnf_r1Nt:
  assumes "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
    and "P \<turnstile> lhs \<Rightarrow> rhs"
  shows "P' \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' C v where Cv: "lhs = p'@[Nt C]@s' \<and> rhs = p'@v@s' \<and> (C,v) \<in> P"
    using derive.cases[OF assms(2)] by fastforce
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts P)
    \<and> (P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(1) set_removeAll unfolding binarizeStep_def by fastforce
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
      by (meson 1 converse_rtranclp_into_rtranclp derive_append derive_prepend r_into_rtranclp) 
    thus ?thesis 
      using False \<open>C = l \<and> v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s\<close> Cv derives_append derives_prepend by blast
  qed
qed

lemma slemma1_1Nt:
  assumes "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
    and "(A, \<alpha>) \<in> P'"
  shows "\<alpha> = [Nt B\<^sub>1,Nt B\<^sub>2]"
proof -
  have "A \<notin> Nts P"
    using assms(1) unfolding binarizeStep_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> P"
    unfolding Nts_def  by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Nt B\<^sub>1,Nt B\<^sub>2] \<and> (A, \<alpha>) \<in> P'"
    using assms(1) unfolding binarizeStep_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_4Nt:
  assumes "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
    and "(l,r) \<in> P"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> Nts P"
    using assms(1) unfolding binarizeStep_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>P\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed


lemma lemma1Nt: 
  assumes "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
    and "P' \<turnstile> lhs \<Rightarrow> rhs"
  shows "(substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs) 
          \<or> (P \<turnstile> (substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] lhs) \<Rightarrow> substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] rhs)"
proof -
  obtain l r p s where lrps: "(l,r) \<in> P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts P)
    \<and> (P' = ((P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))"
    using assms(1) set_removeAll unfolding binarizeStep_def by fastforce
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
        using assms(1) unfolding binarizeStep_def Nts_def by auto 
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
        using True lrps uv assms slemma4_4Nt[of A B\<^sub>1 B\<^sub>2 S P P'] unfolding binarizeStep_def Nts_def by auto
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v = substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] p @ substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] ([Nt A]@s)"
        by simp
      hence "substsNt A [Nt B\<^sub>1,Nt B\<^sub>2] v = p @ [Nt B\<^sub>1,Nt B\<^sub>2] @ s"
        using 1 substs_append by (simp add: substs_skip)
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
         using False substs_skip by fastforce
       thus ?thesis 
         using 1 2 assms(2) uv derive.simps by fast
    qed
  qed
qed

lemma lemma3Nt:
  assumes "P' \<turnstile> lhs \<Rightarrow>* rhs"
    and "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
  shows "P \<turnstile> substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] lhs \<Rightarrow>* substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] rhs"
  using assms 
proof (induction rhs rule: rtranclp_induct)
  case (step y z)
  then show ?case 
    using lemma1Nt[of A B\<^sub>1 B\<^sub>2 S P P' y z] by auto
qed simp

lemma lemma4Nt:
  assumes "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Lang P' S \<subseteq> Lang P S"
proof
  fix w
  assume "w \<in> Lang P' S"
  hence "P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    by (simp add: Lang_def)
  hence "P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding binarizeStep_def by auto
  hence "P \<turnstile> substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] [Nt S] \<Rightarrow>*  substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] (map Tm w)"
    using assms lemma3Nt[of P' \<open>[Nt S]\<close> \<open>map Tm w\<close>] by blast
  moreover have "substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] [Nt S] = [Nt S]"
    using assms unfolding binarizeStep_def by auto
  moreover have "substsNt A [Nt B\<^sub>1, Nt B\<^sub>2] (map Tm w) = map Tm w" by simp
  ultimately show "w \<in> Lang P S" using Lang_def
    by (metis (no_types, lifting) mem_Collect_eq)
qed

lemma slemma5_1Nt:
  assumes "P \<turnstile> u \<Rightarrow>* v"
    and "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
  shows "P' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction v rule: rtranclp_induct) (auto simp: cnf_r1Nt rtranclp_trans)

lemma lemma5Nt: 
  assumes "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'"
  shows "Lang P S \<subseteq> Lang P' S"
proof 
  fix w
  assume "w \<in> Lang P S"
  hence "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def binarizeStep_def by auto 
  thus "w \<in> Lang P' S" 
    using assms slemma5_1Nt Lang_def by fast
qed 

lemma cnf_lemma1Nt: "binarizeStep A B\<^sub>1 B\<^sub>2 S P P' \<Longrightarrow> Lang P S = Lang P' S"
  using lemma4Nt lemma5Nt by fast

lemma binarizeStepRtc_Eps_free:
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeStep A B\<^sub>1 B\<^sub>2 S x y)^** P P'"
    and "Eps_free P"
  shows "Eps_free P'"
  using assms by (induction rule: rtranclp_induct) (auto simp: binarizeStep_Eps_free)

lemma binarizeStepRtc_Unit_free:
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeStep A B\<^sub>1 B\<^sub>2 S x y)^** P P'"
    and "Unit_free P"
  shows "Unit_free P'"
  using assms by (induction rule: rtranclp_induct) (auto simp: binarizeStep_Unit_free)

theorem cnf_lemma2Nt: 
  assumes "(\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeStep A B\<^sub>1 B\<^sub>2 S x y)^** P P'"
  shows "Lang P S = Lang P' S"
  using assms by (induction rule: rtranclp_induct) (fastforce simp: cnf_lemma1Nt)+

text \<open>Termination\<close>

lemma lemma6_b:
  assumes "finite P" "binarizeStep A B\<^sub>1 B\<^sub>2 S P P'" shows "badNtsCount P' < badNtsCount P"
proof -
  from assms(2) obtain l r p s where lrps: "(l,r) \<in> P" "r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" "p \<noteq> [] \<or> s \<noteq> []"
    "A \<notin> Nts P" "P' = P - {(l,r)} \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}"
    unfolding binarizeStep_def by auto
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

lemma noTms_prodTms0:
  assumes "prodTms (l,r) = 0"
  shows "length r \<le> 1 \<or> (\<forall>a \<in> set r. isNt a)"
proof -
  have "length r \<le> 1 \<or> (\<nexists>a. a \<in> set r \<and> isTm a)"
    using assms unfolding prodTms_def using empty_filter_conv by fastforce
  thus ?thesis 
    by (metis isNt_def isTm_def sym.exhaust)
qed

lemma badNtsCountNot0: 
  assumes "finite P" "badNtsCount P > 0" 
  shows "\<exists>l r. (l, r) \<in> P \<and> length r \<ge> 3"
using assms badNtsCountSet not_gr0 unfolding prodNts_def by fastforce


subsubsection \<open>Functional Binarization\<close>

definition freshA :: "('n::fresh0,'t) prods \<Rightarrow> 'n \<Rightarrow> 'n" where
  "freshA ps S = fresh0 (Nts (set ps) \<union> {S})"

lemma freshA_notin_set:
  shows "freshA ps S \<notin> (Nts (set ps) \<union> {S})"
  unfolding freshA_def by (metis ID.set_finite finite_Un finite_nts fresh0_notIn)

(* Simplifying the first two cases complicates proofs *)
fun replaceNts :: "'n::fresh0 \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n \<times> 'n) option \<times> ('n,'t) syms" where
  "replaceNts A [] = (None, [])" |
  "replaceNts A [s] = (None, [s])" |
  "replaceNts A (Nt s\<^sub>1 # Nt s\<^sub>2 # sl) = (Some (s\<^sub>1, s\<^sub>2), Nt A # sl)" |
  "replaceNts A (s#sl) = (let (nn_opt, sl') = replaceNts A sl in (nn_opt, s#sl'))"

lemma replaceNts_tm_unchanged_opt:
  assumes 
    "replaceNts A (s0#s1#sl) = (nn_opt, sl')"
    "\<exists>t. s0 = Tm t \<or> s1 = Tm t"
  obtains sl'' where "replaceNts A (s1#sl) = (nn_opt, sl'')"
proof -
  obtain nn_opt' sl'' where "replaceNts A (s1#sl) = (nn_opt', sl'')"
    by fastforce
  moreover with assms have "nn_opt = nn_opt'" by fastforce
  ultimately show thesis using that by blast
qed

lemma replaceNts_id_iff_None:
  assumes "replaceNts A sl = (nn_opt, sl')"
  shows "nn_opt = None \<longleftrightarrow> sl = sl'"
  using assms proof (induction sl arbitrary: nn_opt sl' rule: replaceNts.induct)
  case ("4_1" A t s sl)
  then obtain sl'' where rec: "replaceNts A (s#sl) = (nn_opt, sl'')"
    using replaceNts_tm_unchanged_opt by blast
  then show ?case using "4_1" by auto
next
  case ("4_2" A s t sl)
  then obtain sl'' where rec: "replaceNts A (Tm t#sl) = (nn_opt, sl'')"
    using replaceNts_tm_unchanged_opt by blast
  then show ?case using "4_2" by auto
qed auto

lemma replaceNts_replaces_pair:
  assumes 
    "replaceNts A sl = (nn_opt, sl')"
    "nn_opt \<noteq> None"
  obtains p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)"
    "sl = p@[Nt B\<^sub>1, Nt B\<^sub>2]@q"
    "sl' = p@[Nt A]@q" 
  using assms proof (induction sl arbitrary: thesis nn_opt sl' rule: replaceNts.induct)
  case ("4_1" A t s sl)
  then obtain sl'' where 
    "replaceNts A (s#sl) = (nn_opt, sl'')" 
    and sl'_def: "sl' = Tm t # sl''"
    using replaceNts_tm_unchanged_opt
    by (metis (lifting) case_prod_conv prod.inject replaceNts.simps(4))
  with "4_1"(1,4) obtain p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)" "s#sl = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl'' = p@[Nt A]@q" 
    by blast
  moreover with sl'_def have "Tm t #s#sl = (Tm t#p)@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl' = (Tm t#p)@[Nt A]@q"
    by auto
  ultimately show ?case using "4_1"(2) by blast
next
  case ("4_2" A s t sl)
  then obtain sl'' where 
    "replaceNts A (Tm t#sl) = (nn_opt, sl'')" 
    and sl'_def: "sl' = s # sl''"
    using replaceNts_tm_unchanged_opt
    by (metis (lifting) old.prod.case prod.inject replaceNts.simps(5))
  with "4_2"(1,4) obtain p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)" "Tm t#sl = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl'' = p@[Nt A]@q" 
    by blast
  moreover with sl'_def have "s#Tm t#sl = (s#p)@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl' = (s#p)@[Nt A]@q"
    by auto
  ultimately show ?case using "4_2"(2) by blast
qed fastforce+

corollary replaceNts_replaces_pair_Some:
  assumes "replaceNts A sl = (Some (B\<^sub>1,B\<^sub>2), sl')"
  obtains p q where 
    "sl = p@[Nt B\<^sub>1, Nt B\<^sub>2]@q"
    "sl' = p@[Nt A]@q"
  using replaceNts_replaces_pair 
  by (smt (verit) assms option.distinct(1) option.inject prod.inject)

fun binarize1 :: "'n::fresh0 \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "binarize1 A ps0 [] = ps0" |
  "binarize1 A ps0 ((l,r)#ps) = 
    (case replaceNts A r of 
      (None, _) \<Rightarrow> binarize1 A ps0 ps|
      (Some (B\<^sub>1,B\<^sub>2), r') \<Rightarrow> 
        if length r < 3 then binarize1 A ps0 ps 
        else (A, [Nt B\<^sub>1,Nt B\<^sub>2]) # (l, r') # removeAll (l,r) ps0)" 

lemma binarize1_rec_if_id_or_lt3:
  assumes 
    "replaceNts A r = (nn_opt, r')"
    "r = r' \<or> length r < 3"
  shows "binarize1 A ps0 ((l,r)#ps) = binarize1 A ps0 ps"
  using assms replaceNts_id_iff_None by (cases nn_opt) auto
   
lemma binarize1_binarizes:
  assumes "binarize1 A ps0 ps \<noteq> ps0"
  obtains l r r' B\<^sub>1 B\<^sub>2 where
    "(l,r) \<in> set ps"
    "length r > 2"
    "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')"
    "binarize1 A ps0 ps = (A, [Nt B\<^sub>1,Nt B\<^sub>2]) # (l, r') # removeAll (l,r) ps0"
  using assms proof (induction ps arbitrary: thesis)
  case (Cons p ps)
  obtain l r r' nn_opt where lr_defs: "p = (l,r)" "replaceNts A r = (nn_opt,r')" 
    by fastforce
  consider (hd) "r \<noteq> r' \<and> length r > 2" | (tl) "r = r' \<or> length r < 3"  by fastforce
  then show ?case 
  proof cases
    case hd
    with replaceNts_id_iff_None lr_defs obtain B\<^sub>1 B\<^sub>2 where "nn_opt = Some (B\<^sub>1,B\<^sub>2)"
      by fast
    moreover from this hd have 
      "binarize1 A ps0 (p#ps) = (A, [Nt B\<^sub>1,Nt B\<^sub>2]) # (l, r') # removeAll (l,r) ps0" 
      using lr_defs by auto
    ultimately show ?thesis using Cons(2) lr_defs hd by fastforce
  next
    case tl
    with lr_defs binarize1_rec_if_id_or_lt3 
      have "binarize1 A ps0 (p#ps) = binarize1 A ps0 ps" by blast
    with Cons show ?thesis using lr_defs by (metis list.set_intros(2))
  qed
qed simp

lemma binarize1_binarized:
  assumes 
    "A \<notin> Nts (set ps) \<union> {S}"
    "binarize1 A ps ps \<noteq> ps"
  obtains B\<^sub>1 B\<^sub>2 where  "binarizeStep A B\<^sub>1 B\<^sub>2 S (set ps) (set (binarize1 A ps ps))"
proof -
  from binarize1_binarizes[OF assms(2)] obtain l r r' B\<^sub>1 B\<^sub>2 where 
  binarize1_defs:
    "(l,r) \<in> set ps"
    "length r > 2"
    "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')"
    "binarize1 A ps ps = (A, [Nt B\<^sub>1,Nt B\<^sub>2]) # (l, r') # removeAll (l,r) ps"
    by metis
  moreover from this obtain p s where "r = p@[Nt B\<^sub>1, Nt B\<^sub>2]@s"  "r' = p@[Nt A]@s"
    using replaceNts_replaces_pair by blast
  ultimately have "binarizeStep A B\<^sub>1 B\<^sub>2 S (set ps) (set (binarize1 A ps ps))" 
    unfolding binarizeStep_def using assms(1) by auto
  then show thesis using that by simp
qed

lemma binarize1_dec_badNtsCount:
  assumes "binarize1 A ps ps \<noteq> ps" 
          "A \<notin> Nts (set ps) \<union> {S}"
  shows "badNtsCount (set (binarize1 A ps ps)) < badNtsCount (set ps)"
  using lemma6_b assms binarize1_binarized 
  by (metis list.set_finite)

lemma badNts_impl_binarize1_not_id_unif:
  assumes "badNtsCount (set ps) = Suc n"
    "uniform (set ps)"
  shows "binarize1 A ps0 ps \<noteq> ps0"
  using assms proof (induction ps arbitrary: n)
  case (Cons p ps)
  obtain l r where lr_def: "(l,r) = p" using old.prod.exhaust by metis
  consider (no_badNts_hd) "badNtsCount (set [p]) = 0" | 
          (Suc_badNts_hd) m where "badNtsCount (set [p]) = Suc m"
    using not0_implies_Suc by blast
  then show ?case
  proof cases
    case no_badNts_hd
    from Cons(3) have only_Nts: "length r = 1 \<or> (\<forall>s\<in>(set r). \<exists>n. s = Nt n)"
      unfolding uniform_def using lr_def
      by (smt (verit, best) One_nat_def case_prodD destTm.cases length_Cons list.set_intros(1)
          list.size(3))
    have "length r < 3"
    proof (rule ccontr)
      assume "\<not>?thesis"
      hence "length r \<ge> 2" by simp
      moreover with only_Nts have "\<forall>s\<in>set r. \<exists>n. s = Nt n" by presburger
      ultimately have "prodNts p \<noteq> 0" unfolding prodNts_def using lr_def 
        by (metis \<open>\<not> length r < 3\<close> filter_True isNt_def le_imp_less_Suc not_numeral_le_zero numeral_2_eq_2
            numeral_3_eq_3 snd_conv)
      with no_badNts_hd show False by simp
    qed
    with lr_def have "binarize1 A ps0 (p#ps) = binarize1 A ps0 ps" 
      using binarize1_rec_if_id_or_lt3 by (metis old.prod.exhaust)
    with Cons show ?thesis 
      by (metis (no_types, lifting) badNtsCountSet bot_nat_0.not_eq_extremum gr0_conv_Suc 
          list.set_finite list.set_intros(1,2) no_badNts_hd set_ConsD uniform_def)
  next
    case Suc_badNts_hd
    with lr_def have all_Nts: "length r > 2 \<and> (\<forall>s\<in>set r. \<exists>n. s = Nt n)"
      using Cons.prems(2) uniform_badTmsCount[of "set (p # ps)"] noTms_prodTms0[of l r]
      by(auto simp: prodNts_def length_Suc_conv isNt_def split: if_splits)
    moreover obtain r' B\<^sub>1 B\<^sub>2 where replace_defs: "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')" "r' \<noteq> r"
    proof -
      from all_Nts obtain ns B\<^sub>1 B\<^sub>2 where "r = [Nt B\<^sub>1, Nt B\<^sub>2] @ ns"
        by (metis (no_types, lifting) append_Cons append_Nil le_imp_less_Suc length_Suc_conv 
            linorder_not_less list.exhaust list.set_intros(1,2) list.size(3) not_less_iff_gr_or_eq 
            numeral_2_eq_2)
      thus thesis using that by simp
    qed
    ultimately have "binarize1 A ps0 (p#ps) = (A, [Nt B\<^sub>1, Nt B\<^sub>2]) # (l,r') # removeAll (l,r) ps0"
                    (is "_ = ?rem")
      using lr_def by fastforce
    also have "... \<noteq> ps0" 
    proof
      assume rem_eq: "... = ps0"
      then obtain xs where "ps0 = (A, [Nt B\<^sub>1, Nt B\<^sub>2]) # (l,r') # xs" by metis
      with rem_eq have "(l,r) = (l,r')" using set_removeAll
        by (smt (verit, ccfv_SIG) Diff_disjoint insert_disjoint(2) length_Cons lessI not_add_less2
            plus_1_eq_Suc removeAll.simps(2) removeAll_id)
      with replace_defs show False by blast
    qed
    finally show ?thesis .
  qed
qed simp


lemma binarize1_preserves_uniform:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes ps_uniform: "uniform (set ps)"
      and ps'_def: "ps' = binarize1 A ps ps"
    shows "uniform (set ps')"
proof -
  consider (id) "binarize1 A ps ps = ps" | (not_id) "binarize1 A ps ps \<noteq> ps" by blast
  then show ?thesis
  proof cases
    case not_id
    from binarize1_binarizes[OF not_id] obtain l r r' B\<^sub>1 B\<^sub>2 where lr_defs:
      "(l,r) \<in> set ps" "length r > 2" "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')" 
      "binarize1 A ps ps = (A,[Nt B\<^sub>1, Nt B\<^sub>2]) # (l,r') # removeAll (l,r) ps" by metis
    moreover from ps_uniform have "uniform (set (removeAll (l,r) ps))"
      unfolding uniform_def by simp
    moreover have "uniform (set [(l,r')])"
    proof -
      from replaceNts_replaces_pair_Some[OF lr_defs(3)] obtain p q where 
        "r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "r' = p@[Nt A]@q" .
      with lr_defs ps_uniform show ?thesis unfolding uniform_def by fastforce
    qed
    ultimately show ?thesis using ps'_def unfolding uniform_def by auto
  qed (use assms in simp)
qed

function binarize :: "'n::fresh0 \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "binarize S ps = 
    (let ps' = binarize1 (freshA ps S) ps ps in
    if ps = ps' then ps else binarize S ps')"
  by auto
termination
proof
  let ?R = "measure (\<lambda>(S,ps). badNtsCount (set ps))"
  show "wf ?R" by fast
  fix S :: "'n::fresh0"
  and ps ps' :: "('n,'t) prods"
  let ?A = "freshA ps S"
  assume ps'_def: "ps' = binarize1 ?A ps ps"
         and neq: "ps \<noteq> ps'"
  moreover with freshA_notin_set have "?A \<notin> Nts (set ps) \<union> {S}" by blast
  ultimately show "((S,ps'),(S,ps)) \<in> ?R" 
    using binarize1_dec_badNtsCount by force
qed

lemma binarize_binRtc:
  "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeStep A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* (set ps) (set (binarize S ps))"
proof (induction "badNtsCount (set ps)" arbitrary: ps rule: less_induct)
  case less
  let ?A = "freshA ps S"
  have A_notin_nts: "?A \<notin> Nts (set ps) \<union> {S}"
    using freshA_notin_set by metis
  consider (eq) "binarize1 ?A ps ps = ps" |
           (neq) "binarize1 ?A ps ps \<noteq> ps" by blast
  then show ?case 
  proof cases
    case neq
    let ?ps' = "binarize1 ?A ps ps"
    from binarize1_dec_badNtsCount[OF neq A_notin_nts] have
      "badNtsCount (set ?ps') < badNtsCount (set ps)" .
    with less have "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeStep A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* (set ?ps') (set (binarize S ?ps'))"
      by blast
    moreover from neq A_notin_nts obtain B\<^sub>1 B\<^sub>2 where "binarizeStep ?A B\<^sub>1 B\<^sub>2 S (set ps) (set ?ps')"
      using binarize1_binarized by blast
    ultimately show ?thesis 
      by (smt (verit, best) binarize.simps
          converse_rtranclp_into_rtranclp)
  qed simp
qed

lemma binarize_preserves_uniform:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes ps_uniform: "uniform (set ps)"
    shows "uniform (set (binarize S ps))"
using assms proof (induction "badNtsCount (set ps)" arbitrary: ps rule: less_induct)
  case less
  let ?A = "freshA ps S"
  consider (rec) "binarize1 ?A ps ps \<noteq> ps" | (no_rec) "binarize1 ?A ps ps = ps" by blast
  then show ?case 
  proof cases
    case rec
    let ?ps' = "binarize1 ?A ps ps"
    from rec have "binarize S ps = binarize S ?ps'" 
      by (smt (verit) binarize.elims)
    with less binarize1_dec_badNtsCount[OF rec] freshA_notin_set 
      binarize1_preserves_uniform
      show ?thesis by metis
  qed (use less in simp)
qed

lemma binarize_preserves_binary:
  assumes binary: "binary (set ps)"
      and ps'_def: "ps' = binarize S ps"
    shows "binary (set ps')"
proof -
  from binary have "badNtsCount (set ps) = 0"
    by (metis badNtsCountNot0 binary_def bot_nat_0.not_eq_extremum leD le_imp_less_Suc numeral_2_eq_2
        numeral_3_eq_3 split_conv list.set_finite)
  hence "binarize S ps = ps" using binarize1_dec_badNtsCount freshA_notin_set 
    by (smt (verit, best) binarize.simps bot_nat_0.extremum_strict)
  with assms show ?thesis by argo
qed

lemma binarize_binary_if_uniform:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes ps'_def: "ps' = binarize S ps"
      and uniform: "uniform (set ps)"
    shows "binary (set ps')"
proof -
  consider (bin) "binary (set ps)" | (not_bin) "\<not>binary (set ps)" by blast
  then show ?thesis
  proof cases
    case bin
    then show ?thesis using ps'_def binarize_preserves_binary by blast
  next
    case not_bin
    with uniform binary_badNtsCount obtain n where Suc_badNts: "badNtsCount (set ps) = Suc n" 
      using not0_implies_Suc by blast
    with uniform ps'_def show ?thesis 
    proof (induction "badNtsCount (set ps)" arbitrary: ps ps' n rule: less_induct)
      case less
      let ?A = "freshA ps S"
      from less badNts_impl_binarize1_not_id_unif have "binarize1 ?A ps ps \<noteq> ps"
        by fastforce
      hence badNtsCount_dec: "badNtsCount (set (binarize1 ?A ps ps)) < badNtsCount (set ps)" 
                              (is "badNtsCount ?ps' < _")
        using freshA_notin_set binarize1_dec_badNtsCount by metis
      consider (zero_badNts) "badNtsCount ?ps' = 0" | (Suc_badNts) m where "badNtsCount ?ps' = Suc m"
        using not0_implies_Suc by blast
      then show ?case
      proof cases
        case zero_badNts
        moreover from less.prems(1) binarize1_preserves_uniform have "uniform ?ps'" 
          by blast
        ultimately show ?thesis using binary_badNtsCount
          by (smt (verit, ccfv_threshold) List.finite_set binarize.elims binarize_preserves_binary
              freshA_def less.prems(2))
      next
        case Suc_badNts
        moreover from less.prems(1) binarize1_preserves_uniform have unif: "uniform ?ps'"
          by blast
        ultimately show ?thesis using less(1)[OF badNtsCount_dec _ _ Suc_badNts] 
          by (smt (verit, best) binarize.simps freshA_def less.prems(2))
      qed
    qed
  qed
qed


subsection \<open>Conversion to CNF\<close>

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

definition cnf_of :: "('n::fresh0, 't) prods \<Rightarrow> 'n \<Rightarrow> ('n,'t) prods" where
  "cnf_of ps S = (binarize S \<circ> uniformize S \<circ> unit_elim \<circ> eps_elim) ps"

theorem cnf_lemma: 
  assumes "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeStep A B\<^sub>1 B\<^sub>2 S x y)^** (set (uniformize S ps)) P''"
  shows "lang ps S = Lang P'' S"
  using assms cnf_lemma2Nt
  by (metis (mono_tags, lifting) Un_insert_right insert_iff lang_uniformize)

theorem cnf_of_CNF_Lang:
  fixes ps :: "('n::fresh0, 't) prods"
  shows "CNF (set(cnf_of ps S))" "lang (cnf_of ps S) S = lang ps S - {[]}"
proof -
  let ?ps1 = "eps_elim ps" let ?ps2 = "unit_elim ?ps1"
  let ?ps3 = "uniformize S ?ps2" let ?ps4 = "binarize S ?ps3"
  have "eps_free ?ps1" by (rule eps_free_eps_elim)
  hence "eps_free ?ps2" by (meson unit_elim_correct unit_elim_rel_Eps_free)
  have "Unit_free(set ?ps2)" by (metis unit_elim_correct Unit_free_if_unit_elim_rel)
  have "eps_free ?ps3" by(rule eps_free_uniformize[OF \<open>eps_free ?ps2\<close>])
  have "Unit_free(set ?ps3)" by (rule Unit_free_uniformize[OF \<open>Unit_free(set ?ps2)\<close>])
  have "uniform (set ?ps3)" by (rule uniform_uniformize)

  have "eps_free ?ps4"
    using binarize_binRtc binarizeStepRtc_Eps_free[OF _ \<open>eps_free ?ps3\<close>] by meson
  moreover have "Unit_free(set ?ps4)"
    using binarize_binRtc binarizeStepRtc_Unit_free[OF _ \<open>Unit_free(set ?ps3)\<close>] by meson
  moreover have "uniform (set ?ps4)"
    by(rule binarize_preserves_uniform[OF \<open>uniform (set ?ps3)\<close>])
  moreover have "binary (set ?ps4)"
    by (rule binarize_binary_if_uniform[OF refl \<open>uniform (set ?ps3)\<close>])
  ultimately show "CNF (set(cnf_of ps S))" unfolding CNF_eq cnf_of_def
    by(simp only: Let_def comp_def)

  have "lang ?ps4 S = lang ?ps3 S" using cnf_lemma binarize_binRtc by blast
  also have "\<dots> = lang ?ps2 S" by (simp add: lang_uniformize)
  also have "\<dots> = lang ?ps1 S" by (rule lang_unit_elim)
  also have "\<dots> = lang ps S - {[]}" by (rule lang_eps_elim)
  finally show "lang (cnf_of ps S) S = lang ps S - {[]}"
    by (simp add: cnf_of_def)
qed

corollary cnf_exists:
  fixes P :: "('n::fresh0,'t) Prods"
  assumes "finite P"
  shows "\<exists>P'::('n,'t)Prods. finite P' \<and> CNF P' \<and> Lang P' S = Lang P S - {[]}"
proof -
  obtain ps where "P = set ps" by (metis finite_list[OF assms])
  with cnf_of_CNF_Lang[of ps] show ?thesis by blast
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

unused_thms

end
