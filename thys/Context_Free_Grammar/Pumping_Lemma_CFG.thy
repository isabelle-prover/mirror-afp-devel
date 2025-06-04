(* Author: August Martin Stimpfle, Tobias Nipkow
   Original theory by Thomas Ammer
*)

section "Pumping Lemma for Context Free Grammars"

theory Pumping_Lemma_CFG
imports
  "List_Power.List_Power"
  Chomsky_Normal_Form
begin

text \<open>Paths in the (implicit) parse tree of the derivation of some terminal word;
specialized for productions in CNF.\<close>

inductive path :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool"
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>\<langle>_\<rangle>/ _))" [50, 0, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[A]\<rangle> [a]" |
left:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<and> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v)\<rbrakk> \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p\<rangle> (w@v)" |
right:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<and> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v)\<rbrakk> \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#q\<rangle> (w@v)"

(* rules for derivations of words if the grammar is in cnf, resembles binary syntax trees *)
inductive cnf_derives :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_/ \<Rightarrow>cnf/ _))" [50, 0, 50] 50) where
step:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>cnf [a]"|
trans:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> P \<turnstile> B \<Rightarrow>cnf w \<and> P \<turnstile> C \<Rightarrow>cnf v\<rbrakk> \<Longrightarrow> P \<turnstile> A \<Rightarrow>cnf (w@v)"

lemma path_if_cnf_derives: "P \<turnstile> S \<Rightarrow>cnf w \<Longrightarrow> \<exists>p. P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  by (induction rule: cnf_derives.induct) (auto intro: path.intros)

lemma cnf_derives_if_path: "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> P \<turnstile> S \<Rightarrow>cnf w"
  by (induction rule: path.induct) (auto intro: cnf_derives.intros)

corollary cnf_path: "P \<turnstile> S \<Rightarrow>cnf w \<longleftrightarrow> (\<exists>p. P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w)"
  using path_if_cnf_derives[of P] cnf_derives_if_path[of P] by blast

lemma cnf_der: 
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w" "CNF P" 
  shows "P \<turnstile> S \<Rightarrow>cnf w"
using assms proof (induction w arbitrary: S rule: length_induct)
  case (1 w)
  have "Eps_free P"
    using assms(2) CNF_eq by blast
  hence "\<not>(P \<turnstile> [Nt S] \<Rightarrow>* [])"
    by (simp add: Eps_free_derives_Nil)
  hence 2: "length w \<noteq> 0" 
    using 1 by auto
  thus ?case
  proof (cases "length w \<le> 1")
    case True
    hence "length w = 1"
      using 2 by linarith
    then obtain t where "w = [t]"
      using length_Suc_conv[of w 0] by auto 
    hence "(S, [Tm t]) \<in> P"
      using 1 assms(2) cnf_single_derive[of P S t] by simp
    thus ?thesis
      by (simp add: \<open>w = _\<close> cnf_derives.intros(1))
  next
    case False 
    obtain A B u v where ABuv: "(S, [Nt A, Nt B]) \<in> P \<and> P \<turnstile> [Nt A] \<Rightarrow>* map Tm u \<and> P \<turnstile> [Nt B] \<Rightarrow>* map Tm v \<and> u@v = w \<and> u \<noteq> [] \<and> v \<noteq> []"
      using False assms(2) 1 cnf_word[of P S w] by auto
    have "length u < length w \<and> length v < length w"
      using ABuv by auto
    hence "cnf_derives P A u \<and> cnf_derives P B v"
      using 1 ABuv by blast
    thus ?thesis
      using ABuv cnf_derives.intros(2)[of S A B P u v] by blast
  qed
qed

lemma der_cnf:
  assumes "P \<turnstile> S \<Rightarrow>cnf w" "CNF P"
  shows "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
using assms proof (induction rule: cnf_derives.induct)
  case (step A a P)
  then show ?case 
    by (simp add: derive_singleton r_into_rtranclp)
next
  case (trans A B C P w v)
  hence "P \<turnstile> [Nt A] \<Rightarrow> [Nt B, Nt C]"
    by (simp add: derive_singleton)
  moreover have "P \<turnstile> [Nt B] \<Rightarrow>* map Tm w \<and> P \<turnstile> [Nt C] \<Rightarrow>* map Tm v"
    using trans by blast
  ultimately show ?case 
    using derives_append_decomp[of P \<open>[Nt B]\<close> \<open>[Nt C]\<close> \<open>map Tm (w @ v)\<close>] by auto
qed

corollary cnf_der_eq: "CNF P \<Longrightarrow> (P \<turnstile> [Nt S] \<Rightarrow>* map Tm w \<longleftrightarrow> P \<turnstile> S \<Rightarrow>cnf w)"
  using cnf_der[of P S w] der_cnf[of P S w] by blast

lemma path_if_derives: 
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w" "CNF P" 
  shows "\<exists>p. P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  using assms cnf_der[of P S w] path_if_cnf_derives[of P S w] by blast

lemma derives_if_path:
  assumes "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w" "CNF P"
  shows "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
  using assms der_cnf[of P S w] cnf_derives_if_path[of P S p w] by blast

text \<open>\<open>lpath\<close> = longest path, similar to \<open>path\<close>; \<open>lpath\<close> always chooses the longest path in a syntax tree\<close>
inductive lpath :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool" 
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>\<llangle>_\<rrangle>/ _))" [50, 0, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<llangle>[A]\<rrangle> [a]" |
nonTerminals:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> (P \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> w) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>q\<rrangle> v)\<rbrakk> \<Longrightarrow> 
                P \<turnstile> A \<Rightarrow>\<llangle>A#(if length p \<ge> length q then p else q)\<rrangle> (w@v)" 

lemma path_lpath: "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>p'. (P \<turnstile> S \<Rightarrow>\<llangle>p'\<rrangle> w) \<and> length p' \<ge> length p"
  by (induction rule: path.induct) (auto intro: lpath.intros)

lemma lpath_path: "(P \<turnstile> S \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  by (induction rule: lpath.induct) (auto intro: path.intros)

(*Property of the a binary tree: Since the tree is a binary tree, word lengths are always \<le> 2^(longest path-1).
However, this version is easier to use/proof and suffices *)
lemma lpath_length: "(P \<turnstile> S \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> length w \<le> 2^length p"
proof (induction rule: lpath.induct)
  case (terminal A a P)
  then show ?case by simp
next
  case (nonTerminals A B C P p w q v)
  then show ?case 
  proof (cases "length p \<ge> length q")
    case True
    hence "length v \<le> 2^length p"
      using nonTerminals order_subst1[of \<open>length v\<close> \<open>\<lambda>x. 2^x\<close> \<open>length q\<close> \<open>length p\<close>] by simp
    hence "length w +length v \<le> 2*2^length p"
      by (simp add: nonTerminals.IH(1) add_le_mono mult_2)
    then show ?thesis
      by (simp add: True)
  next
    case False
    hence "length w \<le> 2^length q"
      using nonTerminals order_subst1[of \<open>length w\<close> \<open>\<lambda>x. 2^x\<close> \<open>length p\<close> \<open>length q\<close>] by simp 
    hence "length w +length v \<le> 2*2^length q"
      by (simp add: nonTerminals.IH add_le_mono mult_2)
    then show ?thesis
      by (simp add: False)
  qed
qed

lemma step_decomp:
  assumes "P \<turnstile> A \<Rightarrow>\<langle>[A]@p\<rangle> w" " length p \<ge> 1" 
  shows "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> P \<and> w =a@b \<and>
        ((P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> a \<and> P \<turnstile> C \<Rightarrow>\<langle>p'\<rangle> b) \<or> (P \<turnstile> B \<Rightarrow>\<langle>p'\<rangle> a \<and> P \<turnstile> C \<Rightarrow>\<langle>p\<rangle> b))"
  using assms by (cases) fastforce+

lemma steplp_decomp:
  assumes "P \<turnstile> A \<Rightarrow>\<llangle>[A]@p\<rrangle> w" " length p \<ge> 1" 
  shows "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> P \<and> w =a@b \<and>
      ((P \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b \<and> length p \<ge> length p') \<or>
       (P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p\<rrangle> b \<and> length p \<ge> length p'))"
  using assms by (cases) fastforce+

lemma path_first_step: "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>q. p = [A]@q "
  by (induction rule: path.induct) simp_all

lemma no_empty: "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> length w > 0"
  by (induction rule: path.induct) simp_all

lemma substitution: 
  assumes "P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p2\<rangle> z"
  shows "\<exists>v w x. P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w \<and> z = v@w@x \<and>
        (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@w'@x) \<and>
        (length p1 > 0 \<longrightarrow> length (v@x) > 0)"
using assms proof (induction p1 arbitrary: P A z)
  case Nil
  hence "\<forall>w' p'. ((P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> z) \<and> z = []@z@[] \<and>
        (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[]@[X]@p'\<rangle> ([]@w'@[])) \<and>
        (length [] > 0 \<longrightarrow> length ([]@[]) > 0))"
    using path_first_step[of P A] by auto
  then show ?case 
    by blast
next
  case (Cons A p1 P Y)
  hence 0: "A = Y"
    using path_first_step[of P Y] by fastforce 
  have "length (p1@[X]@p2) \<ge> 1"
    by simp
  hence "\<exists>B C a b q. (A, [Nt B, Nt C]) \<in> P \<and> a@b = z \<and> 
        ((P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b) \<or> (P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p2\<rangle> a \<and> P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> b))"
    using Cons.prems path_first_step step_decomp by fastforce
  then obtain B C a b q where BC: "(A, [Nt B, Nt C]) \<in> P \<and> a@b = z \<and> 
        ((P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b) \<or> (P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p2\<rangle> a \<and> P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> b))"
    by blast
  then show ?case
  proof (cases "P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b")
    case True
    then obtain v w x where vwx: "P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w \<and> b = v@w@x \<and> 
          (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@w'@x))"
      using Cons.IH by blast
    hence 1: "\<forall>w' p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (a@v@w'@x)"
      using BC by (auto intro: path.intros(3))
    obtain v' where "v' = a@v"
      by simp
    hence "length (v'@x) > 0"
      using True no_empty by fast
    hence "P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w \<and> z = v'@w@x \<and> (\<forall>w' p'.
           P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v'@w'@x)) \<and>
          (length (A#p1) > 0 \<longrightarrow> length (v'@x) >0)"
      using vwx 1 BC \<open>v' = _\<close> by simp
    thus ?thesis
      using 0 by auto
  next
    case False
    then obtain v w x where vwx: "(P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> a = v@w@x \<and> 
          (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@w'@x))"
      using Cons.IH BC by blast
    hence 1: "\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@w'@x@b)"
      using BC left[of A B C P] by fastforce
    hence "P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w \<and> z = v@w@x@b \<and> (\<forall>w' p'.
           P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@w'@x@b)) \<and>
          (length (A#p1) > 0 \<longrightarrow> length (a@v@x) >0)"
      using vwx BC no_empty by fastforce
    moreover have "length (v@x@b) > 0"
      using no_empty BC by fast
    ultimately show ?thesis
    using 0 by auto
  qed
qed

lemma substitution_lp: 
  assumes "P \<turnstile> A \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> z"
  shows "\<exists>v w x. P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w \<and> z = v@w@x \<and>
        (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@w'@x)"
using assms proof (induction p1 arbitrary: P A z)
  case Nil
  hence "\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[]@[X]@p'\<rangle> ([]@w'@[])"
    using path_first_step lpath_path by fastforce
  moreover have "P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> z \<and> z = []@z@[]"
    using Nil lpath.cases[of P A \<open>[X] @ p2\<close> z] by auto
  ultimately show ?case 
    by blast
next
  case (Cons A p1 P Y)
  hence 0: "A = Y"
    using path_first_step[of P Y] lpath_path by fastforce 
  have "length (p1@[X]@p2) \<ge> 1"
    by simp
  hence "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> P \<and> z = a@b \<and> 
        ((P \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b \<and> length (p1@[X]@p2) \<ge> length p') \<or> 
         (P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b \<and> length (p1@[X]@p2) \<ge> length p'))"
    using steplp_decomp[of P A \<open>p1@[X]@p2\<close> z] 0 Cons by simp
  then obtain B C p' a b where BC: "(A, [Nt B, Nt C]) \<in> P \<and> z = a@b \<and> 
        ((P \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b \<and> length (p1@[X]@p2) \<ge> length p') \<or> 
         (P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b \<and> length (p1@[X]@p2) \<ge> length p'))"
    by blast
  then show ?case
  proof (cases "P \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b \<and> length (p1@[X]@p2) \<ge> length p'")
    case True
    then obtain v w x where vwx: "P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w \<and> a = v@w@x \<and> 
          (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@w'@x)"
      using Cons.IH by blast
    hence "P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w \<and> z = v@w@x@b \<and>
       (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> v@w'@x@b)"
      using BC lpath_path[of P] path.intros(2)[of A B C P] by fastforce
    then show ?thesis
      using 0 by auto
  next
    case False
    hence "(P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a \<and> P \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b \<and> length (p1@[X]@p2) \<ge> length p')"
      using BC by blast
    then obtain v w x where vwx: "P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w \<and> b = v@w@x \<and> 
          (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@w'@x)"
      using Cons.IH by blast
    then obtain v' where "v' = a@v"
      by simp
    hence "P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w \<and> z = v'@w@x \<and>
       (\<forall>w' p'. P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> v'@w'@x)"
      using BC lpath_path[of P] path.intros(3)[of A B C P] vwx by fastforce
    then show ?thesis
      using 0 by auto
  qed
qed

lemma path_nts: "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> set p \<subseteq> Nts P"
  unfolding Nts_def by (induction rule: path.induct) auto

lemma inner_aux: 
  assumes "\<forall>w' p'. P \<turnstile> A \<Rightarrow>\<langle>[A]@p3\<rangle> w \<and> (P \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> w' \<longrightarrow>
          P \<turnstile> A \<Rightarrow>\<langle>[A]@p2@[A]@p'\<rangle> v@w'@x)"
  shows "P \<turnstile> A \<Rightarrow>\<langle>(([A]@p2)^^(Suc i)) @ [A]@p3\<rangle> v^^(Suc i) @ w @ x^^(Suc i)"
  using assms proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  hence 1: "P \<turnstile> A \<Rightarrow>\<langle>[A]@p2@ ([A] @ p2)^^i @ [A]@p3\<rangle> v^^(Suc i) @ w @ x^^(Suc i)"
    by simp
  hence "P \<turnstile> A \<Rightarrow>\<langle>[A] @ p2 @ [A] @ p2@ ([A] @ p2)^^i @ [A]@p3\<rangle> v @ v^^(Suc i) @ w @ x^^(Suc i) @ x"
    using assms by fastforce
  thus ?case 
    using pow_list_Suc2[of \<open>Suc i\<close> x] by simp
qed

lemma inner_pumping: 
  assumes "CNF P" "finite P"
    and "m = card (Nts P)"
    and "z \<in> Lang P S"
    and "length z \<ge> 2^(m+1)"
  shows "\<exists>u v w x y . z = u@v@w@x@y \<and> length (v@w@x) \<le> 2^(m+1) \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v^^i)@w@(x^^i)@y \<in> Lang P S)"
proof -
  obtain p' where p': "P \<turnstile> S \<Rightarrow>\<langle>p'\<rangle> z"
    using assms Lang_def[of P S] path_if_derives[of P S] by blast
  then obtain lp where lp: "P \<turnstile> S \<Rightarrow>\<llangle>lp\<rrangle> z"
    using path_lpath[of P] by blast
  hence 1: "set lp \<subseteq> Nts P"
    using lpath_path[of P] path_nts[of P] by blast
  have "length lp > m"
  proof -
    have "(2^(m+1)::nat) \<le> 2^length lp"
      using lp lpath_length[of P S lp z] assms(5) le_trans by blast
    hence "m+1 \<le> length lp" 
      using power_le_imp_le_exp[of 2 \<open>m+1\<close> \<open>length lp\<close>] by auto
    thus ?thesis
      by simp
  qed
  then obtain l p where p: "lp = l@p \<and> length p = m+1"
    using less_Suc_eq by (induction lp) fastforce+
  hence "set l \<subseteq> Nts P \<and> set p \<subseteq> Nts P \<and> finite (Nts P)"
    using \<open>finite P\<close> 1 finite_Nts[of P] assms(1) by auto
  hence "card (set p) < length p"
    using p assms(3) card_mono[of \<open>Nts P\<close> \<open>set p\<close>] by simp
  then obtain A p1 p2 p3 where "p = p1@[A]@p2@[A]@p3"
    by (metis distinct_card nat_neq_iff not_distinct_decomp)
  then obtain u vwx y where uy: "(P \<turnstile> A \<Rightarrow>\<llangle>[A]@p2@[A]@p3\<rrangle> vwx \<and> z = u@vwx@y \<and>
        (\<forall>w' p'. (P \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> w' \<longrightarrow> P \<turnstile> S \<Rightarrow>\<langle>l@p1@[A]@p'\<rangle> u@w'@y)))"
    using substitution_lp[of P S \<open>l@p1\<close> A \<open>p2@[A]@p3\<close> z] lp p by auto
  hence "length vwx \<le> 2^(m+1)"
    using \<open>p = _\<close> p lpath_length[of P A \<open>[A] @ p2 @ [A] @ p3\<close> vwx] order_subst1 by fastforce
  then obtain v w x where vwx: "P \<turnstile> A \<Rightarrow>\<langle>[A]@p3\<rangle> w \<and> vwx = v@w@x \<and>
        (\<forall>w' p'. (P \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> w' \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[A]@p2@[A]@p'\<rangle> v@w'@x)) \<and>
        (length ([A]@p2) > 0 \<longrightarrow> length (v@x) > 0)"
    using substitution[of P A \<open>[A]@p2\<close> A p3 vwx] uy lpath_path[of P A] by auto
  have "P \<turnstile> S \<Rightarrow>\<langle>l@p1@ (([A]@p2)^^i) @[A]@p3\<rangle> u@(v^^i)@w@(x^^i)@y" for i
  proof -
    have "\<forall>i. P \<turnstile> A \<Rightarrow>\<langle>([A]@p2)^^(Suc i) @ [A]@p3\<rangle> v^^(Suc i) @ w @ x^^(Suc i)"
      using vwx inner_aux[of P A] by blast
    hence "\<forall>i. P \<turnstile> S \<Rightarrow>\<langle>l@p1@(([A]@p2)^^(Suc i)) @[A]@p3\<rangle> u@ (v^^(Suc i)) @ w @ (x^^(Suc i)) @y"
      using uy by fastforce
    moreover have "P \<turnstile> S \<Rightarrow>\<langle>l@p1@(([A]@p2)^^0) @[A]@p3\<rangle> u@ (v^^0) @ w @ (x^^0) @y"
      using vwx uy by auto
    ultimately show "P \<turnstile> S \<Rightarrow>\<langle>l@p1@ (([A]@p2)^^i) @[A]@p3\<rangle> u@(v^^i)@w@(x^^i)@y"
      by (induction i) simp_all
  qed
  hence "\<forall>i. u@(v^^i)@w@(x^^i)@y \<in> Lang P S"
    unfolding Lang_def using assms(1) assms(2) derives_if_path[of P S] by blast
  hence "z = u@v@w@x@y \<and> length (v@w@x) \<le> 2^(m+1) \<and> 1 \<le> length (v@x) \<and> (\<forall> i. u@(v^^i)@w@(x^^i)@ y \<in> Lang P S)"
    using vwx uy \<open>length vwx \<le> 2 ^ (m + 1)\<close> by (simp add: Suc_leI)
  then show ?thesis
    by blast
qed

abbreviation "pumping_property L n \<equiv> \<forall>z \<in> L. length z \<ge> n \<longrightarrow>
  (\<exists>u v w x y. z = u @ v @ w @ x @ y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1
        \<and> (\<forall>i. u @ v^^i @ w @ x^^i @ y \<in> L))"

theorem Pumping_Lemma_CNF:
  assumes "CNF P" "finite P"
  shows "\<exists>n. pumping_property (Lang P S) n"
using inner_pumping[OF assms, of \<open>card (Nts P)\<close>] by blast

theorem Pumping_Lemma:
  assumes "finite (P :: ('n::infinite,'t)Prods)"
  shows "\<exists>n. pumping_property (Lang P S) n"
proof -
  obtain ps where "set ps = P" using finite_list[OF assms] by blast
  obtain ps' :: "('n,'t)prods" where ps': "CNF(set ps')" "lang ps' S= lang ps S - {[]}"
    using cnf_exists[of S ps] by auto
  let ?P' = "set ps'"
  have P': "CNF ?P'" "finite ?P'" using ps'(1) by auto
  from Pumping_Lemma_CNF[OF P', of S] obtain n where
    pump: "pumping_property (Lang ?P' S) n" by blast
  then have "pumping_property (Lang ?P' S) (Suc n)"
    by (metis Suc_leD nle_le)
  then have "pumping_property (Lang P S) (Suc n)"
    using ps'(2) \<open>set ps = P\<close> by (metis Diff_iff list.size(3) not_less_eq_eq singletonD zero_le)
  then show ?thesis by blast
qed

end