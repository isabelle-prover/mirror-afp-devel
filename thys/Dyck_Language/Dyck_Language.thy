(* Author: Moritz Roos, Tobias Nipkow *)

section "Dyck Languages"

theory Dyck_Language
imports Main
begin

text \<open>Dyck languages are sets of words/lists of balanced brackets. A bracket is a pair of type
\<^typ>\<open>bool \<times> 'a\<close> where \<open>True\<close> is an opening and \<open>False\<close> a closing bracket.
That is, brackets are tagged with elements of type \<open>'a\<close>.\<close>

type_synonym 'a bracket = "bool \<times> 'a"

abbreviation "Open a \<equiv> (True,a)"
abbreviation "Close a \<equiv> (False,a)"


subsection\<open>Balanced, Inductive and Recursive\<close>

text\<open>Definition of what it means to be a \emph{balanced} list of brackets:\<close>

inductive bal :: "'a bracket list \<Rightarrow> bool" where
  "bal []" |
  "bal xs \<Longrightarrow> bal ys \<Longrightarrow> bal (xs @ ys)" | 
  "bal xs \<Longrightarrow> bal (Open a # xs @ [Close a])" 

declare bal.intros(1)[iff] bal.intros(2)[intro,simp] bal.intros(3)[intro,simp]

lemma bal2[iff]: "bal [Open a, Close a]" 
  using bal.intros(3)[of "[]"] by simp

text \<open>The inductive definition of balanced is complemented with a functional version
that uses a stack to remember which opening brackets need to be closed:\<close>

fun bal_stk :: "'a list \<Rightarrow> 'a bracket list \<Rightarrow> 'a list * 'a bracket list" where
  "bal_stk s [] = (s,[])" |
  "bal_stk s (Open a # bs) = bal_stk (a # s) bs" |
  "bal_stk (a' # s) (Close a # bs) =
    (if a = a' then bal_stk s bs else (a' # s, Close a # bs))" | 
  "bal_stk bs stk = (bs,stk)"

lemma bal_stk_more_stk: "bal_stk s1 xs = (s1',[]) \<Longrightarrow> bal_stk (s1@s2) xs = (s1'@s2,[])"
by(induction s1 xs arbitrary: s2 rule: bal_stk.induct) (auto split: if_splits)

lemma bal_stk_if_Nils[simp]: "ASSUMPTION(bal_stk [] bs = ([], [])) \<Longrightarrow> bal_stk s bs = (s, [])"
unfolding ASSUMPTION_def using bal_stk_more_stk[of "[]" _ "[]"] by simp

lemma bal_stk_append:
  "bal_stk s (xs @ ys)
   = (let (s',xs') = bal_stk s xs in if xs' = [] then bal_stk s' ys else (s', xs' @ ys))"
by(induction s xs rule:bal_stk.induct) (auto split: if_splits)

lemma bal_stk_append_if:
  "bal_stk s1 xs = (s2,[]) \<Longrightarrow> bal_stk s1 (xs @ ys) = bal_stk s2 ys"
by(simp add: bal_stk_append[of _ xs])

lemma bal_stk_split:
  "bal_stk s xs = (s',xs') \<Longrightarrow> \<exists>us. xs = us@xs' \<and> bal_stk s us = (s',[])"
by(induction s xs rule:bal_stk.induct) (auto split: if_splits)


subsection "Equivalence of @{const bal} and @{const bal_stk}"

lemma bal_stk_if_bal:  "bal xs \<Longrightarrow> bal_stk s xs = (s,[])"
by(induction arbitrary: s rule: bal.induct)(auto simp: bal_stk_append_if split: if_splits)

lemma bal_insert_AB:
  "bal (v @ w) \<Longrightarrow> bal (v @ (Open a # Close a # w))"
proof(induction "v @ w" arbitrary: v w rule: bal.induct)
  case 1 thus ?case by blast
next
  case (3 u b)
  then show ?case
  proof (cases v)
    case Nil
    hence "w = Open b # u @ [Close b]"
      using "3.hyps"(3) by fastforce
    hence "bal w" using "3.hyps" 
      by blast
    hence "bal ([Open a, Close a] @ w)" 
      by blast
    thus ?thesis using Nil by simp
  next
    case [simp]: (Cons x v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      from "3.hyps" have "bal ((Open a # u @ [Close a]) @ [Open a, Close a])"
        using bal.intros(2) by blast
      thus ?thesis using Nil Cons 3
        by (metis append_Nil append_Nil2 bal.simps)
    next
      case (snoc w' y)
      thus ?thesis
        using "3.hyps"(2,3) bal.intros(3) by force 
    qed
  qed
next
  case (2 v' w')
  then obtain r where "v'=v@r \<and> r@w'=w \<or> v'@r=v \<and> w'=r@w"
    by (meson append_eq_append_conv2)
  thus ?case
    using "2.hyps" bal.intros(2) by force
qed 

lemma bal_if_bal_stk: "bal_stk s w = ([],[]) \<Longrightarrow> bal (rev(map (\<lambda>x. Open x) s) @ w)"
proof(induction s w rule: bal_stk.induct)
  case 2
  then show ?case by simp
next
  case 3
  then show ?case by (auto simp add: bal_insert_AB split: if_splits) 
qed (auto)

corollary bal_iff_bal_stk: "bal w \<longleftrightarrow> bal_stk [] w = ([],[])"
using bal_if_bal_stk[of "[]"] bal_stk_if_bal by auto


subsection\<open>More properties of \<^const>\<open>bal\<close>, using \<^const>\<open>bal_stk\<close>\<close>

theorem bal_append_inv: "bal (u @ v) \<Longrightarrow> bal u \<Longrightarrow> bal v"
  using bal_stk_append_if bal_iff_bal_stk by metis

lemma bal_insert_bal_iff[simp]: 
  "bal b \<Longrightarrow> bal (v @ b @ w) = bal (v@w)" 
unfolding bal_iff_bal_stk by(auto simp add: bal_stk_append split: prod.splits if_splits)

lemma bal_start_Open: \<open>bal (x#xs) \<Longrightarrow>\<exists>a. x = Open a\<close>
  using bal_stk.elims bal_iff_bal_stk by blast 

lemma bal_Open_split: assumes \<open>bal (x # xs)\<close>
  shows \<open>\<exists>y r a. bal y \<and> bal r \<and> x = Open a \<and> xs = y @ Close a # r\<close>
proof-
  from assms obtain a where \<open>x = Open a\<close> 
    using bal_start_Open by blast
  have \<open>bal (Open a # xs) \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> xs = y @ Close a # r\<close>
  proof(induction \<open>length xs\<close> arbitrary: xs rule: less_induct)
    case less
    have IH: \<open>\<And>w. \<lbrakk>length w < length xs; bal (Open a # w)\<rbrakk> \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> w = y @ Close a # r\<close> 
      using less by blast
    have \<open>bal (Open a # xs)\<close> 
      using less by blast
    from less(2) show ?case
    proof(induction \<open>Open a # xs\<close> rule: bal.induct)
      case (2 as bs)
      consider (as_empty) \<open>as = []\<close> | (bs_empty) \<open>bs = []\<close> | (both_not_empty) \<open>as \<noteq> [] \<and> bs \<noteq> []\<close> by blast
      then show ?case
      proof(cases)
        case as_empty
        then show ?thesis using 2 by (metis append_Nil)
      next
        case bs_empty
        then show ?thesis using 2 by (metis append_self_conv)
      next
        case both_not_empty
        then obtain as' where as'_def: \<open>Open a # as' = as\<close> 
          using 2 by (metis append_eq_Cons_conv)
        then have \<open>length as' < length xs\<close>
          using "2.hyps"(5) both_not_empty by fastforce
        with IH \<open>bal as\<close> obtain y r where yr: \<open>bal y \<and> bal r \<and> as' = y @ Close a # r\<close> 
          using as'_def by meson
        then have \<open>xs = y @ Close a # r @ bs\<close>
          using "2.hyps"(5) as'_def by fastforce 
        moreover have \<open>bal y\<close>
          using yr by blast
        moreover have \<open>bal (r@bs)\<close> 
          using yr by (simp add: "2.hyps"(3))
        ultimately show ?thesis by blast
      qed
    next
      case (3 xs)
      then show ?case by blast    
    qed
  qed
  then show ?thesis using assms \<open>x = _\<close> by blast
qed


subsection\<open>Dyck Language over an Alphabet\<close>

text\<open>The Dyck/bracket language over a set \<open>\<Gamma>\<close> is the set of balanced words over \<open>\<Gamma>\<close>:\<close>

definition Dyck_lang :: "'a set \<Rightarrow> 'a bracket list set" where
"Dyck_lang \<Gamma> = {w. bal w \<and> snd ` (set w) \<subseteq> \<Gamma>}"

lemma Dyck_langI[intro]: 
  assumes \<open>bal w\<close>
    and \<open>snd ` (set w) \<subseteq> \<Gamma>\<close>
  shows \<open>w \<in> Dyck_lang \<Gamma>\<close>
  using assms unfolding Dyck_lang_def by blast

lemma Dyck_langD[dest]:
  assumes \<open>w \<in> Dyck_lang \<Gamma>\<close>
  shows \<open>bal w\<close>
    and \<open>snd ` (set w) \<subseteq> \<Gamma>\<close>
  using assms unfolding Dyck_lang_def by auto

text\<open>Balanced subwords are again in the Dyck Language.\<close>
lemma Dyck_lang_substring:
  \<open>bal w \<Longrightarrow> u @ w @ v \<in> Dyck_lang \<Gamma> \<Longrightarrow> w \<in> Dyck_lang \<Gamma>\<close>
unfolding Dyck_lang_def by auto

end