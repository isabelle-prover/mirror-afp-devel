(*
Authors: Kaan Taskin, Tobias Nipkow
*)

section \<open>Inlining a Single Production\<close>

theory Inlining1Prod
imports Context_Free_Grammar
begin

text 
\<open>A single production of \<open>(A,\<alpha>)\<close> can be removed from \<open>ps\<close> by inlining
(= replacing \<open>Nt A\<close> by \<open>\<alpha>\<close> everywhere in \<open>ps\<close>) without changing the language
if \<open>Nt A \<notin> set \<alpha>\<close> and \<open>A \<notin> lhss ps\<close>.\<close>

text
\<open>\<open>substP ps s u\<close> replaces every occurrence of the symbol \<open>s\<close> with the list of symbols \<open>u\<close> on the right-hand sides of the production list \<open>ps\<close>\<close>

definition substP :: "('n, 't) sym \<Rightarrow>  ('n, 't) syms \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
  "substP s u ps = map (\<lambda>(A,v). (A, substs s u v)) ps"

lemma substP_split: "substP s u (ps @ ps') = substP s u ps @ substP s u ps'"
  by (simp add: substP_def)

lemma substP_skip1: "s \<notin> set v \<Longrightarrow> substP s u ((A,v) # ps) = (A,v) # substP s u ps"
  by (auto simp add: substs_skip substP_def)

lemma substP_skip2: "s \<notin> syms ps \<Longrightarrow> substP s u ps = ps"
  by (induction ps) (auto simp add: substP_def substs_skip)

lemma substP_rev: "Nt B \<notin> syms ps \<Longrightarrow> substP (Nt B) [s] (substP s [Nt B] ps) = ps"
proof (induction ps)
  case Nil
  then show ?case
    by (simp add: substP_def)
next
  case (Cons a ps)
  let ?A = "fst a" let ?u = "snd a" let ?substs = "substs s [Nt B]"
  have "substP (Nt B) [s] (substP s [Nt B] (a # ps)) = substP (Nt B) [s] (map (\<lambda>(A,v). (A, ?substs v)) (a#ps))"
    by (simp add: substP_def)
  also have "... = substP (Nt B) [s] ((?A, ?substs ?u) # map (\<lambda>(A,v). (A, ?substs v)) ps)"
    by (simp add: case_prod_unfold)
  also have "... = map ((\<lambda>(A,v). (A, substsNt B [s] v))) ((?A, ?substs ?u) # map (\<lambda>(A,v). (A, ?substs v)) ps)"
    by (simp add: substP_def)
  also have "... = (?A, substsNt B [s] (?substs ?u)) # substP (Nt B) [s] (substP s [Nt B] ps)"
    by (simp add: substP_def)
  also from Cons have "... = (?A, substsNt B [s] (?substs ?u)) # ps"
    using set_subset_Cons unfolding Syms_def by auto
  also from Cons.prems have "... = (?A, ?u) # ps"
    using substs_rev unfolding Syms_def by force
  also have "... = a # ps" by simp
  finally show ?case .
qed

lemma substP_der:
  "(A,u) \<in> set (substP (Nt B) v ps) \<Longrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
proof -
  assume "(A,u) \<in> set (substP (Nt B) v ps)"
  then have "\<exists>u'. (A,u') \<in> set ps \<and> u = substsNt B v u'" unfolding substP_def by auto
  then obtain u' where u'_def: "(A,u') \<in> set ps \<and> u = substsNt B v u'" by blast
  then have path1: "set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u'"
    by (simp add: derive_singleton r_into_rtranclp)
  have "set ((B,v) # ps) \<turnstile> u' \<Rightarrow>* substsNt B v u'"
    using substs_der by (metis list.set_intros(1))
  with u'_def have path2: "set ((B,v) # ps) \<turnstile> u' \<Rightarrow>* u" by simp
  from path1 path2 show ?thesis by simp
qed

text\<open>A list of symbols \<open>u\<close> can be derived before inlining if \<open>u\<close> can be derived after inlining.\<close>

lemma if_part:
  "set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* u \<Longrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
proof (induction rule: derives_induct)
  case (step u A v w)
  then show ?case
    by (meson derives_append derives_prepend rtranclp_trans substP_der)
qed simp

text
\<open>For the other implication we need to take care that \<open>B\<close> can be derived in the original \<open>ps\<close>.
Thus, after inlining, \<open>B\<close> must also be substituted in the derived sentence \<open>u\<close>:\<close>

lemma only_if_lemma:
assumes "A \<noteq> B"
    and "B \<notin> lhss ps"
    and "Nt B \<notin> set v"
shows "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u \<Longrightarrow> set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* substsNt B v u"
proof (induction rule: derives_induct)
  case base
  then show ?case using assms(1) by simp
next
  case (step s B' w v')
  then show ?case
  proof (cases "B = B'")
    case True
    then have "v = v'" 
      using \<open>B \<notin> lhss ps\<close> step.hyps unfolding Lhss_def by auto
    then have "substsNt B v (s @ [Nt B'] @ w) = substsNt B v (s @ v' @ w)" 
      using step.prems \<open>Nt B \<notin> set v\<close> True by (simp add: substs_skip)
    then show ?thesis
      using step.IH by argo
  next
    case False
    then have "(B',v') \<in> set ps"
      using step by auto
    then have "(B', substsNt B v v') \<in> set (substP (Nt B) v ps)"
      by (metis (no_types, lifting) list.set_map pair_imageI substP_def)
    from derives_rule[OF this _ rtranclp.rtrancl_refl] step.IH False show ?thesis
      by simp
  qed
qed

text
\<open>With the assumption that the non-terminal \<open>B\<close> is not in the list of symbols \<open>u\<close>, \<open>substs u (Nt B) v\<close> reduces to \<open>u\<close>\<close>

corollary only_if_part: 
assumes "A \<noteq> B"
    and "B \<notin> lhss ps"
    and "Nt B \<notin> set v"
    and "Nt B \<notin> set u"
shows "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u \<Longrightarrow> set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* u"
by (metis assms substs_skip only_if_lemma)

text
\<open>Combining the two implications gives us the desired property of language preservation\<close>

lemma derives_inlining: 
assumes "B \<notin> lhss ps" and
        "Nt B \<notin> set v" and
        "Nt B \<notin> set u" and
        "A \<noteq> B"
shows "set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* u \<longleftrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
using assms if_part only_if_part by metis

end