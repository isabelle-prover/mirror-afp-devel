(*
Author: August Martin Stimpfle
Based on HOL4 theories by Aditi Barthwal
*)

section \<open>Elimination of Epsilon Productions\<close>

theory Epsilon_Elimination
imports Context_Free_Grammar
begin

inductive nullable :: "('n,'t) prods \<Rightarrow> ('n,'t) sym \<Rightarrow> bool"
for ps where
  NullableSym:
  "\<lbrakk> (A, w) \<in> set ps; \<forall>s \<in> set w. nullable ps s\<rbrakk>
  \<Longrightarrow> nullable ps (Nt A)"

abbreviation "nullables ps w \<equiv> (\<forall>s \<in> set w. nullable ps s)"

lemma nullables_if: 
  assumes "set ps \<turnstile> u \<Rightarrow>* v" 
    and "u=[a]" "nullables ps v"
  shows "nullables ps u"
  using assms
proof(induction arbitrary: a rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl u v w)
  from \<open>set ps \<turnstile> v \<Rightarrow> w\<close> obtain A \<alpha> l r where A\<alpha>: "v = l @ [Nt A] @ r \<and> w = l @ \<alpha> @ r \<and> (A, \<alpha>) \<in> set ps"
    by (auto simp: derive.simps)
  from this \<open>nullables ps w\<close> have "nullables ps \<alpha> \<and> nullables ps l \<and> nullables ps r"
    by simp
  hence "nullables ps [Nt A]"
    using A\<alpha> nullable.simps by auto
  from this \<open>nullables ps \<alpha> \<and> nullables ps l \<and> nullables ps r\<close> have "nullables ps v"
    using A\<alpha> by auto
  thus ?case
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by blast
qed

lemma nullable_if: "set ps \<turnstile> [a] \<Rightarrow>* [] \<Longrightarrow> nullable ps a"
  using nullables_if[of ps "[a]" "[]" a] by simp

lemma nullable_aux: "\<forall>s\<in>set gamma. nullable ps s \<and> set ps \<turnstile> [s] \<Rightarrow>* [] \<Longrightarrow> set ps \<turnstile> gamma \<Rightarrow>* []"
proof (induction gamma)
  case (Cons a list)
  hence "set ps \<turnstile> list \<Rightarrow>* []"
    by simp
  moreover have "set ps \<turnstile> [a] \<Rightarrow>* []"
    using Cons by simp
  ultimately show ?case 
    using derives_Cons[of \<open>set ps\<close> list \<open>[]\<close> \<open>a\<close>] by simp
qed simp

lemma if_nullable: "nullable ps a \<Longrightarrow> set ps \<turnstile> [a] \<Rightarrow>* []"
proof (induction rule: nullable.induct)
  case (NullableSym x gamma)
    hence "set ps \<turnstile> [Nt x] \<Rightarrow>* gamma" 
      using derive_singleton by blast
    also have "set ps \<turnstile> gamma \<Rightarrow>* []" 
      using NullableSym nullable_aux by blast
  finally show ?case .
qed

corollary nullable_iff: "nullable ps a \<longleftrightarrow> set ps \<turnstile> [a] \<Rightarrow>* []"
  by (auto simp: nullable_if if_nullable)

fun eps_closure :: "('n, 't) prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms list" where
  "eps_closure ps [] = [[]]" |
  "eps_closure ps (s#sl) = (
    if nullable ps s then (map ((#) s) (eps_closure ps sl)) @ eps_closure ps sl 
    else map ((#) s) (eps_closure ps sl))"

definition eps_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
"eps_elim ps \<equiv> {(l,r'). \<exists>r. (l,r) \<in> set ps \<and> r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> [])}"

definition eps_elim_rel :: "('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> bool" where 
  "eps_elim_rel ps ps'\<equiv> set ps'= eps_elim ps"

lemma Eps_free_if_eps_elim_rel: "eps_elim_rel ps ps' \<Longrightarrow> Eps_free (set ps')"
unfolding eps_elim_rel_def eps_elim_def Eps_free_def by blast

(* auxiliary function to prove finiteness *)
definition eps_elim_fun :: "('n, 't) prods \<Rightarrow> ('n, 't) prod \<Rightarrow> ('n, 't) Prods" where 
  "eps_elim_fun ps p = {(l',r'). l' = fst p \<and> r' \<in> set (eps_closure ps (snd p)) \<and> (r' \<noteq> [])}"

lemma eps_elim_fun_eq: "eps_elim ps = \<Union>((eps_elim_fun ps) ` set ps)"
proof 
  show "eps_elim ps \<subseteq> (\<Union> (eps_elim_fun ps ` set ps))" 
   unfolding eps_elim_def eps_elim_fun_def by auto
next
  show "\<Union>((eps_elim_fun ps) ` set ps) \<subseteq> eps_elim ps"
  proof
    fix x
    assume "x \<in> \<Union>((eps_elim_fun ps) ` set ps)"
    obtain l r' where "x = (l,r')" by fastforce
    hence "(l,r') \<in> \<Union>((eps_elim_fun ps) ` set ps)" 
      using \<open>x \<in> \<Union>((eps_elim_fun ps) ` set ps)\<close> by simp
    hence 1: "\<exists>r. r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> []) \<and> (l,r) \<in> set ps" 
      using eps_elim_fun_def by fastforce
    from this  obtain r where "r' \<in> set (eps_closure ps r) \<and> (l,r) \<in> set ps" 
      by blast
    thus "x \<in> eps_elim ps" unfolding eps_elim_fun_def eps_elim_def
      using 1 \<open>x = (l, r')\<close> by blast 
  qed
qed

lemma finite_eps_elim: "finite (eps_elim ps)" 
proof -
  have "\<forall>p \<in> set ps. finite (eps_elim_fun ps p)"
    unfolding eps_elim_fun_def by auto
  hence "finite (\<Union>((eps_elim_fun ps) ` set ps))"
    using finite_UN by simp
  thus ?thesis using eps_elim_fun_eq by metis
qed

lemma eps_elim_rel_exists: "\<forall>ps. \<exists>ps'. eps_elim_rel ps ps'"
  unfolding eps_elim_rel_def by (simp add: finite_list finite_eps_elim)

lemma eps_closure_nullable:  "[] \<in> set (eps_closure ps w) \<Longrightarrow> nullables ps w"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a r)
  hence "nullable ps a"
    using image_iff[of \<open>[]\<close> \<open>eps_closure ps\<close> \<open>{a#r}\<close>] by auto
  then show ?case 
    using Cons Un_iff by auto
qed

lemma eps_elim_rel_1: "r' \<in> set (eps_closure ps r) \<Longrightarrow> set ps \<turnstile> r \<Rightarrow>* r'"
proof (induction r arbitrary: r')
  case (Cons a r)
  then show ?case 
  proof (cases "nullable ps a")
    case True
    obtain e where e: "e \<in> set (eps_closure ps r) \<and> (r' = (a#e) \<or> r' = e)"
      using Cons.prems True by auto
    hence 1: "set ps \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by blast
    hence 2: "set ps \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using e derives_prepend by blast
    have "set ps \<turnstile> [a] \<Rightarrow>* []" 
      using True if_nullable by blast
    hence "set ps \<turnstile> [a]@r \<Rightarrow>* r" 
      using derives_append by fastforce
    thus ?thesis 
      using 1 2 e by force 
  next
    case False
    obtain e where e: "e \<in> set (eps_closure ps r) \<and> (r' = (a#e))"
      using Cons.prems False by auto
    hence "set ps \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by simp
    hence "set ps \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using derives_prepend by blast
    thus ?thesis
      using e by simp
  qed
qed simp

lemma eps_elim_rel_r2: 
  assumes "set ps' \<turnstile> u \<Rightarrow> v" and "eps_elim_rel ps ps'" 
  shows "set ps \<turnstile> u \<Rightarrow>* v"
  using assms 
proof -
  obtain A \<alpha> x y where A: "(A, \<alpha>) \<in> set ps'\<and> u = x @ [Nt A] @ y \<and> v = x @ \<alpha> @ y"
    using assms derive.cases by meson
  hence 1: "(A, \<alpha>) \<in> {(l,r'). \<exists>r. (l,r) \<in> set ps \<and> r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> [])}"
    using assms(2) unfolding eps_elim_rel_def eps_elim_def by simp
  obtain r where r: "(A, r) \<in> set ps \<and> \<alpha> \<in> set (eps_closure ps r)"
    using 1 by blast
  hence "set ps \<turnstile> r \<Rightarrow>* \<alpha>" 
    using eps_elim_rel_1 by blast
  hence 2: "set ps \<turnstile> x @ r @ y \<Rightarrow>* x @ \<alpha> @ y"
    using r derives_prepend derives_append by blast
  hence "set ps \<turnstile> x @ [Nt A] @ y \<Rightarrow> x @ r @ y" 
    using r derive.simps by fast
  thus ?thesis 
    using 2 by (simp add: A)
qed

lemma eps_elim_rel_r3:
  assumes "set ps' \<turnstile> u \<Rightarrow>* v" and "eps_elim_rel ps ps'" 
  shows "set ps \<turnstile> u \<Rightarrow>* v"
    using assms by (induction v rule: rtranclp_induct) (auto simp: eps_elim_rel_r2 rtranclp_trans)

lemma eps_elim_rel_r5: "r \<in> set (eps_closure ps r)" 
  by (induction r) auto

lemma eps_elim_rel_r4:
  assumes "(l,r) \<in> set ps"
    and "eps_elim_rel ps ps'"
    and "(r' \<noteq> [])" 
    and "r' \<in> set (eps_closure ps r)"
  shows "(l,r') \<in> set ps'"
  using assms unfolding eps_elim_rel_def eps_elim_def by blast

lemma eps_elim_rel_r7: 
  assumes "eps_elim_rel ps ps'"
    and "set ps \<turnstile> [Nt A] \<Rightarrow> v"
    and "v' \<in> set (eps_closure ps v) \<and> (v' \<noteq> [])"
  shows "set ps' \<turnstile> [Nt A] \<Rightarrow> v'"
proof -
  have "(A,v) \<in> set ps" 
    using assms(2) by (simp add: derive_singleton)
  hence "(A,v') \<in> set ps'" 
    using assms eps_elim_rel_r4 conjE by fastforce
  thus ?thesis 
    using derive_singleton by fast
qed

lemma eps_elim_rel_r12a: 
  assumes "x' \<in> set (eps_closure ps x)"
    and "y' \<in> set (eps_closure ps y)"
  shows "(x'@y') \<in> set (eps_closure ps (x@y))"
  using assms by (induction x arbitrary: x' y y' rule: eps_closure.induct) auto

lemma eps_elim_rel_r12b:
  assumes "x' \<in> set (eps_closure ps x)"
    and "y' \<in> set (eps_closure ps y)"
    and "z' \<in> set (eps_closure ps z)"
  shows "(x'@y'@z') \<in> set (eps_closure ps (x@y@z))"
  using assms 
  by (induction x arbitrary: x' y y' z z' rule: eps_closure.induct) (auto simp: eps_elim_rel_r12a)

lemma eps_elim_rel_r14:
  assumes "r' \<in> set (eps_closure ps (x@y))"
  shows "\<exists>x' y'. (r'=x'@y') \<and> x' \<in> set (eps_closure ps x) \<and> y' \<in> set (eps_closure ps y)"
  using assms
proof (induction x arbitrary: y r' rule: eps_closure.induct)
  case (2 ps s sl)
  then show ?case
  proof -
    have "\<exists>x' y'. s # x = x' @ y' \<and> (x' \<in> (#) s ` set (eps_closure ps sl) \<or> x' \<in> set (eps_closure ps sl)) \<and> y' \<in> set (eps_closure ps y)"
      if "\<And>r' y. r' \<in> set (eps_closure ps (sl @ y)) \<Longrightarrow> \<exists>x' y'. r' = x' @ y' \<and> x' \<in> set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
        and "nullable ps s"
        and "x \<in> set (eps_closure ps (sl @ y))"
        and "r' = s # x"
      for x :: "('a, 'b) sym list"
      using that by (metis append_Cons imageI)
    moreover have "\<exists>x' y'. r' = x' @ y' \<and> (x' \<in> (#) s ` set (eps_closure ps sl) \<or> x' \<in> set (eps_closure ps sl)) \<and> y' \<in> set (eps_closure ps y)"
      if "\<And>r' y. r' \<in> set (eps_closure ps (sl @ y)) \<Longrightarrow> \<exists>x' y'. r' = x' @ y' \<and> x' \<in> set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
        and "nullable ps s"
        and "r' \<in> set (eps_closure ps (sl @ y))"
      using that by metis
    moreover have "\<exists>x' y'. s # x = x' @ y' \<and> x' \<in> (#) s ` set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
      if "\<And>r' y. r' \<in> set (eps_closure ps (sl @ y)) \<Longrightarrow> \<exists>x' y'. r' = x' @ y' \<and> x' \<in> set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
        and "\<not> nullable ps s"
        and "x \<in> set (eps_closure ps (sl @ y))"
        and "r' = s # x"
      for x :: "('a, 'b) sym list"
      using that by (metis append_Cons imageI)
    ultimately show ?thesis
      using 2 by auto
  qed
qed simp

lemma eps_elim_rel_r15:
  assumes "set ps \<turnstile> [Nt S] \<Rightarrow>* u"
    and "eps_elim_rel ps ps'"
    and "v \<in> set (eps_closure ps u) \<and> (v \<noteq> [])"
  shows "set ps' \<turnstile> [Nt S] \<Rightarrow>* v"
  using assms
proof (induction u arbitrary: v rule: derives_induct)
  case base
  then show ?case
    by (cases "nullable ps (Nt S)") auto
next
  case (step x A y w)
  then obtain x' w' y' where 
    v: "(v = (x'@w'@y')) \<and> x' \<in> set (eps_closure ps x) \<and> w' \<in> set (eps_closure ps w) \<and> y' \<in> set (eps_closure ps y)"
    using step eps_elim_rel_r14 by metis
  then show ?case
  proof (cases "w' = []")
    case True
      hence "v = x'@y'" 
        using v by simp 
      have "[] \<in> set (eps_closure ps w)"
        using True v by simp
      hence "nullables ps w"
        using eps_closure_nullable by blast
      hence "[] \<in> set (eps_closure ps [Nt A])" 
        using step(2) NullableSym by fastforce
      hence "(x'@y') \<in> set (eps_closure ps (x@[Nt A]@y))"
        using eps_elim_rel_r12b[of x' ps x \<open>[]\<close> \<open>[Nt A]\<close> y' y] v by simp
      then show ?thesis 
        using \<open>v = x' @ y'\<close> step by blast
  next
    case False
      have "(x'@[Nt A]@y') \<in> set (eps_closure ps (x@[Nt A]@y)) "
        using eps_elim_rel_r12b[of x' ps x \<open>[Nt A]\<close> \<open>[Nt A]\<close> y' y] eps_elim_rel_r5[of \<open>[Nt A]\<close> ps] v by blast
      hence 1: "set ps' \<turnstile> [Nt S] \<Rightarrow>* (x'@[Nt A]@y')" 
        using step by blast
      have "set ps \<turnstile> [Nt A] \<Rightarrow> w" 
        using step(2) derive_singleton by blast
      hence "set ps' \<turnstile> [Nt A] \<Rightarrow> w'"
        using eps_elim_rel_r7[of ps ps' A w w'] False step v by blast
      hence "set ps' \<turnstile> (x'@[Nt A]@y') \<Rightarrow> (x'@w'@y')" 
        using derive_append derive_prepend by blast
      thus ?thesis using 1
      by (simp add: v step.prems(2))
  qed
qed

theorem eps_elim_rel_eq_if_noe:
  assumes "eps_elim_rel ps ps'"
    and "[] \<notin> lang ps S"
  shows "lang ps S = lang ps' S"
proof 
  show "lang ps S \<subseteq> lang ps' S"
  proof 
    fix x
    assume "x \<in> lang ps S"
    have "\<forall>x. set ps \<turnstile> [Nt S] \<Rightarrow>* x \<longrightarrow> x \<noteq> []"
      using assms Lang_def by fastforce
    hence "(map Tm x) \<in> set (eps_closure ps (map Tm x))" 
      using eps_elim_rel_r5 by auto
    hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* (map Tm x)"
      using assms \<open>x \<in> lang ps S\<close> Lang_def eps_elim_rel_r15[of ps S \<open>map Tm x\<close>] by fast
    thus "x \<in> lang ps' S"
      using Lang_def \<open>x \<in> lang ps S\<close> by fast 
  qed
next
  show "lang ps' S \<subseteq> lang ps S"
  proof
    fix x'
    assume "x' \<in> lang ps' S"
    show "x' \<in> lang ps S" 
      using assms Lang_def \<open>x' \<in> lang ps' S\<close> eps_elim_rel_r3[of ps' \<open>[Nt S]\<close> \<open>map Tm x'\<close> ps] by fast
  qed
qed

(* correctness *)
lemma noe_lang_eps_elim_rel_aux: 
  assumes "ps \<turnstile> [Nt S] \<Rightarrow>* w" "w = []"  
  shows "\<exists>A. ps \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, w) \<in> ps"
  using assms by (induction w rule: rtranclp_induct) (auto simp: derive.simps)

lemma noe_lang_eps_elim_rel: "eps_elim_rel ps ps' \<Longrightarrow> [] \<notin> lang ps' S"
proof (rule ccontr)
  assume "eps_elim_rel ps ps'" "\<not>([] \<notin> lang ps' S)"
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* map Tm []"
    using Lang_def by fast
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* []"
    by simp
  hence "\<exists>A. set ps' \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, []) \<in> set ps'"
    using noe_lang_eps_elim_rel_aux[of \<open>set ps'\<close>] by blast
  thus False 
    using \<open>eps_elim_rel ps ps'\<close> unfolding eps_elim_rel_def eps_elim_def by blast
qed

theorem eps_elim_rel_lang_eq: "eps_elim_rel ps ps'\<Longrightarrow> lang ps' S = lang ps S - {[]}"
proof 
  assume "eps_elim_rel ps ps'"
  show "lang ps' S \<subseteq> lang ps S - {[]}"
  proof 
    fix w
    assume "w \<in> lang ps' S"
    hence "w \<in> lang ps' S - {[]}"
      using noe_lang_eps_elim_rel[of ps] \<open>eps_elim_rel ps ps'\<close> by simp
    thus "w \<in> lang ps S - {[]}"
      using \<open>eps_elim_rel ps ps'\<close> by (auto simp: Lang_def eps_elim_rel_r3)
  qed
next
  assume "eps_elim_rel ps ps'"
  show "lang ps S - {[]} \<subseteq> lang ps' S"
  proof 
    fix w
    assume "w \<in> lang ps S - {[]}"
    hence 1: "(map Tm w) \<noteq> []" 
      by simp
    have 2: "set ps \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using \<open>w \<in> lang ps S - {[]}\<close> Lang_def by fast
    have "(map Tm w) \<in> set (eps_closure ps (map Tm w)) "
      using \<open>w \<in> lang ps S - {[]}\<close> eps_elim_rel_r5 by blast
    hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using 1 2 eps_elim_rel_r15[of ps] \<open>eps_elim_rel ps ps'\<close> by simp
    thus "w \<in> lang ps' S"
      by (simp add: Lang_def)
  qed
qed

end