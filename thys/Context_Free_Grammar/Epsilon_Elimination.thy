(*
Author: August Martin Stimpfle
Based on HOL4 theories by Aditi Barthwal
*)

section \<open>Elimination of Epsilon Productions\<close>

theory Epsilon_Elimination
imports Context_Free_Grammar "HOL-Library.While_Combinator"
begin

inductive Nullable :: "('n,'t) Prods \<Rightarrow> ('n,'t) sym \<Rightarrow> bool"
for P where
  NullableSym:
  "\<lbrakk> (A, w) \<in> P; \<forall>s \<in> set w. Nullable P s\<rbrakk>
  \<Longrightarrow> Nullable P (Nt A)"

abbreviation "Nullables P w \<equiv> (\<forall>s \<in> set w. Nullable P s)"

definition nullables_wrt :: "'n set \<Rightarrow> ('n, 't) syms \<Rightarrow> bool" where
"nullables_wrt N w = (Tms_syms w = {} \<and> Nts_syms w \<subseteq> N)"

definition nullable_step :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
"nullable_step P N = fst ` {(A,w) \<in> P. nullables_wrt N w}"

definition nullable_fun :: "('n,'t)Prods \<Rightarrow> 'n set option" where
"nullable_fun P = while_option (\<lambda>N. nullable_step P N \<noteq> N) (nullable_step P) {}"

lemma "nullable_fun {(0::int,[Nt 1::(int,int)sym]), (1,[])} = Some{0,1}"
by eval

lemma mono_nullable_step: "mono (nullable_step P)"
unfolding mono_def nullable_step_def nullables_wrt_def by auto

(* TODO mv? *)
lemma while_option_Some_closed:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "while_option (\<lambda>x. f x \<noteq> x) f bot = Some x" shows "f x = x"
using while_option_stop2[OF assms(1)] by fastforce

lemma nullable_fun_Some_closed: "nullable_fun P = Some N \<Longrightarrow> nullable_step P N = N"
unfolding nullable_fun_def using while_option_Some_closed[of "nullable_step P"] by blast

lemma Nullable_if_nullable_fun:
assumes "finite P" "nullable_fun P = Some N" shows "\<forall>A\<in>N. Nullable P (Nt A)"
proof -
  let ?I = "\<lambda>N. \<forall>A\<in>N. Nullable P (Nt A)"
  have 0: "?I {}" by simp
  have "?I (nullable_step P N)" if "?I N" for N
  proof -
    have "Nullable P (Nt A)" if asms: "(A, w) \<in> P" "Tms_syms w = {}" "Nts_syms w \<subseteq> N" for A w
    proof -
      have "Nullable P s" if "s \<in> set w" for s
      proof -
        have "s \<in> Nt ` N" using asms(2,3) \<open>s \<in> set w\<close> unfolding Nts_syms_def Tms_syms_def
          by(cases s) auto
        thus ?thesis using \<open>?I N\<close> by blast
      qed
      then show ?thesis by (metis asms(1) NullableSym)
    qed
    then show ?thesis using \<open>?I N\<close> unfolding nullable_step_def nullables_wrt_def by auto
  qed
  from while_option_rule[where P = ?I and s = "{}", OF this assms(2)[unfolded nullable_fun_def] 0]
  show ?thesis by blast
qed

lemma nullable_fun_if_Nullable: assumes "nullable_fun P = Some N"
  shows "Nullable P s \<Longrightarrow> (\<And>A. s = Nt A \<Longrightarrow> A \<in> N)"
proof(induction rule: Nullable.induct)
  case (NullableSym B w)
  then have [simp]: "B = A" by auto
  from NullableSym have "A \<in> nullable_step P N"
   unfolding nullable_step_def nullables_wrt_def image_def Nts_syms_def Tms_syms_def
   apply auto
   using Nullable.cases by blast
  with NullableSym show ?case
    using assms nullable_fun_Some_closed by blast
qed

lemma nullable_fun_Some: assumes "finite P" shows "\<exists>N. nullable_fun P = Some N"
proof -
  let ?M = "Nts P"
  have *: "\<And>X. X \<subseteq> Nts P \<Longrightarrow> nullable_step P X \<subseteq> Nts P"
    unfolding nullable_step_def nullables_wrt_def Nts_def by(auto)
  from while_option_finite_subset_Some[OF mono_nullable_step * finite_Nts[OF assms]]
  show ?thesis unfolding nullable_fun_def by blast
qed

lemma Nullable_iff_nullable_fun: "finite P \<Longrightarrow> Nullable P (Nt A) = (A \<in> the(nullable_fun P))"
  by (metis Nullable_if_nullable_fun nullable_fun_Some nullable_fun_if_Nullable
      option.sel)

lemma nullable_Tm[code]: "Nullable P (Tm a) = False"
  using Nullable.cases by blast

lemma nullable_Nt[code]: "Nullable (set ps) (Nt A) = (A \<in> the(nullable_fun (set ps)))"
  by (simp add: Nullable_iff_nullable_fun)

lemma "nullable_fun {(0::int, [Nt 1, Nt 2, Nt 1]), (1, [Tm (0::int), Nt 1]), (1, []), (2, [Tm 1, Nt 2]), (2,[])}
 = Some{0,1,2}"
by eval

lemma "Nullable {(0::int,[Nt 1::(int,int)sym]), (1,[])} (Nt 0)"
by eval

lemma nullables_if: 
  assumes "P \<turnstile> u \<Rightarrow>* v" 
    and "u=[a]" "Nullables P v"
  shows "Nullables P u"
  using assms
proof(induction arbitrary: a rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl u v w)
  from \<open>P \<turnstile> v \<Rightarrow> w\<close> obtain A \<alpha> l r where A\<alpha>: "v = l @ [Nt A] @ r \<and> w = l @ \<alpha> @ r \<and> (A, \<alpha>) \<in> P"
    by (auto simp: derive.simps)
  from this \<open>Nullables P w\<close> have "Nullables P \<alpha> \<and> Nullables P l \<and> Nullables P r"
    by simp
  hence "Nullables P [Nt A]"
    using A\<alpha> Nullable.simps by auto
  from this \<open>Nullables P \<alpha> \<and> Nullables P l \<and> Nullables P r\<close> have "Nullables P v"
    using A\<alpha> by auto
  thus ?case
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by blast
qed

lemma nullable_if: "P \<turnstile> [a] \<Rightarrow>* [] \<Longrightarrow> Nullable P a"
  using nullables_if[of P "[a]" "[]" a] by simp

lemma nullable_aux: "\<forall>s\<in>set gamma. P \<turnstile> [s] \<Rightarrow>* [] \<Longrightarrow> P \<turnstile> gamma \<Rightarrow>* []"
proof (induction gamma)
  case (Cons a list)
  hence "P \<turnstile> list \<Rightarrow>* []"
    by simp
  moreover have "P \<turnstile> [a] \<Rightarrow>* []"
    using Cons by simp
  ultimately show ?case 
    using derives_Cons[of \<open>P\<close> list \<open>[]\<close> \<open>a\<close>] by simp
qed simp

lemma if_nullable: "Nullable P a \<Longrightarrow> P \<turnstile> [a] \<Rightarrow>* []"
proof (induction rule: Nullable.induct)
  case (NullableSym x gamma)
    hence "P \<turnstile> [Nt x] \<Rightarrow>* gamma" 
      using derive_singleton by blast
    also have "P \<turnstile> gamma \<Rightarrow>* []" 
      using NullableSym nullable_aux by blast
  finally show ?case .
qed

corollary nullable_iff: "Nullable P a \<longleftrightarrow> P \<turnstile> [a] \<Rightarrow>* []"
  by (auto simp: nullable_if if_nullable)

fun eps_closure :: "('n, 't) Prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms list" where
  "eps_closure ps [] = [[]]" |
  "eps_closure ps (s#sl) = (
    if Nullable ps s then (map ((#) s) (eps_closure ps sl)) @ eps_closure ps sl 
    else map ((#) s) (eps_closure ps sl))"

definition Eps_elim :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where
"Eps_elim ps \<equiv> {(l,r'). \<exists>r. (l,r) \<in> ps \<and> r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> [])}"

definition eps_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) prods" where
"eps_elim ps \<equiv> concat (map (\<lambda>(l,r). map (\<lambda>r'. (l,r')) (filter (\<lambda>r'. r' \<noteq> []) (eps_closure (set ps) r))) ps)"

lemma set_eps_elim: "set(eps_elim ps) = Eps_elim (set ps)"
unfolding eps_elim_def Eps_elim_def by auto

lemma Eps_elim_code[code]: "Eps_elim ps =
  (\<Union>(l,r) \<in> ps. \<Union>r' \<in> set (eps_closure ps r). if r' = [] then {} else {(l,r')})"
unfolding Eps_elim_def by (auto split: prod.split)

lemma "Eps_elim
  {(0::int, [Nt 1, Nt 2, Nt 1]), (1, [Tm (0::int), Nt 1]), (1, []), (2, [Tm 1, Nt 2]), (2,[])}
 = {(2, [Tm 1, Nt 2]), (2, [Tm 1]), (1, [Tm 0, Nt 1]), (1, [Tm 0]), (0, [Nt 1, Nt 2, Nt 1]),
    (0, [Nt 1, Nt 2]), (0, [Nt 1, Nt 1]), (0, [Nt 1]), (0, [Nt 2, Nt 1]), (0, [Nt 2])}"
by eval

lemma Eps_free_Eps_elim: "Eps_free (Eps_elim ps')"
unfolding Eps_elim_def Eps_free_def by blast

text \<open>@{const Eps_elim} is identity on @{const Eps_free} input.\<close>

lemma Eps_free_not_Nullable: "Eps_free P \<Longrightarrow> \<not> Nullable P A"
  by (auto simp: nullable_iff Eps_free_derives_Nil)

lemma Eps_free_eps_closure: "Eps_free P \<Longrightarrow> eps_closure P w = [w]"
  by (induction w, auto simp: Eps_free_not_Nullable)

lemma Eps_elim_id: "Eps_free P \<Longrightarrow> Eps_elim P = P"
  by (auto simp: Eps_elim_def Eps_free_eps_closure Eps_free_Nil)

(* auxiliary function to prove finiteness *)
definition Eps_elim_fun :: "('n, 't) Prods \<Rightarrow> ('n, 't) prod \<Rightarrow> ('n, 't) Prods" where 
  "Eps_elim_fun ps p = {(l',r'). l' = fst p \<and> r' \<in> set (eps_closure ps (snd p)) \<and> (r' \<noteq> [])}"

lemma Eps_elim_fun_eq: "Eps_elim ps = \<Union>((Eps_elim_fun ps) ` ps)"
proof 
  show "Eps_elim ps \<subseteq> (\<Union> (Eps_elim_fun ps ` ps))" 
   unfolding Eps_elim_def Eps_elim_fun_def by auto
next
  show "\<Union>((Eps_elim_fun ps) ` ps) \<subseteq> Eps_elim ps"
  proof
    fix x
    assume "x \<in> \<Union>((Eps_elim_fun ps) ` ps)"
    obtain l r' where "x = (l,r')" by fastforce
    hence "(l,r') \<in> \<Union>((Eps_elim_fun ps) ` ps)" 
      using \<open>x \<in> \<Union>((Eps_elim_fun ps) ` ps)\<close> by simp
    hence 1: "\<exists>r. r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> []) \<and> (l,r) \<in> ps" 
      using Eps_elim_fun_def by fastforce
    from this  obtain r where "r' \<in> set (eps_closure ps r) \<and> (l,r) \<in> ps" 
      by blast
    thus "x \<in> Eps_elim ps" unfolding Eps_elim_fun_def Eps_elim_def
      using 1 \<open>x = (l, r')\<close> by blast 
  qed
qed

lemma finite_Eps_elim: assumes "finite ps" shows "finite (Eps_elim ps)" 
proof -
  have "\<forall>p \<in> ps. finite (Eps_elim_fun ps p)"
    unfolding Eps_elim_fun_def by auto
  hence "finite (\<Union>((Eps_elim_fun ps) ` ps))"
    using finite_UN assms by simp
  thus ?thesis using Eps_elim_fun_eq by metis
qed

lemma eps_closure_nullable:  "[] \<in> set (eps_closure ps w) \<Longrightarrow> Nullables ps w"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a r)
  hence "Nullable ps a"
    using image_iff[of \<open>[]\<close> \<open>eps_closure ps\<close> \<open>{a#r}\<close>] by auto
  then show ?case 
    using Cons Un_iff by auto
qed

lemma Eps_elim_rel_1: "r' \<in> set (eps_closure ps r) \<Longrightarrow> ps \<turnstile> r \<Rightarrow>* r'"
proof (induction r arbitrary: r')
  case (Cons a r)
  then show ?case 
  proof (cases "Nullable ps a")
    case True
    obtain e where e: "e \<in> set (eps_closure ps r) \<and> (r' = (a#e) \<or> r' = e)"
      using Cons.prems True by auto
    hence 1: "ps \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by blast
    hence 2: "ps \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using e derives_prepend by blast
    have "ps \<turnstile> [a] \<Rightarrow>* []" 
      using True if_nullable by blast
    hence "ps \<turnstile> [a]@r \<Rightarrow>* r" 
      using derives_append by fastforce
    thus ?thesis 
      using 1 2 e by force 
  next
    case False
    obtain e where e: "e \<in> set (eps_closure ps r) \<and> (r' = (a#e))"
      using Cons.prems False by auto
    hence "ps \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by simp
    hence "ps \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using derives_prepend by blast
    thus ?thesis
      using e by simp
  qed
qed simp

lemma Eps_elim_rel_r2: 
  assumes "Eps_elim ps \<turnstile> u \<Rightarrow> v"
  shows "ps \<turnstile> u \<Rightarrow>* v"
  using assms 
proof -
  obtain A \<alpha> x y where A: "(A, \<alpha>) \<in> Eps_elim ps \<and> u = x @ [Nt A] @ y \<and> v = x @ \<alpha> @ y"
    using assms derive.cases by meson
  hence 1: "(A, \<alpha>) \<in> {(l,r'). \<exists>r. (l,r) \<in> ps \<and> r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> [])}"
    unfolding Eps_elim_def by simp
  obtain r where r: "(A, r) \<in> ps \<and> \<alpha> \<in> set (eps_closure ps r)"
    using 1 by blast
  hence "ps \<turnstile> r \<Rightarrow>* \<alpha>" 
    using Eps_elim_rel_1 by blast
  hence 2: "ps \<turnstile> x @ r @ y \<Rightarrow>* x @ \<alpha> @ y"
    using r derives_prepend derives_append by blast
  hence "ps \<turnstile> x @ [Nt A] @ y \<Rightarrow> x @ r @ y" 
    using r derive.simps by fast
  thus ?thesis 
    using 2 by (simp add: A)
qed

lemma Eps_elim_rel_r3:
  assumes "Eps_elim ps \<turnstile> u \<Rightarrow>* v"
  shows "ps \<turnstile> u \<Rightarrow>* v"
    using assms by (induction v rule: rtranclp_induct) (auto simp: Eps_elim_rel_r2 rtranclp_trans)

lemma Eps_elim_rel_r5: "r \<in> set (eps_closure ps r)" 
  by (induction r) auto

lemma Eps_elim_rel_r4:
  assumes "(l,r) \<in> ps"
    and "(r' \<noteq> [])" 
    and "r' \<in> set (eps_closure ps r)"
  shows "(l,r') \<in> Eps_elim ps"
  using assms unfolding Eps_elim_def by blast

lemma Eps_elim_rel_r7: 
  assumes "ps \<turnstile> [Nt A] \<Rightarrow> v"
    and "v' \<in> set (eps_closure ps v) \<and> (v' \<noteq> [])"
  shows "Eps_elim ps \<turnstile> [Nt A] \<Rightarrow> v'"
proof -
  have "(A,v) \<in> ps" 
    using assms(1) by (simp add: derive_singleton)
  hence "(A,v') \<in> Eps_elim ps" 
    using assms Eps_elim_rel_r4 conjE by fastforce
  thus ?thesis 
    using derive_singleton by fast
qed

lemma Eps_elim_rel_r12a: 
  assumes "x' \<in> set (eps_closure ps x)"
    and "y' \<in> set (eps_closure ps y)"
  shows "(x'@y') \<in> set (eps_closure ps (x@y))"
  using assms by (induction x arbitrary: x' y y' rule: eps_closure.induct) auto

lemma Eps_elim_rel_r12b:
  assumes "x' \<in> set (eps_closure ps x)"
    and "y' \<in> set (eps_closure ps y)"
    and "z' \<in> set (eps_closure ps z)"
  shows "(x'@y'@z') \<in> set (eps_closure ps (x@y@z))"
  using assms 
  by (induction x arbitrary: x' y y' z z' rule: eps_closure.induct) (auto simp: Eps_elim_rel_r12a)

lemma Eps_elim_rel_r14:
  assumes "r' \<in> set (eps_closure ps (x@y))"
  shows "\<exists>x' y'. (r'=x'@y') \<and> x' \<in> set (eps_closure ps x) \<and> y' \<in> set (eps_closure ps y)"
  using assms
proof (induction x arbitrary: y r' rule: eps_closure.induct)
  case (2 ps s sl)
  then show ?case
  proof -
    have "\<exists>x' y'. s # x = x' @ y' \<and> (x' \<in> (#) s ` set (eps_closure ps sl) \<or> x' \<in> set (eps_closure ps sl)) \<and> y' \<in> set (eps_closure ps y)"
      if "\<And>r' y. r' \<in> set (eps_closure ps (sl @ y)) \<Longrightarrow> \<exists>x' y'. r' = x' @ y' \<and> x' \<in> set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
        and "Nullable ps s"
        and "x \<in> set (eps_closure ps (sl @ y))"
        and "r' = s # x"
      for x :: "('a, 'b) sym list"
      using that by (metis append_Cons imageI)
    moreover have "\<exists>x' y'. r' = x' @ y' \<and> (x' \<in> (#) s ` set (eps_closure ps sl) \<or> x' \<in> set (eps_closure ps sl)) \<and> y' \<in> set (eps_closure ps y)"
      if "\<And>r' y. r' \<in> set (eps_closure ps (sl @ y)) \<Longrightarrow> \<exists>x' y'. r' = x' @ y' \<and> x' \<in> set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
        and "Nullable ps s"
        and "r' \<in> set (eps_closure ps (sl @ y))"
      using that by metis
    moreover have "\<exists>x' y'. s # x = x' @ y' \<and> x' \<in> (#) s ` set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
      if "\<And>r' y. r' \<in> set (eps_closure ps (sl @ y)) \<Longrightarrow> \<exists>x' y'. r' = x' @ y' \<and> x' \<in> set (eps_closure ps sl) \<and> y' \<in> set (eps_closure ps y)"
        and "\<not> Nullable ps s"
        and "x \<in> set (eps_closure ps (sl @ y))"
        and "r' = s # x"
      for x :: "('a, 'b) sym list"
      using that by (metis append_Cons imageI)
    ultimately show ?thesis
      using 2 by auto
  qed
qed simp

lemma Eps_elim_rel_r15:
  assumes "ps \<turnstile> [Nt S] \<Rightarrow>* u"
    and "v \<in> set (eps_closure ps u) \<and> (v \<noteq> [])"
  shows "Eps_elim ps \<turnstile> [Nt S] \<Rightarrow>* v"
  using assms
proof (induction u arbitrary: v rule: derives_induct)
  case base
  then show ?case
    by (cases "Nullable ps (Nt S)") auto
next
  case (step x A y w)
  then obtain x' w' y' where 
    v: "(v = (x'@w'@y')) \<and> x' \<in> set (eps_closure ps x) \<and> w' \<in> set (eps_closure ps w) \<and> y' \<in> set (eps_closure ps y)"
    using step Eps_elim_rel_r14 by metis
  then show ?case
  proof (cases "w' = []")
    case True
      hence "v = x'@y'" 
        using v by simp 
      have "[] \<in> set (eps_closure ps w)"
        using True v by simp
      hence "Nullables ps w"
        using eps_closure_nullable by blast
      hence "[] \<in> set (eps_closure ps [Nt A])" 
        using step(2) NullableSym by fastforce
      hence "(x'@y') \<in> set (eps_closure ps (x@[Nt A]@y))"
        using Eps_elim_rel_r12b[of x' ps x \<open>[]\<close> \<open>[Nt A]\<close> y' y] v by simp
      then show ?thesis 
        using \<open>v = x' @ y'\<close> step by blast
  next
    case False
      have "(x'@[Nt A]@y') \<in> set (eps_closure ps (x@[Nt A]@y)) "
        using Eps_elim_rel_r12b[of x' ps x \<open>[Nt A]\<close> \<open>[Nt A]\<close> y' y] Eps_elim_rel_r5[of \<open>[Nt A]\<close> ps] v by blast
      hence 1: "Eps_elim ps \<turnstile> [Nt S] \<Rightarrow>* (x'@[Nt A]@y')" 
        using step by blast
      have "ps \<turnstile> [Nt A] \<Rightarrow> w" 
        using step(2) derive_singleton by blast
      hence "Eps_elim ps \<turnstile> [Nt A] \<Rightarrow> w'"
        using Eps_elim_rel_r7[of ps A w w'] False step v by blast
      hence "Eps_elim ps \<turnstile> (x'@[Nt A]@y') \<Rightarrow> (x'@w'@y')" 
        using derive_append derive_prepend by blast
      thus ?thesis using 1
      by (simp add: v step.prems(1))
  qed
qed

theorem Eps_elim_rel_eq_if_noe:
  assumes "[] \<notin> Lang ps S"
  shows "Lang ps S = Lang (Eps_elim ps) S"
proof 
  show "Lang ps S \<subseteq> Lang (Eps_elim ps) S"
  proof 
    fix x
    assume "x \<in> Lang ps S"
    have "\<forall>x. ps \<turnstile> [Nt S] \<Rightarrow>* x \<longrightarrow> x \<noteq> []"
      using assms Lang_def by fastforce
    hence "(map Tm x) \<in> set (eps_closure ps (map Tm x))" 
      using Eps_elim_rel_r5 by auto
    hence "Eps_elim ps \<turnstile> [Nt S] \<Rightarrow>* (map Tm x)"
      using assms \<open>x \<in> Lang ps S\<close> Lang_def Eps_elim_rel_r15[of ps S \<open>map Tm x\<close>] by fast
    thus "x \<in> Lang (Eps_elim ps) S"
      using Lang_def \<open>x \<in> Lang ps S\<close> by fast 
  qed
next
  show "Lang (Eps_elim ps) S \<subseteq> Lang ps S"
  proof
    fix x'
    assume "x' \<in> Lang (Eps_elim ps) S"
    show "x' \<in> Lang ps S" 
      using assms Lang_def \<open>x' \<in> Lang (Eps_elim ps) S\<close> Eps_elim_rel_r3[of ps \<open>[Nt S]\<close> \<open>map Tm x'\<close>] by fast
  qed
qed

(* correctness *)
lemma noe_lang_Eps_elim_rel_aux: 
  assumes "ps \<turnstile> [Nt S] \<Rightarrow>* w" "w = []"  
  shows "\<exists>A. ps \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, w) \<in> ps"
  using assms by (induction w rule: rtranclp_induct) (auto simp: derive.simps)

lemma noe_lang_Eps_elim_rel: "[] \<notin> Lang (Eps_elim ps) S"
proof (rule notI)
  assume "[] \<in> Lang (Eps_elim ps) S"
  hence "Eps_elim ps \<turnstile> [Nt S] \<Rightarrow>* map Tm []"
    using Lang_def by fast
  hence "Eps_elim ps \<turnstile> [Nt S] \<Rightarrow>* []"
    by simp
  hence "\<exists>A. Eps_elim ps \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, []) \<in> Eps_elim ps"
    using noe_lang_Eps_elim_rel_aux[of \<open>Eps_elim ps\<close>] by blast
  thus False 
    unfolding Eps_elim_def by blast
qed

theorem Lang_Eps_elim: "Lang (Eps_elim ps) S = Lang ps S - {[]}"
proof 
  show "Lang (Eps_elim ps) S \<subseteq> Lang ps S - {[]}"
  proof 
    fix w
    assume "w \<in> Lang (Eps_elim ps) S"
    hence "w \<in> Lang (Eps_elim ps) S - {[]}"
      by (simp add: noe_lang_Eps_elim_rel)
    thus "w \<in> Lang ps S - {[]}"
      by (auto simp: Lang_def Eps_elim_rel_r3)
  qed
next
  show "Lang ps S - {[]} \<subseteq> Lang (Eps_elim ps) S"
  proof 
    fix w
    assume "w \<in> Lang ps S - {[]}"
    hence 1: "(map Tm w) \<noteq> []" 
      by simp
    have 2: "ps \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using \<open>w \<in> Lang ps S - {[]}\<close> Lang_def by fast
    have "(map Tm w) \<in> set (eps_closure ps (map Tm w)) "
      using \<open>w \<in> Lang ps S - {[]}\<close> Eps_elim_rel_r5 by blast
    hence "Eps_elim ps \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using 1 2 Eps_elim_rel_r15[of ps] by simp
    thus "w \<in> Lang (Eps_elim ps) S"
      by (simp add: Lang_def)
  qed
qed

lemma set_eps_closure_subset: "u \<in> set(eps_closure P w) \<Longrightarrow> set u \<subseteq> set w"
apply(induction P w arbitrary: u rule: eps_closure.induct)
 apply simp
apply (fastforce split: if_splits)
done

lemma Nts_Eps_elim: "Nts (Eps_elim P) \<subseteq> Nts P"
unfolding Nts_def Eps_elim_def Nts_syms_def
by(auto split: prod.splits dest: set_eps_closure_subset)

corollary nts_eps_elim: "Nts(set(eps_elim ps)) \<subseteq> Nts(set ps)"
  by (metis set_eps_elim Nts_Eps_elim)

corollary lang_eps_elim: "lang (eps_elim ps) S = lang ps S - {[]}"
  by (metis Lang_Eps_elim set_eps_elim)

corollary eps_free_eps_elim: "eps_free (eps_elim ps)"
  by (metis set_eps_elim Eps_free_Eps_elim)

end