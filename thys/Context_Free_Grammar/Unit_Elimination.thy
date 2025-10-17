(*
Author: August Martin Stimpfle
Based on HOL4 theories by Aditi Barthwal
*)

section \<open>Elimination of Unit Productions\<close>

theory Unit_Elimination
imports Context_Free_Grammar
begin

definition unit_prods :: "('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"unit_prods P = {(l,r) \<in> P. \<exists>A. r = [Nt A]}"

definition unit_rtc :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) set" where
"unit_rtc P = {(A,B). P \<turnstile> [Nt A] \<Rightarrow>* [Nt B] \<and> {A,B} \<subseteq> Nts P}"

definition unit_rm :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where
"unit_rm P = P - unit_prods P"

definition new_prods :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where 
"new_prods P = {(A,r). \<exists>B. (B,r) \<in> unit_rm P \<and> (A, B) \<in> unit_rtc (unit_prods P)}"

definition unit_elim_rel :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods \<Rightarrow> bool" where
"unit_elim_rel ps ps' \<equiv> ps' = (unit_rm ps \<union> new_prods ps)"

definition Unit_free :: "('n, 't) Prods \<Rightarrow> bool" where
"Unit_free P = (\<nexists>A B. (A,[Nt B]) \<in> P)"

lemma Unit_free_if_unit_elim_rel: "unit_elim_rel ps ps' \<Longrightarrow> Unit_free ps'" 
unfolding unit_elim_rel_def unit_rm_def new_prods_def unit_prods_def Unit_free_def by simp

lemma unit_elim_rel_Eps_free:
  assumes "Eps_free ps" and "unit_elim_rel ps ps'"
  shows "Eps_free ps'"
  using assms 
  unfolding unit_elim_rel_def Eps_free_def unit_rm_def unit_prods_def new_prods_def by auto


subsection \<open>Code\<close>

definition unit_pairs :: "('n,'t) Prods \<Rightarrow> ('n \<times> 'n) set" where
"unit_pairs P = {(A,B). (A,[Nt B]) \<in> P}"

lemma unit_pairs_code[code]: "unit_pairs P = (\<Union>(A,w) \<in> P. case w of [Nt B] \<Rightarrow> {(A,B)} | _ \<Rightarrow> {})"
unfolding unit_pairs_def by (auto split: list.splits sym.splits)

lemma unit_prods_unit_pairs[code]: "unit_prods P = (\<lambda>(A,B). (A,[Nt B])) ` unit_pairs P"
unfolding unit_prods_def unit_pairs_def by (auto)

lemma unit_prods_iff_unit_pairs: "unit_prods P \<turnstile> [Nt A] \<Rightarrow> [Nt B] \<longleftrightarrow> (A, B) \<in> unit_pairs P"
unfolding unit_pairs_def unit_prods_def by(simp add: derive_singleton)

lemma Nts_unit_prods:
  "(A, B) \<in> unit_pairs P \<Longrightarrow> A \<in> Lhss (unit_prods P) \<and> B \<in> Rhs_Nts (unit_prods P)"
apply(auto simp: unit_prods_unit_pairs image_def Nts_Lhss_Rhs_Nts Lhss_def Rhs_Nts_def
           split: prod.splits)
 apply blast
by force

lemma rtc_unit_prods_if_tc_unit_pairs:
  "(A,B) \<in> (unit_pairs P)^+ \<Longrightarrow> (A,B) \<in> unit_rtc (unit_prods P)"
proof(induction rule: converse_trancl_induct)
  case (base A)
  then show ?case unfolding unit_rtc_def
  by (auto simp add: r_into_rtranclp unit_prods_iff_unit_pairs Nts_unit_prods Nts_Lhss_Rhs_Nts)
next
  case (step A A')
  then show ?case unfolding unit_rtc_def
    by (auto simp add: Nts_Lhss_Rhs_Nts Nts_unit_prods
        intro: converse_rtranclp_into_rtranclp[of "derive (unit_prods P)"]
               unit_prods_iff_unit_pairs[THEN iffD2])
qed

lemma tc_unit_pairs_if_rtc_unit_prods:
  fixes P :: "('n,'t)Prods"
  assumes "(A,B) \<in> unit_rtc (unit_prods P)"
  shows "A=B \<or> (A,B) \<in> (unit_pairs P)^+"
proof -
  have *: "unit_prods P \<turnstile> [Nt B] \<Rightarrow>* [Nt A] \<Longrightarrow> B=A \<or> (B,A) \<in> (unit_pairs P)^+" for A B
  proof(induction "[Nt B]::('n,'t)syms" arbitrary: B rule: converse_rtranclp_induct)
    case base thus ?case by simp
  next
    case (step \<alpha> C)
    from step.hyps(1) obtain C' where "(C,C') \<in> unit_pairs P" "\<alpha> = [Nt C']"
      by (auto simp: derive_singleton unit_prods_def unit_pairs_def)
    with step.hyps(2-)
    show ?case
      by (metis trancl.r_into_trancl trancl_into_trancl2)
  qed
  with assms show ?thesis
    by (simp add: unit_rtc_def)
qed

lemma unit_rm_Un_new_prods_eq: "unit_rm P \<union> new_prods P = unit_rm P \<union>
  {(A,r). \<exists>B. (B,r) \<in> unit_rm P \<and> (A, B) \<in> (unit_pairs P)^+}"
unfolding new_prods_def unit_rm_def
by(auto intro: rtc_unit_prods_if_tc_unit_pairs dest: tc_unit_pairs_if_rtc_unit_prods)

definition unit_elim_fun where
"unit_elim_fun P = unit_rm P \<union> new_prods P"

lemma unit_elim_fun_code[code]: "unit_elim_fun P = unit_rm P \<union>
  (\<Union>(B,r) \<in> unit_rm P. (\<lambda>(A,B). (A,r)) ` {(X,Y) \<in> (unit_pairs P)^+. Y = B})"
unfolding unit_elim_fun_def unit_rm_Un_new_prods_eq by auto

(* Test for executability only *)
lemma "unit_elim_fun {(0::int, [Nt 1]), (1, [Tm(2::int)])} = {(0, [Tm 2]), (1, [Tm 2])}"
by eval


subsection \<open>Finiteness and Existence\<close>

lemma finiteunit_prods: "finite ps \<Longrightarrow> finite (unit_prods ps)"
unfolding unit_prods_def
by (metis (no_types, lifting) case_prodE finite_subset mem_Collect_eq subsetI)

(* finiteness for unit_rtc *)
definition NtsCross :: "('n, 't) Prods  \<Rightarrow> ('n \<times> 'n) set" where
"NtsCross Ps = Nts Ps \<times> Nts Ps"

lemma finite_unit_rtc: 
  assumes "finite ps" 
  shows  "finite (unit_rtc ps)"
proof -
  have "finite (Nts ps)"
    unfolding Nts_def using assms finite_Nts_syms by auto
  hence "finite (NtsCross ps)"
    unfolding NtsCross_def by auto
  moreover have "unit_rtc ps \<subseteq> NtsCross ps"
    unfolding unit_rtc_def NtsCross_def by blast
  ultimately show ?thesis
    using assms infinite_super by fastforce 
qed

(* finiteness for new_prods *)
definition nPSlambda :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) \<Rightarrow> ('n, 't) Prods" where
"nPSlambda Ps d = {fst d} \<times> {r. (snd d, r) \<in> Ps}"

lemma npsImage: "\<Union>((nPSlambda (unit_rm ps)) ` (unit_rtc (unit_prods ps))) = new_prods ps"
  unfolding new_prods_def nPSlambda_def by fastforce

lemma finite_nPSlambda:
  assumes "finite Ps" 
  shows "finite (nPSlambda Ps d)"
proof -
  have "{(B, r). (B, r) \<in> Ps \<and> B = snd d} \<subseteq> Ps" 
    by blast
  hence "finite {(B, r). (B, r) \<in> Ps \<and> B = snd d}"
    using assms finite_subset by blast
  hence "finite (snd ` {(B, r). (B, r) \<in> Ps \<and> B = snd d})" 
    by simp
  moreover have "{r. (snd d, r) \<in> Ps} = (snd ` {(B, r). (B, r) \<in> Ps \<and> B = snd d})"
    by force
  ultimately show ?thesis
    using assms unfolding nPSlambda_def by simp
qed

lemma finite_unit_rm: "finite ps \<Longrightarrow> finite (unit_rm ps)"
unfolding unit_rm_def by simp

lemma finite_new_prods: assumes "finite ps" shows "finite (new_prods ps)"
proof -
  have "finite (unit_rtc (unit_prods ps))"
    using finiteunit_prods finite_unit_rtc assms by blast
  then show ?thesis
    using assms finite_unit_rm npsImage finite_nPSlambda finite_UN by metis
qed

lemma finiteunit_elim_relRules: "finite ps \<Longrightarrow> finite (unit_rm ps \<union> new_prods ps)"
by (simp add: finite_new_prods finite_unit_rm)

lemma unit_elim_rel_exists: "finite ps \<Longrightarrow> \<exists>ps'. unit_elim_rel ps ps' \<and> finite ps'"
unfolding unit_elim_rel_def using finite_list[OF finiteunit_elim_relRules] by blast

definition unit_elim :: "('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"unit_elim ps = (SOME ps'. unit_elim_rel ps ps' \<and> finite ps')"

lemma unit_elim_rel_unit_elim: "finite ps \<Longrightarrow> unit_elim_rel ps (unit_elim ps)"
by (metis (no_types, lifting) someI_ex unit_elim_def unit_elim_rel_exists)

(* towards theorem 4.4 *)

lemma inNonUnitProds:
  "p \<in> unit_rm ps \<Longrightarrow> p \<in> ps"
  unfolding unit_rm_def by blast

lemma psubDeriv:
  assumes "ps \<turnstile> u \<Rightarrow> v"
    and "\<forall>p \<in> ps. p \<in> ps'"
  shows "ps' \<turnstile> u \<Rightarrow> v"
  using assms by (meson derive_iff)

lemma psubRtcDeriv:
  assumes "ps \<turnstile> u \<Rightarrow>* v"
    and "\<forall>p \<in> ps. p \<in> ps'"
  shows "ps' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: psubDeriv rtranclp.rtrancl_into_rtrancl)

lemma unit_prods_deriv: 
  assumes "unit_prods ps \<turnstile> u \<Rightarrow>* v"
  shows "ps \<turnstile> u \<Rightarrow>* v"
proof -
  have "\<forall>p \<in> unit_prods ps. p \<in> ps"
    unfolding unit_prods_def by blast
  thus ?thesis 
    using assms psubRtcDeriv by blast
qed

lemma unit_elim_rel_r3:
  assumes "unit_elim_rel ps ps'" and "ps' \<turnstile> u \<Rightarrow> v"
  shows "ps \<turnstile> u \<Rightarrow>* v"
proof -
  obtain A \<alpha> r1 r2 where A: "(A, \<alpha>) \<in> ps' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2"
    using assms derive.cases by meson
  hence "(A, \<alpha>) \<in> unit_rm ps \<or> (A, \<alpha>) \<in> new_prods ps"
    using assms(1) unfolding unit_elim_rel_def by simp
  thus ?thesis
  proof
    assume "(A, \<alpha>) \<in> unit_rm ps"
    hence "(A, \<alpha>) \<in> ps"
      using inNonUnitProds by blast
    hence "ps \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis using A by simp
  next 
    assume "(A, \<alpha>) \<in> new_prods ps"
    from this obtain B where B: "(B, \<alpha>) \<in> unit_rm ps \<and> (A, B) \<in> unit_rtc (unit_prods ps)"
      unfolding new_prods_def by blast
    hence "unit_prods ps \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      unfolding unit_rtc_def by simp
    hence "ps \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      using unit_prods_deriv by blast
    hence 1: "ps \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow>* r1 @ [Nt B] @ r2"
      using derives_append derives_prepend by blast
    have "(B, \<alpha>) \<in> ps"
      using B inNonUnitProds by blast
    hence "ps \<turnstile> r1 @ [Nt B] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis 
      using 1 A by simp
  qed
qed

lemma unit_elim_rel_r4: 
  assumes "ps' \<turnstile> u \<Rightarrow>* v"
    and "unit_elim_rel ps ps'"
  shows "ps \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: unit_elim_rel_r3 rtranclp_trans)

lemma deriv_unit_rtc:
  assumes "ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "(A, B) \<in> unit_rtc (unit_prods ps)"
proof -
  have "(A, [Nt B]) \<in> ps"
    using assms by (simp add: derive_singleton)
  hence "(A, [Nt B]) \<in> unit_prods ps"
    unfolding unit_prods_def by blast
  hence "unit_prods ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
    by (simp add: derive_singleton)
  moreover have "B \<in> Nts (unit_prods ps) \<and> A \<in> Nts (unit_prods ps)"
    using \<open>(A, [Nt B]) \<in> unit_prods ps\<close> Nts_def Nts_syms_def by fastforce
  ultimately show ?thesis
    unfolding unit_rtc_def by blast
qed

lemma unit_elim_rel_r12: 
  assumes "unit_elim_rel ps ps'" "(A, \<alpha>) \<in> ps'"
  shows "(A, \<alpha>) \<notin> unit_prods ps"
  using assms unfolding unit_elim_rel_def unit_rm_def unit_prods_def new_prods_def by blast

lemma unit_elim_rel_r14: 
  assumes "unit_elim_rel ps ps'" 
    and "ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]" "ps' \<turnstile> [Nt B] \<Rightarrow> v"
  shows "ps' \<turnstile> [Nt A] \<Rightarrow> v"
proof -
  have 1: "(A, B) \<in> unit_rtc (unit_prods ps)"
    using deriv_unit_rtc assms(2) by fast
  have 2: "(B, v) \<in> ps'"
    using assms(3) by (simp add: derive_singleton)
  thus ?thesis
  proof (cases "(B, v) \<in> ps")
    case True
    hence "(B, v) \<in> unit_rm ps"
      unfolding unit_rm_def using assms(1) assms(3) unit_elim_rel_r12[of ps ps' B v] by (simp add: derive_singleton)
    then show ?thesis
    using 1 assms(1) unfolding unit_elim_rel_def new_prods_def derive_singleton by blast
  next
    case False
    hence "(B, v) \<in> new_prods ps"
      using assms(1) 2 unfolding unit_rm_def unit_elim_rel_def  by simp
    from this obtain C where C: "(C, v) \<in> unit_rm ps \<and> (B, C) \<in> unit_rtc (unit_prods ps)"
      unfolding new_prods_def by blast
    hence "unit_prods ps \<turnstile> [Nt A] \<Rightarrow>* [Nt C]"
      using 1 unfolding unit_rtc_def by auto
    hence "(A, C) \<in> unit_rtc (unit_prods ps)"
      unfolding unit_rtc_def using 1 C unit_rtc_def by fastforce
    hence "(A, v) \<in> new_prods ps"
      unfolding new_prods_def using C by blast
    hence "(A, v) \<in> ps'"
      using assms(1) unfolding unit_elim_rel_def  by blast
    thus ?thesis by (simp add: derive_singleton)
  qed
qed

lemma unit_elim_rel_r20_aux:
  assumes "ps \<turnstile> l @ [Nt A] @ r \<Rightarrow>* map Tm v" 
  shows "\<exists>\<alpha>. ps \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ \<alpha> @ r \<and> ps \<turnstile> l @ \<alpha> @ r \<Rightarrow>* map Tm v \<and> (A, \<alpha>) \<in> ps"
proof -
  obtain l' w r' where w: "ps \<turnstile> l \<Rightarrow>* l'  \<and> ps \<turnstile> [Nt A] \<Rightarrow>* w \<and>  ps \<turnstile> r \<Rightarrow>* r' \<and> map Tm v = l' @ w @ r'"
    using assms(1) by (metis derives_append_decomp)
  have "Nt A \<notin> set (map Tm v)" 
    using assms(1) by auto
  hence "[Nt A] \<noteq> w" 
    using w by auto
  from this obtain \<alpha> where \<alpha>: "ps \<turnstile> [Nt A] \<Rightarrow> \<alpha> \<and> ps \<turnstile> \<alpha> \<Rightarrow>* w"
    by (metis w converse_rtranclpE)
  hence "(A, \<alpha>) \<in> ps" 
    by (simp add: derive_singleton)
  thus ?thesis by (metis \<alpha> w derive.intros derives_append_decomp) 
qed

lemma unit_elim_rel_r20: 
  assumes "ps \<turnstile> u \<Rightarrow>* map Tm v" "unit_elim_rel ps ps'"
  shows "ps' \<turnstile> u \<Rightarrow>* map Tm v"
  using assms proof (induction rule: converse_derives_induct)
  case base
  then show ?case by blast
next
  case (step l A r w)
  then show ?case 
  proof (cases "(A, w) \<in> unit_prods ps")
    case True
    from this obtain B where "w = [Nt B]"
      unfolding unit_prods_def by blast
    have "ps' \<turnstile> l @ w @ r \<Rightarrow>* map Tm v \<and> Nt B \<notin> set (map Tm v)"
      using step.IH assms(2) by auto
    obtain \<alpha> where \<alpha>: "ps' \<turnstile> l @ [Nt B] @ r \<Rightarrow> l @ \<alpha> @ r \<and> ps' \<turnstile> l @ \<alpha> @ r \<Rightarrow>* map Tm v \<and> (B, \<alpha>) \<in> ps'"
      using assms(2) step.IH \<open>w=_\<close>  unit_elim_rel_r20_aux[of ps' l B r v] by blast
    hence "(A, \<alpha>) \<in> ps'"
      using assms(2) step.hyps(2) \<open>w=_\<close> unit_elim_rel_r14[of ps ps' A B \<alpha>] by (simp add: derive_singleton)
    hence "ps' \<turnstile> l @ [Nt A] @ r \<Rightarrow>* l @ \<alpha> @ r"
      using derive.simps by fastforce
    then show ?thesis 
      using \<alpha> by auto
  next
    case False
    hence "(A, w) \<in> unit_rm ps"
      unfolding unit_rm_def using step.hyps(2) by blast
    hence "(A, w) \<in> ps'"
      using assms(2) unfolding unit_elim_rel_def  by simp
    hence "ps' \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ w @ r"
      by (auto simp: derive.simps)
    then show ?thesis
      using step by simp
  qed
qed

theorem unit_elim_rel_Lang_eq: "unit_elim_rel ps ps' \<Longrightarrow> Lang ps' S = Lang ps S"
  unfolding Lang_def using unit_elim_rel_r4 unit_elim_rel_r20 by blast

corollary lang_unit_elim: "finite ps \<Longrightarrow> Lang (unit_elim ps) A = Lang ps A"
by (rule unit_elim_rel_Lang_eq[OF unit_elim_rel_unit_elim])

end