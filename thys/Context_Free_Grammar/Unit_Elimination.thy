(*
Author: August Martin Stimpfle; Tobias Nipkow (simplification)
Based on HOL4 theories by Aditi Barthwal
*)

section \<open>Elimination of Unit Productions\<close>

theory Unit_Elimination
imports Context_Free_Grammar
begin

definition Unit_prods :: "('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"Unit_prods P = {(l,r) \<in> P. \<exists>A. r = [Nt A]}"

definition Unit_rtc :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) set" where
"Unit_rtc P = {(A,B). Unit_prods P \<turnstile> [Nt A] \<Rightarrow>* [Nt B] \<and> A \<in> Nts P}"

definition Unit_rm :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where
"Unit_rm P = P - Unit_prods P"

definition Unit_elim :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where 
"Unit_elim P = {(A,r). \<exists>B. (B,r) \<in> Unit_rm P \<and> (A, B) \<in> Unit_rtc P}"

lemma Unit_rtc_refl: "(A, \<alpha>) \<in> P \<Longrightarrow> (A, A) \<in> Unit_rtc P"
by (auto simp add: Unit_rtc_def Nts_Lhss_Rhs_Nts in_LhssI)

lemma Unit_Free_Unit_elim: "Unit_free (Unit_elim P)" 
unfolding Unit_elim_def Unit_rm_def Unit_prods_def Unit_free_def by simp

lemma Unit_elim_Eps_free:
  assumes "Eps_free P"
  shows "Eps_free (Unit_elim P)"
  using assms 
  unfolding Unit_elim_def Eps_free_def Unit_rm_def Unit_prods_def by auto

lemma Tms_Unit_elim_subset: "Tms (Unit_elim P) \<subseteq> Tms P"
unfolding Unit_elim_def Unit_rm_def Tms_def by(auto)

lemma derives_Unit_in_Nts: "\<lbrakk> P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]; A \<in> Nts P \<rbrakk> \<Longrightarrow> B \<in> Nts P"
by (meson in_Nts_iff_if_derives list.set_intros(1) reachable_def)

subsection \<open>Code on lists\<close>

definition unit_prods :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
"unit_prods ps = [(l,[Nt A]). (l,[Nt A]) \<leftarrow> ps]"

definition unit_pairs :: "('n,'t) prods \<Rightarrow> ('n \<times> 'n) list" where
"unit_pairs ps = [(A,B). (A,[Nt B]) \<leftarrow> ps]"

definition unit_rm :: "('n, 't) prods \<Rightarrow> ('n, 't) prods" where
"unit_rm ps = minus_list_set ps (unit_prods ps)"

definition unit_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) prods" where
"unit_elim ps = [(A,r). (B,r) \<leftarrow> unit_rm ps, (A,B') \<leftarrow> (B,B)#trancl_list(unit_pairs ps), B'=B]"

lemma set_unit_prods: "set (unit_prods ps) = Unit_prods (set ps)"
unfolding unit_prods_def Unit_prods_def
by auto

lemma set_unit_rm: "set (unit_rm ps) = Unit_rm (set ps)"
unfolding unit_rm_def Unit_rm_def set_minus_list_set set_unit_prods ..

lemma Unit_prods_unit_pairs[code]:
  "Unit_prods (set ps) = set(map (\<lambda>(A,B). (A,[Nt B])) (unit_pairs ps))"
unfolding Unit_prods_def unit_pairs_def by (auto)

lemma Unit_prods_iff_unit_pairs:
  "Unit_prods (set ps) \<turnstile> [Nt A] \<Rightarrow> [Nt B] \<longleftrightarrow> (A, B) \<in> set(unit_pairs ps)"
unfolding unit_pairs_def Unit_prods_def by(auto simp add: derive_singleton)

lemma Nts_Unit_prods: "(A, B) \<in> set(unit_pairs ps)
  \<Longrightarrow> A \<in> Lhss (set ps) \<and> B \<in> Rhs_Nts (set ps)"
apply(auto simp: image_def Nts_Lhss_Rhs_Nts Lhss_def Rhs_Nts_def unit_pairs_def Bex_def
           split: prod.splits)
  apply blast
by force

lemma rtc_Unit_prods_if_tc_unit_pairs:
  "(A,B) \<in> (set(unit_pairs ps))^+ \<Longrightarrow> (A,B) \<in> Unit_rtc (set ps)"
proof(induction rule: converse_trancl_induct)
  case (base A)
  then show ?case unfolding Unit_rtc_def
  by (auto simp add: r_into_rtranclp Unit_prods_iff_unit_pairs Nts_Unit_prods Nts_Lhss_Rhs_Nts)
next
  case (step A A')
  then show ?case unfolding Unit_rtc_def
    by (auto simp add: Nts_Lhss_Rhs_Nts Nts_Unit_prods
        intro: converse_rtranclp_into_rtranclp[of "derive (Unit_prods(set ps))"]
               Unit_prods_iff_unit_pairs[THEN iffD2])
qed

lemma tc_unit_pairs_if_rtc_Unit_prods:
  fixes ps :: "('n,'t)prods"
  assumes "(A,B) \<in> Unit_rtc (set ps)"
  shows "A=B \<or> (A,B) \<in> (set(unit_pairs ps))^+"
proof -
  have *: "Unit_prods(set ps) \<turnstile> [Nt B] \<Rightarrow>* [Nt A] \<Longrightarrow> B=A \<or> (B,A) \<in> (set(unit_pairs ps))^+" for A B
  proof(induction "[Nt B]::('n,'t)syms" arbitrary: B rule: converse_rtranclp_induct)
    case base thus ?case by simp
  next
    case (step \<alpha> C)
    from step.hyps(1) obtain C' where "(C,C') \<in> set(unit_pairs ps)" "\<alpha> = [Nt C']"
      by (auto simp: derive_singleton Unit_prods_def unit_pairs_def)
    with step.hyps(2-)
    show ?case
      by (metis trancl.r_into_trancl trancl_into_trancl2)
  qed
  with assms show ?thesis
    by (simp add: Unit_rtc_def)
qed

lemma Unit_elim_set[code]: "Unit_elim (set ps) = set (unit_elim ps)"
unfolding Unit_elim_def unit_elim_def
by (auto simp: set_unit_rm Unit_rm_def Unit_rtc_refl set_trancl_list rtc_Unit_prods_if_tc_unit_pairs
  dest!: tc_unit_pairs_if_rtc_Unit_prods)

(* Test for executability only *)
lemma "Unit_elim {(0::int, [Nt 1]), (1, [Tm(2::int)])} = {(0, [Tm 2]), (1, [Tm 2])}"
by eval


subsection \<open>Finiteness and Existence\<close>

lemma finiteUnit_prods: "finite P \<Longrightarrow> finite (Unit_prods P)"
unfolding Unit_prods_def
by (metis (no_types, lifting) case_prodE finite_subset mem_Collect_eq subsetI)

lemma Unit_prods_subset: "Unit_prods P \<subseteq> P"
  unfolding Unit_prods_def by auto
lemma finite_Unit_rtc: 
  assumes "finite P"
  shows  "finite (Unit_rtc P)"
proof -
  have "finite (Nts P)"
    unfolding Nts_def using assms finite_Nts_syms by auto
  hence "finite (Nts P \<times> Nts P)"
    by auto
  moreover have "Unit_rtc P \<subseteq> Nts P \<times> Nts P"
    using derives_Unit_in_Nts[of P] derives_mono[OF Unit_prods_subset[of P]]
    by (auto simp:Unit_rtc_def)
  ultimately show ?thesis
    using assms infinite_super by fastforce 
qed

(* finiteness for New_prods *)
definition nPSlambda :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) \<Rightarrow> ('n, 't) Prods" where
"nPSlambda P d = {fst d} \<times> {r. (snd d, r) \<in> P}"

lemma npsImage: "Unit_elim P = \<Union>((nPSlambda (Unit_rm P)) ` (Unit_rtc P))"
  unfolding Unit_elim_def nPSlambda_def by fastforce

lemma finite_nPSlambda:
  assumes "finite P" 
  shows "finite (nPSlambda P d)"
proof -
  have "{(B, r). (B, r) \<in> P \<and> B = snd d} \<subseteq> P" 
    by blast
  hence "finite {(B, r). (B, r) \<in> P \<and> B = snd d}"
    using assms finite_subset by blast
  hence "finite (snd ` {(B, r). (B, r) \<in> P \<and> B = snd d})" 
    by simp
  moreover have "{r. (snd d, r) \<in> P} = (snd ` {(B, r). (B, r) \<in> P \<and> B = snd d})"
    by force
  ultimately show ?thesis
    using assms unfolding nPSlambda_def by simp
qed

lemma finite_Unit_elim: assumes "finite P" shows "finite (Unit_elim P)"
proof -
  have "finite (Unit_rtc P)"
    using finiteUnit_prods finite_Unit_rtc assms by blast
  then show ?thesis
    by(simp add:  npsImage Unit_rm_def finite_nPSlambda assms)
qed

(* towards theorem 4.4 *)

lemma inNonUnitProds:
  "p \<in> Unit_rm P \<Longrightarrow> p \<in> P"
  unfolding Unit_rm_def by blast

lemma Unit_elim_rel_r3:
  assumes "Unit_elim P \<turnstile> u \<Rightarrow> v"
  shows "P \<turnstile> u \<Rightarrow>* v"
proof -
  obtain A \<alpha> r1 r2 where A: "(A, \<alpha>) \<in> Unit_elim P \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2"
    using assms derive.cases by meson
  hence "(A, \<alpha>) \<in> Unit_elim P"
    using assms(1) unfolding Unit_elim_def by simp
  from this obtain B where B: "(B, \<alpha>) \<in> Unit_rm P \<and> (A, B) \<in> Unit_rtc P"
    unfolding Unit_elim_def by blast
  hence "Unit_prods P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
    unfolding Unit_rtc_def by simp
  hence "P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
    using  Unit_prods_subset derives_mono by blast
  hence 1: "P \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow>* r1 @ [Nt B] @ r2"
    using derives_append derives_prepend by blast
  have "(B, \<alpha>) \<in> P"
    using B inNonUnitProds by blast
  hence "P \<turnstile> r1 @ [Nt B] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
    by (auto simp: derive.simps)
  thus ?thesis 
    using 1 A by simp
qed

lemma Unit_elim_rel_r4: 
  assumes "Unit_elim P \<turnstile> u \<Rightarrow>* v"
  shows "P \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: Unit_elim_rel_r3 rtranclp_trans)

lemma deriv_Unit_rtc:
  assumes "P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "(A, B) \<in> Unit_rtc P"
proof -
  have "(A, [Nt B]) \<in> P"
    using assms by (simp add: derive_singleton)
  hence "(A, [Nt B]) \<in> Unit_prods P"
    unfolding Unit_prods_def by blast
  hence "Unit_prods P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
    by (simp add: derive_singleton)
  moreover have "B \<in> Nts P \<and> A \<in> Nts P"
    using \<open>(A, [Nt B]) \<in> P\<close> Nts_def Nts_syms_def by fastforce
  ultimately show ?thesis
    unfolding Unit_rtc_def by blast
qed

lemma Unit_elim_rel_r14: 
  assumes "P \<turnstile> [Nt A] \<Rightarrow> [Nt B]" "Unit_elim P \<turnstile> [Nt B] \<Rightarrow> v"
  shows "Unit_elim P \<turnstile> [Nt A] \<Rightarrow> v"
proof -
  have 1: "(A, B) \<in> Unit_rtc P"
    using deriv_Unit_rtc assms(1) by fast
  have 2: "(B, v) \<in> Unit_elim P"
    using assms(2) by (simp add: derive_singleton)
  thus ?thesis
  proof (cases "(B, v) \<in> P")
    case True
    hence "(B, v) \<in> Unit_rm P"
      using 2 unfolding Unit_rm_def Unit_elim_def Unit_prods_def by blast
    then show ?thesis
    using 1 unfolding Unit_elim_def derive_singleton by blast
  next
    case False
    hence "(B, v) \<in> Unit_elim P"
      using assms(1) 2 unfolding Unit_rm_def Unit_elim_def  by simp
    from this obtain C where C: "(C, v) \<in> Unit_rm P \<and> (B, C) \<in> Unit_rtc P"
      unfolding Unit_elim_def by blast
    hence "Unit_prods P \<turnstile> [Nt A] \<Rightarrow>* [Nt C]"
      using 1 unfolding Unit_rtc_def by auto
    hence "(A, C) \<in> Unit_rtc P"
      unfolding Unit_rtc_def using 1 C Unit_rtc_def by fastforce
    hence "(A, v) \<in> Unit_elim P"
      unfolding Unit_elim_def using C by blast
    hence "(A, v) \<in> Unit_elim P"
      using assms(1) unfolding Unit_elim_def  by blast
    thus ?thesis by (simp add: derive_singleton)
  qed
qed

lemma Unit_elim_rel_r20_aux:
  assumes "P \<turnstile> l @ [Nt A] @ r \<Rightarrow>* map Tm v" 
  shows "\<exists>\<alpha>. P \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ \<alpha> @ r \<and> P \<turnstile> l @ \<alpha> @ r \<Rightarrow>* map Tm v \<and> (A, \<alpha>) \<in> P"
proof -
  obtain l' w r' where w: "P \<turnstile> l \<Rightarrow>* l'  \<and> P \<turnstile> [Nt A] \<Rightarrow>* w \<and>  P \<turnstile> r \<Rightarrow>* r' \<and> map Tm v = l' @ w @ r'"
    using assms(1) by (metis derives_appendD)
  have "Nt A \<notin> set (map Tm v)" 
    using assms(1) by auto
  hence "[Nt A] \<noteq> w" 
    using w by auto
  from this obtain \<alpha> where \<alpha>: "P \<turnstile> [Nt A] \<Rightarrow> \<alpha> \<and> P \<turnstile> \<alpha> \<Rightarrow>* w"
    by (metis w converse_rtranclpE)
  hence "(A, \<alpha>) \<in> P" 
    by (simp add: derive_singleton)
  thus ?thesis by (metis \<alpha> w derive.intros derives_appendD) 
qed

lemma Unit_elim_rel_complete: 
  assumes "P \<turnstile> u \<Rightarrow>* map Tm v"
  shows "Unit_elim P \<turnstile> u \<Rightarrow>* map Tm v"
  using assms proof (induction rule: converse_derives_induct)
  case base
  then show ?case by blast
next
  case (step l A r w)
  let ?P = "Unit_elim P"
  show ?case 
  proof (cases "(A, w) \<in> Unit_prods P")
    case True
    from this obtain B where "w = [Nt B]"
      unfolding Unit_prods_def by blast
    have "?P \<turnstile> l @ w @ r \<Rightarrow>* map Tm v \<and> Nt B \<notin> set (map Tm v)"
      using step.IH by auto
    obtain \<alpha> where \<alpha>: "?P \<turnstile> l @ [Nt B] @ r \<Rightarrow> l @ \<alpha> @ r \<and> ?P \<turnstile> l @ \<alpha> @ r \<Rightarrow>* map Tm v \<and> (B, \<alpha>) \<in> ?P"
      using step.IH \<open>w=_\<close>  Unit_elim_rel_r20_aux[of ?P l B r v] by blast
    hence "(A, \<alpha>) \<in> ?P"
      using step.hyps(2) \<open>w=_\<close> Unit_elim_rel_r14[of P] by (simp add: derive_singleton)
    hence "?P \<turnstile> l @ [Nt A] @ r \<Rightarrow>* l @ \<alpha> @ r"
      using derive.simps by fastforce
    then show ?thesis 
      using \<alpha> by auto
  next
    case False
    hence "(A, w) \<in> Unit_rm P"
      unfolding Unit_rm_def using step.hyps(2) by blast
    hence "(A, w) \<in> ?P"
      using assms(1) Unit_rtc_refl step.hyps(2) unfolding Unit_elim_def by fastforce
    hence "?P \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ w @ r"
      by (auto simp: derive.simps)
    then show ?thesis
      using step by simp
  qed
qed

theorem Lang_Unit_elim: "Lang (Unit_elim P) S = Lang P S"
  unfolding Lang_def using Unit_elim_rel_r4 Unit_elim_rel_complete by blast

corollary lang_unit_elim: "lang (unit_elim ps) A = lang ps A"
by (metis Lang_Unit_elim Unit_elim_set)

end