(*
Author: August Martin Stimpfle
Based on HOL4 theories by Aditi Barthwal
*)

section \<open>Elimination of Unit Productions\<close>

theory Unit_Elimination
imports Context_Free_Grammar (*"HOL-Library.While_Combinator"*)
begin

definition Unit_prods :: "('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"Unit_prods P = {(l,r) \<in> P. \<exists>A. r = [Nt A]}"

definition Unit_rtc :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) set" where
"Unit_rtc P = {(A,B). P \<turnstile> [Nt A] \<Rightarrow>* [Nt B] \<and> {A,B} \<subseteq> Nts P}"

definition Unit_rm :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where
"Unit_rm P = P - Unit_prods P"

definition New_prods :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where 
"New_prods P = {(A,r). \<exists>B. (B,r) \<in> Unit_rm P \<and> (A, B) \<in> Unit_rtc (Unit_prods P)}"

definition unit_elim_rel :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods \<Rightarrow> bool" where
"unit_elim_rel ps ps' \<equiv> ps' = (Unit_rm ps \<union> New_prods ps)"

definition Unit_free :: "('n, 't) Prods \<Rightarrow> bool" where
"Unit_free P = (\<nexists>A B. (A,[Nt B]) \<in> P)"

lemma Unit_free_if_unit_elim_rel: "unit_elim_rel ps ps' \<Longrightarrow> Unit_free ps'" 
unfolding unit_elim_rel_def Unit_rm_def New_prods_def Unit_prods_def Unit_free_def by simp

lemma unit_elim_rel_Eps_free:
  assumes "Eps_free ps" and "unit_elim_rel ps ps'"
  shows "Eps_free ps'"
  using assms 
  unfolding unit_elim_rel_def Eps_free_def Unit_rm_def Unit_prods_def New_prods_def by auto


subsection \<open>Code on lists\<close>

definition "trans_list_step ps = [(a,c). (a,b) \<leftarrow> ps, (b',c) \<leftarrow> ps, b=b']"

lemma set_trans_list_step_subset_trancl: "set (trans_list_step ps) \<subseteq> (set ps)^+"
unfolding trans_list_step_def by auto

(* TODO mv *)
lemma trancl_mono_subset: "A \<subseteq> B \<Longrightarrow> A^+ \<subseteq> B^+"
by (meson subsetI trancl_mono)
lemma trancl_incr: "r \<subseteq> r\<^sup>+"
by auto

lemma trancl_trancl_Un: "(A^+ \<union> B)^+ = (A \<union> B)^+"
proof
  show "(A\<^sup>+ \<union> B)\<^sup>+ \<subseteq> (A \<union> B)\<^sup>+"
    using trancl_id trancl_incr trancl_mono_subset trans_trancl by (metis le_sup_iff)
  show "(A \<union> B)\<^sup>+ \<subseteq> (A\<^sup>+ \<union> B)\<^sup>+"
    using trancl_mono_subset trancl_incr by (metis subset_refl sup_mono)
qed

(* TODO mv *)
lemma trancl_absorb_subset_trancl: "B \<subseteq> A^+ \<Longrightarrow> (A \<union> B)^+ = A^+"
  by (metis trancl_incr trancl_trancl_Un sup_idem sup.order_iff)

(* TODO mv *)
function trancl_list :: "('a * 'a) list \<Rightarrow> ('a * 'a) list" where 
"trancl_list ps =
  (let ps' = trans_list_step ps
   in if set ps' \<subseteq>  set ps then ps else trancl_list (List.union ps' ps))"
by pat_completeness auto

termination
proof
  let ?r = "\<lambda>ps::('a * 'a) list. card ((set ps)^+ - set(ps))"

  show "wf (measure ?r)" by blast

  fix ps ps' :: "('a * 'a) list"
  assume asms: "ps' = trans_list_step ps" "\<not> set ps' \<subseteq> set ps"
  let ?P = "set ps" let ?P' = "set(trans_list_step ps)"
  have "(?P' \<union> ?P)\<^sup>+ - (?P' \<union> ?P) = ?P\<^sup>+ - (?P' \<union> ?P)"
    using trancl_absorb_subset_trancl[OF set_trans_list_step_subset_trancl] by (metis Un_commute)
  also have "?P\<^sup>+ - (?P' \<union> ?P) < ?P\<^sup>+ - ?P"
    using asms(1,2) set_trans_list_step_subset_trancl by fastforce
  finally have "card((?P' \<union> ?P)\<^sup>+ - (?P' \<union> ?P)) < card (?P\<^sup>+ - ?P)"
    by (meson List.finite_set finite_Diff finite_trancl psubset_card_mono)
  with asms show "(List.union ps' ps, ps) \<in> measure ?r" by(simp)
qed

declare trancl_list.simps[code, simp del]

lemma set_trancl_list: "set(trancl_list ps) = (set ps)^+"
proof (induction ps rule: trancl_list.induct)
  case (1 ps)
  let ?P = "set ps" let ?P' = "set(trans_list_step ps)"
  show ?case
  proof (cases "?P' \<subseteq> ?P")
    case True
    then have "(a,b) \<in> set ps \<Longrightarrow> (b,c) \<in> set ps \<Longrightarrow> (a,c) \<in> set ps" for a b c
      unfolding trans_list_step_def by fastforce
    then show ?thesis using True trancl_id[OF transI, of ?P]
      using [[simp_depth_limit=3]] by(simp add: Let_def trancl_list.simps[of ps])
  next
    case False
    from 1[OF refl False] False
     show ?thesis using trancl_absorb_subset_trancl[OF set_trans_list_step_subset_trancl]
       by(auto simp add: Un_commute Let_def trancl_list.simps[of ps])
  qed
qed

definition unit_prods :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
"unit_prods ps = [(l,[Nt A]). (l,[Nt A]) \<leftarrow> ps]"

definition unit_rm :: "('n, 't) prods \<Rightarrow> ('n, 't) prods" where
"unit_rm ps = minus_list_set ps (unit_prods ps)"

lemma set_unit_prods: "set (unit_prods ps) = Unit_prods (set ps)"
unfolding unit_prods_def Unit_prods_def
by auto

lemma set_unit_rm: "set (unit_rm ps) = Unit_rm (set ps)"
unfolding unit_rm_def Unit_rm_def set_minus_list_set set_unit_prods ..

definition unit_pairs :: "('n,'t) prods \<Rightarrow> ('n \<times> 'n) list" where
"unit_pairs ps = [(A,B). (A,[Nt B]) \<leftarrow> ps]"

lemma Unit_prods_unit_pairs[code]:
  "Unit_prods (set ps) = set(map (\<lambda>(A,B). (A,[Nt B])) (unit_pairs ps))"
unfolding Unit_prods_def unit_pairs_def by (auto)

lemma Unit_prods_iff_unit_pairs:
  "Unit_prods (set ps) \<turnstile> [Nt A] \<Rightarrow> [Nt B] \<longleftrightarrow> (A, B) \<in> set(unit_pairs ps)"
unfolding unit_pairs_def Unit_prods_def by(auto simp add: derive_singleton)

lemma Nts_Unit_prods: "(A, B) \<in> set(unit_pairs ps)
  \<Longrightarrow> A \<in> Lhss (Unit_prods (set ps)) \<and> B \<in> Rhs_Nts (Unit_prods(set ps))"
apply(auto simp: Unit_prods_unit_pairs image_def Nts_Lhss_Rhs_Nts Lhss_def Rhs_Nts_def
           split: prod.splits)
 apply blast
by force

definition new_prods :: "('n, 't) prods \<Rightarrow> ('n, 't) prods" where
"new_prods ps = [(A,r). (B,r) \<leftarrow> unit_rm ps, (A,B') \<leftarrow> trancl_list(unit_pairs ps), B'=B]"

lemma rtc_Unit_prods_if_tc_unit_pairs:
  "(A,B) \<in> set(trancl_list(unit_pairs ps)) \<Longrightarrow> (A,B) \<in> Unit_rtc (Unit_prods (set ps))"
unfolding set_trancl_list
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
  assumes "(A,B) \<in> Unit_rtc (Unit_prods(set ps))"
  shows "A=B \<or> (A,B) \<in> set(trancl_list(unit_pairs ps))"
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
    by (simp add: set_trancl_list Unit_rtc_def)
qed

lemma Unit_rm_Un_New_prods_eq: "Unit_rm (set ps) \<union> New_prods (set ps) = Unit_rm (set ps) \<union>
  {(A,r). \<exists>B. (B,r) \<in> Unit_rm (set ps) \<and> (A, B) \<in> set(trancl_list(unit_pairs ps))}"
unfolding New_prods_def Unit_rm_def
by(auto intro: rtc_Unit_prods_if_tc_unit_pairs dest: tc_unit_pairs_if_rtc_Unit_prods)

definition Unit_elim :: "('n, 't) Prods \<Rightarrow> ('n, 't) Prods" where
"Unit_elim P = Unit_rm P \<union> New_prods P"

lemma Unit_elim_code[code]: "Unit_elim (set ps) = Unit_rm (set ps) \<union>
  (\<Union>(B,r) \<in> Unit_rm (set ps). (\<lambda>(A,B). (A,r)) ` {(X,Y) \<in> set(trancl_list(unit_pairs ps)). Y = B})"
unfolding Unit_elim_def Unit_rm_Un_New_prods_eq by auto

(* Test for executability only *)
lemma "Unit_elim {(0::int, [Nt 1]), (1, [Tm(2::int)])} = {(0, [Tm 2]), (1, [Tm 2])}"
by eval

corollary Unit_elim_correct: "unit_elim_rel (set ps) (Unit_elim (set ps))"
  by (metis Unit_elim_def unit_elim_rel_def)

definition unit_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) prods" where
"unit_elim ps = unit_rm ps @ new_prods ps"

value "let ps = [(1::int, [Nt 1]), (2, []::(int,nat)syms)] in (unit_rm ps,new_prods ps)"

lemma set_unit_elim: "set(unit_elim ps) = Unit_elim (set ps)"
unfolding unit_elim_def Unit_elim_def Unit_rm_Un_New_prods_eq
by(auto simp add: set_unit_rm new_prods_def)

corollary unit_elim_correct: "unit_elim_rel (set ps) (set(unit_elim ps))"
  by (metis set_unit_elim Unit_elim_correct)

subsection \<open>Finiteness and Existence\<close>

lemma finiteUnit_prods: "finite ps \<Longrightarrow> finite (Unit_prods ps)"
unfolding Unit_prods_def
by (metis (no_types, lifting) case_prodE finite_subset mem_Collect_eq subsetI)

(* finiteness for Unit_rtc *)
definition NtsCross :: "('n, 't) Prods  \<Rightarrow> ('n \<times> 'n) set" where
"NtsCross Ps = Nts Ps \<times> Nts Ps"

lemma finite_Unit_rtc: 
  assumes "finite ps" 
  shows  "finite (Unit_rtc ps)"
proof -
  have "finite (Nts ps)"
    unfolding Nts_def using assms finite_Nts_syms by auto
  hence "finite (NtsCross ps)"
    unfolding NtsCross_def by auto
  moreover have "Unit_rtc ps \<subseteq> NtsCross ps"
    unfolding Unit_rtc_def NtsCross_def by blast
  ultimately show ?thesis
    using assms infinite_super by fastforce 
qed

(* finiteness for New_prods *)
definition nPSlambda :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) \<Rightarrow> ('n, 't) Prods" where
"nPSlambda Ps d = {fst d} \<times> {r. (snd d, r) \<in> Ps}"

lemma npsImage: "\<Union>((nPSlambda (Unit_rm ps)) ` (Unit_rtc (Unit_prods ps))) = New_prods ps"
  unfolding New_prods_def nPSlambda_def by fastforce

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

lemma finite_Unit_rm: "finite ps \<Longrightarrow> finite (Unit_rm ps)"
unfolding Unit_rm_def by simp

lemma finite_New_prods: assumes "finite ps" shows "finite (New_prods ps)"
proof -
  have "finite (Unit_rtc (Unit_prods ps))"
    using finiteUnit_prods finite_Unit_rtc assms by blast
  then show ?thesis
    using assms finite_Unit_rm npsImage finite_nPSlambda finite_UN by metis
qed

lemma finiteunit_elim_relRules: "finite ps \<Longrightarrow> finite (Unit_rm ps \<union> New_prods ps)"
by (simp add: finite_New_prods finite_Unit_rm)

lemma unit_elim_rel_exists: "finite ps \<Longrightarrow> \<exists>ps'. unit_elim_rel ps ps' \<and> finite ps'"
unfolding unit_elim_rel_def using finite_list[OF finiteunit_elim_relRules] by blast

(* towards theorem 4.4 *)

lemma inNonUnitProds:
  "p \<in> Unit_rm ps \<Longrightarrow> p \<in> ps"
  unfolding Unit_rm_def by blast

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

lemma Unit_prods_deriv: 
  assumes "Unit_prods ps \<turnstile> u \<Rightarrow>* v"
  shows "ps \<turnstile> u \<Rightarrow>* v"
proof -
  have "\<forall>p \<in> Unit_prods ps. p \<in> ps"
    unfolding Unit_prods_def by blast
  thus ?thesis 
    using assms psubRtcDeriv by blast
qed

lemma unit_elim_rel_r3:
  assumes "unit_elim_rel ps ps'" and "ps' \<turnstile> u \<Rightarrow> v"
  shows "ps \<turnstile> u \<Rightarrow>* v"
proof -
  obtain A \<alpha> r1 r2 where A: "(A, \<alpha>) \<in> ps' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2"
    using assms derive.cases by meson
  hence "(A, \<alpha>) \<in> Unit_rm ps \<or> (A, \<alpha>) \<in> New_prods ps"
    using assms(1) unfolding unit_elim_rel_def by simp
  thus ?thesis
  proof
    assume "(A, \<alpha>) \<in> Unit_rm ps"
    hence "(A, \<alpha>) \<in> ps"
      using inNonUnitProds by blast
    hence "ps \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis using A by simp
  next 
    assume "(A, \<alpha>) \<in> New_prods ps"
    from this obtain B where B: "(B, \<alpha>) \<in> Unit_rm ps \<and> (A, B) \<in> Unit_rtc (Unit_prods ps)"
      unfolding New_prods_def by blast
    hence "Unit_prods ps \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      unfolding Unit_rtc_def by simp
    hence "ps \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      using Unit_prods_deriv by blast
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

lemma deriv_Unit_rtc:
  assumes "ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "(A, B) \<in> Unit_rtc (Unit_prods ps)"
proof -
  have "(A, [Nt B]) \<in> ps"
    using assms by (simp add: derive_singleton)
  hence "(A, [Nt B]) \<in> Unit_prods ps"
    unfolding Unit_prods_def by blast
  hence "Unit_prods ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
    by (simp add: derive_singleton)
  moreover have "B \<in> Nts (Unit_prods ps) \<and> A \<in> Nts (Unit_prods ps)"
    using \<open>(A, [Nt B]) \<in> Unit_prods ps\<close> Nts_def Nts_syms_def by fastforce
  ultimately show ?thesis
    unfolding Unit_rtc_def by blast
qed

lemma unit_elim_rel_r12: 
  assumes "unit_elim_rel ps ps'" "(A, \<alpha>) \<in> ps'"
  shows "(A, \<alpha>) \<notin> Unit_prods ps"
  using assms unfolding unit_elim_rel_def Unit_rm_def Unit_prods_def New_prods_def by blast

lemma unit_elim_rel_r14: 
  assumes "unit_elim_rel ps ps'" 
    and "ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]" "ps' \<turnstile> [Nt B] \<Rightarrow> v"
  shows "ps' \<turnstile> [Nt A] \<Rightarrow> v"
proof -
  have 1: "(A, B) \<in> Unit_rtc (Unit_prods ps)"
    using deriv_Unit_rtc assms(2) by fast
  have 2: "(B, v) \<in> ps'"
    using assms(3) by (simp add: derive_singleton)
  thus ?thesis
  proof (cases "(B, v) \<in> ps")
    case True
    hence "(B, v) \<in> Unit_rm ps"
      unfolding Unit_rm_def using assms(1) assms(3) unit_elim_rel_r12[of ps ps' B v] by (simp add: derive_singleton)
    then show ?thesis
    using 1 assms(1) unfolding unit_elim_rel_def New_prods_def derive_singleton by blast
  next
    case False
    hence "(B, v) \<in> New_prods ps"
      using assms(1) 2 unfolding Unit_rm_def unit_elim_rel_def  by simp
    from this obtain C where C: "(C, v) \<in> Unit_rm ps \<and> (B, C) \<in> Unit_rtc (Unit_prods ps)"
      unfolding New_prods_def by blast
    hence "Unit_prods ps \<turnstile> [Nt A] \<Rightarrow>* [Nt C]"
      using 1 unfolding Unit_rtc_def by auto
    hence "(A, C) \<in> Unit_rtc (Unit_prods ps)"
      unfolding Unit_rtc_def using 1 C Unit_rtc_def by fastforce
    hence "(A, v) \<in> New_prods ps"
      unfolding New_prods_def using C by blast
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
  proof (cases "(A, w) \<in> Unit_prods ps")
    case True
    from this obtain B where "w = [Nt B]"
      unfolding Unit_prods_def by blast
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
    hence "(A, w) \<in> Unit_rm ps"
      unfolding Unit_rm_def using step.hyps(2) by blast
    hence "(A, w) \<in> ps'"
      using assms(2) unfolding unit_elim_rel_def  by simp
    hence "ps' \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ w @ r"
      by (auto simp: derive.simps)
    then show ?thesis
      using step by simp
  qed
qed

theorem unit_elim_rel_Lang_eq: "unit_elim_rel P P' \<Longrightarrow> Lang P' S = Lang P S"
  unfolding Lang_def using unit_elim_rel_r4 unit_elim_rel_r20 by blast

corollary Lang_Unit_elim: "Lang (Unit_elim (set ps)) A = lang ps A"
by (rule unit_elim_rel_Lang_eq[OF Unit_elim_correct])

corollary lang_unit_elim: "lang (unit_elim ps) A = lang ps A"
by (metis set_unit_elim Lang_Unit_elim)

end