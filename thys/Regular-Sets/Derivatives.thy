header "Derivatives of regular expressions"

(* Author: Christian Urban *)

theory Derivatives
imports Regular_Exp
begin

text{* This theory is based on work by Brozowski \cite{Brzozowski64} and Antimirov \cite{Antimirov95}. *}

subsection {* Left-Quotients of languages *}

definition Deriv :: "'a \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "Deriv x A = { xs. x#xs \<in> A }"

definition Derivs :: "'a list \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "Derivs xs A = { ys. xs @ ys \<in> A }"

abbreviation 
  Derivss :: "'a list \<Rightarrow> 'a lang set \<Rightarrow> 'a lang"
where
  "Derivss s As \<equiv> \<Union> (Derivs s) ` As"


lemma Deriv_empty[simp]:   "Deriv a {} = {}"
  and Deriv_epsilon[simp]: "Deriv a {[]} = {}"
  and Deriv_char[simp]:    "Deriv a {[b]} = (if a = b then {[]} else {})"
  and Deriv_union[simp]:   "Deriv a (A \<union> B) = Deriv a A \<union> Deriv a B"
by (auto simp: Deriv_def)

lemma Deriv_conc_subset:
"Deriv a A @@ B \<subseteq> Deriv a (A @@ B)" (is "?L \<subseteq> ?R")
proof 
  fix w assume "w \<in> ?L"
  then obtain u v where "w = u @ v" "a # u \<in> A" "v \<in> B"
    by (auto simp: Deriv_def)
  then have "a # w \<in> A @@ B"
    by (auto intro: concI[of "a # u", simplified])
  thus "w \<in> ?R" by (auto simp: Deriv_def)
qed

lemma Der_conc [simp]:
  shows "Deriv c (A @@ B) = (Deriv c A) @@ B \<union> (if [] \<in> A then Deriv c B else {})"
unfolding Deriv_def conc_def
by (auto simp add: Cons_eq_append_conv)

lemma Deriv_star [simp]:
  shows "Deriv c (star A) = (Deriv c A) @@ star A"
proof -
  have incl: "[] \<in> A \<Longrightarrow> Deriv c (star A) \<subseteq> (Deriv c A) @@ star A"
    unfolding Deriv_def conc_def 
    apply(auto simp add: Cons_eq_append_conv)
    apply(drule star_decom)
    apply(auto simp add: Cons_eq_append_conv)
    done

  have "Deriv c (star A) = Deriv c (A @@ star A \<union> {[]})"
    by (simp only: star_unfold_left[symmetric])
  also have "... = Deriv c (A @@ star A)"
    by (simp only: Deriv_union) (simp)
  also have "... =  (Deriv c A) @@ (star A) \<union> (if [] \<in> A then Deriv c (star A) else {})"
    by simp
   also have "... =  (Deriv c A) @@ star A"
    using incl by auto
  finally show "Deriv c (star A) = (Deriv c A) @@ star A" . 
qed

lemma Derivs_simps [simp]:
  shows "Derivs [] A = A"
  and   "Derivs (c # s) A = Derivs s (Deriv c A)"
  and   "Derivs (s1 @ s2) A = Derivs s2 (Derivs s1 A)"
unfolding Derivs_def Deriv_def by auto


subsection {* Brozowski's derivatives of regular expressions *}

fun
  nullable :: "'a rexp \<Rightarrow> bool"
where
  "nullable (Zero) = False"
| "nullable (One) = True"
| "nullable (Atom c) = False"
| "nullable (Plus r1 r2) = (nullable r1 \<or> nullable r2)"
| "nullable (Times r1 r2) = (nullable r1 \<and> nullable r2)"
| "nullable (Star r) = True"

fun
  deriv :: "'a \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "deriv c (Zero) = Zero"
| "deriv c (One) = Zero"
| "deriv c (Atom c') = (if c = c' then One else Zero)"
| "deriv c (Plus r1 r2) = Plus (deriv c r1) (deriv c r2)"
| "deriv c (Times r1 r2) = 
    (if nullable r1 then Plus (Times (deriv c r1) r2) (deriv c r2) else Times (deriv c r1) r2)"
| "deriv c (Star r) = Times (deriv c r) (Star r)"

fun 
  derivs :: "'a list \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "derivs [] r = r"
| "derivs (c # s) r = derivs s (deriv c r)"


lemma nullable_iff:
  shows "nullable r \<longleftrightarrow> [] \<in> lang r"
by (induct r) (auto simp add: conc_def split: if_splits)

lemma Deriv_deriv:
  shows "Deriv c (lang r) = lang (deriv c r)"
by (induct r) (simp_all add: nullable_iff)

lemma Derivs_derivs:
  shows "Derivs s (lang r) = lang (derivs s r)"
by (induct s arbitrary: r) (simp_all add: Deriv_deriv)


subsection {* Antimirov's partial derivatives *}

abbreviation
  "Timess rs r \<equiv> {Times r' r | r'. r' \<in> rs}"

fun
  pderiv :: "'a \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp set"
where
  "pderiv c Zero = {}"
| "pderiv c One = {}"
| "pderiv c (Atom c') = (if c = c' then {One} else {})"
| "pderiv c (Plus r1 r2) = (pderiv c r1) \<union> (pderiv c r2)"
| "pderiv c (Times r1 r2) = 
    (if nullable r1 then Timess (pderiv c r1) r2 \<union> pderiv c r2 else Timess (pderiv c r1) r2)"
| "pderiv c (Star r) = Timess (pderiv c r) (Star r)"

fun
  pderivs :: "'a list \<Rightarrow> 'a rexp \<Rightarrow> ('a rexp) set"
where
  "pderivs [] r = {r}"
| "pderivs (c # s) r = \<Union> (pderivs s) ` (pderiv c r)"

abbreviation
 pderiv_set :: "'a \<Rightarrow> 'a rexp set \<Rightarrow> 'a rexp set"
where
  "pderiv_set c rs \<equiv> \<Union> pderiv c ` rs"

abbreviation
  pderivs_set :: "'a list \<Rightarrow> 'a rexp set \<Rightarrow> 'a rexp set"
where
  "pderivs_set s rs \<equiv> \<Union> (pderivs s) ` rs"

lemma pderivs_append:
  "pderivs (s1 @ s2) r = \<Union> (pderivs s2) ` (pderivs s1 r)"
by (induct s1 arbitrary: r) (simp_all)

lemma pderivs_snoc:
  shows "pderivs (s @ [c]) r = pderiv_set c (pderivs s r)"
by (simp add: pderivs_append)

lemma pderivs_simps [simp]:
  shows "pderivs s Zero = (if s = [] then {Zero} else {})"
  and   "pderivs s One = (if s = [] then {One} else {})"
  and   "pderivs s (Plus r1 r2) = (if s = [] then {Plus r1 r2} else (pderivs s r1) \<union> (pderivs s r2))"
by (induct s) (simp_all)

lemma pderivs_Atom:
  shows "pderivs s (Atom c) \<subseteq> {Atom c, One}"
by (induct s) (simp_all)

subsection {* Relating left-quotients and partial derivatives *}

lemma Deriv_pderiv:
  shows "Deriv c (lang r) = \<Union> lang ` (pderiv c r)"
by (induct r) (auto simp add: nullable_iff conc_UNION_distrib)

lemma Derivs_pderivs:
  shows "Derivs s (lang r) = \<Union> lang ` (pderivs s r)"
proof (induct s arbitrary: r)
  case (Cons c s)
  have ih: "\<And>r. Derivs s (lang r) = \<Union> lang ` (pderivs s r)" by fact
  have "Derivs (c # s) (lang r) = Derivs s (Deriv c (lang r))" by simp
  also have "\<dots> = Derivs s (\<Union> lang ` (pderiv c r))" by (simp add: Deriv_pderiv)
  also have "\<dots> = Derivss s (lang ` (pderiv c r))"
    by (auto simp add:  Derivs_def)
  also have "\<dots> = \<Union> lang ` (pderivs_set s (pderiv c r))"
    using ih by auto
  also have "\<dots> = \<Union> lang ` (pderivs (c # s) r)" by simp
  finally show "Derivs (c # s) (lang r) = \<Union> lang ` pderivs (c # s) r" .
qed (simp add: Derivs_def)

subsection {* Relating derivatives and partial derivatives *}

lemma deriv_pderiv:
  shows "(\<Union> lang ` (pderiv c r)) = lang (deriv c r)"
unfolding Deriv_deriv[symmetric] Deriv_pderiv by simp

lemma derivs_pderivs:
  shows "(\<Union> lang ` (pderivs s r)) = lang (derivs s r)"
unfolding Derivs_derivs[symmetric] Derivs_pderivs by simp


subsection {* Finiteness property of partial derivatives *}

definition
  pderivs_lang :: "'a lang \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp set"
where
  "pderivs_lang A r \<equiv> \<Union>x \<in> A. pderivs x r"

lemma pderivs_lang_subsetI:
  assumes "\<And>s. s \<in> A \<Longrightarrow> pderivs s r \<subseteq> C"
  shows "pderivs_lang A r \<subseteq> C"
using assms unfolding pderivs_lang_def by (rule UN_least)

lemma pderivs_lang_union:
  shows "pderivs_lang (A \<union> B) r = (pderivs_lang A r \<union> pderivs_lang B r)"
by (simp add: pderivs_lang_def)

lemma pderivs_lang_subset:
  shows "A \<subseteq> B \<Longrightarrow> pderivs_lang A r \<subseteq> pderivs_lang B r"
by (auto simp add: pderivs_lang_def)

definition
  "UNIV1 \<equiv> UNIV - {[]}"

lemma pderivs_lang_Zero [simp]:
  shows "pderivs_lang UNIV1 Zero = {}"
unfolding UNIV1_def pderivs_lang_def by auto

lemma pderivs_lang_One [simp]:
  shows "pderivs_lang UNIV1 One = {}"
unfolding UNIV1_def pderivs_lang_def by (auto split: if_splits)

lemma pderivs_lang_Atom [simp]:
  shows "pderivs_lang UNIV1 (Atom c) = {One}"
unfolding UNIV1_def pderivs_lang_def 
apply(auto)
apply(frule rev_subsetD)
apply(rule pderivs_Atom)
apply(simp)
apply(case_tac xa)
apply(auto split: if_splits)
done

lemma pderivs_lang_Plus [simp]:
  shows "pderivs_lang UNIV1 (Plus r1 r2) = pderivs_lang UNIV1 r1 \<union> pderivs_lang UNIV1 r2"
unfolding UNIV1_def pderivs_lang_def by auto


text {* Non-empty suffixes of a string (needed for the cases of @{const Times} and @{const Star} below) *}

definition
  "PSuf s \<equiv> {v. v \<noteq> [] \<and> (\<exists>u. u @ v = s)}"

lemma PSuf_snoc:
  shows "PSuf (s @ [c]) = (PSuf s) @@ {[c]} \<union> {[c]}"
unfolding PSuf_def conc_def
by (auto simp add: append_eq_append_conv2 append_eq_Cons_conv)

lemma PSuf_Union:
  shows "(\<Union>v \<in> PSuf s @@ {[c]}. f v) = (\<Union>v \<in> PSuf s. f (v @ [c]))"
by (auto simp add: conc_def)

lemma pderivs_lang_snoc:
  shows "pderivs_lang (PSuf s @@ {[c]}) r = (pderiv_set c (pderivs_lang (PSuf s) r))"
unfolding pderivs_lang_def
by (simp add: PSuf_Union pderivs_snoc)

lemma pderivs_Times:
  shows "pderivs s (Times r1 r2) \<subseteq> Timess (pderivs s r1) r2 \<union> (pderivs_lang (PSuf s) r2)"
proof (induct s rule: rev_induct)
  case (snoc c s)
  have ih: "pderivs s (Times r1 r2) \<subseteq> Timess (pderivs s r1) r2 \<union> (pderivs_lang (PSuf s) r2)" 
    by fact
  have "pderivs (s @ [c]) (Times r1 r2) = pderiv_set c (pderivs s (Times r1 r2))" 
    by (simp add: pderivs_snoc)
  also have "\<dots> \<subseteq> pderiv_set c (Timess (pderivs s r1) r2 \<union> (pderivs_lang (PSuf s) r2))"
    using ih by (auto) (blast)
  also have "\<dots> = pderiv_set c (Timess (pderivs s r1) r2) \<union> pderiv_set c (pderivs_lang (PSuf s) r2)"
    by (simp)
  also have "\<dots> = pderiv_set c (Timess (pderivs s r1) r2) \<union> pderivs_lang (PSuf s @@ {[c]}) r2"
    by (simp add: pderivs_lang_snoc)
  also 
  have "\<dots> \<subseteq> pderiv_set c (Timess (pderivs s r1) r2) \<union> pderiv c r2 \<union> pderivs_lang (PSuf s @@ {[c]}) r2"
    by auto
  also 
  have "\<dots> \<subseteq> Timess (pderiv_set c (pderivs s r1)) r2 \<union> pderiv c r2 \<union> pderivs_lang (PSuf s @@ {[c]}) r2"
    by (auto simp add: if_splits) (blast)
  also have "\<dots> = Timess (pderivs (s @ [c]) r1) r2 \<union> pderiv c r2 \<union> pderivs_lang (PSuf s @@ {[c]}) r2"
    by (simp add: pderivs_snoc)
  also have "\<dots> \<subseteq> Timess (pderivs (s @ [c]) r1) r2 \<union> pderivs_lang (PSuf (s @ [c])) r2"
    unfolding pderivs_lang_def by (auto simp add: PSuf_snoc)  
  finally show ?case .
qed (simp) 

lemma pderivs_lang_Times_aux1:
  assumes a: "s \<in> UNIV1"
  shows "pderivs_lang (PSuf s) r \<subseteq> pderivs_lang UNIV1 r"
using a unfolding UNIV1_def PSuf_def pderivs_lang_def by auto

lemma pderivs_lang_Times_aux2:
  assumes a: "s \<in> UNIV1"
  shows "Timess (pderivs s r1) r2 \<subseteq> Timess (pderivs_lang UNIV1 r1) r2"
using a unfolding pderivs_lang_def by auto

lemma pderivs_lang_Times:
  shows "pderivs_lang UNIV1 (Times r1 r2) \<subseteq> Timess (pderivs_lang UNIV1 r1) r2 \<union> pderivs_lang UNIV1 r2"
apply(rule pderivs_lang_subsetI)
apply(rule subset_trans)
apply(rule pderivs_Times)
using pderivs_lang_Times_aux1 pderivs_lang_Times_aux2
apply(blast)
done

lemma pderivs_Star:
  assumes a: "s \<noteq> []"
  shows "pderivs s (Star r) \<subseteq> Timess (pderivs_lang (PSuf s) r) (Star r)"
using a
proof (induct s rule: rev_induct)
  case (snoc c s)
  have ih: "s \<noteq> [] \<Longrightarrow> pderivs s (Star r) \<subseteq> Timess (pderivs_lang (PSuf s) r) (Star r)" by fact
  { assume asm: "s \<noteq> []"
    have "pderivs (s @ [c]) (Star r) = pderiv_set c (pderivs s (Star r))" by (simp add: pderivs_snoc)
    also have "\<dots> \<subseteq> pderiv_set c (Timess (pderivs_lang (PSuf s) r) (Star r))"
      using ih[OF asm] by (auto) (blast)
    also have "\<dots> \<subseteq> Timess (pderiv_set c (pderivs_lang (PSuf s) r)) (Star r) \<union> pderiv c (Star r)"
      by (auto split: if_splits) (blast)+
    also have "\<dots> \<subseteq> Timess (pderivs_lang (PSuf (s @ [c])) r) (Star r) \<union> (Timess (pderiv c r) (Star r))"
      by (simp only: PSuf_snoc pderivs_lang_snoc pderivs_lang_union)
         (auto simp add: pderivs_lang_def)
    also have "\<dots> = Timess (pderivs_lang (PSuf (s @ [c])) r) (Star r)"
      by (auto simp add: PSuf_snoc PSuf_Union pderivs_snoc pderivs_lang_def)
    finally have ?case .
  }
  moreover
  { assume asm: "s = []"
    then have ?case
      apply (auto simp add: pderivs_lang_def pderivs_snoc PSuf_def)
      apply(rule_tac x = "[c]" in exI)
      apply(auto)
      done
  }
  ultimately show ?case by blast
qed (simp)

lemma pderivs_lang_Star:
  shows "pderivs_lang UNIV1 (Star r) \<subseteq> Timess (pderivs_lang UNIV1 r) (Star r)"
apply(rule pderivs_lang_subsetI)
apply(rule subset_trans)
apply(rule pderivs_Star)
apply(simp add: UNIV1_def)
apply(simp add: UNIV1_def PSuf_def)
apply(auto simp add: pderivs_lang_def)
done

lemma finite_Timess [simp]:
  assumes a: "finite A"
  shows "finite (Timess A r)"
using a by auto

lemma finite_pderivs_lang_UNIV1:
  shows "finite (pderivs_lang UNIV1 r)"
apply(induct r)
apply(simp_all add: 
  finite_subset[OF pderivs_lang_Times]
  finite_subset[OF pderivs_lang_Star])
done
    
lemma pderivs_lang_UNIV:
  shows "pderivs_lang UNIV r = pderivs [] r \<union> pderivs_lang UNIV1 r"
unfolding UNIV1_def pderivs_lang_def
by blast

lemma finite_pderivs_lang_UNIV:
  shows "finite (pderivs_lang UNIV r)"
unfolding pderivs_lang_UNIV
by (simp add: finite_pderivs_lang_UNIV1)

lemma finite_pderivs_lang:
  shows "finite (pderivs_lang A r)"
by (metis finite_pderivs_lang_UNIV pderivs_lang_subset rev_finite_subset subset_UNIV)


subsection {* A regular expression matcher based on Brozowski's derivatives *}

fun
  matcher :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "matcher r s = nullable (derivs s r)"

lemma matcher_correctness:
  shows "matcher r s \<longleftrightarrow> s \<in> lang r"
by (induct s arbitrary: r)
   (simp_all add: nullable_iff Deriv_deriv[symmetric] Deriv_def)


end