(*
    Author:   Salomon Sickert
    Author:   Alexander Schimpf (original entry: CAVA/LTL.thy)
    Author:   Stephan Merz (original entry: Stuttering_Equivalence/PLTL.thy)
    License:  BSD
*)

section \<open>Linear Temporal Logic\<close>

theory LTL
imports 
  Main "~~/src/HOL/Library/Omega_Words_Fun"
begin

-- \<open>This theory provides a formalisation of linear temporal logic. It provides three variants:
    \begin{enumerate}
      \item LTL with syntactic sugar. This variant is the semantic reference and the included parser 
            generates ASTs of this datatype.
      \item LTL in negation normal form without syntactic sugar. This variant is used by the included
            rewriting engine and is used for the translation to automata (implemented in other entries).
      \item PLTL. A variant with a reduced set of operators.
    \end{enumerate}
    This theory subsumes (and partly reuses) the existing formalisation found in LTL\_to\_GBA and 
    Stuttering\_Equivalence and unifies them.\<close>

subsection \<open>LTL with Syntactic Sugar\<close>

-- \<open>In this section, we provide a formulation of LTL with explicit syntactic sugar deeply embedded. 
    This formalization serves as a reference semantics.\<close>

subsubsection \<open>Syntax\<close>

datatype (ltlc_props: 'a) ltlc = 
    LTLcTrue                        ("true\<^sub>c")
  | LTLcFalse                       ("false\<^sub>c")
  | LTLcProp 'a                     ("prop\<^sub>c'(_')")
  | LTLcNeg "'a ltlc"               ("not\<^sub>c _" [85] 85)
  | LTLcAnd "'a ltlc" "'a ltlc"     ("_ and\<^sub>c _" [82,82] 81)
  | LTLcOr "'a ltlc" "'a ltlc"      ("_ or\<^sub>c _" [81,81] 80)
  | LTLcImplies "'a ltlc" "'a ltlc" ("_ implies\<^sub>c _" [81,81] 80)
  | LTLcNext "'a ltlc"              ("X\<^sub>c _" [88] 87) 
  | LTLcFinal "'a ltlc"             ("F\<^sub>c _" [88] 87)
  | LTLcGlobal "'a ltlc"            ("G\<^sub>c _" [88] 87)
  | LTLcUntil "'a ltlc" "'a ltlc"   ("_ U\<^sub>c _" [84,84] 83)
  | LTLcRelease "'a ltlc" "'a ltlc" ("_ V\<^sub>c _" [83,83] 82)

definition LTLcIff ("_ iff\<^sub>c _" [81,81] 80)
where
  "\<phi> iff\<^sub>c \<psi> \<equiv> (\<phi> implies\<^sub>c \<psi>) and\<^sub>c (\<psi> implies\<^sub>c \<phi>)"  

subsubsection \<open>Semantics\<close>

primrec ltlc_semantics :: "['a set word, 'a ltlc] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>c _" [80,80] 80)
where
  "\<xi> \<Turnstile>\<^sub>c true\<^sub>c = True"
| "\<xi> \<Turnstile>\<^sub>c false\<^sub>c = False"
| "\<xi> \<Turnstile>\<^sub>c prop\<^sub>c(q) = (q\<in>\<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>c not\<^sub>c \<phi> = (\<not> \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> and\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<and> \<xi> \<Turnstile>\<^sub>c \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> or\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<or> \<xi> \<Turnstile>\<^sub>c \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> implies\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<longrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c X\<^sub>c \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<phi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<phi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> U\<^sub>c \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<phi>))"
| "\<xi> \<Turnstile>\<^sub>c \<phi> V\<^sub>c \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<phi>))"

lemma ltlc_semantics_sugar [simp]:
  "\<xi> \<Turnstile>\<^sub>c \<phi> iff\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi>)"
  "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c (true\<^sub>c U\<^sub>c \<phi>)"
  "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c (false\<^sub>c V\<^sub>c \<phi>)"
  by (auto simp add: LTLcIff_def)

definition "ltlc_language \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>c \<phi>}"

lemma ltlc_language_negate[simp]:
  "ltlc_language (not\<^sub>c \<phi>) = - ltlc_language \<phi>"
  unfolding ltlc_language_def by auto

lemma ltl_true_or_con[simp]:
  "\<xi> \<Turnstile>\<^sub>c prop\<^sub>c(p) or\<^sub>c (not\<^sub>c prop\<^sub>c(p)) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c true\<^sub>c"
  by auto

lemma ltl_false_true_con[simp]:
  "\<xi> \<Turnstile>\<^sub>c not\<^sub>c true\<^sub>c \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c false\<^sub>c"
  by auto

lemma ltl_Next_Neg_con[simp]:
  "\<xi> \<Turnstile>\<^sub>c X\<^sub>c (not\<^sub>c \<phi>) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c not\<^sub>c X\<^sub>c \<phi>"
  by auto

--\<open>The connection between Until and Release\<close>

lemma ltl_Release_Until_con:
 "\<xi> \<Turnstile>\<^sub>c \<phi> V\<^sub>c \<psi> \<longleftrightarrow> (\<not> \<xi> \<Turnstile>\<^sub>c (not\<^sub>c \<phi>) U\<^sub>c (not\<^sub>c \<psi>))"
  by auto

definition "pw_eq_on S w w' \<equiv> \<forall>i. w i \<inter> S = w' i \<inter> S"

lemma pw_eq_on_refl[simp]: "pw_eq_on S w w"
  and pw_eq_on_sym: "pw_eq_on S w w' \<Longrightarrow> pw_eq_on S w' w"
  and pw_eq_on_trans[trans]: "\<lbrakk>pw_eq_on S w w'; pw_eq_on S w' w''\<rbrakk> \<Longrightarrow> pw_eq_on S w w''"
  unfolding pw_eq_on_def by auto

lemma pw_eq_on_suffix:
  "pw_eq_on S w w' \<Longrightarrow> pw_eq_on S (suffix k w) (suffix k w')"
  by (simp add: pw_eq_on_def)

lemma pw_eq_on_subset:
  "S \<subseteq> S' \<Longrightarrow> pw_eq_on S' w w' \<Longrightarrow> pw_eq_on S w w'"
  by (auto simp add: pw_eq_on_def)

lemma ltlc_eq_on_aux: 
  "pw_eq_on (ltlc_props \<phi>) w w' \<Longrightarrow> w \<Turnstile>\<^sub>c \<phi> \<Longrightarrow> w' \<Turnstile>\<^sub>c \<phi>"
proof (induction \<phi> arbitrary: w w')
  case LTLcUntil
    thus ?case
      by (simp; blast intro!: pw_eq_on_suffix[OF pw_eq_on_subset, of "ltlc_props _" "ltlc_props _ \<union> ltlc_props _"])
next
  case (LTLcRelease \<phi> \<psi>)
    thus ?case
      by (simp; blast intro!: pw_eq_on_suffix[OF pw_eq_on_subset, of "ltlc_props _" "ltlc_props _ \<union> ltlc_props _"])
next
  case (LTLcAnd \<phi> \<psi>)
    thus ?case
      by (simp; blast intro!: pw_eq_on_subset[of "ltlc_props _" "ltlc_props _ \<union> ltlc_props _"]) 
next
  case (LTLcOr \<phi> \<psi>) 
    thus ?case
      by (simp; blast intro!: pw_eq_on_subset[of "ltlc_props _" "ltlc_props _ \<union> ltlc_props _"])  
next
  case (LTLcImplies \<phi> \<psi>)
    thus ?case
      by (simp; meson Un_upper1 Un_upper2 pw_eq_on_subset[of "ltlc_props _" "ltlc_props \<phi> \<union> ltlc_props \<psi>"]  pw_eq_on_sym)
qed (auto simp add: pw_eq_on_def; metis suffix_nth)+

lemma ltlc_eq_on: 
  "pw_eq_on (ltlc_props \<phi>) w w' \<Longrightarrow> w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> w' \<Turnstile>\<^sub>c \<phi>"
  using ltlc_eq_on_aux pw_eq_on_sym by blast

lemma suffix_comp: "(\<lambda>i. f (suffix k w i)) = suffix k (f o w)"
  by auto

lemma suffix_range: "\<Union>(range \<xi>) \<subseteq> APs \<Longrightarrow> \<Union>(range (suffix k \<xi>)) \<subseteq> APs"
    by auto

lemma map_ltlc_semantics_aux:
  assumes "inj_on f APs"
  assumes "\<Union>(range w) \<subseteq> APs"
  assumes "ltlc_props \<phi> \<subseteq> APs"
  shows "w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> (\<lambda>i. f ` w i) \<Turnstile>\<^sub>c map_ltlc f \<phi>"
  using assms(2,3)
proof (induction \<phi> arbitrary: w)
  case (LTLcProp x)
    thus ?case   using assms(1) 
by (simp add: SUP_le_iff inj_on_image_mem_iff)
next
  case (LTLcNext \<phi>)
    show ?case
      using LTLcNext(1)[of "suffix 1 w", unfolded suffix_comp comp_def] LTLcNext(2,3) apply simp 
        by (metis LTLcNext.prems(1) One_nat_def \<open>\<lbrakk>\<Union>range (suffix 1 w) \<subseteq> APs; ltlc_props \<phi> \<subseteq> APs\<rbrakk> \<Longrightarrow> suffix 1 w \<Turnstile>\<^sub>c \<phi> = suffix 1 (\<lambda>x. f ` w x) \<Turnstile>\<^sub>c map_ltlc f \<phi>\<close> suffix_range)
next 
  case (LTLcFinal \<phi>)
    thus ?case 
       using LTLcFinal(1)[of "suffix _ _", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next 
  case (LTLcGlobal)
    thus ?case
      using LTLcGlobal(1)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next 
  case (LTLcUntil)
    thus ?case
      using LTLcUntil(1,2)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next 
  case (LTLcRelease)
    thus ?case
      using LTLcRelease(1,2)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
qed simp+

definition "map_props f APs \<equiv> {i. \<exists>p\<in>APs. f p = Some i}"

lemma map_ltlc_semantics:
  assumes INJ: "inj_on f (dom f)" and DOM: "ltlc_props \<phi> \<subseteq> dom f"
  shows "\<xi> \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> (map_props f o \<xi>) \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi>"
proof -
  let ?\<xi>r = "\<lambda>i. \<xi> i \<inter> ltlc_props \<phi>"
  let ?\<xi>r' = "\<lambda>i. \<xi> i \<inter> dom f"

  have 1: "\<Union>range ?\<xi>r \<subseteq> ltlc_props \<phi>" by auto

  have INJ_the_dom: "inj_on (the o f) (dom f)" 
    using assms
    by (auto simp: inj_on_def domIff) 
  note 2 = subset_inj_on[OF this DOM]

  have 3: "(\<lambda>i. (the o f) ` ?\<xi>r' i) = map_props f o \<xi>" using DOM INJ
    apply (auto intro!: ext simp: map_props_def domIff image_iff)
    by (metis Int_iff domI option.sel)

  have "\<xi> \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> ?\<xi>r \<Turnstile>\<^sub>c \<phi>"
    apply (rule ltlc_eq_on)
    apply (auto simp: pw_eq_on_def)
    done
  also from map_ltlc_semantics_aux[OF 2 1 subset_refl]
  have "\<dots> \<longleftrightarrow> (\<lambda>i. (the o f) ` ?\<xi>r i) \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi>" .
  also have "\<dots> \<longleftrightarrow> (\<lambda>i. (the o f) ` ?\<xi>r' i) \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi>"
    apply (rule ltlc_eq_on) using DOM INJ
    apply (auto simp: pw_eq_on_def ltlc.set_map domIff image_iff)
    by (metis Int_iff contra_subsetD domD domI inj_on_eq_iff option.sel)
  also note 3
  finally show ?thesis .
qed

lemma map_ltlc_semantics_inv:
  assumes INJ: "inj_on f (dom f)" and DOM: "ltlc_props \<phi> \<subseteq> dom f"
  shows "\<xi> \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi> \<longleftrightarrow> (\<lambda>i. (the o f) -` \<xi> i) \<Turnstile>\<^sub>c \<phi>"
  using map_ltlc_semantics[OF assms]
  apply simp
  apply (intro ltlc_eq_on)
  apply (auto simp add: pw_eq_on_def ltlc.set_map map_props_def)
  by (metis DOM comp_apply contra_subsetD domD option.sel vimage_eq)

subsection \<open>LTL in Negation Normal Form\<close>

text\<open>
  We define a type of LTL formula in negation normal form (NNF).
\<close>

subsubsection \<open>Syntax\<close>

datatype (ltln_props: 'a) ltln  = 
    LTLnTrue                        ("true\<^sub>n")
  | LTLnFalse                       ("false\<^sub>n")
  | LTLnProp 'a                     ("prop\<^sub>n'(_')")
  | LTLnNProp 'a                    ("nprop\<^sub>n'(_')")
  | LTLnAnd "'a ltln" "'a ltln"     ("_ and\<^sub>n _" [82,82] 81)
  | LTLnOr "'a ltln" "'a ltln"      ("_ or\<^sub>n _" [84,84] 83)
  | LTLnNext "'a ltln"              ("X\<^sub>n _" [88] 87)
  | LTLnUntil "'a ltln" "'a ltln"   ("_ U\<^sub>n _" [84,84] 83)
  | LTLnRelease "'a ltln" "'a ltln" ("_ V\<^sub>n _" [84,84] 83)

abbreviation F\<^sub>n :: "'a ltln \<Rightarrow> 'a ltln" ("\<diamondsuit>\<^sub>n _" [88] 87)
where 
  "F\<^sub>n \<phi> \<equiv> true\<^sub>n U\<^sub>n \<phi>" 

abbreviation G\<^sub>n :: "'a ltln \<Rightarrow> 'a ltln" ("\<box>\<^sub>n _" [88] 87)
where 
  "G\<^sub>n \<phi> \<equiv> false\<^sub>n V\<^sub>n \<phi>" 

subsubsection \<open>Semantics\<close>

primrec ltln_semantics :: "['a set word, 'a ltln] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>n _" [80,80] 80)
where
  "\<xi> \<Turnstile>\<^sub>n true\<^sub>n = True"
| "\<xi> \<Turnstile>\<^sub>n false\<^sub>n = False"
| "\<xi> \<Turnstile>\<^sub>n prop\<^sub>n(q) = (q \<in> \<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>n nprop\<^sub>n(q) = (q \<notin> \<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>n \<phi> and\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<phi> \<and> \<xi> \<Turnstile>\<^sub>n \<psi>)"
| "\<xi> \<Turnstile>\<^sub>n \<phi> or\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<phi> \<or> \<xi> \<Turnstile>\<^sub>n \<psi>)"
| "\<xi> \<Turnstile>\<^sub>n X\<^sub>n \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>n \<phi>)"
| "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>))"
| "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>))"

definition "ltln_language \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>n \<phi>}"

subsubsection \<open>Conversion\<close>

fun ltlc_to_ltln' :: "bool \<Rightarrow> 'a ltlc \<Rightarrow> 'a ltln"
where
  "ltlc_to_ltln' False true\<^sub>c = true\<^sub>n"
| "ltlc_to_ltln' False false\<^sub>c = false\<^sub>n"
| "ltlc_to_ltln' False prop\<^sub>c(q) = prop\<^sub>n(q)"
| "ltlc_to_ltln' False (\<phi> and\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) and\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> or\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) or\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> implies\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) or\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (F\<^sub>c \<phi>) = true\<^sub>n U\<^sub>n (ltlc_to_ltln' False \<phi>)"
| "ltlc_to_ltln' False (G\<^sub>c \<phi>) = false\<^sub>n V\<^sub>n (ltlc_to_ltln' False \<phi>)"
| "ltlc_to_ltln' False (\<phi> U\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) U\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> V\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) V\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' True true\<^sub>c = false\<^sub>n"
| "ltlc_to_ltln' True false\<^sub>c = true\<^sub>n"
| "ltlc_to_ltln' True prop\<^sub>c(q) = nprop\<^sub>n(q)"
| "ltlc_to_ltln' True (\<nu> and\<^sub>c \<mu>) = ltlc_to_ltln' True \<nu> or\<^sub>n ltlc_to_ltln' True \<mu>"
| "ltlc_to_ltln' True (\<nu> or\<^sub>c \<mu>) = ltlc_to_ltln' True \<nu> and\<^sub>n ltlc_to_ltln' True \<mu>"
| "ltlc_to_ltln' True (\<phi> implies\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) and\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' True (F\<^sub>c \<phi>) = false\<^sub>n V\<^sub>n (ltlc_to_ltln' True \<phi>)"
| "ltlc_to_ltln' True (G\<^sub>c \<phi>) = true\<^sub>n U\<^sub>n (ltlc_to_ltln' True \<phi>)"
| "ltlc_to_ltln' True (\<nu> U\<^sub>c \<mu>) = ltlc_to_ltln' True \<nu> V\<^sub>n ltlc_to_ltln' True \<mu>"
| "ltlc_to_ltln' True (\<nu> V\<^sub>c \<mu>) = ltlc_to_ltln' True \<nu> U\<^sub>n ltlc_to_ltln' True \<mu>"
| "ltlc_to_ltln' b (not\<^sub>c \<psi>) = ltlc_to_ltln' (Not b) \<psi>"
| "ltlc_to_ltln' b (X\<^sub>c \<phi>) = X\<^sub>n (ltlc_to_ltln' b \<phi>)"

fun ltlc_to_ltln :: "'a ltlc \<Rightarrow> 'a ltln"
where
  "ltlc_to_ltln \<phi> = ltlc_to_ltln' False \<phi>"

fun ltln_to_ltlc :: "'a ltln \<Rightarrow> 'a ltlc"
where
  "ltln_to_ltlc true\<^sub>n = true\<^sub>c"
| "ltln_to_ltlc false\<^sub>n = false\<^sub>c"
| "ltln_to_ltlc prop\<^sub>n(q) = prop\<^sub>c(q)"
| "ltln_to_ltlc nprop\<^sub>n(q) = not\<^sub>c (prop\<^sub>c(q))"
| "ltln_to_ltlc (\<phi> and\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> and\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (\<phi> or\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> or\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (X\<^sub>n \<phi>) = (X\<^sub>c ltln_to_ltlc \<phi>)"
| "ltln_to_ltlc (\<phi> U\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> U\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (\<phi> V\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> V\<^sub>c ltln_to_ltlc \<psi>)"

lemma ltlc_to_ltln'_correct:
  "w \<Turnstile>\<^sub>n (ltlc_to_ltln' True \<phi>) \<longleftrightarrow> \<not> w \<Turnstile>\<^sub>c \<phi>"
  "w \<Turnstile>\<^sub>n (ltlc_to_ltln' False \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>c \<phi>" 
  "size (ltlc_to_ltln' True \<phi>) \<le> 2 * size \<phi>"
  "size (ltlc_to_ltln' False \<phi>) \<le> 2 * size \<phi>"
  by (induction \<phi> arbitrary: w) simp+

lemma ltlc_to_ltln_semantics [simp]:
  "w \<Turnstile>\<^sub>n ltlc_to_ltln \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>c \<phi>"
  using ltlc_to_ltln'_correct by auto

lemma ltlc_to_ltln_size:
  "size (ltlc_to_ltln \<phi>) \<le> 2 * size \<phi>"
  using ltlc_to_ltln'_correct by simp

lemma ltln_to_ltlc_semantics [simp]:
  "w \<Turnstile>\<^sub>c ltln_to_ltlc \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (induction \<phi> arbitrary: w) simp+

subsubsection \<open>Auxiliary Functions\<close>

fun not\<^sub>n 
where 
  "not\<^sub>n true\<^sub>n = false\<^sub>n"
| "not\<^sub>n false\<^sub>n = true\<^sub>n"
| "not\<^sub>n prop\<^sub>n(a) = nprop\<^sub>n(a)"
| "not\<^sub>n nprop\<^sub>n(a) = prop\<^sub>n(a)"
| "not\<^sub>n (\<phi> and\<^sub>n \<psi>) = (not\<^sub>n \<phi>) or\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (\<phi> or\<^sub>n \<psi>) = (not\<^sub>n \<phi>) and\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (\<phi> U\<^sub>n \<psi>) = (not\<^sub>n \<phi>) V\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (\<phi> V\<^sub>n \<psi>) = (not\<^sub>n \<phi>) U\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (X\<^sub>n \<phi>) = X\<^sub>n (not\<^sub>n \<phi>)"

lemma not\<^sub>n_semantics [simp]: 
  "w \<Turnstile>\<^sub>n not\<^sub>n \<phi> \<longleftrightarrow> \<not> w \<Turnstile>\<^sub>n \<phi>"
  by (induction \<phi> arbitrary: w) auto

subsubsection \<open>Subformulae\<close>

fun subfrmlsn :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "subfrmlsn (\<mu> and\<^sub>n \<psi>) = {\<mu> and\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn (X\<^sub>n \<mu>) = {X\<^sub>n \<mu>} \<union> subfrmlsn \<mu>"
| "subfrmlsn (\<mu> U\<^sub>n \<psi>) = {\<mu> U\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<mu> V\<^sub>n \<psi>) = {\<mu> V\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<mu> or\<^sub>n \<psi>) = {\<mu> or\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn x = {x}"

lemma subfrmlsn_id[simp]: 
  "\<phi> \<in> subfrmlsn \<phi>" 
  by (induct \<phi>) auto

lemma subfrmlsn_finite: 
  "finite (subfrmlsn \<phi>)" 
  by (induct \<phi>) auto

lemma subfrmlsn_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> subfrmlsn \<psi> \<subseteq> subfrmlsn \<phi>"
  by (induct \<phi> arbitrary:\<psi>) auto

fun size_frmln :: "'a ltln \<Rightarrow> nat"
where
  "size_frmln (\<phi> and\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln (X\<^sub>n \<phi>) = size_frmln \<phi> + 1"
| "size_frmln (\<phi> U\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln (\<phi> V\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln (\<phi> or\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln _ = 1"

lemma size_frmln_gt_zero[simp]: 
  "size_frmln \<phi> > 0" 
  by (induct \<phi>) auto

abbreviation
  "frmlset_sumn \<Phi> \<equiv> setsum size_frmln \<Phi>"

lemma frmlset_sumn_diff_less[intro!]:
  assumes finS:"finite S"
      and "A\<noteq>{}"
      and subset:"A\<subseteq>S"
    shows "frmlset_sumn (S - A) < frmlset_sumn S"
proof -
  have finA: "finite A" using assms by (rule_tac finite_subset)
  then have "frmlset_sumn A > 0" using assms size_frmln_gt_zero by (induct rule:finite_induct) auto
  moreover
  have "frmlset_sumn A \<le> frmlset_sumn S" using assms size_frmln_gt_zero by (rule_tac setsum_mono2) auto
  ultimately show ?thesis using setsum_diff_nat[OF finA, of S size_frmln] assms by auto
qed

definition
  "frmln_props \<phi> \<equiv> {p. prop\<^sub>n(p) \<in> subfrmlsn \<phi> \<or> nprop\<^sub>n(p) \<in> subfrmlsn \<phi>}"

inductive subfrml :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool"
where
  "subfrml \<phi> (\<phi> and\<^sub>n \<psi>)"
| "subfrml \<psi> (\<phi> and\<^sub>n \<psi>)"
| "subfrml \<phi> (\<phi> or\<^sub>n \<psi>)"
| "subfrml \<psi> (\<phi> or\<^sub>n \<psi>)"
| "subfrml \<phi> (X\<^sub>n \<phi>)"
| "subfrml \<phi> (\<phi> U\<^sub>n \<psi>)"
| "subfrml \<psi> (\<phi> U\<^sub>n \<psi>)"
| "subfrml \<phi> (\<phi> V\<^sub>n \<psi>)"
| "subfrml \<psi> (\<phi> V\<^sub>n \<psi>)"

abbreviation is_subfrml ("_ is'_subformula'_of _")
where
  "is_subfrml \<psi> \<phi> \<equiv> subfrml\<^sup>*\<^sup>* \<psi> \<phi>"

lemma subfrml_size:
  assumes "subfrml \<psi> \<phi>"
    shows "size \<psi> < size \<phi>"
using assms by (induct \<phi>) auto

lemma subformula_size:
  assumes "\<psi> is_subformula_of \<phi>"
    shows "size \<psi> < size \<phi> \<or> \<psi> = \<phi>"
using assms proof(induct \<phi>)
  case base then show ?case by auto
next
  case (step \<nu> \<mu>)
    then have "size \<nu> < size \<mu>" by (rule_tac subfrml_size)
    then show ?case using step by auto
qed

subsubsection \<open>Expansion\<close>

lemma ltln_expand_Until:
  "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<psi> or\<^sub>n (\<phi> and\<^sub>n (X\<^sub>n (\<phi> U\<^sub>n \<psi>))))" 
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain i where psi_is: "suffix i \<xi> \<Turnstile>\<^sub>n \<psi>"
    and phi_is: "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
    by auto
  show ?rhs
  proof(cases i)
    assume "i=0"
    then show ?rhs using psi_is by auto
  next
    fix k
    assume i_eq: "i = Suc k"
    with phi_is have "\<xi> \<Turnstile>\<^sub>n \<phi>" by auto
    moreover
    have "\<xi> \<Turnstile>\<^sub>n X\<^sub>n (\<phi> U\<^sub>n \<psi>)" 
    using psi_is phi_is i_eq by auto
    ultimately show ?rhs by auto
  qed
next
  assume rhs: ?rhs
  show ?lhs
  proof(cases "\<xi> \<Turnstile>\<^sub>n \<psi>")
    assume "\<xi> \<Turnstile>\<^sub>n \<psi>"
    then have "suffix 0 \<xi> \<Turnstile>\<^sub>n \<psi>" by auto
    moreover
    have "\<forall>j<0. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>" by auto
    ultimately
    have "\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi>
              \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>)" by blast
    then show ?lhs by auto
  next
    assume "\<not> \<xi> \<Turnstile>\<^sub>n \<psi>"
    then have phi_is: "\<xi> \<Turnstile>\<^sub>n \<phi>"
      and "\<xi> \<Turnstile>\<^sub>n X\<^sub>n (\<phi> U\<^sub>n \<psi>)" using rhs by auto
    then obtain i
          where psi_suc_is: "suffix (Suc i) \<xi> \<Turnstile>\<^sub>n \<psi>"
            and phi_suc_is: "\<forall>j<i. suffix (Suc j) \<xi> \<Turnstile>\<^sub>n \<phi>" by auto
    have sbgoal: "\<forall>j<(Suc i). suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
    proof(clarify)
      fix j
      assume j_less: "j<Suc i"
      show "suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
      proof (cases j)
        assume "j=0"
        then show ?thesis using phi_is by auto
      next
        fix k
        assume "j=Suc k"
        then show ?thesis using j_less phi_suc_is by auto
      qed
    qed
    then show ?lhs using psi_suc_is phi_is by auto
  qed
qed

lemma ltln_expand_Release:
  "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<psi> and\<^sub>n (\<phi> or\<^sub>n (X\<^sub>n (\<phi> V\<^sub>n \<psi>))))" 
  (is "?lhs = ?rhs")
proof
  assume lhs: ?lhs
  then have psi_is: "\<xi> \<Turnstile>\<^sub>n \<psi>" by force

  have "\<And>i. \<lbrakk>\<not> \<xi> \<Turnstile>\<^sub>n \<phi>; \<not> suffix (Suc i) \<xi> \<Turnstile>\<^sub>n \<psi>\<rbrakk>
            \<Longrightarrow> (\<exists>j<i. suffix (Suc j) \<xi> \<Turnstile>\<^sub>n \<phi>)"
  proof -
    fix i
    assume phi_nis: "\<not> \<xi> \<Turnstile>\<^sub>n \<phi>"
       and "\<not> suffix (Suc i) \<xi> \<Turnstile>\<^sub>n \<psi>"
    then obtain j
          where "j<Suc i"
            and "suffix j \<xi> \<Turnstile>\<^sub>n \<phi>" using lhs by auto
    then have "j - 1 < i \<and> suffix (Suc (j - 1)) \<xi> \<Turnstile>\<^sub>n \<phi>"
    using phi_nis by (cases j) auto
    then show "\<exists>j<i. suffix (Suc j) \<xi> \<Turnstile>\<^sub>n \<phi>" by auto
  qed
  then show ?rhs using psi_is by auto
next
  assume rhs: ?rhs
  then have psi_is: "\<xi> \<Turnstile>\<^sub>n \<psi>" by auto

  show ?lhs
  proof(cases "\<xi> \<Turnstile>\<^sub>n \<phi>")
    assume "\<xi> \<Turnstile>\<^sub>n \<phi>"
    then show ?thesis using psi_is by force
  next
    assume phi_nis: "\<not> \<xi> \<Turnstile>\<^sub>n \<phi>"

    then have "\<forall>i. suffix (Suc i) \<xi> \<Turnstile>\<^sub>n \<psi>
               \<or> (\<exists>j<Suc i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>)"
    using rhs by auto

    have "\<And>i. \<not> suffix i \<xi> \<Turnstile>\<^sub>n \<psi>
              \<Longrightarrow> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>)"
    proof -
      fix i
      assume psi_suf_nis: "\<not> suffix i \<xi> \<Turnstile>\<^sub>n \<psi>"
      show "\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
      proof(cases "i")
        assume "i=0"
        with psi_suf_nis psi_is show ?thesis by auto
      next
        fix k
        assume i_eq: "i=Suc k"
        with psi_suf_nis rhs show ?thesis by force
      qed
    qed
    then show ?thesis by auto
  qed
qed

lemma ltln_Release_alterdef:
  "w \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (G\<^sub>n \<psi>) or\<^sub>n (\<psi> U\<^sub>n (\<phi> and\<^sub>n \<psi>))"
proof (cases "\<exists>i. \<not>suffix i w \<Turnstile>\<^sub>n \<psi>")
  case True
    def i \<equiv> "Least (\<lambda>i. \<not>suffix i w \<Turnstile>\<^sub>n \<psi>)"
    have "\<And>j. j < i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<psi>" and "\<not> suffix i w \<Turnstile>\<^sub>n \<psi>"
      using True LeastI not_less_Least unfolding i_def by fast+
    hence "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>n \<phi>) \<Longrightarrow> (\<exists>i. (suffix i w \<Turnstile>\<^sub>n \<psi> \<and> suffix i w \<Turnstile>\<^sub>n \<phi>) \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>n \<psi>))"
      by fastforce  
    moreover
    hence "\<exists>i. (suffix i w \<Turnstile>\<^sub>n \<psi> \<and> suffix i w \<Turnstile>\<^sub>n \<phi>) \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>n \<psi>) \<Longrightarrow> (\<forall>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>n \<phi>))"
      using linorder_cases by blast
    ultimately
    show ?thesis
      using True by auto
qed auto

lemma nested_until_semantics[simp]:
  "w \<Turnstile>\<^sub>n (true\<^sub>n U\<^sub>n (\<phi> U\<^sub>n \<psi>)) \<longleftrightarrow> w \<Turnstile>\<^sub>n (true\<^sub>n U\<^sub>n \<psi>)"
  by auto force

lemma nested_release_semantics[simp]:
  "w \<Turnstile>\<^sub>n (false\<^sub>n V\<^sub>n (\<phi> V\<^sub>n \<psi>)) \<longleftrightarrow> w \<Turnstile>\<^sub>n (false\<^sub>n V\<^sub>n \<psi>)"
  by auto force

subsection \<open>Propositional LTL\<close>

-- \<open>We define the syntax and semantics of propositional linear-time
    temporal logic PLTL.
    PLTL formulas are built from atomic formulas, propositional connectives,
    and the temporal operators ``next'' and ``until''. The following data
    type definition is parameterized by the type of states over which
    formulas are evaluated.\<close>

subsubsection \<open>Syntax\<close>

datatype 'a pltl  = 
    LTLpFalse                       ("false\<^sub>p")
  | LTLpAtom "'a \<Rightarrow> bool"           ("atom\<^sub>p _") 
  | LTLpImplies "'a pltl" "'a pltl" ("_ implies\<^sub>p _" [81,81] 80)
  | LTLpNext "'a pltl"              ("X\<^sub>p _" [88] 87)
  | LTLpUntil "'a pltl" "'a pltl"   ("_ U\<^sub>p _" [84,84] 83)

-- \<open>Further connectives of PLTL can be defined in terms of the existing syntax.\<close>

definition LTLpNot ("not\<^sub>p _" [85] 85) 
where 
  "not\<^sub>p \<phi> \<equiv> \<phi> implies\<^sub>p false\<^sub>p"

definition LTLpTrue ("true\<^sub>p") 
where 
  "true\<^sub>p \<equiv> not\<^sub>p false\<^sub>p"

definition LTLpOr ("_ or\<^sub>p _" [81,81] 80) 
where 
  "\<phi> or\<^sub>p \<psi> \<equiv> (not\<^sub>p \<phi>) implies\<^sub>p \<psi>"

definition LTLpAnd ("_ and\<^sub>p _" [82,82] 81)
where 
  "\<phi> and\<^sub>p \<psi> \<equiv> not\<^sub>p ((not\<^sub>p \<phi>) or\<^sub>p (not\<^sub>p \<psi>))"

definition LTLpEventually ("F\<^sub>p _" [88] 87)
where 
  "F\<^sub>p \<phi> \<equiv> true\<^sub>p U\<^sub>p \<phi>"

definition LTLpAlways ("G\<^sub>p _" [88] 87)
where 
  "G\<^sub>p \<phi> \<equiv> not\<^sub>p (F\<^sub>p (not\<^sub>p \<phi>))"

subsubsection \<open>Semantics\<close>

fun pltl_semantics :: "['a word, 'a pltl] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>p _" [80,80] 80)
where
  "w \<Turnstile>\<^sub>p false\<^sub>p = False"
| "w \<Turnstile>\<^sub>p (atom\<^sub>p p) = (p (w 0))"
| "w \<Turnstile>\<^sub>p \<phi> implies\<^sub>p \<psi> = (w \<Turnstile>\<^sub>p \<phi> \<longrightarrow> w \<Turnstile>\<^sub>p \<psi>)"
| "w \<Turnstile>\<^sub>p X\<^sub>p \<phi> = (suffix 1 w \<Turnstile>\<^sub>p \<phi>)"
| "w \<Turnstile>\<^sub>p \<phi> U\<^sub>p \<psi> = (\<exists>i. suffix i w \<Turnstile>\<^sub>p \<psi> \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>p \<phi>))"

lemma pltl_semantics_sugar [simp]: 
  "w \<Turnstile>\<^sub>p not\<^sub>p \<phi> = (\<not>w \<Turnstile>\<^sub>p \<phi>)"
  "w \<Turnstile>\<^sub>p true\<^sub>p = True"
  "w \<Turnstile>\<^sub>p \<phi> or\<^sub>p \<psi> = (w \<Turnstile>\<^sub>p \<phi> \<or> w \<Turnstile>\<^sub>p \<psi>)"
  "w \<Turnstile>\<^sub>p \<phi> and\<^sub>p \<psi> = (w \<Turnstile>\<^sub>p \<phi> \<and> w \<Turnstile>\<^sub>p \<psi>)"
  "w \<Turnstile>\<^sub>p F\<^sub>p \<phi> = (\<exists>i. suffix i w \<Turnstile>\<^sub>p \<phi>)"
  "w \<Turnstile>\<^sub>p G\<^sub>p \<phi> = (\<forall>i. suffix i w \<Turnstile>\<^sub>p \<phi>)"
  by (auto simp: LTLpNot_def LTLpTrue_def LTLpOr_def LTLpAnd_def LTLpEventually_def LTLpAlways_def)

subsection \<open>Conversion\<close>

fun ltlc_to_pltl :: "'a ltlc \<Rightarrow> 'a set pltl"
where
  "ltlc_to_pltl true\<^sub>c = true\<^sub>p"
| "ltlc_to_pltl false\<^sub>c = false\<^sub>p"
| "ltlc_to_pltl (prop\<^sub>c(q)) = atom\<^sub>p (op \<in> q)"
| "ltlc_to_pltl (not\<^sub>c \<phi>) = not\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (\<phi> and\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) and\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> or\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) or\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> implies\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) implies\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (X\<^sub>c \<phi>) = X\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (F\<^sub>c \<phi>) = F\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (G\<^sub>c \<phi>) = G\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (\<phi> U\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) U\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> V\<^sub>c \<psi>) = not\<^sub>p ((not\<^sub>p (ltlc_to_pltl \<phi>)) U\<^sub>p (not\<^sub>p (ltlc_to_pltl \<psi>)))"
  
lemma ltlc_to_pltl_semantics [simp]: 
  "w \<Turnstile>\<^sub>p (ltlc_to_pltl \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>c \<phi>"
  by (induction \<phi> arbitrary: w) simp_all

subsubsection \<open>Atoms\<close>

fun pltl_atoms :: "'a pltl \<Rightarrow> ('a \<Rightarrow> bool) set"
where
  "pltl_atoms false\<^sub>p = {}"
| "pltl_atoms (atom\<^sub>p p) = {p}"
| "pltl_atoms (\<phi> implies\<^sub>p \<psi>) = pltl_atoms \<phi> \<union> pltl_atoms \<psi>"
| "pltl_atoms (X\<^sub>p \<phi>) = pltl_atoms \<phi>"
| "pltl_atoms (\<phi> U\<^sub>p \<psi>) = pltl_atoms \<phi> \<union> pltl_atoms \<psi>"

lemma atoms_finite [iff]: 
  "finite (pltl_atoms \<phi>)"
  by (induct \<phi>) auto

lemma pltl_atoms_sugar [simp]: 
  "pltl_atoms (not\<^sub>p \<phi>) = pltl_atoms \<phi>"
  "pltl_atoms true\<^sub>p = {}"
  "pltl_atoms (\<phi> or\<^sub>p \<psi>) = pltl_atoms \<phi> \<union> pltl_atoms \<psi>"
  "pltl_atoms (\<phi> and\<^sub>p \<psi>) = pltl_atoms \<phi> \<union> pltl_atoms \<psi>"
  "pltl_atoms (F\<^sub>p \<phi>) = pltl_atoms \<phi>"
  "pltl_atoms (G\<^sub>p \<phi>) = pltl_atoms \<phi>"
  by (auto simp: LTLpNot_def LTLpTrue_def LTLpOr_def LTLpAnd_def LTLpEventually_def LTLpAlways_def)

end
