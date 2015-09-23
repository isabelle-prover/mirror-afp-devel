(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>CAVA LTL Compatibility Layer\<close>

theory LTL_CAVA_Compat
  imports Main "../LTL"
begin

subsection \<open>Original CAVA LTL Definitions\<close>

-- \<open>The following definitions are adapted from the CAVA formalisation. The aim is to reuse the parsing infrastructure of CAVA\<close>

datatype (ltlc_aprops: 'a)
  ltlc = LTLcTrue 
   | LTLcFalse
   | LTLcProp 'a  
   | LTLcNeg "'a ltlc"    
   | LTLcAnd "'a ltlc" "'a ltlc"  
   | LTLcOr "'a ltlc" "'a ltlc"   
   | LTLcImplies "'a ltlc" "'a ltlc"  
   | LTLcIff "'a ltlc" "'a ltlc"  
   | LTLcNext "'a ltlc"      
   | LTLcFinal "'a ltlc"     
   | LTLcGlobal "'a ltlc"    
   | LTLcUntil "'a ltlc" "'a ltlc"
   | LTLcRelease "'a ltlc" "'a ltlc"

notation
      LTLcTrue     ("true\<^sub>c")
  and LTLcFalse    ("false\<^sub>c")
  and LTLcProp     ("prop\<^sub>c'(_')")
  and LTLcNeg      ("not\<^sub>c _" [85] 85)
  and LTLcAnd      ("_ and\<^sub>c _" [82,82] 81)
  and LTLcOr       ("_ or\<^sub>c _" [81,81] 80)
  and LTLcImplies  ("_ implies\<^sub>c _" [81,81] 80)
  and LTLcIff      ("_ iff\<^sub>c _" [81,81] 80)
  and LTLcNext     ("X\<^sub>c _" [88] 87)
  and LTLcFinal    ("F\<^sub>c _" [88] 87)
  and LTLcGlobal   ("G\<^sub>c _" [88] 87)
  and LTLcUntil    ("_ U\<^sub>c _" [84,84] 83)
  and LTLcRelease  ("_ V\<^sub>c _" [83,83] 82)

fun ltlc_semantics 
  :: "['a set word, 'a ltlc] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>c _" [80,80] 80)
where
    "\<xi> \<Turnstile>\<^sub>c true\<^sub>c = True"
  | "\<xi> \<Turnstile>\<^sub>c false\<^sub>c = False"
  | "\<xi> \<Turnstile>\<^sub>c prop\<^sub>c(q) = (q\<in>\<xi> 0)"
  | "\<xi> \<Turnstile>\<^sub>c not\<^sub>c \<phi> = (\<not> \<xi> \<Turnstile>\<^sub>c \<phi>)"
  | "\<xi> \<Turnstile>\<^sub>c \<phi> and\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<and> \<xi> \<Turnstile>\<^sub>c \<psi>)"
  | "\<xi> \<Turnstile>\<^sub>c \<phi> or\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<or> \<xi> \<Turnstile>\<^sub>c \<psi>)"
  | "\<xi> \<Turnstile>\<^sub>c \<phi> implies\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<longrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi>)"
  | "\<xi> \<Turnstile>\<^sub>c \<phi> iff\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi>)"
  | "\<xi> \<Turnstile>\<^sub>c X\<^sub>c \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>c \<phi>)"
  | "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<phi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi>)"
  | "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<phi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi>)"
  | "\<xi> \<Turnstile>\<^sub>c \<phi> U\<^sub>c \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<phi>))"
  | "\<xi> \<Turnstile>\<^sub>c \<phi> V\<^sub>c \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<phi>))"

subsection \<open>Translation\<close>

--\<open>The following infrastructure translates the CAVA LTL datatype to the LTL datatype used in this project\<close>

fun ltlc_to_ltl :: "bool \<Rightarrow> 'a ltlc \<Rightarrow> 'a ltl"
where
  "ltlc_to_ltl False true\<^sub>c  = true"
| "ltlc_to_ltl False false\<^sub>c = false"
| "ltlc_to_ltl False prop\<^sub>c(q) = p(q)"
| "ltlc_to_ltl False (not\<^sub>c \<phi>) = ltlc_to_ltl True \<phi>"
| "ltlc_to_ltl False (\<phi> and\<^sub>c \<psi>) = ltlc_to_ltl False \<phi> and ltlc_to_ltl False \<psi>"
| "ltlc_to_ltl False (\<phi> or\<^sub>c \<psi>) = ltlc_to_ltl False \<phi> or ltlc_to_ltl False \<psi>"
| "ltlc_to_ltl False (\<phi> implies\<^sub>c \<psi>) = ltlc_to_ltl True \<phi> or ltlc_to_ltl False \<psi>"
| "ltlc_to_ltl False (\<phi> iff\<^sub>c \<psi>) = (ltlc_to_ltl True \<phi> or ltlc_to_ltl False \<psi>) and (ltlc_to_ltl False \<phi> or ltlc_to_ltl True \<psi>)"
| "ltlc_to_ltl False (F\<^sub>c \<phi>) = F (ltlc_to_ltl False \<phi>)"
| "ltlc_to_ltl False (G\<^sub>c \<phi>) = G (ltlc_to_ltl False \<phi>)"
| "ltlc_to_ltl False (\<phi> U\<^sub>c \<psi>) = ltlc_to_ltl False \<phi> U ltlc_to_ltl False \<psi>"
| "ltlc_to_ltl False (\<phi> V\<^sub>c \<psi>) = G (ltlc_to_ltl False \<psi>) or (ltlc_to_ltl False \<psi> U (ltlc_to_ltl False \<phi> and ltlc_to_ltl False \<psi>))"
| "ltlc_to_ltl True  true\<^sub>c  = false"
| "ltlc_to_ltl True  false\<^sub>c = true"
| "ltlc_to_ltl True  prop\<^sub>c(q) = np(q)"
| "ltlc_to_ltl True  (not\<^sub>c \<phi>) = ltlc_to_ltl False \<phi>"
| "ltlc_to_ltl True  (\<phi> and\<^sub>c \<psi>) = ltlc_to_ltl True \<phi> or ltlc_to_ltl True \<psi>"
| "ltlc_to_ltl True  (\<phi> or\<^sub>c \<psi>) = ltlc_to_ltl True \<phi> and ltlc_to_ltl True \<psi>"
| "ltlc_to_ltl True  (\<phi> implies\<^sub>c \<psi>) = ltlc_to_ltl False \<phi> and ltlc_to_ltl True \<psi>"
| "ltlc_to_ltl True  (\<phi> iff\<^sub>c \<psi>) = (ltlc_to_ltl True \<phi> and ltlc_to_ltl False \<psi>) or (ltlc_to_ltl False \<phi> and ltlc_to_ltl True \<psi>)"
| "ltlc_to_ltl True  (F\<^sub>c \<phi>) = G (ltlc_to_ltl True \<phi>)"
| "ltlc_to_ltl True  (G\<^sub>c \<phi>) = F (ltlc_to_ltl True \<phi>)"
| "ltlc_to_ltl True  (\<phi> U\<^sub>c \<psi>) = G (ltlc_to_ltl True \<psi>) or (ltlc_to_ltl True \<psi> U (ltlc_to_ltl True \<phi> and ltlc_to_ltl True \<psi>))"
| "ltlc_to_ltl True  (\<phi> V\<^sub>c \<psi>) = ltlc_to_ltl True \<phi> U ltlc_to_ltl True \<psi>"
| "ltlc_to_ltl b     (X\<^sub>c \<phi>) = X (ltlc_to_ltl b \<phi>)"

lemma V_equiv:
  "w \<Turnstile>\<^sub>c \<phi> V\<^sub>c \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>c (\<psi> U\<^sub>c (\<psi> and\<^sub>c \<phi>)) or\<^sub>c G\<^sub>c \<psi>"
proof (cases "\<exists>i. \<not>suffix i w \<Turnstile>\<^sub>c \<psi>")
  case True
    def i \<equiv> "Least (\<lambda>i. \<not>suffix i w \<Turnstile>\<^sub>c \<psi>)"
    have "\<And>j. j < i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>c \<psi>" and "\<not> suffix i w \<Turnstile>\<^sub>c \<psi>"
      using True LeastI not_less_Least unfolding i_def by metis+ (* Slow *)
    hence "(\<forall>i. suffix i w \<Turnstile>\<^sub>c \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>c \<phi>)) \<Longrightarrow> (\<exists>i. (suffix i w \<Turnstile>\<^sub>c \<psi> \<and> suffix i w \<Turnstile>\<^sub>c \<phi>) \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>c \<psi>))"
      by fastforce  
      moreover
     hence "(\<exists>i. (suffix i w \<Turnstile>\<^sub>c \<psi> \<and> suffix i w \<Turnstile>\<^sub>c \<phi>) \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>c \<psi>)) \<Longrightarrow> (\<forall>i. suffix i w \<Turnstile>\<^sub>c \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>c \<phi>))"
        using linorder_cases by blast
      ultimately
    show ?thesis
      using True by auto
qed auto

lemma push_neg_U:
  "w \<Turnstile>\<^sub>c (not\<^sub>c (\<phi> U\<^sub>c \<psi>)) \<longleftrightarrow> w \<Turnstile>\<^sub>c not\<^sub>c \<psi> U\<^sub>c (not\<^sub>c \<psi> and\<^sub>c not\<^sub>c \<phi>) or\<^sub>c G\<^sub>c (not\<^sub>c \<psi>)"
proof -
  have "w \<Turnstile>\<^sub>c (not\<^sub>c (\<phi> U\<^sub>c \<psi>)) \<longleftrightarrow> w \<Turnstile>\<^sub>c (not\<^sub>c \<phi>) V\<^sub>c (not\<^sub>c \<psi>)"
    by simp
  also
  have "\<dots> \<longleftrightarrow> w \<Turnstile>\<^sub>c not\<^sub>c \<psi> U\<^sub>c (not\<^sub>c \<psi> and\<^sub>c not\<^sub>c \<phi>) or\<^sub>c G\<^sub>c (not\<^sub>c \<psi>)"
    unfolding V_equiv by simp
  finally
  show ?thesis
    by blast
qed

lemma translation_correct:
  "w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> w \<Turnstile> ltlc_to_ltl False \<phi>"
  "\<not> w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> w \<Turnstile> ltlc_to_ltl True \<phi>"
proof (induction \<phi> arbitrary: w)
  case (LTLcUntil \<phi> \<psi>)
    case 2
      thus ?case
        by (unfold ltlc_to_ltl.simps ltl_semantics.simps LTLcUntil[symmetric] ltlc_semantics.simps(4)[symmetric] push_neg_U) auto
next
  case (LTLcRelease \<phi> \<psi>)
    case 1
      thus ?case
        by (unfold ltlc_to_ltl.simps ltl_semantics.simps LTLcRelease[symmetric] V_equiv) auto  
qed auto

end