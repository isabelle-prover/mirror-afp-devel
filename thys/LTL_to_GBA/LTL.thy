header {* Linear Temporal Logic *}
(* Author: Alexander Schimpf *)
theory LTL
imports 
  "../CAVA_Automata/Words"
begin

subsection "LTL formulas"

subsubsection {* Syntax *}

datatype_new
 'a ltl = LTLTrue      
       | LTLFalse      
       | LTLProp 'a    
       | LTLNeg "'a ltl"  
       | LTLAnd "'a ltl" "'a ltl"  
       | LTLOr "'a ltl" "'a ltl"   
       | LTLNext "'a ltl"      
       | LTLUntil "'a ltl" "'a ltl"
       | LTLRelease "'a ltl" "'a ltl"

text {* The following locale defines syntactic sugar for 
  parsing and printing LTL formulas in Isabelle *}
locale LTL_Syntax begin
notation 
           LTLTrue     ("true")
       and LTLFalse    ("false")
       and LTLProp     ("prop'(_')")
       and LTLNeg      ("not _" [85] 85)
       and LTLAnd      ("_ and _" [82,82] 81)
       and LTLOr       ("_ or _" [81,81] 80)
       and LTLNext     ("X _" [88] 87)
       and LTLUntil    ("_ U _" [84,84] 83)
       and LTLRelease  ("_ V _" [83,83] 82)
end

subsubsection {* Semantics *}
text {* We first provide an abstract semantics, that is parameterized with 
  the semantics of atomic propositions *}

context begin interpretation LTL_Syntax .

primrec ltl_semantics :: "'ap set word \<Rightarrow> 'ap ltl \<Rightarrow> bool" 
  ("_ \<Turnstile> _" [80,80] 80)
  where 
    "\<xi> \<Turnstile> true = True"
  | "\<xi> \<Turnstile> false = False"
  | "\<xi> \<Turnstile> prop(q) = (q \<in> (\<xi> 0))"
  | "\<xi> \<Turnstile> not \<phi> = (\<not> \<xi> \<Turnstile> \<phi>)"
  | "\<xi> \<Turnstile> \<phi> and \<psi> = (\<xi> \<Turnstile> \<phi> \<and> \<xi> \<Turnstile> \<psi>)"
  | "\<xi> \<Turnstile> \<phi> or \<psi> = (\<xi> \<Turnstile> \<phi> \<or> \<xi> \<Turnstile> \<psi>)"
  | "\<xi> \<Turnstile> X \<phi> = (suffix 1 \<xi> \<Turnstile> \<phi>)"
  | "\<xi> \<Turnstile> \<phi> U \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile> \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile> \<phi>))"
  | "\<xi> \<Turnstile> \<phi> V \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile> \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile> \<phi>))"

definition "ltl_language \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile> \<phi>}"
end

subsubsection {* Explicit Syntactic Sugar *}
text {* In this section, we provide a formulation of LTL with
  explicit syntactic sugar deeply embedded. This formalization
  serves as a reference semantics.
*}
datatype_new
 'a ltlc = LTLcTrue 
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

context LTL_Syntax begin
  notation
        LTLcTrue     ("true\<^sub>c")
    and LTLcFalse    ("false\<^sub>c")
    and LTLcProp     ("prop\<^sub>c'(_')")
    and LTLcNeg      ("not\<^sub>c _" [85] 85)
    and LTLcAnd      ("_ and\<^sub>c _" [82,82] 81)
    and LTLcOr       ("_ or\<^sub>c _" [81,81] 80)
    and LTLcImplies  ("_ implies\<^sub>c _" [81,81] 80)
    and LTLcIff      (" _ iff\<^sub>c _" [81,81] 80)
    and LTLcNext     ("X\<^sub>c _" [88] 87)
    and LTLcFinal    ("F\<^sub>c _" [88] 87)
    and LTLcGlobal   ("G\<^sub>c _" [88] 87)
    and LTLcUntil    ("_ U\<^sub>c _" [84,84] 83)
    and LTLcRelease  ("_ V\<^sub>c _" [83,83] 82)
end

context begin interpretation LTL_Syntax .

primrec ltlc_semantics 
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

definition "ltlc_language \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>c \<phi>}"

lemma ltlc_language_negate[simp]:
  "ltlc_language (not\<^sub>c \<phi>) = - ltlc_language \<phi>"
unfolding ltlc_language_def
by auto

lemma ltlc_semantics_sugar:
  "\<xi> \<Turnstile>\<^sub>c \<phi> implies\<^sub>c \<psi> = \<xi> \<Turnstile>\<^sub>c (not\<^sub>c \<phi> or\<^sub>c \<psi>)"
  "\<xi> \<Turnstile>\<^sub>c \<phi> iff\<^sub>c \<psi> = \<xi> \<Turnstile>\<^sub>c ((not\<^sub>c \<phi> or\<^sub>c \<psi>) and\<^sub>c (not\<^sub>c \<psi> or\<^sub>c \<phi>))"
  "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c (true\<^sub>c U\<^sub>c \<phi>)"
  "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c (false\<^sub>c V\<^sub>c \<phi>)"
by auto

text {* Conversion from LTL with common syntax to LTL *}

fun ltlc_to_ltl :: "'a ltlc \<Rightarrow> 'a ltl"
where
  "ltlc_to_ltl true\<^sub>c = true"
| "ltlc_to_ltl false\<^sub>c = false"
| "ltlc_to_ltl prop\<^sub>c(q) = prop(q)"
| "ltlc_to_ltl (not\<^sub>c \<phi>) = not (ltlc_to_ltl \<phi>)"
| "ltlc_to_ltl (\<phi> and\<^sub>c \<psi>) = ltlc_to_ltl \<phi> and ltlc_to_ltl \<psi>"
| "ltlc_to_ltl (\<phi> or\<^sub>c \<psi>) = ltlc_to_ltl \<phi> or ltlc_to_ltl \<psi>"
| "ltlc_to_ltl (\<phi> implies\<^sub>c \<psi>) = (not (ltlc_to_ltl \<phi>)) or (ltlc_to_ltl \<psi>)"
| "ltlc_to_ltl (\<phi> iff\<^sub>c \<psi>) = (let \<phi>' = ltlc_to_ltl \<phi> in
                             let \<psi>' = ltlc_to_ltl \<psi> in
                             (not \<phi>' or \<psi>') and (not \<psi>' or \<phi>'))"
| "ltlc_to_ltl (X\<^sub>c \<phi>) = X (ltlc_to_ltl \<phi>)"
| "ltlc_to_ltl (F\<^sub>c \<phi>) = true U ltlc_to_ltl \<phi>"
| "ltlc_to_ltl (G\<^sub>c \<phi>) = false V ltlc_to_ltl \<phi>"
| "ltlc_to_ltl (\<phi> U\<^sub>c \<psi>) = ltlc_to_ltl \<phi> U ltlc_to_ltl \<psi>"
| "ltlc_to_ltl (\<phi> V\<^sub>c \<psi>) = ltlc_to_ltl \<phi> V ltlc_to_ltl \<psi>"

lemma ltlc_to_ltl_equiv:
  "\<xi> \<Turnstile> (ltlc_to_ltl \<phi>) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c \<phi>"
  apply (induct \<phi> arbitrary:\<xi>) 
  apply (auto simp: Let_def)
  done

end

subsection {* Semantic Preserving Syntax Transformations *}

context begin interpretation LTL_Syntax .

lemma ltl_true_or_con[simp]:
  "\<xi> \<Turnstile> prop(p) or (not prop(p)) \<longleftrightarrow> \<xi> \<Turnstile> true"
  by auto

lemma ltl_false_true_con[simp]:
  "\<xi> \<Turnstile> not true \<longleftrightarrow> \<xi> \<Turnstile> false"
  by auto

text{*
  The negation symbol can be passed through the next operator.
*}
lemma ltl_Next_Neg_con[simp]:
  "\<xi> \<Turnstile> X (not \<phi>) \<longleftrightarrow> \<xi> \<Turnstile> not X \<phi>"
  by auto

text{*
  The connection between Until and Release
*}
lemma ltl_Release_Until_con:
 "\<xi> \<Turnstile> \<phi> V \<psi> \<longleftrightarrow> (\<not> \<xi> \<Turnstile> (not \<phi>) U (not \<psi>))"
  by auto


text{* Expand strategy *}

lemma ltl_expand_Until:
  "\<xi> \<Turnstile> \<phi> U \<psi> \<longleftrightarrow> (\<xi> \<Turnstile> \<psi> or (\<phi> and (X (\<phi> U \<psi>))))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain i
        where psi_is: "suffix i \<xi> \<Turnstile> \<psi>"
          and phi_is: "\<forall>j<i. suffix j \<xi> \<Turnstile> \<phi>" by auto
  show ?rhs
  proof(cases i)
    case 0
    thus ?rhs using psi_is by auto
  next
    case (Suc k)
    with phi_is have "\<xi> \<Turnstile> \<phi>" by auto
    moreover
    have "\<xi> \<Turnstile> X (\<phi> U \<psi>)" 
    using psi_is phi_is Suc by auto
    ultimately show ?rhs by auto
  qed
next
  assume rhs: ?rhs
  show ?lhs
  proof(cases "\<xi> \<Turnstile> \<psi>")
    case True
    hence "suffix 0 \<xi> \<Turnstile> \<psi>" by auto
    moreover
    have "\<forall>j<0. suffix j \<xi> \<Turnstile> \<phi>" by auto
    ultimately
    have "\<exists>i. suffix i \<xi> \<Turnstile> \<psi>
              \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile> \<phi>)" by blast
    thus ?lhs by auto
  next
    case False
    hence phi_is: "\<xi> \<Turnstile> \<phi>"
      and "\<xi> \<Turnstile> X (\<phi> U \<psi>)" using rhs by auto
    then obtain i
          where psi_suc_is: "suffix (Suc i) \<xi> \<Turnstile> \<psi>"
            and phi_suc_is: "\<forall>j<i. suffix (Suc j) \<xi> \<Turnstile> \<phi>" by auto
    have sbgoal: "\<forall>j<(Suc i). suffix j \<xi> \<Turnstile> \<phi>"
    proof(clarify)
      fix j
      assume j_less: "j<Suc i"
      show "suffix j \<xi> \<Turnstile> \<phi>"
      proof (cases j)
        assume "j=0"
        thus ?thesis using phi_is by auto
      next
        fix k
        assume "j=Suc k"
        thus ?thesis using j_less phi_suc_is by auto
      qed
    qed
    thus ?lhs using psi_suc_is phi_is by auto
  qed
qed

lemma ltl_expand_Release:
  "\<xi> \<Turnstile> \<phi> V \<psi> \<longleftrightarrow> (\<xi> \<Turnstile> \<psi> and (\<phi> or (X (\<phi> V \<psi>))))"
proof -
  from ltl_expand_Until[of \<xi> "not \<phi>" "not \<psi>"]
  show ?thesis by auto
qed

text{* Double negation structure of an LTL formula *}

lemma [simp]:
  "not ((\<lambda>\<mu>. not not \<mu>) ^^ n) \<phi> = ((\<lambda>\<mu>. not not \<mu>) ^^ n) (not \<phi>)" 
  by (induct n) auto

lemma ltl_double_neg_struct:
  shows "\<exists>n \<psi>. \<phi> = ((\<lambda>\<xi>. not not \<xi>) ^^ n) \<psi> \<and> (\<forall>\<nu>. \<psi> \<noteq> not not \<nu>)" 
  (is "\<exists>n \<psi>. ?Q \<phi> n \<psi>")
proof(cases "\<forall>\<nu>. \<phi> \<noteq> not \<nu>")
  case goal1
    hence "?Q \<phi> 0 \<phi>" by auto
    thus ?thesis by blast
next
  case goal2
    thus ?thesis
    proof(induct \<phi>)
      case (LTLNeg \<phi>')
        thus ?case
        proof(cases "\<forall>\<nu>. \<phi>' \<noteq> not \<nu>")
          case goal1
            hence "?Q (not \<phi>') 0 (not \<phi>')" by auto
            thus ?case by blast
        next
          case goal2
            then obtain n' \<psi>' where "?Q \<phi>' n' \<psi>'" by auto
            thus ?case
            proof(cases "\<exists>\<psi>''. \<psi>' = not \<psi>''")
              case goal1
                then obtain \<psi>''
                      where "\<psi>' = not \<psi>''" by auto
                hence "?Q (not \<phi>') (n'+1) \<psi>''" using goal1 by auto
                thus ?case by blast
            next
              case goal2
                hence "?Q (not \<phi>') n' (not \<psi>')" by auto
                thus ?case by blast
            qed
        qed
    qed auto
qed 

lemma ltl_size_double_neg:
  assumes "\<psi> = ((\<lambda>\<mu>. not not \<mu>) ^^ n) \<phi>"
    shows "size \<phi> \<le> size \<psi>"
using assms proof (induct n arbitrary:\<phi> \<psi>)
  case (Suc k)
    obtain \<mu> where \<mu>_eq: "\<mu> = ((\<lambda>\<mu>. not not \<mu>) ^^ k) \<phi>" by auto
    hence "\<psi> = not not \<mu>" using Suc by auto
    moreover have "size \<phi> \<le> size \<mu>" using Suc \<mu>_eq by auto
    ultimately show ?case by auto
qed auto


text{* Pushing negation to the top of a proposition *}

fun
  ltl_pushneg :: "'a ltl \<Rightarrow> 'a ltl"
  where
    "ltl_pushneg true = true"
  | "ltl_pushneg false = false"
  | "ltl_pushneg prop(q) = prop(q)"
  | "ltl_pushneg (not true) = false"
  | "ltl_pushneg (not false) = true"
  | "ltl_pushneg (not prop(q)) = not prop(q)"
  | "ltl_pushneg (not (not \<psi>)) = ltl_pushneg \<psi>"
  | "ltl_pushneg (not (\<nu> and \<mu>)) = ltl_pushneg (not \<nu>) or ltl_pushneg (not \<mu>)"
  | "ltl_pushneg (not (\<nu> or \<mu>)) = ltl_pushneg (not \<nu>) and ltl_pushneg (not \<mu>)"
  | "ltl_pushneg (not (X \<psi>)) = X ltl_pushneg (not \<psi>)"
  | "ltl_pushneg (not (\<nu> U \<mu>)) = ltl_pushneg (not \<nu>) V ltl_pushneg (not \<mu>)"
  | "ltl_pushneg (not (\<nu> V \<mu>)) = ltl_pushneg (not \<nu>) U ltl_pushneg (not \<mu>)"
  | "ltl_pushneg (\<phi> and \<psi>) = (ltl_pushneg \<phi>) and (ltl_pushneg \<psi>)"
  | "ltl_pushneg (\<phi> or \<psi>) = (ltl_pushneg \<phi>) or (ltl_pushneg \<psi>)"
  | "ltl_pushneg (X \<phi>) = X (ltl_pushneg \<phi>)"
  | "ltl_pushneg (\<phi> U \<psi>) = (ltl_pushneg \<phi>) U (ltl_pushneg \<psi>)"
  | "ltl_pushneg (\<phi> V \<psi>) = (ltl_pushneg \<phi>) V (ltl_pushneg \<psi>)"


text{*
  In fact, the @{text ltl_pushneg} function does not change the 
  semantics of the input formula.
*}

lemma ltl_pushneg_neg:
  shows "\<xi> \<Turnstile> ltl_pushneg (not \<phi>) \<longleftrightarrow> \<xi> \<Turnstile> not ltl_pushneg \<phi>"
  by (induct \<phi> arbitrary: \<xi>) auto

theorem ltl_pushneg_equiv[simp]:
  "\<xi> \<Turnstile> ltl_pushneg \<phi> \<longleftrightarrow> \<xi> \<Turnstile> \<phi>"
proof (induct \<phi> arbitrary: \<xi>)
  case (LTLNeg \<psi>) 
  with ltl_pushneg_neg show ?case by auto
qed auto


text{*
  We can now show that @{text ltl_pushneg} does what it should do.
  Actually the negation occurs after the transformation
  only on top of a proposition.
*} (* TODO (Alex): Formulation! Describe the 'what' in one or two sentences! *)

lemma ltl_pushneg_double_neg:
  shows "ltl_pushneg (((\<lambda>\<phi>. not not \<phi>) ^^ n) \<phi>) = ltl_pushneg \<phi>"
by (induct n arbitrary:\<phi>) auto

lemma ltl_pushneg_neg_struct:
  assumes "ltl_pushneg \<phi> = not \<psi>"
    shows "\<exists>q. \<psi> = prop(q)"
proof -
  from ltl_double_neg_struct
  obtain n \<mu> where \<phi>_eq: "\<phi> = ((\<lambda>\<mu>. not not \<mu>) ^^ n) \<mu>"
               and \<mu>_neq: "(\<forall>\<nu>. \<mu> \<noteq> not not \<nu>)" by blast
  with ltl_pushneg_double_neg have "ltl_pushneg \<phi> = ltl_pushneg \<mu>" by auto
  thus ?thesis using \<phi>_eq assms \<mu>_neq
  proof(induct \<mu>)
    case (LTLNeg f) thus ?case by (cases f) auto
  qed auto
qed

inductive subfrml
where
  "subfrml \<phi> (not \<phi>)"
| "subfrml \<phi> (\<phi> and \<psi>)"
| "subfrml \<psi> (\<phi> and \<psi>)"
| "subfrml \<phi> (\<phi> or \<psi>)"
| "subfrml \<psi> (\<phi> or \<psi>)"
| "subfrml \<phi> (X \<phi>)"
| "subfrml \<phi> (\<phi> U \<psi>)"
| "subfrml \<psi> (\<phi> U \<psi>)"
| "subfrml \<phi> (\<phi> V \<psi>)"
| "subfrml \<psi> (\<phi> V \<psi>)"

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
  case base thus ?case by auto
next
  case (step \<nu> \<mu>)
    hence "size \<nu> < size \<mu>" by (rule_tac subfrml_size)
    thus ?case using step by auto
qed


lemma subformula_on_ltl_pushneg:
  assumes "\<psi> is_subformula_of (ltl_pushneg \<phi>)"
    shows "\<exists>\<mu>. \<psi> = ltl_pushneg \<mu>"
proof(cases "\<psi> = ltl_pushneg \<phi>")
  case True thus ?thesis by blast
next
  case False thus ?thesis using assms
  proof(induct \<phi> rule:ltl_pushneg.induct)
    case goal1 thus ?case using subformula_size by force
  next
    case goal2 thus ?case using subformula_size by force
  next
    case goal3 thus ?case using subformula_size by force
  next
    case goal4 thus ?case using subformula_size by force
  next
    case goal5 thus ?case using subformula_size by force
  next
    case (goal6 q)
      let ?frml = "not prop(q)"
      from rtrancl_eq_or_trancl[to_pred, of subfrml]
      have t_prm: "subfrml\<^sup>+\<^sup>+ \<psi> ?frml"
      using goal6 by auto
      obtain \<mu>
       where sf_prm: "subfrml \<psi>  \<mu>"
         and rt_prm: "\<mu> is_subformula_of ?frml"
      using tranclpD[OF t_prm] by blast
      show ?case
      proof(cases "\<mu> = ?frml")
        assume "\<mu> = ?frml"
        with sf_prm have "\<psi> = ltl_pushneg prop(q)"
        by (cases \<psi>) auto
        thus ?thesis by blast
      next
        assume "\<mu> \<noteq> ?frml"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp[of subfrml]
             subformula_size[of \<mu> ?frml]
        have "size \<mu> = 0" by auto
        with subfrml_size[OF sf_prm]
        show ?thesis by auto
      qed
  next
    case goal7 thus ?case by auto
  next
    case (goal8 \<nu> \<mu>)
      let ?frml = "not (\<nu> and \<mu>)"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal8 by auto
      hence z_is:
            "z = ltl_pushneg (not \<nu>) \<or> 
             z = ltl_pushneg (not \<mu>)" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal8 z_is by auto
      qed
  next
    case (goal9 \<nu> \<mu>)
      let ?frml = "not (\<nu> or \<mu>)"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal9 by auto
      hence z_is:
            "z = ltl_pushneg (not \<nu>) \<or> 
             z = ltl_pushneg (not \<mu>)" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal9 z_is by auto
      qed
  next
    case (goal10 \<mu>)
      let ?frml = "not (X \<mu>)"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal10 by auto
      hence z_is: "z = ltl_pushneg (not \<mu>)"
      by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal10 z_is by auto
      qed
  next
    case (goal11 \<nu> \<mu>)
      let ?frml = "not (\<nu> U \<mu>)"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal11 by auto
      hence z_is:
            "z = ltl_pushneg (not \<nu>) \<or> 
             z = ltl_pushneg (not \<mu>)" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal11 z_is by auto
      qed
  next
    case (goal12 \<nu> \<mu>)
      let ?frml = "not (\<nu> V \<mu>)"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal12 by auto
      hence z_is:
            "z = ltl_pushneg (not \<nu>) \<or> 
             z = ltl_pushneg (not \<mu>)" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal12 z_is by auto
      qed
  next
    case (goal13 \<nu> \<mu>)
      let ?frml = "\<nu> and \<mu>"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal13 by auto
      hence z_is:
            "z = ltl_pushneg \<nu> \<or> 
             z = ltl_pushneg \<mu>" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal13 z_is by auto
      qed
  next
    case (goal14 \<nu> \<mu>)
      let ?frml = "\<nu> or \<mu>"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal14 by auto
      hence z_is:
            "z = ltl_pushneg \<nu> \<or> 
             z = ltl_pushneg \<mu>" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal14 z_is by auto
      qed
  next
    case (goal15 \<mu>)
      let ?frml = "X \<mu>"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal15 by auto
      hence z_is: "z = ltl_pushneg \<mu>" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal15 z_is by auto
      qed
  next
    case (goal16 \<nu> \<mu>)
      let ?frml = "\<nu> U \<mu>"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal16 by auto
      hence z_is:
            "z = ltl_pushneg \<nu> \<or> 
             z = ltl_pushneg \<mu>" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal16 z_is by auto
      qed
  next
    case (goal17 \<nu> \<mu>)
      let ?frml = "\<nu> V \<mu>"
      from tranclD2[to_pred, of subfrml \<psi> "ltl_pushneg ?frml"]
           rtrancl_eq_or_trancl[to_pred, of subfrml]
      obtain z
       where "subfrml z (ltl_pushneg ?frml)"
         and rt_prm: "\<psi> is_subformula_of z"
       using goal17 by auto
      hence z_is:
            "z = ltl_pushneg \<nu> \<or> 
             z = ltl_pushneg \<mu>" by (cases z) auto
      show ?case
      proof(cases "\<psi> = z")
        assume "\<psi> = z"
        with z_is show ?thesis by auto
      next
        assume "\<psi> \<noteq> z"
        with rtranclpD[OF rt_prm]
             tranclp_into_rtranclp
        have "\<psi> is_subformula_of z" by auto
        thus ?thesis using goal17 z_is by auto
      qed
  qed
qed


text{*
  The fact that after pushing the negation the structure of a
  formula changes, is shown by the following theorem.
  Indeed, after pushing the negation symbol inside a
  formula, it occurs at most on top of a proposition.
*}

theorem ltl_pushneg_struct:
  assumes "(not \<psi>) is_subformula_of (ltl_pushneg \<phi>)"
    shows "\<exists>q. \<psi> = prop(q)"
proof -
  from assms subformula_on_ltl_pushneg
  obtain \<mu>
   where prm:"not \<psi> = ltl_pushneg \<mu>" by blast
  from ltl_pushneg_neg_struct[OF sym[OF prm]]
  show ?thesis by auto
qed


text{*
  Now we want to show that the size of the formula,
  which is transformed by @{text ltl_pushneg}, does not increase
  'too much', i.e. there is no exponential blowup
  produced by the transformation.
  For that purpose we need an additional function,
  which counts the literals of the derivation tree
  of a formula.
  The idea is, that, assuming the worst case, the
  pushing of negation can only increase the size of a
  formula by putting the negation symbol on top of every
  proposition inside the formula.
*}

fun leafcnt :: "'a ltl \<Rightarrow> nat"
where
  "leafcnt true = 1"
| "leafcnt false = 1"
| "leafcnt prop(q) = 1"
| "leafcnt (not \<phi>) = leafcnt \<phi>"
| "leafcnt (\<phi> and \<psi>) = (leafcnt \<phi>) + (leafcnt \<psi>)"
| "leafcnt (\<phi> or \<psi>) = (leafcnt \<phi>) + (leafcnt \<psi>)"
| "leafcnt (X \<phi>) = leafcnt \<phi>"
| "leafcnt (\<phi> U \<psi>) = (leafcnt \<phi>) + (leafcnt \<psi>)"
| "leafcnt (\<phi> V \<psi>) = (leafcnt \<phi>) + (leafcnt \<psi>)"


lemma leafcnt_double_neg_ident:
  "leafcnt (((\<lambda>\<mu>. not not \<mu>) ^^ n) \<phi>) = leafcnt \<phi>"
by (induct n arbitrary:\<phi>) auto

lemma ltl_pushneg_help:
  "\<exists>\<phi>. ltl_pushneg \<psi> = ltl_pushneg \<phi>
       \<and> ((\<exists>\<nu>. \<phi> = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)) \<or> (\<forall>\<mu>. \<phi> \<noteq> not \<mu>))
       \<and> size \<phi> \<le> size \<psi>
       \<and> leafcnt \<phi> = leafcnt \<psi>"
  (is "\<exists>\<phi>. ?P \<psi> \<phi> \<and> ?Q \<phi> \<and> ?R \<phi>")
proof -
  from ltl_double_neg_struct
  obtain n \<phi> where dblneg: "\<psi> = ((\<lambda>\<mu>. not not \<mu>) ^^ n) \<phi>"
               and \<phi>_neq: "(\<forall>\<nu>. \<phi> \<noteq> not not \<nu>)"
                by blast
  have "?Q \<phi>"
  proof(rule ccontr)
    assume "\<not> ?Q \<phi>"
    thus "False"
    proof(cases "\<exists>\<mu>. \<phi> = not \<mu>")
      case goal1
        then obtain \<mu> where "\<phi> = not \<mu>" by blast
        with goal1 dblneg \<phi>_neq show ?case by auto
    qed auto
  qed
  with dblneg \<phi>_neq
       ltl_pushneg_double_neg[of n \<phi>]
       leafcnt_double_neg_ident[of n \<phi>]
       ltl_size_double_neg[OF dblneg] show ?thesis by auto
qed


lemma ltl_pushneg_size_lin_help:
  assumes "\<psi> = ltl_pushneg \<phi>"
    shows "size \<psi> + 1 \<le> size \<phi> + leafcnt \<phi>"
using assms proof (induct \<psi> arbitrary: \<phi>)
  case goal1 show ?case by (cases \<phi>) auto
next
  case goal2 show ?case by (cases \<phi>) auto
next
  case goal3 show ?case by (cases \<phi>) auto
next
  case (goal4 \<psi>')
    with ltl_pushneg_neg_struct[of \<phi> \<psi>'] obtain q where "\<psi>' = prop(q)" by auto
    moreover
    with ltl_pushneg_help[of \<phi>]
    obtain \<phi>' where "ltl_pushneg \<phi> = ltl_pushneg \<phi>'"
                and "(\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)) \<or> (\<forall>\<mu>. \<phi>' \<noteq> not \<mu>)"
                and "size \<phi>' \<le> size \<phi>"
                and "leafcnt \<phi>' = leafcnt \<phi>" by auto
    ultimately show ?case using goal4
    proof(cases "\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)")
      case goal1
        then obtain \<nu> where \<phi>'is:"\<phi>' = not \<nu>" and "\<forall>\<mu>. \<nu> \<noteq> not \<mu>" by auto
        thus ?case using goal1 by (cases \<nu>) auto
    next
      case goal2 thus ?case by (cases \<phi>') force+
    qed
next
  case (goal5 f g)
    with ltl_pushneg_help[of \<phi>]
    obtain \<phi>' where "ltl_pushneg \<phi> = ltl_pushneg \<phi>'"
                and "(\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)) \<or> (\<forall>\<mu>. \<phi>' \<noteq> not \<mu>)"
                and "size \<phi>' \<le> size \<phi>"
                and "leafcnt \<phi>' = leafcnt \<phi>" by auto
    with goal5 show ?case
    proof(cases "\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)")
      case goal1
        then obtain \<nu> where \<phi>'is:"\<phi>' = not \<nu>" and "\<forall>\<mu>. \<nu> \<noteq> not \<mu>" by auto
        hence "size (f and g) \<le> size \<nu> + leafcnt \<nu>" using goal1 by (cases \<nu>) force+
        thus ?case using goal1 \<phi>'is by auto
    next
      case goal2 thus ?case by (cases \<phi>') force+
    qed
next
  case (goal6 f g)
    with ltl_pushneg_help[of \<phi>]
    obtain \<phi>' where "ltl_pushneg \<phi> = ltl_pushneg \<phi>'"
                and "(\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)) \<or> (\<forall>\<mu>. \<phi>' \<noteq> not \<mu>)"
                and "size \<phi>' \<le> size \<phi>"
                and "leafcnt \<phi>' = leafcnt \<phi>" by auto
    with goal6 show ?case
    proof(cases "\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)")
      case goal1
        then obtain \<nu> where \<phi>'is:"\<phi>' = not \<nu>" and "\<forall>\<mu>. \<nu> \<noteq> not \<mu>" by auto
        hence "size (f or g) \<le> size \<nu> + leafcnt \<nu>" using goal1 by (cases \<nu>) force+
        thus ?case using goal1 \<phi>'is by auto
    next
      case goal2 thus ?case by (cases \<phi>') force+
    qed
next
  case (goal7 f)
    with ltl_pushneg_help[of \<phi>]
    obtain \<phi>' where "ltl_pushneg \<phi> = ltl_pushneg \<phi>'"
                and "(\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)) \<or> (\<forall>\<mu>. \<phi>' \<noteq> not \<mu>)"
                and "size \<phi>' \<le> size \<phi>"
                and "leafcnt \<phi>' = leafcnt \<phi>" by auto
    with goal7 show ?case
    proof(cases "\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)")
      case goal1
        then obtain \<nu> where \<phi>'is:"\<phi>' = not \<nu>" and "\<forall>\<mu>. \<nu> \<noteq> not \<mu>" by auto
        with goal1 show ?case by (cases \<nu>) force+
    next
      case goal2 thus ?case by (cases \<phi>') force+
    qed
next
  case (goal8 f g)
    with ltl_pushneg_help[of \<phi>]
    obtain \<phi>' where "ltl_pushneg \<phi> = ltl_pushneg \<phi>'"
                and "(\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)) \<or> (\<forall>\<mu>. \<phi>' \<noteq> not \<mu>)"
                and "size \<phi>' \<le> size \<phi>"
                and "leafcnt \<phi>' = leafcnt \<phi>" by auto
    with goal8 show ?case
    proof(cases "\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)")
      case goal1
        then obtain \<nu> where \<phi>'is:"\<phi>' = not \<nu>" and "\<forall>\<mu>. \<nu> \<noteq> not \<mu>" by auto
        hence "size (f U g) \<le> size \<nu> + leafcnt \<nu>" using goal1 by (cases \<nu>) force+
        thus ?case using goal1 \<phi>'is by auto
    next
      case goal2 thus ?case by (cases \<phi>') force+
    qed
next
  case (goal9 f g)
    with ltl_pushneg_help[of \<phi>]
    obtain \<phi>' where "ltl_pushneg \<phi> = ltl_pushneg \<phi>'"
                and "(\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)) \<or> (\<forall>\<mu>. \<phi>' \<noteq> not \<mu>)"
                and "size \<phi>' \<le> size \<phi>"
                and "leafcnt \<phi>' = leafcnt \<phi>" by auto
    with goal9 show ?case
    proof(cases "\<exists>\<nu>. \<phi>' = not \<nu> \<and> (\<forall>\<mu>. \<nu> \<noteq> not \<mu>)")
      case goal1
        then obtain \<nu> where \<phi>'is:"\<phi>' = not \<nu>" and "\<forall>\<mu>. \<nu> \<noteq> not \<mu>" by auto
        hence "size (f V g) \<le> size \<nu> + leafcnt \<nu>" using goal1 by (cases \<nu>) force+
        thus ?case using goal1 \<phi>'is by auto
    next
      case goal2 thus ?case by (cases \<phi>') force+
    qed
qed

theorem ltl_pushneg_size_lin:
  "size (ltl_pushneg \<phi>) \<le> 2 * size \<phi>"
proof -
  have "leafcnt \<phi> \<le> size \<phi> + 1" by (induct \<phi>) auto
  with ltl_pushneg_size_lin_help[of _ \<phi>]
  have "size (ltl_pushneg \<phi>) + 1 \<le> size \<phi> + size \<phi> + 1" by force
  thus ?thesis by auto
qed

end

subsection {* LTL formula in negation normal form (NNF) *}
text{*
  We define a type of LTL formula in negation normal form (NNF)
*}


datatype_new
  'a ltln = LTLnTrue  
       | LTLnFalse    
       | LTLnProp 'a    
       | LTLnNProp 'a   
       | LTLnAnd "'a ltln" "'a ltln" 
       | LTLnOr "'a ltln" "'a ltln"  
       | LTLnNext "'a ltln"          
       | LTLnUntil "'a ltln" "'a ltln" 
       | LTLnRelease "'a ltln" "'a ltln"

context LTL_Syntax begin
  notation
        LTLnTrue      ("true\<^sub>n")
    and LTLnFalse     ("false\<^sub>n")
    and LTLnProp      ("prop\<^sub>n'(_')")
    and LTLnNProp     ("nprop\<^sub>n'(_')")
    and LTLnAnd       ("_ and\<^sub>n _" [82,82] 81)
    and LTLnOr        ("_ or\<^sub>n _" [84,84] 83)
    and LTLnNext      ("X\<^sub>n _" [88] 87)
    and LTLnUntil     ("_ U\<^sub>n _" [84,84] 83)
    and LTLnRelease   ("_ V\<^sub>n _" [84,84] 83)

  abbreviation ltln_eventuality :: "'a ltln \<Rightarrow> 'a ltln" ("\<diamondsuit>\<^sub>n _" [88] 87)
    where "ltln_eventuality \<phi> \<equiv> true\<^sub>n U\<^sub>n \<phi>" 

  abbreviation ltln_universality :: "'a ltln \<Rightarrow> 'a ltln" ("\<box>\<^sub>n _" [88] 87)
    where "ltln_universality \<phi> \<equiv> false\<^sub>n V\<^sub>n \<phi>" 

end

context begin interpretation LTL_Syntax .

primrec ltln_semantics :: "['a set word, 'a ltln] \<Rightarrow> bool" 
("_ \<Turnstile>\<^sub>n _" [80,80] 80)
  where
    "\<xi> \<Turnstile>\<^sub>n true\<^sub>n = True"
  | "\<xi> \<Turnstile>\<^sub>n false\<^sub>n = False"
  | "\<xi> \<Turnstile>\<^sub>n prop\<^sub>n(q) = (q\<in>\<xi> 0)"
  | "\<xi> \<Turnstile>\<^sub>n nprop\<^sub>n(q) = (q\<notin>\<xi> 0)"
  | "\<xi> \<Turnstile>\<^sub>n \<phi> and\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<phi> \<and> \<xi> \<Turnstile>\<^sub>n \<psi>)"
  | "\<xi> \<Turnstile>\<^sub>n \<phi> or\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<phi> \<or> \<xi> \<Turnstile>\<^sub>n \<psi>)"
  | "\<xi> \<Turnstile>\<^sub>n X\<^sub>n \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>n \<phi>)"
  | "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>))"
  | "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>))"

definition "ltln_language \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>n \<phi>}"

text{*
  Conversion from LTL to LTL in NNF
*}

fun ltl_to_ltln :: "'a ltl \<Rightarrow> 'a ltln"
where
  "ltl_to_ltln true = true\<^sub>n"
| "ltl_to_ltln false = false\<^sub>n"
| "ltl_to_ltln prop(q) = prop\<^sub>n(q)"
| "ltl_to_ltln (not prop(q)) = nprop\<^sub>n(q)"
| "ltl_to_ltln (\<phi> and \<psi>) = ltl_to_ltln \<phi> and\<^sub>n ltl_to_ltln \<psi>"
| "ltl_to_ltln (\<phi> or \<psi>) = ltl_to_ltln \<phi> or\<^sub>n ltl_to_ltln \<psi>"
| "ltl_to_ltln (X \<phi>) = X\<^sub>n (ltl_to_ltln \<phi>)"
| "ltl_to_ltln (\<phi> U \<psi>) = ltl_to_ltln \<phi> U\<^sub>n ltl_to_ltln \<psi>"
| "ltl_to_ltln (\<phi> V \<psi>) = ltl_to_ltln \<phi> V\<^sub>n ltl_to_ltln \<psi>"


lemma ltl_to_ltln_on_ltl_pushneg_equiv:
  assumes "\<phi> = ltl_pushneg \<psi>"
  shows "\<xi> \<Turnstile> \<phi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n ltl_to_ltln \<phi>"
using assms proof(induct \<phi> arbitrary: \<xi> \<psi>)
  case goal1 show ?case by auto
next
  case goal2 show ?case by auto
next
  case goal3 show ?case by auto
next
  case (goal4 \<phi>)
    with ltl_pushneg_neg_struct[of \<psi> \<phi>]
    obtain q
     where "\<phi> = prop(q)"
        by auto
    thus ?case by auto
next
  case (goal5 f g \<xi> \<psi>)
    hence frml_eq: "ltl_pushneg \<psi> = f and g" by auto
    with subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<mu>
     where "f = ltl_pushneg \<mu>"
        by (auto intro: subfrml.intros)
    moreover
    from frml_eq subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<nu>
     where "g = ltl_pushneg \<nu>"
        by (auto intro: subfrml.intros)
    ultimately
    have "\<xi> \<Turnstile> f = \<xi> \<Turnstile>\<^sub>n ltl_to_ltln f"
     and "\<xi> \<Turnstile> g = \<xi> \<Turnstile>\<^sub>n ltl_to_ltln g"
    using goal5 by auto
    thus ?case by auto
next
  case (goal6 f g \<xi> \<psi>)
    hence frml_eq: "ltl_pushneg \<psi> = f or g" by auto
    with subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<mu>
     where "f = ltl_pushneg \<mu>"
        by (auto intro: subfrml.intros)
    moreover
    from frml_eq subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<nu>
     where "g = ltl_pushneg \<nu>"
        by (auto intro: subfrml.intros)
    ultimately
    have "\<xi> \<Turnstile> f = \<xi> \<Turnstile>\<^sub>n ltl_to_ltln f"
     and "\<xi> \<Turnstile> g = \<xi> \<Turnstile>\<^sub>n ltl_to_ltln g"
    using goal6 by auto
    thus ?case by auto
next
  case (goal7 \<phi> \<xi> \<psi>)
    hence "ltl_pushneg \<psi> = X \<phi>" by auto
    with subformula_on_ltl_pushneg[of \<phi> \<psi>]
    obtain \<mu>
     where "\<phi> = ltl_pushneg \<mu>"
        by (auto intro: subfrml.intros)
    hence "suffix 1 \<xi> \<Turnstile> \<phi> = suffix 1 \<xi> \<Turnstile>\<^sub>n ltl_to_ltln \<phi>"
    using goal7 by auto
    thus ?case by auto
next
  case (goal8 f g \<xi> \<psi>)
    hence frml_eq: "ltl_pushneg \<psi> = f U g" by auto
    with subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<mu>
     where "f = ltl_pushneg \<mu>"
        by (auto intro: subfrml.intros)
    moreover
    from frml_eq subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<nu>
     where "g = ltl_pushneg \<nu>"
        by (auto intro: subfrml.intros)
    ultimately
    have "\<forall>i. suffix i \<xi> \<Turnstile> f = suffix i \<xi> \<Turnstile>\<^sub>n ltl_to_ltln f"
     and "\<forall>i. suffix i \<xi> \<Turnstile> g = suffix i \<xi> \<Turnstile>\<^sub>n ltl_to_ltln g"
    using goal8 by auto
    thus ?case by auto
next   
  case (goal9 f g \<xi> \<psi>)
    hence frml_eq: "ltl_pushneg \<psi> = f V g" by auto
    with subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<mu>
     where "f = ltl_pushneg \<mu>"
        by (auto intro: subfrml.intros)
    moreover
    from frml_eq subformula_on_ltl_pushneg[of _ \<psi>]
    obtain \<nu>
     where "g = ltl_pushneg \<nu>"
        by (auto intro: subfrml.intros)
    ultimately
    have "\<forall>i. suffix i \<xi> \<Turnstile> f = suffix i \<xi> \<Turnstile>\<^sub>n ltl_to_ltln f"
     and "\<forall>i. suffix i \<xi> \<Turnstile> g = suffix i \<xi> \<Turnstile>\<^sub>n ltl_to_ltln g"
    using goal9 by auto
    thus ?case by auto
qed


lemma ltl_nnf_equiv[simp]:
  "\<xi> \<Turnstile>\<^sub>n ltl_to_ltln (ltl_pushneg \<psi>) \<longleftrightarrow> \<xi> \<Turnstile> \<psi>"
  using sym[OF ltl_pushneg_equiv] ltl_to_ltln_on_ltl_pushneg_equiv by blast


fun subfrmlsn :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "subfrmlsn (\<mu> and\<^sub>n \<psi>) = {\<mu> and\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn (X\<^sub>n \<mu>) = {X\<^sub>n \<mu>} \<union> subfrmlsn \<mu>"
| "subfrmlsn (\<mu> U\<^sub>n \<psi>) = {\<mu> U\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<mu> V\<^sub>n \<psi>) = {\<mu> V\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<mu> or\<^sub>n \<psi>) = {\<mu> or\<^sub>n \<psi>} \<union> subfrmlsn \<mu> \<union> subfrmlsn \<psi>"
| "subfrmlsn x = {x}"

lemma subfrmlsn_id[simp]: "\<phi> \<in> subfrmlsn \<phi>" by (induct \<phi>) auto
lemma subfrmlsn_finite: "finite (subfrmlsn \<phi>)" by (induct \<phi>) auto
lemma subfrmlsn_subset:"\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> subfrmlsn \<psi> \<subseteq> subfrmlsn \<phi>"
by (induct \<phi> arbitrary:\<psi>) auto

fun size_frmln :: "'a ltln \<Rightarrow> nat"
where
  "size_frmln (\<phi> and\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln (X\<^sub>n \<phi>) = size_frmln \<phi> + 1"
| "size_frmln (\<phi> U\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln (\<phi> V\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln (\<phi> or\<^sub>n \<psi>) = size_frmln \<phi> + size_frmln \<psi> + 1"
| "size_frmln _ = 1"

lemma size_frmln_gt_zero[simp]: "size_frmln \<phi> > 0" by (induct \<phi>) auto

abbreviation
  "frmlset_sumn \<Phi> \<equiv> setsum size_frmln \<Phi>" -- "FIXME: lemmas about this?"

lemma frmlset_sumn_diff_less[intro!]:
  assumes finS:"finite S"
      and "A\<noteq>{}"
      and subset:"A\<subseteq>S"
    shows "frmlset_sumn (S - A) < frmlset_sumn S"
proof -
  have finA: "finite A" using assms by (rule_tac finite_subset)
  hence "frmlset_sumn A > 0" using assms size_frmln_gt_zero by (induct rule:finite_induct) auto
  moreover
  have "frmlset_sumn A \<le> frmlset_sumn S" using assms size_frmln_gt_zero by (rule_tac setsum_mono2) auto
  ultimately show ?thesis using setsum_diff_nat[OF finA, of S size_frmln] assms by auto
qed

definition
  "frmln_props \<phi> \<equiv> {p. prop\<^sub>n(p) \<in> subfrmlsn \<phi> \<or> nprop\<^sub>n(p) \<in> subfrmlsn \<phi>}"

lemma ltln_expand_Until:
  "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<psi> or\<^sub>n (\<phi> and\<^sub>n (X\<^sub>n (\<phi> U\<^sub>n \<psi>))))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain i
        where psi_is: "suffix i \<xi> \<Turnstile>\<^sub>n \<psi>"
          and phi_is: "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>" by auto
  show ?rhs
  proof(cases i)
    assume "i=0"
    thus ?rhs using psi_is by auto
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
    hence "suffix 0 \<xi> \<Turnstile>\<^sub>n \<psi>" by auto
    moreover
    have "\<forall>j<0. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>" by auto
    ultimately
    have "\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi>
              \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>)" by blast
    thus ?lhs by auto
  next
    assume "\<not> \<xi> \<Turnstile>\<^sub>n \<psi>"
    hence phi_is: "\<xi> \<Turnstile>\<^sub>n \<phi>"
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
        thus ?thesis using phi_is by auto
      next
        fix k
        assume "j=Suc k"
        thus ?thesis using j_less phi_suc_is by auto
      qed
    qed
    thus ?lhs using psi_suc_is phi_is by auto
  qed
qed

lemma ltln_expand_Release:
  "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<psi> and\<^sub>n (\<phi> or\<^sub>n (X\<^sub>n (\<phi> V\<^sub>n \<psi>))))" (is "?lhs = ?rhs")
proof
  assume lhs: ?lhs
  hence psi_is: "\<xi> \<Turnstile>\<^sub>n \<psi>" by force

  have "\<And>i. \<lbrakk>\<not> \<xi> \<Turnstile>\<^sub>n \<phi>; \<not> suffix (Suc i) \<xi> \<Turnstile>\<^sub>n \<psi>\<rbrakk>
            \<Longrightarrow> (\<exists>j<i. suffix (Suc j) \<xi> \<Turnstile>\<^sub>n \<phi>)"
  proof -
    fix i
    assume phi_nis: "\<not> \<xi> \<Turnstile>\<^sub>n \<phi>"
       and "\<not> suffix (Suc i) \<xi> \<Turnstile>\<^sub>n \<psi>"
    then obtain j
          where "j<Suc i"
            and "suffix j \<xi> \<Turnstile>\<^sub>n \<phi>" using lhs by auto
    hence "j - 1 < i \<and> suffix (Suc (j - 1)) \<xi> \<Turnstile>\<^sub>n \<phi>"
    using phi_nis by (cases j) auto
    thus "\<exists>j<i. suffix (Suc j) \<xi> \<Turnstile>\<^sub>n \<phi>" by auto
  qed
  thus ?rhs using psi_is by auto
next
  assume rhs: ?rhs
  hence psi_is: "\<xi> \<Turnstile>\<^sub>n \<psi>" by auto

  show ?lhs
  proof(cases "\<xi> \<Turnstile>\<^sub>n \<phi>")
    assume "\<xi> \<Turnstile>\<^sub>n \<phi>"
    thus ?thesis using psi_is by force
  next
    assume phi_nis: "\<not> \<xi> \<Turnstile>\<^sub>n \<phi>"

    hence "\<forall>i. suffix (Suc i) \<xi> \<Turnstile>\<^sub>n \<psi>
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
    thus ?thesis by auto
  qed
qed

lemma ltln_Release_alterdef:
  "\<xi> \<Turnstile>\<^sub>n \<phi> V\<^sub>n \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>n (\<box>\<^sub>n \<psi>) or\<^sub>n (\<psi> U\<^sub>n (\<phi> and\<^sub>n \<psi>))" (is "?lhs = ?rhs")
proof
  assume ?lhs
  { assume "\<not> (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi>)"
    then obtain i where \<psi>_neq: "\<not> suffix i \<xi> \<Turnstile>\<^sub>n \<psi>" by auto
    let ?k = "LEAST i. \<not> suffix i \<xi> \<Turnstile>\<^sub>n \<psi>"
    from \<psi>_neq `?lhs` have "\<forall>j<?k. suffix j \<xi> \<Turnstile>\<^sub>n \<psi>" by (metis not_less_Least)
    moreover
    have "\<not> suffix ?k \<xi> \<Turnstile>\<^sub>n \<psi>" by (rule LeastI, rule \<psi>_neq)
    moreover then obtain j where "j<?k" and "suffix j \<xi> \<Turnstile>\<^sub>n \<phi>" using `?lhs` by auto
    ultimately have "\<xi> \<Turnstile>\<^sub>n \<psi> U\<^sub>n (\<phi> and\<^sub>n \<psi>)" by auto }
  with `?lhs` show ?rhs by auto
next
  assume ?rhs
  { assume "\<not> \<xi> \<Turnstile>\<^sub>n \<box>\<^sub>n \<psi>"
    with `?rhs` obtain i where "suffix i \<xi> \<Turnstile>\<^sub>n \<phi> and\<^sub>n \<psi>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<psi>" by auto
    hence ?lhs by (auto, metis nat_neq_iff) }
  thus ?lhs using `?rhs` by auto
qed


end
end
