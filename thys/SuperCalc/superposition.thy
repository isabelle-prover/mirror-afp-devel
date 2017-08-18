theory superposition

(* N. Peltier - http://membres-lig.imag.fr/peltier/ *)

imports Main terms equational_clausal_logic well_founded_continued "HOL-Library.Multiset"
 multisets_continued 

begin

section {* Definition of the Superposition Calculus *}

subsection {* Extended Clauses *}

text {* An extended clause is a clause associated with a set of terms. 
The intended meaning is that the terms occurring in the attached set are assumed to be in normal 
form: any application of the superposition rule on these terms is therefore useless and can be 
blocked. Initially the set of irreducible terms attached to each clause is empty. At each inference 
step, new terms can be added or deleted from this set. *}

datatype 'a eclause = Ecl "'a clause" "'a trm set"

fun subst_ecl
where 
  "(subst_ecl (Ecl C S) \<sigma>) =   
    (Ecl (subst_cl C \<sigma>) { s. (\<exists>t. (s = (subst t \<sigma>) \<and> t \<in> S)) })"

fun cl_ecl 
where
  "(cl_ecl (Ecl C X)) = C"

fun trms_ecl
where
  "(trms_ecl (Ecl C X)) = X"

definition renaming_cl
  where "renaming_cl C D = (\<exists> \<eta>. (renaming \<eta> (vars_of_cl (cl_ecl C))) \<and> D = (subst_ecl C \<eta>))"

definition closed_under_renaming
  where "closed_under_renaming S = (\<forall>C D. 
    (C \<in> S) \<longrightarrow> (renaming_cl C D) \<longrightarrow> (D \<in> S))"

definition variable_disjoint
where "(variable_disjoint C D) =  ((vars_of_cl (cl_ecl C)) \<inter>  (vars_of_cl (cl_ecl D)) = {})" 

subsection {* Orders and Selection Functions *}

text {* We assume that the set of variables is infinite (so that shared variables can be renamed 
away) and that the following objects are given:

(i) A term ordering that is total on ground terms, well-founded and 
closed under contextual embedding and substitutions. This ordering is used as usual to orient 
equations and to restrict the application of the replacement rule.

(ii) A selection function, mapping each clause to a (possibly empty) set of negative literals. 
We assume that this selection function is closed under renamings.

(iii) A function mapping every extended clause to an order on positions, 
which contains the (reversed) prefix ordering. This order allows one to control the order in which 
the subterms are rewritten (terms occurring at minimal positions are considered with the highest 
priority). 

(iv) A function @{term "filter_trms"} that allows one to filter away some of the terms attached to 
a given extended clause (it can be used for instance to remove terms if the set becomes too big). 
The standard superposition calculus corresponds to the case where this function always returns the 
empty set. *}

locale basic_superposition =

  fixes trm_ord :: "('a trm \<times> 'a trm) set"
  fixes sel :: "'a clause \<Rightarrow> 'a clause"
  fixes pos_ord :: "'a eclause \<Rightarrow> 'a trm \<Rightarrow> (position \<times> position) set"
  fixes vars :: "'a set" 
  fixes filter_trms :: "'a clause \<Rightarrow> 'a trm set \<Rightarrow> 'a trm set" 
  assumes
    trm_ord_wf : "(wf trm_ord)"
    and trm_ord_ground_total : 
      "(\<forall>x y. ((ground_term x) \<longrightarrow> (ground_term y) \<longrightarrow> x \<noteq> y 
        \<longrightarrow> ((x,y) \<in> trm_ord \<or> (y,x) \<in> trm_ord)))"
    and trm_ord_trans : "trans trm_ord"
    and trm_ord_irrefl :  "irrefl trm_ord"
    and trm_ord_reduction_left : "\<forall>x1 x2 y. (x1,x2)  \<in> trm_ord 
      \<longrightarrow> ((Comb x1 y),(Comb x2 y)) \<in> trm_ord"
    and trm_ord_reduction_right : "\<forall>x1 x2 y. (x1,x2)  \<in> trm_ord 
      \<longrightarrow> ((Comb y x1),(Comb y x2)) \<in> trm_ord"
    and trm_ord_subterm : "\<forall>x1 x2. (x1,(Comb x1 x2))  \<in> trm_ord 
      \<and> (x2,(Comb x1 x2)) \<in> trm_ord"
    and trm_ord_subst : 
    "\<forall>s x y. (x,y) \<in> trm_ord \<longrightarrow> ( (subst x s),(subst y s)) \<in> trm_ord"
    and pos_ord_irrefl : "(\<forall>x y. (irrefl (pos_ord x y)))"
    and pos_ord_trans : "(\<forall>x. (trans (pos_ord x y)))"
    and pos_ord_prefix : "\<forall>x y p q r. ((q,p) \<in> (pos_ord x y) \<longrightarrow> ((append q r),p) \<in> (pos_ord x y))"
    and pos_ord_nil : "\<forall>x y p . (p \<noteq> Nil) \<longrightarrow> (p,Nil) \<in> (pos_ord x y)"
    and sel_neg: "(\<forall>x. ( (sel (cl_ecl x)) \<subseteq> (cl_ecl x)) 
        \<and> (\<forall>y \<in> sel (cl_ecl x). (negative_literal y)))"
    and sel_renaming: "\<forall>\<eta> C. ((renaming \<eta> (vars_of_cl C)) \<longrightarrow> sel C = {} \<longrightarrow> sel (subst_cl C \<eta>) = {})"
    and infinite_vars: "\<not> (finite vars)"
    and filter_trms_inclusion: "filter_trms C E \<subseteq> E"
begin

text {* We provide some functions to decompose a literal in a way that is compatible with the 
ordering and establish some basic properties. *}

definition orient_lit :: "'a literal \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> sign \<Rightarrow> bool"
where
  "(orient_lit L u v s) = 
    ((( (L = (Pos (Eq u v))) \<or> (L = (Pos (Eq v u)))) \<and> ((u,v) \<notin> trm_ord) \<and> (s = pos))
    \<or>
    (( (L = (Neg (Eq u v))) \<or> (L = (Neg (Eq v u)))) \<and> ((u,v) \<notin> trm_ord) \<and> (s = neg)))"

definition orient_lit_inst :: "'a literal \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> sign \<Rightarrow> 'a subst \<Rightarrow> bool"
where
  "(orient_lit_inst L u v s \<sigma>) = 
    ((( (L = (Pos (Eq u v))) \<or> (L = (Pos (Eq v u)))) 
      \<and> (((subst u \<sigma>),(subst v \<sigma>)) \<notin> trm_ord) \<and> (s = pos))
    \<or>
    (( (L = (Neg (Eq u v))) \<or> (L = (Neg (Eq v u)))) \<and> (((subst u \<sigma>),(subst v \<sigma>)) 
    \<notin> trm_ord) \<and> (s = neg)))"

lemma lift_orient_lit: 
  assumes "orient_lit_inst L t s p \<sigma>"
  shows "orient_lit (subst_lit L \<sigma>) (subst t \<sigma>)  (subst s \<sigma>) p"
unfolding orient_lit_inst_def orient_lit_def using assms orient_lit_inst_def by auto 

lemma orient_lit_vars:
  assumes "orient_lit L t s p"
  shows "vars_of t \<subseteq> vars_of_lit L \<and> vars_of s \<subseteq> vars_of_lit L"
proof -
  have "p = neg \<or> p = pos" using sign.exhaust by auto
  then show ?thesis
  proof
    assume "p = neg" 
    from this and assms(1) have "(L = Neg (Eq t s)) \<or> (L = (Neg (Eq s t)))" 
      unfolding orient_lit_def by auto
    then show ?thesis
    proof
      assume "L = Neg (Eq t s)" 
      then have "vars_of_lit L = vars_of t \<union> vars_of s" by simp
      from this show ?thesis by simp 
    next
      assume "L = Neg (Eq s t)" 
      then have "vars_of_lit L = vars_of s \<union> vars_of t" by simp
      from this show ?thesis by simp 
    qed
    next assume "p = pos" 
    from this and assms(1) have "(L = Pos (Eq t s)) \<or> (L = (Pos (Eq s t)))" 
      unfolding orient_lit_def by auto
    then show ?thesis
    proof
      assume "L = Pos (Eq t s)" 
      then have "vars_of_lit L = vars_of t \<union> vars_of s" by simp
      from this show ?thesis by simp 
    next
      assume "L = Pos (Eq s t)" 
      then have "vars_of_lit L = vars_of s \<union> vars_of t" by simp
      from this show ?thesis by simp 
    qed
  qed
qed

lemma orient_lit_inst_vars:
  assumes "orient_lit_inst L t s p \<sigma>"
  shows "vars_of t \<subseteq> vars_of_lit L \<and> vars_of s \<subseteq> vars_of_lit L"
proof -
  have "p = neg \<or> p = pos" using sign.exhaust by auto
  then show ?thesis
  proof
    assume "p = neg" 
    from this and assms(1) have "(L = Neg (Eq t s)) \<or> (L = (Neg (Eq s t)))" 
      unfolding orient_lit_inst_def by auto
    then show ?thesis
    proof
      assume "L = Neg (Eq t s)" 
      then have "vars_of_lit L = vars_of t \<union> vars_of s" by simp
      from this show ?thesis by simp 
    next
      assume "L = Neg (Eq s t)" 
      then have "vars_of_lit L = vars_of s \<union> vars_of t" by simp
      from this show ?thesis by simp 
    qed
    next assume "p = pos" 
    from this and assms(1) have "(L = Pos (Eq t s)) \<or> (L = (Pos (Eq s t)))" 
      unfolding orient_lit_inst_def by auto
    then show ?thesis
    proof
      assume "L = Pos (Eq t s)" 
      then have "vars_of_lit L = vars_of t \<union> vars_of s" by simp
      from this show ?thesis by simp 
    next
      assume "L = Pos (Eq s t)" 
      then have "vars_of_lit L = vars_of s \<union> vars_of t" by simp
      from this show ?thesis by simp 
    qed
  qed
qed

lemma orient_lit_inst_coincide:
  assumes "orient_lit_inst L1 t s polarity \<sigma>"
  assumes "coincide_on \<sigma> \<eta> (vars_of_lit L1)"
  shows "orient_lit_inst L1 t s polarity \<eta>"
proof -
  have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto  
  then show ?thesis
  proof
    assume "polarity = pos" 
    from this and assms(1) have "L1 = Pos (Eq t s) \<or> L1 = Pos (Eq s t)" 
      and "( (subst t \<sigma>),  (subst s \<sigma>)) \<notin> trm_ord"  
      unfolding orient_lit_inst_def by auto
    from `L1 = Pos (Eq t s) \<or> L1 = Pos (Eq s t)` 
      have "vars_of t \<subseteq> vars_of_lit L1" and "vars_of s \<subseteq> vars_of_lit L1" by auto
    from `vars_of t \<subseteq> vars_of_lit L1` and assms(2) have "coincide_on \<sigma> \<eta> (vars_of t)" 
      unfolding coincide_on_def by auto
    from `vars_of s \<subseteq> vars_of_lit L1` and assms(2) have "coincide_on \<sigma> \<eta> (vars_of s)" 
      unfolding coincide_on_def by auto
    from `( (subst t \<sigma>),  (subst s \<sigma>)) \<notin> trm_ord`
      and `coincide_on \<sigma> \<eta> (vars_of t)` and `coincide_on \<sigma> \<eta> (vars_of s)` assms(2) 
    have "( (subst t \<eta>),  (subst s \<eta>)) \<notin> trm_ord"
      using coincide_on_term by metis
    from this and `polarity = pos` and `L1 = Pos (Eq t s) \<or> L1 = Pos (Eq s t)` show ?thesis 
      unfolding orient_lit_inst_def by auto
    next assume "polarity = neg" 
    from this and assms(1) have "L1 = Neg (Eq t s) \<or> L1 = Neg (Eq s t)" 
      and "( (subst t \<sigma>),  (subst s \<sigma>)) \<notin> trm_ord"  
      unfolding orient_lit_inst_def by auto
    from `L1 = Neg (Eq t s) \<or> L1 = Neg (Eq s t)` 
      have "vars_of t \<subseteq> vars_of_lit L1" and "vars_of s \<subseteq> vars_of_lit L1" by auto
    from `vars_of t \<subseteq> vars_of_lit L1` and assms(2) have "coincide_on \<sigma> \<eta> (vars_of t)" 
      unfolding coincide_on_def by auto
    from `vars_of s \<subseteq> vars_of_lit L1` and assms(2) have "coincide_on \<sigma> \<eta> (vars_of s)" 
      unfolding coincide_on_def by auto
    from `( (subst t \<sigma>),  (subst s \<sigma>)) \<notin> trm_ord`
      and `coincide_on \<sigma> \<eta> (vars_of t)` and `coincide_on \<sigma> \<eta> (vars_of s)` assms(2) 
    have "( (subst t \<eta>),  (subst s \<eta>)) \<notin> trm_ord"
      using coincide_on_term by metis
    from this and `polarity = neg` and `L1 = Neg (Eq t s) \<or> L1 = Neg (Eq s t)` show ?thesis 
      unfolding orient_lit_inst_def by auto
  qed
qed

lemma orient_lit_inst_subterms:
  assumes "orient_lit_inst L t s polarity \<sigma>"
  assumes "u \<in> subterms_of t"
  shows "u \<in> subterms_of_lit L"
proof -
  have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto
  then show ?thesis
  proof
    assume "polarity = pos" 
    from this and assms(1) have "L = (Pos (Eq t s)) \<or> L = (Pos (Eq s t))" 
      unfolding orient_lit_inst_def by auto
    then show ?thesis
    proof
      assume "L = (Pos (Eq t s))"
      from this and assms(2) show ?thesis  by simp
      next assume "L = (Pos (Eq s t))"
      from this and assms(2) show ?thesis  by simp
    qed
  next
    assume "polarity = neg" 
    from this and assms(1) have "L = (Neg (Eq t s)) \<or> L = (Neg (Eq s t))" 
      unfolding orient_lit_inst_def by auto
    then show ?thesis
    proof
      assume "L = (Neg (Eq t s))"
      from this and assms(2) show ?thesis  by simp
      next assume "L = (Neg (Eq s t))"
      from this and assms(2) show ?thesis  by simp
    qed
  qed  
qed

subsection {* Clause Ordering *}

text {* Clauses and extended clauses are ordered by transforming them into multisets of multisets 
of terms. To avoid any problem with the merging of identical literals, the multiset is assigned 
to a pair clause-substitution rather than to an instantiated clause. *}

text {* We first map every literal to a multiset of terms, using the usual conventions and then 
define the multisets associated with clauses and extended clauses. *}

fun mset_lit :: "'a literal \<Rightarrow> 'a trm multiset"
  where "mset_lit (Pos (Eq t s)) = {# t,s #}" |
        "mset_lit (Neg (Eq t s)) = {# t,t,s,s #}"

fun mset_cl 
   where "mset_cl (C,\<sigma>) = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set C) #}" 

fun mset_ecl 
   where "mset_ecl (C,\<sigma>) = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set (cl_ecl C)) #}" 

lemma mset_ecl_and_mset_lit:
  assumes "L \<in> (cl_ecl C)"
  assumes "finite (cl_ecl C)"
  shows "(mset_lit (subst_lit L \<sigma>)) \<in># (mset_ecl (C,\<sigma>))"
proof -
  from assms(1) assms(2) have "L \<in># (mset_set (cl_ecl C))" by (simp) 
  then show ?thesis
  proof -
  have f1: "mset_set (cl_ecl C) - {#L#} + {#L#} = mset_set (cl_ecl C)"
    by (meson \<open>L \<in># mset_set (cl_ecl C)\<close> insert_DiffM2)
  have "count {#mset_lit (subst_lit L \<sigma>)#} (mset_lit (subst_lit L \<sigma>)) = 1"
    by simp
  then show ?thesis
    by (metis (no_types, lifting) f1 image_mset_add_mset insert_iff mset_ecl.simps set_mset_add_mset_insert union_mset_add_mset_right)
  qed
qed

lemma ecl_ord_coincide:
  assumes "coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))"
  shows "mset_ecl (C,\<sigma>) = mset_ecl (C,\<sigma>')"
proof -
  have "\<forall>x. (x \<in> (cl_ecl C) \<longrightarrow> ((subst_lit x \<sigma>) = (subst_lit x \<sigma>')))"
  proof ((rule allI),(rule impI))
    fix x assume "x \<in> (cl_ecl C)"
    from this have "vars_of_lit x \<subseteq> (vars_of_cl (cl_ecl C))" by auto
    from this and assms(1) have "coincide_on \<sigma> \<sigma>' (vars_of_lit x)" unfolding coincide_on_def by auto
    from this show "((subst_lit x \<sigma>) = (subst_lit x \<sigma>'))"
      by (simp add: coincide_on_lit) 
  qed
  then show ?thesis using equal_image_mset 
  [of  "cl_ecl C" "\<lambda>x. (mset_lit (subst_lit x \<sigma>))"  "\<lambda>x. (mset_lit (subst_lit x \<sigma>'))"]
    by (metis  mset_ecl.simps)
qed

text {* Literal and clause orderings are obtained as usual as the multiset extensions of the term 
ordering. *}

definition lit_ord :: "('a literal \<times> 'a literal) set"
  where 
  "lit_ord =  
    { (x,y). (((mset_lit x),(mset_lit y)) \<in> (mult trm_ord)) }"

lemma mult_trm_ord_trans:
  shows "trans (mult trm_ord)"
by (metis (no_types, lifting)  mult_def transI transitive_closure_trans(2))

lemma lit_ord_trans:
  shows "trans  lit_ord"
by (metis (no_types, lifting) basic_superposition.lit_ord_def basic_superposition_axioms 
    case_prodD case_prodI mem_Collect_eq mult_def transI transitive_closure_trans(2))

lemma lit_ord_wf:
  shows "wf lit_ord"
proof -
    from trm_ord_wf have "wf (mult trm_ord)" using wf_mult by auto
    then show ?thesis 
      using lit_ord_def 
        and measure_wf [of "(mult trm_ord)" lit_ord mset_lit]
        by blast
qed

definition ecl_ord :: "(('a eclause \<times> 'a subst) \<times> ('a eclause \<times> 'a subst)) set"
  where 
  "ecl_ord =  
    { (x,y). (((mset_ecl x),(mset_ecl y)) \<in> (mult (mult trm_ord))) }"

definition ecl_ord_eq :: "(('a eclause \<times> 'a subst) \<times> ('a eclause \<times> 'a subst)) set"
  where 
  "ecl_ord_eq =  
    ecl_ord \<union> { (x,y). ((mset_ecl x) = (mset_ecl y)) }"

definition cl_ord :: "(('a clause \<times> 'a subst) \<times> ('a clause \<times> 'a subst)) set"
  where 
  "cl_ord =  
    { (x,y). (((mset_cl x),(mset_cl  y)) \<in> (mult (mult trm_ord))) }"

definition cl_ord_eq :: "(('a clause \<times> 'a subst) \<times> ('a clause \<times> 'a subst)) set"
  where 
  "cl_ord_eq =  cl_ord \<union> 
    { (x,y). (mset_cl x) = (mset_cl  y) }"

lemma mult_mult_trm_ord_trans:
  shows "trans (mult (mult trm_ord))"
by (metis (no_types, lifting)  mult_def transI transitive_closure_trans(2))

lemma ecl_ord_trans:
  shows "trans  ecl_ord"
by (metis (no_types, lifting) basic_superposition.ecl_ord_def basic_superposition_axioms case_prodD 
    case_prodI mem_Collect_eq mult_def transI transitive_closure_trans(2))

lemma cl_ord_trans:
  shows "trans cl_ord"
by (metis (no_types, lifting) basic_superposition.cl_ord_def basic_superposition_axioms case_prodD 
    case_prodI mem_Collect_eq mult_def transI transitive_closure_trans(2))

lemma cl_ord_eq_trans:
  shows "trans cl_ord_eq"
proof -
  have "\<forall>r. trans r = (\<forall>p pa pb. ((p::'a literal set \<times> ('a \<times> 'a trm) list, pa) \<notin> r \<or> (pa, pb) \<notin> r) 
          \<or> (p, pb) \<in> r)"
    by (simp add: trans_def)
  then obtain pp :: "(('a literal set \<times> ('a \<times> 'a trm) list) \<times> 'a literal set \<times> ('a \<times> 'a trm) list) set \<Rightarrow> 'a literal set \<times> ('a \<times> 'a trm) list" and ppa :: "(('a literal set \<times> ('a \<times> 'a trm) list) \<times> 'a literal set \<times> ('a \<times> 'a trm) list) set \<Rightarrow> 'a literal set \<times> ('a \<times> 'a trm) list" and ppb :: "(('a literal set \<times> ('a \<times> 'a trm) list) \<times> 'a literal set \<times> ('a \<times> 'a trm) list) set \<Rightarrow> 'a literal set \<times> ('a \<times> 'a trm) list" where
    f1: "\<forall>r. (\<not> trans r \<or> (\<forall>p pa pb. (p, pa) \<notin> r \<or> (pa, pb) \<notin> r \<or> (p, pb) \<in> r)) \<and> (trans r \<or> (pp r, ppa r) \<in> r \<and> (ppa r, ppb r) \<in> r \<and> (pp r, ppb r) \<notin> r)"
    by (metis (no_types))
  have f2: "trans {(p, pa). (mset_cl p, mset_cl pa) \<in> mult (mult trm_ord)}"
    using cl_ord_def cl_ord_trans by presburger
  { assume "\<not> (case (ppa (cl_ord \<union> {(p, pa). mset_cl p = mset_cl pa}), ppb (cl_ord \<union> {(p, pa). mset_cl p = mset_cl pa})) of (p, pa) \<Rightarrow> mset_cl p = mset_cl pa)"
    { assume "(ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)}"
      moreover
      { assume "(ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<and> (mset_cl (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})), mset_cl (ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}))) \<notin> mult (mult trm_ord)"
        then have "(ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<and> mset_cl (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<noteq> mset_cl (ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}))"
          by force
        then have "((pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). mset_cl pa = mset_cl p}) \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<and> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> {(pa, p). mset_cl pa = mset_cl p}"
          using f2 f1 by blast }
      ultimately have "(mset_cl (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})), mset_cl (ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}))) \<in> mult (mult trm_ord) \<or> ((pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). mset_cl pa = mset_cl p}) \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<and> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> {(pa, p). mset_cl pa = mset_cl p}"
        by fastforce }
    then have "(mset_cl (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})), mset_cl (ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}))) \<in> mult (mult trm_ord) \<or> ((pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> {(pa, p). mset_cl pa = mset_cl p}) \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> {(pa, p). (mset_cl pa, mset_cl p) \<in> mult (mult trm_ord)} \<and> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> {(pa, p). mset_cl pa = mset_cl p} \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p} \<or> (ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p} \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}"
      using cl_ord_def by auto }
  then have "(pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p} \<or> (ppa (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<notin> cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p} \<or> (pp (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}), ppb (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})) \<in> cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p}"
    using cl_ord_def by force
  then have "trans (cl_ord \<union> {(pa, p). mset_cl pa = mset_cl p})"
    using f1 by meson
  from this show ?thesis unfolding cl_ord_eq_def by auto
qed

lemma wf_ecl_ord:
  shows "wf ecl_ord"
proof -
    have "wf (mult trm_ord)" using trm_ord_wf and wf_mult  by auto
    then have "wf (mult (mult trm_ord))" using wf_mult  by auto
    thus ?thesis 
      using ecl_ord_def 
        and measure_wf [of "(mult (mult trm_ord))" ecl_ord mset_ecl]
        by blast
qed

definition maximal_literal :: "'a literal \<Rightarrow> 'a clause \<Rightarrow> bool"
  where
    "(maximal_literal L C) = (\<forall>x. (x \<in> C \<longrightarrow> (L,x) \<notin> lit_ord))"

definition eligible_literal 
where 
  "(eligible_literal L C \<sigma>) = (L \<in> sel (cl_ecl C) \<or> 
    (sel(cl_ecl C) = {} 
    \<and> (maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>))))"

definition strictly_maximal_literal
where "strictly_maximal_literal C L \<sigma>  = 
  (\<forall>x \<in> (cl_ecl C) - { L }. ( (subst_lit x \<sigma>),(subst_lit L \<sigma>)) 
                                        \<in> lit_ord)"

definition lower_or_eq 
  where "lower_or_eq t s = ((t = s) \<or> ((t,s) \<in> trm_ord))"

lemma eligible_literal_coincide:
  assumes "coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))"
  assumes "eligible_literal L C \<sigma>"
  assumes "L \<in> (cl_ecl C)"
  shows "eligible_literal L C \<sigma>'"
proof -
  from assms(2) have 
    "L \<in> sel (cl_ecl C) \<or> (sel (cl_ecl C) = {} \<and> maximal_literal (subst_lit L \<sigma>) 
      (subst_cl (cl_ecl C) \<sigma>))" 
    unfolding eligible_literal_def by auto
  then show ?thesis
  proof 
    assume "L \<in> sel (cl_ecl C)" 
    then show ?thesis unfolding eligible_literal_def by auto
  next
    assume "sel (cl_ecl C) = {} \<and> maximal_literal (subst_lit L \<sigma>)  (subst_cl (cl_ecl C) \<sigma>)"
    then have "sel (cl_ecl C) = {}" and "maximal_literal (subst_lit L \<sigma>)  (subst_cl (cl_ecl C) \<sigma>)" 
      by auto
    from assms(1) have "(subst_cl (cl_ecl C) \<sigma>) = (subst_cl (cl_ecl C) \<sigma>')"
      using coincide_on_cl by blast
    from assms(3) and assms(1) have "coincide_on \<sigma> \<sigma>' (vars_of_lit L)" unfolding coincide_on_def 
      by auto
    from this have "(subst_lit L \<sigma>) = (subst_lit L \<sigma>')" 
      using coincide_on_lit by auto
    from this and `(subst_cl (cl_ecl C) \<sigma>) = (subst_cl (cl_ecl C) \<sigma>')` 
      and `maximal_literal (subst_lit L \<sigma>)  (subst_cl (cl_ecl C) \<sigma>)`
      have "maximal_literal (subst_lit L \<sigma>')  (subst_cl (cl_ecl C) \<sigma>')"
      by auto
    from this and `sel (cl_ecl C) = {}` show ?thesis unfolding eligible_literal_def by auto
   qed
qed

text {* The next definition extends the ordering to substitutions. *}

definition lower_on 
where "lower_on \<sigma> \<eta> V = (\<forall>x \<in> V. 
  (lower_or_eq (subst (Var x) \<sigma>) ( (subst (Var x) \<eta>))))"

text {* We now establish some properties of the ordering relations. *}

lemma lower_or_eq_monotonic:
  assumes "lower_or_eq t1 s1"
  assumes "lower_or_eq t2 s2"
  shows "lower_or_eq (Comb t1 t2) (Comb s1 s2)"
unfolding lower_or_eq_def using trm_ord_reduction_left trm_ord_reduction_right
  by (metis assms(1) assms(2) lower_or_eq_def trm_ord_trans transD)
 
lemma lower_on_term:
  shows "\<And> \<sigma> \<eta>. lower_on \<sigma> \<eta> (vars_of t) \<Longrightarrow> 
    (lower_or_eq (subst t \<sigma>) (subst t \<eta>))"
proof (induction t)
  case (Var x)
    from this show ?case 
      unfolding lower_on_def by auto
  next case (Const x)
    show ?case 
     unfolding lower_or_eq_def by auto
  next case (Comb t1 t2)
    show "\<And> \<sigma> \<eta>. lower_on \<sigma> \<eta> (vars_of (Comb t1 t2)) \<Longrightarrow> 
    (lower_or_eq (subst  (Comb t1 t2) \<sigma>) (subst  (Comb t1 t2) \<eta>))"
    proof -
      fix \<sigma> \<eta> assume "lower_on \<sigma> \<eta> (vars_of (Comb t1 t2))"
      from this have "lower_on \<sigma> \<eta> (vars_of t1)" and "lower_on \<sigma> \<eta> (vars_of t2)" 
        unfolding lower_on_def by auto
      from `lower_on \<sigma> \<eta> (vars_of t1)` have "lower_or_eq (subst t1 \<sigma>) (subst t1 \<eta>)" 
        using Comb.IH by auto
      from `lower_on \<sigma> \<eta> (vars_of t2)` have "lower_or_eq (subst t2 \<sigma>) (subst t2 \<eta>)" 
        using Comb.IH by auto
      from `lower_or_eq (subst t1 \<sigma>) (subst t1 \<eta>)` `lower_or_eq (subst t2 \<sigma>) (subst t2 \<eta>)`
        show "lower_or_eq (subst  (Comb t1 t2) \<sigma>) (subst (Comb t1 t2) \<eta>)"
        using lower_or_eq_monotonic by auto 
    qed   
qed

lemma diff_substs_yield_diff_trms:
  assumes "(subst (Var x) \<sigma>) \<noteq> (subst (Var x) \<eta>)"
  shows "(x \<in> vars_of t)
   \<Longrightarrow> (subst t \<sigma>) \<noteq> (subst t \<eta>)"
proof (induction t)
  case (Var y)  
    show "(x \<in> vars_of (Var y))  \<Longrightarrow> (subst  (Var y) \<sigma>) \<noteq> (subst  (Var y) \<eta>)"
    proof -
      assume "(x \<in> vars_of  (Var y))" 
      from `(x \<in> vars_of  (Var y))` have "x = y" by auto
      from this and assms(1)  
      show "(subst  (Var y) \<sigma>) \<noteq> (subst  (Var y) \<eta>)" 
      by auto
    qed
  next case (Const y)
    show " (x \<in> vars_of (Const y))
   \<Longrightarrow> (subst  (Const y) \<sigma>) \<noteq> (subst  (Const y) \<eta>)"
    proof (rule ccontr)
      from `(x \<in> vars_of  (Const y))` show False by auto
    qed
  next case (Comb t1 t2)
    show " (x \<in> vars_of (Comb t1 t2))
   \<Longrightarrow> (subst  (Comb t1 t2) \<sigma>) \<noteq> (subst (Comb t1 t2) \<eta>)"
    proof -
      assume "(x \<in> vars_of (Comb t1 t2))" 
      from `x \<in> vars_of (Comb t1 t2)` have "x \<in> vars_of t1 \<or> x \<in> vars_of t2" by auto
      then show "(subst  (Comb t1 t2) \<sigma>) \<noteq> (subst (Comb t1 t2) \<eta>)"
      proof 
        assume "x \<in> vars_of t1"
        from this have "(subst t1 \<sigma>) \<noteq> (subst t1 \<eta>)" 
          using Comb.IH by auto
        then show ?thesis by auto
      next
        assume "x \<in> vars_of t2"
        from this have "(subst t2 \<sigma>) \<noteq> (subst t2 \<eta>)" 
          using Comb.IH by auto
        then show ?thesis by auto
      qed
    qed   
qed

lemma lower_subst_yields_lower_trms:
  assumes "lower_on \<sigma> \<eta> (vars_of t)"
  assumes "((subst (Var x) \<sigma>),(subst (Var x) \<eta>)) \<in> trm_ord"
  assumes "(x \<in> vars_of t)"
  shows "((subst t \<sigma>),(subst t \<eta>)) \<in> trm_ord"
proof -
  from assms(1) have "lower_or_eq (subst t \<sigma>) (subst t \<eta>)"
    using lower_on_term by auto
  from assms(2) have "(subst (Var x) \<sigma>) \<noteq> (subst (Var x) \<eta>)"
    using trm_ord_irrefl irrefl_def by fastforce 
  from this and assms(3) have "(subst t \<sigma>) \<noteq> (subst t \<eta>)"
    using diff_substs_yield_diff_trms by fastforce 
  from this and `lower_or_eq (subst t \<sigma>) (subst t \<eta>)` 
    show ?thesis unfolding lower_or_eq_def by auto
qed

lemma lower_on_lit:
  assumes "lower_on \<sigma> \<eta> (vars_of_lit L)"
  assumes "((subst (Var x) \<sigma>),(subst (Var x) \<eta>)) \<in> trm_ord"
  assumes "x \<in> vars_of_lit L"
  shows "((subst_lit L \<sigma>), (subst_lit L \<eta>)) \<in> lit_ord"
proof -
  obtain t s where def_l: "L = Pos (Eq t s) | L = (Neg (Eq t s))"
    by (metis mset_lit.cases) 
  from this have "vars_of t \<subseteq> vars_of_lit L" and "vars_of s \<subseteq> vars_of_lit L" by auto
  from `vars_of s \<subseteq> vars_of_lit L` and assms(1) have "lower_on \<sigma> \<eta> (vars_of s)" 
    unfolding lower_on_def by auto
  from def_l have def_ms_l: "mset_lit L = {# t,s #} \<or> mset_lit L = {# t,t,s,s #}" by auto
  from this have "t \<in># (mset_lit L)" and "s \<in># (mset_lit L)" by auto
  from def_l  have "mset_lit (subst_lit L \<sigma>) = {# (subst u \<sigma>). u \<in># (mset_lit L) #}" by auto
  from def_l have "mset_lit (subst_lit L \<eta>) = {# (subst u \<eta>). u \<in># (mset_lit L) #}" by auto
  from `lower_on \<sigma> \<eta> (vars_of s)` have "lower_or_eq (subst s \<sigma>) (subst s \<eta>)" 
    using lower_on_term by auto
  let ?L = "mset_lit L"
  let ?M1 = "mset_lit (subst_lit L \<sigma>)"
  let ?M2 = "mset_lit (subst_lit L \<eta>)"
  from `vars_of t \<subseteq> vars_of_lit L` and assms(1) have "lower_on \<sigma> \<eta> (vars_of t)" 
    unfolding lower_on_def by auto
  from `vars_of s \<subseteq> vars_of_lit L` and assms(1) have "lower_on \<sigma> \<eta> (vars_of s)" 
    unfolding lower_on_def by auto 
  have all_lower: "\<forall>u. (u \<in># (mset_lit L) \<longrightarrow> (((subst  u \<sigma>), (subst u \<eta>)) \<in> trm_ord 
  \<or> (subst  u \<sigma>) = (subst u \<eta>)))"
  proof  (rule allI,rule impI)
    fix u assume "u \<in># (mset_lit L)"
    have "u = t \<or> u = s"
    proof (cases)
      assume "mset_lit L = {# t,s #}"
      from this and `u \<in># (mset_lit L)` show ?thesis
        by (simp add: count_single insert_DiffM2 insert_noteq_member not_gr0)
      next
      assume "\<not>mset_lit L = {# t,s #}"
      from this and def_ms_l have "mset_lit L = {# t,t,s,s #}"
        by auto
      from this and `u \<in># (mset_lit L)` show ?thesis
        using not_gr0 by fastforce
    qed   
    then show "(((subst  u \<sigma>), (subst u \<eta>)) \<in> trm_ord 
  \<or> (subst  u \<sigma>) = (subst u \<eta>))"
    proof 
      assume "u = t"
      from `lower_on \<sigma> \<eta> (vars_of t)` have "lower_or_eq (subst t \<sigma>) (subst t \<eta>)" 
        using lower_on_term by auto
      from this show ?thesis unfolding lower_or_eq_def using \<open>u = t\<close> by auto 
    next
      assume "u = s"
      from `lower_on \<sigma> \<eta> (vars_of s)` have "lower_or_eq (subst s \<sigma>) (subst s \<eta>)" 
        using lower_on_term by auto
      from this show ?thesis unfolding lower_or_eq_def using \<open>u = s\<close> by auto 
    qed
  qed
  have sl_exists: "\<exists>u. (u \<in># (mset_lit L) \<and> ((subst u \<sigma>), (subst u \<eta>)) \<in> trm_ord)"
  proof -
    from `x \<in> vars_of_lit L` and def_l have 
      "x \<in> vars_of t \<or> x \<in> vars_of s" by auto
    then show ?thesis
    proof
      assume "x \<in> vars_of t"
      from this and `lower_on \<sigma> \<eta> (vars_of t)` assms(1) assms(2) 
        have "( (subst t \<sigma>),(subst t \<eta>)) \<in> trm_ord" 
        using lower_subst_yields_lower_trms by auto
      from this and `t \<in># (mset_lit L)` show ?thesis by auto
    next
      assume "x \<in> vars_of s"
      from this and `lower_on \<sigma> \<eta> (vars_of s)` assms(1) assms(2) 
        have "( (subst s \<sigma>),(subst s \<eta>)) \<in> trm_ord" 
        using lower_subst_yields_lower_trms by auto
      from this and `s \<in># (mset_lit L)` show ?thesis by auto
    qed
  qed
  from all_lower sl_exists and 
  `mset_lit (subst_lit L \<sigma>) = {# (subst u \<sigma>). u \<in># (mset_lit L) #}` 
  `mset_lit (subst_lit L \<eta>) = {# (subst u \<eta>). u \<in># (mset_lit L) #}`
  have "(?M1,?M2) \<in> (mult trm_ord)" 
  using trm_ord_irrefl image_mset_ordering 
                        [of ?M1 "\<lambda>x. (subst x \<sigma>)" ?L ?M2 "\<lambda>x. (subst x \<eta>)" trm_ord]
  by blast
  from this show ?thesis unfolding lit_ord_def by auto  
qed

lemma lower_on_lit_eq:
  assumes "lower_on \<sigma> \<eta> (vars_of_lit L)"
  shows "((subst_lit L \<sigma>) = (subst_lit L \<eta>)) \<or> ((subst_lit L \<sigma>), (subst_lit L \<eta>)) \<in> lit_ord"
proof (cases)
  assume "coincide_on \<sigma> \<eta> (vars_of_lit L)"
  then show ?thesis using coincide_on_lit by auto
next
  assume "\<not>coincide_on \<sigma> \<eta> (vars_of_lit L)"
  then obtain x where "x \<in> vars_of_lit L" 
    and "(subst (Var x) \<sigma>) \<noteq> (subst (Var x) \<eta>)"
    unfolding coincide_on_def by auto
  from `x \<in> vars_of_lit L` assms(1) 
  `(subst (Var x) \<sigma>) \<noteq> (subst (Var x) \<eta>)`and assms(1)
    have "((subst (Var x) \<sigma>),(subst (Var x) \<eta>)) \<in> trm_ord"
    unfolding lower_on_def lower_or_eq_def  by auto
  from this assms(1) `x \<in> vars_of_lit L` show ?thesis using lower_on_lit by auto
qed

lemma lower_on_cl:
  assumes "lower_on \<sigma> \<eta> (vars_of_cl (cl_ecl C))"
  assumes "((subst (Var x) \<sigma>),(subst (Var x) \<eta>)) \<in> trm_ord"
  assumes "x \<in> vars_of_cl (cl_ecl C)"
  assumes "finite (cl_ecl C)"
  shows "((C,\<sigma>), (C, \<eta>)) \<in> ecl_ord"
proof -
  let ?M1 = "mset_ecl (C,\<sigma>)"
  let ?M2 = "mset_ecl (C,\<eta>)"
  let ?M = "(mset_set (cl_ecl C))" 
  let ?f1 = "\<lambda>x. (mset_lit (subst_lit x \<sigma>))"
  let ?f2 = "\<lambda>x. (mset_lit (subst_lit x \<eta>))"
  have "?M1 = {# (?f1 u). u \<in># ?M #}" using mset_ecl.simps by blast 
  have "?M2 = {# (?f2 u). u \<in># ?M #}" using mset_ecl.simps by blast 
  have i: "\<forall>u. (u \<in># ?M \<longrightarrow> (((?f1 u), (?f2 u)) \<in> (mult trm_ord) \<or> (?f1 u) = (?f2 u)))"
  proof ((rule allI),(rule impI))
    fix u assume "u \<in># ?M"
    from this have "u \<in> (cl_ecl C)" using count_mset_set(3) by (simp add: assms(4))
    from this and assms(1)  have "lower_on \<sigma> \<eta> (vars_of_lit u)" unfolding lower_on_def by auto
    then have "((subst_lit u \<sigma>) = (subst_lit u \<eta>)) 
      \<or> ((subst_lit u \<sigma>), (subst_lit u \<eta>)) \<in> lit_ord" 
      using lower_on_lit_eq by blast
    from this show "(((?f1 u), (?f2 u)) \<in> (mult trm_ord) \<or> (?f1 u) = (?f2 u))"
      unfolding lit_ord_def by auto
  qed
  have "irrefl (mult trm_ord)" by (simp add: irreflI trm_ord_wf wf_mult) 
  have ii: "\<exists>u. (u \<in># ?M \<and> ((?f1 u), (?f2 u)) \<in> (mult trm_ord))"
  proof -
    from `x \<in> vars_of_cl (cl_ecl C)` obtain u where "u \<in> (cl_ecl C)" and "x \<in> vars_of_lit u" 
      by auto
    from assms(4) `u \<in> (cl_ecl C)` have "u \<in># ?M"  by auto
    from `u \<in> (cl_ecl C)` and assms(1)  have "lower_on \<sigma> \<eta> (vars_of_lit u)" 
      unfolding lower_on_def by auto
    from `x \<in> vars_of_lit u` `lower_on \<sigma> \<eta> (vars_of_lit u)` assms(2) 
      have "((subst_lit u \<sigma>), (subst_lit u \<eta>)) \<in> lit_ord" 
      using lower_on_lit by blast
    from this `u \<in># ?M` have "(u \<in># ?M \<and> ((?f1 u), (?f2 u)) \<in> (mult trm_ord))" 
      unfolding lit_ord_def by auto 
    then show ?thesis by auto
  qed
  from i ii  `?M1 = {# (?f1 u). u \<in># ?M #}` `?M2 = {# (?f2 u). u \<in># ?M #}` `irrefl (mult trm_ord)`
    have "(?M1,?M2) \<in> (mult (mult trm_ord))" 
    using image_mset_ordering [of ?M1 ?f1 ?M ?M2 ?f2 "(mult trm_ord)" ] by auto
  then show ?thesis unfolding ecl_ord_def by auto
qed

lemma subterm_trm_ord :
  shows "\<And> t  s. 
           subterm t p s \<Longrightarrow> p \<noteq> []  
          \<Longrightarrow> (s,t) \<in> trm_ord"
proof (induction p)
  case Nil
    from `Nil \<noteq> []` show ?case by auto
  next case (Cons i q)
    from `subterm t (i # q) s` obtain t1 t2 where
        "t = (Comb t1 t2)" using subterm.elims(2) by blast 
    have "i = Left \<or> i = Right" using indices.exhaust by blast 
    then show "(s,t) \<in> trm_ord"
    proof 
      assume "i = Left"
      from this and `t = Comb t1 t2` and `subterm t (i # q) s`  
        have "subterm t1 q s" by auto
      show ?thesis
      proof (cases)
        assume "q = Nil"
        from this and `subterm t1 q s` have "t1 = s" by auto
        from this and  `t = Comb t1 t2` show ?case using trm_ord_subterm by auto
      next
        assume "q \<noteq> Nil"
        from this and `subterm t1 q s` have "(s,t1) \<in> trm_ord" using Cons.IH by auto
        from `t = Comb t1 t2` have "(t1,t) \<in> trm_ord" using trm_ord_subterm by auto
        from this and `(s,t1) \<in> trm_ord` show ?case 
          using trm_ord_trans unfolding trans_def by metis
      qed
    next
      assume "i = Right"
      from this and `t = Comb t1 t2` and `subterm t (i # q) s`  
        have "subterm t2 q s" by auto
      show ?thesis
      proof (cases)
        assume "q = Nil"
        from this and `subterm t2 q s` have "t2 = s" by auto
        from this and  `t = Comb t1 t2` show ?case using trm_ord_subterm by auto
      next
        assume "q \<noteq> Nil"
        from this and `subterm t2 q s` have "(s,t2) \<in> trm_ord" using Cons.IH by auto
        from `t = Comb t1 t2` have "(t2,t) \<in> trm_ord" using trm_ord_subterm by auto
        from this and `(s,t2) \<in> trm_ord` show ?case 
          using trm_ord_trans unfolding trans_def by metis
      qed
  qed
qed

lemma subterm_trm_ord_eq :
  assumes "subterm t p s" 
  shows "s = t \<or> (s,t) \<in> trm_ord"
proof (cases)
  assume "p = Nil"
    from this and assms(1) show ?thesis by auto
  next assume "p \<noteq> Nil"
    from this and assms(1) show ?thesis using subterm_trm_ord by auto
qed

lemma subterms_of_trm_ord_eq :
  assumes "s \<in> subterms_of t" 
  shows "s = t \<or> (s,t) \<in> trm_ord"
proof -
  from assms(1) obtain p where "subterm t p s" using occurs_in_def by auto
  from this show ?thesis using subterm_trm_ord_eq by auto
qed

lemma subt_trm_ord:
  shows "t \<prec> s \<longrightarrow> (t,s) \<in> trm_ord"
proof (induction s)
    case (Var x)
    show ?case
    proof
      assume "t \<prec> Var x" 
      then show "(t,Var x) \<in> trm_ord" by auto
    qed
    case (Const x)
    show ?case
    proof
      assume "t \<prec> Const x" 
      then show "(t,Const x) \<in> trm_ord" by auto
    qed
    case (Comb t1 t2) 
     show ?case
    proof 
      assume "t \<prec> Comb t1 t2"
      show "(t, Comb t1 t2) \<in> trm_ord"
      proof (rule ccontr)
        assume "(t, Comb t1 t2) \<notin> trm_ord"
        then have i: "t \<noteq> t1" using trm_ord_subterm by auto
        from `(t, Comb t1 t2) \<notin> trm_ord` have ii: "t \<noteq> t2" using trm_ord_subterm by auto
        from i ii and `t \<prec> Comb t1 t2` have "t \<prec> t1 \<or> t \<prec> t2" by auto
        from this and `(t, Comb t1 t2) \<notin> trm_ord`
          show False using Comb.IH trm_ord_subterm trm_ord_trans trans_def by metis
      qed
    qed
qed

lemma trm_ord_vars:
  assumes "(t,s) \<in> trm_ord"
  shows "vars_of t \<subseteq> vars_of s"
proof (rule ccontr)
  assume "\<not>vars_of t \<subseteq> vars_of s"
  then obtain x where "x \<in> vars_of t" and "x \<notin> vars_of s" by auto
  let ?\<sigma> = "[(x,s)]"
  from assms have "((subst t ?\<sigma>),(subst s ?\<sigma>)) \<in> trm_ord" 
    using trm_ord_subst by auto
  let ?\<theta> = "[]"
  let ?V = "vars_of s"
  have "subst s ?\<theta> = s" by simp 
  have "subst (Var x) ?\<sigma> = s" by simp 
  have "coincide_on ?\<sigma> ?\<theta> ?V" 
  proof (rule ccontr)
    assume "\<not> coincide_on ?\<sigma> ?\<theta> ?V"
    then obtain y where "y \<in> ?V" "subst (Var y) ?\<sigma> \<noteq> subst (Var y) ?\<theta>" 
      unfolding coincide_on_def by auto
    from `subst (Var y) ?\<sigma> \<noteq> subst (Var y) ?\<theta>` have "y = x"
      by (metis assoc.simps(2) subst.simps(1)) 
    from this and `x \<notin> vars_of s` `y \<in> ?V` show False by auto
  qed
  from this and `subst s ?\<theta> = s` have "subst s ?\<sigma> = s" 
    using coincide_on_term by metis 
  from `x \<in> vars_of t` have "(Var x) \<prec> t"
    using `(subst t [(x, s)], subst s [(x, s)]) \<in> trm_ord` 
      `subst s [(x, s)] = s` trm_ord_wf vars_iff_occseq by fastforce  
  from this have "((Var x), t) \<in> trm_ord"  using subt_trm_ord by auto
  from this and assms(1) have "(Var x,s) \<in>trm_ord" using trm_ord_trans trans_def by metis
  from this have "((subst (Var x) ?\<sigma>),(subst s ?\<sigma>)) \<in> trm_ord" 
    using trm_ord_subst by metis
  from this and `subst s ?\<sigma> = s` `subst (Var x) ?\<sigma> = s` 
    have "(s,s) \<in> trm_ord" by auto
  from this show False using trm_ord_irrefl irrefl_def by metis
qed

lemma lower_on_ground:
  assumes "lower_on \<sigma> \<eta> V"
  assumes "ground_on  V \<eta>"
  shows "ground_on  V \<sigma>"
proof (rule ccontr)
  assume "\<not> ground_on V \<sigma>"
  from this obtain x where "x \<in> V" and "vars_of (subst (Var x) \<sigma>) \<noteq> {}" 
    unfolding ground_on_def ground_term_def by metis
  from assms(1) `x \<in> V` have "(subst (Var x) \<sigma>) = (subst (Var x) \<eta>)
    \<or> ((subst (Var x) \<sigma>),(subst (Var x) \<eta>)) \<in> trm_ord"
    unfolding lower_on_def lower_or_eq_def by metis
  from this have "vars_of (subst (Var x) \<sigma>) \<subseteq> vars_of (subst (Var x) \<eta>)"
    using trm_ord_vars by auto
  from this and `vars_of (subst (Var x) \<sigma>) \<noteq> {}` 
    have "vars_of (subst (Var x) \<eta>) \<noteq> {}" by auto
  from this and `x \<in> V` and assms(2) show False 
    unfolding ground_on_def ground_term_def by metis
qed
      
lemma replacement_monotonic :
  shows "\<And> t  s. ((subst v \<sigma>), (subst u \<sigma>)) \<in> trm_ord 
          \<Longrightarrow> subterm t p u \<Longrightarrow> replace_subterm t p v s 
          \<Longrightarrow> ((subst s \<sigma>), (subst t \<sigma>)) \<in> trm_ord"
proof (induction p)
  case Nil
    from `subterm t Nil u` have "t = u" by auto 
    from `replace_subterm t Nil v s` have "s = v" by auto
    from `t = u` and `s = v` and `((subst v \<sigma>), (subst u \<sigma>)) \<in> trm_ord` 
      show ?case by auto
  next case (Cons i q)
    from `subterm t (i # q) u` obtain t1 t2 where
        "t = (Comb t1 t2)" using subterm.elims(2) by blast 
    have "i = Left \<or> i = Right" using indices.exhaust by blast 
    then show "((subst s \<sigma>), (subst t \<sigma>)) \<in> trm_ord"
    proof 
      assume "i = Left"
      from this and `t = Comb t1 t2` and `subterm t (i # q) u`  
        have "subterm t1 q u" by auto
      from `i = Left` and `t = Comb t1 t2` and `replace_subterm t (i # q) v s`  
        obtain t1' where "replace_subterm t1 q v t1'" and "s = Comb t1' t2" by auto
      from  `((subst v \<sigma>), (subst u \<sigma>)) \<in> trm_ord` 
        and `subterm t1 q u` and `replace_subterm t1 q v t1'` have 
        "((subst t1' \<sigma>), (subst t1 \<sigma>)) \<in> trm_ord" 
        using Cons.IH Cons.prems(1) by blast 
      from this  and `t = (Comb t1 t2)` and `s = (Comb t1' t2)` 
        show "((subst s \<sigma>), (subst t \<sigma>)) \<in> trm_ord"
        by (simp add: trm_ord_reduction_left)   
    next 
      assume "i = Right"
      from this and `t = Comb t1 t2` and `subterm t (i # q) u`  
        have "subterm t2 q u" by auto
      from `i = Right` and `t = Comb t1 t2` and `replace_subterm t (i # q) v s`  
        obtain t2' where "replace_subterm t2 q v t2'" and "s = Comb t1 t2'" by auto
      from  `((subst v \<sigma>), (subst u \<sigma>)) \<in> trm_ord` 
        and `subterm t2 q u` and `replace_subterm t2 q v t2'` have 
        "((subst t2' \<sigma>), (subst t2 \<sigma>)) \<in> trm_ord" 
        using Cons.IH Cons.prems(2) by blast 
      from this and `t = (Comb t1 t2)` and `s = (Comb t1 t2')` 
        show "((subst s \<sigma>), (subst t \<sigma>)) \<in> trm_ord"
        by (simp add: trm_ord_reduction_right) 
    qed
qed

lemma mset_lit_subst:
  shows "(mset_lit (subst_lit L \<sigma>)) = 
    {# (subst x \<sigma>). x \<in># (mset_lit L) #}"
proof -
  have "positive_literal L \<or> negative_literal L"  
    using negative_literal.simps(2) positive_literal.elims(3) by blast  
  then show ?thesis
  proof 
    assume "positive_literal L"
    then obtain t s where "L = Pos (Eq t s)"
      by (metis equation.exhaust positive_literal.elims(2)) 
    from this show ?thesis by auto
  next
    assume "negative_literal L"
    then obtain t s where "L = Neg (Eq t s)"
      by (metis equation.exhaust negative_literal.elims(2)) 
    from this show ?thesis by auto
  qed
qed

lemma lit_ord_irrefl:
  shows "(L,L) \<notin> lit_ord"
by (simp add: lit_ord_wf)

lemma lit_ord_subst:
  assumes "(L,M) \<in> lit_ord"
  shows "((subst_lit L \<sigma>), (subst_lit M \<sigma>)) \<in> lit_ord"
proof -
  let ?f = "\<lambda>x. (subst x \<sigma>)"
  have i: "\<And> t s. ((t,s) \<in> trm_ord \<Longrightarrow> ((?f t), (?f s)) \<in> trm_ord)"
    using trm_ord_subst by auto
  from assms(1) have ii: "( (mset_lit L),(mset_lit M)) \<in> (mult trm_ord)" 
    unfolding lit_ord_def by auto
  let ?L = "{# (?f x). x \<in># (mset_lit L) #}"
  let ?M = "{# (?f x). x \<in># (mset_lit M) #}"
  from i and ii have iii: "( ?L,?M ) \<in> (mult trm_ord)" using monotonic_fun_mult by metis
  have l: "?L = (mset_lit (subst_lit L \<sigma>))"
    using mset_lit_subst by auto
  have m: "?M = (mset_lit (subst_lit M \<sigma>))"
    using mset_lit_subst by auto
  from l m iii show ?thesis unfolding lit_ord_def by auto
qed

lemma args_are_strictly_lower:
   assumes "is_compound t"
   shows "(lhs t,t) \<in> trm_ord \<and> (rhs t,t) \<in> trm_ord"
by (metis assms is_compound.elims(2) lhs.simps(1) rhs.simps(1) trm_ord_subterm)

lemma mset_subst:
  assumes "C' = subst_cl D \<theta>" 
  assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
  assumes "finite D"
  shows "mset_cl (C',\<eta>) = mset_cl (D,\<sigma>) \<or> (mset_cl (C',\<eta>),mset_cl (D,\<sigma>)) \<in> (mult (mult trm_ord))"
proof -
  let ?f = "\<lambda>x. (subst_lit x \<theta>)"
  let ?g = "\<lambda>x. (mset_lit (subst_lit x \<eta>))"
  let ?h = "\<lambda>x. (mset_lit (subst_lit x \<sigma>))"
  have i: "\<forall>x \<in> D. ( (?g (?f x)) = (?h x))"
  proof 
    fix x
    have "(subst_lit (subst_lit x \<theta>) \<eta>) = (subst_lit x (\<theta> \<lozenge> \<eta>))"
      using composition_of_substs_lit by auto
    from assms(2) have "(subst_lit x  \<sigma>) = (subst_lit x (\<theta> \<lozenge> \<eta>))" 
      using subst_eq_lit by auto
    from this `(subst_lit (subst_lit x \<theta>) \<eta>) = (subst_lit x (\<theta> \<lozenge> \<eta>))`
      show "(?g (?f x)) = (?h x)" by auto
  qed
  from assms(3) have "mset_set (?f ` D) \<subseteq>#  {# (?f x). x \<in># mset_set (D) #}"
    using mset_set_mset_image by auto
  from this have ii: "{# (?g x). x \<in># mset_set (?f ` D) #} \<subseteq>#  {# (?g x). x \<in># {# (?f x). x \<in># mset_set (D) #} #}"
    using image_mset_subseteq_mono by auto
  have "{# (?g x). x \<in># {# (?f x). x \<in># mset_set (D) #} #} = {# (?g (?f x)). x \<in># mset_set D #}"
    using mset_image_comp [of ?g ?f ]  by auto
  from this and ii have
    iii: "{# (?g x). x \<in># mset_set (?f ` D) #} \<subseteq># {# (?g (?f x)). x \<in># mset_set D #}" by auto
  from i have "{# (?g (?f x)). x \<in># (mset_set D) #} = {# (?h x). x \<in># (mset_set D)  #} "
    using equal_image_mset [of D "\<lambda>x. (?g (?f x))"] by auto
  from this and iii 
    have "{# (?g x). x \<in># mset_set (?f ` D) #} \<subseteq># {# (?h x). x \<in># mset_set D #}" by auto
  from this 
    have iv: "{# (?g x). x \<in># mset_set (?f ` D) #} \<subseteq># mset_cl (D,\<sigma>)" by auto
  from assms(1) have "((\<lambda>x. subst_lit x \<theta>) ` D) = C'" by auto
  from this and iv have "{#mset_lit (subst_lit x \<eta>). x \<in># mset_set C' #} \<subseteq># mset_cl (D, \<sigma>)"
    by auto
  from this have "mset_cl (C', \<eta>) \<subseteq># mset_cl (D, \<sigma>)" by auto
  from this show ?thesis using multiset_order_inclusion_eq mult_trm_ord_trans by auto 
qed

lemma max_lit_exists:
  shows "finite C \<Longrightarrow> C \<noteq> {} \<longrightarrow> ground_clause C \<longrightarrow> (\<exists>L. (L \<in> C \<and> (maximal_literal L C)))"
proof (induction rule: finite.induct)
  case emptyI
  show ?case by simp
next
  fix A :: "'a clause" and a:: "'a literal"
  assume "finite A"
  assume hyp_ind: "A \<noteq> {} \<longrightarrow> ground_clause A \<longrightarrow> (\<exists>L. (L \<in> A \<and> (maximal_literal L A)))" 
  show "(insert a A) \<noteq> {} \<longrightarrow> ground_clause (insert a A) 
          \<longrightarrow> (\<exists>L. (L \<in> (insert a A) \<and> (maximal_literal L (insert a A))))"
  proof ((rule impI)+)
    assume "insert a A \<noteq> {}"
    assume "ground_clause (insert a A)"
    show "(\<exists>L. (L \<in> (insert a A) \<and> (maximal_literal L (insert a A))))"
    proof (cases)
      assume "A = {}"
      then have "a \<in> (insert a A) \<and> (maximal_literal a (insert a A))" 
        unfolding maximal_literal_def using lit_ord_irrefl by auto
      then show ?thesis by auto
    next assume "A \<noteq> {}"
      have "insert a A = {a} \<union> A" by auto
      then have "vars_of_cl (insert a A) = vars_of_cl A \<union> vars_of_lit a" by auto
      from this and `ground_clause (insert a A)` have 
        "vars_of_lit a = {}" and "ground_clause A" by auto
      from `ground_clause A` and `A \<noteq> {}` and hyp_ind obtain b where
        "b \<in> A" and "maximal_literal b A" by auto
      show ?thesis 
      proof (cases)
       assume "maximal_literal a A" 
       then have "maximal_literal a (insert a A)" 
        using lit_ord_wf maximal_literal_def by auto  
       then show ?thesis by auto
      next 
       assume "\<not>maximal_literal a A" 
       then obtain a' where "a' \<in> A" and "(a,a') \<in> lit_ord" 
        unfolding maximal_literal_def by auto
       from `a' \<in> A` and `maximal_literal b A` have "(b,a') \<notin> lit_ord"
        unfolding maximal_literal_def by auto
       from this and `(a,a') \<in> lit_ord` 
        have "(b,a) \<notin> lit_ord" unfolding lit_ord_def
          using mult_def trancl_trans by fastforce
        
       from this and `maximal_literal b A` have "maximal_literal b (insert a A)" 
        unfolding maximal_literal_def by simp 
       from this and `b \<in> A` show ?thesis by auto
    qed
  qed
 qed
qed

text {* We deduce that a clause contains at least one eligible literal. *}

lemma eligible_lit_exists:
  assumes "finite (cl_ecl C)"
  assumes "(cl_ecl C) \<noteq> {}"
  assumes "(ground_clause (subst_cl (cl_ecl C) \<sigma>))"
  shows "\<exists>L. ((eligible_literal L C \<sigma>) \<and> (L \<in> (cl_ecl C)))"
proof (cases)
  assume "sel (cl_ecl C) = {}"
  let ?C = "(subst_cl (cl_ecl C) \<sigma>)" 
  have "finite ?C" by (simp add: assms(1))
  have "?C \<noteq> {}"
  proof -
    from assms(2) obtain L where "L \<in> (cl_ecl C)" by auto
    from this have "(subst_lit L \<sigma>) \<in> ?C" by auto
    from this show "?C \<noteq> {}" by auto
  qed
  from `finite ?C` `?C \<noteq> {}` assms(3) obtain L where "L \<in> ?C" "maximal_literal L ?C" using max_lit_exists by metis
  from `L \<in> ?C` obtain L' where "L' \<in> (cl_ecl C)" and "L = (subst_lit L' \<sigma>)" by auto
  from `L' \<in> (cl_ecl C)` `L = (subst_lit L' \<sigma>)` `maximal_literal L ?C` `sel (cl_ecl C) = {}`
    show ?thesis unfolding eligible_literal_def by metis
next
  assume "sel (cl_ecl C) \<noteq> {}"
  then obtain L where "L \<in> sel (cl_ecl C)" by auto
  from this show ?thesis unfolding eligible_literal_def using sel_neg by blast
qed

text {* The following lemmata provide various ways of proving that literals are ordered, depending 
on the relations between the terms they contain. *}

lemma lit_ord_dominating_term:
  assumes "(s1,s2) \<in> trm_ord \<or> (s1,t2) \<in> trm_ord"
  assumes "orient_lit x1 s1 t1 p1"
  assumes "orient_lit x2 s2 t2 p2"
  assumes "vars_of_lit x1 = {}"
  assumes "vars_of_lit x2 = {}"
  shows "(x1,x2) \<in> lit_ord"
proof -
  from `vars_of_lit x1 = {}` and `orient_lit x1 s1 t1 p1` have "vars_of t1 = {}" and "vars_of s1 = {}" 
    and "\<not>(s1,t1) \<in> trm_ord" unfolding orient_lit_def by auto
  from assms(5) and `orient_lit x2 s2 t2 p2` have "vars_of t2 = {}" and "vars_of s2 = {}" 
    and "\<not>(s2,t2) \<in> trm_ord" unfolding orient_lit_def by auto
  from `vars_of t1 = {}` and `vars_of s1 = {}` and `\<not>(s1,t1) \<in> trm_ord` 
    have o1: "t1 = s1 \<or> (t1,s1) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  from `vars_of t2 = {}` and `vars_of s2 = {}` and `\<not>(s2,t2) \<in> trm_ord` 
    have o2: "t2 = s2 \<or> (t2,s2) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  from `\<not>(s2,t2) \<in> trm_ord` and assms(1) have "(s1,s2) \<in> trm_ord"
    by (metis assms(1) o2 trm_ord_trans transE)
  let ?m1 = "mset_lit x1"
  let ?m2 = "mset_lit x2"
  from assms(1) and o1 and o2 have "(t1,s2) \<in> trm_ord" using trm_ord_trans 
     trans_def by metis
  from this and `(s1,s2) \<in> trm_ord` have 
    s2max: "\<forall>x. (x \<in># {# t1,t1,s1,s1 #} \<longrightarrow> (x,s2) \<in> trm_ord)" 
     by auto
   have "{# s2 #} \<subset># {# t2,t2,s2,s2 #}" by simp 
   from `{# s2 #} \<subset># {# t2,t2,s2,s2 #}` 
   have "( {# s2 #}, {# t2,t2,s2,s2 #} ) \<in> mult trm_ord"
     using trm_ord_trans multiset_order_inclusion [of "{# s2 #}" "{# t2,t2,s2,s2 #}" "trm_ord"] by auto
  have "p1 = neg \<or> p1 = pos" using sign.exhaust by auto 
  then show ?thesis
  proof 
    assume "p1 = neg" 
    from this and `orient_lit x1 s1 t1 p1` have "x1 = (Neg (Eq t1 s1)) \<or> x1 = (Neg (Eq s1 t1))" 
      using orient_lit_def by blast
    from this have m1: "?m1 = {# t1,t1,s1,s1 #}" using mset_lit.simps by auto

    have "p2 = neg \<or> p2 = pos" using sign.exhaust by auto 
    then show ?thesis
    proof
      assume "p2 = neg"
      from this and `orient_lit x2 s2 t2 p2` have "x2 = (Neg (Eq t2 s2)) \<or> x2 = (Neg (Eq s2 t2))" 
        using orient_lit_def by blast
      from this have m2: "?m2 = {# t2,t2,s2,s2 #}" using mset_lit.simps by auto
      from s2max have "({# t1,t1,s1,s1 #}, {# s2 #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# s2 #}" "{#}" s2 "{# t1,t1,s1,s1 #}" "{# t1,t1,s1,s1 #}" trm_ord]
        mult_def
        by auto  

      from `( {# s2 #}, {# t2,t2,s2,s2 #} ) \<in> mult trm_ord` and `({# t1,t1,s1,s1 #}, {# s2 #}) \<in> mult trm_ord` 
        have "( {# t1,t1,s1,s1 #}, {# t2,t2,s2,s2 #} ) \<in> mult trm_ord"
        using mult_trm_ord_trans unfolding trans_def by blast

      from this and m1 and m2 show ?thesis
        using lit_ord_def by auto
      next assume "p2 = pos"
      from this and `orient_lit x2 s2 t2 p2` have "x2 = (Pos (Eq t2 s2)) \<or> x2 = (Pos (Eq s2 t2))" 
        using orient_lit_def by blast
      from this have m2: "?m2 = {# t2,s2 #}" using mset_lit.simps by auto
      from s2max have "({# t1,t1,s1,s1 #}, {# s2 #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# s2 #}" "{#}" s2 "{# t1,t1,s1,s1 #}" "{# t1,t1,s1,s1 #}" trm_ord]
        mult_def
        by auto  
      from this and `( {# s2 #}, {# t2,t2,s2,s2 #} ) \<in> mult trm_ord` 
        have "({# t1,t1,s1,s1 #}, {# t2,s2 #}) \<in> mult trm_ord" 
        using mset_ordering_add1 [of "{# t1,t1,s1,s1 #}" " {# s2 #}" trm_ord t2] by (auto)
      from this and m1 and m2 show ?thesis
        using lit_ord_def by auto
   qed
   next 
    assume "p1 = pos" 
    from this and `orient_lit x1 s1 t1 p1` have "x1 = (Pos (Eq t1 s1)) \<or> x1 = (Pos (Eq s1 t1))" 
      using orient_lit_def by blast
    from this have m1: "?m1 = {# t1,s1 #}" using mset_lit.simps by auto
    have "p2 = neg \<or> p2 = pos" using sign.exhaust by auto 
    then show ?thesis
    proof
      assume "p2 = neg"
      from this and `orient_lit x2 s2 t2 p2` have "x2 = (Neg (Eq t2 s2)) \<or> x2 = (Neg (Eq s2 t2))" 
        using orient_lit_def by blast
      from this have m2: "?m2 = {# t2,t2,s2,s2 #}" using mset_lit.simps by auto
      from s2max have "({# t1,s1 #}, {# s2 #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# s2 #}" "{#}" s2 "{# t1,s1 #}" "{# t1,s1 #}" trm_ord]
        mult_def
        by auto  
      from `( {# s2 #}, {# t2,t2,s2,s2 #} ) \<in> mult trm_ord` and `({# t1,s1 #}, {# s2 #}) \<in> mult trm_ord` 
        have "( {# t1,s1 #}, {# t2,t2,s2,s2 #} ) \<in> mult trm_ord"
        using mult_trm_ord_trans unfolding trans_def by blast

      from this and m1 and m2 show ?thesis
        using lit_ord_def by auto
      next assume "p2 = pos"
      from this and `orient_lit x2 s2 t2 p2` have "x2 = (Pos (Eq t2 s2)) \<or> x2 = (Pos (Eq s2 t2))" 
        using orient_lit_def by blast
      from this have m2: "?m2 = {# t2,s2 #}" using mset_lit.simps by auto
      from s2max have "({# t1,s1 #}, {# s2 #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# s2 #}" "{#}" s2 "{# t1,s1 #}" "{# t1,s1 #}" trm_ord]
        mult_def
        by auto  
      from this have "({# t1,s1 #}, {# t2,s2 #}) \<in> mult trm_ord" 
        using mset_ordering_add1 [of "{# t1,s1 #}" " {# s2 #}" trm_ord t2] by auto
      from this and m1 and m2 show ?thesis
        using lit_ord_def by auto
   qed
 qed
qed

lemma lit_ord_neg_lit_lhs:
  assumes "orient_lit x1 s t1 pos"
  assumes "orient_lit x2 s t2 neg"
  assumes "vars_of_lit x1 = {}"
  assumes "vars_of_lit x2 = {}"
  shows "(x1,x2) \<in> lit_ord"
proof -
  from assms(3) and assms(1) have "vars_of t1 = {}" and "vars_of s = {}" 
    and "\<not>(s,t1) \<in> trm_ord" unfolding orient_lit_def by auto
  from assms(4) and assms(2) have "vars_of t2 = {}"  
    and "\<not>(s,t2) \<in> trm_ord" unfolding orient_lit_def by auto
  from `vars_of t1 = {}` and `vars_of s = {}` and `\<not>(s,t1) \<in> trm_ord` 
    have o1: "t1 = s \<or> (t1,s) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  from `vars_of t2 = {}` and `vars_of s = {}` and `\<not>(s,t2) \<in> trm_ord` 
    have o2: "t2 = s \<or> (t2,s) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  let ?m1 = "mset_lit x1"
  let ?m2 = "mset_lit x2"
  from `orient_lit x1 s t1 pos` have "x1 = (Pos (Eq t1 s)) \<or> x1 = (Pos (Eq s t1))" 
      using orient_lit_def by blast
  from this have m1: "?m1 = {# t1,s #}" using mset_lit.simps by auto
  from `orient_lit x2 s t2 neg` have "x2 = (Neg (Eq t2 s)) \<or> x2 = (Neg (Eq s t2))" 
        using orient_lit_def by blast
  from this have m2: "?m2 = {# t2,t2,s,s #}" using mset_lit.simps by auto
  show ?thesis
  proof (cases)
    assume "t1 = s"
    have "({# s,s #}, {# t2,s,s #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# t2,s,s #}" "{# s,s #}" t2 "{# s,s #}" "{#}" trm_ord]
        mult_def by auto
    then have "({# s,s #}, {# t2,t2,s,s #}) \<in> mult trm_ord"
        using mset_ordering_add1 [of "{# s,s #}" " {# t2,s,s #}" trm_ord t2] by auto
    from this and `t1 = s` and m1 and m2 show ?thesis using lit_ord_def by auto
  next
    assume "t1 \<noteq> s"
    from this and o1 have "(t1,s) \<in> trm_ord" by auto
    from this have smax: "\<forall>x. (x \<in># {# t1 #} \<longrightarrow> (x,s) \<in> trm_ord)" 
     by auto
    from smax have "({# t1,s #}, {# s,s #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# s,s #}" "{# s #}" s "{# t1,s #}" "{# t1 #}" trm_ord]
        mult_def by auto
    from this have "({# t1,s #}, {# t2,s,s #}) \<in> mult trm_ord" 
        using mset_ordering_add1 [of "{# t1,s #}" " {# s,s #}" trm_ord t2] by auto
    from this have "({# t1,s #}, {# t2,t2,s,s #}) \<in> mult trm_ord" 
        using mset_ordering_add1 [of "{# t1,s #}" " {# t2,s,s #}" trm_ord t2] by auto
    from this and m1 and m2 show ?thesis using lit_ord_def by auto
   qed
qed

lemma lit_ord_neg_lit_rhs:
  assumes "orient_lit x1 s t1 pos"
  assumes "orient_lit x2 t2 s neg"
  assumes "vars_of_lit x1 = {}"
  assumes "vars_of_lit x2 = {}"
  shows "(x1,x2) \<in> lit_ord"
proof -
  from assms(3) and assms(1) have "vars_of t1 = {}" and "vars_of s = {}" 
    and "\<not>(s,t1) \<in> trm_ord" unfolding orient_lit_def by auto
  from assms(4) and assms(2) have "vars_of t2 = {}"  
    and "\<not>(t2,s) \<in> trm_ord" unfolding orient_lit_def by auto
  from `vars_of t1 = {}` and `vars_of s = {}` and `\<not>(s,t1) \<in> trm_ord` 
    have o1: "t1 = s \<or> (t1,s) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  from `vars_of t2 = {}` and `vars_of s = {}` and `\<not>(t2,s) \<in> trm_ord` 
    have o2: "t2 = s \<or> (s,t2) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  let ?m1 = "mset_lit x1"
  let ?m2 = "mset_lit x2"
  from `orient_lit x1 s t1 pos` have "x1 = (Pos (Eq t1 s)) \<or> x1 = (Pos (Eq s t1))" 
      using orient_lit_def by blast
  from this have m1: "?m1 = {# t1,s #}" using mset_lit.simps by auto
  from `orient_lit x2 t2 s neg` have "x2 = (Neg (Eq t2 s)) \<or> x2 = (Neg (Eq s t2))" 
        using orient_lit_def by blast
  from this have m2: "?m2 = {# t2,t2,s,s #}" using mset_lit.simps by auto
  show ?thesis
  proof (cases)
    assume "t1 = s"
    have "({# s,s #}, {# t2,s,s #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# t2,s,s #}" "{# s,s #}" t2 "{# s,s #}" "{#}" trm_ord]
        mult_def by auto
    then have "({# s,s #}, {# t2,t2,s,s #}) \<in> mult trm_ord"
        using mset_ordering_add1 [of "{# s,s #}" " {# t2,s,s #}" trm_ord t2] by auto
    from this and `t1 = s` and m1 and m2 show ?thesis using lit_ord_def by auto
  next
    assume "t1 \<noteq> s"
    from this and o1 have "(t1,s) \<in> trm_ord" by auto
    from this have smax: "\<forall>x. (x \<in># {# t1 #} \<longrightarrow> (x,s) \<in> trm_ord)" 
     by auto
    from smax have "({# t1,s #}, {# s,s #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# s,s #}" "{# s #}" s "{# t1,s #}" "{# t1 #}" trm_ord]
        mult_def by auto
    from this have "({# t1,s #}, {# t2,s,s #}) \<in> mult trm_ord" 
        using mset_ordering_add1 [of "{# t1,s #}" " {# s,s #}" trm_ord t2] by auto
    from this have "({# t1,s #}, {# t2,t2,s,s #}) \<in> mult trm_ord" 
        using mset_ordering_add1 [of "{# t1,s #}" " {# t2,s,s #}" trm_ord t2] by auto
    from this and m1 and m2 show ?thesis using lit_ord_def by auto
   qed
qed

lemma lit_ord_rhs:
  assumes "(t1,t2) \<in> trm_ord"
  assumes "orient_lit x1 s t1 p"
  assumes "orient_lit x2 s t2 p"
  assumes "vars_of_lit x1 = {}"
  assumes "vars_of_lit x2 = {}"
  shows "(x1,x2) \<in> lit_ord"
proof -
  from assms(2) and assms(4) have "vars_of t1 = {}" and "vars_of s = {}" 
    and "\<not>(s,t1) \<in> trm_ord" unfolding orient_lit_def by auto
  from assms(3) and assms(5) have "vars_of t2 = {}"  
    and "\<not>(s,t2) \<in> trm_ord" unfolding orient_lit_def by auto
  from `vars_of t1 = {}` and `vars_of s = {}` and `\<not>(s,t1) \<in> trm_ord` 
    have o1: "t1 = s \<or> (t1,s) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  from `vars_of t2 = {}` and `vars_of s = {}` and `\<not>(s,t2) \<in> trm_ord` 
    have o2: "t2 = s \<or> (t2,s) \<in> trm_ord" using trm_ord_ground_total 
    unfolding ground_term_def by auto
  let ?m1 = "mset_lit x1"
  let ?m2 = "mset_lit x2"
  have "p = pos \<or> p = neg" using sign.exhaust by auto 
  then show ?thesis
  proof 
    assume "p = pos"
    from this and `orient_lit x1 s t1 p` have "x1 = (Pos (Eq t1 s)) \<or> x1 = (Pos (Eq s t1))" 
      using orient_lit_def by blast
    from this have m1: "?m1 = {# t1,s #}" using mset_lit.simps by auto
    from `p = pos` and `orient_lit x2 s t2 p` have "x2 = (Pos (Eq t2 s)) \<or> x2 = (Pos (Eq s t2))" 
        using orient_lit_def by blast
    from this have m2: "?m2 = {# t2,s #}" using mset_lit.simps  by auto
    from assms(1) have "(\<forall>b. b \<in># {#t1#} \<longrightarrow> (b, t2) \<in> trm_ord)" by auto
    then have "({# t1,s #}, {# t2,s #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# t2,s #}" "{# s #}" t2 "{# t1,s #}" "{# t1 #}" trm_ord]
        mult_def by auto
    from this and m1 and m2 show ?thesis using lit_ord_def by auto
  next assume "p = neg"
    from this and `orient_lit x1 s t1 p` have "x1 = (Neg (Eq t1 s)) \<or> x1 = (Neg (Eq s t1))" 
      using orient_lit_def by blast
    from this have m1: "?m1 = {# t1,t1,s,s #}" using mset_lit.simps by auto
    from `p = neg` and `orient_lit x2 s t2 p` have "x2 = (Neg (Eq t2 s)) \<or> x2 = (Neg (Eq s t2))" 
        using orient_lit_def by blast
    from this have m2: "?m2 = {# t2,t2,s,s #}" using mset_lit.simps by auto
    from assms(1) have max: "(\<forall>b. b \<in># {#t1,t1#} \<longrightarrow> (b, t2) \<in> trm_ord)" by auto

    have i: "{# t2,s,s #} = {# s,s,t2 #}" by (simp add: add.commute add.left_commute) 
    have ii: "{# t1,t1,s,s #} = {# s,s,t1,t1 #}" by (simp add: add.commute add.left_commute) 
    from i and ii and max have "({# t1,t1,s,s #}, {# t2,s,s #}) \<in> mult trm_ord"
        using mult1_def_lemma [of "{# t2,s,s #}" "{# s,s #}" t2 "{# t1,t1,s,s #}" "{# t1,t1 #}" trm_ord]
        mult_def by auto
    then have "({# t1,t1,s,s #}, {# t2,t2,s,s #}) \<in> mult trm_ord"
        using mset_ordering_add1 [of "{# t1,t1,s,s #}" " {# t2,s,s #}" trm_ord t2] by auto
    from this and m1 and m2 show ?thesis using lit_ord_def by auto
  qed
qed

text {* We show that the replacement of a term by an equivalent term preserves the semantics. *}

lemma trm_rep_preserves_eq_semantics:
  assumes "fo_interpretation I"
  assumes "(I (subst t1 \<sigma>) (subst t2 \<sigma>))"
  assumes "(validate_ground_eq I (subst_equation (Eq t1 s) \<sigma>))"
  shows "(validate_ground_eq I (subst_equation (Eq t2 s) \<sigma>))"
proof -
  from assms(1) have "transitive I" and "symmetric I" unfolding 
    fo_interpretation_def congruence_def equivalence_relation_def by auto
  have "(subst_equation (Eq t1 s) \<sigma>) = (Eq (subst t1 \<sigma>) (subst s \<sigma>))" by simp
  from this and assms(3) have "I (subst t1 \<sigma>)  (subst s \<sigma>)"  by simp
  from this and assms(2) and `transitive I` and `symmetric I`
    have "I (subst t2 \<sigma>) (subst s \<sigma>)" 
    unfolding transitive_def symmetric_def by metis 
  have "(subst_equation (Eq t2 s) \<sigma>) = (Eq (subst t2 \<sigma>) (subst s \<sigma>))" by simp
  from this and `I (subst t2 \<sigma>) (subst s \<sigma>)` show ?thesis by simp
qed

lemma trm_rep_preserves_lit_semantics:
  assumes "fo_interpretation I"
  assumes "(I (subst t1 \<sigma>) (subst t2 \<sigma>))"
  assumes "orient_lit_inst L t1 s polarity \<sigma>'"
  assumes "\<not>(validate_ground_lit I (subst_lit L \<sigma>))"
  shows "\<not>validate_ground_lit I (subst_lit (mk_lit polarity (Eq t2 s)) \<sigma>)"

proof -
  from assms(1) have "transitive I" and "symmetric I" unfolding 
    fo_interpretation_def congruence_def equivalence_relation_def by auto
  have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto
  then show ?thesis
  proof
    assume "polarity = pos"
    from this have mk: "(mk_lit polarity (Eq t2 s)) = (Pos (Eq t2 s))" by auto
    from `polarity = pos` and assms(3) have "L = (Pos (Eq t1 s)) \<or> L = (Pos (Eq s t1))"
      unfolding orient_lit_inst_def by auto
    then show ?thesis
    proof
      assume "L = (Pos (Eq t1 s))"
      from this and assms(4) have "\<not>I (subst t1 \<sigma>) (subst s \<sigma>)" by simp
      from this and assms(2) and `transitive I` and `symmetric I` 
        have "\<not>I (subst t2 \<sigma>) (subst s \<sigma>)" 
        unfolding transitive_def symmetric_def by metis 
      from this and mk show ?thesis by simp
    next
      assume "L = (Pos (Eq s t1))"
      from this and assms(4) have "\<not>I (subst s \<sigma>) (subst t1 \<sigma>)" by simp
      from this and assms(2) and `transitive I` and `symmetric I` 
        have "\<not>I (subst t2 \<sigma>) (subst s \<sigma>)" 
        unfolding transitive_def symmetric_def by metis 
      from this and mk show ?thesis by simp
    qed
    next 
    assume "polarity = neg"
    from this have mk: "(mk_lit polarity (Eq t2 s)) = (Neg (Eq t2 s))" by auto
    from `polarity = neg` and assms(3) have "L = (Neg (Eq t1 s)) \<or> L = (Neg (Eq s t1))"
      unfolding orient_lit_inst_def by auto
    then show ?thesis
    proof
      assume "L = (Neg (Eq t1 s))"
      from this and assms(4) have "I (subst t1 \<sigma>) (subst s \<sigma>)" by simp
      from this and assms(2) and `transitive I` and `symmetric I` 
        have "I (subst t2 \<sigma>) (subst s \<sigma>)" 
        unfolding transitive_def symmetric_def by metis 
      from this and mk show ?thesis by simp
    next
      assume "L = (Neg (Eq s t1))"
      from this and assms(4) have "I (subst s \<sigma>) (subst t1 \<sigma>)" by simp
      from this and assms(2) and `transitive I` and `symmetric I` 
        have "I (subst t2 \<sigma>) (subst s \<sigma>)" 
        unfolding transitive_def symmetric_def by metis 
      from this and mk show ?thesis by simp
    qed
 qed
qed

lemma subterms_dominated :
  assumes "maximal_literal L C"
  assumes "orient_lit L t s p"
  assumes "u \<in> subterms_of_cl C"
  assumes "vars_of_lit L = {}"
  assumes "vars_of_cl C = {}"
  shows "u = t \<or> (u,t) \<in> trm_ord"
proof (rule ccontr)
  assume neg_h: "\<not>(u = t \<or> (u,t) \<in> trm_ord)"
  from assms(5) and assms(3) have "vars_of u = {}" using subterm_vars by blast
  from `vars_of_lit L = {}` and `orient_lit L t s p` have "vars_of s = {}" and "vars_of t = {}" 
    and "\<not>(t,s) \<in> trm_ord" unfolding orient_lit_def by auto
  from assms(3) obtain L' where "u \<in> subterms_of_lit L'" and "L' \<in> C"  by auto
  from assms(5) and `L' \<in> C` have "vars_of_lit L' = {}" using vars_of_cl.simps by auto
  from `u \<in> subterms_of_lit L'` obtain t' s' p' where "orient_lit L' t' s' p'" 
    and "u \<in> subterms_of t' \<union> subterms_of s'" unfolding orient_lit_def
      by (metis Un_commute mset_lit.cases subterms_of_eq.simps subterms_of_lit.simps(1) 
          subterms_of_lit.simps(2) trm_ord_wf wf_asym) 
  from `u \<in> subterms_of t' \<union> subterms_of s'` have "u \<in> subterms_of t' \<or> u \<in> subterms_of s'" by auto
  then show False
  proof 
    assume "u \<in> subterms_of t'"
    from this have "u = t' \<or> (u,t') \<in> trm_ord"  
      using subterms_of_trm_ord_eq [of u t'] by auto
    from neg_h and `vars_of u = {}` and  `vars_of t = {}` have "(t,u) \<in> trm_ord" 
      using trm_ord_ground_total unfolding ground_term_def by auto
    from this and `u = t' \<or> (u,t') \<in> trm_ord` have "(t,t') \<in> trm_ord"
      using trm_ord_trans unfolding trans_def by metis
    from this and `vars_of_lit L' = {}`  and assms(4) and 
        `orient_lit L t s p` and `orient_lit L' t' s' p'`
      have "(L,L') \<in> lit_ord" using lit_ord_dominating_term by blast  
    from this and assms(1) and `L' \<in> C`  show False unfolding maximal_literal_def by auto
  next
    assume "u \<in> subterms_of s'"
    from this have "u = s' \<or> (u,s') \<in> trm_ord"  
      using subterms_of_trm_ord_eq [of u s'] by auto
    from neg_h and `vars_of u = {}` and  `vars_of t = {}` have "(t,u) \<in> trm_ord" 
      using trm_ord_ground_total unfolding ground_term_def by auto
    from this and `u = s' \<or> (u,s') \<in> trm_ord` have "(t,s') \<in> trm_ord"
      using trm_ord_trans unfolding trans_def by metis
    from this and `vars_of_lit L' = {}`  and assms(4) and 
        `orient_lit L t s p` and `orient_lit L' t' s' p'`
      have "(L,L') \<in> lit_ord" using lit_ord_dominating_term by blast  
    from this and assms(1) and `L' \<in> C`  show False unfolding maximal_literal_def by auto
 qed
qed

text {* A term dominates an expression if the expression contains no strictly greater subterm: *}

fun dominate_eq:: "'a trm \<Rightarrow> 'a equation \<Rightarrow> bool"
  where "(dominate_eq t (Eq u v)) = ((t,u) \<notin> trm_ord \<and> (t,v) \<notin> trm_ord)"

fun dominate_lit:: "'a trm \<Rightarrow> 'a literal \<Rightarrow> bool"
  where "(dominate_lit t (Pos e)) = (dominate_eq t e)" |
        "(dominate_lit t (Neg e)) = (dominate_eq t e)"

definition dominate_cl:: "'a trm \<Rightarrow> 'a clause \<Rightarrow> bool"
  where "(dominate_cl t C) = (\<forall>x \<in> C. (dominate_lit t x))"

definition no_disequation_in_cl:: "'a trm \<Rightarrow> 'a clause \<Rightarrow> bool"
  where "(no_disequation_in_cl t C) = (\<forall>u v. 
    (Neg (Eq u v) \<in> C \<longrightarrow> (u \<noteq> t \<and> v \<noteq> t)))"

definition no_taut_eq_in_cl:: "'a trm \<Rightarrow> 'a clause \<Rightarrow> bool"
  where "(no_taut_eq_in_cl t C) = (Pos (Eq t t) \<notin> C)"

definition eq_occurs_in_cl
  where
    "(eq_occurs_in_cl t s C \<sigma>) = (\<exists>L t' s'. (L \<in> C) \<and> (orient_lit_inst L t' s' pos \<sigma>) 
        \<and> (t = subst t' \<sigma>) \<and> (s = subst s' \<sigma>))"

subsection {* Inference Rules *}

text {* We now define the rules of the superposition calculus. Standard superposition is 
a refinement of the paramodulation rule based on the following ideas: 

(i) the replacement of a term by a bigger term is forbidden; 

(ii) the replacement can be performed only in the maximal term of a maximal (or selected) literal; 

(iii) replacement of variables is forbidden.

Our definition imposes additional conditions on the positions on which the replacements
are allowed: any superposition inference inside a term occurring in the set attached to the 
extended clause is blocked.
*}

text {* We consider two different kinds of inferences: ground or first-order. Ground inferences
are those needed for completeness, first-order inferences are those actually used 
by theorem provers. For conciseness, these two notions of inferences are defined simultaneously, 
and a parameter is added to the corresponding functions to determine whether the 
inference is ground or first-order. *}

datatype inferences = Ground | FirstOrder 

text {* The following function checks whether a given substitution is a unifier of two terms.
If the inference is first-order then the unifier must be maximal. *}

definition ck_unifier
where 
  "(ck_unifier t s \<sigma> type) = 
    (if (type = FirstOrder) then (MGU \<sigma> t s) else (Unifier \<sigma> t s))"

lemma ck_unifier_thm:
  assumes "ck_unifier t s \<sigma> k"
  shows "(subst t \<sigma>) = (subst s \<sigma>)"
by (metis assms MGU_is_Unifier ck_unifier_def Unifier_def)

lemma subst_preserve_ck_unifier:
  assumes "ck_unifier t s \<sigma> k"
  shows "ck_unifier t s (comp \<sigma> \<eta>) Ground"
proof -
  let ?\<sigma>' = "(comp \<sigma> \<eta>)"
  from assms have "(subst t \<sigma>) = (subst s \<sigma>)" 
    using ck_unifier_thm by auto 
  then have "(subst t ?\<sigma>') = (subst s ?\<sigma>')" by simp
  then show ?thesis unfolding ck_unifier_def Unifier_def by auto
qed

text {* The following function checks whether a given term is allowed to be reduced according to the 
strategy described above, i.e., that it does not occur in the set of terms associated with 
the clause (we do not assume that the set of irreducible terms is closed under subterm
thus we use the function @{term "occurs_in"} instead of a mere membership test. *}

definition allowed_redex 
  where "allowed_redex t C \<sigma> = (\<not> (\<exists>s \<in> (trms_ecl C). 
    (occurs_in (subst t \<sigma>) (subst s \<sigma>))))"

text {* The following function allows one to compute the set of irreducible terms attached to
the conclusion of an inference. The computation depends on the type of the considered inference: 
for ground inferences the entire set of irreducible terms is kept. For first-order inferences, 
the function @{term "filter_trms"} is called to remove some of the terms 
(see also the function @{term "dom_trms"} below). *}

definition get_trms
  where 
      "get_trms C E t = (if (t = FirstOrder) then (filter_trms C E) else E)"

text {* The following definition provides the conditions that allow one to propagate irreducible
terms from the parent clauses to the conclusion. A term can be propagated if it is strictly lower 
than a term occurring in the derived clause, or if it occurs in a negative literal of the derived 
clause. Note that this condition is slightly more restrictive than that of the basic superposition 
calculus, because maximal terms occurring in maximal positive literals cannot be kept in the set of 
irreducible terms. However in our definition, terms can be propagated even if they do not occur in 
the parent clause or in the conclusion. Extended clauses whose set of irreducible terms fulfills 
this property are called well-constrained.*}
 
definition dom_trm
  where "dom_trm t C = 
      (\<exists> L u v p. (L \<in> C \<and> (decompose_literal L u v p) 
        \<and> (( (p = neg \<and> t = u) \<or> (t,u) \<in> trm_ord))))"

lemma dom_trm_lemma:
  assumes "dom_trm t C"
  shows "\<exists> u. (u \<in> (subterms_of_cl C) \<and> (u = t \<or> (t,u) \<in> trm_ord))"
proof -
  from   assms(1) obtain L u v p where
    "L \<in> C" "decompose_literal L u v p" "(u = t \<or> (t,u) \<in> trm_ord)" 
    unfolding dom_trm_def by blast
  from `decompose_literal L u v p` have "u \<in> subterms_of_lit L"
    unfolding decompose_literal_def decompose_equation_def using root_subterm by force
  from this and `L \<in> C` have "u \<in> (subterms_of_cl C)" by auto
  from this and `(u = t \<or> (t,u) \<in> trm_ord)` show ?thesis by auto
qed

definition dom_trms
where
  "dom_trms C E = { x. (x \<in> E) \<and> (dom_trm x C) }"

lemma dom_trms_subset:
  shows "(dom_trms C E ) \<subseteq> E"
unfolding dom_trms_def by auto

lemma dom_trm_vars:
  assumes "dom_trm t C"
  shows "vars_of t \<subseteq> vars_of_cl C"
proof -
  from assms obtain L u v p where "L \<in> C" "decompose_literal L u v p" "t = u \<or> (t,u) \<in> trm_ord"  
    unfolding dom_trm_def by auto
  from `t = u \<or> (t,u) \<in> trm_ord` have "vars_of t \<subseteq> vars_of u" using trm_ord_vars by blast
  from this and `decompose_literal L u v p` have "vars_of t \<subseteq> vars_of_lit L" using decompose_literal_vars by blast
  from this show ?thesis using `L \<in> C` by auto 
qed

definition well_constrained
  where "well_constrained C = (\<forall>y. (y \<in> trms_ecl C \<longrightarrow> dom_trm y (cl_ecl C)))"

text {* The next function allows one to check that a set of terms is in normal form. 
The argument @{term "f"} denotes the function mapping a term to its normal form 
(we do not assume that @{term "f"} is compatible with the term structure at this point). *}

definition all_trms_irreducible
  where "(all_trms_irreducible E f) = (\<forall>x y. (x \<in> E \<longrightarrow> occurs_in y x \<longrightarrow> (f y) = y))"

paragraph {* Superposition *}

text {* We now define the superposition rule. Note that we assume that the parent clauses are
variable-disjoint, but we do not explicitly rename them at this point, thus for completeness
we will have to assume that the clause sets are closed under renaming. During the application 
of the rule, all the terms occurring at a position that is lower than that of the reduced
term can be added in the set of irreducible terms attached to the conclusion (the intuition is that
we assume that the terms occurring at minimal positions are reduced first). 
In particular, every proper subterm of the reduced term @{term "u'"} is added in the set of 
irreducible terms, thus every application of the superposition rule in a term introduced 
by unification will be blocked.

Clause @{term "P1"} is the ``into'' clause and clause @{term "P2"} is the ``from'' clause. *}

definition superposition :: 
  "'a eclause \<Rightarrow> 'a eclause \<Rightarrow> 'a eclause \<Rightarrow> 'a subst \<Rightarrow> inferences \<Rightarrow> 'a clause \<Rightarrow> bool"
where
   "(superposition P1 P2 C \<sigma> k C') =
   (\<exists>L t s u v M p Cl_P1 Cl_P2 Cl_C polarity t' u' L' trms_C. 
      (L \<in> Cl_P1) \<and> (M \<in> Cl_P2) \<and> (eligible_literal L P1 \<sigma>) \<and>  (eligible_literal M P2 \<sigma>)
      \<and> (variable_disjoint P1 P2)
      \<and> (Cl_P1 = (cl_ecl P1)) \<and> (Cl_P2 = (cl_ecl P2)) 
    \<and> (\<not> is_a_variable u')
    \<and> (allowed_redex u' P1 \<sigma>)
    \<and> trms_C = (get_trms Cl_C (dom_trms Cl_C (subst_set 
        ((trms_ecl P1) \<union> (trms_ecl P2) \<union> 
          { r. \<exists> q. (q,p) \<in> (pos_ord P1 t) \<and> (subterm t q r) }) \<sigma>)) k) 
    \<and> (C = (Ecl Cl_C trms_C)) 
    \<and> (orient_lit_inst M u v pos \<sigma>) 
    \<and> (orient_lit_inst L t s polarity \<sigma>) 
    \<and> ((subst u \<sigma>) \<noteq> (subst v \<sigma>))
    \<and> (subterm t p u')
    \<and> (ck_unifier u' u \<sigma> k)
    \<and> (replace_subterm t p v t') 
    \<and> ((k = FirstOrder) \<or> ( (subst_lit M \<sigma>),(subst_lit L \<sigma>)) \<in> lit_ord)
    \<and> ((k = FirstOrder) \<or> (strictly_maximal_literal P2 M \<sigma>))
    \<and> (L' = mk_lit polarity (Eq t' s)) 
    \<and> (Cl_C = (subst_cl C' \<sigma>))
    \<and> (C' = (Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )))"

paragraph {* Reflexion *}

text {* We now define the Reflexion rule, which deletes contradictory literals (after unification). 
All the terms occurring in these literals can be added into the set of irreducible terms
(intuitively, we can assume that these terms have been normalized before applying the rule). 
It is sufficient to add the term @{term "t"}, since every term occurring in the considered literal 
is a subterm of @{term "t"} (after unification). *}

definition reflexion ::
  "'a eclause \<Rightarrow> 'a eclause \<Rightarrow> 'a subst \<Rightarrow> inferences \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  "(reflexion P C \<sigma> k C') = 
    (\<exists>L1 t s Cl_P Cl_C trms_C.
      (eligible_literal L1 P \<sigma>)
      \<and> (L1 \<in> (cl_ecl P)) \<and> (Cl_C = (cl_ecl C)) \<and> (Cl_P = (cl_ecl P)) 
      \<and> (orient_lit_inst L1 t s neg \<sigma>)
      \<and> (ck_unifier t s \<sigma> k)
      \<and> (C = (Ecl Cl_C trms_C))
      \<and> trms_C = (get_trms Cl_C 
          (dom_trms Cl_C (subst_set ( (trms_ecl P) \<union> { t } ) \<sigma>)) k) 
      \<and> (Cl_C = (subst_cl C' \<sigma>))
      \<and> (C' = ((Cl_P - { L1 }) )))"

paragraph {* Factorization *}

text {* We now define the equational factorization rule, which merges two equations sharing the 
same left-hand side (after unification), if the right-hand sides are equivalent. 
Here, contrarily to the previous rule, the term @{term "t"} cannot be added into the set of 
irreducible terms, because we cannot assume that this term is in normal form (e.g., the application
of the equational factorization rule may yield a new rewrite rule of left-hand side @{term "t"}). 
However, all proper subterms of @{term "t"} can be added. *}

definition factorization ::
  "'a eclause \<Rightarrow> 'a eclause \<Rightarrow> 'a subst \<Rightarrow> inferences \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  "(factorization P C \<sigma> k C') = 
    (\<exists>L1 L2 L' t s u v Cl_P Cl_C trms_C.
      (eligible_literal L1 P \<sigma>)
      \<and> (L1 \<in> (cl_ecl P)) \<and> (L2 \<in> (cl_ecl P) - { L1 }) \<and> (Cl_C = (cl_ecl C)) \<and> (Cl_P = (cl_ecl P)) 
      \<and> (orient_lit_inst L1 t s pos \<sigma>)
      \<and> (orient_lit_inst L2 u v pos \<sigma>)
      \<and> ((subst t \<sigma>) \<noteq> (subst s \<sigma>))
      \<and> ((subst t \<sigma>) \<noteq> (subst v \<sigma>))
      \<and> (ck_unifier t u \<sigma> k)
      \<and> (L' = Neg (Eq s v))
      \<and> (C = (Ecl Cl_C trms_C)
      \<and> trms_C = (get_trms Cl_C 
          (dom_trms Cl_C (subst_set ( (trms_ecl P) \<union> (proper_subterms_of t) ) \<sigma>))) k) 
      \<and> (Cl_C = (subst_cl C' \<sigma>))
      \<and> (C' = ( (Cl_P - { L2 }) \<union> { L' } )))"

subsection {* Derivations *}

text {* We now define the set of derivable clauses by induction. Note that redundancy criteria 
are not taken into account at this point. Our definition of derivations also covers renaming. *}

definition derivable :: "'a eclause \<Rightarrow> 'a eclause set 
  \<Rightarrow> 'a eclause set \<Rightarrow> 'a subst \<Rightarrow> inferences \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  "(derivable C P S \<sigma> k C') = 
      ((\<exists>P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> P = { P1, P2 } \<and> superposition P1 P2 C \<sigma> k C'))
    \<or> (\<exists>P1. (P1 \<in> S \<and> P = { P1 } \<and> factorization P1 C \<sigma> k C'))
    \<or> (\<exists>P1. (P1 \<in> S \<and> P = { P1 } \<and> reflexion P1 C \<sigma> k C')))"

lemma derivable_premisses:
  assumes "derivable C P S \<sigma> k C'"
  shows "P \<subseteq> S"
using assms derivable_def by auto

inductive derivable_ecl :: "'a eclause \<Rightarrow> 'a eclause set  \<Rightarrow> bool"
  where
    init [simp, intro!]: "C \<in> S \<Longrightarrow> (derivable_ecl C S)" | 
    rn [simp, intro!]: "(derivable_ecl C S) \<Longrightarrow> (renaming_cl C D) \<Longrightarrow> (derivable_ecl D S)" | 
    deriv [simp, intro!]: "(\<forall>x. (x \<in> P \<longrightarrow> (derivable_ecl x S))) 
      \<Longrightarrow> (derivable C P S' \<sigma> FirstOrder C') \<Longrightarrow> (derivable_ecl C S)" 

text {* We define a notion of instance by associating clauses with ground substitutions. *}

definition instances:: "'a eclause set \<Rightarrow> ('a eclause \<times> 'a subst) set"
  where "instances S = { x. \<exists>C \<sigma>. (C \<in> S  \<and> (ground_clause (subst_cl (cl_ecl C) \<sigma>)) 
  \<and> x = ( C,\<sigma>))}"

definition clset_instances:: "('a eclause \<times> 'a subst) set \<Rightarrow> 'a clause set"
where
  "clset_instances S = { C. \<exists>x. (x \<in> S \<and> C = (subst_cl (cl_ecl (fst x)) (snd x))) }"
  
definition grounding_set
  where "grounding_set S \<sigma> = (\<forall>x. (x \<in> S \<longrightarrow> (ground_clause (subst_cl (cl_ecl x) \<sigma>))))"

section {* Soundness *}

text {* In this section, we prove that the conclusion of every inference rule is a logical 
consequence of the premises. Thus a clause set is unsatisfiable if the empty clause is derivable. 
For each rule, we first prove that all ground instances of the conclusion are entailed by 
the corresponding instances of the parent clauses, then we lift the result to first-order clauses. 
The proof is standard and straightforward, but note that we also prove that the derived 
clauses are finite and well-constrained. *} 

lemma cannot_validate_contradictary_literals :
  assumes "l = Neg (Eq t t)"
  assumes "fo_interpretation I"
  shows "\<not> (validate_ground_lit I l)"
proof -
  from assms(2) have "congruence I" unfolding fo_interpretation_def by auto
  then have "I t t" unfolding congruence_def reflexive_def equivalence_relation_def by auto
  from this and assms(1) show ?thesis by auto
qed

lemma ground_reflexion_is_sound :
  assumes "finite (cl_ecl C)"
  assumes "reflexion C D \<sigma> k C'"
  assumes "(ground_clause (subst_cl (cl_ecl D) \<theta>))"
  shows "clause_entails_clause (subst_cl (subst_cl (cl_ecl C) \<sigma>) \<theta>) 
          (subst_cl (cl_ecl D) \<theta>)"
proof (rule ccontr)
  let ?C = "(cl_ecl C)" 
  let ?D = "(cl_ecl D)"
  let ?C' = "(subst_cl (subst_cl (cl_ecl C) \<sigma>) \<theta>)"
  let ?D' = "(subst_cl (cl_ecl D) \<theta>)"
  assume "\<not> (clause_entails_clause ?C' ?D')"
  then obtain I where "validate_clause I ?C'" and "\<not> (validate_clause I ?D')" "fo_interpretation I"
    unfolding clause_entails_clause_def by auto
  from assms(2) obtain L1 t s where
    "?D = (subst_cl (?C - { L1 }) \<sigma>)" 
    and "orient_lit_inst L1 t s neg \<sigma>" and "ck_unifier t s \<sigma> k" 
      using reflexion_def [of C D \<sigma> k] by auto
  from assms(1) have "finite (subst_cl (subst_cl ?C \<sigma>) \<theta>)" by auto  
  then obtain \<eta> where i: "ground_clause (subst_cl 
        (subst_cl (subst_cl ?C \<sigma>) \<theta>) \<eta>)" 
    using ground_instance_exists [of "(subst_cl (subst_cl ?C \<sigma>) \<theta>)"]  
    by auto
  let ?CC = "(subst_cl (subst_cl (subst_cl ?C \<sigma>) \<theta>) \<eta>)" 
  let ?\<sigma>'' = "comp \<sigma> \<theta>"
  let ?\<sigma>' = "comp ?\<sigma>'' \<eta>"
  have "?CC = (subst_cl (subst_cl ?C ?\<sigma>'') \<eta>)" 
    using composition_of_substs_cl [of ?C] by auto
  then have "?CC = (subst_cl ?C ?\<sigma>')" 
    using composition_of_substs_cl [of ?C] by auto
  from `validate_clause I (subst_cl (subst_cl (cl_ecl C) \<sigma>) \<theta>)` 
    have "validate_ground_clause I ?CC" using i validate_clause.simps by blast 
  then obtain l' where "l' \<in> ?CC" and "validate_ground_lit I l'" by auto
  from `l' \<in> ?CC` and `?CC = (subst_cl ?C ?\<sigma>')` obtain l where 
    "l \<in> ?C" and "l' = (subst_lit l ?\<sigma>')" using subst_cl.simps  by blast
  have "subst_lit l \<sigma> \<in> ?D"
  proof (rule ccontr)
    assume "subst_lit l \<sigma> \<notin> ?D" 
    from this and `?D = (subst_cl (?C - { L1 }) \<sigma>)` and `l \<in> ?C` 
      have "l = L1" by auto
    from this and `orient_lit_inst L1 t s neg \<sigma>` have "l = (Neg (Eq t s)) \<or> l = (Neg (Eq s t))" 
      unfolding orient_lit_inst_def by auto
    from `ck_unifier t s \<sigma> k` have "subst t \<sigma> = subst s \<sigma>" 
      using ck_unifier_thm by auto
    then have "subst (subst (subst t \<sigma>) \<theta>) \<eta> =
      subst (subst (subst s \<sigma>) \<theta>) \<eta>" by auto
    then have "(subst t ?\<sigma>') = subst s ?\<sigma>'" by auto
    from this and `l = (Neg (Eq t s)) \<or> l = (Neg (Eq s t))` 
      have "(subst_lit l ?\<sigma>') = (Neg (Eq (subst t ?\<sigma>') (subst t ?\<sigma>')))"
      by auto
    from this and `fo_interpretation I` have "\<not> (validate_ground_lit I (subst_lit l ?\<sigma>'))" 
      using cannot_validate_contradictary_literals [of "(subst_lit l ?\<sigma>')" "(subst t ?\<sigma>')" I]
      by auto
    from this and `l' = subst_lit l ?\<sigma>'` and `validate_ground_lit I l'` show False by auto
  qed
  from `subst_lit l \<sigma> \<in> ?D` and `l' = subst_lit l ?\<sigma>'`
    have "l' \<in> (subst_cl (subst_cl ?D \<theta>) \<eta>)"
    using subst_cl.simps composition_of_substs_lit mem_Collect_eq
    by (metis (mono_tags, lifting))
  from this and `validate_ground_lit I l'` have 
    "validate_ground_clause I (subst_cl (subst_cl ?D \<theta>) \<eta>)" by auto
  from `ground_clause (subst_cl ?D \<theta>)` have
    "(subst_cl ?D \<theta>) = (subst_cl (subst_cl ?D \<theta>) \<eta>)"
    using substs_preserve_ground_clause [of "(subst_cl ?D \<theta>)"  \<eta>] by blast
  from this and `validate_ground_clause I (subst_cl (subst_cl ?D \<theta>) \<eta>)`
   have "validate_ground_clause I (subst_cl ?D \<theta>)" by force
  from this and assms(3) and `\<not> validate_clause I (subst_cl (cl_ecl D) \<theta>)` show False
    using substs_preserve_ground_clause validate_clause.elims(3) by metis 
qed

lemma reflexion_is_sound :
  assumes "finite (cl_ecl C)"
  assumes "reflexion C D \<sigma> k C'"
  shows "clause_entails_clause (cl_ecl C) (cl_ecl D)"
proof (rule ccontr)
  let ?C = "(cl_ecl C)" 
  let ?D = "(cl_ecl D)"
  assume "\<not> (clause_entails_clause ?C ?D)"
  then obtain I where "validate_clause I ?C" and "\<not> (validate_clause I ?D)" "fo_interpretation I"
    unfolding clause_entails_clause_def by auto
  from `\<not> (validate_clause I ?D)` obtain \<theta> 
    where D_false: "\<not> (validate_ground_clause I (subst_cl ?D \<theta>))" 
      and "(ground_clause (subst_cl ?D \<theta>))" by auto
  have  "validate_clause I (subst_cl (subst_cl ?C \<sigma>) \<theta>)"
    using \<open>validate_clause I (cl_ecl C)\<close> instances_are_entailed by blast 
  from this and assms(1) and assms(2) have "validate_clause I (subst_cl ?D \<theta>)"
    using ground_reflexion_is_sound unfolding clause_entails_clause_def
    using \<open>fo_interpretation I\<close> \<open>ground_clause (subst_cl (cl_ecl D) \<theta>)\<close> by blast   
  from this and D_false show False  
    by (metis \<open>ground_clause (subst_cl (cl_ecl D) \<theta>)\<close> 
    substs_preserve_ground_clause validate_clause.elims(1))  
qed

lemma orient_lit_semantics_pos :
  assumes "fo_interpretation I"
  assumes "orient_lit_inst l u v pos \<eta>"
  assumes "validate_ground_lit I (subst_lit l \<sigma>)"
  shows "I (subst u \<sigma>) (subst v \<sigma>)"
proof -
    let ?u = "subst u \<sigma>"
    let ?v = "subst v \<sigma>"
    from assms(2) have "l = (Pos (Eq u v)) \<or> l = (Pos (Eq v u))"  using orient_lit_inst_def by auto 
    from this and assms(3) have "validate_ground_eq I (Eq ?u ?v) \<or> validate_ground_eq I (Eq ?v ?u)"
      by auto
    then have "I ?u ?v \<or> I ?v ?u" by auto
    from this and `fo_interpretation I` show "I ?u ?v"
      unfolding fo_interpretation_def congruence_def equivalence_relation_def symmetric_def by blast
qed

lemma orient_lit_semantics_neg :
  assumes "fo_interpretation I"
  assumes "orient_lit_inst l u v neg \<theta>"
  assumes "validate_ground_lit I (subst_lit l \<sigma>)"
  shows "\<not>I (subst u \<sigma>) (subst v \<sigma>)"
proof -
    let ?u = "subst u \<sigma>"
    let ?v = "subst v \<sigma>"
    from assms(2) have "l = (Neg (Eq u v)) \<or> l = (Neg (Eq v u))"  using orient_lit_inst_def by auto 
    from this and assms(3) have "\<not>validate_ground_eq I (Eq ?u ?v) \<or> \<not>validate_ground_eq I (Eq ?v ?u)"
      by auto
    then have "\<not>I ?u ?v \<or> \<not>I ?v ?u" by auto
    from this and `fo_interpretation I` show "\<not>I ?u ?v"
      unfolding fo_interpretation_def congruence_def equivalence_relation_def symmetric_def by blast
qed

lemma orient_lit_semantics_replacement :
  assumes "fo_interpretation I"
  assumes "orient_lit_inst l u v polarity \<theta>"
  assumes "validate_ground_lit I (subst_lit l \<sigma>)" 
  assumes "I (subst u \<sigma>) (subst u' \<sigma>)"
  shows "validate_ground_lit I (subst_lit (mk_lit polarity (Eq u' v)) \<sigma>)"
proof -
  from assms(2) obtain e where "l = Pos e \<or> l = Neg e" and "e = Eq u v \<or> e = Eq v u" 
    unfolding orient_lit_inst_def by auto
  have "polarity = pos \<or> polarity = neg" using sign.exhaust by blast 
  then show ?thesis
  proof 
    assume "polarity = pos"
    from this and assms(1) and assms(2) and `validate_ground_lit I (subst_lit l \<sigma>)` have
      "I (subst u \<sigma>) (subst v \<sigma>)" using orient_lit_semantics_pos by auto
    from this and assms(1) and `I (subst u \<sigma>) (subst u' \<sigma>)` 
      have "I (subst u' \<sigma>) (subst v \<sigma>)" unfolding fo_interpretation_def 
      congruence_def equivalence_relation_def symmetric_def transitive_def by blast
    from this and `polarity = pos` show ?thesis by auto
  next
    assume "polarity = neg"
    from this and assms(1) and assms(2) and `validate_ground_lit I (subst_lit l \<sigma>)` have
      "\<not>I (subst u \<sigma>) (subst v \<sigma>)" using orient_lit_semantics_neg
      by blast
    from this and assms(1) and `I (subst u \<sigma>) (subst u' \<sigma>)` 
      have "\<not>I (subst u' \<sigma>) (subst v \<sigma>)" unfolding fo_interpretation_def 
      congruence_def equivalence_relation_def symmetric_def transitive_def by blast
    from this and `polarity = neg` show ?thesis by auto
  qed
qed

lemma ground_factorization_is_sound :
  assumes "finite (cl_ecl C)"
  assumes "factorization C D \<sigma> k C'"
  assumes "(ground_clause (subst_cl (cl_ecl D) \<theta>))"
  shows "clause_entails_clause (subst_cl (subst_cl (cl_ecl C) \<sigma>) \<theta>) 
          (subst_cl (cl_ecl D) \<theta>)"
proof (rule ccontr)
  let ?C = "(cl_ecl C)" 
  let ?D = "(cl_ecl D)"
  assume "\<not> clause_entails_clause (subst_cl (subst_cl (cl_ecl C) \<sigma>) \<theta>) 
          (subst_cl (cl_ecl D) \<theta>)"
  then obtain I where 
    "validate_clause I (subst_cl (subst_cl (cl_ecl C) \<sigma>) \<theta>)" and 
      "\<not> (validate_clause I (subst_cl (cl_ecl D) \<theta>))" and "fo_interpretation I"
    unfolding clause_entails_clause_def by auto
  from assms(2) obtain L1 L2 L' t s u v where
      "orient_lit_inst L1 t s pos \<sigma>" and "orient_lit_inst L2 u v pos \<sigma>" and "ck_unifier t u \<sigma> k"
      and "L' = Neg (Eq s v)" 
      and "(?D =  (subst_cl ( (?C - { L2 }) \<union> { L' } )) \<sigma>)"
      and "L1 \<noteq> L2"
      and "L1 \<in> ?C"
   using factorization_def by auto
  
  from assms(1) have "finite (subst_cl (subst_cl ?C \<sigma>) \<theta>)" by auto  
  then obtain \<eta> where i: "ground_clause (subst_cl 
        (subst_cl (subst_cl ?C \<sigma>) \<theta>) \<eta>)" 
    using ground_instance_exists [of "(subst_cl (subst_cl ?C \<sigma>) \<theta>)"]  
    by auto
  let ?CC = "(subst_cl (subst_cl (subst_cl ?C \<sigma>) \<theta>) \<eta>)" 
  let ?\<sigma>'' = "comp \<sigma> \<theta>"
  let ?\<sigma>' = "comp ?\<sigma>'' \<eta>"
  have "?CC = (subst_cl (subst_cl ?C ?\<sigma>'') \<eta>)" 
    using composition_of_substs_cl [of ?C] by auto
  then have "?CC = (subst_cl ?C ?\<sigma>')" 
    using composition_of_substs_cl [of ?C] by auto
  from `validate_clause I (subst_cl (subst_cl (cl_ecl C) \<sigma>) \<theta>)` 
    have "validate_ground_clause I ?CC" using i validate_clause.simps by blast 
  then obtain l' where "l' \<in> ?CC" and "validate_ground_lit I l'" by auto
  from `l' \<in> ?CC` and `?CC = (subst_cl ?C ?\<sigma>')` obtain l where 
    "l \<in> ?C" and "l' = (subst_lit l ?\<sigma>')" using subst_cl.simps  by blast
   from `\<not> validate_clause I (subst_cl (cl_ecl D) \<theta>)` 
    have "\<not> validate_ground_clause I (subst_cl ?D \<theta>)"
    using assms(3) substs_preserve_ground_clause validate_clause.elims(3) by metis 
   from `ground_clause (subst_cl ?D \<theta>)` have
    "(subst_cl ?D \<theta>) = (subst_cl (subst_cl ?D \<theta>) \<eta>)"
    using substs_preserve_ground_clause [of "(subst_cl ?D \<theta>)"  \<eta>] by blast
  from this and `\<not> validate_ground_clause I (subst_cl ?D \<theta>)`
   have "\<not> validate_ground_clause I (subst_cl (subst_cl ?D \<theta>) \<eta>)" by force
  from `(?D =  (subst_cl ( (?C - { L2 }) \<union> { L' } )) \<sigma>)` 
    have "(subst_lit L' \<sigma>) \<in> ?D" by auto
  then have 
    "(subst_lit (subst_lit (subst_lit L' \<sigma>) \<theta>) \<eta>) 
      \<in> (subst_cl (subst_cl ?D \<theta>) \<eta>)"
    by auto    
  from this and `\<not> validate_ground_clause I (subst_cl (subst_cl ?D \<theta>) \<eta>)`
    have "\<not>validate_ground_lit I (subst_lit (subst_lit (subst_lit L' \<sigma>) \<theta>) \<eta>)"
    by auto 
  from this and `L'= Neg (Eq s v)` have 
    "I (subst (subst (subst s \<sigma>) \<theta>) \<eta>)
       (subst (subst (subst v \<sigma>) \<theta>) \<eta>)" by auto
  from this have "I (subst s ?\<sigma>') (subst v ?\<sigma>')" by simp 

  have "subst_lit l \<sigma> \<in> ?D"
  proof (rule ccontr)
    assume "subst_lit l \<sigma> \<notin> ?D" 
    from this and `(?D =  (subst_cl ( (?C - { L2 }) \<union> { L' } )) \<sigma>)` and `l \<in> ?C` 
      have "l = L2" by auto
    from `ck_unifier t u \<sigma>  k` have "subst t \<sigma> = subst u \<sigma>" 
      using ck_unifier_thm by auto
    then have "subst (subst (subst t \<sigma>) \<theta>) \<eta> =
      subst (subst (subst u \<sigma>) \<theta>) \<eta>" by auto
    then have "(subst t ?\<sigma>') = subst u ?\<sigma>'" by auto
    from `validate_ground_lit I l'` and `l' = (subst_lit l ?\<sigma>')` have 
      "validate_ground_lit I (subst_lit l ?\<sigma>')" by auto 
 
    from this and `fo_interpretation I` and `l = L2` and `orient_lit_inst L2 u v pos \<sigma>` 
      have "I (subst u ?\<sigma>') (subst v ?\<sigma>')" using orient_lit_semantics_pos 
      by blast
    
    from this and `fo_interpretation I` and `I (subst s ?\<sigma>') (subst v ?\<sigma>')`
      have "I (subst u ?\<sigma>') (subst s ?\<sigma>')"
      unfolding fo_interpretation_def congruence_def equivalence_relation_def 
        symmetric_def transitive_def by blast
    from this and `(subst t ?\<sigma>') = subst u ?\<sigma>'` 
      have "I (subst t ?\<sigma>') (subst s ?\<sigma>')" by auto
    from this have "validate_ground_eq I (subst_equation (Eq t s) ?\<sigma>')" 
      by auto
 
    from `I (subst t ?\<sigma>') (subst s ?\<sigma>')` and `fo_interpretation I`  
      have "I (subst s ?\<sigma>') (subst t ?\<sigma>')" 
      unfolding fo_interpretation_def congruence_def equivalence_relation_def 
        symmetric_def by auto
    from this have "validate_ground_eq I (subst_equation (Eq s t) ?\<sigma>')" 
      by auto

    from `orient_lit_inst L1 t s pos \<sigma>` have "L1 = (Pos (Eq t s)) \<or> L1 = (Pos (Eq s t))" 
      unfolding orient_lit_inst_def by auto
    from this and `validate_ground_eq I (subst_equation (Eq s t) ?\<sigma>')` and 
      `validate_ground_eq I (subst_equation (Eq t s) ?\<sigma>')`
      have "validate_ground_lit I (subst_lit L1 ?\<sigma>')" 
    by auto
    from `L1 \<in> ?C` and `?D =  (subst_cl ( (?C - { L2 }) \<union> { L' } )) \<sigma>` and `L1 \<noteq> L2`
      have "(subst_lit L1 \<sigma>) \<in> ?D"
      by auto
    then have 
      "(subst_lit (subst_lit (subst_lit L1 \<sigma>) \<theta>) \<eta>) 
        \<in> (subst_cl (subst_cl ?D \<theta>) \<eta>)" by auto
    then have "(subst_lit L1 ?\<sigma>') \<in> (subst_cl (subst_cl ?D \<theta>) \<eta>)"
      using composition_of_substs_lit by metis
    from this and `validate_ground_lit I (subst_lit L1 ?\<sigma>')` and 
      `\<not> validate_ground_clause I (subst_cl (subst_cl ?D \<theta>) \<eta>)`
      show False by auto
  qed

  from `subst_lit l \<sigma> \<in> ?D` and `l' = subst_lit l ?\<sigma>'`
    have "l' \<in> (subst_cl (subst_cl ?D \<theta>) \<eta>)"
    using subst_cl.simps composition_of_substs_lit mem_Collect_eq
    by (metis (mono_tags, lifting))
  from this and `validate_ground_lit I l'` have 
    "validate_ground_clause I (subst_cl (subst_cl ?D \<theta>) \<eta>)" by auto
  from this and `\<not> validate_ground_clause I (subst_cl (subst_cl ?D \<theta>) \<eta>)` 
    show False by blast
qed

lemma factorization_is_sound :
  assumes "finite (cl_ecl C)"
  assumes "factorization C D \<sigma> k C'"
  shows "clause_entails_clause (cl_ecl C) (cl_ecl D)"
proof (rule ccontr)
  let ?C = "(cl_ecl C)" 
  let ?D = "(cl_ecl D)"
  assume "\<not> (clause_entails_clause ?C ?D)"
  then obtain I where "validate_clause I ?C" and "\<not> (validate_clause I ?D)" "fo_interpretation I"
    unfolding clause_entails_clause_def by auto
  from `\<not> (validate_clause I ?D)` obtain \<theta> 
    where D_false: "\<not> (validate_ground_clause I (subst_cl ?D \<theta>))" 
      and "(ground_clause (subst_cl ?D \<theta>))" by auto
  have  "validate_clause I (subst_cl (subst_cl ?C \<sigma>) \<theta>)"
    using \<open>validate_clause I (cl_ecl C)\<close> instances_are_entailed by blast 
  from this and assms(1) and assms(2) have "validate_clause I (subst_cl ?D \<theta>)"
    using ground_factorization_is_sound unfolding clause_entails_clause_def
    using \<open>fo_interpretation I\<close> \<open>ground_clause (subst_cl (cl_ecl D) \<theta>)\<close> by blast   
  from this and D_false show False  
    by (metis \<open>ground_clause (subst_cl (cl_ecl D) \<theta>)\<close> 
    substs_preserve_ground_clause validate_clause.elims(1))  
qed

lemma ground_superposition_is_sound :
  assumes "finite (cl_ecl P1)"
  assumes "finite (cl_ecl P2)"
  assumes "superposition P1 P2 C \<sigma> k C'"
  assumes "(ground_clause (subst_cl (cl_ecl C) \<theta>))"
  shows "set_entails_clause 
    { (subst_cl (subst_cl (cl_ecl P1) \<sigma>) \<theta>), 
      (subst_cl (subst_cl (cl_ecl P2) \<sigma>) \<theta>) }
          (subst_cl (cl_ecl C) \<theta>)"

proof (rule ccontr)
  let ?P1 = "(cl_ecl P1)" 
  let ?P2 = "(cl_ecl P2)"
  let ?C = "(cl_ecl C)"
  assume "\<not> set_entails_clause 
    { (subst_cl (subst_cl (cl_ecl P1) \<sigma>) \<theta>), 
      (subst_cl (subst_cl (cl_ecl P2) \<sigma>) \<theta>) }
          (subst_cl (cl_ecl C) \<theta>)"
  then obtain I 
    where "validate_clause I (subst_cl (subst_cl (cl_ecl P1) \<sigma>) \<theta>)" 
    and "validate_clause I (subst_cl (subst_cl (cl_ecl P2) \<sigma>) \<theta>)" 
      and "\<not> (validate_clause I (subst_cl (cl_ecl C) \<theta>))" and "fo_interpretation I"
    unfolding set_entails_clause_def by (meson insert_iff validate_clause_set.elims(2))
  from assms(3) obtain t s u v M p polarity t' u' L L'   where
    "orient_lit_inst M u v pos \<sigma>" 
    and "orient_lit_inst L t s polarity \<sigma>"
    and "subterm t p u'"
    and "ck_unifier u' u \<sigma> k"
    and "replace_subterm t p v t'"
    and "L' = mk_lit polarity (Eq t' s)"
    and "?C = (subst_cl ((?P1 - { L }) \<union> ((?P2 - { M }) \<union> { L' } )) \<sigma>)"
   using superposition_def by auto
  
  let ?P1' = "(subst_cl (subst_cl ?P1 \<sigma>) \<theta>)"
  let ?P2' = "(subst_cl (subst_cl ?P2 \<sigma>) \<theta>)"
  from assms(1) have "finite ?P1'" by simp 
  from assms(2) have "finite ?P2'" by simp 

  let ?vars = "(vars_of_cl ?P1') \<union> (vars_of_cl ?P2')"
  from `finite ?P1'` have "finite (vars_of_cl ?P1')" 
    using set_of_variables_is_finite_cl [of ?P1']  by auto 
  from `finite ?P2'` have "finite (vars_of_cl ?P2')" 
    using set_of_variables_is_finite_cl [of ?P2']  by auto 
  from `finite (vars_of_cl ?P1')` and `finite (vars_of_cl ?P2')` have "finite ?vars" by auto
  then obtain \<eta> where "ground_on ?vars \<eta>" using ground_subst_exists by blast 
  then have "ground_on (vars_of_cl ?P1') \<eta>" unfolding ground_on_def by auto
  then have "ground_clause (subst_cl 
        (subst_cl (subst_cl ?P1 \<sigma>) \<theta>) \<eta>)"  
       using ground_substs_yield_ground_clause
        [of "(subst_cl (subst_cl ?P1 \<sigma>) \<theta>)" \<eta>] by auto
  from `ground_on ?vars \<eta>` have "ground_on (vars_of_cl ?P2') \<eta>" unfolding ground_on_def by auto
  then have "ground_clause (subst_cl 
        (subst_cl (subst_cl ?P2 \<sigma>) \<theta>) \<eta>)"  
       using ground_substs_yield_ground_clause 
        [of "(subst_cl (subst_cl ?P2 \<sigma>) \<theta>)" \<eta>] by auto
    
  let ?P1'' = "(subst_cl ?P1' \<eta>)" 
  let ?P2'' = "(subst_cl ?P2' \<eta>)" 
  let ?\<sigma>'' = "comp \<sigma> \<theta>"
  let ?\<sigma>' = "comp ?\<sigma>'' \<eta>"
  have "?P1'' = (subst_cl (subst_cl ?P1 ?\<sigma>'') \<eta>)" 
    using composition_of_substs_cl [of ?P1] by auto
  then have "?P1'' = (subst_cl ?P1 ?\<sigma>')" 
    using composition_of_substs_cl [of ?P1] by auto
  from `ground_clause (subst_cl (subst_cl (subst_cl (cl_ecl P1) \<sigma>) \<theta>) \<eta>)`
    and `validate_clause I (subst_cl (subst_cl (cl_ecl P1) \<sigma>) \<theta>)`
      have "validate_ground_clause I ?P1''" using  validate_clause.simps by blast 
  then obtain l1' where "l1' \<in> ?P1''" and "validate_ground_lit I l1'" by auto

  have "?P2'' = (subst_cl (subst_cl ?P2 ?\<sigma>'') \<eta>)" 
    using composition_of_substs_cl [of ?P2] by auto
  then have "?P2'' = (subst_cl ?P2 ?\<sigma>')" 
    using composition_of_substs_cl [of ?P2] by auto
  from \<open>ground_clause (subst_cl (subst_cl (subst_cl (cl_ecl P2) \<sigma>) \<theta>) \<eta>)\<close> \<open>validate_clause I (subst_cl (subst_cl (cl_ecl P2) \<sigma>) \<theta>)\<close> 
    have "validate_ground_clause I ?P2''" using  validate_clause.simps by blast 
  then obtain l2' where "l2' \<in> ?P2''" and "validate_ground_lit I l2'" by auto

  from `l1' \<in> ?P1''` and `?P1'' = (subst_cl ?P1 ?\<sigma>')` obtain l1 where 
    "l1 \<in> ?P1" and "l1' = (subst_lit l1 ?\<sigma>')" using subst_cl.simps  by blast
  from `l2' \<in> ?P2''` and `?P2'' = (subst_cl ?P2 ?\<sigma>')` obtain l2 where 
    "l2 \<in> ?P2" and "l2' = (subst_lit l2 ?\<sigma>')" using subst_cl.simps  by blast

  let ?C' = "(subst_cl (subst_cl ?C \<theta>) \<eta>)"

  from `ground_clause (subst_cl ?C \<theta>)` have
    "(subst_cl ?C \<theta>) = (subst_cl (subst_cl ?C \<theta>) \<eta>)"
    using substs_preserve_ground_clause [of "(subst_cl ?C \<theta>)"  \<eta>] by blast
  from `\<not> validate_clause I (subst_cl (cl_ecl C) \<theta>)` 
    have "\<not> validate_ground_clause I ?C'"
    by (metis assms(4) substs_preserve_ground_clause validate_clause.simps) 
  have "l1 = L" 
  proof (rule ccontr)
    assume "l1 \<noteq> L"
    from this and `l1 \<in> ?P1` and `?C = (subst_cl ((?P1 - { L }) \<union> ((?P2 - { M }) \<union> { L' } )) \<sigma>)`
    have "(subst_lit l1 \<sigma>) \<in> ?C" by auto 
    from this have "(subst_lit (subst_lit (subst_lit l1 \<sigma>) \<theta>) \<eta>)
      \<in> ?C'" by auto
    from this and `l1' = (subst_lit l1 ?\<sigma>')` have "l1' \<in> ?C'"
      by (simp add: composition_of_substs_lit) 
    from this and `validate_ground_lit I l1'` have "validate_ground_clause I ?C'" by auto
    from this and `\<not> validate_ground_clause I (subst_cl (subst_cl (cl_ecl C) \<theta>) \<eta>)` 
      show False by auto
  qed

  have "l2 = M" 
  proof (rule ccontr)
    assume "l2 \<noteq> M"
    from this and `l2 \<in> ?P2` and `?C = (subst_cl ((?P1 - { L }) \<union> ((?P2 - { M }) \<union> { L' } )) \<sigma>)`
    have "(subst_lit l2 \<sigma>) \<in> ?C" by auto 
    from this have "(subst_lit (subst_lit (subst_lit l2 \<sigma>) \<theta>) \<eta>)
      \<in> ?C'" by auto
    from this and `l2' = (subst_lit l2 ?\<sigma>')` have "l2' \<in> ?C'"
      by (simp add: composition_of_substs_lit) 
    from this and `validate_ground_lit I l2'` have "validate_ground_clause I ?C'" by auto
    from this and `\<not> validate_ground_clause I (subst_cl (subst_cl (cl_ecl C) \<theta>) \<eta>)` 
      show False by auto
  qed
 
  from `orient_lit_inst M u v pos \<sigma>` and `l2 = M` and `fo_interpretation I` 
    and `validate_ground_lit I l2'` and `l2' = (subst_lit l2 ?\<sigma>')`
    have "I (subst u ?\<sigma>') (subst v ?\<sigma>')" 
    using orient_lit_semantics_pos by blast

  from `subterm t p u'` have
    "subterm (subst t ?\<sigma>') p (subst u' ?\<sigma>')" 
      using substs_preserve_subterms [of t p u'] by metis

  from `ck_unifier u' u \<sigma> k` have "(subst u \<sigma>) = (subst u' \<sigma>)"
    using ck_unifier_thm [of u' u \<sigma> k] by auto
  from this have "(subst (subst (subst u \<sigma>) \<theta>) \<eta>) 
    = (subst (subst (subst u' \<sigma>) \<theta> ) \<eta>)" by auto
  from this have "(subst u ?\<sigma>') = (subst u' ?\<sigma>')" 
    using composition_of_substs by auto

  from `(subst u ?\<sigma>') = (subst u' ?\<sigma>')` 
    and `I (subst u ?\<sigma>') (subst v ?\<sigma>')` 
    have "I (subst u' ?\<sigma>') (subst v ?\<sigma>')"
    by auto
  from `subterm t p u'` 
    and `I (subst u' ?\<sigma>') (subst v ?\<sigma>')` 
    and `fo_interpretation I`
    and `replace_subterm t p v t'` 
    have "I (subst t ?\<sigma>') (subst t' ?\<sigma>')" 
      unfolding fo_interpretation_def using replacement_preserves_congruences [of I u' ?\<sigma>' v t p t'] 
      by auto

  from `l1 = L` and `fo_interpretation I` and `validate_ground_lit I l1'` 
    and `l1' = (subst_lit l1 ?\<sigma>')` 
    and `orient_lit_inst L t s polarity \<sigma>` 
    and `I (subst t ?\<sigma>') (subst t' ?\<sigma>')`
    and `L' =  mk_lit polarity (Eq t' s)`
    have "validate_ground_lit I (subst_lit L' ?\<sigma>')" 
    using orient_lit_semantics_replacement [of I L t s polarity \<sigma> ?\<sigma>' t'] by blast

  from `?C = (subst_cl ((?P1 - { L }) \<union> ((?P2 - { M }) \<union> { L' } )) \<sigma>)`
    have "subst_lit L' \<sigma> \<in> ?C" by auto
  then have "subst_lit (subst_lit (subst_lit L' \<sigma>) \<theta>) \<eta> \<in> ?C'" 
    by auto
  then have "subst_lit L' ?\<sigma>' \<in> ?C'" by (simp add: composition_of_substs_lit) 
  
  from this and `validate_ground_lit I (subst_lit L' ?\<sigma>')` and `\<not>validate_ground_clause I ?C'`
    show False by auto
qed

lemma superposition_is_sound :
  assumes "finite (cl_ecl P1)"
  assumes "finite (cl_ecl P2)"
  assumes "superposition P1 P2 C \<sigma> k C'"
  shows "set_entails_clause { cl_ecl P1, cl_ecl P2 } (cl_ecl C)"
proof (rule ccontr)
  let ?P1 = "(cl_ecl P1)" 
  let ?P2 = "(cl_ecl P2)"
  let ?C = "(cl_ecl C)"
  assume "\<not> set_entails_clause { cl_ecl P1, cl_ecl P2 } (cl_ecl C)"
  then obtain I 
    where "validate_clause I ?P1" and "validate_clause I ?P2" 
      and "\<not> (validate_clause I ?C)" and "fo_interpretation I"
    unfolding set_entails_clause_def by (meson insert_iff validate_clause_set.elims(2))
  from `\<not> (validate_clause I ?C)` obtain \<theta> 
    where "\<not> (validate_ground_clause I (subst_cl ?C \<theta>))" 
      and "(ground_clause (subst_cl ?C \<theta>))" by auto

  have P1_true: "validate_clause I (subst_cl (subst_cl ?P1 \<sigma>) \<theta>)"
    using \<open>validate_clause I (cl_ecl P1)\<close> instances_are_entailed by blast 
  have P2_true: "validate_clause I (subst_cl (subst_cl ?P2 \<sigma>) \<theta>)"
    using \<open>validate_clause I (cl_ecl P2)\<close> instances_are_entailed by blast 
  have "\<not> (validate_clause I (subst_cl ?C \<theta>))"
    by (metis \<open>\<not> validate_ground_clause I (subst_cl (cl_ecl C) \<theta>)\<close> 
        \<open>ground_clause (subst_cl (cl_ecl C) \<theta>)\<close> 
        substs_preserve_ground_clause validate_clause.elims(1))  
  let ?S = "{ (subst_cl (subst_cl (cl_ecl P1) \<sigma>) \<theta>), 
      (subst_cl (subst_cl (cl_ecl P2) \<sigma>) \<theta>) }"
  from P1_true and P2_true have "validate_clause_set I ?S"
    by (metis insert_iff singletonD validate_clause_set.elims(3)) 
  from this and `\<not> (validate_clause I (subst_cl ?C \<theta>))` `fo_interpretation I` 
    have "\<not> set_entails_clause ?S (subst_cl (cl_ecl C) \<theta>)"
    using set_entails_clause_def by blast
  from this and assms(1) and assms(2) and assms(3) and 
    `(ground_clause (subst_cl ?C \<theta>))`
  show False using ground_superposition_is_sound by auto
qed

lemma superposition_preserves_finiteness:
  assumes "finite (cl_ecl P1)"
  assumes "finite (cl_ecl P2)"
  assumes "superposition P1 P2 C \<sigma> k C'"
  shows "finite (cl_ecl C) \<and> (finite C')"
proof -
  from assms(3) obtain L M L' where 
    def_C: "(cl_ecl C) = (subst_cl (((cl_ecl P1) - { L }) \<union> (((cl_ecl P2) - { M }) \<union> { L' } )) \<sigma>)"
    and def_C': "C' = (((cl_ecl P1) - { L }) \<union> (((cl_ecl P2) - { M }) \<union> { L' } ))"
    using superposition_def by auto
  from assms(1) and assms(2) have "finite (((cl_ecl P1) - { L }) \<union> (((cl_ecl P2) - { M }) \<union> { L' } ))"
    by auto
  from this and def_C def_C' show ?thesis using substs_preserve_finiteness by auto
qed

lemma reflexion_preserves_finiteness:
  assumes "finite (cl_ecl P1)"
  assumes "reflexion P1 C \<sigma> k C'"
  shows "finite (cl_ecl C) \<and> (finite C')"
proof -
  from assms(2) obtain L1 where 
    def_C: "(cl_ecl C) = (subst_cl ((cl_ecl P1) - { L1 }) \<sigma>)"
    and def_C': "C' = ((cl_ecl P1) - { L1 })"
    using reflexion_def by auto
  from assms(1) have "finite ((cl_ecl P1) - { L1 })" by auto
  from this and def_C def_C' show ?thesis using substs_preserve_finiteness by auto
qed

lemma factorization_preserves_finiteness:
  assumes "finite (cl_ecl P1)"
  assumes "factorization P1 C \<sigma> k C'"
  shows "finite (cl_ecl C) \<and> (finite C')"
proof -
  from assms(2) obtain L2 L' where 
    def_C: "(cl_ecl C) = (subst_cl ( ((cl_ecl P1) - { L2 }) \<union> { L' } ) \<sigma>)"
    and def_C': "C' = ( ((cl_ecl P1) - { L2 }) \<union> { L' } )"
    using factorization_def by auto
  from assms(1) have "(finite (((cl_ecl P1) - { L2 }) \<union> { L' }))" by auto
  from this and def_C def_C' show ?thesis using substs_preserve_finiteness by auto
qed

lemma derivable_clauses_are_finite:
  assumes "derivable C P S \<sigma> k C'"
  assumes "\<forall>x \<in> P. (finite (cl_ecl x))" 
  shows "finite (cl_ecl C) \<and> (finite C')"
proof (rule ccontr)
  assume hyp: "\<not> (finite (cl_ecl C)  \<and> (finite C'))" 
  have not_sup: "\<not> (\<exists>P1 P2. (P1 \<in> P \<and> P2 \<in> P \<and> superposition P1 P2 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1 P2. (P1 \<in> P \<and> P2 \<in> P \<and> superposition P1 P2 C \<sigma> k C'))"
    then obtain P1 P2 where "P1 \<in> P" "P2 \<in> P" "superposition P1 P2 C \<sigma> k C'" by auto
    from `P1 \<in> P` and assms(2) have "finite (cl_ecl P1)" by auto
    from `P2 \<in> P` and assms(2) have "finite (cl_ecl P2)" by auto
    from `(finite (cl_ecl P1))` and  `(finite (cl_ecl P2))` and `superposition P1 P2 C \<sigma> k C'`
      have "finite (cl_ecl C) \<and> (finite C')" using superposition_preserves_finiteness [of P1 P2 C \<sigma>] by auto
    then show False using hyp by auto
  qed
  have not_ref: "\<not> (\<exists>P1. (P1 \<in> P \<and> reflexion P1 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> P \<and> reflexion P1 C \<sigma> k C'))"
    then obtain P1 where "P1 \<in> P" "reflexion P1 C \<sigma> k C'" by auto
    from `P1 \<in> P` and assms(2) have "finite (cl_ecl P1)" by auto
    from `(finite (cl_ecl P1))`  and `reflexion P1 C \<sigma> k C'`
      have "finite (cl_ecl C)  \<and> (finite C')" using reflexion_preserves_finiteness [of P1 C \<sigma>] by auto
    then show False using hyp by auto
  qed
  have not_fact: "\<not> (\<exists>P1. (P1 \<in> P \<and> factorization P1 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> P \<and>  factorization P1 C \<sigma> k C'))"
    then obtain P1 where "P1 \<in> P" " factorization P1 C \<sigma> k C'" by auto
    from `P1 \<in> P` and assms(2) have "finite (cl_ecl P1)" by auto
    from `(finite (cl_ecl P1))`  and ` factorization P1 C \<sigma> k C'`
      have "finite (cl_ecl C)  \<and> (finite C')" using  factorization_preserves_finiteness [of P1 C \<sigma>] by auto
    then show False using hyp by auto
  qed
  from not_sup not_ref not_fact and assms(1) show False unfolding derivable_def by blast
qed
 
lemma derivable_clauses_lemma:
  assumes "derivable C P S \<sigma> k C'"
  shows "((cl_ecl C) = (subst_cl C' \<sigma>))"
proof (rule ccontr)
  assume hyp: "\<not> ((cl_ecl C) = (subst_cl C' \<sigma>))" 
  have not_sup: "\<not> (\<exists>P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> superposition P1 P2 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> superposition P1 P2 C \<sigma> k C'))"
    then obtain P1 P2 where "P1 \<in> S" "P2 \<in> S" "superposition P1 P2 C \<sigma> k C'" by auto
    from `superposition P1 P2 C \<sigma> k C'` obtain Cl_C Cl_P1 L Cl_P2 M L' T
      where "Cl_C = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<sigma>)"
        "(C' = (Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } ))"
        "C = (Ecl Cl_C T)"
        unfolding superposition_def by blast
    from `Cl_C = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<sigma>)` 
      `(C' = (Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } ))` `C = (Ecl Cl_C T)` hyp show False by auto
  qed
  have not_ref: "\<not> (\<exists>P1. (P1 \<in> S \<and> reflexion P1 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> S \<and> reflexion P1 C \<sigma> k C'))"
    then obtain P1 where "P1 \<in> S" "reflexion P1 C \<sigma> k C'" by auto
    from `reflexion P1 C \<sigma> k C'` obtain T Cl_C Cl_P L1 where
      "C = (Ecl Cl_C T)"
      "Cl_C = (subst_cl ((Cl_P - { L1 }) )) \<sigma>"
      "(C' = ((Cl_P - { L1 }) ))" unfolding reflexion_def by blast
    from `Cl_C = (subst_cl ((Cl_P - { L1 }) )) \<sigma>` 
      `(C' = ((Cl_P - { L1 }) ))` `C = (Ecl Cl_C T)` hyp show False by auto
  qed
  have not_fact: "\<not> (\<exists>P1. (P1 \<in> S \<and> factorization P1 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> S \<and>  factorization P1 C \<sigma> k C'))"
    then obtain P1 where "P1 \<in> S" "factorization P1 C \<sigma> k C'" by auto
    from `factorization P1 C \<sigma> k C'` obtain T Cl_C Cl_P L' L2 where
      "C = (Ecl Cl_C T)"
      "Cl_C = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } )) \<sigma>"
      "C' = ( (Cl_P - { L2 }) \<union> { L' } )" unfolding factorization_def by blast
    from `Cl_C = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } )) \<sigma>` 
      `C' = ( (Cl_P - { L2 }) \<union> { L' } )` `C = (Ecl Cl_C T)` hyp show False by auto
  qed
  from not_sup not_ref not_fact and assms(1) show False unfolding derivable_def by blast
qed

lemma substs_preserves_decompose_literal:
  assumes "decompose_literal L t s polarity"
  shows "decompose_literal (subst_lit L \<eta>) (subst t \<eta>) (subst s \<eta>) polarity"
proof -
  let ?L = "(subst_lit L \<eta>)"
  let ?t = "(subst t \<eta>)"
  let ?s = "(subst s \<eta>)"

  have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto  
  then show ?thesis
  proof
    assume "polarity = pos" 
    from this and assms(1) have "L = Pos (Eq t s) \<or> L = Pos (Eq s t)"
      unfolding decompose_literal_def decompose_equation_def by auto
    from `L = Pos (Eq t s) \<or> L = Pos (Eq s t)`
      have "?L = Pos (Eq ?t ?s) \<or> ?L = Pos (Eq ?s ?t)" by auto
    from this `polarity = pos` show ?thesis unfolding decompose_literal_def 
      decompose_equation_def by auto
  next
    assume "polarity = neg" 
    from this and assms(1) have "L = Neg (Eq t s) \<or> L = Neg (Eq s t)"
      unfolding decompose_literal_def decompose_equation_def by auto
    from this `polarity = neg` show ?thesis unfolding decompose_literal_def 
      decompose_equation_def by auto
  qed
qed

lemma substs_preserve_dom_trm:
  assumes "dom_trm t C"
  shows "dom_trm (subst t \<sigma>) (subst_cl C \<sigma>)"
proof -
  let ?t = "(subst t \<sigma>)"
  from assms(1) have "(\<exists> L u v p. (L \<in> C \<and> (decompose_literal L u v p) 
        \<and> (( (p = neg \<and> t = u) \<or> (t,u) \<in> trm_ord))))" unfolding dom_trm_def by auto
  from this obtain L u v p where  "L \<in> C" 
    "decompose_literal L u v p" "(( (p = neg \<and> t = u) \<or> (t,u) \<in> trm_ord))" 
    unfolding dom_trm_def by blast
  let ?u = "(subst u \<sigma>)"

  from `L \<in> C` have "(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)" by auto
  from `decompose_literal L u v p` 
    have "decompose_literal (subst_lit L \<sigma>) (subst u \<sigma>) (subst v \<sigma>) p" 
    using substs_preserves_decompose_literal by metis
  from `(( (p = neg \<and> t = u) \<or> (t,u) \<in> trm_ord))`
    have "(( (p = neg \<and> ?t = ?u) \<or> (?t,?u) \<in> trm_ord))"
      using trm_ord_subst by auto
  from this `(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)` 
    `decompose_literal (subst_lit L \<sigma>) (subst u \<sigma>) (subst v \<sigma>) p` 
    show "dom_trm (subst t \<sigma>) (subst_cl C \<sigma>)" 
    unfolding dom_trm_def by auto
qed

lemma substs_preserve_well_constrainedness:
  assumes "well_constrained C"
  shows "well_constrained (subst_ecl C \<sigma>)"
proof (rule ccontr)
  assume "\<not>?thesis"
  from this obtain y where "y \<in> trms_ecl (subst_ecl C \<sigma>)"
    and "\<not> dom_trm y (cl_ecl (subst_ecl C \<sigma>))" unfolding well_constrained_def by auto
  obtain Cl_C T where "C = (Ecl Cl_C T)" using "eclause.exhaust" by auto
  from this have "(subst_ecl C \<sigma>) 
    = (Ecl (subst_cl Cl_C \<sigma>) (subst_set T \<sigma>))" by auto
  from this have "(cl_ecl (subst_ecl C \<sigma>) = (subst_cl Cl_C \<sigma>))" 
    and "trms_ecl (subst_ecl C \<sigma>) = (subst_set T \<sigma>)" 
    by auto
  from `(cl_ecl (subst_ecl C \<sigma>) = (subst_cl Cl_C \<sigma>))` 
    `C = (Ecl Cl_C T)` have "(cl_ecl (subst_ecl C \<sigma>) = (subst_cl (cl_ecl C) \<sigma>))" by auto
  from `y \<in> trms_ecl (subst_ecl C \<sigma>)` `C = (Ecl Cl_C T)` 
    obtain z where "z \<in> T" and "y = (subst z \<sigma>)" by auto
  from `z \<in> T` assms(1) `C = (Ecl Cl_C T)` have "dom_trm z (cl_ecl C)" 
    unfolding well_constrained_def by auto
  from this have "dom_trm (subst z \<sigma>) (subst_cl (cl_ecl C) \<sigma>)"
    using substs_preserve_dom_trm by auto
  from this `y = (subst z \<sigma>)` have "dom_trm y (subst_cl (cl_ecl C) \<sigma>)"
    by auto
  from this `(cl_ecl (subst_ecl C \<sigma>) = (subst_cl (cl_ecl C) \<sigma>))`
    `\<not> dom_trm y (cl_ecl (subst_ecl C \<sigma>))` show False by auto
qed

lemma ck_trms_sound:
  assumes "T = get_trms D (dom_trms C E) k"
  shows "T \<subseteq> (dom_trms C E)"
proof (cases)
  assume "k = FirstOrder"
  from this and assms have "T = filter_trms D (dom_trms C E)"
    unfolding get_trms_def by auto
  from this show ?thesis using filter_trms_inclusion by blast
next
  assume "k \<noteq> FirstOrder"
  from this and assms have "T = (dom_trms C E)"
    unfolding get_trms_def by auto
  from this show ?thesis using filter_trms_inclusion by blast
qed

lemma derivable_clauses_are_well_constrained:
  assumes "derivable C P S \<sigma> k C'"
  shows "well_constrained C"
proof (rule ccontr)
  assume hyp: "\<not> well_constrained C" 
  then obtain y where "y \<in> trms_ecl C" and "\<not> dom_trm y (cl_ecl C)"
    unfolding well_constrained_def by auto
  have not_sup: "\<not> (\<exists>P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> superposition P1 P2 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> superposition P1 P2 C \<sigma> k C'))"
    then obtain P1 P2 where "P1 \<in> S" "P2 \<in> S" "superposition P1 P2 C \<sigma> k C'" by auto
    from `superposition P1 P2 C \<sigma> k C'` obtain Cl_C T E
      where 
        "T = (get_trms Cl_C (dom_trms Cl_C (subst_set E \<sigma>)) k)"
        "Cl_C = (subst_cl C' \<sigma>)"
        "C = (Ecl Cl_C T)"
        unfolding superposition_def by blast
    from `T = (get_trms Cl_C (dom_trms Cl_C (subst_set E \<sigma>)) k)`
      have "T \<subseteq>(dom_trms Cl_C (subst_set E \<sigma>))" 
      using ck_trms_sound  by metis
    from this and `y \<in> trms_ecl C` and `C = (Ecl Cl_C T)` have 
      "y \<in> (dom_trms (cl_ecl C) (subst_set E \<sigma>))" by auto
    from this and `\<not> dom_trm y (cl_ecl C)` show False unfolding dom_trms_def by auto
  qed
  have not_ref: "\<not> (\<exists>P1. (P1 \<in> S \<and> reflexion P1 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> S \<and> reflexion P1 C \<sigma> k C'))"
    then obtain P1 where "P1 \<in> S" "reflexion P1 C \<sigma> k C'" by auto
    from `reflexion P1 C \<sigma> k C'` obtain T Cl_C E where
        "T = (get_trms Cl_C (dom_trms Cl_C (subst_set E \<sigma>)) k)"
        "Cl_C = (subst_cl C' \<sigma>)"
        "C = (Ecl Cl_C T)"
      unfolding reflexion_def by blast
    from `T = (get_trms Cl_C (dom_trms Cl_C (subst_set E \<sigma>)) k)`
      have "T \<subseteq>(dom_trms Cl_C (subst_set E \<sigma>))" 
      using ck_trms_sound  by metis
    from this and `y \<in> trms_ecl C` and `C = (Ecl Cl_C T)` have 
      "y \<in> (dom_trms (cl_ecl C) (subst_set E \<sigma>))" by auto
    from this and `\<not> dom_trm y (cl_ecl C)` show False unfolding dom_trms_def by auto
  qed
  have not_fact: "\<not> (\<exists>P1. (P1 \<in> S \<and> factorization P1 C \<sigma> k C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> S \<and> factorization P1 C \<sigma> k C'))"
    then obtain P1 where "P1 \<in> S" "factorization P1 C \<sigma> k C'" by auto
    from `factorization P1 C \<sigma> k C'` obtain T Cl_C E where
        "T = (get_trms Cl_C (dom_trms Cl_C (subst_set E \<sigma>)) k)"
        "Cl_C = (subst_cl C' \<sigma>)"
        "C = (Ecl Cl_C T)"
      unfolding factorization_def by blast
    from `T = (get_trms Cl_C (dom_trms Cl_C (subst_set E \<sigma>)) k)`
      have "T \<subseteq>(dom_trms Cl_C (subst_set E \<sigma>))" 
      using ck_trms_sound  by metis
    from this and `y \<in> trms_ecl C` and `C = (Ecl Cl_C T)` have 
      "y \<in> (dom_trms (cl_ecl C) (subst_set E \<sigma>))" by auto
    from this and `\<not> dom_trm y (cl_ecl C)` show False unfolding dom_trms_def by auto
  qed
  from not_sup not_ref not_fact and assms(1) show False unfolding derivable_def by blast
qed

lemma derivable_clauses_are_entailed:
  assumes "derivable C P S \<sigma> k C'"
  assumes "validate_clause_set I (cl_ecl ` P)"
  assumes "fo_interpretation I"
  assumes "\<forall>x \<in> P. (finite (cl_ecl x))"
  shows "validate_clause I (cl_ecl C)"
proof (rule ccontr)
  assume "\<not>validate_clause I (cl_ecl C)"
  have not_sup: "\<not> (\<exists>P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> P = { P1, P2 } \<and> superposition P1 P2 C \<sigma> k C'))"
  proof 
    assume "(\<exists>P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> P = { P1, P2 } \<and> superposition P1 P2 C \<sigma> k C'))"
    from this obtain P1 P2 where "P1 \<in> P" "P2 \<in> P" and "superposition P1 P2 C \<sigma> k C'" by auto
    from `P1 \<in> P` and assms(2) have "validate_clause I (cl_ecl P1)" by auto
    from `P2 \<in> P` and assms(2) have "validate_clause I (cl_ecl P2)" by auto
    from assms(4) and `P1 \<in> P` have "finite (cl_ecl P1)" by auto
    from assms(4) and `P2 \<in> P` have "finite (cl_ecl P2)" by auto
    from assms(3) and `finite (cl_ecl P1)` and `finite (cl_ecl P2)` 
      and `superposition P1 P2 C \<sigma> k C'` have "set_entails_clause { (cl_ecl P1), (cl_ecl P2) } (cl_ecl C)" 
      using superposition_is_sound by blast
    from this and assms(3) and `validate_clause I (cl_ecl P1)` and `validate_clause I (cl_ecl P2)`
      have "validate_clause I (cl_ecl C)" 
      using set_entails_clause_def [of "{ (cl_ecl P1), (cl_ecl P2) }" "cl_ecl C"] by auto
    from this and `\<not>validate_clause I (cl_ecl C)` show False by auto
  qed
  have not_fact: "\<not> (\<exists>P1. (P1 \<in> S \<and> P = { P1 } \<and> factorization P1 C \<sigma> k C'))"
  proof 
    assume "(\<exists>P1. (P1 \<in> S \<and> P = { P1 } \<and> factorization P1 C \<sigma> k C'))"
    from this obtain P1 where "P1 \<in> P" and "factorization P1 C \<sigma> k C'" by auto
    from `P1 \<in> P` and assms(2) have "validate_clause I (cl_ecl P1)" by auto
    from assms(4) and `P1 \<in> P` have "finite (cl_ecl P1)" by auto
    from assms(3) and `finite (cl_ecl P1)` and  
      `factorization P1 C \<sigma> k C'` have "clause_entails_clause (cl_ecl P1) (cl_ecl C)" 
      using factorization_is_sound by auto
    from this and assms(3) and `validate_clause I (cl_ecl P1)`
      have "validate_clause I (cl_ecl C)" unfolding clause_entails_clause_def by auto
    from this and `\<not>validate_clause I (cl_ecl C)` show False by auto
  qed
  have not_ref: "\<not> (\<exists>P1. (P1 \<in> S \<and> P = { P1 } \<and> reflexion P1 C \<sigma> k C'))"
  proof 
    assume "(\<exists>P1. (P1 \<in> S \<and> P = { P1 } \<and> reflexion P1 C \<sigma> k C'))"
    from this obtain P1 where "P1 \<in> P" and "reflexion  P1 C \<sigma> k C'" by auto
    from `P1 \<in> P` and assms(2) have "validate_clause I (cl_ecl P1)" by auto
    from assms(4) and `P1 \<in> P` have "finite (cl_ecl P1)" by auto
    from assms(3) and `finite (cl_ecl P1)` and  
      `reflexion P1 C \<sigma> k C'` have "clause_entails_clause (cl_ecl P1) (cl_ecl C)" 
      using reflexion_is_sound by auto
    from this and assms(3) and `validate_clause I (cl_ecl P1)`
      have "validate_clause I (cl_ecl C)" unfolding clause_entails_clause_def by auto
    from this and `\<not>validate_clause I (cl_ecl C)` show False by auto
  qed
  from not_sup not_fact not_ref and assms(1) show False unfolding derivable_def by blast
qed

lemma all_derived_clauses_are_finite:
  shows "derivable_ecl C S \<Longrightarrow> \<forall>x \<in> S. (finite (cl_ecl x)) \<Longrightarrow> finite (cl_ecl C)"
proof (induction rule: derivable_ecl.induct)
  fix C :: "'a eclause" fix S assume "C \<in> S"
  assume "\<forall>x \<in> S. (finite (cl_ecl x))"
  from this `C \<in> S` show "finite (cl_ecl C)" by auto      
next
  fix C S fix D :: "'a eclause" assume "derivable_ecl C S" 
  assume "\<forall>x \<in> S. (finite (cl_ecl x))" assume hyp_ind: "\<forall>x \<in> S. (finite (cl_ecl x)) \<Longrightarrow> finite (cl_ecl C)"  
    "(renaming_cl C D)"
  from `(renaming_cl C D)` obtain \<eta> where "D = (subst_ecl C \<eta>)" 
    unfolding renaming_cl_def by auto
  obtain C_Cl T where "C = (Ecl C_Cl T)" using "eclause.exhaust" by auto
  from this and `D = (subst_ecl C \<eta>)` 
    have "(cl_ecl D) = (subst_cl (cl_ecl C) \<eta>)" by auto
  from this hyp_ind `\<forall>x \<in> S. (finite (cl_ecl x))` show "finite (cl_ecl D)" 
    using substs_preserve_finiteness by auto
next
  fix P S C S' \<sigma> C' 
  assume h: "\<forall>x. x \<in> P \<longrightarrow> derivable_ecl x S \<and> ((\<forall>x\<in>S. finite (cl_ecl x)) \<longrightarrow> finite (cl_ecl x))" 
  assume "derivable C P S' \<sigma> FirstOrder C'"
  assume "\<forall>x\<in>S. finite (cl_ecl x)"
  from h and `\<forall>x\<in>S. finite (cl_ecl x)` have "\<forall>x \<in> P. (finite (cl_ecl x))" by metis
  from this and `derivable C P S' \<sigma> FirstOrder C'` show "finite (cl_ecl C)" 
    using derivable_clauses_are_finite by auto 
qed

lemma all_derived_clauses_are_wellconstrained:
  shows "derivable_ecl C S \<Longrightarrow> \<forall>x \<in> S. (well_constrained x) \<Longrightarrow> well_constrained C"
proof (induction rule: derivable_ecl.induct)
  fix C :: "'a eclause" fix S assume "C \<in> S"
  assume "\<forall>x \<in> S. (well_constrained x)"
  from this `C \<in> S` show "well_constrained C" by auto      
next
  fix C S fix D :: "'a eclause" assume "derivable_ecl C S" 
  assume "\<forall>x \<in> S. (well_constrained x)" assume hyp_ind: "\<forall>x \<in> S. (well_constrained x) \<Longrightarrow> well_constrained C"  
    "(renaming_cl C D)"
 from `\<forall>x \<in> S. (well_constrained x)` and hyp_ind have "well_constrained C" by auto
  from `(renaming_cl C D)` obtain \<eta> where "D = (subst_ecl C \<eta>)" 
    unfolding renaming_cl_def by auto
  from this and `well_constrained C` show "well_constrained D" 
    using substs_preserve_well_constrainedness by auto
next
  fix P S C S' \<sigma> C' 
  assume "\<forall>x. x \<in> P \<longrightarrow> derivable_ecl x S \<and> (Ball S well_constrained \<longrightarrow> well_constrained x)" 
  assume "derivable C P S' \<sigma> FirstOrder C'"
  assume "Ball S well_constrained"
  from `derivable C P S' \<sigma> FirstOrder C'` show "well_constrained C" 
    using derivable_clauses_are_well_constrained by auto
qed

lemma SOUNDNESS:
  shows "derivable_ecl C S \<Longrightarrow> \<forall>x \<in> S. (finite (cl_ecl x)) 
    \<Longrightarrow> set_entails_clause (cl_ecl ` S) (cl_ecl C)"
proof (induction rule: derivable_ecl.induct)
  fix C :: "'a eclause" fix S assume "C \<in> S"
  assume "\<forall>x \<in> S. (finite (cl_ecl x))"
  from `C \<in> S` show "set_entails_clause (cl_ecl ` S) (cl_ecl C)" 
          unfolding set_entails_clause_def by auto
next
  fix C S fix D :: "'a eclause" assume "derivable_ecl C S" 
  assume "\<forall>x \<in> S. (finite (cl_ecl x))" 
  assume hyp_ind: "\<forall>x \<in> S. (finite (cl_ecl x)) \<Longrightarrow> set_entails_clause (cl_ecl ` S) (cl_ecl C)"  
  assume  "(renaming_cl C D)"
  from `(renaming_cl C D)` obtain \<eta> where "D = (subst_ecl C \<eta>)" 
    unfolding renaming_cl_def by auto
  obtain C_Cl T where "C = (Ecl C_Cl T)" using "eclause.exhaust" by auto
  from this and `D = (subst_ecl C \<eta>)` 
    have "(cl_ecl D) = (subst_cl (cl_ecl C) \<eta>)" by auto
  show "set_entails_clause (cl_ecl ` S) (cl_ecl D)"
  proof (rule ccontr)
    assume "\<not>?thesis"
    from this obtain I where "fo_interpretation I" and i: "validate_clause_set I (cl_ecl `S)" 
      "\<not>validate_clause I (cl_ecl D)" 
      unfolding set_entails_clause_def by auto
    from `\<not>validate_clause I (cl_ecl D)` and `(cl_ecl D) = (subst_cl (cl_ecl C) \<eta>)`
      have "\<not>validate_clause I (cl_ecl C)" using instances_are_entailed by metis
    from this and `fo_interpretation I` i have "\<not>set_entails_clause (cl_ecl ` S) (cl_ecl C)"
      unfolding set_entails_clause_def by auto
    from this and `\<forall>x \<in> S. (finite (cl_ecl x))` hyp_ind show False by auto
  qed
next
  fix P S C S' \<sigma> C' 
  assume h: "\<forall>x. x \<in> P \<longrightarrow> derivable_ecl x S \<and> ((\<forall>x\<in>S. finite (cl_ecl x)) \<longrightarrow> set_entails_clause (cl_ecl ` S) (cl_ecl x))" 
  assume "derivable C P S' \<sigma> FirstOrder C'"
  assume "\<forall>x\<in>S. finite (cl_ecl x)"
  from h and `\<forall>x\<in>S. finite (cl_ecl x)` have i: "\<forall>x \<in> P.  set_entails_clause (cl_ecl ` S) (cl_ecl x)" 
    by metis
  show "set_entails_clause (cl_ecl ` S) (cl_ecl C)"
  proof (rule ccontr)
    assume "\<not>?thesis"
    from this obtain I where "fo_interpretation I" and ii: "validate_clause_set I (cl_ecl `S)" 
      "\<not>validate_clause I (cl_ecl C)" 
      unfolding set_entails_clause_def by auto
    from h `\<forall>x\<in>S. finite (cl_ecl x)` have "(\<forall>x\<in>P. finite (cl_ecl x))"
     using all_derived_clauses_are_finite by metis
    from `fo_interpretation I`  i and ii 
      have "\<forall>x \<in> P.  (validate_clause I (cl_ecl x))" unfolding set_entails_clause_def by auto
    from this have "validate_clause_set I (cl_ecl ` P)"  by auto
    from this and `(\<forall>x\<in>P. finite (cl_ecl x))` `fo_interpretation I` `derivable C P S' \<sigma> FirstOrder C'` 
      have "validate_clause I (cl_ecl C)" 
      using derivable_clauses_are_entailed [of C P S' \<sigma> FirstOrder C' I] by blast 
    from this and `\<not>validate_clause I (cl_ecl C)` show False by auto
 qed
qed

lemma REFUTABLE_SETS_ARE_UNSAT:
  assumes "\<forall>x \<in> S. (finite (cl_ecl x))"
  assumes "derivable_ecl C S"
  assumes "(cl_ecl C = {})"
  shows "\<not> (satisfiable_clause_set (cl_ecl ` S))"
proof 
  assume "(satisfiable_clause_set (cl_ecl ` S))"
  then obtain I where "fo_interpretation I" and model: "validate_clause_set I (cl_ecl ` S)" 
    unfolding satisfiable_clause_set_def [of "cl_ecl ` S"] by blast
  from assms(1) assms(2) have "set_entails_clause (cl_ecl ` S) (cl_ecl C)"
    using SOUNDNESS by metis
  from this `fo_interpretation I` and model have "validate_clause I (cl_ecl C)" 
    unfolding set_entails_clause_def by auto
  from this and assms(3) show False by auto
qed

section {* Redundancy Criteria and Saturated Sets *}

text {* We define redundancy criteria. We use similar notions as in the Bachmair and Ganzinger
paper, the only difference is that we have to handle the sets of irreducible terms associated
with the clauses. Indeed, to ensure completeness, we must guarantee that all the terms that are 
irreducible in the entailing clauses are also irreducible in the entailed one 
(otherwise some needed inferences could be blocked due the irreducibility condition, as in the basic 
superposition calculus). Of course, if the attached sets of terms are empty, then this condition 
trivially holds and the definition collapses to the usual one. 

We introduce the following relation: *}

definition subterms_inclusion :: "'a trm set \<Rightarrow> 'a trm set \<Rightarrow> bool"
  where "subterms_inclusion E1 E2 = (\<forall>x1 \<in> E1. \<exists>x2 \<in> E2. (occurs_in x1 x2))"

lemma subterms_inclusion_refl:
 shows "subterms_inclusion E E"
proof (rule ccontr)
  assume "\<not>subterms_inclusion E E"
  from this obtain x1 where "x1 \<in> E" and "\<not> occurs_in x1 x1" unfolding subterms_inclusion_def by force
  from `\<not> occurs_in x1 x1` have "\<not> (\<exists>p. subterm x1 p x1)"  unfolding occurs_in_def by auto
  from this have "\<not>subterm x1 Nil x1" by metis
  from this show False by auto
qed

lemma subterms_inclusion_subset:
  assumes "subterms_inclusion E1 E2"
  assumes "E2 \<subseteq> E2'"
  shows "subterms_inclusion E1 E2'"
by (meson assms(1) assms(2) basic_superposition.subterms_inclusion_def basic_superposition_axioms 
      set_mp)

lemma set_inclusion_preserve_normalization:
  assumes "all_trms_irreducible E f"
  assumes "E' \<subseteq> E"
  shows "all_trms_irreducible E' f"
by (meson all_trms_irreducible_def assms(1) assms(2) set_mp)

lemma subterms_inclusion_preserves_normalization:
  assumes "all_trms_irreducible E f"
  assumes "subterms_inclusion E' E"
  shows "all_trms_irreducible E' f"
by (meson all_trms_irreducible_def assms(1) assms(2) occur_in_subterm subterms_inclusion_def)

text {* We define two notions of redundancy, the first one is for inferences: any derivable clause 
must be entailed by a set of clauses that are strictly smaller than one of the premises. *}

definition redundant_inference :: 
  "'a eclause \<Rightarrow> 'a eclause set \<Rightarrow> 'a eclause set \<Rightarrow> 'a subst \<Rightarrow> bool"
  where "(redundant_inference C S P \<sigma>) = 
    (\<exists>S'. (S' \<subseteq> (instances S) \<and> (set_entails_clause (clset_instances S') (cl_ecl C)) \<and> 
            (\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl C))) \<and>
            (\<forall>x \<in> S'. \<exists>D' \<in> P. (((fst x),(snd x)),(D',\<sigma>)) \<in> ecl_ord)))"

text {* The second one is the usual notion for clauses: a clause is redundant if it is entailed by
smaller (or equal) clauses. *}

definition redundant_clause :: 
  "'a eclause \<Rightarrow> 'a eclause set  \<Rightarrow> 'a subst \<Rightarrow> 'a clause \<Rightarrow> bool"
  where "(redundant_clause C S \<sigma> C') = 
    (\<exists>S'. (S' \<subseteq> (instances S) \<and> (set_entails_clause (clset_instances S') (cl_ecl C)) \<and> 
            (\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl C))) \<and>
            (\<forall>x \<in> S'. ( ((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<sigma>))) \<in> (mult (mult trm_ord))
              \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>)))))"

text {* Note that according to the definition above, an extended clause is always 
redundant w.r.t.\ a clause obtained from the initial one by adding in the attached set of 
terms a subterm of a term that already occurs in this set. This remark is important because 
explicitly adding such subterms in the attached set may prune the search space, due to the fact 
that the containing term can be removed at some point when calling the function @{term "dom_trm"}.
Adding the subterm explicitly is thus useful in this case. In practice, the simplest solution may be 
to assume that the set of irreducible terms is closed under subterm. 

Of course, a clause is also redundant w.r.t.\ any clause obtained by removing terms in the attached
set. In particular, terms can be safely removed from the set of irreducible terms of the entailing 
clauses if needed to make a given clause redundant.*}

lemma self_redundant_clause:
  assumes "C \<in> S"
  assumes "C' = (cl_ecl C)"
  assumes "ground_clause (subst_cl (cl_ecl C) \<sigma>)"
  shows "redundant_clause (subst_ecl C \<sigma>) S \<sigma> C'"
proof -
  obtain Cl_C and T where "C = Ecl Cl_C T" using eclause.exhaust by auto
  from this have "cl_ecl C = Cl_C" and "trms_ecl C = T" by auto
  let ?Cl_C = "subst_cl Cl_C \<sigma>"
  let ?T  = "subst_set T \<sigma>"
  let ?C = "subst_ecl C \<sigma>"
  from `C = Ecl Cl_C T` have "?C = (Ecl ?Cl_C ?T)" by auto
  from this have "cl_ecl ?C = ?Cl_C" and "trms_ecl ?C = ?T" by auto
  let ?S = "{ (C,\<sigma>) }"
  from assms(1) assms(3) have i: "?S \<subseteq> (instances S)" unfolding instances_def by auto 
  from `cl_ecl C = Cl_C` have "clset_instances ?S = { ?Cl_C }" unfolding clset_instances_def 
    by auto
  from this and `cl_ecl ?C = ?Cl_C` have ii: "set_entails_clause (clset_instances ?S) (cl_ecl ?C)"
    using set_entails_clause_member by force
  have iii: "(\<forall>x \<in> ?S. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl ?C)))"
  proof 
    fix x assume "x \<in> ?S" 
    from this have "x = (C,\<sigma>)" by auto
    from this `C = Ecl Cl_C T` 
      have "subst_set (trms_ecl (fst x)) (snd x) = ?T" by auto
    from this and `trms_ecl ?C = ?T`
      have "subst_set (trms_ecl (fst x)) (snd x) = (trms_ecl ?C)" by auto
    from this show "( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl ?C))" 
              using subterms_inclusion_refl by auto
  qed
  have iv: "(\<forall>x \<in> ?S. ( ((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<sigma>))) \<in> (mult (mult trm_ord))
              \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>)))"
  proof 
    fix x assume "x \<in> ?S"
    from this have "x = (C,\<sigma>)" by auto
    from this `C = Ecl Cl_C T` have "(mset_ecl ((fst x),(snd x))) = (mset_ecl (C,\<sigma>))" by auto
    from this `C' = (cl_ecl C)` have "(mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>)" by auto
    from this show "( ((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<sigma>))) \<in> (mult (mult trm_ord))
              \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>))" by auto
  qed
  from i ii iii iv show ?thesis unfolding redundant_clause_def by metis
qed

definition trms_subsumes
  where "trms_subsumes C D \<sigma>
    = ( (subst_cl (cl_ecl C) \<sigma>) = (cl_ecl D) 
    \<and> ((subst_set (trms_ecl C) \<sigma>) \<subseteq> trms_ecl D))"

definition inference_closed 
  where "inference_closed S  = (\<forall> P C' D \<theta>. 
      (derivable D P S \<theta> FirstOrder C') \<longrightarrow> (D \<in> S))"

text {* Various notions of saturatedness are defined, depending on the kind of inferences that are 
considered and on the redundancy criterion.*}

text {* The first definition is the weakest one: all ground inferences must be redundant (this 
definition is used for the completeness proof to make it the most general). *}

definition ground_inference_saturated :: "'a eclause set \<Rightarrow> bool"
  where "(ground_inference_saturated S) = (\<forall> C P \<sigma> C'. (derivable C P S \<sigma> Ground C') \<longrightarrow> 
      (ground_clause (cl_ecl C)) \<longrightarrow> (grounding_set P \<sigma>) \<longrightarrow> (redundant_inference C S P \<sigma>))"

text {* The second one states that every ground instance of a first-order inference must be 
redundant. *}

definition inference_saturated :: "'a eclause set \<Rightarrow> bool"
  where "(inference_saturated S) = (\<forall> C P \<sigma> C' D \<theta> \<eta>. 
     (derivable C P S \<sigma> Ground C') \<longrightarrow> (ground_clause (cl_ecl C)) \<longrightarrow> (grounding_set P \<sigma>) 
      \<longrightarrow> (derivable D P S \<theta> FirstOrder C') \<longrightarrow> (trms_subsumes D C \<eta>)
      \<longrightarrow> (\<sigma> \<doteq> \<theta> \<lozenge> \<eta>)
      \<longrightarrow> (redundant_inference (subst_ecl D \<eta>) S P \<sigma>))"

text {* The last definition is the most restrictive one: every derivable clause must be 
redundant. *}

definition clause_saturated :: "'a eclause set \<Rightarrow> bool"
  where "(clause_saturated S) = (\<forall> C P \<sigma> C' D \<theta> \<eta>. 
     (derivable C P S \<sigma> Ground C') \<longrightarrow> (ground_clause (cl_ecl C)) 
      \<longrightarrow> (derivable D P S \<theta> FirstOrder C') \<longrightarrow> (trms_subsumes D C \<eta>)
      \<longrightarrow> (\<sigma> \<doteq> \<theta> \<lozenge> \<eta>)
      \<longrightarrow> (redundant_clause (subst_ecl D \<eta>) S \<sigma> C'))"

text {* We now relate these various notions, so that the forthcoming completeness proof applies
to all of them. To this purpose, we have to show that the conclusion of a (ground) inference rule 
is always strictly smaller than one of the premises. *}

lemma conclusion_is_smaller_than_premisses:
  assumes "derivable C P S \<sigma> Ground C'"
  assumes "\<forall>x \<in> S. (finite (cl_ecl x))" 
  assumes "grounding_set P \<sigma>" 
  shows "\<exists> D. (D \<in> P \<and> (( (mset_cl (C',\<sigma>)), (mset_ecl (D,\<sigma>))) \<in> (mult (mult trm_ord))))"
proof (rule ccontr)
  assume hyp: "\<not> (\<exists> D. (D \<in> P \<and> (( (mset_cl (C',\<sigma>)), (mset_ecl (D,\<sigma>))) \<in> (mult (mult trm_ord)))))" 
  from assms(1) have "P \<subseteq> S" unfolding derivable_def by auto
  have not_sup: "\<not> (\<exists>P1 P2. (P1 \<in> P \<and> P2 \<in> P \<and> superposition P1 P2 C \<sigma> Ground C'))"
  proof
    assume "(\<exists>P1 P2. (P1 \<in> P \<and> P2 \<in> P \<and> superposition P1 P2 C \<sigma> Ground C'))"
    then obtain P1 P2 where "P1 \<in> P" "P2 \<in> P" "superposition P1 P2 C \<sigma> Ground C'" by auto
    from `superposition P1 P2 C \<sigma> Ground C'` obtain L t s u v M  L' polarity u' p t' Cl_C NT where
      "M \<in> (cl_ecl P2)" "L \<in> (cl_ecl P1)"
      "orient_lit_inst M u v pos \<sigma>" 
      "orient_lit_inst L t s polarity \<sigma>" 
      "subterm t p u'"
      "ck_unifier u' u \<sigma> Ground"
      "replace_subterm t p v t'"
      "L' = mk_lit polarity (Eq t' s)" 
      "(C = (Ecl Cl_C NT))"
      "(subst u \<sigma>) \<noteq> (subst v \<sigma>)" 
      "( (subst_lit M \<sigma>),(subst_lit L \<sigma>)) 
            \<in> lit_ord"
      "strictly_maximal_literal P2 M \<sigma>"
      "Cl_C = (subst_cl (((cl_ecl P1) - { L }) \<union> (((cl_ecl P2) - { M }) \<union> { L' } )) \<sigma>)"
      "C' = (((cl_ecl P1) - { L }) \<union> (((cl_ecl P2) - { M }) \<union> { L' } ))"
      unfolding superposition_def by blast 
    from `P1 \<in> P` and assms(2) and `P \<subseteq> S` have "finite (cl_ecl P1)" by auto
    from `P2 \<in> P` and assms(2) and `P \<subseteq> S` have "finite (cl_ecl P2)" by auto

    from assms(3) and `P2 \<in> P` have "ground_clause (subst_cl (cl_ecl P2) \<sigma>)" 
      unfolding grounding_set_def by auto 
    from this have "vars_of_cl (subst_cl (cl_ecl P2) \<sigma>) = {}" by auto
    from `M \<in> (cl_ecl P2)`have "(subst_lit M \<sigma>) \<in> (subst_cl (cl_ecl P2) \<sigma>)" by auto
    from this and `vars_of_cl (subst_cl (cl_ecl P2) \<sigma>) = {}` have "vars_of_lit (subst_lit M \<sigma>) = {}"
      by auto
    from `orient_lit_inst M u v pos \<sigma>` have 
      "orient_lit (subst_lit M \<sigma>) (subst u \<sigma>) (subst v \<sigma>) pos" 
      using lift_orient_lit by auto
    from this and `vars_of_lit (subst_lit M \<sigma>) = {}` have "vars_of (subst u \<sigma>) = {}" 
       using orient_lit_vars by blast
    from `orient_lit (subst_lit M \<sigma>) (subst u \<sigma>) (subst v \<sigma>) pos`
      and `vars_of_lit (subst_lit M \<sigma>) = {}` have "vars_of (subst v \<sigma>) = {}" 
       using orient_lit_vars by blast
    from `orient_lit (subst_lit M \<sigma>) (subst u \<sigma>) (subst v \<sigma>) pos` 
      have "((subst u \<sigma>),(subst v \<sigma>)) \<notin> trm_ord" 
      unfolding orient_lit_def by auto
    from this and `(subst u \<sigma>) \<noteq> (subst v \<sigma>)` 
      and `vars_of (subst u \<sigma>) = {}` `vars_of (subst v \<sigma>) = {}` 
       have "((subst v \<sigma>),(subst u \<sigma>)) \<in> trm_ord"  using trm_ord_ground_total 
       unfolding ground_term_def by blast

    from assms(3) and `P1 \<in> P` have "ground_clause (subst_cl (cl_ecl P1) \<sigma>)" unfolding grounding_set_def  by auto 
    from this have "vars_of_cl (subst_cl (cl_ecl P1) \<sigma>) = {}" by auto
    from `L \<in> (cl_ecl P1)`have "(subst_lit L \<sigma>) \<in> (subst_cl (cl_ecl P1) \<sigma>)" by auto
    from this and `vars_of_cl (subst_cl (cl_ecl P1) \<sigma>) = {}` have "vars_of_lit (subst_lit L \<sigma>) = {}"
      by auto
    from `orient_lit_inst L t s polarity \<sigma>` have 
      "orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) polarity" 
      using lift_orient_lit by auto
    from this and `vars_of_lit (subst_lit L \<sigma>) = {}` have "vars_of (subst t \<sigma>) = {}" 
       using orient_lit_vars by blast
    from `orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) polarity` 
       and `vars_of_lit (subst_lit L \<sigma>) = {}` have "vars_of (subst s \<sigma>) = {}" 
       using orient_lit_vars by blast

    let ?mC1 = "mset_ecl (P1, \<sigma>)"
    let ?mC2 = "mset_ecl (C, \<sigma>)"

    from `L \<in> (cl_ecl P1)` `finite (cl_ecl P1)` 
      have "mset_set (cl_ecl P1) = mset_set ((cl_ecl P1)-{ L }) + mset_set { L }"
      using split_mset_set [of "cl_ecl P1" "cl_ecl P1 - { L }" "{ L }"] by blast

    from this have  d1: "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set (cl_ecl P1)) #}
      = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L })) #} 
        + {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L }) #}"
        using split_image_mset by auto
    
    let ?C = "(((cl_ecl P1) - { L }) \<union> (((cl_ecl P2) - { M }) \<union> { L' } ))"
    from `finite (cl_ecl P1)` `finite (cl_ecl P2)` have "finite ?C" by auto
    let ?C' = "?C - ( (cl_ecl P1) - { L })"
    from `finite ?C` have "finite ?C'" by auto
    have "?C = ( (cl_ecl P1) - { L }) \<union> ?C'" by auto
    from `finite (cl_ecl P1)` `finite ?C'` 
      have "mset_set ?C = mset_set ((cl_ecl P1)-{ L }) + mset_set ?C'"
      using split_mset_set [of "?C" "cl_ecl P1 - { L }" "?C'"] by blast

    from this have  d2: "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C) #}
      = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L })) #} 
        + {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"
        using split_image_mset by auto
    
    have "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L }) #} \<noteq> {#}"
      by auto
   let ?K = "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"
   let ?J = "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L }) #}"
   have "(\<forall>k \<in> set_mset ?K. \<exists>j \<in> set_mset ?J. (k, j) \<in> (mult trm_ord))"
   proof 
    fix k assume "k \<in> set_mset ?K"
    from this have "k \<in># ?K" by auto
    from this obtain M' where "M' \<in># (mset_set ?C')" and "k = (mset_lit (subst_lit M' \<sigma>))"
      using image_mset_thm [of "?K"  "\<lambda>x. (mset_lit (subst_lit x \<sigma>))" "(mset_set ?C')"]
      by metis

    from `M' \<in># (mset_set ?C')`and `finite ?C'` have "M' \<in> ?C'" by auto
    have "L \<in># (mset_set { L })" by auto
    from this have "(mset_lit (subst_lit L \<sigma>) \<in># ?J)" by auto
    from this have "(mset_lit (subst_lit L \<sigma>) \<in> set_mset ?J)" by auto
 
  have "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L }) #} \<noteq> {#}" by auto


    show "\<exists>j \<in> set_mset ?J. (k, j) \<in> (mult trm_ord)"
    proof (cases)
      assume "M' \<in> (cl_ecl P2) - { M }"  
      from this and `strictly_maximal_literal P2 M \<sigma>` 
        have "((subst_lit M' \<sigma>),(subst_lit M \<sigma>)) \<in> lit_ord" 
          unfolding strictly_maximal_literal_def by metis
      from this and `( (subst_lit M \<sigma>),(subst_lit L \<sigma>)) \<in> lit_ord` 
        have "((subst_lit M' \<sigma>),(subst_lit L \<sigma>)) \<in> lit_ord"
        using lit_ord_trans unfolding trans_def by metis
      from this have "((mset_lit (subst_lit M' \<sigma>)), 
                (mset_lit (subst_lit L \<sigma>))) \<in>  (mult trm_ord)"
             unfolding lit_ord_def by auto
      from `(mset_lit (subst_lit L \<sigma>) \<in> set_mset ?J)` this `((mset_lit (subst_lit M' \<sigma>)), 
                (mset_lit (subst_lit L \<sigma>))) \<in>  (mult trm_ord)` 
       and `k = (mset_lit (subst_lit M' \<sigma>))` show ?thesis by blast
   next assume "M' \<notin> (cl_ecl P2) - { M }"
    from this and `M' \<in> ?C'` have "M' = L'" by auto
    from `subterm t p u'` have "subterm (subst t \<sigma>) p  (subst u' \<sigma>)"
      using substs_preserve_subterms by blast 
    from `ck_unifier u' u \<sigma> Ground` have 
      "(subst u \<sigma>) = (subst u' \<sigma>)" unfolding ck_unifier_def Unifier_def  by auto
    from this and `((subst v \<sigma>),(subst u \<sigma>)) \<in> trm_ord` 
      have "((subst v \<sigma>),(subst u' \<sigma>)) \<in> trm_ord" by auto
    from this `subterm t p u'` `replace_subterm t p v t'`
      have "((subst t' \<sigma>),(subst t \<sigma>)) \<in> trm_ord" 
      using replacement_monotonic by auto
    have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto
    then have "((subst_lit L' \<sigma>),(subst_lit L \<sigma>)) \<in> lit_ord"
    proof 
      assume "polarity = pos"
      from this and `orient_lit_inst L t s polarity \<sigma>` 
        have i: "(mset_lit (subst_lit L \<sigma>)) = {# (subst s \<sigma>) #} + {# (subst t \<sigma>) #}"
          unfolding orient_lit_inst_def using add.commute by force 
        from  `L' = mk_lit polarity (Eq t' s)` `polarity = pos` 
          have ii: "(mset_lit (subst_lit L' \<sigma>)) = {# (subst s \<sigma>) #} 
          + {# (subst t' \<sigma>) #}"
           using add.commute by force
        have "{# (subst t \<sigma>) #} \<noteq> {#}" by auto
        have "(\<forall>k' \<in> set_mset {# (subst t' \<sigma>) #}. \<exists>j' \<in> set_mset {# (subst t \<sigma>) #}. (k', j') \<in> (trm_ord))"
        proof 
          fix k' assume "k' \<in>set_mset {# (subst t' \<sigma>) #}"
          from this have "k' = (subst t' \<sigma>)" by auto
          have "(subst t \<sigma>) \<in> set_mset {# (subst t \<sigma>) #}" by auto
          from this `k' = (subst t' \<sigma>)` 
            and `((subst t' \<sigma>),(subst t \<sigma>)) \<in> trm_ord` 
            show "\<exists>j' \<in> set_mset {# (subst t \<sigma>) #}. (k', j') \<in> (trm_ord)" 
              by auto
        qed
        from i ii 
          `((subst t' \<sigma>),(subst t \<sigma>)) \<in> trm_ord` 
          have "(mset_lit (subst_lit L' \<sigma>),(mset_lit (subst_lit L \<sigma>))) 
            \<in> (mult trm_ord)"
            by (metis one_step_implies_mult empty_iff insert_iff set_mset_add_mset_insert set_mset_empty)
        from this show ?thesis unfolding lit_ord_def by auto

      next 
        assume "polarity = neg"
        
        from this and `orient_lit_inst L t s polarity \<sigma>` 
        have i: "(mset_lit (subst_lit L \<sigma>)) = {# (subst s \<sigma>), (subst s \<sigma>) #} 
          + {# (subst t \<sigma>), (subst t \<sigma>) #}"
          unfolding orient_lit_inst_def by auto
        from  `L' = mk_lit polarity (Eq t' s)` `polarity = neg` have 
          "subst_lit L' \<sigma> = (Neg (Eq (subst t' \<sigma>) (subst s \<sigma>)))" by auto
        from this have "(mset_lit (subst_lit L' \<sigma>))
          = {# (subst t' \<sigma>), (subst t' \<sigma>), (subst s \<sigma>), (subst s \<sigma>) #}"
          by auto
        from this have ii: "(mset_lit (subst_lit L' \<sigma>))
          = {# (subst s \<sigma>), (subst s \<sigma>) #} + {# (subst t' \<sigma>), (subst t' \<sigma>) #}"
          by (simp add: add.commute add.left_commute)

        have "{# (subst t \<sigma>), (subst t \<sigma>) #} \<noteq> {#}" by auto

        have "(\<forall>k' \<in> set_mset {# (subst t' \<sigma>),(subst t' \<sigma>) #}. 
          \<exists>j' \<in> set_mset {# (subst t \<sigma>),(subst t \<sigma>) #}. (k', j') \<in> (trm_ord))"
        proof 
          fix k' assume "k' \<in>set_mset {# (subst t' \<sigma>),(subst t' \<sigma>) #}"
          from this have "k' = (subst t' \<sigma>)" by auto
          have "(subst t \<sigma>) \<in> set_mset {# (subst t \<sigma>),(subst t \<sigma>) #}" by auto
          from this `k' = (subst t' \<sigma>)` 
            and `((subst t' \<sigma>),(subst t \<sigma>)) \<in> trm_ord` 
            show "\<exists>j' \<in> set_mset {# (subst t \<sigma>),(subst t \<sigma>) #}. (k', j') \<in> (trm_ord)" 
              by auto
        qed

        from this i ii `{# (subst t \<sigma>), (subst t \<sigma>) #} \<noteq> {#}`
          have "(mset_lit (subst_lit L' \<sigma>),
            (mset_lit (subst_lit L \<sigma>))) \<in> (mult trm_ord)"
             using one_step_implies_mult  [of "{# (subst t \<sigma>), (subst t \<sigma>) #}"
               "{# (subst t' \<sigma>),(subst t' \<sigma>) #}" trm_ord
               "{# (subst s \<sigma>),(subst s \<sigma>) #}"] 
             trm_ord_trans by auto
             
        from this show ?thesis unfolding lit_ord_def by auto
      qed
    from this and 
      `(mset_lit (subst_lit L \<sigma>) \<in> set_mset ?J)` 
      `k = (mset_lit (subst_lit M' \<sigma>))`
      `M' = L'` show ?thesis unfolding lit_ord_def by auto
    qed
  qed
  from this d1 d2  have o: "
      ({#mset_lit (subst_lit x \<sigma>). x \<in># mset_set ?C #},
      {#mset_lit (subst_lit x \<sigma>). x \<in># mset_set (cl_ecl P1)#})
     \<in> mult (mult trm_ord)"
  using  mult_trm_ord_trans one_step_implies_mult [of "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L }) #}"
      "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"  "mult trm_ord"
      "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L })) #} " ] by auto

  from this `C' = (((cl_ecl P1) - { L }) \<union> (((cl_ecl P2) - { M }) \<union> { L' } ))` and `P1 \<in> P` 
    and hyp  show False by auto
  qed

  have not_ref: "\<not> (\<exists>P1. (P1 \<in> P \<and> reflexion P1 C \<sigma> Ground C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> P \<and> reflexion P1 C \<sigma> Ground C'))"
    then obtain P1 where "P1 \<in> P" "reflexion P1 C \<sigma> Ground C'" by auto
    from `reflexion P1 C \<sigma> Ground C'` obtain L1 t s Cl_C Cl_P where
      "(eligible_literal L1 P1 \<sigma>)"
      "(L1 \<in> (cl_ecl P1))"  "(Cl_C = (cl_ecl C))" "(Cl_P = (cl_ecl P1))" 
      "(orient_lit_inst L1 t s neg \<sigma>)"
      "(ck_unifier t s \<sigma> Ground)"
      "(Cl_C = (subst_cl ((Cl_P - { L1 }) )) \<sigma>)"
      "(C' = ((Cl_P - { L1 }) ))"
      unfolding reflexion_def by blast 
    from `P1 \<in> P` and assms(2) and `P \<subseteq> S` have "finite (cl_ecl P1)" by auto
  
    let ?mC1 = "mset_ecl (P1, \<sigma>)"
    let ?mC2 = "mset_ecl (C, \<sigma>)"

    from `L1 \<in> (cl_ecl P1)` `finite (cl_ecl P1)` 
      have "mset_set (cl_ecl P1) = mset_set ((cl_ecl P1)-{ L1 }) + mset_set { L1 }"
      using split_mset_set [of "cl_ecl P1" "cl_ecl P1 - { L1 }" "{ L1 }"] by blast

    from this have  d1: "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set (cl_ecl P1)) #}
      = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L1 })) #} 
        + {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L1 }) #}"
        using split_image_mset by auto
    
    let ?C = "((cl_ecl P1) - { L1 })"
    from `finite (cl_ecl P1)` have "finite ?C" by auto
    let ?C' = "{}"
    have "finite ?C'" by auto
    have "?C = ( (cl_ecl P1) - { L1 }) \<union> ?C'" by auto
    from `finite (cl_ecl P1)` `finite ?C'` 
      have "mset_set ?C = mset_set ((cl_ecl P1)-{ L1 }) + mset_set ?C'"
      using split_mset_set [of "?C" "cl_ecl P1 - { L1 }" "?C'"] by blast

    from this have  d2: "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C) #}
      = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L1 })) #} 
        + {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"
        using split_image_mset by auto
    
    have "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L1 }) #} \<noteq> {#}"
      by auto
   let ?K = "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"
   let ?J = "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L1 }) #}"
   have "(\<forall>k \<in> set_mset ?K. \<exists>j \<in> set_mset ?J. (k, j) \<in> (mult trm_ord))" by auto 

  from this d1 d2  `{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L1 }) #} \<noteq> {#}`  
    have o: "
      ({#mset_lit (subst_lit x \<sigma>). x \<in># mset_set ?C #},
      {#mset_lit (subst_lit x \<sigma>). x \<in># mset_set (cl_ecl P1)#})
     \<in> mult (mult trm_ord)"
  using  mult_trm_ord_trans one_step_implies_mult [of
    "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L1 }) #}"
      "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"  "mult trm_ord" 
      "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L1 })) #} " ] by auto

  from this `Cl_P = (cl_ecl P1)` `C' = ((Cl_P - { L1 }) )` and `P1 \<in> P` 
    and hyp  show False by auto
 qed

  have not_fact: "\<not> (\<exists>P1. (P1 \<in> P \<and> factorization P1 C \<sigma> Ground C'))"
  proof
    assume "(\<exists>P1. (P1 \<in> P \<and> factorization P1 C \<sigma> Ground C'))"
    then obtain P1 where "P1 \<in> P" "factorization  P1 C \<sigma> Ground C'" by auto
    from `factorization P1 C \<sigma> Ground C'` obtain L1 L2 L' t s u v Cl_P Cl_C  where
      "(eligible_literal L1 P1 \<sigma>)"
      "(L1 \<in> (cl_ecl P1))" "(L2 \<in> (cl_ecl P1) - { L1 })" "(Cl_C = (cl_ecl C))" "(Cl_P = (cl_ecl P1))" 
      "(orient_lit_inst L1 t s pos \<sigma>)"
      "(orient_lit_inst L2 u v pos \<sigma>)"
      "((subst t \<sigma>) \<noteq> (subst s \<sigma>))"
      "((subst t \<sigma>) \<noteq> (subst v \<sigma>))"
      "(ck_unifier t u \<sigma> Ground)"
      "(L' = Neg (Eq s v))"
      "(Cl_C = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } )) \<sigma>)"
      "(C' = ( (Cl_P - { L2 }) \<union> { L' } ))" 
      unfolding factorization_def by blast 
    from `P1 \<in> P` and assms(2) and `P \<subseteq> S` have "finite (cl_ecl P1)" by auto

    from assms(3) and `P1 \<in> P` have "ground_clause (subst_cl (cl_ecl P1) \<sigma>)" unfolding grounding_set_def  by auto 
    from this have "vars_of_cl (subst_cl (cl_ecl P1) \<sigma>) = {}" by auto
    from `L1 \<in> (cl_ecl P1)`have "(subst_lit L1 \<sigma>) \<in> (subst_cl (cl_ecl P1) \<sigma>)" by auto
    from this and `vars_of_cl (subst_cl (cl_ecl P1) \<sigma>) = {}` have "vars_of_lit (subst_lit L1 \<sigma>) = {}"
      by auto
    from `orient_lit_inst L1 t s pos \<sigma>` have 
      "orient_lit (subst_lit L1 \<sigma>) (subst t \<sigma>) (subst s \<sigma>) pos" 
      using lift_orient_lit by auto
    from this and `vars_of_lit (subst_lit L1 \<sigma>) = {}` have "vars_of (subst t \<sigma>) = {}" 
       using orient_lit_vars by blast
    from `orient_lit (subst_lit L1 \<sigma>) (subst t \<sigma>) (subst s \<sigma>) pos` 
       and `vars_of_lit (subst_lit L1 \<sigma>) = {}` have "vars_of (subst s \<sigma>) = {}" 
       using orient_lit_vars by blast

    from `(L2 \<in> (cl_ecl P1) - { L1 })` have "L2 \<in> (cl_ecl P1)" by auto
    from `L2 \<in> (cl_ecl P1)` have "(subst_lit L2 \<sigma>) \<in> (subst_cl (cl_ecl P1) \<sigma>)" by auto
    from this and `vars_of_cl (subst_cl (cl_ecl P1) \<sigma>) = {}` have "vars_of_lit (subst_lit L2 \<sigma>) = {}"
      by auto

    from `orient_lit_inst L2 u v pos \<sigma>` have 
      "orient_lit (subst_lit L2 \<sigma>) (subst u \<sigma>) (subst v \<sigma>) pos" 
      using lift_orient_lit by auto
    from this and `vars_of_lit (subst_lit L2 \<sigma>) = {}` have "vars_of (subst u \<sigma>) = {}" 
       using orient_lit_vars by blast
    from `orient_lit (subst_lit L2 \<sigma>) (subst u \<sigma>) (subst v \<sigma>) pos` 
       and `vars_of_lit (subst_lit L2 \<sigma>) = {}` have "vars_of (subst v \<sigma>) = {}" 
       using orient_lit_vars by blast

    from `ck_unifier t u \<sigma> Ground` have "(subst t \<sigma>) = (subst u \<sigma>)" 
      unfolding ck_unifier_def Unifier_def by auto

    from `orient_lit (subst_lit L1 \<sigma>) (subst t \<sigma>) (subst s \<sigma>) pos` 
      have "((subst t \<sigma>),(subst s \<sigma>)) \<notin> trm_ord" 
      unfolding orient_lit_def by auto
    from this and `(subst t \<sigma>) \<noteq> (subst s \<sigma>)` 
      and `vars_of (subst t \<sigma>) = {}` `vars_of (subst s \<sigma>) = {}` 
       have "((subst s \<sigma>),(subst t \<sigma>)) \<in> trm_ord"  using trm_ord_ground_total 
       unfolding ground_term_def by blast
    from this and `(subst t \<sigma>) = (subst u \<sigma>)` have 
      "((subst s \<sigma>),(subst u \<sigma>)) \<in> trm_ord"  by auto

    from `orient_lit (subst_lit L2 \<sigma>) (subst u \<sigma>) (subst v \<sigma>) pos` 
      have "((subst u \<sigma>),(subst v \<sigma>)) \<notin> trm_ord" 
      unfolding orient_lit_def by auto
    from this and `(subst t \<sigma>) \<noteq> (subst v \<sigma>)` 
      and `(subst t \<sigma>) = (subst u \<sigma>)`
      and `vars_of (subst u \<sigma>) = {}` `vars_of (subst v \<sigma>) = {}` 
       have "((subst v \<sigma>),(subst u \<sigma>)) \<in> trm_ord"  using trm_ord_ground_total 
       unfolding ground_term_def by metis

    let ?mC1 = "mset_ecl (P1, \<sigma>)"
    let ?mC2 = "mset_ecl (C, \<sigma>)"

    from `L2 \<in> (cl_ecl P1)` `finite (cl_ecl P1)` 
      have "mset_set (cl_ecl P1) = mset_set ((cl_ecl P1)-{ L2 }) + mset_set { L2 }"
      using split_mset_set [of "cl_ecl P1" "cl_ecl P1 - { L2 }" "{ L2 }"] by blast

    from this have  d1: "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set (cl_ecl P1)) #}
      = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L2 })) #} 
        + {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L2 }) #}"
        using split_image_mset by auto
    
    let ?C = "(((cl_ecl P1) - { L2 }) \<union> { L' } )"
    from `finite (cl_ecl P1)`  have "finite ?C" by auto
    let ?C' = "?C - ( (cl_ecl P1) - { L2 })"
    from `finite ?C` have "finite ?C'" by auto
    have "?C = ( (cl_ecl P1) - { L2 }) \<union> ?C'" by auto
    from `finite (cl_ecl P1)` `finite ?C'` 
      have "mset_set ?C = mset_set ((cl_ecl P1)-{ L2 }) + mset_set ?C'"
      using split_mset_set [of "?C" "cl_ecl P1 - { L2 }" "?C'"] by blast

    from this have  d2: "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C) #}
      = {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L2 })) #} 
        + {# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"
        using split_image_mset by auto
    
    have "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L2 }) #} \<noteq> {#}"
      by auto
   let ?K = "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"
   let ?J = "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L2 }) #}"
   have "(\<forall>k \<in> set_mset ?K. \<exists>j \<in> set_mset ?J. (k, j) \<in> (mult trm_ord))"
   proof 
    fix k assume "k \<in> set_mset ?K"
    from this have "k \<in># ?K" by simp
    from this obtain M' where "M' \<in># (mset_set ?C')" and "k = (mset_lit (subst_lit M' \<sigma>))"
      using image_mset_thm [of "?K"  "\<lambda>x. (mset_lit (subst_lit x \<sigma>))" "(mset_set ?C')"]
      by metis

    from `M' \<in># (mset_set ?C')`and `finite ?C'` have "M' \<in> ?C'" by auto
    have "L2 \<in># (mset_set { L2 })" by auto
    from this have "(mset_lit (subst_lit L2 \<sigma>) \<in># ?J)" by auto
    from this have "(mset_lit (subst_lit L2 \<sigma>) \<in> set_mset ?J)" by auto
 
    have "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L2 }) #} \<noteq> {#}" by auto

    show "\<exists>j \<in> set_mset ?J. (k, j) \<in> (mult trm_ord)"
    proof -
      from `M' \<in> ?C'` have "M' = L'" by auto
      from  `orient_lit_inst L2 u v pos \<sigma>` 
        have i: "(mset_lit (subst_lit L2 \<sigma>)) 
          = {#} + {# (subst u \<sigma>), (subst v \<sigma>) #}"
          unfolding orient_lit_inst_def using add.commute by force 
      from  `L' = Neg (Eq s v)`  
          have ii: "(mset_lit (subst_lit L' \<sigma>)) = 
          {#} + {# (subst s \<sigma>), (subst s \<sigma>), (subst v \<sigma>), (subst v \<sigma>) #}"
          by force
      have "{# (subst u \<sigma>), (subst v \<sigma>) #} \<noteq> {#}" by auto
      have "(\<forall>k' \<in> set_mset {# (subst s \<sigma>), (subst s \<sigma>), (subst v \<sigma>), (subst v \<sigma>) #}. 
          \<exists>j' \<in> set_mset {# (subst u \<sigma>), (subst v \<sigma>) #}. (k', j') \<in> (trm_ord))"
        proof 
          fix k' assume nh: "k' \<in>set_mset {# (subst s \<sigma>), (subst s \<sigma>), (subst v \<sigma>), (subst v \<sigma>) #}"
          have "(subst u \<sigma>) \<in> set_mset {# (subst u \<sigma>), (subst v \<sigma>) #}" by auto
          from nh have "k' = (subst s \<sigma>) \<or> k' = (subst v \<sigma>)" by auto
          then show "\<exists>j' \<in> set_mset {# (subst u \<sigma>), (subst v \<sigma>) #}. (k', j') \<in> (trm_ord)" 
          proof 
            assume "k' = (subst s \<sigma>)"
            from this and `((subst s \<sigma>),(subst u \<sigma>)) \<in> trm_ord`
              and `(subst u \<sigma>) \<in> set_mset {# (subst u \<sigma>), (subst v \<sigma>) #}` show ?thesis by auto
          next
            assume "k' = (subst v \<sigma>)"
            from this and `((subst v \<sigma>),(subst u \<sigma>)) \<in> trm_ord`
              and `(subst u \<sigma>) \<in> set_mset {# (subst u \<sigma>), (subst v \<sigma>) #}` show ?thesis by auto
          qed
        qed
      from this i ii `{# (subst u \<sigma>), (subst v \<sigma>) #} \<noteq> {#}`
          have "(mset_lit (subst_lit L' \<sigma>),
            (mset_lit (subst_lit L2 \<sigma>))) \<in> (mult trm_ord)"
             using one_step_implies_mult  [of "{# (subst u \<sigma>), (subst v \<sigma>) #}" 
               "{#  (subst s \<sigma>),(subst s \<sigma>), (subst v \<sigma>),(subst v \<sigma>) #}" 
               trm_ord "{#}"] 
             trm_ord_trans by metis
        from this `M' = L'` `k = (mset_lit (subst_lit M' \<sigma>))` show ?thesis  by auto
     qed

    qed
  from this d1 d2 `{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L2 }) #} \<noteq> {#}` 
  have o: "
      ({#mset_lit (subst_lit x \<sigma>). x \<in># mset_set ?C #},
      {#mset_lit (subst_lit x \<sigma>). x \<in># mset_set (cl_ecl P1)#})
     \<in> mult (mult trm_ord)"
  using  mult_trm_ord_trans one_step_implies_mult [of
      "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set { L2 }) #}"
      "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ?C') #}"  "mult trm_ord" 
      "{# (mset_lit (subst_lit x \<sigma>)). x \<in># (mset_set ((cl_ecl P1) - { L2 })) #} " ] by metis

  from this `(Cl_P = (cl_ecl P1))` `C' = ( (Cl_P - { L2 }) \<union> { L' } )` and `P1 \<in> P` 
    and hyp show False by auto
  qed
  from not_sup not_ref not_fact and assms(1) show False unfolding derivable_def by blast
qed

lemma redundant_inference_clause:
  assumes "redundant_clause E S \<sigma> C'"
  assumes "derivable C P S \<sigma> Ground C'"
  assumes "grounding_set P \<sigma>"
  assumes "\<forall>x \<in> S. (finite (cl_ecl x))" 
  shows "redundant_inference E S P \<sigma>"
proof -
  from assms(1) obtain S' where "S' \<subseteq> (instances S)" 
    "(set_entails_clause (clset_instances S') (cl_ecl E))"
    "(\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl E)))"
    "(\<forall>x \<in> S'. ( ((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<sigma>))) \<in> (mult (mult trm_ord))
              \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>)))" 
    unfolding redundant_clause_def by auto
  from assms(3) assms(4) `derivable C P S \<sigma> Ground C'` 
    obtain D where "D \<in> P" 
      "(( (mset_cl (C',\<sigma>)), (mset_ecl (D,\<sigma>))) \<in> (mult (mult trm_ord)))" 
      using conclusion_is_smaller_than_premisses by blast

  have "(\<forall>x \<in> S'. \<exists>D' \<in> P. (((fst x),(snd x)),(D',\<sigma>)) \<in> ecl_ord)"
  proof 
    fix x assume "x \<in> S'"
    from this and `(\<forall>x \<in> S'. ( ((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<sigma>))) \<in> (mult (mult trm_ord))
              \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>)))` 
       have "((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<sigma>))) \<in> (mult (mult trm_ord)) \<or>
            (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>)" by auto 
    then have "(((fst x),(snd x)),(D,\<sigma>)) \<in> ecl_ord"
    proof
      assume "((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<sigma>))) \<in> (mult (mult trm_ord))"
      from this and `(( (mset_cl (C',\<sigma>)), (mset_ecl (D,\<sigma>))) \<in> (mult (mult trm_ord)))`
        have "((mset_ecl ((fst x),(snd x))),(mset_ecl (D,\<sigma>))) \<in> (mult (mult trm_ord))"
        using mult_mult_trm_ord_trans unfolding trans_def by metis
      from this show ?thesis unfolding ecl_ord_def by auto
    next assume "(mset_ecl ((fst x),(snd x))) = mset_cl (C',\<sigma>)"
      from this and `(( (mset_cl (C',\<sigma>)), (mset_ecl (D,\<sigma>))) \<in> (mult (mult trm_ord)))` 
      have "((mset_ecl ((fst x),(snd x))),(mset_ecl (D,\<sigma>))) \<in> (mult (mult trm_ord))" by auto
      from this show ?thesis unfolding ecl_ord_def by auto
    qed      
    from this and `D \<in> P` show "\<exists>D' \<in> P. (((fst x),(snd x)),(D',\<sigma>)) \<in> ecl_ord" by auto
  qed
  from this and `S' \<subseteq> (instances S)` and `(set_entails_clause (clset_instances S') (cl_ecl E))`
    and `(\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl E)))`
    show ?thesis unfolding redundant_inference_def by auto
qed
  
lemma clause_saturated_and_inference_saturated:
  assumes "clause_saturated S"
  assumes "\<forall>x \<in> S. (finite (cl_ecl x))" 
  shows "inference_saturated S"
proof (rule ccontr)
  assume "\<not> inference_saturated S"
  then obtain C P \<sigma> C' D  \<theta> \<eta>
    where "derivable C P S \<sigma> Ground C'" "ground_clause (cl_ecl C)"
          "derivable D P S \<theta> FirstOrder C'" "trms_subsumes D C \<eta>"
          "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>" "grounding_set P \<sigma>"
          "\<not>redundant_inference (subst_ecl D \<eta>) S P \<sigma>"
      unfolding inference_saturated_def by blast
  
  from assms(2) `grounding_set P \<sigma>` `derivable C P S \<sigma> Ground C'` 
    `\<not>redundant_inference (subst_ecl D \<eta>) S P \<sigma>`
    have "\<not>redundant_clause (subst_ecl D \<eta>) S \<sigma> C'"
    using redundant_inference_clause  by blast

  from assms(1) have "\<And>C P \<sigma> C' D  \<theta> \<eta>. 
     (derivable C P S \<sigma> Ground C') \<longrightarrow> (ground_clause (cl_ecl C)) 
      \<longrightarrow> (derivable D P S \<theta> FirstOrder C') \<longrightarrow> (trms_subsumes D C \<eta>)
      \<longrightarrow> (\<sigma> \<doteq> \<theta> \<lozenge> \<eta>)
      \<longrightarrow> (redundant_clause (subst_ecl D \<eta>) S \<sigma> C')" unfolding clause_saturated_def by blast
  from this  and `derivable C P S \<sigma> Ground C'` `ground_clause (cl_ecl C)` 
    `derivable D P S \<theta> FirstOrder C'` 
    `trms_subsumes D C \<eta>` `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` assms(1) have "redundant_clause (subst_ecl D \<eta>) S \<sigma> C'" 
      by auto
  from this and `\<not>redundant_clause (subst_ecl D \<eta>) S \<sigma> C'` show False by auto
qed

section {* Refutational Completeness *}

text {* We prove that our variant of the superposition calculus is complete under the 
redundancy criteria defined above. This is done as usual, by constructing a model of every
saturated set not containing the empty clause. *}

subsection {* Model Construction *}

text {* We associate as usual every set of extended clauses with an interpretation. 
The interpretation is constructed in such a way that it is a model of the set of clauses 
if the latter is saturated and does not contain the empty clause.
The interpretation is constructed by defining directly a normalization function mapping every term 
to its normal form, i.e., to the minimal equivalent term. Note that we do not consider sets of 
rewrite rules explicitly. *}

text {* The next function associates every normalization function with the corresponding 
interpretation (two terms are in relation if they share the same normal form). 
The obtained relation is an interpretation if the normalization function 
is compatible with the term combination operator. *}

definition same_values :: "('a trm \<Rightarrow> 'a trm) \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool"
  where "(same_values f) = 
           (\<lambda>x y. (f x) = (f y))"

definition value_is_compatible_with_structure :: "('a trm \<Rightarrow> 'a trm) \<Rightarrow> bool"
  where "(value_is_compatible_with_structure f) = (\<forall> t s. (f (Comb t s)) = (f (Comb (f t) (f s))))"

lemma same_values_fo_int:
  assumes "value_is_compatible_with_structure f"
  shows "fo_interpretation (same_values f)"
proof -
  let ?I = "(same_values f)"
  have ref: "reflexive ?I" unfolding same_values_def reflexive_def by simp 
  have sym: "symmetric ?I" unfolding same_values_def symmetric_def by auto 
  have trans: "transitive ?I" unfolding same_values_def transitive_def by auto 
  from assms(1) have comp: "compatible_with_structure ?I" 
    unfolding same_values_def 
      compatible_with_structure_def value_is_compatible_with_structure_def [of f]
   by metis
  from ref trans sym comp have "congruence ?I" unfolding congruence_def equivalence_relation_def 
    by auto
  then show ?thesis unfolding fo_interpretation_def by auto
qed

text {* The normalization function is defined by mapping each term to a set of pairs. Intuitively,
the second element of each pair represents the right hand side of a rule that can be used to rewrite 
the considered term, and the first element of the pair denotes its normal form. 
The value of the term is the first component of the pair with the smallest second component. *}

text {* The following function returns the set of values for which the second component is minimal. 
We then prove that this set is non-empty and define a function returning an arbitrary chosen 
element. *} 
 
definition min_trms :: "('a trm \<times> 'a trm) set \<Rightarrow> 'a trm set" 
  where "(min_trms E) = ({ x. (\<exists> pair. (pair \<in> E 
  \<and> (\<forall>pair' \<in> E. (snd pair',snd pair) \<notin> trm_ord)) \<and> x = fst pair) })"

lemma min_trms_not_empty:
  assumes "E \<noteq> {}"
  shows "min_trms E \<noteq> {}"
proof -
  from assms(1) obtain x where "x \<in> E" by auto
  let ?pair_ordering = "{ (x,y). ((snd x),(snd y)) \<in> trm_ord }"
  from trm_ord_wf have "wf ?pair_ordering" using  measure_wf by auto
  from this `x \<in> E` 
    obtain y where "y \<in> E" and "\<forall>z. (z,y) \<in> ?pair_ordering \<longrightarrow> (z \<notin> E)" 
      using wfE_min [of ?pair_ordering ]
      by metis
  from this have "fst y \<in> min_trms E" unfolding min_trms_def by blast
  then show ?thesis by auto
qed

definition get_min :: "'a trm \<Rightarrow> ('a trm \<times> 'a trm) set \<Rightarrow> 'a trm" 
  where "(get_min t E) = 
      (if ((min_trms E) = {}) then t else (SOME x. (x \<in> min_trms E)))"  

text {* We now define the normalization function. The definition is tuned to 
make the termination proof straightforward. We will reformulate it afterward to get a simpler 
definition. 

We first test whether a subterm of the considered term is reducible. If this is the case then 
the value can be obtained by applying recursively the function on each subterm, and then again on 
the term obtained by combining the obtained normal forms.
If not, then we collect all possible pairs (as explained above), and we use the one with the minimal 
second component. These pairs can be interpreted as rewrite rules, giving the value of the 
considered term: the second component is the right-hand side of the rule and the first component is 
the normal form of the right-hand side. 
As usual, such rewrite rules are obtained from ground clauses that have a strictly positive 
maximal literal, no selected literals, and that are not validated by the constructed interpretation.
*}

function trm_rep:: "'a trm \<Rightarrow> ('a eclause set \<Rightarrow> 'a trm)"
  where
    "(trm_rep t) = 
      (\<lambda>S. (if ((is_compound t) \<and> ((lhs t),t) \<in> trm_ord  \<and> ((rhs t),t) \<in> trm_ord
      \<and> ( ((lhs t,t) \<in> trm_ord \<longrightarrow> (trm_rep (lhs t) S) \<noteq> (lhs t)) 
      \<or> ((rhs t,t) \<in> trm_ord \<longrightarrow>(trm_rep (rhs t) S) \<noteq> (rhs t))))
        then (if ((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t) \<in> trm_ord 
                   then 
              (trm_rep (Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)) S)
              else t)
      else (get_min t 
         { pair. \<exists>z CC C' C s L L' \<sigma> t' s'. 
           pair = (z,s)
          \<and> CC \<in> S \<and> (t \<notin> (subst_set (trms_ecl CC) \<sigma>)) 
          \<and> (\<forall>x. (\<exists>x' \<in> (trms_ecl CC). occurs_in x (subst x' \<sigma>)) 
            \<longrightarrow> ( (x,t) \<in> trm_ord \<longrightarrow> (trm_rep x S) = x))         
          \<and> (C' = (cl_ecl CC)) \<and> (s,t) \<in> trm_ord \<and> ((s,t) \<in> trm_ord \<longrightarrow> (z = trm_rep s S))
          \<and> (orient_lit_inst L' t' s' pos \<sigma>) \<and>  (sel C') = {} \<and>  (L' \<in> C')
          \<and> (maximal_literal L C) \<and> (L = (subst_lit L' \<sigma>)) \<and>  (C = (subst_cl C' \<sigma>))
          \<and> (ground_clause C) \<and> (t = (subst t' \<sigma>)) \<and> (s = (subst s' \<sigma>)) \<and> (finite C') 
          \<and>
          (\<forall> L u v. 
              (L \<in> C \<longrightarrow> orient_lit L u v pos 
                \<longrightarrow> (u,t) \<in> trm_ord \<longrightarrow>  (v,t) \<in> trm_ord
                \<longrightarrow> (trm_rep u S) \<noteq>  (trm_rep v S)) 
          \<and>
            (L \<in> C \<longrightarrow> orient_lit L u v neg \<longrightarrow> (u,t) \<in> trm_ord \<longrightarrow>  (v,t) \<in> trm_ord
                \<longrightarrow> (trm_rep u S) = (trm_rep v S)))
          \<and> (\<forall>s''. ( 
              (eq_occurs_in_cl t s'' (C'- { L' }) \<sigma>) \<longrightarrow> (s'',t) \<in> trm_ord \<longrightarrow>  (s,t) \<in> trm_ord
                \<longrightarrow> (trm_rep s S) \<noteq> (trm_rep s'' S))) })))"
by auto
termination apply (relation "trm_ord") 
by auto (simp add: trm_ord_wf)

text {* We now introduce a few shorthands and rewrite the previous definition into an equivalent 
simpler form. The key point is to prove that a term is always greater than its normal form. *}

definition subterm_reduction_aux:: "'a eclause set \<Rightarrow> 'a trm \<Rightarrow> 'a trm"
where
  "subterm_reduction_aux S t = 
        (if ((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t) \<in> trm_ord 
         then (trm_rep (Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)) S)
         else t)"

definition subterm_reduction:: "'a eclause set \<Rightarrow> 'a trm \<Rightarrow> 'a trm"
where
  "subterm_reduction S t = 
              (trm_rep (Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)) S)"

definition maximal_literal_is_unique 
  where "(maximal_literal_is_unique t s C' L' S \<sigma>) = 
    (\<forall>s''. ( 
              (eq_occurs_in_cl t s'' (C'- { L' }) \<sigma>) \<longrightarrow> (s'',t) \<in> trm_ord \<longrightarrow>  (s,t) \<in> trm_ord
                \<longrightarrow> (trm_rep s S) \<noteq> (trm_rep s'' S)))"

definition smaller_lits_are_false
  where "(smaller_lits_are_false t C S) = 
    (\<forall> L u v. 
              (L \<in> C \<longrightarrow> orient_lit L u v pos 
                \<longrightarrow> (u,t) \<in> trm_ord \<longrightarrow>  (v,t) \<in> trm_ord
                \<longrightarrow> (trm_rep u S) \<noteq>  (trm_rep v S)) 
          \<and>
            (L \<in> C \<longrightarrow> orient_lit L u v neg \<longrightarrow> (u,t) \<in> trm_ord \<longrightarrow>  (v,t) \<in> trm_ord
                \<longrightarrow> (trm_rep u S) = (trm_rep v S)))"

definition int_clset
  where "int_clset S = (same_values (\<lambda>x. (trm_rep x S)))"

lemma smaller_lits_are_false_if_cl_not_valid:
  assumes "\<not>(validate_ground_clause (int_clset S) C)"
  shows "smaller_lits_are_false t C S"
proof (rule ccontr)
  let ?I = "int_clset S"
  assume "\<not>smaller_lits_are_false t C S" 
  from this obtain L u v where "L \<in> C"  
    and "(orient_lit L u v pos \<and> (trm_rep u S) =  (trm_rep v S)) 
          \<or> (orient_lit L u v neg \<and> (trm_rep u S) \<noteq> (trm_rep v S))" 
    unfolding smaller_lits_are_false_def by blast
  then have "(orient_lit L u v pos \<and> (trm_rep u S) =  (trm_rep v S)) 
          \<or> (orient_lit L u v neg \<and> (trm_rep u S) \<noteq> (trm_rep v S))" by blast
  then show False
  proof 
    assume c_pos: "(orient_lit L u v pos \<and> (trm_rep u S) =  (trm_rep v S))"
    then have "orient_lit L u v pos" by blast
    from c_pos have "(trm_rep u S) =  (trm_rep v S)" by blast
    from `orient_lit L u v pos` have "L = (Pos (Eq u v)) \<or> L = (Pos (Eq v u))" 
      unfolding orient_lit_def by auto
    from this and `(trm_rep u S) =  (trm_rep v S)`  have "validate_ground_lit ?I L" 
      using validate_ground_lit.simps(1) validate_ground_eq.simps 
      unfolding same_values_def int_clset_def
      by (metis (mono_tags, lifting)) 
    from this and `L \<in> C` and assms  show False unfolding int_clset_def 
      using validate_ground_clause.simps by blast
  next 
    assume c_neg: "(orient_lit L u v neg \<and> (trm_rep u S) \<noteq> (trm_rep v S))"
    then have "orient_lit L u v neg" by blast
    from c_neg have "(trm_rep u S) \<noteq> (trm_rep v S)" by blast
    from `orient_lit L u v neg` have "L = (Neg (Eq u v)) \<or> L = (Neg (Eq v u))" 
      unfolding orient_lit_def by auto
    from this and `(trm_rep u S) \<noteq> (trm_rep v S)`  have "validate_ground_lit ?I L" 
      using validate_ground_lit.simps(2) validate_ground_eq.simps 
      unfolding same_values_def int_clset_def
      by (metis (mono_tags, lifting)) 
    from this and `L \<in> C` and assms  show False unfolding int_clset_def 
      using validate_ground_clause.simps by blast
  qed
qed

text {* The following function states that all instances of the terms attached to a clause are in 
normal form w.r.t.\ the interpretation associated with @{term "S"}, up to some maximal term 
@{term "t"} *}

definition trms_irreducible
  where "trms_irreducible CC \<sigma> S t = 
            (\<forall>x. (\<exists>x' \<in> (trms_ecl CC). occurs_in x (subst x' \<sigma>)) \<longrightarrow> 
              ( (x,t) \<in> trm_ord \<longrightarrow> (trm_rep x S) = x))"         

lemma trms_irreducible_lemma:
  assumes "all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. trm_rep t S)"
  shows "trms_irreducible C \<sigma> S t"
proof (rule ccontr)
  assume "\<not>trms_irreducible C \<sigma> S t"
  from this obtain x where "\<exists>x'\<in> trms_ecl C. occurs_in x (subst x' \<sigma>)" and
          "trm_rep x S \<noteq> x"  unfolding trms_irreducible_def by blast
  from `\<exists>x'\<in> trms_ecl C. occurs_in x (subst x' \<sigma>)` obtain x' where
    "x' \<in> trms_ecl C" and "occurs_in x (subst x' \<sigma>)" by blast
  from `x' \<in> trms_ecl C` 
    have "(subst x' \<sigma>) \<in> (subst_set (trms_ecl C) \<sigma>)"
    by auto
  from this and assms(1) `occurs_in x (subst x' \<sigma>)` 
    have "trm_rep x S = x" unfolding all_trms_irreducible_def by metis
  from this and `trm_rep x S \<noteq> x` show False by blast
qed

text {* The following predicate states that a term @{term "z"} is the normal form of the right-hand 
side of a rule of left-hand side @{term "t"}. It is used to define the set of possible values for 
term @{term "t"}. The actual value is that corresponding to the smallest right-hand side. *}

definition candidate_values
  where "(candidate_values z CC C' C s L L' \<sigma> t' s' t S) = 
           (CC \<in> S \<and> (t \<notin> (subst_set (trms_ecl CC) \<sigma>)) \<and> (trms_irreducible CC \<sigma> S t)
          \<and> (C' = (cl_ecl CC)) \<and> (s,t) \<in> trm_ord \<and> ((s,t) \<in> trm_ord \<longrightarrow> (z = trm_rep s S))
          \<and> (orient_lit_inst L' t' s' pos \<sigma>) \<and> (sel C' = {}) \<and> (L' \<in> C') \<and> (maximal_literal L C)
          \<and> (L = (subst_lit L' \<sigma>)) \<and> (C = (subst_cl C' \<sigma>)) \<and> (ground_clause C)
          \<and> (t = (subst t' \<sigma>)) \<and>  (s = (subst s' \<sigma>)) \<and> (finite C') 
          \<and> (smaller_lits_are_false t C S)
          \<and> (maximal_literal_is_unique t s C' L' S \<sigma>))"

definition set_of_candidate_values:: "'a eclause set \<Rightarrow> 'a trm \<Rightarrow> ('a trm \<times> 'a trm) set"
where "set_of_candidate_values S t  = 
         { pair. \<exists>z CC C' C s L L' \<sigma> t' s'. 
           pair = (z,s) \<and> (candidate_values z CC C' C s L L' \<sigma> t' s' t S) }"

definition subterm_reduction_applicable_aux:: "'a eclause set \<Rightarrow> 'a trm \<Rightarrow> bool"
  where "subterm_reduction_applicable_aux S t =
   (is_compound t \<and> (lhs t,t) \<in> trm_ord  \<and> (rhs t,t) \<in> trm_ord
      \<and> ( ((lhs t,t) \<in> trm_ord \<longrightarrow> (trm_rep (lhs t) S) \<noteq> (lhs t)) 
      \<or> ((rhs t,t) \<in> trm_ord \<longrightarrow>(trm_rep (rhs t) S) \<noteq> (rhs t))))"

definition subterm_reduction_applicable:: "'a eclause set \<Rightarrow> 'a trm \<Rightarrow> bool"
  where "subterm_reduction_applicable S t =
   (is_compound t \<and> ((trm_rep (lhs t) S) \<noteq> (lhs t) \<or> (trm_rep (rhs t) S) \<noteq> (rhs t)))"

lemma trm_rep_is_lower_aux:
  assumes "\<forall>y. (y,t) \<in> trm_ord \<longrightarrow>
      (y \<noteq> (trm_rep y S) \<longrightarrow> ((trm_rep y S),y) \<in> trm_ord)"
  assumes "(subterm_reduction_applicable S t)"
  shows "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t) \<in> trm_ord"
proof -
  have "(lhs t,t) \<in> trm_ord" using \<open>subterm_reduction_applicable S t\<close> args_are_strictly_lower 
      subterm_reduction_applicable_def 
    by blast 
  have "(rhs t,t) \<in> trm_ord" using \<open>subterm_reduction_applicable S t\<close> args_are_strictly_lower 
    subterm_reduction_applicable_def by blast 
  from assms(1) and `(lhs t,t) \<in> trm_ord` have 
    l: "( (lhs t \<noteq> (trm_rep (lhs t) S)) \<longrightarrow> ((trm_rep  (lhs t) S), (lhs t)) \<in> trm_ord)" 
    by metis
  from assms(1) and `(rhs t,t) \<in> trm_ord` have 
    r: "(rhs t \<noteq> (trm_rep (rhs t) S) \<longrightarrow> ((trm_rep  (rhs t) S), (rhs t)) \<in> trm_ord)" 
    by metis
  from `subterm_reduction_applicable S t` 
    have "((trm_rep (lhs t) S) \<noteq> (lhs t) \<or> (trm_rep (rhs t) S) \<noteq> (rhs t))"
    unfolding subterm_reduction_applicable_def [of S t] by blast
  then show ?thesis
  proof 
    assume "(trm_rep (lhs t) S) \<noteq> (lhs t)"
    from this and l have "((trm_rep  (lhs t) S), (lhs t)) \<in> trm_ord" by metis
    from this 
     have i: "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),(Comb (lhs t)  (trm_rep (rhs t) S))) 
      \<in> trm_ord" using trm_ord_reduction_left by blast
    show "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t) \<in> trm_ord" 
    proof (cases)
      assume "(trm_rep (rhs t) S) = (rhs t)"
      from this 
        and `((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),(Comb (lhs t)  (trm_rep (rhs t) S))) 
          \<in> trm_ord`
      show "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t)  \<in> trm_ord"
        by (metis assms(2) is_compound.elims(2) lhs.simps(1) 
            rhs.simps(1) subterm_reduction_applicable_def) 
    next
      assume "(trm_rep (rhs t) S) \<noteq> (rhs t)"
      from this and r have "((trm_rep  (rhs t) S), (rhs t)) \<in> trm_ord" by metis
      from this have "((Comb (lhs t) (trm_rep (rhs t) S)), ((Comb (lhs t) (rhs t))))  \<in> trm_ord"
          using trm_ord_reduction_right by blast
      from this and i  show "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t)  \<in> trm_ord"
        by (metis assms(2) is_compound.elims(2) lhs.simps(1) rhs.simps(1) 
            subterm_reduction_applicable_def trm_ord_trans transE)
    qed
    next     
      assume "(trm_rep (rhs t) S) \<noteq> (rhs t)"
    from this and r have "((trm_rep  (rhs t) S), (rhs t)) \<in> trm_ord" by metis
    from this 
      have i: "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),(Comb (trm_rep (lhs t) S) (rhs t))) 
                \<in> trm_ord" using trm_ord_reduction_right by blast
    show "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t) \<in> trm_ord" 
    proof (cases)
      assume "(trm_rep (lhs t) S) = (lhs t)"
      from this and 
     `((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),(Comb (trm_rep (lhs t) S) (rhs t))) \<in> trm_ord`
      show "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t)  \<in> trm_ord"
        by (metis assms(2) basic_superposition.subterm_reduction_applicable_def  
            basic_superposition_axioms is_compound.elims(2) lhs.simps(1) rhs.simps(1))
    next
      assume "(trm_rep (lhs t) S) \<noteq> (lhs t)"
      from this and l have "((trm_rep  (lhs t) S), (lhs t)) \<in> trm_ord" by metis
      from this have "((Comb (trm_rep (lhs t) S)  (rhs t)), ((Comb (lhs t) (rhs t))))  \<in> trm_ord"
          using trm_ord_reduction_left by blast
      from this and i  show "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t)  \<in> trm_ord"
        by (metis assms(2) basic_superposition.subterm_reduction_applicable_def 
            basic_superposition_axioms is_compound.elims(2) lhs.simps(1) rhs.simps(1) 
            trm_ord_trans transE) 
    qed      
  qed
qed

text {* The following lemma corresponds to the initial definition of the function 
@{term "trm_rep"}. *}

lemma trm_rep_init_def:
  shows "(trm_rep t) = (\<lambda>S. (if (subterm_reduction_applicable_aux S t) 
                        then (subterm_reduction_aux S t)
                        else (get_min t (set_of_candidate_values S t))))"
unfolding subterm_reduction_aux_def set_of_candidate_values_def candidate_values_def 
   subterm_reduction_applicable_aux_def maximal_literal_is_unique_def smaller_lits_are_false_def 
   trms_irreducible_def
using trm_rep.simps [of t] by force

lemma trm_rep_aux_def:
  assumes "\<forall>y. (y,t) \<in> trm_ord \<longrightarrow>
      (y \<noteq> (trm_rep y S) \<longrightarrow> ((trm_rep y S),y) \<in> trm_ord)"
  shows "(trm_rep t S) = (if (subterm_reduction_applicable S t) 
                        then (subterm_reduction S t)
                        else (get_min t (set_of_candidate_values S t)))"
proof (cases)
  assume "subterm_reduction_applicable S t"
  then have "subterm_reduction_applicable_aux S t"
    using args_are_strictly_lower 
      subterm_reduction_applicable_def subterm_reduction_applicable_aux_def by blast 
  from this have "(trm_rep t S) = (subterm_reduction_aux S t)" 
  using trm_rep_init_def [of t] by meson
  then have "((Comb (trm_rep (lhs t) S) (trm_rep (rhs t) S)),t) \<in> trm_ord"
    using \<open>subterm_reduction_applicable S t\<close> assms trm_rep_is_lower_aux by blast 
  then show ?thesis
    by (metis \<open>trm_rep t S = subterm_reduction_aux S t\<close> 
        \<open>subterm_reduction_applicable S t\<close> 
        subterm_reduction_def 
        subterm_reduction_aux_def)
next
  assume "\<not>subterm_reduction_applicable S t"
  then have "\<not>subterm_reduction_applicable_aux S t"
    using subterm_reduction_applicable_def subterm_reduction_applicable_aux_def by blast 
  from this and `\<not>subterm_reduction_applicable S t` show ?thesis 
    by (meson trm_rep_init_def)
qed
  
lemma trm_rep_is_lower:  
  shows "(t \<noteq> (trm_rep t S)) \<longrightarrow> (((trm_rep t S),t) \<in> trm_ord)" (is "?P t")
proof ((rule wf_induct [of "trm_ord" "?P" "t"]),(simp add: trm_ord_wf))
next 
    fix x assume hyp_ind: "\<forall>y. (y,x) \<in> trm_ord \<longrightarrow> (?P y)"
    let ?v = "(Comb (trm_rep (lhs x) S) (trm_rep (rhs x) S))"
    show "(?P x)"
    proof (rule impI)
      assume "x \<noteq> (trm_rep x S)"
      show "((trm_rep x S),x) \<in> trm_ord"
      proof cases
        assume c1: "subterm_reduction_applicable S x"
        from this and hyp_ind 
          have "(?v,x) \<in> trm_ord" using trm_rep_is_lower_aux by metis
        from c1 and hyp_ind have "(trm_rep x S) = (subterm_reduction S x)" 
          using trm_rep_aux_def [of x S] by metis
        from this have "(trm_rep x S) = (trm_rep ?v S)" 
          unfolding subterm_reduction_def by metis
        from `(?v,x) \<in> trm_ord` and hyp_ind have "?P ?v" by metis
        from this and `(trm_rep x S) = (trm_rep ?v S)` show ?thesis
          by (metis \<open>(trm_rep (lhs x) S \<cdot> trm_rep (rhs x) S, x) \<in> trm_ord\<close> trm_ord_trans transE) 
      next assume c2: "\<not>subterm_reduction_applicable S x"
        from c2 and hyp_ind have "(trm_rep x S) = (get_min x (set_of_candidate_values S x))" 
          using trm_rep_aux_def [of x S] by metis
        from this and `x \<noteq> (trm_rep x S)` 
          have "(trm_rep x S) \<in> (min_trms (set_of_candidate_values S x))" 
          unfolding get_min_def by (metis (full_types) some_in_eq) 
        then obtain pair where  "pair \<in> (set_of_candidate_values S x)" "(trm_rep x S) = fst pair" 
          unfolding min_trms_def by blast 
        from `pair \<in> (set_of_candidate_values S x)` 
          have 
          "\<exists> CC C' C  L L' \<sigma> t' s'. candidate_values (fst pair) CC C' C (snd pair) L L' \<sigma> t' s' x S"
          unfolding set_of_candidate_values_def by fastforce
        from this have "(snd pair,x) \<in> trm_ord" unfolding candidate_values_def by blast
        from 
          `\<exists> CC C' C  L L' \<sigma> t' s'. candidate_values (fst pair) CC C' C (snd pair) L L' \<sigma> t' s' x S`
          have "((snd pair, x) \<in> trm_ord \<longrightarrow> fst pair = trm_rep (snd pair) S)"
          unfolding candidate_values_def by blast
        from `(snd pair,x) \<in> trm_ord` `((snd pair, x) \<in> trm_ord \<longrightarrow> fst pair = trm_rep (snd pair) S)` 
          have "fst pair = trm_rep (snd pair) S" by blast
        from `(snd pair,x) \<in> trm_ord` and hyp_ind have "(?P (snd pair))" by blast
        from this and `fst pair = (trm_rep (snd pair) S)` 
          have "fst pair = snd pair \<or> (fst pair,snd pair) \<in> trm_ord"
          by metis
        from this and `(trm_rep x S) = fst pair` and `(snd pair,x) \<in> trm_ord` `x \<noteq> (trm_rep x S)` 
          show ?thesis by (metis trm_ord_trans transD) 
      qed
    qed
qed

lemma trm_rep_is_lower_subt_red:  
  assumes "(subterm_reduction_applicable S x)"
  shows "((trm_rep x S),x) \<in> trm_ord"
proof -
    let ?v = "(Comb (trm_rep (lhs x) S) (trm_rep (rhs x) S))"
    from assms(1)
          have "(?v,x) \<in> trm_ord" using trm_rep_is_lower_aux trm_rep_is_lower by metis
    from assms(1) have "(trm_rep x S) = (subterm_reduction S x)" 
          using trm_rep_aux_def [of x S] trm_rep_is_lower by metis
    from this have "(trm_rep x S) = (trm_rep ?v S)" 
          unfolding subterm_reduction_def by metis
    have "?v = trm_rep ?v S \<or> (trm_rep ?v S,?v) \<in> trm_ord" using trm_rep_is_lower by blast
    from this and `(trm_rep x S) = (trm_rep ?v S)` show "(((trm_rep x S),x) \<in> trm_ord)"
          by (metis \<open>(trm_rep (lhs x) S \<cdot> trm_rep (rhs x) S, x) \<in> trm_ord\<close> trm_ord_trans transE) 
qed

lemma trm_rep_is_lower_root_red:  
  assumes "\<not>(subterm_reduction_applicable S x)"
  assumes "min_trms (set_of_candidate_values S x) \<noteq> {}"
  shows "(((trm_rep x S),x) \<in> trm_ord)"
proof -
  from assms(1) have "(trm_rep x S) = (get_min x (set_of_candidate_values S x))" 
    using trm_rep_aux_def [of x S] trm_rep_is_lower by metis
  from this and assms(2) have "(trm_rep x S) \<in> (min_trms (set_of_candidate_values S x))" 
    unfolding get_min_def by (metis (full_types) some_in_eq) 
  then obtain pair where  "pair \<in> (set_of_candidate_values S x)" and "(trm_rep x S) = fst pair" 
    unfolding min_trms_def by blast 
  from `pair \<in> (set_of_candidate_values S x)` 
    have "\<exists> CC C' C  L L' \<sigma> t' s'. candidate_values (fst pair) CC C' C (snd pair) L L' \<sigma> t' s' x S"
    unfolding set_of_candidate_values_def by fastforce
  from this have "(snd pair,x) \<in> trm_ord" unfolding candidate_values_def by blast
  from `\<exists> CC C' C  L L' \<sigma> t' s'. candidate_values (fst pair) CC C' C (snd pair) L L' \<sigma> t' s' x S`
    have "((snd pair, x) \<in> trm_ord \<longrightarrow> fst pair = trm_rep (snd pair) S)"
    unfolding candidate_values_def by blast
  from `(snd pair,x) \<in> trm_ord` and `((snd pair, x) \<in> trm_ord \<longrightarrow> fst pair = trm_rep (snd pair) S)` 
    have "fst pair = trm_rep (snd pair) S" by blast
  have "snd pair = trm_rep (snd pair) S \<or> (trm_rep (snd pair) S,snd pair) \<in> trm_ord"
    using trm_rep_is_lower by blast
  from this and `(snd pair,x) \<in> trm_ord` have "(trm_rep (snd pair) S,x) \<in> trm_ord"
    using trm_ord_trans trans_def by metis
  from this and `(trm_rep x S) = fst pair` and `fst pair = trm_rep (snd pair) S` show ?thesis
    by metis
qed

text {* Finally, the next lemma gives a simpler and more convenient definition 
of the function @{term "trm_rep"}. *}

lemma trm_rep_simp_def:
  shows "(trm_rep t S) = (if (subterm_reduction_applicable S t) 
                        then (subterm_reduction S t)
                        else (get_min t (set_of_candidate_values S t)))"
using trm_rep_is_lower  trm_rep_aux_def by blast

text {* We now establish some useful properties of the normalization function. *}

lemma trm_rep_involutive:  
  shows "(trm_rep (trm_rep t S) S) = (trm_rep t S)" (is "?P t")
proof ((rule wf_induct [of "trm_ord" "?P" "t"]),(simp add: trm_ord_wf))
next 
    fix x assume hyp_ind: "\<forall>y. (y,x) \<in> trm_ord \<longrightarrow> (?P y)"
    let ?v = "(Comb (trm_rep (lhs x) S) (trm_rep (rhs x) S))"
    show "(?P x)"
      proof cases
        assume c1: "subterm_reduction_applicable S x"
        from this and hyp_ind 
          have "(?v,x) \<in> trm_ord" using trm_rep_is_lower_aux trm_rep_is_lower by metis
        from this hyp_ind have "(trm_rep (trm_rep ?v S) S) =  (trm_rep ?v S)" 
          using trm_rep_aux_def [of x S] by metis
        from c1 have "trm_rep x S = trm_rep ?v S" 
          using trm_rep_simp_def [of x S] unfolding subterm_reduction_def by metis
        from this and `(trm_rep (trm_rep ?v S) S) =  (trm_rep ?v S)` `trm_rep x S = trm_rep ?v S`
          show ?thesis by metis
       next assume c2: "\<not>subterm_reduction_applicable S x"
        from c2 have "(trm_rep x S) = (get_min x (set_of_candidate_values S x))" 
          using trm_rep_simp_def [of x S] by metis
        show ?thesis
        proof (rule ccontr)
          assume "(trm_rep (trm_rep x S) S) \<noteq> (trm_rep x S)"
          from this have "x \<noteq> (trm_rep x S)" by metis
          from c2 and `x \<noteq> (trm_rep x S)` 
            have "(trm_rep x S) \<in> (min_trms (set_of_candidate_values S x))" 
            using trm_rep_simp_def [of x S] 
            unfolding get_min_def by (metis (full_types) some_in_eq) 
          then obtain pair where  
            "pair \<in> (set_of_candidate_values S x)" and "(trm_rep x S) = fst pair" 
            unfolding min_trms_def by blast 
          from `pair \<in> (set_of_candidate_values S x)` 
            have i: "\<exists> CC C' C  L L' \<sigma> t' s'. 
                    candidate_values (fst pair) CC C' C (snd pair) L L' \<sigma> t' s' x S"
            unfolding set_of_candidate_values_def
            by fastforce
          from this have "(snd pair,x) \<in> trm_ord" unfolding candidate_values_def by blast
          from i have "((snd pair, x) \<in> trm_ord \<longrightarrow> fst pair = trm_rep (snd pair) S)"
            unfolding candidate_values_def by blast
          from `(snd pair,x) \<in> trm_ord` 
            and `((snd pair, x) \<in> trm_ord \<longrightarrow> fst pair = trm_rep (snd pair) S)` 
            have "fst pair = trm_rep (snd pair) S" by blast
          from `(snd pair,x) \<in> trm_ord` and hyp_ind have "(?P (snd pair))" by blast
          from this and `fst pair = (trm_rep (snd pair) S)` and `(trm_rep x S) = fst pair` 
            and `(trm_rep (trm_rep x S) S) \<noteq> (trm_rep x S)` 
            show False by metis
        qed
    qed
qed

text {* The following predicate is true if all proper subterms are in normal form. *}

definition root_term :: "'a eclause set \<Rightarrow> 'a trm \<Rightarrow> bool"
  where
    "(root_term S t) = 
      ((trm_rep t S) = (get_min t (set_of_candidate_values S t)))"

text {* The following function checks that the considered term contains a subterm that can be 
reduced. *}

definition st_red :: "'a eclause set \<Rightarrow> 'a trm \<Rightarrow> bool"
  where
    "(st_red S t) 
      = (\<exists> t' p. ( (subterm t p t') \<and> (root_term S t') \<and> (trm_rep t' S \<noteq> t')))"

lemma red_arg_implies_red_trm :
  assumes "st_red S t1"
  assumes "t = (Comb t1 t2) \<or> t = (Comb t2 t1)"
  shows "st_red S t"
proof -
  from assms(1) obtain t' p where "subterm t1 p t'" and "root_term S t'" and "trm_rep t' S \<noteq> t'"
    unfolding st_red_def by blast
  from `subterm t1 p t'` and assms(2) obtain q where "subterm t q t'"
    by (metis subterm.simps(4) subterm.simps(5)) 
  from this and `root_term S t'` and `trm_rep t' S \<noteq> t'` 
    show ?thesis unfolding st_red_def by blast
qed

lemma subterms_of_irred_trms_are_irred: 
  "(trm_rep t S) \<noteq> t \<longrightarrow> st_red S t" (is "(?P t)")
proof ((rule wf_induct [of "trm_ord" "?P" "t"]),(simp add: trm_ord_wf))
  next
    fix x assume hyp_ind: "\<forall>y. (y,x) \<in> trm_ord \<longrightarrow> (?P y)"
    show "(?P x)"
    proof (rule impI)
      assume "(trm_rep x S) \<noteq> x"
      show "st_red S x"
      proof (rule ccontr)
        assume neg_h: "\<not>st_red S x"
        have i: " \<not>subterm_reduction_applicable S x"
        proof
          assume decomp_case: "subterm_reduction_applicable S x"
          then obtain x1 x2 where "x = (Comb x1 x2)" using is_compound.elims(2)
            unfolding subterm_reduction_applicable_def by blast  
          from this and decomp_case have "((trm_rep x1 S) \<noteq> x1 \<or> (trm_rep x2 S) \<noteq> x2)"
            using lhs.simps(1) rhs.simps(1) 
            unfolding subterm_reduction_applicable_def by metis 
          then show False
          proof 
            assume "(trm_rep x1 S) \<noteq> x1"
            from `x = (Comb x1 x2)` and trm_ord_subterm have "(x1,x) \<in> trm_ord" by auto
            from this and hyp_ind and `(trm_rep x1 S) \<noteq> x1` 
              have "st_red S x1" by blast
            from this and neg_h and `x = (Comb x1 x2)` show False 
              using red_arg_implies_red_trm [of S x1 x x2] by blast
          next
            assume "(trm_rep x2 S) \<noteq> x2"
            from `x = (Comb x1 x2)` and trm_ord_subterm have "(x2,x) \<in> trm_ord" by auto
            from this and hyp_ind and `(trm_rep x2 S) \<noteq> x2` 
              have "st_red S x2" by metis
            from this and neg_h and `x = (Comb x1 x2)` show False 
              using red_arg_implies_red_trm [of S x2 x x1] by blast
          qed
        qed
        then have "(trm_rep x S) = (get_min x (set_of_candidate_values S x))"
          using trm_rep_simp_def by metis
        then have "root_term S x" unfolding root_term_def by blast
        have "subterm x [] x" by auto
        from this and `root_term S x` and `(trm_rep x S) \<noteq> x`have 
          "st_red S x" unfolding st_red_def by blast
        from this and neg_h show False by auto  
      qed
    qed
qed

lemma trm_rep_compatible_with_structure:
  shows "value_is_compatible_with_structure (\<lambda>x. trm_rep x S)"
proof (rule ccontr)
  assume "\<not>value_is_compatible_with_structure (\<lambda>x. trm_rep x S)"
  from this obtain t s 
    where neg_h:"trm_rep (Comb t s) S \<noteq> (trm_rep (Comb (trm_rep t S) (trm_rep s S)) S)" 
    unfolding value_is_compatible_with_structure_def by blast
  from this have "(trm_rep t S) \<noteq> t \<or> (trm_rep s S) \<noteq> s" by metis  
  from this have "subterm_reduction_applicable S (Comb t s)" 
    unfolding subterm_reduction_applicable_def 
    by (metis is_compound.simps(3) lhs.simps(1) rhs.simps(1))
  from this have "(trm_rep (Comb t s) S) = (subterm_reduction S (Comb t s))"
    using trm_rep_simp_def by metis
  from this and neg_h show False unfolding subterm_reduction_def
    by (metis lhs.simps(1) rhs.simps(1)) 
qed

text {* The following function checks that a position can be reduced, taking into account the 
order on positions associated with the considered clause and term. A term is reducible when all 
terms occurring at smaller positions are irreducible. *}

definition minimal_redex 
  where "minimal_redex p t C S t'
    = (\<forall>q s. ((q,p) \<in> (pos_ord C t') \<longrightarrow> (subterm t q s) \<longrightarrow> (trm_rep s S = s)))"

text {* The next function checks that a given clause contains two equations with the same
left-hand side and whose right-hand sides are equivalent in a given interpretation. If no such 
equations exist then it is clear that the maximal literal is necessarily unique. *}
 
definition equivalent_eq_exists
  where "equivalent_eq_exists t s C I \<sigma> L1 = (\<exists>L\<in> C - { L1 }. \<exists> u v.
    (orient_lit_inst L u v pos \<sigma>) \<and> ((subst t \<sigma>) = (subst u \<sigma>))
    \<and> (I  (subst s \<sigma>) (subst v \<sigma>)))"

lemma maximal_literal_is_unique_lemma:
  assumes "\<not>equivalent_eq_exists t s C (int_clset S) \<sigma> L1"
  shows "maximal_literal_is_unique (subst t \<sigma>) (subst s \<sigma>) C L1 S \<sigma>"
proof (rule ccontr)
  let ?t = "(subst t \<sigma>)"
  let ?s = "(subst s \<sigma>)"
  let ?L = "(subst_lit L \<sigma>)"
  let ?C = "(subst_cl C \<sigma>)"

  assume "\<not>(maximal_literal_is_unique ?t ?s C L1 S \<sigma>)"
  from this obtain s'' where "(eq_occurs_in_cl ?t s'' (C- { L1 }) \<sigma>)" 
    and "(trm_rep ?s  S) = (trm_rep s'' S)" unfolding maximal_literal_is_unique_def by blast
  from `(eq_occurs_in_cl ?t s'' (C- { L1 }) \<sigma>)` 
    obtain L' t' s' where "L' \<in> (C- { L1 })" 
      and "orient_lit_inst L' t' s' pos \<sigma>" and "(subst t' \<sigma>) = ?t" 
      and  "s'' = subst s' \<sigma>"
    unfolding eq_occurs_in_cl_def  by auto
  from `s'' = subst s' \<sigma>` and `(trm_rep ?s  S) = (trm_rep s'' S)` 
    have "(trm_rep ?s  S) = (trm_rep (subst s' \<sigma>) S)" by blast
  from `L' \<in> (C- { L1 })` `orient_lit_inst L' t' s' pos \<sigma>` `(subst t' \<sigma>) = ?t` 
  `(trm_rep ?s  S) = (trm_rep (subst s' \<sigma>) S)`
   have "equivalent_eq_exists t s C (int_clset S) \<sigma> L1" 
    unfolding equivalent_eq_exists_def same_values_def int_clset_def
   by metis
  from this and assms(1) show False by blast
qed

lemma max_pos_lit_dominates_cl:
  assumes "maximal_literal (subst_lit L \<sigma>) (subst_cl C \<sigma>)"
  assumes "orient_lit_inst L t s pos \<sigma>"
  assumes "L' \<in> C - { L }"
  assumes "\<not>equivalent_eq_exists t s C I \<sigma> L"
  assumes "vars_of_lit (subst_lit L \<sigma>) = {}"
  assumes "vars_of_lit (subst_lit L' \<sigma>) = {}"
  assumes "fo_interpretation I"
  shows "((subst_lit L' \<sigma>),(subst_lit L \<sigma>)) \<in> lit_ord"
proof -
  let ?L' = "(subst_lit L' \<sigma>)"
  let ?L = "(subst_lit L \<sigma>)"
  let ?t = "(subst t \<sigma>)"
  let ?s = "(subst s \<sigma>)"

  from assms(2) have "(?t,?s) \<notin> trm_ord" unfolding orient_lit_inst_def by auto
  obtain u' v' where "L' = (Pos (Eq u' v')) \<or> L' = (Neg  (Eq u' v'))" 
    using literal.exhaust equation.exhaust by metis
  from this obtain polarity u v where "orient_lit_inst L' u v polarity \<sigma>" 
    and "((subst u \<sigma>),(subst v \<sigma>)) \<notin>  trm_ord" using  
    trm_ord_trans trm_ord_irrefl unfolding trans_def irrefl_def orient_lit_inst_def by metis
  let ?u = "(subst u \<sigma>)"
  let ?v = "(subst v \<sigma>)"
  from `orient_lit_inst L' u v polarity \<sigma>` have "orient_lit ?L' ?u ?v polarity" 
    using lift_orient_lit by auto
  from `orient_lit_inst L t s pos \<sigma>` have "orient_lit ?L ?t ?s pos" 
    using lift_orient_lit by auto

  from assms(6) and `orient_lit ?L' ?u ?v polarity` 
    have "vars_of ?u \<subseteq> {}" using orient_lit_vars by metis
  from assms(6) and `orient_lit ?L' ?u ?v polarity` 
    have "vars_of ?v \<subseteq> {}" using orient_lit_vars by metis

  from assms(5) and `orient_lit ?L ?t ?s pos` 
    have "vars_of ?t \<subseteq> {}" using orient_lit_vars by metis
  from assms(5) and `orient_lit ?L ?t ?s pos` 
    have "vars_of ?s \<subseteq> {}" using orient_lit_vars by metis

  from assms(1) and `L' \<in> C - { L }` have "(?L,?L') \<notin> lit_ord" 
    unfolding maximal_literal_def by auto
  from this and `orient_lit ?L ?t ?s pos` `orient_lit ?L' ?u ?v polarity` and assms(5) assms(6)
    have "(?t,?u) \<notin> trm_ord" using lit_ord_dominating_term by metis
  from this and `vars_of ?t \<subseteq> {}` `vars_of ?u \<subseteq> {}` have "?u = ?t \<or> (?u,?t) \<in> trm_ord" 
    using trm_ord_ground_total unfolding ground_term_def by blast
  from `(?u,?v) \<notin> trm_ord` and `vars_of ?u \<subseteq> {}` `vars_of ?v \<subseteq> {}` 
    have "?u = ?v \<or> (?v,?u) \<in> trm_ord" 
    using trm_ord_ground_total unfolding ground_term_def by blast
  from `(?t,?s) \<notin> trm_ord` and `vars_of ?t \<subseteq> {}` `vars_of ?s \<subseteq> {}` 
    have "?t = ?s \<or> (?s,?t) \<in> trm_ord" 
    using trm_ord_ground_total unfolding ground_term_def by blast
  from `vars_of ?v \<subseteq> {}` `vars_of ?s \<subseteq> {}` have "?v = ?s \<or> (?v,?s) \<in> trm_ord \<or> (?s,?v) \<in> trm_ord" 
    using trm_ord_ground_total unfolding ground_term_def by blast

  show ?thesis
  proof (cases)
    assume "(?u,?t) \<in> trm_ord" 
    from this and `?u = ?v \<or> (?v,?u) \<in> trm_ord` have "(?v,?t) \<in> trm_ord" 
      using trm_ord_trans unfolding trans_def by auto
    from this and `(?u,?t) \<in> trm_ord` and `orient_lit ?L ?t ?s pos` `orient_lit ?L' ?u ?v polarity` 
      assms(5) assms(6) show ?thesis using  lit_ord_dominating_term by metis
  next
    assume "(?u,?t) \<notin> trm_ord"
    from this and `?u = ?t \<or> (?u,?t) \<in> trm_ord` have "?u = ?t" by auto
    have "polarity = pos"
    proof (rule ccontr)
      assume "polarity \<noteq> pos"
      then have "polarity = neg" using sign.exhaust by auto
      from this and `?u = ?t` and  `orient_lit ?L ?t ?s pos` 
        `orient_lit ?L' ?u ?v polarity` assms(5) assms(6)
        have "(?L,?L') \<in> lit_ord" using lit_ord_neg_lit_lhs by auto
      from this and `(?L,?L') \<notin> lit_ord` show False by auto
    qed
    have "?v \<noteq> ?s"
    proof
      assume "?v = ?s"
      from this assms(7) have "I ?s ?v" unfolding fo_interpretation_def congruence_def 
        equivalence_relation_def reflexive_def by auto 
      from this and `orient_lit_inst L' u v polarity \<sigma>` `polarity = pos` `?u = ?t`
        and assms(3) have "equivalent_eq_exists t s C I \<sigma> L" 
        unfolding equivalent_eq_exists_def by metis
      from this and assms(4) show False by auto
    qed
    have "(?s,?v) \<notin> trm_ord"
    proof
      assume "(?s,?v) \<in> trm_ord"
      from this and `?u = ?t` and  `orient_lit ?L ?t ?s pos` `orient_lit ?L' ?u ?v polarity` 
        and `polarity=pos` assms(5) assms(6)
        have "(?L,?L') \<in> lit_ord" using lit_ord_rhs  by auto
      from this and `(?L,?L') \<notin> lit_ord`show False by auto
    qed
    from this and `?v \<noteq> ?s` and `?v = ?s \<or> (?v,?s) \<in> trm_ord \<or> (?s,?v) \<in> trm_ord` 
      have "(?v,?s) \<in> trm_ord" by metis
      from this and `?u = ?t` and  `orient_lit ?L ?t ?s pos` `orient_lit ?L' ?u ?v polarity` 
        and `polarity=pos` assms(5) assms(6)
        show "(?L',?L) \<in> lit_ord" using lit_ord_rhs  by auto
 qed
qed

lemma if_all_smaller_are_false_then_cl_not_valid:
  assumes "(smaller_lits_are_false (subst t \<sigma>) (subst_cl C \<sigma>) S)"
  assumes "(fo_interpretation (same_values (\<lambda>t. (trm_rep t S))))"
  assumes "orient_lit_inst L1 t s pos \<sigma>"
  assumes "maximal_literal (subst_lit L1 \<sigma>) (subst_cl C \<sigma>)"
  assumes "ground_clause (subst_cl C \<sigma>)"
  assumes "(subst_lit L1 \<sigma>) \<in> (subst_cl C \<sigma>)"
  assumes "\<not>equivalent_eq_exists t s C (same_values (\<lambda>t. (trm_rep t S))) \<sigma> L1"
  assumes "trm_rep (subst t \<sigma>) S = trm_rep (subst s \<sigma>) S"
  shows "(\<not> validate_ground_clause (same_values (\<lambda>t. (trm_rep t S))) (subst_cl ( C - { L1 } ) \<sigma>))"
proof
  let ?I = "(same_values (\<lambda>t. (trm_rep t S)))"
  assume "validate_ground_clause ?I (subst_cl ( C - { L1 } ) \<sigma>)"
  then obtain L where "L \<in> (subst_cl ( C - { L1 } ) \<sigma>)" and "validate_ground_lit ?I L"
    using validate_ground_clause.simps [of ?I "(subst_cl ( C - { L1 } ) \<sigma>)"] by blast
    
  from `L \<in> (subst_cl ( C - { L1 } ) \<sigma>)` obtain L' where "L' \<in> C - { L1 }" and 
    "L = (subst_lit L' \<sigma>)" by auto
  from `L' \<in> C - { L1 }`  and `L = (subst_lit L' \<sigma>)` 
    have "L \<in>(subst_cl C \<sigma>)" by auto
  from `L \<in>(subst_cl C \<sigma>)` and assms(5) have "vars_of_lit L = {}" by auto
  from assms(6) and assms(5) have "vars_of_lit (subst_lit L1 \<sigma>) = {}" by auto

  obtain u v polarity where o: "orient_lit_inst L' u v polarity \<sigma>" 
  and "((subst u \<sigma>), (subst v \<sigma>)) \<notin> trm_ord"
    unfolding orient_lit_inst_def using literal.exhaust equation.exhaust 
      trm_ord_trans trm_ord_irrefl unfolding trans_def irrefl_def by metis 
  from o and `L = (subst_lit L' \<sigma>)` 
    have o' : "orient_lit L (subst u \<sigma>)  (subst v \<sigma>) polarity" 
    using lift_orient_lit by auto

    from o' and `vars_of_lit L = {}` have "vars_of (subst u \<sigma>) = {}" 
      using orient_lit_vars by blast
    from o' and `vars_of_lit L = {}` have "vars_of (subst v \<sigma>) = {}" 
      using orient_lit_vars by blast

  from assms(3)  
    have o1 : "orient_lit (subst_lit L1 \<sigma>) (subst t \<sigma>) (subst s \<sigma>) pos" 
    using lift_orient_lit [of L1 t s pos \<sigma>] by auto
  from o1 and `vars_of_lit (subst_lit L1 \<sigma>) = {}` have "vars_of (subst t \<sigma>) = {}"
      using orient_lit_vars by blast

  have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto    
  then show False
  proof
    assume "polarity = pos" 
    from this and o and assms(2) and `validate_ground_lit ?I L` and `L = (subst_lit L' \<sigma>)` 
      have "(trm_rep (subst u \<sigma>) S) = (trm_rep (subst v \<sigma>) S)"
      using orient_lit_semantics_pos [of ?I ] unfolding same_values_def by metis
    from assms(4) and `L \<in>(subst_cl C \<sigma>)` 
      have "((subst_lit L1 \<sigma>),L) \<notin> lit_ord" unfolding maximal_literal_def
      by blast
    from this and o' and o1 and `polarity=pos` and `vars_of_lit L = {}` and `L = (subst_lit L' \<sigma>)` 
      and `vars_of_lit (subst_lit L1 \<sigma>) = {}` 
      have "(subst t \<sigma>, subst u \<sigma>) \<notin> trm_ord"
      and "(subst t \<sigma>, subst v \<sigma>) \<notin> trm_ord"  
      using lit_ord_dominating_term [of "subst t \<sigma>" "subst u \<sigma>"  
          "subst v \<sigma>" "subst_lit L1 \<sigma>" "subst s \<sigma>" pos] by auto
      show ?thesis
      proof (cases)
        assume "(subst t \<sigma>) = (subst u \<sigma>)"
        from this and assms(8) and `(trm_rep (subst u \<sigma>) S) = (trm_rep (subst v \<sigma>) S)`
          have "(trm_rep (subst s \<sigma>) S) = (trm_rep (subst v \<sigma>) S)" by metis
        from this o and `L' \<in> C - { L1 }` `polarity = pos` `(subst t \<sigma>) = (subst u \<sigma>)` assms(7) 
          show False unfolding equivalent_eq_exists_def same_values_def by blast
      next
        assume "(subst t \<sigma>) \<noteq> (subst u \<sigma>)"
        from this and `(subst t \<sigma>, subst u \<sigma>)  \<notin> trm_ord`
        and `vars_of (subst t \<sigma>) = {}` and `vars_of (subst u \<sigma>) = {}` 
        have "(subst u \<sigma>, subst t \<sigma>) \<in> trm_ord" 
        using trm_ord_ground_total unfolding ground_term_def by auto
        
        from this and `(subst u \<sigma>, subst v \<sigma>)  \<notin> trm_ord`
        and `vars_of (subst v \<sigma>) = {}` and `vars_of (subst t \<sigma>) = {}` 
        have "(subst v \<sigma>, subst t \<sigma>) \<in> trm_ord" 
        using trm_ord_ground_total trm_ord_trans 
        unfolding ground_term_def trans_def by metis
       
        from `polarity = pos` and o' and assms(1) and `L \<in>(subst_cl C \<sigma>)` and `L = (subst_lit L' \<sigma>)`
          and `((subst u \<sigma>), subst t \<sigma>) \<in> trm_ord`
          and `((subst v \<sigma>), subst t \<sigma>) \<in> trm_ord`
          have "trm_rep (subst u \<sigma>) S \<noteq> trm_rep (subst v \<sigma>) S" 
          unfolding smaller_lits_are_false_def by metis  
        from this and `trm_rep (subst u \<sigma>) S = trm_rep (subst v \<sigma>) S` 
          show False by blast
      qed  
    next assume "polarity = neg" 
    from this and o and assms(2) and `validate_ground_lit ?I L` and `L = (subst_lit L' \<sigma>)` 
      have "(trm_rep (subst u \<sigma>) S) \<noteq> (trm_rep (subst v \<sigma>) S)"
      using orient_lit_semantics_neg [of ?I ] unfolding same_values_def by metis
    from assms(4) and `L \<in>(subst_cl C \<sigma>)` 
      have "((subst_lit L1 \<sigma>),L) \<notin> lit_ord" unfolding maximal_literal_def
      by blast
    from this and o' and o1 and `vars_of_lit L = {}` and `L = (subst_lit L' \<sigma>)` 
      and `vars_of_lit (subst_lit L1 \<sigma>) = {}` 
      have "(subst t \<sigma>, subst u \<sigma>) \<notin> trm_ord"
      and "(subst t \<sigma>, subst v \<sigma>) \<notin> trm_ord"  
      using lit_ord_dominating_term [of "subst t \<sigma>" "subst u \<sigma>"  
            "subst v \<sigma>" "subst_lit L1 \<sigma>" "subst s \<sigma>" pos] 
      by auto

    from `((subst_lit L1 \<sigma>),L) \<notin> lit_ord` and o' and o1 and `polarity=neg` and `vars_of_lit L = {}` 
      and `L = (subst_lit L' \<sigma>)` and `vars_of_lit (subst_lit L1 \<sigma>) = {}` 
      have "subst t \<sigma> \<noteq> subst u \<sigma>"
      using lit_ord_neg_lit_lhs by auto
    from this and `(subst t \<sigma>, subst u \<sigma>)  \<notin> trm_ord` and `vars_of (subst t \<sigma>) = {}` 
        and `vars_of (subst u \<sigma>) = {}` 
        have "(subst u \<sigma>, subst t \<sigma>) \<in> trm_ord" 
        using trm_ord_ground_total unfolding ground_term_def by auto
        
     from this and `(subst u \<sigma>, subst v \<sigma>)  \<notin> trm_ord` and `vars_of (subst v \<sigma>) = {}` 
        and `vars_of (subst t \<sigma>) = {}` have "(subst v \<sigma>, subst t \<sigma>) \<in> trm_ord" 
        using trm_ord_ground_total trm_ord_trans unfolding ground_term_def trans_def by metis
       
     from `polarity = neg` and o' and assms(1) and `L \<in>(subst_cl C \<sigma>)` and `L = (subst_lit L' \<sigma>)`
          and `((subst u \<sigma>), subst t \<sigma>) \<in> trm_ord` and `((subst v \<sigma>), subst t \<sigma>) \<in> trm_ord`
          have "trm_rep (subst u \<sigma>) S = trm_rep (subst v \<sigma>) S" 
          unfolding smaller_lits_are_false_def by metis  
     from this and `trm_rep (subst u \<sigma>) S \<noteq> trm_rep (subst v \<sigma>) S` show False by blast
   qed
qed

text {* We introduce the notion of a reduction, which is a ground superposition inference 
satisfying some additional conditions: 

(i) the ``from'' clause is smaller than the ``into'' clause;

(ii) its ``body'' (i.e., the part of the clause without the equation involved 
in the rule) is false in a given interpretation and strictly smaller than the involved equation. *}

definition reduction
where "(reduction L1 C \<sigma>' t s polarity L2 u u' p v D I S \<sigma>) =  
       ( (D \<in> S) \<and> (eligible_literal L1 C \<sigma>') \<and> (eligible_literal L2 D \<sigma>')
       \<and> ground_clause (subst_cl (cl_ecl D) \<sigma>')
       \<and> (minimal_redex p (subst t \<sigma>) C S t)
       \<and> (coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C)))
       \<and> (allowed_redex u' C \<sigma>)
       \<and> (\<not> is_a_variable u')
       \<and> (L1 \<in> (cl_ecl C)) \<and> (L2 \<in> (cl_ecl D))
       \<and> (orient_lit_inst L1 t s polarity \<sigma>') 
       \<and> (orient_lit_inst L2 u v pos \<sigma>') 
       \<and> (subst u \<sigma>') \<noteq> (subst v \<sigma>')
       \<and> (subst u' \<sigma>') = (subst u \<sigma>')
       \<and> (\<not> validate_ground_clause I (subst_cl ( (cl_ecl D) - { L2 } ) \<sigma>'))
       \<and> ( (subst_lit L2 \<sigma>'),(subst_lit L1 \<sigma>')) \<in> lit_ord
       \<and> (\<forall>x \<in> (cl_ecl D) - { L2 }. ( (subst_lit x \<sigma>'),(subst_lit L2 \<sigma>')) 
                                        \<in> lit_ord)
       \<and> (all_trms_irreducible (subst_set (trms_ecl D) \<sigma>') 
                  (\<lambda>t. (trm_rep t S)))
       \<and> (I (subst u \<sigma>')  (subst v \<sigma>')) 
       \<and> (subterm t p u'))"

text {* The next lemma states that the rules used to evaluate terms can be renamed so that
they share no variable with the clause in which the term occurs. *}

lemma candidate_values_renaming:
    assumes "(candidate_values z CC C' C s L L' \<sigma> t' s' t S)"
    assumes "finite C'"
    assumes "finite (cl_ecl (D:: 'a eclause))"
    assumes "closed_under_renaming S"
    assumes "Ball S well_constrained"
    shows "\<exists> CC_bis C'_bis L'_bis \<sigma>_bis t'_bis s'_bis t_bis.
     (candidate_values z CC_bis C'_bis C s L L'_bis \<sigma>_bis t'_bis s'_bis t S)
     \<and> (vars_of_cl (cl_ecl D)) \<inter> vars_of_cl (cl_ecl CC_bis) = {}"

proof -
  from assms(2) have "finite (vars_of_cl C')" using set_of_variables_is_finite_cl by auto
  from assms(3) have "finite (vars_of_cl (cl_ecl D))" using set_of_variables_is_finite_cl 
    by auto
  from infinite_vars have "\<not> (finite vars)" by auto
  from `finite (vars_of_cl C')` `finite (vars_of_cl (cl_ecl D))` 
    and `\<not> (finite vars)` 
    obtain \<eta> where "renaming \<eta> (vars_of_cl C')"
      and "((subst_codomain \<eta> (vars_of_cl C')) \<inter> (vars_of_cl (cl_ecl D))) = {}"
      using renaming_exists [of vars ] by meson
  from this `finite (vars_of_cl C')` obtain \<eta>'
    where i: "(\<forall> x \<in> (vars_of_cl C'). (subst (subst (Var x) \<eta> ) \<eta>') 
                                      = (Var x))" 
    using renamings_admit_inverse by blast
  obtain CC_bis where "CC_bis = (subst_ecl CC \<eta>)" by auto
  obtain C'_bis where "C'_bis = (subst_cl C' \<eta>)" by auto
  from assms(1) have "C' = (cl_ecl CC)" unfolding candidate_values_def by metis
  from this obtain T where "CC = (Ecl C' T)"
    by (metis cl_ecl.simps trms_ecl.elims) 
  from this and `CC_bis = (subst_ecl CC \<eta>)` 
    and `C'_bis = (subst_cl C' \<eta>)` 
    have "C'_bis = (cl_ecl CC_bis)" by auto
  from assms(1) have "CC \<in> S" unfolding candidate_values_def by metis
  from assms(1) have "(s,t) \<in> trm_ord" unfolding candidate_values_def by metis
  from assms(1) have "((s,t) \<in> trm_ord \<longrightarrow> (z = trm_rep s S))" 
    unfolding candidate_values_def by metis
  from assms(1) have "(maximal_literal L C)" unfolding candidate_values_def by metis
  from assms(1) have "(ground_clause C)" unfolding candidate_values_def by metis
  from assms(1) have "L' \<in> C'" unfolding candidate_values_def by metis
  from assms(1) have "L = (subst_lit L' \<sigma>)" 
    unfolding candidate_values_def by metis
  from assms(1) have "(smaller_lits_are_false t C S)" 
    unfolding candidate_values_def by metis
  from assms(1) have "C = (subst_cl C' \<sigma>)" 
    unfolding candidate_values_def by metis
  from assms(1) have "(orient_lit_inst L' t' s' pos \<sigma>)" 
    unfolding candidate_values_def by metis
  from assms(1) have "(trms_irreducible CC \<sigma> S t)" 
    unfolding candidate_values_def by metis
  from assms(1) have "t = subst t' \<sigma>"  unfolding candidate_values_def by metis
  from assms(1) have "s = subst s' \<sigma>"  unfolding candidate_values_def by metis

  from `CC \<in> S` and assms(4) and `renaming \<eta> (vars_of_cl C')` and `C' = (cl_ecl CC)` 
    `CC_bis = (subst_ecl CC \<eta>)` have "CC_bis \<in> S"   
    unfolding closed_under_renaming_def renaming_cl_def by auto
  from assms(1) have "(sel C' = {})" unfolding candidate_values_def by metis
  from this and `renaming \<eta> (vars_of_cl C')` `C' = (cl_ecl CC)` 
    `C'_bis = (subst_cl C' \<eta>)` have "sel C'_bis = {}" 
    using sel_renaming by auto
  obtain L'_bis where "L'_bis = (subst_lit L' \<eta>)" by auto
  from this and `L' \<in> C'` `C'_bis = (subst_cl C' \<eta>)` have "L'_bis \<in> C'_bis" by auto 
  let ?\<theta> = "(comp (comp \<eta> \<eta>') \<sigma>)"
  let ?\<theta>' = "(comp \<eta>' \<sigma>)"
  have "coincide_on \<sigma> ?\<theta> (vars_of_cl C')"
  proof (rule ccontr)
    assume "\<not>coincide_on \<sigma> ?\<theta> (vars_of_cl C')"
    from this obtain x where "(subst (Var x) \<sigma>) \<noteq> (subst (Var x) ?\<theta>)"
      and "x \<in> vars_of_cl C'" unfolding coincide_on_def by auto
    from `x \<in> vars_of_cl C'` i  
      have "(subst (subst (Var x) \<eta> ) \<eta>') = (Var x)"
      by blast
    from this and `(subst (Var x) \<sigma>) \<noteq> (subst (Var x) ?\<theta>)`
      show False by simp 
  qed
  from `L' \<in> C'` have "vars_of_lit L' \<subseteq> vars_of_cl C'" by auto
   from this and `coincide_on \<sigma> ?\<theta> (vars_of_cl C')` 
   have "coincide_on \<sigma> ?\<theta> (vars_of_lit L')" unfolding coincide_on_def by auto
  from this and `L = (subst_lit L' \<sigma>)` 
    have "L = (subst_lit L' ?\<theta>)" using coincide_on_lit by auto
  have "subst_lit L' ?\<theta>
    = subst_lit (subst_lit L' \<eta>) ?\<theta>'"
    by (simp add: coincide_on_def coincide_on_lit composition_of_substs_lit)
  from this and `L = (subst_lit L' ?\<theta>)` and 
    `L'_bis = (subst_lit L' \<eta>)` 
    have "L = (subst_lit L'_bis ?\<theta>')" 
    by auto
  from `coincide_on \<sigma> ?\<theta> (vars_of_cl C')` and `C = (subst_cl C' \<sigma>)` 
    have "C  = subst_cl C' ?\<theta>"
    using coincide_on_cl by blast
  have "subst_cl C' ?\<theta>
    = subst_cl (subst_cl C' \<eta>) ?\<theta>'"
    by (metis composition_of_substs_cl) 
  from this and `C  = subst_cl C' ?\<theta>` and `C'_bis = (subst_cl C' \<eta>)`
    have "C = subst_cl C'_bis ?\<theta>'" by auto
  from `(finite C')` and `C'_bis = (subst_cl C' \<eta>)` have "finite C'_bis" by auto
  have "t \<notin> (subst_set (trms_ecl CC_bis) ?\<theta>')"
  proof  
    assume "t \<in> (subst_set (trms_ecl CC_bis) ?\<theta>')"
    from this obtain u where "u \<in> (trms_ecl CC_bis)" 
      and "t = (subst u ?\<theta>')" by auto
    from `u \<in> (trms_ecl CC_bis)` and `CC_bis = (subst_ecl CC \<eta>)`
      obtain v where "v \<in> trms_ecl CC" and "u = (subst v \<eta>)"
      using \<open>CC = Ecl C' T\<close> by auto
    from `u = (subst v \<eta>)` `t = (subst u ?\<theta>')` have "subst v ?\<theta> = t" by simp
    from `v \<in> trms_ecl CC` `CC \<in> S` assms(5) 
      have "dom_trm v (cl_ecl CC)" unfolding Ball_def well_constrained_def by metis
    from this have "vars_of v \<subseteq> vars_of_cl (cl_ecl CC)" using dom_trm_vars by auto
    from this and `C' = (cl_ecl CC)` `coincide_on \<sigma> ?\<theta> (vars_of_cl C')`  
      have "coincide_on \<sigma> ?\<theta> (vars_of v)" unfolding coincide_on_def by auto
    from this and `subst v ?\<theta> = t` have "(subst v \<sigma>) = t"
      using coincide_on_term by metis
    from this and `v \<in> trms_ecl CC` have 
      "(t \<in> (subst_set (trms_ecl CC) \<sigma>))" by auto
    from this and assms(1) show False unfolding candidate_values_def by metis
  qed
  have "(trms_irreducible CC_bis ?\<theta>' S t)"
  proof (rule ccontr)
    assume "\<not>(trms_irreducible CC_bis ?\<theta>' S t)"
    then obtain x x' where "x' \<in> trms_ecl CC_bis" 
            "occurs_in x (subst x' ?\<theta>')"
            "(x,t) \<in> trm_ord" "(trm_rep x S) \<noteq> x"
            using trms_irreducible_def by blast 
    from `x' \<in> (trms_ecl CC_bis)` and `CC_bis = (subst_ecl CC \<eta>)`
      obtain v where "v \<in> trms_ecl CC" and "x' = (subst v \<eta>)"
      using \<open>CC = Ecl C' T\<close> by auto
    from `occurs_in x (subst x' ?\<theta>')` `x' = subst v \<eta>` have "occurs_in x (subst v ?\<theta>)" by simp
    from `v \<in> trms_ecl CC` `CC \<in> S` assms(5) 
      have "dom_trm v (cl_ecl CC)" unfolding Ball_def well_constrained_def by auto
    from this have "vars_of v \<subseteq> vars_of_cl (cl_ecl CC)" using dom_trm_vars by auto
    from this and `C' = (cl_ecl CC)` `coincide_on \<sigma> ?\<theta> (vars_of_cl C')`  
      have "coincide_on \<sigma> ?\<theta> (vars_of v)" unfolding coincide_on_def by auto
    from this have "(subst v \<sigma>) = (subst v ?\<theta>)" 
      using coincide_on_term by metis
    from this and `occurs_in x (subst v ?\<theta>)` 
      have "occurs_in x (subst v \<sigma>)"  by auto
    from this and `v \<in> trms_ecl CC` and `(x,t) \<in> trm_ord` 
      `(trm_rep x S) \<noteq> x` and `(trms_irreducible CC \<sigma> S t)` show False 
        unfolding trms_irreducible_def by metis
   qed
   obtain t'_bis where "t'_bis = (subst t' \<eta>)" by auto
   obtain s'_bis where "s'_bis = (subst s' \<eta>)" by auto

   from `(orient_lit_inst L' t' s' pos \<sigma>)` have "vars_of t' \<subseteq> vars_of_lit L'" 
      using orient_lit_inst_vars by auto
    from this `coincide_on \<sigma> ?\<theta> (vars_of_lit L')`  
      have "coincide_on \<sigma> ?\<theta> (vars_of t')" unfolding coincide_on_def by blast
    from this have "subst t' ?\<theta> = subst t' \<sigma>" 
      using coincide_on_term by metis
    from this `t'_bis = (subst t' \<eta>)` have "subst t'_bis ?\<theta>' = subst t' \<sigma>" by simp

    from `(orient_lit_inst L' t' s' pos \<sigma>)` have "vars_of s' \<subseteq> vars_of_lit L'" 
      using orient_lit_inst_vars by auto
    from this `coincide_on \<sigma> ?\<theta> (vars_of_lit L')`  
      have "coincide_on \<sigma> ?\<theta> (vars_of s')" unfolding coincide_on_def by blast
    from this have "subst s' ?\<theta> = subst s' \<sigma>" 
      using coincide_on_term by metis
    from this `s'_bis = (subst s' \<eta>)` have "subst s'_bis ?\<theta>' = subst s' \<sigma>" by simp
 
   have "(orient_lit_inst L'_bis t'_bis s'_bis pos ?\<theta>')"
   proof -
    from `(orient_lit_inst L' t' s' pos \<sigma>)` 
      have "((subst t' \<sigma>),(subst s' \<sigma>)) \<notin> trm_ord"  
      using orient_lit_inst_def by simp 
 
    from `(orient_lit_inst L' t' s' pos \<sigma>)` 
      have "L' = (Pos (Eq t' s')) \<or> L' = (Pos (Eq s' t'))"
      by (simp add: orient_lit_inst_def)
    from this 
      `L'_bis = (subst_lit L' \<eta>)`
      `t'_bis = (subst t' \<eta>)`
      `s'_bis = (subst s' \<eta>)`
      have "L'_bis = (Pos (Eq t'_bis s'_bis)) \<or> L'_bis = (Pos (Eq s'_bis t'_bis))"
      by auto
    from `subst s'_bis ?\<theta>' = subst s' \<sigma>` 
      and `subst t'_bis ?\<theta>' = subst t' \<sigma>` 
      and `((subst t' \<sigma>),(subst s' \<sigma>)) \<notin> trm_ord` 
      have "((subst t'_bis ?\<theta>'),(subst s'_bis ?\<theta>')) \<notin> trm_ord"
      by auto
    from this and `L'_bis = (Pos (Eq t'_bis s'_bis)) \<or> L'_bis = (Pos (Eq s'_bis t'_bis))`
      show ?thesis unfolding orient_lit_inst_def by auto
  qed
  have "(maximal_literal_is_unique t s C'_bis L'_bis S ?\<theta>')"
  proof (rule ccontr)
    assume "\<not>(maximal_literal_is_unique t s C'_bis L'_bis S ?\<theta>')"
    from this obtain s'' where "(eq_occurs_in_cl t s'' (C'_bis- { L'_bis }) ?\<theta>')"
                "(s'',t) \<in> trm_ord" 
                "(s,t) \<in> trm_ord"
                "(trm_rep s S) = (trm_rep s'' S)"
                unfolding  maximal_literal_is_unique_def
                by metis
    from `(eq_occurs_in_cl t s'' (C'_bis- { L'_bis }) ?\<theta>')` obtain M u v where 
      "M \<in> C'_bis - { L'_bis }" "orient_lit_inst M u v pos ?\<theta>'" 
      "t = (subst u ?\<theta>')" "s'' = (subst v ?\<theta>')"
      unfolding eq_occurs_in_cl_def by blast
    from `M \<in> C'_bis - { L'_bis }` 
      and `C'_bis = (subst_cl C' \<eta>)` and `L'_bis = (subst_lit L' \<eta>)` 
      obtain M' where "M' \<in> C'- { L' }" and "subst_lit M' \<eta> =  M" by auto
    from `orient_lit_inst M u v pos ?\<theta>'` obtain e where "M = (Pos e)" 
      unfolding orient_lit_inst_def by auto
    from this and  `orient_lit_inst M u v pos ?\<theta>'` have "e = (Eq u v) \<or> e = (Eq v u)"  
      unfolding orient_lit_inst_def by auto
    from `orient_lit_inst M u v pos ?\<theta>'` have 
      "( (subst u ?\<theta>'),(subst v ?\<theta>')) \<notin> trm_ord"
      unfolding orient_lit_inst_def by auto
    from `M = (Pos e)` and `subst_lit M' \<eta> =  M` 
      obtain e' where "(subst_equation e' \<eta>)  = e" and "M' = (Pos e')"
      by (metis (no_types, hide_lams) subst_lit.simps(1) subst_lit.simps(2) atom.simps(1) 
          literal.distinct(1) positive_literal.elims(1)) 
    from `e = (Eq u v) \<or> e = (Eq v u)` and `(subst_equation e' \<eta>)  = e`
      obtain u' v' where "e' = (Eq u' v') \<or> (e' = (Eq v' u'))" and "(subst u' \<eta>) = u" and 
        "(subst v' \<eta>) = v"
        by (metis subst_equation.simps equation.inject subterms_of_eq.cases) 
    from `( (subst u ?\<theta>'),(subst v ?\<theta>')) \<notin> trm_ord`
      `(subst u' \<eta>) = u`
      `(subst v' \<eta>) = v`
      have "( (subst u' ?\<theta>),(subst v' ?\<theta>)) \<notin> trm_ord" by simp
    from this and `M' = (Pos e')` and `e' = (Eq u' v') \<or> (e' = (Eq v' u'))` 
      have "orient_lit_inst M' u' v' pos ?\<theta>"
      unfolding orient_lit_inst_def by auto
    from `M' \<in> C' - { L' }` have "vars_of_lit M' \<subseteq> vars_of_cl C'"  by auto
    from this and `coincide_on \<sigma> ?\<theta> (vars_of_cl C')` have "coincide_on \<sigma> ?\<theta> (vars_of_lit M')" 
      unfolding coincide_on_def by auto
    from this have "coincide_on ?\<theta> \<sigma> (vars_of_lit M')" using coincide_sym by auto
    from this and `orient_lit_inst M' u' v' pos ?\<theta>` have "orient_lit_inst M' u' v' pos \<sigma>"
      using orient_lit_inst_coincide by auto
    from `orient_lit_inst M' u' v' pos ?\<theta>` have "vars_of u' \<subseteq> vars_of_lit M'" and 
       "vars_of v' \<subseteq> vars_of_lit M'"  using orient_lit_inst_vars by auto
    from `vars_of u' \<subseteq> vars_of_lit M'` and `coincide_on ?\<theta> \<sigma> (vars_of_lit M')` 
      have "coincide_on ?\<theta> \<sigma> (vars_of u')" unfolding coincide_on_def by auto
    from this have "subst u' ?\<theta> = subst u' \<sigma>" using coincide_on_term by metis
    from this and `(subst u' \<eta>) = u` have "subst u ?\<theta>' = subst u' \<sigma>" by simp
    from `vars_of v' \<subseteq> vars_of_lit M'` and `coincide_on ?\<theta> \<sigma> (vars_of_lit M')` 
      have "coincide_on ?\<theta> \<sigma> (vars_of v')" unfolding coincide_on_def by auto
    from this have "subst v' ?\<theta> = subst v' \<sigma>" using coincide_on_term by metis
    from this and `(subst v' \<eta>) = v` have "subst v ?\<theta>' = subst v' \<sigma>" by simp
    from `subst v ?\<theta>' = subst v' \<sigma>` `s'' = (subst v ?\<theta>')`
      have "s'' = (subst v' \<sigma>)" by auto
    from `subst u ?\<theta>' = subst u' \<sigma>` `t = (subst u ?\<theta>')`
      have "t = (subst u' \<sigma>)" by auto
    from `s'' = (subst v' \<sigma>)` `t = (subst u' \<sigma>)` 
      `orient_lit_inst M' u' v' pos \<sigma>` `M' \<in> C' - { L'}` 
      have "eq_occurs_in_cl t s'' (C'- { L' }) \<sigma>"
      unfolding eq_occurs_in_cl_def by auto
    from this and `(s'',t) \<in> trm_ord` and `(s,t) \<in> trm_ord` and `(trm_rep s S) = (trm_rep s'' S)`
      have "\<not>(maximal_literal_is_unique t s C' L' S \<sigma>)" unfolding maximal_literal_is_unique_def 
      by blast
    from this and assms(1) show False unfolding candidate_values_def by metis
  qed
 
  from `t'_bis = (subst t' \<eta>)` 
    and `t = subst t' \<sigma>` 
    have "t = subst t'_bis (comp \<eta>' \<sigma>)"
    using `subst t'_bis (comp \<eta>' \<sigma>) = subst t' \<sigma>` by auto 

  from `s'_bis = (subst s' \<eta>)` 
    and `s = subst s' \<sigma>` 
    have "s = subst s'_bis (comp \<eta>' \<sigma>)"
    using `subst s'_bis (comp \<eta>' \<sigma>) = subst s' \<sigma>` by auto 
        
  from `CC_bis \<in> S` `t \<notin> subst_set (trms_ecl CC_bis) (comp \<eta>' \<sigma>)`
    `trms_irreducible CC_bis (comp \<eta>' \<sigma>) S t`
    `C'_bis = cl_ecl CC_bis` `(s, t) \<in> trm_ord` `((s, t) \<in> trm_ord \<longrightarrow> z = trm_rep s S)`
    `orient_lit_inst L'_bis t'_bis s'_bis pos (comp \<eta>' \<sigma>)`
    `sel C'_bis = {}` `L'_bis \<in> C'_bis` `maximal_literal L C` 
    `L = subst_lit L'_bis (comp \<eta>' \<sigma>)`
    `C = subst_cl C'_bis (comp \<eta>' \<sigma>)`
    `ground_clause C` `t = subst t'_bis (comp \<eta>' \<sigma>)`
    `s = subst s'_bis (comp \<eta>' \<sigma>)`
    `finite C'_bis` `smaller_lits_are_false t C S` 
    `maximal_literal_is_unique t s C'_bis L'_bis S (comp \<eta>' \<sigma>)`
    have "(candidate_values z CC_bis C'_bis C s L L'_bis ?\<theta>' t'_bis s'_bis t S)"
    unfolding candidate_values_def by metis
  
    have "vars_of_cl (cl_ecl D) \<inter> (vars_of_cl (cl_ecl CC_bis)) = {}"
    proof (rule ccontr)
      assume "vars_of_cl (cl_ecl D) \<inter> (vars_of_cl (cl_ecl CC_bis)) \<noteq> {}"
      from this and `C'_bis = (cl_ecl CC_bis)`
        obtain x where "x \<in> vars_of_cl C'_bis" and "x \<in> vars_of_cl (cl_ecl D)" by auto
      from `x \<in> vars_of_cl C'_bis`  
        obtain N where "N \<in> C'_bis" and "x \<in> vars_of_lit N" by auto
      from `N \<in> C'_bis` and `C'_bis = (subst_cl C' \<eta>)` obtain N' where
        "N' \<in> C'" and "N = subst_lit N' \<eta>" by auto
      from `x \<in> vars_of_lit N` obtain e where "N = (Pos e) \<or> (N = (Neg e))" 
        and "x \<in> vars_of_eq e"
        by (metis negative_literal.elims(2) negative_literal.elims(3) vars_of_lit.simps(1) 
            vars_of_lit.simps(2)) 
      from `N = (Pos e) \<or> (N = (Neg e))` and `N = subst_lit N' \<eta>` obtain e' where
        "N' = (Pos e') \<or> (N' = (Neg e'))" and "e = subst_equation e' \<eta>"
        by (metis subst_lit.elims atom.simps(1) atom.simps(2)) 

      from `x \<in> vars_of_eq e` obtain u v where "e = (Eq u v)" and "x \<in> vars_of u \<union> vars_of v"
        by (metis equation.exhaust vars_of_eq.simps) 
      from `e = (Eq u v)` and `e = subst_equation e' \<eta>` obtain u' v' where "e' = (Eq u' v')"
        "u = (subst u' \<eta>)" and "v = (subst v' \<eta>)"
        by (metis subst_equation.simps equation.exhaust equation.inject) 
      from `x \<in> vars_of u \<union> vars_of v` have "x \<in> vars_of u \<or> x \<in> vars_of v" by auto
      then show False
      proof 
        assume "x \<in> vars_of u"
        from this and `u = (subst u' \<eta>)` 
          obtain y where "y \<in> vars_of u'" and "x \<in> vars_of (subst (Var y) \<eta>)" 
          using vars_of_instances [of u' \<eta>] by auto
        from `y \<in> vars_of u'` and `e' = (Eq u' v')` have "y \<in> vars_of_eq e'" by auto
        from this and `N' = (Pos e') \<or> (N' = (Neg e'))` have "y \<in> vars_of_lit N'" by auto
        from this and `N' \<in> C'` have "y \<in> vars_of_cl C'" by auto
        from this and `renaming \<eta> (vars_of_cl C')` 
          have "is_a_variable (subst (Var y) \<eta>)" unfolding renaming_def by auto
        from this and `x \<in> vars_of (subst (Var y) \<eta>)` have 
          "Var x = (subst (Var y) \<eta>)"
          by (metis is_a_variable.elims(2) singletonD vars_of.simps(1)) 
        from this and `y \<in> vars_of_cl C'` 
          have "x \<in> (subst_codomain \<eta> (vars_of_cl C'))" unfolding subst_codomain_def by auto
        from this and `x \<in> vars_of_cl (cl_ecl D)` 
          and `((subst_codomain \<eta> (vars_of_cl C')) \<inter> (vars_of_cl (cl_ecl D))) = {}` 
          show False by auto
      next
        assume "x \<in> vars_of v"
        from this and `v = (subst v' \<eta>)` 
          obtain y where "y \<in> vars_of v'" and "x \<in> vars_of (subst (Var y) \<eta>)" 
          using vars_of_instances [of v' \<eta>] by auto
        from `y \<in> vars_of v'` and `e' = (Eq u' v')` have "y \<in> vars_of_eq e'" by auto
        from this and `N' = (Pos e') \<or> (N' = (Neg e'))` have "y \<in> vars_of_lit N'" by auto
        from this and `N' \<in> C'` have "y \<in> vars_of_cl C'" by auto
        from this and `renaming \<eta> (vars_of_cl C')` 
          have "is_a_variable (subst (Var y) \<eta>)" unfolding renaming_def by auto
        from this and `x \<in> vars_of (subst (Var y) \<eta>)` have 
          "Var x = (subst (Var y) \<eta>)"
          by (metis is_a_variable.elims(2) singletonD vars_of.simps(1)) 
        from this and `y \<in> vars_of_cl C'` 
          have "x \<in> (subst_codomain \<eta> (vars_of_cl C'))" unfolding subst_codomain_def by auto
        from this and `x \<in> vars_of_cl (cl_ecl D)` 
          and `((subst_codomain \<eta> (vars_of_cl C')) \<inter> (vars_of_cl (cl_ecl D))) = {}` 
          show False by auto
      qed
    qed
    from this and `(candidate_values z CC_bis C'_bis C s L L'_bis ?\<theta>' t'_bis s'_bis t S)`
        show ?thesis by blast
qed

lemma pos_ord_acyclic:
  shows "acyclic (pos_ord C t)"
by (simp add: acyclic_irrefl pos_ord_irrefl pos_ord_trans)
 
definition proper_subterm_red
  where "proper_subterm_red t S \<sigma> = 
    (\<exists>p s. (subterm t p s \<and> p \<noteq> Nil \<and> (trm_rep (subst s \<sigma>) S \<noteq> (subst s \<sigma>))))"

text {* The following lemma states that if an eligible term in a clause instance 
is not in normal form, then the clause instance must be reducible (according to the previous
definition of @{term "reduction"}). This is the key lemma for proving completeness. 
Note that we assume that the considered substitution is in normal form, so that the reduction 
cannot occur inside a variable. We also rename the clause used for the reduction, to ensure that it 
shares no variable with the provided clause.  
The proof requires an additional hypothesis in the case where the reducible term occurs at the root
position in an eligible term of a positive literal, see the first hypothesis below 
and function @{term "equivalent_eq_exists"}. *}

lemma reduction_exists: 
  assumes "polarity = neg \<or> \<not> equivalent_eq_exists t s (cl_ecl C) (int_clset S) \<sigma> L1
    \<or> proper_subterm_red t S \<sigma>"
  assumes "\<forall>x y. (( x \<in> vars_of_cl (cl_ecl C)) \<longrightarrow> (occurs_in y (subst (Var x) \<sigma>)) 
            \<longrightarrow> trm_rep y S = y)"
  assumes "eligible_literal L1 C \<sigma>"
  assumes "(trm_rep (subst t \<sigma>) S) \<noteq>  (subst t \<sigma>)"
  assumes "L1 \<in> (cl_ecl C)"
  assumes "(orient_lit_inst L1 t s polarity \<sigma>)"
  assumes "\<forall>x \<in> S. finite (cl_ecl x)"
  assumes "ground_clause (subst_cl (cl_ecl C) \<sigma>)"
  assumes "(fo_interpretation (same_values (\<lambda>t. (trm_rep t S))))"
  assumes "C \<in> S"
  assumes "Ball S well_constrained"
  assumes "all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. trm_rep t S)"
  assumes "\<not> validate_ground_clause (int_clset S) (subst_cl (cl_ecl C) \<sigma>)"
  assumes "closed_under_renaming S"

  shows "\<exists>\<sigma>' u u' p v D L2. 
    ((reduction L1 C \<sigma>' t s polarity L2 u u' p v D (same_values (\<lambda>t. (trm_rep t S))) S \<sigma>)
    \<and> (variable_disjoint C D))"

proof -

text {* The first step is to get the minimal reducible position in @{term "(subst t \<sigma>)"} and 
the corresponding subterm @{term "v"}. *}

  let ?Redexes = "{ p. \<exists>v. subterm (subst t \<sigma>) p v \<and> root_term S v \<and> trm_rep v S \<noteq> v }"
  have "?Redexes \<subseteq> pos_of (subst t \<sigma>)" 
  proof
    fix x assume "x \<in> ?Redexes"
    then have "\<exists>v. subterm (subst t \<sigma>) x v" by blast
    then have "position_in x (subst t \<sigma>)" unfolding position_in_def by metis
    then show "x \<in> pos_of (subst t \<sigma>)" by auto
  qed
  from this have "finite ?Redexes" using set_of_positions_is_finite [of "(subst t \<sigma>)" ]
    using finite_subset by blast 
  from assms(4) have "st_red S (subst t \<sigma>)" using subterms_of_irred_trms_are_irred by blast
  from this obtain p' where "p' \<in> ?Redexes"  unfolding st_red_def by blast
  from `finite ?Redexes` this obtain mp where "mp \<in> ?Redexes" 
    and "\<And>p'. (p', mp) \<in> (pos_ord C t) \<Longrightarrow> p' \<notin> ?Redexes"  
    using pos_ord_acyclic [of C t] finite_proj_wf [of ?Redexes p' "pos_ord C t"] by blast
  have mr: "minimal_redex mp (subst t \<sigma>) C S t"
  proof (rule ccontr)
    assume "\<not>minimal_redex mp (subst t \<sigma>) C S t"
    from this obtain p'' v' where "(p'',mp) \<in> (pos_ord C t)" "subterm (subst t \<sigma>) p'' v'" 
      and "trm_rep v' S \<noteq> v'" unfolding minimal_redex_def by blast
    show False
    proof (cases)
      assume "(root_term S v')"
      from this and `subterm (subst t \<sigma>) p'' v'` `trm_rep v' S \<noteq> v'` 
        have "p'' \<in>?Redexes" by blast
      from this and `\<And>p'. (p', mp) \<in> (pos_ord C t) \<Longrightarrow> p' \<notin> ?Redexes` and `(p'',mp) \<in> (pos_ord C t)` 
        show False by blast
      next assume "\<not>(root_term S v')"
      from `trm_rep v' S \<noteq> v'` have "st_red S v'" 
        using subterms_of_irred_trms_are_irred by blast
      from this obtain p''' v'' where "subterm v' p''' v''" "root_term S v''" "trm_rep v'' S \<noteq> v''"
        unfolding st_red_def by blast
      from `subterm v' p''' v''` and `subterm (subst t \<sigma>) p'' v'` 
        have "subterm (subst t \<sigma>) (append p'' p''') v''" 
        using subterm_of_a_subterm_is_a_subterm by metis
      from this and `trm_rep v'' S \<noteq> v''` `root_term S v''` 
        have "(append p'' p''') \<in> ?Redexes" by blast
      from this and `\<And>p'. (p', mp) \<in> (pos_ord C t) \<Longrightarrow> p' \<notin> ?Redexes` 
        have "(append p'' p''',mp) \<notin> (pos_ord C t)" by blast
      from this and `(p'',mp) \<in> (pos_ord C t)` show False using pos_ord_prefix by auto
    qed
  qed  
   
  from `mp \<in> ?Redexes` obtain p v where "mp=p" "subterm (subst t \<sigma>) p v" and "root_term S v"
    and "trm_rep v S \<noteq> v" unfolding st_red_def by blast
  
text {* Second, we find the clause @{term "C2"} and substitution @{term "\<eta>"} that are used to 
determine the value of @{term "v"} according to the definition of @{term "trm_rep"},
 and we prove that they satisfy all the desired properties. 
In particular, clause @{term "C2"}  is renamed to ensure that it shares no variable
with @{term "C"}. *}

  from `subterm (subst t \<sigma>) p v` have 
    si: "(\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x \<sigma>) q1 v) \<and> 
                      (subterm t q2 x) \<and> (p = (append q2 q1))) \<or> 
        ((\<exists> u. (\<not>(is_a_variable u) \<and> (subterm t p u) \<and> (v = (subst u \<sigma>)))))" 
        using subterms_of_instances by metis
  let ?v = "trm_rep v S"
  from `trm_rep v S \<noteq> v` and `root_term S v` have "?v \<in> min_trms (set_of_candidate_values S v)"
    unfolding root_term_def get_min_def by (metis some_in_eq)
  from `?v \<in> min_trms (set_of_candidate_values S v)` obtain pair where "?v = fst pair" 
    and "pair \<in> (set_of_candidate_values S v)" and 
    min_pair: "(\<forall>pair'\<in>set_of_candidate_values S v. (snd pair', snd pair) \<notin> trm_ord)" 
    unfolding min_trms_def by blast

  from `pair \<in> (set_of_candidate_values S v)` have 
  "\<exists>z CC C' C s L L' \<sigma> t' s'. pair = (z, s) \<and> (candidate_values z CC C' C s L L' \<sigma> t' s' v S)"
      unfolding set_of_candidate_values_def [of S v] by blast
   from this obtain zz C2_init Cl_C2_init gr_Cl_C2 gr_rhs gr_L2 L2_init \<eta>_init lhs_init rhs_init  
    where "pair = (zz,  gr_rhs)" 
    and "(candidate_values zz C2_init Cl_C2_init gr_Cl_C2 gr_rhs gr_L2 L2_init
          \<eta>_init lhs_init rhs_init v S)" 
    by blast
   
    from assms(7) and `C \<in> S` have "finite (cl_ecl C)" by auto
    from `(candidate_values zz C2_init Cl_C2_init gr_Cl_C2 gr_rhs gr_L2 L2_init 
            \<eta>_init lhs_init rhs_init v S)`   
      have "finite Cl_C2_init" unfolding candidate_values_def by metis
    
   from assms(11) `closed_under_renaming S` `finite Cl_C2_init` `finite (cl_ecl C)`
    `(candidate_values zz C2_init Cl_C2_init gr_Cl_C2 gr_rhs gr_L2 L2_init 
        \<eta>_init lhs_init rhs_init v S)`
    obtain C2 Cl_C2 \<eta> L2 lhs rhs where
    "(candidate_values zz C2 Cl_C2 gr_Cl_C2 gr_rhs gr_L2 L2 \<eta> lhs rhs v S)"
    and "(vars_of_cl (cl_ecl C) \<inter> vars_of_cl (cl_ecl C2)) = {}" 
      using candidate_values_renaming [of zz C2_init Cl_C2_init gr_Cl_C2 gr_rhs gr_L2 L2_init
        \<eta>_init lhs_init rhs_init v S C]  by auto
   
   from `(candidate_values zz C2 Cl_C2 gr_Cl_C2 gr_rhs gr_L2 L2 \<eta> lhs rhs v S)`
    and `pair = (zz,  gr_rhs)` and `?v = fst pair`
      have cv: "(candidate_values ?v C2 Cl_C2 gr_Cl_C2 gr_rhs gr_L2 L2 \<eta> lhs rhs v S)"
      by (metis fst_conv) 
   from cv have "C2 \<in> S" 
    unfolding candidate_values_def  by metis
   from cv have "ground_clause gr_Cl_C2" 
    unfolding candidate_values_def by metis

   from assms(7) and assms(10) have "finite (vars_of_cl (cl_ecl C))"
    using set_of_variables_is_finite_cl by blast

   from cv have "smaller_lits_are_false v gr_Cl_C2 S" 
      unfolding candidate_values_def by metis

   from cv have "gr_Cl_C2 = subst_cl Cl_C2 \<eta>"
      unfolding candidate_values_def by metis
   from cv have "orient_lit_inst L2 lhs rhs pos \<eta>"
      unfolding candidate_values_def by metis
   from cv have "maximal_literal gr_L2 gr_Cl_C2"
      unfolding candidate_values_def by metis
   from cv have "gr_L2 = subst_lit L2 \<eta>"
      unfolding candidate_values_def by metis
   from cv have "ground_clause gr_Cl_C2" 
      unfolding candidate_values_def by metis
   from cv have "L2 \<in> Cl_C2" 
      unfolding candidate_values_def by metis
   from this and `gr_Cl_C2 = subst_cl Cl_C2 \<eta>` and `gr_L2 = subst_lit L2 \<eta>` 
    have "gr_L2 \<in> gr_Cl_C2" by auto
   from cv have "trm_rep v S = trm_rep gr_rhs S" 
      unfolding candidate_values_def by metis
   from cv have "(gr_rhs, v) \<in> trm_ord" 
      unfolding candidate_values_def by metis
   from cv have "Cl_C2 = cl_ecl C2" 
      unfolding candidate_values_def by metis
   from cv have "v \<notin> subst_set (trms_ecl C2) \<eta>"
      unfolding candidate_values_def by metis 
   from cv have "sel (cl_ecl C2) = {}" 
      unfolding candidate_values_def by metis
   from this and `maximal_literal gr_L2 gr_Cl_C2` and `gr_Cl_C2 = subst_cl Cl_C2 \<eta>`
    and `Cl_C2 = (cl_ecl C2)` and `gr_L2 = subst_lit L2 \<eta>` have "eligible_literal L2 C2 \<eta>"
      unfolding eligible_literal_def by auto
   from cv have "(gr_rhs, v) \<in> trm_ord" 
      unfolding candidate_values_def by metis
   
   from cv have norm: "(\<forall>x. (\<exists>x'\<in> trms_ecl C2. occurs_in x (subst x' \<eta>)) \<longrightarrow>
       (x, v) \<in> trm_ord \<longrightarrow> trm_rep x S = x)" 
      unfolding candidate_values_def trms_irreducible_def by metis

    from `ground_clause gr_Cl_C2` and `gr_L2 \<in> gr_Cl_C2` have "vars_of_lit gr_L2 = {}" 
       by auto  
   from cv have "v = subst lhs \<eta>" unfolding candidate_values_def by metis
   from cv have "gr_rhs = subst rhs \<eta>" unfolding candidate_values_def by metis
   
   let ?I = "(same_values (\<lambda>t. (trm_rep t S)))"

   have no_fact: "\<not> equivalent_eq_exists lhs rhs Cl_C2 (same_values (\<lambda>t. trm_rep t S)) \<eta> L2"
   proof 
    assume "equivalent_eq_exists lhs rhs Cl_C2 (same_values (\<lambda>t. trm_rep t S)) \<eta> L2"
    from this have "\<exists>L\<in>Cl_C2 - {L2}.\<exists>u v. orient_lit_inst L u v pos \<eta> \<and>
           subst lhs \<eta> = subst u \<eta> \<and> same_values (\<lambda>t. trm_rep t S) (subst rhs \<eta>) (subst v \<eta>)"
           unfolding equivalent_eq_exists_def
           by blast 
    from this obtain M where "M\<in>Cl_C2 - {L2}" and e: "\<exists>u v. orient_lit_inst M u v pos \<eta> \<and>
           subst lhs \<eta> = subst u \<eta> \<and> same_values (\<lambda>t. trm_rep t S) (subst rhs \<eta>) (subst v \<eta>)"
           by blast 
    from e obtain u' v' where "orient_lit_inst M u' v' pos \<eta>" 
        and i: "subst lhs \<eta> = subst u' \<eta> \<and> same_values (\<lambda>t. trm_rep t S) (subst rhs \<eta>) (subst v' \<eta>)"
        by blast  
    
    from i have "subst lhs \<eta> = subst u' \<eta>" by blast
    from i have "trm_rep (subst rhs \<eta>) S = trm_rep (subst v' \<eta>) S" unfolding same_values_def by blast
    let ?u' = "(subst u' \<eta>)"
    let ?v' = "(subst v' \<eta>)"
    from `orient_lit_inst M u' v' pos \<eta>` have "orient_lit (subst_lit M \<eta>) ?u' ?v' pos"
      using lift_orient_lit by auto  
    from `orient_lit_inst L2 lhs rhs pos \<eta>` have "orient_lit (subst_lit L2 \<eta>) (subst lhs \<eta>) 
      (subst rhs \<eta>) pos" 
      using lift_orient_lit by auto  
    from `orient_lit_inst M u' v' pos \<eta>` and `M \<in> (Cl_C2 - {L2})` and 
    `gr_Cl_C2 = subst_cl Cl_C2 \<eta>`
      have "eq_occurs_in_cl ?u' ?v' (Cl_C2 - {L2}) \<eta>" unfolding eq_occurs_in_cl_def by auto

    from `M\<in>Cl_C2 - {L2}` and `gr_Cl_C2 = subst_cl Cl_C2 \<eta>` 
      have "(subst_lit M \<eta>) \<in> (subst_cl (Cl_C2 - { L2 }) \<eta>)"  by auto
    from `M\<in>Cl_C2 - {L2}` and `gr_Cl_C2 = subst_cl Cl_C2 \<eta>` 
      have "(subst_lit M \<eta>) \<in> gr_Cl_C2" by auto
       
    from `vars_of_lit gr_L2 = {}` and `gr_L2 = subst_lit L2 \<eta>`  
      `orient_lit (subst_lit L2 \<eta>) (subst lhs \<eta>) (subst rhs \<eta>) pos` 
      have "vars_of (subst rhs \<eta>) = {}" using orient_lit_vars by blast

    from `ground_clause gr_Cl_C2` and `(subst_lit M \<eta>) \<in> gr_Cl_C2` 
      have "vars_of_lit (subst_lit M \<eta>) = {}" by auto
    from this and `orient_lit (subst_lit M \<eta>) ?u' ?v' pos` 
      have "vars_of ?v' = {}" using orient_lit_vars by blast

    from `maximal_literal gr_L2 gr_Cl_C2` and `(subst_lit M \<eta>) \<in> gr_Cl_C2` 
      have "(gr_L2,(subst_lit M \<eta>)) \<notin> lit_ord"
      unfolding maximal_literal_def  by auto

    from this and `orient_lit (subst_lit M \<eta>) ?u' ?v' pos` 
      and `orient_lit (subst_lit L2 \<eta>) (subst lhs \<eta>) (subst rhs \<eta>) pos`
      and `subst lhs \<eta> = subst u' \<eta>` 
      and `vars_of_lit gr_L2 = {}` and  `vars_of_lit (subst_lit M \<eta>) = {}` 
      and `gr_L2 = subst_lit L2 \<eta>` have "((subst rhs \<eta>),?v') \<notin>  trm_ord" 
      using lit_ord_rhs by auto
    
    from this and `vars_of ?v' = {}` and `vars_of (subst rhs \<eta>) = {}` 
      have "?v' = (subst rhs \<eta>) \<or> (?v',(subst rhs \<eta>)) \<in>  trm_ord" 
      using trm_ord_ground_total unfolding ground_term_def by auto
    from this and `(gr_rhs,v) \<in> trm_ord` and `gr_rhs = subst rhs \<eta>` have 
     "(?v',v) \<in> trm_ord" using trm_ord_trans unfolding trans_def by auto
    from cv have "maximal_literal_is_unique v gr_rhs Cl_C2 L2 S \<eta>" 
      unfolding candidate_values_def by metis
    from `orient_lit_inst M u' v' pos \<eta>` have "((subst u' \<eta>),(subst v' \<eta>)) \<notin> trm_ord" 
      unfolding orient_lit_inst_def by auto

      have "trm_rep gr_rhs S \<noteq> trm_rep (subst v' \<eta>) S"
        by (metis `(subst v' \<eta>, v) \<in> trm_ord` `(gr_rhs, v) \<in> trm_ord` 
          `subst lhs \<eta> = subst u' \<eta>` 
          `eq_occurs_in_cl (subst u' \<eta>) (subst v' \<eta>) (Cl_C2 - {L2}) \<eta>` 
          `maximal_literal_is_unique v gr_rhs Cl_C2 L2 S \<eta>` `v = subst lhs \<eta>` 
            maximal_literal_is_unique_def) 

    from this and `trm_rep (subst rhs \<eta>) S = trm_rep (subst v' \<eta>) S`
      and `gr_rhs = (subst rhs \<eta>)` show False by blast
   qed
   from  this `gr_Cl_C2 = subst_cl Cl_C2 \<eta>`  
   and  `gr_L2 = subst_lit L2 \<eta>`  
   and `smaller_lits_are_false v gr_Cl_C2 S` and assms(9) and `orient_lit_inst L2 lhs rhs pos \<eta>`
   and `maximal_literal gr_L2 gr_Cl_C2` 
   and `ground_clause gr_Cl_C2`
   and `gr_L2 \<in> gr_Cl_C2` and `v = subst lhs \<eta>` `gr_rhs = subst rhs \<eta>`
   and `trm_rep v S = trm_rep gr_rhs S` 
   have "(\<not> validate_ground_clause ?I (subst_cl ( Cl_C2 - { L2 } ) \<eta>))"
   using if_all_smaller_are_false_then_cl_not_valid [of lhs \<eta> "Cl_C2" S L2 rhs] by blast
   
text {* We fuse the substitutions @{term "\<sigma>"} and @{term "\<eta>"} so that the superposition rule 
can be applied: *}

   from `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
    have "ground_on (vars_of_cl (cl_ecl C)) \<sigma>" using ground_clauses_and_ground_substs
    by auto
   from `finite (vars_of_cl (cl_ecl C))` `(vars_of_cl (cl_ecl C) \<inter> vars_of_cl (cl_ecl C2)) = {}`
    `ground_on (vars_of_cl (cl_ecl C)) \<sigma>`  obtain \<sigma>' where
      "coincide_on \<sigma>' \<sigma> (vars_of_cl (cl_ecl C))" and "coincide_on \<sigma>' \<eta> (vars_of_cl (cl_ecl C2))"
      using combine_substs [of "(vars_of_cl (cl_ecl C))" "(vars_of_cl (cl_ecl C2))" \<sigma> \<eta>] by blast  

   from `coincide_on \<sigma>' \<sigma> (vars_of_cl (cl_ecl C))` have "coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))" 
    using coincide_sym by auto
   from `coincide_on \<sigma>' \<eta> (vars_of_cl (cl_ecl C2))` have "coincide_on \<eta> \<sigma>' (vars_of_cl (cl_ecl C2))" 
    using coincide_sym by auto

   from `eligible_literal L1 C \<sigma>` `L1 \<in> (cl_ecl C)` `coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))`  
    have "eligible_literal L1 C \<sigma>'" using eligible_literal_coincide by auto

   from `eligible_literal L2 C2 \<eta>` `L2 \<in> Cl_C2` `Cl_C2 = (cl_ecl C2)` `coincide_on \<eta> \<sigma>' 
          (vars_of_cl (cl_ecl C2))`  
    have "eligible_literal L2 C2 \<sigma>'" using eligible_literal_coincide by auto

   from `ground_clause gr_Cl_C2` and `gr_Cl_C2 = (subst_cl Cl_C2 \<eta>)` 
    have "ground_clause (subst_cl Cl_C2 \<sigma>')"
    by (metis `Cl_C2 = cl_ecl C2` `coincide_on \<sigma>' \<eta> (vars_of_cl (cl_ecl C2))` coincide_on_cl) 

   from `coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))` `L1 \<in> (cl_ecl C)` have
      "coincide_on \<sigma> \<sigma>' (vars_of_lit L1)" unfolding coincide_on_def by auto

   from `coincide_on \<eta> \<sigma>' (vars_of_cl (cl_ecl C2))` `L2 \<in> Cl_C2` and `Cl_C2 = (cl_ecl C2)` 
    have "coincide_on \<eta> \<sigma>' (vars_of_lit L2)" unfolding coincide_on_def by auto

   from `(orient_lit_inst L1 t s polarity \<sigma>)` and  `coincide_on \<sigma> \<sigma>' (vars_of_lit L1)` 
    have "(orient_lit_inst L1 t s polarity \<sigma>')" 
    using orient_lit_inst_coincide [of L1 t s polarity \<sigma> \<sigma>'] by blast

   from `(orient_lit_inst L2 lhs rhs pos \<eta>)` and  `coincide_on \<eta> \<sigma>' (vars_of_lit L2)` 
    have "(orient_lit_inst L2 lhs rhs pos \<sigma>')" using orient_lit_inst_coincide  by blast

text {* To prove that the superposition rule is applicable, we need to show that @{term "v"}
does not occur inside a variable: *}

   have "\<not>(\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x \<sigma>) q1 v) \<and> 
                      (subterm t q2 x) \<and> (p = (append q2 q1)))" 
   proof 
    assume "(\<exists>x q1 q2. (is_a_variable x) \<and> (subterm (subst x \<sigma>) q1 v) \<and> 
                      (subterm t q2 x) \<and> (p = (append q2 q1)))"
    then obtain x q1 q2 where "is_a_variable x" "subterm (subst x \<sigma>) q1 v" 
      "(subterm (subst x \<sigma>) q1 v)" "(subterm t q2 x)" by auto
    from `(subterm (subst x \<sigma>) q1 v)` have "occurs_in v (subst x \<sigma>)" 
      unfolding occurs_in_def by auto
    from `is_a_variable x` obtain x' where "x = Var x'" using is_a_variable.elims(2) by blast
    from `subterm t q2 x`  have "x \<in> subterms_of t"
      using subterms_of.simps unfolding  occurs_in_def by blast
    from this have "x \<in> subterms_of_lit L1" using assms(6) by (simp add: orient_lit_inst_subterms)   
    from this `L1 \<in> (cl_ecl C)` have "x \<in> subterms_of_cl (cl_ecl C)" by auto
    from this have "vars_of x \<subseteq> vars_of_cl (cl_ecl C)" using subterm_vars by blast 
    from this and `x = (Var x')` have "x' \<in> vars_of_cl (cl_ecl C)" by auto 
    from `x' \<in> vars_of_cl (cl_ecl C)` `occurs_in v (subst x \<sigma>)` 
      `x = Var x'` assms(2) have "trm_rep v S = v" by blast
    from this and `trm_rep v S \<noteq> v` show False by blast
   qed
   from this and si obtain u where "\<not> (is_a_variable u)" "(subterm t p u)" and "v = (subst u \<sigma>)" 
      by auto

   from `orient_lit_inst L1 t s polarity \<sigma>` have "vars_of t \<subseteq> vars_of_lit L1" 
      using orient_lit_inst_vars by auto
   from `subterm t p u` have "vars_of u \<subseteq> vars_of t" using vars_subterm by auto
   from `vars_of t \<subseteq> vars_of_lit L1` `vars_of u \<subseteq> vars_of t` `coincide_on \<sigma> \<sigma>' (vars_of_lit L1)` 
      have "coincide_on \<sigma> \<sigma>' (vars_of u)" unfolding coincide_on_def by blast
   from this have "subst u \<sigma> = subst u \<sigma>'" using coincide_on_term by auto

   from `orient_lit_inst L2 lhs rhs pos \<eta>` have "vars_of lhs \<subseteq> vars_of_lit L2" 
      and "vars_of rhs \<subseteq> vars_of_lit L2" using orient_lit_inst_vars by auto
   from `vars_of lhs \<subseteq> vars_of_lit L2` `coincide_on \<eta> \<sigma>' (vars_of_lit L2)` 
      have "coincide_on \<eta> \<sigma>' (vars_of lhs)" unfolding coincide_on_def by blast
   from this have "subst lhs \<eta> = subst lhs \<sigma>'" 
      using coincide_on_term by auto

   from `vars_of rhs \<subseteq> vars_of_lit L2` `coincide_on \<eta> \<sigma>' (vars_of_lit L2)` 
      have "coincide_on \<eta> \<sigma>' (vars_of rhs)" unfolding coincide_on_def by blast
   from this have "subst rhs \<eta> = subst rhs \<sigma>'" 
      using coincide_on_term by auto
   
   from `trm_rep v S = trm_rep gr_rhs S` and `v= subst lhs \<eta>` and `gr_rhs = (subst rhs \<eta>)` 
      have "trm_rep (subst rhs \<eta>) S = trm_rep (subst lhs \<eta>) S" by metis

   from this and `subst rhs \<eta> = subst rhs \<sigma>'`  `subst lhs \<eta> = subst lhs \<sigma>'` 
      have  "trm_rep (subst rhs \<sigma>') S = trm_rep (subst lhs \<sigma>') S" by metis

   from `subst lhs \<eta> = subst lhs \<sigma>'` `subst u \<sigma> = subst u \<sigma>'` `v = subst u \<sigma>` and `v = subst lhs \<eta>` 
      have "subst u \<sigma>' = subst lhs \<sigma>'"  by auto

   from `coincide_on \<sigma>' \<eta> (vars_of_cl (cl_ecl C2))` and `Cl_C2 = (cl_ecl C2)`
      have "coincide_on \<sigma>' \<eta>  (vars_of_cl (Cl_C2 - { L2 }))" unfolding coincide_on_def by auto
   from this and `(\<not> validate_ground_clause ?I (subst_cl ( Cl_C2 - { L2 } ) \<eta>))` 
      have "(\<not> validate_ground_clause ?I (subst_cl ( Cl_C2 - { L2 } ) \<sigma>'))"
      using coincide_on_cl by metis

   have "(\<forall>x\<in>cl_ecl C2 - {L2}. (subst_lit x \<sigma>', subst_lit L2 \<sigma>') \<in> lit_ord)"
   proof 
    fix x assume "x \<in>cl_ecl C2 - {L2}"
    from `L2 \<in> Cl_C2` and  `gr_L2 = (subst_lit L2 \<eta>)`  
      `gr_Cl_C2 = (subst_cl Cl_C2 \<eta>)` have "gr_L2 \<in> gr_Cl_C2" by auto
    from this and `ground_clause gr_Cl_C2` have "vars_of_lit gr_L2 = {}" by auto
    from `x \<in> cl_ecl C2 - {L2}` and `Cl_C2 = (cl_ecl C2)`  `gr_Cl_C2 = (subst_cl Cl_C2 \<eta>)`
      have "(subst_lit x \<eta>) \<in> gr_Cl_C2" by auto 
    from this and `ground_clause gr_Cl_C2` have "vars_of_lit (subst_lit x \<eta>) = {}" by auto
    
    from this `x \<in> cl_ecl C2 - {L2}` `maximal_literal gr_L2 gr_Cl_C2` `Cl_C2 = cl_ecl C2` 
    `gr_L2 = (subst_lit L2 \<eta>)`  
    `gr_Cl_C2 = (subst_cl Cl_C2 \<eta>)` `orient_lit_inst L2 lhs rhs pos \<eta>` no_fact assms(9)
    `vars_of_lit gr_L2 = {}` `vars_of_lit (subst_lit x \<eta>) = {}`
    have "(subst_lit x \<eta>, subst_lit L2 \<eta>) \<in> lit_ord" 
    using max_pos_lit_dominates_cl [of L2 \<eta> Cl_C2 lhs rhs x ?I] by metis

    from `L2 \<in> Cl_C2` have "vars_of_lit L2 \<subseteq> vars_of_cl Cl_C2" by auto
    from this and `coincide_on \<sigma>' \<eta> (vars_of_cl (cl_ecl C2))` and `Cl_C2 = cl_ecl C2`
      have "coincide_on \<sigma>' \<eta> (vars_of_lit L2)" unfolding coincide_on_def by auto
    from this have "subst_lit L2 \<sigma>' = subst_lit L2 \<eta>" using coincide_on_lit by auto

    from `x \<in> (cl_ecl C2) - {L2}` have "x \<in> cl_ecl C2" by auto
    from this have "vars_of_lit x \<subseteq> vars_of_cl (cl_ecl C2)" by auto
    from this and `coincide_on \<sigma>' \<eta> (vars_of_cl (cl_ecl C2))`
      have "coincide_on \<sigma>' \<eta> (vars_of_lit x)" unfolding coincide_on_def by auto
    from this have "subst_lit x \<sigma>' = subst_lit x \<eta>" using coincide_on_lit by auto

    from `(subst_lit x \<eta>, subst_lit L2 \<eta>) \<in> lit_ord`
      `subst_lit L2 \<sigma>' = subst_lit L2 \<eta>` 
      `subst_lit x \<sigma>' = subst_lit x \<eta>` 
      show "(subst_lit x \<sigma>',subst_lit L2 \<sigma>') \<in> lit_ord" by metis
   qed

   have "all_trms_irreducible (subst_set (trms_ecl C2) \<sigma>') (\<lambda>t. trm_rep t S)"
   proof (rule ccontr)
    assume "\<not>all_trms_irreducible (subst_set (trms_ecl C2) \<sigma>') (\<lambda>t. trm_rep t S)"
    from this obtain x y where "x \<in> (subst_set (trms_ecl C2) \<sigma>')" and "occurs_in y x"
      and "trm_rep y S \<noteq> y" unfolding all_trms_irreducible_def by blast
    from `x \<in> (subst_set (trms_ecl C2) \<sigma>')` obtain x' where "x' \<in> trms_ecl C2"
      and "x = (subst x' \<sigma>')" by auto
    from assms(11) and `x' \<in> (trms_ecl C2)` and `C2 \<in> S`
      have "dom_trm x' (cl_ecl C2)" unfolding Ball_def well_constrained_def by blast
    from this obtain x'' 
       where "x'' \<in> subterms_of_cl (cl_ecl C2)" and "x'' = x' \<or> (x',x'') \<in> trm_ord"
       using dom_trm_lemma by blast
    from `dom_trm x' (cl_ecl C2)` have "vars_of x'  \<subseteq> vars_of_cl (cl_ecl C2)" 
      using dom_trm_vars by blast
    from this and `coincide_on \<sigma>' \<eta> (vars_of_cl (cl_ecl C2))` have "coincide_on \<sigma>' \<eta> (vars_of x')" 
      unfolding coincide_on_def by auto
    from this have "(subst x' \<eta>) = (subst x' \<sigma>')" using coincide_on_term by metis
    from this and `x = (subst x' \<sigma>')` have "x = (subst x' \<eta>)" by auto
    from this and `x' \<in> trms_ecl C2` have "x \<in>(subst_set (trms_ecl C2) \<eta>)"
      by auto
    from `x'' \<in> (subterms_of_cl (cl_ecl C2))` have 
        "(subst x'' \<eta>) \<in> (subterms_of_cl (subst_cl (cl_ecl C2) \<eta>))"
        using subterm_cl_subst [of x'' "cl_ecl C2"] by auto 

    from `orient_lit_inst L2 lhs rhs pos \<eta>` `gr_rhs = (subst rhs \<eta>)` 
      `gr_L2 = (subst_lit L2 \<eta>)` 
      have "orient_lit gr_L2  (subst lhs \<eta>) gr_rhs pos"
      using lift_orient_lit
      by auto
    from `ground_clause gr_Cl_C2` have "vars_of_cl gr_Cl_C2 = {}" by auto
    from  `vars_of_lit gr_L2 = {}` `vars_of_cl gr_Cl_C2 = {}` 
    `(subst x'' \<eta>) \<in> (subterms_of_cl (subst_cl (cl_ecl C2) \<eta>))` 
    `orient_lit gr_L2 (subst lhs \<eta>) gr_rhs pos` `maximal_literal gr_L2 gr_Cl_C2`  
    `Cl_C2 = cl_ecl C2` `gr_L2 = (subst_lit L2 \<eta>)`  
    `gr_Cl_C2 = (subst_cl Cl_C2 \<eta>)` `v = (subst lhs \<eta>)` `v = (subst lhs \<eta>)` 
      have "(subst x'' \<eta>) = v \<or> (((subst x'' \<eta>),v) \<in> trm_ord)"
      using subterms_dominated [of gr_L2 gr_Cl_C2  "(subst lhs \<eta>)" gr_rhs pos "subst x'' \<eta>"]
      by metis
    from `x'' = x' \<or> (x',x'') \<in> trm_ord`  `x = (subst x' \<eta>)` have
      "(subst x'' \<eta>) = x \<or> (x,(subst x'' \<eta>)) \<in> trm_ord"
      using trm_ord_subst by metis
    from this and `(subst x'' \<eta>) = v \<or> (((subst x'' \<eta>),v) \<in> trm_ord)` 
      have "x = v \<or> ((x,v) \<in> trm_ord)" using trm_ord_trans trans_def by metis
    then show False
    proof
      assume "x = v"
      from this and `v \<notin> subst_set (trms_ecl C2) \<eta>` 
      `x \<in> (subst_set (trms_ecl C2) \<eta>)` show False by auto
    next
      assume "(x,v) \<in> trm_ord"
      from `occurs_in y x` have "y = x \<or> (y,x) \<in> trm_ord" unfolding occurs_in_def 
        using subterm_trm_ord_eq by auto
      from this and `(x,v) \<in> trm_ord` have "(y,v) \<in> trm_ord" using trm_ord_trans 
        unfolding trans_def by metis
      from this and norm and `trm_rep y S \<noteq> y` and `occurs_in y x` and `x' \<in> trms_ecl C2`
        and `x = (subst x' \<eta>)` show False by metis
    qed
   qed
   
   from `subterm t p u` have "u = t \<or> (u,t) \<in> trm_ord" using subterm_trm_ord_eq by auto
   from assms(8) and `L1 \<in> (cl_ecl C)` have "vars_of_lit (subst_lit L1 \<sigma>) = {}"
    by auto
   from `coincide_on \<sigma> \<sigma>' (vars_of_lit L1)` have "(subst_lit L1 \<sigma>) = (subst_lit L1 \<sigma>')"
      using  coincide_on_lit by metis
   from this and  `vars_of_lit (subst_lit L1 \<sigma>) = {}` 
     have "vars_of_lit (subst_lit L1 \<sigma>') = {}" by auto

   from `coincide_on \<eta> \<sigma>' (vars_of_lit L2)` have "(subst_lit L2 \<eta>) = (subst_lit L2 \<sigma>')"
      using  coincide_on_lit by metis
   from `vars_of_lit gr_L2 = {}` `ground_clause gr_Cl_C2` `gr_Cl_C2 = (subst_cl Cl_C2 \<eta>)` 
    `L2 \<in> Cl_C2` have "vars_of_lit (subst_lit L2 \<eta>) = {}" by auto
   from this and `(subst_lit L2 \<eta>) = (subst_lit L2 \<sigma>')`
    have "vars_of_lit (subst_lit L2 \<sigma>') = {}" by auto
   
text {* We now prove that the ``into'' clause is strictly smaller than the ``from'' clause. This is
easy if the rewritten literal is negative or if the reduction does not occur at root level. 
Otherwise, we must use the fact that the function @{term "trm_rep"} selects the smallest right-hand
side to compute the value of a term. *}

  have "(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<in> lit_ord"  
   proof (rule ccontr)
    assume "\<not>(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<in> lit_ord"
    from `orient_lit_inst L1 t s polarity \<sigma>'` 
        have "orient_lit (subst_lit L1 \<sigma>') 
          (subst t \<sigma>') (subst s \<sigma>') polarity"
        using lift_orient_lit [of L1 t s polarity \<sigma>'] by auto
      from `orient_lit_inst L2 lhs rhs pos \<sigma>'` 
        have "orient_lit (subst_lit L2 \<sigma>') 
          (subst lhs \<sigma>') (subst rhs \<sigma>') pos"
        using lift_orient_lit by auto
    have "(u,t) \<notin> trm_ord"
    proof
      assume "(u,t) \<in> trm_ord"
      from this have "(subst u \<sigma>', subst t \<sigma>') \<in> trm_ord" 
        using trm_ord_subst by auto
      have False "subst u \<sigma>' = subst lhs \<sigma>'" 
        using `(subst u \<sigma>', subst t \<sigma>') \<in> trm_ord` 
        `(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<notin> lit_ord` `subst lhs \<eta> = subst lhs \<sigma>'` 
        `subst u \<sigma> = subst u \<sigma>'` `subst_lit L2 \<eta> = subst_lit L2 \<sigma>'` `gr_L2 = subst_lit L2 \<eta>` 
        `orient_lit (subst_lit L1 \<sigma>') (subst t \<sigma>') (subst s \<sigma>') polarity` 
        `orient_lit (subst_lit L2 \<sigma>') (subst lhs \<sigma>') (subst rhs \<sigma>') pos` `v = subst lhs \<eta>` 
        `v = subst u \<sigma>` `vars_of_lit (subst_lit L1 \<sigma>') = {}` `vars_of_lit gr_L2 = {}` 
        lit_ord_dominating_term apply fastforce
        using `(subst u \<sigma>', subst t \<sigma>') \<in> trm_ord` 
        `(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<notin> lit_ord` 
        `subst u \<sigma>' = subst lhs \<sigma>'` 
        `orient_lit (subst_lit L1 \<sigma>') (subst t \<sigma>') (subst s \<sigma>') polarity` 
        `orient_lit (subst_lit L2 \<sigma>') (subst lhs \<sigma>') (subst rhs \<sigma>') pos` 
        `vars_of_lit (subst_lit L1 \<sigma>') = {}` `vars_of_lit (subst_lit L2 \<sigma>') = {}` 
        lit_ord_dominating_term by fastforce  
      then show False by auto
    qed
    from this and `subterm t p u` have "p = Nil" using subterm_trm_ord by auto

    have "\<not> proper_subterm_red t S \<sigma>" 
    proof 
      assume "proper_subterm_red t S \<sigma>"
      from this obtain p' s where "p' \<noteq> Nil" and "subterm t p' s" 
        "trm_rep (subst s \<sigma>) S \<noteq> (subst s \<sigma>)"
        unfolding proper_subterm_red_def by blast
      from `p = Nil` and `p' \<noteq> Nil` have "(p',p) \<in> (pos_ord C t)" 
        using pos_ord_nil by auto
      from `subterm t p' s` have "subterm (subst t \<sigma>) p' (subst s \<sigma>)"   
        by (simp add: substs_preserve_subterms)
        
      from this and `(p',p) \<in> (pos_ord C t)` mr and `trm_rep (subst s \<sigma>) S \<noteq> (subst s \<sigma>)` `mp=p`
        show False using minimal_redex_def by blast
    qed
    
    from `(u,t) \<notin> trm_ord` and `u = t \<or> (u,t) \<in> trm_ord` have "u = t" by auto
    have "polarity = pos"
    proof (rule ccontr)
      assume "polarity \<noteq> pos"
      then have "polarity = neg" using sign.exhaust by auto
      from `u = t` have "subst t \<sigma>' = subst u \<sigma>'" by auto
      from this and `v = (subst u \<sigma>)` and `v = (subst lhs \<eta>)`
          and `subst lhs \<eta> = subst lhs \<sigma>'` 
          and `(subst u \<sigma>) = (subst u \<sigma>')` 
          have "(subst t \<sigma>') = (subst lhs \<sigma>')" by auto 
      from this and `polarity = neg` `orient_lit (subst_lit L1 \<sigma>') 
          (subst t \<sigma>') (subst s \<sigma>') polarity` 
           and `orient_lit (subst_lit L2 \<sigma>') 
          (subst lhs \<sigma>') (subst rhs \<sigma>') pos` 
          `(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<notin> lit_ord`
          `vars_of_lit (subst_lit L1 \<sigma>')  = {}` 
          `vars_of_lit (subst_lit L2 \<sigma>') = {}` 
       show False using lit_ord_neg_lit_lhs by auto
     qed
     from  `vars_of_lit (subst_lit L1 \<sigma>) = {}` assms(6) 
            have "vars_of (subst t \<sigma>) = {}" using lift_orient_lit orient_lit_vars 
            by blast
     from  `vars_of_lit (subst_lit L1 \<sigma>) = {}` assms(6) 
            have "vars_of (subst s \<sigma>) = {}" using lift_orient_lit orient_lit_vars 
            by blast

     have "trm_rep (subst t \<sigma>) S \<noteq> trm_rep (subst s \<sigma>) S"
     proof 
      assume "trm_rep (subst t \<sigma>) S = trm_rep (subst s \<sigma>) S"
      from this have "validate_ground_eq ?I (Eq (subst t \<sigma>) (subst s \<sigma>))"
        unfolding same_values_def using validate_ground_eq.simps by (metis (mono_tags, lifting)) 
      from `trm_rep (subst t \<sigma>) S = trm_rep (subst s \<sigma>) S` 
        have "validate_ground_eq ?I (Eq (subst s \<sigma>) (subst t \<sigma>))"
        unfolding same_values_def using validate_ground_eq.simps by (metis (mono_tags, lifting)) 
      from `orient_lit_inst L1 t s polarity \<sigma>` and `polarity=pos` 
        have "L1 = (Pos (Eq t s)) \<or> L1 = (Pos (Eq s t))"
        unfolding orient_lit_inst_def by auto
      from this have "subst_lit L1 \<sigma> = (Pos (Eq (subst t \<sigma>)  (subst s \<sigma>))) \<or>
        subst_lit L1 \<sigma> = (Pos (Eq (subst s \<sigma>)  (subst t \<sigma>)))" by auto
      from this and `validate_ground_eq ?I (Eq (subst s \<sigma>) (subst t \<sigma>))`
        and `validate_ground_eq ?I (Eq (subst t \<sigma>) (subst s \<sigma>))` 
        have "validate_ground_lit ?I (subst_lit L1 \<sigma>)" using validate_ground_lit.simps(1) by metis
      from `L1 \<in> (cl_ecl C)` have "(subst_lit L1 \<sigma>) \<in> (subst_cl (cl_ecl C) \<sigma>)" by auto
      from this and `validate_ground_lit ?I (subst_lit L1 \<sigma>)` 
        have "validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)" 
        using validate_ground_clause.simps by metis
      from this and `\<not> validate_ground_clause (int_clset S) (subst_cl (cl_ecl C) \<sigma>)` 
        show False unfolding int_clset_def by blast
     qed
     have cv': "(candidate_values (trm_rep (subst s \<sigma>) S) C (cl_ecl C) (subst_cl (cl_ecl C) \<sigma>) 
                  (subst s \<sigma>) (subst_lit L1 \<sigma>) L1 \<sigma> t s v S)"
     proof -
        from `polarity=pos` and `orient_lit_inst L1 t s polarity \<sigma>` have "\<not>negative_literal L1" 
          unfolding  orient_lit_inst_def by auto 
        from this and `eligible_literal L1 C \<sigma>`  
          have "sel(cl_ecl C) = {}" and "maximal_literal (subst_lit L1 \<sigma>) (subst_cl (cl_ecl C) \<sigma>)" 
          using sel_neg unfolding eligible_literal_def by auto
        from  `v = subst u \<sigma>` and `u = t` have "v = subst t \<sigma>" by auto
        from assms(7) `C \<in> S` have "finite (cl_ecl C)" by auto
        have "v \<notin> subst_set (trms_ecl C) \<sigma>"
        proof
          assume "v \<in> subst_set (trms_ecl C) \<sigma>"
          from this and assms(12) `subterm (subst t \<sigma>) p v` `v = subst t \<sigma>` 
            have "trm_rep v S = v"  unfolding all_trms_irreducible_def occurs_in_def by blast 
          from this `v = subst t \<sigma>` `trm_rep (subst t \<sigma>) S \<noteq> (subst t \<sigma>)` 
            show False by blast
        qed
        
        from assms(13) have "smaller_lits_are_false v (subst_cl (cl_ecl C) \<sigma>) S" 
          using smaller_lits_are_false_if_cl_not_valid [of S "(subst_cl (cl_ecl C) \<sigma>)" ] by blast
        from assms(1) `\<not> proper_subterm_red t S \<sigma>` `polarity=pos` `v = subst t \<sigma>` have 
          "maximal_literal_is_unique v (subst s \<sigma>) (cl_ecl C) L1 S \<sigma>" 
          using maximal_literal_is_unique_lemma [of t s "(cl_ecl C)" S \<sigma> L1]  by blast
        from `all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. trm_rep t S)` 
          have "trms_irreducible C \<sigma> S v" using trms_irreducible_lemma [of C \<sigma> S v] by blast
        have "(subst s \<sigma>, subst t \<sigma>) \<in> trm_ord"
        proof -
          from `orient_lit_inst L1 t s polarity \<sigma>` have "(subst t \<sigma>, subst s \<sigma>) \<notin> trm_ord"
            unfolding orient_lit_inst_def by auto
          
          from `trm_rep (subst t \<sigma>) S \<noteq> trm_rep (subst s \<sigma>) S` 
            have "(subst t \<sigma>) \<noteq> (subst s \<sigma>)" by metis
          from this and `(subst t \<sigma>, subst s \<sigma>) \<notin> trm_ord` 
            `vars_of (subst t \<sigma>) = {}`
            `vars_of (subst s \<sigma>) = {}`
            show "(subst s \<sigma>, subst t \<sigma>) \<in> trm_ord"
            using trm_ord_ground_total unfolding ground_term_def by metis
        qed

        from `C \<in> S` `(subst s \<sigma>, subst t \<sigma>) \<in> trm_ord` 
          and `polarity=pos` `orient_lit_inst L1 t s polarity \<sigma>` and `sel (cl_ecl C) = {}` 
          and `L1 \<in> cl_ecl C` 
          and `maximal_literal (subst_lit L1 \<sigma>) (subst_cl (cl_ecl C) \<sigma>)`
          and `ground_clause (subst_cl (cl_ecl C) \<sigma>)` and `v = subst t \<sigma>` 
          and `finite (cl_ecl C)` 
          and `v \<notin> subst_set (trms_ecl C) \<sigma>`
          and `smaller_lits_are_false v (subst_cl (cl_ecl C) \<sigma>) S` 
          and `maximal_literal_is_unique v (subst s \<sigma>) (cl_ecl C) L1 S \<sigma>`
          and `trms_irreducible C \<sigma> S v`
          show cv': "(candidate_values (trm_rep (subst s \<sigma>) S) C (cl_ecl C) (subst_cl (cl_ecl C) \<sigma>) 
            (subst s \<sigma>) (subst_lit L1 \<sigma>) L1 \<sigma> t s v S)"
            unfolding candidate_values_def by blast
     qed
          
     from cv' have "(trm_rep (subst s \<sigma>) S,(subst s \<sigma>)) \<in> set_of_candidate_values S v" 
     unfolding set_of_candidate_values_def by blast 

     from this and min_pair and `pair = (zz,  gr_rhs)` 
      have "((subst s \<sigma>),gr_rhs) \<notin> trm_ord"
      by (metis snd_conv) 
     have "(subst s \<sigma>)  \<noteq> gr_rhs"
      using `trm_rep v S = trm_rep gr_rhs S` `u = t` `v = subst u \<sigma>`   
            `trm_rep (subst t \<sigma>) S \<noteq> trm_rep (subst s \<sigma>) S` by blast 
     have "vars_of gr_rhs = {}" 
      using `subst rhs \<eta> = subst rhs \<sigma>'` 
      `subst_lit L2 \<eta> = subst_lit L2 \<sigma>'` 
      `gr_L2 = subst_lit L2 \<eta>` `gr_rhs = subst rhs \<eta>` 
      `orient_lit (subst_lit L2 \<sigma>') (subst lhs \<sigma>') (subst rhs \<sigma>') pos` 
      `vars_of_lit gr_L2 = {}` orient_lit_vars by fastforce 
     from `(subst s \<sigma>)  \<noteq> gr_rhs` and `vars_of (subst s \<sigma>) = {}` `vars_of gr_rhs = {}` 
        `((subst s \<sigma>),gr_rhs) \<notin> trm_ord` 
      have "(gr_rhs,(subst s \<sigma>)) \<in> trm_ord" 
      using trm_ord_ground_total unfolding ground_term_def by blast

     have "(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<in> lit_ord"
      using `(gr_rhs, subst s \<sigma>) \<in> trm_ord` 
        `subst lhs \<eta> = subst lhs \<sigma>'` `subst rhs \<eta> = subst rhs \<sigma>'` 
        `subst_lit L1 \<sigma> = subst_lit L1 \<sigma>'` 
        `gr_rhs = subst rhs \<eta>` 
        `orient_lit (subst_lit L2 \<sigma>') (subst lhs \<sigma>') (subst rhs \<sigma>') pos` 
        `polarity = pos` `u = t` `v = subst lhs \<eta>` `v = subst u \<sigma>` 
        `vars_of_lit (subst_lit L1 \<sigma>') = {}` `vars_of_lit (subst_lit L2 \<sigma>') = {}` 
        assms(6) lit_ord_rhs lift_orient_lit by fastforce 
     from this and `(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<notin> lit_ord` show False by auto
   qed

   have "trm_rep (subst u \<sigma>) S \<noteq> (subst u \<sigma>)"
    using `trm_rep v S \<noteq> v` `v = subst u \<sigma>` by blast 
   have "allowed_redex u C \<sigma>"
   proof (rule ccontr) 
    assume "\<not>allowed_redex u C \<sigma>"
    from this obtain ss where "ss \<in> trms_ecl C" 
      and "occurs_in (subst u \<sigma>) (subst ss \<sigma>)" unfolding allowed_redex_def by auto
    from `ss \<in> trms_ecl C` have "(subst ss \<sigma>) \<in> (subst_set (trms_ecl C) \<sigma>)" by auto
    from this and assms(12) and `occurs_in (subst u \<sigma>) (subst ss \<sigma>)` 
      `trm_rep (subst u \<sigma>) S \<noteq> (subst u \<sigma>)`
      show False
      unfolding all_trms_irreducible_def by blast
   qed
   have "subst lhs \<sigma>' \<noteq> subst rhs \<sigma>'"
    using `(gr_rhs, v) \<in> trm_ord` 
    `subst lhs \<eta> = subst lhs \<sigma>'` 
    `subst rhs \<eta> = subst rhs \<sigma>'` 
    `gr_rhs = subst rhs \<eta>` `v = subst lhs \<eta>` trm_ord_wf by auto 
   from this `mp=p` `\<not> (is_a_variable u)`
   `all_trms_irreducible (subst_set (trms_ecl C2) \<sigma>') (\<lambda>t. trm_rep t S)`
   `(subst_lit L2 \<sigma>', subst_lit L1 \<sigma>') \<in> lit_ord` 
   `all_trms_irreducible (subst_set (trms_ecl C2) \<sigma>') (\<lambda>t. trm_rep t S)`  
   `(\<forall>x\<in>cl_ecl C2 - {L2}. (subst_lit x \<sigma>', subst_lit L2 \<sigma>') \<in> lit_ord)` 
   `C2 \<in> S` `eligible_literal L1 C \<sigma>'` `eligible_literal L2 C2 \<sigma>'` 
   `ground_clause (subst_cl Cl_C2 \<sigma>')` `Cl_C2 = cl_ecl C2` 
    mr `coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))` `L1 \<in> cl_ecl C` `L2 \<in> Cl_C2`  
    `orient_lit_inst L1 t s polarity \<sigma>'` `(orient_lit_inst L2 lhs rhs pos \<sigma>')`
    `(subterm t p u)` `subst u \<sigma>' = subst lhs \<sigma>'` 
    `trm_rep (subst rhs \<sigma>') S = trm_rep (subst lhs \<sigma>') S` 
    `(\<not> validate_ground_clause ?I (subst_cl ( Cl_C2 - { L2 } ) \<sigma>'))`
    `allowed_redex u C \<sigma>`
   have "(reduction L1 C \<sigma>' t s polarity L2 lhs u mp rhs C2 (same_values (\<lambda>t. (trm_rep t S))) S \<sigma>)"
    unfolding reduction_def same_values_def 
    by metis
   from `vars_of_cl (cl_ecl C) \<inter> vars_of_cl (cl_ecl C2) = {}` have "variable_disjoint C C2" 
      unfolding variable_disjoint_def by auto
   from this and 
    `(reduction L1 C \<sigma>' t s polarity L2 lhs u mp rhs C2 (same_values (\<lambda>t. (trm_rep t S))) S \<sigma>)`  
    show ?thesis by blast
qed

lemma subts_of_irred_trms_are_irred:
  assumes "trm_rep y S \<noteq> y"
  shows "\<And> x. subterm x p y \<longrightarrow> trm_rep x S \<noteq> x"
proof (induction p)
  case (Nil)
    from assms(1) show ?case by (metis subterm.simps(1))   
  next case (Cons i p) 
    show "\<And> x. subterm x (Cons i p) y \<longrightarrow> trm_rep x S \<noteq> x"
    proof
      fix x assume "subterm x (Cons i p) y"
      from this obtain x1 x2 where "x = Comb x1 x2" using subterm.elims(2) by blast
      have "i = Left | i = Right" using indices.exhaust by auto
      then show "trm_rep x S \<noteq> x"
      proof
        assume "i = Left"
        from this and `subterm x (Cons i p) y` `x = Comb x1 x2` have "subterm x1 p y" by auto
        from this and Cons.IH have "trm_rep x1 S \<noteq> x1" by blast
        from this and `x = Comb x1 x2` have "subterm_reduction_applicable S x"  
          unfolding subterm_reduction_applicable_def  
          by (metis is_compound.simps(3) lhs.simps(1))
        from this have "(trm_rep x S, x) \<in> trm_ord" using  trm_rep_is_lower_subt_red by blast
        from this show ?thesis using trm_ord_irrefl unfolding irrefl_def by metis
      next
        assume "i = Right"
        from this and `subterm x (Cons i p) y` `x = Comb x1 x2` have "subterm x2 p y" by auto
        from this and Cons.IH have "trm_rep x2 S \<noteq> x2" by blast
        from this and `x = Comb x1 x2` have "subterm_reduction_applicable S x"  
          unfolding subterm_reduction_applicable_def  
          by (metis is_compound.simps(3) rhs.simps(1))
        from this have "(trm_rep x S, x) \<in> trm_ord" using  trm_rep_is_lower_subt_red by blast
        from this show ?thesis using trm_ord_irrefl unfolding irrefl_def by metis
      qed
    qed
qed

lemma allowed_redex_coincide:
  assumes "allowed_redex t C \<sigma>"
  assumes "t \<in> subterms_of_cl (cl_ecl C)" 
  assumes "coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))"
  assumes "well_constrained C"
  shows "allowed_redex t C \<sigma>'"
proof (rule ccontr)
  assume "\<not>allowed_redex t C \<sigma>'"
  from this  obtain s 
    where "s \<in> trms_ecl C" and "occurs_in (subst t \<sigma>') (subst s \<sigma>')" 
    unfolding allowed_redex_def by auto
  from `s \<in> trms_ecl C` and assms(4) have "vars_of s \<subseteq> vars_of_cl (cl_ecl C)" 
    using dom_trm_vars unfolding well_constrained_def by blast
  from this have "vars_of s \<subseteq> vars_of_cl (cl_ecl C)" using subterm_vars by blast 
  from this and assms(3) have "coincide_on \<sigma> \<sigma>' (vars_of s)" unfolding coincide_on_def by auto
  from this have "(subst s \<sigma>) = (subst s \<sigma>')" using coincide_on_term by auto
  from assms(2) have "vars_of t \<subseteq> vars_of_cl (cl_ecl C)" using subterm_vars by blast 
  from this and assms(3) have "coincide_on \<sigma> \<sigma>' (vars_of t)" unfolding coincide_on_def by auto
  from this have "(subst t \<sigma>) = (subst t \<sigma>')" using coincide_on_term by auto
  from this and `(subst s \<sigma>) = (subst s \<sigma>')` and `occurs_in (subst t \<sigma>') (subst s \<sigma>')`
    have "occurs_in (subst t \<sigma>) (subst s \<sigma>)" by auto
  from this and `s \<in> trms_ecl C` have "\<not>allowed_redex t C \<sigma>" unfolding allowed_redex_def by auto
  from this and assms(1) show False by auto
qed

text {* The next lemma states that the irreducibility of an instance of a set of terms 
is preserved when the substitution is replaced by its equivalent normal form. *}

lemma irred_terms_and_reduced_subst:
  assumes "f = (\<lambda>t. (trm_rep t S))"
  assumes "\<eta> = (map_subst f \<sigma>)"
  assumes "all_trms_irreducible (subst_set E \<sigma>) f"
  assumes "I = int_clset S"
  assumes "equivalent_on  \<sigma> \<eta> (vars_of_cl (cl_ecl C)) I"
  assumes "lower_on \<eta> \<sigma>  (vars_of_cl (cl_ecl C))"
  assumes "E = (trms_ecl C)"
  assumes "\<forall>x \<in> S. \<forall>y. (y \<in> trms_ecl x \<longrightarrow> dom_trm y (cl_ecl x))"
  assumes "C \<in> S"
  assumes "fo_interpretation I"
  shows "all_trms_irreducible (subst_set E \<eta> ) f"
proof (rule ccontr)
  assume "\<not>all_trms_irreducible (subst_set E \<eta>) f"
  from this obtain t y where "y \<in> (subst_set E \<eta>)" "occurs_in t y" "f t \<noteq> t"
    unfolding all_trms_irreducible_def by metis
  from `occurs_in t y` obtain p where "subterm y p t" unfolding occurs_in_def by auto
  from this and `f t \<noteq> t` and assms(1) have "f y \<noteq> y" using subts_of_irred_trms_are_irred by blast
  from `y \<in> (subst_set E \<eta>)` obtain z where "z \<in> E" and "y = (subst z \<eta>)" 
    by auto
  from `z \<in> E` have "(subst z \<sigma>) \<in> (subst_set E \<sigma>)" by auto
  have "subterm (subst z \<sigma>) [] (subst z \<sigma>)" by auto
  then have "occurs_in (subst z \<sigma>) (subst z \<sigma>)" unfolding occurs_in_def 
    by blast
  from this and assms(3) and `(subst z \<sigma>) \<in> (subst_set E \<sigma>)` 
     have "f (subst z \<sigma>) = (subst z \<sigma>)"
     unfolding all_trms_irreducible_def by metis
  from this and `f y \<noteq> y` and `y = (subst z \<eta>)` 
    have "(subst z \<sigma>) \<noteq> (subst z \<eta>)" by metis
  from `z \<in> E` and assms(7) assms(8) assms(9) have "dom_trm z (cl_ecl C)" by metis
  from this have "vars_of z \<subseteq> vars_of_cl (cl_ecl C)" using dom_trm_vars by auto 
  from this assms(5) have "equivalent_on \<sigma> \<eta> (vars_of z) I" 
    unfolding equivalent_on_def by auto
  from `vars_of z \<subseteq> vars_of_cl (cl_ecl C)` assms(6) have "lower_on \<eta> \<sigma>  (vars_of z)" 
    unfolding lower_on_def by auto
  from `(subst z \<sigma>) \<noteq> (subst z \<eta>)` 
       `lower_on \<eta> \<sigma>  (vars_of z)` 
     have "( (subst z \<eta>),(subst z \<sigma>) ) \<in> trm_ord"
     using lower_on_term unfolding lower_or_eq_def  by metis
  from this have "( (subst z \<sigma>),(subst z \<eta>) ) \<notin> trm_ord"
    using trm_ord_trans trm_ord_irrefl irrefl_def trans_def by metis
  from assms(10) `equivalent_on \<sigma> \<eta> (vars_of z) I`  
    have "(I (subst z \<sigma>) (subst z \<eta>))" using equivalent_on_term 
      unfolding fo_interpretation_def by auto
  from this and assms(4) assms(1) `f (subst z \<sigma>) = (subst z \<sigma>)`
    have "(subst z \<sigma>) = f (subst z \<eta>)" unfolding same_values_def int_clset_def 
    by metis
  from this `( (subst z \<sigma>),(subst z \<eta>) ) \<notin> trm_ord` 
    `(subst z \<sigma>) \<noteq> (subst z \<eta>)` assms(1)
    show False using trm_rep_is_lower by metis
qed

lemma no_valid_literal:
  assumes "L \<in> C"
  assumes "orient_lit_inst L t s pos \<sigma>"
  assumes "\<not>(validate_ground_clause (int_clset S) (subst_cl C \<sigma>))"
  shows "trm_rep (subst t \<sigma>) S \<noteq> trm_rep (subst s \<sigma>) S"
proof 
      assume neg_hyp: "trm_rep (subst t \<sigma>) S = trm_rep (subst s \<sigma>) S"
      let ?I = "int_clset S"
      from neg_hyp have "validate_ground_eq ?I (Eq (subst t \<sigma>) (subst s \<sigma>))"
        unfolding same_values_def int_clset_def using validate_ground_eq.simps 
        by (metis (mono_tags, lifting)) 
      from `trm_rep (subst t \<sigma>) S = trm_rep (subst s \<sigma>) S` 
        have "validate_ground_eq ?I (Eq (subst s \<sigma>) (subst t \<sigma>))"
        unfolding same_values_def  int_clset_def  using validate_ground_eq.simps 
        by (metis (mono_tags, lifting)) 
      from `orient_lit_inst L t s pos \<sigma>` have "L = (Pos (Eq t s)) \<or> L = (Pos (Eq s t))"
        unfolding orient_lit_inst_def by auto
      from this have "subst_lit L \<sigma> = (Pos (Eq (subst t \<sigma>)  (subst s \<sigma>))) \<or>
            subst_lit L \<sigma> = (Pos (Eq (subst s \<sigma>)  (subst t \<sigma>)))" by auto
      from this and `validate_ground_eq ?I (Eq (subst s \<sigma>) (subst t \<sigma>))` 
        and `validate_ground_eq ?I (Eq (subst t \<sigma>) (subst s \<sigma>))` 
        have "validate_ground_lit ?I (subst_lit L \<sigma>)" using validate_ground_lit.simps(1) by metis
      from assms(1) have "(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)" by auto
      from `(subst_lit L \<sigma>) \<in> (subst_cl C \<sigma>)` 
          and `validate_ground_lit ?I (subst_lit L \<sigma>)` 
          have "validate_ground_clause ?I (subst_cl C \<sigma>)"
          using validate_ground_clause.elims(3) by blast 
      from this and `\<not> validate_ground_clause ?I (subst_cl C \<sigma>)` show False by blast
qed

subsection {* Lifting *}

text {* This section contains all the necessary lemmata for transforming ground inferences into 
first-order inferences. We show that all the necessary properties can be lifted. *}

lemma lift_orient_lit_inst:
  assumes "orient_lit_inst  L t s polarity \<theta>"
  assumes "subst_eq \<theta> (comp \<sigma> \<eta>)" 
  shows "orient_lit_inst L t s polarity \<sigma>"
proof -
  let ?\<theta> = "(comp \<sigma> \<eta>)"
  have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto  
  then show ?thesis
  proof
    assume "polarity = pos" 
    from this and assms(1) have "L = Pos (Eq t s) \<or> L = Pos (Eq s t)"
      and "( (subst t \<theta>),  (subst s \<theta>)) \<notin> trm_ord"  
      unfolding orient_lit_inst_def by auto
    from assms(2) have "(subst t \<theta>) = (subst (subst t \<sigma>) \<eta>)" 
      by auto
    from assms(2) have "(subst s \<theta>) = (subst (subst s \<sigma>) \<eta>)" 
      by auto
    from `(subst t \<theta>) = (subst (subst t \<sigma>) \<eta>)`
         `(subst s \<theta>) = (subst (subst s \<sigma>) \<eta>)`
         `( (subst t \<theta>),  (subst s \<theta>)) \<notin> trm_ord`
      have "( (subst (subst t \<sigma>) \<eta>),(subst (subst s \<sigma>) \<eta>)) \<notin> trm_ord"
      by auto
    from this have "( (subst t \<sigma>),  (subst s \<sigma>)) \<notin> trm_ord"
      using trm_ord_subst by auto
    from this and `polarity = pos` `L = Pos (Eq t s) \<or> L = Pos (Eq s t)` show ?thesis 
      unfolding orient_lit_inst_def by blast
  next
    assume "polarity = neg" 
    from this and assms(1) have "L = Neg (Eq t s) \<or> L = Neg (Eq s t)"
      and "( (subst t \<theta>),  (subst s \<theta>)) \<notin> trm_ord"  
      unfolding orient_lit_inst_def by auto
    from assms(2) have "(subst t \<theta>) = (subst (subst t \<sigma>) \<eta>)" 
      by auto
    from assms(2) have "(subst s \<theta>) = (subst (subst s \<sigma>) \<eta>)" 
      by auto
    from `(subst t \<theta>) = (subst (subst t \<sigma>) \<eta>)`
         `(subst s \<theta>) = (subst (subst s \<sigma>) \<eta>)`
         `( (subst t \<theta>),  (subst s \<theta>)) \<notin> trm_ord`
      have "( (subst (subst t \<sigma>) \<eta>),(subst (subst s \<sigma>) \<eta>)) \<notin> trm_ord"
      by auto
    from this have "( (subst t \<sigma>),  (subst s \<sigma>)) \<notin> trm_ord"
      using trm_ord_subst by auto
    from this and `polarity = neg` `L = Neg (Eq t s) \<or> L = Neg (Eq s t)` show ?thesis 
      unfolding orient_lit_inst_def by blast
  qed
qed

lemma lift_maximal_literal:
  assumes "maximal_literal (subst_lit L \<sigma>) (subst_cl C \<sigma>)"
  shows "maximal_literal L C"
proof (rule ccontr)
  assume "\<not>maximal_literal L C"
  then obtain M where "M \<in> C" and "(L,M) \<in> lit_ord" unfolding maximal_literal_def by auto
  from `M \<in> C` have "(subst_lit M \<sigma>) \<in> (subst_cl C \<sigma>)" by auto
  from `(L,M) \<in> lit_ord` have "((subst_lit L \<sigma>),(subst_lit M \<sigma>)) \<in> lit_ord"
    using lit_ord_subst by auto
  from this and `(subst_lit M \<sigma>) \<in> (subst_cl C \<sigma>)` and assms(1) 
    show False unfolding maximal_literal_def by auto
qed

lemma lift_eligible_literal:
  assumes "eligible_literal L C \<sigma>"
  assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
  shows "eligible_literal L C \<theta>"
proof -
  from assms(1) have "(L \<in> sel (cl_ecl C) \<or> 
    (sel(cl_ecl C) = {} 
    \<and> (maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>))))"
    unfolding eligible_literal_def by auto
  then show ?thesis
  proof
    assume "L \<in> sel (cl_ecl C)"
    then show ?thesis unfolding eligible_literal_def by auto
  next
    assume "sel(cl_ecl C) = {} 
     \<and> (maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>))"
    then have "sel (cl_ecl C) = {}" and "maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>)"
      by auto
    let ?\<sigma> = "\<theta> \<lozenge> \<eta>"
    from assms(2) have "(subst_lit L \<sigma>) = (subst_lit L ?\<sigma>)" 
      using subst_eq_lit by auto
    then have "(subst_lit L \<sigma>) = (subst_lit (subst_lit L \<theta>) \<eta>)"
      using composition_of_substs_lit [of L \<theta> \<eta>] by auto

    from assms(2) have "(subst_cl (cl_ecl C) \<sigma>) = (subst_cl (cl_ecl C) ?\<sigma>)" 
      using subst_eq_cl [of \<sigma> "?\<sigma>" "(cl_ecl C)"] by auto
    then have "(subst_cl (cl_ecl C) \<sigma>) = (subst_cl (subst_cl (cl_ecl C) \<theta>) \<eta>)"
      using composition_of_substs_cl [of "cl_ecl C" \<theta> \<eta>] by auto
    
    from `maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>)` 
      `(subst_lit L \<sigma>) = (subst_lit (subst_lit L \<theta>) \<eta>)` 
      `(subst_cl (cl_ecl C) \<sigma>) = (subst_cl (subst_cl (cl_ecl C) \<theta>) \<eta>)`
      have "maximal_literal (subst_lit (subst_lit L \<theta>) \<eta>) 
         (subst_cl (subst_cl (cl_ecl C) \<theta>) \<eta>)" by auto
    from this have "maximal_literal (subst_lit L \<theta>) (subst_cl (cl_ecl C) \<theta>)" 
      using lift_maximal_literal by metis
    from this and `sel (cl_ecl C) = {}` show ?thesis unfolding eligible_literal_def by auto
  qed
qed

lemma lift_allowed_redex:  
    assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
    assumes "(allowed_redex u C \<sigma>)"
    shows "(allowed_redex u C \<theta>)"
proof (rule ccontr)
  assume "\<not>(allowed_redex u C \<theta>)"
  from this obtain s where "s \<in> (trms_ecl C)" and "(occurs_in (subst u \<theta>) (subst s \<theta>))"
    unfolding allowed_redex_def by metis
  from `(occurs_in (subst u \<theta>) (subst s \<theta>))`
    have "(occurs_in (subst (subst u \<theta>) \<eta>) (subst (subst s \<theta>) \<eta>))"
    using substs_preserve_occurs_in by auto
  from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst u \<sigma>) = (subst (subst u \<theta>) \<eta>)" by auto
  from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst s \<sigma>) = (subst (subst s \<theta>) \<eta>)" by auto
  from `(occurs_in (subst (subst u \<theta>) \<eta>) (subst (subst s \<theta>) \<eta>))` 
    `(subst u \<sigma>) = (subst (subst u \<theta>) \<eta>)` 
    `(subst s \<sigma>) = (subst (subst s \<theta>) \<eta>)`
    have "(occurs_in (subst u \<sigma>) (subst s \<sigma>))" by auto
  from this and `s \<in> (trms_ecl C)` assms(2)  show False unfolding allowed_redex_def by auto
qed

lemma lift_decompose_literal:
  assumes "decompose_literal (subst_lit L \<sigma>) t s polarity"
  assumes "subst_eq \<theta> (comp \<sigma> \<eta>)" 
  shows "decompose_literal (subst_lit L \<theta>) (subst t \<eta>) (subst s \<eta>) polarity"
proof -
  let ?L = "(subst_lit L \<sigma>)"
  let ?t' = "(subst t \<eta>)"
  let ?s' = "(subst s \<eta>)"

  let ?\<theta> = "(comp \<sigma> \<eta>)"
  let ?L' = "(subst_lit ?L \<eta>)"

  from assms(2) have "(subst_lit L \<theta>) = (subst_lit L ?\<theta>)" using 
      subst_eq_lit by auto
  from this have "(subst_lit L \<theta>) = ?L'" 
      using composition_of_substs_lit by metis

  have "polarity = pos \<or> polarity = neg" using sign.exhaust by auto  
  then show ?thesis
  proof
    assume "polarity = pos" 
    from this and assms(1) have "?L = Pos (Eq t s) \<or> ?L = Pos (Eq s t)"
      unfolding decompose_literal_def decompose_equation_def by auto
    from `?L = Pos (Eq t s) \<or> ?L = Pos (Eq s t)`
      have "?L' = Pos (Eq ?t' ?s') \<or> ?L' = Pos (Eq ?s' ?t')" by auto
    from this  `(subst_lit L \<theta>) = ?L'`
      have "(subst_lit L \<theta>) = Pos (Eq ?t' ?s') \<or> (subst_lit L \<theta>) = Pos (Eq ?s' ?t')" by auto
    from this `polarity = pos` show ?thesis unfolding decompose_literal_def 
      decompose_equation_def by auto
  next
    assume "polarity = neg" 
    from this and assms(1) have "?L = Neg (Eq t s) \<or> ?L = Neg (Eq s t)"
      unfolding decompose_literal_def decompose_equation_def by auto
    from `?L = Neg (Eq t s) \<or> ?L = Neg (Eq s t)`
      have "?L' = Neg (Eq ?t' ?s') \<or> ?L' = Neg (Eq ?s' ?t')" by auto
    from this and `(subst_lit L \<theta>) = ?L'`
      have "(subst_lit L \<theta>) = Neg (Eq ?t' ?s') \<or> (subst_lit L \<theta>) = Neg (Eq ?s' ?t')" by auto
    from this `polarity = neg` show ?thesis unfolding decompose_literal_def 
      decompose_equation_def by auto
  qed
qed

lemma lift_dom_trm:
  assumes "dom_trm (subst t \<theta>) (subst_cl C \<theta>)"
  assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
  shows "dom_trm (subst t \<sigma>) (subst_cl C \<sigma>)"
proof -
  let ?t = "(subst t \<theta>)"
  let ?t' = "(subst ?t \<eta>)"
  let ?t'' = "(subst t \<sigma>)"
  have "?t' = (subst t (\<theta> \<lozenge> \<eta>))" by auto
  from assms(2) have "?t'' = (subst t (\<theta> \<lozenge> \<eta>))" by auto
  from this and `?t' = (subst t (\<theta> \<lozenge> \<eta>))` have "?t' = ?t''" by metis
  from assms(1) have "(\<exists> L u v p. (L \<in> (subst_cl C \<theta>) \<and> (decompose_literal L u v p) 
        \<and> (( (p = neg \<and> ?t = u) \<or> (?t,u) \<in> trm_ord))))" unfolding dom_trm_def by auto
  from this obtain L u v p where  "L \<in> (subst_cl C \<theta>)" 
    "decompose_literal L u v p" "(( (p = neg \<and> ?t = u) \<or> (?t,u) \<in> trm_ord))" 
    unfolding dom_trm_def by blast

  from `L \<in> (subst_cl C \<theta>)` obtain L' where "L' \<in> C" 
    "L = (subst_lit L' \<theta>)" by auto
  from this and `decompose_literal L u v p` have "decompose_literal (subst_lit L' \<theta>) u v p" by auto
  from this assms(2)  `L = (subst_lit L' \<theta>)` 
    have "decompose_literal (subst_lit L' \<sigma>) (subst u \<eta>) (subst v \<eta>) p"
    using lift_decompose_literal [of L' \<theta> u v p \<sigma> \<eta>] by auto
  let ?u = "(subst u \<eta>)"
  from `L' \<in> C` have "(subst_lit L' \<sigma>) \<in> (subst_cl C \<sigma>)" by auto
  from `(( (p = neg \<and> ?t = u) \<or> (?t,u) \<in> trm_ord))`
    have "(( (p = neg \<and> ?t' = ?u) \<or> (?t',?u) \<in> trm_ord))"
      using trm_ord_subst by auto
  from this and `?t' = ?t''`  have "(( (p = neg \<and> ?t'' = ?u) \<or> (?t'',?u) \<in> trm_ord))" by auto
  from this `(subst_lit L' \<sigma>) \<in> (subst_cl C \<sigma>)` 
    `decompose_literal (subst_lit L' \<sigma>) (subst u \<eta>) (subst v \<eta>) p` 
    show "dom_trm (subst t \<sigma>) (subst_cl C \<sigma>)" 
    unfolding dom_trm_def by auto
qed

lemma lift_irreducible_terms:
  assumes "T = get_trms C (dom_trms (subst_cl D \<sigma>) (subst_set E \<sigma>)) Ground"
  assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
  shows "\<exists>T'. ( (subst_set T' \<eta>) \<subseteq> T \<and> T' = get_trms C' 
    (dom_trms (subst_cl D \<theta>) (subst_set E \<theta>)) FirstOrder)"
proof -
  let ?E = "(dom_trms (subst_cl D \<theta>) (subst_set E \<theta>))"
  let ?E' = "(dom_trms (subst_cl D \<sigma>) (subst_set E \<sigma>))"
  let ?T' = "(filter_trms C' ?E)"
  have "?T' = get_trms C' ?E FirstOrder"
    unfolding get_trms_def by auto
  from assms(1) have "T = ?E'" unfolding get_trms_def by auto
  have "(subst_set ?T' \<eta>) \<subseteq> ?E'"
  proof
    fix x assume "x \<in> (subst_set ?T' \<eta>)"
    from this obtain x' where "x = (subst x' \<eta>)" and "x' \<in> ?T'" by auto
    from `x' \<in> ?T'` have "x' \<in> ?E" using filter_trms_inclusion by auto
    from `x' \<in> ?E` have "x' \<in> (subst_set E \<theta>)" 
      and "dom_trm x' (subst_cl D \<theta>)" unfolding dom_trms_def by auto 
    from `x' \<in> (subst_set E \<theta>)` obtain y where "y \<in> E"
      and "x' = (subst y \<theta>)" by auto
    from `x' = (subst y \<theta>)` and `dom_trm x' (subst_cl D \<theta>)`
      have "dom_trm (subst y \<theta>) (subst_cl D \<theta>)" by auto
    from this assms(2)  
      have "dom_trm (subst y \<sigma>) (subst_cl D \<sigma>)" 
      using lift_dom_trm by auto
    from `y \<in> E` have "(subst y \<sigma>) \<in> (subst_set E \<sigma>)" by auto
    from this and `dom_trm (subst y \<sigma>) (subst_cl D \<sigma>)`
      have "(subst y \<sigma>) \<in> ?E'" unfolding dom_trms_def by auto
    from assms(2) have "(subst y \<sigma>) = (subst y (\<theta> \<lozenge> \<eta>))" by auto
    from this `x = (subst x' \<eta>)` and `x' = (subst y \<theta>)` 
      have "x = (subst y \<sigma>)" by auto
    from this and `(subst y \<sigma>) \<in> ?E'` show "x \<in> ?E'" by auto
  qed
  from this and `T = ?E'` `?T' = get_trms C' ?E FirstOrder` show ?thesis by auto
qed

text {* We eventually deduce the following lemma, which allows one to transform ground derivations
into first-order derivations. *}
 
lemma lifting_lemma:
  assumes "derivable C P S \<sigma> Ground C'"
  shows "\<exists> D \<theta> \<eta>. ((derivable D P S \<theta> FirstOrder C') \<and> (\<sigma> \<doteq> \<theta> \<lozenge> \<eta>) \<and> (trms_subsumes D C \<eta>))"
proof (rule ccontr)
  assume hyp: "\<not> (\<exists> D \<theta> \<eta>. ((derivable D P S \<theta> FirstOrder C') \<and> (\<sigma> \<doteq> \<theta> \<lozenge> \<eta>) 
                \<and> (trms_subsumes D C \<eta>)))" 
  from assms(1) have "P \<subseteq> S" unfolding derivable_def by auto
  have not_sup: "\<not> (\<exists>P1 P2. (P = { P1, P2 } \<and> superposition P1 P2 C \<sigma> Ground C'))"
  proof
    assume "(\<exists>P1 P2. (P = { P1, P2 } \<and> superposition P1 P2 C \<sigma> Ground C'))"
    then obtain P1 P2 where "P = { P1, P2 }" "superposition P1 P2 C \<sigma> Ground C'" by auto
    from this obtain L t s u v M p Cl_P1 Cl_P2 Cl_C polarity t' u' L' trms_C
      where "L \<in> Cl_P1" "(M \<in> Cl_P2)" "(eligible_literal L P1 \<sigma>)" "(eligible_literal M P2 \<sigma>)"
      "(variable_disjoint P1 P2)"
      "(Cl_P1 = (cl_ecl P1))" "(Cl_P2 = (cl_ecl P2))" 
      "(\<not> is_a_variable u')"
      "(allowed_redex u' P1 \<sigma>)"
      "(C = (Ecl Cl_C trms_C))" 
      "(orient_lit_inst M u v pos \<sigma>)" 
      "(orient_lit_inst L t s polarity \<sigma>)" 
      "((subst u \<sigma>) \<noteq> (subst v \<sigma>))"
      "(subterm t p u')"
      "(ck_unifier u' u \<sigma> Ground)"
      "(replace_subterm t p v t')" 
      "(L' = mk_lit polarity (Eq t' s))"
      "(trms_C = get_trms Cl_C (dom_trms Cl_C (subst_set 
        ((trms_ecl P1) \<union> (trms_ecl P2) \<union> 
          { r. \<exists> q. (q,p) \<in> (pos_ord P1 t) \<and> (subterm t q r) }) \<sigma>)) Ground)" 
      "(Cl_C = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<sigma>))"
      "(C' = (Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } ))" 
      unfolding superposition_def get_trms_def by auto
    from `(ck_unifier u' u \<sigma> Ground)` have " Unifier \<sigma> u' u"
      unfolding ck_unifier_def by auto
    from this have "(subst u' \<sigma>) = (subst u \<sigma>)" unfolding Unifier_def by auto
    from this have "unify u' u \<noteq> None" using MGU_exists by auto
    from this obtain \<theta> where "unify u' u = Some \<theta>" by auto
    from this have "MGU \<theta> u' u" using unify_computes_MGU by auto
    from this and `Unifier \<sigma> u' u` obtain \<eta> where "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>" 
      unfolding MGU_def by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` and `(eligible_literal L P1 \<sigma>)` have "eligible_literal L P1 \<theta>" 
      using lift_eligible_literal by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` and `(eligible_literal M P2 \<sigma>)` have "eligible_literal M P2 \<theta>" 
      using lift_eligible_literal by auto
    from `MGU \<theta> u' u` have "ck_unifier u' u \<theta> FirstOrder" unfolding ck_unifier_def  by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst u \<sigma>) = (subst (subst u \<theta>) \<eta>)" by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst v \<sigma>) = (subst (subst v \<theta>) \<eta>)" by auto
    from `((subst u \<sigma>) \<noteq> (subst v \<sigma>))` 
      `(subst u \<sigma>) = (subst (subst u \<theta>) \<eta>)` 
      `(subst v \<sigma>) = (subst (subst v \<theta>) \<eta>)`
      have "(subst (subst u \<theta>) \<eta>) \<noteq> (subst (subst v \<theta>) \<eta>)" by auto
    from this have "(subst u \<theta>) \<noteq> (subst v \<theta>)" by auto
    
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `(allowed_redex u' P1 \<sigma>)` have "(allowed_redex u' P1 \<theta>)" 
      using lift_allowed_redex [of \<sigma> \<theta> \<eta> ] by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `orient_lit_inst M u v pos \<sigma>` have "orient_lit_inst M u v pos \<theta>"
      using lift_orient_lit_inst by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `orient_lit_inst L t s polarity \<sigma>` have "orient_lit_inst L t s polarity \<theta>"
      using lift_orient_lit_inst by auto

    from `(Cl_C = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<sigma>))` 
      and `C' = (Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )` 
      have "(Cl_C = (subst_cl C' \<sigma>))" by auto

    obtain E where "E = ((trms_ecl P1) \<union> (trms_ecl P2) \<union> 
          { r. \<exists> q. (q,p) \<in> (pos_ord P1 t) \<and> (subterm t q r) })" by auto
    from this and `(Cl_C = (subst_cl C' \<sigma>))` 
      `trms_C = (get_trms  Cl_C (dom_trms Cl_C (subst_set 
        ((trms_ecl P1) \<union> (trms_ecl P2) \<union> 
          { r. \<exists> q. (q,p) \<in> (pos_ord P1 t) \<and> (subterm t q r) }) \<sigma>)) Ground)`
        have "trms_C = (get_trms Cl_C 
        (dom_trms (subst_cl C' \<sigma>) (subst_set 
        E  \<sigma>)) Ground)" 
       by auto
  
    let ?Cl_C' = "(subst_cl C' \<theta>)"
    from  `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `trms_C = (get_trms Cl_C 
        (dom_trms (subst_cl C' \<sigma>) (subst_set 
        E  \<sigma>)) Ground)` 
        obtain "\<exists>T'. ( (subst_set T' \<eta>) \<subseteq> trms_C \<and> T' = get_trms ?Cl_C' 
    (dom_trms (subst_cl C' \<theta>) (subst_set E \<theta>)) FirstOrder)"
    using lift_irreducible_terms by auto
    from this obtain T' where "(subst_set T' \<eta>) \<subseteq> trms_C" 
      and "T' = get_trms ?Cl_C' 
    (dom_trms (subst_cl C' \<theta>) (subst_set E \<theta>)) FirstOrder" by auto

    obtain C_fo where "C_fo = (Ecl ?Cl_C' T')" by auto
    from `C' = (Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )` 
      have "(?Cl_C' = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<theta>))" 
      by auto
    from `L \<in> Cl_P1` `(M \<in> Cl_P2)` `(eligible_literal L P1 \<theta>)` `(eligible_literal M P2 \<theta>)`
      `(variable_disjoint P1 P2)`
      `(Cl_P1 = (cl_ecl P1))` `(Cl_P2 = (cl_ecl P2))` 
      `(\<not> is_a_variable u')`
      `(allowed_redex u' P1 \<theta>)`
      `(C_fo = (Ecl ?Cl_C' T'))` 
      `(orient_lit_inst M u v pos \<theta>)` 
      `(orient_lit_inst L t s polarity \<theta>)` 
      `((subst u \<theta>) \<noteq> (subst v \<theta>))`
      `(subterm t p u')`
      `(ck_unifier u' u \<theta> FirstOrder)`
      `(replace_subterm t p v t')` 
      `(L' = mk_lit polarity (Eq t' s))`
      `T' = (get_trms ?Cl_C' (dom_trms (subst_cl C' \<theta>) (subst_set E \<theta>)) FirstOrder)`
      `(?Cl_C' = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<theta>))`
      `(C' = (Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } ))` 
      `E = ((trms_ecl P1) \<union> (trms_ecl P2) \<union> 
          { r. \<exists> q. (q,p) \<in> (pos_ord P1 t) \<and> (subterm t q r) })`
      have "superposition P1 P2 C_fo \<theta> FirstOrder C'" unfolding superposition_def by blast
    from this `P = { P1, P2 }`  `P \<subseteq> S` have "(derivable C_fo P S \<theta> FirstOrder C')" 
      unfolding derivable_def by auto
    
    from `(?Cl_C' = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<theta>))` 
      have 
      i: "(subst_cl ?Cl_C' \<eta>) = 
      (subst_cl (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<theta>)) \<eta>"
        by auto
    have ii: "(subst_cl (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<theta>) \<eta>)
      =  (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) (\<theta> \<lozenge> \<eta>))"
      using composition_of_substs_cl [of "((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } ))" ] by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<sigma>) 
      = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) (\<theta> \<lozenge> \<eta>))" 
      using subst_eq_cl [of \<sigma> "\<theta> \<lozenge> \<eta>" "((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } ))" ] by auto
    from this and i ii  `Cl_C = (subst_cl ((Cl_P1 - { L }) \<union> ((Cl_P2 - { M }) \<union> { L' } )) \<sigma>)` 
      have "(subst_cl ?Cl_C' \<eta>) = Cl_C" by metis
    from this and `(C = (Ecl Cl_C trms_C))` and `(C_fo = (Ecl ?Cl_C' T'))` 
      have "(subst_cl (cl_ecl C_fo) \<eta>) = (cl_ecl C)" by auto
    from `(subst_set T' \<eta>) \<subseteq> trms_C` 
      and `(C = (Ecl Cl_C trms_C))` and `(C_fo = (Ecl ?Cl_C' T'))`
      have "(subst_set (trms_ecl C_fo) \<eta>) \<subseteq> (trms_ecl C)" by auto
    from `(subst_cl (cl_ecl C_fo) \<eta>) = (cl_ecl C)` `(subst_set (trms_ecl C_fo) \<eta>) \<subseteq> (trms_ecl C)`
      have "(trms_subsumes C_fo C \<eta>)"
      unfolding trms_subsumes_def by auto
    from this and `(derivable C_fo P S \<theta> FirstOrder C')` and `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` and hyp show False by auto
 qed

  have not_fact: "\<not> (\<exists>P1. ({ P1 } =  P \<and> factorization P1 C \<sigma> Ground C'))"
  proof
    assume "(\<exists>P1. ({ P1 } = P \<and> factorization P1 C \<sigma> Ground C'))"
    then obtain P1 where "P = { P1 }" "factorization P1 C \<sigma> Ground C'" by auto
    from this obtain L1 L2 L' t s u v Cl_P Cl_C trms_C where
      "eligible_literal L1 P1 \<sigma>"
      "L1 \<in> (cl_ecl P1)" "L2 \<in> (cl_ecl P1) - { L1 }" "Cl_C = (cl_ecl C)" "(Cl_P = (cl_ecl P1))" 
      "(orient_lit_inst L1 t s pos \<sigma>)"
      "(orient_lit_inst L2 u v pos \<sigma>)"
      "((subst t \<sigma>) \<noteq> (subst s \<sigma>))"
      "(subst t \<sigma>) \<noteq> (subst v \<sigma>)"
      "(ck_unifier t u \<sigma> Ground)"
      "(L' = Neg (Eq s v))"
      "C = (Ecl Cl_C trms_C)"
      "trms_C  = (get_trms Cl_C 
          (dom_trms Cl_C (subst_set ( (trms_ecl P1) \<union> (proper_subterms_of t) ) \<sigma>))) Ground"
      "(Cl_C = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } )) \<sigma>)"
      "(C' = ( (Cl_P - { L2 }) \<union> { L' } ))"
      unfolding factorization_def get_trms_def by auto
    from `(ck_unifier t u \<sigma> Ground)` have " Unifier \<sigma> t u"
      unfolding ck_unifier_def Unifier_def by auto
    from this have "(subst t \<sigma>) = (subst u \<sigma>)" unfolding Unifier_def by auto
    from this have "unify t u \<noteq> None" using MGU_exists by auto
    from this obtain \<theta> where "unify t u = Some \<theta>" by auto
    from this have "MGU \<theta> t u" using unify_computes_MGU by auto
    from this and `Unifier \<sigma> t u` obtain \<eta> where "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>" 
      unfolding MGU_def by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` and `(eligible_literal L1 P1 \<sigma>)` have "eligible_literal L1 P1 \<theta>" 
      using lift_eligible_literal by auto
    from `MGU \<theta> t u` have "ck_unifier t u \<theta> FirstOrder" unfolding ck_unifier_def  by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst t \<sigma>) = (subst (subst t \<theta>) \<eta>)" by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst s \<sigma>) = (subst (subst s \<theta>) \<eta>)" by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst v \<sigma>) = (subst (subst v \<theta>) \<eta>)" by auto

    from `((subst t \<sigma>) \<noteq> (subst s \<sigma>))` 
      `(subst t \<sigma>) = (subst (subst t \<theta>) \<eta>)` 
      `(subst s \<sigma>) = (subst (subst s \<theta>) \<eta>)`
      have "(subst (subst t \<theta>) \<eta>) \<noteq> (subst (subst s \<theta>) \<eta>)" by auto
    from this have "(subst t \<theta>) \<noteq> (subst s \<theta>)" by auto

    from `((subst t \<sigma>) \<noteq> (subst v \<sigma>))` 
      `(subst t \<sigma>) = (subst (subst t \<theta>) \<eta>)` 
      `(subst v \<sigma>) = (subst (subst v \<theta>) \<eta>)`
      have "(subst (subst t \<theta>) \<eta>) \<noteq> (subst (subst v \<theta>) \<eta>)" by auto
    from this have "(subst t \<theta>) \<noteq> (subst v \<theta>)" by auto
    
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `orient_lit_inst L1 t s pos \<sigma>` have "orient_lit_inst L1 t s pos \<theta>"
      using lift_orient_lit_inst by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `orient_lit_inst L2 u v pos \<sigma>` have "orient_lit_inst L2 u v pos \<theta>"
      using lift_orient_lit_inst by auto

    from `(Cl_C = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } )) \<sigma>)` 
      and `C' = ( (Cl_P - { L2 }) \<union> { L' } )` 
      have "(Cl_C = (subst_cl C' \<sigma>))" by auto

    obtain E where "E = (trms_ecl P1)" by auto
    from this and `(Cl_C = (subst_cl C' \<sigma>))` 
      `trms_C = (get_trms  Cl_C 
          (dom_trms Cl_C (subst_set ( (trms_ecl P1) \<union> (proper_subterms_of t) ) \<sigma>))) Ground`
        have "trms_C = (get_trms Cl_C 
        (dom_trms (subst_cl C' \<sigma>) (subst_set 
        (E \<union> (proper_subterms_of t))  \<sigma>)) Ground)" 
       by auto
  
    let ?Cl_C' = "(subst_cl C' \<theta>)"
    from  `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `trms_C = (get_trms Cl_C 
        (dom_trms (subst_cl C' \<sigma>) (subst_set 
        (E \<union> (proper_subterms_of t))  \<sigma>)) Ground)` 
        have "\<exists>T'. ( (subst_set T' \<eta>) \<subseteq> trms_C \<and> T' = get_trms ?Cl_C' 
    (dom_trms (subst_cl C' \<theta>) (subst_set (E \<union> (proper_subterms_of t)) \<theta>)) FirstOrder)"
    using lift_irreducible_terms by blast
    from this obtain T' where "(subst_set T' \<eta>) \<subseteq> trms_C" 
      and "T' = get_trms ?Cl_C' 
    (dom_trms (subst_cl C' \<theta>) (subst_set (E \<union> (proper_subterms_of t)) \<theta>)) FirstOrder" by auto

    obtain C_fo where "C_fo = (Ecl ?Cl_C' T')" by auto
    from `C' = ( (Cl_P - { L2 }) \<union> { L' } )` 
      have "(?Cl_C' = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) \<theta>))" 
      by auto
    from `C_fo = (Ecl ?Cl_C' T')` have "?Cl_C' = (cl_ecl C_fo)" by auto
    have "?Cl_C' = (subst_cl C' \<theta>)" by auto
    from 
      `eligible_literal L1 P1 \<theta>`
      `L1 \<in> (cl_ecl P1)` `L2 \<in> (cl_ecl P1) - { L1 }` `?Cl_C' = (cl_ecl C_fo)` `(Cl_P = (cl_ecl P1))` 
      `(orient_lit_inst L1 t s pos \<theta>)`
      `(orient_lit_inst L2 u v pos \<theta>)`
      `((subst t \<theta>) \<noteq> (subst s \<theta>))`
      `(subst t \<theta>) \<noteq> (subst v \<theta>)`
      `(ck_unifier t u \<theta> FirstOrder)`
      `(L' = Neg (Eq s v))`
      `C_fo = (Ecl ?Cl_C' T')`
      `T' = get_trms?Cl_C' 
        (dom_trms ?Cl_C' (subst_set (E \<union> (proper_subterms_of t)) \<theta>)) FirstOrder`
      `(?Cl_C' = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) \<theta>))`
      `C' = ( (Cl_P - { L2 }) \<union> { L' } )`
      `E = (trms_ecl P1)`
      have "factorization P1 C_fo \<theta> FirstOrder C'" unfolding factorization_def by blast

    from this `P = { P1 }`  `P \<subseteq> S` have "(derivable C_fo P S \<theta> FirstOrder C')" 
      unfolding derivable_def by auto
    
    from `(?Cl_C' = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) \<theta>))` 
      have 
      i: "(subst_cl ?Cl_C' \<eta>) = 
      (subst_cl (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) \<theta>)) \<eta>"
        by auto
    have ii: "(subst_cl (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) \<theta>) \<eta>)
      =  (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) (\<theta> \<lozenge> \<eta>))"
      using composition_of_substs_cl [of "( (Cl_P - { L2 }) \<union> { L' } )" ] by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) \<sigma>) 
      = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) (\<theta> \<lozenge> \<eta>))" 
      using subst_eq_cl [of \<sigma> "\<theta> \<lozenge> \<eta>" "( (Cl_P - { L2 }) \<union> { L' } )" ] by auto
    from this and i ii  `Cl_C = (subst_cl ( (Cl_P - { L2 }) \<union> { L' } ) \<sigma>)` 
      have "(subst_cl ?Cl_C' \<eta>) = Cl_C" by metis
    from this and `(C = (Ecl Cl_C trms_C))` and `(C_fo = (Ecl ?Cl_C' T'))` 
      have "(subst_cl (cl_ecl C_fo) \<eta>) = (cl_ecl C)" by auto
    from `(subst_set T' \<eta>) \<subseteq> trms_C` 
      and `(C = (Ecl Cl_C trms_C))` and `(C_fo = (Ecl ?Cl_C' T'))`
      have "(subst_set (trms_ecl C_fo) \<eta>) \<subseteq> (trms_ecl C)" by auto
    from `(subst_cl (cl_ecl C_fo) \<eta>) = (cl_ecl C)` `(subst_set (trms_ecl C_fo) \<eta>) \<subseteq> (trms_ecl C)`
      have "(trms_subsumes C_fo C \<eta>)"
      unfolding trms_subsumes_def by auto
    from this and `(derivable C_fo P S \<theta> FirstOrder C')` and `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` and hyp show False by auto
 qed

  have not_ref: "\<not> (\<exists>P1. ({ P1 } = P \<and> reflexion P1 C \<sigma> Ground C'))"
  proof
    assume "(\<exists>P1. ({ P1 } = P  \<and> reflexion P1 C \<sigma> Ground C'))"
    then obtain P1 where "{ P1 } = P" "reflexion P1 C \<sigma> Ground C'" by auto
    from this obtain L1 t s Cl_P Cl_C trms_C
  where "(eligible_literal L1 P1 \<sigma>)"
      "(L1 \<in> (cl_ecl P1))"  "(Cl_C = (cl_ecl C))" "(Cl_P = (cl_ecl P1))" 
      "(orient_lit_inst L1 t s neg \<sigma>)"
      "(ck_unifier t s \<sigma> Ground)"
      "(C = (Ecl Cl_C trms_C))"
      "(trms_C = get_trms Cl_C
          (dom_trms Cl_C (subst_set ( (trms_ecl P1) \<union> { t } ) \<sigma>)) Ground)" 
     "(Cl_C = (subst_cl ((Cl_P - { L1 }) )) \<sigma>)"
     "(C' = ((Cl_P - { L1 }) ))"
      unfolding reflexion_def get_trms_def by auto

    from `(ck_unifier t s \<sigma> Ground)` have " Unifier \<sigma> t s" 
      unfolding ck_unifier_def Unifier_def by auto
    from this have "(subst t \<sigma>) = (subst s \<sigma>)" unfolding Unifier_def by auto
    from this have "unify t s \<noteq> None" using MGU_exists by auto
    from this obtain \<theta> where "unify t s = Some \<theta>" by auto
    from this have "MGU \<theta> t s" using unify_computes_MGU by auto
    from this and `Unifier \<sigma> t s` obtain \<eta> where "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>" 
      unfolding MGU_def by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` and `(eligible_literal L1 P1 \<sigma>)` have "eligible_literal L1 P1 \<theta>" 
      using lift_eligible_literal by auto
    from `MGU \<theta> t s` have "ck_unifier t s \<theta> FirstOrder" unfolding ck_unifier_def  by auto

    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `orient_lit_inst L1 t s neg \<sigma>` have "orient_lit_inst L1 t s neg \<theta>"
      using lift_orient_lit_inst by auto

    from `(Cl_C = (subst_cl ((Cl_P - { L1 }) )) \<sigma>)` 
      and `C' = ((Cl_P - { L1 }) )` 
      have "(Cl_C = (subst_cl C' \<sigma>))" by auto

    obtain E where "E = (trms_ecl P1)" by auto
    from this and `(Cl_C = (subst_cl C' \<sigma>))` 
      `trms_C = (get_trms Cl_C 
          (dom_trms Cl_C (subst_set ( (trms_ecl P1)  \<union> { t } ) \<sigma>))) Ground`
        have "trms_C = (get_trms Cl_C 
        (dom_trms (subst_cl C' \<sigma>) (subst_set 
        (E  \<union> { t })  \<sigma>)) Ground)" 
       by auto
  
    let ?Cl_C' = "(subst_cl C' \<theta>)"
    from  `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `trms_C = (get_trms  Cl_C 
        (dom_trms (subst_cl C' \<sigma>) (subst_set 
        (E  \<union> { t })  \<sigma>)) Ground)` 
        have "\<exists>T'. ( (subst_set T' \<eta>) \<subseteq> trms_C \<and> T' = get_trms ?Cl_C' 
    (dom_trms (subst_cl C' \<theta>) (subst_set (E  \<union> { t }) \<theta>)) FirstOrder)"
    using lift_irreducible_terms by blast
    from this obtain T' where "(subst_set T' \<eta>) \<subseteq> trms_C" 
      and "T' = get_trms ?Cl_C' 
    (dom_trms (subst_cl C' \<theta>) (subst_set (E  \<union> { t }) \<theta>)) FirstOrder" by auto

    obtain C_fo where "C_fo = (Ecl ?Cl_C' T')" by auto
    from `C' = ((Cl_P - { L1 }) )` 
      have "(?Cl_C' = (subst_cl ((Cl_P - { L1 }) ) \<theta>))" 
      by auto
    from `C_fo = (Ecl ?Cl_C' T')` have "?Cl_C' = (cl_ecl C_fo)" by auto
    have "?Cl_C' = (subst_cl C' \<theta>)" by auto
    from 
      `(eligible_literal L1 P1 \<theta>)`
      `(L1 \<in> (cl_ecl P1))` `?Cl_C' = (cl_ecl C_fo)` `(Cl_P = (cl_ecl P1))` 
      `(orient_lit_inst L1 t s neg \<theta>)`
      `(ck_unifier t s \<theta> FirstOrder)`
      `(C_fo = (Ecl ?Cl_C' T'))`
      `(T' = get_trms  ?Cl_C'
          (dom_trms (subst_cl C' \<theta>) (subst_set (E \<union> { t }) \<theta>)) FirstOrder)` 
     `(?Cl_C' = (subst_cl ((Cl_P - { L1 }) )) \<theta>)`
     `(C' = ((Cl_P - { L1 }) ))`
     `E = (trms_ecl P1)`
      have "reflexion P1 C_fo \<theta> FirstOrder C'" unfolding reflexion_def by metis

    from this `{ P1 } = P`  `P \<subseteq> S` have "(derivable C_fo P S \<theta> FirstOrder C')" 
      unfolding derivable_def by auto
    
    from `(?Cl_C' = (subst_cl ((Cl_P - { L1 }) )) \<theta>)` 
      have 
      i: "(subst_cl ?Cl_C' \<eta>) = 
      (subst_cl (subst_cl ((Cl_P - { L1 }) ) \<theta>)) \<eta>"
        by auto
    have ii: "(subst_cl (subst_cl ((Cl_P - { L1 }) ) \<theta>) \<eta>)
      =  (subst_cl ((Cl_P - { L1 }) ) (\<theta> \<lozenge> \<eta>))"
      using composition_of_substs_cl [of "((Cl_P - { L1 }) )" ] by auto
    from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "(subst_cl((Cl_P - { L1 }) ) \<sigma>) 
      = (subst_cl ((Cl_P - { L1 }) ) (\<theta> \<lozenge> \<eta>))" 
      using subst_eq_cl [of \<sigma> "\<theta> \<lozenge> \<eta>" "((Cl_P - { L1 }) )" ] by auto
    from this and i ii  `Cl_C = (subst_cl ((Cl_P - { L1 }) ) \<sigma>)` 
      have "(subst_cl ?Cl_C' \<eta>) = Cl_C" by metis
    from this and `(C = (Ecl Cl_C trms_C))` and `(C_fo = (Ecl ?Cl_C' T'))` 
      have "(subst_cl (cl_ecl C_fo) \<eta>) = (cl_ecl C)" by auto
    from `(subst_set T' \<eta>) \<subseteq> trms_C` 
      and `(C = (Ecl Cl_C trms_C))` and `(C_fo = (Ecl ?Cl_C' T'))`
      have "(subst_set (trms_ecl C_fo) \<eta>) \<subseteq> (trms_ecl C)" by auto
    from `(subst_cl (cl_ecl C_fo) \<eta>) = (cl_ecl C)` 
        `(subst_set (trms_ecl C_fo) \<eta>) \<subseteq> (trms_ecl C)`
      have "(trms_subsumes C_fo C \<eta>)" unfolding trms_subsumes_def by auto
    from this and `(derivable C_fo P S \<theta> FirstOrder C')` and `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` and hyp show False by auto
 qed

   from not_sup not_ref not_fact and assms(1) show False unfolding derivable_def by blast
qed

lemma trms_subsumes_and_red_inf:
  assumes "trms_subsumes D C \<eta>"
  assumes "redundant_inference (subst_ecl D \<eta>) S P \<sigma>"
  assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
  shows "redundant_inference C S P \<sigma>"
proof -
  from assms(2) obtain S' where "S' \<subseteq> (instances S)" 
    "(set_entails_clause (clset_instances S') (cl_ecl (subst_ecl D \<eta>)))"
    "(\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl (subst_ecl D \<eta>))))"
    "(\<forall>x \<in> S'. \<exists>D' \<in> P. (((fst x),(snd x)),(D',\<sigma>)) \<in> ecl_ord)"
     unfolding redundant_inference_def by auto
  from assms(1) have "(subst_cl (cl_ecl D) \<eta>) = (cl_ecl C)" 
    unfolding trms_subsumes_def by auto
  obtain Cl_D T where "D = Ecl Cl_D T" using eclause.exhaust by auto
  from this have "(cl_ecl D) = Cl_D" and "trms_ecl D = T" by auto
  from `D = Ecl Cl_D T` have "subst_ecl D \<eta> = Ecl (subst_cl Cl_D \<eta>) (subst_set T \<eta>)"
    by auto
  from this have "(cl_ecl (subst_ecl D \<eta>)) = (subst_cl Cl_D \<eta>)" 
    and "trms_ecl (subst_ecl D \<eta>) = (subst_set T \<eta>)" by auto
  from `(cl_ecl (subst_ecl D \<eta>)) = (subst_cl Cl_D \<eta>)`
    and `(cl_ecl D) = Cl_D` `(subst_cl (cl_ecl D) \<eta>) = (cl_ecl C)` 
    have "(cl_ecl (subst_ecl D \<eta>)) = (cl_ecl C)" by auto
  from this and `(set_entails_clause (clset_instances S') (cl_ecl (subst_ecl D \<eta>)))`
    have "(set_entails_clause (clset_instances S') (cl_ecl C))" by auto
  
  from `trms_ecl D = T` and `trms_ecl (subst_ecl D \<eta>) = (subst_set T \<eta>)` 
    have "trms_ecl (subst_ecl D \<eta>) = (subst_set (trms_ecl D) \<eta>)" by auto

  from assms(1) have "(subst_set (trms_ecl D) \<eta>) \<subseteq> (trms_ecl C)" 
    unfolding trms_subsumes_def by auto
  have ii: "(\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl C)))"
  proof (rule ccontr)
    assume "\<not> (\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl C)))"
    from this obtain x where "x \<in> S'" and 
      "\<not>( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl C))" 
      by auto
    from `x \<in> S'` and `(\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl (subst_ecl D \<eta>))))` 
        have "( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl (subst_ecl D \<eta>)))" by auto

    obtain E1 where "E1 = (subst_set (trms_ecl (fst x)) (snd x))" by auto
    obtain E2 where "E2 = (subst_set (trms_ecl D) \<eta>)" by auto
    obtain E2' where "E2' = (trms_ecl C)" by auto
    from `E2 = (subst_set (trms_ecl D) \<eta>)` `E2' = (trms_ecl C)` 
          `(subst_set (trms_ecl D) \<eta>) \<subseteq> (trms_ecl C)` 
      have "E2 \<subseteq> E2'" by auto
    from `E1 = (subst_set (trms_ecl (fst x)) (snd x))` 
         `E2 = (subst_set (trms_ecl D) \<eta>)` 
         `trms_ecl (subst_ecl D \<eta>) = (subst_set (trms_ecl D) \<eta>)` 
         `( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl (subst_ecl D \<eta>)))` have "subterms_inclusion E1 E2" by auto
    from this and `E2 \<subseteq> E2'` have "subterms_inclusion E1 E2'" 
      using subterms_inclusion_subset by auto
    from this and `E1 = (subst_set (trms_ecl (fst x)) (snd x))` `E2' = (trms_ecl C)`
      and `\<not>( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl C))` show False by auto
   qed
   from this and `(set_entails_clause (clset_instances S') (cl_ecl C))` 
      and `(\<forall>x \<in> S'. \<exists>D' \<in> P. (((fst x),(snd x)),(D',\<sigma>)) \<in> ecl_ord)`
      and `S' \<subseteq> (instances S)` 
    show "redundant_inference C S P \<sigma>" unfolding redundant_inference_def by auto
qed

lemma lift_inference:
  assumes "inference_saturated S"
  shows "ground_inference_saturated S"
proof (rule ccontr)
  assume "\<not> (ground_inference_saturated S)"
  from this obtain C P \<sigma> C' where "derivable C P S \<sigma> Ground C'" "ground_clause (cl_ecl C)" 
    "grounding_set P \<sigma>" "\<not>redundant_inference C S P \<sigma>" unfolding ground_inference_saturated_def 
    by blast
  from `derivable C P S \<sigma> Ground C'` obtain D \<theta> \<eta> where "derivable D P S \<theta> FirstOrder C'" 
    "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>" "trms_subsumes D C \<eta>" using lifting_lemma by blast
  from `trms_subsumes D C \<eta>` and `\<not>redundant_inference C S P \<sigma>`  `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>`
    have "\<not> redundant_inference (subst_ecl D \<eta>) S P \<sigma>" 
    using trms_subsumes_and_red_inf by auto
  from this and `derivable C P S \<sigma> Ground C'` `derivable D P S \<theta> FirstOrder C'` `trms_subsumes D C \<eta>`
   `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` `ground_clause (cl_ecl C)` `grounding_set P \<sigma>` 
   `\<not> redundant_inference (subst_ecl D \<eta>) S P \<sigma>`
    assms(1) show False unfolding inference_saturated_def by auto
qed

lemma lift_redundant_cl :
  assumes "C' = subst_cl D \<theta>" 
  assumes "redundant_clause C S \<eta> C'" 
  assumes "\<sigma> \<doteq> \<theta> \<lozenge> \<eta>"
  assumes "finite D"
  shows "redundant_clause C S \<sigma> D"
proof -
  from assms(2) have 
    "(\<exists>S'. (S' \<subseteq> (instances S) \<and> (set_entails_clause (clset_instances S') (cl_ecl C)) \<and> 
            (\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl C))) \<and>
            (\<forall>x \<in> S'. ( ((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<eta>))) \<in> (mult (mult trm_ord))
              \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<eta>)))))"
               unfolding  redundant_clause_def  by auto
  from this obtain S' where i: "S' \<subseteq> (instances S)" 
    and ii: "(set_entails_clause (clset_instances S') (cl_ecl C))"
  and iii: "(\<forall>x \<in> S'. ( subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) 
              (trms_ecl C)))"
  and 
  iv: "(\<forall>x \<in> S'. ( ((mset_ecl ((fst x),(snd x))),(mset_cl (C',\<eta>))) \<in> (mult (mult trm_ord))
              \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (C',\<eta>)))"
             by auto
  let ?m1 = "mset_cl (C',\<eta>)"
  let ?m2 = "mset_cl (D,\<sigma>)"
  from assms(1) assms(3) assms(4)
    have "mset_cl (C',\<eta>) = mset_cl (D,\<sigma>) \<or> (mset_cl (C',\<eta>),mset_cl (D,\<sigma>)) \<in> (mult (mult trm_ord))" 
    using mset_subst by auto
  from this iv 
    have "(\<forall>x \<in> S'. ( ((mset_ecl ((fst x),(snd x))),(mset_cl (D,\<sigma>))) \<in> (mult (mult trm_ord))
            \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (D,\<sigma>)))" 
    using mult_mult_trm_ord_trans unfolding trans_def by metis
  from this and i ii iii show ?thesis  unfolding  redundant_clause_def by meson
qed
  
text {* We deduce the following (trivial) lemma, stating that sets that are closed under all 
inferences are also saturated. *}

lemma inference_closed_sets_are_saturated:
  assumes "inference_closed S"
  assumes "\<forall>x \<in> S. (finite (cl_ecl x))"
  shows "clause_saturated S"
proof (rule ccontr)
  assume "\<not>?thesis"
  from this obtain C P \<sigma> C' D \<theta> \<eta> 
    where 
     "(derivable C P S \<sigma> Ground C')" "(ground_clause (cl_ecl C))" 
     "(derivable D P S \<theta> FirstOrder C')" "(trms_subsumes D C \<eta>)"
     "(\<sigma> \<doteq> \<theta> \<lozenge> \<eta>)"
     "\<not>(redundant_clause (subst_ecl D \<eta>) S \<sigma> C')"
      unfolding clause_saturated_def by blast
  from `(derivable D P S \<theta> FirstOrder C')` assms(1) have "D \<in> S" 
    unfolding inference_closed_def by auto
  from `derivable D P S \<theta> FirstOrder C'` have "(cl_ecl D) = (subst_cl C' \<theta>)" 
    using derivable_clauses_lemma by auto
  from `trms_subsumes D C \<eta>` have "(cl_ecl C) = (subst_cl (cl_ecl D) \<eta>)"
    unfolding trms_subsumes_def by blast
  from `\<sigma> \<doteq> \<theta> \<lozenge> \<eta>` have "subst_cl (cl_ecl D) \<sigma> = subst_cl (cl_ecl D) (\<theta> \<lozenge> \<eta>)"
    using subst_eq_cl by blast
  then have "(subst_cl (cl_ecl D) \<sigma>) = (subst_cl (subst_cl (cl_ecl D) \<theta>) \<eta>)"
      using composition_of_substs_cl [of "cl_ecl D" \<theta> \<eta>] by auto
  from this and `(cl_ecl C) = (subst_cl (cl_ecl D) \<eta>)` 
    `(ground_clause (cl_ecl C))` have "ground_clause (subst_cl (cl_ecl D) \<eta>)"
    by auto
  from this `D \<in> S` `(cl_ecl D) = (subst_cl C' \<theta>)`
    `(cl_ecl D) = (subst_cl C' \<theta>)`  
    have "redundant_clause (subst_ecl D \<eta>) S \<eta> (subst_cl C' \<theta>)" 
    using self_redundant_clause  by metis
  from `derivable D P S \<theta> FirstOrder C'` have "P \<subseteq> S" unfolding derivable_def by auto
  from this assms(2) have "\<forall>x \<in> P. (finite (cl_ecl x))" by auto
  from this  `derivable D P S \<theta> FirstOrder C'` have  "finite C'" 
    using derivable_clauses_are_finite by auto
  from this `(cl_ecl D) = subst_cl C' \<theta>` 
      `redundant_clause (subst_ecl D \<eta>) S \<eta> (subst_cl C' \<theta>)` `(\<sigma> \<doteq> \<theta> \<lozenge> \<eta>)` 
    have "redundant_clause (subst_ecl D \<eta>) S \<sigma> C'"
    using lift_redundant_cl  by metis
  from this and `\<not>(redundant_clause (subst_ecl D \<eta>) S \<sigma> C')` show False by auto
qed

subsection {* Satisfiability of Saturated Sets with No Empty Clause *}

text {* We are now in the position to prove that the previously constructed interpretation 
is indeed a model of the set of extended clauses, if the latter is saturated and does not contain
an extended clause with empty clausal part. More precisely, the constructed interpretation satisfies 
the clausal part of every extended clause whose attached set of terms is in normal form. This is the 
case in particular if this set is empty, hence if the clause is an input clause. 

Note that we do not provide any function for explicitly 
constructing such saturated sets, except by generating all derivable clauses (see below). *}
 
lemma int_clset_is_a_model:
  assumes "ground_inference_saturated S"
  assumes all_finite: "\<forall>x \<in> S. (finite (cl_ecl x))"
  assumes "Ball S well_constrained"
  assumes all_non_empty: "\<forall>x \<in> S. (cl_ecl x) \<noteq> {}"
  assumes "closed_under_renaming S"
  shows "\<forall> C \<sigma>. (fst pair = C) \<longrightarrow> \<sigma> = (snd pair) \<longrightarrow> C \<in> S \<longrightarrow> 
    ground_clause (subst_cl (cl_ecl C) \<sigma>) 
    \<longrightarrow> (all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. (trm_rep t S))) 
          \<longrightarrow> validate_ground_clause (same_values (\<lambda>t. (trm_rep t S))) (subst_cl (cl_ecl C) \<sigma>)" 
          (is "?P pair") 
proof ((rule wf_induct [of "ecl_ord" "?P" "pair"]),(simp add: wf_ecl_ord))
next

text {* The proof is by induction and contradiction. We consider a minimal instance  
that is not true in the interpretation and we derive a contradiction. *}

    fix pair assume hyp_ind: "\<forall>y. (y,pair) \<in> ecl_ord \<longrightarrow> (?P y)"
    let ?I = "(int_clset S)"
    have "fo_interpretation ?I" 
      unfolding int_clset_def using trm_rep_compatible_with_structure same_values_fo_int  
      by metis
    show "(?P pair)"
    proof (rule ccontr)
      assume "\<not>(?P pair)"
      then obtain C \<sigma> where "C = (fst pair)" and "\<sigma> = (snd pair)" and "C \<in> S" 
            and "ground_clause (subst_cl (cl_ecl C) \<sigma>)" 
            and "(all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) 
                  (\<lambda>t. (trm_rep t S)))"
            and cm: "\<not>validate_ground_clause (int_clset S) (subst_cl (cl_ecl C) \<sigma>)"
         unfolding int_clset_def by metis
      
text {* First, we prove that no reduction is possible (otherwise the superposition rule applies). *}

     let ?nored = "(\<forall>L1 L2 D t s u' u v p polarity \<sigma>'. 
      \<not> ((reduction L1 C \<sigma>' t s polarity L2 u u' p v D ?I S \<sigma>) \<and> (variable_disjoint C D)))"
      have ?nored
      proof (rule ccontr)
        assume "\<not> ?nored"
        then obtain L1 L2 D t s u' u v p polarity \<sigma>'
          where red: "reduction L1 C \<sigma>' t s polarity L2 u u' p v D ?I S \<sigma>" 
            and "variable_disjoint C D" 
          by blast
        from red have "(subst u \<sigma>') \<noteq> (subst v \<sigma>')" 
          unfolding reduction_def by blast
        from red have "ground_clause (subst_cl (cl_ecl D) \<sigma>')" 
          unfolding reduction_def by blast
        from red have "(coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C)))"
          unfolding reduction_def by blast
        from red have "\<not> is_a_variable u'"  unfolding reduction_def by blast
        from red have "D \<in> S" unfolding reduction_def by blast
        from red have el1: "(eligible_literal L1 C \<sigma>')" unfolding reduction_def by blast
        from red have el2: "(eligible_literal L2 D \<sigma>')" unfolding reduction_def by blast
        from red have "D \<in> S" unfolding reduction_def by blast
        from red have "(minimal_redex p (subst t \<sigma>) C S t)" 
          unfolding reduction_def by blast
        from red have l1: "L1 \<in> (cl_ecl C)" unfolding reduction_def by blast
        from red have l2: "L2 \<in> (cl_ecl D)" unfolding reduction_def by blast
        from red have  o1: "(orient_lit_inst L1 t s polarity \<sigma>')"  unfolding reduction_def by blast
        from red have  o2: "(orient_lit_inst L2 u v pos \<sigma>')"  unfolding reduction_def by blast
        from red have  e:"(subst u' \<sigma>') = (subst u \<sigma>')" 
          unfolding reduction_def by blast
        from red have "(\<not> validate_ground_clause ?I (subst_cl ( (cl_ecl D) - { L2 } ) \<sigma>'))" 
          unfolding reduction_def by blast
        from red have "(\<forall>x \<in> (cl_ecl D) - { L2 }. ( (subst_lit x \<sigma>'),(subst_lit L2 \<sigma>')) 
                                        \<in> lit_ord)"
                     unfolding reduction_def by blast
        from red have st: "(subterm t p u')" unfolding reduction_def by blast
        from red have "(allowed_redex u' C \<sigma>)"  unfolding reduction_def by blast
        from st have "u' \<in> (subterms_of t)" using occurs_in_def by auto
        from this and o1 have "u' \<in> (subterms_of_lit L1)" using orient_lit_inst_subterms by auto
        from this and `L1 \<in> (cl_ecl C)` have "u' \<in> (subterms_of_cl (cl_ecl C))" by auto
        from this and `(allowed_redex u' C \<sigma>)` and `C \<in> S` 
          and `(coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C)))` 
          assms(3)
          have rte: "(allowed_redex u' C \<sigma>')"  using allowed_redex_coincide [of u' C \<sigma> \<sigma>'] 
             by metis

        from red have "( (subst_lit L2 \<sigma>'),(subst_lit L1 \<sigma>')) 
            \<in> lit_ord" unfolding reduction_def by blast 
        from red have "(all_trms_irreducible (subst_set (trms_ecl D) \<sigma>') 
                  (\<lambda>t. (trm_rep t S)))" unfolding reduction_def by blast 
        from red have "?I (subst u \<sigma>')  (subst v \<sigma>')" 
          unfolding reduction_def by blast 

        from e have t: "ck_unifier u' u \<sigma>' Ground" unfolding ck_unifier_def Unifier_def by auto

        have "\<forall>x \<in> (cl_ecl D). ( (mset_lit (subst_lit x \<sigma>')),(mset_lit (subst_lit L1 \<sigma>'))) 
                                        \<in> (mult trm_ord)"
        proof (rule ccontr)
          assume "\<not>(\<forall>x \<in> (cl_ecl D). ( (mset_lit (subst_lit x \<sigma>')),(mset_lit (subst_lit L1 \<sigma>'))) 
                                        \<in> (mult trm_ord))"
          from this obtain x where "x \<in> (cl_ecl D)" 
          and "( (mset_lit (subst_lit x \<sigma>')),(mset_lit (subst_lit L1 \<sigma>'))) 
                                        \<notin> (mult trm_ord)" 
          by auto
          show False
          proof (cases)
            assume "x = L2"
            from this and `((subst_lit L2 \<sigma>'),(subst_lit L1 \<sigma>')) 
            \<in> lit_ord` and `( (mset_lit (subst_lit x \<sigma>')),(mset_lit (subst_lit L1 \<sigma>'))) 
                                        \<notin> (mult trm_ord)`
              show False unfolding lit_ord_def by auto
          next
            assume "x \<noteq> L2"
            from this and `x \<in> (cl_ecl D)` have "x \<in> (cl_ecl D) - { L2 }" by auto
            from this and `(\<forall>x \<in> (cl_ecl D) - { L2 }. ( (subst_lit x \<sigma>'),(subst_lit L2 \<sigma>')) 
                                        \<in> lit_ord)`
                    have "( (subst_lit x \<sigma>'),(subst_lit L2 \<sigma>')) 
                                        \<in> lit_ord" by auto
            from `((mset_lit (subst_lit x \<sigma>')),(mset_lit (subst_lit L1 \<sigma>'))) 
                                        \<notin> (mult trm_ord)` 
                have "((subst_lit x \<sigma>'),(subst_lit L1 \<sigma>')) 
                                        \<notin> lit_ord" 
                                        unfolding lit_ord_def by auto

            from this and `( (subst_lit x \<sigma>'),(subst_lit L2 \<sigma>')) 
                                        \<in> lit_ord`  
             and `((subst_lit L2 \<sigma>'),(subst_lit L1 \<sigma>')) 
            \<in> lit_ord` 
            show False using lit_ord_trans unfolding trans_def by blast
          qed
        qed
        from all_finite and `C \<in> S` have "finite (cl_ecl C)" by auto
        from this and `L1 \<in> (cl_ecl C)`  
        have "(mset_lit (subst_lit L1 \<sigma>')) \<in>#  mset_ecl (C,\<sigma>')" 
          using mset_ecl_and_mset_lit by auto 
          from this have "(mset_lit (subst_lit L1 \<sigma>')) \<in> (set_mset (mset_ecl (C,\<sigma>')))"
            by simp
        have "\<forall>x. (x \<in> (set_mset (mset_ecl (D,\<sigma>'))) 
          \<longrightarrow> (\<exists>y \<in> set_mset (mset_ecl (C,\<sigma>')). (x,y) \<in> (mult trm_ord)))"
        proof ((rule allI),(rule impI))
          fix x assume "x \<in> (set_mset (mset_ecl (D,\<sigma>')))"

          then have "x \<in># mset_ecl (D,\<sigma>')" by simp
          from `x \<in># mset_ecl (D,\<sigma>')` obtain x' 
            where "x' \<in># (mset_set (cl_ecl D))" 
            and "x = (mset_lit (subst_lit x' \<sigma>'))" by auto
              
        from `x' \<in># (mset_set (cl_ecl D))` have "x' \<in> (cl_ecl D)"
          using count_mset_set(3) by (fastforce simp: count_eq_zero_iff)
        from this 
          and `\<forall>x \<in> (cl_ecl D). 
          ( (mset_lit (subst_lit x \<sigma>')),(mset_lit (subst_lit L1 \<sigma>'))) 
                                        \<in> (mult trm_ord)` 
                  and `x = (mset_lit (subst_lit x' \<sigma>'))` 
                  have "(x,(mset_lit (subst_lit L1 \<sigma>'))) \<in> (mult trm_ord)" 
                  by auto
        
          from `(mset_lit (subst_lit L1 \<sigma>')) \<in> (set_mset (mset_ecl (C,\<sigma>')))`
          and `(x,(mset_lit (subst_lit L1 \<sigma>'))) \<in> (mult trm_ord)` 
          show 
          "(\<exists>y \<in> set_mset (mset_ecl (C,\<sigma>')). (x,y) \<in> (mult trm_ord))"
          by auto
        qed

        from this have 
          dom: "\<And>I J K. J \<noteq> {#} \<and> (\<forall>k\<in>set_mset K. \<exists>j\<in>set_mset J. (k, j) \<in> (mult trm_ord)) \<longrightarrow>
          (I + K, I + J) \<in> mult (mult trm_ord)"
          by (blast intro: one_step_implies_mult)
        from `(mset_lit (subst_lit L1 \<sigma>')) \<in>#  mset_ecl (C,\<sigma>')` 
          have "mset_ecl (C,\<sigma>') \<noteq> {#}" by auto 
        from `\<forall>x. (x \<in> (set_mset (mset_ecl (D,\<sigma>')))   
                \<longrightarrow> (\<exists>y \<in> set_mset (mset_ecl (C,\<sigma>')). (x,y) \<in> (mult trm_ord)))`
             and `mset_ecl (C,\<sigma>') \<noteq> {#}` 
          have "({#} + mset_ecl (D, \<sigma>'), {#} + mset_ecl (C, \<sigma>')) \<in> mult (mult trm_ord)"
        using dom [of "(mset_ecl (C,\<sigma>'))" "mset_ecl (D,\<sigma>')" "{#}"] by auto
        from this have "(mset_ecl (D, \<sigma>'), mset_ecl (C, \<sigma>')) \<in> mult (mult trm_ord)"
        by auto
        from this have "( (D,\<sigma>'), (C,\<sigma>') ) \<in> ecl_ord" 
          unfolding ecl_ord_def by auto

      from st obtain t' where rt: "(replace_subterm t p v t')" 
        using replace_subterm_is_a_function by blast

      from st  obtain R Cl_R nt_R L' Cl_C Cl_D  where 
            ntr: "nt_R = (dom_trms Cl_R (subst_set 
              ((trms_ecl C) \<union> (trms_ecl D) \<union> 
              { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) }) \<sigma>'))"
            and r: "R = Ecl Cl_R nt_R" 
            and clc: "Cl_C = (cl_ecl C)"
            and cld: "Cl_D = (cl_ecl D)"
            and clr: "Cl_R = (subst_cl ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } )) \<sigma>')"
            and l': "L' = mk_lit polarity (Eq t' s)" 
            by auto

       from `orient_lit_inst L1 t s polarity \<sigma>'` have "vars_of t \<subseteq> vars_of_lit L1" 
        using orient_lit_inst_vars by auto
       from `L1 \<in> (cl_ecl C)` have "vars_of_lit L1 \<subseteq> vars_of_cl (cl_ecl C)" by auto
       from this and `vars_of t \<subseteq> vars_of_lit L1` have "vars_of t \<subseteq>vars_of_cl (cl_ecl C)" by auto
       from this and `coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))` 
        have "coincide_on \<sigma> \<sigma>' (vars_of t)" unfolding coincide_on_def by auto
       from this have "subst t \<sigma> = subst t \<sigma>'" using coincide_on_term by auto

       from `(\<forall>x \<in> (cl_ecl D) - { L2 }. ( (subst_lit x \<sigma>'),(subst_lit L2 \<sigma>')) 
                                        \<in> lit_ord)`
          have "strictly_maximal_literal D L2 \<sigma>'" unfolding strictly_maximal_literal_def by metis
       from ntr have "nt_R = get_trms Cl_R (dom_trms Cl_R (subst_set 
              ((trms_ecl C) \<union> (trms_ecl D) \<union> 
              { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) }) \<sigma>')) Ground"
               unfolding get_trms_def by auto
       from this `(subst u \<sigma>') \<noteq> (subst v \<sigma>')` `\<not> is_a_variable u'` l1 l2 el1 el2  
        `variable_disjoint C D` rte r o1 o2 t st rt l' clr ntr clr clc cld `R = Ecl Cl_R nt_R`
        `( (subst_lit L2 \<sigma>'),(subst_lit L1 \<sigma>')) 
            \<in> lit_ord`  
        `strictly_maximal_literal D L2 \<sigma>' `
        have "superposition C D R \<sigma>' Ground ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } ))" 
          unfolding superposition_def  by blast
         from l2 have "(subst_lit L2 \<sigma>') \<in> (subst_cl (cl_ecl D) \<sigma>')" by auto
         from this and `ground_clause (subst_cl (cl_ecl D) \<sigma>')` 
          have "vars_of_lit (subst_lit L2 \<sigma>') = {}"
          by auto
         from this and o2 have "vars_of (subst v \<sigma>') = {}" 
          unfolding orient_lit_inst_def using vars_of_lit.simps vars_of_eq.simps by force

         from `(coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C)))`
            have "(subst_cl (cl_ecl C) \<sigma>') = (subst_cl (cl_ecl C) \<sigma>)" 
            using  coincide_on_cl [of  \<sigma> \<sigma>' "(cl_ecl C)"] by auto

         from this and `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
            have "ground_clause (subst_cl (cl_ecl C) \<sigma>')" using  
              coincide_on_cl by auto

         from l1 have "(subst_lit L1 \<sigma>') \<in> (subst_cl (cl_ecl C) \<sigma>')" by auto
         from this and `ground_clause (subst_cl (cl_ecl C) \<sigma>')` 
          have "vars_of_lit (subst_lit L1 \<sigma>') = {}" by auto
         from this and o1 have "vars_of (subst t \<sigma>') = {}" 
          unfolding orient_lit_inst_def using vars_of_lit.simps vars_of_eq.simps by force
         from `vars_of_lit (subst_lit L1 \<sigma>') = {}`
          and o1 have "vars_of (subst s \<sigma>') = {}" 
          unfolding orient_lit_inst_def using vars_of_lit.simps vars_of_eq.simps by force

         from `vars_of (subst t \<sigma>') = {}` and `vars_of (subst v \<sigma>') = {}`
          and rt have "vars_of (subst t' \<sigma>') = {}" using ground_replacement [of t p v t' \<sigma>']
            unfolding ground_term_def by blast

         from `vars_of (subst t' \<sigma>') = {}` and `vars_of (subst s \<sigma>') = {}`
          have "vars_of_eq (subst_equation (Eq t' s) \<sigma>') = {}" by auto
         from l' have "L' = (Pos (Eq t' s)) \<or> L' = (Neg (Eq t' s))" using mk_lit.elims by auto 
         from this and `vars_of_eq (subst_equation (Eq t' s) \<sigma>') = {}`
          have "vars_of_lit (subst_lit L' \<sigma>') = {}" by auto

        from `C \<in> S` and `D \<in> S` and 
          `superposition C D R \<sigma>' Ground ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } ))` 
          have "derivable R { C,D } S \<sigma>' Ground ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } ))" 
          unfolding derivable_def by auto

        have "ground_clause Cl_R"
        proof (rule ccontr)
          assume "\<not>ground_clause Cl_R"
          then have "vars_of_cl Cl_R \<noteq> {}" by auto
          then obtain M where "M \<in> Cl_R" and "vars_of_lit M \<noteq> {}" by auto
          from `M \<in> Cl_R` and clr obtain M' where "M = (subst_lit M' \<sigma>')" 
          and "M' \<in> ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } )) "
            by auto
          show False
          proof (cases)
            assume "M' = L'"
            from this and `vars_of_lit (subst_lit L' \<sigma>') = {}` and `vars_of_lit M \<noteq> {}`
              and `M = (subst_lit M' \<sigma>')` show False by auto
          next
            assume "M' \<noteq> L'"
            from this and l1 clc cld and `M' \<in>(Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } )` 
              have "M' \<in> (cl_ecl C) \<or> M' \<in> (cl_ecl D)"
              by auto
            then show False
            proof
              assume "M' \<in> (cl_ecl C)"
              from this and `ground_clause (subst_cl (cl_ecl C) \<sigma>')` have 
              "vars_of_lit (subst_lit M' \<sigma>') = {}" by auto
              from this and `M = (subst_lit M' \<sigma>')` and
              `vars_of_lit M \<noteq> {}` show False by auto
            next
              assume "M' \<in> (cl_ecl D)"
              from this and `ground_clause (subst_cl (cl_ecl D) \<sigma>')` have 
              "vars_of_lit (subst_lit M' \<sigma>') = {}" by auto
              from this and `M = (subst_lit M' \<sigma>')` and
              `vars_of_lit M \<noteq> {}` show False by auto
           qed
          qed
        qed
        from `ground_clause (subst_cl (cl_ecl C) \<sigma>')` and `ground_clause (subst_cl (cl_ecl D) \<sigma>')` 
          have "grounding_set { C,D } \<sigma>'" unfolding grounding_set_def by auto   
        from `ground_clause Cl_R` and `R = Ecl Cl_R nt_R` have "ground_clause (cl_ecl R)" by auto
        
        from this and `derivable R { C,D } S \<sigma>' Ground ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } ))`
          and `ground_inference_saturated S` `grounding_set { C,D } \<sigma>'` 
          have "(redundant_inference R S { C,D } \<sigma>')" unfolding ground_inference_saturated_def 
          by blast
        from this obtain S' where "S' \<subseteq> (instances S)" and 
          "(set_entails_clause (clset_instances S') (cl_ecl R))"
          and order: "(\<forall>x \<in> S'. (((fst x),(snd x)),(C,\<sigma>')) \<in> ecl_ord 
          \<or> (((fst x),(snd x)),(D,\<sigma>')) \<in> ecl_ord)"
          and all_normalized_term_included: "(\<forall>x \<in> S'. 
          (subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x))  
              (trms_ecl R)))"
          unfolding redundant_inference_def by auto 

        have all_smaller: "(\<forall>x \<in> S'. (((fst x),(snd x)),(C,\<sigma>)) \<in> ecl_ord)"
        proof (rule ccontr)
          assume "\<not>(\<forall>x \<in> S'. (((fst x),(snd x)),(C,\<sigma>)) \<in> ecl_ord)"
          then obtain x where "x \<in> S'" and "(((fst x),(snd x)),(C,\<sigma>)) \<notin> ecl_ord"
            by auto
          from `x \<in> S'` and order have "(((fst x),(snd x)),(C,\<sigma>')) \<in> ecl_ord 
          \<or> (((fst x),(snd x)),(D,\<sigma>')) \<in> ecl_ord" by auto
          then have "(((fst x),(snd x)),(C,\<sigma>')) \<in> ecl_ord" 
          proof
            assume "(((fst x),(snd x)),(C,\<sigma>')) \<in> ecl_ord"
            from this show ?thesis by auto
          next
            assume "(((fst x),(snd x)),(D,\<sigma>')) \<in> ecl_ord"
            from this and `( (D,\<sigma>'),(C,\<sigma>')) \<in> ecl_ord` show 
              "(((fst x),(snd x)),(C,\<sigma>')) \<in> ecl_ord" using ecl_ord_trans 
                unfolding trans_def by metis
          qed
          from this have 
            "((mset_ecl x), (mset_ecl (C,\<sigma>'))) \<in> (mult (mult trm_ord))"
              unfolding ecl_ord_def by auto
            from `(coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C)))` 
              have "(mset_ecl (C,\<sigma>')) = (mset_ecl (C,\<sigma>))" 
              using ecl_ord_coincide [of \<sigma> \<sigma>' C] by auto
            from this and `((mset_ecl x), (mset_ecl (C,\<sigma>'))) \<in> (mult (mult trm_ord))`
              have "((mset_ecl x), (mset_ecl (C,\<sigma>))) \<in> (mult (mult trm_ord))"
              by simp
            from this and `\<not>(((fst x),(snd x)),(C,\<sigma>)) \<in> ecl_ord` show False 
              unfolding ecl_ord_def by auto
        qed

        have "validate_clause_set ?I (clset_instances S')"
        proof (rule ccontr)
          assume "\<not> validate_clause_set ?I (clset_instances S')"
          then obtain x where "x \<in>(clset_instances S')" and "\<not>validate_clause ?I x"
            using validate_clause_set.simps by blast
         from `x \<in>(clset_instances S')` obtain pair' where "pair' \<in> S'" 
          and "x = (subst_cl (cl_ecl (fst pair')) (snd pair'))" 
          unfolding clset_instances_def 
          by auto
         from all_smaller and `pair' \<in> S'` have "(pair',(C,\<sigma>)) \<in> ecl_ord"
          by auto
         from this and  `C = fst pair` and `\<sigma> = snd pair` have "(pair',pair) \<in> ecl_ord"
          by auto
         from this and hyp_ind  have "?P pair'" by blast

         from `pair' \<in> S'` and all_normalized_term_included have 
          "(subterms_inclusion (subst_set (trms_ecl (fst pair')) (snd pair')) 
             (trms_ecl R))" by auto
         have i: "(all_trms_irreducible (subst_set (trms_ecl (fst pair')) (snd pair')) 
                  (\<lambda>t. (trm_rep t S)))"
         proof (rule ccontr)
          assume "\<not>(all_trms_irreducible (subst_set (trms_ecl (fst pair')) (snd pair')) 
                  (\<lambda>t. (trm_rep t S)))"
          then obtain w w' where "w \<in> subst_set (trms_ecl (fst pair')) (snd pair')"
           and "occurs_in w' w"
            "trm_rep w' S \<noteq> w'" 
            unfolding all_trms_irreducible_def by blast
          from `w \<in> subst_set (trms_ecl (fst pair')) (snd pair')` and 
          `(subterms_inclusion (subst_set (trms_ecl (fst pair')) (snd pair')) 
             (trms_ecl R))` obtain w'' where "w'' \<in> trms_ecl R" and "occurs_in w w''" 
             unfolding subterms_inclusion_def by auto
          from `occurs_in w w''` and `occurs_in w' w` have "occurs_in w' w''"
            using occur_in_subterm by blast  
          from  ntr have "nt_R \<subseteq> (subst_set ((trms_ecl C) \<union> (trms_ecl D) \<union> 
              { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) }) \<sigma>')" 
          using dom_trms_subset [of Cl_R "(subst_set ((trms_ecl C) \<union> (trms_ecl D) \<union> 
              { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) }) \<sigma>')"] by blast
          from this and r have "trms_ecl R \<subseteq> (subst_set ((trms_ecl C) \<union> (trms_ecl D) \<union> 
              { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) }) \<sigma>')" by auto
          from this and `w'' \<in> trms_ecl R` have
            "w'' \<in> (subst_set ((trms_ecl C) \<union> (trms_ecl D) \<union> 
              { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) }) \<sigma>')" by blast
          from this obtain w'''
            where "w''' \<in> ((trms_ecl C) \<union> (trms_ecl D) \<union> 
              { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) })" and "w'' = subst w''' \<sigma>'"
              by auto
          from this and `occurs_in w' w''` have "occurs_in w' (subst w''' \<sigma>')" by auto

          have "\<not> (w''' \<in> trms_ecl C)"
          proof 
            assume "w''' \<in> trms_ecl C"
            from this and `occurs_in w' w''` and `w'' = subst w''' \<sigma>'` have
              "occurs_in w' (subst w''' \<sigma>')" by auto
            from assms(3) and `C \<in> S` and `w''' \<in> trms_ecl C` 
              have "vars_of w''' \<subseteq> vars_of_cl (cl_ecl C)" using dom_trm_vars 
                unfolding Ball_def well_constrained_def by blast
            from this and `coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))` have "coincide_on \<sigma> \<sigma>' (vars_of w''')"
              unfolding coincide_on_def by auto
            from this have "subst w''' \<sigma> = subst w''' \<sigma>'" 
              using coincide_on_term by auto
            from this 
              and `occurs_in w' (subst w''' \<sigma>')` 
              have "occurs_in w' (subst w''' \<sigma>)" by auto
            from this and `w''' \<in> trms_ecl C` 
              `(all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) 
                  (\<lambda>t. (trm_rep t S)))` 
                  have "trm_rep w' S = w'" 
                  unfolding all_trms_irreducible_def using subst_set.simps by blast
            from this and `trm_rep w' S \<noteq> w'` show False by blast
          qed

          have "\<not> (w''' \<in> trms_ecl D)"
          proof 
            assume "w''' \<in> trms_ecl D"
            from this and `occurs_in w' w''` and `w'' = subst w''' \<sigma>'` have
              "occurs_in w' (subst w''' \<sigma>')" by auto
            from this and `w''' \<in> trms_ecl D` 
              `(all_trms_irreducible (subst_set (trms_ecl D) \<sigma>') 
                  (\<lambda>t. (trm_rep t S)))` 
                  have "trm_rep w' S = w'" 
                  unfolding all_trms_irreducible_def using subst_set.simps by blast
            from this and `trm_rep w' S \<noteq> w'` show False by blast
          qed

          from this and 
          `w''' \<in> ((trms_ecl C) \<union> (trms_ecl D) 
            \<union> { r. \<exists> q. (q,p) \<in> (pos_ord C t) \<and> (subterm t q r) })` 
          and `\<not> (w''' \<in> trms_ecl C)` 
              obtain q_w where "(subterm t q_w w''')" and "(q_w,p) \<in> (pos_ord C t)" by auto

          from `subterm t q_w w'''` have "subterm (subst t \<sigma>') q_w (subst w''' \<sigma>')"
            using substs_preserve_subterms by auto
          from `occurs_in w' (subst w''' \<sigma>')` obtain q 
            where "(subterm  (subst w''' \<sigma>') q w')" unfolding occurs_in_def by blast
          from this and `subterm (subst t \<sigma>') q_w (subst w''' \<sigma>')`
            have "subterm (subst t \<sigma>') (append q_w q) w'" using subterm_of_a_subterm_is_a_subterm
           by blast
           from this and `(subst t \<sigma>) = (subst t \<sigma>')`
            have "subterm (subst t \<sigma>) (append q_w q) w'" by auto
          from `(q_w,p) \<in> (pos_ord C t)` have "((append q_w q),p) \<in> (pos_ord C t)" 
            using pos_ord_prefix by blast
          from this and `minimal_redex p (subst t \<sigma>) C S t`
            and `subterm (subst t \<sigma>) (append q_w q) w'` 
            have "trm_rep w' S = w'"
            unfolding minimal_redex_def by blast
          from this and `trm_rep w' S \<noteq> w'` show False by blast
         qed
         from `S' \<subseteq> (instances S)` and `pair' \<in> S'` have 
          ii: "ground_clause (subst_cl (cl_ecl (fst pair')) (snd pair'))" 
          unfolding instances_def [of S] by fastforce 
         from `S' \<subseteq> (instances S)` and `pair' \<in> S'` have 
          iii: "(fst pair') \<in> S" unfolding instances_def [of S] by fastforce 
         from `?P pair'` and i ii iii have "validate_ground_clause ?I 
          (subst_cl (cl_ecl (fst pair')) (snd pair'))" unfolding int_clset_def by blast
         from this and `x = (subst_cl (cl_ecl (fst pair')) (snd pair'))` 
          and `\<not>validate_clause ?I x` show False  
          by (metis ii substs_preserve_ground_clause validate_clause.simps) 
        qed
        from this and `fo_interpretation ?I` and 
        `(set_entails_clause (clset_instances S') (cl_ecl R))`
          have "validate_clause ?I (cl_ecl R)" unfolding set_entails_clause_def by blast
        from this have "validate_ground_clause ?I (cl_ecl R)"
          by (metis `R = Ecl Cl_R nt_R` `ground_clause Cl_R` 
            cl_ecl.simps substs_preserve_ground_clause validate_clause.simps) 
        from this obtain L'' where "L'' \<in> (cl_ecl R)" and "validate_ground_lit ?I L''"
          using validate_ground_clause.simps by blast 
        from `L'' \<in> (cl_ecl R)` and `R = Ecl Cl_R nt_R` and
          `Cl_R = (subst_cl ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } )) \<sigma>')` 
          obtain M where m: "M \<in> ((Cl_C - { L1 }) \<union> ((Cl_D - { L2 }) \<union> { L' } ))" 
          and "L'' = subst_lit M \<sigma>'" by auto 
        have "M \<notin> cl_ecl C"  
        proof 
          assume "M \<in> cl_ecl C"
          from this have "vars_of_lit M \<subseteq> vars_of_cl (cl_ecl C)" by auto
          from this and `coincide_on \<sigma> \<sigma>' (vars_of_cl (cl_ecl C))`  
            have "coincide_on \<sigma> \<sigma>' (vars_of_lit M)" unfolding coincide_on_def by auto
          from this have "subst_lit M \<sigma> = subst_lit M \<sigma>'" using coincide_on_lit by auto
          from this and `L'' = subst_lit M \<sigma>'`have "L'' = subst_lit M \<sigma>" by auto
          from `M \<in> cl_ecl C` and `L'' = subst_lit M \<sigma>`and `validate_ground_lit ?I L''`
          have "validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)"
            by (metis (mono_tags, lifting) subst_cl.simps mem_Collect_eq 
              validate_ground_clause.simps)
          from this and cm show False by blast
        qed
        have "M \<notin> Cl_D - { L2 }"  
        proof 
          assume "M \<in> Cl_D - { L2 }"
          from this  and cld and `L'' = subst_lit M \<sigma>'` and `validate_ground_lit ?I L''`
            have "validate_ground_clause ?I (subst_cl ( (cl_ecl D) - { L2 } ) \<sigma>')"
            by (metis (mono_tags, lifting) subst_cl.simps mem_Collect_eq validate_ground_clause.simps)  
          from this and `\<not>validate_ground_clause ?I (subst_cl ( (cl_ecl D) - { L2 } ) \<sigma>')` 
            show False by blast
        qed
        have "M \<noteq> L'"
        proof
          assume "M = L'"
          from `?I (subst u \<sigma>')  (subst v \<sigma>')` 
            and e have "?I (subst u' \<sigma>')  (subst v \<sigma>')" by metis
          from rt and st `fo_interpretation ?I` `?I (subst u' \<sigma>')  (subst v \<sigma>')` 
            have "?I (subst t \<sigma>') (subst t' \<sigma>')" 
            using replacement_preserves_congruences [of ?I u' \<sigma>' v t p t'] 
              unfolding fo_interpretation_def by metis
          from l1 and cm have "\<not> (validate_ground_lit ?I (subst_lit L1 \<sigma>'))"
            using `subst_cl (cl_ecl C) \<sigma>' = subst_cl (cl_ecl C) \<sigma>` 
            `subst_lit L1 \<sigma>' \<in> subst_cl (cl_ecl C) \<sigma>'` 
            validate_ground_clause.simps by blast  
          from this and `?I (subst t \<sigma>') (subst t' \<sigma>')` and `fo_interpretation ?I` 
            and l' `orient_lit_inst L1 t s polarity \<sigma>'` 
            have "\<not>validate_ground_lit ?I (subst_lit L' \<sigma>')" 
            using trm_rep_preserves_lit_semantics [of ?I t \<sigma>' t' L1 s polarity \<sigma>'] by metis
          from this and `M = L'` and `validate_ground_lit ?I L''` and `L'' = subst_lit M \<sigma>'` 
            show False by blast
         qed
          from this and `M \<notin> Cl_D - { L2 }` `M \<notin> (cl_ecl C)` and m clc  show False by auto
       qed

text {* Second, we show that the clause contains no contradictory literal (otherwise the reflexion 
rule applies). *}

     let ?no_cont = "\<forall>L t s. (L \<in> (cl_ecl C)) \<longrightarrow> (eligible_literal L C \<sigma>) 
        \<longrightarrow> (orient_lit_inst L t s neg \<sigma>) \<longrightarrow> (trm_rep (subst t \<sigma>)  S) =  (subst t \<sigma>) 
        \<longrightarrow> (subst t \<sigma>) \<noteq> (subst s \<sigma>)"
      have ?no_cont
      proof (rule ccontr)
        assume "\<not> ?no_cont"
        then obtain L t s where l: "L \<in> (cl_ecl C)" and e: "(eligible_literal L C \<sigma>)" 
          and o: "orient_lit_inst L t s neg \<sigma>"
          and "(trm_rep (subst t \<sigma>)  S) =  (subst t \<sigma>)"
          and "(subst t \<sigma>) = (subst s \<sigma>)" by blast
        from `(subst t \<sigma>) = (subst s \<sigma>)`
          have t: "ck_unifier t s \<sigma> Ground" unfolding ck_unifier_def Unifier_def by auto
        from l and e and o and t obtain R Cl_R nt_R where 
            "R = Ecl Cl_R nt_R" and "Cl_R = (subst_cl ((cl_ecl C) - { L }) \<sigma>)" and 
            "reflexion C R \<sigma> Ground ((cl_ecl C) - { L })" 
            and "trms_ecl R = (dom_trms (cl_ecl R) (subst_set ((trms_ecl C) \<union> { t }) \<sigma>))"
            unfolding reflexion_def get_trms_def 
            by fastforce
        from `C \<in> S` and `reflexion C R \<sigma> Ground ((cl_ecl C) - { L })` 
          have "derivable R { C } S \<sigma> Ground ((cl_ecl C) - { L })" 
          unfolding derivable_def by auto
        from `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
          and `Cl_R = (subst_cl ((cl_ecl C) - { L }) \<sigma>)`
          have "ground_clause Cl_R" using ground_clause.simps by auto 
        from this and `R = Ecl Cl_R nt_R` have "ground_clause (cl_ecl R)" by auto
        from `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
          have "grounding_set { C } \<sigma>" unfolding grounding_set_def by auto
        from this and `ground_clause (cl_ecl R)`
         `derivable R { C } S \<sigma> Ground ((cl_ecl C) - { L })` and `ground_inference_saturated S` 
          have "(redundant_inference R S { C } \<sigma>)" unfolding ground_inference_saturated_def 
          by blast
        from this obtain S' where "S' \<subseteq> (instances S)" and 
          "(set_entails_clause (clset_instances S') (cl_ecl R))"
          and all_smaller: "(\<forall>x \<in> S'. (((fst x),(snd x)),(C,\<sigma>)) \<in> ecl_ord)"
          and all_normalized_term_included: "(\<forall>x \<in> S'. 
          (subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x))  
              (trms_ecl R)))"
          unfolding redundant_inference_def by auto
        have "validate_clause_set ?I (clset_instances S')"
        proof (rule ccontr)
          assume "\<not> validate_clause_set ?I (clset_instances S')"
          then obtain x where "x \<in>(clset_instances S')" and "\<not>validate_clause ?I x"
            using validate_clause_set.simps by blast
         from `x \<in>(clset_instances S')` obtain pair' where "pair' \<in> S'" 
          and "x = (subst_cl (cl_ecl (fst pair')) (snd pair'))" 
          unfolding clset_instances_def 
          by auto
         from all_smaller and `pair' \<in> S'` have "(pair',(C,\<sigma>)) \<in> ecl_ord"
          by auto
         from this and  `C = fst pair` and `\<sigma> = snd pair` have "(pair',pair) \<in> ecl_ord"
          by auto
         from this and hyp_ind  have "?P pair'" by blast
         
         from `trms_ecl R = (dom_trms (cl_ecl R) (subst_set ((trms_ecl C) \<union> { t }) \<sigma>))` 
          have "trms_ecl R \<subseteq> (subst_set ((trms_ecl C) \<union> { t }) \<sigma>)"
          using dom_trms_subset by metis
         from `pair' \<in> S'` and all_normalized_term_included have 
          "(subterms_inclusion (subst_set (trms_ecl (fst pair')) (snd pair')) 
             (trms_ecl R))" by auto
         have i: "(all_trms_irreducible (subst_set (trms_ecl (fst pair')) (snd pair')) 
                  (\<lambda>t. (trm_rep t S)))"
         proof (rule ccontr)
          assume "\<not>(all_trms_irreducible (subst_set (trms_ecl (fst pair')) (snd pair')) 
                  (\<lambda>t. (trm_rep t S)))"
          then obtain t' t'' where "t' \<in> (subst_set (trms_ecl (fst pair')) (snd pair'))" 
            "occurs_in t'' t'" and "trm_rep t'' S \<noteq> t''" unfolding all_trms_irreducible_def by blast
          from `t' \<in> (subst_set (trms_ecl (fst pair')) (snd pair'))` 
            and `(subterms_inclusion (subst_set (trms_ecl (fst pair')) (snd pair')) (trms_ecl R))`
            obtain s' where "s' \<in> (trms_ecl R)" and "occurs_in t' s'" 
            unfolding subterms_inclusion_def by auto
          from `s' \<in> (trms_ecl R)` and `trms_ecl R \<subseteq> (subst_set ((trms_ecl C) \<union> { t }) \<sigma>)` 
            obtain s'' where "s' = subst s'' \<sigma>" and "s'' \<in> ((trms_ecl C) \<union> { t })" by auto
          from `s'' \<in> ((trms_ecl C) \<union> { t })` have "s'' \<in> trms_ecl C \<or> s'' = t" by auto 
          thus False 
          proof 
            assume "s'' \<in> trms_ecl C"
            from this and `s' = subst s'' \<sigma>` have "s' \<in> (subst_set (trms_ecl C) \<sigma>)" by auto
            from this and `(all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) 
                  (\<lambda>t. (trm_rep t S)))` and `occurs_in t' s'` have "trm_rep t' S = t'" 
              unfolding all_trms_irreducible_def by blast
            from this and `occurs_in t'' t'` and `trm_rep t'' S \<noteq> t''`show False
              using occurs_in_def subts_of_irred_trms_are_irred by blast 
          next
            assume "s'' = t"
            from this and `s' = subst s'' \<sigma>` have "s' = subst t \<sigma>" by auto
            from this and `(trm_rep (subst t \<sigma>)  S) =  (subst t \<sigma>)` 
              have "trm_rep s' S = s'" by blast
            from `trm_rep s' S = s'` `trm_rep t'' S \<noteq> t''` `occurs_in t' s'` `occurs_in t'' t'` 
              show False using occurs_in_def subts_of_irred_trms_are_irred by blast 
          qed
         qed
         from `S' \<subseteq> (instances S)` and `pair' \<in> S'` have 
          ii: "ground_clause (subst_cl (cl_ecl (fst pair')) (snd pair'))" 
          unfolding instances_def [of S] by fastforce 
         from `S' \<subseteq> (instances S)` and `pair' \<in> S'` have 
          iii: "(fst pair') \<in> S" unfolding instances_def [of S] by fastforce 
         from `?P pair'` and i ii iii have "validate_ground_clause ?I 
          (subst_cl (cl_ecl (fst pair')) (snd pair'))" unfolding int_clset_def by blast
         from this and `x = (subst_cl (cl_ecl (fst pair')) (snd pair'))` 
          and `\<not>validate_clause ?I x` show False  
          by (metis ii substs_preserve_ground_clause validate_clause.simps) 
        qed
        from this and `fo_interpretation ?I` and 
        `(set_entails_clause (clset_instances S') (cl_ecl R))`
          have "validate_clause ?I (cl_ecl R)" unfolding set_entails_clause_def by blast
        from this have "validate_ground_clause ?I (cl_ecl R)"
          by (metis `R = Ecl Cl_R nt_R` `ground_clause Cl_R` 
            cl_ecl.simps substs_preserve_ground_clause validate_clause.simps) 
        from this obtain L' where "L' \<in> (cl_ecl R)" and "validate_ground_lit ?I L'"
          using validate_ground_clause.simps by blast 
        from `L' \<in> (cl_ecl R)` and `R = Ecl Cl_R nt_R` and
          `Cl_R = (subst_cl ((cl_ecl C) - { L }) \<sigma>)` 
          obtain L'' where "L'' \<in> cl_ecl C" and "L' = subst_lit L'' \<sigma>" 
          by auto
        from `L'' \<in> cl_ecl C` and `L' = subst_lit L'' \<sigma>`and `validate_ground_lit ?I L'`
          have "validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)"
            by (metis (mono_tags, lifting) subst_cl.simps mem_Collect_eq 
              validate_ground_clause.simps)
        from this and cm show False unfolding int_clset_def by blast
      qed

text {* Third, we prove that the clause contains no pair of equations with the same left-hand side
and equivalent right-hand sides (otherwise the factorization rule applies and a smaller false clause
is derived). *}

     let ?no_fact = "\<forall>L1 L2 t s u v. (L1 \<in> (cl_ecl C)) \<longrightarrow> (eligible_literal L1 C \<sigma>) 
       \<longrightarrow> (L2 \<in> (cl_ecl C) - { L1 }) \<longrightarrow> (orient_lit_inst L1 t s pos \<sigma>) 
       \<longrightarrow> (orient_lit_inst L2 u v pos \<sigma>) \<longrightarrow> (subst t \<sigma>) = (subst u \<sigma>)
       \<longrightarrow> (\<not> (proper_subterm_red t S \<sigma>))
       \<longrightarrow> (trm_rep ((subst s) \<sigma>) S) \<noteq>  (trm_rep ((subst v) \<sigma>) S)"
      have ?no_fact
      proof (rule ccontr)
        assume "\<not> ?no_fact"
        then obtain L1 L2 t s u v where l1: "L1 \<in> (cl_ecl C)" and l2: "L2 \<in> (cl_ecl C) - { L1 }" 
       and e1: "(eligible_literal L1 C \<sigma>)" and o1: "(orient_lit_inst L1 t s pos \<sigma>)" 
       and o2: "(orient_lit_inst L2 u v pos \<sigma>)" and e: "(subst t \<sigma>) = (subst u \<sigma>)"
       and "(\<not> (proper_subterm_red t S \<sigma>))"
       and i: "(trm_rep ((subst s) \<sigma>) S) =  (trm_rep ((subst v) \<sigma>) S)"
        by blast
        from e have t: "ck_unifier t u \<sigma> Ground" unfolding ck_unifier_def Unifier_def 
          using "inferences.distinct" by metis
        from `L1 \<in> (cl_ecl C)` o1 `\<not>(validate_ground_clause (int_clset S) (subst_cl (cl_ecl C) \<sigma>))`
          have "trm_rep (subst t \<sigma>) S \<noteq> trm_rep (subst s \<sigma>) S"
          using no_valid_literal by metis
          then have "subst t \<sigma> \<noteq> subst s \<sigma>" by metis

        from `L2 \<in> (cl_ecl C) - { L1 }` have "L2 \<in> (cl_ecl C)" by auto
        from this o2 `\<not>(validate_ground_clause (int_clset S) (subst_cl (cl_ecl C) \<sigma>))`
          have "trm_rep (subst u \<sigma>) S \<noteq> trm_rep (subst v \<sigma>) S"
          using no_valid_literal by metis
          from this and e have "subst t \<sigma> \<noteq> subst v \<sigma>" by metis

        obtain R Cl_R nt_R L' where 
            ntr: "nt_R = (dom_trms Cl_R (subst_set ((trms_ecl C) \<union> (proper_subterms_of t)) \<sigma>))"
            and r: "R = Ecl Cl_R nt_R" 
            and clr: "Cl_R = (subst_cl ( ((cl_ecl C) - { L2 }) \<union> { L' } ) \<sigma>)"
            and l': "L' = Neg (Eq s v)" by auto
        from ntr r l' clr l1 l2 o1 o2 e1 t
        `subst t \<sigma> \<noteq> subst s \<sigma>` `subst t \<sigma> \<noteq> subst v \<sigma>`
        have "factorization C R \<sigma> Ground (((cl_ecl C) - { L2 }) \<union> { L' } )" 
          unfolding factorization_def get_trms_def using inferences.distinct
          by (metis cl_ecl.simps)
         
         from l2 have "(subst_lit L2 \<sigma>) \<in> (subst_cl (cl_ecl C) \<sigma>)" by auto
         from this and `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
          have "vars_of_lit (subst_lit L2 \<sigma>) = {}"
          by auto
         from this and o2 have "vars_of (subst v \<sigma>) = {}" 
          unfolding orient_lit_inst_def using vars_of_lit.simps vars_of_eq.simps by force

         from l1 have "(subst_lit L1 \<sigma>) \<in> (subst_cl (cl_ecl C) \<sigma>)" by auto
         from this and `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
          have "vars_of_lit (subst_lit L1 \<sigma>) = {}" by auto
         from this and o1 have "vars_of (subst s \<sigma>) = {}" 
          unfolding orient_lit_inst_def using vars_of_lit.simps vars_of_eq.simps by force
         from `vars_of (subst v \<sigma>) = {}` and `vars_of (subst s \<sigma>) = {}`
          and l' have "vars_of_lit (subst_lit L' \<sigma>) = {}" by auto 

        from `C \<in> S` and `factorization C R \<sigma> Ground (((cl_ecl C) - { L2 }) \<union> { L' } )` 
          have "derivable R { C } S \<sigma> Ground (((cl_ecl C) - { L2 }) \<union> { L' } )" 
          unfolding derivable_def by auto
        have "ground_clause Cl_R"
        proof (rule ccontr)
          assume "\<not>ground_clause Cl_R"
          then have "vars_of_cl Cl_R \<noteq> {}" by auto
          then obtain M where "M \<in> Cl_R" and "vars_of_lit M \<noteq> {}" by auto
          from `M \<in> Cl_R` and clr obtain M' where "M = (subst_lit M' \<sigma>)" 
          and "M' \<in>((cl_ecl C) - { L2, L1 }) \<union> { L', L1 } "
            by auto
          show False
          proof (cases)
            assume "M' = L'"
            from this and `vars_of_lit (subst_lit L' \<sigma>) = {}` and `vars_of_lit M \<noteq> {}`
              and `M = (subst_lit M' \<sigma>)` show False by auto
          next
            assume "M' \<noteq> L'"
            from this and l1 and `M' \<in>((cl_ecl C) - { L2, L1 }) \<union> { L', L1 }` have "M' \<in> (cl_ecl C)"
              by auto
            from this and `ground_clause (subst_cl (cl_ecl C) \<sigma>)` have 
              "vars_of_lit (subst_lit M' \<sigma>) = {}" by auto
            from this and `M = (subst_lit M' \<sigma>)` and
              `vars_of_lit M \<noteq> {}` show False by auto
          qed
        qed
          
        from `ground_clause Cl_R` and `R = Ecl Cl_R nt_R` have "ground_clause (cl_ecl R)" by auto
        from `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
          have "grounding_set { C } \<sigma>" unfolding grounding_set_def by auto
        from this `ground_clause (cl_ecl R)` 
          and `derivable R { C } S \<sigma> Ground (((cl_ecl C) - { L2 }) \<union> { L' } )` 
          and `ground_inference_saturated S` 
          have "(redundant_inference R S { C } \<sigma>)" unfolding ground_inference_saturated_def 
          by blast
        from this obtain S' where "S' \<subseteq> (instances S)" and 
          "(set_entails_clause (clset_instances S') (cl_ecl R))"
          and all_smaller: "(\<forall>x \<in> S'. (((fst x),(snd x)),(C,\<sigma>)) \<in> ecl_ord)"
          and all_normalized_term_included: "(\<forall>x \<in> S'. 
          (subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x))
            (trms_ecl R)))"
          unfolding redundant_inference_def by auto
        have "validate_clause_set ?I (clset_instances S')"
        proof (rule ccontr)
          assume "\<not> validate_clause_set ?I (clset_instances S')"
          then obtain x where "x \<in>(clset_instances S')" and "\<not>validate_clause ?I x"
            using validate_clause_set.simps by blast
         from `x \<in>(clset_instances S')` obtain pair' where "pair' \<in> S'" 
          and "x = (subst_cl (cl_ecl (fst pair')) (snd pair'))" 
          unfolding clset_instances_def 
          by auto
         from all_smaller and `pair' \<in> S'` have "(pair',(C,\<sigma>)) \<in> ecl_ord"
          by auto
         from this and  `C = fst pair` and `\<sigma> = snd pair` have "(pair',pair) \<in> ecl_ord"
          by auto
         from this and hyp_ind  have "?P pair'" by blast

          from r ntr have "trms_ecl R = (dom_trms (cl_ecl R) 
            (subst_set ((trms_ecl C) \<union> (proper_subterms_of t)) \<sigma>))"
            by auto

         from this have "trms_ecl R \<subseteq> (subst_set ((trms_ecl C) \<union> (proper_subterms_of t)) \<sigma>)"
            using dom_trms_subset by metis

         from `pair' \<in> S'` and all_normalized_term_included have 
          "(subterms_inclusion (subst_set (trms_ecl (fst pair')) (snd pair')) 
             (trms_ecl R))" by auto

         have i: "(all_trms_irreducible (subst_set (trms_ecl (fst pair')) (snd pair')) 
                  (\<lambda>t. (trm_rep t S)))"
         proof (rule ccontr)
          assume "\<not>(all_trms_irreducible (subst_set (trms_ecl (fst pair')) (snd pair')) 
                  (\<lambda>t. (trm_rep t S)))"
          then obtain t' t'' where "t' \<in> (subst_set (trms_ecl (fst pair')) (snd pair'))" 
            "occurs_in t'' t'" and "trm_rep t'' S \<noteq> t''" unfolding all_trms_irreducible_def by blast
          from `t' \<in> (subst_set (trms_ecl (fst pair')) (snd pair'))` 
            and `(subterms_inclusion (subst_set (trms_ecl (fst pair')) (snd pair')) (trms_ecl R))`
            obtain s' where "s' \<in> (trms_ecl R)" and "occurs_in t' s'" 
            unfolding subterms_inclusion_def by auto
          from `s' \<in> (trms_ecl R)` and `trms_ecl R \<subseteq> (subst_set ((trms_ecl C) \<union> (proper_subterms_of t)) \<sigma>)` 
          have "s' \<in>(subst_set ((trms_ecl C) \<union> (proper_subterms_of t)) \<sigma>)" by auto
          then obtain s''
            where "s' = subst s'' \<sigma>" and "s'' \<in> ((trms_ecl C) \<union> (proper_subterms_of t))" by auto
          from `s'' \<in> ((trms_ecl C) \<union> (proper_subterms_of t))` have "s'' \<in> trms_ecl C 
            \<or> s'' \<in> (proper_subterms_of t)" by auto 
          thus False 
          proof 
            assume "s'' \<in> trms_ecl C"
            from this and `s' = subst s'' \<sigma>` have "s' \<in> (subst_set (trms_ecl C) \<sigma>)" by auto
            from this and `(all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) 
                  (\<lambda>t. (trm_rep t S)))` and `occurs_in t' s'` have "trm_rep t' S = t'" 
              unfolding all_trms_irreducible_def by blast
            from this and `occurs_in t'' t'` and `trm_rep t'' S \<noteq> t''`show False
              using occurs_in_def subts_of_irred_trms_are_irred by blast 
          next
            assume " s'' \<in> (proper_subterms_of t)"
            from `occurs_in t' s'` `occurs_in t'' t'` `s' = s'' \<lhd> \<sigma>` `trm_rep t'' S \<noteq> t''`
              have "trm_rep (subst s'' \<sigma>) S \<noteq>  (subst s'' \<sigma>)"
              using occurs_in_def subts_of_irred_trms_are_irred by blast 
            from this and `s'' \<in> (proper_subterms_of t)` and `\<not> (proper_subterm_red t S \<sigma>)`
              show False using proper_subterm_red_def "proper_subterms_of.simps" by blast
          qed
         qed
         from `S' \<subseteq> (instances S)` and `pair' \<in> S'` have 
          ii: "ground_clause (subst_cl (cl_ecl (fst pair')) (snd pair'))" 
          unfolding instances_def [of S] by fastforce 
         from `S' \<subseteq> (instances S)` and `pair' \<in> S'` have 
          iii: "(fst pair') \<in> S" unfolding instances_def [of S] by fastforce 
         from `?P pair'` and i ii iii have "validate_ground_clause ?I 
          (subst_cl (cl_ecl (fst pair')) (snd pair'))"
          unfolding int_clset_def by blast
         from this and `x = (subst_cl (cl_ecl (fst pair')) (snd pair'))` 
          and `\<not>validate_clause ?I x` show False  
          by (metis ii substs_preserve_ground_clause validate_clause.simps) 
        qed
        from this and `fo_interpretation ?I` and 
        `(set_entails_clause (clset_instances S') (cl_ecl R))`
          have "validate_clause ?I (cl_ecl R)" unfolding set_entails_clause_def by blast
        from this have "validate_ground_clause ?I (cl_ecl R)"
          by (metis `R = Ecl Cl_R nt_R` `ground_clause Cl_R` 
            cl_ecl.simps substs_preserve_ground_clause validate_clause.simps) 
        from this obtain L'' where "L'' \<in> (cl_ecl R)" and "validate_ground_lit ?I L''"
          using validate_ground_clause.simps by blast 
        from `L'' \<in> (cl_ecl R)` and `R = Ecl Cl_R nt_R` and
          `Cl_R = (subst_cl ( ((cl_ecl C) - { L2 }) \<union> { L' } ) \<sigma>)` 
          obtain M where m: "M \<in> ( ((cl_ecl C) - { L2, L1 }) \<union> { L', L1 } )" 
          and "L'' = subst_lit M \<sigma>" 
          by auto
        have "M \<in> cl_ecl C"
        proof (rule ccontr)
          assume "M \<notin> cl_ecl C"
          from this and m and l1 have "M = L'" by auto
          from this and `L'' = subst_lit M \<sigma>` and `L' = (Neg (Eq s v))`
            have "L'' = (Neg (Eq (subst s \<sigma>)  (subst v \<sigma>)))" by auto
          from this and `validate_ground_lit ?I L''` 
            have "\<not>(?I (subst s \<sigma>) (subst v \<sigma>))" 
                using validate_ground_lit.simps(2) validate_ground_eq.simps by metis
            from this and i show False unfolding same_values_def int_clset_def by blast
        qed
        from `M \<in> cl_ecl C` and `L'' = subst_lit M \<sigma>`and `validate_ground_lit ?I L''`
          have "validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)"
            by (metis (mono_tags, lifting) subst_cl.simps mem_Collect_eq 
              validate_ground_clause.simps)
        from this and cm show False by blast
      qed
      
text {* Now, it remains to prove that the considered clause yields a rule which can be used to 
reduce the left-hand side of the maximal equation, which (since no reduction is possible)
entails that the left-hand side must be equivalent to the right-hand side 
(thus contradicting the fact that the clause is false). *}

       have "(finite (cl_ecl C))" by (simp add: `C \<in> S` all_finite) 
       have "(cl_ecl C) \<noteq> {}"  by (simp add: `C \<in> S` all_non_empty) 
       from `finite (cl_ecl C)` `(cl_ecl C) \<noteq> {}` `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
        obtain L where "L \<in> (cl_ecl C)" "eligible_literal L C \<sigma>" using eligible_lit_exists by metis
       obtain t s p where "orient_lit_inst L t s p \<sigma>" using literal.exhaust equation.exhaust  
         using trm_ord_irrefl trm_ord_trans
         unfolding orient_lit_inst_def irrefl_def trans_def by metis

text {* We first show that the terms occurring inside variables are irreducible. To this aim, 
we need to consider the normal form of the substitution @{term "\<sigma>"}, obtained by replacing the 
image of each variable by its normal form. *}

       have "\<forall>x y. 
        ((x \<in> vars_of_cl (cl_ecl C)) \<longrightarrow> occurs_in y (subst (Var x) \<sigma>) \<longrightarrow> trm_rep y S = y)"  
       proof (rule ccontr)
        assume "\<not>(\<forall>x y. (x \<in> vars_of_cl (cl_ecl C)) \<longrightarrow> occurs_in y (subst (Var x) \<sigma>) \<longrightarrow> trm_rep y S = y)"
        then obtain x y where "(x \<in> vars_of_cl (cl_ecl C))" and
          "occurs_in y (subst (Var x) \<sigma>)" and "trm_rep y S \<noteq> y" by blast
        from `occurs_in y (subst (Var x) \<sigma>)` obtain p where "subterm (subst (Var x) \<sigma>) p y" 
          unfolding occurs_in_def by auto
        from `subterm (subst (Var x) \<sigma>) p y` and `trm_rep y S \<noteq> y` 
          have "trm_rep (subst (Var x) \<sigma>) S \<noteq> (subst (Var x) \<sigma>)" 
          using subts_of_irred_trms_are_irred by blast

        let ?\<theta> = "map_subst (\<lambda>x. (trm_rep x S)) \<sigma>"
        have "equivalent_on \<sigma> ?\<theta> (vars_of_cl (cl_ecl C)) ?I"
        proof (rule ccontr)
          assume "\<not>equivalent_on \<sigma> ?\<theta> (vars_of_cl (cl_ecl C)) ?I"
          then obtain z where "z \<in> vars_of_cl (cl_ecl C)" 
            and "\<not> (?I (subst (Var z) \<sigma>)  (subst (Var z) ?\<theta>))"
            unfolding equivalent_on_def by blast
          from `\<not> (?I (subst (Var z) \<sigma>)  (subst (Var z) ?\<theta>))`
            have "trm_rep (subst (Var z) \<sigma>) S \<noteq> trm_rep (subst (Var z) ?\<theta>) S"
            unfolding same_values_def int_clset_def by blast
          from this have "trm_rep (trm_rep (subst (Var z) \<sigma>) S) S \<noteq> trm_rep (subst (Var z) ?\<theta>) S"
            using trm_rep_involutive by metis
          from this have "(subst (Var z) \<sigma>) = (subst (Var z) ?\<theta>)" 
            using map_subst_lemma [of z \<sigma> "\<lambda>x. (trm_rep x S)"] by metis
          from this and `\<not> (?I (subst (Var z) \<sigma>)  (subst (Var z) ?\<theta>))` 
            show False using `fo_interpretation ?I` 
            unfolding fo_interpretation_def congruence_def equivalence_relation_def reflexive_def 
            by metis 
        qed
        from this and `\<not> validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)`
          `fo_interpretation ?I`
          have "\<not> validate_ground_clause ?I (subst_cl (cl_ecl C) ?\<theta>)"
          using equivalent_on_cl by metis
        have "lower_on ?\<theta> \<sigma> (vars_of_cl (cl_ecl C))"
        proof (rule ccontr)
          assume "\<not>lower_on ?\<theta> \<sigma> (vars_of_cl (cl_ecl C))"
          then obtain z where "z \<in> vars_of_cl (cl_ecl C)" 
            and "(subst (Var z) \<sigma>) \<noteq> (subst (Var z) ?\<theta>)"
            and "((subst (Var z) ?\<theta>),(subst (Var z) \<sigma>)) \<notin> trm_ord"
            unfolding lower_on_def lower_or_eq_def by metis
          from `(subst (Var z) \<sigma>) \<noteq> (subst (Var z) ?\<theta>)` have 
            "(trm_rep (subst (Var z) \<sigma>) S) = (subst (Var z) ?\<theta>)" 
             using map_subst_lemma [of z \<sigma> "\<lambda>x. (trm_rep x S)"] by metis
          from this and `(subst (Var z) \<sigma>) \<noteq> (subst (Var z) ?\<theta>)` 
            and `((subst (Var z) ?\<theta>),(subst (Var z) \<sigma>)) \<notin> trm_ord`
              show False using trm_rep_is_lower by metis 
        qed
        have "subst (Var x) \<sigma> \<noteq> (Var x)"
        proof 
          assume "subst (Var x) \<sigma> = (Var x)"
          from this and `x \<in> vars_of_cl (cl_ecl C)` have "\<not> (ground_on (vars_of_cl (cl_ecl C)) \<sigma>)"
            unfolding ground_on_def ground_term_def by auto
          from this and `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
            show False using ground_clauses_and_ground_substs by metis
        qed
        from `subst (Var x) \<sigma> \<noteq> (Var x)` 
          have "(trm_rep (subst (Var x) \<sigma>) S) = (subst (Var x) ?\<theta>)" 
             using map_subst_lemma [of x \<sigma> "\<lambda>x. (trm_rep x S)"] by metis
        from this and `trm_rep (subst (Var x) \<sigma>) S \<noteq> (subst (Var x) \<sigma>)`
          have "((subst (Var x) ?\<theta>),(subst (Var x) \<sigma>)) \<in> trm_ord"
          using trm_rep_is_lower by metis
        from `lower_on ?\<theta> \<sigma> (vars_of_cl (cl_ecl C))` and `x \<in> vars_of_cl (cl_ecl C)` 
          `finite (cl_ecl C)` 
          and `((subst (Var x) ?\<theta>),(subst (Var x) \<sigma>)) \<in> trm_ord`    
        have "((C,?\<theta>), (C, \<sigma>)) \<in> ecl_ord"
          using lower_on_cl by blast
        from `C = fst pair` `\<sigma> = snd pair` have "pair = (C,\<sigma>)" by auto
        from this  and `((C,?\<theta>), (C, \<sigma>)) \<in> ecl_ord` have 
          "((C,?\<theta>),pair) \<in> ecl_ord"
          by metis
         from this and hyp_ind  have "?P (C,?\<theta>)" by blast
         from `(all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) 
                  (\<lambda>t. (trm_rep t S)))`
              `lower_on ?\<theta> \<sigma> (vars_of_cl (cl_ecl C))` `C \<in> S` `fo_interpretation ?I`
              `equivalent_on \<sigma> ?\<theta> (vars_of_cl (cl_ecl C)) ?I` assms(3)
             have "(all_trms_irreducible (subst_set (trms_ecl C) ?\<theta>) 
                  (\<lambda>t. (trm_rep t S)))" 
                  using irred_terms_and_reduced_subst unfolding Ball_def well_constrained_def 
                  by metis
         have "ground_clause (subst_cl (cl_ecl C) ?\<theta>)" 
         proof -
          from `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
            have "ground_on (vars_of_cl (cl_ecl C)) \<sigma>" using ground_clauses_and_ground_substs by auto
          from this and `lower_on ?\<theta> \<sigma> (vars_of_cl (cl_ecl C))` 
            have "ground_on (vars_of_cl (cl_ecl C)) ?\<theta>"
            using lower_on_ground by meson
          from this show ?thesis using ground_substs_yield_ground_clause by metis
         qed
         from this 
          `(all_trms_irreducible (subst_set (trms_ecl C) ?\<theta>) (\<lambda>t. (trm_rep t S)))` 
          `?P (C,?\<theta>)` `\<not> validate_ground_clause ?I (subst_cl (cl_ecl C) ?\<theta>)` 
          `C \<in> S` show False unfolding int_clset_def by (metis fst_conv snd_conv) 
       qed

text {* Next, we show that the eligible term @{term "t"} is in normal form. 
We first need to establish the result for proper subterms of @{term "t"} before considering 
the general case. *}

    have "\<not>(proper_subterm_red t S \<sigma>)"
       proof 
        assume "(proper_subterm_red t S \<sigma>)"
        from this have "trm_rep (subst t \<sigma>) S \<noteq> subst t \<sigma>" 
          using proper_subterm_red_def substs_preserve_subterms subts_of_irred_trms_are_irred 
          by blast 

        from `(proper_subterm_red t S \<sigma>)`
          `\<forall>x y. 
        ((x \<in> vars_of_cl (cl_ecl C)) \<longrightarrow> occurs_in y (subst (Var x) \<sigma>) \<longrightarrow> trm_rep y S = y)` 
        `eligible_literal L C \<sigma>`
        `trm_rep (subst t \<sigma>) S \<noteq> subst t \<sigma>` `L \<in> cl_ecl C` 
        `orient_lit_inst L t s p \<sigma>` `\<forall>x\<in>S. finite (cl_ecl x)` 
        `ground_clause (subst_cl (cl_ecl C) \<sigma>)`
        `fo_interpretation (int_clset S)` 
        `Ball S well_constrained` `C \<in> S`
        `all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. trm_rep t S)`
        `\<not> validate_ground_clause (int_clset S) (subst_cl (cl_ecl C) \<sigma>)`
        `closed_under_renaming S`
            have "
            \<exists>\<sigma>'' u u' pa v D L2. (reduction L C \<sigma>'' t s p L2 u u' pa v D 
              (same_values (\<lambda>t. trm_rep t S)) S \<sigma> \<and> variable_disjoint C D)" 
             using reduction_exists [of p t s C S \<sigma> L] unfolding int_clset_def by blast
        from this and `?nored` show False unfolding int_clset_def  by blast
      qed

       have "p = neg \<or> \<not> equivalent_eq_exists t s (cl_ecl C) (same_values (\<lambda>x. trm_rep x S)) \<sigma>
        L" 
       proof (rule ccontr) 
          assume neg: "\<not> (p = neg \<or> \<not> equivalent_eq_exists t s (cl_ecl C) 
            (same_values (\<lambda>x. trm_rep x S)) \<sigma> L)"
          then have "p \<noteq> neg" by metis
          from neg have "equivalent_eq_exists t s (cl_ecl C) (same_values (\<lambda>x. trm_rep x S)) \<sigma> L" 
            by metis
          from `p \<noteq> neg` have "p = pos" using sign.exhaust by auto
          from `equivalent_eq_exists t s (cl_ecl C) (same_values (\<lambda>x. trm_rep x S)) \<sigma> L` 
            obtain L2 where "L2 \<in> (cl_ecl C) - { L }" and f:"\<exists>u v. orient_lit_inst L2 u v pos \<sigma> \<and>
                subst t \<sigma> = subst u \<sigma> \<and> trm_rep (subst s \<sigma>) S = trm_rep (subst v \<sigma>) S"     
            unfolding equivalent_eq_exists_def unfolding same_values_def by metis 
          from f obtain u v where f': "orient_lit_inst L2 u v pos \<sigma> \<and> subst t \<sigma> = subst u \<sigma> 
            \<and> trm_rep (subst s \<sigma>) S = trm_rep (subst v \<sigma>) S"
           by blast
          from f' have "orient_lit_inst L2 u v pos \<sigma>"  by metis
          from f' have "subst t \<sigma> = subst u \<sigma>" by metis
          from f' have "trm_rep (subst s \<sigma>) S = trm_rep (subst v \<sigma>) S" by metis
          from `orient_lit_inst L2 u v pos \<sigma>` `subst t \<sigma> = subst u \<sigma>`  
            `trm_rep (subst s \<sigma>) S = trm_rep (subst v \<sigma>) S` 
            `orient_lit_inst L t s p \<sigma>` `p = pos` `L \<in> (cl_ecl C)` `L2 \<in> (cl_ecl C) - { L }`
            `eligible_literal L C \<sigma>`
           `\<not>(proper_subterm_red t S \<sigma>)`
            and `?no_fact` show False by blast
       qed

    have "(trm_rep (subst t \<sigma>) S) = (subst t \<sigma>)"
    proof (rule ccontr)
        assume "(trm_rep (subst t \<sigma>) S) \<noteq>  (subst t \<sigma>)"

        from `p = neg \<or> \<not> equivalent_eq_exists t s (cl_ecl C) (same_values (\<lambda>x. trm_rep x S)) \<sigma> L` 
          `\<forall>x y. 
        ((x \<in> vars_of_cl (cl_ecl C)) \<longrightarrow> occurs_in y (subst (Var x) \<sigma>) \<longrightarrow> trm_rep y S = y)` 
        `eligible_literal L C \<sigma>`
        `trm_rep (subst t \<sigma>) S \<noteq> subst t \<sigma>` `L \<in> cl_ecl C` 
        `orient_lit_inst L t s p \<sigma>` `\<forall>x\<in>S. finite (cl_ecl x)` 
        `ground_clause (subst_cl (cl_ecl C) \<sigma>)`
        `fo_interpretation (int_clset S)` 
        `Ball S well_constrained` `C \<in> S`
        `all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. trm_rep t S)`
        `\<not> validate_ground_clause (int_clset S) (subst_cl (cl_ecl C) \<sigma>)`
        `closed_under_renaming S`
            have "
            \<exists>\<sigma>'' u u' pa v D L2. (reduction L C \<sigma>'' t s p L2 u u' pa v D 
              (same_values (\<lambda>t. trm_rep t S)) S \<sigma> \<and> variable_disjoint C D)" 
             using reduction_exists [of p t s C S \<sigma> L] unfolding int_clset_def by blast
        from this and `?nored` show False unfolding int_clset_def  by blast
      qed

      from `orient_lit_inst L t s p \<sigma>` have "((subst t \<sigma>),(subst s \<sigma>)) \<notin> trm_ord" 
          unfolding orient_lit_inst_def by auto
      from `ground_clause (subst_cl (cl_ecl C) \<sigma>)` 
          have "vars_of_cl (subst_cl (cl_ecl C) \<sigma>) = {}" by auto  
      from this and `L \<in> (cl_ecl C)` have "vars_of_lit (subst_lit L \<sigma>) = {}" by auto
      from `orient_lit_inst L t s p \<sigma>` 
          have "orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) p" 
          using lift_orient_lit by auto
      from  `orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) p` 
          have "vars_of (subst t \<sigma>) \<subseteq> vars_of_lit  (subst_lit L \<sigma>)" 
          using  orient_lit_vars by auto
      from this and `vars_of_lit (subst_lit L \<sigma>) = {}` have "vars_of (subst t \<sigma>) = {}" 
          by auto
      from  `orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) p` 
          have "vars_of (subst s \<sigma>) \<subseteq> vars_of_lit  (subst_lit L \<sigma>)" 
          using  orient_lit_vars by auto
      from this and `vars_of_lit (subst_lit L \<sigma>) = {}` have "vars_of (subst s \<sigma>) = {}" 
          by auto
      from
          `((subst t \<sigma>),(subst s \<sigma>)) \<notin> trm_ord`
          `vars_of (subst t \<sigma>) = {}` `vars_of (subst s \<sigma>) = {}`
          have "(subst t \<sigma>) = (subst s \<sigma>) \<or> ((subst s \<sigma>),(subst t \<sigma>)) \<in> trm_ord" 
          using trm_ord_ground_total unfolding ground_term_def by blast

      from  `L \<in> (cl_ecl C)` have "(subst_lit L \<sigma>) \<in> (subst_cl (cl_ecl C) \<sigma>)" by auto

text {* Using the fact that the eligible term is in normal form and that the eligible literal
is false in the considered interpretation but is not a contradiction, we deduce that this literal 
must be positive. *}

      have "p = pos"
      proof (rule ccontr)
        assume "p \<noteq> pos"
        from this have "p = neg" using sign.exhaust by auto
        from `trm_rep (subst t \<sigma>) S =  (subst t \<sigma>)` `L \<in> (cl_ecl C)` `eligible_literal L C \<sigma>` 
          and `orient_lit_inst L t s p \<sigma>` `p = neg` `?no_cont` 
          have "(subst t \<sigma>) \<noteq> (subst s \<sigma>)" by blast
        from this and
           `(subst t \<sigma>) = (subst s \<sigma>) \<or> ((subst s \<sigma>),(subst t \<sigma>)) \<in> trm_ord`
          and `trm_rep (subst t \<sigma>) S = subst t \<sigma>`
          have "((trm_rep (subst s \<sigma>) S),(trm_rep (subst t \<sigma>) S)) \<in> trm_ord"
          using trm_rep_is_lower [of " (subst s \<sigma>)" S ] trm_ord_trans unfolding trans_def
            by metis
        from this have "(trm_rep (subst s \<sigma>) S) \<noteq> (trm_rep (subst t \<sigma>) S)"
          using trm_ord_irrefl irrefl_def by metis
        
        from this have "\<not>validate_ground_eq ?I (Eq (subst t \<sigma>) (subst s \<sigma>))"
          unfolding same_values_def int_clset_def using validate_ground_eq.simps 
          by (metis (mono_tags, lifting)) 
        from `(trm_rep (subst s \<sigma>) S) \<noteq> (trm_rep (subst t \<sigma>) S)` 
          have "\<not>validate_ground_eq ?I (Eq (subst s \<sigma>) (subst t \<sigma>))"
          unfolding same_values_def  int_clset_def using validate_ground_eq.simps 
          by (metis (mono_tags, lifting)) 
        from `orient_lit_inst L t s p \<sigma>` and `p=neg` have "L = (Neg (Eq t s)) \<or> L = (Neg (Eq s t))"
          unfolding orient_lit_inst_def by auto
        from this have "subst_lit L \<sigma> = (Neg (Eq (subst t \<sigma>)  (subst s \<sigma>))) 
          \<or> subst_lit L \<sigma> = (Neg (Eq (subst s \<sigma>)  (subst t \<sigma>)))" by auto
        from this and `\<not>validate_ground_eq ?I (Eq (subst s \<sigma>) (subst t \<sigma>))` 
          and `\<not>validate_ground_eq ?I (Eq (subst t \<sigma>) (subst s \<sigma>))` 
          have "validate_ground_lit ?I (subst_lit L \<sigma>)" using validate_ground_lit.simps(2) by metis
        
        from `(subst_lit L \<sigma>) \<in> (subst_cl (cl_ecl C) \<sigma>)` 
          and `validate_ground_lit ?I (subst_lit L \<sigma>)` 
          have "validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)"
          using validate_ground_clause.elims(3) by blast 
                   
        from this and `\<not> validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)` show False by blast
      qed

text {* This entails that the right-hand side of the eligible literal occurs in the set of 
possible values for the left-hand side @{term "t"}, which is impossible since this term is 
irreducible. *}

     from `L \<in> (cl_ecl C)` `orient_lit_inst L t s p \<sigma>` `p = pos` 
      `\<not> validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)` 
      have "trm_rep (subst t \<sigma>) S \<noteq> trm_rep (subst s \<sigma>) S"
      using no_valid_literal by metis

     from this have "(subst t \<sigma>) \<noteq> (subst s \<sigma>)" by metis
     from this and `(subst t \<sigma>) = (subst s \<sigma>) \<or> ((subst s \<sigma>),(subst t \<sigma>)) \<in> trm_ord`
          have "((subst s \<sigma>),(subst t \<sigma>)) \<in> trm_ord" 
          using trm_ord_ground_total unfolding ground_term_def by blast
     from `p=pos` and `orient_lit_inst L t s p \<sigma>` have "\<not>negative_literal L" 
          unfolding  orient_lit_inst_def by auto 
     from this and `eligible_literal L C \<sigma>`  
          have "sel(cl_ecl C) = {}" and "maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>)" 
          using sel_neg unfolding eligible_literal_def by auto
     
     from `\<not> validate_ground_clause ?I (subst_cl (cl_ecl C) \<sigma>)` 
      have "smaller_lits_are_false (subst t \<sigma>) (subst_cl (cl_ecl C) \<sigma>) S" 
          using smaller_lits_are_false_if_cl_not_valid [of S "(subst_cl (cl_ecl C) \<sigma>)" ] by blast
     from `p = pos` and `p = neg \<or> \<not> equivalent_eq_exists t s (cl_ecl C) 
                          (same_values (\<lambda>x. trm_rep x S)) \<sigma> L` 
        have "\<not> equivalent_eq_exists t s (cl_ecl C) (int_clset S) \<sigma> L" unfolding int_clset_def
        using sign.distinct by metis
     from this `p=pos` have "maximal_literal_is_unique (subst t \<sigma>) (subst s \<sigma>) (cl_ecl C) L S \<sigma>" 
          using maximal_literal_is_unique_lemma [of t s "(cl_ecl C)" S \<sigma> L]  by blast
     from `all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. trm_rep t S)` 
          have "trms_irreducible C \<sigma> S (subst t \<sigma>)" 
          using trms_irreducible_lemma  by blast

     have "(subst t \<sigma>) \<notin> subst_set (trms_ecl C) \<sigma>"
     proof
      assume "(subst t \<sigma>) \<in> subst_set (trms_ecl C) \<sigma>"
      from this obtain t' where "t' \<in> trms_ecl C" and "(subst t' \<sigma>) = (subst t \<sigma>)" by auto
      from `t' \<in> trms_ecl C` and assms(3) and `C \<in> S` have "dom_trm t' (cl_ecl C)" 
        unfolding Ball_def well_constrained_def by auto
      from this obtain M u v q where "M \<in> (cl_ecl C)" "decompose_literal M u v q" and 
        "q = neg \<and> (u = t') \<or> ( (t',u) \<in> trm_ord)" unfolding dom_trm_def by blast
       obtain u' v' q' where "orient_lit_inst M u' v' q' \<sigma>" using literal.exhaust equation.exhaust  
         using trm_ord_irrefl trm_ord_trans
         unfolding orient_lit_inst_def irrefl_def trans_def by metis
       from `decompose_literal M u v q` and `orient_lit_inst M u' v' q' \<sigma>`
        have "u = u' \<or> u = v'"
        unfolding decompose_literal_def orient_lit_inst_def
          by (metis atom.simps(2) decompose_equation_def equation.inject literal.distinct(1) 
              literal.inject(1))  
       from `decompose_literal M u v q` and `orient_lit_inst M u' v' q' \<sigma>`
        have "q = q'"
        unfolding decompose_literal_def orient_lit_inst_def by auto 
      from `vars_of_cl (subst_cl (cl_ecl C) \<sigma>) = {}` and `M \<in> (cl_ecl C)` 
          have "vars_of_lit (subst_lit M \<sigma>) = {}" by auto
      from `orient_lit_inst M u' v' q' \<sigma>` have 
          "orient_lit (subst_lit M \<sigma>) (subst u' \<sigma>) (subst v' \<sigma>) q'" 
          using lift_orient_lit by auto
      from `orient_lit_inst L t s p \<sigma>` have 
          "orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) p" 
          using lift_orient_lit by auto
      have "(t',u) \<notin> trm_ord"
      proof 
        assume "(t',u) \<in> trm_ord"
        then have "((subst t' \<sigma>),(subst u \<sigma>)) \<in> trm_ord" 
          using trm_ord_subst by auto
        from this and `(subst t' \<sigma>) = (subst t \<sigma>)` have 
          "((subst t \<sigma>),(subst u \<sigma>)) \<in> trm_ord" by auto
        from `orient_lit (subst_lit M \<sigma>) (subst u' \<sigma>) (subst v' \<sigma>) q'`
          and `orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) p` 
          and `((subst t \<sigma>),(subst u \<sigma>)) \<in> trm_ord`
          and `vars_of_lit (subst_lit M \<sigma>) = {}`
          and `vars_of_lit (subst_lit L \<sigma>) = {}`
          and `u = u' \<or> u = v'` 
          have "((subst_lit L \<sigma>),(subst_lit M \<sigma>)) \<in> lit_ord" 
          using lit_ord_dominating_term by metis
        from this and `maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>)`
          and `M \<in> (cl_ecl C)` show False using maximal_literal_def by auto 
      qed
      have "\<not> (q = neg \<and> (u = t'))"
      proof 
        assume "q = neg \<and> (u = t')"
        then have "q = neg" and "u = t'" by auto
        from `orient_lit (subst_lit M \<sigma>) (subst u' \<sigma>) (subst v' \<sigma>) q'`
          and `orient_lit (subst_lit L \<sigma>) (subst t \<sigma>) (subst s \<sigma>) p` 
          and `u = t'`
          and `(subst t' \<sigma>) = (subst t \<sigma>)`
          and `q = neg` and `q = q'`
          and `p = pos`
          and `vars_of_lit (subst_lit M \<sigma>) = {}`
          and `vars_of_lit (subst_lit L \<sigma>) = {}`
          and `u = u' \<or> u = v'` 
          have "((subst_lit L \<sigma>),(subst_lit M \<sigma>)) \<in> lit_ord" 
          using lit_ord_neg_lit_lhs lit_ord_neg_lit_rhs by metis
        from this and `maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>)`
          and `M \<in> (cl_ecl C)` show False using maximal_literal_def by auto 
      qed
      from this and `(t',u) \<notin> trm_ord` and `q = neg \<and> (u = t') \<or> ( (t',u) \<in> trm_ord)`
        show False by auto
     qed

     from `C \<in> S` `(subst s \<sigma>, subst t \<sigma>) \<in> trm_ord` 
          and `p=pos` `orient_lit_inst L t s p \<sigma>` and `sel (cl_ecl C) = {}` 
          and `L \<in> cl_ecl C` 
          and `maximal_literal (subst_lit L \<sigma>) (subst_cl (cl_ecl C) \<sigma>)`
          and `ground_clause (subst_cl (cl_ecl C) \<sigma>)`  
          and `finite (cl_ecl C)` 
          and `smaller_lits_are_false (subst t \<sigma>) (subst_cl (cl_ecl C) \<sigma>) S` 
          and `maximal_literal_is_unique  (subst t \<sigma>) (subst s \<sigma>) (cl_ecl C) L S \<sigma>`
          and `trms_irreducible C \<sigma> S  (subst t \<sigma>)`
          and `(subst t \<sigma>) \<notin> subst_set (trms_ecl C) \<sigma>`
          have cv: "(candidate_values (trm_rep (subst s \<sigma>) S) C (cl_ecl C) 
          (subst_cl (cl_ecl C) \<sigma>) (subst s \<sigma>) (subst_lit L \<sigma>) L \<sigma> t s (subst t \<sigma>) S)"
            unfolding candidate_values_def by blast
          from cv have "(trm_rep (subst s \<sigma>) S,(subst s \<sigma>)) \<in> set_of_candidate_values S (subst t \<sigma>)" 
            unfolding set_of_candidate_values_def by blast 
  
      from `trm_rep (subst t \<sigma>) S = (subst t \<sigma>)` 
        have "\<not>(subterm_reduction_applicable S (subst t \<sigma>))" 
        using trm_rep_is_lower_subt_red trm_ord_irrefl irrefl_def
        by metis
      
      from `(trm_rep (subst s \<sigma>) S, subst s \<sigma>) 
              \<in> set_of_candidate_values S (subst t \<sigma>)` 
              have "set_of_candidate_values S (subst t \<sigma>) \<noteq> {}"  by blast

      from `(trm_rep (subst s \<sigma>) S, subst s \<sigma>) 
              \<in> set_of_candidate_values S (subst t \<sigma>)` 
              have "min_trms (set_of_candidate_values S (subst t \<sigma>)) \<noteq> {}"
              using min_trms_not_empty by blast

      from `\<not>(subterm_reduction_applicable S (subst t \<sigma>))`
        `min_trms (set_of_candidate_values S (subst t \<sigma>)) \<noteq> {}` 
                have "(trm_rep (subst t \<sigma>) S,(subst t \<sigma>)) \<in> trm_ord"
                using trm_rep_is_lower_root_red [of S "subst t \<sigma>"] by blast
      from this and `(trm_rep (subst t \<sigma>) S) = (subst t \<sigma>)` 
       show False using trm_ord_irrefl irrefl_def by metis
 qed
qed

text {* As an immediate consequence of the previous lemma, we show that the set of clauses that 
are derivable from an unsatisfiable clause set must contain an empty clause (since this set is
trivially saturated). *}

lemma COMPLETENESS:
  assumes "\<forall>x. (x \<in> S \<longrightarrow> (trms_ecl x = {}))"
  assumes "(\<forall>x\<in>S. finite (cl_ecl x))"
  assumes "\<not> (satisfiable_clause_set (cl_ecl ` S))"
  shows "\<exists>x. (derivable_ecl x S) \<and> cl_ecl x = {}"
proof (rule ccontr)
  assume "\<not> (\<exists>x. (derivable_ecl x S) \<and> cl_ecl x = {})"
  let ?S = "{ y. (derivable_ecl y S) }"
  let ?I = "same_values (\<lambda>x. (trm_rep x ?S))"
  have "fo_interpretation ?I" using trm_rep_compatible_with_structure same_values_fo_int 
      by metis

  have "\<forall>x \<in> ?S. (cl_ecl x) \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain x where "x \<in> ?S" and "cl_ecl x = {}" by blast
    from `x \<in> ?S` have "derivable_ecl x S" by (meson CollectD) 
    from this  `cl_ecl x = {}` `\<not> (\<exists>x. (derivable_ecl x S) \<and> cl_ecl x = {})` 
      show False  by metis
  qed
  have all_finite: "\<forall>x \<in> ?S. (finite (cl_ecl x))"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain x where "x \<in> ?S" and "\<not> finite (cl_ecl x)" by blast
    from `x \<in> ?S` have "derivable_ecl x S" by (meson CollectD) 
    from this assms(2) `\<not> finite (cl_ecl x)` show False  using all_derived_clauses_are_finite by metis
  qed
  have "Ball S well_constrained"
  proof 
    fix x assume "x \<in> S"
    from this assms(1) have "trms_ecl x = {}" by auto
    from this show "well_constrained x" unfolding well_constrained_def by blast
  qed
  have "Ball ?S well_constrained"
  proof 
    fix x assume "x \<in> ?S"
    from this have "derivable_ecl x S" by (meson CollectD) 
    from this assms(2) `Ball S well_constrained` show "well_constrained x" 
      using all_derived_clauses_are_wellconstrained 
      by metis
  qed
  have "closed_under_renaming ?S"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain C D  where "C \<in> ?S" "renaming_cl C D" "D \<notin> ?S" 
      unfolding closed_under_renaming_def by metis
    from `C \<in> ?S` have "derivable_ecl C S" by (meson CollectD) 
    from `derivable_ecl C S` `renaming_cl C D` have "(derivable_ecl D S)" 
      using derivable_ecl.intros(2) by metis
    from this and `D \<notin> ?S` show False by blast 
  qed
  have "inference_closed ?S"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain D P \<theta> C' where "(derivable D P ?S \<theta> FirstOrder C')" "D \<notin> ?S" 
      unfolding inference_closed_def by metis
    from `derivable D P ?S \<theta> FirstOrder C'` have "P \<subseteq> ?S" using derivable_premisses by metis
    have "\<forall>x. x \<in> P \<longrightarrow> derivable_ecl x S"
    proof ((rule allI),(rule impI)) 
      fix x assume "x \<in> P"
      from this and `P \<subseteq> ?S` have "x \<in> ?S" by (meson set_rev_mp)
      from this show "derivable_ecl x S" by (meson CollectD) 
    qed
    from this and `(derivable D P ?S \<theta> FirstOrder C')` have "derivable_ecl D S" 
        using derivable_ecl.intros(3) [of P S D ?S \<theta> C'] by meson
    from this and `D \<notin> ?S`  show False by blast
  qed
  from this all_finite have "clause_saturated ?S"
    using inference_closed_sets_are_saturated by meson
  from this all_finite have "inference_saturated ?S" 
    using clause_saturated_and_inference_saturated by meson
  from this have "ground_inference_saturated ?S" 
    using lift_inference by metis
  have "validate_clause_set ?I (cl_ecl ` S)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    from this obtain Cl_C where clc: "Cl_C \<in> (cl_ecl ` S)" and "\<not> (validate_clause ?I Cl_C)"
      using validate_clause_set.simps by metis
    from clc  obtain C where "C \<in> S" and "Cl_C = (cl_ecl C)" by blast
    from `C \<in> S` have "derivable_ecl C S"
      using derivable_ecl.intros(1) by metis
    from this have "C \<in> ?S" by blast
    from `\<not> (validate_clause ?I Cl_C)` obtain \<sigma>
      where "\<not> (validate_ground_clause ?I (subst_cl Cl_C \<sigma>))"
        and "ground_clause (subst_cl Cl_C \<sigma>)"
      using validate_clause.simps by metis
    let ?pair = "(C,\<sigma>)"
    have "fst ?pair = C" by auto
    have "snd ?pair = \<sigma>" by auto

    from `C \<in> S` assms(1) have "trms_ecl C = {}" by auto
    then have "(subst_set (trms_ecl C) \<sigma>) = {}" by auto
    then have n: "all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) 
                  (\<lambda>t. trm_rep t {y. derivable_ecl y S})"
        unfolding all_trms_irreducible_def by blast

    from `ground_inference_saturated ?S` all_finite `Ball ?S well_constrained` 
      `closed_under_renaming ?S` `\<forall>x \<in> ?S. (cl_ecl x) \<noteq> {}`
    have "\<forall>C \<sigma>. fst ?pair = C \<longrightarrow>
           \<sigma> = snd ?pair \<longrightarrow>
           C \<in> {y. derivable_ecl y S} \<longrightarrow>
           ground_clause (subst_cl (cl_ecl C) \<sigma>) \<longrightarrow>
           all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. trm_rep t {y. derivable_ecl y S}) 
           \<longrightarrow> validate_ground_clause ?I  (subst_cl (cl_ecl C) \<sigma>)"
          using int_clset_is_a_model [of ?S ?pair] by blast
    from this `fst ?pair = C` `C \<in> ?S` `snd ?pair = \<sigma>` `Cl_C = (cl_ecl C)` 
        `ground_clause (subst_cl Cl_C \<sigma>)` n
      have "validate_ground_clause ?I  (subst_cl (cl_ecl C) \<sigma>)" by metis
     from this and `\<not> (validate_ground_clause ?I (subst_cl Cl_C \<sigma>))` `Cl_C = (cl_ecl C)` 
      show False by metis
  qed
  from this and assms(3) `fo_interpretation ?I` show False using satisfiable_clause_set_def by metis
qed

end

end
