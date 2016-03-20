(* N. Peltier. LIG/CNRS http://membres-lig.imag.fr/peltier/ *)

section {* Syntax of Propositional Clausal Logic *}

text {* We define the usual syntactic notions of clausal propositional logic.
The set of atoms may be arbitrary (even uncountable), but a well-founded total order is assumed 
to be given. *}

theory Propositional_Resolution

imports Main Finite_Set

begin

locale propositional_atoms =
  fixes atom_ordering :: "('at \<times> 'at) set" 
  assumes
        atom_ordering_wf :"(wf atom_ordering)" 
  and   atom_ordering_total:"(\<forall>x y. (x \<noteq> y \<longrightarrow> ((x,y) \<in> atom_ordering \<or> (y,x) \<in> atom_ordering)))"
  and   atom_ordering_trans: "\<forall>x y z. (x,y) \<in> atom_ordering \<longrightarrow> (y,z) \<in> atom_ordering
          \<longrightarrow> (x,z) \<in> atom_ordering"
  and   atom_ordering_irrefl: "\<forall>x y. (x,y) \<in> atom_ordering \<longrightarrow> (y,x) \<notin> atom_ordering"
begin

text {* Literals are defined as usual and clauses and formulas are considered as sets. 
Clause sets are not assumed to be finite (so that the results can 
be applied to sets of clauses obtained by grounding first-order clauses). *}

datatype 'a Literal = Pos "'a" | Neg "'a" 

definition "atoms = { x::'at. True }"

fun atom :: "'a Literal \<Rightarrow> 'a"
where 
  "(atom (Pos A)) = A" |
  "(atom (Neg A)) = A"

fun complement :: "'a Literal \<Rightarrow> 'a Literal"
where 
  "(complement (Pos A)) = (Neg A)" | 
  "(complement (Neg A)) = (Pos A)"

lemma atom_property : "A = (atom L) \<Longrightarrow> (L = (Pos A) \<or> L = (Neg A))"
by (metis atom.elims)

fun positive :: "'at Literal \<Rightarrow> bool"
where
  "(positive (Pos A)) = True" |
  "(positive (Neg A)) = False"

fun negative :: "'at Literal \<Rightarrow> bool"
where
  "(negative (Pos A)) = False" |
  "(negative (Neg A)) = True"

type_synonym 'a Clause = "'a Literal set"

type_synonym 'a Formula = "'a Clause set"

text {* Note that the clauses are not assumed to be finite (some of the properties below
hold for infinite clauses). *}

text {* The following functions return the set of atoms occurring in a clause or formula. *}

fun atoms_clause :: "'at Clause \<Rightarrow> 'at set"
  where "atoms_clause C = { A. \<exists>L. L \<in> C \<and> A = atom(L) }"

fun atoms_formula :: "'at Formula \<Rightarrow> 'at set"
  where "atoms_formula S = { A. \<exists>C. C \<in> S \<and> A \<in> atoms_clause(C) }"

lemma atoms_formula_subset: "S1 \<subseteq> S2 \<Longrightarrow> atoms_formula S1 \<subseteq> atoms_formula S2"
by auto

lemma atoms_formula_union: "atoms_formula (S1 \<union> S2) = atoms_formula S1 \<union> atoms_formula S2"
by auto

text {* The following predicate is useful to state that every clause in a set fulfills 
some property. *}

definition all_fulfill :: "('at Clause \<Rightarrow> bool) \<Rightarrow> 'at Formula \<Rightarrow> bool"
  where "all_fulfill P S = (\<forall>C. (C \<in> S \<longrightarrow> (P C)))"

text {* The order on atoms induces a (non total) order among literals: *}

fun literal_ordering :: "'at Literal \<Rightarrow> 'at Literal \<Rightarrow> bool"
where
    "(literal_ordering L1 L2) = ((atom L1,atom L2) \<in> atom_ordering)"

lemma literal_ordering_trans : 
  assumes "literal_ordering A B"
  assumes "literal_ordering B C"
  shows "literal_ordering A C"
using assms(1) assms(2) atom_ordering_trans literal_ordering.simps by blast

definition strictly_maximal_literal :: "'at Clause \<Rightarrow> 'at Literal \<Rightarrow> bool"
where
  "(strictly_maximal_literal S A) \<equiv> (A \<in> S) \<and> (\<forall>B. ( B \<in> S \<and> A \<noteq> B)  \<longrightarrow> (literal_ordering B A))"

section {* Semantics *}

text {* We define the notions of interpretation, satisfiability and entailment and establish  
some basic properties. *}

type_synonym 'a Interpretation  = "'a set" 

fun validate_literal :: "'at Interpretation \<Rightarrow> 'at Literal \<Rightarrow> bool" (infix "\<Turnstile>" 65)
  where
    "(validate_literal I (Pos A)) = (A \<in> I)" |
    "(validate_literal I (Neg A)) = (A \<notin> I)"

fun validate_clause :: "'at Interpretation \<Rightarrow> 'at Clause \<Rightarrow> bool" (infix "\<Turnstile>" 65)
  where
    "(validate_clause I C) = (\<exists>L. (L \<in>  C) \<and> (validate_literal I L))"

fun validate_formula :: "'at Interpretation \<Rightarrow> 'at Formula \<Rightarrow> bool" (infix "\<Turnstile>" 65)
  where
    "(validate_formula I S) = (\<forall>C. (C \<in> S \<longrightarrow> (validate_clause I C)))"     

definition satisfiable :: "'at Formula \<Rightarrow> bool"
where
  "(satisfiable S) \<equiv> (\<exists>I. (validate_formula I S))"

text {* We define the usual notions of entailment between clauses and formulas. *}

definition entails :: "'at Formula \<Rightarrow> 'at Clause \<Rightarrow> bool"
where
  "(entails S C) \<equiv> (\<forall>I. (validate_formula I S) \<longrightarrow> (validate_clause I C))"

lemma entails_member:
  assumes "C \<in> S"
  shows "entails S C"
using assms unfolding entails_def by simp

definition entails_formula :: "'at Formula \<Rightarrow> 'at Formula \<Rightarrow> bool"
  where "(entails_formula S1 S2) = (\<forall>C \<in> S2. (entails S1 C))"

definition equivalent :: "'at Formula \<Rightarrow> 'at Formula \<Rightarrow> bool"
  where "(equivalent S1 S2) = (entails_formula S1 S2 \<and> entails_formula S2 S1)"

lemma equivalent_symmetric: "equivalent S1 S2 \<Longrightarrow> equivalent S2 S1"
by (simp add: equivalent_def)

lemma entailment_implies_validity:
  assumes "entails_formula S1 S2"
  assumes "validate_formula I S1"
  shows "validate_formula I S2"
using assms entails_def entails_formula_def by auto

lemma validity_implies_entailment:
  assumes "\<forall>I. validate_formula I S1 \<longrightarrow> validate_formula I S2"
  shows "entails_formula S1 S2"
by (meson assms entails_def entails_formula_def validate_formula.elims(2))

lemma entails_transitive:
  assumes "entails_formula S1 S2"
  assumes "entails_formula S2 S3"
  shows "entails_formula S1 S3"
by (meson assms entailment_implies_validity validity_implies_entailment)

lemma equivalent_transitive:
  assumes "equivalent S1 S2"
  assumes "equivalent S2 S3"
  shows "equivalent S1 S3"
using assms entails_transitive equivalent_def by auto

lemma entailment_subset :
  assumes "S2 \<subseteq> S1"
  shows "entails_formula S1 S2"
proof -
  have "\<forall>L La. L \<notin> La \<or> entails La L"
    by (meson entails_member)
  thus ?thesis
    by (meson assms entails_formula_def set_rev_mp)
qed

lemma entailed_formula_entails_implicates:
  assumes "entails_formula S1 S2"
  assumes "entails S2 C"
  shows "entails S1 C"
using assms entailment_implies_validity entails_def by blast

section {* Inference Rules *}

text {* We first define an abstract notion of a binary inference rule. *}

type_synonym 'a BinaryRule = "'a Clause \<Rightarrow> 'a Clause \<Rightarrow> 'a Clause \<Rightarrow> bool"

definition less_restrictive :: "'at BinaryRule \<Rightarrow> 'at BinaryRule \<Rightarrow> bool"
where
  "(less_restrictive R1 R2) = (\<forall>P1 P2 C. (R2 P1 P2 C) \<longrightarrow> ((R1 P1 P2 C) \<or> (R1 P2 P1 C)))"

text {* The following functions allow to generate all the clauses that are deducible
from a given clause set (in one step). *}

fun all_deducible_clauses:: "'at BinaryRule \<Rightarrow> 'at Formula \<Rightarrow> 'at Formula"
  where "all_deducible_clauses R S = { C. \<exists>P1 P2. P1 \<in> S \<and> P2 \<in> S \<and> (R P1 P2 C) }" 

fun add_all_deducible_clauses:: "'at BinaryRule \<Rightarrow> 'at Formula \<Rightarrow> 'at Formula"
  where "add_all_deducible_clauses R S = (S \<union> all_deducible_clauses R S)"

definition derived_clauses_are_finite :: "'at BinaryRule \<Rightarrow> bool"
  where "derived_clauses_are_finite R = 
    (\<forall>P1 P2 C. (finite P1 \<longrightarrow> finite P2 \<longrightarrow> (R P1 P2 C) \<longrightarrow> finite C))"

lemma less_restrictive_and_finite :
  assumes "less_restrictive R1 R2"
  assumes "derived_clauses_are_finite R1"
  shows "derived_clauses_are_finite R2"
by (metis assms derived_clauses_are_finite_def less_restrictive_def)  (* takes a few seconds *)
 
text {* We then define the unrestricted resolution rule and usual resolution refinements. *} 

subsection {* Unrestricted Resolution *}

definition resolvent :: "'at BinaryRule"
  where
  "(resolvent P1 P2 C) \<equiv> 
    (\<exists>A. ((Pos A) \<in> P1 \<and> (Neg A) \<in> P2 \<and> (C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A })))))"

text {* For technical convience, we now introduce a slightly extended definition in which resolution 
upon a literal  not occurring in the premises is allowed (the obtained resolvent is then redundant 
with the premises). If the atom is fixed then this version of the resolution rule can be turned into 
a total function. *}

fun resolvent_upon :: "'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at \<Rightarrow> 'at Clause"
where
  "(resolvent_upon P1 P2 A) =
      ( (P1 - { Pos A}) \<union> ( P2 - { Neg A }))"

lemma resolvent_upon_is_resolvent : 
  assumes "Pos A \<in> P1"
  assumes "Neg A \<in> P2"
  shows "resolvent P1 P2 (resolvent_upon P1 P2 A)"
using assms unfolding resolvent_def by auto

lemma resolvent_is_resolvent_upon : 
  assumes "resolvent P1 P2 C"
  shows "\<exists>A. C = resolvent_upon P1 P2 A"
using assms unfolding resolvent_def by auto

lemma resolvent_is_finite :
  shows "derived_clauses_are_finite resolvent"
proof (rule ccontr)
  assume "\<not>derived_clauses_are_finite resolvent"
  then have "\<exists>P1 P2 C. \<not>(resolvent P1 P2 C \<longrightarrow> finite P1 \<longrightarrow> finite P2 \<longrightarrow> finite C)"
    unfolding derived_clauses_are_finite_def by blast
 then obtain P1 P2 C where "resolvent P1 P2 C" "finite P1" "finite P2" and "\<not>finite C" by blast    
 from `resolvent P1 P2 C` `finite P1` `finite P2` and `\<not>finite C` show "False"
 using assms unfolding resolvent_def using finite_Diff and finite_Union by auto
qed


text {* In the next subsections we introduce various resolution refinements and show that they are 
more restrictive than unrestricted resolution. *}

subsection {* Ordered Resolution *}

text {* In the first refinement, resolution is only allowed on maximal literals. *}

definition ordered_resolvent :: "'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> bool" 
  where
  "(ordered_resolvent P1 P2 C) \<equiv> 
    (\<exists>A. ((C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A })))
      \<and> (strictly_maximal_literal P1 (Pos A)) \<and> (strictly_maximal_literal P2 (Neg A))))"

text {* We now show that the maximal literal of the resolvent is always smaller than those of 
the premises. *}

lemma resolution_and_max_literal : 
  assumes "R = resolvent_upon P1 P2 A"
  assumes "strictly_maximal_literal P1 (Pos A)"
  assumes "strictly_maximal_literal P2 (Neg A)"
  assumes "strictly_maximal_literal R M"
  shows "(atom M, A) \<in> atom_ordering" 
proof -
  obtain MA where "M = (Pos MA) \<or> M = (Neg MA)" using Literal.exhaust [of M] by auto
  hence "MA = (atom M)" by auto
  from `strictly_maximal_literal R M` and `R = resolvent_upon P1 P2 A` 
    have "M \<in> P1 - { Pos A } \<or> M \<in> P2 - { Neg A }"
    unfolding strictly_maximal_literal_def by auto
  hence "(MA,A) \<in> atom_ordering"
  proof 
    assume "M \<in> P1 - { Pos A }"
    from `M \<in> P1 - { Pos A }` and `strictly_maximal_literal P1 (Pos A)` 
      have "literal_ordering M (Pos A)" 
      unfolding strictly_maximal_literal_def by auto
    from `M = Pos MA \<or> M = Neg MA` and `literal_ordering M (Pos A)` 
    show "(MA,A) \<in> atom_ordering" by auto
  next
    assume "M \<in> P2 - { Neg A }"
    from `M \<in> P2 - { Neg A }` and `strictly_maximal_literal P2 (Neg A)` 
      have "literal_ordering M (Neg A)" by (auto simp only: strictly_maximal_literal_def)
    from `M = Pos MA \<or> M = Neg MA` and `literal_ordering M (Neg A)` 
    show "(MA,A) \<in> atom_ordering" by auto
  qed
  from this and `MA = atom M` show ?thesis by auto
qed

subsection {* Ordered Resolution with Selection *}

text {* In the next restriction strategy, some negative literals are selected with highest priority 
for applying the resolution rule, regardless of the ordering. Relaxed ordering restrictions also 
apply. *}

definition "(selected_part Sel C) = { L. L \<in> C \<and> (\<exists>A \<in> Sel. L = (Neg A)) }"

definition ordered_sel_resolvent :: "'at set \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> bool" 
  where
  "(ordered_sel_resolvent Sel P1 P2 C) \<equiv> 
    (\<exists>A. ((C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A })))
      \<and> (strictly_maximal_literal P1 (Pos A)) \<and> ((selected_part Sel P1) = {}) \<and> 
          ( ((strictly_maximal_literal P2 (Neg A)) \<and> (selected_part Sel P2) = {}) 
          \<or> (strictly_maximal_literal (selected_part Sel P2) (Neg A)))))"

lemma ordered_resolvent_is_resolvent : "less_restrictive resolvent ordered_resolvent"
using less_restrictive_def ordered_resolvent_def resolvent_upon_is_resolvent strictly_maximal_literal_def by auto

text {* The next lemma states that ordered resolution with selection coincides with ordered 
resolution if the selected part is empty. *}

lemma ordered_sel_resolvent_is_ordered_resolvent : 
 assumes "ordered_resolvent P1 P2 C"
 assumes "selected_part Sel P1 = {}"
 assumes "selected_part Sel P2 = {}"
 shows "ordered_sel_resolvent Sel P1 P2 C"
using assms ordered_resolvent_def ordered_sel_resolvent_def by auto

lemma ordered_resolvent_upon_is_resolvent : 
  assumes "strictly_maximal_literal P1 (Pos A)"
  assumes "strictly_maximal_literal P2 (Neg A)"
  shows "ordered_resolvent P1 P2 (resolvent_upon P1 P2 A)"
using assms ordered_resolvent_def by auto


subsection {* Semantic Resolution *}

text {* In this strategy, resolution is applied only if one parent is false in some (fixed) 
interpretation. Note that ordering restrictions still apply, although they are relaxed. *}

definition validated_part :: "'at set \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause"
where "(validated_part I C) = { L. L \<in> C \<and> (validate_literal I L) }"

definition ordered_model_resolvent :: 
  "'at Interpretation \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> bool"
where 
  "(ordered_model_resolvent I P1 P2 C) = 
    (\<exists>L. (C = (P1 - { L } \<union> (P2 - { complement L }))) \<and>
      ((validated_part I P1) = {}  \<and> (strictly_maximal_literal P1 L))
      \<and> (strictly_maximal_literal (validated_part I P2) (complement L)))"

lemma ordered_model_resolvent_is_resolvent : "less_restrictive resolvent (ordered_model_resolvent I)"
proof (rule ccontr)
  assume "\<not> less_restrictive resolvent (ordered_model_resolvent I)"
  then obtain P1 P2 C where "ordered_model_resolvent I P1 P2 C" and "\<not>resolvent P1 P2 C" 
    and "\<not>resolvent P2 P1 C" unfolding less_restrictive_def by auto
  from `ordered_model_resolvent I P1 P2 C` obtain L 
    where "strictly_maximal_literal P1 L" 
    and "strictly_maximal_literal (validated_part I P2) (complement L)" 
    and "C = (P1 - { L }) \<union> (P2 - { complement L })"
    using ordered_model_resolvent_def [of I P1 P2 C] by auto 
  from `strictly_maximal_literal P1 L` have "L \<in> P1" by (simp only: strictly_maximal_literal_def)
  from `strictly_maximal_literal (validated_part I P2) (complement L)` have "(complement L) \<in> P2" 
    by (auto simp only: strictly_maximal_literal_def validated_part_def)
  obtain A where "L = Pos A \<or> L = Neg A" using Literal.exhaust [of L] by auto
  from this and `C = (P1 - { L }) \<union> (P2 - { complement L })` and `L \<in> P1` and `(complement L) \<in> P2`
    have "resolvent P1 P2 C \<or> resolvent P2 P1 C" unfolding resolvent_def by auto
  from this and `\<not>resolvent P2 P1 C` and `\<not>resolvent P1 P2 C` show "False" by auto
qed

subsection {* Unit Resolution *}

text {* Resolution is applied only if one parent is unit (this restriction is incomplete).*}

definition Unit :: "'at Clause \<Rightarrow> bool"
  where "(Unit C) = ((card C) = 1)"

definition unit_resolvent :: "'at BinaryRule"
  where "(unit_resolvent P1 P2 C) =  ((\<exists>L. (C = ( (P1 - { L}) \<union> ( P2 - { complement L })))
      \<and> L \<in> P1 \<and> (complement L) \<in> P2) \<and> Unit P1)"

lemma unit_resolvent_is_resolvent : "less_restrictive resolvent unit_resolvent"
proof (rule ccontr)
  assume "\<not> less_restrictive resolvent unit_resolvent"
  then obtain P1 P2 C where "unit_resolvent P1 P2 C" and "\<not>resolvent P1 P2 C" 
    and "\<not>resolvent P2 P1 C" unfolding less_restrictive_def by auto
  from `unit_resolvent P1 P2 C` obtain L where "L \<in> P1" and "complement L \<in> P2" 
    and "C = (P1 - { L }) \<union> (P2 - { complement L })"
    using unit_resolvent_def [of P1 P2 C] by auto 
  obtain A where "L = Pos A \<or> L = Neg A" using Literal.exhaust [of L] by auto
  from this and `C = (P1 - { L }) \<union> (P2 - { complement L })` and `L \<in> P1` and `complement L \<in> P2`
    have "resolvent P1 P2 C \<or> resolvent P2 P1 C" unfolding resolvent_def by auto
  from this and `\<not>resolvent P2 P1 C` and `\<not>resolvent P1 P2 C` show "False" by auto
qed

subsection {* Positive and Negative Resolution *}

text {* Resolution is applied only if one parent is positive (resp. negative). Again, relaxed
ordering restrictions apply. *}

definition positive_part :: "'at Clause \<Rightarrow> 'at Clause"
where 
  "(positive_part C) = { L. (\<exists>A. L = Pos A) \<and> L \<in> C }"

definition negative_part :: "'at Clause \<Rightarrow> 'at Clause"
where 
  "(negative_part C) = { L. (\<exists>A. L = Neg A) \<and> L \<in> C }"

lemma decomposition_clause_pos_neg :
  "C = (negative_part C) \<union> (positive_part C)"
proof
  show "C \<subseteq> (negative_part C) \<union> (positive_part C)"
  proof
    fix x assume "x \<in> C"
    obtain A where "x = Pos A \<or> x = Neg A" using Literal.exhaust [of x] by auto
    show "x \<in> (negative_part C) \<union> (positive_part C)"
    proof cases 
      assume "x = Pos A"
      from this and `x \<in> C` have "x \<in> positive_part C" unfolding positive_part_def by auto
      then show "x \<in> (negative_part C) \<union> (positive_part C)" by auto
    next
      assume "x \<noteq> Pos A"
      from this and `x = Pos A \<or> x = Neg A`have "x = Neg A" by auto
      from this and `x \<in> C` have "x \<in> negative_part C" unfolding negative_part_def by auto
      then show "x \<in> (negative_part C) \<union> (positive_part C)" by auto
    qed
  qed
next
  show "(negative_part C) \<union> (positive_part C) \<subseteq> C" unfolding negative_part_def
  and positive_part_def by auto
qed

definition ordered_positive_resolvent :: "'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> bool"
where 
  "(ordered_positive_resolvent P1 P2 C) = 
    (\<exists>L. (C = (P1 - { L } \<union> (P2 - { complement L }))) \<and>
      ((negative_part P1) = {}  \<and> (strictly_maximal_literal P1 L))
      \<and> (strictly_maximal_literal (negative_part P2) (complement L)))"

definition ordered_negative_resolvent :: "'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> bool"
where 
  "(ordered_negative_resolvent P1 P2 C) = 
    (\<exists>L. (C = (P1 - { L } \<union> (P2 - { complement L }))) \<and>
      ((positive_part P1) = {}  \<and> (strictly_maximal_literal P1 L))
      \<and> (strictly_maximal_literal (positive_part P2) (complement L)))"

lemma positive_resolvent_is_resolvent : "less_restrictive resolvent ordered_positive_resolvent"
proof (rule ccontr)
  assume "\<not> less_restrictive resolvent ordered_positive_resolvent"
  then obtain P1 P2 C where "ordered_positive_resolvent P1 P2 C" and "\<not>resolvent P1 P2 C" 
    and "\<not>resolvent P2 P1 C"  unfolding less_restrictive_def by auto
  from `ordered_positive_resolvent P1 P2 C` obtain L 
    where "strictly_maximal_literal P1 L" 
    and "strictly_maximal_literal (negative_part P2)(complement L)" 
    and "C = (P1 - { L }) \<union> (P2 - { complement L })"
    using ordered_positive_resolvent_def [of P1 P2 C] by auto 
  from `strictly_maximal_literal P1 L` have "L \<in> P1" unfolding strictly_maximal_literal_def by auto
  from `strictly_maximal_literal (negative_part P2) (complement L)` have "(complement L) \<in> P2" 
    unfolding strictly_maximal_literal_def negative_part_def by auto
  obtain A where "L = Pos A \<or> L = Neg A" using Literal.exhaust [of L] by auto
  from this and `C = (P1 - { L }) \<union> (P2 - { complement L })` and `L \<in> P1` and `(complement L) \<in> P2`
  have "resolvent P1 P2 C \<or> resolvent P2 P1 C" unfolding resolvent_def by auto
  from this and `\<not>(resolvent P2 P1 C)` and `\<not>(resolvent P1 P2 C)` show "False" by auto
qed

lemma negative_resolvent_is_resolvent : "less_restrictive resolvent ordered_negative_resolvent"
proof (rule ccontr)
  assume "\<not> less_restrictive resolvent ordered_negative_resolvent"
  then obtain P1 P2 C where "(ordered_negative_resolvent P1 P2 C)" and "\<not>(resolvent P1 P2 C)" 
    and "\<not>(resolvent P2 P1 C)"  unfolding less_restrictive_def by auto
  from `ordered_negative_resolvent P1 P2 C` obtain L where "strictly_maximal_literal P1 L" 
    and "strictly_maximal_literal (positive_part P2)(complement L)" 
    and "C = (P1 - { L }) \<union> (P2 - { complement L })"
    using ordered_negative_resolvent_def [of P1 P2 C] by auto 
  from `strictly_maximal_literal P1 L` have "L \<in> P1" unfolding strictly_maximal_literal_def by auto
  from `strictly_maximal_literal (positive_part P2) (complement L)` have "(complement L) \<in> P2" 
  unfolding strictly_maximal_literal_def positive_part_def by auto
  obtain A where "L = Pos A \<or> L = Neg A" using Literal.exhaust [of L] by auto
  from this and `C = (P1 - { L }) \<union> (P2 - { complement L })` and `L \<in> P1` and `(complement L) \<in> P2`
  have "resolvent P1 P2 C \<or> resolvent P2 P1 C" unfolding resolvent_def by auto
  from this and `\<not>resolvent P2 P1 C` and `\<not>resolvent P1 P2 C` show "False" by auto
qed

section {* Redundancy Elimination Rules *}

text {* We define the usual redundancy elimination rules. *}

definition tautology :: "'a Clause \<Rightarrow> bool"
where
  "(tautology C) \<equiv> (\<exists> A. (Pos A \<in> C \<and> Neg A \<in> C))"

definition subsumes :: "'a Clause \<Rightarrow> 'a Clause \<Rightarrow> bool"
where
  "(subsumes C D)  \<equiv> (C \<subseteq> D)"

definition redundant :: "'a Clause \<Rightarrow> 'a Formula \<Rightarrow> bool"
where 
  "redundant C S = ((tautology C) \<or> (\<exists>D. (D \<in> S \<and> subsumes D C)))"

definition strictly_redundant :: "'a Clause \<Rightarrow> 'a Formula \<Rightarrow> bool"
where 
  "strictly_redundant C S = ((tautology C) \<or> (\<exists>D. (D \<in> S \<and> (D \<subset> C))))"

definition simplify :: "'at Formula \<Rightarrow> 'at Formula"
where 
  "simplify S = { C. C \<in> S \<and> \<not>strictly_redundant C S }"

text {* We first establish some basic syntactic properties. *}

lemma tautology_monotonous : "(tautology C) \<Longrightarrow> (C \<subseteq> D) \<Longrightarrow> (tautology D)"
unfolding tautology_def by auto

lemma simplify_involutive:
  shows "simplify (simplify S) = (simplify S)"
proof -
  from assms show ?thesis unfolding simplify_def strictly_redundant_def by auto
qed

lemma simplify_finite:
  assumes "all_fulfill finite S"
  shows "all_fulfill finite (simplify S)"
using assms all_fulfill_def simplify_def by auto

lemma atoms_formula_simplify:
  shows "atoms_formula (simplify S) \<subseteq> atoms_formula S"
unfolding simplify_def using atoms_formula_subset by auto

lemma subsumption_preserves_redundancy :
  assumes "redundant C S"
  assumes "subsumes C D" 
  shows "redundant D S"
using assms tautology_monotonous unfolding redundant_def subsumes_def by blast

lemma subsumption_and_max_literal : 
  assumes "subsumes C1 C2"
  assumes "strictly_maximal_literal C1 L1"
  assumes "strictly_maximal_literal C2 L2"
  assumes "A1 = atom L1"
  assumes "A2 = atom L2"
  shows "(A1 = A2) \<or> (A1,A2) \<in> atom_ordering"
proof -
  from `A1 = atom L1` have "L1 = (Pos A1) \<or> L1 = (Neg A1)" by (rule atom_property)
  from `A2 = atom L2` have "L2 = (Pos A2) \<or> L2 = (Neg A2)" by (rule atom_property)
  from `subsumes C1 C2` and `strictly_maximal_literal C1 L1` have "L1 \<in> C2" 
    unfolding strictly_maximal_literal_def subsumes_def by auto
  from `strictly_maximal_literal C2 L2` and `L1 \<in> C2` have "L1 = L2 \<or> literal_ordering L1 L2" 
    unfolding strictly_maximal_literal_def by auto
  thus ?thesis 
  proof
    assume "L1 = L2"
    from `L1 = L2` and `A1 = atom L1` and `A2 = atom L2` show ?thesis by auto
  next
    assume "literal_ordering L1 L2"
    from `literal_ordering L1 L2` and `L1 = (Pos A1) \<or> L1 = (Neg A1)`   
      and `L2 = (Pos A2) \<or> L2 = (Neg A2)` 
      show ?thesis by auto
  qed
qed

lemma superset_preserves_redundancy: 
  assumes "redundant C S"
  assumes "S \<subseteq> S'"
  shows "redundant C S'"
using assms unfolding redundant_def by blast

lemma superset_preserves_strict_redundancy: 
  assumes "strictly_redundant C S"
  assumes "S \<subseteq> SS"
  shows "strictly_redundant C SS"
using assms unfolding strictly_redundant_def by blast

text {* The following lemmas relate the above notions with that of semantic entailment and thus 
establish the soundness of redundancy elimination rules. *}

lemma tautologies_are_valid : 
  assumes "tautology C"
  shows "validate_clause I C"
by (meson assms tautology_def validate_clause.simps validate_literal.simps(1) 
    validate_literal.simps(2))

lemma subsumption_and_semantics : 
  assumes "subsumes C D"
  assumes "validate_clause I C"
  shows "validate_clause I D"
using assms unfolding subsumes_def by auto

lemma redundancy_and_semantics : 
  assumes "redundant C S"
  assumes "validate_formula I S"
  shows "validate_clause I C"
by 
(meson assms redundant_def subsumption_and_semantics tautologies_are_valid validate_formula.elims)

lemma redundancy_implies_entailment:
  assumes "redundant C S"
  shows "entails S C"
using assms entails_def redundancy_and_semantics by auto

lemma simplify_and_membership :
  assumes "all_fulfill finite S"
  assumes "T = simplify S"
  assumes "C \<in> S"
  shows "redundant C T"
proof -
  {
    fix n 
    have "\<forall>C. card C \<le> n \<longrightarrow> C \<in> S \<longrightarrow> redundant C T" (is "?P n")
    proof (induction n)
      show "?P 0"
      proof ((rule allI),(rule impI)+)
        fix C assume "card C \<le> 0" and "C \<in> S"
        from `card C \<le> 0` and `C \<in> S` and `all_fulfill finite S` have "C = {}" using card_0_eq 
          unfolding all_fulfill_def by auto
        then have "\<not> strictly_redundant C S" unfolding strictly_redundant_def tautology_def by auto
        from this and `C \<in> S` and `T = simplify S` have "C \<in> T" using simplify_def by auto 
        from this show "redundant C T" unfolding redundant_def subsumes_def by auto
      qed
    next 
      fix n assume "?P n"
      show "?P (Suc n)"
        proof ((rule allI),(rule impI)+)
          fix C assume "card C \<le> (Suc n)" and "C \<in> S"
          show "redundant C T"
          proof (rule ccontr)
            assume "\<not>redundant C T"
            from this have "C \<notin> T" unfolding redundant_def subsumes_def by auto
            from this and `T = simplify S` and `C \<in> S` have "strictly_redundant C S" 
              unfolding simplify_def strictly_redundant_def by auto
              from this and `\<not>redundant C T` obtain D where "D \<in> S" and "D \<subset> C" 
              unfolding redundant_def strictly_redundant_def by auto
            from `D \<subset> C` and `C \<in> S` and `all_fulfill finite S` have "card D < card C" 
              unfolding all_fulfill_def 
              using psubset_card_mono  by auto
            from this and `card C \<le> (Suc n)` have "card D \<le> n" by auto
            from this and  `?P n` and `D \<in> S` have "redundant D T" by auto
            show "False"
            proof cases
              assume "tautology D"
              from this and  `D \<subset> C` have "tautology C" unfolding tautology_def by auto
              then have "redundant C T" unfolding redundant_def by auto
              from this and `\<not>redundant C T` show "False" by auto
            next 
              assume "\<not>tautology D"
              from this and `redundant D T` obtain E where "E \<in> T" and "E \<subseteq> D" 
                unfolding redundant_def subsumes_def by auto
              from this and  `D \<subset> C` have "E \<subseteq> C" by auto
              from this and `E \<in> T` and  `\<not>redundant C T` show False 
                unfolding redundant_def and subsumes_def by auto
            qed 
          qed
        qed
      qed
    }
  from this and `C \<in> S` show ?thesis by auto
qed

lemma simplify_preserves_redundancy: 
  assumes "all_fulfill finite S"
  assumes "redundant C S"
  shows "redundant C (simplify S)"
by (meson assms redundant_def simplify_and_membership subsumption_preserves_redundancy)

lemma simplify_preserves_strict_redundancy: 
  assumes "all_fulfill finite S"
  assumes "strictly_redundant C S"
  shows "strictly_redundant C (simplify S)"
proof ((cases "tautology C"),(auto simp add: strictly_redundant_def)[1])
next
  assume "\<not>tautology C"
  from this and assms(2) obtain D where "D \<subset> C" and "D \<in> S" unfolding strictly_redundant_def by auto
  from `D \<in> S` have "redundant D S" unfolding redundant_def subsumes_def by auto
  from assms(1) this have "redundant D (simplify S)" using simplify_preserves_redundancy by auto
  from `\<not>tautology C` and `D \<subset> C` have "\<not>tautology D" unfolding tautology_def by auto
  from this and `redundant D (simplify S)` obtain E where "E \<in> simplify S" 
    and "subsumes E D" unfolding redundant_def by auto
  from `subsumes E D` and `D \<subset> C` have "E \<subset> C" unfolding subsumes_def by auto
  from this and `E \<in> simplify S` show "strictly_redundant C (simplify S)" 
    unfolding strictly_redundant_def by auto
qed

lemma simplify_preserves_semantic : 
  assumes "T = simplify S"
  assumes "all_fulfill finite S"
  shows "validate_formula I S \<longleftrightarrow> validate_formula I T"
by (metis (mono_tags, lifting) assms mem_Collect_eq redundancy_and_semantics simplify_and_membership 
    simplify_def validate_formula.simps)

lemma simplify_preserves_equivalence : 
  assumes "T = simplify S"
  assumes "all_fulfill finite S"
  shows "equivalent S T"
using assms equivalent_def simplify_preserves_semantic validity_implies_entailment by auto

text {* After simplification, the formula contains no strictly redundant clause: *}

definition non_redundant :: "'at Formula \<Rightarrow> bool"
  where "non_redundant S = (\<forall>C. (C \<in> S \<longrightarrow> \<not>strictly_redundant C S))"

lemma simplify_non_redundant:
  shows "non_redundant (simplify S)"
by (simp add: non_redundant_def simplify_def strictly_redundant_def)

lemma deducible_clause_preserve_redundancy:
  assumes "redundant C S"
  shows "redundant C (add_all_deducible_clauses R S)"
using assms superset_preserves_redundancy by fastforce

section {* Renaming *}

text {* A renaming is a function changing the sign of some literals. We show that this operation preserves 
 most of the previous syntactic and semantic notions. *}

definition rename_literal :: "'at set \<Rightarrow> 'at Literal \<Rightarrow> 'at Literal" 
where "rename_literal A L = (if ((atom L) \<in> A) then (complement L) else L)"
  
definition rename_clause :: "'at set \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause"
 where "rename_clause A C = {L. \<exists>LL. LL \<in> C \<and> L = (rename_literal A LL)}"

definition rename_formula :: "'at set \<Rightarrow> 'at Formula \<Rightarrow> 'at Formula"
where "rename_formula A S = {C. \<exists>CC. CC \<in> S \<and> C = (rename_clause A CC)}"

lemma inverse_renaming : "(rename_literal A (rename_literal A L)) = L"
proof -
  obtain A where at: "L = (Pos A) \<or> L = (Neg A)" using Literal.exhaust [of L ] by auto
  from at show ?thesis unfolding rename_literal_def  by auto
qed

lemma inverse_clause_renaming : "(rename_clause A (rename_clause A L)) = L"
proof -
  show ?thesis using inverse_renaming unfolding rename_clause_def by auto
qed

lemma inverse_formula_renaming : "rename_formula A (rename_formula A L) = L"
proof -
  show ?thesis using inverse_clause_renaming unfolding rename_formula_def by auto
qed

lemma renaming_preserves_cardinality :
  "card (rename_clause A C) = card C"
proof -
  have im: "rename_clause A C = (rename_literal A) ` C" unfolding rename_clause_def by auto
  have "inj_on (rename_literal A) C" by (metis inj_onI inverse_renaming)  
  from this and im show ?thesis using card_image by auto
qed

lemma renaming_preserves_literal_order :
  assumes "literal_ordering L1 L2"
  shows "literal_ordering (rename_literal A L1) (rename_literal A L2)"
proof -
  obtain A1 where at1: "L1 = (Pos A1) \<or> L1 = (Neg A1)" using Literal.exhaust [of L1 ] by auto
  obtain A2 where at2: "L2 = (Pos A2) \<or> L2 = (Neg A2)" using Literal.exhaust [of L2 ] by auto
  from assms and at1 and at2 show ?thesis unfolding rename_literal_def by auto
qed

lemma inverse_renaming_preserves_literal_order :
  assumes  "literal_ordering (rename_literal A L1) (rename_literal A L2)"
  shows "literal_ordering L1 L2"
by (metis assms inverse_renaming renaming_preserves_literal_order)

lemma renaming_is_injective:
  assumes "rename_literal A L1 = rename_literal A L2"
  shows "L1 = L2"
by (metis (no_types) assms inverse_renaming)
  
lemma renaming_preserves_strictly_maximal_literal :
  assumes "strictly_maximal_literal C L"
  shows "strictly_maximal_literal (rename_clause A C) (rename_literal A L)"
proof -
  from assms have "(L \<in> C)" and Lismax: "(\<forall>B. (B \<in> C \<and> L \<noteq> B)  \<longrightarrow> (literal_ordering B L))" 
  unfolding strictly_maximal_literal_def by auto
  from `L \<in> C` have "(rename_literal A L) \<in> (rename_clause A C)" 
    unfolding rename_literal_def and rename_clause_def by auto
  have 
    "\<forall>B. (B \<in> rename_clause A C \<longrightarrow> rename_literal A L \<noteq> B  
      \<longrightarrow> literal_ordering B (rename_literal A L))"
  proof (rule)+
    fix B assume "B \<in> rename_clause A C" and "rename_literal A L \<noteq> B"
    from `B \<in> rename_clause A C` obtain B' where "B' \<in> C" and "B = rename_literal A B'" 
      unfolding rename_clause_def by auto 
    from `rename_literal A L \<noteq> B` and `B = rename_literal A B'` 
      have "rename_literal A L \<noteq> rename_literal A B'" by auto
    hence "L \<noteq> B'" by auto
    from this and `B' \<in> C` and Lismax have "literal_ordering B' L" by auto
    from this and `B = (rename_literal A B')` 
      show "literal_ordering B (rename_literal A L)" using renaming_preserves_literal_order by auto
  qed
  from this and `(rename_literal A L) \<in> (rename_clause A C)` show ?thesis 
    unfolding strictly_maximal_literal_def by auto
qed

lemma renaming_and_selected_part :
  "selected_part UNIV C = rename_clause Sel (validated_part Sel (rename_clause Sel C))"
proof  
  show "selected_part UNIV C \<subseteq> rename_clause Sel (validated_part Sel (rename_clause Sel C))"
  proof
    fix x assume "x \<in> selected_part UNIV C"
    show "x \<in> rename_clause Sel (validated_part Sel (rename_clause Sel C))"
    proof -
      from `x \<in> selected_part UNIV C` obtain A where "x = Neg A" and "x \<in> C" 
        unfolding selected_part_def by auto
      from `x \<in> C` have "rename_literal Sel x \<in> rename_clause Sel C" 
        unfolding rename_clause_def by blast
      show "x \<in> rename_clause Sel (validated_part Sel (rename_clause Sel C))"
      proof cases
        assume "A \<in> Sel"
        from this and `x = Neg A` have "rename_literal Sel x = Pos A" 
          unfolding rename_literal_def by auto  
        from this and `A \<in> Sel` have "validate_literal Sel (rename_literal Sel x)" by auto
        from this and `rename_literal Sel x \<in> rename_clause Sel C` 
        have "rename_literal Sel x \<in> validated_part Sel (rename_clause Sel C)" 
          unfolding validated_part_def by auto
        thus "x \<in> rename_clause Sel (validated_part Sel (rename_clause Sel C))" 
          using inverse_renaming rename_clause_def by auto
      next
        assume "A \<notin> Sel"
        from this and `x = Neg A` have "rename_literal Sel x = Neg A" 
          unfolding rename_literal_def by auto  
        from this and `A \<notin> Sel` have "validate_literal Sel (rename_literal Sel x)" by auto
        from this and `rename_literal Sel x \<in> rename_clause Sel C` 
        have "rename_literal Sel x \<in> validated_part Sel (rename_clause Sel C)" 
          unfolding  validated_part_def by auto
        thus "x \<in> rename_clause Sel (validated_part Sel (rename_clause Sel C))" 
          using inverse_renaming rename_clause_def by auto
      qed
    qed
  qed
  next
  show "rename_clause Sel (validated_part Sel (rename_clause Sel C)) \<subseteq> (selected_part UNIV C)"
  proof
    fix x
    assume "x \<in> rename_clause Sel (validated_part Sel (rename_clause Sel C))"
    from this obtain y where "y \<in> validated_part Sel (rename_clause Sel C)" 
      and "x = rename_literal Sel y" 
      unfolding rename_clause_def validated_part_def by auto
    from `y \<in> validated_part Sel (rename_clause Sel C)` have
      "y \<in> rename_clause Sel C" and "validate_literal Sel y" unfolding validated_part_def by auto
    from `y \<in> rename_clause Sel C` obtain z where "z \<in> C" and "y = rename_literal Sel z" 
      unfolding rename_clause_def by auto
    obtain A where zA: "z = Pos A \<or> z = Neg A" using Literal.exhaust [of z] by auto
    show "x \<in> selected_part UNIV C"
    proof cases
        assume "A \<in> Sel"
        from this and zA and `y = rename_literal Sel z` have "y = complement z" 
          using rename_literal_def by auto
        from this and `A \<in> Sel` and zA and `validate_literal Sel y` have "y = Pos A" 
          and "z = Neg A" by auto
        from this and  `A \<in> Sel` and `x = rename_literal Sel y` have "x = Neg A" 
          unfolding rename_literal_def by auto
        from this and `z \<in> C` and `z = Neg A` show "x \<in> selected_part UNIV C" 
          unfolding selected_part_def by auto
    next 
        assume "A \<notin> Sel"
        from this and zA and `y = rename_literal Sel z` have "y = z" 
          using rename_literal_def by auto
        from this and `A \<notin> Sel` and zA and `validate_literal Sel y` have "y = Neg A" 
          and "z = Neg A" by auto
        from this and  `A \<notin> Sel` and `x = rename_literal Sel y` have "x = Neg A" 
          unfolding rename_literal_def by auto
        from this and `z \<in> C` and `z = Neg A` show "x \<in> selected_part UNIV C" 
          unfolding selected_part_def by auto
    qed
  qed
qed

lemma renaming_preserves_tautology:
  assumes "tautology C"
  shows "tautology (rename_clause Sel C)"
proof -
  from assms obtain A where "Pos A \<in> C" and "Neg A \<in> C" unfolding tautology_def by auto
  from `Pos A \<in> C` have "rename_literal Sel (Pos A) \<in>  rename_clause Sel C" 
    unfolding rename_clause_def by auto
  from `Neg A \<in> C` have "rename_literal Sel (Neg A) \<in>  rename_clause Sel C" 
    unfolding rename_clause_def by auto
  show ?thesis
  proof cases
    assume "A \<in> Sel"
    from this have "rename_literal Sel (Pos A) = Neg A" 
      and "rename_literal Sel (Neg A) = (Pos A)" 
      unfolding rename_literal_def by auto
    from `rename_literal Sel (Pos A) = (Neg A)` and  `rename_literal Sel (Neg A) = (Pos A)` 
      and `rename_literal Sel (Pos A) \<in>  (rename_clause Sel C)` 
      and  `rename_literal Sel (Neg A) \<in>  (rename_clause Sel C)`
      show "tautology (rename_clause Sel C)" unfolding tautology_def by auto
  next 
    assume "A \<notin> Sel"
    from this have "rename_literal Sel (Pos A) = Pos A" and "rename_literal Sel (Neg A) = (Neg A)" 
      unfolding rename_literal_def by auto
    from `rename_literal Sel (Pos A) = Pos A` and `rename_literal Sel (Neg A) = (Neg A)` 
      and `rename_literal Sel (Pos A) \<in>  rename_clause Sel C` 
      and  `rename_literal Sel (Neg A) \<in>  rename_clause Sel C`
      show "tautology (rename_clause Sel C)" unfolding tautology_def by auto
  qed
qed

lemma rename_union : "rename_clause Sel (C \<union> D) = rename_clause Sel C \<union> rename_clause Sel D"
unfolding rename_clause_def by auto

lemma renaming_set_minus_subset : 
  "rename_clause Sel (C - { L }) \<subseteq> rename_clause Sel C - {rename_literal Sel L }"
proof 
    fix x assume "x \<in> rename_clause Sel (C - { L })"
    then obtain y where "y \<in> C - { L }" and "x = rename_literal Sel y" 
      unfolding rename_clause_def by auto
    from `y \<in> C - { L }` and `x = rename_literal Sel y` have "x \<in> rename_clause Sel C" 
      unfolding rename_clause_def by auto
    have "x \<noteq> rename_literal Sel L" 
    proof
      assume "x = rename_literal Sel L"
      hence "rename_literal Sel x = L" using inverse_renaming by auto
      from this and `x = rename_literal Sel y` have "y = L" using inverse_renaming by auto
      from this and `y \<in> C - { L }` show "False" by auto
    qed
    from `x \<noteq> rename_literal Sel L` and `x \<in> rename_clause Sel C`
      show "x \<in> (rename_clause Sel C) - {rename_literal Sel L }" by auto
qed

lemma renaming_set_minus : "rename_clause Sel (C - { L }) 
  = (rename_clause Sel C) - {rename_literal Sel L }"
proof 
  show "rename_clause Sel (C - { L }) \<subseteq>  (rename_clause Sel C) - {rename_literal Sel L }"
    using renaming_set_minus_subset by auto
  next
  show "(rename_clause Sel C) - {rename_literal Sel L } \<subseteq> rename_clause Sel (C - { L })"
  proof -
  have "rename_clause Sel ( (rename_clause Sel C) - { (rename_literal Sel L) }) 
      \<subseteq>  (rename_clause Sel (rename_clause Sel C)) - {rename_literal Sel (rename_literal Sel L) }" 
    using renaming_set_minus_subset by auto
  from this 
    have "rename_clause Sel ( (rename_clause Sel C) - { (rename_literal Sel L) }) \<subseteq>  (C - {L })" 
    using inverse_renaming inverse_clause_renaming by auto
  from this 
    have "rename_clause Sel (rename_clause Sel ( (rename_clause Sel C) - { (rename_literal Sel L) })) 
            \<subseteq>  (rename_clause Sel (C - {L }))" using rename_clause_def by auto
  from this 
    show "(rename_clause Sel C) - { (rename_literal Sel L) } \<subseteq>  rename_clause Sel (C - {L })" 
    using inverse_renaming inverse_clause_renaming by auto
 qed
qed

definition rename_interpretation :: "'at set \<Rightarrow> 'at Interpretation \<Rightarrow> 'at Interpretation"
where 
  "rename_interpretation Sel I = { A. (A \<in> I \<and> A \<notin> Sel) } \<union> { A. (A \<notin> I \<and> A \<in> Sel) }"

lemma renaming_preserves_semantic :
  assumes "validate_literal I L"
  shows "validate_literal (rename_interpretation Sel I) (rename_literal Sel L)"
proof -
  let ?J = "rename_interpretation Sel I"
    obtain A where "L = Pos A \<or> L = Neg A" using Literal.exhaust [of L] by auto
    from `L = Pos A \<or> L = Neg A` have "atom L = A" by auto
    show ?thesis
    proof cases
      assume "A \<in> Sel"
      from this and `atom L = A` have "rename_literal Sel L = complement L"  
      unfolding rename_literal_def by auto
      show ?thesis 
      proof cases
        assume "L = Pos A" 
        from this and `validate_literal I L` have "A \<in> I" by auto
        from this and `A \<in> Sel` have "A \<notin> ?J" unfolding rename_interpretation_def by blast
        from this and `L = Pos A` and `rename_literal Sel L = complement L` show ?thesis by auto
        next
        assume "L \<noteq> Pos A"
        from this and `L = Pos A \<or> L = Neg A`have "L = Neg A" by auto
        from this and `validate_literal I L` have "A \<notin> I" by auto
        from this and `A \<in> Sel` have "A \<in> ?J" unfolding rename_interpretation_def by blast
        from this and `L = Neg A` and `rename_literal Sel L = complement L` show ?thesis by auto
      qed
      next
      assume "A \<notin> Sel"
      from this and `atom L = A` have "rename_literal Sel L = L"  
        unfolding rename_literal_def by auto
      show ?thesis 
      proof cases
        assume "L = Pos A" 
        from this and `validate_literal I L` have "A \<in> I" by auto
        from this and `A \<notin> Sel` have "A \<in> ?J" unfolding rename_interpretation_def by blast
        from this and `L = Pos A` and `rename_literal Sel L = L` show ?thesis by auto
        next
        assume "L \<noteq> Pos A"
        from this and `L = Pos A \<or> L = Neg A`have "L = Neg A" by auto
        from this and `validate_literal I L` have "A \<notin> I" by auto
        from this and `A \<notin> Sel` have "A \<notin> ?J" unfolding rename_interpretation_def by blast
        from this and `L = Neg A` and `rename_literal Sel L = L` show ?thesis by auto
      qed
   qed
qed

lemma renaming_preserves_satisfiability:
  assumes "satisfiable S"
  shows "satisfiable (rename_formula Sel S)"
proof -
  from assms obtain I where "validate_formula I S" unfolding satisfiable_def by auto
  let ?J = "rename_interpretation Sel I"
  have "validate_formula ?J (rename_formula Sel S)"
  proof (rule ccontr)
    assume "\<not>validate_formula ?J (rename_formula Sel S)"
    then obtain C where "C \<in> S" and "\<not>(validate_clause ?J (rename_clause Sel C))" 
    unfolding rename_formula_def by auto
    from `C \<in> S` and `validate_formula I S` obtain L where "L \<in> C" 
      and "validate_literal I L" by auto
    from `validate_literal I L` have "validate_literal ?J (rename_literal Sel L)" 
      using renaming_preserves_semantic by auto 
    from this and `L \<in> C` and `\<not>validate_clause ?J (rename_clause Sel C)` show "False" 
      unfolding rename_clause_def by auto
  qed
  from this show ?thesis unfolding satisfiable_def by auto
qed

lemma renaming_preserves_subsumption:
  assumes "subsumes C D"
  shows "subsumes (rename_clause Sel C) (rename_clause Sel D)"
using assms unfolding subsumes_def rename_clause_def by auto

section {* Soundness *}

text {* In this section we prove that all the rules introduced in the previous section are sound. 
We first introduce an abstract notion of soundness. *}

definition Sound :: "'at BinaryRule \<Rightarrow> bool"
where 
  "(Sound Rule) \<equiv> \<forall>I P1 P2 C. (Rule P1 P2 C \<longrightarrow> (validate_clause I P1) \<longrightarrow> (validate_clause I P2) 
    \<longrightarrow> (validate_clause I C))"

lemma soundness_and_entailment :
  assumes "Sound Rule"
  assumes "Rule P1 P2 C"
  assumes "P1 \<in> S"
  assumes "P2 \<in> S"
  shows "entails S C"
using Sound_def assms entails_def by auto

lemma all_deducible_sound:
  assumes "Sound R"
  shows "entails_formula S (all_deducible_clauses R S)"
proof (rule ccontr)
  assume "\<not>entails_formula S (all_deducible_clauses R S)"
  then obtain C where "C \<in> all_deducible_clauses R S" and "\<not> entails S C" 
    unfolding entails_formula_def by auto
  from `C \<in> all_deducible_clauses R S` obtain P1 P2 where "R P1 P2 C" and "P1 \<in> S" and "P2 \<in> S"    
    by auto
  from `R P1 P2 C`and assms(1) and `P1 \<in> S` and `P2 \<in> S` and `\<not> entails S C` 
    show "False" using soundness_and_entailment by auto
qed

lemma add_all_deducible_sound:
  assumes "Sound R"
  shows "entails_formula S (add_all_deducible_clauses R S)"
by (metis UnE add_all_deducible_clauses.simps all_deducible_sound assms 
      entails_formula_def entails_member)

text {* If a rule is more restrictive than a sound rule then it is necessarily sound. *}

lemma less_restrictive_correct:
  assumes "less_restrictive R1 R2"
  assumes "Sound R1"
  shows "Sound R2"
using assms unfolding less_restrictive_def Sound_def by blast

text {* We finally establish usual concrete soundness results. *}

theorem resolution_is_correct: 
  "(Sound resolvent)" 
proof (rule ccontr)
  assume "\<not> (Sound resolvent)"
  then obtain I P1 P2 C where  
    "resolvent P1 P2 C" "validate_clause I P1" "validate_clause I P2" and "\<not>validate_clause I C" 
    unfolding  Sound_def by blast
  from `resolvent P1 P2 C` obtain A where
      "(Pos A) \<in> P1" and "(Neg A) \<in> P2" and "C = ( (P1 - { Pos A}) \<union> (P2 - { Neg A }))"
      unfolding resolvent_def by auto 
  show "False" 
  proof cases
        assume "A \<in> I"
        hence "\<not>validate_literal I (Neg A)" by auto
        from `\<not>validate_literal I (Neg A)` and `validate_clause I P2` 
          have "validate_clause I (P2 - { Neg A })" by auto
        from `validate_clause I (P2 - { Neg A })` and `C = ( (P1 - { Pos A}) \<union> (P2 - { Neg A }))` 
          and `\<not>validate_clause I C` show "False" by auto
  next
        assume "A \<notin> I"
        hence "\<not>validate_literal I (Pos A)" by auto
        from `\<not>validate_literal I (Pos A)` and `validate_clause I P1` 
          have "validate_clause I (P1 - { Pos A })" by auto
        from `validate_clause I (P1 - { Pos A })` and `C = ( (P1 - { Pos A}) \<union> (P2 - { Neg A }))` 
          and `\<not>validate_clause I C`
          show "False" by auto
  qed 
qed

theorem ordered_resolution_correct : "Sound ordered_resolvent"
using resolution_is_correct and ordered_resolvent_is_resolvent  less_restrictive_correct  by auto 

theorem ordered_model_resolution_correct : "Sound (ordered_model_resolvent I)"
using resolution_is_correct ordered_model_resolvent_is_resolvent less_restrictive_correct by auto 

theorem ordered_positive_resolution_correct : "Sound ordered_positive_resolvent"
using less_restrictive_correct positive_resolvent_is_resolvent resolution_is_correct by auto

theorem ordered_negative_resolution_correct : "Sound ordered_negative_resolvent"
using less_restrictive_correct negative_resolvent_is_resolvent resolution_is_correct by auto

theorem unit_resolvent_correct : "Sound unit_resolvent"
using less_restrictive_correct resolution_is_correct unit_resolvent_is_resolvent by auto

section {* Refutational Completeness *}

text {* In this section we establish the refutational completeness of the previous inference 
rules (under adequate restrictions for the unit resolution rule). Completeness is proven
w.r.t.\ redundancy elimination rules, i.e., we show that every saturated unsatisfiable clause set
contains the empty clause. *}

text {* We first introduce an abstract notion of saturation. *}

definition saturated_binary_rule :: "'a BinaryRule \<Rightarrow> 'a Formula \<Rightarrow> bool"
where
  "(saturated_binary_rule Rule S) \<equiv> (\<forall> P1 P2 C. (((P1 \<in> S) \<and> (P2 \<in> S) \<and> (Rule P1 P2 C)))
    \<longrightarrow> redundant C S)"

definition Complete :: "'at BinaryRule \<Rightarrow> bool"
where 
  "(Complete Rule) = (\<forall>S. ((saturated_binary_rule Rule S) \<longrightarrow> (all_fulfill finite S) 
    \<longrightarrow> ({} \<notin> S) \<longrightarrow> satisfiable S))"

text {* If a set of clauses is saturated under some rule then it is necessarily saturated 
under more restrictive rules, which entails that if a rule is less restrictive than a complete rule 
then it is also complete.*}

lemma less_restrictive_saturated:
  assumes "less_restrictive R1 R2"
  assumes "saturated_binary_rule R1 S"
  shows "saturated_binary_rule R2 S"
using assms unfolding less_restrictive_def Complete_def saturated_binary_rule_def by blast

lemma less_restrictive_complete:
  assumes "less_restrictive R1 R2"
  assumes "Complete R2"
  shows "Complete R1"
using assms less_restrictive_saturated Complete_def by auto

subsection {* Ordered Resolution *}

text {* We define a function associating every set of clauses @{ term S } with a ``canonic'' 
interpretation constructed from @{ term S }.
If @{ term S } is saturated under ordered resolution and does not contain the empty clause
then the interpretation is a model of @{ term S }. The interpretation is defined by mean
of an auxiliary function that maps every atom to a function indicating whether the
atom occurs in the interpretation corresponding to a given clause set.
The auxiliary function is defined by induction on the set of atoms.
*}

function canonic_int_fun_ordered :: "'at \<Rightarrow> ('at Formula \<Rightarrow> bool)"
where
  "(canonic_int_fun_ordered A) = 
      (\<lambda>S. (\<exists> C. (C \<in> S) \<and> (strictly_maximal_literal C (Pos A) ) 
      \<and> ( \<forall> B. ( Pos B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering \<longrightarrow> (\<not>(canonic_int_fun_ordered B) S)))
      \<and> ( \<forall> B. ( Neg B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering \<longrightarrow> ((canonic_int_fun_ordered B) S)))))"
by auto 
termination apply (relation "atom_ordering")
by auto (simp add: atom_ordering_wf)

definition canonic_int_ordered :: "'at Formula \<Rightarrow> 'at Interpretation"
where
  "(canonic_int_ordered S) = { A. ((canonic_int_fun_ordered A) S) }"

text {* We first prove that the canonic interpretation validates every clause 
having a positive strictly maximal literal *}
 
lemma int_validate_cl_with_pos_max : 
  assumes "strictly_maximal_literal C (Pos A)"
  assumes "C \<in> S"
  shows "validate_clause (canonic_int_ordered S) C"
proof cases
    assume c1: "(\<forall> B. ( Pos B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering 
                  \<longrightarrow> (\<not>(canonic_int_fun_ordered B) S)))"
    show ?thesis
    proof cases
      assume c2: "( \<forall> B. ( Neg B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering 
                    \<longrightarrow> ((canonic_int_fun_ordered B) S)))"
      have "((canonic_int_fun_ordered A) S)" 
      proof (rule ccontr)
        assume "\<not> ((canonic_int_fun_ordered A) S)"
        from `\<not> ((canonic_int_fun_ordered A) S)`
        have e: "\<not> (\<exists> C. (C \<in> S) \<and> (strictly_maximal_literal C (Pos A) ) 
      \<and> ( \<forall> B. ( Pos B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering \<longrightarrow> (\<not>(canonic_int_fun_ordered B) S)))
      \<and> ( \<forall> B. ( Neg B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering \<longrightarrow> ((canonic_int_fun_ordered B) S))))"
        by ((simp only:canonic_int_fun_ordered.simps[of A]), blast)
        from e and c1 and c2 and `(C \<in> S)`and `(strictly_maximal_literal C (Pos A))`
        show "False" by blast
      qed
      from `((canonic_int_fun_ordered A) S)` have "A \<in> (canonic_int_ordered S)" 
        unfolding canonic_int_ordered_def by blast
      from `A \<in> (canonic_int_ordered S)` and `(strictly_maximal_literal C (Pos A))` 
        show "?thesis"
        unfolding strictly_maximal_literal_def by auto
    next
      assume not_c2: "\<not>( \<forall> B. ( Neg B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering 
                        \<longrightarrow> ((canonic_int_fun_ordered B) S)))"
      from not_c2 obtain B where "Neg B \<in> C" and "\<not>((canonic_int_fun_ordered B) S)"
      by blast
      from `\<not> ((canonic_int_fun_ordered B) S)` have "B \<notin> (canonic_int_ordered S)" 
        unfolding canonic_int_ordered_def by blast
      with `Neg B \<in> C` show "?thesis" by auto
    qed
  next
    assume not_c1: "\<not>(\<forall> B. ( Pos B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering 
                      \<longrightarrow> (\<not>(canonic_int_fun_ordered B) S)))"
    from not_c1 obtain B where "Pos B \<in> C" and "((canonic_int_fun_ordered B) S)"
      by blast
    from `((canonic_int_fun_ordered B) S)` have "B \<in> (canonic_int_ordered S)" 
      unfolding canonic_int_ordered_def by blast
    with `Pos B \<in> C` show "?thesis" by auto
qed

lemma strictly_maximal_literal_exists : 

  "\<forall>C. (((finite C) \<and> (card C) = n \<and> n \<noteq> 0 \<and> (\<not> (tautology C)))) 
    \<longrightarrow> (\<exists>A. (strictly_maximal_literal C A))" (is "?P n")

proof (induction n)
    show "(?P 0)"  by auto
    next
      fix n assume "?P n"
      show "?P (Suc n)"
      proof  
            fix C
            show "(finite C \<and> card C = Suc n \<and> Suc n \<noteq> 0 \<and> \<not> (tautology C)) 
              \<longrightarrow> (\<exists>A. (strictly_maximal_literal C A))"
            proof 
              assume "finite C \<and> card C = Suc n \<and> Suc n \<noteq> 0 \<and> \<not>(tautology C)"
              hence "(finite C)" and "(card C) = (Suc n)" and "(\<not> (tautology C))" by auto 
              have "C \<noteq> {}"
              proof
                assume "C = {}"
                from `finite C` and `C = {}` have "card C = 0" using card_0_eq by auto
                from `card C = 0` and `card C = Suc n` show "False" by auto
              qed
              then obtain L where "L \<in> C" by auto
              from `\<not>tautology C` have "\<not>tautology (C - { L })" using tautology_monotonous 
                by auto
              from `L \<in> C` and  `finite C` have "Suc (card (C - { L })) = card C" 
                using card_Suc_Diff1  by metis
              with `card C = Suc n` have "card (C - { L }) = n" by auto
             
              show "\<exists>A. (strictly_maximal_literal C A)"
              proof cases
                assume "card C = 1"
                  from this and  `card C = Suc n` have "n = 0" by auto
                  from this and `finite C` and `card (C - { L }) = n` have "C - { L } = {}" 
                    using card_0_eq by auto
                  from this and `L \<in> C` show ?thesis  unfolding strictly_maximal_literal_def by auto
                next
                assume "card C \<noteq> 1"
                  from `finite C` have "finite (C - { L })" by auto
                  from  `Suc (card (C - { L })) = card C` and `card C \<noteq> 1` 
                    and `(card (C - { L })) = n` have "n \<noteq> 0" by auto
                  from this and `finite (C - { L })` and `card (C - { L }) = n` 
                    and `\<not>tautology (C - { L })` and `?P n` 
                  obtain A where "strictly_maximal_literal (C - { L }) A" by metis
                  show "\<exists>M. strictly_maximal_literal C M" 
                  proof cases
                    assume "(atom L, atom A) \<in> atom_ordering"
                      from this have "literal_ordering L A" by auto            
                      from this and `strictly_maximal_literal (C - { L }) A` 
                        have "strictly_maximal_literal C A" 
                      unfolding strictly_maximal_literal_def by blast
                      thus ?thesis by auto
                    next 
                    assume "(atom L, atom A) \<notin> atom_ordering"
                      have l_cases: "L = (Pos (atom L)) \<or> L = (Neg (atom L))" 
                        by ((rule atom_property [of "(atom L)"]), auto)
                      have a_cases: "A = (Pos (atom A)) \<or> A = (Neg (atom A))" 
                        by ((rule atom_property [of "(atom A)"]), auto)
                      from l_cases and a_cases and`(strictly_maximal_literal (C - { L }) A)` 
                        and `\<not> (tautology C)` and `L \<in> C`  
                      have "atom L \<noteq> atom A" 
                      unfolding strictly_maximal_literal_def and tautology_def by auto
                      from this and `(atom L, atom A) \<notin> atom_ordering` and atom_ordering_total 
                        have "(atom A,atom L) \<in> atom_ordering" by auto
                      hence "literal_ordering A L" by auto
                      from this and `L \<in> C` and `strictly_maximal_literal (C - { L }) A` 
                        and literal_ordering_trans  
                      have "strictly_maximal_literal C L" unfolding strictly_maximal_literal_def
                      unfolding strictly_maximal_literal_def by blast
                      thus ?thesis by auto
                  qed
               qed
            qed
      qed
  qed

text {* We then deduce that all clauses are validated. *}

lemma canonic_int_validates_all_clauses : 
  assumes "saturated_binary_rule ordered_resolvent S"
  assumes "all_fulfill finite S"
  assumes "{} \<notin> S"
  assumes "C \<in> S"
  shows "validate_clause (canonic_int_ordered S) C"
proof cases
    assume "(tautology C)"
    thus ?thesis using tautologies_are_valid [of "C" "(canonic_int_ordered S)"] by auto
  next
    assume "\<not>tautology C"
    from `all_fulfill finite S` and `C \<in> S` have "finite C" using all_fulfill_def by auto
    from `{} \<notin> S` and `C \<in> S` and `finite C` have "card C \<noteq> 0" using card_0_eq by auto 
    from `\<not>tautology C` and `finite C` and `card C \<noteq> 0` obtain "L"
      where "strictly_maximal_literal C L" using strictly_maximal_literal_exists by blast
    obtain A where "A = atom L" by auto
  
  have inductive_lemma: 
    "\<forall>C L. ((C \<in> S) \<longrightarrow> (strictly_maximal_literal C L) \<longrightarrow> (A = (atom L))
      \<longrightarrow> (validate_clause (canonic_int_ordered S) C))" (is "(?Q A)")
  proof ((rule wf_induct [of "atom_ordering" "?Q" "A"]),(rule atom_ordering_wf))
      next
        fix x
        assume hyp_induct: "\<forall>y. (y,x) \<in> atom_ordering \<longrightarrow> (?Q y)"
        show "?Q x"
        proof (rule)+
        fix C L assume "C \<in> S" "strictly_maximal_literal C L" "x = (atom L)"
        show "validate_clause (canonic_int_ordered S) C"
        proof cases
          assume "L = Pos x"
          from `L = Pos x` and `strictly_maximal_literal C L` and `C \<in> S`
            show "validate_clause (canonic_int_ordered S) C" 
            using int_validate_cl_with_pos_max by auto
        next
          assume "L \<noteq> Pos x"
          have "L = (Neg x)" using `L \<noteq> Pos x` `x = atom L` atom_property by fastforce 
          show "(validate_clause (canonic_int_ordered S) C)" 
          proof (rule ccontr)
            assume  "\<not> (validate_clause(canonic_int_ordered S) C)"
            from `(L = (Neg x))` and `(strictly_maximal_literal C L)` 
              and `(\<not> (validate_clause (canonic_int_ordered S) C))`
            have "x \<in> canonic_int_ordered S" unfolding strictly_maximal_literal_def by auto
            from `x \<in> canonic_int_ordered S` have "(canonic_int_fun_ordered x) S" 
              unfolding canonic_int_ordered_def by blast
            from `(canonic_int_fun_ordered x) S` 
              have "(\<exists> C. (C \<in> S) \<and> (strictly_maximal_literal C (Pos x) ) 
            \<and> ( \<forall> B. ( Pos B \<in> C \<longrightarrow> (B, x) \<in> atom_ordering \<longrightarrow> (\<not>(canonic_int_fun_ordered B) S)))
            \<and> ( \<forall> B. ( Neg B \<in> C \<longrightarrow> (B, x) \<in> atom_ordering \<longrightarrow> ((canonic_int_fun_ordered B) S))))" 
              by (simp only: canonic_int_fun_ordered.simps [of x])
            then obtain D 
            where "(D \<in> S)" and "(strictly_maximal_literal D (Pos x))"
            and a: "( \<forall> B. ( Pos B \<in> D \<longrightarrow> (B, x) \<in> atom_ordering 
                  \<longrightarrow> (\<not>(canonic_int_fun_ordered B) S)))"
            and b: "( \<forall> B. ( Neg B \<in> D \<longrightarrow> (B, x) \<in> atom_ordering 
                      \<longrightarrow> ((canonic_int_fun_ordered B) S)))"
            by blast
            obtain R where "R = (resolvent_upon D C x)" by auto
            from `R = resolvent_upon D C x` and `strictly_maximal_literal D (Pos x)` 
              and `strictly_maximal_literal C L` and `L = (Neg x)` have "resolvent D C R" 
            unfolding strictly_maximal_literal_def using resolvent_upon_is_resolvent by auto

            from `R = resolvent_upon D C x` and `strictly_maximal_literal D (Pos x)` 
              and `strictly_maximal_literal C L` and `L = Neg x` 
              have "ordered_resolvent D C R" 
            using ordered_resolvent_upon_is_resolvent by auto

            have "\<not> validate_clause (canonic_int_ordered S) R"
            proof
              assume "validate_clause (canonic_int_ordered S) R"
              from `validate_clause (canonic_int_ordered S) R` obtain M 
                where "(M \<in> R)" and "validate_literal (canonic_int_ordered S) M" 
                by auto
              from `M \<in> R` and `R = resolvent_upon D C x` 
                have "(M \<in> (D - { Pos x })) \<or> (M \<in> (C - { Neg x }))" by auto
              thus "False"
              proof
                assume "M \<in> (D - { Pos x })"
                show "False"
                proof cases
                  assume "\<exists>AA. M = (Pos AA)"
                  from this obtain AA where "M = Pos AA" by auto
                  from `M \<in> D - { Pos x }` and `strictly_maximal_literal D (Pos x)` 
                    and `(M = Pos AA)`
                  have "(AA,x) \<in> atom_ordering" unfolding strictly_maximal_literal_def by auto
                  from a and `(AA,x) \<in> atom_ordering` and `M = (Pos AA)` and `M \<in> (D - { Pos x })`
                  have "\<not>(canonic_int_fun_ordered AA) S" by blast
                  from `\<not>(canonic_int_fun_ordered AA) S` have "AA \<notin> canonic_int_ordered S" 
                    unfolding canonic_int_ordered_def by blast
                  from `AA \<notin> canonic_int_ordered S` and `M = Pos AA` 
                    and `validate_literal (canonic_int_ordered S) M` 
                    show "False" by auto
                next
                  assume "\<not>(\<exists>AA. M = (Pos AA))"
                  obtain AA where "M = (Pos AA) \<or> M = (Neg AA)" using Literal.exhaust [of M] by auto
                  from this and `\<not>(\<exists>AA. M = (Pos AA))` have "M = (Neg AA)" by auto
                  from `M \<in> (D - { Pos x })` and `strictly_maximal_literal D (Pos x)` 
                    and `M = (Neg AA)`
                  have "(AA,x) \<in> atom_ordering" unfolding strictly_maximal_literal_def by auto
                  from b and `(AA,x) \<in> atom_ordering` and `M = (Neg AA)` and `M \<in> (D - { Pos x })`
                  have "(canonic_int_fun_ordered AA) S" by blast
                  from `(canonic_int_fun_ordered AA) S` have "AA \<in> canonic_int_ordered S"
                    unfolding canonic_int_ordered_def by blast
                  from `AA \<in> canonic_int_ordered S` and `M = (Neg AA)` 
                    and `validate_literal (canonic_int_ordered S) M` show "False" by auto
                qed
              next
                assume "M \<in> (C - { Neg x })"
                from `\<not>validate_clause(canonic_int_ordered S) C` and `M \<in> (C - { Neg x })`
                and `validate_literal (canonic_int_ordered S) M` show "False" by auto
              qed
            qed  
            from `\<not>validate_clause (canonic_int_ordered S) R` have "\<not>tautology R" 
              using tautologies_are_valid by auto
            from `ordered_resolvent D C R` and `D \<in> S` and `C \<in> S` 
              and `saturated_binary_rule ordered_resolvent S` 
              have "redundant R S" unfolding saturated_binary_rule_def  by auto
            from this and `\<not>tautology R` obtain R' where "R' \<in> S" and "subsumes R' R" 
              unfolding redundant_def by auto
            from `R = resolvent_upon D C x` and `strictly_maximal_literal D (Pos x)` 
              and `strictly_maximal_literal C L` and `L = (Neg x)` 
            have "resolvent D C R" unfolding strictly_maximal_literal_def 
              using resolvent_upon_is_resolvent by auto
            from `all_fulfill finite S` and `C \<in> S` have "finite C" using all_fulfill_def by auto
            from `all_fulfill finite S` and `D \<in> S` have "finite D" using all_fulfill_def by auto
            from `finite C` and `finite D` and  `(resolvent D C R)` have "finite R" 
            using resolvent_is_finite unfolding derived_clauses_are_finite_def  by blast
            from `finite R` and `subsumes R' R` have "finite R'" unfolding subsumes_def 
            using finite_subset by auto
            from `R' \<in> S` and `{} \<notin> S` and `(subsumes R' R)` have "R' \<noteq> {}" 
              unfolding subsumes_def by auto
            from `finite R'` and `R' \<noteq> {}` have "card R' \<noteq> 0" using card_0_eq by auto
            from `subsumes R' R` and `\<not>tautology R` have "\<not>tautology R'" 
              unfolding subsumes_def 
              using tautology_monotonous by auto
            from `\<not>tautology R'` and `finite R'`  and `card R' \<noteq> 0` obtain "LR'" 
              where "strictly_maximal_literal R' LR'" using strictly_maximal_literal_exists 
              by blast
            from `finite R` and `finite R'` and `card R' \<noteq> 0` and `subsumes R' R` 
              have "card R \<noteq> 0" 
              unfolding subsumes_def by auto
            from `\<not>tautology R` and `finite R`  and `card R \<noteq> 0` obtain "LR" 
              where "strictly_maximal_literal R LR" using strictly_maximal_literal_exists by blast
            obtain AR and AR' where "AR = atom LR" and "AR' = atom LR'" by auto
            from `subsumes R' R` and `AR = atom LR` and `AR' = atom LR'` 
              and `(strictly_maximal_literal R LR)`
              and `(strictly_maximal_literal R' LR')` have "(AR' = AR) \<or> (AR',AR) \<in> atom_ordering" 
              using subsumption_and_max_literal by auto
            from `R = (resolvent_upon D C x)` and `AR = atom LR` 
              and `strictly_maximal_literal R LR` 
              and `strictly_maximal_literal D (Pos x)` 
              and `strictly_maximal_literal C L` and `L = (Neg x)`
            have "(AR,x) \<in> atom_ordering" using resolution_and_max_literal by auto
            from `(AR,x) \<in> atom_ordering` and `(AR' = AR) \<or> (AR',AR) \<in> atom_ordering` 
              have "(AR',x) \<in> atom_ordering" using atom_ordering_trans by auto
            from this and hyp_induct and `R' \<in> S` and `strictly_maximal_literal R' LR'` 
              and `AR' = atom LR'` have "validate_clause (canonic_int_ordered S) R'" by auto
            from this and `subsumes R' R` and `\<not>validate_clause (canonic_int_ordered S) R` 
            show "False" using subsumption_and_semantics by blast
          qed
        qed
      qed
  qed
  from inductive_lemma and `C \<in> S` and `strictly_maximal_literal C L` and `A = atom L` show ?thesis by blast
qed

theorem ordered_resolution_is_complete :
  "Complete ordered_resolvent"
proof (rule ccontr)
  assume "\<not> Complete ordered_resolvent"
  then obtain S where "saturated_binary_rule ordered_resolvent S"
    and "all_fulfill finite S" and "{} \<notin> S" and "\<not>satisfiable S" unfolding Complete_def by auto
  have "validate_formula (canonic_int_ordered S) S"
  proof (rule ccontr)
    assume "\<not>validate_formula (canonic_int_ordered S) S"
    from this obtain C where "C \<in> S" and "\<not>validate_clause (canonic_int_ordered S) C" by auto
    from `saturated_binary_rule ordered_resolvent S` and `all_fulfill finite S` and `{} \<notin> S` 
      and `C \<in> S` and `\<not>validate_clause (canonic_int_ordered S) C` 
      show "False" using canonic_int_validates_all_clauses by auto
  qed
  from `validate_formula (canonic_int_ordered S) S` and `\<not>satisfiable S` show "False" 
    unfolding satisfiable_def by blast
qed

subsection {* Ordered Resolution with Selection *}

text {* We now consider the case where some negative literals are considered with highest priority. 
The proof reuses the canonic interpretation defined in the previous section. 
The interpretation is constructed using only clauses with no selected literals. By the previous 
result, all such clauses must be satisfied. We then show that the property carries over to the 
clauses with non empty selected part. *}

definition "empty_selected_part Sel S = { C. C \<in> S \<and> (selected_part Sel C) = {} }"

lemma saturated_ordered_sel_res_empty_sel : 
  assumes "saturated_binary_rule (ordered_sel_resolvent Sel) S"
  shows "saturated_binary_rule ordered_resolvent (empty_selected_part Sel S)"
proof -
  show ?thesis
  proof (rule ccontr)
    assume "\<not>saturated_binary_rule ordered_resolvent (empty_selected_part Sel S)"
    then obtain P1 and P2 and C
    where "P1 \<in> empty_selected_part Sel S" and "P2 \<in> empty_selected_part Sel S" 
      and "ordered_resolvent P1 P2 C"
      and "\<not>redundant C (empty_selected_part Sel S)"
    unfolding "saturated_binary_rule_def" by auto
    from `ordered_resolvent P1 P2 C` obtain A where "C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A }))"
      and "strictly_maximal_literal P1 (Pos A)" and  "strictly_maximal_literal P2 (Neg A)"
      unfolding ordered_resolvent_def by auto
    from  `P1 \<in> empty_selected_part Sel S` have "selected_part Sel P1 = {}"
    unfolding empty_selected_part_def by auto
    from  `P2 \<in> empty_selected_part Sel S` have "selected_part Sel P2 = {}"
    unfolding empty_selected_part_def by auto
    from `C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A }))` and `strictly_maximal_literal P1 (Pos A)` 
    and `strictly_maximal_literal P2 (Neg A)` and `(selected_part Sel P1) = {}` 
    and `selected_part Sel P2 = {}`
    have "ordered_sel_resolvent Sel P1 P2 C" unfolding ordered_sel_resolvent_def by auto
    from `saturated_binary_rule (ordered_sel_resolvent Sel) S`  
    have "\<forall>P1 P2 C. (P1 \<in> S \<and> P2 \<in> S \<and> (ordered_sel_resolvent Sel P1 P2 C)) \<longrightarrow> redundant C S" 
    unfolding saturated_binary_rule_def  by auto
    from this and `P1 \<in> (empty_selected_part Sel S)` and `P2 \<in> (empty_selected_part Sel S)` 
    and `ordered_sel_resolvent Sel P1 P2 C` have "tautology C \<or> (\<exists>D. D \<in> S \<and> subsumes D C)"
    unfolding empty_selected_part_def redundant_def by auto
    from this and `tautology C \<or> (\<exists>D. D \<in> S \<and> subsumes D C)` 
      and `\<not>redundant C (empty_selected_part Sel S)` 
      obtain D where "D \<in> S" and "subsumes D C" and "D \<notin> empty_selected_part Sel S" 
      unfolding redundant_def by auto
    from `D \<notin> empty_selected_part Sel S` and `D \<in> S` obtain B where "B \<in> Sel" and "Neg B \<in> D" 
    unfolding empty_selected_part_def selected_part_def by auto
    from `Neg B \<in> D` this and `subsumes D C` have "Neg B \<in> C" unfolding subsumes_def by auto
    from this and `C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A }))` have "Neg B \<in> (P1 \<union> P2)" by auto
    from `Neg B \<in> (P1 \<union> P2)` and `P1 \<in> empty_selected_part Sel S` 
      and `P2 \<in> empty_selected_part Sel S` and `B \<in> Sel` show "False" 
      unfolding empty_selected_part_def selected_part_def by auto
  qed  
qed

definition ordered_sel_resolvent_upon :: "'at set \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at Clause \<Rightarrow> 'at \<Rightarrow> bool" 
  where
  "ordered_sel_resolvent_upon Sel P1 P2 C A \<equiv> 
    (((C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A })))
      \<and> (strictly_maximal_literal P1 (Pos A)) \<and> ((selected_part Sel P1) = {}) 
      \<and> ( ((strictly_maximal_literal P2 (Neg A)) \<and> (selected_part Sel P2) = {})
         \<or> (strictly_maximal_literal (selected_part Sel P2) (Neg A)))))"

lemma ordered_sel_resolvent_upon_is_resolvent:
  assumes "ordered_sel_resolvent_upon Sel P1 P2 C A"
  shows "ordered_sel_resolvent Sel P1 P2 C"
using assms unfolding ordered_sel_resolvent_upon_def and ordered_sel_resolvent_def by auto

lemma resolution_decreases_selected_part:
  assumes "ordered_sel_resolvent_upon Sel P1 P2 C A"
  assumes "Neg A \<in> P2"
  assumes "finite P1"
  assumes "finite P2"
  assumes "card (selected_part Sel P2) = Suc n"
  shows "card (selected_part Sel C) = n"
proof -
  from `finite P2` have "finite (selected_part Sel P2)" unfolding selected_part_def by auto
  from `card (selected_part Sel P2) = (Suc n)` have "card (selected_part Sel P2) \<noteq> 0" by auto
  from this and `finite (selected_part Sel P2)` have "selected_part Sel P2 \<noteq> {}" 
  using card_0_eq by auto
  from this and `ordered_sel_resolvent_upon Sel P1 P2 C A` have 
    "C = (P1 - { Pos A}) \<union> ( P2 - { Neg A })"
      and "selected_part Sel P1 = {}" and  "strictly_maximal_literal (selected_part Sel P2) (Neg A)"
      unfolding ordered_sel_resolvent_upon_def by auto
  from `strictly_maximal_literal (selected_part Sel P2) (Neg A)` 
    have "Neg A \<in> selected_part Sel P2"
    unfolding strictly_maximal_literal_def by auto 
  from this have "A \<in> Sel" unfolding selected_part_def by auto
  from `selected_part Sel P1 = {}` have "selected_part Sel (P1 - { Pos A}) = {}" 
    unfolding selected_part_def by auto
  from `Neg A \<in> (selected_part Sel P2)` 
    have "selected_part Sel (P2 - { Neg A}) = (selected_part Sel P2) - { Neg A }" 
  unfolding selected_part_def by auto
  from `C = ( (P1 - { Pos A}) \<union> ( P2 - { Neg A }))` have
  "selected_part Sel C 
    = (selected_part Sel (P1 - { Pos A})) \<union> (selected_part Sel (P2 - { Neg A}))"
  unfolding selected_part_def by auto
  from this and `selected_part Sel (P1 - { Pos A}) = {}`
    and `selected_part Sel (P2 - { Neg A}) = selected_part Sel P2 - { Neg A }`
  have "selected_part Sel C = selected_part Sel P2 - { Neg A }" by auto
  from `Neg A \<in> P2` and `A \<in> Sel` have "Neg A \<in> selected_part Sel P2" 
    unfolding selected_part_def by auto
  from this and `selected_part Sel C = (selected_part Sel P2) - { Neg A }` 
    and `finite (selected_part Sel P2)`
  have "card (selected_part Sel C) = card (selected_part Sel P2) - 1" by auto
  from this and `card (selected_part Sel P2) = Suc n` show ?thesis by auto
qed

lemma canonic_int_validates_all_clauses_sel : 
  assumes "saturated_binary_rule (ordered_sel_resolvent Sel) S"
  assumes "all_fulfill finite S"
  assumes "{} \<notin> S"
  assumes "C \<in> S"
  shows "validate_clause (canonic_int_ordered (empty_selected_part Sel S)) C"
proof -
  let ?nat_order = "{ (x::nat,y::nat). x < y}"
  let ?SE = "empty_selected_part Sel S"
  let ?I = "canonic_int_ordered ?SE"
  obtain n where "n = card (selected_part Sel C)" by auto
  have "\<forall>C. card (selected_part Sel C) = n \<longrightarrow> C \<in> S \<longrightarrow> validate_clause ?I C" (is "?P n")
  proof ((rule wf_induct [of ?nat_order ?P n]), (simp add:wf))
  next
    fix n assume ind_hyp: "\<forall>m. (m,n) \<in> ?nat_order \<longrightarrow> (?P m)"
    show "(?P n)"
    proof (rule+)
      fix C assume "card (selected_part Sel C) = n" and "C \<in> S"
      from `all_fulfill finite S` and `C \<in> S` have "finite C" unfolding all_fulfill_def by auto 
      from this have "finite (selected_part Sel C)" unfolding selected_part_def by auto
      show "validate_clause ?I  C"
      proof (rule nat.exhaust [of "n"])
        assume "n = 0"
        from this and `card (selected_part Sel C) = n` and `finite (selected_part Sel C)`
          have "selected_part Sel C = {}" by auto
        from `saturated_binary_rule (ordered_sel_resolvent Sel) S` 
          have "saturated_binary_rule ordered_resolvent ?SE" 
          using saturated_ordered_sel_res_empty_sel by auto
        from `{} \<notin> S` have "{} \<notin> ?SE" unfolding empty_selected_part_def by auto
        from `selected_part Sel C = {}` `C \<in> S` have "C \<in> ?SE" unfolding empty_selected_part_def 
          by auto
        from `all_fulfill finite S` have "all_fulfill finite ?SE" 
          unfolding empty_selected_part_def all_fulfill_def by auto
        from this  and `saturated_binary_rule ordered_resolvent ?SE` and `{} \<notin> ?SE` and `C \<in> ?SE` 
        show "validate_clause ?I C" using canonic_int_validates_all_clauses by auto
      next
        fix m assume "n = Suc m"
        from this and `card (selected_part Sel C) = n` have "selected_part Sel C \<noteq> {}" by auto
        show "validate_clause ?I C" 
        proof (rule ccontr)
          assume "\<not>validate_clause ?I C"
          show "False"
          proof (cases)
            assume "tautology C" 
            from `tautology C` and `\<not>validate_clause ?I C` show "False" 
              using tautologies_are_valid by auto
          next
            assume "\<not>(tautology C)"
            hence "\<not>(tautology (selected_part Sel C))" 
              unfolding selected_part_def tautology_def by auto
            from `selected_part Sel C \<noteq> {}` and `finite (selected_part Sel C)` 
              have "card (selected_part Sel C) \<noteq> 0" by auto
            from this and `\<not>(tautology (selected_part Sel C))` and `finite (selected_part Sel C)` 
              obtain L where "strictly_maximal_literal (selected_part Sel C) L" 
              using strictly_maximal_literal_exists [of "card (selected_part Sel C)"] by blast
            from `strictly_maximal_literal (selected_part Sel C) L` have "L \<in> (selected_part Sel C)" 
              and "L \<in> C" unfolding strictly_maximal_literal_def selected_part_def by auto
            from this and `\<not>validate_clause ?I C` have "\<not>(validate_literal ?I L)" by auto
            from `L \<in> (selected_part Sel C)` obtain A where "L = (Neg A)" and "A \<in> Sel" 
              unfolding selected_part_def by auto
            from `\<not>(validate_literal ?I L)` and `L = (Neg A)` have "A \<in> ?I" by auto
            from this have "((canonic_int_fun_ordered A) ?SE)" unfolding canonic_int_ordered_def 
              by blast
            have "((\<exists> C. (C \<in> ?SE) \<and> (strictly_maximal_literal C (Pos A) ) 
                \<and> ( \<forall> B. ( Pos B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering 
                  \<longrightarrow> (\<not>(canonic_int_fun_ordered B) ?SE)))
                \<and> ( \<forall> B. ( Neg B \<in> C \<longrightarrow> (B, A) \<in> atom_ordering 
                  \<longrightarrow> ((canonic_int_fun_ordered B) ?SE)))))" (is ?exp)
            proof (rule ccontr)                
                assume "\<not> ?exp"
                from this have "\<not>((canonic_int_fun_ordered A) ?SE)" 
                  by ((simp only:canonic_int_fun_ordered.simps [of A]), blast)
                from this and `(canonic_int_fun_ordered A) ?SE` show "False" by blast
            qed
            then obtain D where 
                "D \<in> ?SE" and "strictly_maximal_literal D (Pos A)" 
                and c1: "( \<forall> B. ( Pos B \<in> D \<longrightarrow> (B, A) \<in> atom_ordering 
                  \<longrightarrow> (\<not>(canonic_int_fun_ordered B) ?SE)))"
                and c2: "( \<forall> B. ( Neg B \<in> D \<longrightarrow> (B, A) \<in> atom_ordering 
                  \<longrightarrow> ((canonic_int_fun_ordered B) ?SE)))"
                by blast
            from `D \<in> ?SE` have "(selected_part Sel D) = {}" and "D \<in> S" 
              unfolding empty_selected_part_def by auto
            from `D \<in> ?SE` and `all_fulfill finite S` have "finite D" 
              unfolding empty_selected_part_def all_fulfill_def by auto
            let ?R = "(D - { Pos A }) \<union> (C - { Neg A })"
              from `strictly_maximal_literal D (Pos A)` 
                and `strictly_maximal_literal (selected_part Sel C) L` 
                and `L = (Neg A)` and `(selected_part Sel D) = {}`
              have "(ordered_sel_resolvent_upon Sel D C ?R A)" 
                unfolding ordered_sel_resolvent_upon_def by auto
              from this have "ordered_sel_resolvent Sel D C ?R" 
                by (rule ordered_sel_resolvent_upon_is_resolvent)
              from `(ordered_sel_resolvent_upon Sel D C ?R A)` `(card (selected_part Sel C)) = n` 
                and `n = Suc m` and `L \<in> C` and `L = (Neg A)` and `finite D` and `finite C`
                have "card (selected_part Sel ?R) = m" 
                using resolution_decreases_selected_part by auto
              from `ordered_sel_resolvent Sel D C ?R` and `D \<in> S`and `C \<in> S` 
                and `saturated_binary_rule (ordered_sel_resolvent Sel) S`
                have "redundant ?R S" unfolding saturated_binary_rule_def by auto
              hence "tautology ?R \<or> (\<exists>RR. (RR \<in> S \<and> (subsumes RR ?R)))" 
                unfolding redundant_def by auto  
              hence "validate_clause ?I ?R"
              proof 
                assume "tautology ?R"
                thus "validate_clause ?I ?R" by (rule tautologies_are_valid)
              next
                assume "\<exists>R'. R' \<in> S \<and> (subsumes R' ?R)"
                then obtain R' where "R' \<in> S" and "subsumes R' ?R" by auto
                from `finite C`and `finite D` have "finite ?R" by auto
                from this have "finite (selected_part Sel ?R)" unfolding selected_part_def by auto
                from `subsumes R' ?R` have "selected_part Sel R' \<subseteq> selected_part Sel ?R" 
                  unfolding selected_part_def and subsumes_def by auto
                from this and `finite (selected_part Sel ?R)` 
                  have "card (selected_part Sel R') \<le> card (selected_part Sel ?R)" 
                  using card_mono by auto
                from this and `card (selected_part Sel ?R) = m` and `n = Suc m` 
                  have "card (selected_part Sel R') < n" by auto
                from this and ind_hyp and `R' \<in> S` have "validate_clause ?I R'" by auto
                from this and `subsumes R' ?R` show "validate_clause ?I ?R" 
                  using subsumption_and_semantics [of R' ?R ?I] by auto
              qed
              from this obtain L' where "L' \<in> ?R" and "validate_literal ?I L'" by auto
              have "L' \<notin> D - { Pos A }" 
              proof 
                assume "L' \<in> D - { Pos A }"
                from this have "L' \<in> D" by auto
                let ?A' = "atom L'"
                have "L' = (Pos ?A') \<or> L' = (Neg ?A')" using atom_property [of ?A' L'] by auto
                thus "False"
                proof
                  assume "L' = (Pos ?A')" 
                  from this and `strictly_maximal_literal D (Pos A)` and `L' \<in> D - { Pos A }`
                  have "(?A',A) \<in> atom_ordering" unfolding strictly_maximal_literal_def by auto
                  from c1 
                  have c1': "Pos ?A' \<in> D \<longrightarrow> (?A', A) \<in> atom_ordering 
                                \<longrightarrow> (\<not>(canonic_int_fun_ordered ?A') ?SE)"
                    by blast
                  from `L' \<in> D` and `L' = Pos ?A'` have "Pos ?A' \<in> D" by auto 
                  from c1' and `Pos ?A' \<in> D` and `(?A',A) \<in> atom_ordering`  
                  have "\<not>(canonic_int_fun_ordered ?A') ?SE" by blast
                  from this have "?A' \<notin> ?I" unfolding canonic_int_ordered_def by blast
                  from this have "\<not>(validate_literal ?I (Pos ?A'))" by auto
                  from this and `L' = Pos ?A'` and `validate_literal ?I L'` show "False" by auto
                next
                  assume "L' = Neg ?A'" 
                  from this and `strictly_maximal_literal D (Pos A)` and `L' \<in> D - { Pos A }`
                  have "(?A',A) \<in> atom_ordering" unfolding strictly_maximal_literal_def by auto
                  from c2 
                    have c2': "Neg ?A' \<in> D \<longrightarrow> (?A', A) \<in> atom_ordering 
                      \<longrightarrow> (canonic_int_fun_ordered ?A') ?SE"
                    by blast
                  from `L' \<in> D` and `L' = (Neg ?A')` have "Neg ?A' \<in> D" by auto 
                  from c2' and `Neg ?A' \<in> D` and `(?A',A) \<in> atom_ordering`  
                  have "(canonic_int_fun_ordered ?A') ?SE" by blast
                  from this have "?A' \<in> ?I" unfolding canonic_int_ordered_def by blast
                  from this have "\<not>validate_literal ?I (Neg ?A')" by auto
                  from this and `L' = Neg ?A'` and `validate_literal ?I L'` show "False" by auto
                qed
             qed
           from this and `L' \<in> ?R` have "L' \<in> C" by auto
           from this and `validate_literal ?I L'` and `\<not>validate_clause ?I C` show "False" by auto
         qed
      qed
    qed
  qed
 qed
 from `?P n` and `n = card (selected_part Sel C)` and `C \<in> S` show ?thesis by auto
qed

theorem ordered_resolution_is_complete_ordered_sel : 
  "Complete (ordered_sel_resolvent Sel)"
proof (rule ccontr)
  assume "\<not>Complete (ordered_sel_resolvent Sel)"
  then obtain S where "saturated_binary_rule (ordered_sel_resolvent Sel) S"
    and "all_fulfill finite S"
    and "{} \<notin> S"
    and "\<not>satisfiable S" unfolding Complete_def by auto
  let ?SE = "empty_selected_part Sel S"
  let ?I = "canonic_int_ordered ?SE"
  have "validate_formula ?I S"
  proof (rule ccontr)
    assume "\<not>(validate_formula ?I S)"
    from this obtain C where "C \<in> S" and "\<not>(validate_clause ?I C)" by auto
    from `saturated_binary_rule (ordered_sel_resolvent Sel) S` and `all_fulfill finite S` 
      and `{} \<notin> S` and `C \<in> S` and `\<not>(validate_clause ?I C)` 
    show "False" using canonic_int_validates_all_clauses_sel [of Sel S C] by auto
  qed
  from `(validate_formula ?I S)` and `\<not>(satisfiable S)` show "False" 
    unfolding satisfiable_def by blast
qed

subsection {* Semantic Resolution *}

text {* We show that under some particular renaming, model resolution simulates ordered resolution 
where all negative literals are selected, which immediately entails the refutational completeness 
of model resolution. *}

lemma ordered_res_with_selection_is_model_res :
  assumes "ordered_sel_resolvent UNIV P1 P2 C"
  shows "ordered_model_resolvent Sel (rename_clause Sel P1) (rename_clause Sel P2) 
            (rename_clause Sel C)"
proof -
  from assms obtain A 
  where c_def: "C = ((P1 - { Pos A }) \<union> (P2 - { Neg A }))"
    and "selected_part UNIV P1 = {}" 
    and "strictly_maximal_literal P1 (Pos A)"
    and disj: "((strictly_maximal_literal P2 (Neg A)) \<and> (selected_part UNIV P2) = {}) 
      \<or> strictly_maximal_literal (selected_part UNIV P2) (Neg A)"
  unfolding ordered_sel_resolvent_def by blast
  have "rename_clause Sel ((P1 - { Pos A }) \<union> (P2 - { Neg A })) 
    =  (rename_clause Sel (P1 - { Pos A })) \<union> rename_clause Sel (P2 - { (Neg A) })"
  using rename_union [of Sel "P1 - { Pos A }" "P2 - { Neg A }"] by auto 
  from this and c_def have ren_c: "(rename_clause Sel C) =
    (rename_clause Sel (P1 - { Pos A })) \<union> rename_clause Sel (P2 - { (Neg A) })" by auto
  have m1: "(rename_clause Sel (P1 - { Pos A })) = (rename_clause Sel P1) 
              - { rename_literal Sel (Pos A) }" 
    using renaming_set_minus by auto
  have m2: "rename_clause Sel (P2 - { Neg A }) = (rename_clause Sel P2) 
              - { rename_literal Sel (Neg A) }" 
    using renaming_set_minus by auto
  from m1 and m2 and ren_c have 
  rc_def: "(rename_clause Sel C) = 
    ((rename_clause Sel P1) - { rename_literal Sel (Pos A) })
    \<union> ((rename_clause Sel P2) - { rename_literal Sel (Neg A)  })"
  by auto
  have "\<not>((strictly_maximal_literal P2 (Neg A)) \<and> (selected_part UNIV P2) = {})"
  proof
    assume "(strictly_maximal_literal P2 (Neg A)) \<and> (selected_part UNIV P2) = {}"
    from this have "strictly_maximal_literal P2 (Neg A)" and "selected_part UNIV P2 = {}" by auto
    from `strictly_maximal_literal P2 (Neg A)` have "Neg A \<in> P2" 
      unfolding strictly_maximal_literal_def by auto
    from this and `selected_part UNIV P2 = {}` show "False" unfolding selected_part_def by auto
  qed
  from this and disj have "strictly_maximal_literal (selected_part UNIV P2) (Neg A)" by auto
  from this have "strictly_maximal_literal (rename_clause Sel (validated_part Sel (rename_clause Sel P2))) (Neg A)" 
    using renaming_and_selected_part by auto
  from this have 
    "strictly_maximal_literal (rename_clause Sel (rename_clause Sel (validated_part Sel (rename_clause Sel P2)))) 
        (rename_literal Sel (Neg A))" using renaming_preserves_strictly_maximal_literal by auto
  from this have 
    p1: "strictly_maximal_literal (validated_part Sel (rename_clause Sel P2)) 
      (rename_literal Sel (Neg A))" 
    using inverse_clause_renaming  by auto 
  from `strictly_maximal_literal P1 (Pos A)`
  have p2: "strictly_maximal_literal (rename_clause Sel P1) (rename_literal Sel (Pos A))" 
    using renaming_preserves_strictly_maximal_literal by auto
  from `(selected_part UNIV P1) = {}` have 
    "rename_clause Sel (validated_part Sel (rename_clause Sel P1)) = {}" 
    using renaming_and_selected_part by auto
  from this have q: "validated_part Sel (rename_clause Sel P1) = {}"   
    unfolding rename_clause_def by auto
  have r: "rename_literal Sel (Neg A) = complement (rename_literal Sel (Pos A))" 
    unfolding rename_literal_def by auto
  from r and q and p1 and p2 and rc_def show 
    "ordered_model_resolvent Sel (rename_clause Sel P1) (rename_clause Sel P2)(rename_clause Sel C)" 
    using ordered_model_resolvent_def [of Sel "rename_clause Sel P1" "rename_clause Sel P2" 
      "rename_clause Sel C"] by auto
qed

theorem ordered_resolution_is_complete_model_resolution:
  "Complete (ordered_model_resolvent Sel)"
proof (rule ccontr)
  assume "\<not>Complete (ordered_model_resolvent Sel)"
  then obtain S where "saturated_binary_rule (ordered_model_resolvent Sel) S"
    and "{} \<notin> S" and "all_fulfill finite S" and "\<not>(satisfiable S)" unfolding Complete_def by auto
  let ?S' = "rename_formula Sel S"
  have "{} \<notin> ?S'"
  proof
    assume "{} \<in> ?S'"
    then obtain V where "V \<in> S" and "rename_clause Sel V = {}" unfolding rename_formula_def by auto
    from `rename_clause Sel V = {}` have "V = {}" unfolding rename_clause_def by auto
    from this and `V \<in> S`  and `{} \<notin> S` show "False" by auto
  qed
  from `all_fulfill finite S` have "all_fulfill finite ?S'" 
  unfolding all_fulfill_def rename_formula_def rename_clause_def by auto
  have "saturated_binary_rule (ordered_sel_resolvent UNIV) ?S'"
  proof (rule ccontr)
    assume "\<not>(saturated_binary_rule (ordered_sel_resolvent UNIV) ?S')"
    from this obtain P1 and P2 and C where "P1 \<in> ?S'" and "P2 \<in> ?S'" 
      and "ordered_sel_resolvent UNIV P1 P2 C" and "\<not>tautology C" 
      and not_subsumed: "\<forall>D. (D \<in> ?S' \<longrightarrow> \<not>subsumes D C)" 
      unfolding saturated_binary_rule_def redundant_def by auto  
    from `ordered_sel_resolvent UNIV P1 P2 C` 
      have ord_ren: "ordered_model_resolvent Sel (rename_clause Sel P1) (rename_clause Sel P2) 
                        (rename_clause Sel C)" 
      using ordered_res_with_selection_is_model_res by auto
    have "\<not>tautology (rename_clause Sel C)" 
      using renaming_preserves_tautology inverse_clause_renaming 
      by (metis `\<not> tautology C` inverse_clause_renaming renaming_preserves_tautology)
    from `P1 \<in> ?S'` have "rename_clause Sel P1 \<in> rename_formula Sel ?S'" 
      unfolding rename_formula_def by auto
    hence "rename_clause Sel P1 \<in> S" using inverse_formula_renaming by auto
    from `P2 \<in> ?S'` have "rename_clause Sel P2 \<in> rename_formula Sel ?S'" 
      unfolding rename_formula_def by auto
    hence "rename_clause Sel P2 \<in> S" using inverse_formula_renaming by auto
    from `\<not>tautology (rename_clause Sel C)` and ord_ren 
      and `saturated_binary_rule (ordered_model_resolvent Sel) S` 
      and `rename_clause Sel P1 \<in> S` and `rename_clause Sel P2 \<in> S` 
      obtain D' where "D' \<in> S" and "subsumes D' (rename_clause Sel C)" 
      unfolding saturated_binary_rule_def redundant_def by blast
    from `subsumes D' (rename_clause Sel C)` 
      have "subsumes (rename_clause Sel D') (rename_clause Sel (rename_clause Sel C))" 
      using renaming_preserves_subsumption by auto
    hence "subsumes (rename_clause Sel D') C" using inverse_clause_renaming by auto
    from `D' \<in> S` have "rename_clause Sel D' \<in> ?S'" unfolding rename_formula_def by auto
    from this and not_subsumed and  `subsumes (rename_clause Sel D') C` show "False" by auto
  qed
  from this and `{} \<notin> ?S'` and `all_fulfill finite ?S'` have "satisfiable ?S'" 
    using ordered_resolution_is_complete_ordered_sel unfolding Complete_def by auto
  hence "satisfiable (rename_formula Sel ?S')" using renaming_preserves_satisfiability  by auto
  from this and `\<not>satisfiable S` show "False" using inverse_formula_renaming by auto
qed

subsection {* Positive and Negative Resolution *}

text {* We show that positive and negative resolution simulate model resolution 
with some specific interpretation. Then completeness follows from previous results. *}

lemma empty_interpretation_validate :
  "validate_literal {} L = (\<exists>A. (L = Neg A))"
by (meson empty_iff validate_literal.elims(2) validate_literal.simps(2))

lemma universal_interpretation_validate :
  "validate_literal UNIV L = (\<exists>A. (L = Pos A))"
by (meson UNIV_I validate_literal.elims(2) validate_literal.simps(1))

lemma negative_part_lemma:
  "(negative_part C) = (validated_part {} C)"
unfolding negative_part_def validated_part_def using empty_interpretation_validate by blast

lemma positive_part_lemma:
  "(positive_part C) = (validated_part UNIV C)"
unfolding positive_part_def validated_part_def using universal_interpretation_validate by blast

lemma negative_resolvent_is_model_res:
  "less_restrictive ordered_negative_resolvent (ordered_model_resolvent UNIV)"
unfolding ordered_negative_resolvent_def ordered_model_resolvent_def  less_restrictive_def 
  using positive_part_lemma by auto

lemma positive_resolvent_is_model_res:
  "less_restrictive ordered_positive_resolvent (ordered_model_resolvent {})"
unfolding ordered_positive_resolvent_def ordered_model_resolvent_def less_restrictive_def 
  using negative_part_lemma by auto

theorem ordered_positive_resolvent_is_complete : "Complete ordered_positive_resolvent"
using ordered_resolution_is_complete_model_resolution less_restrictive_complete positive_resolvent_is_model_res by auto

theorem ordered_negative_resolvent_is_complete: "Complete ordered_negative_resolvent"
using ordered_resolution_is_complete_model_resolution less_restrictive_complete negative_resolvent_is_model_res by auto

subsection {* Unit Resolution and Horn Renamable Clauses *}

text {* Unit resolution is complete if the considered clause set can be transformed into a 
Horn clause set by renaming. 
This result is proven by showing that unit resolution simulates
semantic resolution for Horn-renamable clauses (for some specific interpretation). *}

definition Horn :: "'at Clause \<Rightarrow> bool"
  where "(Horn C) = ((card (positive_part C)) \<le> 1)"

definition Horn_renamable_formula :: "'at Formula \<Rightarrow> bool"
  where "Horn_renamable_formula S = (\<exists>I. (all_fulfill Horn (rename_formula I S)))"

theorem unit_resolvent_complete_for_Horn_renamable_set:
  assumes "saturated_binary_rule unit_resolvent S"
  assumes "all_fulfill finite S"
  assumes "{} \<notin> S" 
  assumes "Horn_renamable_formula S"
  shows "satisfiable S"
proof -
  from `Horn_renamable_formula S` obtain I where "all_fulfill Horn (rename_formula I S)" 
    unfolding Horn_renamable_formula_def by auto
  have "saturated_binary_rule (ordered_model_resolvent I) S"
  proof (rule ccontr)
    assume "\<not>saturated_binary_rule (ordered_model_resolvent I) S"
    then obtain P1 P2 C where "ordered_model_resolvent I P1 P2 C" and "P1 \<in> S" and "P2 \<in> S" 
      and "\<not>redundant C S"
      unfolding saturated_binary_rule_def by auto
    from `ordered_model_resolvent I P1 P2 C` obtain L 
      where def_c: "C = ( (P1 - { L }) \<union> ( P2 - { (complement L) }))" 
      and "strictly_maximal_literal P1 L" and "validated_part I P1 = {}" 
      and "strictly_maximal_literal (validated_part I P2) (complement L)"
      unfolding ordered_model_resolvent_def by auto
    from `strictly_maximal_literal P1 L` have "L \<in> P1" 
      unfolding strictly_maximal_literal_def by auto
    from `strictly_maximal_literal (validated_part I P2) (complement L)` have "complement L \<in> P2" 
      unfolding strictly_maximal_literal_def validated_part_def by auto
    have "selected_part UNIV (rename_clause I P1) 
      =  rename_clause I (validated_part I (rename_clause I (rename_clause I P1)))" 
      using renaming_and_selected_part [of "rename_clause I P1" I] by auto
    then have "selected_part UNIV (rename_clause I P1) =  rename_clause I (validated_part I P1)" 
      using inverse_clause_renaming by auto 
    from this and `validated_part I P1 = {}` have "selected_part UNIV (rename_clause I P1) = {}" 
      unfolding rename_clause_def by auto 
    then have "negative_part (rename_clause I P1) = {}" 
      unfolding selected_part_def negative_part_def by auto
    from `all_fulfill Horn (rename_formula I S)` and `P1 \<in> S` have "Horn (rename_clause I P1)" 
      unfolding all_fulfill_def and rename_formula_def by auto
    then have "card (positive_part (rename_clause I P1)) \<le> 1" unfolding Horn_def by auto
      from  `negative_part (rename_clause I P1) = {}` 
      have "rename_clause I P1 = (positive_part (rename_clause I P1))" 
      using decomposition_clause_pos_neg by auto
    from this and `card (positive_part (rename_clause I P1)) \<le> 1` 
      have "card (rename_clause I P1) \<le> 1" by auto
    from `strictly_maximal_literal P1 L` have "P1 \<noteq> {}" 
      unfolding strictly_maximal_literal_def by auto
    then have "rename_clause I P1 \<noteq> {}" unfolding rename_clause_def by auto
    from `all_fulfill finite S` and `P1 \<in> S` have "finite P1" unfolding all_fulfill_def by auto
    then have "finite (rename_clause I P1)" unfolding rename_clause_def by auto
    from this and `rename_clause I P1 \<noteq> {}` have "card(rename_clause I P1) \<noteq> 0" 
      using card_0_eq by auto
    from this and `card (rename_clause I P1) \<le> 1` have "card (rename_clause I P1) = 1" by auto
    then have "card P1 = 1" using renaming_preserves_cardinality by auto
    then have "Unit P1" unfolding Unit_def using card_image by auto
    from this and `L \<in> P1` and `complement L \<in> P2` and def_c have "unit_resolvent P1 P2 C"
      unfolding unit_resolvent_def by auto
    from this and `\<not>(redundant C S)` and `P1 \<in> S` and `P2 \<in> S` 
      and `saturated_binary_rule unit_resolvent S`
    show "False" unfolding saturated_binary_rule_def by auto
  qed
  from this and `all_fulfill finite S` and `{} \<notin> S` show ?thesis 
    using ordered_resolution_is_complete_model_resolution unfolding Complete_def by auto
qed

section {* Computation of Saturated Clause Sets *}

text {* We now provide a concrete (rather straightforward) procedure for computing saturated clause 
sets. Starting from the initial set, we define a sequence of clause sets, where each set is obtained 
from the previous one by applying the resolution rule in a systematic way, followed by redundancy 
elimination rules. The algorithm is generic, in the sense that it applies to any binary 
inference rule. *}

fun inferred_clause_sets :: "'at BinaryRule \<Rightarrow> 'at Formula \<Rightarrow> nat \<Rightarrow> 'at Formula"
 where 
  "(inferred_clause_sets R S 0) = (simplify S)" |
  "(inferred_clause_sets R S (Suc N)) = 
    (simplify (add_all_deducible_clauses R (inferred_clause_sets R S N)))"

text {* The saturated set is constructed by considering the set of persistent clauses, i.e.,
the clauses that are generated and never deleted. *}
 
fun saturation :: "'at BinaryRule \<Rightarrow> 'at Formula \<Rightarrow> 'at Formula"
 where 
  "saturation R S = { C. \<exists>N. (\<forall>M. (M \<ge> N \<longrightarrow> C \<in> inferred_clause_sets R S M)) }"

text {* We prove that all inference rules yield finite clauses. *}

theorem ordered_resolvent_is_finite : "derived_clauses_are_finite ordered_resolvent"
using less_restrictive_and_finite ordered_resolvent_is_resolvent resolvent_is_finite by auto

theorem model_resolvent_is_finite : "derived_clauses_are_finite (ordered_model_resolvent I)"
using less_restrictive_and_finite ordered_model_resolvent_is_resolvent resolvent_is_finite 
  by auto

theorem positive_resolvent_is_finite : "derived_clauses_are_finite ordered_positive_resolvent"
using less_restrictive_and_finite positive_resolvent_is_resolvent resolvent_is_finite by auto

theorem negative_resolvent_is_finite : "derived_clauses_are_finite ordered_negative_resolvent"
using less_restrictive_and_finite negative_resolvent_is_resolvent resolvent_is_finite by auto

theorem unit_resolvent_is_finite : "derived_clauses_are_finite unit_resolvent"
using less_restrictive_and_finite unit_resolvent_is_resolvent resolvent_is_finite by auto

lemma all_deducible_clauses_are_finite:
  assumes "derived_clauses_are_finite R"
  assumes "all_fulfill finite S"
  shows "all_fulfill finite (all_deducible_clauses R S)"
proof (rule ccontr)
  assume "\<not>all_fulfill finite (all_deducible_clauses R S)"
  from this obtain C where "C \<in> all_deducible_clauses R S" and "\<not>finite C"
    unfolding all_fulfill_def by auto
  from `C \<in> all_deducible_clauses R S` have "\<exists> P1 P2. R P1 P2 C \<and> P1 \<in> S \<and> P2 \<in> S" by auto
  then obtain P1 P2 where "R P1 P2 C" and "P1 \<in> S" and "P2 \<in> S" by auto
  from `P1 \<in> S` and `all_fulfill finite S` have "finite P1" unfolding all_fulfill_def by auto
  from `P2 \<in> S` and `all_fulfill finite S` have "finite P2" unfolding  all_fulfill_def by auto
  from `finite P1` and `finite P2` and `derived_clauses_are_finite R` and `R P1 P2 C` and `\<not>finite C` show "False"
    unfolding derived_clauses_are_finite_def by metis
qed

text {* This entails that all the clauses occurring in the sets in the sequence are finite. *}

lemma all_inferred_clause_sets_are_finite: 
  assumes "derived_clauses_are_finite R" 
  assumes "all_fulfill finite S"
  shows "all_fulfill finite (inferred_clause_sets R S N)"
proof (induction N)
  from assms show "all_fulfill finite (inferred_clause_sets R S 0)"
    using simplify_finite by auto
next
  fix N assume "all_fulfill finite (inferred_clause_sets R S N)"
  then have "all_fulfill finite (all_deducible_clauses R (inferred_clause_sets R S N))"
    using assms(1) all_deducible_clauses_are_finite [of R "inferred_clause_sets R S N"]
    by auto 
  from this and `all_fulfill finite (inferred_clause_sets R S N)`
    have "all_fulfill finite (add_all_deducible_clauses R (inferred_clause_sets R S N))"
    using all_fulfill_def by auto
  then show "all_fulfill finite (inferred_clause_sets R S (Suc N))"
    using simplify_finite by auto
qed  

lemma add_all_deducible_clauses_finite: 
  assumes "derived_clauses_are_finite R" 
  assumes "all_fulfill finite S"
  shows "all_fulfill finite (add_all_deducible_clauses R (inferred_clause_sets R S N))"
proof -
  from assms have "all_fulfill finite (all_deducible_clauses R (inferred_clause_sets R S N))"
  using all_deducible_clauses_are_finite [of R "inferred_clause_sets R S N"] 
    all_inferred_clause_sets_are_finite [of R S N] by metis 
  then show "all_fulfill finite (add_all_deducible_clauses R (inferred_clause_sets R S N))"
  using assms all_fulfill_def all_inferred_clause_sets_are_finite [of R S "N"] by auto
qed

text {* We show that the set of redundant clauses can only increase. *}

lemma sequence_of_inferred_clause_sets_is_monotonous: 
 assumes "derived_clauses_are_finite R"
 assumes "all_fulfill finite S"
 shows "\<forall>C. redundant C (inferred_clause_sets R S N) 
  \<longrightarrow> redundant C (inferred_clause_sets R S (N+M::nat))"

proof ((induction M), auto simp del: inferred_clause_sets.simps)
  fix M C assume ind_hyp: "\<forall>C. redundant C (inferred_clause_sets R S N) 
    \<longrightarrow> redundant C (inferred_clause_sets R S (N+M::nat))"
  assume "redundant C (inferred_clause_sets R S N)"
  from this and ind_hyp have "redundant C (inferred_clause_sets R S (N+M))" by auto 
  then have "redundant C (add_all_deducible_clauses R (inferred_clause_sets R S (N+M)))"
    using deducible_clause_preserve_redundancy by auto
  then have "all_fulfill finite (add_all_deducible_clauses R (inferred_clause_sets R S (N+M)))"
  using assms  add_all_deducible_clauses_finite [of R S "N+M"] by auto
  from  `redundant C (inferred_clause_sets R S N)` and ind_hyp 
    have "redundant C (inferred_clause_sets R S (N+M))" by auto
  from  `redundant C (inferred_clause_sets R S (N+M))` 
    have "redundant C (add_all_deducible_clauses R (inferred_clause_sets R S (N+M)))"
    using deducible_clause_preserve_redundancy by blast
  from this and `all_fulfill finite (add_all_deducible_clauses R (inferred_clause_sets R S (N+M)))` 
    have "redundant C (simplify (add_all_deducible_clauses R (inferred_clause_sets R S (N+M))))"
    using simplify_preserves_redundancy by auto 
  thus "redundant C (inferred_clause_sets R S (Suc (N + M)))"  by auto
qed

text {* We show that non-persistent clauses are strictly redundant in some element of the 
sequence. *}

lemma non_persistent_clauses_are_redundant:
  assumes "D \<in> inferred_clause_sets R S N"
  assumes "D \<notin> saturation R S"
  assumes "all_fulfill finite S"
  assumes "derived_clauses_are_finite R"
  shows "\<exists>M. strictly_redundant D (inferred_clause_sets R S M)"
proof (rule ccontr)
  assume hyp: "\<not>(\<exists>M. strictly_redundant D (inferred_clause_sets R S M))"
  { 
    fix M 
    have "D \<in> (inferred_clause_sets R S (N+M))"
    proof (induction M)
      show "D \<in> inferred_clause_sets R S (N+0)" using assms(1) by auto
    next
      fix M assume "D \<in> inferred_clause_sets R S (N+M)"
      from this have "D \<in> add_all_deducible_clauses R (inferred_clause_sets R S (N+M))" by auto
      show "D \<in> (inferred_clause_sets R S (N+(Suc M)))"
      proof (rule ccontr)
        assume "D \<notin> (inferred_clause_sets R S (N+(Suc M)))"
        from this and `D \<in> add_all_deducible_clauses R (inferred_clause_sets R S (N+M))`
          have "strictly_redundant D (add_all_deducible_clauses R (inferred_clause_sets R S (N+M)))"
          using simplify_def by auto
        then have "all_fulfill finite (add_all_deducible_clauses R (inferred_clause_sets R S (N+M)))"
        using assms(4) assms(3)  add_all_deducible_clauses_finite [of R S "N+M"] 
        by auto

        from this 
          and `strictly_redundant D (add_all_deducible_clauses R (inferred_clause_sets R S (N+M)))`
          have "strictly_redundant D (inferred_clause_sets R S (N+(Suc M)))"
          using simplify_preserves_strict_redundancy by auto

        from this and hyp show "False" by blast
      qed
    qed
  }
  from assms(2) and assms(1) have "\<not>(\<forall>M'. (M' \<ge> N \<longrightarrow> D \<in> inferred_clause_sets R S M'))" by auto 
  from this obtain M' where "M' \<ge> N" and "D \<notin> inferred_clause_sets R S M'" by auto 
  from `M' \<ge> N` obtain N':: nat where "N' = M' - N" by auto
  have "D \<in> inferred_clause_sets R S (N+(M'-N))"
    by (simp add: `\<And>M. D \<in> inferred_clause_sets R S (N + M)`) 
  from this and `D \<notin> inferred_clause_sets R S M'` show "False" by (simp add: `N \<le> M'`) 
qed        

text {* This entails that the clauses that are redundant in some set in the sequence are also 
redundant in the set of persistent clauses. *}

lemma persistent_clauses_subsume_redundant_clauses:
  assumes "redundant C (inferred_clause_sets R S N)"
  assumes "all_fulfill finite S"
  assumes "derived_clauses_are_finite R"
  assumes "finite C"
  shows "redundant C (saturation R S)"
proof -
  let ?nat_order = "{ (x::nat,y::nat). x < y}"
  {
    fix I have "\<forall>C N. finite C \<longrightarrow> card C = I 
         \<longrightarrow> (redundant C (inferred_clause_sets R S N)) \<longrightarrow> redundant C (saturation R S)" (is "?P I")
    proof ((rule wf_induct [of ?nat_order ?P I]),(simp add:wf))
    fix I assume hyp_induct: "\<forall>J. (J,I) \<in> ?nat_order \<longrightarrow> (?P J)"
    show "?P I" 
    proof ((rule allI)+,(rule impI)+)
      fix C N assume "finite C" "card C = I" "redundant C (inferred_clause_sets R S N)"
      show "redundant C (saturation R S)"
      proof (cases)
        assume "tautology C"
        then show "redundant C (saturation R S)" unfolding redundant_def by auto
      next
        assume "\<not>tautology C"
        from this and `redundant C (inferred_clause_sets R S N)` obtain D 
          where "subsumes D C" and "D \<in> inferred_clause_sets R S N" unfolding redundant_def by auto
        show "redundant C (saturation R S)"
        proof (cases)
          assume "D \<in> saturation R S"
          from this and `subsumes D C` show "redundant C (saturation R S)" 
            unfolding redundant_def by auto
        next
          assume "D \<notin> saturation R S"
          from assms(2) assms(3) and `D \<in> inferred_clause_sets R S N` and `D \<notin> saturation R S`
          obtain M where "strictly_redundant D (inferred_clause_sets R S M)" using 
            non_persistent_clauses_are_redundant [of D R S] by auto
          from `subsumes D C` and `\<not>tautology C` have "\<not>tautology D" 
            unfolding subsumes_def tautology_def by auto
          from `strictly_redundant D (inferred_clause_sets R S M)` and `\<not>tautology D` 
            obtain D' where "D' \<subset> D" and "D' \<in> inferred_clause_sets R S M"
            unfolding strictly_redundant_def by auto
   
          from `D' \<subset> D` and `subsumes D C` have "D' \<subset> C" unfolding subsumes_def by auto 
          from `D' \<subset> C` and `finite C` have "finite D'" 
            by (meson psubset_imp_subset rev_finite_subset) 
          from `D' \<subset> C` and `finite C` have "card D' < card C" 
              unfolding all_fulfill_def 
              using psubset_card_mono  by auto
          from this and `card C = I` have "(card D',I) \<in> ?nat_order" by auto
          from `D' \<in> inferred_clause_sets R S M` have "redundant D' (inferred_clause_sets R S M)"
            unfolding redundant_def subsumes_def by auto
          from  hyp_induct and `(card D',I) \<in> ?nat_order` have "?P (card D')" by force
          from this and `finite D'` and `redundant D' (inferred_clause_sets R S M)` have 
            "redundant D' (saturation R S)" by auto
          show "redundant C (saturation R S)"
            by (meson `D' \<subset> C` `redundant D' (saturation R S)` 
              psubset_imp_subset subsumes_def subsumption_preserves_redundancy) 
        qed
      qed
  qed
 qed
 }
 then show "redundant C (saturation R S)" using assms(1) assms(4) by blast
qed

text {* We deduce that the set of persistent clauses is saturated. *}

theorem persistent_clauses_are_saturated:
 assumes "derived_clauses_are_finite R"
 assumes "all_fulfill finite S"
  shows "saturated_binary_rule R (saturation R S)"
proof (rule ccontr)
  let ?S = "saturation R S"
  assume "\<not>saturated_binary_rule R ?S"
  then obtain P1 P2 C where "R P1 P2 C" and "P1 \<in> ?S" and "P2 \<in> ?S" and "\<not>redundant C ?S"
    unfolding saturated_binary_rule_def by blast
  from `P1 \<in> ?S` obtain N1 where i: "\<forall>M. (M \<ge> N1 \<longrightarrow> P1 \<in> (inferred_clause_sets R S M))"
    by auto
  from `P2 \<in> ?S` obtain N2 where ii: "\<forall>M. (M \<ge> N2 \<longrightarrow> P2 \<in> (inferred_clause_sets R S M))"
    by auto
  let ?N = "max N1 N2"
  have "?N \<ge> N1" and "?N \<ge> N2" by auto
  from this and i have "P1 \<in> inferred_clause_sets R S ?N" by metis
  from `?N \<ge> N2` and ii have "P2 \<in> inferred_clause_sets R S ?N" by metis
  from `R P1 P2 C` and `P1 \<in> inferred_clause_sets R S ?N` and `P2 \<in> inferred_clause_sets R S ?N`
    have "C \<in> all_deducible_clauses R ( inferred_clause_sets R S ?N)" by auto
  from this have "C \<in> add_all_deducible_clauses R (inferred_clause_sets R S ?N)" by auto
  from assms have "all_fulfill finite (inferred_clause_sets R S ?N)"
    using all_inferred_clause_sets_are_finite [of R S ?N] by auto
  from assms have "all_fulfill finite (add_all_deducible_clauses R (inferred_clause_sets R S ?N))"
    using add_all_deducible_clauses_finite by auto
  from this and `C \<in> add_all_deducible_clauses R (inferred_clause_sets R S ?N)`
    have "redundant C (inferred_clause_sets R S (Suc ?N))" 
    using simplify_and_membership
    [of "add_all_deducible_clauses R (inferred_clause_sets R S ?N)" 
      "inferred_clause_sets R S (Suc ?N)" C]
        by auto
  have "finite P1"
    using `P1 \<in> inferred_clause_sets R S (max N1 N2)`
      `all_fulfill finite (inferred_clause_sets R S (max N1 N2))` all_fulfill_def by auto 
  have "finite P2"
    using `P2 \<in> inferred_clause_sets R S (max N1 N2)`
      `all_fulfill finite (inferred_clause_sets R S (max N1 N2))` all_fulfill_def by auto 
  from `R P1 P2 C` and `finite P1` and `finite P2` and `derived_clauses_are_finite R` have "finite C" 
    unfolding derived_clauses_are_finite_def  by blast
  from assms this and `redundant C (inferred_clause_sets R S (Suc ?N))`
    have "redundant C (saturation R S)" 
    using  persistent_clauses_subsume_redundant_clauses [of C R S "Suc ?N"]
    by auto
  thus "False" using `\<not>redundant C ?S` by auto
 qed

text {* Finally, we show that the computed saturated set is equivalent to the initial formula. *}

theorem saturation_is_correct: 
  assumes "Sound R"
  assumes "derived_clauses_are_finite R"
  assumes "all_fulfill finite S"
  shows "equivalent S (saturation R S)"
proof -
  have "entails_formula S (saturation R S)"
  proof (rule ccontr)
    assume "\<not> entails_formula S (saturation R S)"
    then obtain C where "C \<in> saturation R S" and "\<not> entails S C" 
      unfolding entails_formula_def by auto
    from `C \<in> saturation R S` obtain N where "C \<in> inferred_clause_sets R S N" by auto
    { 
      fix N 
      have "entails_formula S (inferred_clause_sets R S N)"
      proof (induction N)
        show "entails_formula S (inferred_clause_sets R S 0)"
          using assms(3) simplify_preserves_semantic validity_implies_entailment by auto
      next
        fix N assume "entails_formula S (inferred_clause_sets R S N)"
        from assms(1) have "entails_formula (inferred_clause_sets R S N)   
          (add_all_deducible_clauses R (inferred_clause_sets R S N))"
          using add_all_deducible_sound  by auto
        from this and `entails_formula S (inferred_clause_sets R S N)` 
          have "entails_formula S (add_all_deducible_clauses R (inferred_clause_sets R S N))"
          using entails_transitive 
        [of S "inferred_clause_sets R S N" "add_all_deducible_clauses R (inferred_clause_sets R S N)"] 
          by auto
        have "inferred_clause_sets R S (Suc N) \<subseteq> add_all_deducible_clauses R 
                (inferred_clause_sets R S N)"
          using simplify_def by auto
        then have "entails_formula (add_all_deducible_clauses R (inferred_clause_sets R S N))
              (inferred_clause_sets R S (Suc N))" using entailment_subset by auto
        from this and `entails_formula S (add_all_deducible_clauses R (inferred_clause_sets R S N))`
          show "entails_formula S (inferred_clause_sets R S (Suc N))"
          using entails_transitive [of S "add_all_deducible_clauses R (inferred_clause_sets R S N)"] 
          by auto
      qed
    }
    from this and `C \<in> inferred_clause_sets R S N` and `\<not> entails S C` show "False" 
    unfolding entails_formula_def by auto
  qed
  have "entails_formula (saturation R S) S"
  proof (rule ccontr)
    assume "\<not> entails_formula (saturation R S) S"
    then obtain C where "C \<in> S" and "\<not> entails (saturation R S) C" 
      unfolding entails_formula_def by auto
    from `C \<in> S` have "redundant C S" unfolding redundant_def subsumes_def by auto
    from assms(3) and `redundant C S` have "redundant C (inferred_clause_sets R S 0)" 
      using simplify_preserves_redundancy by auto
    from assms(3) and `C \<in> S` have "finite C" unfolding all_fulfill_def by auto
    from `redundant C (inferred_clause_sets R S 0)` assms(2) assms(3) `finite C` 
      have "redundant C (saturation R S)" 
      using persistent_clauses_subsume_redundant_clauses [of C R S 0] by auto
    from this and `\<not> entails (saturation R S) C` show "False" 
      using entails_formula_def redundancy_implies_entailment by auto
 qed
 from `entails_formula S (saturation R S)` and `entails_formula (saturation R S) S` 
 show ?thesis
 unfolding equivalent_def by auto
qed

end

end


