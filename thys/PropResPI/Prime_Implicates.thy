
(* N. Peltier. LIG/CNRS http://membres-lig.imag.fr/peltier/ *)


section {* Prime Implicates  Generation *}

text {* We show that the unrestricted resolution rule is deductive complete, i.e. that it is able
to generate all (prime) implicates of any given clause set. *}

theory Prime_Implicates

imports Main Finite_Set Propositional_Resolution

begin

context propositional_atoms

begin

subsection {* Implicates and Prime Implicates *}

text {* We first introduce the definitions of implicates and prime implicates.*}

definition implicates :: "'at Formula \<Rightarrow> 'at Formula"
  where "implicates S = { C. entails S C }"

definition prime_implicates :: "'at Formula \<Rightarrow> 'at Formula"
  where "prime_implicates S = simplify (implicates S)"

subsection {* Generation of Prime Implicates *}


text {* We introduce a function simplifying a given clause set by evaluating some literals
   to false. We show that this partial evaluation operation preserves saturatedness and 
that if the considered set of literals is an implicate of the initial clause set 
then the partial evaluation yields a clause set that is unsatisfiable.
Then the proof follows from refutational completeness: since the partially evaluated set 
is unsatisfiable and saturated it must contain the empty clause, and therefore the initial 
clause set necessarily contains a clause subsuming the implicate. *}

fun partial_evaluation :: "'a Formula \<Rightarrow> 'a Literal set \<Rightarrow> 'a Formula"
where
  "(partial_evaluation S C) = { E. \<exists>D. D \<in> S \<and> E = D-C \<and> \<not>(\<exists>L. (L \<in> C) \<and> (complement L) \<in> D)}"

lemma partial_evaluation_is_saturated : 
  assumes "saturated_binary_rule resolvent S"
  shows "saturated_binary_rule ordered_resolvent (partial_evaluation S C)"
proof (rule ccontr)
    let ?peval = "partial_evaluation S C"
    assume "\<not>saturated_binary_rule ordered_resolvent ?peval"
    from this obtain P1 and P2 and R where "P1 \<in> ?peval" and "P2 \<in> ?peval"
      and "ordered_resolvent P1 P2 R"  and "\<not>(tautology R)" 
      and not_subsumed: "\<not>(\<exists>D. ((D \<in> (partial_evaluation S C)) \<and> (subsumes D R)))" 
    unfolding saturated_binary_rule_def and redundant_def  by auto
    from `P1 \<in> ?peval` obtain PP1 where "PP1 \<in> S" and "P1 = PP1 - C" 
      and i: "\<not>(\<exists>L. (L \<in> C) \<and> (complement L) \<in> PP1)" by auto
    from `P2 \<in> ?peval` obtain PP2 where "PP2 \<in> S" and "P2 = PP2 - C" 
      and  ii: "\<not>(\<exists>L. (L \<in> C) \<and> (complement L) \<in> PP2)" by auto
    from `(ordered_resolvent P1 P2 R)` obtain A where 
      r_def: "R = (P1 - { Pos A }) \<union> (P2 - { Neg A })" and "(Pos A) \<in> P1" and "(Neg A) \<in> P2"
    unfolding ordered_resolvent_def strictly_maximal_literal_def by auto
    let ?RR = "(PP1 - { Pos A }) \<union> (PP2 - { Neg A })"
    from `P1 = PP1 - C` and `(Pos A) \<in> P1` have "(Pos A) \<in> PP1" by auto
    from `P2 = PP2 - C` and `(Neg A) \<in> P2` have "(Neg A) \<in> PP2" by auto
    from r_def and `P1 = PP1 - C` and `P2 = PP2 - C` have "R =  ?RR - C" by auto
    from `(Pos A) \<in> PP1` and `(Neg A) \<in> PP2` 
      have "resolvent PP1 PP2 ?RR" unfolding resolvent_def by auto
    with `PP1 \<in> S` and `PP2 \<in> S` and `saturated_binary_rule resolvent S` 
      have "tautology ?RR \<or> (\<exists>D. (D \<in> S \<and> (subsumes D ?RR)))"
    unfolding saturated_binary_rule_def redundant_def by auto
    thus "False"
    proof 
      assume "tautology ?RR"
      with `R = ?RR - C` and `\<not>tautology R`
        obtain X where "X \<in> C" and "complement X \<in> PP1 \<union> PP2"
        unfolding tautology_def by auto
      from `X \<in> C` and `complement X \<in> PP1 \<union> PP2` and i and ii 
        show "False" by auto
    next
      assume "\<exists>D. ((D \<in> S) \<and> (subsumes D ?RR))"
      from this obtain D where "D \<in> S" and "subsumes D ?RR"
      by auto
      from `subsumes D ?RR` and `R = ?RR - C` 
        have "subsumes (D - C) R" unfolding subsumes_def by auto
      from `D \<in> S` and ii and i and `(subsumes D ?RR)` have "D - C \<in> ?peval" 
        unfolding subsumes_def by auto
      with `subsumes (D - C) R` and not_subsumed show "False" by auto
    qed
qed

lemma evaluation_wrt_implicate_is_unsat : 
  assumes "entails S C"
  assumes "\<not>tautology C"
  shows "\<not>satisfiable (partial_evaluation S C)"
proof
    let ?peval = "partial_evaluation S C"
    assume "satisfiable ?peval"
    then obtain I where "validate_formula I ?peval" unfolding satisfiable_def by auto
    let ?J = "(I - { X. (Pos X) \<in> C }) \<union> { Y. (Neg Y) \<in> C }" 
    have "\<not>validate_clause ?J C"  
    proof 
      assume "validate_clause ?J C"
      then obtain L where "L \<in> C" and "validate_literal ?J L" by auto
      obtain X where "L = (Pos X) \<or> L = (Neg X)" using Literal.exhaust [of L] by auto
      from `L = (Pos X) \<or> L = (Neg X)` and `L \<in> C` and `\<not>tautology C` and `validate_literal ?J L` 
      show "False" unfolding tautology_def by auto
    qed
    have "validate_formula ?J S" 
    proof (rule ccontr)
      assume "\<not> (validate_formula ?J S)"
      then obtain D where "D \<in> S" and "\<not>(validate_clause ?J D)" by auto
      from `D \<in> S` have "D-C \<in> ?peval \<or>  (\<exists>L. (L \<in> C) \<and> (complement L) \<in> D)" 
      by auto
      thus "False" 
      proof
        assume "\<exists>L. (L \<in> C) \<and> (complement L) \<in> D"
        then obtain L where "L \<in> C" and "complement L \<in> D" by auto
        obtain X where "L = (Pos X) \<or> L = (Neg X)" using Literal.exhaust [of L] by auto
        from this  and `L \<in> C` and `\<not>(tautology C)` have "validate_literal ?J (complement L)" 
        unfolding tautology_def by auto
        from `(validate_literal ?J (complement L))` and `(complement L) \<in> D` 
          and `\<not>(validate_clause ?J D)`
        show "False" by auto
      next  
        assume "D-C \<in> ?peval"
        from `D-C \<in> ?peval` and `(validate_formula I ?peval)`
        have "validate_clause I (D-C)" using validate_formula.simps by blast
        from this obtain L where "L \<in> D" and "L \<notin> C" and "validate_literal I L" by auto
        obtain X where "L = (Pos X) \<or> L = (Neg X)" using Literal.exhaust [of L] by auto
        from `L = (Pos X) \<or> L = (Neg X)` and `validate_literal I L` and `L \<notin> C` 
        have "validate_literal ?J L" unfolding tautology_def by auto
        from `validate_literal ?J L` and `L \<in> D` and `\<not>(validate_clause ?J D)`
        show "False" by auto
      qed
    qed
    from `\<not>validate_clause ?J C` and `validate_formula ?J S` and `entails S C` show "False" 
    unfolding entails_def by auto
qed

lemma entailment_and_implicates:
  assumes "entails_formula S1 S2"
  shows "implicates S2 \<subseteq> implicates S1"
using assms entailed_formula_entails_implicates implicates_def by auto

lemma equivalence_and_implicates:
  assumes "equivalent S1 S2"
  shows "implicates S1 = implicates S2"
using assms entailment_and_implicates equivalent_def by blast

lemma equivalence_and_prime_implicates:
  assumes "equivalent S1 S2"
  shows "prime_implicates S1 = prime_implicates S2"
using assms equivalence_and_implicates prime_implicates_def by auto

lemma unrestricted_resolution_is_deductive_complete : 
  assumes "saturated_binary_rule resolvent S"
  assumes "all_fulfill finite S"
  assumes "C \<in> implicates S"
  shows "redundant C S"
proof ((cases "tautology C"),(simp add: redundant_def))
next 
  assume "\<not> tautology C"
  have "\<exists>D. (D \<in> S) \<and> (subsumes D C)"
  proof -
    let ?peval = "partial_evaluation S C"
    from `saturated_binary_rule resolvent S` 
      have "saturated_binary_rule ordered_resolvent ?peval" 
      using partial_evaluation_is_saturated by auto
    from `C \<in> implicates S` have "entails S C" unfolding implicates_def by auto
    from `entails S C` and `\<not>tautology C` have "\<not>satisfiable ?peval"
    using evaluation_wrt_implicate_is_unsat by auto
    from `all_fulfill finite S` have "all_fulfill finite ?peval" unfolding all_fulfill_def by auto
    from `\<not>satisfiable ?peval` and `saturated_binary_rule ordered_resolvent ?peval` 
      and `all_fulfill finite ?peval` 
    have "{} \<in> ?peval" using Complete_def ordered_resolution_is_complete by blast 
    then show ?thesis unfolding subsumes_def by auto
  qed
  then show ?thesis unfolding redundant_def by auto
qed

lemma prime_implicates_generation_correct :
  assumes "saturated_binary_rule resolvent S"
  assumes "non_redundant S"
  assumes "all_fulfill finite S"
  shows "S \<subseteq> prime_implicates S"
proof 
  fix x assume "x \<in> S"
  show "x \<in> prime_implicates S"
  proof (rule ccontr)
    assume "\<not> x \<in> prime_implicates S"
    from `x \<in> S` have "entails S x" unfolding entails_def implicates_def by auto
    then have "x \<in> implicates S" unfolding implicates_def by auto
    with `\<not> x \<in> (prime_implicates S)` have "strictly_redundant x (implicates S)"
      unfolding prime_implicates_def simplify_def by auto
    from this have "tautology x \<or> (\<exists>y. (y \<in> (implicates S)) \<and> (y \<subset> x))" 
      unfolding strictly_redundant_def by auto
    then have "strictly_redundant x S"
    proof ((cases "tautology x"),(simp add: strictly_redundant_def))
    next 
      assume "\<not>tautology x"
      with `tautology x \<or> (\<exists>y. (y \<in> (implicates S)) \<and> (y \<subset> x))` 
        obtain y where "y \<in> implicates S" and "y \<subset> x" by auto
      from `y \<in> implicates S` and `saturated_binary_rule resolvent S` and `all_fulfill finite S`
        have "redundant y S" using unrestricted_resolution_is_deductive_complete by auto
      from `y \<subset> x` and `\<not>tautology x` have "\<not>tautology y" unfolding tautology_def by auto 
      with `redundant y S` obtain z where "z \<in> S" and "z \<subseteq> y" 
        unfolding redundant_def subsumes_def by auto
      with `y \<subset> x` have "z \<subset> x" by auto
      with `z \<in> S` show "strictly_redundant x S" using strictly_redundant_def by auto
    qed
    with `non_redundant S` and `x \<in> S` show "False" unfolding non_redundant_def by auto
 qed
qed

theorem prime_implicates_of_saturated_sets: 
  assumes "saturated_binary_rule resolvent S"
  assumes "all_fulfill finite S"
  assumes "non_redundant S"
  shows "S = prime_implicates S"
proof
  from assms show "S \<subseteq> prime_implicates S" using prime_implicates_generation_correct by auto
  show "prime_implicates S \<subseteq> S"
  proof
    fix x assume "x \<in> prime_implicates S"
    from this have "x \<in> implicates S" unfolding prime_implicates_def simplify_def by auto
    with assms have "redundant x S" 
      using unrestricted_resolution_is_deductive_complete by auto
    show "x \<in> S"
    proof (rule ccontr)
      assume "x \<notin> S"
      with `redundant x S` have "strictly_redundant x S" 
        unfolding redundant_def strictly_redundant_def subsumes_def by auto
      with `S \<subseteq> prime_implicates S` have "strictly_redundant x (prime_implicates S)"
        unfolding strictly_redundant_def by auto
      then have "strictly_redundant x (implicates S)"
        unfolding strictly_redundant_def prime_implicates_def simplify_def by auto
      with `x \<in> prime_implicates S` show "False"  
        unfolding prime_implicates_def simplify_def  by auto
   qed
  qed
qed

subsection {* Incremental Prime Implicates Computation *}

text {* We show that it is possible to compute the set of prime implicates incrementally
i.e., to fix an ordering among atoms, and to compute the set of resolvents upon each atom
one by one, without backtracking (in the sense that if the resolvents upon a given atom are 
generated at some step @{ term i } then no resolvents upon the same atom are generated at 
step @{ term "j>i" }. 
This feature is critical in practice for the efficiency of prime implicates 
generation algorithms.*}

text {* We first introduce a function computing all resolvents upon a given atom.*}

definition all_resolvents_upon :: "'at Formula \<Rightarrow> 'at \<Rightarrow> 'at Formula"
 where  "(all_resolvents_upon S A) = { C. \<exists>P1 P2. P1 \<in> S \<and> P2 \<in> S \<and> C = (resolvent_upon P1 P2 A) }" 

lemma resolvent_upon_correct:
  assumes "P1 \<in> S"
  assumes "P2 \<in> S"
  assumes "C = resolvent_upon P1 P2 A"
  shows "entails S C"
proof cases
  assume "Pos A \<in> P1 \<and> Neg A \<in> P2" 
  with `C = resolvent_upon P1 P2 A` have "resolvent P1 P2 C" 
    unfolding resolvent_def by auto
  with `P1 \<in> S` and `P2 \<in> S` show ?thesis
    using soundness_and_entailment resolution_is_correct by auto
next 
  assume "\<not> (Pos A \<in> P1 \<and> Neg A \<in> P2)"
  with `C = resolvent_upon P1 P2 A` have "P1 \<subseteq> C \<or> P2 \<subseteq> C" by auto
  with `P1 \<in> S` and `P2 \<in> S` have "redundant C S" 
    unfolding redundant_def subsumes_def by auto 
  then show ?thesis using redundancy_implies_entailment by auto
qed

lemma all_resolvents_upon_is_finite:
  assumes "all_fulfill finite S"
  shows "all_fulfill finite (S \<union> (all_resolvents_upon S A))"
using assms unfolding all_fulfill_def all_resolvents_upon_def by auto

lemma atoms_formula_resolvents:
  shows "atoms_formula (all_resolvents_upon S A) \<subseteq>  atoms_formula S"
using assms unfolding all_resolvents_upon_def by auto

text {* We define a partial saturation predicate that is restricted to a specific atom. *}

definition partial_saturation :: "'at Formula \<Rightarrow> 'at \<Rightarrow> 'at Formula \<Rightarrow> bool"
where
  "(partial_saturation S A R) = (\<forall>P1 P2. (P1 \<in> S \<longrightarrow> P2 \<in> S  
    \<longrightarrow>(redundant (resolvent_upon P1 P2 A) R)))"

text {* We show that the resolvent of two redundant clauses in a partially saturated set 
is itself redundant. *}

lemma resolvent_upon_and_partial_saturation :
  assumes "redundant P1 S"
  assumes "redundant P2 S"
  assumes "partial_saturation S A (S \<union> R)"
  assumes "C = resolvent_upon P1 P2 A"
  shows "redundant C (S \<union> R)"
proof (rule ccontr)
  assume "\<not>redundant C  (S \<union> R)"
  from `C = resolvent_upon P1 P2 A` have "C = (P1 - { Pos A }) \<union> (P2 - { Neg A })" by auto
  from `\<not>redundant C  (S \<union> R)` have "\<not>tautology C" unfolding redundant_def by auto 
  have "\<not> (tautology P1)"
  proof   
    assume "tautology P1"
    then obtain B where "Pos B \<in> P1" and "Neg B \<in> P1" unfolding tautology_def by auto
    show "False"
    proof cases
      assume "A = B"
      with `Neg B \<in> P1` and `C = (P1 - { Pos A }) \<union> (P2 - { Neg A })` have "subsumes P2 C"
        unfolding subsumes_def using Literal.distinct by blast
      with `redundant P2 S` have "redundant C S" 
        using subsumption_preserves_redundancy by auto
      with `\<not>redundant C (S \<union> R)` show "False" unfolding redundant_def by auto
    next 
      assume "A \<noteq> B"
      with `C = (P1 - { Pos A }) \<union> (P2 - { Neg A })` and `Pos B \<in> P1` and `Neg B \<in> P1` 
      have "Pos B \<in> C" and "Neg B \<in> C" by auto
      with `\<not>redundant C  (S \<union> R)` show "False" 
        unfolding tautology_def redundant_def by auto
    qed
  qed
  with `redundant P1 S` obtain Q1 where "Q1 \<in> S" and "subsumes Q1 P1" 
    unfolding redundant_def by auto
  have "\<not> (tautology P2)"
  proof   
    assume "tautology P2"
    then obtain B where "Pos B \<in> P2" and "Neg B \<in> P2" unfolding tautology_def by auto
    show "False"
    proof cases
      assume "A = B"
      with `Pos B \<in> P2` and `C = (P1 - { Pos A }) \<union> (P2 - { Neg A })` have "subsumes P1 C"
        unfolding subsumes_def using Literal.distinct by blast
      with `redundant P1 S` have "redundant C S" 
        using subsumption_preserves_redundancy by auto
      with `\<not>redundant C  (S \<union> R)` show "False" unfolding redundant_def by auto
    next 
      assume "A \<noteq> B"
      with `C = (P1 - { Pos A }) \<union> (P2 - { Neg A })` and `Pos B \<in> P2` and `Neg B \<in> P2` 
      have "Pos B \<in> C" and "Neg B \<in> C" by auto
      with `\<not>redundant C  (S \<union> R)` show "False" 
      unfolding tautology_def redundant_def  by auto
    qed
  qed
  with `redundant P2 S` obtain Q2 where "Q2 \<in> S" and "subsumes Q2 P2" 
    unfolding redundant_def by auto
  let ?res = "(Q1 - { Pos A }) \<union> (Q2 - { Neg A })"
  have "?res = resolvent_upon Q1 Q2 A" by auto
  from this  and `partial_saturation S A  (S \<union> R)` and `Q1 \<in> S` and  `Q2 \<in> S` 
    have "redundant ?res  (S \<union> R)" 
    unfolding partial_saturation_def by auto  
  from `subsumes Q1 P1` and `subsumes Q2 P2` and `C = (P1 - { Pos A }) \<union> (P2 - { Neg A })` 
  have "subsumes ?res C" unfolding subsumes_def by auto
  with `redundant ?res  (S \<union> R)` and `\<not>redundant C  (S \<union> R)` show False 
    using subsumption_preserves_redundancy by auto
qed

text {* We show that if @{term R} is a set of resolvents of a set of clauses @{term S} then the 
same holds for @{ term "S \<union> R"}. For the clauses in @{term S}, the premises are identical to 
the resolvent and the inference is thus redundant (this trick is useful to simplify proofs). *}

definition in_all_resolvents_upon:: "'at Formula \<Rightarrow> 'at \<Rightarrow> 'at Clause \<Rightarrow> bool"
where 
  "in_all_resolvents_upon S A C = (\<exists> P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> C = resolvent_upon P1 P2 A))"
 
lemma every_clause_is_a_resolvent:
  assumes "all_fulfill (in_all_resolvents_upon S A) R"
  assumes "all_fulfill (\<lambda>x. \<not>(tautology x)) S"
  assumes "P1 \<in> S \<union> R"
  shows "in_all_resolvents_upon S A P1"
proof ((cases "P1 \<in> R"),(metis all_fulfill_def assms(1)))
next 
    assume "P1 \<notin> R"
    with `P1 \<in> S \<union> R` have "P1 \<in> S" by auto
    with `(all_fulfill (\<lambda>x. \<not>(tautology x)) S )` have "\<not> tautology P1" 
      unfolding all_fulfill_def by auto
    from `\<not> tautology P1` have "Neg A \<notin> P1 \<or> Pos A \<notin> P1" unfolding tautology_def by auto
    from this have "P1 = (P1 - { Pos A }) \<union> (P1 - { Neg A })" by auto
    with `P1 \<in> S` show ?thesis unfolding resolvent_def 
      unfolding in_all_resolvents_upon_def by auto
qed

text {* We show that if a formula is partially saturated then it stays so when new resolvents 
are added in the set. *}

lemma partial_saturation_is_preserved :
  assumes "partial_saturation S E1 S"
  assumes "partial_saturation S E2 (S \<union> R)"
  assumes "all_fulfill (\<lambda>x. \<not>(tautology x)) S"
  assumes "all_fulfill (in_all_resolvents_upon S E2) R"
  shows "partial_saturation (S \<union> R) E1 (S \<union> R)"
proof (rule ccontr)
  assume "\<not> partial_saturation (S \<union> R) E1 (S \<union> R)"
  from this obtain P1 P2 C where "P1 \<in> S \<union> R" and "P2 \<in> S \<union> R" and "C = resolvent_upon P1 P2 E1" 
    and "\<not> redundant C (S \<union> R)"
    unfolding partial_saturation_def by auto
  from `C = resolvent_upon P1 P2 E1` have "C = (P1 - { Pos E1 }) \<union> (P2 - { Neg E1 })" by auto
  from `P1 \<in> S \<union> R` and assms(4) and `(all_fulfill (\<lambda>x. \<not>(tautology x)) S )` 
  have "in_all_resolvents_upon S E2 P1" using every_clause_is_a_resolvent by auto
  then obtain P1_1 P1_2 where "P1_1 \<in> S" and "P1_2 \<in> S" and "P1 = resolvent_upon P1_1 P1_2 E2"
    using every_clause_is_a_resolvent unfolding in_all_resolvents_upon_def by blast
  from `P2 \<in> S \<union> R` and assms(4) and `(all_fulfill (\<lambda>x. \<not>(tautology x)) S )` 
    have "in_all_resolvents_upon S E2 P2"  using every_clause_is_a_resolvent by auto
  then obtain P2_1 P2_2 where "P2_1 \<in> S" and "P2_2 \<in> S" and  "P2 = resolvent_upon P2_1 P2_2 E2"
    using every_clause_is_a_resolvent unfolding in_all_resolvents_upon_def by blast
  let ?R1 = "resolvent_upon P1_1 P2_1 E1"
  from `partial_saturation S E1 S` and `P1_1 \<in> S` and `P2_1 \<in> S` have "redundant ?R1 S" 
    unfolding partial_saturation_def by auto
  let ?R2 = "resolvent_upon P1_2 P2_2 E1"
  from `partial_saturation S E1 S` and `P1_2 \<in> S` and `P2_2 \<in> S` have "redundant ?R2 S" 
    unfolding partial_saturation_def by auto
  let ?C = "resolvent_upon ?R1 ?R2 E2"
  from `C = resolvent_upon P1 P2 E1` and `P2 = resolvent_upon P2_1 P2_2 E2` 
    and `P1 = resolvent_upon P1_1 P1_2 E2`
    have "?C = C" by auto
  with `redundant ?R1 S` and `redundant ?R2 S` and `partial_saturation S E2 (S \<union> R)` 
    and `\<not> redundant C (S \<union> R)`
    show "False" using resolvent_upon_and_partial_saturation by auto 
qed

text {* The next lemma shows that the clauses inferred by applying the resolution rule
 upon a given atom contain no occurrence of this atom, unless the inference is redundant. *}

lemma resolvents_do_not_contain_atom :
  assumes "\<not> tautology P1"
  assumes "\<not> tautology P2"
  assumes "C = resolvent_upon P1 P2 E2"
  assumes "\<not> subsumes P1 C"
  assumes "\<not> subsumes P2 C"
  shows "(Neg E2) \<notin> C \<and> (Pos E2) \<notin> C"
proof
  from `C = resolvent_upon P1 P2 E2` have "C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })" 
    by auto
  show "(Neg E2) \<notin> C"
  proof 
    assume "Neg E2 \<in> C"
    from `C = resolvent_upon P1 P2 E2` have "C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })" 
      by auto
    with `Neg E2 \<in> C` have "Neg E2 \<in> P1" by auto
    from `\<not> subsumes P1 C` and  `C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })` have "Pos E2 \<in> P1"  
      unfolding subsumes_def by auto
    from `Neg E2 \<in> P1` and `Pos E2 \<in> P1` and  `\<not> tautology P1` show "False" 
      unfolding tautology_def by auto
  qed
  next show "(Pos E2) \<notin> C"
  proof
    assume "Pos E2 \<in> C"
    from `C = resolvent_upon P1 P2 E2` have "C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })" 
      by auto
    with `Pos E2 \<in> C` have "Pos E2 \<in> P2" by auto
    from `\<not> subsumes P2 C` and  `C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })` have "Neg E2 \<in> P2"  
      unfolding subsumes_def by auto
    from `Neg E2 \<in> P2` and `Pos E2 \<in> P2` and  `\<not> tautology P2` show "False" 
      unfolding tautology_def by auto
  qed
qed

text {* The next lemma shows that partial saturation can be ensured by computing all 
(non-redundant) resolvents upon the considered atom. *}

lemma ensures_partial_saturation :
  assumes "partial_saturation S E2 (S \<union> R)"
  assumes "all_fulfill (\<lambda>x. \<not>(tautology x)) S"
  assumes "all_fulfill (in_all_resolvents_upon S E2) R"
  assumes "all_fulfill (\<lambda>x. (\<not>redundant x S)) R"
  shows "partial_saturation (S \<union> R) E2 (S \<union> R)"
proof (rule ccontr)
  assume "\<not> partial_saturation (S \<union> R) E2 (S \<union> R)"
  from this obtain P1 P2 C where "P1 \<in> S \<union> R" and "P2 \<in> S \<union> R" and "C = resolvent_upon P1 P2 E2" 
    and "\<not> redundant C (S \<union> R)"
    unfolding partial_saturation_def by auto
  have "P1 \<in> S"
  proof (rule ccontr)
    assume "P1 \<notin> S"
    with `P1 \<in> S \<union> R` have "P1 \<in> R" by auto
    with assms(3) obtain P1_1 and P1_2 where "P1_1 \<in> S" and "P1_2 \<in> S" 
     and "P1 = resolvent_upon P1_1 P1_2 E2"
     unfolding all_fulfill_def in_all_resolvents_upon_def by auto
    from `all_fulfill (\<lambda>x. \<not>(tautology x)) S` and `P1_1 \<in> S` and `P1_2 \<in> S` 
      have "\<not> tautology P1_1" and "\<not> tautology P1_2"
      unfolding all_fulfill_def by auto
    from `all_fulfill (\<lambda>x. (\<not>redundant x S)) R` and `P1 \<in> R` and `P1_1 \<in> S` and `P1_2 \<in> S` 
      have "\<not> subsumes P1_1 P1" and "\<not> subsumes P1_2 P1" 
      unfolding redundant_def all_fulfill_def by auto
    from `\<not> tautology P1_1` `\<not> tautology P1_2` `\<not> subsumes P1_1 P1` and `\<not> subsumes P1_2 P1` 
      and `P1 = resolvent_upon P1_1 P1_2 E2` 
      have "(Neg E2) \<notin> P1 \<and> (Pos E2) \<notin> P1" 
      using resolvents_do_not_contain_atom [of P1_1 P1_2 P1 E2] by auto
    with `C = resolvent_upon P1 P2 E2` have "subsumes P1 C" unfolding subsumes_def by auto
    with `\<not> redundant C (S \<union> R)` and `P1 \<in> S \<union> R` show "False" unfolding redundant_def 
      by auto
    qed    
  have "P2 \<in> S"
  proof (rule ccontr)
    assume "P2 \<notin> S"
    with `P2 \<in> S \<union> R` have "P2 \<in> R" by auto
    with assms(3) obtain P2_1 and P2_2 where "P2_1 \<in> S" and "P2_2 \<in> S" 
      and "P2 = resolvent_upon P2_1 P2_2 E2" 
      unfolding all_fulfill_def in_all_resolvents_upon_def by auto
    from `(all_fulfill (\<lambda>x. \<not>(tautology x)) S )` and `P2_1 \<in> S` and `P2_2 \<in> S` 
      have "\<not> tautology P2_1" and "\<not> tautology P2_2"
      unfolding all_fulfill_def by auto
    from `all_fulfill (\<lambda>x. (\<not>redundant x S)) R` and `P2 \<in> R` and `P2_1 \<in> S` and `P2_2 \<in> S` 
      have "\<not> subsumes P2_1 P2" and "\<not> subsumes P2_2 P2" 
      unfolding redundant_def all_fulfill_def by auto
    from `\<not> tautology P2_1` `\<not> tautology P2_2` `\<not> subsumes P2_1 P2` and `\<not> subsumes P2_2 P2` 
      and `P2 = resolvent_upon P2_1 P2_2 E2` 
      have "(Neg E2) \<notin> P2 \<and> (Pos E2) \<notin> P2" 
      using resolvents_do_not_contain_atom [of P2_1 P2_2 P2 E2] by auto
    with `C = resolvent_upon P1 P2 E2` have "subsumes P2 C" unfolding subsumes_def by auto
    with `\<not> redundant C (S \<union> R)` and `P2 \<in> S \<union> R` 
      show "False" unfolding redundant_def by auto
    qed    
   from `P1 \<in> S` and `P2 \<in> S` and `partial_saturation S E2 (S \<union> R)` 
    and `C = resolvent_upon P1 P2 E2` and `\<not> redundant C (S \<union> R)`
    show "False" unfolding redundant_def partial_saturation_def by auto
qed

lemma resolvents_preserve_equivalence:
  shows "equivalent S (S \<union> (all_resolvents_upon S A))"
proof -
  have "S \<subseteq> (S \<union> (all_resolvents_upon S A))" by auto
  then have "entails_formula (S \<union> (all_resolvents_upon S A)) S" using entailment_subset by auto
  have "entails_formula S (S \<union> (all_resolvents_upon S A))"
  proof (rule ccontr)
    assume "\<not>entails_formula S (S \<union> (all_resolvents_upon S A))"
    from this obtain C where "C \<in> (all_resolvents_upon S A)" and "\<not>entails S C" 
      unfolding entails_formula_def using entails_member by auto
    from `C \<in> (all_resolvents_upon S A)` obtain P1 P2 
      where "C = resolvent_upon P1 P2 A" and "P1 \<in> S" and "P2 \<in> S" 
      unfolding all_resolvents_upon_def by auto
    from `C = resolvent_upon P1 P2 A` and `P1 \<in> S` and `P2 \<in> S` have "entails S C" 
      using resolvent_upon_correct by auto
    with `\<not>entails S C` show "False" by auto
  qed
  from `entails_formula (S \<union> (all_resolvents_upon S A)) S` 
    and `entails_formula S (S \<union> (all_resolvents_upon S A))` 
    show ?thesis unfolding equivalent_def by auto
qed

text {* Given a sequence of atoms, we define a sequence of clauses obtained by resolving upon 
each atom successively. Simplification rules are applied at each iteration step. *}

fun resolvents_sequence :: "(nat \<Rightarrow> 'at) \<Rightarrow> 'at Formula \<Rightarrow> nat \<Rightarrow> 'at Formula"
 where 
  "(resolvents_sequence A S 0) = (simplify S)" |
  "(resolvents_sequence A S (Suc N)) = 
    (simplify ((resolvents_sequence A S N)
      \<union> (all_resolvents_upon (resolvents_sequence A S N) (A N))))"

text {* The following lemma states that partial saturation is preserved by simplification. *}
 
lemma redundancy_implies_partial_saturation:
  assumes "partial_saturation S1 A S1"
  assumes "S2 \<subseteq> S1"
  assumes "all_fulfill (\<lambda>x. redundant x S2) S1"
  shows "partial_saturation S2 A S2"
proof (rule ccontr)
  assume "\<not>partial_saturation S2 A S2"
  then obtain P1 P2 C where "P1 \<in> S2" "P2 \<in> S2" and "C = (resolvent_upon P1 P2 A)" 
    and "\<not> redundant C S2"
    unfolding partial_saturation_def by auto
  from `P1 \<in> S2` and `S2 \<subseteq> S1` have "P1 \<in> S1" by auto
  from `P2 \<in> S2` and `S2 \<subseteq> S1` have "P2 \<in> S1" by auto
  from `P1 \<in> S1` and `P2 \<in> S1` and `partial_saturation S1 A S1` and `C = resolvent_upon P1 P2 A` 
    have "redundant C S1" unfolding partial_saturation_def by auto
  from `\<not> redundant C S2` have "\<not>tautology C" unfolding redundant_def by auto
  with `redundant C S1` obtain D where "D \<in> S1" and "D \<subseteq> C"  
    unfolding redundant_def subsumes_def by auto
  from `D \<in> S1` and `all_fulfill (\<lambda>x. redundant x S2) S1` have "redundant D S2" 
    unfolding all_fulfill_def by auto
  from `\<not> tautology C` and `D \<subseteq> C` have "\<not> tautology D" unfolding tautology_def by auto
  with `redundant D S2` obtain E where "E \<in> S2" and "E \<subseteq> D" 
    unfolding redundant_def subsumes_def by auto
  from  `E \<subseteq> D` and `D \<subseteq> C` have "E \<subseteq> C" by auto
  from  `E \<in> S2` and `E \<subseteq> C` and `\<not>redundant C S2` show "False" 
    unfolding redundant_def subsumes_def by auto
qed

text {* The next theorem finally states that the implicate generation algorithm is sound and 
complete in the sense that the final clause set in the sequence is exactly the set of prime 
implicates of the considered clause set. *}

theorem incremental_prime_implication_generation:
  assumes "atoms_formula S = { X. \<exists>I::nat. I < N \<and> X = (A I) }"
  assumes "all_fulfill finite S"
  shows "(prime_implicates S) = (resolvents_sequence A S N)"
proof -

text {* We define a set of invariants and show that they are satisfied by all sets in the 
above sequence. For the last set in the sequence, the invariants ensure that the clause set is 
saturated, which entails the desired property. *}

  let ?Final = "resolvents_sequence A S N"

text {* We define some properties and show by induction that they are satisfied by all the 
clause sets in the constructed sequence *}

  let ?equiv_init = "\<lambda>I.(equivalent S (resolvents_sequence A S I))" 
  let ?partial_saturation = "\<lambda>I. (\<forall>J::nat. (J < I 
    \<longrightarrow> (partial_saturation (resolvents_sequence A S I) (A J) (resolvents_sequence A S I))))" 
  let ?no_tautologies = "\<lambda>I.(all_fulfill (\<lambda>x. \<not>(tautology x)) (resolvents_sequence A S I) )"
  let ?atoms_init = "\<lambda>I.(atoms_formula (resolvents_sequence A S I)  
                      \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)})"
  let ?non_redundant = "\<lambda>I.(non_redundant (resolvents_sequence A S I))" 
  let ?finite ="\<lambda>I. (all_fulfill finite (resolvents_sequence A S I))"

  have "\<forall>I. (I \<le> N   \<longrightarrow> (?equiv_init I)  \<and> (?partial_saturation I) \<and>  (?no_tautologies I) 
          \<and> (?atoms_init I) \<and> (?non_redundant I) \<and> (?finite I) )"

  proof (rule allI)
    fix I
    show " (I \<le> N  
      \<longrightarrow> (?equiv_init I) \<and> (?partial_saturation I) \<and>  (?no_tautologies I) \<and> (?atoms_init I)    
            \<and> (?non_redundant I) \<and> (?finite I) )" (is "I \<le> N \<longrightarrow> ?P I")
    proof (induction I)

text {* We show that the properties are all satisfied by the initial clause set 
(after simplification). *}

      show "0 \<le> N \<longrightarrow> ?P 0" 
      proof (rule impI)+
          assume "0 \<le> N" 
          let ?R = "resolvents_sequence A S 0"
          from `all_fulfill finite S` 
          have "?equiv_init 0" using simplify_preserves_equivalence  by auto
          moreover have "?no_tautologies 0" 
            using simplify_def strictly_redundant_def all_fulfill_def by auto
          moreover have "?partial_saturation 0" by auto
          moreover from `all_fulfill finite S`  have "?finite 0" using simplify_finite by auto
          moreover have "atoms_formula ?R \<subseteq> atoms_formula S" using atoms_formula_simplify by auto
          moreover with `atoms_formula S = { X. \<exists>I::nat. I < N \<and> X = (A I) }` 
            have v: "?atoms_init 0"  unfolding simplify_def by auto
          moreover have "?non_redundant 0" using simplify_non_redundant by auto
          ultimately show "?P 0" by auto
      qed

text {* We then show that the properties are preserved by induction. *}

      next
      fix I assume "I \<le> N \<longrightarrow> ?P I" 
      show "(Suc I) \<le> N \<longrightarrow> (?P (Suc I))" 
      proof (rule impI)+
        assume  "(Suc I) \<le> N"
        let ?Prec = "resolvents_sequence A S I"
        let ?R = "resolvents_sequence A S (Suc I)"
        from `Suc I \<le> N` and `I \<le> N \<longrightarrow> ?P I` 
          have "?equiv_init I" and "?partial_saturation I" and "?no_tautologies I" and "?finite I"
            and "?atoms_init I" and "?non_redundant I" by auto
        have "equivalent ?Prec (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
          using resolvents_preserve_equivalence by auto
        from `?finite I` have "all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
          using all_resolvents_upon_is_finite by auto
        then have "all_fulfill finite (simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I))))" 
          using simplify_finite by auto
        then have "?finite (Suc I)" by auto
        from `all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))` 
          have "equivalent (?Prec \<union> (all_resolvents_upon ?Prec (A I))) ?R" 
        using simplify_preserves_equivalence by auto
        from `equivalent ?Prec (?Prec \<union> (all_resolvents_upon ?Prec (A I)))` 
        and `equivalent (?Prec \<union> (all_resolvents_upon ?Prec (A I))) ?R`
          have "equivalent ?Prec ?R" by (rule equivalent_transitive)
        from `?equiv_init I` and this have "?equiv_init (Suc I)" by (rule equivalent_transitive)
        have "?no_tautologies (Suc I)" using simplify_def strictly_redundant_def all_fulfill_def 
          by auto
        let ?Delta = "?R - ?Prec"
        have "?R \<subseteq> ?Prec \<union> ?Delta" by auto
        have "all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)"
        proof (rule ccontr)
          assume "\<not>all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)"
          then obtain x where "\<not>redundant x ?R" and "x \<in> ?Prec \<union> ?Delta" unfolding all_fulfill_def 
            by auto
          from `\<not>redundant x ?R` have "\<not>x \<in> ?R" unfolding redundant_def subsumes_def by auto
          with `x \<in> ?Prec \<union> ?Delta` have "x \<in> (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
            by auto
          with `all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))`
            have "redundant x (simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I))))"
              using simplify_and_membership by blast 
          with `\<not>redundant x ?R` show "False" by auto
        qed
        have "all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta"
        proof (rule ccontr)
          assume "\<not> (all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta)"
          then obtain C where "C \<in> ?Delta" 
            and "\<not>in_all_resolvents_upon ?Prec (A I) C" 
            unfolding all_fulfill_def by auto
          then obtain C where "C \<in> ?Delta" 
            and not_res: "\<forall> P1 P2. \<not>(P1 \<in> ?Prec \<and> P2 \<in> ?Prec \<and> C = resolvent_upon P1 P2 (A I))" 
            unfolding all_fulfill_def in_all_resolvents_upon_def by blast
          from `C \<in> ?Delta` have "C \<in> ?R" and "C \<notin> ?Prec" by auto 
          then have "C \<in> simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" by auto 
          then have "C \<in> ?Prec \<union> (all_resolvents_upon ?Prec (A I))" unfolding simplify_def by auto
          with `C \<notin> ?Prec` have "C \<in> (all_resolvents_upon ?Prec (A I))" by auto
          with not_res show "False" unfolding all_resolvents_upon_def by auto
        qed
        have "all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta"
        proof (rule ccontr)
          assume "\<not>all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta"
          then obtain C where "C \<in> ?Delta" and redundant: "redundant C ?Prec" 
            unfolding all_fulfill_def by auto
          from `C \<in> ?Delta` have "C \<in> ?R" and "C \<notin> ?Prec" by auto 
            show "False"
          proof cases
            assume "strictly_redundant C ?Prec"
            then have "strictly_redundant C (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
              unfolding strictly_redundant_def by auto
            then have "C \<notin> simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
              unfolding simplify_def by auto
            then have "C \<notin> ?R" by auto
            with `C \<in> ?R` show "False" by auto
            next assume "\<not>strictly_redundant C ?Prec"
            with redundant have "C \<in> ?Prec" 
              unfolding strictly_redundant_def redundant_def subsumes_def by auto
            with `C \<notin> ?Prec` show "False" by auto
          qed
        qed
        have "\<forall>J::nat. (J < (Suc I)) \<longrightarrow> (partial_saturation ?R (A J) ?R)"
        proof (rule ccontr)
          assume "\<not>(\<forall>J::nat. (J < (Suc I)) \<longrightarrow> (partial_saturation ?R (A J) ?R))"
          then obtain J where "J < (Suc I)" and "\<not>(partial_saturation ?R (A J) ?R)" by auto          
          from `\<not>(partial_saturation ?R (A J) ?R)` obtain P1 P2 C 
          where "P1 \<in> ?R" and "P2 \<in> ?R" and "C = resolvent_upon P1 P2 (A J)" and "\<not> redundant C ?R" 
          unfolding partial_saturation_def by auto
          have "partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)"
          proof (rule ccontr)
            assume "\<not>partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)"
            then obtain P1 P2 C where "P1 \<in> ?Prec" and "P2 \<in> ?Prec" 
              and "C = resolvent_upon P1 P2 (A I)" and 
              "\<not>redundant C (?Prec \<union> ?Delta)" unfolding partial_saturation_def by auto
            from `C = resolvent_upon P1 P2 (A I)` and `P1 \<in> ?Prec` and `P2 \<in> ?Prec` 
              have "C \<in> ?Prec \<union> (all_resolvents_upon ?Prec (A I))" 
              unfolding all_resolvents_upon_def by auto
            from `all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))` 
              and this have "redundant C ?R"  
              using simplify_and_membership [of "?Prec \<union> (all_resolvents_upon ?Prec (A I))" ?R C] 
              by auto
            with `?R \<subseteq> ?Prec \<union> ?Delta` have "redundant C (?Prec \<union> ?Delta)" 
            using superset_preserves_redundancy [of C ?R "(?Prec \<union> ?Delta)"] by auto
            with `\<not>redundant C (?Prec \<union> ?Delta)` show "False" by auto
          qed
          show "False"
          proof cases
            assume "J = I"
            from `partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)` and `?no_tautologies I` 
              and `(all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta)` 
              and `all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta`
              have "partial_saturation (?Prec \<union> ?Delta) (A I) (?Prec \<union> ?Delta)" 
              using ensures_partial_saturation [of ?Prec "(A I)" ?Delta] by auto
            with `?R \<subseteq> ?Prec \<union> ?Delta` 
              and `all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)`
            have "partial_saturation ?R (A I) ?R" using redundancy_implies_partial_saturation 
              by auto
            with `J = I` and `\<not>(partial_saturation ?R (A J) ?R)` show "False" by auto
          next 
            assume "J \<noteq> I"
            with `J < (Suc I)` have "J < I" by auto
            with `?partial_saturation I` 
              have "partial_saturation ?Prec (A J) ?Prec" by auto
            with `partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)` and `?no_tautologies I` 
              and `(all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta)`
              and `all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta` 
              have "partial_saturation (?Prec \<union> ?Delta) (A J) (?Prec \<union> ?Delta)"
              using partial_saturation_is_preserved [of ?Prec "A J" "A I" ?Delta] by auto
            with `?R \<subseteq> ?Prec \<union> ?Delta` 
              and `all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)`
              have "partial_saturation ?R (A J) ?R" 
              using redundancy_implies_partial_saturation by auto
            with `\<not>(partial_saturation ?R (A J) ?R)` show "False" by auto
         qed
       qed
       have  "non_redundant ?R" using simplify_non_redundant by auto
       from `?atoms_init I` have "atoms_formula (all_resolvents_upon ?Prec (A I)) 
                                    \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}"
       using atoms_formula_resolvents [of ?Prec "A I"] by auto
       with `?atoms_init I` 
        have "atoms_formula (?Prec \<union> (all_resolvents_upon ?Prec (A I))) 
                \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}"
        using atoms_formula_union [of ?Prec "all_resolvents_upon ?Prec (A I)"]  by auto
       from this have "atoms_formula ?R \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}"
       using atoms_formula_simplify [of "?Prec \<union> (all_resolvents_upon ?Prec (A I))"]  by auto
       from  `equivalent S (resolvents_sequence A S (Suc I))` 
          and `(\<forall>J::nat. (J < (Suc I) 
            \<longrightarrow> (partial_saturation (resolvents_sequence A S (Suc I)) (A J) 
                  (resolvents_sequence A S (Suc I)))))` 
          and `(all_fulfill (\<lambda>x. \<not>(tautology x)) (resolvents_sequence A S (Suc I)) )`
          and `(all_fulfill finite (resolvents_sequence A S (Suc I)))`
          and `non_redundant ?R`
          and `atoms_formula (resolvents_sequence A S (Suc I))  \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}`
       show "?P (Suc I)" by auto
     qed
   qed
  qed

text {* Using the above invariants, we show that the final clause set is saturated. *}

  from this have "\<forall>J. (J < N \<longrightarrow> partial_saturation ?Final (A J) ?Final)" 
    and "atoms_formula (resolvents_sequence A S N)  \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}" 
    and "equivalent S ?Final"
    and "non_redundant ?Final"
    and "all_fulfill finite ?Final"
  by auto
  have "saturated_binary_rule resolvent ?Final"
  proof (rule ccontr)
    assume "\<not> saturated_binary_rule resolvent ?Final"
    then obtain P1 P2 C where "P1 \<in> ?Final" and "P2 \<in> ?Final" and "resolvent P1 P2 C" 
      and "\<not>redundant C ?Final" 
      unfolding saturated_binary_rule_def by auto
    from `resolvent P1 P2 C` obtain B where "C = resolvent_upon P1 P2 B" 
      unfolding resolvent_def by auto
      show "False"
    proof cases
      assume "B \<in> (atoms_formula ?Final)"
      with `atoms_formula ?Final \<subseteq> { X. \<exists>I::nat. I < N \<and> X = (A I) }` 
        obtain I where "B = (A I)" and "I < N" 
        by auto
      from `B = (A I)` and `C = resolvent_upon P1 P2 B` have "C = resolvent_upon P1 P2 (A I)" 
        by auto
      from `\<forall>J. (J < N \<longrightarrow> partial_saturation ?Final (A J) ?Final)` and `B = (A I)`and `I < N` 
        have "partial_saturation ?Final (A I) ?Final" by auto 
      with `C = resolvent_upon P1 P2 (A I)`and `P1 \<in> ?Final` and `P2 \<in> ?Final`
        have "redundant C ?Final" unfolding partial_saturation_def by auto
      with `\<not>redundant C ?Final` show "False" by auto
    next 
      assume "B \<notin> atoms_formula ?Final"
      with `P1 \<in> ?Final` have "B \<notin> atoms_clause P1" by auto 
      then have "Pos B \<notin> P1" by auto 
      with `C = resolvent_upon P1 P2 B` have "P1 \<subseteq> C" by auto
      with `P1 \<in> ?Final` and  `\<not>redundant C ?Final` show "False" 
        unfolding redundant_def subsumes_def by auto
    qed
   qed
   with `all_fulfill finite ?Final` and `non_redundant ?Final` 
    have "prime_implicates ?Final = ?Final" 
    using prime_implicates_of_saturated_sets [of ?Final] by auto
   with `equivalent S ?Final` show ?thesis using  equivalence_and_prime_implicates by auto
qed

end
end
