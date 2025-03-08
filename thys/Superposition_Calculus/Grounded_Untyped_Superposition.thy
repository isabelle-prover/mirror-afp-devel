theory Grounded_Untyped_Superposition
  imports Untyped_Superposition Grounded_Superposition
begin

context untyped_superposition_calculus
begin

sublocale typed: superposition_calculus where \<F> = "\<lambda>f n. (replicate n (), ())"
proof unfold_locales
  show "\<And>\<tau>. \<exists>f. (replicate 0 (), ()) = ([], \<tau>)"
    by simp
qed

lemma all_welltyped [intro]: "typed.welltyped \<V> t ()"
proof (induction t)
  case (Var x)
  then show ?case
    by auto
next
  case (Fun f ts)

  show ?case
  proof(rule typed.welltyped.Fun)
    show "(replicate (length ts) (), ()) = (replicate (length ts) (), ())"
      by simp
  next
    from Fun
    show "list_all2 (typed.welltyped \<V>) ts (replicate (length ts) ())"
      by (induction ts) simp_all
  qed
qed

lemma all_infinite_variables_per_type [intro]: 
  fixes \<V> :: "'v \<Rightarrow> unit"
  shows "infinite_variables_per_type_on X \<V>"
  unfolding infinite_variables_per_type_on_def
  using infinite_UNIV
  by auto

lemma typed_eq_resolution_eq_eq_resolution [simp]: 
  "typed.eq_resolution (D, \<V>) (C, \<V>) \<longleftrightarrow> eq_resolution D C"
proof (rule iffI)
  assume "typed.eq_resolution (D, \<V>) (C, \<V>)"
  
  then show "eq_resolution D C"
  proof (cases rule: typed.eq_resolution.cases)
    case typed_eq_resolutionI: (eq_resolutionI t t' \<mu> l D')
    
    then show ?thesis
      by (intro eq_resolutionI) auto
  qed
next
  assume "eq_resolution D C"

  then show "typed.eq_resolution (D, \<V>) (C, \<V>)"
  proof (cases rule: eq_resolution.cases)
    case (eq_resolutionI \<mu> t t' l D')
    
    then show ?thesis
      by (intro typed.eq_resolutionI) auto
  qed
qed

lemma typed_eq_factoring_eq_eq_factoring [simp]: 
  "typed.eq_factoring (D, \<V>) (C, \<V>) \<longleftrightarrow> eq_factoring D C"
proof (rule iffI)
  assume "typed.eq_factoring (D, \<V>) (C, \<V>)"
  
  then show "eq_factoring D C"
  proof (cases rule: typed.eq_factoring.cases)
    case typed_eq_factoringI: (eq_factoringI t t' \<mu> l D')
    
    then show ?thesis
      by (intro eq_factoringI) auto
  qed
next
  assume "eq_factoring D C"

  then show "typed.eq_factoring (D, \<V>) (C, \<V>)"
  proof (cases rule: eq_factoring.cases)
    case (eq_factoringI l\<^sub>1 \<mu> t\<^sub>1 t\<^sub>1' t\<^sub>2 l\<^sub>2 D' t\<^sub>2')
    
    then show ?thesis
      by (intro typed.eq_factoringI) auto
  qed
qed

lemma typed_superposition_eq_superposition [simp]:
  "typed.superposition (D, \<V>\<^sub>1) (E, \<V>\<^sub>2) (C, \<V>\<^sub>3) \<longleftrightarrow> superposition D E C"
proof (rule iffI)
  assume "typed.superposition (D, \<V>\<^sub>1) (E, \<V>\<^sub>2) (C, \<V>\<^sub>3)"
  
  then show "superposition D E C"
  proof (cases rule: typed.superposition.cases)
    case typed_superpositionI: (superpositionI \<P> \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 t\<^sub>2 \<mu> c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 E' D')
    
    show ?thesis
    proof(intro superpositionI; (rule typed_superpositionI)?)

      show "term.is_imgu \<mu> {{t\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
        using typed_superpositionI
        by argo
    qed
  qed
next
  assume "superposition D E C"

  then show "typed.superposition (D, \<V>\<^sub>1) (E, \<V>\<^sub>2) (C, \<V>\<^sub>3)"
  proof (cases rule: superposition.cases)
    case (superpositionI \<P> \<rho>\<^sub>1 \<rho>\<^sub>2 t\<^sub>1 \<mu> t\<^sub>2 c\<^sub>1 t\<^sub>1' t\<^sub>2' l\<^sub>1 l\<^sub>2 E' D')
   
    show ?thesis
    proof (intro typed.superpositionI; (rule superpositionI all_infinite_variables_per_type)?)

      show "typed.welltyped_imgu_on 
              (clause.vars (E \<cdot> \<rho>\<^sub>1) \<union> clause.vars (D \<cdot> \<rho>\<^sub>2)) \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu>"
        using superpositionI(6)
        by auto

    qed auto
  qed
qed

abbreviation bottom\<^sub>F :: "('f, 'v) atom clause set" where
  "bottom\<^sub>F \<equiv> {{#}}"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> { Infer [D] C | D C. eq_factoring D C }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> { Infer [D] C | D C. eq_resolution D C }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [D, E] C | D E C. superposition D E C }"

definition inferences :: "('f, 'v) atom clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation empty_typed :: "'C \<Rightarrow> ('C \<times> ('v \<Rightarrow> unit))" where
  "empty_typed C \<equiv> (C, (\<lambda>_. ()))"

abbreviation empty_typed_inference :: "'C inference \<Rightarrow> ('C \<times> ('v \<Rightarrow> unit)) inference" where
  "empty_typed_inference \<iota> \<equiv> Infer (map empty_typed (prems_of \<iota>)) (empty_typed (concl_of \<iota>))"

lemma \<V>_all_same [simp]:
  fixes \<V> :: "'v \<Rightarrow> unit"
  shows "\<V> = (\<lambda>_. ())"
  by auto

lemma typed_eq_factoring_inferences [simp]: 
  "typed.eq_factoring_inferences = empty_typed_inference ` eq_factoring_inferences"
proof -
  {
    fix D C \<V>\<^sub>1 \<V>\<^sub>2

    assume "typed.eq_factoring (D, \<V>\<^sub>1) (C, \<V>\<^sub>2)"

    then have "Infer [(D, \<V>\<^sub>1)] (C, \<V>\<^sub>2) \<in> empty_typed_inference ` eq_factoring_inferences"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2]
      by force
  }

  then show ?thesis
    by auto
qed

lemma typed_eq_resolution_inferences [simp]: 
  "typed.eq_resolution_inferences = empty_typed_inference `  eq_resolution_inferences"
proof -
  {
    fix D C \<V>\<^sub>1 \<V>\<^sub>2

    assume "typed.eq_resolution (D, \<V>\<^sub>1) (C, \<V>\<^sub>2)"

    then have "Infer [(D, \<V>\<^sub>1)] (C, \<V>\<^sub>2) \<in> empty_typed_inference ` eq_resolution_inferences"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2]
      by force
  }
  
  then show ?thesis
    by auto
qed

lemma typed_superposition_inferences [simp]: 
  "typed.superposition_inferences = empty_typed_inference ` superposition_inferences"
proof -
  {
    fix D E C \<V>\<^sub>1 \<V>\<^sub>2 \<V>\<^sub>3

    assume "typed.superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

    then have "Infer [(D, \<V>\<^sub>2), (E, \<V>\<^sub>1)] (C, \<V>\<^sub>3) \<in> empty_typed_inference ` superposition_inferences"
      unfolding \<V>_all_same[of \<V>\<^sub>1] \<V>_all_same[of \<V>\<^sub>2] \<V>_all_same[of \<V>\<^sub>3]
      by force
  }

  then show ?thesis
    by auto
qed

lemma typed_inferences [simp]: "typed.inferences = empty_typed_inference ` inferences"
  unfolding
    inferences_def
    typed.inferences_def
    typed_superposition_inferences
    typed_eq_resolution_inferences
    typed_eq_factoring_inferences
  by auto

(* TODO: tiebreaker ? *)
sublocale standard_lifting where 
  Bot_F = bottom\<^sub>F and
  Inf_F = inferences and
  Bot_G  = typed.bottom\<^sub>F and
  entails_G = typed.entails_\<G> and
  Inf_G = typed.inferences and
  Red_I_G = typed.Red_I and
  Red_F_G = typed.Red_F and
  \<G>_F = "\<lambda>C. {empty_typed C}" and
  \<G>_I = "\<lambda>\<iota>. Some {empty_typed_inference \<iota>}"
proof unfold_locales
  fix \<iota>

  assume "\<iota> \<in> inferences"

  then have "empty_typed_inference \<iota> \<in> typed.inferences"
    by simp

  then have "empty_typed_inference \<iota> \<in> typed.Red_I_\<G> {empty_typed (concl_of \<iota>)}"
    by (rule typed.Red_I_of_Inf_to_N) simp

  then show "the (Some {empty_typed_inference \<iota>}) \<subseteq> typed.Red_I_\<G> {empty_typed (concl_of \<iota>)}"
    by simp

qed auto

end

end