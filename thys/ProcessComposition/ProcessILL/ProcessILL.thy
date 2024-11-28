theory ProcessILL
  imports
    ResourceILL
    ProcessComposition.Process
begin

section\<open>Process Compositions as ILL Deductions\<close>

text\<open>
  We show that process compositions correspond to deductions of linear logic such that the following
  properties hold:
  \<^item> For every valid composition the corresponding deduction is well-formed.
  \<^item> The conclusion of the deduction for compositions @{term x} is the sequent
    @{term "[resource_to_ill (input x)] \<turnstile> resource_to_ill (output x)"}.
  \<^item> Primitive actions of the composition correspond exactly to the premises of the deduction.
  \<^item> The structure of the composition matches that of the deduction.
\<close>

text\<open>
  We first use the shallow embedding of ILL deductions to show that a deduction satisfying the first
  two properties exists.
  However, this gives no assurance for the latter two properties.
  We then use the deep embedding of ILL deductions to construct the specific deduction for each
  composition and show that it satisfies all four properties for any valid composition.
\<close>

subsection\<open>Shallow Deduction\<close>

text\<open>
  With shallow deductions we can show that the input-output sequent is valid for every valid process
  composition assuming that input-output sequents of all of its primitive actions are valid. 
\<close>
lemma shallow_linearity:
  assumes "valid p"
      and "\<And>ins outs l m. (ins, outs, l, m) \<in> set (primitives p)
            \<Longrightarrow> [resource_to_ill ins] \<turnstile> resource_to_ill outs"
    shows "[resource_to_ill (input p)] \<turnstile> resource_to_ill (output p)"
  using assms
proof (induct p)
     case (Primitive x y l m) then show ?case by simp
next case (Identity x) then show ?case by simp
next
  case (Swap x y)
  moreover have
    " [res_term_to_ill (of_resource (Resource.Parallel [x, y]))]
    \<turnstile> res_term_to_ill (of_resource (Resource.Parallel [y, x]))"
  proof transfer
    fix x y :: "('a, 'b) res_term"
    have
      " [res_term_to_ill (normal_rewr (res_term.Parallel [x, y]))]
      \<turnstile> res_term_to_ill (res_term.Parallel [x, y])"
      using normal_rewr_ill_eq ill_eqE by blast
    also have "[...] \<turnstile> res_term_to_ill (res_term.Parallel [y, x])"
      using ILL.swap by simp
    also have "[...] \<turnstile> res_term_to_ill (normal_rewr (res_term.Parallel [y, x]))"
      using normal_rewr_ill_eq ill_eqE by blast
    finally show
      " [res_term_to_ill (normal_rewr (res_term.Parallel [x, y]))]
      \<turnstile> res_term_to_ill (normal_rewr (res_term.Parallel [y, x]))" .
  qed
  ultimately show ?case
    by (simp add: resource_par_def)
next case (Seq x y) then show ?case by simp (blast intro: simple_cut res_term_ill_equiv)
next
  case (Par x y)
  then have x: "[resource_to_ill (input x)] \<turnstile> resource_to_ill (output x)"
        and y: "[resource_to_ill (input y)] \<turnstile> resource_to_ill (output y)"
    by fastforce+

  have "[resource_to_ill (input x \<odot> input y)] \<turnstile> resource_to_ill (output x \<odot> output y)"
  proof -
    have "[resource_to_ill (input x \<odot> input y)]
      \<turnstile> resource_to_ill (input x) \<otimes> resource_to_ill (input y)"
      using normal_rewr_ill_eq[of "res_term.Parallel [_, _]"]
      by (fastforce simp add: of_resource_par)
    also have "[...] \<turnstile> resource_to_ill (output x) \<otimes> resource_to_ill (output y)"
      using x y tensor by metis
    also have "[...] \<turnstile> resource_to_ill (output x \<odot> output y)"
      using normal_rewr_ill_eq[of "res_term.Parallel [_, _]"]
      by (fastforce simp add: of_resource_par)
    finally show ?thesis .
  qed
  then show ?case
    by simp
next
  case (Opt x y)
  then have x: "[resource_to_ill (input x)] \<turnstile> resource_to_ill (output x)"
        and y: "[resource_to_ill (input y)] \<turnstile> resource_to_ill (output y)"
    by fastforce+

  have
    " [resource_to_ill (NonD (input x) (input y))]
    \<turnstile> resource_to_ill (input x) \<oplus> resource_to_ill (input y)"
    by simp
  also have "[...] \<turnstile> resource_to_ill (output x)"
    using Opt(3) x y by (simp add: simple_plusL)
  finally show ?case
    by simp
next case (InjectL x1 x2a) then show ?case by (simp add: plusR1)
next case (InjectR x1 x2a) then show ?case by (simp add: plusR2)
next
  case (OptDistrIn a b c)
  moreover have "[resource_to_ill (a \<odot> NonD b c)] \<turnstile> resource_to_ill (NonD (a \<odot> b) (a \<odot> c))"
  proof -
    have "[resource_to_ill (a \<odot> NonD b c)]
      \<turnstile> resource_to_ill a \<otimes> (resource_to_ill b \<oplus> resource_to_ill c)"
      using normal_rewr_ill_eq[of "res_term.Parallel [_, res_term.NonD _ _]"]
      by (fastforce simp add: of_resource_par)
    also have "[...]
      \<turnstile> (resource_to_ill a \<otimes> resource_to_ill b) \<oplus> (resource_to_ill a \<otimes> resource_to_ill c)"
      by (rule plus_distrib)
    also have "[...] \<turnstile> resource_to_ill (NonD (a \<odot> b) (a \<odot> c))"
      using normal_rewr_ill_eq[of "res_term.Parallel [_, _]"] plus_progress
      by (fastforce simp add: of_resource_par)
    finally show ?thesis .
  qed
  ultimately show ?case
    by simp
next
  case (OptDistrOut a b c)
  moreover have "[resource_to_ill (NonD (a \<odot> b) (a \<odot> c))] \<turnstile> resource_to_ill (a \<odot> NonD b c)"
  proof -
    have "[resource_to_ill (NonD (a \<odot> b) (a \<odot> c))]
      \<turnstile> (resource_to_ill a \<otimes> resource_to_ill b) \<oplus> (resource_to_ill a \<otimes> resource_to_ill c)"
      using normal_rewr_ill_eq[of "res_term.Parallel [_, _]"] plus_progress
      by (fastforce simp add: of_resource_par)
    also have "[...]
      \<turnstile> resource_to_ill a \<otimes> (resource_to_ill b \<oplus> resource_to_ill c)"
      by (rule plus_distrib')
    also have "[...] \<turnstile> resource_to_ill (a \<odot> NonD b c)"
      using normal_rewr_ill_eq[of "res_term.Parallel [_, res_term.NonD _ _]"]
      by (fastforce simp add: of_resource_par)
    finally show ?thesis .
  qed
  ultimately show ?case
    by simp
next case (Duplicate x) then show ?case by (simp add: of_resource_par duplicate)
next case (Erase x) then show ?case by (simp add: simple_weaken)
next case (Represent x) then show ?case by (simp add: simple_limpR_exp)
next
  case (Apply x y)
  moreover have "[resource_to_ill (x \<odot> Executable x y)] \<turnstile> resource_to_ill y"
  proof -
    have "[resource_to_ill (x \<odot> Executable x y)]
      \<turnstile> resource_to_ill x \<otimes> (resource_to_ill x \<rhd> resource_to_ill y)"
      using normal_rewr_ill_eq[of "res_term.Parallel [_, res_term.Executable _ _]"]
      by (fastforce simp add: of_resource_par)
    also have "[...] \<turnstile> resource_to_ill y"
      by (rule limp_eval)
    finally show ?thesis .
  qed
  ultimately show ?case
    by simp
next
  case (Repeat x y)
  moreover have
    "[resource_to_ill (Repeatable x y)] \<turnstile> resource_to_ill (Repeatable x y \<odot> Repeatable x y)"
  proof -
    have "[resource_to_ill (Repeatable x y)] \<turnstile> !(resource_to_ill x \<rhd> resource_to_ill y)"
      by simp
    also have "[...]
      \<turnstile> !(resource_to_ill x \<rhd> resource_to_ill y) \<otimes> !(resource_to_ill x \<rhd> resource_to_ill y)"
      by (rule duplicate)
    also have "[...] \<turnstile> resource_to_ill (Repeatable x y \<odot> Repeatable x y)"
      using normal_rewr_ill_eq[of
              "res_term.Parallel [res_term.Repeatable _ _, res_term.Repeatable _ _]"]
      by (fastforce simp add: of_resource_par)
    finally show ?thesis .
  qed
  ultimately show ?case
    by simp
next case (Close x y) then show ?case by (simp add: simple_weaken)
next case (Once x y) then show ?case by (simp add: simple_derelict)
next case (Forget x) then show ?case by (simp add: topR)
qed

text\<open>
  This proof on its own is not enough to verify our composition validity with respect to linear
  logic, because an undesirable definition of validity can still satisfy it.
  Consider for instance validity that also permits any composition whose input equals to its output.
  Even though this permits undesirable processes, such as composing in sequence identities on
  distinct resources, we can still prove an equivalent of the shallow linearity theorem.
  We formally explore this in an anonymous context before using the deep embedding of deductions to
  address this weakness.
\<close>
experiment
begin

text\<open>Define the bad validity predicate by adding a special case to our original validity\<close>
definition "valid_bad x = (valid x \<or> input x = output x)"

text\<open>
  This permits, for instance, a composition of three identities as long as the first and last ones
  are on the same resource even if the middle one is on a distinct resource.
\<close>
lemma
  "valid_bad (Seq (Identity Empty) (Seq (Identity Anything) (Identity Empty)))"
  by (simp add: valid_bad_def)

text\<open>
  But we can prove the shallow linearity theorem for this validity predicate by handling the special
  case with the ILL identity rule @{thm sequent.identity}
\<close>
lemma
  assumes "valid_bad p"
      and "\<And>ins outs l m. (ins, outs, l, m) \<in> set (primitives p)
            \<Longrightarrow> [resource_to_ill ins] \<turnstile> resource_to_ill outs"
    shows "[resource_to_ill (input p)] \<turnstile> resource_to_ill (output p)"
proof (cases "valid p")
  case True
  then show ?thesis
    using assms(2) by (rule shallow_linearity)
next
  case False
  then have "input p = output p"
    using assms(1) by (simp add: valid_bad_def)
  then show ?thesis
    \<comment> \<open>Uses: @{thm sequent.identity[of "resource_to_ill (input p)"]}\<close>
    by simp
qed

end

subsection\<open>Deep Deduction\<close>

text\<open>
  To demonstrate all four properties, we use the deep embedding of deductions to construct the
  specific deduction for each process composition.
  Not only can we then show that the deduction is well-formed for valid compositions and has the
  input-output sequent as conclusion, we also know that it corresponds in structure to the process
  composition (because it is defined by primitive recursion).
  Furthermore, we can show that its premises correspond to the primitive actions of the process.
\<close>

text\<open>
  The deduction we construct combines the linear and copyable resource atoms to form the
  propositions, and the primitive action labels and metadata to form the premise labels.
\<close>
primrec to_deduct :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a + 'b, 'l \<times> 'm) ill_deduct"
  where
    "to_deduct (Primitive a b l m) = Premise [resource_to_ill a] (resource_to_ill b) (l, m)"
  | "to_deduct (Identity a) = ill_deduct.Identity (resource_to_ill a)"
  | "to_deduct (Swap a b) =
      ill_deduct_simple_cut
      ( ill_deduct_res_term_from_normal_rewr (res_term.Parallel [of_resource a, of_resource b]))
      ( ill_deduct_simple_cut
        ( ill_deduct_swap (resource_to_ill a) (resource_to_ill b))
        ( ill_deduct_res_term_to_normal_rewr (res_term.Parallel [of_resource b, of_resource a])))"
  | "to_deduct (Seq f g) =
      ill_deduct_simple_cut
      ( to_deduct f)
      ( to_deduct g)"
  | "to_deduct (Par p q) =
      ill_deduct_simple_cut
      ( ill_deduct_res_term_from_normal_rewr
        ( res_term.Parallel [of_resource (input p), of_resource (input q)]))
      ( ill_deduct_simple_cut
        ( ill_deduct_tensor
          ( to_deduct p)
          ( to_deduct q))
        ( ill_deduct_res_term_to_normal_rewr
          ( res_term.Parallel [of_resource (output p), of_resource (output q)])))"
  | "to_deduct (Opt p q) =
      ill_deduct_simple_plusL
      ( to_deduct p)
      ( to_deduct q)"
  | "to_deduct (InjectL a b) = ill_deduct_plusR1 (resource_to_ill a) (resource_to_ill b)"
  | "to_deduct (InjectR a b) = ill_deduct_plusR2 (resource_to_ill a) (resource_to_ill b)"
  | "to_deduct (OptDistrIn a b c) =
      ill_deduct_simple_cut
      ( ill_deduct_res_term_from_normal_rewr
        ( res_term.Parallel [of_resource a, of_resource (NonD b c)]))
      ( ill_deduct_simple_cut
        ( ill_deduct_distrib_plus (resource_to_ill a) (resource_to_ill b) (resource_to_ill c))
        ( ill_deduct_plus_progress
          ( ill_deduct_res_term_to_normal_rewr (res_term.Parallel [of_resource a, of_resource b]))
          ( ill_deduct_res_term_to_normal_rewr (res_term.Parallel [of_resource a, of_resource c]))))"
  | "to_deduct (OptDistrOut a b c) =
      ill_deduct_simple_cut
      ( ill_deduct_plus_progress
        ( ill_deduct_res_term_from_normal_rewr (res_term.Parallel [of_resource a, of_resource b]))
        ( ill_deduct_res_term_from_normal_rewr (res_term.Parallel [of_resource a, of_resource c])))
      ( ill_deduct_simple_cut
        ( ill_deduct_distrib_plus' (resource_to_ill a) (resource_to_ill b) (resource_to_ill c))
        ( ill_deduct_res_term_to_normal_rewr
          ( res_term.Parallel [of_resource a, of_resource (NonD b c)])))"
  | "to_deduct (Duplicate a) = ill_deduct_duplicate (Prop (Inr a))"
  | "to_deduct (Erase a) = ill_deduct_simple_weaken (Prop (Inr a))"
  | "to_deduct (Represent p) = ill_deduct_simple_limpR_exp (to_deduct p)"
  | "to_deduct (Apply a b) =
      ill_deduct_simple_cut
      ( ill_deduct_res_term_from_normal_rewr
        ( res_term.Parallel [of_resource a, of_resource (Executable a b)]))
      ( ill_deduct_simple_cut
        ( ill_deduct_limp_eval (resource_to_ill a) (resource_to_ill b))
        ( ill_deduct_res_term_to_normal_rewr (of_resource b)))"
  | "to_deduct (Repeat a b) = ill_deduct_duplicate (resource_to_ill (Executable a b))"
  | "to_deduct (Close a b) = ill_deduct_simple_weaken (resource_to_ill (Executable a b))"
  | "to_deduct (Once a b) = ill_deduct_dereliction (resource_to_ill (Executable a b))"
    \<comment> \<open>The above three processes use @{const Repeatable} resources but their deductions use as
        argument @{const Executable} resources instead, because the deduction patterns expect
        unexponentiated propositions which is exactly the difference between the two resource types'
        translations.\<close>
  | "to_deduct (Forget a) = TopR [resource_to_ill a]"

text\<open>Conclusion of the deduction is the input-output sequent of the process\<close>
lemma to_deduct_conclusion [simp]:
  includes deep_sequent shows
  "ill_conclusion (to_deduct P) = [resource_to_ill (input P)] \<turnstile> resource_to_ill (output P)"
proof (induct P)
  case (Primitive ins outs l m) then show ?case by simp
next
  case (Seq P1 P2)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (Par P1 P2)
  then show ?case
    by (simp add: of_resource_par ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (Opt P1 P2)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (Represent P)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next case (Identity x) then show ?case by simp
next
  case (Swap x y)
  then show ?case
    by (simp add: of_resource_par ill_conclusion_antecedents ill_conclusion_consequent)
next case (InjectL x y) then show ?case by simp
next case (InjectR x y) then show ?case by simp
next
  case (OptDistrIn x y z)
  then show ?case
    by (simp add: of_resource_par ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (OptDistrOut x y z)
  then show ?case
    by (simp add: of_resource_par ill_conclusion_antecedents ill_conclusion_consequent)
next case (Duplicate x) then show ?case by (simp add: of_resource_par)
next case (Erase x) then show ?case by simp
next
  case (Apply x y)
  then show ?case
    by (simp add: of_resource_par ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (Repeat x y)
  then show ?case
    by (simp add: of_resource_par normal_rewr_is_normal_dir)
next case (Close x y) then show ?case by simp
next case (Once x y) then show ?case by simp
next case (Forget x) then show ?case by simp
qed

text\<open>
  Not only is the deduction for valid composition well-formed, this relation is actually an equality
  thanks to the injectivity of the resource translation.
\<close>
lemma valid_to_deduct_wf:
  "valid P = ill_deduct_wf (to_deduct P)"
proof (induct P)
  case (Primitive ins outs l m) then show ?case by simp
next
  case (Seq P1 P2)
  then show ?case
    using resource_to_ill_inject
    by (fastforce simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (Par P1 P2)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (Opt P1 P2)
  then show ?case
    using resource_to_ill_inject
    by (fastforce simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (Represent P)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next case (Identity x) then show ?case by simp
next
  case (Swap x y)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next case (InjectL x y) then show ?case by simp
next case (InjectR x y) then show ?case by simp
next
  case (OptDistrIn x y z)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next
  case (OptDistrOut x y z)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next case (Duplicate x) then show ?case by simp
next case (Erase x) then show ?case by simp
next
  case (Apply x y)
  then show ?case
    by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
next case (Repeat x y) then show ?case by simp
next case (Close x y) then show ?case by simp
next case (Once x y) then show ?case by simp
next case (Forget x) then show ?case by simp
qed

text\<open>
  With the specific deduction on hand, we can show that its premises correspond to the primitive
  actions of the composition.
  This includes their order in the deduction/composition trees.
  Specifically, the list of premises can be obtained by mapping a bijective function over the list
  of primitive actions.
\<close>
lemma primitives_give_premises:
  " map (\<lambda>(a, b, l, m). ([resource_to_ill a], resource_to_ill b, (l, m))) (primitives P)
  = ill_deduct_premises (to_deduct P)"
  by (induct P) simp_all
lemma primitive_premise_bij:
  "bij_betw (\<lambda>(a, b, l, m). ([resource_to_ill a], resource_to_ill b, (l, m)))
    (set (primitives P))
    (set (ill_deduct_premises (to_deduct P)))"
proof -
  have "inj_on (\<lambda>(a, b, l, m). ([resource_to_ill a], resource_to_ill b, (l, m)))
          (set (primitives P))"
    using resource_to_ill_inject by (fastforce simp add: inj_on_def)
  moreover have
    " (\<lambda>(a, b, l, m). ([resource_to_ill a], resource_to_ill b, (l, m))) ` set (primitives P)
    = set (ill_deduct_premises (to_deduct P))"
    by (induct P) (simp_all add: image_Un inj_on_Un)
  ultimately show ?thesis
    by (simp add: bij_betw_def)
qed

text\<open>
  Further supporting the structural correspondence between the composition and deduction,
  substituting compositions for primitive actions is the same as substituting their translations
  for the corresponding premises.
  Because the ILL deduction steps are not just parameterised by the other deductions they rely on
  but also the propositions instantiating the rule itself, the substitution also needs to preserve
  the process input and output.
\<close>
lemma to_deduct_subst:
  assumes "\<And>a b l m. P a b l m = P' [resource_to_ill a] (resource_to_ill b) (l, m)"
      and "\<And>a b l m. to_deduct (f a b l m) = f' [resource_to_ill a] (resource_to_ill b) (l, m)"
      and "\<And>a b l m. P a b l m \<Longrightarrow> input (f a b l m) = a"
      and "\<And>a b l m. P a b l m \<Longrightarrow> output (f a b l m) = b"
    shows "to_deduct (process_subst P f x) = ill_deduct_subst P' f' (to_deduct x)"
proof -
  have [simp]: "antecedents (ill_deduct_subst P' f' (to_deduct x)) = [resource_to_ill (input x)]"
    if "to_deduct (process_subst P f x) = ill_deduct_subst P' f' (to_deduct x)" for x
  proof -
    have
      " antecedents (ill_deduct_subst P' f' (to_deduct x))
      = antecedents (to_deduct (process_subst P f x))"
      using that by metis
    also have "... = [resource_to_ill (input (process_subst P f x))]"
      using to_deduct_conclusion ill_conclusion_antecedents by metis
    also have "... = [resource_to_ill (input x)]"
      using assms(3) process_subst_input by metis
    finally show ?thesis .
  qed
  have [simp]: "consequent (ill_deduct_subst P' f' (to_deduct x)) = resource_to_ill (output x)"
    if "to_deduct (process_subst P f x) = ill_deduct_subst P' f' (to_deduct x)" for x
  proof -
    have
      " consequent (ill_deduct_subst P' f' (to_deduct x))
      = consequent (to_deduct (process_subst P f x))"
      using that by metis
    also have "... = resource_to_ill (output (process_subst P f x))"
      using to_deduct_conclusion ill_conclusion_consequent by metis
    also have "... = resource_to_ill (output x)"
      using assms(3,4) process_subst_output by metis
    finally show ?thesis .
  qed

  have "to_deduct (process_subst P f x) = ill_deduct_subst P' f' (to_deduct x)"
    if "x = Primitive a b l m" for x a b l m
    using that by (simp add: assms(1,2))
  then show ?thesis
    by (induct x)
       (fastforce simp add: assms(3,4)
          ill_conclusion_antecedents ill_conclusion_consequent ill_deduct_subst_no_prems)+
qed

end