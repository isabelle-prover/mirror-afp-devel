theory ResTermILL
  imports
    ProcessComposition.ResNormRewrite
    ILL.Proof
begin

section\<open>Resource Terms as ILL Propositions\<close>

text\<open>
  We represent resource terms with propositions of intuitionistic linear logic in such a way that
  equivalent resource terms are represented by propositions equivalent in the logic.
  We demonstrate that fact with functions that generate a deeply embedded deduction for any pair of
  equivalent terms, following the structure of the rewriting normalisation procedure.
  Because linear logic only has one type of propositional atoms, we use the sum type to merge the
  two atom types of resource terms (linear and copyable atoms).
\<close>

primrec res_term_to_ill :: "('a, 'b) res_term \<Rightarrow> ('a + 'b) ill_prop"
  where
    "res_term_to_ill Empty = \<one>"
  | "res_term_to_ill Anything = \<top>"
  | "res_term_to_ill (Res x) = Prop (Inl x)"
  | "res_term_to_ill (Copyable r) = !(Prop (Inr r))"
  | "res_term_to_ill (Parallel rs) = compact (map res_term_to_ill rs)"
  | "res_term_to_ill (NonD r t) = (res_term_to_ill r) \<oplus> (res_term_to_ill t)"
  | "res_term_to_ill (Executable a b) = (res_term_to_ill a) \<rhd> (res_term_to_ill b)"
  | "res_term_to_ill (Repeatable a b) = !((res_term_to_ill a) \<rhd> (res_term_to_ill b))"

text\<open>
  It will be useful to prove when the representation of a term in a list cannot be @{const ILL.One}
  or @{const ILL.Times}, as these must be considered when relating to equivalence of
  @{const Parallel} terms
\<close>
lemma res_term_to_ill_not_one:
  assumes "\<not> list_ex is_Parallel xs"
      and "\<not> list_ex is_Empty xs"
      and "x \<in> set xs"
    shows "res_term_to_ill x \<noteq> \<one>"
  using assms by (cases x) (fastforce simp add: Bex_set[symmetric])+

lemma res_term_to_ill_not_times:
  assumes "\<not> list_ex is_Parallel xs"
      and "x \<in> set xs"
    shows "res_term_to_ill x \<noteq> a \<otimes> b"
  using assms by (cases x) (fastforce simp add: Bex_set[symmetric])+

text\<open>Resource term translation is injective on normalised terms\<close>
lemma res_term_to_ill_inject:
  assumes "normalised x"
      and "normalised y"
      and "res_term_to_ill x = res_term_to_ill y"
    shows "x = y"
proof -
  have [simp]: "(a = compact xs) = (xs = [a])"
    if "\<And>x y. a \<noteq> x \<otimes> y" and "a \<noteq> \<one>" for a :: "('a + 'b) ill_prop" and xs
    using that
  proof (induct xs)
       case Nil then show ?case by simp
  next case (Cons a xs) then show ?case by simp (metis compact_code(2))
  qed
  then have [simp]: "(compact xs = a) = (xs = [a])"
    if "\<And>x y. a \<noteq> x \<otimes> y" and "a \<noteq> \<one>" for a :: "('a + 'b) ill_prop" and xs
    using that by metis
  note [elim] = compact_eq_oneE[OF sym] compact_eq_oneE

  show ?thesis
    using assms
  proof (induct x arbitrary: y)
       case Empty then show ?case by (cases y) force+
  next case Anything then show ?case by (cases y) clarsimp+
  next case (Res a) then show ?case by (cases y) clarsimp+
  next case (Copyable u) then show ?case by (cases y) clarsimp+
  next case (NonD u v) then show ?case by (cases y) clarsimp+
  next case (Executable u v) then show ?case by (cases y) clarsimp+
  next case (Repeatable u v) then show ?case by (cases y) clarsimp+
  next
    case x: (Parallel xs)
    show ?case
    proof (cases y)
         case Empty then show ?thesis using x by fastforce
    next case Anything then show ?thesis using x by clarsimp
    next case (Res a) then show ?thesis using x by clarsimp
    next case (Copyable u) then show ?thesis using x by clarsimp
    next case (NonD u v) then show ?thesis using x by clarsimp
    next case (Executable u v) then show ?thesis using x by clarsimp
    next case (Repeatable u v) then show ?thesis using x by clarsimp
    next
      case (Parallel ys)
  
      have "compact (map res_term_to_ill xs) = compact (map res_term_to_ill ys)"
        using x Parallel by simp
      then have "map res_term_to_ill xs = map res_term_to_ill ys"
        using compact_eq res_term_to_ill_not_one res_term_to_ill_not_times
        using Parallel x
        by (smt (verit) Ball_set_list_all Bex_set image_iff list.set_map normalised.simps(5))
      then have "xs = ys"
        using x Parallel
        by (metis (mono_tags, lifting) list.inj_map_strong normalised_parallel_children)
      then show ?thesis
        using Parallel by simp
    qed
  qed
qed

text\<open>
  First we verify that equivalent resource terms give equivalent propositions using the shallow
  embedding.
  This proves the existence of a deduction, while our later construction of the deep embedding
  builds the specific deduction for that case.
\<close>
lemma res_term_ill_equiv:
  "a \<sim> b \<Longrightarrow> res_term_to_ill a \<stileturn>\<turnstile> res_term_to_ill b"
proof (induct rule: res_term_equiv.induct)
     case empty then show ?case by simp
next case anything then show ?case by simp
next case (res x) then show ?case by simp
next case (copyable x) then show ?case by simp
next case nil then show ?case by simp
next case (singleton a) then show ?case by simp
next
  case (merge a xs b)
  then show ?case
    by simp
       (metis ill_eqI append.left_neutral append_Cons append_Nil2 compact_antecedents identity_list)
next
  case (parallel xs ys)
  then show ?case
  proof (induct rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    have
      "  res_term_to_ill x \<otimes> compact (map res_term_to_ill xs)
      \<stileturn>\<turnstile> res_term_to_ill y \<otimes> compact (map res_term_to_ill ys)"
      using Cons ill_eq_tensor by auto
    then have
      "  compact (res_term_to_ill x # map res_term_to_ill xs)
      \<stileturn>\<turnstile> compact (res_term_to_ill y # map res_term_to_ill ys)"
      using times_equivalent_cons times_equivalent_cons[symmetric] ill_eq_tran by (smt (z3))
    then show ?case
      by simp
  qed
next
  case (nondet x y u v)
  then show ?case by (simp add: ill_eq_def plusR1 sequent.intros(16) simple_plusL)
next
  case (executable x y u v)
  then show ?case
    by (simp add: ill_eq_def) (metis limpL append_Cons append_Nil limpR)
next
  case (repeatable x y u v)
  then show ?case
    apply simp
    apply standard

     apply (rule promote[of "[_]", unfolded list.map])
     apply (rule simple_derelict)
     apply (metis limpL append_Cons append_Nil ill_eqE limpR)

     apply (rule promote[of "[_]", unfolded list.map])
     apply (rule simple_derelict)
    apply (metis limpL append_Cons append_Nil ill_eqE limpR)

    done
next case (sym x y) then show ?case by (simp add: ill_eq_sym)
next case (trans x y z) then show ?case using ill_eq_tran by blast
qed

subsection\<open>Relating to Rewriting Step\<close>

text\<open>
  Because @{const step} rewrites a resource to an equivalent one, the ILL representations remain
  equivalent, meaning there is a deduction we can construct.
  Inspecting individual cases using procedural proof can be useful for defining that deduction.
\<close>
lemma step_ill_eq:
  "res_term_to_ill a \<stileturn>\<turnstile> res_term_to_ill (step a)"
  using res_term_ill_equiv res_term_equiv_step by blast

text\<open>
  In our construction of the deduction we follow the definition of @{const step}.
  As such, we first define deductions for @{const remove_one_empty} and @{const merge_one_parallel}.

  Note that, in these functions, if the relevant term is not in the list the deduction is left
  undefined.
  This does not hinder their use, because we first check that the relevant term is present before
  applying them.
\<close>

fun ill_deduct_to_remove_empty :: "('a, 'b) res_term list \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "[res_term_to_ill (Parallel xs)] \<turnstile> res_term_to_ill (Parallel (remove_one_empty xs))"}\<close>
  where
    "ill_deduct_to_remove_empty [] = undefined"
  | "ill_deduct_to_remove_empty (x#xs) =
      (if x = Empty
        then ill_deduct_simple_cut
              (ill_deduct_compact_cons_to_times (\<one>) (map res_term_to_ill xs))
              (ill_deduct_simple_cut
                (ill_deduct_swap (\<one>) (compact (map res_term_to_ill xs)))
                (ill_deduct_unit (compact (map res_term_to_ill xs))))
        else ill_deduct_simple_cut
              (ill_deduct_compact_cons_to_times (res_term_to_ill x) (map res_term_to_ill xs))
              (ill_deduct_simple_cut
                (ill_deduct_tensor
                  (Identity (res_term_to_ill x))
                  (ill_deduct_to_remove_empty xs))
                (ill_deduct_times_to_compact_cons
                  (res_term_to_ill x)
                  (map res_term_to_ill (remove_one_empty xs)))))"

lemma ill_deduct_to_remove_empty [simp]:
  assumes "list_ex is_Empty xs"
    shows
      " ill_conclusion (ill_deduct_to_remove_empty xs)
      = Sequent [res_term_to_ill (Parallel xs)] (res_term_to_ill (Parallel (remove_one_empty xs)))"
    and "ill_deduct_premises (ill_deduct_to_remove_empty xs) = []"
    and "ill_deduct_wf (ill_deduct_to_remove_empty xs)"
proof -
  have [simp]:
    " ill_conclusion (ill_deduct_to_remove_empty xs)
    = Sequent [res_term_to_ill (Parallel xs)] (res_term_to_ill (Parallel (remove_one_empty xs)))"
    if "list_ex is_Empty xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
  then show
    " ill_conclusion (ill_deduct_to_remove_empty xs)
    = Sequent [res_term_to_ill (Parallel xs)] (res_term_to_ill (Parallel (remove_one_empty xs)))"
    using assms .

  have "ill_deduct_premises (ill_deduct_to_remove_empty xs) = []"
    if "list_ex is_Empty xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) simp_all
  qed
  then show "ill_deduct_premises (ill_deduct_to_remove_empty xs) = []"
    using assms .

  show "ill_deduct_wf (ill_deduct_to_remove_empty xs)"
    using assms
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
qed

fun ill_deduct_from_remove_empty :: "('a, 'b) res_term list \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "[res_term_to_ill (Parallel (remove_one_empty xs))] \<turnstile> res_term_to_ill (Parallel xs)"}\<close>
  where
    "ill_deduct_from_remove_empty [] = undefined"
  | "ill_deduct_from_remove_empty (x#xs) =
      (if x = Empty
        then ill_deduct_simple_cut
              (ill_deduct_unit' (compact (map res_term_to_ill xs)))
              (ill_deduct_simple_cut
                (ill_deduct_swap (compact (map res_term_to_ill xs)) (\<one>))
                (ill_deduct_times_to_compact_cons (\<one>) (map res_term_to_ill xs)))
        else ill_deduct_simple_cut
              (ill_deduct_compact_cons_to_times
                (res_term_to_ill x)
                (map res_term_to_ill (remove_one_empty xs)))
              (ill_deduct_simple_cut
                (ill_deduct_tensor
                  (Identity (res_term_to_ill x))
                  (ill_deduct_from_remove_empty xs))
                (ill_deduct_times_to_compact_cons (res_term_to_ill x) (map res_term_to_ill xs))))"

lemma ill_deduct_from_remove_empty [simp]:
  assumes "list_ex is_Empty xs"
    shows
      " ill_conclusion (ill_deduct_from_remove_empty xs)
      = Sequent [res_term_to_ill (Parallel (remove_one_empty xs))] (res_term_to_ill (Parallel xs))"
    and "ill_deduct_premises (ill_deduct_from_remove_empty xs) = []"
    and "ill_deduct_wf (ill_deduct_from_remove_empty xs)"
proof -
  have [simp]:
    " ill_conclusion (ill_deduct_from_remove_empty xs)
    = Sequent [res_term_to_ill (Parallel (remove_one_empty xs))] (res_term_to_ill (Parallel xs))"
    if "list_ex is_Empty xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
  then show
    " ill_conclusion (ill_deduct_from_remove_empty xs)
    = Sequent [res_term_to_ill (Parallel (remove_one_empty xs))] (res_term_to_ill (Parallel xs))"
    using assms .

  have "ill_deduct_premises (ill_deduct_from_remove_empty xs) = []"
    if "list_ex is_Empty xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) simp_all
  qed
  then show "ill_deduct_premises (ill_deduct_from_remove_empty xs) = []"
    using assms .

  show "ill_deduct_wf (ill_deduct_from_remove_empty xs)"
    using assms
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
qed

fun ill_deduct_to_merge_parallel :: "('a, 'b) res_term list \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "[res_term_to_ill (Parallel xs)] \<turnstile> res_term_to_ill (Parallel (merge_one_parallel xs))"}\<close>
  where
    "ill_deduct_to_merge_parallel [] = undefined"
  | "ill_deduct_to_merge_parallel (x#xs) =
      (case x of
        Parallel as \<Rightarrow> ill_deduct_simple_cut
          (ill_deduct_compact_cons_to_times
            (compact (map res_term_to_ill as))
            (map res_term_to_ill xs))
          (ill_deduct_times_to_compact_append (map res_term_to_ill as) (map res_term_to_ill xs))
      | _ \<Rightarrow> ill_deduct_simple_cut
          (ill_deduct_compact_cons_to_times (res_term_to_ill x) (map res_term_to_ill xs))
          (ill_deduct_simple_cut
            (ill_deduct_tensor
              (Identity (res_term_to_ill x))
              (ill_deduct_to_merge_parallel xs))
            (ill_deduct_times_to_compact_cons
              (res_term_to_ill x)
              (map res_term_to_ill (merge_one_parallel xs)))))"

lemma ill_deduct_to_merge_parallel [simp]:
  assumes "list_ex is_Parallel xs"
    shows
    " ill_conclusion (ill_deduct_to_merge_parallel xs)
    = Sequent [res_term_to_ill (Parallel xs)] (res_term_to_ill (Parallel (merge_one_parallel xs)))"
    and "ill_deduct_premises (ill_deduct_to_merge_parallel xs) = []"
    and "ill_deduct_wf (ill_deduct_to_merge_parallel xs)"
proof -
  have [simp]:
    " ill_conclusion (ill_deduct_to_merge_parallel xs)
    = Sequent [res_term_to_ill (Parallel xs)] (res_term_to_ill (Parallel (merge_one_parallel xs)))"
    if "list_ex is_Parallel xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
  then show
    " ill_conclusion (ill_deduct_to_merge_parallel xs)
    = Sequent [res_term_to_ill (Parallel xs)] (res_term_to_ill (Parallel (merge_one_parallel xs)))"
    using assms .

  have "ill_deduct_premises (ill_deduct_to_merge_parallel xs) = []"
    if "list_ex is_Parallel xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) simp_all
  qed
  then show "ill_deduct_premises (ill_deduct_to_merge_parallel xs) = []"
    using assms .

  show "ill_deduct_wf (ill_deduct_to_merge_parallel xs)"
    using assms
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
qed

fun ill_deduct_from_merge_parallel :: "('a, 'b) res_term list \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "[res_term_to_ill (Parallel (merge_one_parallel xs))] \<turnstile> res_term_to_ill (Parallel xs)"}\<close>
  where
    "ill_deduct_from_merge_parallel [] = undefined"
  | "ill_deduct_from_merge_parallel (x#xs) =
      (case x of
        Parallel as \<Rightarrow> ill_deduct_simple_cut
          (ill_deduct_compact_append_to_times (map res_term_to_ill as) (map res_term_to_ill xs))
          (ill_deduct_times_to_compact_cons
            (compact (map res_term_to_ill as))
            (map res_term_to_ill xs))
      | _ \<Rightarrow> ill_deduct_simple_cut
        (ill_deduct_compact_cons_to_times
          (res_term_to_ill x)
          (map res_term_to_ill (merge_one_parallel xs)))
        (ill_deduct_simple_cut
          (ill_deduct_tensor
            (Identity (res_term_to_ill x))
            (ill_deduct_from_merge_parallel xs))
          (ill_deduct_times_to_compact_cons (res_term_to_ill x) (map res_term_to_ill xs))))"

lemma ill_deduct_from_merge_parallel [simp]:
  assumes "list_ex is_Parallel xs"
    shows
    " ill_conclusion (ill_deduct_from_merge_parallel xs)
    = Sequent [res_term_to_ill (Parallel (merge_one_parallel xs))] (res_term_to_ill (Parallel xs))"
    and "ill_deduct_premises (ill_deduct_from_merge_parallel xs) = []"
    and "ill_deduct_wf (ill_deduct_from_merge_parallel xs)"
proof -
  have [simp]:
    " ill_conclusion (ill_deduct_from_merge_parallel xs)
    = Sequent [res_term_to_ill (Parallel (merge_one_parallel xs))] (res_term_to_ill (Parallel xs))"
    if "list_ex is_Parallel xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
  then show
    " ill_conclusion (ill_deduct_from_merge_parallel xs)
    = Sequent [res_term_to_ill (Parallel (merge_one_parallel xs))] (res_term_to_ill (Parallel xs))"
    using assms .

  have "ill_deduct_premises (ill_deduct_from_merge_parallel xs) = []"
    if "list_ex is_Parallel xs" for xs :: "('a, 'b) res_term list"
    using that
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) simp_all
  qed
  then show "ill_deduct_premises (ill_deduct_from_merge_parallel xs) = []"
    using assms .

  show "ill_deduct_wf (ill_deduct_from_merge_parallel xs)"
    using assms
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases a) (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)
  qed
qed

text\<open>
  To construct the deeply embedded deductions witnessing equivalence of representations for
  @{const step} we need to define both directions at the same time using mutual recursion.
  This is because of @{const Executable} and @{const Repeatable} terms and the way that the left-
  and right-hand sides of linear implication are differently treated by the @{text limpL} rule:
  @{thm limpL}
\<close>
fun ill_deduct_res_term_to_step :: "('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "[res_term_to_ill a] \<turnstile> res_term_to_ill (step a)"}\<close>
and ill_deduct_res_term_from_step :: "('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "[res_term_to_ill (step a)] \<turnstile> res_term_to_ill a"}\<close>
  where
    "ill_deduct_res_term_to_step Empty = Identity (\<one>)"
  | "ill_deduct_res_term_to_step Anything = Identity (\<top>)"
  | "ill_deduct_res_term_to_step (Res x) = Identity (Prop (Inl x))"
  | "ill_deduct_res_term_to_step (Copyable x) = Identity (!(Prop (Inr x)))"
  | "ill_deduct_res_term_to_step (NonD x y) =
      (if \<not> normalised x
        then ill_deduct_simple_plusL
              ( ill_deduct_simple_cut
                ( ill_deduct_res_term_to_step x)
                ( ill_deduct_plusR1 (res_term_to_ill (step x)) (res_term_to_ill y)))
              ( ill_deduct_plusR2 (res_term_to_ill (step x)) (res_term_to_ill y))
        else if \<not> normalised y
        then ill_deduct_simple_plusL
              ( ill_deduct_plusR1 (res_term_to_ill x) (res_term_to_ill (step y)))
              ( ill_deduct_simple_cut
                ( ill_deduct_res_term_to_step y)
                ( ill_deduct_plusR2 (res_term_to_ill x) (res_term_to_ill (step y))))
        else Identity (res_term_to_ill (NonD x y)))"
  | "ill_deduct_res_term_to_step (Executable x y) =
      (if \<not> normalised x
        then LimpR [] (res_term_to_ill (step x)) [res_term_to_ill x \<rhd> res_term_to_ill y]
                   (res_term_to_ill y)
              ( LimpL [res_term_to_ill (step x)] (res_term_to_ill x) [] (res_term_to_ill y) []
                      (res_term_to_ill y)
                ( ill_deduct_res_term_from_step x)
                ( Identity (res_term_to_ill y)))
        else if \<not> normalised y
        then LimpR [] (res_term_to_ill x) [res_term_to_ill x \<rhd> res_term_to_ill y]
                   (res_term_to_ill (step y))
              ( LimpL [res_term_to_ill x] (res_term_to_ill x) [] (res_term_to_ill y) []
                      (res_term_to_ill (step y))
                ( Identity (res_term_to_ill x))
                ( ill_deduct_res_term_to_step y))
        else Identity (res_term_to_ill (Executable x y)))"
  | "ill_deduct_res_term_to_step (Repeatable x y) =
      (if \<not> normalised x
        then ill_deduct_exp
              ( LimpR [] (res_term_to_ill (step x)) [res_term_to_ill x \<rhd> res_term_to_ill y]
                      (res_term_to_ill y)
                ( LimpL [res_term_to_ill (step x)] (res_term_to_ill x) [] (res_term_to_ill y) []
                        (res_term_to_ill y)
                  ( ill_deduct_res_term_from_step x)
                  ( Identity (res_term_to_ill y))))
        else if \<not> normalised y
        then ill_deduct_exp
              ( LimpR [] (res_term_to_ill x) [res_term_to_ill x \<rhd> res_term_to_ill y]
                      (res_term_to_ill (step y))
                ( LimpL [res_term_to_ill x] (res_term_to_ill x) [] (res_term_to_ill y) []
                        (res_term_to_ill (step y))
                  ( Identity (res_term_to_ill x))
                  ( ill_deduct_res_term_to_step y)))
        else Identity (res_term_to_ill (Repeatable x y)))"
  | "ill_deduct_res_term_to_step (Parallel xs) =
      ( if list_ex (\<lambda>x. \<not> normalised x) xs
          then ill_deduct_tensor_list (map ill_deduct_res_term_to_step xs)
        else if list_ex is_Parallel xs then ill_deduct_to_merge_parallel xs
        else if list_ex is_Empty xs then ill_deduct_to_remove_empty xs
        else (case xs of
                [] \<Rightarrow> Identity (\<one>)
              | [a] \<Rightarrow> Identity (res_term_to_ill a)
              | _ \<Rightarrow> Identity (res_term_to_ill (Parallel xs))))"
  | "ill_deduct_res_term_from_step Empty = Identity (\<one>)"
  | "ill_deduct_res_term_from_step Anything = Identity (\<top>)"
  | "ill_deduct_res_term_from_step (Res x) = Identity (Prop (Inl x))"
  | "ill_deduct_res_term_from_step (Copyable x) = Identity (!(Prop (Inr x)))"
  | "ill_deduct_res_term_from_step (NonD x y) =
      (if \<not> normalised x
        then ill_deduct_simple_plusL
              ( ill_deduct_simple_cut
                ( ill_deduct_res_term_from_step x)
                ( ill_deduct_plusR1 (res_term_to_ill x) (res_term_to_ill y)))
              ( ill_deduct_plusR2 (res_term_to_ill x) (res_term_to_ill y))
        else if \<not> normalised y
        then ill_deduct_simple_plusL
              ( ill_deduct_plusR1 (res_term_to_ill x) (res_term_to_ill y))
              ( ill_deduct_simple_cut
                ( ill_deduct_res_term_from_step y)
                ( ill_deduct_plusR2 (res_term_to_ill x) (res_term_to_ill y)))
        else Identity (res_term_to_ill (NonD x y)))"
  | "ill_deduct_res_term_from_step (Executable x y) =
      (if \<not> normalised x
        then LimpR [] (res_term_to_ill x) [res_term_to_ill (step x) \<rhd> res_term_to_ill y]
                   (res_term_to_ill y)
              ( LimpL [res_term_to_ill x] (res_term_to_ill (step x)) [] (res_term_to_ill y) []
                      (res_term_to_ill y)
                ( ill_deduct_res_term_to_step x)
                ( Identity (res_term_to_ill y)))
        else if \<not> normalised y
        then LimpR [] (res_term_to_ill x) [res_term_to_ill x \<rhd> res_term_to_ill (step y)]
                   (res_term_to_ill y)
              ( LimpL [res_term_to_ill x] (res_term_to_ill x) [] (res_term_to_ill (step y)) []
                      (res_term_to_ill y)
                ( Identity (res_term_to_ill x))
                ( ill_deduct_res_term_from_step y))
        else Identity (res_term_to_ill (Executable x y)))"
  | "ill_deduct_res_term_from_step (Repeatable x y) =
      (if \<not> normalised x
        then ill_deduct_exp
              ( LimpR [] (res_term_to_ill x) [res_term_to_ill (step x) \<rhd> res_term_to_ill y]
                      (res_term_to_ill y)
                ( LimpL [res_term_to_ill x] (res_term_to_ill (step x)) [] (res_term_to_ill y) []
                        (res_term_to_ill y)
                  ( ill_deduct_res_term_to_step x)
                  ( Identity (res_term_to_ill y))))
        else if \<not> normalised y
        then ill_deduct_exp
              ( LimpR [] (res_term_to_ill x) [res_term_to_ill x \<rhd> res_term_to_ill (step y)]
                      (res_term_to_ill y)
                ( LimpL [res_term_to_ill x] (res_term_to_ill x) [] (res_term_to_ill (step y)) []
                        (res_term_to_ill y)
                  ( Identity (res_term_to_ill x))
                  ( ill_deduct_res_term_from_step y)))
        else Identity (res_term_to_ill (Repeatable x y)))"
  | "ill_deduct_res_term_from_step (Parallel xs) =
      ( if list_ex (\<lambda>x. \<not> normalised x) xs
          then ill_deduct_tensor_list (map ill_deduct_res_term_from_step xs)
        else if list_ex is_Parallel xs then ill_deduct_from_merge_parallel xs
        else if list_ex is_Empty xs then ill_deduct_from_remove_empty xs
        else (case xs of
                [] \<Rightarrow> Identity (\<one>)
              | [a] \<Rightarrow> Identity (res_term_to_ill a)
              | _ \<Rightarrow> Identity (res_term_to_ill (Parallel xs))))"

text\<open>
  Note that in verifying these functions we need to explicitly annotate the resulting deduction's
  type to fix the second type variable (premise labels).
  Otherwise type inference will assume they are distinct, breaking the mutually inductive proof.
\<close>
lemma ill_deduct_res_term_to_step_conc [simp]:
        " ill_conclusion (ill_deduct_res_term_to_step a :: ('a + 'b, 'l) ill_deduct)
        = Sequent [res_term_to_ill a] (res_term_to_ill (step a))"
  and ill_deduct_res_term_from_step_conc [simp]:
        " ill_conclusion (ill_deduct_res_term_from_step a :: ('a + 'b, 'l) ill_deduct)
        = Sequent [res_term_to_ill (step a)] (res_term_to_ill a)"
proof -
  let ?proof_to = "ill_deduct_res_term_to_step :: ('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  and ?proof_from = "ill_deduct_res_term_from_step :: ('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"

  have "ill_conclusion (?proof_to a) = Sequent [res_term_to_ill a] (res_term_to_ill (step a)) \<and>
        ill_conclusion (?proof_from a) = Sequent [res_term_to_ill (step a)] (res_term_to_ill a)"
  proof (induct a rule: step_induct')
       case Empty then show ?case by simp
  next case Anything then show ?case by simp
  next case (Res a) then show ?case by simp
  next case (Copyable x) then show ?case by simp
  next case (NonD_L x y) then show ?case by (simp add: ill_conclusion_antecedents)
  next case (NonD_R x y) then show ?case by (simp add: ill_conclusion_antecedents)
  next case (NonD x y) then show ?case by simp
  next case (Executable_L x y) then show ?case by simp
  next case (Executable_R x y) then show ?case by simp
  next case (Executable x y) then show ?case by simp
  next case (Repeatable_L x y) then show ?case by simp
  next case (Repeatable_R x y) then show ?case by simp
  next case (Repeatable x y) then show ?case by simp
  next
    case (Par_Norm xs)
    moreover have "\<exists>a. antecedents x = [a]"
      if "x \<in> set (map ill_deduct_res_term_to_step xs)" for x :: "('a + 'b, 'l) ill_deduct"
      using that Par_Norm by fastforce
    moreover have "\<exists>a. antecedents x = [a]"
      if "x \<in> set (map ill_deduct_res_term_from_step xs)" for x :: "('a + 'b, 'l) ill_deduct"
      using that Par_Norm by fastforce
    ultimately show ?case
      apply (simp add: Bex_set[symmetric] Bex_def comp_def)
      apply (subst (1 2) ill_deduct_tensor_list(1))
      apply (simp_all add: comp_def ill_conclusion_alt)
      by (metis (mono_tags, lifting) list.sel(1) map_eq_conv)
  next
  next case (Par_Par xs) then show ?case by (simp add: Bex_set[symmetric])
  next case (Par_Empty xs) then show ?case by (simp add: Bex_set[symmetric] not_list_ex[symmetric])
  next case Par_Nil then show ?case by simp
  next case (Par_Single u) then show ?case by simp
  next
    case (Par v vb vc)
    then have "Parallel (v # vb # vc) = step (Parallel (v # vb # vc))"
      by simp
    moreover have
      " ill_deduct_res_term_to_step (Parallel (v # vb # vc))
      = Identity (res_term_to_ill (Parallel (v # vb # vc)))"
      using Par by (simp add: Bex_set[symmetric] not_list_ex[symmetric])
    moreover have
      " ill_deduct_res_term_from_step (Parallel (v # vb # vc))
      = Identity (res_term_to_ill (Parallel (v # vb # vc)))"
      using Par by (simp add: Bex_set[symmetric] not_list_ex[symmetric])
    ultimately show ?case
      by (metis ill_conclusion.simps(2))
  qed
  then show "ill_conclusion (?proof_to a) = Sequent [res_term_to_ill a] (res_term_to_ill (step a))"
       and "ill_conclusion (?proof_from a) = Sequent [res_term_to_ill (step a)] (res_term_to_ill a)"
    by simp_all
qed

text\<open>Verify there are no premises:\<close>
lemma ill_deduct_res_term_to_step_prem [simp]:
      "ill_deduct_premises (ill_deduct_res_term_to_step a :: ('a + 'b, 'l) ill_deduct) = []"
  and ill_deduct_res_term_from_step_prem [simp]:
      "ill_deduct_premises (ill_deduct_res_term_from_step a :: ('a + 'b, 'l) ill_deduct) = []"
proof -
  let ?proof_to = "ill_deduct_res_term_to_step :: ('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  and ?proof_from = "ill_deduct_res_term_from_step :: ('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"

  have "ill_deduct_premises (?proof_to a) = [] \<and>
        ill_deduct_premises (?proof_from a) = []"
  proof (induct a rule: step_induct')
       case Empty then show ?case by simp
  next case Anything then show ?case by simp
  next case (Res a) then show ?case by simp
  next case (Copyable x) then show ?case by simp
  next case (NonD_L x y) then show ?case by simp
  next case (NonD_R x y) then show ?case by simp
  next case (NonD x y) then show ?case by simp
  next case (Executable_L x y) then show ?case by simp
  next case (Executable_R x y) then show ?case by simp
  next case (Executable x y) then show ?case by simp
  next case (Repeatable_L x y) then show ?case by simp
  next case (Repeatable_R x y) then show ?case by simp
  next case (Repeatable x y) then show ?case by simp
  next
    case (Par_Norm xs)
    moreover have "\<exists>a. antecedents x = [a]" and "ill_deduct_premises x = []"
      if "x \<in> set (map ill_deduct_res_term_to_step xs)" for x :: "('a + 'b, 'l) ill_deduct"
    proof -
      show "\<exists>a. antecedents x = [a]"
        using that by (metis ex_map_conv ill_conclusionE ill_deduct_res_term_to_step_conc)
      show "ill_deduct_premises x = []"
        using Par_Norm that by fastforce
    qed
    then have "ill_deduct_premises (ill_deduct_tensor_list (map ?proof_to xs)) = []"
      by (subst ill_deduct_tensor_list(3)) simp_all
    moreover have "\<exists>a. antecedents x = [a]" and "ill_deduct_premises x = []"
      if "x \<in> set (map ill_deduct_res_term_from_step xs)" for x :: "('a + 'b, 'l) ill_deduct"
    proof -
      show "\<exists>a. antecedents x = [a]"
        using that by (metis ex_map_conv ill_conclusionE ill_deduct_res_term_from_step_conc)
      show "ill_deduct_premises x = []"
        using Par_Norm that by fastforce
    qed
    then have "ill_deduct_premises (ill_deduct_tensor_list (map ?proof_from xs)) = []"
      by (subst ill_deduct_tensor_list(3)) simp_all
    ultimately show ?case
      by (simp add: Bex_set[symmetric] Bex_def)
  next case (Par_Par xs) then show ?case by (simp add: Bex_set[symmetric])
  next case (Par_Empty xs) then show ?case by (simp add: Bex_set[symmetric])
  next case Par_Nil then show ?case by simp
  next case (Par_Single u) then show ?case by simp
  next
    case (Par v vb vc)
    have
      " ill_deduct_res_term_to_step (Parallel (v # vb # vc))
      = Identity (res_term_to_ill (Parallel (v # vb # vc)))"
      using Par by (simp add: Bex_set[symmetric] not_list_ex[symmetric])
    moreover have
      " ill_deduct_res_term_from_step (Parallel (v # vb # vc))
      = Identity (res_term_to_ill (Parallel (v # vb # vc)))"
      using Par by (simp add: Bex_set[symmetric] not_list_ex[symmetric])
    ultimately show ?case
      by (metis ill_deduct_premises.simps(2))
  qed
  then show "ill_deduct_premises (?proof_to a) = []"
        and "ill_deduct_premises (?proof_from a) = []"
    by simp_all
qed

text\<open>Verify well-formedness:\<close>
lemma ill_deduct_res_term_to_step_wf [simp]:
        "ill_deduct_wf (ill_deduct_res_term_to_step a :: ('a + 'b, 'l) ill_deduct)"
  and ill_deduct_res_term_from_step_wf [simp]:
        "ill_deduct_wf (ill_deduct_res_term_from_step a :: ('a + 'b, 'l) ill_deduct)"
proof -
  let ?proof_to = "ill_deduct_res_term_to_step :: ('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  and ?proof_from = "ill_deduct_res_term_from_step :: ('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"

  have "ill_deduct_wf (?proof_to a) \<and>
        ill_deduct_wf (?proof_from a)"
  proof (induct a rule: step_induct')
       case Empty then show ?case by simp
  next case Anything then show ?case by simp
  next case (Res a) then show ?case by simp
  next case (Copyable x) then show ?case by simp
  next
    case (NonD_L x y)
    then show ?case
      by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
  next
    case (NonD_R x y)
    then show ?case
      by (simp add: ill_conclusion_antecedents ill_conclusion_consequent)
  next case (NonD x y) then show ?case by simp
  next case (Executable_L x y) then show ?case by simp
  next case (Executable_R x y) then show ?case by simp
  next case (Executable x y) then show ?case by simp
  next case (Repeatable_L x y) then show ?case by simp
  next case (Repeatable_R x y) then show ?case by simp
  next case (Repeatable x y) then show ?case by simp
  next
    case (Par_Norm xs)
    moreover have "\<exists>a. antecedents x = [a]" and "ill_deduct_wf x"
      if "x \<in> set (map ill_deduct_res_term_to_step xs)" for x :: "('a + 'b, 'l) ill_deduct"
    proof -
      show "\<exists>a. antecedents x = [a]"
        using that by (metis ex_map_conv ill_conclusionE ill_deduct_res_term_to_step_conc)
      show "ill_deduct_wf x"
        using Par_Norm that by fastforce
    qed
    then have "ill_deduct_wf (ill_deduct_tensor_list (map ?proof_to xs))"
      by (intro ill_deduct_tensor_list(2)) simp_all
    moreover have "\<exists>a. antecedents x = [a]" and "ill_deduct_wf x"
      if "x \<in> set (map ill_deduct_res_term_from_step xs)" for x :: "('a + 'b, 'l) ill_deduct"
    proof -
      show "\<exists>a. antecedents x = [a]"
        using that by (metis ex_map_conv ill_conclusionE ill_deduct_res_term_from_step_conc)
      show "ill_deduct_wf x"
        using Par_Norm that by fastforce
    qed
    then have "ill_deduct_wf (ill_deduct_tensor_list (map ?proof_from xs))"
      by (intro ill_deduct_tensor_list(2)) simp_all
    ultimately show ?case
      by (simp add: Bex_set[symmetric] Bex_def)
  next case (Par_Par xs) then show ?case by (simp add: Bex_set[symmetric])
  next case (Par_Empty xs) then show ?case by (simp add: Bex_set[symmetric])
  next case Par_Nil then show ?case by simp
  next case (Par_Single u) then show ?case by simp
  next
    case (Par v vb vc)
    have
      " ill_deduct_res_term_to_step (Parallel (v # vb # vc))
      = Identity (res_term_to_ill (Parallel (v # vb # vc)))"
      using Par by (simp add: Bex_set[symmetric] not_list_ex[symmetric])
    moreover have
      " ill_deduct_res_term_from_step (Parallel (v # vb # vc))
      = Identity (res_term_to_ill (Parallel (v # vb # vc)))"
      using Par by (simp add: Bex_set[symmetric] not_list_ex[symmetric])
    ultimately show ?case
      by (metis ill_deduct_wf.simps(2))
  qed
  then show "ill_deduct_wf (?proof_to a)"
        and "ill_deduct_wf (?proof_from a)"
    by simp_all
qed

subsection\<open>Relating to Rewriting Normalisation\<close>

text\<open>
  To extend the deduction from the rewriting step to the full normalisation procedure, we only need
  to appropriately repeat it.
  In the shallow embedding this is done simply by induction.
  In the deep embedding we construct the deduction by recursively applying the deduction for
  @{const step} (in the relevant direction) connected with the simplified cut rule.

  As with @{const normal_rewr}, we remove the function definitions from the simplifier to prevent
  looping.
  The termination proofs once again use the rewriting bound @{const res_term_rewrite_bound}.
\<close>
lemma normal_rewr_ill_eq:
  "res_term_to_ill a \<stileturn>\<turnstile> res_term_to_ill (normal_rewr a)"
proof (induct a rule: normal_rewr.induct)
  case (1 x)
  then show ?case
  proof (cases "normalised x")
    case True then show ?thesis by (simp add: normal_rewr.simps)
  next
    case False

    have "res_term_to_ill x \<stileturn>\<turnstile> res_term_to_ill (step x)"
      by (rule step_ill_eq)
    also have "... \<stileturn>\<turnstile> res_term_to_ill (normal_rewr (step x))"
      using 1 False by simp
    also have "... \<stileturn>\<turnstile> res_term_to_ill (normal_rewr x)"
      using False by (simp add: normal_rewr.simps)
    finally show ?thesis .
  qed
qed

function ill_deduct_res_term_to_normal_rewr :: "('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "\<And>a. [res_term_to_ill a] \<turnstile> res_term_to_ill (normal_rewr a)"}\<close>
  where "ill_deduct_res_term_to_normal_rewr x =
    (if normalised x
      then Identity (res_term_to_ill x)
      else ill_deduct_simple_cut
        ( ill_deduct_res_term_to_step x)
        ( ill_deduct_res_term_to_normal_rewr (step x)))"
  by pat_completeness auto
termination ill_deduct_res_term_to_normal_rewr
  using res_term_rewrite_bound_step_decrease
  by (relation "Wellfounded.measure res_term_rewrite_bound", auto)
lemmas [simp del] = ill_deduct_res_term_to_normal_rewr.simps

lemma ill_deduct_res_term_to_normal_rewr [simp]:
  " ill_conclusion (ill_deduct_res_term_to_normal_rewr a :: ('a + 'b, 'l) ill_deduct)
  = Sequent [res_term_to_ill a] (res_term_to_ill (normal_rewr a))"
  "ill_deduct_premises (ill_deduct_res_term_to_normal_rewr a :: ('a + 'b, 'l) ill_deduct) = []"
  "ill_deduct_wf (ill_deduct_res_term_to_normal_rewr a :: ('a + 'b, 'l) ill_deduct)"
proof (induct a rule: normal_rewr.induct)
  case (1 x)
  let ?proof = "ill_deduct_res_term_to_normal_rewr x :: ('a + 'b, 'l) ill_deduct"

  show "ill_conclusion ?proof = Sequent [res_term_to_ill x] (res_term_to_ill (normal_rewr x))"
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: ill_deduct_res_term_to_normal_rewr.simps normal_rewr.simps)
  next
    case False
    then show ?thesis
      using "1.hyps"(1) normal_rewr_step ill_deduct_res_term_to_normal_rewr.simps
      by (metis ill_conclusionE ill_deduct_res_term_to_step_conc ill_deduct_simple_cut(2))
  qed
  show "ill_deduct_premises ?proof = []"
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: ill_deduct_res_term_to_normal_rewr.simps)
  next
    case False
    then show ?thesis
      using "1.hyps"(2) ill_deduct_res_term_to_normal_rewr.simps
      by (metis append_Nil ill_deduct_res_term_to_step_prem ill_deduct_simple_cut(3))
  qed
  show "ill_deduct_wf ?proof"
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: ill_deduct_res_term_to_normal_rewr.simps)
  next
    case False
    then show ?thesis
      using "1.hyps"(1,3) ill_deduct_res_term_to_normal_rewr.simps ill_deduct_simple_cut(1)
      by (metis ill_conclusion_alt ill_deduct_res_term_to_step_conc ill_deduct_res_term_to_step_wf)
  qed
qed


function ill_deduct_res_term_from_normal_rewr :: "('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  \<comment> \<open>@{prop "\<And>a. [res_term_to_ill (normal_rewr a)] \<turnstile> res_term_to_ill a"}\<close>
  where "ill_deduct_res_term_from_normal_rewr x =
    (if normalised x
      then Identity (res_term_to_ill x)
      else ill_deduct_simple_cut
        ( ill_deduct_res_term_from_normal_rewr (step x))
        ( ill_deduct_res_term_from_step x))"
  by pat_completeness auto
termination ill_deduct_res_term_from_normal_rewr
  using res_term_rewrite_bound_step_decrease
  by (relation "Wellfounded.measure res_term_rewrite_bound", auto)
lemmas [simp del] = ill_deduct_res_term_from_normal_rewr.simps

lemma ill_deduct_res_term_from_normal_rewr [simp]:
  " ill_conclusion (ill_deduct_res_term_from_normal_rewr a :: ('a + 'b, 'l) ill_deduct)
  = Sequent [res_term_to_ill (normal_rewr a)] (res_term_to_ill a)"
  " ill_deduct_premises (ill_deduct_res_term_from_normal_rewr a :: ('a + 'b, 'l) ill_deduct)
  = []"
  "ill_deduct_wf (ill_deduct_res_term_from_normal_rewr a :: ('a + 'b, 'l) ill_deduct)"
proof (induct a rule: normal_rewr.induct)
  case (1 x)
  let ?proof = "ill_deduct_res_term_from_normal_rewr x :: ('a + 'b, 'l) ill_deduct"

  show "ill_conclusion ?proof = Sequent [res_term_to_ill (normal_rewr x)] (res_term_to_ill x)"
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: ill_deduct_res_term_from_normal_rewr.simps normal_rewr.simps)
  next
    case False
    then show ?thesis
      using "1.hyps"(1) normal_rewr_step ill_deduct_res_term_from_normal_rewr.simps
      by (metis ill_conclusionE ill_deduct_res_term_from_step_conc ill_deduct_simple_cut(2))
  qed
  show "ill_deduct_premises ?proof = []"
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: ill_deduct_res_term_from_normal_rewr.simps)
  next
    case False
    then show ?thesis
      using "1.hyps"(2) ill_deduct_res_term_from_normal_rewr.simps
      by (metis append_Nil ill_deduct_res_term_from_step_prem ill_deduct_simple_cut(3))
  qed
  then show "ill_deduct_wf ?proof"
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: ill_deduct_res_term_from_normal_rewr.simps)
  next
    case False
    then show ?thesis
      using "1.hyps"(1,3) ill_deduct_res_term_from_normal_rewr.simps ill_deduct_simple_cut(1)
      by (metis ill_conclusion_alt ill_deduct_res_term_from_step_conc
                ill_deduct_res_term_from_step_wf)
  qed
qed

text\<open>
  Finally, we can connect the two proof directions to move between ILL representations of any two
  equivalent resource terms by stepping through their shared normal form
\<close>
fun ill_deduct_res_term_ill_eq
    :: "('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term \<Rightarrow> ('a + 'b, 'l) ill_deduct"
  where "ill_deduct_res_term_ill_eq a b =
    ill_deduct_simple_cut
      (ill_deduct_res_term_to_normal_rewr a)
      (ill_deduct_res_term_from_normal_rewr b)"

lemma ill_deduct_res_term_ill_eq [simp]:
  " ill_conclusion (ill_deduct_res_term_ill_eq a b)
  = Sequent [res_term_to_ill a] (res_term_to_ill b)"
  "normal_rewr a = normal_rewr b \<Longrightarrow> ill_deduct_wf (ill_deduct_res_term_ill_eq a b)"
  "ill_deduct_premises (ill_deduct_res_term_ill_eq a b) = []"
  by (simp_all add: ill_conclusion_antecedents ill_conclusion_consequent)

end