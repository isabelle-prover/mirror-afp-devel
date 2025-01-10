theory CopyableElimination
  imports Process
begin

section\<open>Copyable Resource Elimination\<close>

text\<open>
  We can show that copyable resources are not strictly necessary for the theory, being instead a
  convenience feature, by taking any valid process and transforming it into one that does not use
  any copyable resources.
  The cost is that we introduce new primitive actions, which represent the explicit assumptions that
  the resources that were copyable have actions that correspond to @{const Duplicate} and
  @{const Erase} in the domain.
  While an equivalent assumption (that such actions exist in the domain) is made by making an atom
  copyable instead of linear, that avenue fixes the form of those actions and as such lessens the
  risk of error in manually introducing them for this frequent pattern.

  The concrete transformation takes a process of type @{typ "('a, 'b, 'l, 'm) process"} to one of
  type @{typ "('a + 'b, 'c, 'l + String.literal, 'm + unit) process"}.
  Note the following:
  \<^item> The two resource atom types are combined into one to form the new linear atoms.
  \<^item> The new copyable atoms can be of any type, because the result makes no use of them.
  \<^item> The old labels are combined with string literals to add label simple labels for the new actions.
  \<^item> The old metadata is combined with @{type unit}, allowing the new actions to have no metadata.
\<close>

subsection\<open>Replacing Copyable Resource Actions\<close>

text\<open>
  To remove the copyable resource actions @{const Duplicate} and @{const Erase} we replace them with
  @{const Primitive} actions with the corresponding input and output, string labels and no metadata.
\<close>
primrec makeDuplEraToPrim
  :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l + String.literal, 'm + unit) process"
  where
    "makeDuplEraToPrim (Primitive a b l m) = Primitive a b (Inl l) (Inl m)"
  | "makeDuplEraToPrim (Identity a) = Identity a"
  | "makeDuplEraToPrim (Swap a b) = Swap a b"
  | "makeDuplEraToPrim (Seq p q) = Seq (makeDuplEraToPrim p) (makeDuplEraToPrim q)"
  | "makeDuplEraToPrim (Par p q) = Par (makeDuplEraToPrim p) (makeDuplEraToPrim q)"
  | "makeDuplEraToPrim (Opt p q) = Opt (makeDuplEraToPrim p) (makeDuplEraToPrim q)"
  | "makeDuplEraToPrim (InjectL a b) = InjectL a b"
  | "makeDuplEraToPrim (InjectR a b) = InjectR a b"
  | "makeDuplEraToPrim (OptDistrIn a b c) = OptDistrIn a b c"
  | "makeDuplEraToPrim (OptDistrOut a b c) = OptDistrOut a b c"
  | "makeDuplEraToPrim (Duplicate a) =
      Primitive (Copyable a) (Copyable a \<odot> Copyable a) (Inr STR ''Duplicate'') (Inr ())"
  | "makeDuplEraToPrim (Erase a) =
      Primitive (Copyable a) Empty (Inr STR ''Erase'') (Inr ())"
  | "makeDuplEraToPrim (Represent p) = Represent (makeDuplEraToPrim p)"
  | "makeDuplEraToPrim (Apply a b) = Apply a b"
  | "makeDuplEraToPrim (Repeat a b) = Repeat a b"
  | "makeDuplEraToPrim (Close a b) = Close a b"
  | "makeDuplEraToPrim (Once a b) = Once a b"
  | "makeDuplEraToPrim (Forget a) = Forget a"

subsection\<open>Making Copyable Resource Terms Linear\<close>

text\<open>
  To eventually replace copyable resources, we first define how resource terms are replaced.
  Linear atoms are injected into the left side of the sum while copyable ones are injected into the
  right side, but both are turned into linear atoms in the result.
\<close>
primrec copyableToRes_term :: "('a, 'b) res_term \<Rightarrow> ('a + 'b, 'c) res_term"
  where
    "copyableToRes_term res_term.Empty = res_term.Empty"
  | "copyableToRes_term res_term.Anything = res_term.Anything"
  | "copyableToRes_term (res_term.Res a) = res_term.Res (Inl a)"
  | "copyableToRes_term (res_term.Copyable a) = res_term.Res (Inr a)"
  | "copyableToRes_term (res_term.Parallel xs) =
      res_term.Parallel (map copyableToRes_term xs)"
  | "copyableToRes_term (res_term.NonD a b) =
      res_term.NonD (copyableToRes_term a) (copyableToRes_term b)"
  | "copyableToRes_term (res_term.Executable a b) =
      res_term.Executable (copyableToRes_term a) (copyableToRes_term b)"
  | "copyableToRes_term (res_term.Repeatable a b) =
      res_term.Repeatable (copyableToRes_term a) (copyableToRes_term b)"

text\<open>Replacing copyable resource terms preserves term equivalence\<close>
lemma copyableToRes_term_equiv:
  "x \<sim> y \<Longrightarrow> copyableToRes_term x \<sim> copyableToRes_term y"
proof (induct x y rule: res_term_equiv.induct)
     case nil then show ?case by simp
next case (singleton a) then show ?case by simp
next
  case (merge x y z)
  then show ?case
    using res_term_equiv.merge by force
next case empty then show ?case by simp
next case anything then show ?case by simp
next case (res x) then show ?case by simp
next case (copyable x) then show ?case by simp
next
  case (parallel xs ys)
  then show ?case
    by (simp add: list.rel_map list_all2_mono res_term_equiv.parallel)
next case (nondet x y u v) then show ?case by (simp add: res_term_equiv.nondet)
next case (executable x y u v) then show ?case by (simp add: res_term_equiv.executable)
next case (repeatable x y u v) then show ?case by (simp add: res_term_equiv.repeatable)
next case (sym x y) then show ?case by (metis res_term_equiv.sym)
next case (trans x y z) then show ?case by (metis res_term_equiv.trans)
qed

text\<open>Replacing copyable resource terms does not affect the nature of non-atoms\<close>
lemma copyableToRes_term_is_Empty [simp]:
  "is_Empty (copyableToRes_term x) = is_Empty x"
  by (cases x) simp_all
lemma copyableToRes_term_has_Empty [simp]:
  "list_ex is_Empty (map copyableToRes_term xs) = list_ex is_Empty xs"
  by (induct xs) simp_all
lemma copyableToRes_term_has_no_Empty [simp]:
  "list_all (\<lambda>x. \<not> is_Empty x) (map copyableToRes_term xs) = list_all (\<lambda>x. \<not> is_Empty x) xs"
  by (induct xs) simp_all
lemma copyableToRes_term_is_Parallel [simp]:
  "is_Parallel (copyableToRes_term x) = is_Parallel x"
  by (cases x) simp_all
lemma copyableToRes_term_has_Parallel [simp]:
  "list_ex is_Parallel (map copyableToRes_term xs) = list_ex is_Parallel xs"
  by (induct xs) simp_all
lemma copyableToRes_term_has_no_Parallel [simp]:
  "list_all (\<lambda>x. \<not> is_Parallel x) (map copyableToRes_term xs) = list_all (\<lambda>x. \<not> is_Parallel x) xs"
  by (induct xs) simp_all

text\<open>Replacing copyable resource terms does not affect whether they are normalised\<close>
lemma normalised_copyableToRes_term [simp]:
  "normalised (copyableToRes_term x) = normalised x" (is "normalised (?f x) = normalised x")
  \<comment> \<open>Note the pattern matching, which is needed to later refer to @{const copyableToRes_term} with
      the right type variable for copyable resources in its output\<close>
proof (induct x)
     case (Res x) then show ?case by simp
next case (Copyable x) then show ?case by simp
next case Empty then show ?case by simp
next case Anything then show ?case by simp
next
  case (Parallel xs)
  then show ?case
  proof (induct xs rule: induct_list012)
       case 1 then show ?case by simp
  next case (2 x) then show ?case by simp
  next
    case (3 x y zs)
    then have [simp]: "list_all normalised (map ?f zs) = list_all normalised zs"
      by (simp add: Ball_set[symmetric])
    show ?case
      using 3 by simp
  qed
next case (NonD x1 x2) then show ?case by simp
next case (Executable x1 x2) then show ?case by simp
next case (Repeatable x1 x2) then show ?case by simp
qed

text\<open>Term rewriting step commutes with the copyable term replacement\<close>
lemma remove_one_empty_copyableToRes_term_commute:
  "remove_one_empty (map copyableToRes_term xs) = map copyableToRes_term (remove_one_empty xs)"
proof (induct xs)
     case Nil then show ?case by simp
next case (Cons a xs) then show ?case by (cases a) simp_all
qed

lemma merge_one_parallel_copyableToRes_term_commute:
  "merge_one_parallel (map copyableToRes_term xs) = map copyableToRes_term (merge_one_parallel xs)"
proof (induct xs)
     case Nil then show ?case by simp
next case (Cons a xs) then show ?case by (cases a) simp_all
qed

lemma step_copyableToRes_term:
  "step (copyableToRes_term x) = copyableToRes_term (step x)" (is "step (?f x) = ?f (step x)")
proof (induct x rule: step_induct')
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
  moreover have "list_ex (\<lambda>x. \<not> normalised x) (map ?f xs)"
    using Par_Norm(2) by (fastforce simp add: Bex_set[symmetric])
  ultimately show ?case
    by simp
next
  case (Par_Par xs)
  moreover have "\<not> list_ex (\<lambda>x. \<not> normalised x) (map ?f xs)"
    using Par_Par(2) by (simp add: Bex_set[symmetric])
  ultimately show ?case
    by (simp add: merge_one_parallel_copyableToRes_term_commute)
next
  case (Par_Empty xs)
  moreover have "\<not> list_ex (\<lambda>x. \<not> normalised x) (map ?f xs)"
    using Par_Empty(2) by (simp add: Bex_set[symmetric])
  moreover have "\<not> list_ex is_Parallel xs"
    using Par_Empty(3) not_list_ex by metis
  ultimately show ?case
    by (simp add: remove_one_empty_copyableToRes_term_commute)
next case Par_Nil then show ?case by simp
next case (Par_Single u) then show ?case by simp
next
  case (Par v vb vc)
  moreover have "\<not> list_ex (\<lambda>x. \<not> normalised x) (map ?f (v # vb # vc))"
    using Par(2) by (simp add: Bex_set[symmetric])
  moreover have "\<not> list_ex is_Parallel (v # vb # vc)"
    using Par(3) not_list_ex by metis
  moreover have "\<not> list_ex is_Empty (v # vb # vc)"
    using Par(4) not_list_ex by metis
  ultimately show ?case
    by simp
qed

text\<open>By induction, the replacement of copyable terms also passes through term normalisation\<close>
lemma normal_rewr_copyableToRes_term:
  "normal_rewr (copyableToRes_term x) = copyableToRes_term (normal_rewr x)"
proof (induct x rule: normal_rewr.induct)
  case (1 x)
  then show ?case
  proof (cases "normalised x")
    case True
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using 1 by simp (metis step_copyableToRes_term normal_rewr_step)
  qed
qed

text\<open>Copyable term replacement is injective\<close>
lemma copyableToRes_term_inj:
  "copyableToRes_term x = copyableToRes_term y \<Longrightarrow> x = y"
proof (induct x arbitrary: y)
     case (Res x) then show ?case by (cases y) simp_all
next case (Copyable x) then show ?case by (cases y) simp_all
next case Empty then show ?case by (cases y) simp_all
next case Anything then show ?case by (cases y) simp_all
next
  case (Parallel x)
  then show ?case
    by (cases y) (simp_all, metis list.inj_map_strong)
next case (NonD x1 x2) then show ?case by (cases y) simp_all
next case (Executable x1 x2) then show ?case by (cases y) simp_all
next case (Repeatable x1 x2) then show ?case by (cases y) simp_all
qed

text\<open>Making Copyable Resources Linear\<close>

text\<open>We then lift the term-level replacement to resources\<close>
lift_definition copyableToRes :: "('a, 'b) resource \<Rightarrow> ('a + 'b, 'c) resource"
  is copyableToRes_term by (rule copyableToRes_term_equiv)

lemma copyableToRes_simps [simp]:
  "copyableToRes Empty = Empty"
  "copyableToRes Anything = Anything"
  "copyableToRes (Res a) = Res (Inl a)"
  "copyableToRes (Copyable a) = Res (Inr a)"
  "copyableToRes (Parallel xs) = Parallel (map copyableToRes xs)"
  "copyableToRes (NonD x y) = NonD (copyableToRes x) (copyableToRes y)"
  "copyableToRes (Executable x y) = Executable (copyableToRes x) (copyableToRes y)"
  "copyableToRes (Repeatable x y) = Repeatable (copyableToRes x) (copyableToRes y)"
  by (transfer, simp)+

text\<open>Resource-level replacement is injective, which is vital for preserving composition validity\<close>
lemma copyableToRes_inj:
  fixes x y :: "('a, 'b) resource"
  shows "(copyableToRes x :: ('a + 'b, 'c) resource) = copyableToRes y \<Longrightarrow> x = y"
proof transfer
  fix x y :: "('a, 'b) res_term"
  assume "(copyableToRes_term x :: ('a + 'b, 'c) res_term) \<sim> copyableToRes_term y"
  then show "x \<sim> y"
    unfolding res_term_equiv_is_normal_rewr normal_rewr_copyableToRes_term
    by (rule copyableToRes_term_inj)
qed

lemma copyableToRes_eq_conv [simp]:
  "(copyableToRes x = copyableToRes y) = (x = y)"
  by (metis copyableToRes_inj)

text\<open>Resource-level replacement can then be applied over a process\<close>
primrec process_copyableToRes :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a + 'b, 'c, 'l, 'm) process"
  where
    "process_copyableToRes (Primitive ins outs l m) =
      Primitive (copyableToRes ins) (copyableToRes outs) l m"
  | "process_copyableToRes (Identity a) = Identity (copyableToRes a)"
  | "process_copyableToRes (Swap a b) = Swap (copyableToRes a) (copyableToRes b)"
  | "process_copyableToRes (Seq p q) = Seq (process_copyableToRes p) (process_copyableToRes q)"
  | "process_copyableToRes (Par p q) = Par (process_copyableToRes p) (process_copyableToRes q)"
  | "process_copyableToRes (Opt p q) = Opt (process_copyableToRes p) (process_copyableToRes q)"
  | "process_copyableToRes (InjectL a b) = InjectL (copyableToRes a) (copyableToRes b)"
  | "process_copyableToRes (InjectR a b) = InjectR (copyableToRes a) (copyableToRes b)"
  | "process_copyableToRes (OptDistrIn a b c) =
      OptDistrIn (copyableToRes a) (copyableToRes b) (copyableToRes c)"
  | "process_copyableToRes (OptDistrOut a b c) =
      OptDistrOut (copyableToRes a) (copyableToRes b) (copyableToRes c)"
  | "process_copyableToRes (Duplicate a) = undefined"
      \<comment> \<open>There is no sensible definition for @{const Duplicate}, but we will not need one\<close>
  | "process_copyableToRes (Erase a) = undefined"
      \<comment> \<open>There is no sensible definition for @{const Erase}, but we will not need one\<close>
  | "process_copyableToRes (Represent p) = Represent (process_copyableToRes p)"
  | "process_copyableToRes (Apply a b) = Apply (copyableToRes a) (copyableToRes b)"
  | "process_copyableToRes (Repeat a b) = Repeat (copyableToRes a) (copyableToRes b)"
  | "process_copyableToRes (Close a b) = Close (copyableToRes a) (copyableToRes b)"
  | "process_copyableToRes (Once a b) = Once (copyableToRes a) (copyableToRes b)"
  | "process_copyableToRes (Forget a) = Forget (copyableToRes a)"

subsection\<open>Final Properties\<close>

text\<open>
  The final transformation proceeds by first @{const makeDuplEraToPrim} to remove the resource
  actions that depend on their copyable nature and then @{const process_copyableToRes} to make all
  copyable resources into linear ones.
  We verify that the result:
  \<^item> Has the expected type,
  \<^item> Has as input the original input made linear,
  \<^item> Has as output the original output made linear,
  \<^item> Is valid iff the original is valid.
  \<^item> Contains no copyable atoms
\<close>

notepad begin
  fix x :: "('a, 'b, 'l, 'm) process"
  term "process_copyableToRes (makeDuplEraToPrim x)
        :: ('a + 'b, 'c, 'l + String.literal, 'm + unit) process"
end

lemma eliminateCopyable_input:
  "input (process_copyableToRes (makeDuplEraToPrim x)) = copyableToRes (input x)"
  by (induct x) (simp_all add: resource_par_def)

lemma eliminateCopyable_output:
  "output (process_copyableToRes (makeDuplEraToPrim x)) = copyableToRes (output x)"
  by (induct x) (simp_all add: resource_par_def eliminateCopyable_input)

lemma eliminateCopyable_valid:
  "valid (process_copyableToRes (makeDuplEraToPrim x)) = valid x"
  by (induct x)
     (simp_all add: resource_par_def eliminateCopyable_input eliminateCopyable_output)

lemma set2_process_eliminateCopyable:
  fixes x :: "('a, 'b, 'l, 'm) process"
  shows "set2_process (process_copyableToRes (makeDuplEraToPrim x)) = {}"
proof -
  have [simp]: "set2_resource (copyableToRes x) = {}"
    for x :: "('a, 'b) resource"
    by (induct x rule: resource_induct) simp_all
  show ?thesis
    by (induct x) simp_all
qed

end
