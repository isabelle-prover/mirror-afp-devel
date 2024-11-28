theory ResNormDirect
  imports ResNormalForm
begin

section\<open>Direct Resource Term Normalisation\<close>

text\<open>
  In this section we define a normalisation procedure for resource terms that directly normalises a
  term in a single bottom-up pass.
  This could be considered normalisation by evaluation as opposed to by rewriting.

  Note that, while this procedure is more computationally efficient, it is less useful in proofs.
  In this way it is complemented by rewriting-based normalisation that is less direct but more
  helpful in inductive proofs.
\<close>

text\<open>
  First, for a list of terms where no @{const Parallel} term contains an @{const Empty} term, the
  order of @{const merge_all_parallel} and @{const remove_all_empty} does not matter.
  This is specifically the case for a list of normalised terms.
  As such, our choice of order in the normalisation definition does not matter.
\<close>
lemma merge_all_parallel_remove_all_empty_comm:
  assumes "\<And>ys. Parallel ys \<in> set xs \<Longrightarrow> \<not> list_ex is_Empty ys"
    shows "merge_all_parallel (remove_all_empty xs) = remove_all_empty (merge_all_parallel xs)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a) (simp_all add: remove_all_empty_append remove_all_empty_none)
qed

text\<open>
  Direct normalisation of resource terms proceeds in a single bottom-up pass.
  The interesting case is for @{const Parallel} terms, where any @{const Empty} and nested
  @{const Parallel} children are handled using @{const parallel_parts} and the resulting list is
  turned into the simplest term representing its parallel combination using @{const parallelise}.
\<close>
primrec normal_dir :: "('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term"
  where
    "normal_dir Empty = Empty"
  | "normal_dir Anything = Anything"
  | "normal_dir (Res x) = Res x"
  | "normal_dir (Copyable x) = Copyable x"
  | "normal_dir (Parallel xs) =
      parallelise (merge_all_parallel (remove_all_empty (map normal_dir xs)))"
  | "normal_dir (NonD x y) = NonD (normal_dir x) (normal_dir y)"
  | "normal_dir (Executable x y) = Executable (normal_dir x) (normal_dir y)"
  | "normal_dir (Repeatable x y) = Repeatable (normal_dir x) (normal_dir y)"

text\<open>Any resource term is equivalent to its direct normalisation\<close>
lemma normal_dir_equiv:
  "a \<sim> normal_dir a"
proof (induct a)
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable a) then show ?case by simp
next
  case (Parallel xs)
  then have "Parallel xs \<sim> Parallel (map normal_dir xs)"
    by (intro res_term_equiv.parallel) (simp add: list_all2_conv_all_nth)
  also have "... \<sim> Parallel (remove_all_empty (map normal_dir xs))"
    by (rule remove_all_empty_equiv)
  also have "... \<sim> Parallel (merge_all_parallel (remove_all_empty (map normal_dir xs)))"
    by (rule merge_all_parallel_equiv)
  finally show ?case
    using parallelise_equiv res_term_equiv.trans res_term_equiv.sym by fastforce
next case (NonD a1 a2) then show ?case by (simp add: res_term_equiv.nondet)
next case (Executable a1 a2) then show ?case by (simp add: res_term_equiv.executable)
next case (Repeatable a1 a2) then show ?case by (simp add: res_term_equiv.repeatable)
qed

text\<open>Thus terms with equal normalisation are equivalent\<close>
lemma normal_dir_eq_imp_equiv:
  "normal_dir a = normal_dir b \<Longrightarrow> a \<sim> b"
  using normal_dir_equiv res_term_equiv.sym res_term_equiv.trans by metis

text\<open>
  If the output of @{const merge_all_parallel} still contains a @{const Parallel} term then it must
  have been nested in one of the input elements
\<close>
lemma merge_all_parallel_has_Parallel:
  assumes "list_ex is_Parallel (merge_all_parallel xs)"
  obtains ys
    where "Parallel ys \<in> set xs"
      and "list_ex is_Parallel ys"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    using merge_all_parallel_result by blast
qed

text\<open>
  If the output of @{const remove_all_empty} contains a @{const Parallel} term then it must have
  been in the input
\<close>
lemma remove_all_empty_has_Parallel:
  assumes "Parallel ys \<in> set (remove_all_empty xs)"
    shows "Parallel ys \<in> set xs"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    using remove_all_empty_subset by blast
qed

text\<open>If a resource term normalises to a @{const Parallel} term then that does not contain any nested\<close>
lemma normal_dir_no_nested_Parallel:
  "normal_dir a = Parallel xs \<Longrightarrow> \<not> list_ex is_Parallel xs"
proof (rule notI, induct a arbitrary: xs)
  case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable a) then show ?case by simp
next
  case (Parallel x)
  then have "parallelise (merge_all_parallel (remove_all_empty (map normal_dir x))) = Parallel xs"
    by simp
  then have "list_ex is_Parallel (merge_all_parallel (remove_all_empty (map normal_dir x)))"
    using Parallel(3) ResTerm.parallelise_to_parallel_has_paralell by blast
  then obtain ys
    where "Parallel ys \<in> set (remove_all_empty (map normal_dir x))"
      and ex_ys: "list_ex is_Parallel ys"
    by (erule merge_all_parallel_has_Parallel)
  then have "Parallel ys \<in> set (map normal_dir x)"
    using remove_all_empty_has_Parallel by blast
  then show ?case
    using Parallel(1) ex_ys by fastforce
next case (NonD a1 a2) then show ?case by simp
next case (Executable a1 a2) then show ?case by simp
next case (Repeatable a1 a2) then show ?case by simp
qed

text\<open>
  If a resource term normalises to a @{const Parallel} term then it does not contain @{const Empty}
\<close>
lemma normal_dir_no_nested_Empty:
  "normal_dir a = Parallel xs \<Longrightarrow> \<not> list_ex is_Empty xs"
proof (rule notI, induct a arbitrary: xs)
  case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable a) then show ?case by simp
next
  case (Parallel x)
  then have "parallelise (merge_all_parallel (remove_all_empty (map normal_dir x))) = Parallel xs"
    by simp
  then have "merge_all_parallel (remove_all_empty (map normal_dir x)) = xs"
  proof (elim parallelise_to_parallel_has_empty)
    assume "merge_all_parallel (remove_all_empty (map normal_dir x)) = [Parallel xs]"
    then show ?thesis
      using Parallel(3) merge_all_parallel_has_Parallel normal_dir_no_nested_Parallel
            remove_all_empty_has_Parallel
      by (smt (verit, best) image_iff list.set_map list_ex_simps(1) res_term.discI(5))
  next
    assume "merge_all_parallel (remove_all_empty (map normal_dir x)) = xs"
    then show ?thesis .
  qed
  then have "list_ex is_Empty (merge_all_parallel (remove_all_empty (map normal_dir x)))"
    using Parallel(3) by blast
  then have "list_ex is_Empty (remove_all_empty (map normal_dir x))"
  proof (elim merge_all_parallel_has_empty)
    fix ys
    assume "Parallel ys \<in> set (remove_all_empty (map normal_dir x))" and "list_ex is_Empty ys"
    then show ?thesis
      using Parallel(1) remove_all_empty_has_Parallel
      by (metis (mono_tags, lifting) image_iff list.set_map)
  next
    assume "list_ex is_Empty (remove_all_empty (map normal_dir x))"
    then show ?thesis .
  qed
  then show ?case
    using remove_all_empty_result by blast
next case (NonD a1 a2) then show ?case by simp
next case (Executable a1 a2) then show ?case by simp
next case (Repeatable a1 a2) then show ?case by simp
qed

text\<open>
  Merging @{const Parallel} terms in a list of normalised terms keeps all terms in the result
  normalised
\<close>
lemma normalised_merge_all_parallel:
  assumes "x \<in> set (merge_all_parallel xs)"
      and "\<And>x. x \<in> set xs \<Longrightarrow> normalised x"
    shows "normalised x"
  using assms
proof (induct xs arbitrary: x)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases a)
       case Empty then show ?thesis using Cons by simp metis
  next case Anything then show ?thesis using Cons by simp metis
  next case (Res x3) then show ?thesis using Cons by simp metis
  next case (Copyable x4) then show ?thesis using Cons by simp metis
  next
    case (Parallel x5)
    then show ?thesis
      using Cons by simp (metis Ball_set normalised.simps(5))
  next case (NonD x61 x62) then show ?thesis using Cons by simp metis
  next case (Executable x71 x72) then show ?thesis using Cons by simp metis
  next case (Repeatable x71 x72) then show ?thesis using Cons by simp metis
  qed
qed

text\<open>Normalisation produces resources in normal form\<close>
lemma normalised_normal_dir:
  "normalised (normal_dir a)"
proof (induct a)
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable a) then show ?case by simp
next
  case (Parallel xs)
  have "normalised (parallelise (merge_all_parallel (remove_all_empty (map normal_dir xs))))"
  proof (intro normalised_parallelise)
    fix x
    assume "x \<in> set (merge_all_parallel (remove_all_empty (map normal_dir xs)))"
    then show "normalised x"
      using Parallel(1) normalised_merge_all_parallel remove_all_empty_subset
      by (metis (mono_tags, lifting) imageE list.set_map)
  next
    show "\<not> list_ex is_Empty (merge_all_parallel (remove_all_empty (map normal_dir xs)))"
      using merge_all_parallel_has_empty remove_all_empty_has_Parallel remove_all_empty_result
            normal_dir_no_nested_Empty
      by (metis imageE list.set_map)
  next
    show "\<not> list_ex is_Parallel (merge_all_parallel (remove_all_empty (map normal_dir xs)))"
      using merge_all_parallel_has_Parallel remove_all_empty_has_Parallel
            normal_dir_no_nested_Parallel
      by (metis imageE list.set_map)
  qed
  then show ?case
    by simp
next case (NonD a1 a2) then show ?case by simp
next case (Executable a1 a2) then show ?case by simp
next case (Repeatable a1 a2) then show ?case by simp
qed

text\<open>Normalisation does nothing to resource terms in normal form\<close>
lemma normal_dir_normalised:
  "normalised x \<Longrightarrow> normal_dir x = x"
proof (induct x)
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable x) then show ?case by simp
next
  case (Parallel x)
  then show ?case
    by (simp add: map_idI merge_all_parallel_none normalised_parallel_children not_list_ex
                  parallelise_to_parallel_conv remove_all_empty_none)
next case (NonD x1 x2) then show ?case by simp
next case (Executable x1 x2) then show ?case by simp
next case (Repeatable a1 a2) then show ?case by simp
qed

text\<open>
  Parallelising to anything but @{const Empty} or @{const Parallel} means the input list contained
  just that
\<close>
lemma parallelise_eq_Anything [simp]: "(parallelise xs = Anything) = (xs = [Anything])"
  and parallelise_eq_Res [simp]: "(parallelise xs = Res a) = (xs = [Res a])"
  and parallelise_eq_Copyable [simp]: "(parallelise xs = Copyable b) = (xs = [Copyable b])"
  and parallelise_eq_NonD [simp]: "(parallelise xs = NonD x y) = (xs = [NonD x y])"
  and parallelise_eq_Executable [simp]:"(parallelise xs = Executable x y) = (xs = [Executable x y])"
  and parallelise_eq_Repeatable [simp]:"(parallelise xs = Repeatable x y) = (xs = [Repeatable x y])"
  using parallelise.elims parallelise.simps(2) by blast+

text\<open>Equivalent resource terms normalise to equal results\<close>
lemma res_term_equiv_normal_dir:
  "a \<sim> b \<Longrightarrow> normal_dir a = normal_dir b"
proof (induct a b rule: res_term_equiv.induct)
     case empty then show ?case by simp
next case anything then show ?case by simp
next case (res x) then show ?case by simp
next case (copyable x) then show ?case by simp
next case nil then show ?case by simp
next
  case (singleton a)
  have "\<And>xs. normal_dir a = Parallel xs \<Longrightarrow> parallelise xs = Parallel xs"
    using normalised_normal_dir normalised.simps(5) parallelise_to_parallel_same_length by metis
  then show ?case
    by (cases "normal_dir a" ; simp add: is_Parallel_def)
next
  case (merge x y z)
  then show ?case
  proof (cases "normal_dir (Parallel y) = Empty")
    case True
    then consider
        "merge_all_parallel (remove_all_empty (map normal_dir y)) = []"
      | "merge_all_parallel (remove_all_empty (map normal_dir y)) = [Empty]"
      using parallelise_to_empty_eq by fastforce
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by (simp add: remove_all_empty_append merge_all_parallel_append)
    next
      case 2
      have "list_ex is_Empty (remove_all_empty (map normal_dir y))"
      proof (rule merge_all_parallel_has_empty)
        show "list_ex is_Empty (merge_all_parallel (remove_all_empty (map normal_dir y)))"
          using 2 by simp
        show "list_ex is_Empty (remove_all_empty (map normal_dir y))"
          if "Parallel ys \<in> set (remove_all_empty (map normal_dir y))" and "list_ex is_Empty ys"
          for ys
          using that remove_all_empty_has_Parallel normal_dir_no_nested_Empty
          by (metis ex_map_conv)
      qed
      then show ?thesis
        using remove_all_empty_result by blast
    qed
  next
    case False

    have ?thesis if y: "normal_dir (Parallel y) = Parallel ys" for ys
    proof -
      consider
          "merge_all_parallel (remove_all_empty (map normal_dir y)) = [Parallel ys]"
        | "1 < length (merge_all_parallel (remove_all_empty (map normal_dir y)))"
          and "merge_all_parallel (remove_all_empty (map normal_dir y)) = ys"
        using y parallelise_to_parallel_conv
        by (fastforce simp add: remove_all_empty_append merge_all_parallel_append)
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          by (simp add: remove_all_empty_append merge_all_parallel_append)
             (smt (z3) image_iff list.set_map list_ex_simps(1) merge_all_parallel_has_Parallel
              remove_all_empty_has_Parallel res_term.discI(5) normal_dir_no_nested_Parallel)
      next
        case 2
        then show ?thesis
          using False y by (simp add: remove_all_empty_append merge_all_parallel_append)
      qed
    qed
    then show ?thesis
      using False
      by (cases "normal_dir (Parallel y)")
         (simp_all add: remove_all_empty_append merge_all_parallel_append)
  qed
next
  case (parallel xs ys)
  then have "map normal_dir xs = map normal_dir ys"
    by (clarsimp simp add: list_all2_conv_all_nth list_eq_iff_nth_eq)
  then show ?case
    by simp
next case (nondet x y u v) then show ?case by simp
next case (executable x y u v) then show ?case by simp
next case (repeatable x y u v) then show ?case by simp
next case (sym x y) then show ?case by simp
next case (trans x y z) then show ?case by simp
qed

text\<open>Equivalence of resource term is equality of their normal forms\<close>
lemma res_term_equiv_is_normal_dir:
  "a \<sim> b = (normal_dir a = normal_dir b)"
  using res_term_equiv_normal_dir normal_dir_eq_imp_equiv by standard

text\<open>We use this fact to give a code equation for @{const res_term_equiv}\<close>
lemmas [code] = res_term_equiv_is_normal_dir

text\<open>The normal form is unique in each resource term equivalence class\<close>
lemma normal_dir_unique:
  "\<lbrakk>normal_dir x = x; normal_dir y = y; x \<sim> y\<rbrakk> \<Longrightarrow> x = y"
  using res_term_equiv_normal_dir by metis

end