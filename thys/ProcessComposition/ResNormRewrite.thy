theory ResNormRewrite
  imports
    ResNormalForm
    "Abstract-Rewriting.Abstract_Rewriting"
    Util
begin

section\<open>Rewriting Resource Term Normalisation\<close>

text\<open>
  This resource term normalisation procedure is based on the following rewrite rules:
  \<^item> @{text "Parallel [] \<rightarrow> Empty"}
  \<^item> @{text "Parallel [a] \<rightarrow> a"}
  \<^item> @{text "Parallel (x @ [Parallel y] @ z) \<rightarrow> Parallel (x @ y @ z)"}
  \<^item> @{text "Parallel (x @ [Empty] @ y) \<rightarrow> Parallel (x @ y)"}

  This represents the one-directional, single-step version of resource term equivalence.
  Note that the last rule must be made explicit here, because its counterpart theorem
  @{thm res_term_equiv.drop} can only be derived thanks to symmetry.
\<close>

subsection\<open>Rewriting Relation\<close>

text\<open>
  The rewriting relation contains a rewriting rule for each introduction rule of
  @{const res_term_equiv} except for symmetry and transitivity, and an explicit rule for
  @{thm res_term_equiv.drop}.
\<close>
inductive res_term_rewrite :: "('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term \<Rightarrow> bool" where
  empty: "res_term_rewrite Empty Empty"
| anything: "res_term_rewrite Anything Anything"
| res: "res_term_rewrite (Res x) (Res x)"
| copyable: "res_term_rewrite (Copyable x) (Copyable x)"
| nil: "res_term_rewrite (Parallel []) Empty"
| singleton: "res_term_rewrite (Parallel [a]) a"
| merge: "res_term_rewrite (Parallel (x @ [Parallel y] @ z)) (Parallel (x @ y @ z))"
| drop: "res_term_rewrite (Parallel (x @ [Empty] @ z)) (Parallel (x @ z))"
| parallel: "list_all2 res_term_rewrite xs ys \<Longrightarrow> res_term_rewrite (Parallel xs) (Parallel ys)"
| nondet: "\<lbrakk>res_term_rewrite x y; res_term_rewrite u v\<rbrakk> \<Longrightarrow> res_term_rewrite (NonD x u) (NonD y v)"
| executable: "\<lbrakk>res_term_rewrite x y; res_term_rewrite u v\<rbrakk> \<Longrightarrow>
    res_term_rewrite (Executable x u) (Executable y v)"
| repeatable: "\<lbrakk>res_term_rewrite x y; res_term_rewrite u v\<rbrakk> \<Longrightarrow>
    res_term_rewrite (Repeatable x u) (Repeatable y v)"

hide_fact (open) empty anything res copyable nil singleton merge drop parallel nondet executable
  repeatable

setup \<open>Sign.mandatory_path "res_term_rewrite"\<close>

text\<open>The rewrite relation is reflexive\<close>
lemma refl [simp]:
  "res_term_rewrite x x"
proof (induct x)
     case Empty then show ?case by (rule res_term_rewrite.empty)
next case Anything then show ?case by (rule res_term_rewrite.anything)
next case (Res x) then show ?case by (rule res_term_rewrite.res)
next case (Copyable x) then show ?case by (rule res_term_rewrite.copyable)
next
  case (Parallel x)
  then show ?case
    by (simp add: res_term_rewrite.parallel list.rel_refl_strong)
next case (NonD x1 x2) then show ?case by (rule res_term_rewrite.nondet)
next case (Executable x1 x2) then show ?case by (rule res_term_rewrite.executable)
next case (Repeatable x1 x2) then show ?case by (rule res_term_rewrite.repeatable)
qed

lemma parallel_one:
  "res_term_rewrite a b \<Longrightarrow> res_term_rewrite (Parallel (xs @ [a] @ ys)) (Parallel (xs @ [b] @ ys))"
  using res_term_rewrite.refl res_term_rewrite.parallel
  by (metis list.rel_refl list_all2_Cons2 list_all2_appendI)

setup \<open>Sign.parent_path\<close>

text\<open>Every term rewrites to an equivalent term\<close>
lemma res_term_rewrite_imp_equiv:
  "res_term_rewrite x y \<Longrightarrow> x \<sim> y"
proof (induct x y rule: res_term_rewrite.induct)
     case empty then show ?case by (rule res_term_equiv.empty)
next case anything then show ?case by (rule res_term_equiv.anything)
next case (res x) then show ?case by (rule res_term_equiv.res)
next case (copyable x) then show ?case by (intro res_term_equiv.copyable)
next case nil then show ?case by (rule res_term_equiv.nil)
next case (singleton a) then show ?case by (rule res_term_equiv.singleton)
next case (merge x y z) then show ?case by (rule res_term_equiv.merge)
next case (drop x z) then show ?case by (rule res_term_equiv.drop)
next
  case (parallel xs ys)
  then show ?case
    using res_term_equiv.parallel list_all2_mono by blast
next case (nondet x y u v) then show ?case by (intro res_term_equiv.nondet)
next case (executable x y u v) then show ?case by (intro res_term_equiv.executable)
next case (repeatable x y u v) then show ?case by (intro res_term_equiv.repeatable)
qed

text\<open>By transitivity of the equivalence this holds for transitive closure of the rewriting\<close>
lemma res_term_rewrite_trancl_imp_equiv:
  "res_term_rewrite\<^sup>+\<^sup>+ x y \<Longrightarrow> x \<sim> y"
proof (induct rule: tranclp_induct)
  case (base y)
  then show ?case using res_term_rewrite_imp_equiv by blast
next
  case (step y z)
  then show ?case using res_term_rewrite_imp_equiv res_term_equiv.trans by blast
qed

text\<open>Normalised terms have no distinct term to which they transition\<close>
lemma res_term_rewrite_normalised:
  assumes "normalised x"
    shows "\<nexists>y. res_term_rewrite x y \<and> x \<noteq> y"
proof safe
  fix y
  assume "res_term_rewrite x y"
  then have "x = y"
    using assms
  proof (induct x y rule: res_term_rewrite.induct)
       case empty then show ?case by simp
  next case anything then show ?case by simp
  next case (res x) then show ?case by simp
  next case (copyable x) then show ?case by simp
  next case nil then show ?case by simp
  next case (singleton a) then show ?case by simp
  next case (merge x y z) then show ?case by simp
  next case (drop x z) then show ?case by simp
  next
    case (parallel xs ys)
    then show ?case
      by simp (smt (z3) Ball_set list.rel_eq list.rel_mono_strong)
  next case (nondet x y u v) then show ?case by simp
  next case (executable x y u v) then show ?case by simp
  next case (repeatable x y u v) then show ?case by simp
  qed
  moreover assume "x \<noteq> y"
  ultimately show False
    by metis
qed

lemma res_term_rewrite_normalisedD:
  "\<lbrakk>res_term_rewrite x y; normalised x\<rbrakk> \<Longrightarrow> x = y"
  by (drule res_term_rewrite_normalised) clarsimp

text\<open>Whereas other terms have a distinct term to which they transition\<close>
lemma res_term_rewrite_not_normalised:
  assumes "\<not> normalised x"
    shows "\<exists>y. res_term_rewrite x y \<and> x \<noteq> y"
  using assms
proof (induct x)
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable x) then show ?case by simp
next
  case (Parallel xs)
  then show ?case
  proof (cases "list_ex is_Parallel xs")
    case True
    then obtain a b c where "xs = a @ [Parallel b] @ c" and "list_all (\<lambda>x. \<not> is_Parallel x) a"
      using obtain_first_parallel by metis
    then show ?thesis
      using Parallel res_term_rewrite.merge
      by (metis append_eq_append_conv parallel_neq_single res_term.sel(3))
  next
    case no_par: False
    then show ?thesis
    proof (cases "list_ex is_Empty xs")
      case True
    then obtain a c where "xs = a @ [Empty] @ c" and "list_all (\<lambda>x. \<not> is_Empty x) a"
      using obtain_first_empty by metis
    then show ?thesis
      using no_par Parallel res_term_rewrite.drop by blast
    next
      case no_empty: False
      then show ?thesis
      proof (cases "list_ex (\<lambda>x. \<not> normalised x) xs")
        case True
        then obtain a b c
          where xs: "xs = a @ [b] @ c" and "list_all normalised a" and "\<not> normalised b"
          using obtain_first_unnormalised by metis
        then obtain b' where "res_term_rewrite b b'" and "b \<noteq> b'"
          using Parallel by (metis append_eq_Cons_conv in_set_conv_decomp)
        then have "res_term_rewrite (Parallel (a @ [b] @ c)) (Parallel (a @ [b'] @ c))"
              and "Parallel (a @ [b] @ c) \<noteq> Parallel (a @ [b'] @ c)"
          using res_term_rewrite.parallel_one by blast+
        then show ?thesis
          using xs by metis
      next
        case all_normal: False
        then consider "xs = []" | a where "xs = [a]"
          using no_par no_empty Parallel by (metis Bex_set normalised_parallelise parallelise.elims)
        then show ?thesis
          using res_term_rewrite.nil res_term_rewrite.singleton
          by (metis parallel_neq_single res_term.distinct(29))
      qed
    qed
  qed
next
  case (NonD x1 x2)
  then show ?case
    by (metis normalised.simps(6) res_term.inject(4) res_term_rewrite.nondet res_term_rewrite.refl)
next
  case (Executable x1 x2)
  then show ?case
    by (metis normalised.simps(7) res_term.inject(5) res_term_rewrite.executable
        res_term_rewrite.refl)
next
  case (Repeatable x1 x2)
  then show ?case
    by (metis normalised.simps(8) res_term.inject(6) res_term_rewrite.repeatable
        res_term_rewrite.refl)
qed

text\<open>Therefore a term is normalised iff it rewrites only back to itself\<close>
lemma normalised_is_rewrite_refl:
  "normalised x = (\<forall>y. res_term_rewrite x y \<longrightarrow> x = y)"
  using res_term_rewrite_normalised res_term_rewrite_not_normalised by metis

text\<open>Every term rewrites to one of at most equal size\<close>
lemma res_term_rewrite_not_increase_size:
  "res_term_rewrite x y \<Longrightarrow> size_res_term f g y \<le> size_res_term f g x"
  by (induct x y rule: res_term_rewrite.induct)
     (simp_all add: list_all2_conv_all_nth size_list_conv_sum_list sum_list_mono_list_all2)

subsection\<open>Rewriting Bound\<close>

text\<open>
  There is an upper bound to how many rewriting steps could be applied to a term.
  We find it by considering the worst (most un-normalised) possible case of each node.
\<close>
primrec res_term_rewrite_bound :: "('a, 'b) res_term \<Rightarrow> nat"
  where
    "res_term_rewrite_bound Empty = 0"
  | "res_term_rewrite_bound Anything = 0"
  | "res_term_rewrite_bound (Res a) = 0"
  | "res_term_rewrite_bound (Copyable x) = 0"
  | "res_term_rewrite_bound (Parallel xs) =
      sum_list (map res_term_rewrite_bound xs) + length xs + 1"
    \<comment> \<open>All the steps of the children, plus one for every child that could need to be merged/dropped
        and another if in the end there are less than two children.\<close>
  | "res_term_rewrite_bound (NonD x y) = res_term_rewrite_bound x + res_term_rewrite_bound y"
  | "res_term_rewrite_bound (Executable x y) = res_term_rewrite_bound x + res_term_rewrite_bound y"
  | "res_term_rewrite_bound (Repeatable x y) = res_term_rewrite_bound x + res_term_rewrite_bound y"

text\<open>For un-normalised terms the bound is non-zero\<close>
lemma res_term_rewrite_bound_not_normalised:
  "\<not> normalised x \<Longrightarrow> res_term_rewrite_bound x \<noteq> 0"
  by (induct x ; fastforce)

text\<open>Rewriting relation does not increase this bound\<close>
lemma res_term_rewrite_non_increase_bound:
  "res_term_rewrite x y \<Longrightarrow> res_term_rewrite_bound y \<le> res_term_rewrite_bound x"
  by (induct x y rule: res_term_rewrite.induct)
     (simp_all add: sum_list_mono_list_all2 list_all2_conv_all_nth)

subsection\<open>Step\<close>

text\<open>
  The rewriting step function implements a specific algorithm for the rewriting relation by picking
  one approach where the relation allows multiple rewriting paths.
  To help define its parallel resource case, we first define a function to remove one @{const Empty}
  term from a list and another to merge the children of one @{const Parallel} term up into the
  containing list of terms.
\<close>

subsubsection\<open>Removing One Empty\<close>

text\<open>Remove the first @{const Empty} from a list of term\<close>
fun remove_one_empty :: "('a, 'b) res_term list \<Rightarrow> ('a, 'b) res_term list"
  where
    "remove_one_empty [] = []"
  | "remove_one_empty (Empty # xs) = xs"
  | "remove_one_empty (x # xs) = x # remove_one_empty xs"

lemma remove_one_empty_cons [simp]:
  "is_Empty x \<Longrightarrow> remove_one_empty (x # xs) = xs"
  "\<not> is_Empty x \<Longrightarrow> remove_one_empty (x # xs) = x # remove_one_empty xs"
  by (cases x ; simp)+

lemma remove_one_empty_append:
  "list_all (\<lambda>x. \<not> is_Empty x) a \<Longrightarrow> remove_one_empty (a @ d) = a @ remove_one_empty d"
  by (induct a ; simp)

lemma remove_one_empty_distinct:
  "list_ex is_Empty xs \<Longrightarrow> remove_one_empty xs \<noteq> xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

text\<open>This is identity when there are no @{const Empty} terms\<close>
lemma remove_one_empty_none [simp]:
  "\<not> list_ex is_Empty xs \<Longrightarrow> remove_one_empty xs = xs"
  by (induct xs rule: remove_one_empty.induct ; simp)

text\<open>This decreases length by one when there are @{const Empty} terms\<close>
lemma length_remove_one_empty [simp]:
  "list_ex is_Empty xs \<Longrightarrow> length (remove_one_empty xs) + 1 = length xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases "is_Empty a" ; simp)
qed

text\<open>Removing an @{const Empty} term does not increase the size\<close>
lemma remove_one_empty_not_increase_size:
  "size_res_term f g (Parallel (remove_one_empty xs)) \<le> size_res_term f g (Parallel xs)"
  by (induct xs rule: remove_one_empty.induct ; simp)

text\<open>Any @{const Parallel} term is equivalent to itself with an @{const Empty} term removed\<close>
lemma remove_one_empty_equiv:
  "Parallel xs \<sim> Parallel (remove_one_empty xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases "is_Empty a")
    case True
    then show ?thesis
      using res_term_equiv.drop[of Nil] Cons by (fastforce simp add: is_Empty_def)
  next
    case False
    then show ?thesis
      using Cons by (simp add: res_term_parallel_cons)
  qed
qed

text\<open>Removing an @{const Empty} term commutes with the resource term map\<close>
lemma remove_one_empty_map:
  "map (map_res_term f g) (remove_one_empty xs) = remove_one_empty (map (map_res_term f g) xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases "is_Empty a" ; simp)
qed

text\<open>
  The result of dropping an @{const Empty} from a list of resource terms is a subset of the original
  list
\<close>
lemma remove_one_empty_subset:
  "x \<in> set (remove_one_empty xs) \<Longrightarrow> x \<in> set xs"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases "is_Empty a" ; simp) blast
qed

subsubsection\<open>Merging One Parallel\<close>

text\<open>Merge the first @{const Parallel} in a list of terms\<close>
fun merge_one_parallel :: "('a, 'b) res_term list \<Rightarrow> ('a, 'b) res_term list"
  where
    "merge_one_parallel [] = []"
  | "merge_one_parallel (Parallel x # xs) = x @ xs"
  | "merge_one_parallel (x # xs) = x # merge_one_parallel xs"

lemma merge_one_parallel_cons_not [simp]:
  "\<not> is_Parallel x \<Longrightarrow> merge_one_parallel (x # xs) = x # merge_one_parallel xs"
  by (cases x ; simp)

lemma merge_one_parallel_append:
  "list_all (\<lambda>x. \<not> is_Parallel x) a \<Longrightarrow> merge_one_parallel (a @ d) = a @ merge_one_parallel d"
  for a d
  by (induct a ; simp)

lemma merge_one_parallel_distinct:
  "list_ex is_Parallel xs \<Longrightarrow> merge_one_parallel xs \<noteq> xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp) (metis parallel_neq_single)
qed

text\<open>This is identity when there are no @{const Parallel} terms\<close>
lemma merge_one_parallel_none [simp]:
  "\<not> list_ex is_Parallel xs \<Longrightarrow> merge_one_parallel xs = xs"
  by (induct xs rule: merge_one_parallel.induct ; simp)

text\<open>Merging a @{const Parallel} term does not increase the size\<close>
lemma merge_one_parallel_not_increase_size:
  "size_res_term f g (Parallel (merge_one_parallel xs)) \<le> size_res_term f g (Parallel xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

text\<open>Any @{const Parallel} term is equivalent to itself with a @{const Parallel} term merged\<close>
lemma merge_one_parallel_equiv:
  "Parallel xs \<sim> Parallel (merge_one_parallel xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases "is_Parallel a")
    case True
    then show ?thesis
      using Cons res_term_equiv.merge[of Nil] by (fastforce simp add: is_Parallel_def)
  next
    case False
    then show ?thesis
      using Cons by (simp add: res_term_parallel_cons)
  qed
qed

text\<open>Merging a @{const Parallel} term commutes with the resource term map\<close>
lemma merge_one_parallel_map:
  "map (map_res_term f g) (merge_one_parallel xs) = merge_one_parallel (map (map_res_term f g) xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

subsubsection\<open>Rewriting Step Function\<close>

text\<open>
  The rewriting step function itself performs one rewrite for any un-normalised input term.
  Where there are multiple choices, it proceeds as follows:
  \<^item> For binary internal nodes (@{const NonD}, @{const Executable} and @{const Repeatable}), first
    fully rewrite the first child until normalised and only then start rewriting the second.
  \<^item> For @{const Parallel} nodes proceed in phases:
    \<^item> If any child is not normalised, rewrite all children; otherwise
    \<^item> If there is some nested @{const Parallel} node in the children, merge one up; otherwise
    \<^item> If there is some @{const Empty} node in the children, remove one; otherwise
    \<^item> If there are no children, then return @{const Empty}; otherwise
    \<^item> If there is exactly one child, then return that term; otherwise
    \<^item> Do nothing and return the same term.
\<close>
primrec step :: "('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term"
  where
    "step Empty = Empty"
  | "step Anything = Anything"
  | "step (Res x) = Res x"
  | "step (Copyable x) = Copyable x"
  | "step (NonD x y) =
      ( if \<not> normalised x then NonD (step x) y
        else if \<not> normalised y then NonD x (step y)
        else NonD x y)"
  | "step (Executable x y) =
      ( if \<not> normalised x then Executable (step x) y
        else if \<not> normalised y then Executable x (step y)
        else Executable x y)"
  | "step (Repeatable x y) =
      ( if \<not> normalised x then Repeatable (step x) y
        else if \<not> normalised y then Repeatable x (step y)
        else Repeatable x y)"
  | "step (Parallel xs) =
      ( if list_ex (\<lambda>x. \<not> normalised x) xs then Parallel (map step xs)
        else if list_ex is_Parallel xs then Parallel (merge_one_parallel xs)
        else if list_ex is_Empty xs then Parallel (remove_one_empty xs)
        else (case xs of
                [] \<Rightarrow> Empty
              | [a] \<Rightarrow> a
              | _ \<Rightarrow> Parallel xs))"

text\<open>Case split and induction for step fully expanded\<close>
lemma step_cases
  [case_names Empty Anything Res Copyable NonD_L NonD_R NonD Executable_L Executable_R Executable
              Repeatable_L Repeatable_R Repeatable Par_Norm Par_Par Par_Empty Par_Nil Par_Single
              Par]:
  assumes "x = Empty \<Longrightarrow> P"
      and "x = Anything \<Longrightarrow> P"
      and "\<And>a. x = Res a \<Longrightarrow> P"
      and "\<And>u. x = Copyable u \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>\<not> normalised u; x = NonD u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>normalised u; \<not> normalised v; x = NonD u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>normalised u; normalised v; x = NonD u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>\<not> normalised u; x = Executable u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>normalised u; \<not> normalised v; x = Executable u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>normalised u; normalised v; x = Executable u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>\<not> normalised u; x = Repeatable u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>normalised u; \<not> normalised v; x = Repeatable u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>u v. \<lbrakk>normalised u; normalised v; x = Repeatable u v\<rbrakk> \<Longrightarrow> P"
      and "\<And>xs. \<lbrakk>x = Parallel xs; \<exists>a. a \<in> set xs \<and> \<not> normalised a\<rbrakk> \<Longrightarrow> P"
      and "\<And>xs. \<lbrakk>x = Parallel xs; \<forall>a. a \<in> set xs \<longrightarrow> normalised a; list_ex is_Parallel xs\<rbrakk> \<Longrightarrow> P"
      and "\<And>xs. \<lbrakk>x = Parallel xs; \<forall>a. a \<in> set xs \<longrightarrow> normalised a;
                  list_all (\<lambda>x. \<not> is_Parallel x) xs; list_ex is_Empty xs\<rbrakk> \<Longrightarrow> P"
      and "x = Parallel [] \<Longrightarrow> P"
      and "\<And>u. \<lbrakk>x = Parallel [u]; normalised u; \<not> is_Parallel u; \<not> is_Empty u\<rbrakk> \<Longrightarrow> P"
      and "\<And>v vb vc. \<lbrakk>x = Parallel (v # vb # vc); \<forall>a. a \<in> set (v # vb # vc) \<longrightarrow> normalised a;
                      list_all (\<lambda>x. \<not> is_Parallel x) (v # vb # vc);
                      list_all (\<lambda>x. \<not> is_Empty x) (v # vb # vc)\<rbrakk>
            \<Longrightarrow> P"
    shows P
proof (cases x)
     case Empty then show ?thesis using assms by simp
next case Anything then show ?thesis using assms by simp
next case (Res x3) then show ?thesis using assms by simp
next case (Copyable x4) then show ?thesis using assms by simp
next
  case (Parallel xs)
  then show ?thesis
  proof (cases "list_ex (\<lambda>x. \<not> normalised x) xs")
    case True
    then show ?thesis
      using assms(14) by (meson Bex_set Parallel)
  next
    case not_norm: False
    then show ?thesis
    proof (cases "list_ex is_Parallel xs")
      case True
      then show ?thesis
        using Parallel assms(14,15) by blast
    next
      case not_par: False
      then show ?thesis
      proof (cases "list_ex is_Empty xs")
        case True
        then show ?thesis
          by (metis not_par Parallel assms(14,16) not_list_ex)
      next
        case not_empty: False
        then show ?thesis
        proof (cases xs rule: remdups_adj.cases)
          case 1
          then show ?thesis
            by (simp add: Parallel assms(17))
        next
          case (2 x)
          then show ?thesis
            using Parallel assms(14,18) not_empty not_par by fastforce
        next
          case (3 x y xs)
          then show ?thesis
            by (metis Parallel assms(14,19) not_empty not_list_ex not_par)
        qed
      qed
    qed
  qed
next case (NonD x61 x62) then show ?thesis using assms(5-7) by blast
next case (Executable x71 x72) then show ?thesis using assms(8-10) by blast
next case (Repeatable x71 x72) then show ?thesis using assms(11-13) by blast
qed

lemma step_induct
  [case_names Empty Anything Res Copyable NonD_L NonD_R NonD Executable_L Executable_R Executable
              Repeatable_L Repeatable_R Repeatable Par_Norm Par_Par Par_Empty Par_Nil Par_Single
              Par]:
  assumes "P Empty"
      and "P Anything"
      and "\<And>a. P (Res a)"
      and "\<And>x. P (Copyable x)"
      and "\<And>x y. \<lbrakk>P x; P y; \<not> normalised x\<rbrakk> \<Longrightarrow> P (NonD x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; \<not> normalised y\<rbrakk> \<Longrightarrow> P (NonD x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; normalised y\<rbrakk> \<Longrightarrow> P (NonD x y)"
      and "\<And>x y. \<lbrakk>P x; P y; \<not> normalised x\<rbrakk> \<Longrightarrow> P (Executable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; \<not> normalised y\<rbrakk> \<Longrightarrow> P (Executable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; normalised y\<rbrakk> \<Longrightarrow> P (Executable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; \<not> normalised x\<rbrakk> \<Longrightarrow> P (Repeatable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; \<not> normalised y\<rbrakk> \<Longrightarrow> P (Repeatable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; normalised y\<rbrakk> \<Longrightarrow> P (Repeatable x y)"
      and "\<And>xs. \<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> P x; \<exists>a. a \<in> set xs \<and> \<not> normalised a\<rbrakk> \<Longrightarrow> P (Parallel xs)"
      and "\<And>xs. \<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> P x; \<forall>a. a \<in> set xs \<longrightarrow> normalised a; list_ex is_Parallel xs\<rbrakk>
            \<Longrightarrow> P (Parallel xs)"
      and "\<And>xs. \<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> P x; \<forall>a. a \<in> set xs \<longrightarrow> normalised a
                ; list_all (\<lambda>x. \<not> is_Parallel x) xs; list_ex is_Empty xs\<rbrakk>
            \<Longrightarrow> P (Parallel xs)"
      and "P (Parallel [])"
      and "\<And>u. \<lbrakk>P u; normalised u; \<not> is_Parallel u; \<not> is_Empty u\<rbrakk> \<Longrightarrow> P (Parallel [u])"
      and "\<And>v vb vc.
              \<lbrakk> \<And>x. x \<in> set (v # vb # vc) \<Longrightarrow> P x; \<forall>a. a \<in> set (v # vb # vc) \<longrightarrow> normalised a
              ; list_all (\<lambda>x. \<not> is_Parallel x) (v # vb # vc)
              ; list_all (\<lambda>x. \<not> is_Empty x) (v # vb # vc)\<rbrakk>
            \<Longrightarrow> P (Parallel (v # vb # vc))"
    shows "P x"
proof (induct x)
     case Empty then show ?case using assms by simp
next case Anything then show ?case using assms by simp
next case (Res x) then show ?case using assms by simp
next case (Copyable x) then show ?case using assms by simp
next
  case (Parallel xs)
  then show ?case
  proof (cases "list_ex (\<lambda>x. \<not> normalised x) xs")
    case True
    then show ?thesis
      using assms(14) by (metis Bex_set Parallel)
  next
    case not_norm: False
    then show ?thesis
    proof (cases "list_ex is_Parallel xs")
      case True
      then show ?thesis
        using Parallel assms(14,15) by blast
    next
      case not_par: False
      then show ?thesis
      proof (cases "list_ex is_Empty xs")
        case True
        then show ?thesis
          by (metis not_par Parallel assms(14,16) not_list_ex)
      next
        case not_empty: False
        then show ?thesis
        proof (cases xs rule: remdups_adj.cases)
          case 1
          then show ?thesis
            by (simp add: Parallel assms(17))
        next
          case (2 x)
          then show ?thesis
            using Parallel assms(14,18) not_empty not_par by fastforce
        next
          case (3 x y xs)
          then show ?thesis
            by (metis Parallel assms(14,19) not_empty not_list_ex not_par)
        qed
      qed
    qed
  qed
next case (NonD x61 x62) then show ?case using assms(5-7) by blast
next case (Executable x71 x72) then show ?case using assms(8-10) by blast
next case (Repeatable x71 x72) then show ?case using assms(11-13) by blast
qed

text\<open>Variant of induction with some relevant step results is also useful\<close>
lemma step_induct'
  [case_names Empty Anything Res Copyable NonD_L NonD_R NonD Executable_L Executable_R Executable
              Repeatable_L Repeatable_R Repeatable Par_Norm Par_Par Par_Empty Par_Nil Par_Single
              Par]:
  assumes "P Empty"
      and "P Anything"
      and "\<And>a. P (Res a)"
      and "\<And>x. P (Copyable x)"
      and "\<And>x y. \<lbrakk>P x; P y; \<not> normalised x; step (NonD x y) = NonD (step x) y\<rbrakk> \<Longrightarrow> P (NonD x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; \<not> normalised y; step (NonD x y) = NonD x (step y)\<rbrakk>
            \<Longrightarrow> P (NonD x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; normalised y; step (NonD x y) = NonD x y\<rbrakk>
            \<Longrightarrow> P (NonD x y)"
      and "\<And>x y. \<lbrakk>P x; P y; \<not> normalised x; step (Executable x y) = Executable (step x) y\<rbrakk>
            \<Longrightarrow> P (Executable x y)"
      and "\<And>x y. \<lbrakk> P x; P y; normalised x; \<not> normalised y
                  ; step (Executable x y) = Executable x (step y)\<rbrakk>
            \<Longrightarrow> P (Executable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; normalised y; step (Executable x y) = Executable x y\<rbrakk>
            \<Longrightarrow> P (Executable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; \<not> normalised x; step (Repeatable x y) = Repeatable (step x) y\<rbrakk>
            \<Longrightarrow> P (Repeatable x y)"
      and "\<And>x y. \<lbrakk> P x; P y; normalised x; \<not> normalised y
                  ; step (Repeatable x y) = Repeatable x (step y)\<rbrakk>
            \<Longrightarrow> P (Repeatable x y)"
      and "\<And>x y. \<lbrakk>P x; P y; normalised x; normalised y; step (Repeatable x y) = Repeatable x y\<rbrakk>
            \<Longrightarrow> P (Repeatable x y)"
      and "\<And>xs. \<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> P x; \<exists>a. a \<in> set xs \<and> \<not> normalised a
                ; step (Parallel xs) = Parallel (map step xs)\<rbrakk>
            \<Longrightarrow> P (Parallel xs)"
      and "\<And>xs. \<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> P x; \<forall>a. a \<in> set xs \<longrightarrow> normalised a; list_ex is_Parallel xs;
                  step (Parallel xs) = Parallel (merge_one_parallel xs)\<rbrakk>
            \<Longrightarrow> P (Parallel xs)"
      and "\<And>xs. \<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> P x; \<forall>a. a \<in> set xs \<longrightarrow> normalised a
                ; list_all (\<lambda>x. \<not> is_Parallel x) xs; list_ex is_Empty xs
                ; step (Parallel xs) = Parallel (remove_one_empty xs)\<rbrakk>
            \<Longrightarrow> P (Parallel xs)"
      and "P (Parallel [])"
      and "\<And>u. \<lbrakk>P u; normalised u; \<not> is_Parallel u; \<not> is_Empty u; step (Parallel [u]) = u\<rbrakk>
            \<Longrightarrow> P (Parallel [u])"
      and "\<And>v vb vc.
            \<lbrakk> \<And>x. x \<in> set (v # vb # vc) \<Longrightarrow> P x; \<forall>a. a \<in> set (v # vb # vc) \<longrightarrow> normalised a
            ; list_all (\<lambda>x. \<not> is_Parallel x) (v # vb # vc)
            ; list_all (\<lambda>x. \<not> is_Empty x) (v # vb # vc)
            ; step (Parallel (v # vb # vc)) = Parallel (v # vb # vc)\<rbrakk>
            \<Longrightarrow> P (Parallel (v # vb # vc))"
    shows "P x"
proof (induct x rule: step_induct)
     case Empty then show ?case using assms(1) by simp
next case Anything then show ?case using assms(2) by simp
next case (Res a) then show ?case using assms(3) by simp
next case (Copyable x) then show ?case using assms(4) by simp
next case (NonD_L x y) then show ?case using assms(5) by simp
next case (NonD_R x y) then show ?case using assms(6) by simp
next case (NonD x y) then show ?case using assms(7) by simp
next case (Executable_L x y) then show ?case using assms(8) by simp
next case (Executable_R x y) then show ?case using assms(9) by simp
next case (Executable x y) then show ?case using assms(10) by simp
next case (Repeatable_L x y) then show ?case using assms(11) by simp
next case (Repeatable_R x y) then show ?case using assms(12) by simp
next case (Repeatable x y) then show ?case using assms(13) by simp
next case (Par_Norm xs) then show ?case using assms(14) by (simp add: Bex_set[symmetric] Bex_def)
next case (Par_Par xs) then show ?case using assms(15) by (simp add: Bex_set[symmetric] Bex_def)
next
  case (Par_Empty xs)
  then show ?case
    using assms(15,16) by (metis (mono_tags, lifting) list_ex_iff step.simps(8))
next case Par_Nil then show ?case using assms(17) by simp
next case (Par_Single u) then show ?case using assms(18) by simp
next
  case (Par v vb vc)
  then show ?case
  proof (rule assms(19))
    show "\<And>x. x \<in> set (v # vb # vc) \<Longrightarrow> x \<in> set (v # vb # vc)"
      by simp
    show "step (Parallel (v # vb # vc)) = Parallel (v # vb # vc)"
      using Par by (simp add: Ball_set[symmetric] Bex_set[symmetric])
  qed
qed

text\<open>Set of atoms remains unchanged by rewriting step\<close>
lemma set1_res_term_step [simp]:
  "set1_res_term (step x) = set1_res_term x"
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
next case (Par_Norm xs) then show ?case by simp
next
  case (Par_Par xs)
  then show ?case
    by (fastforce elim!: obtain_first_parallel simp add: merge_one_parallel_append)
next
  case (Par_Empty xs)
  then show ?case
    by (fastforce elim!: obtain_first_empty simp add: remove_one_empty_append)
next case Par_Nil then show ?case by simp
next case (Par_Single u) then show ?case by simp
next case (Par v vb vc) then show ?case by simp
qed

lemma set2_res_term_step [simp]:
  "set2_res_term (step x) = set2_res_term x"
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
next case (Par_Norm xs) then show ?case by simp
next
  case (Par_Par xs)
  then show ?case
    by (fastforce elim!: obtain_first_parallel simp add: merge_one_parallel_append)
next
  case (Par_Empty xs)
  then show ?case
    by (fastforce elim!: obtain_first_empty simp add: remove_one_empty_append)
next case Par_Nil then show ?case by simp
next case (Par_Single u) then show ?case by simp
next case (Par v vb vc) then show ?case by simp
qed

text\<open>
  Resource term rewriting relation contains the step function graph.
  In other words, the step function is a particular strategy implementing that rewriting.
\<close>
lemma res_term_rewrite_contains_step:
  "res_term_rewrite x (step x)"
proof (induct x rule: step_induct')
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res a) then show ?case by simp
next case (Copyable x) then show ?case by simp
next case (NonD_L x y) then show ?case by (simp add: res_term_rewrite.nondet)
next case (NonD_R x y) then show ?case by (simp add: res_term_rewrite.nondet)
next case (NonD x y) then show ?case by simp
next case (Executable_L x y) then show ?case by (simp add: res_term_rewrite.executable)
next case (Executable_R x y) then show ?case by (simp add: res_term_rewrite.executable)
next case (Executable x y) then show ?case by simp
next case (Repeatable_L x y) then show ?case by (simp add: res_term_rewrite.repeatable)
next case (Repeatable_R x y) then show ?case by (simp add: res_term_rewrite.repeatable)
next case (Repeatable x y) then show ?case by simp
next
  case (Par_Norm xs)
  then show ?case
    by (simp add: Bex_set[symmetric] res_term_rewrite.intros(9) list.rel_map(2) list_all2_same)
next
  case (Par_Par xs)
  moreover obtain a b c where "xs = a @ [Parallel b] @ c" and "list_all (\<lambda>x. \<not> is_Parallel x) a"
    using Par_Par(3) obtain_first_parallel by blast
  moreover have "res_term_rewrite (Parallel (a @ [Parallel b] @ c)) (Parallel (a @ b @ c))"
    using res_term_rewrite.intros(7) .
  ultimately show ?case
    by (simp add: Bex_set[symmetric] merge_one_parallel_append)
next
  case (Par_Empty xs)
  moreover obtain a c where "xs = a @ [Empty] @ c" and "list_all (\<lambda>x. \<not> is_Empty x) a"
    using Par_Empty(4) obtain_first_empty by blast
  moreover have "res_term_rewrite (Parallel (a @ [Empty] @ c)) (Parallel (a @ c))"
    using res_term_rewrite.intros(8) .
  ultimately show ?case
    by (simp add: Bex_set[symmetric] remove_one_empty_append)
next case Par_Nil then show ?case by (simp add: res_term_rewrite.intros(5))
next case (Par_Single u) then show ?case by (simp add: res_term_rewrite.intros(6))
next case (Par v vb vc) then show ?case by simp
qed

text\<open>Resource term being normalised is the same as the step not changing it\<close>
lemma normalised_is_step_id:
  "normalised x = (step x = x)"
proof
  show "normalised x \<Longrightarrow> step x = x"
  by (metis res_term_rewrite_contains_step res_term_rewrite_normalised)
  show "step x = x \<Longrightarrow> normalised x"
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
  next case (Par_Norm xs) then show ?case by simp (metis map_eq_conv map_ident)
  next case (Par_Par xs) then show ?case by (simp add: merge_one_parallel_distinct)
  next case (Par_Empty xs) then show ?case by (simp add: remove_one_empty_distinct)
  next case Par_Nil then show ?case by simp
  next case (Par_Single u) then show ?case by simp
  next case (Par v vb vc) then show ?case by (simp add: Ball_set[symmetric])
  qed
qed

text\<open>So, for normalised terms we can drop any step applied to them\<close>
lemma step_normalised [simp]:
  "normalised x \<Longrightarrow> step x = x"
  using normalised_is_step_id by (rule iffD1)

text\<open>Rewriting step never increases the term size\<close>
lemma step_not_increase_size:
  "size_res_term f g (step x) \<le> size_res_term f g x"
  using res_term_rewrite_not_increase_size res_term_rewrite_contains_step by blast

text\<open>Every resource is equivalent to itself after the step\<close>
lemma res_term_equiv_step:
  "x \<sim> step x"
  using res_term_rewrite_contains_step res_term_rewrite_imp_equiv by blast

text\<open>Normalisation step commutes with the resource term map\<close>
lemma step_map:
  "map_res_term f g (step x) = step (map_res_term f g x)"
proof (induct x rule: step_induct')
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res a) then show ?case by simp
next case (Copyable x) then show ?case by simp
next case (NonD_L x y) then show ?case by (simp add: normalised_map)
next case (NonD_R x y) then show ?case by (simp add: normalised_map)
next case (NonD x y) then show ?case by simp
next case (Executable_L x y) then show ?case by (simp add: normalised_map)
next case (Executable_R x y) then show ?case by (simp add: normalised_map)
next case (Executable x y) then show ?case by simp
next case (Repeatable_L x y) then show ?case by (simp add: normalised_map)
next case (Repeatable_R x y) then show ?case by (simp add: normalised_map)
next case (Repeatable x y) then show ?case by simp
next
  case (Par_Norm xs)
  then show ?case
    by (fastforce simp add: Bex_set[symmetric] normalised_map)
next
  case (Par_Par xs)
  then show ?case
    by (fastforce simp add: Bex_set[symmetric] normalised_map merge_one_parallel_map)
next
  case (Par_Empty xs)
  then show ?case
    by (simp add: Bex_set[symmetric] normalised_map remove_one_empty_map)
       (metis Ball_set)
next case Par_Nil then show ?case by simp
next case (Par_Single u) then show ?case by (simp add: normalised_map)
next
  case (Par v vb vc)
  then show ?case
    by (fastforce simp add: Bex_set[symmetric] Ball_set normalised_map)
qed

text\<open>Because it implements the rewriting relation, the non-increasing of bound extends to the step\<close>
lemmas res_term_rewrite_bound_step_non_increase =
  res_term_rewrite_non_increase_bound[OF res_term_rewrite_contains_step]

text\<open>
  On un-normalised terms, the step actually strictly decreases the bound.
  While this should also be true of the rewriting relation it implements, the stricter way the step
  proceeds makes this proof more tractable.
\<close>
lemma res_term_rewrite_bound_step_decrease:
  "\<not> normalised x \<Longrightarrow> res_term_rewrite_bound (step x) < res_term_rewrite_bound x"
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
  then have "(\<Sum>x\<leftarrow>xs. res_term_rewrite_bound (step x)) < sum_list (map res_term_rewrite_bound xs)"
    by (meson res_term_rewrite_bound_step_non_increase sum_list_mono_one_strict)
  then show ?case
    using Par_Norm.hyps by (simp add: comp_def)
next
  case (Par_Par xs)
  then show ?case
    by (fastforce elim: obtain_first_parallel simp add: merge_one_parallel_append)
next
  case (Par_Empty xs)
  then show ?case
    by (fastforce elim: obtain_first_empty simp add: remove_one_empty_append)
next case Par_Nil then show ?case by simp
next case (Par_Single u) then show ?case by simp
next case (Par v vb vc) then show ?case using normalised_is_step_id by blast
qed

subsection\<open>Normalisation Procedure\<close>

text\<open>Rewrite a resource term until normalised\<close>
function normal_rewr :: "('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term"
  where "normal_rewr x = (if normalised x then x else normal_rewr (step x))"
  by pat_completeness auto

text\<open>This terminates with the rewriting bound as measure, because the step keeps decreasing it\<close>
termination normal_rewr
  using res_term_rewrite_bound_step_decrease
  by (relation "Wellfounded.measure res_term_rewrite_bound", auto)

text\<open>We remove the normalisation procedure definition from the simplifier, because it can loop\<close>
lemmas [simp del] = normal_rewr.simps

text\<open>However, the terminal case can be safely used for simplification\<close>
lemma normalised_normal_rewr [simp]:
  "normalised x \<Longrightarrow> normal_rewr x = x"
  by (simp add: normal_rewr.simps)

text\<open>Normalisation produces actually normalised terms\<close>
lemma normal_rewr_normalised:
  "normalised (normal_rewr x)"
  by (induct x rule: normal_rewr.induct, simp add: normal_rewr.simps)

text\<open>Normalisation is idempotent\<close>
lemma normal_rewr_idempotent [simp]:
  "normal_rewr (normal_rewr x) = normal_rewr x"
  using normal_rewr_normalised normalised_normal_rewr by blast

text\<open>Normalisation absorbs rewriting step\<close>
lemma normal_rewr_step:
  "normal_rewr x = normal_rewr (step x)"
  by (cases "normalised x") (simp_all add: normal_rewr.simps)

text\<open>Normalisation leaves leaf terms unchanged\<close>
lemma normal_rewr_leaf:
  "normal_rewr Empty = Empty"
  "normal_rewr Anything = Anything"
  "normal_rewr (Res x) = Res x"
  "normal_rewr (Copyable x) = Copyable x"
  by simp_all

text\<open>
  Normalisation passes through @{const NonD}, @{const Executable} and @{const Repeatable}
  constructors
\<close>
lemma normal_rewr_nondet:
  "normal_rewr (NonD x y) =  NonD (normal_rewr x) (normal_rewr y)"
proof (induct x rule: normal_rewr.induct)
  case x: (1 x)
  then show ?case
  proof (induct y rule: normal_rewr.induct)
    case y: (1 y)
    then show ?case
      by (metis normal_rewr_step normalised.simps(6) normalised_normal_rewr step.simps(5))
  qed
qed
lemma normal_rewr_executable:
  "normal_rewr (Executable x y) = Executable (normal_rewr x) (normal_rewr y)"
proof (induct x rule: normal_rewr.induct)
  case x: (1 x)
  then show ?case
  proof (induct y rule: normal_rewr.induct)
    case y: (1 y)
    then show ?case
      by (metis normal_rewr_step normalised.simps(7) normalised_normal_rewr step.simps(6))
  qed
qed
lemma normal_rewr_repeatable:
  "normal_rewr (Repeatable x y) = Repeatable (normal_rewr x) (normal_rewr y)"
proof (induct x rule: normal_rewr.induct)
  case x: (1 x)
  then show ?case
  proof (induct y rule: normal_rewr.induct)
    case y: (1 y)
    then show ?case
      by (metis normal_rewr_step normalised.simps(8) normalised_normal_rewr step.simps(7))
  qed
qed

text\<open>Normalisation simplifies empty @{const Parallel} terms\<close>
lemma normal_rewr_parallel_empty:
  "normal_rewr (Parallel []) = Empty"
  by (simp add: normal_rewr.simps)

text\<open>Every resource is equivalent to its normalisation\<close>
lemma res_term_equiv_normal_rewr:
  "x \<sim> normal_rewr x"
proof (induct x rule: normal_rewr.induct)
  case (1 x)
  then show ?case
  proof (cases "normalised x")
    case True
    then show ?thesis by (simp add: normal_rewr.simps)
  next
    case False
    then have "step x \<sim> normal_rewr (step x)"
      using 1 by simp
    then have "x \<sim> normal_rewr (step x)"
      using res_term_equiv.trans res_term_equiv_step by blast
    then show ?thesis
      by (simp add: normal_rewr.simps)
  qed
qed

text\<open>And, by transitivity, resource terms with equal normalisations are equivalent\<close>
lemma normal_rewr_imp_equiv:
  "normal_rewr x = normal_rewr y \<Longrightarrow> x \<sim> y"
  using res_term_equiv_normal_rewr[of x] res_term_equiv_normal_rewr[of y, symmetric]
  by (metis res_term_equiv.trans)

text\<open>Resource normalisation commutes with the resource map\<close>
lemma normal_rewr_map:
  "map_res_term f g (normal_rewr x) = normal_rewr (map_res_term f g x)"
proof (induct x rule: normal_rewr.induct)
  case (1 x)
  then show ?case
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: normalised_map normal_rewr.simps)
  next
    case False
    have "map_res_term f g (normal_rewr x) = map_res_term f g (normal_rewr (step x))"
      using False by (simp add: normal_rewr.simps)
    also have "... = normal_rewr (map_res_term f g (step x))"
      using 1 False by simp
    also have "... = normal_rewr (step (map_res_term f g x))"
      using step_map[of f g x] by simp
    also have "... = normal_rewr (map_res_term f g x)"
      using False by (simp add: normalised_map normal_rewr.simps)
    finally show ?thesis .
  qed
qed

text\<open>Normalisation is contained in transitive closure of the rewriting\<close>
lemma res_term_rewrite_tranclp_normal_rewr:
  "res_term_rewrite\<^sup>+\<^sup>+ x (normal_rewr x)"
proof (induct x rule: normal_rewr.induct)
  case (1 x)
  then show ?case
  proof (cases "normalised x")
    case True
    then show ?thesis
      by (simp add: tranclp.r_into_trancl)
  next
    case False
    then show ?thesis
      using 1 res_term_rewrite_contains_step tranclp_into_tranclp2 normal_rewr_step by metis
  qed
qed

subsection\<open>As Abstract Rewriting System\<close>

text\<open>
  The normalisation procedure described above implements an abstract rewriting system.
  Their theory allows us to prove that equality of normal forms is the same as term equivalence by
  reasoning about how equivalent terms are joinable by the rewriting.
\<close>

subsubsection\<open>Rewriting System Properties\<close>

text\<open>
  In the ARS mechanisation normal forms are terminal elements of the rewriting relation, while in
  our case they are fixpoints.
  To interface with that property, we use the irreflexive graph of @{const step}.
\<close>
definition step_irr :: "('a, 'b) res_term rel"
  where "step_irr = {(x,y). x \<noteq> y \<and> step x = y}"

lemma step_irr_inI:
  "x \<noteq> step x \<Longrightarrow> (x, step x) \<in> step_irr"
  by (simp add: step_irr_def)

text\<open>Graph of @{const normal_rewr} is in the transitive-reflexive closure of irreflexive step\<close>
lemma normal_rewr_in_step_rtrancl:
  "(x, normal_rewr x) \<in> step_irr\<^sup>*"
proof (induct x rule: normal_rewr.induct)
  case (1 x)
  then show ?case
  proof (cases "normalised x")
    case True
    then show ?thesis by simp
  next
    case False
    moreover have "(x, step x) \<in> step_irr"
      using False normalised_is_step_id by (fastforce simp add: step_irr_def)
    ultimately show ?thesis
      by (metis 1 converse_rtrancl_into_rtrancl normal_rewr.elims)
  qed
qed

text\<open>Normal forms of irreflexive step are exactly the normalised terms\<close>
lemma step_nf_is_normalised:
  "NF step_irr = {x. normalised x}"
proof safe
  fix x :: "('a, 'b) res_term"
  show "x \<in> NF step_irr \<Longrightarrow> normalised x"
    by (metis NF_not_suc normal_rewr_in_step_rtrancl normal_rewr_normalised)
  show "normalised x \<Longrightarrow> x \<in> NF step_irr"
    by (simp add: NF_I step_irr_def)
qed

text\<open>As such, every value of @{const normal_rewr} is a normal form of irreflexive step\<close>
lemma normal_rewr_NF [simp]:
  "normal_rewr x \<in> NF step_irr"
  by (simp add: normal_rewr_normalised step_nf_is_normalised)

text\<open>Terms related by reflexive-transitive step are equivalent\<close>
lemma step_rtrancl_equivalent:
  "(a,b) \<in> step_irr\<^sup>* \<Longrightarrow> a \<sim> b"
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case
    by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD fst_conv res_term_equiv.refl
        res_term_equiv.trans_both snd_conv res_term_equiv_step step_irr_def)
qed

text\<open>Irreflexive step is locally and strongly confluent because it's part of a function\<close>
lemma step_irr_locally_confluent:
  "WCR step_irr"
  unfolding step_irr_def by standard fastforce

lemma step_irr_strongly_confluent:
  "strongly_confluent step_irr"
  unfolding step_irr_def by standard fastforce

text\<open>Therefore it is Church-Rosser and has unique normal forms\<close>
lemma step_CR: "CR step_irr"
  using step_irr_strongly_confluent strong_confluence_imp_CR CR_imp_UNC CR_imp_UNF by blast
lemma step_UNC: "UNC step_irr"
  using step_CR CR_imp_UNC by blast
lemma step_UNF: "UNF step_irr"
  using step_CR CR_imp_UNF by blast

text\<open>Irreflexive step is strongly normalising because it decreases the well-founded rewriting bound\<close>
lemma step_SN:
  "SN step_irr"
  unfolding SN_def
  using SN_onI
proof
  fix x :: "('a, 'b) res_term" and f
  show "\<lbrakk>f 0 \<in> {x}; \<forall>i. (f i, f (Suc i)) \<in> step_irr\<rbrakk> \<Longrightarrow> False"
    \<comment> \<open>Irreflexivity of step is essential here to get the needed contradiction\<close>
    \<comment> \<open>Strong induction is needed because bound may decrease by more than 1\<close>
  proof (induct "res_term_rewrite_bound x" arbitrary: f x rule: less_induct)
    case less
    then show ?case
      using less(1)[where x = "step x" and f = "\<lambda>x. f (Suc x)"]
      by (metis (mono_tags, lifting) case_prodD mem_Collect_eq normalised_is_step_id
          res_term_rewrite_bound_step_decrease singleton_iff step_irr_def)
  qed
qed

text\<open>Normalisability relation of irreflexive step is exactly the graph of @{const normal_rewr}\<close>
lemma step_normalizability_normal_rewr:
  "step_irr\<^sup>! = {(x, y). y = normal_rewr x}"
proof safe
  fix a b :: "('a, 'b) res_term"
  assume "(a, b) \<in> step_irr\<^sup>!"
  then show "b = normal_rewr a"
    by (meson UNF_onE UNIV_I normal_rewr_NF normal_rewr_in_step_rtrancl normalizability_I step_UNF)
next
  fix a :: "('a, 'b) res_term"
  show "(a, normal_rewr a) \<in> step_irr\<^sup>!"
    using normal_rewr_NF normal_rewr_in_step_rtrancl by blast
qed

text\<open>The unique normal form, @{const the_NF} in the ARS language, is @{const normal_rewr}\<close>
lemma step_irr_the_NF [simp]:
  "the_NF step_irr x = normal_rewr x"
  by (meson UNF_onE UNIV_I normal_rewr_NF normal_rewr_in_step_rtrancl normalizability_I
      step_CR step_SN step_UNF the_NF)

text\<open>Terms related by reflexive-transitive step have the same normal form\<close>
lemma step_rtrancl_eq_normal:
  "(x,y) \<in> step_irr\<^sup>* \<Longrightarrow> normal_rewr x = normal_rewr y"
  by (metis normal_rewr_NF normal_rewr_in_step_rtrancl rtrancl_trans some_NF_UNF step_UNF)

subsubsection\<open>@{const NonD} Joinability\<close>

text\<open>Two @{const NonD} terms are joinable if their corresponding children are joinable\<close>

lemma step_rtrancl_nondL:
  "(x,u) \<in> step_irr\<^sup>* \<Longrightarrow> (NonD x y, NonD u y) \<in> step_irr\<^sup>*"
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case
    by (fastforce intro: rtrancl_into_rtrancl simp add: step_irr_def)
qed

lemma step_rtrancl_nondR:
  "\<lbrakk>(y,v) \<in> step_irr\<^sup>*; normalised x\<rbrakk> \<Longrightarrow> (NonD x y, NonD x v) \<in> step_irr\<^sup>*"
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case
    by (fastforce intro: rtrancl_into_rtrancl simp add: step_irr_def)
qed

lemma step_rtrancl_nond:
  "\<lbrakk>(x,u) \<in> step_irr\<^sup>*; normalised u; (y,v) \<in> step_irr\<^sup>*\<rbrakk> \<Longrightarrow> (NonD x y, NonD u v) \<in> step_irr\<^sup>*"
  using step_rtrancl_nondL step_rtrancl_nondR by (metis rtrancl_trans)

lemma step_join_apply_nondet:
  assumes "(x,u) \<in> step_irr\<^sup>\<down>" and "(y,v) \<in> step_irr\<^sup>\<down>" shows "(NonD x y, NonD u v) \<in> step_irr\<^sup>\<down>"
proof (rule joinI)
  have "(NonD x y, NonD (normal_rewr x) y) \<in> step_irr\<^sup>*"
    using step_rtrancl_nondL normal_rewr_in_step_rtrancl by metis
  also have "(NonD (normal_rewr x) y, NonD (normal_rewr x) (normal_rewr y)) \<in> step_irr\<^sup>*"
    using step_rtrancl_nondR normal_rewr_in_step_rtrancl normal_rewr_normalised by metis
  finally show "(NonD x y, NonD (normal_rewr x) (normal_rewr y)) \<in> step_irr\<^sup>*" .


  have "(NonD u v, NonD (normal_rewr u) v) \<in> step_irr\<^sup>*"
    using step_rtrancl_nondL normal_rewr_in_step_rtrancl by metis
  also have "(NonD (normal_rewr u) v, NonD (normal_rewr u) (normal_rewr v)) \<in> step_irr\<^sup>*"
    using step_rtrancl_nondR normal_rewr_in_step_rtrancl normal_rewr_normalised by metis
  also have
    "(NonD (normal_rewr u) (normal_rewr v), NonD (normal_rewr x) (normal_rewr y)) \<in> step_irr\<^sup>*"
    using assms joinD step_rtrancl_eq_normal rtrancl.rtrancl_refl by metis
  finally show "(NonD u v, NonD (normal_rewr x) (normal_rewr y)) \<in> step_irr\<^sup>*" .
qed

subsubsection\<open>@{const Executable} and @{const Repeatable} Joinability\<close>

text\<open>
  Two (repeatably) executable resource terms are joinable if their corresponding children are
  joinable
\<close>

lemma step_join_apply_executable:
  "\<lbrakk>(x,u) \<in> step_irr\<^sup>\<down>; (y,v) \<in> step_irr\<^sup>\<down>\<rbrakk> \<Longrightarrow> (Executable x y, Executable u v) \<in> step_irr\<^sup>\<down>"
  using joinI[where c = "Executable (normal_rewr x) (normal_rewr y)"] normal_rewr_executable
  by (metis (mono_tags, lifting) joinD normal_rewr_in_step_rtrancl step_rtrancl_eq_normal)

lemma step_join_apply_repeatable:
  "\<lbrakk>(x,u) \<in> step_irr\<^sup>\<down>; (y,v) \<in> step_irr\<^sup>\<down>\<rbrakk> \<Longrightarrow> (Repeatable x y, Repeatable u v) \<in> step_irr\<^sup>\<down>"
  using joinI[where c = "Repeatable (normal_rewr x) (normal_rewr y)"] normal_rewr_repeatable
  by (metis (mono_tags, lifting) joinD normal_rewr_in_step_rtrancl step_rtrancl_eq_normal)

subsubsection\<open>@{const Parallel} Joinability\<close>

text\<open>From two lists of joinable terms we can obtain a list of common destination terms\<close>
lemma list_all2_join:
  assumes "list_all2 (\<lambda>x y. (x, y) \<in> R\<^sup>\<down>) xs ys"
  obtains cs
    where "list_all2 (\<lambda>x c. (x, c) \<in> R\<^sup>*) xs cs"
      and "list_all2 (\<lambda>y c. (y, c) \<in> R\<^sup>*) ys cs"
  using assms by (induct rule: list_all2_induct ; blast)

text\<open>
  Every parallel resource term with at least two elements is related to a parallel resource term
  with the contents normalised
\<close>
lemma step_rtrancl_map_normal:
  "(Parallel xs, Parallel (map normal_rewr xs)) \<in> step_irr\<^sup>*"
proof (induct "sum_list (map res_term_rewrite_bound xs)" arbitrary: xs rule: less_induct)
  case less
  then show ?case
  proof (cases "list_all normalised xs")
    case True
    then show ?thesis
      by (metis Ball_set map_idI normalised_normal_rewr rtrancl.rtrancl_refl)
  next
    case False
    then have unnorm: "\<not> normalised (Parallel xs)"
      by simp

    have step: "step (Parallel xs) = Parallel (map step xs)"
      using False by (simp add: not_list_all)
    moreover have "Parallel xs \<noteq> Parallel (map step xs)"
      using unnorm by (metis calculation normalised_is_step_id)
    ultimately have "(Parallel xs, Parallel (map step xs)) \<in> step_irr"
      using step_irr_inI by metis
    moreover have "(Parallel (map step xs), Parallel (map normal_rewr (map step xs))) \<in> step_irr\<^sup>*"
      using less[of "map step xs"] False step unnorm
      by (smt (verit, ccfv_threshold) ab_semigroup_add_class.add_ac(1)
          add_mono_thms_linordered_field(3) dual_order.refl length_map not_less_eq plus_1_eq_Suc
          res_term_rewrite_bound.simps(5) res_term_rewrite_bound_step_decrease)
    moreover have "map normal_rewr (map step xs) = map normal_rewr xs"
      by (simp ; safe ; rule normal_rewr_step[symmetric])
    ultimately show ?thesis
      by (metis (no_types, lifting) converse_rtrancl_into_rtrancl)
  qed
qed

text\<open>Two lists of joinable terms have the same normal forms\<close>
lemma list_all2_join_normal_eq:
  "list_all2 (\<lambda>u v. (u, v) \<in> step_irr\<^sup>\<down>) xs ys \<Longrightarrow> map normal_rewr xs = map normal_rewr ys"
proof (induct rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case by simp (metis (no_types, lifting) joinD step_rtrancl_eq_normal)
qed

text\<open>Parallel resource terms whose contents are joinable are themselves joinable\<close>
lemma step_join_apply_parallel:
  assumes "list_all2 (\<lambda>u v. (u,v) \<in> step_irr\<^sup>\<down>) xs ys"
  shows "(Parallel xs, Parallel ys) \<in> step_irr\<^sup>\<down>"
  by (metis assms joinI list_all2_join_normal_eq step_rtrancl_map_normal)

text\<open>Removing all @{const Empty} terms absorbs the removal of one\<close>
lemma remove_all_empty_subsumes_remove_one:
  "remove_all_empty (remove_one_empty xs) = remove_all_empty xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a ; fastforce)
qed

text\<open>For any list with an @{const Empty} term, removing one strictly decreases their count\<close>
lemma remove_one_empty_count_if_decrease:
  "list_ex is_Empty xs \<Longrightarrow> count_if is_Empty (remove_one_empty xs) < count_if is_Empty xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a ; simp)
qed

text\<open>
  Removing all @{const Empty} terms from children of a @{const Parallel} term, that are already all
  normalised and none of which are nested @{const Parallel} terms, is related by transitive and
  reflexive closure of irreflexive step.
\<close>
lemma step_rtrancl_remove_all_empty:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> normalised x"
      and "\<not> list_ex is_Parallel xs"
    shows "(Parallel xs, Parallel (remove_all_empty xs)) \<in> step_irr\<^sup>*"
  using assms
proof (induct "count_if is_Empty xs" arbitrary: xs rule: less_induct)
  case less
  then show ?case
  proof (cases "list_ex is_Empty xs")
    case True
    then have a: "step (Parallel xs) = Parallel (remove_one_empty xs)"
      using less by (metis Bex_set step.simps(8))
    moreover have b: "count_if is_Empty (remove_one_empty xs) < count_if is_Empty xs"
      using True by (rule remove_one_empty_count_if_decrease)
    moreover have c: "\<And>x. x \<in> set (remove_one_empty xs) \<Longrightarrow> normalised x"
      using remove_one_empty_subset less(2) by fast
    moreover have "\<not> list_ex is_Parallel (remove_one_empty xs)"
      using remove_one_empty_subset less(3) not_list_ex
      by (metis (mono_tags, lifting) Ball_set)
    ultimately show ?thesis
      using less remove_all_empty_subsumes_remove_one
      by (metis converse_rtrancl_into_rtrancl step_irr_inI)
  next
    case False
    then show ?thesis
      by (simp add: joinI_right remove_all_empty_none)
  qed
qed

text\<open>
  After merging all @{const Parallel} elements of a list of normalised terms, there remain no more
  @{const Parallel} terms in it
\<close>
lemma merge_all_parallel_map_normal_result:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> normalised x"
    shows "\<not> list_ex is_Parallel (merge_all_parallel xs)"
  using assms merge_all_parallel_result normalised.simps(5) not_list_ex by blast

text\<open>
  For any list with a @{const Parallel} term, removing one strictly decreases their count if no
  element contains further nested @{const Parallel} terms within it
\<close>
lemma merge_one_parallel_count_if_decrease:
  assumes "list_ex is_Parallel xs"
      and "\<And>y ys. \<lbrakk>y \<in> set xs; y = Parallel ys\<rbrakk> \<Longrightarrow> \<not> list_ex is_Parallel ys"
    shows "count_if is_Parallel (merge_one_parallel xs) < count_if is_Parallel xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a) (simp_all add: count_if_0_conv)
qed

text\<open>
  Merging all @{const Parallel} terms absorbs the merging of one if no element contains further
  nested @{const Parallel} terms within it
\<close>
lemma merge_all_parallel_subsumes_merge_one:
  assumes "\<And>y ys. \<lbrakk>y \<in> set xs; y = Parallel ys\<rbrakk> \<Longrightarrow> \<not> list_ex is_Parallel ys"
    shows "merge_all_parallel (merge_one_parallel xs) = merge_all_parallel xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases a)
       case Empty then show ?thesis using Cons by simp
  next case Anything then show ?thesis using Cons by simp
  next case (Res x3) then show ?thesis using Cons by simp
  next case (Copyable x4) then show ?thesis using Cons by simp
  next
    case (Parallel x5)
    then show ?thesis
      using Cons by (simp add: merge_all_parallel_append merge_all_parallel_none)
  next case (NonD x61 x62) then show ?thesis using Cons by simp
  next case (Executable x71 x72) then show ?thesis using Cons by simp
  next case (Repeatable x81 x82) then show ?thesis using Cons by simp
  qed
qed

text\<open>Merging one @{const Parallel} term in a list of normalised terms keeps them normalised\<close>
lemma merge_one_parallel_preserve_normalised:
  "\<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> normalised x; a \<in> set (merge_one_parallel xs)\<rbrakk> \<Longrightarrow> normalised a"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp ; (presburger | metis normalised_parallel_children))
qed

text\<open>Merging all @{const Parallel} terms in a list of normalised terms keeps them normalised\<close>
lemma merge_all_parallel_preserve_normalised:
  "\<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> normalised x; a \<in> set (merge_all_parallel xs)\<rbrakk> \<Longrightarrow> normalised a"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp ; (presburger | metis normalised_parallel_children))
qed

text\<open>
  Merging all @{const Parallel} terms from children of a @{const Parallel} term, that are already
  all normalised, is related by transitive and reflexive closure of irreflexive step.
\<close>
lemma step_rtrancl_merge_all_parallel:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> normalised x"
  shows "(Parallel xs, Parallel (merge_all_parallel xs)) \<in> step_irr\<^sup>*"
  using assms
proof (induct "count_if is_Parallel xs" arbitrary: xs rule: less_induct)
  case less
  then show ?case
  proof (cases "list_ex is_Parallel xs")
    case False
    then show ?thesis
      using merge_all_parallel_none by (metis rtrancl.rtrancl_refl)
  next
    case True
    then have "step (Parallel xs) = Parallel (merge_one_parallel xs)"
      using less by (metis Bex_set step.simps(8))
    moreover have "\<And>x. x \<in> set (merge_one_parallel xs) \<Longrightarrow> normalised x"
      using merge_one_parallel_preserve_normalised less(2) by blast
    moreover have "count_if is_Parallel (merge_one_parallel xs) < count_if is_Parallel xs"
      using less(2) True merge_one_parallel_count_if_decrease normalised.simps(5) not_list_ex
      by blast
    ultimately show ?thesis
      using less merge_all_parallel_subsumes_merge_one
      by (metis converse_rtrancl_into_rtrancl normalised.simps(5) not_list_ex step_irr_inI)
  qed
qed

text\<open>Thus, there is a general rewriting path that @{const Parallel} terms take\<close>
lemma step_rtrancl_parallel:
  "(Parallel xs, Parallel (remove_all_empty (merge_all_parallel (map normal_rewr xs)))) \<in> step_irr\<^sup>*"
proof -
  have "(Parallel xs, Parallel (map normal_rewr xs)) \<in> step_irr\<^sup>*"
    by (rule step_rtrancl_map_normal)
  also have
    " (Parallel (map normal_rewr xs), Parallel (merge_all_parallel (map normal_rewr xs)))
    \<in> step_irr\<^sup>*"
    by (metis ex_map_conv normal_rewr_normalised step_rtrancl_merge_all_parallel)
  also have "(Parallel (merge_all_parallel (map normal_rewr xs)),
              Parallel (remove_all_empty (merge_all_parallel (map normal_rewr xs)))) \<in> step_irr\<^sup>*"
    using merge_all_parallel_map_normal_result merge_all_parallel_preserve_normalised
          normal_rewr_normalised step_rtrancl_remove_all_empty
    by (metis (mono_tags, lifting) imageE list.set_map)
  finally show ?thesis .
qed

subsubsection\<open>Other Helpful Lemmas\<close>

text\<open>For Church-Rosser strongly normalising rewriting systems, joinability is transitive\<close>
lemma CR_SN_join_trans:
  assumes "CR R"
      and "SN R"
      and "(x, y) \<in> R\<^sup>\<down>"
      and "(y, z) \<in> R\<^sup>\<down>"
    shows "(x, z) \<in> R\<^sup>\<down>"
proof -
  obtain a where a: "(x, a) \<in> R\<^sup>*" "(y, a) \<in> R\<^sup>*"
    using assms(3) joinE by metis
  then have "the_NF R y = the_NF R a"
    using assms(1,2) the_NF_steps by metis
  moreover obtain b where b: "(y, b) \<in> R\<^sup>*" "(z, b) \<in> R\<^sup>*"
    using assms(4) joinE by metis
  then have "the_NF R y = the_NF R b"
    using assms(1,2) the_NF_steps by metis
  ultimately show ?thesis
    using assms(1,2) a b by (meson CR_join_right_I joinI join_rtrancl_join)
qed

text\<open>More generally, for such systems, two joinable pairs can be bridged by a third\<close>
lemma CR_SN_join_both:
  "\<lbrakk>CR R; SN R; (a, b) \<in> R\<^sup>\<down>; (x, y) \<in> R\<^sup>\<down>; (b, y) \<in> R\<^sup>\<down>\<rbrakk> \<Longrightarrow> (a, x) \<in> R\<^sup>\<down>"
  by (meson CR_SN_join_trans join_sym)

text\<open>With irreflexive step being one such rewriting system\<close>
lemmas step_irr_join_trans = CR_SN_join_trans[OF step_CR step_SN]
lemmas step_irr_join_both = CR_SN_join_both[OF step_CR step_SN]

text\<open>@{const Parallel} term with no work left in children normalises in three possible ways\<close>
lemma normal_rewr_parallel_cases:
  assumes "\<forall>x. x \<in> set xs \<longrightarrow> normalised x"
      and "\<not> list_ex is_Empty xs"
      and "\<not> list_ex is_Parallel xs"
    obtains
      (Parallel) "normalised (Parallel xs)" and "normal_rewr (Parallel xs) = Parallel xs"
    | (Empty) "xs = []" and "normal_rewr (Parallel xs) = Empty"
    | (Single) a where "xs = [a]" and "normal_rewr (Parallel xs) = a"
proof (cases xs rule: remdups_adj.cases)
  case 1
  then show ?thesis using that normal_rewr_parallel_empty by fastforce
next
  case (2 x)
  then have "normal_rewr (Parallel [x]) = step (Parallel [x])"
    using assms by (subst normal_rewr.simps) simp
  then show ?thesis
    using that assms 2 by simp
next
  case (3 x y xs)
  then show ?thesis
    using assms that
    by (metis normal_rewr.simps normalised_parallelise parallelise.simps(3))
qed

text\<open>
  For a list of already normalised terms with no @{const Empty} or @{const Parallel} terms, the
  normalisation procedure acts like @{const parallel_parts} followed by @{const parallelise}.
  It only does simplifications related to the number of elements.
\<close>
lemma normal_rewr_parallelise:
  assumes "\<forall>x. x \<in> set xs \<longrightarrow> normalised x"
      and "\<not> list_ex is_Empty xs"
      and "\<not> list_ex is_Parallel xs"
    shows "normal_rewr (Parallel xs) = parallelise (parallel_parts (Parallel xs))"
proof -
  show ?thesis
    using assms
  proof (cases rule: normal_rewr_parallel_cases)
    case Parallel
    then show ?thesis
      using parallel_parts_no_empty_parallel assms
      by (metis list_obtain_2 normalised.simps(5) parallelise.simps(3))
  next case Empty then show ?thesis by simp
  next case (Single a) then show ?thesis using assms by (cases a ; simp)
  qed
qed

text\<open>Removing all @{const Empty} terms has no effect on number of @{const Parallel} terms\<close>
lemma parallel_remove_all_empty:
  "list_ex is_Parallel (remove_all_empty xs) = list_ex is_Parallel xs"
proof (induct xs)
     case Nil then show ?case by simp
next case (Cons a xs) then show ?case by (cases a) simp_all
qed

text\<open>
  Removing all @{const Empty} terms is idempotent because there are no @{const Empty} terms to
  remove on the second pass
\<close>
lemma remove_all_empty_idempotent:
  shows "remove_all_empty (remove_all_empty xs) = remove_all_empty xs"
  by (induct xs) simp_all

text\<open>
  Every @{const Parallel} term rewrites to the parallelisation of normalised children with all
  @{const Empty} terms removed and all @{const Parallel} terms merged
\<close>
lemma normal_rewr_to_parallelise:
  " normal_rewr (Parallel xs)
  = parallelise (remove_all_empty (merge_all_parallel (map normal_rewr xs)))"
proof -
  have
    " normal_rewr (Parallel xs)
    = normal_rewr (Parallel (remove_all_empty (merge_all_parallel (map normal_rewr xs))))"
    using step_rtrancl_parallel step_rtrancl_eq_normal by metis
  also have " ...
    = parallelise (parallel_parts (Parallel
        (remove_all_empty (merge_all_parallel (map normal_rewr xs)))))"
    using merge_all_parallel_preserve_normalised normal_rewr_parallelise parallel_remove_all_empty
    using merge_all_parallel_map_normal_result remove_all_empty_result normal_rewr_normalised
    by (smt (verit, ccfv_threshold) imageE list.set_map remove_all_empty_subset)
  also have "... = parallelise (remove_all_empty (merge_all_parallel (map normal_rewr xs)))"
    using parallel_parts_no_empty_parallel parallel_remove_all_empty
    using merge_all_parallel_map_normal_result remove_all_empty_result normal_rewr_normalised
    by (metis (mono_tags, lifting) imageE list.set_map)
  finally show ?thesis .
qed

text\<open>
  @{const Parallel} term that normalises to @{const Empty} must have had no children left after
  normalising them, merging @{const Parallel} terms and removing @{const Empty} terms
\<close>
lemma normal_rewr_to_empty:
  assumes "normal_rewr (Parallel xs) = Empty"
    shows "remove_all_empty (merge_all_parallel (map normal_rewr xs)) = []"
  using assms normal_rewr_to_parallelise parallelise_to_empty_eq remove_all_empty_result
  by (metis list_ex_simps(1) res_term.disc(19))

text\<open>
  @{const Parallel} term that normalises to another @{const Parallel} must have had those children
  left after normalising its own, merging @{const Parallel} terms and removing @{const Empty} terms
\<close>
lemma normal_rewr_to_parallel:
  assumes "normal_rewr (Parallel xs) = Parallel ys"
    shows "remove_all_empty (merge_all_parallel (map normal_rewr xs)) = remove_all_empty ys"
proof -
  have "\<not> list_ex is_Parallel (remove_all_empty (merge_all_parallel (map normal_rewr xs)))"
    using merge_all_parallel_map_normal_result normal_rewr_normalised parallel_remove_all_empty
    by (metis (mono_tags, lifting) imageE list.set_map)
  then have "remove_all_empty (merge_all_parallel (map normal_rewr xs)) = ys"
    by (metis assms normal_rewr_to_parallelise normal_rewr_normalised normalised_parallel_parts_eq
        parallel_parts_no_empty_parallel parallel_parts_parallelise_eq remove_all_empty_result)
  then show ?thesis
    using assms remove_all_empty_idempotent by metis
qed

text\<open>
  @{const Parallel} that normalises to anything else must have had that as the only term left after
  normalising its own, merging @{const Parallel} terms and removing @{const Empty} terms
\<close>
lemma normal_rewr_to_other:
  assumes "normal_rewr (Parallel xs) = a"
      and "\<not> is_Empty a"
      and "\<not> is_Parallel a"
    shows "remove_all_empty (merge_all_parallel (map normal_rewr xs)) = [a]"
  using assms by (simp add: normal_rewr_to_parallelise parallelise_to_single_eq)

subsubsection\<open>Equivalent Term Joinability\<close>

text\<open>Equivalent resource terms are joinable by irreflexive step\<close>
lemma res_term_equiv_joinable:
  "x \<sim> y \<Longrightarrow> (x, y) \<in> step_irr\<^sup>\<down>"
proof (induct rule: res_term_equiv.induct)
     case empty then show ?case by blast
next case anything then show ?case by blast
next case (res x) then show ?case by blast
next case (copyable x) then show ?case by blast
next
  case nil
  then show ?case
    by (metis joinI_left normal_rewr_in_step_rtrancl normal_rewr_parallel_empty)
next
  case (singleton a)
  then show ?case
  proof (induct "res_term_rewrite_bound a" arbitrary: a rule: less_induct)
    case less
      then show ?case
    proof (cases "normalised a")
      case True
      then show ?thesis
      proof (cases a)
        case Empty
        moreover have "(Parallel [Empty], Empty) \<in> step_irr\<^sup>*"
        proof -
          have "step (Parallel [Empty]) = Parallel []"
            by simp
          then show ?thesis
            using normal_rewr_in_step_rtrancl normal_rewr_parallel_empty
            by (metis converse_rtrancl_into_rtrancl step_irr_inI)
        qed
        ultimately show ?thesis
          using joinI_left by simp
      next
        case Anything
        then have "step (Parallel [a]) = a"
          by simp
        then show ?thesis
          using step_irr_inI parallel_neq_single r_into_rtrancl joinI_left by metis
      next
        case (Res x3)
        then have "step (Parallel [a]) = a"
          by simp
        then show ?thesis
          using step_irr_inI parallel_neq_single r_into_rtrancl joinI_left by metis
      next
        case (Copyable x4)
        then have "step (Parallel [a]) = a"
          using True by simp
        then show ?thesis
          using step_irr_inI parallel_neq_single r_into_rtrancl joinI_left by metis
      next
        case (Parallel x5)
        then have "step (Parallel [Parallel x5]) = Parallel x5"
          using True by simp
        then show ?thesis
          using step_irr_inI parallel_neq_single r_into_rtrancl joinI_left Parallel by metis
      next
        case (NonD x61 x62)
        then have "step (Parallel [a]) = a"
          using True by simp
        then show ?thesis
          using step_irr_inI parallel_neq_single r_into_rtrancl joinI_left by metis
      next
        case (Executable x71 x72)
        then have "step (Parallel [a]) = a"
          using True by simp
        then show ?thesis
          using step_irr_inI parallel_neq_single r_into_rtrancl joinI_left by metis
      next
        case (Repeatable x71 x72)
        then have "step (Parallel [a]) = a"
          using True by simp
        then show ?thesis
          using step_irr_inI parallel_neq_single r_into_rtrancl joinI_left by metis
      qed
    next
      case False
      then have "step (Parallel [a]) = Parallel [step a]"
        by simp
      moreover have "res_term_rewrite_bound (step a) < res_term_rewrite_bound a"
        using res_term_rewrite_bound_step_decrease False by blast
      ultimately show ?thesis
        using less normal_rewr_in_step_rtrancl step_irr_join_trans step_normalised
        by (metis joinI normal_rewr.elims)
    qed
  qed
next
  case (merge x y z)
  have
    "( Parallel (x @ y @ z)
     ,  Parallel (remove_all_empty (merge_all_parallel (map normal_rewr (x @ y @ z))))
     ) \<in> step_irr\<^sup>*"
    using step_rtrancl_parallel .
  also have
    "( Parallel (remove_all_empty (merge_all_parallel (map normal_rewr (x @ y @ z))))
      , Parallel (remove_all_empty (merge_all_parallel (map normal_rewr (x @ [Parallel y] @ z))))
     ) \<in> step_irr\<^sup>*"
  proof (cases "normal_rewr (Parallel y)")
    case Empty
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_empty)
  next
    case Anything
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_other)
  next
    case (Res x3)
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_other)
  next
    case (Copyable x4)
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_other)
  next
    case (Parallel x5)
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_parallel)
  next
    case (NonD x61 x62)
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_other)
  next
    case (Executable x71 x72)
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_other)
  next
    case (Repeatable x81 x82)
    then show ?thesis
      by (simp add: merge_all_parallel_append remove_all_empty_append normal_rewr_to_other)
  qed
  finally show ?case
    using step_rtrancl_parallel by blast
next
  case (parallel xs ys)
  then show ?case
    by (simp add: list_all2_mono step_join_apply_parallel)
next
  case (nondet x y u v)
  then show ?case using step_join_apply_nondet by blast
next
  case (executable x y u v)
  then show ?case using step_join_apply_executable by blast
next
  case (repeatable x y u v)
  then show ?case using step_join_apply_repeatable by blast
next
  case (sym x y)
  then show ?case by (simp add: join_sym)
next
  case (trans x y z)
  then show ?case by (meson joinE CR_join_right_I joinI join_rtrancl_join step_CR)
qed

text\<open>Therefore this rewriting-based normalisation brings equivalent terms to the same normal form\<close>
lemma res_term_equiv_imp_normal_rewr:
  assumes "x \<sim> y" shows "normal_rewr x = normal_rewr y"
proof (rule join_NF_imp_eq)
  have "normal_rewr x \<sim> x"
    using res_term_equiv_normal_rewr res_term_equiv.sym by blast
  moreover have "y \<sim> normal_rewr y"
    by (rule res_term_equiv_normal_rewr)
  ultimately have "normal_rewr x \<sim> normal_rewr y"
    using assms by (rule res_term_equiv.trans_both)
  then show "(normal_rewr x, normal_rewr y) \<in> step_irr\<^sup>\<down>"
    by (rule res_term_equiv_joinable)

  show "normal_rewr x \<in> NF step_irr"
   and "normal_rewr y \<in> NF step_irr"
    by (rule normal_rewr_NF)+
qed

text\<open>And resource term equivalence is equal to having equal normal forms\<close>
theorem res_term_equiv_is_normal_rewr:
  "x \<sim> y = (normal_rewr x = normal_rewr y)"
  using res_term_equiv_imp_normal_rewr normal_rewr_imp_equiv by standard

subsection\<open>Term Equivalence as Rewriting Closure\<close>

text\<open>
  We can now show that @{const res_term_equiv} is the equivalence closure of
  @{const res_term_rewrite}.

  An equivalence closure is a reflexive, transitive and symmetric closure.
  In our case, the rewriting is already reflexive, so we only need to verify the symmetric and
  transitive closure.

  As such, the core difficulty in this section is to prove the following equality:
  @{term "x \<sim> y = (symclp res_term_rewrite)\<^sup>+\<^sup>+ x y"}
\<close>

text\<open>One direction is simpler, because rewriting implies equivalence\<close>
lemma res_term_rewrite_equivclp_imp_equiv:
  "(symclp res_term_rewrite)\<^sup>+\<^sup>+ x y \<Longrightarrow> x \<sim> y"
proof (induct rule: tranclp.induct)
  case (r_into_trancl a b)
  then show ?case
    by (metis symclp_def res_term_rewrite_imp_equiv res_term_equiv.sym)
next
  case (trancl_into_trancl a b c)
  then have "b \<sim> c"
    by (metis symclp_def res_term_rewrite_imp_equiv res_term_equiv.sym)
  then show ?case
    by (metis trancl_into_trancl(2) res_term_equiv.trans)
qed

text\<open>Trying to prove the other direction purely through facts about the rewriting itself fails\<close>
lemma
  "x \<sim> y \<Longrightarrow> (symclp res_term_rewrite)\<^sup>+\<^sup>+ x y"
proof (induct x y rule: res_term_equiv.induct)
     case empty then show ?case by (simp add: tranclp.r_into_trancl)
next case anything then show ?case by (simp add: tranclp.r_into_trancl)
next case (res x) then show ?case by (simp add: tranclp.r_into_trancl)
next case (copyable x) then show ?case by (simp add: tranclp.r_into_trancl)
next
  case nil
  then show ?case
    by (simp add: res_term_rewrite.nil tranclp.r_into_trancl)
next
  case (singleton a)
  then show ?case
    by (simp add: res_term_rewrite.singleton tranclp.r_into_trancl)
next
  case (merge x y z)
  then show ?case
    by (meson res_term_rewrite.merge symclp_def tranclp.r_into_trancl)
next
  case (sym x y)
  then show ?case
    by (metis rtranclpD rtranclp_symclp_sym tranclp_into_rtranclp)
next case (trans x y z) then show ?case by simp
next
  case (parallel xs ys)
  then show ?case
    \<comment> \<open>While we do know that corresponding parallel terms are related, the rewrite rule
        @{thm res_term_rewrite.parallel} needs all rewrites to be in a uniform direction.
        Such an issue arises with all remaining cases.\<close>
oops

text\<open>But, we can take advantage of the normalisation procedure to prove it\<close>
lemma res_term_rewrite_equiv_imp_equivclp:
  assumes "x \<sim> y"
  shows "(symclp res_term_rewrite)\<^sup>+\<^sup>+ x y"
proof -
  have "normal_rewr x = normal_rewr y"
    using assms res_term_equiv_is_normal_rewr by metis
  then have "(symclp res_term_rewrite)\<^sup>+\<^sup>+ (normal_rewr x) (normal_rewr y)"
    by (simp add: tranclp.r_into_trancl)
  moreover have "(symclp res_term_rewrite)\<^sup>+\<^sup>+ x (normal_rewr x)"
    using res_term_rewrite_tranclp_normal_rewr symclp_def res_term_rewrite.refl
    by (metis equivclp_def rev_predicate2D rtranclp_into_tranclp2 rtranlcp_le_equivclp
        tranclp_into_rtranclp)
  moreover have "(symclp res_term_rewrite)\<^sup>+\<^sup>+ (normal_rewr y) y"
    using res_term_rewrite_tranclp_normal_rewr symclp_def res_term_rewrite.refl
    by (metis conversepD equivclp_def rev_predicate2D rtranclpD rtranlcp_le_equivclp
        symp_conv_conversep_eq symp_rtranclp_symclp tranclp.r_into_trancl tranclp_into_rtranclp)
  ultimately show ?thesis
    by simp
qed

text\<open>Thus, we prove that resource term equivalence is the equivalence closure of the rewriting\<close>
lemma res_term_equiv_is_rewrite_closure:
  "(\<sim>) = equivclp res_term_rewrite"
proof -
  have "equivclp res_term_rewrite x y = (symclp res_term_rewrite)\<^sup>+\<^sup>+ x y"
    for x y :: "('a, 'b) res_term"
    by (metis equivclp_def res_term_equiv.refl res_term_rewrite_equiv_imp_equivclp rtranclpD
        tranclp_into_rtranclp)
  then have "x \<sim> y = equivclp res_term_rewrite x y"
    for x y :: "('a, 'b) res_term"
    using res_term_rewrite_equivclp_imp_equiv res_term_rewrite_equiv_imp_equivclp by metis
  then show ?thesis
    by blast
qed


end
