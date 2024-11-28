theory ResNormalForm
  imports
    ResTerm
    Util
begin

section\<open>Resource Term Normal Form\<close>

text\<open>
  A resource term is normalised when:
  \<^item> It is a leaf node, or
  \<^item> It is an internal node with all children normalised and additionally:
    \<^item> If it is a parallel resource then none of its children are @{const Empty} or @{const Parallel}
      and it has more than one child.
\<close>
primrec normalised :: "('a, 'b) res_term \<Rightarrow> bool"
  where
    "normalised Empty = True"
  | "normalised Anything = True"
  | "normalised (Res x) = True"
  | "normalised (Copyable x) = True"
  | "normalised (Parallel xs) =
    ( list_all normalised xs \<and>
      list_all (\<lambda>x. \<not> is_Empty x) xs \<and> list_all (\<lambda>x. \<not> is_Parallel x) xs \<and>
      1 < length xs)"
  | "normalised (NonD x y) = (normalised x \<and> normalised y)"
  | "normalised (Executable x y) = (normalised x \<and> normalised y)"
  | "normalised (Repeatable x y) = (normalised x \<and> normalised y)"

text\<open>The fact that a term is not normalised can be split into cases\<close>
lemma not_normalised_cases:
  assumes "\<not> normalised x"
  obtains
    (Parallel_Child) xs where "x = Parallel xs" and "list_ex (\<lambda>x. \<not> normalised x) xs"
  | (Parallel_Empty) xs where "x = Parallel xs" and "list_ex is_Empty xs"
  | (Parallel_Par) xs where "x = Parallel xs" and "list_ex is_Parallel xs"
  | (Parallel_Nil) "x = Parallel []"
  | (Parallel_Singleton) a where "x = Parallel [a]"
  | (NonD_L) a b where "x = NonD a b" and "\<not> normalised a"
  | (NonD_R) a b where "x = NonD a b" and "\<not> normalised b"
  | (Executable_L) a b where "x = Executable a b" and "\<not> normalised a"
  | (Executable_R) a b where "x = Executable a b" and "\<not> normalised b"
  | (Repeatable_L) a b where "x = Repeatable a b" and "\<not> normalised a"
  | (Repeatable_R) a b where "x = Repeatable a b" and "\<not> normalised b"
proof (cases x)
     case Empty then show ?thesis using assms by simp
next case Anything then show ?thesis using assms by simp
next case (Res x) then show ?thesis using assms by simp
next case (Copyable x) then show ?thesis using assms by simp
next
  case (Parallel xs)
  then consider
      "list_ex (\<lambda>x. \<not> normalised x) xs"
    | "list_ex is_Empty xs"
    | "list_ex is_Parallel xs"
    | "length xs \<le> Suc 0"
    using assms not_list_ex by fastforce
  then show ?thesis
    using that(1-5) Parallel
    by (metis (no_types, lifting) le_Suc_eq le_zero_eq length_0_conv length_Suc_conv)
next
  case (NonD x y)
  then show ?thesis
    using assms that(6,7) by (cases "normalised x") simp_all
next
  case (Executable x y)
  then show ?thesis
    using assms that(8,9) by (cases "normalised x") simp_all
next
  case (Repeatable x y)
  then show ?thesis
    using assms that(10,11) by (cases "normalised x") simp_all
qed

text\<open>
  When a @{const Parallel} term is not normalised then it can be useful to obtain the first term in
  it that is @{const Empty}, @{const Parallel} or not normalised.
\<close>
lemma obtain_first_parallel:
  assumes "list_ex is_Parallel xs"
  obtains a b c where "xs = a @ [Parallel b] @ c" and "list_all (\<lambda>x. \<not> is_Parallel x) a"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by simp (metis (mono_tags, lifting) append_eq_Cons_conv is_Parallel_def list.pred_inject)
qed
lemma obtain_first_empty:
  assumes "list_ex is_Empty xs"
  obtains a b c where "xs = a @ [Empty] @ c" and "list_all (\<lambda>x. \<not> is_Empty x) a"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by simp (metis (mono_tags, lifting) append_eq_Cons_conv is_Empty_def list.pred_inject)
qed
lemma obtain_first_unnormalised:
  assumes "list_ex (\<lambda>x. \<not> normalised x) xs"
  obtains a b c where "xs = a @ [b] @ c" and "list_all normalised a" and "\<not> normalised b"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by simp (metis (mono_tags, lifting) append_eq_Cons_conv list.pred_inject)
qed

text\<open>Mapping functions over a resource term does not change whether it is normalised\<close>
lemma normalised_map:
  "normalised (map_res_term f g x) = normalised x"
  by (induct x) (simp_all add: Ball_set[symmetric])

text\<open>If a @{const Parallel} term is normalised then so are all its children\<close>
lemma normalised_parallel_children:
  "\<lbrakk>normalised (Parallel xs); x \<in> set xs\<rbrakk> \<Longrightarrow> normalised x"
  by (induct xs rule: remdups_adj.induct ; fastforce)

text\<open>Normalised @{const Parallel} term has as parallel parts exactly its direct children\<close>
lemma normalised_parallel_parts_eq:
  "normalised (Parallel xs) \<Longrightarrow> parallel_parts (Parallel xs) = xs"
  by (induct xs rule: induct_list012 ; fastforce)

text\<open>
  Parallelising a list of normalised terms with no nested @{const Empty} or @{const Parallel} terms
  gives normalised result.
\<close>
lemma normalised_parallelise:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> normalised x"
      and "\<not> list_ex is_Empty xs"
      and "\<not> list_ex is_Parallel xs"
    shows "normalised (parallelise xs)"
proof (cases xs rule: parallelise.cases)
  case 1
  then show ?thesis
    by simp
next
  case (2 x)
  then show ?thesis
    using assms(1) by simp
next
  case (3 v vb vc)
  then show ?thesis
    using assms by (simp add: not_list_ex Ball_set[symmetric])
qed

end