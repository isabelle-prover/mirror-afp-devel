theory ResTerm
  imports Main
begin

section\<open>Resource Terms\<close>

text\<open>
  Resource terms describe resources with atoms drawn from two types, linear and copyable, combined
  in a number of ways:
  \<^item> Parallel resources represent their simultaneous presence,
  \<^item> Non-deterministic resource represent exactly one of two options,
  \<^item> Executable resources represent a single potential execution of a process transforming one
    resource into another,
  \<^item> Repeatably executable resources represent an unlimited amount of such potential executions.

  We define two distinguished resources on top of the atoms:
  \<^item> Empty, to represent the absence of a resource and serve as the unit for parallel combination,
  \<^item> Anything, to represent a resource about which we have no information.
\<close>
datatype (discs_sels) ('a, 'b) res_term =
  Res 'a
    \<comment> \<open>Linear resource atom\<close>
  | Copyable 'b
    \<comment> \<open>Copyable resource atom\<close>
  | is_Empty: Empty
    \<comment> \<open>The absence of a resource\<close>
  | is_Anything: Anything
    \<comment> \<open>Resource about which we know nothing\<close>
  | Parallel "('a, 'b) res_term list"
    \<comment> \<open>Parallel combination\<close>
  | NonD "('a, 'b) res_term" "('a, 'b) res_term"
    \<comment> \<open>Non-deterministic combination\<close>
  | Executable "('a, 'b) res_term" "('a, 'b) res_term"
    \<comment> \<open>Executable resource\<close>
  | Repeatable "('a, 'b) res_term" "('a, 'b) res_term"
    \<comment> \<open>Repeatably executable resource\<close>

text\<open>Every child of @{const Parallel} is smaller than it\<close>
lemma parallel_child_smaller:
  "x \<in> set xs \<Longrightarrow> size_res_term f g x < size_res_term f g (Parallel xs)"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by simp (metis add_Suc_right less_SucI less_add_Suc1 trans_less_add2)
qed

text\<open>No singleton @{const Parallel} is equal to its own child, because the child has to be smaller\<close>
lemma parallel_neq_single [simp]:
  "Parallel [a] \<noteq> a"
proof -
  have "\<And>f g. size_res_term f g a < size_res_term f g (Parallel [a])"
    using parallel_child_smaller by simp
  then show ?thesis
    by fastforce
qed

subsection\<open>Resource Term Equivalence\<close>

text\<open>
  Some resource terms are different descriptions of the same situation.
  We express this by relating resource terms as follows:
  \<^item> @{term "Parallel []"} with @{term "Empty"}
  \<^item> @{term "Parallel [x]"} with @{term "x"}
  \<^item> @{term "Parallel (xs @ [Parallel ys] @ zs)"} with @{term "Parallel (xs @ ys @ zs)"}

  We extend this with the reflexive base cases, recursive cases and symmetric-transitive closure.
  As a result, we get an equivalence relation on resource terms, which we will later use to quotient
  the terms and form a type of resources.
\<close>
inductive res_term_equiv :: "('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term \<Rightarrow> bool" (infix "\<sim>" 100)
  where
    nil: "Parallel [] \<sim> Empty"
  | singleton: "Parallel [a] \<sim> a"
  | merge: "Parallel (x @ [Parallel y] @ z) \<sim> Parallel (x @ y @ z)"
  | empty: "Empty \<sim> Empty"
  | anything: "Anything \<sim> Anything"
  | res: "Res x \<sim> Res x"
  | copyable: "Copyable x \<sim> Copyable x"
  | parallel: "list_all2 (\<sim>) xs ys \<Longrightarrow> Parallel xs \<sim> Parallel ys"
  | nondet: "\<lbrakk>x \<sim> y; u \<sim> v\<rbrakk> \<Longrightarrow> NonD x u \<sim> NonD y v"
  | executable: "\<lbrakk>x \<sim> y; u \<sim> v\<rbrakk> \<Longrightarrow> Executable x u \<sim> Executable y v"
  | repeatable: "\<lbrakk>x \<sim> y; u \<sim> v\<rbrakk> \<Longrightarrow> Repeatable x u \<sim> Repeatable y v"
  | sym [sym]: "x \<sim> y \<Longrightarrow> y \<sim> x"
  | trans [trans]: "\<lbrakk>x \<sim> y; y \<sim> z\<rbrakk> \<Longrightarrow> x \<sim> z"

text\<open>Add some of the rules for the simplifier\<close>
lemmas [simp] =
  nil nil[symmetric]
  singleton singleton[symmetric]

text\<open>Constrain all these rules to the resource term equivalence namespace\<close>
hide_fact (open) empty anything res copyable nil singleton merge parallel nondet executable
  repeatable sym trans

text\<open>Next we derive a handful of rules for the equivalence, placing them in its namespace\<close>
setup \<open>Sign.mandatory_path "res_term_equiv"\<close>

text\<open>It can be shown to be reflexive\<close>
lemma refl [simp]:
  "a \<sim> a"
  by (induct a ; rule res_term_equiv.intros ; simp add: list_all2_same)

lemma reflI:
  "a = b \<Longrightarrow> a \<sim> b"
  by simp

lemma equivp [simp]:
  "equivp res_term_equiv"
  by (simp add: equivpI reflpI res_term_equiv.sym res_term_equiv.trans sympI transpI)

text\<open>Parallel resource terms can be related by splitting them into parts\<close>
lemma decompose:
  assumes "Parallel x1 \<sim> Parallel y1"
      and "Parallel x2 \<sim> Parallel y2"
    shows "Parallel (x1 @ x2) \<sim> Parallel (y1 @ y2)"
proof -
  have "Parallel [Parallel x1, Parallel x2] \<sim> Parallel [Parallel y1, Parallel y2]"
    by (simp add: assms res_term_equiv.parallel)
  then have "Parallel (Parallel x1 # x2) \<sim> Parallel (Parallel y1 # y2)"
    using res_term_equiv.merge[of "[Parallel x1]" x2 Nil, simplified]
          res_term_equiv.merge[of "[Parallel y1]" y2 Nil, simplified]
    by (meson res_term_equiv.sym res_term_equiv.trans)
  then show "Parallel (x1 @ x2) \<sim> Parallel (y1 @ y2)"
    using res_term_equiv.merge[of Nil y1 y2, simplified]
          res_term_equiv.merge[of Nil x1 x2, simplified]
    by (meson res_term_equiv.sym res_term_equiv.trans)
qed

text\<open>We can drop a unit from any parallel resource term\<close>
lemma drop:
  "Parallel (x @ [Empty] @ y) \<sim> Parallel (x @ y)"
proof -
  have "Parallel [Empty] \<sim> Parallel [Parallel []]"
    using res_term_equiv.nil res_term_equiv.sym res_term_equiv.trans res_term_equiv.singleton
    by blast
  then have "Parallel (x @ [Empty] @ y) \<sim> Parallel (x @ [Parallel []] @ y)"
    using res_term_equiv.decompose[OF res_term_equiv.refl, of "[Empty] @ y" "[Parallel []] @ y" x]
          res_term_equiv.decompose[OF _ res_term_equiv.refl, of "[Empty]" "[Parallel []]" y]
    by blast
  then show ?thesis
    using res_term_equiv.merge res_term_equiv.trans by fastforce
qed

text\<open>Equivalent resource terms remain equivalent wrapped in a parallel\<close>
lemma singleton_both:
  "x \<sim> y \<Longrightarrow> Parallel [x] \<sim> Parallel [y]"
  by (simp add: res_term_equiv.parallel)

text\<open>We can reduce a resource term equivalence given equivalences for both sides\<close>
lemma trans_both:
  "\<lbrakk>a \<sim> x; y \<sim> b; x \<sim> y\<rbrakk> \<Longrightarrow> a \<sim> b"
  by (rule res_term_equiv.trans[OF res_term_equiv.trans])

setup \<open>Sign.parent_path\<close>

experiment begin
lemma "Parallel [Parallel [], Empty] \<sim> Empty"
proof -
  have "Parallel [Parallel [], Empty] \<sim> Parallel [Parallel []]"
    using res_term_equiv.drop[of "[Parallel []]"] by simp
  also have "... \<sim> Parallel []" by simp
  also have "... \<sim> Empty" by simp
  finally show ?thesis .
qed
end

text\<open>Inserting equivalent terms anywhere in equivalent parallel terms preserves the equivalence\<close>
lemma res_term_parallel_insert:
  assumes "Parallel x \<sim> Parallel y"
      and "Parallel u \<sim> Parallel v"
      and "a \<sim> b"
    shows "Parallel (x @ [a] @ u) \<sim> Parallel (y @ [b] @ v)"
  by (meson assms res_term_equiv.decompose res_term_equiv.singleton_both)
text\<open>With inserting at the start being just a special case\<close>
lemma res_term_parallel_cons:
  assumes "Parallel x \<sim> Parallel y"
      and "a \<sim> b"
    shows "Parallel (a # x) \<sim> Parallel (b # y)"
  using res_term_parallel_insert[OF res_term_equiv.refl assms, of Nil] by simp

text\<open>@{const Empty} is a unit for binary @{const Parallel}\<close>
lemma res_term_parallel_emptyR [simp]: "Parallel [x, Empty] \<sim> x"
  using res_term_equiv.drop[of "[x]" Nil] by (simp add: res_term_equiv.trans)
lemma res_term_parallel_emptyL [simp]: "Parallel [Empty, x] \<sim> x"
  using res_term_equiv.drop[of Nil "[x]"] by (simp add: res_term_equiv.trans)

text\<open>Term equivalence is preserved by parallel on either side\<close>
lemma res_term_equiv_parallel [simp]:
  "x \<sim> y \<Longrightarrow> x \<sim> Parallel [y]"
  using res_term_equiv.singleton res_term_equiv.sym res_term_equiv.trans by blast
lemmas [simp] = res_term_equiv_parallel[symmetric]

text\<open>Resource term map preserves equivalence:\<close>
lemma map_res_term_preserves_equiv [simp]:
  "x \<sim> y \<Longrightarrow> map_res_term f g x \<sim> map_res_term f g y"
proof (induct rule: res_term_equiv.induct)
     case empty then show ?case by simp
next case anything then show ?case by simp
next case (res x) then show ?case by simp
next case (copyable x) then show ?case by simp
next case nil then show ?case by simp
next case (singleton a) then show ?case by simp
next case (merge x y z) then show ?case using res_term_equiv.merge by fastforce
next
  case (parallel xs ys)
  then show ?case
    by (simp add: list_all2_conv_all_nth res_term_equiv.parallel)
next case (nondet x y u v) then show ?case by (simp add: res_term_equiv.nondet)
next case (executable x y u v) then show ?case by (simp add: res_term_equiv.executable)
next case (repeatable x y u v) then show ?case by (simp add: res_term_equiv.repeatable)
next case (sym x y) then show ?case by (simp add: res_term_equiv.sym)
next case (trans x y z) then show ?case using res_term_equiv.trans by blast
qed

text\<open>
  The other direction is not true in general, because they may be new equivalences created by
  mapping different atoms to the same one.
  However, the counter-example proof requires a decision procedure for the equivalence to prove
  that two distinct atoms are not equivalent terms.
  As such, we delay it until normalisation for the terms is established.
\<close>

subsection\<open>Parallel Parts\<close>

text\<open>
  Parallel resources often arise in processes, because they describe the frequent situation of
  having multiple resources be simultaneously present.
  With resource terms, the way this situation is expressed can get complex.
  To simplify it, we define a function to extract the list of parallel resource terms, traversing
  nested @{const Parallel} terms and dropping any @{const Empty} resources in them.
  We call these the parallel parts.
\<close>
primrec parallel_parts :: "('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term list"
  where
    "parallel_parts Empty = []"
  | "parallel_parts Anything = [Anything]"
  | "parallel_parts (Res a) = [Res a]"
  | "parallel_parts (Copyable a) = [Copyable a]"
  | "parallel_parts (Parallel xs) = concat (map parallel_parts xs)"
  | "parallel_parts (NonD a b) = [NonD a b]"
  | "parallel_parts (Executable a b) = [Executable a b]"
  | "parallel_parts (Repeatable a b) = [Repeatable a b]"

text\<open>Every resource is equivalent to combining its parallel parts in parallel\<close>
lemma parallel_parts_eq:
  "x \<sim> Parallel (parallel_parts x)"
proof (induct x)
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable x) then show ?case by simp
next
  case (Parallel xs)
  then show ?case
  proof (induct xs)
    case Nil then show ?case by simp
  next
    case (Cons a x)
    then have a1: "a \<sim> Parallel (parallel_parts a)"
          and a2: "Parallel x \<sim> Parallel (parallel_parts (Parallel x))"
      by simp_all

    have "Parallel [a] \<sim> Parallel (parallel_parts a)"
      using a1 res_term_equiv.trans res_term_equiv.singleton by blast
    then have "Parallel (a # x) \<sim> Parallel (parallel_parts a @ parallel_parts (Parallel x))"
      using res_term_equiv.decompose[OF _ a2, of "[a]"] by simp
    then show ?case
      by simp
  qed
next case (NonD x1 x2) then show ?case by simp
next case (Executable x1 x2) then show ?case by simp
next case (Repeatable x1 x2) then show ?case by simp
qed

text\<open>Equivalent parallel parts is the same as equivalent resource terms\<close>
lemma equiv_parallel_parts:
  "list_all2 (\<sim>) (parallel_parts a) (parallel_parts b) = a \<sim> b"
proof
  show "list_all2 (\<sim>) (parallel_parts a) (parallel_parts b) \<Longrightarrow> a \<sim> b"
    by (meson res_term_equiv.parallel parallel_parts_eq res_term_equiv.sym res_term_equiv.trans)
  show "a \<sim> b \<Longrightarrow> list_all2 (\<sim>) (parallel_parts a) (parallel_parts b)"
  proof (induct rule: res_term_equiv.induct)
       case empty then show ?case by simp
  next case anything then show ?case by simp
  next case (res x) then show ?case by simp
  next case (copyable x) then show ?case by simp
  next case nil then show ?case by simp
  next case (singleton a) then show ?case by (simp add: list_all2_refl)
  next case (merge x y z) then show ?case by (simp add: list_all2_refl)
  next
    case (parallel xs ys)
    then show ?case
      by (induct rule: list_all2_induct ; simp add: list_all2_appendI)
  next case (nondet x y u v) then show ?case by (simp add: res_term_equiv.nondet)
  next case (executable x y u v) then show ?case by (simp add: res_term_equiv.executable)
  next case (repeatable x y u v) then show ?case by (simp add: res_term_equiv.repeatable)
  next case (sym x y) then show ?case by (simp add: list_all2_conv_all_nth res_term_equiv.sym)
  next case (trans x y z) then show ?case using res_term_equiv.trans list_all2_trans by blast
  qed
qed

text\<open>Note that resource term equivalence does not imply parallel parts equality\<close>
lemma
  obtains x y where "x \<sim> y" and "parallel_parts x \<noteq> parallel_parts y"
proof
  let ?x = "NonD (Parallel [Anything, Empty]) (Parallel [])"
  let ?y = "NonD Anything Empty"

  show "?x \<sim> ?y"
    by (simp add: res_term_equiv.nondet)
  show "parallel_parts ?x \<noteq> parallel_parts ?y"
    by simp
qed
text\<open>But it does imply that both have equal number of parallel parts\<close>
lemma parallel_parts_length_eq:
  "x \<sim> y \<Longrightarrow> length (parallel_parts x) = length (parallel_parts y)"
  using equiv_parallel_parts list_all2_lengthD by blast

text\<open>Empty parallel parts, however, is the same as equivalence to the unit\<close>
lemma parallel_parts_nil_equiv_empty:
  "(parallel_parts a = []) = a \<sim> Empty"
  using equiv_parallel_parts list.rel_sel parallel_parts.simps(1) by blast

text\<open>Singleton parallel parts imply equivalence to the one element\<close>
lemma parallel_parts_single_equiv_element:
  "parallel_parts a = [x] \<Longrightarrow> a \<sim> x"
  using parallel_parts_eq res_term_equiv.trans by force

text\<open>No element of parallel parts is @{const Parallel} or @{const Empty}\<close>
lemma parallel_parts_have_no_empty:
  "x \<in> set (parallel_parts a) \<Longrightarrow> \<not> is_Empty x"
  by (induct a) fastforce+
lemma parallel_parts_have_no_par:
  "x \<in> set (parallel_parts a) \<Longrightarrow> \<not> is_Parallel x"
  by (induct a) fastforce+

text\<open>Every parallel part of a resource is at most as big as it\<close>
lemma parallel_parts_not_bigger:
  "x \<in> set (parallel_parts a) \<Longrightarrow> size_res_term f g x \<le> (size_res_term f g a)"
proof (induct a)
     case Empty then show ?case by simp
next case Anything then show ?case by simp
next case (Res x) then show ?case by simp
next case (Copyable x) then show ?case by simp
next
  case (Parallel x)
  then show ?case
    by (clarsimp simp add: le_SucI size_list_estimation')
next case (NonD a1 a2) then show ?case by simp
next case (Executable a1 a2) then show ?case by simp
next case (Repeatable a1 a2) then show ?case by simp
qed

text\<open>Any resource that is not @{const Empty} or @{const Parallel} has itself as parallel part\<close>
lemma parallel_parts_self [simp]:
  "\<lbrakk>\<not> is_Empty x; \<not> is_Parallel x\<rbrakk> \<Longrightarrow> parallel_parts x = [x]"
  by (cases x) simp_all

text\<open>
  List of terms with no @{const Empty} or @{const Parallel} elements is the same as parallel parts
  of the @{const Parallel} term build from it
\<close>
lemma parallel_parts_no_empty_parallel:
  assumes "\<not> list_ex is_Empty xs"
      and "\<not> list_ex is_Parallel xs"
    shows "parallel_parts (Parallel xs) = xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

subsection\<open>Parallelisation\<close>

text\<open>
  In the opposite direction of parallel parts, we can take a list of resource terms and combine them
  in parallel in a way smarter than just using @{const Parallel}.
  This rests in checking the list length, using the @{const Empty} resource if it is empty and
  skipping the wrapping in @{const Parallel} if it has only a single element.
  We call this parallelisation.
\<close>
fun parallelise :: "('a, 'b) res_term list \<Rightarrow> ('a, 'b) res_term"
  where
    "parallelise [] = Empty"
  | "parallelise [x] = x"
  | "parallelise xs = Parallel xs"

text\<open>This produces equivalent results to the @{const Parallel} constructor\<close>
lemma parallelise_equiv:
  "parallelise xs \<sim> Parallel xs"
  by (cases xs rule: parallelise.cases) simp_all

text\<open>Lists of equal length that parallelise to the same term must have been equal\<close>
lemma parallelise_same_length:
  "\<lbrakk>parallelise x = parallelise y; length x = length y\<rbrakk> \<Longrightarrow> x = y"
  by (elim parallelise.elims) simp_all

text\<open>Parallelisation and naive parallel combination have the same parallel parts\<close>
lemma parallel_parts_parallelise_eq:
  "parallel_parts (parallelise xs) = parallel_parts (Parallel xs)"
  by (cases xs rule: parallelise.cases) simp_all

text\<open>
  Parallelising to a @{const Parallel} term means the input is either:
  \<^item> A singleton set containing just that resulting @{const Parallel} term, or
  \<^item> Exactly the children of the output and with at least two elements.
\<close>
lemma parallelise_to_parallel_conv:
  "(parallelise xs = Parallel ys) = (xs = [Parallel ys] \<or> (1 < length xs \<and> xs = ys))"
proof
  show "parallelise xs = Parallel ys \<Longrightarrow> xs = [Parallel ys] \<or> 1 < length xs \<and> xs = ys"
    by (fastforce elim: parallelise.elims)
  have "xs = [Parallel ys] \<Longrightarrow> parallelise xs = Parallel ys"
    by simp
  moreover have "1 < length xs \<and> xs = ys \<Longrightarrow> parallelise xs = Parallel ys"
    by simp (metis Suc_lessD length_Cons list.size(3) nat_neq_iff parallelise.elims)
  ultimately show "xs = [Parallel ys] \<or> 1 < length xs \<and> xs = ys \<Longrightarrow> parallelise xs = Parallel ys"
    by blast
qed

text\<open>
  So parallelising to a @{const Parallel} term with the same children is the same as the list having
  at least two elements
\<close>
lemma parallelise_to_parallel_same_length:
  "(parallelise xs = Parallel xs) = (1 < length xs)"
  by (simp add: parallelise_to_parallel_conv) (metis parallel_neq_single)

text\<open>
  If the output of parallelisation contains a nested @{const Parallel} term then so must have the
  input list
\<close>
lemma parallelise_to_parallel_has_paralell:
  assumes "parallelise xs = Parallel ys"
      and "list_ex is_Parallel ys"
    shows "list_ex is_Parallel xs"
  using assms by (induct xs rule: parallelise.induct) simp_all

text\<open>If the output of parallelisation contains @{const Empty} then so must have the input\<close>
lemma parallelise_to_parallel_has_empty:
  assumes "parallelise xs = Parallel ys"
  obtains "xs = [Parallel ys]"
        | "xs = ys"
  using assms parallelise_to_parallel_conv by blast

text\<open>Parallelising to @{const Empty} means the input list was either empty or contained just that\<close>
lemma parallelise_to_empty_eq:
  assumes "parallelise xs = Empty"
  obtains "xs = []"
        | "xs = [Empty]"
  using assms parallelise.elims by blast

text\<open>
  If a list parallelises to anything but @{const Parallel} or @{const Empty}, then it must have been
  a singleton of that term
\<close>
lemma parallelise_to_single_eq:
  assumes "parallelise xs = a"
      and "\<not> is_Empty a"
      and "\<not> is_Parallel a"
    shows "xs = [a]"
  using assms by (cases xs rule: parallelise.cases ; fastforce)

text\<open>Sets of atoms after parallelisation are unions of those atoms sets for the inputs\<close>
lemma set1_res_term_parallelise [simp]:
  "set1_res_term (ResTerm.parallelise xs) = \<Union>(set1_res_term ` set xs)"
  by (induct xs rule: parallelise.induct) simp_all
lemma set2_res_term_parallelise [simp]:
  "set2_res_term (ResTerm.parallelise xs) = \<Union>(set2_res_term ` set xs)"
  by (induct xs rule: parallelise.induct) simp_all

subsection\<open>Refinement\<close>

text\<open>
  Resource term refinement applies two functions to the linear and copyable atoms in a term.
  Unlike @{const map_res_term}, the first function (applied to linear atoms) is allowed to produce
  full resource terms, not just other atoms.
  (The second function must still produce other atoms, because we cannot replace a copyable atom
  with an arbitrary, possibly not copyable, resource.)
  This allows us to refine atoms into potentially complex terms.
\<close>
primrec refine_res_term ::
    "('a \<Rightarrow> ('x, 'y) res_term) \<Rightarrow> ('b \<Rightarrow> 'y) \<Rightarrow> ('a, 'b) res_term \<Rightarrow> ('x, 'y) res_term"
  where
    "refine_res_term f g Empty = Empty"
  | "refine_res_term f g Anything = Anything"
  | "refine_res_term f g (Res a) = f a"
  | "refine_res_term f g (Copyable x) = Copyable (g x)"
  | "refine_res_term f g (Parallel xs) = Parallel (map (refine_res_term f g) xs)"
  | "refine_res_term f g (NonD x y) = NonD (refine_res_term f g x) (refine_res_term f g y)"
  | "refine_res_term f g (Executable x y) =
      Executable (refine_res_term f g x) (refine_res_term f g y)"
  | "refine_res_term f g (Repeatable x y) =
      Repeatable (refine_res_term f g x) (refine_res_term f g y)"

text\<open>
  Two refined resources are equivalent if:
  \<^item> the original resources were equivalent,
  \<^item> the linear atom refinements produce equivalent terms and
  \<^item> the copyable atom refinements produce identical atoms.
\<close>
lemma refine_res_term_eq:
  assumes "x \<sim> y"
      and "\<And>x. f x \<sim> f' x"
      and "\<And>x. g x = g' x"
    shows "refine_res_term f g x \<sim> refine_res_term f' g' y"
proof -
  have reflexivity: "refine_res_term f g a \<sim> refine_res_term f' g' a" for a
  \<comment> \<open>First we prove the simpler case where the two resources are equal, so we can use it later\<close>
  proof (induct a)
       case Empty then show ?case by simp
  next case Anything then show ?case by simp
  next case (Res x) then show ?case using assms(2) by simp
  next case (Copyable x) then show ?case using assms(3) by simp
  next
    case (Parallel x)
    then show ?case
      by (clarsimp intro!: res_term_equiv.parallel)
         (metis (mono_tags, lifting) length_map list_all2_all_nthI nth_map nth_mem)
  next case (NonD a1 a2) then show ?case by (simp add: res_term_equiv.nondet)
  next case (Executable a1 a2) then show ?case by (simp add: res_term_equiv.executable)
  next case (Repeatable a1 a2) then show ?case by (simp add: res_term_equiv.repeatable)
  qed

  from assms show ?thesis
  \<comment> \<open>Then we prove the general statement by induction on assumed equivalence\<close>
  proof (induct rule: res_term_equiv.induct)
       case empty then show ?case by simp
  next case anything then show ?case by simp
  next case (res x) then show ?case by simp
  next case (copyable x) then show ?case by simp
  next case nil then show ?case by simp
  next
    case (singleton a)
    then have "refine_res_term f g (Parallel [a]) \<sim> refine_res_term f g a"
      by simp
    then show ?case
      using reflexivity res_term_equiv.trans by metis
  next
    case (merge x y z)
    have
      " length (map (refine_res_term f g') x @
          map (refine_res_term f g') y @ map (refine_res_term f g') z)
      = length (map (refine_res_term f' g') x @
          map (refine_res_term f' g') y @ map (refine_res_term f' g') z)"
      by simp
    moreover have
      " ((map (refine_res_term f g) x @
            map (refine_res_term f g) y @ map (refine_res_term f g) z) ! i)
      \<sim> ((map (refine_res_term f' g') x @
            map (refine_res_term f' g') y @ map (refine_res_term f' g') z) ! i)"
      if "i < length x + length y + length z" for i
      by (metis append.assoc length_append map_append nth_map reflexivity that)
    ultimately have
      " list_all2 (\<sim>)
          ( map (refine_res_term f g) x
          @ map (refine_res_term f g) y
          @ map (refine_res_term f g) z)
          ( map (refine_res_term f' g') x
          @ map (refine_res_term f' g') y
          @ map (refine_res_term f' g') z)"
      by (smt (verit, del_insts) append_assoc length_append length_map list_all2_all_nthI)
    then have
      " Parallel (map (refine_res_term f g) x @
          [Parallel (map (refine_res_term f g) y)] @ map (refine_res_term f g) z)
      \<sim> Parallel (map (refine_res_term f' g') x @
          map (refine_res_term f' g') y @ map (refine_res_term f' g') z)"
      using res_term_equiv.merge res_term_equiv.parallel res_term_equiv.trans by blast
    then show ?case
      by simp
  next
    case (parallel xs ys)
    then show ?case
      by (simp add: res_term_equiv.parallel list_all2_conv_all_nth)
  next case (nondet x y u v) then show ?case by (simp add: res_term_equiv.nondet)
  next case (executable x y u v) then show ?case by (simp add: res_term_equiv.executable)
  next case (repeatable x y u v) then show ?case by (simp add: res_term_equiv.repeatable)
  next
    case (sym x y)
    then show ?case
      by (metis res_term_equiv.sym res_term_equiv.trans reflexivity)
  next
    case (trans x y z)
    then show ?case
      by (metis res_term_equiv.sym res_term_equiv.trans reflexivity)
  qed
qed

subsection\<open>Removing @{const Empty} Terms From a List\<close>

text\<open>
  As part of simplifying resource terms, it is sometimes useful to be able to take a list of terms
  and drop from it any empty resource.
\<close>
primrec remove_all_empty :: "('a, 'b) res_term list \<Rightarrow> ('a, 'b) res_term list"
  where
    "remove_all_empty [] = []"
  | "remove_all_empty (x#xs) = (if is_Empty x then remove_all_empty xs else x#remove_all_empty xs)"

text\<open>
  The result of dropping @{const Empty} terms from a list of resource terms is a subset of the
  original list
\<close>
lemma remove_all_empty_subset:
  "x \<in> set (remove_all_empty xs) \<Longrightarrow> x \<in> set xs"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by simp (metis (full_types) set_ConsD)
qed

text\<open>If there are no @{const Empty} terms then removing them is the same as not doing anything\<close>
lemma remove_all_empty_none:
  "\<not> list_ex is_Empty xs \<Longrightarrow> remove_all_empty xs = xs"
  by (induct xs ; force)

text\<open>There are no @{const Empty} terms left after they are removed\<close>
lemma remove_all_empty_result:
  "\<not> list_ex is_Empty (remove_all_empty xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

text\<open>Removing @{const Empty} terms distributes over appending lists\<close>
lemma remove_all_empty_append:
  "remove_all_empty (xs @ ys) = remove_all_empty xs @ remove_all_empty ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

text\<open>Removing @{const Empty} terms distributes over constructing lists\<close>
lemma remove_all_empty_Cons:
  "remove_all_empty (x # xs) = remove_all_empty [x] @ remove_all_empty xs"
  using remove_all_empty_append by (metis append.left_neutral append_Cons)

text\<open>
  Removing @{const Empty} terms from children of a parallel resource term results in an equivalent
  term
\<close>
lemma remove_all_empty_equiv:
  "Parallel xs \<sim> Parallel (remove_all_empty xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis append.left_neutral append_Cons remove_all_empty.simps(2) res_term_equiv.drop
        res_term_equiv.refl res_term_equiv.trans res_term_parallel_cons is_Empty_def)
qed

text\<open>Removing @{const Empty} terms does not affect the atom sets\<close>
lemma set1_res_term_remove_all_empty [simp]:
  "\<Union>(set1_res_term ` set (remove_all_empty xs)) = \<Union>(set1_res_term ` set xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a) simp_all
qed
lemma set2_res_term_remove_all_empty [simp]:
  "\<Union>(set2_res_term ` set (remove_all_empty xs)) = \<Union>(set2_res_term ` set xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a) simp_all
qed

subsection\<open>Merging Nested @{const Parallel} Terms in a List\<close>

text\<open>
  Similarly, it is sometimes useful to be able to take a list of terms and merge the children of any
  @{const Parallel} term in it up into the list itself
\<close>
primrec merge_all_parallel :: "('a, 'b) res_term list \<Rightarrow> ('a, 'b) res_term list"
  where
    "merge_all_parallel [] = []"
  | "merge_all_parallel (x#xs) =
      (case x of Parallel y \<Rightarrow> y @ merge_all_parallel xs | _ \<Rightarrow> x # merge_all_parallel xs)"

text\<open>If there are no @{const Parallel} terms then merging them is the same as not doing anything\<close>
lemma merge_all_parallel_none:
  "\<not> list_ex is_Parallel xs \<Longrightarrow> merge_all_parallel xs = xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

text\<open>
  If no element of the input list has itself nested @{const Parallel} terms then there will be none
  left after merging @{const Parallel} terms in the list
\<close>
lemma merge_all_parallel_result:
  assumes "\<And>ys. Parallel ys \<in> set xs \<Longrightarrow> \<not> list_ex is_Parallel ys"
    shows "\<not> list_ex is_Parallel (merge_all_parallel xs)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; fastforce)
qed

text\<open>Merging nested @{const Parallel} terms distributes over appending lists\<close>
lemma merge_all_parallel_append:
  "merge_all_parallel (xs @ ys) = merge_all_parallel xs @ merge_all_parallel ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a ; simp)
qed

text\<open>Merging @{const Parallel} terms distributes over constructing lists\<close>
lemma merge_all_parallel_Cons:
  "merge_all_parallel (x # xs) = merge_all_parallel [x] @ merge_all_parallel xs"
  using merge_all_parallel_append by (metis append.left_neutral append_Cons)

text\<open>
  Merging @{const Parallel} terms nested in another @{const Parallel} term results in an equivalent
  term
\<close>
lemma merge_all_parallel_equiv:
  "Parallel xs \<sim> Parallel (merge_all_parallel xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have ?case if "a = Parallel as" for as
    using Cons
    by (simp add: that)
       (metis append.left_neutral append_Cons res_term_equiv.decompose res_term_equiv.singleton)
  moreover have ?case if "\<And>as. a \<noteq> Parallel as"
    using Cons by (cases a) (simp_all add: that res_term_parallel_cons)
  ultimately show ?case
    by metis
qed

text\<open>
  If the output of @{const merge_all_parallel} contains @{const Empty} then:
  \<^item> It was nested in one of the input elements, or
  \<^item> It was in the input.
\<close>
lemma merge_all_parallel_has_empty:
  assumes "list_ex is_Empty (merge_all_parallel xs)"
  obtains ys where "Parallel ys \<in> set xs" and "list_ex is_Empty ys"
        | "list_ex is_Empty xs"
  using assms
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases a) fastforce+
qed

text\<open>Merging @{const Parallel} terms does not affect the atom sets\<close>
lemma set1_res_term_merge_all_parallel [simp]:
  "\<Union>(set1_res_term ` set (merge_all_parallel xs)) = \<Union>(set1_res_term ` set xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a) simp_all
qed
lemma set2_res_term_merge_all_parallel [simp]:
  "\<Union>(set2_res_term ` set (merge_all_parallel xs)) = \<Union>(set2_res_term ` set xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a) simp_all
qed

end