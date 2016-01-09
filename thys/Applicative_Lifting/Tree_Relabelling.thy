(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Tree relabelling\<close>

theory Tree_Relabelling imports
  Applicative_State
  Applicative_Option
  "~~/src/HOL/Library/Stream"
begin

interpretation applicative_syntax .
adhoc_overloading Applicative.pure pure_state
adhoc_overloading Applicative.pure pure_option

text \<open> Hutton and Fulger \cite{HuttonFulger2008TFP} suggested the following tree relabelling problem
  as an example for reasoning about effects. Given a binary tree with labels at the leaves, the
  relabelling assigns a unique number to every leaf.  Their correctness property states that the
  list of labels in the obtained tree is distinct.  As observed by Gibbons and Bird \cite{backwards},
  this breaks the abstraction of the state monad, because the relabeling function must be run.
  Although Hutton and Fulger are careful to reason in point-free style, they nevertheless unfold
  the implementation of the state monad operations.  Gibbons and Hinze \cite{GibbonsHinze2011ICFP}
  suggest to state the correctness in an effectful way using an exception-state monad.  Thereby, they
  lose the applicative structure and have to resort to a full monad.
  
  Here, we model the tree relabelling function three times. First, we state correctness in pure
  terms following Hutton and Fulger.  Second, we take Gibbons' and Bird's approach of considering
  traversals. Third, we state correctness effectfully, but only using the applicative functors.
\<close>

datatype 'a tree = Leaf 'a | Node "'a tree" "'a tree"

primrec fold_tree :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a tree \<Rightarrow> 'b"
where
  "fold_tree f g (Leaf a) = f a"
| "fold_tree f g (Node l r) = g (fold_tree f g l) (fold_tree f g r)"

definition leaves :: "'a tree \<Rightarrow> nat"
where "leaves = fold_tree (\<lambda>_. 1) (op +)"

lemma leaves_simps [simp]:
  "leaves (Leaf x) = 1"
  "leaves (Node l r) = leaves l + leaves r"
by(simp_all add: leaves_def)


subsubsection \<open>Pure correctness statement\<close>

definition labels :: "'a tree \<Rightarrow> 'a list"
where "labels = fold_tree (\<lambda>x. [x]) append"

lemma labels_simps [simp]:
  "labels (Leaf x) = [x]"
  "labels (Node l r) = labels l @ labels r"
by(simp_all add: labels_def)

locale labelling =
  fixes fresh :: "('x, 's) state"
begin

definition label_tree :: "'a tree \<Rightarrow> ('x tree, 's) state"
where "label_tree = fold_tree (\<lambda>_ :: 'a. pure Leaf \<diamondop> fresh) (\<lambda>l r. pure Node \<diamondop> l \<diamondop> r)"

lemma label_tree_simps [simp]:
  "label_tree (Leaf x) = pure Leaf \<diamondop> fresh"
  "label_tree (Node l r) = pure Node \<diamondop> label_tree l \<diamondop> label_tree r"
by(simp_all add: label_tree_def)

primrec label_list :: "'a list \<Rightarrow> ('x list, 's) state"
where
    "label_list [] = pure []"
  | "label_list (x # xs) = pure (op #) \<diamondop> fresh \<diamondop> label_list xs"

lemma label_append: "label_list (a @ b) = pure (op @) \<diamondop> label_list a \<diamondop> label_list b"
  -- \<open>The proof lifts the defining equations of @{const append} to the state monad.\<close>
proof (induction a)
  case Nil
  show ?case
    unfolding append.simps label_list.simps
    by applicative_nf simp
next
  case (Cons a1 a2)
  show ?case
    unfolding append.simps label_list.simps Cons.IH
    by applicative_nf simp
qed

lemma label_tree_list: "pure labels \<diamondop> label_tree t = label_list (labels t)"
proof (induction t)
  case Leaf show ?case unfolding label_tree_simps labels_simps label_list.simps
    by applicative_nf simp
next
  case Node show ?case unfolding label_tree_simps labels_simps label_append Node.IH[symmetric]
    by applicative_nf simp
qed

text \<open>We directly show correctness without going via streams like Hutton and Fulger \cite{HuttonFulger2008TFP}. \<close>

lemma correctness_pure:
  fixes t :: "'a tree"
  assumes distinct: "\<And>xs :: 'a list. distinct (fst (label_list xs s))"
  shows "distinct (labels (fst (label_tree t s)))"
using label_tree_list[of t, THEN fun_cong, of s] assms[of "labels t"]
by(cases "label_list (labels t) s")(simp add: ap_state_def split_beta)

end

subsubsection \<open>Correctness via monadic traversals\<close>

text \<open>Dual version of an applicative functor with effects composed in the opposite order\<close>

typedef 'a dual = "UNIV :: 'a set" morphisms un_B B by blast
setup_lifting type_definition_dual

lift_definition pure_dual :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b dual"
is "\<lambda>pure. pure" .

lift_definition ap_dual :: "(('a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> 'af1) \<Rightarrow> ('af1 \<Rightarrow> 'af3 \<Rightarrow> 'af13) \<Rightarrow> ('af13 \<Rightarrow> 'af2 \<Rightarrow> 'af) \<Rightarrow> 'af2 dual \<Rightarrow> 'af3 dual \<Rightarrow> 'af dual"
is "\<lambda>pure ap1 ap2 f x. ap2 (ap1 (pure (\<lambda>x f. f x)) x) f" .

type_synonym ('a, 's) state_rev = "('a, 's) state dual"

definition pure_state_rev :: "'a \<Rightarrow> ('a, 's) state_rev"
where "pure_state_rev = pure_dual pure_state"

definition ap_state_rev :: "('a \<Rightarrow> 'b, 's) state_rev \<Rightarrow> ('a, 's) state_rev \<Rightarrow> ('b, 's) state_rev"
where "ap_state_rev = ap_dual pure_state ap_state ap_state"

adhoc_overloading Applicative.pure pure_state_rev
adhoc_overloading Applicative.ap ap_state_rev

applicative state_rev
for
  pure: pure_state_rev
  ap: ap_state_rev
unfolding pure_state_rev_def ap_state_rev_def by(transfer, applicative_nf, rule refl)+


type_synonym ('a, 's) state_rev_rev = "('a, 's) state_rev dual"

definition pure_state_rev_rev :: "'a \<Rightarrow> ('a, 's) state_rev_rev"
where "pure_state_rev_rev = pure_dual pure_state_rev"

definition ap_state_rev_rev :: "('a \<Rightarrow> 'b, 's) state_rev_rev \<Rightarrow> ('a, 's) state_rev_rev \<Rightarrow> ('b, 's) state_rev_rev"
where "ap_state_rev_rev = ap_dual pure_state_rev ap_state_rev ap_state_rev"

adhoc_overloading Applicative.pure pure_state_rev_rev
adhoc_overloading Applicative.ap ap_state_rev_rev

applicative state_rev_rev
for
  pure: pure_state_rev_rev
  ap: ap_state_rev_rev
unfolding pure_state_rev_rev_def ap_state_rev_rev_def by(transfer, applicative_nf, rule refl)+


context begin interpretation applicative_syntax .
lemma ap_state_rev_B: "B f \<diamondop> B x = B (pure_state (\<lambda>x f. f x) \<diamondop> x \<diamondop> f)"
unfolding ap_state_rev_def by(fact ap_dual.abs_eq)

lemma ap_state_rev_pure_B: "pure f \<diamondop> B x = B (pure_state f \<diamondop> x)"
unfolding ap_state_rev_def pure_state_rev_def
by transfer(applicative_nf, rule refl)

lemma ap_state_rev_rev_B: "B f \<diamondop> B x = B (pure_state_rev (\<lambda>x f. f x) \<diamondop> x \<diamondop> f)"
unfolding ap_state_rev_rev_def by(fact ap_dual.abs_eq)

lemma ap_state_rev_rev_pure_B: "pure f \<diamondop> B x = B (pure_state_rev f \<diamondop> x)"
unfolding ap_state_rev_rev_def pure_state_rev_rev_def
by transfer(applicative_nf, rule refl)
end

text \<open>
  The formulation by Gibbons and Bird \cite{backwards} crucially depends on Kleisli composition,
  so we need the state monad rather than the applicative functor only.
\<close>
definition bind_state :: "('s \<Rightarrow> 'a \<times> 's) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'b \<times> 's) \<Rightarrow> 's \<Rightarrow> 'b \<times> 's"
where "bind_state x f s = (let (a, s') = x s in f a s')"

lemma bind_state_assoc: "bind_state (bind_state x f) g = bind_state x (\<lambda>x. bind_state (f x) g)"
by(simp add: fun_eq_iff bind_state_def split_def Let_def)

lemma bind_state_return1: "bind_state (Pair x) f = f x"
by(simp add: bind_state_def fun_eq_iff)

lemma ap_conv_bind_state: "ap_state f x = bind_state f (\<lambda>f. bind_state x (Pair \<circ> f))"
by(simp add: ap_state_def bind_state_def Let_def split_def o_def fun_eq_iff)

lemma ap_pure_bind_state: "pure x \<diamondop> bind_state y f = bind_state y (op \<diamondop> (pure x) \<circ> f)"
by(simp add: ap_conv_bind_state bind_state_return1 bind_state_assoc o_def)

definition kleisli_state :: "('b \<Rightarrow> ('c, 's) state) \<Rightarrow> ('a \<Rightarrow> ('b, 's) state) \<Rightarrow> 'a \<Rightarrow> ('c, 's) state" (infixl "\<bullet>" 55)
where [simp]: "kleisli_state g f a = bind_state (f a) g"

definition fetch :: "('a, 'a stream) state"
where "fetch s = (shd s, stl s)"

primrec traverse :: "('a \<Rightarrow> ('b, 's) state) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state"
where
  "traverse f (Leaf x) = pure Leaf \<diamondop> f x"
| "traverse f (Node l r) = pure Node \<diamondop> traverse f l \<diamondop> traverse f r"

text \<open>As we cannot abstract over the applicative functor in definitions, we define
  traversal on the transformed applicative function once again.\<close>

primrec traverse_rev :: "('a \<Rightarrow> ('b, 's) state_rev) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state_rev"
where
  "traverse_rev f (Leaf x) = pure Leaf \<diamondop> f x"
| "traverse_rev f (Node l r) = pure Node \<diamondop> traverse_rev f l \<diamondop> traverse_rev f r"

definition recurse :: "('a \<Rightarrow> ('b, 's) state) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state"
where "recurse f = un_B \<circ> traverse_rev (B \<circ> f)"

lemma recurse_Leaf: "recurse f (Leaf x) = pure Leaf \<diamondop> f x"
unfolding recurse_def traverse_rev.simps o_def ap_state_rev_pure_B
by(simp add: B_inverse)

lemma recurse_Node:
  "recurse f (Node l r) = pure (\<lambda>r l. Node l r) \<diamondop> recurse f r \<diamondop> recurse f l"
proof -
  have "recurse f (Node l r) = un_B (pure Node \<diamondop> traverse_rev (B \<circ> f) l \<diamondop> traverse_rev (B \<circ> f) r)"
    by(simp add: recurse_def)
  also have "\<dots> = un_B (B (pure Node) \<diamondop> B (recurse f l) \<diamondop> B (recurse f r))"
    by(simp add: un_B_inverse recurse_def pure_state_rev_def pure_dual_def)
  also have "\<dots> = pure (\<lambda>x f. f x) \<diamondop> recurse f r \<diamondop> (pure (\<lambda>x f. f x) \<diamondop> recurse f l \<diamondop> pure Node)"
    by(simp add: ap_state_rev_B B_inverse)
  also have "\<dots> = pure (\<lambda>r l. Node l r) \<diamondop> recurse f r \<diamondop> recurse f l"
    -- \<open>This step expands to 13 steps in \cite{backwards}\<close>
    by(applicative_nf) simp
  finally show ?thesis .
qed

lemma traverse_pure: "traverse pure t = pure t"
proof(induction t)
  { case Leaf show ?case unfolding traverse.simps by applicative_nf simp }
  { case Node show ?case unfolding traverse.simps Node.IH by applicative_nf simp }
qed


text \<open>@{term "B \<circ> B"} is an idiom morphism\<close>

lemma B_pure: "pure x = B (pure_state x)"
unfolding pure_state_rev_def by transfer simp

lemma BB_pure: "pure x = B (B (pure x))"
unfolding pure_state_rev_rev_def B_pure[symmetric] by transfer(rule refl)

lemma BB_ap: "B (B f) \<diamondop> B (B x) = B (B (f \<diamondop> x))"
proof -
  have "B (B f) \<diamondop> B (B x) = B (B (pure (\<lambda>x f. f x) \<diamondop> f \<diamondop> (pure (\<lambda>x f. f x) \<diamondop> x \<diamondop> pure (\<lambda>x f. f x))))"
    (is "_ = B (B ?exp)")
    unfolding ap_state_rev_rev_B B_pure ap_state_rev_B ..
  also have "?exp = f \<diamondop> x" -- \<open>This step takes 15 steps in \cite{backwards}.\<close>
    by(applicative_nf)(rule refl)
  finally show ?thesis .
qed

primrec traverse_rev_rev :: "('a \<Rightarrow> ('b, 's) state_rev_rev) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state_rev_rev"
where
  "traverse_rev_rev f (Leaf x) = pure Leaf \<diamondop> f x"
| "traverse_rev_rev f (Node l r) = pure Node \<diamondop> traverse_rev_rev f l \<diamondop> traverse_rev_rev f r"

definition recurse_rev :: "('a \<Rightarrow> ('b, 's) state_rev) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state_rev"
where "recurse_rev f = un_B \<circ> traverse_rev_rev (B \<circ> f)"

lemma traverse_B_B: "traverse_rev_rev (B \<circ> B \<circ> f) = B \<circ> B \<circ> traverse f" (is "?lhs = ?rhs")
proof
  fix t
  show "?lhs t = ?rhs t" by(induction t)(simp_all add: BB_pure BB_ap)
qed

lemma traverse_recurse: "traverse f = un_B \<circ> recurse_rev (B \<circ> f)" (is "?lhs = ?rhs")
proof -
  have "?lhs = un_B \<circ> un_B \<circ> B \<circ> B \<circ> traverse f" by(simp add: o_def B_inverse)
  also have "\<dots> = un_B \<circ> un_B \<circ> traverse_rev_rev (B \<circ> B \<circ> f)" unfolding traverse_B_B by(simp add: o_assoc)
  also have "\<dots> = ?rhs" by(simp add: recurse_rev_def o_assoc)
  finally show ?thesis .
qed

lemma recurse_traverse:
  assumes "f \<bullet> g = pure"
  shows "recurse f \<bullet> traverse g = pure"
-- \<open>Gibbons and Bird impose this as an additional requirement on traversals, but they write
  that they have not found a way to derive this fact from other axioms. So we prove it directly.\<close>
proof
  fix t
  from assms have *: "\<And>x. bind_state (g x) f = Pair x" by(simp add: fun_eq_iff)
  hence **: "\<And>x h. bind_state (g x) (\<lambda>x. bind_state (f x) h) = h x"
    by(fold bind_state_assoc)(simp add: bind_state_return1)
  show "(recurse f \<bullet> traverse g) t = pure t" unfolding kleisli_state_def
  proof(induction t)
    case (Leaf x)
    show ?case
      by(simp add: ap_conv_bind_state bind_state_assoc bind_state_return1 recurse_Leaf **)
  next
    case (Node l r)
    show ?case
      by(simp add: ap_conv_bind_state bind_state_assoc bind_state_return1 recurse_Node)
        (simp add: bind_state_assoc[symmetric] Node.IH bind_state_return1)
  qed
qed

text \<open>Apply traversals to labelling\<close>

definition strip :: "'a \<times> 'b \<Rightarrow> ('a, 'b stream) state"
where "strip = (\<lambda>(a, b) s. (a, SCons b s))"

definition adorn :: "'a \<Rightarrow> ('a \<times> 'b, 'b stream) state"
where "adorn a = pure (Pair a) \<diamondop> fetch"

abbreviation label :: "'a tree \<Rightarrow> (('a \<times> 'b) tree, 'b stream) state"
where "label \<equiv> traverse adorn"

abbreviation unlabel :: "('a \<times> 'b) tree \<Rightarrow> ('a tree, 'b stream) state"
where "unlabel \<equiv> recurse strip"

lemma strip_adorn: "strip \<bullet> adorn = pure"
by(simp add: strip_def adorn_def fun_eq_iff fetch_def[abs_def] bind_state_def ap_conv_bind_state)

lemma correctness_monadic: "unlabel \<bullet> label = pure"
by(rule recurse_traverse)(rule strip_adorn)


subsubsection \<open>Applicative correctness statement\<close>

text \<open>Repeating an effect\<close>

primrec repeatM :: "nat \<Rightarrow> ('x, 's) state \<Rightarrow> ('x list, 's) state"
where
  "repeatM 0 f = pure_state []"
| "repeatM (Suc n) f = pure op # \<diamondop> f \<diamondop> repeatM n f"

lemma repeatM_plus: "repeatM (n + m) f = pure append \<diamondop> repeatM n f \<diamondop> repeatM m f"
by(induction n)(simp; applicative_nf; simp)+

abbreviation (input) fail :: "'a option" where "fail \<equiv> None"


definition lift_state :: "('a, 's) state \<Rightarrow> ('a option, 's) state"
where [applicative_unfold]: "lift_state x = pure pure \<diamondop> x"

definition lift_option :: "'a option \<Rightarrow> ('a option, 's) state"
where [applicative_unfold]: "lift_option x = pure x"

fun assert :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option"
where
  assert_fail: "assert P fail = fail"
| assert_pure: "assert P (pure x) = (if P x then pure x else fail)"

context labelling begin

abbreviation symbols :: "nat \<Rightarrow> ('x list option, 's) state"
where "symbols n \<equiv> lift_state (repeatM n fresh)"

abbreviation (input) disjoint :: "'x list \<Rightarrow> 'x list \<Rightarrow> bool"
where "disjoint xs ys \<equiv> set xs \<inter> set ys = {}"

definition dlabels :: "'x tree \<Rightarrow> 'x list option"
where "dlabels = fold_tree (\<lambda>x. pure [x])
     (\<lambda>l r. pure (case_prod append) \<diamondop> (assert (case_prod disjoint) (pure Pair \<diamondop> l \<diamondop> r)))"

lemma dlabels_simps [simp]:
  "dlabels (Leaf x) = pure [x]"
  "dlabels (Node l r) = pure (case_prod append) \<diamondop> (assert (case_prod disjoint) (pure Pair \<diamondop> dlabels l \<diamondop> dlabels r))"
by(simp_all add: dlabels_def)

lemma correctness_applicative:
  assumes distinct: "\<And>n. pure (assert distinct) \<diamondop> symbols n = symbols n"
  shows "pure_state dlabels \<diamondop> label_tree t = symbols (leaves t)"
proof(induction t)
  case Leaf
  show ?case unfolding label_tree_simps leaves_simps One_nat_def repeatM.simps
    by applicative_nf simp
next
  case (Node l r)
  let ?cat = "case_prod append" and ?disj = "case_prod disjoint"
  have "pure_state dlabels \<diamondop> label_tree (Node l r) =
     pure (\<lambda>l r. pure ?cat \<diamondop> (assert ?disj (pure Pair \<diamondop> l \<diamondop> r))) \<diamondop>
       (pure dlabels \<diamondop> label_tree l) \<diamondop> (pure dlabels \<diamondop> label_tree r)"
    unfolding label_tree_simps by applicative_nf simp
  also have "\<dots> = pure (\<lambda>l r. pure ?cat \<diamondop> (assert ?disj (pure Pair \<diamondop> l \<diamondop> r))) \<diamondop>
    (pure (assert distinct) \<diamondop> symbols (leaves l)) \<diamondop> (pure (assert distinct) \<diamondop> symbols (leaves r))"
    unfolding Node.IH distinct ..
  also have "\<dots> = pure (assert distinct) \<diamondop> symbols (leaves (Node l r))"
    unfolding leaves_simps repeatM_plus by applicative_nf simp
  also have "\<dots> = symbols (leaves (Node l r))" by(rule distinct)
  finally show ?case .
qed

end

end