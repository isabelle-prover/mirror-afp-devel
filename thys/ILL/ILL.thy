section\<open>Intuitionistic Linear Logic\<close>

theory ILL
  imports
    Main
    "HOL-Combinatorics.Permutations"
begin

text\<open>
  Note that in this theory we often use procedural proofs rather than structured ones.
  We find these to be more informative about how the basic rules of the logic are used when
  compared to collecting all the rules in one call of an automated method.
\<close>

subsection\<open>Deep Embedding of Propositions\<close>

text\<open>
  We formalise ILL propositions as a datatype, parameterised by the type of propositional variables.
  The propositions are:
  \<^item> Propositional variables
  \<^item> Times of two terms, with unit @{text \<one>}
  \<^item> With of two terms, with unit @{text \<top>}
  \<^item> Plus of two terms, with unit @{text \<zero>}
  \<^item> Linear implication, with no unit
  \<^item> Exponential of a term
\<close>
datatype 'a ill_prop =
    Prop 'a
  | Times "'a ill_prop" "'a ill_prop" (infixr "\<otimes>" 90) | One ("\<one>")
  | With "'a ill_prop" "'a ill_prop" (infixr "&" 90) | Top ("\<top>")
  | Plus "'a ill_prop" "'a ill_prop" (infixr "\<oplus>" 90) | Zero ("\<zero>")
  | LImp "'a ill_prop" "'a ill_prop" (infixr "\<rhd>" 90)
    \<comment> \<open>Note that Isabelle font does not include $\multimap$, so we use @{text \<rhd>} instead\<close>
  | Exp "'a ill_prop" ("!" 1000)

(* Note: With syntax causes ambiguity, do the following to counteract it:
no_notation HOL.conj (infixr "&" 35)
 *)

subsection\<open>Shallow Embedding of Deductions\<close>

text\<open>
  See Bierman~\<^cite>\<open>"bierman-1994"\<close> or Kalvala and de~Paiva~\<^cite>\<open>"kalvala_depaiva-1995"\<close> for an
  overview of valid sequents in ILL.

  We first formalise ILL deductions as a relation between a list of propositions (anteceents) and a
  single proposition (consequent).
  This constitutes a shallow embedding of deductions (with a deep embedding to follow).

  In using a list, as opposed to a multiset, we make the exchange rule explicit.
  Furthermore, we take as primitive a rule exchanging two propositions and later derive both the
  corresponding rule for lists of propositions as well as for multisets.

  The specific formulation of rules we use here includes lists in more positions than is
  traditionally done when presenting ILL.
  This is inspired by the recommendations of Kalvala and de~Paiva, intended to improve pattern
  matching and automation.
\<close>
inductive sequent :: "'a ill_prop list \<Rightarrow> 'a ill_prop \<Rightarrow> bool" (infix "\<turnstile>" 60)
  where
  identity: "[a] \<turnstile> a"
| exchange: "\<lbrakk>G @ [a] @ [b] @ D \<turnstile> c\<rbrakk> \<Longrightarrow> G @ [b] @ [a] @ D \<turnstile> c"
| cut:      "\<lbrakk>G \<turnstile> b; D @ [b] @ E \<turnstile> c\<rbrakk> \<Longrightarrow> D @ G @ E \<turnstile> c"
| timesL:   "G @ [a] @ [b] @ D \<turnstile> c \<Longrightarrow> G @ [a \<otimes> b] @ D \<turnstile> c"
| timesR:   "\<lbrakk>G \<turnstile> a; D \<turnstile> b\<rbrakk> \<Longrightarrow> G @ D \<turnstile> a \<otimes> b"
| oneL:     "G @ D \<turnstile> c \<Longrightarrow> G @ [\<one>] @ D \<turnstile> c"
| oneR:     "[] \<turnstile> \<one>"
| limpL:    "\<lbrakk>G \<turnstile> a; D @ [b] @ E \<turnstile> c\<rbrakk> \<Longrightarrow> G @ D @ [a \<rhd> b] @ E \<turnstile> c"
| limpR:    "G @ [a] @ D \<turnstile> b \<Longrightarrow> G @ D \<turnstile> a \<rhd> b"
| withL1:   "G @ [a] @ D \<turnstile> c \<Longrightarrow> G @ [a & b] @ D \<turnstile> c"
| withL2:   "G @ [b] @ D \<turnstile> c \<Longrightarrow> G @ [a & b] @ D \<turnstile> c"
| withR:    "\<lbrakk>G \<turnstile> a; G \<turnstile> b\<rbrakk> \<Longrightarrow> G \<turnstile> a & b"
| topR:     "G \<turnstile> \<top>"
| plusL:    "\<lbrakk>G @ [a] @ D \<turnstile> c; G @ [b] @ D \<turnstile> c\<rbrakk> \<Longrightarrow> G @ [a \<oplus> b] @ D \<turnstile> c"
| plusR1:   "G \<turnstile> a \<Longrightarrow> G \<turnstile> a \<oplus> b"
| plusR2:   "G \<turnstile> b \<Longrightarrow> G \<turnstile> a \<oplus> b"
| zeroL:    "G @ [\<zero>] @ D \<turnstile> c"
| weaken:   "G @ D \<turnstile> b \<Longrightarrow> G @ [!a] @ D \<turnstile> b"
| contract: "G @ [!a] @ [!a] @ D \<turnstile> b \<Longrightarrow> G @ [!a] @ D \<turnstile> b"
| derelict: "G @ [a] @ D \<turnstile> b \<Longrightarrow> G @ [!a] @ D \<turnstile> b"
| promote:  "map Exp G \<turnstile> a \<Longrightarrow> map Exp G \<turnstile> !a"

lemmas [simp] = sequent.identity

subsection\<open>Proposition Equivalence\<close>

text\<open>Two propositions are equivalent when each can be derived from the other\<close>
definition ill_eq :: "'a ill_prop \<Rightarrow> 'a ill_prop \<Rightarrow> bool" (infix "\<stileturn>\<turnstile>" 60)
  where "a \<stileturn>\<turnstile> b = ([a] \<turnstile> b \<and> [b] \<turnstile> a)"

text\<open>We show that this is an equivalence relation\<close>
lemma ill_eq_refl [simp]:
  "a \<stileturn>\<turnstile> a"
  by (simp add: ill_eq_def)

lemma ill_eq_sym [sym]:
  "a \<stileturn>\<turnstile> b \<Longrightarrow> b \<stileturn>\<turnstile> a"
  by (smt ill_eq_def)

lemma ill_eq_tran [trans]:
  "\<lbrakk>a \<stileturn>\<turnstile> b; b \<stileturn>\<turnstile> c\<rbrakk> \<Longrightarrow> a \<stileturn>\<turnstile> c"
  using cut[of _ _ Nil Nil] by (simp add: ill_eq_def) blast

lemma "equivp ill_eq"
  by (metis equivpI ill_eq_refl ill_eq_sym ill_eq_tran reflp_def sympI transp_def)

lemma ill_eqI [intro]:
  "[a] \<turnstile> b \<Longrightarrow> [b] \<turnstile> a \<Longrightarrow> a \<stileturn>\<turnstile> b"
  using ill_eq_def by blast

lemma ill_eqE [elim]:
  "a \<stileturn>\<turnstile> b \<Longrightarrow> ([a] \<turnstile> b \<Longrightarrow> [b] \<turnstile> a \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: ill_eq_def)

lemma ill_eq_lr: "a \<stileturn>\<turnstile> b \<Longrightarrow> [a] \<turnstile> b"
  and ill_eq_rl: "a \<stileturn>\<turnstile> b \<Longrightarrow> [b] \<turnstile> a"
  by (simp_all add: ill_eq_def)

subsection\<open>Useful Rules\<close>

text\<open>
  We can derive a number of useful rules from the defining ones, especially their specific
  instantiations.

  Particularly useful is an instantiation of the Cut rule that makes it transitive, allowing us to
  use equational reasoning (@{command also} and @{command finally}) to build derivations using
  single propositions
\<close>
lemma simple_cut [trans]:
  "\<lbrakk>G \<turnstile> b; [b] \<turnstile> c\<rbrakk> \<Longrightarrow> G \<turnstile> c"
  using cut[of _ _ Nil Nil] by simp

lemma
  shows sequent_Nil_left: "[] @ G \<turnstile> c \<Longrightarrow> G \<turnstile> c"
    and sequent_Nil_right: "G @ [] \<turnstile> c \<Longrightarrow> G \<turnstile> c"
  by simp_all

lemma simple_exchange:
  "\<lbrakk>[a, b] \<turnstile> c\<rbrakk> \<Longrightarrow> [b, a] \<turnstile> c "
  using exchange[of Nil _ _ Nil] by simp

lemma simple_timesL:
  "\<lbrakk>[a] @ [b] \<turnstile> c\<rbrakk> \<Longrightarrow> [a \<otimes> b] \<turnstile> c"
  using timesL[of Nil] by simp

lemma simple_withL1: "\<lbrakk>[a] \<turnstile> c\<rbrakk> \<Longrightarrow> [a & b] \<turnstile> c"
  and simple_withL2: "\<lbrakk>[b] \<turnstile> c\<rbrakk> \<Longrightarrow> [a & b] \<turnstile> c"
  using withL1[of Nil] withL2[of Nil] by simp_all

lemma simple_plusL:
  "\<lbrakk>[a] \<turnstile> c; [b] \<turnstile> c\<rbrakk> \<Longrightarrow> [a \<oplus> b] \<turnstile> c"
  using plusL[of Nil] by simp

lemma simple_weaken:
  "[!a] \<turnstile> \<one>"
  using weaken[of Nil] oneR by simp

lemma simple_derelict:
  "\<lbrakk>[a] \<turnstile> b\<rbrakk> \<Longrightarrow> [!a] \<turnstile> b"
  using derelict[of Nil] by simp

lemmas simple_promote = promote[of "[_]", unfolded list.map]

lemma promote_and_derelict:
  assumes "G \<turnstile> c"
  shows "map Exp G \<turnstile> !c"
proof -
  have ind: "map Exp (take n G) @ drop n G \<turnstile> c" if n: "n \<le> length G" for n
    using n
  proof (induct n)
    case 0
    then show ?case using assms by simp
  next
    case (Suc m)
    moreover have "nth G m # drop (Suc m) G = drop m G"
      using Suc Cons_nth_drop_Suc Suc_le_lessD by blast
    moreover have "map Exp (take m G) @ [! (nth G m)] = map Exp (take (Suc m) G)"
      by (simp add: Suc Suc_le_lessD take_Suc_conv_app_nth)
    ultimately show ?case
      using derelict[of "map Exp (take m G)" "nth G m" "drop (Suc m) G" c]
      by simp (metis append.assoc append_Cons append_Nil)
  qed

  have "map Exp G \<turnstile> c"
    using ind[of "length G"] by simp
  then show ?thesis
    by (rule promote)
qed

lemmas dereliction = simple_derelict[OF identity]

lemma simple_contract:
  "\<lbrakk>[!a] @ [!a] \<turnstile> b\<rbrakk> \<Longrightarrow> [!a] \<turnstile> b"
  using contract[of Nil] by simp

lemma duplicate:
  "[!a] \<turnstile> !a \<otimes> !a"
  using identity simple_contract timesR by blast

lemma unary_promote:
  "\<lbrakk>[!g] \<turnstile> a\<rbrakk> \<Longrightarrow> [!g] \<turnstile> !a"
  by (metis (mono_tags, opaque_lifting) promote list.simps(8) list.simps(9))

lemma tensor:
  "\<lbrakk>[a] \<turnstile> b; [c] \<turnstile> d\<rbrakk> \<Longrightarrow> [a \<otimes> c] \<turnstile> b \<otimes> d"
  using simple_timesL timesR by blast

lemma ill_eq_tensor:
  "a \<stileturn>\<turnstile> b \<Longrightarrow> x \<stileturn>\<turnstile> y \<Longrightarrow> a \<otimes> x \<stileturn>\<turnstile> b \<otimes> y"
  by (simp add: ill_eq_def tensor)

lemma times_assoc:
  "[(a \<otimes> b) \<otimes> c] \<turnstile> a \<otimes> (b \<otimes> c)"
proof -
  have "[a] @ [b] @ [c] \<turnstile> a \<otimes> (b \<otimes> c)"
    by (rule timesR[OF identity timesR, OF identity identity])
  then have "[a \<otimes> b] @ [c] \<turnstile> a \<otimes> (b \<otimes> c)"
    by (metis timesL append_self_conv2)
  then show ?thesis
    by (simp add: simple_timesL)
qed

lemma times_assoc':
  "[a \<otimes> (b \<otimes> c)] \<turnstile> (a \<otimes> b) \<otimes> c"
proof -
  have "([a] @ [b]) @ [c] \<turnstile> (a \<otimes> b) \<otimes> c"
    by (rule timesR[OF timesR identity, OF identity identity])
  then have "[a] @ [b] @ [c] \<turnstile> (a \<otimes> b) \<otimes> c"
    by simp
  then show ?thesis
    using timesL[of "[a]" b c Nil] by (simp add: simple_timesL)
qed

lemma simple_limpR:
  "[a] \<turnstile> b \<Longrightarrow> [\<one>] \<turnstile> a \<rhd> b"
  using limpR[of Nil _ "[\<one>]"] oneL[of "[a]" Nil b] by simp

lemma simple_limpR_exp:
  "[a] \<turnstile> b \<Longrightarrow> [\<one>] \<turnstile> !(a \<rhd> b)"
proof -
  assume "[a] \<turnstile> b"
  then have "[] \<turnstile> a \<rhd> b"
    by (rule simple_cut[of Nil \<one> "a \<rhd> b", OF oneR simple_limpR])
  then have "[] \<turnstile> !(a \<rhd> b)"
    using promote[of Nil "a \<rhd> b"] by simp
  then show ?thesis
    using oneL[of Nil] by simp
qed

lemma limp_eval:
  "[a \<otimes> a \<rhd> b] \<turnstile> b"
  using limpL[of "[a]" a Nil] simple_timesL[of a] by simp

lemma timesR_intro:
  "\<lbrakk>G \<turnstile> a; D \<turnstile> b; G @ D = X\<rbrakk> \<Longrightarrow> X \<turnstile> a \<otimes> b"
  using timesR by metis

lemma explimp_eval:
  "[a \<otimes> !(a \<rhd> b)] \<turnstile> b \<otimes> !(a \<rhd> b)"
  apply (rule simple_timesL)
  apply (subst (2) append_Nil2[symmetric], subst append_assoc)
  apply (rule contract)
  apply (subst append_Nil2, subst append_assoc[symmetric])
  apply (rule timesR)

   apply (subst (2) append_Nil2[symmetric], subst append_assoc)
   apply (rule derelict)
   apply (subst (2) append_Nil[symmetric], subst append_assoc)
   apply (rule limpL)
    apply (rule identity)
   apply (subst append_Nil2, subst append_Nil)
   apply (rule identity)

  apply (rule identity)
  done

lemma plus_progress:
  "\<lbrakk>[a] \<turnstile> b; [c] \<turnstile> d\<rbrakk> \<Longrightarrow> [a \<oplus> c] \<turnstile> b \<oplus> d"
  using plusR1 plusR2 simple_plusL by blast

text\<open>
  The following set of rules are based on Proposition~1 of Bierman~\<^cite>\<open>"bierman-1994"\<close>.
  Where there is a direct correspondence, we include a comment indicating the specific item in the
  proposition.
\<close>

lemma swap: \<comment> \<open>Item 1\<close>
  "[a \<otimes> b] \<turnstile> b \<otimes> a"
proof -
  have "[b] @ [a] \<turnstile> b \<otimes> a"
    by (rule timesR[OF identity identity])
  then have "[a] @ [b] \<turnstile> b \<otimes> a"
    using simple_exchange by force
  then show ?thesis
    using simple_timesL by simp
qed

lemma unit: \<comment> \<open>Item 2\<close>
  "[a \<otimes> \<one>] \<turnstile> a"
  using oneL[of "[a]"] by (simp add: simple_timesL)

lemma unit': \<comment> \<open>Item 2\<close>
  "[a] \<turnstile> a \<otimes> \<one>"
  using timesR[of "[a]" a Nil \<one>] oneR by simp

lemma with_swap: \<comment> \<open>Item 3\<close>
  "[a & b] \<turnstile> b & a"
  using withL2[of Nil b] withL1[of Nil a] by (simp add: withR)

lemma with_top: \<comment> \<open>Item 4\<close>
  "a \<stileturn>\<turnstile> a & \<top>"
proof
  show "[a & \<top>] \<turnstile> a"
    by (simp add: simple_withL1)
next
  show "[a] \<turnstile> a & \<top>"
    by (rule withR[OF identity topR])
qed

lemma plus_swap: \<comment> \<open>Item 5\<close>
  "[a \<oplus> b] \<turnstile> b \<oplus> a"
  using plusL[of Nil a] by (simp add: plusR1 plusR2)

lemma plus_zero: \<comment> \<open>Item 6\<close>
  "a \<stileturn>\<turnstile> a \<oplus> \<zero>"
proof
  show "[a \<oplus> \<zero>] \<turnstile> a"
    using plusL[of Nil a] zeroL[of Nil _ a] by simp
next
  show "[a] \<turnstile> a \<oplus> \<zero>"
    by (simp add: plusR1)
qed

lemma with_distrib: \<comment> \<open>Item 7\<close>
  "[a \<otimes> (b & c)] \<turnstile> (a \<otimes> b) & (a \<otimes> c)"
  by (intro withR tensor identity simple_withL1 simple_withL2)

lemma plus_distrib: \<comment> \<open>Item 8\<close>
  "[a \<otimes> (b \<oplus> c)] \<turnstile> (a \<otimes> b) \<oplus> (a \<otimes> c)"
  using timesR[OF identity identity] plusL[of "[a]" b Nil _ c]
  by (metis append_Cons append_Nil plusR1 plusR2 simple_timesL)

lemma plus_distrib': \<comment> \<open>Item 9\<close>
  "[(a \<otimes> b) \<oplus> (a \<otimes> c)] \<turnstile> a \<otimes> (b \<oplus> c)"
  by (simp add: simple_plusL tensor plusR1 plusR2)

lemma times_exp: \<comment> \<open>Item 10\<close>
  "[!a \<otimes> !b] \<turnstile> !(a \<otimes> b)"
proof -
  have "[a, b] \<turnstile> a \<otimes> b"
    using timesR[of "[a]"] by simp
  then have "[!a, !b] \<turnstile> a \<otimes> b"
    by (metis derelict append_Cons append_Nil)
  then have "[!a, !b] \<turnstile> !(a \<otimes> b)"
    by (metis (mono_tags, opaque_lifting) promote list.simps(8) list.simps(9))
  then show ?thesis
    by (simp add: simple_timesL)
qed

lemma one_exp: \<comment> \<open>Item 10\<close>
  "\<one> \<stileturn>\<turnstile> !(\<one>)"
  by (meson ill_eq_def simple_cut simple_limpR_exp simple_weaken unary_promote)

lemma \<comment> \<open>Item 11\<close>
  "[!a] \<turnstile> \<one> & a & (!a \<otimes> !a)"
  by (metis identity withR simple_weaken simple_derelict simple_contract timesR)

lemma \<comment> \<open>Item 12\<close>
  "!a \<otimes> !b \<stileturn>\<turnstile> !(a & b)"
proof
  show "[!a \<otimes> !b] \<turnstile> !(a & b)"
  proof -
    have "[!a, !b] \<turnstile> a & b"
    proof (rule withR)
      show "[! a, ! b] \<turnstile> a"
        using weaken[of "[!a]"] dereliction[of a] by simp
    next
      show "[! a, ! b] \<turnstile> b"
        using weaken[of "[!b]"] dereliction[of b] simple_exchange[of "!b" "!a"] by simp
    qed
    then show ?thesis
      using promote simple_timesL
      by (metis (mono_tags, opaque_lifting) append_Cons append_Nil list.simps(8) list.simps(9))
  qed
next
  show "[!(a & b)] \<turnstile> !a \<otimes> !b"
  proof (rule simple_contract, rule timesR)
    show "[! (a & b)] \<turnstile> ! a"
      by (simp add: unary_promote simple_derelict simple_withL1)
  next
    show "[! (a & b)] \<turnstile> ! b"
      by (simp add: unary_promote simple_derelict simple_withL2)
  qed
qed

lemma \<comment> \<open>Item 13\<close>
  "\<one> \<stileturn>\<turnstile> !(\<top>)"
proof
  show "[\<one>] \<turnstile> !(\<top>)"
    using simple_cut simple_limpR_exp topR unary_promote by blast
next
  show "[!(\<top>)] \<turnstile> \<one>"
    by (rule simple_weaken)
qed

subsection\<open>Compacting Lists of Propositions\<close>

text\<open>
  Compacting transforms a list of propositions into a single proposition using the @{const Times}
  operator, taking care to not expand the size when given a list with only one element.
  This operation allows us to link the meta-level antecedent concatenation with the object-level
  @{const Times} operator, turning a list of antecedents into a single proposition with the same
  power in proofs.
\<close>
function compact :: "'a ill_prop list \<Rightarrow> 'a ill_prop"
  where
    "xs \<noteq> [] \<Longrightarrow> compact (x # xs) = x \<otimes> compact xs"
  | "xs = [] \<Longrightarrow> compact (x # xs) = x"
  | "compact [] = \<one>"
  by (metis list.exhaust) simp_all
termination by (relation "measure length", auto)

text\<open>For code generation we use an if statement\<close>
lemma compact_code [code]:
  "compact [] = \<one>"
  "compact (x # xs) = (if xs = [] then x else x \<otimes> compact xs)"
  by simp_all

text\<open>
  Two lists of propositions that compact to the same result must be equal if they do not include any
  @{const Times} or @{const One} elements.
  We show first that they must be equally long and then that they must be equal.
\<close>
lemma compact_eq_length:
  assumes "\<And>a. a \<in> set xs \<Longrightarrow> a \<noteq> \<one>"
      and "\<And>a. a \<in> set ys \<Longrightarrow> a \<noteq> \<one>"
      and "\<And>a u v. a \<in> set xs \<Longrightarrow> a \<noteq> u \<otimes> v"
      and "\<And>a u v. a \<in> set ys \<Longrightarrow> a \<noteq> u \<otimes> v"
      and "compact xs = compact ys"
    shows "length xs = length ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case
    by simp (metis ill_prop.simps(24) list.set_intros(1) compact.elims compact.simps(2))
next
  case xs: (Cons a xs)
  then show ?case
  proof (cases ys)
    case Nil
    then have False
      using xs by simp (metis compact.simps(1,2) ill_prop.distinct(17))
    then show ?thesis
      by metis
  next
    case (Cons a list)
    then show ?thesis
      using xs by simp (metis ill_prop.inject(2) compact.simps(1,2))
  qed
qed

lemma compact_eq:
  assumes "\<And>a. a \<in> set xs \<Longrightarrow> a \<noteq> \<one>"
      and "\<And>a. a \<in> set ys \<Longrightarrow> a \<noteq> \<one>"
      and "\<And>a u v. a \<in> set xs \<Longrightarrow> a \<noteq> u \<otimes> v"
      and "\<And>a u v. a \<in> set ys \<Longrightarrow> a \<noteq> u \<otimes> v"
      and "compact xs = compact ys"
    shows "xs = ys"
proof -
  have "length xs = length ys"
    using assms by (rule compact_eq_length)
  then show ?thesis
    using assms
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case xs: (Cons a xs)
    then show ?case
    proof (cases ys)
      case Nil
      then show ?thesis using xs by simp
    next
      case (Cons a list)
      then show ?thesis
        using xs by simp (metis ill_prop.inject(2) compact.simps(1,2))
    qed
  qed
qed

text\<open>Compacting to @{const ILL.One} means the list of propositions was either empty or just that\<close>
lemma compact_eq_oneE:
  assumes "compact xs = \<one>"
  obtains "xs = []" | "xs = [\<one>]"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp (metis compact.simps(1,2) ill_prop.distinct(17))
qed

text\<open>
  Compacting to @{const ILL.Times} means the list of propositions was either just that or started
  with the left-hand proposition and the rest compacts to the right-hand proposition
\<close>
lemma compact_eq_timesE:
  assumes "compact xs = x \<otimes> y"
  obtains "xs = [x \<otimes> y]" | ys where "xs = x # ys" and "compact ys = y"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp (metis compact.simps(1,2) ill_prop.inject(2))
qed

text\<open>
  Compacting to anything but @{const ILL.One} or @{const ILL.Times} means the list was just that
\<close>
lemma compact_eq_otherD:
  assumes "compact xs = a"
      and "\<And>x y. a \<noteq> x \<otimes> y"
      and "a \<noteq> \<one>"
    shows "xs = [a]"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp (metis compact_code(2))
qed

text\<open>For any list of propositions, we can derive its compacted form from it\<close>
lemma identity_list:
  "G \<turnstile> (compact G)"
proof (induction G rule: induct_list012)
     case 1 then show ?case by (simp add: oneR)
next case (2 a) then show ?case by simp
next case (3 a b G) then show ?case using timesR[OF identity] by simp
qed

text\<open>For any valid sequent, we can compact any sublist of its antecedents without invalidating it\<close>
lemma compact_split_antecedents:
  assumes "X @ G @ Y \<turnstile> c"
    shows "n \<le> length G \<Longrightarrow> X @ take (length G - n) G @ [compact (drop (length G - n) G)] @ Y \<turnstile> c"
proof (induct n)
  case 0
  then show ?case
    using oneL[of "X @ G"] assms by simp
next
  case (Suc n)
  then obtain as x bs where G: "G = as @ [x] @ bs" and bs: "length bs = n"
    by (metis Suc_length_conv append_Cons append_Nil append_take_drop_id diff_diff_cancel
              length_drop)

  have "X @ take (length G - n) G @ [compact (drop (length G - n) G)] @ Y \<turnstile> c"
    using Suc by simp
  then show ?case
    using timesL[of "X @ as" x "compact bs" Y c, simplified] G Suc.prems assms bs
    using Suc_diff_le Suc_leD Suc_le_D append.assoc append_Cons append_Nil append_eq_append_conv
          append_take_drop_id butlast_snoc diff_Suc_Suc diff_diff_cancel diff_less length_drop
          take_hd_drop compact.simps(1) compact.simps(2) zero_less_Suc
    by (smt (verit, ccfv_threshold))
qed

text\<open>More generally, compacting a sublist of antecedents does not affect sequent validity\<close>
lemma compact_antecedents:
  "(X @ [compact G] @ Y \<turnstile> c) = (X @ G @ Y \<turnstile> c)"
proof
  assume "X @ [compact G] @ Y \<turnstile> c"
  then show "X @ G @ Y \<turnstile> c"
    using identity_list cut by blast
next
  assume "X @ G @ Y \<turnstile> c"
  then show "X @ [compact G] @ Y \<turnstile> c"
    using compact_split_antecedents[where n = "length G"] by fastforce
qed

text\<open>Times with a single proposition can be absorbed into compacting up to proposition equivalence\<close>
lemma times_equivalent_cons:
  "a \<otimes> compact b \<stileturn>\<turnstile> compact (a # b)"
proof (cases b)
  case Nil then show ?thesis by (simp add: ill_eq_def unit unit')
next
  case (Cons a list) then show ?thesis by simp
qed

text\<open>Times of compacted lists is equivalent to compacting the appended lists\<close>
lemma times_equivalent_append:
  "compact a \<otimes> compact b \<stileturn>\<turnstile> compact (a @ b)"
proof (induct a)
  case Nil
  then show ?case
    using simple_cut[OF swap unit] simple_cut[OF unit' swap] ill_eqI by (simp, blast)
next
  case assm: (Cons a1 a2)
  have "compact (a1 # a2) \<otimes> compact b \<stileturn>\<turnstile> (a1 \<otimes> compact a2) \<otimes> compact b"
    by (simp add: times_equivalent_cons ill_eq_sym ill_eq_tensor)
  also have "... \<stileturn>\<turnstile> a1 \<otimes> (compact a2 \<otimes> compact b)"
    by (simp add: times_assoc times_assoc' ill_eqI)
  also have "... \<stileturn>\<turnstile> a1 \<otimes> compact (a2 @ b)"
    using ill_eq_tensor[OF _ assm] by simp
  finally show ?case
    by (simp add: ill_eq_tran times_equivalent_cons)
qed

text\<open>Any number of single-antecedent sequents can be compacted with the rule @{thm tensor}\<close>
lemma compact_sequent:
  "\<forall>x \<in> set xs. [f x] \<turnstile> g x \<Longrightarrow> [compact (map f xs)] \<turnstile> compact (map g xs)"
proof (induct xs rule: induct_list012)
     case 1 then show ?case by simp
next case (2 x) then show ?case by simp
next case (3 x y zs) then show ?case by (simp add: tensor)
qed

text\<open>Any number of equivalences can be compacted together\<close>
lemma compact_equivalent:
  "\<forall>x \<in> set xs. f x \<stileturn>\<turnstile> g x \<Longrightarrow> compact (map f xs) \<stileturn>\<turnstile> compact (map g xs)"
  by (simp add: ill_eqI[OF compact_sequent compact_sequent] ill_eq_lr ill_eq_rl)

subsection\<open>Multiset Exchange\<close>

text\<open>
  Recall that our @{const sequent} definition uses explicit single-proposition exchange.
  We now derive a rule for exchanging lists of propositions and then a rule that uses multisets to
  disregard the antecedent order entirely.
\<close>

text\<open>We can exchange lists of propositions by stepping through @{const compact}\<close>
lemma exchange_list:
  "G @ A @ B @ D \<turnstile> c \<Longrightarrow> G @ B @ A @ D \<turnstile> c"
proof -
  assume "G @ A @ B @ D \<turnstile> c"
  then have "G @ [compact A] @ B @ D \<turnstile> c"
    using compact_antecedents by force
  then have "G @ [compact A] @ [compact B] @ D \<turnstile> c"
    using compact_antecedents[where X = "G @ [compact A]" and G = B] by force
  then have "G @ [compact B] @ [compact A] @ D \<turnstile> c"
    using exchange by simp
  then have "G @ [compact B] @ A @ D \<turnstile> c"
    using compact_antecedents[where X = "G @ [compact B]" and G = A] by force
  then show ?thesis
    using compact_antecedents by force
qed

lemma simple_exchange_list:
  "\<lbrakk>A @ B \<turnstile> c\<rbrakk> \<Longrightarrow> B @ A \<turnstile> c "
  using exchange_list[of Nil _ _ Nil] by simp

text\<open>By applying the list exchange rule multiple times, the lists do not need to be adjacent\<close>
lemma exchange_separated:
  "G @ A @ X @ B @ D \<turnstile> c \<Longrightarrow> G @ B @ X @ A @ D \<turnstile> c"
  by (metis append.assoc exchange_list)

text\<open>Single transposition in the antecedents does not invalidate a sequent\<close>
lemma exchange_transpose:
  assumes "G \<turnstile> c"
      and "a \<in> {..<length G}"
      and "b \<in> {..<length G}"
    shows "permute_list (transpose a b) G \<turnstile> c"
proof -
  consider "a < b" | "a = b" | "b < a"
    using not_less_iff_gr_or_eq by blast
  moreover { fix x y
    assume x_in [simp]: "x \<in> {..<length G}"
       and y_in [simp]: "y \<in> {..<length G}"
       and xy [arith]: "x < y"

    have "G = take x G @ drop x G"
      by simp
    also have "... = take x G @ nth G x # drop (Suc x) G"
      by simp (metis x_in id_take_nth_drop lessThan_iff)
    also have "... = take x G @ nth G x # take (y - Suc x) (drop (Suc x) G) @ drop y G"
      by simp (metis Suc_leI add.commute append_take_drop_id drop_drop le_add_diff_inverse xy)
    also have
      "... = take x G @ nth G x # take (y - Suc x) (drop (Suc x) G) @ nth G y # drop (Suc y) G"
      by simp (metis Cons_nth_drop_Suc y_in lessThan_iff)
    finally have G:
      "G = take x G @ nth G x # take (y - Suc x) (drop (Suc x) G) @ nth G y # drop (Suc y) G" .

    have "take x G @ [nth G y] @ take (y - Suc x) (drop (Suc x) G) @ [nth G x] @ drop (Suc y) G \<turnstile> c"
      by (rule exchange_separated, simp add: G[symmetric] assms(1))
    moreover have
      " permute_list (transpose x y) G
      = take x G @ nth G y # take (y - Suc x) (drop (Suc x) G) @ nth G x # drop (Suc y) G"
      unfolding list_eq_iff_nth_eq drop_Suc
    proof safe
      show
        " length (permute_list (Transposition.transpose x y) G)
        = length (take x G @ nth G y # take (y - Suc x) (drop x (tl G)) @ nth G x # drop y (tl G))"
        using y_in by simp
    next
      fix i
      assume "i < length (permute_list (Transposition.transpose x y) G)"
      then show "nth (permute_list (Transposition.transpose x y) G) i =
            nth (take x G @ nth G y # take (y - Suc x) (drop x (tl G)) @ nth G x # drop y (tl G)) i"
        by (simp add: permute_list_def transpose_def nth_append min_diff nth_tl)
    qed
    ultimately have "permute_list (transpose x y) G \<turnstile> c"
      by simp
  }
  ultimately show ?thesis
    using assms by (metis permute_list_id transpose_commute transpose_same)
qed

text\<open>
  More generally, by transposition being involutive, a single antecedent transposition does not
  affect sequent validity
\<close>
lemma exchange_permute_eq:
  assumes "a \<in> {..<length G}"
      and "b \<in> {..<length G}"
    shows "permute_list (transpose a b) G \<turnstile> c = G \<turnstile> c"
  using assms exchange_transpose transpose_comp_involutory
  by (metis length_permute_list permute_list_compose permute_list_id permutes_swap_id)

text\<open>
  Validity of a sequent is not affected by replacing any antecedent sublist with a list that
  represents the same multiset.
  This is because lists representing equal multisets are connected by a permutation, which is a
  sequence of transpositions and as such does not affect validity.
\<close>
lemma exchange_mset:
  "mset A = mset B \<Longrightarrow> G @ A @ D \<turnstile> c = G @ B @ D \<turnstile> c"
proof -
  { fix X Y :: "'a ill_prop list"
    assume "X \<turnstile> c" and "mset X = mset Y"
    then have "Y \<turnstile> c"
    proof (elim mset_eq_permutation)
      fix p
      assume "p permutes {..<length Y}"
      moreover have "finite {..<length Y}"
        by simp
      moreover assume "X \<turnstile> c" and "permute_list p Y = X"
      ultimately show "Y \<turnstile> c"
      proof (induct arbitrary: X rule: permutes_rev_induct)
        case id then show ?case by simp
      next
        case (swap a b p)
        then show ?case
          by (metis permute_list_compose permutes_swap_id length_permute_list exchange_permute_eq)
      qed
    qed
  } note base = this

  show "mset A = mset B \<Longrightarrow> G @ A @ D \<turnstile> c = G @ B @ D \<turnstile> c"
    by (standard ; simp add: base)
qed

subsection\<open>Additional Lemmas\<close>

text\<open>
  These rules are based on Figure~2 of Kalvala and de~Paiva~\<^cite>\<open>"kalvala_depaiva-1995"\<close>, labelled
  by them as ``additional rules for proof search''.
  We present them out of order because we use some in the proofs of the others, but annotate them
  with the original labels as comments.
\<close>

lemma ill_mp1: \<comment> \<open>@{text mp\<^sub>1}\<close>
  assumes "A @ [b] @ B @ C \<turnstile> c"
    shows "A @ [a] @ B @ [a \<rhd> b] @ C \<turnstile> c"
proof -
  have "[a] @ [a \<rhd> b] \<turnstile> b"
    using limpL[of "[a]" a Nil] by simp
  then have "A @ [a] @ [a \<rhd> b] @ B @ C \<turnstile> c"
    using assms cut[of _ b A "B @ C" c] by force
  then show ?thesis
    using exchange_list[of "A @ [a]" "[a \<rhd> b]"] by simp
qed

lemmas simple_mp1 = ill_mp1[of Nil _ Nil Nil, simplified, OF identity]

lemma \<comment> \<open>@{text raa\<^sub>1}\<close>
  "G @ [!b] @ D @ [!b \<rhd> \<zero>] @ E \<turnstile> a"
  using zeroL ill_mp1 by blast

lemma ill_mp2: \<comment> \<open>@{text mp\<^sub>2}\<close>
  assumes "A @ [b] @ B @ C \<turnstile> c"
    shows "A @ [a \<rhd> b] @ B @ [a] @ C \<turnstile> c"
  using ill_mp1[OF assms] exchange_list by (metis append.assoc)

lemmas simple_mp2 = ill_mp2[of Nil _ Nil Nil, simplified, OF identity]

lemma \<comment> \<open>@{text raa\<^sub>2}\<close>
  "G @ [!b \<rhd> \<zero>] @ D @ [!b] @ P \<turnstile> A"
  using zeroL ill_mp2 by blast

lemma \<comment> \<open>@{text "\<otimes>_&"}\<close>
  assumes "G @ [(!a \<rhd> \<zero>) & (!b \<rhd> \<zero>)] @ D \<turnstile> c"
    shows "G @ [!(!(a \<oplus> b) \<rhd> \<zero>)] @ D \<turnstile> c"
proof -
  note exp_injL = unary_promote[OF simple_derelict, OF plusR1[OF identity, of a b]]
   and exp_injR = unary_promote[OF simple_derelict, OF plusR2[OF identity, of b a]]
  have "[!(!(a \<oplus> b) \<rhd> \<zero>)] \<turnstile> (!a \<rhd> \<zero>) & (!b \<rhd> \<zero>)"
    apply (rule withR ; rule simple_derelict , rule limpR[of Nil, simplified])
     apply (rule cut[OF exp_injL, of Nil, simplified], rule simple_mp1)
     apply (rule cut[OF exp_injR, of Nil, simplified], rule simple_mp1)
    done
  then show ?thesis
    using assms cut by blast
qed

lemma \<comment> \<open>@{text "&_lemma"}\<close>
  assumes "G @ [!a, !b] @ D \<turnstile> c"
    shows "G @ [!(a & b)] @ D \<turnstile> c"
proof -
  have as: "[!(a & b)] \<turnstile> !a"
    apply (rule unary_promote)
    apply (rule simple_derelict)
    by (rule simple_withL1[OF identity])
  have bs: "[!(a & b)] \<turnstile> !b"
    apply (rule unary_promote)
    apply (rule simple_derelict)
    by (rule simple_withL2[OF identity])
  show ?thesis
    apply (rule contract)
    using cut[OF as, of G "[!b] @ D" c] cut[OF bs, of "G @ [!(a & b)]" D c] assms
    by simp
qed

lemma \<comment> \<open>$\multimap_L$@{text "_lemma"}\<close>
  assumes "G @ D \<turnstile> a"
  shows "G @ [!(a \<rhd> b)] @ D \<turnstile> b"
  apply (rule derelict)
  using exchange_list[of G D "[a \<rhd> b]" Nil b, simplified]
        limpL[OF assms, of Nil b Nil b, simplified]
  by simp

lemma \<comment> \<open>$\multimap_R$@{text "_lemma"}\<close>
  assumes "[a, !a] @ G \<turnstile> b"
  shows "G \<turnstile> !a \<rhd> b"
  apply (rule limpR[of _ _ Nil, simplified])
  apply (rule exchange_list[of Nil "[!a]" _ Nil, simplified])
  apply (rule contract[of Nil, simplified])
  apply (rule derelict[of Nil, simplified])
  using assms by simp

lemma \<comment> \<open>@{text "a_not_a"}\<close>
  assumes "G @ [!a \<rhd> \<zero>] @ D \<turnstile> b"
  shows "G @ [!a \<rhd> (!a \<rhd> \<zero>)] @ D \<turnstile> b"
proof -
  have "[!a \<rhd> (!a \<rhd> \<zero>)] \<turnstile> !a \<rhd> \<zero>"
    apply (rule limpR[of _ _ Nil, simplified])
    apply (rule contract[of _ _ Nil, simplified])
    apply simp
    apply (rule ill_mp2[of Nil _  Nil "[!a]", simplified])
    by (rule simple_mp2)
  then show ?thesis
    using cut[OF _ assms] by blast
qed

end
