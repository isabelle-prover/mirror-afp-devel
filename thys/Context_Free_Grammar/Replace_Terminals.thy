(*<*)
theory Replace_Terminals
  imports Context_Free_Grammar.Expansion
begin
(*>*)

section \<open>Replacing Terminals by (Fresh) Nonterminals\<close>

text \<open>Some code setup for partial maps.\<close>

declare dom_empty[code_unfold]

lemma dom_upd[code_unfold]: "dom (f(x\<mapsto>y)) = insert x (dom f)"
  by simp

value "dom [0::int \<mapsto> 10::nat, 1 \<mapsto> 11, 2 \<mapsto> 12]"

lemma ranE: "y \<in> ran f \<Longrightarrow> (\<And>x. f x = Some y \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: ran_def)

lemma Rhss_image_Pair_inj_on:
  assumes f: "inj_on f X" and x: "x \<in> X"
  shows "Rhss ((\<lambda>x. (f x, g x)) ` X) (f x) = {g x}"
  using inj_onD[OF f] x by (auto simp: Rhss_def)

text \<open>First, we define the grammar where fresh nonterminals produce the corresponding terminals.
We abstract the partial map from terminals to the fresh nonterminals by \<open>f\<close>.\<close>

definition Replace_Tm_new :: "('t \<rightharpoonup> 'n) \<Rightarrow> ('n,'t) Prods" where
"Replace_Tm_new f = {(A,[Tm a]) | A a. f a = Some A}"

lemma Replace_Tm_new_code[code_unfold]: "Replace_Tm_new f = (\<lambda>a. (the (f a), [Tm a])) ` dom f"
  by (force simp: Replace_Tm_new_def)

value "Replace_Tm_new [0::int \<mapsto> 10::nat, 1 \<mapsto> 11, 2 \<mapsto> 12]"

definition replace_Tm_new :: "('t \<times> 'n) list \<Rightarrow> ('n,'t) prods" where
"replace_Tm_new f = [(A,[Tm a]). (a,A) \<leftarrow> f]"

lemma set_replace_Tm_new:
"distinct (map fst f) \<Longrightarrow> set (replace_Tm_new f) = Replace_Tm_new (map_of f)"
  by (auto simp: replace_Tm_new_def Replace_Tm_new_def)

text \<open>Admissible replacements can choose to replace or preserve each terminal.\<close>

definition Replace_Tm_sym_ops :: "('t \<rightharpoonup> 'n) \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) syms set" where
"Replace_Tm_sym_ops f x =
  insert [x] (case x of Tm a \<Rightarrow> (case f a of Some A \<Rightarrow> {[Nt A]} | _ \<Rightarrow> {}) | _ \<Rightarrow> {})"

fun Replace_Tm_syms_ops :: "('t \<rightharpoonup> 'n) \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms set" where
  "Replace_Tm_syms_ops f [] = {[]}"
| "Replace_Tm_syms_ops f (x#xs) =
   Replace_Tm_sym_ops f x @@ Replace_Tm_syms_ops f xs"

definition Replace_Tm_ops :: "('t \<rightharpoonup> 'n) \<Rightarrow> (('n,'t) syms \<Rightarrow> ('n,'t) syms) set" where
"Replace_Tm_ops f = {g. \<forall>\<alpha>. g \<alpha> \<in> Replace_Tm_syms_ops f \<alpha>}"

definition Replace_Tm :: "('t \<rightharpoonup> 'n) \<Rightarrow> (('n,'t) syms \<Rightarrow> ('n,'t) syms) \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"Replace_Tm f g P = {(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} \<union> Replace_Tm_new f"

definition replace_Tm :: "('t \<times> 'n) list \<Rightarrow> (('n,'t) syms \<Rightarrow> ('n,'t) syms) \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
"replace_Tm f g P = [(A, g \<alpha>). (A,\<alpha>) \<leftarrow> P] @ replace_Tm_new f"

lemma set_replace_Tm:
  "distinct (map fst f) \<Longrightarrow> set (replace_Tm f g P) = Replace_Tm (map_of f) g (set P)"
  by (auto simp: replace_Tm_def Replace_Tm_def set_tms set_replace_Tm_new)

lemma Replace_Tm_code[code_unfold]:
  "Replace_Tm f = (let Q = Replace_Tm_new f in (\<lambda>g P. map_prod id g ` P \<union> Q))"
  by (force simp: Replace_Tm_def)

value "Replace_Tm [0::int \<mapsto> 10::nat, 1 \<mapsto> 11, 2 \<mapsto> 12] g P"

text \<open>Expansion with respect to the grammar @{const Replace_Tm_new} should
revert the fresh nonterminals to the original terminals,
while preserving terminals and locked nonterminals.\<close>

lemma Rhss_Replace_Tm_new:
  assumes inj: "inj_on f (dom f)" and fa: "f a = Some A"
  shows "Rhss (Replace_Tm_new f) A = {[Tm a]}"
  using inj_onD[OF inj] fa
  by (auto simp add: domIff notin_Lhss_iff_Rhss Replace_Tm_new_def Rhss_def)

lemma Expand_sym_Replace_Tm_Tm:
  "Expand_sym (Replace_Tm_new f) X (Tm a) = {[Tm a]}"
  by (auto simp: Expand_sym_def)

lemma Expand_sym_Replace_Tm_Nt:
  assumes A: "A \<notin> X"
  shows "Expand_sym (Replace_Tm_new f) X (Nt A) = {[Nt A]}"
  using A by (auto simp: Expand_sym_def)

lemma Expand_sym_Replace_Tm_new:
  assumes inj: "inj_on f (dom f)" and a: "f a = Some A" and A: "A \<in> X"
  shows "Expand_sym (Replace_Tm_new f) X (Nt A) = {[Tm a]}"
  using A by (auto simp: Expand_sym_def Rhss_Replace_Tm_new[OF inj a])

lemma Expand_all_syms_Replace_Tm_ops:
  assumes inj: "inj_on f (dom f)"
    and X: "ran f \<subseteq> X" and \<alpha>: "X \<inter> Nts_syms \<alpha> = {}" "\<beta> \<in> Replace_Tm_syms_ops f \<alpha>"
  shows "Expand_all_syms (Replace_Tm_new f) X \<beta> = {\<alpha>}"
proof (insert \<alpha>, induction \<alpha> arbitrary: \<beta>)
  case Nil
  then show ?case by simp
next
  case (Cons x \<alpha>)
  then have "X \<inter> Nts_syms \<alpha> = {}" by auto
  note IH = Cons.IH[OF this]
  show ?case
  proof (cases x)
    case [simp]: (Nt A)
    from Cons.prems X have "A \<notin> X" by auto
    with Cons.prems(2)
    show ?thesis
      by (auto simp: Replace_Tm_sym_ops_def insert_conc Expand_sym_Replace_Tm_Nt IH)
  next
    case [simp]: (Tm a)
    from X have AX: "f a = Some A \<Longrightarrow> A \<in> X" for A by (auto simp: ranI)
    with Cons.prems(2)
    show ?thesis
      by (auto simp: Replace_Tm_sym_ops_def insert_conc IH
          Expand_sym_Replace_Tm_Tm Expand_sym_Replace_Tm_new[OF inj]
          split: option.splits)
  qed
qed

lemma Expand_all_Replace_Tm_ops:
  assumes g: "g \<in> Replace_Tm_ops f" and inj: "inj_on f (dom f)"
    and f: "ran f \<subseteq> X" and X: "X \<inter> Rhs_Nts P = {}"
  shows "Expand_all (Replace_Tm_new f) X {(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} = P"
proof-
  have *: "(A,\<alpha>) \<in> P \<Longrightarrow> Expand_all_syms (Replace_Tm_new f) X (g \<alpha>) = {\<alpha>}" for A \<alpha>
    apply (rule Expand_all_syms_Replace_Tm_ops[OF inj f])
    using X g by (auto simp: Tms_def Rhs_Nts_def Replace_Tm_ops_def)
  then show ?thesis by (force simp: Expand_def)
qed

text \<open>Admissible replacements preserves the language, because
expanding the replaced grammar results in the original grammar,
and expansion preserves the language.\<close>

theorem Lang_Replace_Tm:
  assumes g: "g \<in> Replace_Tm_ops f"
    and inj: "inj_on f (dom f)"
    and disj: "ran f \<inter> Nts P = {}"
    and A: "A \<notin> ran f"
  shows "Lang (Replace_Tm f g P) A = Lang P A"
    (is "?l = ?r")
proof-
  have "?l = Lang ({(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} \<union> Replace_Tm_new f) A"
    by (simp add: Replace_Tm_def)
  also have "\<dots> = Lang (Expand_all (Replace_Tm_new f) (ran f) {(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} \<union> Replace_Tm_new f) A"
    apply (subst Lang_Expand_all_Un)
    using disj by (auto simp: Nts_def Lhss_def)
  also have "\<dots> = Lang (P \<union> Replace_Tm_new f) A"
    apply (subst Expand_all_Replace_Tm_ops[OF g inj])
    using disj
    by (auto simp: Nts_Lhss_Rhs_Nts)
  also have "\<dots> = ?r"
    apply (rule Lang_Un_disj_Lhss) using disj A
    by (auto simp: Replace_Tm_new_def Lhss_Collect Nts_Lhss_Rhs_Nts ran_def)
  finally show ?thesis.
qed

subsection \<open>Mapping to Fresh Nonterminals\<close>

text \<open>We provide an implementation of a function that maps terminals to corresponding
fresh nonterminals.\<close>

fun fresh_map :: "'a :: fresh0 set \<Rightarrow> 'b list \<Rightarrow> 'b \<rightharpoonup> 'a" where
  "fresh_map A [] = Map.empty"
| "fresh_map A (x#xs) = (let a = fresh0 A in (fresh_map (insert a A) xs)(x \<mapsto> a))"

lemma dom_fresh_map[code_unfold]: "dom (fresh_map A xs) = set xs"
  by (induction xs arbitrary: A, simp_all add: Let_def)

fun fresh_assoc :: "'a :: fresh0 set \<Rightarrow> 'b list \<Rightarrow> ('b \<times> 'a) list" where
  "fresh_assoc A [] = []"
| "fresh_assoc A (x#xs) = (let a = fresh0 A in (x,a) # fresh_assoc (insert a A) xs)"

lemma map_of_fresh_assoc: "distinct xs \<Longrightarrow> map_of (fresh_assoc A xs) = fresh_map A xs"
  by (induction xs arbitrary: A, auto simp: Let_def)

lemma map_fst_fresh_assoc: "map fst (fresh_assoc A xs) = xs"
  by (induction xs arbitrary: A, auto simp: Let_def)

lemma fst_set_fresh_assoc: "fst ` set (fresh_assoc A xs) = set xs"
  by (simp flip: set_map add: map_fst_fresh_assoc)

lemma fresh_map_notIn: "finite A \<Longrightarrow> fresh_map A xs x = Some a \<Longrightarrow> a \<notin> A"
  by (induction xs arbitrary: A; force simp: Let_def fresh0_notIn split: if_splits)

lemma fresh_map_imp_in: "fresh_map A xs x = Some a \<Longrightarrow> x \<in> set xs"
  by (induction xs arbitrary: A; simp add: Let_def split: if_splits) 

lemma fresh_map_disj: assumes fin: "finite A" shows "ran (fresh_map A xs) \<inter> A = {}"
  by (auto simp: fresh_map_notIn[OF fin, of xs] elim!: ranE)

lemma fresh_map_inj_on: "finite A \<Longrightarrow> inj_on (fresh_map A xs) (set xs)"
proof (induction xs arbitrary: A)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  define a where "a = fresh0 A"
  from Cons
  have IH: "inj_on (fresh_map (insert a A) xs) (set xs)"
    and fin: "finite (insert a A)" by auto
  { fix y b assume "y \<in> set xs" and fy: "fresh_map (insert a A) xs y = Some b"
    from fresh_map_notIn[OF fin fy]
    have "b \<notin> A" "a \<noteq> b" by auto
  } note * = this this(2)[symmetric]
  show ?case
    apply (auto simp flip: a_def intro!: inj_onI split: if_splits simp: inj_onD[OF IH])
    using *(2) apply auto[]
    using "*"(2) apply metis
    using "*"(3) by metis
qed

lemma fresh_map_inj_onI: "finite A \<Longrightarrow> X \<subseteq> set xs \<Longrightarrow> inj_on (fresh_map A xs) X"
  using inj_on_subset[OF fresh_map_inj_on].

lemma fresh_map_distinct:
  assumes fin: "finite A"
  shows "distinct (map (fresh_map A xs) xs) \<longleftrightarrow> distinct xs" (is "?l \<longleftrightarrow> ?r")
  using fresh_map_inj_on[OF fin] by (auto simp: distinct_map)

subsection \<open>Instances\<close>

text \<open>The function replacing a terminal by the corresponding fresh nonterminal is
formalized as follows.\<close>

definition replace_Tm_sym :: "('t \<rightharpoonup> 'n) \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) sym" where
"replace_Tm_sym f x = (case x of Tm a \<Rightarrow> (case f a of Some A \<Rightarrow> Nt A | _ \<Rightarrow> x) | _ \<Rightarrow> x)"

lemma replace_Tm_sym_simps:
  "replace_Tm_sym f (Nt A) = Nt A"
  "replace_Tm_sym f (Tm a) = (case f a of Some A \<Rightarrow> Nt A | _ \<Rightarrow> Tm a)"
  by (auto simp: replace_Tm_sym_def)

subsubsection \<open>Replacing all terminals\<close>

definition Replace_all_Tm :: "('t \<rightharpoonup> 'n) \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
[code_unfold]: "Replace_all_Tm f = Replace_Tm f (map (replace_Tm_sym f))"

value "Replace_all_Tm (fresh_map {0::nat,1,2,3} [10::int,11,12])
  {(0,[Tm 10, Tm 12, Tm 10]),(2,[Tm 11, Tm 11, Tm 12])}"

definition replace_all_Tm :: "('t \<times> 'n) list \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
"replace_all_Tm f = replace_Tm f (map (replace_Tm_sym (map_of f)))"

lemma set_replace_all_Tm:
  "distinct (map fst f) \<Longrightarrow> set (replace_all_Tm f P) = Replace_all_Tm (map_of f) (set P)"
  by (simp add: replace_all_Tm_def Replace_all_Tm_def set_replace_Tm)

lemma map_replace_Tm_sym_ops:
  "map (replace_Tm_sym f) xs \<in> Replace_Tm_syms_ops f xs"
  by (induction xs, auto split: sym.splits option.splits simp: Replace_Tm_sym_ops_def insert_conc replace_Tm_sym_simps)

lemma map_replace_Tm_ops:
  "map (replace_Tm_sym f) \<in> Replace_Tm_ops f"
  by (simp add: Replace_Tm_ops_def map_replace_Tm_sym_ops)

corollary Lang_Replace_all_Tm:
  assumes "inj_on f (dom f)" "ran f \<inter> Nts P = {}" "A \<notin> ran f"
  shows "Lang (Replace_all_Tm f P) A = Lang P A"
  using Lang_Replace_Tm[OF map_replace_Tm_ops assms] by (simp add: Replace_all_Tm_def)

subsubsection \<open>Replacing non-head terminals\<close>

definition replace_Tm_tl_syms :: "('t \<rightharpoonup> 'n) \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms" where
"replace_Tm_tl_syms f xs = (case xs of x#xs' \<Rightarrow> x # map (replace_Tm_sym f) xs' | _ \<Rightarrow> xs)"

definition Replace_Tm_tl :: "('t \<rightharpoonup> 'n) \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
[code_unfold]: "Replace_Tm_tl f = Replace_Tm f (replace_Tm_tl_syms f)"

value "Replace_Tm_tl (fresh_map {0::nat,1,2,3} [10::int,11,12])
  {(0,[Tm 10, Tm 12, Tm 10]),(2,[Tm 11, Tm 11, Tm 12])}"

definition replace_Tm_tl :: "('t \<times> 'n) list \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
"replace_Tm_tl f = replace_Tm f (replace_Tm_tl_syms (map_of f))"

lemma set_replace_Tm_tl:
  "distinct (map fst f) \<Longrightarrow> set (replace_Tm_tl f P) = Replace_Tm_tl (map_of f) (set P)"
  by (simp add: replace_Tm_tl_def Replace_Tm_tl_def set_replace_Tm)

lemma replace_Tm_tl_syms_ops:
  "replace_Tm_tl_syms f xs \<in> Replace_Tm_syms_ops f xs"
  by (auto simp: Replace_Tm_sym_ops_def replace_Tm_tl_syms_def insert_conc map_replace_Tm_sym_ops split: list.splits)

lemma replace_Tm_tl_ops:
  "replace_Tm_tl_syms f \<in> Replace_Tm_ops f"
  by (simp add: Replace_Tm_ops_def replace_Tm_tl_syms_ops)

corollary Lang_Replace_Tm_tl:
  assumes "inj_on f (dom f)" "ran f \<inter> Nts P = {}" "A \<notin> ran f"
  shows "Lang (Replace_Tm_tl f P) A = Lang P A"
  using Lang_Replace_Tm[OF replace_Tm_tl_ops assms] by (simp add: Replace_Tm_tl_def)

end