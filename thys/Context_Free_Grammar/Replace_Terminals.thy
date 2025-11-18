(*<*)
theory Replace_Terminals
  imports Context_Free_Grammar.Expansion
begin
(*>*)

section \<open>Replacing Terminals by (Fresh) Nonterminals\<close>

lemma Lhss_image_Pair: "Lhss ((\<lambda>x. (f x, g x)) ` X) = f ` X"
  by (auto simp: Lhss_def)

lemma Rhss_image_Pair_inj_on:
  assumes f: "inj_on f X" and x: "x \<in> X"
  shows "Rhss ((\<lambda>x. (f x, g x)) ` X) (f x) = {g x}"
  using inj_onD[OF f] x by (auto simp: Rhss_def)

text \<open>First, we define the grammar where fresh nonterminals produce the corresponding terminals.
We abstract the map from terminals to the fresh nonterminals by \<open>f\<close>.\<close>

abbreviation Replace_Tm_new :: "('t \<Rightarrow> 'n) \<Rightarrow> 't set \<Rightarrow> ('n,'t) Prods" where
"Replace_Tm_new f as \<equiv> (\<lambda>a. (f a, [Tm a])) ` as"

text \<open>Admissible replacements can choose to replace or preserve each terminal.\<close>

fun Replace_Tm_syms_ops where
  "Replace_Tm_syms_ops f [] = {[]}"
| "Replace_Tm_syms_ops f (x#xs) =
   insert [x] (case x of Tm a \<Rightarrow> {[Nt (f a)]} | _ \<Rightarrow> {}) @@ Replace_Tm_syms_ops f xs"

definition Replace_Tm_ops :: "('t \<Rightarrow> 'n) \<Rightarrow> (('n,'t) syms \<Rightarrow> ('n,'t) syms) set" where
"Replace_Tm_ops f = {g. \<forall>\<alpha>. g \<alpha> \<in> Replace_Tm_syms_ops f \<alpha>}"

definition Replace_Tm :: "('t \<Rightarrow> 'n) \<Rightarrow> (('n,'t) syms \<Rightarrow> ('n,'t) syms) \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"Replace_Tm f g P = {(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} \<union> Replace_Tm_new f (Tms P)"

text \<open>Expansion with respect to the grammar @{const Replace_Tm_new} should
revert the fresh nonterminals to the original terminals,
while preserving terminals and locked nonterminals.\<close>

lemma Rhss_Un_Replace_Tm_new:
  assumes inj: "inj_on f as" and a: "a \<in> as" and fa: "f a \<notin> Lhss P"
  shows "Rhss (P \<union> Replace_Tm_new f as) (f a) = {[Tm a]}"
  by (simp add: Rhss_Un Rhss_image_Pair_inj_on[OF inj a] fa[unfolded notin_Lhss_iff_Rhss])

lemma Expand_sym_Replace_Tm_Tm:
  "Expand_sym (Replace_Tm_new f as) L (Tm a) = {[Tm a]}"
  by (auto simp: Expand_sym_def)

lemma Expand_sym_Replace_Tm_Nt:
  assumes inj: "inj_on f as" and A: "A \<in> L"
  shows "Expand_sym (Replace_Tm_new f as) L (Nt A) = {[Nt A]}"
  using A by (auto simp: Expand_sym_def)

lemma Expand_sym_Replace_Tm_new:
  assumes inj: "inj_on f as" and L: "L \<inter> f ` as = {}" and a: "a \<in> as"
  shows "Expand_sym (Replace_Tm_new f as) L (Nt (f a)) = {[Tm a]}"
  using a L by (auto simp: Expand_sym_def Rhss_image_Pair_inj_on[OF inj])

lemma Expand_all_syms_Replace_Tm_ops:
  assumes inj: "inj_on f as"
    and L: "L \<inter> f ` as = {}"
    and \<alpha>: "Tms_syms \<alpha> \<subseteq> as" "Nts_syms \<alpha> \<subseteq> L" "\<beta> \<in> Replace_Tm_syms_ops f \<alpha>"
  shows "Expand_all_syms (Replace_Tm_new f as) L \<beta> = {\<alpha>}"
proof (insert \<alpha>, induction \<alpha> arbitrary: \<beta>)
  case Nil
  then show ?case by simp
next
  case (Cons x \<alpha>)
  then have 1: "Tms_syms \<alpha> \<subseteq> as" and 2: "Nts_syms \<alpha> \<subseteq> L" by auto
  from Cons.prems(3)
  obtain y \<beta>' where [simp]: "\<beta> = y # \<beta>'"
    and 3: "\<beta>' \<in> Replace_Tm_syms_ops f \<alpha>"
    and y: "case x of Tm a \<Rightarrow> y = Nt (f a) \<or> y = x | _ \<Rightarrow> y = x"
    by (auto simp: insert_conc split:sym.splits)
  note IH = Cons.IH[OF 1 2 3]
  from y Cons.prems(1,2) Expand_sym_Replace_Tm_new[OF inj L]
  show ?case
    by (auto split: sym.splits simp: Expand_sym_Replace_Tm_Nt[OF inj] insert_conc IH
        Expand_sym_Replace_Tm_Tm conc_insert)
qed

lemma Expand_all_Replace_Tm_ops:
  assumes g: "g \<in> Replace_Tm_ops f"
    and inj: "inj_on f as"
    and L: "L \<inter> f ` as = {}"
    and P: "Tms P \<subseteq> as" "Rhs_Nts P \<subseteq> L"
  shows "Expand_all (Replace_Tm_new f as) L {(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} = P"
proof-
  have *: "(A,\<alpha>) \<in> P \<Longrightarrow> Expand_all_syms (Replace_Tm_new f as) L (g \<alpha>) = {\<alpha>}" for A \<alpha>
    apply (rule Expand_all_syms_Replace_Tm_ops[OF inj L])
    using P g by (auto simp: Tms_def Rhs_Nts_def Replace_Tm_ops_def)
  then show ?thesis by (force simp: Expand_def)
qed

text \<open>Admissible replacements preserves the language, because
expanding the replaced grammar results in the original grammar,
and expansion preserves the language.\<close>

theorem Lang_Replace_Tm:
  assumes g: "g \<in> Replace_Tm_ops f"
    and inj: "inj_on f (Tms P)"
    and disj: "Nts P \<inter> f ` Tms P = {}"
    and A: "A \<notin> f ` Tms P"
  shows "Lang (Replace_Tm f g P) A = Lang P A"
    (is "?l = ?r")
proof-
  have "?l = Lang ({(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} \<union> Replace_Tm_new f (Tms P)) A"
    by (simp add: Replace_Tm_def)
  also have "\<dots> = Lang (Expand_all (Replace_Tm_new f (Tms P)) (Nts P) {(A, g \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P} \<union> Replace_Tm_new f (Tms P)) A"
    apply (subst Lang_Expand_all)
    by (auto simp: Nts_def Lhss_def)
  also have "\<dots> = Lang (P \<union> Replace_Tm_new f (Tms P)) A"
    using Expand_all_Replace_Tm_ops[OF g inj disj]
    by (simp add: Nts_Lhss_Rhs_Nts)
  also have "\<dots> = ?r"
    apply (rule Lang_Un_disj_Lhss) using disj A by (auto simp: Lhss_image_Pair)
  finally show ?thesis.
qed

subsection \<open>Mapping to Fresh Nonterminals\<close>

text \<open>We provide an implementation of a function that maps terminals to corresponding
fresh nonterminals.\<close>

fun fresh_map :: "'a :: fresh0 set \<Rightarrow> 'b list \<Rightarrow> 'b \<rightharpoonup> 'a" where
  "fresh_map A [] = Map.empty"
| "fresh_map A (x#xs) = (let a = fresh0 A in (fresh_map (insert a A) xs)(x \<mapsto> a))"

abbreviation fresh_fun where
"fresh_fun A xs x \<equiv> the (fresh_map A xs x)"

lemma fresh_fun_notIn: "finite A \<Longrightarrow> x \<in> set xs \<Longrightarrow> fresh_fun A xs x \<notin> A"
  apply (induction xs arbitrary: A)
  by (auto simp: Let_def fresh0_notIn)

lemma fresh_fun_disj: "finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> X \<subseteq> set xs \<Longrightarrow> B \<inter> fresh_fun A xs ` X = {}"
  by (force simp: fresh_fun_notIn)

lemma fresh_fun_inj_on: "finite A \<Longrightarrow> inj_on (fresh_fun A xs) (set xs)"
proof (induction xs arbitrary: A)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  define a where "a = fresh0 A"
  from Cons
  have IH: "inj_on (fresh_fun (insert a A) xs) (set xs)"
    and fin: "finite (insert a A)" by auto
  { fix y assume "y \<in> set xs"
    from fresh_fun_notIn[OF fin this]
    have "fresh_fun (insert a A) xs y \<notin> A" "a \<noteq> fresh_fun (insert a A) xs y" by auto
  } note * = this this(2)[symmetric]
  show ?case
    by (auto simp flip: a_def intro!: inj_onI split: if_splits simp: inj_onD[OF IH] *)
qed

lemma fresh_fun_distinct:
  assumes fin: "finite A"
  shows "distinct (map (fresh_fun A xs) xs) \<longleftrightarrow> distinct xs" (is "?l \<longleftrightarrow> ?r")
  using fresh_fun_inj_on[OF fin] by (auto simp: distinct_map)

subsection \<open>Instances\<close>

text \<open>The function replacing a terminal by the corresponding fresh nonterminal is
formalized as follows.\<close>

definition replace_Tm_sym :: "('t \<Rightarrow> 'n) \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) sym" where
"replace_Tm_sym f x = (case x of Tm a \<Rightarrow> Nt (f a) | _ \<Rightarrow> x)"

lemma replace_Tm_sym_simps:
  "replace_Tm_sym f (Nt A) = Nt A"
  "replace_Tm_sym f (Tm a) = Nt (f a)"
  by (auto simp: replace_Tm_sym_def)

subsubsection \<open>Replacing all terminals\<close>

definition Replace_all_Tm :: "('t \<Rightarrow> 'n) \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"Replace_all_Tm f = Replace_Tm f (map (replace_Tm_sym f))"

lemma map_replace_Tm_sym_ops:
  "map (replace_Tm_sym f) xs \<in> Replace_Tm_syms_ops f xs"
  by (induction xs, auto split: sym.splits simp: insert_conc replace_Tm_sym_simps)

lemma map_replace_Tm_ops:
  "map (replace_Tm_sym f) \<in> Replace_Tm_ops f"
  by (simp add: Replace_Tm_ops_def map_replace_Tm_sym_ops)

corollary Lang_Replace_all_Tm:
  assumes "inj_on f (Tms P)" "Nts P \<inter> f ` Tms P = {}" "A \<notin> f ` Tms P"
  shows "Lang (Replace_all_Tm f P) A = Lang P A"
  using Lang_Replace_Tm[OF map_replace_Tm_ops assms] by (simp add: Replace_all_Tm_def)

subsubsection \<open>Replacing non-head terminals\<close>

definition replace_Tm_tl_syms :: "('t \<Rightarrow> 'n) \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms" where
"replace_Tm_tl_syms f xs = (case xs of x#xs' \<Rightarrow> x # map (replace_Tm_sym f) xs' | _ \<Rightarrow> xs)"

definition Replace_Tm_tl :: "('t \<Rightarrow> 'n) \<Rightarrow> ('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
"Replace_Tm_tl f = Replace_Tm f (replace_Tm_tl_syms f)"

lemma replace_Tm_tl_syms_ops:
  "replace_Tm_tl_syms f xs \<in> Replace_Tm_syms_ops f xs"
  by (auto simp: replace_Tm_tl_syms_def insert_conc map_replace_Tm_sym_ops split: list.splits)

lemma replace_Tm_tl_ops:
  "replace_Tm_tl_syms f \<in> Replace_Tm_ops f"
  by (simp add: Replace_Tm_ops_def replace_Tm_tl_syms_ops)

corollary Lang_Replace_Tm_tl:
  assumes "inj_on f (Tms P)" "Nts P \<inter> f ` Tms P = {}" "A \<notin> f ` Tms P"
  shows "Lang (Replace_Tm_tl f P) A = Lang P A"
  using Lang_Replace_Tm[OF replace_Tm_tl_ops assms] by (simp add: Replace_Tm_tl_def)

end