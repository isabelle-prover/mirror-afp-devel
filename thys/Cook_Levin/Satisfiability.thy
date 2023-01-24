chapter \<open>Satisfiability\label{s:Sat}\<close>

theory Satisfiability
  imports Wellformed NP
begin

text \<open>
This chapter introduces the language \SAT{} and shows that it is in $\NP$, which
constitutes the easier part of the Cook-Levin theorem. The other part, the
$\NP$-hardness of \SAT{}, is what all the following chapters are concerned with.

We first introduce Boolean formulas in conjunctive normal form and the concept
of satisfiability. Then we define a way to represent such formulas as bit
strings, leading to the definition of the language \SAT{} as a set of strings
(Section~\ref{s:sat-sat}).

For the proof that \SAT{} is in $\NP$, we construct a Turing machine that, given
a CNF formula and a string representing a variable assignment, outputs
\textbf{1} iff. the assignment satisfies the formula. The TM will run in
polynomial time, and there are always assignments polynomial (in fact, linear)
in the length of the formula (Section~\ref{s:Sat-np}).
\<close>


section \<open>The language \SAT{}\label{s:sat-sat}\<close>

text \<open>
\SAT{} is the language of all strings representing satisfiable Boolean
formulas in conjunctive normal form (CNF).  This section introduces a minimal
version of Boolean formulas in conjunctive normal form, including the
concepts of assignments and satisfiability.
\<close>


subsection \<open>CNF formulas and satisfiability\label{s:CNF}\<close>

text \<open>
Arora and Barak~\cite[p.~44]{ccama} define Boolean formulas in general as
expressions over $\land$, $\lor$, $\lnot$, parentheses, and variables $v_1, v_2,
\dots$ in the usual way. Boolean formulas in conjunctive normal form are defined as
$\bigwedge_i\left(\bigvee_j v_{i_j}\right)$, where the $v_{i_j}$ are literals.
This definition does not seem to allow for empty clauses. Also whether the
``empty CNF formula'' exists is somewhat doubtful.  Nevertheless, our
formalization allows for both empty clauses and the empty CNF formula, because
this enables us to represent CNF formulas as lists of clauses and clauses as
lists of literals without having to somehow forbid the empty list. This seems to
be a popular approach for formalizing CNF formulas in the context of \SAT{} and
$\NP$~\cite{Gher2021MechanisingCT,Multiset_Ordering_NPC-AFP}.

We identify a variable $v_i$ with its index $i$, which can be any natural
number. A \emph{literal} can either be positive or negative, representing a
variable or negated variable, respectively.

\null
\<close>

datatype literal = Neg nat | Pos nat

type_synonym clause = "literal list"

type_synonym formula = "clause list"

text \<open>
An \emph{assignment} maps all variables, given by their index, to a Boolean:
\<close>

type_synonym assignment = "nat \<Rightarrow> bool"

abbreviation satisfies_literal :: "assignment \<Rightarrow> literal \<Rightarrow> bool" where
  "satisfies_literal \<alpha> x \<equiv> case x of Neg n \<Rightarrow> \<not> \<alpha> n | Pos n \<Rightarrow> \<alpha> n"

definition satisfies_clause :: "assignment \<Rightarrow> clause \<Rightarrow> bool" where
  "satisfies_clause \<alpha> c \<equiv> \<exists>x\<in>set c. satisfies_literal \<alpha> x"

definition satisfies :: "assignment \<Rightarrow> formula \<Rightarrow> bool" (infix "\<Turnstile>" 60) where
  "\<alpha> \<Turnstile> \<phi> \<equiv> \<forall>c\<in>set \<phi>. satisfies_clause \<alpha> c"

text \<open>
As is customary, the empty clause is satisfied by no assignment, and the empty
CNF formula is satisfied by every assignment.
\<close>

proposition "\<not> satisfies_clause \<alpha> []"
  by (simp add: satisfies_clause_def)

proposition "\<alpha> \<Turnstile> []"
  by (simp add: satisfies_def)

lemma satisfies_clause_take:
  assumes "i < length clause"
  shows "satisfies_clause \<alpha> (take (Suc i) clause) \<longleftrightarrow>
    satisfies_clause \<alpha> (take i clause) \<or> satisfies_literal \<alpha> (clause ! i)"
  using assms satisfies_clause_def by (auto simp add: take_Suc_conv_app_nth)

lemma satisfies_take:
  assumes "i < length \<phi>"
  shows "\<alpha> \<Turnstile> take (Suc i) \<phi> \<longleftrightarrow> \<alpha> \<Turnstile> take i \<phi> \<and> satisfies_clause \<alpha> (\<phi> ! i)"
  using assms satisfies_def by (auto simp add: take_Suc_conv_app_nth)

lemma satisfies_append:
  assumes "\<alpha> \<Turnstile> \<phi>\<^sub>1 @ \<phi>\<^sub>2"
  shows "\<alpha> \<Turnstile> \<phi>\<^sub>1" and "\<alpha> \<Turnstile> \<phi>\<^sub>2"
  using assms satisfies_def by simp_all

lemma satisfies_append':
  assumes "\<alpha> \<Turnstile> \<phi>\<^sub>1" and "\<alpha> \<Turnstile> \<phi>\<^sub>2"
  shows "\<alpha> \<Turnstile> \<phi>\<^sub>1 @ \<phi>\<^sub>2"
  using assms satisfies_def by auto

lemma satisfies_concat_map:
  assumes "\<alpha> \<Turnstile> concat (map f [0..<k])" and "i < k"
  shows "\<alpha> \<Turnstile> f i"
  using assms satisfies_def by simp

lemma satisfies_concat_map':
  assumes "\<And>i. i < k \<Longrightarrow> \<alpha> \<Turnstile> f i"
  shows "\<alpha> \<Turnstile> concat (map f [0..<k])"
  using assms satisfies_def by simp

text \<open>
The main ingredient for defining \SAT{} is the concept of \emph{satisfiable} CNF
formula:
\<close>

definition satisfiable :: "formula \<Rightarrow> bool" where
  "satisfiable \<phi> \<equiv> \<exists>\<alpha>. \<alpha> \<Turnstile> \<phi>"

text \<open>
The set of all variables used in a CNF formula is finite.
\<close>

definition variables :: "formula \<Rightarrow> nat set" where
  "variables \<phi> \<equiv> {n. \<exists>c\<in>set \<phi>. Neg n \<in> set c \<or> Pos n \<in> set c}"

lemma finite_variables: "finite (variables \<phi>)"
proof -
  define voc :: "clause \<Rightarrow> nat set" where
    "voc c = {n. Neg n \<in> set c \<or> Pos n \<in> set c}" for c
  let ?vocs = "set (map voc \<phi>)"

  have "finite (voc c)" for c
  proof (induction c)
    case Nil
    then show ?case
      using voc_def by simp
  next
    case (Cons a c)
    have "voc (a # c) = {n. Neg n \<in> set (a # c) \<or> Pos n \<in> set (a # c)}"
      using voc_def by simp
    also have "... = {n. Neg n \<in> set c \<or> Neg n = a \<or> Pos n \<in> set c \<or> Pos n = a}"
      by auto
    also have "... = {n. (Neg n \<in> set c \<or> Pos n \<in> set c) \<or> (Pos n = a \<or> Neg n = a)}"
      by auto
    also have "... = {n. Neg n \<in> set c \<or> Pos n \<in> set c} \<union> {n. Pos n = a \<or> Neg n = a}"
      by auto
    also have "... = voc c \<union> {n. Pos n = a \<or> Neg n = a}"
      using voc_def by simp
    finally have "voc (a # c) = voc c \<union> {n. Pos n = a \<or> Neg n = a}" .
    moreover have "finite {n. Pos n = a \<or> Neg n = a}"
      using finite_nat_set_iff_bounded by auto
    ultimately show ?case
      using Cons by simp
  qed
  moreover have "variables \<phi> = \<Union>?vocs"
    using variables_def voc_def by auto
  moreover have "finite ?vocs"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma variables_append: "variables (\<phi>\<^sub>1 @ \<phi>\<^sub>2) = variables \<phi>\<^sub>1 \<union> variables \<phi>\<^sub>2"
  using variables_def by auto

text \<open>
Arora and Barak~\cite[Claim~2.13]{ccama} define the \emph{size} of a CNF formula
as the numbr of $\wedge / \vee$ symbols. We use a slightly different definition,
namely the number of literals:
\<close>

definition fsize :: "formula \<Rightarrow> nat" where
  "fsize \<phi> \<equiv> sum_list (map length \<phi>)"


subsection \<open>Predicates on assignments\<close>

text \<open>
Every CNF formula is satisfied by a set of assignments. Conversely, for certain
sets of assignments we can construct CNF formulas satisfied by exactly these
assignments.  This will be helpful later when we construct formulas for reducing
arbitrary languages to \SAT{} (see Section~\ref{s:Reducing}).
\<close>


subsubsection \<open>Universality of CNF formulas\<close>

text \<open>
A set (represented by a predicate) $F$ of assignments depends on the first
$\ell$ variables iff.\ any two assignments that agree on the first $\ell$
variables are either both in the set or both outside of the set.
\<close>

definition depon :: "nat \<Rightarrow> (assignment \<Rightarrow> bool) \<Rightarrow> bool" where
  "depon l F \<equiv> \<forall>\<alpha>\<^sub>1 \<alpha>\<^sub>2. (\<forall>i<l. \<alpha>\<^sub>1 i = \<alpha>\<^sub>2 i) \<longrightarrow> F \<alpha>\<^sub>1 = F \<alpha>\<^sub>2"

text \<open>
Lists of all strings of the same length:
\<close>

fun str_of_len :: "nat \<Rightarrow> string list" where
  "str_of_len 0 = [[]]" |
  "str_of_len (Suc l) = map ((#) \<bbbO>) (str_of_len l) @ map ((#) \<bbbI>) (str_of_len l)"

lemma length_str_of_len: "length (str_of_len l) = 2 ^ l"
  by (induction l) simp_all

lemma in_str_of_len_length: "xs \<in> set (str_of_len l) \<Longrightarrow> length xs = l"
  by (induction l arbitrary: xs) auto

lemma length_in_str_of_len: "length xs = l \<Longrightarrow> xs \<in> set (str_of_len l)"
proof (induction l arbitrary: xs)
  case 0
  then show ?case
    by simp
next
  case (Suc l)
  then obtain y ys where "xs = y # ys"
    by (meson length_Suc_conv)
  then have "length ys = l"
    using Suc by simp
  show ?case
  proof (cases y)
    case True
    then have "xs \<in> set (map ((#) \<bbbI>) (str_of_len l))"
      using `length ys = l` Suc `xs = y # ys` by simp
    then show ?thesis
      by simp
  next
    case False
    then have "xs \<in> set (map ((#) \<bbbO>) (str_of_len l))"
      using `length ys = l` Suc `xs = y # ys` by simp
    then show ?thesis
      by simp
  qed
qed

text \<open>
A predicate $F$ depending on the first $\ell$ variables $v_0, \dots, v_{\ell-1}$
can be regarded as a truth table over $\ell$ variables. The next lemma shows
that for every such truth table there exists a CNF formula with at most $2^\ell$
clauses and $\ell\cdot2^\ell$ literals over the first $\ell$ variables. This is
the well-known fact that every Boolean function (over $\ell$ variables) can be
represented by a CNF formula~\cite[Claim~2.13]{ccama}.
\<close>

lemma depon_ex_formula:
  assumes "depon l F"
  shows "\<exists>\<phi>.
    fsize \<phi> \<le> l * 2 ^ l \<and>
    length \<phi> \<le> 2 ^ l \<and>
    variables \<phi> \<subseteq> {..<l} \<and>
    (\<forall>\<alpha>. F \<alpha> = \<alpha> \<Turnstile> \<phi>)"
proof -
  define cl where "cl = (\<lambda>v. map (\<lambda>i. if v ! i then Neg i else Pos i) [0..<l])"
  have cl1: "satisfies_clause a (cl v)" if "length v = l" and "v \<noteq> map a [0..<l]" for v a
  proof -
    obtain i where i: "i < l" "a i \<noteq> v ! i"
      using \<open>length v = l\<close> \<open>v \<noteq> map a [0..<l]\<close>
      by (smt (verit, best) atLeastLessThan_iff map_eq_conv map_nth set_upt)
    then have *: "cl v ! i = (if v ! i then Neg i else Pos i)"
      using cl_def by simp
    then have "case (cl v ! i) of Neg n \<Rightarrow> \<not> a n | Pos n \<Rightarrow> a n"
      using i(2) by simp
    then show ?thesis
      using cl_def * that(1) satisfies_clause_def i(1) by fastforce
  qed
  have cl2: "v \<noteq> map a [0..<l]" if "length v = l" and "satisfies_clause a (cl v)" for v a
  proof
    assume assm: "v = map a [0..<l]"
    from that(2) have "\<exists>x\<in>set (cl v). case x of Neg n \<Rightarrow> \<not> a n | Pos n \<Rightarrow> a n"
      using satisfies_clause_def by simp
    then obtain i where i: "i < l" and "case (cl v ! i) of Neg n \<Rightarrow> \<not> a n | Pos n \<Rightarrow> a n"
      using cl_def by auto
    then have "v ! i \<noteq> a i"
      using cl_def by fastforce
    then show False
      using i assm by simp
  qed

  have filter_length_nth: "f (vs ! j)" if "vs = filter f sol" and "j < length vs"
    for vs sol :: "'a list" and f j
    using that nth_mem by (metis length_removeAll_less less_irrefl removeAll_filter_not)

  have sum_list_map: "sum_list (map g xs) \<le> k * length xs" if "\<And>x. x \<in> set xs \<Longrightarrow> g x = k"
    for xs :: "'a list" and g k
    using that
  proof (induction "length xs" arbitrary: xs)
    case 0
    then show ?case
      by simp
  next
    case (Suc x)
    then obtain y ys where "xs = y # ys"
      by (metis length_Suc_conv)
    then have "length ys = x"
      using Suc by simp
    have "y \<in> set xs"
      using `xs = y # ys` by simp
    have "sum_list (map g xs) = sum_list (map g (y # ys))"
      using `xs = y # ys` by simp
    also have "... = g y + sum_list (map g ys)"
      by simp
    also have "... = k + sum_list (map g ys)"
      using Suc `y \<in> set xs` by simp
    also have "... \<le> k + k * length ys"
      using Suc `length ys = x` \<open>xs = y # ys\<close> by auto
    also have "... = k * length xs"
      by (metis Suc.hyps(2) \<open>length ys = x\<close> mult_Suc_right)
    finally show ?case
      by simp
  qed

  define vs where
    "vs = filter (\<lambda>v. F (\<lambda>i. if i < l then v ! i else False) = False) (str_of_len l)"
  define \<phi> where "\<phi> = map cl vs"

  have "a \<Turnstile> \<phi>" if "F a" for a
  proof -
    define v where "v = map a [0..<l]"
    then have "(\<lambda>i. if i < l then v ! i else False) j = a j" if "j < l" for j
      by (simp add: that)
    then have *: "F (\<lambda>i. if i < l then v ! i else False)"
      using assms(1) depon_def that by (smt (verit, ccfv_SIG))
    have "satisfies_clause a c" if "c \<in> set \<phi>" for c
    proof -
      obtain j where j: "c = \<phi> ! j" "j < length \<phi>"
        using \<phi>_def `c \<in> set \<phi>` by (metis in_set_conv_nth)
      then have "c = cl (vs ! j)"
        using \<phi>_def by simp
      have "j < length vs"
        using \<phi>_def j by simp
      then have "F (\<lambda>i. if i < l then (vs ! j) ! i else False) = False"
        using vs_def filter_length_nth by blast
      then have "vs ! j \<noteq> v"
        using * by auto
      moreover have "length (vs ! j) = l"
        using vs_def length_str_of_len \<open>j < length vs\<close>
        by (smt (z3) filter_eq_nths in_str_of_len_length notin_set_nthsI nth_mem)
      ultimately have "satisfies_clause a (cl (vs ! j))"
        using v_def cl1 by simp
      then show ?thesis
        using `c = cl (vs ! j)` by simp
    qed
    then show ?thesis
      using satisfies_def by simp
  qed
  moreover have "F \<alpha>" if "\<alpha> \<Turnstile> \<phi>" for \<alpha>
  proof (rule ccontr)
    assume assm: "\<not> F \<alpha>"
    define v where "v = map \<alpha> [0..<l]"
    have *: "F (\<lambda>i. if i < l then v ! i else False) = False"
    proof -
      have "(\<lambda>i. if i < l then v ! i else False) j = \<alpha> j" if "j < l" for j
        using v_def by (simp add: that)
      then show ?thesis
        using assm assms(1) depon_def by (smt (verit, best))
    qed
    have "length v = l"
      using v_def by simp
    then obtain j where "j < length (str_of_len l)" and "v = str_of_len l ! j"
      by (metis in_set_conv_nth length_in_str_of_len)
    then have "v \<in> set vs"
      using vs_def * by fastforce
    then have "cl v \<in> set \<phi>"
      using \<phi>_def by simp
    then have "satisfies_clause \<alpha> (cl v)"
      using that satisfies_def by simp
    then have "v \<noteq> map \<alpha> [0..<l]"
      using `length v = l` cl2 by simp
    then show False
      using v_def by simp
  qed
  ultimately have "\<forall>\<alpha>. F \<alpha> = \<alpha> \<Turnstile> \<phi>"
    by auto
  moreover have "fsize \<phi> \<le> l * 2 ^ l"
  proof -
    have "length c = l" if "c \<in> set \<phi>" for c
      using that cl_def \<phi>_def by auto
    then have "fsize \<phi> \<le> l * length \<phi>"
      unfolding fsize_def using sum_list_map by auto
    also have "... \<le> l * length (str_of_len l)"
      using \<phi>_def vs_def by simp
    also have "... = l * 2 ^ l"
      using length_str_of_len by simp
    finally show ?thesis .
  qed
  moreover have "length \<phi> \<le> 2 ^ l"
  proof -
    have "length \<phi> \<le> length (str_of_len l)"
      using \<phi>_def vs_def by simp
    also have "... = 2 ^ l"
      using length_str_of_len by simp
    finally show ?thesis .
  qed
  moreover have "variables \<phi> \<subseteq> {..<l}"
  proof
    fix x assume "x \<in> variables \<phi>"
    then obtain c where c: "c \<in> set \<phi>" "Neg x \<in> set c \<or> Pos x \<in> set c"
      using variables_def by auto
    then obtain v where v: "v \<in> set (str_of_len l)" "c = cl v"
      using \<phi>_def vs_def by auto
    then show "x \<in> {..<l}"
      using cl_def c by auto
  qed
  ultimately show ?thesis
    by auto
qed


subsubsection \<open>Substitutions of variables\<close>

text \<open>
We will sometimes consider CNF formulas over the first $\ell$ variables and
derive other CNF formulas from them by substituting these variables.  Such a
substitution will be represented by a list $\sigma$ of length at least $\ell$,
meaning that the variable $v_i$ is replaced by $v_{\sigma(i)}$. We will call
this operation on formulas \emph{relabel}, and the corresponding one on literals
\emph{rename}:
\<close>

fun rename :: "nat list \<Rightarrow> literal \<Rightarrow> literal" where
  "rename \<sigma> (Neg i) = Neg (\<sigma> ! i)" |
  "rename \<sigma> (Pos i) = Pos (\<sigma> ! i)"

definition relabel :: "nat list \<Rightarrow> formula \<Rightarrow> formula" where
  "relabel \<sigma> \<phi> \<equiv> map (map (rename \<sigma>)) \<phi>"

lemma fsize_relabel: "fsize (relabel \<sigma> \<phi>) = fsize \<phi>"
  using relabel_def fsize_def by (metis length_concat length_map map_concat)

text \<open>
A substitution $\sigma$ can also be applied to an assignment and to a list of
variable indices:
\<close>

definition remap :: "nat list \<Rightarrow> assignment \<Rightarrow> assignment" where
  "remap \<sigma> \<alpha> i \<equiv> if i < length \<sigma> then \<alpha> (\<sigma> ! i) else \<alpha> i"

definition reseq :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reseq \<sigma> vs \<equiv> map ((!) \<sigma>) vs"

lemma length_reseq [simp]: "length (reseq \<sigma> vs) = length vs"
  using reseq_def by simp

text \<open>
Relabeling a formula and remapping an assignment are equivalent in a sense.
\<close>

lemma satisfies_sigma:
  assumes "variables \<phi> \<subseteq> {..<length \<sigma>}"
  shows "\<alpha> \<Turnstile> relabel \<sigma> \<phi> \<longleftrightarrow> remap \<sigma> \<alpha> \<Turnstile> \<phi>"
proof
  assume sat: "\<alpha> \<Turnstile> relabel \<sigma> \<phi>"
  have "satisfies_clause (remap \<sigma> \<alpha>) c" if "c \<in> set \<phi>" for c
  proof -
    obtain i where "i < length \<phi>" "\<phi> ! i = c"
      by (meson \<open>c \<in> set \<phi>\<close> in_set_conv_nth)
    then have "satisfies_clause \<alpha> (map (rename \<sigma>) c)"
        (is "satisfies_clause \<alpha> ?c")
      using sat satisfies_def relabel_def by auto
    then obtain x where "x\<in>set ?c" "case x of Neg n \<Rightarrow> \<not> \<alpha> n | Pos n \<Rightarrow> \<alpha> n"
      using satisfies_clause_def by auto
    then obtain j where j: "j < length ?c" "case (?c ! j) of Neg n \<Rightarrow> \<not> \<alpha> n | Pos n \<Rightarrow> \<alpha> n"
      by (metis in_set_conv_nth)
    have "case c ! j of Neg n \<Rightarrow> \<not> (remap \<sigma> \<alpha>) n | Pos n \<Rightarrow> (remap \<sigma> \<alpha>) n"
    proof (cases "c ! j")
      case (Neg n)
      then have 1: "?c ! j = Neg (\<sigma> ! n)"
        using j(1) by simp
      have "n \<in> variables \<phi>"
        using Neg j(1) nth_mem that variables_def by force
      then have "n < length \<sigma>"
        using assms by auto
      then show ?thesis
        using Neg 1 j(2) remap_def by auto
    next
      case (Pos n)
      then have 1: "?c ! j = Pos (\<sigma> ! n)"
        using j(1) by simp
      have "n \<in> variables \<phi>"
        using Pos j(1) nth_mem that variables_def by force
      then have "n < length \<sigma>"
        using assms by auto
      then show ?thesis
        using Pos 1 j(2) remap_def by auto
    qed
    then show ?thesis
      using satisfies_clause_def j by auto
  qed
  then show "remap \<sigma> \<alpha> \<Turnstile> \<phi>"
    using satisfies_def by simp
next
  assume sat: "remap \<sigma> \<alpha> \<Turnstile> \<phi>"
  have "satisfies_clause \<alpha> c" if "c \<in> set (relabel \<sigma> \<phi>)" for c
  proof -
    let ?phi = "relabel \<sigma> \<phi>"
    let ?beta = "remap \<sigma> \<alpha>"
    obtain i where i: "i < length ?phi" "?phi ! i = c"
      by (meson \<open>c \<in> set ?phi\<close> in_set_conv_nth)
    then have "satisfies_clause ?beta (\<phi> ! i)"
        (is "satisfies_clause _ ?c")
      using sat satisfies_def relabel_def by simp
    then obtain x where "x\<in>set ?c" "case x of Neg n \<Rightarrow> \<not> ?beta n | Pos n \<Rightarrow> ?beta n"
      using satisfies_clause_def by auto
    then obtain j where j: "j < length ?c" "case (?c ! j) of Neg n \<Rightarrow> \<not> ?beta n | Pos n \<Rightarrow> ?beta n"
      by (metis in_set_conv_nth)
    then have ren: "c ! j = rename \<sigma> (?c ! j)"
      using i relabel_def by auto
    have "case c ! j of Neg n \<Rightarrow> \<not> \<alpha> n | Pos n \<Rightarrow> \<alpha> n"
    proof (cases "?c ! j")
      case (Neg n)
      then have *: "c ! j = Neg (\<sigma> ! n)"
        by (simp add: ren)
      have "n \<in> variables \<phi>"
        using Neg i j variables_def that length_map mem_Collect_eq nth_mem relabel_def by force
      then have "n < length \<sigma>"
        using assms by auto
      moreover have "\<not> (remap \<sigma> \<alpha>) n"
        using j(2) Neg by simp
      ultimately have "\<not> \<alpha> (\<sigma> ! n)"
        using remap_def by simp
      then show ?thesis
        by (simp add: *)
    next
      case (Pos n)
      then have *: "c ! j = Pos (\<sigma> ! n)"
        by (simp add: ren)
      have "n \<in> variables \<phi>"
        using Pos i j variables_def that length_map mem_Collect_eq nth_mem relabel_def by force
      then have "n < length \<sigma>"
        using assms by auto
      moreover have "(remap \<sigma> \<alpha>) n"
        using j(2) Pos by simp
      ultimately have "\<alpha> (\<sigma> ! n)"
        using remap_def by simp
      then show ?thesis
        by (simp add: *)
    qed
    moreover have "length c = length (\<phi> ! i)"
      using relabel_def i by auto
    ultimately show ?thesis
      using satisfies_clause_def j by auto
  qed
  then show "\<alpha> \<Turnstile> relabel \<sigma> \<phi>"
    by (simp add: satisfies_def)
qed


subsection \<open>Representing CNF formulas as strings\label{s:sat-sat-repr}\<close>

text \<open>
By identifying negated literals with even numbers and positive literals with odd
numbers, we can identify literals with natural numbers. This yields a
straightforward representation of a clause as a list of numbers and of a CNF
formula as a list of lists of numbers. Such a list can, in turn, be represented
as a symbol sequence over a quaternary alphabet as described in
Section~\ref{s:tm-numlistlist}, which ultimately can be encoded over a binary
alphabet (see Section~\ref{s:tm-quaternary}). This is essentially how we
represent CNF formulas as strings.

We have to introduce a bunch of functions for mapping between these
representations.

\null
\<close>

fun literal_n :: "literal \<Rightarrow> nat" where
  "literal_n (Neg i) = 2 * i" |
  "literal_n (Pos i) = Suc (2 * i)"

definition n_literal :: "nat \<Rightarrow> literal" where
  "n_literal n \<equiv> if even n then Neg (n div 2) else Pos (n div 2)"

lemma n_literal_n: "n_literal (literal_n x) = x"
  using n_literal_def by (cases x) simp_all

lemma literal_n_literal: "literal_n (n_literal n) = n"
  using n_literal_def by simp

definition clause_n :: "clause \<Rightarrow> nat list" where
  "clause_n cl \<equiv> map literal_n cl"

definition n_clause :: "nat list \<Rightarrow> clause" where
  "n_clause ns \<equiv> map n_literal ns"

lemma n_clause_n: "n_clause (clause_n cl) = cl"
  using n_clause_def clause_n_def n_literal_n by (simp add: map_idI)

lemma clause_n_clause: "clause_n (n_clause n) = n"
  using n_clause_def clause_n_def literal_n_literal by (simp add: map_idI)

definition formula_n :: "formula \<Rightarrow> nat list list" where
  "formula_n \<phi> \<equiv> map clause_n \<phi>"

definition n_formula :: "nat list list \<Rightarrow> formula" where
  "n_formula nss \<equiv> map n_clause nss"

lemma n_formula_n: "n_formula (formula_n \<phi>) = \<phi>"
  using n_formula_def formula_n_def n_clause_n by (simp add: map_idI)

lemma formula_n_formula: "formula_n (n_formula nss) = nss"
  using n_formula_def formula_n_def clause_n_clause by (simp add: map_idI)

definition formula_zs :: "formula \<Rightarrow> symbol list" where
  "formula_zs \<phi> \<equiv> numlistlist (formula_n \<phi>)"

text \<open>
The mapping between formulas and well-formed symbol sequences for
lists of lists of numbers is bijective.
\<close>

lemma formula_n_inj: "formula_n \<phi>\<^sub>1 = formula_n \<phi>\<^sub>2 \<Longrightarrow> \<phi>\<^sub>1 = \<phi>\<^sub>2"
  using n_formula_n by metis

definition zs_formula :: "symbol list \<Rightarrow> formula" where
  "zs_formula zs \<equiv> THE \<phi>. formula_zs \<phi> = zs"

lemma zs_formula:
  assumes "numlistlist_wf zs"
  shows "\<exists>!\<phi>. formula_zs \<phi> = zs"
proof -
  obtain nss where nss: "numlistlist nss = zs"
    using assms numlistlist_wf_def by auto
  let ?phi = "n_formula nss"
  have *: "formula_n ?phi = nss"
    using nss formula_n_formula by simp
  then have "formula_zs ?phi = zs"
    using nss formula_zs_def by simp
  then have "\<exists>\<phi>. formula_zs \<phi> = zs"
    by auto
  moreover have "\<phi> = ?phi" if "formula_zs \<phi> = zs" for \<phi>
  proof -
    have "numlistlist (formula_n \<phi>) = zs"
      using that formula_zs_def by simp
    then have "nss = formula_n \<phi>"
      using nss numlistlist_inj by simp
    then show ?thesis
      using formula_n_inj * by simp
  qed
  ultimately show ?thesis
    by auto
qed

lemma zs_formula_zs: "zs_formula (formula_zs \<phi>) = \<phi>"
  by (simp add: formula_n_inj formula_zs_def numlistlist_inj the_equality zs_formula_def)

lemma formula_zs_formula:
  assumes "numlistlist_wf zs"
  shows "formula_zs (zs_formula zs) = zs"
  using assms zs_formula zs_formula_zs by metis

text \<open>
There will of course be Turing machines that perform computations on formulas.
In order to bound their running time, we need bounds for the length of the
symbol representation of formulas.
\<close>

lemma nlength_literal_n_Pos: "nlength (literal_n (Pos n)) \<le> Suc (nlength n)"
  using nlength_times2plus1 by simp

lemma nlength_literal_n_Neg: "nlength (literal_n (Neg n)) \<le> Suc (nlength n)"
  using nlength_times2 by simp

lemma nlllength_formula_n:
  fixes V :: nat and \<phi> :: formula
  assumes "\<And>v. v \<in> variables \<phi> \<Longrightarrow> v \<le> V"
  shows "nlllength (formula_n \<phi>) \<le> fsize \<phi> * Suc (Suc (nlength V)) + length \<phi>"
  using assms
proof (induction \<phi>)
  case Nil
  then show ?case
    using formula_n_def by simp
next
  case (Cons cl \<phi>)
  then have 0: "\<And>v. v \<in> variables \<phi> \<Longrightarrow> v \<le> V"
    using variables_def by simp
  have 1: "n \<le> V" if "Pos n \<in> set cl" for n
    using that variables_def by (simp add: Cons.prems)
  have 2: "n \<le> V" if "Neg n \<in> set cl" for n
    using that variables_def by (simp add: Cons.prems)
  have 3: "nlength (literal_n v) \<le> Suc (nlength V)" if "v \<in> set cl" for v
  proof (cases v)
    case (Neg n)
    then have "nlength (literal_n v) \<le> Suc (nlength n)"
      using nlength_literal_n_Neg by blast
    moreover have "n \<le> V"
      using Neg that 2 by simp
    ultimately show ?thesis
      using nlength_mono by fastforce
  next
    case (Pos n)
    then have "nlength (literal_n v) \<le> Suc (nlength n)"
      using nlength_literal_n_Pos by blast
    moreover have "n \<le> V"
      using Pos that 1 by simp
    ultimately show ?thesis
      using nlength_mono by fastforce
  qed

  have "nllength (clause_n cl) = length (numlist (map literal_n cl))"
    using clause_n_def nllength_def by simp
  have "nllength (clause_n cl) = (\<Sum>n\<leftarrow>(map literal_n cl). Suc (nlength n))"
    using clause_n_def nllength by simp
  also have "... = (\<Sum>v\<leftarrow>cl. Suc (nlength (literal_n v)))"
  proof -
    have "map (\<lambda>n. Suc (nlength n)) (map literal_n cl) = map (\<lambda>v. Suc (nlength (literal_n v))) cl"
      by simp
    then show ?thesis
      by metis
  qed
  also have "... \<le> (\<Sum>v\<leftarrow>cl. Suc (Suc (nlength V)))"
    using sum_list_mono[of cl "\<lambda>v. Suc (nlength (literal_n v))" "\<lambda>v. Suc (Suc (nlength V))"] 3
    by simp
  also have "... = Suc (Suc (nlength V)) * length cl"
    using sum_list_const by blast
  finally have 4: "nllength (clause_n cl) \<le> Suc (Suc (nlength V)) * length cl" .

  have "concat (map (\<lambda>ns. numlist ns @ [5]) (map clause_n (cl # \<phi>))) =
      (numlist (clause_n cl) @ [5]) @ concat (map (\<lambda>ns. numlist ns @ [5]) (map clause_n \<phi>))"
    by simp
  then have "length (concat (map (\<lambda>ns. numlist ns @ [5]) (map clause_n (cl # \<phi>)))) =
      length ((numlist (clause_n cl) @ [5]) @ concat (map (\<lambda>ns. numlist ns @ [5]) (map clause_n \<phi>)))"
    by simp
  then have "nlllength (formula_n (cl # \<phi>)) =
      length ((numlist (clause_n cl) @ [5]) @ concat (map (\<lambda>ns. numlist ns @ [5]) (map clause_n \<phi>)))"
    using formula_n_def numlistlist_def nlllength_def by simp
  also have "... = length (numlist (clause_n cl) @ [5]) + length (concat (map (\<lambda>ns. numlist ns @ [5]) (map clause_n \<phi>)))"
      by simp
  also have "... = length (numlist (clause_n cl) @ [5]) + nlllength (formula_n \<phi>)"
    using formula_n_def numlistlist_def nlllength_def by simp
  also have "... = Suc (nllength (clause_n cl)) + nlllength (formula_n \<phi>)"
    using nllength_def by simp
  also have "... \<le> Suc (Suc (Suc (nlength V)) * length cl) + nlllength (formula_n \<phi>)"
    using 4 by simp
  also have "... \<le> Suc (Suc (Suc (nlength V)) * length cl) + fsize \<phi> * Suc (Suc (nlength V)) + length \<phi>"
    using Cons 0 by simp
  also have "... = fsize (cl # \<phi>) * Suc (Suc (nlength V)) + length (cl # \<phi>)"
    by (simp add: add_mult_distrib2 mult.commute fsize_def)
  finally show ?case
    by simp
qed

text \<open>
Since \SAT{} is supposed to be a set of strings rather than symbol
sequences, we need to map symbol sequences representing formulas to strings:
\<close>

abbreviation formula_to_string :: "formula \<Rightarrow> string" where
  "formula_to_string \<phi> \<equiv> symbols_to_string (binencode (numlistlist (formula_n \<phi>)))"

lemma formula_to_string_inj:
  assumes "formula_to_string \<phi>\<^sub>1 = formula_to_string \<phi>\<^sub>2"
  shows "\<phi>\<^sub>1 = \<phi>\<^sub>2"
proof -
  let ?xs1 = "binencode (numlistlist (formula_n \<phi>\<^sub>1))"
  let ?xs2 = "binencode (numlistlist (formula_n \<phi>\<^sub>2))"
  have bin1: "binencodable (numlistlist (formula_n \<phi>\<^sub>1))"
    by (simp add: Suc_le_eq numeral_2_eq_2 proper_symbols_numlistlist symbols_lt_numlistlist)
  then have "bit_symbols ?xs1"
    using bit_symbols_binencode by simp
  then have 1: "string_to_symbols (symbols_to_string ?xs1) = ?xs1"
    using bit_symbols_to_symbols by simp

  have bin2: "binencodable (numlistlist (formula_n \<phi>\<^sub>2))"
    by (simp add: Suc_le_eq numeral_2_eq_2 proper_symbols_numlistlist symbols_lt_numlistlist)
  then have "bit_symbols ?xs2"
    using bit_symbols_binencode by simp
  then have "string_to_symbols (symbols_to_string ?xs2) = ?xs2"
    using bit_symbols_to_symbols by simp
  then have "?xs1 = ?xs2"
    using 1 assms by simp
  then have "numlistlist (formula_n \<phi>\<^sub>1) = numlistlist (formula_n \<phi>\<^sub>2)"
    using binencode_inj bin1 bin2 by simp
  then have "formula_n \<phi>\<^sub>1 = formula_n \<phi>\<^sub>2"
    using numlistlist_inj by simp
  then show ?thesis
    using formula_n_inj by simp
qed

text \<open>
While @{const formula_to_string} maps every CNF formula to a string, not every
string represents a CNF formula. We could just ignore such invalid strings and
define \SAT{} to only contain well-formed strings.  But this would implicitly
place these invalid strings in the complement of \SAT{}. While this does not
cause us any issues here, it would if we were to introduce co-$\NP$ and wanted
to show that $\overline{\mathtt{SAT}}$ is in co-$\NP$, as we would then have to
deal with the invalid strings. So it feels a little like cheating to ignore the
invalid strings like this.

Arora and Barak~\cite[p.~45 footnote~3]{ccama} recommend mapping invalid strings
to ``some fixed formula''.  A natural candidate for this fixed formula is the
empty CNF, since an invalid string in a sense represents nothing, and the empty
CNF formula is represented by the empty string. Since the empty CNF formula is
satisfiable this implies that all invalid strings become elements of \SAT{}.

We end up with the following definition of the protagonist of this article:
\<close>

definition SAT :: language where
  "SAT \<equiv> {formula_to_string \<phi> | \<phi>. satisfiable \<phi>} \<union> {x. \<not> (\<exists>\<phi>. x = formula_to_string \<phi>)}"


section \<open>\SAT{} is in $\NP$\label{s:Sat-np}\<close>

text \<open>
In order to show that \SAT{} is in $\NP$, we will construct a polynomial-time
Turing machine $M$ and specify a polynomial function $p$ such that for every
$x$, $x\in \SAT$ iff. there is a $u\in\bbOI^{p(|x|)}$ such that $M$ outputs
\textbf{1} on $\langle x; u\rangle$.

The idea is straightforward: Let $\phi$ be the formula represented by the
string $x$.  Interpret the string $u$ as a list of variables and interpret this
as the assignment that assigns True to only the variables in the list. Then
check if the assignment satisfies the formula. This check is ``obviously''
possible in polynomial time because $M$ simply has to iterate over all clauses
and check if at least one literal per clause is true under the assignment.
Checking if a literal is true is simply a matter of checking whether the
literal's variable is in the list $u$. If the assignment satisfies $\phi$,
output \textbf{1}, otherwise the empty symbol sequence.

If $\phi$ is unsatisfiable then no assignment, hence no $u$ no matter the length
will make $M$ output \textbf{1}. On the other hand, if $\phi$ is satisfiable
then there will be a satisfying assignment where a subset of the variables in
$\phi$ are assigned True. Hence there will be a list of variables of at most
roughly the length of $\phi$. So setting the polynomial $p$ to something like
$p(n) = n$ should suffice.

In fact, as we shall see, $p(n) = n$ suffices. This is so because in our
representation, the string $x$, being a list of lists, has slightly more
overhead per number than the plain list $u$ has. Therefore listing all variables
in $\phi$ is guaranteed to need fewer symbols than $x$ has.

There are several technical details to work out. First of all, the input to $M$
need not be a well-formed pair. And if it is, the pair $\langle x, u\rangle$ has
to be decoded into separate components $x$ and $u$. These have to be decoded
again from the binary to the quaternary alphabet, which is only possible if both
$x$ and $u$ comprise only bit symbols (\textbf{01}). Then $M$ needs to check if
the decoded $x$ and $u$ are valid symbol sequences for lists (of lists) of
numbers. In the case of $u$ this is particularly finicky because the definition
of $\NP$ requires us to provide a string $u$ of exactly the length $p(|x|)$ and
so we have to pad $u$ with extra symbols, which have to be stripped again before
the validation can take place.

In the first subsection we describe what the verifier TM has to do in terms of
symbol sequences. In the subsections after that we devise a Turing machine that
implements this behavior.
\<close>


subsection \<open>Verifying \SAT{} instances\<close>

text \<open>
Our verifier Turing machine for \SAT{} will implement the following function;
that is, on input @{term zs} it will output @{term "verify_sat zs"}.  It
performs a number of decodings and well-formedness checks and outputs either
\textbf{1} or the empty symbol sequence.
\<close>

definition verify_sat :: "symbol list \<Rightarrow> symbol list" where
  "verify_sat zs \<equiv>
    let
      ys = bindecode zs;
      xs = bindecode (first ys);
      vs = rstrip \<sharp> (bindecode (second ys))
    in
      if even (length (first ys)) \<and> bit_symbols (first ys) \<and> numlistlist_wf xs
      then if bit_symbols (second ys) \<and> numlist_wf vs
           then if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then [\<one>] else []
           else []
      else [\<one>]"

text \<open>
Next we show that @{const verify_sat} behaves as is required of a verifier TM
for \SAT. Its polynomial running time is the subject of the next subsection.
\<close>

text \<open>
First we consider the case that @{term zs} encodes a pair $\langle x, u\rangle$
of strings where $x$ does not represent a CNF formula. Such an $x$ is in \SAT{},
hence the verifier TM is supposed to output \textbf{1}.
\<close>

lemma ex_phi_x:
  assumes "xs = string_to_symbols x"
  assumes "even (length xs)" and "numlistlist_wf (bindecode xs)"
  shows "\<exists>\<phi>. x = formula_to_string \<phi>"
proof -
  obtain nss where "numlistlist nss = bindecode xs"
    using assms(3) numlistlist_wf_def by auto
  moreover have "binencode (bindecode xs) = xs"
    using assms(1,2) binencode_decode by simp
  ultimately have "binencode (numlistlist nss) = xs"
    by simp
  then have "binencode (numlistlist (formula_n (n_formula nss))) = xs"
    using formula_n_formula by simp
  then have "formula_to_string (n_formula nss) = symbols_to_string xs"
    by simp
  then show ?thesis
    using assms(1) symbols_to_string_to_symbols by auto
qed

lemma verify_sat_not_wf_phi:
  assumes "zs = \<langle>x; u\<rangle>" and "\<not> (\<exists>\<phi>. x = formula_to_string \<phi>)"
  shows "verify_sat zs = [\<one>]"
proof -
  define ys where "ys = bindecode zs"
  then have first_ys: "first ys = string_to_symbols x"
    using first_pair assms(1) by simp
  then have 2: "bit_symbols (first ys)"
    using assms(1) bit_symbols_first ys_def by presburger

  define xs where "xs = bindecode (first ys)"
  then have "\<not> (even (length (first ys)) \<and> bit_symbols (first ys) \<and> numlistlist_wf xs)"
    using first_ys ex_phi_x assms(2) by auto
  then show "verify_sat zs = [\<one>]"
    unfolding verify_sat_def Let_def using ys_def xs_def by simp
qed

text \<open>
The next case is that @{term zs} represents a pair $\langle x, u\rangle$ where
$x$ represents an unsatisfiable CNF formula. This $x$ is thus not in \SAT{} and
the verifier TM must output something different from \textbf{1}, such as the
empty string, regardless of $u$.
\<close>

lemma verify_sat_not_sat:
  fixes \<phi> :: formula
  assumes "zs = \<langle>formula_to_string \<phi>; u\<rangle>" and "\<not> satisfiable \<phi>"
  shows "verify_sat zs = []"
proof -
  have bs_phi: "bit_symbols (binencode (formula_zs \<phi>))"
    using bit_symbols_binencode formula_zs_def proper_symbols_numlistlist symbols_lt_numlistlist
    by (metis Suc_le_eq dual_order.refl numeral_2_eq_2)

  define ys where "ys = bindecode zs"
  then have "first ys = string_to_symbols (formula_to_string \<phi>)"
    using first_pair assms(1) by simp
  then have first_ys: "first ys = binencode (formula_zs \<phi>)"
    using bit_symbols_to_symbols bs_phi formula_zs_def by simp
  then have 2: "bit_symbols (first ys)"
    using assms(1) bit_symbols_first ys_def by presburger
  have 22: "even (length (first ys))"
    using first_ys by simp

  define xs where "xs = bindecode (first ys)"
  define vs where "vs = rstrip 5 (bindecode (second ys))"

  have wf_xs: "numlistlist_wf xs"
    using xs_def first_ys bindecode_encode formula_zs_def numlistlist_wf_def numlistlist_wf_has2'
    by (metis le_simps(3) numerals(2))

  have \<phi>: "zs_formula xs = \<phi>"
    using xs_def first_ys "2" binencode_decode formula_to_string_inj formula_zs_def formula_zs_formula wf_xs
    by auto

  have "verify_sat zs =
     (if bit_symbols (second ys) \<and> numlist_wf vs
      then if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> \<phi> then [3] else []
      else [])"
    unfolding verify_sat_def Let_def using ys_def xs_def vs_def 2 22 wf_xs \<phi> by simp
  then show "verify_sat zs = []"
    using assms(2) satisfiable_def by simp
qed

text \<open>
Next we consider the case in which @{term zs} represents a pair $\langle x,
u\rangle$ where $x$ represents a satisfiable CNF formula and $u$ a list of
numbers padded at the right with @{text \<sharp>} symbols. This $u$ thus represents a
variable assignment, namely the one assigning True to exactly the variables in
the list. The verifier TM is to output \textbf{1} iff.\ this assignment
satisfies the CNF formula represented by $x$.

First we show that stripping away @{text \<sharp>} symbols does not damage a symbol
sequence representing a list of numbers.
\<close>

lemma rstrip_numlist_append: "rstrip \<sharp> (numlist vars @ replicate pad \<sharp>) = numlist vars"
  (is "rstrip \<sharp> ?zs = ?ys")
proof -
  have "(LEAST i. i \<le> length ?zs \<and> set (drop i ?zs) \<subseteq> {\<sharp>}) = length ?ys"
  proof (rule Least_equality)
    show "length ?ys \<le> length ?zs \<and> set (drop (length ?ys) ?zs) \<subseteq> {\<sharp>}"
      by auto
    show "length ?ys \<le> m" if "m \<le> length ?zs \<and> set (drop m ?zs) \<subseteq> {\<sharp>}" for m
    proof (rule ccontr)
      assume "\<not> length ?ys \<le> m"
      then have "m < length ?ys"
        by simp
      then have "?ys ! m \<in> set (drop m ?ys)"
        by (metis Cons_nth_drop_Suc list.set_intros(1))
      moreover have "set (drop m ?ys) \<subseteq> {\<sharp>}"
        using that by simp
      ultimately have "?ys ! m = \<sharp>"
        by auto
      moreover have "?ys ! m < \<sharp>"
        using symbols_lt_numlist `m < length ?ys` by simp
      ultimately show False
        by simp
    qed
  qed
  then show ?thesis
    using rstrip_def by simp
qed

lemma verify_sat_wf:
  fixes \<phi> :: formula and pad :: nat
  assumes "zs = \<langle>formula_to_string \<phi>; symbols_to_string (binencode (numlist vars @ replicate pad \<sharp>))\<rangle>"
  shows "verify_sat zs = (if (\<lambda>v. v \<in> set vars) \<Turnstile> \<phi> then [\<one>] else [])"
proof -
  have bs_phi: "bit_symbols (binencode (formula_zs \<phi>))"
    using bit_symbols_binencode formula_zs_def proper_symbols_numlistlist symbols_lt_numlistlist
    by (metis Suc_le_eq dual_order.refl numeral_2_eq_2)

  have "binencodable (numlist vars @ replicate pad \<sharp>)"
    using proper_symbols_numlist symbols_lt_numlist binencodable_append[of "numlist vars" "replicate pad \<sharp>"]
    by fastforce
  then have bs_vars: "bit_symbols (binencode (numlist vars @ replicate pad \<sharp>))"
    using bit_symbols_binencode by simp

  define ys where "ys = bindecode zs"
  then have "first ys = string_to_symbols (formula_to_string \<phi>)"
    using first_pair assms(1) by simp
  then have first_ys: "first ys = binencode (formula_zs \<phi>)"
    using bit_symbols_to_symbols bs_phi formula_zs_def by simp
  then have bs_first: "bit_symbols (first ys)"
    using assms(1) bit_symbols_first ys_def by presburger

  have even: "even (length (first ys))"
    using first_ys by simp

  have second_ys: "second ys = binencode (numlist vars @ replicate pad \<sharp>)"
    using bs_vars ys_def assms(1) bit_symbols_to_symbols second_pair by simp
  then have bs_second: "bit_symbols (second ys)"
    using bs_vars by simp

  define xs where "xs = bindecode (first ys)"
  define vs where "vs = rstrip \<sharp> (bindecode (second ys))"

  then have "vs = rstrip \<sharp> (numlist vars @ replicate pad \<sharp>)"
    using second_ys \<open>binencodable (numlist vars @ replicate pad \<sharp>)\<close> bindecode_encode by simp
  then have vs: "vs = numlist vars"
    using rstrip_numlist_append by simp

  have wf_xs: "numlistlist_wf xs"
    using xs_def first_ys bindecode_encode formula_zs_def numlistlist_wf_def numlistlist_wf_has2'
    by (metis le_simps(3) numerals(2))

  have "verify_sat zs =
     (if even (length (first ys)) \<and> bit_symbols (first ys) \<and> numlistlist_wf xs
      then if bit_symbols (second ys) \<and> numlist_wf vs
           then if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then [\<one>] else []
           else []
      else [3])"
    unfolding verify_sat_def Let_def using bs_second ys_def xs_def vs_def by simp
  then have *: "verify_sat zs =
        (if bit_symbols (second ys) \<and> numlist_wf vs
         then if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then [\<one>] else []
         else [])"
    unfolding verify_sat_def Let_def using even bs_first wf_xs by simp

  have "xs = formula_zs \<phi>"
    using xs_def bindecode_encode formula_zs_def first_ys proper_symbols_numlistlist symbols_lt_numlistlist
    by (simp add: Suc_leI numerals(2))
  then have \<phi>: "\<phi> = zs_formula xs"
    by (simp add: zs_formula_zs)

  have vars: "vars = zs_numlist vs"
    using vs numlist_wf_def numlist_zs_numlist zs_numlist_ex1 by blast
  then have wf_vs: "numlist_wf vs"
    using numlist_wf_def vs by auto

  have "verify_sat zs = (if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then [\<one>] else [])"
    using * bs_second wf_xs wf_vs by simp
  then show ?thesis
    using \<phi> vars by simp
qed

text \<open>
Finally we show that for every string $x$ representing a satisfiable CNF formula
there is a list of numbers representing a satisfying assignment and represented
by a string of length at most $|x|$. That means there is always a string of
exactly the length of $x$ consisting of a satisfying assignment plus some
padding symbols.
\<close>

lemma nllength_remove1:
  assumes "n \<in> set ns"
  shows "nllength (n # remove1 n ns) = nllength ns"
  using assms nllength sum_list_map_remove1[of n ns "\<lambda>n. Suc (nlength n)"] by simp

lemma nllength_distinct_le:
  assumes "distinct ns"
    and "set ns \<subseteq> set ms"
  shows "nllength ns \<le> nllength ms"
  using assms
proof (induction ms arbitrary: ns)
  case Nil
  then show ?case
    by simp
next
  case (Cons m ms)
  show ?case
  proof (cases "m \<in> set ns")
    case True
    let ?ns = "remove1 m ns"
    have "set ?ns \<subseteq> set ms"
      using Cons by auto
    moreover have "distinct ?ns"
      using Cons by simp
    ultimately have *: "nllength ?ns \<le> nllength ms"
      using Cons by simp

    have "nllength ns = nllength (m # ?ns)"
      using True nllength_remove1 by simp
    also have "... = Suc (nlength m) + nllength ?ns"
      using nllength by simp
    also have "... \<le> Suc (nlength m) + nllength ms"
      using * by simp
    also have "... = nllength (m # ms)"
      using nllength by simp
    finally show ?thesis .
  next
    case False
    then have "set ns \<subseteq> set ms"
      using Cons by auto
    moreover have "distinct ns"
      using Cons by simp
    ultimately have "nllength ns \<le> nllength ms"
      using Cons by simp
    then show ?thesis
      using nllength by simp
  qed
qed

lemma nlllength_nllength_concat: "nlllength nss = nllength (concat nss) + length nss"
  using nlllength nllength by (induction nss) simp_all

fun variable :: "literal \<Rightarrow> nat" where
  "variable (Neg i) = i" |
  "variable (Pos i) = i"

lemma sum_list_eq: "ns = ms \<Longrightarrow> sum_list ns = sum_list ms"
  by simp

lemma nllength_clause_le: "nllength (clause_n cl) \<ge> nllength (map variable cl)"
proof -
  have "variable x \<le> literal_n x" for x
    by (cases x) simp_all
  then have *: "Suc (nlength (variable x)) \<le> Suc (nlength (literal_n x))" for x
    using nlength_mono by simp

  let ?ns = "map literal_n cl"
  have "nllength (clause_n cl) = nllength ?ns"
    using clause_n_def by presburger
  also have "... = (\<Sum>n\<leftarrow>?ns. Suc (nlength n))"
    using nllength by simp
  also have "... = (\<Sum>x\<leftarrow>cl. Suc (nlength (literal_n x)))"
    by (smt (verit, del_insts) length_map nth_equalityI nth_map)
  also have "... \<ge> (\<Sum>x\<leftarrow>cl. Suc (nlength (variable x)))"
    using * by (simp add: sum_list_mono)
  finally have "(\<Sum>x\<leftarrow>cl. Suc (nlength (variable x))) \<le> nllength (clause_n cl)"
    by simp
  moreover have "(\<Sum>x\<leftarrow>cl. Suc (nlength (variable x))) = nllength (map variable cl)"
  proof -
    have 1: "map (\<lambda>x. Suc (nlength (variable x))) cl = map (\<lambda>n. Suc (nlength n)) (map variable cl)"
      by simp
    then have "(\<Sum>x\<leftarrow>cl. Suc (nlength (variable x))) = (\<Sum>n\<leftarrow>(map variable cl). Suc (nlength n))"
      using sum_list_eq[OF 1] by simp
    then show ?thesis
      using nllength by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma nlllength_formula_ge: "nlllength (formula_n \<phi>) \<ge> nlllength (map (map variable) \<phi>)"
proof (induction \<phi>)
  case Nil
  then show ?case
    by simp
next
  case (Cons cl \<phi>)
  have "nlllength (map (map variable) (cl # \<phi>)) =
      nlllength (map (map variable) [cl]) + nlllength (map (map variable) \<phi>)"
    using nlllength by simp
  also have "... = Suc (nllength (map variable cl)) + nlllength (map (map variable) \<phi>)"
    using nlllength by simp
  also have "... \<le> Suc (nllength (map variable cl)) + nlllength (formula_n \<phi>)"
    using Cons by simp
  also have "... \<le> Suc (nllength (clause_n cl)) + nlllength (formula_n \<phi>)"
    using nllength_clause_le by simp
  also have "... = nlllength (formula_n (cl # \<phi>))"
    using nlllength by (simp add: formula_n_def)
  finally show ?case .
qed

lemma variables_shorter_formula:
  fixes \<phi> :: formula and vars :: "nat list"
  assumes "set vars \<subseteq> variables \<phi>" and "distinct vars"
  shows "nllength vars \<le> nlllength (formula_n \<phi>)"
proof -
  let ?nss = "map (map variable) \<phi>"
  have "nllength (concat ?nss) \<le> nlllength ?nss"
    using nlllength_nllength_concat by simp
  then have *: "nllength (concat ?nss) \<le> nlllength (formula_n \<phi>)"
    using nlllength_formula_ge by (meson le_trans)

  have "set vars \<subseteq> set (concat ?nss)"
  proof
    fix n :: nat
    assume "n \<in> set vars"
    then have "n \<in> variables \<phi>"
      using assms(1) by auto
    then obtain c where c: "c \<in> set \<phi>" "Neg n \<in> set c \<or> Pos n \<in> set c"
      using variables_def by auto
    then obtain x where x: "x \<in> set c" "variable x = n"
      by auto
    then show "n \<in> set (concat (map (map variable) \<phi>))"
      using c by auto
  qed
  then have "nllength vars \<le> nllength (concat ?nss)"
    using nllength_distinct_le assms(2) by simp
  then show ?thesis
    using * by simp
qed

lemma ex_assignment_linear_length:
  assumes "satisfiable \<phi>"
  shows "\<exists>vars. (\<lambda>v. v \<in> set vars) \<Turnstile> \<phi> \<and> nllength vars \<le> nlllength (formula_n \<phi>)"
proof -
  obtain \<alpha> where \<alpha>: "\<alpha> \<Turnstile> \<phi>"
    using assms satisfiable_def by auto
  define poss where "poss = {v. v \<in> variables \<phi> \<and> \<alpha> v}"
  then have "finite poss"
    using finite_variables by simp

  let ?beta = "\<lambda>v. v \<in> poss"
  have sat: "?beta \<Turnstile> \<phi>"
    unfolding satisfies_def
  proof
    fix c :: clause
    assume "c \<in> set \<phi>"
    then have "satisfies_clause \<alpha> c"
      using satisfies_def \<alpha> by simp
    then obtain x where x: "x \<in> set c" "satisfies_literal \<alpha> x"
      using satisfies_clause_def by auto
    show "satisfies_clause ?beta c"
    proof (cases x)
      case (Neg n)
      then have "\<not> \<alpha> n"
        using x(2) by simp
      then have "n \<notin> poss"
        using poss_def by simp
      then have "\<not> ?beta n"
        by simp
      then have "satisfies_literal ?beta x"
        using Neg by simp
      then show ?thesis
        using satisfies_clause_def x(1) by auto
    next
      case (Pos n)
      then have "\<alpha> n"
        using x(2) by simp
      then have "n \<in> poss"
        using poss_def Pos \<open>c \<in> set \<phi>\<close> variables_def x(1) by auto
      then have "?beta n"
        by simp
      then have "satisfies_literal ?beta x"
        using Pos by simp
      then show ?thesis
        using satisfies_clause_def x(1) by auto
    qed
  qed

  obtain vars where vars: "set vars = poss" "distinct vars"
    using `finite poss` by (meson finite_distinct_list)
  moreover from this have "set vars \<subseteq> variables \<phi>"
    using poss_def by simp
  ultimately have "nllength vars \<le> nlllength (formula_n \<phi>)"
    using variables_shorter_formula by simp
  moreover have "(\<lambda>v. v \<in> set vars) \<Turnstile> \<phi>"
    using vars(1) sat by simp
  ultimately show ?thesis
    by auto
qed

lemma ex_witness_linear_length:
  fixes \<phi> :: formula
  assumes "satisfiable \<phi>"
  shows "\<exists>us.
    bit_symbols us \<and>
    length us = length (formula_to_string \<phi>) \<and>
    verify_sat \<langle>formula_to_string \<phi>; symbols_to_string us\<rangle> = [\<one>]"
proof -
  obtain vars where vars:
    "(\<lambda>v. v \<in> set vars) \<Turnstile> \<phi>"
    "nllength vars \<le> nlllength (formula_n \<phi>)"
    using assms ex_assignment_linear_length by auto

  define pad where "pad = nlllength (formula_n \<phi>) - nllength vars"
  then have "nllength vars + pad = nlllength (formula_n \<phi>)"
    using vars(2) by simp
  moreover define us where "us = numlist vars @ replicate pad \<sharp>"
  ultimately have "length us = nlllength (formula_n \<phi>)"
    by (simp add: nllength_def)
  then have "length (binencode us) = length (formula_to_string \<phi>)" (is "length ?us = _")
    by (simp add: nlllength_def)
  moreover have "verify_sat \<langle>formula_to_string \<phi>; symbols_to_string ?us\<rangle> = [\<one>]"
    using us_def vars(1) assms verify_sat_wf by simp
  moreover have "bit_symbols ?us"
  proof -
    have "binencodable (numlist vars)"
      using proper_symbols_numlist symbols_lt_numlist
      by (metis Suc_leI lessI less_Suc_numeral numeral_2_eq_2 numeral_le_iff numeral_less_iff
        order_less_le_trans pred_numeral_simps(3) semiring_norm(74))
    moreover have "binencodable (replicate pad \<sharp>)"
      by simp
    ultimately have "binencodable us"
      using us_def binencodable_append by simp
    then show ?thesis
      using bit_symbols_binencode by simp
  qed
  ultimately show ?thesis
    by blast
qed

lemma bit_symbols_verify_sat: "bit_symbols (verify_sat zs)"
  unfolding verify_sat_def Let_def by simp


subsection \<open>A Turing machine for verifying formulas\<close>

text \<open>
The core of the function @{const verify_sat} is the expression @{term " (\<lambda>v. v \<in>
set (zs_numlist vs)) \<Turnstile> zs_formula xs"}, which checks if an assignment
represented by a list of variable indices satisfies a CNF formula represented by
a list of lists of literals. In this section we devise a Turing machine
performing this check.

Recall that the numbers 0 and 1 are represented by the empty symbol sequence
and the symbol sequence \textbf{1}, respectively. The Turing machines in this
section are described in terms of numbers.

We start with a Turing machine that checks a clause. The TM accepts on tape
$j_1$ a list of numbers representing an assignment $\alpha$ and on tape $j_2$ a
list of numbers representing a clause. It outputs on tape $j_3$ the number 1 if
$\alpha$ satisfies the clause, and otherwise 0. To do this the TM iterates over
all literals in the clause and determines the underlying variable and the sign
of the literal. If the literal is positive and the variable is in the list
representing $\alpha$ or if the literal is negative and the variable is not in
the list, the number 1 is written to the tape $j_3$. Otherwise the tape remains
unchanged. We assume $j_3$ is initialized with 0, and so it will be 1 if and
only if at least one literal is satisfied by $\alpha$.

The TM requires five auxiliary tapes $j_3 + 1, \dots, j_3 + 5$. Tape $j_3 + 1$
stores the literals one at a time, and later the variable; tape $j_3 + 2$ stores
the sign of the literal; tape $j_3 + 3$ stores whether the variable is contained
in $\alpha$; tapes $j_3 + 4$ and $j_3 + 5$ are the auxiliary tapes of @{const
tm_contains}.
\<close>

definition tm_sat_clause :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_sat_clause j1 j2 j3 \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j2 \<noteq> \<box> DO
      tm_nextract 4 j2 (j3 + 1) ;;
      tm_mod2 (j3 + 1) (j3 + 2) ;;
      tm_div2 (j3 + 1) ;;
      tm_contains j1 (j3 + 1) (j3 + 3) ;;
      IF \<lambda>rs. rs ! (j3 + 3) = \<box> \<and> rs ! (j3 + 2) = \<box> \<or> rs ! (j3 + 3) \<noteq> \<box> \<and> rs ! (j3 + 2) \<noteq> \<box> THEN
        tm_setn j3 1
      ELSE
        []
      ENDIF ;;
      tm_setn (j3 + 1) 0 ;;
      tm_setn (j3 + 2) 0 ;;
      tm_setn (j3 + 3) 0
    DONE ;;
    tm_cr j2"

lemma tm_sat_clause_tm:
  assumes "k \<ge> 2" and "G \<ge> 5" and "j3 + 5 < k" "0 < j1" "j1 < k" "j2 < k" "j1 < j3"
  shows "turing_machine k G (tm_sat_clause j1 j2 j3)"
  using tm_sat_clause_def tm_mod2_tm tm_div2_tm tm_nextract_tm tm_setn_tm tm_contains_tm Nil_tm tm_cr_tm
    assms turing_machine_loop_turing_machine turing_machine_branch_turing_machine
  by simp

locale turing_machine_sat_clause =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tmL1 \<equiv> tm_nextract 4 j2 (j3 + 1)"
definition "tmL2 \<equiv> tmL1 ;; tm_mod2 (j3 + 1) (j3 + 2)"
definition "tmL3 \<equiv> tmL2 ;; tm_div2 (j3 + 1)"
definition "tmL4 \<equiv> tmL3 ;; tm_contains j1 (j3 + 1) (j3 + 3)"
definition "tmI \<equiv> IF \<lambda>rs. rs ! (j3 + 3) = \<box> \<and> rs ! (j3 + 2) = \<box> \<or> rs ! (j3 + 3) \<noteq> \<box> \<and> rs ! (j3 + 2) \<noteq> \<box> THEN tm_setn j3 1 ELSE [] ENDIF"
definition "tmL5 \<equiv> tmL4 ;; tmI"
definition "tmL6 \<equiv> tmL5 ;; tm_setn (j3 + 1) 0"
definition "tmL7 \<equiv> tmL6 ;; tm_setn (j3 + 2) 0"
definition "tmL8 \<equiv> tmL7 ;; tm_setn (j3 + 3) 0"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j2 \<noteq> \<box> DO tmL8 DONE"
definition "tm2 \<equiv> tmL ;; tm_cr j2"

lemma tm2_eq_tm_sat_clause: "tm2 = tm_sat_clause j1 j2 j3"
  unfolding tm2_def tmL_def tmL8_def tmL7_def tmL6_def tmL5_def tmL4_def tmL3_def tmI_def
    tmL2_def tmL1_def tm_sat_clause_def
  by simp

context
  fixes tps0 :: "tape list" and k :: nat and vars :: "nat list" and clause :: clause
  assumes jk: "0 < j1" "j1 \<noteq> j2" "j3 + 5 < k" "j1 < j3" "j2 < j3" "0 < j2" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = nltape' vars 0"
    "tps0 ! j2 = nltape' (clause_n clause) 0"
    "tps0 ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

abbreviation "sat_take t \<equiv> satisfies_clause (\<lambda>v. v \<in> set vars) (take t clause)"

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j2 := nltape' (clause_n clause) t,
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1)]"

lemma tpsL0: "tpsL 0 = tps0"
proof -
  have "nltape' (clause_n clause) 0 = tps0 ! j2"
    using tps0(2) by presburger
  moreover have "\<lfloor>sat_take 0\<rfloor>\<^sub>B = \<lfloor>0\<rfloor>\<^sub>N"
    using satisfies_clause_def by simp
  ultimately show ?thesis
    using tpsL_def tps0 jk by (metis list_update_id)
qed

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>literal_n (clause ! t)\<rfloor>\<^sub>N, 1)]"

lemma tmL1 [transforms_intros]:
  assumes "ttt = 12 + 2 * nlength (clause_n clause ! t)" and "t < length (clause_n clause)"
  shows "transforms tmL1 (tpsL t) ttt (tpsL1 t)"
  unfolding tmL1_def
proof (tform tps: assms tps0 tpsL_def tpsL1_def jk)
  have len: "t < length clause"
    using assms(2) clause_n_def by simp
  show "ttt = 12 + 2 * nlength 0 + 2 * nlength (clause_n clause ! t)"
    using assms(1) by simp
  have *: "j2 \<noteq> j3"
    using jk by simp
  have **: "clause_n clause ! t = literal_n (clause ! t)"
    using len by (simp add: clause_n_def)
  show "tpsL1 t = (tpsL t)
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 + 1 := (\<lfloor>clause_n clause ! t\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL_def tpsL1_def using list_update_swap[OF *, of tps0] by (simp add: **)
qed

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>literal_n (clause ! t)\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>literal_n (clause ! t) mod 2\<rfloor>\<^sub>N, 1)]"

lemma tmL2 [transforms_intros]:
  assumes "ttt = 12 + 2 * nlength (clause_n clause ! t) + 1"
    and "t < length (clause_n clause)"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def by (tform tps: assms tps0 tpsL2_def tpsL1_def jk)

definition tpsL3 :: "nat \<Rightarrow> tape list" where
  "tpsL3 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>literal_n (clause ! t) div 2\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>literal_n (clause ! t) mod 2\<rfloor>\<^sub>N, 1)]"

lemma tmL3 [transforms_intros]:
  assumes "ttt = 16 + 4 * nlength (clause_n clause ! t)"
    and "t < length (clause_n clause)"
  shows "transforms tmL3 (tpsL t) ttt (tpsL3 t)"
  unfolding tmL3_def
proof (tform tps: assms(2) tps0 tpsL3_def tpsL2_def jk)
  have len: "t < length clause"
    using assms(2) clause_n_def by simp
  have **: "clause_n clause ! t = literal_n (clause ! t)"
    using len by (simp add: clause_n_def)
  show "ttt = 12 + 2 * nlength (clause_n clause ! t) + 1 + (2 * nlength (literal_n (clause ! t)) + 3)"
    using assms(1) ** by simp
qed

definition tpsL4 :: "nat \<Rightarrow> tape list" where
  "tpsL4 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>literal_n (clause ! t) div 2\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>literal_n (clause ! t) mod 2\<rfloor>\<^sub>N, 1),
     j3 + 3 := (\<lfloor>literal_n (clause ! t) div 2 \<in> set vars\<rfloor>\<^sub>B, 1)]"

lemma tmL4 [transforms_intros]:
  assumes "ttt = 20 + 4 * nlength (clause_n clause ! t) + 67 * (nllength vars)\<^sup>2"
    and "t < length (clause_n clause)"
  shows "transforms tmL4 (tpsL t) ttt (tpsL4 t)"
  unfolding tmL4_def
proof (tform tps: assms(2) tps0 tpsL4_def tpsL3_def jk time: assms(1))
  have "tpsL3 t ! (j3 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL3_def tps0 jk by simp
  then show "tpsL3 t ! (j3 + 3 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by (metis ab_semigroup_add_class.add_ac(1) numeral_plus_one semiring_norm(2) semiring_norm(8))
  have "tpsL3 t ! (j3 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL3_def tps0 jk by simp
  then show "tpsL3 t ! (j3 + 3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by (simp add: numeral_Bit1)
qed

definition tpsL5 :: "nat \<Rightarrow> tape list" where
  "tpsL5 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>literal_n (clause ! t) div 2\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>literal_n (clause ! t) mod 2\<rfloor>\<^sub>N, 1),
     j3 + 3 := (\<lfloor>literal_n (clause ! t) div 2 \<in> set vars\<rfloor>\<^sub>B, 1)]"

lemma tmI [transforms_intros]:
  assumes "ttt = 16" and "t < length (clause_n clause)"
  shows "transforms tmI (tpsL4 t) ttt (tpsL5 t)"
  unfolding tmI_def
proof (tform tps: jk tpsL4_def time: assms(1))
  show "10 + 2 * nlength (if sat_take t then 1 else 0) + 2 * nlength 1 + 2 \<le> ttt"
    using assms(1) nlength_0 nlength_1_simp by simp

  have len: "t < length clause"
    using assms(2) by (simp add: clause_n_def)

  let ?l = "clause ! t"
  have 1: "read (tpsL4 t) ! (j3 + 3) = \<box> \<longleftrightarrow> literal_n ?l div 2 \<notin> set vars"
    using tpsL4_def jk read_ncontents_eq_0[of "tpsL4 t" "j3 + 3"] by simp
  have 2: "read (tpsL4 t) ! (j3 + 2) = \<box> \<longleftrightarrow> literal_n ?l mod 2 = 0"
    using tpsL4_def jk read_ncontents_eq_0[of "tpsL4 t" "j3 + 2"] by simp

  let ?a = "\<lambda>v. v \<in> set vars"
  let ?cond = "read (tpsL4 t) ! (j3 + 3) = \<box> \<and> read (tpsL4 t) ! (j3 + 2) = \<box> \<or>
    read (tpsL4 t) ! (j3 + 3) \<noteq> \<box> \<and> read (tpsL4 t) ! (j3 + 2) \<noteq> \<box>"
  have *: "?cond \<longleftrightarrow> satisfies_literal ?a ?l"
  proof (cases ?l)
    case (Neg v)
    then have "literal_n ?l div 2 = v" "literal_n ?l mod 2 = 0"
      by simp_all
    moreover from this have "satisfies_literal ?a ?l \<longleftrightarrow> v \<notin> set vars"
      using Neg by simp
    ultimately show ?thesis
      using 1 2 by simp
  next
    case (Pos v)
    then have "literal_n ?l div 2 = v" "literal_n ?l mod 2 = 1"
      by simp_all
    moreover from this have "satisfies_literal ?a ?l \<longleftrightarrow> v \<in> set vars"
      using Pos by simp
    ultimately show ?thesis
      using 1 2 by simp
  qed

  have **: "sat_take (Suc t) \<longleftrightarrow> sat_take t \<or> satisfies_literal ?a ?l"
    using satisfies_clause_take[OF len] by simp

  show "tpsL5 t = (tpsL4 t)[j3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]" if ?cond
  proof -
    have "(if sat_take (Suc t) then 1::nat else 0) = 1"
      using that * ** by simp
    then show ?thesis
      unfolding tpsL5_def tpsL4_def using that by (simp add: list_update_swap)
  qed
  show "tpsL5 t = (tpsL4 t)" if "\<not> ?cond"
  proof -
    have "sat_take t = sat_take (Suc t)"
      using * ** that by simp
    then show ?thesis
      unfolding tpsL5_def tpsL4_def using that by (simp add: list_update_swap)
  qed
qed

lemma tmL5 [transforms_intros]:
  assumes "ttt = 36 + 4 * nlength (clause_n clause ! t) + 67 * (nllength vars)\<^sup>2"
    and "t < length (clause_n clause)"
  shows "transforms tmL5 (tpsL t) ttt (tpsL5 t)"
  unfolding tmL5_def by (tform tps: assms)

definition tpsL6 :: "nat \<Rightarrow> tape list" where
  "tpsL6 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>literal_n (clause ! t) mod 2\<rfloor>\<^sub>N, 1),
     j3 + 3 := (\<lfloor>literal_n (clause ! t) div 2 \<in> set vars\<rfloor>\<^sub>B, 1)]"

lemma tmL6 [transforms_intros]:
  assumes "ttt = 46 + 4 * nlength (clause_n clause ! t) + 67 * (nllength vars)\<^sup>2 + 2 * nlength (literal_n (clause ! t) div 2)"
    and "t < length (clause_n clause)"
  shows "transforms tmL6 (tpsL t) ttt (tpsL6 t)"
  unfolding tmL6_def by (tform tps: assms tps0 tpsL6_def tpsL5_def jk)

definition tpsL7 :: "nat \<Rightarrow> tape list" where
  "tpsL7 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 3 := (\<lfloor>literal_n (clause ! t) div 2 \<in> set vars\<rfloor>\<^sub>B, 1)]"

lemma tmL7 [transforms_intros]:
  assumes "ttt = 56 + 4 * nlength (clause_n clause ! t) + 67 * (nllength vars)\<^sup>2 + 2 * nlength (literal_n (clause ! t) div 2) +
      2 * nlength (literal_n (clause ! t) mod 2)"
    and "t < length (clause_n clause)"
  shows "transforms tmL7 (tpsL t) ttt (tpsL7 t)"
  unfolding tmL7_def by (tform tps: assms tps0 tpsL7_def tpsL6_def jk)

definition tpsL8 :: "nat \<Rightarrow> tape list" where
  "tpsL8 t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tmL8:
  assumes "ttt = 66 + 4 * nlength (clause_n clause ! t) + 67 * (nllength vars)\<^sup>2 +
      2 * nlength (literal_n (clause ! t) div 2) +
      2 * nlength (literal_n (clause ! t) mod 2) +
      2 * nlength (if literal_n (clause ! t) div 2 \<in> set vars then 1 else 0)"
    and "t < length (clause_n clause)"
  shows "transforms tmL8 (tpsL t) ttt (tpsL8 t)"
  unfolding tmL8_def by (tform tps: assms tps0 tpsL8_def tpsL7_def jk)

lemma tmL8':
  assumes "ttt = 70 + 6 * nllength (clause_n clause) + 67 * (nllength vars)\<^sup>2"
    and "t < length (clause_n clause)"
  shows "transforms tmL8 (tpsL t) ttt (tpsL8 t)"
proof -
  let ?l = "literal_n (clause ! t)"
  let ?ll = "clause_n clause ! t"
  let ?t = "66 + 4 * nlength ?ll + 67 * (nllength vars)\<^sup>2 +
      2 * nlength (?l div 2) + 2 * nlength (?l mod 2) + 2 * nlength (if ?l div 2 \<in> set vars then 1 else 0)"
  have "?t = 66 + 4 * nlength ?ll + 67 * (nllength vars)\<^sup>2 +
      2 * nlength (?ll div 2) + 2 * nlength (?ll mod 2) + 2 * nlength (if ?ll div 2 \<in> set vars then 1 else 0)"
    using assms(2) clause_n_def by simp
  also have "... \<le> 66 + 4 * nlength ?ll + 67 * (nllength vars)\<^sup>2 +
      2 * nlength ?ll + 2 * nlength (?ll mod 2) + 2 * nlength (if ?ll div 2 \<in> set vars then 1 else 0)"
    using nlength_mono[of "?ll div 2" "?ll"] by simp
  also have "... = 66 + 6 * nlength ?ll + 67 * (nllength vars)\<^sup>2 +
      2 * nlength (?ll mod 2) + 2 * nlength (if ?ll div 2 \<in> set vars then 1 else 0)"
    by simp
  also have "... \<le> 66 + 6 * nlength ?ll + 67 * (nllength vars)\<^sup>2 +
      2 * nlength 1 + 2 * nlength (if ?ll div 2 \<in> set vars then 1 else 0)"
    using nlength_mono by simp
  also have "... \<le> 66 + 6 * nlength ?ll + 67 * (nllength vars)\<^sup>2 + 2 * nlength 1 + 2 * nlength 1"
    using nlength_mono by simp
  also have "... = 70 + 6 * nlength ?ll + 67 * (nllength vars)\<^sup>2"
    using nlength_1_simp by simp
  also have "... \<le> 70 + 6 * nllength (clause_n clause) + 67 * (nllength vars)\<^sup>2"
    using assms(2) member_le_nllength by simp
  finally have "?t \<le> ttt"
    using assms(1) by simp
  then show ?thesis
    using assms tmL8 transforms_monotone by blast
qed

definition tpsL8' :: "nat \<Rightarrow> tape list" where
  "tpsL8' t \<equiv> tps0
    [j2 := nltape' (clause_n clause) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1)]"

lemma tpsL8': "tpsL8' = tpsL8"
proof -
  { fix t :: nat
    have "tpsL8 t = tps0
      [j2 := nltape' (clause_n clause) (Suc t),
       j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
       j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
       j3 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
      unfolding tpsL8_def
      using tps0 list_update_id[of "tps0" "j3 + 3"] jk
      by (simp add: list_update_swap[of _ "j3 + 3"])
    also have "... = tps0
      [j2 := nltape' (clause_n clause) (Suc t),
       j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
       j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
      unfolding tpsL8_def
      using tps0 list_update_id[of "tps0" "j3 + 2"] jk
      by (simp add: list_update_swap[of _ "Suc (Suc j3)"])
    also have "... = tps0
      [j2 := nltape' (clause_n clause) (Suc t),
       j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1)]"
      unfolding tpsL8_def
      using tps0 list_update_id[of "tps0" "j3 + 1"] jk
      by (simp add: list_update_swap[of _ "Suc j3"])
    also have "... = tpsL8' t"
      using tpsL8'_def by simp
    finally have "tpsL8 t = tpsL8' t" .
  }
  then show ?thesis
    by auto
qed

lemma tmL8'' [transforms_intros]:
  assumes "ttt = 70 + 6 * nllength (clause_n clause) + 67 * (nllength vars)\<^sup>2"
    and "t < length (clause_n clause)"
  shows "transforms tmL8 (tpsL t) ttt (tpsL8' t)"
  using tmL8' tpsL8' assms by simp

lemma tmL [transforms_intros]:
  assumes "ttt = length (clause_n clause) * (72 + 6 * nllength (clause_n clause) + 67 * (nllength vars)\<^sup>2) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length (clause_n clause)))"
  unfolding tmL_def
proof (tform)
  let ?t = "70 + 6 * nllength (clause_n clause) + 67 * (nllength vars)\<^sup>2"
  have "tpsL8' t = tpsL (Suc t)" for t
    using tpsL8'_def tpsL_def by simp
  then show "\<And>i. i < length (clause_n clause) \<Longrightarrow> transforms tmL8 (tpsL i) ?t (tpsL (Suc i))"
    using tmL8'' by simp

  let ?ns = "clause_n clause"
  have *: "tpsL t ! j2 = nltape' ?ns t" for t
    using tpsL_def jk by simp
  moreover have "read (tpsL t) ! j2 = tpsL t :.: j2" for t
    using tapes_at_read'[of j2 "tpsL t"] tpsL_def jk by simp
  ultimately have "read (tpsL t) ! j2 = |.| (nltape' ?ns t)" for t
    by simp
  then have "read (tpsL t) ! j2 = \<box> \<longleftrightarrow> (t \<ge> length ?ns)" for t
    using nltape'_tape_read by simp
  then show
      "\<And>i. i < length ?ns \<Longrightarrow> read (tpsL i) ! j2 \<noteq> \<box>"
      "\<not> read (tpsL (length ?ns)) ! j2 \<noteq> \<box>"
    using * by simp_all

  show "length ?ns * (70 + 6 * nllength ?ns + 67 * (nllength vars)\<^sup>2 + 2) + 1 \<le> ttt"
    using assms by simp
qed

definition tps1 :: "tape list" where
  "tps1 \<equiv> tps0
    [j2 := nltape' (clause_n clause) (length (clause_n clause)),
     j3 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) clause\<rfloor>\<^sub>B, 1)]"

lemma tps1: "tps1 = tpsL (length (clause_n clause))"
proof -
  have "length (clause_n clause) = length clause"
    by (simp add: clause_n_def)
  then show ?thesis
    using tps1_def tpsL_def by simp
qed

lemma tm1 [transforms_intros]:
  assumes "ttt = length (clause_n clause) * (72 + 6 * nllength (clause_n clause) + 67 * (nllength vars)\<^sup>2) + 1"
  shows "transforms tmL tps0 ttt tps1"
  using tmL tpsL0 assms tps1 by simp

definition tps2 :: "tape list" where
  "tps2 \<equiv> tps0
    [j2 := nltape' (clause_n clause) 0,
     j3 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) clause\<rfloor>\<^sub>B, 1)]"

lemma tm2:
  assumes "ttt = length (clause_n clause) * (72 + 6 * nllength (clause_n clause) + 67 * (nllength vars)\<^sup>2) +
      nllength (clause_n clause) + 4"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: assms tps0 tps1_def jk)
  have *: "tps1 ! j2 = nltape' (clause_n clause) (length (clause_n clause))"
    using tps1_def jk by simp
  then show "clean_tape (tps1 ! j2)"
    using clean_tape_nlcontents by simp
  have neq: "j3 \<noteq> j2"
    using jk by simp
  have "tps2 = tps1[j2 := nltape' (clause_n clause) 0]"
    unfolding tps2_def tps1_def by (simp add: list_update_swap[OF neq])
  moreover have "tps1 ! j2 |#=| 1 = nltape' (clause_n clause) 0"
    using * by simp
  ultimately show "tps2 = tps1[j2 := tps1 ! j2 |#=| 1]"
    by simp
qed

definition tps2' :: "tape list" where
  "tps2' \<equiv> tps0
    [j3 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) clause\<rfloor>\<^sub>B, 1)]"

lemma tm2':
  assumes "ttt = 79 * (nllength (clause_n clause)) ^ 2 + 67 * (nllength (clause_n clause)) * nllength vars ^ 2 + 4"
  shows "transforms tm2 tps0 ttt tps2'"
proof -
  let ?l = "nllength (clause_n clause)"
  let ?t = "length (clause_n clause) * (72 + 6 * ?l + 67 * (nllength vars)\<^sup>2) + ?l + 4"
  have "?t \<le> ?l * (72 + 6 * ?l + 67 * (nllength vars)\<^sup>2) + ?l + 4"
    by (simp add: length_le_nllength)
  also have "... = ?l * (73 + 6 * ?l + 67 * (nllength vars)\<^sup>2) + 4"
    by algebra
  also have "... = 73 * ?l + 6 * ?l ^ 2 + 67 * ?l * (nllength vars)\<^sup>2 + 4"
    by algebra
  also have "... \<le> 79 * ?l ^ 2 + 67 * ?l * (nllength vars)\<^sup>2 + 4"
    using linear_le_pow by simp
  finally have "?t \<le> ttt"
    using assms by simp
  moreover have "tps2' = tps2"
    unfolding tps2'_def tps2_def using jk tps0 by (metis tape_list_eq)
  ultimately show ?thesis
    using tps2'_def tm2 assms transforms_monotone by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_sat_clauseI [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k :: nat and vars :: "nat list" and clause :: "literal list"
  assumes "0 < j1" "j1 \<noteq> j2" "j3 + 5 < k" "j1 < j3" "j2 < j3" "0 < j2" "length tps = k"
  assumes
    "tps ! j1 = nltape' vars 0"
    "tps ! j2 = nltape' (clause_n clause) 0"
    "tps ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "tps' = tps
    [j3 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) clause\<rfloor>\<^sub>B, 1)]"
  assumes "ttt = 79 * (nllength (clause_n clause)) ^ 2 + 67 * (nllength (clause_n clause)) * nllength vars ^ 2 + 4"
  shows "transforms (tm_sat_clause j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_sat_clause j1 j2 j3 .
  show ?thesis
    using assms loc.tps2'_def loc.tm2' loc.tm2_eq_tm_sat_clause by simp
qed

text \<open>
The following Turing machine expects a list of lists of numbers representing a
formula $\phi$ on tape $j_1$ and a list of numbers representing an assignment
$\alpha$ on tape $j_2$. It outputs on tape $j_3$ the number 1 if $\alpha$
satisfies $\phi$, and otherwise the number 0. To do so the TM iterates over all
clauses in $\phi$ and uses @{const tm_sat_clause} on each of them. It requires
seven auxiliary tapes: $j_3 + 1$ to store the clauses one at a time, $j_3 + 2$ to
store the results of @{const tm_sat_clause}, whose auxiliary tapes are $j_3 + 3,
\dots, j_3 + 7$.
\<close>

definition tm_sat_formula :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_sat_formula j1 j2 j3 \<equiv>
    tm_setn j3 1 ;;
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      tm_nextract \<sharp> j1 (j3 + 1) ;;
      tm_sat_clause j2 (j3 + 1) (j3 + 2) ;;
      IF \<lambda>rs. rs ! (j3 + 2) = \<box> THEN
        tm_setn j3 0
      ELSE
        []
      ENDIF ;;
      tm_erase_cr (j3 + 1) ;;
      tm_setn (j3 + 2) 0
    DONE"

lemma tm_sat_formula_tm:
  assumes "k \<ge> 2" and "G \<ge> 6" and "0 < j1" "j1 \<noteq> j2" "j3 + 7 < k" "j1 < j3" "j2 < j3" "0 < j2"
  shows "turing_machine k G (tm_sat_formula j1 j2 j3)"
  using tm_sat_formula_def tm_sat_clause_tm tm_nextract_tm tm_setn_tm assms Nil_tm tm_erase_cr_tm
    turing_machine_loop_turing_machine turing_machine_branch_turing_machine
  by simp

locale turing_machine_sat_formula =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tm1 \<equiv> tm_setn j3 1"

definition "tmL1 \<equiv> tm_nextract \<sharp> j1 (j3 + 1)"
definition "tmL2 \<equiv> tmL1 ;; tm_sat_clause j2 (j3 + 1) (j3 + 2)"
definition "tmI \<equiv> IF \<lambda>rs. rs ! (j3 + 2) = \<box> THEN tm_setn j3 0 ELSE [] ENDIF"
definition "tmL3 \<equiv> tmL2 ;; tmI"
definition "tmL4 \<equiv> tmL3 ;; tm_erase_cr (j3 + 1)"
definition "tmL5 \<equiv> tmL4 ;; tm_setn (j3 + 2) 0"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tmL5 DONE"

definition "tm2 \<equiv> tm1 ;; tmL"

lemma tm2_eq_tm_sat_formula: "tm2 = tm_sat_formula j1 j2 j3"
  unfolding tm2_def tm1_def tmL_def tmL5_def tmL4_def tmL3_def tmI_def tmL2_def tmL1_def tm_sat_formula_def
  by simp

context
  fixes tps0 :: "tape list" and k :: nat and vars :: "nat list" and \<phi> :: formula
  assumes jk: "0 < j1" "j1 \<noteq> j2" "j3 + 7 < k" "j1 < j3" "j2 < j3" "0 < j2" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = nlltape' (formula_n \<phi>) 0"
    "tps0 ! j2 = nltape' vars 0"
    "tps0 ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 1) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps0 ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 6) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps0 ! (j3 + 7) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 12"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def jk)
  show "ttt = 10 + 2 * nlength 0 + 2 * nlength 1"
    using assms nlength_1_simp by simp
qed

abbreviation "sat_take t \<equiv> (\<lambda>v. v \<in> set vars) \<Turnstile> take t \<phi>"

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j1 := nlltape' (formula_n \<phi>) t,
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1)]"

lemma tpsL0: "tpsL 0 = tps1"
proof -
  have "nlltape' (formula_n \<phi>) 0 = tps1 ! j1"
    using tps0(1) tps1_def jk by simp
  moreover have "\<lfloor>sat_take 0\<rfloor>\<^sub>B = \<lfloor>1\<rfloor>\<^sub>N"
    using satisfies_def by simp
  ultimately show ?thesis
    using tpsL_def tps0 jk tps1_def by (metis list_update_id)
qed

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>formula_n \<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tmL1 [transforms_intros]:
  assumes "ttt = 12 + 2 * nllength (formula_n \<phi> ! t)" and "t < length (formula_n \<phi>)"
  shows "transforms tmL1 (tpsL t) ttt (tpsL1 t)"
  unfolding tmL1_def
proof (tform tps: assms tps0 tpsL_def tpsL1_def jk)
  show "ttt = 12 + 2 * nllength [] + 2 * nllength (formula_n \<phi> ! t)"
    using assms(1) by simp
  show "tpsL1 t = (tpsL t)
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 + 1 := (\<lfloor>formula_n \<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1)]"
    using tpsL1_def tpsL_def jk by (simp add: list_update_swap)
qed

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take t\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>formula_n \<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1),
     j3 + 2 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) (\<phi> ! t)\<rfloor>\<^sub>B, 1)]"

lemma tmL2 [transforms_intros]:
  assumes "ttt = 12 + 2 * nllength (formula_n \<phi> ! t) +
    (79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
     67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2 + 4)"
    and "t < length (formula_n \<phi>)"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def
proof (tform tps: assms tps0 tpsL_def tpsL1_def jk)
  let ?clause = "\<phi> ! t"
  have *: "formula_n \<phi> ! t = clause_n ?clause"
    using assms(2) formula_n_def by simp
  then have "(\<lfloor>formula_n \<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1) = nltape' (clause_n ?clause) 0"
    by simp
  then show "tpsL1 t ! (j3 + 1) = nltape' (clause_n ?clause) 0"
    using tpsL1_def jk by simp
  have "j3 + 2 + 1 = j3 + 3"
    by simp
  moreover have "tpsL1 t ! (j3 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def tps0 jk by simp
  ultimately show "tpsL1 t ! (j3 + 2 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by metis
  have "j3 + 2 + 2 = j3 + 4"
    by simp
  moreover have "tpsL1 t ! (j3 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def tps0 jk by simp
  ultimately show "tpsL1 t ! (j3 + 2 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by metis
  have "j3 + 2 + 3 = j3 + 5"
    by simp
  moreover have "tpsL1 t ! (j3 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def tps0 jk by simp
  ultimately show "tpsL1 t ! (j3 + 2 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by metis
  have "j3 + 2 + 4 = j3 + 6"
    by simp
  moreover have "tpsL1 t ! (j3 + 6) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def tps0 jk by simp
  ultimately show "tpsL1 t ! (j3 + 2 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by metis
  have "j3 + 2 + 5 = j3 + 7"
    by simp
  moreover have "tpsL1 t ! (j3 + 7) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsL1_def tps0 jk by simp
  ultimately show "tpsL1 t ! (j3 + 2 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    by metis
  show "tpsL2 t = (tpsL1 t)
      [j3 + 2 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) (\<phi> ! t)\<rfloor>\<^sub>B, 1)]"
    unfolding tpsL2_def tpsL1_def by simp
  show "ttt = 12 + 2 * nllength (formula_n \<phi> ! t) +
      (79 * (nllength (clause_n (\<phi> ! t)))\<^sup>2 +
       67 * nllength (clause_n (\<phi> ! t)) * (nllength vars)\<^sup>2 + 4)"
    using assms(1) * by simp
qed

definition tpsL3 :: "nat \<Rightarrow> tape list" where
  "tpsL3 t \<equiv> tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>formula_n \<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1),
     j3 + 2 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) (\<phi> ! t)\<rfloor>\<^sub>B, 1)]"

lemma tmI [transforms_intros]:
  assumes "ttt = 16" and "t < length (formula_n \<phi>)"
  shows "transforms tmI (tpsL2 t) ttt (tpsL3 t)"
  unfolding tmI_def
proof (tform tps: assms(2) tps0 tpsL2_def tpsL3_def jk time: assms(1))
  show "10 + 2 * nlength (if sat_take t then 1 else 0) + 2 * nlength 0 + 2 \<le> ttt"
    using assms(1) nlength_1_simp by simp

  let ?a = "\<lambda>v. v \<in> set vars"
  let ?cl = "\<phi> ! t"
  have *: "read (tpsL2 t) ! (j3 + 2) \<noteq> \<box> \<longleftrightarrow> satisfies_clause ?a ?cl"
    using tpsL2_def jk read_ncontents_eq_0[of "tpsL2 t" "j3 + 2"] by force

  have len: "t < length \<phi>"
    using assms(2) by (simp add: formula_n_def)
  have **: "sat_take (Suc t) \<longleftrightarrow> sat_take t \<and> satisfies_clause ?a ?cl"
    using satisfies_take[OF len] by simp

  show "tpsL3 t = (tpsL2 t)[j3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]" if "read (tpsL2 t) ! (j3 + 2) = \<box>"
  proof -
    have "(if sat_take (Suc t) then 1::nat else 0) = 0"
      using that * ** by simp
    then show ?thesis
      unfolding tpsL3_def tpsL2_def using that by (simp add: list_update_swap)
  qed
  show "tpsL3 t = (tpsL2 t)" if "read (tpsL2 t) ! (j3 + 2) \<noteq> \<box>"
  proof -
    have "sat_take t = sat_take (Suc t)"
      using * ** that by simp
    then show ?thesis
      unfolding tpsL3_def tpsL2_def using that by (simp add: list_update_swap)
  qed
qed

lemma tmL3 [transforms_intros]:
  assumes "ttt = 32 + 2 * nllength (formula_n \<phi> ! t) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2"
    and "t < length (formula_n \<phi>)"
  shows "transforms tmL3 (tpsL t) ttt (tpsL3 t)"
  unfolding tmL3_def by (tform tps: assms)

definition tpsL4 :: "nat \<Rightarrow> tape list" where
  "tpsL4 t \<equiv> tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
     j3 + 2 := (\<lfloor>satisfies_clause (\<lambda>v. v \<in> set vars) (\<phi> ! t)\<rfloor>\<^sub>B, 1)]"

lemma tmL4 [transforms_intros]:
  assumes "ttt = 39 + 4 * nllength (formula_n \<phi> ! t) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2"
    and "t < length (formula_n \<phi>)"
  shows "transforms tmL4 (tpsL t) ttt (tpsL4 t)"
  unfolding tmL4_def
proof (tform tps: assms(2) tps0 tpsL3_def tpsL4_def jk)
  let ?zs = "numlist (formula_n \<phi> ! t)"
  have *: "tpsL3 t ! (j3 + 1) = (\<lfloor>formula_n \<phi> ! t\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tpsL3_def jk by simp
  then show "tpsL3 t ::: (j3 + 1) = \<lfloor>?zs\<rfloor>"
    using nlcontents_def by simp
  show "proper_symbols ?zs"
    using proper_symbols_numlist by simp
  show "tpsL4 t = (tpsL3 t)[j3 + 1 := (\<lfloor>[]\<rfloor>, 1)]"
    unfolding tpsL4_def tpsL3_def using nlcontents_Nil by (simp add: list_update_swap)
  show "ttt = 32 + 2 * nllength (formula_n \<phi> ! t) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2 +
      (tpsL3 t :#: (j3 + 1) + 2 * length (numlist (formula_n \<phi> ! t)) + 6)"
    using * assms(1) nllength_def by simp
qed

definition tpsL5 :: "nat \<Rightarrow> tape list" where
  "tpsL5 t \<equiv> tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1),
     j3 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tmL5:
  assumes "ttt = 49 + 4 * nllength (formula_n \<phi> ! t) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2 +
      2 * nlength (if satisfies_clause (\<lambda>v. v \<in> set vars) (\<phi> ! t) then 1 else 0)"
    and "t < length (formula_n \<phi>)"
  shows "transforms tmL5 (tpsL t) ttt (tpsL5 t)"
  unfolding tmL5_def by (tform tps: assms tps0 tpsL4_def tpsL5_def jk)

definition tpsL5' :: "nat \<Rightarrow> tape list" where
  "tpsL5' t \<equiv> tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1)]"

lemma tpsL5': "tpsL5' = tpsL5"
proof
  fix t
  have 5: "j1 \<noteq> j3 + 1"
    using jk by simp
  have 4: "j3 \<noteq> j3 + 1"
    by simp
  have 1: "j3 \<noteq> j3 + 2"
    by simp
  have 2: "j3 + 1 \<noteq> j3 + 2"
    by simp
  have 22: "Suc j3 \<noteq> Suc (Suc j3)"
    by simp
  have 3: "j1 \<noteq> j3 + 2"
    using jk by simp
  let ?tps1 = "tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t)]"
  let ?tps2 = "tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1)]"
  have "tpsL5 t = tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)]"
    unfolding tpsL5_def
    using tps0(5)
      list_update_swap[OF 2, of ?tps2]
      list_update_swap[OF 1, of ?tps1]
      list_update_swap[OF 3, of tps0]
      list_update_id[of tps0 "j3 + 2"]
    by (simp only:)
  also have "... = tps0
    [j1 := nlltape' (formula_n \<phi>) (Suc t),
     j3 := (\<lfloor>sat_take (Suc t)\<rfloor>\<^sub>B, 1)]"
    using tps0(4)
      list_update_swap[OF 4, of ?tps1]
      list_update_swap[OF 5, of tps0]
      list_update_id[of tps0 "j3 + 1"]
    by (simp only:)
  finally show "tpsL5' t = tpsL5 t"
    using tpsL5'_def by simp
qed

lemma tmL5' [transforms_intros]:
  assumes "ttt = 51 + 83 * (nlllength (formula_n \<phi>))\<^sup>2 +
      67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2"
    and "t < length (formula_n \<phi>)"
  shows "transforms tmL5 (tpsL t) ttt (tpsL5' t)"
proof -
  let ?ttt = "49 + 4 * nllength (formula_n \<phi> ! t) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2 +
      2 * nlength (if satisfies_clause (\<lambda>v. v \<in> set vars) (\<phi> ! t) then 1 else 0)"
  have "?ttt \<le> 49 + 4 * nllength (formula_n \<phi> ! t) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2 +
      2 * nlength 1"
    by simp
  also have "... = 51 + 4 * nllength (formula_n \<phi> ! t) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2"
    using nlength_1_simp by simp
  also have "... \<le> 51 + 4 * nlllength (formula_n \<phi>) +
      79 * (nllength (formula_n \<phi> ! t))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2"
    using member_le_nlllength_1[of "formula_n \<phi> ! t" "formula_n \<phi>"] assms(2) by simp
  also have "... \<le> 51 + 4 * nlllength (formula_n \<phi>) +
      79 * (nlllength (formula_n \<phi>))\<^sup>2 +
      67 * nllength (formula_n \<phi> ! t) * (nllength vars)\<^sup>2"
    using member_le_nlllength_1[of "formula_n \<phi> ! t" "formula_n \<phi>"] assms(2) by simp
  also have "... \<le> 51 + 4 * nlllength (formula_n \<phi>) +
      79 * (nlllength (formula_n \<phi>))\<^sup>2 +
      67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2"
    using member_le_nlllength_1[of "formula_n \<phi> ! t" "formula_n \<phi>"] assms(2) by auto
  also have "... \<le> 51 + 83 * (nlllength (formula_n \<phi>))\<^sup>2 +
      67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2"
    using linear_le_pow by simp
  finally have "?ttt \<le> ttt"
    using assms(1) by simp
  then show ?thesis
    using tpsL5' transforms_monotone[OF tmL5] assms by simp
qed

lemma tmL [transforms_intros]:
  assumes "ttt = length (formula_n \<phi>) * (53 + 83 * (nlllength (formula_n \<phi>))\<^sup>2 + 67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length (formula_n \<phi>)))"
  unfolding tmL_def
proof (tform)
  let ?t = "51 + 83 * (nlllength (formula_n \<phi>))\<^sup>2 + 67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2"
  have "tpsL5' t = tpsL (Suc t)" for t
    using tpsL5'_def tpsL_def by simp
  then show "\<And>t. t < length (formula_n \<phi>) \<Longrightarrow> transforms tmL5 (tpsL t) ?t (tpsL (Suc t))"
    using tmL5' by simp

  let ?nss = "formula_n \<phi>"
  have *: "tpsL t ! j1 = nlltape' ?nss t" for t
    using tpsL_def jk by simp
  moreover have "read (tpsL t) ! j1 = tpsL t :.: j1" for t
    using tapes_at_read'[of j1 "tpsL t"] tpsL_def jk by simp
  ultimately have "read (tpsL t) ! j1 = |.| (nlltape' ?nss t)" for t
    by simp
  then have "read (tpsL t) ! j1 = \<box> \<longleftrightarrow> (t \<ge> length ?nss)" for t
    using nlltape'_tape_read by simp
  then show
      "\<And>i. i < length ?nss \<Longrightarrow> read (tpsL i) ! j1 \<noteq> \<box>"
      "\<not> read (tpsL (length ?nss)) ! j1 \<noteq> \<box>"
    using * by simp_all
  show "length (formula_n \<phi>) * (?t + 2) + 1 \<le> ttt"
    using assms by simp
qed

lemma tm2:
  assumes "ttt = length (formula_n \<phi>) * (53 + 83 * (nlllength (formula_n \<phi>))\<^sup>2 + 67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2) + 13"
  shows "transforms tm2 tps0 ttt (tpsL (length (formula_n \<phi>)))"
  unfolding tm2_def
proof (tform tps: assms tps0 tpsL4_def tpsL5_def jk tpsL0)
  show "transforms tm1 tps0 12 (tpsL 0)"
    using tm1 tpsL0 by simp
qed

definition tps2 :: "tape list" where
  "tps2 \<equiv> tps0
    [j1 := nlltape (formula_n \<phi>),
     j3 := (\<lfloor>(\<lambda>v. v \<in> set vars) \<Turnstile> \<phi>\<rfloor>\<^sub>B, 1)]"

lemma tps2: "tps2 = tpsL (length (formula_n \<phi>))"
  using formula_n_def tps2_def tpsL_def by simp

lemma tm2':
  assumes "ttt = length (formula_n \<phi>) * (53 + 83 * (nlllength (formula_n \<phi>))\<^sup>2 + 67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2) + 13"
  shows "transforms tm2 tps0 ttt tps2"
  using tm2 tps2 assms by simp

end  (* context *)

end  (* locale *)

lemma transforms_tm_sat_formulaI [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k :: nat and vars :: "nat list" and \<phi> :: formula
  assumes "0 < j1" "j1 \<noteq> j2" "j3 + 7 < k" "j1 < j3" "j2 < j3" "0 < j2" "length tps = k"
  assumes
    "tps ! j1 = nlltape' (formula_n \<phi>) 0"
    "tps ! j2 = nltape' vars 0"
    "tps ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 1) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 6) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 7) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "tps' = tps
    [j1 := nlltape (formula_n \<phi>),
     j3 := (\<lfloor>(\<lambda>v. v \<in> set vars) \<Turnstile> \<phi>\<rfloor>\<^sub>B, 1)]"
  assumes "ttt = length (formula_n \<phi>) * (53 + 83 * (nlllength (formula_n \<phi>))\<^sup>2 + 67 * nlllength (formula_n \<phi>) * (nllength vars)\<^sup>2) + 13"
  shows "transforms (tm_sat_formula j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_sat_formula j1 j2 j3 .
  show ?thesis
    using assms loc.tps2_def loc.tm2' loc.tm2_eq_tm_sat_formula by metis
qed


subsection \<open>A Turing machine for verifying \SAT{} instances\<close>

text \<open>
The previous Turing machine, @{const tm_sat_formula}, expects a well-formed
formula and a well-formed list representing an assignment on its tapes. The TM
we ultimately need, however, is not guaranteed to be given anything well-formed
as input and even the well-formed inputs require decoding from the binary
alphabet to the quaternary alphabet used for lists of lists of numbers. The next
TM takes care of all of that and, if everything was well-formed, runs @{const
tm_sat_formula}. If the first element of the pair input is invalid, it outputs
\textbf{1}, as required by the definition of \SAT{}.

Thus, the next Turing machine implements the function @{const verify_sat} and
therefore is a verifier for \SAT.
\<close>

definition tm_verify_sat :: machine where
  "tm_verify_sat \<equiv>
    tm_right_many {0..<22} ;;
    tm_bindecode 0 2 ;;
    tm_unpair 2 3 4 ;;
    tm_even_length 3 5 ;;
    tm_proper_symbols_lt 3 6 4 ;;
    tm_and 6 5 ;;
    IF \<lambda>rs. rs ! 6 \<noteq> \<box> THEN
      tm_bindecode 3 7 ;;
      tm_numlistlist_wf 7 8 ;;
      IF \<lambda>rs. rs ! 8 \<noteq> \<box> THEN
        tm_proper_symbols_lt 4 10 4 ;;
        IF \<lambda>rs. rs ! 10 \<noteq> \<box> THEN
          tm_bindecode 4 11 ;;
          tm_rstrip \<sharp> 11 ;;
          tm_numlist_wf 11 12 ;;
          IF \<lambda>rs. rs ! 12 \<noteq> \<box> THEN
            tm_sat_formula 7 11 14 ;;
            tm_copyn 14 1
          ELSE
            []
          ENDIF
        ELSE
          []
        ENDIF
      ELSE
        tm_setn 1 1
      ENDIF
    ELSE
      tm_setn 1 1
    ENDIF"

lemma tm_verify_sat_tm: "turing_machine 22 6 tm_verify_sat"
  unfolding tm_verify_sat_def
  using tm_copyn_tm tm_setn_tm turing_machine_branch_turing_machine tm_sat_formula_tm tm_bindecode_tm
    tm_rstrip_tm tm_numlist_wf_tm tm_proper_symbols_lt_tm tm_numlistlist_wf_tm Nil_tm
    tm_right_many_tm tm_unpair_tm tm_even_length_tm tm_and_tm
  by simp

locale turing_machine_verify_sat
begin

definition "tm1 \<equiv> tm_right_many {0..<22}"
definition "tm2 \<equiv> tm1 ;; tm_bindecode 0 2"
definition "tm3 \<equiv> tm2 ;; tm_unpair 2 3 4"
definition "tm4 \<equiv> tm3 ;; tm_even_length 3 5"
definition "tm5 \<equiv> tm4 ;; tm_proper_symbols_lt 3 6 4"
definition "tm6 \<equiv> tm5 ;; tm_and 6 5"

definition "tmTTT1 \<equiv> tm_bindecode 4 11"
definition "tmTTT2 \<equiv> tmTTT1 ;; tm_rstrip \<sharp> 11"
definition "tmTTT3 \<equiv> tmTTT2 ;; tm_numlist_wf 11 12"

definition "tmTTTT1 \<equiv> tm_sat_formula 7 11 14"
definition "tmTTTT2 \<equiv> tmTTTT1 ;; tm_copyn 14 1"
definition "tmTTTI \<equiv> IF \<lambda>rs. rs ! 12 \<noteq> \<box> THEN tmTTTT2 ELSE [] ENDIF"

definition "tmTTT \<equiv> tmTTT3 ;; tmTTTI"
definition "tmTTI \<equiv> IF \<lambda>rs. rs ! 10 \<noteq> \<box> THEN tmTTT ELSE [] ENDIF"

definition "tmTT1 \<equiv> tm_proper_symbols_lt 4 10 4"
definition "tmTT \<equiv> tmTT1 ;; tmTTI"
definition "tmTI \<equiv> IF \<lambda>rs. rs ! 8 \<noteq> \<box> THEN tmTT ELSE tm_setn 1 1 ENDIF"

definition "tmT1 \<equiv> tm_bindecode 3 7"
definition "tmT2 \<equiv> tmT1 ;; tm_numlistlist_wf 7 8"
definition "tmT \<equiv> tmT2 ;; tmTI"

definition "tmI \<equiv> IF \<lambda>rs. rs ! 6 \<noteq> \<box> THEN tmT ELSE tm_setn 1 1 ENDIF"
definition "tm7 \<equiv> tm6 ;; tmI"

lemma tm7_eq_tm_verify_sat: "tm7 = tm_verify_sat"
  unfolding tm_verify_sat_def tm7_def tmI_def tmT_def tmT2_def tmTI_def tmT1_def tmTT_def tmTT1_def tmTTI_def
    tmTTT_def tmTTT3_def tmTTTT1_def tmTTTI_def tmTTTT2_def tmTTT3_def tmTTT2_def tmTTT1_def tm6_def tm5_def
    tm4_def tm3_def tm2_def tm1_def
  by simp

context
  fixes tps0 :: "tape list" and zs :: "symbol list"
  assumes zs: "bit_symbols zs"
  assumes tps0: "tps0 = snd (start_config 22 zs)"
begin

definition "tps1 \<equiv> map (\<lambda>tp. tp |#=| 1) tps0"

lemma map_upt_length: "map f xs = map (\<lambda>i. f (xs ! i)) [0..<length xs]"
  by (smt (verit, ccfv_SIG) in_set_conv_nth length_map map_eq_conv map_nth nth_map)

lemma tps1:
  "tps1 ! 0 = (\<lfloor>zs\<rfloor>, 1)"
  "0 < j \<Longrightarrow> j < 22 \<Longrightarrow> tps1 ! j = (\<lfloor>[]\<rfloor>, 1)"
  "length tps1 = 22"
  using tps0 start_config_def tps1_def by auto

lemma tm1 [transforms_intros]: "transforms tm1 tps0 1 tps1"
  unfolding tm1_def
proof (tform tps: tps0 tps1_def)
  have "length tps0 = 22"
    using tps0 start_config_def by simp
  then have "map (\<lambda>j. if j \<in> {0..<22} then tps0 ! j |+| 1 else tps0 ! j) [0..<length tps0] =
      map (\<lambda>j. tps0 ! j |+| 1) [0..<length tps0]"
    by simp
  also have "... = map (\<lambda>j. tps0 ! j |#=| 1) [0..<length tps0]"
    using tps0 \<open>length tps0 = 22\<close> start_config_pos by simp
  also have "... = map (\<lambda>tp. tp |#=| 1) tps0"
    using map_upt_length[of "\<lambda>tp. tp |#=| 1" tps0] by simp
  also have "... = tps1"
    using tps1_def by simp
  finally show "tps1 = map (\<lambda>j. if j \<in> {0..<22} then tps0 ! j |+| 1 else tps0 ! j) [0..<length tps0]"
    by simp
qed

definition "tps2 \<equiv> tps1
  [2 := (\<lfloor>bindecode zs\<rfloor>, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 8 + 3 * length zs"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: assms zs tps1 tps2_def)

definition "tps3 \<equiv> tps1
  [2 := (\<lfloor>bindecode zs\<rfloor>, 1),
   3 := (\<lfloor>first (bindecode zs)\<rfloor>, 1),
   4 := (\<lfloor>second (bindecode zs)\<rfloor>, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 21 + 3 * length zs + 6 * length (bindecode zs)"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: assms zs tps2_def tps1 tps3_def)
  show "proper_symbols (bindecode zs)"
    using zs proper_bindecode by simp
  show "ttt = 8 + 3 * length zs + (6 * length (bindecode zs) + 13)"
    using assms by simp
qed

definition "tps4 \<equiv> tps1
  [2 := (\<lfloor>bindecode zs\<rfloor>, 1),
   3 := (\<lfloor>first (bindecode zs)\<rfloor>, 1),
   4 := (\<lfloor>second (bindecode zs)\<rfloor>, 1),
   5 := (\<lfloor>even (length (first (bindecode zs)))\<rfloor>\<^sub>B, 1)]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 28 + 3 * length zs + 6 * length (bindecode zs) + 7 * length (first (bindecode zs))"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: assms zs tps1 tps3_def tps4_def)
  show "proper_symbols (first (bindecode zs))"
    using zs proper_bindecode first_def by simp
  show "tps3 ! 5 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps3_def canrepr_0 tps1 by simp
qed

definition "tps5 \<equiv> tps1
  [2 := (\<lfloor>bindecode zs\<rfloor>, 1),
   3 := (\<lfloor>first (bindecode zs)\<rfloor>, 1),
   4 := (\<lfloor>second (bindecode zs)\<rfloor>, 1),
   5 := (\<lfloor>even (length (first (bindecode zs)))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first (bindecode zs))\<rfloor>\<^sub>B, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 33 + 3 * length zs + 6 * length (bindecode zs) + 14 * length (first (bindecode zs))"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: assms zs tps1 tps4_def tps5_def)
  show "proper_symbols (first (bindecode zs))"
    using zs proper_bindecode first_def by simp
qed

abbreviation "ys \<equiv> bindecode zs"
abbreviation "xs \<equiv> bindecode (first ys)"
abbreviation "vs \<equiv> rstrip 5 (bindecode (second ys))"

definition "tps6 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1)]"

lemma tm6 [transforms_intros]:
  assumes "ttt = 36 + 3 * length zs + 6 * length (bindecode zs) + 14 * length (first (bindecode zs))"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def by (tform tps: assms zs tps1 tps5_def tps6_def)

context
  assumes bs_even: "proper_symbols_lt 4 (first ys) \<and> even (length (first ys))"
begin

lemma bs: "bit_symbols (first ys)"
    using bs_even by fastforce

definition "tpsT1 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>bindecode (first ys)\<rfloor>, 1)]"

lemma tmT1 [transforms_intros]:
  assumes "ttt = 7 + 3 * length (first ys)"
  shows "transforms tmT1 tps6 ttt tpsT1"
  unfolding tmT1_def by (tform tps: assms bs tps1 tps6_def tpsT1_def)

definition "tpsT2 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>bindecode (first ys)\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf (bindecode (first ys))\<rfloor>\<^sub>B, 1)]"

lemma tmT2 [transforms_intros]:
  assumes "ttt = 213 + 3 * length (first ys) + 39 * length (bindecode (first ys))"
  shows "transforms tmT2 tps6 ttt tpsT2"
  unfolding tmT2_def
proof (tform tps: assms tps1 tpsT1_def tpsT2_def)
  show "proper_symbols (bindecode (first ys))"
    using proper_bindecode by simp
  show "ttt = 7 + 3 * length (first ys) + (206 + 39 * length (bindecode (first ys)))"
    using assms by simp
qed

context
  assumes first_wf: "numlistlist_wf (bindecode (first ys))"
begin

definition "tpsTT1 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>bindecode (first ys)\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf (bindecode (first ys))\<rfloor>\<^sub>B, 1),
   10 := (\<lfloor>proper_symbols_lt 4 (second ys)\<rfloor>\<^sub>B, 1)]"

lemma tmTT1 [transforms_intros]:
  assumes "ttt = 5 + 7 * length (second ys)"
  shows "transforms tmTT1 tpsT2 ttt tpsTT1"
  unfolding tmTT1_def
proof (tform tps: tps1 tpsT2_def tpsTT1_def assms)
  show "proper_symbols (second ys)"
    using proper_bindecode second_def zs by simp
qed

context
  assumes proper_second: "proper_symbols_lt 4 (second ys)"
begin

definition "tpsTTT1 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>xs\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf xs\<rfloor>\<^sub>B, 1),
   10 := (\<lfloor>proper_symbols_lt 4 (second ys)\<rfloor>\<^sub>B, 1),
   11 := (\<lfloor>bindecode (second ys)\<rfloor>, 1)]"

lemma tmTTT1 [transforms_intros]:
  assumes "ttt = 7 + 3 * length (second ys)"
  shows "transforms tmTTT1 tpsTT1 ttt tpsTTT1"
  unfolding tmTTT1_def
proof (tform tps: assms tps1 tpsT2_def tpsTT1_def tpsTTT1_def)
  show "bit_symbols (second ys)"
    using proper_second by fastforce
qed

definition "tpsTTT2 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>xs\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf xs\<rfloor>\<^sub>B, 1),
   10 := (\<lfloor>proper_symbols_lt 4 (second ys)\<rfloor>\<^sub>B, 1),
   11 := (\<lfloor>vs\<rfloor>, 1)]"

lemma tmTTT2 [transforms_intros]:
  assumes "ttt = 12 + 3 * length (second ys) + 3 * length (bindecode (second ys))"
  shows "transforms tmTTT2 tpsTT1 ttt tpsTTT2"
  unfolding tmTTT2_def
proof (tform tps: assms tps1 tpsTTT1_def tpsTTT2_def)
  show "proper_symbols (bindecode (second ys))"
    using proper_bindecode by simp
  show "ttt = 7 + 3 * length (second ys) + (3 * length (bindecode (second ys)) + 5)"
    using assms by simp
qed

definition "tpsTTT3 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>xs\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf xs\<rfloor>\<^sub>B, 1),
   10 := (\<lfloor>proper_symbols_lt 4 (second ys)\<rfloor>\<^sub>B, 1),
   11 := (\<lfloor>vs\<rfloor>, 1),
   12 := (\<lfloor>numlist_wf vs\<rfloor>\<^sub>B, 1)]"

lemma tmTTT3 [transforms_intros]:
  assumes "ttt = 106 + 3 * length (second ys) + 3 * length (bindecode (second ys)) + 19 * length vs"
  shows "transforms tmTTT3 tpsTT1 ttt tpsTTT3"
  unfolding tmTTT3_def
proof (tform tps: assms tps1 tpsTTT2_def tpsTTT3_def)
  show "proper_symbols vs"
    using proper_bindecode rstrip_def by simp
qed

context
  assumes second_wf: "numlist_wf vs"
begin

definition "tpsTTTT1 \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>xs\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf xs\<rfloor>\<^sub>B, 1),
   10 := (\<lfloor>proper_symbols_lt 4 (second ys)\<rfloor>\<^sub>B, 1),
   11 := (\<lfloor>vs\<rfloor>, 1),
   12 := (\<lfloor>numlist_wf vs\<rfloor>\<^sub>B, 1),
   7 := nlltape (formula_n (zs_formula xs)),
   14 := (\<lfloor>(\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs\<rfloor>\<^sub>B, 1)]"

lemma tmTTTT1 [transforms_intros]:
  assumes "ttt = length (formula_n (zs_formula xs)) *
    (53 + 83 * (nlllength (formula_n (zs_formula xs)))\<^sup>2 + 67 * nlllength (formula_n (zs_formula xs)) * (nllength (zs_numlist vs))\<^sup>2) +
    13"
  shows "transforms tmTTTT1 tpsTTT3 ttt tpsTTTT1"
  unfolding tmTTTT1_def
proof (tform time: assms)
  show
    "tpsTTT3 ! 14 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tpsTTT3 ! (14 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tpsTTT3 ! (14 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tpsTTT3 ! (14 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tpsTTT3 ! (14 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tpsTTT3 ! (14 + 6) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tpsTTT3 ! (14 + 7) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    unfolding tpsTTT3_def using tps1 canrepr_0 by auto
  show "tpsTTT3 ! (14 + 1) = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    unfolding tpsTTT3_def using tps1 nlcontents_Nil by simp
  show "14 + 7 < length tpsTTT3"
    unfolding tpsTTT3_def using tps1 by simp
  let ?phi = "zs_formula xs"
  have "numlistlist (formula_n ?phi) = xs"
    using formula_zs_def formula_zs_formula first_wf by simp
  then have "nlltape' (formula_n ?phi) 0 = (\<lfloor>xs\<rfloor>, 1)"
    by (simp add: nllcontents_def)
  then show "tpsTTT3 ! 7 = nlltape' (formula_n ?phi) 0"
    unfolding tpsTTT3_def using tps1 by simp
  let ?vars = "zs_numlist vs"
  have "numlist ?vars = vs"
    using numlist_zs_numlist second_wf by simp
  then have "nltape' ?vars 0 = (\<lfloor>vs\<rfloor>, 1)"
    by (simp add: nlcontents_def)
  then show "tpsTTT3 ! 11 = nltape' ?vars 0"
    unfolding tpsTTT3_def using tps1 by simp
  show "tpsTTTT1 = tpsTTT3
    [7 := nlltape (formula_n (zs_formula xs)),
     14 := (\<lfloor>(\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs\<rfloor>\<^sub>B, 1)]"
    unfolding tpsTTTT1_def tpsTTT3_def by fast
qed

definition "tpsTTTT2 \<equiv> tps1
  [1 := (\<lfloor>(\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs\<rfloor>\<^sub>B, 1),
   2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>xs\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf xs\<rfloor>\<^sub>B, 1),
   10 := (\<lfloor>proper_symbols_lt 4 (second ys)\<rfloor>\<^sub>B, 1),
   11 := (\<lfloor>vs\<rfloor>, 1),
   12 := (\<lfloor>numlist_wf vs\<rfloor>\<^sub>B, 1),
   7 := nlltape (formula_n (zs_formula xs)),
   14 := (\<lfloor>(\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs\<rfloor>\<^sub>B, 1)]"

lemma tmTTTT2:
  assumes "ttt = length (formula_n (zs_formula xs)) *
    (53 + 83 * (nlllength (formula_n (zs_formula xs)))\<^sup>2 + 67 * nlllength (formula_n (zs_formula xs)) * (nllength (zs_numlist vs))\<^sup>2) +
    27 + 3 * (nlength (if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then 1 else 0))"
  shows "transforms tmTTTT2 tpsTTT3 ttt tpsTTTT2"
  unfolding tmTTTT2_def
proof (tform)
  show "14 < length tpsTTTT1" "1 < length tpsTTTT1"
    unfolding tpsTTTT1_def using tps1 by simp_all
  show "tpsTTTT1 ! 1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    unfolding tpsTTTT1_def using tps1 canrepr_0 by auto
  let ?b = "if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then 1 else 0 :: nat"
  show "tpsTTTT1 ! 14 = (\<lfloor>?b\<rfloor>\<^sub>N, 1)"
    unfolding tpsTTTT1_def using tps1 by simp
  show "ttt = length (formula_n (zs_formula xs)) *
      (53 + 83 * (nlllength (formula_n (zs_formula xs)))\<^sup>2 +
       67 * nlllength (formula_n (zs_formula xs)) * (nllength (zs_numlist vs))\<^sup>2) +
      13 + (14 + 3 *
      (nlength (if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then 1 else 0) + nlength 0))"
    using assms by simp
  show "tpsTTTT2 = tpsTTTT1
      [1 := (\<lfloor>(\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs\<rfloor>\<^sub>B, 1)]"
    unfolding tpsTTTT2_def tpsTTTT1_def by (simp add: list_update_swap)
qed

lemma tmTTTT2' [transforms_intros]:
  assumes "ttt = 203 * length zs ^ 4 + 30"
  shows "transforms tmTTTT2 tpsTTT3 ttt tpsTTTT2"
proof -
  let ?phi = "zs_formula xs"
  let ?ttt = "length (formula_n ?phi) *
    (53 + 83 * (nlllength (formula_n ?phi))\<^sup>2 + 67 * nlllength (formula_n ?phi) * (nllength (zs_numlist vs))\<^sup>2) +
    27 + 3 * (nlength (if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> ?phi then 1 else 0))"
  have "nlllength (formula_n ?phi) \<le> length xs"
    using formula_zs_def formula_zs_formula first_wf nlllength_def by simp
  then have 1: "nlllength (formula_n ?phi) \<le> length zs"
    by (metis div_le_dividend le_trans length_bindecode length_first)
  moreover have "length (formula_n ?phi) \<le> nlllength (formula_n ?phi)"
    by (simp add: length_le_nlllength)
  ultimately have 2: "length (formula_n ?phi) \<le> length zs"
    by simp
  have "nllength (zs_numlist vs) \<le> length vs"
    using second_wf numlist_zs_numlist nllength_def by simp
  moreover have "length vs \<le> length zs"
    using second_def length_bindecode length_rstrip_le by (metis div_le_dividend dual_order.trans length_second)
  ultimately have 3: "nllength (zs_numlist vs) \<le> length zs"
    by simp
  have 4: "nlength (if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> ?phi then 1 else 0) \<le> 1"
    using nlength_1_simp by simp

  have "?ttt \<le> length (formula_n ?phi) *
      (53 + 83 * (nlllength (formula_n ?phi))\<^sup>2 + 67 * nlllength (formula_n ?phi) * (nllength (zs_numlist vs))\<^sup>2) + 30"
    using 4 by simp
  also have "... \<le> length zs *
      (53 + 83 * (nlllength (formula_n ?phi))\<^sup>2 + 67 * nlllength (formula_n ?phi) * (nllength (zs_numlist vs))\<^sup>2) + 30"
    using 2 by simp
  also have "... \<le> length zs * (53 + 83 * (length zs)\<^sup>2 + 67 * length zs * (nllength (zs_numlist vs))\<^sup>2) + 30"
    using 1 by (simp add: add_mono)
  also have "... \<le> length zs * (53 + 83 * (length zs)\<^sup>2 + 67 * length zs * (length zs)\<^sup>2) + 30"
    using 3 by simp
  also have "... = 53 * length zs + 83 * length zs ^ 3 + 67 * length zs ^ 4 + 30"
    by algebra
  also have "... \<le> 53 * length zs + 83 * length zs ^ 4 + 67 * length zs ^ 4 + 30"
    using pow_mono' by simp
  also have "... \<le> 53 * length zs ^ 4 + 83 * length zs ^ 4 + 67 * length zs ^ 4 + 30"
    using linear_le_pow by simp
  also have "... = 203 * length zs ^ 4 + 30"
    by simp
  finally have "?ttt \<le> 203 * length zs ^ 4 + 30" .
  then show ?thesis
    using assms tmTTTT2 transforms_monotone by simp
qed

end  (* context second_wf: "numlist_wf vs" *)

definition "tpsTTT \<equiv> (if numlist_wf vs then tpsTTTT2 else tpsTTT3)"

lemma length_tpsTTT: "length tpsTTT = 22"
  using tpsTTT_def tpsTTTT2_def tpsTTT3_def tps1 by (metis (no_types, lifting) length_list_update)

lemma tpsTTT: "tpsTTT ! 1 =
  (\<lfloor>if numlist_wf vs then (if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then 1 else 0) else 0\<rfloor>\<^sub>N, 1)"
proof (cases "numlist_wf vs")
  case True
  then have "tpsTTT ! 1 = tpsTTTT2 ! 1"
    using tpsTTT_def by simp
  also have "... = (\<lfloor>(\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs\<rfloor>\<^sub>B, 1)"
    unfolding tpsTTTT2_def[OF True] using tps1 by simp
  finally show ?thesis
    using True by simp
next
  case False
  then have "tpsTTT ! 1 = tpsTTT3 ! 1"
    using tpsTTT_def by simp
  also have "... = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    unfolding tpsTTT3_def using tps1 canrepr_0 by simp
  finally show ?thesis
    using False by simp
qed

lemma tmTTTI [transforms_intros]:
  assumes "ttt = 203 * length zs ^ 4 + 32"
  shows "transforms tmTTTI tpsTTT3 ttt tpsTTT"
  unfolding tmTTTI_def
proof (tform time: assms)
  have *: "read tpsTTT3 ! 12 \<noteq> \<box> \<longleftrightarrow> numlist_wf vs"
    using tpsTTT3_def tps1 read_ncontents_eq_0 by simp
  show "read tpsTTT3 ! 12 \<noteq> \<box> \<Longrightarrow> numlist_wf vs"
    using * by simp
  show "read tpsTTT3 ! 12 \<noteq> \<box> \<Longrightarrow> tpsTTT = tpsTTTT2"
    using * tpsTTT_def by simp
  show "\<not> read tpsTTT3 ! 12 \<noteq> \<box> \<Longrightarrow> tpsTTT = tpsTTT3"
    using * tpsTTT_def by simp
qed

lemma tmTTT:
  assumes "ttt = 138 + 3 * length (second ys) + 3 * length (bindecode (second ys)) +
      19 * length vs + 203 * length zs ^ 4"
  shows "transforms tmTTT tpsTT1 ttt tpsTTT"
  unfolding tmTTT_def by (tform tps: assms)

lemma tmTTT' [transforms_intros]:
  assumes "ttt = 138 + 228 * length zs ^ 4"
  shows "transforms tmTTT tpsTT1 ttt tpsTTT"
proof -
  let ?ttt = "138 + 3 * length (second ys) + 3 * length (bindecode (second ys)) +
     19 * length vs + 203 * length zs ^ 4"
  have "length ys \<le> length zs"
    by simp
  then have 1: "length (second ys) \<le> length zs"
    using length_second dual_order.trans by blast
  then have 2: "length (bindecode (second ys)) \<le> length zs"
    by simp
  then have 3: "length vs \<le> length zs"
    by (meson dual_order.trans length_rstrip_le)

  have "?ttt \<le> 138 + 3 * length zs + 3 * length zs + 19 * length zs + 203 * length zs ^ 4"
    using 1 2 3 by simp
  also have "... = 138 + 25 * length zs + 203 * length zs ^ 4"
    by simp
  also have "... \<le> 138 + 25 * length zs ^ 4 + 203 * length zs ^ 4"
    using linear_le_pow by simp
  also have "... = 138 + 228 * length zs ^ 4"
    by simp
  finally have "?ttt \<le> 138 + 228 * length zs ^ 4" .
  then show ?thesis
    using assms tmTTT transforms_monotone by blast
qed

end  (* context proper_second: "proper_symbols_lt 4 (second ys)" *)

definition "tpsTT \<equiv> (if proper_symbols_lt 4 (second ys) then tpsTTT else tpsTT1)"

lemma length_tpsTT: "length tpsTT = 22"
  using tpsTT_def length_tpsTTT tpsTT1_def tps1 by simp

lemma tpsTT: "tpsTT ! 1 =
  (ncontents
    (if proper_symbols_lt 4 (second ys) \<and> numlist_wf vs
     then if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then 1 else 0
     else 0),
   1)"
proof (cases "proper_symbols_lt 4 (second ys)")
  case True
  then have "tpsTT ! 1 = tpsTTT ! 1"
    using tpsTT_def by simp
  then show ?thesis
    using tpsTTT True by simp
next
  case False
  then have "tpsTT ! 1 = tpsTT1 ! 1"
    using tpsTT_def by auto
  then show ?thesis
    using tpsTT1_def tps1 canrepr_0 False by auto
qed

lemma tmTTI [transforms_intros]:
  assumes "ttt = 140 + 228 * length zs ^ 4"
  shows "transforms tmTTI tpsTT1 ttt tpsTT"
  unfolding tmTTI_def
proof (tform time: assms)
  have *: "read tpsTT1 ! 10 \<noteq> \<box> \<longleftrightarrow> proper_symbols_lt 4 (second ys)"
    using tpsTT1_def tps1 read_ncontents_eq_0 by simp
  show "read tpsTT1 ! 10 \<noteq> \<box> \<Longrightarrow> proper_symbols_lt 4 (second ys)"
    using * by simp
  let ?t = "138 + 228 * length zs ^ 4"
  show "read tpsTT1 ! 10 \<noteq> \<box> \<Longrightarrow> tpsTT = tpsTTT"
    using * tpsTT_def by simp
  show "\<not> read tpsTT1 ! 10 \<noteq> \<box> \<Longrightarrow> tpsTT = tpsTT1"
    using * tpsTT_def by auto
qed

lemma tmTT [transforms_intros]:
  assumes "ttt = 145 + 7 * length (second ys) + 228 * length zs ^ 4"
  shows "transforms tmTT tpsT2 ttt tpsTT"
  unfolding tmTT_def by (tform time: assms)

end  (* context first_wf: "numlistlist_wf (bindecode (first ys))" *)

definition "tpsTE \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   7 := (\<lfloor>bindecode (first ys)\<rfloor>, 1),
   8 := (\<lfloor>numlistlist_wf xs\<rfloor>\<^sub>B, 1),
   1 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

definition "tpsT \<equiv> (if numlistlist_wf xs then tpsTT else tpsTE)"

lemma length_tpsT: "length tpsT = 22"
  using tpsT_def length_tpsTT tpsTE_def tps1 by simp

lemma tpsT: "tpsT ! 1 =
  (ncontents
   (if numlistlist_wf xs
    then if proper_symbols_lt 4 (second ys) \<and> numlist_wf vs
         then if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then 1 else 0
         else 0
    else 1),
   1)"
proof (cases "numlistlist_wf xs")
  case True
  then have "tpsT ! 1 = tpsTT ! 1"
    using tpsT_def by simp
  then show ?thesis
    using tpsTT True by simp
next
  case False
  then have "tpsT ! 1 = tpsTE ! 1"
    using tpsT_def by auto
  then show ?thesis
    using tpsTE_def tps1 canrepr_0 False by auto
qed

lemma tmTI [transforms_intros]:
  assumes "ttt = 147 + 7 * length (second ys) + 228 * length zs ^ 4"
  shows "transforms tmTI tpsT2 ttt tpsT"
  unfolding tmTI_def
proof (tform time: assms)
  have *: "read tpsT2 ! 8 \<noteq> \<box> \<longleftrightarrow> numlistlist_wf xs"
    using tpsT2_def tps1 read_ncontents_eq_0 by simp
  show "read tpsT2 ! 8 \<noteq> \<box> \<Longrightarrow> numlistlist_wf xs"
    using * by simp
  show "1 < length tpsT2"
    using tpsT2_def tps1 by simp
  show "tpsT2 ! 1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tpsT2_def tps1 canrepr_0 by simp
  show "\<not> read tpsT2 ! 8 \<noteq> \<box> \<Longrightarrow> tpsT = tpsT2[1 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    using tpsT_def * tpsT2_def tpsTE_def by presburger
  show "read tpsT2 ! 8 \<noteq> \<box> \<Longrightarrow> tpsT = tpsTT"
    using * tpsT_def by simp
  show "10 + 2 * nlength 0 + 2 * nlength 1 + 1 \<le> ttt"
    using assms nlength_1_simp by simp
qed

lemma tmT [transforms_intros]:
  assumes "ttt = 360 + 3 * length (first ys) + 39 * length xs + 7 * length (second ys) + 228 * length zs ^ 4"
  shows "transforms tmT tps6 ttt tpsT"
  unfolding tmT_def by (tform time: assms)

end  (* context bs_even: "proper_symbols_lt 4 (first ys) \<and> even (length (first ys))" *)

definition "tpsE \<equiv> tps1
  [2 := (\<lfloor>ys\<rfloor>, 1),
   3 := (\<lfloor>first ys\<rfloor>, 1),
   4 := (\<lfloor>second ys\<rfloor>, 1),
   5 := (\<lfloor>even (length (first ys))\<rfloor>\<^sub>B, 1),
   6 := (\<lfloor>proper_symbols_lt 4 (first ys) \<and> even (length (first ys))\<rfloor>\<^sub>B, 1),
   1 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"

definition "tps7 \<equiv> (if proper_symbols_lt 4 (first ys) \<and> even (length (first ys)) then tpsT else tpsE)"

lemma length_tps7: "length tps7 = 22"
  using tps7_def length_tpsT tpsE_def tps1 by simp

lemma tps7: "tps7 ! 1 =
  (ncontents
   (if proper_symbols_lt 4 (first ys) \<and> even (length (first ys)) \<and> numlistlist_wf xs
    then if proper_symbols_lt 4 (second ys) \<and> numlist_wf vs
         then if (\<lambda>v. v \<in> set (zs_numlist vs)) \<Turnstile> zs_formula xs then 1 else 0
         else 0
    else 1),
   1)"
proof (cases "proper_symbols_lt 4 (first ys) \<and> even (length (first ys))")
  case True
  then have "tps7 ! 1 = tpsT ! 1"
    using tps7_def by simp
  then show ?thesis
    using tpsT True by simp
next
  case False
  then have "tps7 ! 1 = tpsE ! 1"
    using tps7_def by auto
  then show ?thesis
    using tpsE_def tps1 canrepr_0 False by auto
qed

lemma tps7': "tps7 ! 1 = (\<lfloor>verify_sat zs\<rfloor>, 1)"
proof -
  have "proper_symbols_lt 4 zs = bit_symbols zs" for zs
    by fastforce
  then show ?thesis
    unfolding verify_sat_def Let_def using tps7 canrepr_0 canrepr_1 by auto
qed

lemma tmI [transforms_intros]:
  assumes "ttt = 362 + 3 * length (first ys) + 39 * length xs + 7 * length (second ys) + 228 * length zs ^ 4"
  shows "transforms tmI tps6 ttt tps7"
  unfolding tmI_def
proof (tform time: assms)
  have *: "read tps6 ! 6 \<noteq> \<box> \<longleftrightarrow> (proper_symbols_lt 4 (first ys)) \<and> even (length (first ys))"
    using tps6_def tps1 read_ncontents_eq_0 by simp
  show "read tps6 ! 6 \<noteq> \<box> \<Longrightarrow> (proper_symbols_lt 4 (first ys)) \<and> even (length (first ys))"
    using * by simp
  show "1 < length tps6"
    using tps6_def tps1 by simp
  show "tps6 ! 1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    using tps6_def tps1 canrepr_0 by simp
  show "\<not> read tps6 ! 6 \<noteq> \<box> \<Longrightarrow> tps7 = tps6[1 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]"
    using tps7_def * tps6_def tpsE_def by metis
  show "read tps6 ! 6 \<noteq> \<box> \<Longrightarrow> tps7 = tpsT"
    using tps7_def * by simp
  show "10 + 2 * nlength 0 + 2 * nlength 1 + 1 \<le> ttt"
    using assms nlength_1_simp by simp
qed

lemma tm7:
  assumes "ttt = 398 + 3 * length zs + 6 * length ys + 17 * length (first ys) +
     39 * length xs + 7 * length (second ys) + 228 * length zs ^ 4"
  shows "transforms tm7 tps0 ttt tps7"
  unfolding tm7_def by (tform time: assms)

lemma tm7' [transforms_intros]:
  assumes "ttt = 398 + 300 * length zs ^ 4"
  shows "transforms tm7 tps0 ttt tps7"
proof -
  have *: "length ys \<le> length zs"
    by simp
  then have 1: "length (second ys) \<le> length zs"
    using length_second dual_order.trans by blast
  have 2: "length (first ys) \<le> length zs"
    using * dual_order.trans length_first by blast
  then have 3: "length xs \<le> length zs"
    by simp
  let ?ttt = "398 + 3 * length zs + 6 * length ys + 17 * length (first ys) +
     39 * length xs + 7 * length (second ys) + 228 * length zs ^ 4"
  have "?ttt \<le> 398 + 9 * length zs + 17 * length zs + 39 * length zs + 7 * length zs + 228 * length zs ^ 4"
    using * 1 2 3 by simp
  also have "... = 398 + 72 * length zs + 228 * length zs ^ 4"
    by simp
  also have "... \<le> 398 + 72 * length zs ^ 4 + 228 * length zs ^ 4"
    using linear_le_pow by simp
  also have "... = 398 + 300 * length zs ^ 4"
    by simp
  finally have "?ttt \<le> 398 + 300 * length zs ^ 4" .
  then show ?thesis
    using assms tm7 transforms_monotone by fast
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_verify_sat:
  fixes zs :: "symbol list" and tps :: "tape list"
  assumes "bit_symbols zs"
    and "tps = snd (start_config 22 zs)"
    and "ttt = 398 + 300 * length zs ^ 4"
  shows "\<exists>tps'. tps' ! 1 = (\<lfloor>verify_sat zs\<rfloor>, 1) \<and> transforms tm_verify_sat tps ttt tps'"
proof -
  interpret loc: turing_machine_verify_sat .
  show ?thesis
    using assms loc.tm7' loc.tps7' loc.tm7_eq_tm_verify_sat by metis
qed

text \<open>
With the Turing machine just constructed and the polynomial $p(n) = n$ we can
satisfy the definition of $\NP$ and prove the main result of this chapter.
\<close>

theorem SAT_in_NP: "SAT \<in> \<N>\<P>"
proof -
  define p :: "nat \<Rightarrow> nat" where "p = (\<lambda>n. n)"
  define T :: "nat \<Rightarrow> nat" where "T = (\<lambda>n. 398 + 300 * n ^ 4)"
  define f :: "string \<Rightarrow> string" where
    "f = (\<lambda>x. symbols_to_string (verify_sat (string_to_symbols x)))"
  have "turing_machine 22 6 tm_verify_sat"
    using tm_verify_sat_tm .
  moreover have "polynomial p"
    using p_def polynomial_id by (metis eq_id_iff)
  moreover have "big_oh_poly T"
    using T_def big_oh_poly_poly big_oh_poly_const big_oh_poly_sum big_oh_poly_prod by simp
  moreover have "computes_in_time 22 tm_verify_sat f T"
  proof
    fix x :: string
    let ?zs = "string_to_symbols x"
    have bs: "bit_symbols ?zs"
      by simp
    have "bit_symbols (verify_sat ?zs)"
      using bit_symbols_verify_sat by simp
    then have *: "string_to_symbols (f x) = verify_sat ?zs"
      unfolding f_def using bit_symbols_to_symbols by simp

    obtain tps where tps:
        "tps ! 1 = (\<lfloor>verify_sat ?zs\<rfloor>, 1)"
        "transforms tm_verify_sat (snd (start_config 22 ?zs)) (T (length ?zs)) tps"
      using bs transforms_tm_verify_sat T_def by blast
    then have "tps ::: 1 = string_to_contents (f x)"
      using * start_config_def contents_string_to_contents by simp
    then show "\<exists>tps. tps ::: 1 = string_to_contents (f x) \<and>
        transforms tm_verify_sat (snd (start_config_string 22 x)) (T (length x)) tps"
      using tps(2) by auto
  qed
  moreover have "\<forall>x. x \<in> SAT \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> f \<langle>x, u\<rangle> = [\<bbbI>])"
  proof
    fix x :: string
    show "(x \<in> SAT) = (\<exists>u. length u = p (length x) \<and> f \<langle>x, u\<rangle> = [\<bbbI>])"
    proof
      show "\<exists>u. length u = p (length x) \<and> f \<langle>x, u\<rangle> = [\<bbbI>]" if "x \<in> SAT"
      proof (cases "\<exists>\<phi>. x = formula_to_string \<phi>")
        case True
        then obtain \<phi> where \<phi>: "x = formula_to_string \<phi>" "satisfiable \<phi>"
          using SAT_def using \<open>x \<in> SAT\<close> by auto
        then obtain us where us:
            "bit_symbols us"
            "length us = length (formula_to_string \<phi>)"
            "verify_sat \<langle>formula_to_string \<phi>; symbols_to_string us\<rangle> = [\<one>]"
          using ex_witness_linear_length by blast
        let ?zs = "\<langle>formula_to_string \<phi>; symbols_to_string us\<rangle>"
        define u where "u = symbols_to_string us"
        have "length us = p (length x)"
          using us(2) \<phi>(1) p_def by simp
        then have 1: "length u = p (length x)"
          using u_def by simp

        have "f \<langle>x, u\<rangle> = symbols_to_string (verify_sat \<langle>x; u\<rangle>)"
          using f_def by simp
        also have "... = symbols_to_string (verify_sat ?zs)"
          using \<phi>(1) u_def by simp
        also have "... = symbols_to_string [\<one>]"
          using us(3) by simp
        also have "... = [\<bbbI>]"
          by simp
        finally have "f \<langle>x, u\<rangle> = [\<bbbI>]" .
        then show ?thesis
          using 1 by auto
      next
        case False
        define u where "u = replicate (length x) \<bbbO>"
        then have 1: "length u = p (length x)"
          using p_def by simp
        have "f \<langle>x, u\<rangle> = symbols_to_string (verify_sat \<langle>x; u\<rangle>)"
          using f_def by simp
        also have "... = symbols_to_string [\<one>]"
          using verify_sat_not_wf_phi False by simp
        also have "... = [\<bbbI>]"
          by simp
        finally have "f \<langle>x, u\<rangle> = [\<bbbI>]" .
        then show ?thesis
          using 1 by auto
      qed
      show "x \<in> SAT" if ex: "\<exists>u. length u = p (length x) \<and> f \<langle>x, u\<rangle> = [\<bbbI>]"
      proof (rule ccontr)
        assume notin: "x \<notin> SAT"
        then obtain \<phi> where \<phi>: "x = formula_to_string \<phi>" "\<not> satisfiable \<phi>"
          using SAT_def by auto
        obtain u where u: "length u = p (length x)" "f \<langle>x, u\<rangle> = [\<bbbI>]"
          using ex by auto
        have "f \<langle>x, u\<rangle> = symbols_to_string (verify_sat \<langle>x; u\<rangle>)"
          using f_def by simp
        also have "... = symbols_to_string (verify_sat \<langle>formula_to_string \<phi>; u\<rangle>)"
          using \<phi>(1) by simp
        also have "... = symbols_to_string []"
          using verify_sat_not_sat \<phi>(2) by simp
        also have "... = []"
          by simp
        finally have "f \<langle>x, u\<rangle> = []" .
        then show False
          using u(2) by simp
      qed
    qed
  qed
  ultimately show ?thesis
    using complexity_class_NP_def by fast
qed

end
