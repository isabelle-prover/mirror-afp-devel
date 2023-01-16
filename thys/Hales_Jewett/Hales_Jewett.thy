theory "Hales_Jewett"
  imports Main "HOL-Library.Disjoint_Sets" "HOL-Library.FuncSet"
begin

section \<open>Preliminaries\<close>

text \<open>
  The Hales--Jewett Theorem is at its core a statement about sets of tuples called the
$n$-dimensional cube over $t$ elements (denoted by $C^n_t$); i.e.\ the set $\{0,\ldots,t - 1\}^n$, where 
$\{0,\ldots,t - 1\}$ is called the base. 
  We represent tuples by functions $f : \{0,\ldots,n - 1\} \rightarrow \{0,\ldots,t - 1\}$ because
they're easier to deal with. The set of tuples then becomes the function space 
$\{0,\ldots,t - 1\}^{\{0,\ldots,n - 1\}}$.
  Furthermore, $r$-colourings of the cube are represented by mappings from the function space to the
set $\{0,\ldots, r-1\}$.
\<close>

subsection \<open>The $n$-dimensional cube over $t$ elements\<close>

text \<open>
  Function spaces in Isabelle are supported by the library component FuncSet.
  In essence, \<^prop>\<open>f \<in> A \<rightarrow>\<^sub>E B\<close> means \<^prop>\<open>a \<in> A \<Longrightarrow> f a \<in> B\<close> and \<^prop>\<open>a \<notin> A \<Longrightarrow> f a = undefined\<close>
\<close>

text \<open>The (canonical) $n$-dimensional cube over $t$ elements is defined in the following using the variables:

\begin{tabular}{lcp{8cm}}
$n$:& \<^typ>\<open>nat\<close>& dimension\\
$t$:& \<^typ>\<open>nat\<close>& number of elements\\
\end{tabular}\<close>
definition cube :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "cube n t \<equiv> {..<n} \<rightarrow>\<^sub>E {..<t}"

text \<open>
  For any function $f$ whose image under a set $A$ is a subset of another set $B$, there's
a unique function $g$ in the function space $B^A$ that equals $f$ everywhere in $A$.
  The function $g$ is usually written as $f|_A$ in the mathematical literature.
\<close>
lemma PiE_uniqueness: "f ` A \<subseteq> B \<Longrightarrow> \<exists>!g \<in> A
\<rightarrow>\<^sub>E B. \<forall>a\<in>A. g a = f a"
  using exI[of "\<lambda>x. x \<in> A \<rightarrow>\<^sub>E B \<and> (\<forall>a\<in>A. x a = f a)"
      "restrict f A"] PiE_ext PiE_iff by fastforce


text \<open>Any prefix of length $j$ of an $n$-tuple (i.e.\ element of $C^n_t$) is a $j$-tuple
(i.e.\ element of $C^j_t$).\<close>
lemma cube_restrict: 
  assumes "j < n" 
    and "y \<in> cube n t" 
  shows "(\<lambda>g \<in> {..<j}. y g) \<in> cube j t" using assms unfolding cube_def by force

text \<open>Narrowing down the obvious fact $B^A \subseteq C^A$ if $B \subseteq C$ to a specific case for cubes. \<close>
lemma cube_subset: "cube n t \<subseteq> cube n (t + 1)"
  unfolding cube_def using PiE_mono[of "{..<n}" "\<lambda>x. {..<t}" "\<lambda>x. {..<t+1}"]
  by simp 

text \<open>A simplifying definition for the 0-dimensional cube.\<close>
lemma cube0_alt_def: "cube 0 t = {\<lambda>x. undefined}"
  unfolding cube_def by simp

text \<open>
  The cardinality of the \<open>n\<close>-dimensional over \<open>t\<close> elements is simply a consequence of the overarching 
definition of the cardinality of function spaces (over finite sets).\<close>
lemma cube_card: "card ({..<n::nat} \<rightarrow>\<^sub>E {..<t::nat}) = t ^ n"
  by (simp add: card_PiE)

text \<open>A simplifying definition for the \<open>n\<close>-dimensional cube over 
a single element, i.e.\ the single \<open>n\<close>-dimensional point \<open>(0, \<dots>, 0)\<close>.\<close>
lemma cube1_alt_def: "cube n 1 = {\<lambda>x\<in>{..<n}. 0}" unfolding cube_def by (simp add: lessThan_Suc)

subsection \<open>Lines\<close>

text \<open>The property of being a line in $C^n_t$ is defined in the following using the variables:

\begin{tabular}{llp{8cm}}
$L$:& \<^typ>\<open>nat \<Rightarrow> (nat \<Rightarrow> nat)\<close>& line\\
$n$:& \<^typ>\<open>nat\<close>& dimension of cube\\
$t$:& \<^typ>\<open>nat\<close>& the size of the cube's base\\
\end{tabular}\<close>
definition is_line :: "(nat \<Rightarrow> (nat \<Rightarrow> nat)) \<Rightarrow> nat \<Rightarrow>
nat \<Rightarrow> bool"
  where "is_line L n t \<equiv> (L \<in> {..<t} \<rightarrow>\<^sub>E cube n t \<and>
  ((\<forall>j<n. (\<forall>x<t. \<forall>y<t. L x j =  L y j) \<or> (\<forall>s<t. L s j = s))
  \<and> (\<exists>j < n. (\<forall>s < t. L s j = s))))"

text \<open>We introduce an elimination rule to relate lines with the more general definition of a
subspace (see below). \<close>
lemma is_line_elim_t_1:
  assumes "is_line L n t" and "t = 1"
  obtains B\<^sub>0 B\<^sub>1
  where "B\<^sub>0 \<union> B\<^sub>1 = {..<n} \<and> B\<^sub>0 \<inter> B\<^sub>1 = {} \<and>
  B\<^sub>0 \<noteq> {} \<and> (\<forall>j \<in> B\<^sub>1. (\<forall>x<t. \<forall>y<t. L x j = L y
  j)) \<and> (\<forall>j \<in> B\<^sub>0. (\<forall>s<t. L s j = s))"
proof -
  define B0 where "B0 = {..<n}"
  define B1 where "B1 = ({}::nat set)"
  have "B0 \<union> B1 = {..<n}" unfolding B0_def B1_def by simp
  moreover have "B0 \<inter> B1 = {}" unfolding B0_def B1_def by simp
  moreover have "B0 \<noteq> {}" using assms unfolding B0_def is_line_def by auto
  moreover have "(\<forall>j \<in> B1. (\<forall>x<t. \<forall>y<t. L x j = L y j))" unfolding B1_def by simp
  moreover have "(\<forall>j \<in> B0. (\<forall>s<t. L s j = s))" using assms(1, 2) cube1_alt_def
    unfolding B0_def is_line_def by auto
  ultimately show ?thesis using that by simp
qed


text \<open>The next two lemmas are used to simplify proofs by enabling us to use the resulting
facts directly. This avoids having to unfold the definition of \<^const>\<open>is_line\<close> each
time.\<close>
lemma line_points_in_cube: 
  assumes "is_line L n t" 
    and "s < t" 
  shows "L s \<in> cube n t"
  using assms unfolding cube_def is_line_def
  by auto     

lemma line_points_in_cube_unfolded:
  assumes "is_line L n t" 
    and "s < t" 
    and "j < n" 
  shows "L s j \<in> {..<t}" 
  using assms line_points_in_cube unfolding cube_def by blast

text \<open>The incrementation of all elements of a set is defined in the following using the variables:

\begin{tabular}{llp{8cm}}
$n$:& \<^typ>\<open>nat\<close>& increment size\\
$S$:& \<^typ>\<open>nat set\<close>& set\\
\end{tabular}\<close>
definition set_incr :: "nat \<Rightarrow> nat set \<Rightarrow> nat set"
  where
  	"set_incr n S \<equiv> (\<lambda>a. a + n) ` S"

lemma set_incr_disjnt: 
  assumes "disjnt A B" 
  shows "disjnt (set_incr n A) (set_incr n B)" 
  using assms unfolding disjnt_def set_incr_def by force

lemma set_incr_disjoint_family: 
  assumes "disjoint_family_on B {..k}" 
  shows " disjoint_family_on (\<lambda>i. set_incr n (B i)) {..k}" 
  using assms set_incr_disjnt unfolding disjoint_family_on_def by (meson disjnt_def)

lemma set_incr_altdef: "set_incr n S = (+) n ` S"
  by (auto simp: set_incr_def)

lemma set_incr_image:
  assumes "(\<Union>i\<in>{..k}. B i) = {..<n}"
  shows "(\<Union>i\<in>{..k}. set_incr m (B i)) = {m..<m+n}"
  using assms by (simp add: set_incr_altdef add.commute flip: image_UN atLeast0LessThan)

text \<open>Each tuple of dimension $k+1$ can be split into a tuple of dimension $1$ (the first
entry) and a tuple of dimension $k$ (the remaining entries).\<close>
lemma split_cube: 
  assumes "x \<in> cube (k+1) t" 
  shows "(\<lambda>y \<in> {..<1}. x y) \<in> cube 1 t" 
    and "(\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube k t"
  using assms unfolding cube_def by auto

subsection \<open>Subspaces\<close>

text \<open>The property of being a $k$-dimensional subspace of $C^n_t$ is defined in the following using the variables:

\begin{tabular}{llp{8cm}}
$S$:& \<^typ>\<open>(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)\<close>& the subspace\\
$k$:& \<^typ>\<open>nat\<close>& the dimension of the subspace\\
$n$:& \<^typ>\<open>nat\<close>& the dimension of the cube\\
$t$:& \<^typ>\<open>nat\<close>& the size of the cube's base
\end{tabular}\<close>
definition is_subspace
  where "is_subspace S k n t \<equiv> (\<exists>B f. disjoint_family_on B {..k} \<and> \<Union>(B `
  {..k}) = {..<n} \<and> ({} \<notin> B ` {..<k}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t}
  \<and> S \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube k t.
  (\<forall>i \<in> B k. S y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (S y) i = y j)))"

text \<open>A $k$-dimensional subspace of $C^n_t$ can be thought of as an embedding of the $C^k_t$
into $C^n_t$, akin to how a $k$-dimensional vector subspace of $\mathbf{R}^n$ may be thought of as
an embedding of $\mathbf{R}^k$ into $\mathbf{R}^n$.\<close> 
lemma subspace_inj_on_cube: 
  assumes "is_subspace S k n t" 
  shows "inj_on S (cube k t)"
proof 
	fix x y
	assume a: "x \<in> cube k t" "y \<in> cube k t" "S x = S y"
	from assms obtain B f where Bf_props: "disjoint_family_on B {..k} \<and> \<Union>(B ` {..k}) =
    {..<n} \<and> ({} \<notin> B ` {..<k}) \<and> f \<in> (B k) \<rightarrow>\<^sub>E {..<t} \<and>
    S \<in> (cube k t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube k t.
    (\<forall>i \<in> B k. S y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. (S y) i = y j))"
    unfolding is_subspace_def by auto
	have "\<forall>i<k. x i = y i"
	proof (intro allI impI)
		fix j assume "j < k"
	  then have "B j \<noteq> {}" using Bf_props by auto
	  then obtain i where i_prop: "i \<in> B j" by blast
	  then have "y j = S y i" using Bf_props a(2) \<open>j < k\<close> by auto
	  also have " ... = S x i" using a by simp
	  also have " ... = x j" using Bf_props a(1) \<open>j < k\<close> i_prop by blast
	  finally show "x j = y j" by simp
	qed
	then show "x = y" using a(1,2) unfolding cube_def by (meson PiE_ext lessThan_iff)
qed

text \<open>The following is required to handle base cases in the key lemmas.\<close>
lemma dim0_subspace_ex: 
  assumes "t > 0" 
  shows "\<exists>S. is_subspace S 0 n t"
proof-
  define B where "B \<equiv> (\<lambda>x::nat. undefined)(0:={..<n})"

  have "{..<t} \<noteq> {}" using assms by auto
  then have "\<exists>f. f \<in> (B 0) \<rightarrow>\<^sub>E {..<t}" 
    by (meson PiE_eq_empty_iff all_not_in_conv)
  then obtain f where f_prop: "f \<in> (B 0) \<rightarrow>\<^sub>E {..<t}" by blast
  define S where "S \<equiv> (\<lambda>x::(nat \<Rightarrow> nat). undefined)((\<lambda>x. undefined):=f)"

  have "disjoint_family_on B {..0}" unfolding disjoint_family_on_def by simp
  moreover have "\<Union>(B ` {..0}) = {..<n}" unfolding B_def by simp
  moreover have "({} \<notin> B ` {..<0})" by simp
  moreover have "S \<in> (cube 0 t) \<rightarrow>\<^sub>E (cube n t)"
    using f_prop PiE_I unfolding B_def cube_def S_def by auto
  moreover have "(\<forall>y \<in> cube 0 t. (\<forall>i \<in> B 0. S y i = f i) \<and>
  (\<forall>j<0. \<forall>i \<in> B j. (S y) i = y j))" unfolding cube_def S_def by force
  ultimately have "is_subspace S 0 n t" using f_prop unfolding is_subspace_def by blast
  then show "\<exists>S. is_subspace S 0 n t" by auto
qed

subsection \<open>Equivalence classes\<close>
text \<open>Defining the equivalence classes of \<^term>\<open>cube n (t + 1)\<close>:
\<open>{classes n t 0, \<dots>, classes n t n}\<close>\<close>
definition classes
  where "classes n t \<equiv> (\<lambda>i. {x . x \<in> (cube n (t + 1)) \<and> (\<forall>u \<in>
  {(n-i)..<n}. x u = t) \<and> t \<notin> x ` {..<(n - i)}})"

lemma classes_subset_cube: "classes n t i \<subseteq> cube n (t+1)" unfolding classes_def by blast

definition layered_subspace
  where "layered_subspace S k n t r \<chi> \<equiv> (is_subspace S k n (t + 1)  \<and> (\<forall>i
  \<in> {..k}. \<exists>c<r. \<forall>x \<in> classes k t i. \<chi> (S x) = c)) \<and> \<chi> \<in>
  cube n (t + 1) \<rightarrow>\<^sub>E {..<r}"

lemma layered_eq_classes: 
  assumes "layered_subspace S k n t r \<chi>" 
  shows "\<forall>i \<in> {..k}. \<forall>x \<in> classes k t i. \<forall>y \<in> classes k t i.
  \<chi> (S x) = \<chi> (S y)" 
proof (safe)
  fix i x y
  assume a: "i \<le> k" "x \<in> classes k t i" "y \<in> classes k t i"
  then obtain c where "c < r \<and> \<chi> (S x) = c \<and> \<chi> (S y) = c" using assms unfolding
      layered_subspace_def by fast
  then show "\<chi> (S x) = \<chi> (S y)" by simp
qed

lemma dim0_layered_subspace_ex: 
  assumes "\<chi> \<in> (cube n (t + 1)) \<rightarrow>\<^sub>E {..<r::nat}" 
  shows "\<exists>S. layered_subspace S (0::nat) n t r \<chi>"
proof-
  obtain S where S_prop: "is_subspace S (0::nat) n (t+1)" using dim0_subspace_ex by auto
  have "classes (0::nat) t 0 = cube 0 (t+1)" unfolding classes_def by simp
  moreover have "(\<forall>i \<in> {..0::nat}. \<exists>c<r. \<forall>x \<in> classes (0::nat) t i. \<chi> (S x) = c)"
  proof(safe)
    fix i
    have "\<forall>x \<in> classes 0 t 0. \<chi> (S x) = \<chi> (S (\<lambda>x. undefined))" using cube0_alt_def 
      using \<open>classes 0 t 0 = cube 0 (t + 1)\<close> by auto
    moreover have "S (\<lambda>x. undefined) \<in> cube n (t+1)" using S_prop cube0_alt_def
      unfolding is_subspace_def by auto
    moreover have "\<chi> (S (\<lambda>x. undefined)) < r" using assms calculation by auto
    ultimately show "\<exists>c<r. \<forall>x\<in>classes 0 t 0. \<chi> (S x) = c" by auto
  qed
  ultimately have "layered_subspace S 0 n t r \<chi>" using S_prop assms unfolding layered_subspace_def by blast
  then show "\<exists>S. layered_subspace S (0::nat) n t r \<chi>" by auto
qed

lemma disjoint_family_onI [intro]:
  assumes "\<And>m n. m \<in> S \<Longrightarrow> n \<in> S \<Longrightarrow> m \<noteq> n
  \<Longrightarrow> A m \<inter> A n = {}"
  shows   "disjoint_family_on A S"
  using assms by (auto simp: disjoint_family_on_def)

lemma fun_ex: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> \<exists>f \<in> A
\<rightarrow>\<^sub>E B. f a = b" 
proof-
  assume assms: "a \<in> A" "b \<in> B"
  then obtain g where g_def: "g \<in> A \<rightarrow> B \<and> g a = b" by fast
  then have "restrict g A \<in> A \<rightarrow>\<^sub>E B \<and> (restrict g A) a = b" using assms(1) by auto
  then show ?thesis by blast
qed

lemma ex_bij_betw_nat_finite_2: 
  assumes "card A = n" 
    and "n > 0" 
  shows "\<exists>f. bij_betw f A {..<n}"
  using assms ex_bij_betw_finite_nat[of A] atLeast0LessThan card_ge_0_finite by auto

lemma one_dim_cube_eq_nat_set: "bij_betw (\<lambda>f. f 0) (cube 1 k) {..<k}"
proof (unfold bij_betw_def)
  have *: "(\<lambda>f. f 0) ` cube 1 k = {..<k}"
  proof(safe)
    fix x f
    assume "f \<in> cube 1 k"
    then show "f 0 < k" unfolding cube_def by blast
  next
    fix x
    assume "x < k"
    then have "x \<in> {..<k}" by simp
    moreover have "0 \<in> {..<1::nat}" by simp
    ultimately have "\<exists>y \<in> {..<1::nat} \<rightarrow>\<^sub>E {..<k}. y 0 = x" using
        fun_ex[of "0" "{..<1::nat}" "x" "{..<k}"] by auto 
    then show "x \<in> (\<lambda>f. f 0) ` cube 1 k" unfolding cube_def by blast
  qed
  moreover 
  {
    have "card (cube 1 k) = k" using cube_card by (simp add: cube_def)
    moreover have "card {..<k} = k" by simp
    ultimately have "inj_on (\<lambda>f. f 0) (cube 1 k)" using * eq_card_imp_inj_on[of "cube 1 k" "\<lambda>f. f 0"] 
      by force
  }
  ultimately show "inj_on (\<lambda>f. f 0) (cube 1 k) \<and> (\<lambda>f. f 0) ` cube 1 k = {..<k}" by simp
qed

text \<open>An alternative introduction rule for the $\exists!x$ quantifier, which means "there
exists exactly one $x$".\<close>
lemma ex1I_alt: "(\<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> x = y)) \<Longrightarrow> (\<exists>!x. P x)" 
  by auto
lemma nat_set_eq_one_dim_cube: "bij_betw (\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) {..<k::nat} (cube 1 k)"
proof (unfold bij_betw_def)
  have *: "(\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) ` {..<k} = cube 1 k"
  proof (safe)
    fix x y
    assume "y < k"
    then show "(\<lambda>z\<in>{..<1}. y) \<in> cube 1 k" unfolding cube_def by simp
  next
    fix x
    assume "x \<in> cube 1 k"
    have "x = (\<lambda>z. \<lambda>y\<in>{..<1::nat}. z) (x 0::nat)" 
    proof
      fix j 
      consider "j \<in> {..<1}" | "j \<notin> {..<1::nat}" by linarith
      then show "x j = (\<lambda>z. \<lambda>y\<in>{..<1::nat}. z) (x 0::nat) j" using \<open>x
      \<in> cube 1 k\<close> unfolding cube_def by auto
    qed
    moreover have "x 0 \<in> {..<k}" using \<open>x \<in> cube 1 k\<close> by (auto simp add: cube_def)
    ultimately show "x \<in> (\<lambda>z. \<lambda>y\<in>{..<1}. z) ` {..<k}"  by blast
  qed
  moreover
  {
    have "card (cube 1 k) = k" using cube_card by (simp add: cube_def)
    moreover have "card {..<k} = k" by simp
    ultimately have  "inj_on (\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) {..<k}" using *
        eq_card_imp_inj_on[of "{..<k}" "\<lambda>x. \<lambda>y\<in>{..<1::nat}. x"] by force
  }
  ultimately show "inj_on (\<lambda>x. \<lambda>y\<in>{..<1::nat}. x) {..<k} \<and> (\<lambda>x.
  \<lambda>y\<in>{..<1::nat}. x) ` {..<k} = cube 1 k" by blast
qed

text \<open>A bijection $f$ between domains $A_1$ and $A_2$ creates a correspondence between
functions in $A_1 \rightarrow B$ and $A_2 \rightarrow B$.\<close>
lemma bij_domain_PiE:
  assumes "bij_betw f A1 A2" 
    and "g \<in> A2 \<rightarrow>\<^sub>E B"
  shows "(restrict (g \<circ> f) A1) \<in> A1 \<rightarrow>\<^sub>E B"
  using bij_betwE assms by fastforce

text \<open>The following three lemmas relate lines to $1$-dimensional subspaces (in the natural
way). This is a direct consequence of the elimination rule \<open>is_line_elim\<close> introduced
above.\<close>
lemma line_is_dim1_subspace_t_1: 
  assumes "n > 0" 
    and "is_line L n 1"
  shows "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 1)) 1 n 1"
proof -
  obtain B\<^sub>0 B\<^sub>1 where B_props: "B\<^sub>0 \<union> B\<^sub>1 = {..<n} \<and> B\<^sub>0
  \<inter> B\<^sub>1 = {} \<and> B\<^sub>0 \<noteq> {} \<and> (\<forall>j \<in> B\<^sub>1.
  (\<forall>x<1. \<forall>y<1. L x j = L y j)) \<and> (\<forall>j \<in> B\<^sub>0. (\<forall>s<1. L
  s j = s))" using is_line_elim_t_1[of L n 1] assms by auto
  define B where "B \<equiv> (\<lambda>i::nat. {}::nat set)(0:=B\<^sub>0, 1:=B\<^sub>1)" 
  define f where "f \<equiv> (\<lambda>i \<in> B 1. L 0 i)"
  have *: "L 0 \<in> {..<n} \<rightarrow>\<^sub>E {..<1}" using assms(2) unfolding cube_def is_line_def by auto
  have "disjoint_family_on B {..1}" unfolding B_def using B_props 
    by (simp add: Int_commute disjoint_family_onI)
  moreover have "\<Union> (B ` {..1}) = {..<n}" unfolding B_def using B_props by auto
  moreover have "{} \<notin> B ` {..<1}" unfolding B_def using B_props by auto
  moreover have " f \<in> B 1 \<rightarrow>\<^sub>E {..<1}" using * calculation(2) unfolding f_def by auto
  moreover have "(restrict (\<lambda>y. L (y 0)) (cube 1 1)) \<in> cube 1 1 \<rightarrow>\<^sub>E cube n 1" 
    using assms(2) cube1_alt_def unfolding is_line_def by auto
  moreover have "(\<forall>y\<in>cube 1 1. (\<forall>i\<in>B 1. (restrict (\<lambda>y. L (y 0)) (cube 1 1)) y i = f i) 
  \<and> (\<forall>j<1. \<forall>i\<in>B j. (restrict (\<lambda>y. L (y 0)) (cube 1 1)) y i = y j))" 
    using cube1_alt_def B_props * unfolding B_def f_def by auto
  ultimately show ?thesis unfolding is_subspace_def by blast 
qed

lemma line_is_dim1_subspace_t_ge_1: 
  assumes "n > 0"
    and "t > 1"
    and "is_line L n t"
  shows "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 n t"
proof -
  let ?B1 = "{i::nat . i < n \<and> (\<forall>x<t. \<forall>y<t. L x i =  L y i)}"
  let ?B0 = "{i::nat . i < n \<and> (\<forall>s < t. L s i = s)}"
  define B where "B \<equiv> (\<lambda>i::nat. {}::nat set)(0:=?B0, 1:=?B1)"
  let ?L = "(\<lambda>y \<in> cube 1 t. L (y 0))"
  have "?B0 \<noteq> {}" using assms(3) unfolding is_line_def by simp

  have L1: "?B0 \<union> ?B1 = {..<n}" using assms(3) unfolding is_line_def by auto
  {
    have "(\<forall>s < t. L s i = s) \<longrightarrow> \<not>(\<forall>x<t. \<forall>y<t. L x i =
    L y i)" if "i < n" for i using assms(2) less_trans by auto 
    then have *:"i \<notin> ?B0" if "i \<in> ?B1" for i using that by blast
  }
  moreover
  {
    have "(\<forall>x<t. \<forall>y<t. L x i =  L y i) \<longrightarrow> \<not>(\<forall>s < t. L s i = s)" 
      if "i < n" for i using that calculation by blast
    then have **: "\<forall>i \<in> ?B0. i \<notin> ?B1" 
      by blast
  }
  ultimately have L2: "?B0 \<inter> ?B1 = {}" by blast

  let ?f = "(\<lambda>i. if i \<in> B 1 then L 0 i else undefined)"
  {
    have "{..1::nat} = {0, 1}" by auto
    then have "\<Union>(B ` {..1::nat}) = B 0 \<union> B 1" by simp
    then have "\<Union>(B ` {..1::nat}) = ?B0 \<union> ?B1" unfolding B_def by simp
    then have A1: "disjoint_family_on B {..1::nat}" using L2 
      by (simp add: B_def Int_commute disjoint_family_onI)
  }
  moreover
  {
    have "\<Union>(B ` {..1::nat}) = B 0 \<union> B 1" unfolding B_def by auto
    then have "\<Union>(B ` {..1::nat}) = {..<n}" using L1 unfolding B_def by simp
  }
  moreover
  {
    have "\<forall>i \<in> {..<1::nat}. B i \<noteq> {}" 
      using \<open>{i. i < n \<and> (\<forall>s<t. L s i = s)} \<noteq> {}\<close> fun_upd_same lessThan_iff less_one 
      unfolding B_def by auto
    then have "{} \<notin> B ` {..<1::nat}" by blast
  }
  moreover 
  {
    have "?f \<in> (B 1) \<rightarrow>\<^sub>E {..<t}" 
    proof
      fix i
      assume asm: "i \<in> (B 1)"
      have "L a b \<in> {..<t}" if "a < t" and "b < n" for a b using assms(3) that unfolding is_line_def cube_def by auto
      then have "L 0 i \<in> {..<t}" using assms(2) asm calculation(2) by blast
      then show "?f i \<in> {..<t}" using asm by presburger
    qed (auto)
  }

  moreover
  {
    have "L \<in> {..<t} \<rightarrow>\<^sub>E (cube n t)" using assms(3) by (simp add: is_line_def)
    then have "?L \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube n t)"
      using bij_domain_PiE[of "(\<lambda>f. f 0)" "(cube 1 t)" "{..<t}" "L" "cube n t"] one_dim_cube_eq_nat_set[of "t"] 
      by auto
  }
  moreover
  {
    have "\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. ?L y i = ?f i) \<and> (\<forall>j < 1.
    \<forall>i \<in> B j. (?L y) i = y j)"
    proof
      fix y 
      assume "y \<in> cube 1 t"
      then have "y 0 \<in> {..<t}" unfolding cube_def by blast

      have "(\<forall>i \<in> B 1. ?L y i = ?f i)"
      proof
        fix i
        assume "i \<in> B 1"
        then have "?f i = L 0 i" 
          by meson
        moreover have "?L y i = L (y 0) i" using \<open>y \<in> cube 1 t\<close> by simp
        moreover have "L (y 0) i = L 0 i" 
        proof -
          have "i \<in> ?B1" using \<open>i \<in> B 1\<close> unfolding B_def fun_upd_def by presburger
          then have "(\<forall>x<t. \<forall>y<t. L x i = L y i)" by blast
          then show "L (y 0) i = L 0 i" using \<open>y 0 \<in> {..<t}\<close> by blast
        qed
        ultimately show "?L y i = ?f i" by simp
      qed

      moreover have "(?L y) i = y j" if "j < 1" and "i \<in> B j" for i j
      proof-
        have "i \<in> B 0" using that by blast
        then have "i \<in> ?B0" unfolding B_def by auto 
        then have "(\<forall>s < t. L s i = s)" by blast
        moreover have "y 0 < t" using \<open>y \<in> cube 1 t\<close> unfolding cube_def by auto
        ultimately have "L (y 0) i = y 0" by simp
        then show "?L y i = y j" using that using \<open>y \<in> cube 1 t\<close> by force
      qed

      ultimately show "(\<forall>i \<in> B 1. ?L y i = ?f i) \<and> (\<forall>j < 1. \<forall>i
      \<in> B j. (?L y) i = y j)" 
        by blast
    qed
  }
  ultimately show "is_subspace ?L 1 n t" unfolding is_subspace_def by blast
qed

lemma line_is_dim1_subspace: 
  assumes "n > 0" 
    and "t > 0" 
    and "is_line L n t"
  shows "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 n t"
  using line_is_dim1_subspace_t_1[of n L] line_is_dim1_subspace_t_ge_1[of n t L] assms not_less_iff_gr_or_eq by blast

text \<open>The key property of the existence of a minimal dimension $N$, such that for any
$r$-colouring in $C^{N'}_t$ (for $N' \geq N$) there exists a monochromatic line is defined in the
following using the variables:

\begin{tabular}{llp{8cm}}
$r$:& \<^typ>\<open>nat\<close>& the number of colours\\
$t$:& \<^typ>\<open>nat\<close>& the size of of the base
\end{tabular}\<close>
definition hj 
  where "hj r t \<equiv> (\<exists>N>0. \<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in> (cube N'
  t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t
  \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c)))"

text \<open>The key property of the existence of a minimal dimension $N$, such that for any
$r$-colouring in $C^{N'}_t$ (for $N' \geq N$) there exists a layered subspace of dimension $k$ is
defined in the following using the variables:

\begin{tabular}{llp{8cm}}
$r$:& \<^typ>\<open>nat\<close>& the number of colours\\
$t$:& \<^typ>\<open>nat\<close>& the size of of the base\\
$k$:& \<^typ>\<open>nat\<close>& the dimension of the subspace
\end{tabular}\<close>
definition lhj
  where "lhj r t k \<equiv> (\<exists>N > 0. \<forall>N' \<ge> N. \<forall>\<chi>. \<chi> \<in>
  (cube N' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S.
  layered_subspace S k N' t r \<chi>))"

text \<open>We state some useful facts about $1$-dimensional subspaces.\<close>
lemma dim1_subspace_elims: 
  assumes "disjoint_family_on B {..1::nat}" and "\<Union>(B ` {..1::nat}) = {..<n}" and "({}
  \<notin> B ` {..<1::nat})" and  "f \<in> (B 1) \<rightarrow>\<^sub>E {..<t}" and "S \<in> (cube 1
  t) \<rightarrow>\<^sub>E (cube n t)" and "(\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i
  = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. (S y) i = y j))"
  shows "B 0 \<union> B 1 = {..<n}"
    and "B 0 \<inter> B 1 = {}"
    and "(\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>i \<in> B 0. (S y) i = y 0))"
    and "B 0 \<noteq> {}"
proof -
  have "{..1} = {0::nat, 1}" by auto
  then show "B 0 \<union> B 1 = {..<n}"  using assms(2) by simp
next
  show "B 0 \<inter> B 1 = {}" using assms(1) unfolding disjoint_family_on_def by simp
next
  show "(\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>i \<in> B 0. (S y) i = y 0))" 
    using assms(6) by simp
next
  show "B 0 \<noteq> {}" using assms(3) by auto
qed

text \<open>We state some properties of cubes.\<close>
lemma cube_props:
  assumes "s < t"
  shows "\<exists>p \<in> cube 1 t. p 0 = s"
    and "(SOME p. p \<in> cube 1 t \<and> p 0 = s) 0 = s"
    and "(\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) s =
    (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) ((SOME p. p \<in> cube 1 t
    \<and> p 0 = s) 0)"
    and "(SOME p. p \<in> cube 1 t \<and> p 0 = s) \<in> cube 1 t"
proof -
  show 1: "\<exists>p \<in> cube 1 t. p 0 = s" using assms unfolding cube_def by (simp add: fun_ex)
  show 2: "(SOME p. p \<in> cube 1 t \<and> p 0 = s) 0 = s" using assms 1 someI_ex[of "\<lambda>x. x
  \<in> cube 1 t \<and> x 0 = s"] by blast 
  show 3: "(\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) s =
  (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) ((SOME p. p \<in> cube 1 t
  \<and> p 0 = s) 0)" using 2 by simp
  show 4: "(SOME p. p \<in> cube 1 t \<and> p 0 = s) \<in> cube 1 t" using 1 someI_ex[of
        "\<lambda>p. p \<in> cube 1 t \<and> p 0 = s"] assms by blast
qed

text \<open>The following lemma relates $1$-dimensional subspaces to lines, thus establishing a
bidirectional correspondence between the two together with
\<open>line_is_dim1_subspace\<close>.\<close>
lemma dim1_subspace_is_line: 
  assumes "t > 0" 
    and "is_subspace S 1 n t" 
  shows   "is_line (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) n t"
proof-
  define L where "L \<equiv> (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s))"
  have "{..1} = {0::nat, 1}" by auto
  obtain B f where Bf_props: "disjoint_family_on B {..1::nat} \<and> \<Union>(B ` {..1::nat}) =
  {..<n} \<and> ({} \<notin> B ` {..<1::nat}) \<and> f \<in> (B 1) \<rightarrow>\<^sub>E {..<t}
  \<and> S \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube n t) \<and> (\<forall>y \<in> cube 1 t.
  (\<forall>i \<in> B 1. S y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. (S y) i = y j))"
    using assms(2) unfolding is_subspace_def by auto
  then have 1: "B 0 \<union> B 1 = {..<n} \<and> B 0 \<inter> B 1 = {}" using dim1_subspace_elims(1,
        2)[of B n f t S] by simp

  have "L \<in> {..<t} \<rightarrow>\<^sub>E cube n t"
  proof
    fix s assume a: "s \<in> {..<t}"
    then have "L s = S (SOME p. p\<in>cube 1 t \<and> p 0 = s)" unfolding L_def by simp
    moreover have "(SOME p. p\<in>cube 1 t \<and> p 0 = s) \<in> cube 1 t" using cube_props(1) a
        someI_ex[of "\<lambda>p. p \<in> cube 1 t \<and> p 0 = s"] by blast
    moreover have "S (SOME p. p\<in>cube 1 t \<and> p 0 = s) \<in> cube n t"
      using assms(2) calculation(2) is_subspace_def by auto
    ultimately show "L s \<in> cube n t" by simp
  next
    fix s assume a: "s \<notin> {..<t}"
    then show "L s = undefined" unfolding L_def by simp
  qed
  moreover have "(\<forall>x<t. \<forall>y<t. L x j = L y j) \<or> (\<forall>s<t. L s j = s)" if "j < n" for j
  proof-
    consider "j \<in> B 0" | "j \<in> B 1" using \<open>j < n\<close> 1 by blast 
    then show "(\<forall>x<t. \<forall>y<t. L x j = L y j) \<or> (\<forall>s<t. L s j = s)"
    proof (cases)
      case 1
      have "L s j = s" if "s < t" for s
      proof-
        have "\<forall>y \<in> cube 1 t. (S y) j = y 0" using Bf_props 1 by simp
        then show "L s j = s" using that cube_props(2,4)  unfolding L_def by auto
      qed
      then show ?thesis by blast
    next
      case 2
      have "L x j = L y j" if "x < t" and "y < t" for x y
      proof-
        have *: "S y j = f j" if "y \<in> cube 1 t" for y using 2 that Bf_props by simp
        then have "L y j = f j" using that(2) cube_props(2,4) lessThan_iff restrict_apply unfolding L_def by fastforce
        moreover from * have "L x j = f j" using that(1) cube_props(2,4) lessThan_iff restrict_apply unfolding L_def 
          by fastforce
        ultimately show "L x j = L y j" by simp
      qed
      then show ?thesis by blast
    qed
  qed
  moreover have "(\<exists>j<n. \<forall>s<t. (L s j = s))"
  proof -
    obtain j where j_prop: "j \<in> B 0 \<and> j < n" using Bf_props by blast
    then have "(S y) j = y 0" if "y \<in> cube 1 t" for y using that Bf_props by auto
    then have "L s j = s" if "s < t" for s using that cube_props(2,4) unfolding L_def by auto
    then show "\<exists>j<n. \<forall>s<t. (L s j = s)" using j_prop by blast
  qed
  ultimately show "is_line (\<lambda>s\<in>{..<t}. S (SOME p. p\<in>cube 1 t \<and> p 0 = s)) n t" 
    unfolding L_def is_line_def by auto
qed

lemma bij_unique_inv: 
  assumes "bij_betw f A B"  
    and "x \<in> B"
  shows "\<exists>!y \<in> A. (the_inv_into A f) x = y" 
  using assms unfolding bij_betw_def inj_on_def the_inv_into_def 
  by blast

lemma inv_into_cube_props:
  assumes "s < t"
  shows "the_inv_into (cube 1 t) (\<lambda>f. f 0) s \<in> cube 1 t" 
    and "the_inv_into (cube 1 t) (\<lambda>f. f 0) s 0 = s"
  using assms bij_unique_inv one_dim_cube_eq_nat_set f_the_inv_into_f_bij_betw
  by fastforce+

lemma some_inv_into: 
  assumes "s < t" 
  shows "(SOME p. p\<in>cube 1 t \<and> p 0 = s) = (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)"
  using inv_into_cube_props[of s t] one_dim_cube_eq_nat_set[of t] assms unfolding bij_betw_def inj_on_def by auto

lemma some_inv_into_2: 
  assumes "s < t" 
  shows "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) = (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)"
proof-
  have *: "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) \<in> cube 1 (t+1)" using cube_props assms by simp
  then have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) 0 = s" using cube_props assms by simp
  moreover
  {
    have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) ` {..<1} \<subseteq> {..<t}" using calculation assms by force
    then have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) \<in> cube 1 t" using * unfolding cube_def by auto  
  }
  moreover have "inj_on (\<lambda>f. f 0) (cube 1 t)" using one_dim_cube_eq_nat_set[of t] 
    unfolding bij_betw_def inj_on_def by auto 
  ultimately show "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s) = (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)" 
    using the_inv_into_f_eq [of "\<lambda>f. f 0" "cube 1 t" "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)" s] by auto
qed

lemma dim1_layered_subspace_as_line:
  assumes "t > 0"
    and "layered_subspace S 1 n t r \<chi>"
  shows "\<exists>c1 c2. c1<r \<and> c2<r \<and> (\<forall>s<t. \<chi> (S (SOME p. p\<in>cube 1
  (t+1) \<and> p 0 = s)) = c1) \<and> \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = t)) = c2"
proof -
  have "x u < t" if "x \<in> classes 1 t 0" and "u < 1" for x u 
  proof -
    have "x \<in> cube 1 (t+1)" using that unfolding classes_def by blast
    then have "x u \<in> {..<t+1}" using that unfolding cube_def by blast
    then have "x u \<in> {..<t}" using that
      using that less_Suc_eq unfolding classes_def by auto
    then show "x u < t" by simp
  qed
  then have "classes 1 t 0 \<subseteq> cube 1 t" unfolding cube_def classes_def by auto
  moreover have "cube 1 t \<subseteq> classes 1 t 0" using cube_subset[of 1 t] unfolding cube_def classes_def by auto
  ultimately have X: "classes 1 t 0 = cube 1 t" by blast

  obtain c1 where c1_prop: "c1 < r \<and> (\<forall>x\<in>classes 1 t 0. \<chi> (S x) = c1)" using assms(2) 
    unfolding layered_subspace_def by blast
  then have "(\<chi> (S x) = c1)" if "x \<in> cube 1 t" for x using X that by blast
  then have "\<chi> (S (the_inv_into (cube 1 t) (\<lambda>f. f 0) s)) = c1" if "s < t" for s 
    using one_dim_cube_eq_nat_set[of t] by (meson that bij_betwE bij_betw_the_inv_into lessThan_iff)
  then have K1: "\<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) = c1" if "s < t" for s 
    using that some_inv_into_2 by simp

  have *: "\<exists>c<r. \<forall>x \<in> classes 1 t 1. \<chi> (S x) = c" 
    using assms(2) unfolding layered_subspace_def by blast

  have "x 0 = t" if "x \<in> classes 1 t 1" for x using that unfolding classes_def by simp
  moreover have "\<exists>!x \<in> cube 1 (t+1). x 0 = t" using one_dim_cube_eq_nat_set[of "t+1"] 
    unfolding bij_betw_def inj_on_def using inv_into_cube_props(1) inv_into_cube_props(2) by force 
  moreover have **: "\<exists>!x. x  \<in> classes 1 t 1" unfolding classes_def using calculation(2) by simp
  ultimately have "the_inv_into (cube 1 (t+1)) (\<lambda>f. f 0) t \<in> classes 1 t 1" 
    using inv_into_cube_props[of t "t+1"] unfolding classes_def by simp

  then have "\<exists>c2. c2 < r \<and> \<chi> (S (the_inv_into (cube 1 (t+1)) (\<lambda>f. f 0) t)) = c2" 
    using * ** by blast
  then have K2: "\<exists>c2. c2 < r \<and> \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = t)) = c2" 
    using some_inv_into by simp

  from K1 K2 show ?thesis 
    using c1_prop by blast
qed

lemma dim1_layered_subspace_mono_line: 
  assumes "t > 0" 
    and "layered_subspace S 1 n t r \<chi>"
  shows "\<forall>s<t. \<forall>l<t.  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) =
  \<chi> (S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = l)) \<and>  \<chi> (S (SOME p. p\<in>cube 1
  (t+1) \<and> p 0 = s)) < r"
  using dim1_layered_subspace_as_line[of t S n r \<chi>] assms by auto  

definition join :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat
\<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)"
  where
    "join f g n m \<equiv> (\<lambda>x. if x \<in> {..<n} then f x else (if x \<in> {n..<n+m} then g
    (x - n) else undefined))"

lemma join_cubes: 
  assumes "f \<in> cube n (t+1)" 
    and "g \<in> cube m (t+1)"
  shows "join f g n m \<in> cube (n+m) (t+1)"
proof (unfold cube_def; intro PiE_I)
  fix i
  assume "i \<in> {..<n+m}"
  then consider "i < n" | "i \<ge> n \<and> i < n+m" by fastforce
  then show "join f g n m i \<in> {..<t + 1}"
  proof (cases)
    case 1
    then have "join f g n m i = f i" unfolding join_def by simp
    moreover have "f i \<in> {..<t+1}" using assms(1) 1 unfolding cube_def by blast
    ultimately show ?thesis by simp
  next
    case 2
    then have "join f g n m i = g (i - n)" unfolding join_def by simp
    moreover have "i - n \<in> {..<m}" using 2 by auto
    moreover have "g (i - n) \<in> {..<t+1}" using calculation(2) assms(2) unfolding cube_def by blast
    ultimately show ?thesis by simp
  qed
next
  fix i
  assume "i \<notin> {..<n+m}"
  then show "join f g n m i = undefined" unfolding join_def by simp
qed

lemma subspace_elems_embed: 
  assumes "is_subspace S k n t"
  shows "S ` (cube k t) \<subseteq> cube n t"
  using assms unfolding cube_def is_subspace_def by blast


section \<open>Core proofs\<close>
text\<open>The numbering of the theorems has been borrowed from the textbook~\<^cite>\<open>"thebook"\<close>.\<close>

subsection \<open>Theorem 4\<close>
subsubsection \<open>Base case of Theorem 4\<close>
lemma hj_imp_lhj_base: 
  fixes r t
  assumes "t > 0"
    and "\<And>r'. hj r' t" 
  shows "lhj r t 1"
proof-
  from assms(2) obtain N where N_def: "N > 0 \<and> (\<forall>N' \<ge> N. \<forall>\<chi>. \<chi>
  \<in> (cube N' t) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r.
  is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c)))" unfolding hj_def by blast

  have "(\<exists>S. is_subspace S 1 N' (t + 1) \<and> (\<forall>i \<in> {..1}. \<exists>c < r.
  (\<forall>x \<in> classes 1 t i. \<chi> (S x) = c)))" if asm: "N' \<ge> N" "\<chi> \<in> (cube N'
  (t + 1)) \<rightarrow>\<^sub>E {..<r::nat}" for N' \<chi>
  proof-
    have N'_props: "N' > 0 \<and> (\<forall>\<chi>. \<chi> \<in> (cube N' t) \<rightarrow>\<^sub>E
    {..<r::nat} \<longrightarrow> (\<exists>L. \<exists>c<r. is_line L N' t \<and> (\<forall>y \<in>
    L ` {..<t}. \<chi> y = c)))" using asm N_def by simp
    let ?chi_t = "\<lambda>x \<in> cube N' t. \<chi> x"
    have "?chi_t \<in> cube N' t \<rightarrow>\<^sub>E {..<r::nat}" using cube_subset asm by auto
    then obtain L where L_def: "is_line L N' t \<and> (\<exists>c<r.  (\<forall>y \<in> L ` {..<t}. ?chi_t y = c))" 
      using N'_props by blast

    have "is_subspace (restrict (\<lambda>y. L (y 0)) (cube 1 t)) 1 N' t" using line_is_dim1_subspace N'_props L_def 
      using assms(1) by auto 
    then obtain B f where Bf_defs: "disjoint_family_on B {..1} \<and> \<Union>(B ` {..1}) = {..<N'}
    \<and> ({} \<notin> B ` {..<1}) \<and> f \<in> (B 1) \<rightarrow>\<^sub>E {..<t} \<and>
    (restrict (\<lambda>y. L (y 0)) (cube 1 t)) \<in> (cube 1 t) \<rightarrow>\<^sub>E (cube N' t)
    \<and> (\<forall>y \<in> cube 1 t. (\<forall>i \<in> B 1. (restrict (\<lambda>y. L (y 0)) (cube
    1 t)) y i = f i) \<and> (\<forall>j<1. \<forall>i \<in> B j. ((restrict (\<lambda>y. L (y 0))
    (cube 1 t)) y) i = y j))" unfolding is_subspace_def by auto 

    have "{..1::nat} = {0, 1}" by auto
    then have B_props: "B 0 \<union> B 1 = {..<N'} \<and> (B 0 \<inter> B 1 = {})" 
      using Bf_defs unfolding disjoint_family_on_def by auto
    define L' where "L' \<equiv> L(t:=(\<lambda>j. if j \<in> B 1 then L (t - 1) j else (if j \<in>
    B 0 then t else undefined)))"
    text \<open>\<open>S1\<close> is the corresponding $1$-dimensional subspace of \<open>L'\<close>.\<close>
    define S1 where "S1 \<equiv> restrict (\<lambda>y. L' (y (0::nat))) (cube 1 (t+1))"
    have line_prop: "is_line L' N' (t + 1)"
    proof-
      have A1: "L' \<in> {..<t+1} \<rightarrow>\<^sub>E cube N' (t + 1)" 
      proof
        fix x
        assume asm: "x \<in> {..<t + 1}"
        then show "L' x \<in> cube N' (t + 1)"
        proof (cases "x < t")
          case True
          then have "L' x = L x" by (simp add: L'_def)
          then have "L' x \<in> cube N' t" using L_def True unfolding is_line_def by auto
          then show "L' x \<in> cube N' (t + 1)" using cube_subset by blast
        next
          case False
          then have "x = t" using asm by simp
          show "L' x \<in> cube N' (t + 1)"
          proof(unfold cube_def, intro PiE_I)
            fix j
            assume "j \<in> {..<N'}"
            have "j \<in> B 1 \<or> j \<in> B 0 \<or> j \<notin> (B 0 \<union> B 1)" by blast
            then show "L' x j \<in> {..<t + 1}"
            proof (elim disjE)
              assume "j \<in> B 1"
              then have "L' x j = L (t - 1) j" 
                by (simp add: \<open>x = t\<close> L'_def)
              have "L (t - 1) \<in> cube N' t" using line_points_in_cube L_def 
                by (meson assms(1) diff_less less_numeral_extra(1))
              then have "L (t - 1) j < t" using \<open>j \<in> {..<N'}\<close> unfolding cube_def by auto 
              then show "L' x j \<in> {..<t + 1}" using \<open>L' x j = L (t - 1) j\<close> by simp
            next
              assume "j \<in> B 0"
              then have "j \<notin> B 1" using Bf_defs unfolding disjoint_family_on_def by auto
              then have "L' x j = t"  by (simp add: \<open>j \<in> B 0\<close> \<open>x = t\<close> L'_def)
              then show "L' x j \<in> {..<t + 1}" by simp
            next
              assume a: "j \<notin> (B 0 \<union> B 1)"
              have "{..1::nat} = {0, 1}" by auto
              then have "B 0 \<union> B 1 = (\<Union>(B ` {..1::nat}))" by simp
              then have "B 0 \<union> B 1 = {..<N'}" using Bf_defs unfolding partition_on_def by simp
              then have "\<not>(j \<in> {..<N'})" using a by simp
              then have False using \<open>j \<in> {..<N'}\<close> by simp
              then show ?thesis by simp
            qed
          next
            fix j 
            assume "j \<notin> {..<N'}"
            then have "j \<notin> (B 0) \<and> j \<notin> B 1" using Bf_defs unfolding partition_on_def by auto
            then show "L' x j = undefined" using \<open>x = t\<close> by (simp add: L'_def)
          qed
        qed
      next
        fix x
        assume asm: "x \<notin> {..<t+1}" 
        then have "x \<notin> {..<t} \<and> x \<noteq> t" by simp
        then show "L' x = undefined" using L_def unfolding L'_def is_line_def by auto
      qed
      have A2: "(\<exists>j<N'. (\<forall>s < (t + 1). L' s j = s))"
      proof (cases "t = 1")
        case True
        obtain j where j_prop: "j \<in> B 0 \<and> j < N'" using Bf_defs by blast
        then have "L' s j = L s j" if "s < t" for s using that by (auto simp: L'_def)
        moreover have "L s j = 0" if "s < t" for s  using that True L_def j_prop line_points_in_cube_unfolded[of L N' t]
          by simp
        moreover have "L' s j = s" if "s < t" for s using True calculation that by simp
        moreover have "L' t j = t" using j_prop B_props by (auto simp: L'_def)
        ultimately show ?thesis unfolding L'_def using j_prop by auto
      next
        case False
        then show ?thesis
        proof-
          have "(\<exists>j<N'. (\<forall>s < t. L' s j = s))" using L_def unfolding is_line_def by (auto simp: L'_def)
          then obtain j where j_def: "j < N' \<and> (\<forall>s < t. L' s j = s)" by blast
          have "j \<notin> B 1"
          proof 
            assume a:"j \<in> B 1"
            then have "(restrict (\<lambda>y. L (y 0)) (cube 1 t)) y j = f j" if "y \<in> cube 1 t" for y 
              using Bf_defs that by simp
            then have "L (y 0) j = f j" if "y \<in> cube 1 t" for y using that by simp
            moreover have "\<exists>!i. i < t \<and> y 0 = i" if "y \<in> cube 1 t" for y 
              using that one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def by blast
            moreover have "\<exists>!y. y \<in> cube 1 t \<and> y 0 = i" if "i < t" for i 
            proof (intro ex1I_alt)
              define y where "y \<equiv> (\<lambda>x::nat. \<lambda>y\<in>{..<1::nat}. x)" 
              have "y i \<in> (cube 1 t)" using that unfolding cube_def y_def by simp
              moreover have "y i 0 = i" unfolding y_def by simp
              moreover have "z = y i" if "z \<in> cube 1 t" and "z 0 = i" for z
              proof (rule ccontr)
                assume "z \<noteq> y i" 
                then obtain l where l_prop: "z l \<noteq> y i l" by blast
                consider "l \<in> {..<1::nat}" | "l \<notin> {..<1::nat}" by blast
                then show False
                proof cases
                  case 1
                  then show ?thesis using l_prop that(2) unfolding y_def by auto
                next
                  case 2
                  then have "z l = undefined" using that unfolding cube_def by blast
                  moreover have "y i l = undefined" unfolding y_def using 2 by auto
                  ultimately show ?thesis using l_prop by presburger
                qed
              qed
              ultimately show "\<exists>y. (y \<in> cube 1 t \<and> y 0 = i) \<and> (\<forall>ya. ya
              \<in> cube 1 t \<and> ya 0 = i \<longrightarrow> y = ya)" by blast
            qed

            moreover have "L i j = f j" if "i < t" for i using that calculation by blast
            moreover have "(\<exists>j<N'. (\<forall>s < t. L s j = s))" using
                \<open>(\<exists>j<N'. (\<forall>s < t. L' s j = s))\<close> by (auto simp: L'_def)
            ultimately show False using False
              by (metis (no_types, lifting) L'_def assms(1) fun_upd_apply j_def less_one nat_neq_iff)
          qed
          then have "j \<in> B 0" using \<open>j \<notin> B 1\<close> j_def B_props by auto

          then have "L' t j = t" using \<open>j \<notin> B 1\<close> by (auto simp: L'_def)
          then have "L' s j = s" if "s < t + 1" for s using j_def that by (auto simp: L'_def)
          then show ?thesis using j_def by blast
        qed
      qed
      have A3: "(\<forall>x<t+1. \<forall>y<t+1. L' x j =  L' y j) \<or> (\<forall>s<t+1. L' s j = s)" if "j < N'" for j 
      proof-
        consider "j \<in> B 1" | "j \<in> B 0" using \<open>j < N'\<close> B_props by auto
        then show "(\<forall>x<t+1. \<forall>y<t+1. L' x j =  L' y j) \<or> (\<forall>s<t+1. L' s j = s)"
        proof (cases)
          case 1
          then have "(restrict (\<lambda>y. L (y 0)) (cube 1 t)) y j = f j" if "y \<in> cube 1 t" for y 
            using that Bf_defs by simp
          moreover have "\<exists>!i. i < t \<and> y 0 = i" if "y \<in> cube 1 t" for y 
            using that one_dim_cube_eq_nat_set[of "t"] unfolding bij_betw_def by blast
          moreover have "\<exists>!y. y \<in> cube 1 t \<and> y 0 = i" if "i < t" for i 
          proof (intro ex1I_alt)
            define y where "y \<equiv> (\<lambda>x::nat. \<lambda>y\<in>{..<1::nat}. x)" 
            have "y i \<in> (cube 1 t)" using that unfolding cube_def y_def by simp
            moreover have "y i 0 = i" unfolding y_def by auto
            moreover have "z = y i" if "z \<in> cube 1 t" and "z 0 = i" for z
            proof (rule ccontr)
              assume "z \<noteq> y i" 
              then obtain l where l_prop: "z l \<noteq> y i l" by blast
              consider "l \<in> {..<1::nat}" | "l \<notin> {..<1::nat}" by blast
              then show False
              proof cases
                case 1
                then show ?thesis using l_prop that(2) unfolding y_def by auto
              next
                case 2
                then have "z l = undefined" using that unfolding cube_def by blast
                moreover have "y i l = undefined" unfolding y_def using 2 by auto
                ultimately show ?thesis using l_prop by presburger
              qed
            qed
            ultimately show "\<exists>y. (y \<in> cube 1 t \<and> y 0 = i) \<and> (\<forall>ya. ya
            \<in> cube 1 t \<and> ya 0 = i \<longrightarrow> y = ya)" by blast

          qed
          moreover have "L i j = f j" if "i < t" for i using calculation that by force
          moreover have  "L i j = L x j" if "x < t" "i < t" for x i using that calculation by simp
          moreover have "L' x j = L x j" if "x < t" for x using that fun_upd_other[of x t L
                "\<lambda>j. if j \<in> B 1 then L (t - 1) j else if j \<in> B 0 then t else undefined"]
            unfolding L'_def by simp
          ultimately have *: "L' x j = L' y j" if "x < t" "y < t" for x y using that by presburger

          have "L' t j = L' (t - 1) j" using \<open>j \<in> B 1\<close> by (auto simp: L'_def)
          also have "... = L' x j" if "x < t" for x using * by (simp add: assms(1) that)
          finally have **: "L' t j = L' x j" if "x < t" for x using that by auto
          have "L' x j = L' y j" if "x < t + 1" "y < t + 1" for x y 
          proof-
            consider "x < t \<and> y = t" | "y < t \<and> x = t" | "x = t \<and> y = t" | "x < t \<and> y < t" 
              using \<open>x < t + 1\<close> \<open>y < t + 1\<close> by linarith
            then show "L' x j = L' y j" 
            proof cases
              case 1
              then show ?thesis using ** by auto
            next
              case 2
              then show ?thesis using ** by auto
            next
              case 3
              then show ?thesis by simp
            next
              case 4
              then show ?thesis using * by auto
            qed
          qed
          then show ?thesis by blast
        next
          case 2
          then have "\<forall>y \<in> cube 1 t. ((restrict (\<lambda>y. L (y 0)) (cube 1 t)) y) j = y 0" 
            using \<open>j \<in> B 0\<close> Bf_defs by auto
          then have "\<forall>y \<in> cube 1 t. L (y 0) j = y 0"  by auto
          moreover have "\<exists>!y. y \<in> cube 1 t \<and> y 0 = i" if "i < t" for i 
          proof (intro ex1I_alt)
            define y where "y \<equiv> (\<lambda>x::nat. \<lambda>y\<in>{..<1::nat}. x)" 
            have "y i \<in> (cube 1 t)" using that unfolding cube_def y_def by simp
            moreover have "y i 0 = i" unfolding y_def by auto
            moreover have "z = y i" if "z \<in> cube 1 t" and "z 0 = i" for z
            proof (rule ccontr)
              assume "z \<noteq> y i" 
              then obtain l where l_prop: "z l \<noteq> y i l" by blast
              consider "l \<in> {..<1::nat}" | "l \<notin> {..<1::nat}" by blast
              then show False
              proof cases
                case 1
                then show ?thesis using l_prop that(2) unfolding y_def by auto
              next
                case 2
                then have "z l = undefined" using that unfolding cube_def by blast
                moreover have "y i l = undefined" unfolding y_def using 2 by auto
                ultimately show ?thesis using l_prop by presburger
              qed
            qed
            ultimately show "\<exists>y. (y \<in> cube 1 t \<and> y 0 = i) \<and> (\<forall>ya. ya
            \<in> cube 1 t \<and> ya 0 = i \<longrightarrow> y = ya)" by blast

          qed
          ultimately have "L s j = s" if "s < t" for s using that by blast
          then have "L' s j = s" if "s < t" for s using that by (auto simp: L'_def)
          moreover have "L' t j = t" using 2 B_props by (auto simp: L'_def)
          ultimately have "L' s j = s" if "s < t+1" for s using that by (auto simp: L'_def)
          then show ?thesis by blast
        qed
      qed
      from A1 A2 A3 show ?thesis unfolding is_line_def by simp
    qed
    then have F1: "is_subspace S1 1 N' (t + 1)" unfolding S1_def 
      using line_is_dim1_subspace[of "N'" "t+1"] N'_props assms(1) by force
    moreover have F2: "\<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c)" if "i \<le> 1" for i
    proof-
      have "\<exists>c < r. (\<forall>y \<in> L' ` {..<t}. ?chi_t y = c)" unfolding L'_def using L_def by fastforce
      have "\<forall>x \<in> (L ` {..<t}). x \<in> cube N' t" using L_def 
        using line_points_in_cube by blast
      then have "\<forall>x \<in> (L' ` {..<t}). x \<in> cube N' t" by (auto simp: L'_def)
      then have *:"\<forall>x \<in> (L' ` {..<t}). \<chi> x = ?chi_t x" by simp
      then have "?chi_t ` (L' ` {..<t}) = \<chi> ` (L' ` {..<t})" by force
      then have "\<exists>c < r. (\<forall>y \<in> L' ` {..<t}. \<chi> y = c)" using
          \<open>\<exists>c < r. (\<forall>y \<in> L' ` {..<t}. ?chi_t y = c)\<close> by fastforce
      then obtain linecol where lc_def: "linecol < r \<and> (\<forall>y \<in> L' ` {..<t}. \<chi> y = linecol)" by blast
      consider "i = 0" | "i = 1" using \<open>i \<le> 1\<close> by linarith
      then show "\<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S1 x) = c)"
      proof (cases)
        case 1
        assume "i = 0"
        have *: "\<forall>a t. a \<in> {..<t+1} \<and> a \<noteq> t \<longleftrightarrow> a \<in> {..<(t::nat)}" by auto
        from \<open>i = 0\<close> have "classes 1 t 0 = {x . x \<in> (cube 1 (t + 1)) \<and>
        (\<forall>u \<in> {((1::nat) - 0)..<1}. x u = t) \<and> t \<notin> x ` {..<(1 - (0::nat))}}"
          using classes_def by simp
        also have "... = {x . x \<in> cube 1 (t+1) \<and> t \<notin> x ` {..<(1::nat)}}" by simp
        also have "... = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<noteq> t)}" by blast 
        also have " ... = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<in> {..<t+1} \<and> x 0 \<noteq> t)}" 
          unfolding cube_def by blast
        also have " ... = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<in> {..<t})}" using * by simp
        finally have redef: "classes 1 t 0 = {x . x \<in> cube 1 (t+1) \<and> (x 0 \<in> {..<t})}" by simp
        have "{x 0 | x . x \<in> classes 1 t 0} \<subseteq> {..<t}" using redef by auto
        moreover have "{..<t} \<subseteq> {x 0 | x . x \<in> classes 1 t 0}" 
        proof
          fix x assume x: "x \<in> {..<t}"
          hence "\<exists>a\<in>cube 1 t. a 0 = x"
            unfolding cube_def by (intro fun_ex) auto
          then show "x \<in> {x 0 |x. x \<in> classes 1 t 0}"
            using x cube_subset unfolding redef by auto
        qed
        ultimately have **: "{x 0 | x . x \<in> classes 1 t 0} = {..<t}" by blast

        have "\<chi> (S1 x) = linecol" if "x \<in> classes 1 t 0" for x
        proof-
          have "x \<in> cube 1 (t+1)" unfolding classes_def using that redef by blast
          then have "S1 x = L' (x 0)" unfolding S1_def by simp
          moreover have "x 0 \<in> {..<t}" using ** using \<open>x \<in> classes 1 t 0\<close> by blast
          ultimately show "\<chi> (S1 x) = linecol" using lc_def using fun_upd_triv image_eqI by blast
        qed
        then show ?thesis using lc_def \<open>i = 0\<close> by auto
      next
        case 2 
        assume "i = 1"
        have "classes 1 t 1 = {x . x \<in> (cube 1 (t + 1)) \<and> (\<forall>u \<in> {0::nat..<1}. x
        u = t) \<and> t \<notin> x ` {..<0}}" unfolding classes_def by simp
        also have " ... = {x . x \<in> cube 1 (t+1) \<and> (\<forall>u \<in> {0}. x u = t)}" by simp
        finally have redef: "classes 1 t 1 = {x . x \<in> cube 1 (t+1) \<and> (x 0 = t)}" by auto
        have "\<forall>s \<in> {..<t+1}. \<exists>!x \<in> cube 1 (t+1). (\<lambda>p.
        \<lambda>y\<in>{..<1::nat}. p) s = x" using nat_set_eq_one_dim_cube[of "t+1"] 
          unfolding bij_betw_def by blast
        then have "\<exists>!x \<in>cube 1 (t+1). (\<lambda>p. \<lambda>y\<in>{..<1::nat}. p) t = x" by auto
        then obtain x where x_prop: "x \<in> cube 1 (t+1)" and "(\<lambda>p.
        \<lambda>y\<in>{..<1::nat}. p) t = x" and "\<forall>z \<in> cube 1 (t+1). (\<lambda>p.
        \<lambda>y\<in>{..<1::nat}. p) t = z \<longrightarrow> z = x" by blast
        then have "(\<lambda>p. \<lambda>y\<in>{0}. p)  t  = x \<and> (\<forall>z \<in> cube 1
        (t+1). (\<lambda>p. \<lambda>y\<in>{0}. p) t = z \<longrightarrow> z = x)"  by force
        then have *:"((\<lambda>p. \<lambda>y\<in>{0}. p) t) 0  = x 0 \<and> (\<forall>z \<in> cube
        1 (t+1). (\<lambda>p. \<lambda>y\<in>{0}. p) t  = z  \<longrightarrow> z = x)"  
          using x_prop by force

        then have "\<exists>!y \<in> cube 1 (t + 1). y 0 = t" 
        proof (intro ex1I_alt)
          define y where "y \<equiv> (\<lambda>x::nat. \<lambda>y\<in>{..<1::nat}. x)" 
          have "y t \<in> (cube 1 (t + 1))" unfolding cube_def y_def by simp 
          moreover have "y t 0 = t" unfolding y_def by auto
          moreover have "z = y t" if "z \<in> cube 1 (t + 1)" and "z 0 = t" for z
          proof (rule ccontr)
            assume "z \<noteq> y t" 
            then obtain l where l_prop: "z l \<noteq> y t l" by blast
            consider "l \<in> {..<1::nat}" | "l \<notin> {..<1::nat}" by blast
            then show False
            proof cases
              case 1
              then show ?thesis using l_prop that(2) unfolding y_def by auto
            next
              case 2
              then have "z l = undefined" using that unfolding cube_def by blast
              moreover have "y t l = undefined" unfolding y_def using 2 by auto
              ultimately show ?thesis using l_prop by presburger
            qed
          qed
          ultimately show "\<exists>y. (y \<in> cube 1 (t + 1) \<and> y 0 = t) \<and> (\<forall>ya.
          ya \<in> cube 1 (t + 1) \<and> ya 0 = t \<longrightarrow> y = ya)" by blast
        qed
        then have "\<exists>!x \<in> classes 1 t 1. True" using redef by simp
        then obtain x where x_def: "x \<in> classes 1 t 1 \<and> (\<forall>y \<in> classes 1 t 1. x = y)" by auto

        have "\<chi> (S1 y) < r" if "y \<in> classes 1 t 1" for y
        proof-
          have "y = x" using x_def that by auto
          then have "\<chi> (S1 y) = \<chi> (S1 x)" by auto
          moreover have "S1 x \<in> cube N' (t+1)" unfolding S1_def is_line_def 
            using line_prop line_points_in_cube redef x_def by fastforce
          ultimately show "\<chi> (S1 y) < r" using asm unfolding cube_def by auto
        qed
        then show ?thesis using lc_def \<open>i = 1\<close> using x_def by fast
      qed
    qed
    ultimately show "(\<exists>S. is_subspace S 1 N' (t + 1) \<and> (\<forall>i \<in> {..1}.
    \<exists>c < r. (\<forall>x \<in> classes 1 t i. \<chi> (S x) = c)))" by blast
  qed
  then show ?thesis using N_def unfolding layered_subspace_def lhj_def by auto
qed

subsubsection \<open>Induction step of theorem 4\<close>
text \<open>The proof has four parts:
\begin{enumerate}
\item We obtain two layered subspaces of dimension 1 and k (respectively), whose existence is
guaranteed by the assumption \<^const>\<open>lhj\<close> (i.e.\ the induction hypothesis).
Additionally, we prove some useful facts about these.
\item We construct a \<open>k+1\<close>-dimensional subspace with the goal of showing that it is layered.
\item We prove that our construction is a subspace in the first place.
\item We prove that it is a layered subspace.
\end{enumerate}\<close>

lemma hj_imp_lhj_step: 
  fixes   r k
  assumes "t > 0"
    and "k \<ge> 1"
    and "True" 
    and "(\<And>r k'. k' \<le> k \<Longrightarrow> lhj r t k')" 
    and "r > 0"
  shows   "lhj r t (k+1)"
proof-
  obtain m where m_props: "(m > 0 \<and> (\<forall>M' \<ge> m. \<forall>\<chi>. \<chi> \<in> (cube
  M' (t + 1)) \<rightarrow>\<^sub>E {..<r::nat} \<longrightarrow> (\<exists>S. layered_subspace S k
  M' t r \<chi>)))" using assms(4)[of "k" "r"] unfolding lhj_def  by blast
  define s where "s \<equiv> r^((t + 1)^m)"
  obtain n' where n'_props: "(n' > 0 \<and> (\<forall>N \<ge> n'. \<forall>\<chi>. \<chi> \<in>
  (cube N (t + 1)) \<rightarrow>\<^sub>E {..<s::nat} \<longrightarrow> (\<exists>S. layered_subspace
  S 1 N t s \<chi>)))" using assms(2) assms(4)[of "1" "s"] unfolding lhj_def by auto 

  have "(\<exists>T. layered_subspace T (k + 1) (M') t r \<chi>)" if \<chi>_prop: "\<chi> \<in> cube
  M' (t + 1) \<rightarrow>\<^sub>E {..<r}" and M'_prop: "M' \<ge> n' + m" for \<chi> M'
  proof -
    define d where "d \<equiv> M' - (n' + m)"
    define n where "n \<equiv> n' + d"
    have "n \<ge> n'" unfolding n_def d_def by simp
    have "n + m = M'" unfolding n_def d_def using M'_prop by simp
    have line_subspace_s: "\<exists>S. layered_subspace S 1 n t s \<chi> \<and> is_line
    (\<lambda>s\<in>{..<t+1}. S (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) n (t+1)" if "\<chi>
    \<in> (cube n (t + 1)) \<rightarrow>\<^sub>E {..<s::nat}" for \<chi> 
    proof-
      have "\<exists>S. layered_subspace S 1 n t s \<chi>" using that n'_props \<open>n \<ge> n'\<close> by blast
      then obtain L where "layered_subspace L 1 n t s \<chi>" by blast
      then have "is_subspace L 1 n (t+1)" unfolding layered_subspace_def by simp
      then have "is_line (\<lambda>s\<in>{..<t+1}. L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s)) n (t + 1)" 
        using dim1_subspace_is_line[of "t+1" "L" "n"] assms(1) by simp
      then show "\<exists>S. layered_subspace S 1 n t s \<chi> \<and> is_line (\<lambda>s\<in>{..<t
      + 1}. S (SOME p. p \<in> cube 1 (t+1) \<and> p 0 = s)) n (t + 1)" using
        \<open>layered_subspace L 1 n t s \<chi>\<close> by auto
    qed

    paragraph \<open>Part 1: Obtaining the subspaces \<open>L\<close> and \<open>S\<close>\\\<close>
    text \<open>Recall that @{term lhj} claims the existence of a layered subspace for any colouring
    (of a fixed size, where the size of a colouring refers to the number of colours). Therefore, the
    colourings have to be defined first, before the layered subspaces can be obtained. The colouring
    \<open>\<chi>L\<close> here is $\chi^*$ in the book~\<^cite>\<open>"thebook"\<close>, an
    \<open>s\<close>-colouring; see the fact \<open>s_coloured\<close> a couple of lines
    below.\<close>

    define \<chi>L where "\<chi>L \<equiv> (\<lambda>x \<in> cube n (t+1). (\<lambda>y \<in> cube m
    (t + 1). \<chi> (join x y n m)))"
    have A: "\<forall>x \<in> cube n (t+1). \<forall>y \<in> cube m (t+1). \<chi> (join x y n m) \<in> {..<r}"
    proof(safe)
      fix x y
      assume "x \<in> cube n (t+1)" "y \<in> cube m (t+1)"
      then have "join x y n m \<in> cube (n+m) (t+1)" using join_cubes[of x n t y m] by simp
      then show "\<chi> (join x y n m) < r" using \<chi>_prop \<open>n + m = M'\<close> by blast 
    qed
    have \<chi>L_prop: "\<chi>L \<in> cube n (t+1) \<rightarrow>\<^sub>E cube m (t+1) \<rightarrow>\<^sub>E {..<r}" 
      using A by (auto simp: \<chi>L_def)

    have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = (card {..<r}) ^ (card (cube m (t+1)))" 
      using card_PiE[of "cube m (t + 1)" "\<lambda>_. {..<r}"] by (simp add: cube_def finite_PiE)
    also have "... = r ^ (card (cube m (t+1)))" by simp
    also have "... = r ^ ((t+1)^m)" using cube_card unfolding cube_def by simp
    finally have "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = r ^ ((t+1)^m)" .
    then have s_coloured: "card (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) = s" unfolding s_def by simp
    have "s > 0" using assms(5) unfolding s_def by simp
    then obtain \<phi> where \<phi>_prop: "bij_betw \<phi> (cube m (t+1) \<rightarrow>\<^sub>E {..<r}) {..<s}" 
      using assms(5) ex_bij_betw_nat_finite_2[of "cube m (t+1) \<rightarrow>\<^sub>E {..<r}" "s"] s_coloured by blast
    define \<chi>L_s where "\<chi>L_s \<equiv> (\<lambda>x\<in>cube n (t+1). \<phi> (\<chi>L x))"
    have "\<chi>L_s \<in> cube n (t+1) \<rightarrow>\<^sub>E {..<s}"
    proof
      fix x assume a: "x \<in> cube n (t+1)"
      then have "\<chi>L_s x = \<phi> (\<chi>L x)" unfolding \<chi>L_s_def by simp
      moreover have "\<chi>L x \<in> (cube m (t+1) \<rightarrow>\<^sub>E {..<r})" 
        using a \<chi>L_def \<chi>L_prop unfolding \<chi>L_def by blast
      moreover have "\<phi> (\<chi>L x) \<in> {..<s}" using \<phi>_prop calculation(2) unfolding bij_betw_def by blast
      ultimately show "\<chi>L_s x \<in> {..<s}" by auto
    qed (auto simp: \<chi>L_s_def)
    text \<open>L is the layered line which we obtain from the monochromatic line guaranteed to
    exist by the assumption \<open>hj s t\<close>.\<close>
    then obtain L where L_prop: "layered_subspace L 1 n t s \<chi>L_s" using line_subspace_s by blast
    define L_line where "L_line \<equiv> (\<lambda>s\<in>{..<t+1}. L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s))"
    have L_line_base_prop: "\<forall>s \<in> {..<t+1}. L_line s \<in> cube n (t+1)" 
      using assms(1) dim1_subspace_is_line[of "t+1" "L" "n"] L_prop line_points_in_cube[of L_line n "t+1"] 
      unfolding layered_subspace_def L_line_def by auto

    text \<open>Here, \<open>\<chi>S\<close> is $\chi^{**}$ in the book~\<^cite>\<open>"thebook"\<close>, an r-colouring.\<close>
    define \<chi>S where "\<chi>S \<equiv> (\<lambda>y\<in>cube m (t+1). \<chi> (join (L_line 0) y n m))"
    have "\<chi>S \<in> (cube m (t + 1)) \<rightarrow>\<^sub>E {..<r::nat}"
    proof
    	fix x assume a: "x \<in> cube m (t+1)"
    	then have "\<chi>S x = \<chi> (join (L_line 0) x n m)" unfolding \<chi>S_def by simp
    	moreover have "L_line 0 = L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0)" 
    	  using L_prop assms(1) unfolding L_line_def by simp
    	moreover have "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0) \<in> cube 1 (t+1)" using cube_props(4)[of 0 "t+1"] 
    	  using assms(1) by auto
    	moreover have "L \<in> cube 1 (t+1) \<rightarrow>\<^sub>E cube n (t+1)" 
    	  using L_prop unfolding layered_subspace_def is_subspace_def by blast
    	moreover have "L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = 0) \<in> cube n (t+1)" 
    	  using calculation (3,4) unfolding cube_def by auto
    	moreover have "join (L_line 0) x n m \<in> cube (n + m) (t+1)" using join_cubes a calculation(2, 5) by auto
    	ultimately show "\<chi>S x \<in> {..<r}" using A a by fastforce
    qed (auto simp: \<chi>S_def)
    text \<open>\<open>S\<close> is the $k$-dimensional layered subspace that arises as a
    consequence of the induction hypothesis. Note that the colouring is \<open>\<chi>S\<close>, an
    \<open>r\<close>-colouring.\<close>
    then obtain S where S_prop: "layered_subspace S k m t r \<chi>S" using assms(4) m_props by blast
    text \<open>Remark: \<open>L_Line i\<close> returns the i-th point of the line.\<close>

    paragraph \<open>Part 2: Constructing the $(k+1)$-dimensional subspace \<open>T\<close>\\\<close>

    text \<open>Below, \<open>Tset\<close> is the set as defined in the book~\<^cite>\<open>"thebook"\<close>. It
    represents the $(k+1)$-dimensional subspace. In this construction, subspaces (e.g.
    \<open>T\<close>) are functions whose image is a set. See the fact \<open>im_T_eq_Tset\<close>
    below.\<close>

    text\<open>Having obtained our subspaces \<open>S\<close> and \<open>L\<close>, we define the
    $(k+1)$-dimensional subspace very straightforwardly Namely, T = L \times S. Since we represent
    tuples by function sets, we need an appropriate operator that mirrors the Cartesian product
    $\times$ for these. We call this \<open>join\<close> and define it for elements of a function
    set.\<close> 
    define Tset where "Tset \<equiv> {join (L_line i) s n m | i s . i \<in> {..<t+1} \<and> s \<in> S ` (cube k (t+1))}"
    define T' where "T' \<equiv> (\<lambda>x \<in> cube 1 (t+1). \<lambda>y \<in> cube k (t+1). join
    (L_line (x 0)) (S y) n m)"
    have T'_prop: "T' \<in> cube 1 (t+1) \<rightarrow>\<^sub>E cube k (t+1) \<rightarrow>\<^sub>E cube (n + m) (t+1)"
    proof
      fix x assume a: "x \<in> cube 1 (t+1)"
      show "T' x \<in> cube k (t + 1) \<rightarrow>\<^sub>E cube (n + m) (t + 1)"
      proof
        fix y assume b: "y \<in> cube k (t+1)"
        then have "T' x y = join (L_line (x 0)) (S y) n m" using a unfolding T'_def by simp
        moreover have "L_line (x 0) \<in> cube n (t+1)" using a L_line_base_prop unfolding cube_def by blast
        moreover have "S y \<in> cube m (t+1)" 
          using subspace_elems_embed[of "S" "k" "m" "t+1"] S_prop b unfolding layered_subspace_def by blast
        ultimately show "T' x y \<in> cube (n + m) (t + 1)" using join_cubes by presburger
      next
      qed (unfold T'_def; use a in simp)
   	qed (auto simp: T'_def)

    define T where "T \<equiv> (\<lambda>x \<in> cube (k + 1) (t+1). T' (\<lambda>y \<in> {..<1}. x
    y) (\<lambda>y \<in> {..<k}. x (y + 1)))"
   	have T_prop: "T \<in> cube (k+1) (t+1) \<rightarrow>\<^sub>E cube (n+m) (t+1)"
   	proof
   	  fix x assume a: "x \<in> cube (k+1) (t+1)"
   	  then have "T x = T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1))" unfolding T_def by auto
   	  moreover have "(\<lambda>y \<in> {..<1}. x y) \<in> cube 1 (t+1)" using a unfolding cube_def by auto
   	  moreover have "(\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube k (t+1)" using a unfolding cube_def by auto
   	  moreover have "T' (\<lambda>y \<in> {..<1}. x y) (\<lambda>y \<in> {..<k}. x (y + 1)) \<in> cube (n + m) (t+1)" 
        using T'_prop calculation unfolding T'_def by blast
   	  ultimately show "T x \<in> cube (n + m) (t+1)" by argo
   	qed (auto simp: T_def)

   	have im_T_eq_Tset: "T ` cube (k+1) (t+1) = Tset"
   	proof
   	  show "T ` cube (k + 1) (t + 1) \<subseteq> Tset"
   	  proof
   	    fix x assume "x \<in> T ` cube (k+1) (t+1)"
   	    then obtain y where y_prop: "y \<in> cube (k+1) (t+1) \<and> x = T y" by blast
   	    then have "T y = T' (\<lambda>i \<in> {..<1}. y i) (\<lambda>i \<in> {..<k}. y (i + 1))" unfolding T_def by simp
   	    moreover have "(\<lambda>i \<in> {..<1}. y i) \<in> cube 1 (t+1)" using y_prop unfolding cube_def by auto
   	    moreover have "(\<lambda>i \<in> {..<k}. y (i + 1)) \<in> cube k (t+1)" using y_prop unfolding cube_def by auto
        moreover have " T' (\<lambda>i \<in> {..<1}. y i) (\<lambda>i \<in> {..<k}. y (i + 1)) =
        join (L_line ((\<lambda>i \<in> {..<1}. y i) 0)) (S (\<lambda>i \<in> {..<k}. y (i + 1))) n m" 
          using calculation unfolding T'_def by auto
        ultimately have *: "T y = join (L_line ((\<lambda>i \<in> {..<1}. y i) 0)) 
                                       (S (\<lambda>i \<in> {..<k}. y (i + 1))) n m" by simp

   	    have "(\<lambda>i \<in> {..<1}. y i) 0 \<in> {..<t+1}" using y_prop unfolding cube_def by auto
   	    moreover have "S (\<lambda>i \<in> {..<k}. y (i + 1)) \<in> S ` (cube k (t+1))" 
   	      using \<open>(\<lambda>i\<in>{..<k}. y (i + 1)) \<in> cube k (t + 1)\<close> by blast
   	    ultimately have "T y \<in> Tset" using * unfolding Tset_def by blast
   	    then show "x \<in> Tset" using y_prop by simp
   	  qed

   	  show "Tset \<subseteq> T ` cube (k + 1) (t + 1)" 
   	  proof
   	    fix x assume "x \<in> Tset"
        then obtain i sx sxinv where isx_prop: "x = join (L_line i) sx n m \<and> i \<in> {..<t+1}
        \<and> sx \<in> S ` (cube k (t+1)) \<and> sxinv \<in> cube k (t+1) \<and> S sxinv = sx"
          unfolding Tset_def by blast
   	    let ?f1 = "(\<lambda>j \<in> {..<1::nat}. i)"
   	    let ?f2 = "sxinv"
   	    have "?f1 \<in> cube 1 (t+1)" using isx_prop unfolding cube_def by simp
   	    moreover have "?f2 \<in> cube k (t+1)" using isx_prop by blast
   	    moreover have "x = join (L_line (?f1 0)) (S ?f2) n m" by (simp add: isx_prop)
   	    ultimately have *: "x = T' ?f1 ?f2" unfolding T'_def by simp 

   	    define f where "f \<equiv> (\<lambda>j \<in> {1..<k+1}. ?f2 (j - 1))(0:=i)"
   	    have "f \<in> cube (k+1) (t+1)"
   	    proof (unfold cube_def; intro PiE_I)
   	      fix j assume "j \<in> {..<k+1}"
   	      then consider "j = 0" | "j \<in> {1..<k+1}" by fastforce
   	      then show "f j \<in> {..<t+1}"
   	      proof (cases)
   	        case 1
   	        then have "f j = i" unfolding f_def by simp
   	        then show ?thesis using isx_prop by simp
   	      next
   	        case 2
   	        then have "j - 1 \<in> {..<k}" by auto
   	        moreover have "f j = ?f2 (j - 1)" using 2 unfolding f_def by simp
   	        moreover have "?f2 (j - 1) \<in> {..<t+1}" using calculation(1) isx_prop unfolding cube_def by blast
   	        ultimately show ?thesis by simp
   	      qed
   	    qed (auto simp: f_def)
   	    have "?f1 = (\<lambda>j \<in> {..<1}. f j)" unfolding f_def using isx_prop by auto
   	    moreover have "?f2 = (\<lambda>j\<in>{..<k}. f (j+1))" 
          using calculation isx_prop unfolding cube_def f_def by fastforce
   	    ultimately have "T' ?f1 ?f2 = T f" using \<open>f \<in> cube (k+1) (t+1)\<close> unfolding T_def by simp
   	    then show "x \<in> T ` cube (k + 1) (t + 1)" using * 
   	      using \<open>f \<in> cube (k + 1) (t + 1)\<close> by blast
   	  qed


   	qed
   	have "Tset \<subseteq> cube (n + m) (t+1)"
   	proof
   	  fix x assume a: "x\<in>Tset"
      then obtain i sx where isx_props: "x = join (L_line i) sx n m \<and> i \<in> {..<t+1} \<and>
      sx \<in> S ` (cube k (t+1))" unfolding Tset_def by blast
   	  then have "L_line i \<in> cube n (t+1)" using L_line_base_prop by blast
   	  moreover have "sx \<in> cube m (t+1)" 
        using subspace_elems_embed[of "S" "k" "m" "t+1"] S_prop isx_props unfolding layered_subspace_def by blast
   	  ultimately show "x \<in> cube (n + m) (t+1)" using join_cubes[of "L_line i" "n" "t" sx m] isx_props by simp 
   	qed


   	paragraph \<open>Part 3: Proving that \<open>T\<close> is a subspace\\\<close>

    text \<open>To prove something is a subspace, we have to provide the \<open>B\<close> and \<open>f\<close>
    satisfying the subspace properties. 
    We construct \<open>BT\<close> and \<open>fT\<close> from \<open>BS\<close>, \<open>fS\<close> and
    \<open>BL\<close>, \<open>fL\<close>, which correspond to the $k$-dimensional subspace \<open>S\<close> 
    and the $1$-dimensional subspace (i.e.\ line) \<open>L\<close>, respectively.\<close>
    obtain BS fS where BfS_props: "disjoint_family_on BS {..k}" "\<Union>(BS ` {..k}) = {..<m}" "({}
    \<notin> BS ` {..<k})" " fS \<in> (BS k) \<rightarrow>\<^sub>E {..<t+1}" "S \<in> (cube k (t+1))
    \<rightarrow>\<^sub>E (cube m (t+1)) " "(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> BS k.
    S y i = fS i) \<and> (\<forall>j<k. \<forall>i \<in> BS j. (S y) i = y j))" using S_prop
      unfolding layered_subspace_def is_subspace_def by auto

    obtain BL fL where BfL_props: "disjoint_family_on BL {..1}" "\<Union>(BL ` {..1}) = {..<n}"
      "({} \<notin> BL ` {..<1})" "fL \<in> (BL 1) \<rightarrow>\<^sub>E {..<t+1}" "L \<in> (cube 1
    (t+1)) \<rightarrow>\<^sub>E (cube n (t+1))" "(\<forall>y \<in> cube 1 (t+1). (\<forall>i \<in>
    BL 1. L y i = fL i) \<and> (\<forall>j<1. \<forall>i \<in> BL j. (L y) i = y j))" using L_prop
      unfolding layered_subspace_def is_subspace_def by auto

   	define Bstat where "Bstat \<equiv> set_incr n (BS k) \<union> BL 1"
   	define Bvar where "Bvar \<equiv> (\<lambda>i::nat. (if i = 0 then BL 0 else set_incr n (BS (i - 1))))"
   	define BT where "BT \<equiv> (\<lambda>i \<in> {..<k+1}. Bvar i)((k+1):=Bstat)"
    define fT where "fT \<equiv> (\<lambda>x. (if x \<in> BL 1 then fL x else (if x \<in> set_incr n
    (BS k) then fS (x - n) else undefined)))"

   	have fact1: "set_incr n (BS k) \<inter> BL 1 = {}"  using BfL_props BfS_props unfolding set_incr_def by auto
   	have fact2: "BL 0 \<inter> (\<Union>i\<in>{..<k}. set_incr n (BS i)) = {}" 
      using BfL_props BfS_props unfolding set_incr_def by auto
   	have fact3: "\<forall>i \<in> {..<k}. BL 0 \<inter> set_incr n (BS i) = {}" 
      using BfL_props BfS_props unfolding set_incr_def by auto
    have fact4: "\<forall>i \<in> {..<k+1}. \<forall>j \<in> {..<k+1}. i \<noteq> j
    \<longrightarrow> set_incr n (BS i) \<inter> set_incr n (BS j) = {}" 
      using set_incr_disjoint_family[of BS k] BfS_props unfolding disjoint_family_on_def by simp 
   	have fact5: "\<forall>i \<in> {..<k+1}. Bvar i \<inter> Bstat = {}"
   	proof
   	  fix i assume a: "i \<in> {..<k+1}"
   	  show "Bvar i \<inter> Bstat = {}"
   	  proof (cases i)
   	    case 0
   	    then have "Bvar i = BL 0" unfolding Bvar_def by simp
   	    moreover have "BL 0 \<inter> BL 1 = {}" using BfL_props unfolding disjoint_family_on_def by simp
   	    moreover have "set_incr n (BS k) \<inter> BL 0 = {}" using BfL_props BfS_props unfolding set_incr_def by auto
   	    ultimately show ?thesis unfolding Bstat_def by blast
   	  next
   	    case (Suc nat)
   	    then have "Bvar i = set_incr n (BS nat)" unfolding Bvar_def by simp
   	    moreover have "set_incr n (BS nat) \<inter> BL 1 = {}" using BfS_props BfL_props a Suc unfolding set_incr_def 
          by auto
   	    moreover have "set_incr n (BS nat) \<inter> set_incr n (BS k) = {}" using a Suc fact4 by simp
   	    ultimately show ?thesis unfolding Bstat_def by blast
   	  qed
   	qed

   	text \<open>The facts \<open>F1\<close>, ..., \<open>F5\<close> are the disjuncts in the subspace definition.\<close>
    have "Bvar ` {..<k+1} = BL ` {..<1} \<union> Bvar ` {1..<k+1}" unfolding Bvar_def by force
    also have " ... = BL ` {..<1} \<union> {set_incr n (BS i) | i . i \<in> {..<k}} " unfolding Bvar_def by fastforce  
    moreover have "{} \<notin> BL ` {..<1}" using BfL_props by auto
    moreover have "{} \<notin> {set_incr n (BS i) | i . i \<in> {..<k}}" using BfS_props(2, 3) set_incr_def by fastforce
    ultimately have "{} \<notin> Bvar ` {..<k+1}" by simp
    then have F1: "{} \<notin> BT ` {..<k+1}" unfolding BT_def by simp
    moreover
    {
      have F2_aux: "disjoint_family_on Bvar {..<k+1}"
      proof (unfold disjoint_family_on_def; safe)
        fix m n x assume a: "m < k + 1" "n < k + 1" "m \<noteq> n" "x \<in> Bvar m" "x \<in> Bvar n"
        show "x \<in> {}"
        proof (cases "n")
          case 0
          then show ?thesis using a fact3 unfolding Bvar_def by auto
        next
          case (Suc nnat)
          then have *: "n = Suc nnat" by simp
          then show ?thesis 
          proof (cases m)
            case 0
            then show ?thesis using a fact3 unfolding Bvar_def by auto
          next
            case (Suc mnat)
            then show ?thesis using a fact4  * unfolding Bvar_def by fastforce
          qed
        qed
      qed

      have F2: "disjoint_family_on BT {..k+1}"
      proof
        fix m n assume a: "m\<in>{..k+1}" "n\<in>{..k+1}" "m \<noteq> n"
        have "\<forall>x. x \<in> BT m \<inter> BT n \<longrightarrow> x \<in> {}" 
        proof (intro allI impI)
          fix x assume b: "x \<in> BT m \<inter> BT n"
          have "m < k + 1 \<and> n < k + 1 \<or> m = k + 1 \<and> n = k + 1 \<or> m < k + 1 
          \<and> n = k + 1 \<or> m = k + 1 \<and> n < k + 1" using a le_eq_less_or_eq by auto
          then show "x \<in> {}"
          proof (elim disjE)
            assume c: "m < k + 1 \<and> n < k + 1"
            then have "BT m = Bvar m \<and> BT n = Bvar n" unfolding BT_def by simp
            then show "x \<in> {}" using a b c fact4 F2_aux unfolding Bvar_def disjoint_family_on_def by auto
          qed (use a b fact5 in \<open>auto simp: BT_def\<close>)
        qed
        then show "BT m \<inter> BT n = {}" by auto
      qed
    }
    moreover have F3: "\<Union>(BT ` {..k+1}) = {..<n + m}"
    proof 
      show "\<Union> (BT ` {..k + 1}) \<subseteq> {..<n + m}"
      proof
        fix x assume "x \<in> \<Union> (BT ` {..k + 1})"
        then obtain i where i_prop: "i \<in> {..k+1} \<and> x \<in> BT i" by blast
        then consider "i = k +1" | "i \<in> {..<k+1}" by fastforce
        then show "x \<in> {..<n + m}"
        proof (cases)
          case 1
          then have "x \<in> Bstat" using i_prop unfolding BT_def by simp
          then have "x \<in> BL 1 \<or> x \<in> set_incr n (BS k)" unfolding Bstat_def by blast
          then have "x \<in> {..<n} \<or> x \<in> {n..<n+m}" using BfL_props BfS_props(2) set_incr_image[of BS k m n] 
            by blast
          then show ?thesis by auto
        next
          case 2
          then have "x \<in> Bvar i" using i_prop unfolding BT_def by simp
          then have "x \<in> BL 0 \<or> x \<in> set_incr n (BS (i - 1))" unfolding Bvar_def by presburger
          then show ?thesis
          proof (elim disjE)
            assume "x \<in> BL 0"
            then have "x \<in> {..<n}" using BfL_props by auto
            then show "x \<in> {..<n + m}" by simp
          next
            assume a: "x \<in> set_incr n (BS (i - 1))"
            then have "i - 1 \<le> k" 
              by (meson atMost_iff i_prop le_diff_conv) 
            then have "set_incr n (BS (i - 1)) \<subseteq> {n..<n+m}" using set_incr_image[of BS k m n] BfS_props 
              by auto
            then show "x \<in> {..<n+m}" using a by auto
          qed
        qed
      qed
    next
      show "{..<n + m} \<subseteq> \<Union> (BT ` {..k + 1})"
      proof 
        fix x assume "x \<in> {..<n + m}"
        then consider "x \<in> {..<n}" | "x \<in> {n..<n+m}" by fastforce
        then show "x \<in> \<Union> (BT ` {..k + 1})"
        proof (cases)
          case 1
          have *: "{..1::nat} = {0, 1::nat}" by auto
          from 1 have "x \<in> \<Union> (BL ` {..1::nat})" using BfL_props by simp
          then have "x \<in> BL 0 \<or> x \<in> BL 1" using * by simp
          then show ?thesis 
          proof (elim disjE)
            assume "x \<in> BL 0"
            then have "x \<in> Bvar 0" unfolding Bvar_def by simp
            then have "x \<in> BT 0" unfolding BT_def by simp
            then show "x \<in> \<Union> (BT ` {..k + 1})" by auto
          next
            assume "x \<in> BL 1"
            then have "x \<in> Bstat" unfolding Bstat_def by simp
            then have "x \<in> BT (k+1)" unfolding BT_def by simp
            then show "x \<in> \<Union> (BT ` {..k + 1})" by auto
          qed
        next
          case 2
          then have "x \<in> (\<Union>i\<le>k. set_incr n (BS i))" using set_incr_image[of BS k m n] BfS_props by simp
          then obtain i where i_prop: "i \<le> k \<and> x \<in> set_incr n (BS i)" by blast
          then consider "i = k" | "i < k" by fastforce
          then show ?thesis
          proof (cases)
            case 1
            then have "x \<in> Bstat" unfolding Bstat_def using i_prop by auto
            then have "x \<in> BT (k+1)" unfolding BT_def by simp
            then show ?thesis by auto
          next
            case 2
            then have "x \<in> Bvar (i + 1)" unfolding Bvar_def using i_prop by simp
            then have "x \<in> BT (i + 1)" unfolding BT_def using 2 by force
            then show ?thesis using 2 by auto
          qed
        qed
      qed
    qed

    moreover have F4: "fT \<in> (BT (k+1)) \<rightarrow>\<^sub>E {..<t+1}"
    proof
      fix x assume "x \<in> BT (k+1)"
      then have "x \<in> Bstat" unfolding BT_def by simp
      then have "x \<in> BL 1 \<or> x \<in> set_incr n (BS k)" unfolding Bstat_def by auto
      then show "fT x \<in> {..<t + 1}"
      proof (elim disjE)
        assume "x \<in> BL 1"
        then have "fT x = fL x" unfolding fT_def by simp
        then show "fT x \<in> {..<t+1}" using BfL_props \<open>x \<in> BL 1\<close> by auto
      next
        assume a: "x \<in> set_incr n (BS k)"
        then have "fT x = fS (x - n)" using fact1 unfolding fT_def by auto
        moreover have "x - n \<in> BS k" using a unfolding set_incr_def by auto
        ultimately show "fT x \<in> {..<t+1}" using BfS_props by auto
      qed
    qed(auto simp: BT_def Bstat_def fT_def)
    moreover have F5: "((\<forall>i \<in> BT (k + 1). T y i = fT i) \<and> (\<forall>j<k+1.
    \<forall>i \<in> BT j. (T y) i = y j))" if "y \<in> cube (k + 1) (t + 1)" for y
    proof(intro conjI allI impI ballI)
      fix i assume "i \<in> BT (k + 1)"
      then have "i \<in> Bstat" unfolding BT_def by simp
      then consider "i \<in> set_incr n (BS k)" |  "i \<in> BL 1" unfolding Bstat_def by blast
      then show "T y i = fT i"
      proof (cases)
        case 1
        then have "\<exists>s<m. i = n + s" unfolding set_incr_def using BfS_props(2) by auto
        then obtain s where s_prop: "s < m \<and> i = n + s" by blast
        then have *: " i \<in> {n..<n+m}" by simp
        have "i \<notin> BL 1" using 1 fact1 by auto
        then have "fT i = fS (i - n)" using 1 unfolding fT_def by simp
        then have **: "fT i = fS s" using s_prop by simp

        have XX: "(\<lambda>z \<in> {..<k}. y (z + 1)) \<in> cube k (t+1)" using split_cube that by simp
        have XY: "s \<in> BS k" using  s_prop  1 unfolding set_incr_def by auto

        from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" 
          unfolding T_def by auto
        also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in>
        {..<k}. y (z + 1))) n m) i" using split_cube that unfolding T'_def by simp
        also have "... = (join (L_line (y 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" by simp
        also have "... = (S (\<lambda>z \<in> {..<k}. y (z + 1))) s" using * s_prop unfolding join_def by simp
        also have "... = fS s" using XX XY BfS_props(6) by blast
        finally show ?thesis using ** by simp
      next
        case 2
        have XZ: "y 0 \<in> {..<t+1}" using that unfolding cube_def by auto
        have XY: "i \<in> {..<n}" using 2 BfL_props(2) by blast
        have XX: "(\<lambda>z \<in> {..<1}. y z)  \<in> cube 1 (t+1)" using that split_cube by simp

        have some_eq_restrict: "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}.
        y z) 0)) = (\<lambda>z \<in> {..<1}. y z)"
        proof 
          show "restrict y {..<1} \<in> cube 1 (t + 1) \<and> restrict y {..<1} 0 = restrict y {..<1} 0" 
            using XX by simp
        next
          fix p
          assume "p \<in> cube 1 (t+1) \<and> p 0 = restrict y {..<1} 0"
          moreover have "p u = restrict y {..<1} u" if "u \<notin> {..<1}" for u 
            using that calculation XX unfolding cube_def 
            using PiE_arb[of "restrict y {..<1}" "{..<1}" "\<lambda>x. {..<t + 1}" u] 
              PiE_arb[of p "{..<1}" "\<lambda>x. {..<t + 1}" u] by simp
          ultimately show "p = restrict y {..<1}" by auto 
        qed

        from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" 
          unfolding T_def by auto
        also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" 
          using split_cube that unfolding T'_def by simp
        also have "... = (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XY unfolding join_def by simp
        also have "... = L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) i" 
          using XZ unfolding L_line_def by auto
        also have "... = L (\<lambda>z \<in> {..<1}. y z) i" using some_eq_restrict by simp
        also have "... = fL i" using BfL_props(6) XX 2 by blast
        also have "... = fT i" using 2 unfolding fT_def by simp
        finally show ?thesis .
      qed
    next
      fix j i assume "j < k + 1" "i \<in> BT j"
      then have i_prop: "i \<in> Bvar j" unfolding BT_def by auto
      consider "j = 0" | "j > 0" by auto
      then show "T y i = y j"
      proof cases
        case 1
        then have "i \<in> BL 0" using i_prop unfolding Bvar_def by auto
        then have XY: "i \<in> {..<n}" using 1 BfL_props(2) by blast
        have XX: "(\<lambda>z \<in> {..<1}. y z)  \<in> cube 1 (t+1)" using that split_cube by simp
        have XZ: "y 0 \<in> {..<t+1}" using that unfolding cube_def by auto

        have some_eq_restrict: "(SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}.
        y z) 0)) = (\<lambda>z \<in> {..<1}. y z)"
        proof 
          show "restrict y {..<1} \<in> cube 1 (t + 1) \<and> restrict y {..<1} 0 = restrict y {..<1} 0" using XX by simp
        next
          fix p
          assume "p \<in> cube 1 (t+1) \<and> p 0 = restrict y {..<1} 0"
          moreover have "p u = restrict y {..<1} u" if "u \<notin> {..<1}" for u 
            using that calculation XX unfolding cube_def 
            using PiE_arb[of "restrict y {..<1}" "{..<1}" "\<lambda>x. {..<t + 1}" u] 
              PiE_arb[of p "{..<1}" "\<lambda>x. {..<t + 1}" u] by simp
          ultimately show "p = restrict y {..<1}" by auto 
        qed

        from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" 
          unfolding T_def by auto
        also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i"
          using split_cube that unfolding T'_def by simp
        also have "... = (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) i" using XY unfolding join_def by simp
        also have "... = L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = ((\<lambda>z \<in> {..<1}. y z) 0)) i" 
          using XZ unfolding L_line_def by auto
        also have "... = L (\<lambda>z \<in> {..<1}. y z) i" using some_eq_restrict by simp
        also have "... =  (\<lambda>z \<in> {..<1}. y z) j" using BfL_props(6) XX 1  \<open>i \<in> BL 0\<close> by blast
        also have "... = (\<lambda>z \<in> {..<1}. y z) 0" using 1 by blast
        also have "... = y 0" by simp
        also have "... = y j" using 1 by simp
        finally show ?thesis .
      next
        case 2
        then have "i \<in> set_incr n (BS (j - 1))" using i_prop unfolding Bvar_def by simp
        then have "\<exists>s<m. n + s = i" using BfS_props(2) \<open>j < k + 1\<close> unfolding set_incr_def by force 
        then obtain s where s_prop: "s < m" "i = s + n" by auto
        then have *: " i \<in> {n..<n+m}" by simp

        have XX: "(\<lambda>z \<in> {..<k}. y (z + 1)) \<in> cube k (t+1)" using split_cube that by simp
        have XY: "s \<in> BS (j - 1)" using s_prop 2 \<open>i \<in> set_incr n (BS (j - 1))\<close> 
          unfolding set_incr_def by force

        from that have "T y i = (T' (\<lambda>z \<in> {..<1}. y z) (\<lambda>z \<in> {..<k}. y (z + 1))) i" 
          unfolding T_def by auto
        also have "... = (join (L_line ((\<lambda>z \<in> {..<1}. y z) 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" 
          using split_cube that unfolding T'_def by simp
        also have "... = (join (L_line (y 0)) (S (\<lambda>z \<in> {..<k}. y (z + 1))) n m) i" by simp
        also have "... = (S (\<lambda>z \<in> {..<k}. y (z + 1))) s" using * s_prop unfolding join_def by simp
        also have "... = (\<lambda>z \<in> {..<k}. y (z + 1)) (j-1)" 
          using XX XY BfS_props(6) 2 \<open>j < k + 1\<close> by auto
        also have "... = y j" using 2 \<open>j < k + 1\<close> by force
        finally show ?thesis .
      qed
    qed

    ultimately have subspace_T: "is_subspace T (k+1) (n+m) (t+1)" unfolding is_subspace_def using T_prop by metis

    paragraph \<open>Part 4: Proving \<open>T\<close> is layered\\\<close>
    text \<open>The following redefinition of the classes makes proving the layered property easier.\<close>
    define T_class where "T_class \<equiv> (\<lambda>j\<in>{..k}. {join (L_line i) s n m | i s . i
    \<in> {..<t} \<and> s \<in> S ` (classes k t j)})(k+1:= {join (L_line t) (SOME s. s \<in> S `
    (cube m (t+1))) n m})"
    have classprop: "T_class j = T ` classes (k + 1) t j" if j_prop: "j \<le> k" for j
    proof
      show "T_class j \<subseteq> T ` classes (k + 1) t j"
      proof
        fix x assume "x \<in> T_class j"
        from that have "T_class j = {join (L_line i) s n m | i s . i \<in> {..<t} \<and> s \<in> S ` (classes k t j)}" 
          unfolding T_class_def by simp
        then obtain i s where is_defs: "x = join (L_line i) s n m \<and> i < t \<and> s \<in> S ` (classes k t j)" 
          using \<open>x \<in> T_class j\<close> unfolding T_class_def by auto
        moreover have *:"classes k t j \<subseteq> cube k (t+1)" unfolding classes_def by simp
        moreover have "\<exists>!y. y \<in> classes k t j \<and> s = S y" 
          using subspace_inj_on_cube[of S k m "t+1"] S_prop inj_onD[of S "cube k (t+1)"] calculation 
          unfolding layered_subspace_def inj_on_def by blast
        ultimately obtain y where y_prop: "y \<in> classes k t j \<and> s = S y \<and>
        (\<forall>z\<in>classes k t j. s = S z \<longrightarrow> y = z)" by auto

        define p where "p \<equiv> join (\<lambda>g\<in>{..<1}. i) y 1 k"
        have "(\<lambda>g\<in>{..<1}. i) \<in> cube 1 (t+1)" using is_defs unfolding cube_def by simp
        then have p_in_cube: "p \<in> cube (k + 1) (t+1)" 
          using join_cubes[of "(\<lambda>g\<in>{..<1}. i)" 1 t y k] y_prop * unfolding p_def by auto
        then have **: "p 0 = i \<and> (\<forall>l < k. p (l + 1) = y l)" unfolding p_def join_def by simp 

        have "t \<notin> y ` {..<(k - j)}" using y_prop unfolding classes_def by simp
        then have "\<forall>u < k - j. y u \<noteq> t" by auto
        then have "\<forall>u < k - j. p (u + 1) \<noteq> t" using ** by simp
        moreover have "p 0 \<noteq> t" using is_defs ** by simp
        moreover have "\<forall>u < k - j + 1. p u \<noteq> t" 
          using calculation by (auto simp: algebra_simps less_Suc_eq_0_disj)
        ultimately have "\<forall>u < (k + 1) - j. p u \<noteq> t" using that by auto
        then have A1: "t \<notin> p ` {..<((k+1) - j)}" by blast


        have "p u = t" if "u \<in> {k - j + 1..<k+1}" for u 
        proof -
          from that have "u - 1 \<in> {k - j..<k}" by auto
          then have "y (u - 1) = t" using y_prop unfolding classes_def by blast
          then show "p u = t" using ** that \<open>u - 1 \<in> {k - j..<k}\<close> by auto
        qed
        then have A2: "\<forall>u\<in>{(k+1) - j..<k+1}. p u = t" using that by auto

        from A1 A2 p_in_cube have "p \<in> classes (k+1) t j" unfolding classes_def by blast

        moreover have "x = T p"
        proof-
          have loc_useful:"(\<lambda>y \<in> {..<k}. p (y + 1)) = (\<lambda>z \<in> {..<k}. y z)" using ** by auto
          have "T p = T' (\<lambda>y \<in> {..<1}. p y) (\<lambda>y \<in> {..<k}. p (y + 1))" 
            using p_in_cube unfolding T_def by auto

          have "T' (\<lambda>y \<in> {..<1}. p y) (\<lambda>y \<in> {..<k}. p (y + 1)) 
                = join (L_line ((\<lambda>y \<in> {..<1}. p y) 0)) (S (\<lambda>y \<in> {..<k}. p (y + 1))) n m" 
            using split_cube p_in_cube unfolding T'_def by simp
          also have "... = join (L_line (p 0)) (S (\<lambda>y \<in> {..<k}. p (y + 1))) n m" by simp
          also have "... = join (L_line i) (S (\<lambda>y \<in> {..<k}. p (y + 1))) n m" by (simp add: **)
          also have "... = join (L_line i) (S (\<lambda>z \<in> {..<k}. y z)) n m" using loc_useful by simp
          also have "... = join (L_line i) (S y) n m" using y_prop * unfolding cube_def by auto
          also have "... = x" using is_defs y_prop by simp
          finally show "x = T p" 
            using \<open>T p = T' (restrict p {..<1}) (\<lambda>y\<in>{..<k}. p (y + 1))\<close> by presburger
        qed
        ultimately show "x \<in> T ` classes (k + 1) t j" by blast
      qed
    next
      show "T ` classes (k + 1) t j \<subseteq> T_class j"
      proof
        fix x assume "x \<in> T ` classes (k+1) t j"
        then obtain y where y_prop: "y \<in> classes (k+1) t j \<and> T y = x" by blast
        then have y_props: "(\<forall>u \<in> {((k+1)-j)..<k+1}. y u = t) \<and> t \<notin> y ` {..<(k+1) - j }" 
          unfolding classes_def by blast

        define z where "z \<equiv> (\<lambda>v \<in> {..<k}. y (v+1))" 
        have "z \<in> cube k (t+1)" using  y_prop classes_subset_cube[of "k+1" t j] unfolding z_def cube_def by auto
        moreover
        {
          have "z ` {..<k - j} = y ` ((+) 1 ` {..<k-j}) "  unfolding z_def by fastforce
          also have "... = y ` {1..<k-j+1}" by (simp add: atLeastLessThanSuc_atLeastAtMost image_Suc_lessThan)
          also have "... = y ` {1..<(k+1)-j}" using j_prop by auto
          finally have "z ` {..<k - j} \<subseteq> y ` {..<(k+1)-j}" by auto
          then have "t \<notin> z ` {..<k - j}" using y_props by blast

        }
        moreover have "\<forall>u \<in> {k-j..<k}. z u = t" unfolding z_def using y_props by auto
        ultimately have z_in_classes: "z \<in> classes k t j" unfolding classes_def by blast

        have "y 0 \<noteq> t"
        proof-
          from that have "0 \<in> {..<k + 1 - j}" by simp
          then show "y 0 \<noteq> t" using y_props by blast
        qed
        then have tr: "y 0 < t" using y_prop classes_subset_cube[of "k+1" t j] unfolding cube_def by fastforce

        have "(\<lambda>g \<in> {..<1}. y g) \<in> cube 1 (t+1)" 
          using y_prop classes_subset_cube[of "k+1" t j] cube_restrict[of 1 "(k+1)" y "t+1"] assms(2) by auto
        then have "T y = T' (\<lambda>g \<in> {..<1}. y g) z" using y_prop classes_subset_cube[of "k+1" t j] 
          unfolding T_def z_def by auto
        also have " ... = join (L_line ((\<lambda>g \<in> {..<1}. y g) 0)) (S z) n m" 
          unfolding T'_def 
          using \<open>(\<lambda>g \<in> {..<1}. y g) \<in> cube 1 (t+1)\<close> \<open>z \<in> cube k (t+1)\<close> 
          by auto
        also have " ... = join (L_line (y 0)) (S z) n m" by simp
        also have " ... \<in> T_class j" using tr z_in_classes that unfolding T_class_def by force
        finally show "x \<in> T_class j" using y_prop by simp
      qed
    qed

    text \<open>The core case $i \leq k$. The case $i = k+1$ is trivial since $k+1$ has only one point.\<close>
    have "\<chi> x = \<chi> y \<and> \<chi> x < r" if a: "i \<le> k" "x \<in> T ` classes (k+1) t i"
      "y \<in> T ` classes (k+1) t i" for i x y
    proof-
      from a have *: "T ` classes (k+1) t i = T_class i" by (simp add: classprop)
      then have  "x \<in> T_class i " using that by simp
      moreover have **: "T_class i = {join (L_line l) s n m | l s . l \<in> {..<t} \<and> s \<in> S ` (classes k t i)}" 
        using a unfolding T_class_def by simp
      ultimately obtain xs xi where xdefs: "x = join (L_line xi) xs n m \<and> xi < t \<and> xs \<in> S ` (classes k t i)"
        by blast

      from * ** obtain ys yi where ydefs: "y = join (L_line yi) ys n m \<and> yi < t \<and> ys \<in> S ` (classes k t i)"
        using a by auto

      have "(L_line xi) \<in> cube n (t+1)" using L_line_base_prop xdefs by simp
      moreover have "xs \<in> cube m (t+1)" 
        using xdefs S_prop subspace_elems_embed imageE image_subset_iff mem_Collect_eq 
        unfolding layered_subspace_def classes_def by blast
      ultimately have AA1: "\<chi> x = \<chi>L (L_line xi) xs" using xdefs unfolding \<chi>L_def by simp

      have "(L_line yi) \<in> cube n (t+1)" using L_line_base_prop ydefs by simp
      moreover have "ys \<in> cube m (t+1)" 
        using ydefs S_prop subspace_elems_embed imageE image_subset_iff mem_Collect_eq 
        unfolding layered_subspace_def classes_def by blast
      ultimately have AA2: "\<chi> y = \<chi>L (L_line yi) ys" using ydefs unfolding \<chi>L_def by simp

      have "\<forall>s<t. \<forall>l < t. \<chi>L_s (L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = s))
      = \<chi>L_s (L (SOME p. p\<in>cube 1 (t+1) \<and> p 0 = l))" using
        dim1_layered_subspace_mono_line[of t L n s \<chi>L_s] L_prop assms(1) by blast
      then have key_aux: "\<chi>L_s (L_line s) = \<chi>L_s (L_line l)" if "s \<in> {..<t}" "l \<in> {..<t}" for s l 
        using that unfolding L_line_def 
        by (metis (no_types, lifting) add.commute 
            lessThan_iff less_Suc_eq plus_1_eq_Suc restrict_apply)
      have key: "\<chi>L (L_line s) = \<chi>L (L_line l)" if "s < t" "l < t" for s l
      proof-
        have L1: "\<chi>L (L_line s) \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}" unfolding \<chi>L_def 
          using A L_line_base_prop \<open>s < t\<close> by simp
        have L2: "\<chi>L (L_line l) \<in> cube m (t + 1) \<rightarrow>\<^sub>E {..<r}" unfolding \<chi>L_def 
          using A L_line_base_prop \<open>l < t\<close> by simp
        have "\<phi> (\<chi>L (L_line s)) = \<chi>L_s (L_line s)" unfolding \<chi>L_s_def 
          using \<open>s < t\<close> L_line_base_prop by simp
        also have " ... =  \<chi>L_s (L_line l)" using key_aux \<open>s <t\<close> \<open>l < t\<close> by blast
        also have " ... = \<phi> (\<chi>L (L_line l))" unfolding \<chi>L_s_def using L_line_base_prop \<open>l<t\<close>
          by simp
        finally have "\<phi> (\<chi>L (L_line s)) = \<phi> (\<chi>L (L_line l))" by simp
        then show "\<chi>L (L_line s) = \<chi>L (L_line l)" 
          using \<phi>_prop L_line_base_prop L1 L2 unfolding bij_betw_def inj_on_def by blast
      qed
      then have "\<chi>L (L_line xi) xs = \<chi>L (L_line 0) xs" using xdefs assms(1) by metis
      also have " ... =  \<chi>S xs" unfolding \<chi>S_def \<chi>L_def using xdefs L_line_base_prop by auto
      also have " ... = \<chi>S ys" using xdefs ydefs layered_eq_classes[of S k m t r \<chi>S] S_prop a by blast
      also have " ... = \<chi>L (L_line 0) ys"  unfolding \<chi>S_def \<chi>L_def using xdefs L_line_base_prop 
        by auto
      also have " ... = \<chi>L (L_line yi) ys" using ydefs key assms(1) by metis
      finally have core_prop: "\<chi>L (L_line xi) xs =  \<chi>L (L_line yi) ys" by simp
      then have "\<chi> x = \<chi> y" using AA1 AA2 by simp      
      then show " \<chi> x = \<chi> y \<and> \<chi> x < r" 
        using xdefs AA1 key assms(1) A 
          \<open>L_line xi \<in> cube n (t + 1)\<close> \<open>xs \<in> cube m (t + 1)\<close> by blast
    qed
    then have "\<exists>c<r. \<forall>x \<in> T ` classes (k+1) t i. \<chi> x = c" if "i \<le> k" for i
      using that assms(5) by blast

    moreover have "\<exists>c<r. \<forall>x \<in> T ` classes (k+1) t (k+1). \<chi> x = c"
    proof -
      have "\<forall>x \<in> classes (k+1) t (k+1). \<forall>u < k + 1. x u = t" unfolding classes_def by auto
      have "(\<lambda>u. t) ` {..<k + 1} \<subseteq> {..<t + 1}" by auto
      then have "\<exists>!y \<in> cube (k+1) (t+1). (\<forall>u < k + 1. y u = t)" 
        using PiE_uniqueness[of "(\<lambda>u. t)" "{..<k+1}" "{..<t+1}"] unfolding cube_def by auto
      then have "\<exists>!y \<in> classes (k+1) t (k+1). (\<forall>u < k + 1. y u = t)" 
        unfolding classes_def using classes_subset_cube[of "k+1" t "k+1"] by auto
      then have "\<exists>!y. y \<in> classes (k+1) t (k+1)" 
        using \<open>\<forall>x \<in> classes (k+1) t (k+1). \<forall>u < k + 1. x u = t\<close> by auto
      have "\<exists>c<r. \<forall>y \<in> classes (k+1) t (k+1). \<chi> (T y) = c" 
      proof -
        have "\<forall>y \<in> classes (k+1) t (k+1). T y \<in> cube (n+m) (t+1)" using T_prop classes_subset_cube
          by blast
        then have "\<forall>y \<in> classes (k+1) t (k+1). \<chi> (T y) < r" using \<chi>_prop 
          unfolding n_def d_def using M'_prop by auto 
        then show "\<exists>c<r. \<forall>y \<in> classes (k+1) t (k+1). \<chi> (T y) = c" 
          using \<open>\<exists>!y. y \<in> classes (k+1) t (k+1)\<close> by blast
      qed
      then show "\<exists>c<r. \<forall>x \<in> T ` classes (k+1) t (k+1). \<chi> x = c" by blast
    qed
    ultimately have "\<exists>c<r. \<forall>x \<in> T ` classes (k+1) t i. \<chi> x = c" if "i \<le> k + 1" for i 
      using that by (metis Suc_eq_plus1 le_Suc_eq)
    then have "\<exists>c<r. \<forall>x \<in> classes (k+1) t i. \<chi> (T x) = c" if "i \<le> k + 1" for i 
      using that by simp
    then have "layered_subspace T (k+1) (n + m) t r \<chi>" using subspace_T that(1) \<open>n + m = M'\<close> 
      unfolding layered_subspace_def by blast
  	then show ?thesis using \<open>n + m = M'\<close> by blast 
  qed
  then show ?thesis unfolding lhj_def 
    using m_props 
      exI[of "\<lambda>M. \<forall>M'\<ge>M. \<forall>\<chi>. \<chi> \<in> cube M' (t + 1)
      \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>S. layered_subspace S (k + 1) M' t r
      \<chi>)" m]
    by blast
qed

theorem hj_imp_lhj: 
  fixes k 
  assumes "\<And>r'. hj r' t" 
  shows "lhj r t k"
proof (induction k arbitrary: r rule: less_induct)
  case (less k)
  consider "k = 0" | "k = 1" | "k \<ge> 2" by linarith
  then show ?case
  proof (cases)
    case 1
    then show ?thesis using dim0_layered_subspace_ex unfolding lhj_def by auto
  next
    case 2
    then show ?thesis
    proof (cases "t > 0")
      case True
      then show ?thesis using hj_imp_lhj_base[of "t"] assms 2 by blast
    next
      case False
      then show ?thesis using assms unfolding hj_def lhj_def cube_def by fastforce
    qed
  next
    case 3
    note less
    then show ?thesis
    proof (cases "t > 0 \<and> r > 0")
    	case True
    	then show ?thesis  using hj_imp_lhj_step[of t "k-1" r]
    	  using assms less.IH 3 One_nat_def Suc_pred by fastforce
    next
      case False
      then consider "t = 0" | "t > 0 \<and> r = 0" | "t = 0 \<and> r = 0" by fastforce
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using assms unfolding hj_def lhj_def cube_def by fastforce
      next
        case 2
        then obtain N where N_props: "N > 0" "\<forall>N'\<ge>N. \<forall>\<chi> \<in> cube N' t
        \<rightarrow>\<^sub>E {..<r}. (\<exists>L c. c < r \<and> is_line L N' t \<and> (\<forall>y
        \<in> L ` {..<t}. \<chi> y = c))" using assms[of r] unfolding hj_def by force
        have "cube N' (t + 1) \<rightarrow>\<^sub>E {..<r} = {}" if "N' \<ge> N" for N'
        proof-
          have "cube N' t \<noteq> {}" using N_props(2) that 2 by fastforce  
          then have "cube N' (t + 1) \<noteq> {}" using cube_subset[of N' t] by blast
          then show ?thesis using 2 by blast
        qed
        then show ?thesis unfolding lhj_def using N_props(1) by blast
      next
        case 3
        then have "(\<exists>L c. c < r \<and> is_line L N' t \<and> (\<forall>y \<in> L ` {..<t}. \<chi> y = c))
        \<Longrightarrow> False" for N' \<chi> by blast
        then have False using assms 3 unfolding hj_def cube_def by fastforce
        then show ?thesis by blast
      qed

    qed
  qed
qed


subsection \<open>Theorem 5\<close>

text \<open>We provide a way to construct a monochromatic line in $C^n_{t + 1}$ from a $k$-dimensional $k$-coloured
layered subspace \<open>S\<close> in $C^n_{t + 1}$.
The idea is to rely on the fact that there are $k+1$ classes in \<open>S\<close>, but only $k$ colours. It thus follows
from the Pigeonhole Principle that two classes must share the same colour. The way classes are defined allows for a
straightforward construction of a line with points only from those two classes. Thus we have our monochromatic
line.\<close>
theorem layered_subspace_to_mono_line: 
  assumes "layered_subspace S k n t k \<chi>" 
    and "t > 0"  
  shows "(\<exists>L. \<exists>c<k. is_line L n (t+1) \<and> (\<forall>y \<in> L ` {..<t+1}. \<chi> y = c))"
proof-
  define x where "x \<equiv> (\<lambda>i\<in>{..k}. \<lambda>j\<in>{..<k}. (if j < k - i then 0 else t))"

  have A: "x i \<in> cube k (t + 1)" if "i \<le> k" for i using that unfolding cube_def x_def by simp
  then have "S (x i) \<in> cube n (t+1)" if "i \<le> k" for i using that assms(1) 
    unfolding layered_subspace_def is_subspace_def by fast

  have "\<chi> \<in> cube n (t + 1) \<rightarrow>\<^sub>E {..<k}" using assms unfolding layered_subspace_def by linarith
  then have "\<chi> ` (cube n (t+1)) \<subseteq> {..<k}" by blast
  then have "card (\<chi> ` (cube n (t+1))) \<le> card {..<k}" 
    by (meson card_mono finite_lessThan)
  then have *: "card (\<chi> ` (cube n (t+1))) \<le> k" by auto
  have "k > 0" using assms(1) unfolding layered_subspace_def by auto
  have "inj_on x {..k}"
  proof -
    have *:"x i1 (k - i2) \<noteq> x i2 (k - i2)" if "i1 \<le> k" "i2 \<le> k" "i1 \<noteq> i2" "i1 < i2" for i1 i2 
      using that assms(2) unfolding x_def by auto 
    have "\<exists>j<k. x i1 j \<noteq> x i2 j" if "i1 \<le> k" "i2 \<le> k" "i1 \<noteq> i2" for i1 i2
    proof (cases "i1 \<le> i2")
      case True
      then have "k - i2 < k" 
        using \<open>0 < k\<close> that(3) by linarith
      then show ?thesis using that * 
        by (meson True nat_less_le)
    next
      case False
      then have "i2 < i1" by simp
      then show ?thesis using that *[of i2 i1] \<open>k > 0\<close>  
        by (metis diff_less gr_implies_not0 le0 nat_less_le)
    qed
    then have "x i1 \<noteq> x i2" if "i1 \<le> k" "i2 \<le> k" "i1 \<noteq> i2" "i1 < i2" for i1 i2 using that 
      by fastforce
    then show ?thesis unfolding inj_on_def  by (metis atMost_iff linorder_cases)
  qed
  then have "card (x ` {..k}) = card {..k}" using card_image by blast
  then have B: "card (x ` {..k}) = k+1" by simp
  have "x ` {..k} \<subseteq> cube k (t+1)" using A by blast
  then have "S ` x ` {..k} \<subseteq> S ` cube k (t+1)" by fast
  also have "... \<subseteq> cube n (t+1)" 
    by (meson assms(1) layered_subspace_def subspace_elems_embed)
  finally have "S ` x ` {..k} \<subseteq> cube n (t+1)" by blast
  then have "\<chi> ` S ` x ` {..k} \<subseteq> \<chi> ` cube n (t+1)" by auto
  then have "card (\<chi> ` S ` x ` {..k}) \<le> card (\<chi> ` cube n (t+1))" 
    by (simp add: card_mono cube_def finite_PiE)
  also have " ... \<le> k" using * by blast
  also have " ... < k + 1" by auto
  also have " ... = card {..k}" by simp
  also have " ... = card (x ` {..k})" using B by auto
  also have " ... = card (S ` x ` {..k})" 
    using subspace_inj_on_cube[of S k n "t+1"] card_image[of S "x ` {..k}"] 
      inj_on_subset[of S "cube k (t+1)" "x ` {..k}"]  assms(1) \<open>x ` {..k} \<subseteq> cube k (t + 1)\<close> 
    unfolding layered_subspace_def by simp
  finally have "card (\<chi> ` S ` x ` {..k}) < card (S ` x ` {..k})" by blast
  then have "\<not>inj_on \<chi> (S ` x ` {..k})" using pigeonhole[of \<chi> "S ` x ` {..k}"] by blast
  then have "\<exists>a b. a \<in> S ` x ` {..k} \<and> b \<in> S ` x ` {..k} \<and> a \<noteq> b \<and> \<chi> a =
  \<chi> b" unfolding inj_on_def by auto
  then obtain ax bx where ab_props: "ax \<in> S ` x ` {..k} \<and> bx \<in> S ` x ` {..k} \<and> ax \<noteq> bx \<and>
  \<chi> ax = \<chi> bx" by blast
  then have "\<exists>u v. u \<in> {..k} \<and> v \<in> {..k} \<and> u \<noteq> v \<and> \<chi> (S (x u)) = \<chi> (S (x
  v))" by blast
  then obtain u v where uv_props: "u \<in> {..k} \<and> v \<in> {..k} \<and> u < v \<and> \<chi> (S (x u)) 
    = \<chi> (S (x v))" by (metis linorder_cases)

  let ?f = "\<lambda>s. (\<lambda>i \<in> {..<k}. if i < k - v then 0 else (if i < k - u then s else t))"
  define y where "y \<equiv> (\<lambda>s \<in> {..t}. S (?f s))"

  have line1: "?f s \<in> cube k (t+1)" if "s \<le> t" for s unfolding cube_def using that by auto

  have f_cube: "?f j \<in> cube k (t+1)" if "j < t+1" for j using line1 that by simp
  have f_classes_u: "?f j \<in> classes k t u" if j_prop: "j < t" for j
    using that j_prop uv_props f_cube unfolding classes_def by auto
  have f_classes_v: "?f j \<in> classes k t v" if j_prop: "j = t" for j
    using that j_prop uv_props assms(2) f_cube unfolding classes_def by auto

  obtain B f where Bf_props: "disjoint_family_on B {..k}" "\<Union>(B ` {..k}) = {..<n}" "({} \<notin> B ` {..<k})" 
    "f \<in> (B k) \<rightarrow>\<^sub>E {..<t+1}" "S \<in> (cube k (t+1)) \<rightarrow>\<^sub>E (cube n (t+1))" 
    "(\<forall>y \<in> cube k (t+1). (\<forall>i \<in> B k. S y i = f i) \<and> (\<forall>j<k. \<forall>i \<in> B j. 
      (S y) i = y j))" 
      using assms(1) unfolding layered_subspace_def is_subspace_def by auto

  have "y \<in> {..<t+1} \<rightarrow>\<^sub>E cube n (t+1)" unfolding y_def using line1 \<open>S ` cube k (t + 1)
  \<subseteq> cube n (t + 1)\<close> by auto
  moreover have "(\<forall>u<t+1. \<forall>v<t+1. y u j = y v j) \<or> (\<forall>s<t+1. y s j = s)" 
    if j_prop: "j<n" for j 
  proof-
    show "(\<forall>u<t+1. \<forall>v<t+1. y u j = y v j) \<or> (\<forall>s<t+1. y s j = s)"
    proof -
      consider "j \<in> B k" | "\<exists>ii<k. j \<in> B ii" using Bf_props(2) j_prop 
        by (metis UN_E atMost_iff le_neq_implies_less lessThan_iff)
      then have "y a j = y b j \<or> y s j = s" if "a < t + 1" "b < t +1" "s < t +1" for a b s
      proof cases
        case 1
        then have "y a j = S (?f a) j" using that(1) unfolding y_def by auto
        also have " ... = f j" using Bf_props(6) f_cube 1 that(1) by auto
        also have " ... = S (?f b) j" using Bf_props(6) f_cube 1 that(2) by auto
        also have " ... = y b j" using that(2) unfolding y_def by simp
        finally show ?thesis by simp
      next
        case 2
        then obtain ii where ii_prop:" ii < k \<and> j \<in> B ii" by blast
        then consider "ii < k - v" | "ii \<ge> k - v \<and> ii < k - u" | "ii \<ge> k - u \<and> ii < k" using not_less
          by blast
        then show ?thesis
        proof cases
          case 1
          then have "y a j = S (?f a) j" using that(1) unfolding y_def by auto
          also have " ... = (?f a) ii" using Bf_props(6) f_cube that(1) ii_prop by auto
          also have " ... = 0" using 1 by (simp add: ii_prop)
          also have " ... = (?f b) ii" using 1 by (simp add: ii_prop)
          also have " ... = S (?f b) j" using Bf_props(6) f_cube that(2) ii_prop by auto
          also have " ... = y b j" using that(2) unfolding y_def by auto
          finally show ?thesis by simp
        next
          case 2
          then have "y s j = S (?f s) j" using that(3) unfolding y_def by auto
          also have " ... = (?f s) ii" using Bf_props(6) f_cube that(3) ii_prop by auto
          also have " ... = s" using 2 by (simp add: ii_prop)
          finally show ?thesis by simp
        next
          case 3
          then have "y a j = S (?f a) j" using that(1) unfolding y_def by auto
          also have " ... = (?f a) ii" using Bf_props(6) f_cube that(1) ii_prop by auto
          also have " ... = t" using 3 uv_props by auto
          also have " ... = (?f b) ii" using 3 uv_props by auto
          also have " ... = S (?f b) j" using Bf_props(6) f_cube that(2) ii_prop by auto
          also have " ... = y b j" using that(2) unfolding y_def by auto
          finally show ?thesis by simp
        qed
      qed
      then show ?thesis by blast
    qed
  qed
  moreover have "\<exists>j < n. \<forall>s<t+1. y s j = s"
  proof -
    have "k > 0" using uv_props by simp
    have "k - v < k" using uv_props by auto
    have "k - v < k - u" using uv_props by auto
    then have "B (k - v) \<noteq> {}" using Bf_props(3) uv_props by auto
    then obtain j where j_prop: "j \<in> B (k - v) \<and> j < n" using Bf_props(2) uv_props by force
    then have "y s j = s" if "s<t+1" for s
    proof
      have "y s j = S (?f s) j" using that unfolding y_def by auto
      also have " ... = (?f s) (k - v)" using Bf_props(6) f_cube that j_prop \<open>k - v < k\<close> by fast
      also have " ... = s" using that j_prop \<open>k - v < k - u\<close> by simp
      finally show ?thesis .
    qed
    then show "\<exists>j < n. \<forall>s<t+1. y s j = s" using j_prop by blast
  qed
  ultimately have Z1: "is_line y n (t+1)" unfolding is_line_def by blast
  moreover 
  {
    have k_colour: "\<chi> e < k" if "e \<in> y ` {..<t+1}" for e 
      using \<open>y \<in> {..<t+1} \<rightarrow>\<^sub>E cube n (t + 1)\<close> \<open>\<chi> \<in> cube n (t + 1)
      \<rightarrow>\<^sub>E {..<k}\<close> that by auto
    have "\<chi> e1 = \<chi> e2 \<and> \<chi> e1 < k" if "e1 \<in> y ` {..<t+1}" "e2 \<in> y ` {..<t+1}" for e1 e2 
    proof  
      from that obtain i1 i2 where i_props: "i1 < t + 1" "i2 < t + 1" "e1 = y i1" "e2 = y i2" by blast 
      from i_props(1,2) have "\<chi> (y i1) = \<chi> (y i2)"
      proof (induction i1 i2 rule: linorder_wlog)
        case (le a b)
        then show ?case
        proof (cases "a = b")
          case True
          then show ?thesis by blast
        next
          case False
          then have "a < b" using le by linarith
          then consider "b = t" | "b < t" using le.prems(2) by linarith
          then show ?thesis
          proof cases
            case 1
            then have "y b \<in> S ` classes k t v" 
            proof -
              have "y b = S (?f b)" unfolding y_def using \<open>b = t\<close> by auto
              moreover have "?f b \<in> classes k t v" using \<open>b = t\<close> f_classes_v by blast
              ultimately show "y b \<in> S ` classes k t v" by blast
            qed
            moreover have "x u \<in> classes k t u"
            proof -
              have "x u cord = t" if "cord \<in> {k - u..<k}" for cord using uv_props that unfolding x_def by simp 
              moreover 
              {  
                have "x u cord \<noteq> t" if "cord \<in> {..<k - u}" for cord 
                  using uv_props that assms(2) unfolding x_def by auto
                then have "t \<notin> x u ` {..<k - u}" by blast
              }
              ultimately show "x u \<in> classes k t u" unfolding classes_def 
                using \<open>x ` {..k} \<subseteq> cube k (t + 1)\<close> uv_props by blast
            qed
            moreover have "x v \<in> classes k t v"
            proof -
              have "x v cord = t" if "cord \<in> {k - v..<k}" for cord using uv_props that unfolding x_def by simp 
              moreover 
              {  
                have "x v cord \<noteq> t" if "cord \<in> {..<k - v}" for cord 
                  using uv_props that assms(2) unfolding x_def by auto
                then have "t \<notin> x v ` {..<k - v}" by blast
              }
              ultimately show "x v \<in> classes k t v" unfolding classes_def 
                using \<open>x ` {..k} \<subseteq> cube k (t + 1)\<close> uv_props by blast
            qed
            moreover have "\<chi> (y b) = \<chi> (S (x v))" 
              using assms(1) calculation(1, 3) unfolding layered_subspace_def by (metis imageE uv_props)
            moreover have "y a \<in> S ` classes k t u" 
            proof -
              have "y a = S (?f a)" unfolding y_def using \<open>a < b\<close> 1 by simp
              moreover have "?f a \<in> classes k t u" using \<open>a < b\<close> 1 f_classes_u by blast
              ultimately show "y a \<in> S ` classes k t u" by blast
            qed
            moreover have "\<chi> (y a) = \<chi> (S (x u))" using assms(1) calculation(2, 5) 
              unfolding layered_subspace_def by (metis imageE uv_props)
            ultimately have "\<chi> (y a) = \<chi> (y b)" using uv_props by simp
            then show ?thesis by blast
          next
            case 2
            then have "a < t" using \<open>a < b\<close> less_trans by blast
            then have "y a \<in> S ` classes k t u"
            proof -
              have "y a = S (?f a)" unfolding y_def using \<open>a < t\<close> by auto
              moreover have "?f a \<in> classes k t u" using \<open>a < t\<close> f_classes_u by blast
              ultimately show "y a \<in> S ` classes k t u" by blast
            qed
            moreover have "y b \<in> S ` classes k t u"
            proof -
              have "y b = S (?f b)" unfolding y_def using \<open>b < t\<close> by auto
              moreover have "?f b \<in> classes k t u" using \<open>b < t\<close> f_classes_u by blast
              ultimately show "y b \<in> S ` classes k t u" by blast
            qed
            ultimately have "\<chi> (y a) = \<chi> (y b)" using assms(1) uv_props unfolding layered_subspace_def 
              by (metis imageE)
            then show ?thesis by blast
          qed
        qed
      next
        case (sym a b)
        then show ?case by presburger
      qed
      then show "\<chi> e1 = \<chi> e2" using i_props(3,4) by blast
    qed (use that(1) k_colour in blast)
    then have Z2: "\<exists>c < k. \<forall>e \<in> y ` {..<t+1}. \<chi> e = c"
      by (meson image_eqI lessThan_iff less_add_one)
  }
  ultimately show "\<exists>L c. c < k \<and> is_line L n (t + 1) \<and> (\<forall>y\<in>L ` {..<t + 1}. \<chi> y = c)" 
    by blast

qed

subsection \<open>Corollary 6\<close>
corollary lhj_imp_hj: 
  assumes "(\<And>r k. lhj r t k)" 
    and "t>0" 
  shows "(hj r (t+1))"
  using assms(1)[of r r] assms(2) unfolding lhj_def hj_def using layered_subspace_to_mono_line[of _ r _ t] by metis

subsection \<open>Main result\<close>

subsubsection \<open>Edge cases and auxiliary lemmas\<close>
lemma single_point_line: 
  assumes "N > 0" 
  shows "is_line (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) N 1"
  using assms unfolding is_line_def cube_def by auto

lemma single_point_line_is_monochromatic: 
  assumes "\<chi> \<in> cube N 1 \<rightarrow>\<^sub>E {..<r}" "N > 0" 
  shows "(\<exists>c < r. is_line (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) N 1 \<and> (\<forall>i \<in>
  (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) ` {..<1}. \<chi> i = c))"
proof -
  have "is_line (\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) N 1" using assms(2) single_point_line by blast
  moreover have "\<exists>c < r. \<chi> ((\<lambda>s\<in>{..<1}. \<lambda>a\<in>{..<N}. 0) j) = c" 
    if "(j::nat) < 1" for j using assms line_points_in_cube calculation that unfolding cube_def by blast
  ultimately show ?thesis by auto
qed


lemma hj_r_nonzero_t_0: 
  assumes "r > 0" 
  shows "hj r 0"
proof-
  have "(\<exists>L c. c < r \<and> is_line L N' 0 \<and> (\<forall>y \<in> L ` {..<0::nat}. \<chi> y = c))" 
    if "N' \<ge> 1" "\<chi> \<in> cube N' 0 \<rightarrow>\<^sub>E {..<r}" for N' \<chi> using assms is_line_def that(1) by fastforce
  then show ?thesis unfolding hj_def by auto
qed

text \<open>Any cube over 1 element always has a single point, which also forms the only line in the cube. Since it's a
single point line, it's trivially monochromatic. We show the result for dimension 1.\<close>
lemma hj_t_1: "hj r 1"
  unfolding hj_def 
proof-
  let ?N = 1
  have "\<exists>L c. c < r \<and> is_line L N' 1 \<and> (\<forall>y\<in>L ` {..<1}. \<chi> y = c)" if "N' \<ge> ?N" "\<chi> \<in> cube N' 1 \<rightarrow>\<^sub>E {..<r}" for N' \<chi> 
    using single_point_line_is_monochromatic[of \<chi> N' r] that by force
  then show "\<exists>N>0. \<forall>N'\<ge>N. \<forall>\<chi>. \<chi> \<in> cube N' 1 \<rightarrow>\<^sub>E {..<r} \<longrightarrow> (\<exists>L c. c < r \<and> is_line L N' 1 \<and> (\<forall>y\<in>L ` {..<1}. \<chi> y = c))" 
    by blast
qed

subsubsection \<open>Main theorem\<close>
text \<open>We state the main result \<^prop>\<open>hj r t\<close>. The explanation for the choice of assumption is
offered subsequently.\<close>
theorem hales_jewett:
  assumes "\<not>(r = 0 \<and> t = 0)" 
  shows "hj r t"
  using assms
proof (induction t arbitrary: r)
  case 0
  then show ?case using hj_r_nonzero_t_0[of r] by blast
next
  case (Suc t)
  then show ?case using hj_t_1[of r] hj_imp_lhj[of t] lhj_imp_hj[of t r] by auto
qed
text \<open>We offer a justification for having excluded the special case $r = t = 0$ from the statement of the main
theorem \<open>hales_jewett\<close>. The exclusion is a consequence of the fact that colourings are defined as members
of the function set \<open>cube n t \<rightarrow>\<^sub>E {..<r}\<close>, which for $r = t = 0$ means there's a dummy
colouring \<^term>\<open>\<lambda>x. undefined\<close>, even though \<^prop>\<open>cube n 0 = {}\<close> for $n > 0$.
Hence, in this case, no line exists at all (let alone one monochromatic under the aforementioned colouring). This means
\<^prop>\<open>hj 0 0 \<Longrightarrow> False\<close>---but only because of the quirky behaviour of the FuncSet
\<open>cube n t \<rightarrow>\<^sub>E {..<r}\<close>. This could have been circumvented by letting colourings $\chi$ be
arbitrary functions constraint only by \<^prop>\<open>\<chi> ` cube n t \<subseteq> {..<r}\<close>. We avoided this in
order to have consistency with the cube's definition, for which FuncSets were crucial because the proof heavily relies
on arguments about the cardinality of the cube. he constraint \<^prop>\<open>x ` {..<n} \<subseteq> {..<t}\<close> for
elements \<open>x\<close> of $C^n_t$ would not have sufficed there, as there are infinitely many functions over the
naturals satisfying it.\<close>

end
