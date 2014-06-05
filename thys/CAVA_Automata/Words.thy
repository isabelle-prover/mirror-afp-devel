(* Author: Stefan Merz *)
header {* $\omega$-words *}
theory Words
imports "~~/src/HOL/Library/Infinite_Set"
begin
text {* Note: This theory is copied from Stefan Merz's work. *}

text {*
  Automata recognize languages, which are sets of words. For the
  theory of $\omega$-automata, we are mostly interested in
  $\omega$-words, but it is sometimes useful to reason about
  finite words, too. We are modeling finite words as lists; this
  lets us benefit from the existing library. Other formalizations
  could be investigated, such as representing words as functions
  whose domains are initial intervals of the natural numbers.
*}

subsection {* Type declaration and elementary operations *}

text {*
  We represent $\omega$-words as functions from the natural numbers
  to the alphabet type. Other possible formalizations include
  a coinductive definition or a uniform encoding of finite and
  infinite words, as studied by M\"uller et al.
*}

type_synonym
  'a word = "nat \<Rightarrow> 'a"

definition
  suffix :: "[nat, 'a word] \<Rightarrow> 'a word"
  where "suffix k x \<equiv> \<lambda>n. x (k+n)"

lemma suffix_nth [simp]:
  "(suffix k x) n = x (k+n)"
by (simp add: suffix_def)

lemma suffix_0 [simp]:
  "suffix 0 x = x"
by (simp add: suffix_def)

lemma suffix_suffix [simp]:
  "suffix m (suffix k x) = suffix (k+m) x"
by (rule ext, simp add: suffix_def add_assoc)

(*
text {*
  A finite part of an infinite word can be obtained as the
  result of mapping the word over the desired index interval.
  For now, we do not define a separate constant for this
  construction, as it does not occur very often, and we prefer
  to rely on the proof machinery provided by the standard library.
  However, the standard rewriting rules include the theorem @{text upt_Suc},
  which tends to convert, say, $[i..j]$ into $[i..j(] @ [j]$.
  Since this is (almost) never what we want, we remove the theorem
  from the rule base in effect for this session.
*}
declare upt_Suc [simp del]
*)

text {*
  We can prefix a finite word to an $\omega$-word, and a way
  to obtain an $\omega$-word from a finite, non-empty word is by
  $\omega$-iteration.
*}

definition
  conc :: "['a list, 'a word] \<Rightarrow> 'a word"    ("_/ conc _" [66,65] 65)
  where "w conc x == \<lambda>n. if n < length w then w!n else x (n - length w)"

definition
  iter :: "'a list \<Rightarrow> 'a word"
  where "iter w == if w = [] then undefined else (\<lambda>n. w!(n mod (length w)))"

syntax (xsymbols)
  conc :: "['a list, 'a word] \<Rightarrow> 'a word"    ("_/ \<frown> _" [66,65] 65)
  iter :: "'a list \<Rightarrow> 'a word"               ("(_\<^sup>\<omega>)" [1000])

lemma conc_empty[simp]: "[] \<frown> w = w"
  unfolding conc_def by auto

lemma conc_fst:
  "n < length w \<Longrightarrow> (w \<frown> x) n = w!n"
by (simp add: conc_def)

lemma conc_snd:
  "\<not>(n < length w) \<Longrightarrow> (w \<frown> x) n = x (n - length w)"
by (simp add: conc_def)

lemma iter_nth [simp]:
  "0 < length w \<Longrightarrow> w\<^sup>\<omega> n = w!(n mod (length w))"
by (simp add: iter_def)

lemma conc_conc:
  "u \<frown> v \<frown> w = (u @ v) \<frown> w" (is "?lhs = ?rhs")
proof
  fix n
  have u: "n < length u \<Longrightarrow> ?lhs n = ?rhs n"
    by (simp add: conc_def nth_append)
  have v: "\<lbrakk> \<not>(n < length u); n < length u + length v \<rbrakk> \<Longrightarrow> ?lhs n = ?rhs n"
    by (simp add: conc_def nth_append, arith)
  have w: "\<not>(n < length u + length v) \<Longrightarrow> ?lhs n = ?rhs n"
    by (simp add: conc_def nth_append, arith)
  from u v w show "?lhs n = ?rhs n" by auto
qed

lemma prefix_suffix: 
  "x = (map x [0..<n] ) \<frown> (suffix n x)"
by (rule ext, simp add: conc_def)

lemma iter_unroll:
  "0 < length w \<Longrightarrow> w\<^sup>\<omega> = w \<frown> w\<^sup>\<omega>"
by (rule ext, simp add: conc_def mod_geq)

subsection {* The limit set of an $\omega$-word *}

text {*
  The limit set (also called infinity set) of an $\omega$-word
  is the set of letters that appear infinitely often in the word.
  This set plays an important role in defining acceptance conditions
  of $\omega$-automata.
*}

definition
  limit :: "'a word \<Rightarrow> 'a set"
  where "limit x \<equiv> { a . \<exists>\<^sub>\<infinity>n . x n = a }"

lemma limit_iff_frequent:
  "(a \<in> limit x) = (\<exists>\<^sub>\<infinity>n . x n = a)"
by (simp add: limit_def)

text {*
  The following is a different way to define the limit,
  using the reverse image, making the laws about reverse
  image applicable to the limit set. 
  (Might want to change the definition above?)
*}

lemma limit_vimage:
  "(a \<in> limit x) = infinite (x -` {a})"
by (simp add: limit_def Inf_many_def vimage_def)

lemma two_in_limit_iff:
  "({a,b} \<subseteq> limit x) = 
   ((\<exists>n. x n =a ) \<and> (\<forall>n. x n = a \<longrightarrow> (\<exists>m>n. x m = b)) \<and> (\<forall>m. x m = b \<longrightarrow> (\<exists>n>m. x n = a)))"
  (is "?lhs = (?r1 \<and> ?r2 \<and> ?r3)")
proof
  assume lhs: "?lhs"
  hence 1: "?r1" by (auto simp: limit_def elim: INFM_EX)
  from lhs have "\<forall>n. \<exists>m>n. x m = b" by (auto simp: limit_def INFM_nat)
  hence 2: "?r2" by simp
  from lhs have "\<forall>m. \<exists>n>m. x n = a" by (auto simp: limit_def INFM_nat)
  hence 3: "?r3" by simp
  from 1 2 3 show "?r1 \<and> ?r2 \<and> ?r3" by simp
next
  assume "?r1 \<and> ?r2 \<and> ?r3"
  hence 1: "?r1" and 2: "?r2" and 3: "?r3" by simp+
  have infa: "\<forall>m. \<exists>n\<ge>m. x n = a"
  proof
    fix m
    show "\<exists>n\<ge>m. x n = a" (is "?A m")
    proof (induct m)
      from 1 show "?A 0" by simp
    next
      fix m
      assume ih: "?A m"
      then obtain n where n: "n \<ge> m" "x n = a" by auto
      with 2 obtain k where k: "k>n" "x k = b" by auto
      with 3 obtain l where l: "l>k" "x l = a" by auto
      from n k l have "l \<ge> Suc m" by auto
      with l show "?A (Suc m)" by auto
    qed
  qed
  hence infa': "\<exists>\<^sub>\<infinity>n. x n = a" by (simp add: INFM_nat_le)
  have "\<forall>n. \<exists>m>n. x m = b"
  proof
    fix n
    from infa obtain k where k1: "k\<ge>n" and k2: "x k = a" by auto
    from 2 k2 obtain l where l1: "l>k" and l2: "x l = b" by auto
    from k1 l1 have "l > n" by auto
    with l2 show "\<exists>m>n. x m = b" by auto
  qed
  hence "\<exists>\<^sub>\<infinity>m. x m = b" by (simp add: INFM_nat)
  with infa' show "?lhs" by (auto simp: limit_def)
qed

text {*
  For $\omega$-words over a finite alphabet, the limit set is
  non-empty. Moreover, from some position onward, any such word
  contains only letters from its limit set.
*}

lemma limit_nonempty:
  assumes fin: "finite (range x)"
  shows "\<exists>a. a \<in> limit x"
proof -
  from fin obtain a where "a \<in> range x \<and> infinite (x -` {a})"
    by (rule inf_img_fin_domE, auto)
  hence "a \<in> limit x"
    by (auto simp add: limit_vimage)
  thus ?thesis ..
qed

lemmas limit_nonemptyE = limit_nonempty[THEN exE]

lemma limit_inter_INF:
  assumes hyp: "limit w \<inter> S \<noteq> {}"
  shows "\<exists>\<^sub>\<infinity> n. w n \<in> S"
proof -
  from hyp obtain x where "\<exists>\<^sub>\<infinity> n. w n = x" and "x \<in> S"
    by (auto simp add: limit_def)
  thus ?thesis
    by (auto elim: INFM_mono)
qed

text {*
  The reverse implication is true only if $S$ is finite.
*}

lemma INF_limit_inter:
  assumes hyp: "\<exists>\<^sub>\<infinity> n. w n \<in>  S" and fin: "finite (S \<inter> range w)"
  shows  "\<exists>a. a \<in> limit w \<inter> S"
proof (rule ccontr)
  assume contra: "\<not>(\<exists>a. a \<in> limit w \<inter> S)"
  hence "\<forall>a\<in>S. finite {n. w n = a}"
    by (auto simp add: limit_def Inf_many_def)
  with fin have "finite (UN a:S \<inter> range w. {n. w n = a})"
    by auto
  moreover
  have "(UN a:S \<inter> range w. {n. w n = a}) = {n. w n \<in> S}"
    by auto
  moreover
  note hyp
  ultimately show "False"
    by (simp add: Inf_many_def)
qed

lemma fin_ex_inf_eq_limit: "finite A \<Longrightarrow> (\<exists>\<^sub>\<infinity>i. w i \<in> A) \<longleftrightarrow> limit w \<inter> A \<noteq> {}"
  by (metis INF_limit_inter equals0D finite_Int limit_inter_INF)

lemma limit_in_range_suffix:
  "limit x \<subseteq> range (suffix k x)"
proof
  fix a
  assume "a \<in> limit x"
  then obtain l where
    kl: "k < l" and xl: "x l = a"
    by (auto simp add: limit_def INFM_nat)
  from kl obtain m where "l = k+m"
    by (auto simp add:  less_iff_Suc_add)
  with xl show "a \<in> range (suffix k x)"
    by auto
qed

lemma limit_in_range: "limit r \<subseteq> range r"
  using limit_in_range_suffix[of r 0] by simp

lemmas limit_in_range_suffixD = limit_in_range_suffix[THEN subsetD]

theorem limit_is_suffix:
  assumes fin: "finite (range x)"
  shows "\<exists>k. limit x = range (suffix k x)"
proof -
  have "\<exists>k. range (suffix k x) \<subseteq> limit x"
  proof -
    -- "The set of letters that are not in the limit is certainly finite."
    from fin have "finite (range x - limit x)"
      by simp
    -- "Moreover, any such letter occurs only finitely often"
    moreover
    have "\<forall>a \<in> range x - limit x. finite (x -` {a})"
      by (auto simp add: limit_vimage)
    -- "Thus, there are only finitely many occurrences of such letters."
    ultimately have "finite (UN a : range x - limit x. x -` {a})"
      by (blast intro: finite_UN_I)
    -- "Therefore these occurrences are within some initial interval."
    then obtain k where "(UN a : range x - limit x. x -` {a}) \<subseteq> {..<k}"
      by (blast dest: finite_nat_bounded)
    -- "This is just the bound we are looking for."
    hence "\<forall>m. k \<le> m \<longrightarrow> x m \<in> limit x"
      by (auto simp add: limit_vimage)
    hence "range (suffix k x) \<subseteq> limit x"
      by auto
    thus ?thesis ..
  qed
  then obtain k where "range (suffix k x) \<subseteq> limit x" ..
  with limit_in_range_suffix
  have "limit x = range (suffix k x)"
    by (rule subset_antisym)
  thus ?thesis ..
qed

theorems limit_is_suffixE = limit_is_suffix[THEN exE]


text {*
  The limit set enjoys some simple algebraic laws with respect
  to concatenation, suffixes, iteration, and renaming.
*}

theorem limit_conc [simp]:
  "limit (w \<frown> x) = limit x"
proof (auto)
  fix a assume a: "a \<in> limit (w \<frown> x)"
  have "\<forall>m. \<exists>n. m<n \<and> x n = a"
  proof
    fix m
    from a obtain n where "m + length w < n \<and> (w \<frown> x) n = a"
      by (auto simp add: limit_def Inf_many_def infinite_nat_iff_unbounded)
    hence "m < n - length w \<and> x (n - length w) = a"
      by (auto simp add: conc_def)
    thus "\<exists>n. m<n \<and> x n = a" ..
  qed
  hence "infinite {n . x n = a}"
    by (simp add: infinite_nat_iff_unbounded)
  thus "a \<in> limit x"
    by (simp add: limit_def Inf_many_def)
next
  fix a assume a: "a \<in> limit x"
  have "\<forall>m. length w < m \<longrightarrow> (\<exists>n. m<n \<and> (w \<frown> x) n = a)"
  proof (clarify)
    fix m
    assume m: "length w < m"
    with a obtain n where "m - length w < n \<and> x n = a"
      by (auto simp add: limit_def Inf_many_def infinite_nat_iff_unbounded)
    with m have "m < n + length w \<and> (w \<frown> x) (n + length w) = a"
      by (simp add: conc_def, arith)
    thus "\<exists>n. m<n \<and> (w \<frown> x) n = a" ..
  qed
  hence "infinite {n . (w \<frown> x) n = a}"
    by (simp add: unbounded_k_infinite)
  thus "a \<in> limit (w \<frown> x)"
    by (simp add: limit_def Inf_many_def)
qed

theorem limit_suffix [simp]: 
  "limit (suffix n x) = limit x"
proof -
  have "x = (map x [0..<n]) \<frown> (suffix n x)"
    by (simp add: prefix_suffix)
  hence "limit x = limit ((map x [0..<n]) \<frown> suffix n x)"
    by simp
  also have "\<dots> = limit (suffix n x)"
    by (rule limit_conc)
  finally show ?thesis
    by (rule sym)
qed

theorem limit_iter [simp]:
  assumes nempty: "0 < length w"
  shows "limit w\<^sup>\<omega> = set w"
proof
  have "limit w\<^sup>\<omega> \<subseteq> range w\<^sup>\<omega>"
    by (auto simp add: limit_def dest: INFM_EX)
  also from nempty have "\<dots> \<subseteq> set w"
    by auto
  finally show "limit w\<^sup>\<omega> \<subseteq> set w" .
next
  {
    fix a assume a: "a \<in> set w"
    then obtain k where k: "k < length w \<and> w!k = a"
      by (auto simp add: set_conv_nth)
    -- "the following bound is terrible, but it simplifies the proof"
    from nempty k
    have "\<forall>m. w\<^sup>\<omega> ((Suc m)*(length w) + k) = a"
      by (simp add: mod_add_left_eq)
    moreover
    -- "why is the following so hard to prove??"
    have "\<forall>m. m < (Suc m)*(length w) + k"
    proof
      fix m
      from nempty have "1 \<le> length w" by arith
      hence "m*1 \<le> m*length w" by simp
      hence "m \<le> m*length w" by simp
      with nempty have "m < length w + (m*length w) + k" by arith
      thus "m < (Suc m)*(length w) + k" by simp
    qed
    moreover note nempty
    ultimately have "a \<in> limit w\<^sup>\<omega>"
      by (auto simp add: limit_iff_frequent INFM_nat)
  }
  then show "set w \<subseteq> limit w\<^sup>\<omega>" by auto
qed

lemma limit_o [simp]:
  assumes a: "a \<in> limit w"
  shows "f a \<in> limit (f \<circ> w)"
proof -
  from a
  have "\<exists>\<^sub>\<infinity>n. w n = a"
    by (simp add: limit_iff_frequent)
  hence "\<exists>\<^sub>\<infinity>n. f (w n) = f a"
    by (rule INFM_mono, simp)
  thus "f a \<in> limit (f \<circ> w)"
    by (simp add: limit_iff_frequent)
qed

text {*
  The converse relation is not true in general: $f(a)$ can be in the
  limit of $f \circ w$ even though $a$ is not in the limit of $w$.
  However, @{text limit} commutes with renaming if the function is
  injective. More generally, if $f(a)$ is the image of only finitely
  many elements, some of these must be in the limit of $w$.
*}

lemma limit_o_inv:
  assumes fin: "finite (f -` {x})" and x: "x \<in> limit (f \<circ> w)"
  shows "\<exists>a \<in> (f -` {x}). a \<in> limit w"
proof (rule ccontr)
  assume contra: "\<not>(\<exists>a \<in> (f -` {x}). a \<in> limit w)"
  -- "hence, every element in the pre-image occurs only finitely often"
  then have "\<forall>a \<in> (f -` {x}). finite {n. w n = a}"
    by (simp add: limit_def Inf_many_def)
  -- "so there are only finitely many occurrences of any such element"
  with fin have "finite (\<Union> a \<in> (f -` {x}). {n. w n = a})"
    by auto
  -- {* these are precisely those positions where $x$ occurs in $f \circ w$ *}
  moreover
  have "(\<Union> a \<in> (f -` {x}). {n. w n = a}) = {n. f(w n) = x}"
    by auto
  ultimately
  -- "so $x$ can occur only finitely often in the translated word"
  have "finite {n. f(w n) = x}"
    by simp
  -- {* \ldots\ which yields a contradiction *}
  with x show "False"
    by (simp add: limit_def Inf_many_def)
qed

theorem limit_inj [simp]:
  assumes inj: "inj f"
  shows "limit (f \<circ> w) = f ` (limit w)"
proof
  show "f ` limit w \<subseteq> limit (f \<circ> w)"
    by auto
next
  show "limit (f \<circ> w) \<subseteq> f ` limit w"
  proof
    fix x
    assume x: "x \<in> limit (f \<circ> w)"
    from inj have "finite (f -` {x})"
      by (blast intro: finite_vimageI)
    with x obtain a where a: "a \<in> (f -` {x}) \<and> a \<in> limit w"
      by (blast dest: limit_o_inv)
    thus "x \<in> f ` (limit w)"
      by auto
  qed
qed

subsection {* Index sequences and piecewise definitions *}

text {*
  A word can be defined piecewise: given a sequence of words $w_0, w_1, \ldots$
  and a strictly increasing sequence of integers $i_0, i_1, \ldots$ where $i_0=0$,
  a single word is obtained by concatenating subwords of the $w_n$ as given by
  the integers: the resulting word is
  \[
    (w_0)_{i_0} \ldots (w_0)_{i_1-1} (w_1)_{i_1} \ldots (w_1)_{i_2-1} \ldots
  \]
  We prepare the field by proving some trivial facts about such sequences of 
  indexes.
*}

definition
  idx_sequence :: "nat word \<Rightarrow> bool"
  where "idx_sequence idx \<equiv> (idx 0 = 0) \<and> (\<forall>n. idx n < idx (Suc n))"

lemma idx_sequence_less:
  assumes iseq: "idx_sequence idx"
  shows "idx n < idx (Suc(n+k))"
proof (induct k)
  from iseq show "idx n < idx (Suc (n + 0))"
    by (simp add: idx_sequence_def)
next
  fix k
  assume ih: "idx n < idx (Suc(n+k))"
  from iseq have "idx (Suc(n+k)) < idx (Suc(n + Suc k))"
    by (simp add: idx_sequence_def)
  with ih show "idx n < idx (Suc(n + Suc k))"
    by (rule less_trans)
qed

lemma idx_sequence_inj:
  assumes iseq: "idx_sequence idx"
  and eq: "idx m = idx n"
  shows "m = n"
proof (rule nat_less_cases)
  assume "n<m"
  then obtain k where "m = Suc(n+k)"
    by (auto simp add: less_iff_Suc_add)
  with iseq have "idx n < idx m"
    by (simp add: idx_sequence_less)
  with eq show ?thesis
    by simp
next
  assume "m<n"
  then obtain k where "n = Suc(m+k)"
    by (auto simp add: less_iff_Suc_add)
  with iseq have "idx m < idx n"
    by (simp add: idx_sequence_less)
  with eq show ?thesis
    by simp
qed (simp)

lemma idx_sequence_mono:
  assumes iseq: "idx_sequence idx"
  and m: "m \<le> n"
  shows "idx m \<le> idx n"
proof (cases "m=n")
  case True
  thus ?thesis by simp
next
  case False
  with m have "m < n" by simp
  then obtain k where "n = Suc(m+k)"
    by (auto simp add: less_iff_Suc_add)
  with iseq have "idx m < idx n"
    by (simp add: idx_sequence_less)
  thus ?thesis by simp
qed

text {*
  Given an index sequence, every natural number is contained in the
  interval defined by two adjacent indexes, and in fact this interval
  is determined uniquely.
*}

lemma idx_sequence_idx:
  assumes "idx_sequence idx"
  shows "idx k \<in> {idx k ..< idx (Suc k)}"
using assms by (auto simp add: idx_sequence_def)

lemma idx_sequence_interval:
  assumes iseq: "idx_sequence idx"
  shows "\<exists>k. n \<in> {idx k ..< idx (Suc k) }"
    (is "?P n" is "\<exists>k. ?in n k")
proof (induct n)
  from iseq have "0 = idx 0"
    by (simp add: idx_sequence_def)
  moreover
  from iseq have "idx 0 \<in> {idx 0 ..< idx (Suc 0) }"
    by (rule idx_sequence_idx)
  ultimately
  show "?P 0" by auto
next
  fix n
  assume "?P n"
  then obtain k where k: "?in n k" ..
  show "?P (Suc n)"
  proof (cases "Suc n < idx (Suc k)")
    case True
    with k have "?in (Suc n) k"
      by simp
    thus ?thesis ..
  next
    case False
    with k have "Suc n = idx (Suc k)"
      by auto
    with iseq have "?in (Suc n) (Suc k)"
      by (simp add: idx_sequence_def)
    thus ?thesis ..
  qed
qed

lemma idx_sequence_interval_unique:
  assumes iseq: "idx_sequence idx"
  and k: "n \<in> {idx k ..< idx (Suc k) }"
  and m: "n \<in> {idx m ..< idx (Suc m) }"
  shows "k = m"
proof (rule nat_less_cases)
  assume "k < m"
  hence "Suc k \<le> m" by simp
  with iseq have "idx (Suc k) \<le> idx m"
    by (rule idx_sequence_mono)
  with m have "idx (Suc k) \<le> n"
    by auto
  with k have "False"
    by simp
  thus ?thesis ..
next
  assume "m < k"
  hence "Suc m \<le> k" by simp
  with iseq have "idx (Suc m) \<le> idx k"
    by (rule idx_sequence_mono)
  with k have "idx (Suc m) \<le> n"
    by auto
  with m have "False"
    by simp
  thus ?thesis ..
qed (simp)

lemma idx_sequence_unique_interval:
  assumes iseq: "idx_sequence idx"
  shows "\<exists>! k. n \<in> {idx k ..< idx (Suc k) }"
proof (rule ex_ex1I)
  from iseq show "\<exists>k. n \<in> {idx k ..< idx (Suc k)}"
    by (rule idx_sequence_interval)
next
  fix k y
  assume "n \<in> {idx k..<idx (Suc k)}" and "n \<in> {idx y..<idx (Suc y)}"
  with iseq show "k = y" by (auto elim: idx_sequence_interval_unique)
qed

text {*
  Now we can define the piecewise construction of a word using
  an index sequence.
*}

definition
  merge :: "['a word word, nat word] \<Rightarrow> 'a word"
  where "merge ws idx \<equiv>
           \<lambda> n. let i = THE i. n \<in> {idx i ..< idx (Suc i) } in ws i n"

lemma merge:
  assumes idx: "idx_sequence idx"
  and n: "n \<in> {idx i ..< idx (Suc i) }"
  shows "merge ws idx n = ws i n"
proof -
  from n have "(THE k. n \<in> {idx k ..< idx (Suc k) }) = i"
    by (rule the_equality[OF _ sym[OF idx_sequence_interval_unique[OF idx n]]]) simp
  thus ?thesis
    by (simp add: merge_def Let_def)
qed

lemma merge0:
  assumes idx: "idx_sequence idx"
  shows "merge ws idx 0 = ws 0 0"
proof (rule merge[OF idx])
  from idx have "idx 0 < idx (Suc 0)"
    by (unfold idx_sequence_def, blast)
  with idx show "0 \<in> {idx 0 ..< idx (Suc 0)}"
    by (simp add: idx_sequence_def)
qed

lemma merge_Suc:
  assumes idx: "idx_sequence idx"
  and n: "n \<in> {idx i ..< idx (Suc i) }"
  shows "merge ws idx (Suc n) = 
         (if Suc n = idx (Suc i) then ws (Suc i) else ws i) (Suc n)"
proof (auto)
  assume eq: "Suc n = idx (Suc i)"
  from idx have "idx (Suc i) < idx (Suc(Suc i))"
    by (unfold idx_sequence_def, blast)
  with eq idx show "merge ws idx (idx (Suc i)) = ws (Suc i) (idx (Suc i))"
    by (simp add: merge)
next
  assume neq: "Suc n \<noteq> idx (Suc i)"
  with n have "Suc n \<in> {idx i ..< idx (Suc i) }"
    by auto
  with idx show "merge ws idx (Suc n) = ws i (Suc n)"
    by (rule merge)
qed

end