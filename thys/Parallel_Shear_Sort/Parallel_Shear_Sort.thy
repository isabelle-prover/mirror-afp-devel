(*
  File:      Shear_Sort.thy
  Authors:   Manuel Eberl, University of Innsbruck
             Peter Lammich, University of Twente

  A formalisation of shear sort, an parallel comparison-based sorting algorithm that sorts n
  elements in time O(sqrt(n) log^2(n)), assuming sqrt(n) parallel processors.
  This can be improved to O(sqrt(n) log(n)) if a linear-time parallel sorting algorithm is used
  for sorting the rows and columns, e.g. odd–even sorting.

  It does this by arranging the elements in a square matrix and then alternating between sorting
  rows and columns until the matrix stabilises.

  Originally a submission to VerifyThis 2021.
*)
theory Parallel_Shear_Sort
  imports Complex_Main "HOL-Library.Multiset" "HOL-Library.FuncSet" Ceil_Log2
begin

subsubsection \<open>Facts about multisets\<close>

(* TODO: Move to distribution? *)
lemma mset_concat: "mset (concat xss) = (\<Sum>xs\<leftarrow>xss. mset xs)"
  by (induction xss) auto

lemma sum_mset_singleton_mset [simp]: "(\<Sum>x\<in>#A. {#f x#}) = image_mset f A"
  by (induction A) auto

lemma sum_list_singleton_mset [simp]: "(\<Sum>x\<leftarrow>xs. {#f x#}) = image_mset f (mset xs)"
  by (induction xs) auto

lemma count_conv_size_mset: "count A x = size (filter_mset (\<lambda>y. y = x) A)"
  by (induction A) auto

lemma size_conv_count_bool_mset: "size A = count A True + count A False"
  by (induction A) auto

lemma set_mset_sum: "finite A \<Longrightarrow> set_mset (\<Sum>x\<in>A. f x) = (\<Union>x\<in>A. set_mset (f x))"
  by (induction A rule: finite_induct) auto

lemma filter_image_mset:
  "filter_mset P (image_mset f A) = image_mset f (filter_mset (\<lambda>x. P (f x)) A)"
  by (induction A) auto


subsubsection \<open>Facts about sorting\<close>

(* TODO: Move to distribution? *)
lemma sort_replicate [simp]: "sort (replicate n x) = replicate n x"
  by (intro properties_for_sort) auto

lemma mset_replicate [simp]: "mset (replicate n x) = replicate_mset n x"
  by (induction n) auto

lemma sorted_wrt_induct [consumes 1, case_names Nil Cons]:
  assumes "sorted_wrt R xs"
  assumes "P []"
          "\<And>x xs. (\<And>y. y \<in> set xs \<Longrightarrow> R x y) \<Longrightarrow> P xs \<Longrightarrow> P (x # xs)"
  shows   "P xs"
  using assms(1) by (induction xs) (auto intro: assms)

lemma sorted_wrt_trans_induct [consumes 2, case_names Nil single Cons]:
  assumes "sorted_wrt R xs" "transp R"
  assumes "P []" "\<And>x. P [x]"
          "\<And>x y xs. R x y \<Longrightarrow> P (y # xs) \<Longrightarrow> P (x # y # xs)"
  shows   "P xs"
  using assms(1)
  by (induction xs rule: induct_list012)
     (auto intro: assms simp: sorted_wrt2[OF assms(2)])

lemmas sorted_induct [consumes 1, case_names Nil single Cons] =
  sorted_wrt_trans_induct[OF _ preorder_class.transp_on_le]

lemma sorted_wrt_map_mono:
  assumes "sorted_wrt R xs"
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> R x y \<Longrightarrow> R' (f x) (f y)"
  shows   "sorted_wrt R' (map f xs)"
  using assms by (induction rule: sorted_wrt_induct) auto

lemma sorted_map_mono:
  assumes "sorted xs" and "mono_on (set xs) f"
  shows   "sorted (map f xs)"
  using assms(1)
  by (rule sorted_wrt_map_mono) (use assms in \<open>auto simp: mono_on_def\<close>)

lemma sort_map_mono: "mono f \<Longrightarrow> sort (map f xs) = map f (sort xs)"
  by (intro properties_for_sort sorted_map_mono)
     (use mono_on_subset in auto)

lemma sorted_boolE:
  assumes "sorted xs" "length xs = w"
  shows   "\<exists>k\<le>w. xs = replicate k False @ replicate (w - k) True"
proof -
  define k where "k = length (filter (\<lambda>b. \<not>b) xs)"
  have "mset xs = replicate_mset k False + replicate_mset (w - k) True"
    unfolding k_def assms(2)[symmetric] by (induction xs) (auto simp: Suc_diff_le)
  moreover have "sorted (replicate k False @ replicate (w - k) True)"
    by (auto simp: sorted_append)
  ultimately have "sort xs = replicate k False @ replicate (w - k) True"
    by (intro properties_for_sort) auto
  moreover have "k \<le> w"
    using assms by (auto simp: k_def)
  ultimately show ?thesis
    using assms(1) by (intro exI[of _ k]) (simp_all add: sorted_sort_id)
qed

lemma rev_sorted_boolE:
  assumes "sorted (rev xs)" "length xs = w"
  shows   "\<exists>k\<le>w. xs = replicate k True @ replicate (w - k) False"
proof -
  from sorted_boolE[OF assms(1)] assms(2) obtain k
    where k: "k \<le> w" "rev xs = replicate k False @ replicate (w - k) True" by auto
  note k(2)
  also have "rev (replicate k False @ replicate (w - k) True) =
             replicate (w - k) True @ replicate (w - (w - k)) False"
    using k(1) by auto
  finally show ?thesis
    by (intro exI[of _ "w - k"]) auto
qed

lemma sort_append:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> x \<le> y"
  shows   "sort (xs @ ys) = sort xs @ sort ys"
  using assms by (intro properties_for_sort) (auto simp: sorted_append)

lemma sort_append_replicate_left:
  "(\<And>y. y \<in> set xs \<Longrightarrow> x \<le> y) \<Longrightarrow> sort (replicate n x @ xs) = replicate n x @ sort xs"
  by (subst sort_append) auto

lemma sort_append_replicate_right:
  "(\<And>y. y \<in> set xs \<Longrightarrow> x \<ge> y) \<Longrightarrow> sort (xs @ replicate n x) = sort xs @ replicate n x"
  by (subst sort_append) auto


subsubsection \<open>Miscellaneous\<close>

(* TODO: Move to distribution? *)
lemma nth_append_left: "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i"
  by (auto simp: nth_append)

lemma nth_append_right: "i \<ge> length xs \<Longrightarrow> (xs @ ys) ! i = ys ! (i - length xs)"
  by (auto simp: nth_append)

lemma Times_insert_right: "A \<times> insert y B = (\<lambda>x. (x, y)) ` A \<union> A \<times> B"
  by auto

lemma Times_insert_left: "insert x A \<times> B = (\<lambda>y. (x, y)) ` B \<union> A \<times> B"
  by auto

lemma map_nth_shift:
  assumes "length xs = b - a"
  shows   "map (\<lambda>j. xs ! (j - a)) [a..<b] = xs"
proof -
  have "map (\<lambda>j. xs ! (j - a)) [a..<b] = map (\<lambda>j. xs ! j) (map (\<lambda>j. j - a) [a..<b])"
    unfolding map_map o_def ..
  also have "map (\<lambda>j. j - a) [a..<b] = [0..<b - a]"
  proof (cases "a \<le> b")
    case True
    thus ?thesis
      by (induction rule: dec_induct) (auto simp: Suc_diff_le)
  qed auto
  also have "map (\<lambda>j. xs ! j) \<dots> = xs"
    by (metis assms map_nth)
  finally show ?thesis .
qed



subsection \<open>Auxiliary definitions\<close>

text \<open>
  The following predicate states that all elements of a list are equal to one another.
\<close>
definition all_same :: "'a list \<Rightarrow> bool"
  where "all_same xs = (\<exists>x. set xs \<subseteq> {x})"

lemma all_same_replicate [intro]: "all_same (replicate n x)"
  unfolding all_same_def by auto

lemma all_same_altdef: "all_same xs \<longleftrightarrow> xs = replicate (length xs) (hd xs)"
proof
  assume *: "xs = replicate (length xs) (hd xs)"
  show "all_same xs"
    by (subst *) auto
next
  assume "all_same xs"
  thus   "xs = replicate (length xs) (hd xs)"
    by (cases xs) (auto simp: all_same_def intro!: replicate_eqI)
qed

lemma all_sameE:
  assumes "all_same xs"
  obtains n x where "xs = replicate n x"
  using assms that unfolding all_same_altdef by metis


text \<open>
  The following predicate states that a list is sorted in ascending or descending order,
  depending on the boolean flag.
\<close>
definition sorted_asc_desc :: "bool \<Rightarrow> 'a :: linorder list \<Rightarrow> bool"
  where "sorted_asc_desc asc xs = (if asc then sorted xs else sorted (rev xs))"

text \<open>
  Analogously, we define a sorting function that takes such a flag.
\<close>
definition sort_asc_desc :: "bool \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list"
  where "sort_asc_desc asc xs = (if asc then sort xs else rev (sort xs))"

lemma length_sort_asc_desc [simp]: "length (sort_asc_desc asc xs) = length xs"
  by (auto simp: sort_asc_desc_def)

lemma mset_sort_asc_desc [simp]: "mset (sort_asc_desc asc xs) = mset xs"
  by (auto simp: sort_asc_desc_def)

lemma sort_asc_desc_map_mono: "mono f \<Longrightarrow> sort_asc_desc b (map f xs) = map f (sort_asc_desc b xs)"
  by (auto simp: sort_asc_desc_def sort_map_mono rev_map)

lemma sort_asc_desc_all_same: "all_same xs \<Longrightarrow> sort_asc_desc asc xs = xs"
  by (auto simp: sort_asc_desc_def elim!: all_sameE)


subsection \<open>Matrices\<close>

text \<open>
  We represent matrices as functions mapping index pairs to elements. The first index is
  the row, the second the column. For convenience, we also fix explicit lower and upper bounds
  for the indices so that we can easily talk about minors of a matrix (or ‘submatrices’).
  The lower bound is inclusive, the upper bound exclusive.
\<close>
type_synonym 'a mat = "nat \<times> nat \<Rightarrow> 'a"

locale shearsort =
  fixes lrow urow lcol ucol :: nat and dummy :: "'a :: linorder"
  assumes lrow_le_urow: "lrow \<le> urow"
  assumes lcol_le_ucol: "lcol \<le> ucol"
begin

text \<open>The set of valid indices:\<close>
definition idxs :: "(nat \<times> nat) set" where "idxs = {lrow..<urow} \<times> {lcol..<ucol}"

text \<open>The multiset of all entries in the matrix:\<close>
definition mset_mat :: "(nat \<times> nat \<Rightarrow> 'b) \<Rightarrow> 'b multiset"
  where "mset_mat m = image_mset m (mset_set idxs)"

text \<open>The \<open>i\<close>-th row and \<open>j\<close>-th column of a matrix:\<close>
definition row :: "(nat \<times> nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b list"
  where "row m i = map (\<lambda>j. m (i, j)) [lcol..<ucol]"
definition col :: "(nat \<times> nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b list"
  where "col m j = map (\<lambda>i. m (i, j)) [lrow..<urow]"

lemma length_row [simp]: "length (row m i) = ucol - lcol"
  and length_col [simp]: "length (col m i) = urow - lrow"
  by (simp_all add: row_def col_def)

lemma nth_row [simp]: "j < ucol - lcol \<Longrightarrow> row m i ! j = m (i, lcol + j)"
  unfolding row_def by (subst nth_map) auto

lemma set_row: "set (row m i) = (\<lambda>j. m (i, j)) ` {lcol..<ucol}"
  unfolding row_def by simp

lemma set_col: "set (col m j) = (\<lambda>i. m (i, j)) ` {lrow..<urow}"
  unfolding col_def by simp

lemma mset_row: "mset (row m i) = image_mset (\<lambda>j. m (i, j)) (mset [lcol..<ucol])"
  unfolding row_def by simp

lemma mset_col: "mset (col m j) = image_mset (\<lambda>i. m (i, j)) (mset [lrow..<urow])"
  unfolding col_def by simp

lemma nth_col [simp]: "i < urow - lrow \<Longrightarrow> col m j ! i = m (lrow + i, j)"
  unfolding col_def by (subst nth_map) auto


text \<open>
  The following helps us to restrict a matrix operation to the valid indices. Here, \<open>m\<close> is the 
  original matrix and \<open>m'\<close> the changed matrix that we obtained after applying
  some operation on it.
\<close>
definition restrict_mat :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "restrict_mat m m' = (\<lambda>ij. if ij \<in> idxs then m' ij else m ij)"

lemma row_restrict_mat [simp]:
  "row (restrict_mat m m') i = (if i \<in> {lrow..<urow} then row m' i else row m i)"
  by (auto simp: restrict_mat_def idxs_def row_def)

lemma col_restrict_mat [simp]:
  "col (restrict_mat m m') j = (if j \<in> {lcol..<ucol} then col m' j else col m j)"
  by (auto simp: restrict_mat_def idxs_def col_def)


text \<open>
  The following lemmas allow us to prove that two matrices are equal by showing that 
  their rows (or columns) are the same.
\<close>
lemma matrix_eqI_rows:
  assumes "\<And>i. i \<in> {lrow..<urow} \<Longrightarrow> row m1 i = row m2 i"
  assumes "\<And>i j. (i, j) \<notin> idxs \<Longrightarrow> m1 (i, j) = m2 (i, j)"
  shows   "m1 = m2"
  using assms by (auto simp: fun_eq_iff row_def idxs_def atLeastLessThan_def)

lemma matrix_eqI_cols:
  assumes "\<And>j. j \<in> {lcol..<ucol} \<Longrightarrow> col m1 j = col m2 j"
  assumes "\<And>i j. (i, j) \<notin> idxs \<Longrightarrow> m1 (i, j) = m2 (i, j)"
  shows   "m1 = m2"
  using assms by (auto simp: fun_eq_iff col_def idxs_def atLeastLessThan_def)


text \<open>
  The following lemmas express the multiset of elements as a sum of rows (or columns):
\<close>
lemma mset_mat_conv_sum_rows: "mset_mat m = (\<Sum>i\<in>{lrow..<urow}. mset (row m i))"
  using lrow_le_urow unfolding mset_mat_def idxs_def
proof (induction rule: dec_induct)
  case (step n)
  have "image_mset m (mset_set ({lrow..<Suc n} \<times> {lcol..<ucol})) =
        image_mset m (mset_set ((\<lambda>j. (n, j)) ` {lcol..<ucol} \<union> {lrow..<n} \<times> {lcol..<ucol}))"
    using step.prems step.hyps by (auto simp: Times_insert_left atLeastLessThanSuc)
  also have "\<dots> = image_mset m (mset_set ((\<lambda>j. (n, j)) ` {lcol..<ucol})) +
                  image_mset m (mset_set ({lrow..<n} \<times> {lcol..<ucol}))"
    by (subst mset_set_Union) (auto simp flip: image_mset_mset_set)
  also have "\<dots> = image_mset m (image_mset (\<lambda>j. (n, j)) (mset_set {lcol..<ucol})) +
                  image_mset m (mset_set ({lrow..<n} \<times> {lcol..<ucol}))"
    by (subst image_mset_mset_set [symmetric]) (auto simp: inj_on_def)
  also have "\<dots> = (\<Sum>i = lrow..<Suc n. mset (row m i))"
    using step by (simp add: row_def multiset.map_comp o_def)
  finally show ?case .
qed auto

lemma mset_mat_conv_sum_cols: "mset_mat m = (\<Sum>j\<in>{lcol..<ucol}. mset (col m j))"
  using lcol_le_ucol unfolding mset_mat_def idxs_def
proof (induction rule: dec_induct)
  case (step n)
  have "image_mset m (mset_set ({lrow..<urow} \<times> {lcol..<Suc n})) =
        image_mset m (mset_set ((\<lambda>i. (i, n)) ` {lrow..<urow} \<union> {lrow..<urow} \<times> {lcol..<n}))"
    using step.prems step.hyps by (auto simp: Times_insert_right atLeastLessThanSuc)
  also have "\<dots> = image_mset m (mset_set ((\<lambda>i. (i, n)) ` {lrow..<urow})) +
                  image_mset m (mset_set ({lrow..<urow} \<times> {lcol..<n}))"
    by (subst mset_set_Union) (auto simp flip: image_mset_mset_set)
  also have "\<dots> = image_mset m (image_mset (\<lambda>i. (i, n)) (mset_set {lrow..<urow})) +
                  image_mset m (mset_set ({lrow..<urow} \<times> {lcol..<n}))"
    by (subst image_mset_mset_set [symmetric]) (auto simp: inj_on_def)
  also have "\<dots> = (\<Sum>i = lcol..<Suc n. mset (col m i))"
    using step by (simp add: col_def multiset.map_comp o_def)
  finally show ?case .
qed auto


text \<open>Lastly, we define the transposition operation:\<close>

definition transpose_mat :: "((nat \<times> nat) \<Rightarrow> 'a) \<Rightarrow> (nat \<times> nat) \<Rightarrow> 'a"
  where "transpose_mat m = (\<lambda>(i,j). m (j, i))"

lemma transpose_mat_apply: "transpose_mat m (j, i) = m (i, j)"
  by (simp add: transpose_mat_def)

sublocale transpose: shearsort lcol ucol lrow urow
  by unfold_locales (fact lcol_le_ucol lrow_le_urow)+

lemma row_transpose [simp]: "transpose.row (transpose_mat m) i = col m i"
  and col_transpose [simp]: "transpose.col (transpose_mat m) i = row m i"
  by (simp_all add: transpose.row_def col_def transpose.col_def row_def transpose_mat_def)

lemma in_transpose_idxs_iff: "(j, i) \<in> transpose.idxs \<longleftrightarrow> (i, j) \<in> idxs"
  by (auto simp: idxs_def transpose.idxs_def)


subsection \<open>Snake-wise sortedness\<close>

text \<open>
  Next, we define snake-wise sortedness. For this, even-numbered rows must be sorted ascendingly,
  the odd-numbered ones descendingly, etc. We will show a nicer characterisation of this below. 
\<close>

definition snake_sorted :: "'a mat \<Rightarrow> bool" where
  "snake_sorted m \<longleftrightarrow>
     (\<forall>i\<in>{lrow..<urow}. sorted_asc_desc (even i) (row m i)) \<and>
     (\<forall>i i' x y. lrow \<le> i \<and> i < i' \<and> i' < urow \<and> x \<in> set (row m i) \<and> y \<in> set (row m i') \<longrightarrow> x \<le> y)"


text \<open>
  Next, we define the list of elements encountered on the snake-like path through the matrix,
  i.e.\ when traversing the matrix top to bottom, even-numbered rows left-to-right and
  odd-numbered rows right-to-left.
\<close>

context
  fixes m :: "'a mat"
begin

function snake_aux :: "nat \<Rightarrow> 'a list" where
  "snake_aux i =
     (if i \<ge> urow then [] else (if even i then row m i else rev (row m i)) @ snake_aux (Suc i))"
  by auto
termination by (relation "measure (\<lambda>i. urow - i)") auto

lemmas [simp del] = snake_aux.simps


definition snake :: "'a list"
  where "snake = snake_aux lrow"

lemma mset_snake_aux: "mset (snake_aux lrow') = (\<Sum>i\<in>{lrow'..<urow}. mset (row m i))"
  by (induction lrow' rule: snake_aux.induct; subst snake_aux.simps)
     (simp_all add: sum.atLeast_Suc_lessThan)

lemma set_snake_aux: "set (snake_aux lrow') = (\<Union>i\<in>{lrow'..<urow}. set (row m i))"
proof -
  have "set (snake_aux lrow') = set_mset (mset (snake_aux lrow'))"
    by simp
  thus ?thesis
    by (subst (asm) mset_snake_aux) (simp_all add: set_mset_sum)
qed


text \<open>
  We can now show that snake-wise sortedness is equivalent to saying that
  \<^const>\<open>snake\<close> is sorted.
\<close>
lemma sorted_snake_aux_iff:
  "sorted (snake_aux lrow') \<longleftrightarrow>
     (\<forall>i\<in>{lrow'..<urow}. sorted_asc_desc (even i) (row m i)) \<and>
     (\<forall>i i' x y. lrow' \<le> i \<and> i < i' \<and> i' < urow \<and> x \<in> set (row m i) \<and> y \<in> set (row m i') \<longrightarrow> x \<le> y)"
proof -
  define sorted1 where
    "sorted1 = (\<lambda>lrow'. \<forall>i\<in>{lrow'..<urow}. sorted_asc_desc (even i) (row m i))"
  define sorted2 where
    "sorted2 = (\<lambda>lrow'. \<forall>i i' x y. lrow' \<le> i \<and> i < i' \<and> i' < urow \<and>
                        x \<in> set (row m i) \<and> y \<in> set (row m i') \<longrightarrow> x \<le> y)"
  have ivl_split: "{lrow'..<urow} = insert lrow' {Suc lrow'..<urow}" if "lrow' < urow" for lrow'
    using that by auto

  have "sorted (snake_aux lrow') \<longleftrightarrow> sorted1 lrow' \<and> sorted2 lrow'"
  proof (induction lrow' rule: snake_aux.induct)
    case (1 lrow')
    show ?case
    proof (cases "lrow' \<ge> urow")
      case True
      thus ?thesis
        by (subst snake_aux.simps) (auto simp: sorted1_def sorted2_def)
    next
      case False
      hence "sorted (snake_aux lrow') \<longleftrightarrow>
               (sorted_asc_desc (even lrow') (row m lrow') \<and> sorted1 (Suc lrow')) \<and>
               (sorted2 (Suc lrow') \<and>
                  (\<forall>j\<in>{lcol..<ucol}. \<forall>i\<in>{Suc lrow'..<urow}. \<forall>y\<in>set (row m i). y \<ge> m (lrow', j)))"
        (is "_ \<longleftrightarrow> ?A \<and> (_ \<and> ?B)") using 1
        by (subst snake_aux.simps)
           (simp_all add: sorted_append set_row set_snake_aux sorted_asc_desc_def)
      also have "?A \<longleftrightarrow> sorted1 lrow'"
        using False unfolding sorted1_def by (auto simp: ivl_split)
      also have "?B \<longleftrightarrow> (\<forall>i\<in>{Suc lrow'..<urow}. \<forall>x\<in>set (row m lrow'). \<forall>y\<in>set (row m i). x \<le> y)"
        by (auto simp: set_row)
      also have "sorted2 (Suc lrow') \<and> \<dots> \<longleftrightarrow> sorted2 lrow'"
      proof (safe, goal_cases)
        case 1
        thus ?case 
          using False
          unfolding sorted2_def by (metis Suc_leI atLeastLessThan_iff le_neq_implies_less)
      next
        case 2
        thus ?case 
          unfolding sorted2_def using False by (auto simp: sorted2_def dest: Suc_leD)
      next
        case 3
        thus ?case 
          using False by (auto simp: sorted2_def dest!: Suc_le_lessD)
      qed
      finally show ?thesis .
    qed
  qed
  thus ?thesis by (simp add: sorted1_def sorted2_def)
qed

lemma sorted_snake_iff: "sorted snake \<longleftrightarrow> snake_sorted m"
  by (simp add: snake_def sorted_snake_aux_iff snake_sorted_def)

end


subsection \<open>Definition of the abstract algorithm\<close>

text \<open>
  We can now define shear sort on matrices. We will also show that the multiset of elements is
  preserved.
\<close>

subsubsection \<open>Sorting the rows\<close>

definition step1 :: "'a mat \<Rightarrow> 'a mat" where
  "step1 m = restrict_mat m (\<lambda>(i,j). sort_asc_desc (even i) (row m i) ! (j - lcol))"

lemma step1_outside [simp]: "z \<notin> idxs \<Longrightarrow> step1 m z = m z"
  by (simp add: step1_def restrict_mat_def)

lemma row_step1:
  "row (step1 m) i = (if i \<in> {lrow..<urow} then sort_asc_desc (even i) (row m i) else row m i)"
  unfolding step1_def row_restrict_mat by (subst (2) row_def) (simp add: map_nth_shift)

lemma mset_mat_step1 [simp]: "mset_mat (step1 m) = mset_mat m"
  by (simp add: mset_mat_conv_sum_rows row_step1)


subsubsection \<open>Sorting the columns\<close>

definition step2 :: "'a mat \<Rightarrow> 'a mat" where
  "step2 m = restrict_mat m (\<lambda>(i,j). sort (col m j) ! (i - lrow))"

lemma step2_outside [simp]: "z \<notin> idxs \<Longrightarrow> step2 m z = m z"
  by (simp add: step2_def restrict_mat_def)

lemma col_step2: "col (step2 m) j = (if j \<in> {lcol..<ucol} then sort (col m j) else col m j)"
  unfolding step2_def col_restrict_mat by (subst (2) col_def) (simp add: map_nth_shift)

lemma mset_mat_step2 [simp]: "mset_mat (step2 m) = mset_mat m"
  by (simp add: mset_mat_conv_sum_cols col_step2)

lemma step2_height_le_1:
  assumes "urow \<le> lrow + 1"
  shows   "step2 m = m"
proof (rule matrix_eqI_cols, goal_cases)
  case (1 j)
  with assms have "length (col m j) \<le> 1"
    by auto
  hence "sort (col m j) = col m j"
    using sorted01 sorted_sort_id by blast
  thus ?case using 1
    by (auto simp: col_step2)
qed (auto simp: step2_def restrict_mat_def)

text \<open>
  We also show the alternative definiton of \<^const>\<open>step2\<close> involving transposition and sorting rows:
\<close>
definition step2' :: "'a mat \<Rightarrow> 'a mat" where
  "step2' m = restrict_mat m (\<lambda>(i,j). sort (row m i) ! (j - lcol))"

lemma step2'_outside [simp]: "z \<notin> idxs \<Longrightarrow> step2' m z = m z"
  by (simp add: step2'_def restrict_mat_def)

lemma row_step2': "row (step2' m) i = (if i \<in> {lrow..<urow} then sort (row m i) else row m i)"
  unfolding step2'_def row_restrict_mat by (subst (2) row_def) (simp add: map_nth_shift)

end

context shearsort
begin

lemma step2_altdef: "step2 m = transpose.transpose_mat (transpose.step2' (transpose_mat m))"
  by (rule matrix_eqI_cols, goal_cases)
     (simp_all add: col_step2 transpose.row_step2' transpose_mat_apply in_transpose_idxs_iff)


subsubsection \<open>Combining the two steps\<close>

definition step where "step = step2 \<circ> step1"

lemma step_outside [simp]: "z \<notin> idxs \<Longrightarrow> step m z = m z"
  by (auto simp: step_def step1_def step2_def restrict_mat_def)

lemma row_step_outside [simp]: "i \<notin> {lrow..<urow} \<Longrightarrow> row (step m) i = row m i"
  by (auto simp add: step_def step2_def row_step1)

lemma mset_mat_step [simp]: "mset_mat (step m) = mset_mat m"
  by (simp add: step_def)


text \<open>
  The overall algorithm now simply alternates between steps 1 and 2 sufficiently often for
  the result to stabilise. We will show below that a logarithmic number of steps suffices.
\<close>
definition shearsort :: "'a mat \<Rightarrow> 'a mat" where
  "shearsort = step ^^ (ceillog2 (urow - lrow) + 1)"

text \<open>
  The preservation of the multiset of elements is very easy to show:
\<close>
theorem mset_mat_shearsort [simp]: "mset_mat (shearsort m) = mset_mat m"
proof -
  define l where "l = ceillog2 (urow - lrow) + 1"
  have "mset_mat ((step ^^ l) m) = mset_mat m"
    by (induction l) auto
  thus ?thesis by (simp add: shearsort_def l_def)
qed

end


subsection \<open>Restriction to boolean matrices\<close>

text \<open>
  To more towards the proof of sortedness, we first take a closer look at shear sort on boolean
  matrices. Our ultimate goal is to show that shear sort correctly sorts any boolean matrix
  in \<open>\<lceil>log\<^sub>2 h\<rceil> + 1\<close> steps, where \<open>h\<close> is the height of the matrix. By the 0--1 principle, this 
  implies that shear sort works on a matrix of any type.
\<close>

subsubsection \<open>Preliminary definitions\<close>

text \<open>
  We first define predicates that tell us whether a list is all zeros (i.e. \<^const>\<open>False\<close>) or
  all ones (i.e. \<^const>\<open>True\<close>). The significance of such lists is that we call all-zero rows
  at the top of the matrix and all-one rows at the bottom ``clean'', and we will show that
  even in the worst case, the number of non-clean rows halves in every step.
\<close>

definition all0 :: "bool list \<Rightarrow> bool" where "all0 xs = (set xs \<subseteq> {False})"
definition all1 :: "bool list \<Rightarrow> bool" where "all1 xs = (set xs \<subseteq> {True})"

lemma all0_nth: "all0 xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i = False"
  and all1_nth: "all1 xs \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i = True"
  unfolding all0_def all1_def using nth_mem[of i xs] by blast+

lemma all0_imp_all_same [dest]: "all0 xs \<Longrightarrow> all_same xs"
  and all1_imp_all_same [dest]: "all1 xs \<Longrightarrow> all_same xs"
  unfolding all0_def all1_def all_same_def by blast+


locale shearsort_bool =
  fixes lrow urow lcol ucol :: nat
  assumes lrow_le_urow: "lrow \<le> urow"
  assumes lcol_le_ucol: "lcol \<le> ucol"
begin

sublocale shearsort lrow urow lcol ucol True
  by unfold_locales (fact lrow_le_urow lcol_le_ucol)+

text \<open>
  We say that a matrix \<open>m\<close> of height \<open>h\<close> has a clean decomposition of order \<open>n\<close> if there are at
  most \<open>n\<close> non-clean rows, i.e.\ there exists a \<open>k\<close> such that \<open>m\<close> has \<open>k\<close> lines that are all 0 at
  the top and \<open>h - n - k\<close> lines that are all 1 at the bottom.
\<close>
definition clean_decomp where
  "clean_decomp n m \<longleftrightarrow> (\<exists>k. lrow \<le> k \<and> k + n \<le> urow \<and>
     (\<forall>i\<in>{lrow..<k}. all0 (row m i)) \<and> (\<forall>i\<in>{k+n..<urow}. all1 (row m i)))"

text \<open>
  A matrix of height \<open>h\<close> trivially has a clean decomposition of order \<open>h\<close>.
\<close>
lemma clean_decomp_initial: "clean_decomp (urow - lrow) m"
  unfolding clean_decomp_def by (rule exI[of _ lrow]) (use lrow_le_urow in auto)

lemma all0_rowI:
  assumes "i \<in> {lrow..<urow}" "\<And>j. j \<in> {lcol..<ucol} \<Longrightarrow> \<not>m (i, j)"
  shows   "all0 (row m i)"
  using assms unfolding set_row all0_def by auto

lemma all1_rowI:
  assumes "i \<in> {lrow..<urow}" "\<And>j. j \<in> {lcol..<ucol} \<Longrightarrow> m (i, j)"
  shows   "all1 (row m i)"
  using assms unfolding set_row all1_def by auto

text \<open>
  The \<^const>\<open>step2\<close> function on boolean matrices has the following nice characterisation:
  \<^term>\<open>step2 m\<close> has a \<open>1\<close> at position \<open>(i, j)\<close> iff the number of \<open>0\<close>s in the column \<open>j\<close> is
  at most \<open>i\<close>.
\<close>
lemma step2_bool:
  assumes "(i, j) \<in> idxs"
  shows   "step2 m (i, j) \<longleftrightarrow> i \<ge> lrow + size (count (mset (col m j)) False)"
proof -
  have "\<exists>k\<le>urow - lrow. sort (col m j) = replicate k False @ replicate (urow - lrow - k) True"
    by (rule sorted_boolE) auto
  then obtain k where k: 
    "k \<le> urow - lrow"
    "sort (col m j) = replicate k False @ replicate (urow - lrow - k) True"
    by blast
  have "k = size (count (mset (sort (col m j))) False)"
    by (subst k(2)) auto
  hence k_eq: "k = size (count (mset (col m j)) False)"
    by simp

  have "step2 m (i, j) = col (step2 m) j ! (i - lrow)"
    using assms by (subst nth_col) (auto simp: idxs_def)
  also have "\<dots> = sort (col m j) ! (i - lrow)"
    using assms by (simp add: col_step2 idxs_def)
  also have "\<dots> \<longleftrightarrow> i \<ge> lrow + k"
    using assms by (auto simp: k nth_append idxs_def)
  finally show ?thesis
    by (simp only: k_eq)
qed

end


subsubsection \<open>Shearsort steps ignore clean rows\<close>

text \<open>
  We now look at a at the matrix minor consisting of the \<open>n\<close> (possibly) non-clean rows in the middle
  of a matrix with a clean decomposition of order \<open>n\<close>. We call the new upper and lower index bounds
  for the rows \<open>lrow'\<close> and \<open>urow'\<close>.
\<close>

locale sub_shearsort_bool = shearsort_bool +
  fixes lrow' urow' :: nat and m :: "bool mat"
  assumes subrows: "lrow \<le> lrow'" "lrow' \<le> urow'" "urow' \<le> urow"
  assumes all0_first: "\<And>i. i \<in> {lrow..<lrow'} \<Longrightarrow> all0 (row m i)"
  assumes all1_last: "\<And>i. i \<in> {urow'..<urow} \<Longrightarrow> all1 (row m i)"
begin

sublocale sub: shearsort_bool lrow' urow' lcol ucol
  by unfold_locales (use subrows lcol_le_ucol in auto)

lemma idxs_subset: "sub.idxs \<subseteq> idxs"
  using subrows by (auto simp: sub.idxs_def idxs_def)

text \<open>
  It is easy to see that \<^const>\<open>step1\<close> does not touch the clean rows at all (i.e.\ it can
  be seen as operating entirely on the minor):
\<close>
lemma sub_step1: "sub.step1 m = step1 m"
proof (rule sym, rule matrix_eqI_rows, goal_cases)
  case (1 i)
  show "row (step1 m) i = row (sub.step1 m) i"
  proof (cases "i \<in> {lrow'..<urow'}")
    case True
    thus ?thesis using subrows
      by (simp add: row_step1 sub.row_step1)
  next
    case False
    hence "all_same (sub.row m i)"
      using all0_first[of i] all1_last[of i] 1 by auto
    thus ?thesis using 1
      by (simp add: row_step1 sub.row_step1 sort_asc_desc_all_same)
  qed
next
  case (2 i j)
  with idxs_subset have "(i, j) \<notin> sub.idxs"
    by auto
  thus ?case
    using 2 by auto
qed

text \<open>
  Every column of the matrix has \<open>lrow' - lrow\<close> \<open>0\<close>s at the top and \<open>urow - urow'\<close> \<open>1\<close>s at the bottom:
\<close>
lemma col_conv_sub_col:
  assumes "j \<in> {lcol..<ucol}"
  shows   "col m j = replicate (lrow' - lrow) False @ sub.col m j @ replicate (urow - urow') True"
proof (intro nth_equalityI, goal_cases)
  case 1
  thus ?case using subrows by auto
next
  case (2 i)
  consider "i < lrow' - lrow" | "i \<in> {lrow'-lrow..<urow'-lrow}" | "i \<in> {urow'-lrow..<urow-lrow}"
    using 2 by force
  thus ?case
  proof cases
    case 1
    hence "all0 (row m (lrow + i))"
      by (intro all0_first) auto
    hence "row m (lrow + i) ! (j - lcol) = False"
      using assms by (intro all0_nth) auto
    thus ?thesis using 1 assms subrows
      by (auto simp: nth_append)
  next
    case 2
    have "(replicate (lrow' - lrow) False @ sub.col m j @ replicate (urow - urow') True) ! i =
          (sub.col m j @ replicate (urow - urow') True) ! (i - (lrow' - lrow))"
      using 2 by (subst nth_append_right) auto
    also have "\<dots> = sub.col m j ! (i - (lrow' - lrow))"
      using 2 by (subst nth_append_left) auto
    also have "\<dots> = m (lrow + i, j)"
      using 2 subrows by (subst sub.nth_col) (auto simp: algebra_simps)
    also have "\<dots> = col m j ! i"
      using 2 subrows by (subst nth_col) auto
    finally show ?thesis ..
  next
    case 3
    hence "all1 (row m (lrow + i))"
      by (intro all1_last) auto
    hence "row m (lrow + i) ! (j - lcol) = True"
      using assms by (intro all1_nth) auto
    hence "col m j ! i = True"
      using 3 assms by auto
    also have "True = (replicate (lrow' - lrow) False @ sub.col m j @ replicate (urow - urow') True) ! i"
      by (subst append_assoc [symmetric], subst nth_append_right) (use 3 subrows in auto)
    finally show ?thesis .
  qed
qed

text \<open>mset
  \<^const>\<open>step2\<close> preserves the clean rows at the bottom and top.
\<close>
lemma all0_step2:
  assumes "i \<in> {lrow..<lrow'}"
  shows   "all0 (row (step2 m) i)"
proof -
  have *: "row (step2 m) i ! (j - lcol) = False" if j: "j \<in> {lcol..<ucol}" for j
  proof -
    have "row (step2 m) i ! (j - lcol) = step2 m (i, j)"
      using assms j subrows by (subst nth_row) auto
    also have "step2 m (i, j) = col (step2 m) j ! (i - lrow)"
      using assms j subrows by (subst nth_col) auto
    also have "\<dots> = False"
      using j assms by (auto simp: col_step2 col_conv_sub_col sort_append_replicate_left
                                   sort_append_replicate_right nth_append)
    finally show ?thesis .
  qed
  have "row (step2 m) i ! j = False" if "j < length (row (step2 m) i)" for j
    using *[of "j + lcol"] that by auto
  thus ?thesis unfolding all0_def set_conv_nth
    by blast
qed

lemma all1_step2:
  assumes "i \<in> {urow'..<urow}"
  shows   "all1 (row (step2 m) i)"
proof -
  have *: "row (step2 m) i ! (j - lcol) = True" if j: "j \<in> {lcol..<ucol}" for j
  proof -
    have "row (step2 m) i ! (j - lcol) = step2 m (i, j)"
      using assms j subrows by (subst nth_row) auto
    also have "step2 m (i, j) = col (step2 m) j ! (i - lrow)"
      using assms j subrows by (subst nth_col) auto
    also have "\<dots> = ((replicate (lrow' - lrow) False @ sort (sub.col m j)) @ replicate (urow - urow') True) ! (i - lrow)"
      using j assms by (simp add: col_step2 col_conv_sub_col sort_append_replicate_left sort_append_replicate_right)
    also have "\<dots> = True"
      using j assms subrows by (subst nth_append_right) auto
    finally show ?thesis .
  qed
  have "row (step2 m) i ! j = True" if "j < length (row (step2 m) i)" for j
    using *[of "j + lcol"] that by auto
  thus ?thesis unfolding all1_def set_conv_nth
    by blast
qed

text \<open>
  Consequently, \<^const>\<open>step2\<close> can also be seen as operating only on the minor.
\<close>
lemma sub_step2: "sub.step2 m = step2 m"
proof (rule sym, rule matrix_eqI_cols, goal_cases)
  case (1 j)
  interpret step2: sub_shearsort_bool lrow urow lcol ucol lrow' urow' "sub.step2 m"
    by unfold_locales
       (use subrows all0_step2 all1_step2 all0_first all1_last in \<open>auto simp: sub.step2_def\<close>)
  have "col (step2 m) j =
           sort (replicate (lrow' - lrow) False @ sub.col m j @ replicate (urow - urow') True)"
    using 1 by (simp add: col_step2 col_conv_sub_col)
  also have "\<dots> = replicate (lrow' - lrow) False @ sort (sub.col m j) @ replicate (urow - urow') True"
    by (simp add: sort_append_replicate_left sort_append_replicate_right)
  also have "\<dots> = col (sub.step2 m) j"
    using 1 subrows by (simp add: sub.col_step2 step2.col_conv_sub_col)
  finally show ?case .
next
  case (2 i j)
  with idxs_subset have "(i, j) \<notin> sub.idxs"
    by auto
  thus ?case
    using 2 by auto
qed

text \<open>
  Thus, the same holds for the combined shear sort step.
\<close>
lemma sub_step: "sub.step m = step m"
proof -
  interpret step1: sub_shearsort_bool lrow urow lcol ucol lrow' urow' "step1 m"
    using all0_first all1_last subrows 
    by unfold_locales (auto simp: sub.row_step1 simp flip: sub_step1)
  show ?thesis
    unfolding step_def o_def by (simp add: step1.sub_step2 sub.step_def sub_step1)
qed

end


subsubsection \<open>Correctness of boolean shear sort\<close>

text \<open>
  We are now ready for the final push. The main work in this section is to show that if 
  we run a single shear sort step on a matrix of height \<open>h\<close>, the number of non-clean rows
  in the result is no greater than \<open>\<lceil>h/2\<rceil>\<close>.

  Together with the fact from above that the step preserves clean rows and can such be thought
  of as operating solely on the non-clean minor, this means that the number of non-clean rows
  at least halves in every step, leading to a matrix with at most one non-clean row after
  \<open>\<lceil>log\<^sub>2 h\<rceil>\<close> steps.
\<close>

context shearsort_bool
begin

text \<open>
  If we look at two rows, one of which is sorted in ascending order and one in descending order,
  there exists a boolean value \<open>x\<close> such that every column contains an \<open>x\<close>
  (i.e.\ for every column index \<open>j\<close>, at least one of the two rows has an \<open>x\<close> at index \<open>j\<close>).
\<close>
lemma clean_decomp_step2_aux:
  fixes m :: "bool mat"
  assumes "i \<in> {lrow..<urow}" "i' \<in> {lrow..<urow}"
  assumes "sorted (row m i)" "sorted (rev (row m i'))"
  shows   "\<exists>x. \<forall>j\<in>{lcol..<ucol}. x \<in> {m (i, j), m (i', j)}"
proof -
  obtain k1 where k1: "k1 \<le> ucol - lcol"
     "row m i = replicate k1 False @ replicate (ucol - lcol - k1) True"
    using sorted_boolE[OF assms(3), of "ucol - lcol"] by auto
  obtain k2 where k2: "k2 \<le> ucol - lcol"
     "row m i' = replicate k2 True @ replicate (ucol - lcol - k2) False"
    using rev_sorted_boolE[OF assms(4), of "ucol - lcol"] by auto

  define x where "x = (k2 > k1)"
  have "x \<in> {m (i, j), m (i', j)}" if j: "j \<in> {lcol..<ucol}" for j
  proof -
    have "x \<in> {row m i ! (j - lcol), row m i' ! (j - lcol)}"
      using j k1 k2 by (auto simp: x_def nth_append)
    thus "x \<in> {m (i, j), m (i', j)}"
      using assms(1,2) j by auto
  qed
  thus ?thesis by metis
qed

text \<open>
  \<^const>\<open>step1\<close> leaves every even-numbered row in the matrix sorted in ascending order and
  every odd-numbered row in descending order:
\<close>
lemma sorted_asc_desc_row_step1:
  "i \<in> {lrow..<urow} \<Longrightarrow> sorted_asc_desc (even i) (row (step1 m) i)"
  by (auto simp: row_step1 sorted_asc_desc_def sort_asc_desc_def)

text \<open>
  These two facts imply that applying \<^const>\<open>step2\<close> to such a matrix indeed leads to at most
  \<open>\<lceil>h/2\<rceil>\<close> non-clean rows. The argument is as follows: we go through the matrix top-to-bottom,
  grouping adjacent rows into pairs of two (ignoring the last row if the matrix has odd height).

  The above lemma proves that each such pair of rows either has a \<open>1\<close> in every column or a \<open>0\<close> in
  every column. Thus, the maximum number \<open>k\<^sub>0\<close> such that every column contains at least \<open>k\<^sub>0\<close> \<open>0\<close>s
  plus the maximum number \<open>k\<^sub>1\<close> such that every column contains at least \<open>k\<^sub>1\<close> 1s is at least
  \<open>\<lfloor>h/2\<rfloor>\<close>. Thus, after applying \<^const>\<open>step2\<close>, we have at least \<open>k\<^sub>0\<close> all-zero rows at the top and
  at least \<open>k\<^sub>1\<close> all-one rows at the bottom, and therefore at least \<open>\<lfloor>h/2\<rfloor>\<close> clean lines in total.
\<close>
lemma clean_decomp_step2:
  assumes "\<And>i. i \<in> {lrow..<urow} \<Longrightarrow> sorted_asc_desc (even i) (row m i)"
  shows   "clean_decomp ((urow - lrow + 1) div 2) (step2 m)"
proof -
  define r where [simp]: "r = row m"

  have "\<exists>x. \<forall>j\<in>{lcol..<ucol}. x \<in> {m (lrow+2*i, j), m (lrow+2*i+1, j)}"
    if i: "i < (urow - lrow) div 2" for i
  proof -
    have *: "lrow + 2 * i \<in> {lrow..<urow}" "lrow + 2 * i + 1 \<in> {lrow..<urow}"
      using i by auto
    have "sorted_asc_desc (even (lrow+2*i)) (row m (lrow+2*i))"
         "sorted_asc_desc (even (lrow+2*i+1)) (row m (lrow+2*i+1))"
      by (intro assms *)+
    hence "sorted (row m (lrow+2*i)) \<and> sorted (rev (row m (lrow+2*i+1))) \<or> 
           sorted (rev (row m (lrow+2*i))) \<and> sorted (row m (lrow+2*i+1))"
      using assms[of i] by (auto simp: sorted_asc_desc_def split: if_splits)
    thus ?thesis
      using clean_decomp_step2_aux[of "lrow+2*i" "lrow+2*i+1" m]
            clean_decomp_step2_aux[of "lrow+2*i+1" "lrow+2*i" m] * 
      by (metis insert_iff)
  qed

  then obtain f where f: "\<And>i j. i < (urow - lrow) div 2 \<Longrightarrow> j \<in> {lcol..<ucol} \<Longrightarrow>
                                  f i \<in> {m (lrow+2*i, j), m (lrow+2*i+1, j)}" by metis

  define I where "I = (\<lambda>x. filter_mset (\<lambda>i. f i = x) (mset [0..<(urow - lrow) div 2]))"
  have size_I: "size (I x) \<le> (urow - lrow) div 2" for x
    unfolding I_def by (rule order.trans[OF size_filter_mset_lesseq]) auto

  have size_I_le: "count (mset (col m j)) x \<ge> size (I x)" if j: "j \<in> {lcol..<ucol}" for x j
  proof -
    define g where "g = (\<lambda>i. if m (lrow+2*i, j) = x then lrow + 2 * i else lrow + 2 * i + 1)"
    have "size (I x) = card {i. i < (urow - lrow) div 2 \<and> f i = x}"
      by (simp add: I_def)
    also have "\<dots> = card (g ` {i. i < (urow - lrow) div 2 \<and> f i = x})"
      by (intro card_image [symmetric] inj_onI) (auto simp: g_def split: if_splits)    
    also have "\<dots> \<le> card {i. lrow \<le> i \<and> i < urow \<and> m (i, j) = x}"
      using j f by (intro card_mono) (auto simp: g_def)
    also have "\<dots> = count (mset (col m j)) x"
      by (simp add: count_conv_size_mset mset_col filter_image_mset)
    finally show ?thesis .
  qed

  show ?thesis
    unfolding clean_decomp_def
  proof (intro exI[of _ "lrow + size (I False)"] conjI ballI)
    show "lrow + size (I False) + (urow - lrow + 1) div 2 \<le> urow"
      using size_I[of False] lrow_le_urow by linarith
  next
    fix i assume i: "i \<in> {lrow..<lrow + size (I False)}"
    show "all0 (row (step2 m) i)"
    proof (intro all0_rowI)
      fix j assume j: "j \<in> {lcol..<ucol}"
      show "\<not>step2 m (i, j)"
        using i j size_I[of False] size_I_le[of j False]
        by (subst step2_bool) (auto simp: idxs_def)
    qed (use i size_I[of False] in auto)
  next
    fix i assume i: "i \<in> {lrow + size (I False) + (urow - lrow + 1) div 2..<urow}"
    show "all1 (row (step2 m) i)"
    proof (intro all1_rowI)
      fix j assume j: "j \<in> {lcol..<ucol}"

      have "size (I True) \<le> count (mset (col m j)) True"
        using j by (intro size_I_le) auto
      moreover have "size (I False + I True) = size (mset [0..<(urow - lrow) div 2])"
        unfolding I_def by (subst union_filter_mset_complement) auto
      hence "size (I True) + size (I False) = (urow - lrow) div 2"
        by simp
      moreover have "count (mset (col m j)) True + count (mset (col m j)) False =
                     size (mset (col m j))"
        by (simp add: size_conv_count_bool_mset)
      hence "count (mset (col m j)) True + count (mset (col m j)) False = urow - lrow"
        by simp
      ultimately have "count (mset (col m j)) False \<le> size (I False) + Suc (urow - lrow) div 2"
        by linarith
      with i have "lrow + count (mset (col m j)) False \<le> i"
        by simp
      thus "step2 m (i, j)"
        using i j by (subst step2_bool) (auto simp: idxs_def)
    qed (use i size_I[of False] in auto)
  qed auto
qed

lemma clean_decomp_step_aux:
  "clean_decomp ((urow - lrow + 1) div 2) (step m)"
  unfolding step_def o_def by (intro clean_decomp_step2 sorted_asc_desc_row_step1)

text \<open>
  We can now finally show that the number of non-clean rows halves in every step:
\<close>
lemma clean_decomp_step:
  assumes "clean_decomp n m"
  shows   "clean_decomp ((n + 1) div 2) (step m)"
proof -
  from assms obtain k where k:
    "lrow \<le> k" "k + n \<le> urow" "\<forall>i\<in>{lrow..<k}. all0 (row m i)" "\<forall>i\<in>{k+n..<urow}. all1 (row m i)"
    unfolding clean_decomp_def by metis
  interpret sub_shearsort_bool lrow urow lcol ucol k "k + n"
    by unfold_locales (use k lcol_le_ucol in auto)
  have idxs_subset: "sub.idxs \<subseteq> idxs"
    using k by (auto simp: sub.idxs_def idxs_def)

  have "sub.clean_decomp ((n + 1) div 2) (sub.step m)"
    using sub.clean_decomp_step_aux[of m] by simp
  then obtain k' where k':
    "k \<le> k'" "k' + (n + 1) div 2 \<le> k + n"
    "\<forall>i\<in>{k..<k'}. all0 (row (sub.step m) i)"
    "\<forall>i\<in>{k'+(n+1) div 2..<k + n}. all1 (row (sub.step m) i)"
    unfolding sub.clean_decomp_def by blast

  have "\<forall>i\<in>{lrow..<k'}. all0 (sub.row (step m) i)"
    using k'(3) k(3) by (auto simp flip: sub_step)
  moreover have "(\<forall>i\<in>{k' + (n + 1) div 2..<urow}. all1 (sub.row (step m) i))"
    using k'(4) k(4) by (auto simp flip: sub_step)
  moreover have "lrow \<le> k'" "k' + (n + 1) div 2 \<le> urow"
    using k(1,2) k'(1,2) by linarith+
  ultimately show ?thesis
    unfolding clean_decomp_def by metis
qed

text \<open>
  Moreover, if we have a matrix that has at most one non-clean row, applying one last step
  of shear sort leads to a snake-sorted matrix. This is because 

    \<^enum> \<^const>\<open>step1\<close> leaves the clean rows untouched and sorts the non-clean row (if it exists)
      in the correct order.

    \<^enum> \<^const>\<open>step2\<close> leaves the clean parts of the columns untouched, and since the non-clean part
      has height at most 1, it also leaves that part untouched.
\<close>
lemma snake_sorted_step_final:
  assumes "clean_decomp n m" and "n \<le> 1"
  shows   "snake_sorted (step m)"
proof -
  define n' where "n' = (n + 1) div 2"
  have "n' \<le> 1"
    using \<open>n \<le> 1\<close> unfolding n'_def by linarith
  have "clean_decomp n' (step m)"
    unfolding n'_def by (rule clean_decomp_step) fact
  from assms(1) obtain k where k: "k \<ge> lrow" "k + n \<le> urow"
     "\<And>i. i \<in> {lrow..<k} \<Longrightarrow> all0 (row m i)"
     "\<And>i. i \<in> {k + n..<urow} \<Longrightarrow> all1 (row m i)"
    unfolding clean_decomp_def by metis
  interpret sub_shearsort_bool lrow urow lcol ucol k "k + n"
    by unfold_locales (use k in auto)

  show ?thesis
    unfolding snake_sorted_def
  proof safe
    fix i assume "i \<in> {lrow..<urow}"
    thus "sorted_asc_desc (even i) (row (step m) i)"
      by (metis \<open>n \<le> 1\<close> comp_eq_dest_lhs nat_add_left_cancel_le
            sorted_asc_desc_row_step1 sub.step2_height_le_1 sub.step_def sub_step sub_step1)
  next
    fix i i' x y
    assume *: "lrow \<le> i" "i < i'" "i' < urow"
              "x \<in> set (row (step m) i)" "y \<in> set (row (step m) i')"
    have **: "row (step m) i = row m i" if "i \<noteq> k" for i
    proof -
      have "row (sub.step m) i = row m i"
        using that assms(2) by force
      thus ?thesis
        by (simp add: sub_step)
    qed

    from *(1-3) consider "i < k" | "i' > k"
      by linarith
    thus "x \<le> y"
    proof cases
      assume "i < k"
      hence "all0 (row m i)"
        using * by (intro k) auto
      thus "x \<le> y"
        using * \<open>i < k\<close> by (auto simp: all0_def **)
    next
      assume "i' > k"
      hence "all1 (row m i')"
        using * assms(2) by (intro k) auto
      thus "x \<le> y"
        using * \<open>i' > k\<close> by (auto simp: all1_def **)
    qed
  qed
qed

text \<open>
  It is now easy to show that shear sort is indeed correct for boolean matrices.
\<close>
lemma snake_sorted_shearsort_bool: "snake_sorted (shearsort m)"
proof -
  define div2 where "div2 = (\<lambda>x::nat. (x + 1) div 2)"
  define l where "l = ceillog2 (urow - lrow)"
  have "clean_decomp ((div2 ^^ l) (urow - lrow)) ((step ^^ l) m)"
  proof (induction l)
    case (Suc k)
    have "clean_decomp (((div2 ^^ k) (urow - lrow) + 1) div 2) (step ((step ^^ k) m))"
      by (intro clean_decomp_step Suc.IH)
    thus ?case by (simp add: div2_def)
  qed (auto intro: clean_decomp_initial)
  moreover have "(div2 ^^ l) (urow - lrow) \<le> 1"
    unfolding l_def div2_def by (rule funpow_div2_ceillog2_le_1)
  ultimately have "snake_sorted (step ((step ^^ l) m))"
    by (rule snake_sorted_step_final)
  thus ?thesis
    by (simp add: shearsort_def l_def)
qed

end


subsection \<open>Shearsort commutes with monotone functions\<close>

text \<open>
  To invoke the 0--1 principle, we must now prove that shear sort commutes with monotone functions.
  We will only show it for functions that return booleans, since that is all we need, but it
  could easily be shown the same way for a more general result type as well.
\<close>

context shearsort
begin

interpretation bool: shearsort_bool lrow urow lcol ucol
  by unfold_locales (fact lrow_le_urow lcol_le_ucol)+

context
  fixes f :: "'a \<Rightarrow> bool"
begin

lemma row_commute: "row (f \<circ> m) i = map f (row m i)"
  and col_commute: "col (f \<circ> m) i = map f (col m i)"
  by (simp_all add: row_def col_def)

lemma restrict_mat_commute:
  assumes "\<And>i j. (i, j) \<in> idxs \<Longrightarrow> f (m' (i, j)) = fm' (i, j)"
  shows   "bool.restrict_mat (f \<circ> m) fm' = f \<circ> restrict_mat m m'"
  using assms by (auto simp: restrict_mat_def bool.restrict_mat_def fun_eq_iff)

lemma step1_mono_commute: "mono f \<Longrightarrow> bool.step1 (f \<circ> m) = f \<circ> step1 m"
  unfolding step1_def bool.step1_def
  by (intro restrict_mat_commute) (auto simp: idxs_def sort_asc_desc_map_mono row_commute)

lemma step2_mono_commute: "mono f \<Longrightarrow> bool.step2 (f \<circ> m) = f \<circ> step2 m"
  unfolding step2_def bool.step2_def
  by (intro restrict_mat_commute) (auto simp: idxs_def sort_map_mono col_commute)

lemma step_mono_commute: "mono f \<Longrightarrow> bool.step (f \<circ> m) = f \<circ> step m"
  by (simp add: step_def bool.step_def step1_mono_commute step2_mono_commute)

lemma snake_aux_commute: "bool.snake_aux (f \<circ> m) lrow' = map f (snake_aux m lrow')"
  by (induction lrow' rule: snake_aux.induct;
      subst snake_aux.simps; subst bool.snake_aux.simps)
     (auto simp: row_commute rev_map simp del: o_apply)

lemma snake_commute: "bool.snake (f \<circ> m) = map f (snake m)"
  by (simp add: snake_def bool.snake_def snake_aux_commute)

lemma shearsort_mono_commute:
  assumes "mono f"
  shows   "bool.shearsort (f \<circ> m) = f \<circ> shearsort m"
proof -
  have "(bool.step ^^ k) (f \<circ> m) = f \<circ> (step ^^ k) m" for k
    by (induction k) (simp_all add: step_mono_commute assms del: o_apply
                               add: o_apply[of "bool.step"] o_apply[of step])
  from this[of "ceillog2 (urow - lrow) + 1"] show ?thesis
    unfolding shearsort_def bool.shearsort_def .
qed

end


subsection \<open>Final correctness theorem\<close>

text \<open>
  All that is left now is a routine application of the 0--1 principle.
\<close>
theorem snake_sorted_shearsort: "snake_sorted (shearsort m)"
proof (rule ccontr)
  define xs where "xs = snake (shearsort m)"
  assume "\<not>snake_sorted (shearsort m)"
  hence "\<not>sorted (snake (shearsort m))"
    by (simp add: sorted_snake_iff)
  then obtain i j where ij: "i < j" "j < length xs" "xs ! i > xs ! j"
    by (auto simp: sorted_iff_nth_mono_less xs_def)
  define f where "f = (\<lambda>x. x > xs ! j)"
  have [simp]: "mono f"
    by (auto simp: f_def mono_def)

  have "sorted (bool.snake (bool.shearsort (f \<circ> m)))"
    by (simp add: bool.sorted_snake_iff bool.snake_sorted_shearsort_bool)
  also have "bool.snake (bool.shearsort (f \<circ> m)) = map f xs"
    by (simp add: xs_def shearsort_mono_commute snake_commute)
  finally have "f (xs ! i) \<le> f (xs ! j)"
    using ij unfolding sorted_iff_nth_mono_less by auto
  hence "xs ! i \<le> xs ! j"
    by (auto simp: f_def)
  with ij(3) show False by simp
qed

end


subsection \<open>Refinement to lists\<close>

text \<open>
  Next, we define a refinement of matrices to lists of lists and show the correctness of
  the corresponding shear sort implementation. Note that this is not useful as an actual
  implementation in practice since the fact that we have to transpose the list of lists once
  in every step negates all the advantage of having a parallel algorithm.
\<close>
primrec step1_list :: "bool \<Rightarrow> 'a :: linorder list list \<Rightarrow> 'a list list" where
  "step1_list b [] = []"
| "step1_list b (xs # xss) = sort_asc_desc b xs # step1_list (\<not>b) xss"

definition step2_list :: "'a :: linorder list list \<Rightarrow> 'a list list"
  where "step2_list xss =
           (if xss = [] \<or> hd xss = [] then xss else transpose (map sort (transpose xss)))"

definition shearsort_list :: "bool \<Rightarrow> 'a :: linorder list list \<Rightarrow> 'a list list" where
  "shearsort_list b xss = ((step2_list \<circ> step1_list b) ^^ (ceillog2 (length xss) + 1)) xss"

primrec snake_list :: "bool \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "snake_list asc [] = []"
| "snake_list asc (xs # xss) = (if asc then xs else rev xs) @ snake_list (\<not>asc) xss"

lemma mset_snake_list: "mset (snake_list b xss) = mset (concat xss)"
  by (induction xss arbitrary: b) auto

definition (in shearsort) mat_of_list :: "'a list list \<Rightarrow> 'a mat"
  where "mat_of_list xss = (\<lambda>(i,j). xss ! (i - lrow) ! (j - lcol))"


text \<open>
  The following relator relates a matrix to a list of rows. It ensure that the dimensions
  and the entries are the same.
\<close>
definition (in shearsort) mat_list_rel :: "'a mat \<Rightarrow> 'a list list \<Rightarrow> bool" where
  "mat_list_rel m xss \<longleftrightarrow>
     length xss = urow - lrow \<and> (\<forall>xs\<in>set xss. length xs = ucol - lcol) \<and>
     (\<forall>i j. i < urow - lrow \<and> j < ucol - lcol \<longrightarrow> xss ! i ! j = m (lrow + i, lcol + j))"

lemma (in shearsort) mat_list_rel_transpose [intro]: 
  assumes "mat_list_rel m xss" "xss \<noteq> []"
  shows   "transpose.mat_list_rel (transpose_mat m) (transpose xss)"
proof -
  have "transpose xss = map (\<lambda>i. map (\<lambda>j. xss ! j ! i) [0..<length xss]) [0..<ucol - lcol]"
    using assms
    by (intro transpose_rectangle[where n = "ucol - lcol"]) (auto simp: mat_list_rel_def)
  thus ?thesis
    using assms by (auto simp: mat_list_rel_def transpose.mat_list_rel_def transpose_mat_def)
qed

lemma (in shearsort) mat_list_rel_row [intro]:
  assumes "mat_list_rel m xss" "i \<in> {lrow..<urow}"
  shows   "row m i = xss ! (i - lrow)"
  using assms unfolding row_def mat_list_rel_def by (intro nth_equalityI) auto

lemma (in shearsort) mat_list_rel_mset:
  assumes "mat_list_rel m xss"
  shows   "mset_mat m = (\<Sum>xs\<leftarrow>xss. mset xs)"
proof -
  define S where "S = (SIGMA i:{..<length xss}. {..<length (xss ! i)})"
  have "mset_mat m = image_mset m (mset_set ({lrow..<urow} \<times> {lcol..<ucol}))"
    by (simp add: mat_list_rel_def mset_mat_def idxs_def)
  also have "\<dots> = image_mset (\<lambda>(i,j). xss ! (i - lrow) ! (j - lcol))
                    (mset_set ({lrow..<urow} \<times> {lcol..<ucol}))"
    using lcol_le_ucol lrow_le_urow diff_less_mono
    by (intro image_mset_cong) (use assms in \<open>auto simp: mat_list_rel_def\<close>)
  also have "\<dots> = image_mset (\<lambda>(i,j). xss ! i ! j)
                    (image_mset (\<lambda>(i,j). (i - lrow, j - lcol))
                      (mset_set ({lrow..<urow} \<times> {lcol..<ucol})))"
    by (simp add: multiset.map_comp o_def case_prod_unfold)
  also have "image_mset (\<lambda>(i,j). (i - lrow, j - lcol)) (mset_set ({lrow..<urow} \<times> {lcol..<ucol})) =
               mset_set ((\<lambda>(i,j). (i - lrow, j - lcol)) ` ({lrow..<urow} \<times> {lcol..<ucol}))"
    by (rule image_mset_mset_set) (auto intro!: inj_onI)
  also have "bij_betw (\<lambda>(i,j). (i - lrow, j - lcol)) ({lrow..<urow} \<times> {lcol..<ucol}) 
              ({..<urow-lrow} \<times> {..<ucol-lcol})"
    by (rule bij_betwI[of _ _ _ "\<lambda>(i,j). (i + lrow, j + lcol)"]) auto
  hence "(\<lambda>(i,j). (i - lrow, j - lcol)) ` ({lrow..<urow} \<times> {lcol..<ucol}) =
             {..<urow-lrow} \<times> {..<ucol-lcol}"
    by (simp add: bij_betw_def)
  also have "{..<urow-lrow} \<times> {..<ucol-lcol} = S"
    unfolding S_def by (rule Sigma_cong) (use assms in \<open>simp_all add: mat_list_rel_def\<close> )
  also have "image_mset (\<lambda>(i,j). xss ! i ! j) (mset_set S) = (\<Sum>(i,j)\<in>#mset_set S. {#xss ! i ! j#})"
    by (simp add: case_prod_unfold)
  also have "\<dots> = (\<Sum>(i,j)\<in>S. {#xss ! i ! j#})"
    by (rule sum_unfold_sum_mset [symmetric])
  also have "\<dots> = (\<Sum>xs\<leftarrow>xss. \<Sum>x\<leftarrow>xs. {#x#})"
    unfolding S_def
    by (subst sum.Sigma [symmetric])
       (auto simp: atLeast0LessThan sum.list_conv_set_nth simp del: sum_list_singleton_mset)
  also have "\<dots> = (\<Sum>xs\<leftarrow>xss. mset xs)"
    by simp
  finally show ?thesis .
qed

lemma (in shearsort) mat_list_rel_of_list:
  assumes "length xss = urow - lrow" "\<And>xs. xs \<in> set xss \<Longrightarrow> length xs = ucol - lcol"
  shows   "mat_list_rel (mat_of_list xss) xss"
  using assms by (auto simp: mat_list_rel_def mat_of_list_def)

lemma (in shearsort) mset_mat_of_list:
  assumes "length xss = urow - lrow" "\<And>xs. xs \<in> set xss \<Longrightarrow> length xs = ucol - lcol"
  shows   "mset_mat (mat_of_list xss) = (\<Sum>xs\<leftarrow>xss. mset xs)"
  using mat_list_rel_mset[OF mat_list_rel_of_list[OF assms]] by simp
    

context shearsort
begin

lemma mat_list_rel_col [intro]:
  assumes "mat_list_rel m xss" "j \<in> {lcol..<ucol}" "xss \<noteq> []"
  shows   "col m j = transpose xss ! (j - lcol)"
  using transpose.mat_list_rel_row[OF mat_list_rel_transpose[OF assms(1,3)] assms(2)] by simp

lemma length_step1_list [simp]: "length (step1_list b xss) = length xss"
  by (induction xss arbitrary: b) auto

lemma nth_step1_list:
  "i < length xss \<Longrightarrow> step1_list b xss ! i = sort_asc_desc (b = even i) (xss ! i)"
proof -
  have [simp]: "(\<not>b1) = b2 \<longleftrightarrow> b1 = (\<not>b2)" for b1 b2
    by auto
  show ?thesis if "i < length xss"
    using that by (induction xss arbitrary: b i) (auto simp: nth_Cons split: nat.splits)
qed

lemma mat_list_rel_step1:
  assumes "mat_list_rel m xss"
  shows   "mat_list_rel (step1 m) (step1_list (even lrow) xss)"
  using assms mat_list_rel_row[OF assms]
  unfolding mat_list_rel_def
  by (force simp: step1_def nth_step1_list restrict_mat_def set_conv_nth idxs_def)

lemma mat_list_rel_step2:
  assumes [intro]: "mat_list_rel m xss"
  shows   "mat_list_rel (step2 m) (step2_list xss)"
proof (cases "lcol \<ge> ucol \<or> lrow \<ge> urow")
  case False
  define m' xss' where "m' = transpose_mat m" and "xss' = transpose xss"
  define step2' where
    "step2' = transpose.restrict_mat m' (\<lambda>(i, j). sort (transpose.row m' i) ! (j - lrow))"

  from False assms have "xss \<noteq> []"
    by (auto simp: mat_list_rel_def not_le set_conv_nth hd_conv_nth)
  from False assms this have "hd xss \<noteq> []"
    by (cases xss) (auto simp: mat_list_rel_def)
  have "xss' \<noteq> []"
    using \<open>xss \<noteq> []\<close> \<open>hd xss \<noteq> []\<close> unfolding xss'_def by (subst transpose_empty) auto

  have *: "transpose.mat_list_rel m' xss'"
    using \<open>xss \<noteq> []\<close> unfolding m'_def xss'_def by blast
  hence "transpose.mat_list_rel step2' (map sort xss')"
    unfolding step2'_def using transpose.mat_list_rel_row[OF *]
    by (auto simp: transpose.mat_list_rel_def transpose.restrict_mat_def transpose.idxs_def)
  hence "mat_list_rel (transpose_mat step2') (transpose (map sort xss'))"
    using \<open>xss' \<noteq> []\<close> by (intro transpose.mat_list_rel_transpose) auto
  also have "transpose_mat step2' = step2 m"
    by (simp add: step2_def step2'_def restrict_mat_def transpose.restrict_mat_def
                  transpose.idxs_def idxs_def transpose_mat_def fun_eq_iff m'_def
                  transpose.row_def col_def)
  also have "transpose (map sort xss') = step2_list xss"
    using \<open>xss \<noteq> []\<close> \<open>hd xss \<noteq> []\<close> by (simp add: step2_list_def xss'_def)
  finally show ?thesis .
qed (use assms in \<open>auto simp: mat_list_rel_def step2_list_def\<close>)

lemma mat_list_rel_step:
  "mat_list_rel m xss \<Longrightarrow> mat_list_rel (step m) (step2_list (step1_list (even lrow) xss))"
  by (simp add: step_def mat_list_rel_step1 mat_list_rel_step2)

lemma mat_list_rel_shearsort:
  assumes "mat_list_rel m xss"
  shows   "mat_list_rel (shearsort m) (shearsort_list (even lrow) xss)"
proof -
  define l where "l = ceillog2 (urow - lrow) + 1"
  have "mat_list_rel ((step ^^ l) m) (((step2_list \<circ> step1_list (even lrow)) ^^ l) xss)"
    using assms by (induction l) (auto simp: mat_list_rel_step)
  moreover have "length xss = urow - lrow"
    using assms by (simp add: mat_list_rel_def)
  ultimately show ?thesis
    by (simp add: shearsort_list_def shearsort_def l_def)
qed

lemma mat_list_rel_snake_aux:
  assumes "mat_list_rel m xss" "lrow' \<in> {lrow..urow}"
  shows   "snake_aux m lrow' = snake_list (even lrow') (drop (lrow' - lrow) xss)"
  using assms(2)
proof (induction lrow' rule: snake_aux.induct)
  case (1 lrow')
  have len: "length xss = urow - lrow"
    using assms(1) by (auto simp: mat_list_rel_def)

  show ?case
  proof (cases "lrow' < urow")
    case False
    thus ?thesis using len
      by (subst snake_aux.simps) auto
  next
    case True
    hence "snake_aux m lrow' =
             (if even lrow' then row m lrow' else rev (row m lrow')) @ snake_aux m (Suc lrow')"
      by (subst snake_aux.simps) simp
    also have "snake_aux m (Suc lrow') = snake_list (odd lrow') (drop (Suc (lrow' - lrow)) xss)"
      using True "1.prems" by (subst 1) (auto simp: Suc_diff_le)
    also have "(if even lrow' then row m lrow' else rev (row m lrow')) @ \<dots> =
               snake_list (even lrow') (drop (lrow' - lrow) xss)"
      using mat_list_rel_row[OF assms(1), of lrow'] "1.prems" True
      by (subst (2) Cons_nth_drop_Suc [symmetric]) (simp_all add: len)
    finally show ?thesis .
  qed
qed

lemma mat_list_rel_snake:
  assumes "mat_list_rel m xss"
  shows   "snake m = snake_list (even lrow) xss"
  using mat_list_rel_snake_aux[OF assms, of lrow] lrow_le_urow by (auto simp: snake_def)

end


text \<open>
  The final correctness theorem for shear sort on lists of lists:
\<close>
theorem shearsort_list_correct:
  assumes "\<And>xs. xs \<in> set xss \<Longrightarrow> length xs = ncols"
  shows   "mset (concat (shearsort_list True xss)) = mset (concat xss)"
    and   "sorted (snake_list True (shearsort_list True xss))"
proof -
  define nrows where "nrows = length xss"
  interpret shearsort 0 nrows 0 ncols
    by standard auto
  define m where "m = mat_of_list xss"
  have m: "mat_list_rel m xss"
    unfolding m_def
    by (rule mat_list_rel_of_list) (use assms in \<open>auto simp: nrows_def\<close>)
  hence m': "mat_list_rel (shearsort m) (shearsort_list True xss)"
    using mat_list_rel_shearsort[of m xss] by simp
  hence "sum_list (map mset (shearsort_list True xss)) = mset_mat (shearsort m)"
    by (rule mat_list_rel_mset [symmetric])
  also have "\<dots> = mset_mat m"
    by simp
  also have "\<dots> = mset (concat xss)"
    unfolding m_def
    by (subst mset_mat_of_list) (use assms in \<open>auto simp: nrows_def mset_concat\<close>)
  finally show "mset (concat (shearsort_list True xss)) = mset (concat xss)"
    by (simp add: mset_concat)

  have "sorted (snake (shearsort m))"
    by (simp add: sorted_snake_iff snake_sorted_shearsort)
  also have "snake (shearsort m) = snake_list True (shearsort_list True xss)"
    using mat_list_rel_snake[OF m'] by simp
  finally show "sorted (snake_list True (shearsort_list True xss))" .
qed

value "shearsort_list True [[5, 8, 2], [9, 1, 7], [3, 6, 4 :: int]]"

end