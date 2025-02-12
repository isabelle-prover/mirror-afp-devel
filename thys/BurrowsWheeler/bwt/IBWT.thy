theory IBWT
  imports BWT_SA_Corres
begin

section "Inverse Burrows-Wheeler Transform"

text \<open>Inverse BWT algorithm obtained from \<^cite>\<open>"Ferragina_FOCS_2000"\<close>\<close>

subsection \<open>Abstract Versions\<close>

context Suffix_Array_General begin

text \<open>These are abstract because they use additional information about the original string and its
      suffix array.\<close>

text \<open>Definition 3.15 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Abstract LF-Mapping\<close>
fun lf_map_abs :: "'a list \<Rightarrow> nat \<Rightarrow> nat" 
where
"lf_map_abs s i = select (sort s) (bwt_sa s ! i) (rank (bwt_sa s) (bwt_sa s ! i) i)"

text \<open>Definition 3.16 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Inverse BWT Permutation\<close>
fun ibwt_perm_abs :: "nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat list" 
where
"ibwt_perm_abs 0 _ _ = []" |
"ibwt_perm_abs (Suc n) s i = ibwt_perm_abs n s (lf_map_abs s i) @ [i]"

end (* of context *)

subsection \<open>Concrete Versions\<close>

text \<open>These are concrete because they only rely on the BWT-transformed sequence without any
      additional information.\<close>

text \<open>Definition 3.14 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Inverse BWT - LF-mapping\<close>
fun lf_map_conc ::  "('a  :: {linorder, order_bot}) list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" 
  where
    "lf_map_conc ss bs i = (select ss (bs ! i) 0) + (rank bs (bs ! i) i)"

(* Concrete version of the inverse BWT permutation *)
fun ibwt_perm_conc :: "nat \<Rightarrow> ('a  :: {linorder, order_bot}) list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat list" 
  where
    "ibwt_perm_conc 0 _ _ _ = []" |
    "ibwt_perm_conc (Suc n) ss bs i = ibwt_perm_conc n ss bs (lf_map_conc ss bs i) @ [i]"

text \<open>Definition 3.14 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Inverse BWT - Inverse BWT Rotated Subsequence\<close>
fun ibwtn :: "nat \<Rightarrow> ('a  :: {linorder, order_bot}) list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" 
  where
    "ibwtn 0 _ _ _ = []" |
    "ibwtn (Suc n) ss bs i = ibwtn n ss bs (lf_map_conc ss bs i) @ [bs ! i]"

text \<open>Definition 3.14 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Inverse BWT\<close>
fun ibwt :: "('a  :: {linorder, order_bot}) list \<Rightarrow> 'a list"
  where
    "ibwt bs = ibwtn (length bs) (sort bs) bs (select bs bot 0)"


section "List Filter"

lemma filter_nth_app_upt:
  "filter (\<lambda>i. P (xs ! i)) [0..<length xs] = filter (\<lambda>i. P ((xs @ ys) ! i)) [0..<length xs]"
  by (induct xs arbitrary: ys rule: rev_induct; simp)

lemma filter_eq_nth_upt:
  "filter P xs = map (\<lambda>i. xs ! i) (filter (\<lambda>i. P (xs ! i)) [0..<length xs])"
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  have "?case \<longleftrightarrow> 
        map ((!) xs) (filter (\<lambda>i. P (xs ! i)) [0..<length xs]) =
        map ((!) (xs @ [x])) (filter (\<lambda>i. P ((xs @ [x]) ! i)) [0..<length xs])"
    using snoc by simp
  moreover
  have "map ((!) (xs @ [x])) (filter (\<lambda>i. P ((xs @ [x]) ! i)) [0..<length xs]) = 
        map ((!) (xs @ [x])) (filter (\<lambda>i. P (xs ! i)) [0..<length xs])"
    using filter_nth_app_upt[of P xs "[x]"] by simp
  moreover
  have "map ((!) xs) (filter (\<lambda>i. P (xs ! i)) [0..<length xs]) =
        map ((!) (xs @ [x])) (filter (\<lambda>i. P (xs ! i)) [0..<length xs])"
    by (clarsimp simp: nth_append)
  ultimately show ?case
    by argo
qed

lemma distinct_filter_nth_upt:
  "distinct (filter (\<lambda>i. P (xs ! i)) [0..<length xs])"
  by simp

lemma filter_nth_upt_set:
  "set (filter (\<lambda>i. P (xs ! i)) [0..<length xs]) = {i. i < length xs \<and> P (xs ! i)}"
  using set_filter by simp

lemma filter_length_upt:
  "length (filter (\<lambda>i. P (xs ! i)) [0..<length xs]) = card {i. i < length xs \<and> P (xs ! i)}"
  by (metis distinct_card distinct_filter_nth_upt filter_nth_upt_set)

lemma perm_filter_length:
  "xs <~~> ys \<Longrightarrow>
   length (filter (\<lambda>i. P (xs ! i)) [0..<length xs])
    = length (filter (\<lambda>i. P (ys ! i)) [0..<length ys])"
  by (metis filter_eq_nth_upt length_map mset_filter perm_length)

section "Verification of the Inverse Burrows-Wheeler Transform"

context Suffix_Array_General begin

subsection "LF-Mapping Simple Properties"

lemma lf_map_abs_less_length:
  fixes s :: "'a  list"
  fixes i j :: nat
  assumes  "i < length s"
shows "lf_map_abs s i < length s"
proof -
  let ?v = "bwt_sa s ! i"
  let ?r = "rank (bwt_sa s) ?v i"
  let ?i = "lf_map_abs s i"

  have "?i = select (sort s) ?v ?r"
    by (metis lf_map_abs.simps)

  have "?r < count_list (bwt_sa s) ?v"
    by (simp add: assms bwt_sa_length rank_upper_bound)
  moreover
  have "bwt_sa s <~~> sort s"
    using bwt_sa_perm by auto
  ultimately have "?r < count_list (sort s) ?v"
    by (metis (no_types, lifting) count_list_perm)
  with rank_length[of "sort s" ?v, symmetric]
  have "?r < rank (sort s) ?v (length s)"
    by simp
  with select_upper_bound
  have "select (sort s) ?v ?r < length (sort s)"
    by metis
  with `?i = select (sort s) ?v ?r`
  show ?thesis
    by (metis length_sort)
qed

corollary lf_map_abs_less_length_funpow:
  fixes s :: "'a list"
  fixes i j :: nat
  assumes "i < length s"
shows "((lf_map_abs s)^^k) i < length s"
proof (induct k)
  case 0
  then show ?case
    using assms by auto
next
  case (Suc k)
  then show ?case
    by (metis comp_apply funpow.simps(2) lf_map_abs_less_length)
qed

lemma lf_map_abs_equiv:
  fixes s :: "('a  :: {linorder, order_bot}) list"
  fixes i r :: nat
  fixes v :: 'a
  assumes "i < length (bwt_sa s)"
  and     "v = bwt_sa s ! i"
  and     "r = rank (bwt_sa s) v i"
shows "lf_map_abs s i = card {j. j < length (bwt_sa s) \<and> bwt_sa s ! j < v} + r"
proof -

  have "\<exists>k. length s = Suc k"
    by (metis assms(1) bwt_sa_length less_nat_zero_code not0_implies_Suc)
  then obtain n where
    "length s = Suc n"
    by blast

  let ?P = "(\<lambda>x. x < v)"

  have "lf_map_abs s i = select (sort s) v r"
    by (metis assms(2) assms(3) lf_map_abs.simps)
  moreover
  from rank_upper_bound[OF assms(1) assms(2)[symmetric]] assms(3)
  have "r < count_list (bwt_sa s) v"
    by simp
  hence "r < count_list (sort s) v"
    using count_list_perm[OF trans[OF bwt_sa_perm sort_perm]]  by simp
  with sorted_select[of "sort s" r v]
  have "select (sort s) v r = card {j. j < length (sort s) \<and> sort s ! j < v} + r"
    by simp
  moreover
  have "length (filter (\<lambda>x. ?P (sort s ! x)) [0..<length (sort s)])
          = card {j. j < length (sort s) \<and> sort s ! j < v}"
    using filter_length_upt[of ?P "sort s"] by simp
  moreover
  have "length (filter (\<lambda>x. ?P (bwt_sa s ! x)) [0..<length (bwt_sa s)])
          = card {j. j < length (bwt_sa s) \<and> bwt_sa s ! j < v}"
    using filter_length_upt[of ?P "bwt_sa s"] by simp
  ultimately show ?thesis
    using perm_filter_length[OF trans[OF bwt_sa_perm sort_perm], of ?P s]
    by presburger
qed

subsection "LF-Mapping Correctness"

lemma sa_lf_map_abs:
  assumes "valid_list s"
  and     "i < length s"
shows "sa s ! (lf_map_abs s i) = (sa s ! i + length s - Suc 0) mod (length s)"
proof -
  let ?v = "bwt_sa s ! i"
  let ?r = "rank (bwt_sa s) ?v i"
  let ?i = "lf_map_abs s i"

  have "?i = select (sort s) ?v ?r"
    by (metis lf_map_abs.simps)

  from lf_map_abs_less_length[OF assms(2)]
  have "?i < length s" .
  hence "select (sort s) ?v ?r < length (sort s)"
    by (metis length_sort lf_map_abs.simps)
  with rank_select
  have "rank (sort s) ?v (select (sort s) ?v ?r) = ?r"
    by metis
  with `?i = select (sort s) ?v ?r`
  have "rank (sort s) ?v ?i = ?r"
    by simp
  moreover
  have "?i < length s"
    using \<open>select (sort s) ?v ?r < length (sort s)\<close> \<open>?i = select (sort s) ?v ?r\<close> by auto
  moreover
  {
    from select_nth[of "sort s" ?v ?r ?i]
    have "sort s ! lf_map_abs s i = bwt_sa s ! i"
      by (metis \<open>?i = select (sort s) ?v ?r\<close> calculation(2) length_sort)
    moreover
    have "s ! (sa s ! ?i) = sort s ! ?i"
      using `?i < length s` sort_sa_nth by presburger
    ultimately have "s ! (sa s ! ?i) = ?v"
      by presburger
  }
  ultimately have "sa s ! ?i = bwt_perm s ! i"
    using rank_same_sa_bwt_perm[OF assms(1)_ assms(2), of ?i ?v]
    by blast
  then show ?thesis
    using bwt_perm_nth[OF assms(2)]
    by simp
qed

text \<open>Theorem 3.18 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Abstract LF-Mapping Correctness\<close>
corollary bwt_perm_lf_map_abs:
  fixes s :: "('a  :: {linorder, order_bot}) list"
  fixes i :: nat
  assumes "valid_list s"
  and     "i < length s"
shows "bwt_perm s ! (lf_map_abs s i) = (bwt_perm s ! i + length s - Suc 0) mod (length s)"
  by (metis One_nat_def bwt_perm_nth assms(1,2) lf_map_abs_less_length sa_lf_map_abs)

subsection "Backwards Inverse BWT Simple Properties"

lemma ibwt_perm_abs_length:
  fixes s :: "'a list"
  fixes n i :: nat
  shows "length (ibwt_perm_abs n s i) = n"
  by (induct n arbitrary: i; simp)

lemma ibwt_perm_abs_nth:
  fixes s :: "'a list"
  fixes k n i :: nat
  assumes "k \<le> n"
  shows "(ibwt_perm_abs (Suc n) s i) ! k = ((lf_map_abs s)^^(n-k)) i"
using assms
proof (induct n arbitrary: i k)
  case 0
  then show ?case
    by simp
next
  case (Suc n i k)
  note IH = this

  have A: "ibwt_perm_abs (Suc (Suc n)) s i = ibwt_perm_abs (Suc n) s (lf_map_abs s i) @ [i]"
    by simp

  have "k \<le> n \<Longrightarrow> ?case"
  proof -
    assume "k \<le> n"
    with IH(1)[of k "lf_map_abs s i"]
    have "ibwt_perm_abs (Suc n) s (lf_map_abs s i) ! k = (lf_map_abs s ^^ (Suc n - k)) i"
      by (metis Suc_diff_le comp_apply funpow.simps(2) funpow_swap1)
    then show ?thesis
      by (metis \<open>k \<le> n\<close> A ibwt_perm_abs_length le_imp_less_Suc nth_append)
  qed
  moreover
  have "k = Suc n \<Longrightarrow> ?case"
  proof -
    assume "k = Suc n"
    with ibwt_perm_abs_length[of "Suc (Suc n)" s i] A
    have "ibwt_perm_abs (Suc (Suc n)) s i ! k = i"
      by (metis ibwt_perm_abs_length nth_append_length)
    moreover
    have "(lf_map_abs s ^^ (Suc n - k)) i = i"
      by (simp add: \<open>k = Suc n\<close>)
    ultimately show ?thesis
      by presburger
  qed
  ultimately show ?case
    using Suc.prems le_Suc_eq by blast
qed

corollary ibwt_perm_abs_alt_nth:
  fixes s :: "'a list"
  fixes n i k :: nat
  assumes "k < n"
  shows "(ibwt_perm_abs n s i) ! k = ((lf_map_abs s)^^(n - Suc k)) i"
  by (metis assms add_diff_cancel_left' diff_diff_left le_add1 less_imp_Suc_add plus_1_eq_Suc
            ibwt_perm_abs_nth)

lemma ibwt_perm_abs_nth_le_length:
  fixes s :: "'a list"
  fixes n i k :: nat
  assumes "i < length s"
  assumes "k < n"
  shows "(ibwt_perm_abs n s i) ! k < length s"
  using assms ibwt_perm_abs_alt_nth lf_map_abs_less_length_funpow by force

lemma ibwt_perm_abs_map_ver:
  "ibwt_perm_abs n s i = map (\<lambda>x. ((lf_map_abs s)^^x) i) (rev [0..<n])"
proof (intro list_eq_iff_nth_eq[THEN iffD2] conjI allI impI)
  show "length (ibwt_perm_abs n s i) = length (map (\<lambda>x. (lf_map_abs s ^^ x) i) (rev [0..<n]))"
    by (simp add: ibwt_perm_abs_length)
next
  fix j
  assume "j < length (ibwt_perm_abs n s i)"
  hence "j < n"
    by (simp add: ibwt_perm_abs_length)

  have "map (\<lambda>x. (lf_map_abs s ^^ x) i) (rev [0..<n]) ! j =
        (\<lambda>x. (lf_map_abs s ^^ x) i) (rev [0..<n] ! j)"
    by (simp add: \<open>j < n\<close>)
  moreover
  have "(\<lambda>x. (lf_map_abs s ^^ x) i) (rev [0..<n] ! j) = (lf_map_abs s ^^ (n - Suc j)) i"
    by (metis \<open>j < n\<close> add_cancel_right_left diff_Suc_less diff_zero length_greater_0_conv length_upt 
              less_nat_zero_code nth_upt rev_nth)
  ultimately show "ibwt_perm_abs n s i ! j = map (\<lambda>x. (lf_map_abs s ^^ x) i) (rev [0..<n]) ! j"
    using ibwt_perm_abs_alt_nth[OF \<open>j < n\<close>, of s i] by presburger
qed

subsection "Backwards Inverse BWT Correctness"

lemma inc_one_bounded_sa_ibwt_perm_abs:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i n :: nat
  assumes "valid_list s"
  and     "i < length s"
shows "inc_one_bounded (length s) (map ((!) (sa s)) (ibwt_perm_abs n s i))"
      (is "inc_one_bounded ?n ?xs")
  unfolding inc_one_bounded_def
proof (safe)
  fix j
  assume "Suc j < length (map ((!) (sa s)) (ibwt_perm_abs n s i))"
  hence "Suc j < n"
    by (simp add: ibwt_perm_abs_length)
  hence "\<exists>k. n = Suc k"
    using less_imp_Suc_add by blast
  then obtain k where
    "n = Suc k"
    by blast

  let ?i = "((lf_map_abs s)^^(k - Suc j)) i"
  have "ibwt_perm_abs n s i ! Suc j = ?i"
    by (metis \<open>Suc j < n\<close> \<open>n = Suc k\<close> less_Suc_eq_le ibwt_perm_abs_nth)
  moreover
  {
    have "ibwt_perm_abs n s i ! j = ((lf_map_abs s)^^(k - j)) i"
      by (metis Suc_less_SucD \<open>Suc j < n\<close> \<open>n = Suc k\<close> nless_le ibwt_perm_abs_nth)
    moreover
    have "((lf_map_abs s)^^(k - j)) i = lf_map_abs s ?i"
      using \<open>Suc j < n\<close> \<open>n = Suc k\<close> less_imp_Suc_add by fastforce
    ultimately have "ibwt_perm_abs n s i ! j = lf_map_abs s ?i"
      by presburger
  }
  moreover
  {
    have "?i < length s"
      by (simp add: assms lf_map_abs_less_length_funpow)
    with sa_lf_map_abs[OF assms(1), of ?i]
    have "sa s ! lf_map_abs s ?i = (sa s ! ?i + length s - Suc 0) mod length s"
      by fastforce
    hence "Suc (sa s ! lf_map_abs s ?i) mod length s
            = Suc ((sa s ! ?i + length s - Suc 0) mod length s) mod length s"
      by simp
    moreover
    have "Suc ((sa s ! ?i + length s - Suc 0) mod length s) mod length s = sa s ! ?i"
      using \<open>?i < length s\<close> assms(1) mod_Suc_eq sa_nth_ex valid_list_length by fastforce
    ultimately have "sa s ! ?i = Suc (sa s ! lf_map_abs s ?i) mod length s"
      by presburger
  }
  ultimately have
    "sa s ! (ibwt_perm_abs n s i ! Suc j) = Suc (sa s ! (ibwt_perm_abs n s i ! j)) mod length s"
    by presburger
  then show 
    "map ((!) (sa s)) (ibwt_perm_abs n s i) ! Suc j = 
      Suc (map ((!) (sa s)) (ibwt_perm_abs n s i) ! j) mod length s"
    using \<open>Suc j < length (map ((!) (sa s)) (ibwt_perm_abs n s i))\<close> by auto
next
  fix j
  assume "j < length (map ((!) (sa s)) (ibwt_perm_abs n s i))"
  hence "j < n"
    by (simp add: ibwt_perm_abs_length)
  hence"ibwt_perm_abs n s i ! j = ((lf_map_abs s)^^(n - Suc j)) i"
    using ibwt_perm_abs_alt_nth by blast
  moreover
  have "((lf_map_abs s)^^(n - Suc j)) i < length s"
    using assms lf_map_abs_less_length_funpow by blast
  hence "sa s ! (((lf_map_abs s)^^(n - Suc j)) i) < length s"
    using sa_nth_ex by blast
  ultimately have "sa s ! (ibwt_perm_abs n s i ! j) < length s"
    by presburger
  then show "map ((!) (sa s)) (ibwt_perm_abs n s i) ! j < length s"
    by (simp add: \<open>j < n\<close> ibwt_perm_abs_length)
qed

corollary is_rot_sublist_sa_ibwt_perm_abs:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i n :: nat
  assumes "valid_list s"
  and     "i < length s"
  and     "n \<le> length s"
shows "is_rot_sublist [0..<length s] (map ((!) (sa s)) (ibwt_perm_abs n s i))"
  by (simp add: assms inc_one_bounded_is_rot_sublist inc_one_bounded_sa_ibwt_perm_abs
                ibwt_perm_abs_length)

lemma inc_one_bounded_bwt_perm_ibwt_perm_abs:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i n :: nat
  assumes "valid_list s"
  and     "i < length s"
shows "inc_one_bounded (length s) (map ((!) (bwt_perm s)) (ibwt_perm_abs n s i))"
  unfolding inc_one_bounded_def
proof safe
  fix j
  assume "Suc j < length (map ((!) (bwt_perm s)) (ibwt_perm_abs n s i))"
  hence "Suc j < n"
    by (simp add: ibwt_perm_abs_length)
  hence "\<exists>k. n = Suc k"
    using less_imp_Suc_add by auto
  then obtain k where
    "n = Suc k"
    by blast

  let ?i = "((lf_map_abs s)^^(k - Suc j)) i"
  from ibwt_perm_abs_nth[of "Suc j" k s i]
  have "ibwt_perm_abs n s i ! Suc j = ?i"
    using \<open>Suc j < n\<close> \<open>n = Suc k\<close> less_Suc_eq_le by blast
  moreover
  {
    have "ibwt_perm_abs n s i ! j = ((lf_map_abs s)^^(k - j)) i"
      by (metis Suc_less_SucD \<open>Suc j < n\<close> \<open>n = Suc k\<close> nless_le ibwt_perm_abs_nth)
    moreover
    have "((lf_map_abs s)^^(k - j)) i = lf_map_abs s ?i"
      using \<open>Suc j < n\<close> \<open>n = Suc k\<close> less_imp_Suc_add by fastforce
    ultimately have "ibwt_perm_abs n s i ! j = lf_map_abs s ?i"
      by presburger
  }
  moreover
  {
    have "?i < length s"
      by (simp add: assms lf_map_abs_less_length_funpow)
    with bwt_perm_lf_map_abs[OF assms(1), of ?i]
    have "bwt_perm s ! lf_map_abs s ?i = (bwt_perm s ! ?i + length s - Suc 0) mod length s"
      by blast
    hence "Suc (bwt_perm s ! lf_map_abs s ?i) mod length s =
            Suc ((bwt_perm s ! ?i + length s - Suc 0) mod length s) mod length s"
      by presburger
    moreover
    from valid_list_length_ex[OF assms(1)]
    obtain n where
      "length s = Suc n"
      by blast
    hence "Suc ((bwt_perm s ! ?i + length s - Suc 0) mod length s) mod length s =
            bwt_perm s ! ?i"
      by (metis (no_types, lifting) Suc_pred bwt_perm_nth \<open>?i < length s\<close> add_gr_0 assms(1)
                                    mod_Suc_eq mod_add_self2 mod_mod_trivial valid_list_length)
    ultimately have "bwt_perm s ! ?i = Suc (bwt_perm s ! lf_map_abs s ?i) mod length s"
      by presburger
  }
  ultimately have "bwt_perm s ! (ibwt_perm_abs n s i ! Suc j) =
                     Suc (bwt_perm s ! (ibwt_perm_abs n s i ! j)) mod length s"
    by presburger
  then show "map ((!) (bwt_perm s)) (ibwt_perm_abs n s i) ! Suc j =
          Suc (map ((!) (bwt_perm s)) (ibwt_perm_abs n s i) ! j) mod length s"
    using \<open>Suc j < length (map ((!) (bwt_perm s)) (ibwt_perm_abs n s i))\<close> by auto
next
  fix j
  assume "j < length (map ((!) (bwt_perm s)) (ibwt_perm_abs n s i))"
  hence "j < n"
    by (simp add: ibwt_perm_abs_length)
  hence "\<exists>k. n = Suc k"
    using less_imp_Suc_add by blast
  then obtain k where
    "n = Suc k"
    by blast
  hence "ibwt_perm_abs n s i ! j = ((lf_map_abs s)^^(k - j)) i"
    by (metis \<open>j < n\<close> less_Suc_eq_le ibwt_perm_abs_nth)
  moreover
  have "((lf_map_abs s)^^(k - j)) i < length s"
    using assms lf_map_abs_less_length_funpow by blast
  hence "bwt_perm s ! ((lf_map_abs s)^^(k - j)) i < length s"
    using map_bwt_indexes_perm perm_nth_ex by blast
  ultimately have "bwt_perm s ! (ibwt_perm_abs n s i ! j) < length s"
    by presburger
  then show "map ((!) (bwt_perm s)) (ibwt_perm_abs n s i) ! j < length s"
    by (simp add: \<open>j < n\<close> ibwt_perm_abs_length)
qed

text \<open>Theorem 3.19 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Abstract Inverse BWT Permutation Rotated Sub-list\<close>
corollary is_rot_sublist_bwt_perm_ibwt_perm_abs:
  fixes s :: "('a :: {linorder, order_bot}) list"
  fixes i n :: nat
  assumes "valid_list s"
  and     "i < length s"
  and     "n \<le> length s"
  shows "is_rot_sublist [0..<length s] (map ((!) (bwt_perm s)) (ibwt_perm_abs n s i))"
  by (simp add: assms inc_one_bounded_is_rot_sublist inc_one_bounded_bwt_perm_ibwt_perm_abs
                ibwt_perm_abs_length)

lemma bwt_ibwt_perm_sa_lookup_idx:
  assumes "valid_list s"
  shows "map ((!) (bwt_perm s)) (ibwt_perm_abs (length s) s (select (bwt_sa s) bot 0))
          = [0..<length s]"
proof -
  from valid_list_length_ex[OF assms]
  obtain n where
    "length s = Suc n"
    by blast

  let ?i = "select (bwt_sa s) bot 0"
  let ?xs = "ibwt_perm_abs (length s) s ?i"

  have "bot \<in> set s"
    by (metis assms in_set_conv_decomp valid_list_ex_def)
  hence "bot \<in> set (bwt_sa s)"
    by (metis bwt_sa_perm perm_set_eq)
  hence "count_list (bwt_sa s) bot > 0"
    by (meson count_in)
  hence "0 < rank (bwt_sa s) bot (length (bwt_sa s))"
    by (metis rank_length)
  hence "?i < length (bwt_sa s)"
    by (meson select_upper_bound)
  hence "?i < length s"
    by (metis bwt_sa_length)
  with is_rot_sublist_bwt_perm_ibwt_perm_abs[OF assms, of ?i "length s"] `length s = Suc n`
  have "is_rot_sublist [0..<Suc n] (map ((!) (bwt_perm s)) ?xs)"
    by (metis nle_le)
  moreover
  have "length (map ((!) (bwt_perm s)) ?xs) = Suc n"
    by (metis \<open>length s = Suc n\<close> length_map ibwt_perm_abs_length)
  moreover
  {
    have "(map ((!) (bwt_perm s)) ?xs) ! n = bwt_perm s ! ?i"
      by (simp add: \<open>length s = Suc n\<close> nth_append ibwt_perm_abs_length)
    moreover
    have "bwt_sa s ! ?i = bot"
      by (simp add: \<open>?i < length (bwt_sa s)\<close> select_nth_alt)
    hence "bwt_perm s ! ?i = n"
      by (metis \<open>length s = Suc n\<close> \<open>?i < length s\<close> antisym_conv3 assms bwt_perm_nth
                bwt_perm_s_nth diff_Suc_1 mod_less_divisor not_less_eq valid_list_def)
    ultimately
    have "(map ((!) (bwt_perm s)) ?xs) ! n = n"
      by blast
  }
  ultimately show ?thesis
    using is_rot_sublist_upt_eq_upt_last[of n "map ((!) (bwt_perm s)) ?xs"]
    by (metis \<open>length s = Suc n\<close>)
qed

lemma map_bwt_sa_bwt_perm:
  "\<forall>x \<in> set xs. x < length s \<Longrightarrow>
   map ((!) (bwt_sa s)) xs = map ((!) s) (map ((!) (bwt_perm s)) xs)"
  by (simp add: bwt_perm_s_nth)

theorem ibwt_perm_abs_bwt_sa_lookup_correct:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  shows "map ((!) (bwt_sa s)) (ibwt_perm_abs (length s) s (select (bwt_sa s) bot 0)) = s"
proof -
  let ?i = "select (bwt_sa s) bot 0"
  let ?xs = "map ((!) (bwt_perm s)) (ibwt_perm_abs (length s) s ?i)"

  have "bot \<in> set s"
    by (metis assms in_set_conv_decomp valid_list_ex_def)
  hence "bot \<in> set (bwt_sa s)"
    by (metis bwt_sa_perm perm_set_eq)
  hence "count_list (bwt_sa s) bot > 0"
    by (meson count_in)
  hence "0 < rank (bwt_sa s) bot (length (bwt_sa s))"
    by (metis rank_length)
  hence "?i < length (bwt_sa s)"
    by (meson select_upper_bound)
  hence "?i < length s"
    by (metis bwt_sa_length)

  have "map ((!) (bwt_sa s)) (ibwt_perm_abs (length s) s ?i) = map ((!) s) ?xs"
  proof (intro map_bwt_sa_bwt_perm ballI)
    fix x
    assume "x \<in> set (ibwt_perm_abs (length s) s ?i)"

    from in_set_conv_nth[THEN iffD1, OF `x  \<in> _`]
    obtain i where
      "i < length (ibwt_perm_abs (length s) s ?i)"
      "ibwt_perm_abs (length s) s ?i ! i = x"
      by blast
    with ibwt_perm_abs_alt_nth[of i "length s" s ?i]
    have "x = (lf_map_abs s ^^ (length s - Suc i)) ?i"
      by (metis ibwt_perm_abs_length)
    moreover
    have "(lf_map_abs s ^^ (length s - Suc i)) ?i < length s"
      using \<open>?i < length s\<close> assms lf_map_abs_less_length_funpow by presburger
    ultimately show "x < length s"
      by blast
  qed
  then show ?thesis
    using bwt_ibwt_perm_sa_lookup_idx[OF assms] map_nth by auto
qed

subsection "Concretization"

lemma lf_map_abs_eq_conc:
  "i < length s \<Longrightarrow> lf_map_abs s i = lf_map_conc (sort (bwt_sa s)) (bwt_sa s) i"
proof -
  let ?v = "bwt_sa s ! i"
  let ?r = "rank (bwt_sa s) ?v i"
  let ?ss = "sort (bwt_sa s)"
  assume "i < length s"
  hence "rank (bwt_sa s) ?v i < count_list (sort s) ?v"
    using rank_upper_bound[of i "bwt_sa s" ?v]
    by (metis bwt_sa_length bwt_sa_perm count_list_perm mset_sort)
  with sorted_select[of ?ss ?r ?v]
  have "select ?ss ?v ?r = card {j. j < length ?ss \<and> ?ss ! j < ?v} + ?r"
    by (metis (full_types) bwt_sa_perm sorted_list_of_multiset_mset sorted_sort)
  moreover
  have "sort s = sort ?ss"
    by (simp add: bwt_sa_perm properties_for_sort)
  moreover
  have "select (sort s) ?v ?r = card {j. j < length (sort s) \<and> (sort s) ! j < ?v} + ?r"
    by (simp add: \<open>rank (bwt_sa s) ?v i < count_list (sort s) ?v\<close> sorted_select)
  ultimately show ?thesis
    by (metis (full_types) \<open>rank (bwt_sa s) ?v i < count_list (sort s) ?v\<close> bwt_sa_perm 
                           lf_map_abs.simps lf_map_conc.simps sorted_list_of_multiset_mset 
                           sorted_select_0_plus sorted_sort)
qed

lemma ibwt_perm_abs_conc_eq:
  "i < length s \<Longrightarrow> ibwt_perm_abs n s i = ibwt_perm_conc n (sort (bwt_sa s)) (bwt_sa s) i"
proof (induct n arbitrary: i)
  case 0
  then show ?case
    by auto
next
  case (Suc n)

  let ?ss = "sort (bwt_sa s)"
  let ?bs = "bwt_sa s"

  have "ibwt_perm_abs (Suc n) s i = ibwt_perm_abs n s (lf_map_abs s i) @ [i]"
    by simp
  moreover
  have "ibwt_perm_conc (Suc n) ?ss ?bs i = ibwt_perm_conc n ?ss ?bs (lf_map_conc ?ss ?bs i) @ [i]"
    by simp
  moreover
  have "lf_map_abs s i = lf_map_conc ?ss ?bs i"
    using Suc.prems lf_map_abs_eq_conc by blast
  moreover
  have "lf_map_abs s i < length s"
    using Suc.prems lf_map_abs_less_length by blast
  ultimately show ?case
    using Suc.hyps by presburger
qed

theorem ibwtn_bwt_sa_lookup_correct:
  fixes s xs ys :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  and     "xs = sort (bwt_sa s)"
  and     "ys = bwt_sa s"
shows "map ((!) ys) (ibwt_perm_conc (length ys) xs ys (select ys bot 0)) = s"
proof -
  from ibwt_perm_abs_bwt_sa_lookup_correct[OF assms(1)]
  have "map ((!) (bwt_sa s)) (ibwt_perm_abs (length s) s (select (bwt_sa s) bot 0)) = s" .
  moreover
  have "select (bwt_sa s) bot 0 < length s"
    by (metis (no_types, lifting) assms(1) bot_nat_0.extremum_uniqueI bwt_sa_length bwt_sa_perm 
                                  count_list_perm diff_Suc_1 last_conv_nth length_greater_0_conv
                                  less_nat_zero_code rank_upper_bound sa_nth_ex select_spec 
                                  valid_list_def valid_list_sa_hd)
  with ibwt_perm_abs_conc_eq
  have "ibwt_perm_abs (length s) s (select (bwt_sa s) bot 0) =
        ibwt_perm_conc (length ys) xs ys (select ys bot 0)"
    using assms(2) assms(3) bwt_sa_length by presburger
  ultimately show ?thesis
    using assms(3) by auto
qed

lemma ibwtn_eq_map_ibwt_perm_conc:
  shows "ibwtn n ss bs i = map ((!) bs) (ibwt_perm_conc n ss bs i)"
  by (induct n arbitrary: i; simp)

theorem ibwtn_correct:
  fixes s xs ys :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  and     "xs = sort (bwt_sa s)"
  and     "ys = bwt_sa s"
shows "ibwtn (length ys) xs ys (select ys bot 0) = s"
  by (metis ibwtn_eq_map_ibwt_perm_conc ibwtn_bwt_sa_lookup_correct assms)

subsection "Inverse BWT Correctness"

text "BWT (suffix array version) is invertible"
theorem ibwt_correct:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  shows "ibwt (bwt_sa s) = s"
  by (simp add: assms ibwtn_correct)

end (* of context *)

text \<open>Theorem 3.20 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Correctness of the Inverse BWT\<close>
theorem ibwt_correct_canon:
  fixes s :: "('a :: {linorder, order_bot}) list"
  assumes "valid_list s"
  shows "ibwt (bwt_canon s) = s"
  by (metis Suffix_Array_General.bwt_canon_eq_bwt_sa Suffix_Array_General.ibwt_correct
            Suffix_Array_General_ex assms)

end