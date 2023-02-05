theory BHLE

imports 
  Main
  Additional_Lemmas
begin

section \<open>Bounded Homogeneous Linear Equation Problem\<close>

definition bhle :: "(int vec * int) set" where
  "bhle \<equiv> {(a,k). \<exists>x. a \<bullet> x = 0 \<and> dim_vec x = dim_vec a \<and> dim_vec a > 0 \<and>
      x \<noteq> 0\<^sub>v (dim_vec x) \<and> \<parallel>x\<parallel>\<^sub>\<infinity> \<le> k}"

text \<open>Reduction of bounded homogeneous linear equation to partition problem\<close>

text \<open>For the reduction function, one defines five-tuples for every element in a. 
  The last tuple plays an important role. It consists only of four elements in order 
  to add constraints to the other tuples.
  These values are formed in a way such that they form all constraints needed for the 
  reductions.
  Note, that some indices have been changed with respect to \cite{EmBo81}
  to enable better indexing in the vectors/lists.\<close>

definition b1 :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b1 i M a = a + M * (5^(4*i-4) + 5^(4*i-3) + 5^(4*i-1))"

definition b2 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b2 i M = M * (5^(4*i-3) + 5^(4*i))"

definition b2_last :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b2_last i M = M * (5^(4*i-3) + 1)"

definition b3 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b3 i M =  M * (5^(4*i-4) + 5^(4*i-2))"

definition b4 :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b4 i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 5^(4*i))"

definition b4_last :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b4_last i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 1)"

definition b5 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b5 i M = M * (5^(4*i-1))"

text \<open>Change order of indices in \cite{EmBo81} such that $b3$ is in last place and can be omitted 
    in the last entry. This ensures that the weight of the solution is $1$ or $-1$,
    essential for the proof of NP-hardnes.\<close>

definition b_list :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "b_list as i M = [b1 (i+1) M (as!i), b2 (i+1) M, b4 (i+1) M (as!i), b5 (i+1) M, b3 (i+1) M]"

definition b_list_last :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "b_list_last as n M = [b1 n M (last as), b2_last n M, b4_last n M (last as), b5 n M]"

definition gen_bhle :: "int list \<Rightarrow> int vec" where
"gen_bhle as = (let M = 2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1; n = length as in
  vec_of_list (concat 
  (map (\<lambda>i. b_list as i M) [0..<n-1]) 
  @ (if n>0 then b_list_last as n M else [])))"

text \<open>The reduction function.\<close>
definition reduce_bhle_partition:: "(int list) \<Rightarrow> ((int vec) * int)" where
  "reduce_bhle_partition \<equiv> (\<lambda> a. (gen_bhle a, 1))"



text \<open>Lemmas for proof\<close>

lemma dim_vec_gen_bhle:
  assumes "as\<noteq>[]"
  shows "dim_vec (gen_bhle as) = 5 * (length as) - 1"
using assms 
proof (induct as rule: list_nonempty_induct)
  case (single x)
  then show ?case unfolding gen_bhle_def Let_def b_list_def b_list_last_def by auto
next
  case (cons x xs)
  define M where "M = (2 * (\<Sum>i<length (x # xs). \<bar>(x # xs) ! i\<bar>) + 1)"
  then show ?case using cons unfolding gen_bhle_def b_list_def b_list_last_def 
    Let_def M_def[symmetric]
    by (subst dim_vec_of_list)+ 
       (use length_concat_map_5[of 
      "(\<lambda>i. b1 (i + 1) M ((x#xs) ! i))"  
      "(\<lambda>i. b2 (i + 1) M             )"
      "(\<lambda>i. b4 (i + 1) M ((x#xs) ! i))"
      "(\<lambda>i. b5 (i + 1) M             )"
      "(\<lambda>i. b3 (i + 1) M             )"] in \<open>simp\<close>)
qed

lemma dim_vec_gen_bhle_empty:
  "dim_vec (gen_bhle []) = 0"
unfolding gen_bhle_def by auto


text \<open>Lemmas about length\<close>

lemma length_b_list:
  "length (b_list a i M) = 5" unfolding b_list_def by auto

lemma length_b_list_last:
  "length (b_list_last a n M) = 4" unfolding b_list_last_def by auto

lemma length_concat_map_b_list:
  "length (concat (map (\<lambda>i. b_list as i M) [0..<k])) = 5 * k"
by (subst length_concat)(simp add: comp_def length_b_list sum_list_triv) 

text \<open>Last values of \<open>gen_bhle\<close>\<close>
lemma gen_bhle_last0:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as -1) * 5) = 
    b1 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (last as)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_splits,
        subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed


lemma gen_bhle_last1:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as -1) * 5 + 1) = 
    b2_last (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

text \<open>The third entry of the last tuple is omitted, thus we skip one lemma\<close>

lemma gen_bhle_last3:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as -1) * 5 + 2) = 
    b4_last (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (last as)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms 
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

lemma gen_bhle_last4:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as-1) * 5 + 3) = 
    b5 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

text \<open>Up to last values of \<open>gen_bhle\<close>\<close>

lemma b_list_nth:
  assumes "i<length as-1" "j<5"
  shows "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) ! (i * 5 + j) = 
      b_list as i M ! j"
proof -
  have "map (\<lambda>i. b_list as i M) [0..<length as - 1] = 
        map (\<lambda>i. b_list as i M) [0..<i] @
        map (\<lambda>i. b_list as i M) [i..<length as - 1]"
    using assms
    by (metis append_self_conv2 less_zeroE linorder_neqE_nat map_append upt.simps(1) upt_append)
  then have "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) =
        concat (map (\<lambda>i. b_list as i M) [0..<i]) @
        concat (map (\<lambda>i. b_list as i M) [i..<length as - 1])"
    by (subst concat_append[of "map (\<lambda>i. b_list as i M) [0..<i]" 
      "map (\<lambda>i. b_list as i M) [i..<length as -1]", symmetric], auto)
  moreover have "concat (map (\<lambda>i. b_list as i M) [i..<length as - 1]) =
    (b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1]))" 
    using assms upt_conv_Cons by fastforce
  ultimately have concat_unfold: "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) =
        concat (map (\<lambda>i. b_list as i M) [0..<i]) @
        (b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1]))"
    by auto
  have "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) ! (i * 5 + j) =
    (b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1])) ! j"
    unfolding concat_unfold 
    by (subst nth_append_length_plus[of "concat (map (\<lambda>i. b_list as i M) [0..<i])" 
      "b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i + 1..<length as - 1])" j, symmetric])
       (subst length_concat_map_b_list, simp add: mult.commute)
  moreover have "(b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1])) ! j =
    b_list as i M ! j" using assms length_b_list
    by (subst nth_append[of "b_list as i M" "concat (map (\<lambda>i. b_list as i M) 
      [i+1..<length as - 1])" j], auto)
  ultimately show ?thesis by auto
qed


lemma b_list_nth0:
  assumes "i<length as-1"
  shows "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) ! (i * 5) = 
      b_list as i M ! 0"
using b_list_nth[OF assms, of 0] by auto

lemma gen_bhle_0:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5) = 
    b1 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (as!i)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+ 
     (subst b_list_nth0[OF assms, of M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_1:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 1) = 
    b2 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 1 M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_4:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 4) = 
    b3 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 4 M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_2:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 2) = 
    b4 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (as!i)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 2 M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_3:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 3) = 
    b5 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
unfolding gen_bhle_def Let_def
proof (subst vec_of_list_append, subst index_append_vec(1), goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 3 M], auto split: if_splits, simp add: b_list_def)
qed




text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem_nonzero"
  shows "reduce_bhle_partition a \<in> bhle"
using assms unfolding partition_problem_nonzero_def reduce_bhle_partition_def bhle_def
proof (safe, goal_cases)
  case (1 I)
text \<open>Given a subset $I$, we must construct a vector $x$ such that the properties of \<open>bhle\<close> hold.\<close>
  have "finite I" using 1 by (meson subset_eq_atLeast0_lessThan_finite)
  have "length a > 0" using \<open>a\<noteq>[]\<close> by auto
  define n where "n = length a"
  define minus_x::"int list" where "minus_x = [0,0,-1,1,1]"
  define plus_x::"int list" where "plus_x = [1,-1,0,-1,0]"
  define plus_x_last::"int list" where "plus_x_last = [1,-1,0,-1]"
  define plus_minus::"int list" where "plus_minus = (if n-1\<in>I then plus_x else minus_x)"
  define minus_plus::"int list" where "minus_plus = (if n-1\<in>I then minus_x else plus_x)"
  define x::"int vec" where 
    "x = vec_of_list(concat (map (\<lambda>i. if i\<in>I then plus_minus else minus_plus) [0..<n-1])
       @ plus_x_last)"
  have length_plus_minus: "length plus_minus = 5" 
    unfolding plus_minus_def plus_x_def minus_x_def by auto
  have length_minus_plus: "length minus_plus = 5" 
    unfolding minus_plus_def plus_x_def minus_x_def by auto
  have length_concat_map: "length (concat (map (\<lambda>i. if i \<in> I then plus_minus else minus_plus) 
    [0..<b])) = b*5" for b 
    using length_plus_minus length_minus_plus by (induct b, auto)
  have dimx_eq_5dima:"dim_vec x = length a * 5 - 1" 
  unfolding x_def dim_vec_of_list length_append length_concat_map plus_x_last_def 
    using \<open>length a > 0\<close> unfolding n_def[symmetric] by auto
  have "0 < dim_vec x" unfolding dimx_eq_5dima using \<open>length a > 0\<close> by linarith
  define M where "M = 2*(\<Sum>i<length a. \<bar>a!i\<bar>)+1"

text \<open>Some conditional lemmas for the proof.\<close>
  have x_nth: 
    "x $ (i*5+j) = (if i\<in>I then plus_minus ! j else minus_plus ! j)" if "i<n-1" "j<5" for i j 
  proof -
    have lt: "i * 5 + j < length (concat (map (\<lambda>i. if i \<in> I then plus_minus else minus_plus) 
      [0..<n - 1]))"
      using that length_concat_map by auto
    have len_rew: "i*5 = length (concat (map (\<lambda>i. if i \<in> I then plus_minus else minus_plus) 
      [0..<i]))"
    proof -
      have if_rew: "(\<lambda>i. if i\<in>I then plus_minus else minus_plus) = 
        (\<lambda>i. [(if i\<in>I then plus_minus!0 else minus_plus!0), 
              (if i\<in>I then plus_minus!1 else minus_plus!1),
              (if i\<in>I then plus_minus!2 else minus_plus!2), 
              (if i\<in>I then plus_minus!3 else minus_plus!3),
              (if i\<in>I then plus_minus!4 else minus_plus!4)])"
       unfolding plus_minus_def minus_plus_def plus_x_def minus_x_def by auto
      then show ?thesis
      unfolding if_rew length_concat_map_5[of 
        "(\<lambda>i. if i\<in>I then plus_minus!0 else minus_plus!0)"
        "(\<lambda>i. if i\<in>I then plus_minus!1 else minus_plus!1)" 
        "(\<lambda>i. if i\<in>I then plus_minus!2 else minus_plus!2)"
        "(\<lambda>i. if i\<in>I then plus_minus!3 else minus_plus!3)" 
        "(\<lambda>i. if i\<in>I then plus_minus!4 else minus_plus!4)"
        "[0..<i]"] by auto
    qed
    have map_rew: "map f [0..<n-1] = map f [0..<i] @ map f [i..<n-1]" 
      for f ::"nat \<Rightarrow> int list"
      using that(1) by (metis append_Nil map_append not_gr_zero upt_0 upt_append)
    have "concat (map (\<lambda>i. if i \<in> I then plus_minus else minus_plus) [0..<n-1]) ! (i * 5 + j) =
          concat (map (\<lambda>i. if i \<in> I then plus_minus else minus_plus) [i..<n-1]) ! j"
     by (subst map_rew, subst concat_append, subst len_rew)
        (subst nth_append_length_plus[of 
          "concat (map (\<lambda>i. if i \<in> I then plus_minus else minus_plus) [0..<i])"], simp)
    also have "\<dots> = (if i \<in> I then plus_minus!j else minus_plus!j)"
    proof -
      have concat_rewr: "concat (map f [i..<n-1])=
       (f i) @ (concat (map f [i+1..<n-1]))" for f::"nat \<Rightarrow> int list"
       using that(1) upt_conv_Cons by force
      have length_if: "length (if i \<in> I then plus_minus else minus_plus) = 5" 
        using length_plus_minus length_minus_plus by auto
      show ?thesis unfolding concat_rewr nth_append length_if using \<open>j<5\<close> by auto
    qed
    finally show ?thesis unfolding x_def by (subst vec_index_vec_of_list) 
      (subst nth_append, use lt in \<open>auto\<close>) 
  qed

  have x_nth0:
    "x $ (i*5) = (if i\<in>I then plus_minus ! 0 else minus_plus ! 0)" if "i<n-1" for i 
    using that by (subst x_nth[of i 0,symmetric], auto)
  
  have x_nth_last:
    "x $ ((length a -1)*5+j) = plus_x_last ! j" 
    if "j<4" for j 
  using that unfolding  x_def vec_of_list_index using nth_append_length_plus[of 
    "concat (map (\<lambda>i. if i \<in> I then plus_minus else minus_plus) [0..<n - 1])"
    "plus_x_last" j] unfolding length_concat_map n_def
  by auto

  have x_nth0_last:
    "x $ ((length a-1) *5) = plus_x_last ! 0" 
  by (subst x_nth_last[of 0,symmetric], auto)

  have gen_bhle_in_I_plus:
    "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) = 
     (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)" if "i\<in>I-{length a-1}" "n-1\<in>I" for i
  proof -
    have "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
            (gen_bhle a) $ (i*5) * x $ (i*5) +
            (gen_bhle a) $ (i*5+1) * x $ (i*5+1) +
            (gen_bhle a) $ (i*5+2) * x $ (i*5+2) +
            (gen_bhle a) $ (i*5+3) * x $ (i*5+3) +
            (gen_bhle a) $ (i*5+4) * x $ (i*5+4)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)" 
    using that 1 n_def \<open>length a > 0\<close>
    apply (subst gen_bhle_0[of i a], fastforce)
    apply (subst gen_bhle_1[of i a], fastforce)
    apply (subst gen_bhle_2[of i a], fastforce)
    apply (subst gen_bhle_3[of i a], fastforce)
    apply (subst gen_bhle_4[of i a], fastforce)
    apply (subst x_nth[of i], fastforce, fastforce)+
    apply (subst x_nth0[of i], fastforce)
    apply (unfold M_def plus_minus_def minus_plus_def plus_x_def minus_x_def)
    apply (simp add: eval_nat_numeral) 
    done
    finally show ?thesis by auto
  qed

  have gen_bhle_in_I_minus:
    "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
     (b3 (i+1) M) - (b4 (i+1) M (a!i)) + (b5 (i+1) M)" if "i\<in>I-{length a-1}" "n-1\<notin>I" for i
  proof -
    have "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
            (gen_bhle a) $ (i*5) * x $ (i*5) +
            (gen_bhle a) $ (i*5+1) * x $ (i*5+1) +
            (gen_bhle a) $ (i*5+2) * x $ (i*5+2) +
            (gen_bhle a) $ (i*5+3) * x $ (i*5+3) +
            (gen_bhle a) $ (i*5+4) * x $ (i*5+4)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (b3 (i+1) M) - (b4 (i+1) M (a!i)) + (b5 (i+1) M)" 
    using that 1 n_def \<open>length a > 0\<close>
    apply (subst gen_bhle_0[of i a], fastforce)
    apply (subst gen_bhle_1[of i a], fastforce)
    apply (subst gen_bhle_2[of i a], fastforce)
    apply (subst gen_bhle_3[of i a], fastforce)
    apply (subst gen_bhle_4[of i a], fastforce)
    apply (subst x_nth[of i], fastforce, fastforce)+
    apply (subst x_nth0[of i], fastforce)
    apply (unfold M_def plus_minus_def minus_x_def)
    apply (simp add: eval_nat_numeral) 
    done
    finally show ?thesis by auto
  qed

  have gen_bhle_not_in_I_plus:
    "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
     (b3 (i+1) M) - (b4 (i+1) M (a!i)) + (b5 (i+1) M)" if "i\<in>{0..<n}-I-{n-1}" "n-1\<in>I" for i
  proof -
    have "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
            (gen_bhle a) $ (i*5) * x $ (i*5) +
            (gen_bhle a) $ (i*5+1) * x $ (i*5+1) +
            (gen_bhle a) $ (i*5+2) * x $ (i*5+2) +
            (gen_bhle a) $ (i*5+3) * x $ (i*5+3) +
            (gen_bhle a) $ (i*5+4) * x $ (i*5+4)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (b3 (i+1) M) - (b4 (i+1) M (a!i)) + (b5 (i+1) M)" 
    using that 1 n_def \<open>length a > 0\<close>
    apply (subst gen_bhle_0[of i a], fastforce)
    apply (subst gen_bhle_1[of i a], fastforce)
    apply (subst gen_bhle_2[of i a], fastforce)
    apply (subst gen_bhle_3[of i a], fastforce)
    apply (subst gen_bhle_4[of i a], fastforce)
    apply (subst x_nth[of i], fastforce, fastforce)+
    apply (subst x_nth0[of i], fastforce)
    apply (unfold M_def minus_plus_def minus_x_def)
    apply (simp add: eval_nat_numeral) 
    done
    finally show ?thesis by auto
  qed

  have gen_bhle_not_in_I_minus:
    "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) = 
     (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)" if "i\<in>{0..<n}-I-{n-1}" "n-1\<notin>I" for i
  proof -
    have "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
            (gen_bhle a) $ (i*5) * x $ (i*5) +
            (gen_bhle a) $ (i*5+1) * x $ (i*5+1) +
            (gen_bhle a) $ (i*5+2) * x $ (i*5+2) +
            (gen_bhle a) $ (i*5+3) * x $ (i*5+3) +
            (gen_bhle a) $ (i*5+4) * x $ (i*5+4)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)" 
    using that 1 n_def \<open>length a > 0\<close>
    apply (subst gen_bhle_0[of i a], fastforce)
    apply (subst gen_bhle_1[of i a], fastforce)
    apply (subst gen_bhle_2[of i a], fastforce)
    apply (subst gen_bhle_3[of i a], fastforce)
    apply (subst gen_bhle_4[of i a], fastforce)
    apply (subst x_nth[of i], fastforce, fastforce)+
    apply (subst x_nth0[of i], fastforce)
    apply (unfold M_def minus_plus_def plus_x_def)
    apply (simp add: eval_nat_numeral) 
    done
    finally show ?thesis by auto
  qed

  have gen_bhle_last:
    "(\<Sum>j=0..<4. (gen_bhle a) $ ((n-1)*5+j) * x $ ((n-1)*5+j)) =
     (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M)"
  proof -
    have "(\<Sum>j=0..<4. (gen_bhle a) $ ((n-1)*5+j) * x $ ((n-1)*5+j)) =
            (gen_bhle a) $ ((n-1)*5) * x $ ((n-1)*5) +
            (gen_bhle a) $ ((n-1)*5+1) * x $ ((n-1)*5+1) +
            (gen_bhle a) $ ((n-1)*5+2) * x $ ((n-1)*5+2) +
            (gen_bhle a) $ ((n-1)*5+3) * x $ ((n-1)*5+3)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M)" 
    using 1 n_def \<open>length a > 0\<close> unfolding n_def
    apply (subst gen_bhle_last0[of a, OF \<open>length a > 0\<close>])
    apply (subst gen_bhle_last1[of a, OF \<open>length a > 0\<close>])
    apply (subst gen_bhle_last3[of a, OF \<open>length a > 0\<close>])
    apply (subst gen_bhle_last4[of a, OF \<open>length a > 0\<close>]) 
    apply (subst x_nth_last, simp)+
    apply (subst x_nth0_last, simp add: n_def)
    apply (unfold M_def plus_x_last_def)
    apply (auto simp add: eval_nat_numeral last_conv_nth) 
    done
    finally show ?thesis by auto
  qed

text \<open>The actual proof. \<close>
  have "(gen_bhle a) \<bullet> x = 0"
  proof -
    define f where "f = (\<lambda>i. (\<Sum>j = 0..<5. gen_bhle a $ (i*5+j) * x $ (i*5+j)))"
    have "(gen_bhle a) \<bullet> x = (\<Sum>i<n*5 -1. (gen_bhle a) $ i * x $ i) "
      unfolding M_def n_def gen_bhle_def scalar_prod_def dimx_eq_5dima 
      using lessThan_atLeast0 by auto
    also have "\<dots> = (\<Sum>i<(n-1)*5. (gen_bhle a) $ i * x $ i) + 
      (\<Sum>i = (n-1)*5..<(n-1)*5 +4. (gen_bhle a) $ i * x $ i)"
    proof (subst split_sum_mid_less[of "(n-1)*5" "n*5-1"], goal_cases)
      case 1
      then show ?case unfolding n_def using \<open>0 < length a\<close> by linarith
    next
      case 2
      have "n * 5 - 1 = (n-1) * 5 + 4" unfolding n_def using \<open>0 < length a\<close> by linarith
      then show ?case by auto
    qed
    also have "\<dots> = (\<Sum>i = 0..<n-1. f i) + 
      (\<Sum>j=0..<4. gen_bhle a $ ((n-1)*5+j) * x $ ((n-1)*5+j))" 
    proof -
      have *: "(+) ((n - 1) * 5) ` {0..<4} = {(n-1)*5..<(n-1)*5+4}" by auto
      have "(\<Sum>i = (n - 1) * 5..<(n - 1) * 5 + 4. gen_bhle a $ i * x $ i) =
        (\<Sum>j = 0..<4. gen_bhle a $ ((n - 1) * 5 + j) * x $ ((n - 1) * 5 + j))" 
      using sum.reindex[of "(\<lambda>j. (n-1)*5+j)" "{0..<4}" "(\<lambda>i. gen_bhle a $ i * x $ i)"] 
      unfolding comp_def * by auto
      then show ?thesis unfolding f_def lessThan_atLeast0 
      by (subst sum_split_idx_prod[of "(\<lambda>i. (gen_bhle a) $ i * x $ i)" "n-1" 5], auto)
    qed
    also have "\<dots> = (\<Sum>i\<in>I-{n-1}. f i) + (\<Sum>i\<in>{0..<n}-I-{n-1}. f i) + 
      (\<Sum>j=0..<4. gen_bhle a $ ((n-1)*5+j) * x $ ((n-1)*5+j))" 
    proof -
      have "I - {n - 1} \<union> (({0..<n} - I) - {n - 1}) = {0..<n-1}"
        using "1"(1) n_def by auto
      then show ?thesis
        by (subst sum.union_disjoint[of "I - {n - 1}" "{0..<n} - I - {n - 1}", symmetric]) 
           (auto simp add: \<open>finite I\<close>)
    qed
    also have "\<dots> = M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
        + M * 5^(4*n-4) - M"
    proof (cases "n-1\<in>I")
      case True
      have "sum f (I - {n - 1}) + sum f ({0..<n} - I - {n - 1}) +
        (\<Sum>j = 0..<4. gen_bhle a $ ((n - 1) * 5 + j) * x $ ((n - 1) * 5 + j)) = 
        (\<Sum>i\<in>I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) 
        + (\<Sum>i\<in>{0..<n}-I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) 
        + (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M)"
      proof -
        have "(\<Sum>i\<in>I-{n-1}. f i) =
              (\<Sum>i\<in>I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) "
        unfolding f_def using gen_bhle_in_I_plus[OF _ True] by (simp add: n_def)
        moreover have "(\<Sum>i\<in>{0..<n}-I-{n-1}. f i) =
              (\<Sum>i\<in>{0..<n}-I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) "
        unfolding f_def using gen_bhle_not_in_I_plus[OF _ True] by (meson sum.cong)
        ultimately show ?thesis unfolding f_def using gen_bhle_last by auto
      qed
      also have "\<dots> = (\<Sum>i\<in>I-{n-1}.  (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))) 
        + (\<Sum>i\<in>{0..<n}-I-{n-1}. - (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))) 
        + (a!(n-1)) + M * 5^(4*n-4) - M*1"
      proof -
        have "b1 (i + 1) M (a ! i) - b2 (i + 1) M - b5 (i + 1) M =
           (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))" if "i\<in>I-{n-1}" for i
        unfolding b1_def b2_def b5_def
        by (smt (verit, best) add_uminus_conv_diff right_diff_distrib)
        moreover have "b3 (i + 1) M - b4 (i + 1) M (a ! i) + b5 (i + 1) M =
          - (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))" if "i\<in>{0..<n} - I - {n - 1}" for i
        unfolding b3_def b4_def b5_def 
        by (smt (verit, best) add_uminus_conv_diff right_diff_distrib)
        moreover have "b1 n M (a ! (n - 1)) - b2_last n M - b5 n M =
          (a!(n-1)) + M * 5^(4*n-4) - M"
        unfolding b1_def b2_last_def b5_def by (simp add: distrib_left)
        moreover have "- b4_last n M (a ! (n - 1)) + b5 n M = 
          -(a!(n-1)) - M * 5^(4*n-2) - M"
        unfolding b4_last_def b5_def by (simp add: distrib_left)
        ultimately show ?thesis by auto
      qed
      also have "\<dots> = (\<Sum>i\<in>I-{n-1}.  (a!i)) + (\<Sum>i\<in>{0..<n}-I-{n-1}. - (a!i))
        + M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
        + (a!(n-1)) + M * 5^(4*n-4) - M"
      proof -
        have sets1: "{0..<n - 1} \<inter> I = I - {n -1}" using "1"(1) n_def by auto
        have sets2: "{0..<n - 1} - I = {0..<n}- I - {n-1}" using "1"(1) n_def by auto
        have subs: "(\<Sum>i\<in>I-{n-1}. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1)) +
              (\<Sum>i\<in>{0..<n}-I-{n-1}. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1)) =
              (\<Sum>i = 0..<n-1. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1))" 
        using sum.Int_Diff[of "{0..<n-1}" "(\<lambda>i. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1))" "I"]
          \<open>finite I\<close> unfolding sets1 sets2  by auto
        show ?thesis
          apply (subst distrib_left)+ 
          apply (subst sum.distrib)+ 
          apply (subst sum_distrib_left) 
          apply (subst right_diff_distrib)+ 
          apply (subst subs[symmetric])
          apply auto 
          done
      qed
      also have "\<dots> = (\<Sum>i\<in>I. (a!i)) + (\<Sum>i\<in>{0..<n}-I. - (a!i))
        + M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
        + M * 5^(4*n-4) - M" 
      proof -
        have *: "a ! (n-1) = sum ((!) a) (I \<inter> {n-1})" using True by auto
        have "sum ((!) a) (I - {n-1}) + a ! (n-1) = sum ((!) a) I"
        by (subst sum.Int_Diff[of "I" _ "{n-1}"], unfold *, auto simp add: \<open>finite I\<close>)
        then show ?thesis using True by auto 
      qed
      also have "\<dots> = M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
        + M * 5^(4*n-4) - M "
        unfolding n_def using 1(2) by (subst sum_negf, auto)
      finally show ?thesis by auto
    (* Case n-1\<notin>I*)
    next
    case False
      have "sum f (I - {n - 1}) + sum f ({0..<n} - I - {n - 1}) +
        (\<Sum>j = 0..<4. gen_bhle a $ ((n - 1) * 5 + j) * x $ ((n - 1) * 5 + j)) = 
        (\<Sum>i\<in>{0..<n}-I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) 
        + (\<Sum>i\<in>I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) 
        + (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M)"
      proof -
        have "(\<Sum>i\<in>{0..<n}-I-{n-1}. f i) =
              (\<Sum>i\<in>{0..<n}-I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) "
        unfolding f_def using gen_bhle_not_in_I_minus[OF _ False] by (simp add: n_def)
        moreover have "(\<Sum>i\<in>I-{n-1}. f i) =
              (\<Sum>i\<in>I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) "
        unfolding f_def using gen_bhle_in_I_minus[OF _ False] by (simp add: n_def)
        ultimately show ?thesis unfolding f_def using gen_bhle_last by auto
      qed
      also have "\<dots> = (\<Sum>i\<in>{0..<n}-I-{n-1}.  (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))) 
        + (\<Sum>i\<in>I-{n-1}. - (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))) 
        + (a!(n-1)) + M * 5^(4*n-4) - M*1"
      proof -
        have "b1 (i + 1) M (a ! i) - b2 (i + 1) M - b5 (i + 1) M =
           (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))" if "i\<in>{0..<n} - I - {n - 1}" for i
        unfolding b1_def b2_def b5_def
        by (smt (verit, best) add_uminus_conv_diff right_diff_distrib)
        moreover have "b3 (i + 1) M - b4 (i + 1) M (a ! i) + b5 (i + 1) M =
          - (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))" if "i\<in>I-{n-1}" for i
        unfolding b3_def b4_def b5_def 
        by (smt (verit, best) add_uminus_conv_diff right_diff_distrib)
        moreover have "b1 n M (a ! (n - 1)) - b2_last n M - b5 n M =
          (a!(n-1)) + M * 5^(4*n-4) - M"
        unfolding b1_def b2_last_def b5_def by (simp add: distrib_left)
        moreover have "- b4_last n M (a ! (n - 1)) + b5 n M = 
          -(a!(n-1)) - M * 5^(4*n-2) - M"
        unfolding b4_last_def b5_def by (simp add: distrib_left)
        ultimately show ?thesis by auto
      qed
      also have "\<dots> = (\<Sum>i\<in>{0..<n}-I-{n-1}.  (a!i)) + (\<Sum>i\<in>I-{n-1}. - (a!i))
        + M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
        + (a!(n-1)) + M * 5^(4*n-4) - M"
      proof -
        have sets1: "{0..<n - 1} \<inter> I = I - {n -1}" using "1"(1) n_def by auto
        have sets2: "{0..<n - 1} - I = {0..<n}- I - {n-1}" using "1"(1) n_def by auto
        have subs: "(\<Sum>i\<in>{0..<n}-I-{n-1}. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1)) +
              (\<Sum>i\<in>I-{n-1}. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1)) =
              (\<Sum>i = 0..<n-1. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1))" 
        using sum.Int_Diff[of "{0..<n-1}" "(\<lambda>i. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1))" "I"]
          \<open>finite I\<close> unfolding sets1 sets2  by auto
        show ?thesis
          apply (subst distrib_left)+ 
          apply (subst sum.distrib)+ 
          apply (subst sum_distrib_left) 
          apply (subst right_diff_distrib)+ 
          apply (subst subs[symmetric])
          apply auto 
          done
      qed
      also have "\<dots> = (\<Sum>i\<in>{0..<n}-I. (a!i)) + (\<Sum>i\<in>I. - (a!i))
        + M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
        + M * 5^(4*n-4) - M" 
      proof -
        have *: "({0..<n}-I) \<inter> {n-1} = {n-1}" using False n_def \<open>length a > 0\<close> by auto
        then have **: "a ! (n-1) = sum ((!) a) (({0..<n}-I) \<inter> {n-1})" using False by auto
        have "sum ((!) a) (({0..<n}-I) - {n-1}) + a ! (n-1) = sum ((!) a) ({0..<n}-I)"
        by (subst sum.Int_Diff[of "{0..<n}-I" _ "{n-1}"], unfold * **, auto simp add: \<open>finite I\<close>)
        then show ?thesis using False by auto 
      qed
      also have "\<dots> = M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
        + M * 5^(4*n-4) - M "
        unfolding n_def using 1(2) by (subst sum_negf, auto)
      finally show ?thesis by auto
    qed
      also have "\<dots> = M * ((\<Sum>i\<in>{1..<n}. 5^(4*i-4) - 5^(4*i)) + 5^(4*n-4) - 1)"
      proof -
        have sums: "(\<Sum>i = Suc 0..<Suc (n - 1). 5 ^ (4 * i - 4) - 5 ^ (4 * i)) =
                    sum ((\<lambda>i. 5 ^ (4*(i+1) - 4) - 5 ^ (4*(i+1)))) {0..<n - 1}"
        using sum.atLeast_Suc_lessThan_Suc_shift[of "(\<lambda>i. 5^(4*i-4) - 5^(4*i))" 0 "n-1"] 
        unfolding comp_def by auto
        show ?thesis
        by (subst distrib_left[symmetric], subst right_diff_distrib, subst mult_1_right)
           (subst sums[symmetric], use \<open>0 < length a\<close> n_def in \<open>force\<close>)
      qed
      also have "\<dots> = M * (((\<Sum>i\<in>{1..<n}. 5^(4*i-4)) + 5^(4*n-4)) - ((\<Sum>i\<in>{1..<n}. 5^(4*i)) + 1))"
        using sum.distrib[of "(\<lambda>i. 5^(4*i-4))" "(\<lambda>i. (-1) * 5^(4*i))" "{1..<n}"] 
        by (simp add: sum_subtractf)
      also have "\<dots> = M * ((\<Sum>i\<in>{1..<n+1}. 5^(4*i-4)) - (\<Sum>i\<in>{0..<n}. 5^(4*i)))"
        using sum.atLeastLessThan_Suc[of 1 n "(\<lambda>i. 5^(4*i-4))"]
              sum.atLeast_Suc_lessThan[of 0 n "(\<lambda>i. 5^(4*i))"]
        by (smt (verit, best) One_nat_def Suc_eq_plus1 Suc_leI \<open>0 < length a\<close> mult_eq_0_iff 
          n_def power_0)
      also have "\<dots> = M * ((\<Sum>i\<in>{0..<n}. 5^(4*i)) - (\<Sum>i\<in>{0..<n}. 5^(4*i)))"
        using sum.atLeast_Suc_lessThan_Suc_shift[of "(\<lambda>i. 5^(4*i-4))" 0 n] by auto
      also have "\<dots> = 0" by auto
    finally show ?thesis by blast
  qed

  moreover have "dim_vec x = dim_vec (gen_bhle a)" 
    using dim_vec_gen_bhle[OF \<open>a\<noteq>[]\<close>] dimx_eq_5dima by simp
  moreover have "x \<noteq> 0\<^sub>v (dim_vec x)"
  proof (rule ccontr)
    assume "\<not> x \<noteq> 0\<^sub>v (dim_vec x)"
    then have "x = 0\<^sub>v (dim_vec x)" by auto
    have "dim_vec x > 3" using \<open>0 < length a\<close> dimx_eq_5dima by linarith
    have "(n - Suc 0) * 5 + 3 < dim_vec x" 
      unfolding dimx_eq_5dima n_def using \<open>length a > 0\<close> by linarith
    then have "x $ ((n-1)*5 + 3) = 0" using \<open>dim_vec x > 3\<close> 
      by (subst \<open>x=0\<^sub>v (dim_vec x)\<close>, subst index_zero_vec(1)[of "(n-1)*5+3"], auto)
    moreover have "x $ ((n-1)*5+3) \<noteq> 0"
    proof -
      have "\<not> ((n - 1) * 5 + 3 < (n - 1) * 5)" by auto
      then show ?thesis unfolding x_def vec_of_list_index nth_append length_concat_map 
      plus_x_last_def by auto
    qed
    ultimately show False by auto
  qed
  moreover have "\<parallel>x\<parallel>\<^sub>\<infinity> \<le> 1"
  proof -
    let ?x_list = "(concat (map (\<lambda>i. if i \<in> I then plus_minus
      else minus_plus) [0..<n-1]))"
    have set: "set (?x_list) \<subseteq> {-1,0,1::int}" 
      using \<open>length a > 0\<close> 1 unfolding n_def plus_minus_def minus_plus_def 
      plus_x_def minus_x_def
      by (subst set_concat, subst set_map)(auto simp add: atLeast0LessThan)
    have "?x_list ! i \<in> {-1,0,1::int}" if "i< length ?x_list" for i
      using nth_mem[OF that] set by auto
    then have *:"?x_list ! i \<in> {-1,0,1::int}" if "i< (n - 1) * 5" for i using that 
      unfolding length_concat_map by auto
    have **: "plus_x_last ! (i - (n - 1) * 5)\<in>{-1,0,1::int}"
      if "\<not> (i<(n-1)*5)" "i<dim_vec x" for i 
    proof -
      have "(i - (n - 1) * 5)<4" using that \<open>length a > 0\<close> 
        unfolding dimx_eq_5dima n_def by auto
      then show ?thesis unfolding plus_x_last_def
      by (smt (z3) add.assoc add_diff_cancel_right' diff_is_0_eq insertCI less_Suc_eq not_le 
      not_less_iff_gr_or_eq nth_Cons' numeral_1_eq_Suc_0 numeral_Bit0 plus_1_eq_Suc)
    qed
    have "x$i\<in>{-1,0,1::int}" if "i<dim_vec x" for i 
      using that * ** unfolding x_def vec_of_list_index nth_append length_concat_map 
        plus_x_last_def by auto
    then have "\<bar>x$i\<bar>\<le>1" if "i<dim_vec x" for i using that by fastforce
    then show ?thesis unfolding linf_norm_vec_Max 
      by (subst Max_le_iff, auto simp add: exI[of "(\<lambda>i. dim_vec x > i)" 0] \<open>dim_vec x > 0\<close>)
  qed
  ultimately show ?case by (subst exI[of _ x], auto) 
qed



text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_subset_sum:
  assumes "reduce_bhle_partition a \<in> bhle"
  shows "a \<in> partition_problem_nonzero"
using assms unfolding reduce_bhle_partition_def bhle_def partition_problem_nonzero_def
proof (safe, goal_cases)
  case (1 x)
text \<open>Given a vector $x$ from \<open>bhle\<close> find the subset $I$ such that it has the same sum as 
  its complement.\<close>
  have "length a > 0" using 1(3) dim_vec_gen_bhle dim_vec_gen_bhle_empty by auto
  define I where "I = {i\<in>{0..<length a}. x $ (5*i)\<noteq>0}"
  define n where "n = length a"
  then have "n > 0" using \<open>length a>0\<close> by auto 
  have dim_vec_x_5n: "dim_vec x = 5 * n - 1" unfolding n_def using 1
  by (metis dim_vec_gen_bhle dim_vec_gen_bhle_empty less_not_refl2)
  have "I\<subseteq>{0..<length a}" using 1 I_def by auto
text \<open>This is the trickiest part in the proof. One first has to generate equations from $x$
  which form conditions on the entries of $x$. To do so, we consider the formula
  \<open>gen_bhle a \<bullet> x = 0\<close> and rewrite it in basis $5$. Every digit then gives us an 
  arithmetic expression in entries of $x$ equals to zero.
  From these equations, we can deduce the wanted properties.\<close>
  moreover have "sum ((!) a) I = sum ((!) a) ({0..<length a} - I)" 
  proof -
    define M where "M = 2 * (\<Sum>i<length a. \<bar>a ! i\<bar>) + 1"

    text \<open>Rewriting the first formula in a huge sum.\<close>
    define a0 where "a0 = (\<lambda>i. if i mod (5::nat) \<in> {0,2} then a!(i div 5) else 0)"
    define a1 where "a1 = (\<lambda>i. if i mod (5::nat) \<in> {0,4} then 1 else 0::int)"
    define a1_last where "a1_last = (\<lambda>i. if i mod (5::nat) \<in> {0} then 1 else 0::int)"
    define a2 where "a2 = (\<lambda>i. if i mod (5::nat) \<in> {0,1} then 1 else 0::int)"
    define a3 where "a3 = (\<lambda>i. if i mod (5::nat) \<in> {4,2} then 1 else 0::int)"
    define a3_last where "a3_last = (\<lambda>i. if i mod (5::nat) \<in> {2} then 1 else 0::int)"
    define a4 where "a4 = (\<lambda>i. if i mod (5::nat) \<in> {0,2,3} then 1 else 0::int)"
    define a5 where "a5 = (\<lambda>i. if i mod (5::nat) \<in> {1,2} then 
                          (if i div 5 < n-1 then 5^(4*(i div 5 +1)) else 1) else 0::int)"
    
    define a0_rest' where "a0_rest' = 
          (\<lambda>i. a1 i * 5 ^ (4 * (i div 5)) + a2 i * 5 ^ (4 * (i div 5) + 1) +
          a3 i * 5 ^ (4 * (i div 5) + 2) + a4 i * 5 ^ (4 * (i div 5) + 3) + a5 i)"
    define a0_last where "a0_last = (\<lambda>i.
          a1_last i * 5 ^ (4 * (i div 5)) + a2 i * 5 ^ (4 * (i div 5) + 1) +
          a3_last i * 5 ^ (4 * (i div 5) + 2) + a4 i * 5 ^ (4 * (i div 5) + 3) + 
          a5 i)"

    define a0_rest where "a0_rest = (\<lambda>i. if i div 5 < n-1 then a0_rest' i else a0_last i)"

    let ?P0 = "(\<lambda>i. b1 (i div 5 + 1) M (a!(i div 5)))"
    let ?P1 = "(\<lambda>i. (if i div 5 < n-1 then b2 (i div 5 + 1) M else b2_last (i div 5 + 1) M))"
    let ?P4 = "(\<lambda>i. (if i div 5 < n-1 then b3 (i div 5 + 1) M else 0))"
    let ?P2 = "(\<lambda>i. (if i div 5 < n-1 then b4 (i div 5 + 1) M (a!(i div 5)) 
                      else b4_last (i div 5 + 1) M (a!(i div 5))))"
    let ?P3 = "(\<lambda>i. b5 (i div 5 + 1) M)"

    have cases_a0: "(a0 i + M * (a0_rest i)) = 
      (if i mod 5 = 0 then ?P0 i else 
      (if i mod 5 = 1 then ?P1 i else
      (if i mod 5 = 2 then ?P2 i else
      (if i mod 5 = 3 then ?P3 i else ?P4 i))))" 
    if "i<5*n" for i
    proof (cases "i div 5 < n-1")
    case True
    then show ?thesis
    by (subst mod_5_if_split[of i "a0 i + M * (a0_rest i)" ?P0 ?P1 ?P2 ?P3 ?P4])
       (auto simp add: a0_def a0_rest_def a0_rest'_def 
         a1_def a2_def a3_def a4_def a5_def b1_def b2_def b3_def b4_def b5_def) 
    next
    case False
    then have "i div 5 = n-1" using that by auto
    then show ?thesis 
      by (subst mod_5_if_split[of i "a0 i + M * (a0_rest i)" ?P0 ?P1 ?P2 ?P3 ?P4])
         (auto simp add: False a0_def a0_rest_def a0_last_def 
         a1_def a1_last_def a2_def a3_def a3_last_def a4_def a5_def 
         b1_def b2_def b2_last_def b3_def b4_def b4_last_def b5_def)
    qed

    text \<open>Splitting of the first part of the sum containing the $a_i$.\<close>
    have gen_bhle_nth: "gen_bhle a $ i = a0 i + M * (a0_rest i)" 
      if "i<dim_vec (gen_bhle a)" for i
    proof -
      have dim_gen_bhle: "dim_vec (gen_bhle a) = 5 * n-1" 
        unfolding n_def using \<open>length a >0\<close> dim_vec_gen_bhle by auto
      have gen_bhle_subst: "gen_bhle a $ i = (concat
         (map (\<lambda>i. b_list a i M) [0..<n - 1]) @ b_list_last a n M ) ! i"
      (is "gen_bhle a $ i = (?concat_map @ ?last)! i")
        unfolding gen_bhle_def Let_def unfolding M_def[symmetric] n_def vec_index_vec_of_list
        using \<open>length a > 0\<close> by auto
      have len_concat_map: "length ?concat_map = 5 * (n-1)"using length_concat_map_b_list .
      show ?thesis
      proof (cases "i div 5 < n-1")
        case True
        then have "i<5*(n-1)" by auto
        then have j_th: "(?concat_map @ ?last)! i = ?concat_map ! i" 
          by (subst nth_append, subst len_concat_map, auto)
        have "concat (map (\<lambda>i. b_list a i M) [0..<n - 1]) ! i = 
              concat (map (\<lambda>i. b_list a i M) [0..<n - 1]) ! (i mod 5 + 5*(i div 5))"
          using mod_mult_div_eq[of i 5,symmetric] by auto
        also have "\<dots> = (concat (map (\<lambda>i. b_list a i M) [0..<i div 5]) @ 
          concat (map (\<lambda>i. b_list a i M) [i div 5..<n - 1]) ) ! (i mod 5 + 5*(i div 5))"
          by (smt (z3) True append_self_conv2 concat_append less_zeroE linorder_neqE_nat 
            map_append upt.simps(1) upt_append)
        also have "\<dots> = concat (map (\<lambda>i. b_list a i M) [i div 5..<n - 1]) ! (i mod 5)"
          using nth_append_length_plus[of "concat (map (\<lambda>i. b_list a i M) [0..<i div 5])" 
            "concat (map (\<lambda>i. b_list a i M) [i div 5..<n - 1])" "i mod 5"] 
            length_concat_map_b_list[of a M "i div 5"]
          by auto
        also have "\<dots> = (b_list a (i div 5) M @ 
          concat (map (\<lambda>i. b_list a i M) [i div 5 +1..<n - 1])) ! (i mod 5)"
          using True upt_conv_Cons by auto
        also have "\<dots> = b_list a (i div 5) M  ! (i mod 5)" 
          unfolding nth_append b_list_def by auto
        finally have i_th: "?concat_map ! i = b_list a (i div 5) M ! (i mod 5)"
          by auto
        show ?thesis
        apply(subst gen_bhle_subst, subst j_th, subst i_th, subst cases_a0) 
          subgoal apply (use that dim_vec_gen_bhle n_def \<open>length a > 0\<close> in \<open>auto\<close>) done
          subgoal apply (subst mod_5_if_split[of i "b_list a (i div 5) M ! (i mod 5)" 
            ?P0 ?P1 ?P2 ?P3 ?P4])
            apply (use True in \<open>auto simp add: b_list_def that\<close>) done
        done
      next
        case False
        then have "i \<ge> 5*(n-1)" by auto
        then obtain j where "i = 5*(n-1) + j" and "j<4"
          using \<open>i<dim_vec (gen_bhle a)\<close> \<open>length a > 0\<close>
          unfolding dim_gen_bhle n_def
          by (subst split_lower_plus_diff[of i "5*(length a-1)" "5*(length a)"], auto)
        have j_th: "(?concat_map @ ?last)! i = ?last ! j" 
          using \<open>i<dim_vec (gen_bhle a)\<close> nth_append_length_plus[of ?concat_map ?last j]
          unfolding len_concat_map by (auto simp add: \<open>i = 5*(n-1) + j\<close> \<open>j<4\<close>)
        have "j = i mod 5" using \<open>i = 5*(n-1) + j\<close> \<open>j<4\<close> by auto
        have "n = i div 5 + 1" using \<open>i = 5*(n-1) + j\<close> \<open>j<4\<close> \<open>length a > 0\<close> n_def by auto
        then have "i div 5 = n-1" by auto
        have "last a = a ! (i div 5)" unfolding \<open>i div 5 = n-1\<close>
          by (subst last_conv_nth[of a]) (use \<open>length a > 0\<close> n_def in \<open>auto\<close>)
        have *: "i mod 5 = 4 \<Longrightarrow> [] ! 0 = 0" by (use \<open>j < 4\<close> \<open>j = i mod 5\<close> in \<open>presburger\<close>)
        show ?thesis 
          apply(subst gen_bhle_subst, subst j_th, subst cases_a0)
            subgoal apply (use that dim_vec_gen_bhle n_def \<open>length a > 0\<close> in \<open>auto\<close>) done
            subgoal apply (subst mod_5_if_split[of i "b_list_last a n M ! j" ?P0 ?P1 ?P2 ?P3 ?P4])
            apply (auto simp add: b_list_last_def that \<open>j = i mod 5\<close> \<open>n = i div 5 + 1\<close> 
            \<open>last a = a ! (i div 5)\<close> *)
            done
          done 
      qed
    qed


    have  "gen_bhle a \<bullet> x = (\<Sum>i<5*n-1. x $ i *  (a0 i + M * a0_rest i))"
      using 1(1) gen_bhle_nth  unfolding scalar_prod_def Let_def dim_vec_x_5n 1(2)[symmetric]
      by (smt (verit, best) lessThan_atLeast0 lessThan_iff mult.commute sum.cong)

    then have sum_gen_bhle: "(\<Sum>i<5 * n-1. x $ i * (a0 i + M * a0_rest i)) = 0"
      using 1(1) by simp

text \<open>The first equation containing the $a_i$\<close>
    have eq_0: "(\<Sum>i<n. (x $ (i*5) + x $ (i*5+2)) * a!i) = 0" and
         eq_0': "(\<Sum>i<5*n-1. x$i * (a0_rest i)) = 0"
    proof -
      have *: "(\<Sum>i<5*n-1. \<bar>a0 i\<bar>) < M"
      proof -
        have "5 * n - 1 = Suc (5 * n - 2)" using \<open>n > 0\<close> by auto
        have "5 * n - 2 = Suc (5 * n - 3)" using \<open>n > 0\<close> by auto
        have "5 * n - 3 = Suc (5 * n - 4)" using \<open>n > 0\<close> by auto
        have "5 * n - 4 = Suc (5 * n - 5)" using \<open>n > 0\<close> by auto
        have "(\<Sum>i<5*n-1. \<bar>a0 i\<bar>) = (\<Sum>i<5*(n-1). \<bar>a0 i\<bar>) + (\<Sum>j<4.\<bar>a0 ((n-1)*5+j)\<bar>)"
        proof -
          have "5*n-5 = 5*(n-1)" by auto
          have "(\<Sum>i<5*n-1. \<bar>a0 i\<bar>) = 
            (\<Sum>i<5*n-5. \<bar>a0 i\<bar>) + \<bar>a0 (5*(n-1))\<bar> + \<bar>a0 (5*(n-1)+1)\<bar> +
            \<bar>a0 (5*(n-1)+2)\<bar> + \<bar>a0 (5*(n-1)+3)\<bar>"
          unfolding \<open>5 * n - 1 = Suc (5 * n - 2)\<close> sum.lessThan_Suc[of "(\<lambda>i.\<bar>a0 i\<bar>)" "5 * n - 2"]
          unfolding \<open>5 * n - 2 = Suc (5 * n - 3)\<close> sum.lessThan_Suc[of "(\<lambda>i.\<bar>a0 i\<bar>)" "5 * n - 3"]
          unfolding \<open>5 * n - 3 = Suc (5 * n - 4)\<close> sum.lessThan_Suc[of "(\<lambda>i.\<bar>a0 i\<bar>)" "5 * n - 4"]
          unfolding \<open>5 * n - 4 = Suc (5 * n - 5)\<close> sum.lessThan_Suc[of "(\<lambda>i.\<bar>a0 i\<bar>)" "5 * n - 5"]
          unfolding \<open>5*n-5 = 5*(n-1)\<close>
          by (auto simp add: Suc3_eq_add_3 add.commute)
          moreover have "\<bar>a0 (5*(n-1))\<bar> + \<bar>a0 (5*(n-1)+1)\<bar> + \<bar>a0 (5*(n-1)+2)\<bar> + \<bar>a0 (5*(n-1)+3)\<bar> =
            (\<Sum>j<4.\<bar>a0 ((n-1)*5+j)\<bar>)" by (simp add:eval_nat_numeral)
          ultimately show ?thesis using \<open>5*n-5 = 5*(n-1)\<close> by auto
        qed
        also have "\<dots> = (\<Sum>i<n-1. (\<Sum>j<5. \<bar>a0 (i*5+j)\<bar>)) + (\<Sum>j<4.\<bar>a0 ((n-1)*5+j)\<bar>)"
          using sum_split_idx_prod[of "(\<lambda>i. \<bar>a0 i\<bar>)" "n-1" 5]
          by (simp add: lessThan_atLeast0 mult.commute)
        also have "\<dots> = (\<Sum>i<n. (\<Sum>j<5::nat. \<bar>if j \<in> {0, 2} then a ! i else 0\<bar>))" 
        proof -
          have "(5::nat) = Suc 4" by auto
          have "(\<Sum>i<n-1. (\<Sum>j<5::nat. \<bar>a0 (i*5+j)\<bar>)) = 
            (\<Sum>i<n-1. (\<Sum>j<5::nat. \<bar>if j \<in> {0, 2} then a ! i else 0\<bar>))"
            by(rule sum.cong[OF refl], rule sum.cong[OF refl],
              auto simp add: a0_def div_mult_self3[of 5])
          moreover have "(\<Sum>j<4::nat.\<bar>a0 ((n-1)*5+j)\<bar>) = 
            (\<Sum>j<4::nat.\<bar>if j \<in> {0, 2} then a ! (n-1) else 0\<bar>)"
            by(rule sum.cong[OF refl],
              auto simp add: a0_def div_mult_self3[of 5])
          moreover have "(\<Sum>j<4::nat.\<bar>if j \<in> {0, 2} then a ! (n-1) else 0\<bar>) = 
            (\<Sum>j<5::nat.\<bar>if j \<in> {0, 2} then a ! (n-1) else 0\<bar>)"
            unfolding \<open>5=Suc 4\<close>
            using sum.lessThan_Suc[of "(\<lambda>j.\<bar>if j \<in> {0, 2} then a ! (n-1) else 0\<bar>)" "4::nat"] 
            by auto
          ultimately have *: "(\<Sum>i<n-1. (\<Sum>j<5. \<bar>a0 (i*5+j)\<bar>)) + (\<Sum>j<4.\<bar>a0 ((n-1)*5+j)\<bar>) = 
            (\<Sum>i<n-1. (\<Sum>j<5::nat. \<bar>if j \<in> {0, 2} then a ! i else 0\<bar>)) + 
            (\<Sum>j<5::nat. \<bar>if j \<in> {0, 2} then a ! (n-1) else 0\<bar>)" by auto
          show ?thesis by (subst *, subst sum.lessThan_Suc[symmetric], auto simp add: \<open>n>0\<close>)
        qed  
        also have "\<dots> = (\<Sum>i<n. 2 * \<bar>a ! i\<bar>)" by (auto simp add: eval_nat_numeral)
        also have "\<dots> = 2 * (\<Sum>i<n. \<bar>a ! i\<bar>)"
          by (simp add: sum_distrib_left)
        finally show ?thesis unfolding M_def n_def by linarith
      qed
      have **: "\<forall>i<5*n-1. \<bar>x $ i\<bar> \<le> 1" using 1(5) 
        by (metis dim_vec_x_5n order_trans vec_index_le_linf_norm)
      have "(\<Sum>i<5*n-1. x $ i * a0 i) = 0 \<and> (\<Sum>i<5*n-1. x$i * (a0_rest i)) = 0"
        using split_eq_system[OF * ** sum_gen_bhle] by auto
      moreover have "(\<Sum>i<5*n-1. x $ i * a0 i) = (\<Sum>i<n. (x $ (i*5) + x $ (i*5+2)) * a!i)"
      proof -
        let ?g = "(\<lambda>j. x $ j * (if j mod 5 \<in> {0, 2} then a ! (j div 5) else 0))"
        let ?h = "(\<lambda>i. (x $ (i * 5) + x $ (i * 5 + 2)) * a ! i)"
        have "(\<Sum>j = i*5..<i*5+5. ?g j) = ?h i" if "i<n-1" for i
        proof -
          have div_rule: "(i * 5 + xa) div 5 = i" if "xa <5" for xa using that by auto
          have "(\<Sum>j = i*5..<i*5+5. ?g j) = sum ?g ((+) (i * 5) ` {0..<5})"
            by (simp add: add.commute)
          also have "\<dots> = (\<Sum>j<5. x$(i*5 + j) * (if j \<in> {0, 2} then a!i else 0))" 
            using mod_mult_self3[of i 5] div_rule
            by (subst sum.reindex[of "(\<lambda>j. i*5+j)" "{0..<5}"], simp, unfold comp_def) 
              (metis (no_types, lifting) One_nat_def lessThan_atLeast0 lessThan_iff 
              nat_mod_lem not_less_eq not_numeral_less_one sum.cong)
          also have "\<dots> = x$(i*5 + 0) * a!i + x$(i*5 + 2) * a!i" 
            by (auto simp add: eval_nat_numeral split: if_splits)
          finally show ?thesis by (simp add: distrib_left mult.commute)
        qed
        then have *: "(\<Sum>i<(n-1)*5. x $ i * a0 i) = (\<Sum>i<n-1. ?h i)"
          unfolding a0_def by (subst sum.nat_group[symmetric], auto)
        have **: "(\<Sum>j = 5*(n-1)..<5*(n-1)+4. x $ j * a0 j) = ?h (n-1)"
        proof -
          have div_rule: "((n-1) * 5 + xa) div 5 = (n-1)" if "xa <4" for xa using that by auto
          have "(\<Sum>j = (n-1)*5..<(n-1)*5+4. ?g j) = sum ?g ((+) ((n-1) * 5) ` {0..<4})"
            by (simp add: add.commute)
          also have "\<dots> = (\<Sum>j<4. x$((n-1)*5 + j) * (if j \<in> {0, 2} then a!(n-1) else 0))"
          proof -
            have *: "(\<Sum>xa = 0..<4.?g ((n - 1) * 5 + xa)) =
            (\<Sum>j = 0..<4. x $ ((n - 1) * 5 + j) * (if j \<in> {0, 2} then a ! (n - 1) else 0))" 
            (is "(\<Sum>xa = 0..<4. ?g' xa) = (\<Sum>j = 0..<4. ?h' j)")
              by (rule sum.cong) auto
            show ?thesis
            using mod_mult_self3[of "n-1" 4] div_rule
            by (subst sum.reindex[of "(\<lambda>j. (n-1)*5+j)" "{0..<4}"], simp, 
              unfold comp_def lessThan_atLeast0) (use * in \<open>auto\<close>)
          qed
          also have "\<dots> = x$((n-1)*5 + 0) * a!(n-1) + x$((n-1)*5 + 2) * a!(n-1)" 
            by (auto simp add: eval_nat_numeral split: if_splits)
          finally show ?thesis unfolding a0_def by (simp add: distrib_left mult.commute)
        qed
        have "5 * (n - 1) < 5 * n - 1" using \<open>n> 0\<close> by auto
        then have ***: "(\<Sum>i<5*n-1. x $ i * a0 i) = (\<Sum>i<5*(n-1). x $ i * a0 i) +
          (\<Sum>i=5*(n-1)..<5*n-1. x $ i * a0 i)"
        by (subst split_sum_mid_less[of "5*(n-1)" "5*n-1"], auto) 
        have ****: "5 * n - 1 = 5 * (n - 1) + 4" using \<open>n> 0\<close> by auto
        show ?thesis 
          by (unfold ***, subst mult.commute[of 5 "n-1"], unfold * **** **)
             (subst sum.lessThan_Suc[of ?h "n-1", symmetric], auto simp add: \<open>n>0\<close>)
      qed
      ultimately show "(\<Sum>i<n. (x $ (i*5) + x $ (i*5+2)) * a!i) = 0" and
                      "(\<Sum>i<5*n-1. x$i * (a0_rest i)) = 0" by auto
    qed
  
    let ?eq_0'_left = "(\<Sum>i<5*n-1. x$i * (a0_rest i))"
    interpret digits 5 by (simp add: digits_def)
    have digit_a0_rest: "digit ?eq_0'_left k = 0" for k
      using eq_0' by (simp add: eq_0' digit_altdef)

text \<open>Define the digits in basis 5.\<close>
    define d1 where "d1 = (\<lambda>i. x$(i*5) + (if i<n-1 then x$(i*5+4) else 0))"
    define d2 where "d2 = (\<lambda>i. x$(i*5) + x$(i*5+1))"
    define d3 where "d3 = (\<lambda>i. (if i<n-1 then x$(i*5+4) else 0) + x$(i*5+2))"
    define d4 where "d4 = (\<lambda>i. x$(i*5) + x$(i*5+2) + x$(i*5+3))"
    define d5 where "d5 = (\<lambda>i. x$(5*i+1) + x$(5*i+2))"

    define d where "d = (\<lambda>k. 
      (if k mod 4 = 0 then 
          (if k = 0 then d5 (n-1) + d1 0 else (d1 (k div 4) + d5 (k div 4 -1))) else
      (if k mod 4 = 1 then d2 (k div 4) else                  
      (if k mod 4 = 2 then d3 (k div 4) else d4 (k div 4)))))"

text \<open>Rewrite the sum in basis 5.\<close>
    have rewrite_digits: "(\<Sum>i<5*n-1. x$i * (a0_rest i)) = (\<Sum>k<4*n. d k * 5^k)"
    proof -
      define f1::"nat \<Rightarrow> nat \<Rightarrow> int" where "f1 = (\<lambda>i j.
            ((if i<n-1 then (if j \<in> {0, 4} then 1 else 0) else (if j\<in>{0} then 1 else 0))
               * 5 ^ (4 * i) +
            (if j \<in> {0, 1} then 1 else 0) * 5 ^ (4 * i + 1) +
            (if i<n-1 then (if j \<in> {4, 2} then 1 else 0) else (if j\<in>{2} then 1 else 0)) 
              * 5 ^ (4 * i + 2) +
            (if j \<in> {0, 2, 3} then 1 else 0) * 5 ^ (4 * i + 3) +
            (if j \<in> {1, 2} then if i < n - 1 then 5 ^ (4 * (i + 1)) else 1 else 0)))"
      have "f1 (n-1) 4 = 0" unfolding f1_def by auto
      define f2 where "f2 = (\<lambda>i. 
          x $ (i * 5) * (5 ^ (4 * i) + 5 ^ (4 * i + 1) + 5 ^ (4 * i + 3)) +
          x $ (i * 5 + 1) * (5 ^ (4 * i + 1) + (if i < n - 1 then 5 ^ (4 * (i + 1)) else 1)) +
          x $ (i * 5 + 4) * (if i<n-1 then 5 ^ (4 * i) + 5 ^ (4 * i + 2) else 0) +
          x $ (i * 5 + 2) * (5 ^ (4 * i + 2) + 5 ^ (4 * i + 3) + 
            (if i < n - 1 then 5 ^ (4 * (i + 1)) else 1)) +
          x $ (i * 5 + 3) * (5 ^ (4 * i + 3)))"
      define f3 where "f3 = (\<lambda>i. 
          d1 i * (5 ^ (4 * i)) + d5 i * (if i < n - 1 then 5 ^ (4 * (i + 1)) else 1) +
          d2 i * 5 ^ (4 * i + 1) + d3 i * 5 ^ (4 * i + 2) + d4 i * 5 ^ (4 * i + 3))"
      have f2_f3: "f2 i = f3 i" if "i<n" for i 
      proof (cases "i<n-1")
        case True
        then have "f2 i = x $ (i * 5) * 5 ^ (4 * i) + x $ (i * 5) * 5 ^ (4 * i + 1) + 
          x $ (i * 5) * 5 ^ (4 * i + 3) +
          x $ (i * 5 + 1) * 5 ^ (4 * i + 1) + x $ (i * 5 + 1) * 5 ^ (4 * (i + 1)) +
          x $ (i * 5 + 4) * 5 ^ (4 * i) + x $ (i * 5 + 4) * 5 ^ (4 * i + 2) +
          x $ (i * 5 + 2) * 5 ^ (4 * i + 2) + x $ (i * 5 + 2) * 5 ^ (4 * i + 3) + 
          x $ (i * 5 + 2) * 5 ^ (4 * (i + 1)) + x $ (i * 5 + 3) * 5 ^ (4 * i + 3)"
        unfolding f2_def by (subst ring_distribs)+ simp
        also have "\<dots> = f3 i" unfolding f3_def d1_def d2_def d3_def d4_def d5_def using True 
          by (subst distrib_right)+  (simp add: mult.commute[of 5 i])
        ultimately show ?thesis by auto
      next
        case False
        then have "f2 i = x $ (i * 5) * 5 ^ (4 * i) + x $ (i * 5) * 5 ^ (4 * i + 1) + 
          x $ (i * 5) * 5 ^ (4 * i + 3) +
          x $ (i * 5 + 1) * 5 ^ (4 * i + 1) + x $ (i * 5 + 1) +
          x $ (i * 5 + 2) * 5 ^ (4 * i + 2) + x $ (i * 5 + 2) * 5 ^ (4 * i + 3) + 
          x $ (i * 5 + 2) + x $ (i * 5 + 3) * 5 ^ (4 * i + 3)"
        unfolding f2_def by (subst ring_distribs)+ simp
      also have "\<dots> = f3 i" unfolding f3_def d1_def d2_def d3_def d4_def d5_def using False 
        by(simp add: algebra_simps)
        ultimately show ?thesis by auto
      qed
      define x_pad where "x_pad = (\<lambda>i. if i<5*n-1 then x$i else 1)"
      have pad: "(\<Sum>i<5*n-1. x$i * (a0_rest i)) = (\<Sum>i<5*n. x_pad i * (a0_rest i))" 
      proof -
        have "Suc (5 * n - 1) = 5*n" using \<open>n>0\<close> by auto
        have "(\<Sum>i<5 * n - 1. x_pad i * a0_rest i) = (\<Sum>i<5 * n - 1. x$i * a0_rest i)"
          by(rule sum.cong)(auto simp: x_pad_def)
        moreover have "x_pad (5 * n - 1) * a0_rest (5 * n - 1) = 0" 
        proof -
          have "\<not>((5 * n - 1) div 5 < n - 1)" using \<open>n>0\<close> by auto
          moreover have "(5 * n - 1) mod 5 = 4" 
          proof -
            have "5 * n - 1 = 5*(n-1)+4" using \<open>n>0\<close> by auto
            show ?thesis unfolding \<open>5 * n - 1 = 5*(n-1)+4\<close> by auto
          qed
          ultimately show ?thesis
            unfolding a0_rest_def a0_last_def a1_last_def a2_def a3_last_def a4_def a5_def 
            by auto
        qed
        ultimately show ?thesis
          using sum.lessThan_Suc[of "(\<lambda>i. x_pad i * (a0_rest i))" "5 * n - 1"] 
          unfolding \<open>Suc (5 * n - 1) = 5*n\<close> by auto
      qed
      have *: "(\<Sum>i<5*n. x_pad i * (a0_rest i)) = 
        (\<Sum>i<n.(\<Sum>j<5. x_pad (i*5+j) * (a0_rest (i*5+j))))"
        (is "\<dots> =  (\<Sum>i<n.(\<Sum>j<5. ?f0 i j))")
        using sum_split_idx_prod[of "(\<lambda>i. x_pad i * a0_rest i)" n 5] 
        unfolding mult.commute[of n 5] using atLeast0LessThan by auto
      also have  "\<dots> = (\<Sum>i<n. \<Sum>j<5. x_pad (i * 5 + j) * f1 i j)"
      proof (subst sum.cong[of _ _ "(\<lambda>i. (\<Sum>j<(5::nat). ?f0 i j))" 
             "(\<lambda>i. (\<Sum>j<(5::nat).  x_pad (i * 5 + j) * f1 i j))", symmetric], simp, goal_cases)
        case (1 i)
        have **: "a0_rest (i * 5 + j) = f1 i j"    
          if "j<5" for j using that lt_5_split[of j] 1
        unfolding f1_def a0_rest_def a0_rest'_def a0_last_def
               a1_def a1_last_def a2_def a3_def a3_last_def a4_def a5_def
          by auto
        show ?case
          by (rule sum.cong) (use ** 1 in auto)
      next
        case 2
        then show ?case using * by auto
      qed
      also have "\<dots> = (\<Sum>i<n. f2 i)"
      proof (rule sum.cong[OF refl], goal_cases)
        case (1 i)
        show ?case 
        proof (cases "i<n-1")
          case True
          then show ?thesis unfolding f1_def x_pad_def f2_def 
          by (auto simp add: eval_nat_numeral)
        next
          case False
          then have "i = n-1" using 1 by auto
          then have "(\<Sum>j<5. x_pad (i * 5 + j) * f1 i j) = 
            x_pad ((n-1) * 5 + 0) * f1 (n-1) 0 + 
            x_pad ((n-1) * 5 + 1) * f1 (n-1) 1 + 
            x_pad ((n-1) * 5 + 2) * f1 (n-1) 2 + 
            x_pad ((n-1) * 5 + 3) * f1 (n-1) 3 +
            x_pad ((n-1) * 5 + 4) * f1 (n-1) 4" 
          by (simp add: eval_nat_numeral)
          also have "\<dots>  = 
            x_pad ((n-1) * 5 + 0) * f1 (n-1) 0 + 
            x_pad ((n-1) * 5 + 1) * f1 (n-1) 1 + 
            x_pad ((n-1) * 5 + 2) * f1 (n-1) 2 + 
            x_pad ((n-1) * 5 + 3) * f1 (n-1) 3" 
          using \<open>f1 (n-1) 4 = 0\<close> by auto
          also have "\<dots> = f2 i"
          proof - 
            have "x_pad ((n-1) * 5 + 0) * f1 (n-1) 0 = 
              x $ ((n-1)*5) * (5^(4 * (n - 1)) + 5 ^ (4 * (n - 1) + 1) + 5 ^ (4 * (n - 1) + 3))"
            unfolding f1_def x_pad_def using \<open>n>0\<close> by auto
            moreover have "x_pad ((n-1) * 5 + 1) * f1 (n-1) 1 =
              x $ ((n-1)*5 + 1) * (5^(4 * (n - 1) + 1) + 1)"
            unfolding f1_def x_pad_def using \<open>n>0\<close> by auto
            moreover have "x_pad ((n-1) * 5 + 2) * f1 (n-1) 2 =
              x $ ((n-1)*5 + 2) * (5^(4 * (n - 1) + 2) + 5 ^ (4 * (n - 1) + 3) + 1)"
            unfolding f1_def x_pad_def using \<open>n>0\<close> by auto
            moreover have "x_pad ((n-1) * 5 + 3) * f1 (n-1) 3 =
              x $ ((n-1)*5 + 3) * 5^(4 * (n - 1) + 3)" 
            unfolding f1_def x_pad_def using \<open>n>0\<close> by auto
            ultimately show ?thesis unfolding f2_def using \<open>i=n-1\<close> by auto
          qed
          finally show ?thesis by auto
        qed
      qed
      also have "\<dots> = (\<Sum>i<n-1. f2 i) + f2 (n-1)"
        by (subst sum.lessThan_Suc[of f2 "n-1", symmetric])
        (use Suc_diff_1 \<open>0 < length a\<close> n_def in \<open>presburger\<close>)
      also have "\<dots> = (\<Sum>i<n-1. f3 i) + f3 (n-1)"
        by (subst sum.cong[of "{..<n-1}" "{..<n-1}" f2 f3], auto simp add: f2_f3)
           (use f2_f3[of "n-1"] \<open>length a > 0\<close> n_def in \<open>auto\<close>)
      also have "\<dots> = (\<Sum>i<n-1.  d1 i * (5 ^ (4 * i)) + d5 i *  5 ^ (4 * (i + 1)) +
          d2 i * 5 ^ (4 * i + 1) + d3 i * 5 ^ (4 * i + 2) + d4 i * 5 ^ (4 * i + 3) ) +
          d1 (n-1) * (5 ^ (4 * (n-1))) + d5 (n-1) + d2 (n-1) * 5 ^ (4 * (n-1) + 1) + 
          d3 (n-1) * 5 ^ (4 * (n-1) + 2) + d4 (n-1) * 5 ^ (4 * (n-1) + 3)"
        unfolding f3_def by auto
      also have "\<dots> = (\<Sum>i<n-1.  d1 i * (5 ^ (4 * i))) + d1 (n-1) * (5 ^ (4 * (n-1))) +
                      (\<Sum>i<n-1. d2 i * 5 ^ (4 * i + 1)) + d2 (n-1) * 5 ^ (4 * (n-1) + 1) + 
                      (\<Sum>i<n-1. d3 i * 5 ^ (4 * i + 2)) + d3 (n-1) * 5 ^ (4 * (n-1) + 2) + 
                      (\<Sum>i<n-1. d4 i * 5 ^ (4 * i + 3)) + d4 (n-1) * 5 ^ (4 * (n-1) + 3) +
                      (\<Sum>i<n-1. d5 i *  5 ^ (4 * (i + 1))) + d5 (n-1)"
      by auto
      also have "\<dots> = (\<Sum>i<n. d1 i * (5 ^ (4 * i))) +
                      (\<Sum>i<n. d2 i * 5 ^ (4 * i + 1)) + 
                      (\<Sum>i<n. d3 i * 5 ^ (4 * i + 2)) + 
                      (\<Sum>i<n. d4 i * 5 ^ (4 * i + 3)) +
                      (\<Sum>i<n-1. d5 i *  5 ^ (4 * (i + 1))) +
                       d5 (n-1)" (is "\<dots> = ?f4")
        using sum.lessThan_Suc[of "(\<lambda>i. d1 i * 5 ^ (4 * i))" "n-1"]
        using sum.lessThan_Suc[of "(\<lambda>i. d2 i * 5 ^ (4 * i + 1))" "n-1"]
        using sum.lessThan_Suc[of "(\<lambda>i. d3 i * 5 ^ (4 * i + 2))" "n-1"]
        using sum.lessThan_Suc[of "(\<lambda>i. d4 i * 5 ^ (4 * i + 3))" "n-1"]
        using \<open>0 < length a\<close> n_def by force
      finally have "(\<Sum>i<5*n. x_pad i * (a0_rest i)) = ?f4" using * by auto
      then have "(\<Sum>i<5*n-1. x$i * (a0_rest i)) = ?f4" using pad by auto
      moreover have "(\<Sum>i<n. d1 i * (5 ^ (4 * i))) = d1 0 + (\<Sum>i<n-1. d1 (i + 1) * (5 ^ (4 * (i+1))))"
        using sum.lessThan_Suc_shift[of "(\<lambda>i. d1 i * 5 ^ (4 * i))" "n-1"] 
        using \<open>0 < length a\<close> n_def by force
      moreover have "(\<Sum>i<n-1. d1 (i + 1) * (5 ^ (4 * (i+1)))) + 
        (\<Sum>i<n-1. d5 i *  5 ^ (4 * (i + 1))) =
        (\<Sum>i<n-1. (d1 (i+1) + d5 i) *  5 ^ (4 * (i + 1)))" 
        unfolding sum.distrib[of "(\<lambda>i. d1 (i + 1) * 5 ^ (4 * (i + 1)))" 
          "(\<lambda>i. d5 i * 5 ^ (4 * (i + 1)))" "{..<n-1}", symmetric] 
          distrib_right by simp 
      moreover have "(\<Sum>i<n-1. (d1 (i+1) + d5 i) *  5 ^ (4 * (i + 1))) = 
        (\<Sum>i\<in>{1..<n}. (d1 i + d5 (i-1)) *  5 ^ (4 * i))" 
      proof -
        have "bij_betw (\<lambda>i. i - 1) {1..<n} {..<n - 1}" unfolding bij_betw_def 
          by (auto simp add: inj_on_def) 
             (metis One_nat_def Suc_diff_1 Suc_leI Suc_mono \<open>0 < length a\<close> add_diff_cancel_left' 
              atLeastLessThan_iff image_eqI n_def plus_1_eq_Suc zero_less_Suc)
        then show ?thesis
        by (subst sum.reindex_bij_betw[of "(\<lambda>i. i-1)" "{1..<n}" "{..<n-1}" 
          "(\<lambda>i. (d1 (i + 1) + d5 i) * 5 ^ (4 * (i + 1)))", symmetric]) auto
      qed
      moreover have "(\<Sum>i\<in>{1..<n}. (d1 i + d5 (i-1)) *  5 ^ (4 * i)) + d1 0 + d5 (n-1) =
        (\<Sum>i<n. (if i = 0 then d5 (n-1) + d1 0 else (d1 i + d5 (i-1))) * 5 ^ (4 * i))" 
         using sum.atLeast_Suc_lessThan[OF \<open>0<length a\<close>, 
          of "(\<lambda>i. (if i = 0 then d5 (n - 1) + d1 0 else d1 i + d5 (i - 1)) * 5 ^ (4 * i))"] 
          unfolding atLeast0LessThan n_def by (auto)
      ultimately have "(\<Sum>i<5*n-1. x$i * (a0_rest i)) = (\<Sum>i<n. 
        (if i = 0 then d5 (n - 1) + d1 0 else d1 i + d5 (i - 1)) * 5 ^ (4 * i) +
         d2 i * 5 ^ (4 * i + 1) + d3 i * 5 ^ (4 * i + 2) + d4 i * 5 ^ (4 * i + 3))" 
        (is "(\<Sum>i<5*n-1. x$i * (a0_rest i)) = (\<Sum>i<n. ?f5 i)") by auto
      moreover have "\<dots> = (\<Sum>i<n. (\<Sum>j<4. d (i*4+j) * 5^(i*4+j)))"
      proof (rule sum.cong, goal_cases)
        case (2 i)
        have d_rew: "(\<Sum>j<4. d (i * 4 + j) * 5 ^ (i * 4 + j)) = 
          d (i * 4) * 5 ^ (i * 4) + d (i * 4 + 1) * 5 ^ (i * 4 + 1) +
          d (i * 4 + 2) * 5 ^ (i * 4 + 2) + d (i * 4 + 3) * 5 ^ (i * 4 + 3)" 
          by (simp add: eval_nat_numeral)
        have d1_rew: "d (i * 4) = (if i = 0 then d5 (n - 1) + d1 0 else d1 i + d5 (i - 1))"
          unfolding d_def by auto
        have d2_rew: "d (i*4+1) = d2 i" unfolding d_def
          by (metis add.commute add.right_neutral div_mult_self3 mod_Suc mod_div_trivial 
          mod_mult_self2_is_0 one_eq_numeral_iff plus_1_eq_Suc semiring_norm(85) zero_neq_numeral)
        have d3_rew: "d (i*4+2) = d3 i" unfolding d_def
          by (metis add.commute add_2_eq_Suc' add_cancel_right_left div_less div_mult_self1 
          less_Suc_eq mod_mult_self1 nat_mod_lem numeral_Bit0 one_add_one zero_neq_numeral)
        have d4_rew: "d (i*4+3) = d4 i" unfolding d_def by auto
        show ?case by (subst d_rew, subst d1_rew, subst d2_rew, subst d3_rew, subst d4_rew) 
           (auto simp add: mult.commute)
      qed auto
      moreover have "\<dots> = (\<Sum>k<4*n. d k * 5^k)" 
        using sum_split_idx_prod[of "(\<lambda>k. d k * 5^k)" n 4, symmetric]
        by (simp add: lessThan_atLeast0 mult.commute)
      ultimately show ?thesis by auto
    qed

text \<open>Some helping lemmas to get equations.\<close>
    have xi_le_1: "\<bar>x$i\<bar>\<le>1" if "i< dim_vec x" for i 
      using 1(5) that unfolding linf_norm_vec_Max by auto
    have xs_le_2: "\<bar>x$i + x$j\<bar>\<le>2" if "i< dim_vec x" "j< dim_vec x" for i j
    proof - 
      have "\<bar>x$i + x$j\<bar> \<le> \<bar>x$i\<bar> + \<bar>x$j\<bar>"
      by (auto simp add: abs_triangle_ineq)
      then show ?thesis using xi_le_1[OF that(1)] xi_le_1[OF that(2)] by auto
    qed

    have if_xi_le_1: "\<bar>(if i < n - 1 then x $ (i * 5 + 4) else 0)\<bar> \<le> 1" 
      if "i< n" for i 
      using that xi_le_1[of "i*5+4"] unfolding dim_vec_x_5n by auto

    have prec_0: "i * 5 < dim_vec x" if "i<n" for i 
      using that unfolding dim_vec_x_5n  by auto
    have prec_i: "i * 5 + j < dim_vec x" if "i<n" "j<4" for i j 
      using that unfolding dim_vec_x_5n  by auto

    have abs_d1: "\<bar>d1 i\<bar>\<le>2" if "i<n" for i unfolding d1_def 
      using xi_le_1[OF prec_0[OF that]] if_xi_le_1[OF that] by auto

    have abs_d2: "\<bar>d2 i\<bar>\<le>2" if "i<n" for i unfolding d2_def
      using xi_le_1[OF prec_0[OF that]] xi_le_1[OF prec_i[OF that, where j=1]] by auto

    have abs_d3: "\<bar>d3 i\<bar>\<le>2" if "i<n" for i unfolding d3_def
      using xi_le_1[OF prec_i[OF that, where j=2]] if_xi_le_1[OF that] by auto

    have abs_d4: "\<bar>d4 i\<bar>\<le>3" if "i<n" for i unfolding d4_def
      using xi_le_1[OF prec_0[OF that]] 
        xs_le_2[OF prec_i[OF that, where j=2] prec_i[OF that, where j=3]] by auto

    have abs_d5: "\<bar>d5 i\<bar>\<le>2" if "i<n" for i unfolding d5_def
      using xi_le_1[OF prec_i[OF that, where j=2]] 
        xi_le_1[OF prec_i[OF that, where j=1]] by (simp add: mult.commute)

    have " \<bar>d5 (n - Suc 0) + d1 0\<bar> < 5"
      using abs_d5[of "n-1"] abs_d1[of 0] \<open>0 < length a\<close> n_def by fastforce
    moreover have "\<bar>d1 (i div 4) + d5 (i div 4 - Suc 0)\<bar> < 5" 
      if "0 < i" and "i<4*n" and "i mod 4 = 0" for i 
    using that abs_d1[of "i div 4"] abs_d5[of "i div 4 - 1"] \<open>0 < length a\<close> n_def by fastforce
    moreover have "\<bar>d2 (i div 4)\<bar> < 5" if "i<4*n" and "i mod 4 = 1" for i 
    using that abs_d2[of "i div 4"] \<open>0 < length a\<close> n_def by fastforce
    moreover have "\<bar>d3 (i div 4)\<bar> < 5" if "i<4*n" and "i mod 4 = 2" for i 
    using that abs_d3[of "i div 4"] \<open>0 < length a\<close> n_def by fastforce
    moreover have "\<bar>d4 (i div 4)\<bar> < 5" if "i<4*n" and "i mod 4 = 3" for i 
    using that abs_d4[of "i div 4"] \<open>0 < length a\<close> n_def by fastforce
    ultimately have d_lt_5: "\<bar>d i\<bar> < 5" if "i < 4 * n" for i
      using that by (subst mod_4_choices[of i], unfold d_def, auto)
    
    have sum_zero: "(\<Sum>k<4*n. d k * 5^k) = 0" using eq_0' rewrite_digits by auto

    then have d_eq_0: "d k = 0" if "k<4*n" for k 
      using respresentation_in_basis_eq_zero[OF sum_zero _ _ that] d_lt_5 by auto

text \<open>These are the main equations.\<close>
    have eq_1: "x$(i*5) + (if i <n-1 then x$(i*5+4) else 0) + x$((i-1)*5+1) + x$((i-1)*5+2) = 0"
       if "i\<in>{1..<n}" for i
      using that d_eq_0[of "4*i"] unfolding d_def d1_def d5_def by (auto simp add: mult.commute)

    have eq_2: "x$0 + (if 0<n-1 then x $ 4 else 0) + x$((n-1)*5+1) + x$((n-1)*5+2) = 0" 
      using d_eq_0[of "0"] unfolding d_def d1_def d5_def
      by (smt (z3) \<open>0 < length a\<close> add_cancel_right_left bits_mod_0 bot_nat_0.not_eq_extremum 
      mult.commute mult_is_0 n_def zero_neq_numeral)

    have eq_3: "x$(i*5) + x$(i*5+1) = 0" if "i\<in>{0..<n}" for i 
      using that d_eq_0[of "4*i+1"] unfolding d_def d2_def
      by (auto, metis add.right_neutral div_less div_mult_self1 mult.commute one_less_numeral_iff 
        plus_1_eq_Suc semiring_norm(76) zero_neq_numeral)

    have eq_4: "(if i<n-1 then x$(i*5+4) else 0) + x$(i*5+2) = 0" if "i\<in>{0..<n}" for i 
    proof -
      have **: "(4 * i + 2) div 4 = i" by auto
      have *: "(if (4 * i + 2) div 4 < n - 1 then x $ ((4 * i + 2) div 4 * 5 + 2) else 0) +
        x $ ((4 * i + 2) div 4 * 5 + 3) = (if i<n-1 then x$(i*5+2) else 0) + x$(i*5+3)"
        unfolding ** by auto
      show ?thesis using that d_eq_0[of "4*i+2"] unfolding d_def d3_def *
      by (smt (verit, ccfv_threshold) \<open>0 < length a\<close> add.right_neutral add_self_div_2 
        add_self_mod_2 atLeastLessThan_iff bits_one_mod_two_eq_one div_mult2_eq 
        div_mult_self4 mod_mult2_eq mod_mult_self3 mult.commute mult_2 mult_is_0 n_def 
        nat_1_add_1 nat_mod_lem neq0_conv numeral_Bit0 one_div_two_eq_zero)
    qed

    have eq_5: "x$(i*5) + x$(i*5+2) + x$(i*5+3) = 0" if "i\<in>{0..<n}" for i 
      using that d_eq_0[of "4*i+3"] unfolding d_def d4_def by auto
    
    have eq_3': "x$(i*5) = - x$(i*5+1)" if "i\<in>{0..<n}" for i
      using eq_3[OF that] by auto

    have eq_4': "x$(i*5+4) = - x$(i*5+2)" if "i\<in>{0..<n-1}" for i
      using that eq_4[of i] by force


    have eq_1': "x$(i*5) + (if i<n-1 then x$(i*5+4) else 0) = 
      x$((i-1)*5) + x$((i-1)*5+4)" if "i\<in>{1..<n}" for i 
    proof -
      have *: "i - 1 \<in> {0..<n}" using that by auto
      have **: "i-1 \<in>{0..<n-1}" using that by auto
      then show ?thesis using eq_1[OF that] 
      by (subst eq_3'[OF *], subst eq_4'[OF **], auto)
    qed

text \<open>This defines the weight of the solution, since $x_{i,0} + x_{i,4}$ does not depend on 
    the index i.
    We take $x_{n-1,0} + x_{n-1,4}$, since we omitted the last element (thus $x_{n-1,4} = 0$) 
    to ensure that the weight has absolute value at most $1$.\<close>
    define w where "w = x$((n-1)*5)"

    have w_eq_02: "w = x$(i*5) + (if i<n-1 then x$(i*5+4) else 0)" if "i\<in>{0..<n}" for i
    proof -
      have "i\<le>n-1" using that by auto
      then show ?thesis
      proof (induct rule: Nat.inc_induct)
        case (step m)
        then show ?case unfolding w_def using eq_1'[of "Suc m"] by auto
      qed (unfold w_def, auto)
    qed

    have "\<bar>w\<bar> \<le> 1"  using xi_le_1[of "(n-1)*5"] \<open>n > 0\<close>
      unfolding w_def dim_vec_x_5n by auto

text \<open>Rule out the all zero solution.\<close>
    moreover have "w\<noteq>0"
    proof (rule ccontr)
      assume "\<not> w \<noteq> 0"
      then have "w = 0" by blast
      then have "x$((n-1)*5) = 0" unfolding w_def by auto
      have zero_eq_min2: "x$(i*5) = - (if i<n-1 then x$(i*5+4) else 0)" if "i\<in>{0..<n}" for i
        using w_eq_02[OF that] \<open>w=0\<close> by auto
      have two0_plus_4: "2 * x$(i*5) + x$(i*5+3) = 0" if "i \<in> {0..<n-1}" for i 
        using that eq_5[of i] eq_4'[OF that] zero_eq_min2 by auto   

      have p_zero: "x$(i*5) = 0" if "i<n"  for i 
        using that 
      proof (cases "i=n-1")
        case True
        then show ?thesis using that \<open>x$((n-1)*5) = 0\<close> by auto
      next
        case False
        then have "i \<in> {0..<n - 1}" using that by auto
        show ?thesis
        proof (rule ccontr)
          assume "x $ (i * 5) \<noteq> 0"
          then have "\<bar>2 * x $ (i * 5) + x $ (i * 5 + 3)\<bar>\<ge>1" 
            using xi_le_1[OF prec_0[where i=i]] xi_le_1[OF prec_i[where i=i and j=3]] 
            by (auto simp add: \<open>i<n\<close>)
          then show False using two0_plus_4[OF \<open>i \<in> {0..<n - 1}\<close>] by auto
        qed
      qed
      have "x$j = 0" if "j<5*n" "j mod 5 = 0" for j
      proof -
        obtain i where "i*5 = j" "i<n" 
        by (metis \<open>j < 5 * n\<close> \<open>j mod 5 = 0\<close> mod_eq_0D mult.commute nat_mult_less_cancel1 
          zero_less_numeral)
        then show ?thesis unfolding \<open>i*5 = j\<close>[symmetric] using p_zero[OF \<open>i<n\<close>] by auto
      qed

      moreover have p_one: "x$(i*5+1) = 0" if "i<n"  for i 
        using p_zero[OF that] eq_3' that by auto
      then have "x$j = 0" if "j<5*n" "j mod 5 = 1" for j
      proof -
        obtain i where "i*5+1 = j" "i<n" using \<open>j<5*n\<close> \<open>j mod 5 = 1\<close> 
        by (metis add.commute less_mult_imp_div_less mod_mult_div_eq mult.commute)
        then show ?thesis unfolding \<open>i*5+1 = j\<close>[symmetric] using p_one[OF \<open>i<n\<close>] by auto
      qed

      moreover have p_four: "x$(i*5+4) = 0" if "i<n-1" for i 
        using w_eq_02[of i] that p_zero unfolding \<open>w=0\<close> by auto
      then have "x$j = 0" if "j<5*n-1" "j mod 5 = 4" for j
      proof -
        obtain i where "i*5+4 = j" "i<n-1" using \<open>j<5*n-1\<close> \<open>j mod 5 = 4\<close>
        by (metis add.assoc add.commute less_Suc_eq less_diff_conv less_mult_imp_div_less 
          mod_mult_div_eq mult.commute mult_Suc_right not_less_eq numeral_nat(3) plus_1_eq_Suc)
        then show ?thesis unfolding \<open>i*5+4 = j\<close>[symmetric] using p_four by auto
      qed

      moreover have p_two: "x$(i*5+2) = 0" if "i<n"  for i
      proof (cases "i<n-1")
        case True
        then show ?thesis using p_four[OF \<open>i<n-1\<close>] eq_4' by auto
      next
        case False
        then have "i=n-1" using that by auto
        show ?thesis using eq_4[of "n-1"] unfolding \<open>i=n-1\<close> using \<open>n>0\<close> by auto
      qed
      then have "x$j = 0" if "j<5*n" "j mod 5 = 2" for j
      proof -
        obtain i where "i*5+2 = j" "i<n" using \<open>j<5*n\<close> \<open>j mod 5 = 2\<close> 
        by (metis add.commute less_mult_imp_div_less mod_mult_div_eq mult.commute)
        then show ?thesis unfolding \<open>i*5+2 = j\<close>[symmetric] using p_two[OF \<open>i<n\<close>] by auto
      qed

      moreover have p_three: "x$(i*5+3) = 0" if "i<n"  for i 
        using eq_5[of i] that p_two[OF that] p_zero[OF that] by auto
      then have "x$j = 0" if "j<5*n" "j mod 5 = 3" for j
      proof -
        obtain i where "i*5+3 = j" "i<n" using \<open>j<5*n\<close> \<open>j mod 5 = 3\<close> 
        by (metis add.commute less_mult_imp_div_less mod_mult_div_eq mult.commute)
        then show ?thesis unfolding \<open>i*5+3 = j\<close>[symmetric] using p_three[OF \<open>i<n\<close>] by auto
      qed
      ultimately have "x$j = 0" if "j<5*n-1" for j 
      using mod_5_choices[of j "(\<lambda>j. x $ j = 0)"] that by auto
      then have "x = 0\<^sub>v (dim_vec x)" unfolding dim_vec_x_5n[symmetric] by auto
      then show False using 1(4) by auto
    qed

text \<open>Then we can deduce the wanted property for both cases $w=1$ and $w=-1$. 
  The only differences between the two cases is the switch of signs.\<close>
    ultimately have "w=1 \<or> w = -1" by auto
    then consider (pos) "w=1" | (neg) "w=-1" by blast
    then show ?thesis
    proof cases
      case pos
      have 01:"(x$(i*5) = 0 \<and> x$(i*5+4) = 1) \<or> (x$(i*5) = 1 \<and> x$(i*5+4) = 0)" if "i<n-1" for i
      proof -
        have "i * 5 < dim_vec x" using that \<open>n>0\<close> unfolding dim_vec_x_5n by auto
        then have "x$(i*5) \<in> {-1,0,1}" using xi_le_1[of "i*5"] 
          by auto
        then consider (minus) "x$(i*5) = -1" | (zero) "x$(i*5) = 0" | (plus) "x$(i*5) = 1" 
          by blast
        then show ?thesis 
        proof (cases)
          case minus
          then have "2 = x $ (i * 5 + 4)" using w_eq_02[of i] that \<open>w=1\<close> by auto
          then have False using xi_le_1[of "i*5+4"] that unfolding dim_vec_x_5n
            by linarith
          then show ?thesis by auto
        next
          case zero
          then have "x $ (i * 5 + 4) = 1" using w_eq_02[of i] that unfolding \<open>w=1\<close> by auto
          then show ?thesis using zero by auto
        next
          case plus
          then have "x $ (i * 5 + 4) = 0" using w_eq_02[of i] that unfolding \<open>w=1\<close> by auto
          then show ?thesis using plus by auto
        qed
      qed

      have "n-1\<in>I" using w_def unfolding \<open>w=1\<close> I_def n_def[symmetric] 
        by (auto simp add: \<open>n>0\<close> mult.commute)

      have I_0: "x$(i*5) = 1" if "i\<in>I" for i 
      proof (cases "i<n-1")
        case True
        then show ?thesis using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then show ?thesis using w_def \<open>w=1\<close> by auto
      qed
      have I_2: "x$(i*5+2) = 0" if "i\<in>I" for i 
      proof (cases "i<n-1")
        case True
        then have "x $ (i * 5 + 4) = 0" using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
        then show ?thesis using eq_4[of i] that True unfolding I_def n_def[symmetric] by auto
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then have "x$(i*5+1) = -1" using I_0[OF that] eq_3'[of i] by (simp add: \<open>0 < n\<close>)
        moreover have "1 + x $ (i * 5 + 1) + x $ (i * 5 + 2) = 0"
          using eq_2 w_eq_02[of 0] unfolding \<open>i=n-1\<close>
          by (metis \<open>0 < n\<close> add_cancel_right_left atLeast0LessThan 
            lessThan_iff mult_zero_left pos)
        ultimately show ?thesis by auto
      qed
      have notI_0: "x$(i*5) = 0" if "i\<in>{0..<n} - I" for i 
      proof (cases "i<n-1")
        case True
        then show ?thesis using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then show ?thesis using \<open>n-1\<in>I\<close> that by auto
      qed
      have notI_2: "x$(i*5+2) = -1" if "i\<in>{0..<n} - I" for i 
      proof (cases "i<n-1")
        case True
        then have "x $ (i * 5 + 4) = 1" using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
        then show ?thesis using eq_4[of i] that True unfolding I_def n_def[symmetric] by auto
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then show ?thesis using \<open>n-1\<in>I\<close> that by auto
      qed

      have "0 = (\<Sum>i\<in>I. (x $ (i * 5) + x $ (i * 5 + 2)) * a ! i) + 
        (\<Sum>i\<in>{0..<n} - I. (x $ (i * 5) + x $ (i * 5 + 2)) * a ! i)" 
        unfolding eq_0[symmetric] 
        by (subst sum.subset_diff[of I]) (auto simp add: I_def n_def lessThan_atLeast0)
      moreover have "(x $ (i * 5) + x $ (i * 5 + 2)) = 1" if "i\<in>I" for i 
        using I_0 I_2 that by auto
      moreover have "(x $ (i * 5) + x $ (i * 5 + 2)) = -1" if "i\<in>{0..<n} - I" for i 
        using notI_0 notI_2 that by auto
      ultimately have "0 = (\<Sum>i\<in>I. a ! i) - (\<Sum>i\<in>{0..<n} - I. a ! i)" 
        by (auto simp add: sum_negf)
      then show ?thesis unfolding n_def by auto
    next
      case neg
      have 01:"(x$(i*5) = 0 \<and> x$(i*5+4) = -1) \<or> (x$(i*5) = -1 \<and> x$(i*5+4) = 0)" if "i<n-1" for i
      proof -
        have "i * 5 < dim_vec x" using that \<open>n>0\<close> unfolding dim_vec_x_5n by auto
        then have "x$(i*5) \<in> {-1,0,1}" using xi_le_1[of "i*5"] 
          by auto
        then consider (minus) "x$(i*5) = -1" | (zero) "x$(i*5) = 0" | (plus) "x$(i*5) = 1" 
          by blast
        then show ?thesis 
        proof (cases)
          case plus
          then have "-2 = x $ (i * 5 + 4)" using w_eq_02[of i] that \<open>w=-1\<close> by force
          then have False using xi_le_1[of "i*5+4"] that unfolding dim_vec_x_5n
            by linarith
          then show ?thesis by auto
        next
          case zero
          then have "x $ (i * 5 + 4) = -1" using w_eq_02[of i] that unfolding \<open>w=-1\<close> by auto
          then show ?thesis using zero by auto
        next
          case minus
          then have "x $ (i * 5 + 4) = 0" using w_eq_02[of i] that unfolding \<open>w=-1\<close> by auto
          then show ?thesis using minus by auto
        qed
      qed

      have "n-1\<in>I" using w_def unfolding \<open>w=-1\<close> I_def n_def[symmetric] 
        by (auto simp add: \<open>n>0\<close> mult.commute)

      have I_0: "x$(i*5) = -1" if "i\<in>I" for i 
      proof (cases "i<n-1")
        case True
        then show ?thesis using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then show ?thesis using w_def \<open>w=-1\<close> by auto
      qed
      have I_2: "x$(i*5+2) = 0" if "i\<in>I" for i 
      proof (cases "i<n-1")
        case True
        then have "x $ (i * 5 + 4) = 0" using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
        then show ?thesis using eq_4[of i] that True unfolding I_def n_def[symmetric] by auto
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then have "x$(i*5+1) = 1" using I_0[OF that] eq_3'[of i] by (simp add: \<open>0 < n\<close>)
        moreover have "-1 + x $ (i * 5 + 1) + x $ (i * 5 + 2) = 0"
          using eq_2 w_eq_02[of 0] unfolding \<open>i=n-1\<close>
          by (metis \<open>0 < n\<close> add_cancel_right_left lessThan_atLeast0 lessThan_iff 
            mult_zero_left neg)
        ultimately show ?thesis by auto
      qed
      have notI_0: "x$(i*5) = 0" if "i\<in>{0..<n} - I" for i 
      proof (cases "i<n-1")
        case True
        then show ?thesis using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then show ?thesis using \<open>n-1\<in>I\<close> that by auto
      qed
      have notI_2: "x$(i*5+2) = 1" if "i\<in>{0..<n} - I" for i 
      proof (cases "i<n-1")
        case True
        then have "x $ (i * 5 + 4) = -1" using 01[OF True] that unfolding I_def n_def[symmetric] 
        by (simp add: mult.commute)
        then show ?thesis using eq_4[of i] that True unfolding I_def n_def[symmetric] by auto
      next
        case False
        then have "i=n-1" using that unfolding I_def n_def[symmetric] by auto
        then show ?thesis using \<open>n-1\<in>I\<close> that by auto
      qed

      have "0 = (\<Sum>i\<in>I. (x $ (i * 5) + x $ (i * 5 + 2)) * a ! i) + 
        (\<Sum>i\<in>{0..<n} - I. (x $ (i * 5) + x $ (i * 5 + 2)) * a ! i)" 
        unfolding eq_0[symmetric] 
        by (subst sum.subset_diff[of I]) (auto simp add: I_def n_def lessThan_atLeast0)
      moreover have "(x $ (i * 5) + x $ (i * 5 + 2)) = -1" if "i\<in>I" for i 
        using I_0 I_2 that by auto
      moreover have "(x $ (i * 5) + x $ (i * 5 + 2)) = 1" if "i\<in>{0..<n} - I" for i 
        using notI_0 notI_2 that by auto
      ultimately have "0 = (\<Sum>i\<in>I. a ! i) - (\<Sum>i\<in>{0..<n} - I. a ! i)" 
        by (auto simp add: sum_negf)
      then show ?thesis unfolding n_def by auto
    qed
  qed
  ultimately show ?case using \<open>length a > 0\<close> by auto
qed



text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_bhle_partition partition_problem_nonzero bhle"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 a)
  then show ?case using well_defined_reduction_subset_sum by auto
next
  case (2 a)
  then show ?case using NP_hardness_reduction_subset_sum by auto
qed

end