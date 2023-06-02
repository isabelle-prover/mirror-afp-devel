theory Subset_Sum

imports 
  Main
  Partition
  "Jordan_Normal_Form.Matrix"
begin

section \<open>Subset Sum Problem\<close>

text \<open>The Subset Sum Problem is a common NP-hard Problem. \<close>

definition subset_sum :: "((int vec) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int vec. 
    (\<forall>i<dim_vec xs. xs$i \<in> {0,1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as)}"


definition subset_sum_nonzero :: "((int vec) * int) set" where
  "subset_sum_nonzero \<equiv> {(as,s). (\<exists>xs::int vec. 
    (\<forall>i<dim_vec xs. xs$i \<in> {0,1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as) \<and> dim_vec as \<noteq> 0}"

definition subset_sum_list :: "((int list) * int) set" where
  "subset_sum_list \<equiv> {(as,s). (\<exists>xs::int list. 
    (\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as)}"



text \<open>Reduction Subset Sum to Partition.\<close>

definition reduce_subset_sum_partition:: "(int list) \<Rightarrow> ((int list) * int)" where
  "reduce_subset_sum_partition \<equiv> 
    (\<lambda> a. (a, (if sum_list a mod 2 = 0 then sum_list a div 2 else (\<Sum>i<length a. \<bar>a!i\<bar>) + 1)))"


text \<open>Well-definedness of reduction function\<close>

lemma sum_list_map_2:
  assumes "length a = length xs"
  shows "(sum_list (map2 (*) a xs)) = (\<Sum>i<length a. a!i * xs!i)"
using assms  proof (induct rule: list_induct2)
  case (Cons x xs y ys)
  have "(\<Sum>i<length ys. (x # xs) ! i * (y # ys) ! i) + (x # xs) ! length ys * (y # ys) ! length ys = 
    (\<Sum>i\<le>length ys. (x # xs) ! i * (y # ys) ! i)"
    by (metis (no_types, lifting) lessThan_Suc_atMost sum.lessThan_Suc)
  also have "\<dots> = (x # xs) ! 0 * (y # ys) ! 0 + 
    (\<Sum>i<length ys. (x # xs) ! (i+1) * (y # ys) ! (i+1))"
    using sum.atMost_shift[of "(\<lambda>i. (x # xs) ! i * (y # ys) ! i)" "length ys"] by auto
  also have "\<dots> = x * y + sum_list (map2 (*) xs ys)" using Cons by auto
  finally have "x * y + sum_list (map2 (*) xs ys) = (\<Sum>i<length ys. (x # xs) ! i * (y # ys) ! i) + 
    (x # xs) ! length ys * (y # ys) ! length ys" by presburger
  then show ?case using Cons by auto
qed auto 


lemma ex_01_list: 
  assumes "I\<subseteq>{0..<n}"
  shows "\<exists>xs::int list. (\<forall>i\<in>I. xs ! i = 1) \<and> (\<forall>i\<in>{0..<n}-I. xs ! i = 0) \<and> length xs = n"
using assms proof (induct n arbitrary: I)
  case (Suc n)
  define I' where "I' = I \<inter> {0..<n}"
  then have "I'\<subseteq> {0..<n}" by auto
  obtain xs'::"int list" where xs'_def:
    "(\<forall>i\<in>I'. xs' ! i = 1) \<and> (\<forall>i\<in>{0..<n} - I'. xs' ! i = 0) \<and> length xs' = n"
    using Suc(1)[OF \<open>I'\<subseteq>{0..<n}\<close>] by blast
  define xs where "xs = xs' @ [if n \<in> I then 1 else 0]"
  then have eq: "xs ! i = xs' ! i" if "i<n" for i using that
    by (simp add: nth_append xs'_def)+
  have 1: "(\<forall>i\<in>I. xs ! i = 1)" unfolding xs_def 
  proof (split if_split, safe, goal_cases)
    case (1 i)
    then have "\<not> i < n \<Longrightarrow> [1] ! (i - n) = 1"
    by (metis Suc.prems atLeast0LessThan atMost_iff cancel_comm_monoid_add_class.diff_cancel 
      lessThan_Suc_atMost linorder_neqE_nat not_le nth_Cons_0 subset_eq)
    with 1 show ?case by (subst nth_append) 
     (use eq in \<open>auto simp add: xs'_def I'_def Suc xs_def\<close>)
  next
    case (2 i)
    then have "i < n"
      by (metis Suc.prems atLeastLessThan_iff less_antisym subset_eq)
    with 2 show ?case by (subst nth_append) 
      (use eq in \<open>auto simp add: xs'_def I'_def Suc xs_def\<close>)
  qed
  moreover have 2: "(\<forall>i\<in>{0..<Suc n} - I. xs ! i = 0)"unfolding xs_def 
  proof (split if_split, safe, goal_cases)
    case (1 i)
    then have "i<n" by (metis atLeastLessThan_iff less_antisym)
    with 1 show ?case by (subst nth_append) (auto simp add: xs'_def I'_def Suc xs_def)
  next
    case (2 i)
    then show ?case by (subst nth_append) (auto simp add: xs'_def I'_def Suc xs_def)
  qed
  moreover have "length xs = Suc n" by (auto simp add: xs'_def I'_def Suc xs_def)
  ultimately have "(\<forall>i\<in>I. xs ! i = 1) \<and> (\<forall>i\<in>{0..<Suc n} - I. xs ! i = 0) \<and> length xs = Suc n" 
    by auto
  then show ?case by (subst exI, auto)
qed auto

lemma sum_list_even:
  assumes "a \<in> partition_problem"
  shows "sum_list a mod 2 = 0"
using assms unfolding partition_problem_def
proof (safe, goal_cases)
  case (1 I)
  then have "sum ((!) a) {0..<length a} = sum ((!) a) I + sum ((!) a) ({0..<length a} - I)"
    by (metis finite_atLeastLessThan sum.subset_diff)
  then have "sum ((!) a) {0..<length a} = 2 * sum ((!) a) I" using 1 by auto
  then show ?case by (simp add: sum_list_sum_nth)
qed

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem"
  shows "reduce_subset_sum_partition a \<in> subset_sum_list"
using assms unfolding partition_problem_def reduce_subset_sum_partition_def subset_sum_list_def Let_def
proof (safe, goal_cases)
  case (1 I)
  have sum_even: "sum_list a mod 2 = 0" using sum_list_even[OF assms] by auto
  then have if_rewrite: 
    "(if sum_list a mod 2 = 0 then sum_list a div 2 else (\<Sum>i<length a. \<bar>a!i\<bar>) + 1) = 
    sum_list a div 2" by auto
  have split_set: "{0..<length a} = I \<union> ({0..<length a}-I)"
    using 1(1) by (subst Un_Diff_cancel, auto)
  have disjoint: "I \<inter> ({0..<length a}-I) = {}" by auto
  have "\<exists>xs::int list. (\<forall>i\<in>I. xs ! i = 1) \<and> (\<forall>i\<in>{0..<length a}-I. xs ! i = 0) \<and> 
    length xs = length a" using ex_01_list[OF \<open>I \<subseteq> {0..<length a}\<close>] by auto
  then obtain xs::"int list" where 
    xs_prop: "\<forall>i\<in>I. xs ! i = 1"  
    "\<forall>i\<in>{0..<length a}-I. xs ! i = 0"  
    "length xs = length a" by blast
  then have eq: "(\<Sum>i<length a. a!i * xs!i) = (\<Sum>i\<in>I. a!i)" using split_set 1(1)
    by (metis (no_types, lifting) finite_lessThan lessThan_atLeast0 mult_cancel_left2 
      mult_cancel_right2 sum.cong sum.mono_neutral_right)
  have "sum_list a = (\<Sum>i\<in>I. a!i) + (\<Sum>i\<in>{0..<length a}-I. a!i)" using 1(1)
    by (smt (verit) finite_atLeastLessThan sum.subset_diff sum_list_sum_nth)
  also have "\<dots> = 2 * (\<Sum>i\<in>I. a!i)" using 1(2)[symmetric] by auto
  also have "\<dots> = 2 * (sum_list (map2 (*) a xs))" using eq xs_prop by (subst sum_list_map_2, auto)
  finally have "sum_list (map2 (*) a xs) = (sum_list a) div 2" by simp
  then show ?case using xs_prop sum_list_map_2 \<open>2 * sum ((!) a) I = 2 * sum_list (map2 (*) a xs)\<close> eq
    by (subst exI[of _ xs], auto simp add: if_rewrite)
qed




text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_subset_sum:
  assumes "reduce_subset_sum_partition a \<in> subset_sum_list"
  shows "a \<in> partition_problem"
using assms unfolding partition_problem_def reduce_subset_sum_partition_def subset_sum_list_def Let_def
proof (safe, goal_cases)
  case (1 xs)
  have "(sum_list a) mod 2 = 0" using 1
  proof -
    have "(\<Sum>i<length a. a ! i * xs ! i) \<le> (\<Sum>i<length a. \<bar>a!i\<bar>)" using 1 by (subst sum_mono, auto)
    then have "(\<Sum>i<length a. a ! i * xs ! i) \<noteq> (\<Sum>i<length a. \<bar>a!i\<bar>) + 1" by auto
    then show ?thesis using 1 by presburger
  qed
  obtain I where I_prop: "I = {i. i< length xs \<and> xs!i = 1}" by blast
  then have split_set: "{0..<length a} = I \<union> ({0..<length a}-I)"
    using I_prop 1 by (subst Un_Diff_cancel, auto)
  have "I\<subseteq>{0..<length a}" using I_prop 1 by auto
  moreover have "sum ((!) a) I = sum ((!) a) ({0..<length a} - I)"
  proof - 
    have eq: "(\<Sum>i\<in>I. a!i) = (\<Sum>i<length a. a!i * xs!i)" using split_set  I_prop 1 
      by (smt (verit, ccfv_threshold) Diff_iff \<open>I \<subseteq> {0..<length a}\<close> atLeast0LessThan 
      atLeastLessThan_iff empty_iff finite_atLeastLessThan insert_iff mem_Collect_eq 
      mult_cancel_left2 mult_cancel_right2 sum.cong sum.mono_neutral_right)
    have "(\<Sum>i\<in>{0..<length a}-I. a!i) = sum ((!) a) {0..<length a} - (\<Sum>i\<in>I. a!i)" using split_set 
      by (meson \<open>I \<subseteq> {0..<length a}\<close> finite_atLeastLessThan sum_diff)
    also have "\<dots> = sum_list a - sum_list a div 2"
    by (metis "1"(2) \<open>sum_list a mod 2 = 0\<close> eq sum_list_sum_nth)
    also have "\<dots> = sum_list a div 2" using \<open>(sum_list a) mod 2 = 0\<close> by auto
    finally have "(\<Sum>i\<in>{0..<length a}-I. a!i) = (\<Sum>i\<in>I. a!i)"
      using "1"(2) \<open>sum_list a mod 2 = 0\<close> eq by presburger
    then show ?thesis by auto
  qed    
  ultimately show ?case by (subst exI, auto)
qed



text \<open>The Subset Sum on lists is NP-hard.\<close>
lemma "is_reduction reduce_subset_sum_partition partition_problem subset_sum_list"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 a)
  then show ?case using well_defined_reduction_subset_sum by auto
next
  case (2 a)
  then show ?case using NP_hardness_reduction_subset_sum by auto
qed


text \<open>Subset Sum on vectors is the same as on lists\<close>

lemma subset_sum_vec_list:
"(as,s) \<in> subset_sum \<longleftrightarrow> (list_of_vec as,s) \<in> subset_sum_list"
proof (safe, goal_cases)
  case 1
  then have "\<exists>xs. (\<forall>i<dim_vec xs. xs $ i \<in> {0, 1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as" 
    unfolding subset_sum_def by auto
  then have " \<exists>xs. (\<forall>i<length xs. xs ! i \<in> {0, 1}) \<and>
             (\<Sum>i<length (list_of_vec as). (list_of_vec as) ! i * xs ! i) = s \<and> 
              length xs = length (list_of_vec as)"
  unfolding scalar_prod_def
  by (metis (no_types, lifting) atLeast0LessThan length_list_of_vec mult.commute 
    sum.cong vec_list vec_of_list_index)
  then show ?case unfolding subset_sum_list_def by auto
next
  case 2
  then have " \<exists>xs. (\<forall>i<length xs. xs ! i \<in> {0, 1}) \<and>
             (\<Sum>i<length (list_of_vec as). (list_of_vec as) ! i * xs ! i) = s \<and> 
              length xs = length (list_of_vec as)"
  unfolding subset_sum_list_def by auto
  then have "\<exists>xs. (\<forall>i<dim_vec xs. xs $ i \<in> {0, 1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as" 
  unfolding scalar_prod_def
  by (metis (no_types, lifting) dim_vec_of_list lessThan_atLeast0 mult.commute 
    sum.ivl_cong vec_list vec_of_list_index)
  then show ?case unfolding subset_sum_def by auto
qed

end