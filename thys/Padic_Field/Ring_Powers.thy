theory Ring_Powers
  imports "HOL-Algebra.Chinese_Remainder" "HOL-Combinatorics.List_Permutation"
          Padic_Ints.Function_Ring "HOL-Algebra.Generated_Rings" Cring_Multivariable_Poly Indices
begin

type_synonym arity = nat
type_synonym 'a tuple = "'a list"

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Cartesian Powers of a Ring\<close>
(**************************************************************************************************)
(**************************************************************************************************)

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Constructing the Cartesian Power of a Ring\<close>
  (**********************************************************************)
  (**********************************************************************)
text\<open>Powers of a ring\<close>

text\<open>\texttt{R\_list n R} produces the list $[R, ... , R]$ of length n\<close>

fun R_list :: "nat \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> (('a, 'b) ring_scheme ) list" where
"R_list n R = map (\<lambda>_. R) (index_list n)"

text\<open>Cartesian powers of a ring\<close>

definition cartesian_power :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a list) ring" ("_\<^bsup>_\<^esup>" 80) where
"R\<^bsup>n\<^esup> \<equiv> RDirProd_list (R_list n R)"

lemma R_list_length: 
"length (R_list n R) = n"
  apply(induction n) by auto 

lemma R_list_nth:
"i < n \<Longrightarrow> R_list n R ! i = R"
  by (simp add: index_list_length)

lemma cartesian_power_car_memI:
  assumes "length as = n" 
  assumes "set as \<subseteq> carrier R" 
  shows "as \<in> carrier (R\<^bsup>n\<^esup>)"
  unfolding cartesian_power_def 
  apply(rule RDirProd_list_carrier_memI)
    using R_list_length assms(1) apply auto[1]
      by (metis R_list_length R_list_nth assms(1) assms(2) nth_mem subsetD)

lemma cartesian_power_car_memI':
  assumes "length as = n"
  assumes "\<And>i. i < n \<Longrightarrow>  as ! i \<in> carrier R"
  shows "as \<in> carrier (R\<^bsup>n\<^esup>)"
  unfolding cartesian_power_def 
  apply(rule RDirProd_list_carrier_memI)
    using R_list_length assms(1) apply auto[1]
      by (metis R_list_length R_list_nth assms(2))  

lemma cartesian_power_car_memE:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "length as = n"
  using RDirProd_list_carrier_mem(1) 
  by (metis R_list_length assms cartesian_power_def)
 
lemma cartesian_power_car_memE':
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "i < n"
  shows " as ! i \<in> carrier R"
  using assms  RDirProd_list_carrier_mem(2) 
  by (metis (no_types, lifting) R_list_length R_list_nth cartesian_power_def)
  
lemma cartesian_power_car_memE'':
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "set as \<subseteq> carrier R"
  using cartesian_power_car_memE' 
  by (metis assms cartesian_power_car_memE in_set_conv_nth subsetI)
  
lemma cartesian_power_car_memI'':
  assumes "length as = n + k"
  assumes "take n as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "drop n as \<in> carrier (R\<^bsup>k\<^esup>)"
  shows "as \<in> carrier (R\<^bsup>n+k\<^esup>)"
  apply(rule cartesian_power_car_memI')
  apply (simp add: assms(1))
proof- fix i assume A: "i < n + k"
  show " as ! i \<in> carrier R"
    apply(cases "i < n")
     apply (metis assms(2) cartesian_power_car_memE' nth_take)
    by (metis A add_diff_inverse_nat add_less_imp_less_left 
        append_take_drop_id assms(2) assms(3) cartesian_power_car_memE 
        cartesian_power_car_memE' nth_append_length_plus)
qed

lemma cartesian_power_cons:
  assumes " as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "a \<in> carrier R"
  shows "a#as \<in> carrier (R\<^bsup>n+1\<^esup>)"
  apply(rule cartesian_power_car_memI)
  apply (metis One_nat_def assms(1) cartesian_power_car_memE list.size(4))
  by (metis assms(1) assms(2) cartesian_power_car_memE cartesian_power_car_memE' in_set_conv_nth set_ConsD subsetI)

lemma cartesian_power_append:
  assumes " as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "a \<in> carrier R"
  shows "as@[a] \<in> carrier (R\<^bsup>n+1\<^esup>)"
  apply(rule cartesian_power_car_memI'')
   apply (metis add.commute assms(1) cartesian_power_car_memE length_append_singleton plus_1_eq_Suc)
  apply (metis append_eq_append_conv_if assms(1) butlast_snoc cartesian_power_car_memE length_append_singleton lessI take_butlast)
  by (metis add.commute add.right_neutral append_eq_conv_conj assms(1) assms(2) bot_least
      cartesian_power_car_memE cartesian_power_car_memI cartesian_power_cons 
      list.set(1) list.size(3))

lemma cartesian_power_head:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "hd as \<in> carrier R"
  by (metis assms cartesian_power_car_memE cartesian_power_car_memE''  list.set_sel(1) list.size(3) old.nat.distinct(1) subsetD)

lemma cartesian_power_tail:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "tl as \<in> carrier (R\<^bsup>n\<^esup>)"
  apply(rule cartesian_power_car_memI)
  apply (metis add_diff_cancel_left' assms cartesian_power_car_memE length_tl plus_1_eq_Suc)
  by (metis assms cartesian_power_car_memE cartesian_power_car_memE'' list.set_sel(2) list.size(3) nat.simps(3) subsetD subsetI)

lemma insert_at_index_closed:
  assumes "length as = n"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "a \<in> carrier R"
  assumes "k \<le> n"
  shows "(insert_at_index as a k) \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  apply(rule cartesian_power_car_memI')
   apply (metis Groups.add_ac(2) assms(1) insert_at_index_length plus_1_eq_Suc)
  by (smt R_list_length Suc_le_eq assms(1) assms(2) assms(3) assms(4) 
      cartesian_power_car_memE' insert_at_index_eq insert_at_index_eq' 
      insert_at_index_eq'' less_Suc_eq less_Suc_eq_0_disj not_less_eq_eq)

lemma insert_at_index_pow_not_car:
  assumes "k \<le>n"
  assumes "length x = n"
  assumes "(insert_at_index x a k) \<in> carrier (R\<^bsup>Suc n\<^esup>)" 
  shows "x \<in> carrier (R\<^bsup>n\<^esup>)"
  apply(rule cartesian_power_car_memI')
  apply (simp add: assms(2))
  by (metis Suc_mono assms(1) assms(2) assms(3) 
      cartesian_power_car_memE' insert_at_index_eq' 
      insert_at_index_eq'' leI less_SucI)

lemma insert_at_index_pow_not_car':
  assumes "k \<le>n"
  assumes "length x = n"
  assumes "x \<notin> carrier (R\<^bsup>n\<^esup>)"
  shows "(insert_at_index x a n) \<notin> carrier (R\<^bsup>Suc n\<^esup>)"
  by (metis assms(2) assms(3) insert_at_index_pow_not_car lessI less_Suc_eq_le)

lemma take_closed:
  assumes "k \<le>n"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "take k x \<in> carrier (R\<^bsup>k\<^esup>)"
  apply(rule cartesian_power_car_memI)
  apply (metis assms(1) assms(2) cartesian_power_car_memE length_take min.absorb_iff2)
  by (meson assms(2) cartesian_power_car_memE'' set_take_subset subset_trans)

lemma drop_closed:
  assumes "k < n"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "drop k x \<in> carrier (R\<^bsup>n - k\<^esup>)"
  apply(rule   cartesian_power_car_memI[of "drop k x" "n - k"] )
  using assms(2) cartesian_power_car_memE length_drop apply blast
   by (metis add_diff_inverse_nat assms(1) assms(2) cartesian_power_car_memE 
      cartesian_power_car_memE' in_set_conv_nth length_drop less_imp_le_nat
      nat_add_left_cancel_less nth_drop order.asym subsetI)

lemma last_closed: 
  assumes "n > 0"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "last x \<in> carrier R"
  using assms 
  by (metis Suc_diff_1 cartesian_power_car_memE cartesian_power_car_memE'
      last_conv_nth lessI list.size(3) neq0_conv)

lemma cartesian_power_concat:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "b \<in> carrier (R\<^bsup>k\<^esup>)"
  shows "a@b \<in> carrier (R\<^bsup>n+k\<^esup>)"
        "b@a \<in> carrier (R\<^bsup>n+k\<^esup>)"
  apply (metis (no_types, lifting) append_eq_conv_conj assms(1) assms(2) 
    cartesian_power_car_memE cartesian_power_car_memI'' length_append)
  by (metis (no_types, lifting) add.commute append_eq_conv_conj assms(1) assms(2) 
      cartesian_power_car_memE cartesian_power_car_memI'' length_append)

lemma cartesian_power_decomp:
  assumes "a \<in> carrier (R\<^bsup>n+k\<^esup>)"
  obtains a0 a1 where "a0 \<in> carrier (R\<^bsup>n\<^esup>) \<and> a1 \<in> carrier (R\<^bsup>k\<^esup>) \<and> a0@a1 = a"
  using assms 
  by (metis (no_types, lifting) add_diff_cancel_left' append.assoc append_eq_append_conv 
      append_take_drop_id cartesian_power_car_memE drop_closed le_add1 
      le_neq_implies_less length_append take_closed)

lemma list_segment_pow:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "j \<le> n"
  assumes "i \<le>  j"
  shows "list_segment i j as \<in> carrier (R\<^bsup>j - i\<^esup>)"
  apply(rule cartesian_power_car_memI)
  using list_segment_length assms cartesian_power_car_memE 
   apply blast
  using assms 
  by (metis cartesian_power_car_memE cartesian_power_car_memE''
      dual_order.trans list_segment_subset_list_set)

lemma nth_list_segment:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "j \<le>n"
  assumes "i \<le>  j"
  assumes "k < j - i"
  shows "(list_segment i j as) ! k = as ! (i + k)" 
  unfolding list_segment_def
  using assms nth_map_upt[of k j i "((!) as)"   ] 
  by blast

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Mapping the Carrier of a Ring to its 1-Dimensional Cartesian Power.\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context cring
begin

lemma R1_carI:
  assumes "length as = 1"
  assumes "as!0 \<in> carrier R"
  shows "as \<in> carrier (R\<^bsup>1\<^esup>)"
  apply(rule cartesian_power_car_memI)
  using assms 
   apply blast
     using assms 
    by (metis in_set_conv_nth less_one subsetI)
  
abbreviation(input) to_R1 where
"to_R1 a \<equiv> [a]"

abbreviation(input) to_R :: "'a list \<Rightarrow> 'a"  where
"to_R as \<equiv> as!0"

lemma to_R1_to_R:
  assumes "a \<in> carrier (R\<^bsup>1\<^esup>)"
  shows "to_R1 (to_R a) = a"
proof-
  have "length a = 1"
    using assms cartesian_power_car_memE by blast
  then obtain b where "a = [b]"
    by (metis One_nat_def length_0_conv length_Suc_conv)
  then show ?thesis 
    using assms
    by (metis nth_Cons_0)
qed

lemma to_R_to_R1:
  shows "to_R (to_R1 a) = a"
  by (meson nth_Cons_0)

lemma to_R1_closed:
  assumes "a \<in> carrier R"
  shows "to_R1 a \<in> carrier (R\<^bsup>1\<^esup>)"
proof(rule R1_carI)
  show "length [a] = 1"
    by simp 
  show "[a] ! 0 \<in> carrier R"
    using assms to_R_to_R1 by presburger    
qed
    
lemma to_R_pow_closed:
  assumes "a \<in> carrier (R\<^bsup>1\<^esup>)"
  shows "to_R a \<in> carrier R"
  using assms cartesian_power_car_memE' by blast

lemma to_R1_intersection:
  assumes "A \<subseteq> carrier R"
  assumes "B \<subseteq> carrier R"
  shows "to_R1 ` (A \<inter> B) = to_R1` A \<inter> to_R1 ` B"
proof
  show "(\<lambda>a. [a]) ` (A \<inter> B) \<subseteq> (\<lambda>a. [a]) ` A \<inter> (\<lambda>a. [a]) ` B"
    by blast
  show "(\<lambda>a. [a]) ` A \<inter> (\<lambda>a. [a]) ` B \<subseteq> (\<lambda>a. [a]) ` (A \<inter> B)"
    using assms 
  by blast
qed

lemma to_R1_finite:
  assumes "finite A"
  shows "finite (to_R1` A)"
        "card A = card (to_R1` A)"
  using assms 
  apply blast
  apply(rule finite.induct[of A])
  apply (simp add: assms(1))
   apply simp
  by (smt card_insert_if finite_imageI image_iff image_insert list.inject)

lemma to_R1_carrier:
"to_R1` (carrier R)= carrier (R\<^bsup>1\<^esup>)"
proof
  show "(\<lambda>a. [a]) ` carrier R \<subseteq> carrier (R\<^bsup>1\<^esup>)"
  proof fix x
    assume "x \<in> (\<lambda>a. [a]) ` carrier R"
    then show "x \<in> carrier (R\<^bsup>1\<^esup>)"
      using cartesian_power_car_memI[of x 1 R] 
      by (metis (no_types, lifting) image_iff to_R1_closed)
  qed
  show "carrier (R\<^bsup>1\<^esup>) \<subseteq> (\<lambda>a. [a]) ` carrier R"
  proof fix x
    assume "x \<in> carrier (R\<^bsup>1\<^esup>)"
    then obtain a where a_def: "a \<in> carrier R \<and> x = [a]"
      using cartesian_power_car_memE'[of x R 1] cartesian_power_car_memE[of x R 1]
      by (metis less_numeral_extra(1) to_R1_to_R)
    then show "x \<in> (\<lambda>a. [a]) ` carrier R"
      by blast
  qed
qed

lemma to_R1_diff:
"to_R1` (A - B) = to_R1` A - to_R1` B"
proof
  show "(\<lambda>a. [a]) ` (A - B) \<subseteq> (\<lambda>a. [a]) ` A - (\<lambda>a. [a]) ` B"
    by blast
  show "(\<lambda>a. [a]) ` A - (\<lambda>a. [a]) ` B \<subseteq> (\<lambda>a. [a]) ` (A - B)"
    by blast
qed

lemma to_R1_complement:
  shows "to_R1` (carrier R - A) = carrier (R\<^bsup>1\<^esup>) - to_R1` A"
  by (metis to_R1_carrier to_R1_diff)

lemma to_R1_subset:
  assumes "A \<subseteq> B"
  shows "to_R1` A \<subseteq> to_R1` B"
  using assms 
  by blast

lemma to_R1_car_subset:
  assumes "A \<subseteq> carrier R"
  shows "to_R1` A \<subseteq> carrier (R\<^bsup>1\<^esup>)"
  using assms to_R1_carrier 
  by blast
end 

      (**********************************************************************)
      (**********************************************************************)
      subsection\<open>Simple Cartesian Products\<close>
      (**********************************************************************)
      (**********************************************************************)
definition cartesian_product :: "('a list) set \<Rightarrow> ('a list) set \<Rightarrow> ('a list) set" where
"cartesian_product A B \<equiv> {xs. \<exists>as \<in> A. \<exists>bs \<in> B. xs = as@bs}"

lemma cartesian_product_closed:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  shows "cartesian_product A B \<subseteq> carrier (R\<^bsup>n + m\<^esup>)"
proof
  fix x 
  assume A: "x \<in> cartesian_product A B "
  then obtain as bs where as_bs_def: "x = as@bs \<and> as \<in> A \<and> bs \<in> B"
    unfolding cartesian_product_def by blast
  show "x \<in> carrier (R\<^bsup>n + m\<^esup>) "
    apply(rule cartesian_power_car_memI')
     apply (metis as_bs_def assms cartesian_power_car_memE length_append subsetD)
    using A unfolding cartesian_product_def 
    by (metis (no_types, lifting) add_diff_inverse_nat as_bs_def assms(1)
        assms(2) cartesian_power_car_memE cartesian_power_car_memE' 
        nat_add_left_cancel_less nth_append subsetD)   
qed

lemma cartesian_product_closed':
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "b \<in>  carrier (R\<^bsup>m\<^esup>)"
  shows "(a@b) \<in>  carrier (R\<^bsup>n + m\<^esup>)"
proof-
  have "a@b \<in> cartesian_product {a} {b}"
    using cartesian_product_def by blast
  then show ?thesis 
  using cartesian_product_closed[of "{a}" R n "{b}" m]
        assms 
  by blast
qed      

lemma cartesian_product_carrier: 
"cartesian_product (carrier (R\<^bsup>n\<^esup>)) (carrier (R\<^bsup>m\<^esup>)) =  carrier (R\<^bsup>n + m\<^esup>)"
proof
  show "cartesian_product (carrier (R\<^bsup>n\<^esup>)) (carrier (R\<^bsup>m\<^esup>)) \<subseteq> carrier (R\<^bsup>n + m\<^esup>)"
    using cartesian_product_closed[of "(carrier (R\<^bsup>n\<^esup>))" R n "(carrier (R\<^bsup>m\<^esup>)) " m] 
    by blast
  show "carrier (R\<^bsup>n + m\<^esup>) \<subseteq> cartesian_product (carrier (R\<^bsup>n\<^esup>)) (carrier (R\<^bsup>m\<^esup>))"
  proof
    fix x
    assume A: "x \<in> carrier (R\<^bsup>n + m\<^esup>)"
    have 0: "take n x \<in> carrier (R\<^bsup>n\<^esup>)"
      apply(rule cartesian_power_car_memI')  
       apply (metis A cartesian_power_car_memE le_add1 length_take min.absorb2)
         by (metis A add.commute cartesian_power_car_memE' 
            nth_take trans_less_add2) 
    have 1: "drop n x \<in> carrier (R\<^bsup>m\<^esup>)"
      apply(rule cartesian_power_car_memI')  
        apply (metis A add_diff_cancel_left' cartesian_power_car_memE length_drop)
          by (metis A cartesian_power_car_memE cartesian_power_car_memE' le_add1 nat_add_left_cancel_less nth_drop)
    show "x \<in> cartesian_product (carrier (R\<^bsup>n\<^esup>)) (carrier (R\<^bsup>m\<^esup>))"
      using 0 1 
      by (smt A cartesian_power_decomp cartesian_product_def mem_Collect_eq)
qed


text\<open>Higher function rings\<close>
qed

lemma cartesian_product_memI:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "take n a \<in> A"
  assumes "drop n a \<in> B"
  shows "a \<in> cartesian_product A B"
proof-
  have "a = (take n a) @ (drop n a)"
    by (metis append_take_drop_id)
  then show ?thesis 
    using assms(3) assms(4) cartesian_product_def by blast    
qed

lemma cartesian_product_memI':
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "a \<in> A"
  assumes "b \<in> B"
  shows "a@b \<in> cartesian_product A B"
  using assms unfolding cartesian_product_def
  by blast   

lemma cartesian_product_memE: 
assumes "a \<in> cartesian_product A B"
assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
shows "take n a \<in> A"
      "drop n a \<in> B"
  using assms unfolding cartesian_product_def  
  apply (smt append_eq_conv_conj cartesian_power_car_memE in_mono mem_Collect_eq)
  using assms unfolding cartesian_product_def  
  by (smt append_eq_conv_conj cartesian_power_car_memE in_mono mem_Collect_eq)

lemma cartesian_product_intersection:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "C \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "D \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  shows "cartesian_product A B \<inter> cartesian_product C D = cartesian_product (A \<inter> C) (B \<inter> D)"
proof
  show "cartesian_product A B \<inter> cartesian_product C D \<subseteq> cartesian_product (A \<inter> C) (B \<inter> D)"
  proof fix x
    assume "x \<in> cartesian_product A B \<inter> cartesian_product C D"
    then show "x \<in> cartesian_product (A \<inter> C) (B \<inter> D)"
      using assms cartesian_product_memE[of x C D] cartesian_product_memE[of x A B] 
            cartesian_product_memI[of "A \<inter> C" R n "B \<inter> D" m x] 
      by (smt Int_iff inf.coboundedI1)
  qed
  show "cartesian_product (A \<inter> C) (B \<inter> D) \<subseteq> cartesian_product A B \<inter> cartesian_product C D"
  proof fix x
    assume "x \<in> cartesian_product (A \<inter> C) (B \<inter> D)"
    then show "x \<in> cartesian_product A B \<inter> cartesian_product C D"
          using assms cartesian_product_memI[of C R n D m] cartesian_product_memI[of A R n B m]
            cartesian_product_memE[of x "A \<inter> B" "C \<inter> D" R n ] 
          by (metis (no_types, lifting) Int_iff cartesian_product_memE(1) cartesian_product_memE(2) inf_le1 subset_trans)          
  qed
qed         

lemma cartesian_product_subsetI:
  assumes "C \<subseteq> A"
  assumes "D \<subseteq> B"
  shows "cartesian_product C D \<subseteq> cartesian_product A B"
  using assms unfolding cartesian_product_def
  by blast

lemma cartesian_product_binary_union_right:
  assumes "C \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "D \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "cartesian_product A (C \<union> D) = (cartesian_product A C) \<union> (cartesian_product A D)"
proof
  show "cartesian_product A (C \<union> D) \<subseteq> cartesian_product A C \<union> cartesian_product A D"
    unfolding cartesian_product_def  by blast
  show "cartesian_product A C \<union> cartesian_product A D \<subseteq> cartesian_product A (C \<union> D)"
    unfolding cartesian_product_def by blast
qed

lemma cartesian_product_binary_union_left:
  assumes "C \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "D \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "cartesian_product (C \<union> D) A = (cartesian_product C A) \<union> (cartesian_product D A)"
proof
  show "cartesian_product (C \<union> D) A \<subseteq> cartesian_product C A \<union> cartesian_product D A"
    unfolding cartesian_product_def by blast
  show "cartesian_product C A \<union> cartesian_product D A \<subseteq> cartesian_product (C \<union> D) A"
    unfolding cartesian_product_def by blast 
qed

lemma cartesian_product_binary_intersection_right:
  assumes "C \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "D \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  shows "cartesian_product A (C \<inter> D) = (cartesian_product A C) \<inter> (cartesian_product A D)"
proof
  show "cartesian_product A (C \<inter> D) \<subseteq> cartesian_product A C \<inter> cartesian_product A D"
    unfolding cartesian_product_def by blast
  show "cartesian_product A C \<inter> cartesian_product A D \<subseteq> cartesian_product A (C \<inter> D)"
  proof fix x assume A: "x \<in> cartesian_product A C \<inter> cartesian_product A D"
    show "x \<in> cartesian_product A (C \<inter> D)" apply(rule cartesian_product_memI[of A R m _ n  ])
    apply (simp add: assms(3)) 
      apply (simp add: assms(1) inf.coboundedI1)
       apply (meson A IntD1 assms(3) cartesian_product_memE(1))
        by (meson A Int_iff assms(3) cartesian_product_memE(2))
  qed
qed

lemma cartesian_product_binary_intersection_left:
  assumes "C \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "D \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  shows "cartesian_product (C \<inter> D) A = (cartesian_product C A) \<inter> (cartesian_product D A)"
proof
  show "cartesian_product (C \<inter> D) A \<subseteq> cartesian_product C A \<inter> cartesian_product D A"
    unfolding cartesian_product_def by blast
  show "cartesian_product C A \<inter> cartesian_product D A \<subseteq> cartesian_product (C \<inter> D) A"
    proof fix x assume A: "x \<in> cartesian_product C A \<inter> cartesian_product D A"
    show "x \<in> cartesian_product (C \<inter> D) A" apply(rule cartesian_product_memI[of _ R n _ m ])
       apply (simp add: assms(2) inf.coboundedI2)
        apply (simp add: assms(3))
          apply (meson A Int_iff assms(1) assms(2) cartesian_product_memE(1))
            by (meson A IntD1 assms(1) cartesian_product_memE(2))
  qed
qed

lemma cartesian_product_car_complement_right:
  assumes "A \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  shows "carrier (R\<^bsup>n + m\<^esup>) - cartesian_product (carrier (R\<^bsup>n\<^esup>)) A = 
          cartesian_product (carrier (R\<^bsup>n\<^esup>)) ((carrier (R\<^bsup>m\<^esup>)) - A)"
proof
  show "carrier (R\<^bsup>n + m\<^esup>) - cartesian_product (carrier (R\<^bsup>n\<^esup>)) A \<subseteq> cartesian_product (carrier (R\<^bsup>n\<^esup>)) ((carrier (R\<^bsup>m\<^esup>)) - A)"
  proof fix x assume A: "x \<in> (carrier (R\<^bsup>n + m\<^esup>) - cartesian_product (carrier (R\<^bsup>n\<^esup>)) A)"
  show "x \<in> cartesian_product (carrier (R\<^bsup>n\<^esup>)) ((carrier (R\<^bsup>m\<^esup>)) - A)"
  apply(rule cartesian_product_memI[of  _  R n _ m]) 
    apply simp 
      apply simp
        apply (meson A DiffE le_add1 take_closed)
    apply(rule ccontr) 
    proof-
      assume A': "drop n x \<notin> (carrier (R\<^bsup>m\<^esup>) - A)"
      have "drop n x \<in> A"
      proof-
      have "x \<in> cartesian_product (carrier (R\<^bsup>n\<^esup>)) (carrier (R\<^bsup>m\<^esup>))"
        using A 
        by (metis (mono_tags, lifting) DiffD1 cartesian_product_carrier)
      then show ?thesis 
        using A' cartesian_product_memE[of x "(carrier (R\<^bsup>n\<^esup>))" "(carrier (R\<^bsup>m\<^esup>))" R n] 
        by blast
      qed
      then show False 
        using A cartesian_product_memI[of "(carrier (R\<^bsup>n\<^esup>))" R n A m x] 
        by (meson DiffD1 DiffD2 assms le_add1 order_refl take_closed)
    qed
  qed
  show "cartesian_product (carrier (R\<^bsup>n\<^esup>)) ((carrier (R\<^bsup>m\<^esup>)) - A) \<subseteq> carrier (R\<^bsup>n + m\<^esup>) - cartesian_product (carrier (R\<^bsup>n\<^esup>)) A"
  proof fix x assume A: "x \<in> cartesian_product (carrier (R\<^bsup>n\<^esup>)) ((carrier (R\<^bsup>m\<^esup>)) - A)"
    show "x \<in> carrier (R\<^bsup>n + m\<^esup>) - cartesian_product (carrier (R\<^bsup>n\<^esup>)) A"
      apply(rule ccontr)
      using A cartesian_product_memE[of x "carrier (R\<^bsup>n\<^esup>)" A R n]
      using A cartesian_product_memE[of x "(carrier (R\<^bsup>n\<^esup>))" "(carrier (R\<^bsup>m\<^esup>)) - A" R n] 
      by (metis (no_types, lifting) DiffD1 DiffD2 DiffI 
          append_take_drop_id cartesian_product_closed' order_refl)
  qed
qed

lemma cartesian_product_car_complement_left:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "carrier (R\<^bsup>n + m\<^esup>) - cartesian_product  A (carrier (R\<^bsup>m\<^esup>)) = 
          cartesian_product ((carrier (R\<^bsup>n\<^esup>)) - A) (carrier (R\<^bsup>m\<^esup>)) "
proof
  show "carrier (R\<^bsup>n + m\<^esup>) - cartesian_product  A (carrier (R\<^bsup>m\<^esup>)) \<subseteq>
          cartesian_product ((carrier (R\<^bsup>n\<^esup>)) - A) (carrier (R\<^bsup>m\<^esup>)) "
  proof fix x assume A: " x \<in> carrier (R\<^bsup>n + m\<^esup>) - cartesian_product  A (carrier (R\<^bsup>m\<^esup>))"
    show "x \<in> cartesian_product ((carrier (R\<^bsup>n\<^esup>)) - A) (carrier (R\<^bsup>m\<^esup>)) "
    proof(rule cartesian_product_memI[of _ R n _ m]) 
      show "carrier (R\<^bsup>n\<^esup>) - A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
        by simp
      show "carrier (R\<^bsup>m\<^esup>) \<subseteq> carrier (R\<^bsup>m\<^esup>)"
        by simp
      show "take n x \<in> carrier (R\<^bsup>n\<^esup>) - A"
        by (metis (no_types, lifting) A DiffD1 DiffD2 DiffI assms 
            cartesian_product_carrier cartesian_product_memE(2) cartesian_product_memI 
            le_add1 order_refl take_closed)
      show "drop n x \<in> carrier (R\<^bsup>m\<^esup>)"
        by (metis A DiffD1 cartesian_product_carrier cartesian_product_memE(2) order_refl)
    qed
  qed
  show "cartesian_product ((carrier (R\<^bsup>n\<^esup>)) - A) (carrier (R\<^bsup>m\<^esup>)) \<subseteq>
        carrier (R\<^bsup>n + m\<^esup>) - cartesian_product  A (carrier (R\<^bsup>m\<^esup>)) "
  proof fix x assume A: " x \<in> cartesian_product ((carrier (R\<^bsup>n\<^esup>)) - A) (carrier (R\<^bsup>m\<^esup>))"
    show "x \<in> carrier (R\<^bsup>n + m\<^esup>) - cartesian_product  A (carrier (R\<^bsup>m\<^esup>))"
    apply(rule ccontr)
      using A cartesian_product_memE[of x "((carrier (R\<^bsup>n\<^esup>)) - A)" "(carrier (R\<^bsup>m\<^esup>))"]
              cartesian_product_memE[of x A "(carrier (R\<^bsup>m\<^esup>))"]
      by (smt DiffD1 DiffD2 DiffI Diff_subset append_take_drop_id assms cartesian_product_closed')
  qed
qed

lemma cartesian_product_complement_right:
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "cartesian_product A (carrier (R\<^bsup>m\<^esup>)) - (cartesian_product A B) = 
          cartesian_product A ((carrier (R\<^bsup>m\<^esup>)) - B)"
proof
  show "cartesian_product A (carrier (R\<^bsup>m\<^esup>)) - cartesian_product A B \<subseteq> cartesian_product A ((carrier (R\<^bsup>m\<^esup>)) - B)"
    unfolding cartesian_product_def by blast
  show "cartesian_product A ((carrier (R\<^bsup>m\<^esup>)) - B) \<subseteq> cartesian_product A ((carrier (R\<^bsup>m\<^esup>))) - cartesian_product A B"
  proof fix x assume A: "x \<in> cartesian_product A ((carrier (R\<^bsup>m\<^esup>)) - B)"
    have 0: "x \<in> cartesian_product A (carrier (R\<^bsup>m\<^esup>))" 
      using A unfolding cartesian_product_def by blast
    show "x \<in> cartesian_product A (carrier (R\<^bsup>m\<^esup>)) - cartesian_product A B "
      apply(rule ccontr) 
      using assms 0 A cartesian_product_memE[of x A "((carrier (R\<^bsup>m\<^esup>)) - B)" R n] 
                      cartesian_product_memE[of x A B R n] 
      by blast
  qed
qed

lemma cartesian_product_complement_left:
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "cartesian_product (carrier (R\<^bsup>m\<^esup>)) A  - (cartesian_product B A) = 
          cartesian_product ((carrier (R\<^bsup>m\<^esup>)) - B) A "
proof
  show "cartesian_product (carrier (R\<^bsup>m\<^esup>)) A - cartesian_product B A \<subseteq> cartesian_product ((carrier (R\<^bsup>m\<^esup>)) - B) A"
    unfolding cartesian_product_def by blast
  show "cartesian_product ((carrier (R\<^bsup>m\<^esup>)) - B) A \<subseteq> cartesian_product (carrier (R\<^bsup>m\<^esup>)) A - cartesian_product B A"
  proof fix x assume A: "x \<in> cartesian_product ((carrier (R\<^bsup>m\<^esup>)) - B) A"
    have 0: "x \<in> cartesian_product (carrier (R\<^bsup>m\<^esup>)) A"
      using A  unfolding cartesian_product_def by blast
    have 1: "take m x \<in> (carrier (R\<^bsup>m\<^esup>)) - B"
      using A cartesian_product_memE[of x "((carrier (R\<^bsup>m\<^esup>)) - B)" A R m]
      by blast
    have 2: "drop m x \<in> A"
      using cartesian_product_memE[of x "((carrier (R\<^bsup>m\<^esup>)) - B)" A R m]
      by (metis  A  Diff_subset)
    show "x \<in> cartesian_product (carrier (R\<^bsup>m\<^esup>)) A - cartesian_product B A"
      apply(rule ccontr) 
      using A 0 1 2 cartesian_product_memE[of x B A R m] assms  
      by blast
  qed
qed

lemma cartesian_product_empty_right:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B = {[]}"
  shows "cartesian_product A B = A"
proof
  show "cartesian_product A B \<subseteq> A"
    using assms unfolding cartesian_product_def
    by (smt append_Nil2 mem_Collect_eq singletonD subsetI)
  show "A \<subseteq> cartesian_product A B"
    using assms unfolding cartesian_product_def 
    by blast
qed

lemma cartesian_product_empty_left:
  assumes "B \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "A = {[]}"
  shows "cartesian_product A B = B"
proof
  show "cartesian_product A B \<subseteq> B"
    using assms unfolding cartesian_product_def
    by (smt append.simps(1) mem_Collect_eq singletonD subsetI)
  show "B \<subseteq> cartesian_product A B"
    using assms unfolding cartesian_product_def
    by blast
qed

      (**********************************************************************)
      (**********************************************************************)
      subsection\<open>Cartesian Products at Arbitrary Indices\<close>
      (**********************************************************************)
      (**********************************************************************)

definition(in ring) ring_pow_proj ::  "nat  \<Rightarrow> (nat set) \<Rightarrow>  ('a list)  \<Rightarrow> ('a list) " ("\<pi>\<^bsub>_, _\<^esub>")  where
"ring_pow_proj n S \<equiv> restrict (project_at_indices S) (carrier (R\<^bsup>n\<^esup>))"

text\<open>The projection at an arbitrary index set\<close>

lemma project_at_indices_closed:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "S \<subseteq> indices_of a"
  shows "\<pi>\<^bsub>S\<^esub> a \<in> carrier (R\<^bsup>card S\<^esup>)"
  apply(rule cartesian_power_car_memI')
  using assms proj_at_index_list_length apply blast
    using assms project_at_indices_nth[of S] 
    by (smt cartesian_power_car_memE cartesian_power_car_memE' indices_of_def lessThan_iff nth_elem_closed subsetD)

lemma(in ring) ring_pow_proj_is_map:
  assumes "S \<subseteq> {..<n}"
  shows "\<pi>\<^bsub>n,S\<^esub> \<in> struct_maps (R\<^bsup>n\<^esup>) (R\<^bsup>card S\<^esup>)"
proof(rule struct_maps_memI)
  show "\<And>x. x \<in> carrier (R\<^bsup>n\<^esup>) \<Longrightarrow> \<pi>\<^bsub>n,S\<^esub> x \<in> carrier (R\<^bsup>card S\<^esup>)"
    using project_at_indices_closed unfolding ring_pow_proj_def 
    by (metis assms cartesian_power_car_memE indices_of_def restrict_apply')
  show " \<And>x. x \<notin> carrier (R\<^bsup>n\<^esup>) \<Longrightarrow> \<pi>\<^bsub>n, S\<^esub> x = undefined"
    by (metis restrict_apply ring_pow_proj_def)
qed

lemma(in ring) project_at_indices_ring_pow_proj:
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "\<pi>\<^bsub>S\<^esub> x = \<pi>\<^bsub>n,S\<^esub> x"
  unfolding ring_pow_proj_def 
  by (metis assms restrict_apply')

text\<open>
  Cartesian products where the first factor \<open>A\<close> occurs at the entries of some arbitrary index set.
  Note that this product isn't completely arbitrary because the entries of the factor of \<open>A\<close> 
  still occurs in ascending order.\<close>

definition twisted_cartesian_product ("Prod\<^bsub>_, _\<^esub>") where
"twisted_cartesian_product S S' A B = {a . length a = card S + card S' \<and> \<pi>\<^bsub>S\<^esub> a \<in> A \<and> \<pi>\<^bsub>S'\<^esub> a \<in> B}"

lemma twisted_cartesian_product_mem_length:
  assumes "card S = n"
  assumes "card S' = m"
  assumes "a \<in> Prod\<^bsub>S,S'\<^esub> A B"
  shows "length a = n + m"
  using assms unfolding twisted_cartesian_product_def 
  by blast

lemma twisted_cartesian_product_closed:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "card S = n"
  assumes "card S' = m"
  assumes "S \<union> S' = {..<n + m}"
  shows "twisted_cartesian_product S S' A B \<subseteq> carrier (R\<^bsup>n + m\<^esup>)"
proof(rule subsetI)
  fix x assume A: "x \<in> twisted_cartesian_product S S' A B"
  show "x \<in> carrier (R\<^bsup>n + m\<^esup>)"
  proof(rule cartesian_power_car_memI')
    show "length x = n + m"
      using twisted_cartesian_product_mem_length \<open>x \<in> twisted_cartesian_product S S' A B\<close> assms(1) assms(2) assms(3) assms(4) assms(5) by blast
    fix i assume A': "i < n + m"
    have 0: "indices_of x = {..<n+m}"
      by (simp add: \<open>length x = n + m\<close> indices_of_def)
    show "x ! i \<in> carrier R"
    proof(cases "i \<in> S")
      case True
      have "x!i = \<pi>\<^bsub>S\<^esub>x ! (set_rank S i)"
        using A' 0 assms 
        by (metis True Un_upper1 project_at_indices_nth')
      then show ?thesis 
        using project_at_indices_closed[of x R "n + m" S] A A'
              cartesian_power_car_memE'[of "\<pi>\<^bsub>S\<^esub> x" R "card S"]
        by (metis (no_types, lifting) True UnI2 Un_upper1 assms(1) assms(3) assms(5) 
            finite_lessThan finite_subset mem_Collect_eq set_rank_range sup.absorb_iff1 
            twisted_cartesian_product_def)
    next
      case False
      have "x!i = \<pi>\<^bsub>S'\<^esub>x ! (set_rank S' i)"
        using A' 0 assms 
        by (metis False UnE lessThan_iff project_at_indices_nth' sup.absorb_iff1 sup.right_idem)        
      then show ?thesis 
        using project_at_indices_closed[of x R "n + m" S'] A A'
              cartesian_power_car_memE'[of "\<pi>\<^bsub>S'\<^esub> x" R "card S'"]
        by (metis (no_types, lifting) False UnE UnI2 Un_upper2 assms(2) assms(4) assms(5) 
            finite_lessThan finite_subset lessThan_iff mem_Collect_eq set_rank_range sup.absorb_iff1 
            twisted_cartesian_product_def)
    qed
  qed
qed

lemma twisted_cartesian_product_memE:
  assumes "a \<in> twisted_cartesian_product S S' A B"
  shows "\<pi>\<^bsub>S\<^esub> a \<in> A" "\<pi>\<^bsub>S'\<^esub> a \<in> B"
  using assms(1) unfolding twisted_cartesian_product_def apply blast 
    using assms(1) unfolding twisted_cartesian_product_def by blast

lemma twisted_cartesian_product_memI:
  assumes "\<pi>\<^bsub>S\<^esub> a \<in> A" 
  assumes "\<pi>\<^bsub>S'\<^esub> a \<in> B"
  assumes "length a = card S + card S'"
  shows "a \<in> twisted_cartesian_product S S' A B"
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) mem_Collect_eq twisted_cartesian_product_def)

lemma twisted_cartesian_product_empty_left_factor:
  assumes "A = {}"
  shows "twisted_cartesian_product S S' A B = {}"
  by (metis assms emptyE equals0I twisted_cartesian_product_memE(1))

lemma twisted_cartesian_product_empty_right_factor:
  assumes "B = {}"
  shows "twisted_cartesian_product S S' A B = {}"
  by (metis assms emptyE equals0I twisted_cartesian_product_memE(2))

lemma twisted_cartesian_project_left:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "A \<noteq> {}"
  assumes "B \<noteq> {}"
  assumes "card S = n"
  assumes "card S' = m"
  assumes "S \<union> S' = {..<n + m}"
  shows "\<pi>\<^bsub>S\<^esub> ` (Prod\<^bsub>S,S'\<^esub> A B) = A"
proof
  have f0: "S \<inter> S' = {}"
  proof-
    have "card (S \<union> S') = card S + card S'"
      by (simp add: assms(5) assms(6) assms(7))
    thus ?thesis 
    by (metis Nat.add_diff_assoc2 add.right_neutral add_diff_cancel_left' assms(6) 
        assms(7) card_0_eq card_Un_Int finite_Int finite_Un finite_lessThan le_add1)
qed    
  show "\<pi>\<^bsub>S\<^esub> ` (Prod\<^bsub>S,S'\<^esub> A B) \<subseteq> A"
   unfolding twisted_cartesian_product_def 
   by blast
  show "A \<subseteq> \<pi>\<^bsub>S\<^esub> ` (Prod\<^bsub>S,S'\<^esub> A B)"
  proof fix x assume A: "x \<in> A"
    obtain y where y_def: "y \<in> B"
    using assms(4) by blast  
    obtain a where a_def: 
      "a = map (\<lambda>i. if i \<in> S then (x ! set_rank S i) else (y ! set_rank S' i)) [0..<n+m]"
      by blast 
    have 0: "S \<subseteq> indices_of a"
      by (metis (no_types, lifting) Un_upper1 a_def assms(7) diff_zero indices_of_def length_map length_upt)
    have 1: "S' \<subseteq> indices_of a"
      by (metis (no_types, lifting) Un_upper2 a_def assms(7) diff_zero indices_of_def length_map length_upt)
    have 2: "\<pi>\<^bsub>S\<^esub> a = x"
    proof-
      have 20: "length (\<pi>\<^bsub>S\<^esub> a) = n"
        by (metis (no_types, lifting) Un_upper1 a_def assms(5) assms(7) diff_zero indices_of_def length_map length_upt proj_at_index_list_length)
      have "\<And>i. i < n \<Longrightarrow> \<pi>\<^bsub>S\<^esub> a ! i = x ! i"
      proof- fix i assume A: "i < n" show "\<pi>\<^bsub>S\<^esub> a ! i = x ! i"
          using 0 assms a_def project_at_indices_nth'[of S a "nth_elem S i"] set_rank_nth_elem_inv[of S i]
                nth_map[of i "[0..<n+m]"] 
          by (smt (z3) A add.left_neutral card.infinite diff_zero indices_of_def length_map length_upt lessThan_iff not_less_zero nth_elem_closed nth_map nth_upt subsetD)
      qed
      thus ?thesis using 20 
        by (metis A assms(1) cartesian_power_car_memE nth_equalityI subsetD)
    qed
    have 3: "\<pi>\<^bsub>S'\<^esub> a = y"
    proof-
      have 20: "length (\<pi>\<^bsub>S'\<^esub> a) = m"
        using "1" assms(6) proj_at_index_list_length by blast        
      have "\<And>i. i < m \<Longrightarrow> \<pi>\<^bsub>S'\<^esub> a ! i = y ! i"
      proof- fix i assume A: "i < m" 
        have "nth_elem S' i \<notin> S"
          using nth_elem_closed[of i S']  f0  A assms(6) by blast
        thus "\<pi>\<^bsub>S'\<^esub> a ! i = y ! i"
          using 0 assms a_def project_at_indices_nth'[of S' a "nth_elem S' i"] set_rank_nth_elem_inv[of S' i]
                nth_map[of i "[0..<n+m]"] 
          by (smt "1" A add.left_neutral card.infinite diff_zero indices_of_def length_map length_upt lessThan_iff not_less0 nth_elem_closed nth_map nth_upt subsetD)
      qed
      thus ?thesis 
        by (metis "20" assms(2) cartesian_power_car_memE nth_equalityI subsetD y_def)      
    qed
    have"a \<in> (Prod\<^bsub>S,S'\<^esub> A B)"
      apply(rule twisted_cartesian_product_memI)
        apply (simp add: "2" A)
          apply (simp add: "3" y_def)
            by (metis (no_types, lifting) a_def assms(5) assms(6) diff_zero length_map length_upt)
    thus "x \<in> \<pi>\<^bsub>S\<^esub> ` (Prod\<^bsub>S,S'\<^esub> A B)"
      using "2" by blast
  qed
qed

lemma twisted_cartesian_product_swap:
  shows "(Prod\<^bsub>S,S'\<^esub> A B) = (Prod\<^bsub>S',S\<^esub> B A)"
  unfolding twisted_cartesian_product_def 
  by (metis add.commute)

lemma twisted_cartesian_project_right:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "A \<noteq> {}"
  assumes "B \<noteq> {}"
  assumes "card S = n"
  assumes "card S' = m"
  assumes "S \<union> S' = {..<n + m}"
  shows "\<pi>\<^bsub>S'\<^esub> ` (Prod\<^bsub>S,S'\<^esub> A B) = B"
  using assms twisted_cartesian_project_left[of B R m A n S' S] twisted_cartesian_product_swap
  by (metis add.commute sup_commute)

text \<open>
  Cartesian products which send points $a = (a_1, \dots, a_{m})$ and $b = (b_1, \dots, b_{n})$ to
  the point $(a_1, \dots, a_i, b_1, \dots, b_{n},a_{i+1}, \dots, a_m)$
\<close>
definition splitting_permutation :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
                                          nat \<Rightarrow> nat" where
"splitting_permutation l1 l2 i j = (if j < i then j else 
                                      (if i \<le> j \<and> j < l1 then (l2 + j) else 
                                          (if j < l1 + l2 then j - l1 + i else j)))"

lemma splitting_permutation_case_1_unique: 
  assumes "i \<le> l1"
  assumes "y < i"
  assumes "splitting_permutation l1 l2 i j = y"
  shows "j = y"
  unfolding splitting_permutation_def 
  using assms(2) assms(3) splitting_permutation_def by auto
  
lemma splitting_permutation_case_1_exists: 
  assumes "i \<le> l1"
  assumes "y < i"
  shows "splitting_permutation l1 l2 i y = y"
  unfolding splitting_permutation_def 
  by (simp add: assms(2))

lemma splitting_permutation_case_2_unique:
  assumes "i \<le> l1"
  assumes "i \<le> y \<and> y < l2 + i"
  assumes "splitting_permutation l1 l2 i j = y"
  shows "j = y + l1 - i"
  unfolding splitting_permutation_def 
  using assms(1) assms(2) assms(3) le_add_diff_inverse2 not_less_iff_gr_or_eq 
        splitting_permutation_def trans_less_add2 by auto

lemma splitting_permutation_case_2_exists:
  assumes "i \<le> l1"
  assumes "i \<le> y \<and> y < l2 + i"
  shows "splitting_permutation l1 l2 i (y + l1 - i) = y"
  unfolding splitting_permutation_def 
  using assms(1) assms(2) less_diff_conv2 by auto

lemma splitting_permutation_case_3_unique: 
  assumes "i \<le> l1"
  assumes "l2 + i \<le> y \<and> y < l1 + l2"
  assumes "splitting_permutation l1 l2 i j = y"
  shows "j = y - l2"
  unfolding splitting_permutation_def 
  by (smt Nat.le_diff_conv2 add_diff_cancel_left' add_diff_cancel_right' add_leD2 
      assms(2) assms(3) le_add1 le_diff_iff not_le splitting_permutation_def)

lemma splitting_permutation_case_3_exists: 
  assumes "i \<le> l1"
  assumes "l2 + i \<le> y \<and> y < l1 + l2"
  shows "splitting_permutation l1 l2 i (y - l2) = y"
  unfolding splitting_permutation_def 
  by (metis Nat.le_diff_conv2 add.commute add_leD1 assms(2) leD le_add_diff_inverse less_diff_conv2)

lemma splitting_permutation_case_4_unique: 
  assumes "i \<le> l1"
  assumes "l1 + l2 \<le> y"
  assumes "splitting_permutation l1 l2 i j = y"
  shows "j = y"
  using assms(1) assms(2) assms(3) le_add_diff_inverse2 less_le_trans 
      splitting_permutation_def by auto

lemma splitting_permutation_case_4_exists: 
  assumes "i \<le> l1"
  assumes "l1 + l2 \<le>y"
  shows "splitting_permutation l1 l2 i y = y"
  unfolding splitting_permutation_def 
  using assms(2) by auto

lemma splitting_permutation_permutes:
  assumes "i \<le> l1"
  shows "(splitting_permutation l1 l2 i) permutes {..< l1 + l2}"
proof-
  have 0: "(\<forall>x. x \<notin> {..<l1 + l2} \<longrightarrow> splitting_permutation l1 l2 i x = x)"
  proof fix x show "x \<notin> {..<l1 + l2} \<longrightarrow> splitting_permutation l1 l2 i x = x"
    proof assume A: "x \<notin> {..<l1 + l2}"
        then show "splitting_permutation l1 l2 i x = x"
          using assms unfolding splitting_permutation_def 
    by simp
    qed
  qed
  have 1: "(\<forall>y. \<exists>!x. splitting_permutation l1 l2 i x = y)"
  proof fix y
    show "\<exists>!x. splitting_permutation l1 l2 i x = y"
    proof(cases "y < i")
      case True
      then show ?thesis 
        using splitting_permutation_case_1_exists splitting_permutation_case_1_unique assms 
        by (metis splitting_permutation_def)        
    next
      case F0: False
      show ?thesis 
      proof(cases "i \<le> y \<and> y < l2 + i")
        case True
        then show ?thesis
        using F0 splitting_permutation_case_2_exists splitting_permutation_case_2_unique assms 
        by metis
      next
        case F1: False
        show ?thesis
          proof(cases "l2 + i \<le> y \<and> y < l1 + l2")
            case True
            then show ?thesis 
              using F0 F1 splitting_permutation_case_3_exists splitting_permutation_case_3_unique assms 
              by metis 
          next
            case F2: False
            show ?thesis
              using F0 F1 F2 splitting_permutation_case_4_exists splitting_permutation_case_4_unique assms 
              by (metis leI not_less)
          qed
        qed
      qed
  qed
  show ?thesis 
    using 0 1  permutes_def  
    by  blast 
qed

lemma splitting_permutation_action:
  assumes "i \<le>l1"
  assumes "length a1 = l1"
  assumes "length a2 = l2"
  shows "permute_list (splitting_permutation l1 l2 i) ((take i a1) @ a2 @ (drop i a1)) = 
                      a1@a2"
proof-
  obtain x where x_def:  "x = permute_list (splitting_permutation l1 l2 i) ((take i a1) @ a2 @ (drop i a1))"
    by blast 
  obtain y where y_def: "y = a1 @ a2"
    by blast 
  have 0: "length x = length y"
    using x_def y_def  assms splitting_permutation_permutes[of i l1 l2]
    by (smt add.commute add.left_commute le_add_diff_inverse length_append 
        length_drop length_permute_list length_take min.absorb2)
  have 1: "\<And>i. i < l1 + l2 \<Longrightarrow> x ! i = y ! i"
  proof- fix j assume A: "j < l1 + l2"
    show "x ! j = y ! j"
      apply(cases "j < i")
       apply (smt "0" A append_take_drop_id assms(1) assms(2) assms(3) length_append length_permute_list length_take less_le_trans min.absorb2 nth_append permute_list_nth splitting_permutation_case_1_exists splitting_permutation_permutes x_def y_def)
      apply(cases "i \<le> j \<and> j < l1")
       apply (smt "0" A add.left_commute append_take_drop_id assms(1) assms(2) assms(3) le_add_diff_inverse length_append length_permute_list length_take min.absorb2 nth_append nth_append_length_plus permute_list_nth splitting_permutation_def splitting_permutation_permutes x_def y_def)
      using x_def y_def assms
    by (smt "0" A add.commute add_diff_cancel_left' add_diff_inverse_nat length_append length_permute_list length_take less_diff_conv min.absorb2 not_le nth_append permute_list_nth splitting_permutation_case_1_unique splitting_permutation_def splitting_permutation_permutes) 
  qed
  have 2: "length x = l1 + l2"
     by (simp add: x_def assms(2) assms(3))
   have 3: "x = y"
     using 0 1 2  
  by (metis nth_equalityI)
  then show ?thesis 
    using x_def y_def 
    by blast
qed

definition scp_permutation where
"scp_permutation l1 l2 i = fun_inv (splitting_permutation l1 l2 i)"

lemma scp_permutation_action:
  assumes "i \<le>l1"
  assumes "length a1 = l1"
  assumes "length a2 = l2"
  shows "permute_list (scp_permutation l1 l2 i) (a1@a2) = ((take i a1) @ a2 @ (drop i a1))"
proof-
  have "(scp_permutation l1 l2 i) \<circ> (splitting_permutation l1 l2 i) = id"
    by (metis assms(1) fun_inv_def permutes_inv_o(2) scp_permutation_def splitting_permutation_permutes)
  then have "permute_list ((scp_permutation l1 l2 i) \<circ> (splitting_permutation l1 l2 i) ) ((take i a1) @ a2 @ (drop i a1)) = 
          ((take i a1) @ a2 @ (drop i a1))"
    by (metis permute_list_id)
  then show ?thesis using splitting_permutation_action permute_list_compose
    by (smt \<open>scp_permutation l1 l2 i \<circ> splitting_permutation l1 l2 i = id\<close> assms(1) 
        assms(2) assms(3) fun_inv_def length_append length_permute_list permutes_inv permutes_inv_o(1) scp_permutation_def splitting_permutation_permutes)
qed

lemma scp_permutes:
  assumes "i \<le>l1"
  shows "(scp_permutation l1 l2 i) permutes {..<l1 + l2}"
  by (simp add: assms(1) fun_inv_def permutes_inv scp_permutation_def splitting_permutation_permutes)

definition split_cartesian_product where
"split_cartesian_product l1 l2 i A B = permute_list (scp_permutation l1 l2 i) ` (cartesian_product A B)"

lemma split_cartesian_product_memI:
  assumes "a1@a2 \<in> A"
  assumes "b \<in> B"
  assumes "A \<subseteq> carrier (R\<^bsup>l1\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>l2\<^esup>)"
  assumes "length a1 = i"
  shows "a1@b@a2 \<in> split_cartesian_product l1 l2 i A B"
proof-
  have P: "a1@a2@b \<in> cartesian_product A B"
    by (metis append.assoc assms(1) assms(2) assms(3) assms(4) cartesian_product_memI')  
  have 0: "i \<le> l1" 
    using assms 
    by (metis cartesian_power_car_memE le_add1 length_append subset_iff)
  have 1: "length (a1@a2) = l1"
    using assms(1) assms(3) cartesian_power_car_memE 
    by blast
  have 2: "length b = l2"
    using assms(2) assms(4) cartesian_power_car_memE 
    by blast
  have 3: "take i (a1 @ a2) = a1"
    by (simp add: assms(5))
  have 4: "drop i (a1 @ a2) = a2"
    by (simp add: assms(5))
  have "permute_list (scp_permutation l1 l2 i) ((a1 @ a2) @ b) = take i (a1 @ a2) @ b @ drop i (a1 @ a2)"
    using 0 1 2 scp_permutation_action[of i l1 "a1@a2" b l2]
    by blast
  then have "permute_list (scp_permutation l1 l2 i) ((a1@a2)@b) = a1@b@a2 "
    by(simp only: 3 4)
  then have "permute_list (scp_permutation l1 l2 i) (a1@a2@b) = a1@b@a2 "
    by simp
  then show ?thesis
    using P unfolding split_cartesian_product_def  
    by (metis (mono_tags, lifting) image_eqI)
qed
    
lemma split_cartesian_product_memI':
  assumes "a \<in> A"
  assumes "b \<in> B"
  assumes "A \<subseteq> carrier (R\<^bsup>l1\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>l2\<^esup>)"
  assumes "i \<le> l1"
  shows "(take i a)@b@(drop i a) \<in> split_cartesian_product l1 l2 i A B"
  using assms split_cartesian_product_memI[of "take i a" "drop i a" A b B R l1 l2 i]
  by (metis append_take_drop_id cartesian_power_car_memE length_take min.absorb2 subset_iff)

lemma split_cartesian_product_memE:
  assumes "a \<in> split_cartesian_product l1 l2 i A B"
  assumes "A \<subseteq> carrier (R\<^bsup>l1\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>l2\<^esup>)"
  assumes "i \<le> l1"
  shows "(take i a)@(drop (i + l2) a) \<in> A"
        "(drop i (take (i + l2) a)) \<in> B"
proof-
  obtain b where b_def: "b \<in> cartesian_product A B \<and> a = permute_list (scp_permutation l1 l2 i) b"
    using assms split_cartesian_product_def
    by (metis (mono_tags, lifting) image_iff)
  then have 0: "(take l1 b) \<in> A \<and> (drop l1 b) \<in> B"
    using assms(2) cartesian_product_memE(1)[of b A B R l1] cartesian_product_memE(2)[of b A B R l1]  
    by metis 
  have 1: "a = (take i (take l1 b))@(drop l1 b)@(drop i (take l1 b))"
    using  "0" append_take_drop_id assms(2) assms(3) assms(4) b_def 
      cartesian_power_car_memE scp_permutation_action subsetD
    by smt
  have 2: "(take i a) = (take i (take l1 b))"
    using 0 1 
    by (metis (no_types, lifting) append_eq_append_conv append_take_drop_id   
        assms(4) b_def length_permute_list length_take min.absorb1 take_take)
  have "drop (i + l2) a = drop i (take l1 b)"
  proof-
    have "drop (i + l2) ( (take i (take l1 b))@(drop l1 b)@(drop i (take l1 b))) = drop i (take l1 b)"
      using assms 
      by (metis "0" "1" "2" add.commute append_eq_conv_conj append_take_drop_id 
          cartesian_power_car_memE drop_drop subsetD)
    then show ?thesis 
      using 1 
      by blast
  qed
  then show "take i a @ drop (i + l2) a \<in> A"
    by (metis "0" "2" append_take_drop_id)
  have 3: "length b = l1 + l2 "
    by (metis "0" append_take_drop_id assms(2) assms(3) cartesian_power_car_memE length_append subsetD)
  then have "(drop i (take (i + l2) ((take i (take l1 b))@(drop l1 b)@(drop i (take l1 b))))) = (drop l1 b)"
  proof-
    have 0: "take (i + l2) ((take i (take l1 b))@(drop l1 b)@(drop i (take l1 b))) = 
            take (i + l2) ((take i b)@(drop l1 b)@(drop i (take l1 b)))"
      using assms(4) 
      by (metis min.absorb1 take_take)
    have 1: "length ((take i b)@(drop l1 b)) = i  + l2"
      using 3  assms 
      by (metis (no_types, opaque_lifting) add_diff_cancel_left' b_def length_append length_drop 
          length_permute_list length_take  min.absorb2 trans_le_add1)
    have 2: "take (i + l2) (((take i b)@(drop l1 b))@(drop i (take l1 b))) = (take i b)@(drop l1 b)"
      using 1 
      by (metis append_eq_conv_conj)
    have 3: "take (i + l2) ((take i b)@(drop l1 b)@(drop i (take l1 b))) = (take i b)@(drop l1 b)"
      using 2 
      by (metis append.assoc)
    have 4: "take (i + l2) ((take i (take l1 b))@(drop l1 b)@(drop i (take l1 b))) =  (take i b)@(drop l1 b)"
      using "0" "3" 
      by presburger
    then have 5: "(drop i (take (i + l2) ((take i (take l1 b))@(drop l1 b)@(drop i (take l1 b))))) = 
                drop i ((take i b)@(drop l1 b))"
      by presburger
    have "length (take i b) = i"
      by (metis "1" append_take_drop_id assms(4) le_add1 length_take min.absorb2 min.bounded_iff nat_le_linear take_all)
    then show ?thesis using 5 
      by (metis append_eq_conv_conj)
  qed
  then have "drop i (take (i + l2) a) = drop l1 b"
    using 1 by blast 
  then show "(drop i (take (i + l2) a)) \<in> B"
    using 0 
    by presburger
qed

lemma split_cartesian_product_mem_length:
  assumes "a \<in> split_cartesian_product l1 l2 i A B"
  assumes "A \<subseteq> carrier (R\<^bsup>l1\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>l2\<^esup>)"
  assumes "i \<le> l1"
  shows "length a = l1 + l2"
  using assms unfolding split_cartesian_product_def 
  using cartesian_product_closed[of A R l1 B l2] scp_permutes[of i l1 l2]
  by (smt cartesian_power_car_memE imageE in_mono length_permute_list scp_permutation_def)

lemma split_cartesian_product_memE':
  assumes "a1@b@a2 \<in> split_cartesian_product l1 l2 i A B"
  assumes "A \<subseteq> carrier (R\<^bsup>l1\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>l2\<^esup>)"
  assumes "i \<le> l1"
  assumes "length a1 = i"
  assumes "length b = l2"
  assumes "length as = (l1 - i)"
  shows "a1@a2 \<in> A"
        "b \<in> B"
  using assms split_cartesian_product_memE(1)[of "a1@b@a2" l1 l2  i A B R]
  apply (metis  append.assoc append_eq_conv_conj length_append)
  using assms split_cartesian_product_memE(2)[of "a1@b@a2" l1 l2  i A B R]
  by (metis add_diff_cancel_left' append_eq_conv_conj drop_take)

lemma split_cartesian_product_closed:
  assumes "A \<subseteq> carrier (R\<^bsup>l1\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>l2\<^esup>)"
  assumes "i \<le> l1"
  shows "split_cartesian_product l1 l2 i A B \<subseteq> carrier (R\<^bsup>l1 + l2\<^esup>)"
proof fix x 
  assume A: "x \<in> split_cartesian_product l1 l2 i A B"
  show "x \<in> carrier (R\<^bsup>l1 + l2\<^esup>)"
    apply(rule cartesian_power_car_memI)
     apply (meson \<open>x \<in> split_cartesian_product l1 l2 i A B\<close> assms(1) 
        assms(2) assms(3) split_cartesian_product_mem_length)
    using assms A unfolding split_cartesian_product_def 
    using cartesian_product_closed[of A R l1 B l2]
    by (smt A cartesian_power_car_memE'' image_iff length_permute_list 
        scp_permutes set_permute_list split_cartesian_product_mem_length subsetD)
qed
    
text\<open>General function for permuting the elements of a simple cartesian product:\<close>

definition intersperse :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
"intersperse \<sigma> as bs = permute_list \<sigma> (as@bs) "

lemma intersperseE:
  assumes "\<sigma> permutes ({..<n})"
  assumes "length as + length bs = n"
  shows "length (intersperse \<sigma> as bs) = n"
  by (metis assms(2) intersperse_def length_append length_permute_list)

lemma intersperseE':
  assumes "\<sigma> permutes ({..<n})"
  assumes "length as + length bs = n"
  assumes "length as = k"
  assumes "\<sigma> i < k"
  shows "(intersperse \<sigma> as bs)! i  = as ! \<sigma> i"
proof-
  have "permute_list \<sigma> (as @ bs) ! i = (as @ bs) ! \<sigma> i"
    using assms permute_list_nth[of \<sigma> "(as@bs)" i]
    unfolding intersperse_def 
    by (metis length_append lessThan_iff permutes_not_in trans_less_add1)    
  then show ?thesis using assms 
    by (metis intersperse_def nth_append)
qed

lemma intersperseE'':
  assumes "\<sigma> permutes ({..<n})"
  assumes "length as + length bs = n"
  assumes "length as = k"
  assumes "i < n"
  assumes "\<sigma> i \<ge> k"
  shows "(intersperse \<sigma> as bs)! i  = bs ! ((\<sigma> i) - k)"  
proof-
  have 0: "permute_list \<sigma> (as @ bs) ! i = (as @ bs) ! \<sigma> i"
    using assms permute_list_nth[of \<sigma> "(as@bs)" i]
    unfolding intersperse_def 
  proof -
    have "(as @ bs) ! \<sigma> i = (as @ bs) ! \<sigma> ([0..<n] ! i)"
      by (simp add: \<open>i < n\<close>)
    then show ?thesis
      by (metis (no_types) \<open>i < n\<close> \<open>length as + length bs = n\<close> diff_zero length_append 
          length_upt nth_map permute_list_def)
  qed
  have 1: "\<sigma> i < n"
    using assms 
    by (meson lessThan_iff permutes_in_image)  
  have 2: "(\<sigma> i) - k < length bs"
    using "1" assms(2) assms(3) assms(5) by linarith
  have "(as @ bs) ! (\<sigma> i)  =  bs ! (\<sigma> i - length as)"
    using assms 1 2 nth_append[of as bs "(\<sigma> i)"] 
    by (meson not_le)
  then   have 3: "(as @ bs) ! (\<sigma> i)  =  bs ! (\<sigma> i - k)"
    using assms 
    by blast
  have 4: "permute_list \<sigma> (as @ bs) ! i = (as @ bs) ! (\<sigma> i)"
    using "0" by blast
  show ?thesis using 4 3  unfolding intersperse_def
    by auto     
qed

text\<open>Some more lemmas about the project\_at\_indices function.\<close>

lemma project_at_indices_consecutive_ind_length:
  assumes "(i::nat) < j"
  assumes "j \<le> n"
  assumes "length a = n"
  shows "length (project_at_indices {i..<j} a) = j - i"
  using assms proj_at_index_list_length[of "{i..<j}" a] 
  unfolding indices_of_def 
  by (metis card_atLeastLessThan ivl_subset le_less_linear lessThan_atLeast0 not_less0)   

lemma project_at_indices_consecutive_ind_length':
  assumes "(i::nat) < j"
  assumes "j \<le> n"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "length (project_at_indices {i..<j} a) = j - i"
  using assms(1) assms(2) assms(3) cartesian_power_car_memE project_at_indices_consecutive_ind_length by blast

lemma  sorted_list_of_set_from_up_to:
  assumes  "(i::nat)  < j"
  assumes "k < j - i"
  shows "sorted_list_of_set {i..<j} ! k = i + k"
  using assms apply(induction k)
  apply simp by simp
    
lemma nth_elem_consecutive_indices:
  assumes "(i::nat) < j"
  assumes "k < j - i"
  shows "nth_elem {i..<j} k = i + k"
  using nth_elem.simps[of "{i..<j}" k] sorted_list_of_set_from_up_to assms(2) 
  by auto
  
lemma project_at_indices_consecutive_indices:
  assumes "(i::nat) < j"
  assumes "j \<le> n"
  assumes "length a = n"
  assumes "k < j - i"
  shows "(project_at_indices {i..<j} a) ! k = a! (i + k)"
  using assms nth_elem_consecutive_indices[of i j k]
  by (metis atLeast0LessThan card_atLeastLessThan indices_of_def ivl_subset linorder_le_less_linear not_less0 project_at_indices_nth)
  
lemma project_at_indices_consecutive_indices':
  assumes "(i::nat) < j"
  assumes "j \<le> n" 
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "k < j - i"
  shows "(project_at_indices {i..<j} a) ! k = a! (i + k)"
  using assms(1) assms(2) assms(3) assms(4) cartesian_power_car_memE project_at_indices_consecutive_indices by blast

lemma tl_as_projection:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "tl a = project_at_indices {1::nat..<n} a"
proof-
  have 0: "indices_of a = {..<n}"
    using assms cartesian_power_car_memE indices_of_def 
    by blast    
  have 1: "length (tl a) = n - 1"
    using assms cartesian_power_car_memE length_tl 
    by blast
  have 2: "length (tl a) = length (project_at_indices {1::nat..<n} a)"
    using 0 assms cartesian_power_car_memE[of a R n] proj_at_index_list_length[of "{1::nat..<n}" a] 
    by (metis "1" atLeastLessThan_iff card_atLeastLessThan  lessThan_iff subsetI)
  have "\<And>i. i < n - 1 \<Longrightarrow> (tl a) ! i = (project_at_indices {1::nat..<n} a) ! i"
    using project_at_indices_consecutive_indices'[of 1 n n a R] assms 
    by (metis "1" One_nat_def Suc_leI le_add_diff_inverse2 le_numeral_extra(4) 
        linorder_neqE_nat nat_add_left_cancel_le nat_diff_split_asm not_less0 nth_tl plus_1_eq_Suc)
  then show ?thesis 
    by (metis "1" "2" nth_equalityI)
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Function Rings on Cartesian Powers\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Complement operator\<close>

definition ring_pow_comp :: "('a, 'b) ring_scheme \<Rightarrow> arity \<Rightarrow> 'a tuple set \<Rightarrow> 'a tuple set" where
"ring_pow_comp R n S \<equiv> carrier (R\<^bsup>n\<^esup>) - S"
 
lemma ring_pow_comp_closed:
"ring_pow_comp R n S \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  by (simp add: ring_pow_comp_def)

lemma ring_pow_comp_disjoint:
"ring_pow_comp R n S \<inter> S = {}"
  by (simp add: ring_pow_comp_def inf_sup_aci(1))
  
lemma ring_pow_comp_union:
  assumes "S \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "(ring_pow_comp R n S) \<union> S = carrier (R\<^bsup>n\<^esup>)"
  by (metis ring_pow_comp_def Un_Diff_cancel2 assms sup.absorb_iff1)

lemma ring_pow_comp_carrier:
"ring_pow_comp R n (carrier (R\<^bsup>n\<^esup>)) = {}"
  by (simp add: ring_pow_comp_def)

lemma ring_pow_comp_empty:
"ring_pow_comp R n {} = (carrier (R\<^bsup>n\<^esup>)) "
  by (simp add: ring_pow_comp_def)

lemma ring_pow_comp_demorgans:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "ring_pow_comp R n (A \<union> B) = (ring_pow_comp R n A) \<inter> (ring_pow_comp R n B)"
  by (simp add: ring_pow_comp_def Diff_Un )

lemma ring_pow_comp_demorgans':
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "ring_pow_comp R n (A \<inter> B) = (ring_pow_comp R n A) \<union> (ring_pow_comp R n B)"
  by (simp add: ring_pow_comp_def Diff_Int)

lemma ring_pow_comp_inv:
  assumes "A \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "ring_pow_comp R n (ring_pow_comp R n A) = A"
  by (simp add: ring_pow_comp_def assms double_diff)

text\<open>The function ring defined on the powers of a ring:\<close>
abbreviation(input) ring_pow_function_ring ("Fun\<^bsub>_\<^esub> _") where
"ring_pow_function_ring n R \<equiv> function_ring (carrier (R\<^bsup>n\<^esup>)) R"

text \<open>
  Partial function application. Given a function $f(x_1, \dots, x_{n+1})$, an index $i$ and a 
  point $a \in \text{carrier R}$ returns the function
  $(x_1,..,x_n) \mapsto f(x_1, \dots, x_{i-1}, a, x_i, \dots, x_n)$ \<close>

lemma ring_pow_function_ring_car_memE:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  shows "f \<in> extensional (carrier (R\<^bsup>n\<^esup>))"
        "f \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R"
  using ring_functions.function_ring_car_memE[of R f "carrier (R\<^bsup>n\<^esup>)"] assms 
  unfolding ring_functions_def 
  using  function_ring_def partial_object.select_convs(1)  apply (metis PiE_iff)
  using Int_iff assms PiE_iff function_ring_def partial_object.select_convs(1)
  by (simp add: PiE_iff function_ring_def)
  
definition partial_eval :: "('a, 'b) ring_scheme \<Rightarrow> arity \<Rightarrow> nat \<Rightarrow>  ('a list \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> ('a list \<Rightarrow> 'a)" where
"partial_eval R m n f c = restrict (\<lambda> as. f (insert_at_index as c n)) (carrier (R\<^bsup>m\<^esup>))"

context ring 
begin

lemma function_ring_car_mem_closed: 
  assumes "f \<in> carrier (function_ring S R)"
  assumes "s \<in> S"
  shows "f s \<in> carrier R"
  using assms unfolding function_ring_def ring_record_simps by blast 

lemma function_ring_car_mem_closed': 
  assumes "f \<in> carrier (Fun\<^bsub>Suc k\<^esub> R)"
  assumes "s \<in> carrier (R\<^bsup>Suc k\<^esup>)"
  shows "f s \<in> carrier R"
  using assms unfolding function_ring_def ring_record_simps by blast 

lemma(in ring) partial_eval_domain:
  assumes "f \<in> carrier (Fun\<^bsub>Suc k\<^esub> R)"
  assumes "a \<in> carrier R"
  assumes "n \<le>k"
  shows "(partial_eval R k n f a)  \<in> carrier (Fun\<^bsub>k\<^esub> R)"
  apply(rule ring_functions.function_ring_car_memI)
proof-
  show "\<And>x. x \<in> carrier (R\<^bsup>k\<^esup>) \<Longrightarrow> (partial_eval  R k n f a)  x \<in> (carrier R)"  
  proof-
    fix x
    assume A: "x \<in> carrier (R\<^bsup>k\<^esup>)"
    show "(partial_eval  R k n f a)  x \<in> (carrier R)"
    proof(cases "n = k")
      case True
      then have "(partial_eval  R k n f a)  x = f (insert_at_index x a n)"
        by (metis (no_types, lifting) A restrict_apply' partial_eval_def)     
      then show "(partial_eval  R k n f a) x \<in> carrier R"
        using insert_at_index_closed[of x k R a n] assms ring_functions.function_ring_car_memE[of R]
        unfolding ring_functions_def 
        by (smt A cartesian_power_car_memE funcset_carrier ring_pow_function_ring_car_memE(2))
        
    next
      case False
      then have F0: "(partial_eval  R k n f a)  x = f (insert_at_index x a n)"
        unfolding partial_eval_def 
        using assms   
        by (meson A restrict_apply')  
      have F1: "(insert_at_index x a n) \<in> carrier (R\<^bsup>Suc k\<^esup>)"
        using A assms insert_at_index_closed[of x k R a n] cartesian_power_car_memE 
        by blast
      show "(partial_eval  R k n f a) x \<in> carrier R"
        unfolding F0 apply(rule function_ring_car_mem_closed[of f "carrier (R\<^bsup>Suc k\<^esup>)"]) 
         apply (simp add: assms(1))
        by(rule F1)         
    qed
  qed
  show "\<And>x. x \<notin> carrier (R\<^bsup>k\<^esup>) \<Longrightarrow> (partial_eval  R k n f a)  x = undefined"
  proof-
    fix x
    assume "x \<notin> carrier (R\<^bsup>k\<^esup>)"
    show "(partial_eval  R k n f a) x = undefined"
      unfolding partial_eval_def 
      by (meson \<open>x \<notin> carrier (R\<^bsup>k\<^esup>)\<close> restrict_apply)
  qed
  show "ring_functions R"
    unfolding ring_functions_def 
    by (simp add: ring_axioms)
qed

text\<open>Pullbacks preserve ring power functions\<close>

lemma fun_struct_maps:
"struct_maps (R\<^bsup>n\<^esup>) R = carrier (Fun\<^bsub>n\<^esub> R)"
proof
  show "struct_maps (R\<^bsup>n\<^esup>) R \<subseteq> carrier Fun\<^bsub>n\<^esub> R"
    by (smt function_ring_car_memI struct_maps_memE(1) struct_maps_memE(2) subsetI)    
  show "carrier (Fun\<^bsub>n\<^esub> R) \<subseteq> struct_maps (R\<^bsup>n\<^esup>) R"
    using struct_maps_memI ring_functions.function_ring_car_memE
  by (smt function_ring_car_mem_closed  ring_axioms ring_functions.function_ring_not_car ring_functions.intro subsetI)
qed

lemma pullback_fun_closed:
  assumes "f \<in> struct_maps (R\<^bsup>n\<^esup>) (R\<^bsup>m\<^esup>)"
  assumes "g \<in> carrier (Fun\<^bsub>m\<^esub> R)"
  shows "pullback (R\<^bsup>n\<^esup>) f g \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  using assms(1) assms(2) fun_struct_maps pullback_closed by blast

end


text\<open>Includes $R^{|S|}$ into $R^n$ by pulling back along the projection $R^n \mapsto R^{|S|}$ at indices $S$ \<close>

context ring
begin

definition(in ring) ring_pow_inc :: " (nat set) \<Rightarrow> arity  \<Rightarrow> ('a tuple  \<Rightarrow> 'a) => ('a tuple \<Rightarrow> 'a)  " where
"ring_pow_inc S n f = pullback (R\<^bsup>n\<^esup>) (\<pi>\<^bsub>n,S\<^esub>) f"

lemma ring_pow_inc_is_fun:
  assumes "S \<subseteq> {..<n}"
  assumes "f \<in> carrier (Fun\<^bsub>card S\<^esub> R)"
  shows "ring_pow_inc S n f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  by (metis assms(1) assms(2) ring_pow_proj_is_map pullback_fun_closed ring_pow_inc_def)

text\<open>The "standard" inclusion of powers of function rings into one another\<close>

abbreviation(input) std_proj:: "nat \<Rightarrow> nat \<Rightarrow> ('a list) \<Rightarrow> ('a list)" where 
"std_proj n m \<equiv> ring_pow_proj n ({..<m}) "

lemma std_proj_id: 
  assumes "m \<le> n"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "i < m"
  shows "std_proj n m as ! i = as ! i"
proof-
  have "{..<m} \<subseteq> indices_of as"
    using assms cartesian_power_car_memE unfolding indices_of_def 
    by blast
  thus ?thesis 
  unfolding ring_pow_proj_def
    using assms nth_elem_upto[of i m] 
           project_at_indices_nth[of "{..<m}" as i] 
  by (metis card_lessThan restrict_apply)
qed

abbreviation(input) std_inc:: "nat \<Rightarrow> nat \<Rightarrow> ('a list  \<Rightarrow> 'a)  => ('a list  \<Rightarrow> 'a)" where
"std_inc n m f \<equiv> ring_pow_inc ({..<m}) n f"

lemma std_proj_is_map[simp]:
  assumes "m \<le> n"
  shows "std_proj n m \<in> struct_maps (R\<^bsup>n\<^esup>) (R\<^bsup>m\<^esup>)"
  by (metis assms card_lessThan lessThan_subset_iff ring_pow_proj_is_map)

end
(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Coordinate Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition var :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a)" where
"var R n i = restrict (\<lambda>x. x!i) (carrier (R\<^bsup>n\<^esup>))"

context ring
begin

lemma var_in_car:
  assumes "i < n"
  shows "var R n i \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  apply(rule function_ring_car_memI)
  unfolding var_def 
  apply (metis assms cartesian_power_car_memE' restrict_apply')
  by (meson restrict_apply)
  

lemma varE[simp]: 
  assumes "i < n"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "var R n i x = x ! i"
  unfolding var_def 
  using  assms(2) 
  by (meson restrict_apply')

lemma std_inc_of_var:
  assumes "i < n"
  assumes "n \<le>m"
  shows "std_inc m n (var R n i) =  (var R m i)"
  apply(rule ext)
proof-
  fix x
  show "std_inc m n (var R n i) x = var R m i x"
    apply(cases "x \<in> carrier (R\<^bsup>m\<^esup> )")
  proof-
    show "x \<in> carrier (R\<^bsup>m\<^esup>) \<Longrightarrow> std_inc m n (var R n i) x = var R m i x"
    proof-
      assume A: "x \<in> carrier (R\<^bsup>m\<^esup>)"
      have "(restrict (project_at_indices ({..<n})) (carrier (R\<^bsup>m\<^esup>))) x =  ((project_at_indices ({..<n})) x)"
        by (meson A restrict_apply')
      then have B: "std_inc m n (var R n i) x = (var R n i) ((project_at_indices ({..<n})) x)"
        unfolding ring_pow_inc_def ring_pow_proj_def pullback_def 
        by (metis A compose_eq)
      have C: "var R m i x = x ! i"
        by (metis A assms(1) assms(2) le_iff_add trans_less_add1 varE)
      show "std_inc m n (var R n i) x = var R m i x"
        by (metis A B C assms(1) assms(2) project_at_indices_ring_pow_proj std_proj_id std_proj_is_map struct_maps_memE(1) varE)
    qed
    show "x \<notin> carrier (R\<^bsup>m\<^esup>) \<Longrightarrow> std_inc m n (var R n i) x = var R m i x"
      by (metis (mono_tags, lifting) assms(1) assms(2) card_lessThan lessThan_subset_iff less_SucI ring_axioms nat_induct_at_least ring.fun_struct_maps ring_pow_inc_is_fun struct_maps_memE(2) var_in_car)      
  qed
qed

abbreviation variable ("\<vv>\<^bsub>_\<^esub>") where
"variable n i \<equiv> var R n i"

end

definition var_set :: "('a, 'b) ring_scheme \<Rightarrow>  nat \<Rightarrow> ('a list \<Rightarrow> 'a) set" where
"var_set R n = var R n ` {..<n}"

lemma var_setE:
  assumes "f \<in> var_set R n"
  obtains i where "f = var R n i \<and> i \<in> {..<n}"
  by (metis assms imageE that var_set_def)

lemma var_setI:
  assumes "i \<in> {..<n}"
  assumes  "f = var R n i"
  shows "f \<in> var_set R n"
  using assms(1) assms(2) var_set_def 
  by blast

context ring 
begin

lemma var_set_in_fun_ring_car:
  shows "var_set R n \<subseteq> carrier Fun\<^bsub>n\<^esub> R"
proof
  fix x
  assume "x \<in> var_set R n"
  then obtain i where i_def: "i \<in> {..<n} \<and> x = var R n i"
    unfolding var_set_def 
    by blast
  have "i < n"using i_def 
    using atLeastLessThan_iff by blast  
  then show "x \<in> carrier Fun\<^bsub>n\<^esub> R" 
    using i_def var_in_car by blast     
qed



end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Graphs of functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition fun_graph:: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a) \<Rightarrow> 'a list set" where
"fun_graph R n f = {as. (\<exists>x \<in> carrier (R\<^bsup>n\<^esup>). as = x @ [f x])}"

context ring 
begin

lemma function_ring_car_memE:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "f a \<in> carrier R"
  using ring_functions.function_ring_car_memE(1)[of R f] 
  unfolding ring_functions_def 
  by (meson assms(1) assms(2) ring_axioms function_ring_car_mem_closed ring_functions_def)

lemma graph_range:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  shows "fun_graph R n f \<subseteq> carrier (R\<^bsup>Suc n\<^esup> )"
proof
  fix x
  assume x_def: "x \<in> fun_graph R n f"
  obtain a where a_def: "a \<in> carrier (R\<^bsup>n\<^esup>) \<and> x = a@[f a]"
    using x_def fun_graph_def 
    by (smt mem_Collect_eq)
  have f_closed: "f a \<in> carrier R"
    using assms function_ring_car_memE a_def 
    by blast 
  show "x \<in> carrier (R\<^bsup>Suc n\<^esup> )"
  proof(rule cartesian_power_car_memI)
    show "length x = Suc n"
      using x_def a_def cartesian_power_car_memE[of a R n]
      by (metis length_append_singleton)
    have "set x = insert (f a) (set a)"
      using a_def   
      by (metis Un_insert_right append_Nil2 list.simps(15) set_append)
    thus "set x \<subseteq> carrier R"
      using a_def 
      by (metis cartesian_power_car_memE'' f_closed insert_subset)
  qed
qed

lemma fun_graph_memE:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  assumes "p \<in> fun_graph R n f"
  shows "(take n p) \<in> carrier (R\<^bsup>n\<^esup>)"
    using assms unfolding fun_graph_def  
  by (metis (no_types, lifting) assms(2) graph_range le_add2 plus_1_eq_Suc subsetD take_closed)

lemma fun_graph_memE':
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  assumes "p \<in> fun_graph R n f"
  shows "f (take n p) = p!n"
  using assms 
  unfolding fun_graph_def 
  by (smt Cons_nth_drop_Suc append_take_drop_id assms(2) butlast_snoc cartesian_power_car_memE 
      drop_all graph_range last_snoc le_Suc_eq lessI mem_Collect_eq subsetD)
  
text\<open>
  apply a function f to the tuple consisting of the first n indices, leaving the remaining indices
  unchanged
\<close>

definition partial_image :: "arity \<Rightarrow> ('c list \<Rightarrow> 'c) \<Rightarrow> 'c list \<Rightarrow> 'c list" where
"partial_image n f as = (f (take n as)) # (drop n as) "

lemma partial_image_range:
  assumes "f \<in> carrier (Fun\<^bsub>n\<^esub> R)"
  assumes "m \<ge> n"
  assumes "as \<in> carrier (R\<^bsup>m\<^esup>)"
  shows "partial_image n f as \<in> carrier (R\<^bsup>m - n + 1\<^esup>)"
proof(cases "m = n")
  case True
  then have "f (take n as) = f as"
    by (metis assms(2) assms(3) cartesian_power_car_memE take_all)
  then have 0: "f (take n as) \<in> carrier R"
    using True assms(1) assms(3) function_ring_car_memE by presburger    
  have 1: "(drop n as) = []"
    using True assms(3) cartesian_power_car_memE drop_all by blast
  then show ?thesis 
    unfolding partial_image_def 
    using 0 1   
    by (metis (no_types, lifting) One_nat_def assms(3) cartesian_power_car_memE 
        cartesian_power_car_memI empty_iff insert_iff length_drop list.set(1) 
        list.set(2) list.size(4) subsetI)
next
  case False
  then have 0: "(drop n as) \<in> carrier (R\<^bsup>m - n\<^esup>)"
    using assms drop_closed[of n m as R] le_neq_implies_less 
    by blast
  have 1: "f (take n as) \<in> carrier R"
    using assms(1) assms(2) assms(3) function_ring_car_memE take_closed by blast    
  show ?thesis 
    apply(rule cartesian_power_car_memI)
     apply (metis "0" One_nat_def cartesian_power_car_memE list.size(4) partial_image_def)
      by (smt "1" assms(3) cartesian_power_car_memE cartesian_power_car_memE' in_set_conv_nth 
      partial_image_def set_ConsD set_drop_subset subsetD subsetI) 
qed

end 


(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Coordinate Rings on Cartesian Powers\<close>
(**************************************************************************************************)
(**************************************************************************************************)

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Basic Facts and Definitions\<close>
(**************************************************************************************************)
(**************************************************************************************************)
locale cring_coord_rings = UP_cring + 
  assumes one_neq_zero: "\<one> \<noteq> \<zero>"

text\<open>coordinate polynomial ring in n variables over a commutative ring\<close>

definition coord_ring :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a, ('a, nat) mvar_poly) module"
 ("_ [\<X>\<^bsub>_\<^esub>]" 80) where "R[\<X>\<^bsub>n\<^esub>] \<equiv> Pring R {..< n::nat}"

sublocale cring_coord_rings < cring_functions R "carrier (R\<^bsup>n\<^esup>)" "Fun\<^bsub>n\<^esub> R"
  unfolding cring_functions_def ring_functions_def  
  apply (simp add: R.ring_axioms R_cring)
  by simp

sublocale cring_coord_rings <  MP?: cring "R[\<X>\<^bsub>n\<^esub>]"
  by (simp add: R.Pring_is_cring R_cring coord_ring_def)

sublocale cring_coord_rings < F?: cring "Fun\<^bsub>n\<^esub> R"
  by (simp add: function_ring_is_cring)

context cring_coord_rings
begin

lemma coord_cring_cring:
"cring (R[\<X>\<^bsub>n\<^esub>])" unfolding coord_ring_def
  by (simp add: R.Pring_is_cring R_cring)
  
text\<open>coordinate constant functions\<close>

abbreviation(input) coord_const :: "'a \<Rightarrow> ('a, nat) mvar_poly" where
"coord_const k \<equiv> ring.indexed_const R k"

lemma coord_const_ring_hom:
"ring_hom_ring R (R[\<X>\<^bsub>n\<^esub>]) coord_const"
  unfolding coord_ring_def
  apply(rule ring_hom_ringI)
       apply (simp add: R.ring_axioms)
      apply (simp add: R.Pring_is_ring)
     apply (simp add: R.indexed_const_closed)
    apply (simp add: R.indexed_const_mult)
  apply (simp add: R.Pring_add R.indexed_padd_const)
 by (simp add: R.Pring_one)
  
text\<open>coordinate functions\<close>

lemma pvar_closed:
  assumes "i < n"
  shows "pvar R i \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  unfolding var_to_IP_def
proof-
  have "set_mset {#i#} \<subseteq> {..<n}"
    using assms 
    by simp    
  then show "mset_to_IP R {#i#} \<in> carrier (R[\<X>\<^bsub>n\<^esub>])" 
    by (simp add: R.ring_axioms coord_ring_def R.Pring_car ring.mset_to_IP_closed)
qed

text\<open>relationship between multiplciation by a variable and index multiplcation\<close>

lemma pvar_indexed_pmult:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "(p \<Otimes> i) = p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i"
proof-
  have "p \<in> Pring_set R {..<(n::nat)} " 
    using R.Pring_car assms 
    by (metis coord_ring_def)   
  then have "p \<in> Pring_set R (UNIV::nat set)" 
    using R.Pring_set_restrict 
    by blast
  then show ?thesis  
    using assms R.poly_index_mult[of p UNIV i]  unfolding var_to_IP_def
    by (metis R.Pring_mult UNIV_I coord_ring_def)    
qed

lemma coord_ring_cfs_closed:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "p m \<in> carrier R"
  using assms unfolding coord_ring_def 
  using R.Pring_carrier_coeff' by blast  

lemma coord_ring_plus:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "(p \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q) m = p m \<oplus> Q m"
  using assms unfolding coord_ring_def 
  by (metis R.Pring_add R.indexed_padd_def)

lemma coord_ring_uminus:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "(\<ominus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> p) m = \<ominus> (p m)"
  using assms unfolding coord_ring_def 
  using MP.add.inv_closed MP.minus_minus coord_ring_cfs_closed coord_ring_def 
        coord_ring_plus is_abelian_group R.is_cring
        R.ring_axioms 
  by (metis P_ring_uminus_def R.Pring_a_inv assms)

lemma coord_ring_minus:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "(p \<ominus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q) m = p m \<ominus> Q m"
  using assms R.Pring_add[of _ p Q] coord_ring_cfs_closed
  unfolding indexed_padd_def coord_ring_def a_minus_def 
  by (metis (no_types, lifting) MP.add.inv_closed coord_ring_def coord_ring_plus 
      cring_coord_rings.coord_ring_uminus cring_coord_rings_axioms)

lemma coord_ring_one:
"\<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m = (if m = {#} then \<one> else \<zero>)"
  by (metis R.Pring_one coord_ring_def R.indexed_const_def)

lemma coord_ring_zero:
"\<zero>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m = \<zero>"
  by (metis MP.minus_zero MP.r_zero MP.zero_closed R_cring coord_ring_cfs_closed coord_ring_plus coord_ring_uminus cring.cring_simprules(17))
  
text\<open>Evaluation of a polynomial at a point\<close>

end

abbreviation(input) point_to_eval_map where
"point_to_eval_map R as \<equiv> (\<lambda>i. (if i< length as then as ! i else \<zero>\<^bsub>R\<^esub>))"

definition eval_at_point :: "('a, 'b) ring_scheme \<Rightarrow> 'a list \<Rightarrow> ('a, nat) mvar_poly \<Rightarrow> 'a" where
"eval_at_point R as p \<equiv> total_eval R  (\<lambda>i. (if i< length as then as ! i else \<zero>\<^bsub>R\<^esub>)) p"


lemma(in cring_coord_rings) eval_at_point_factored:
"eval_at_point R as p = total_eval R (point_to_eval_map R as) p"
  using eval_at_point_def by blast  

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Total Evaluation of a Polynomial\<close>
(**************************************************************************************************)
(**************************************************************************************************)

abbreviation(input) eval_at_poly where
"eval_at_poly R p as \<equiv> eval_at_point R as p"


text\<open>evaluation of coordinate polynomials\<close>

context cring_coord_rings
begin

lemma eval_at_point_closed:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "eval_at_point R a p \<in> carrier R"
proof- 
  have 0: "R.indexed_pset ({..<n}- UNIV) (carrier R) \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
    unfolding coord_ring_def 
    by (simp add: R.Pring_car R.Pring_carrier_subset)
  have 1 : "poly_eval R UNIV (\<lambda>i. if i < length a then a ! i else \<zero>) p \<in> R.indexed_pset ({..<n}- UNIV) (carrier R)"
    by (smt R.Pring_car R.closed_funI R.poly_eval_closed R.zero_closed assms(1) assms(2) cartesian_power_car_memE cartesian_power_car_memE' coord_ring_def)
  hence 2: "poly_eval R UNIV (\<lambda>i. if i < length a then a ! i else \<zero>) p \<in>carrier (R[\<X>\<^bsub>n\<^esub>])"
    using 0 by blast 
  show ?thesis
    unfolding eval_at_point_def total_eval_def eval_in_ring_def  
    using 1 R.Pring_car R.Pring_cfs_closed cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI coord_ring_def R.zero_closed 
    by blast
qed

lemma eval_pvar:
  assumes "i < (n::nat)"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "eval_at_point R a (pvar R i) = a!i"
  unfolding eval_at_point_def
proof-
  have "pvar R i = \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> \<Otimes> i"
    unfolding var_to_IP_def  
    by (metis R.Pring_one coord_ring_def R.monom_add_mset R.one_mset_to_IP)    
  then show "total_eval R (\<lambda>i. if i < length a then a ! i else \<zero>) (pvar R i) = a ! i" 
    using assms R.total_eval_var[of "(\<lambda>i. (if i< length a then a ! i else \<zero>\<^bsub>R\<^esub>))" i ] 
    by (smt cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI var_to_IP_def R.zero_closed)
qed

lemma eval_at_point_const:
  assumes "k \<in> carrier R"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "eval_at_point R a (R.indexed_const k) = k"
  unfolding eval_at_point_def
  using assms(1) R.total_eval_const by blast

lemma eval_at_point_add:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "B \<in> carrier (coord_ring R  n)"
  shows "eval_at_point R a (A \<oplus>\<^bsub>coord_ring R  n\<^esub> B) = 
          eval_at_point R a A \<oplus>\<^bsub>R\<^esub> eval_at_point R a B"
  unfolding eval_at_point_def
  using R.total_eval_add[of A "{..<n}" B] 
  by (smt assms(1) assms(2) assms(3) cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI coord_ring_def R.zero_closed)  
  
lemma eval_at_point_mult:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "B \<in> carrier ((R[\<X>\<^bsub>n\<^esub>]))"
  shows "eval_at_point R a (A \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B) = 
          eval_at_point R a A \<otimes>\<^bsub>R\<^esub> eval_at_point R a B"
    unfolding eval_at_point_def
    using R.total_eval_mult[of A "{..<n}" B] 
    by (smt assms(1) assms(2) assms(3) cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI coord_ring_def R.zero_closed)
    
lemma eval_at_point_indexed_pmult:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "i < n"
  shows "eval_at_point R a (A \<Otimes> i) = 
          eval_at_point R a A \<otimes>\<^bsub>R\<^esub> (a!i)"
proof-
  have "(A \<Otimes> i) = A \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar R i)"
    using assms(2) pvar_indexed_pmult by blast
  then show ?thesis 
    using assms eval_at_point_mult eval_pvar pvar_closed
    by presburger
qed

lemma eval_at_point_ring_hom:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "ring_hom_ring (coord_ring R I) R (eval_at_point R a)"
  unfolding eval_at_point_def
  using R.total_eval_ring_hom 
  by (smt assms cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI coord_ring_def R.zero_closed)
  
lemma eval_at_point_scalar_mult:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "k \<in> carrier R"
  shows "eval_at_point R a (poly_scalar_mult R k A) = k \<otimes>\<^bsub>R\<^esub> (eval_at_point R a A)"
  using assms unfolding eval_at_point_def total_eval_def eval_in_ring_def
  using  R.poly_eval_scalar_mult[of k "(\<lambda>i. if i < length a then a ! i else \<zero>)" A "{..<n}" UNIV]  
        poly_scalar_mult_def
  by (smt R.Pring_car cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI coord_ring_def R.zero_closed)

lemma eval_at_point_smult:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "k \<in> carrier R"
  shows "eval_at_point R a (k \<odot>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> A) = k \<otimes>\<^bsub>R\<^esub> (eval_at_point R a A)"
  by (metis R.Pring_smult assms(1) assms(2) assms(3) coord_ring_def eval_at_point_scalar_mult)

lemma eval_at_point_subtract:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "B \<in> carrier (coord_ring R  n)"
  shows "eval_at_point R a (A \<ominus>\<^bsub>coord_ring R  n\<^esub> B) = 
          eval_at_point R a A \<ominus>\<^bsub>R\<^esub> eval_at_point R a B"
  using assms eval_at_point_add[of a n A "\<ominus>\<^bsub>coord_ring R  n\<^esub> B"] 
        abelian_group.a_inv_closed[of "R[\<X>\<^bsub>n\<^esub>]" B]
  unfolding a_minus_def 
    abelian_group.a_inv_closed abelian_group.minus_minus abelian_group.r_neg1 abelian_groupE(1) abelian_groupE(4) coord_cring_cring cring_def eval_at_point_add eval_at_point_closed is_abelian_group ring_def 
  by (smt MP.add.inv_closed MP.l_neg MP.r_zero MP.zero_closed R.add.inv_closed R.add.m_assoc R.l_neg R.r_zero R.zero_closed eval_at_point_add eval_at_point_closed)

lemma eval_at_point_a_inv:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "B \<in> carrier (coord_ring R  n)"
  shows "eval_at_point R a (\<ominus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B) = \<ominus>\<^bsub>R\<^esub> eval_at_point R a B"
  using assms eval_at_point_subtract[of a n "\<zero>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>" B]
  by (smt MP.add.inv_eq_1_iff MP.l_zero MP.minus_add MP.zero_closed R.is_abelian_group R.r_neg R.r_neg2 a_minus_def abelian_group.a_inv_closed abelian_groupE(4) eval_at_point_add eval_at_point_closed)

lemma eval_at_point_nat_pow:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "eval_at_point R a (A[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>(k::nat)) = (eval_at_point R a A)[^]k"
  apply(induction k)
   apply (metis Group.nat_pow_0 R.Pring_one assms(1) coord_ring_def eval_at_point_const R.one_closed)   
proof- fix k::nat assume IH: "eval_at_poly R (A [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> k) a = eval_at_poly R A a [^] k"
  have "A [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Suc k = A [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> k \<otimes>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> A"
    using MP.nat_pow_Suc by blast    
  then have "eval_at_poly R (A [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Suc k) a =
      eval_at_poly R (A [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> k) a \<otimes> eval_at_poly R A a"
    using monoid.nat_pow_closed[of "(R[\<X>\<^bsub>n\<^esub>])" A k] eval_at_point_mult[of a n "A [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> k" A] assms 
    by (metis R.Pring_is_monoid coord_ring_def)    
  then show " eval_at_poly R (A [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Suc k) a = eval_at_poly R A a [^] Suc k"
    using IH R.nat_pow_Suc 
    by auto 
qed

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Partial Evaluation of a Polynomial\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition coord_partial_eval :: 
  "('a, 'b) ring_scheme \<Rightarrow> nat set \<Rightarrow> 'a list \<Rightarrow> ('a, nat) mvar_poly \<Rightarrow> ('a, nat) mvar_poly" where
"coord_partial_eval R S as = poly_eval R S (point_to_eval_map R as)"

context cring_coord_rings
begin

lemma point_to_eval_map_closed:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "closed_fun R (point_to_eval_map R as)"
  using assms 
  by (smt cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI R.zero_closed)  

lemma coord_partial_eval_hom:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "coord_partial_eval R S as \<in> ring_hom (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>n\<^esub>])"
  unfolding coord_partial_eval_def 
  using point_to_eval_map_closed[of as n] assms 
        R.poly_eval_ring_hom[of "{..<n}" "{..<n}" "point_to_eval_map R as" S]
  by (metis (mono_tags, lifting) Diff_subset coord_ring_def order_refl ring_hom_ring.homh)  

lemma coord_partial_eval_hom':
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "coord_partial_eval R S as \<in> ring_hom (R[\<X>\<^bsub>n\<^esub>]) (Pring R ({..<n} - S))"
  unfolding coord_partial_eval_def 
  using point_to_eval_map_closed[of as n] assms 
        R.poly_eval_ring_hom[of "{..<n} - S" "{..<n}" "point_to_eval_map R as" S]
  by (metis (no_types, lifting) Diff_subset coord_ring_def order_refl ring_hom_ring.homh)  

lemma coord_partial_eval_closed:
  assumes "S \<subseteq> {..<n}"
  assumes "{..<n} - S \<subseteq> I"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "coord_partial_eval R S as p \<in> carrier (Pring R I)"
  unfolding coord_partial_eval_def
  using R.poly_eval_closed[of "point_to_eval_map R as" p "{..<n}" S ] R.Pring_car[of I] R.Pring_carrier_subset  
  by (smt R.Pring_car assms(2) assms(3) assms(4) cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI coord_ring_def subsetD R.zero_closed)  

lemma coord_partial_eval_add:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "coord_partial_eval R S as  (p \<oplus>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> Q) =  
          (coord_partial_eval R S as  p) \<oplus>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> (coord_partial_eval R S as  Q)"
  using assms R.poly_eval_add[of p "{..<n}" Q "(point_to_eval_map R as)" S] Pring_def[of R "{..<n}"]      
  point_to_eval_map_closed[of as n] 
  unfolding coord_partial_eval_def 
  by (metis R.Pring_add R.Pring_car coord_ring_def)  

lemma coord_partial_eval_mult:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "coord_partial_eval R S as  (p \<otimes>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> Q) =  
          (coord_partial_eval R S as  p) \<otimes>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> (coord_partial_eval R S as  Q)"
  using assms R.poly_eval_mult[of p "{..<n}" Q "(point_to_eval_map R as)" S] Pring_def[of R "{..<n}"]      
  point_to_eval_map_closed[of as n] 
  unfolding coord_partial_eval_def 
  by (metis R.Pring_car R.Pring_mult coord_ring_def)  

lemma coord_partial_eval_pvar:
  assumes "\<one> \<noteq> \<zero>"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "i \<in> S \<inter> {..<n}"
  shows "coord_partial_eval R S as (pvar R i) = coord_const (as!i)"
proof-
  have 0: "i \<in> S" using assms 
    by blast
  have "i < length as" 
    by (metis IntD2 assms(2) assms(3) cartesian_power_car_memE lessThan_iff)
  then have "(point_to_eval_map R as i) = as!i"
    by presburger  
  then show ?thesis 
    unfolding coord_partial_eval_def var_to_IP_def  
    using 0 assms point_to_eval_map_closed[of as n] 
        R.poly_eval_index[of "point_to_eval_map R as" S i ]
    by presburger
qed

lemma coord_partial_eval_pvar':
  assumes "\<one> \<noteq> \<zero>"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "i \<notin> S"
  shows "coord_partial_eval R S as (pvar R i) = (pvar R i)"
  unfolding coord_partial_eval_def
  using R.poly_eval_index[of "point_to_eval_map R as" S i ]
  by (smt assms(1) assms(2) assms(3) cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI var_to_IP_def R.zero_closed)  

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>An induction rule for coordinate rings\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma coord_ring_induct:
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "\<And>a. a \<in> carrier R \<Longrightarrow> p (coord_const a)"
  assumes "\<And>i Q. Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> p Q \<Longrightarrow>  i < n \<Longrightarrow> p (Q \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>pvar R i)"
  assumes "\<And>Q0 Q1. Q0 \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> Q1 \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> p Q0 \<Longrightarrow> p Q1 \<Longrightarrow> p (Q0 \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q1)"
  shows "p A"
  apply(rule R.indexed_pset.induct[of A "{..<n}" "carrier R"])
  using R.Pring_car assms(1) 
  apply (metis coord_ring_def) 
  using assms(2) apply blast
  apply (metis (full_types) R.Pring_add R.Pring_car assms(4) coord_ring_def) 
proof-
  fix a i
  assume "a \<in> Pring_set R {..<n}"
  then have 0: "a \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    using R.Pring_car 
    by (simp add: \<open>\<And>I. carrier (Pring R I) = Pring_set R I\<close> \<open>a \<in> Pring_set R {..<n}\<close> coord_ring_def)
  assume 1: "p a"
  assume "i \<in> {..< n}"
  then have 2: "i < n"
    using assms 
    by blast 
  have "p (a \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>pvar R i)"
    using "0" "1" "2" assms(3) by blast
  then show "p (a \<Otimes> i)"
    using "0" pvar_indexed_pmult 
    by presburger
qed
  
end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Algebraic Sets in Cartesian Powers\<close>  
(**************************************************************************************************)
(**************************************************************************************************)

  (**********************************************************************)
  (**********************************************************************)
  subsubsection\<open>The Zero Set of a Single Polynomial\<close>
  (**********************************************************************)
  (**********************************************************************)
definition zero_set  :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a, nat) mvar_poly \<Rightarrow> 'a list set"
 ("V\<index>") where
"zero_set R n p =  {a \<in> carrier (R\<^bsup>n\<^esup>). eval_at_point R a p =\<zero>\<^bsub>R\<^esub>}"

context cring_coord_rings
begin 

lemma zero_setI:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "eval_at_point R a p =\<zero>\<^bsub>R\<^esub>"
  shows  "a \<in> zero_set R n p"
  using assms 
  by (metis (mono_tags, lifting) mem_Collect_eq zero_set_def)

lemma zero_setE:
  assumes  "a \<in> zero_set R n p"
  shows  "a \<in> carrier (R\<^bsup>n\<^esup>)"
         "eval_at_point R a p =\<zero>\<^bsub>R\<^esub>"
  using assms zero_set_def 
  apply blast
  by (metis (mono_tags, lifting) assms mem_Collect_eq zero_set_def)

lemma zero_set_closed:
 "zero_set R n p \<subseteq> carrier (R\<^bsup>n\<^esup>)"
unfolding zero_set_def 
  by blast

end

  (**********************************************************************)
  (**********************************************************************)
  subsubsection\<open>The Zero Set of a Collection of Polynomials\<close>
  (**********************************************************************)
  (**********************************************************************)
definition affine_alg_set :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a, nat) mvar_poly set \<Rightarrow> 'a list set"
  where "affine_alg_set R n as = {a \<in> carrier (R\<^bsup>n\<^esup>). \<forall> b \<in> as. a \<in> (zero_set R n b)}"

context cring_coord_rings
begin 

lemma affine_alg_set_empty:
"affine_alg_set R n {} = carrier (R\<^bsup>n\<^esup>)"
  unfolding affine_alg_set_def by blast 

lemma affine_alg_set_subset_zero_set:
  assumes "b \<in> as"
  shows " affine_alg_set R n as \<subseteq> (zero_set R n b)"
  using assms affine_alg_set_def 
  by blast

lemma(in cring_coord_rings) affine_alg_set_memE:
  assumes "b \<in> as"
  assumes "a \<in>  affine_alg_set R n as"
  shows "eval_at_poly R b a = \<zero>"
  using affine_alg_set_subset_zero_set zero_set_def assms(1) assms(2) 
  by blast

lemma affine_alg_set_subset:
  assumes "as \<subseteq> bs"
  shows " affine_alg_set R n bs \<subseteq> affine_alg_set R n as "
  using assms affine_alg_set_def 
  by blast

lemma affine_alg_set_empty_set:
  assumes "as = {}"
  shows " affine_alg_set R n as = carrier (R\<^bsup>n\<^esup>)"
  unfolding affine_alg_set_def 
  using assms by blast

lemma affine_alg_set_closed: 
  shows "affine_alg_set R n as \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  unfolding affine_alg_set_def 
  by blast 

lemma affine_alg_set_singleton:
"affine_alg_set R n {a} = zero_set R n a"
  unfolding affine_alg_set_def using zero_set_closed  
  by blast

lemma affine_alg_set_insert:
"affine_alg_set R n (insert a A) = zero_set R n a \<inter> (affine_alg_set R n A)"
proof
  show "affine_alg_set R n (insert a A) \<subseteq> V\<^bsub>R\<^esub> n a \<inter> affine_alg_set R n A"
    using affine_alg_set_subset 
    by (metis Int_greatest affine_alg_set_subset_zero_set insertI1 subset_insertI)
  show "V\<^bsub>R\<^esub> n a \<inter> affine_alg_set R n A \<subseteq> affine_alg_set R n (insert a A)"
    unfolding affine_alg_set_def 
    by blast
qed

lemma affine_alg_set_intersect:
"affine_alg_set R n (A \<union> B) = (affine_alg_set R n A) \<inter> (affine_alg_set R n B)"
  unfolding affine_alg_set_def by blast 

lemma affine_alg_set_memI:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "\<And>p. p \<in> B \<Longrightarrow> eval_at_point R a p = \<zero>"
  shows "a \<in> (affine_alg_set R n B)"
  unfolding affine_alg_set_def zero_set_def 
  using assms 
  by blast

lemma affine_alg_set_not_memE:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "a \<notin> (affine_alg_set R n B)"
  shows "\<exists>b \<in> B. eval_at_poly R b a \<noteq> \<zero>"
  using assms affine_alg_set_memI by blast


  (**********************************************************************)
  (**********************************************************************)
  subsubsection\<open>Finite Unions and Intersections of Algebraic Sets are Algebraic\<close>
  (**********************************************************************)
  (**********************************************************************)
text\<open>The product set of two sets in an arbitrary ring. That is, the set $\{ xy \mid x \in A \land y \in B \}$ for two sets $A$, $B$.\<close>
definition(in ring) prod_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"prod_set as bs = (\<lambda>x. fst x \<otimes> snd x) ` (as \<times> bs)"

lemma(in ring) prod_setI:
  assumes "c \<in> prod_set as bs"
  shows "\<exists>a \<in> as. \<exists>b \<in> bs. c = a \<otimes> b"
proof-
  obtain p where p_def: "p \<in> (as \<times> bs) \<and> c = fst p \<otimes> snd p" 
    using assms prod_set_def[of as bs] 
    by (metis (no_types, lifting) image_iff)
  then show ?thesis 
    using mem_Times_iff by blast
qed

lemma(in ring) prod_set_closed:
  assumes "as \<subseteq> carrier R"
  assumes "bs \<subseteq> carrier R"
  shows "prod_set as bs \<subseteq> carrier R"
proof
  fix x
  assume " x \<in> prod_set as bs"
  then obtain a b where "a \<in> as \<and> b \<in> bs \<and> x = a \<otimes> b"
    by (meson ring_axioms ring.prod_setI)
  then have "a \<in> carrier R \<and> b \<in> carrier R \<and> x = a \<otimes> b"
    using assms 
    by blast 
  then show "x \<in> carrier R"
    by blast
qed

text\<open>The set of products of elements from two finite sets is again finite.\<close>
lemma(in ring) prod_set_finite:
  assumes "finite as"
  assumes "finite bs"
  shows "finite (prod_set as bs)" "card (prod_set as bs) \<le> card as * card bs"
proof-
  have "finite (as \<times> bs)"
    using assms 
    by blast
  then show "finite (prod_set as bs)" 
    using  prod_set_def 
    by (metis (no_types, lifting) finite_imageI)
  have "card (prod_set as bs) \<le> card (as \<times> bs)"
    using assms 
    unfolding prod_set_def 
    using \<open>finite (as \<times> bs)\<close> card_image_le by blast
  then show "card (prod_set as bs) \<le> card as * card bs"
    by (simp add: card_cartesian_product)
qed

definition poly_prod_set where
"poly_prod_set n as bs = ring.prod_set (R[\<X>\<^bsub>n\<^esub>]) as bs"

lemma poly_prod_setE:
  assumes "c \<in> poly_prod_set n as bs"
  shows "\<exists>a \<in> as. \<exists>b \<in> bs. c = a \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> b"
  using ring.prod_setI[of "R[\<X>\<^bsub>n\<^esub>]"] R.Pring_is_ring assms poly_prod_set_def coord_cring_cring cring.axioms(1) 
  by blast
  
lemma poly_prod_setI:
  assumes "a \<in> as"
  assumes "b \<in> bs"
  shows "a \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> b \<in> poly_prod_set n as bs"
proof-
  have 0: "(a,b) \<in> (as \<times> bs)"
    using assms by blast 
  have 1: "(\<lambda>x. fst x \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> snd x) (a, b) = a \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> b"
    by (metis fst_conv snd_conv)    
  have 2: "(\<lambda>x. fst x \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> snd x) (a, b) \<in> ((\<lambda>x. fst x \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> snd x) ` (as \<times> bs))"
    using 0  by blast 
  have 3: "ring (R[\<X>\<^bsub>n\<^esub>])"
    by (simp add: R.Pring_is_ring coord_ring_def)    
  then show ?thesis
    unfolding poly_prod_set_def using 0 1 2 3 ring.prod_set_def[of "R[\<X>\<^bsub>n\<^esub>]" as bs]  
    by presburger
qed

lemma poly_prod_set_closed:
  assumes "as \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "bs \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "poly_prod_set n as bs \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
  using ring.prod_set_closed[of "R[\<X>\<^bsub>n\<^esub>]"]  R.Pring_is_ring assms(1) assms(2) poly_prod_set_def 
  by (simp add: coord_cring_cring cring.axioms(1))  

lemma poly_prod_set_finite:
  assumes "finite as"
  assumes "finite bs"
  shows "finite (poly_prod_set n as bs)" "card (poly_prod_set n as bs) \<le> card as * card bs"
 
  using ring.prod_set_finite[of "R[\<X>\<^bsub>n\<^esub>]"]
  apply (simp add: R.Pring_is_ring assms(1) assms(2) poly_prod_set_def)
  using ring.prod_set_finite[of "R[\<X>\<^bsub>n\<^esub>]"]
  apply (simp add: assms(1) assms(2) coord_cring_cring cring.axioms(1))
  by (simp add: assms(1) assms(2) coord_cring_cring cring.axioms(1) poly_prod_set_def ring.prod_set_finite(2))

end 

locale domain_coord_rings = cring_coord_rings + domain

lemma(in domain_coord_rings) poly_prod_set_algebraic_set:
  assumes "as \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "bs \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "affine_alg_set R n as \<union> affine_alg_set R n bs = affine_alg_set R n (poly_prod_set n as bs)"
proof
  show "affine_alg_set R n as \<union> affine_alg_set R n bs \<subseteq> affine_alg_set R n (poly_prod_set n as bs)"
  proof fix x
    assume A: "x \<in> affine_alg_set R n as \<union> affine_alg_set R n bs"
    show "x \<in> affine_alg_set R n (poly_prod_set n as bs)"
    proof(rule affine_alg_set_memI)
      show "x \<in> carrier (R\<^bsup>n\<^esup>)"
        using A affine_alg_set_closed 
        by blast
      show "\<And>p. p \<in> poly_prod_set n as bs \<Longrightarrow> eval_at_poly R p x = \<zero>"
      proof- fix p
        assume B: "p \<in> poly_prod_set n as bs"
        show "eval_at_poly R p x = \<zero>"
        proof-
          obtain p0 p1 where C: "p0 \<in> as \<and> p1 \<in> bs \<and> p = p0 \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> p1"
            using B poly_prod_setE by blast
          then have D: "eval_at_poly R p x = (eval_at_poly R p0 x) \<otimes> (eval_at_poly R p1 x)"
            using \<open>x \<in> carrier (R\<^bsup>n\<^esup>)\<close> assms(1) assms(2) eval_at_point_mult 
            by blast 
          show ?thesis proof(cases "x \<in> affine_alg_set R n as")
            case True
            then have "(eval_at_poly R p0 x) = \<zero>"
              using C  affine_alg_set_memE by blast              
            then show ?thesis 
              by (smt C D \<open>x \<in> carrier (R\<^bsup>n\<^esup>)\<close> assms(2) eval_at_point_closed R.semiring_axioms semiring.l_null subsetD)            
          next
            case False
            then have "x \<in> affine_alg_set R n bs"
              using A 
              by blast
            then have "(eval_at_poly R p1 x) = \<zero>"
              using C affine_alg_set_memE by blast
            then show ?thesis 
              using C A False 
              by (smt D \<open>x \<in> carrier (R\<^bsup>n\<^esup>)\<close> assms(1) eval_at_point_closed R.r_null subsetD)
          qed 
        qed
      qed
    qed
  qed  
  show "affine_alg_set R n (poly_prod_set n as bs) \<subseteq> affine_alg_set R n as \<union> affine_alg_set R n bs"
  proof fix x 
    assume A: "x \<in> affine_alg_set R n (poly_prod_set n as bs)"
    have x_car: "x \<in> carrier (R\<^bsup>n\<^esup>)"
      using A affine_alg_set_closed 
      by blast
    show "x \<in> affine_alg_set R n as \<union> affine_alg_set R n bs"
    proof(cases "x \<in> affine_alg_set R n as")
      case True
      then show ?thesis by blast 
    next
      case False
      have "x \<in> affine_alg_set R n bs"
      proof(rule affine_alg_set_memI)
        show "x \<in> carrier (R\<^bsup>n\<^esup>)"
          using A affine_alg_set_closed by blast
        show "\<And>p. p \<in> bs \<Longrightarrow> eval_at_poly R p x = \<zero>"
        proof-
          fix p assume p_def: "p \<in> bs"
          obtain a where a_def: "a \<in> as \<and> eval_at_poly R a x \<noteq> \<zero>"
            using False affine_alg_set_not_memE  \<open>x \<in> carrier (R\<^bsup>n\<^esup>)\<close> 
            by blast
          then have "a \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> p \<in> (poly_prod_set n as bs)"
            using poly_prod_setI[of a as p bs] p_def 
            by blast
          then have "eval_at_poly R (a \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> p) x = \<zero>"
            using A affine_alg_set_memE 
            by blast
         
          then have "eval_at_poly R a x \<otimes> eval_at_poly R p  x = \<zero>"
            using eval_at_point_mult[of x n a p]
            by (metis (no_types, lifting) \<open>x \<in> carrier (R\<^bsup>n\<^esup>)\<close> a_def assms(1) assms(2) p_def subsetD)
          then show "eval_at_poly R p  x  = \<zero>"
            using a_def p_def 
            by (meson assms(1) assms(2) eval_at_point_closed integral_iff subsetD x_car)            
        qed
      qed
      then show ?thesis 
        by blast
    qed
  qed
qed
      
definition is_algebraic :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow> bool" where
"is_algebraic R n S = (\<exists>ps. finite ps \<and> ps \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>]) \<and> S = affine_alg_set R n ps)"

context cring_coord_rings
begin 

lemma is_algebraicE:
  assumes "is_algebraic R n S"
  obtains ps where  "finite ps" "ps \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])" "S = affine_alg_set R n ps"
  using assms 
  by (meson is_algebraic_def)

lemma is_algebraicI:
  assumes "finite ps"
  assumes "ps \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "S = affine_alg_set R n ps"
  shows "is_algebraic R n S"
  using is_algebraic_def assms 
  by blast

lemma is_algebraicI':
  assumes "p \<in>  carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "S = zero_set R n p"
  shows "is_algebraic R n S"
  by (metis affine_alg_set_singleton assms(1) assms(2) empty_subsetI finite.emptyI finite.intros(2) insert_subset is_algebraic_def)

end

definition alg_sets :: "arity \<Rightarrow> ('a, 'b) ring_scheme \<Rightarrow> ('a list set) set" where
"alg_sets n R = {S. is_algebraic R n S}"

context cring_coord_rings
begin 

lemma intersection_is_alg:
  assumes "is_algebraic R n A"
  assumes "is_algebraic R n B"
  shows "is_algebraic R n (A \<inter> B)"
proof-
  obtain as where as_def: "finite as \<and> as \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>]) \<and> A = affine_alg_set R n as"
    by (meson assms(1) is_algebraicE)
  obtain bs where bs_def: "finite bs \<and> bs \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>]) \<and> B = affine_alg_set R n bs"
    by (meson assms(2) is_algebraicE)
  show ?thesis apply(rule is_algebraicI[of "as \<union> bs"])
    using as_def bs_def apply blast
    using as_def bs_def apply blast
    by (simp add: affine_alg_set_intersect as_def bs_def)
qed

lemma(in domain_coord_rings) union_is_alg:
  assumes "is_algebraic R n A"
  assumes "is_algebraic R n B"
  shows "is_algebraic R n (A \<union> B)"
proof-
  obtain as where as_def: "finite as \<and> as \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>]) \<and> A = affine_alg_set R n as"
    by (meson assms(1) is_algebraicE)
  obtain bs where bs_def: "finite bs \<and> bs \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>]) \<and> B = affine_alg_set R n bs"
    by (meson assms(2) is_algebraicE)
  show ?thesis apply(rule is_algebraicI[of "poly_prod_set n as bs"])
    using as_def bs_def 
    apply (simp add: poly_prod_set_finite(1))
    using as_def bs_def poly_prod_set_closed apply blast
        using as_def bs_def poly_prod_set_algebraic_set 
        by simp
qed

lemma zero_set_zero:
"zero_set R n \<zero>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> = carrier (R\<^bsup>n\<^esup>)"
  by (metis R.add.r_cancel_one cring.cring_simprules(2) cring.cring_simprules(8) 
      coord_cring_cring cring_coord_rings.eval_at_point_add cring_coord_rings.eval_at_point_closed 
      cring_coord_rings_axioms subsetI subset_antisym zero_setI zero_set_closed)
  
lemma affine_alg_set_set:
"affine_alg_set  R n {\<zero>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>} = carrier (R\<^bsup>n\<^esup>)"
using affine_alg_set_singleton zero_set_zero 
by blast

lemma car_is_alg:
"is_algebraic R n (carrier (R\<^bsup>n\<^esup>))"
  apply(rule is_algebraicI[of "{\<zero>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>}"])
  apply blast
  using R.Pring_zero_closed  
   apply blast
    using affine_alg_set_set by blast

lemma zero_set_nonzero_constant:
  assumes "a \<noteq> \<zero>"
  assumes "a \<in> carrier R"
  shows "zero_set R n (coord_const a) = {}"
proof(rule ccontr)
  assume "V n (coord_const a) \<noteq> {}"
  then obtain x where "x \<in> V n (coord_const a)"
    by blast 
  then show False
    by (metis assms(1) assms(2) cring_coord_rings.eval_at_point_const cring_coord_rings.zero_setE(1) cring_coord_rings.zero_setE(2) cring_coord_rings_axioms)    
qed  

lemma zero_set_one:
  assumes "a \<noteq> \<zero>"
  assumes "a \<in> carrier R"
  shows "zero_set R n \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> = {}"
  using zero_set_nonzero_constant
  by (metis R.Pring_one coord_ring_def one_neq_zero R.one_closed)  

lemma empty_set_as_affine_alg_set:
"affine_alg_set  R n {\<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>} = {}"
  using affine_alg_set_singleton local.one_neq_zero zero_set_one by blast

lemma empty_is_alg:
"is_algebraic R n {}"
  apply(rule is_algebraicI'[of "\<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>"])
  apply blast  
  using local.one_neq_zero zero_set_one by blast
  

  (**********************************************************************)
  (**********************************************************************)
  subsubsection\<open>Finite Sets Are Algebraic\<close>
  (**********************************************************************)
  (**********************************************************************)
text\<open>the function mapping a point in $R^n$ to the unique linear polynomial vanishing exclusively at that point\<close>

definition pvar_trans ::  "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a, nat) mvar_poly" where
"pvar_trans n i a = (pvar R i) \<ominus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> coord_const a"

lemma pvar_trans_closed:
  assumes "a \<in> carrier R"
  assumes "i < n"
  shows "pvar_trans n i a \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  unfolding pvar_trans_def using assms 
  by (metis MP.minus_closed coord_ring_def R.indexed_const_closed local.pvar_closed)
  
lemma pvar_trans_eval:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "i < n"
  shows "eval_at_point R b (pvar_trans n i a) = (b!i) \<ominus> a"
proof-
  have "eval_at_point R b (pvar_trans n i a) = 
        (eval_at_point R b (pvar R i)) \<oplus> (eval_at_point R b (\<ominus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (coord_const a)))"
  unfolding pvar_trans_def a_minus_def using assms 
  by (metis MP.add.inv_closed coord_ring_def eval_at_point_add R.indexed_const_closed local.pvar_closed)
 
  then show ?thesis
    by (metis a_minus_def assms(1) assms(2) assms(3) coord_ring_def eval_at_point_a_inv eval_at_point_const eval_pvar R.indexed_const_closed)
qed
  
definition point_to_polys :: "'a list \<Rightarrow> ('a, nat) mvar_poly list" where
"point_to_polys as = map (\<lambda> x. pvar_trans (length as) (snd x) (fst x)) (zip as (index_list (length as)))"

lemma point_to_polys_length: 
"length (point_to_polys as) = length as"
  unfolding point_to_polys_def 
  by (smt index_list_length length_map list.map_ident map_eq_imp_length_eq zip_eq_conv)
  
lemma point_to_polysE: 
  assumes "i < length as"
  shows "(point_to_polys as) ! i = (pvar_trans (length as) i (as ! i))"
proof- 
  have " (zip as (index_list (length as)))!i =  ((as!i), i)"
    by (metis assms index_list_indices index_list_length nth_zip)    
  then  have 0: "(point_to_polys as) ! i = (\<lambda> x. pvar_trans (length as) (snd x) (fst x)) ((as!i), i)"
    unfolding point_to_polys_def
    using  assms nth_map[of i "(zip as (index_list (length as)))" "(\<lambda>x. pvar_trans (length as) (snd x) (fst x))" ]
    by (metis index_list_length length_map map_fst_zip)
  then show ?thesis 
    by (metis fst_conv snd_conv)
qed

lemma point_to_polysE': 
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "i < n"
  shows "eval_at_point R as ((point_to_polys as) ! i) = \<zero>"
  by (metis assms(1) assms(2) cartesian_power_car_memE cartesian_power_car_memE' point_to_polysE pvar_trans_eval R.r_right_minus_eq)

lemma point_to_polysE'': 
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "b \<in> set (point_to_polys as)"
  shows "eval_at_point R as b = \<zero>"
  using point_to_polysE' 
  by (metis assms(1) assms(2) cartesian_power_car_memE in_set_conv_nth point_to_polys_length)

lemma point_to_polys_zero_set: 
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "b \<in> set (point_to_polys as)"
  shows "as \<in> zero_set R n b"
  using assms(1) assms(2) point_to_polysE'' zero_setI by blast

lemma point_to_polys_closed:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "set (point_to_polys as) \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>])"
  using assms point_to_polysE pvar_trans_closed 
  by (smt cartesian_power_car_memE cartesian_power_car_memE' in_set_conv_nth point_to_polys_length subsetI)  

lemma point_to_polys_affine_alg_set:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "affine_alg_set R n (set (point_to_polys as)) = {as}"
proof
  show "affine_alg_set R n (set (point_to_polys as)) \<subseteq> {as}"
  proof
    fix x
    assume A0: "x \<in> affine_alg_set R n (set (point_to_polys as))"
    then have 0: "length x = n" using affine_alg_set_closed[of  n " (set (point_to_polys as))"]
      using cartesian_power_car_memE by blast
    have "\<And>i. i < n \<Longrightarrow> x!i = as!i"
    proof-
      fix i
      assume A1: "i < n"
      show " x!i = as!i"
        using A0 
        by (smt A1 affine_alg_set_closed affine_alg_set_memE assms cartesian_power_car_memE 
            cartesian_power_car_memE' nth_mem point_to_polysE point_to_polys_length
            pvar_trans_eval R.r_right_minus_eq subsetD)
    qed
    then have "x = as"
      by (metis "0" assms cartesian_power_car_memE nth_equalityI)
    then show "x \<in> {as}"
      by blast
  qed
  show "{as} \<subseteq> affine_alg_set R n (set (point_to_polys as))"
  proof-
    have "as \<in>  affine_alg_set R n (set (point_to_polys as))"
      using affine_alg_set_not_memE assms point_to_polysE'' 
      by blast
    then show ?thesis 
      by blast
  qed
qed

lemma singleton_is_algebraic:
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "is_algebraic R n {as}"
  apply(rule is_algebraicI[of "(set (point_to_polys as))"])
  apply blast
  using point_to_polys_affine_alg_set
  using assms point_to_polys_closed apply blast
  by (simp add: assms point_to_polys_affine_alg_set)

lemma(in domain_coord_rings) finite_sets_are_algebraic:
  assumes "finite F"
  shows "F \<subseteq> carrier (R\<^bsup>n\<^esup>) \<longrightarrow> is_algebraic R n F"
  apply(rule finite.induct) 
  apply (simp add: assms) 
  using empty_is_alg apply blast
  using singleton_is_algebraic 
  by (metis union_is_alg insert_is_Un insert_subset)


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Polynomial Maps\<close>
(**************************************************************************************************)
(**************************************************************************************************)

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>The Action of Index Permutations on Polynomials\<close>
  (**********************************************************************)
  (**********************************************************************)

definition permute_poly_args :: 
  "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> ('a, nat) mvar_poly \<Rightarrow> ('a, nat) mvar_poly" where
"permute_poly_args (n::nat) \<sigma> p = indexed_poly_induced_morphism {..<n} (R[\<X>\<^bsub>n\<^esub>]) coord_const (\<lambda>i. pvar R (\<sigma> i)) p" 

lemma permute_poly_args_characterization:
  assumes "\<sigma> permutes {..< n}"
  shows "(ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>n\<^esub>]) (permute_poly_args (n::nat) \<sigma>))"
        "(\<forall>i \<in> {..<n}. (permute_poly_args (n::nat) \<sigma>) (pvar R i) =  pvar R (\<sigma> i))"
        "(\<forall>a \<in> carrier R. permute_poly_args (n::nat) \<sigma> (coord_const a) = (coord_const a))"
proof-
  have 0: "cring (R[\<X>\<^bsub>n\<^esub>])"
    by (simp add: MP.is_cring)
  have 1: "(\<lambda>i. pvar R (\<sigma> i)) \<in> {..<n} \<rightarrow> carrier (R[\<X>\<^bsub>n\<^esub>])"
  proof
    fix x
    assume A: "x \<in> {..<n}"
    then have 0: "\<sigma> x \<in> {..<n}"
      using assms 
      by (meson permutes_in_image)
    then have "\<sigma> x < n"
      using assms 
      by auto
    then  show "pvar R (\<sigma> x) \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) "
      using  pvar_closed[of "\<sigma> x" n]
      by blast
  qed
  have 2: " ring_hom_ring R (R[\<X>\<^bsub>n\<^esub>]) coord_const"
    using R.indexed_const_ring_hom unfolding coord_ring_def 
    by blast    
  have 3: "  indexed_poly_induced_morphism {..<n} (R[\<X>\<^bsub>n\<^esub>]) coord_const (\<lambda>i. pvar R (\<sigma> i)) =
    indexed_poly_induced_morphism {..<n} (R[\<X>\<^bsub>n\<^esub>]) coord_const (\<lambda>i. pvar R (\<sigma> i))"
    by blast   
  show "ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>n\<^esub>]) (permute_poly_args n \<sigma>)"
    using 0 1 2 3
        R.Pring_universal_prop[of "(R[\<X>\<^bsub>n\<^esub>])" " (\<lambda>i. pvar R (\<sigma> i))" "{..<n}" coord_const "permute_poly_args (n::nat) \<sigma>" ]
    unfolding permute_poly_args_def 
    by (metis coord_ring_def)  
  show "\<forall>i\<in>{..<n}. permute_poly_args n \<sigma> (pvar R i) = pvar R (\<sigma> i)"
    using 0 1 2 3
        R.Pring_universal_prop(2)[of "(R[\<X>\<^bsub>n\<^esub>])" " (\<lambda>i. pvar R (\<sigma> i))" "{..<n}" coord_const "permute_poly_args (n::nat) \<sigma>" ]
    unfolding permute_poly_args_def var_to_IP_def
    by blast
  show "\<forall>a\<in>carrier R. permute_poly_args n \<sigma> (coord_const a) = coord_const a"
    using 0 1 2 3 
        R.Pring_universal_prop[of "(R[\<X>\<^bsub>n\<^esub>])" " (\<lambda>i. pvar R (\<sigma> i))" "{..<n}" coord_const "permute_poly_args (n::nat) \<sigma>" ]
    unfolding permute_poly_args_def var_to_IP_def
    by blast 
qed

lemma permute_poly_args_closed:
  assumes "\<sigma> permutes {..<n}"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "permute_poly_args n \<sigma> p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
proof-
  have "(ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>n\<^esub>]) (permute_poly_args (n::nat) \<sigma>))"
    using assms permute_poly_args_characterization(1) 
    by blast
  then have "(permute_poly_args (n::nat) \<sigma>) \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<rightarrow> carrier (R[\<X>\<^bsub>n\<^esub>])"
    unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def
    by blast
  then show ?thesis
    using assms  
    by blast
qed


lemma permute_poly_args_constant:
  assumes "a \<in> carrier R"
  assumes "\<sigma> permutes {..<n}"
  shows "permute_poly_args n \<sigma> (coord_const a) = (coord_const a)"
  using assms permute_poly_args_characterization(3) 
  by blast

lemma permute_poly_args_add:
  assumes "\<sigma> permutes {..<n}"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "permute_poly_args n \<sigma> (p \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> q) = (permute_poly_args n \<sigma> p) \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (permute_poly_args n \<sigma> q)"
  using permute_poly_args_characterization(1)[of  \<sigma>] assms
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def
  by (metis (no_types, lifting) ring_hom_add)
  
lemma permute_poly_args_mult:
  assumes "\<sigma> permutes {..<n}"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "permute_poly_args n \<sigma> (p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> q) = (permute_poly_args n \<sigma> p) \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (permute_poly_args n \<sigma> q)"
  using permute_poly_args_characterization(1)[of  \<sigma>] assms
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def
  using ring_hom_mult 
  by (metis (mono_tags, lifting))
  
lemma permute_poly_args_indexed_pmult:
  assumes "\<sigma> permutes {..<n}"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "i \<in> {..<n}"
  shows "(permute_poly_args n \<sigma> (p \<Otimes> i)) = (permute_poly_args n \<sigma> p) \<Otimes> (\<sigma> i)"
proof
  fix x
  show "permute_poly_args n \<sigma> (p \<Otimes> i) x = (permute_poly_args n \<sigma> p \<Otimes> \<sigma> i) x"
  proof-
    have 0: "(p \<Otimes> i) = (p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i)"
      using assms  pvar_indexed_pmult 
      by blast
    have 1: "(permute_poly_args n \<sigma> p) \<Otimes> (\<sigma> i) = (permute_poly_args n \<sigma> p) \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R (\<sigma> i)"
      using assms permute_poly_args_closed pvar_indexed_pmult by blast
    have 2: "permute_poly_args n \<sigma> (p \<Otimes> i) x = permute_poly_args n \<sigma> (p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i) x"
      using \<open>p \<Otimes> i = p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i\<close> by presburger
    then show ?thesis using 1 R.Pring_var_closed assms(1) assms(2) assms(3) assms 
          permute_poly_args_mult R.is_cring permute_poly_args_characterization(2) R.zero_closed
      by (metis coord_ring_def)
  qed
qed

lemma permute_list_closed:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "\<sigma> permutes {..<n}"
  shows "(permute_list \<sigma> a)  \<in> carrier (R\<^bsup>n\<^esup>)"
  apply(rule cartesian_power_car_memI)
  using assms cartesian_power_car_memE length_permute_list apply blast
proof-
  have 0: "set a \<subseteq> carrier R"
    using assms(1) cartesian_power_car_memE'' by blast
  have "\<sigma> permutes {..<length a}"
  proof-
    have 0: "length a = n"
      using assms cartesian_power_car_memE by blast
    have "{..<n} = {..<length a}"
      using 0 by blast  
    then show ?thesis 
      using assms by presburger
  qed
  have  1: "set (permute_list \<sigma> a) = set a"
    using assms set_permute_list[of \<sigma> a] \<open>\<sigma> permutes {..<length a}\<close>
    by blast
  then show "set (permute_list \<sigma> a) \<subseteq> carrier R" 
    by (simp add: "1" "0")
qed

lemma permute_list_set:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "\<sigma> permutes {..<n}"
  shows "set (permute_list \<sigma> a) = set a"
proof-
  have "\<sigma> permutes {..<length a}"
  proof-
    have 0: "length a = n"
      using assms cartesian_power_car_memE by blast
    have "{..<n} = {..<length a}"
      using 0 by blast 
    then show ?thesis 
      using assms by presburger
  qed
  then show  1: "set (permute_list \<sigma> a) = set a"
    using assms set_permute_list[of \<sigma> a] 
    by blast
qed  

end 

definition perm_map :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"perm_map R n \<sigma> = restrict (permute_list \<sigma>) (carrier (R\<^bsup>n\<^esup>))"

context cring_coord_rings
begin

lemma perm_map_is_struct_map:
  assumes "\<sigma> permutes {..<n}"
  shows "perm_map R n \<sigma> \<in> struct_maps (R\<^bsup>n\<^esup>) (R\<^bsup>n\<^esup>)"
  apply(rule struct_maps_memI)
  unfolding perm_map_def restrict_def using assms permute_list_closed[of _ n \<sigma>] 
   apply metis 
  by metis 

lemma permute_poly_args_eval:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "\<sigma> permutes {..<n}"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "eval_at_point R a (permute_poly_args n \<sigma> p) = eval_at_point R (permute_list \<sigma> a) p"
  apply(rule R.indexed_pset.induct[of p "{..<n}" "carrier R"])
  using R.Pring_car assms  apply (metis coord_ring_def)
   apply (metis assms(1) assms(2) eval_at_point_const permute_list_closed permute_poly_args_constant)
proof-
  show "\<And>p Q. p \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_point R a (permute_poly_args n \<sigma> p) = eval_at_point R (permute_list \<sigma> a) p \<Longrightarrow>
           Q \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_point R a (permute_poly_args n \<sigma> Q) = eval_at_point R (permute_list \<sigma> a) Q \<Longrightarrow>
           eval_at_point R a (permute_poly_args n \<sigma> (p \<Oplus> Q)) = eval_at_point R (permute_list \<sigma> a) (p \<Oplus> Q)"
  proof-
    fix p Q assume  A0: "p \<in> Pring_set R {..<n} "
    assume A1: "eval_at_point R a (permute_poly_args n \<sigma> p) = eval_at_point R (permute_list \<sigma> a) p "
    assume A2: "Q \<in> Pring_set R {..<n}"
    assume A3: "eval_at_point R a (permute_poly_args n \<sigma> Q) = eval_at_point R (permute_list \<sigma> a) Q"
    have A0': "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) "
      using A0 R.Pring_car unfolding coord_ring_def  by blast
    have A2': "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) "
      using A2 R.Pring_car unfolding coord_ring_def by blast
    have A4: "(permute_poly_args n \<sigma> (p \<Oplus> Q)) = (permute_poly_args n \<sigma> p) \<Oplus> (permute_poly_args n \<sigma> Q)"
    proof-
      have  "(permute_poly_args n \<sigma> (p \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q)) = (permute_poly_args n \<sigma> p) \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (permute_poly_args n \<sigma> Q)"
        using A0' A2' assms permute_poly_args_add by blast
      then show ?thesis 
        unfolding coord_ring_def 
        by (metis R.Pring_add)        
    qed    
    show A5: "eval_at_point R a (permute_poly_args n \<sigma> (p \<Oplus> Q)) = eval_at_point R (permute_list \<sigma> a) (p \<Oplus> Q)"
      using eval_at_point_add[of a n "permute_poly_args n \<sigma> p" "permute_poly_args n \<sigma> Q" ]
            permute_poly_args_add[of \<sigma> n p Q] A0' A1 A2' A3 A4 permute_poly_args_closed assms 
      by (metis R.Pring_add cartesian_power_car_memE cartesian_power_car_memE'' 
          cartesian_power_car_memI coord_ring_def eval_at_point_add length_permute_list permute_list_set)  
  qed
  show "\<And>p i. p \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_point R a (permute_poly_args n \<sigma> p) = eval_at_point R (permute_list \<sigma> a) p \<Longrightarrow>
           i \<in> {..<n} \<Longrightarrow> eval_at_point R a (permute_poly_args n \<sigma> (p \<Otimes> i)) = eval_at_point R (permute_list \<sigma> a) (p \<Otimes> i)"
  proof-
    fix p i
    assume A0: "p \<in> Pring_set R {..<n}"
    assume A1: "eval_at_point R a (permute_poly_args n \<sigma> p) = eval_at_point R (permute_list \<sigma> a) p "
    assume A2: "i \<in> {..<n}"
    have LHS:  "eval_at_point R a (permute_poly_args n \<sigma> (p \<Otimes> i)) = eval_at_point R a (permute_poly_args n \<sigma> p \<Otimes> \<sigma> i)"
      using permute_poly_args_indexed_pmult[of \<sigma> n p i ] A0 A1 A2 assms 
      by (metis R.Pring_car coord_ring_def)      
    then have LHS' : "eval_at_point R a (permute_poly_args n \<sigma> (p \<Otimes> i)) =
                 eval_at_point R a (permute_poly_args n \<sigma> p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R (\<sigma> i))"
      using A0 R.Pring_car assms(1) assms  permute_poly_args_closed pvar_indexed_pmult
      by (metis coord_ring_def)
    have "eval_at_point R a (permute_poly_args n \<sigma> p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R (\<sigma> i)) =
          eval_at_point R a (permute_poly_args n \<sigma>  p) \<otimes> eval_at_point R a (pvar R (\<sigma> i))"
    proof-
      have 1: "permute_poly_args n \<sigma> p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
        using A0 R.Pring_car assms(1) assms  permute_poly_args_closed 
        by (metis coord_ring_def)        
      have "pvar R (\<sigma> i) \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
      proof-
        have "\<sigma> i \<in> {..<n}"
          using A2 assms 
          by (meson permutes_in_image)
        then have "(\<sigma> i) < n"
           by blast 
         then show ?thesis 
           using pvar_closed[of "\<sigma> i" n]   
          by blast
      qed
      then have LHS'' : "eval_at_point R a (permute_poly_args n \<sigma> (p \<Otimes> i)) =
                 (eval_at_point R a (permute_poly_args n \<sigma>  p)) \<otimes>\<^bsub>R\<^esub> eval_at_point R a (pvar R (\<sigma> i))"
        using LHS' "1" eval_at_point_mult assms 
        by presburger       
      then show ?thesis  
        using LHS' by presburger
    qed
    then have LHS'': "eval_at_point R a (permute_poly_args n \<sigma> (p \<Otimes> i)) =
        eval_at_point R a (permute_poly_args n \<sigma>  p) \<otimes> eval_at_point R a (pvar R (\<sigma> i))"
      using LHS' by presburger
    have 0: "eval_at_point R a (pvar R (\<sigma> i)) = a! (\<sigma> i)"
    proof-
      have "\<sigma> i \<in> {..<n}" 
      using A2 assms 
      by (meson permutes_in_image)
      then have 0: "\<sigma> i < n" 
        by blast 
     have 1: "permute_list \<sigma> a \<in> carrier (R\<^bsup>n\<^esup>)"
      using assms(1) assms(2) assms(3) permute_list_closed by blast
     show ?thesis 
      using 0 1 eval_pvar[of "\<sigma> i" n a] assms  
      by blast
    qed
    have 1: "(permute_list \<sigma> a)! i  = a! \<sigma>  i"
    proof-
      have "length a = n"
        using assms  cartesian_power_car_memE
        by blast
      then have "{..<length a} = {..<n}"
        by blast
      then have 0: " \<sigma> permutes {..<length a}" 
        using assms 
        by presburger
      have 1: "i < length a"
        using A2 \<open>{..<length a} = {..<n}\<close> 
        by blast
      show ?thesis using 0 1  permute_list_nth[of \<sigma> a i]
        by blast
    qed
    have LHS''': "eval_at_point R a (permute_poly_args n \<sigma> (p \<Otimes> i)) =
        eval_at_point R (permute_list \<sigma> a) p \<otimes> a! (\<sigma> i)"
      using 0 LHS''  A1 
      by presburger
    have RHS: "eval_at_point R (permute_list \<sigma> a) (p \<Otimes> i) = 
        (eval_at_point R (permute_list \<sigma> a) p) \<otimes>\<^bsub>R\<^esub> (eval_at_point R (permute_list \<sigma> a) (pvar R i))"
    proof-
      have "(p \<Otimes> i) = p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar R i)"
        using A0 R.Pring_car pvar_indexed_pmult unfolding coord_ring_def 
        by blast        
      then show ?thesis 
        using eval_at_point_mult[of "(permute_list \<sigma> a)" n p "(pvar R i)" ] 
             A0 A2 R.Pring_car R.Pring_var_closed assms(1) assms(2) assms(3) permute_list_closed
        by (metis coord_ring_def)
    qed
    then have RHS': "eval_at_point R (permute_list \<sigma> a) (p \<Otimes> i) = 
        (eval_at_point R (permute_list \<sigma> a) p) \<otimes>\<^bsub>R\<^esub> (permute_list \<sigma> a)! i"
    proof-
      have 0: "i < n" 
        using A2 assms 
        by blast 
      have 1: "permute_list \<sigma> a \<in> carrier (R\<^bsup>n\<^esup>)"
        using assms permute_list_closed 
        by blast
      show ?thesis 
        using 0 1 eval_pvar[of i n "(permute_list \<sigma> a)" ] RHS 
        by presburger
    qed
    then show "eval_at_point R a (permute_poly_args n \<sigma> (p \<Otimes> i)) = eval_at_point R (permute_list \<sigma> a) (p \<Otimes> i)"
      using LHS''' A1 1 
      by presburger
  qed
qed

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Inverse Images of Sets by Tuples of Polynomials\<close>
  (**********************************************************************)
  (**********************************************************************)

definition is_poly_tuple :: "nat \<Rightarrow> ('a, nat) mvar_poly list \<Rightarrow> bool" where
"is_poly_tuple (n::nat) fs = (set (fs) \<subseteq> carrier (R[\<X>\<^bsub>n\<^esub>]))"

lemma is_poly_tupleE:
  assumes "is_poly_tuple n fs"
  assumes "j < length fs"
  shows "fs ! j \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  using assms is_poly_tuple_def nth_mem 
  by blast

lemma is_poly_tuple_Cons:
  assumes "is_poly_tuple n fs"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "is_poly_tuple n (f#fs)"
  using assms unfolding is_poly_tuple_def 
  by (metis (no_types, lifting) set_ConsD subset_iff)

lemma is_poly_tuple_append:
  assumes "is_poly_tuple n fs"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "is_poly_tuple n (fs@[f])"
  using assms set_append unfolding is_poly_tuple_def 
  by (metis (no_types, lifting) Un_subset_iff append_Nil2 set_ConsD subset_code(1))

definition poly_tuple_eval :: "('a, nat) mvar_poly list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"poly_tuple_eval fs as = map (\<lambda> f. eval_at_poly R f as) fs "

lemma poly_tuple_evalE:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "j < m"
  shows "(poly_tuple_eval fs as)!j \<in> carrier R"
proof-
  have 0: "(poly_tuple_eval fs as)!j = (eval_at_poly R (fs!j) as)"
    using poly_tuple_eval_def 
    by (metis assms(2) assms(4) nth_map)   
  have 1: "(fs!j) \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    using assms is_poly_tupleE
    by blast
  show ?thesis 
    using assms 0 1 eval_at_point_closed 
    by presburger   
qed

lemma poly_tuple_evalE':
  shows "length (poly_tuple_eval fs as) = length fs"
  unfolding poly_tuple_eval_def 
  using length_map by blast

lemma poly_tuple_evalE'':
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "j < m"
  shows "(poly_tuple_eval fs as)!j = (eval_at_poly R (fs!j) as)"
  using assms 
  unfolding poly_tuple_eval_def 
  using nth_map
  by blast

lemma poly_tuple_eval_closed:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "(poly_tuple_eval fs as) \<in> carrier (R\<^bsup>m\<^esup>)"
proof(rule cartesian_power_car_memI)
  show "length (poly_tuple_eval fs as) = m"
    using assms 
    by (simp add: assms poly_tuple_evalE')
  show "set (poly_tuple_eval fs as) \<subseteq> carrier R"
  proof fix x
    assume "x \<in> set (poly_tuple_eval fs as)"
    then obtain j where j_def: "j< m \<and> x = (poly_tuple_eval fs as)!j"
      using assms 
      by (metis \<open>length (poly_tuple_eval fs as) = m\<close> in_set_conv_nth)
    then show "x \<in> carrier R"
      using assms(1) assms(2) assms(3)  poly_tuple_evalE assms by blast       
  qed
qed

lemma poly_tuple_eval_Cons:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "(poly_tuple_eval (f#fs) as) = (eval_at_point R as f)#(poly_tuple_eval fs as)"
  using assms poly_tuple_eval_def 
  by (metis list.simps(9))

definition poly_tuple_pullback :: 
   "nat \<Rightarrow> 'a list set \<Rightarrow> ('a, nat) mvar_poly list \<Rightarrow> 'a list set" where
"poly_tuple_pullback n S fs = ((poly_tuple_eval fs) -` S) \<inter> (carrier (R\<^bsup>n\<^esup>)) "

lemma poly_pullbackE: 
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "S \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  shows "poly_tuple_pullback n S fs \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  using poly_tuple_pullback_def assms  
  by blast
  
lemma poly_pullbackE': 
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "S \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "as \<in> poly_tuple_pullback n S fs"
  shows "as \<in> carrier (R\<^bsup>n\<^esup>)"
        "poly_tuple_eval fs as \<in> S"
  using assms 
  apply (meson poly_pullbackE subsetD)
proof-
  have "as \<in> poly_tuple_eval fs -` S" 
    using assms unfolding poly_tuple_pullback_def
    by blast
  then show "poly_tuple_eval fs as \<in> S" 
    by blast
qed

lemma poly_pullbackI: 
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "S \<subseteq> carrier (R\<^bsup>m\<^esup>)"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "poly_tuple_eval fs as \<in> S"
  shows "as \<in> poly_tuple_pullback n S fs"
  using assms 
  unfolding poly_tuple_pullback_def 
  by blast



end 

text\<open>coordinate permutations as pullbacks. The point here is to realize that permutations of 
indices are just pullbacks (or pushforwards) by particular polynomial maps\<close>

abbreviation pvar_list where 
"pvar_list R n \<equiv> map (pvar R) (index_list n)"

lemma pvar_list_elements:
  assumes "i < n"
  shows "pvar_list R n ! i = pvar R i"
  by (simp add: assms index_list_indices index_list_length)
  
lemma pvar_list_length:
"length (pvar_list R n) = n"
  by (simp add: index_list_length)

context cring_coord_rings
begin

lemma pvar_list_is_poly_tuple:
  shows "is_poly_tuple n (pvar_list R n)"
  unfolding is_poly_tuple_def 
proof fix x
  assume A: "x \<in> set (pvar_list R n)"
  have "set (index_list n) = {..<n}"
    by (simp add: index_list_set)
  obtain i where "i < n \<and> x = pvar R i"
    using A  pvar_list_elements[of _ n R] pvar_list_length[of R n] 
    by (metis in_set_conv_nth)
  then show "x \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    using pvar_closed 
    by blast
qed

lemma permutation_of_poly_list_is_poly_list:
  assumes "is_poly_tuple k fs"
  assumes "\<sigma> permutes {..< length fs}"
  shows "is_poly_tuple k (permute_list \<sigma> fs)"
  unfolding is_poly_tuple_def 
proof-
  show "set (permute_list \<sigma> fs) \<subseteq> carrier (coord_ring R k)"
    using assms is_poly_tuple_def set_permute_list 
    by blast
qed

lemma permutation_of_poly_listE:
  assumes "is_poly_tuple k fs"
  assumes "\<sigma> permutes {..< length fs}"
  assumes "i < length fs"
  shows "(permute_list \<sigma> fs) ! i = fs ! (\<sigma> i)"
  using assms permute_list_nth 
  by blast

lemma pushforward_by_permutation_of_poly_list:
  assumes "is_poly_tuple k fs"
  assumes "\<sigma> permutes {..< length fs}"
  assumes "as \<in> carrier (R\<^bsup>k\<^esup>)"
  shows "poly_tuple_eval (permute_list \<sigma> fs) as = permute_list \<sigma> (poly_tuple_eval fs as)"
  using assms unfolding poly_tuple_eval_def 
  by (metis permute_list_map)

lemma pushforward_by_pvar_list:
  assumes "as \<in>  carrier (R\<^bsup>n\<^esup>)"
  shows "poly_tuple_eval (pvar_list R n) as = as"
  using assms pvar_list_elements[of _ n R] unfolding poly_tuple_eval_def using eval_pvar[of _ n as]
  by (metis (mono_tags, lifting) cartesian_power_car_memE length_map nth_equalityI nth_map pvar_list_length)

lemma pushforward_by_permuted_pvar_list:
  assumes "\<sigma> permutes {..< n}"
  assumes "as \<in>  carrier (R\<^bsup>n\<^esup>)"
  shows "poly_tuple_eval (permute_list \<sigma> (pvar_list R n)) as = permute_list \<sigma> as"
  by (metis assms pushforward_by_permutation_of_poly_list 
      pushforward_by_pvar_list pvar_list_is_poly_tuple pvar_list_length)

lemma pullback_by_permutation_of_poly_list:
  assumes "\<sigma> permutes {..< n}"
  assumes "S \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_tuple_pullback n S (permute_list \<sigma> (pvar_list R n)) = 
          permute_list (fun_inv \<sigma>) ` S"
proof
   show "poly_tuple_pullback n S (permute_list \<sigma> (pvar_list R n)) \<subseteq> permute_list (fun_inv \<sigma>) ` S"
   proof fix x
     assume A: " x \<in> poly_tuple_pullback n S (permute_list \<sigma> (pvar_list R n))"
     then obtain y where y_def: "y \<in> S \<and> poly_tuple_eval (permute_list \<sigma> (pvar_list R n)) x = y"
       by (metis assms length_permute_list 
           permutation_of_poly_list_is_poly_list poly_pullbackE'(2) pvar_list_is_poly_tuple 
           pvar_list_length)
     then have 0: "y = permute_list \<sigma> x"
       by (metis A assms length_permute_list 
           permutation_of_poly_list_is_poly_list poly_pullbackE'(1) pushforward_by_permuted_pvar_list pvar_list_is_poly_tuple pvar_list_length)
     have 1: "length x = n"
       using A 
       by (metis "0" length_permute_list poly_tuple_evalE' pvar_list_length y_def)
     then have "{..<length x} = {..<n}"
       by blast 
     then have "permute_list (fun_inv \<sigma>) y = x"
       using 0 permutes_inv_o(1)[of \<sigma> "{..< n}"] permute_list_id[of x] permutes_inv[of \<sigma> "{..<n}"]
            assms permute_list_compose[of "(fun_inv \<sigma>)" x \<sigma> ]
       unfolding fun_inv_def 
       by metis 
     then show " x \<in> permute_list (fun_inv \<sigma>) ` S"
       using y_def by blast
   qed
   show "permute_list (fun_inv \<sigma>) ` S \<subseteq> poly_tuple_pullback n S (permute_list \<sigma> (pvar_list R n))"
   proof fix x assume A: "x \<in> permute_list (fun_inv \<sigma>) ` S"
     then obtain y where y_def: "y \<in> S \<and> x = permute_list (fun_inv \<sigma>) y"
       by blast
     have 0: "(fun_inv \<sigma>) permutes {..<n}"
       using assms unfolding fun_inv_def 
       by (simp add: permutes_inv)
     have 1: "permute_list \<sigma> x = permute_list \<sigma> (permute_list (fun_inv \<sigma>) y)"
       by (simp add: y_def)
     have 2: "length y = n"
       using y_def A assms cartesian_power_car_memE 
       by blast
     have 3: "\<sigma> permutes {..<length y}"
       by (simp add: "2" assms)
     have 4: "permute_list \<sigma> x = y"
       using assms(2) permute_list_id[of y]  permute_list_compose[of \<sigma> y "(fun_inv \<sigma>)" ] 
              3 2 1 0 permutes_inv_o(2)[of \<sigma> "{..< n}"] 
       unfolding fun_inv_def 
       by metis 
     have 5: "x \<in> carrier (R\<^bsup>n\<^esup>)"
       apply(rule cartesian_power_car_memI)
       using A 0 assms  
        apply (metis "2" "4" length_permute_list)
       using A 0 assms  
       by (smt "2" in_set_conv_nth neq0_conv poly_tuple_evalE pushforward_by_pvar_list 
           pvar_list_is_poly_tuple pvar_list_length set_permute_list subset_iff y_def)
     then have 6: "poly_tuple_eval (permute_list \<sigma> (pvar_list R n)) x = y"
       using 4  assms pushforward_by_permuted_pvar_list[of \<sigma> n x] 
       by blast
     then show "x \<in> poly_tuple_pullback n S (permute_list \<sigma> (pvar_list R n))"
       using 5 y_def unfolding poly_tuple_pullback_def 
       by blast
   qed
qed

lemma pullback_by_permutation_of_poly_list':
  assumes "\<sigma> permutes {..< n}"
  assumes "S \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_tuple_pullback n S (permute_list (fun_inv \<sigma>) (pvar_list R n)) = 
          permute_list \<sigma> ` S"
proof-
  have 0: "(fun_inv (fun_inv \<sigma>)) = \<sigma>"
    using assms unfolding fun_inv_def 
    using permutes_inv_inv 
    by blast
  have 1: "fun_inv \<sigma> permutes {..<n}"
    unfolding fun_inv_def 
    using assms permutes_inv by blast
  then show ?thesis using 0 assms pullback_by_permutation_of_poly_list[of "fun_inv \<sigma>" n S]
    by presburger
qed


  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Composing Polynomial Tuples With Polynomials\<close>
  (**********************************************************************)
  (**********************************************************************)

text\<open>composition of a multivaribale polynomial by a list of polynomials\<close>

definition poly_compose :: 
  "nat \<Rightarrow> nat \<Rightarrow> ('a, nat) mvar_poly list \<Rightarrow> ('a, nat) mvar_poly \<Rightarrow> ('a, nat) mvar_poly" where
"poly_compose n m fs = indexed_poly_induced_morphism {..<n} (coord_ring R m) (\<lambda> s. R.indexed_const s) (\<lambda>i. fs!i) "

lemma poly_compose_var:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "j < n"
  shows "poly_compose n m fs (pvar R j) = (fs!j)"
proof-
  have 0: "cring (coord_ring R m)"
    using R.Pring_is_cring R.is_cring 
    unfolding coord_ring_def  by blast    
  have 1: "(!) fs \<in> {..<n} \<rightarrow> carrier (coord_ring R m)"
    using assms is_poly_tuple_def 
    by auto            
  have 2: "ring_hom_ring R (coord_ring R m) coord_const"
    using indexed_const_ring_hom coord_const_ring_hom by blast    
  have "\<forall>i\<in>{..<n}. indexed_poly_induced_morphism {..<n} (coord_ring R m) coord_const ((!) fs) (mset_to_IP R {#i#}) = fs ! i"  
    using assms 0 1 2 R.Pring_universal_prop(2)[of "(coord_ring R m)" "(\<lambda>i. fs!i)" "{..<n}" "(\<lambda> s. R.indexed_const s)" "poly_compose n m fs"] 
           poly_compose_def 
    by (metis var_to_IP_def)    
  then show ?thesis
    using assms 
    unfolding poly_compose_def var_to_IP_def
  by blast
qed

lemma Pring_universal_prop_assms:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  shows  "(\<lambda>i. fs!i) \<in> {..<n} \<rightarrow> carrier (coord_ring R m)"
           "ring_hom_ring R (coord_ring R m) coord_const"
proof
  show "\<And>x. x \<in> {..<n} \<Longrightarrow> fs ! x \<in> carrier (coord_ring R m)"
    using assms  is_poly_tupleE by blast    
  show "ring_hom_ring R (coord_ring R m) coord_const"
    using R.indexed_const_ring_hom coord_const_ring_hom by blast   
qed

lemma poly_compose_ring_hom:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  shows  "(ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (coord_ring R m) (poly_compose n m fs))"
  using Pring_universal_prop_assms[of n fs] assms
        R.Pring_universal_prop(1)[of "(coord_ring R m)" "(\<lambda>i. fs!i)" "{..<n}" coord_const "(poly_compose n m fs)"]
  unfolding poly_compose_def 
  using R.Pring_is_cring R.is_cring
  by (metis Pi_I Pring_universal_prop_assms(2) coord_ring_def is_poly_tupleE lessThan_iff)
  
lemma poly_compose_closed:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "(poly_compose n m fs f) \<in> carrier (coord_ring R m)"
proof-
  have "poly_compose n m fs \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<rightarrow> carrier (R [\<X>\<^bsub>m\<^esub>])"
  using poly_compose_ring_hom[of m fs n] assms 
  unfolding  ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def 
  by blast
  then show ?thesis  using assms by blast 
qed
  
lemma poly_compose_add:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "poly_compose n m fs (f \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> g) = (poly_compose n m fs f) \<oplus>\<^bsub>coord_ring R m\<^esub>  (poly_compose n m fs g)"
  using assms poly_compose_ring_hom ring_hom_add 
  by (metis (mono_tags, lifting) ring_hom_ring.homh)

lemma poly_compose_mult:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "g \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "poly_compose n m fs (f \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> g) = (poly_compose n m fs f) \<otimes>\<^bsub>coord_ring R m\<^esub>  (poly_compose n m fs g)"
  using assms poly_compose_ring_hom ring_hom_mult
  by (metis (mono_tags, lifting) ring_hom_ring.homh)

lemma poly_compose_indexed_pmult:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "i < n"
  shows "poly_compose n m fs (f \<Otimes> i) = (poly_compose n m fs f) \<otimes>\<^bsub>coord_ring R m\<^esub> (fs!i)"
proof-
  have "(f \<Otimes> i) = f \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i"
    using assms pvar_indexed_pmult 
    by blast
  then show ?thesis using poly_compose_mult poly_compose_var  assms 
    by (metis pvar_closed)
qed

lemma poly_compose_const:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "a \<in> carrier R"
  shows "poly_compose n m fs (coord_const a) = coord_const a"
  using R.Pring_universal_prop(3)[of "(coord_ring R m)" "(\<lambda>i. fs!i)" "{..<n}" coord_const "(poly_compose n m fs)"]
        Pring_universal_prop_assms assms
  unfolding poly_compose_def 
  using R.Pring_is_cring coord_cring_cring by blast
  
text\<open>evaluating polynomial compositions\<close>

lemma poly_compose_eval:
  assumes "is_poly_tuple m fs"
  assumes "length fs = n"
  assumes "f \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "as \<in> carrier (R\<^bsup>m\<^esup>)"
  shows "eval_at_point R (poly_tuple_eval fs as) f = eval_at_point R as (poly_compose n m fs f)"
  apply(rule R.indexed_pset.induct[of f "{..<n}" "carrier R"])
  using R.Pring_car assms
  apply (metis coord_ring_def)  
proof-
    show "\<And>k. k \<in> carrier R \<Longrightarrow> eval_at_poly R (coord_const k) (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs (coord_const k)) as"
      using assms 
      by (metis (no_types, lifting) eval_at_point_factored poly_compose_const R.total_eval_const)     
    show " \<And>p Q. p \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_poly R p (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs p) as \<Longrightarrow>
           Q \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_poly R Q (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs Q) as \<Longrightarrow>
           eval_at_poly R (p \<Oplus> Q) (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs (p \<Oplus> Q)) as"
    proof-
      fix p Q
      assume A0: "p \<in> Pring_set R {..<n}"
      assume A1: "eval_at_poly R p (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs p) as"
      assume A2: "Q \<in> Pring_set R {..<n}"
      assume A3: " eval_at_poly R Q (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs Q) as"
      have A4: "eval_at_poly R (p \<Oplus> Q) (poly_tuple_eval fs as) = eval_at_poly R p (poly_tuple_eval fs as) \<oplus> eval_at_poly R Q (poly_tuple_eval fs as)"
        using A0  A1 A2 A3  
            eval_at_point_add[of "(poly_tuple_eval fs as)" n p Q]  
        by (metis R.Pring_add R.Pring_car assms(2) assms(3) assms(4) assms coord_ring_def neq0_conv poly_tuple_eval_closed)
      have A5: "poly_compose n m fs (p \<Oplus> Q) = poly_compose n m fs p \<oplus>\<^bsub>coord_ring R m\<^esub> poly_compose n m fs Q"
        using assms poly_compose_add
        by (metis A0 A2 R.Pring_add R.Pring_car coord_ring_def)        
      have A6: " eval_at_poly R (poly_compose n m fs (p \<Oplus> Q)) as =  eval_at_poly R (poly_compose n m fs p) as \<oplus> eval_at_poly R (poly_compose n m fs Q) as"
      proof-
        have 0: " as \<in> carrier (R\<^bsup>m\<^esup>)"
          by (simp add: assms)
        have 1: "poly_compose n m fs p \<in> carrier (coord_ring R m)"
          using A0 R.Pring_car assms(1) assms(2) assms(3) assms(4) poly_compose_closed 
          by (metis coord_ring_def)           
        have 2: "poly_compose n m fs Q \<in> carrier (coord_ring R m)"
          using A2 R.Pring_car assms(1) assms(2) assms(3) assms(4) poly_compose_closed 
          by (metis coord_ring_def)
        show ?thesis 
          using  0 1 2 eval_at_point_add[of as m "(poly_compose n m fs p)" "(poly_compose n m fs Q)"]
                A5
          by presburger
      qed
      show  "eval_at_poly R (p \<Oplus> Q) (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs (p \<Oplus> Q)) as"
        using A5 A6 A3 A1  A4 
        by presburger
    qed
    show "\<And>p i. p \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_poly R p (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs p) as \<Longrightarrow>
           i \<in> {..<n} \<Longrightarrow> eval_at_poly R (p \<Otimes> i) (poly_tuple_eval fs as) = eval_at_poly R (poly_compose n m fs (p \<Otimes> i)) as"
      using assms poly_compose_indexed_pmult eval_at_point_indexed_pmult
      by (smt R.Pring_car coord_ring_def eval_at_point_mult is_poly_tupleE lessThan_iff neq0_conv poly_compose_closed poly_tuple_evalE'' poly_tuple_eval_closed)
qed

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Extensional Polynomial Maps\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>Polynomial Maps between powers of a ring\<close>

definition poly_map :: "nat \<Rightarrow> ('a, nat) mvar_poly list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"poly_map n fs = (\<lambda>a \<in> carrier (R\<^bsup>n\<^esup>). poly_tuple_eval fs a)"

lemma poly_map_is_struct_map:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  shows "poly_map n fs \<in> struct_maps (R\<^bsup>n\<^esup>) (R\<^bsup>m\<^esup>)"
  apply(rule struct_maps_memI)
  unfolding poly_map_def using assms 
  apply (metis poly_tuple_eval_closed restrict_apply')
  by (meson restrict_apply)

lemma poly_map_closed:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "as \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_map n fs as \<in> carrier (R\<^bsup>m\<^esup>)"
  using assms 
  by (meson poly_map_is_struct_map struct_maps_memE(1))

definition poly_maps :: "nat \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a list) set"  where 
"poly_maps n m = {F. (\<exists> fs. length fs = m \<and> is_poly_tuple n fs \<and> F = poly_map n fs)}"

lemma poly_maps_memE:
  assumes "F \<in> poly_maps n m"
  obtains fs where "length fs = m \<and> is_poly_tuple n fs \<and> F = poly_map n fs"
  using assms unfolding poly_maps_def by blast 

lemma poly_maps_memI:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "F = poly_map n fs"
  shows "F \<in> poly_maps n m"
  using assms unfolding poly_maps_def by blast 

lemma poly_map_compose_closed:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "is_poly_tuple k gs"
  assumes "length gs = n"
  shows "is_poly_tuple k (map (poly_compose n k gs) fs)"
  unfolding is_poly_tuple_def 
proof fix y assume A: "y \<in> set (map (poly_compose n k gs) fs)"
  then obtain f where f_def: "f \<in> set fs \<and> y = poly_compose n k gs f"
    by (smt in_set_conv_nth length_map nth_map)
  then show "y \<in> carrier (coord_ring R k)"
    using assms poly_compose_closed 
    by (metis in_set_conv_nth is_poly_tupleE )
qed

lemma poly_map_compose_closed':
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "is_poly_tuple k gs"
  assumes "length gs = n"
  shows "poly_map k (map (poly_compose n k gs) fs) \<in> poly_maps k m"
  apply(rule poly_maps_memI[of _ "map (poly_compose n k gs) fs"])
  using poly_map_compose_closed[of n fs m k gs] assms apply blast
   apply (simp add: assms)
     by auto

lemma poly_map_pullback_char:
  assumes "is_poly_tuple n fs"
  assumes "length fs = m"
  assumes "is_poly_tuple k gs"
  assumes "length gs = n"
  shows "(pullback (R\<^bsup>k\<^esup>) (poly_map k gs) (poly_map n fs)) = 
          poly_map k (map (poly_compose n k gs) fs)"
proof(rule ext)
  fix x 
  show "pullback (R\<^bsup>k\<^esup>) (poly_map k gs) (poly_map n fs) x =
         poly_map k (map (poly_compose n k gs) fs) x"
  proof(cases "x \<in> carrier (R\<^bsup>k\<^esup>)")
    case True
      have 0: "length (pullback (R\<^bsup>k\<^esup>) (poly_map k gs) (poly_map n fs) x) =  m"
        using True assms poly_map_closed cartesian_power_car_memE
        unfolding pullback_def  
        by (metis (mono_tags, lifting) compose_eq)
      have 1: "is_poly_tuple k (map (poly_compose n k gs) fs)"
       by (simp add: assms poly_map_compose_closed)               
      have 2: "length (map (poly_compose n k gs) fs) = m"
        using assms length_map by auto 
      have 3: "\<And>i. i < m \<Longrightarrow> 
            (pullback (R\<^bsup>k\<^esup>) (poly_map k gs) (poly_map n fs) x)! i = 
                  eval_at_point R (poly_map k gs x) (fs ! i)"
        unfolding pullback_def poly_map_def poly_tuple_eval_def 
        using assms True 
        by (smt compose_eq nth_map poly_tuple_eval_closed poly_tuple_eval_def restrict_apply')
      have 4: "\<And>i. i < m \<Longrightarrow> 
            poly_map k (map (poly_compose n k gs) fs) x ! i = 
                  eval_at_point R (poly_map k gs x) (fs ! i)"       
        unfolding poly_map_def poly_tuple_eval_def using True assms 
        by (smt "2" cring_coord_rings.is_poly_tuple_def cring_coord_rings_axioms neq0_conv 
            nth_map nth_mem poly_compose_eval poly_tuple_eval_def restrict_apply' subset_code(1))
      show ?thesis using 0 1 2 3 4 assms True 
        by (metis cartesian_power_car_memE nth_equalityI poly_map_closed)
  next
    case False
    then show ?thesis 
      unfolding poly_map_def pullback_def
      by (metis affine_alg_set_empty compose_extensional extensional_restrict poly_map_def restrict_def)
  qed
qed

lemma poly_map_pullback_closed:
  assumes "F \<in> poly_maps n m"
  assumes "G \<in> poly_maps k n"
  shows "(pullback (R\<^bsup>k\<^esup>) G F) \<in> poly_maps k m"
  by (metis assms poly_map_compose_closed' 
      poly_map_pullback_char poly_maps_memE)

lemma poly_map_cons: 
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_map n (f#fs) a = (eval_at_point R a f)#poly_map n fs a"
  unfolding poly_map_def poly_tuple_eval_def  
  by (metis (mono_tags, lifting) assms list.simps(9) restrict_apply')
   
lemma poly_map_append: 
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows  "poly_map n (fs@gs) a = (poly_map n fs a) @ (poly_map n gs a)"
proof(induction fs)
  case Nil
  then show ?case 
    using assms unfolding poly_map_def poly_tuple_eval_def 
  by (metis (no_types, lifting) map_append restrict_apply')
next
  case (Cons f fs)
  have "poly_map n ((f # fs) @ gs) a = (eval_at_point R a f)#(poly_map n (fs@gs) a)"
    using poly_map_cons 
    by (metis append_Cons assms)
  hence "poly_map n ((f # fs) @ gs) a = (eval_at_point R a f)#(poly_map n fs a)@(poly_map n gs a)"
    using Cons.IH by metis 
  thus ?case 
    by (metis Cons_eq_appendI assms poly_map_cons)
qed

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Nesting of Polynomial Rings\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma poly_ring_car_mono:
  assumes "n \<le> m"
  shows "carrier (R[\<X>\<^bsub>n\<^esub>]) \<subseteq> carrier (coord_ring R m)"
  using R.Pring_carrier_subset 
  unfolding coord_ring_def 
  by (simp add: R.Pring_car R.Pring_carrier_subset assms)
    
lemma poly_ring_car_mono'[simp]:
  shows "carrier (R[\<X>\<^bsub>n\<^esub>]) \<subseteq> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
        "carrier (R[\<X>\<^bsub>n\<^esub>]) \<subseteq> carrier (R[\<X>\<^bsub>n+m\<^esub>])"
  using poly_ring_car_mono 
  apply simp
  using poly_ring_car_mono 
  by simp

lemma poly_ring_add_mono:
  assumes "n \<le> m"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "B \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "A \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B = A \<oplus>\<^bsub>coord_ring R m\<^esub> B"
  using assms unfolding coord_ring_def 
  by (metis R.Pring_add_eq)
  
lemma poly_ring_add_mono':
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "B \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "A \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B = A \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> B"
        "A \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B = A \<oplus>\<^bsub>R[\<X>\<^bsub>n+m\<^esub>]\<^esub> B"
  using assms unfolding coord_ring_def 
  apply (metis R.Pring_add_eq)
  by (metis R.Pring_add_eq)  

lemma poly_ring_times_mono:
  assumes "n \<le> m"
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "B \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "A \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B = A \<otimes>\<^bsub>coord_ring R m\<^esub> B"
  using assms unfolding coord_ring_def 
  by (metis R.Pring_mult_eq)
  
lemma poly_ring_times_mono':
  assumes "A \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "B \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "A \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B = A \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> B"
        "A \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> B = A \<otimes>\<^bsub>R[\<X>\<^bsub>n+m\<^esub>]\<^esub> B"
  using assms unfolding coord_ring_def 
  apply (metis R.Pring_mult_eq)
  by (metis R.Pring_mult_eq)  
 
lemma poly_ring_one_mono:
  assumes "n \<le> m"
  shows "\<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> = \<one>\<^bsub>coord_ring R m\<^esub>"
  by (metis R.Pring_one coord_ring_def) 

lemma poly_ring_zero_mono:
  assumes "n \<le> m"
  shows "\<zero>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> = \<zero>\<^bsub>coord_ring R m\<^esub>"
  using R.Pring_zero_eq
  by (metis coord_ring_def)

text\<open>replacing the variables in a polynomial with new variables\<close>

definition shift_vars :: "nat \<Rightarrow> nat \<Rightarrow> ('a, nat) mvar_poly \<Rightarrow> ('a, nat) mvar_poly" where
"shift_vars n m p = indexed_poly_induced_morphism {..<n} (R[\<X>\<^bsub>n+m\<^esub>]) coord_const (\<lambda>i. pvar R (i + m)) p" 

lemma shift_vars_char:
  shows "(ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>n+m\<^esub>]) (shift_vars n m))"
        "(\<forall>i \<in> {..<n}. (shift_vars n m) (pvar R i) = pvar R (i + m))"
        "(\<forall>a \<in> carrier R. (shift_vars n m) (R.indexed_const a) = (coord_const a))"
proof-
  have 1:  "(\<lambda>i. pvar R (i + m)) \<in> {..<n} \<rightarrow> carrier (R[\<X>\<^bsub>n+m\<^esub>])"
  proof fix x
    assume "x \<in> {..<n}"
    then have "x + m < n + m"
      using  add_less_mono1 by blast      
    then show "pvar R (x + m) \<in> carrier (R[\<X>\<^bsub>n+m\<^esub>])"
      using pvar_closed by blast
  qed
  have 2:  "ring_hom_ring R (R[\<X>\<^bsub>n+m\<^esub>]) coord_const"
    using R.indexed_const_ring_hom unfolding coord_ring_def 
    by blast
  have 3:  "shift_vars n m = indexed_poly_induced_morphism {..<n} (R[\<X>\<^bsub>n+m\<^esub>]) coord_const (\<lambda>i. pvar R (i + m))"
    unfolding shift_vars_def 
    by blast 
  show "(ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>n+m\<^esub>]) (shift_vars n m))"
    using 1 2 3 R.Pring_universal_prop[of "(R[\<X>\<^bsub>n+m\<^esub>])"  "(\<lambda>i. pvar R (i + m))" "{..<n}" "coord_const" "(shift_vars n m)"]
    using MP.is_cring by (metis coord_ring_def)    
  show "(\<forall>i \<in> {..<n}. (shift_vars n m) (pvar R i) = pvar R (i + m))"
    using 1 2 3 R.Pring_universal_prop[of "(R[\<X>\<^bsub>n+m\<^esub>])"  "(\<lambda>i. pvar R (i + m))" "{..<n}" "coord_const" "(shift_vars n m)"]
    by (metis R.Pring_is_cring MP.is_cring var_to_IP_def)
  show "(\<forall>a \<in> carrier R. (shift_vars n m) (R.indexed_const a) = (coord_const a))"
    using 1 2 3 R.Pring_universal_prop[of "(R[\<X>\<^bsub>n+m\<^esub>])"  "(\<lambda>i. pvar R (i + m))" "{..<n}" "coord_const" "(shift_vars n m)"]
    by (meson MP.is_cring)
qed

lemma shift_vars_constant:
  assumes "a \<in> carrier R"
  shows "shift_vars n m (coord_const a) = coord_const a"
  using assms(1) shift_vars_char(3) by blast

lemma shift_vars_pvar:
  assumes "i \<in> {..<n}"
  shows "shift_vars n m (pvar R i) = pvar R (i + m)"
  using assms shift_vars_char(2) by blast 

lemma shift_vars_add:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "shift_vars n m (p \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q) = shift_vars n m p \<oplus>\<^bsub>R[\<X>\<^bsub>n+m\<^esub>]\<^esub> shift_vars n m Q"
  using assms shift_vars_char(1)[of n m] 
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def 
  using ring_hom_add  
  by (metis (no_types, lifting))  

lemma shift_vars_mult:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "shift_vars n m (p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q) = shift_vars n m p \<otimes>\<^bsub>R[\<X>\<^bsub>n+m\<^esub>]\<^esub> shift_vars n m Q"
  using assms shift_vars_char(1)[of n m] 
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def unfolding coord_ring_def 
  using ring_hom_mult 
  by metis

lemma shift_vars_indexed_pmult:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "i \<in> {..<n}"
  shows "shift_vars n m (p \<Otimes> i) = (shift_vars n m p) \<otimes>\<^bsub>R[\<X>\<^bsub>n+m\<^esub>]\<^esub> (pvar R (i + m))"
proof-
  have "(p \<Otimes> i) = p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (pvar R i)"
    using assms pvar_indexed_pmult by blast
  then show ?thesis 
    using shift_vars_mult shift_vars_pvar assms unfolding coord_ring_def 
    by (metis R.Pring_var_closed)
qed

lemma shift_vars_closed:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "shift_vars n m p \<in> carrier (R[\<X>\<^bsub>n+m\<^esub>])"
  using assms shift_vars_char(1)[of n m] ring_hom_closed[of "shift_vars n m"]
  unfolding ring_hom_ring_def ring_hom_ring_axioms_def  
  by blast

lemma shift_vars_eval:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "a \<in> carrier (R\<^bsup>m\<^esup>)"
  assumes "b \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "eval_at_point R (a@b) (shift_vars n m p)  = eval_at_point R b p"
  apply(rule R.indexed_pset.induct[of p "{..<n}" "carrier R"])
  using R.Pring_car assms apply (metis coord_ring_def)  
proof-
  show "\<And>k. k \<in> carrier R \<Longrightarrow> eval_at_poly R (shift_vars n m (coord_const k)) (a @ b) = eval_at_poly R (coord_const k) b"
  proof-
    fix k
    have 0: "(a @ b) \<in> carrier (R\<^bsup>n + m\<^esup>)"
      using assms 
      by (metis add.commute cartesian_product_closed')
    assume A: "k \<in> carrier R"
    then show "eval_at_poly R (shift_vars n m (coord_const k)) (a @ b) = eval_at_poly R (coord_const k) b"
      using assms shift_vars_constant
          eval_at_point_const[of k "(a @ b)" "m + n"] 
          eval_at_point_const[of k "b" n]  0
      by (metis eval_at_point_const)
  qed
  show "\<And>p Q. p \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_poly R (shift_vars n m p) (a @ b) = eval_at_poly R p b \<Longrightarrow>
           Q \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_poly R (shift_vars n m Q) (a @ b) = eval_at_poly R Q b \<Longrightarrow>
           eval_at_poly R (shift_vars n m (p \<Oplus> Q)) (a @ b) = eval_at_poly R (p \<Oplus> Q) b"
  proof- fix p Q
    assume A0: " p \<in> Pring_set R {..<n}"
    assume A1: "eval_at_poly R (shift_vars n m p) (a @ b) = eval_at_poly R p b"
    assume A2: "Q \<in> Pring_set R {..<n}"
    assume A3: "eval_at_poly R (shift_vars n m Q) (a @ b) = eval_at_poly R Q b"
    have A4: "eval_at_poly R (p \<Oplus> Q) b = eval_at_poly R p b \<oplus> eval_at_poly R Q b"
      using A0 A2 assms eval_at_point_add[of b n p Q]  
      by (metis R.Pring_add R.Pring_car coord_ring_def)      
    have A5: "(shift_vars n m (p \<Oplus> Q)) = (shift_vars n m p) \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (shift_vars n m Q)"
      using A0 A2 R.Pring_add R.Pring_car assms(1) shift_vars_add unfolding coord_ring_def 
      by metis
    have A6: " eval_at_poly R (shift_vars n m (p \<Oplus> Q)) (a @ b) = 
             eval_at_poly R (shift_vars n m p) (a @ b) \<oplus> eval_at_poly R (shift_vars n m Q) (a @ b) "
      using A5 eval_at_point_add shift_vars_closed A0 A2  R.Pring_car add.commute 
        assms unfolding coord_ring_def  
      by (metis R.Pring_add cartesian_power_concat(1))       
    have A7: " eval_at_poly R (shift_vars n m (p \<Oplus> Q)) (a @ b) = 
             eval_at_poly R p b \<oplus> eval_at_poly R Q b "
      using A6  A1 A3 by presburger
    then show " eval_at_poly R (shift_vars n m (p \<Oplus> Q)) (a @ b) = eval_at_poly R (p \<Oplus> Q) b "
      using A4 
      by presburger
  qed
  show "\<And>p i. p \<in> Pring_set R {..<n} \<Longrightarrow>
           eval_at_poly R (shift_vars n m p) (a @ b) = eval_at_poly R p b \<Longrightarrow>
           i \<in> {..<n} \<Longrightarrow> eval_at_poly R (shift_vars n m (p \<Otimes> i)) (a @ b) = eval_at_poly R (p \<Otimes> i) b"
  proof- fix p i
    assume A0: "p \<in> Pring_set R {..<n}" 
    then have A0': "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
      using R.Pring_car unfolding coord_ring_def
      by blast
    assume A1: " eval_at_poly R (shift_vars n m p) (a @ b) = eval_at_poly R p b"
    assume A2: "i \<in> {..<n}"
    have A3: "(shift_vars n m (p \<Otimes> i)) = (shift_vars n m p) \<otimes>\<^bsub>R[\<X>\<^bsub>n+m\<^esub>]\<^esub> (pvar R (i + m))"
      using A0'  shift_vars_indexed_pmult A2 assms(1) 
      by blast
    have A4: "eval_at_poly R (shift_vars n m (p \<Otimes> i)) (a @ b) = 
              eval_at_poly R ( (shift_vars n m p) \<otimes>\<^bsub>R[\<X>\<^bsub>n+m\<^esub>]\<^esub> (pvar R (i + m))) (a@b)"
      using A3 
      by presburger
    have A5: "a@b \<in> carrier (R\<^bsup>n+m\<^esup>)"
      using assms(2) assms(3) cartesian_power_concat(2) by blast    
    have A6: "eval_at_poly R (shift_vars n m (p \<Otimes> i)) (a @ b) = 
              eval_at_poly R p b \<otimes> eval_at_poly R (pvar R (i + m)) (a @ b)"
      using A5  A0' eval_at_point_mult[of "a@b" "n+m" "shift_vars n m p" "pvar R (i + m)"]
      unfolding A4 by (metis A1 A2 Groups.add_ac(2) lessThan_iff local.pvar_closed nat_add_left_cancel_less shift_vars_closed)      
    have A7: " eval_at_poly R (pvar R (i + m)) (a @ b) = (a@b)!(i+m)"
    proof-
      have "i < n"
        using assms A2 by blast        
      then have "i + m < n + m "
        using add_less_cancel_right 
        by blast
      then show ?thesis 
        using A5 eval_pvar[of "i+m" "n+m" "a@b"] 
        by blast
    qed
    then  have A8: "eval_at_poly R (shift_vars n m (p \<Otimes> i)) (a @ b) = eval_at_poly R p b \<otimes> ((a @ b)!(i+m))"
      using A6 by presburger
    have A9: "eval_at_poly R (shift_vars n m (p \<Otimes> i)) (a @ b) = eval_at_poly R p b \<otimes> (b!i)"
    proof-
      have "length a = m"
        using assms cartesian_power_car_memE by blast
      then have "(a @ b)!(i+m) = b!i"
        by (metis add.commute nth_append_length_plus)
      then show ?thesis 
        using A8 
        by presburger
    qed
    show " eval_at_poly R (shift_vars n m (p \<Otimes> i)) (a @ b) = eval_at_poly R (p \<Otimes> i) b"
    proof-
      have "i < n"
        using A2 assms 
        by blast        
      then have "eval_at_poly R (p \<Otimes> i) b = eval_at_poly R p b \<otimes> (b!i)"
        using assms A0' eval_at_point_indexed_pmult
        by blast
      then show ?thesis using A9 
        by presburger
    qed
  qed
qed

      
text\<open>Evaluating a polynomial from a lower poly ring in a higher power:\<close>

lemma poly_eval_cartesian_prod:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "b \<in> carrier (R\<^bsup>m\<^esup>)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "eval_at_point R a p = eval_at_point R (a@b) p"
  apply(rule coord_ring_induct[of p n])
  using assms apply blast
proof-
  have 0: "a@b \<in> carrier (R\<^bsup>n + m\<^esup>)"
    using assms cartesian_product_closed' by blast
  show "\<And>aa. aa \<in> carrier R \<Longrightarrow> eval_at_poly R (coord_const aa) a = eval_at_poly R (coord_const aa) (a @ b)"
  proof- fix c assume "c \<in> carrier R"
    show "eval_at_poly R (coord_const c) a = eval_at_poly R (coord_const c) (a @ b)"
      using eval_at_point_const[of c a n] eval_at_point_const[of c "a@b" "n+m"] 0 
        \<open>c \<in> carrier R\<close> assms(2) assms(1) by presburger     
  qed
  show "\<And>i Q. Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
           eval_at_poly R Q a = eval_at_poly R Q (a @ b) \<Longrightarrow>
           i < n \<Longrightarrow> eval_at_poly R (Q \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i) a = eval_at_poly R (Q \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i) (a @ b)"    
  proof-
  fix i Q
  assume A0: "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])" 
  assume A1: "eval_at_poly R Q a = eval_at_poly R Q (a @ b)"
  assume A2: "i < n"
  have LHS: "eval_at_poly R (Q \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i) a = eval_at_poly R Q a \<otimes> (a!i)"
    by (metis A0 A2 assms eval_at_point_indexed_pmult pvar_indexed_pmult)
  have RHS: "eval_at_poly R (Q \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i) (a @ b) = eval_at_poly R Q (a@b) \<otimes> ((a@b)!i)"
    by (smt "0" A0 A2 add.commute eval_at_point_indexed_pmult le_add1 poly_ring_car_mono 
      pvar_indexed_pmult subsetD trans_less_add2)
  show "eval_at_poly R (Q \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i) a = eval_at_poly R (Q \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i) (a @ b)"   
  proof-
    have "length a > i" using A2 assms
      using cartesian_power_car_memE by blast
    then have "a!i = (a@b)!i"
      by (metis nth_append)
    then show ?thesis 
      using LHS RHS A1 
      by presburger
  qed
  qed
  show "\<And>Q0 Q1.
       Q0 \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
       Q1 \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
       eval_at_poly R Q0 a = eval_at_poly R Q0 (a @ b) \<Longrightarrow>
       eval_at_poly R Q1 a = eval_at_poly R Q1 (a @ b) \<Longrightarrow>
       eval_at_poly R (Q0 \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q1) a = eval_at_poly R (Q0 \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q1) (a @ b)"
  proof-
    fix Q0 Q1 
    assume A0: "eval_at_poly R Q0 a = eval_at_poly R Q0 (a @ b)"
    assume A1: "eval_at_poly R Q1 a = eval_at_poly R Q1 (a @ b)"
    assume A2: "Q0 \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    assume A3: "Q1 \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    show "eval_at_poly R (Q0 \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q1) a = eval_at_poly R (Q0 \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q1) (a @ b)"
      using A0 A1 A2 A3  assms eval_at_point_add[of _ n Q0 Q1] 0 unfolding coord_ring_def
      by (metis (no_types, lifting) R.Pring_add_eq basic_trans_rules(31) coord_ring_def eval_at_point_add le_add1 poly_ring_car_mono)      
  qed
qed

text\<open>Evaluating polynomials at points in higher powers:\<close>

lemma eval_at_points_higher_pow:
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "k \<ge> n"
  assumes "a \<in> carrier (R\<^bsup>k\<^esup>)"
  shows "eval_at_point R a p = eval_at_point R (take n a) p"
  using poly_eval_cartesian_prod[of "take n a" n "drop n a" "k - n" p] assms 
  by (metis (no_types, lifting) append_take_drop_id cartesian_power_car_memE cartesian_power_car_memE''
      cartesian_power_car_memI length_drop set_drop_subset subset_trans take_closed)


subsection\<open> Diagonal sets in even powers of \<open>R\<close>\<close>

text\<open>
  In this section, by a diagonal set in $R^(2m)$ we will mean the set of points $(x,x)$,
  where $x \in R^m$. This is slightly different from the standard definition. Introducing these 
  sets will be useful for reasoning about multiplicative inverses of functions later on.
\<close>

definition diagonal :: "nat \<Rightarrow> 'a list set" where 
"diagonal m = {x \<in> carrier (R\<^bsup>m+m\<^esup>). take m x = drop m x}"

lemma diagonalE: 
  assumes "x \<in> diagonal  m"
  shows "x = (take m x)@(take m x)"
        "x \<in> carrier (R\<^bsup>m+m\<^esup>)"
        "take m x \<in> carrier (R\<^bsup>m\<^esup>)"
        "\<And>i. i < m \<Longrightarrow> x!i = x!(i + m)"
   apply (metis (mono_tags, lifting) append_take_drop_id assms(1) diagonal_def mem_Collect_eq )
  using assms diagonal_def 
  apply blast
  apply(rule cartesian_power_car_memI)
  using assms unfolding diagonal_def 
  apply (metis (no_types, lifting) cartesian_power_car_memE le_add2 mem_Collect_eq take_closed)
proof-
  show "set (take m x) \<subseteq> carrier R"
  proof fix a
    assume "a \<in> set (take m x)"
    then have "a \<in> set x"
      by (meson in_set_takeD)
    then show "a \<in> carrier R"
      using assms unfolding diagonal_def using cartesian_power_car_memE'[of x] 
      by (smt cartesian_power_car_memE in_set_conv_nth mem_Collect_eq)
  qed
  show "\<And>i. i < m \<Longrightarrow> x!i = x!(i + m)"
  proof- fix i
    assume A: "i < m"
    have 0: "x = (take m x)@(take m x)"
      using assms diagonal_def[of m] 
      by (metis (mono_tags, lifting) append_take_drop_id mem_Collect_eq)
    then have 1: "x!i = take m x ! i"
      by (metis A nth_take)
    have 2: "length x = m + m"
      using assms(1) cartesian_power_car_memE diagonal_def by blast
    have 3: "take m x = drop m x"
      by (metis "0" append_take_drop_id same_append_eq)
    have 4: "drop m x ! i = x ! (i + m)"
      by (metis "2" add.commute le_add1 nth_drop)
    then show "x!i = x!(i + m)"
      using "1" "3" by presburger
  qed
qed

lemma diagonalI: 
  assumes "x = (take m x)@(take m x)"
  assumes "take m x \<in> carrier (R\<^bsup>m\<^esup>)"
  shows "x \<in> diagonal m"
  unfolding diagonal_def using assms 
  by (metis (mono_tags, lifting) append_eq_conv_conj cartesian_power_car_memE 
      cartesian_power_car_memI'' length_append mem_Collect_eq)

definition diag_def_poly :: "nat \<Rightarrow> nat \<Rightarrow>('a, nat) mvar_poly" where
"diag_def_poly n i = pvar R i \<ominus>\<^bsub>coord_ring R (n + n)\<^esub> pvar R (i + n)"

lemma diag_def_poly_closed:
  assumes "i < n"
  shows "diag_def_poly n i \<in> carrier (coord_ring R (n + n))"
  using assms unfolding diag_def_poly_def  coord_ring_def
  by (metis (no_types, lifting) MP.minus_closed add.assoc add_leD1 coord_ring_def less_add_eq_less local.pvar_closed nat_less_le not_add_less1)  

lemma diag_def_poly_eval:
  assumes "i < n"
  assumes "x \<in> carrier (R\<^bsup>n+n\<^esup>)"
  shows "eval_at_point R x (diag_def_poly n i)  = (x!i) \<ominus> (x!(i + n))"

  using assms diag_def_poly_def[of n i]  
        eval_at_point_subtract[of x "n + n" "pvar R i" "pvar R (i + n)"] eval_pvar[of i "n + n"]
        eval_pvar[of "i+n" "n + n"] pvar_closed[of i "n + n"] pvar_closed[of "i + n" "n + n"] 
  by (metis add_less_cancel_right trans_less_add2)

definition diag_def_poly_set :: "nat \<Rightarrow> ('a, nat) mvar_poly set" where 
"diag_def_poly_set n = diag_def_poly n ` {..<n}"

lemma diag_def_poly_set_in_coord_ring:
  shows "diag_def_poly_set n \<subseteq> carrier (coord_ring R (n + n))"
proof fix x 
  assume "x \<in> diag_def_poly_set n"
  then obtain i where i_def: "i < n \<and> x = diag_def_poly n i"
    unfolding diag_def_poly_set_def  
    by blast   
  then show "x \<in> carrier (coord_ring R (n + n))"
    using diag_def_poly_closed
    by blast
qed

lemma diag_def_poly_set_finite: 
"finite (diag_def_poly_set n)"
  unfolding diag_def_poly_set_def 
  by blast

lemma diag_def_poly_eval_at_diagonal:
  assumes "x \<in> diagonal n"
  assumes "i < n"
  shows "eval_at_point R x (diag_def_poly n i) = \<zero>"
proof-
  have "x!i = x!(i + n)"
    using assms diagonalE(4) by blast
  then show ?thesis 
    by (metis assms(1) assms(2) cartesian_power_car_memE cartesian_power_car_memE' cring_coord_rings.diag_def_poly_eval cring_coord_rings_axioms diagonalE(2) point_to_polysE point_to_polysE' pvar_trans_eval trans_less_add2)    
qed

lemma diagonal_as_affine_alg_set:
  shows "diagonal n = affine_alg_set R (n + n) (diag_def_poly_set n)"
proof
  show "diagonal n \<subseteq> affine_alg_set R (n + n) (diag_def_poly_set n)"
  proof fix x assume A: "x \<in> diagonal n"
    show " x \<in> affine_alg_set R (n + n) (diag_def_poly_set n)"
        apply(rule affine_alg_set_memI)
        using A  diagonalE(2) apply blast
        using diag_def_poly_eval_at_diagonal[of x] diag_def_poly_set_def[of n]
              atLeastAtMost_iff[of _ 0 "n-1"] 
        by (metis (no_types, lifting) A image_iff lessThan_iff)                     
  qed
  show "affine_alg_set R (n + n) (diag_def_poly_set n) \<subseteq> diagonal n"
  proof fix x 
    assume A: "x \<in> affine_alg_set R (n + n) (diag_def_poly_set n)"
    show "x \<in> diagonal n"
    proof(rule diagonalI)
      show "x = take n x @ take n x"
      proof-
        have 0: "x = take n x @ drop n x"
          by (metis append_take_drop_id)
        have "take n x = drop n x"
        proof-
          have 0: "length x = n + n"
            using A unfolding affine_alg_set_def  
            using cartesian_power_car_memE by blast
          then have 1: "length (take n x) = length (drop n x)"
            using A 
            by (metis (no_types, lifting) \<open>x = take n x @ drop n x\<close> 
                add.commute add_right_cancel affine_alg_set_closed cartesian_power_car_memE 
                le_add1 length_append subsetD take_closed)
          have "\<And>i::nat. i < n \<Longrightarrow> (take n x)!i = (drop n x) ! i"
          proof- fix i::nat assume A0: "i < n"
            then have "i \<in> {..<n}" using atLeastAtMost_iff[of i 0 "n-1"]
              by auto
            then have "diag_def_poly n i \<in>  (diag_def_poly_set n)"
              using diag_def_poly_set_def by blast
            then have "eval_at_point R x (diag_def_poly n i) = \<zero>"
              using A affine_alg_set_memE by blast
            then have "x!i = x!(n + i)"
              using A0 diag_def_poly_eval[of i n x] 
              by (metis (no_types, lifting) A add.commute affine_alg_set_closed
                  cartesian_power_car_memE' nat_add_left_cancel_less R.r_right_minus_eq subsetD trans_less_add2)
            then show "take n x ! i =drop n x ! i"
              by (metis "0" A0 le_add1 nth_drop nth_take)
          qed
          then show ?thesis using 0 
            by (metis "1" \<open>x = take n x @ drop n x\<close> add_less_mono 
                length_append less_not_refl linorder_neqE_nat nth_equalityI)
        qed
        then show ?thesis 
          using 0 by metis   
      qed
      show "take n x \<in> carrier (R\<^bsup>n\<^esup>)"
        using A unfolding affine_alg_set_def 
        by (meson A affine_alg_set_closed le_add2 subset_eq take_closed)
    qed
  qed
qed

lemma diagonal_is_algebraic:
  shows "is_algebraic R (n + n) (diagonal n)"
  apply(rule is_algebraicI[of "diag_def_poly_set n"])
  apply (simp add: diag_def_poly_set_finite)
  using  diag_def_poly_set_in_coord_ring apply blast
  by (simp add:  diagonal_as_affine_alg_set)

end 

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Tuples of Functions\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition is_function_tuple :: "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a) list \<Rightarrow> bool" where 
"is_function_tuple R n fs = (set fs \<subseteq> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R)"

lemma is_function_tupleI:
  assumes "(set fs \<subseteq> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R)"
  shows "is_function_tuple R n fs "
  by (simp add: assms is_function_tuple_def)

lemma is_function_tuple_append:
  assumes "is_function_tuple R n fs" 
  assumes "is_function_tuple R n gs" 
  shows "is_function_tuple R n (fs@gs)"
  using assms is_function_tupleI set_append
  by (simp add: is_function_tuple_def)

lemma is_function_tuple_Cons:
  assumes "is_function_tuple R n fs" 
  assumes "f \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R"
  shows "is_function_tuple R n (f#fs)"
  using assms is_function_tupleI  
  by (simp add: assms(2) is_function_tuple_def)

lemma is_function_tuple_snoc:
  assumes "is_function_tuple R n fs" 
  assumes "f \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R"
  shows "is_function_tuple R n (fs@[f])"
  apply(rule is_function_tupleI)
  by (metis (no_types) Un_subset_iff append_Nil assms(1) assms(2) is_function_tuple_Cons is_function_tuple_def set_append)

lemma is_function_tuple_list_update:
  assumes "is_function_tuple R n fs" 
  assumes "f \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R"
  assumes "i < n"
  shows "is_function_tuple R n (fs[i := f])"
  apply(rule is_function_tupleI)
  by (metis assms(1) assms(2) is_function_tuple_def set_update_subsetI)

definition function_tuple_eval :: "'b \<Rightarrow> 'c \<Rightarrow> ('d \<Rightarrow> 'a) list \<Rightarrow> 'd \<Rightarrow> 'a list" where
"function_tuple_eval R n fs x = map (\<lambda>f. f x) fs"

lemma function_tuple_eval_closed:
  assumes "is_function_tuple R n fs" 
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "function_tuple_eval R n fs x \<in> carrier (R\<^bsup>length fs\<^esup>)"
  apply(rule cartesian_power_car_memI')
  apply (metis function_tuple_eval_def length_map)
proof- fix i assume "i < length fs"
  then show "function_tuple_eval R n fs x ! i \<in> carrier R"
    unfolding function_tuple_eval_def using assms unfolding is_function_tuple_def 
  by (metis funcset_carrier nth_map nth_mem subsetD)
qed

definition coord_fun :: 
  "('a, 'c) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'b list) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b" where 
"coord_fun R n g i = (\<lambda>x \<in>  carrier (R\<^bsup>n\<^esup>). (g x) ! i)"

lemma(in cring) map_is_coord_fun_tuple:
  assumes "g \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow>\<^sub>E carrier (R\<^bsup>m\<^esup>)"
  shows "g = (\<lambda> x \<in> carrier (R\<^bsup>n\<^esup>). function_tuple_eval R n (map (coord_fun R n g) [0..<m]) x)"
proof
  fix x 
  show "g x = restrict (function_tuple_eval R n (map (coord_fun R n g) [0..<m])) (carrier (R\<^bsup>n\<^esup>)) x"
  proof(cases "x \<in> carrier (R\<^bsup>n\<^esup>)")
    case True
    then have T0: "restrict (function_tuple_eval R n (map (coord_fun R n g) [0..<m])) (carrier (R\<^bsup>n\<^esup>)) x = 
              function_tuple_eval R n (map (coord_fun R n g) [0..<m]) x"
      by (meson restrict_apply')
    have T1: "length (g x) = m"
      by (metis PiE_mem True assms cartesian_power_car_memE)
    have T2: "\<And>i. i < m \<Longrightarrow> (g x) ! i = (function_tuple_eval R n (map (coord_fun R n g) [0..<m]) x) ! i"
      unfolding function_tuple_eval_def coord_fun_def 
      using restrict_apply True T1 length_map map_nth nth_map by smt 
    have T3: "length (function_tuple_eval R n (map (coord_fun R n g) [0..<m]) x) = m"
      unfolding function_tuple_eval_def using length_map 
      by (metis T1 map_nth)
    show ?thesis using T1 T2 T3 
      by (metis T0 nth_equalityI)
  next
    case False
    then show ?thesis using assms unfolding restrict_def  
      by (meson PiE_E)
  qed
qed

definition function_tuple_comp :: 
  "'c \<Rightarrow> ('a \<Rightarrow> 'd) list \<Rightarrow> ('d list \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"function_tuple_comp R fs f = f \<circ> (function_tuple_eval R (0::nat) fs)"

lemma function_tuple_comp_closed:
  assumes "f \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R"
  assumes "length fs = n"
  assumes "is_function_tuple R m fs"
  shows "function_tuple_comp R fs f \<in> carrier (R\<^bsup>m\<^esup>) \<rightarrow> carrier R"
  unfolding function_tuple_comp_def
  using assms 
  by (smt Pi_iff comp_apply function_tuple_eval_closed function_tuple_eval_def)

fun id_function_tuple where
"id_function_tuple (R::('a,'b) partial_object_scheme) 0 = []"|
"id_function_tuple R (Suc n) = id_function_tuple R n @ [(\<lambda>(x::'a list). x! n)] "

lemma id_function_tuple_is_function_tuple:
"\<And>k. k \<ge> n \<Longrightarrow> is_function_tuple R k (id_function_tuple R n)"
  apply(induction n)
  apply (simp add: is_function_tupleI)
proof- fix n k
  assume IH: "(\<And>k. n \<le> k \<Longrightarrow> is_function_tuple R k (id_function_tuple R n))"

  assume A: "Suc n \<le> k"
  have 0: "(\<lambda>a. a!n) \<in> carrier (R\<^bsup>k\<^esup>)  \<rightarrow> carrier R"
    using A cartesian_power_car_memE' 
    by (metis Pi_I Suc_le_lessD)
  have 1: " is_function_tuple R k (id_function_tuple R n)"
    using A IH  Suc_leD by blast
  then show "is_function_tuple R k (id_function_tuple R (Suc n))"
    using A  0 id_function_tuple.simps(2)[of R n] 
          is_function_tuple_snoc[of R k "id_function_tuple R n" "\<lambda>a. a!n" ] 
     by (simp add: "0")
qed

lemma id_function_tuple_is_function_tuple':
"is_function_tuple R n (id_function_tuple R n)"
by (simp add: id_function_tuple_is_function_tuple)
    
lemma id_function_tuple_eval_is_take:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "k \<le> n \<Longrightarrow> function_tuple_eval R n (id_function_tuple R k) a = take k a"
  apply(induction k)
  using assms  
  apply (simp add: assms function_tuple_eval_def)
proof- fix k
  assume IH: "(k \<le>  n \<Longrightarrow> function_tuple_eval R n (id_function_tuple R k) a = take k a) "
  assume A: "Suc k \<le> n"
  then have 0: "function_tuple_eval R n (id_function_tuple R k) a = take k a "
    using IH  Suc_leD 
    by blast   
  have  "function_tuple_eval R n (id_function_tuple R (Suc  k)) a
          = function_tuple_eval R n (id_function_tuple R k) a @ [a!k]"
    using id_function_tuple.simps(2)[of R k]  
    by (simp add: function_tuple_eval_def)
  then  show "function_tuple_eval R n (id_function_tuple R (Suc k)) a = take (Suc k) a"
    by (metis "0" A Suc_le_lessD assms cartesian_power_car_memE take_Suc_conv_app_nth)
qed
  
lemma id_function_tuple_eval_is_id:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "function_tuple_eval R n (id_function_tuple R n) a = a"
  using assms  id_function_tuple_eval_is_take[of a R n n]
  by (metis cartesian_power_car_memE order_refl take_all)

text\<open>Composing a function tuple with a polynomial\<close>

definition poly_function_tuple_comp :: 
   "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a) list \<Rightarrow> ('a, nat) mvar_poly \<Rightarrow> 'a list \<Rightarrow> 'a" where
"poly_function_tuple_comp R n fs f = eval_at_poly R f \<circ> function_tuple_eval R n fs"

context cring_coord_rings
begin

lemma poly_function_tuple_comp_closed:
  assumes "is_function_tuple R n fs" 
  assumes "f \<in> carrier (coord_ring R (length fs))"
  shows "poly_function_tuple_comp R n fs f \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier R"
proof fix x assume A: "x \<in> carrier (R\<^bsup>n\<^esup>)" 
  then show "poly_function_tuple_comp R n fs f x \<in> carrier R"
    using assms function_tuple_eval_closed eval_at_point_closed
    unfolding poly_function_tuple_comp_def 
    by (metis comp_apply)
qed

lemma poly_function_tuple_comp_eq:
  assumes "is_function_tuple R n fs" 
  assumes "f \<in> carrier (coord_ring R (length fs))"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_function_tuple_comp R n fs f a = eval_at_poly R f ( function_tuple_eval R n fs a)"
  unfolding poly_function_tuple_comp_def 
  using comp_apply 
  by metis
  
lemma poly_function_tuple_comp_constant:
  assumes "is_function_tuple R n fs" 
  assumes "a \<in> carrier R"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_function_tuple_comp R n fs (coord_const a) x = a"
  unfolding poly_function_tuple_comp_def 
  using assms comp_apply function_tuple_eval_closed
  by (metis eval_at_point_const)

lemma poly_function_tuple_comp_add:
  assumes "is_function_tuple R n fs"
  assumes "k \<le>length fs"
  assumes "p \<in> carrier (coord_ring R k)"
  assumes "Q \<in> carrier (coord_ring R k)"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_function_tuple_comp R n fs (p \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q) x = 
          (poly_function_tuple_comp R n fs p x) \<oplus> (poly_function_tuple_comp R n fs Q x)"
proof-
  have 0: "p \<in> carrier (coord_ring R (length fs))"
    using assms poly_ring_car_mono[of k "length fs"]
    by blast 
  have 1: "Q \<in> carrier (coord_ring R (length fs))"
    using assms poly_ring_car_mono[of k "length fs"]
    by blast 
  show ?thesis  
    using assms(1) assms(5) 0 1 R.Pring_add_eq[of ]
        poly_function_tuple_comp_eq
        function_tuple_eval_closed[of R n fs x]  
        eval_at_point_add[of "function_tuple_eval R n fs x" "length fs" p Q]
   unfolding coord_ring_def by (metis R.Pring_add_closed)    
qed    

lemma poly_function_tuple_comp_mult:
  assumes "is_function_tuple R n fs"
  assumes "k \<le>length fs"
  assumes "p \<in> carrier (coord_ring R k)"
  assumes "Q \<in> carrier (coord_ring R k)"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_function_tuple_comp R n fs (p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q) x = 
          (poly_function_tuple_comp R n fs p x) \<otimes> (poly_function_tuple_comp R n fs Q x)"
proof-
  have 0: "p \<in> carrier (coord_ring R (length fs))"
    using assms poly_ring_car_mono[of k "length fs"]
    by blast 
  have 1: "Q \<in> carrier (coord_ring R (length fs))"
    using assms poly_ring_car_mono[of k "length fs"]
    by blast 
  show ?thesis
    using assms  0 1
        poly_function_tuple_comp_eq
        function_tuple_eval_closed[of R n fs x]  
        eval_at_point_mult[of "function_tuple_eval R n fs x" "length fs" p Q]
    unfolding coord_ring_def 
    by (metis MP.m_closed R.Pring_mult_eq coord_ring_def)    
qed

lemma poly_function_tuple_comp_pvar:
  assumes "is_function_tuple R n fs"
  assumes "k < length fs"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  shows "poly_function_tuple_comp R n fs (pvar R k) x = (fs ! k) x"
proof-
  have "(map (\<lambda>f. f x) fs) \<in> carrier (R\<^bsup>length fs\<^esup>)"
    using function_tuple_eval_closed[of R n fs x] 
    unfolding function_tuple_eval_def
    using assms(1) assms(3) by blast
  then have "eval_at_poly R (pvar R k) (map (\<lambda>f. f x) fs)  = (fs! k) x"
    using eval_pvar[of k "length fs" "(map (\<lambda>f. f x) fs)"] 
    by (metis assms(2) nth_map)
  then show ?thesis 
    by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) function_tuple_eval_def 
        nth_map poly_function_tuple_comp_eq pvar_closed)
qed

end
text\<open>The coordinate ring of polynomials indexed by natural numbers\<close>

definition Coord_ring :: "('a, 'b) ring_scheme \<Rightarrow> ('a, ('a, nat) mvar_poly) module" where
"Coord_ring R = Pring R (UNIV :: nat set)"


text\<open>Some general closure lemmas for coordinate rings\<close>
context cring_coord_rings
begin
lemma coord_ring_monom_term_closed:
  assumes "a \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "b \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "a \<otimes>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> b[^]\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub>(n::nat) \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  using assms  monoid.nat_pow_closed[of "(R[\<X>\<^bsub>n\<^esub>])"] 
  unfolding coord_ring_def
  by (meson R.Pring_is_monoid monoid.m_closed)

lemma coord_ring_monom_term_plus_closed:
  assumes "a \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "b \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "c \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "c \<oplus>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> a \<otimes>\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub> b[^]\<^bsub>(R[\<X>\<^bsub>n\<^esub>])\<^esub>(n::nat) \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  using assms coord_ring_monom_term_closed R.Pring_add_closed
  by blast

end

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Generic Univariate Polynomials\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  By a generic univariate polynomial, we mean a polynomial in one variable whose coefficients are
  coordinate functions over a ring. That is, a polynomial of the form:
  \[f(t) = x_0 + x_1t + \dots + x_nt^n\]
  Such a polynomial can be construed as an element of $R[x_0,..,x_n](t)$, or as an element of
  $R[x_0,..,x_n, x_n{n+1}]$. We will intially define the latter version, and show that it can
  easily be cast to the former using the function ``\texttt{IP\_to\_UP"}. Such a polynomial can be
  cast to a univariate polynomial over the ring $R$ by substituting a tuple of ring elements for
  the coefficients.  
\<close>
definition generic_poly_lt ::  "('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> ('a, nat) mvar_poly" where
"generic_poly_lt R n = (pvar R (Suc n)) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> (pvar R 0)[^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n"

fun generic_poly where
"generic_poly R (0::nat) = pvar R 1"|
"generic_poly R (Suc n) = (generic_poly R n) \<oplus>\<^bsub>(coord_ring R (n+3))\<^esub> generic_poly_lt R (Suc n)"


context cring_coord_rings
begin

lemma generic_poly_lt_closed:
"generic_poly_lt R n \<in> carrier (coord_ring R (Suc (Suc n)))"
proof-
  have 0: "(pvar R (Suc n)) \<in> carrier (coord_ring R (Suc (Suc n)))"
    using pvar_closed 
    by blast
  have 1: " (pvar R 0) \<in> carrier (coord_ring R (Suc (Suc n)))"
    using pvar_closed 
    by blast
  then have "(pvar R 0)[^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n \<in> carrier (coord_ring R (Suc (Suc n)))"
    using monoid.nat_pow_closed 
    unfolding coord_ring_def by (metis R.Pring_is_monoid)
  then show ?thesis using 0 
    unfolding coord_ring_def 
    by (metis R.Pring_mult_closed coord_ring_def generic_poly_lt_def)    
qed

lemma generic_poly_lt_eval:
  assumes "a \<in> carrier (R\<^bsup>n+2\<^esup>)"
  shows "eval_at_point R a (generic_poly_lt R n) = a!(Suc n) \<otimes> (a!0)[^]n "
proof-
  have "(pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) \<in> carrier (coord_ring R (n + 2))"
    using monoid.nat_pow_closed pvar_closed unfolding coord_ring_def
    by (metis R.Pring_is_monoid add_2_eq_Suc' zero_less_Suc)
  then have "eval_at_point R a (generic_poly_lt R n) =
    eval_at_poly R (pvar R (Suc n)) a \<otimes> eval_at_poly R (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) a"
    unfolding generic_poly_lt_def 
    using assms pvar_closed[of "(Suc n)" "n + 2"] eval_at_point_mult[of a "n + 2" "pvar R (Suc n)" "(pvar R 0)[^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n"]
    by (metis add_2_eq_Suc' lessI)  
  then show ?thesis using assms 
    by (metis add_2_eq_Suc' add_gr_0 eval_at_point_nat_pow eval_pvar lessI pvar_closed zero_less_numeral)
qed  

lemma generic_poly_closed:
"generic_poly R n \<in> carrier (coord_ring R (Suc (Suc n)))"
  apply(induction n)
  using pvar_closed[of 1 "Suc (Suc n)"]
  apply (metis One_nat_def generic_poly.simps(1) lessI pvar_closed)
proof-
  fix n assume IH: "generic_poly R n \<in> carrier (coord_ring R (Suc (Suc n)))"
    have "generic_poly R n \<in> carrier (coord_ring R (Suc (Suc (Suc n))))"
      using IH poly_ring_car_mono'[of "Suc (Suc n)"]
      by blast
    then show " generic_poly R (Suc n) \<in> carrier (coord_ring R (Suc (Suc (Suc n))))"
      unfolding coord_ring_def 
      using generic_poly.simps[of R] generic_poly_lt_closed[of n]
      by (metis MP.add.m_closed R.Pring_add_eq coord_ring_def generic_poly_lt_closed)
qed

lemma generic_poly_closed':
  assumes "k \<le>n"
  shows "generic_poly R k \<in> carrier (coord_ring R (Suc (Suc n)))"
by (meson Suc_le_mono assms generic_poly_closed poly_ring_car_mono subsetD)

lemma generic_poly_eval_at_point:
  assumes "a \<in> carrier (R\<^bsup>n+3\<^esup>)"
  shows "eval_at_point R a (generic_poly R (Suc n)) = (eval_at_point R a (generic_poly R n)) \<oplus>
                                                    (a!(n + 2)) \<otimes> (a!0)[^](Suc n)"
proof-
  have 0: "(generic_poly R n) \<in> carrier (coord_ring R (n + 3))"
    using generic_poly_closed' 
    by (metis Suc3_eq_add_3 add.commute eq_imp_le le_SucI)
  then show ?thesis 
    using generic_poly.simps(2) 
          generic_poly_closed'[of n "n + 3"] 
          generic_poly_lt_eval eval_at_point_add[of a "(n + 3)" "generic_poly R n"]  
    by (metis (no_types, lifting) add.left_commute add_2_eq_Suc' assms 
        generic_poly_lt_closed numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc)
qed

end

text \<open>
  We can turn points in $R^{n+1}$ into univariate polynomials with the associated coefficients 
  via partial evaluation of the generic polynomials of degree $n$. \<close>

definition ring_cfs_to_poly :: 
"('a, 'b) ring_scheme \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a, nat) mvar_poly" where
"ring_cfs_to_poly R n as = coord_partial_eval R {1..<n+2} (\<zero>\<^bsub>R\<^esub>#as) (generic_poly R n)" 

context cring_coord_rings
begin

lemma ring_cfs_to_poly_closed:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "ring_cfs_to_poly R n as \<in> carrier (coord_ring R 1)"
proof-
  have 0: "\<zero> # as \<in> carrier (R\<^bsup>n+2\<^esup>)"
    apply(rule cartesian_power_car_memI)
    using assms 
    apply (metis add_2_eq_Suc' cartesian_power_car_memE length_Cons)
    using assms 
    by (metis cartesian_power_car_memE'' insert_subset list.simps(15) R.zero_closed)
  then have 1: "coord_partial_eval R {1..<n + 2} (\<zero> # as) \<in> ring_hom (coord_ring R (n + 2)) (Pring R ({..<n + 2} - {1..<n + 2}))"
    using coord_partial_eval_hom' by blast
  have "({..<n + 2} - {1..<n + 2}) = {..<1}"
    by auto 
  then have 2: "coord_partial_eval R {1..<n + 2} (\<zero> # as) \<in> ring_hom (coord_ring R (n + 2)) (coord_ring R 1)"
    using 1 unfolding coord_ring_def
    by presburger    
  then show ?thesis
    unfolding ring_cfs_to_poly_def  coord_ring_def
    by (metis "0" Diff_subset \<open>{..<n + 2} - {1..<n + 2} = {..<1}\<close> 
      add_2_eq_Suc' coord_partial_eval_closed generic_poly_closed 
      le_numeral_extra(4) lessThan_minus_lessThan lessThan_subset_iff)
qed

text\<open>Variant which maps to the univariate polynomial ring\<close>

definition ring_cfs_to_univ_poly :: "nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
"ring_cfs_to_univ_poly n as = IP_to_UP (0::nat) (ring_cfs_to_poly R n as)" 

lemma ring_cfs_to_univ_poly_closed:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows  "ring_cfs_to_univ_poly n as \<in> carrier (UP R)"
  unfolding ring_cfs_to_univ_poly_def apply(rule R.IP_to_UP_closed, rule R.is_cring)
  using ring_cfs_to_poly_closed unfolding coord_ring_def 
  using assms  by (metis One_nat_def lessThan_0 lessThan_Suc)

lemma ring_cfs_to_poly_eq:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  assumes "k \<le>n"
  shows  "ring_cfs_to_poly R k as = ring_cfs_to_poly R k (take (Suc k) as) "
  unfolding ring_cfs_to_poly_def coord_partial_eval_def 
  apply(rule R.poly_eval_eval_function_eq[of "(point_to_eval_map R (\<zero> # as))" "(point_to_eval_map R (\<zero> # take (Suc k) as))" "{1..<k + 2}" _ "{..<k + 2}"])   
proof-
  show "closed_fun R (point_to_eval_map R (\<zero> # as))"
    apply(rule R.closed_funI)
    using assms cartesian_power_car_memE[of as R "Suc n"] 
    by (metis cartesian_power_car_memE'' nth_mem set_ConsD subset_code(1) R.zero_closed)
  show "closed_fun R (\<lambda>i. if i < length (\<zero> # take (Suc k) as) then (\<zero> # take (Suc k) as) ! i else \<zero>)"
    apply(rule R.closed_funI)
    using assms 
    by (metis cartesian_power_car_memE'' in_set_takeD nth_mem set_ConsD subset_code(1) R.zero_closed)
  have 0: "length (\<zero> # as) \<ge> k + 2"
    using assms 
    by (metis Suc_le_mono add_2_eq_Suc' cartesian_power_car_memE length_Cons)
  have 1: "length (\<zero> # take (Suc k) as) \<ge>k + 2"
    using 0 
    by (metis add_2_eq_Suc' assms(1) cartesian_power_car_memE 
        impossible_Cons length_Cons not_less_eq_eq take_closed)
  show "restrict (point_to_eval_map R (\<zero> # as)) {1..<k + 2} = restrict (point_to_eval_map R (\<zero> # take (Suc k) as)) {1..<k + 2}"
  proof fix x 
    show "restrict (point_to_eval_map R (\<zero> # as)) {1..<k + 2} x = restrict (point_to_eval_map R (\<zero> # take (Suc k) as)) {1..<k + 2} x"
    proof(cases "x \<in> {1..<k + 2}")
      case True
      have 00: "restrict (point_to_eval_map R (\<zero> # as)) {1..<k + 2} x = (\<zero>#as)!x"
        unfolding restrict_def 
        by (metis "0" True atLeastLessThan_iff le_Suc_ex trans_less_add1)
      have 11: "restrict (point_to_eval_map R (\<zero> # take (Suc k) as)) {1..<k + 2} x = (\<zero> # take (Suc k) as)!x"
        unfolding restrict_def 
        by (metis "1" True atLeastLessThan_iff le_Suc_ex trans_less_add1)
      have 2: "(\<zero> # as) ! x = (\<zero> # take (Suc k) as) ! x"
      proof-
        obtain l where l_def: "Suc l = x"
          using True
          by (metis One_nat_def Suc_le_D atLeastLessThan_iff) 
        have P1: "(\<zero> # as) ! x = as ! l"
          using 0 True l_def 
          by (meson nth_Cons_Suc)
        have P0: "(\<zero> # take (Suc k) as) ! x = (take (Suc k) as) ! l"
          using 1 True l_def 
          by (meson nth_Cons_Suc)
        have "l < Suc k"
          using True l_def 
          by (metis Suc_1 Suc_eq_plus1 Suc_less_SucD add_Suc_right atLeastLessThan_iff)
        then have "(\<zero> # take (Suc k) as) ! x = as ! l"
          using P0 
          by (metis nth_take)
        then show ?thesis
          using P1 by metis  
      qed
      then show ?thesis using 00 11 True 
        by presburger        
    next
      case False
      then show ?thesis 
        unfolding restrict_def 
        by presburger       
    qed
  qed
  show " generic_poly R k \<in> Pring_set R {..<k + 2}"
   by (metis R.Pring_car add_2_eq_Suc' coord_ring_def generic_poly_closed)    
qed

lemma coord_partial_eval_generic_poly_lt:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "coord_partial_eval R {1..<n+2} (\<zero>\<^bsub>R\<^esub>#as) (generic_poly_lt R n) = 
        poly_scalar_mult R (as!n) ((pvar R 0)[^]\<^bsub>coord_ring R (n+2)\<^esub> n)"
proof-
  have 0: "\<zero> # as \<in>  carrier (R\<^bsup>Suc (Suc n)\<^esup>)"
    using assms cartesian_power_cons 
    by (metis Suc_eq_plus1 R.zero_closed)
  have 1: "pvar R (Suc n) \<in> Pring_set R {..<n + 2}"
    using pvar_closed 
    by (metis R.Pring_car add_2_eq_Suc' coord_ring_def lessI)         
  have 2: " pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n \<in> Pring_set R {..<n + 2}"
    using monoid.nat_pow_closed pvar_closed unfolding coord_ring_def 
    using R.Pring_car R.Pring_is_monoid add_2_eq_Suc' zero_less_Suc
    by (metis)
  have 3: "poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))
     (pvar R (Suc n) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) = 
 (poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as)) (pvar R (Suc n))) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> 
 (poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))
     (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n))"
    using 0 1 2 R.poly_eval_mult[of "pvar R (Suc n)" "{..<n+2}" " pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n"
          "(point_to_eval_map R (\<zero> # as))" "{1..<n + 2}"] unfolding coord_ring_def  
    by (smt R.Pring_mult cartesian_power_car_memE cartesian_power_car_memE' R.closed_funI R.zero_closed)
  have 4: "poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))
     (pvar R (Suc n) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) = 
  (coord_const ((\<zero> # as)! (Suc n))) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> 
  (poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))
     (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n))"
    using 0 3 point_to_eval_map_closed[of "(\<zero> # as)" "Suc (Suc n)"]   
          R.poly_eval_index[of "(point_to_eval_map R (\<zero> # as))" "{1..<n + 2}" "Suc n"]
     add_2_eq_Suc' atLeastLessThan_iff cartesian_power_car_memE le_neq_implies_less 
        less_Suc_eq not_less_eq_eq not_less_zero numeral_1_eq_Suc_0 numeral_One var_to_IP_def 
    by (smt local.one_neq_zero)
  have 5: "pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n \<in> Pring_set R ({..<n + 2} - {1..<n + 2}) "
  proof-
    have "0 \<in> {..<n + 2} - {1..<n + 2}" by auto 
    then have "pvar R 0 [^]\<^bsub>Pring R ({..<n + 2} - {1..<n + 2})\<^esub> n \<in> carrier (Pring R ({..<n + 2} - {1..<n + 2}))"
      using R.Pring_var_closed[of 0 "{..<n + 2} - {1..<n + 2}"] R.Pring_is_monoid[of "{..<n + 2} - {1..<n + 2}"] 
          monoid.nat_pow_closed[of "Pring R ({..<n + 2} - {1..<n + 2})" "pvar R 0" n ] 
      by blast          
    have "\<And>k::nat. (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> k) = (pvar R 0 [^]\<^bsub>Pring R ({..<n + 2} - {1..<n + 2})\<^esub>k)"
    proof- fix k::nat show "(pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> k) = (pvar R 0 [^]\<^bsub>Pring R ({..<n + 2} - {1..<n + 2})\<^esub>k)"
        apply(induction k)
        using R.Pring_var_closed[of 0 "{..<(Suc (Suc n))}"] R.Pring_var_closed[of 0 "{..<n + 2} - {1..<n + 2}"]
        unfolding coord_ring_def 
        apply (metis Group.nat_pow_0 R.ring_axioms R.Pring_one)
        using R.Pring_var_closed[of 0 "{..<(Suc (Suc n))}"] R.Pring_var_closed[of 0 "{..<n + 2} - {1..<n + 2}"]
        nat_pow_def
        by (metis R.Pring_mult_eq R.Pring_one_eq add_2_eq_Suc')
    qed
    then show ?thesis 
      by (metis R.Pring_car \<open>pvar R 0 [^]\<^bsub>Pring R ({..<n + 2} - {1..<n + 2})\<^esub> n \<in> carrier (Pring R ({..<n + 2} - {1..<n + 2}))\<close>)
  qed
  have 6: "(poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))  
               (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n)) = (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n)"
    using 5 0 point_to_eval_map_closed[of "(\<zero> # as)" "Suc (Suc n)"]
          R.poly_eval_trivial[of "(point_to_eval_map R (\<zero> # as))" "pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n" "{..<n + 2}" "{1..<n + 2}" ]
    by blast
  have 7: "poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))
     (pvar R (Suc n) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) = 
  (coord_const ((\<zero> # as)! (Suc n))) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> 
     (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n)"
    using 4 6 
    by presburger
  have 8: "(\<zero> # as) ! Suc n = as! n"
    by (meson nth_Cons_Suc)
  have 88: "(\<zero> # as) ! Suc n \<in> carrier R"
    by (metis "8" assms cartesian_power_car_memE' less_Suc_eq)
  have 9: "poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))
     (pvar R (Suc n) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) = 
    coord_const ((\<zero> # as) ! Suc n) \<Otimes>\<^sub>p pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n "
    using R.poly_scalar_mult_eq[of "(\<zero> # as) ! Suc n" "pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n"] 
    unfolding coord_ring_def  
    by (metis (no_types, lifting) "7" R.Pring_mult coord_ring_def)     
  have 10: "poly_scalar_mult R ((\<zero> # as) ! Suc n) (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) =
    coord_const ((\<zero> # as) ! Suc n) \<Otimes>\<^sub>p pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n"
    using 9 8 88 0 5 R.poly_scalar_mult_eq[of "(\<zero> # as) ! Suc n" "pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n" "({..<n + 2} - {1..<n + 2})"]  
    by blast
  have 11: "poly_scalar_mult R (as! n) (pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) =
    coord_const ((\<zero> # as) ! Suc n) \<Otimes>\<^sub>p pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n"
    using 10 8 
    by metis 
  have 12: "poly_eval R {1..<n + 2} (point_to_eval_map R (\<zero> # as))
     (pvar R (Suc n) \<otimes>\<^bsub>coord_ring R (Suc (Suc n))\<^esub> pvar R 0 [^]\<^bsub>coord_ring R (Suc (Suc n))\<^esub> n) = 
    poly_scalar_mult R (as ! n) ((pvar R 0) [^]\<^bsub>coord_ring R (n + 2)\<^esub> n)"
    using 11 9 
    by (metis add_2_eq_Suc')
  then show ?thesis 
    unfolding coord_partial_eval_def generic_poly_lt_def 
    by blast
qed

lemma coord_partial_eval_generic_poly_lt':
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "coord_partial_eval R {1..<n+2} (\<zero>\<^bsub>R\<^esub>#as) (generic_poly_lt R n) = 
        poly_scalar_mult R (as!n) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> n)"
proof-
  have 0: "coord_partial_eval R {1..<n+2} (\<zero>\<^bsub>R\<^esub>#as) (generic_poly_lt R n) = 
        poly_scalar_mult R (as!n) ((pvar R 0)[^]\<^bsub>coord_ring R (n+2)\<^esub> n)"
    using assms coord_partial_eval_generic_poly_lt by blast    
  have 1: "\<And>k::nat. (pvar R 0)[^]\<^bsub>coord_ring R (n+2)\<^esub> k = (pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> k"
  proof- fix k::nat show "(pvar R 0)[^]\<^bsub>coord_ring R (n+2)\<^esub> k = (pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> k"
      apply(induction k)
      unfolding coord_ring_def 
       apply (metis Group.nat_pow_0 R.Pring_one_eq)
      using nat_pow_def 
      by (metis R.Pring_mult_eq R.Pring_one add_2_eq_Suc')
  qed
  then show ?thesis 
    using "0" by presburger
qed

lemma ring_cfs_to_poly_decomp:
  assumes "as \<in> carrier (R\<^bsup>Suc (Suc n)\<^esup>)"
  shows "ring_cfs_to_poly R (Suc n) as = ring_cfs_to_poly R n as \<oplus>\<^bsub>coord_ring R 1\<^esub>
        poly_scalar_mult R (as!(Suc n)) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n))"
proof-
  have LHS: "ring_cfs_to_poly R (Suc n) as = 
              coord_partial_eval R {1..<Suc n + 2} (\<zero> # as) (generic_poly R n \<oplus>\<^bsub>coord_ring R (Suc (Suc (Suc n)))\<^esub> generic_poly_lt R (Suc n))" 
    by (smt add_2_eq_Suc' add_Suc_right generic_poly.simps(2) numeral_2_eq_2 numeral_3_eq_3 ring_cfs_to_poly_def)   
  have LHS': "ring_cfs_to_poly R (Suc n) as = 
              coord_partial_eval R {1..<Suc n + 2} (\<zero> # as) (generic_poly R n) \<oplus>\<^bsub>coord_ring R (Suc (Suc (Suc n)))\<^esub> 
              coord_partial_eval R {1..<Suc n + 2} (\<zero> # as) (generic_poly_lt R (Suc n))" 
    using coord_partial_eval_add[of as "Suc n"]    
    by (metis LHS add_2_eq_Suc' add_Suc_shift assms cartesian_power_cons 
        coord_partial_eval_add generic_poly_closed' generic_poly_lt_closed le_add2 plus_1_eq_Suc R.zero_closed) 
  have LHS'': "ring_cfs_to_poly R (Suc n) as = 
              coord_partial_eval R {1..<Suc n + 2} (\<zero> # as) (generic_poly R n) \<oplus>\<^bsub>coord_ring R (Suc (Suc (Suc n)))\<^esub> 
              coord_partial_eval R {1..<Suc n + 2} (\<zero> # as) (generic_poly_lt R (Suc n))" 
    using coord_partial_eval_add[of as "Suc n"]    
    by (metis LHS add_2_eq_Suc' add_Suc_shift assms cartesian_power_cons 
        coord_partial_eval_add generic_poly_closed' generic_poly_lt_closed le_add2 plus_1_eq_Suc R.zero_closed)
  have LHS''': "ring_cfs_to_poly R (Suc n) as =
              coord_partial_eval R {1..<Suc n + 2} (\<zero> # as) (generic_poly R n) \<oplus>\<^bsub>coord_ring R (Suc (Suc (Suc n)))\<^esub>  
              poly_scalar_mult R (as! (Suc n)) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n))" 
    using LHS'' coord_partial_eval_generic_poly_lt'[of as "Suc n"] assms 
    by presburger
  have 0: "coord_partial_eval R {1..<Suc n + 2} (\<zero> # as) (generic_poly R n) = ring_cfs_to_poly R n as"
  proof-
    have 00: "(generic_poly R n) \<in> carrier (coord_ring R (n + 2))"
      using add_2_eq_Suc' generic_poly_closed by presburger      
    have 01: "\<one> \<noteq> \<zero>"
      using one_neq_zero
      by presburger
    have 02: "(\<zero> # as) \<in> carrier (R\<^bsup>Suc (Suc n) + 1\<^esup>)"
      using cartesian_power_cons[of as R "Suc (Suc n)" \<zero>] assms 
      by blast
    have 03: "closed_fun R (point_to_eval_map R (\<zero> # as))"
      using point_to_eval_map_closed[of "\<zero>#as" "Suc (Suc (Suc n))"] 
      by (metis "02" Suc_eq_plus1)     
    have 04: "{1..<Suc n + 2} \<inter> {..<n + 2} = {1..<n + 2} \<inter> {..<n + 2}"
      by auto 
    show ?thesis
      unfolding ring_cfs_to_poly_def coord_partial_eval_def 
      using 04 03 02 01 00 R.Pring_car[of "{..<n + 2}"] assms 
            R.poly_eval_eval_set_eq[of "point_to_eval_map R (\<zero> # as)" "{1..<Suc n + 2}"
                                  "{..<n + 2}" "{1..<n + 2}" "(generic_poly R n)" ] 
      by (metis coord_ring_def)      
  qed
  show ?thesis 
    using generic_poly.simps(2)[of R n] coord_partial_eval_add LHS''' 0 
    unfolding ring_cfs_to_poly_def 
    by (metis R.Pring_add_eq coord_ring_def)   
qed

lemma ring_cfs_to_poly_decomp':
  assumes "as \<in> carrier (R\<^bsup>Suc (Suc n)\<^esup>)"
  shows "ring_cfs_to_poly R (Suc n) as = 
                ring_cfs_to_poly R n (take (Suc n) as) \<oplus>\<^bsub>coord_ring R 1\<^esub>
                poly_scalar_mult R (as!(Suc n)) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n))"
  using assms ring_cfs_to_poly_decomp[of as n] 
        ring_cfs_to_poly_eq[of as "Suc n" n] le_eq_less_or_eq less_Suc_eq 
  by presburger

lemma ring_cfs_to_univ_poly_decomp':
  assumes "as \<in> carrier (R\<^bsup>Suc (Suc n)\<^esup>)"
  shows "ring_cfs_to_univ_poly (Suc n) as = 
                ring_cfs_to_univ_poly n (take (Suc n) as) \<oplus>\<^bsub>UP R\<^esub>
                 (as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n))"
proof-
  have 00: "(pvar R 0 [^]\<^bsub>coord_ring R 1\<^esub> Suc n) \<in> carrier (Pring R {0})"
    using pvar_closed[of 0 1] monoid.nat_pow_closed[of "coord_ring R 1"  _ n ]
    unfolding coord_ring_def 
    by (metis One_nat_def R.Pring_is_monoid lessThan_0 lessThan_Suc less_one monoid.nat_pow_closed)
  have LHS: "ring_cfs_to_univ_poly (Suc n) as = 
      IP_to_UP 0 (ring_cfs_to_poly R n (take (Suc n) as) \<oplus>\<^bsub>coord_ring R 1\<^esub>
                poly_scalar_mult R (as!(Suc n)) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n)))"
    using assms ring_cfs_to_poly_decomp' 
    unfolding ring_cfs_to_univ_poly_def 
    by presburger
  have LHS': "ring_cfs_to_univ_poly (Suc n) as = 
      IP_to_UP 0 (ring_cfs_to_poly R n (take (Suc n) as)) \<oplus>\<^bsub>UP R\<^esub>
      IP_to_UP 0 (poly_scalar_mult R (as!(Suc n)) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n)))"
  proof-
    have 0: " ring_cfs_to_poly R n (take (Suc n) as) \<in> carrier (Pring R {0})"
      by (metis One_nat_def assms coord_ring_def le_add2 lessThan_0 lessThan_Suc plus_1_eq_Suc ring_cfs_to_poly_closed take_closed)      
    have 1: "as ! Suc n \<in> carrier R"
      using assms cartesian_power_car_memE'[of as R "Suc (Suc n)"] 
      by blast
    have 2: "poly_scalar_mult R (as ! Suc n) (pvar R 0 [^]\<^bsub>coord_ring R 1\<^esub> Suc n) \<in> carrier (Pring R {0})"
      using 1 00 R.Pring_car R.poly_scalar_mult_closed[of "(as ! Suc n)" "(pvar R 0 [^]\<^bsub>coord_ring R 1\<^esub> Suc n)" "{0}"] 
      by blast
    then show ?thesis      
      using 0 1 2 UP_cring.IP_to_UP_add[of R "(ring_cfs_to_poly R n (take (Suc n) as))" "0"
              "poly_scalar_mult R (as!(Suc n)) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n))"] 
      by (metis LHS One_nat_def UP_cring_def coord_ring_def R.is_cring lessThan_0 lessThan_Suc)
  qed
  have 0: "IP_to_UP 0 (ring_cfs_to_poly R n (take (Suc n) as)) = 
           ring_cfs_to_univ_poly n  (take (Suc n) as)"
    using ring_cfs_to_univ_poly_def
    by presburger
  have 1: "(mset_to_IP R (nat_to_mset 0 (Suc n))) = (pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n)"
    unfolding coord_ring_def using  lessThan_iff less_one 
    by (metis UP_cring.intro UP_cring.pvar_pow R.is_cring)    
  have 2: "as ! Suc n \<in> carrier R"
    using cartesian_power_car_memE' assms 
    by blast
  have 3: "IP_to_UP 0 (poly_scalar_mult R (as ! Suc n) (pvar R 0 [^]\<^bsub>coord_ring R 1\<^esub> Suc n)) =
    as ! Suc n \<odot>\<^bsub>UP R\<^esub> IP_to_UP 0 (pvar R 0 [^]\<^bsub>coord_ring R 1\<^esub> Suc n)"   
    using UP_cring.IP_to_UP_scalar_mult[of R "as!(Suc n)" "((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n))" 0]
          "00" "2" unfolding coord_ring_def 
    by (metis R.Pring_smult UP_cring.intro R.is_cring)                  
  have 4: "IP_to_UP 0 (poly_scalar_mult R (as!(Suc n)) ((pvar R 0)[^]\<^bsub>coord_ring R 1\<^esub> (Suc n)))
            = (as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n))"
  proof -
    have "as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> Suc n = IP_to_UP (0::nat) (Mt (as ! Suc n) (nat_to_mset 0 (Suc n)))"
      using 3 1 UP_cring.IP_to_UP_monom
      by (metis UP_cring.intro R.is_cring)      
    then show ?thesis
      using \<open>mset_to_IP R (nat_to_mset 0 (Suc n)) = pvar R 0 [^]\<^bsub>coord_ring R 1\<^esub> Suc n\<close> 
      by presburger
  qed
  then show ?thesis 
    using "0" LHS' 
    by presburger
qed

lemma ring_cfs_to_univ_poly_decomp:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  assumes "k < n"
  shows "ring_cfs_to_univ_poly (Suc k) (take (Suc (Suc k)) as) = ring_cfs_to_univ_poly k (take (Suc k) as) 
                              \<oplus>\<^bsub>UP R\<^esub> (as!(Suc k)) \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (Suc k)"
proof- 
  have 0: "(take (Suc (Suc k)) as) \<in> carrier (R\<^bsup>Suc (Suc k)\<^esup>)"
    using assms  
    by (meson Suc_leI Suc_mono take_closed)
  then show ?thesis using ring_cfs_to_univ_poly_decomp'[of "take (Suc (Suc k)) as" k]
    by (metis (no_types, lifting) Suc_leI assms(1) assms(2) cartesian_power_car_memE 
        lessI less_SucI nth_take nth_take_lemma)
qed

lemma ring_cfs_to_univ_poly_degree:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows  "deg R (ring_cfs_to_univ_poly n as) \<le> n"
         "as!n \<noteq> \<zero> \<Longrightarrow> deg R (ring_cfs_to_univ_poly n as) = n"
proof-
  have 0:"\<And>as. as \<in> carrier (R\<^bsup>Suc n\<^esup>)  \<Longrightarrow> 
              deg R (ring_cfs_to_univ_poly n as) \<le> n \<and> (as!n \<noteq> \<zero> \<longrightarrow> deg R (ring_cfs_to_univ_poly n as) = n)"
  proof(induction n)
    case 0
    show "\<And>as. as \<in> carrier (R\<^bsup>Suc 0\<^esup>) \<Longrightarrow>
          deg R (ring_cfs_to_univ_poly 0 as) \<le> 0 \<and>
          (as ! 0 \<noteq> \<zero> \<longrightarrow> deg R (ring_cfs_to_univ_poly 0 as) = 0)"
    proof-
      fix as assume A: "as \<in> carrier (R\<^bsup>Suc 0\<^esup>)"
      have 0:"cring R"
        by (simp add: R.is_cring)
      have 1:"\<zero> # as \<in> carrier (R\<^bsup>2\<^esup>)"
        using A cartesian_power_cons[of as R "Suc 0" \<zero>] 
        by (metis numeral_1_eq_Suc_0 numeral_One one_add_one R.zero_closed)
      have 2: "(\<zero> # as) ! 1 = as!0"
        using A 
        by (metis One_nat_def nth_Cons_Suc)
      have 3: "1 \<in> {(1::nat)..<0 + 2} \<inter> {..<2}"
        by auto 
      have 4: "coord_partial_eval R {1::nat..<0 + 2} (\<zero> # as) (pvar R (1::nat)) =
                 R.indexed_const (as!0)"
      unfolding ring_cfs_to_univ_poly_def ring_cfs_to_poly_def
        using 0 1 2 one_neq_zero UP_cring.IP_to_UP_indexed_const[of R "as!0" 0]  generic_poly.simps(1)[of R] coord_partial_eval_pvar[of "\<zero>#as" 2 "1::nat" "{1..<0+2}" ]
        unfolding UP_cring_def  
        using "3" by presburger
      have 5: "ring_cfs_to_univ_poly 0 as = IP_to_UP (0::nat) (R.indexed_const (as ! 0))"
        unfolding ring_cfs_to_univ_poly_def ring_cfs_to_poly_def 
        using 4 generic_poly.simps(1)[of R]  
        by presburger
      hence "ring_cfs_to_univ_poly 0 as = to_polynomial R (as!0)"
        by (metis A UP_cring.IP_to_UP_indexed_const UP_cring.intro  
            cartesian_power_car_memE' R.is_cring lessI)
    assume B: "as \<in> carrier (R\<^bsup>Suc 0\<^esup>) "
    have 0: "(point_to_eval_map R (\<zero> # as) 1) = as!0"
      by (metis B One_nat_def cartesian_power_car_memE impossible_Cons le_numeral_extra(4) 
          linorder_neqE_nat nat_less_le nth_Cons_Suc)
    have 1: "closed_fun R ((point_to_eval_map R (\<zero> # as)))"
      apply(rule R.closed_funI) 
      by (metis "0" B One_nat_def cartesian_power_car_memE cartesian_power_car_memE' 
          length_Suc_conv less_Suc0 less_SucE nth_Cons_0 R.zero_closed)
    have 2: "(1::nat) \<in> ({1..<0 + 2}::nat set)"     
      by simp 
    have 3: "poly_eval R {1..<0 + 2} (point_to_eval_map R (\<zero> # as)) (mset_to_IP R {#1#}) =
              coord_const (point_to_eval_map R (\<zero> # as) 1)"
      using generic_poly.simps(1)[of R] one_neq_zero
      unfolding ring_cfs_to_poly_def  coord_partial_eval_def var_to_IP_def 
      using 0 1 2 R.poly_eval_index[of "(point_to_eval_map R (\<zero> # as))" "{1..<0 + 2}" 1]
      by (metis (no_types, lifting))
    have 4: "(ring_cfs_to_poly R 0 as) = coord_const (as! 0)"
      using 3 0 generic_poly.simps(1)[of R]
      unfolding ring_cfs_to_poly_def  coord_partial_eval_def var_to_IP_def 
      by presburger
    have 5: "as! 0 \<in> carrier R"
      using assms B cartesian_power_car_memE' by blast     
    have 6: "(ring_cfs_to_univ_poly 0 as) = to_polynomial R (as! 0)"
      unfolding ring_cfs_to_univ_poly_def ring_cfs_to_poly_def 
      using 3 4 5 UP_cring.IP_to_UP_indexed_const[of R "as!0" "0::nat"]
      unfolding coord_partial_eval_def 
      by (smt "0" \<open>ring_cfs_to_univ_poly 0 as = to_polynomial R (as ! 0)\<close> generic_poly.simps(1) ring_cfs_to_univ_poly_def var_to_IP_def)     
    then show " deg R (ring_cfs_to_univ_poly 0 as) \<le> 0 \<and> (as ! 0 \<noteq> \<zero> \<longrightarrow> deg R (ring_cfs_to_univ_poly 0 as) = 0)"
      using  UP_cring.degree_to_poly[of R "as! 0"] 5  UP_cring_def[of R]
      using R.is_cring by presburger      
  qed
  next
  case (Suc n)
    have 0: "(ring_cfs_to_univ_poly (Suc n) as) = ring_cfs_to_univ_poly n (take (Suc n) as) \<oplus>\<^bsub>UP R\<^esub>
                 (as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n))"
    using ring_cfs_to_univ_poly_decomp' Suc.prems by blast
   have 1: "(take (Suc n) as) \<in> carrier (R\<^bsup>Suc n\<^esup>)"
    using Suc.prems
    by (meson le_Suc_eq take_closed)
   have 2: "deg R (ring_cfs_to_univ_poly n (take (Suc n) as)) \<le> n"
    using "1" Suc.IH 
    by blast
   have 3: "deg R ((as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n))) \<le> Suc n"
    using UP_cring.degree_monom[of R "as!(Suc n)" "Suc n"] UP_cring_def[of R] 
    Suc.prems cartesian_power_car_memE' le_Suc_eq lessI less_imp_le_nat zero_less_Suc
    by (metis R.is_cring)
  have 4: "(X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)) \<in> carrier (UP R)"
  proof-
    have 40: "Group.monoid (UP R)" 
      using UP_cring_def[of R] UP_domain_def cring.axioms(1) ring.is_monoid
      using UP_cring.UP_cring R.is_cring by blast
    have 41: "X_poly R \<in> carrier (UP R)"
      using UP_cring.X_closed[of R] UP_cring_def[of R] R.is_cring 
      by blast 
    show ?thesis
      using monoid.nat_pow_closed[of "UP R" "X_poly R" "Suc n"] 40 41 
      by blast 
  qed
  have 5: "deg R (ring_cfs_to_univ_poly (Suc n) as) \<le>Suc n"
  proof(cases "as!(Suc n) = \<zero>")
    case True
    then have T0: "(as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)) = \<zero>\<^bsub>UP R\<^esub>"
      using 4 UP_ring.UP_smult_zero[of R "X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)"] UP_ring_def[of R] R.ring_axioms 
      by presburger
    then show ?thesis 
      using UP_ring.deg_zero[of R] UP_ring_def[of R]  
      by (metis "0" "1" "2" "3" UP_ring.UP_zero_closed UP_ring.bound_deg_sum le_SucI R.ring_axioms ring_cfs_to_univ_poly_closed)        
  next
    case False
    have F0 : "as!(Suc n) \<in> carrier R"
       by (metis Suc.prems cartesian_power_car_memE le_simps(1) lessI not_less_eq_eq poly_tuple_evalE poly_tuple_evalE' pushforward_by_pvar_list pvar_list_is_poly_tuple zero_less_Suc)     
    have F1: "(as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)) \<in> carrier (UP R)"
      using F0 4 UP_ring.UP_smult_closed[of R "as!(Suc n)" "X_poly R [^]\<^bsub>UP R\<^esub> Suc n "] 
            UP_ring_def[of R] assms R.ring_axioms 
      by blast
    have "deg R ((as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n))) = Suc n"
      using False UP_cring.degree_monom[of R "as!(Suc n)" "Suc n"] UP_cring_def[of R]
         cartesian_power_car_memE' lessI 
      using F0 R.is_cring 
      by presburger            
    then show ?thesis 
      using UP_ring.degree_of_sum_diff_degree[of R "(as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n))"
               "ring_cfs_to_univ_poly n (take (Suc n) as)"] 1 2 4 UP_domain_def[of R] F1
              ring_cfs_to_univ_poly_closed[of "take (Suc n) as" "Suc n"]  "0" "3"
              UP_ring_def[of R] UP_cring_def[of R] 
              UP_ring.equal_deg_sum less_Suc_eq_le ring_cfs_to_univ_poly_closed
      by (metis R.ring_axioms)
  qed
  have 6: "(as ! (Suc n) \<noteq> \<zero> \<longrightarrow> deg R (ring_cfs_to_univ_poly (Suc n) as) = Suc n)"
    proof 
    assume F: "as ! (Suc n) \<noteq> \<zero> "
    have F0 : "as!(Suc n) \<in> carrier R"
      by (metis Suc.prems cartesian_power_car_memE le_simps(1) lessI not_less_eq_eq poly_tuple_evalE poly_tuple_evalE' pushforward_by_pvar_list pvar_list_is_poly_tuple zero_less_Suc)     
    have F1: "(as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)) \<in> carrier (UP R)"
      using F0 4 UP_ring.UP_smult_closed[of R "as!(Suc n)" "X_poly R [^]\<^bsub>UP R\<^esub> Suc n "] 
            UP_ring_def[of R] assms R.ring_axioms 
      by blast
    then have F2: "deg R ((as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc n))) = Suc n"
      using F0 F UP_cring.degree_monom[of R "as!(Suc n)" "Suc n"] UP_cring_def[of R] R.is_cring 
      by presburger
    have F3: "ring_cfs_to_univ_poly n (take (Suc n) as) \<in> carrier (UP R)"
      using "1" ring_cfs_to_univ_poly_closed 
      by blast
    show "deg R (ring_cfs_to_univ_poly (Suc n) as) = Suc n"
      using UP_domain_def[of R] 0 F1 F2 F3 1 2 
            UP_ring.degree_of_sum_diff_degree[of R "ring_cfs_to_univ_poly n (take (Suc n) as)" 
                                                "as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> Suc n"] 
      UP_ring.equal_deg_sum le_imp_less_Suc UP_ring_def[of R] UP_cring_def[of R]
  by (metis R.ring_axioms)
  qed
  show ?case 
    using "5" "6" by blast
  qed
  show "deg R (ring_cfs_to_univ_poly n as) \<le> n"
    using 0 assms 
    by blast
  show "as ! n \<noteq> \<zero> \<Longrightarrow> deg R (ring_cfs_to_univ_poly n as) = n"
    using 0 assms 
    by blast
qed

lemma ring_cfs_to_univ_poly_constant:
  assumes "as \<in> carrier (R\<^bsup>1\<^esup>)"
  shows "ring_cfs_to_univ_poly 0 as = to_polynomial R (as!0)"
proof-
  have 0: "(1::nat) \<in> {1..<0 + 2}" 
    by simp 
  have 1: "closed_fun R (point_to_eval_map R (\<zero> # as))"
    using assms 
    by (smt cartesian_power_car_memE'' R.closed_funI nth_mem set_ConsD subset_code(1) R.zero_closed)    
  have 2: "(point_to_eval_map R (\<zero> # as) (1::nat)) = as!0"
    by (metis One_nat_def assms cartesian_power_car_memE impossible_Cons
      le_numeral_extra(4) linorder_neqE_nat nat_less_le nth_Cons_Suc)
  have 3: "as!0 \<in> carrier R"
    using assms cartesian_power_car_memE' 
    by blast
  have "(poly_eval R {1::nat..<0 + 2} (point_to_eval_map R (\<zero> # as)) (generic_poly R 0)) = coord_const (point_to_eval_map R (\<zero> # as) 1)"
    using generic_poly.simps(1)[of R] 0 1 one_not_zero 
          cring.poly_eval_index[of R "point_to_eval_map R (\<zero> # as)" "{1..<0 + 2}" 1]
    unfolding var_to_IP_def 
    using R.is_cring local.one_neq_zero by presburger   
  then have "(poly_eval R {1..<0 + 2} (point_to_eval_map R (\<zero> # as)) (generic_poly R 0)) = coord_const (as!0)"
    using 2 
    by presburger
  then show ?thesis 
    using 3
    unfolding ring_cfs_to_univ_poly_def ring_cfs_to_poly_def coord_partial_eval_def 
    by (metis UP_cring.IP_to_UP_indexed_const UP_cring.intro R.is_cring)
qed

lemma ring_cfs_to_univ_poly_top_coeff:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "(ring_cfs_to_univ_poly n as) n = as ! n"
  proof(cases "n = 0")
    case True
    have 0: "as ! 0 \<in> carrier R"
      using assms cartesian_power_car_memE' 
      by blast
    have 1: "to_polynomial R (as ! 0)  0 = as ! 0"
      using assms cartesian_power_car_memE'[of as R "Suc n"] UP_ring.cfs_monom[of R]
      unfolding to_polynomial_def UP_ring_def
      using "0" R.ring_axioms by presburger
    have "ring_cfs_to_univ_poly 0 as = to_polynomial R (as ! 0)"
      using One_nat_def True assms ring_cfs_to_univ_poly_constant by presburger      
    then show ?thesis 
      using True 1 
      by presburger
  next
    case False
    obtain k where k_def: "Suc k = n"
      using False 
      by (metis lessI less_Suc_eq_0_disj)
    have "ring_cfs_to_univ_poly (Suc k) as (Suc k) = as ! (Suc k)"
    proof-
      have 0: "ring_cfs_to_univ_poly (Suc k) as n = ring_cfs_to_univ_poly (Suc k) (take (Suc (Suc k))as) n"
        by (metis assms(1) k_def le_Suc_eq ring_cfs_to_poly_eq ring_cfs_to_univ_poly_def)
      have 1: "take (Suc (Suc k)) as \<in> carrier (R\<^bsup>Suc (Suc k)\<^esup>)"
        using assms k_def take_closed 
        by blast
      have 2: "ring_cfs_to_univ_poly (Suc k) (take (Suc (Suc k))as) = 
                ring_cfs_to_univ_poly k (take (Suc k) (take (Suc (Suc k)) as)) \<oplus>\<^bsub>UP R\<^esub>  (as!(Suc k))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc k))"
        using 1 ring_cfs_to_univ_poly_decomp'[of "take (Suc (Suc k))as" k] assms  
        by (metis cartesian_power_car_memE k_def nat_le_linear take_all)
      have 3: "ring_cfs_to_univ_poly (Suc k) (take (Suc (Suc k))as) = 
                ring_cfs_to_univ_poly k (take (Suc k) as) \<oplus>\<^bsub>UP R\<^esub>  (as!(Suc k))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc k))"
        using 2  
        by (metis assms(1) k_def le_Suc_eq ring_cfs_to_poly_eq ring_cfs_to_univ_poly_decomp' ring_cfs_to_univ_poly_def)
      have 4: "deg R (ring_cfs_to_univ_poly k (take (Suc k) as)) \<le> k"
        by (metis assms(1) dual_order.refl k_def le_SucI ring_cfs_to_univ_poly_degree(1) take_closed)
      have 5: "(ring_cfs_to_univ_poly k (take (Suc k) as)) \<in> carrier (UP R)"
        by (metis assms(1) k_def le_Suc_eq le_refl ring_cfs_to_univ_poly_closed take_closed)
      have  6: "X_poly R [^]\<^bsub>UP R\<^esub> Suc k \<in> carrier (UP R)"
        using monoid.nat_pow_closed[of "UP R" "X_poly R" "Suc k"]  domain_def ring.is_monoid[of "UP R"] 
              UP_cring.X_closed[of R] UP_domain_def[of R]  UP_cring_def[of R] 
              cring.axioms(1)   UP_cring.UP_cring 
        using R.is_cring by blast
      have 7: " (as!(Suc k))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc k)) \<in> carrier (UP R)"
        using UP_ring.UP_smult_closed[of R "as!(Suc k)" " (X_poly R [^]\<^bsub>UP R\<^esub> (Suc k))"]
              UP_ring_def[of R] domain_def 6 cartesian_power_car_memE'[of as R _ "Suc k"] 
               assms(1) k_def R.ring_axioms by blast         
      have 8:  "ring_cfs_to_univ_poly (Suc k) as (Suc k) = ( (as!(Suc k))\<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> (Suc k))) (Suc k)"
        using 3 4 k_def 
            "5"  7  UP_cring_def[of R] UP_ring_def[of R] add.r_cancel_one' assms(1)
            cartesian_power_car_memE  le_eq_less_or_eq 
            le_imp_less_Suc take_all R.zero_closed  UP_ring.UP_a_comm UP_ring.coeff_of_sum_diff_degree0 R.ring_axioms
        by (metis (no_types, lifting))          
      then show ?thesis using UP_cring_def[of R]  UP_cring.monom_coeff assms(1) cartesian_power_car_memE
            k_def lessI point_to_eval_map_closed 
        by (metis (no_types, lifting) cartesian_power_car_memE' R.is_cring)        
    qed 
    then show ?thesis 
      using k_def False 
      by blast
  qed

lemma(in UP_cring) monom_plus_lower_degree_top_coeff:
  assumes "degree  p < n"
  assumes "p \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "(p \<oplus>\<^bsub>UP R\<^esub> (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> n)) n = a"
proof-
  have 0: "(a \<odot>\<^bsub>UP R\<^esub> (X_poly R [^]\<^bsub>UP R\<^esub> n)) \<in> carrier (UP R)"
    using P.nat_pow_closed P_def X_closed assms(3) smult_closed 
    by blast
  have 1: "( (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> n) \<oplus>\<^bsub>UP R\<^esub> p) n = (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> n) n"
    using "0" UP_ring.coeff_of_sum_diff_degree0[of R] UP_cring_def[of R] assms(1) assms(2)   
    using is_UP_ring by blast
  then show ?thesis 
    using 0 assms  P_def UP_a_comm  UP_cring.monom_coeff  UP_cring_def[of R]
    by (metis R_cring)
qed

lemma(in UP_cring) monom_closed:
  assumes "a \<in> carrier R"
  shows "a \<odot>\<^bsub>UP R\<^esub> ((X_poly R)[^]\<^bsub>UP R\<^esub> (n::nat)) \<in> carrier (UP R)"
  using P.nat_pow_closed P_def assms X_closed carrier_is_submodule submoduleE(4)
  by blast

lemma(in UP_cring) monom_bottom_coeff:
  assumes "a \<in> carrier R"
  assumes "n > 0"
  shows "(a \<odot>\<^bsub>UP R\<^esub> ((X_poly R)[^]\<^bsub>UP R\<^esub> (n::nat))) 0 = \<zero>"
  using assms monom_coeff[of a n]  P_def local.monom_coeff 
  by presburger

lemma(in UP_cring) monom_plus_lower_degree_bottom_coeff:
  assumes "0 < n"
  assumes "p \<in> carrier (UP R)"
  assumes "a \<in> carrier R"
  shows "(p \<oplus>\<^bsub>UP R\<^esub> (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (n::nat))) 0 = p 0"
proof-
  have 0: "p 0 \<in> carrier R"
    using assms(2) UP_ring_def is_UP_ring P_def cfs_closed by blast    
  have 1: "(p \<oplus>\<^bsub>UP R\<^esub> (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (n::nat))) 0 = p 0 \<oplus> (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> n) 0"
    using assms monom_closed[of a n] cfs_add[of p "(a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (n::nat))" 0]
    unfolding P_def   
    by blast
  then have "(a \<odot>\<^bsub>UP R\<^esub> ((X_poly R) [^]\<^bsub>UP R\<^esub> n)) 0 = \<zero>"
    using monom_bottom_coeff[of a n] P_def assms(1) assms(3) local.monom_coeff 
    by blast   
  then have 2: "(p \<oplus>\<^bsub>UP R\<^esub> (a \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (n::nat))) 0 = p 0 \<oplus> \<zero>"
    using 1 by metis 
  then show ?thesis 
    using 0  R.add.l_cancel_one[of "p 0"] R.zero_closed 
    by presburger
qed

lemma ring_cfs_to_univ_poly_bottom_coeff:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "(ring_cfs_to_univ_poly n as) 0 = as ! 0"
proof-
  have "\<And>as. as \<in> carrier (R\<^bsup>Suc n\<^esup>) \<Longrightarrow> (ring_cfs_to_univ_poly n as) 0 = as ! 0"
    apply(induction n)
    using ring_cfs_to_univ_poly_top_coeff apply blast
  proof-
    fix n as 
    assume IH: "\<And>as. as \<in> carrier (R\<^bsup>Suc n\<^esup>) \<Longrightarrow> (ring_cfs_to_univ_poly n as) 0 = as ! 0"
    assume A: "as \<in> carrier (R\<^bsup>Suc (Suc n)\<^esup>)"
    show "ring_cfs_to_univ_poly (Suc n) as 0 = as ! 0"
    proof-
      have 0: "ring_cfs_to_univ_poly (Suc n) as = ring_cfs_to_univ_poly n (take (Suc n) as) \<oplus>\<^bsub>UP R\<^esub> (as!(Suc n))\<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (Suc n)"
        using A ring_cfs_to_univ_poly_decomp'[of as n] 
        by blast
      have 1: "ring_cfs_to_univ_poly n (take (Suc n) as) \<in> carrier (UP R)"
       by (meson A ring_cfs_to_univ_poly_closed R.is_cring le_Suc_eq take_closed)
     have 2:"as ! Suc n \<in> carrier R"
       using assms cartesian_power_car_memE'  A 
       by blast
     have 3: "(ring_cfs_to_univ_poly n (take (Suc n) as) \<oplus>\<^bsub>UP R\<^esub> as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)) 0 =
              ring_cfs_to_univ_poly n (take (Suc n) as) 0"
     proof-
       have "as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> Suc n \<in> carrier (UP R)"
         by (meson "2" UP_cring.monom_closed UP_cring_def R.is_cring)
       hence 30: "(ring_cfs_to_univ_poly n (take (Suc n) as) \<oplus>\<^bsub>UP R\<^esub> as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)) 0 = 
        (ring_cfs_to_univ_poly n (take (Suc n) as)) 0 \<oplus> (as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)) 0"
         using A ring_cfs_to_univ_poly_closed[of "take (Suc n) as" "n"] take_closed[of "Suc n" "Suc (Suc n)" as R]
              UP_ring.cfs_add[of R "ring_cfs_to_univ_poly n (take (Suc n) as)" "as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> (Suc n)"  0]
         unfolding UP_ring_def 
         using "1" R.ring_axioms by blast
       have 31: "(as ! Suc n \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> Suc n) 0 = \<zero>"
         by (metis (no_types, lifting) "2" Suc_neq_Zero UP_cring.monom_coeff UP_cring_def R.is_cring)
       thus ?thesis using  30 2 
         by (simp add: "1" UP_car_memE(1))         
     qed
     have 4: "(take (Suc n) as) \<in> carrier (R\<^bsup>Suc n\<^esup>)"
       by (meson A le_Suc_eq take_closed)
     have 5: "ring_cfs_to_univ_poly n (take (Suc n) as) 0 = as!0"
       using IH[of "(take (Suc n) as)"] 4 nth_take[of 0 "Suc n" as] less_Suc_eq_0_disj 
       by presburger
     then show ?thesis 
        using 0 3 
        by presburger
    qed   
  qed
  then show ?thesis 
    using assms 
    by blast
qed

lemma ring_cfs_to_univ_poly_chain:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  assumes "l \<le> n"
  shows "l \<le> k \<and> k \<le> n  \<Longrightarrow> (ring_cfs_to_univ_poly k (take (Suc k) as)) l = (ring_cfs_to_univ_poly l (take (Suc l) as)) l"
  apply( induction k)
   apply blast
proof-
  fix k 
  assume IH: "(l \<le> k \<and> k \<le> n \<Longrightarrow> ring_cfs_to_univ_poly k (take (Suc k) as) l = ring_cfs_to_univ_poly l (take (Suc l) as) l)"
  assume A: "l \<le> Suc k \<and> Suc k \<le> n"
  show "ring_cfs_to_univ_poly (Suc k) (take (Suc (Suc k)) as) l = ring_cfs_to_univ_poly l (take (Suc l) as) l"
  proof(cases "l = Suc k")
    case True
    then show ?thesis 
      by blast
  next
    case False
    then have "l \<le> k \<and> k \<le> n " 
      using A le_Suc_eq 
      by blast
    then have 0: " ring_cfs_to_univ_poly k (take (Suc k) as) l = ring_cfs_to_univ_poly l (take (Suc l) as) l"
      using IH 
      by blast
    have 1: "ring_cfs_to_univ_poly (Suc k) (take (Suc (Suc k)) as) = ring_cfs_to_univ_poly k (take (Suc k) as) 
                              \<oplus>\<^bsub>UP R\<^esub> (as!(Suc k)) \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (Suc k)"
      using assms A ring_cfs_to_univ_poly_decomp[of as n k] Suc_le_lessD 
      by blast
    have 2: "ring_cfs_to_univ_poly (Suc k) (take (Suc (Suc k)) as) l = ring_cfs_to_univ_poly k (take (Suc k) as) l 
                              \<oplus>( (as!(Suc k)) \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (Suc k)) l"
    proof-
      have 21: "ring_cfs_to_univ_poly k (take (Suc k) as) \<in> carrier (UP R)"
        by (meson A assms(1) le_SucI ring_cfs_to_univ_poly_closed take_closed)
      have 22: "as ! Suc k \<odot>\<^bsub>UP R\<^esub> X_poly R [^]\<^bsub>UP R\<^esub> Suc k \<in> carrier (UP R)"
        using UP_ring_def[of R] A UP_ring.monom_closed assms(1) cartesian_power_car_memE' less_Suc_eq_le
              monoid.nat_pow_closed[of "UP R" "X_poly R" "Suc k"] 
        unfolding X_poly_def 
        by (metis UP_ring.UP_ring UP_ring.UP_smult_closed R.ring_axioms R.one_closed ring.is_monoid)
      show ?thesis 
        using 1 21 22 UP_ring.cfs_add[of R "ring_cfs_to_univ_poly k (take (Suc k) as)" "( (as!(Suc k)) \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (Suc k))" l]
        UP_ring_def[of R] R.ring_axioms by presburger 
    qed
    have 3: "( (as!(Suc k)) \<odot>\<^bsub>UP R\<^esub> (X_poly R)[^]\<^bsub>UP R\<^esub> (Suc k)) l = \<zero>"
      using UP_cring.monom_coeff[of R "as!(Suc k)"]  A False UP_cring_def assms(1) cartesian_power_car_memE' 
      by (metis R.is_cring le_imp_less_Suc)
    then show ?thesis 
      using 2 
      by (metis "0" Suc_le_mono assms(1) assms(2) cartesian_power_car_memE' lessI R.r_zero 
          ring_cfs_to_univ_poly_top_coeff take_closed)
  qed
qed

lemma ring_cfs_to_univ_poly_coeffs:
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  assumes "l \<le> n"
  shows "(ring_cfs_to_univ_poly n as) l = (ring_cfs_to_univ_poly l (take (Suc l) as)) l"
proof-
  have "(take (Suc n) as) = as"
    using assms 
    by (metis cartesian_power_car_memE le_refl take_all)
  then show ?thesis 
    using ring_cfs_to_univ_poly_chain[of as n l n]
    by (metis assms(1) assms(2) order_refl)
qed

lemma ring_cfs_to_univ_poly_coeffs':
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  assumes "l \<le> n"
  shows "(ring_cfs_to_univ_poly n as) l = as! l"
proof-
  have 0: "(ring_cfs_to_univ_poly l (take (Suc l) as)) l = (take (Suc l) as) ! l"
    by (meson Suc_le_mono assms(1) assms(2) ring_cfs_to_univ_poly_top_coeff take_closed)
  have 1: "(take (Suc l) as) ! l = as! l"
    using nth_take[of l "Suc l" as] 
    by blast
  then show ?thesis
    using 0 assms ring_cfs_to_univ_poly_coeffs[of as n l] 
    by presburger
qed

lemma ring_cfs_to_univ_poly_coeffs'':
  assumes "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  shows "(ring_cfs_to_univ_poly n as) l = (if l \<le> n then as! l else \<zero>)"
  apply(cases "l \<le>n")
  apply (meson assms ring_cfs_to_univ_poly_coeffs')
proof- assume "\<not> l \<le> n " then 
  have A: "n < l" 
    by auto 
  have "deg R (ring_cfs_to_univ_poly n as) \<le> n"
    using assms ring_cfs_to_univ_poly_degree(1) by blast    
  then show ?thesis 
    using A domain_def[of R]  deg_leE  assms le_less_trans ring_cfs_to_univ_poly_closed UP_car_memE(2) 
    by auto
qed
end

definition fun_tuple_to_univ_poly where
"fun_tuple_to_univ_poly R n m fs x = cring_coord_rings.ring_cfs_to_univ_poly R m (function_tuple_eval R n fs x)"

context cring_coord_rings
begin

lemma  fun_tuple_to_univ_poly_closed:
  assumes "is_function_tuple R n fs"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "length fs = Suc m"
  shows "fun_tuple_to_univ_poly R n m fs x \<in> carrier (UP R)"
  unfolding fun_tuple_to_univ_poly_def 
  using assms 
        ring_cfs_to_univ_poly_closed[of "function_tuple_eval R n fs x" m] 
        function_tuple_eval_closed[of R n fs x] 
  by metis 

lemma  fun_tuple_to_univ_poly_degree_bound:
  assumes "is_function_tuple R n fs"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "length fs = Suc m"
  shows "deg R (fun_tuple_to_univ_poly R n m fs x) \<le> m"
  unfolding fun_tuple_to_univ_poly_def 
  using ring_cfs_to_univ_poly_degree assms 
  by (metis function_tuple_eval_closed)

lemma  fun_tuple_to_univ_poly_degree:
  assumes "is_function_tuple R n fs"
  assumes "x \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "length fs = Suc m"
  assumes "(fs!m) x \<noteq>\<zero>"
  shows "deg R (fun_tuple_to_univ_poly R n m fs x) = m"
  unfolding fun_tuple_to_univ_poly_def 
  using ring_cfs_to_univ_poly_degree[of "function_tuple_eval R n fs x" m] 
        assms 
        function_tuple_eval_def
        function_tuple_eval_closed[of R n fs x]
  by (metis lessI nth_map)

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Factoring a Polynomial as a Univariate Polynomial over a Multivariable Polynomial Ring\<close>
(**************************************************************************************************)
(**************************************************************************************************)

definition pre_to_univ_poly_hom :: "nat \<Rightarrow> nat \<Rightarrow> ('a, (('a, nat) mvar_poly, nat) mvar_poly) ring_hom" where
"pre_to_univ_poly_hom n i= MP.indexed_const (n-1) \<circ>
                                    R.indexed_const"

lemma pre_to_univ_poly_hom_is_hom:
  assumes "i < n"
  shows "ring_hom_ring R (Pring (coord_ring R (n-1)) {i}) (pre_to_univ_poly_hom n i)"
  using ring_hom_trans[of R.indexed_const R "coord_ring R (n-1)" 
                          "ring.indexed_const(Pring R ({..<n-1}))"
                          "Pring (coord_ring R (n-1)) {i}"]
                        R.indexed_const_ring_hom[of "{..<n-1}"]                      
                        MP.indexed_const_ring_hom[of n "{..<n-1}"]
                        ring_hom_ring.homh[of R "coord_ring R (n - 1)" "coord_const"]
  unfolding ring_hom_ring_def[of R] 
  by (smt MP.Pring_is_ring MP.indexed_const_ring_hom coord_ring_def pre_to_univ_poly_hom_def ring_hom_ring.homh ring_hom_ring_axioms_def)
  
definition pre_to_univ_poly_var_ass :: 
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (('a, nat) mvar_poly, nat) mvar_poly" where
"pre_to_univ_poly_var_ass n i j =(if j < i then MP.indexed_const (n-1) (pvar R j) else 
                                   (if j = i then pvar (coord_ring R (n-1)) i else 
                                   (if j < n then MP.indexed_const (n-1) (pvar R (j - 1)) else 
                                    \<zero>\<^bsub>Pring (coord_ring R (n-1)) {i}\<^esub>)))"

lemma pre_to_univ_poly_var_ass_closed: 
  assumes "i < n"
  shows "closed_fun (Pring (coord_ring R (n-1)) {i}) (pre_to_univ_poly_var_ass n i)"
proof fix j
  show "pre_to_univ_poly_var_ass n i j \<in> carrier (Pring (coord_ring R (n - 1)) {i})"
    unfolding pre_to_univ_poly_var_ass_def 
    apply(cases "j < i")
    using pvar_closed[of j n] assms cring.indexed_const_closed 
    apply (metis (no_types, lifting) R.Pring_is_cring Suc_diff_1 Suc_le_eq coord_ring_def diff_diff_cancel R.is_cring less_imp_diff_less local.pvar_closed not_less0 not_less_eq_eq)    
    apply(cases "j = i")
    using assms apply (meson pvar_closed R.Pring_is_cring R.is_cring singletonI)    
    apply(cases "j < n")
    using pvar_closed[of "j-1" n] assms MP.indexed_const_closed R.Pring_is_cring Suc_diff_1 Suc_le_eq coord_ring_def R.is_cring pvar_closed neq0_conv not_le
      apply (metis MP.Pring_var_closed singletonI)
    using MP.Pring_is_ring[of "n-1" "{i}"] apply blast
  by (smt MP.Pring_zero_closed MP.indexed_const_closed Suc_diff_1 Suc_le_eq le_eq_less_or_eq less_Suc_eq local.pvar_closed nat_induct) 
qed

lemma pre_to_univ_poly_var_ass_closed': 
  assumes "i < n"
  shows "(pre_to_univ_poly_var_ass n i) \<in> {..<n} \<rightarrow> carrier (Pring (coord_ring R (n-1)) {i})"
  by (metis (no_types, lifting) Pi_iff UNIV_I assms pre_to_univ_poly_var_ass_closed)

definition pre_to_univ_poly :: 
  "nat \<Rightarrow> nat \<Rightarrow> (('a, nat) mvar_poly, (('a, nat) mvar_poly, nat) mvar_poly) ring_hom" where
"pre_to_univ_poly (n::nat) (i::nat) = indexed_poly_induced_morphism {..<n} (Pring (coord_ring R (n-1)) {i})
                                                         (pre_to_univ_poly_hom n i)
                                                         (pre_to_univ_poly_var_ass n i)"

lemma pre_to_univ_poly_is_hom:
  assumes "i < n"
  assumes "\<psi> = pre_to_univ_poly n i"
  shows "ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (Pring (coord_ring R (n-1)) {i}) \<psi> "
        "\<And>j. j < i \<Longrightarrow> \<psi> (pvar R j) = MP.indexed_const (n-1) (pvar R j)"
        "\<psi> (pvar R i) = pvar (coord_ring R (n-1)) i"
        "\<And>j. i < j \<and> j < n \<Longrightarrow> \<psi> (pvar R j) = MP.indexed_const (n-1) (pvar R (j - 1))"
        "\<And>a. a \<in> carrier R \<Longrightarrow> \<psi> (coord_const a) = MP.indexed_const (n-1) (coord_const a)"
        "\<And>p. p \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> pre_to_univ_poly n i p \<in> carrier (Pring (coord_ring R (n-1)) {i})"
proof-
  have 0: "cring (Pring (coord_ring R (n - 1)) {i})"
    using MP.Pring_is_cring coord_cring_cring by blast    
  have 1: "pre_to_univ_poly_var_ass n i \<in> {..<n} \<rightarrow> carrier (Pring (coord_ring R (n - 1)) {i})"
    using Pi_iff assms(1) pre_to_univ_poly_var_ass_closed[of i n]
    by blast
  have 2: "ring_hom_ring R (Pring (coord_ring R (n - 1)) {i}) (pre_to_univ_poly_hom n i)"
    using assms(1) pre_to_univ_poly_hom_is_hom by auto

  show 3:"ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (Pring (coord_ring R (n-1)) {i}) \<psi> "
  using R.Pring_universal_prop(1)[of "(Pring (coord_ring R (n-1)) {i})" "pre_to_univ_poly_var_ass n i"
                                "{..<n}" "pre_to_univ_poly_hom n i" \<psi>] assms 0 1 2
  unfolding pre_to_univ_poly_def 
  by (metis coord_ring_def)
  
  show " \<And>j. j < i \<Longrightarrow>
         \<psi> (pvar R j) = MP.indexed_const (n-1) (pvar R j)"
  proof- 
    fix j assume A: "j < i"
    then have 00: "MP.indexed_const (n - 1) (pvar R j) = pre_to_univ_poly_var_ass n i j "
      unfolding pre_to_univ_poly_var_ass_def by auto
    have 01: "j \<in> {..<n}"
      using assms A by auto
    show "\<psi> (pvar R j) = MP.indexed_const (n-1) (pvar R j)" 
    using R.Pring_universal_prop(2)[of "(Pring (coord_ring R (n-1)) {i})" "pre_to_univ_poly_var_ass n i"
                                "{..<n}" "pre_to_univ_poly_hom n i" \<psi>] assms 0 1 2 01
        MP.is_cring 
    unfolding pre_to_univ_poly_def  00 unfolding coord_ring_def var_to_IP_def  
    by blast
  qed
  show "\<psi> (pvar R i) = pvar (coord_ring R (n - 1)) i"
    using R.Pring_universal_prop[of "(Pring (coord_ring R (n-1)) {i})" "pre_to_univ_poly_var_ass n i"
                                "{..<n}" "pre_to_univ_poly_hom n i" \<psi>] assms 0 1 2
    unfolding pre_to_univ_poly_def  coord_ring_def
    using lessThan_iff less_not_refl pre_to_univ_poly_var_ass_def var_to_IP_def 
    by (metis coord_ring_def)    
  show "\<And>j. i < j \<and> j < n \<Longrightarrow> \<psi> (pvar R j) = MP.indexed_const (n - 1) (pvar R (j - 1))"
    using R.Pring_universal_prop[of "(Pring (coord_ring R (n-1)) {i})" "pre_to_univ_poly_var_ass n i"
                                "{..<n}" "pre_to_univ_poly_hom n i" \<psi>] assms 0 1 2
    unfolding pre_to_univ_poly_def
    using add_diff_inverse_nat lessThan_iff less_diff_conv less_imp_add_positive 
        not_add_less1 pre_to_univ_poly_var_ass_def trans_less_add2 var_to_IP_def 
    by (metis (no_types, lifting) coord_ring_def)    
  show "\<And>a. a \<in> carrier R \<Longrightarrow> \<psi> (R.indexed_const a) = MP.indexed_const (n - 1) (R.indexed_const a)"
    using R.Pring_universal_prop(3)[of "(Pring (coord_ring R (n-1)) {i})" "pre_to_univ_poly_var_ass n i"
                                "{..<n}" "pre_to_univ_poly_hom n i" \<psi>] assms 0 1 2 comp_apply 
    unfolding pre_to_univ_poly_def pre_to_univ_poly_hom_def
    by metis
  show "\<And>p. p \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> pre_to_univ_poly n i p \<in> carrier (Pring (coord_ring R (n - 1)) {i})"
  proof-
    fix p assume A: "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    have "\<psi> \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<rightarrow> carrier (Pring (coord_ring R (n - 1)) {i})"
      using 3 unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def by blast  
    then show " pre_to_univ_poly n i p \<in> carrier (Pring (coord_ring R (n - 1)) {i})"
      using A assms 
      by blast
  qed
qed   
     
lemma insert_at_index_closed:
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "x \<in> carrier R"
  assumes "i \<le> n"
  shows "insert_at_index a x i \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  apply(rule cartesian_power_car_memI')
proof-
  have 0: "length (take i a) = i"
    using assms(1) assms(3) cartesian_power_car_memE take_closed by blast
  have 1: "length (drop i a) = (n - i)"
    using assms cartesian_power_car_memE length_drop 
    by blast
  then have "length (x # drop i a) = Suc (n - i)"    
    by (metis length_Cons)
  then show "length (insert_at_index a x i) = Suc n"
    using 0 1 assms 
    by (metis Suc_eq_plus1 cartesian_power_car_memE insert_at_index_length)   
  show "\<And>ia. ia < Suc n \<Longrightarrow> insert_at_index a x i ! ia \<in> carrier R"
  proof- fix j assume A: "j < Suc n"
    show "insert_at_index a x i ! j \<in> carrier R"
      apply(cases "j < i")
       apply (metis A assms(1) assms(3) cartesian_power_car_memE cartesian_power_car_memE' insert_at_index_eq' le_imp_less_Suc less_Suc_eq not_less_eq)
      apply(cases "j = i")
       apply (metis assms(1) assms(2) assms(3) cartesian_power_car_memE insert_at_index_eq)
    proof- assume A1: "\<not> j < i " "j \<noteq>i"
      then have "i < j" by auto 
      then have "(take i a @ x # drop i a) ! j = drop i a ! (j - (Suc i))"
        by (metis "0" A1(1) Suc_diff_Suc nth_Cons_Suc nth_append)
      then show "insert_at_index a x i ! j \<in> carrier R"
        by (metis A \<open>i < j\<close> assms(1) cartesian_power_car_memE cartesian_power_car_memE' insert_at_index_eq'' less_Suc_eq_0_disj less_Suc_eq_le not_less0)
    qed
  qed
qed
        
lemma  pre_to_univ_poly_eval: 
  assumes "i < Suc n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "x \<in> carrier R"
  assumes "as = insert_at_index a x i"
  shows "eval_at_point R as p = eval_at_point R a (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda> i. coord_const x) (pre_to_univ_poly (Suc n) i p))"
  apply(rule R.Pring_car_induct''[of p "{..<Suc n}"])
  unfolding coord_ring_def 
  apply (metis assms(2) coord_ring_def)
proof-
  have 0: "as \<in> carrier (R\<^bsup>Suc n\<^esup>)"
    using assms insert_at_index_closed 
    by (meson less_Suc_eq_le)
  show  " \<And>c. c \<in> carrier R \<Longrightarrow>
         eval_at_point R as (R.indexed_const c) =
         eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i (R.indexed_const c)))"
  proof- fix c assume "c \<in> carrier R"
    have 00: "eval_at_poly R (coord_const c) as = c"
      using assms eval_at_point_const[of c as "Suc n"] "0" \<open>c \<in> carrier R\<close>
      by blast
    have 01: "closed_fun (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>n. coord_const x)"
      using assms(4) R.indexed_const_closed 
      by (metis Pi_I coord_ring_def)     
    have 02: "(pre_to_univ_poly (Suc n) i (coord_const c)) = ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) (coord_const c)"
      using pre_to_univ_poly_is_hom(5)[of i "Suc n" _ c] \<open>c \<in> carrier R\<close> assms(1) diff_Suc_1 
      by (metis coord_ring_def)     
    have 03: "(total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda> i. coord_const x) (pre_to_univ_poly (Suc n) i (coord_const c))) = 
             coord_const c"    
      using 01 cring.total_eval_const[of "R[\<X>\<^bsub>n\<^esub>]" "coord_const c" ]
      by (smt "02" MP.total_eval_const \<open>c \<in> carrier R\<close> coord_ring_def cring.indexed_const_closed R.is_cring)
    show " eval_at_point R as (R.indexed_const c) =
         eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i (R.indexed_const c))) "
      using assms 00 02 03 
      by (metis \<open>c \<in> carrier R\<close> coord_ring_def eval_at_point_const)
  qed
  have 01: "closed_fun (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>n. coord_const x)"
    using assms(4) R.indexed_const_closed 
    by (metis Pi_I coord_ring_def)    
  have 02: "ring_hom_ring (R[\<X>\<^bsub>Suc n\<^esub>]) (Pring (R[\<X>\<^bsub>n\<^esub>]) {i}) (pre_to_univ_poly (Suc n) i)"
    using pre_to_univ_poly_is_hom(1)[of i "Suc n" ]  
    by (simp add: assms)
  show "\<And>p q. p \<in> carrier (Pring R {..<Suc n}) \<Longrightarrow>
           q \<in> carrier (Pring R {..<Suc n}) \<Longrightarrow>
           eval_at_point R as p = eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i p)) \<Longrightarrow>
           eval_at_point R as q = eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i q)) \<Longrightarrow>
           eval_at_point R as (p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q) =
           eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q)))"
    proof- fix p q assume A: "p \<in> carrier (Pring R {..<Suc n})"
                           " q \<in> carrier (Pring R {..<Suc n})"
                             "eval_at_point R as p = eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i p))"
                             " eval_at_point R as q = eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i q))"
      have 0: "eval_at_poly R (p \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> q) as = 
                eval_at_poly R p as \<oplus>\<^bsub>R\<^esub> eval_at_poly R q as"
        using "0" A(1) A(2) eval_at_point_add unfolding coord_ring_def  
        by blast  
      have 1: "(total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> q))) = 
                (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i p)) \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>
                 (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i q))"
      proof-
        have 10: "pre_to_univ_poly (Suc n) i p \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
          using   pre_to_univ_poly_is_hom(6)[of i "Suc n"  _ p] 
          unfolding coord_ring_def
          by (metis A(1) assms(1) diff_Suc_1)
        have 11: "pre_to_univ_poly (Suc n) i q \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
          using pre_to_univ_poly_is_hom(6)[of i "Suc n" _ q] 
          unfolding coord_ring_def

          by (metis A(2) assms(1) diff_Suc_1)
        have 12: "(pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> q)) = 
                  (pre_to_univ_poly (Suc n) i p \<oplus>\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub> pre_to_univ_poly (Suc n) i q)"
          using ring_hom_ring.homh A 02 ring_hom_add[of "pre_to_univ_poly (Suc n) i" "R[\<X>\<^bsub>Suc n\<^esub>] " "Pring (R[\<X>\<^bsub>n\<^esub>]) {i}"
                    p q ] 
          unfolding coord_ring_def

          by blast
          
        show ?thesis

          using 01 10 11 12  A cring.total_eval_add[of "R[\<X>\<^bsub>n\<^esub>]" "pre_to_univ_poly (Suc n) i p" "{i}"
                                                       "pre_to_univ_poly (Suc n) i q" "\<lambda>i. coord_const x"]             
               coord_cring_cring 
          unfolding coord_ring_def

          by smt          
      qed
     have 2: "eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> q))) a = 
              eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i p)) a \<oplus>
              eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i q)) a"
     proof-
       have 20: "pre_to_univ_poly (Suc n) i p \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i}) "
         using A(1) 02 unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def          unfolding coord_ring_def
         by blast 
       have 21: "pre_to_univ_poly (Suc n) i q \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i}) " 
         using A(2) 02 unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def           unfolding coord_ring_def
         by blast 
       have 22: "(total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i p)) \<in> 
                  carrier (R[\<X>\<^bsub>n\<^esub>])"
         using 21 01 A cring.total_eval_closed[of "R[\<X>\<^bsub>n\<^esub>]" "pre_to_univ_poly (Suc n) i p" 
                                                "{i}" "\<lambda>i. coord_const x"] "20" coord_cring_cring 
         by metis        
       have 23: "(total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i q)) \<in> 
                  carrier (R[\<X>\<^bsub>n\<^esub>])"
         using cring.total_eval_closed[of "R[\<X>\<^bsub>n\<^esub>]" "pre_to_univ_poly (Suc n) i q" "{i}"
                                        "\<lambda>i. coord_const x"]
         by (metis "01" "21" coord_cring_cring)

       show ?thesis
         using "1" "22" "23" assms(3) eval_at_point_add by presburger
     qed
      show "eval_at_point R as (p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q) =
           eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q)))"
        using eval_at_point_add A 0 1 2 
          unfolding coord_ring_def

        by presburger
    qed
    fix p j
    assume A: "p \<in> carrier (Pring R {..<Suc n})"  "j \<in> {..<Suc n}"
      "eval_at_point R as p = eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i p))"
    show "eval_at_point R as (p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R j) =
       eval_at_point R a
        (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R j)))"
    proof-
    have A0: "eval_at_poly R (p \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar R j) as = 
              eval_at_poly R p as \<otimes> as!j"
    proof-
      have "eval_at_poly R (pvar R j) as = as!j"
        using A(2) 0 eval_pvar
        by blast
      then show ?thesis using A eval_at_point_mult[of as "Suc n" p "pvar R j" ] 0  
        by (metis R.Pring_var_closed coord_ring_def)        
    qed
    have A1: "(pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar R j)) = 
              (pre_to_univ_poly (Suc n) i p) \<otimes>\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub> pre_to_univ_poly (Suc n) i (pvar R j)"
      using A 02 ring_hom_ring.homh ring_hom_mult[of _ "R[\<X>\<^bsub>Suc n\<^esub>]"  _ p "pvar R j"] R.Pring_var_closed[of j "{..< Suc n}"] 
      unfolding coord_ring_def 
      by blast
    have A2: "(total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar R j))) = 
              (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i p ))\<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>
              (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) ( pre_to_univ_poly (Suc n) i (pvar R j)))"
    proof-
      have A20: "pre_to_univ_poly (Suc n) i p \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
        using 02 A unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def 
              unfolding coord_ring_def 

        by blast
      have A21: "pre_to_univ_poly (Suc n) i (pvar R j) \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
        using 02 A unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_hom_def 
        using  R.Pring_var_closed[of j "{..< Suc n}"] 
              unfolding coord_ring_def 

        by blast
      show ?thesis using A1 cring.total_eval_mult[of _ "pre_to_univ_poly (Suc n) i p"] 
     
          by (smt A20 A21 MP.closed_funI MP.total_eval_mult assms(4) coord_ring_def cring.indexed_const_closed R.is_cring)          
    qed
    have A3: "pre_to_univ_poly (Suc n) i p \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
      using 02 A ring_hom_ring.homh unfolding ring_hom_def
            unfolding coord_ring_def 
            by blast 
    have A4: "pre_to_univ_poly (Suc n) i (pvar R j) \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
      using 02 A ring_hom_ring.homh R.Pring_var_closed[of j "{..< Suc n}"] unfolding ring_hom_def
           unfolding coord_ring_def 

      by blast
    have A5: "total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i p ) \<in>
              carrier (R[\<X>\<^bsub>n\<^esub>])"
      using 01 cring.total_eval_closed[of "R[\<X>\<^bsub>n\<^esub>]" "pre_to_univ_poly (Suc n) i p " "{i}"]
            A3 coord_cring_cring
            unfolding coord_ring_def 
            by smt
    have A6: "total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j) ) \<in> 
              carrier (R[\<X>\<^bsub>n\<^esub>])"
      using 01 cring.total_eval_closed[of "R[\<X>\<^bsub>n\<^esub>]" "pre_to_univ_poly (Suc n) i (pvar R j) " "{i}"]
            A4 coord_cring_cring 
      unfolding coord_ring_def 
      by smt
    have A7: " eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar R j))) a
            =  eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i p)) a \<otimes>
               eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j))) a"
      using eval_at_point_mult A5 A6 A2 assms(3) by presburger
    have A8: "eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j))) a = 
              as!j"
    proof(cases "j = i")
      case True
      then have "pre_to_univ_poly (Suc n) i (pvar R j) = pvar (R[\<X>\<^bsub>n\<^esub>]) i"
        using pre_to_univ_poly_is_hom(3)[of i "Suc n"] assms(1) diff_Suc_1 by presburger
      then have "total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j)) = 
                  coord_const x"
        using cring.total_eval_var[of "R[\<X>\<^bsub>n\<^esub>]" "\<lambda>i. coord_const x"]
              unfolding coord_ring_def 
        by (smt "01" \<open>\<And>i. \<lbrakk>cring (R [\<X>\<^bsub>n\<^esub>]); (\<lambda>i. R.indexed_const x) \<in> UNIV \<rightarrow> carrier (R [\<X>\<^bsub>n\<^esub>])\<rbrakk> \<Longrightarrow> total_eval (R [\<X>\<^bsub>n\<^esub>]) (\<lambda>i. R.indexed_const x) (mset_to_IP (R [\<X>\<^bsub>n\<^esub>]) {#i#}) = R.indexed_const x\<close> coord_ring_def cring_coord_rings.coord_cring_cring cring_coord_rings_axioms var_to_IP_def)            
      then have T0: "eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j))) a
                 = x"
        using eval_at_point_const 
        by (metis assms(3) assms(4))
      have T1: "as!j = x"
        using assms 
        by (metis True  assms(5)  cartesian_power_car_memE insert_at_index_eq le_eq_less_or_eq nat_le_linear
        not_less_eq)
      then show ?thesis  
        using T0 by blast
    next
      case False
      then show ?thesis
      proof(cases "j < i")
        case True
      then have "pre_to_univ_poly (Suc n) i (pvar R j) = ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) (pvar R j)"
        using pre_to_univ_poly_is_hom(2)[of i "Suc n"] assms(1) diff_Suc_1
        unfolding coord_ring_def 
        by presburger
      then have "total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j)) = 
                  pvar R j"
        using cring.total_eval_const[of "R[\<X>\<^bsub>n\<^esub>]"] 
        by (smt Suc_less_eq True assms(1) coord_cring_cring less_trans_Suc local.pvar_closed)        
      then have T0: "eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j))) a
                 = a!j"
        using eval_pvar
        by (metis Suc_less_eq True assms(1) assms(3) less_trans_Suc)       
      have T1: "as!j = a!j"
        using assms  
        by (metis True assms(5) cartesian_power_car_memE insert_at_index_eq' less_Suc_eq_le)        
        then show ?thesis 
          using T0 by presburger
      next
        case F: False
      then have "pre_to_univ_poly (Suc n) i (pvar R j) = ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) (pvar R (j-1))"
        using pre_to_univ_poly_is_hom(4)[of i "Suc n"] assms(1) diff_Suc_1 
           unfolding coord_ring_def 
        by (metis A(2) False lessThan_iff linorder_neqE_nat)
      then have "total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j)) = 
                  pvar R (j-1)"
        using cring.total_eval_const[of "R[\<X>\<^bsub>n\<^esub>]"] 
        by (smt A(2) F False Suc_less_SucD add_diff_inverse_nat coord_cring_cring 
            lessThan_iff less_one linorder_neqE_nat local.pvar_closed not_less0 plus_1_eq_Suc)                      
      then have T0: "eval_at_poly R (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>i. coord_const x) (pre_to_univ_poly (Suc n) i (pvar R j))) a
                 = a!(j-1)"
        using eval_pvar[of "j-1" n a]
        by (metis A(2) F False One_nat_def Suc_diff_Suc Suc_less_eq assms(3)
            lessThan_iff linorder_neqE_nat minus_nat.diff_0 not_less0)
      have T1: "as!j = a!(j-1)"
      proof-
        obtain k where k_def: "j = i + 1 + k"
          using False F 
          by (metis Nat.add_0_right less_imp_add_positive less_one
              nat_neq_iff semiring_normalization_rules(25))
        show "as!j = a!(j-1)"
        proof-
          have "length (take i a) = i"
            using assms 
            by (meson cartesian_power_car_memE less_Suc_eq_le take_closed)
          then have "as!j = ( x # drop i a)!(k+1)"
            using k_def assms 
            unfolding coord_ring_def 
            by (metis Suc_eq_plus1 add.assoc insert_at_index.simps nth_append_length_plus plus_1_eq_Suc)
          have "length (drop i a) \<ge> k"
          proof-
            have "length (drop i a) = n - i"
              using assms cartesian_power_car_memE length_drop 
              by blast
            then show ?thesis 
              using assms k_def A(2) 
              by (metis Suc_eq_plus1 add.commute diff_Suc_Suc lessThan_iff less_diff_conv less_imp_le_nat)
          qed
          then have "as!j = (drop i a)! k"
            using assms k_def 
            by (metis Nat.add_0_right One_nat_def \<open>as ! j = (x # drop i a) ! (k + 1)\<close> add_Suc_right nth_Cons_Suc)
          then show ?thesis using k_def assms 
            by (metis Nat.add_diff_assoc2 add_diff_cancel_right' cartesian_power_car_memE le_add2 less_Suc_eq_le nth_drop)
        qed
      qed
      then show ?thesis 
        using T0 by presburger
      qed
    qed
    then show "eval_at_point R as (p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R j) =
    eval_at_point R a (total_eval (Pring R {..<n}) (\<lambda>i. R.indexed_const x) (pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R j)))"      
      using A(3) A0 A7
      unfolding coord_ring_def 
      by presburger
  qed
qed

definition pre_to_univ_poly_inv_hom :: 
    "nat \<Rightarrow> nat \<Rightarrow> (('a, nat) mvar_poly,('a, nat) mvar_poly) ring_hom" where
"pre_to_univ_poly_inv_hom n i = R.relabel_vars {..<(n-1)} {..<n} (\<lambda>j. if j < i then j else j + 1)"

lemma pre_to_univ_poly_inv_hom_is_hom:
  assumes "i < Suc n"
  shows "ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>Suc n\<^esub>]) (pre_to_univ_poly_inv_hom (Suc n) i)"
proof-
  have 0: "ring_hom_ring (R[\<X>\<^bsub>n\<^esub>]) (R[\<X>\<^bsub>Suc n\<^esub>]) (R.relabel_vars {..<n} {..<Suc n} (\<lambda>j. if j < i then j else j + 1))"
    unfolding coord_ring_def 
    apply(rule R.relabel_vars_is_morphism)
    using assms 
    by (smt Pi_I Suc_eq_plus1 add_less_cancel_right lessThan_iff less_Suc_eq)
  then show ?thesis 
    unfolding pre_to_univ_poly_inv_hom_def
    by simp
qed

lemma pre_to_univ_poly_inv_hom_const:
  assumes "i < Suc n" 
  assumes "k \<in> carrier R"
  shows "(pre_to_univ_poly_inv_hom (Suc n) i) (R.indexed_const k) = R.indexed_const k"
proof-
  have 0: "(R.relabel_vars {..<n} {..<Suc n} (\<lambda>j. if j < i then j else j + 1)) (R.indexed_const k) = R.indexed_const k"
    unfolding coord_ring_def 
    apply(rule R.relabel_vars_is_morphism)
    using assms 
    apply (smt Pi_I Suc_eq_plus1 add_less_cancel_right lessThan_iff less_Suc_eq)
    using assms(2) by blast 
  then show ?thesis 
    unfolding pre_to_univ_poly_inv_hom_def
    using diff_Suc_1 by presburger    
qed

lemma pre_to_univ_poly_inv_hom_pvar_0:
  assumes "i < Suc n"
  assumes "j < i"
  shows "pre_to_univ_poly_inv_hom (Suc n) i (pvar R j) = 
            pvar R j"
  unfolding pre_to_univ_poly_inv_hom_def coord_ring_def
  using R.relabel_vars_is_morphism(2)[of "\<lambda>j. if j < i then j else j + 1" "{..<n}" "{..< Suc n}" j]
  by (smt Pi_I add.commute add_diff_cancel_left' assms(1) assms(2) 
      lessThan_iff less_Suc_eq less_trans_Suc not_less_eq plus_1_eq_Suc)

lemma pre_to_univ_poly_inv_hom_pvar_1:
  assumes "i < Suc n"
  assumes "i \<le> j"
  assumes "j < n"
  shows "pre_to_univ_poly_inv_hom (Suc n) i (pvar R j) = 
            pvar R (j + 1)"
  unfolding pre_to_univ_poly_inv_hom_def 
  using assms R.relabel_vars_is_morphism(2)[of "\<lambda>j. if j < i then j else j + 1" "{..<n}" "{..< Suc n}" j]
  by (smt Pi_I add.commute add_less_cancel_right diff_Suc_1 lessThan_iff less_Suc_eq not_le plus_1_eq_Suc) 
 
definition pre_to_univ_poly_inv_var_ass ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a, nat) mvar_poly" where
"pre_to_univ_poly_inv_var_ass n i j =  pvar R i"

lemma pre_to_univ_poly_inv_var_ass_closed: 
  assumes "i < Suc n"
  shows "pre_to_univ_poly_inv_var_ass (Suc n) i \<in> {i} \<rightarrow> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  by (metis Pi_I assms local.pvar_closed pre_to_univ_poly_inv_var_ass_def)

definition pre_to_univ_poly_inv :: 
  "nat \<Rightarrow> nat \<Rightarrow> ((('a, nat) mvar_poly, nat) mvar_poly,('a, nat) mvar_poly) ring_hom" where
"pre_to_univ_poly_inv n i  = indexed_poly_induced_morphism {i} (R[\<X>\<^bsub>n\<^esub>])
                                 (pre_to_univ_poly_inv_hom n i) (pre_to_univ_poly_inv_var_ass n i)"

lemma pre_to_univ_poly_inv_is_hom: 
  assumes "i < Suc n"
  shows "ring_hom_ring (Pring (R[\<X>\<^bsub>n\<^esub>]) {i}) (R[\<X>\<^bsub>Suc n\<^esub>]) (pre_to_univ_poly_inv (Suc n) i)"
  apply(rule cring.Pring_universal_prop[of _ _  "pre_to_univ_poly_inv_var_ass (Suc n) i" "{i}" "pre_to_univ_poly_inv_hom (Suc n) i"])
  unfolding coord_ring_def
  apply (simp add: R.Pring_is_cring R.is_cring)
  apply (simp add: R.Pring_is_cring R.is_cring)
  apply (metis Pi_I R.Pring_var_closed assms lessThan_iff pre_to_univ_poly_inv_var_ass_def)
  apply (metis assms coord_ring_def pre_to_univ_poly_inv_hom_is_hom)
  by (simp add: coord_ring_def pre_to_univ_poly_inv_def)

lemma pre_to_univ_poly_inv_pvar: 
  assumes "i < Suc n"
  shows  "(pre_to_univ_poly_inv (Suc n) i) (pvar (R[\<X>\<^bsub>n\<^esub>]) i) = pvar R i"
  using assms  cring.Pring_universal_prop[of "R[\<X>\<^bsub>n\<^esub>]" "R[\<X>\<^bsub>Suc n\<^esub>]" 
                    "pre_to_univ_poly_inv_var_ass (Suc n) i" "{i}" "pre_to_univ_poly_inv_hom (Suc n) i"]
  by (metis Pi_I coord_cring_cring cring_coord_rings.pre_to_univ_poly_inv_var_ass_def
      cring_coord_rings_axioms local.pvar_closed pre_to_univ_poly_inv_def 
      pre_to_univ_poly_inv_hom_is_hom singletonI var_to_IP_def)

lemma pre_to_univ_poly_inv_const: 
  assumes "i < Suc n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows  "(pre_to_univ_poly_inv (Suc n) i) (ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) p) = pre_to_univ_poly_inv_hom (Suc n) i p "
  using assms  cring.Pring_universal_prop[of "R[\<X>\<^bsub>n\<^esub>]" "R[\<X>\<^bsub>Suc n\<^esub>]" 
                    "pre_to_univ_poly_inv_var_ass (Suc n) i" "{i}" "pre_to_univ_poly_inv_hom (Suc n) i"]
  by (metis Pi_I coord_cring_cring cring_coord_rings.pre_to_univ_poly_inv_var_ass_def
      cring_coord_rings_axioms local.pvar_closed pre_to_univ_poly_inv_def pre_to_univ_poly_inv_hom_is_hom)
  
lemma pre_to_univ_poly_inverse:
  assumes  "i < Suc n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  shows "pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i p) = p"
  apply(rule R.Pring_car_induct''[of p "{..<Suc n}"])
  using assms coord_ring_def  apply metis    
proof-
  show 0: " \<And>c. c \<in> carrier R \<Longrightarrow> pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i (coord_const c)) = coord_const c"
  proof-
    fix c assume A: "c \<in> carrier R"
    have 0: "pre_to_univ_poly (Suc n) i (coord_const c) = 
                MP.indexed_const n (coord_const c)"
      using A assms(1) diff_Suc_1 pre_to_univ_poly_is_hom(5) by presburger
    have 1: "(\<lambda>j. if j < i then j else j + 1) \<in> {..<n} \<rightarrow> {..<Suc n}"
      by (smt Pi_I Suc_eq_plus1 add_less_cancel_right lessThan_iff less_Suc_eq)
    have 2: "pre_to_univ_poly_inv_hom (Suc n) i (coord_const c) = coord_const c"
      unfolding pre_to_univ_poly_inv_hom_def
      using 1 R.relabel_vars_is_morphism(3)[of "(\<lambda>j. if j < i then j else j + 1)" "{..<n}" "{..<Suc n}" c] 
     unfolding coord_ring_def 
     using A diff_Suc_1 by presburger
    show "pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i (coord_const c)) = coord_const c "
      using 0 1 2 
      by (metis (no_types, lifting) A R.indexed_const_closed assms(1) coord_ring_def pre_to_univ_poly_inv_const)      
  qed
  show 1: "\<And>p q. p \<in> carrier (Pring R {..<Suc n}) \<Longrightarrow>
           q \<in> carrier (Pring R {..<Suc n}) \<Longrightarrow>
           pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i p) =
           p \<Longrightarrow>
           pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i q) =
           q \<Longrightarrow>
           pre_to_univ_poly_inv (Suc n) i
            (pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q)) =
           p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q"
  proof- fix p q assume A: "p \<in> carrier (Pring R {..<Suc n})"
          "q \<in> carrier (Pring R {..<Suc n})"
          "pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i p) = p"
          "pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i q) = q"
    have 0: "(pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> q)) = 
            (pre_to_univ_poly (Suc n) i p) \<oplus>\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub> pre_to_univ_poly (Suc n) i q"
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"] ring_hom_ring.homh ring_hom_add A
      unfolding coord_ring_def 
      by (metis (mono_tags, lifting) assms(1) diff_Suc_1)
    have 1: "pre_to_univ_poly (Suc n) i p \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"] A      
      unfolding coord_ring_def 
      by (metis assms(1) coord_ring_def diff_Suc_1 pre_to_univ_poly_is_hom(6))
    have 2: "pre_to_univ_poly (Suc n) i q \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"] A
      unfolding coord_ring_def 
      by (metis assms(1) coord_ring_def diff_Suc_1 pre_to_univ_poly_is_hom(6))      
    show "pre_to_univ_poly_inv (Suc n) i
            (pre_to_univ_poly (Suc n) i (p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q)) =
           p \<oplus>\<^bsub>Pring R {..<Suc n}\<^esub> q"
      using 0 1 2 A pre_to_univ_poly_inv_is_hom[of i n] ring_hom_ring.homh ring_hom_add
      unfolding coord_ring_def      
      by (smt assms(1))
  qed
  show "\<And>p ia.
       p \<in> carrier (Pring R {..<Suc n}) \<Longrightarrow>
       ia \<in> {..<Suc n} \<Longrightarrow>
       pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i p) = p \<Longrightarrow>
       pre_to_univ_poly_inv (Suc n) i
        (pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R ia)) =
       p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R ia"
  proof- fix p j 
    assume A: " p \<in> carrier (Pring R {..<Suc n})"  "j \<in> {..<Suc n}"
           "pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i p) = p "
    have 0: "(pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> pvar R j)) 
            = (pre_to_univ_poly (Suc n) i p) \<otimes>\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub> pre_to_univ_poly (Suc n) i (pvar  R j)"
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"] ring_hom_ring.homh ring_hom_mult A
      unfolding coord_ring_def
      by (metis R.Pring_var_closed assms(1) diff_Suc_1)
    have 1: "pre_to_univ_poly (Suc n) i p \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"] A    
      unfolding coord_ring_def
      by (metis assms(1) coord_ring_def diff_Suc_1 pre_to_univ_poly_is_hom(6))
    have 1: "pre_to_univ_poly (Suc n) i (pvar R j) \<in> carrier (Pring (R[\<X>\<^bsub>n\<^esub>]) {i})"
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"] A      
      unfolding coord_ring_def
      by (metis R.Pring_var_closed assms(1) coord_ring_def diff_Suc_1 pre_to_univ_poly_is_hom(6))
    have 2: "pre_to_univ_poly_inv (Suc n) i (pre_to_univ_poly (Suc n) i (pvar R j)) = pvar R j"   
    proof(cases "j = i")
      case True
      then have "(pre_to_univ_poly (Suc n) i (pvar R j)) = pvar (R[\<X>\<^bsub>n\<^esub>]) j"
        using pre_to_univ_poly_is_hom(3)[of i "Suc n"] assms(1) diff_Suc_1 by presburger
      then show ?thesis 
      unfolding coord_ring_def
      using True \<open>pre_to_univ_poly (Suc n) i (pvar R j) = pvar (R[\<X>\<^bsub>n\<^esub>]) j\<close> assms(1) pre_to_univ_poly_inv_pvar by presburger
    next
      case False
      show ?thesis 
      proof(cases "j < i")
        case True
        then have "(pre_to_univ_poly (Suc n) i (pvar R j)) = ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) (pvar R j)"
          using pre_to_univ_poly_is_hom(2) [of i "Suc n"] assms(1) diff_Suc_1 
           unfolding coord_ring_def

          by presburger
        then show ?thesis 
          using pre_to_univ_poly_inv_const[of i n "(pvar R j)"]
                pre_to_univ_poly_inv_hom_pvar_0[of i n j]
          by (metis Suc_less_eq True assms(1) less_trans_Suc local.pvar_closed)
      next
        case F: False
        then have "(pre_to_univ_poly (Suc n) i (pvar R j)) = ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) (pvar R (j-1))"
          using pre_to_univ_poly_is_hom(4)[of i "Suc n"] assms(1) diff_Suc_1 
               unfolding coord_ring_def
 by (metis A(2) False lessThan_iff linorder_neqE_nat)
        then show ?thesis 
          using pre_to_univ_poly_inv_const[of i n "(pvar R (j-1))"]
                pre_to_univ_poly_inv_hom_pvar_0[of i n "j-1"]
          by (metis (no_types, lifting) A(2) F False One_nat_def Suc_eq_plus1 add_diff_inverse_nat 
              assms(1) le_neq_implies_less lessThan_iff less_one local.pvar_closed nat_le_linear 
              not_less_eq plus_1_eq_Suc pre_to_univ_poly_inv_hom_pvar_1)        
      qed
    qed
    show "pre_to_univ_poly_inv (Suc n) i
        (pre_to_univ_poly (Suc n) i (p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R j)) =
       p \<otimes>\<^bsub>Pring R {..<Suc n}\<^esub> pvar R j"
      using 0 1 2 A pre_to_univ_poly_inv_is_hom[of i n] 
            ring_hom_ring.homh[of _ _ "pre_to_univ_poly_inv (Suc n) i "] 
            ring_hom_mult[of "pre_to_univ_poly_inv (Suc n) i "]
      unfolding coord_ring_def 
      by (smt assms(1) coord_ring_def diff_Suc_1 pre_to_univ_poly_is_hom(6))
  qed
qed

lemma coord_ring_car_induct:
  assumes "Q \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  assumes "\<And>c. c \<in> carrier R \<Longrightarrow> A (R.indexed_const c)"
  assumes "\<And>p q. p \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> q \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> A p \<Longrightarrow> A q \<Longrightarrow> A (p \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> q)"
  assumes "\<And>p i. p \<in> carrier (R[\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> i < n \<Longrightarrow> A p \<Longrightarrow> A (p \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> pvar R i)"
  shows "A Q"
  unfolding coord_ring_def apply(rule R.Pring_car_induct''[of _ "{..<n}"])
  apply (metis assms(1) coord_ring_def)
  using assms(2) apply auto[1]
  apply (metis assms(3) coord_ring_def)
  by (metis assms(4) coord_ring_def lessThan_iff)

lemma pre_to_univ_poly_inverse':
  assumes  "i < Suc n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)) = MP.indexed_const n p"
  apply(rule coord_ring_car_induct[of _ n])
  using assms(2) apply blast
proof-
  show "\<And>c. c \<in> carrier R \<Longrightarrow>
         pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (R.indexed_const c))) =
         MP.indexed_const n (R.indexed_const c)"
  proof- fix k assume A: "k \<in> carrier R"
    have 0: "R.indexed_const k \<in> carrier (R [\<X>\<^bsub>n\<^esub>])"
      using A 
      by (metis coord_ring_def R.indexed_const_closed)
    have 1: "pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (R.indexed_const k)) = pre_to_univ_poly_inv_hom (Suc n) i (R.indexed_const k)"
      using 0 assms pre_to_univ_poly_inv_const[of i n "R.indexed_const k"]
      by linarith
    have "pre_to_univ_poly_inv_hom (Suc n) i (R.indexed_const k) = R.indexed_const k"
      using A pre_to_univ_poly_inv_hom_const[of i n k] assms
      by blast
    thus "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (R.indexed_const k))) = MP.indexed_const n (R.indexed_const k) "
      using 1 
      by (metis A assms(1) coord_ring_def diff_Suc_1 pre_to_univ_poly_is_hom(5))
  qed
  show "\<And>p q. p \<in> carrier (R [\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
           q \<in> carrier (R [\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
           pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)) = MP.indexed_const n p \<Longrightarrow>
           pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n q)) = MP.indexed_const n q \<Longrightarrow>
           pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<oplus>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> q))) = MP.indexed_const n (p \<oplus>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> q)"
  proof- fix p Q
    assume A: "p \<in> carrier (R [\<X>\<^bsub>n\<^esub>]) "
           "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)) = MP.indexed_const n p"
           "Q \<in> carrier (R [\<X>\<^bsub>n\<^esub>])"
           "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n Q)) = MP.indexed_const n Q "
    have 0: "p \<Oplus> Q = p \<oplus>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> Q"
      by (metis R.Pring_add coord_ring_def)
    have 1: "MP.indexed_const n (p \<Oplus> Q) = (MP.indexed_const n p) \<oplus>\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub>(MP.indexed_const n Q)"
      by (metis "0" MP.Pring_add MP.indexed_padd_const)
    have 2: "MP.indexed_const n p \<in> carrier (Pring (R [\<X>\<^bsub>n\<^esub>]) {i})"
      using A unfolding coord_ring_def 
      by (metis MP.indexed_const_closed R.Pring_car coord_ring_def)
    have 3: "MP.indexed_const n Q \<in> carrier (Pring (R [\<X>\<^bsub>n\<^esub>]) {i})"
      using A(3) MP.indexed_const_closed by blast
    have 4: "(pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<oplus>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> Q))) = 
      pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p) \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n Q)"
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"]
            pre_to_univ_poly_inv_is_hom(1)[of i n] 
            ring_hom_add[of "pre_to_univ_poly_inv (Suc n) i" "(Pring (R [\<X>\<^bsub>n\<^esub>]) {i})" 
                          "(R [\<X>\<^bsub>Suc n\<^esub>])" "MP.indexed_const n p" "MP.indexed_const n Q"] 
            ring_hom_ring.homh 
            MP.indexed_const_closed[of p n "{i}"] 
            MP.indexed_const_closed[of Q n "{i}"] A R.Pring_car[of "{..<n}"] unfolding coord_ring_def 
      by (metis "0" "1" assms(1) coord_ring_def)
    have 5: "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<oplus>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> Q))) = 
          pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)) \<oplus>\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub>
          pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n Q))"
    proof-
      have 50: "pre_to_univ_poly (Suc n) i \<in> ring_hom (R [\<X>\<^bsub>Suc n\<^esub>]) (Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i})"
        using pre_to_univ_poly_is_hom(1)[of i "Suc n"] ring_hom_ring.homh
        by (metis assms(1))
      have 51: "pre_to_univ_poly_inv (Suc n) i \<in> ring_hom (Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}) (R [\<X>\<^bsub>Suc n\<^esub>]) "
        using pre_to_univ_poly_inv_is_hom ring_hom_ring.homh
        by (metis assms(1) diff_Suc_1)
      have 52: " pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p) \<in> carrier (R [\<X>\<^bsub>Suc n\<^esub>])"
        using 51 ring_hom_closed[of "pre_to_univ_poly_inv (Suc n) i" ] 
        by (smt "2" diff_Suc_1)
      have 53: "  pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n Q) \<in> carrier (R [\<X>\<^bsub>Suc n\<^esub>]) "
        using 51 ring_hom_closed[of "pre_to_univ_poly_inv (Suc n) i" ] 
        by (smt 3 diff_Suc_1)
      show ?thesis using 50 51 52 53
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"]
            ring_hom_add[of "pre_to_univ_poly (Suc n) i" "R [\<X>\<^bsub>Suc n\<^esub>]" "Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}"
                "pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)" 
                "pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n Q)"] 4
      by (metis diff_Suc_1)
    qed
    show "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<oplus>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> Q))) = MP.indexed_const n (p \<oplus>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> Q)"
      using 5 A "0" "1" by metis 
  qed
  show "\<And>p ia.
       p \<in> carrier (R [\<X>\<^bsub>n\<^esub>]) \<Longrightarrow>
       ia < n \<Longrightarrow>
       pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)) = MP.indexed_const n p \<Longrightarrow>
       pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> pvar R ia))) = MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> pvar R ia)"
  proof- fix p j
    assume A: "p \<in> carrier (R [\<X>\<^bsub>n\<^esub>])" "j < n"
               "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)) = MP.indexed_const n p"
    show "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> pvar R j))) = MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> pvar R j)"
    proof-
      have 0: "pre_to_univ_poly_inv (Suc n) i \<in> ring_hom (Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}) (R [\<X>\<^bsub>Suc n\<^esub>]) "
        using pre_to_univ_poly_inv_is_hom(1)[of i n] ring_hom_ring.homh
        by (metis assms(1) diff_Suc_1)    
      have 1: "MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> (pvar R j)) = MP.indexed_const n p \<otimes>\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub> MP.indexed_const n (pvar R j)"
        by (metis A(1) A(2) MP.indexed_const_mult local.pvar_closed)
      have 2: "(pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> pvar R j))) = 
          pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p) \<otimes>\<^bsub>(R [\<X>\<^bsub>Suc n\<^esub>])\<^esub> pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j))"
        using 0 1 ring_hom_mult A
        by (metis (no_types, lifting) MP.indexed_const_closed diff_Suc_1 local.pvar_closed)
      have 3: "pre_to_univ_poly(Suc n) i \<in> ring_hom  (R [\<X>\<^bsub>Suc n\<^esub>]) (Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}) "
        using assms(1) pre_to_univ_poly_is_hom(1) ring_hom_ring.homh by blast        
      have 4: "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> pvar R j))) =
                pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n p)) \<otimes>\<^bsub>Pring (R [\<X>\<^bsub>n\<^esub>]) {i}\<^esub> 
                  pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j)))"
        using 2 3 ring_hom_mult
        by (smt "0" A(1) A(2) MP.indexed_const_closed diff_Suc_1 local.pvar_closed ring_hom_closed)
      have 5: "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (p \<otimes>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> pvar R j))) =
                MP.indexed_const n p \<otimes>\<^bsub>Pring (R [\<X>\<^bsub>n\<^esub>]) {i}\<^esub> 
                  pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j)))"
       using A "4" by presburger
     have 6: "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j))) = (MP.indexed_const n (pvar R j))"
     proof- 
       have "(pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j))) = pre_to_univ_poly_inv_hom (Suc n) i  (pvar R j)"
         using A(2) assms(1) local.pvar_closed pre_to_univ_poly_inv_const by blast
       hence "pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j))) = 
              pre_to_univ_poly (Suc n) i (pre_to_univ_poly_inv_hom (Suc n) i  (pvar R j))"
         by presburger
       show ?thesis 
       proof(cases "j < i")
         case True
         then have "(pre_to_univ_poly_inv_hom (Suc n) i  (pvar R j)) = (pvar R j)"
           using pre_to_univ_poly_inv_hom_pvar_0[of i n j] assms(1) by blast
         thus ?thesis using   pre_to_univ_poly_is_hom 
           by (metis True \<open>pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j)) = pre_to_univ_poly_inv_hom (Suc n) i (pvar R j)\<close> assms(1) coord_ring_def diff_Suc_1)
       next
         case False
         have "pre_to_univ_poly_inv_hom (Suc n) i  (pvar R j) = pvar R (j + 1)"
           using pre_to_univ_poly_inv_hom_pvar_1[of i n j]  A(2) False assms(1) not_le 
           by blast
         thus ?thesis using   pre_to_univ_poly_is_hom 
           by (metis A(2) False Suc_eq_plus1 \<open>pre_to_univ_poly_inv (Suc n) i (MP.indexed_const n (pvar R j)) = pre_to_univ_poly_inv_hom (Suc n) i (pvar R j)\<close> 
               assms(1) coord_ring_def diff_Suc_1 not_less_eq)
       qed
     qed
     show ?thesis using 6 A 
       using "1" "5" by presburger
   qed
 qed
qed

definition to_univ_poly :: "nat \<Rightarrow> nat \<Rightarrow> 
  (('a, nat) mvar_poly , ('a, nat) mvar_poly u_poly) ring_hom" where
"to_univ_poly n i  = IP_to_UP i \<circ> (pre_to_univ_poly n i) "

definition from_univ_poly :: "nat \<Rightarrow> nat \<Rightarrow> 
      (('a, nat) mvar_poly u_poly , ('a, nat) mvar_poly) ring_hom" where
"from_univ_poly n i  = pre_to_univ_poly_inv n i \<circ> (UP_to_IP (coord_ring R (n-1)) i)"

lemma to_univ_poly_is_hom:
  assumes "i \<le> n"
  shows "(to_univ_poly (Suc n) i) \<in> ring_hom (R[\<X>\<^bsub>Suc n\<^esub>]) (UP (R[\<X>\<^bsub>n\<^esub>])) "
  unfolding to_univ_poly_def 
  apply(rule ring_hom_trans[of _ _ "Pring (R[\<X>\<^bsub>n\<^esub>]) {i}"])
  using assms pre_to_univ_poly_is_hom ring_hom_ring.homh
   apply (metis diff_Suc_1 le_imp_less_Suc)
  using UP_cring.IP_to_UP_ring_hom[of "(Pring R {..<n})" i] assms  ring_hom_ring.homh
  unfolding coord_ring_def UP_cring_def
  using R.Pring_is_cring R.is_cring by blast

lemma from_univ_poly_is_hom:
  assumes "i \<le> n"
  shows "(from_univ_poly (Suc n) i) \<in> ring_hom  (UP (R[\<X>\<^bsub>n\<^esub>])) (R[\<X>\<^bsub>Suc n\<^esub>]) "
  unfolding from_univ_poly_def 
  apply(rule ring_hom_trans[of _ _ "Pring (R[\<X>\<^bsub>n\<^esub>]) {i}"])
  using assms UP_cring.UP_to_IP_ring_hom[of "coord_ring R (Suc n - 1)" i] 
              ring_hom_ring.homh[of "UP (coord_ring R (Suc n - 1))" "Pring (coord_ring R (Suc n - 1)) {i}" "UP_to_IP (coord_ring R (Suc n - 1)) i"]
  unfolding coord_ring_def UP_cring_def 
  apply (metis R.Pring_is_cring diff_Suc_1 R.is_cring)  
  using assms ring_hom_ring.homh le_imp_less_Suc pre_to_univ_poly_inv_is_hom 
   unfolding coord_ring_def UP_cring_def
  by blast

lemma to_univ_poly_inverse:
  assumes "i \<le> n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  shows "from_univ_poly (Suc n) i (to_univ_poly (Suc n) i p) = p"
proof-
  have 0: "pre_to_univ_poly (Suc n) i p \<in> Pring_set (R[\<X>\<^bsub>n\<^esub>]) {i}"
    using pre_to_univ_poly_is_hom(6)[of i "Suc n" _ p] assms ring.Pring_car
     unfolding coord_ring_def UP_domain_def
    by (metis R.Pring_is_ring diff_Suc_1 le_imp_less_Suc)
  have 1: "UP_to_IP (R[\<X>\<^bsub>n\<^esub>]) i 
           (IP_to_UP i (pre_to_univ_poly (Suc n) i p)) = 
           pre_to_univ_poly (Suc n) i p"
    using 0 UP_cring.UP_to_IP_inv[of "R[\<X>\<^bsub>n\<^esub>]" "pre_to_univ_poly (Suc n) i p" i ] 
          R.Pring_is_cring
    unfolding coord_ring_def UP_cring_def
    using R.is_cring by blast     
  have 2: "from_univ_poly (Suc n) i (to_univ_poly (Suc n) i p) =
          (pre_to_univ_poly_inv (Suc n) i (
          (UP_to_IP (coord_ring R (Suc n - 1)) i) (
          (IP_to_UP i (
          (pre_to_univ_poly (Suc n) i) p)))))"
    unfolding from_univ_poly_def to_univ_poly_def 
  unfolding coord_ring_def
    by (metis comp_eq_dest_lhs)    
  have 3: "from_univ_poly (Suc n) i (to_univ_poly (Suc n) i p) =
          (pre_to_univ_poly_inv (Suc n) i (
          pre_to_univ_poly (Suc n) i p))"
    using 0 1 2 
  unfolding coord_ring_def 
    using diff_Suc_1 by presburger    
  then show ?thesis 
    using pre_to_univ_poly_inverse assms(1) assms(2) less_Suc_eq_le 
    by presburger
qed
 
lemma to_univ_poly_closed: 
  assumes "i \<le> n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  shows "to_univ_poly (Suc n) i p \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>]))"
  using to_univ_poly_is_hom[of i n] assms unfolding  ring_hom_def
  by blast 

lemma to_univ_poly_add: 
  assumes "i \<le> n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  shows "to_univ_poly (Suc n) i (p \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>Q) = 
        to_univ_poly (Suc n) i p \<oplus>\<^bsub>UP (R[\<X>\<^bsub>n\<^esub>])\<^esub> to_univ_poly (Suc n) i Q"
  using to_univ_poly_is_hom ring_hom_add 
  by (metis assms(1) assms(2) assms(3))
  
lemma to_univ_poly_mult: 
  assumes "i \<le> n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "Q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  shows "to_univ_poly (Suc n) i (p \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>Q) = 
        to_univ_poly (Suc n) i p \<otimes>\<^bsub>UP (R[\<X>\<^bsub>n\<^esub>])\<^esub> to_univ_poly (Suc n) i Q"
  using to_univ_poly_is_hom ring_hom_mult
  by (metis assms(1) assms(2) assms(3))

lemma from_univ_poly_closed: 
  assumes "i \<le> n"
  assumes "p \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>])) "
  shows "from_univ_poly (Suc n) i p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  using from_univ_poly_is_hom[of i n] assms unfolding  ring_hom_def
  by blast 

lemma from_univ_poly_add: 
  assumes "i \<le> n"
  assumes "p \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>])) "
  assumes "Q \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>])) "
  shows "from_univ_poly (Suc n) i (p \<oplus>\<^bsub>UP (R[\<X>\<^bsub>n\<^esub>])\<^esub>Q) = 
        from_univ_poly (Suc n) i p \<oplus>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> from_univ_poly (Suc n) i Q"
  using from_univ_poly_is_hom ring_hom_add 
  by (metis assms(1) assms(2) assms(3))
  
lemma from_univ_poly_mult: 
  assumes "i \<le> n"
  assumes "p \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>])) "
  assumes "Q \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>])) "
  shows "from_univ_poly (Suc n) i (p \<otimes>\<^bsub>UP (R[\<X>\<^bsub>n\<^esub>])\<^esub>Q) = 
        from_univ_poly (Suc n) i p \<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> from_univ_poly (Suc n) i Q"
  using from_univ_poly_is_hom ring_hom_mult 
  by (metis assms(1) assms(2) assms(3))

lemma(in UP_cring) monom_as_mult:
  assumes "a \<in> carrier R"
  shows "up_ring.monom (UP R) a n = to_poly a  \<otimes>\<^bsub> UP R\<^esub> up_ring.monom (UP R) \<one> n"
  by (metis One_nat_def P_def R.one_closed R.r_one UP_cring.poly_shift_monom add_Suc assms is_UP_cring local.monom_mult plus_1_eq_Suc to_polynomial_def)

lemma cring_coord_rings_coord_ring:
"cring_coord_rings (R[\<X>\<^bsub>n\<^esub>])"
  unfolding cring_coord_rings_def 
            cring_coord_rings_axioms_def coord_ring_def 
  apply(rule conjI)
  unfolding UP_cring_def 
  apply (metis coord_cring_cring coord_ring_def)
  using cring_coord_rings_axioms
  unfolding cring_coord_rings_def cring_coord_rings_axioms_def
  by (metis coord_ring_def coord_ring_one coord_ring_zero)

lemma from_univ_poly_monom_inverse:
  assumes "i < Suc n"
  assumes "a \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  shows "to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) a m)) = up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) a m"
proof-
  have 0: "up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) a m = (to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a) \<otimes>\<^bsub>UP (R[\<X>\<^bsub>n\<^esub>])\<^esub> (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m)"
    using UP_cring.monom_as_mult[of "R[\<X>\<^bsub>n\<^esub>]" a m] unfolding UP_ring_def 
    using UP_cring_def assms coord_cring_cring by blast
  have 1 : "(UP_to_IP (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i) (to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a) = ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) a"
    using UP_cring.UP_to_IP_const[of "R [\<X>\<^bsub>Suc n - 1\<^esub>]" a i] unfolding UP_cring_def  
    by (simp add: assms coord_cring_cring)
  have 2: "(from_univ_poly (Suc n) i (to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a)) 
                = pre_to_univ_poly_inv (Suc n) i (ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) a)"
    unfolding from_univ_poly_def using 1  
    by (metis comp_apply)
  have 3: "from_univ_poly (Suc n) i (to_polynomial (R [\<X>\<^bsub>n\<^esub>]) a) = pre_to_univ_poly_inv_hom (Suc n) i a"
    using pre_to_univ_poly_inv_const[of i n a] assms 2
    by presburger
  have 4: "to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (to_polynomial (R [\<X>\<^bsub>n\<^esub>]) a)) = 
            IP_to_UP i ((pre_to_univ_poly (Suc n) i) (pre_to_univ_poly_inv_hom (Suc n) i a))"
    using 3 unfolding to_univ_poly_def from_univ_poly_def 
    by (metis comp_apply)
  have 5: "(pre_to_univ_poly (Suc n) i) (pre_to_univ_poly_inv (Suc n) i (ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) a)) =  (ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) a)"
    using assms(1) assms(2) pre_to_univ_poly_inverse' by blast
  have "(to_univ_poly (Suc n) i) (from_univ_poly (Suc n) i (to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a)) = IP_to_UP i  (ring.indexed_const (R[\<X>\<^bsub>n\<^esub>]) a)"
    unfolding to_univ_poly_def 
    by (metis "2" "5" comp_apply)
  hence 6: "(to_univ_poly (Suc n) i) (from_univ_poly (Suc n) i (to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a)) = to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a"
    using UP_cring.IP_to_UP_indexed_const[of "R[\<X>\<^bsub>n\<^esub>]"] 
    by (smt UP_cring_def assms(2) coord_cring_cring)
  have 7: "(to_univ_poly (Suc n) i) (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m)) = up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m"
  proof-
    have 70: "pvar (R [\<X>\<^bsub>n\<^esub>]) i [^]\<^bsub>Pring (R [\<X>\<^bsub>n\<^esub>]) {i}\<^esub> m \<in> carrier (Pring (R [\<X>\<^bsub>n\<^esub>]) {i})"
      using Cring_Multivariable_Poly.pvar_closed[of  "R[\<X>\<^bsub>n\<^esub>]" i "{i}"] monoid.nat_pow_closed[of "R[\<X>\<^bsub>n\<^esub>]"]
      by (meson MP.Pring_is_monoid coord_cring_cring equalityD2 insert_subset monoid.nat_pow_closed)
    have 71: "(UP_to_IP (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i) (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> m) = 
                          (pvar (R[\<X>\<^bsub>n\<^esub>]) i)[^]\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub>m"
      using 70 UP_cring.UP_to_IP_monom[of "R[\<X>\<^bsub>n\<^esub>]" "\<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>" i m ] cring.Pring_smult_one[of "R[\<X>\<^bsub>n\<^esub>]" "pvar (R [\<X>\<^bsub>n\<^esub>]) i [^]\<^bsub>Pring (R [\<X>\<^bsub>n\<^esub>]) {i}\<^esub> m" "{i}"]
      unfolding UP_cring_def 
      using MP.one_closed coord_cring_cring diff_Suc_1 by presburger
    hence 72: "from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m) = 
                   pre_to_univ_poly_inv (Suc n) i ((pvar (R[\<X>\<^bsub>n\<^esub>]) i)[^]\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub>m)"
      unfolding from_univ_poly_def
      using comp_apply[of "pre_to_univ_poly_inv (Suc n) i" "UP_to_IP (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i" "up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> m"]  
      by presburger 
    have 73: " pre_to_univ_poly_inv (Suc n) i \<in> ring_hom (Pring (R [\<X>\<^bsub>n\<^esub>]) {i}) (R [\<X>\<^bsub>Suc n\<^esub>]) "
      using pre_to_univ_poly_inv_is_hom[of i n] assms(1) ring_hom_ring.homh by blast
    hence 74: "from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m) = (pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>m"
      unfolding from_univ_poly_def 
      using 70 71 72 pre_to_univ_poly_inv_pvar[of i n] 
              ring_hom_nat_pow[of "(Pring (R [\<X>\<^bsub>n\<^esub>]) {i})" "R [\<X>\<^bsub>Suc n\<^esub>]" "pre_to_univ_poly_inv (Suc n) i" "(pvar (R[\<X>\<^bsub>n\<^esub>]) i)" m]
      by (metis MP.Pring_is_ring MP.Pring_var_closed MP.ring_axioms assms(1) from_univ_poly_def singletonI)
    hence 75: "(to_univ_poly (Suc n) i) (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m)) 
                  = (to_univ_poly (Suc n) i) ((pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>m)"
      by metis 
    have 76: "pre_to_univ_poly (Suc n) i (pvar R i) = pvar (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i"
      using pre_to_univ_poly_is_hom(3)[of i "Suc n" ] assms(1) by blast
    have "pre_to_univ_poly (Suc n) i \<in> ring_hom (R [\<X>\<^bsub>Suc n\<^esub>]) (Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}) "
      apply(rule ring_hom_ring.homh)
      using pre_to_univ_poly_is_hom(1)[of i "Suc n"] 
      using assms(1) by blast
    hence "pre_to_univ_poly (Suc n) i (pvar R i [^]\<^bsub>R [\<X>\<^bsub>Suc n\<^esub>]\<^esub> m) = pvar (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i [^]\<^bsub>Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}\<^esub> m"
      using 76 ring_hom_nat_pow[of "R[\<X>\<^bsub>Suc n\<^esub>]" "Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}" "pre_to_univ_poly (Suc n) i" "pvar R i" m]
      by (metis MP.Pring_is_ring MP.ring_axioms assms(1) local.pvar_closed)
    hence 77: "(to_univ_poly (Suc n) i) (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m)) 
                  =IP_to_UP i  (pvar (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i [^]\<^bsub>Pring (R [\<X>\<^bsub>Suc n - 1\<^esub>]) {i}\<^esub> m)"
      unfolding to_univ_poly_def using comp_apply[of "IP_to_UP i" " pre_to_univ_poly (Suc n) i"]
      using "74" by presburger
    have 78: "IP_to_UP i  (pvar (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i) = X_poly (R[\<X>\<^bsub>n\<^esub>])"
      using cring.IP_to_UP_var[of "R[\<X>\<^bsub>n\<^esub>]"] 
      by (simp add: MP.IP_to_UP_var var_to_IP_def)
    have 79: "IP_to_UP i \<in> ring_hom (Pring (R [\<X>\<^bsub>n\<^esub>]) {i}) (UP (R [\<X>\<^bsub>n\<^esub>]))"
      using UP_cring.IP_to_UP_ring_hom[of "R[\<X>\<^bsub>n\<^esub>]" i] ring_hom_ring.homh[of "Pring (R [\<X>\<^bsub>n\<^esub>]) {i}"] 
      unfolding UP_cring_def
      using coord_cring_cring by blast
    have 80: "pvar (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i \<in> carrier (Pring (R [\<X>\<^bsub>n\<^esub>]) {i})"
      by (metis "76" assms(1) diff_Suc_1 local.pvar_closed pre_to_univ_poly_is_hom(6))
    have 81: "ring (UP (R[\<X>\<^bsub>n\<^esub>]))"
      using UP_ring.UP_ring[of "R[\<X>\<^bsub>n\<^esub>]"] unfolding UP_ring_def  
      using MP.ring_axioms by blast
    hence 82: "IP_to_UP i  (pvar (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i [^]\<^bsub>Pring (R[\<X>\<^bsub>n\<^esub>]) {i}\<^esub> m) = X_poly (R[\<X>\<^bsub>n\<^esub>]) [^]\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> m"

      using 78 79 80 ring_hom_nat_pow[of "Pring (R [\<X>\<^bsub>n\<^esub>]) {i}" "UP (R [\<X>\<^bsub>n\<^esub>])" "IP_to_UP i" "pvar (R [\<X>\<^bsub>Suc n - 1\<^esub>]) i" m] 
      by (metis MP.Pring_is_ring)
    have 83: "\<one>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> \<odot>\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> X_poly (R [\<X>\<^bsub>n\<^esub>]) [^]\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> m = X_poly (R [\<X>\<^bsub>n\<^esub>]) [^]\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> m"
      using UP_ring.UP_smult_one[of "R[\<X>\<^bsub>n\<^esub>]" "X_poly (R [\<X>\<^bsub>n\<^esub>]) [^]\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> m"]
            UP_cring.X_closed[of "R[\<X>\<^bsub>n\<^esub>]"] monoid.nat_pow_closed[of "UP (R[\<X>\<^bsub>n\<^esub>])" "X_poly (R[\<X>\<^bsub>n\<^esub>])" m]
      unfolding UP_ring_def UP_cring_def  
      using 81 MP.ring_axioms coord_cring_cring ring.is_monoid by blast
    have 84: "X_poly (R[\<X>\<^bsub>n\<^esub>]) [^]\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> m = up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> m"
      using 83 UP_cring.monom_rep_X_pow[of "R[\<X>\<^bsub>n\<^esub>]" "\<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>" m] 
            monoid.nat_pow_closed[of "UP (R[\<X>\<^bsub>n\<^esub>])" "X_poly (R[\<X>\<^bsub>n\<^esub>])" m] 81
      unfolding UP_cring_def 
       using MP.one_closed coord_cring_cring by presburger       
    thus ?thesis using 77 
      by (metis "82" diff_Suc_1)
  qed
  have 8: "to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) a m)) = 
        to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a)) \<otimes>\<^bsub>UP (R[\<X>\<^bsub>n\<^esub>])\<^esub>
        to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m))"
  proof-
    have 80: "to_polynomial (R [\<X>\<^bsub>n\<^esub>]) a \<in> carrier (UP (R [\<X>\<^bsub>n\<^esub>]))"
      using UP_cring.to_poly_closed[of "R[\<X>\<^bsub>n\<^esub>]" a]  UP_cring_def assms(2) coord_cring_cring 
      by blast
    have 81: "up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R [\<X>\<^bsub>n\<^esub>]\<^esub> m \<in> carrier (UP (R [\<X>\<^bsub>n\<^esub>])) "
    apply(rule UP_ring.monom_closed[of  "R[\<X>\<^bsub>n\<^esub>]"]) unfolding UP_ring_def using MP.one_closed
    apply (simp add: MP.ring_axioms)
      using MP.one_closed by blast     
    have 82: "(from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) a m)) = 
                (from_univ_poly (Suc n) i (to_polynomial (R[\<X>\<^bsub>n\<^esub>]) a)) \<otimes>\<^bsub>(R[\<X>\<^bsub>Suc n\<^esub>])\<^esub> 
                  (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m))"
      using 80 81  from_univ_poly_mult[of i n "to_polynomial (R [\<X>\<^bsub>n\<^esub>]) a" "(up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> m)"] 0  
      by (metis assms(1) less_Suc_eq_le)
    thus ?thesis using to_univ_poly_mult 80 81 
      by (metis assms(1) from_univ_poly_closed less_Suc_eq_le)
  qed
  thus ?thesis 
    using "0" "6" "7" by metis 
qed

lemma from_univ_poly_inverse:
  assumes "i \<le> n"
  assumes "p \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>]))"
  shows "to_univ_poly (Suc n) i (from_univ_poly (Suc n) i p) = p"
proof(rule UP_ring.poly_induct3[of "R[\<X>\<^bsub>n\<^esub>]"])
  show "UP_ring (R [\<X>\<^bsub>n\<^esub>])"
    unfolding UP_ring_def 
    by (simp add: MP.ring_axioms)
  show "p \<in> carrier (UP (R [\<X>\<^bsub>n\<^esub>]))"
    using assms by blast 
  show "\<And>p q. q \<in> carrier (UP (R [\<X>\<^bsub>n\<^esub>])) \<Longrightarrow>
           p \<in> carrier (UP (R [\<X>\<^bsub>n\<^esub>])) \<Longrightarrow>
           to_univ_poly (Suc n) i (from_univ_poly (Suc n) i p) = p \<Longrightarrow>
           to_univ_poly (Suc n) i (from_univ_poly (Suc n) i q) = q \<Longrightarrow>
           to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (p \<oplus>\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> q)) = p \<oplus>\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> q"
  proof- fix p q 
    assume A: "q \<in> carrier (UP (R [\<X>\<^bsub>n\<^esub>]))" "p \<in> carrier (UP (R [\<X>\<^bsub>n\<^esub>]))"
              "to_univ_poly (Suc n) i (from_univ_poly (Suc n) i p) = p"
              "to_univ_poly (Suc n) i (from_univ_poly (Suc n) i q) = q"
    show "to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (p \<oplus>\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> q)) = p \<oplus>\<^bsub>UP (R [\<X>\<^bsub>n\<^esub>])\<^esub> q"
      using A assms
          from_univ_poly_add[of i n p q] 
          to_univ_poly_add[of i n "from_univ_poly (Suc n) i p" "from_univ_poly (Suc n) i q"] 
          from_univ_poly_closed[of i n p] from_univ_poly_closed[of i n q] 
      by presburger
  qed
  show "\<And>a na. a \<in> carrier (R [\<X>\<^bsub>n\<^esub>]) \<Longrightarrow> 
            to_univ_poly (Suc n) i (from_univ_poly (Suc n) i (up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) a na)) = up_ring.monom (UP (R [\<X>\<^bsub>n\<^esub>])) a na"
    using from_univ_poly_monom_inverse[of i ] assms(1) le_imp_less_Suc by presburger
qed

lemma to_univ_poly_eval:
  assumes "i < Suc n"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "x \<in> carrier R"
  assumes  "as = insert_at_index a x i"
  shows "eval_at_point R as p = eval_at_point R a (to_function (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p) (coord_const x))"
proof-
  have 0: "pre_to_univ_poly (Suc n) i p \<in> Pring_set (R[\<X>\<^bsub>n\<^esub>]) {i}"
    using assms pre_to_univ_poly_is_hom(1)[of i "Suc n"] unfolding ring_hom_ring_def 
      unfolding coord_ring_def UP_domain_def   coord_ring_def UP_domain_def
  by (metis MP.Pring_car coord_ring_def diff_Suc_1 pre_to_univ_poly_is_hom(6))
  have 1: " closed_fun (R[\<X>\<^bsub>n\<^esub>]) (\<lambda>n. coord_const x)"
    using assms(4) R.indexed_const_closed 
      unfolding coord_ring_def UP_domain_def
    by blast
  have "(to_function (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p) (coord_const x)) = 
           to_function (R[\<X>\<^bsub>n\<^esub>]) (IP_to_UP i ((pre_to_univ_poly (Suc n) i) p)) (coord_const x)"
    unfolding to_univ_poly_def 
  unfolding coord_ring_def UP_domain_def
    by (metis comp_apply)    
  then have 2: "(to_function (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p) (coord_const x)) = 
              (total_eval (R[\<X>\<^bsub>n\<^esub>]) (\<lambda> i. coord_const x) (pre_to_univ_poly (Suc n) i p))"
      using 0 1 UP_cring.IP_to_UP_poly_eval[of "R[\<X>\<^bsub>n\<^esub>]" 
                                  "(pre_to_univ_poly (Suc n) i) p" i "\<lambda> i. coord_const x"]
      unfolding coord_ring_def UP_cring_def 
      using assms(4) cring.indexed_const_closed R.Pring_is_cring R.cring_axioms 
      by smt
    then show ?thesis using pre_to_univ_poly_eval[of i n p a x as] 
      using assms(1) assms(2) assms(3) assms(4) assms(5) by presburger
qed

text\<open>
  The function \texttt{one\_over\_poly}, introduced in the theory \texttt{Cring\_Poly}, maps a 
  polynomial $p(x)$ to the unique polynomial $q(x)$ which satisfies the relation 
  $q(x) = x^n p(1/x)$. This will be used later to show that the function $f(x) = 1/x$ is 
  semialgebraic over the field $\mathbb{Q}_p$.\<close>
lemma to_univ_poly_one_over_poly:
  assumes "field R"
  assumes "i < (Suc n)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "Q = from_univ_poly (Suc n) i (UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "x \<in> carrier R"
  assumes "x \<noteq> \<zero>"
  assumes "b = insert_at_index a x i"
  assumes "c = insert_at_index a (inv x) i"
  assumes "N = UP_ring.degree (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p)"
  shows "Q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
        "eval_at_point R b Q = (x[^]N) \<otimes> (eval_at_point R c p)"
proof-
  have 0: "(to_univ_poly (Suc n) i p) \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>]))"
    using assms(2) assms(3) less_Suc_eq_le to_univ_poly_closed by blast
  have 1: "(UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p)) \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>]))"
      using 0 assms  UP_domain_def UP_cring.one_over_poly_closed UP_cring_def coord_cring_cring by blast
  show "Q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
    using 1 assms from_univ_poly_closed[of i n] less_Suc_eq_le 
    by blast
  have 2: "coord_const x \<in> Units (R[\<X>\<^bsub>n\<^esub>])"
  proof-

    have 20: "inv x \<in> carrier R"
      using assms(1) assms(6) assms(7) field.field_Units by blast
    have 21: "x \<otimes> (inv x) = \<one> "
    using assms field.field_Units R.Units_r_inv 
    by blast
   have 22: "coord_const x \<in> carrier (R[\<X>\<^bsub>n\<^esub>])" 
     using assms(6) R.indexed_const_closed 
     unfolding coord_ring_def
     by blast
    have 23: "coord_const (inv x) \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
      using "20" R.indexed_const_closed
           unfolding coord_ring_def
by blast
    have 24:  "coord_const x \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> coord_const (inv x)  = coord_const  (x \<otimes> (inv x))"
    using assms(6) 20 R.indexed_const_mult      unfolding coord_ring_def
    by blast
   have 25:  "coord_const x \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> coord_const (inv x)  = \<one>\<^bsub>coord_ring  R n\<^esub>"
       unfolding coord_ring_def
  by (metis "20" "21" R.Pring_one assms(6) R.indexed_const_mult)
   have 26:  "coord_const (inv x) \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> coord_const x  = \<one>\<^bsub>coord_ring  R n\<^esub>"
         unfolding coord_ring_def
  by (metis "21" "22" "23" "24" MP.m_comm R.Pring_one coord_ring_def)
   then show ?thesis
     using 23 Units_def[of "R[\<X>\<^bsub>n\<^esub>]"] "22" "25"
     by blast
  qed
  have 3: "inv\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (coord_const x) = coord_const (inv x)"
  proof-
    have 20: "inv x \<in> carrier R"
      using assms(1) assms(6) assms(7) field.field_Units by blast
    have 21: "x \<otimes> (inv x) = \<one> "
    using assms field.field_Units R.Units_r_inv 
    by blast
   have 22: "coord_const x \<in> carrier (R[\<X>\<^bsub>n\<^esub>])" 
     using assms(6) R.indexed_const_closed 
          unfolding coord_ring_def
by blast
    have 23: "coord_const (inv x) \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
      using "20" R.indexed_const_closed     unfolding coord_ring_def
 by blast
    have 24:  "coord_const x \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> coord_const (inv x)  = coord_const  (x \<otimes> (inv x))"
    using assms(6) 20 R.indexed_const_mult     unfolding coord_ring_def
    by blast
   have 25:  "coord_const x \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> coord_const (inv x)  = \<one>\<^bsub>coord_ring  R n\<^esub>"
          unfolding coord_ring_def
  by (metis "20" "21" R.Pring_one assms(6) R.indexed_const_mult)
   show ?thesis
    using 22 23 25  R.Pring_is_cring[of "{..<n}"] 
    monoid.inv_char[of "R[\<X>\<^bsub>n\<^esub>]"]
     unfolding coord_ring_def

    by (metis R.Pring_is_monoid R.Pring_mult_comm R.is_cring)
  qed
  have 4: "to_function (R[\<X>\<^bsub>n\<^esub>]) (UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))
              (coord_const x) = (coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> 
                            (to_function (R[\<X>\<^bsub>n\<^esub>]) ( (to_univ_poly (Suc n) i p)) (coord_const (inv\<^bsub>R\<^esub> x)))" 
    using 3 assms UP_cring_def UP_cring.one_over_poly_eval[of "R[\<X>\<^bsub>n\<^esub>]" " (to_univ_poly (Suc n) i p)" "coord_const x"]
       unfolding coord_ring_def
       by (metis "0" "2" MP.Units_closed R.Pring_is_cring UP_cring.to_fun_def coord_ring_def R.is_cring)  
  have 5: "eval_at_point R a (to_function (R[\<X>\<^bsub>n\<^esub>]) (UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))
              (coord_const x))
           = eval_at_point R a ((coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N \<otimes>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> 
                            (to_function (R[\<X>\<^bsub>n\<^esub>]) ( (to_univ_poly (Suc n) i p)) (coord_const (inv\<^bsub>R\<^esub> x))) ) "
    using 4 
    by presburger
  have 6: "to_univ_poly (Suc n) i Q =  (UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))"
    using assms from_univ_poly_inverse 
    by (meson "1" less_Suc_eq_le)
  have 7: "eval_at_point R a (to_function (R[\<X>\<^bsub>n\<^esub>]) (UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))
              (coord_const x)) = eval_at_point R b Q"
    using 6 to_univ_poly_eval[of i n Q a x b] assms  \<open>Q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])\<close>
    by smt
  have 8: "(coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    using monoid.nat_pow_closed[of "R[\<X>\<^bsub>n\<^esub>]"]
     unfolding coord_ring_def
  using R.Pring_is_monoid assms(6) R.indexed_const_closed by blast
  have 9: "to_function (R[\<X>\<^bsub>n\<^esub>]) ( (to_univ_poly (Suc n) i p)) (coord_const (inv\<^bsub>R\<^esub> x))
 \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
  proof-
    have 91: "to_univ_poly (Suc n) i p \<in> carrier (UP (R[\<X>\<^bsub>n\<^esub>]))"
      by (simp add: "0")
    have "  coord_const (inv x) \<in> carrier (R[\<X>\<^bsub>n\<^esub>])"
    proof-
      have "inv x \<in> carrier R"
        using assms(1) assms(6) assms(7) field.field_Units by blast      
      then show ?thesis
        using R.indexed_const_closed[of "inv x"] assms
     unfolding coord_ring_def

        by blast
    qed
    then show ?thesis 
    using 91 UP_cring_def[of "R[\<X>\<^bsub>n\<^esub>]" ] UP_cring.to_fun_closed[of "R[\<X>\<^bsub>n\<^esub>]" "to_univ_poly (Suc n) i p" "coord_const (inv\<^bsub>R\<^esub> x)"]
        to_univ_poly_closed[of i n p] UP_domain_def[of "R[\<X>\<^bsub>n\<^esub>]"]   
         unfolding coord_ring_def
         using R.Pring_is_cring R.is_cring 
         by (metis UP_cring.to_fun_def)                 
  qed
  have 10: " eval_at_point R b Q = (eval_at_point R a ((coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N)) \<otimes>
        (eval_at_point R a  (to_function (R[\<X>\<^bsub>n\<^esub>]) ( (to_univ_poly (Suc n) i p)) (coord_const (inv\<^bsub>R\<^esub> x))))"
    using 7 5 eval_at_point_mult[of a n "(coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N" 
        "(to_function (R[\<X>\<^bsub>n\<^esub>]) ( (to_univ_poly (Suc n) i p)) (coord_const (inv\<^bsub>R\<^esub> x)))"]  
       "8" "9" assms(5) 
    by presburger
  have 11: "inv x \<in> carrier R"
    using assms(1) assms(6) assms(7) field.field_Units by blast
  have 12: " eval_at_point R b Q = (eval_at_point R a ((coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N)) \<otimes>
        (eval_at_point R c p)"
     using 10 11 to_univ_poly_eval[of i n p a "inv x" c] assms(2) assms(3) assms(5) assms(9) 
     by presburger
   show 12: " eval_at_point R b Q = (x[^]N) \<otimes>
        (eval_at_point R c p)"
  proof-
    have 0: "(coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N = coord_const (x[^]N)"
    proof(induction N)
      case 0
      have 00: "coord_const x [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> (0::nat) = \<one>\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>"
        using nat_pow_def[of "R[\<X>\<^bsub>n\<^esub>]" _ "(0::nat)"] 
          unfolding coord_ring_def
          by (meson Group.nat_pow_0)
        then show ?case 
     unfolding coord_ring_def
        by (metis Group.nat_pow_0 R.Pring_one)
    next
      case (Suc N) fix N::nat assume IH: "coord_const x [^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub> N = coord_const (x [^] N)"
      then show ?case 
        using R.indexed_const_mult Group.nat_pow_Suc Suc.IH assms(6) R.nat_pow_closed
           unfolding coord_ring_def 
           by (metis )           
       qed
    have 1: "(eval_at_point R a ((coord_const x)[^]\<^bsub>R[\<X>\<^bsub>n\<^esub>]\<^esub>N)) = x[^]N"
      using 0 
      by (metis assms(5) assms(6) eval_at_point_const R.nat_pow_closed)
    show ?thesis using 0 1 "12" 
      by presburger
  qed
qed

lemma to_univ_poly_one_over_poly':
  assumes "field R"
  assumes "i < (Suc n)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "Q = from_univ_poly (Suc n) i (UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))"
  assumes "a \<in> carrier (R\<^bsup>n\<^esup>)"
  assumes "x \<in> carrier R"
  assumes "x \<noteq> \<zero>"
  assumes "b = insert_at_index a x i"
  assumes "c = insert_at_index a (inv x) i"
  assumes "N = UP_ring.degree (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p)"
  assumes "q = (pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>(k::nat)\<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> Q"
  shows "q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
        "eval_at_point R b q = (x[^](N + k)) \<otimes> (eval_at_point R c p)"
proof-
  have 0: "(pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>k \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
    using pvar_closed[of i "Suc n"] monoid.nat_pow_closed[] 
        unfolding coord_ring_def
 by (metis R.Pring_is_monoid assms(2))
  have 1: "b \<in> carrier (R\<^bsup>Suc n\<^esup>)"
    using assms(2) assms(5) assms(6) assms(8) insert_at_index_closed less_Suc_eq_le
    by blast
  have 11 : "c \<in> carrier (R\<^bsup>Suc n\<^esup>)"
  proof-
    have "inv x \<in> carrier R"
      using assms field.field_Units 
      by blast
    then show ?thesis 
    using assms insert_at_index_closed less_Suc_eq_le 
    by blast  
  qed
  have 2: "eval_at_point R b q = eval_at_point R b ((pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>(k::nat)) 
                                 \<otimes> eval_at_point R b Q"
    using assms 0 1      unfolding coord_ring_def
  by (metis R.Pring_mult coord_ring_def eval_at_point_mult to_univ_poly_one_over_poly(1))
  have 3: "eval_at_point R b ((pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>(k::nat)) = 
           x[^](k::nat)"   
  proof(induction k)
    case 0
    have T0: "eval_at_point R b ((pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>(0::nat)) = 
              eval_at_point R b (\<one>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>)"
      using nat_pow_def[of "R[\<X>\<^bsub>Suc n\<^esub>]" "pvar R i" "0::nat"] 
      by (metis Group.nat_pow_0)  
    then show ?case 
      by (metis "1" assms(2) eval_at_point_nat_pow R.nat_pow_0 local.pvar_closed)   
  next
    case (Suc k) fix k::nat
    assume IH: "eval_at_poly R (pvar R i [^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> k) b = x [^] k "
    have 0: "eval_at_poly R (pvar R i) b = b!i"
      using eval_pvar[of i "Suc n"] assms "1" 
      by blast
    have "length a = n"
      using assms(5) cartesian_power_car_memE by blast
    then have "eval_at_poly R (pvar R i) b = x"
      using 0 assms(8) insert_at_index_eq[of i a x] 
      by (metis assms(2) less_Suc_eq_le)
    then show ?case 
      using "1" assms(2) eval_at_point_nat_pow local.pvar_closed 
      by blast
  qed
  have 4: "eval_at_point R b Q = (x[^]N) \<otimes> (eval_at_point R c p)"
    using to_univ_poly_one_over_poly(2)[of i n p Q a x b c N] assms(1) assms(10) assms(2)
          assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) 
    by blast
  have 5: "eval_at_point R b q = x[^](k::nat) \<otimes> ((x[^]N) \<otimes> (eval_at_point R c p))"
     using 4 3 2 
     by presburger
  show 6: "eval_at_point R b q = x[^](N + k) \<otimes> (eval_at_point R c p)"
  proof-

    have 60: "x[^](k::nat) \<in> carrier R" 
      using assms(6) by blast
    have 61: "x[^]N \<in> carrier R" 
      using assms(6) by blast
    have 62: "eval_at_point R c p \<in> carrier R"
      using eval_at_point_closed[of c "Suc n" p]  \<open>c \<in> carrier (R\<^bsup>Suc n\<^esup>)\<close> assms(3) 
      by blast
    show ?thesis using 5 60 61 62
      by (metis assms(6) R.m_assoc R.m_comm R.nat_pow_mult)      
  qed
  show "q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
    using assms 
     unfolding coord_ring_def
     using 0 R.Pring_mult_closed to_univ_poly_one_over_poly(1) 
     by (metis coord_ring_def)
  
qed

lemma to_univ_poly_one_over_poly'':
  assumes "field R"
  assumes "i < (Suc n)"
  assumes "p \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  assumes "N \<ge>  UP_ring.degree (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p)"
  shows "\<exists> q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>]). ( \<forall> x \<in> carrier R - {\<zero>}. ( \<forall> a \<in>  carrier (R\<^bsup>n\<^esup>).
        eval_at_point R (insert_at_index a x i) q =  (x[^]N) \<otimes> (eval_at_point R (insert_at_index a (inv x) i) p)))"
proof-
  obtain Q where Q_def: 
    "Q = from_univ_poly (Suc n) i (UP_cring.one_over_poly (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))"
    by blast 
  obtain k where k_def: "k = (N - UP_ring.degree (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p))"
    by blast 
  obtain q where q_def: "q = (pvar R i)[^]\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub>(k::nat)\<otimes>\<^bsub>R[\<X>\<^bsub>Suc n\<^esub>]\<^esub> Q"
    by blast 
  have 0: " ( \<forall> x \<in> carrier R - {\<zero>}.( \<forall> a \<in>  carrier (R\<^bsup>n\<^esup>).
        eval_at_point R (insert_at_index a x i) q =  (x[^]N) \<otimes> (eval_at_point R (insert_at_index a (inv x) i) p)))"
  proof fix x
    assume A0: " x \<in> carrier R - {\<zero>}"
    show " \<forall>a\<in>carrier (R\<^bsup>n\<^esup>). eval_at_poly R q (insert_at_index a x i) = x [^] N \<otimes> eval_at_poly R p (insert_at_index a (inv x) i)"
    proof fix a assume A1: "a \<in> carrier (R\<^bsup>n\<^esup>)"
      obtain l where l_def: "l = UP_ring.degree (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p)"
        by blast 
      have "eval_at_poly R q (insert_at_index a x i) = x [^] (l + k) \<otimes> eval_at_poly R p (insert_at_index a (inv x) i)"
        using assms A1 A0 to_univ_poly_one_over_poly'(2)[of i n p Q a x "insert_at_index a x i" "insert_at_index a (inv x) i" l q k]
              Q_def l_def q_def 
        by blast
      then show " eval_at_poly R q (insert_at_index a x i) = x [^] N \<otimes> eval_at_poly R p (insert_at_index a (inv x) i)"
        using k_def  assms l_def add_diff_inverse_nat less_Suc_eq not_less_eq
        by (metis diff_diff_cancel diff_less_Suc)       
    qed
  qed
  have 1: "q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
  proof-
    obtain a where a_def: "a = map (\<lambda>i. \<one>) [(0::nat)..<n] "
      by blast 
    have a_car: "a \<in> carrier (R\<^bsup>n\<^esup>)"
      apply(rule cartesian_power_car_memI')
      using a_def 
       apply (metis Ex_list_of_length coeff_list length_map length_rev)
    proof- fix i assume A: "i < n"
      then have "a!i = \<one>"
        using a_def 
        by (metis R_list_length length_map map_nth nth_map)
      then show "a ! i \<in> carrier R"
        using a_def  R.one_closed 
        by metis 
    qed
    then show "q \<in> carrier (R[\<X>\<^bsub>Suc n\<^esub>])"
      using assms q_def k_def Q_def to_univ_poly_one_over_poly'(1)[of i n p Q a \<one> _ _ "deg (R[\<X>\<^bsub>n\<^esub>]) 
          (to_univ_poly (Suc n) i p)" q "N -deg (R[\<X>\<^bsub>n\<^esub>]) (to_univ_poly (Suc n) i p)" ]
      using one_closed local.one_neq_zero by blast      
  qed
  show ?thesis 
    using 0 1 by blast 
qed

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Restricted Inverse Images and Complements\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  This section introduces some versions of basic set operations for extensional functions and sets.
  We would like a version of the inverse image which intersects the inverse image of a function 
  with the set \texttt{carrier }$(R^n)$, and a version of the complement of a set which takes the
  comeplement relative to \texttt{carrier }$(R^n)$. These will have to be defined in parametrized 
  families, with one such object for each natural number $n$.\<close>
definition evimage (infixr "\<inverse>\<index>" 90) where
"evimage n f S = ((f -` S) \<inter> carrier (R\<^bsup>n\<^esup>))"

definition euminus_set :: "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set" ("_ \<^sup>c\<index>" 70) where
"S\<^sup>c\<^bsub>n\<^esub> = carrier (R\<^bsup>n\<^esup>) - S"

lemma extensional_vimage_closed:
"f \<inverse>\<^bsub>n\<^esub> S \<subseteq> carrier (R\<^bsup>n\<^esup>)"
  unfolding evimage_def by blast 

subsection \<open>Inverse image of a function\<close>

lemma evimage_eq [simp]: "a \<in> f \<inverse>\<^bsub>n\<^esub> B \<longleftrightarrow> a \<in> carrier (R\<^bsup>n\<^esup>) \<and> f a \<in> B"
  unfolding evimage_def 
  by blast
  
lemma evimage_singleton_eq: "a \<in> f \<inverse>\<^bsub>n\<^esub> {b} \<longleftrightarrow> a \<in> carrier (R\<^bsup>n\<^esup>) \<and>  f a = b"
  unfolding evimage_def 
  by blast

lemma evimageI [intro]: "a \<in> carrier (R\<^bsup>n\<^esup>) \<Longrightarrow> f a = b \<Longrightarrow> b \<in> B \<Longrightarrow> a \<in> f \<inverse>\<^bsub>n\<^esub> B"
  unfolding vimage_def 
  using evimage_eq by blast  

lemma evimageI2: "a \<in> carrier (R\<^bsup>n\<^esup>) \<Longrightarrow> f a \<in> A \<Longrightarrow> a \<in> f \<inverse>\<^bsub>n\<^esub> A"
  unfolding vimage_def by fast

lemma evimageE [elim!]: "a \<in> f \<inverse>\<^bsub>n\<^esub> B \<Longrightarrow> (\<And>x. f a = x \<Longrightarrow> x \<in> B \<Longrightarrow> p) \<Longrightarrow> p"
  unfolding evimage_def 
  by blast
  
lemma evimageD: "a \<in> f\<inverse>\<^bsub>n\<^esub> A \<Longrightarrow> f a \<in> A"
  unfolding vimage_def by fast

lemma evimage_empty [simp]: "f \<inverse>\<^bsub>n\<^esub> {} = {}"
  by blast

lemma evimage_Compl:
  assumes "f \<in> carrier (R\<^bsup>n\<^esup>) \<rightarrow> carrier (R\<^bsup>m\<^esup>)"
  shows  "(f \<inverse>\<^bsub>n\<^esub>(A\<^sup>c\<^bsub>m\<^esub>)) = ((f -` A)\<^sup>c\<^bsub>n\<^esub>) "
proof-
  have "(f \<inverse>\<^bsub>n\<^esub>(A\<^sup>c\<^bsub>m\<^esub>)) =  ((f -` (carrier (R\<^bsup>m\<^esup>))  - (f -`  A))) \<inter> carrier (R\<^bsup>n\<^esup>)"
    unfolding evimage_def euminus_set_def by blast 
  hence 0: "(f \<inverse>\<^bsub>n\<^esub>(A\<^sup>c\<^bsub>m\<^esub>)) =  (f -` (carrier (R\<^bsup>m\<^esup>))  \<inter> carrier (R\<^bsup>n\<^esup>))  - (f -`  A)"
    by (simp add: Int_Diff Int_commute)
  have  "(f -` (carrier (R\<^bsup>m\<^esup>))  \<inter> carrier (R\<^bsup>n\<^esup>)) = carrier (R\<^bsup>n\<^esup>)"
  proof
    show "f -` carrier (R\<^bsup>m\<^esup>) \<inter> carrier (R\<^bsup>n\<^esup>) \<subseteq> carrier (R\<^bsup>n\<^esup>)"
      by auto 
    show "carrier (R\<^bsup>n\<^esup>) \<subseteq> f -` carrier (R\<^bsup>m\<^esup>) \<inter> carrier (R\<^bsup>n\<^esup>)"
      using assms by blast 
  qed
  thus ?thesis using 0 
    by (simp add: euminus_set_def)
qed

lemma evimage_Un [simp]: "f \<inverse>\<^bsub>n\<^esub> (A \<union> B) = (f \<inverse>\<^bsub>n\<^esub> A) \<union> (f \<inverse>\<^bsub>n\<^esub> B)"
  unfolding evimage_def by blast 

lemma evimage_Int [simp]: "f \<inverse>\<^bsub>n\<^esub> (A \<inter> B) = (f \<inverse>\<^bsub>n\<^esub> A) \<inter> (f \<inverse>\<^bsub>n\<^esub> B)"
  unfolding evimage_def by blast 

lemma evimage_Collect_eq [simp]: "f \<inverse>\<^bsub>n\<^esub> Collect p = {y \<in> carrier (R\<^bsup>n\<^esup>). p (f y)}"
  unfolding evimage_def by blast 

lemma evimage_Collect: "(\<And>x. x \<in> carrier (R\<^bsup>n\<^esup>) \<Longrightarrow> p (f x) = Q x) \<Longrightarrow> f \<inverse>\<^bsub>n\<^esub> (Collect p) = Collect Q \<inter> carrier (R\<^bsup>n\<^esup>)"
  unfolding evimage_def by blast 

lemma evimage_insert: "f \<inverse>\<^bsub>n\<^esub> (insert a B) = (f \<inverse>\<^bsub>n\<^esub> {a}) \<union> (f \<inverse>\<^bsub>n\<^esub> B)"
  \<comment> \<open>NOT suitable for rewriting because of the recurrence of \<open>{a}\<close>.\<close>
  unfolding evimage_def by blast 

lemma evimage_Diff: "f \<inverse>\<^bsub>n\<^esub> (A - B) = (f \<inverse>\<^bsub>n\<^esub> A) - (f \<inverse>\<^bsub>n\<^esub> B)"
  unfolding evimage_def by blast 

lemma evimage_UNIV [simp]: "f \<inverse>\<^bsub>n\<^esub> UNIV = carrier (R\<^bsup>n\<^esup>)"
  unfolding evimage_def by blast 

lemma evimage_mono: "A \<subseteq> B \<Longrightarrow> f \<inverse>\<^bsub>n\<^esub> A \<subseteq> f \<inverse>\<^bsub>n\<^esub> B"
  \<comment> \<open>monotonicity\<close>
  unfolding evimage_def by blast 

lemma evimage_image_eq: "(f \<inverse>\<^bsub>n\<^esub> (f ` A)) = {y \<in> carrier (R\<^bsup>n\<^esup>). \<exists>x\<in>A. f x = f y}"
  unfolding evimage_def  by (blast intro: sym)

lemma image_evimage_subset: "f ` (f \<inverse>\<^bsub>n\<^esub> A) \<subseteq> A"
  by blast

lemma image_evimage_eq [simp]: "f ` (f \<inverse>\<^bsub>n\<^esub> A) = A \<inter> (f ` carrier (R\<^bsup>n\<^esup>))"
  unfolding evimage_def   by blast

lemma image_subset_iff_subset_evimage: "A \<subseteq> carrier (R\<^bsup>n\<^esup>) \<Longrightarrow> f ` A \<subseteq> B \<longleftrightarrow> A \<subseteq> f \<inverse>\<^bsub>n\<^esub> B"
  by blast

lemma evimage_const [simp]: "((\<lambda>x. c) \<inverse>\<^bsub>n\<^esub> A) = (if c \<in> A then carrier (R\<^bsup>n\<^esup>) else {})"
  unfolding evimage_def using vimage_const[of c A] 
  by (smt Int_commute inf_bot_right inf_top.right_neutral)

lemma evimage_if [simp]: "((\<lambda>x. if x \<in> B then c else d) \<inverse>\<^bsub>n\<^esub> A) =
   (if c \<in> A then (if d \<in> A then carrier (R\<^bsup>n\<^esup>) else B \<inter> carrier (R\<^bsup>n\<^esup>) )
    else if d \<in> A then B\<^sup>c\<^bsub>n\<^esub>  else {})"
unfolding evimage_def euminus_set_def using vimage_if[of B c d A]  
  by (metis Diff_Compl Diff_UNIV Diff_empty Int_commute double_compl)

lemma evimage_inter_cong: "(\<And> w. w \<in> S \<Longrightarrow> f w = g w) \<Longrightarrow> f \<inverse>\<^bsub>n\<^esub> y \<inter> S = g \<inverse>\<^bsub>n\<^esub> y \<inter> S"
unfolding evimage_def 
  by (smt Int_assoc Int_commute vimage_inter_cong)

lemma evimage_ident [simp]: "(\<lambda>x. x) \<inverse>\<^bsub>n\<^esub> Y = Y \<inter> carrier (R\<^bsup>n\<^esup>)"
unfolding evimage_def 
  by blast


end  




end
