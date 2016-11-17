(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Deep Learning Networks\<close>

theory DL_Network 
imports Tensor_Product Real DL_Missing_Matrix
"../Jordan_Normal_Form/Matrix" Tensor_Unit_Vec DL_Flatten_Matrix DL_Missing_List
begin

text \<open>This symbol is used for the Tensor product:\<close>
no_notation Group.monoid.mult (infixl "\<otimes>\<index>" 70)

datatype 'a convnet = Input nat | Conv 'a "'a convnet" | Pool "'a convnet" "'a convnet"

fun input_sizes :: "'a convnet \<Rightarrow> nat list" where
"input_sizes (Input M) = [M]" |
"input_sizes (Conv A m) = input_sizes m" |
"input_sizes (Pool m1 m2) = input_sizes m1 @ input_sizes m2"

fun count_weights :: "(nat \<times> nat) convnet \<Rightarrow> nat" where
"count_weights (Input M) = 0" |
"count_weights (Conv (r0, r1) m) = r0 * r1 + count_weights m" |
"count_weights (Pool m1 m2) = count_weights m1 + count_weights m2"

fun output_size :: "(nat \<times> nat) convnet \<Rightarrow> nat" where
"output_size (Input M) = M" |
"output_size (Conv (r0,r1) m) = r0" |
"output_size (Pool m1 m2) = output_size m1"

inductive valid_net :: "(nat\<times>nat) convnet \<Rightarrow> bool" where
"valid_net (Input M)" |
"output_size m = r1 \<Longrightarrow> valid_net m \<Longrightarrow> valid_net (Conv (r0,r1) m)" |
"output_size m1 = output_size m2 \<Longrightarrow> valid_net m1 \<Longrightarrow> valid_net m2 \<Longrightarrow> valid_net (Pool m1 m2)"


fun insert_weights :: "(nat \<times> nat) convnet \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real mat convnet" where
"insert_weights (Input M) w = Input M" |
"insert_weights (Conv (r0,r1) m) w = Conv 
  (extract_matrix w r0 r1) 
  (insert_weights m (\<lambda>i. w (i+r0*r1)))" |
"insert_weights (Pool m1 m2) w = Pool 
  (insert_weights m1 w)
  (insert_weights m2 (\<lambda>i. w (i+(count_weights m1))))"

fun remove_weights :: "real mat convnet \<Rightarrow> (nat \<times> nat) convnet" where
"remove_weights (Input M) = Input M" |
"remove_weights (Conv A m) = Conv (dim\<^sub>r A, dim\<^sub>c A) (remove_weights m)" |
"remove_weights (Pool m1 m2) = Pool (remove_weights m1) (remove_weights m2)"

abbreviation "output_size' == (\<lambda>m. output_size (remove_weights m))"
abbreviation "valid_net' == (\<lambda>m. valid_net (remove_weights m))"

fun evaluate_net :: "real mat convnet \<Rightarrow> real vec list \<Rightarrow> real vec" where
"evaluate_net (Input M) inputs = hd inputs" |
"evaluate_net (Conv A m) inputs = A \<otimes>\<^sub>m\<^sub>v evaluate_net m inputs" |
"evaluate_net (Pool m1 m2) inputs = component_mult
  (evaluate_net m1 (take (length (input_sizes m1)) inputs)) 
  (evaluate_net m2 (drop (length (input_sizes m1)) inputs))"

definition mat_tensorlist_mult :: "real mat \<Rightarrow> real tensor vec \<Rightarrow> nat list \<Rightarrow> real tensor vec"
where "mat_tensorlist_mult A Ts ds
 = Matrix.vec (dim\<^sub>r A) (\<lambda>j. tensor_from_lookup ds (\<lambda>is. (A \<otimes>\<^sub>m\<^sub>v (map\<^sub>v (\<lambda>T. Tensor.lookup T is) Ts)) $j))"

lemma insert_weights_cong:
assumes "(\<And>i. i<count_weights m \<Longrightarrow> w1 i = w2 i)"
shows "insert_weights m w1 = insert_weights m w2"
using assms proof (induction m arbitrary: w1 w2)
  case Input
  then show ?case by simp 
next
  case (Conv r01 m)
  then obtain r0 r1 where "r01 = (r0,r1)" by (meson surj_pair)
  have 2:"insert_weights m (\<lambda>i. w1 (i + r0 * r1)) = insert_weights m (\<lambda>i. w2 (i + r0 * r1))" using Conv 
    using \<open>r01 = (r0, r1)\<close> add.commute add_less_cancel_right count_weights.simps(2) by fastforce
  then show ?case unfolding `r01 = (r0,r1)` insert_weights.simps 
    by (metis Conv.prems \<open>r01 = (r0, r1)\<close> count_weights.simps(2) extract_matrix_cong trans_less_add1)
next
  case (Pool m1 m2)
  have 1:"insert_weights m1 w1 = insert_weights m1 w2" 
    using Pool(1)[of w1 w2] Pool(3)[unfolded count_weights.simps] by simp
  have 2:"insert_weights m2 (\<lambda>i. w1 (i + count_weights m1)) = insert_weights m2 (\<lambda>i. w2 (i + count_weights m1))" 
    using Pool(2)[of "\<lambda>i. w1 (i + count_weights m1)" "\<lambda>i. w2 (i + count_weights m1)"] Pool(3)[unfolded count_weights.simps] by simp
  show ?case unfolding insert_weights.simps 1 2 by metis
qed

lemma dims_mat_tensorlist_mult:
assumes "T\<in>set\<^sub>v (mat_tensorlist_mult A Ts ds)"
shows "Tensor.dims T = ds"
proof -
  obtain j where "T = tensor_from_lookup ds (\<lambda>is. (A \<otimes>\<^sub>m\<^sub>v (map\<^sub>v (\<lambda>T. Tensor.lookup T is) Ts)) $j)"
    using vec_setE[OF assms, unfolded mat_tensorlist_mult_def] by (metis vec_dim_vec vec_index_vec)
  then show ?thesis by (simp add: length_tensor_vec_from_lookup tensor_from_lookup_def)
qed

fun tensors_from_net :: "real mat convnet \<Rightarrow> real tensor vec" where
"tensors_from_net (Input M) = Matrix.vec M (\<lambda>i. unit_vec M i)" |
"tensors_from_net (Conv A m) = mat_tensorlist_mult A (tensors_from_net m) (input_sizes m)" |
"tensors_from_net (Pool m1 m2) = component_mult (tensors_from_net m1) (tensors_from_net m2)"

lemma output_size_correct_tensors:
assumes "valid_net' m"
shows "output_size' m = dim\<^sub>v (tensors_from_net m)"
using assms proof (induction m)
  case Input
  then show ?case by simp
next
  case (Conv A m)
  then show ?case 
    unfolding remove_weights.simps output_size.simps tensors_from_net.simps
    using mat_tensorlist_mult_def by auto
next
  case (Pool m1 m2)
  then show ?case by (metis convnet.distinct(3) convnet.distinct(5) convnet.inject(3) dim_component_mult 
    min.idem output_size.simps(3) remove_weights.simps(3) tensors_from_net.simps(3) valid_net.simps)
qed


lemma output_size_correct:
assumes "valid_net' m"
and "map dim\<^sub>v inputs = input_sizes m"
shows "output_size' m = dim\<^sub>v (evaluate_net m inputs)"
using assms proof (induction m arbitrary:inputs)
  case Input
  then show ?case using length_Cons list.map_sel(1) list.sel(1) list.simps(8) list.size(3) nat.simps(3) by auto
next
  case (Conv A m)
  then show ?case unfolding evaluate_net.simps remove_weights.simps output_size.simps dim_mat_mult_vec
    by auto
next
  case (Pool m1 m2)
  then have "valid_net' m1" "valid_net' m2" 
    using convnet.distinct(3) convnet.distinct(5) convnet.inject(3) remove_weights.simps(3) valid_net.cases by fastforce+
  moreover have "map dim\<^sub>v (take (length (input_sizes m1)) inputs) = input_sizes m1"
       "map dim\<^sub>v (drop (length (input_sizes m1)) inputs) = input_sizes m2"
    using Pool.prems(2) by (metis append_eq_conv_conj drop_map input_sizes.simps(3) take_map)+
  ultimately have 
    "output_size' m1 = dim\<^sub>v (evaluate_net m1 (take (length (input_sizes m1)) inputs))"
    "output_size' m2 = dim\<^sub>v (evaluate_net m2 (drop (length (input_sizes m1)) inputs))"
    using Pool.IH by blast+
  then show ?case unfolding evaluate_net.simps remove_weights.simps output_size.simps 
    by (metis Pool.prems(1) \<open>valid_net' m1\<close> \<open>valid_net' m2\<close> dim_component_mult 
     output_size.simps(3) output_size_correct_tensors remove_weights.simps(3) tensors_from_net.simps(3))
qed

lemma input_sizes_remove_weights: "input_sizes m = input_sizes (remove_weights m)"
  by (induction m; simp)

lemma dims_tensors_from_net:
assumes "T \<in> set\<^sub>v (tensors_from_net m)"
shows "Tensor.dims T = input_sizes m"
using assms proof (induction m arbitrary:T)
  case (Input M)
  then obtain j where "T = unit_vec M j" 
    using vec_setE tensors_from_net.simps(1) by (metis vec_dim_vec vec_index_vec)
  then show ?case by (simp add: dims_unit_vec)
next
  case (Conv A m)   
  then show ?case unfolding remove_weights.simps input_sizes.simps  
    using dims_mat_tensorlist_mult by (simp add: input_sizes_remove_weights)
next
  case (Pool m1 m2 T)
  then obtain i where 
    "component_mult (tensors_from_net m1) (tensors_from_net m2) $ i = T" 
    "i < dim\<^sub>v (tensors_from_net m1)" "i < dim\<^sub>v (tensors_from_net m2)"
    using tensors_from_net.simps vec_setE dim_component_mult by (metis min.strict_boundedE)
  then obtain T1 T2 where "T = T1 \<otimes> T2" "T1 \<in> set\<^sub>v (tensors_from_net m1)" "T2 \<in> set\<^sub>v (tensors_from_net m2)" 
    using vec_setI by (metis index_component_mult)         
  then show ?case unfolding remove_weights.simps input_sizes.simps by (simp add: Pool.IH(1) Pool.IH(2))
qed

definition base_input :: "real mat convnet \<Rightarrow> nat list \<Rightarrow> real vec list" where
"base_input m is = (map (\<lambda>(n, i). unit\<^sub>v n i) (zip (input_sizes m) is))"

lemma base_input_length:
assumes "is \<lhd> input_sizes m"
shows "input_sizes m = map dim\<^sub>v (base_input m is)" 
proof (rule nth_equalityI)
  have "length (input_sizes m) = length is" using assms valid_index_length by auto
  then show "length (input_sizes m) = length (map dim\<^sub>v (base_input m is))" unfolding base_input_def by auto
  { 
    fix i
    assume "i<length (input_sizes m)"
    then have "map (\<lambda>(n, i). unit\<^sub>v n i) (zip (input_sizes m) is) ! i = unit\<^sub>v (input_sizes m ! i) (is ! i)" 
      using \<open>length (input_sizes m) = length is\<close> by auto
    then have "input_sizes m ! i = map dim\<^sub>v (base_input m is) ! i" unfolding base_input_def using vec_unit_index(3) 
      using \<open>i < length (input_sizes m)\<close> \<open>length (input_sizes m) = length (map dim\<^sub>v (base_input m is))\<close>
       base_input_def assms length_map nth_map valid_index_lt by (simp add: input_sizes_remove_weights)
  }
  then show "\<forall>i<length (input_sizes m). input_sizes m ! i = map dim\<^sub>v (base_input m is) ! i" by auto
qed

lemma nth_mat_tensorlist_mult:
assumes "\<And>A. A\<in>set\<^sub>v Ts \<Longrightarrow> dims A = ds"
assumes "i < dim\<^sub>r A"
assumes "dim\<^sub>v Ts = dim\<^sub>c A"
shows "mat_tensorlist_mult A Ts ds $ i = listsum ds (map (\<lambda>j. (A $$ (i,j)) \<cdot> Ts $ j) [0..<dim\<^sub>v Ts])"
  (is "_ = listsum ds ?Ts'")
proof (rule tensor_lookup_eqI)
  have dims_Ts':"\<And>T. T\<in>set ?Ts' \<Longrightarrow> dims T = ds"
  proof -
    fix T assume "T\<in>set ?Ts'"
    then obtain k where "T = ?Ts' ! k" and "k < length ?Ts'" "k < dim\<^sub>v Ts" using in_set_conv_nth by force
    show "dims T = ds" unfolding `T = ?Ts' ! k`   nth_map[OF \<open>k < length ?Ts'\<close>[unfolded length_map]] 
      using assms(1) `k < dim\<^sub>v Ts` 
      by (simp add: \<open>k < length (map (\<lambda>j. A $$ (i, j) \<cdot> Ts $ j) [0..<dim\<^sub>v Ts])\<close> vec_setI)
  qed
  then show dims_eq:"dims (mat_tensorlist_mult A Ts ds $ i) = dims (Tensor_Plus.listsum ds (map (\<lambda>j. A $$ (i, j) \<cdot> Ts $ j) [0..<dim\<^sub>v Ts]))"
    using dims_mat_tensorlist_mult assms  mat_tensorlist_mult_def listsum_dims
    by (metis (no_types, lifting) vec_dim_vec vec_setI)

  fix "is" assume is_valid:"is \<lhd> dims (mat_tensorlist_mult A Ts ds $ i)"
  then have "is \<lhd> ds" using dims_eq dims_Ts' listsum_dims by (metis (no_types, lifting))
 
  have summand_eq: "\<And>j. j \<in> {0 ..< dim\<^sub>v Ts} \<Longrightarrow> row A i $ j * (map\<^sub>v (\<lambda>T. Tensor.lookup T is) Ts) $ j = lookup (A $$ (i, j) \<cdot> Ts $ j) is"
    using vec_index_vec `i<dim\<^sub>r A` row_def `dim\<^sub>v Ts = dim\<^sub>c A` 
     \<open>is \<lhd> ds\<close> assms(1) lookup_smult atLeastLessThan_iff vec_index_map(1) vec_setI by metis

  have "lookup (mat_tensorlist_mult A Ts ds $ i) is = (A \<otimes>\<^sub>m\<^sub>v (map\<^sub>v (\<lambda>T. Tensor.lookup T is) Ts)) $ i"
    unfolding mat_tensorlist_mult_def using lookup_tensor_from_lookup[OF `is \<lhd> ds`] using `i<dim\<^sub>r A` by auto
  also have "... = row A i \<bullet> map\<^sub>v (\<lambda>T. Tensor.lookup T is) Ts" 
    using `i<dim\<^sub>r A` by simp
  also have "... = (\<Sum> j \<in> {0 ..< dim\<^sub>v Ts}. row A i $ j * (map\<^sub>v (\<lambda>T. Tensor.lookup T is) Ts) $ j)" 
    unfolding scalar_prod_def rows_nth[OF `i<dim\<^sub>r A`] by simp
  also have "... = (\<Sum>j\<in>{0..<dim\<^sub>v Ts}. lookup (A $$ (i, j) \<cdot> Ts $ j) is)" using summand_eq by force
  also have "... = (\<Sum>A\<leftarrow>?Ts'. lookup A is)" unfolding map_map 
    Groups_List.setsum_set_upt_conv_listsum_nat[symmetric]  atLeastLessThan_upt[symmetric] by auto
  also have "... = lookup (listsum ds ?Ts') is" using lookup_listsum[OF `is \<lhd> ds`] dims_Ts' by fastforce
  finally show "lookup (mat_tensorlist_mult A Ts ds $ i) is = lookup (listsum ds ?Ts') is" by metis
qed

lemma lookup_tensors_from_net:
assumes "valid_net' m"
and "is \<lhd> input_sizes m"
and "j < output_size' m"
shows "Tensor.lookup (tensors_from_net m $ j) is = evaluate_net m (base_input m is) $ j"
using assms proof (induction m arbitrary:j "is")
  case (Input M)
  then have "j < M" using output_size.simps(1) using Input by auto
  then have 1:"tensors_from_net (Input M) $ j = unit_vec M j" by simp
  obtain i where "is = [i]" "i<M" using Input Suc_length_conv input_sizes.simps(1) length_0_conv list.size(3) valid_index_length by auto
  then have 2:"Tensor.lookup (tensors_from_net (Input M) $ j) is = (if i=j then 1 else 0)" using lookup_unit_vec 1 by metis
  have "evaluate_net (Input M) (map (\<lambda>(n, i). unit\<^sub>v n i) (zip (input_sizes (Input M)) is)) = unit\<^sub>v M i" using `is = [i]` by auto
  then show ?case using 2 \<open>j < M\<close> base_input_def by (simp add: \<open>i < M\<close>)
next
  case (Conv A m j "is")
  have is_valid:"is \<lhd> input_sizes m" using Conv.prems by simp
  have valid_net:"valid_net' m" using Conv.prems(1) unfolding remove_weights.simps 
    using valid_net.simps convnet.distinct(1) convnet.distinct(5) convnet.inject(2) by blast
  then have length_em: "dim\<^sub>v (evaluate_net m (base_input m is)) = output_size' m"
    using output_size_correct base_input_length is_valid by metis

  have IH':"map\<^sub>v (\<lambda>T. Tensor.lookup T is) (tensors_from_net m) =
                evaluate_net m (base_input m is)"
  proof (rule vec_eqI)
    show equal_lengths: "dim\<^sub>v (map\<^sub>v (\<lambda>T. lookup T is) (tensors_from_net m)) 
      = dim\<^sub>v (evaluate_net m (base_input m is))" using length_em 
      by (simp add: output_size_correct_tensors valid_net)
    show "\<And>i. i < dim\<^sub>v (evaluate_net m (base_input m is)) \<Longrightarrow>
         map\<^sub>v (\<lambda>T. lookup T is) (tensors_from_net m) $ i = evaluate_net m (base_input m is) $ i" 
    proof -
      fix i 
      assume "i < dim\<^sub>v (evaluate_net m (base_input m is))"
      then have "i < output_size' m" using equal_lengths length_em by auto
      then show "map\<^sub>v (\<lambda>T. lookup T is) (tensors_from_net m) $ i
        = evaluate_net m (base_input m is) $ i"
        using Conv.IH is_valid equal_lengths valid_net base_input_def length_em nth_map_upt 
        length_map nth_map by auto
    qed
  qed

  have "Tensor.lookup ((tensors_from_net (Conv A m)) $ j) is = 
    (A \<otimes>\<^sub>m\<^sub>v (map\<^sub>v (\<lambda>T. Tensor.lookup T is) (tensors_from_net m))) $ j"
  proof -
    have "dim\<^sub>v (tensors_from_net (Conv A m)) = output_size' (Conv A m)" 
      using Conv by (simp add: mat_tensorlist_mult_def)
    then have "j<dim\<^sub>v (tensors_from_net (Conv A m))" using Conv.prems by auto
    then have "(tensors_from_net (Conv A m)) $ j =  tensor_from_lookup (input_sizes m)
                (\<lambda>is. (A \<otimes>\<^sub>m\<^sub>v (map\<^sub>v (\<lambda>T. Tensor.lookup T is) (tensors_from_net m))) $ j)" 
      unfolding tensors_from_net.simps mat_tensorlist_mult_def by fastforce
    then show ?thesis
        using lookup_tensor_from_lookup[OF is_valid] by auto
  qed
  also have "(A \<otimes>\<^sub>m\<^sub>v (map\<^sub>v (\<lambda>T. Tensor.lookup T is) (tensors_from_net m))) $ j 
    = (A \<otimes>\<^sub>m\<^sub>v (evaluate_net m (base_input m is))) $ j" using IH' by auto
  also have "... = evaluate_net (Conv A m) (base_input (Conv A m) is) $ j"
    unfolding base_input_def using evaluate_net.simps by auto
  finally show ?case by auto
next
  case (Pool m1 m2 j "is")

  text \<open>We split "is" into two parts for each subnet:\<close>
  obtain is1 is2 where is12_def:"is = is1 @ is2" "is1 \<lhd> input_sizes m1" "is2 \<lhd> input_sizes m2"
    by (metis Pool.prems(2) input_sizes.simps(3) valid_index_split)  

  text \<open>Apply the induction hypothesis to the subnets:\<close>
  have IH:"Tensor.lookup (tensors_from_net m1 $ j) is1 
      = evaluate_net m1 (map (\<lambda>(x, y). unit\<^sub>v x y) (zip (input_sizes m1) is1)) $ j"
      "Tensor.lookup (tensors_from_net m2 $ j) is2 
      = evaluate_net m2 (map (\<lambda>(x, y). unit\<^sub>v x y) (zip (input_sizes m2) is2)) $ j"
    using Pool convnet.distinct(3) convnet.distinct(5) convnet.inject(3) remove_weights.simps(3) 
    valid_net.simps  `is1 \<lhd> input_sizes m1` `is2 \<lhd> input_sizes m2` output_size.simps(3) 
    by (metis base_input_def)+
  
  text \<open>In the Pool layer tensor entries get multiplied:\<close>
  have lookup_prod: "Tensor.lookup (tensors_from_net (Pool m1 m2) $ j) is
    = Tensor.lookup (tensors_from_net m1 $ j) is1 * Tensor.lookup (tensors_from_net m2 $ j) is2"
  proof -
    have j_small: "j < dim\<^sub>v (tensors_from_net m1)"  "j < dim\<^sub>v (tensors_from_net m2)" 
      by (metis Pool.prems(1) Pool.prems(3) convnet.distinct(3) convnet.inject(3) convnet.simps(9) 
      output_size.simps(3) output_size_correct_tensors remove_weights.simps(3) valid_net.cases)+
    then have 0:"tensors_from_net (Pool m1 m2) $ j = tensors_from_net m1 $ j \<otimes> tensors_from_net m2 $ j"
      unfolding tensors_from_net.simps using j_small index_component_mult by blast
    have "Tensor.dims (tensors_from_net m1 $ j) = input_sizes m1" 
         "Tensor.dims (tensors_from_net m2 $ j) = input_sizes m2" 
      using dims_tensors_from_net j_small nth_mem by (simp_all add: vec_setI)
    then have is12_valid:
              "is1 \<lhd> Tensor.dims (tensors_from_net m1 $ j)" 
              "is2 \<lhd> Tensor.dims (tensors_from_net m2 $ j)" 
      using is12_def by presburger+
    then show ?thesis 
      unfolding 0 using lookup_tensor_prod[OF is12_valid] is12_def by auto
  qed

  text \<open>Output values get multiplied in the Pool layer as well:\<close>
  have "evaluate_net (Pool m1 m2) (base_input (Pool m1 m2) is) $ j
    = evaluate_net m1 (base_input m1 is1) $ j * evaluate_net m2 (base_input m2 is2) $ j"
  proof -   
    have "valid_net' m1" "valid_net' m2" 
      using remove_weights.simps  valid_net.simps Pool.prems 
      by (metis convnet.distinct(3) convnet.distinct(5) convnet.inject(3))+  
    have "input_sizes m1 = map dim\<^sub>v (base_input m1 is1)" 
         "input_sizes m2 = map dim\<^sub>v (base_input m2 is2)" 
      using base_input_def base_input_length base_input_def is12_def by auto  
    have "j < dim\<^sub>v (evaluate_net m1 (base_input m1 is1))" "j < dim\<^sub>v (evaluate_net m2 (base_input m2 is2))"
      using Pool.prems \<open>input_sizes m1 = map dim\<^sub>v (base_input m1 is1)\<close> \<open>valid_net' m1\<close> 
      output_size_correct by (auto,metis Pool.prems(1) Pool.prems(3) \<open>input_sizes m2 = map dim\<^sub>v (base_input m2 is2)\<close>
      convnet.distinct(3) convnet.distinct(5) convnet.inject(3) output_size.simps(3) output_size_correct 
      remove_weights.simps(3) valid_net.cases)  
    then show ?thesis unfolding evaluate_net.simps unfolding base_input_def
      using is12_def(1) is12_def(2) valid_index_length by (simp add: append_eq_conv_conj drop_map 
      drop_zip index_component_mult input_sizes_remove_weights take_map take_zip)
  qed

  then show ?case using lookup_prod IH base_input_def by auto
qed

lemma insert_remove_weights:
obtains w where "m = insert_weights (remove_weights m) w"
using assms proof (induction m arbitrary:thesis)
  case (Input m thesis)
  then show ?case by simp
next
  case (Conv A m thesis)
  then obtain w where "m = insert_weights (remove_weights m) w" by auto
  then have 1:"remove_weights (Conv A m) = Conv (dim\<^sub>r A, dim\<^sub>c A) (remove_weights m)" by simp
  have "Conv A m = insert_weights (remove_weights (Conv A m)) (\<lambda>i. if i<dim\<^sub>r A *dim\<^sub>c A then flatten_matrix A i else w (i-dim\<^sub>r A *dim\<^sub>c A))"
    unfolding 1 insert_weights.simps  
    using extract_matrix_flatten_matrix[of A] extract_matrix_cong[of "dim\<^sub>r A" "dim\<^sub>c A" 
    "\<lambda>i. if i < dim\<^sub>r A * dim\<^sub>c A then flatten_matrix A i else w (i - dim\<^sub>r A * dim\<^sub>c A)" "flatten_matrix A"]
    using \<open>m = insert_weights (remove_weights m) w\<close> by fastforce
  then show ?case using Conv.prems by blast
next
  case (Pool m1 m2)
  then obtain w1 w2 where "m1 = insert_weights (remove_weights m1) w1" "m2 = insert_weights (remove_weights m2) w2" by metis
  then have "Pool m1 m2 = insert_weights (remove_weights (Pool m1 m2)) (\<lambda>i. if i<count_weights (remove_weights m1) then w1 i else w2 (i - count_weights (remove_weights m1)))"
    unfolding remove_weights.simps insert_weights.simps 
    using insert_weights_cong[of _ "\<lambda>i. if i < count_weights (remove_weights m1) then w1 i else w2 (i - count_weights (remove_weights m1))" w1] by fastforce
  then show ?case unfolding Pool using Pool.prems by blast
qed

lemma remove_insert_weights:
shows "remove_weights (insert_weights m w) = m"
using assms proof (induction m arbitrary:w)
  case Input
  then show ?case by simp
next
  case (Conv r12 m)
  then obtain r1 r2 where "r12 = (r1, r2)" by fastforce
  then have "remove_weights (insert_weights m w) = m" using Conv.IH by blast
  then have "remove_weights (insert_weights (Conv (r1,r2) m) w) = Conv (r1,r2) m" 
    unfolding insert_weights.simps remove_weights.simps
    using extract_matrix_def Conv.IH dim_extract_matrix(1) by (metis mat_dim_col_mat(1) )
  then show ?case using \<open>r12 = (r1, r2)\<close> by blast
next
  case (Pool m1 m2 w)
  then show ?case unfolding insert_weights.simps remove_weights.simps using Pool.IH by blast
qed

lemma finite_valid_index: "finite {is. is \<lhd> ds}"  
proof (induction ds)
  case Nil
  then show ?case by (metis List.finite_set finite_subset length_0_conv list.set_intros(1) mem_Collect_eq subsetI valid_index_length)
next
  case (Cons d ds)
  have "{is. is \<lhd> d # ds} \<subseteq> (\<Union>i<d. {i # is |is. is \<lhd> ds})" 
  proof (rule subsetI)
    fix "is" assume "is \<in> {is. is \<lhd> d # ds}"
    then have "is \<lhd> d # ds" by auto
    then obtain i is' where "is = i # is'" by blast
    then have "i<d" using \<open>is \<lhd> d # ds\<close> by blast
    have "is' \<lhd> ds" using \<open>is = i # is'\<close> \<open>is \<lhd> d # ds\<close> by blast
    have "is \<in> {i # is |is. is \<lhd> ds}" by (simp add: \<open>is = i # is'\<close> \<open>is' \<lhd> ds\<close>)
    then show "is \<in> (\<Union>i<d. {i # is |is. is \<lhd> ds})" using \<open>i < d\<close> by blast
  qed
  moreover have "\<And>i. finite {i # is |is. is \<lhd> ds}" by (simp add: Cons.IH)
  ultimately show "finite {is. is \<lhd> d # ds}" by (simp add: finite_subset)
qed

lemma setsum_valid_index_split:
"(\<Sum>is | is \<lhd> ds1 @ ds2. f is) = (\<Sum>is1 | is1 \<lhd> ds1. (\<Sum>is2 | is2 \<lhd> ds2. f (is1 @ is2)))"
proof -
  have 1:"((\<lambda>(is1, is2). is1 @ is2) ` ({is1. is1 \<lhd> ds1} \<times> {is2. is2 \<lhd> ds2})) = {is. is \<lhd> ds1 @ ds2}" (is "?A = ?B")
  proof (rule subset_antisym; rule subsetI)
    fix x assume "x \<in> ?A"
    then show "x \<in> ?B" using valid_index_append by auto
  next
    fix x assume "x \<in> ?B"
    then have "x \<lhd> ds1 @ ds2" by auto
    then obtain x1 x2 where "x = x1 @ x2" "x1 \<lhd> ds1" "x2 \<lhd> ds2" by (metis valid_index_split)
    then have "(x1, x2) \<in> ({is1. is1 \<lhd> ds1} \<times> {is2. is2 \<lhd> ds2})" by auto
    then show "x \<in> ?A" using imageI `x = x1 @ x2` by blast
  qed
  have 2:"inj_on (\<lambda>(is1, is2). is1 @ is2) ({is1. is1 \<lhd> ds1} \<times> {is2. is2 \<lhd> ds2})"
    by (simp add: inj_on_def valid_index_length)
  show ?thesis
    unfolding Groups_Big.comm_monoid_add_class.setsum.cartesian_product[of "\<lambda>is1 is2. f (is1 @ is2)"] 
    using Groups_Big.comm_monoid_add_class.setsum.reindex[OF 2, of f] 1 
     "2" SigmaE prod.simps(2) setsum.reindex_cong by (simp add: split_def)
qed

lemma setprod_lessThan_split:
fixes g :: "nat \<Rightarrow> real" shows "setprod g {..<n+m} = setprod g {..<n} * setprod (\<lambda>x. g (x+n)) {..<m}"
using Groups_Big.comm_monoid_mult_class.setprod.union_inter_neutral[of "{..<n}" "{n..<n+m}" g, unfolded ivl_disj_un_one(2)[OF le_add1], OF finite_lessThan finite_atLeastLessThan]
by (metis (no_types) add.commute add.left_neutral atLeast0LessThan empty_iff ivl_disj_int_one(2) setprod_shift_bounds_nat_ivl)

lemma evaluate_net_from_tensors:
assumes "valid_net' m"
and "map dim\<^sub>v inputs = input_sizes m"
and "j < output_size' m"
shows "evaluate_net m inputs $ j
  = (\<Sum>is\<in>{is. is \<lhd> input_sizes m}. (\<Prod>k<length inputs. inputs ! k $ (is!k)) * Tensor.lookup (tensors_from_net m $ j) is)"
using assms proof (induction m arbitrary:j "is" inputs)
  case (Input M)
  then have "length inputs = 1" "input_sizes (Input M) = [M]" by auto
  { 
    fix "is" assume "is \<lhd> input_sizes (Input M)" 
    then have "length is = 1" by (simp add: valid_index_length)
    then have "is = [hd is]" by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    then have "Tensor.lookup (tensors_from_net (Input M) $ j) is = (if hd is=j then 1 else 0)" 
      by (metis Input.prems(3) \<open>input_sizes (Input M) = [M]\<close> \<open>is \<lhd> input_sizes (Input M)\<close> list.distinct(1) 
      lookup_unit_vec nth_Cons_0 output_size.simps(1) remove_weights.simps(1) tensors_from_net.simps(1) valid_indexE vec_index_vec)
    then have "(\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net (Input M) $ j) is = 
               (if is=[j] then (\<Prod>k<length inputs. inputs ! k $ (is ! k)) else 0)" using \<open>is = [hd is]\<close> by auto
  }
  then have "(\<Sum>is | is \<lhd> input_sizes (Input M). (\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net (Input M) $ j) is)
   = (\<Sum>is | is \<lhd> input_sizes (Input M). (if is=[j] then (\<Prod>k<length inputs. inputs ! k $ (is ! k)) else 0))"  by auto
  also have "(\<Sum>is | is \<lhd> input_sizes (Input M). (if is=[j] then (\<Prod>k<length inputs. inputs ! k $ (is ! k)) else 0))
   = (\<Prod>k<length inputs. inputs ! k $ ([j] ! k))" unfolding setsum.delta[OF finite_valid_index] 
    using Input.prems(3) valid_index.Cons valid_index.Nil by auto
  also have "... = inputs ! 0 $ j" using `length inputs = 1` by (simp add: setprod_lessThan_Suc)
  also have "... = evaluate_net (Input M) inputs $ j" unfolding evaluate_net.simps 
    by (metis \<open>length inputs = 1\<close> hd_conv_nth list.size(3) zero_neq_one)
  finally show ?case by auto
next
  case (Conv A m j)
  have "j < dim\<^sub>r A" using Conv.prems(3) by auto
  have 0:"\<And>is. is \<lhd> input_sizes (Conv A m) \<Longrightarrow>
  (\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net (Conv A m) $ j) is =
  (\<Sum>i = 0..<dim\<^sub>v (tensors_from_net m). row A j $ i * ((\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net m $ i) is))"
  proof -
    fix "is" assume "is \<lhd> input_sizes (Conv A m)"
    then have "is \<lhd> input_sizes m" by simp
    have 0:"lookup (tensors_from_net (Conv A m) $ j) is = 
          (\<Sum>i = 0..<dim\<^sub>v (tensors_from_net m). row A j $ i * lookup (tensors_from_net m $ i) is)"
      unfolding tensors_from_net.simps mat_tensorlist_mult_def vec_index_vec[OF `j < dim\<^sub>r A`] 
      lookup_tensor_from_lookup[OF `is \<lhd> input_sizes m`] index_mat_mult_vec[OF `j < dim\<^sub>r A`] scalar_prod_def
      using vec_index_map by auto
    show "(\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net (Conv A m) $ j) is
      = (\<Sum>i = 0..<dim\<^sub>v (tensors_from_net m). row A j $ i * ((\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net m $ i) is))"
      unfolding 0 setsum_right_distrib by (simp add: semiring_normalization_rules(19))
  qed
  have "valid_net' m" by (metis Conv.prems(1) convnet.distinct(1) convnet.distinct(5) convnet.inject(2) remove_weights.simps(2) valid_net.simps) 
  have "map dim\<^sub>v inputs = input_sizes m" by (simp add: Conv.prems(2))
  have "output_size' m = dim\<^sub>v (tensors_from_net m)" by (simp add: \<open>valid_net' m\<close> output_size_correct_tensors)
  have 1:"\<And>i. i<dim\<^sub>v (tensors_from_net m) \<Longrightarrow> (\<Sum>is | is \<lhd> input_sizes (Conv A m). ((\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net m $ i) is)) = evaluate_net m inputs $ i" unfolding input_sizes.simps 
    using Conv.IH `valid_net' m` `map dim\<^sub>v inputs = input_sizes m` `output_size' m = dim\<^sub>v (tensors_from_net m)` by simp

  have "(\<Sum>is | is \<lhd> input_sizes (Conv A m). (\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net (Conv A m) $ j) is)
    = (\<Sum>i = 0..<dim\<^sub>v (tensors_from_net m). (\<Sum>is | is \<lhd> input_sizes (Conv A m).  row A j $ i *  ((\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net m $ i) is)))"
    using Groups_Big.comm_monoid_add_class.setsum.commute 0 by auto
  also have "... = (\<Sum>i = 0..<dim\<^sub>v (tensors_from_net m). row A j $ i * (\<Sum>is | is \<lhd> input_sizes (Conv A m). ((\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net m $ i) is)))"
    by (simp add: setsum_right_distrib)
  also have "... = (\<Sum>i = 0..<dim\<^sub>v (tensors_from_net m). row A j $ i * evaluate_net m inputs $ i)" using 1 by auto
  also have "... = row A j \<bullet> evaluate_net m inputs" 
    by (metis (full_types) \<open>map dim\<^sub>v inputs = input_sizes m\<close> \<open>output_size' m = dim\<^sub>v (tensors_from_net m)\<close>
    \<open>valid_net' m\<close> output_size_correct scalar_prod_def)
  also have "... = (A \<otimes>\<^sub>m\<^sub>v evaluate_net m inputs) $ j" by (simp add: \<open>j < dim\<^sub>r A\<close>)
  also have "... = evaluate_net (Conv A m) inputs $ j" by simp
  finally show ?case by auto
next
  case (Pool m1 m2 j)  
  have "valid_net' m1" "valid_net' m2" 
    by (metis Pool.prems(1) convnet.distinct(3) convnet.inject(3) convnet.simps(9) remove_weights.simps(3) valid_net.simps)+
  have "j < output_size' m2" "j < output_size' m1"  
    apply (metis Pool.prems(1) Pool.prems(3) convnet.distinct(3) convnet.inject(3) convnet.simps(9)
    output_size.simps(3) remove_weights.simps(3) valid_net.simps) using Pool.prems by auto
  then have "j < dim\<^sub>v (tensors_from_net m1)" "j < dim\<^sub>v (tensors_from_net m2)"
    by (simp_all add: \<open>valid_net' m1\<close> \<open>valid_net' m2\<close> output_size_correct_tensors)

  def inputs1 == "take (length (input_sizes m1)) inputs"
  def inputs2 == "drop (length (input_sizes m1)) inputs"
  have "map dim\<^sub>v inputs1 = input_sizes m1" "map dim\<^sub>v inputs2 = input_sizes m2" 
    apply (metis Pool.prems(2) append_eq_conv_conj input_sizes.simps(3) inputs1_def take_map)
    by (metis Pool.prems(2) append_eq_conv_conj drop_map input_sizes.simps(3) inputs2_def)
  have "inputs = inputs1 @ inputs2" by (simp add: inputs1_def inputs2_def)
  {
    fix is1 is2 assume "is1 \<lhd> input_sizes m1" "is2 \<lhd> input_sizes m2" 
    have "length is1 = length inputs1" 
      using \<open>is1 \<lhd> input_sizes m1\<close> \<open>map dim\<^sub>v inputs1 = input_sizes m1\<close> valid_index_length by fastforce
    have "length is2 = length inputs2" 
      using \<open>is2 \<lhd> input_sizes m2\<close> \<open>map dim\<^sub>v inputs2 = input_sizes m2\<close> valid_index_length by fastforce
    have 1:"(\<Prod>k<length inputs1. (inputs1 @ inputs2) ! k $ ((is1 @ is2) ! k))  = (\<Prod>k<length inputs1. inputs1 ! k $ (is1 ! k))"
      using `length is1 = length inputs1` `length is2 = length inputs2`
      nth_append by (metis (no_types, lifting) lessThan_iff setprod.cong)
    have 2:"(\<Prod>x<length inputs2. (inputs1 @ inputs2) ! (x + length inputs1) $ ((is1 @ is2) ! (x + length inputs1))) =
      (\<Prod>k<length inputs2. inputs2 ! k $ (is2 ! k))"
      using `length is1 = length inputs1` `length is2 = length inputs2`
      by (metis (no_types, lifting) add.commute nth_append_length_plus)
    have "(\<Prod>k<length inputs. inputs ! k $ ((is1 @ is2) ! k)) = (\<Prod>k<length inputs1. inputs1 ! k $ (is1 ! k)) * (\<Prod>k<length inputs2. inputs2 ! k $ (is2 ! k))"
      unfolding `inputs = inputs1 @ inputs2` length_append setprod_lessThan_split using 1 2 by metis
  }
  note 1 = this
  {
    fix is1 is2 assume "is1 \<lhd> input_sizes m1" "is2 \<lhd> input_sizes m2" 
    then have "is1 \<lhd> dims (tensors_from_net m1 $ j)" "is2 \<lhd> dims (tensors_from_net m2 $ j)" 
      using \<open>j < dim\<^sub>v (tensors_from_net m1)\<close>  \<open>j < dim\<^sub>v (tensors_from_net m2)\<close> dims_tensors_from_net vec_setI by force+
    have "lookup (tensors_from_net (Pool m1 m2) $ j) (is1 @ is2) = lookup (tensors_from_net m1 $ j) is1 * lookup (tensors_from_net m2 $ j) is2" 
      unfolding "tensors_from_net.simps" index_component_mult[OF `j < dim\<^sub>v (tensors_from_net m1)` `j < dim\<^sub>v (tensors_from_net m2)`]
      lookup_tensor_prod[OF `is1 \<lhd> dims (tensors_from_net m1 $ j)` `is2 \<lhd> dims (tensors_from_net m2 $ j)`] by metis
  }
  note 2 = this

  have j_le_eval:"j < dim\<^sub>v (evaluate_net m1 (take (length (input_sizes m1)) inputs))" 
                 "j < dim\<^sub>v (evaluate_net m2 (drop (length (input_sizes m1)) inputs))" 
    using \<open>j < output_size' m1\<close> \<open>map dim\<^sub>v inputs1 = input_sizes m1\<close> \<open>valid_net' m1\<close> inputs1_def output_size_correct 
    using \<open>j < output_size' m2\<close> \<open>map dim\<^sub>v inputs2 = input_sizes m2\<close> \<open>valid_net' m2\<close> inputs2_def by auto
  have "(\<Sum>is | is \<lhd> input_sizes (Pool m1 m2). (\<Prod>k<length inputs. inputs ! k $ (is ! k)) * lookup (tensors_from_net (Pool m1 m2) $ j) is)
        = (\<Sum>is1 | is1 \<lhd> input_sizes m1. \<Sum>is2 | is2 \<lhd> input_sizes m2.
          (\<Prod>k<length inputs1. inputs1 ! k $ (is1 ! k)) * (\<Prod>k<length inputs2. inputs2 ! k $ (is2 ! k)) * 
          lookup (tensors_from_net m1 $ j) is1 * lookup (tensors_from_net m2 $ j) is2)"
    unfolding input_sizes.simps setsum_valid_index_split using 1 2 
    using mem_Collect_eq setsum.cong by (simp add: mult.assoc)
  also have "... = (\<Sum>is1 | is1 \<lhd> input_sizes m1. (\<Prod>k<length inputs1. inputs1 ! k $ (is1 ! k)) * lookup (tensors_from_net m1 $ j) is1) *
                   (\<Sum>is2 | is2 \<lhd> input_sizes m2. (\<Prod>k<length inputs2. inputs2 ! k $ (is2 ! k)) * lookup (tensors_from_net m2 $ j) is2)" 
    unfolding setsum_product by (rule setsum.cong, metis, rule setsum.cong, metis, simp)
  also have "... = evaluate_net (Pool m1 m2) inputs $ j" unfolding "evaluate_net.simps" index_component_mult[OF j_le_eval]
    using Pool.IH(1)[OF `valid_net' m1` _ `j < output_size' m1`] Pool.IH(2)[OF `valid_net' m2` _ `j < output_size' m2`]
    using \<open>map dim\<^sub>v inputs1 = input_sizes m1\<close> \<open>map dim\<^sub>v inputs2 = input_sizes m2\<close> inputs1_def inputs2_def by auto
  finally show ?case by metis
qed  

lemma tensors_from_net_eqI:
assumes "valid_net' m1" "valid_net' m2" "input_sizes m1 = input_sizes m2"
assumes "\<And>inputs. input_sizes m1 = map dim\<^sub>v inputs \<Longrightarrow> evaluate_net m1 inputs = evaluate_net m2 inputs"
shows "tensors_from_net m1 = tensors_from_net m2"
proof -
  have "map dim\<^sub>v (map \<zero>\<^sub>v (input_sizes m2)) = input_sizes m2"
       "map dim\<^sub>v (map \<zero>\<^sub>v (input_sizes m1)) = input_sizes m1" by (simp_all add: nth_equalityI)
  then have "output_size' m1 = output_size' m2" using 
    output_size_correct[OF `valid_net' m1` `map dim\<^sub>v (map \<zero>\<^sub>v (input_sizes m1)) = input_sizes m1`]
    output_size_correct[OF `valid_net' m2` `map dim\<^sub>v (map \<zero>\<^sub>v (input_sizes m2)) = input_sizes m2`] 
    assms(3) assms(4) 
    by (metis (no_types))
  have "\<And>is. base_input m1 is = base_input m2 is" 
    unfolding base_input_def `input_sizes m1 = input_sizes m2` by metis
  show ?thesis by (rule vec_eqI, rule tensor_lookup_eqI; metis
    lookup_tensors_from_net[OF `valid_net' m1`, unfolded `\<And>is. base_input m1 is = base_input m2 is` \<open>output_size' m1 = output_size' m2\<close>]
    lookup_tensors_from_net[OF `valid_net' m2`] assms(3) base_input_length
    assms(1) assms(2) dims_tensors_from_net output_size_correct_tensors vec_setI
    \<open>output_size' m1 = output_size' m2\<close> assms(4))
qed

end
