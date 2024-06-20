section \<open> Coppersmith Generic \<close>

text \<open> In this file, we develop the generic argument behind Coppersmith's method. \<close>

theory Coppersmith_Generic

imports Coppersmith_Algorithm
  Howgrave_Graham
  More_LLL
begin

hide_const (open) module.smult

subsection \<open> Some matrix properties \<close>

text \<open> This definition should only be used for lists of vectors that correspond to square matrices \<close>
definition vec_list_to_square_mat:: "'a vec list \<Rightarrow> 'a mat"
  where "vec_list_to_square_mat L = mat_of_rows (length L) L"

text \<open> This lemma is similar to upper\_triangular\_imp\_distinct, from 
  the "Jordan\_Normal\_Form.Matrix" library by Thiemann and Yamada. \<close>
lemma lower_triangular_imp_distinct:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "\<And>i j. i < j \<Longrightarrow> j < n \<Longrightarrow> A $$ (i,j) = 0"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "distinct (rows A)"
proof-
  {fix i and j
    assume eq: "rows A ! i = rows A ! j" and ij: "i < j" and jn: "j < n"
    from tri A ij jn have "rows A ! i $ j = 0"  
      by simp
    with eq have "rows A ! j $ j = 0" by auto
    with diag ij jn A have False by (auto simp: diag_mat_def)
  }
  with A show ?thesis by (force simp: distinct_conv_nth nat_neq_iff)
qed 

lemma lower_triangular_imp_det_eq_0_iff:
  fixes A :: "'a :: idom mat"
  assumes "A \<in> carrier_mat n n" and "\<And>i j. i < j \<Longrightarrow> j < n \<Longrightarrow> A $$ (i,j) = 0"
  shows "det A = 0 \<longleftrightarrow> 0 \<in> set (diag_mat A)"
  using assms det_lower_triangular 
  by (metis semidom_class.prod_list_zero_iff)

text \<open> This next lemma is similar to upper\_triangular\_imp\_lin\_indpt\_rows, from 
  the "Jordan\_Normal\_Form.VS\_Connect" library by Thiemann and Yamada. \<close>
lemma (in idom_vec) lower_triangular_imp_lin_indpt_rows:
  assumes A: "A \<in> carrier_mat n n"
    and lower_tri: "\<And>i j. i < j \<Longrightarrow> j < n \<Longrightarrow> A $$ (i,j) = 0"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "lin_indpt (set (rows A))"
  using det_not_0_imp_lin_indpt_rows lower_triangular_imp_det_eq_0_iff assms
  by auto

lemma g_i_vec_ith_element:
  assumes "degree p \<ge> 1"
  assumes "i < degree p"
  assumes "M > 0"
  assumes "X > 0"
  shows "(g_i_vec M X i (degree p + 1)) $ i = M*X^i"
  unfolding g_i_vec_def
  using assms(2) assms(3) assms(4) by auto

lemma ith_row_form_basis_helper:
  assumes "i \<le> d"
  shows "((form_basis_helper p M X d)!i) = g_i_vec M X i (degree p + 1)"
  using assms unfolding form_basis_helper_def 
  by (metis add_cancel_right_left add_cancel_right_right le_imp_less_Suc less_diff_conv nth_map_upt semiring_norm(174))

lemma no_zeros_on_diagonal_helper:
  assumes "degree p \<ge> 1"
  assumes "i < degree p"
  assumes "M > 0"
  assumes "X > 0"
  shows "((form_basis_helper p M X (degree p - 1))!i)$i = M*X^i"
  using ith_row_form_basis_helper assms g_i_vec_ith_element 
  by (metis Suc_eq_plus1 less_diff_conv2 not_less_eq verit_comp_simplify(3))

subsection \<open> Casting lemmas \<close>

lemma casted_distinct_is_distinct:
  fixes vecs:: "int vec list"
  assumes distinct_vecs: "distinct vecs"
  shows "distinct ((map of_int_vec vecs)::rat vec list)"
proof - 
  let ?map_list = "(map of_int_vec vecs)::rat vec list"
  have same_map: "?map_list = map (map_vec rat_of_int) vecs"
    by simp
  have eq_iff: "\<And>a b::int vec. a = b \<longleftrightarrow> map_vec rat_of_int a = map_vec rat_of_int b"
    using of_int_hom.vec_hom_inj by blast
  then have "inj (map_vec rat_of_int)" unfolding inj_def 
    by simp 
  then show ?thesis using distinct_map[of "map_vec rat_of_int" vecs] distinct_vecs
    same_map inj_on_def local.eq_iff 
    by blast
qed

text \<open> Copy pasted from VS\_Connect, which only has it for field coefficients \<close>
lemma (in vec_module) finsum_dim:
  shows "f \<in> A \<rightarrow> carrier_vec n \<Longrightarrow>
    dim_vec (finsum V f A) = n"
  by (smt (verit) M.add.finprod_closed carrier_vecD)

lemma (in vec_module) finsum_index:
  assumes i: "i < n"
    and f: "f \<in> X \<rightarrow> carrier_vec n"
    and X: "X \<subseteq> carrier_vec n"
  shows "finsum V f X $ i = sum (\<lambda>x. f x $ i) X"
  using X f
proof (induct X rule: infinite_finite_induct)
  case empty
    then show ?case using i by simp next
  case (insert x X)
    then have Xf: "finite X"
      and xX: "x \<notin> X"
      and x: "x \<in> carrier_vec n"
      and X: "X \<subseteq> carrier_vec n"
      and fx: "f x \<in> carrier_vec n"
      and f: "f \<in> X \<rightarrow> carrier_vec n" by auto
    have i2: "i < dim_vec (finsum V f X)"
      using i finsum_closed[OF f] by auto
    have ix: "i < dim_vec x" using x i by auto
    show ?case
      unfolding finsum_insert[OF Xf xX f fx]
      unfolding sum.insert[OF Xf xX]
      unfolding index_add_vec(1)[OF i2]
      using insert lincomb_def
      by auto
  qed (insert i, auto)

lemma is_int_rat_mul_of_int:
  assumes "snd (quotient_of y) dvd x"
  shows "is_int_rat (of_int x * y)"
proof -
  have y: "y * of_int (snd (quotient_of y)) = of_int (fst (quotient_of y))"
    by (smt (verit) nonzero_eq_divide_eq of_int_eq_0_iff prod.collapse quotient_of_div quotient_of_nonzero(2))
  obtain k where "x = k * snd (quotient_of y)"
    by (smt (verit) assms dvd_div_mult_self)
  thus ?thesis
    by (smt (verit) Groups.mult_ac(2) Groups.mult_ac(3) Ints_of_int y is_int_rat of_int_mult)
qed

lemma casting_lin_comb_helper_set:
  assumes vs: "vs \<subseteq> carrier_vec n"
  assumes ldi: "module.lin_dep class_ring (module_vec TYPE(rat) n)
     (of_int_vec ` vs)"
  shows "module.lin_dep class_ring (module_vec TYPE(int) n) vs"
proof -                
  interpret vmint: vec_module "TYPE(int)" "n" .
  interpret vmrat: vec_module "TYPE(rat)" "n" .

  have mrat:"module class_ring vmrat.V"
    using vec_module by blast
  have mint:"module class_ring vmint.V"
    using vmint.module_axioms by auto

  from ldi
  obtain A a va where av: "finite A" "A \<subseteq> of_int_vec ` vs"
    "a \<in> A \<rightarrow> carrier class_ring"
    "vmrat.lincomb a A = \<zero>\<^bsub>vmrat.V\<^esub>"
    "va \<in> A" "a va \<noteq> \<zero>\<^bsub>class_ring\<^esub>"
    unfolding module.lin_dep_def[OF mrat]
    by blast

  obtain B vb where B: "finite B" "B \<subseteq> vs" "A = of_int_vec ` B"
    "vb \<in> B" and va: "va = of_int_vec vb"
    by (metis (no_types, opaque_lifting) av(1) av(2) av(5) finite_subset_image image_iff)
    
  have Bcarr: "B \<subseteq> carrier_vec n"
    using B(2) vs
    by auto
  then have Acarr: "A \<subseteq> carrier_vec n"
    unfolding B
    by auto
  have 0: "finite B"
    using B(1) assms(1) infinite_super by blast

  text \<open> maximum denominator in any coefficient \<close>
  define md where "(md::rat) = of_int (Prod ((\<lambda>r. snd (quotient_of r)) ` (image a A)))"

  have mdpos: "md > 0" unfolding md_def
    by (metis (no_types, lifting) imageE of_int_pos prod_pos quotient_of_denom_pos') 

  have inj_of_int_vec:"inj_on (of_int_vec:: int vec \<Rightarrow> rat vec) B"
    unfolding inj_on_def vec_eq_iff
    by (auto simp add: )

  have *:"(\<lambda>v. md * a v \<cdot>\<^sub>v v) \<in> of_int_vec ` B \<rightarrow> carrier_vec n"
    using Acarr B(3) by blast

  have "v \<in> A \<Longrightarrow> is_int_rat (md * a v)" for v
    unfolding md_def
    apply (intro is_int_rat_mul_of_int)
    by (metis av(1) dvd_prodI finite_imageI imageI)

  define b where "b = (\<lambda>v::int vec. int_of_rat (md * a (of_int_vec v)))"

  have bvb: "b vb = int_of_rat (md * a va)"
    unfolding b_def va[symmetric] by auto

  have "a va \<noteq> 0" using av(6)
    by auto
  then have "fst (quotient_of (a va)) \<noteq> 0"
    by (metis Is_Rat_To_Rat.int_of_rat_0 Is_Rat_To_Rat.int_of_rat_def)
  then have 1: "b vb \<noteq> 0"
    using bvb mdpos
    by (simp add: \<open>a va \<noteq> 0\<close>)

  have [simp]: "dim_vec (\<Oplus>\<^bsub>vmint.V\<^esub>v\<in>B. b v \<cdot>\<^sub>v v) = n"
     apply (subst vmint.finsum_dim)
    using Bcarr by auto
  have [simp]: "dim_vec (finsum vmrat.V (of_int_vec \<circ> (\<lambda>v. b v \<cdot>\<^sub>v v)) B) = n"
     apply (subst vmrat.finsum_dim)
    using Bcarr by auto

  have all_B_in_carrier_n: "\<And>x. x \<in> B \<Longrightarrow> x \<in> carrier_vec n "
    by (metis B(2) basic_trans_rules(23) smult_carrier_vec vmint.summands_valid vs)
  then have B_prop2:  "\<And>i. i \<in> B \<Longrightarrow>
         rat_of_int (int_of_rat (md * a (of_int_vec i))) \<cdot>\<^sub>v
         of_int_vec i =
         md * a (of_int_vec i) \<cdot>\<^sub>v of_int_vec i "
    using B(3) \<open>\<And>v. v \<in> A \<Longrightarrow> is_int_rat (md * a v)\<close> by force

  have " \<And>i. i < n \<Longrightarrow>
         B \<subseteq> carrier_vec n \<Longrightarrow>
         (\<Sum>x\<in>B. rat_of_int ((b x \<cdot>\<^sub>v x) $ i)) = (\<Sum>x\<in>B. of_int_vec (b x \<cdot>\<^sub>v x) $ i)"
    by (auto intro!: sum.cong)
  then have "\<And>i. i < n \<Longrightarrow>
         rat_of_int ((\<Oplus>\<^bsub>vmint.V\<^esub>v\<in>B. b v \<cdot>\<^sub>v v) $ i) =
         (\<Sum>x\<in>B. (of_int_vec \<circ> (\<lambda>v. b v \<cdot>\<^sub>v v)) x $ i)"
    apply (subst vmint.finsum_index)
    using Bcarr by auto[4]
  then have finsum_prop: "\<And>i. i < n \<Longrightarrow>
         rat_of_int ((\<Oplus>\<^bsub>vmint.V\<^esub>v\<in>B. b v \<cdot>\<^sub>v v) $ i) =
         finsum vmrat.V (of_int_vec \<circ> (\<lambda>v. b v \<cdot>\<^sub>v v)) B $ i"   
    apply (subst vmrat.finsum_index) using Bcarr by auto
  have "of_int_vec (vmint.lincomb b B) =
    of_int_vec (finsum vmint.V (\<lambda>v. b v \<cdot>\<^sub>v v) B)"
    unfolding vmint.lincomb_def by auto
  also have "... = finsum vmrat.V (of_int_vec \<circ> (\<lambda>v. b v \<cdot>\<^sub>v v)) B"
    using finsum_prop vec_eq_iff by auto
    
  also have "... =
    finsum vmrat.V
      (\<lambda>v. (md * a (of_int_vec v)) \<cdot>\<^sub>v of_int_vec v) B"
    unfolding b_def o_def of_int_hom.vec_hom_smult
    using all_B_in_carrier_n B_prop2
    by (auto intro!: vmrat.M.finsum_cong2)
  also have "... =
    finsum vmrat.V (\<lambda>v. (md * a v) \<cdot>\<^sub>v v) A"
    unfolding B(3)
    apply (subst vmrat.finsum_reindex[OF * inj_of_int_vec])
    by (auto simp add: smult_smult_assoc)
  also have "... = 
    vmrat.lincomb (\<lambda>v. md * (a v)) A"
    by (metis vmrat.lincomb_def)
  also have "... = md \<cdot>\<^sub>v vmrat.lincomb a A"
    using Acarr
    by (metis vmrat.lincomb_smult)
  also have "... = \<zero>\<^bsub>vmrat.V\<^esub>"
    by (smt (verit) av(4) module_vec_simps(2) vmrat.smult_r_null)
  finally have "of_int_vec (vmint.lincomb b B) = \<zero>\<^bsub>vmrat.V\<^esub>" .
  then have 2: "vmint.lincomb b B = 0\<^sub>v n"
    by (smt (verit) module_vec_simps(2) of_int_hom.vec_hom_zero_iff)

  show ?thesis
    unfolding vmint.lin_dep_def
    using B 0 1 2
    by blast
qed

lemma casting_lin_comb_helper:
  assumes dim_vecs: "\<And>v. v \<in> set vecs \<Longrightarrow> dim_vec v = len_vec"
  assumes "module.lin_indpt class_ring (module_vec TYPE(int) (len_vec)) (set vecs)"
  shows "\<not> (module.lin_dep class_ring (module_vec TYPE(rat) (len_vec))
     (set ((map of_int_vec vecs)::rat vec list)))"
  using assms(2)
  apply (rule contrapos_nn)
  using dim_vecs apply (auto intro!: casting_lin_comb_helper_set)[1]
  by (smt (verit) carrier_vec_dim_vec)

lemma casting_lin_comb_helper_set_2:
  assumes vs: "vs \<subseteq> carrier_vec n"
  assumes ldi: "module.lin_dep class_ring (module_vec TYPE(int) n) vs"
  shows "module.lin_dep class_ring (module_vec TYPE(rat) n)
     (of_int_vec ` vs)"
proof -
  interpret vmint: vec_module "TYPE(int)" "n" .
  interpret vmrat: vec_module "TYPE(rat)" "n" .

  have mrat:"module class_ring vmrat.V"
    using vec_module by blast
  have mint:"module class_ring vmint.V"
    using vmint.module_axioms by auto

  from ldi
  obtain A a va where av: "finite A" "A \<subseteq> vs"
    "a \<in> A \<rightarrow> carrier class_ring"
    "vmint.lincomb a A = \<zero>\<^bsub>vmint.V\<^esub>"
    "va \<in> A" "a va \<noteq> \<zero>\<^bsub>class_ring\<^esub>"
    unfolding module.lin_dep_def[OF mint]
    by blast

  define B where "(B :: rat vec set) = of_int_vec ` A"
  define b where "(b::rat vec \<Rightarrow> rat) = (\<lambda>v::rat vec. of_int (a (map_vec floor v)))"
  define vb where "(vb::rat vec) = of_int_vec va"

  have [simp]: "dim_vec (\<Oplus>\<^bsub>vmint.V\<^esub>v\<in>A. a v \<cdot>\<^sub>v v) = n"
     apply (subst vmint.finsum_dim)
    using av 
    using assms(1) by auto
  have [simp]: "dim_vec
     (\<Oplus>\<^bsub>vmrat.V\<^esub>v\<in>of_int_vec `
                    A. rat_of_int
                        (a (map_vec floor v)) \<cdot>\<^sub>v v) = n"
    apply (subst vmrat.finsum_dim)
    using av(2) vs by auto

  have B1: "finite B"
    by (simp add: B_def av(1))
  have B2: "B \<subseteq> of_int_vec ` vs"
    unfolding B_def
    using av by blast
  have B3_aux_helper: "\<And>i. i < n \<Longrightarrow> A \<subseteq> carrier_vec n  \<Longrightarrow> (\<And>i x. i < n \<Longrightarrow>
           x \<in> A \<Longrightarrow>
           (rat_of_int (a (map_vec floor (of_int_vec x))) \<cdot>\<^sub>v of_int_vec x) $ i =
           rat_of_int ((a x \<cdot>\<^sub>v x) $ i))"
    by (smt (verit, del_insts) carrier_vecD eq_vecI floor_of_int index_map_vec(1) index_map_vec(2) index_smult_vec(1) of_int_mult smult_carrier_vec vmint.summands_valid)
  have B3_aux: "\<And>i. i < n \<Longrightarrow>
         (\<Oplus>\<^bsub>vmrat.V\<^esub>v\<in>of_int_vec ` A. rat_of_int (a (map_vec floor v)) \<cdot>\<^sub>v v) $ i =
         rat_of_int ((\<Oplus>\<^bsub>vmint.V\<^esub>v\<in>A. a v \<cdot>\<^sub>v v) $ i)"
    apply (subst vmrat.finsum_index)
    apply (metis)
    subgoal
      using assms(1) av(2) by force
     apply (smt (verit, ccfv_threshold) B2 B_def basic_trans_rules(31) image_iff map_carrier_vec subsetI vs)
     apply (subst vmint.finsum_index)
    subgoal by auto
    subgoal
      using av(2) vs by auto
    subgoal
      using assms(1) av(2) by auto
    apply (subst sum.reindex)
    subgoal
      by (simp add: inj_on_def of_int_hom.vec_hom_inj)
    using B3_aux_helper 
    by (smt (verit, del_insts) \<open>\<And>i. i < n \<Longrightarrow> A \<subseteq> carrier_vec n\<close> o_apply of_int_sum sum.cong) have B3: "vmrat.lincomb b B = of_int_vec (vmint.lincomb a A)"
    unfolding b_def B_def
    vmrat.lincomb_def vmint.lincomb_def
    apply (subst vec_eq_iff)
    using B3_aux by auto
   
  have B4: "vb \<in> B"
    unfolding vb_def B_def
    by (simp add: av(5))
    
  have B5: "b vb \<noteq> 0"
    unfolding vb_def b_def
    using av(6)
    apply clarsimp
    by (metis eq_vecI floor_of_int index_map_vec(1) index_map_vec(2))
    
  show ?thesis
    unfolding vmrat.lin_dep_def
    using B1 B2 B3 B4 B5
    by (metis av(4) module_vec_simps(2) of_int_hom.vec_hom_zero)
qed

lemma casting_lin_comb_helper_2:
  assumes dim_vecs: "\<And>v. v \<in> set vecs \<Longrightarrow> dim_vec v = len_vec"
  assumes "\<not> (module.lin_dep class_ring (module_vec TYPE(rat) (len_vec))
     (set ((map of_int_vec vecs)::rat vec list)))"
  shows "module.lin_indpt class_ring (module_vec TYPE(int) (len_vec)) (set vecs)"
  using assms(2)
  apply (rule contrapos_nn)
  using dim_vecs apply (auto intro!: casting_lin_comb_helper_set_2)[1]
  by (smt (verit) carrier_vec_dim_vec)

subsection \<open> Properties of associated polynomial \<close>

lemma f_representation:
  shows "f = (\<Sum>i<degree f. monom (poly.coeff f i) i) +
    monom (lead_coeff f) (degree f)"
  by (metis (full_types) lessThan_Suc_atMost poly_as_sum_of_monoms sum.lessThan_Suc)

lemma vec_associated_to_int_poly_inverse:
  assumes "X > 0"
  fixes f:: "int poly"
  shows "f = int_poly_associated_to_vec (vec_associated_to_int_poly f X) X"
  using assms f_representation
  unfolding int_poly_associated_to_vec_def vec_associated_to_poly_def
  by auto             

lemma int_poly_associated_to_vec_degree_helper_le:
  shows "degree (\<Sum>i\<le>n. monom (f i) i) \<le> n"
  apply (intro degree_sum_le)
  apply clarsimp
  using degree_monom_le
  using ge_trans by blast

lemma int_poly_associated_to_vec_degree_helper_lt:
  assumes "n > 0"
  shows "degree (\<Sum>i<n. monom (f i) i) < n"
  apply (cases n)
  using assms
  by (auto simp add: lessThan_Suc_atMost less_Suc_eq_le int_poly_associated_to_vec_degree_helper_le)

lemma int_poly_associated_to_vec_degree:
  fixes v:: "int vec"
  assumes "dim_vec v > 0"
  shows "degree (int_poly_associated_to_vec v X) < dim_vec v"
  unfolding int_poly_associated_to_vec_def
  using assms by (auto intro!: int_poly_associated_to_vec_degree_helper_lt)

lemma degree_associated_poly:
  shows "degree (int_poly_associated_to_vec v X) \<le> dim_vec v"
  unfolding int_poly_associated_to_vec_def
  apply(cases "dim_vec v = 0")
  subgoal by auto
  by (metis bot_nat_0.not_eq_extremum less_imp_le_nat int_poly_associated_to_vec_def int_poly_associated_to_vec_degree)

lemma degree_associated_poly_lt:
  assumes "X > 0"
  assumes "dim_vec v \<ge> 1"
  shows "degree (int_poly_associated_to_vec v X) < dim_vec v"
  using assms 
  by (simp add: int_poly_associated_to_vec_degree)

lemma degree_of_monom_sum_list:
  fixes ell:: "int list"
  fixes j:: "nat"
  assumes "ell \<noteq> []"
  shows "degree
          (\<Sum>i<length ell. monom
               (ell ! i) i) < length ell"
  using assms 
proof (induct "length ell" arbitrary: ell)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then obtain ell1 a where ell_prop: "ell = ell1@[a]"
    by (metis length_Suc_conv_rev)
  then have len_ell1: "x = length ell1"
    using Suc.hyps(2) by auto 
  have "\<And>i. i < length ell1 \<Longrightarrow> (ell1 @ [a]) ! i = ell1 ! i"
    by (simp add: append_Cons_nth_left)
  then have "(\<Sum>i<length ell1. monom ((ell1 @ [a]) ! i) i) =
    (\<Sum>i<length ell1. monom (ell1 ! i) i)"
    by auto
  then have sum_is: "(\<Sum>i<length ell. monom (ell ! i) i) = 
    (\<Sum>i<length ell1. monom (ell1 ! i) i) + monom a (length ell - 1)"
    using ell_prop by auto 
  {assume *: "ell1 = []"
    then have "length ell = 1"
      using ell_prop by auto 
    then have " degree (\<Sum>i<length ell. monom (ell ! i) i)
       < length ell" using * sum_is 
      by auto
  } moreover {assume *: "ell1 \<noteq> []"
    have "degree (\<Sum>i<length ell1. monom (ell1 ! i) i) < length ell1"
      using Suc len_ell1 
      using "*" by blast
    then have lt1: "degree (\<Sum>i<length ell1. monom (ell1 ! i) i) < length ell"
      using ell_prop by auto
    have lt2: "degree (monom a (length ell - 1)) <  length ell"

      by (metis Suc(2) degree_0 degree_monom_eq diff_Suc_1 lessI less_Suc_eq_0_disj monom_eq_0_iff)
    then have " degree (\<Sum>i<length ell. monom (ell ! i) i)
       < length ell"
      using sum_is lt1 
      by (simp add: degree_add_less)
  }
  ultimately show ?case
    by blast
qed

lemma coeff_of_monom_sum_list:
  fixes ell:: "int list"
  fixes j:: "nat"
  assumes "j < length ell"
  shows "coeff
          (\<Sum>i<length ell. monom
               (ell ! i) i) j = ell ! j"
  using assms
proof (induct "length ell" arbitrary: ell)
  case 0
  then show ?case by auto
next
  case (Suc x)
  {assume *: "x = 0"
    obtain a where "ell = [a]"
      using Suc *
      by (metis length_0_conv length_Suc_conv)
    have "j = 0"
      using Suc * by auto
    then have "poly.coeff (\<Sum>i<1. monom (ell ! i) i) j =
       ell ! j"
      by auto
  } moreover {assume *: "x > 0"
    then have "length ell > 1"
      using Suc
      by auto
    then obtain ell1 a where "ell = ell1@[a]"
      by (metis Suc.hyps(2) length_nth_simps(1) nat.simps(3) rev_cases)
    then have "poly.coeff (\<Sum>i<length ell. monom (ell ! i) i) j =
       ell ! j"
      using Suc degree_of_monom_sum_list 
      by (simp add: coeff_sum_monom lessThan_Suc_atMost not_less_eq)
  }
  ultimately show ?case
    using Suc.hyps(2)
    by (metis One_nat_def bot_nat_0.not_eq_extremum)
qed

lemma coeff_of_monom_sum:
  fixes a:: "int vec"
  assumes "i < dim_vec a"
  shows "coeff
          (\<Sum>i<dim_vec a. monom
               (a $ i) i) i = a $ i"
  using coeff_of_monom_sum_list   
  by (metis (no_types, lifting)  Matrix.length_list_of_vec assms list_of_vec_index sum.cong)

text \<open>  This next lemma required showing that every vector in the lattice
  has its ith component divisible by $X^n$ (a property of the basis).\<close>
lemma access_entry_in_int_poly_associated_to_vec: 
  fixes x i:: "nat"
  fixes v:: "int vec"
  assumes "i < dim_vec v"
  shows "(coeff (int_poly_associated_to_vec v X) i) = \<lfloor>real_of_int (v $ i) / real (X ^ i)\<rfloor>"
proof - 
  let ?newvec = "vec (dim_vec v) (\<lambda>j. \<lfloor>real_of_int (v $ j) / real (X ^ j)\<rfloor>)"
  have "\<And>i k. k \<noteq> 0 \<Longrightarrow> degree (monom k i) = i"
    by (simp add: degree_monom_eq)
  then have helper: "\<And>(j::nat). \<And> (v::int vec). j < dim_vec v \<Longrightarrow> poly.coeff (\<Sum>i<dim_vec v. monom (v $ i) i) j = (v $ j)"
    by (smt (z3) coeff_of_monom_sum dim_vec not_less_zero)
  have "poly.coeff (\<Sum>i<dim_vec v. monom (?newvec $ i) i) i =
    \<lfloor>real_of_int (v $ i) / real (X ^ i)\<rfloor>"
    using helper[of i ?newvec] assms dim_vec index_vec sum.cong
    unfolding int_poly_associated_to_vec_def 
    by force
  then show ?thesis unfolding int_poly_associated_to_vec_def by auto
qed

lemma dim_vec_associated_to_int_poly_lteq:
  fixes v:: "int vec"
  assumes "dim_vec v \<ge> 1"
  assumes "X > 0"
  shows "dim_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X) \<le> dim_vec v"
proof - 
  have "\<And>i k. k \<noteq> 0 \<Longrightarrow> degree (monom k i) = i"
    by (simp add: degree_monom_eq)
  then have helper: "\<And>(j::nat). \<And> (v::int vec). j < dim_vec v \<Longrightarrow> poly.coeff (\<Sum>i<dim_vec v. monom (v $ i) i) j = (v $ j)"
    by (smt (z3) coeff_of_monom_sum dim_vec not_less_zero)
  then have "degree (int_poly_associated_to_vec v X) < dim_vec v"
    unfolding int_poly_associated_to_vec_def using assms degree_associated_poly_lt
    by (metis (no_types) assms int_poly_associated_to_vec_def)
  then show ?thesis 
    unfolding vec_associated_to_poly_def 
    by simp
qed

lemma dim_vec_associated_to_int_poly_lt_imp_zeros:
  fixes v:: "int vec"
  fixes i:: "nat"
  assumes entries_div: "\<And>j. j < dim_vec v \<Longrightarrow> (\<exists>k. (X^j)*k = (v $ j))"
  assumes X_gt: "X > 0"
  assumes "dim_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X) < dim_vec v"
  assumes i_gt: "i \<ge> dim_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X)"
  assumes i_lt: "i < dim_vec v"
  shows "v $ i = 0"
proof - 
  let ?associated_p = "(int_poly_associated_to_vec v X)"
  let ?associated_v = "vec_associated_to_int_poly (int_poly_associated_to_vec v X) X"
  have "\<And>i k. k \<noteq> 0 \<Longrightarrow> degree (monom k i) = i"
    by (simp add: degree_monom_eq)
  then have helper1: "\<And>(j::nat). \<And> (v::int vec). j < dim_vec v \<Longrightarrow> poly.coeff (\<Sum>i<dim_vec v. monom (v $ i) i) j = (v $ j)"
    by (smt (z3) coeff_of_monom_sum dim_vec not_less_zero)
  have helper2:  "poly.coeff ?associated_p i = 0"
    using i_gt
    by (simp add: coeff_eq_0)
  have coeff_is: "poly.coeff ?associated_p i = floor (((v $ i)::real)/(X^i))"
    unfolding int_poly_associated_to_vec_def using i_lt helper1
    using access_entry_in_int_poly_associated_to_vec int_poly_associated_to_vec_def by force
  then have "v$i \<noteq> 0 \<Longrightarrow> floor (((v $ i)::real)/(X^i)) \<noteq> 0"
    using entries_div i_lt X_gt 
    by (smt (verit) divide_cancel_right divide_divide_eq_left divide_eq_0_iff mult_divide_mult_cancel_left of_int_eq_0_iff of_int_floor_cancel of_int_mult of_int_of_nat_eq of_nat_0_eq_iff of_nat_eq_of_nat_power_cancel_iff)
  then show ?thesis using coeff_is helper2 by metis
qed

lemma int_poly_associated_to_notNil_vec_same_norm_upto:
  assumes "dim_vec v \<ge> 1"
  assumes X_gt: "X > 0"
  assumes entries_div: "\<And>j. j < dim_vec v \<Longrightarrow> (\<exists>k. (X^j)*k = (v $ j))"
  assumes "w = (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X)"
  shows "(\<Sum>i<(dim_vec v). (v$i)^2) = (\<Sum>i<(dim_vec w). (v$i)^2)"
proof - 
  {assume *: "dim_vec w = dim_vec v"
    then have "(\<Sum>i<(dim_vec v). (v$i)^2) = (\<Sum>i<(dim_vec w). (v$i)^2)"
      by auto
  } moreover {assume *:"dim_vec w < dim_vec v"
    then have dim_v_at_least_1: "dim_vec v \<ge> 1"
      by auto
    have "\<And>i. dim_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X) \<le> i \<Longrightarrow>
    i < dim_vec v \<Longrightarrow> v $ i = 0"
      using * dim_vec_associated_to_int_poly_lt_imp_zeros[OF entries_div X_gt] assms
      by blast
    then have i_zero_prop: "\<And>i. i \<in> {dim_vec w..<(dim_vec v)} \<Longrightarrow> (v$i)^2 = 0"
      by (metis assms(4) atLeastLessThan_iff zero_power2)
    then have "(\<Sum>i<(dim_vec v). (v$i)^2) = (\<Sum>i<(dim_vec w). (v$i)^2)"
    proof - 
      have finset1: "finite {x. x < dim_vec w}"
        by auto
      have finset2: "finite ({x. (dim_vec w) \<le> x} \<inter> {x. x < dim_vec v})"
        by blast
      have empty_inter: "{x. x < dim_vec w} \<inter> ({x. (dim_vec w) \<le> x} \<inter> {x. x < dim_vec v}) = {}"
        by auto
      have "{x. x < dim_vec v} = {x. x < dim_vec w} \<union> ({x. (dim_vec w) \<le> x} \<inter> {x. x < dim_vec v})"
        using *
        by auto
      then have "(\<Sum>i<(dim_vec v). (v$i)^2) = (\<Sum>i<(dim_vec w). (v$i)^2) + (\<Sum>i \<in> {dim_vec w..<(dim_vec v)}. (v$i)^2) "
        using * empty_inter unfolding atLeastLessThan_def atLeast_def lessThan_def 
        using sum_Un_nat[OF finset1 finset2]  
        by (metis (no_types, lifting) finset1 finset2 sum.union_disjoint)
      then show ?thesis
      using assms i_zero_prop 
      by auto
  qed
  }
  ultimately show ?thesis 
    using dim_vec_associated_to_int_poly_lteq assms
    by (metis One_nat_def le_neq_implies_less)
  qed

lemma int_poly_associated_to_notNil_vec_same_entries:
  fixes i:: "nat"
  fixes v w:: "int vec"
  assumes i_lt: "i < dim_vec w"
  assumes "dim_vec v \<ge> 1"
  assumes X_gt: "X > 0"
  assumes entries_div: "\<And>j. j < dim_vec v \<Longrightarrow> (\<exists>k. (X^j)*k = (v $ j))"
  assumes w_is: "w = (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X)"
  shows "((v $ i) = (w $ i))"
proof - 
  let ?p = "int_poly_associated_to_vec v X"
  have "w$i = (coeff ?p i)*X^i"
    using i_lt w_is unfolding int_poly_associated_to_vec_def 
    using index_vec vec_associated_to_poly_def
    by (smt (verit, del_insts) dim_vec_vec_associated_to_poly semiring_1_class.of_nat_power)
  then show ?thesis
    using assms unfolding int_poly_associated_to_vec_def 
    by (smt (verit) access_entry_in_int_poly_associated_to_vec assms(5) bot_nat_0.not_eq_extremum dim_vec_associated_to_int_poly_lteq floor_divide_of_int_eq mult_of_nat_commute nat_SN.compat nonzero_mult_div_cancel_left of_int_of_nat_eq of_nat_eq_iff semiring_1_class.of_nat_power semiring_1_class.of_nat_simps(1) semiring_1_no_zero_divisors_class.power_not_zero vec_associated_to_int_poly_inverse)
qed

lemma int_poly_associated_to_nil_vec_same_norm:
  assumes "X > 0"
  assumes "dim_vec v = 0"
  shows "euclidean_norm_int_vec v = euclidean_norm_int_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X)"
proof -
  have v_is_nil: "v = vNil"
    using assms 
    by simp
  then have h1: "euclidean_norm_int_vec v= 0"
    unfolding euclidean_norm_int_vec_eq by auto
  have "int_poly_associated_to_vec v X = 0"
    using v_is_nil unfolding int_poly_associated_to_vec_def by simp
  then have "vec_associated_to_int_poly (int_poly_associated_to_vec v X) X = vec_of_list [0]"
    unfolding vec_associated_to_poly_def by auto
  then have h2: "euclidean_norm_int_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X) = 0"
    unfolding euclidean_norm_int_vec_eq by auto
  show ?thesis
    using h1 h2 by auto
qed

lemma int_poly_associated_to_notNil_vec_same_norm:
  assumes X_gt: "X > 0"
  assumes "dim_vec v > 0"
  assumes "\<And>j. j < dim_vec v \<Longrightarrow> (\<exists>k. (X^j)*k = (v $ j))"
  shows "euclidean_norm_int_vec v = euclidean_norm_int_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X)"
proof -
  let ?w = "vec_associated_to_int_poly (int_poly_associated_to_vec v X) X"
  have h1: "(\<Sum>i<(dim_vec v). (v$i)^2) = (\<Sum>i<(dim_vec ?w). (v$i)^2)"
    using assms int_poly_associated_to_notNil_vec_same_norm_upto
    by simp
  then have h2: "\<And>i. i < dim_vec ?w \<Longrightarrow> ((v $ i) = (?w $ i))"
    using int_poly_associated_to_notNil_vec_same_entries assms 
    by (metis One_nat_def Suc_leI)
  then have "(\<Sum>i<(dim_vec v). (v$i)^2) = (\<Sum>i<(dim_vec ?w). (?w$i)^2)" using h1 h2 
    by auto
  then show ?thesis
    using assms euclidean_norm_int_vec_eq
    by presburger
qed

lemma int_poly_associated_to_vec_same_norm:
  assumes "X > 0"
  assumes "\<And>j. j < dim_vec v \<Longrightarrow> (\<exists>k. (X^j)*k = (v $ j))"
  shows "euclidean_norm_int_vec v = euclidean_norm_int_vec (vec_associated_to_int_poly (int_poly_associated_to_vec v X) X)"
  using assms int_poly_associated_to_nil_vec_same_norm int_poly_associated_to_notNil_vec_same_norm
  by (metis bot_nat_0.not_eq_extremum)

lemma int_poly_associated_to_vec_sum:
  assumes "dim_vec a = dim_vec b"
  assumes "\<And>i. i < dim_vec a \<Longrightarrow>
      a $ i mod X ^ i = 0"
  assumes "\<And>i. i < dim_vec b \<Longrightarrow>
      b $ i mod X ^ i = 0"
  assumes "X > 0"
  shows "int_poly_associated_to_vec (a+b) X = int_poly_associated_to_vec a X + int_poly_associated_to_vec b X"
proof -
  let ?newvec_sum = "vec (dim_vec (a + b)) (\<lambda>j. \<lfloor>real_of_int ((a + b) $ j) / real (X ^ j)\<rfloor>)"
  let ?newvec_a = "vec (dim_vec a) (\<lambda>j. \<lfloor>real_of_int (a $ j) / real (X ^ j)\<rfloor>)"
  let ?newvec_b = "vec (dim_vec b) (\<lambda>j. \<lfloor>real_of_int (b $ j) / real (X ^ j)\<rfloor>)"
  have same_dim: "dim_vec (a + b) = dim_vec a"
    using assms(1) 
    by auto
  have "\<And>j. j < dim_vec a \<Longrightarrow> \<lfloor>real_of_int ((a + b) $ j) / real (X ^ j)\<rfloor> = \<lfloor>real_of_int (a $ j) / real (X ^ j)\<rfloor> + \<lfloor>real_of_int (b $ j) / real (X ^ j)\<rfloor>"
  proof - fix j
    assume j_lt: "j < dim_vec a"
    then obtain k1 k2::"int" where k1k2_prop: "a $ j = k1*X^j" "b $ j = k2*X^j"
      using assms(2)[of j] assms(3)[of j] assms(1) by (auto elim!: dvdE) blast
    have roi: "\<lfloor>real_of_int (a $ j) / real (X ^ j)\<rfloor> = k1"  "\<lfloor>real_of_int (b $ j) / real (X ^ j)\<rfloor> = k2"
      using assms(4) k1k2_prop(1) apply simp 
      using assms(4) k1k2_prop(2) by simp 
    have "(a + b) $ j = k1*X^j + k2*X^j"
      using k1k2_prop assms(1) j_lt by auto
    then show "\<lfloor>real_of_int ((a + b) $ j) / real (X ^ j)\<rfloor> = \<lfloor>real_of_int (a $ j) / real (X ^ j)\<rfloor> + \<lfloor>real_of_int (b $ j) / real (X ^ j)\<rfloor>"
      using k1k2_prop roi assms(4)  
      using div_mult_self3 floor_divide_real_eq_div floor_of_int of_int_of_nat_eq of_nat_0_eq_iff of_nat_0_le_iff power_eq_0_iff zero_less_iff_neq_zero by auto
  qed
  then have "\<And>j. j < dim_vec a \<Longrightarrow>  monom (?newvec_sum $ j) j = 
    monom (?newvec_a $ j) j  + monom (?newvec_b $ j) j"
    by (simp add: add_monom assms(1))
  then have "(\<Sum>i<dim_vec a. monom (?newvec_sum $ i) i) = (\<Sum>i<dim_vec a. monom (?newvec_a $ i) i) + (\<Sum>i<dim_vec a. monom (?newvec_b $ i) i)"
    by auto
  then  show ?thesis
    unfolding int_poly_associated_to_vec_def using assms(1) same_dim by algebra
qed

lemma int_poly_associated_to_vec_constant_mult:
  fixes c:: "nat \<Rightarrow> int"
  fixes v:: "int vec"
  assumes "X > 0"
  assumes div_by_X: "\<And>i. i < dim_vec v \<Longrightarrow>
      v $ i mod X ^ i = 0"
  shows "int_poly_associated_to_vec (c i \<cdot>\<^sub>v v) X =
    smult (c i) (int_poly_associated_to_vec v X)"
proof - 
  let ?newvec = "vec (dim_vec v) (\<lambda>j. \<lfloor>real_of_int (v $ j) / real (X ^ j)\<rfloor>)"
  let ?newvec_mult = "vec (dim_vec (c i \<cdot>\<^sub>v v)) (\<lambda>j. \<lfloor>real_of_int ((c i \<cdot>\<^sub>v v) $ j) / real (X ^ j)\<rfloor>)"
  have same_dim: "dim_vec ?newvec = dim_vec ?newvec_mult"
    by auto
then have "(c i) * ?newvec $ j =  (?newvec_mult $ j)" if j_prop: "j < dim_vec v" for j
  using div_by_X [of j] \<open>0 < X\<close> that
  by (simp only: floor_divide_of_int_eq flip: Power.of_nat_power of_int_of_nat_eq [where ?'a = real])
    auto
then have "smult (c i) (monom (?newvec $ j) j) =  monom (?newvec_mult $ j) j" if j_prop: "j < dim_vec v" for j
  by (simp add: smult_monom j_prop)
  then have "(\<Sum>j<dim_vec v. monom (?newvec_mult $ j) j) = (\<Sum>j<dim_vec v. smult (c i) (monom (?newvec $ j) j))"
    by auto
  then have "(\<Sum>j<dim_vec v. monom (?newvec_mult $ j) j) = smult (c i) (\<Sum>j<dim_vec v. monom (?newvec $ j) j)"
    by (simp add: smult_sum2)
  then show ?thesis
    unfolding int_poly_associated_to_vec_def by auto
qed

subsection \<open> Generic Coppersmith assumptions locale\<close>

text \<open> The generic properties required are stored in this locale. \<close>

locale coppersmith_assms = LLL_with_assms +
  fixes x0 :: int
  fixes M X :: nat
  fixes F :: "int poly"
  assumes M: "M > 0"
  assumes X: "X > 0"
  assumes n: "n > 0"
  assumes x0: "poly F x0 mod M = 0" "\<bar>x0\<bar> \<le> int X"
  assumes lfs: "length fs_init \<noteq> 0"
  assumes Xpoly: "\<And>v j.
    v \<in> set fs_init \<Longrightarrow> j < n \<Longrightarrow>
    v $ j mod int X ^ j = 0"
  assumes rt: "\<And>v.
    v \<in> set fs_init \<Longrightarrow>
    poly (int_poly_associated_to_vec v X) x0 mod M = 0"
begin

lemma sumlist_mod:
  assumes "\<And>v. v \<in> set xs \<Longrightarrow> dim_vec v = n"
  assumes m0: "\<And>v j.
    v \<in> set xs \<Longrightarrow> j < n \<Longrightarrow>
    v $ j mod int X ^ j = 0"
  assumes "i < n"
  shows "M.sumlist xs $ i mod X ^ i = 0"
proof -
  from sumlist_nth
  have "M.sumlist xs $ i =
    (\<Sum>j = 0..<length xs. xs ! j $ i)"
    by (metis assms(1,3))

  moreover have "... mod int (X ^ i) =
    (\<Sum>j = 0..<length xs.
      xs ! j $ i  mod int X ^ i) mod
    int X ^ i"
    apply (subst mod_sum_eq[symmetric])
    by (simp add: mod_mult_left_eq)
  moreover have "... = 0"
    using m0
    by (simp add: assms(3))
  ultimately show ?thesis
    by auto
qed

lemma poly_associated_to_vec_sumlist:
  assumes "\<And>v. v \<in> set xs \<Longrightarrow> dim_vec v = n"
  assumes "\<And>v j. v \<in> set xs \<Longrightarrow>
      j < dim_vec v \<Longrightarrow> v $ j mod X ^ j = 0"
  shows "int_poly_associated_to_vec (sumlist xs) X =
    (\<Sum>i < length xs. int_poly_associated_to_vec (xs ! i) X)"
  using assms
proof (induction xs)
  case Nil
  then show ?case 
    unfolding int_poly_associated_to_vec_def
    by auto
next
  case ih: (Cons x xs)
  have "int_poly_associated_to_vec (M.sumlist (x # xs)) X =
    int_poly_associated_to_vec (x + M.sumlist xs) X"
    by auto
  also have "... =  int_poly_associated_to_vec x X +
     int_poly_associated_to_vec (M.sumlist xs) X "
    apply (intro int_poly_associated_to_vec_sum[OF _ _ _ X])
    using ih.prems(1) dim_sumlist apply clarsimp
    using ih.prems(2) apply simp
    using dim_sumlist ih(2) ih.prems(2) sumlist_mod by auto 
  also have "... =  int_poly_associated_to_vec x X +
     (\<Sum>i<length xs. int_poly_associated_to_vec (xs ! i) X)"
    apply (subst ih(1))
    using ih by auto
  also have "... = 
   (\<Sum>i \<in> {0..<Suc (length xs)}.
    int_poly_associated_to_vec ((x # xs) ! i) X)"
    apply (subst  sum.atLeast0_lessThan_Suc_shift)
    using atLeast_upt set_upt
    by auto
  finally show ?case
    using atLeast0LessThan by fastforce
qed

lemma short_vector_inherit_props:
  shows "\<And>j. j < n \<Longrightarrow> short_vector $ j mod X ^ j = 0"
    "poly (int_poly_associated_to_vec short_vector X) x0 mod M = 0"
proof -
  have *: "set fs_init \<subseteq> carrier_vec n"
    by (simp add: fs_init)
  have svin: "short_vector \<in> lattice_of fs_init"
    using L_def lfs len short_vector(2) short_vector_impl by auto
  from in_latticeE[OF this]
  obtain c where 
    c: "short_vector =
        M.sumlist
         (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v fs_init ! i)
           [0..<length fs_init])" .

  {
    fix i j
    assume "i < m" "j < n"
    then have "fs_init ! i $ j mod int X ^ j = 0"
      using Xpoly len nth_mem by blast
    
    moreover have "(c i \<cdot>\<^sub>v fs_init ! i) $ j = c i * fs_init ! i $ j"
      apply (subst index_smult_vec)
       apply (metis LLL_inv_wD(4) LLL_inv_wI L_def \<open>i < m\<close> \<open>j < n\<close> carrier_vecD fs_init len lin_dep)
      by auto
    ultimately have "(c i \<cdot>\<^sub>v fs_init ! i) $ j mod int X ^ j = 0"
      by force 
  }
  then have m0: "i < m \<Longrightarrow> j < n \<Longrightarrow> (c i \<cdot>\<^sub>v fs_init ! i) $ j mod int X ^ j = 0" for i j
    by auto

  {
    fix j
    assume j: "j < n"
    show "short_vector $ j mod int (X ^ j) = 0"
      unfolding c
      apply (intro sumlist_mod[OF _ _ j])
      subgoal apply clarsimp
        by (metis LLL_invD(7) LLL_inv_wD(4) LLL_inv_wI LLL_with_assms.LLL_inv_initial_state LLL_with_assms_axioms carrier_vecD fs_init len lin_dep)
      using m0 len by auto
  }
  have 1: "(\<Sum>i<m.
         int_poly_associated_to_vec (c i \<cdot>\<^sub>v fs_init ! i) X) =
    (\<Sum>i<m.
         smult (c i) (int_poly_associated_to_vec (fs_init ! i) X))"
    apply (intro sum.cong)
     apply clarsimp
    apply (subst int_poly_associated_to_vec_constant_mult[OF X])
    using len nth_mem 
    apply (auto intro!: Xpoly)[2]
    by (metis LLL_inv_wD(4) LLL_inv_wI L_def carrier_vecD fs_init lin_dep)

  then have 2: "poly ... x0 =
    (\<Sum>i<m. c i * poly (int_poly_associated_to_vec (fs_init ! i) X) x0)"
    apply (subst poly_hom.hom_sum)
    by auto
  then have "... mod M =
    (\<Sum>i<m. (c i * poly (int_poly_associated_to_vec (fs_init ! i) X) x0) mod M)  mod M"
    by (auto simp add: mod_sum_eq)
  also have "... =
    (\<Sum>i<m. (0::int)) mod M"
    apply (intro arg_cong[where f = "\<lambda>i::int. i mod M"])
    apply (intro sum.cong)
    using len nth_mem
    using rt by (auto simp add: pull_mods(10))
  also have "... = 0" by auto
  finally show "poly
     (int_poly_associated_to_vec local.short_vector X)
     x0 mod M = 0"
    unfolding c
    apply (subst poly_associated_to_vec_sumlist)
    subgoal
      using LLL_inv_wD(4) LLL_inv_wI L_def fs_init len lin_dep by auto
    subgoal
      using m0 apply clarsimp
      by (metis LLL.LLL_inv_wD(4) LLL_inv_wI L_def carrier_vecD fs_init index_smult_vec(1) len lin_dep)
    using 1 2 len by auto
qed

lemma root_poly_short_vector:
  assumes bnd: "real_of_int \<parallel>short_vector\<parallel>\<^sup>2 < M^2 / n"
  shows "poly (int_poly_associated_to_vec short_vector X) x0 = 0"
proof -
  have dimsv: "dim_vec short_vector = n"
    using lfs carrier_dim_vec len short_vector(1) short_vector_impl by blast
  
  have *: "\<And>j. j < dim_vec short_vector \<Longrightarrow>
         \<exists>k. int X ^ j * k = short_vector $ j"
    unfolding dimsv
    apply (drule  short_vector_inherit_props(1))
    by auto

  have db: "1 +
      real (degree (int_poly_associated_to_vec short_vector X)) \<le> n"
    by (smt (verit, best) dimsv n nat_less_real_le int_poly_associated_to_vec_degree)

  have "sqrt (real_of_int \<parallel>short_vector\<parallel>\<^sup>2) <
    sqrt (real M^2 / (real n))"
    using bnd unfolding real_sqrt_le_iff by auto

  then have "sqrt (real_of_int \<parallel>short_vector\<parallel>\<^sup>2) <
    M / sqrt (real n)"
    by (simp add: real_sqrt_divide)
 
  also have "... \<le>
    real M / sqrt
       (real (degree(int_poly_associated_to_vec short_vector X) + 1))"
    using db
    by (clarsimp simp add: field_simps M )

  finally have **:
    "sqrt (real_of_int \<parallel>short_vector\<parallel>\<^sup>2) < real M / sqrt
       (real
         (degree
           (int_poly_associated_to_vec short_vector X) + 1))" by auto

  show ?thesis                                               
    apply (intro Howgrave_Graham_int_poly[OF M short_vector_inherit_props(2) x0(2)])
    apply (subst int_poly_associated_to_vec_same_norm[OF X, symmetric, OF *])
    using **
    by auto
qed

lemma bnd_raw_imp_short_vec_bound:
  assumes bnd_raw:"
    (real_of_rat \<alpha>) ^ (m * (m - 1) div 2) *
    real_of_int (gs.Gramian_determinant fs_init m) *
    (real n) ^ m <
    M ^ (2 * m)"
  shows "real_of_int \<parallel>short_vector\<parallel>\<^sup>2 < M^2 / n"
proof -

  have LLLinv: "LLL_invariant True m reduce_basis"
    using reduce_basis_inv by auto

  have i1: "distinct reduce_basis"
    by (metis (no_types, lifting) LLL_invD(1) LLL_invD(2) LLL_invD(6) LLLinv distinct_conv_nth gs.lin_indpt_list_def nth_map)
  
  from LLL_invD[OF LLLinv]
  have "gs.lin_indpt_list
     (map of_int_vec reduce_basis)" by blast

  then have "module.lin_indpt class_ring
     (module_vec TYPE(rat) n)
     (set (map of_int_vec reduce_basis))"
    unfolding gs.lin_indpt_list_def
    by blast

  then have i2: "module.lin_indpt class_ring
     (module_vec TYPE(int) n)
     (set reduce_basis)"
    using casting_lin_comb_helper_2
    by (metis \<open>set local.reduce_basis \<subseteq> carrier_vec n\<close> carrier_vecD subset_code(1))
  
  have i3: "set reduce_basis \<subseteq> carrier_vec n"
    using LLL.LLL_invD(3) LLLinv by blast
  have i4:"set fs_init \<subseteq> carrier_vec n"
    using fs_init by blast
  have i5:"length reduce_basis = length fs_init"
    by (simp add: \<open>length local.reduce_basis = m\<close> len)

  have i6: "vec_module.lattice_of n reduce_basis =
    vec_module.lattice_of n fs_init"
      using LLL_invD(7) LLLinv L_def by blast

  from ring_char_0_vec_module.lattice_of_eq_gram_det_rows_eq[OF i1 i2 i3 i4 i5 i6]
  have "det (mat_of_rows n reduce_basis *
     (mat_of_rows n reduce_basis)\<^sup>T) =
    det (mat_of_rows n fs_init * (mat_of_rows n fs_init)\<^sup>T)" .


  have deteq: "gs.Gramian_determinant reduce_basis m = gs.Gramian_determinant fs_init m"
    unfolding gs.Gramian_determinant_def
    apply (subst  gs.Gramian_matrix_alt_def)
    using \<open>length local.reduce_basis = m\<close> apply linarith
    apply (subst  gs.Gramian_matrix_alt_def)
    using len apply blast
    by (metis \<open>det (mat_of_rows n local.reduce_basis * (mat_of_rows n local.reduce_basis)\<^sup>T) = det (mat_of_rows n fs_init * (mat_of_rows n fs_init)\<^sup>T)\<close> \<open>length local.reduce_basis = m\<close> \<open>m \<le> m\<close> i5 take_all)

  have bnd:
  "(real_of_rat \<alpha>) ^ (m * (m - 1) div 2) *
      real_of_int (gs.Gramian_determinant fs_init m) <
  (M^2 / (real n)) ^ m"
  proof -
    have m_gt: "m > 0"
      using len lfs by blast
    from bnd_raw
    have "real_of_rat \<alpha> ^ (m * (m - 1) div 2) *
    real_of_int (gs.Gramian_determinant fs_init m)
    < real (M ^ (2 * m)) / (real n) ^ m"
      using m_gt n by (auto simp add: field_simps)
    also have "... = (M^2 / (real n)) ^ m"
      unfolding power_mult
      by (auto simp add: field_simps)
    finally show ?thesis .
  qed

  have "rat_of_int \<parallel>short_vector\<parallel>\<^sup>2 ^ m
      \<le> \<alpha> ^ (m * (m - 1) div 2) *
      rat_of_int (gs.Gramian_determinant reduce_basis m)"
    using LLL.LLL_invD(6) LLL_inv_initial_state LLL_with_assms.short_vector_det_bound LLL_with_assms_axioms lfs by blast

  have
    "rat_of_int \<parallel>short_vector\<parallel>\<^sup>2 ^ m
      \<le> \<alpha> ^ (m * (m - 1) div 2) *
      rat_of_int (gs.Gramian_determinant reduce_basis m)"
    using LLL.LLL_invD(6) LLL_inv_initial_state LLL_with_assms.short_vector_det_bound LLL_with_assms_axioms lfs by blast
  then have "(real_of_int \<parallel>short_vector\<parallel>\<^sup>2) ^ m <
    (M^2 / (real n)) ^ m"
    using bnd
    by (smt (verit, best) deteq of_rat_hom.hom_power of_rat_less_eq of_rat_mult of_rat_of_int_eq)

  thus ?thesis
    using power_mono_iff n
    by (smt (verit, best) LLL_inv_initial_state LLL_invariant_def M Num.of_nat_simps(1) lfs length_0_conv length_greater_0_conv linorder_not_le nat_le_real_less nat_zero_less_power_iff zero_compare_simps(7))
qed

end

end