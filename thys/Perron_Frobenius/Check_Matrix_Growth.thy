(* Author: Thiemann *)
section \<open>An efficient algorithm to compute the growth rate of $A^n$.\<close>
theory Check_Matrix_Growth
  imports Spectral_Radius_Theory_2
  Algebraic_Numbers.Complex_Algebraic_Numbers
begin
subsection \<open>For completeness, we also present the naive implementation which
  always invokes algebraic numbers.\<close>

hide_const (open) Coset.order

definition compute_set_of_jordan_blocks_cp :: "'a :: field mat \<Rightarrow> 'a \<Rightarrow> 'a poly \<Rightarrow> (nat \<times> 'a)list" where
  "compute_set_of_jordan_blocks_cp A ev f \<equiv> let 
     k = order ev f;
     as = map (dim_gen_eigenspace A ev) [0 ..< Suc (Suc k)];
     cards = map (\<lambda> k. (k, 2 * as ! k - as ! (k - 1) - as ! Suc k)) [1 ..< Suc k]
     in map (\<lambda> (k,c). (k,ev)) (filter (\<lambda> (k,c). c \<noteq> 0) cards)"

definition check_jordan_block_cp :: "'a :: field mat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a poly \<Rightarrow> bool" where
  "check_jordan_block_cp A d x cp = (\<forall>bsize\<in>fst ` set (compute_set_of_jordan_blocks_cp A x cp). bsize \<le> d + 1)" 

definition naive_matrix_complexity_checker :: "real mat \<Rightarrow> real poly \<Rightarrow> nat \<Rightarrow> bool option" where
  "naive_matrix_complexity_checker A cp d = (let
     cpc = map_poly complex_of_real cp;
     rts = roots_of_complex_poly cpc in 
     case rts of None \<Rightarrow> None 
     | Some evs \<Rightarrow> Some 
       (let evn = map (\<lambda> ev. (ev, cmod ev)) evs
          in (\<forall> ev \<in> set evn. snd ev \<le> 1 \<and> 
          (snd ev = 1 \<longrightarrow> check_jordan_block_cp (map_mat of_real A) d (fst ev) cpc))))" 

lemma compute_set_of_jordan_blocks_cp[simp]: 
  "compute_set_of_jordan_blocks_cp A ev (char_poly A) = 
    compute_set_of_jordan_blocks A ev" 
  unfolding compute_set_of_jordan_blocks_cp_def compute_set_of_jordan_blocks_def Let_def 
  by auto

lemma naive_matrix_complexity_checker: assumes A: "A \<in> carrier_mat n n" 
  and check: "naive_matrix_complexity_checker A (char_poly A) d = Some True" 
shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof -
  let ?c = complex_of_real
  let ?A = "map_mat ?c A" 
  from A have cA: "?A \<in> carrier_mat n n" by auto
  note check = check[unfolded naive_matrix_complexity_checker_def Let_def 
    of_real_hom.char_poly_hom[OF A, symmetric]]
  from check obtain evs where rts: "roots_of_complex_poly (char_poly ?A) = Some evs" 
    by (auto split: option.splits)
  note check = check[unfolded this, simplified, rule_format]
  note rts = roots_of_complex_poly[OF rts]
  show ?thesis
  proof (rule norm_bound_complex_to_real[OF A], rule jnf_complexity_generic[OF cA])
    fix ev
    assume "poly (char_poly ?A) ev = 0" 
    hence ev: "ev \<in> set evs" using rts by auto
    from check[OF ev] show "cmod ev \<le> 1" 
      "cmod ev = 1 \<Longrightarrow>
         \<forall>bsize\<in>fst ` set (compute_set_of_jordan_blocks ?A ev).
            bsize \<le> d + 1" 
      by (auto simp: check_jordan_block_cp_def)
  qed
qed

subsection \<open>The improved algorithm\<close>

definition prim_root_unity_list :: "nat \<Rightarrow> complex list" where
  "prim_root_unity_list k = (if k = 0 then [] else 
     if k = 1 then [1] else 
     if k = 2 then [-1] else
     if k = 3 then [Complex (-1/2) (sqrt 3 / 2), Complex (-1/2) (- sqrt 3 / 2)] else
     if k = 4 then [\<i>, - \<i>] else complex_roots_of_int_poly (monom 1 k - 1))"

definition compute_set_of_jordan_blocks_order :: "'a :: field mat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)list" where
  "compute_set_of_jordan_blocks_order A ev k \<equiv> let 
     as = map (dim_gen_eigenspace A ev) [0 ..< Suc (Suc k)];
     cards = map (\<lambda> k. (k, 2 * as ! k - as ! (k - 1) - as ! Suc k)) [1 ..< Suc k]
     in map (\<lambda> (k,c). (k,ev)) (filter (\<lambda> (k,c). c \<noteq> 0) cards)"

definition check_jordan_block :: "'a :: field mat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "check_jordan_block A d x or = 
     (\<forall>bsize\<in>fst ` set (compute_set_of_jordan_blocks_order A x or). bsize \<le> d + 1)" 

definition check_matrix_complexity :: "real mat \<Rightarrow> real poly \<Rightarrow> nat \<Rightarrow> bool" where
  "check_matrix_complexity A cp d = (let 
     ks = fst (decompose_prod_root_unity cp);
     n = dim_row A;
     lks = length ks;
     m = max_list ks 
   in count_roots_above cp 1 = 0 \<and> (if d + 1 < lks 
     then check_jordan_block A d 1 lks
      \<and> (n > 4 \<longrightarrow> 
          (2 \<le> m \<longrightarrow> (let lks2 = length (filter even ks) in 
               lks2 > d + 1 \<longrightarrow> check_jordan_block A d (- 1) lks2))
         \<and> (\<forall> k \<in> set [3 ..< m + 1]. let lksk = length [k'\<leftarrow>ks . k dvd k'] in
               lksk > d + 1 \<longrightarrow> (\<forall> x \<in> set (prim_root_unity_list k). 
                 check_jordan_block (map_mat complex_of_real A) d x lksk)))            
     else True))" 

lemma compute_set_of_jordan_blocks_order[simp]: 
  "compute_set_of_jordan_blocks_order A ev (order ev (char_poly A)) = 
    compute_set_of_jordan_blocks A ev" 
  unfolding compute_set_of_jordan_blocks_order_def compute_set_of_jordan_blocks_def Let_def 
  by auto

lemma prim_root_unity_list: "set (prim_root_unity_list k) \<supseteq> Collect (primitive_root_unity k)" 
proof (cases "k \<le> 4")
  case True
  hence "k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4" by auto
  thus ?thesis using primitive_root_unity_explicit
    by (auto simp: prim_root_unity_list_def primitive_root_unity_def[of 0])
next
  case False
  let ?p = "monom 1 k - 1 :: int poly" 
  have "degree ?p = k" using False 
    by (metis degree_root_unity root_unity_def)
  hence p0: "?p \<noteq> 0" using False by auto
  from False
  have "set (prim_root_unity_list k) = set (complex_roots_of_int_poly (monom 1 k - 1))" 
    unfolding prim_root_unity_list_def by auto
  also have "\<dots> = {x. ipoly ?p x = 0}" unfolding complex_roots_of_int_poly(1)[OF p0] ..
  also have "\<dots> = {x. x^k = 1}"  
    by (simp add: of_int_poly_hom.hom_minus poly_monom)
  also have "\<dots> \<supseteq> Collect (primitive_root_unity k)" 
    unfolding primitive_root_unity_def by auto
  finally show ?thesis by auto
qed

lemma check_matrix_complexity: assumes A: "A \<in> carrier_mat n n" and nn: "nonneg_mat A" 
  and check: "check_matrix_complexity A (char_poly A) d" 
shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof -
  let ?c = complex_of_real 
  obtain ks where ks: "ks = fst (decompose_prod_root_unity (char_poly A))" by auto
  note check = check[unfolded check_matrix_complexity_def 
      Let_def count_roots_above_correct, folded ks]
  have fin: "finite {x. poly (char_poly A) x = 0}" 
    by (rule poly_roots_finite, insert degree_monic_char_poly[OF A], auto)
  from check have "card {x. 1 < x \<and> poly (char_poly A) x = 0} = 0" by auto
  from this[unfolded card_eq_0_iff] fin 
  have "{x. 1 < x \<and> poly (char_poly A) x = 0} = {}" by auto
  hence sr: "poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" for x by force
  show ?thesis
  proof (cases "n \<le> 4")
    case True
    show ?thesis
    proof (rule jnf_perron_frobenius_only_block_1_dim_4[OF A nn sr ks True], goal_cases)
      case 2
      from check 2 have jb: "check_jordan_block A d 1 (length ks)" by auto
      thus ?case unfolding check_jordan_block_def 2(3)[symmetric] by simp
    qed
  next
    case False
    hence dim: "(dim_row A > 4) = True" using A by auto
    have "set [3..<max_list ks + 1] = {3 .. max_list ks}" by auto
    note check = check[unfolded this dim]
    show ?thesis
    proof (rule jnf_perron_frobenius_generic[OF A nn sr ks], goal_cases)
      case (2 x k)
      from 2(2) have "(d + 1 < length ks) = True" by auto
      note check = check[unfolded this, simplified]
      {
        assume "k \<le> 2" 
        with 2(4,6) have choice: "k = 1 \<and> x = ?c 1 \<or> k = 2 \<and> x = ?c (-1) \<and> 2 \<le> max_list ks" 
          by (cases "k = 0"; cases "k = 1"; cases "k = 2", 
            auto simp: primitive_root_unity_explicit[simplified])
        then obtain y where x: "x = ?c y" by blast
        from choice have choice: "k = 1 \<and> y = 1 \<or> k = 2 \<and> y = (-1) \<and> 2 \<le> max_list ks" 
          unfolding x of_real_eq_iff by auto 
        from choice 2(5) False x check
        have "check_jordan_block A d y (length (filter ((dvd) k) ks))" by auto
        from this[unfolded 2(7)[symmetric] x order_of_real_char_poly[OF A]]
        have "check_jordan_block A d y (order y (char_poly A))" by auto
        from this[unfolded check_jordan_block_def compute_set_of_jordan_blocks_order]
        have ?case unfolding x of_real_hom.hom_compute_set_of_jordan_blocks[OF A] by auto
      } 
      moreover
      {
        let ?A = "map_mat ?c A" 
        from 2(6) have x: "x \<in> set (prim_root_unity_list k)" using prim_root_unity_list[of k] by auto
        assume "k \<ge> 3" 
        with 2(4) have "2 \<le> max_list ks" "k \<in> {3 .. max_list ks}" by auto
        with check 2(5,7) x
        have "check_jordan_block ?A d x (order x (char_poly ?A))" by auto
        from this[unfolded check_jordan_block_def compute_set_of_jordan_blocks_order]
        have ?case .
      }
      ultimately show ?case by linarith
    qed
  qed 
qed

end
