(*  Title:       The Cayley-Hamilton Theorem
    Author:      Stephan Adelsberger <sadelsbe /at/ wu /dot/ ac /dot/ at>,
                 Stefan Hetzl <stefan.hetzl /at/ tuwien /dot/ ac /dot/ at>,
                 Florian Pollak <florian.pollak /at/ gmail /dot/ com>, 2014
    Maintainer:  Stephan Adelsberger <sadelsbe /at/ wu /dot/ ac /dot/ at>
*)

header {* The Cayley-Hamilton theorem\label{sec.ch} *}

theory Cayley_Hamilton
imports
  Main
  "~~/src/HOL/Library/Polynomial"  
  "~~/src/HOL/Multivariate_Analysis/Determinants" 
  Polynomial_extension
  Determinants_extension
  Matrices
  Polynomial_matrix
begin

text{* As preparation for the proof of the Cayley-Hamilton theorem we first show
   that the maximal degree of $\mathrm{adj}(X I_n - A)$ is $n-1$. *}

lemma maxdeg_cofactorM:
fixes A :: "'a::comm_ring_1^'n\<Colon>finite^'n"
shows "maxdegM (transpose (cofactorM (mat (monom 1 (Suc 0)) - mat2matofpoly A))) = CARD('n) - 1"
proof-
  txt{* charpoly *}
  let ?B = "mat (monom 1 (Suc 0)) - mat2matofpoly A"
  let ?U = "UNIV :: 'n::finite set"
   
  let ?f = "\<lambda>p. \<Sum>i\<in>?U. degree (?B $ i $ p i)" 
  let ?m = "Max {\<Sum>i\<in>?U. degree (?B $ i $ p i) | p. p permutes ?U}"
  let ?mon_A = "\<lambda>i. monom 1 (Suc 0) - [:A $ i $ i:]"

  { fix i j :: "'n::finite" 
    let ?B' = "minorM ?B i j"
    let ?aB' = "\<lambda> r c. (if r = i \<and> c = j then 1 else if r = i \<or> c = j then 0 
               else (if r = c then monom 1 (Suc 0) - [:A $ r $ c:]  else [: - A $ r $ c:]))"
            
    have deg_aB': "\<And> r c. degree (?aB' r c) = (if r = i \<or> c = j \<or> r \<noteq> c then 0 else 1)"
      by(simp add: monom_poly_degree_one)

    have B'_eq: "?B' = (\<chi> i j. ?aB' i j)"
      by (simp add: vec_eq_iff minorM_def mat_def mat2matofpoly_def)
      
    let ?f = "\<lambda>p. \<Sum>l\<in>?U. degree (?aB' l (p l))"   

    have max_card_minus: "Max {?f p |p. p permutes ?U} \<le> card(?U) - 1"
      by(intro Max.boundedI)
        (auto simp add: card_insert Collect_disj_eq
                        deg_aB' setsum.If_cases card_Compl exI[of _ id] permutes_id[of ?U])

    { assume ij: "i = j"
      
      { fix p assume a: "p \<noteq> id" "?aB' i (p i) = 1" 
        have "\<exists>k. (k \<noteq> i) \<and> degree (?aB' k (p k)) = 0"
          by(simp add: a) (metis a eq_id_iff[of p] one_neq_zero)
  
        then obtain k where P: "k \<noteq> i" "degree (?aB' k (p k)) = 0"
          by auto
        
        have "(\<Sum>l\<in>?U. degree (?aB' l (p l))) = (\<Sum>l\<in>?U - {k} - {i}. degree (?aB' l (p l)))"
          using P
          by(intro setsum.mono_neutral_right) (auto)
        also have "\<dots> \<le> (\<Sum>l\<in>?U - {k} - {i}. 1)"
          by (intro setsum_mono)
             (simp add: minorM_def mat_def mat2matofpoly_def monom_poly_degree_one)
        finally have "degree (\<Prod>l\<in>?U. (?aB' l (p l))) \<le> card(?U) - 2"
          using P degree_setprod_le[of "\<lambda>l. (?aB' l (p l))" "?U"]
          by (auto simp: card_Diff_subset)
          
      } note case_p_not_id1 = this
  
      txt {* one diagonal element is 1, while everything else is equal to B *}
      
      have 1: "(\<Sum>l\<in>?U. degree (?aB' l (id l))) = card(?U) - 1"
        unfolding deg_aB' using ij by (simp add: setsum.If_cases card_Compl)
  
      have 2: "degree (\<Prod>l\<in>?U. ?aB' l (id l)) = card (?U) - 1"
        using ij degree_setprod_le[of "\<lambda>l. ?mon_A l" "?U - {j}"]
        coeff_mult_setprod_setsum[of "\<lambda>l. ?aB' l (id l)" "?U-{i}"]
        le_degree[of "\<Prod>i\<in>UNIV - {j}. ?mon_A i" "CARD('n) - Suc 0"]
        by(simp add: setprod.If_cases monom_poly_degree_one Compl_eq_Diff_UNIV)
        
      have case_B_i_p_i_is_zero: "\<And>p. ?aB' i (p i) = 0 \<Longrightarrow> (\<Prod>i\<in>?U. ?aB' i (p i)) = 0"
        by(force intro!: setprod_zero)
         
      { fix p:: "'n::finite \<Rightarrow> 'n"
        assume "p \<noteq> id"
        then have "degree (\<Prod>l\<in>UNIV. ?aB' l (p l)) \<le> CARD('n) - 2"
          using case_B_i_p_i_is_zero[of p] case_p_not_id1(1)[of p]
          by (metis (no_types, lifting) degree_0 le0)
      } note case_p_not_id2 = this
  
      { assume a1: "1 < CARD('n)"
          
        let ?f = "\<lambda>p. \<Sum>l\<in>UNIV. degree (?aB' l (p l))"
        let ?S = "{?f p | p. p permutes ?U}"
         
        have "Max ?S = CARD('n) - 1"
          using ij 1[symmetric] permutes_id max_card_minus 
          by(intro Max_eqI)
            (simp_all add: permutes_id[of ?U] exI[of _ id])
  
          also have "\<forall>(p::'n::finite \<Rightarrow> 'n). p\<noteq>id \<longrightarrow> degree (\<Prod>l\<in>?U. ?aB' l (p l)) \<le> CARD('n) - 2"
          using ij case_p_not_id2 
          by simp
            
        ultimately have "degree (det ?B') = CARD('n) - 1"
          unfolding B'_eq
          using ij a1 2 permutes_id[of ?U]             
          by(subst det_coeff_poly_mat(1)[of id "(\<chi> i j. ?aB' i j)"])
            (auto simp only: vec_lambda_beta)
      }
    }
    hence "1 < CARD('n) \<Longrightarrow> i = j \<Longrightarrow> degree (det ?B') = CARD('n) - 1"
     and  "i \<noteq> j \<Longrightarrow> degree (det ?B') \<le> CARD('n) - 1"
      using max_card_minus det_coeff_poly_mat(3)[of ?B'] B'_eq
      by auto
  } note deg_det_B' = this 
  
  let ?f_cofactor = "\<lambda> i j. degree (transpose (\<chi> i. vec_lambda (cofactor ?B i)) $ i $ j)"
  
  { fix i j :: "'n::finite"
    assume a0: "CARD('n::finite) = 1"
    moreover then have *: "{undefined::'n::finite} = UNIV"
      by (simp add: a0 card_eq_UNIV_imp_eq_UNIV)  
    moreover have eq: "\<And>P. (\<forall>i::'n. P i) \<longleftrightarrow> P undefined"
      using ball_UNIV[where 'a='n] unfolding *[symmetric] by simp
    ultimately have **: "i = j \<and> j = (undefined::'n::finite)" by auto 
     
    have "degree(det (minorM ?B i j)) = 0"
      using det_coeff_poly_mat(3)[of "minorM ?B i j"]
      by(simp add: det_def minorM_def mat_def mat2matofpoly_def *[symmetric] ** cong del: if_cong)        
  } note trivial_case = this
  
  then have "maxdegM (transpose (cofactorM ?B)) \<ge> card ?U - 1"
    using deg_det_B'(1) zero_less_card_finite[where 'a='n]
    by(cases "CARD('n) = Suc 0")
      (fastforce simp add: cofactorM_def maxdegM_eq_range Max_ge_iff
       transpose_def cofactor_def[of ?B] gr0_conv_Suc simp del: zero_less_card_finite)+
  
  also have "maxdegM (transpose (cofactorM ?B)) \<le> card ?U - 1"
    using deg_det_B'(1) deg_det_B'(2) trivial_case  
    using full_SetCompr_eq[of "\<lambda> (i, j) \<Rightarrow> ?f_cofactor i j"]
    by(simp_all add: transpose_def cofactor_def[of ?B] maxdegM_def cofactorM_def)
      (metis le0 le_refl less_le one_le_card_finite )

  finally show "maxdegM (transpose (cofactorM (mat (monom 1 (Suc 0)) - mat2matofpoly A))) 
  = CARD('n) - 1"
    using dual_order.antisym by simp
qed  

text{* Evaluation of polynomials as formalised in HOL/Library/Polynomial.thy assumes that
   the point at which evaluation happens is of the same type as the coefficients. In the
   present setting something more general is needed.

   Also, the following cannot be used as its reordering assumes working in a commutative setting 
   definition poly\_mat where @{term "poly_mat = poly_rec (\<lambda>x. 0) (\<lambda>a p f x. mat a + x * f x)"}
   

   Therefore, the following definition is made:

   evaluate a polynomial with coefficients in 'a on a matrix over 'a
*}
definition evalmat :: "'a\<Colon>comm_ring_1 poly \<Rightarrow> 'a^'n^'n \<Rightarrow> 'a^'n^'n" where
  "evalmat P A = (\<Sum> i \<in> { n\<Colon>nat . n \<le> ( degree P ) } . (coeff P i) *ss (matpow A i) )"

theorem Cayley_Hamilton:
  fixes A :: "'a::comm_ring_1^'n\<Colon>finite^'n"
  shows "evalmat (charpoly A) A = 0"
proof-

  let ?A = "mat2matofpoly A"
  let ?I = "mat (monom 1 1)"

  def n == "Suc (maxdegM (adjugate (?I - ?A)))"
  then have n_gt_0: "0 < n"
    by auto
  then have [simp]: "\<not> n \<le> n - Suc 0"
    by auto
    
  from poly_basis obtain B where Pred: 
  "adjugate (?I - ?A) = (\<Sum> i \<le> n - 1 . monom 1 i *ss mat2matofpoly (B i))"
    using n_def by auto  

  let ?B = "\<lambda>i. mat2matofpoly (B i)"
  
  txt{* B\_mat is a matrix, while B is a function that returns a matrix ) *}
  def B_mat == "\<Sum> i \<le> n - 1 . monom 1 i *ss ?B i"

  have charpoly_aux: "degree (charpoly A) = n" "coeff (charpoly A) n = 1"
    using coeff_charpoly_xn_is_one[of A] maxdeg_cofactorM[of A]  n_def
    by (simp_all add: adjugate_def) 

  have 1: "{Suc 0..n - Suc 0} \<inter> {i. i \<le> n} \<inter> Collect (op \<le> n) = {}"
    by auto

  let ?M = "\<lambda>i B. monom 1 i *ss B"
  have "mat (charpoly A) = det (?I - ?A) *ss mat 1" 
    by (simp add: charpoly_def mat2matofpoly_def scalar_matrix_mult_def mat_def vec_eq_iff)
  also have "\<dots> = (?I - ?A) ** B_mat"
    by (metis adjugate_det_symmetric Pred B_mat_def)
  also have "\<dots> = ?I ** B_mat - ?A ** B_mat"
    unfolding matrix_mult_right_distributes_minus ..
  also have "\<dots> = (\<Sum>i\<le>n - 1. ?M (i + 1) (?B i)) - (\<Sum>i\<le>n - 1 . ?M i (?A ** ?B i))"
    by (simp add: B_mat_def matrix_sum_mult scalar_mat_matrix_mult_left scalar_scalar_mult_assoc 
       mult_monom matrix_scalar_assoc)
  also have "(\<Sum>i\<le>n - 1. ?M (i + 1) (?B i)) = (\<Sum> i\<in>insert (n - 1) {..< n - 1} . ?M (i + 1) (?B i))"
    by (intro setsum.cong) auto
  also have "\<dots> = (\<Sum>i<n - 1. ?M (i + 1) (?B i)) + ?M n (?B (n - 1))"
    by (simp add: n_def)
  also have "(\<Sum>i\<le>n - 1. ?M i (?A ** ?B i)) = (\<Sum>i\<in>insert 0 {1 .. n - 1} . ?M i (?A ** ?B i))"
    by (intro setsum.cong) auto
  also have "\<dots> = (\<Sum>i=1..n - 1. ?M i (?A ** ?B i)) + ?A ** ?B 0"
    by (simp add: scalar_matrix_mult_monom)
  also have "(\<Sum>i\<in>{1..n - 1}. ?M i (?A ** ?B i)) = (\<Sum>i<n - 1. ?M (i + 1) (?A ** ?B (i + 1)))"
    by (rule setsum.reindex_bij_witness[where i="\<lambda>x. x + 1" and j="\<lambda>x. x - 1"]) auto
  also have "((\<Sum>i<n - 1. ?M (i + 1) (?B i)) + ?M n (?B (n - 1))) -
    ((\<Sum>i<n - 1. ?M (i + 1) (?A ** ?B (i + 1))) + ?A ** ?B 0) =
    - (?A ** ?B 0) + (\<Sum>i<n - 1. ?M (i + 1) (?B i - ?A ** ?B (i + 1))) + ?M n (?B (n - 1))"
    by (simp add: scalar_minus_ldistrib setsum_subtractf scalar_minus_left)
  also have "(\<Sum>i<n - 1. ?M (i + 1) (?B i - ?A ** ?B (i + 1))) =
      (\<Sum>i=1..n - 1. ?M i (mat2matofpoly (B (i - 1) - A ** (B i))))" 
    by (rule setsum.reindex_bij_witness[where i="\<lambda>x. x - 1" and j="\<lambda>x. x + 1"])
       (auto simp: mat2matofpoly_mult mat2matofpoly_simps)
  finally have *: "mat (charpoly A) =
    - (?A ** ?B 0) +
    (\<Sum>i = 1..n - 1. ?M i (mat2matofpoly (B (i - 1) - A ** B i))) +
    ?M n (mat2matofpoly (B (n - 1)))" .

  have coeff_top: "B (n - 1) = coeffM (mat (charpoly A)) n"          
    using n_gt_0 *
    by(simp_all add: coeffM_simps coeffM_monom_mult coeffM_mat2matofpoly mat2matofpoly_mult
    coeffM_setsum if_distrib[where f="\<lambda>x. x * y" for y] setsum.If_cases 1)
        
  { fix i
    have "coeffM (mat (charpoly A)) i = (if \<not> (1 \<le> i) then - (A ** B 0) else
    if i \<le> n - 1 then B (i - 1) - A ** B i else if i = n then mat 1 else 0)"
    proof-
      
      { fix i
        { fix i assume a1: "1 \<le> i" "i \<le> n - 1"
          then have "(\<Sum>j=1..n - 1. coeffM (monom 1 j *ss mat2matofpoly (B (j - 1) - A ** B j)) i) =
            B (i - 1) - A ** B i"
            using if_distrib[where f="\<lambda>x. y * x" for y]
            by (simp add: vec_eq_iff mat2matofpoly_def coeffM_def coeff_setsum 
            scalar_matrix_mult_def if_distrib[where f="\<lambda>x. y * x" for y] setsum.If_cases) }
        moreover
        { fix i assume  "i \<notin> {1..n - 1}"
          then have "(\<Sum>j=1..n - 1. coeffM (monom 1 j *ss mat2matofpoly (B (j - 1) - A ** B j)) i) = 
            (\<Sum>j=1..n - 1. 0)"
            by (intro setsum.cong) (auto simp add: coeffM_monom_mult coeffM_mat2matofpoly) }
        ultimately have x: "(\<Sum>j=1..n - 1. 
        coeffM (monom 1 j *ss mat2matofpoly (B (j - 1) - A ** B j)) i) =
        (if i \<in> {1..n - 1} then B (i - 1) - A ** B i else 0)"
          by simp
       
       have "coeffM (mat (charpoly A)) i = - coeffM (mat2matofpoly A ** mat2matofpoly (B 0)) i +
       (if i \<in> {1..n - 1} then B (i - 1) - A ** B i else 0) +
       coeffM (monom 1 n *ss mat2matofpoly (B (n - 1))) i"
         using n_gt_0
         by(simp only: mat2matofpoly_mult x[symmetric] * coeffM_setsum coeffM_simps)
       }
      
    thus ?thesis  
    using charpoly_aux(2) coeff_top
    by(auto simp add: coeffM_monom_mult mat2matofpoly_mult coeffM_mat2matofpoly coeffM_mat 1
                         one_scalar_mult_mat)
    qed
  } note coeffM_charpoly = this   
    
    
  have zero: "1 < n \<Longrightarrow> - (A ** B 0) + (\<Sum>i=1.. n - 1. (matpow A i ** B (i - 1)) - 
  (matpow A (i + 1) ** B i)) + matpow A n ** B (n - 1) = 0"
  proof-
    assume a0: "1 < n"
    let ?AB = "\<lambda>i j. matpow A i ** B j" 
  
    have "{1..n- 1} = {1} \<union> {2..n- 1}"
      using a0 by auto
  
    then have sum_one: "(\<Sum>i=1..n- 1. ?AB i (i - 1)) = ?AB 1 0 + (\<Sum>i=1..n- 2. ?AB (i + 1) i)"
      using setsum_shift_bounds_cl_nat_ivl[of "\<lambda>i. ?AB i (i- 1)" 1 1 "n- 2"] 
      Suc_diff_Suc[of 1 n] a0   
      by(simp only: Suc_1 one_add_one) simp
   
    have "{1..n- 1} =  {n- 1} \<union> {1..n- 2}"
      using a0 by auto
  
    then have sum_two: "(\<Sum>i=1..n- 1. ?AB (i + 1) i) = ?AB n (n- 1) + (\<Sum>i=1..n- 2. ?AB (i + 1) i)"
      using a0 by(simp add: n_def)
   
    show ?thesis
      using a0 sum_one sum_two
      by (simp only: diff_conv_add_uminus comm_monoid_add_class.setsum.distrib setsum_negf)
         (simp add: matrix_mul_rid) 
  qed

   
  have final: "1 < n \<Longrightarrow> (\<Sum>i\<le> n. coeff (charpoly A) i *ss matpow A i) = 0"
  proof-
    assume a0: "1 < n"

    { fix i assume a1: "1 \<le> i" "i \<le> n - 1"
      then have "coeff (charpoly A) i *ss matpow A i
      = matpow A i ** B (i - 1) - matpow A (Suc i) ** B i"
        using coeffM_charpoly[of i]                  
        by(simp only: matrix_scalar_mat_one[of "matpow A i" "coeff (charpoly A) i", symmetric]
           coeffM_mat[of "charpoly A", symmetric] matrix_mul_assoc[symmetric] 
           matpow_suc[symmetric] matrix_mult_left_distributes_minus[symmetric])
          (simp) } 
     
    moreover have "{i. i \<le> n} = {1.. n - 1}\<union>{n}\<union>{0}"
    by auto

    ultimately show ?thesis 
      using a0 coeff_top coeffM_charpoly[of 0]
      by(simp add: zero[symmetric] atMost_def matrix_mul_rid coeffM_mat 
      matrix_mul_lid setsum_subtractf charpoly_aux(2) one_scalar_mult_mat)
  qed

  txt{* case n > 1 *}
  { assume "degree (charpoly A) = n" "n>1"
    then have ?thesis
      using final by(simp add: evalmat_def atMost_def[of n]) 
  }   
  txt{* case n = 1 *}
  moreover
  { assume a0: "CARD('n::finite) = 1"
    moreover then have *: "{undefined::'n::finite} = UNIV"
      by (simp add: a0 card_eq_UNIV_imp_eq_UNIV)  
    moreover have eq: "\<And>P. (\<forall>i::'n. P i) \<longleftrightarrow> P undefined"
      using ball_UNIV[where 'a='n] unfolding *[symmetric] by simp
    moreover have "{n. n \<le> Suc 0} = {0, 1}"
      by auto
    ultimately have ?thesis
      using coeff_charpoly_xn_is_one[of A]
      apply (simp_all add: mat_def mat2matofpoly_def scalar_matrix_mult_def matrix_matrix_mult_def 
             evalmat_def vec_eq_iff charpoly_def det_one_element_matrix[of _ undefined])
      unfolding *[symmetric]
      apply simp
      done
  }
  ultimately show ?thesis
    using charpoly_aux(1) n_gt_0 coeff_charpoly_xn_is_one
    by(simp, metis less_nat_zero_code less_one linorder_neqE_nat)
qed

text{*
   {\bf Acknowledgements.}

   The authors would like to thank the Isabelle community, and in particular Johannes H{\"o}lzl, 
   Makarius Wenzel, Andreas Lochbihler and Lukas Bulwahn for their helpful support.
*}

end
