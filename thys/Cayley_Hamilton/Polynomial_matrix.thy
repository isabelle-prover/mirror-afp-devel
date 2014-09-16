header {* Matrices of Polynomials\label{sec.mat.poly} *}

theory Polynomial_matrix
imports
  Main
  Polynomial_extension
  Determinants_extension
  Matrices
begin

(* ------------------------------------------------------------------------- *)
subsection {* Basics *}
(* ------------------------------------------------------------------------- *)

definition coeffM_zero :: "'a poly^'n^'n \<Rightarrow> 'a\<Colon>zero^'n^'n" where
  "coeffM_zero A = (\<chi> i j. (coeff (A $ i $ j) 0))"

definition coeffM :: "'a poly^'n^'n \<Rightarrow> nat \<Rightarrow> 'a\<Colon>zero^'n^'n" where
  "coeffM A n = (\<chi> i j. coeff (A $ i $ j) n)"

lemma coeffM_simps:
  "coeffM (A - B) n = coeffM A n - coeffM B n"
  "coeffM (A + B) n = coeffM A n + coeffM B n"
  "coeffM (- A) n = - coeffM A n"
  "coeffM 0 n = 0"
  by (simp_all add: coeffM_def vec_eq_iff)

lemma expand_poly_eqM:
  "A = B \<longleftrightarrow> (\<forall> n. coeffM A n = coeffM B n)"
  by(auto simp add: coeffM_def vec_eq_iff poly_eq_iff)

lemma coeffM_monom_mult:
  fixes A :: "'a\<Colon>comm_ring_1 poly^'n\<Colon>finite^'n"
  shows "coeffM (monom 1 j *ss A) n = (if j \<le> n then coeffM A (n - j) else 0)"
  by (simp add: coeffM_def vec_eq_iff scalar_matrix_mult_def coeff_mult
     if_distrib[where f="\<lambda>x. x * y" for y] setsum.If_cases)
  
lemma coeffM_mat:
  fixes p :: "'a\<Colon>comm_ring_1 poly"
  shows "coeffM (mat p) i = coeff p i *ss mat 1"
  by (simp add: mat_def coeffM_def scalar_matrix_mult_def vec_eq_iff)

lemma coeffM_setsum: "coeffM (\<Sum>i\<in>A. f i) num = (\<Sum>i\<in>A. coeffM (f i) num)"
  by(simp add: coeff_setsum coeffM_def vec_eq_iff)

definition maxdegM :: "'a\<Colon>zero poly^'n^'n \<Rightarrow> nat" 
  where "maxdegM A = Max {degree (A $ i $ j) | i j. True }"

lemma maxdegM_eq_range: "maxdegM A = Max (range (\<lambda>(i, j). degree (A $ i $ j)))"
  by (auto simp add: maxdegM_def intro!: arg_cong[where f=Max])
  
lemma all_degree_smaller:
  "degree (A $ i $ j) \<le> (maxdegM A)"
  using full_SetCompr_eq[of "\<lambda> (i, j) \<Rightarrow> degree (A $ i $ j)"]  
  by(auto simp add: maxdegM_def intro!: Max_ge)

lemma all_degree_smaller_implies_smaller:
  "(\<forall> i j. degree (A $ i $ j) < n) \<Longrightarrow> maxdegM A < n"
  using full_SetCompr_eq[of "\<lambda> (i, j) \<Rightarrow> degree (A $ i $ j)"]
  by(auto simp add: maxdegM_def)

lemma deg_if_monom_minus:
  fixes A :: "'a::comm_ring_1^'n^'n"
  shows "degree ((if i = p i then monom 1 (Suc 0) else 0) - [:A $ i $ p i:])
         = (if i = p i then 1 else 0)"
  using monom_poly_degree_one by auto
  
definition mat2matofpoly :: "'a\<Colon>zero^'n^'n \<Rightarrow> ('a poly)^'n^'n" where
  "mat2matofpoly A = (\<chi> i j. [: A $ i $ j :])"

lemma mat2matofpoly_simps: 
  "mat2matofpoly (A - B) = mat2matofpoly A - mat2matofpoly B"
  "mat2matofpoly (A + B) = mat2matofpoly A + mat2matofpoly B"
  "mat2matofpoly (- A) = - (mat2matofpoly A)"
  "mat2matofpoly 0 = 0"
  by(simp_all add: mat2matofpoly_def vec_eq_iff)

lemma coeffM_mat2matofpoly: "coeffM (mat2matofpoly A) i = (if i = 0 then A else 0)"
  by (auto simp add: coeffM_def mat2matofpoly_def vec_eq_iff gr0_conv_Suc)

lemma mat2matofpoly_mult:
  fixes A B :: "('a\<Colon>comm_ring_1)^'n^'n"
  shows "(mat2matofpoly A) ** (mat2matofpoly B) = mat2matofpoly (A ** B)" 
  unfolding mat2matofpoly_def matrix_matrix_mult_def vec_eq_iff
  using finite[of UNIV]
  by(induct rule: finite_induct)
    (auto)

(* ------------------------------------------------------------------------- *)
subsection {* Euclidean division *}
(* ------------------------------------------------------------------------- *)
 
lemma matofpoly_euclidean_division:
  fixes A :: "('a::comm_ring_1 poly)^'n\<Colon>finite^'n\<Colon>finite"
  assumes *: "maxdegM A >0" 
  shows "\<exists> B :: ('a^'n^'n). \<exists> A'\<in>{ x . maxdegM x < maxdegM A}.    
         A = ( (monom 1 (maxdegM A)) *ss (mat2matofpoly B) ) + A'"
proof-
  have "\<And> i j . \<exists> b a'. degree (A $ i $ j) = maxdegM A \<longrightarrow>
  (degree a' < (degree (A $ i $ j))) \<and>
  (A $ i $ j) = monom b (degree (A $ i $ j)) + a'"
    by (metis assms mem_Collect_eq poly_euclidean_division)
        
  then obtain a' and b where Pred: 
  "\<And> i j. degree (A $ i $ j) = maxdegM A \<Longrightarrow> (degree (a' i j) < maxdegM A) \<and>
  (A $ i $ j) = monom (b i j) (degree (A $ i $ j)) + a' i j"
    by metis  

  def A'_mat \<equiv> "(\<chi> i j. if (degree (A $ i $ j) = maxdegM A) then a' i j else (A $ i $ j))"
  def B_mat \<equiv> "(\<chi> i j. if( degree (A $ i $ j) = maxdegM A) then b i j else 0)"
   
  have "\<And>i j. B_mat $ i $ j \<noteq> 0 \<longrightarrow> b i j \<noteq> 0"
       "\<And>i j. degree (A'_mat $ i $ j) < maxdegM A"
       "\<And>i j. A $ i $ j = monom (B_mat $ i $ j) (degree (A $ i $ j)) + A'_mat $ i $ j"
    using Pred
    by(simp_all add: all_degree_smaller le_neq_implies_less A'_mat_def B_mat_def )
      
  then obtain A' B where Pred2: "\<And> i j . ((B $ i $ j) \<noteq> 0 \<longrightarrow> (B_mat $ i $ j)\<noteq> 0) \<and>   
  (degree (A' $ i $ j) < maxdegM A) \<and>  
  (A $ i $ j) = monom (B $ i $ j) (degree (A $ i $ j)) + A' $ i $ j"
    by blast
    
  show ?thesis unfolding vec_eq_iff 
    using B_mat_def Pred2 
    by(simp add: scalar_matrix_mult_def mat2matofpoly_def)
      (metis (erased, hide_lams) all_degree_smaller_implies_smaller[of A' "maxdegM A"] 
       monom_eq_0 smult_monom monoid_mult_class.mult.right_neutral) 
qed
  

(* ------------------------------------------------------------------------- *)
subsection {* The characteristic polynomial *}
(* ------------------------------------------------------------------------- *)

text{* The characteristic polynomial of a square matrix is defined as follows: *}
definition "charpoly A = det (mat (monom 1 (Suc 0)) - mat2matofpoly A)"

text{* First we prove an auxiliary lemma that will later be used for analysing
   the degree of the characteristic polynomial via the Leibniz formula
   for the determinant. The lemma describes the degree and highest coefficient
   of a polynomial obtained as determinant of a matrix of polynomials (via the
   Leibniz formula). *}

lemma det_coeff_poly_mat:
  fixes A :: "'a\<Colon>comm_ring_1 poly^'n\<Colon>finite^'n"
  defines 
     Sn: "Sn \<equiv> {p . p permutes (UNIV\<Colon>'n\<Colon>finite set)}"
  and m: "m \<equiv> Max { (\<Sum>i\<in>(UNIV\<Colon>'n\<Colon>finite set). degree (A $ i $ p i))| p. p permutes (UNIV\<Colon>'n set)}"
  shows 
  "p\<in>Sn \<Longrightarrow> ((\<forall>p0\<in>Sn. degree (\<Prod>i\<in>(UNIV\<Colon>'n\<Colon>finite set). A $ i $ p0 i) = m \<longrightarrow> p0 = p) 
                    \<and> degree (\<Prod>i\<in>(UNIV\<Colon>'n set). A $ i $ p i) = m) \<Longrightarrow> degree (det A) = m"
        
  "p\<in>Sn \<Longrightarrow> ((\<forall>p0\<in>Sn. degree (\<Prod>i\<in>(UNIV\<Colon>'n\<Colon>finite set). A $ i $ p0 i) = m \<longrightarrow> p0 = p) 
             \<and> degree (\<Prod>i\<in>(UNIV\<Colon>'n set). A $ i $ p i) = m) \<Longrightarrow> coeff (det A) (degree (det A)) =
            of_int (sign p) * (\<Prod>i\<in>(UNIV\<Colon>'n set). coeff (A $ i $ p i) (degree (A $ i $ p i)))"
          
  "degree(det A) \<le> m"  
proof-
  let ?U = "UNIV\<Colon>'n\<Colon>finite set"
  let ?Sn = "{p. p permutes ?U}"

  let ?m = "Max { \<Sum>i\<in>?U. degree (A $ i $ p i) | p. p permutes ?U}"
  let ?f = "\<lambda>p. \<Prod>i\<in>?U. A $ i $ p i"
  
  have p: "Sup ((\<lambda>p. degree(?f p)) ` ?Sn) \<le> Sup ((\<lambda>p. (\<Sum>i\<in>?U. degree (A $ i $ p i))) ` ?Sn)"
    unfolding Sup_image_eq
    by(intro cSUP_subset_mono)
      (simp_all add: exI[of _ id] permutes_id degree_setprod_le)

  then show "degree(det A) \<le> m"
    using degree_setsum_le_max[of "\<lambda>p. of_int (sign p) * (\<Prod>i\<in>?U. A $ i $ p i)" ?Sn] 
    by(simp add: m sign_permut det_def Sup_nat_def image_Collect) 
    
  
  { fix p0 :: "'n::finite \<Rightarrow> 'n"
    assume a: "p0 permutes ?U"
              "\<forall>pp0 \<in> ?Sn. degree (\<Prod>i\<in>?U. A $ i $ pp0 i) = ?m \<longrightarrow> pp0 = p0"
              "degree (\<Prod>i\<in>?U. A $ i $ p0 i) = ?m"
    
    let ?f = "\<lambda>p. (\<Prod>i\<in>?U. A $ i $ p i)"
    let ?ff = "\<lambda>p. of_int (sign p) * ?f p"
    let ?Sn_p = "?Sn - {p0}"
    
    let ?p = "of_int (sign p0) * ?f p0"
    let ?q = "(\<Sum>p\<in>?Sn - {p0}. of_int (sign p) * ?f p)"
    
    have th6b: "(\<Sum>p\<in>?Sn. ?ff p) = (\<Sum>p\<in>{p0}. ?ff p) + (\<Sum>p\<in>(?Sn - {p0}). ?ff p)"
      by (subst setsum.union_disjoint[symmetric])
         (auto intro!: setsum.cong a)

    { assume a2: "?Sn_p \<noteq> {}"
      let ?S = "{degree (?f p) | p. p\<in>?Sn_p}"
      
      have "Max ?S \<le> Max{ degree (?f p) | p. p permutes ?U}"
        using a2 by (auto intro!: Max_mono)
      
      also have "Max ?S \<noteq> ?m"
        using Max_in[of ?S] a(2) a2 
        by force
      
      ultimately have "degree ?q < ?m"
        using p degree_setsum_le_max[of ?ff ?Sn_p]
        by(simp add: Sup_nat_def image_Collect sign_permut)
    } note deg_q_smaller_m = this 
   
    have coeffs: "coeff ?p (degree(?p + ?q)) + coeff ?q (degree(?p + ?q)) = coeff ?p (degree ?p)"
      by (cases "?Sn_p = {}")
         (auto simp add: a(3) coeff_eq_0 degree_add_eq_left deg_q_smaller_m sign_permut
               simp del: Diff_eq_empty_iff)
         
    let ?fp0 = "\<lambda>i. (A $ i $ p0 i)"

    have "(\<Sum>i\<in>?U. degree (?fp0 i)) = degree (\<Prod>i\<in>?U. ?fp0 i)"
      by(intro dual_order.antisym degree_setprod_le)
        (auto simp add: a(1) a(3) intro!: Max_ge)
         
    then have "coeff ?p (degree ?p) = of_int (sign p0) * (\<Prod>i\<in>?U. coeff (?fp0 i) (degree (?fp0 i)))"
    by(simp add: coeff_mult_setprod_setsum[of ?fp0 ?U, symmetric] sign_def)
    
    then have 1: "coeff (det A) (degree (det A)) = 
                  of_int (sign p0) * (\<Prod>i\<in>?U. coeff (?fp0 i) (degree (?fp0 i)))"
         and 2: "degree (det A) = ?m"
      apply(simp_all add: coeffs det_def th6b)
      apply(cases "?Sn_p = {}")
      apply(simp_all add:sign_permut a(3) degree_add_eq_left deg_q_smaller_m del: Diff_eq_empty_iff)
      done
    note 1 2
  } 
  thus "p\<in>Sn \<Longrightarrow> ((\<forall>p0 \<in> Sn. degree (\<Prod>i\<in>?U. A $ i $ p0 i) = m \<longrightarrow> p0 = p)
        \<and> degree (\<Prod>i\<in>?U. A $ i $ p i) = m) \<Longrightarrow> degree(det A) = m"
       
       "p\<in>Sn \<Longrightarrow> ((\<forall>p0 \<in> Sn. degree (\<Prod>i\<in>?U. A $ i $ p0 i) = m \<longrightarrow> p0 = p) 
        \<and> degree (\<Prod>i\<in>?U. A $ i $ p i) = m) \<Longrightarrow>        
        coeff (det A) (degree (det A)) =
          of_int (sign p) * (\<Prod>i\<in>?U. coeff (A $ i $ p i) (degree (A $ i $ p i)))"
    using Sn m by fast+ 
qed
 
lemma p_not_id:  
  assumes a1: "p\<noteq>id"
  shows "\<exists>i\<in>(UNIV :: 'n::finite set). i \<noteq> p i" "card {i. i = p i} < CARD('n)"
proof-
  show "\<exists>i\<in>(UNIV :: 'n::finite set). i \<noteq> p i" 
    using a1 by auto
  then show "card {i. i = p i} < CARD('n)"
    by (metis (full_types) UNIV_I finite mem_Collect_eq psubset_card_mono top.not_eq_extremum)
qed   

lemma coeff_charpoly_xn_is_one:
fixes A :: "'a::comm_ring_1^'n\<Colon>finite^'n"
shows "coeff (charpoly A) (card (UNIV\<Colon>'n set)) = 1" 
      "degree (charpoly A) = card (UNIV\<Colon>'n set)" 
proof-
  txt{* charpoly *}
  let ?B = "mat (monom 1 (Suc 0)) - mat2matofpoly A"
  let ?U = "UNIV :: 'n::finite set"
   
  let ?f = "\<lambda>p. \<Sum>i\<in>?U. degree (?B $ i $ p i)" 
  let ?m = "Max {\<Sum>i\<in>?U. degree (?B $ i $ p i) | p. p permutes ?U}"
  let ?mon_A = "\<lambda>i. monom 1 (Suc 0) - [:A $ i $ i:]"
   
  have deg_prod_B_card: "degree (\<Prod>i\<in>?U. ?B $i $ i) = card ?U"
    using coeff_mult_setprod_setsum[of ?mon_A ?U]
    degree_setprod_le[of ?mon_A ?U] le_degree[of "\<Prod>i\<in>?U. ?mon_A i" "card ?U"]
    by(simp add: monom_poly_degree_one mat_def mat2matofpoly_def)
  
  have max_is_id: "Max {?f p | p. p permutes ?U} = ?f id"
    by (intro Max_eqI)
       (auto simp add: mat_def mat2matofpoly_def deg_if_monom_minus monom_poly_degree_one 
             setsum.If_cases intro!: exI[of _ id] card_mono permutes_id cong del: if_cong)
       
  { fix p0
    have "degree (\<Prod>i\<in>?U. ?B $ i $ p0 i) = ?m \<Longrightarrow> p0 = id"
      unfolding max_is_id 
      using degree_setprod_le[of "\<lambda>i.(if i=p0 i then monom 1 (Suc 0) else 0)- [:A $ i $ p0 i:]" ?U]
      p_not_id(2)[of p0] 
      by(auto simp add: mat_def mat2matofpoly_def deg_if_monom_minus setsum.If_cases 
         monom_poly_degree_one)
  } note x = this

  then show "degree (charpoly A) = card ?U"
    using max_is_id det_coeff_poly_mat(1)[of id ?B]
    by(simp add: charpoly_def deg_prod_B_card permutes_id del: vector_minus_component)
      (simp add: mat2matofpoly_def mat_def monom_poly_degree_one)
    
  then show "coeff (charpoly A) (card ?U) = 1"
    using x det_coeff_poly_mat(2)[of id ?B]
    by (simp add: charpoly_def max_is_id deg_prod_B_card permutes_id del: vector_minus_component)
       (simp add: mat2matofpoly_def mat_def sign_id monom_poly_degree_one)
qed  

(* ------------------------------------------------------------------------- *)
subsection {* The basis lemma *}
(* ------------------------------------------------------------------------- *)
   
lemma poly_basis:
  fixes A :: "'a::comm_ring_1 poly^'n\<Colon>finite^'n"
  shows "\<exists> B. A = (\<Sum> i\<le>maxdegM A. monom 1 i *ss mat2matofpoly (B i))"
proof-
  { fix d
    have "\<forall>A. maxdegM A \<le> d \<longrightarrow> ( \<exists> B\<Colon>nat \<Rightarrow> 'a^'n^'n. A =
         (\<Sum>i\<le>maxdegM A. monom 1 i *ss mat2matofpoly (B i)))"
    proof (induct d)
      case 0
      { fix A :: "('a poly)^'n^'n"
        assume caseass: "maxdegM A = 0"

        have "A = mat2matofpoly (coeffM A 0)"
          by(simp add: coeffM_def mat2matofpoly_def vec_eq_iff )
            (metis (erased, hide_lams) caseass all_degree_smaller coeff_pCons_0 degree_pCons_eq_if 
                                       le0 le_antisym nat.distinct(1) pCons_cases)

        hence "\<exists> B\<Colon>(nat \<Rightarrow> 'a^'n^'n). A = (\<Sum>i\<le>maxdegM A. monom 1 i *ss mat2matofpoly (B i))"
          by(auto simp add: caseass scalar_matrix_mult_monom intro!: exI[of _ "\<lambda>x. coeffM A 0"])          
      }
      thus ?case by auto
    next
      case ( Suc n ) note IH = this        
      { fix A :: "'a poly^'n\<Colon>finite^'n"
        assume caseass: "maxdegM A = Suc n"

        from matofpoly_euclidean_division[of A]
        obtain A' B where Pred: "A = monom 1 (maxdegM A) *ss mat2matofpoly B + A'"
                                "maxdegM A' < maxdegM A"
          using caseass by auto
          
        obtain B' where Pred2: "A' = (\<Sum>i\<le> maxdegM A'. monom 1 i *ss mat2matofpoly (B' i))"
          using IH caseass Pred by fastforce

        txt{* aB: combine B and B' *}
        def aB \<equiv> "\<lambda>i. if i \<le> maxdegM A' then B' i else (if i = maxdegM A then B else 0)" 
        let ?MB = "\<lambda>i. monom 1 i *ss mat2matofpoly (aB i)"

        have "A = ?MB (maxdegM A) + (\<Sum>i\<le>maxdegM A'. ?MB i)" 
          using Pred Pred Pred2 
          by (simp add: aB_def cong del: if_cong)

        also have "\<And>i.(i > maxdegM A') \<and> (i < (maxdegM A)) \<Longrightarrow> ?MB i = 0"
          by(simp add: aB_def mat2matofpoly_def scalar_matrix_mult_def zero_vec_def)

        ultimately have "A = ?MB (maxdegM A) + (\<Sum>i=maxdegM A'+1 ..< maxdegM A. ?MB i) +
        (\<Sum>i \<le> maxdegM A'. ?MB i)"
          by simp
        also have "... = (\<Sum>i\<in>{maxdegM A} \<union> {maxdegM A'+1 ..< maxdegM A} \<union> {.. maxdegM A'}. ?MB i)"
          using Pred by (subst setsum.union_disjoint) auto
        also have "{maxdegM A} \<union> {maxdegM A'+1 ..< maxdegM A} \<union> {.. maxdegM A'} = {.. maxdegM A}"
          using Pred by auto
        finally have "A = (\<Sum>i \<le> maxdegM A. ?MB i)" .

        hence "\<exists> B. A = (\<Sum>i\<le> maxdegM A. monom 1 i *ss mat2matofpoly (B i))"
          by auto      
      } 
      then show ?case 
        by(simp add: le_Suc_eq IH)
    qed 
  }
  thus ?thesis by auto
qed

end
