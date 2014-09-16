header {* Determinants\label{sec.det.ext} *}

theory Determinants_extension
imports
  Main
  "~~/src/HOL/Library/Polynomial"  
  "~~/src/HOL/Multivariate_Analysis/Determinants"    
begin

text{* This theory generalises a number of lemmas from HOL/Multivariate\_Analysis/Determinants to
   the case of commutative rings, i.e.~to the type class comm\_ring\_1. To that aim, some auxiliary
   results, in particular on the decomposition of the symmetric group,
   are established in advance. *}

(* ------------------------------------------------------------------------- *)
subsection {* Decomposition of the symmetric group *}                               
(* ------------------------------------------------------------------------- *)

abbreviation fscomp :: "(('b \<Rightarrow> 'c) set) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'c) set)" (infixl "oS" 55) where
  "S oS g \<equiv> (\<lambda>f. f \<circ> g) ` S"

lemma fscomp_singleton: "{ f } oS g = { f o g }"
  by auto

lemma permlem:
  assumes "finite S" "a \<in> S" "b \<in> S" "a \<noteq> b"
  shows "{ p. p permutes S \<and> sign p = -1 } =
         { q. q permutes S \<and> sign q = 1 } oS Fun.swap a b id" (is "?lhs = ?rhs")
proof-
  let ?s = "Fun.swap a b id"
  from permutation_swap_id[of a b] have perms: "permutation ?s"
    by auto
  from assms have spermS: "?s permutes S" 
    by (simp add: permutes_swap_id)
  from assms sign_swap_id[of a b] have signs: "sign ?s = -1" 
    by auto

  have "?lhs \<subseteq> ?rhs"
  proof(rule subsetI)
    fix p assume "p \<in> ?lhs"
    hence caseass: "p permutes S" "sign p = -1" 
      by auto
    let ?q = "p o ?s"
    have qpS: "?q permutes S" 
      by (simp add: caseass permutes_compose spermS)
    have sq1: "sign (?q) = 1"
    proof-
      have "permutation p"
        using caseass assms permutation_permutes  by auto
      hence "sign (?q) = sign p * sign ?s"
        using perms sign_compose[of p ?s] by auto
      with signs caseass show ?thesis
        by simp
    qed
    from qpS sq1 have qinset: "?q \<in> { q. q permutes S \<and> sign q = 1 }"
      by auto
    have qsp: "?q o ?s = p" 
      by (metis comp_swap o_id swap_nilpotent)
    from qsp qinset show "p \<in> ?rhs"
      by (auto simp: image_iff)
  qed

  also have "?rhs \<subseteq> ?lhs"
  proof(rule subsetI)
    fix p assume "p \<in> ?rhs"
    then obtain q where "q \<in> { q. q permutes S \<and> sign q = 1 }" and psq: "p = q o ?s" 
      by auto
    then have qpermS: "q permutes S" and sq1: "sign q = 1"
      by auto
    have ppermS: "p permutes S" using spermS qpermS permutes_compose[of ?s S q] psq
      by auto
    have spm1: "sign p = -1"
    proof-
      have "permutation q"
        using qpermS assms permutation_permutes by auto
      moreover have "sign p = sign (q o ?s)"
        using psq by auto
      ultimately have "sign p = sign(q) * sign(?s)" 
        using perms sign_compose[of q ?s] by auto
      with signs sq1 show ?thesis
        by auto
    qed
    show "p \<in> ?lhs" using ppermS spm1
      by auto
  qed
  
  finally show ?thesis
    by auto 
qed

theorem dec_symgroup:
  assumes "finite S" "a \<in> S" "b \<in> S" "a \<noteq> b"
  shows "{ p. p permutes S } = { q. q permutes S \<and> sign q = 1 } \<union>
                               ( { q. q permutes S \<and> sign q = 1 } oS Fun.swap a b id )"
proof-
  have "\<And> p. sign p = 1 \<or> sign p = -1"
    by (simp add: sign_def)
  with set_eq_iff have "{ p. p permutes S } =
                        { p. p permutes S \<and> sign p = 1 } \<union> { p. p permutes S \<and> sign p = -1 }"
    by auto
  with permlem[of S a b] assms show ?thesis
    by simp
qed

theorem dec_symgroup_disjoint:
  assumes "finite S" "a \<in> S" "b \<in> S" "a \<noteq> b"
  shows "{ q. q permutes S \<and> sign q = 1 } \<inter>
         ( { p. p permutes S \<and> sign p = 1 } oS Fun.swap a b id ) = {}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain q p where eq: "q permutes S" "sign q = 1" 
  "p permutes S" "sign p = 1" "q = p o Fun.swap a b id"
    by auto
  hence "sign q = -1"
    by (metis assms(1) assms(4) evenperm_comp evenperm_swap
        permutation_permutes permutation_swap_id sign_def)
  hence "sign q \<noteq> 1"
    by auto
  thus "False"
    using eq by auto
qed

(* ------------------------------------------------------------------------- *)
subsection {* Auxiliary lemma concerning big operators *}                        
(* ------------------------------------------------------------------------- *)

lemma setprod_remove2:
  assumes "finite A" "a \<in> A" "b \<in> A" "a \<noteq> b"
  shows "setprod f A = f a * f b * setprod f (A - {a,b})"
  using setprod.remove[of "A - {a}" b f] setprod.remove[of "A" a f] assms
  by (simp add: ac_simps Diff_insert2[symmetric])

(* ------------------------------------------------------------------------- *)
subsection {* Generalisations of / additions to properties of determinants *}
(* ------------------------------------------------------------------------- *)

text {* This subsection collects generalisations and additions to the library on determinants. A
   generalization of a lemma XYZ in the library is indicated by giving it the name my\_XYZ here. *} 

lemma my_det_identical_rows:
  fixes A :: "'a::comm_ring_1^'n^'n" and i j :: "'n"
  assumes ij: "i \<noteq> j" and r: "row i A = row j A"
  shows "det A = 0"
proof-
  let ?S = "(UNIV::'n set)"
  let ?Sn = "{ p. p permutes ?S }"
  let ?An = "{ q. q permutes ?S \<and> sign q = 1 }"
  let ?\<tau> = "Fun.swap i j id"
  have dec: "?Sn = ?An \<union> (?An oS ?\<tau>)"
    using assms dec_symgroup[of ?S i j] by auto
  have disj: "?An \<inter> (?An oS ?\<tau>) = {}" 
    using assms dec_symgroup_disjoint[of ?S i j] by auto

  have aux_even2: "\<And> p. (\<Prod>k\<in>UNIV. A $ k $ p k) =
    A $ i $ p i * A $ j $ p j * (\<Prod>k\<in>UNIV-{i,j}. A $ k $ p k)"
    by (rule setprod_remove2)
       (simp_all add: ij) 
    
  have aux_ij: "\<And> k. A $ i $ k = A $ j $ k"
    using r row_def[of i A] row_def[of j A] by (metis vec_lambda_beta)

  txt{* main calculation *}
  have "det A = (\<Sum>p\<in> ?Sn. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i) )"
    by (simp add: det_def)
  also have "\<dots> = (\<Sum>p\<in> ?An. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i) ) 
                + (\<Sum>p\<in>( ?An oS ?\<tau>). of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i) )"
    using dec disj setsum.union_disjoint[of "?An" "?An oS ?\<tau>" "\<lambda> p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)"]
    by auto
  also have "(\<Sum>p\<in> ?An. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i) )
           = (\<Sum>p\<in> ?An. \<Prod>i\<in>UNIV. A $ i $ p i )"
    by simp
  also have "(\<Sum>p\<in>( ?An oS ?\<tau> ). of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i) )
         = - (\<Sum> q \<in> ?An. \<Prod>i\<in>UNIV. A $ i $ (q o ?\<tau>) i)"
  proof-
    let ?f = "(\<lambda> p. p o ?\<tau>)"
    have f_inj_on_An: "inj_on ?f ?An"
    by(rule inj_onI)
      (metis comp_id comp_swap swap_nilpotent)
    have sign: "\<And> q. q \<in> ?An \<Longrightarrow> sign (q o ?\<tau>) = - 1"
    proof-
      fix q assume ass: "q \<in> ?An"
      hence "permutation q"
        using permutation_permutes[of q] by auto
      then have "sign (q o ?\<tau>) = sign q * sign ?\<tau>" 
        using sign_compose[of q ?\<tau>] by (simp add: permutation_swap_id)
      thus "sign (q o ?\<tau>) = - 1"
        using ass sign_swap_id[of i j] ij by auto
    qed

    have "(\<Sum>p\<in>( ?An oS ?\<tau> ). of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i) )
      = (\<Sum> q \<in> ?An. of_int(sign (q o ?\<tau>)) * (\<Prod>i\<in>UNIV. A $ i $ (q o ?\<tau>) i) ) "
      using f_inj_on_An setsum.reindex[of "?f" "?An"
        "\<lambda> p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)"] by simp
    also have "\<dots> = (\<Sum> q \<in> ?An. (- 1) * (\<Prod>i\<in>UNIV. A $ i $ (q o ?\<tau>) i) )" 
      using sign setsum.cong by auto
    finally show ?thesis
      by (metis (no_types) comm_ring_1_class.normalizing_ring_rules(1)  setsum_right_distrib)
  qed
  also have "(\<Sum>p\<in>{q. q permutes UNIV \<and> sign q = 1}. \<Prod>i\<in>UNIV. A $ i $ p i) +
  - (\<Sum>q | q permutes UNIV \<and> sign q = 1. \<Prod>ia\<in>UNIV. A $ ia $ (q \<circ> Fun.swap i j id) ia) = (\<Sum>p\<in>?An. \<Prod>i\<in>UNIV. A $ i $ p i) - (\<Sum>p\<in>?An. \<Prod>i\<in>UNIV. A $ i $ (p o ?\<tau>) i)"
    by simp
  also have "\<dots> = (\<Sum>p\<in>?An. (\<Prod>k\<in>UNIV. A $ k $ p k) - (\<Prod>k\<in>UNIV. A $ k $ (p o ?\<tau>) k))"
    using setsum_subtractf[of "\<lambda> p. \<Prod>i\<in>UNIV. A $ i $ p i" "\<lambda> p. \<Prod>i\<in>UNIV. A $ i $ (p o ?\<tau>) i" "?An"] 
    by presburger
  also have "\<dots> = (\<Sum>p\<in>?An. (A $ i $ p i) * (A $ j $ p j) * (\<Prod> k \<in> UNIV - {i,j}. A $ k $ p k) -
    (A $ j $ p j) * (A $ i $ p i) * (\<Prod> k \<in> UNIV - {i,j}. A $ k $ p k))"
    using aux_ij aux_even2 
    by simp
    
  finally show ?thesis by auto
qed

lemma my_det_row_operation:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes ij: "i \<noteq> j"
  shows "det (\<chi> k. if k = i then row i A + c *s row j A else row k A) = det A"
  (is "?lhs = ?rhs")
proof-
  let ?Z = "(\<chi> k. if k = i then row j A else row k A)"
  have aux1: "row i ?Z = row j ?Z" 
    by (vector row_def)
  have "(\<chi> k. if k = i then row i A else row k A) = A"
    by (vector row_def)
  hence "?lhs = det A + det (\<chi> k. if k = i then c *s row j A else row k A)"
    by (simp add: det_row_add)
  also have "\<dots> = det A + c * det ?Z"
    by (simp add: det_row_mul)
  finally show ?thesis
    by (simp add: my_det_identical_rows[OF ij aux1])
qed

lemma my_det_identical_columns:
  fixes A :: "'a::comm_ring_1^'n^'n" and i j :: "'n"
  assumes a: "i \<noteq> j" "column i A = column j A"
  shows "det A = 0"
  by(subst det_transpose[symmetric])
    (metis row_transpose a(2) my_det_identical_rows[OF a(1)])

lemma det_col_mul:
  shows "det (\<chi> i j. if j = k then c * (A $ i $ j) else A $ i $ j) = c * det A"
  (is "det ?lm = c * det ?rm")
proof-
  { fix A :: "'a::comm_ring_1^'n^'n" and l c
    have "det (\<chi> i j. if i = l then c * (A $ j $ i) else A $ j $ i) = c * det A" 
    (is "det ?lm = ?rm" )
    proof-
    { fix A :: "'a::comm_ring_1^'n^'n" and c
      have "det (\<chi> i j. if i = l then c * (A $ i $ j) else A $ i $ j) = c * det A"
      proof-
        have "(\<chi> i j. if i = l then (c *s (A $ i)) $ j else (A $ i $ j))
        = (\<chi> i. if i = l then (c *s (A $ i)) else (A $ i))"
          by (simp add: vec_eq_iff)
        moreover have "det (\<chi> i. if i = l then (c *s (A $ i)) else (A $ i)) = c * det( A )"
          by(simp_all add: Determinants.det_row_mul[of l c] vec_lambda_eta[of A])
        ultimately show ?thesis
          by(simp only: vector_smult_component[of c, symmetric])
      qed }
    moreover have "det (\<chi> i j. if i = l then c * (transpose A $ i $ j) else transpose A $ i $ j) = 
    det (\<chi> i j. if i = l then c * (A $ j $ i) else A $ j $ i)"
      by(simp add: transpose_def cong del: if_weak_cong)
    ultimately show ?thesis
      by (metis det_transpose) 
  qed }
  thus ?thesis 
  by (subst det_transpose[symmetric]) (simp add: transpose_def)
qed

lemma det_linear_column_setsum:
  assumes "finite S"
  fixes A :: "'a::comm_ring_1^'n^'n" and b :: "'n \<Rightarrow> 'a^'n" and k :: "'n"
  shows "det ( \<chi> r c . if c = k then (\<Sum> j \<in> S. b j $ r) else A $ r $ c ) =
  (\<Sum>j\<in>S. det( \<chi> r c . if c = k then b j $ r else A $ r $ c ))"
proof-
  { fix A k 
    have "det( \<chi> i c . if i = k then ( \<Sum> j \<in> S . b j $ c ) else A $ i $ c )  
    = (\<Sum>j\<in>S. det(\<chi> i c. if i = k then b j $ c else A $ i $ c) )" (is "?left = ?r")
    proof-
      have "\<And>j. (\<chi> i . if i = k then ( b j) else A $ i ) 
      = (\<chi> i c . if i = k then ( b j $ c ) else A $ i $ c)"
        by (simp add: vec_eq_iff)
      moreover have "det( \<chi> i . if i = k then setsum b S else A $ i) = ?left"
        by(subst Cart_lambda_cong)
          (auto simp add: setsum_eq vec_lambda_eta)
      ultimately show ?thesis 
        using det_linear_row_setsum[of "S" "k" "\<lambda> i. b" "\<lambda> s. A $ s"]
        by auto
    qed
  } note 1 = this

  have "det (transpose ( \<chi> r c . if c = k then (\<Sum> j \<in> S. b j $ r) else A $ r $ c )) =
  (\<Sum> j \<in> S. det(transpose ( \<chi> r c . if c = k then b j $ r else A $ r $ c )))"
    using 1[of _ "transpose A"]
    by(simp only: assms transpose_def vec_lambda_inverse[OF UNIV_I])
      
  thus ?thesis
    by (simp add: det_transpose)
qed

lemma det_one_element_matrix:
  fixes A :: "'a::comm_ring_1 poly^'n\<Colon>finite^'n" 
  assumes *: "card(UNIV :: 'n set) = 1"
  shows "det A = A $ x $ x"
proof -
  have 1: "{x} = UNIV"
    using * card_eq_UNIV_imp_eq_UNIV finite_code
    by (metis Nat.add_0_right Suc_eq_plus1 card_0_eq card_insert_disjoint empty_iff add.commute)
  show ?thesis
    unfolding det_def 1[symmetric]
    by (simp add: sign_id)
qed

end
