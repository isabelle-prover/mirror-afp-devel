(*
  Authors: J. Divasón, R. Thiemann, A. Yamada, O. Kunčar
*)

subsection \<open>Transfer rules to convert theorems from JNF to HMA and vice-versa.\<close>

theory HMA_Connect
imports 
  "../Jordan_Normal_Form/Spectral_Radius" 
  "../Echelon_Form/Code_Cayley_Hamilton" (* defines matpow *)
  Bij_Nat
  Cancel_Card_Constraint
  "~~/src/HOL/Eisbach/Eisbach" 
begin

text \<open>Prefer certain constants and lemmas without prefix.\<close>

hide_const Cayley_Hamilton.C

hide_const (open) Matrix.mat
hide_const (open) Matrix.row
hide_const (open) Determinant.det

lemmas mat_def = Cartesian_Euclidean_Space.mat_def
lemmas det_def = Determinants.det_def
lemmas row_def = Cartesian_Euclidean_Space.row_def

notation vec_index (infixl "$v" 90)
notation vec_nth (infixl "$h" 90)


text \<open>Forget that @{typ "'a mat"}, @{typ "'a Matrix.vec"}, and @{typ "'a poly"} 
  have been defined via lifting\<close>


(* TODO: add to end of matrix theory, stores lifting + transfer setup *)
lifting_forget vec.lifting
lifting_forget mat.lifting

lifting_forget poly.lifting

text \<open>Some notions which we did not find in the HMA-world.\<close>
definition eigen_vector :: "'a::comm_ring_1 ^ 'n ^ 'n \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigen_vector A v ev = (v \<noteq> 0 \<and> A *v v = ev *s v)"

definition eigen_value :: "'a :: comm_ring_1 ^ 'n ^ 'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigen_value A k = (\<exists> v. eigen_vector A v k)"

definition spectral_radius :: "complex ^ 'n ^ 'n \<Rightarrow> real" where
  "spectral_radius A = Max { norm ev | v ev. eigen_vector A v ev}"

definition vec_elements_h :: "'a ^ 'n \<Rightarrow> 'a set" where
  "vec_elements_h v = range (vec_nth v)"

lemma vec_elements_h_def': "vec_elements_h v = {v $h i | i. True}"
  unfolding vec_elements_h_def by auto

definition mat_elements_h :: "'a ^ 'nc ^ 'nr \<Rightarrow> 'a set" where
  "mat_elements_h A = range (\<lambda> (i,j). A $h i $h j)"

lemma mat_elements_h_def': "mat_elements_h A = {A $h i $h j | i j. True}"
  unfolding mat_elements_h_def by auto

definition map_vector :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ^'n \<Rightarrow> 'b ^'n" where 
  "map_vector f v \<equiv> \<chi> i. f (v $h i)"

definition map_matrix :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ^ 'n ^ 'm \<Rightarrow> 'b ^ 'n ^ 'm" where 
  "map_matrix f A \<equiv> \<chi> i. map_vector f (A $h i)"

definition normbound :: "'a :: real_normed_field ^ 'nc ^ 'nr \<Rightarrow> real \<Rightarrow> bool" where
  "normbound A b \<equiv> \<forall> x \<in> mat_elements_h A. norm x \<le> b"

lemma spectral_radius_ev_def: "spectral_radius A = Max (norm ` (Collect (eigen_value A)))"
  unfolding spectral_radius_def eigen_value_def[abs_def]
  by (rule arg_cong[where f = Max], auto) 

lemma mat_elements: "mat_elements A = {A $$ (i,j) | i j. i < dim\<^sub>r A \<and> j < dim\<^sub>c A}"
  unfolding mat_elements_def by force

definition vec_elements :: "'a Matrix.vec \<Rightarrow> 'a set"
  where "vec_elements v = set [v $ i. i <- [0 ..< dim\<^sub>v v]]"

lemma vec_elements: "vec_elements v = { v $ i | i. i < dim\<^sub>v v}"
  unfolding vec_elements_def by auto


(* TODO: restore a bundle, for e.g., for matrix_impl *)
context includes vec.lifting 
begin
end

definition from_hma\<^sub>v :: "'a ^ 'n  \<Rightarrow> 'a Matrix.vec" where
  "from_hma\<^sub>v v = Matrix.vec CARD('n) (\<lambda> i. v $h from_nat i)"

definition from_hma\<^sub>m :: "'a ^ 'nc ^ 'nr \<Rightarrow> 'a Matrix.mat" where
  "from_hma\<^sub>m a = Matrix.mat CARD('nr) CARD('nc) (\<lambda> (i,j). a $h from_nat i $h from_nat j)"

definition to_hma\<^sub>v :: "'a Matrix.vec \<Rightarrow> 'a ^ 'n" where
  "to_hma\<^sub>v v = (\<chi> i. v $v to_nat i)"

definition to_hma\<^sub>m :: "'a Matrix.mat \<Rightarrow> 'a ^ 'nc  ^ 'nr " where
  "to_hma\<^sub>m a = (\<chi> i j. a $$ (to_nat i, to_nat j))"

declare vec_lambda_eta[simp]

lemma to_hma_from_hma\<^sub>v[simp]: "to_hma\<^sub>v (from_hma\<^sub>v v) = v"
  by (auto simp: to_hma\<^sub>v_def from_hma\<^sub>v_def to_nat_less_card)

lemma to_hma_from_hma\<^sub>m[simp]: "to_hma\<^sub>m (from_hma\<^sub>m v) = v"
  by (auto simp: to_hma\<^sub>m_def from_hma\<^sub>m_def to_nat_less_card)

lemma from_hma_to_hma\<^sub>v[simp]:
  "v \<in> carrier\<^sub>v (CARD('n)) \<Longrightarrow> from_hma\<^sub>v (to_hma\<^sub>v v :: 'a ^ 'n) = v"
  by (auto simp: to_hma\<^sub>v_def from_hma\<^sub>v_def to_nat_from_nat_id)

lemma from_hma_to_hma\<^sub>m[simp]:
  "A \<in> carrier\<^sub>m (CARD('nr)) (CARD('nc)) \<Longrightarrow> from_hma\<^sub>m (to_hma\<^sub>m A :: 'a ^ 'nc  ^ 'nr) = A"
  by (auto simp: to_hma\<^sub>m_def from_hma\<^sub>m_def to_nat_from_nat_id)

lemma from_hma\<^sub>v_inj[simp]: "from_hma\<^sub>v x = from_hma\<^sub>v y \<longleftrightarrow> x = y"
  by (intro iffI, insert to_hma_from_hma\<^sub>v[of x], auto)

lemma from_hma\<^sub>m_inj[simp]: "from_hma\<^sub>m x = from_hma\<^sub>m y \<longleftrightarrow> x = y"
  by(intro iffI, insert to_hma_from_hma\<^sub>m[of x], auto)

definition HMA_V :: "'a Matrix.vec \<Rightarrow> 'a ^ 'n  \<Rightarrow> bool" where 
  "HMA_V = (\<lambda> v w. v = from_hma\<^sub>v w)"

definition HMA_M :: "'a Matrix.mat \<Rightarrow> 'a ^ 'nc  ^ 'nr  \<Rightarrow> bool" where 
  "HMA_M = (\<lambda> a b. a = from_hma\<^sub>m b)"

definition HMA_I :: "nat \<Rightarrow> 'n :: finite \<Rightarrow> bool" where
  "HMA_I = (\<lambda> i a. i = to_nat a)"

context includes lifting_syntax
begin

lemma Domainp_HMA_V [transfer_domain_rule]: 
  "Domainp (HMA_V :: 'a Matrix.vec \<Rightarrow> 'a ^ 'n \<Rightarrow> bool) = (\<lambda> v. v \<in> carrier\<^sub>v (CARD('n )))"
  by(intro ext iffI, insert from_hma_to_hma\<^sub>v[symmetric], auto simp: from_hma\<^sub>v_def HMA_V_def)

lemma Domainp_HMA_M [transfer_domain_rule]: 
  "Domainp (HMA_M :: 'a Matrix.mat \<Rightarrow> 'a ^ 'nc  ^ 'nr  \<Rightarrow> bool) 
  = (\<lambda> A. A \<in> carrier\<^sub>m CARD('nr) CARD('nc))"
  by (intro ext iffI, insert from_hma_to_hma\<^sub>m[symmetric], auto simp: from_hma\<^sub>m_def HMA_M_def)

lemma Domainp_HMA_I [transfer_domain_rule]: 
  "Domainp (HMA_I :: nat \<Rightarrow> 'n :: finite \<Rightarrow> bool) = (\<lambda> i. i < CARD('n))" (is "?l = ?r")
proof (intro ext)
  fix i :: nat
  show "?l i = ?r i"
    unfolding HMA_I_def Domainp_iff
    by (auto intro: exI[of _ "from_nat i"] simp: to_nat_from_nat_id to_nat_less_card)
qed

lemma bi_unique_HMA_V [transfer_rule]: "bi_unique HMA_V" "left_unique HMA_V" "right_unique HMA_V"
  unfolding HMA_V_def bi_unique_def left_unique_def right_unique_def by auto

lemma bi_unique_HMA_M [transfer_rule]: "bi_unique HMA_M" "left_unique HMA_M" "right_unique HMA_M"
  unfolding HMA_M_def bi_unique_def left_unique_def right_unique_def by auto

lemma bi_unique_HMA_I [transfer_rule]: "bi_unique HMA_I" "left_unique HMA_I" "right_unique HMA_I"
  unfolding HMA_I_def bi_unique_def left_unique_def right_unique_def by auto

lemma right_total_HMA_V [transfer_rule]: "right_total HMA_V"
  unfolding HMA_V_def right_total_def by simp

lemma right_total_HMA_M [transfer_rule]: "right_total HMA_M"
  unfolding HMA_M_def right_total_def by simp

lemma right_total_HMA_I [transfer_rule]: "right_total HMA_I"
  unfolding HMA_I_def right_total_def by simp

lemma HMA_V_index [transfer_rule]: "(HMA_V ===> HMA_I ===> op =) (op $v) (op $h)"
  unfolding rel_fun_def HMA_V_def HMA_I_def from_hma\<^sub>v_def
  by (auto simp: to_nat_less_card)

text \<open>We introduce the index function to have pointwise access to 
  HMA-matrices by a constant. Otherwise, the transfer rule 
  with @{term "\<lambda> A i j. A $h i $h j"} instead of index is not applicable.\<close>

definition "index_hma A i j \<equiv> A $h i $h j"

lemma HMA_M_index [transfer_rule]:
  "(HMA_M ===> HMA_I ===> HMA_I ===> op =) (\<lambda> A i j. A $$ (i,j)) index_hma"
  by (intro rel_funI, simp add: index_hma_def to_nat_less_card HMA_M_def HMA_I_def from_hma\<^sub>m_def)  

lemma HMA_V_0 [transfer_rule]: "HMA_V (\<zero>\<^sub>v CARD('n)) (0 :: 'a :: zero ^ 'n)"
  unfolding HMA_V_def from_hma\<^sub>v_def by auto

lemma HMA_M_0 [transfer_rule]: 
  "HMA_M (\<zero>\<^sub>m CARD('nr) CARD('nc)) (0 :: 'a :: zero ^ 'nc  ^ 'nr )"
  unfolding HMA_M_def from_hma\<^sub>m_def by auto

lemma HMA_M_1[transfer_rule]:
  "HMA_M (\<one>\<^sub>m (CARD('n))) (mat 1 :: 'a::{zero,one}^'n^'n)"
  unfolding HMA_M_def
  by (auto simp add: mat_def from_hma\<^sub>m_def from_nat_inj)

lemma from_hma\<^sub>v_add: "from_hma\<^sub>v v \<oplus>\<^sub>v from_hma\<^sub>v w = from_hma\<^sub>v (v + w)"
  unfolding from_hma\<^sub>v_def by auto

lemma HMA_V_add [transfer_rule]: "(HMA_V ===> HMA_V ===> HMA_V) (op \<oplus>\<^sub>v) (op +) "
  unfolding rel_fun_def HMA_V_def
  by (auto simp: from_hma\<^sub>v_add)

lemma from_hma\<^sub>m_add: "from_hma\<^sub>m a \<oplus>\<^sub>m from_hma\<^sub>m b = from_hma\<^sub>m (a + b)"
  unfolding from_hma\<^sub>m_def by auto

lemma HMA_M_add [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) (op \<oplus>\<^sub>m) (op +) "
  unfolding rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_add)

definition hma_scalar_prod :: "'a :: semiring_1 ^ 'n \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a" where
  "hma_scalar_prod v w = (\<Sum> i \<in> UNIV. v $h i * w $h i)"

lemma hma_scalar_prod: fixes v :: "'a :: semiring_1 ^ 'n "
  shows "scalar_prod (from_hma\<^sub>v v) (from_hma\<^sub>v w) = hma_scalar_prod v w"
  unfolding hma_scalar_prod_def scalar_prod_def from_hma\<^sub>v_def vec_dim_vec
  by (simp add: setsum.reindex[OF inj_to_nat, unfolded range_to_nat])

lemma [simp]:
  "from_hma\<^sub>m (y :: 'a ^ 'nc  ^ 'nr) \<in> carrier\<^sub>m (CARD('nr)) (CARD('nc))"
  "dim\<^sub>r (from_hma\<^sub>m (y :: 'a ^ 'nc  ^ 'nr )) = CARD('nr)"
  "dim\<^sub>c (from_hma\<^sub>m (y :: 'a ^ 'nc  ^ 'nr )) = CARD('nc)"
  unfolding from_hma\<^sub>m_def by simp_all

lemma [simp]:
  "from_hma\<^sub>v (y :: 'a ^ 'n) \<in> carrier\<^sub>v (CARD('n))"
  "dim\<^sub>v (from_hma\<^sub>v (y :: 'a ^ 'n)) = CARD('n)"
  unfolding from_hma\<^sub>v_def by simp_all

declare rel_funI [intro!]

lemma HMA_scalar_prod [transfer_rule]:
  "(HMA_V ===> HMA_V ===> op =) scalar_prod hma_scalar_prod"
  by (auto simp: HMA_V_def hma_scalar_prod)

lemma HMA_row [transfer_rule]: "(HMA_I ===> HMA_M ===> HMA_V) (\<lambda> i a. Matrix.row a i) row"
  unfolding HMA_M_def HMA_I_def HMA_V_def
  by (auto simp: from_hma\<^sub>m_def from_hma\<^sub>v_def to_nat_less_card row_def)

lemma HMA_col [transfer_rule]: "(HMA_I ===> HMA_M ===> HMA_V) (\<lambda> i a. col a i) column"
  unfolding HMA_M_def HMA_I_def HMA_V_def
  by (auto simp: from_hma\<^sub>m_def from_hma\<^sub>v_def to_nat_less_card column_def)

definition mk_mat :: "('i \<Rightarrow> 'j \<Rightarrow> 'c) \<Rightarrow> 'c^'j^'i" where
  "mk_mat f = (\<chi> i j. f i j)"

definition mk_vec :: "('i \<Rightarrow> 'c) \<Rightarrow> 'c^'i" where
  "mk_vec f = (\<chi> i. f i)"

lemma HMA_M_mk_mat[transfer_rule]: "((HMA_I ===> HMA_I ===> op =) ===> HMA_M) 
  (\<lambda> f. Matrix.mat (CARD('nr)) (CARD('nc)) (\<lambda> (i,j). f i j)) 
  (mk_mat :: (('nr \<Rightarrow> 'nc \<Rightarrow> 'a) \<Rightarrow> 'a^'nc^'nr))"
proof-
  {
    fix x y i j
    assume id: "\<forall> (ya :: 'nr) (yb :: 'nc). (x (to_nat ya) (to_nat yb) :: 'a) = y ya yb"
       and i: "i < CARD('nr)" and j: "j < CARD('nc)"
    from to_nat_from_nat_id[OF i] to_nat_from_nat_id[OF j] id[rule_format, of "from_nat i" "from_nat j"]
    have "x i j = y (from_nat i) (from_nat j)" by auto
  }
  thus ?thesis
    unfolding rel_fun_def mk_mat_def HMA_M_def HMA_I_def from_hma\<^sub>m_def by auto
qed

lemma HMA_M_mk_vec[transfer_rule]: "((HMA_I ===> op =) ===> HMA_V) 
  (\<lambda> f. Matrix.vec (CARD('n)) (\<lambda> i. f i)) 
  (mk_vec :: (('n \<Rightarrow> 'a) \<Rightarrow> 'a^'n))"
proof-
  {
    fix x y i
    assume id: "\<forall> (ya :: 'n). (x (to_nat ya) :: 'a) = y ya"
       and i: "i < CARD('n)" 
    from to_nat_from_nat_id[OF i] id[rule_format, of "from_nat i"]
    have "x i = y (from_nat i)" by auto
  }
  thus ?thesis
    unfolding rel_fun_def mk_vec_def HMA_V_def HMA_I_def from_hma\<^sub>v_def by auto
qed


lemma mat_mult_scalar: "A ** B = mk_mat (\<lambda> i j. hma_scalar_prod (row i A) (column j B))"
  unfolding vec_eq_iff matrix_matrix_mult_def hma_scalar_prod_def mk_mat_def
  by (auto simp: row_def column_def)

lemma mat_mult_vec_scalar: "A *v v = mk_vec (\<lambda> i. hma_scalar_prod (row i A) v)"
  unfolding vec_eq_iff matrix_vector_mult_def hma_scalar_prod_def mk_mat_def mk_vec_def
  by (auto simp: row_def column_def)

lemma dim_row_transfer_rule: 
  "HMA_M A (A' :: 'a ^ 'nc ^ 'nr) \<Longrightarrow> (op =) (dim\<^sub>r A) (CARD('nr))"
  unfolding HMA_M_def by auto

lemma dim_col_transfer_rule: 
  "HMA_M A (A' :: 'a ^ 'nc ^ 'nr) \<Longrightarrow> (op =) (dim\<^sub>c A) (CARD('nc))"
  unfolding HMA_M_def by auto

lemma HMA_M_mult [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) (op \<otimes>\<^sub>m) (op **)"
proof -
  {
    fix A B :: "'a :: semiring_1 mat" and A' :: "'a ^ 'n  ^ 'nr" and B' :: "'a ^ 'nc ^ 'n"
    assume 1[transfer_rule]: "HMA_M A A'" "HMA_M B B'"
    note [transfer_rule] = dim_row_transfer_rule[OF 1(1)] dim_col_transfer_rule[OF 1(2)]
    have "HMA_M (A \<otimes>\<^sub>m B) (A' ** B')"
      unfolding mat_mult_mat_def mat_mult_scalar
      by (transfer_prover_start, transfer_step+, transfer, auto)
  }
  thus ?thesis by blast
qed
      

lemma HMA_V_scalar_mult [transfer_rule]: "(op = ===> HMA_V ===> HMA_V) (op \<odot>\<^sub>v) (op *s)"
  unfolding vec_scalar_mult_def vector_scalar_mult_def
  unfolding rel_fun_def HMA_V_def from_hma\<^sub>v_def
  by auto

lemma HMA_M_mult_vec [transfer_rule]: "(HMA_M ===> HMA_V ===> HMA_V) (op \<otimes>\<^sub>m\<^sub>v) (op *v)"
proof -
  {
    fix A :: "'a :: semiring_1 mat" and v :: "'a Matrix.vec"
      and A' :: "'a ^ 'nc  ^ 'nr" and v' :: "'a ^ 'nc"
    assume 1[transfer_rule]: "HMA_M A A'" "HMA_V v v'"
    note [transfer_rule] = dim_row_transfer_rule
    have "HMA_V (A \<otimes>\<^sub>m\<^sub>v v) (A' *v v')"
      unfolding mat_mult_vec_def mat_mult_vec_scalar
      by (transfer_prover_start, transfer_step+, transfer, auto)
  }
  thus ?thesis by blast  
qed

lemma HMA_det [transfer_rule]: "(HMA_M ===> op =) Determinant.det 
  (det :: 'a :: comm_ring_1 ^ 'n ^ 'n \<Rightarrow> 'a)"
proof -
  {
    fix a :: "'a ^ 'n ^ 'n"
    let ?tn = "to_nat :: 'n :: finite \<Rightarrow> nat"
    let ?fn = "from_nat :: nat \<Rightarrow> 'n"
    let ?zn = "{0..< CARD('n)}"
    let ?U = "UNIV :: 'n set"
    let ?p1 = "{p. p permutes ?zn}"
    let ?p2 = "{p. p permutes ?U}"  
    let ?f= "\<lambda> p i. if i \<in> ?U then ?fn (p (?tn i)) else i"
    let ?g = "\<lambda> p i. ?fn (p (?tn i))"
    have fg: "\<And> a b c. (if a \<in> ?U then b else c) = b" by auto
    have "?p2 = ?f ` ?p1" 
      by (rule permutes_bij', auto simp: to_nat_less_card to_nat_from_nat_id)
    hence id: "?p2 = ?g ` ?p1" by simp
    have inj_g: "inj_on ?g ?p1"
      unfolding inj_on_def
    proof (intro ballI impI ext, auto)
      fix p q i
      assume p: "p permutes ?zn" and q: "q permutes ?zn"
        and id: "(\<lambda> i. ?fn (p (?tn i))) = (\<lambda> i. ?fn (q (?tn i)))"
      {
        fix i
        from permutes_in_image[OF p] have pi: "p (?tn i) < CARD('n)" by (simp add: to_nat_less_card)
        from permutes_in_image[OF q] have qi: "q (?tn i) < CARD('n)" by (simp add: to_nat_less_card)
        from fun_cong[OF id] have "?fn (p (?tn i))  = from_nat (q (?tn i))" .
        from arg_cong[OF this, of ?tn] have "p (?tn i) = q (?tn i)"
          by (simp add: to_nat_from_nat_id pi qi)
      } note id = this             
      show "p i = q i"
      proof (cases "i < CARD('n)")
        case True
        hence "?tn (?fn i) = i" by (simp add: to_nat_from_nat_id)
        from id[of "?fn i", unfolded this] show ?thesis .
      next
        case False
        thus ?thesis using p q unfolding permutes_def by simp
      qed
    qed
    have mult_cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by simp
    have "setsum (\<lambda> p. 
      signof p * (\<Prod>i\<in>?zn. a $h ?fn i $h ?fn (p i))) ?p1
      = setsum (\<lambda> p. of_int (sign p) * (\<Prod>i\<in>UNIV. a $h i $h p i)) ?p2"
      unfolding id setsum.reindex[OF inj_g]
    proof (rule setsum.cong[OF refl], unfold mem_Collect_eq o_def, rule mult_cong)
      fix p
      assume p: "p permutes ?zn"
      let ?q = "\<lambda> i. ?fn (p (?tn i))"
      from id p have q: "?q permutes ?U" by auto
      from p have pp: "permutation p" unfolding permutation_permutes by auto
      let ?ft = "\<lambda> p i. ?fn (p (?tn i))"
      have fin: "finite ?zn" by simp
      have "sign p = sign ?q \<and> p permutes ?zn"
      proof (induct rule: permutes_induct[OF fin _ _ p])    
        case 1 
        show ?case by (auto simp: sign_id[unfolded id_def] permutes_id[unfolded id_def])
      next
        case (2 a b p)
        let ?sab = "Fun.swap a b id"
        let ?sfab = "Fun.swap (?fn a) (?fn b) id"
        have p_sab: "permutation ?sab" by (rule permutation_swap_id)
        have p_sfab: "permutation ?sfab" by (rule permutation_swap_id)
        from 2(3) have IH1: "p permutes ?zn" and IH2: "sign p = sign (?ft p)" by auto
        have sab_perm: "?sab permutes ?zn" using 2(1-2) by (rule permutes_swap_id)
        from permutes_compose[OF IH1 this] have perm1: "?sab o p permutes ?zn" .
        from IH1 have p_p1: "p \<in> ?p1" by simp
        hence "?ft p \<in> ?ft ` ?p1" by (rule imageI)
        from this[folded id] have "?ft p permutes ?U" by simp
        hence p_ftp: "permutation (?ft p)" unfolding permutation_permutes by auto
        {
          fix a b
          assume a: "a \<in> ?zn" and b: "b \<in> ?zn"
          hence "(?fn a = ?fn b) = (a = b)" using 2(1-2)
            by (auto simp: from_nat_inj)
        } note inj = this
        from inj[OF 2(1-2)] have id2: "sign ?sfab = sign ?sab" unfolding sign_swap_id by simp
        have id: "?ft (Fun.swap a b id \<circ> p) = Fun.swap (?fn a) (?fn b) id \<circ> ?ft p"
        proof
          fix c 
          show "?ft (Fun.swap a b id \<circ> p) c = (Fun.swap (?fn a) (?fn b) id \<circ> ?ft p) c"
          proof (cases "p (?tn c) = a \<or> p (?tn c) = b")
            case True
            thus ?thesis by (cases, auto simp add: o_def swap_def)
          next
            case False
            hence neq: "p (?tn c) \<noteq> a" "p (?tn c) \<noteq> b" by auto
            have pc: "p (?tn c) \<in> ?zn" unfolding permutes_in_image[OF IH1] 
              by (simp add: to_nat_less_card)
            from neq[folded inj[OF pc 2(1)] inj[OF pc 2(2)]]
            have "?fn (p (?tn c)) \<noteq> ?fn a" "?fn (p (?tn c)) \<noteq> ?fn b" .
            with neq show ?thesis by (auto simp: o_def swap_def)
          qed
        qed
        show ?case unfolding IH2 id sign_compose[OF p_sab 2(5)] sign_compose[OF p_sfab p_ftp] id2 
          by (rule conjI[OF refl perm1])
      qed
      thus "signof p = of_int (sign ?q)" unfolding signof_def sign_def by auto
      show "(\<Prod>i = 0..<CARD('n). a $h ?fn i $h ?fn (p i)) =
           (\<Prod>i\<in>UNIV. a $h i $h ?q i)" unfolding 
           range_to_nat[symmetric] setprod.reindex[OF inj_to_nat]
        by (rule setprod.cong[OF refl], unfold o_def, simp)
    qed   
  }
  thus ?thesis unfolding HMA_M_def 
    by (auto simp: from_hma\<^sub>m_def Determinant.det_def det_def)
qed

lemma HMA_mat[transfer_rule]: "(op = ===> HMA_M) (\<lambda> k. k \<odot>\<^sub>m \<one>\<^sub>m CARD('n)) 
  (Cartesian_Euclidean_Space.mat :: 'a::semiring_1 \<Rightarrow> 'a^'n^'n)"
  unfolding Cartesian_Euclidean_Space.mat_def[abs_def] rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_def from_nat_inj)


lemma HMA_mat_minus[transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) 
  (\<lambda> A B. A \<oplus>\<^sub>m map\<^sub>m uminus B) (op - :: 'a :: group_add ^'nc^'nr \<Rightarrow> 'a^'nc^'nr \<Rightarrow> 'a^'nc^'nr)"
  unfolding rel_fun_def HMA_M_def from_hma\<^sub>m_def by auto

lemma HMA_mat2matofpoly[transfer_rule]: "(HMA_M ===> HMA_M) (\<lambda>x. map\<^sub>m (\<lambda>a. [:a:]) x) mat2matofpoly"
  unfolding rel_fun_def HMA_M_def from_hma\<^sub>m_def mat2matofpoly_def by auto

lemma HMA_char_poly [transfer_rule]: 
  "((HMA_M :: ('a:: comm_ring_1 mat \<Rightarrow> 'a^'n^'n \<Rightarrow> bool)) ===> (op =)) char_poly charpoly"
proof -
  {
    fix A :: "'a mat" and A' :: "'a^'n^'n"
    assume [transfer_rule]: "HMA_M A A'"
    hence [simp]: "dim\<^sub>r A = CARD('n)" by (simp add: HMA_M_def)
    have [simp]: "monom 1 (Suc 0) = [: 0,1 :: 'a :]" by (simp add: monom_Suc one_poly_def)
    have [simp]: "map\<^sub>m uminus (map\<^sub>m (\<lambda>a. [:a:]) A) = map\<^sub>m (\<lambda>a. [:-a:]) A"
      by (rule mat_eqI, auto)
    have "char_poly A = charpoly A'"
      unfolding char_poly_def[abs_def] char_poly_matrix_def charpoly_def[abs_def]
      by (transfer, simp)
  }
  thus ?thesis by blast
qed
 

lemma matpow_commute: "matpow A n ** A = A ** matpow A n"
  by (induct n, auto simp: matrix_mul_lid matrix_mul_rid, subst matrix_mul_assoc[symmetric], auto) 

lemma HMA_mat_pow[transfer_rule]:
  "((HMA_M ::'a::{semiring_1} mat \<Rightarrow> 'a^'n^'n \<Rightarrow> bool) ===> op = ===> HMA_M) mat_pow matpow"
proof -
  {
    fix A :: "'a mat" and A' :: "'a^'n^'n" and n :: nat
    assume [transfer_rule]: "HMA_M A A'"
    hence [simp]: "dim\<^sub>r A = CARD('n)" unfolding HMA_M_def by simp
    have "HMA_M (mat_pow A n) (matpow A' n)"
    proof (induct n)
      case (Suc n)
      note [transfer_rule] = this
      show ?case by (simp add: matpow_commute[symmetric], transfer_prover)
    qed (simp, transfer_prover)
  }
  thus ?thesis by blast
qed


lemma HMA_eigen_vector [transfer_rule]: "(HMA_M ===> HMA_V ===> op =) eigenvector eigen_vector"
proof -
  { 
    fix A :: "'a mat" and v :: "'a Matrix.vec" 
    and A' :: "'a ^ 'n ^ 'n" and v' :: "'a ^ 'n" and k :: 'a
    assume 1[transfer_rule]: "HMA_M A A'" and 2[transfer_rule]: "HMA_V v v'"
    hence [simp]: "dim\<^sub>r A = CARD('n)" "dim\<^sub>v v = CARD('n)" by (auto simp add: HMA_V_def HMA_M_def)
    have [simp]: "v \<in> carrier\<^sub>v CARD('n)" using 2 unfolding HMA_V_def by simp
    have "eigenvector A v = eigen_vector A' v'" 
      unfolding eigenvector_def[abs_def] eigen_vector_def[abs_def] 
      by (transfer, simp)
  }
  thus ?thesis by blast
qed


lemma HMA_eigen_value [transfer_rule]: "(HMA_M ===> op = ===> op =) eigenvalue eigen_value"
proof -
  {
    fix A :: "'a mat" and A' :: "'a ^ 'n  ^ 'n" and k
    assume 1[transfer_rule]: "HMA_M A A'"
    hence [simp]: "dim\<^sub>r A = CARD('n)" by (simp add: HMA_M_def)
    note [transfer_rule] = dim_row_transfer_rule[OF 1(1)]    
    have "(eigenvalue A k) = (eigen_value A' k)"
      unfolding eigenvalue_def[abs_def] eigen_value_def[abs_def] 
      by (transfer, auto simp add: eigenvector_def)
  }
  thus ?thesis by blast
qed


lemma HMA_spectral_radius [transfer_rule]: 
  "(HMA_M ===> op =) Spectral_Radius.spectral_radius spectral_radius"
  unfolding Spectral_Radius.spectral_radius_def[abs_def] spectrum_def 
    spectral_radius_ev_def[abs_def]
  by transfer_prover

lemma HMA_mat_elements[transfer_rule]: "((HMA_M :: ('a mat \<Rightarrow> 'a ^ 'nc ^ 'nr \<Rightarrow> bool))  ===> op =) 
  mat_elements mat_elements_h"
proof -
  {
    fix y :: "'a ^ 'nc ^ 'nr" and i j :: nat
    assume i: "i < CARD('nr)" and j: "j < CARD('nc)"
    hence "from_hma\<^sub>m y $$ (i, j) \<in> range (\<lambda>(i, ya). y $h i $h ya)"      
      using to_nat_from_nat_id[OF i] to_nat_from_nat_id[OF j] by (auto simp: from_hma\<^sub>m_def)
  }
  moreover
  {
    fix y :: "'a ^ 'nc ^ 'nr" and a b
    have "\<exists>i j. y $h a $h b = from_hma\<^sub>m y $$ (i, j) \<and> i < CARD('nr) \<and> j < CARD('nc)"
      unfolding from_hma\<^sub>m_def
      by (rule exI[of _ "Bij_Nat.to_nat a"], rule exI[of _ "Bij_Nat.to_nat b"], auto
        simp: to_nat_less_card)
  }
  ultimately show ?thesis
    unfolding mat_elements[abs_def] mat_elements_h_def[abs_def] HMA_M_def
    by auto
qed  

lemma HMA_vec_elements[transfer_rule]: "((HMA_V :: ('a Matrix.vec \<Rightarrow> 'a ^ 'n \<Rightarrow> bool))  ===> op =) 
  vec_elements vec_elements_h"
proof -
  {
    fix y :: "'a ^ 'n" and i :: nat
    assume i: "i < CARD('n)" 
    hence "from_hma\<^sub>v y $ i \<in> range (vec_nth y)"      
      using to_nat_from_nat_id[OF i] by (auto simp: from_hma\<^sub>v_def)
  }
  moreover
  {
    fix y :: "'a ^ 'n" and a
    have "\<exists>i. y $h a = from_hma\<^sub>v y $ i \<and> i < CARD('n)"
      unfolding from_hma\<^sub>v_def
      by (rule exI[of _ "Bij_Nat.to_nat a"], auto simp: to_nat_less_card)
  }
  ultimately show ?thesis
    unfolding vec_elements[abs_def] vec_elements_h_def[abs_def] rel_fun_def HMA_V_def
    by auto
qed  
  
lemma norm_bound_mat_elements: "norm_bound A b = (\<forall> x \<in> mat_elements A. norm x \<le> b)"
  unfolding norm_bound_def mat_elements by auto

lemma HMA_normbound [transfer_rule]: 
  "((HMA_M :: 'a :: real_normed_field mat \<Rightarrow> 'a ^ 'nc ^ 'nr \<Rightarrow> bool) ===> op = ===> op =)
  norm_bound normbound"
  unfolding normbound_def[abs_def] norm_bound_mat_elements[abs_def]
  by (transfer_prover)

lemma HMA_map_matrix [transfer_rule]: 
  "(op = ===> HMA_M ===> HMA_M) map\<^sub>m map_matrix"
  unfolding map_vector_def map_matrix_def[abs_def] mat_map_def[abs_def] HMA_M_def from_hma\<^sub>m_def
  by auto

lemma HMA_map_vector [transfer_rule]: 
  "(op = ===> HMA_V ===> HMA_V) map\<^sub>v map_vector"
  unfolding map_vector_def[abs_def] map_vec_def[abs_def] HMA_V_def from_hma\<^sub>v_def
  by auto
end 

text \<open>Setup a method to easily convert theorems from JNF into HMA.\<close>

method transfer_hma uses rule = (
  (fold index_hma_def)?, (* prepare matrix access for transfer *)
  transfer,
  rule rule, 
  (unfold vec_carrier_def mat_carrier_def)?, 
  auto)

text \<open>Now it becomes easy to transfer results which are not yet proven in HMA, such as:\<close>

lemma matrix_add_vect_distrib: "(A + B) *v v = A *v v + B *v v"
  by (transfer_hma rule: mat_mult_vec_left_distrib)

lemma eigen_value_root_charpoly: 
  "eigen_value A k \<longleftrightarrow> poly (charpoly (A :: 'a :: field ^ 'n ^ 'n)) k = 0"
  by (transfer_hma rule: eigenvalue_root_char_poly)

lemma finite_spectrum: fixes A :: "'a :: field ^ 'n ^ 'n"
  shows "finite (Collect (eigen_value A))" 
  by (transfer_hma rule: card_finite_spectrum(1)[unfolded spectrum_def])

lemma non_empty_spectrum: fixes A :: "complex ^ 'n ^ 'n"
  shows "Collect (eigen_value A) \<noteq> {}"
  by (transfer_hma rule: spectrum_non_empty[unfolded spectrum_def])

end