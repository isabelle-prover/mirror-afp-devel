(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Determinants\<close>

text \<open>Most of the following definitions and proofs on determinants have been copied and adapted 
  from ~~/src/HOL/Multivariate-Analysis/Determinants.thy.

Exceptions are \emph{det-identical-rows}.

We further generalized some lemmas, e.g., that the determinant is 0 iff the kernel of a matrix
is non-empty is available for integral domains, not just for fields.\<close>

theory Determinant
imports 
  Missing_Permutations
  Missing_Fraction_Field
  Column_Operations
  "../Polynomial_Interpolation/Ring_Hom"
  "../Polynomial_Interpolation/Missing_Unsorted"
begin

definition det:: "'a mat \<Rightarrow> 'a :: comm_ring_1" where
  "det A = (if dim\<^sub>r A = dim\<^sub>c A then (\<Sum> p \<in> {p. p permutes {0 ..< dim\<^sub>r A}}. 
     signof p * (\<Prod> i = 0 ..< dim\<^sub>r A. A $$ (i, p i))) else 0)"

context ring_hom
begin
lemma hom_signof[simp]: "hom (signof p) = signof p"
  unfolding signof_def by auto

lemma hom_det[simp]: "det (map\<^sub>m hom A) = hom (det A)"
  unfolding det_def by auto
end

lemma det_def': "A \<in> carrier\<^sub>m n n \<Longrightarrow> 
  det A = (\<Sum> p \<in> {p. p permutes {0 ..< n}}. 
     signof p * (\<Prod> i = 0 ..< n. A $$ (i, p i)))" unfolding det_def by auto

lemma det_smult[simp]: "det (a \<odot>\<^sub>m A) = a ^ dim\<^sub>c A * det A"
proof -
  have [simp]: "(\<Prod>i = 0..<dim\<^sub>c A. a) = a ^ dim\<^sub>c A" by(subst setprod_constant;simp)
  show ?thesis
  unfolding det_def
  unfolding mat_index_scalar_mult
  by (auto intro: setsum.cong simp: setsum_right_distrib setprod.distrib)
qed

lemma det_transpose: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "det (transpose\<^sub>m A) = det A"
proof -
  let ?di = "\<lambda>A i j. A $$ (i,j)"
  let ?U = "{0 ..< n}"
  have fU: "finite ?U" by simp
  let ?inv = "Hilbert_Choice.inv"
  {
    fix p
    assume p: "p \<in> {p. p permutes ?U}"
    from p have pU: "p permutes ?U"
      by blast
    have sth: "signof (?inv p) = signof p"
      by (rule signof_inv[OF _ pU], simp)
    from permutes_inj[OF pU]
    have pi: "inj_on p ?U"
      by (blast intro: subset_inj_on)
    let ?f = "\<lambda>i. transpose\<^sub>m A $$ (i, ?inv p i)"
    note pU_U = permutes_image[OF pU]
    note [simp] = permutes_less[OF pU]
    have "setprod ?f ?U = setprod ?f (p ` ?U)"
      using pU_U by simp
    also have "\<dots> = setprod (?f \<circ> p) ?U"
      by (rule setprod.reindex[OF pi])
    also have "\<dots> = setprod (\<lambda>i. A $$ (i, p i)) ?U"
      by (rule setprod.cong, insert A, auto)
    finally have "signof (?inv p) * setprod ?f ?U =
      signof p * setprod (\<lambda>i. A $$ (i, p i)) ?U"
      unfolding sth by simp
  }
  then show ?thesis
    unfolding det_def using A
    by (simp, subst setsum_permutations_inverse, intro setsum.cong, auto)
qed

lemma det_col:
  assumes A: "A \<in> carrier\<^sub>m n n"
  shows "det A = (\<Sum> p | p permutes {0 ..< n}. signof p * (\<Prod>j<n. A $$ (p j, j)))"
    (is "_ = (setsum (\<lambda>p. _ * ?prod p) ?P)")
proof -
  let ?i = "Hilbert_Choice.inv"
  let ?N = "{0 ..< n}"
  let ?f = "\<lambda>p. signof p * ?prod p"
  let ?prod' = "\<lambda>p. \<Prod>j<n. A $$ (j, ?i p j)"
  let ?prod'' = "\<lambda>p. \<Prod>j<n. A $$ (j, p j)"
  let ?f' = "\<lambda>p. signof (?i p) * ?prod' p"
  let ?f'' = "\<lambda>p. signof p * ?prod'' p"
  let ?P' = "{ ?i p | p. p permutes ?N }"
  have [simp]: "{0..<n} = {..<n}" by auto
  have "setsum ?f ?P = setsum ?f' ?P"
  proof (rule setsum.cong[OF refl],unfold mem_Collect_eq)
      fix p assume p: "p permutes ?N"
      have [simp]: "?prod p = ?prod' p"
        using permutes_setprod[OF p, of "\<lambda>x y. A $$ (x,y)"] by auto
      have [simp]: "signof p = signof (?i p)"
        apply(rule signof_inv[symmetric]) using p by auto
      show "?f p = ?f' p" by auto
  qed
  also have "... = setsum ?f' ?P'"
    by (rule setsum.cong[OF image_inverse_permutations[symmetric]],auto)
  also have "... = setsum ?f'' ?P"
    unfolding setsum.reindex[OF inv_inj_on_permutes,unfolded image_Collect]
    unfolding o_def
    apply (rule setsum.cong[OF refl])
    using inv_inv_eq[OF permutes_bij] by force
  finally show ?thesis unfolding det_def'[OF A] by auto
qed

lemma mat_det_left_def: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "det A = (\<Sum>p\<in>{p. p permutes {0..<dim\<^sub>r A}}. signof p * (\<Prod>i = 0 ..< dim\<^sub>r A. A $$ (p i, i)))"
proof -
  have cong: "\<And> a b c. b = c \<Longrightarrow> a * b = a * c" by simp
  show ?thesis
  unfolding det_transpose[OF A, symmetric]
  unfolding det_def mat_index_transpose using A by simp
qed

lemma det_upper_triangular:
  assumes ut: "upper_triangular A"
  and m: "A \<in> carrier\<^sub>m n n"
  shows "det A = listprod (mat_diag A)"
proof -
  note det_def = det_def'[OF m]
  let ?U = "{0..<n}"
  let ?PU = "{p. p permutes ?U}"
  let ?pp = "\<lambda>p. signof p * (\<Prod> i = 0 ..< n. A $$ (i, p i))"
  have fU: "finite ?U"
    by simp
  from finite_permutations[OF fU] have fPU: "finite ?PU" .
  have id0: "{id} \<subseteq> ?PU"
    by (auto simp add: permutes_id)
  {
    fix p
    assume p: "p \<in> ?PU - {id}"
    from p have pU: "p permutes ?U" and pid: "p \<noteq> id"
      by blast+
    from permutes_natset_ge[OF pU] pid obtain i where i: "p i < i" and "i < n" 
      by fastforce
    from upper_triangularD[OF ut i] `i < n` m
    have ex:"\<exists>i \<in> ?U. A $$ (i,p i) = 0" by auto
    have "(\<Prod> i = 0 ..< n. A $$ (i, p i)) = 0" 
      by (rule setprod_zero[OF fU ex])
    hence "?pp p = 0" by simp
  }
  then have p0: "\<And> p. p \<in> ?PU - {id} \<Longrightarrow> ?pp p = 0"
    by blast
  from m have dim: "dim\<^sub>r A = n" by simp
  have "det A = (\<Sum> p \<in> ?PU. ?pp p)" unfolding det_def by auto
  also have "\<dots> = ?pp id + (\<Sum> p \<in> ?PU - {id}. ?pp p)"
    by (rule setsum.remove, insert id0 fPU m, auto simp: p0)
  also have "(\<Sum> p \<in> ?PU - {id}. ?pp p) = 0"
    by (rule setsum.neutral, insert fPU, auto simp: p0)
  finally show ?thesis using m by (auto simp: signof_id listprod_diag_setprod)
qed

lemma det_one[simp]: "det (\<one>\<^sub>m n) = 1"
proof -
  have "det (\<one>\<^sub>m n) = listprod (mat_diag (\<one>\<^sub>m n))"
    by (rule det_upper_triangular[of _ n], auto)
  also have "\<dots> = 1" by (induct n, auto)
  finally show ?thesis .
qed

lemma det_zero[simp]: assumes "n > 0" shows "det (\<zero>\<^sub>m n n) = 0"
proof -
  have "det (\<zero>\<^sub>m n n) = listprod (mat_diag (\<zero>\<^sub>m n n))"
    by (rule det_upper_triangular[of _ n], auto)
  also have "\<dots> = 0" using `n > 0` by (cases n, auto)
  finally show ?thesis .
qed

lemma det_dim_zero[simp]: "A \<in> carrier\<^sub>m 0 0 \<Longrightarrow> det A = 1"
  unfolding det_def mat_carrier_def signof_def sign_def by auto
 

lemma det_lower_triangular:
  assumes ld: "\<And>i j. i < j \<Longrightarrow> j < n \<Longrightarrow> A $$ (i,j) = 0"
  and m: "A \<in> carrier\<^sub>m n n"
  shows "det A = listprod (mat_diag A)"
proof -
  have "det A = det (transpose\<^sub>m A)" using det_transpose[OF m] by simp
  also have "\<dots> = listprod (mat_diag (transpose\<^sub>m A))"
    by (rule det_upper_triangular, insert m ld, auto)
  finally show ?thesis using m by simp
qed

lemma det_permute_rows: assumes A: "A \<in> carrier\<^sub>m n n"
  and p: "p permutes {0 ..< (n :: nat)}"
  shows "det (mat n n (\<lambda> (i,j). A $$ (p i, j))) = signof p * det A"
proof -
  let ?U = "{0 ..< (n :: nat)}"
  have cong: "\<And> a b c. b = c \<Longrightarrow> a * b = a * c" by auto
  have "det (mat n n (\<lambda> (i,j). A $$ (p i, j))) = 
    (\<Sum> q \<in> {q . q permutes ?U}. signof q * (\<Prod> i \<in> ?U. A $$ (p i, q i)))"
    unfolding det_def using A p by auto
  also have "\<dots> = (\<Sum> q \<in> {q . q permutes ?U}. signof (q \<circ> p) * (\<Prod> i \<in> ?U. A $$ (p i, (q \<circ> p) i)))"
    by (rule sum_permutations_compose_right[OF p])
  finally have 1: "det (mat n n (\<lambda> (i,j). A $$ (p i, j)))
    = (\<Sum> q \<in> {q . q permutes ?U}. signof (q \<circ> p) * (\<Prod> i \<in> ?U. A $$ (p i, (q \<circ> p) i)))" .
  have 2: "signof p * det A = 
    (\<Sum> q\<in>{q. q permutes ?U}. signof p * signof q * (\<Prod>i\<in> ?U. A $$ (i, q i)))"
    unfolding det_def'[OF A] setsum_right_distrib by (simp add: ac_simps)
  show ?thesis unfolding 1 2
  proof (rule setsum.cong, insert p A, auto)
    fix q
    assume q: "q permutes ?U"
    let ?inv = "Hilbert_Choice.inv"
    from permutes_inv[OF p] have ip: "?inv p permutes ?U" .
    have "setprod (\<lambda>i. A $$ (p i, (q \<circ> p) i)) ?U = 
      setprod (\<lambda>i. A $$ ((p \<circ> ?inv p) i, (q \<circ> (p \<circ> ?inv p)) i)) ?U" unfolding o_def
      by (rule trans[OF setprod.permute[OF ip] setprod.cong], insert A p q, auto)
    also have "\<dots> = setprod (\<lambda>i. A$$(i,q i)) ?U"
      by (simp only: o_def permutes_inverses[OF p])
    finally have thp: "setprod (\<lambda>i. A $$ (p i, (q \<circ> p) i)) ?U = setprod (\<lambda>i. A$$(i,q i)) ?U" .      
    show "signof (q \<circ> p) * (\<Prod>i\<in>{0..<n}. A $$ (p i, q (p i))) =
         signof p * signof q * (\<Prod>i\<in>{0..<n}. A $$ (i, q i))"
      unfolding thp[symmetric] signof_compose[OF q p]
      by (simp add: ac_simps)
  qed
qed

lemma det_multrow_mat: assumes k: "k < n"
  shows "det (multrow_mat n k a) = a"
proof (rule trans[OF det_lower_triangular[of n]], unfold listprod_diag_setprod)
  let ?f = "\<lambda> i. multrow_mat n k a $$ (i, i)"
  have "(\<Prod>i\<in>{0..<n}. ?f i) = ?f k * (\<Prod>i\<in>{0..<n} - {k}. ?f i)"
    by (rule setprod.remove, insert k, auto)
  also have "(\<Prod>i\<in>{0..<n} - {k}. ?f i) = 1" 
    by (rule setprod.neutral, auto)
  finally show "(\<Prod>i\<in>{0..<dim\<^sub>r (multrow_mat n k a)}. ?f i) = a" using k by simp
qed (insert k, auto)

lemma swap_rows_mat_eq_permute: 
  "k < n \<Longrightarrow> l < n \<Longrightarrow> swaprows_mat n k l = mat n n (\<lambda>(i, j). \<one>\<^sub>m n $$ (Fun.swap k l id i, j))"
  by (rule mat_eqI, auto simp: swap_def)

lemma det_swaprows_mat: assumes k: "k < n" and l: "l < n" and kl: "k \<noteq> l"
  shows "det (swaprows_mat n k l) = - 1"
proof -
  let ?n = "{0 ..< (n :: nat)}"
  let ?p = "Fun.swap k l id"
  have p: "?p permutes ?n"
    by (rule permutes_swap_id, insert k l, auto)
  show ?thesis
    by (rule trans[OF trans[OF _ det_permute_rows[OF mat_one_closed[of n] p]]],
    subst swap_rows_mat_eq_permute[OF k l], auto simp: signof_def sign_swap_id kl)
qed
  
lemma det_addrow_mat: 
  assumes l: "k \<noteq> l"
  shows "det (addrow_mat n a k l) = 1"
proof -
  have "det (addrow_mat n a k l) = listprod (mat_diag (addrow_mat n a k l))"
  proof (cases "k < l")
    case True
    show ?thesis
      by (rule det_upper_triangular[of _ n], insert True, auto intro!: upper_triangularI)
  next
    case False
    show ?thesis
      by (rule det_lower_triangular[of n], insert False, auto)
  qed
  also have "\<dots> = 1" unfolding listprod_diag_setprod
    by (rule setprod.neutral, insert l, auto)
  finally show ?thesis .
qed

text \<open>The following proof is new, as it does not use $2 \neq 0$ as in Multivariate-Analysis.\<close>

lemma det_identical_rows:
  assumes A: "A \<in> carrier\<^sub>m n n"  
    and ij: "i \<noteq> j"
    and i: "i < n" and j: "j < n"
    and r: "row A i = row A j"
  shows "det A = 0"
proof-
  let ?p = "Fun.swap i j id"
  let ?n = "{0 ..< n}"
  have sp: "signof ?p = - 1" "sign ?p = -1" unfolding signof_def using ij
    by (auto simp add: sign_swap_id)
  let ?f = "\<lambda> p. signof p * (\<Prod>i\<in>?n. A $$ (p i, i))"
  let ?all = "{p. p permutes ?n}"
  let ?one = "{p. p permutes ?n \<and> sign p = 1}"
  let ?none = "{p. p permutes ?n \<and> sign p \<noteq> 1}"
  let ?pone = "(\<lambda> p. ?p o p) ` ?one"
  have split: "?one \<union> ?none = ?all" by auto
  have p: "?p permutes ?n" by (rule permutes_swap_id, insert i j, auto)
  from permutes_inj[OF p] have injp: "inj ?p" by auto
  {
    fix q
    assume q: "q permutes ?n"
    have "(\<Prod>k\<in>?n. A $$ (?p (q k), k)) = (\<Prod>k\<in>?n. A $$ (q k, k))"
    proof (rule setprod.cong)
      fix k
      assume k: "k \<in> ?n"
      from r have row: "row A i $ k = row A j $ k" by simp
      hence "A $$ (i,k) = A $$ (j,k)" using k i j A by auto
      thus "A $$ (?p (q k), k) = A $$ (q k, k)"
        by (cases "q k = i", auto, cases "q k = j", auto)
    qed (insert A q, auto)
  } note * = this
  have pp: "\<And> q. q permutes ?n \<Longrightarrow> permutation q" unfolding 
    permutation_permutes by auto
  have "det A = (\<Sum>p\<in> ?one \<union> ?none. ?f p)"
    using A unfolding mat_det_left_def[OF A] split by simp
  also have "\<dots> = (\<Sum>p\<in> ?one. ?f p) + (\<Sum>p\<in> ?none. ?f p)"
    by (rule setsum.union_disjoint, insert A, auto simp: finite_permutations)
  also have "?none = ?pone" 
  proof -
    {
      fix q
      assume "q \<in> ?none"
      hence q: "q permutes ?n" and sq: "sign q = -1" unfolding sign_def by auto
      from permutes_compose[OF q p] sign_compose[OF pp[OF p] pp[OF q], unfolded sp sq]
      have "?p o q \<in> ?one" by auto
      hence "?p o (?p o q) \<in> ?pone" by auto
      also have "?p o (?p o q) = q" unfolding o_def
        by (intro ext, auto simp: swap_def)
      finally have "q \<in> ?pone" .
    }
    moreover
    {
      fix pq
      assume "pq \<in> ?pone"
      then obtain q where q: "q \<in> ?one" and pq: "pq = ?p o q" by auto
      from q have q: "q permutes ?n" and sq: "sign q = 1" by auto
      from sign_compose[OF pp[OF p] pp[OF q], unfolded sq sp] have spq: "sign pq = -1" unfolding pq by auto
      from permutes_compose[OF q p] have pq: "pq permutes ?n" unfolding pq by auto
      from pq spq have "pq \<in> ?none" by auto
    }
    ultimately
    show ?thesis by blast
  qed  
  also have "(\<Sum>p\<in> ?pone. ?f p) = (\<Sum>p\<in> ?one. ?f (?p o p))"
  proof (rule trans[OF setsum.reindex])
    show "inj_on (op \<circ> ?p) ?one" 
      using fun.inj_map[OF injp] unfolding inj_on_def by auto
  qed simp
  also have "(\<Sum>p\<in> ?one. ?f p) + (\<Sum>p\<in> ?one. ?f (?p o p))
    = (\<Sum>p\<in> ?one. ?f p + ?f (?p o p))"
    by (rule setsum.distrib[symmetric])
  also have "\<dots> = 0"
    by (rule setsum.neutral, insert A, auto simp: 
      sp sign_compose[OF pp[OF p] pp] ij signof_def finite_permutations *)
  finally show ?thesis .
qed

lemma det_row_0: assumes k: "k < n"
  and c: "c \<in> {0 ..< n} \<rightarrow> carrier\<^sub>v n"
  shows "det (mat\<^sub>r n n (\<lambda>i. if i = k then \<zero>\<^sub>v n else c i)) = 0"
proof -
  {
    fix p
    assume p: "p permutes {0 ..< n}"
    have "(\<Prod>i\<in>{0..<n}. mat\<^sub>r n n (\<lambda>i. if i = k then \<zero>\<^sub>v n else c i) $$ (i, p i)) = 0" 
      by (rule setprod_zero[OF _ bexI[of _ k]], 
      insert k p c[unfolded vec_carrier_def], auto)
  }
  thus ?thesis unfolding det_def by simp
qed

lemma det_row_add: 
  assumes abc: "a k \<in> carrier\<^sub>v n" "b k \<in> carrier\<^sub>v n" "c \<in> {0..<n} \<rightarrow> carrier\<^sub>v n"
    and k: "k < n"
  shows "det(mat\<^sub>r n n (\<lambda> i. if i = k then a i \<oplus>\<^sub>v b i else c i)) =
    det(mat\<^sub>r n n (\<lambda> i. if i = k then a i else c i)) +
    det(mat\<^sub>r n n (\<lambda> i. if i = k then b i else c i))"
  (is "?lhs = ?rhs")
proof -
  let ?n = "{0..<n}"
  let ?m = "\<lambda> a b p i. mat\<^sub>r n n (\<lambda>i. if i = k then a i else b i) $$ (i, p i)"
  let ?c = "\<lambda> p i. mat\<^sub>r n n c $$ (i, p i)"
  let ?ab = "\<lambda> i. a i \<oplus>\<^sub>v b i"
  note intros = vec_add_closed[of _ n]
  have "?rhs = (\<Sum>p\<in>{p. p permutes ?n}. 
    signof p * (\<Prod>i\<in>?n. ?m a c p i)) + (\<Sum>p\<in>{p. p permutes ?n}. signof p * (\<Prod>i\<in>?n. ?m b c p i))"
    unfolding det_def by simp
  also have "\<dots> = (\<Sum>p\<in>{p. p permutes ?n}. signof p * (\<Prod>i\<in>?n. ?m a c p i) +  signof p * (\<Prod>i\<in>?n. ?m b c p i))"
    by (rule setsum.distrib[symmetric])
  also have "\<dots> = (\<Sum>p\<in>{p. p permutes ?n}. signof p * (\<Prod>i\<in>?n. ?m ?ab c p i))"
  proof (rule setsum.cong, force)
    fix p
    assume "p \<in> {p. p permutes ?n}"
    hence p: "p permutes ?n" by simp
    show "signof p * (\<Prod>i\<in>?n. ?m a c p i) + signof p * (\<Prod>i\<in>?n. ?m b c p i) = 
      signof p * (\<Prod>i\<in>?n. ?m ?ab c p i)"
      unfolding distrib_left[symmetric]
    proof (rule arg_cong[of _ _ "\<lambda> a. signof p * a"])
      from k have f: "finite ?n" and k': "k \<in> ?n" by auto
      let ?nk = "?n - {k}"
      note split = setprod.remove[OF f k']
      have id1: "(\<Prod>i\<in>?n. ?m a c p i) = ?m a c p k * (\<Prod>i\<in>?nk. ?m a c p i)"
        by (rule split)
      have id2: "(\<Prod>i\<in>?n. ?m b c p i) = ?m b c p k * (\<Prod>i\<in>?nk. ?m b c p i)"
        by (rule split)
      have id3: "(\<Prod>i\<in>?n. ?m ?ab c p i) = ?m ?ab c p k * (\<Prod>i\<in>?nk. ?m ?ab c p i)"
        by (rule split)
      have id: "\<And> a. (\<Prod>i\<in>?nk. ?m a c p i) = (\<Prod>i\<in>?nk. ?c p i)"
        by (rule setprod.cong, insert abc k p, auto intro!: intros)
      have ab: "?ab k \<in> carrier\<^sub>v n" using abc by (auto intro: intros)
      {
        fix f
        assume "f k \<in> (carrier\<^sub>v n :: 'a vec set)"
        hence "mat\<^sub>r n n (\<lambda>i. if i = k then f i else c i) $$ (k, p k) = f k $ p k"
          by (insert p k abc, auto)
      } note first = this
      note id' = id1 id2 id3
      have dist: "(a k \<oplus>\<^sub>v b k) $ p k = a k $ p k + b k $ p k"  
        by (rule vec_index_add(1), insert p k abc, force)
      show "(\<Prod>i\<in>?n. ?m a c p i) + (\<Prod>i\<in>?n. ?m b c p i) = (\<Prod>i\<in>?n. ?m ?ab c p i)"
        unfolding id' id first[of a, OF abc(1)] first[of b, OF abc(2)] first[of ?ab, OF ab] dist
        by (rule distrib_right[symmetric])
    qed 
  qed 
  also have "\<dots> = ?lhs" unfolding det_def by simp
  finally show ?thesis by simp
qed


lemma det_linear_row_finsum:
  assumes fS: "finite S" and c: "c \<in> {0..<n} \<rightarrow> carrier\<^sub>v n" and k: "k < n"
  and a: "a k \<in> S \<rightarrow> carrier\<^sub>v n"
  shows "det (mat\<^sub>r n n (\<lambda> i. if i = k then finsum_vec TYPE('a :: comm_ring_1) n (a i) S else c i)) =
    setsum (\<lambda>j. det (mat\<^sub>r n n (\<lambda> i. if i = k then a  i j else c i))) S"
proof -
  let ?sum = "finsum_vec TYPE('a) n"
  show ?thesis using a
  proof (induct rule: finite_induct[OF fS])
    case 1
    show ?case
      by (simp, unfold finsum_vec_empty, rule det_row_0[OF k c])
  next
    case (2 x F)
    from 2(4) have ak: "a k \<in> F \<rightarrow> carrier\<^sub>v n" and akx: "a k x \<in> carrier\<^sub>v n" by auto    
    {
      fix i
      note if_cong[OF refl finsum_vec_insert[OF 2(1-2)],
        of _ "a i" n "c i" "c i"]
    } note * = this
    show ?case
    proof (subst *)
      show "det (mat\<^sub>r n n (\<lambda>i. if i = k then a i x \<oplus>\<^sub>v ?sum (a i) F else c i)) =
        (\<Sum>j\<in>insert x F. det (mat\<^sub>r n n (\<lambda>i. if i = k then a i j else c i)))"
      proof (subst det_row_add)
        show "det (mat\<^sub>r n n (\<lambda>i. if i = k then a i x else c i)) +
          det (mat\<^sub>r n n (\<lambda>i. if i = k then ?sum (a i) F else c i)) =
        (\<Sum>j\<in>insert x F. det (mat\<^sub>r n n (\<lambda>i. if i = k then a i j else c i)))"
        unfolding 2(3)[OF ak] setsum.insert[OF 2(1-2)] by simp
      qed (insert c k ak akx 2(1), 
        auto intro!: finsum_vec_closed)
    qed (insert akx ak, force+)
  qed
qed


lemma det_linear_rows_finsum_lemma:
  assumes fS: "finite S"
    and fT: "finite T" and c: "c \<in> {0..<n} \<rightarrow> carrier\<^sub>v n"
    and T: "T \<subseteq> {0 ..< n}"
    and a: "a \<in> T \<rightarrow> S \<rightarrow> carrier\<^sub>v n"
  shows "det (mat\<^sub>r n n (\<lambda> i. if i \<in> T then finsum_vec TYPE('a :: comm_ring_1) n (a i) S else c i)) =
    setsum (\<lambda>f. det(mat\<^sub>r n n (\<lambda> i. if i \<in> T then a i (f i) else c i)))
      {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)}"
proof -
  let ?sum = "finsum_vec TYPE('a) n"
  show ?thesis using fT c a T
  proof (induct T arbitrary: a c set: finite)
    case empty
    let ?f = "(\<lambda> i. i) :: nat \<Rightarrow> nat"
    have [simp]: "{f. \<forall>i. f i = i} = {?f}" by auto    
    show ?case by simp
  next
    case (insert z T a c)
    hence z: "z < n" and azS: "a z \<in> S \<rightarrow> carrier\<^sub>v n" by auto
    let ?F = "\<lambda>T. {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)}"
    let ?h = "\<lambda>(y,g) i. if i = z then y else g i"
    let ?k = "\<lambda>h. (h(z),(\<lambda>i. if i = z then i else h i))"
    let ?s = "\<lambda> k a c f. det(mat\<^sub>r n n (\<lambda> i. if i \<in> T then a i (f i) else c i))"
    let ?c = "\<lambda>j i. if i = z then a i j else c i"
    have thif: "\<And>a b c d. (if a \<or> b then c else d) = (if a then c else if b then c else d)"
      by simp
    have thif2: "\<And>a b c d e. (if a then b else if c then d else e) =
       (if c then (if a then b else d) else (if a then b else e))"
      by simp
    from `z \<notin> T` have nz: "\<And>i. i \<in> T \<Longrightarrow> i = z \<longleftrightarrow> False"
      by auto
    from insert have c: "\<And> i. i < n \<Longrightarrow> c i \<in> carrier\<^sub>v n" by auto
    have fin: "finite {f. (\<forall>i\<in>T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)}"
      by (rule finite_bounded_functions[OF fS insert(1)])
    have "det (mat\<^sub>r n n (\<lambda> i. if i \<in> insert z T then ?sum (a i) S else c i)) =
      det (mat\<^sub>r n n (\<lambda> i. if i = z then ?sum (a i) S else if i \<in> T then ?sum (a i) S else c i))"
      unfolding insert_iff thif ..
    also have "\<dots> = (\<Sum>j\<in>S. det (mat\<^sub>r n n (\<lambda> i. if i \<in> T then ?sum (a i) S else if i = z then a i j else c i)))"
      apply (subst det_linear_row_finsum[OF fS _ z])
      prefer 3
      apply (subst thif2)
      using nz
      apply (simp cong del: if_weak_cong cong add: if_cong)
      apply (insert azS c fS insert(5), (force intro!: finsum_vec_closed)+)
      done
    also have "\<dots> = (setsum (\<lambda> (j, f). det (mat\<^sub>r n n (\<lambda> i. if i \<in> T then a i (f i)
      else if i = z then a i j
      else c i))) (S \<times> ?F T))"
      unfolding setsum.cartesian_product[symmetric]
      by (rule setsum.cong[OF refl], subst insert.hyps(3), 
        insert azS c fin z insert(5-6), auto)
    finally have tha:
      "det (mat\<^sub>r n n (\<lambda> i. if i \<in> insert z T then ?sum (a i) S else c i)) =
       (setsum (\<lambda> (j, f). det (mat\<^sub>r n n (\<lambda> i. if i \<in> T then a i (f i)
          else if i = z then a i j
          else c i))) (S \<times> ?F T))" .                
    show ?case unfolding tha
      by (rule setsum.reindex_bij_witness[where i="?k" and j="?h"], insert `z \<notin> T`
      azS c fS insert(5-6) z fin, 
      auto intro!: arg_cong[of _ _ det])
  qed
qed

lemma det_linear_rows_setsum:
  assumes fS: "finite S"
  and a: "a \<in> {0..<n} \<rightarrow> S \<rightarrow> carrier\<^sub>v n"
  shows "det (mat\<^sub>r n n (\<lambda> i. finsum_vec TYPE('a :: comm_ring_1) n (a i) S)) =
    setsum (\<lambda>f. det (mat\<^sub>r n n (\<lambda> i. a i (f i)))) 
    {f. (\<forall>i\<in>{0..<n}. f i \<in> S) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
proof -
  let ?T = "{0..<n}"
  have fT: "finite ?T" by auto
  have th0: "\<And>x y. mat\<^sub>r n n (\<lambda> i. if i \<in> ?T then x i else y i) = mat\<^sub>r n n (\<lambda> i. x i)"
    by (rule mat_row_eqI, auto)
  have c: "(\<lambda> _. \<zero>\<^sub>v n) \<in> ?T \<rightarrow> carrier\<^sub>v n" by auto
  show ?thesis
    by (rule det_linear_rows_finsum_lemma[OF fS fT c subset_refl a, unfolded th0])
qed

lemma det_rows_mul:
  assumes a: "a \<in> {0..<n} \<rightarrow> carrier\<^sub>v n"
  shows "det(mat\<^sub>r n n (\<lambda> i. c i \<odot>\<^sub>v a i)) =
    setprod c {0..<n} * det(mat\<^sub>r n n (\<lambda> i. a i))"
proof -
  have A: "mat\<^sub>r n n (\<lambda> i. c i \<odot>\<^sub>v a i) \<in> carrier\<^sub>m n n" 
  and A': "mat\<^sub>r n n (\<lambda> i. a i) \<in> carrier\<^sub>m n n" using a unfolding mat_carrier_def by auto
  show ?thesis unfolding det_def'[OF A] det_def'[OF A']
  proof (rule trans[OF setsum.cong setsum_right_distrib[symmetric]])
    fix p
    assume p: "p \<in> {p. p permutes {0..<n}}"
    have id: "(\<Prod>ia\<in>{0..<n}. mat\<^sub>r n n (\<lambda>i. c i \<odot>\<^sub>v a i) $$ (ia, p ia))
      = setprod c {0..<n} * (\<Prod>ia\<in>{0..<n}. mat\<^sub>r n n a $$ (ia, p ia))"
      unfolding setprod.distrib[symmetric]
      by (rule setprod.cong, insert p a, force+)
    show "signof p * (\<Prod>ia\<in>{0..<n}. mat\<^sub>r n n (\<lambda>i. c i \<odot>\<^sub>v a i) $$ (ia, p ia)) =
           setprod c {0..<n} * (signof p * (\<Prod>ia\<in>{0..<n}. mat\<^sub>r n n a $$ (ia, p ia)))"
      unfolding id by auto
  qed simp
qed


lemma mat_mul_finsum_alt:
  assumes A: "A \<in> carrier\<^sub>m nr n" and B: "B \<in> carrier\<^sub>m n nc"
  shows "A \<otimes>\<^sub>m B = mat\<^sub>r nr nc (\<lambda> i. finsum_vec TYPE('a :: semiring_0) nc (\<lambda>k. A $$ (i,k) \<odot>\<^sub>v row B k) {0 ..< n})"
  by (rule mat_eqI, insert A B, auto, subst finsum_vec_index, auto simp: scalar_prod_def intro: setsum.cong)


lemma det_mult:
  assumes A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n n"
  shows "det (A \<otimes>\<^sub>m B) = det A * det (B :: 'a :: comm_ring_1 mat)"
proof -
  let ?U = "{0 ..< n}"
  let ?F = "{f. (\<forall>i\<in> ?U. f i \<in> ?U) \<and> (\<forall>i. i \<notin> ?U \<longrightarrow> f i = i)}"
  let ?PU = "{p. p permutes ?U}"
  have fU: "finite ?U" 
    by blast
  have fF: "finite ?F"
    by (rule finite_bounded_functions, auto)
  {
    fix p
    assume p: "p permutes ?U"
    have "p \<in> ?F" unfolding mem_Collect_eq permutes_in_image[OF p]
      using p[unfolded permutes_def] by simp
  }
  then have PUF: "?PU \<subseteq> ?F" by blast
  {
    fix f
    assume fPU: "f \<in> ?F - ?PU"
    have fUU: "f ` ?U \<subseteq> ?U"
      using fPU by auto
    from fPU have f: "\<forall>i \<in> ?U. f i \<in> ?U" "\<forall>i. i \<notin> ?U \<longrightarrow> f i = i" "\<not>(\<forall>y. \<exists>!x. f x = y)"
      unfolding permutes_def by auto
    let ?A = "mat\<^sub>r n n (\<lambda> i. A $$ (i, f i) \<odot>\<^sub>v row B (f i))"
    let ?B = "mat\<^sub>r n n (\<lambda> i. row B (f i))"
    have B': "?B \<in> carrier\<^sub>m n n"
      by (intro mat_row_carrierI)
    {
      assume fi: "inj_on f ?U"
      from inj_on_nat_permutes[OF fi] f
      have "f permutes ?U" by auto
      with fPU have False by simp
    } 
    hence fni: "\<not> inj_on f ?U" by auto
    then obtain i j where ij: "f i = f j" "i \<noteq> j" "i < n" "j < n"
      unfolding inj_on_def by auto
    from ij
    have rth: "row ?B i = row ?B j" by auto
    have "det ?A = 0" 
      by (subst det_rows_mul, unfold det_identical_rows[OF B' ij(2-4) rth], insert f A B, auto)
  }
  then have zth: "\<And> f. f \<in> ?F - ?PU \<Longrightarrow> det (mat\<^sub>r n n (\<lambda> i. A $$ (i, f i) \<odot>\<^sub>v row B (f i))) = 0"
    by simp
  {
    fix p
    assume pU: "p \<in> ?PU"
    from pU have p: "p permutes ?U"
      by blast
    let ?s = "\<lambda>p. (signof p) :: 'a"
    let ?f = "\<lambda>q. ?s p * (\<Prod> i\<in> ?U. A $$ (i,p i)) * (?s q * (\<Prod>i\<in> ?U. B $$ (i, q i)))"
    have "(setsum (\<lambda>q. ?s q *
        (\<Prod>i\<in> ?U. mat\<^sub>r n n (\<lambda> i. A $$ (i, p i) \<odot>\<^sub>v row B (p i)) $$ (i, q i))) ?PU) =
      (setsum (\<lambda>q. ?s p * (\<Prod> i\<in> ?U. A $$ (i,p i)) * (?s q * (\<Prod> i\<in> ?U. B $$ (i, q i)))) ?PU)"
      unfolding sum_permutations_compose_right[OF permutes_inv[OF p], of ?f]
    proof (rule setsum.cong[OF refl])
      fix q
      assume "q \<in> {q. q permutes ?U}"
      hence q: "q permutes ?U" by simp
      from p q have pp: "permutation p" and pq: "permutation q"
        unfolding permutation_permutes by auto
      note sign = signof_compose[OF q permutes_inv[OF p], unfolded signof_inv[OF fU p]]
      let ?inv = "Hilbert_Choice.inv"
      have th001: "setprod (\<lambda>i. B$$ (i, q (?inv p i))) ?U = setprod ((\<lambda>i. B$$ (i, q (?inv p i))) \<circ> p) ?U"
        by (rule setprod.permute[OF p])
      have thp: "setprod (\<lambda>i. mat\<^sub>r n n (\<lambda> i. A$$(i,p i) \<odot>\<^sub>v row B (p i)) $$ (i, q i)) ?U =
        setprod (\<lambda>i. A$$(i,p i)) ?U * setprod (\<lambda>i. B$$ (i, q (?inv p i))) ?U"
        unfolding th001 o_def permutes_inverses[OF p]
        by (subst setprod.distrib[symmetric], insert A p q B, auto intro: setprod.cong)
      def AA \<equiv> "\<Prod>i\<in>?U. A $$ (i, p i)"
      def BB \<equiv> "\<Prod>ia\<in>{0..<n}. B $$ (ia, q (?inv p ia))"
      have "?s q * (\<Prod>ia\<in>{0..<n}. mat\<^sub>r n n (\<lambda>i. A $$ (i, p i) \<odot>\<^sub>v row B (p i)) $$ (ia, q ia)) =
         ?s p * (\<Prod>i\<in>{0..<n}. A $$ (i, p i)) * (?s (q \<circ> ?inv p) * (\<Prod>ia\<in>{0..<n}. B $$ (ia, q (?inv p ia))))"
        unfolding sign thp
        unfolding AA_def[symmetric] BB_def[symmetric]
        by (simp add: ac_simps signof_def)
      thus "?s q * (\<Prod>i = 0..<n. mat\<^sub>r n n (\<lambda>i. A $$ (i, p i) \<odot>\<^sub>v row B (p i)) $$ (i, q i)) =
         ?s p * (\<Prod>i = 0..<n. A $$ (i, p i)) *
         (?s (q \<circ> ?inv p) * (\<Prod>i = 0..<n. B $$ (i, (q \<circ> ?inv p) i)))" by simp
    qed 
  } note * = this
  have th2: "setsum (\<lambda>f. det (mat\<^sub>r n n (\<lambda> i. A$$(i,f i) \<odot>\<^sub>v row B (f i)))) ?PU = det A * det B"
    unfolding det_def'[OF A] det_def'[OF B] det_def'[OF mat_row_carrierI]
    unfolding setsum_product mat_dim_row_mat
    by (rule setsum.cong, insert A, force, subst *, insert A B, auto)
  let ?f = "\<lambda> f. det (mat\<^sub>r n n (\<lambda> i. A $$ (i, f i) \<odot>\<^sub>v row B (f i)))"
  have "det (A \<otimes>\<^sub>m B) = setsum ?f ?F"
    unfolding mat_mul_finsum_alt[OF A B]
    by (rule det_linear_rows_setsum[OF fU], insert A B, auto)
  also have "\<dots> = setsum ?f ((?F - ?PU) \<union> (?F \<inter> ?PU))"
    by (rule arg_cong[where f = "setsum ?f"], auto)
  also have "\<dots> = setsum ?f (?F - ?PU) + setsum ?f (?F \<inter> ?PU)"
    by (rule setsum.union_disjoint, insert A B finite_bounded_functions[OF fU fU], auto)
  also have "setsum ?f (?F - ?PU) = 0"
    by (rule setsum.neutral, insert zth, auto)
  also have "?F \<inter> ?PU = ?PU" unfolding permutes_def by fastforce
  also have "setsum ?f ?PU = det A * det B"
    unfolding th2 ..
  finally show ?thesis by simp
qed

lemma unit_imp_det_non_zero: assumes "A \<in> Units (ring\<^sub>m TYPE('a :: comm_ring_1) n b)"
   shows "det A \<noteq> 0"
proof -
  from assms[unfolded Units_def mat_ring_def]
  obtain B where A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n n" and BA: "B \<otimes>\<^sub>m A = \<one>\<^sub>m n" by auto
  from arg_cong[OF BA, of det, unfolded det_mult[OF B A] det_one]
  show ?thesis by auto
qed

text \<open>The following proof is based on the Gauss-Jordan algorithm.\<close>

lemma det_non_zero_imp_unit: assumes A: "A \<in> carrier\<^sub>m n n"
  and dA: "det A \<noteq> (0 :: 'a :: field)"
  shows "A \<in> Units (ring\<^sub>m TYPE('a) n b)"
proof (rule ccontr)
  let ?g = "gauss_jordan A (\<zero>\<^sub>m n 0)"
  let ?B = "fst ?g"
  obtain B C where B: "?g = (B,C)" by (cases ?g)
  assume "\<not> ?thesis"
  from this[unfolded gauss_jordan_check_invertable[OF A mat_zero_closed[of n 0]] B]
  have "B \<noteq> \<one>\<^sub>m n" by auto
  with row_echelon_form_imp_1_or_0_row[OF gauss_jordan_carrier(1)[OF A _ B] gauss_jordan_row_echelon[OF A B], of 0]
  have n: "0 < n" and row: "row B (n - 1) = \<zero>\<^sub>v n" by auto
  let ?n = "n - 1"
  from n have n1: "?n < n" by auto
  from gauss_jordan_transform[OF A _ B, of 0 b] obtain P
    where P: "P\<in>Units (ring\<^sub>m TYPE('a) n b)" and PA: "B = P \<otimes>\<^sub>m A" by auto
  from unit_imp_det_non_zero[OF P] have dP: "det P \<noteq> 0" by auto
  from P have P: "P \<in> carrier\<^sub>m n n" unfolding Units_def mat_ring_def by auto
  from det_mult[OF P A] dP dA have "det B \<noteq> 0" unfolding PA by simp
  also have "det B = 0" 
  proof -
    from gauss_jordan_carrier[OF A _ B, of 0] have B: "B \<in> carrier\<^sub>m n n" by auto
    {
      fix j
      assume j: "j < n"
      from row_index(1)[symmetric, of ?n B j, unfolded row] B
      have "B $$ (?n, j) = 0" using B n j by auto
    }
    hence "B = mat\<^sub>r n n (\<lambda>i. if i = ?n then \<zero>\<^sub>v n else row B i)"
      by (intro mat_eqI, insert B, auto)
    also have "det \<dots> = 0"
      by (rule det_row_0[OF n1], insert B, auto)
    finally show "det B = 0" .
  qed 
  finally show False by simp
qed

lemma mat_mult_left_right_inverse: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n" 
  and B: "B \<in> carrier\<^sub>m n n" and AB: "A \<otimes>\<^sub>m B = \<one>\<^sub>m n"
  shows "B \<otimes>\<^sub>m A = \<one>\<^sub>m n"
proof -
  let ?R = "ring\<^sub>m TYPE('a) n undefined"
  from det_mult[OF A B, unfolded AB] have "det A \<noteq> 0" "det B \<noteq> 0" by auto
  from det_non_zero_imp_unit[OF A this(1)] det_non_zero_imp_unit[OF B this(2)]  
  have U: "A \<in> Units ?R" "B \<in> Units ?R" .
  interpret ring ?R by (rule mat_ring)
  from Units_inv_comm[unfolded mat_ring_simps, OF AB U] show ?thesis .
qed

lemma det_zero_imp_zero_row: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n"
  and det: "det A = 0"
  shows "\<exists> P. P \<in> Units (ring\<^sub>m TYPE('a) n b) \<and> row (P \<otimes>\<^sub>m A) (n - 1) = \<zero>\<^sub>v n \<and> 0 < n
    \<and> row_echelon_form (P \<otimes>\<^sub>m A)"
proof -
  let ?R = "ring\<^sub>m TYPE('a) n b"
  let ?U = "Units ?R"
  interpret m: ring ?R by (rule mat_ring)
  let ?g = "gauss_jordan A A"
  obtain A' B' where g: "?g = (A', B')" by (cases ?g)
  from det unit_imp_det_non_zero[of A n b] have AU: "A \<notin> ?U" by auto
  with gauss_jordan_inverse_one_direction(1)[OF A A, of _ b]
  have A'1: "A' \<noteq> \<one>\<^sub>m n" using g by auto
  from gauss_jordan_carrier(1)[OF A A g] have A': "A' \<in> carrier\<^sub>m n n" by auto
  from gauss_jordan_row_echelon[OF A g] have re: "row_echelon_form A'" .
  from row_echelon_form_imp_1_or_0_row[OF A' this] A'1
  have n: "0 < n" and row: "row A' (n - 1) = \<zero>\<^sub>v n" by auto
  from gauss_jordan_transform[OF A A g, of b] obtain P
    where P: "P \<in> ?U" and A': "A' = P \<otimes>\<^sub>m A" by auto
  thus ?thesis using n row re by auto
qed

lemma det_0_iff_vec_prod_zero_field: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n"
  shows "det A = 0 \<longleftrightarrow> (\<exists> v. v \<in> carrier\<^sub>v n \<and> v \<noteq> \<zero>\<^sub>v n \<and> A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n)" (is "?l = (\<exists> v. ?P v)")
proof -
  let ?R = "ring\<^sub>m TYPE('a) n ()"
  let ?U = "Units ?R"
  interpret m: ring ?R by (rule mat_ring)
  show ?thesis
  proof (cases "det A = 0")
    case False
    from det_non_zero_imp_unit[OF A this, of "()"]
    have "A \<in> ?U" .
    then obtain B where unit: "B \<otimes>\<^sub>m A = \<one>\<^sub>m n" and B: "B \<in> carrier\<^sub>m n n"
      unfolding Units_def mat_ring_def by auto
    {
      fix v
      assume "?P v"
      hence v: "v \<in> carrier\<^sub>v n" "v \<noteq> \<zero>\<^sub>v n" "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
      have "v = (B \<otimes>\<^sub>m A) \<otimes>\<^sub>m\<^sub>v v" using v B unfolding unit by auto
      also have "\<dots> = B \<otimes>\<^sub>m\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" using B A v by simp
      also have "\<dots> = B \<otimes>\<^sub>m\<^sub>v \<zero>\<^sub>v n" unfolding v ..
      also have "\<dots> = \<zero>\<^sub>v n" using B by auto
      finally have False using v by simp
    }
    with False show ?thesis by blast
  next
    case True
    let ?n = "n - 1"
    from det_zero_imp_zero_row[OF A True, of "()"]
    obtain P where PU: "P \<in> ?U" and row: "row (P \<otimes>\<^sub>m A) ?n = \<zero>\<^sub>v n" and n: "0 < n" "?n < n"
      and re: "row_echelon_form (P \<otimes>\<^sub>m A)" by auto
    def PA \<equiv> "P \<otimes>\<^sub>m A"
    note row = row[folded PA_def]
    note re = re[folded PA_def]
    from PU obtain Q where P: "P \<in> carrier\<^sub>m n n" and Q: "Q \<in> carrier\<^sub>m n n"
      and unit: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "P \<otimes>\<^sub>m Q =  \<one>\<^sub>m n" unfolding Units_def mat_ring_def by auto    
    from P A have PA: "PA \<in> carrier\<^sub>m n n" and dimPA: "dim\<^sub>r PA = n" unfolding PA_def by auto
    from re[unfolded row_echelon_form_def] obtain p where p: "pivot_fun PA p n" using PA by auto 
    note piv = pivot_positions[OF PA p]
    note pivot = pivot_funD[OF dimPA p n(2)]
    {
      assume "p ?n < n"
      with pivot(4)[OF this] n arg_cong[OF row, of "\<lambda> v. v $ p ?n"] have False using PA by auto
    }
    with pivot(1) have pn: "p ?n = n" by fastforce
    with piv(1) have "set (pivot_positions PA) \<subseteq>  {(i, p i) |i. i < n \<and> p i \<noteq> n} - {(?n,p ?n)}" by auto
    also have "\<dots> \<subseteq> {(i, p i) | i. i < ?n}" using n by force
    finally have "card (set (pivot_positions PA)) \<le> card {(i, p i) | i. i < ?n}"
      by (intro card_mono, auto)
    also have "{(i, p i) | i. i < ?n} = (\<lambda> i. (i, p i)) ` {0 ..< ?n}" by auto
    also have "card \<dots> = card {0 ..< ?n}" by (rule card_image, auto simp: inj_on_def)
    also have "\<dots> < n" using n by simp
    finally have "card (set (pivot_positions PA)) < n" .
    hence "card (snd ` (set (pivot_positions PA))) < n" 
      using card_image_le[OF finite_set, of snd "pivot_positions PA"] by auto
    hence neq: "snd ` (set (pivot_positions PA)) \<noteq> {0 ..< n}" by auto
    from find_base_vector[OF re PA neq] obtain v where v: "v \<in> carrier\<^sub>v n"
      and v0: "v \<noteq> \<zero>\<^sub>v n" and pav: "PA \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
    have "A \<otimes>\<^sub>m\<^sub>v v = Q \<otimes>\<^sub>m P \<otimes>\<^sub>m\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" unfolding unit using A v by auto
    also have "\<dots> = Q \<otimes>\<^sub>m\<^sub>v (PA \<otimes>\<^sub>m\<^sub>v v)" unfolding PA_def using Q P A v by auto
    also have "PA \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" unfolding pav ..
    also have "Q \<otimes>\<^sub>m\<^sub>v \<zero>\<^sub>v n = \<zero>\<^sub>v n" using Q by auto
    finally have Av: "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
    show ?thesis unfolding True using Av v0 v by auto
  qed
qed

text \<open>In order to get the result for integral domains, we embed the domain in its
  fraction field, and then apply the result for fields.\<close>
lemma det_0_iff_vec_prod_zero: assumes A: "(A :: 'a :: idom mat) \<in> carrier\<^sub>m n n"
  shows "det A = 0 \<longleftrightarrow> (\<exists> v. v \<in> carrier\<^sub>v n \<and> v \<noteq> \<zero>\<^sub>v n \<and> A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n)"
proof -
  let ?h = "embed_ff :: 'a \<Rightarrow> 'a fract"
  let ?A = "map\<^sub>m ?h A"
  have A': "?A \<in> carrier\<^sub>m n n" using A by auto
  interpret inj_ring_hom ?h by (rule embed_ff)
  have "(det A = 0) = (?h (det A) = ?h 0)" using hom_inj by auto
  also have "\<dots> = (det ?A = 0)" unfolding hom_zero hom_det ..
  also have "\<dots> = ((\<exists> v. v \<in> carrier\<^sub>v n \<and> v \<noteq> \<zero>\<^sub>v n \<and> ?A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n))"
    unfolding det_0_iff_vec_prod_zero_field[OF A'] ..
  also have "\<dots> = ((\<exists> v. v \<in> carrier\<^sub>v n \<and> v \<noteq> \<zero>\<^sub>v n \<and> A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n))" (is "?l = ?r")
  proof
    assume ?r
    then obtain v where v: "v \<in> carrier\<^sub>v n" "v \<noteq> \<zero>\<^sub>v n" "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
    show ?l
      by (rule exI[of _ "map\<^sub>v ?h v"], insert v, auto simp: mat_vec_mult_hom[symmetric, OF A v(1)])
  next
    assume ?l
    then obtain v where v: "v \<in> carrier\<^sub>v n" and v0: "v \<noteq> \<zero>\<^sub>v n" and Av: "?A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
    have "\<forall> i. \<exists> a b. v $ i = Fraction_Field.Fract a b \<and> b \<noteq> 0" using Fract_cases[of "v $ i" for i] by metis
    from choice[OF this] obtain a where "\<forall> i. \<exists> b. v $ i = Fraction_Field.Fract (a i) b \<and> b \<noteq> 0" by metis
    from choice[OF this] obtain b where vi: "\<And> i. v $ i = Fraction_Field.Fract (a i) (b i)" and bi: "\<And> i. b i \<noteq> 0" by auto
    def m \<equiv> "listprod (map b [0..<n])"
    let ?m = "?h m"
    have m0: "m \<noteq> 0" unfolding m_def hom_0_iff listprod_zero_iff using bi by auto
    from v0[unfolded vec_eq_iff] v obtain i where i: "i < n" "v $ i \<noteq> 0" by auto
    {
      fix i
      assume "i < n"
      hence "b i \<in> set (map b [0 ..< n])" by auto
      from split_list[OF this]
        obtain ys zs where "map b [0..<n] = ys @ b i # zs" by auto
      hence "b i dvd m" unfolding m_def by auto
      then obtain c where "m = b i * c" ..
      hence "?m * v $ i = ?h (a i * c)" unfolding vi using bi[of i]
        by (simp add: eq_fract embed_ff_def)
      hence "\<exists> c. ?m * v $ i = ?h c" ..
    }
    hence "\<forall> i. \<exists> c. i < n \<longrightarrow> ?m * v $ i = ?h c" by auto
    from choice[OF this] obtain c where c: "\<And> i. i < n \<Longrightarrow> ?m * v $ i = ?h (c i)" by auto
    def w \<equiv> "vec n c"
    have w: "w \<in> carrier\<^sub>v n" unfolding w_def by simp
    have mvw: "?m \<odot>\<^sub>v v = map_vec ?h w" unfolding w_def using c v
      by (intro vec_eqI, auto)
    with m0 i c[OF i(1)] have "w $ i \<noteq> 0" unfolding w_def by auto
    with i w have w0: "w \<noteq> \<zero>\<^sub>v n" by auto
    from arg_cong[OF Av, of "\<lambda> v. ?m \<odot>\<^sub>v v"]
    have "?m \<odot>\<^sub>v (?A \<otimes>\<^sub>m\<^sub>v v) = map\<^sub>v ?h (\<zero>\<^sub>v n)" by auto
    also have "?m \<odot>\<^sub>v (?A \<otimes>\<^sub>m\<^sub>v v) = ?A \<otimes>\<^sub>m\<^sub>v (?m \<odot>\<^sub>v v)" using A v by auto
    also have "\<dots> = ?A \<otimes>\<^sub>m\<^sub>v (map\<^sub>v ?h w)" unfolding mvw ..
    also have "\<dots> = map\<^sub>v ?h (A \<otimes>\<^sub>m\<^sub>v w)" unfolding mat_vec_mult_hom[OF A w] ..
    finally have "A \<otimes>\<^sub>m\<^sub>v w = \<zero>\<^sub>v n" by (rule vec_hom_inj)
    with w w0 show ?r by blast
  qed
  finally show ?thesis .
qed

lemma det_0_negate: assumes  A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n"
  shows "(det (\<ominus>\<^sub>m A) = 0) = (det A = 0)"
proof -
  from A have mA: "\<ominus>\<^sub>m A \<in> carrier\<^sub>m n n" by auto
  {
    fix v :: "'a vec"
    assume v: "v \<in> carrier\<^sub>v n"
    hence Av: "A \<otimes>\<^sub>m\<^sub>v v \<in> carrier\<^sub>v n" using A by auto
    have id: "\<ominus>\<^sub>m A \<otimes>\<^sub>m\<^sub>v v = \<ominus>\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" using v A by simp
    have "(\<ominus>\<^sub>m A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n) = (A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n)" unfolding id 
      unfolding uminus_vec_zero_eq[OF Av] ..
  }
  thus ?thesis unfolding det_0_iff_vec_prod_zero[OF A] det_0_iff_vec_prod_zero[OF mA] by auto
qed
  
lemma det_multrow: 
  assumes k: "k < n" and A: "A \<in> carrier\<^sub>m n n"
  shows "det (multrow k a A) = a * det A"
proof -
  have "multrow k a A = multrow_mat n k a \<otimes>\<^sub>m A"
    by (rule multrow_mat[OF A])
  also have "det (multrow_mat n k a \<otimes>\<^sub>m A) = det (multrow_mat n k a) * det A"
    by (rule det_mult[OF _ A], auto)
  also have "det (multrow_mat n k a) = a"
    by (rule det_multrow_mat[OF k])
  finally show ?thesis .
qed

lemma det_multrow_div:
  assumes k: "k < n" and A: "A \<in> carrier\<^sub>m n n" and a0: "a \<noteq> 0"
  shows "det (multrow k a A :: 'a :: ring_div mat) div a = det A"
proof -
  have "det (multrow k a A) div a = a * det A div a" using k A by (simp add: det_multrow)
  also have "... = det A" using a0 by auto
  finally show ?thesis.
qed

lemma det_addrow: 
  assumes l: "l < n" and k: "k \<noteq> l" and A: "A \<in> carrier\<^sub>m n n"
  shows "det (addrow a k l A) = det A"
proof -
  have "addrow a k l A = addrow_mat n a k l \<otimes>\<^sub>m A"
    by (rule addrow_mat[OF A l])
  also have "det (addrow_mat n a k l \<otimes>\<^sub>m A) = det (addrow_mat n a k l) * det A"
    by (rule det_mult[OF _ A], auto)
  also have "det (addrow_mat n a k l) = 1"
    by (rule det_addrow_mat[OF k])
  finally show ?thesis using A by simp
qed

lemma det_swaprows: 
  assumes *: "k < n" "l < n" and k: "k \<noteq> l" and A: "A \<in> carrier\<^sub>m n n"
  shows "det (swaprows k l A) = - det A"
proof -
  have "swaprows k l A = swaprows_mat n k l \<otimes>\<^sub>m A"
    by (rule swaprows_mat[OF A *])
  also have "det (swaprows_mat n k l \<otimes>\<^sub>m A) = det (swaprows_mat n k l) * det A"
    by (rule det_mult[OF _ A], insert A, auto)
  also have "det (swaprows_mat n k l) = - 1"
    by (rule det_swaprows_mat[OF * k])
  finally show ?thesis using A by simp
qed

lemma det_similar: assumes "mat_similar A B" 
  shows "det A = det B"
proof -
  from mat_similarD[OF assms] obtain n P Q where
  carr: "{A, B, P, Q} \<subseteq> carrier\<^sub>m n n" (is "_ \<subseteq> ?C")
  and PQ: "P \<otimes>\<^sub>m Q = \<one>\<^sub>m n" 
  and AB: "A = P \<otimes>\<^sub>m B \<otimes>\<^sub>m Q" by blast
  hence A: "A \<in> ?C" and B: "B \<in> ?C" and P: "P \<in> ?C" and Q: "Q \<in> ?C" by auto  
  from det_mult[OF P Q, unfolded PQ] have PQ: "det P * det Q = 1" by auto
  from det_mult[OF _ Q, of "P \<otimes>\<^sub>m B", unfolded det_mult[OF P B] AB[symmetric]] P B
  have "det A = det P * det B * det Q" by auto
  also have "\<dots> = (det P * det Q) * det B" by (simp add: ac_simps)
  also have "\<dots> = det B" unfolding PQ by simp
  finally show ?thesis .
qed

lemma det_four_block_mat_upper_right_zero_col: assumes A1: "A1 \<in> carrier\<^sub>m n n"
  and A20: "A2 = (\<zero>\<^sub>m n 1)" and A3: "A3 \<in> carrier\<^sub>m 1 n"
  and A4: "A4 \<in> carrier\<^sub>m 1 1"
  shows "det (four_block_mat A1 A2 A3 A4) = det A1 * det A4" (is "det ?A = _")
proof -
  let ?A = "four_block_mat A1 A2 A3 A4"
  from A20 have A2: "A2 \<in> carrier\<^sub>m n 1" by auto  
  def A \<equiv> ?A
  from four_block_mat_carrier[OF A1 A4] A1
  have A: "A \<in> carrier\<^sub>m (Suc n) (Suc n)" and dim: "dim\<^sub>r A1 = n" unfolding A_def by auto
  let ?Pn = "\<lambda> p. p permutes {0 ..< n}"
  let ?Psn = "\<lambda> p. p permutes {0 ..< Suc n}"
  let ?perm = "{p. ?Psn p}"
  let ?permn = "{p. ?Pn p}"
  let ?prod = "\<lambda> p. signof p * (\<Prod>i = 0..<Suc n. A $$ (p i, i))"
  let ?prod' = "\<lambda> p. A $$ (p n, n) * signof p * (\<Prod>i = 0..<n. A $$ (p i, i))"
  let ?prod'' = "\<lambda> p. signof p * (\<Prod>i = 0..< n. A $$ (p i, i))"
  let ?prod''' = "\<lambda> p. signof p * (\<Prod>i = 0..< n. A1 $$ (p i, i))"
  let ?p0 = "{p. p 0 = 0}"
  have [simp]: "{0..<Suc n} - {n} = {0..< n}" by auto
  {
    fix p
    assume "?Psn p"
    have "?prod p = signof p * (A $$ (p n, n) * (\<Prod> i \<in> {0..< n}. A $$ (p i, i)))"
      by (subst setprod.remove[of _ n], auto)
    also have "\<dots> = A $$ (p n, n) * signof p * (\<Prod> i \<in> {0..< n}. A $$ (p i, i))" by simp
    finally have "?prod p = ?prod' p" .
  } note prod_id = this
  def prod' \<equiv> ?prod'
  {
    fix i q
    assume i: "i \<in> {0..< n}" "q permutes {0 ..< n}"
    hence "Fun.swap n i id (q n) < n" 
      unfolding permutes_def by auto
    hence "A $$ (Fun.swap n i id (q n), n) = 0"
      unfolding A_def using A1 A20 A3 A4 by auto
    hence "prod' (Fun.swap n i id \<circ> q) = 0"
      unfolding prod'_def by simp 
  } note zero = this
  have cong: "\<And> a b c. b = c \<Longrightarrow> a * b = a * c" by auto
  have "det ?A = setsum ?prod ?perm"
    unfolding A_def[symmetric] using mat_det_left_def[OF A] A by simp
  also have "\<dots> = setsum prod' ?perm" unfolding prod'_def
    by (rule setsum.cong[OF refl], insert prod_id, auto)
  also have "{0 ..< Suc n} = insert n {0 ..< n}" by auto
  also have "setsum prod' {p. p permutes \<dots>} = 
    (\<Sum>i\<in>insert n {0..<n}. \<Sum>q\<in>?permn. prod' (Fun.swap n i id \<circ> q))"
    by (subst setsum_over_permutations_insert, auto)
  also have "\<dots> = (\<Sum>q\<in>?permn. prod' q) +
    (\<Sum>i\<in>{0..<n}. \<Sum>q\<in>?permn. prod' (Fun.swap n i id \<circ> q))"
    by (subst setsum.insert, auto)
  also have "(\<Sum>i\<in>{0..<n}. \<Sum>q\<in>?permn. prod' (Fun.swap n i id \<circ> q)) = 0"
    by (rule setsum.neutral, intro ballI, rule setsum.neutral, intro ballI, rule zero, auto)
  also have "(\<Sum>q\<in> ?permn. prod' q) = A $$ (n,n) * (\<Sum>q\<in> ?permn. ?prod'' q)"
    unfolding prod'_def
    by (subst setsum_right_distrib, rule setsum.cong[OF refl], auto simp: permutes_def ac_simps)
  also have "A $$ (n,n) = A4 $$ (0,0)" unfolding A_def using A1 A2 A3 A4 by auto
  also have "(\<Sum>q\<in> ?permn. ?prod'' q) = (\<Sum>q\<in> ?permn. ?prod''' q)" 
    by (rule setsum.cong[OF refl], rule cong, rule setprod.cong,
    insert A1 A2 A3 A4, auto simp: permutes_def A_def)
  also have "\<dots> = det A1"
    unfolding mat_det_left_def[OF A1] dim by auto
  also have "A4 $$ (0,0) = det A4"
    using A4 unfolding det_def[of A4] by (auto simp: signof_def sign_def)
  finally show ?thesis by simp
qed

lemma det_swapcols: 
  assumes *: "k < n" "l < n" "k \<noteq> l" and A: "A \<in> carrier\<^sub>m n n"
  shows "det (swapcols k l A) = - det A"
proof -
  let ?B = "transpose\<^sub>m A"
  let ?C = "swaprows k l ?B"
  let ?D = "transpose\<^sub>m ?C"
  have C: "?C \<in> carrier\<^sub>m n n" and B: "?B \<in> carrier\<^sub>m n n"
    unfolding mat_transpose_closed swaprows_closed using A by auto
  show ?thesis 
    unfolding 
      swapcols_is_transp_swap_rows[OF A *(1-2)]
      det_transpose[OF C] det_swaprows[OF * B] det_transpose[OF A] ..
qed


lemma swap_row_to_front_det: "A \<in> carrier\<^sub>m n n \<Longrightarrow> I < n \<Longrightarrow> det (swap_row_to_front A I)
  = (-1)^I * det A"
proof (induct I arbitrary: A)
  case (Suc I A)
  from Suc(3) have I: "I < n" by auto
  let ?I = "Suc I"
  let ?A = "swaprows I ?I A"
  have AA: "?A \<in> carrier\<^sub>m n n" using Suc(2) by simp
  have "det (swap_row_to_front A (Suc I)) = det (swap_row_to_front ?A I)" by simp
  also have "\<dots> = (-1)^I * det ?A" by (rule Suc(1)[OF AA I])
  also have "det ?A = -1 * det A" using det_swaprows[OF I Suc(3) _ Suc(2)] by simp
  finally show ?case by simp
qed simp

lemma swap_col_to_front_det: "A \<in> carrier\<^sub>m n n \<Longrightarrow> I < n \<Longrightarrow> det (swap_col_to_front A I)
  = (-1)^I * det A"
proof (induct I arbitrary: A)
  case (Suc I A)
  from Suc(3) have I: "I < n" by auto
  let ?I = "Suc I"
  let ?A = "swapcols I ?I A"
  have AA: "?A \<in> carrier\<^sub>m n n" using Suc(2) by simp
  have "det (swap_col_to_front A (Suc I)) = det (swap_col_to_front ?A I)" by simp
  also have "\<dots> = (-1)^I * det ?A" by (rule Suc(1)[OF AA I])
  also have "det ?A = -1 * det A" using det_swapcols[OF I Suc(3) _ Suc(2)] by simp
  finally show ?case by simp
qed simp


lemma swap_row_to_front_four_block: assumes A1: "A1 \<in> carrier\<^sub>m n m1"
  and A2: "A2 \<in> carrier\<^sub>m n m2" 
  and A3: "A3 \<in> carrier\<^sub>m 1 m1" 
  and A4: "A4 \<in> carrier\<^sub>m 1 m2"
  shows "swap_row_to_front (four_block_mat A1 A2 A3 A4) n = four_block_mat A3 A4 A1 A2"
  by (subst swap_row_to_front_result[OF four_block_mat_carrier[OF A1 A4]], force,
  rule mat_eqI, insert A1 A2 A3 A4, auto)

lemma swap_col_to_front_four_block: assumes A1: "A1 \<in> carrier\<^sub>m n1 m"
  and A2: "A2 \<in> carrier\<^sub>m n1 1" 
  and A3: "A3 \<in> carrier\<^sub>m n2 m" 
  and A4: "A4 \<in> carrier\<^sub>m n2 1"
  shows "swap_col_to_front (four_block_mat A1 A2 A3 A4) m = four_block_mat A2 A1 A4 A3"
  by (subst swap_col_to_front_result[OF four_block_mat_carrier[OF A1 A4]], force,
  rule mat_eqI, insert A1 A2 A3 A4, auto)

lemma det_four_block_mat_lower_right_zero_col: assumes A1: "A1 \<in> carrier\<^sub>m 1 n"
  and A2: "A2 \<in> carrier\<^sub>m 1 1"
  and A3: "A3 \<in> carrier\<^sub>m n n"
  and A40: "A4 = (\<zero>\<^sub>m n 1)" 
  shows "det (four_block_mat A1 A2 A3 A4) = (-1)^n * det A2 * det A3" (is "det ?A = _")
proof -
  let ?B = "four_block_mat A3 A4 A1 A2"
  from four_block_mat_carrier[OF A3 A2]
  have B: "?B \<in> carrier\<^sub>m (Suc n) (Suc n)" by simp
  from A40 have A4: "A4 \<in> carrier\<^sub>m n 1" by auto
  from arg_cong[OF swap_row_to_front_four_block[OF A3 A4 A1 A2], of det]
    swap_row_to_front_det[OF B, of n]
  have "det ?A = (-1)^n * det ?B" by auto
  also have "det ?B = det A3 * det A2"
    by (rule det_four_block_mat_upper_right_zero_col[OF A3 A40 A1 A2])
  finally show ?thesis by simp
qed
  
lemma det_four_block_mat_lower_left_zero_col: assumes A1: "A1 \<in> carrier\<^sub>m 1 1"
  and A2: "A2 \<in> carrier\<^sub>m 1 n"
  and A30: "A3 = (\<zero>\<^sub>m n 1)" 
  and A4: "A4 \<in> carrier\<^sub>m n n"
  shows "det (four_block_mat A1 A2 A3 A4) = det A1 * det A4" (is "det ?A = _")
proof -
  from A30 have A3: "A3 \<in> carrier\<^sub>m n 1" by auto
  let ?B = "four_block_mat A2 A1 A4 A3"
  from four_block_mat_carrier[OF A2 A3]
  have B: "?B \<in> carrier\<^sub>m (Suc n) (Suc n)" by simp
  from arg_cong[OF swap_col_to_front_four_block[OF A2 A1 A4 A3], of det]
    swap_col_to_front_det[OF B, of n]
  have "det ?A = (-1)^n * det ?B" by auto
  also have "det ?B = (- 1) ^ n * det A1 * det A4"
    by (rule det_four_block_mat_lower_right_zero_col[OF A2 A1 A4 A30])
  also have "(-1)^n * \<dots> = (-1 * -1)^n * det A1 * det A4"
    unfolding power_mult_distrib by simp
  finally show ?thesis by simp
qed

lemma det_addcol[simp]: 
  assumes l: "l < n" and k: "k \<noteq> l" and A: "A \<in> carrier\<^sub>m n n"
  shows "det (addcol a k l A) = det A"
proof -
  have "addcol a k l A = A \<otimes>\<^sub>m addrow_mat n a l k"
    using addcol_mat[OF A l].
  also have "det (A \<otimes>\<^sub>m addrow_mat n a l k) = det A * det (addrow_mat n a l k)"
    by(rule det_mult[OF A], auto)
  also have "det (addrow_mat n a l k) = 1"
    using det_addrow_mat[OF k[symmetric]].
  finally show ?thesis using A by simp
qed

definition "insert_index i \<equiv> \<lambda>i'. if i' < i then i' else Suc i'"

definition "delete_index i \<equiv> \<lambda>i'. if i' < i then i' else i' - Suc 0"

lemma insert_index[simp]:
  "i' < i \<Longrightarrow> insert_index i i' = i'"
  "i' \<ge> i \<Longrightarrow> insert_index i i' = Suc i'"
unfolding insert_index_def by auto


lemma delete_insert_index[simp]:
  "delete_index i (insert_index i i') = i'"
  unfolding insert_index_def delete_index_def by auto

lemma insert_delete_index:
  assumes i'i: "i' \<noteq> i"
  shows "insert_index i (delete_index i i') = i'"
  unfolding insert_index_def delete_index_def using i'i by auto

definition "delete_dom p i \<equiv> \<lambda>i'. p (insert_index i i')"

definition "delete_ran p j \<equiv> \<lambda>i. delete_index j (p i)"

definition "permutation_delete p i = delete_ran (delete_dom p i) (p i)"

definition "insert_ran p j \<equiv> \<lambda>i. insert_index j (p i)"

definition "insert_dom p i j \<equiv>
  \<lambda>i'. if i' < i then p i' else if i' = i then j else p (i'-1)"

definition "permutation_insert i j p \<equiv> insert_dom (insert_ran p j) i j"

lemmas permutation_delete_expand =
  permutation_delete_def[unfolded delete_dom_def delete_ran_def insert_index_def delete_index_def]

lemmas permutation_insert_expand =
  permutation_insert_def[unfolded insert_dom_def insert_ran_def insert_index_def delete_index_def]

lemma permutation_insert_inserted[simp]:
  "permutation_insert (i::nat) j p i = j"
  unfolding permutation_insert_expand by auto

lemma permutation_insert_base:
  assumes p: "p permutes {0..<n}"
  shows "permutation_insert n n p = p"
proof (rule ext)
  fix x show "permutation_insert n n p x = p x"
    apply (cases rule: linorder_cases[of "x" "n"])
    unfolding permutation_insert_expand
    using permutes_others[OF p] p by auto
qed

lemma permutation_insert_row_step:
  shows "permutation_insert (Suc i) j p \<circ> Fun.swap i (Suc i) id = permutation_insert i j p"
    (is "?l = ?r")
proof (rule ext)
  fix x show "?l x = ?r x"
    apply (cases rule: linorder_cases[of "x" "i"])
    unfolding permutation_insert_expand swap_def by auto
qed

lemma permutation_insert_column_step:
  assumes p: "p permutes {0..<n}" and "j < n"
  shows "(Fun.swap j (Suc j) id) \<circ> (permutation_insert i (Suc j) p) = permutation_insert i j p"
    (is "?l = ?r")
proof (rule ext)
  fix x show "?l x = ?r x"
  proof (cases rule: linorder_cases[of "x" "i"])
    case less note x = this
      show ?thesis
        apply (cases rule: linorder_cases[of "p x" "j"])
        unfolding permutation_insert_expand using x by simp+
    next case equal thus ?thesis by simp
    next case greater note x = this
      show ?thesis
        apply (cases rule: linorder_cases[of "p (x-1)" "j"])
        unfolding permutation_insert_expand using x by simp+
  qed
qed

lemma delete_dom_image:
  assumes i: "i \<in> {0..<Suc n}" (is "_ \<in> ?N")
  assumes iff: "\<forall>i' \<in> ?N. f i' = f i \<longrightarrow> i' = i"
  shows "delete_dom f i ` {0..<n} = f ` ?N - {f i}" (is "?L = ?R")
proof(unfold set_eq_iff, intro allI iffI)
  fix j'
  { assume L: "j' \<in> ?L"
    then obtain i' where i': "i' \<in> {0..<n}" and dj': "delete_dom f i i' = j'" by auto
    show "j' \<in> ?R"
    proof(cases "i' < i")
      case True
        show ?thesis
          unfolding image_def
          unfolding Diff_iff
          unfolding mem_Collect_eq singleton_iff
        proof(intro conjI bexI)
          show "j' \<noteq> f i"
          proof
            assume j': "j' = f i"
            hence "f i' = f i"
              using dj'[unfolded delete_dom_def insert_index_def] using True by simp
            thus "False" using iff i True by auto
          qed
          show "j' = f i'"
            using dj' True unfolding delete_dom_def insert_index_def by simp
        qed (insert i',simp)
      next case False
        show ?thesis
          unfolding image_def
          unfolding Diff_iff
          unfolding mem_Collect_eq singleton_iff
        proof(intro conjI bexI)
          show Si': "Suc i' \<in> ?N" using i' by auto
          show "j' \<noteq> f i"
          proof
            assume j': "j' = f i"
            hence "f (Suc i') = f i"
              using dj'[unfolded delete_dom_def insert_index_def] j' False by simp
            thus "False" using iff Si' False by auto
          qed
          show "j' = f (Suc i')"
            using dj' False unfolding delete_dom_def insert_index_def by simp
        qed
    qed
  }
  { assume R: "j' \<in> ?R"
    then obtain i'
      where i': "i' \<in> ?N" and j'fi: "j' \<noteq> f i" and j'fi': "j' = f i'" by auto
    hence i'i: "i' \<noteq> i" using iff by auto
    hence n: "n > 0" using i i' by auto
    show "j' \<in> ?L"
    proof (cases "i' < i")
      case True show ?thesis
        proof
          show "j' = delete_dom f i i'"
            unfolding delete_dom_def insert_index_def using True j'fi' by simp
        qed (insert True i, simp)
      next case False show ?thesis
        proof
          show "i'-1 \<in> {0..<n}" using i' n by auto
          show "j' = delete_dom f i (i'-1)"
            unfolding delete_dom_def insert_index_def using False j'fi' i'i by auto
        qed
    qed
  }
qed

lemma delete_ran_image:
  assumes j: "j \<in> {0..<Suc n}" (is "_ \<in> ?N")
  assumes fimg: "f ` {0..<n} =  ?N - {j}"
  shows "delete_ran f j ` {0..<n} = {0..<n}" (is "?L = ?R")
proof(unfold set_eq_iff, intro allI iffI)
  fix j'
  { assume L: "j' \<in> ?L"
    then obtain i where i: "i \<in> {0..<n}" and ij': "delete_ran f j i = j'" by auto
    have "f i \<in> ?N - {j}" using fimg i by blast
    thus "j' \<in> ?R" using ij' j unfolding delete_ran_def delete_index_def by auto
  }
  { assume R: "j' \<in> ?R" show "j' \<in> ?L"
    proof (cases "j' < j")
      case True
        hence "j' \<in> ?N - {j}" using R by auto
        then obtain i where fij': "f i = j'" and i: "i \<in> {0..<n}"
          unfolding fimg[symmetric] by auto
        have "delete_ran f j i = j'"
          unfolding delete_ran_def delete_index_def unfolding fij' using True by simp
        thus ?thesis using i by auto
      next case False
        hence "Suc j' \<in> ?N - {j}" using R by auto
        then obtain i where fij': "f i = Suc j'" and i: "i \<in> {0..<n}"
          unfolding fimg[symmetric] by auto
        have "delete_ran f j i = j'"
          unfolding delete_ran_def delete_index_def unfolding fij' using False by simp
        thus ?thesis using i by auto
    qed
  }
qed

lemma delete_index_inj_on:
  assumes iS: "i \<notin> S"
  shows "inj_on (delete_index i) S"
proof(intro inj_onI)
  fix x y
  assume eq: "delete_index i x = delete_index i y" and x: "x \<in> S" and y: "y \<in> S"
  have "x \<noteq> i" "y \<noteq> i" using x y iS by auto
  thus "x = y"
    using eq unfolding delete_index_def
    by(cases "x < i"; cases "y < i";simp)
qed

lemma insert_index_inj_on:
  shows "inj_on (insert_index i) S"
proof(intro inj_onI)
  fix x y
  assume eq: "insert_index i x = insert_index i y" and x: "x \<in> S" and y: "y \<in> S"
  show "x = y"
    using eq unfolding insert_index_def
    by(cases "x < i"; cases "y < i";simp)
qed


lemma delete_dom_inj_on:
  assumes i: "i \<in> {0..<Suc n}" (is "_ \<in> ?N")
  assumes inj: "inj_on f ?N"
  shows "inj_on (delete_dom f i) {0..<n}"
proof (rule eq_card_imp_inj_on)
  have "card ?N = card (f ` ?N)" using card_image[OF inj]..
  hence "card {0..<n} = card (f ` ?N - {f i})" using i by auto
  also have "... = card (delete_dom f i ` {0..<n})"
    apply(subst delete_dom_image[symmetric])
    using i inj unfolding inj_on_def by auto
  finally show "card (delete_dom f i ` {0..<n}) = card {0..<n}"..
qed simp

lemma delete_ran_inj_on:
  assumes j: "j \<in> {0..<Suc n}" (is "_ \<in> ?N")
  assumes img: "f ` {0..<n} =  ?N - {j}"
  shows "inj_on (delete_ran f j) {0..<n}"
  apply (rule eq_card_imp_inj_on)
  unfolding delete_ran_image[OF j img] by simp+

lemma permutation_delete_bij_betw:
  assumes i: "i \<in> {0 ..< Suc n}" (is "_ \<in> ?N")
  assumes bij: "bij_betw p ?N ?N"
  shows "bij_betw (permutation_delete p i) {0..<n} {0..<n}" (is "bij_betw ?p _ _")
proof-
  have inj: "inj_on p ?N" using bij_betw_imp_inj_on[OF bij].
  have ran: "p ` ?N = ?N" using bij_betw_imp_surj_on[OF bij].
  hence j: "p i \<in> ?N" using i by auto
  have "\<forall>i'\<in>?N. p i' = p i \<longrightarrow> i' = i" using inj i unfolding inj_on_def by auto
  from delete_dom_image[OF i this]
  have "delete_dom p i ` {0..<n} = ?N - {p i}" unfolding ran.
  from delete_ran_inj_on[OF j this] delete_ran_image[OF j this]
  show ?thesis unfolding permutation_delete_def
    using bij_betw_imageI by blast
qed

lemma permutation_delete_permutes:
  assumes p: "p permutes {0 ..< Suc n}" (is "_ permutes ?N")
      and i: "i < Suc n"
  shows "permutation_delete p i permutes {0..<n}" (is "?p permutes ?N'")
proof (rule bij_imp_permutes, rule permutation_delete_bij_betw)
  have pi: "p i < Suc n" using p i by auto
  show "bij_betw p ?N ?N" using permutes_imp_bij[OF p].
  fix x assume "x \<notin> {0..<n}" hence x: "x \<ge> n" by simp
    show "?p x = x"
    proof(cases "x < i")
      case True thus ?thesis
        unfolding permutation_delete_def using x i by simp
      next case False
        hence "p (Suc x) = Suc x" using x permutes_others[OF p] by auto
        thus ?thesis
        unfolding permutation_delete_expand using False pi x by simp
    qed
qed (insert i,auto)

lemma permutation_insert_delete:
  assumes p: "p permutes {0..<Suc n}"
      and i: "i < Suc n"
  shows "permutation_insert i (p i) (permutation_delete p i) = p"
    (is "?l = _")
proof
  fix i'
  show "?l i' = p i'"
  proof (cases rule: linorder_cases[of "i'" "i"])
    case less note i'i = this
      show ?thesis
      proof (cases "p i = p i'")
        case True
          hence "i = i'" using permutes_inj[OF p] injD by metis
          hence False using i'i by auto
          thus ?thesis by auto
        next case False thus ?thesis
          unfolding permutation_insert_expand permutation_delete_expand
          using i'i by auto
      qed
    next case equal thus ?thesis unfolding permutation_insert_expand by simp
    next case greater hence i'i: "i' > i" by auto
      hence cond: "\<not> i' - 1 < i" using i'i by simp
      show ?thesis
      proof (cases rule: linorder_cases[of "p i'" "p i"])
        case less
          hence pd: "permutation_delete p i (i'-1) = p i'"
            unfolding permutation_delete_expand
            using i'i cond by auto
          show ?thesis
            unfolding permutation_insert_expand pd
            using i'i less by simp
        next case equal
          hence "i = i'" using permutes_inj[OF p] injD by metis
          hence False using i'i by auto
          thus ?thesis by auto
        next case greater
          hence pd: "permutation_delete p i (i'-1) = p i' - 1"
            unfolding permutation_delete_expand
            using i'i cond by simp
          show ?thesis
            unfolding permutation_insert_expand pd
            using i'i greater by auto
      qed
  qed
qed

lemma insert_index_exclude[simp]:
  "insert_index i i' \<noteq> i" unfolding insert_index_def by auto

lemma insert_index_image:
  assumes i: "i < Suc n"
  shows "insert_index i ` {0..<n} = {0..<Suc n} - {i}" (is "?L = ?R")
proof(unfold set_eq_iff, intro allI iffI)
  let ?N = "{0..<Suc n}"
  fix i'
  { assume L: "i' \<in> ?L"
    then obtain i''
      where ins: "i' = insert_index i i''" and i'': "i'' \<in> {0..<n}" by auto
    show "i' \<in> ?N - {i}"
    proof(rule DiffI)
      show "i' \<in> ?N" using ins unfolding insert_index_def using i'' by auto
      show "i' \<notin> {i}"
        unfolding singleton_iff
        unfolding ins unfolding insert_index_def by auto
    qed
  }
  { assume R: "i' \<in> ?R"
    show "i' \<in> ?L"
    proof(cases rule: linorder_cases[of "i'" "i"])
      case less
        hence i': "i' \<in> {0..<n}" using i by auto
        hence "insert_index i i' = i'" unfolding insert_index_def using less by auto
        thus ?thesis using i' by force
      next case equal
        hence False using R by auto
        thus ?thesis by auto
      next case greater
        hence i'': "i'-1 \<in> {0..<n}" using i R by auto
        hence "insert_index i (i'-1) = i'"
          unfolding insert_index_def using greater by auto
        thus ?thesis using i'' by force
    qed
  }
qed

lemma insert_ran_image:
  assumes j: "j < Suc n"
  assumes img: "f ` {0..<n} = {0..<n}"
  shows "insert_ran f j ` {0..<n} = {0..<Suc n} - {j}" (is "?L = ?R")
proof -
  have "?L = (\<lambda>i. insert_index j (f i)) ` {0..<n}" unfolding insert_ran_def..
  also have "... = (insert_index j \<circ> f) ` {0..<n}" by auto
  also have "... = insert_index j ` f ` {0..<n}" by auto
  also have "... = insert_index j ` {0..<n}" unfolding img by auto
  finally show ?thesis using insert_index_image[OF j] by auto
qed

lemma insert_dom_image:
  assumes i: "i < Suc n" and j: "j < Suc n"
    and img: "f ` {0..<n} = {0..<Suc n} - {j}" (is "_ = ?N - _")
  shows "insert_dom f i j ` ?N = ?N" (is "?f ` _ = _")
proof(unfold set_eq_iff,intro allI iffI)
  fix j'
  { assume "j' \<in> ?f ` ?N"
    then obtain i' where i': "i' \<in> ?N" and j': "j' = ?f i'" by auto
    show "j' \<in> ?N"
    proof (cases rule:linorder_cases[of "i'" "i"])
      case less
        hence "i' \<in> {0..<n}" using i by auto
        hence "f i' < Suc n" using imageI[of i' "{0..<n}" f] img by auto
        thus ?thesis
          unfolding j' unfolding insert_dom_def using less by auto
      next case equal
        thus ?thesis unfolding j' insert_dom_def using j by auto
      next case greater
        hence "i'-1 \<in> {0..<n}" using i' by auto
        hence "f (i'-1) < Suc n" using imageI[of "i'-1" "{0..<n}" f] img by auto
        thus ?thesis
          unfolding j' insert_dom_def using greater by auto
    qed
  }
  { assume j': "j' \<in> ?N" show "j' \<in> ?f ` ?N"
    proof (cases "j' = j")
      case True
        hence "?f i = j'" unfolding insert_dom_def by auto
        thus ?thesis using i by auto
      next case False
        hence j': "j' \<in> ?N - {j}" using j j' by auto
        then obtain i' where j'fi: "j' = f i'" and i': "i' \<in> {0..<n}"
          unfolding img[symmetric] by auto
        show ?thesis
        proof(cases "i' < i")
          case True thus ?thesis unfolding j'fi insert_dom_def using i' by auto
          next case False
            hence "?f (Suc i') = j'" unfolding j'fi insert_dom_def using i' by auto
            thus ?thesis using i' by auto
        qed
    qed
  }
qed

lemma insert_ran_inj_on:
  assumes inj: "inj_on f {0..<n}" and j: "j < Suc n"
  shows "inj_on (insert_ran f j) {0..<n}" (is "inj_on ?f _")
proof (rule inj_onI)
  fix i i'
  assume i: "i \<in> {0..<n}" and i': "i' \<in> {0..<n}" and eq: "?f i = ?f i'"
  note eq2 = eq[unfolded insert_ran_def insert_index_def]
  have "f i = f i'"
  proof (cases "f i < j")
    case True
      moreover have "f i' < j" apply (rule ccontr) using eq2 True by auto
      ultimately show ?thesis using eq2 by auto
    next case False
      moreover have "\<not> f i' < j" apply (rule ccontr) using eq2 False by auto
      ultimately show ?thesis using eq2 by auto
  qed
  from inj_onD[OF inj this i i'] show "i = i'".
qed

lemma insert_dom_inj_on:
  assumes inj: "inj_on f {0..<n}"
      and i: "i < Suc n" and j: "j < Suc n"
      and img: "f ` {0..<n} = {0..<Suc n} - {j}" (is "_ = ?N - _")
  shows "inj_on (insert_dom f i j) ?N"
  apply(rule eq_card_imp_inj_on)
  unfolding insert_dom_image[OF i j img] by simp+

lemma permutation_insert_bij_betw:
  assumes q: "q permutes {0..<n}" and i: "i < Suc n" and j: "j < Suc n"
  shows "bij_betw (permutation_insert i j q) {0..<Suc n} {0..<Suc n}"
    (is "bij_betw ?q ?N _")
proof (rule bij_betw_imageI)
  have img: "q ` {0..<n} = {0..<n}" using permutes_image[OF q].
  show "?q ` ?N = ?N"
    unfolding permutation_insert_def
    using insert_dom_image[OF i j insert_ran_image[OF j permutes_image[OF q]]].
  have inj: "inj_on q {0..<n}"
    apply(rule subset_inj_on) using permutes_inj[OF q] by auto
  show "inj_on ?q ?N"
    unfolding permutation_insert_def
    using insert_dom_inj_on[OF _ i j]
    using insert_ran_inj_on[OF inj j] insert_ran_image[OF j img] by auto
qed

lemma permutation_insert_permutes:
  assumes q: "q permutes {0..<n}"
      and i: "i < Suc n" and j: "j < Suc n"
  shows "permutation_insert i j q permutes {0..<Suc n}" (is "?p permutes ?N")
  using permutation_insert_bij_betw[OF q i j]
proof (rule bij_imp_permutes)
  fix i' assume "i' \<notin> ?N"
  moreover hence "q (i'-1) = i'-1" using permutes_others[OF q] by auto
  ultimately show "?p i' = i'"
    unfolding permutation_insert_expand using i j by auto
qed

lemma permutation_fix:
  assumes i: "i < Suc n" and j: "j < Suc n"
  shows "{ p. p permutes {0..<Suc n} \<and> p i = j } =
         permutation_insert i j ` { q. q permutes {0..<n} }"
    (is "?L = ?R")
  unfolding set_eq_iff
proof(intro allI iffI)
  let ?N = "{0..<Suc n}"
  fix p
  { assume "p \<in> ?L"
    hence p: "p permutes ?N" and pij: "p i = j" by auto
    show "p \<in> ?R"
      unfolding mem_Collect_eq
      using permutation_delete_permutes[OF p i]
      using permutation_insert_delete[OF p i,symmetric]
      unfolding pij by auto
  }
  { assume "p \<in> ?R"
    then obtain q where pq: "p = permutation_insert i j q" and q: "q permutes {0..<n}" by auto
    hence "p i = j" unfolding permutation_insert_expand by simp
    thus "p \<in> ?L"
      using pq permutation_insert_permutes[OF q i j] by auto
  }
qed

lemma permutation_split_ran:
  assumes j: "j \<in> S"
  shows "{ p. p permutes S } = (\<Union>i \<in> S. { p. p permutes S \<and> p i = j })"
  (is "?L = ?R")
  unfolding set_eq_iff
proof(intro allI iffI)
  fix p
  { assume "p \<in> ?L"
    hence p: "p permutes S" by auto
    obtain i where i: "i \<in> S" and pij: "p i = j" using j permutes_image[OF p] by force
    thus "p \<in> ?R" using p by auto
  }
  { assume "p \<in> ?R"
    then obtain i
      where p: "p permutes S" and i: "i \<in> S" and pij: "p i = j"
      by auto
    show "p \<in> ?L"
      unfolding mem_Collect_eq using p.
  }
qed

lemma permutation_disjoint_dom:
  assumes i: "i \<in> S" and i': "i' \<in> S" and j: "j \<in> S" and ii': "i \<noteq> i'"
  shows "{ p. p permutes S \<and> p i = j } \<inter> { p. p permutes S \<and> p i' = j } = {}"
    (is "?L \<inter> ?R = {}")
proof -
  {
    fix p assume "p \<in> ?L \<inter> ?R"
    hence p: "p permutes S" and "p i = j" and "p i' = j" by auto
    hence "p i = p i'" by auto
    note injD[OF permutes_inj[OF p] this]
    hence False using ii' by auto
  }
  thus ?thesis by auto
qed

lemma permutation_disjoint_ran:
  assumes i: "i \<in> S" and j: "j \<in> S" and j': "j' \<in> S" and jj': "j \<noteq> j'"
  shows "{ p. p permutes S \<and> p i = j } \<inter> { p. p permutes S \<and> p i = j' } = {}"
    (is "?L \<inter> ?R = {}")
proof -
  {
    fix p assume "p \<in> ?L \<inter> ?R"
    hence "p permutes S" and "p i = j" and "p i = j'" by auto
    hence False using jj' by auto
  }
  thus ?thesis by auto
qed

lemma permutation_insert_inj_on:
  assumes "i < Suc n"
  assumes "j < Suc n"
  shows "inj_on (permutation_insert i j) { q. q permutes {0..<n} }"
  (is "inj_on ?f ?S")
proof (rule inj_onI)
  fix q q'
  assume "q \<in> ?S" "q' \<in> ?S"
  hence q: "q permutes {0..<n}" and q': "q' permutes {0..<n}" by auto
  assume "?f q = ?f q'"
  hence eq: "permutation_insert i j q = permutation_insert i j q'" by auto
  note eq = cong[OF eq refl, unfolded permutation_insert_expand]
  show qq': "q = q'"
  proof(rule ext)
    fix x
    have foo: "Suc x - 1 = x" by auto
    show "q x = q' x"
    proof(cases "x < i")
      case True thus ?thesis apply(cases "q x < j";cases "q' x < j") using eq[of x] by auto
      next case False thus ?thesis
        apply(cases "q x < j";cases "q' x < j") using eq[of "Suc x"] by auto
    qed
  qed
qed

lemma signof_permutation_insert:
  assumes p: "p permutes {0..<n}" and i: "i < Suc n" and j: "j < Suc n"
  shows "signof (permutation_insert i j p) = (-1::'a::ring_1)^(i+j) * signof p"
proof -
  { fix j assume "j \<le> n"
    hence "signof (permutation_insert n (n-j) p) = (-1::'a)^(n+(n-j)) * signof p"
    proof(induct "j")
      case 0 show ?case using permutation_insert_base[OF p] by (simp add: mult_2[symmetric])
      next case (Suc j)
        hence Sjn: "Suc j \<le> n" and j: "j < n" and Sj: "n - Suc j < n" by auto
        hence n0: "n > 0" by auto
        have ease: "Suc (n - Suc j) = n - j" using j by auto
        let ?swap = "Fun.swap (n - Suc j) (n - j) id"
        let ?prev = "permutation_insert n (n - j) p"
        have "signof (permutation_insert n (n - Suc j) p) = signof (?swap \<circ> ?prev)"
          unfolding permutation_insert_column_step[OF p Sj, unfolded ease]..
        also have "... = signof ?swap * signof ?prev"
          proof(rule signof_compose)
            show "?swap permutes {0..<Suc n}" by (rule permutes_swap_id,auto)
            show "?prev permutes {0..<Suc n}" by (rule permutation_insert_permutes[OF p],auto)
          qed
        also have "signof ?swap = -1"
          proof-
            have "n - Suc j < n - j" using Sjn by simp
            thus ?thesis unfolding signof_def sign_swap_id by simp
          qed
        also have "signof ?prev = (-1::'a) ^ (n + (n - j)) * signof p" using Suc(1) j by auto
        also have "(-1) * ... =  (-1) ^ (1 + n + (n - j)) * signof p" by simp
        also have "n - j = 1 + (n - Suc j)" using j by simp
        also have "1 + n + ... = 2 + (n + (n - Suc j))" by simp
        also have "(-1::'a) ^ ... = (-1) ^ 2 * (-1) ^ (n + (n - Suc j))" by simp
        also have "... = (-1) ^ (n + (n - Suc j))" by simp
        finally show ?case.
    qed
  }
  note col = this
  have nj: "n - j \<le> n" using j by auto
  have row_base: "signof (permutation_insert n j p) = (-1::'a)^(n+j) * signof p"
    using col[OF nj] using j by simp
  { fix i assume "i \<le> n"
    hence "signof (permutation_insert (n-i) j p) = (-1::'a)^((n-i)+j) * signof p"
    proof (induct i)
      case 0 show ?case using row_base by auto
      next case (Suc i)
        hence Sin: "Suc i \<le> n" and i: "i \<le> n" and Si: "n - Suc i < n" by auto
        have ease: "Suc (n - Suc i) = n - i" using Sin by auto
        let ?prev = "permutation_insert (n-i) j p"
        let ?swap = "Fun.swap (n - Suc i) (n-i) id"
        have "signof (permutation_insert (n - Suc i) j p) = signof (?prev \<circ> ?swap)"
          using permutation_insert_row_step[of "n - Suc i"] unfolding ease by auto
        also have "... = signof ?prev * signof ?swap"
          proof(rule signof_compose)
            show "?swap permutes {0..<Suc n}" by (rule permutes_swap_id,auto)
            show "?prev permutes {0..<Suc n}"
              apply(rule permutation_insert_permutes[OF p]) using j by auto
          qed
        also have "signof ?swap = (-1)"
          proof-
            have "n - Suc i < n - i" using Sin by simp
            thus ?thesis unfolding signof_def sign_swap_id by simp
          qed
        also have "signof ?prev = (-1::'a) ^ (n - i + j) * signof p"
          using Suc(1)[OF i].
        also have "... * (-1) = (-1) ^ Suc (n - i + j) * signof p"
          by auto
        also have "Suc (n - i + j) = Suc (Suc (n - Suc i + j))"
          using Sin by auto
        also have "(-1::int) ^ ... = (-1) ^ (n - Suc i + j)" by auto
        ultimately show ?case by auto
    qed
  }
  note row = this
  have ni: "n - i \<le> n" using i by auto
  show ?thesis using row[OF ni] using i by simp
qed

lemma foo:
  assumes i: "i < Suc n" and j: "j < Suc n"
  assumes q: "q permutes {0..<n}"
  shows "{(i', permutation_insert i j q i') | i'. i' \<in> {0..<Suc n} - {i} } =
  { (insert_index i i'', insert_index j (q i'')) | i''. i'' < n }" (is "?L = ?R")
  unfolding set_eq_iff
proof(intro allI iffI)
  fix ij
  { assume "ij \<in> ?L"
    then obtain i'
      where ij: "ij = (i', permutation_insert i j q i')" and i': "i' < Suc n" and i'i: "i' \<noteq> i"
      by auto
    show "ij \<in> ?R" unfolding mem_Collect_eq
    proof(intro exI conjI)
      show "ij = (insert_index i (delete_index i i'), insert_index j (q (delete_index i i')))"
        using ij unfolding insert_delete_index[OF i'i] using i'i
        unfolding permutation_insert_expand insert_index_def delete_index_def by auto
      show "delete_index i i' < n" using i' i i'i unfolding delete_index_def by auto
    qed
  }
  { assume "ij \<in> ?R"
    then obtain i''
      where ij: "ij = (insert_index i i'', insert_index j (q i''))" and i'': "i'' < n"
      by auto
    show "ij \<in> ?L" unfolding mem_Collect_eq
    proof(intro exI conjI)
      show "insert_index i i'' \<in> {0..<Suc n} - {i}"
        unfolding insert_index_image[OF i,symmetric] using i'' by auto
      have "insert_index j (q i'') = permutation_insert i j q (insert_index i i'')"
        unfolding permutation_insert_expand insert_index_def by auto
      thus "ij = (insert_index i i'', permutation_insert i j q (insert_index i i''))"
        unfolding ij by auto
    qed
  }
qed

definition "mat_delete A i j \<equiv>
  mat (dim\<^sub>r A - 1) (dim\<^sub>c A - 1) (\<lambda>(i',j').
    A $$ (if i' < i then i' else Suc i', if j' < j then j' else Suc j'))"

lemma mat_delete_dim[simp]:
  "dim\<^sub>r (mat_delete A i j) = dim\<^sub>r A - 1"
  "dim\<^sub>c (mat_delete A i j) = dim\<^sub>c A - 1"
  unfolding mat_delete_def by auto

lemma mat_delete_carrier:
  assumes A: "A \<in> carrier\<^sub>m m n"
  shows "mat_delete A i j \<in> carrier\<^sub>m (m-1) (n-1)" unfolding mat_delete_def using A by auto

lemma "mat_delete_index":
  assumes A: "A \<in> carrier\<^sub>m (Suc n) (Suc n)"
      and i: "i < Suc n" and j: "j < Suc n"
      and i': "i' < n" and j': "j' < n"
  shows "A $$ (insert_index i i', insert_index j j') = mat_delete A i j $$ (i', j')"
  unfolding mat_delete_def
  unfolding permutation_insert_expand
  unfolding insert_index_def
  using A i j i' j' by auto

definition "cofactor A i j = (-1)^(i+j) * det (mat_delete A i j)"


lemma laplace_expansion_column:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier\<^sub>m n n"
      and j: "j < n"
  shows "det A = (\<Sum>i<dim\<^sub>r A. A $$ (i,j) * cofactor A i j)"
proof -
  def l \<equiv> "n-1"
  have A: "A \<in> carrier\<^sub>m (Suc l) (Suc l)"
   and j: "j < Suc l" using A j unfolding l_def by auto
  let ?N = "{0 ..< Suc l}"
  def f \<equiv> "\<lambda>p i. A $$ (i, p i)"
  def g \<equiv> "\<lambda>p. setprod (f p) ?N"
  def h \<equiv> "\<lambda>p. signof p * g p"
  def Q \<equiv> "{ q . q permutes {0..<l} }"
  have jN: "j \<in> ?N" using j by auto
  have disj: "\<forall>i \<in> ?N. \<forall>i' \<in> ?N. i \<noteq> i' \<longrightarrow>
    {p. p permutes ?N \<and> p i = j} \<inter> {p. p permutes ?N \<and> p i' = j} = {}"
    using permutation_disjoint_dom[OF _ _ jN] by auto
  have fin: "\<forall>i\<in>?N. finite {p. p permutes ?N \<and> p i = j}"
    using finite_permutations[of ?N] by auto

  have "det A = setsum h { p. p permutes ?N }"
    using det_def'[OF A] unfolding h_def g_def f_def using atLeast0LessThan by auto
  also have "... = setsum h (\<Union>i\<in>?N. {p. p permutes ?N \<and> p i = j})"
    unfolding permutation_split_ran[OF jN]..
  also have "... = (\<Sum>i\<in>?N. setsum h { p | p. p permutes ?N \<and> p i = j})"
    using setsum.UNION_disjoint[OF _ fin disj] by auto
  also {
    fix i assume "i \<in> ?N"
    hence i: "i < Suc l" by auto
    have "setsum h { p | p. p permutes ?N \<and> p i = j} = setsum h (permutation_insert i j ` Q)"
      using permutation_fix[OF i j] unfolding Q_def by auto
    also have "... = setsum (h \<circ> permutation_insert i j) Q"
      unfolding Q_def using setsum.reindex[OF permutation_insert_inj_on[OF i j]].
    also have "... = (\<Sum> q \<in> Q.
      signof (permutation_insert i j q) * setprod (f (permutation_insert i j q)) ?N)"
      unfolding h_def g_def Q_def by simp
    also {
      fix q assume "q \<in> Q"
      hence q: "q permutes {0..<l}" unfolding Q_def by auto
      let ?p = "permutation_insert i j q"
      have fin: "finite (?N - {i})" by auto
      have notin: "i \<notin> ?N - {i}" by auto
      have close: "insert i (?N - {i}) = ?N" using notin i by auto
      have "setprod (f ?p) ?N = f ?p i * setprod (f ?p) (?N-{i})"
        unfolding setprod.insert[OF fin notin, unfolded close] by auto
      also have "... = A $$ (i, j) * setprod (f ?p) (?N-{i})"
        unfolding f_def Q_def using permutation_insert_inserted by simp
      also have "setprod (f ?p) (?N-{i}) = setprod (\<lambda>i'. A $$ (i', permutation_insert i j q i')) (?N-{i})"
        unfolding f_def..
      also have "... = setprod (\<lambda>ij. A $$ ij) ((\<lambda>i'. (i', permutation_insert i j q i')) ` (?N-{i}))"
        (is "_ = setprod _ ?part")
        unfolding setprod.reindex[OF inj_on_convol_ident] o_def..
      also have "?part = {(i', permutation_insert i j q i') | i'. i' \<in> ?N-{i} }"
        unfolding image_def by metis
      also have "... = {(insert_index i i'', insert_index j (q i'')) | i''. i'' < l}"
        unfolding foo[OF i j q]..
      also have "... = ((\<lambda>i''. (insert_index i i'', insert_index j (q i''))) ` {0..<l})"
        unfolding image_def by auto
      also have "setprod (\<lambda>ij. A $$ ij)... = setprod ((\<lambda>ij. A $$ ij) \<circ> (\<lambda>i''. (insert_index i i'', insert_index j (q i'')))) {0..<l}"
        proof(subst setprod.reindex[symmetric])
          have 1: "inj (\<lambda>i''. (i'', insert_index j (q i'')))" using inj_on_convol_ident.
          have 2: "inj (\<lambda>(i'',j). (insert_index i i'', j))"
            apply (intro injI) using injD[OF insert_index_inj_on[of _ UNIV]] by auto
          have "inj (\<lambda>i''. (insert_index i i'', insert_index j (q i'')))"
            using inj_comp[OF 2 1] unfolding o_def by auto
          thus "inj_on (\<lambda>i''. (insert_index i i'', insert_index j (q i''))) {0..<l}"
            using subset_inj_on by auto
        qed auto
      also have "... = setprod (\<lambda>i''. A $$ (insert_index i i'', insert_index j (q i''))) {0..<l}"
        by auto
      also have "... = setprod (\<lambda>i''. mat_delete A i j $$ (i'', q i'')) {0..<l}"
      proof (rule setprod.cong[OF refl], unfold atLeastLessThan_iff, elim conjE)
        fix x assume x: "x < l"
        show "A $$ (insert_index i x, insert_index j (q x)) = mat_delete A i j $$ (x, q x)"
          apply(rule mat_delete_index[OF A i j]) using q x by auto
      qed
      finally have "setprod (f ?p) ?N =
        A $$ (i, j) * (\<Prod>i'' = 0..< l. mat_delete A i j $$ (i'', q i''))"
        by auto
      hence "signof ?p * setprod (f ?p) ?N  = (-1::'a)^(i+j) * signof q * ..."
        unfolding signof_permutation_insert[OF q i j] by auto
    }
    hence "... = (\<Sum> q \<in> Q. (-1)^(i+j) * signof q *
      A $$ (i, j) * (\<Prod>i'' = 0 ..< l. mat_delete A i j $$ (i'', q i'')))"
      by(intro setsum.cong[OF refl],auto)
    also have "... = ( \<Sum> q \<in> Q. A $$ (i, j) * (-1)^(i+j) *
       ( signof q * (\<Prod>i'' = 0..< l. mat_delete A i j $$ (i'', q i'')) ) )"
      by (intro setsum.cong[OF refl],auto)
    also have "... = A $$ (i, j) * (-1)^(i+j) *
      ( \<Sum> q \<in> Q. signof q * (\<Prod>i''= 0 ..< l. mat_delete A i j $$ (i'', q i'')) )"
      unfolding setsum_right_distrib by auto
    also have "... = (A $$ (i, j) * (-1)^(i+j) * det (mat_delete A i j))"
      unfolding det_def'[OF mat_delete_carrier[OF A]]
      unfolding Q_def by auto
    finally have "setsum h {p | p. p permutes ?N \<and> p i = j} = A $$ (i, j) * cofactor A i j"
      unfolding cofactor_def by auto
  }
  hence "... = (\<Sum>i\<in>?N. A $$ (i,j) * cofactor A i j)" by auto
  finally show ?thesis using A atLeast0LessThan by auto
qed


end
