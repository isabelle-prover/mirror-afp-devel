(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Determinants\<close>

text \<open>Most of the following definitions and proofs on determinants have been copied and adapted 
  from ~~/src/HOL/Multivariate-Analysis/Determinants.thy.

Exceptions are \emph{det-identical-rows}.\<close>

theory Determinant
imports 
  Missing_Permutations
  Row_Operations
begin

definition det:: "'a mat \<Rightarrow> 'a :: comm_ring_1" where
  "det A = (if dim\<^sub>r A = dim\<^sub>c A then (\<Sum> p \<in> {p. p permutes {0 ..< dim\<^sub>r A}}. 
     signof p * (\<Prod> i = 0 ..< dim\<^sub>r A. A $$ (i, p i))) else 0)"

lemma det_def': "A \<in> carrier\<^sub>m n n \<Longrightarrow> 
  det A = (\<Sum> p \<in> {p. p permutes {0 ..< n}}. 
     signof p * (\<Prod> i = 0 ..< n. A $$ (i, p i)))" unfolding det_def by auto

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

lemma det_0_iff_vec_prod_zero: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m n n"
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
    obtain P where PU: "P \<in> ?U" and row: "row (P \<otimes>\<^sub>m A) ?n = \<zero>\<^sub>v n" and n: "0 < n" 
      and re: "row_echelon_form (P \<otimes>\<^sub>m A)" by auto
    def PA \<equiv> "P \<otimes>\<^sub>m A"
    note row = row[folded PA_def]
    note re = re[folded PA_def]
    from PU obtain Q where P: "P \<in> carrier\<^sub>m n n" and Q: "Q \<in> carrier\<^sub>m n n"
      and unit: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m n" "P \<otimes>\<^sub>m Q =  \<one>\<^sub>m n" unfolding Units_def mat_ring_def by auto    
    from P A have PA: "PA \<in> carrier\<^sub>m n n" and dimPA: "dim\<^sub>r PA = n" unfolding PA_def by auto
    from re[unfolded row_echelon_form_def, folded PA_def] PA
    obtain p where pivot: "pivot_fun PA p n" by auto
    note p = pivot_funD[OF dimPA pivot]
    from n have n1: "?n < n" by auto
    let ?p = "\<lambda> i. p i \<noteq> i \<and> i < n"
    def qj \<equiv> "LEAST i. ?p i"
    {
      assume "p ?n < n"
      with p(4)[OF n1 this] n1 arg_cong[OF row, of "\<lambda> v. v $ p ?n"] PA have False by auto
    }    
    with p(1)[OF n1] n1 have "?p ?n" by auto 
    from LeastI[of ?p, OF this] have qj: "?p qj" unfolding qj_def .
    have "qj \<notin> p ` {0 ..<n}"
    proof
      assume "qj \<in> p ` {0 ..<n}"
      then obtain i where i: "i < n" and qjpi: "qj = p i" by auto
      from qj qjpi i have "i \<noteq> qj" by auto
      hence "i < qj \<or> i > qj" by auto
      thus False
      proof 
        assume "i < qj"
        from not_less_Least[of _ ?p, folded qj_def, OF this] i have "p i = i" by auto
        with `qj = p i` `i < qj` show False by auto
      next
        assume gt: "qj < i"
        def diff \<equiv> "i - qj"
        from gt have isum: "i = qj + diff" and diff: "diff > 0" unfolding diff_def by auto
        from pivot_bound[OF dimPA pivot, of qj diff, folded isum qjpi, OF i] qj diff
        have "p qj < qj" by simp
        with pivot_bound[OF dimPA pivot, of 0 qj] qj show False by auto
      qed
    qed
    with qj have qj: "qj < n" "qj \<notin> p ` {0..<n}" by auto
    def v \<equiv> "non_pivot_base PA qj p"
    from non_pivot_base[OF PA pivot qj, folded v_def] qj(1)
    have v: "v \<in> carrier\<^sub>v n" and 
       v0: "v \<noteq> \<zero>\<^sub>v n" and
       pav: "PA \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
    have "A \<otimes>\<^sub>m\<^sub>v v = Q \<otimes>\<^sub>m P \<otimes>\<^sub>m\<^sub>v (A \<otimes>\<^sub>m\<^sub>v v)" unfolding unit using A v by auto
    also have "\<dots> = Q \<otimes>\<^sub>m\<^sub>v (PA \<otimes>\<^sub>m\<^sub>v v)" unfolding PA_def using Q P A v by auto
    also have "PA \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" unfolding pav ..
    also have "Q \<otimes>\<^sub>m\<^sub>v \<zero>\<^sub>v n = \<zero>\<^sub>v n" using Q by auto
    finally have Av: "A \<otimes>\<^sub>m\<^sub>v v = \<zero>\<^sub>v n" by auto
    show ?thesis unfolding True using Av v0 v by auto
  qed
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


end