(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Gauss-Jordan Algorithm\<close>

text \<open>We define the elementary row operations and use them to implement the
  Gauss-Jordan algorithm to transform matrices into row-echelon-form. 
  This algorithm is used to implement the inverse of a matrix and to derive
  certain results on determinants, as well as determine a basis of the kernel
  of a matrix.\<close> 

theory Gauss_Jordan
imports Matrix
begin

subsection \<open>Row Operations\<close>

definition mat_multrow_gen :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mat_multrow_gen mul k a A = mat (dim\<^sub>r A) (dim\<^sub>c A) 
     (\<lambda> (i,j). if k = i then mul a (A $$ (i,j)) else A $$ (i,j))"

abbreviation mat_multrow :: "nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("multrow") where
  "multrow \<equiv> mat_multrow_gen (op *)"

lemmas mat_multrow_def = mat_multrow_gen_def

definition multrow_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> 'a mat" where
  "multrow_mat n k a = mat n n 
     (\<lambda> (i,j). if k = i \<and> k = j then a else if i = j then 1 else 0)"

definition mat_swaprows :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("swaprows")where
  "swaprows k l A = mat (dim\<^sub>r A) (dim\<^sub>c A) 
    (\<lambda> (i,j). if k = i then A $$ (l,j) else if l = i then A $$ (k,j) else A $$ (i,j))"

definition swaprows_mat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a :: semiring_1 mat" where
  "swaprows_mat n k l = mat n n
    (\<lambda> (i,j). if k = i \<and> l = j \<or> k = j \<and> l = i \<or> i = j \<and> i \<noteq> k \<and> i \<noteq> l then 1 else 0)"

definition mat_addrow_gen :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mat_addrow_gen ad mul a k l A = mat (dim\<^sub>r A) (dim\<^sub>c A) 
    (\<lambda> (i,j). if k = i then ad (mul a (A $$ (l,j))) (A $$ (i,j)) else A $$ (i,j))"

abbreviation mat_addrow :: "'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("addrow") where
  "addrow \<equiv> mat_addrow_gen (op +) (op *)"

lemmas mat_addrow_def = mat_addrow_gen_def

definition addrow_mat :: "nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "addrow_mat n a k l = mat n n (\<lambda> (i,j). 
    (if k = i \<and> l = j then op + a else id) (if i = j then 1 else 0))"

lemma mat_index_multrow[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> mat_multrow_gen mul k a A $$ (i,j) = (if k = i then mul a (A $$ (i,j)) else A $$ (i,j))"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> mat_multrow_gen mul i a A $$ (i,j) = mul a (A $$ (i,j))"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> k \<noteq> i \<Longrightarrow> mat_multrow_gen mul k a A $$ (i,j) = A $$ (i,j)"
  "dim\<^sub>r (mat_multrow_gen mul k a A) = dim\<^sub>r A" "dim\<^sub>c (mat_multrow_gen mul k a A) = dim\<^sub>c A"
  unfolding mat_multrow_def by auto

lemma mat_index_multrow_mat[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> multrow_mat n k a $$ (i,j) = (if k = i \<and> k = j then a else if i = j 
     then 1 else 0)"
  "dim\<^sub>r (multrow_mat n k a) = n" "dim\<^sub>c (multrow_mat n k a) = n"
  unfolding multrow_mat_def by auto

lemma mat_index_swaprows[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> swaprows k l A $$ (i,j) = (if k = i then A $$ (l,j) else 
    if l = i then A $$ (k,j) else A $$ (i,j))"
  "dim\<^sub>r (swaprows k l A) = dim\<^sub>r A" "dim\<^sub>c (swaprows k l A) = dim\<^sub>c A"
  unfolding mat_swaprows_def by auto

lemma mat_index_swaprows_mat[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> swaprows_mat n k l $$ (i,j) = 
    (if k = i \<and> l = j \<or> k = j \<and> l = i \<or> i = j \<and> i \<noteq> k \<and> i \<noteq> l then 1 else 0)"
  "dim\<^sub>r (swaprows_mat n k l) = n" "dim\<^sub>c (swaprows_mat n k l) = n"
  unfolding swaprows_mat_def by auto

lemma mat_index_addrow[simp]: 
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> mat_addrow_gen ad mul a k l A $$ (i,j) = (if k = i then 
    ad (mul a (A $$ (l,j))) (A $$ (i,j)) else A $$ (i,j))"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> mat_addrow_gen ad mul a i l A $$ (i,j) = ad (mul a (A $$ (l,j))) (A $$ (i,j))"
  "i < dim\<^sub>r A \<Longrightarrow> j < dim\<^sub>c A \<Longrightarrow> k \<noteq> i \<Longrightarrow> mat_addrow_gen ad mul a k l A $$ (i,j) = A $$(i,j)"
  "dim\<^sub>r (mat_addrow_gen ad mul a k l A) = dim\<^sub>r A" "dim\<^sub>c (mat_addrow_gen ad mul a k l A) = dim\<^sub>c A"
  unfolding mat_addrow_def by auto

lemma mat_index_addrow_mat[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> addrow_mat n a k l $$ (i,j) = 
    (if k = i \<and> l = j then op + a else id) (if i = j then 1 else 0)"
  "dim\<^sub>r (addrow_mat n a k l) = n" "dim\<^sub>c (addrow_mat n a k l) = n"
  unfolding addrow_mat_def by auto

lemma multrow_closed[simp]: "(mat_multrow_gen mul k a A \<in> carrier\<^sub>m n nc) = (A \<in> carrier\<^sub>m n nc)"
  unfolding mat_carrier_def by fastforce

lemma multrow_mat_closed[simp]: "multrow_mat n k a \<in> carrier\<^sub>m n n"
  unfolding mat_carrier_def by auto

lemma addrow_mat_closed[simp]: "addrow_mat n a k l \<in> carrier\<^sub>m n n"
  unfolding mat_carrier_def by auto

lemma swaprows_mat_closed[simp]: "swaprows_mat n k l \<in> carrier\<^sub>m n n"
  unfolding mat_carrier_def by auto

lemma swaprows_closed[simp]: "(swaprows k l A \<in> carrier\<^sub>m n nc) = (A \<in> carrier\<^sub>m n nc)"
  unfolding mat_carrier_def by fastforce

lemma addrow_closed[simp]: "(mat_addrow_gen ad mul a k l A \<in> carrier\<^sub>m n nc) = (A \<in> carrier\<^sub>m n nc)"
  unfolding mat_carrier_def by fastforce

lemma row_multrow:  "k \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> row (multrow_mat n k a) i = unit\<^sub>v n i"
  "k < n \<Longrightarrow> row (multrow_mat n k a) k = a \<odot>\<^sub>v unit\<^sub>v n k"
  by (rule vec_eqI, auto)

lemma multrow_mat: assumes A: "A \<in> carrier\<^sub>m n nc"
  shows "multrow k a A = multrow_mat n k a \<otimes>\<^sub>m A"
  by (rule mat_eqI, insert A, auto simp: row_multrow scalar_scalar_prod_assoc[of _ n])

lemma row_addrow: 
  "k \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> row (addrow_mat n a k l) i = unit\<^sub>v n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> row (addrow_mat n a k l) k = a \<odot>\<^sub>v unit\<^sub>v n l \<oplus>\<^sub>v unit\<^sub>v n k"
  by (rule vec_eqI, auto)

lemma addrow_mat: assumes A: "A \<in> carrier\<^sub>m n nc" 
  and l: "l < n"
  shows "addrow a k l A = addrow_mat n a k l \<otimes>\<^sub>m A"
  by (rule mat_eqI, insert l A, auto simp: row_addrow 
  scalar_prod_left_distrib[of _ n] scalar_scalar_prod_assoc[of _ n])

lemma row_swaprows: 
  "l < n \<Longrightarrow> row (swaprows_mat n l l) l = unit\<^sub>v n l"
  "i \<noteq> k \<Longrightarrow> i \<noteq> l \<Longrightarrow> i < n \<Longrightarrow> row (swaprows_mat n k l) i = unit\<^sub>v n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> row (swaprows_mat n k l) l = unit\<^sub>v n k"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> row (swaprows_mat n k l) k = unit\<^sub>v n l"
  by (rule vec_eqI, auto)

lemma swaprows_mat: assumes A: "A \<in> carrier\<^sub>m n nc" and k: "k < n" "l < n"
  shows "swaprows k l A = swaprows_mat n k l \<otimes>\<^sub>m A"
  by (rule mat_eqI, insert A k, auto simp: row_swaprows)

lemma swaprows_mat_inv: assumes k: "k < n" and l: "l < n"
  shows "swaprows_mat n k l \<otimes>\<^sub>m swaprows_mat n k l = \<one>\<^sub>m n"
proof -
  have "swaprows_mat n k l \<otimes>\<^sub>m swaprows_mat n k l = 
    swaprows_mat n k l \<otimes>\<^sub>m (swaprows_mat n k l \<otimes>\<^sub>m \<one>\<^sub>m n)"
    by (simp add: mat_right_mult_one[of _ n])
  also have "swaprows_mat n k l \<otimes>\<^sub>m \<one>\<^sub>m n = swaprows k l (\<one>\<^sub>m n)"
    by (rule swaprows_mat[symmetric, OF _ k l, of _ n], simp)
  also have "swaprows_mat n k l \<otimes>\<^sub>m \<dots> = swaprows k l \<dots>"
    by (rule swaprows_mat[symmetric, of _ _ n], insert k l, auto)
  also have "\<dots> = \<one>\<^sub>m n"
    by (rule mat_eqI, insert k l, auto)
  finally show ?thesis .
qed

lemma swaprows_mat_Unit: assumes k: "k < n" and l: "l < n"
  shows "swaprows_mat n k l \<in> Units (ring\<^sub>m TYPE('a :: semiring_1) n b)"
proof -
  interpret m: semiring "ring\<^sub>m TYPE('a) n b" by (rule mat_semiring)
  show ?thesis unfolding Units_def
    by (rule, rule conjI[OF _ bexI[of _ "swaprows_mat n k l"]],
    auto simp: mat_ring_def swaprows_mat_inv[OF k l] swaprows_mat_inv[OF l k])
qed

lemma addrow_mat_inv: assumes k: "k < n" and l: "l < n" and neq: "k \<noteq> l"
  shows "addrow_mat n a k l \<otimes>\<^sub>m addrow_mat n (- (a :: 'a :: comm_ring_1)) k l = \<one>\<^sub>m n"
proof -
  have "addrow_mat n a k l \<otimes>\<^sub>m addrow_mat n (- a) k l = 
    addrow_mat n a k l \<otimes>\<^sub>m (addrow_mat n (- a) k l \<otimes>\<^sub>m \<one>\<^sub>m n)"
    by (simp add: mat_right_mult_one[of _ n])
  also have "addrow_mat n (- a) k l \<otimes>\<^sub>m \<one>\<^sub>m n = addrow (- a) k l (\<one>\<^sub>m n)"
    by (rule addrow_mat[symmetric, of _ _ n], insert k l, auto)
  also have "addrow_mat n a k l \<otimes>\<^sub>m \<dots> = addrow a k l \<dots>"
    by (rule addrow_mat[symmetric, of _ _ n], insert k l, auto)
  also have "\<dots> = \<one>\<^sub>m n"
    by (rule mat_eqI, insert k l neq, auto, algebra)
  finally show ?thesis .
qed

lemma addrow_mat_Unit: assumes k: "k < n" and l: "l < n" and neq: "k \<noteq> l"
  shows "addrow_mat n a k l \<in> Units (ring\<^sub>m TYPE('a :: comm_ring_1) n b)"
proof -
  interpret m: semiring "ring\<^sub>m TYPE('a) n b" by (rule mat_semiring)
  show ?thesis unfolding Units_def
    by (rule, rule conjI[OF _ bexI[of _ "addrow_mat n (- a) k l"]], insert neq,
    auto simp: mat_ring_def addrow_mat_inv[OF k l neq], 
    rule trans[OF _ addrow_mat_inv[OF k l neq, of "- a"]], auto)
qed

lemma multrow_mat_inv: assumes k: "k < n" and a: "(a :: 'a :: division_ring) \<noteq> 0"
  shows "multrow_mat n k a \<otimes>\<^sub>m multrow_mat n k (inverse a) = \<one>\<^sub>m n"
proof -
  have "multrow_mat n k a \<otimes>\<^sub>m multrow_mat n k (inverse a) = 
    multrow_mat n k a \<otimes>\<^sub>m (multrow_mat n k (inverse a) \<otimes>\<^sub>m \<one>\<^sub>m n)"
    using k by (simp add: mat_right_mult_one[of _ n])
  also have "multrow_mat n k (inverse a) \<otimes>\<^sub>m \<one>\<^sub>m n = multrow k (inverse a) (\<one>\<^sub>m n)"
    by (rule multrow_mat[symmetric, of _ _ n], insert k, auto)
  also have "multrow_mat n k a \<otimes>\<^sub>m \<dots> = multrow k a \<dots>"
    by (rule multrow_mat[symmetric, of _ _ n], insert k, auto)
  also have "\<dots> = \<one>\<^sub>m n"
    by (rule mat_eqI, insert a k a, auto)
  finally show ?thesis .
qed

lemma multrow_mat_Unit: assumes k: "k < n" and a: "(a :: 'a :: division_ring) \<noteq> 0"
  shows "multrow_mat n k a \<in> Units (ring\<^sub>m TYPE('a) n b)"
proof -
  from a have ia: "inverse a \<noteq> 0" by auto
  interpret m: semiring "ring\<^sub>m TYPE('a) n b" by (rule mat_semiring)
  show ?thesis unfolding Units_def
    by (rule, rule conjI[OF _ bexI[of _ "multrow_mat n k (inverse a)"]], insert a,
    auto simp: mat_ring_def multrow_mat_inv[OF k],
    rule trans[OF _ multrow_mat_inv[OF k ia]], insert a, auto)
qed

subsection \<open>Gauss-Jordan Elimination\<close>

context
  fixes add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and uminus :: "'a \<Rightarrow> 'a"
  and zero :: "'a"
begin
fun eliminate_entries_gen where
  "eliminate_entries_gen A B i j [] = B"
| "eliminate_entries_gen A B i j (i' # is) = (let ai'j = A $$ (i',j) in if ai'j = zero 
    then eliminate_entries_gen A B i j is
    else eliminate_entries_gen A (mat_addrow_gen add times (uminus ai'j) i' i B) i j is)"

lemma dimc_eliminate_entries[simp]: "dim\<^sub>c (eliminate_entries_gen A B i j as) = dim\<^sub>c B"
  by (induct as arbitrary: A B, auto simp: Let_def)

lemma dimr_eliminate_entries[simp]: "dim\<^sub>r (eliminate_entries_gen A B i j as) = dim\<^sub>r B"
  by (induct as arbitrary: A B, auto simp: Let_def)

lemma carrier_eliminate_entries: "B \<in> carrier\<^sub>m nr nc \<Longrightarrow> eliminate_entries_gen A B i j as \<in> carrier\<^sub>m nr nc"
  unfolding mat_carrier_def by simp
end

abbreviation "eliminate_entries \<equiv> eliminate_entries_gen (op +) (op *) uminus (0 :: 'a :: ring_1)"

lemma Unit_prod_eliminate_entries: "i < nr \<Longrightarrow> (\<And> i'. i' \<in> set is \<Longrightarrow> i' < nr \<and> i' \<noteq> i)
  \<Longrightarrow> \<exists> P \<in> Units (ring\<^sub>m TYPE('a :: comm_ring_1) nr b) . \<forall> B nc. B \<in> carrier\<^sub>m nr nc \<longrightarrow> eliminate_entries A B i j is = P \<otimes>\<^sub>m B" 
proof (induct "is")
  case Nil
  thus ?case by (intro bexI[of _ "\<one>\<^sub>m nr"], auto simp: Units_def mat_ring_def)
next
  case (Cons i' "is")
  let ?U = "Units (ring\<^sub>m TYPE('a) nr b)"
  interpret m: ring "ring\<^sub>m TYPE('a) nr b" by (rule mat_ring)
  let ?a = "A $$ (i',j)"
  show ?case
  proof (cases "?a = 0")
    case False
    from Cons(1)[OF Cons(2-3)] 
    obtain P where P: "P \<in> ?U" and id: "\<And> B nc . B \<in> carrier\<^sub>m nr nc \<Longrightarrow> 
      eliminate_entries A B i j is = P \<otimes>\<^sub>m B" by force
    let ?Add = "addrow_mat nr (- ?a) i' i"
    have Add: "?Add \<in> ?U"
      by (rule addrow_mat_Unit, insert Cons, auto)
    from m.Units_m_closed[OF P Add] have PI: "P \<otimes>\<^sub>m ?Add \<in> ?U" unfolding mat_ring_def by simp
    from m.Units_closed[OF P] have P: "P \<in> carrier\<^sub>m nr nr" unfolding mat_ring_def by simp
    show ?thesis
    proof (rule bexI[OF _ PI], intro allI impI)
      fix B :: "'a mat" and nc
      assume BB: "B \<in> carrier\<^sub>m nr nc"
      let ?B = "addrow (- ?a) i' i B"
      from BB have B: "?B \<in> carrier\<^sub>m nr nc" by simp
      from id[OF B] have id: "eliminate_entries A ?B i j is = P \<otimes>\<^sub>m ?B" .
      from False have id2: "eliminate_entries A B i j (i' # is) = eliminate_entries A ?B i j is" by simp
      show "eliminate_entries A B i j (i' # is) = P \<otimes>\<^sub>m ?Add \<otimes>\<^sub>m B"
        unfolding id2 id unfolding addrow_mat[OF BB Cons(2)]
        by (rule mat_mult_assoc[symmetric, OF P _ BB], auto)
    qed
  qed (insert Cons, auto)
qed

function gauss_jordan_main :: "'a :: field mat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<times> 'a mat" where
  "gauss_jordan_main A B i j = (let nr = dim\<^sub>r A; nc = dim\<^sub>c A in
    if i < nr \<and> j < nc then let aij = A $$ (i,j) in if aij = 0 then
      (case [ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0] 
        of [] \<Rightarrow> gauss_jordan_main A B i (Suc j)
         | (i' # _) \<Rightarrow> gauss_jordan_main (swaprows i i' A) (swaprows i i' B) i j)
      else if aij = 1 then let is = filter (\<lambda> i'. i' \<noteq> i) [0 ..< nr] in
        gauss_jordan_main 
        (eliminate_entries A A i j is) (eliminate_entries A B i j is) (Suc i) (Suc j)
      else let iaij = inverse aij in gauss_jordan_main (multrow i iaij A) (multrow i iaij B) i j
    else (A,B))"
  by pat_completeness auto

termination
proof -
  let ?R = "measures [\<lambda> (A :: 'a :: field mat,B,i,j). dim\<^sub>c A - j, 
    \<lambda> (A,B,i,j). if A $$ (i,j) = 0 then 2 else if A $$ (i,j) = 1 then 0 else 1]"
  show ?thesis
  proof
    show "wf ?R" by auto
  next
    fix A B :: "'a mat" and i j nr nc a i' "is"
    assume *: "nr = dim\<^sub>r A" "nc = dim\<^sub>c A" "i < nr \<and> j < nc" "a = A $$ (i, j)" "a = 0"
      and ne: "[ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0] = i' # is"
    from ne have "i' \<in> set ([ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0])" by auto
    with *
    show "((swaprows i i' A, swaprows i i' B, i, j), A, B, i, j) \<in> ?R" by auto
  qed auto
qed

definition "gauss_jordan A B \<equiv> gauss_jordan_main A B 0 0"

lemma gauss_jordan_transform: assumes A: "A \<in> carrier\<^sub>m nr nc" and B: "B \<in> carrier\<^sub>m nr nc'"
  and res: "gauss_jordan (A :: 'a :: field mat) B = (A',B')"
  shows "\<exists> P \<in> Units (ring\<^sub>m TYPE('a) nr b). A' = P \<otimes>\<^sub>m A \<and> B' = P \<otimes>\<^sub>m B"
proof -
  let ?U = "Units (ring\<^sub>m TYPE('a) nr b)"
  interpret m: ring "ring\<^sub>m TYPE('a) nr b" by (rule mat_ring)
  {
    fix i j :: nat
    assume "gauss_jordan_main A B i j = (A',B')"
    with A B
    have "\<exists> P \<in> ?U. A' = P \<otimes>\<^sub>m A \<and> B' = P \<otimes>\<^sub>m B"
    proof (induction A B i j rule: gauss_jordan_main.induct)
      case (1 A B i j)
      note A = 1(5)
      hence dim: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc" by auto
      note B = 1(6)
      hence dimB: "dim\<^sub>r B = nr" "dim\<^sub>c B = nc'" by auto
      note IH = 1(1-4)[OF dim[symmetric]]
      note res = 1(7)
      note simp = gauss_jordan_main.simps[of A B i j] Let_def
      let ?g = "gauss_jordan_main A B i j"
      show ?case 
      proof (cases "i < nr \<and> j < nc")
        case False
        with res have res: "A' = A" "B' = B" unfolding simp dim by auto
        show ?thesis unfolding res
          by (rule bexI[of _ "\<one>\<^sub>m nr"], insert A B, auto simp: Units_def mat_ring_def)
      next
        case True note valid = this
        note IH = IH[OF valid refl]
        show ?thesis 
        proof (cases "A $$ (i,j) = 0")
          case False note nZ = this
          note IH = IH(3-4)[OF nZ]
          show ?thesis
          proof (cases "A $$ (i,j) = 1")
            case False note nO = this
            let ?inv = "inverse (A $$ (i,j))"
            from nO nZ valid res 
            have "gauss_jordan_main (multrow i ?inv A) (multrow i ?inv B) i j = (A',B')"
              unfolding simp dim by simp
            note IH = IH(2)[OF nO refl, unfolded multrow_closed, OF A B this]
            from IH obtain P where P: "P \<in> ?U" and
              id: "A' = P \<otimes>\<^sub>m multrow i ?inv A" "B' = P \<otimes>\<^sub>m multrow i ?inv B" by blast
            let ?Inv = "multrow_mat nr i ?inv"
            from nZ valid have "i < nr" "?inv \<noteq> 0" by auto
            from multrow_mat_Unit[OF this]
            have Inv: "?Inv \<in> ?U" .
            from m.Units_m_closed[OF P Inv] have PI: "P \<otimes>\<^sub>m ?Inv \<in> ?U" unfolding mat_ring_def by simp
            from m.Units_closed[OF P] have P: "P \<in> carrier\<^sub>m nr nr" unfolding mat_ring_def by simp
            show ?thesis unfolding id unfolding multrow_mat[OF A] multrow_mat[OF B]
              by (rule bexI[OF _ PI], intro conjI, 
                rule mat_mult_assoc[symmetric, OF P _ A], simp, 
                rule mat_mult_assoc[symmetric, OF P _ B], simp)
          next
            case True note O = this
            let ?E = "\<lambda> B. eliminate_entries A B i j (filter (\<lambda> i'. i' \<noteq> i) [0 ..< nr])"
            let ?A = "?E A"
            let ?B = "?E B"
            from O nZ valid res have "gauss_jordan_main ?A ?B (Suc i) (Suc j) = (A',B')"
              unfolding simp dim by simp
            note IH = IH(1)[OF O refl carrier_eliminate_entries[OF A] carrier_eliminate_entries[OF B] this]
            from IH obtain P where P: "P \<in> ?U" and id: "A' = P \<otimes>\<^sub>m ?A" "B' = P \<otimes>\<^sub>m ?B" by blast
            have "\<exists>P\<in>?U. \<forall> B nc. B \<in> carrier\<^sub>m nr nc \<longrightarrow> ?E B = P \<otimes>\<^sub>m B"
              by (rule Unit_prod_eliminate_entries, insert valid, auto)
            then obtain Q where Q: "Q \<in> ?U" and QQ: "\<And> B nc. B \<in> carrier\<^sub>m nr nc \<Longrightarrow> ?E B = Q \<otimes>\<^sub>m B" by auto
            have id3: "?A = Q \<otimes>\<^sub>m A" by (rule QQ[OF A])
            have id4: "?B = Q \<otimes>\<^sub>m B" by (rule QQ[OF B])
            from m.Units_closed[OF P] have Pc: "P \<in> carrier\<^sub>m nr nr" unfolding mat_ring_def by simp
            from m.Units_closed[OF Q] have Qc: "Q \<in> carrier\<^sub>m nr nr" unfolding mat_ring_def by simp
            from m.Units_m_closed[OF P Q] have PQ: "P \<otimes>\<^sub>m Q \<in> ?U" unfolding mat_ring_def by simp
            show ?thesis unfolding id unfolding id3 id4 
              by (rule bexI[OF _ PQ], rule conjI, 
              rule mat_mult_assoc[symmetric, OF Pc Qc A],
              rule mat_mult_assoc[symmetric, OF Pc Qc B])
          qed
        next
          case True note Z = this
          note IH = IH(1-2)[OF Z]
          let ?is = "[ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0]"
          show ?thesis
          proof (cases ?is)
            case Nil 
            from Z valid res have id: "gauss_jordan_main A B i (Suc j) = (A',B')" unfolding simp dim Nil by simp
            from IH(1)[OF Nil A B this] show ?thesis unfolding id .
          next
            case (Cons i' iis)
            from Z valid res have "gauss_jordan_main (swaprows i i' A) (swaprows i i' B) i j = (A',B')" 
              unfolding simp dim Cons by simp
            from IH(2)[OF Cons, unfolded swaprows_closed, OF A B this]
            obtain P where P: "P \<in> ?U" and
              id: "A' = P \<otimes>\<^sub>m swaprows i i' A" "B' = P \<otimes>\<^sub>m swaprows i i' B" by blast
            let ?Swap = "swaprows_mat nr i i'"
            from Cons have "i' \<in> set ?is" by auto
            with valid have i': "i < nr" "i' < nr" by auto
            from swaprows_mat_Unit[OF this] have Swap: "?Swap \<in> ?U" .
            from m.Units_m_closed[OF P Swap] have PI: "P \<otimes>\<^sub>m ?Swap \<in> ?U" unfolding mat_ring_def by simp
            from m.Units_closed[OF P] have P: "P \<in> carrier\<^sub>m nr nr" unfolding mat_ring_def by simp
            show ?thesis unfolding id swaprows_mat[OF A i'] swaprows_mat[OF B i']
              by (rule bexI[OF _ PI], rule conjI, 
              rule mat_mult_assoc[symmetric, OF P _ A], simp,
              rule mat_mult_assoc[symmetric, OF P _ B], simp)
          qed
        qed
      qed
    qed
  }
  from this[of 0 0, folded gauss_jordan_def, OF res] show ?thesis .
qed

lemma gauss_jordan_carrier: assumes A: "(A :: 'a :: field mat) \<in> carrier\<^sub>m nr nc"
  and B: "B \<in> carrier\<^sub>m nr nc'" 
  and res: "gauss_jordan A B = (A',B')"
  shows "A' \<in> carrier\<^sub>m nr nc" "B' \<in> carrier\<^sub>m nr nc'"
proof -
  from gauss_jordan_transform[OF A B res, of undefined]
  obtain P where P: "P \<in> Units (ring\<^sub>m TYPE('a) nr undefined)"
    and id: "A' = P \<otimes>\<^sub>m A" "B' = P \<otimes>\<^sub>m B" by auto
  from P have P: "P \<in> carrier\<^sub>m nr nr" unfolding Units_def mat_ring_def by auto
  show "A' \<in> carrier\<^sub>m nr nc" "B' \<in> carrier\<^sub>m nr nc'" unfolding id
    using P A B by auto
qed


definition pivot_fun :: "'a :: {zero,one} mat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "pivot_fun A f nc \<equiv> let nr = dim\<^sub>r A in 
    (\<forall> i < nr. f i \<le> nc \<and> 
      (f i < nc \<longrightarrow> A $$ (i, f i) = 1 \<and> (\<forall> i' < nr. i' \<noteq> i \<longrightarrow> A $$ (i',f i) = 0)) \<and> 
      (\<forall> j < f i. A $$ (i, j) = 0) \<and>
      (Suc i < nr \<longrightarrow> f (Suc i) > f i \<or> f (Suc i) = nc))"

lemma pivot_funI: assumes d: "dim\<^sub>r A = nr"
  and *: "\<And> i. i < nr \<Longrightarrow> f i \<le> nc"
      "\<And> i j. i < nr \<Longrightarrow> j < f i \<Longrightarrow> A $$ (i,j) = 0"
      "\<And> i. i < nr \<Longrightarrow> Suc i < nr \<Longrightarrow> f (Suc i) > f i \<or> f (Suc i) = nc"
      "\<And> i. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> A $$ (i, f i) = 1"
      "\<And> i i'. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> i' < nr \<Longrightarrow> i' \<noteq> i \<Longrightarrow> A $$ (i',f i) = 0"
  shows "pivot_fun A f nc"
  unfolding pivot_fun_def Let_def d using * by blast

lemma pivot_funD: assumes d: "dim\<^sub>r A = nr"
  and p: "pivot_fun A f nc"
  shows "\<And> i. i < nr \<Longrightarrow> f i \<le> nc"
      "\<And> i j. i < nr \<Longrightarrow> j < f i \<Longrightarrow> A $$ (i,j) = 0"
      "\<And> i. i < nr \<Longrightarrow> Suc i < nr \<Longrightarrow> f (Suc i) > f i \<or> f (Suc i) = nc"
      "\<And> i. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> A $$ (i, f i) = 1"
      "\<And> i i'. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> i' < nr \<Longrightarrow> i' \<noteq> i \<Longrightarrow> A $$ (i',f i) = 0"
  using p unfolding pivot_fun_def Let_def d by blast+

lemma pivot_fun_multrow: assumes p: "pivot_fun A f jj"
  and d: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc"
  and fi: "f ii = jj"
  and jj: "jj \<le> nc"
  shows "pivot_fun (multrow ii a A) f jj"
proof -
  note p = pivot_funD[OF d(1) p]
  let ?A = "multrow ii a A"
  have "dim\<^sub>r ?A = nr" using d by simp
  thus ?thesis
  proof (rule pivot_funI)
    fix i
    assume i: "i < nr"
    note p = p[OF i]
    show "f i \<le> jj" by fact
    show "Suc i < nr \<Longrightarrow> f i < f (Suc i) \<or> f (Suc i) = jj" by fact
    {
      fix i'
      assume *: "f i < jj" "i' < nr" "i' \<noteq> i" 
      from p(5)[OF this]
      show "?A $$ (i', f i) = 0"
        by (subst mat_index_multrow(1), insert * d jj, auto)
    }
    {
      assume *: "f i < jj"
      from p(4)[OF this] have A: "A $$ (i, f i) = 1" by auto
      show "?A $$ (i, f i) = 1"
        by (subst mat_index_multrow(1), insert * d i A jj fi, auto)
    }
    {
      fix j
      assume j: "j < f i"
      from p(2)[OF j]
      show "?A $$ (i, j) = 0"
        by (subst mat_index_multrow(1), insert j d i p jj fi, auto)
    }
  qed
qed

lemma pivot_fun_swaprows: assumes p: "pivot_fun A f jj"
  and d: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc"
  and flk: "f l = jj" "f k = jj"
  and nr: "l < nr" "k < nr"
  and jj: "jj \<le> nc"
  shows "pivot_fun (swaprows l k A) f jj"
proof -
  note pivot = pivot_funD[OF d(1) p]
  let ?A = "swaprows l k A"
  have "dim\<^sub>r ?A = nr" using d by simp
  thus ?thesis
  proof (rule pivot_funI)
    fix i
    assume i: "i < nr"
    note p = pivot[OF i]
    show "f i \<le> jj" by fact
    show "Suc i < nr \<Longrightarrow> f i < f (Suc i) \<or> f (Suc i) = jj" by fact
    {
      fix i'
      assume *: "f i < jj" "i' < nr" "i' \<noteq> i" 
      from *(1) flk have diff: "l \<noteq> i" "k \<noteq> i" by auto
      from p(5)[OF *] p(5)[OF *(1) nr(1) diff(1)] p(5)[OF *(1) nr(2) diff(2)]
      show "?A $$ (i', f i) = 0"  
        by (subst mat_index_swaprows(1), insert * d jj, auto)
    }
    {
      assume *: "f i < jj"
      from p(4)[OF this] have A: "A $$ (i, f i) = 1" by auto
      show "?A $$ (i, f i) = 1"
        by (subst mat_index_swaprows(1), insert * d i A jj flk, auto)
    }
    {
      fix j
      assume j: "j < f i"
      with p(1) flk have le: "j < f l" "j < f k" by auto
      from p(2)[OF j] pivot(2)[OF nr(1) le(1)] pivot(2)[OF nr(2) le(2)]
      show "?A $$ (i, j) = 0" 
        by (subst mat_index_swaprows(1), insert j d i p jj, auto) 
    }
  qed
qed

lemma pivot_fun_addrow: assumes p: "pivot_fun A f jj"
  and d: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc"
  and fl: "f l = jj"
  and nr: "k < nr" "l < nr"
  and jj: "jj \<le> nc"
  shows "pivot_fun (addrow a k l A) f jj"
proof -
  note pivot = pivot_funD[OF d(1) p]
  let ?A = "addrow a k l A"
  have "dim\<^sub>r ?A = nr" using d by simp
  thus ?thesis
  proof (rule pivot_funI)
    fix i
    assume i: "i < nr"
    note p = pivot[OF i]
    show "f i \<le> jj" by fact
    show "Suc i < nr \<Longrightarrow> f i < f (Suc i) \<or> f (Suc i) = jj" by fact
    {
      fix i'
      assume *: "f i < jj" "i' < nr" "i' \<noteq> i" 
      from *(1) fl have diff: "l \<noteq> i" by auto
      from p(5)[OF *] p(5)[OF *(1) nr(2) diff(1)] 
      show "?A $$ (i', f i) = 0"  
        by (subst mat_index_addrow(1), insert * d jj, auto)
    }
    {
      assume *: "f i < jj"
      from p(4)[OF this] have A: "A $$ (i, f i) = 1" by auto
      from p(5)[OF * nr(2)] * fl have AA: "A $$ (l, f i) = 0" by auto
      show "?A $$ (i, f i) = 1"
        by (subst mat_index_addrow(1), insert * d i A AA jj fl, auto)
    }
    {
      fix j
      assume j: "j < f i"
      with p(1) fl have le: "j < f l" by auto
      from p(2)[OF j] pivot(2)[OF nr(2) le]
      show "?A $$ (i, j) = 0" 
        by (subst mat_index_addrow(1), insert j d i p jj, auto) 
    }
  qed
qed

lemma pivot_fun_eliminate_rows: assumes p: "pivot_fun A f jj"
  and d: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc"
  and fl: "f l = jj"
  and nr: "l < nr"
  and jj: "jj \<le> nc"
  shows "set ks \<subseteq> {0 ..< nr} \<Longrightarrow> pivot_fun (eliminate_entries B A l j ks) f jj"
  using p d
proof (induct ks arbitrary: A)
  case (Cons k ks A)
  hence k: "k < nr" and rec: "set ks \<subseteq> {0 ..< nr}" by auto
  note IH = Cons(1)[OF rec]
  note pivot = Cons(3)
  note dim = Cons(4-5)
  let ?b = "B $$ (k, j)"
  let ?A = "addrow (- ?b) k l A"
  show ?case
  proof (cases "?b = 0")
    case True
    with IH[OF pivot dim]
    show ?thesis by simp
  next
    case False
    hence id: "eliminate_entries B A l j (k # ks) = eliminate_entries B ?A l j ks" by simp
    show ?thesis unfolding id
      by (rule IH[OF pivot_fun_addrow[OF pivot dim fl k nr jj]], insert dim, auto)
  qed
qed simp

lemma eliminate_rows_index: assumes d: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc"
  and lj: "l < nr" "j < nc" and A: "B $$ (l,j) = (1 :: 'a :: ring_1)"
  and i: "i < nr"
  shows "set ks \<subseteq> {0 ..< nr} \<Longrightarrow> distinct ks \<Longrightarrow> l \<notin> set ks \<Longrightarrow> 
    (\<And> k. k \<in> set ks \<Longrightarrow> B $$ (k,j) = A $$ (k,j)) \<Longrightarrow> B $$ (l,j) = A $$ (l,j) \<Longrightarrow>
    eliminate_entries B A l j ks $$ (i,j) = (if i \<in> set ks then 0 else A $$ (i,j))"
  using d 
proof (induct ks arbitrary: A)
  case (Cons k ks A)
  hence k: "k < nr" and rec: "set ks \<subseteq> {0 ..< nr}" by auto
  note IH = Cons(1)[OF rec]
  from Cons(3) have dist: "distinct ks" and kks: "k \<notin> set ks" by auto
  from Cons(4) have l: "l \<noteq> k" "l \<notin> set ks" by auto
  note eq = Cons(5)
  note eq2 = Cons(6)
  note dim = Cons(7-8)
  let ?b = "B $$ (k, j)"
  let ?A = "addrow (- ?b) k l A"
  show ?case
  proof (cases "?b = 0")
    case True
    with IH[OF dist l(2) eq eq2 dim] eq[of k]
    show ?thesis by simp
  next
    case False
    hence id: "eliminate_entries B A l j (k # ks) = eliminate_entries B ?A l j ks" by simp
    from dim have dimA: "dim\<^sub>r ?A = nr" "dim\<^sub>c ?A = nc" by auto
    show ?thesis unfolding id
    proof (subst IH[OF dist l(2) _ _ dimA])
      show "B $$ (l, j) = ?A $$ (l, j)" unfolding eq2 using dim lj l by auto
      fix k'
      assume kk': "k' \<in> set ks"
      with kks have k': "k' \<noteq> k" "k' \<in> set (k # ks)" by auto
      show "B $$ (k', j) = ?A $$ (k', j)"
        unfolding eq[OF k'(2)] using k'(1) dim lj rec kk' by auto
    next
      show "(if i \<in> set ks then 0 else ?A $$ (i, j)) =
        (if i \<in> set (k # ks) then 0 else A $$ (i, j))"
      proof (cases "i \<in> set (k # ks)")
        case False
        thus ?thesis using False k dim i lj by auto
      next
        case True
        show ?thesis
        proof (cases "i = k")
          case True
          thus ?thesis using kks k dim i lj A by (simp add: eq2 eq)
        qed (insert True, auto)
      qed
    qed
  qed
qed simp

definition row_echelon_form :: "'a :: {zero,one} mat \<Rightarrow> bool" where
  "row_echelon_form A \<equiv> \<exists> f. pivot_fun A f (dim\<^sub>c A)"

lemma pivot_fun_init: "pivot_fun A (\<lambda> _. 0) 0"
  by (rule pivot_funI, auto)

lemma gauss_jordan_main_row_echelon: 
  assumes 
    "A \<in> carrier\<^sub>m nr nc"
    "gauss_jordan_main A B i j = (A',B')"
    "pivot_fun A f j" 
    "\<And> i'. i' < i \<Longrightarrow> f i' < j" "\<And> i'. i' \<ge> i \<Longrightarrow> f i' = j"
    "i \<le> nr" "j \<le> nc"
  shows "row_echelon_form A'"
proof -
  fix b
  interpret m: ring "ring\<^sub>m TYPE('a) nr b" by (rule mat_ring)
  show ?thesis
    using assms
  proof (induct A B i j arbitrary: f rule: gauss_jordan_main.induct)
    case (1 A B i j f)
    note A = 1(5)
    hence dim: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc" by auto
    note res = 1(6)
    note pivot = 1(7)
    note f = 1(8-9)
    note ij = 1(10-11)
    note IH = 1(1-4)[OF dim[symmetric]]
    note simp = gauss_jordan_main.simps[of A B i j] Let_def
    let ?g = "gauss_jordan_main A B i j"
    show ?case 
    proof (cases "i < nr \<and> j < nc")
      case False note nij = this
      with res have id: "A' = A" unfolding simp dim by auto
      have "pivot_fun A f nc"
      proof (cases "j \<ge> nc")
        case True
        with ij have j: "j = nc" by auto
        with pivot show "pivot_fun A f nc" by simp
      next
        case False
        hence j: "j < nc" by simp
        from False nij ij have i: "i = nr" by auto
        note f = f[unfolded i]
        note p = pivot_funD[OF dim(1) pivot]
        show ?thesis
        proof (rule pivot_funI[OF dim(1)])
          fix i
          assume i: "i < nr"
          note p = p[OF i]
          from p(1) j show "f i \<le> nc" by simp
          from f(1)[OF i] have fij: "f i < j" .
          from p(4)[OF fij] show "A $$ (i, f i) = 1" .
          from p(5)[OF fij] show "\<And> i'. i' < nr \<Longrightarrow> i' \<noteq> i \<Longrightarrow> A $$ (i', f i) = 0" .
          show "\<And> j. j < f i \<Longrightarrow> A $$ (i, j) = 0" by (rule p(2))
          assume "Suc i < nr"
          with p(3)[OF this] f
          show "f i < f (Suc i) \<or> f (Suc i) = nc" by auto
        qed          
      qed
      thus ?thesis using pivot unfolding id row_echelon_form_def dim by blast
    next
      case True note valid = this
      hence sij: "Suc i \<le> nr" "Suc j \<le> nc" by auto
      note IH = IH[OF valid refl]
      show ?thesis 
      proof (cases "A $$ (i,j) = 0")
        case False note nZ = this
        note IH = IH(3-4)[OF nZ]
        show ?thesis
        proof (cases "A $$ (i,j) = 1")
          case False note nO = this
          let ?inv = "inverse (A $$ (i,j))"
          let ?A = "multrow i ?inv A"
          from nO nZ valid res have id: "gauss_jordan_main (multrow i ?inv A) (multrow i ?inv B) i j = (A', B')"
            unfolding simp dim by simp
          have "pivot_fun ?A f j"
            by (rule pivot_fun_multrow[OF pivot dim f(2) ij(2)], auto)
          note IH = IH(2)[OF nO refl, unfolded multrow_closed, OF A id this f ij]
          show ?thesis unfolding id using IH .
        next
          case True note O = this
          let ?E = "\<lambda> B. eliminate_entries A B i j (filter (\<lambda> i'. i' \<noteq> i) [0 ..< nr])"
          let ?A = "?E A"
          let ?B = "?E B"
          def E \<equiv> ?A
          let ?f = "\<lambda> i'. if i' = i then j else if i' > i then Suc j else f i'"
          have pivot: "pivot_fun E f j" unfolding E_def
            by (rule pivot_fun_eliminate_rows[OF pivot dim f(2)], insert valid, auto)
          {
            fix i'
            assume i': "i' < nr"
            have "E $$ (i', j) = (if i' = i then 1 else 0)"
              unfolding E_def
              by (subst eliminate_rows_index[OF dim _ _ O i'], insert valid O i', auto)
          } note Ej = this
          have E: "E \<in> carrier\<^sub>m nr nc" unfolding E_def by (rule carrier_eliminate_entries[OF A])
          hence dimE: "dim\<^sub>r E = nr" "dim\<^sub>c E = nc" by auto
          note pivot = pivot_funD[OF dimE(1) pivot]
          have "pivot_fun E ?f (Suc j)"
          proof (rule pivot_funI[OF dimE(1)])
            fix ii
            assume ii: "ii < nr"
            note p = pivot[OF ii]
            show "?f ii \<le> Suc j" using p(1) by simp
            {
              fix jj
              assume jj: "jj < ?f ii"
              show "E $$ (ii,jj) = 0"
              proof (cases "ii < i")
                case True
                with jj have "jj < f ii" by auto
                from p(2)[OF this] show ?thesis .
              next
                case False note ge = this
                with f have fiij: "f ii = j" by simp 
                show ?thesis
                proof (cases "i < ii")
                  case True
                  with jj have jj: "jj \<le> j" by auto
                  show ?thesis
                  proof (cases "jj < j")
                    case True
                    with p(2)[of jj] fiij show ?thesis by auto
                  next
                    case False
                    with jj have jj: "jj = j" by auto
                    with Ej[OF ii] True show ?thesis by auto
                  qed
                next
                  case False
                  with ge have ii: "ii = i" by simp
                  with jj have jj: "jj < j" by simp
                  from p(2)[of jj] ii jj fiij show ?thesis by auto
                qed
              qed
            }
            {
              assume "Suc ii < nr"
              from p(3)[OF this] f
              show "?f (Suc ii) > ?f ii \<or> ?f (Suc ii) = Suc j" by auto
            }
            {
              assume fii: "?f ii < Suc j"
              show "E $$ (ii, ?f ii) = 1"
              proof (cases "ii = i")
                case True
                with Ej[of i] valid show ?thesis by auto
              next
                case False
                with fii have ii: "ii < i" by (auto split: if_splits)
                from f(1)[OF this] have "f ii < j" by auto
                from p(4)[OF this] ii show ?thesis by simp
              qed
            }
            {
               fix i'
               assume *: "?f ii < Suc j" "i' < nr" "i' \<noteq> ii"
               show "E $$ (i', ?f ii) = 0"
               proof (cases "ii = i")
                 case False
                 with *(1) have iii: "ii < i" by (auto split: if_splits)
                 from f(1)[OF this] have "f ii < j" by auto
                 from p(5)[OF this *(2-3)] show ?thesis using iii by simp
               next
                 case True
                 with *(2-3) Ej[of i'] show ?thesis by auto
               qed
            }
          qed 
          note IH = IH(1)[OF O refl, folded E_def, OF E _ this _ _ sij]     
          from O nZ valid res have "gauss_jordan_main E ?B (Suc i) (Suc j) = (A', B')"
            unfolding E_def simp dim by simp
          note IH = IH[OF this]
          show ?thesis  
          proof (rule IH)
            fix i'
            assume "i' < Suc i"
            thus "?f i' < Suc j" using f[of i'] by (cases "i' < i", auto)
          qed auto
        qed
      next
        case True note Z = this
        note IH = IH(1-2)[OF Z]
        let ?is = "[ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0]"
        show ?thesis
        proof (cases ?is)
          case Nil
          {
            fix i'
            assume "i \<le> i'" and "i' < nr"
            hence "i' = i \<or> i' \<in> {Suc i ..< nr}" by auto
            from this arg_cong[OF Nil, of set] Z have "A $$ (i',j) = 0" by auto
          } note zero = this
          let ?f = "\<lambda> i'. if i' < i then f i' else Suc j"
          note p = pivot_funD[OF dim(1) pivot]
          have "pivot_fun A ?f (Suc j)"
          proof (rule pivot_funI[OF dim(1)])
            fix ii
            assume ii: "ii < nr"
            note p = p[OF this]
            show "?f ii \<le> Suc j" using p(1) by simp
            {
              fix jj
              assume jj: "jj < ?f ii"              
              show "A $$ (ii,jj) = 0"
              proof (cases "ii < i")
                case True
                with jj have "jj < f ii" by auto
                from p(2)[OF this] show ?thesis .
              next
                case False
                with jj have ii': "ii \<ge> i" and jjj: "jj \<le> j" by auto
                from zero[OF ii' ii] have Az: "A $$ (ii,j) = 0" .
                show ?thesis
                proof (cases "jj < j")
                  case False
                  with jjj have "jj = j" by auto
                  with Az show ?thesis by simp
                next
                  case True
                  show ?thesis
                    by (rule p(2), insert True False f, auto)
                qed
              qed
            }
            {
              assume sii: "Suc ii < nr"
              show "?f ii < ?f (Suc ii) \<or> ?f (Suc ii) = Suc j"
                using p(3)[OF sii] f by auto
            }
            {
              assume fii: "?f ii < Suc j"
              thus "A $$ (ii, ?f ii) = 1"
                using p(4) f by (cases "ii < i", auto)
              fix i'
              assume "i' < nr" "i' \<noteq> ii"
              from p(5)[OF _ this] f fii
              show "A $$ (i', ?f ii) = 0" 
                by (cases "ii < i", auto)
            }
          qed
          note IH = IH(1)[OF Nil A _ this _ _ ij(1) sij(2)]
          from Z valid res have "gauss_jordan_main A B i (Suc j) = (A',B')" unfolding simp dim Nil by simp
          note IH = IH[OF this]
          show ?thesis  
            by (rule IH, insert f, force+)
        next
          case (Cons i' iis)
          from arg_cong[OF this, of set] have i': "i' \<ge> Suc i" "i' < nr" by auto
          from f[of i] f[of "i'"] i' have fij: "f i = j" "f i' = j" by auto 
          let ?A = "swaprows i i' A"
          let ?B = "swaprows i i' B"
          have "pivot_fun ?A f j"
            by (rule pivot_fun_swaprows[OF pivot dim fij], insert i' ij, auto)
          note IH = IH(2)[OF Cons, unfolded swaprows_closed, OF A _ this f ij]
          from Z valid res have id: "gauss_jordan_main ?A ?B i j = (A', B')" unfolding simp dim Cons by simp
          note IH = IH[OF this]
          show ?thesis using IH .
        qed
      qed
    qed
  qed
qed

lemma gauss_jordan_row_echelon: 
  assumes A: "A \<in> carrier\<^sub>m nr nc" 
  and res: "gauss_jordan A B = (A', B')"
  shows "row_echelon_form A'"
  by (rule gauss_jordan_main_row_echelon[OF A res[unfolded gauss_jordan_def] pivot_fun_init], auto)

lemma pivot_bound: assumes dim: "dim\<^sub>r A = nr"
  and pivot: "pivot_fun A f n"
  shows "i + j < nr \<Longrightarrow> f (i + j) = n \<or> f (i + j) \<ge> j + f i"
proof (induct j)
  case (Suc j)
  hence IH: "f (i + j) = n \<or> j + f i \<le> f (i + j)" 
    and lt: "i + j < nr" "Suc (i + j) < nr" by auto
  note p = pivot_funD[OF dim pivot]
  from p(3)[OF lt] IH p(1)[OF lt(2)] show ?case by auto
qed simp

context
  fixes zero :: 'a
  and A :: "'a mat"
  and nr nc :: nat
begin
function pivot_positions_main_gen :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "pivot_positions_main_gen i j = (
     if i < nr then
       if j < nc then 
         if A $$ (i,j) = zero then 
           pivot_positions_main_gen i (Suc j)
         else (i,j) # pivot_positions_main_gen (Suc i) (Suc j)
       else []
     else [])" by pat_completeness auto

termination by (relation "measures [(\<lambda> (i,j). Suc nr - i), (\<lambda> (i,j). Suc nc - j)]", auto)

declare pivot_positions_main_gen.simps[simp del]
end

context
  fixes A :: "'a :: semiring_1 mat"
  and nr nc :: nat
begin

abbreviation "pivot_positions_main \<equiv> pivot_positions_main_gen (0 :: 'a) A nr nc"

lemma pivot_positions_main: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and pivot: "pivot_fun A f nc"
  shows "j \<le> f i \<or> i \<ge> nr \<Longrightarrow> 
    set (pivot_positions_main i j) = {(i', f i') | i'. i \<le> i' \<and> i' < nr} - UNIV \<times> {nc}
    \<and> distinct (map snd (pivot_positions_main i j))
    \<and> distinct (map fst (pivot_positions_main i j))"
proof (induct i j rule: pivot_positions_main_gen.induct[of nr nc A 0])
  case (1 i j)
  let ?a = "A $$ (i,j)"
  let ?pivot = "\<lambda> i j. pivot_positions_main i j"
  let ?set = "\<lambda> i. {(i',f i') | i'. i \<le> i' \<and> i' < nr}"
  let ?s = "?set i"
  let ?set = "\<lambda> i. {(i',f i') | i'. i \<le> i' \<and> i' < nr}"
  let ?s = "?set i"
  let ?p = "?pivot i j"
  from A have dA: "dim\<^sub>r A = nr" by simp
  note [simp] = pivot_positions_main_gen.simps[of 0 A nr nc i j]
  show ?case
  proof (cases "i < nr")
    case True note i = this
    note IH = 1(1-2)[OF True]
    have jfi: "j \<le> f i" using 1(3) i by auto
    note pivotB = pivot_bound[OF dA pivot]
    note pivot' = pivot_funD[OF dA pivot]
    note pivot = pivot'[OF True]
    have id1: "[i ..< nr] = i # [Suc i ..< nr]" using i by (rule upt_conv_Cons)
    show ?thesis
    proof (cases "j < nc")
      case True note j = this
      note IH = IH(1-2)[OF True]
      show ?thesis
      proof (cases "?a = 0")
        case True note a = this
        from i j a have p: "?p = ?pivot i (Suc j)" by simp
        {
          assume "f i = j"
          with pivot(4) j have "?a = 1" by simp
          with a have False by simp
        }
        with jfi have "Suc j \<le> f i \<or> i \<ge> nr" by fastforce
        note IH = IH(1)[OF True this]
        thus ?thesis unfolding p .
      next
        case False note a = this
        from i j a have p: "?p = (i,j) # ?pivot (Suc i) (Suc j)" by simp
        from pivot(2)[of j] jfi a have jfi: "j = f i" by force
        from pivotB[of i "Suc 0"] jfi have "Suc j \<le> f (Suc i) \<or> nr \<le> Suc i" 
          using Suc_le_eq j leI by auto
        note IH = IH(2)[OF False this]
        {
          fix i'
          assume *: "f i = f i'" "Suc i \<le> i'" "i' < nr" 
          hence "i + (i' - i) = i'" by auto
          from pivotB[of i "i' - i", unfolded this] * jfi j have False by auto
        } note distinct = this
        have id2: "?s = insert (i,j) (?set (Suc i))" using i jfi not_less_eq_eq
          by fastforce
        show ?thesis using IH j jfi i unfolding p id1 id2 by (auto intro: distinct)
      qed
    next
      case False note j = this
      from pivot(1) j jfi have *: "f i = nc" "nc = j" by auto
      from i j have p: "?p = []" by simp
      from pivotB[of i "Suc 0"] * have "j \<le> f (Suc i) \<or> nr \<le> Suc i" by auto
      {
        fix i'
        assume **: "i \<le> i'" "i' < nr" 
        hence "i + (i' - i) = i'" by auto
        from pivotB[of i "i' - i", unfolded this] ** * have "nc \<le> f i'" by auto
        with pivot'(1)[OF `i' < nr`] have "f i' = nc" by auto
      }
      thus ?thesis using IH unfolding p id1 by auto
    qed
  qed auto
qed
end

lemma pivot_fun_zero_row_iff: assumes pivot: "pivot_fun (A :: 'a :: semiring_1 mat) f nc"
  and A: "A \<in> carrier\<^sub>m nr nc"
  and i: "i < nr"
  shows "f i = nc \<longleftrightarrow> row A i = \<zero>\<^sub>v nc"
proof -
  from A have dim: "dim\<^sub>r A = nr" by auto
  note pivot = pivot_funD[OF dim pivot i]
  {
    assume "f i = nc"
    from pivot(2)[unfolded this]
    have "row A i = \<zero>\<^sub>v nc"
      by (intro vec_eqI, insert A, auto simp: row_def)
  }
  moreover
  {
    assume row: "row A i = \<zero>\<^sub>v nc"
    assume "f i \<noteq> nc"
    with pivot(1) have "f i < nc" by auto
    with pivot(4)[OF this] i A arg_cong[OF row, of "\<lambda> v. v $ f i"] have False by auto
  }
  ultimately show ?thesis by auto
qed

definition pivot_positions_gen :: "'a \<Rightarrow> 'a mat \<Rightarrow> (nat \<times> nat) list" where
  "pivot_positions_gen zer A \<equiv> pivot_positions_main_gen zer A (dim\<^sub>r A) (dim\<^sub>c A) 0 0"

abbreviation pivot_positions :: "'a :: semiring_1 mat \<Rightarrow> (nat \<times> nat) list" where
  "pivot_positions \<equiv> pivot_positions_gen 0"

lemmas pivot_positions_def = pivot_positions_gen_def

lemma pivot_positions: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and pivot: "pivot_fun A f nc"
  shows 
    "set (pivot_positions A) = {(i, f i) | i. i < nr \<and> f i \<noteq> nc}"
    "distinct (map fst (pivot_positions A))"
    "distinct (map snd (pivot_positions A))"
    "length (pivot_positions A) = card { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
proof -
  from A have dim: "dim\<^sub>r A = nr" by auto
  let ?pp = "pivot_positions A"
  show id: "set ?pp = {(i, f i) | i. i < nr \<and> f i \<noteq> nc}"
    and dist: "distinct (map fst ?pp)"
    and "distinct (map snd ?pp)"  
  using pivot_positions_main[OF A pivot, of 0 0] A
  unfolding pivot_positions_def by auto
  have "length ?pp = length (map fst ?pp)" by simp
  also have "\<dots> = card (fst ` set ?pp)" using distinct_card[OF dist] by simp
  also have "fst ` set ?pp = { i. i < nr \<and> f i \<noteq> nc}" unfolding id by force
  also have "\<dots> = { i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}"
    using pivot_fun_zero_row_iff[OF pivot A] by auto
  finally show "length ?pp = card {i. i < nr \<and> row A i \<noteq> \<zero>\<^sub>v nc}" .
qed

context 
  fixes uminus :: "'a \<Rightarrow> 'a"
  and zero :: 'a
  and one :: 'a
begin
definition non_pivot_base_gen :: "'a mat \<Rightarrow> (nat \<times> nat)list \<Rightarrow> nat \<Rightarrow> 'a vec" where
  "non_pivot_base_gen A pivots \<equiv> let nr = dim\<^sub>r A; nc = dim\<^sub>c A; 
     invers = map_of (map prod.swap pivots)
     in (\<lambda> qj. vec nc (\<lambda> i. 
     if i = qj then one else (case invers i of Some j => uminus (A $$ (j,qj)) | None \<Rightarrow> zero)))"

definition find_base_vectors_gen :: "'a mat \<Rightarrow> 'a vec list" where
  "find_base_vectors_gen A \<equiv> 
    let 
      pp = pivot_positions_gen zero A;     
      cands = filter (\<lambda> j. j \<notin> set (map snd pp)) [0 ..< dim\<^sub>c A]
    in map (non_pivot_base_gen A pp) cands"
end

abbreviation "non_pivot_base \<equiv> non_pivot_base_gen uminus 0 (1 :: 'a :: comm_ring_1)"
abbreviation "find_base_vectors \<equiv> find_base_vectors_gen uminus 0 (1 :: 'a :: comm_ring_1)"

lemmas non_pivot_base_def = non_pivot_base_gen_def
lemmas find_base_vectors_def = find_base_vectors_gen_def

text \<open>The soundness of @{const find_base_vectors} is proven in theory Matrix-Kern,
  where it is shown that @{const find_base_vectors} is a basis of the kern of $A$.\<close>

definition find_base_vector :: "'a :: comm_ring_1 mat \<Rightarrow> 'a vec" where
  "find_base_vector A \<equiv> 
    let 
      pp = pivot_positions A;     
      cands = filter (\<lambda> j. j \<notin> set (map snd pp)) [0 ..< dim\<^sub>c A]
    in non_pivot_base A pp (hd cands)"

context
  fixes A :: "'a :: field mat" and nr nc :: nat and p :: "nat \<Rightarrow> nat"
  assumes ref: "row_echelon_form A"
  and A: "A \<in> carrier\<^sub>m nr nc"
begin

lemma non_pivot_base:
  defines pp: "pp \<equiv> pivot_positions A"
  assumes qj: "qj < nc" "qj \<notin> snd ` set pp" 
  shows "non_pivot_base A pp qj \<in> carrier\<^sub>v nc"
    "non_pivot_base A pp qj $ qj = 1"
    "A \<otimes>\<^sub>m\<^sub>v non_pivot_base A pp qj = \<zero>\<^sub>v nr"
    "\<And> qj'. qj' < nc \<Longrightarrow> qj' \<notin> snd ` set pp \<Longrightarrow> qj \<noteq> qj' \<Longrightarrow> non_pivot_base A pp qj $ qj' = 0"
proof -
  from A have dim: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
  where pivot: "pivot_fun A p nc" using dim by auto
  note pivot' = pivot_funD[OF dim(1) pivot]
  note pp = pivot_positions[OF A pivot, folded pp]
  let ?p = "\<lambda> i. i < nr \<and> p i = nc \<or> i = nr"
  let ?spp = "map prod.swap pp"
  let ?map = "map_of ?spp"
  def I \<equiv> "\<lambda> i. case map_of (map prod.swap pp) i of Some j \<Rightarrow> - A $$ (j,qj) | None \<Rightarrow> 0"
  have d: "non_pivot_base A pp qj = vec nc (\<lambda> i. if i = qj then 1 else I i)"
    unfolding non_pivot_base_def Let_def dim I_def ..
  from pp have dist: "distinct (map fst ?spp)" 
    unfolding map_map o_def prod.swap_def by auto
  let ?r = "set (map snd pp)"
  have r: "?r = p ` {0 ..< nr} - {nc}" unfolding set_map pp by force
  let ?l = "set (map fst pp)"
  from qj have qj': "qj \<notin> p ` {0 ..< nr}" using r by auto
  let ?v = "non_pivot_base A pp qj"
  let ?P = "p ` {0 ..< nr}"
  have dimv: "dim\<^sub>v ?v = nc" unfolding d by simp
  thus "?v \<in> carrier\<^sub>v nc" unfolding vec_carrier_def by auto
  show vqj: "?v $ qj = 1" unfolding d using qj by auto
  { 
    fix qj'
    assume *: "qj' < nc" "qj \<noteq> qj'" "qj' \<notin> snd ` set pp"
    hence "?map qj' = None" unfolding map_of_eq_None_iff by force
    hence "I qj' = 0" unfolding I_def by simp
    with * show "non_pivot_base A pp qj $ qj' = 0" 
      unfolding d by simp
  }    
  {
    fix i
    assume i: "i < nr"
    let ?I = "{j. ?map j = Some i}"
    have "row A i \<bullet> ?v = 0" 
    proof -
      have id: "({0..<nc} \<inter> ?P) \<union> ({0..<nc} - ?P) = {0..<nc}" by auto
      let ?e = "\<lambda> j. row A i $ j * ?v $ j"
      let ?e' = "\<lambda> j. (if ?map j = Some i then - A $$ (i, qj) else 0)"
      {
        fix j
        assume j: "j < nc" "j \<in> ?P"
        then obtain ii where ii: "ii < nr" and jpi: "j = p ii" and pii: "p ii < nc" by auto
        hence mem: "(ii,j) \<in> set pp" and "(j,ii) \<in> set ?spp" by (auto simp: pp)        
        from map_of_is_SomeI[OF dist this(2)] 
        have map: "?map j = Some ii" by auto
        from mem j qj have jqj: "j \<noteq> qj" by force
        note p = pivot'(4-5)[OF ii pii]
        def start \<equiv> "?e j"
        have "start = A $$ (i,j) * ?v $ j" using j i A by (auto simp: start_def)
        also have "A $$ (i,j) = A $$ (i, p ii)" unfolding jpi ..
        also have "\<dots> = (if i = ii then 1 else 0)" using p(1) p(2)[OF i] by auto
        also have "\<dots> * ?v $ j = (if i = ii then ?v $ j else 0)" by simp
        also have "?v $ j = I j" unfolding d 
          using j jqj A by auto
        also have "I j = - A $$ (ii, qj)" unfolding I_def map by simp
        finally have "?e j = ?e' j" 
          unfolding start_def map by auto
      } note piv = this
      have "row A i \<bullet> ?v = (\<Sum> j = 0..<nc. ?e j)" unfolding row_def scalar_prod_def dimv ..
      also have "\<dots> = setsum ?e ({0..<nc} \<inter> ?P) + setsum ?e ({0..<nc} - ?P)"
        by (subst setsum.union_disjoint[symmetric], auto simp: id)
      also have "setsum ?e ({0..<nc} - ?P) = ?e qj + setsum ?e ({0 ..<nc} - ?P - {qj})"
        by (rule setsum.remove, insert qj qj', auto)
      also have "?e qj = row A i $ qj" unfolding vqj by simp
      also have "row A i $ qj = A $$ (i, qj)" using i A qj by auto
      also have "setsum ?e ({0 ..<nc} - ?P - {qj}) = 0"
      proof (rule setsum.neutral, intro ballI)
        fix j
        assume "j \<in> {0 ..<nc} - ?P - {qj}"
        hence j: "j < nc" "j \<notin> ?P" "j \<noteq> qj" "j \<notin> ?r" unfolding r by auto
        hence id: "map_of ?spp j = None" unfolding map_of_eq_None_iff by force
        have "?v $ j = I j" unfolding d using j by simp
        also have "\<dots> = 0" unfolding I_def id by simp 
        finally show "row A i $ j * ?v $ j = 0" by simp
      qed
      also have "A $$ (i, qj) + 0 = A $$ (i, qj)" by simp
      also have "setsum ?e ({0..<nc} \<inter> ?P) = setsum ?e' ({0..<nc} \<inter> ?P)"
        by (rule setsum.cong, insert piv, auto)
      also have "{0..<nc} \<inter> ?P = {0..<nc} \<inter> ?I \<inter> ?P \<union> ({0..<nc} - ?I) \<inter> ?P" by auto
      also have "setsum ?e' ({0..<nc} \<inter> ?I \<inter> ?P \<union> ({0..<nc} - ?I) \<inter> ?P)
        = setsum ?e' ({0..<nc} \<inter> ?I \<inter> ?P) + setsum ?e' (({0..<nc} - ?I) \<inter> ?P)"
        by (rule setsum.union_disjoint, auto)
      also have "setsum ?e' (({0..<nc} - ?I) \<inter> ?P) = 0"
        by (rule setsum.neutral, auto)
      also have "setsum ?e' ({0..<nc} \<inter> ?I \<inter> ?P) = 
        setsum (\<lambda> _. - A $$ (i, qj)) ({0..<nc} \<inter> ?I \<inter> ?P)"
        by (rule setsum.cong, auto)
      also have "\<dots> + 0 = \<dots>" by simp
      also have "setsum (\<lambda> _. - A $$ (i, qj)) ({0..<nc} \<inter> ?I \<inter> ?P) + A $$ (i, qj) = 0" 
      proof (cases "i \<in> ?l")
        case False
        with pp(1) i have "p i = nc" by force
        from pivot'(2)[OF i, unfolded this, OF qj(1)] have z: "A $$ (i, qj) = 0" .
        show ?thesis 
          by (subst setsum.neutral, auto simp: z)
      next
        case True
        then obtain j where mem: "(i,j) \<in> set pp" and id: "(j,i) \<in> set ?spp" by auto
        from map_of_is_SomeI[OF dist this(2)] have map: "?map j = Some i" .
        from pivot'(1)[OF i] have pi: "p i \<le> nc" .
        with mem[unfolded pp] have j: "j = p i" "j < nc" by auto
        {
          fix j'
          assume "j' \<in> ?I"
          hence "?map j' = Some i" by auto
          from map_of_SomeD[OF this] have "(i, j') \<in> set pp" by auto
          with mem pp(2) have "j' = j" using map_of_is_SomeI by fastforce
        }
        with map have II: "?I = {j}" by blast
        have II: "{0..<nc} \<inter> ?I \<inter> ?P = {j}" unfolding II using mem[unfolded pp] i j by auto
        show ?thesis unfolding II by simp
      qed
      finally show "row A i \<bullet> ?v = 0" .
    qed
  } note main = this
  show "A \<otimes>\<^sub>m\<^sub>v ?v = \<zero>\<^sub>v nr"  
    by (rule vec_eqI, auto simp: dim main)
qed

lemma find_base_vector: assumes "snd ` set (pivot_positions A) \<noteq> {0 ..< nc}"
  shows 
    "find_base_vector A \<in> carrier\<^sub>v nc"
    "find_base_vector A \<noteq> \<zero>\<^sub>v nc"
    "A \<otimes>\<^sub>m\<^sub>v find_base_vector A = \<zero>\<^sub>v nr"
proof -
  def cands \<equiv> "filter (\<lambda> j. j \<notin> snd ` set (pivot_positions A)) [0 ..< nc]"
  from A have dim: "dim\<^sub>r A = nr" "dim\<^sub>c A = nc" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
  where pivot: "pivot_fun A p nc" using dim by auto
  note piv = pivot_funD[OF dim(1) pivot]
  have "set cands \<noteq> {}" using assms piv unfolding cands_def  pivot_positions[OF A pivot]
    by (auto simp: le_neq_implies_less)
  then obtain c cs where cands: "cands = c # cs" by (cases cands, auto)
  hence res: "find_base_vector A = non_pivot_base A (pivot_positions A) c"
    unfolding find_base_vector_def Let_def cands_def dim by auto
  from cands have "c \<in> set cands" by auto
  hence c: "c < nc" "c \<notin> snd ` set (pivot_positions A)"
    unfolding cands_def by auto
  from non_pivot_base[OF this, folded res] c show
    "find_base_vector A \<in> carrier\<^sub>v nc"
    "find_base_vector A \<noteq> \<zero>\<^sub>v nc"
    "A \<otimes>\<^sub>m\<^sub>v find_base_vector A = \<zero>\<^sub>v nr"
  by auto
qed
end

lemma row_echelon_form_imp_1_or_0_row: assumes A: "A \<in> carrier\<^sub>m n n"
  and row: "row_echelon_form A"
  shows "A = \<one>\<^sub>m n \<or> (n > 0 \<and> row A (n - 1) = \<zero>\<^sub>v n)"
proof -
  from A have dim: "dim\<^sub>r A = n" "dim\<^sub>c A = n" by auto
  from row[unfolded row_echelon_form_def] A
  obtain f where pivot: "pivot_fun A f n" by auto
  note p = pivot_funD[OF dim(1) this]
  show ?thesis
  proof (cases "\<exists> i < n. f i \<noteq> i")
    case True
    then obtain i where i: "i < n" and fi: "f i \<noteq> i" by auto
    note pb = pivot_bound[OF dim(1) pivot]
    from pb[of 0 i] i have "f i = n \<or> i \<le> f i" by auto
    with fi have fi: "f i = n \<or> i < f i" by auto
    from i have n: "n - 1 = i + (n - i - 1)" by auto
    from pb[of i "n - i - 1", folded n] fi i p(1)[of "n - 1"] 
    have fn: "f (n - 1) = n" by auto
    from i have n0: "n > 0" and n1: "n - 1 < n" by auto
    from p(2)[OF n1, unfolded fn] have zero: "\<And> j. j < n \<Longrightarrow> A $$ (n - 1, j) = 0" by auto
    show ?thesis
      by (rule disjI2[OF conjI[OF n0]], rule vec_eqI, insert zero A, auto)
  next
    case False
    {
      fix j
      assume j: "j < n"
      with False have id: "f j = j" by auto
      note pj = p[OF j, unfolded id]
      from pj(5)[OF j] pj(4)[OF j] 
      have "\<And> i. i < n \<Longrightarrow> A $$ (i,j) = (if i = j then 1 else 0)" by auto
    } note id = this
    show ?thesis
      by (rule disjI1, rule mat_eqI, subst id, insert A, auto)
  qed
qed

context
  fixes A :: "'a :: field mat" and n :: nat and p :: "nat \<Rightarrow> nat"
  assumes ref: "row_echelon_form A"
  and A: "A \<in> carrier\<^sub>m n n"
  and 1: "A \<noteq> \<one>\<^sub>m n"
begin

lemma find_base_vector_not_1_pivot_positions: "snd ` set (pivot_positions A) \<noteq> {0 ..< n}"
proof 
  let ?pp = "pivot_positions A"
  assume id: "snd ` set ?pp = {0 ..< n}"
  from A have dim: "dim\<^sub>r A = n" "dim\<^sub>c A = n" by auto
  let ?n = "n - 1"
  from row_echelon_form_imp_1_or_0_row[OF A ref] 1
  have *: "0 < n" and row: "row A ?n = \<zero>\<^sub>v n" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
    where pivot: "pivot_fun A p n" using dim by auto
  note pp = pivot_positions[OF A pivot]
  note piv = pivot_funD[OF dim(1) pivot]
  from * have n: "?n < n" by auto
  {
    
    assume "p ?n < n"
    with piv(4)[OF n this] row n A have False
      by (metis dim row_index(1) vec_zero_index(1) zero_neq_one)
  }
  with piv(1)[OF n] have pn: "p ?n = n" by fastforce
  hence "?n \<notin> fst ` set ?pp" unfolding pp by auto
  hence "fst ` set ?pp \<subseteq> {0 ..< n} - {?n}" unfolding pp by force
  also have "\<dots> \<subseteq> {0 ..< n - 1}" by auto
  finally have "card (fst ` set ?pp) \<le> card {0 ..< n - 1}" using card_mono by blast
  also have "\<dots> = n - 1" by auto
  also have "card (fst ` set ?pp) = card (snd ` set ?pp)"
    unfolding set_map[symmetric] distinct_card[OF pp(2)] distinct_card[OF pp(3)] by simp
  also have "\<dots> = n" unfolding id by simp
  finally show False using n by simp
qed
  
lemma find_base_vector_not_1: 
    "find_base_vector A \<in> carrier\<^sub>v n"
    "find_base_vector A \<noteq> \<zero>\<^sub>v n"
    "A \<otimes>\<^sub>m\<^sub>v find_base_vector A = \<zero>\<^sub>v n"
  using find_base_vector[OF ref A find_base_vector_not_1_pivot_positions] .
end

lemma gauss_jordan: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and B: "B \<in> carrier\<^sub>m nr nc2"
  and gauss: "gauss_jordan A B = (C,D)"
  shows "x \<in> carrier\<^sub>v nc \<Longrightarrow> (A \<otimes>\<^sub>m\<^sub>v x = \<zero>\<^sub>v nr) = (C \<otimes>\<^sub>m\<^sub>v x = \<zero>\<^sub>v nr)" (is "_ \<Longrightarrow> ?l = ?r")
    "w \<in> carrier\<^sub>v nc \<Longrightarrow> X \<in> carrier\<^sub>m nc nc2  \<Longrightarrow> (A \<otimes>\<^sub>m X = B) = (C \<otimes>\<^sub>m X = D)" (is "_ \<Longrightarrow> _ \<Longrightarrow> ?l2 = ?r2")
    "C \<in> carrier\<^sub>m nr nc"
    "D \<in> carrier\<^sub>m nr nc2"
proof -
  from gauss_jordan_transform[OF A B gauss, unfolded mat_ring_def Units_def, simplified]
  obtain P Q where P: "P \<in> carrier\<^sub>m nr nr" and Q: "Q \<in> carrier\<^sub>m nr nr"
    and inv: "Q \<otimes>\<^sub>m P = \<one>\<^sub>m nr" 
    and CPA: "C = P \<otimes>\<^sub>m A" 
    and DPB: "D = P \<otimes>\<^sub>m B" by auto
  from CPA P A show C: "C \<in> carrier\<^sub>m nr nc" by auto
  from DPB P B show D: "D \<in> carrier\<^sub>m nr nc2" by auto
  have "A = \<one>\<^sub>m nr \<otimes>\<^sub>m A" using A by simp
  also have "\<dots> = Q \<otimes>\<^sub>m C" unfolding inv[symmetric] CPA using Q P A by simp
  finally have AQC: "A = Q \<otimes>\<^sub>m C" .
  have "B = \<one>\<^sub>m nr \<otimes>\<^sub>m B" using B by simp
  also have "\<dots> = Q \<otimes>\<^sub>m D" unfolding inv[symmetric] DPB using Q P B by simp
  finally have BQD: "B = Q \<otimes>\<^sub>m D" .
  {
    assume x: "x \<in> carrier\<^sub>v nc"
    {
      assume ?l
      from arg_cong[OF this, of "\<lambda> v. P \<otimes>\<^sub>m\<^sub>v v"] P A x have ?r unfolding CPA by auto
    }
    moreover
    {
      assume ?r
      from arg_cong[OF this, of "\<lambda> v. Q \<otimes>\<^sub>m\<^sub>v v"] Q C x have ?l unfolding AQC by auto
    }
    ultimately show "?l = ?r" by auto
  }
  {
    assume X: "X \<in> carrier\<^sub>m nc nc2"
    {
      assume ?l2
      from arg_cong[OF this, of "\<lambda> X. P \<otimes>\<^sub>m X"] P A X have ?r2 unfolding CPA DPB by simp
    }
    moreover
    {
      assume ?r2
      from arg_cong[OF this, of "\<lambda> X. Q \<otimes>\<^sub>m X"] Q C X have ?l2 unfolding AQC BQD by simp
    }
    ultimately show "?l2 = ?r2" by auto
  }
qed

definition gauss_jordan_single :: "'a :: field mat \<Rightarrow> 'a mat" where
  "gauss_jordan_single A = fst (gauss_jordan A (\<zero>\<^sub>m (dim\<^sub>r A) 0))"

lemma gauss_jordan_single: assumes A: "A \<in> carrier\<^sub>m nr nc"
  and gauss: "gauss_jordan_single A = C"
  shows "x \<in> carrier\<^sub>v nc \<Longrightarrow> (A \<otimes>\<^sub>m\<^sub>v x = \<zero>\<^sub>v nr) = (C \<otimes>\<^sub>m\<^sub>v x = \<zero>\<^sub>v nr)" 
    "C \<in> carrier\<^sub>m nr nc"
    "row_echelon_form C"
    "\<exists> P Q. C = P \<otimes>\<^sub>m A \<and> P \<in> carrier\<^sub>m nr nr \<and> Q \<in> carrier\<^sub>m nr nr \<and> P \<otimes>\<^sub>m Q = \<one>\<^sub>m nr \<and> Q \<otimes>\<^sub>m P = \<one>\<^sub>m nr" (is "?ex")
proof -
  from A gauss[unfolded gauss_jordan_single_def] obtain D where gauss: "gauss_jordan A (\<zero>\<^sub>m nr 0) = (C,D)"
    by (cases "gauss_jordan A (\<zero>\<^sub>m nr 0)", auto)
  from gauss_jordan[OF A mat_zero_closed gauss] gauss_jordan_row_echelon[OF A gauss]
    gauss_jordan_transform[OF A mat_zero_closed gauss, of "()"]
  show "x \<in> carrier\<^sub>v nc \<Longrightarrow> (A \<otimes>\<^sub>m\<^sub>v x = \<zero>\<^sub>v nr) = (C \<otimes>\<^sub>m\<^sub>v x = \<zero>\<^sub>v nr)" 
    "C \<in> carrier\<^sub>m nr nc" "row_echelon_form C" ?ex unfolding Units_def mat_ring_def by auto
qed



lemma gauss_jordan_inverse_one_direction: 
  assumes A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n nc"
  and res: "gauss_jordan A B = (\<one>\<^sub>m n, B')"
  shows "A \<in> Units (ring\<^sub>m TYPE('a :: field) n b)"
  "B = \<one>\<^sub>m n \<Longrightarrow> A \<otimes>\<^sub>m B' = \<one>\<^sub>m n \<and> B' \<otimes>\<^sub>m A = \<one>\<^sub>m n"
proof -
  let ?R = "ring\<^sub>m TYPE('a) n b"
  let ?U = "Units ?R"
  interpret m: ring ?R by (rule mat_ring)
  from gauss_jordan_transform[OF A B res, of b]
  obtain P where P: "P \<in> ?U" and id: "P \<otimes>\<^sub>m A = \<one>\<^sub>m n" and B': "B' = P \<otimes>\<^sub>m B" by auto
  from P have Pc: "P \<in> carrier\<^sub>m n n" unfolding Units_def mat_ring_def by auto
  from m.Units_one_side_I(1)[of A P] A P id show Au: "A \<in> ?U" unfolding mat_ring_def by auto
  assume B: "B = \<one>\<^sub>m n" 
  from B'[unfolded this] Pc have B': "B' = P" by auto
  show "A \<otimes>\<^sub>m B' = \<one>\<^sub>m n \<and> B' \<otimes>\<^sub>m A = \<one>\<^sub>m n" unfolding B' 
    using m.Units_inv_comm[OF _ P Au] id by (auto simp: mat_ring_def)
qed

lemma gauss_jordan_inverse_other_direction: 
  assumes AU: "A \<in> Units (ring\<^sub>m TYPE('a :: field) n b)" and B: "B \<in> carrier\<^sub>m n nc"
  shows "fst (gauss_jordan A B) = \<one>\<^sub>m n"
proof -
  let ?R = "ring\<^sub>m TYPE('a) n b"
  let ?U = "Units ?R"
  interpret m: ring ?R by (rule mat_ring)
  from AU have A: "A \<in> carrier\<^sub>m n n" unfolding Units_def mat_ring_def by auto
  obtain A' B' where res: "gauss_jordan A B = (A',B')" by force
  from gauss_jordan_transform[OF A B res, of b]
  obtain P where P: "P \<in> ?U" and id: "A' = P \<otimes>\<^sub>m A" by auto
  from m.Units_m_closed[OF P AU]  have A': "A' \<in> ?U" unfolding id mat_ring_def by auto
  hence A'c: "A' \<in> carrier\<^sub>m n n" unfolding Units_def mat_ring_def by auto
  from A'[unfolded Units_def mat_ring_def] obtain IA' where IA': "IA' \<in> carrier\<^sub>m n n"
    and IA: "A' \<otimes>\<^sub>m IA' = \<one>\<^sub>m n" by auto
  from row_echelon_form_imp_1_or_0_row[OF gauss_jordan_carrier(1)[OF A B res] gauss_jordan_row_echelon[OF A res]] 
  have choice: "A' = \<one>\<^sub>m n \<or> 0 < n \<and> row A' (n - 1) = \<zero>\<^sub>v n" .
  hence "A' = \<one>\<^sub>m n"
  proof 
    let ?n = "n - 1"
    assume "0 < n \<and> row A' ?n = \<zero>\<^sub>v n" 
    hence n: "?n < n" and row: "row A' ?n =  \<zero>\<^sub>v n" by auto
    have "1 = \<one>\<^sub>m n $$ (?n,?n)" using n by simp
    also have "\<one>\<^sub>m n = A' \<otimes>\<^sub>m IA'" unfolding IA ..
    also have "(A' \<otimes>\<^sub>m IA') $$ (?n, ?n) = row A' ?n \<bullet> col IA' ?n"
      using n IA' A'c by simp
    also have "row A' ?n = \<zero>\<^sub>v n" unfolding row ..
    also have "\<zero>\<^sub>v n \<bullet> col IA' ?n = 0" using IA' n by simp
    finally have "1 = (0 :: 'a)" by simp
    thus ?thesis by simp
  qed 
  with res show ?thesis by simp
qed

lemma gauss_jordan_compute_inverse:
  assumes A: "A \<in> carrier\<^sub>m n n"
  and res: "gauss_jordan A (\<one>\<^sub>m n) = (\<one>\<^sub>m n, B')"
  shows "A \<otimes>\<^sub>m B' = \<one>\<^sub>m n" "B' \<otimes>\<^sub>m A = \<one>\<^sub>m n" "B' \<in> carrier\<^sub>m n n"
proof -
  from gauss_jordan_inverse_one_direction(2)[OF A _ res refl, of n]
  show "A \<otimes>\<^sub>m B' = \<one>\<^sub>m n" "B' \<otimes>\<^sub>m A = \<one>\<^sub>m n" by auto
  from gauss_jordan_carrier(2)[OF A _ res, of n] show "B' \<in> carrier\<^sub>m n n" by auto
qed

lemma gauss_jordan_check_invertable: assumes A: "A \<in> carrier\<^sub>m n n" and B: "B \<in> carrier\<^sub>m n nc"
  shows "(A \<in> Units (ring\<^sub>m TYPE('a :: field) n b)) \<longleftrightarrow> fst (gauss_jordan A B) = \<one>\<^sub>m n"
  (is "?l = ?r")
proof 
  assume ?l
  show ?r
    by (rule gauss_jordan_inverse_other_direction[OF `?l` B])
next
  let ?g = "gauss_jordan A B"
  assume ?r
  then obtain B' where "?g = (\<one>\<^sub>m n, B')" by (cases ?g, auto)
  from gauss_jordan_inverse_one_direction(1)[OF A B this]
  show ?l .
qed

definition mat_inverse :: "'a :: field mat \<Rightarrow> 'a mat option" where 
  "mat_inverse A = (if dim\<^sub>r A = dim\<^sub>c A then
    let one = \<one>\<^sub>m (dim\<^sub>r A) in
    (case gauss_jordan A one of
      (B, C) \<Rightarrow> if B = one then Some C else None) else None)"

lemma mat_inverse: assumes A: "A \<in> carrier\<^sub>m n n"
  shows "mat_inverse A = None \<Longrightarrow> A \<notin> Units (ring\<^sub>m TYPE('a :: field) n b)"
    "mat_inverse A = Some B \<Longrightarrow> A \<otimes>\<^sub>m B = \<one>\<^sub>m n \<and> B \<otimes>\<^sub>m A = \<one>\<^sub>m n \<and> B \<in> carrier\<^sub>m n n"
proof -
  let ?one = "\<one>\<^sub>m n"
  obtain BB C where res: "gauss_jordan A ?one = (BB,C)" by force
  {
    assume "mat_inverse A = None"
    with res have "BB \<noteq> ?one" unfolding mat_inverse_def using A by auto
    thus "A \<notin> Units (ring\<^sub>m TYPE('a :: field) n b)"
      using gauss_jordan_check_invertable[OF A, of ?one n] res by force
  }
  {
    assume "mat_inverse A = Some B"
    with res A have "BB = ?one" "C = B" unfolding mat_inverse_def
      by (auto split: if_splits option.splits)
    from gauss_jordan_compute_inverse[OF A res[unfolded this]]
    show "A \<otimes>\<^sub>m B = \<one>\<^sub>m n \<and> B \<otimes>\<^sub>m A = \<one>\<^sub>m n \<and> B \<in> carrier\<^sub>m n n" by auto
  }
qed
end