section \<open>More on Determinants\<close>

text \<open>We require the result that for a block-matrix where the upper-right block is 0
  the determinant is precisely the determinant of the upper-left block times the determinant
  of the lower-right block. Moreover, we provide lemmas which show how a determinant changes
  signs if one swaps blocks of rows or blocks of columns.\<close>
  
theory Missing_Determinant
  imports 
  "../Jordan_Normal_Form/Determinant"
begin

lemma mat_cong: assumes "nr = nr'" "nc = nc'" "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> 
  f (i,j) = f' (i,j)" shows "mat nr nc f = mat nr' nc' f'" 
  by (rule mat_eqI, insert assms, auto)
  
lemma det_swap_rows: assumes A: "A \<in> carrier\<^sub>m (k + n) (k + n)" 
  shows "det A = (-1)^(k * n) * det (mat (k + n) (k + n) (\<lambda> (i,j). let r = 
      (if i < k then i + n else i - k)
      in A $$ (r,j)))" (is "_ = _ * det ?B")
proof -
  define sw where "sw = (\<lambda> (A :: 'a mat) xs. fold (\<lambda> (i,j). swaprows i j) xs A)"
  have dim_sw[simp]: "dim\<^sub>r (sw A xs) = dim\<^sub>r A" "dim\<^sub>c (sw A xs) = dim\<^sub>c A" for xs A
    unfolding sw_def by (induct xs arbitrary: A, auto)
  {
    fix xs and A :: "'a mat"
    assume "dim\<^sub>r A = dim\<^sub>c A" "\<And> i j. (i,j) \<in> set xs \<Longrightarrow> i < dim\<^sub>c A \<and> j < dim\<^sub>c A \<and> i \<noteq> j"
    hence "det (sw A xs) = (-1)^(length xs) * det A"
      unfolding sw_def
    proof (induct xs arbitrary: A)
      case (Cons xy xs A)
      obtain x y where xy: "xy = (x,y)" by force
      from Cons(3)[unfolded xy, of x y] Cons(2)
      have [simp]: "det (swaprows x y A) = - det A"
        by (intro det_swaprows, auto)
      show ?case unfolding xy by (simp, insert Cons(2-), (subst Cons(1), auto)+)
    qed simp
  } note sw = this
  define swb where "swb = (\<lambda> A i n. sw A (map (\<lambda> j. (j,Suc j)) [i ..< i + n]))"
  {
    fix k n and A :: "'a mat"
    assume k_n: "k + n < dim\<^sub>r A"
    hence "swb A k n = mat (dim\<^sub>r A) (dim\<^sub>c A) (\<lambda> (i,j). let r = 
      (if i < k \<or> i > k + n then i else if i = k + n then k else Suc i)
      in A $$ (r,j))"
    proof (induct n)
      case 0
      show ?case unfolding swb_def sw_def by (rule mat_eqI, auto)
    next
      case (Suc n)
      hence dim: "k + n < dim\<^sub>r A" by auto
      have id: "swb A k (Suc n) = swaprows (k + n) (Suc k + n) (swb A k n)" unfolding swb_def sw_def by simp
      show ?case unfolding id Suc(1)[OF dim]
        by (rule mat_eqI, insert Suc(2), auto)
    qed
  } note swb = this
  define swbl where "swbl = (\<lambda> A k n. fold (\<lambda> i A. swb A i n) (rev [0 ..< k]) A)"
  {
    fix k n and A :: "'a mat"
    assume k_n: "k + n \<le> dim\<^sub>r A"
    hence "swbl A k n = mat (dim\<^sub>r A) (dim\<^sub>c A) (\<lambda> (i,j). let r = 
      (if i < n then i + k else if i < k + n then i - n else i)
      in A $$ (r,j))"
    proof (induct k arbitrary: A)
      case 0
      thus ?case unfolding swbl_def by (intro mat_eqI, auto simp: swb)
    next
      case (Suc k)
      hence dim: "k + n < dim\<^sub>r A" by auto
      have id: "swbl A (Suc k) n = swbl (swb A k n) k n" unfolding swbl_def by simp
      show ?case unfolding id swb[OF dim]
        by (subst Suc(1), insert dim, force, intro mat_eqI, auto simp: less_Suc_eq_le) 
    qed
  } note swbl = this
  {
    fix k n and A :: "'a mat"
    assume k_n: "k + n \<le> dim\<^sub>c A" "dim\<^sub>r A = dim\<^sub>c A" 
    hence "det (swbl A k n) = (-1)^(k*n) * det A" 
    proof (induct k arbitrary: A)
      case 0
      thus ?case unfolding swbl_def by auto
    next
      case (Suc k)
      hence dim: "k + n < dim\<^sub>r A" by auto
      have id: "swbl A (Suc k) n = swbl (swb A k n) k n" unfolding swbl_def by simp
      have det: "det (swb A k n) = (-1)^n * det A" unfolding swb_def
        by (subst sw, insert Suc(2-), auto)
      show ?case unfolding id 
        by (subst Suc(1), insert Suc(2-), auto simp: det, auto simp: swb power_add)
    qed
  } note det_swbl = this
  from assms have le: "n + k \<le> dim\<^sub>r A" by auto
  have B: "?B = swbl A n k" by (subst swbl[OF le], rule mat_eqI, insert assms, auto)
  have det: "det ?B = (- 1) ^ (n * k) * det A" unfolding B
    by (rule det_swbl, insert assms, auto)
  show ?thesis unfolding det by (simp add: ac_simps)
qed
  
lemma det_swap_cols: assumes A: "A \<in> carrier\<^sub>m (k + n) (k + n)" 
  shows "det A = (-1)^(k * n) * det (mat (k + n) (k + n) (\<lambda> (i,j). let c = 
      (if j < k then j + n else j - k)
      in A $$ (i,c)))" (is "_ = _ * det ?B")
proof -
  let ?A = "transpose\<^sub>m A" 
  let ?C = "mat (k + n) (k + n) (\<lambda> (i,j). let r = 
      (if i < k then i + n else i - k)
      in ?A $$ (r,j))" 
  have "det A = (det ?A)" using det_transpose[OF A] by simp
  also have "\<dots> = (-1)^(k * n) * det ?C"
    by (rule det_swap_rows, insert A, auto)
  also have "det ?C = det (transpose\<^sub>m ?C)" by (subst det_transpose, auto)
  also have "transpose\<^sub>m ?C = ?B" 
    by (rule mat_eqI, insert assms, auto)
  finally show ?thesis .
qed  
  
lemma det_four_block_mat_upper_right_zero: fixes A1 :: "'a :: idom mat" 
  assumes A1: "A1 \<in> carrier\<^sub>m n n"
  and A20: "A2 = (\<zero>\<^sub>m n m)" and A3: "A3 \<in> carrier\<^sub>m m n"
  and A4: "A4 \<in> carrier\<^sub>m m m"  
shows "det (four_block_mat A1 A2 A3 A4) = det A1 * det A4" 
  using assms(2-)
proof (induct m arbitrary: A2 A3 A4)  
  case (0 A2 A3 A4)
  hence *: "four_block_mat A1 A2 A3 A4 = A1" using A1
    by (intro mat_eqI, auto)
  from 0 have 4: "A4 = \<one>\<^sub>m 0" by auto
  show ?case unfolding * unfolding 4 by simp
next
  case (Suc m A2 A3 A4)    
  let ?m = "Suc m" 
  from Suc have A2: "A2 \<in> carrier\<^sub>m n ?m" by auto
  note A20 = Suc(2)
  note A34 = Suc(3-4)
  let ?A = "four_block_mat A1 A2 A3 A4" 
  let ?P = "\<lambda> B3 B4 v k. v \<noteq> 0 \<and> v * det ?A = det (four_block_mat A1 A2 B3 B4)
    \<and> v * det A4 = det B4 \<and> B3 \<in> carrier\<^sub>m ?m n \<and> B4 \<in> carrier\<^sub>m ?m ?m \<and> (\<forall> i < k. B4 $$ (i,m) = 0)" 
  have "k \<le> m \<Longrightarrow> \<exists> B3 B4 v. ?P B3 B4 v k" for k
  proof (induct k)
    case 0
    have "?P A3 A4 1 0" using A34 by auto
    thus ?case by blast
  next
    case (Suc k)
    then obtain B3 B4 v where v: "v \<noteq> 0" and det: "v * det ?A = 
      det (four_block_mat A1 A2 B3 B4)" "v * det A4 = det B4" 
     and B3: "B3 \<in> carrier\<^sub>m ?m n" and B4: "B4 \<in> carrier\<^sub>m ?m ?m"  and 0: "\<forall> i < k. B4 $$ (i,m) = 0" by auto
    show ?case
    proof (cases "B4 $$ (k,m) = 0")
      case True
      with 0 have 0: "\<forall> i < Suc k. B4 $$ (i,m) = 0" using less_Suc_eq by auto
      with v det B3 B4 have "?P B3 B4 v (Suc k)" by auto
      thus ?thesis by blast
    next
      case Bk: False
      let ?k = "Suc k" 
      from Suc(2) have k: "k < ?m" "Suc k < ?m" "k \<noteq> Suc k" by auto      
      show ?thesis
      proof (cases "B4 $$ (?k,m) = 0")
        case True
        let ?B4 = "swaprows k (Suc k) B4" 
        let ?B3 = "swaprows k (Suc k) B3" 
        let ?B = "four_block_mat A1 A2 ?B3 ?B4" 
        let ?v = "-v" 
        from det_swaprows[OF k B4] det have det1: "?v * det A4 = det ?B4" by simp
        from v have v: "?v \<noteq> 0" by auto
        from B3 have B3': "?B3 \<in> carrier\<^sub>m ?m n" by auto
        from B4 have B4': "?B4 \<in> carrier\<^sub>m ?m ?m" by auto
        have "?v * det ?A = - det (four_block_mat A1 A2 B3 B4)" using det by simp            
        also have "\<dots> = det (swaprows (n + k) (n + ?k) (four_block_mat A1 A2 B3 B4))" 
          by (rule sym, rule det_swaprows[of _ "n + ?m"], insert A1 A2 B3 B4 k, auto)
        also have "swaprows (n + k) (n + ?k) (four_block_mat A1 A2 B3 B4) = ?B" 
        proof (rule mat_eqI, unfold four_block_mat_index mat_index_swaprows, goal_cases)
          case (1 i j)
          show ?case
          proof (cases "i < n")
            case True
            thus ?thesis using 1(2) A1 A2 B3 B4 by simp
          next
            case False
            hence "i = n + (i - n)" by simp
            then obtain d where "i = n + d" by blast 
            thus ?thesis using 1 A1 A2 B3 B4 k(2) by simp
          qed
        qed auto
        finally have det2: "?v * det ?A = det ?B" .
        from True 0 B4 k(2) have "\<forall> i < Suc k. ?B4 $$ (i,m) = 0" unfolding less_Suc_eq by auto
        with det1 det2 B3' B4' v have "?P ?B3 ?B4 ?v (Suc k)" by auto
        thus ?thesis by blast
      next
        case False
        let ?bk = "B4 $$ (?k,m)" 
        let ?b = "B4 $$ (k,m)" 
        let ?v = "v * ?bk" 
        let ?B3 = "addrow (- ?b) k ?k (multrow k ?bk B3)" 
        let ?B4 = "addrow (- ?b) k ?k (multrow k ?bk B4)" 
        have *: "det ?B4 = ?bk * det B4" 
          by (subst det_addrow[OF k(2-3)], force simp: B4, rule det_multrow[OF k(1) B4])
        with det(2)[symmetric] have det2: "?v * det A4 = det ?B4" by (auto simp: ac_simps)
        from 0 k(2) B4 have 0: "\<forall> i < Suc k. ?B4 $$ (i,m) = 0" unfolding less_Suc_eq by auto
        from False v have v: "?v \<noteq> 0" by auto
        from B3 have B3': "?B3 \<in> carrier\<^sub>m ?m n" by auto
        from B4 have B4': "?B4 \<in> carrier\<^sub>m ?m ?m" by auto
        let ?B' = "multrow (n + k) ?bk (four_block_mat A1 A2 B3 B4)" 
        have B': "?B' \<in> carrier\<^sub>m (n + ?m) (n + ?m)" using A1 A2 B3 B4 k by auto          
        let ?B = "four_block_mat A1 A2 ?B3 ?B4" 
        have "?v * det ?A = ?bk * det (four_block_mat A1 A2 B3 B4)" using det by simp            
        also have "\<dots> = det (addrow (- ?b) (n + k) (n + ?k) ?B')" 
          by (subst det_addrow[OF _ _ B'], insert k(2), force, force, rule sym, rule det_multrow[of _ "n + ?m"],
          insert A1 A2 B3 B4 k, auto)
        also have "addrow (- ?b) (n + k) (n + ?k) ?B' = ?B" 
        proof (rule mat_eqI, unfold four_block_mat_index mat_index_multrow mat_index_addrow, goal_cases)
          case (1 i j)
          show ?case
          proof (cases "i < n")
            case True
            thus ?thesis using 1(2) A1 A2 B3 B4 by simp
          next
            case False
            hence "i = n + (i - n)" by simp
            then obtain d where "i = n + d" by blast 
            thus ?thesis using 1 A1 A2 B3 B4 k(2) by simp
          qed
        qed auto
        finally have det1: "?v * det ?A = det ?B" .
        from det1 det2 B3' B4' v 0 have "?P ?B3 ?B4 ?v (Suc k)" by auto
        thus ?thesis by blast
      qed
    qed
  qed
  from this[OF le_refl] obtain B3 B4 v where P: "?P B3 B4 v m" by blast
  let ?B = "four_block_mat A1 A2 B3 B4" 
  from P have v: "v \<noteq> 0" and det: "v * det ?A = det ?B" "v * det A4 = det B4" 
    and B3: "B3 \<in> carrier\<^sub>m ?m n" and B4: "B4 \<in> carrier\<^sub>m ?m ?m" and 0: "\<And> i. i < m \<Longrightarrow> B4 $$ (i, m) = 0" 
    by auto
  let ?A2 = "\<zero>\<^sub>m n m"  
  let ?A3 = "mat m n (\<lambda> ij. B3 $$ ij)" 
  let ?A4 = "mat m m (\<lambda> ij. B4 $$ ij)" 
  let ?B1 = "four_block_mat A1 ?A2 ?A3 ?A4" 
  let ?B2 = "\<zero>\<^sub>m (n + m) 1" 
  let ?B3 = "mat 1 (n + m) (\<lambda> (i,j). if j < n then B3 $$ (m,j) else B4 $$ (m,j - n))" 
  let ?B4 = "mat 1 1 (\<lambda> _. B4 $$ (m,m))" 
  have B44: "B4 = four_block_mat ?A4 (\<zero>\<^sub>m m 1) (mat 1 m (\<lambda> (i,j). B4 $$ (m,j))) ?B4" 
  proof (rule mat_eqI, unfold four_block_mat_index mat_dim_col_mat mat_dim_row_mat, goal_cases)
    case (1 i j)
    hence [simp]: "\<not> i < m \<Longrightarrow> i = m" "\<not> j < m \<Longrightarrow> j = m" by auto
    from 1 show ?case using B4 0 by auto
  qed (insert B4, auto)
  have "?B = four_block_mat ?B1 ?B2 ?B3 ?B4"
  proof (rule mat_eqI, unfold four_block_mat_index mat_dim_col_mat mat_dim_row_mat, goal_cases)
    case (1 i j)
    then consider (UL) "i < n + m" "j < n + m" | (UR) "i < n + m" "j = n + m" 
        | (LL) "i = n + m" "j < n + m" | (LR) "i = n + m" "j = n + m" using A1 by auto linarith
    thus ?case
    proof cases
      case UL
      hence [simp]: "\<not> i < n \<Longrightarrow> i - n < m" 
         "\<not> j < n \<Longrightarrow> j - n < m" "\<not> j < n \<Longrightarrow> j - n < Suc m" by auto
      from UL show ?thesis using A1 A20 B3 B4 by simp
    next
      case LL
      hence [simp]: "\<not> j < n \<Longrightarrow> j - n < m" "\<not> j < n \<Longrightarrow> j - n < Suc m" by auto
      from LL show ?thesis using A1 A2 B3 B4 by simp
    next
      case LR
      thus ?thesis using A1 A2 B3 B4 by simp
    next
      case UR
      hence [simp]: "\<not> i < n \<Longrightarrow> i - n < m" by auto
      from UR show ?thesis using A1 A20 0 B3 B4 by simp
    qed
  qed (insert B4, auto)
  hence "det ?B = det (four_block_mat ?B1 ?B2 ?B3 ?B4)" by simp
  also have "\<dots> = det ?B1 * det ?B4" 
    by (rule det_four_block_mat_upper_right_zero_col[of _ "n + m"], insert A1 A2 B3 B4, auto)
  also have "det ?B1 = det A1 * det (mat m m (op $$ B4))"  
    by (rule Suc(1), insert B3 B4, auto)
  also have "\<dots> * det ?B4 = det A1 * (det (mat m m (op $$ B4)) * det ?B4)" by simp
  also have "det (mat m m (op $$ B4)) * det ?B4 = det B4"
    unfolding arg_cong[OF B44, of det] 
    by (subst det_four_block_mat_upper_right_zero_col[OF _ refl], auto)
  finally have id: "det ?B = det A1 * det B4" .
  from this[folded det] have "v * det ?A = v * (det A1 * det A4)" by simp
  with v show "det ?A = det A1 * det A4" by simp
qed

end  
