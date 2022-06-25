section \<open>Weak and Strong Duality of Linear Programming\<close>

theory LP_Duality
  imports 
    Linear_Inequalities.Farkas_Lemma 
    Minimum_Maximum
begin

lemma weak_duality_theorem: 
  fixes A :: "'a :: linordered_comm_semiring_strict mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and x: "x \<in> carrier_vec nc" 
    and Axb: "A *\<^sub>v x \<le> b"   
    and y0: "y \<ge> 0\<^sub>v nr" 
    and yA: "A\<^sup>T *\<^sub>v y = c"
  shows "c \<bullet> x \<le> b \<bullet> y" 
proof -
  from y0 have y: "y \<in> carrier_vec nr" unfolding less_eq_vec_def by auto
  have "c \<bullet> x = (A\<^sup>T *\<^sub>v y) \<bullet> x" unfolding yA by simp
  also have "\<dots> = y \<bullet> (A *\<^sub>v x)" using x y A by (metis transpose_vec_mult_scalar)
  also have "\<dots> \<le> y \<bullet> b" 
    unfolding scalar_prod_def using A b Axb y0
    by (auto intro!: sum_mono mult_left_mono simp: less_eq_vec_def)
  also have "\<dots> = b \<bullet> y" using y b by (metis comm_scalar_prod)
  finally show ?thesis . 
qed

corollary unbounded_primal_solutions:
  fixes A :: "'a :: linordered_idom mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and unbounded: "\<forall> v. \<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b \<and> c \<bullet> x \<ge> v" 
  shows "\<not> (\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c)" 
proof 
  assume "(\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c)" 
  then obtain y where y: "y \<ge> 0\<^sub>v nr" and Ayc: "A\<^sup>T *\<^sub>v y = c" 
    by auto
  from unbounded[rule_format, of "b \<bullet> y + 1"]
  obtain x where x: "x \<in> carrier_vec nc" and Axb: "A *\<^sub>v x \<le> b" 
    and le: "b \<bullet> y + 1 \<le> c \<bullet> x" by auto
  from weak_duality_theorem[OF A b c x Axb y Ayc]
  have "c \<bullet> x \<le> b \<bullet> y" by auto
  with le show False by  auto
qed

corollary unbounded_dual_solutions:
  fixes A :: "'a :: linordered_idom mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and unbounded: "\<forall> v. \<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c \<and> b \<bullet> y \<le> v"
  shows "\<not> (\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b)" 
proof
  assume "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
  then obtain x where x: "x \<in> carrier_vec nc" and Axb: "A *\<^sub>v x \<le> b" by auto
  from unbounded[rule_format, of "c \<bullet> x - 1"]
  obtain y where y: "y\<ge>0\<^sub>v nr" and Ayc: "A\<^sup>T *\<^sub>v y = c" and le: "b \<bullet> y \<le> c \<bullet> x - 1" by auto
  from weak_duality_theorem[OF A b c x Axb y Ayc]
  have "c \<bullet> x \<le> b \<bullet> y" by auto
  with le show False by auto
qed

text \<open>A version of the strong duality theorem which demands
  that both primal and dual problem are solvable. At this point
  we do not use min- or max-operations\<close>
theorem strong_duality_theorem_both_sat:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and primal: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
    and dual: "\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c"
  shows "\<exists> x y. 
       x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b \<and> 
       y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c \<and>
       c \<bullet> x = b \<bullet> y" 
proof -
  define M_up where "M_up = four_block_mat A (0\<^sub>m nr nr) (mat_of_row (- c)) (mat_of_row b)" 
  define M_low where "M_low = four_block_mat (0\<^sub>m nc nc) (A\<^sup>T) (0\<^sub>m nc nc) (- (A\<^sup>T))" 
  define M_last where "M_last = append_cols (0\<^sub>m nr nc) (- 1\<^sub>m nr :: 'a mat)" 
  define M where "M = (M_up  @\<^sub>r M_low) @\<^sub>r M_last"
  define bc where "bc = ((b @\<^sub>v 0\<^sub>v 1) @\<^sub>v (c @\<^sub>v -c)) @\<^sub>v (0\<^sub>v nr)" 
    (* M = ( A   0) bc = (  b)
           (-c   b)      (  0)
           ( 0  At)      (  c)
           ( 0 -At)      ( -c)
           ( 0  -I)      (  0) *)
  let ?nr = "((nr + 1) + (nc + nc)) + nr" 
  let ?nc = "nc + nr" 
  have M_up: "M_up \<in> carrier_mat (nr + 1) ?nc" 
    unfolding M_up_def using A b c by auto
  have M_low: "M_low \<in> carrier_mat (nc + nc) ?nc" 
    unfolding M_low_def using A by auto
  have M_last: "M_last \<in> carrier_mat nr ?nc" 
    unfolding M_last_def by auto
  have M: "M \<in> carrier_mat ?nr ?nc" 
    using carrier_append_rows[OF carrier_append_rows[OF M_up M_low] M_last]
    unfolding M_def by auto
  have bc: "bc \<in> carrier_vec ?nr" unfolding bc_def
    by (intro append_carrier_vec, insert b c, auto)
  have "(\<exists>xy. xy \<in> carrier_vec ?nc \<and> M *\<^sub>v xy \<le> bc)" 
  proof (subst gram_schmidt.Farkas_Lemma'[OF M bc], intro allI impI, elim conjE)
    fix ulv
    assume ulv0: "0\<^sub>v ?nr \<le> ulv" and Mulv: "M\<^sup>T *\<^sub>v ulv = 0\<^sub>v ?nc" 
    from ulv0[unfolded less_eq_vec_def]
    have ulv: "ulv \<in> carrier_vec ?nr" by auto
    define u1 where "u1 = vec_first ulv ((nr + 1) + (nc + nc))" 
    define u2 where "u2 = vec_first u1 (nr + 1)" 
    define u3 where "u3 = vec_last u1 (nc + nc)" 
    define t where "t = vec_last ulv nr" 
    have ulvid: "ulv = u1 @\<^sub>v t" using ulv
      unfolding u1_def t_def by auto
    have t: "t \<in> carrier_vec nr" unfolding t_def by auto
    have u1: "u1 \<in> carrier_vec ((nr + 1) + (nc + nc))" 
      unfolding u1_def by auto
    have u1id: "u1 = u2 @\<^sub>v u3" using u1
      unfolding u2_def u3_def by auto
    have u2: "u2 \<in> carrier_vec (nr + 1)" unfolding u2_def by auto
    have u3: "u3 \<in> carrier_vec (nc + nc)" unfolding u3_def by auto  
    define v where "v = vec_first u3 nc" 
    define w where "w = vec_last u3 nc" 
    have u3id: "u3 = v @\<^sub>v w" using u3
      unfolding v_def w_def by auto
    have v: "v \<in> carrier_vec nc" unfolding v_def by auto
    have w: "w \<in> carrier_vec nc" unfolding w_def by auto  

    define u where "u = vec_first u2 nr" 
    define L where "L = vec_last u2 1" 
    have u2id: "u2 = u @\<^sub>v L" using u2
      unfolding u_def L_def by auto
    have u: "u \<in> carrier_vec nr" unfolding u_def by auto
    have L: "L \<in> carrier_vec 1" unfolding L_def by auto  
    define vec1 where "vec1 = A\<^sup>T *\<^sub>v u + mat_of_col (- c) *\<^sub>v L" 
    have vec1: "vec1 \<in> carrier_vec nc" 
      unfolding vec1_def mat_of_col_def using A u c L
      by (meson add_carrier_vec mat_of_row_carrier(1) mult_mat_vec_carrier transpose_carrier_mat uminus_carrier_vec)
    define vec2 where "vec2 = A *\<^sub>v (v - w)" 
    have vec2: "vec2 \<in> carrier_vec nr"
      unfolding vec2_def using A v w by auto  
    define vec3 where "vec3 = mat_of_col b *\<^sub>v L"
    have vec3: "vec3 \<in> carrier_vec nr" 
      using A b L unfolding mat_of_col_def vec3_def
      by (meson add_carrier_vec mat_of_row_carrier(1) mult_mat_vec_carrier transpose_carrier_mat uminus_carrier_vec)
    have Mt: "M\<^sup>T = (M_up\<^sup>T @\<^sub>c M_low\<^sup>T) @\<^sub>c M_last\<^sup>T" 
      unfolding M_def append_cols_def by simp
    have "M\<^sup>T *\<^sub>v ulv = (M_up\<^sup>T @\<^sub>c M_low\<^sup>T) *\<^sub>v u1 + M_last\<^sup>T *\<^sub>v t" 
      unfolding Mt ulvid
      by (subst mat_mult_append_cols[OF carrier_append_cols _ u1 t],
          insert M_up M_low M_last, auto)
    also have "M_last\<^sup>T = 0\<^sub>m nc nr @\<^sub>r - 1\<^sub>m nr" unfolding M_last_def
      unfolding append_cols_def by (simp, subst transpose_uminus, auto)
    also have "\<dots> *\<^sub>v t = 0\<^sub>v nc @\<^sub>v - t" 
      by (subst mat_mult_append[OF _ _ t], insert t, auto)
    also have "(M_up\<^sup>T @\<^sub>c M_low\<^sup>T) *\<^sub>v u1 = (M_up\<^sup>T *\<^sub>v u2) + (M_low\<^sup>T *\<^sub>v u3)" 
      unfolding u1id
      by (rule mat_mult_append_cols[OF _ _ u2 u3], insert M_up M_low, auto)
    also have "M_low\<^sup>T = four_block_mat (0\<^sub>m nc nc) (0\<^sub>m nc nc) A (- A)" 
      unfolding M_low_def
      by (subst transpose_four_block_mat, insert A, auto)
    also have "\<dots> *\<^sub>v u3 = (0\<^sub>m nc nc *\<^sub>v v + 0\<^sub>m nc nc *\<^sub>v w) @\<^sub>v (A *\<^sub>v v + - A *\<^sub>v w)" unfolding u3id
      by (subst four_block_mat_mult_vec[OF _ _ A _ v w], insert A, auto)
    also have "0\<^sub>m nc nc *\<^sub>v v + 0\<^sub>m nc nc *\<^sub>v w = 0\<^sub>v nc" 
      using v w by auto
    also have "A *\<^sub>v v + - A *\<^sub>v w = vec2" unfolding vec2_def using A v w
      by (metis (full_types) carrier_matD(2) carrier_vecD minus_add_uminus_vec mult_mat_vec_carrier mult_minus_distrib_mat_vec uminus_mult_mat_vec)
    also have "M_up\<^sup>T  = four_block_mat A\<^sup>T (mat_of_col (- c)) (0\<^sub>m nr nr) (mat_of_col b)" 
      unfolding M_up_def mat_of_col_def
      by (subst transpose_four_block_mat[OF A], insert b c, auto)
    also have "\<dots> *\<^sub>v u2 = vec1 @\<^sub>v vec3" 
      unfolding u2id vec1_def vec3_def
      by (subst four_block_mat_mult_vec[OF _ _ _ _ u L], insert A b c u, auto)
    also have "(vec1 @\<^sub>v vec3)
      + (0\<^sub>v nc @\<^sub>v vec2) + (0\<^sub>v nc @\<^sub>v - t) = 
      (vec1 @\<^sub>v (vec3 + vec2 - t))" 
      apply (subst append_vec_add[of _ nc _ _ nr, OF vec1 _ vec3 vec2])
      subgoal by force
      apply (subst append_vec_add[of _ nc _ _ nr])
      subgoal using vec1 by auto
      subgoal by auto
      subgoal using vec2 vec3 by auto
      subgoal using t by auto
      subgoal using vec1 by auto
      done
    finally have "vec1 @\<^sub>v (vec3 + vec2 - t) = 0\<^sub>v ?nc"
      unfolding Mulv by simp
    also have "\<dots> = 0\<^sub>v nc @\<^sub>v 0\<^sub>v nr" by auto
    finally have "vec1 = 0\<^sub>v nc \<and> vec3 + vec2 - t = 0\<^sub>v nr" 
      by (subst (asm) append_vec_eq[OF vec1], auto)
    hence 01: "vec1 = 0\<^sub>v nc" and 02: "vec3 + vec2 - t = 0\<^sub>v nr" by auto
    from 01 have "vec1 + mat_of_col c *\<^sub>v L = mat_of_col c *\<^sub>v L"
      using c L vec1 unfolding mat_of_col_def  by auto
    also have "vec1 + mat_of_col c *\<^sub>v L = A\<^sup>T *\<^sub>v u" 
      unfolding vec1_def
      using A u c L unfolding mat_of_col_def mat_of_row_uminus transpose_uminus
      by (subst uminus_mult_mat_vec, auto)
    finally have As: "A\<^sup>T *\<^sub>v u = mat_of_col c *\<^sub>v L" .
    from 02 have "(vec3 + vec2 - t) + t = 0\<^sub>v nr + t"
      by simp 
    also have "(vec3 + vec2 - t) + t = vec2 + vec3" 
      using vec3 vec2 t by auto
    finally have t23: "t = vec2 + vec3" using t by auto
    have id0: "0\<^sub>v ?nr = ((0\<^sub>v nr @\<^sub>v 0\<^sub>v 1) @\<^sub>v (0\<^sub>v nc @\<^sub>v 0\<^sub>v nc)) @\<^sub>v 0\<^sub>v nr" 
      by auto
    from ulv0[unfolded id0 ulvid u1id u2id u3id]
    have "0\<^sub>v nr \<le> u \<and> 0\<^sub>v 1 \<le> L \<and> 0\<^sub>v nc \<le> v \<and> 0\<^sub>v nc \<le> w \<and> 0\<^sub>v nr \<le> t" 
      apply (subst (asm) append_vec_le[of _ "(nr + 1) + (nc + nc)"])
      subgoal by (intro append_carrier_vec, auto)
      subgoal by (intro append_carrier_vec u L v w)
      apply (subst (asm) append_vec_le[of _ "(nr + 1)"])
      subgoal by (intro append_carrier_vec, auto)
      subgoal by (intro append_carrier_vec u L v w)
      apply (subst (asm) append_vec_le[OF _ u], force)
      apply (subst (asm) append_vec_le[OF _ v], force)
      by auto
    hence ineqs: "0\<^sub>v nr \<le> u" "0\<^sub>v 1 \<le> L" "0\<^sub>v nc \<le> v" "0\<^sub>v nc \<le> w" "0\<^sub>v nr \<le> t"
      by auto
    have "ulv \<bullet> bc = u \<bullet> b + (v \<bullet> c + w \<bullet> (-c))" 
      unfolding ulvid u1id u2id u3id bc_def
      apply (subst scalar_prod_append[OF _ t])
         apply (rule append_carrier_vec[OF append_carrier_vec[OF u L] append_carrier_vec[OF v w]])
        apply (rule append_carrier_vec[OF append_carrier_vec[OF b] append_carrier_vec]; use c in force)
       apply force
      apply (subst scalar_prod_append)
          apply (rule append_carrier_vec[OF u L])
         apply (rule append_carrier_vec[OF v w])
      subgoal by (rule append_carrier_vec, insert b, auto)
      subgoal by (rule append_carrier_vec, insert c, auto)
      apply (subst scalar_prod_append[OF u L b], force)
      apply (subst scalar_prod_append[OF v w c], use c in force)
      apply (insert L t, auto)
      done
    also have "v \<bullet> c + w \<bullet> (-c) = c \<bullet> v + (-c) \<bullet> w" 
      by (subst (1 2) comm_scalar_prod, insert w c v, auto)
    also have "\<dots> = c \<bullet> v - (c \<bullet> w)" using c w by simp
    also have "\<dots> = c \<bullet> (v - w)" using c v w
      by (simp add: scalar_prod_minus_distrib)
    finally have ulvbc: "ulv \<bullet> bc = u \<bullet> b + c \<bullet> (v - w)" .
    define lam where "lam = L $ 0" 
    from ineqs(2) L have lam0: "lam \<ge> 0" unfolding less_eq_vec_def lam_def by auto
    have As: "A\<^sup>T *\<^sub>v u = lam \<cdot>\<^sub>v c" unfolding As using c L
      unfolding lam_def mat_of_col_def
      by (intro eq_vecI, auto simp: scalar_prod_def)
    have vec3: "vec3 = lam \<cdot>\<^sub>v b" unfolding vec3_def using b L
      unfolding lam_def mat_of_col_def
      by (intro eq_vecI, auto simp: scalar_prod_def)
    note preconds = lam0 ineqs(1,3-)[unfolded t23[unfolded vec2_def vec3]] As
    have "0 \<le> u \<bullet> b + c \<bullet> (v - w)"
    proof (cases "lam > 0")
      case True
      hence "u \<bullet> b = inverse lam * (lam * (b \<bullet> u))" 
        using comm_scalar_prod[OF b u] by simp
      also have "\<dots> = inverse lam * ((lam \<cdot>\<^sub>v b) \<bullet> u)"
        using b u by simp
      also have "\<dots> \<ge> inverse lam * (-(A *\<^sub>v (v - w)) \<bullet> u)" 
      proof (intro mult_left_mono)
        show "0 \<le> inverse lam" using preconds by auto
        show "-(A *\<^sub>v (v - w)) \<bullet> u \<le> (lam \<cdot>\<^sub>v b) \<bullet> u" 
          unfolding scalar_prod_def
          apply (rule sum_mono)
          subgoal for i
            using lesseq_vecD[OF _ preconds(2), of nr i] lesseq_vecD[OF _ preconds(5), of nr i] u v w b A
            by (intro mult_right_mono, auto)
          done
      qed
      also have "inverse lam * (-(A *\<^sub>v (v - w)) \<bullet> u) =
         - (inverse lam * ((A *\<^sub>v (v - w)) \<bullet> u))" 
        by (subst scalar_prod_uminus_left, insert A u v w, auto)
      also have "(A *\<^sub>v (v - w)) \<bullet> u = (A\<^sup>T *\<^sub>v u) \<bullet> (v - w)" 
        apply (subst transpose_vec_mult_scalar[OF A _ u])
        subgoal using v w by force
        by (rule comm_scalar_prod[OF _ u], insert A v w, auto)
      also have "inverse lam * \<dots> = c \<bullet> (v - w)" unfolding preconds(6)
        using True
        by (subst scalar_prod_smult_left, insert c v w, auto)
      finally show ?thesis by simp
    next
      case False
      with preconds have lam: "lam = 0" by auto
      from primal obtain x0 where x0: "x0 \<in> carrier_vec nc"
        and Ax0b: "A *\<^sub>v x0 \<le> b" by auto
      from dual obtain y0 where y00: "y0 \<ge> 0\<^sub>v nr" 
        and Ay0c: "A\<^sup>T *\<^sub>v y0 = c" by auto
      from y00 have y0: "y0 \<in> carrier_vec nr" 
        unfolding less_eq_vec_def by auto
      have Au: "A\<^sup>T *\<^sub>v u = 0\<^sub>v nc" 
        unfolding preconds lam using c by auto
      have "0 = (A\<^sup>T *\<^sub>v u) \<bullet> x0" unfolding Au using x0 by auto
      also have "\<dots> = u \<bullet> (A *\<^sub>v x0)"
        by (rule transpose_vec_mult_scalar[OF A x0 u])
      also have "\<dots> \<le> u \<bullet> b" 
        unfolding scalar_prod_def 
        apply (use A x0 b in simp) 
        apply (intro sum_mono)
        subgoal for i
          using lesseq_vecD[OF _ preconds(2), of nr i] lesseq_vecD[OF _ Ax0b, of nr i] u v w b A x0
          by (intro mult_left_mono, auto)
        done
      finally have ub: "0 \<le> u \<bullet> b" .
      have "c \<bullet> (v - w) = (A\<^sup>T *\<^sub>v y0) \<bullet> (v - w)" unfolding Ay0c by simp
      also have "\<dots> = y0 \<bullet> (A *\<^sub>v (v - w))" 
        by (subst transpose_vec_mult_scalar[OF A _ y0], insert v w, auto)
      also have "\<dots> \<ge> 0"
        unfolding scalar_prod_def
        apply (use A v w in simp)
        apply (intro sum_nonneg)
        subgoal for i
          using lesseq_vecD[OF _ y00, of nr i] lesseq_vecD[OF _ preconds(5)[unfolded lam], of nr i] A y0 v w b
          by (intro mult_nonneg_nonneg, auto)
        done
      finally show ?thesis using ub by auto
    qed
    thus "0 \<le> ulv \<bullet> bc" unfolding ulvbc .
  qed
  then obtain xy where xy: "xy \<in> carrier_vec ?nc" and le: "M *\<^sub>v xy \<le> bc" by auto
  define x where "x = vec_first xy nc" 
  define y where "y = vec_last xy nr" 
  have xyid: "xy = x @\<^sub>v y" using xy
    unfolding x_def y_def by auto
  have x: "x \<in> carrier_vec nc" unfolding x_def by auto
  have y: "y \<in> carrier_vec nr" unfolding y_def by auto
  have At: "A\<^sup>T \<in> carrier_mat nc nr" using A by auto
  have Ax1: "A *\<^sub>v x @\<^sub>v vec 1 (\<lambda>_. b \<bullet> y - c \<bullet> x) \<in> carrier_vec (nr + 1)" 
    using A x by fastforce
  have b0cc: "(b @\<^sub>v 0\<^sub>v 1) @\<^sub>v c @\<^sub>v - c \<in> carrier_vec ((nr + 1) + (nc + nc))" 
    using b c 
    by (intro append_carrier_vec, auto)
  have "M *\<^sub>v xy = (M_up *\<^sub>v xy @\<^sub>v M_low *\<^sub>v xy) @\<^sub>v (M_last *\<^sub>v xy)" 
    unfolding M_def
    unfolding mat_mult_append[OF carrier_append_rows[OF M_up M_low] M_last xy]
    by (simp add: mat_mult_append[OF M_up M_low xy])
  also have "M_low *\<^sub>v xy = (0\<^sub>m nc nc *\<^sub>v x + A\<^sup>T *\<^sub>v y) @\<^sub>v (0\<^sub>m nc nc *\<^sub>v x + - A\<^sup>T *\<^sub>v y)" 
    unfolding M_low_def xyid
    by (rule four_block_mat_mult_vec[OF _ At _ _ x y], insert A, auto)
  also have "0\<^sub>m nc nc *\<^sub>v x + A\<^sup>T *\<^sub>v y = A\<^sup>T *\<^sub>v y" using A x y by auto
  also have "0\<^sub>m nc nc *\<^sub>v x + - A\<^sup>T *\<^sub>v y = - A\<^sup>T *\<^sub>v y" using A x y by auto
  also have "M_up *\<^sub>v xy = (A *\<^sub>v x + 0\<^sub>m nr nr *\<^sub>v y) @\<^sub>v
               (mat_of_row (- c) *\<^sub>v x + mat_of_row b *\<^sub>v y)" 
    unfolding M_up_def xyid
    by (rule four_block_mat_mult_vec[OF A _ _ _ x y], insert b c, auto)
  also have "A *\<^sub>v x + 0\<^sub>m nr nr *\<^sub>v y = A *\<^sub>v x" using A x y by auto
  also have "mat_of_row (- c) *\<^sub>v x + mat_of_row b *\<^sub>v y = 
    vec 1 (\<lambda> _. b \<bullet> y - c \<bullet> x)" 
    unfolding mult_mat_vec_def using c x by (intro eq_vecI, auto)
  also have "M_last *\<^sub>v xy = - y" 
    unfolding M_last_def xyid using x y
    by (subst mat_mult_append_cols[OF _ _ x y], auto)
  finally have "((A *\<^sub>v x @\<^sub>v vec 1 (\<lambda>_. b \<bullet> y - c \<bullet> x)) @\<^sub>v (A\<^sup>T *\<^sub>v y @\<^sub>v - A\<^sup>T *\<^sub>v y)) @\<^sub>v -y
    = M *\<^sub>v xy" ..
  also have "\<dots> \<le> bc" by fact
  also have "\<dots> = ((b @\<^sub>v 0\<^sub>v 1) @\<^sub>v (c @\<^sub>v -c)) @\<^sub>v 0\<^sub>v nr" unfolding bc_def by auto
  finally have ineqs: "A *\<^sub>v x \<le> b \<and> vec 1 (\<lambda>_. b \<bullet> y - c \<bullet> x) \<le> 0\<^sub>v 1
             \<and> A\<^sup>T *\<^sub>v y \<le> c \<and> - A\<^sup>T *\<^sub>v y \<le> -c \<and> -y \<le> 0\<^sub>v nr"
    apply (subst (asm) append_vec_le[OF _ b0cc])
    subgoal using A x y by (intro append_carrier_vec, auto)
    apply (subst (asm) append_vec_le[OF Ax1], use b in fastforce)
    apply (subst (asm) append_vec_le[OF _ b], use A x in force)
    apply (subst (asm) append_vec_le[OF _ c], use A y in force)
    by auto
  show ?thesis
  proof (intro exI conjI)
    from ineqs show Axb: "A *\<^sub>v x \<le> b" by auto
    from ineqs have "- A\<^sup>T *\<^sub>v y \<le> -c" "A\<^sup>T *\<^sub>v y \<le> c" by auto
    hence "A\<^sup>T *\<^sub>v y \<ge> c" "A\<^sup>T *\<^sub>v y \<le> c" unfolding less_eq_vec_def using A y by auto
    then show Aty: "A\<^sup>T *\<^sub>v y = c" by simp
    from ineqs have "- y \<le> 0\<^sub>v nr" by simp
    then show y0: "0\<^sub>v nr \<le> y" unfolding less_eq_vec_def by auto
    from ineqs have "b \<bullet> y \<le> c \<bullet> x" unfolding less_eq_vec_def by auto
    with weak_duality_theorem[OF A b c x Axb y0 Aty]
    show "c \<bullet> x = b \<bullet> y" by auto
  qed (insert x)
qed

text \<open>A version of the strong duality theorem which demands
  that the primal problem is solvable and the objective function
  is bounded.\<close>
theorem strong_duality_theorem_primal_sat_bounded:
  fixes bound :: "'a :: trivial_conjugatable_linordered_field" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and sat: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
    and bounded: "\<forall> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b \<longrightarrow> c \<bullet> x \<le> bound" 
  shows "\<exists> x y. 
       x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b \<and> 
       y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c \<and>
       c \<bullet> x = b \<bullet> y" 
proof (rule strong_duality_theorem_both_sat[OF A b c sat])
  show "\<exists>y\<ge>0\<^sub>v nr. A\<^sup>T *\<^sub>v y = c" 
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    hence "\<exists>y. y \<in> carrier_vec nc \<and> 0\<^sub>v nr \<le> A *\<^sub>v y \<and> 0 > y \<bullet> c" 
      by (subst (asm) gram_schmidt.Farkas_Lemma[OF _ c], insert A, auto)
    then obtain y where y: "y \<in> carrier_vec nc" 
      and Ay0: "A *\<^sub>v y \<ge> 0\<^sub>v nr" and yc0: "y \<bullet> c < 0" by auto
    from sat obtain x where x: "x \<in> carrier_vec nc" 
      and Axb: "A *\<^sub>v x \<le> b" by auto
    define diff where "diff = bound + 1 - c \<bullet> x" 
    from x Axb bounded have "c \<bullet> x < bound + 1" by auto
    hence diff: "diff > 0" unfolding diff_def by auto
    from yc0 have inv: "inverse (- (y \<bullet> c)) > 0" by auto
    define fact where "fact = diff * (inverse (- (y \<bullet> c)))"
    have fact: "fact > 0" unfolding fact_def using diff inv by (metis mult_pos_pos)
    define z where "z = x - fact \<cdot>\<^sub>v y" 
    have "A *\<^sub>v z = A *\<^sub>v x - A *\<^sub>v (fact \<cdot>\<^sub>v y)" 
      unfolding z_def using A x y by (meson mult_minus_distrib_mat_vec smult_carrier_vec)
    also have "\<dots> = A *\<^sub>v x - fact \<cdot>\<^sub>v (A *\<^sub>v y)" using A y by auto
    also have "\<dots> \<le> b"
    proof (intro lesseq_vecI[OF _ b])
      show "A *\<^sub>v x - fact \<cdot>\<^sub>v (A *\<^sub>v y) \<in> carrier_vec nr" using A x y by auto
      fix i 
      assume i: "i < nr" 
      have "(A *\<^sub>v x - fact \<cdot>\<^sub>v (A *\<^sub>v y)) $ i
        = (A *\<^sub>v x) $ i - fact * (A *\<^sub>v y) $ i" 
        using i A x y by auto
      also have "\<dots> \<le> b $ i - fact * (A *\<^sub>v y) $ i" 
        using lesseq_vecD[OF b Axb i] by auto
      also have "\<dots> \<le> b $ i - 0 * 0" using lesseq_vecD[OF _ Ay0 i] fact A y i
        by (intro diff_left_mono mult_monom, auto)
      finally show "(A *\<^sub>v x - fact \<cdot>\<^sub>v (A *\<^sub>v y)) $ i \<le> b $ i" by simp
    qed
    finally have Azb: "A *\<^sub>v z \<le> b" .
    have z: "z \<in> carrier_vec nc" using x y unfolding z_def by auto
    have "c \<bullet> z = c \<bullet> x - fact * (c \<bullet> y)" unfolding z_def
      using c x y by (simp add: scalar_prod_minus_distrib)
    also have "\<dots> = c \<bullet> x + diff" 
      unfolding comm_scalar_prod[OF c y] fact_def using yc0 by simp
    also have "\<dots> = bound + 1" unfolding diff_def by simp
    also have "\<dots> > c \<bullet> z" using bounded Azb z by auto
    finally show False by simp
  qed
qed

text \<open>A version of the strong duality theorem which demands
  that the dual problem is solvable and the objective function
  is bounded.\<close>
theorem strong_duality_theorem_dual_sat_bounded:
  fixes bound :: "'a :: trivial_conjugatable_linordered_field" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and sat: "\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c"
    and bounded: "\<forall> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c \<longrightarrow> bound \<le> b \<bullet> y" 
  shows "\<exists> x y. 
       x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b \<and> 
       y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c \<and>
       c \<bullet> x = b \<bullet> y" 
proof (rule strong_duality_theorem_both_sat[OF A b c _ sat])
  show "\<exists>x\<in>carrier_vec nc. A *\<^sub>v x \<le> b" 
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence "\<not> (\<exists>x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b)" by auto
    then obtain y where y0: "y \<ge> 0\<^sub>v nr" and Ay0: "A\<^sup>T *\<^sub>v y = 0\<^sub>v nc" and yb: "y \<bullet> b < 0"  
      by (subst (asm) gram_schmidt.Farkas_Lemma'[OF A b], auto)
    from sat obtain x where x0: "x \<ge> 0\<^sub>v nr" and Axc: "A\<^sup>T *\<^sub>v x = c" by auto
    define diff where "diff = b \<bullet> x - (bound - 1)" 
    from x0 Axc bounded have "bound \<le> b \<bullet> x" by auto
    hence diff: "diff > 0" unfolding diff_def by auto
    define fact where "fact = - inverse (y \<bullet> b) * diff" 
    have fact: "fact > 0" unfolding fact_def using diff yb by (auto intro: mult_neg_pos)
    define z where "z = x + fact \<cdot>\<^sub>v y" 
    from x0 have x: "x \<in> carrier_vec nr" 
      unfolding less_eq_vec_def by auto
    from y0 have y: "y \<in> carrier_vec nr" 
      unfolding less_eq_vec_def by auto
    have "A\<^sup>T *\<^sub>v z = A\<^sup>T *\<^sub>v x + A\<^sup>T *\<^sub>v (fact \<cdot>\<^sub>v y)" 
      unfolding z_def using A x y by (simp add: mult_add_distrib_mat_vec)
    also have "\<dots> = A\<^sup>T *\<^sub>v x + fact \<cdot>\<^sub>v (A\<^sup>T *\<^sub>v y)" using A y by auto
    also have "\<dots> = c" unfolding Ay0 Axc using c by auto
    finally have Azc: "A\<^sup>T *\<^sub>v z = c" .
    have z0: "z \<ge> 0\<^sub>v nr" unfolding z_def
      by (intro lesseq_vecI[of _ nr], insert x y lesseq_vecD[OF _ x0, of nr] lesseq_vecD[OF _ y0, of nr] fact, 
          auto intro!: add_nonneg_nonneg)
    from bounded Azc z0 have bz: "bound \<le> b \<bullet> z" by auto
    also have "\<dots> = b \<bullet> x + fact * (b \<bullet> y)" unfolding z_def using b x y
      by (simp add: scalar_prod_add_distrib)
    also have "\<dots> = diff + (bound - 1) + fact * (b \<bullet> y)" 
      unfolding diff_def by auto
    also have "fact * (b \<bullet> y) = - diff" using yb 
      unfolding fact_def comm_scalar_prod[OF y b] by auto
    finally show False by simp
  qed
qed


text \<open>Now the previous three duality theorems are formulated via min/max.\<close>
corollary strong_duality_theorem_min_max:
  fixes A :: "'a :: trivial_conjugatable_linordered_field mat" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and primal: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
    and dual: "\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c"
  shows "Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}
       = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
    and "has_Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
    and "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
proof -
  let ?Prim = "{c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
  let ?Dual = "{b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
  define Prim where "Prim = ?Prim" 
  define Dual where "Dual = ?Dual" 
  from strong_duality_theorem_both_sat[OF assms]
  obtain x y where x: "x \<in> carrier_vec nc" and Axb: "A *\<^sub>v x \<le> b"  
    and y: "y \<ge> 0\<^sub>v nr" and Ayc: "A\<^sup>T *\<^sub>v y = c" 
    and eq: "c \<bullet> x = b \<bullet> y" by auto
  have cxP: "c \<bullet> x \<in> Prim" unfolding Prim_def using x Axb by auto
  have cxD: "c \<bullet> x \<in> Dual" unfolding eq Dual_def using y Ayc by auto
  {
    fix z
    assume "z \<in> Prim"
    from this[unfolded Prim_def] obtain x' where x': "x' \<in> carrier_vec nc" 
      and Axb': "A *\<^sub>v x' \<le> b" and z: "z = c \<bullet> x'" by auto
    from weak_duality_theorem[OF A b c x' Axb' y Ayc, folded eq]
    have "z \<le> c \<bullet> x" unfolding z .
  } note cxMax = this
  have max: "Maximum Prim = c \<bullet> x"     
    by (intro eqMaximumI cxP cxMax)
  show "has_Maximum ?Prim" 
    unfolding Prim_def[symmetric] has_Maximum_def using cxP cxMax by auto
  {
    fix z
    assume "z \<in> Dual"
    from this[unfolded Dual_def] obtain y' where y': "y' \<ge> 0\<^sub>v nr"  
      and Ayc': "A\<^sup>T *\<^sub>v y' = c" and z: "z = b \<bullet> y'" by auto
    from weak_duality_theorem[OF A b c x Axb y' Ayc', folded z]
    have "c \<bullet> x \<le> z" .
  } note cxMin = this
  show "has_Minimum ?Dual" 
    unfolding Dual_def[symmetric] has_Minimum_def using cxD cxMin by auto
  have min: "Minimum Dual = c \<bullet> x" 
    by (intro eqMinimumI cxD cxMin)
  from min max show "Maximum ?Prim = Minimum ?Dual"  
    unfolding Dual_def Prim_def by auto
qed

corollary strong_duality_theorem_primal_sat_bounded_min_max:
  fixes bound :: "'a :: trivial_conjugatable_linordered_field" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and sat: "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" 
    and bounded: "\<forall> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b \<longrightarrow> c \<bullet> x \<le> bound" 
  shows "Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}
       = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}"
    and "has_Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
    and "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
proof -
  let ?Prim = "{c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
  let ?Dual = "{b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
  from strong_duality_theorem_primal_sat_bounded[OF assms]
  have "\<exists>y\<ge>0\<^sub>v nr. A\<^sup>T *\<^sub>v y = c" by blast
  from strong_duality_theorem_min_max[OF A b c sat this]
  show "Maximum ?Prim = Minimum ?Dual" "has_Maximum ?Prim"  "has_Minimum ?Dual"
    by blast+
qed

corollary strong_duality_theorem_dual_sat_bounded_min_max:
  fixes bound :: "'a :: trivial_conjugatable_linordered_field" 
  assumes A: "A \<in> carrier_mat nr nc" 
    and b: "b \<in> carrier_vec nr" 
    and c: "c \<in> carrier_vec nc"
    and sat: "\<exists> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c"
    and bounded: "\<forall> y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c \<longrightarrow> bound \<le> b \<bullet> y" 
  shows "Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}
       = Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}"
    and "has_Maximum {c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
    and "has_Minimum {b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
proof - 
  let ?Prim = "{c \<bullet> x | x. x \<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b}" 
  let ?Dual = "{b \<bullet> y | y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = c}" 
  from strong_duality_theorem_dual_sat_bounded[OF assms]
  have "\<exists> x \<in> carrier_vec nc. A *\<^sub>v x \<le> b" by blast
  from strong_duality_theorem_min_max[OF A b c this sat]
  show "Maximum ?Prim = Minimum ?Dual" "has_Maximum ?Prim"  "has_Minimum ?Dual"
    by blast+
qed

end
