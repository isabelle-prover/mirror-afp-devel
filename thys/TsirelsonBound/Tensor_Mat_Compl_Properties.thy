(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Tensor_Mat_Compl_Properties 
  imports 
    Commuting_Hermitian.Spectral_Theory_Complements
    Projective_Measurements.Projective_Measurements
begin

section \<open>Basic algebraic results\<close>


lemma pos_sum_gt_0:
  assumes "finite I"
and "\<And>i. i \<in> I \<Longrightarrow> (0:: 'a :: linordered_field) \<le> f i"
and "0 < sum f I"
shows "\<exists>j \<in> I. 0 < f j"
proof (rule ccontr)
  assume "\<not> (\<exists>j\<in>I. 0 < f j)"
  hence "\<forall>j \<in> I. f j \<le> 0" by auto
  hence "\<forall>j \<in> I. f j = 0" using assms by fastforce
  hence "sum f I = 0" by simp
  thus False using assms by simp
qed

lemma pos_square_1_elem:
  assumes "finite I"
and "\<And>i. i \<in> I \<Longrightarrow> (0::real) \<le> f i"
and "sum f I = 1"
and "sum (\<lambda>x. f x * f x) I = 1"
shows "\<exists>j \<in> I. f j = 1"
proof (rule ccontr)
  assume "\<not> (\<exists>j\<in>I. f j = 1)"
  hence ne: "\<forall>j\<in> I. f j \<noteq> 1" by simp
  have "\<exists>j \<in> I. 0 < f j" using pos_sum_gt_0[of I f] assms by simp
  from this obtain j where "j\<in>I" and "0 < f j" by auto
  hence "f j \<noteq> 1" using ne by simp
  moreover have "f j \<le> 1" using \<open>j\<in> I\<close> assms pos_sum_le_comp by force
  ultimately have "f j < 1" by auto
  have "sum (\<lambda>x. f x * f x) I = f j * f j + sum (\<lambda>x. f x * f x) (I-{j})"
    by (meson \<open>j \<in> I\<close> assms(1) sum.remove)
  also have "... < f j + sum (\<lambda>x. f x * f x) (I-{j})"
    by (simp add: \<open>0 < f j\<close> \<open>f j < 1\<close>)
  also have "... \<le> f j + sum f (I-{j})" 
    using square_pos_mult_le[of "I -  {j}"]
    by (smt (verit, ccfv_SIG) DiffD1 assms
        mult_left_le sum_mono sum_nonneg_leq_bound)
  also have "... = sum f I"
    by (metis \<open>j \<in> I\<close> assms(1) sum.remove)
  also have "... = 1" using assms by simp
  finally have "sum (\<lambda>x. f x * f x) I < 1" .
  thus False using assms by simp
qed

lemma cpx_pos_square_1_elem:
  assumes "finite I"
and "\<And>i. i \<in> I \<Longrightarrow> (0::complex) \<le> f i"
and "sum f I = 1"
and "sum (\<lambda>x. f x * f x) I = 1"
shows "\<exists>j \<in> I. f j = 1"
proof -
  have "\<forall>i\<in> I. Im( f i) = 0" using assms complex_is_Real_iff
    by (meson  nonnegative_complex_is_real 
        positive_unitary_diag_pos real_diag_decompD(1))
  hence al: "\<forall>i \<in> I. Re(f i) = f i"
    by (simp add: assms complex.expand)
  have "\<exists> j \<in> I. Re (f j) = 1"
  proof (rule pos_square_1_elem)
    show "finite I" using assms by simp
    show "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> Re (f i)" using assms al
      by (simp add: less_eq_complex_def) 
    show "(\<Sum>j\<in>I. Re (f j)) = 1" using al
      by (metis Re_sum assms(3) one_complex.simps(1))
    show "(\<Sum>x\<in>I. Re (f x) * Re (f x)) = 1" using al
      by (smt (z3) assms(4) of_real_hom.hom_1 of_real_hom.hom_mult 
          of_real_hom.hom_sum sum.cong) 
  qed
  thus ?thesis using al by force
qed

lemma sum_eq_elmt:
  assumes "finite I"
  and "\<And>i. i \<in> I \<Longrightarrow> (0::'a :: linordered_field) \<le> f i"
  and "sum f I = c"
  and "j\<in>I"
  and "f j = c"
shows "\<forall>k\<in>(I-{j}). f k = 0"
proof -
  have "sum f I - f j= sum f (I - {j})" using assms sum_diff1[of I f j] by auto
  also have "sum f I - f j = 0" using assms
    using \<open>f j = c\<close> by linarith
  hence "sum f (I - {j}) = 0" using assms
    using calculation by linarith 
  finally show "\<forall>k\<in>(I-{j}). f k = 0"
    by (meson DiffD1 \<open>sum f (I - {j}) = 0\<close> assms(1) assms(2) finite_Diff sum_nonneg_eq_0_iff)
qed

lemma cpx_sum_eq_elmt:
  assumes "finite I"
  and "\<And>i. i \<in> I \<Longrightarrow> (0::complex) \<le> f i"
  and "sum f I = c"
  and "j\<in>I"
  and "f j = c"
shows "\<forall>k\<in>(I-{j}). f k = 0"
proof -
  have "sum f I - f j= sum f (I - {j})" using assms sum_diff1[of I f j] by auto
  also have "sum f I - f j = 0" using assms
    using \<open>f j = c\<close> by simp
  hence "sum f (I - {j}) = 0" using assms
    using calculation by simp 
  finally show "\<forall>k\<in>(I-{j}). f k = 0"
    by (meson DiffD1 \<open>sum f (I - {j}) = 0\<close> assms(1) assms(2) 
        finite_Diff sum_nonneg_eq_0_iff)
qed

lemma sum_nat_div_mod:
  shows "sum (\<lambda>i. sum (\<lambda>j. f i * g j) {..< (m::nat)}) {..< (n::nat)} =  
    sum (\<lambda>k. f (k div m) * g (k mod m)) {..< n*m}" 
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "(\<Sum>i<Suc n. \<Sum>j<m. f i * g j) = (\<Sum>i< n. \<Sum>j<m. f i * g j) + 
    (\<Sum>j<m. f n * g j)" 
    by simp
  also have "... = (\<Sum>k<n * m. f (k div m) * g (k mod m)) + 
    (\<Sum>j<m. f n * g j)" 
    using Suc by simp
  also have "... = (\<Sum>k<n * m. f (k div m) * g (k mod m)) + 
    sum (\<lambda>k. f (k div m) * g (k mod m)) {n*m ..< (Suc n) * m}"
  proof -
    have "(\<Sum>j<m. f n * g j) = 
      sum (\<lambda>k. f (k div m) * g (k mod m)) {n*m ..< (Suc n) * m}"
    proof (rule sum.reindex_cong)
      show "inj_on (\<lambda>j. j mod m) {n * m..<Suc n * m}" 
      proof
        fix x y
        assume "x \<in> {n * m..<Suc n * m}" and "y \<in> {n * m..<Suc n * m}"
          and "x mod m = y mod m"
        thus "x = y"
          by (metis atLeastLessThan_iff div_nat_eqI mod_div_decomp 
              mult.commute)
      qed
      show "{..<m} = (\<lambda>j. j mod m) ` {n * m..<Suc n * m}"
      proof
        show "{..<m} \<subseteq> (\<lambda>j. j mod m) ` {n * m..<Suc n * m}"
        proof
          fix x
          assume "x\<in> {..< m}"
          hence "n * m + x\<in> {n * m..<Suc n * m}" by simp
          moreover have "x = (n * m + x) mod m" using \<open>x \<in> {..<m}\<close> by auto 
          ultimately show "x \<in> (\<lambda>j. j mod m) ` {n * m..<Suc n * m}" 
            using \<open>x \<in> {..<m}\<close> by blast 
        qed
      qed auto
      fix x
      assume "x \<in> {n * m..<Suc n * m}"
      thus "f n * g (x mod m) = f (x div m) * g (x mod m)" by auto
    qed
    thus ?thesis by simp
  qed
  also have "... = sum (\<lambda>k. f (k div m) * g (k mod m)) 
    ({..<n*m} \<union> {n * m..<Suc n * m})" 
    by (rule sum.union_disjoint[symmetric], auto)
  also have "... = (\<Sum>k<(Suc n) * m. f (k div m) * g (k mod m))" 
  proof -
    have "{..<n*m} \<union> {n * m..<Suc n * m} = {..< Suc n * m}"
      by (simp add: ivl_disj_un_one(2))
    thus ?thesis by simp
  qed
  finally show ?case .
qed

lemma abs_cmod_eq:
  fixes z::complex
  shows "\<bar>z\<bar> = cmod z"
  by (simp add: abs_complex_def)

lemma real_cpx_abs_leq:
  fixes A::complex
  assumes "A\<in> Reals"
  and "B\<in> Reals"
  and "\<bar>A * B\<bar> \<le> 1"
shows "\<bar>Re A * Re B\<bar> \<le> 1"
proof -
  have "\<bar>Re A * Re B\<bar> = \<bar>A * B\<bar>"  using assms
      by (metis Reals_mult abs_cmod_eq in_Reals_norm real_mult_re) 
  also have "... \<le> 1" using assms by simp 
  finally show "\<bar>Re A * Re B\<bar> \<le> 1"
    by (metis Re_complex_of_real less_eq_complex_def one_complex.sel(1)) 
qed

lemma cpx_real_abs_eq:
  fixes z::complex and r::real
  assumes "z\<in> Reals"
  and "z = r"
shows "\<bar>z\<bar> = \<bar>r\<bar>"
proof -
  have "Re z = r" using assms by simp
  have "Im z = 0"  using assms complex_is_Real_iff by auto
  have "\<bar>z\<bar> = cmod z" by (simp add: abs_complex_def)  
  hence "\<bar>z\<bar> = \<bar>Re z\<bar>" using \<open>Im z = 0\<close> assms by simp
  thus ?thesis using \<open>Re z = r\<close> by simp
qed

lemma cpx_real_abs_leq:
  fixes z::complex and r::real
  assumes "z\<in> Reals"
  and "z = r" 
  and "\<bar>r\<bar> \<le> k"
shows "\<bar>z\<bar> \<le> (k::real)"
proof -
  have "Re z = r" using assms by simp
  hence "\<bar>Re z\<bar> \<le> k" using assms by simp
  have "Im z = 0"  using assms complex_is_Real_iff by auto
  have "\<bar>z\<bar> = cmod z" by (simp add: abs_complex_def)  
  hence "\<bar>z\<bar> = \<bar>Re z\<bar>" using \<open>Im z = 0\<close> assms by simp
  thus ?thesis using \<open>\<bar>Re z\<bar> \<le> k\<close> by (simp add: less_eq_complex_def)
qed

lemma cpx_abs_mult_le_1:
  fixes z::complex
  assumes "\<bar>z\<bar> \<le> 1"
  and "\<bar>z'\<bar> \<le> 1"
shows "\<bar>z*z'\<bar> \<le> 1"
proof -
  have a: "cmod z \<le> 1"
    by (metis Reals_1 abs_1 abs_cmod_eq assms(1) 
        cpx_real_abs_leq dual_order.antisym linorder_le_cases 
        of_real_eq_1_iff)
  have b: "cmod z' \<le> 1"
    by (metis Reals_1 abs_1 abs_cmod_eq assms(2) 
        cpx_real_abs_leq dual_order.antisym linorder_le_cases 
        of_real_eq_1_iff)
  have "\<bar>z*z'\<bar> = \<bar>z\<bar>*\<bar>z'\<bar>"
    by (simp add: abs_mult)
  also have "... = cmod z * (cmod z')"
    using abs_cmod_eq by auto
  also have "... \<le> 1" using a b
    by (simp add: less_eq_complex_def mult_le_one)
  finally show ?thesis .
qed

lemma sum_abs_cpx:
  shows "\<bar>sum K I\<bar> \<le> sum (\<lambda>x. \<bar>(K x)::complex\<bar>) I"
proof -
  have "\<bar>sum K I\<bar> = cmod (sum K I)"
    using abs_cmod_eq by blast
  also have "... \<le> sum (\<lambda>x. cmod (K x)) I" using norm_sum
    by (metis Im_complex_of_real Re_complex_of_real less_eq_complex_def)
  also have "... = sum (\<lambda>x. \<bar>(K x)::complex\<bar>) I"
    using abs_cmod_eq by fastforce
  finally show ?thesis .
qed

lemma abs_mult_cpx:
  fixes z::complex
  assumes "0 \<le> (a::real)"
  shows "\<bar>a*z\<bar> = a * \<bar>z\<bar>"
proof -
  have "\<bar>a*z\<bar> = cmod (a*z)" using abs_cmod_eq by blast
  also have "... = a * cmod z" using assms
    by (simp add: norm_mult)
  also have "... = a * \<bar>z\<bar>" by (simp add: abs_cmod_eq) 
  finally show ?thesis .
qed

lemma cpx_ge_0_real:
  fixes c::complex
  assumes "0 \<le> c"
  and "c\<in> Reals"
shows "0 \<le> Re c" 
proof -
  have "Re c = c" using assms by simp
  hence "0 \<le> complex_of_real (Re (c::complex))" using assms by simp
  thus ?thesis using less_eq_complex_def by auto
qed

lemma cpx_of_real_ge_0:
  assumes "0 \<le> complex_of_real a"
  shows "0 \<le> a" 
proof -
  have "0 \<le> Re (complex_of_real a)"
    using Reals_of_real assms cpx_ge_0_real by blast
  also have "... = a" by simp
  finally show ?thesis .
qed


lemma set_cst_list:  
  shows "(\<And>i. i < length l \<Longrightarrow> l!i = x) \<Longrightarrow> 0 < length l \<Longrightarrow> set l = {x}"
proof (induct l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by (metis in_set_conv_nth insert_absorb is_singletonI' 
        is_singleton_def singleton_iff)
qed

lemma pos_mult_Max:
  assumes "finite F"
and "F \<noteq> {}"
and "0 \<le> x"
and "\<forall>a\<in> F. 0 \<le> (a::real)"
shows "Max.F {x * a|a. a \<in> F} = x * Max.F F" 
proof -
  define M where "M = Max.F F"
  have "finite {x * a|a. a \<in> F}" using assms by auto
  have "M\<in> F" using assms unfolding M_def by simp
  hence "x*M \<in> {x * a|a. a \<in> F}"  by auto
  moreover have "\<forall>c\<in>{x * a|a. a \<in> F}. c \<le> x*M"
    using M_def assms eq_Max_iff 
      ordered_comm_semiring_class.comm_mult_left_mono by fastforce
  ultimately show ?thesis using assms Max_eqI M_def \<open>finite {x * a |a. a \<in> F}\<close> 
    by blast
qed

lemma square_Max:
  assumes "finite A"
  and "A\<noteq> {}"
  and "\<forall>a\<in> A. 0 \<le> ((f a)::real)"
  and "b = Max.F {f a |a. a\<in> A}"
shows "Max.F {f a* f a|a. a\<in> A} = b * b" 
proof -
  define B where "B = {f a* f a|a. a\<in> A}"
  have "finite B" using finite_image_set unfolding B_def by (simp add: assms)
  have "finite {f a |a. a\<in> A}" using assms by auto
  hence "b\<in> {f a |a. a\<in> A}" using assms
    by (metis (mono_tags, lifting) Collect_empty_eq_bot Max_eq_iff all_not_in_conv 
        bot_empty_eq)
  hence "b*b \<in> B" unfolding B_def by auto
  moreover have "\<forall>c\<in>B. c \<le> b*b"
  proof
    fix c
    assume "c\<in> B"
    hence "\<exists>d\<in> A. c = f d* f d" unfolding B_def by auto
    from this obtain d where "d\<in> A" and "c = f d * f d" by auto 
      note dprop = this
    hence "f d \<in> {f a |a. a\<in> A}" by auto
    hence "f d \<le> b" using assms by auto
    thus "c \<le> b*b" using assms by (simp add: dprop mult_mono')
  qed
  ultimately show ?thesis using assms Max_eqI[of B "b*b"] \<open>finite B\<close> 
    by (metis B_def)
qed

lemma ereal_Sup_switch: 
  assumes "\<forall> m\<in> P. (b::real) \<le> f m"
  and "\<forall>m \<in> P. f m \<le> (c::real)"
  and "P \<noteq> {}"
shows "ereal (Sup (f ` P)) = (\<Squnion>m\<in> P. ereal (f m))"
proof (rule ereal_SUP)
  have b: "\<forall>m \<in> P. b \<le> (ereal (f m))" using assms by auto
  hence "b \<le> (\<Squnion> m\<in> P. ereal (f m))" using assms 
    by (meson Sup_upper2 ex_in_conv image_eqI) 
  have m: "\<forall>m \<in> P. (ereal (f m)) \<le> c" using assms by auto
  hence c: "Sup (ereal ` (f` P)) \<le> c"
    by (simp add: assms(3) cSUP_least image_image)  
  show "\<bar>\<Squnion> m\<in> P. ereal (f m)\<bar> \<noteq> \<infinity>" using b c MInfty_neq_ereal(2)
    by (metis PInfty_neq_ereal(1) m b 
        assms(3) ereal_SUP_not_infty) 
qed

lemma Sup_ge_real:
  assumes "a\<in> (A::real set)"
  and "\<forall>a \<in> A. a \<le> c"
  and "\<forall>a \<in> A. b \<le> a"
shows "a \<le> Sup A"
proof -
  define B where "B = {ereal a|a. a\<in> A}"
  have "ereal a \<in> B" using assms unfolding B_def by simp
  hence "ereal a \<le> Sup B" by (simp add: Sup_upper) 
  also have "... = ereal (Sup A)" 
    using ereal_Sup_switch[symmetric, of A b "\<lambda>x. x" c] assms unfolding B_def
    by (metis B_def Collect_mem_eq empty_iff image_Collect image_ident)
  finally have "ereal a \<le> ereal (Sup A)" .
  thus ?thesis by simp
qed

lemma Sup_real_le:
  assumes "\<forall>a \<in> (A::real set). a \<le> c"
  and "\<forall>a \<in> A. b \<le> a"
  and "A\<noteq> {}"
shows "Sup A \<le> c" 
proof -
  define B where "B = {ereal a|a. a\<in> A}"
  have "Sup B \<le> ereal c" unfolding B_def using SUP_least[of A "\<lambda>x. x" c] assms 
    by (simp add: Setcompr_eq_image) 
  moreover have "Sup B = ereal (Sup A)" unfolding B_def
    using ereal_Sup_switch[symmetric, of A b "\<lambda>x. x" c] assms 
    by (metis B_def Collect_mem_eq image_Collect image_ident)
  ultimately show ?thesis by simp
qed

section \<open>Results in linear algebra\<close>


lemma mat_add_eq_0_if:
  fixes A::"'a ::group_add Matrix.mat"
  assumes "A\<in> carrier_mat n m"
  and "B\<in> carrier_mat n m"
  and "A+B = 0\<^sub>m n m"
shows "B = -A" 
proof (rule eq_matI)
  show "dim_row B = dim_row (-A)" using assms by simp
  show "dim_col B = dim_col (-A)" using assms by simp
  fix i j
  assume "i < dim_row (-A)" and "j < dim_col (-A)" note ij= this
  hence "i < dim_row B" "j < dim_col B" 
    using \<open>dim_row B = dim_row (-A)\<close> \<open>dim_col B = dim_col (-A)\<close> by auto
  hence "A $$ (i,j) + B $$ (i,j) = (A+B)$$(i,j)" using ij by simp
  also have "... = 0"
    by (metis \<open>dim_col B = dim_col (-A)\<close> \<open>dim_row B = dim_row (-A)\<close> 
        assms(2) assms(3) carrier_matD(1) ij(1) ij(2) index_add_mat(3) 
        index_zero_mat(1) index_zero_mat(3))
  finally have "A $$ (i,j) + B $$ (i,j) = 0" .
  thus "B $$ (i, j) = (- A) $$ (i, j)"
    by (metis \<open>dim_col B = dim_col (- A)\<close> \<open>dim_row B = dim_row (- A)\<close> 
        \<open>i < dim_row B\<close> \<open>j < dim_col B\<close> add_eq_0_iff index_uminus_mat(1) 
        index_uminus_mat(2) index_uminus_mat(3))
qed

lemma trace_rank_1_proj:
  shows "Complex_Matrix.trace (rank_1_proj v) = \<parallel>v\<parallel>\<^sup>2"
proof -
  have "Complex_Matrix.trace (rank_1_proj v) = inner_prod v v" 
    using trace_outer_prod carrier_vecI
    unfolding rank_1_proj_def by blast
  also have "... = (vec_norm v)\<^sup>2" 
    unfolding vec_norm_def using power2_csqrt by presburger
  also have "... = \<parallel>v\<parallel>\<^sup>2" using vec_norm_sq_cpx_vec_length_sq by simp
  finally show ?thesis .
qed

lemma trace_ch_expand:
  fixes A::"'a::{minus,comm_ring} Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "C\<in> carrier_mat n n"
  and "D\<in> carrier_mat n n"
shows "Complex_Matrix.trace (A - B + C + D) =
  Complex_Matrix.trace A - Complex_Matrix.trace B + 
  Complex_Matrix.trace C + Complex_Matrix.trace D" 
proof -
  have "Complex_Matrix.trace (A - B + C + D) = 
    Complex_Matrix.trace (A - B + C) + Complex_Matrix.trace D" 
    using trace_add_linear[of _ n D] assms by simp
  also have "... = Complex_Matrix.trace (A - B) + Complex_Matrix.trace C + 
    Complex_Matrix.trace D" using assms trace_add_linear[of _ n C] 
    by (metis minus_carrier_mat')
  finally show ?thesis using assms trace_minus_linear by auto
qed

lemma squared_A_trace:
  assumes "A\<in> carrier_mat n n"
  and "unitarily_equiv A B U"
shows "Complex_Matrix.trace (A*A) = Complex_Matrix.trace (B*B)"
proof (rule unitarily_equiv_trace)
  show "A*A \<in> carrier_mat n n" using assms by simp
  show "unitarily_equiv (A * A) (B * B) U" 
    using assms unitarily_equiv_square[of A n] by simp
qed

lemma squared_A_trace':
assumes "A\<in> carrier_mat n n"
  and "unitary_diag A B U"
shows "Complex_Matrix.trace (A*A) = (\<Sum> i \<in> {0 ..< n}. (B $$ (i,i) * B $$ (i,i)))"
proof -
  have "Complex_Matrix.trace (A*A) = Complex_Matrix.trace (B*B)"
    using assms squared_A_trace[of A]
    by (meson unitary_diag_imp_unitarily_equiv)
  also have "... = (\<Sum> i \<in> {0 ..< n}. (B * B) $$ (i,i))" using assms 
    unfolding Complex_Matrix.trace_def
    by (metis (mono_tags, lifting) carrier_matD(1) index_mult_mat(2) 
        unitary_diag_carrier(1))
  also have "... = (\<Sum> i \<in> {0 ..< n}. (B $$ (i,i) * B $$ (i,i)))"
  proof (rule sum.cong)
    fix i
    assume "i \<in> {0..<n}"
    hence "i < n" by simp
    thus "(B*B) $$ (i,i) = B $$(i,i) * B$$(i,i)" using diagonal_mat_sq_index
      by (metis assms(1) assms(2) unitary_diag_carrier(1) 
          unitary_diag_diagonal) 
  qed simp
  finally show ?thesis .
qed


lemma positive_square_trace:
  assumes "A \<in> carrier_mat n n"
  and "Complex_Matrix.trace A = (1::real)"
  and "Complex_Matrix.trace (A*A) = 1"
  and "real_diag_decomp A B U"
  and "Complex_Matrix.positive A"
  and "0 < n" (*A retirer?*)
shows "\<exists>j<n. B $$ (j,j) = 1 \<and> (\<forall>i<n. i\<noteq>j \<longrightarrow> B $$ (i,i) = 0)"
proof -
  have b: "\<forall>i<n. 0 \<le> B $$ (i, i)" using assms positive_unitary_diag_pos
    by (meson \<open>real_diag_decomp A B U\<close> real_diag_decompD(1))
  also have t: "Complex_Matrix.trace B  = (1::real)" 
    using assms
    by (metis \<open>real_diag_decomp A B U\<close> of_real_1 real_diag_decompD(1) 
        unitarily_equiv_trace unitary_diag_imp_unitarily_equiv)
  have t_sq: "(\<Sum>i\<in>{0..<n}. (B $$ (i,i) * B $$ (i,i))) = 1" 
    using assms unitary_diag_carrier squared_A_trace'
    by (smt (verit, ccfv_SIG) \<open>real_diag_decomp A B U\<close> real_diag_decompD(1) sum.cong)
  have dim_n: "dim_row B = n" using assms
      by (meson \<open>real_diag_decomp A B U\<close> carrier_matD(1) 
          real_diag_decompD(1) unitary_diag_carrier(1))
  have ex_j: "\<exists>j\<in>{0..<n}.  (B $$ (j, j)) = 1"
  proof (rule cpx_pos_square_1_elem)
    show "finite {0..<n}" by simp
    show "\<And>i. i \<in> {0..<n} \<Longrightarrow> 0 \<le> B $$ (i, i)" using b by simp
    show "(\<Sum>j \<in> {0..<n}. B $$ (j, j)) = 1" using t 
      unfolding Complex_Matrix.trace_def
      by (metis \<open>dim_row B = n\<close> of_real_hom.hom_one)
    show "(\<Sum>x = 0..<n. B $$ (x, x) * B $$ (x, x)) = 1" using t_sq
      by blast
  qed
  from this obtain j where jn: "j\<in>{0..<n}" and bj: "B $$ (j, j) = 1" by auto
  have "\<forall>k \<in> ({0..<n}-{j}). B $$ (k, k) = 0"
  proof (rule cpx_sum_eq_elmt)
    show "finite {0..<n}" by simp
    show "\<And>i. i \<in> {0..<n} \<Longrightarrow> 0 \<le> B $$ (i, i)" using b by simp
    show "(\<Sum>k = 0..<n. B $$ (k, k)) = 1" using t 
      unfolding Complex_Matrix.trace_def
      by (simp add: dim_n) 
    show "j \<in> {0..<n}" using jn by simp
    show "B $$ (j, j) = 1" using bj by simp
  qed
  hence "\<forall>i<n. i \<noteq> j \<longrightarrow> B $$ (i, i) = 0"
    using atLeastLessThan_iff by blast
  thus ?thesis
    by (metis atLeastLessThan_iff bj jn)
qed

lemma idty_square:
  shows "((1\<^sub>m n):: 'a :: semiring_1 Matrix.mat) * (1\<^sub>m n) = 1\<^sub>m n" 
  using right_mult_one_mat by simp

lemma pos_hermitian_trace_reals:
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "0 < n"
  and "Complex_Matrix.positive A"
  and "hermitian B"
  shows "Complex_Matrix.trace (B*A) \<in> Reals"
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat n n"
  interpret cpx_sq_mat n n fc  
  proof 
    show "0 < n" using assms by simp
  qed (auto simp add: fc_def)
  have "Complex_Matrix.trace (B*A) = Complex_Matrix.trace (A*B)" using assms
    by (metis trace_comm)
  also have "... = Re (Complex_Matrix.trace (A * B))" 
  proof (rule trace_hermitian_pos_real[of B A])
    show "hermitian B" using assms by simp
    show "A\<in> fc" using assms unfolding fc_def by simp
    show "B\<in> fc" using assms unfolding fc_def by simp
    show "Complex_Matrix.positive A" using assms by simp
  qed
  finally have "Complex_Matrix.trace (B*A) =
    Re (Complex_Matrix.trace (A * B))" .
  thus ?thesis by (metis Reals_of_real) 
qed

lemma pos_hermitian_trace_reals':
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
  and "0 < n"
  and "Complex_Matrix.positive A"
  and "hermitian B"
  shows "Complex_Matrix.trace (A*B) \<in> Reals"
  by (metis assms pos_hermitian_trace_reals trace_comm)

lemma hermitian_commute:
  assumes "hermitian A"
  and "hermitian B"
  and "A*B = B*A"
shows "hermitian (A*B)"
  by (metis adjoint_mult assms hermitian_def 
      hermitian_square index_mult_mat(2))


lemma idty_unitary_diag:
  assumes "unitary_diag (1\<^sub>m n) B U"
  shows "B = 1\<^sub>m n"
proof -
  have l: "(Complex_Matrix.adjoint U) * U = 1\<^sub>m n"
    using assms one_carrier_mat similar_mat_witD2(2) unitary_diagD(1) by blast
  have r: "(Complex_Matrix.adjoint U) * U = 1\<^sub>m n"
    by (simp add: l)
  hence "B = ((Complex_Matrix.adjoint U) * U) * B * 
    ((Complex_Matrix.adjoint U) * U)" using l r
    by (metis assms index_one_mat(2) left_mult_one_mat' right_mult_one_mat 
        similar_mat_witD(5) similar_mat_wit_dim_row unitary_diagD(1))
  also have "... = (Complex_Matrix.adjoint U) * 
    (U * B * (Complex_Matrix.adjoint U)) * U"
    by (metis assms calculation similar_mat_witD(3) similar_mat_wit_sym 
        unitary_diagD(1))
  also have "... = (Complex_Matrix.adjoint U) * (1\<^sub>m n) * U"
    by (metis assms one_carrier_mat similar_mat_witD2(3) unitary_diagD(1))
  also have "... = 1\<^sub>m n"
    by (metis assms index_one_mat(2) l right_mult_one_mat similar_mat_witD(7) 
        unitary_diagD(1))
  finally show ?thesis .
qed

lemma diag_mat_idty:
  assumes "0 < n"
  shows "set (diag_mat ((1\<^sub>m n)::'a::{one,zero} Matrix.mat)) = {1}" 
    (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix x::'a
    assume "x \<in> set (diag_mat (1\<^sub>m n))"
    hence "\<exists>i < length (diag_mat (1\<^sub>m n)). nth (diag_mat (1\<^sub>m n))  i = x" 
      using in_set_conv_nth[of x "diag_mat (1\<^sub>m n)"] assms by simp
    from this obtain i where "i < length (diag_mat (1\<^sub>m n))" 
      and "nth (diag_mat (1\<^sub>m n))  i = x"
      by auto note iprop = this
    hence "i < dim_row (1\<^sub>m n)" unfolding diag_mat_def by simp
    hence "i < n" using assms by simp
    have "x = (1\<^sub>m n)$$(i,i)" using iprop unfolding diag_mat_def by simp
    thus "x \<in> ?R" using \<open>i < n\<close> by simp
  qed
next
  show "?R \<subseteq> ?L"
  proof
    fix x
    assume "x\<in> ?R"
    hence "x = 1" by simp
    also have "... = (1\<^sub>m n)$$(0,0)" using assms by simp
    also have "... \<in> ?L" using assms unfolding diag_mat_def by simp
    finally show "x\<in> ?L" .
  qed
qed

lemma idty_spectrum:
assumes "0 < n"
shows "spectrum ((1\<^sub>m n)::complex Matrix.mat) = {1}"
proof -
  have "spectrum ((1\<^sub>m n)::complex Matrix.mat) = set (diag_mat (1\<^sub>m n))"
    using similar_spectrum_eq
    by (meson one_carrier_mat similar_mat_refl upper_triangular_one)
  also have "... = {1}" using diag_mat_idty assms by simp
  finally show ?thesis .
qed

lemma spectrum_ne:
  fixes A::"complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  and "0 < n"
shows "spectrum A \<noteq> {}" unfolding spectrum_def 
  using eigvals_poly_length[of A] assms by auto

lemma  unitary_diag_square_spectrum:
  fixes A::"complex Matrix.mat"
  assumes "hermitian A"
  and "A\<in> carrier_mat n n"
and "unitary_diag A B U"
shows "spectrum (A*A) = set (diag_mat (B*B))"
proof -
  have sa: "similar_mat (A*A) (B*B)" 
    using assms hermitian_square_similar_mat_wit[of A n] 
    unfolding similar_mat_def by auto
  have  "diagonal_mat (B*B)" using diagonal_mat_sq_diag[of B] assms
    by (meson unitary_diag_carrier(1) unitary_diag_diagonal) 
  have "(\<Prod>a\<leftarrow>eigvals (A*A). [:- a, 1:]) = char_poly (A*A)" using assms
    by (metis eigvals_poly_length mult_carrier_mat) 
  also have "... = char_poly (B*B)" using char_poly_similar[OF sa] by simp
  also have "... = (\<Prod>a\<leftarrow>diag_mat (B*B). [:- a, 1:])" using  
      \<open>diagonal_mat (B*B)\<close>
    by (metis assms(2) assms(3) char_poly_upper_triangular 
        diagonal_imp_upper_triangular mult_carrier_mat 
        unitary_diag_carrier(1)) 
  finally  have  "(\<Prod>a\<leftarrow>eigvals (A*A). [:- a, 1:]) = 
    (\<Prod>a\<leftarrow>diag_mat (B*B). [:- a, 1:])" . 
  hence "set (eigvals (A*A)) = set (diag_mat (B*B))" 
    using poly_root_set_eq[of "eigvals (A*A)"] by simp
  thus ?thesis unfolding spectrum_def by simp
qed

lemma diag_mat_square_eq:
  fixes B::"'a::{ring} Matrix.mat"
  assumes "diagonal_mat B"
  and "B \<in> carrier_mat n n"
  shows "set (diag_mat (B*B)) = {b*b|b. b\<in> set (diag_mat B)}"
proof
  show "set (diag_mat (B * B)) \<subseteq> {b*b |b. b \<in> set (diag_mat B)}"
  proof
    fix x
    assume "x \<in> set (diag_mat (B * B))"
    hence "\<exists>i < length (diag_mat (B * B)). nth (diag_mat (B * B))  i = x" 
      using in_set_conv_nth[of x] by simp
    from this obtain i where "i < length (diag_mat (B * B))" 
      and "nth (diag_mat (B * B))  i = x"
      by auto note iprop = this
    hence "i < n" using assms unfolding diag_mat_def by simp
    have "(B*B) $$ (i,i) = x" using iprop 
      unfolding diag_mat_def by simp
    hence "B $$ (i,i)* B $$ (i,i) = x" 
      using diagonal_mat_sq_index[of B n i i] assms iprop \<open>i < n\<close> 
      by simp
    moreover have "B $$ (i,i) \<in> set (diag_mat B)" 
      using \<open>i < n\<close> assms in_set_conv_nth[of x] 
      unfolding diag_mat_def by auto
    ultimately show "x \<in> {b*b |b. b \<in> set (diag_mat B)}" by auto
  qed
next
  show "{b * b |b. b \<in> set (diag_mat B)} \<subseteq> set (diag_mat (B * B))"
  proof
    fix x
    assume "x \<in> {b * b |b. b \<in> set (diag_mat B)}"
    hence "\<exists>b\<in> set (diag_mat B). x = b * b" by auto
    from this obtain b where "b\<in> set (diag_mat B)" and "x = b * b" by auto
    hence "\<exists> i < length (diag_mat B). (diag_mat B)!i = b" 
      using in_set_conv_nth[of b] by simp
    from this obtain i where "i < length (diag_mat B)" 
      and "(diag_mat B) ! i = b" by auto
    note iprop = this
    hence "B $$ (i,i) = b" unfolding diag_mat_def by simp
    moreover have "i < n" using assms iprop unfolding diag_mat_def by simp
    ultimately have "(B*B) $$ (i,i) = x" 
      using \<open>x = b*b\<close> diagonal_mat_sq_index[of B n i i] assms iprop by simp
    hence "x = (diag_mat (B*B)) ! i" using \<open>i < n\<close> assms 
      unfolding diag_mat_def by fastforce
    moreover have "i<length (diag_mat (B * B))" 
      using \<open>i < n\<close> assms unfolding diag_mat_def by auto
    ultimately show "x \<in> set (diag_mat (B * B))" 
      using in_set_conv_nth[of x "diag_mat (B*B)"] 
      by simp
  qed
qed

lemma hermitian_square_spectrum_eq:
  fixes A::"complex Matrix.mat"
  assumes "hermitian A"
and "A\<in> carrier_mat n n"
and "0 < n"
shows "spectrum (A*A) = {a*a | a. a\<in> spectrum A}"
proof -
  obtain B U where herm: "real_diag_decomp A B U" 
    using hermitian_real_diag_decomp[of A] assms by auto
  hence "spectrum (A*A) = set (diag_mat (B*B))" 
    using unitary_diag_square_spectrum assms real_diag_decompD(1)  by blast
  also have "... = {a*a|a. a\<in> set (diag_mat B)}" 
    using diag_mat_square_eq[of B] assms herm
    by (meson real_diag_decompD(1) unitary_diagD(2) unitary_diag_carrier(1))
  also have "... = {a*a | a. a\<in> spectrum A}" 
    using assms herm real_diag_decompD(1) spectrum_def unitary_diag_spectrum_eq 
    by blast
  finally show ?thesis .
qed

lemma adjoint_uminus:
  shows "Complex_Matrix.adjoint (-A) = - (Complex_Matrix.adjoint A)"
proof (rule eq_matI)
  fix i j
  assume "i < dim_row (- Complex_Matrix.adjoint A)" and 
    "j < dim_col (- Complex_Matrix.adjoint A)"
  thus "Complex_Matrix.adjoint (- A) $$ (i, j) = 
    (- Complex_Matrix.adjoint A) $$ (i, j)"
    by (simp add: adjoint_eval conjugate_neg)
qed auto

lemma (in fixed_carrier_mat) sum_mat_zero:
  assumes "finite I"
  and "\<And>i. i \<in> I \<Longrightarrow> A i \<in> fc_mats"
  and "\<And>i. i\<in> I \<Longrightarrow> f i = 0"
shows "sum_mat (\<lambda> i. (f i)  \<cdot>\<^sub>m (A i)) I = 0\<^sub>m dimR dimC" using assms
proof (induct rule: finite_induct)
  case empty
  then show ?case using sum_mat_empty by simp
next
  case (insert j F)
  hence "sum_mat (\<lambda>i. f i \<cdot>\<^sub>m A i) (insert j F) = f j \<cdot>\<^sub>m A j + 
    sum_mat (\<lambda>i. f i \<cdot>\<^sub>m A i) F" 
    using sum_mat_insert
    by (smt (verit, best) Set.basic_monos(7) image_subsetI insertI1 
        smult_mem subset_insertI)
  also have "... = 0\<^sub>m dimR dimC + sum_mat (\<lambda>i. f i \<cdot>\<^sub>m A i) F" 
    using insert smult_zero[of "A j"] fc_mats_carrier by force
  also have "... = 0\<^sub>m dimR dimC + 0\<^sub>m dimR dimC" using insert by simp
  finally show ?case by simp
qed

lemma (in fixed_carrier_mat) sum_mat_zero':
  fixes A::"'b \<Rightarrow> 'a Matrix.mat"
  assumes "finite I"
  and "\<And>i. i \<in> I \<Longrightarrow> A i = 0\<^sub>m dimR dimC"
shows "sum_mat A I = 0\<^sub>m dimR dimC" using assms
proof (induct rule: finite_induct)
  case empty
  then show ?case using sum_mat_empty by simp
next
  case (insert j F)
  have "sum_mat A (insert j F) =  A j + sum_mat A F" using sum_mat_insert
    by (metis Set.basic_monos(7) image_subsetI insertI1 insert(1) 
        insert(2) insert(4) subset_insertI zero_mem) 
  also have "... = 0\<^sub>m dimR dimC + sum_mat A F" 
    using insert by simp
  also have "... = 0\<^sub>m dimR dimC + 0\<^sub>m dimR dimC" using insert by simp
  finally show ?case by simp
qed

lemma (in fixed_carrier_mat) sum_mat_remove:
  assumes "A ` I \<subseteq> fc_mats"
    and A: "finite I" and x: "x \<in> I"
  shows "sum_mat A I = A x + sum_mat A (I-{x})" unfolding sum_mat_def
  using assms sum_with_insert[of A x "I-{x}"] insert_Diff by fastforce

lemma (in fixed_carrier_mat) sum_mat_singleton:
  fixes A::"'b \<Rightarrow> 'a Matrix.mat"
  assumes "finite I"
  and "A ` I \<subseteq> fc_mats"
  and "j \<in> I"
  and "\<forall>i\<in>I. i \<noteq> j \<longrightarrow> f i = 0"
shows "sum_mat (\<lambda> i. (f i)  \<cdot>\<^sub>m (A i)) I = f j  \<cdot>\<^sub>m (A j)"
proof -
  have "sum_mat (\<lambda> i. (f i)  \<cdot>\<^sub>m (A i)) I = f j  \<cdot>\<^sub>m (A j) + 
    sum_mat (\<lambda> i. (f i)  \<cdot>\<^sub>m (A i)) (I-{j})" using sum_mat_remove
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) 
        image_subset_iff smult_mem)
  moreover have "sum_mat (\<lambda> i. (f i)  \<cdot>\<^sub>m (A i)) (I-{j}) = 0\<^sub>m dimR dimC"
  proof (rule sum_mat_zero)
    show "\<And>i. i \<in> I - {j}  \<Longrightarrow> A i \<in> fc_mats" using assms by auto
  qed (auto simp add: assms)
  ultimately show "sum_mat (\<lambda> i. (f i)  \<cdot>\<^sub>m (A i)) I = f j  \<cdot>\<^sub>m (A j)"
    by (metis Matrix.right_add_zero_mat assms(2) assms(3) fc_mats_carrier 
        image_subset_iff smult_mem)
qed

context fixed_carrier_mat 
begin
lemma sum_mat_disj_union:
  assumes "finite J"
  and "finite I"
  and "I \<inter> J = {}"
  and "\<forall> i \<in> I \<union> J. A i \<in> fc_mats"
shows "sum_mat A (I \<union> J) = sum_mat A I + sum_mat A J" using assms
proof (induct rule: finite_induct)
  case empty  
  then show ?case
    by (simp add: sum_mat_carrier)
next
  case (insert x F)
  have "sum_mat A (I \<union> (insert x F)) = sum_mat A (insert x (I \<union> F))" by simp
  also have "... = A x + sum_mat A (I \<union> F)" 
  proof (rule sum_mat_insert)
    show "A x \<in> fc_mats" by (simp add: local.insert(6))
    show "A ` (I \<union> F) \<subseteq> fc_mats" using local.insert(6) by force
    show "finite (I\<union> F)" using insert by simp
    show "x \<notin> I \<union> F" using insert by auto 
  qed
  also have "... = A x + sum_mat A I + sum_mat A F" using insert
    by (simp add: add_assoc fc_mats_carrier sum_mat_carrier)
  also have "... = sum_mat A I + sum_mat A (insert x F)"
  proof -
    have "A x + sum_mat A F = sum_mat A (insert x F)"
      by (simp add: insert.prems(3) local.insert(1) local.insert(2) 
          subset_eq sum_mat_insert) 
    thus ?thesis
      by (metis Un_iff add_assoc add_commute fc_mats_carrier 
          insertCI local.insert(6) sum_mat_carrier)
  qed
  finally show ?case .
qed

lemma sum_with_reindex_cong':
  fixes g :: "'c \<Rightarrow> 'a Matrix.mat"
  assumes "\<forall>x. g x \<in> fc_mats"
  and "\<forall>x. h x \<in> fc_mats"
  and "inj_on l B"
  and "\<And>x. x \<in> B \<Longrightarrow> g (l x) = h x"
  shows "sum_with (+) (0\<^sub>m dimR dimC) g (l ` B) = 
  sum_with (+) (0\<^sub>m dimR dimC) h B" 
  by (rule sum_with_reindex_cong, (simp add: assms)+)

lemma sum_mat_cong':
  shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> A i = B i) \<Longrightarrow> 
    (\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow> 
    (\<And>i. i\<in> I \<Longrightarrow> B i \<in> fc_mats) \<Longrightarrow> I = J \<Longrightarrow> sum_mat A I = sum_mat B J"
proof (induct arbitrary: J rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "sum_mat A (insert x F) = A x + sum_mat A F" 
    using insert sum_mat_insert[of A]
    by (meson image_subsetI insert_iff)
  also have "... = B x + sum_mat B F" using insert by force
  also have "... = sum_mat B (insert x F)" using insert sum_mat_insert[of B]
    by (metis image_subsetI insert_iff)
  also have "... = sum_mat B J" using insert by simp
  finally show ?case .
qed

lemma sum_mat_reindex_cong:
  assumes "finite B"
  and "\<And>x. x \<in> l` B \<Longrightarrow> g x \<in> fc_mats"
  and "\<And>x. x \<in> B \<Longrightarrow> h x \<in> fc_mats"
  and "inj_on l B"
  and "\<And>x. x \<in> B \<Longrightarrow> g (l x) = h x"
  shows "sum_mat g (l ` B) = sum_mat h B"
proof -
  define gp where "gp = (\<lambda>i. if i\<in> l`B then g i else (0\<^sub>m dimR dimC))"
  define hp where "hp = (\<lambda>i. if i \<in> B then h i else (0\<^sub>m dimR dimC))"
  have "sum_mat g (l`B) = sum_mat gp (l`B)" 
  proof (rule sum_mat_cong')
    show "\<And>i. i \<in> l ` B \<Longrightarrow> g i = gp i" unfolding gp_def by auto
    show "\<And>i. i \<in> l ` B \<Longrightarrow> g i \<in> fc_mats" using assms by simp
    show "\<And>i. i \<in> l ` B \<Longrightarrow> gp i \<in> fc_mats" unfolding gp_def using assms by auto
  qed (simp add: assms)+
  also have "... = sum_mat hp B" unfolding sum_mat_def
  proof (rule sum_with_reindex_cong')
    show "\<forall>x. gp x \<in> fc_mats" unfolding gp_def using assms
      by (simp add: zero_mem)
    show "\<forall>x. hp x \<in> fc_mats" unfolding hp_def using assms 
      by (simp add: zero_mem)
    show "\<And>x. x \<in> B \<Longrightarrow> gp (l x) = hp x"
      by (simp add: assms(5) gp_def hp_def)
  qed (simp add: assms)
  also have "... = sum_mat h B"
  proof (rule sum_mat_cong')
    show "\<And>i. i \<in> B \<Longrightarrow> hp i = h i" unfolding hp_def by auto
    show "\<And>i. i \<in> B \<Longrightarrow> hp i \<in> fc_mats" unfolding hp_def using assms by auto
    show "\<And>i. i \<in> B \<Longrightarrow> h i \<in> fc_mats" using assms by simp
  qed (simp add: assms)+
  finally show ?thesis .
qed

lemma sum_mat_mod_eq:
  fixes A :: "nat \<Rightarrow> 'a Matrix.mat"
  assumes "\<And>x. x \<in> {..<m} \<Longrightarrow> A x \<in> fc_mats"
shows "sum_mat (\<lambda>i. A (i mod m)) ((\<lambda>i. n * m+i)`{..< m}) = sum_mat A {..<m}" 
proof (rule sum_mat_reindex_cong)
  show "\<And>x. x \<in> {..<m} \<Longrightarrow> A ((n * m + x) mod m) = A x" by simp
  show "inj_on ((+) (n * m)) {..<m}" by simp
  show "\<And>x. x \<in> (+) (n * m) ` {..<m} \<Longrightarrow> A (x mod m) \<in> fc_mats" 
    using assms by force
qed (simp add: assms)+

lemma sum_mat_singleton':
  assumes "A i \<in> fc_mats"
  shows "sum_mat A {i} = A i"
  by (metis add_zero assms comm_add_mat empty_iff fc_mats_carrier 
      finite.intros(1) image_is_empty subsetI sum_mat_empty sum_mat_insert 
      zero_mem)

end

context cpx_sq_mat
begin

lemma sum_mat_mod_div_ne_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "dimR = n *m"
  and "nD \<noteq> 0"
shows "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j))) {..< nD}) 
  {..< nC} = 
  sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC*nD}" 
proof -
  define D where "D = (\<lambda>i. sum_mat (\<lambda>j. f i*g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j))) {..< nD})"
  have fc: "fc_mats = carrier_mat (n*m) (n*m)" 
    using assms fc_mats_carrier dim_eq 
    by simp
  show ?thesis using  assms
  proof (induct nC)
    case 0
    define C where "C = sum_mat D {..< (0::nat)}"
    have "C =  0\<^sub>m (n*m) (n*m)" unfolding C_def 
      using sum_mat_empty assms dim_eq
      by (simp add: fixed_carrier_mat_def)
    moreover have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< 0*nD} = 0\<^sub>m (n*m) (n*m)" 
      using sum_mat_empty assms dim_eq
      by (simp add: fixed_carrier_mat_def)
    ultimately show ?case unfolding C_def by simp
  next
    case (Suc nC)
    define C where "C = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC*nD}"
    have dm: "\<And>i. i \<in> {..<Suc nC} \<Longrightarrow> D i \<in> fc_mats"
    proof -
      fix i
      assume "i \<in> {..<Suc nC}"
      hence "A i \<in> carrier_mat n n" using Suc by simp
      hence "\<And>j. j\<in> {..< nD} \<Longrightarrow> B j \<in> carrier_mat m m" using Suc
        by simp
      hence "\<And>j. j\<in> {..< nD} \<Longrightarrow> A i \<Otimes> B j \<in> fc_mats" 
        using fc \<open>A i \<in> carrier_mat n n\<close> tensor_mat_carrier
        by (metis carrier_matD(1) carrier_matD(2))
      thus "D i \<in> fc_mats" unfolding D_def
        by (metis (mono_tags, lifting) cpx_sq_mat_smult fc_mats_carrier 
            sum_mat_carrier)
    qed
    have "sum_mat D {..< Suc nC} = sum_mat D ({..< nC} \<union> {nC..< Suc nC})" 
    proof -
      have "{..< Suc nC} = {..< nC} \<union> {nC..< Suc nC}" by auto
      thus ?thesis by simp
    qed
    also have "... = sum_mat D {..< nC} + sum_mat D {nC..< Suc nC}"
    proof (rule sum_mat_disj_union)
      show "\<forall>i\<in>{..<nC} \<union> {nC..<Suc nC}. D i \<in> fc_mats" using dm by auto
    qed auto
    also have "... = C + sum_mat D {nC..< Suc nC}" 
      using Suc unfolding C_def D_def by simp
    also have "... = C + (sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {nC*nD..< Suc nC*nD})"
    proof -
      have "sum_mat D {nC..< Suc nC} = sum_mat D {nC}" by simp
      also have "... = D nC"  using  dm
        by (simp add: sum_mat_singleton')
      also have "... = (sum_mat (\<lambda>i. (f nC * g (i mod nD))\<cdot>\<^sub>m 
        ((A nC) \<Otimes> (B (i mod nD)))) ((+) (nC * nD) ` {..<nD}))" 
        unfolding D_def 
      proof (rule sum_mat_mod_eq[symmetric])
        show "\<And>x. x \<in> {..<nD} \<Longrightarrow> f nC * g x \<cdot>\<^sub>m (A nC \<Otimes> B x) \<in> fc_mats" 
        proof -
          fix x
          assume "x\<in> {..< nD}"
          hence "B x \<in> carrier_mat m m" using Suc by simp
          have "A nC \<in> carrier_mat n n" using Suc by simp
          hence  "A nC \<Otimes> B x \<in> fc_mats" 
            using fc tensor_mat_carrier  \<open>B x \<in> carrier_mat m m\<close> by blast
          thus "f nC * g x \<cdot>\<^sub>m (A nC \<Otimes> B x) \<in> fc_mats"
            by (simp add: cpx_sq_mat_smult)
        qed
      qed
      also have "... = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
        ((A (i div nD)) \<Otimes> (B (i mod nD)))) {nC*nD..< Suc nC*nD}" 
      proof (rule sum_mat_cong')
        show "(+) (nC * nD) ` {..<nD} = {nC * nD..<Suc nC * nD}"
          by (simp add: lessThan_atLeast0) 
        show "\<And>i. i \<in> (+) (nC * nD) ` {..<nD} \<Longrightarrow> 
          f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) \<in> fc_mats"
        proof -
          fix i
          assume "i \<in> (+) (nC * nD) ` {..<nD}"
          hence "i mod nD < nD" using  assms mod_less_divisor by blast 
          hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
          moreover have "A nC \<in> carrier_mat n n" using Suc by simp
          ultimately have "A nC \<Otimes> B (i mod nD) \<in> fc_mats" 
            using fc tensor_mat_carrier by blast
          thus "f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) \<in> fc_mats"
            by (simp add: cpx_sq_mat_smult)
        qed
        show "\<And>i. i \<in> (+) (nC * nD) ` {..<nD} \<Longrightarrow> 
          f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) \<in> 
          fc_mats"
        proof -
          fix i
          assume "i \<in> (+) (nC * nD) ` {..<nD}"
          hence "i div nD = nC" using Suc(2) mod_less_divisor
            by (metis \<open>(+) (nC * nD) ` {..<nD} = {nC * nD..<Suc nC * nD}\<close> 
                index_div_eq semiring_norm(174))
          have "i mod nD < nD" using \<open>i \<in> (+) (nC * nD) ` {..<nD}\<close>  
              mod_less_divisor assms by blast
          hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
          moreover have "A (i div nD) \<in> carrier_mat n n" 
            using \<open>i div nD = nC\<close> Suc by simp
          ultimately have "A (i div nD) \<Otimes> B (i mod nD) \<in> fc_mats" 
            using fc tensor_mat_carrier by blast
          thus "f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) \<in>
             fc_mats"
            by (simp add: cpx_sq_mat_smult)
        qed
      qed auto
      finally have "sum_mat D {nC..< Suc nC} = 
        sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
        ((A (i div nD)) \<Otimes> (B (i mod nD)))) {nC*nD..< Suc nC*nD}" .
      thus ?thesis by simp
    qed
    also have "... =  
      sum_mat (\<lambda>i. f (i div nD)*g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)))
      ({..< nC * nD} \<union> {nC * nD..<Suc nC * nD})" unfolding C_def 
    proof (rule sum_mat_disj_union[symmetric])
      show "\<forall>i\<in>{..<nC * nD} \<union> {nC * nD..<Suc nC * nD}.
       f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) \<in> fc_mats" 
      proof
        fix i
        assume "i \<in> {..<nC * nD} \<union> {nC * nD..<Suc nC * nD}"
        hence "i \<in> {..< Suc nC * nD}" by auto
        hence "i div nD < Suc nC" using Suc(2) mod_less_divisor
          by (simp add: less_mult_imp_div_less)
        have "i mod nD < nD" using \<open>i \<in> {..<nC * nD} \<union> {nC * nD..<Suc nC * nD}\<close>
          Suc(2) mod_less_divisor assms by blast
        hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
        moreover have "A (i div nD) \<in> carrier_mat n n" 
          using \<open>i div nD < Suc nC\<close> Suc by simp
        ultimately have "A (i div nD) \<Otimes> B (i mod nD) \<in> fc_mats" 
          using fc tensor_mat_carrier by blast
        thus "f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) \<in>
           fc_mats"
          by (simp add: cpx_sq_mat_smult)
      qed
    qed auto
    also have "... = 
      sum_mat (\<lambda>i. f (i div nD)*g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)))
      {..< Suc nC * nD}"
    proof -
      have "{..< nC * nD} \<union> {nC * nD..<Suc nC * nD} = {..< Suc nC *  nD}" 
        by auto
      thus ?thesis by simp
    qed
    finally show ?case unfolding D_def .
  qed
qed

lemma sum_mat_mod_div_eq_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "0 < n"
  and "nD = 0"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j))) {..< nD}) 
  {..< nC} = 
  sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC*nD}" 
proof-
  have "{..< nC*nD} = {}" using assms by simp
  hence "sum_mat (\<lambda>i. f (i div nD) * g (i mod nD) \<cdot>\<^sub>m 
    (A (i div nD) \<Otimes> B (i mod nD))) {..<nC * nD} = 0\<^sub>m (n*m) (n*m)"
    using sum_mat_empty assms dim_eq
    by (simp add: fixed_carrier_mat_def)
  moreover have "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j \<cdot>\<^sub>m (A i \<Otimes> B j)) {..<nD}) 
    {..<nC} = 0\<^sub>m dimR dimC" 
  proof (rule sum_mat_zero')
    fix i
    assume "i \<in> {..< nC}"
    show "sum_mat (\<lambda>j. f i * g j \<cdot>\<^sub>m (A i \<Otimes> B j)) {..<nD} = 0\<^sub>m dimR dimC" 
      using assms sum_mat_empty by simp
  qed simp
  ultimately show ?thesis using assms dim_eq by simp
qed

lemma sum_mat_mod_div:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j))) {..< nD}) 
  {..< nC} = 
  sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC*nD}" 
proof (cases "nD = 0")
  case True
  then show ?thesis using sum_mat_mod_div_eq_0 assms by simp
next
  case False
  then show ?thesis using sum_mat_mod_div_ne_0 assms by simp
qed

lemma sum_sum_mat_expand_ne_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "R\<in> carrier_mat (n*m) (n*m)"
  and "0 < n"
  and "0 < m"
  and "nD \<noteq> 0"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j))*R) {..< nD}) 
  {..< nC} = 
  sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD))) * R) {..< nC*nD}" 
proof -
  define D where "D = (\<lambda>i. sum_mat (\<lambda>j. f i*g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j)) * R) 
    {..< nD})"
  have fc: "fc_mats = carrier_mat (n*m) (n*m)" 
    using assms fc_mats_carrier dim_eq 
    by simp
  show ?thesis using  assms
  proof (induct nC)
    case 0
    define C where "C = sum_mat D {..< (0::nat)}"
    have "C =  0\<^sub>m (n*m) (n*m)" unfolding C_def 
      using sum_mat_empty assms dim_eq
      by (simp add: fixed_carrier_mat_def)
    moreover have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD))) * R) {..< 0*nD} = 0\<^sub>m (n*m) (n*m)" 
      using sum_mat_empty assms dim_eq
      by (simp add: fixed_carrier_mat_def)
    ultimately show ?case unfolding C_def by simp
  next
    case (Suc nC)
    define C where "C = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))* R) {..< nC*nD}"
    have "R\<in> fc_mats" using fc_mats_carrier Suc dim_eq by simp
    have dm: "\<And>i. i \<in> {..<Suc nC} \<Longrightarrow> D i \<in> fc_mats"
    proof -
      fix i
      assume "i \<in> {..<Suc nC}"
      hence "A i \<in> carrier_mat n n" using Suc by simp
      hence "\<And>j. j\<in> {..< nD} \<Longrightarrow> B j \<in> carrier_mat m m" using Suc
        by simp
      hence "\<And>j. j\<in> {..< nD} \<Longrightarrow> A i \<Otimes> B j \<in> fc_mats" 
        using fc \<open>A i \<in> carrier_mat n n\<close> tensor_mat_carrier
        by (metis carrier_matD(1) carrier_matD(2))
      hence "\<And>j. j \<in> {..< nD} \<Longrightarrow> (A i \<Otimes> B j) * R \<in> fc_mats" using Suc fc
        using cpx_sq_mat_mult by blast
      thus "D i \<in> fc_mats" unfolding D_def
        by (metis (mono_tags, lifting) \<open>R \<in> fc_mats\<close> 
            \<open>\<And>j. j \<in> {..<nD} \<Longrightarrow> A i \<Otimes> B j \<in> fc_mats\<close> cpx_sq_mat_mult 
            cpx_sq_mat_smult fc_mats_carrier sum_mat_carrier)
    qed
    have "sum_mat D {..< Suc nC} = sum_mat D ({..< nC} \<union> {nC..< Suc nC})" 
    proof -
      have "{..< Suc nC} = {..< nC} \<union> {nC..< Suc nC}" by auto
      thus ?thesis by simp
    qed
    also have "... = sum_mat D {..< nC} + sum_mat D {nC..< Suc nC}"
    proof (rule sum_mat_disj_union)
      show "\<forall>i\<in>{..<nC} \<union> {nC..<Suc nC}. D i \<in> fc_mats" using dm by auto
    qed auto
    also have "... = C + sum_mat D {nC..< Suc nC}" 
      using Suc unfolding C_def D_def by simp
    also have "... = C + (sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD))) * R) {nC*nD..< Suc nC*nD})"
    proof -
      have "sum_mat D {nC..< Suc nC} = sum_mat D {nC}" by simp
      also have "... = D nC"  using  dm
        by (simp add: sum_mat_singleton')
      also have "... = (sum_mat (\<lambda>i. (f nC * g (i mod nD))\<cdot>\<^sub>m 
        ((A nC) \<Otimes> (B (i mod nD))) * R) ((+) (nC * nD) ` {..<nD}))" 
        unfolding D_def 
      proof (rule sum_mat_mod_eq[symmetric])
        show "\<And>x. x \<in> {..<nD} \<Longrightarrow> f nC * g x \<cdot>\<^sub>m (A nC \<Otimes> B x)*R \<in> fc_mats" 
        proof -
          fix x
          assume "x\<in> {..< nD}"
          hence "B x \<in> carrier_mat m m" using Suc by simp
          have "A nC \<in> carrier_mat n n" using Suc by simp
          hence  "A nC \<Otimes> B x \<in> fc_mats" 
            using fc tensor_mat_carrier  \<open>B x \<in> carrier_mat m m\<close> by blast
          thus "f nC * g x \<cdot>\<^sub>m (A nC \<Otimes> B x) * R \<in> fc_mats"
            by (simp add: \<open>R \<in> fc_mats\<close> cpx_sq_mat_mult cpx_sq_mat_smult)
        qed
      qed
      also have "... = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
        ((A (i div nD)) \<Otimes> (B (i mod nD))) * R) {nC*nD..< Suc nC*nD}" 
      proof (rule sum_mat_cong')
        show "(+) (nC * nD) ` {..<nD} = {nC * nD..<Suc nC * nD}"
          by (simp add: lessThan_atLeast0) 
        show "\<And>i. i \<in> (+) (nC * nD) ` {..<nD} \<Longrightarrow> 
          f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD))*R \<in> fc_mats"
        proof -
          fix i
          assume "i \<in> (+) (nC * nD) ` {..<nD}"
          hence "i mod nD < nD" using Suc mod_less_divisor by blast 
          hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
          moreover have "A nC \<in> carrier_mat n n" using Suc by simp
          ultimately have "A nC \<Otimes> B (i mod nD) \<in> fc_mats" 
            using fc tensor_mat_carrier by blast
          thus "f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) * R \<in> fc_mats"
             by (simp add: \<open>R \<in> fc_mats\<close> cpx_sq_mat_mult cpx_sq_mat_smult)
        qed
        show "\<And>i. i \<in> (+) (nC * nD) ` {..<nD} \<Longrightarrow> 
          f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) * R \<in> 
          fc_mats"
        proof -
          fix i
          assume "i \<in> (+) (nC * nD) ` {..<nD}"
          hence "i div nD = nC" using Suc(2) mod_less_divisor
            by (metis \<open>(+) (nC * nD) ` {..<nD} = {nC * nD..<Suc nC * nD}\<close> 
                index_div_eq semiring_norm(174))
          have "i mod nD < nD" using \<open>i \<in> (+) (nC * nD) ` {..<nD}\<close>  Suc
              mod_less_divisor by blast
          hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
          moreover have "A (i div nD) \<in> carrier_mat n n" 
            using \<open>i div nD = nC\<close> Suc by simp
          ultimately have "A (i div nD) \<Otimes> B (i mod nD) \<in> fc_mats" 
            using fc tensor_mat_carrier by blast
          thus "f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD))*R \<in>
             fc_mats"
             by (simp add: \<open>R \<in> fc_mats\<close> cpx_sq_mat_mult cpx_sq_mat_smult)
        qed
      qed auto
      finally have "sum_mat D {nC..< Suc nC} = 
        sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
        ((A (i div nD)) \<Otimes> (B (i mod nD)))* R) {nC*nD..< Suc nC*nD}" .
      thus ?thesis by simp
    qed
    also have "... =  
      sum_mat (\<lambda>i. f (i div nD)*g (i mod nD)\<cdot>\<^sub>m(A (i div nD) \<Otimes> B (i mod nD))*R)
      ({..< nC * nD} \<union> {nC * nD..<Suc nC * nD})" unfolding C_def 
    proof (rule sum_mat_disj_union[symmetric])
      show "\<forall>i\<in>{..<nC * nD} \<union> {nC * nD..<Suc nC * nD}.
       f (i div nD) *g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD))*R \<in> fc_mats" 
      proof
        fix i
        assume "i \<in> {..<nC * nD} \<union> {nC * nD..<Suc nC * nD}"
        hence "i \<in> {..< Suc nC * nD}" by auto
        hence "i div nD < Suc nC" using Suc(2) mod_less_divisor
          by (simp add: less_mult_imp_div_less)
        have "i mod nD < nD" using \<open>i \<in> {..<nC * nD} \<union> {nC * nD..<Suc nC * nD}\<close>
          Suc mod_less_divisor by blast
        hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
        moreover have "A (i div nD) \<in> carrier_mat n n" 
          using \<open>i div nD < Suc nC\<close> Suc by simp
        ultimately have "A (i div nD) \<Otimes> B (i mod nD) \<in> fc_mats" 
          using fc tensor_mat_carrier by blast
        thus "f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD))*R \<in>
           fc_mats"
           by (simp add: \<open>R \<in> fc_mats\<close> cpx_sq_mat_mult cpx_sq_mat_smult)
      qed
    qed auto
    also have "... = 
      sum_mat (\<lambda>i. f (i div nD)*g (i mod nD)\<cdot>\<^sub>m(A (i div nD) \<Otimes> B (i mod nD))*R)
      {..< Suc nC * nD}"
    proof -
      have "{..< nC * nD} \<union> {nC * nD..<Suc nC * nD} = {..< Suc nC *  nD}" 
        by auto
      thus ?thesis by simp
    qed
    finally show ?case unfolding D_def .
  qed
qed

lemma sum_sum_mat_expand_eq_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "R\<in> carrier_mat (n*m) (n*m)"
  and "0 < n"
  and "0 < m"
  and "nD = 0"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j))*R) {..< nD}) 
  {..< nC} = 
  sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD))) * R) {..< nC*nD}" 
proof -
  have "{..< nC*nD} = {}" using assms by simp
  hence "sum_mat (\<lambda>i. f (i div nD) * g (i mod nD) \<cdot>\<^sub>m 
    (A (i div nD) \<Otimes> B (i mod nD))*R) {..<nC * nD} = 0\<^sub>m (n*m) (n*m)"
    using sum_mat_empty assms dim_eq
    by (simp add: fixed_carrier_mat_def)
  moreover have "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j \<cdot>\<^sub>m (A i \<Otimes> B j)*R) 
    {..<nD}) 
    {..<nC} = 0\<^sub>m dimR dimC" 
  proof (rule sum_mat_zero')
    fix i
    assume "i \<in> {..< nC}"
    show "sum_mat (\<lambda>j. f i * g j \<cdot>\<^sub>m (A i \<Otimes> B j) * R) {..<nD} = 
      0\<^sub>m dimR dimC" 
      using assms sum_mat_empty by simp
  qed simp
  ultimately show ?thesis using assms dim_eq by simp
qed

lemma sum_sum_mat_expand:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "R\<in> carrier_mat (n*m) (n*m)"
  and "0 < n"
  and "0 < m"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j\<cdot>\<^sub>m ((A i) \<Otimes> (B j))*R) {..< nD}) 
  {..< nC} = 
  sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD))) * R) {..< nC*nD}"
proof (cases "nD = 0")
  case True
  then show ?thesis using assms sum_sum_mat_expand_eq_0 by simp
next
  case False
  then show ?thesis using assms sum_sum_mat_expand_ne_0 by simp
qed

end

section \<open>Results on tensor products\<close>

lemma tensor_mat_trace:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
shows "Complex_Matrix.trace (A \<Otimes> B) = Complex_Matrix.trace A *
  Complex_Matrix.trace B"
proof -
  have "{0 ..< n*m} = {..< n*m}" by auto
  have n: "{0 ..< n} = {..< n}" by auto
  have m: "{0 ..< m} = {..< m}" by auto
  have "Complex_Matrix.trace (A \<Otimes> B) = (\<Sum> i \<in> {0 ..< n*m}. (A \<Otimes> B) $$ (i,i))"
    unfolding Complex_Matrix.trace_def using tensor_mat_carrier assms by simp
  also have "... = (\<Sum> i \<in> {..< n*m}. 
    A $$ (i div m, i div m) * B $$ (i mod m, i mod m))"
    using index_tensor_mat' assms \<open>{0 ..< n*m} = {..< n*m}\<close> by simp
  also have "... =sum (\<lambda>i. sum (\<lambda>j. A $$ (i, i) * B $$ (j,j)) {..< m}) {..< n}"
    by (rule sum_nat_div_mod[symmetric])
  also have "... = sum (\<lambda>i. A $$(i,i)) {..< n}*(sum (\<lambda>j. B $$ (j,j)) {..< m})" 
    by (rule sum_product[symmetric])
  also have "... = Complex_Matrix.trace A * (Complex_Matrix.trace B)"
    using n m assms unfolding Complex_Matrix.trace_def by simp
  finally show ?thesis .
qed

lemma tensor_vec_inner_prod:
  assumes "u \<in> carrier_vec n"
  and "v \<in> carrier_vec n"
  and "a \<in> carrier_vec n"
  and "b \<in> carrier_vec n"
  and "0 < n"
shows "Complex_Matrix.inner_prod (tensor_vec u v) (tensor_vec a b) =
  Complex_Matrix.inner_prod u a * Complex_Matrix.inner_prod v b"
proof -
  have "{0 ..< n * n} = {..< n*n}" by auto
  have "{0 ..< n} = {..< n}" by auto
  have "Complex_Matrix.inner_prod (tensor_vec u v) (tensor_vec a b) = 
    (\<Sum> i \<in> {0 ..< n * n}. (vec_index (tensor_vec a b) i) * 
    vec_index (conjugate (tensor_vec u v)) i)" 
    unfolding scalar_prod_def using assms by simp
  also have "... = (\<Sum> i \<in> {0 ..< n * n}. vec_index a (i div n) * 
    vec_index b (i mod n) * (vec_index (conjugate (tensor_vec u v)) i))" 
  proof -
    have "\<forall> i < n * n. vec_index (tensor_vec a b) i = vec_index a (i div n) * 
    vec_index b (i mod n)" using assms by simp
    thus ?thesis by auto
  qed
  also have "... = (\<Sum> i \<in> {0 ..< n * n}. vec_index a (i div n) * 
    vec_index b (i mod n) * (conjugate (vec_index (tensor_vec u v) i)))" 
    using assms by simp
  also have "... = (\<Sum> i \<in> {0 ..< n * n}. vec_index a (i div n) * 
    vec_index b (i mod n) * (conjugate (vec_index u (i div n) * 
    vec_index v (i mod n))))" 
  proof -
    have "\<forall> i < n * n. vec_index (tensor_vec u v) i = vec_index u (i div n) * 
    vec_index v (i mod n)" 
      using assms by simp
    thus ?thesis by auto
  qed
  also have "... = (\<Sum> i \<in> {0 ..< n * n}. vec_index a (i div n) * 
    vec_index b (i mod n) * (conjugate (vec_index u (i div n)) * 
    (conjugate (vec_index v (i mod n)))))" 
    by simp
  also have "... = (\<Sum> i \<in> {0 ..< n * n}. vec_index a (i div n) * 
    (conjugate (vec_index u (i div n)) * (vec_index b (i mod n) *  
    (conjugate (vec_index v (i mod n))))))"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) 
        vector_space_over_itself.scale_left_commute)
  also have "... = (\<Sum> i \<in> {..< n * n}. (vec_index a (i div n) * 
    (conjugate (vec_index u (i div n))) * (vec_index b (i mod n) *  
    (conjugate (vec_index v (i mod n))))))"
    using \<open>{0 ..< n * n} = {..< n*n}\<close>
    by (metis (no_types, lifting) sum.cong vector_space_over_itself.scale_scale)
  also have "... =sum (\<lambda>i. sum (\<lambda>j. vec_index a i * conjugate (vec_index u i) *
    (vec_index b j * (conjugate (vec_index v j)))) {..< n}) {..< n}"
    by (rule sum_nat_div_mod[symmetric])
  also have "... = sum (\<lambda>i. vec_index a i * conjugate (vec_index u i)) {..< n}*
    (sum (\<lambda>j. vec_index b j * (conjugate (vec_index v j))) {..< n})" 
    by (rule sum_product[symmetric])
  also have "... = Complex_Matrix.inner_prod u a * Complex_Matrix.inner_prod v b" 
  proof -
    have "dim_vec (conjugate u) = n" using assms by simp
    moreover have "dim_vec (conjugate v) = n" using assms by simp
    ultimately show ?thesis using \<open>{0 ..< n} = {..< n}\<close> 
      unfolding Matrix.scalar_prod_def by simp
  qed
  finally show ?thesis .
qed

lemma tensor_mat_positive:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "Complex_Matrix.positive A"
  and "Complex_Matrix.positive B"
shows "Complex_Matrix.positive (A \<Otimes> B)"
proof (rule positive_if_decomp)
  show "A \<Otimes> B \<in> carrier_mat (n*m) (n*m)" using assms by auto
  have "\<exists>P \<in> carrier_mat n n. P * Complex_Matrix.adjoint P = A" 
    using assms positive_only_if_decomp by simp
  from this obtain P where "P\<in> carrier_mat n n" 
    and "P * Complex_Matrix.adjoint P = A" by auto note ppr = this
  have "\<exists>Q \<in> carrier_mat m m. Q * Complex_Matrix.adjoint Q = B" 
    using assms positive_only_if_decomp by simp
  from this obtain Q where "Q\<in> carrier_mat m m" 
    and "Q * Complex_Matrix.adjoint Q = B" by auto note qpr = this
  define M where "M = P \<Otimes> Q"
  have "Complex_Matrix.adjoint M = 
    Complex_Matrix.adjoint P \<Otimes> (Complex_Matrix.adjoint Q)" unfolding M_def 
    using tensor_mat_adjoint ppr qpr assms 
    by blast
  hence "M * Complex_Matrix.adjoint M = 
    (P * Complex_Matrix.adjoint P) \<Otimes> (Q * Complex_Matrix.adjoint Q)"
    using mult_distr_tensor M_def ppr qpr assms by fastforce
  also have "... = A \<Otimes> B" using ppr qpr by simp
  finally have "M * Complex_Matrix.adjoint M = A \<Otimes> B" .
  thus "\<exists>M. M * Complex_Matrix.adjoint M = A \<Otimes> B" by auto
qed


lemma tensor_mat_square_idty:
  assumes "A * A = 1\<^sub>m n"
  and "B * B = 1\<^sub>m m"
  and "0 < n"
  and "0 < m"
shows "(A \<Otimes> B) * (A \<Otimes> B) = 1\<^sub>m (n*m)"
proof -
  have "(A \<Otimes> B) * (A \<Otimes> B) = A*A \<Otimes> (B*B)" 
  proof (rule mult_distr_tensor[symmetric])
    show a: "dim_col A = dim_row A"
      by (metis assms(1) index_mult_mat(2) index_mult_mat(3) index_one_mat(2) 
          index_one_mat(3))
    show b: "dim_col B = dim_row B"
      by (metis assms(2) index_mult_mat(2) index_mult_mat(3) index_one_mat(2) 
          index_one_mat(3))
    show "0 < dim_col A"
      by (metis a assms(1) assms(3) index_mult_mat(2) index_one_mat(2))
    thus "0 < dim_col A" .
    show "0 < dim_col B"
      by (metis b assms(2) assms(4) index_mult_mat(2) index_one_mat(2))
    thus "0 < dim_col B" .
  qed
  also have "... = 1\<^sub>m n \<Otimes> 1\<^sub>m m" using assms by simp
  also have "... = 1\<^sub>m (n*m)" using tensor_mat_id assms by simp
  finally show ?thesis .
qed

lemma tensor_mat_commute:
  assumes "A \<in> carrier_mat n n"
  and "B \<in> carrier_mat m m"
  and "C \<in> carrier_mat n n"
  and "D \<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "A * C = C * A"
  and "B * D = D * B"
shows "(A \<Otimes> B) * (C \<Otimes> D) = (C \<Otimes> D) * (A \<Otimes> B)"
proof -
  have "(A \<Otimes> B) * (C \<Otimes> D) = (A*C) \<Otimes> (B*D)" using mult_distr_tensor assms
    by (metis carrier_matD(1) carrier_matD(2))
  also have "... = (C*A) \<Otimes> (D*B)" using assms by simp
  also have "... = (C \<Otimes> D) * (A \<Otimes> B)" using mult_distr_tensor assms
    by (metis carrier_matD(1) carrier_matD(2))
  finally show ?thesis .
qed

lemma tensor_mat_mult_id:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
shows "(A \<Otimes> 1\<^sub>m m) * (1\<^sub>m n \<Otimes> B) = A \<Otimes> B"
proof -
  have "(A \<Otimes> 1\<^sub>m m) * (1\<^sub>m n \<Otimes> B) = (A * 1\<^sub>m n) \<Otimes> (1\<^sub>m m * B)" 
    using mult_distr_tensor
    by (metis assms carrier_matD(1) carrier_matD(2) 
        index_one_mat(2) index_one_mat(3))
  also have "... = A \<Otimes> B"
    by (metis assms(1) assms(2) left_mult_one_mat right_mult_one_mat)
  finally show ?thesis .
qed

lemma tensor_mat_trace_mult_distr:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "C\<in> carrier_mat n n"
  and "D\<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  shows "Complex_Matrix.trace ((A \<Otimes>  B) * (C\<Otimes>D)) =
    Complex_Matrix.trace (A * C) * (Complex_Matrix.trace (B * D))" 
proof -
  have "(A \<Otimes>  B) * (C\<Otimes>D) = (A*C) \<Otimes> (B*D)" using assms mult_distr_tensor by auto
  hence "Complex_Matrix.trace ((A \<Otimes>  B) * (C\<Otimes>D)) =
    Complex_Matrix.trace ((A*C) \<Otimes> (B*D))" by simp
  also have "... = Complex_Matrix.trace (A * C) * (Complex_Matrix.trace (B * D))"
    by (meson assms mult_carrier_mat tensor_mat_trace) 
  finally show ?thesis .
qed

lemma tensor_mat_diagonal:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "diagonal_mat A"
  and "diagonal_mat B"
shows "diagonal_mat (A \<Otimes> B)" unfolding diagonal_mat_def
proof (intro allI impI)
  fix i j
  assume "i < dim_row (A \<Otimes> B)"
  and "j < dim_col (A \<Otimes> B)"
  and "i\<noteq> j"
  have "A \<Otimes> B \<in> carrier_mat (n*m) (n*m)" 
    using assms tensor_mat_carrier by blast
  hence "i < n * m"
    by (metis \<open>i < dim_row (A \<Otimes> B)\<close> carrier_matD(1))
  have "j < n* m"
    using \<open>A \<Otimes> B \<in> carrier_mat (n * m) (n * m)\<close> \<open>j < dim_col (A \<Otimes> B)\<close> by auto 
  have "(A \<Otimes> B) $$ (i, j) = A $$ (i div (dim_row B), j div (dim_col B)) * 
    B $$ (i mod (dim_row B), j mod (dim_col B))" using index_tensor_mat'
    by (metis \<open>i < dim_row (A \<Otimes> B)\<close> \<open>j < dim_col (A \<Otimes> B)\<close> dim_col_tensor_mat 
        dim_row_tensor_mat less_nat_zero_code neq0_conv semiring_norm(63) 
        semiring_norm(64))
  also have "... = 0" 
  proof (cases "i div (dim_row B) = j div (dim_col B)")
    case True
    have "i div (dim_row B) < n" using assms \<open>i < n * m\<close>
      by (metis carrier_matD(1) less_mult_imp_div_less)
    moreover have "j div (dim_row B) < n" using assms \<open>j < n * m\<close>
      by (metis carrier_matD(1) less_mult_imp_div_less)
    ultimately have "(i mod (dim_row B) \<noteq> j mod (dim_col B))" using \<open>i \<noteq> j\<close>
      by (metis True assms(2) carrier_matD(1) carrier_matD(2) mod_div_decomp)
    then show ?thesis using assms unfolding diagonal_mat_def
      by (metis \<open>i < n * m\<close> carrier_matD(1) carrier_matD(2) gr_zeroI 
          mod_less_divisor mult.commute semiring_norm(63) zero_order(3))
  next
    case False
    have "i div (dim_row B) < n" using assms \<open>i < n * m\<close>
      by (metis carrier_matD(1) less_mult_imp_div_less)
    moreover have "j div (dim_row B) < n" using assms \<open>j < n * m\<close>
      by (metis carrier_matD(1) less_mult_imp_div_less)
    ultimately show ?thesis using assms unfolding diagonal_mat_def
      by (metis False carrier_matD(1) carrier_matD(2) semiring_norm(63))
  qed
  finally show "(A \<Otimes> B) $$ (i, j) = 0" .
qed


lemma tensor_mat_add_right:
  assumes "A\<in> carrier_mat n m"
  and "B\<in> carrier_mat i j"
  and "C\<in> carrier_mat i j"
  and "0 < m"
  and "0 < j"
shows "A \<Otimes> (B + C) = (A \<Otimes> B) + (A \<Otimes> C)"
proof (rule eq_matI)
  have "B + C \<in> carrier_mat i j" using assms by simp
  hence bc: "A \<Otimes> (B + C) \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  have  "A \<Otimes> B \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  moreover have  "A \<Otimes> C \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  ultimately have a: "(A \<Otimes> B) + (A \<Otimes> C) \<in> carrier_mat (n * i) (m * j)" 
    by simp
  thus dr: "dim_row (A \<Otimes> (B + C)) = dim_row ((A \<Otimes> B) + (A \<Otimes> C))" 
    using bc by simp
  show dc: "dim_col (A \<Otimes> B + C) = dim_col ((A \<Otimes> B) + (A \<Otimes> C))" 
    using a bc by simp
  fix k l
  assume "k < dim_row ((A \<Otimes> B) + (A \<Otimes> C))"
  and "l < dim_col ((A \<Otimes> B) + (A \<Otimes> C))"
  hence "(A \<Otimes> B + C) $$ (k, l) = 
    A $$ (k div dim_row (B + C), l div dim_col (B + C)) * 
    (B + C) $$ (k mod dim_row (B + C), l mod dim_col (B + C))" 
    using index_tensor_mat'
    by (metis \<open>B + C \<in> carrier_mat i j\<close> dc dr assms(1) assms(4) assms(5) bc 
        carrier_matD(1) carrier_matD(2))
  also have "... = A $$ (k div dim_row (B + C), l div dim_col (B + C)) * 
    (B $$ (k mod dim_row (B + C), l mod dim_col (B + C)) +
    C $$ (k mod dim_row (B + C), l mod dim_col (B + C)))"
    by (metis div_eq_0_iff \<open>B + C \<in> carrier_mat i j\<close> 
        \<open>k < dim_row ((A \<Otimes> B) + (A \<Otimes> C))\<close> assms(3) assms(5) bc carrier_matD(1) 
        carrier_matD(2) dr index_add_mat(1) less_nat_zero_code mod_div_trivial 
        mult_not_zero)
  also have "... = A $$ (k div dim_row (B + C), l div dim_col (B + C)) * 
    B $$ (k mod dim_row (B + C), l mod dim_col (B + C)) + 
    A $$ (k div dim_row (B + C), l div dim_col (B + C)) * 
    C $$ (k mod dim_row (B + C), l mod dim_col (B + C))"
    using distrib_left by blast
  also have "... = (A \<Otimes> B) $$ (k,l) + (A \<Otimes> C) $$ (k,l)"
    using \<open>k < dim_row ((A \<Otimes> B) + (A \<Otimes> C))\<close> \<open>l < dim_col ((A \<Otimes> B) + (A \<Otimes> C))\<close> 
      assms by force
  also have "... = ((A \<Otimes> B) + (A \<Otimes> C)) $$ (k,l)"
    using \<open>k < dim_row ((A \<Otimes> B) + (A \<Otimes> C))\<close> \<open>l < dim_col ((A \<Otimes> B) + (A \<Otimes> C))\<close> 
    by force
  finally show "(A \<Otimes> B + C) $$ (k, l) = ((A \<Otimes> B) + (A \<Otimes> C)) $$ (k,l)" .
qed

lemma tensor_mat_zero:
  assumes "B \<in> carrier_mat i j"
  and "0 < j"
  and "0 < m"
shows "0\<^sub>m n m \<Otimes> B = 0\<^sub>m (n * i) (m * j)"
proof (rule eq_matI)
  show "dim_row (0\<^sub>m n m \<Otimes> B) = dim_row (0\<^sub>m (n * i) (m * j))" 
    using assms by simp
  show "dim_col (0\<^sub>m n m \<Otimes> B) = dim_col (0\<^sub>m (n * i) (m * j))" 
    using assms by simp
  fix k l
  assume "k < dim_row (0\<^sub>m (n * i) (m * j))" 
    and "l < dim_col (0\<^sub>m (n * i) (m * j))"
  thus "(0\<^sub>m n m \<Otimes> B) $$ (k, l) = 0\<^sub>m (n * i) (m * j) $$ (k,l)" 
    using index_tensor_mat assms less_mult_imp_div_less by force
qed

lemma tensor_mat_zero':
  assumes "B \<in> carrier_mat i j"
  and "0 < j"
  and "0 < m"
shows "B \<Otimes> 0\<^sub>m n m = 0\<^sub>m (i * n) (j*m)"
proof (rule eq_matI)
  show "dim_row (B \<Otimes> 0\<^sub>m n m) = dim_row (0\<^sub>m (i * n) (j * m))" 
    using assms by simp
  show "dim_col (B \<Otimes> 0\<^sub>m n m) = dim_col (0\<^sub>m (i * n) (j * m))" 
    using assms by simp
  fix k l
  assume "k < dim_row (0\<^sub>m (i * n) (j * m))" 
    and "l < dim_col (0\<^sub>m (i * n) (j * m))"
  thus "(B \<Otimes> 0\<^sub>m n m ) $$ (k, l) = 0\<^sub>m (i * n) (j * m) $$ (k,l)" 
    using index_tensor_mat assms less_mult_imp_div_less
    by (metis (no_types, lifting) carrier_matD(1) carrier_matD(2) 
        index_zero_mat(1) index_zero_mat(2) index_zero_mat(3) 
        less_nat_zero_code linorder_neqE_nat mod_less_divisor mult_eq_0_iff)
qed

lemma tensor_mat_sum_right:
  fixes A::"complex Matrix.mat"
  assumes "finite I"
  and "A\<in> carrier_mat n m"
  and "\<And>k. k\<in> I \<Longrightarrow> ((B k)::complex Matrix.mat) \<in> carrier_mat i j"
  and "0 < m"
  and "0 < j"
  and "dimR = n *i"
  and "dimC = m*j"
shows "A \<Otimes> (fixed_carrier_mat.sum_mat i j B I) = 
  fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A \<Otimes> (B i)) I" 
  using assms
proof (induct rule: finite_induct)
  case empty
  hence "A \<Otimes> (fixed_carrier_mat.sum_mat i j B {}) = 0\<^sub>m (n *i) (m*j)" 
    using tensor_mat_zero'
    by (simp add: fixed_carrier_mat.sum_mat_empty fixed_carrier_mat_def) 
  also have "... = fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A \<Otimes> (B i)) {}"
    by (metis fixed_carrier_mat.intro fixed_carrier_mat.sum_mat_empty)
  finally show ?case .
next
  case (insert x F)
  hence "A \<Otimes> (fixed_carrier_mat.sum_mat i j B (insert x F)) =
    A \<Otimes> (B x + (fixed_carrier_mat.sum_mat i j B F))"
  proof -
    have "fixed_carrier_mat.sum_mat i j B (insert x F) =
      B x + (fixed_carrier_mat.sum_mat i j B F)"
      using fixed_carrier_mat.sum_mat_insert
      by (metis fixed_carrier_mat.intro image_subsetI insertCI 
          insert(1) insert(2) insert(5))
    thus ?thesis by simp
  qed
  also have "... = (A \<Otimes> (B x)) + (A \<Otimes> (fixed_carrier_mat.sum_mat i j B F))"
  proof (rule tensor_mat_add_right)
    show "0 < m" using assms by simp
    show "0 < j" using assms by simp
    show "A \<in> carrier_mat n m" using insert by simp
    show "B x \<in> carrier_mat i j" using insert by simp
    show "fixed_carrier_mat.sum_mat i j B F \<in> carrier_mat i j" 
    proof (rule fixed_carrier_mat.sum_mat_carrier)
      show "\<And>k. k \<in> F \<Longrightarrow> B k \<in> carrier_mat i j" using insert by simp
      show "fixed_carrier_mat (carrier_mat i j) i j" 
        by (simp add: fixed_carrier_mat.intro) 
    qed
  qed
  also have "... = (A \<Otimes> (B x)) + 
    fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A \<Otimes> (B i)) F" 
    using insert by simp
  also have "... = fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A \<Otimes> (B i)) 
    (insert x F)"   
  proof (rule fixed_carrier_mat.sum_mat_insert[symmetric])
    show "finite F" using insert by simp
    show "x\<notin> F" using insert by simp
    show "A \<Otimes> B x \<in> carrier_mat (n*i) (m*j)" 
      using  tensor_mat_carrier insert
      by (metis carrier_matD(1) carrier_matD(2) insertI1) 
    show "(\<lambda>i. A \<Otimes> B i) ` F \<subseteq> carrier_mat (n*i) (m*j)" 
    proof -
      {
        fix k
        assume "k\<in> F"
        hence "A \<Otimes> (B k) \<in> carrier_mat (n*i) (m*j)" 
          using  tensor_mat_carrier insert by blast
      }
      thus ?thesis by auto
    qed
    show "fixed_carrier_mat (carrier_mat (n * i) (m * j)) (n * i) (m * j)"
      by (simp add: fixed_carrier_mat.intro)
  qed
  finally show "A \<Otimes> (fixed_carrier_mat.sum_mat i j B (insert x F)) =
    fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A \<Otimes> (B i)) (insert x F)" .
qed

lemma tensor_mat_add_left:
  assumes "A\<in> carrier_mat n m"
  and "B\<in> carrier_mat n m"
  and "C\<in> carrier_mat i j"
  and "0 < m"
  and "0 < j"
shows "(A + B) \<Otimes> C = (A \<Otimes> C) + (B \<Otimes> C)"
proof (rule eq_matI)
  have "A + B \<in> carrier_mat n m" using assms by simp
  hence bc: "(A+B) \<Otimes> C \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  have  "A \<Otimes> C \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  moreover have  "B \<Otimes> C \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  ultimately have a: "(A \<Otimes> C) + (B \<Otimes> C) \<in> carrier_mat (n * i) (m * j)" 
    by simp
  thus dr: "dim_row ((A+B) \<Otimes> C) = dim_row ((A \<Otimes> C) + (B \<Otimes> C))" 
    using bc by simp
  show dc: "dim_col ((A+B) \<Otimes> C) = dim_col ((A \<Otimes> C) + (B \<Otimes> C))" 
    using a bc by simp
  fix k l
  assume "k < dim_row ((A \<Otimes> C) + (B \<Otimes> C))"
  and "l < dim_col ((A \<Otimes> C) + (B \<Otimes> C))"
  hence "((A+B) \<Otimes> C) $$ (k, l) = 
    (A+B) $$ (k div dim_row C, l div dim_col C) * 
    C $$ (k mod dim_row C, l mod dim_col C)" 
    using index_tensor_mat'
    by (metis \<open>A + B \<in> carrier_mat n m\<close> assms(3) assms(4) assms(5) bc 
        carrier_matD(1) carrier_matD(2) dc dr)
  also have "... = (A $$ (k div dim_row C, l div dim_col C) + 
    B $$ (k div dim_row C, l div dim_col C)) *
    C $$ (k mod dim_row C, l mod dim_col C)"
    using \<open>k < dim_row ((A \<Otimes> C) + (B \<Otimes> C))\<close> \<open>l < dim_col ((A \<Otimes> C) + (B \<Otimes> C))\<close> 
      less_mult_imp_div_less by force
  also have "... = A $$ (k div dim_row C, l div dim_col C) * 
    C $$ (k mod dim_row C, l mod dim_col C) + 
    B $$ (k div dim_row C, l div dim_col C) * 
    C $$ (k mod dim_row C, l mod dim_col C)"
    using distrib_right by blast
  also have "... = (A \<Otimes> C) $$ (k,l) + (B \<Otimes> C) $$ (k,l)"
    using \<open>k < dim_row ((A \<Otimes> C) + (B \<Otimes> C))\<close> \<open>l < dim_col ((A \<Otimes> C) + (B \<Otimes> C))\<close> 
      assms by fastforce
  also have "... = ((A \<Otimes> C) + (B \<Otimes> C)) $$ (k,l)"
    using \<open>k < dim_row ((A \<Otimes> C) + (B \<Otimes> C))\<close> \<open>l < dim_col ((A \<Otimes> C) + (B \<Otimes> C))\<close> 
    by force
  finally show "((A+B) \<Otimes> C) $$ (k, l) = ((A \<Otimes> C) + (B \<Otimes> C)) $$ (k,l)" .
qed

lemma tensor_mat_smult_left:
  assumes "A\<in> carrier_mat n m"
  and "B\<in> carrier_mat i j"
  and "0 < m"
  and "0 < j"
shows "x  \<cdot>\<^sub>m A  \<Otimes> B = x  \<cdot>\<^sub>m (A \<Otimes> B)"
proof (rule eq_matI)
  have "x  \<cdot>\<^sub>m A \<in> carrier_mat n m" using assms by simp
  hence "x \<cdot>\<^sub>m A \<Otimes> B \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  moreover have "A \<Otimes> B \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  ultimately show 
    "dim_row (x \<cdot>\<^sub>m A \<Otimes> B) = dim_row (x \<cdot>\<^sub>m (A \<Otimes> B))" 
    "dim_col (x \<cdot>\<^sub>m A \<Otimes> B) = dim_col (x \<cdot>\<^sub>m (A \<Otimes> B))" by auto
  fix k l
  assume k: "k < dim_row (x \<cdot>\<^sub>m (A \<Otimes> B))"
  and l: "l < dim_col (x \<cdot>\<^sub>m (A \<Otimes> B))"
  hence "(x \<cdot>\<^sub>m A \<Otimes> B) $$ (k, l) = 
    (x \<cdot>\<^sub>m A) $$ (k div dim_row B, l div dim_col B) * 
    B $$ (k mod dim_row B, l mod dim_col B)" 
    using index_tensor_mat' assms by force
  also have "... = x * (A $$ (k div dim_row B, l div dim_col B)) * 
    B $$ (k mod dim_row B, l mod dim_col B)"
    using k l less_mult_imp_div_less by fastforce
  also have "... = x * (A $$ (k div dim_row B, l div dim_col B) * 
    B $$ (k mod dim_row B, l mod dim_col B))" by simp
  also have "... = x * (A \<Otimes> B) $$ (k,l)"
    using assms k l by force
  also have "... = (x \<cdot>\<^sub>m (A \<Otimes> B)) $$ (k,l)" using assms k l by auto
  finally show "(x \<cdot>\<^sub>m A \<Otimes> B) $$ (k, l) = (x \<cdot>\<^sub>m (A \<Otimes> B)) $$ (k,l)" .
qed

lemma tensor_mat_smult_right:
  assumes "A\<in> carrier_mat n m"
  and "B\<in> carrier_mat i j"
  and "0 < m"
  and "0 < j"
shows "A  \<Otimes> (x  \<cdot>\<^sub>m B) = x  \<cdot>\<^sub>m (A \<Otimes> B)"
proof (rule eq_matI)
  have "x  \<cdot>\<^sub>m B \<in> carrier_mat i j" using assms by simp
  hence "A \<Otimes> (x \<cdot>\<^sub>m B) \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  moreover have "A \<Otimes> B \<in> carrier_mat (n * i) (m * j)" 
    using assms tensor_mat_carrier
    by (metis carrier_matD(1) carrier_matD(2))
  ultimately show 
    "dim_row (A \<Otimes> x \<cdot>\<^sub>m B) = dim_row (x \<cdot>\<^sub>m (A \<Otimes> B))" 
    "dim_col (A \<Otimes> x \<cdot>\<^sub>m B) = dim_col (x \<cdot>\<^sub>m (A \<Otimes> B))" by auto
  fix k l
  assume k: "k < dim_row (x \<cdot>\<^sub>m (A \<Otimes> B))"
  and l: "l < dim_col (x \<cdot>\<^sub>m (A \<Otimes> B))"
  hence "(A \<Otimes> (x \<cdot>\<^sub>m B)) $$ (k, l) = 
    A $$ (k div dim_row (x \<cdot>\<^sub>m B), l div dim_col (x \<cdot>\<^sub>m B)) * 
    (x \<cdot>\<^sub>m B) $$ (k mod dim_row (x \<cdot>\<^sub>m B), l mod dim_col (x \<cdot>\<^sub>m B))" 
    using index_tensor_mat' assms by force
  also have "... = A $$ (k div dim_row (x \<cdot>\<^sub>m B), l div dim_col (x \<cdot>\<^sub>m B)) * 
    (x * B $$ (k mod dim_row (x \<cdot>\<^sub>m B), l mod dim_col (x \<cdot>\<^sub>m B)))"
    using k l
    by (metis (no_types, opaque_lifting) add_lessD1 dim_col_tensor_mat 
        dim_row_tensor_mat index_smult_mat(1) index_smult_mat(2) 
        index_smult_mat(3) mod_less_divisor nat_0_less_mult_iff 
        plus_nat.simps(1)) 
  also have "... = x *(A$$ (k div dim_row (x \<cdot>\<^sub>m B), l div dim_col (x \<cdot>\<^sub>m B))* 
    B $$ (k mod dim_row (x \<cdot>\<^sub>m B), l mod dim_col (x \<cdot>\<^sub>m B)))" by simp
  also have "... = x * (A \<Otimes> B) $$ (k,l)"
    using assms k l by force
  also have "... = (x \<cdot>\<^sub>m (A \<Otimes> B)) $$ (k,l)" using assms k l by auto
  finally show "(A \<Otimes> (x \<cdot>\<^sub>m B)) $$ (k, l) = (x \<cdot>\<^sub>m (A \<Otimes> B)) $$ (k,l)" .
qed

lemma tensor_mat_smult:
  assumes "A\<in> carrier_mat n m"
  and "B\<in> carrier_mat i j"
  and "0 < m"
  and "0 < j"
shows "x \<cdot>\<^sub>m A  \<Otimes> (y  \<cdot>\<^sub>m B) = x * y  \<cdot>\<^sub>m (A \<Otimes> B)"
  by (metis (no_types, opaque_lifting) assms smult_carrier_mat 
      smult_smult_times tensor_mat_smult_left tensor_mat_smult_right)

lemma tensor_mat_singleton_right:
  assumes "0 < dim_col A"
  and "B \<in> carrier_mat 1 1"
shows "A \<Otimes> B = B $$(0,0)  \<cdot>\<^sub>m A"
proof (rule eq_matI)
  show "dim_row (A \<Otimes> B) = dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)" using assms by auto
  show "dim_col (A \<Otimes> B) = dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)" using assms by auto
  fix i j
  assume "i < dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)"
  and "j < dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)"
  have "(A \<Otimes> B) $$ (i, j) = A $$ (i div dim_row B,j div dim_col B) * 
    B $$(i mod dim_row B, j mod dim_col B)" using index_tensor_mat
    \<open>i < dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> \<open>j < dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> assms 
    by fastforce
  also have "... = A $$(i,j) * B$$(0,0)" using assms by auto
  also have "... = (B $$ (0, 0) \<cdot>\<^sub>m A) $$ (i, j)"
    using \<open>i < dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> \<open>j < dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> 
    by force
  finally show "(A \<Otimes> B) $$ (i, j) = (B $$ (0, 0) \<cdot>\<^sub>m A) $$ (i, j)" .
qed

lemma tensor_mat_singleton_left:
  assumes "0 < dim_col A"
  and "B \<in> carrier_mat 1 1"
shows "B \<Otimes> A = B $$(0,0)  \<cdot>\<^sub>m A"
proof (rule eq_matI)
  show "dim_row (B \<Otimes> A) = dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)" using assms by auto
  show "dim_col (B \<Otimes> A) = dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)" using assms by auto
  fix i j
  assume "i < dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)"
  and "j < dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)"
  have "(B \<Otimes> A) $$ (i, j) = A $$ (i div dim_row B,j div dim_col B) * 
    B $$(i mod dim_row B, j mod dim_col B)" using index_tensor_mat
    \<open>i < dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> \<open>j < dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> assms 
    by fastforce
  also have "... = A $$(i,j) * B$$(0,0)" using assms by auto
  also have "... = (B $$ (0, 0) \<cdot>\<^sub>m A) $$ (i, j)"
    using \<open>i < dim_row (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> \<open>j < dim_col (B $$ (0, 0) \<cdot>\<^sub>m A)\<close> 
    by force
  finally show "(B \<Otimes> A) $$ (i, j) = (B $$ (0, 0) \<cdot>\<^sub>m A) $$ (i, j)" .
qed

lemma tensor_mat_sum_left:
  assumes "finite I"
  and "B\<in> carrier_mat i j"
  and "\<And>k. k\<in> I \<Longrightarrow> A k \<in> carrier_mat n m"
  and "0 < m"
  and "0 < j"
  and "dimR = n *i"
  and "dimC = m*j"
shows "(fixed_carrier_mat.sum_mat n m A I) \<Otimes> B = 
  fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. (A i) \<Otimes> B) I" 
  using assms
proof (induct rule: finite_induct)
  case empty
  hence "(fixed_carrier_mat.sum_mat n m A {}) \<Otimes> B = 0\<^sub>m (n *i) (m*j)" 
    using tensor_mat_zero
    by (simp add: fixed_carrier_mat.sum_mat_empty fixed_carrier_mat_def) 
  also have "... = fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. (A i) \<Otimes> B) {}"
    by (metis fixed_carrier_mat.intro fixed_carrier_mat.sum_mat_empty)
  finally show ?case .
next
  case (insert x F)
  hence "(fixed_carrier_mat.sum_mat n m A (insert x F)) \<Otimes> B =
    (A x + (fixed_carrier_mat.sum_mat n m A F))  \<Otimes> B"
  proof -
    have "fixed_carrier_mat.sum_mat n m A (insert x F) =
      A x + (fixed_carrier_mat.sum_mat n m A F)"
      using fixed_carrier_mat.sum_mat_insert
      by (metis fixed_carrier_mat.intro image_subsetI insertCI 
          insert(1) insert(2) insert(5))
    thus ?thesis by simp
  qed
  also have "... = (A x \<Otimes> B) + (fixed_carrier_mat.sum_mat n m A F \<Otimes> B)"
  proof (rule tensor_mat_add_left)
    show "0 < m" using assms by simp
    show "0 < j" using assms by simp
    show "A x \<in> carrier_mat n m" using insert by simp
    show "B \<in> carrier_mat i j" using insert by simp
    show "fixed_carrier_mat.sum_mat n m A F \<in> carrier_mat n m" 
    proof (rule fixed_carrier_mat.sum_mat_carrier)
      show "\<And>k. k \<in> F \<Longrightarrow> A k \<in> carrier_mat n m" using insert by simp
      show "fixed_carrier_mat (carrier_mat n m) n m" 
        by (simp add: fixed_carrier_mat.intro) 
    qed
  qed
  also have "... = (A x \<Otimes> B) + 
    fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A i \<Otimes> B) F" 
    using insert by simp
  also have "... = fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A i \<Otimes> B) 
    (insert x F)"  
  proof (rule fixed_carrier_mat.sum_mat_insert[symmetric])
    show "finite F" using insert by simp
    show "x\<notin> F" using insert by simp
    show "A x \<Otimes> B \<in> carrier_mat (n*i) (m*j)" 
      using  tensor_mat_carrier insert by blast
    show "(\<lambda>i. A i \<Otimes> B) ` F \<subseteq> carrier_mat (n*i) (m*j)" 
    proof -
      {
        fix k
        assume "k\<in> F"
        hence "A k \<Otimes> B \<in> carrier_mat (n*i) (m*j)" 
          using tensor_mat_carrier insert by blast
      }
      thus ?thesis by auto
    qed
    show "fixed_carrier_mat (carrier_mat (n * i) (m * j)) (n * i) (m * j)"
      by (simp add: fixed_carrier_mat.intro)
  qed
  finally show "fixed_carrier_mat.sum_mat n m A (insert x F) \<Otimes> B =
    fixed_carrier_mat.sum_mat (n*i) (m*j) (\<lambda>i. A i \<Otimes> B) (insert x F)" .
qed

lemma tensor_mat_diag_elem:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat m m"
  and "i < n * m"
  and "0 < n*m"
shows "(A \<Otimes> B) $$ (i, i) = A $$ (i div m, i div m) * 
    B $$ (i mod m, i mod m)"
proof -
  have "i < dim_row (A \<Otimes> B)" using assms by auto
  have "(A \<Otimes> B) $$ (i, i) = A $$ (i div (dim_row B), i div (dim_col B)) * 
    B $$ (i mod (dim_row B), i mod (dim_col B))" using index_tensor_mat'
    by (metis \<open>i < dim_row (A \<Otimes> B)\<close> assms carrier_matD(2) dim_row_tensor_mat 
        nat_0_less_mult_iff)
  also have "... = A $$ (i div m, i div m) * B $$ (i mod m, i mod m)"
    using assms by auto
  finally show ?thesis .
qed

context cpx_sq_mat
begin

lemma tensor_mat_sum_mat_right:
  assumes "finite I"
  and "A\<in> carrier_mat n n"
  and "\<And>k. k\<in> I \<Longrightarrow> B k \<in> carrier_mat i i"
  and "0 < n"
  and "0 < i"
  and "dimR = n *i"
shows "A \<Otimes> (fixed_carrier_mat.sum_mat i i B I) = sum_mat (\<lambda>i. A \<Otimes> (B i)) I"
  using assms dim_eq tensor_mat_sum_right by blast 

lemma tensor_mat_sum_mat_left:
  assumes "finite I"
  and "B\<in> carrier_mat i i"
  and "\<And>k. k\<in> I \<Longrightarrow> A k \<in> carrier_mat n n"
  and "0 < n"
  and "0 < i"
  and "dimR = n *i"
shows "(fixed_carrier_mat.sum_mat n n A I) \<Otimes> B = sum_mat (\<lambda>i. (A i) \<Otimes> B) I" 
  using assms dim_eq tensor_mat_sum_left by blast 

lemma tensor_mat_sum_nat_mod_div_ne_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  and "nD\<noteq> 0"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD)))) 
  {..< nC*nD} = C\<Otimes> D" using assms
proof (induct nC arbitrary: C)
  case 0
  hence "C = fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {}" by simp
  also have "... =  0\<^sub>m n n" 
    using fixed_carrier_mat.sum_mat_empty[of _ n n "\<lambda>i. f i \<cdot>\<^sub>m (A i)"]
    by (simp add: fixed_carrier_mat_def)
  finally have "C = 0\<^sub>m n n" .
  moreover have "D \<in> carrier_mat m m" using 0
    fixed_carrier_mat.sum_mat_carrier[of _ m m "{..< nD}" "\<lambda>j. g j \<cdot>\<^sub>m (B j)"]
    by (simp add: fixed_carrier_mat_def)
  ultimately have "C\<Otimes> D = 0\<^sub>m (n*m) (n*m)" using tensor_mat_zero
    by (simp add: "0"(5) "0"(6)) 
  have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) 
    {..< 0*nD} = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) {}" by simp
  also have "... = 0\<^sub>m (n*m) (n*m)" using sum_mat_empty
    using "0" dim_eq by blast
  also have "... = C\<Otimes> D" using \<open>C\<Otimes> D = 0\<^sub>m (n*m) (n*m)\<close> by simp
  finally show ?case .
next
  case (Suc nC)
  define Cp where 
    "Cp = fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC}"
  have fc: "\<forall>i\<in>{..<nC * nD} \<union> {nC * nD..<Suc nC * nD}.
    (A (i div nD) \<Otimes> B (i mod nD)) \<in> fc_mats" 
  proof
    fix i
    assume "i \<in> {..<nC * nD} \<union> {nC * nD..<Suc nC * nD}"
    hence i: "i \<in> {..< Suc nC * nD}" by auto
    hence "i div nD < Suc nC"
      by (simp add: less_mult_imp_div_less) 
    hence "A (i div nD) \<in> carrier_mat n n" using Suc by simp
    have "i mod nD < nD" using Suc by simp 
    hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
    hence "A (i div nD) \<Otimes> B (i mod nD) \<in> carrier_mat (n*m) (n*m)" 
      using tensor_mat_carrier
      by (metis \<open>A (i div nD) \<in> carrier_mat n n\<close> 
          carrier_matD(1) carrier_matD(2))
    thus "(A (i div nD) \<Otimes> B (i mod nD)) \<in> fc_mats"
      using Suc dim_eq fc_mats_carrier by blast 
  qed
  have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) 
    {..< (Suc nC)*nD} = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC*nD} + 
    sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) {nC*nD..< (Suc nC)*nD}"  
  proof -
    have "{..< (Suc nC)*nD} = {..< nC*nD} \<union> {nC*nD..< (Suc nC)*nD}" by auto
    moreover have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) 
      ({..< nC*nD} \<union> {nC*nD..< (Suc nC)*nD}) = 
      sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC*nD} + 
      sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {nC*nD..< (Suc nC)*nD}"
    proof (rule sum_mat_disj_union)
      show "{..<nC * nD} \<inter> {nC * nD..<Suc nC * nD} = {}"
        by (simp add: ivl_disj_int(2))
      show "\<forall>i\<in>{..<nC * nD} \<union> {nC * nD..<Suc nC * nD}.
       f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) \<in> fc_mats" 
        using fc smult_mem by blast        
    qed simp+
    ultimately show ?thesis by simp
  qed
  also have "... = 
    (Cp \<Otimes> D) + 
    sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) {nC*nD..< (Suc nC)*nD}"
  proof -
    have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC*nD} = Cp \<Otimes> D"
      unfolding Cp_def using Suc by simp
    thus ?thesis by simp
  qed
  also have "... = 
    (Cp \<Otimes> D) + 
    sum_mat (\<lambda>i. (f nC * g (i mod nD))\<cdot>\<^sub>m 
    ((A nC) \<Otimes> (B (i mod nD)))) {nC*nD..< (Suc nC)*nD}" 
  proof -
    have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {nC*nD..< (Suc nC)*nD} = 
      sum_mat (\<lambda>i. (f nC * g (i mod nD))\<cdot>\<^sub>m 
      ((A nC) \<Otimes> (B (i mod nD)))) {nC*nD..< (Suc nC)*nD}" 
    proof (rule sum_mat_cong)
      show "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow>
        f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) \<in> 
        fc_mats" using fc by (metis UnI2 smult_mem) 
      show "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow> 
        f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) \<in> fc_mats" 
      proof
        fix i
        assume "i \<in> {nC * nD..<Suc nC * nD}" 
        hence "i mod nD < nD" using Suc mod_less_divisor by blast 
        hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
        moreover have "A nC \<in> carrier_mat n n" using Suc by simp
        ultimately have "A nC \<Otimes> B (i mod nD) \<in> carrier_mat (n*m) (n*m)" 
          using tensor_mat_carrier by (metis carrier_matD(1) carrier_matD(2))
        hence "(A nC \<Otimes> B (i mod nD)) \<in> fc_mats"
            using Suc dim_eq fc_mats_carrier by blast 
        thus "f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) \<in> fc_mats"
          using smult_mem by blast
      qed simp
      show "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow>
        f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) =
        f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD))"
      proof -
        fix i
        assume "i \<in> {nC * nD..<Suc nC * nD}"
        hence "i div nD = nC"
          by (metis atLeastLessThan_iff div_nat_eqI mult.commute)
        thus "f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) =
          f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD))" by simp
      qed
    qed simp
    thus ?thesis by simp
  qed
  also have "... = 
    (Cp \<Otimes> D) + 
    sum_mat (\<lambda>i. (f nC \<cdot>\<^sub>m (A nC)) \<Otimes> (g (i mod nD)\<cdot>\<^sub>m (B (i mod nD)))) 
    {nC*nD..< (Suc nC)*nD}" 
  proof -
    have "sum_mat (\<lambda>i. f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD))) 
      {nC * nD..<Suc nC * nD} =
      sum_mat (\<lambda>i. f nC \<cdot>\<^sub>m A nC \<Otimes> g (i mod nD) \<cdot>\<^sub>m B (i mod nD)) 
      {nC * nD..<Suc nC * nD}" 
    proof (rule sum_mat_cong)
      show "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow> 
        f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) \<in> fc_mats" 
      proof -
        fix i
        assume "i \<in> {nC * nD..<Suc nC * nD}"
        have "i mod nD < nD" using Suc mod_less_divisor by blast
        hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
        moreover have "A nC \<in> carrier_mat n n" by (simp add: Suc(2))
        ultimately have "A nC \<Otimes> (B (i mod nD)) \<in> carrier_mat (n*m) (n*m)"
          using tensor_mat_carrier
          by (metis carrier_matD(1) carrier_matD(2))
        hence "A nC \<Otimes> B (i mod nD) \<in> fc_mats" using fc_mats_carrier
          Suc dim_eq by blast
        thus "f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) \<in> fc_mats"
          using cpx_sq_mat_smult by blast
      qed
      show "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow> 
        f nC \<cdot>\<^sub>m A nC \<Otimes> g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> fc_mats"
      proof -
        fix i
        assume "i \<in> {nC * nD..<Suc nC * nD}"
        have "i mod nD < nD" using Suc mod_less_divisor by blast
        hence "g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> carrier_mat m m" using Suc 
          by simp
        moreover have "f nC \<cdot>\<^sub>m A nC \<in> carrier_mat n n" by (simp add: Suc(2))
        ultimately have "f nC \<cdot>\<^sub>m A nC \<Otimes> g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> 
          carrier_mat (n*m) (n*m)"
          using tensor_mat_carrier
          by (metis carrier_matD(1) carrier_matD(2))
        thus "f nC \<cdot>\<^sub>m A nC \<Otimes> g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> fc_mats" 
          using fc_mats_carrier Suc dim_eq by blast
      qed
      show "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow>
        f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) =
        f nC \<cdot>\<^sub>m A nC \<Otimes> g (i mod nD) \<cdot>\<^sub>m B (i mod nD)" 
      proof -
        fix i
        assume "i \<in> {nC * nD..<Suc nC * nD}"
        show "f nC * g (i mod nD) \<cdot>\<^sub>m (A nC \<Otimes> B (i mod nD)) =
        f nC \<cdot>\<^sub>m A nC \<Otimes> g (i mod nD) \<cdot>\<^sub>m B (i mod nD)" using tensor_mat_smult
          by (metis div_eq_0_iff Suc(3) Suc(8) 
              Suc.prems(1) assms(5) assms(6) lessI mod_div_trivial)
      qed
    qed simp
    thus ?thesis by simp
  qed
  also have "... = 
    (Cp \<Otimes> D) +
    ((f nC \<cdot>\<^sub>m (A nC)) \<Otimes> (fixed_carrier_mat.sum_mat m m 
      (\<lambda>i. g (i mod nD)\<cdot>\<^sub>m (B (i mod nD))) 
    {nC*nD..< (Suc nC)*nD}))"
  proof -
    have "sum_mat (\<lambda>i. f nC \<cdot>\<^sub>m A nC \<Otimes> g (i mod nD) \<cdot>\<^sub>m B (i mod nD)) 
      {nC * nD..<Suc nC * nD} = 
      f nC \<cdot>\<^sub>m (A nC) \<Otimes> (fixed_carrier_mat.sum_mat m m 
        (\<lambda>i. g (i mod nD)\<cdot>\<^sub>m (B (i mod nD))) 
      {nC*nD..< (Suc nC)*nD})" 
    proof (rule tensor_mat_sum_mat_right[symmetric])
      show "0 < n" "0 < m" "dimR = n*m" using Suc by auto
      show "f nC \<cdot>\<^sub>m A nC \<in> carrier_mat n n" by (simp add: Suc(2))
      fix i
      assume "i \<in> {nC * nD..<Suc nC * nD}"
      have "i mod nD < nD" using Suc mod_less_divisor by blast
      hence "B (i mod nD) \<in> carrier_mat m m" using Suc by simp
      thus "g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> carrier_mat m m" by simp
    qed simp
    thus ?thesis by simp
  qed
  also have "... = 
    (Cp \<Otimes> D) +
    ((f nC \<cdot>\<^sub>m (A nC)) \<Otimes> (fixed_carrier_mat.sum_mat m m 
    (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD}))" 
  proof -
    have "fixed_carrier_mat.sum_mat m m (\<lambda>i. g (i mod nD) \<cdot>\<^sub>m B (i mod nD)) 
      {nC * nD..<Suc nC * nD} = 
      fixed_carrier_mat.sum_mat m m (\<lambda>i. g (i mod nD) \<cdot>\<^sub>m B (i mod nD)) 
      ((+) (nC * nD) ` {..<nD})" 
    proof (rule fixed_carrier_mat.sum_mat_cong')
      show "{nC * nD..<Suc nC * nD} = (+) (nC * nD) ` {..<nD}"
        by (simp add: lessThan_atLeast0)
      show "fixed_carrier_mat (carrier_mat m m) m m"
        by (simp add: fixed_carrier_mat.intro)
      show "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow> 
        g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> carrier_mat m m"
      proof -
        fix i
        assume "i \<in> {nC * nD..<Suc nC * nD}"
        hence "i mod nD < nD"
          using Suc mod_less_divisor by blast
        thus "g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> carrier_mat m m"
          using Suc(3) smult_carrier_mat by blast
      qed
      thus "\<And>i. i \<in> {nC * nD..<Suc nC * nD} \<Longrightarrow> 
        g (i mod nD) \<cdot>\<^sub>m B (i mod nD) \<in> carrier_mat m m" .
    qed simp+
    also have "... = 
      fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m B j) {..<nD}" 
    proof (rule fixed_carrier_mat.sum_mat_mod_eq)
      show "fixed_carrier_mat (carrier_mat m m) m m"
        by (simp add: fixed_carrier_mat.intro)
      show "\<And>x. x \<in> {..<nD} \<Longrightarrow> g x \<cdot>\<^sub>m B x \<in> carrier_mat m m"
        by (simp add: Suc(3))
    qed
    finally have "fixed_carrier_mat.sum_mat m m 
      (\<lambda>i. g (i mod nD) \<cdot>\<^sub>m B (i mod nD)) 
      {nC * nD..<Suc nC * nD} =
      fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m B j) {..<nD}" .
    thus ?thesis by simp
  qed
  also have "... = (Cp \<Otimes> D) + ((f nC \<cdot>\<^sub>m (A nC)) \<Otimes> D)" using Suc by simp
  also have "... = Cp + (f nC \<cdot>\<^sub>m (A nC)) \<Otimes> D" 
  proof (rule tensor_mat_add_left[symmetric])      
    show "Cp \<in> carrier_mat n n" unfolding Cp_def 
    proof (rule fixed_carrier_mat.sum_mat_carrier)
      show "\<And>i. i \<in> {..< nC} \<Longrightarrow> f i \<cdot>\<^sub>m A i \<in> carrier_mat n n"
        by (simp add: Suc(2))
      show "fixed_carrier_mat (carrier_mat n n) n n"
        by (simp add: fixed_carrier_mat.intro)
    qed
    have "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m B j) {..<nD} \<in>
      carrier_mat m m" 
    proof (rule fixed_carrier_mat.sum_mat_carrier)
      show "\<And>i. i \<in> {..< nD} \<Longrightarrow> g i \<cdot>\<^sub>m B i \<in> carrier_mat m m"
        by (simp add: Suc)
      show "fixed_carrier_mat (carrier_mat m m ) m m"
        by (simp add: fixed_carrier_mat.intro)
    qed
    thus "D \<in> carrier_mat m m" using Suc by simp
    show "f nC \<cdot>\<^sub>m A nC \<in> carrier_mat n n"
      by (simp add: Suc(2))
  qed (auto simp add: Suc)
  also have "... = 
    (fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< Suc nC}) \<Otimes> D"
  proof -
    have "Cp + f nC \<cdot>\<^sub>m A nC = f nC \<cdot>\<^sub>m A nC + Cp" 
    proof (rule comm_add_mat)
      show "f nC \<cdot>\<^sub>m A nC \<in> carrier_mat n n" by (simp add: Suc(2))
      show "Cp \<in> carrier_mat n n" unfolding Cp_def 
      proof (rule fixed_carrier_mat.sum_mat_carrier)
        show "\<And>i. i \<in> {..< nC} \<Longrightarrow> f i \<cdot>\<^sub>m A i \<in> carrier_mat n n"
          by (simp add: Suc(2))
        show "fixed_carrier_mat (carrier_mat n n) n n"
          by (simp add: fixed_carrier_mat.intro)
      qed
    qed
    also have "... = fixed_carrier_mat.sum_mat n n 
      (\<lambda>i. f i \<cdot>\<^sub>m (A i)) (insert nC {..< nC})" unfolding Cp_def 
    proof (rule fixed_carrier_mat.sum_mat_insert[symmetric])
      show "f nC \<cdot>\<^sub>m A nC \<in> carrier_mat n n"
        by (simp add: Suc(2))
      show "fixed_carrier_mat (carrier_mat n n) n n"
        by (simp add: fixed_carrier_mat.intro)
      show "(\<lambda>i. f i \<cdot>\<^sub>m A i) ` {..<nC} \<subseteq> carrier_mat n n"
      proof 
        fix x
        assume "x \<in> (\<lambda>i. f i \<cdot>\<^sub>m A i) ` {..<nC}"
        hence "\<exists>i \<in> {..<nC}. x = f i \<cdot>\<^sub>m A i" by auto
        from this obtain i where "i\<in> {..<nC}" and "x = f i \<cdot>\<^sub>m A i" by auto
        have "f i \<cdot>\<^sub>m A i \<in> carrier_mat n n"
          using Suc.prems(1) \<open>i \<in> {..<nC}\<close> by auto 
        thus "x \<in> carrier_mat n n" using \<open>x = f i \<cdot>\<^sub>m A i\<close> by simp
      qed
    qed auto
    also have "... = fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) 
      {..< Suc nC}"
    proof (rule fixed_carrier_mat.sum_mat_cong')
      show "fixed_carrier_mat (carrier_mat n n) n n"
        by (simp add: fixed_carrier_mat.intro)
      show "insert nC {..<nC} = {..<Suc nC}"
        by (simp add: lessThan_Suc)
      show "\<And>i. i \<in> insert nC {..<nC} \<Longrightarrow> f i \<cdot>\<^sub>m A i \<in> carrier_mat n n"
        by (simp add: Suc(2) \<open>insert nC {..<nC} = {..<Suc nC}\<close>)
      thus "\<And>i. i \<in> insert nC {..<nC} \<Longrightarrow> f i \<cdot>\<^sub>m A i \<in> carrier_mat n n" .
    qed auto
    finally have "Cp + f nC \<cdot>\<^sub>m A nC = fixed_carrier_mat.sum_mat n n 
      (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< Suc nC}" .
    thus ?thesis by simp
  qed
  also have "... = C\<Otimes> D" using Suc by simp
  finally show ?case .
qed

lemma tensor_mat_sum_nat_mod_div_eq_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  and "nD = 0"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD)))) 
  {..< nC*nD} = C\<Otimes> D"
proof -
  have "D = fixed_carrier_mat.sum_mat m m (\<lambda>i. g i \<cdot>\<^sub>m (B i)) {}" 
    using assms by auto
  also have "... =  0\<^sub>m m m" 
    using fixed_carrier_mat.sum_mat_empty[of _ m m "\<lambda>i. g i \<cdot>\<^sub>m (B i)"]
    by (simp add: fixed_carrier_mat_def)
  finally have "D = 0\<^sub>m m m" .
  moreover have "C \<in> carrier_mat n n" using assms
    fixed_carrier_mat.sum_mat_carrier[of _ n n "{..< nC}" "\<lambda>j. f j \<cdot>\<^sub>m (A j)"]
    by (simp add: fixed_carrier_mat_def)
  ultimately have "C\<Otimes> D = 0\<^sub>m (n*m) (n*m)" using tensor_mat_zero'
    by (simp add: assms)
  have "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) 
    {..< nC*nD} = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) {}" using assms by simp
  also have "... = 0\<^sub>m (n*m) (n*m)" using sum_mat_empty
    using assms(7) dim_eq by blast
  also have "... = C\<Otimes> D" using \<open>C\<Otimes> D = 0\<^sub>m (n*m) (n*m)\<close> by simp
  finally show ?thesis .
qed

lemma tensor_mat_sum_nat_mod_div:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  and "dimR = n *m"
shows "sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
  ((A (i div nD)) \<Otimes> (B (i mod nD)))) 
  {..< nC*nD} = C\<Otimes> D"
proof (cases "nD = 0")
  case True
  then show ?thesis using assms 
      tensor_mat_sum_nat_mod_div_eq_0[OF assms(1) assms(3)] by simp
next
  case False
  then show ?thesis using assms tensor_mat_sum_nat_mod_div_ne_0 by simp
qed

end
  
lemma tensor_mat_sum_mult_trace_expand_ne_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "R \<in> carrier_mat (n*m) (n*m)"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  and "nD \<noteq> 0"
  shows "sum (\<lambda>i. Complex_Matrix.trace ((f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD} = 
    Complex_Matrix.trace ((C \<Otimes> D) * R)" 
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat (n*m) (n*m)"
  interpret cpx_sq_mat "n*m" "n*m" fc  
  proof 
    show "0 < n*m" using assms by simp
  qed (auto simp add: fc_def)
  have fc: "\<forall>i\<in>{..<nC * nD}.
    f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) \<in> fc" 
  proof
    fix i
    assume "i \<in> {..<nC * nD}"
    hence "i div nD <  nC"
      by (simp add: less_mult_imp_div_less) 
    hence "A (i div nD) \<in> carrier_mat n n" using assms by simp
    have "i mod nD < nD" using assms by simp 
    hence "B (i mod nD) \<in> carrier_mat m m" using assms by simp
    hence "A (i div nD) \<Otimes> B (i mod nD) \<in> carrier_mat (n*m) (n*m)" 
      using tensor_mat_carrier
      by (metis \<open>A (i div nD) \<in> carrier_mat n n\<close> 
          carrier_matD(1) carrier_matD(2))
    hence "(A (i div nD) \<Otimes> B (i mod nD)) \<in> fc"
      using assms dim_eq fc_mats_carrier by blast 
    thus "f (i div nD) * g (i mod nD) \<cdot>\<^sub>m(A (i div nD) \<Otimes> B (i mod nD)) \<in> fc"
      using smult_mem by blast
  qed
  have "sum_mat (\<lambda>i. ((f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD} = 
    (sum_mat (\<lambda>i. f (i div nD) * g (i mod nD)\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC * nD}) * R"
  proof (rule sum_mat_distrib_right)
    show "R\<in> fc" using assms unfolding fc_def by simp
  qed (auto simp add: fc assms)
  also have "... = (C \<Otimes> D) * R"
  proof -
    have "sum_mat (\<lambda>i. f (i div nD) * g (i mod nD)\<cdot>\<^sub>m 
      ((A (i div nD)) \<Otimes> (B (i mod nD)))) {..< nC * nD} = C \<Otimes> D"
      using tensor_mat_sum_nat_mod_div assms by simp
    thus ?thesis by simp
  qed
  finally have sr: "sum_mat (\<lambda>i. ((f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD} = (C \<Otimes> D) * R" .
  have "sum (\<lambda>i. Complex_Matrix.trace ((f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD} = 
    Complex_Matrix.trace (sum_mat (\<lambda>i. ((f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD})"
  proof (rule trace_sum_mat[symmetric])
    show "\<And>i. i \<in> {..<nC * nD} \<Longrightarrow>
      f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) * R \<in> fc"
      using fc assms cpx_sq_mat_mult fc_def by blast 
  qed simp
  also have "... = Complex_Matrix.trace ((C \<Otimes> D) * R)" using sr by simp
  finally show ?thesis .
qed

lemma tensor_mat_sum_mult_trace_expand_eq_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "R \<in> carrier_mat (n*m) (n*m)"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  and "nD = 0"
  shows "sum (\<lambda>i. Complex_Matrix.trace ((f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD} = 
    Complex_Matrix.trace ((C \<Otimes> D) * R)" 
proof -
  have "D = 0\<^sub>m m m" using assms fixed_carrier_mat.sum_mat_empty
    fixed_carrier_mat.intro by fastforce
  hence "C \<Otimes> D = C \<Otimes> (0\<^sub>m m m)" by simp
  also have "... = 0\<^sub>m (n*m) (n*m)" 
  proof (rule tensor_mat_zero')
    have "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m A i) {..<nC} \<in> 
      carrier_mat n n" 
    proof (rule fixed_carrier_mat.sum_mat_carrier)
      show "fixed_carrier_mat (carrier_mat n n) n n"
        by (simp add: fixed_carrier_mat.intro)
      show "\<And>i. i \<in> {..<nC} \<Longrightarrow> f i \<cdot>\<^sub>m A i \<in> carrier_mat n n" using assms
        by simp
    qed 
    thus "C\<in> carrier_mat n n" using assms by simp
  qed (simp add: assms)+
  finally have "C \<Otimes> D = 0\<^sub>m (n*m) (n*m)" .
  hence "(C \<Otimes> D) * R = 0\<^sub>m (n*m) (n*m)"
    by (simp add: assms left_mult_zero_mat)
  hence "Complex_Matrix.trace ((C \<Otimes> D) * R) = 0" by simp
  moreover have "sum (\<lambda>i. Complex_Matrix.trace ((f (i div nD)*g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD} = 0" 
    using assms by simp
  ultimately show ?thesis by simp
qed

lemma tensor_mat_sum_mult_trace_expand:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "R \<in> carrier_mat (n*m) (n*m)"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  shows "sum (\<lambda>i. Complex_Matrix.trace ((f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD))) * R)) {..< nC * nD} = 
    Complex_Matrix.trace ((C \<Otimes> D) * R)" 
proof (cases "nD = 0")
  case True
  then show ?thesis 
    using assms tensor_mat_sum_mult_trace_expand_eq_0[OF assms(1)] by simp
next
  case False
  then show ?thesis 
    using assms tensor_mat_sum_mult_trace_expand_ne_0[OF assms(1) assms(2)] 
    by simp
qed

lemma tensor_mat_sum_mult_trace_ne_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "R \<in> carrier_mat (n*m) (n*m)"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  and "0 \<noteq> nD"
  shows "sum (\<lambda>i. (sum (\<lambda>j. Complex_Matrix.trace ((f i * g j)\<cdot>\<^sub>m 
    ((A i) \<Otimes> (B j)) * R)) {..< nD})) {..< nC} = 
    Complex_Matrix.trace ((C \<Otimes> D) * R)" 
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat (n*m) (n*m)"
  interpret cpx_sq_mat "n*m" "n*m" fc  
  proof 
    show "0 < n*m" using assms by simp
  qed (auto simp add: fc_def)
  have "sum (\<lambda>i. (sum (\<lambda>j. Complex_Matrix.trace ((f i * g j)\<cdot>\<^sub>m 
    ((A i) \<Otimes> (B j)) * R)) {..< nD})) {..< nC} = 
    sum (\<lambda>i. Complex_Matrix.trace (sum_mat (\<lambda>j. (f i * g j)\<cdot>\<^sub>m 
    ((A i) \<Otimes> (B j)) * R) {..< nD})) {..< nC}"
  proof (rule sum.cong)
    fix x
    assume "x \<in> {..< nC}"
    hence "A x \<in> carrier_mat n n" using assms by simp
    show "(\<Sum>j\<in> {..< nD}. Complex_Matrix.trace (f x * g j \<cdot>\<^sub>m (A x \<Otimes> B j) * R))=
         Complex_Matrix.trace (sum_mat (\<lambda>j. f x * g j \<cdot>\<^sub>m (A x \<Otimes> B j) * R) 
          {..<nD})" 
    proof (rule trace_sum_mat[symmetric])
      fix j
      assume "j \<in> {..< nD}"
      hence "B j \<in> carrier_mat m m" using assms by simp
      hence "A x \<Otimes> B j \<in> carrier_mat (n*m) (n*m)" 
        using tensor_mat_carrier
        by (metis \<open>A x \<in> carrier_mat n n\<close> carrier_matD(1) carrier_matD(2))
      hence "A x \<Otimes> B j \<in> fc"
        using assms dim_eq fc_mats_carrier by blast 
      thus "f x * g j \<cdot>\<^sub>m(A x \<Otimes> B j)*R \<in> fc"
        using smult_mem assms(3) cpx_sq_mat_mult fc_def by blast
    qed simp
  qed simp
  also have "... = Complex_Matrix.trace (sum_mat (\<lambda>i. 
    (sum_mat (\<lambda>j. (f i * g j)\<cdot>\<^sub>m ((A i) \<Otimes> (B j)) * R) {..< nD})) {..< nC})"
  proof (rule trace_sum_mat[symmetric])
    fix x
    assume "x\<in>{..< nC}"
    hence "A x\<in> carrier_mat n n" using assms by simp
    show "sum_mat (\<lambda>j. f x * g j \<cdot>\<^sub>m (A x \<Otimes> B j) * R) {..<nD} \<in> fc" 
      unfolding fc_def
    proof (rule sum_mat_carrier)
      fix j
      assume "j\<in> {..< nD}"
      hence "B j \<in> carrier_mat m m" using assms by simp
      hence "A x \<Otimes> B j \<in> carrier_mat (n*m) (n*m)" 
        using tensor_mat_carrier
        by (metis \<open>A x \<in> carrier_mat n n\<close> carrier_matD(1) carrier_matD(2))
      hence "A x \<Otimes> B j \<in> fc"
        using assms dim_eq fc_mats_carrier by blast 
      thus "f x * g j \<cdot>\<^sub>m(A x \<Otimes> B j)*R \<in> fc"
        using smult_mem assms(3) cpx_sq_mat_mult fc_def by blast
    qed 
  qed simp
  also have "... = Complex_Matrix.trace 
    (sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))*R) {..< nC*nD})" 
  proof -
    have "sum_mat (\<lambda>i. sum_mat (\<lambda>j. f i * g j \<cdot>\<^sub>m (A i \<Otimes> B j) * R) {..<nD}) 
      {..<nC} = sum_mat (\<lambda>i. (f (i div nD) * g (i mod nD))\<cdot>\<^sub>m 
    ((A (i div nD)) \<Otimes> (B (i mod nD)))*R) {..< nC*nD}" 
      by (rule sum_sum_mat_expand, (auto simp add: assms))
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>i<nC * nD.
      Complex_Matrix.trace
       (f (i div nD) * g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD)) * R))"
  proof (rule trace_sum_mat)
    fix i
    assume "i \<in> {..<nC * nD}"
    hence "i div nD <  nC"
      by (simp add: less_mult_imp_div_less) 
    hence "A (i div nD) \<in> carrier_mat n n" using assms by simp
    have "i mod nD < nD" using assms by simp 
    hence "B (i mod nD) \<in> carrier_mat m m" using assms by simp
    hence "A (i div nD) \<Otimes> B (i mod nD) \<in> carrier_mat (n*m) (n*m)" 
      using tensor_mat_carrier
      by (metis \<open>A (i div nD) \<in> carrier_mat n n\<close> 
          carrier_matD(1) carrier_matD(2))
    hence "(A (i div nD) \<Otimes> B (i mod nD)) \<in> fc"
      using assms dim_eq fc_mats_carrier by blast 
    hence "f (i div nD) * g (i mod nD) \<cdot>\<^sub>m(A (i div nD) \<Otimes> B (i mod nD)) \<in> fc"
      using smult_mem by blast
    thus "f (i div nD)*g (i mod nD) \<cdot>\<^sub>m (A (i div nD) \<Otimes> B (i mod nD))*R \<in> fc"
      using assms(3) cpx_sq_mat_mult fc_mats_carrier by blast
  qed simp
  also have "... = Complex_Matrix.trace ((C \<Otimes> D) * R)" 
  proof (rule tensor_mat_sum_mult_trace_expand)
    show "\<And>k. k < nC \<Longrightarrow> A k \<in> carrier_mat n n" using assms by simp
    show "\<And>j. j < nD \<Longrightarrow> B j \<in> carrier_mat m m" using assms by simp
  qed (auto simp add: assms)
  finally show ?thesis .
qed

lemma tensor_mat_sum_mult_trace_eq_0:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "R \<in> carrier_mat (n*m) (n*m)"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  and "0 = (nD::nat)"
  shows "sum (\<lambda>i. (sum (\<lambda>j. Complex_Matrix.trace ((f i * g j)\<cdot>\<^sub>m 
    ((A i) \<Otimes> (B j)) * R)) {..< nD})) {..< nC} = 
    Complex_Matrix.trace ((C \<Otimes> D) * R)" 
proof -
  define fc::"complex Matrix.mat set" where "fc = carrier_mat (n*m) (n*m)"
  interpret cpx_sq_mat "n*m" "n*m" fc  
  proof 
    show "0 < n*m" using assms by simp
  qed (auto simp add: fc_def)
  have "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {} = 0\<^sub>m m m"
    using assms fixed_carrier_mat.sum_mat_empty[of _ m m ]
    fixed_carrier_mat.intro by fastforce
  hence "D = 0\<^sub>m m m" using assms by simp
  hence "C \<Otimes> D = C \<Otimes> (0\<^sub>m m m)" by simp
  also have "... = 0\<^sub>m (n*m) (n*m)" 
  proof (rule tensor_mat_zero')
    have "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m A i) {..<nC} \<in> 
      carrier_mat n n" 
    proof (rule fixed_carrier_mat.sum_mat_carrier)
      show "fixed_carrier_mat (carrier_mat n n) n n"
        by (simp add: fixed_carrier_mat.intro)
      show "\<And>i. i \<in> {..<nC} \<Longrightarrow> f i \<cdot>\<^sub>m A i \<in> carrier_mat n n" using assms
        by simp
    qed 
    thus "C\<in> carrier_mat n n" using assms by simp
    show "0<n" "0<m" using assms by auto
  qed 
  finally have "C \<Otimes> D = 0\<^sub>m (n*m) (n*m)" .
  hence "(C \<Otimes> D) * R = 0\<^sub>m (n*m) (n*m)"
    by (simp add: assms left_mult_zero_mat)
  hence 1: "Complex_Matrix.trace ((C \<Otimes> D) * R) = 0" by simp
  have "\<And>i. i\<in>{..< nC} \<Longrightarrow> sum (\<lambda>j. Complex_Matrix.trace ((f i * g j)\<cdot>\<^sub>m 
    ((A i) \<Otimes> (B j)) * R)) {..< nD} = 0"
  proof -
    fix i
    assume "i\<in> {..< nC}"
    show "sum (\<lambda>j. Complex_Matrix.trace ((f i * g j)\<cdot>\<^sub>m 
      ((A i) \<Otimes> (B j)) * R)) {..< nD} = 0" using assms by simp
  qed
  hence "sum (\<lambda>i. (sum (\<lambda>j. Complex_Matrix.trace ((f i * g j)\<cdot>\<^sub>m 
    ((A i) \<Otimes> (B j)) * R)) {..< nD})) {..< nC} = 0" by simp
  thus ?thesis using 1 by simp
qed

lemma tensor_mat_sum_mult_trace:
  assumes "\<And>k. k < (nC::nat) \<Longrightarrow> A k \<in> carrier_mat n n"
  and "\<And>j. j < (nD::nat) \<Longrightarrow> B j \<in> carrier_mat m m"
  and "R \<in> carrier_mat (n*m) (n*m)"
  and "fixed_carrier_mat.sum_mat n n (\<lambda>i. f i \<cdot>\<^sub>m (A i)) {..< nC} = C"
  and "fixed_carrier_mat.sum_mat m m (\<lambda>j. g j \<cdot>\<^sub>m (B j)) {..< nD} = D"
  and "0 < n"
  and "0 < m"
  shows "sum (\<lambda>i. (sum (\<lambda>j. Complex_Matrix.trace ((f i * g j)\<cdot>\<^sub>m 
    ((A i) \<Otimes> (B j)) * R)) {..< nD})) {..< nC} = 
    Complex_Matrix.trace ((C \<Otimes> D) * R)" 
proof (cases "nD = 0")
  case True
  then show ?thesis using assms tensor_mat_sum_mult_trace_eq_0[OF assms(1)] 
    by simp
next
  case False
  then show ?thesis 
    using assms tensor_mat_sum_mult_trace_ne_0[OF assms(1) assms(2)] by simp
qed

lemma tensor_mat_make_pm_mult_trace:
  assumes "A \<in> carrier_mat n n"
  and "hermitian A"
  and "B\<in> carrier_mat m m"
  and "hermitian B"
  and "R \<in> carrier_mat (n*m) (n*m)"
  and "(nA, M) = cpx_sq_mat.make_pm n n A"
  and "(nB, N) = cpx_sq_mat.make_pm m m B"
  and "0 < n"
  and "0 < m"
shows "sum (\<lambda>i. (sum (\<lambda>j. Complex_Matrix.trace 
    ((complex_of_real (meas_outcome_val (M i)) * 
    complex_of_real (meas_outcome_val (N j)))\<cdot>\<^sub>m 
    ((meas_outcome_prj (M i)) \<Otimes> (meas_outcome_prj (N j))) * R)) {..< nB})) 
    {..< nA} = 
    Complex_Matrix.trace ((A \<Otimes> B) * R)" 
proof (rule tensor_mat_sum_mult_trace)
  have A: "cpx_sq_mat.proj_measurement n n (carrier_mat n n) nA M" 
  proof (rule cpx_sq_mat.make_pm_proj_measurement)
    show "A \<in> carrier_mat n n" using assms by simp
    show "cpx_sq_mat n n (carrier_mat n n)"
      by (simp add: assms cpx_sq_mat.intro cpx_sq_mat_axioms.intro 
          fixed_carrier_mat_def)
  qed (auto simp add: assms)
  have B: "cpx_sq_mat.proj_measurement m m (carrier_mat m m) nB N" 
  proof (rule cpx_sq_mat.make_pm_proj_measurement)
    show "B \<in> carrier_mat m m" using assms by simp
    show "cpx_sq_mat m m (carrier_mat m m)"
      by (simp add: assms cpx_sq_mat.intro cpx_sq_mat_axioms.intro 
          fixed_carrier_mat_def)
  qed (auto simp add: assms)
  show "\<And>k. k < nA \<Longrightarrow> meas_outcome_prj (M k) \<in> carrier_mat n n"
  proof -
    fix k
    assume "k < nA"
    show "meas_outcome_prj (M k) \<in> carrier_mat n n" 
      using cpx_sq_mat.proj_measurement_carrier
      by (meson A \<open>k < nA\<close> assms(8) cpx_sq_mat_axioms.intro cpx_sq_mat_def 
          fixed_carrier_mat.intro)
  qed
  show "\<And>k. k < nB \<Longrightarrow> meas_outcome_prj (N k) \<in> carrier_mat m m"
  proof -
    fix k
    assume "k < nB"
    show "meas_outcome_prj (N k) \<in> carrier_mat m m" 
      using cpx_sq_mat.proj_measurement_carrier
      by (meson B \<open>k < nB\<close> assms(9) cpx_sq_mat_axioms.intro cpx_sq_mat_def 
          fixed_carrier_mat.intro)
  qed
  show "fixed_carrier_mat.sum_mat n n 
    (\<lambda>i. complex_of_real (meas_outcome_val (M i)) \<cdot>\<^sub>m meas_outcome_prj (M i)) 
    {..<nA} = A"
  proof (rule cpx_sq_mat.make_pm_sum)
    show "cpx_sq_mat n n (carrier_mat n n)"
      by (simp add: assms cpx_sq_mat.intro cpx_sq_mat_axioms.intro 
          fixed_carrier_mat_def)
  qed (auto simp add: assms)
  show "fixed_carrier_mat.sum_mat m m
    (\<lambda>i. complex_of_real (meas_outcome_val (N i)) \<cdot>\<^sub>m meas_outcome_prj (N i)) 
    {..<nB} = B"
  proof (rule cpx_sq_mat.make_pm_sum)
    show "cpx_sq_mat m m (carrier_mat m m)"
      by (simp add: assms cpx_sq_mat.intro cpx_sq_mat_axioms.intro 
          fixed_carrier_mat_def)
  qed (auto simp add: assms)
qed (auto simp add: assms)

lemma tensor_mat_mat_conj:
  assumes "A\<in> carrier_mat n n"
  and "B \<in> carrier_mat n n"
  and "U \<in> carrier_mat n n"
  and "C\<in> carrier_mat m m"
  and "D \<in> carrier_mat m m"
  and "V \<in> carrier_mat m m"
  and "0 < n"
  and "0 < m"
  and "A = mat_conj U B"
  and "C = mat_conj V D"
shows "A \<Otimes> C = mat_conj (U \<Otimes> V) (B \<Otimes> D)" 
proof -
  have "A \<Otimes> C = (U * B * Complex_Matrix.adjoint U) \<Otimes> 
    (V * D * Complex_Matrix.adjoint V)" using assms unfolding mat_conj_def 
    by simp
  also have "... = (U*B \<Otimes> (V*D)) * 
    (Complex_Matrix.adjoint U \<Otimes> Complex_Matrix.adjoint V)" 
    using mult_distr_tensor assms by simp
  also have "... = (U \<Otimes> V) * (B \<Otimes> D) * Complex_Matrix.adjoint (U \<Otimes> V)"
    using mult_distr_tensor assms
    by (metis carrier_matD(1) carrier_matD(2) tensor_mat_adjoint)
  finally show ?thesis unfolding mat_conj_def by simp
qed

lemma unitarily_equiv_mat_conj[simp]:
  assumes "unitarily_equiv A B U"
  shows "A = mat_conj U B" unfolding mat_conj_def
  by (simp add: assms unitarily_equiv_eq)

lemma hermitian_tensor_mat_decomp:
  assumes "A\<in> carrier_mat n n"
  and "C\<in> carrier_mat m m"
  and "unitary_diag A B U"
  and "unitary_diag C D V"
  and "0 < n"
  and "0 < m"
shows "unitary_diag (A \<Otimes> C) (B \<Otimes> D) (U \<Otimes> V)"
proof (rule unitary_diagI')
  show "A \<Otimes> C \<in> carrier_mat (n *m) (n*m)" using assms
    by (metis carrier_matD(1) carrier_matD(2) tensor_mat_carrier)
  show "B \<Otimes> D \<in> carrier_mat (n * m) (n * m)" using assms
    by (metis (no_types, opaque_lifting)  carrier_matD(1) 
        carrier_matD(2) carrier_mat_triv dim_col_tensor_mat 
        dim_row_tensor_mat unitary_diag_carrier(1))
  show "Complex_Matrix.unitary (U \<Otimes> V)"
    by (metis Complex_Matrix.unitary_def assms(3) assms(4) 
        carrier_matD(2) carrier_mat_triv dim_col_tensor_mat dim_row_tensor_mat 
        nat_0_less_mult_iff tensor_mat_unitary unitary_diagD(3) unitary_zero 
        zero_order(5))
  show "diagonal_mat (B \<Otimes> D)" using tensor_mat_diagonal
    by (meson assms(3) assms(4) unitarily_equiv_carrier'(2) unitary_diagD(2) 
        unitary_diag_imp_unitarily_equiv)
  show "A \<Otimes> C = mat_conj (U \<Otimes> V) (B \<Otimes> D)" 
  proof (rule tensor_mat_mat_conj[of _ n _ _ _ m])
    show "B\<in> carrier_mat n n"
      using assms(1) assms(3) unitary_diag_carrier(1) by auto
    show "D \<in> carrier_mat m m"
      using assms unitary_diag_carrier(1) by auto
    show "U \<in> carrier_mat n n"
      using assms(1) assms(3) unitary_diag_carrier(2) by blast
    show "V \<in> carrier_mat m m"
      using assms unitary_diag_carrier(2) by blast
  qed (auto simp add: assms)
qed

end