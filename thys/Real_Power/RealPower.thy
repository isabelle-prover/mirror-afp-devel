(*  Title:      RealPower/RealPower.thy
    Authors:    Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)

section \<open>Real Exponents via Limits\<close>

theory RealPower
imports RatPower
begin

instance rat :: ab_group_add 
by intro_classes

instance rat :: field
by intro_classes

instance rat :: comm_ring_1
by intro_classes

instantiation rat :: dist
begin
definition rat_dist_def:
  "dist x y = of_rat (abs(y - x))"

instance ..
end

instantiation rat :: dist_norm
begin
definition rat_norm_def:
  "norm (q::rat) = of_rat \<bar>q\<bar>"

instance
by intro_classes (simp add: rat_dist_def rat_norm_def)
end

instantiation rat :: metric_space
begin

definition uniformity_rat_def [code del]:
  "(uniformity :: (rat \<times> rat) filter) = 
      (INF e\<in>{0 <..}. principal {((x::rat), y). dist x y < e})"

definition open_rat_def [code del]:
  "open (U :: rat set) \<longleftrightarrow> 
      (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance 
proof 
  show "uniformity = 
         (INF e\<in>{0<..}. principal {(x::rat, y). dist x y < e})"
    using uniformity_rat_def by blast
next
  fix U 
  show "open U = 
         (\<forall>x\<in>U. \<forall>\<^sub>F (x', y::rat) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    using open_rat_def by blast
next
  fix x y show "(dist x y = 0) = (x = (y::rat))"
    by (force simp add: rat_dist_def)
next
  fix x y z show "dist x y \<le> dist x z + dist y (z::rat)"
    by (force simp add: rat_dist_def of_rat_add [symmetric] of_rat_less_eq)
qed

end

instance rat :: topological_space
by intro_classes

lemma LIMSEQ_squeeze: 
  assumes abc: "\<forall>n. a n \<le> b n \<and> b n \<le> c n" 
  and alim: "a \<longlonglongrightarrow> (L::real)" 
  and clim: "c \<longlonglongrightarrow> L" shows "b \<longlonglongrightarrow> L"
proof -
  {fix r
  assume r0: "(r::real) > 0" 
  then have "\<exists>no. \<forall>n\<ge>no. \<bar>a n - L\<bar> < r"
    by (metis LIMSEQ_def alim dist_real_def)
  then obtain p where 1: "\<forall>n\<ge>p. \<bar>a n - L\<bar> < r" by blast
  have "\<exists>no. \<forall>n\<ge>no. \<bar>c n - L\<bar> < r"
     by (metis LIMSEQ_def r0 clim dist_real_def)
  then obtain k where 2: "\<forall>n\<ge>k. \<bar>c n - L\<bar> < r" by blast
  have  "\<exists>m. \<forall>n\<ge>m. \<bar>b n - L\<bar> < r"  
  proof -
    {fix n 
      assume n_max: "max p k \<le> n"
      then have a_n: "\<bar>a n - L\<bar> < r" using 1 by simp
      have c_n: "\<bar>c n - L\<bar> < r" using n_max 2 by simp 
      have "a n \<le> b n \<and> b n \<le> c n" using abc by simp
      then have "\<bar>b n - L\<bar> < r" 
        using a_n c_n by linarith
    }
    then have "\<forall>n\<ge>max p k. \<bar>b n - L\<bar> < r"
       by blast
     then show ?thesis by blast
  qed
  }
  then have "\<forall>r>0. \<exists>m. \<forall>n\<ge>m. \<bar>b n - L\<bar> < r" 
    by blast
  then show ?thesis
    by (simp add: dist_real_def lim_sequentially) 
qed

primrec incratseq :: "real \<Rightarrow> nat \<Rightarrow> rat" where
  "incratseq x 0 = (\<some>q. x - 1 < of_rat q \<and> of_rat q < x)"
| "incratseq x (Suc n) = 
       (\<some>q. max (of_rat(incratseq x n)) (x - 1/(n + 2)) < of_rat q \<and> 
            of_rat q < x)"

lemma incratseq_0_gt [simp]: "x - 1 < of_rat(incratseq x 0)"
proof -
  have "x - 1 < x" by simp
  then have "\<exists>q. x - 1 < real_of_rat q \<and> real_of_rat q < x" 
    using of_rat_dense
    by blast
  then obtain q where " x - 1 < real_of_rat q \<and> real_of_rat q < x" 
    by force
  then show ?thesis 
    by (auto intro: someI2) 
qed

lemma incratseq_0_less [simp]: "of_rat(incratseq x 0) < x"
proof -
  have "x - 1 < x" by simp
  then have "\<exists>q. x - 1 < real_of_rat q \<and> real_of_rat q < x" 
    using of_rat_dense
    by blast
  then obtain q where " x - 1 < real_of_rat q \<and> real_of_rat q < x" 
    by force
  then show ?thesis 
    by (auto intro: someI2) 
qed

declare incratseq.simps [simp del]

lemma incratseq_ub [simp]: 
  "real_of_rat (incratseq x n) < x"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case 
  proof (cases "real_of_rat (incratseq x n) \<le> x - 1/(n + 2)")
    case True
    then have "x - 1/(Suc(Suc n)) < x" by simp
    then have "\<exists>q. x - 1 / real (Suc (Suc n))
              < real_of_rat q \<and>
              real_of_rat q < x"
      using of_rat_dense by blast
      
    then have "\<exists>a. (if True then x - 1 / real (n + 2)
                  else real_of_rat
                        (incratseq x n))
                 < real_of_rat a \<and>
                 real_of_rat a < x"
      by auto 
    then have "real_of_rat
              (SOME q.
                  (if real_of_rat
                       (incratseq x n)
                      \<le> x - 1 / real (n + 2)
                   then x - 1 / real (n + 2)
                   else real_of_rat
                         (incratseq x n))
                  < real_of_rat q \<and>
                  real_of_rat q < x)
             < x"
      using True by (fastforce intro: someI2_ex) 
    then show ?thesis 
      by (auto simp only: incratseq.simps max_def)
  next
    case False
    then have "\<exists>a. real_of_rat (incratseq x n)
                 < real_of_rat a \<and>
                 real_of_rat a < x"
      using Suc of_rat_dense by auto
    then have "real_of_rat
              (SOME q.
                  (if real_of_rat
                       (incratseq x n)
                      \<le> x - 1 / real (n + 2)
                   then x - 1 / real (n + 2)
                   else real_of_rat
                         (incratseq x n))
                  < real_of_rat q \<and>
                  real_of_rat q < x)
             < x"
      using False by (fastforce intro: someI2_ex) 
  then show ?thesis 
    by (simp only: incratseq.simps max_def)
  qed
qed


lemma incratseq_incseq [simp]: 
   "incratseq x n < incratseq x (Suc n)"
proof -
  have "max (real_of_rat (incratseq x n)) (x - 1 / real (n + 2)) < x"
    by simp 
   then have "\<exists>q. max (real_of_rat (incratseq x n))
          (x - 1 / real (n + 2))
         < real_of_rat q \<and>
         real_of_rat q < x"
     using of_rat_dense by blast
   then have "incratseq x n
    < (SOME q.
          max (real_of_rat (incratseq x n))
           (x - 1 / real (n + 2))
          < real_of_rat q \<and>
          real_of_rat q < x)"
     by (fastforce intro: someI2_ex simp add: of_rat_less)
   then show ?thesis 
     by (simp only: incratseq.simps)
 qed

lemma incratseq_lb [simp]: "x - 1/(Suc n) < real_of_rat (incratseq x n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases "real_of_rat (incratseq x n) \<le> x - 1/Suc(Suc n)")
    case True
    then have " 1 / Suc(Suc n) < 1 / Suc n"
      using Suc.IH by auto
     have "x - 1/Suc(Suc n) < x"
      by simp
    then have "\<exists>a. x - 1 /Suc(Suc n) < real_of_rat a \<and> real_of_rat a < x"
      using of_rat_dense by blast 
    then have "x - 1 / real (Suc (Suc n))
             < real_of_rat
                (SOME q.
                    (if real_of_rat (incratseq x n) \<le> x - 1 / Suc(Suc n)
                     then x - 1 / Suc(Suc n) else real_of_rat (incratseq x n))
                    < real_of_rat q \<and>
                    real_of_rat q < x)"
      using True by (auto intro: someI2_ex)
    then show ?thesis using True 
      by (auto simp add: incratseq.simps(2) max_def)
  next
    case False
    then show ?thesis
      using incratseq_incseq 
      by (meson less_trans not_less of_rat_less) 
  qed
qed

lemma incseq_incratseq [simp]: 
   "incseq (incratseq x)"
by (auto intro!: incseq_SucI less_imp_le)


lemma LIMSEQ_rat_real_ex: 
    "\<exists>r. incseq r \<and> (\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real)"
proof -
  have squeeze_left:
       "\<forall>n. x - 1 / real (Suc n)
        \<le> real_of_rat (incratseq x n) \<and> real_of_rat (incratseq x n) \<le> x"
    using incratseq_lb less_imp_le
    by (simp add: less_imp_le) 
  moreover have "(\<lambda>n. x - 1 / real (Suc n)) \<longlonglongrightarrow> x"
    by (simp only: minus_real_def LIMSEQ_inverse_real_of_nat_add_minus 
           inverse_eq_divide [symmetric])
  ultimately have "(\<lambda>n. real_of_rat (incratseq x n)) \<longlonglongrightarrow> x"
    using  LIMSEQ_squeeze tendsto_const by fastforce
  then show ?thesis 
    using incseq_incratseq by blast 
qed
 
lemma incseq_incseq_powrat: 
     "\<lbrakk> 1 \<le> a; incseq r \<rbrakk> \<Longrightarrow> incseq (\<lambda>n. a pow\<^sub>\<rat> (r n))"
by (metis (lifting) incseq_def powrat_le_mono)

lemma ex_less_of_rat: "\<exists>r. (x :: 'a :: archimedean_field) < of_rat r"
  using ex_less_of_int of_rat_of_int_eq by metis  

lemma powrat_incseq_bounded: 
     "\<lbrakk> 1 \<le> a; \<forall>n. r n < of_rat q; incseq r \<rbrakk> \<Longrightarrow>  a pow\<^sub>\<rat> (r n) \<le> a pow\<^sub>\<rat> q"
  by (simp add: less_imp_le powrat_le_mono)

lemma Bseq_powrat_incseq: 
  assumes "1 \<le> a" 
  and "incseq r" 
  and "\<forall>n. of_rat(r n) \<le> (x :: 'a :: archimedean_field)" 
  shows "Bseq (\<lambda>n. a pow\<^sub>\<rat> (r n))"
proof -
  from ex_less_of_rat 
  obtain q where xq: "x < of_rat q" by blast
  then have "\<forall>n. 0 \<le> a pow\<^sub>\<rat> r n \<and> a pow\<^sub>\<rat> r n \<le> a pow\<^sub>\<rat> of_rat q"
  proof - 
    {fix m
      have " r m < q"
        using assms(3) le_less_trans of_rat_less xq by blast 
      then have "a pow\<^sub>\<rat> r m \<le> a pow\<^sub>\<rat> of_rat q"
        by (simp add: assms(1) powrat_le_mono)}
    then show ?thesis using less_imp_le [OF powrat_gt_zero]
      using assms(1) by auto
  qed
  then show ?thesis
     by (metis BseqI2' abs_of_nonneg real_norm_def)
qed

lemma convergent_powrat_incseq: 
   "\<lbrakk> 1 \<le> a; incseq r; \<forall>n. r n \<le> x \<rbrakk> \<Longrightarrow> convergent (\<lambda>n. a pow\<^sub>\<rat> (r n))"
  by (auto intro!: Bseq_monoseq_convergent 
       intro: incseq_imp_monoseq incseq_incseq_powrat Bseq_powrat_incseq [of _ _ x])

definition 
    incseq_of :: "real \<Rightarrow> (nat \<Rightarrow> rat)" where
    "incseq_of x = (SOME r. incseq r \<and>  (\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> x)"

lemma LIMSEQ_incseq_of [simp]:
     "(\<lambda>n. of_rat (incseq_of x n)) \<longlonglongrightarrow> x"
by (auto intro: someI2_ex [OF LIMSEQ_rat_real_ex] simp add: incseq_of_def)

lemma incseq_incseq_of [simp]:
      "incseq (incseq_of x)"
by (auto intro: someI2_ex [OF LIMSEQ_rat_real_ex] simp add: incseq_of_def)

lemma incseq_of_Suc [simp]:
      "incseq_of x n \<le> incseq_of x (Suc n)"
by (metis incseq_def incseq_incseq_of le_SucI le_refl)

lemma incseq_of_rat_incseq_of:
      "incseq (\<lambda>n. of_rat(incseq_of x n) :: 'a::linordered_field)"
  by (meson incseq_def incseq_incseq_of of_rat_less_eq)

lemma incseq_of_rat:
      "incseq s \<Longrightarrow> incseq (\<lambda>n. of_rat(s n) :: 'a :: linordered_field)"
by (auto simp add: incseq_def of_rat_less_eq)

lemma incseq_rat_le_real:
      "\<lbrakk> incseq s;  (\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> x \<rbrakk> \<Longrightarrow> of_rat (s n) \<le> (x::real)"
by (auto intro: incseq_le incseq_of_rat)

lemma incseq_of_le_self: "of_rat(incseq_of x n) \<le> x"
by (auto intro!: incseq_rat_le_real LIMSEQ_incseq_of)

lemma powrat_incseq_of_bounded: 
     "\<lbrakk> 1 \<le> a; x < of_rat r \<rbrakk> \<Longrightarrow>  a pow\<^sub>\<rat> (incseq_of x n) \<le> a pow\<^sub>\<rat> r"
  by (meson incseq_of_le_self le_less le_less_trans of_rat_less powrat_le_mono)

lemma incseq_powrat_insec_of: 
     "1 \<le> a \<Longrightarrow> incseq (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n))"
by (auto intro: incseq_incseq_powrat)

lemma Bseq_powrat_incseq_of: "1 \<le> a \<Longrightarrow> Bseq (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n))"
by (auto intro!: Bseq_powrat_incseq incseq_of_le_self)

lemma convergent_powrat_incseq_of: "1 \<le> a \<Longrightarrow> convergent (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n))"
by (blast intro: Bseq_monoseq_convergent Bseq_powrat_incseq_of incseq_imp_monoseq 
             incseq_powrat_insec_of)

text\<open>We're now ready to define real exponentation.\<close>

definition
    powa  :: "[real,real] \<Rightarrow> real"      (infixr "powa" 80) where
   "a powa x = (THE y. (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n)) \<longlonglongrightarrow> y)"

text \<open>real exponents.\<close>
definition
    powreal  :: "[real,real] \<Rightarrow> real"     (infixr "pow\<^sub>\<real>" 80) where
    "a pow\<^sub>\<real> x = (if 0 < a \<and> a < 1 then (inverse a) powa (-x) 
                 else if a \<ge> 1 then a powa x else 0)"

lemma powreal_eq_powa:
    "a \<ge> 1 \<Longrightarrow> a pow\<^sub>\<real> x = a powa x"
by (simp add: powreal_def)

lemma LIMSEQ_powrat_incseq_of_ex1:
   "1 \<le> a \<Longrightarrow> \<exists>!y. (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n))\<longlonglongrightarrow> y"
  by (metis LIMSEQ_unique convergentD convergent_powrat_incseq_of)

lemma LIMSEQ_powa:
   "1 \<le> a \<Longrightarrow> (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n)) \<longlonglongrightarrow> a powa x"
unfolding powa_def by (erule theI' [OF LIMSEQ_powrat_incseq_of_ex1])

lemma lemma_incseq_incseq_diff_inverse:
   "incseq s \<Longrightarrow> incseq (\<lambda>n. (s n :: rat) - 1/of_nat(Suc n))"
  by (auto intro: diff_mono simp add: divide_inverse incseq_def)

lemma lemma_incseq_diff_inverse_ub:
  assumes "incseq s" 
  and "(\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> x"
shows "of_rat(s n - 1/of_nat(Suc n)) < (x::real)"
proof -
  have "real_of_rat (s n - 1 / rat_of_nat (Suc n)) < real_of_rat (s n)"
    by (simp add: of_rat_diff)
  then show ?thesis
    by (meson assms incseq_rat_le_real linorder_not_less order_trans) 
qed

lemma lemma_LIMSEQ_incseq_diff_inverse: 
  assumes "(\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> x"
  shows " (\<lambda>n. of_rat(s n - 1/of_nat(Suc n))) \<longlonglongrightarrow> (x::real)"
proof -
  have "(\<lambda>x. real_of_rat (s x) - inverse (real (Suc x))) \<longlonglongrightarrow> x"
    using assms tendsto_diff [OF _ LIMSEQ_inverse_real_of_nat]
    by simp
  then show ?thesis 
    by (simp add: divide_inverse  of_rat_diff of_rat_inverse of_rat_add)
qed

lemma lemma_LIMSEQ_powrat_diff_inverse: 
  assumes "1 \<le> a" 
  and "(\<lambda>n. a pow\<^sub>\<rat> (s n))\<longlonglongrightarrow> y"
  shows "(\<lambda>n. a pow\<^sub>\<rat> (s n - 1/of_nat(Suc n))) \<longlonglongrightarrow> y"
proof -  
  have "(\<lambda>x. a pow\<^sub>\<rat> (1 / rat_of_nat (Suc x))) \<longlonglongrightarrow> 1"
    using assms(1) LIMSEQ_powrat_inverse_of_nat 
    by (auto intro!: LIMSEQ_Suc simp only: divide_inverse mult_1_left)
  then have " (\<lambda>n. a pow\<^sub>\<rat> s n / a pow\<^sub>\<rat> (1 / rat_of_nat (Suc n))) \<longlonglongrightarrow> y" 
    using assms(2) tendsto_divide by fastforce 
  then show ?thesis using powrat_diff assms(1) by auto
qed

lemma lemma_LIMSEQ_powrat_diff_inverse2: 
  assumes "1 \<le> a"
  and "(\<lambda>n. a pow\<^sub>\<rat> (s n - 1/of_nat(Suc n)))\<longlonglongrightarrow> y"
  shows "(\<lambda>n. a pow\<^sub>\<rat> (s n)) \<longlonglongrightarrow> y"
proof -
  have "(\<lambda>x. a pow\<^sub>\<rat> (1 / rat_of_nat (Suc x))) \<longlonglongrightarrow> 1"
    using assms(1) LIMSEQ_powrat_inverse_of_nat 
    by (auto intro!: LIMSEQ_Suc simp only: divide_inverse mult_1_left)
  then have "(\<lambda>x. a pow\<^sub>\<rat> inverse (rat_of_nat (Suc x)) * 
                  a pow\<^sub>\<rat> (s x - inverse(rat_of_nat (Suc x))))
              \<longlonglongrightarrow> 1 * y"
    using assms(2) by (auto intro!: tendsto_mult simp only: inverse_eq_divide)
  then show ?thesis using assms(1)
    by (auto simp add: powrat_add [symmetric]  )
qed

lemma lemma_seq_point_gt_ex: 
  "\<lbrakk> (\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real); y < x \<rbrakk> 
   \<Longrightarrow> \<exists>(m::nat).  y < of_rat(r m)"
  by (metis convergent_def limI lim_le not_less)

lemma lemma_seq_point_gt_ex2: 
   "\<lbrakk> (\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real); of_rat y < x \<rbrakk> 
    \<Longrightarrow> (\<exists>m. y < r m)"
  by (force dest: lemma_seq_point_gt_ex simp add: of_rat_less)

primrec interlaced_index :: "(nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> nat \<Rightarrow> nat" where
  "interlaced_index r s 0 = 0"
| "interlaced_index r s (Suc n) =  
          (LEAST m. if odd n then r (interlaced_index r s n) < s m
                    else s (interlaced_index r s n) < r m)"


definition interlaced_seq :: "(nat \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat) \<Rightarrow> nat \<Rightarrow> rat" where
  "interlaced_seq r s n = (if odd n then r (interlaced_index r s n) 
                           else s (interlaced_index r s n))"

lemma incseq_interlaced_seq:
  assumes "(\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real)" 
  and "(\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> (x::real)"
  and "\<forall>n. of_rat (r n) < x" 
  and "\<forall>n. of_rat (s n) < x"
  shows "incseq (interlaced_seq r s)"
proof -
  {fix n
  have "interlaced_seq r s n \<le> interlaced_seq r s (Suc n)" 
    using assms 
    by (auto intro: LeastI2_ex [OF lemma_seq_point_gt_ex2] 
          simp add: interlaced_seq_def)}
  then show ?thesis
    by (simp add: incseq_SucI) 
qed

lemma incseq_of_rat_interlaced_seq:
   "\<lbrakk> (\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real); 
      (\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> (x::real);
      \<forall>n. of_rat (r n) < x; \<forall>n. of_rat (s n) < x \<rbrakk> 
    \<Longrightarrow> incseq (\<lambda>n. real_of_rat (interlaced_seq r s n))"
  using incseq_interlaced_seq incseq_of_rat by blast

lemma interlaced_seq_bounded: 
   "\<lbrakk> \<forall>n. of_rat (r n) < x; \<forall>n. of_rat (s n) < x\<rbrakk> 
    \<Longrightarrow> of_rat (interlaced_seq r s n) < x"
unfolding interlaced_seq_def by auto


lemma convergent_interlaced_seq:
  assumes "(\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real)" 
  and "(\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> (x::real)" 
  and "\<forall>n. of_rat (r n) < x" 
  and "\<forall>n. of_rat (s n) < x"
  shows "convergent (\<lambda>n. real_of_rat (interlaced_seq r s n))"
proof - 
  have mono: "monoseq (\<lambda>n. real_of_rat (interlaced_seq r s n))"
    using assms incseq_interlaced_seq incseq_of_rat monoseq_iff by blast 
  {fix n 
     have "interlaced_seq r s 0 \<le> interlaced_seq r s n"
     proof (induction n)
       case 0
       then show ?case by simp
     next
       case (Suc n)
       then show ?case
         using assms incseq_def incseq_interlaced_seq by blast 
     qed}
  moreover 
  {fix n
   have "real_of_rat (interlaced_seq r s n) \<le> x"
     by (simp add: assms(3,4) interlaced_seq_bounded le_less)}
  ultimately have "Bseq (\<lambda>n. real_of_rat (interlaced_seq r s n))"
    by (metis decseq_bounded incseq_bounded mono monoseq_iff of_rat_less_eq)
  then show ?thesis using mono
    by (simp add: Bseq_monoseq_convergent) 
qed

lemma convergent_powrat_interlaced_seq:
   "\<lbrakk> 1 \<le> a; (\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real); 
      (\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> (x::real);
      \<forall>n. of_rat (r n) < x; \<forall>n. of_rat (s n) < x \<rbrakk> 
    \<Longrightarrow> convergent (\<lambda>n. a pow\<^sub>\<rat> (interlaced_seq r s n))"
by (auto intro: Bseq_monoseq_convergent incseq_interlaced_seq 
            interlaced_seq_bounded less_imp_le incseq_imp_monoseq 
            incseq_incseq_powrat Bseq_powrat_incseq [of _ _ x])

lemma LIMSEQ_even_odd_subseq_LIMSEQ:
  assumes "(\<lambda>n. (X (2 *n))) \<longlonglongrightarrow> a" "(\<lambda>n. (X (Suc(2 *n)))) \<longlonglongrightarrow> a"
  shows "X \<longlonglongrightarrow> (a :: 'a::real_normed_vector)"
proof (auto simp add: LIMSEQ_iff)
  fix r::real
  assume e0: "r > 0"
  obtain p where evenx: "\<forall>n\<ge>p. norm (X (2 * n) - a) < r"
    using  e0 assms(1) by (metis  LIMSEQ_iff) 
  obtain q where oddx: "\<forall>n\<ge>q. norm (X (Suc (2 * n)) - a) < r"
    using  e0 assms(2) by (metis  LIMSEQ_iff) 
  {fix n 
    assume max: "max (2 * p) (2 * q) \<le> n"
    have "norm (X n - a) < r"
    proof (cases "even n")
      case True
      then show ?thesis
        using dvd_def evenx max 
        by auto 
    next
      case False
      then show ?thesis using oddx max 
        by (auto elim: oddE)
    qed}
  then show "\<exists>no. \<forall>n\<ge>no. norm (X n - a) < r"
    by blast
qed

(* Not proved before? *)
lemma incseqD2: "incseq r \<Longrightarrow> r m < r n \<Longrightarrow> m < n"
  by (metis le_less mono_def not_le order.asym)

lemma subseq_interlaced_index_even:
  assumes "incseq r" 
  and "incseq s"
  and "(\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real)"
  and "(\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> (x::real)"
  and "\<forall>n. of_rat (r n) < x"
  and "\<forall>n. of_rat (s n) < x"
  shows "strict_mono (\<lambda>n. interlaced_index r s (2 * n))"
proof -
 {fix n
  have "interlaced_index r s (2 * n)
         < (LEAST m. r (LEAST m. s (interlaced_index r s (2 * n)) < r m) < s m)"
  proof (rule LeastI2_ex [of "\<lambda> m. s (interlaced_index r s (2 * n)) < r m"])
    show "\<exists>a. s (interlaced_index r s (2 * n)) < r a"
      using assms(3) assms(6) lemma_seq_point_gt_ex2 by blast
  next
    fix m
    assume inter_s: "s (interlaced_index r s (2 * n)) < r m"
    show "interlaced_index r s (2 * n) < (LEAST ma. r m < s ma) "
    proof (rule LeastI2_ex)
      show "\<exists>a. r m < s a"
        using assms(4) assms(5) lemma_seq_point_gt_ex2 by blast
    next
      fix k
      assume "r m < s k" 
      then show "interlaced_index r s (2 * n) < k" 
        using inter_s assms(2) incseqD2 less_trans by blast
    qed
  qed}
  then show ?thesis 
    by (simp add: strict_mono_Suc_iff)
qed

lemma subseq_interlaced_index_odd:
  assumes "incseq r"
  and "incseq s"
  and "(\<lambda>n. of_rat (r n)) \<longlonglongrightarrow> (x::real)"
  and "(\<lambda>n. of_rat (s n)) \<longlonglongrightarrow> (x::real)"
  and "\<forall>n. of_rat (r n) < x" 
  and "\<forall>n. of_rat (s n) < x" 
shows "strict_mono (\<lambda>n. interlaced_index r s (Suc (2 * n)))"
proof - 
  {fix n
    have "(LEAST m. s (interlaced_index r s (2 * n)) < r m)
             < (LEAST m.
                  s (LEAST m. r (LEAST m. s (interlaced_index r s (2 * n)) < r m) < s m)
                   < r m)"
    proof (rule LeastI2_ex [of "(\<lambda> m. s (interlaced_index r s (2 * n)) < r m)"])
      show "\<exists>a. s (interlaced_index r s (2 * n)) < r a"
        using assms(3) assms(6) lemma_seq_point_gt_ex2 by blast
    next
      fix m
      assume inter_s: "s (interlaced_index r s (2 * n)) < r m" 
      show "m < (LEAST ma. s (LEAST ma. r m < s ma) < r ma)"
      proof (rule LeastI2_ex [of "\<lambda>ma. r m < s ma"])
        show "\<exists>a. r m < s a"
          using assms(4) assms(5) lemma_seq_point_gt_ex2 by blast
      next
        fix k 
        assume rs: "r m < s k"
        show "m < (LEAST ma. s k < r ma)"
        proof (rule LeastI2_ex)
          show "\<exists>a. s k < r a"
            using assms(3) assms(6) lemma_seq_point_gt_ex2 by blast
        next
          fix l
          assume "s k < r l" 
          then show "m < l" using rs
            using assms(1) incseqD2 less_trans by blast
        qed
      qed
    qed} 
  then show ?thesis 
    by (simp add: strict_mono_Suc_iff)
qed

lemma interlaced_seq_even:
      "interlaced_seq r s (2*n) = s (interlaced_index r s (2*n))"
  by (simp add: interlaced_seq_def)


lemma interlaced_seq_odd:
      "interlaced_seq r s (Suc (2*n)) = r (interlaced_index r s (Suc (2*n)))"
  by (simp add: interlaced_seq_def)

lemma powa_indep_incseq_of:
  assumes "1 \<le> a" 
  and "incseq r" 
  and "incseq s"
  and "(\<lambda>n. real_of_rat (r n)) \<longlonglongrightarrow> x"
  and "(\<lambda>n. real_of_rat (s n)) \<longlonglongrightarrow> x"
  and "(\<lambda>n. a pow\<^sub>\<rat> (r n)) \<longlonglongrightarrow> y"
  and "(\<lambda>n. a pow\<^sub>\<rat> (s n)) \<longlonglongrightarrow> z"
shows "y = z"
proof -
  have rx: "(\<lambda>n. real_of_rat (r n - 1 / rat_of_nat (Suc n))) \<longlonglongrightarrow> x"
    using assms(4) lemma_LIMSEQ_incseq_diff_inverse by blast
  have sx: "(\<lambda>n. real_of_rat (s n - 1 / rat_of_nat (Suc n))) \<longlonglongrightarrow> x"
    using assms(5) lemma_LIMSEQ_incseq_diff_inverse by blast
  have "convergent
      (\<lambda>n. a pow\<^sub>\<rat>
           interlaced_seq (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
            (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) n)"
  using convergent_powrat_interlaced_seq  
             [of _ "(\<lambda>n. r n - 1 / rat_of_nat (Suc n))"
                 _ "(\<lambda>n. s n - 1 / rat_of_nat (Suc n))"]
               assms(1,2,3,4,5) lemma_incseq_diff_inverse_ub
               lemma_LIMSEQ_incseq_diff_inverse by blast 
  then obtain L 
    where converge: "(\<lambda>n. a pow\<^sub>\<rat> 
                interlaced_seq (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
                (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) n) \<longlonglongrightarrow> L"
    using convergent_def by force
  then have "((\<lambda>n. a pow\<^sub>\<rat>
                interlaced_seq (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
                 (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) n) \<circ> (\<lambda>n. 2 * n)) \<longlonglongrightarrow> L"  
    by (simp add: LIMSEQ_subseq_LIMSEQ strict_mono_Suc_iff) 
  moreover have "((\<lambda>n. a pow\<^sub>\<rat>
                interlaced_seq (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
                 (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) n) \<circ> (\<lambda>n. Suc (2 * n))) \<longlonglongrightarrow> L"
    using converge by (simp add: LIMSEQ_subseq_LIMSEQ strict_mono_Suc_iff) 
  moreover have "((\<lambda>n. a pow\<^sub>\<rat> (r n - 1 / rat_of_nat (Suc n))) \<circ>
           (\<lambda>n. interlaced_index (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
                 (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) (Suc (2 * n)))) \<longlonglongrightarrow> y"
  proof -
    from rx sx 
    have "strict_mono
            (\<lambda>n. interlaced_index (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
              (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) (Suc (2 * n)))"
      using subseq_interlaced_index_odd lemma_incseq_incseq_diff_inverse
                    lemma_incseq_diff_inverse_ub assms by blast
    moreover  have "(\<lambda>n. a pow\<^sub>\<rat> (r n - 1 / rat_of_nat (Suc n))) \<longlonglongrightarrow> y"
      using assms(1) assms(6) lemma_LIMSEQ_powrat_diff_inverse by blast
    ultimately show ?thesis
      using LIMSEQ_subseq_LIMSEQ by blast 
  qed
  moreover have "((\<lambda>n. a pow\<^sub>\<rat> (s n - 1 / rat_of_nat (Suc n))) \<circ>
           (\<lambda>n. interlaced_index (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
                 (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) (2 * n)))
          \<longlonglongrightarrow> z"
  proof -
    from rx sx 
    have "strict_mono
     (\<lambda>n. interlaced_index (\<lambda>n. r n - 1 / rat_of_nat (Suc n))
           (\<lambda>n. s n - 1 / rat_of_nat (Suc n)) (2 * n))"
      using subseq_interlaced_index_even lemma_incseq_incseq_diff_inverse
                    lemma_incseq_diff_inverse_ub assms by blast
    moreover have "(\<lambda>n. a pow\<^sub>\<rat> (s n - 1 / rat_of_nat (Suc n))) \<longlonglongrightarrow> z"
      using assms(1) assms(7) lemma_LIMSEQ_powrat_diff_inverse by blast
    ultimately show ?thesis
      using LIMSEQ_subseq_LIMSEQ by blast
  qed
  ultimately show ?thesis
    by (force dest: LIMSEQ_unique simp only: o_def interlaced_seq_even interlaced_seq_odd)
qed

lemma powa_indep_incseq_of':
      "\<lbrakk> 1 \<le> a; incseq r;
         (\<lambda>n. real_of_rat (r n)) \<longlonglongrightarrow> x; 
         (\<lambda>n. a pow\<^sub>\<rat> (r n)) \<longlonglongrightarrow> y \<rbrakk> 
       \<Longrightarrow> (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n)) \<longlonglongrightarrow> y"
  using powa_indep_incseq_of [of a r "incseq_of x"] LIMSEQ_powa
  by fastforce

(* Similar theorems as above, but specialized to incseq_of *)
lemma lemma_incseq_incseq_of_diff_inverse:
   "incseq (\<lambda>n. incseq_of x n - 1/of_nat(Suc n))"
by (blast intro: lemma_incseq_incseq_diff_inverse incseq_incseq_of)
 
lemma lemma_incseq_of_diff_inverse_ub:
   "of_rat(incseq_of x n - 1/of_nat(Suc n)) < x"
by (blast intro: lemma_incseq_diff_inverse_ub incseq_incseq_of LIMSEQ_incseq_of)

 lemma lemma_LIMSEQ_incseq_of_diff_inverse: 
    "(\<lambda>n. of_rat(incseq_of x n - 1/of_nat(Suc n))) \<longlonglongrightarrow> x"
by (blast intro: lemma_LIMSEQ_incseq_diff_inverse incseq_incseq_of LIMSEQ_incseq_of)

lemma powa_add: 
  assumes "1 \<le> a" 
  shows "a powa (x + y) = a powa x * a powa y"
proof -
  obtain k where 1: "(\<lambda>n. a pow\<^sub>\<rat> incseq_of y n) \<longlonglongrightarrow> k"
    using LIMSEQ_powrat_incseq_of_ex1 assms by blast
  moreover obtain l where 2: "(\<lambda>n. a pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> l"
    using LIMSEQ_powrat_incseq_of_ex1 assms by blast
  ultimately have "(\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n + incseq_of y n)) \<longlonglongrightarrow> l * k"
    using assms by (auto intro:  tendsto_mult simp add: powrat_add )
  moreover 
  have "incseq (\<lambda>n. incseq_of x n + incseq_of y n)"
    by  (force intro: incseq_SucI add_mono)
  moreover have "(\<lambda>n. real_of_rat (incseq_of x n + incseq_of y n)) \<longlonglongrightarrow> x + y"
    by (auto simp add: of_rat_add intro: tendsto_add LIMSEQ_incseq_of)
  ultimately have "(\<lambda>n. a pow\<^sub>\<rat> incseq_of (x + y) n) \<longlonglongrightarrow> l * k"
    using assms powa_indep_incseq_of' by blast 
  then show ?thesis using powa_def 1 2
    by (metis Lim_def limI) 
qed

lemma real_inverse_ge_one_lemma: 
      "\<lbrakk> 0 < (a::real); a < 1 \<rbrakk> \<Longrightarrow> inverse a \<ge> 1"
by (metis less_eq_real_def one_le_inverse_iff)

lemma real_inverse_gt_one_lemma: 
      "\<lbrakk> 0 < (a::real); a < 1 \<rbrakk> \<Longrightarrow> inverse a > 1"
by (metis one_less_inverse_iff)

lemma real_inverse_bet_one_one_lemma: 
      "1 < (a::real) \<Longrightarrow> 0 < inverse a \<and> inverse a < 1"
  by (metis inverse_less_1_iff inverse_positive_iff_positive 
        le_less_trans zero_le_one)

lemma powreal_add: 
   "a pow\<^sub>\<real> (x + y) = a pow\<^sub>\<real> x * a pow\<^sub>\<real> y"
  by (metis minus_add_distrib mult_zero_right powa_add 
       powreal_def real_inverse_ge_one_lemma)

lemma powa_one_eq_one [simp]: "1 powa a = 1"
proof -
  have "(\<lambda>n. 1 pow\<^sub>\<rat> incseq_of a n) \<longlonglongrightarrow> 1"
    by simp
  then show ?thesis
    by (metis Lim_def limI powa_def) 
qed 

lemma powreal_one_eq_one [simp]: "1 pow\<^sub>\<real> a = 1"
by (simp add: powreal_def)

lemma powa_zero_eq_one [simp]: "a \<ge> 1 \<Longrightarrow> a powa 0 = 1"
by (auto intro!: the1_equality LIMSEQ_powrat_incseq_of_ex1 
            intro: powa_indep_incseq_of' [of a "\<lambda>n. 0"] incseq_SucI
            simp add: powa_def)

lemma powreal_zero_eq_one [simp]: "a > 0 \<Longrightarrow> a pow\<^sub>\<real> 0 = 1"
by (auto dest: real_inverse_ge_one_lemma simp add: powreal_def)

lemma powr_zero_eq_one_iff [simp]: "x pow\<^sub>\<real> 0 = (if x \<le> 0 then 0 else 1)"
  using powreal_def powreal_zero_eq_one by force

lemma powa_one_gt_zero [simp]: "1 \<le> a \<Longrightarrow> a powa 1 = a"
by (auto intro!: LIMSEQ_powrat_incseq_of_ex1 the1_equality 
    powa_indep_incseq_of' [of a "\<lambda>n. 1"]  incseq_SucI simp add: powa_def)

lemma powa_minus_one: 
  assumes "1 \<le> a" shows "a powa -1 = inverse a"
proof -
  have "(\<lambda>n. a pow\<^sub>\<rat> - 1) \<longlonglongrightarrow> inverse a" using assms
    by (simp add: powrat_minus)
  then have "(\<lambda>n. a pow\<^sub>\<rat> incseq_of (- 1) n) \<longlonglongrightarrow> inverse a" 
    using powa_indep_incseq_of' [of a "\<lambda>n. -1"] assms
    by simp 
  then show ?thesis using powa_def
    by (metis Lim_def limI)
qed 

lemma powreal_minus_one: "0 \<le> a \<Longrightarrow> a pow\<^sub>\<real> -1 = inverse a"
  by (simp add: powa_minus_one powreal_def real_inverse_ge_one_lemma)

lemma powreal_one [simp]: "a \<ge> 0 \<Longrightarrow> a pow\<^sub>\<real> 1 = a"
  by (simp add: powa_minus_one powreal_def real_inverse_ge_one_lemma)

lemma powa_gt_zero: 
  assumes "a \<ge> 1" 
  shows "a powa x > 0"
proof - 
  obtain y where 1: "(\<lambda>n. a pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y"
    using LIMSEQ_powrat_incseq_of_ex1 assms by blast 
  moreover have "incseq (\<lambda>n. a pow\<^sub>\<rat> incseq_of x n)"
    by (simp add: assms incseq_powrat_insec_of) 
  ultimately have "y > 0"
    using assms incseq_le powrat_gt_zero
    by (metis less_le_trans zero_less_one)
  then show ?thesis using powa_def 1
    by (metis Lim_def limI) 
qed

lemma powreal_gt_zero: "a > 0 \<Longrightarrow> a pow\<^sub>\<real> x > 0"
  by (auto dest: powa_gt_zero real_inverse_ge_one_lemma 
        simp add: powreal_def not_less)

lemma powreal_not_zero: "a > 0 \<Longrightarrow> a pow\<^sub>\<real> x \<noteq> 0"
by (metis order_less_imp_not_eq powreal_gt_zero)

lemma powreal_minus: 
    "a pow\<^sub>\<real> -x = inverse (a pow\<^sub>\<real> x)"
proof (cases "a < 0")
  case True
  then show ?thesis
    using powreal_def by force 
next
  case False
  then have "a pow\<^sub>\<real> (x + -x) = a pow\<^sub>\<real> x * a pow\<^sub>\<real> -x"
    using powreal_add by presburger
  then show ?thesis
    using inverse_unique powreal_def powreal_zero_eq_one 
    by fastforce
qed

lemma powreal_minus_base_ge_one: 
   "a pow\<^sub>\<real> (-x) = (inverse a) pow\<^sub>\<real> x"
using one_le_inverse_iff powreal_def  by auto

lemma powreal_inverse:
     "inverse (a pow\<^sub>\<real> x) = (inverse a) pow\<^sub>\<real> x"
  using powreal_minus powreal_minus_base_ge_one 
  by presburger

lemma powa_minus:"a \<ge> 1 \<Longrightarrow> a powa (-x) = inverse (a powa x)"
  by (metis powreal_eq_powa powreal_minus)

lemma powa_mult_base: 
  assumes "1 \<le> a" and "1 \<le> b" 
  shows "(a * b) powa x = (a powa x) * (b powa x)"
proof - 
  obtain x' where lim_a: "(\<lambda>n. a pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> x'" 
    using LIMSEQ_powrat_incseq_of_ex1 assms(1) by blast
   then have lim_a_eq: "(THE y. (\<lambda>n. a pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y) = x'"
     by (metis Lim_def limI) 
   obtain y' where lim_b: "(\<lambda>n. b pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y'"
     using LIMSEQ_powrat_incseq_of_ex1 assms(2) by blast
   then have lim_b_eq: "(THE y. (\<lambda>n. b pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y) = y'"
     by (metis Lim_def limI) 
   have lim_ab: "(\<lambda>n. (a * b) pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> x' * y'"  
     using lim_a lim_b by (auto dest: tendsto_mult simp add: powrat_mult_base)
   then have "(THE y. (\<lambda>n. (a * b) pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y) = x' * y'"
     by (metis Lim_def limI)
   then show ?thesis
     by (simp add: lim_a_eq lim_b_eq powa_def)
 qed   


lemma powreal_mult_base_lemma1: 
  "\<lbrakk> 1 \<le> a; 1 \<le> b \<rbrakk> 
   \<Longrightarrow> (a * b) pow\<^sub>\<real> x = (a pow\<^sub>\<real> x) * (b pow\<^sub>\<real> x)"
by (metis mult.left_neutral mult_mono' powa_mult_base powreal_eq_powa zero_le_one)

lemma powreal_mult_base_lemma2: 
  assumes "1 \<le> a" 
  and "0 < b" 
  and "b < 1" 
shows "(a * b) pow\<^sub>\<real> x = (a pow\<^sub>\<real> x) * (b pow\<^sub>\<real> x)"
proof (cases "a * b < 1")
  case True
  assume ab1: "a * b < 1" 
  have "a * b > 0"
    using assms(1) assms(2) by auto
  then have inv_ab1: "1 \<le> inverse (a * b)"
    using ab1 real_inverse_ge_one_lemma by blast
  then have "(a * (inverse a * inverse b)) powa - x =
             a powa - x * (inverse a * inverse b) powa - x"
    by (simp add: assms(1) powa_mult_base) 
  then have "(inverse b) powa - x =
             a powa - x * (inverse a * inverse b) powa - x"
    using assms(1) by (simp add: mult.assoc [symmetric])
  then have "(inverse a * inverse b) powa - x = a powa x * inverse b powa - x"
    by (simp add:  mult.assoc [symmetric]  powa_add [symmetric] assms(1))
  then show ?thesis
    using ab1 assms powreal_def by auto 
next
  case False
  have inv_b: "inverse b \<ge> 1"
    by (simp add: assms real_inverse_ge_one_lemma) 
  assume "\<not> a * b < 1" 
  then have "a * b \<ge> 1" by simp
  then have "(a * b * inverse b) powa x = (a * b) powa x * inverse b powa x"
    by (simp add: assms(2) assms(3) powa_mult_base real_inverse_ge_one_lemma)
  then have "a powa x = (a * b) powa x * inverse b powa x"
  using assms(2) by (auto simp add: mult.assoc)
  then have "(a * b) powa x = a powa x * inverse b powa - x" 
    by (simp add: mult.assoc powa_add [symmetric] assms inv_b)
  then show ?thesis
    using False assms powreal_def by auto 
qed

lemma powreal_mult_base_lemma3: 
  assumes "0 < a" 
  and "a < 1" 
  and "0 < b" 
  and "b < 1" 
shows "(a * b) pow\<^sub>\<real> x = (a pow\<^sub>\<real> x) * (b pow\<^sub>\<real> x)"
proof - 
  have "a * b < 1" using assms
    by (metis less_trans mult.left_neutral mult_less_cancel_right_disj) 
  moreover have "(inverse a * inverse b) powa - x = 
                   inverse a powa - x * inverse b powa - x"
    by (simp add: assms powa_mult_base real_inverse_ge_one_lemma)
  ultimately show ?thesis using powreal_def assms by simp
qed

lemma powreal_mult_base: 
  assumes "0 \<le> a" and "0 \<le> b" 
  shows "(a * b) pow\<^sub>\<real> x = (a pow\<^sub>\<real> x) * (b pow\<^sub>\<real> x)"
proof (cases "a \<ge> 1 \<and> b \<ge> 1")
  case True
  then show ?thesis
    by (simp add: powreal_mult_base_lemma1) 
next
  case False
  then show ?thesis 
    using powreal_mult_base_lemma3 powreal_mult_base_lemma2 assms
    by (smt (verit) mult.commute mult_minus_left powreal_def)
qed

lemma incseq_le_all: "incseq X \<Longrightarrow> X \<longlonglongrightarrow> L \<Longrightarrow> \<forall>n. X n \<le> (L::real)"
by (metis incseq_le)

lemma powa_powrat_eq: 
  assumes "a \<ge> 1" shows "a powa (of_rat q) = a pow\<^sub>\<rat> q"
proof -
  have "(\<lambda>n. a pow\<^sub>\<rat> incseq_of (real_of_rat q) n) \<longlonglongrightarrow> a pow\<^sub>\<rat> q"
    using powa_indep_incseq_of' assms by fastforce 
  then show ?thesis using powa_def
    by (metis Lim_def limI) 
qed


lemma realpow_powrat_eq: "a > 0 \<Longrightarrow> a pow\<^sub>\<real> (of_rat q) = a pow\<^sub>\<rat> q"
proof -
  assume a1: "0 < a"
  then have "\<not> a < 1 \<or> 1 \<le> inverse a"
    using real_inverse_ge_one_lemma by blast
  then show ?thesis
    using a1
    by (metis inverse_inverse_eq not_le powa_powrat_eq 
         powrat_inverse powreal_eq_powa powreal_inverse)
qed

(* Move to NthRoot.thy *)
lemma LIMSEQ_real_root: 
   "\<lbrakk> X \<longlonglongrightarrow> a; m > 0 \<rbrakk> \<Longrightarrow> (\<lambda>n. root m (X n)) \<longlonglongrightarrow> (root m a)"
by (metis isCont_tendsto_compose [where g="\<lambda>x. root m x"] isCont_real_root)

lemma powa_powrat_lemma1:
  assumes "a \<ge> 1" and "p \<ge> 0" 
  shows "(a powa x) pow\<^sub>\<rat> p = (a powa (x * of_rat p))"
proof -
  obtain y where lim_a: "(\<lambda>n. a pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y" 
    using LIMSEQ_powrat_incseq_of_ex1 assms(1) by blast
   then have the_lim: "(THE y. (\<lambda>n. a pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y) = y"
     by (metis Lim_def limI) 
   then have  "(\<lambda>n. (a pow\<^sub>\<rat> incseq_of x n) pow\<^sub>\<rat> p) \<longlonglongrightarrow> y pow\<^sub>\<rat> p"
     using LIMSEQ_powrat_base assms(1) lim_a powa_def powa_gt_zero by auto
   then have lim_ap: "(\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n * p)) \<longlonglongrightarrow> y pow\<^sub>\<rat> p"
     using assms(1) powrat_mult by auto 
   then have "(\<lambda>n. a pow\<^sub>\<rat> incseq_of (x * real_of_rat p) n) \<longlonglongrightarrow> y pow\<^sub>\<rat> p"
   proof -
     have "incseq (\<lambda>n. incseq_of x n * p)"
       by (simp add: assms(2) incseq_SucI mult_right_mono) 
     moreover have "(\<lambda>n. real_of_rat (incseq_of x n * p)) \<longlonglongrightarrow> x * real_of_rat p" 
       by (auto intro!: tendsto_mult simp add: of_rat_mult)
     ultimately show ?thesis
       using assms(1) lim_ap powa_indep_incseq_of' by blast
   qed
   then show ?thesis using powa_def
     by (metis Lim_def limI the_lim)
 qed

lemma powa_powrat_lemma2:
  assumes "a \<ge> 1" and "p < 0" 
  shows "(a powa x) pow\<^sub>\<rat> p = (a powa (x * of_rat p))"
proof - 
  have "(a powa x) pow\<^sub>\<rat> - p = a powa (x * real_of_rat (- p))"
    by (simp add: assms(1) assms(2) less_imp_le powa_powrat_lemma1) 
  then have  "inverse ((a powa x) pow\<^sub>\<rat> p) = inverse (a powa (x * real_of_rat p))"
    by (simp add: assms(1) of_rat_minus powa_minus powrat_minus)
  then show ?thesis by simp
qed

lemma powa_powrat_lemma:
  "a \<ge> 1 \<Longrightarrow> (a powa x) pow\<^sub>\<rat> p = (a powa (x * of_rat p))"
by (metis linorder_not_less powa_powrat_lemma1 powa_powrat_lemma2)

(* Didn't we use to have something similar proved? *)
lemma LIMSEQ_iff2:
  fixes L :: "'a::metric_space"
  shows "(X \<longlonglongrightarrow> L) = (\<forall>m::nat>0. \<exists>no. \<forall>n\<ge>no. dist (X n)  L < inverse m)"
proof
  assume  "X \<longlonglongrightarrow> L" 
  then show "\<forall>m>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < inverse (real m)" 
    by (auto simp add: LIMSEQ_def)
next 
  assume assm: "\<forall>m>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < inverse (real m)" 
  {fix r
   assume "(r::real) > 0" 
   then have " \<exists>no. \<forall>n\<ge>no. dist (X n) L < r" 
     using assm  
     by (metis ex_inverse_of_nat_less less_trans)
  }
  then show "X \<longlonglongrightarrow> L"
    by (simp add: metric_LIMSEQ_I) 
qed

lemma LIM_def2:
   "f \<midarrow>a\<rightarrow> L  = (\<forall>m::nat>0. \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < inverse m)"
   for a :: "'a::metric_space" and L :: "'b::metric_space"
proof
  assume "f \<midarrow>a\<rightarrow> L"  
  then show "\<forall>m::nat>0. \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < inverse m" 
    by (auto simp add: LIM_def)
next
  assume assm: "\<forall>m::nat>0. \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < inverse m"
  {fix r
    assume r0: "(r::real) > 0" 
    then obtain n where "inverse (real (Suc n)) < r"
      using reals_Archimedean by blast 
    then have "\<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r" 
      using assm r0 by (metis order_less_trans zero_less_Suc)
  } 
  then show "f \<midarrow>a\<rightarrow> L"
    by (simp add: metric_LIM_I) 
qed

lemma powa_ge_one: 
  assumes "a \<ge> 1" 
  and "x \<ge> 0" 
  shows "a powa x \<ge> 1"
proof -
  obtain y where lima: "(\<lambda>n. a pow\<^sub>\<rat> incseq_of x n) \<longlonglongrightarrow> y"
    using LIMSEQ_powrat_incseq_of_ex1 assms(1) by blast
  moreover have "incseq (\<lambda>n. a pow\<^sub>\<rat> incseq_of x n)"
    using assms(1) incseq_powrat_insec_of by blast
  moreover have "\<forall>n. a pow\<^sub>\<rat> incseq_of x n \<le> y"
    using incseq_le_all using calculation by blast 
  ultimately have "1 \<le> y" 
    using assms LIMSEQ_incseq_of LIMSEQ_powa LIMSEQ_powrat_incseq_of_ex1 
          lemma_seq_point_gt_ex2 powa_zero_eq_one powrat_ge_one
    by (metis less_le  of_rat_0  less_eq_real_def xt1(6))
  then show ?thesis
    using LIMSEQ_powa LIMSEQ_unique assms(1) lima by blast
qed

lemma powreal_ge_one: "a \<ge> 1 \<Longrightarrow> x \<ge> 0 \<Longrightarrow> a pow\<^sub>\<real> x \<ge> 1"
by (simp add: powreal_def powa_ge_one)

lemma powreal_ge_one2:  
   "\<lbrakk> 0 < a; a < 1; x \<le> 0 \<rbrakk> \<Longrightarrow> a pow\<^sub>\<real> x \<ge> 1"
  by (simp add: powa_ge_one powreal_def real_inverse_ge_one_lemma)
  
lemma inverse_of_real_nat_of_rat_of_nat: 
      "inverse (real_of_nat n) =  of_rat(inverse (of_nat n))"
by (metis Ratreal_def of_rat_of_nat_eq real_inverse_code)

lemma LIMSEQ_powa_inverse_of_nat: 
   "a \<ge> 1 \<Longrightarrow> (\<lambda>n. a powa inverse (real_of_nat n)) \<longlonglongrightarrow> 1"
  by (simp add:  inverse_of_real_nat_of_rat_of_nat powa_powrat_eq 
      LIMSEQ_powrat_inverse_of_nat)

lemma incseq_of_le_mono:
  assumes "r \<le> s" 
  shows "\<exists>N. \<forall>n\<ge>N. incseq_of r n \<le>  incseq_of s n"
proof -
  have "r = s \<or> r < s" using assms by force
  then show ?thesis
  proof
    assume "r = s" then show ?thesis by simp
  next
    assume rs: "r < s" 
    then obtain m where less_incseq: "r < real_of_rat (incseq_of s m)"
      using LIMSEQ_incseq_of lemma_seq_point_gt_ex by blast
    moreover have "\<forall>n. real_of_rat (incseq_of r n) \<le> r"
      using incseq_of_le_self by simp
    ultimately have "\<forall>n. real_of_rat (incseq_of r n) < real_of_rat (incseq_of s m)"
      using le_less_trans by blast
    then have incrs: "\<forall>n. incseq_of r n \<le> incseq_of s m"
      by (simp add: less_imp_le of_rat_less)
    then show ?thesis
      by (meson incseq_def incseq_incseq_of order_trans) 
  qed
qed

lemma powa_le_mono:
  assumes "r \<le> s" 
  and "a \<ge> 1" 
  shows "a powa r \<le> a powa s"
proof -
  obtain y where "(\<lambda>n. a pow\<^sub>\<rat> incseq_of s n) \<longlonglongrightarrow> y"
    using LIMSEQ_powrat_incseq_of_ex1 assms(2) by blast
  moreover obtain x where "(\<lambda>n. a pow\<^sub>\<rat> incseq_of r n) \<longlonglongrightarrow> x"
    using LIMSEQ_powrat_incseq_of_ex1 assms(2) by blast
  moreover have "\<exists>N. \<forall>n\<ge>N. a pow\<^sub>\<rat> incseq_of r n \<le> a pow\<^sub>\<rat> incseq_of s n"
    by (meson assms(1) assms(2) incseq_of_le_mono powrat_le_mono)
  moreover have "x \<le> y"
    using LIMSEQ_le calculation by blast
  ultimately show ?thesis
    by (metis Lim_def limI powa_def) 
qed

lemma powreal_le_mono:
   "\<lbrakk> r \<le> s; a \<ge> 1 \<rbrakk> \<Longrightarrow> a pow\<^sub>\<real> r \<le> a pow\<^sub>\<real> s"
by (metis powa_le_mono powreal_eq_powa)

lemma powreal_le_anti_mono:
   "\<lbrakk> r \<le> s; 0 < a; a < 1 \<rbrakk> \<Longrightarrow> a pow\<^sub>\<real> r \<ge> a pow\<^sub>\<real> s"
  by (simp add: powa_le_mono powreal_def real_inverse_ge_one_lemma)

lemma powreal_less_cancel:
   "\<lbrakk> a pow\<^sub>\<real> r < a pow\<^sub>\<real> s; a \<ge> 1 \<rbrakk> \<Longrightarrow> r < s"
by (metis less_le_not_le linorder_not_less powreal_eq_powa powreal_le_mono)

lemma powa_less_mono:
  assumes "r < s" and "a > 1" 
  shows "a powa r < a powa s"
proof -
  obtain q where "r < real_of_rat q" "real_of_rat q < s"
    using assms(1) of_rat_dense by blast
  moreover obtain qa where "real_of_rat q < real_of_rat qa" "real_of_rat qa < s"
    using of_rat_dense calculation(2) by blast
  ultimately show ?thesis using assms 
    by (metis (full_types) antisym less_eq_real_def less_imp_not_eq2 powa_le_mono 
        powa_powrat_eq powrat_inject_exp)
  qed

lemma powreal_less_anti_mono:
  assumes "r < s" 
  and "0 < a" 
  and "a < 1" 
shows "a pow\<^sub>\<real> r > a pow\<^sub>\<real> s"
proof -
  have "inverse a > 1"
    by (simp add: assms(2, 3) one_less_inverse_iff) 
  moreover have "inverse a powa r < inverse a powa s"
    using assms(1) powa_less_mono
    using calculation by blast
  ultimately show ?thesis 
    using powreal_eq_powa powreal_inverse powreal_le_anti_mono powreal_less_cancel
    by (metis assms(2,3) le_less less_irrefl)
qed

lemma powreal_less_mono:
   "\<lbrakk> r < s; a > 1 \<rbrakk> \<Longrightarrow> a pow\<^sub>\<real> r < a pow\<^sub>\<real> s"
by (simp add: powreal_def powa_less_mono)

lemma powa_le_cancel:
   "\<lbrakk> a powa r \<le> a powa s; a > 1 \<rbrakk> \<Longrightarrow> r \<le> s"
by (metis not_le powa_less_mono)

lemma powreal_le_cancel:
   "\<lbrakk> a pow\<^sub>\<real> r \<le> a pow\<^sub>\<real> s; a > 1 \<rbrakk> \<Longrightarrow> r \<le> s"
by (metis not_le powreal_less_mono)

lemma powreal_less_cancel_iff [simp]: 
  "1 < a \<Longrightarrow> (a pow\<^sub>\<real> r < a pow\<^sub>\<real> s) = (r < s)"
by (metis less_imp_le powreal_less_cancel powreal_less_mono)

lemma powreal_le_cancel_iff [simp]: 
  "1 < a \<Longrightarrow> (a pow\<^sub>\<real> r \<le> a pow\<^sub>\<real> s) = (r \<le> s)"
by (simp add: linorder_not_less [symmetric])

lemma powreal_inject_exp1 [simp]: 
  "1 < a  \<Longrightarrow> (a pow\<^sub>\<real> r = a pow\<^sub>\<real> s) = (s = r)"
by (metis antisym_conv3 less_irrefl powreal_less_mono)

lemma powreal_eq_one_iff [simp]:
  "a pow\<^sub>\<real> x = 1 \<longleftrightarrow> x = 0" if "a > 1" 
  using powreal_inject_exp1 that by fastforce

lemma powreal_inject_base_less_one [simp]: 
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> (a pow\<^sub>\<real> r = a pow\<^sub>\<real> s) = (s = r)"
by (metis linorder_neq_iff order_less_imp_not_eq2 powreal_less_anti_mono)

lemma powreal_inject [simp]: 
  "0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> (a pow\<^sub>\<real> r = a pow\<^sub>\<real> s) = (s = r)"
  using powreal_inject_base_less_one by fastforce

lemma powreal_gt_one: "a > 1 \<Longrightarrow> x > 0 \<Longrightarrow> a pow\<^sub>\<real> x > 1"
by (metis less_eq_real_def powa_less_mono powa_zero_eq_one powreal_eq_powa)

lemma isCont_powa_exponent_at_zero: 
  assumes "a > 1" shows "isCont (\<lambda>x. a powa x) 0"
proof -
  {fix m 
  assume m0: "(m::nat) > 0" 
  have lim1: "(\<lambda>n. a powa inverse (real n)) \<longlonglongrightarrow> 1"
    by (simp add: LIMSEQ_powa_inverse_of_nat assms less_imp_le)
  then have "\<exists>no. \<forall>n\<ge>no. \<bar>a powa inverse (real n) - 1\<bar> < inverse (real m)"
    using lim1 LIMSEQ_iff2  dist_real_def m0 by metis      
  then obtain "no" 
    where pow1: "\<forall>n\<ge>no. \<bar>a powa inverse (real n) - 1\<bar> < inverse (real m)" 
    by blast

  have lim2: "(\<lambda>x. inverse (a powa inverse (real x))) \<longlonglongrightarrow> 1"
    using tendsto_inverse lim1 by fastforce
  then have "\<exists>k. \<forall>n\<ge>k. \<bar>inverse (a powa inverse (real n)) - 1\<bar> < inverse (real m)"
    using LIMSEQ_iff2 dist_real_def m0 by metis
  then obtain "k" 
    where pow2: "\<forall>n\<ge>k. \<bar>inverse (a powa inverse (real n)) - 1\<bar> < inverse (real m)" 
    by blast
  have "\<exists>s>0. \<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < s \<longrightarrow>  \<bar>(a powa x) - 1\<bar> < inverse (real m)"
  proof - 
    let ?d = "min (inverse (Suc no)) (inverse (Suc k))"
    {fix x
    assume "abs x < ?d"
    then have x_bounds: "- inverse (of_nat(Suc k)) < x" "x < inverse (of_nat(Suc no))"
      by linarith+
    then have "a powa - inverse (of_nat (Suc k)) < a powa x"
      using assms powa_less_mono by blast 
    moreover have "- inverse (real m) < a powa - inverse (real (Suc k)) - 1"
      using assms pow2 powa_minus
      by (metis minus_diff_eq neg_less_iff_less abs_less_iff lessI less_imp_le)  
    ultimately have lo: "- inverse(real m) < a powa x - 1"
      by linarith
    have "a powa x < a powa inverse (of_nat(Suc no))"
      using assms powa_less_mono x_bounds(2) by blast
    moreover have "a powa inverse (real (Suc no)) - 1 < inverse (real m)"
      using assms pow1 by (metis less_imp_le abs_less_iff lessI) 
    ultimately have "a powa x - 1 < inverse(real m)"
      by linarith
    then have "abs (a powa x - 1) < inverse(real m)" 
      using lo by linarith}
    then show ?thesis
      by (metis inverse_positive_iff_positive min_less_iff_conj of_nat_0_less_iff zero_less_Suc) 
  qed}
  then have "\<forall>m>0. \<exists>s>0. \<forall>x. x \<noteq> 0 \<and> \<bar>x\<bar> < s \<longrightarrow> \<bar>a powa x - 1\<bar> < inverse (real m)"
    by blast
  then show ?thesis 
    by (auto simp add: assms isCont_def LIM_def2 dist_real_def less_imp_le)
qed

lemma LIM_powa_exponent_at_zero: "1 < a \<Longrightarrow> (\<lambda>h. a powa h) \<midarrow>0\<rightarrow>  1"
by (metis isCont_def isCont_powa_exponent_at_zero less_eq_real_def powa_zero_eq_one)

lemma isCont_powa_exponent_gt_one: 
  assumes "a > 1" 
  shows "isCont (\<lambda>x. a powa x) x"
proof -
  have "(\<lambda>h. a powa x * a powa h) \<midarrow>0\<rightarrow> a powa x"
    using LIM_powa_exponent_at_zero assms tendsto_mult_left by fastforce
  then have "(\<lambda>h. a powa (x + h)) \<midarrow>0\<rightarrow> a powa x"
    using assms powa_add by auto 
  then have "(powa) a \<midarrow>x\<rightarrow> a powa x"
    using LIM_offset_zero_cancel by blast
  then show ?thesis
    using isCont_def by blast
qed

lemma isCont_powreal_exponent_gt_one: 
   "a > 1 \<Longrightarrow> isCont (\<lambda>x. a pow\<^sub>\<real> x) x"
by (metis ext isCont_powa_exponent_gt_one less_eq_real_def powreal_eq_powa)

lemma isCont_powreal_exponent_less_one: 
  assumes "0 < a" 
  and "a < 1" 
  shows "isCont (\<lambda>x. a pow\<^sub>\<real> x) x"
proof -
  have "1 < inverse a"
    by (simp add: assms one_less_inverse) 
  then have "isCont ((pow\<^sub>\<real>) (inverse a)) x"
    by (simp add: isCont_powreal_exponent_gt_one) 
  then have "isCont (\<lambda>x. inverse (inverse a pow\<^sub>\<real> x)) x"
    using assms(1) continuous_at_within_inverse powreal_not_zero by fastforce
  then show ?thesis
    using assms(1) powreal_inverse by auto 
qed

lemma isCont_powreal_exponent: 
  assumes a_gt_0: "0 < a" shows "isCont (\<lambda>x. a pow\<^sub>\<real> x) x"
proof cases 
  assume "a > 1" then show ?thesis 
    using isCont_powreal_exponent_gt_one by blast 
  next 
  assume "\<not> a > 1" 
    then have "a < 1 \<or> a = 1" by auto
    then show ?thesis 
    proof 
      assume "a < 1"  then show ?thesis 
        using a_gt_0 isCont_powreal_exponent_less_one by blast
    next 
     assume "a =1" then show ?thesis by simp
    qed
qed
 
(* A little diversion *)
lemma real_of_rat_abs: 
    "real_of_rat(abs a) = abs(of_rat a)"
by (simp add: abs_if of_rat_minus)

lemma isCont_powrat_exponent:                                 
  assumes "0 < a" shows "isCont (\<lambda>x. a pow\<^sub>\<rat> x) x"
proof - 
  have isCont_of_rat: "isCont real_of_rat x"  using isCont_def LIM_def dist_real_def
    by (metis dist_commute of_rat_diff rat_dist_def real_of_rat_abs)
  have "isCont ((pow\<^sub>\<real>) a) (real_of_rat x)" using assms
    by (simp add: isCont_powreal_exponent)
  then have "isCont (\<lambda>x. a pow\<^sub>\<real> real_of_rat x) x" using isCont_of_rat
    using isCont_o2 by blast
  then show ?thesis using realpow_powrat_eq assms by simp
qed


lemma LIMSEQ_powrat_exponent: 
  "\<lbrakk> X \<longlonglongrightarrow> x; a > 0 \<rbrakk> \<Longrightarrow> (\<lambda>n. a pow\<^sub>\<rat> (X n)) \<longlonglongrightarrow> a pow\<^sub>\<rat> x"
by (metis isCont_tendsto_compose isCont_powrat_exponent)

(* Now, back to business *)
lemma powa_mult: 
  assumes "1 \<le> a" and "0 \<le> x" 
  shows "(a powa x) powa y = a powa (x * y)"
proof (cases)
  assume "a \<noteq> 1"
  then have a_gt_1: "a > 1" using assms(1) by simp
  have "a powa x \<ge> 1" using assms powa_ge_one by blast
  then have lim1: "(\<lambda>n. a powa (x * real_of_rat (incseq_of y n))) \<longlonglongrightarrow> (a powa x) powa y"
    using LIMSEQ_powa [of "a powa x" y] powa_powrat_lemma assms(1) by simp
  have "isCont ((powa) a) (x * y)" using isCont_powa_exponent_gt_one a_gt_1 by blast
  moreover have "(\<lambda>n. x * real_of_rat (incseq_of y n)) \<longlonglongrightarrow> x * y"
    by (simp add: tendsto_mult_left) 
  ultimately have "(\<lambda>n. a powa (x * real_of_rat (incseq_of y n))) \<longlonglongrightarrow> a powa (x * y)"
    using isCont_tendsto_compose by blast 
  then show ?thesis
    using LIMSEQ_unique lim1 by blast 
next
  assume "\<not> a \<noteq> 1" 
  then show ?thesis
    by auto 
qed
  
lemma powreal_mult1: 
      "\<lbrakk> 1 \<le> a; 0 \<le> x \<rbrakk> \<Longrightarrow> (a pow\<^sub>\<real> x) pow\<^sub>\<real> y = a pow\<^sub>\<real> (x * y)"
by (metis powa_mult powreal_eq_powa powreal_ge_one)

lemma powreal_mult2: 
  assumes "0 < a" and "a < 1" and "0 \<le> x"
  shows "(a pow\<^sub>\<real> x) pow\<^sub>\<real> y = a pow\<^sub>\<real> (x * y)"
proof -
  have "1 \<le> inverse a" using assms using real_inverse_ge_one_lemma by simp
  then have "(inverse a pow\<^sub>\<real> x) pow\<^sub>\<real> y = inverse a pow\<^sub>\<real> (x * y)" 
    using powreal_mult1 assms(3) by blast
  then have "inverse((inverse a pow\<^sub>\<real> x) pow\<^sub>\<real> y) =  a pow\<^sub>\<real> (x * y)"
    by (simp add: assms(1) powreal_inverse) 
  then show ?thesis
    using assms(1) powreal_gt_zero powreal_inverse by auto 
qed

lemma powreal_mult3: 
      "\<lbrakk> 0 < a; 0 \<le> x \<rbrakk> \<Longrightarrow> (a pow\<^sub>\<real> x) pow\<^sub>\<real> y = a pow\<^sub>\<real> (x * y)"
by (metis linorder_not_less powreal_mult1 powreal_mult2)

lemma powreal_mult4: 
  assumes a0: "0 < a" and x0: "x \<le> 0" 
  shows "(a pow\<^sub>\<real> x) pow\<^sub>\<real> y = a pow\<^sub>\<real> (x * y)"
proof -
  have minux0: "-x \<ge> 0" using x0  by simp
  then have "(a pow\<^sub>\<real> -x) pow\<^sub>\<real> y = a pow\<^sub>\<real> (-x * y)" 
    using powreal_mult3 a0 by simp
  then have "inverse (a pow\<^sub>\<real> x) pow\<^sub>\<real> y = inverse (a pow\<^sub>\<real> (x * y))"
    by (simp add: powreal_minus)
  then have "inverse ((a pow\<^sub>\<real> x) pow\<^sub>\<real> y) = inverse (a pow\<^sub>\<real> (x * y))"
    by (simp add: a0 powreal_gt_zero powreal_inverse)
  then show ?thesis
    using inverse_eq_iff_eq by blast 
qed

(* At long last... *)
lemma powreal_mult: 
  "(a pow\<^sub>\<real> x) pow\<^sub>\<real> y = a pow\<^sub>\<real> (x * y)"
  by (smt (verit, best) powreal_def powreal_mult3 powreal_mult4)

lemma powreal_divide:
  "\<lbrakk> 0 \<le> a; 0 \<le> b \<rbrakk> \<Longrightarrow> (a/b) pow\<^sub>\<real> x = (a pow\<^sub>\<real> x) / (b pow\<^sub>\<real> x)"
  by (simp add: divide_inverse powreal_inverse powreal_mult_base)

lemma powreal_divide2:
  "0 \<le> a \<Longrightarrow> a pow\<^sub>\<real> (x - y) = (a pow\<^sub>\<real> x) / (a pow\<^sub>\<real> y)"
proof -
  assume a1: "0 \<le> a"
  have f2: "\<forall>x0. - (x0::real) = - 1 * x0"
    by auto
  have "x - y = x + - 1 * y"
    by auto
  then show ?thesis
    using f2 a1 by (metis field_class.field_divide_inverse powreal_add powreal_minus)
qed

lemma powreal_less_mono_base:
  assumes r0: "r > 0" and a0: "0 < a" and ab: "a < b" 
  shows "a pow\<^sub>\<real> r < b pow\<^sub>\<real> r"
proof - 
  have "b/a > 1" using ab a0 by simp
  then have "(b/a) pow\<^sub>\<real> r > 1" 
    using powreal_gt_one r0 by simp
  then have "b pow\<^sub>\<real> r / a pow\<^sub>\<real> r > 1"
    using ab a0 powreal_divide by simp
  also have "a pow\<^sub>\<real> r > 0"
    by (simp add: a0 powreal_gt_zero) 
  ultimately show ?thesis
    using less_divide_eq_1_pos by blast 
qed  

lemma powreal_less_antimono_base:
  assumes "r < 0" and "0 < a" and "a < b" 
  shows "a pow\<^sub>\<real> r > b pow\<^sub>\<real> r"
proof -
  have "0 < -r" using assms(1) by simp 
  then have "a pow\<^sub>\<real> - r < b pow\<^sub>\<real> - r"
    using assms(2) assms(3) powreal_less_mono_base by blast
  then show ?thesis
    using assms(2) assms(3) powreal_gt_zero powreal_minus by auto 
qed

lemma powa_power_eq: 
  assumes "a \<ge> 1" shows "a powa (of_nat n) = a ^ n"
proof -
  have "incseq (\<lambda>m. rat_of_nat n)" by simp
  moreover have "(\<lambda>na. real_of_rat (rat_of_nat n)) \<longlonglongrightarrow> real n" by simp
  moreover have "(\<lambda>na. a pow\<^sub>\<rat> rat_of_nat n) \<longlonglongrightarrow> a ^ n" 
    using powrat_power_eq assms by auto
  ultimately have "(\<lambda>na. a pow\<^sub>\<rat> incseq_of (real n) na) \<longlonglongrightarrow> a ^ n" 
    using powa_indep_incseq_of' assms by blast
  then show ?thesis
    by (metis Lim_def limI powa_def) 
qed

lemma powreal_power_eq:
  "a > 0 \<Longrightarrow> a pow\<^sub>\<real> (of_nat n) = a ^ n"
unfolding powreal_def
by (simp add: powa_minus powa_power_eq power_inverse real_inverse_ge_one_lemma)

lemma powreal_power_eq2: 
   "0 \<le> a \<Longrightarrow> 0 < n \<Longrightarrow> a ^ n = (if a = 0 then 0 else a pow\<^sub>\<real> (real n))"
  by (auto simp add:  powreal_power_eq)

lemma powreal_mult_power: "a > 0 \<Longrightarrow> a pow\<^sub>\<real> (n * x) = (a pow\<^sub>\<real> x) ^ n"
  by (metis mult.commute powreal_gt_zero powreal_mult powreal_power_eq)

lemma powreal_int:
  assumes "x > 0"
  shows "x pow\<^sub>\<real> i = (if i \<ge> 0 then x ^ nat i else 1 / x ^ nat (-i))"
proof cases
  assume "i < 0" 
  have r: "x pow\<^sub>\<real> i = 1 / x  pow\<^sub>\<real> (-i)" by (simp add: assms powreal_minus divide_inverse)
  show ?thesis using \<open>i < 0\<close> \<open>x > 0\<close> by (simp add: r field_simps powreal_power_eq [symmetric])  
qed (simp add: assms powreal_power_eq[symmetric])

lemma powreal_numeral: "0 \<le> x \<Longrightarrow> x pow\<^sub>\<real> numeral n = x^numeral n"
  using powreal_power_eq [of x "numeral n"] powreal_def 
  by fastforce

lemma root_powreal_inverse:
  assumes "0 < n" and "0 \<le> x" 
  shows "root n x = x pow\<^sub>\<real> (1/n)"
proof -
  have "root n x = x pow\<^sub>\<real> real_of_rat (inverse (rat_of_nat n))" 
    using assms real_root_eq_powrat_inverse realpow_powrat_eq [symmetric] powreal_def
    by simp
  then show ?thesis
    by (metis inverse_eq_divide of_rat_inverse of_rat_of_nat_eq)  
qed

lemma powreal_inverse_of_nat_gt_one:
  "\<lbrakk> 1 < a; n \<noteq> 0\<rbrakk>  \<Longrightarrow> a pow\<^sub>\<real> (inverse (of_nat n)) > 1"
by (metis inverse_positive_iff_positive neq0_conv of_nat_0_less_iff powreal_gt_one)

end 