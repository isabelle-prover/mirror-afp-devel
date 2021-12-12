theory Extended_Reals_Sums_Compl imports  
  "HOL-Analysis.Analysis" 
begin

lemma real_ereal_leq:
  fixes a::ereal and b::real
  assumes "real_of_ereal a \<le> b"
    and "a \<noteq> \<infinity>"
  shows "a \<le> ereal b"
  by (metis (mono_tags, opaque_lifting) MInfty_eq_minfinity assms eq_iff ereal_eq_0(2) ereal_le_real_iff 
      ereal_less_eq(2) le_cases real_of_ereal.elims real_of_ereal.simps(1) zero_ereal_def) 

lemma ereal_sums_Pinfty:
  fixes f::"nat \<Rightarrow> ereal"
  assumes "f sums \<infinity>"
    and "\<And>n. \<bar>f n\<bar> \<noteq> \<infinity>"
  shows "(\<lambda>n. - f n) sums -\<infinity>" 
proof -
  define rf where "rf = (\<lambda>n. real_of_ereal (f n))"
  have "\<And>n. f n = ereal (rf n)" unfolding rf_def using assms by (simp add: ereal_real')
  define g where "g = (\<lambda>n. (\<Sum>i \<in> {..< n}. rf i))"
  define gm where "gm = (\<lambda>n. (\<Sum>i \<in> {..< n}. - rf i))"
  have "\<And>n. gm n = - g n" unfolding g_def gm_def by (simp add: sum_negf)  
  hence "\<And>n. ereal (gm n) = (\<Sum>i \<in> {..< n}.- f i)" using \<open>\<And>n. f n = ereal (rf n)\<close>
    using gm_def by auto
  have "(\<lambda>n. ereal (g n)) \<longlonglongrightarrow> \<infinity>" using assms \<open>\<And>n. f n = ereal (rf n)\<close> unfolding sums_def g_def 
    by simp
  have "\<forall>M. \<exists>N. \<forall>n\<ge> N. (gm n) \<le> M" 
  proof
    fix M
    have "\<exists>N. \<forall>n\<ge> N. ereal (-M) \<le> g n" using \<open>g \<longlonglongrightarrow> \<infinity>\<close>  Lim_PInfty by simp
    from this obtain N where "\<forall>n\<ge> N. ereal (-M) \<le> g n" by auto
    hence "\<forall>n \<ge> N. - (g n) \<le> M" by auto
    hence "\<forall>n \<ge> N. gm n \<le> M" using \<open>\<And>n. gm n = - g n\<close> by simp
    thus "\<exists>N. \<forall>n \<ge> N. gm n \<le> M" by auto
  qed
  hence "(\<lambda>n. ereal (gm n)) \<longlonglongrightarrow> -\<infinity>" by (simp add: Lim_MInfty)
  thus ?thesis  using \<open>\<And>n. ereal (gm n) = (\<Sum>i \<in> {..< n}.- f i)\<close> unfolding sums_def by simp
qed

lemma ereal_sums_Minfty:
  fixes f::"nat \<Rightarrow> ereal"
  assumes "f sums -\<infinity>"
    and "\<And>n. \<bar>f n\<bar> \<noteq> \<infinity>"
  shows "(\<lambda>n. - f n) sums \<infinity>" 
proof -
  define rf where "rf = (\<lambda>n. real_of_ereal (f n))"
  have "\<And>n. f n = ereal (rf n)" unfolding rf_def using assms by (simp add: ereal_real')
  define g where "g = (\<lambda>n. (\<Sum>i \<in> {..< n}. rf i))"
  define gm where "gm = (\<lambda>n. (\<Sum>i \<in> {..< n}. - rf i))"
  have "\<And>n. gm n = - g n" unfolding g_def gm_def by (simp add: sum_negf)  
  hence "\<And>n. ereal (gm n) = (\<Sum>i \<in> {..< n}.- f i)" using \<open>\<And>n. f n = ereal (rf n)\<close>
    using gm_def by auto
  have "(\<lambda>n. ereal (g n)) \<longlonglongrightarrow> -\<infinity>" using assms \<open>\<And>n. f n = ereal (rf n)\<close> unfolding sums_def g_def 
    by simp
  have "\<forall>M. \<exists>N. \<forall>n\<ge> N. M \<le> (gm n)" 
  proof
    fix M
    have "\<exists>N. \<forall>n\<ge> N. g n \<le> ereal (-M)" using \<open>g \<longlonglongrightarrow> -\<infinity>\<close>  Lim_MInfty by simp
    from this obtain N where "\<forall>n\<ge> N. g n \<le> ereal (-M)" by auto
    hence "\<forall>n \<ge> N. M \<le> - (g n)" by auto
    hence "\<forall>n \<ge> N. M \<le> gm n" using \<open>\<And>n. gm n = - g n\<close> by simp
    thus "\<exists>N. \<forall>n \<ge> N. M \<le> gm n" by auto
  qed
  hence "(\<lambda>n. ereal (gm n)) \<longlonglongrightarrow> \<infinity>" by (simp add: Lim_PInfty)
  thus ?thesis  using \<open>\<And>n. ereal (gm n) = (\<Sum>i \<in> {..< n}.- f i)\<close> unfolding sums_def by simp
qed

lemma mem_sums_Pinfty:
  assumes "((f i)::ereal) = \<infinity>"
  shows "f sums \<infinity>" 
proof -
  define g where "g = (\<lambda>n. (\<Sum>i \<in> {..< n}. f i))"
  have ginf: "\<forall> j \<ge> Suc i. g j = \<infinity>"
  proof (intro allI impI)
    fix j
    assume "Suc i \<le> j"
    hence "i < j" by simp
    hence "i \<in> {..< j}" by auto
    thus "g j = \<infinity>" unfolding g_def using sum_Pinfty[of f "{..< j}"] assms by blast
  qed
  have "\<forall>M. \<exists>N. \<forall>n\<ge> N. M \<le> (g n)" 
  proof
    fix M
    show "\<exists>N. \<forall>n\<ge> N. M \<le> g n" using ginf by force
  qed
  hence "g \<longlonglongrightarrow> \<infinity>" by (simp add: Lim_PInfty)
  thus ?thesis   unfolding sums_def g_def by simp
qed

lemma sum_Minfty:
  fixes f :: "nat \<Rightarrow> ereal"
  shows "\<And>i. finite P \<Longrightarrow> i \<in> P \<Longrightarrow> f i = - \<infinity> \<Longrightarrow> \<infinity> \<notin> range f \<Longrightarrow> sum f P = -\<infinity>"
proof -
  fix i 
  assume "finite P"
    and "i \<in> P" 
    and "f i = -\<infinity>"
    and "\<infinity> \<notin> range f"
  thus "sum f P = -\<infinity>"
  proof induct
    case empty
    then show ?case by simp
  next
    case (insert x F)
    then show ?case
      by (metis ereal_plus_eq_MInfty insert_iff rangeI sum.insert sum_Pinfty)
  qed
qed

lemma mem_sums_Minfty:
  assumes "((f i)::ereal) = -\<infinity>"
    and "\<infinity> \<notin> range f"
  shows "f sums -\<infinity>" 
proof -
  define g where "g = (\<lambda>n. (\<Sum>i \<in> {..< n}. f i))"
  have ginf: "\<forall> j \<ge> Suc i. g j = -\<infinity>"
  proof (intro allI impI)
    fix j
    assume "Suc i \<le> j"
    hence "i < j" by simp
    hence "i \<in> {..< j}" by auto
    thus "g j = -\<infinity>" unfolding g_def using sum_Minfty[of  "{..< j}"] assms by simp
  qed
  have "\<forall>M. \<exists>N. \<forall>n\<ge> N. (g n) \<le> M" 
  proof
    fix M
    show "\<exists>N. \<forall>n\<ge> N. g n \<le> M" using ginf by force
  qed
  hence "g \<longlonglongrightarrow> -\<infinity>" by (simp add: Lim_MInfty)
  thus ?thesis   unfolding sums_def g_def by simp
qed

lemma ereal_sums_not_infty:
  assumes "f sums (a::ereal)"
    and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "\<And>n. \<bar>f n\<bar> \<noteq> \<infinity>" 
proof (rule ccontr)
  fix n
  assume "\<not>\<bar>f n\<bar> \<noteq> \<infinity>"
  hence "\<bar>f n\<bar> = \<infinity>" by simp
  show False
  proof (cases "f n = \<infinity>")
    case True
    hence "f sums \<infinity>" using mem_sums_Pinfty by simp
    thus False using assms sums_unique2 by force
  next
    case False
    hence "f n = -\<infinity>" using \<open>\<bar>f n\<bar> = \<infinity>\<close> by blast
    show False
    proof (cases "\<exists>i. f i = \<infinity>")
      case True
      from this obtain i where "f i = \<infinity>" by auto
      hence "f sums \<infinity>" using mem_sums_Pinfty by simp
      thus False using assms sums_unique2 by force
    next
      case False
      hence "\<forall>i. f i \<noteq> \<infinity>" by simp
      hence "f sums -\<infinity>" using mem_sums_Minfty \<open>f n = -\<infinity>\<close>
        by (metis MInfty_eq_minfinity image_iff)
      thus False using assms sums_unique2 by force
    qed
  qed
qed

lemma ereal_sums_not_infty_minus:
  assumes "f sums (a::ereal)"
    and "\<bar>a\<bar> \<noteq> \<infinity>"
  shows "(\<lambda>n. - f n) sums -a" 
proof -
  have "\<And>n. \<bar>f n\<bar> \<noteq> \<infinity>" using assms  ereal_sums_not_infty by simp
  define g where "g = (\<lambda>n. real_of_ereal (f n))"
  have "\<And>n. f n = ereal (g n)" using  \<open>\<And>n. \<bar>f n\<bar> \<noteq> \<infinity>\<close> by (simp add: ereal_real' g_def) 
  hence "\<And>n. - f n = ereal (-g n)" by simp
  have "\<exists>r. a = ereal (r)" using assms by auto
  from this obtain r where "a = ereal r" by auto
  hence "f sums (ereal r)" using assms by simp
  hence "(\<lambda>n. ereal (g n)) sums (ereal r)" using \<open>\<And>n. f n = ereal (g n)\<close> 
      sums_cong[of f "\<lambda>n. ereal (g n)"] by simp
  hence "g sums r" by (simp add: sums_ereal) 
  hence "(\<lambda>n. -g n) sums -r" using sums_minus[of g] by simp
  hence "(\<lambda>n. ereal (- g n)) sums ereal (-r)" by (simp add: sums_ereal) 
  hence "(\<lambda>n. - f n) sums (ereal (-r))" using \<open>\<And>n. - f n = ereal (-g n)\<close>
      sums_cong[of f "\<lambda>n. ereal (g n)"] by simp
  thus ?thesis using \<open>a = ereal r\<close> by simp
qed

lemma ereal_sums_minus:
  fixes f::"nat \<Rightarrow> ereal"
  assumes "f sums a"
    and "\<And>n. \<bar>f n\<bar> \<noteq> \<infinity>"
  shows "(\<lambda>n. - f n) sums -a" 
proof (cases "\<bar>a\<bar> = \<infinity>")
  case False
  thus ?thesis using assms ereal_sums_not_infty_minus by simp
next
  case True
  hence "a = \<infinity> \<or> a = - \<infinity>" by auto
  thus ?thesis using assms ereal_sums_Pinfty ereal_sums_Minfty by auto
qed

lemma sums_minus':
  fixes f::"nat \<Rightarrow> ereal"
  assumes "-\<infinity> \<notin> range f \<or> \<infinity> \<notin> range f"
    and "f sums a"
  shows "(\<lambda>n. - f n) sums (- a)"
proof (cases "\<forall>n. \<bar>f n\<bar> \<noteq> \<infinity>")
  case True
  thus ?thesis using ereal_sums_minus assms by simp
next
  case False
  have "\<exists>n. \<bar>f n\<bar> = \<infinity>" using False by simp
  from this obtain n where "\<bar>f n\<bar> = \<infinity>" by meson
  show ?thesis
  proof (cases "\<infinity> \<in> range f")
    case True
    hence "\<exists>j. f j = \<infinity>" by (metis image_iff) 
    from this obtain j where "f j = \<infinity>" by auto
    hence "a = \<infinity>" using mem_sums_Pinfty assms(2) sums_unique2 by blast
    moreover have "-\<infinity> \<notin> range f" using assms True by simp
    ultimately show ?thesis using mem_sums_Minfty[of "\<lambda>n. - f n"] assms \<open>f j = \<infinity>\<close>
      using ereal_uminus_eq_reorder by fastforce
  next
    case False
    hence "f n = -\<infinity>" using \<open>\<bar>f n\<bar> = \<infinity>\<close> by (metis ereal_infinity_cases range_eqI) 
    hence "a = -\<infinity>" using mem_sums_Minfty False sums_unique2 assms(2) by blast 
    thus ?thesis using mem_sums_Pinfty[of "\<lambda>n. - f n"] assms
      by (metis MInfty_eq_minfinity \<open>f n = - \<infinity>\<close> ereal_uminus_uminus uminus_ereal.simps(3))
  qed
qed

end