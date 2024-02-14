(*  Author:     Ata Keskin, TU München 
*)

theory Martingale
  imports Stochastic_Process Conditional_Expectation_Banach
begin                

section \<open>Martingales\<close>

text \<open>The following locales are necessary for defining martingales.\<close>

subsection \<open>Martingale\<close>

text \<open>A martingale is an adapted process where the expected value of the next observation, given all past observations, is equal to the current value.\<close>

locale martingale = sigma_finite_filtered_measure + adapted_process +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and martingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>"

locale martingale_order = martingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}"
locale martingale_linorder = martingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology, ordered_real_vector}"
sublocale martingale_linorder \<subseteq> martingale_order ..

lemma (in sigma_finite_filtered_measure) martingale_const_fun[intro]:  
  assumes "integrable M f" "f \<in> borel_measurable (F t\<^sub>0)"
  shows "martingale M F t\<^sub>0 (\<lambda>_. f)"
  using assms sigma_finite_subalgebra.cond_exp_F_meas[OF _ assms(1), THEN AE_symmetric] borel_measurable_mono
  by (unfold_locales) blast+

lemma (in sigma_finite_filtered_measure) martingale_cond_exp[intro]:  
  assumes "integrable M f"
  shows "martingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)"
  using sigma_finite_subalgebra.borel_measurable_cond_exp' borel_measurable_cond_exp 
  by (unfold_locales) (auto intro: sigma_finite_subalgebra.cond_exp_nested_subalg[OF _ assms] simp add: subalgebra_F subalgebras)

corollary (in sigma_finite_filtered_measure) martingale_zero[intro]: "martingale M F t\<^sub>0 (\<lambda>_ _. 0)" by fastforce

corollary (in finite_filtered_measure) martingale_const[intro]: "martingale M F t\<^sub>0 (\<lambda>_ _. c)" by fastforce

subsection \<open>Submartingale\<close>

text \<open>A submartingale is an adapted process where the expected value of the next observation, given all past observations, is greater than or equal to the current value.\<close>

locale submartingale = sigma_finite_filtered_measure M F t\<^sub>0 + adapted_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}" +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and submartingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>"

locale submartingale_linorder = submartingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

lemma (in sigma_finite_filtered_measure) submartingale_const_fun[intro]:  
  assumes "integrable M f" "f \<in> borel_measurable (F t\<^sub>0)"
  shows "submartingale M F t\<^sub>0 (\<lambda>_. f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>_. f" using assms by (rule martingale_const_fun)
  show "submartingale M F t\<^sub>0 (\<lambda>_. f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

lemma (in sigma_finite_filtered_measure) submartingale_cond_exp[intro]:  
  assumes "integrable M f"
  shows "submartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>i. cond_exp M (F i) f" using assms by (rule martingale_cond_exp)
  show "submartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

corollary (in finite_filtered_measure) submartingale_const[intro]: "submartingale M F t\<^sub>0 (\<lambda>_ _. c)" by fastforce

sublocale martingale_order \<subseteq> submartingale using martingale_property by (unfold_locales) (force simp add: integrable)+
sublocale martingale_linorder \<subseteq> submartingale_linorder ..

subsection \<open>Supermartingale\<close>

text \<open>A supermartingale is an adapted process where the expected value of the next observation, given all past observations, is less than or equal to the current value.\<close>

locale supermartingale = sigma_finite_filtered_measure M F t\<^sub>0 + adapted_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}" +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and supermartingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>"

locale supermartingale_linorder = supermartingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

lemma (in sigma_finite_filtered_measure) supermartingale_const_fun[intro]:  
  assumes "integrable M f" "f \<in> borel_measurable (F t\<^sub>0)"
  shows "supermartingale M F t\<^sub>0 (\<lambda>_. f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>_. f" using assms by (rule martingale_const_fun)
  show "supermartingale M F t\<^sub>0 (\<lambda>_. f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

lemma (in sigma_finite_filtered_measure) supermartingale_cond_exp[intro]:  
  assumes "integrable M f"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)"
proof -
  interpret martingale M F t\<^sub>0 "\<lambda>i. cond_exp M (F i) f" using assms by (rule martingale_cond_exp)
  show "supermartingale M F t\<^sub>0 (\<lambda>i. cond_exp M (F i) f)" using martingale_property by (unfold_locales) (force simp add: integrable)+
qed

corollary (in finite_filtered_measure) supermartingale_const[intro]: "supermartingale M F t\<^sub>0 (\<lambda>_ _. c)" by fastforce

sublocale martingale_order \<subseteq> supermartingale using martingale_property by (unfold_locales) (force simp add: integrable)+
sublocale martingale_linorder \<subseteq> supermartingale_linorder ..

text \<open>A stochastic process is a martingale, if and only if it is both a submartingale and a supermartingale.\<close>

lemma martingale_iff: 
  shows "martingale M F t\<^sub>0 X \<longleftrightarrow> submartingale M F t\<^sub>0 X \<and> supermartingale M F t\<^sub>0 X"
proof (rule iffI)
  assume asm: "martingale M F t\<^sub>0 X"
  interpret martingale_order M F t\<^sub>0 X by (intro martingale_order.intro asm)
  show "submartingale M F t\<^sub>0 X \<and> supermartingale M F t\<^sub>0 X" using submartingale_axioms supermartingale_axioms by blast
next
  assume asm: "submartingale M F t\<^sub>0 X \<and> supermartingale M F t\<^sub>0 X"
  interpret submartingale M F t\<^sub>0 X by (simp add: asm)
  interpret supermartingale M F t\<^sub>0 X by (simp add: asm)
  show "martingale M F t\<^sub>0 X" using submartingale_property supermartingale_property by (unfold_locales) (intro integrable, blast, force)
qed

subsection \<open>Martingale Lemmas\<close>

text \<open>In the following segment, we cover basic properties of martingales.\<close>

context martingale
begin

lemma cond_exp_diff_eq_zero:
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) \<xi> = 0"
  using martingale_property[OF assms] assms
        sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i]
        sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] by fastforce

lemma set_integral_eq:
  assumes "A \<in> F i" "t\<^sub>0 \<le> i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)"
proof -
  interpret sigma_finite_subalgebra M "F i" using assms(2) by blast
  have "(\<integral>x \<in> A. X i x \<partial>M) = (\<integral>x \<in> A. cond_exp M (F i) (X j) x \<partial>M)" using martingale_property[OF assms(2,3)] borel_measurable_cond_exp' assms subalgebras subalgebra_def by (intro set_lebesgue_integral_cong_AE[OF _ random_variable]) fastforce+
  also have "... = (\<integral>x \<in> A. X j x \<partial>M)" using assms by (auto simp: integrable intro: cond_exp_set_integral[symmetric])
  finally show ?thesis .
qed

lemma scaleR_const[intro]:
  shows "martingale M F t\<^sub>0 (\<lambda>i x. c *\<^sub>R X i x)"
proof -
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    interpret sigma_finite_subalgebra M "F i" using asm by blast
    have "AE x in M. c *\<^sub>R X i x = cond_exp M (F i) (\<lambda>x. c *\<^sub>R X j x) x" using asm cond_exp_scaleR_right[OF integrable, of j, THEN AE_symmetric] martingale_property[OF asm] by force
  }
  thus ?thesis by (unfold_locales) (auto simp add: integrable martingale.integrable)
qed

lemma uminus[intro]:
  shows "martingale M F t\<^sub>0 (- X)" 
  using scaleR_const[of "-1"] by (force intro: back_subst[of "martingale M F t\<^sub>0"])

lemma add[intro]:
  assumes "martingale M F t\<^sub>0 Y"
  shows "martingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: martingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> + Y i \<xi> = cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_add[OF _ integrable martingale.integrable[OF assms], of "F i" j j, THEN AE_symmetric]
            martingale_property[OF asm] martingale.martingale_property[OF assms asm] by force
  }
  thus ?thesis using assms
  by (unfold_locales) (auto simp add: integrable martingale.integrable)
qed

lemma diff[intro]:
  assumes "martingale M F t\<^sub>0 Y"
  shows "martingale M F t\<^sub>0 (\<lambda>i x. X i x - Y i x)"
proof -
  interpret Y: martingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> - Y i \<xi> = cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_diff[OF _ integrable martingale.integrable[OF assms], of "F i" j j, THEN AE_symmetric] 
            martingale_property[OF asm] martingale.martingale_property[OF assms asm] by fastforce
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: integrable martingale.integrable)  
qed

end

text \<open>Using properties of the conditional expectation, we present the following alternative characterizations of martingales.\<close>

lemma (in sigma_finite_filtered_measure) martingale_of_cond_exp_diff_eq_zero: 
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and diff_zero: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x = 0"
    shows "martingale M F t\<^sub>0 X"
proof
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" 
      using diff_zero[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] 
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

lemma (in sigma_finite_filtered_measure) martingale_of_set_integral_eq:
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" 
    shows "martingale M F t\<^sub>0 X"
proof (unfold_locales)
  fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  interpret sigma_finite_subalgebra M "F i" using asm by blast
  interpret r: sigma_finite_measure "restr_to_subalg M (F i)" by (simp add: sigma_fin_subalg)
  {
    fix A assume "A \<in> restr_to_subalg M (F i)"
    hence *: "A \<in> F i" using sets_restr_to_subalg subalgebras asm by blast 
    have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * subalg asm by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
    also have "... = set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(3)[OF asm] cond_exp_set_integral[OF integrable] asm by auto
    finally have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * subalg by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
  }
  hence "AE \<xi> in restr_to_subalg M (F i). X i \<xi> = cond_exp M (F i) (X j) \<xi>" using asm by (intro r.density_unique_banach, auto intro: integrable_in_subalg subalg borel_measurable_cond_exp integrable)
  thus "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalg] by blast
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

subsection \<open>Submartingale Lemmas\<close>

context submartingale
begin

lemma cond_exp_diff_nonneg:
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<ge> 0"
  using submartingale_property[OF assms] assms sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of _ j i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce

lemma add[intro]:
  assumes "submartingale M F t\<^sub>0 Y"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: submartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> + Y i \<xi> \<le> cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_add[OF _ integrable submartingale.integrable[OF assms], of "F i" j j] 
            submartingale_property[OF asm] submartingale.submartingale_property[OF assms asm] add_mono[of "X i _" _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_add random_variable adapted integrable Y.random_variable Y.adapted submartingale.integrable)  
qed

lemma diff[intro]:
  assumes "supermartingale M F t\<^sub>0 Y"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
proof -
  interpret Y: supermartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> - Y i \<xi> \<le> cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_diff[OF _ integrable supermartingale.integrable[OF assms], of "F i" j j] 
            submartingale_property[OF asm] supermartingale.supermartingale_property[OF assms asm] diff_mono[of "X i _" _ _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_diff random_variable adapted integrable Y.random_variable Y.adapted supermartingale.integrable)  
qed

lemma scaleR_nonneg: 
  assumes "c \<ge> 0"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<le> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>"  
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] submartingale_property[OF asm] by (fastforce intro!: scaleR_left_mono[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma scaleR_le_zero: 
  assumes "c \<le> 0"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<ge> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] submartingale_property[OF asm] 
            by (fastforce intro!: scaleR_left_mono_neg[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma uminus[intro]:
  shows "supermartingale M F t\<^sub>0 (- X)"
  unfolding fun_Compl_def using scaleR_le_zero[of "-1"] by simp

end

context submartingale_linorder
begin

lemma set_integral_le:
  assumes "A \<in> F i" "t\<^sub>0 \<le> i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)"  
  using submartingale_property[OF assms(2), of j] assms subsetD[OF sets_F_subset]
  by (subst sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable assms(1), of j])
     (auto intro!: scaleR_left_mono integral_mono_AE_banach integrable_mult_indicator integrable simp add: set_lebesgue_integral_def)

lemma max:
  assumes "submartingale M F t\<^sub>0 Y"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. max (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: submartingale_linorder M F t\<^sub>0 Y by (intro submartingale_linorder.intro assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    have "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> max (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)" using submartingale_property Y.submartingale_property asm unfolding max_def by fastforce
    thus "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> cond_exp M (F i) (\<lambda>\<xi>. max (X j \<xi>) (Y j \<xi>)) \<xi>" using sigma_finite_subalgebra.cond_exp_max[OF _ integrable Y.integrable, of "F i" j j] asm by (fast intro: order.trans)
  }
  show "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma max_0:
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. max 0 (X i \<xi>))"
proof -
  interpret zero: martingale_linorder M F t\<^sub>0 "\<lambda>_ _. 0" by (force intro: martingale_linorder.intro martingale_order.intro)
  show ?thesis by (intro zero.max submartingale_linorder.intro submartingale_axioms)
qed

end

lemma (in sigma_finite_filtered_measure) submartingale_of_cond_exp_diff_nonneg:
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow>  integrable M (X i)" 
      and diff_nonneg: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<ge> 0"
    shows "submartingale M F t\<^sub>0 X"
proof (unfold_locales)
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" 
      using diff_nonneg[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i]
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

lemma (in sigma_finite_filtered_measure) submartingale_of_set_integral_le:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)"
    shows "submartingale M F t\<^sub>0 X"
proof (unfold_locales)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    interpret adapted_process M F t\<^sub>0 X by (rule adapted)
    interpret r: sigma_finite_measure "restr_to_subalg M (F i)" using asm sigma_finite_subalgebra.sigma_fin_subalg by blast
    {
      fix A assume "A \<in> restr_to_subalg M (F i)"
      hence *: "A \<in> F i" using asm sets_restr_to_subalg subalgebras by blast
      have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * asm subalgebras by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
      also have "... \<le> set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(3)[OF asm] asm sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable] by fastforce
      also have "... = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * asm subalgebras by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
      finally have "0 \<le> set_lebesgue_integral (restr_to_subalg M (F i)) A (\<lambda>\<xi>. cond_exp M (F i) (X j) \<xi> - X i \<xi>)" using * asm subalgebras by (subst set_integral_diff, auto simp add: set_integrable_def sets_restr_to_subalg intro!: integrable adapted integrable_in_subalg borel_measurable_scaleR borel_measurable_indicator borel_measurable_cond_exp integrable_mult_indicator)
    }
    hence "AE \<xi> in restr_to_subalg M (F i). 0 \<le> cond_exp M (F i) (X j) \<xi> - X i \<xi>"
      by (intro r.density_nonneg integrable_in_subalg asm subalgebras borel_measurable_diff borel_measurable_cond_exp adapted Bochner_Integration.integrable_diff integrable_cond_exp integrable)  
    thus "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalgebras] asm by simp
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

subsection \<open>Supermartingale Lemmas\<close>

text \<open>The following lemmas are exact duals of the ones for submartingales.\<close>

context supermartingale
begin

lemma cond_exp_diff_nonneg:
  assumes "t\<^sub>0 \<le> i" "i \<le> j"
  shows "AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X i \<xi> - X j \<xi>) x \<ge> 0"
  using assms supermartingale_property[OF assms] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" i j] 
        sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce

lemma add[intro]:
  assumes "supermartingale M F t\<^sub>0 Y"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> + Y i \<xi>)"
proof -
  interpret Y: supermartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> + Y i \<xi> \<ge> cond_exp M (F i) (\<lambda>x. X j x + Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_add[OF _ integrable supermartingale.integrable[OF assms], of "F i" j j] 
            supermartingale_property[OF asm] supermartingale.supermartingale_property[OF assms asm] add_mono[of _ "X i _" _ "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_add random_variable adapted integrable Y.random_variable Y.adapted supermartingale.integrable)  
qed

lemma diff[intro]:
  assumes "submartingale M F t\<^sub>0 Y"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. X i \<xi> - Y i \<xi>)"
proof -
  interpret Y: submartingale M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    hence "AE \<xi> in M. X i \<xi> - Y i \<xi> \<ge> cond_exp M (F i) (\<lambda>x. X j x - Y j x) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_diff[OF _ integrable submartingale.integrable[OF assms], of "F i" j j, unfolded fun_diff_def] 
            supermartingale_property[OF asm] submartingale.submartingale_property[OF assms asm] diff_mono[of _ "X i _" "Y i _"] by force
  }
  thus ?thesis using assms by (unfold_locales) (auto simp add: borel_measurable_diff random_variable adapted integrable Y.random_variable Y.adapted submartingale.integrable)  
qed

lemma scaleR_nonneg: 
  assumes "c \<ge> 0"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<ge> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>"
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] supermartingale_property[OF asm] by (fastforce intro!: scaleR_left_mono[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma scaleR_le_zero: 
  assumes "c \<le> 0"
  shows "submartingale M F t\<^sub>0 (\<lambda>i \<xi>. c *\<^sub>R X i \<xi>)"
proof
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. c *\<^sub>R X i \<xi> \<le> cond_exp M (F i) (\<lambda>\<xi>. c *\<^sub>R X j \<xi>) \<xi>" 
      using sigma_finite_subalgebra.cond_exp_scaleR_right[OF _ integrable, of "F i" j c] supermartingale_property[OF asm] by (fastforce intro!: scaleR_left_mono_neg[OF _ assms])
  }
qed (auto simp add: borel_measurable_integrable borel_measurable_scaleR integrable random_variable adapted borel_measurable_const_scaleR)

lemma uminus[intro]:
  shows "submartingale M F t\<^sub>0 (- X)"
  unfolding fun_Compl_def using scaleR_le_zero[of "-1"] by simp

end

context supermartingale_linorder
begin

lemma set_integral_ge:
  assumes "A \<in> F i" "t\<^sub>0 \<le> i" "i \<le> j"
  shows "set_lebesgue_integral M A (X i) \<ge> set_lebesgue_integral M A (X j)"
  using supermartingale_property[OF assms(2), of j] assms subsetD[OF sets_F_subset]
  by (subst sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable assms(1), of j])
     (auto intro!: scaleR_left_mono integral_mono_AE_banach integrable_mult_indicator integrable simp add: set_lebesgue_integral_def)

lemma min:
  assumes "supermartingale M F t\<^sub>0 Y"
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. min (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: supermartingale_linorder M F t\<^sub>0 Y by (intro supermartingale_linorder.intro assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    have "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> min (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)" using supermartingale_property Y.supermartingale_property asm unfolding min_def by fastforce
    thus "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> cond_exp M (F i) (\<lambda>\<xi>. min (X j \<xi>) (Y j \<xi>)) \<xi>" using sigma_finite_subalgebra.cond_exp_min[OF _ integrable Y.integrable, of "F i" j j] asm by (fast intro: order.trans)
  }
  show "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma min_0:
  shows "supermartingale M F t\<^sub>0 (\<lambda>i \<xi>. min 0 (X i \<xi>))"
proof -
  interpret zero: martingale_linorder M F t\<^sub>0 "\<lambda>_ _. 0" by (force intro: martingale_linorder.intro)
  show ?thesis by (intro zero.min supermartingale_linorder.intro supermartingale_axioms)
qed

end

lemma (in sigma_finite_filtered_measure) supermartingale_of_cond_exp_diff_le_zero:
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and diff_le_zero: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<le> 0"
    shows "supermartingale M F t\<^sub>0 X"
proof 
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>" 
      using diff_le_zero[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] 
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (auto intro: integrable adapted[THEN adapted_process.adapted])

lemma (in sigma_finite_filtered_measure) supermartingale_of_set_integral_ge:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F t\<^sub>0 X"
      and integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X j) \<le> set_lebesgue_integral M A (X i)" 
    shows "supermartingale M F t\<^sub>0 X"
proof -
  interpret adapted_process M F t\<^sub>0 X by (rule adapted)
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "supermartingale M F t\<^sub>0 (-(- X))"
    using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(3)] *[symmetric]]] sets_F_subset[THEN subsetD]
    by (intro submartingale.uminus submartingale_of_set_integral_le[OF uminus_adapted]) 
       (clarsimp simp add: fun_Compl_def integrable | fastforce)+
  thus ?thesis unfolding fun_Compl_def by simp
qed

text \<open>Many of the statements we have made concerning martingales can be simplified when the indexing set is the natural numbers. 
      Given a point in time \<^term>\<open>i \<in> \<nat>\<close>, it suffices to consider the successor \<^term>\<open>i + 1\<close>, instead of all future times \<^term>\<open>j \<ge> i\<close>.\<close>

subsection \<open>Discrete Time Martingales\<close>

context nat_sigma_finite_filtered_measure
begin

text \<open>A predictable martingale is necessarily constant.\<close>
lemma predictable_const:
  assumes "martingale M F 0 X" 
    and "predictable_process M F 0 X"
  shows "AE \<xi> in M. X i \<xi> = X j \<xi>"
proof -
  interpret martingale M F 0 X by (rule assms)
  have *: "AE \<xi> in M. X i \<xi> = X 0 \<xi>" for i
  proof (induction i)
    case 0
    then show ?case by (simp add: bot_nat_def)
  next
    case (Suc i)
    interpret S: adapted_process M F 0 "\<lambda>i. X (Suc i)" by (intro predictable_implies_adapted_Suc assms)
    show ?case using Suc S.adapted[of i] martingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
  qed
  show ?thesis using *[of i] *[of j] by force
qed

lemma martingale_of_set_integral_eq_Suc:
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)"
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X (Suc i))" 
    shows "martingale M F 0 X"
proof (intro martingale_of_set_integral_eq adapted integrable)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF _ le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(3)[THEN trans])
  qed
qed

lemma martingale_nat:
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "martingale M F 0 X"
proof (unfold_locales)
  interpret adapted_process M F 0 X by (rule adapted)
  fix i j :: nat assume asm: "i \<le> j"
  show "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    hence "j = i" by simp
    thus ?case using sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, THEN AE_symmetric] by blast
  next
    case (Suc n)
    have j: "j = Suc (n + i)" using Suc by linarith
    have n: "n = n + i - i" using Suc by linarith
    have *: "AE \<xi> in M. cond_exp M (F (n + i)) (X j) \<xi> = X (n + i) \<xi>" unfolding j using assms(3)[THEN AE_symmetric] by blast
    have "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (cond_exp M (F (n + i)) (X j)) \<xi>" by (intro cond_exp_nested_subalg integrable subalg, simp add: subalgebra_def sets_F_mono)
    hence "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (X (n + i)) \<xi>" using cond_exp_cong_AE[OF integrable_cond_exp integrable *] by force
    thus ?case using Suc(1)[OF n] by fastforce
  qed
qed (auto simp add: integrable adapted[THEN adapted_process.adapted])

lemma martingale_of_cond_exp_diff_Suc_eq_zero:
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> = 0" 
    shows "martingale M F 0 X"
proof (intro martingale_nat integrable adapted)
  interpret adapted_process M F 0 X by (rule adapted)
  fix i 
  show "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(3)[of i] by fastforce
qed

end

subsection \<open>Discrete Time Submartingales\<close>

context nat_sigma_finite_filtered_measure
begin

lemma predictable_mono:
  assumes "submartingale M F 0 X"
    and "predictable_process M F 0 X" "i \<le> j"
  shows "AE \<xi> in M. X i \<xi> \<le> X j \<xi>"
  using assms(3)
proof (induction "j - i" arbitrary: i j)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  hence *: "n = j - Suc i" by linarith
  interpret submartingale M F 0 X by (rule assms)
  interpret S: adapted_process M F 0 "\<lambda>i. X (Suc i)" by (intro predictable_implies_adapted_Suc assms)
  have "Suc i \<le> j" using Suc(2,3) by linarith
  thus ?case using Suc(1)[OF *] S.adapted[of i] submartingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
qed

lemma submartingale_of_set_integral_le_Suc:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X (Suc i))" 
    shows "submartingale M F 0 X"
proof (intro submartingale_of_set_integral_le adapted integrable)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF _ le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(3)[THEN order_trans])
  qed
qed

lemma submartingale_nat:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "submartingale M F 0 X"
proof -
  show ?thesis using subalg assms(3) integrable
    by (intro submartingale_of_set_integral_le_Suc adapted integrable ord_le_eq_trans[OF set_integral_mono_AE_banach cond_exp_set_integral[symmetric]])
       (meson in_mono integrable_mult_indicator set_integrable_def subalgebra_def, meson integrable_cond_exp in_mono integrable_mult_indicator set_integrable_def subalgebra_def, fast+)
qed

lemma submartingale_of_cond_exp_diff_Suc_nonneg:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> \<ge> 0" 
    shows "submartingale M F 0 X"
proof (intro submartingale_nat integrable adapted)
  interpret adapted_process M F 0 X by (rule assms)
  fix i 
  show "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(3)[of i] by fastforce
qed

lemma submartingale_partial_sum_scaleR:
  assumes "submartingale_linorder M F 0 X"
    and "adapted_process M F 0 C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "submartingale M F 0 (\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
proof -
  interpret submartingale_linorder M F 0 X by (rule assms)
  interpret C: adapted_process M F 0 C by (rule assms)
  interpret C': adapted_process M F 0 "\<lambda>i \<xi>. C (i - 1) \<xi> *\<^sub>R (X i \<xi> - X (i - 1) \<xi>)" by (intro adapted_process.scaleR_right_adapted adapted_process.diff_adapted, unfold_locales) (auto intro: adaptedD C.adaptedD)+
  interpret S: adapted_process M F 0 "\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>)" using C'.adapted_process_axioms[THEN partial_sum_Suc_adapted] diff_Suc_1 by simp
  have "integrable M (\<lambda>x. C i x *\<^sub>R (X (Suc i) x - X i x))" for i using assms(3,4)[of i] by (intro Bochner_Integration.integrable_bound[OF integrable_scaleR_right, OF Bochner_Integration.integrable_diff, OF integrable(1,1), of R "Suc i" i]) (auto simp add: mult_mono)
  moreover have "AE \<xi> in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. (\<Sum>i<Suc i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>)) - (\<Sum>i<i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))) \<xi>" for i 
    using sigma_finite_subalgebra.cond_exp_measurable_scaleR[OF _ calculation _ C.adapted, of i] 
          cond_exp_diff_nonneg[OF _ le_SucI, OF _ order.refl, of i] assms(3,4)[of i] by (fastforce simp add: scaleR_nonneg_nonneg integrable)
  ultimately show ?thesis by (intro submartingale_of_cond_exp_diff_Suc_nonneg S.adapted_process_axioms Bochner_Integration.integrable_sum, blast+)
qed

lemma submartingale_partial_sum_scaleR':
  assumes "submartingale_linorder M F 0 X"
    and "predictable_process M F 0 C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "submartingale M F 0 (\<lambda>n \<xi>. \<Sum>i<n. C (Suc i) \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
proof -
  interpret Suc_C: adapted_process M F 0 "\<lambda>i. C (Suc i)" using predictable_implies_adapted_Suc assms by blast
  show ?thesis by (intro submartingale_partial_sum_scaleR[OF assms(1), of _ R] assms) (intro_locales)
qed

end

subsection \<open>Discrete Time Supermartingales\<close>

context nat_sigma_finite_filtered_measure
begin

lemma predictable_mono':
  assumes "supermartingale M F 0 X"
    and "predictable_process M F 0 X" "i \<le> j"
  shows "AE \<xi> in M. X i \<xi> \<ge> X j \<xi>"
  using assms(3)
proof (induction "j - i" arbitrary: i j)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  hence *: "n = j - Suc i" by linarith
  interpret supermartingale M F 0 X by (rule assms)
  interpret S: adapted_process M F 0 "\<lambda>i. X (Suc i)" by (intro predictable_implies_adapted_Suc assms)
  have "Suc i \<le> j" using Suc(2,3) by linarith
  thus ?case using Suc(1)[OF *] S.adapted[of i] supermartingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
qed
  
lemma supermartingale_of_set_integral_ge_Suc:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<ge> set_lebesgue_integral M A (X (Suc i))" 
    shows "supermartingale M F 0 X"
proof -
  interpret adapted_process M F 0 X by (rule assms)
  interpret uminus_X: adapted_process M F 0 "-X" by (rule uminus_adapted)
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "supermartingale M F 0 (-(- X))" 
    using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(3)] *[symmetric]]] sets_F_subset[THEN subsetD]
    by (intro submartingale.uminus submartingale_of_set_integral_le_Suc[OF uminus_adapted]) 
       (clarsimp simp add: fun_Compl_def integrable | fastforce)+
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma supermartingale_nat:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "supermartingale M F 0 X"
proof -
  interpret adapted_process M F 0 X by (rule assms)
  have "AE \<xi> in M. - X i \<xi> \<le> cond_exp M (F i) (\<lambda>x. - X (Suc i) x) \<xi>" for i using assms(3) cond_exp_uminus[OF integrable, of i "Suc i"] by force
  hence "supermartingale M F 0 (-(- X))" by (intro submartingale.uminus submartingale_nat[OF uminus_adapted]) (auto simp add: fun_Compl_def integrable)
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma supermartingale_of_cond_exp_diff_Suc_le_zero:
  fixes X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"
  assumes adapted: "adapted_process M F 0 X"
      and integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> \<le> 0" 
    shows "supermartingale M F 0 X"
proof (intro supermartingale_nat integrable adapted) 
  interpret adapted_process M F 0 X by (rule assms)
  fix i
  show "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(3)[of i] by fastforce
qed

end

end