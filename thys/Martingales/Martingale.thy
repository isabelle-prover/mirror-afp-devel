(*  Author:     Ata Keskin, TU München 
*)

theory Martingale
  imports Stochastic_Process Conditional_Expectation_Banach
begin                

section \<open>Martingales\<close>

text \<open>The following locales are necessary for defining martingales.\<close>

subsection \<open>Additional Locale Definitions\<close>

locale sigma_finite_adapted_process = sigma_finite_filtered_measure M F t\<^sub>0 + adapted_process M F t\<^sub>0 X for M F t\<^sub>0 X

locale nat_sigma_finite_adapted_process = sigma_finite_adapted_process M F "0 :: nat" X for M F X
locale real_sigma_finite_adapted_process = sigma_finite_adapted_process M F "0 :: real" X for M F X

sublocale nat_sigma_finite_adapted_process \<subseteq> nat_sigma_finite_filtered_measure ..
sublocale real_sigma_finite_adapted_process \<subseteq> real_sigma_finite_filtered_measure ..

locale finite_adapted_process = finite_filtered_measure M F t\<^sub>0 + adapted_process M F t\<^sub>0 X for M F t\<^sub>0 X

sublocale finite_adapted_process \<subseteq> sigma_finite_adapted_process ..

locale nat_finite_adapted_process = finite_adapted_process M F "0 :: nat" X for M F X
locale real_finite_adapted_process = finite_adapted_process M F "0 :: real" X for M F X

sublocale nat_finite_adapted_process \<subseteq> nat_sigma_finite_adapted_process ..
sublocale real_finite_adapted_process \<subseteq> real_sigma_finite_adapted_process ..

(* with ordering *)

locale sigma_finite_adapted_process_order = sigma_finite_adapted_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_  \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}" 

locale nat_sigma_finite_adapted_process_order = sigma_finite_adapted_process_order M F "0 :: nat" X for M F X
locale real_sigma_finite_adapted_process_order = sigma_finite_adapted_process_order M F "0 :: real" X for M F X

sublocale nat_sigma_finite_adapted_process_order \<subseteq> nat_sigma_finite_adapted_process ..
sublocale real_sigma_finite_adapted_process_order \<subseteq> real_sigma_finite_adapted_process ..
                                                
locale finite_adapted_process_order = finite_adapted_process M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_  \<Rightarrow> _ \<Rightarrow> _ :: {order_topology, ordered_real_vector}" 

locale nat_finite_adapted_process_order = finite_adapted_process_order M F "0 :: nat" X for M F X
locale real_finite_adapted_process_order = finite_adapted_process_order M F "0 :: real" X for M F X

sublocale nat_finite_adapted_process_order \<subseteq> nat_sigma_finite_adapted_process_order ..
sublocale real_finite_adapted_process_order \<subseteq> real_sigma_finite_adapted_process_order ..

(* with linear ordering *)

locale sigma_finite_adapted_process_linorder = sigma_finite_adapted_process_order M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_  \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

locale nat_sigma_finite_adapted_process_linorder = sigma_finite_adapted_process_linorder M F "0 :: nat" X for M F X
locale real_sigma_finite_adapted_process_linorder = sigma_finite_adapted_process_linorder M F "0 :: real" X for M F X

sublocale nat_sigma_finite_adapted_process_linorder \<subseteq> nat_sigma_finite_adapted_process_order ..
sublocale real_sigma_finite_adapted_process_linorder \<subseteq> real_sigma_finite_adapted_process_order ..

locale finite_adapted_process_linorder = finite_adapted_process_order M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_  \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

locale nat_finite_adapted_process_linorder = finite_adapted_process_linorder M F "0 :: nat" X for M F X
locale real_finite_adapted_process_linorder = finite_adapted_process_linorder M F "0 :: real" X for M F X

sublocale nat_finite_adapted_process_linorder \<subseteq> nat_sigma_finite_adapted_process_linorder ..
sublocale real_finite_adapted_process_linorder \<subseteq> real_sigma_finite_adapted_process_linorder ..

subsection \<open>Martingale\<close>

text \<open>A martingale is an adapted process where the expected value of the next observation, given all past observations, is equal to the current value.\<close>

locale martingale = sigma_finite_adapted_process +
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

locale submartingale = sigma_finite_adapted_process_order +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and submartingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>"

locale submartingale_linorder = submartingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

sublocale martingale_order \<subseteq> submartingale using martingale_property by (unfold_locales) (force simp add: integrable)+
sublocale martingale_linorder \<subseteq> submartingale_linorder ..

subsection \<open>Supermartingale\<close>

text \<open>A supermartingale is an adapted process where the expected value of the next observation, given all past observations, is less than or equal to the current value.\<close>

locale supermartingale = sigma_finite_adapted_process_order +
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and supermartingale_property: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>"

locale supermartingale_linorder = supermartingale M F t\<^sub>0 X for M F t\<^sub>0 and X :: "_ \<Rightarrow> _ \<Rightarrow> _ :: {linorder_topology}"

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
  have "\<integral>x \<in> A. X i x \<partial>M = \<integral>x \<in> A. cond_exp M (F i) (X j) x \<partial>M" using martingale_property[OF assms(2,3)] borel_measurable_cond_exp' assms subalgebras subalgebra_def by (intro set_lebesgue_integral_cong_AE[OF _ random_variable]) fastforce+
  also have "... = \<integral>x \<in> A. X j x \<partial>M" using assms by (auto simp: integrable intro: cond_exp_set_integral[symmetric])
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

lemma (in sigma_finite_adapted_process) martingale_of_cond_exp_diff_eq_zero: 
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and diff_zero: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x = 0"
    shows "martingale M F t\<^sub>0 X"
proof 
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" 
      using diff_zero[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] 
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (intro integrable)

lemma (in sigma_finite_adapted_process) martingale_of_set_integral_eq:
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" 
    shows "martingale M F t\<^sub>0 X"
proof (unfold_locales)
  fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
  interpret sigma_finite_subalgebra M "F i" using asm by blast
  interpret r: sigma_finite_measure "restr_to_subalg M (F i)" by (simp add: sigma_fin_subalg)
  {
    fix A assume "A \<in> restr_to_subalg M (F i)"
    hence *: "A \<in> F i" using sets_restr_to_subalg subalgebras asm by blast 
    have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * subalg asm by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
    also have "... = set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(2)[OF asm] cond_exp_set_integral[OF integrable] asm by auto
    finally have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * subalg by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
  }
  hence "AE \<xi> in restr_to_subalg M (F i). X i \<xi> = cond_exp M (F i) (X j) \<xi>" using asm by (intro r.density_unique_banach, auto intro: integrable_in_subalg subalg borel_measurable_cond_exp integrable)
  thus "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalg] by blast
qed (simp add: integrable)

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
  using submartingale_property[OF assms(2), of j] assms subalgebras
  by (subst sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable assms(1), of j])
     (auto intro!: scaleR_left_mono integral_mono_AE_banach integrable_mult_indicator integrable simp add: subalgebra_def set_lebesgue_integral_def)

lemma max:
  assumes "submartingale_linorder M F t\<^sub>0 Y"
  shows "submartingale_linorder M F t\<^sub>0 (\<lambda>i \<xi>. max (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: submartingale_linorder M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    have "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> max (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)" using submartingale_property Y.submartingale_property asm unfolding max_def by fastforce
    thus "AE \<xi> in M. max (X i \<xi>) (Y i \<xi>) \<le> cond_exp M (F i) (\<lambda>\<xi>. max (X j \<xi>) (Y j \<xi>)) \<xi>" using sigma_finite_subalgebra.cond_exp_max[OF _ integrable Y.integrable, of "F i" j j] asm by (fast intro: order.trans)
  }
  show "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<xi>. max (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma max_0:
  shows "submartingale_linorder M F t\<^sub>0 (\<lambda>i \<xi>. max 0 (X i \<xi>))"
proof -
  interpret zero: martingale_linorder M F t\<^sub>0 "\<lambda>_ _. 0" by (force intro: martingale_linorder.intro martingale_order.intro)
  show ?thesis by (intro zero.max submartingale_linorder.intro submartingale_axioms)
qed

end

lemma (in sigma_finite_adapted_process_order) submartingale_of_cond_exp_diff_nonneg:
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow>  integrable M (X i)" 
      and diff_nonneg: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<ge> 0"
    shows "submartingale M F t\<^sub>0 X"
proof (unfold_locales)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" 
      using diff_nonneg[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i]
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (intro integrable)

lemma (in sigma_finite_adapted_process_linorder) submartingale_of_set_integral_le:
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)"
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)"
    shows "submartingale M F t\<^sub>0 X"
proof (unfold_locales)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    interpret r: sigma_finite_measure "restr_to_subalg M (F i)" using asm sigma_finite_subalgebra.sigma_fin_subalg by blast
    {
      fix A assume "A \<in> restr_to_subalg M (F i)"
      hence *: "A \<in> F i" using asm sets_restr_to_subalg subalgebras by blast
      have "set_lebesgue_integral (restr_to_subalg M (F i)) A (X i) = set_lebesgue_integral M A (X i)" using * asm subalgebras by (auto simp: set_lebesgue_integral_def intro: integral_subalgebra2 borel_measurable_scaleR adapted borel_measurable_indicator) 
      also have "... \<le> set_lebesgue_integral M A (cond_exp M (F i) (X j))" using * assms(2)[OF asm] asm sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable] by fastforce
      also have "... = set_lebesgue_integral (restr_to_subalg M (F i)) A (cond_exp M (F i) (X j))" using * asm subalgebras by (auto simp: set_lebesgue_integral_def intro!: integral_subalgebra2[symmetric] borel_measurable_scaleR borel_measurable_cond_exp borel_measurable_indicator)
      finally have "0 \<le> set_lebesgue_integral (restr_to_subalg M (F i)) A (\<lambda>\<xi>. cond_exp M (F i) (X j) \<xi> - X i \<xi>)" using * asm subalgebras by (subst set_integral_diff, auto simp add: set_integrable_def sets_restr_to_subalg intro!: integrable adapted integrable_in_subalg borel_measurable_scaleR borel_measurable_indicator borel_measurable_cond_exp integrable_mult_indicator)
    }
    hence "AE \<xi> in restr_to_subalg M (F i). 0 \<le> cond_exp M (F i) (X j) \<xi> - X i \<xi>" 
      by (intro r.density_nonneg integrable_in_subalg asm subalgebras borel_measurable_diff borel_measurable_cond_exp adapted Bochner_Integration.integrable_diff integrable_cond_exp integrable)
    thus "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X j) \<xi>" using AE_restr_to_subalg[OF subalgebras] asm by simp
  }
qed (intro integrable)

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
  using supermartingale_property[OF assms(2), of j] assms subalgebras
  by (subst sigma_finite_subalgebra.cond_exp_set_integral[OF _ integrable assms(1), of j])
     (auto intro!: scaleR_left_mono integral_mono_AE_banach integrable_mult_indicator integrable simp add: subalgebra_def set_lebesgue_integral_def)

lemma min:
  assumes "supermartingale_linorder M F t\<^sub>0 Y"
  shows "supermartingale_linorder M F t\<^sub>0 (\<lambda>i \<xi>. min (X i \<xi>) (Y i \<xi>))"
proof (unfold_locales)
  interpret Y: supermartingale_linorder M F t\<^sub>0 Y by (rule assms)
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    have "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> min (cond_exp M (F i) (X j) \<xi>) (cond_exp M (F i) (Y j) \<xi>)" using supermartingale_property Y.supermartingale_property asm unfolding min_def by fastforce
    thus "AE \<xi> in M. min (X i \<xi>) (Y i \<xi>) \<ge> cond_exp M (F i) (\<lambda>\<xi>. min (X j \<xi>) (Y j \<xi>)) \<xi>" using sigma_finite_subalgebra.cond_exp_min[OF _ integrable Y.integrable, of "F i" j j] asm by (fast intro: order.trans)
  }
  show "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>)) \<in> borel_measurable (F i)" "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (\<lambda>\<xi>. min (X i \<xi>) (Y i \<xi>))" by (force intro: Y.integrable integrable assms)+
qed

lemma min_0:
  shows "supermartingale_linorder M F t\<^sub>0 (\<lambda>i \<xi>. min 0 (X i \<xi>))"
proof -
  interpret zero: martingale_linorder M F t\<^sub>0 "\<lambda>_ _. 0" by (force intro: martingale_linorder.intro)
  show ?thesis by (intro zero.min supermartingale_linorder.intro supermartingale_axioms)
qed

end

lemma (in sigma_finite_adapted_process_order) supermartingale_of_cond_exp_diff_le_zero:
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and diff_le_zero: "\<And>i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> AE x in M. cond_exp M (F i) (\<lambda>\<xi>. X j \<xi> - X i \<xi>) x \<le> 0"
    shows "supermartingale M F t\<^sub>0 X"
proof 
  {
    fix i j :: 'b assume asm: "t\<^sub>0 \<le> i" "i \<le> j"
    thus "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X j) \<xi>" 
      using diff_le_zero[OF asm] sigma_finite_subalgebra.cond_exp_diff[OF _ integrable(1,1), of "F i" j i] 
            sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable adapted, of i] by fastforce
  }
qed (intro integrable)

lemma (in sigma_finite_adapted_process_linorder) supermartingale_of_set_integral_ge:
  assumes integrable: "\<And>i. t\<^sub>0 \<le> i \<Longrightarrow> integrable M (X i)" 
      and "\<And>A i j. t\<^sub>0 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow> A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X j) \<le> set_lebesgue_integral M A (X i)" 
    shows "supermartingale M F t\<^sub>0 X"
proof -
  interpret _: adapted_process M F t\<^sub>0 "-X" by (rule uminus_adapted)
  interpret uminus_X: sigma_finite_adapted_process_linorder M F t\<^sub>0 "-X" ..
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "supermartingale M F t\<^sub>0 (-(- X))"
    using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(2)] *[symmetric]]] subalgebras
    by (intro submartingale.uminus uminus_X.submartingale_of_set_integral_le) 
       (clarsimp simp add: fun_Compl_def subalgebra_def integrable | fastforce)+
  thus ?thesis unfolding fun_Compl_def by simp
qed

text \<open>Many of the statements we have made concerning martingales can be simplified when the indexing set is the natural numbers. 
      Given a point in time \<^term>\<open>i \<in> \<nat>\<close>, it suffices to consider the successor \<^term>\<open>i + 1\<close>, instead of all future times \<^term>\<open>j \<ge> i\<close>.\<close>

subsection \<open>Discrete Time Martingales\<close>

locale nat_martingale = martingale M F "0 :: nat" X for M F X
locale nat_submartingale = submartingale M F "0 :: nat" X for M F X
locale nat_supermartingale = supermartingale M F "0 :: nat" X for M F X

locale nat_submartingale_linorder = submartingale_linorder M F "0 :: nat" X for M F X
locale nat_supermartingale_linorder = supermartingale_linorder M F "0 :: nat" X for M F X

sublocale nat_submartingale_linorder \<subseteq> nat_submartingale ..
sublocale nat_supermartingale_linorder \<subseteq> nat_supermartingale ..

text \<open>A predictable martingale is necessarily constant.\<close>
lemma (in nat_martingale) predictable_const:
  assumes "nat_predictable_process M F X"
  shows "AE \<xi> in M. X i \<xi> = X j \<xi>"
proof -
  have *: "AE \<xi> in M. X i \<xi> = X 0 \<xi>" for i
  proof (induction i)
    case 0
    then show ?case by (simp add: bot_nat_def)
  next
    case (Suc i)
    interpret S: nat_adapted_process M F "\<lambda>i. X (Suc i)" by (intro nat_predictable_process.adapted_Suc assms)
    show ?case using Suc S.adapted[of i] martingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
  qed
  show ?thesis using *[of i] *[of j] by force
qed

lemma (in nat_sigma_finite_adapted_process) martingale_of_set_integral_eq_Suc:
  assumes integrable: "\<And>i. integrable M (X i)"
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X (Suc i))" 
    shows "nat_martingale M F X"
proof (intro nat_martingale.intro martingale_of_set_integral_eq)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) = set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF _ le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(2)[THEN trans])
  qed
qed (simp add: integrable)

lemma (in nat_sigma_finite_adapted_process) martingale_nat:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "nat_martingale M F X"
proof (unfold_locales)
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
    have *: "AE \<xi> in M. cond_exp M (F (n + i)) (X j) \<xi> = X (n + i) \<xi>" unfolding j using assms(2)[THEN AE_symmetric] by blast
    have "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (cond_exp M (F (n + i)) (X j)) \<xi>" by (intro cond_exp_nested_subalg integrable subalg, simp add: subalgebra_def sets_F_mono)
    hence "AE \<xi> in M. cond_exp M (F i) (X j) \<xi> = cond_exp M (F i) (X (n + i)) \<xi>" using cond_exp_cong_AE[OF integrable_cond_exp integrable *] by force
    thus ?case using Suc(1)[OF n] by fastforce
  qed
qed (simp add: integrable)

lemma (in nat_sigma_finite_adapted_process) martingale_of_cond_exp_diff_Suc_eq_zero:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> = 0" 
    shows "nat_martingale M F X"
proof (intro martingale_nat integrable) 
  fix i 
  show "AE \<xi> in M. X i \<xi> = cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(2)[of i] by fastforce
qed

subsection \<open>Discrete Time Submartingales\<close>

lemma (in nat_submartingale) predictable_mono:
  assumes "nat_predictable_process M F X" "i \<le> j"
  shows "AE \<xi> in M. X i \<xi> \<le> X j \<xi>"
  using assms(2)
proof (induction "j - i" arbitrary: i j)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  hence *: "n = j - Suc i" by linarith
  interpret S: nat_adapted_process M F "\<lambda>i. X (Suc i)" by (intro nat_predictable_process.adapted_Suc assms)
  have "Suc i \<le> j" using Suc(2,3) by linarith
  thus ?case using Suc(1)[OF *] S.adapted[of i] submartingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
qed

lemma (in nat_sigma_finite_adapted_process_linorder) submartingale_of_set_integral_le_Suc:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X (Suc i))" 
    shows "nat_submartingale M F X"
proof (intro nat_submartingale.intro submartingale_of_set_integral_le)
  fix i j A assume asm: "i \<le> j" "A \<in> sets (F i)"
  show "set_lebesgue_integral M A (X i) \<le> set_lebesgue_integral M A (X j)" using asm
  proof (induction "j - i" arbitrary: i j)
    case 0
    then show ?case using asm by simp
  next
    case (Suc n)
    hence *: "n = j - Suc i" by linarith
    have "Suc i \<le> j" using Suc(2,3) by linarith
    thus ?case using sets_F_mono[OF _ le_SucI] Suc(4) Suc(1)[OF *] by (auto intro: assms(2)[THEN order_trans])
  qed
qed (simp add: integrable)

lemma (in nat_sigma_finite_adapted_process_linorder) submartingale_nat:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "nat_submartingale M F X"
  using subalg integrable assms(2)
  by (intro submartingale_of_set_integral_le_Suc ord_le_eq_trans[OF set_integral_mono_AE_banach cond_exp_set_integral[symmetric]], simp)
     (meson in_mono integrable_mult_indicator set_integrable_def subalgebra_def, meson integrable_cond_exp in_mono integrable_mult_indicator set_integrable_def subalgebra_def, fast+)

lemma (in nat_sigma_finite_adapted_process_linorder) submartingale_of_cond_exp_diff_Suc_nonneg:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> \<ge> 0" 
    shows "nat_submartingale M F X"
proof (intro submartingale_nat integrable) 
  fix i 
  show "AE \<xi> in M. X i \<xi> \<le> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(2)[of i] by fastforce
qed

lemma (in nat_submartingale_linorder) partial_sum_scaleR:
  assumes "nat_adapted_process M F C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "nat_submartingale M F (\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
proof-
  interpret C: nat_adapted_process M F C by (rule assms)
  interpret C': nat_adapted_process M F "\<lambda>i \<xi>. C (i - 1) \<xi> *\<^sub>R (X i \<xi> - X (i - 1) \<xi>)" by (intro nat_adapted_process.intro adapted_process.scaleR_right_adapted adapted_process.diff_adapted, unfold_locales) (auto intro: adaptedD C.adaptedD)+
  interpret C'': nat_adapted_process M F "\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>)" by (rule C'.partial_sum_Suc_adapted[unfolded diff_Suc_1])
  interpret S: nat_sigma_finite_adapted_process_linorder M F "(\<lambda>n \<xi>. \<Sum>i<n. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))" ..
  have "integrable M (\<lambda>x. C i x *\<^sub>R (X (Suc i) x - X i x))" for i using assms(2,3)[of i] by (intro Bochner_Integration.integrable_bound[OF integrable_scaleR_right, OF Bochner_Integration.integrable_diff, OF integrable(1,1), of R "Suc i" i]) (auto simp add: mult_mono)
  moreover have "AE \<xi> in M. 0 \<le> cond_exp M (F i) (\<lambda>\<xi>. (\<Sum>i<Suc i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>)) - (\<Sum>i<i. C i \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))) \<xi>" for i 
    using sigma_finite_subalgebra.cond_exp_measurable_scaleR[OF _ calculation _ C.adapted, of i] 
          cond_exp_diff_nonneg[OF _ le_SucI, OF _ order.refl, of i] assms(2,3)[of i] by (fastforce simp add: scaleR_nonneg_nonneg integrable)
  ultimately show ?thesis by (intro S.submartingale_of_cond_exp_diff_Suc_nonneg Bochner_Integration.integrable_sum, blast+)
qed

lemma (in nat_submartingale_linorder) partial_sum_scaleR':
  assumes "nat_predictable_process M F C" "\<And>i. AE \<xi> in M. 0 \<le> C i \<xi>" "\<And>i. AE \<xi> in M. C i \<xi> \<le> R"
  shows "nat_submartingale M F (\<lambda>n \<xi>. \<Sum>i<n. C (Suc i) \<xi> *\<^sub>R (X (Suc i) \<xi> - X i \<xi>))"
proof -
  interpret C: nat_predictable_process M F C by (rule assms)
  interpret Suc_C: nat_adapted_process M F "\<lambda>i. C (Suc i)" using C.adapted_Suc .
  show ?thesis by (intro partial_sum_scaleR[of _ R] assms) (intro_locales)
qed

subsection \<open>Discrete Time Supermartingales\<close>

lemma (in nat_supermartingale) predictable_mono:
  assumes "nat_predictable_process M F X" "i \<le> j"
  shows "AE \<xi> in M. X i \<xi> \<ge> X j \<xi>"
  using assms(2)
proof (induction "j - i" arbitrary: i j)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  hence *: "n = j - Suc i" by linarith
  interpret S: nat_adapted_process M F "\<lambda>i. X (Suc i)" by (intro nat_predictable_process.adapted_Suc assms)
  have "Suc i \<le> j" using Suc(2,3) by linarith
  thus ?case using Suc(1)[OF *] S.adapted[of i] supermartingale_property[OF _ le_SucI, of i] sigma_finite_subalgebra.cond_exp_F_meas[OF _ integrable, of "F i" "Suc i"] by fastforce
qed
  
lemma (in nat_sigma_finite_adapted_process_linorder) supermartingale_of_set_integral_ge_Suc:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>A i. A \<in> F i \<Longrightarrow> set_lebesgue_integral M A (X i) \<ge> set_lebesgue_integral M A (X (Suc i))" 
    shows "nat_supermartingale M F X"
proof -
  interpret _: adapted_process M F 0 "-X" by (rule uminus_adapted)
  interpret uminus_X: nat_sigma_finite_adapted_process_linorder M F "-X" ..
  note * = set_integral_uminus[unfolded set_integrable_def, OF integrable_mult_indicator[OF _ integrable]]
  have "nat_supermartingale M F (-(- X))" 
    using ord_eq_le_trans[OF * ord_le_eq_trans[OF le_imp_neg_le[OF assms(2)] *[symmetric]]] subalgebras
    by (intro nat_supermartingale.intro submartingale.uminus nat_submartingale.axioms uminus_X.submartingale_of_set_integral_le_Suc) 
       (clarsimp simp add: fun_Compl_def subalgebra_def integrable | fastforce)+
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma (in nat_sigma_finite_adapted_process_linorder) supermartingale_nat:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" 
    shows "nat_supermartingale M F X"
proof -
  interpret _: adapted_process M F 0 "-X" by (rule uminus_adapted)
  interpret uminus_X: nat_sigma_finite_adapted_process_linorder M F "-X" ..
  have "AE \<xi> in M. - X i \<xi> \<le> cond_exp M (F i) (\<lambda>x. - X (Suc i) x) \<xi>" for i using assms(2) cond_exp_uminus[OF integrable, of i "Suc i"] by force
  hence "nat_supermartingale M F (-(- X))" by (intro nat_supermartingale.intro submartingale.uminus nat_submartingale.axioms uminus_X.submartingale_nat) (auto simp add: fun_Compl_def integrable)
  thus ?thesis unfolding fun_Compl_def by simp
qed

lemma (in nat_sigma_finite_adapted_process_linorder) supermartingale_of_cond_exp_diff_Suc_le_zero:
  assumes integrable: "\<And>i. integrable M (X i)" 
      and "\<And>i. AE \<xi> in M. cond_exp M (F i) (\<lambda>\<xi>. X (Suc i) \<xi> - X i \<xi>) \<xi> \<le> 0" 
    shows "nat_supermartingale M F X"
proof (intro supermartingale_nat integrable) 
  fix i
  show "AE \<xi> in M. X i \<xi> \<ge> cond_exp M (F i) (X (Suc i)) \<xi>" using cond_exp_diff[OF integrable(1,1), of i "Suc i" i] cond_exp_F_meas[OF integrable adapted, of i] assms(2)[of i] by fastforce
qed

end