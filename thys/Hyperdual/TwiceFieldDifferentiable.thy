(*  Title:   TwiceFieldDifferentiable.thy
    Authors: Jacques Fleuriot and Filip Smola, University of Edinburgh, 2020
*)

section \<open>Twice Field Differentiable\<close>

theory TwiceFieldDifferentiable
  imports "HOL-Analysis.Analysis"
begin

subsection\<open>Differentiability on a Set\<close>

text\<open>A function is differentiable on a set iff it is differentiable at any point within that set.\<close>
definition field_differentiable_on :: "('a \<Rightarrow> 'a::real_normed_field) \<Rightarrow> 'a set \<Rightarrow> bool"
  (infix "field'_differentiable'_on" 50)
  where "f field_differentiable_on s \<equiv> \<forall>x\<in>s. f field_differentiable (at x within s)"

text\<open>This is preserved for subsets.\<close>
lemma field_differentiable_on_subset:
  assumes "f field_differentiable_on S"
      and "T \<subseteq> S"
    shows "f field_differentiable_on T"
  by (meson assms field_differentiable_on_def field_differentiable_within_subset in_mono)

subsection\<open>Twice Differentiability\<close>
text\<open>
  Informally, a function is twice differentiable at x iff it is differentiable on some neighbourhood
  of x and its derivative is differentiable at x.
\<close>
definition twice_field_differentiable_at :: "['a \<Rightarrow> 'a::real_normed_field, 'a ] \<Rightarrow> bool"
  (infixr "(twice'_field'_differentiable'_at)" 50)
  where "f twice_field_differentiable_at x \<equiv>
           \<exists>S. f field_differentiable_on S \<and> x \<in> interior S \<and> (deriv f) field_differentiable (at x)"

lemma once_field_differentiable_at:
  "f twice_field_differentiable_at x \<Longrightarrow> f field_differentiable (at x)"
  by (metis at_within_interior field_differentiable_on_def interior_subset subsetD twice_field_differentiable_at_def)

lemma deriv_field_differentiable_at:
  "f twice_field_differentiable_at x \<Longrightarrow> deriv f field_differentiable (at x)"
  using twice_field_differentiable_at_def by blast

text\<open>
  For a composition of two functions twice differentiable at x, the chain rule eventually holds on
  some neighbourhood of x.
\<close>
lemma eventually_deriv_compose:
  assumes "\<exists>S. f field_differentiable_on S \<and> x \<in> interior S"
      and "g twice_field_differentiable_at (f x)"
    shows "\<forall>\<^sub>F x in nhds x. deriv (\<lambda>x. g (f x)) x = deriv g (f x) * deriv f x"
proof -
  obtain S S'
   where Df_on_S:  "f field_differentiable_on S" and x_int_S: "x \<in> interior S"
     and Dg_on_S': "g field_differentiable_on S'" and fx_int_S': "f x \<in> interior S'"
    using assms twice_field_differentiable_at_def by blast

  let ?T = "{x \<in> interior S. f x \<in> interior S'}"

  have "continuous_on (interior S) f"
    by (meson Df_on_S continuous_on_eq_continuous_within continuous_on_subset field_differentiable_imp_continuous_at
         field_differentiable_on_def interior_subset)
  then have "open (interior S \<inter> {x. f x \<in> interior S'})"
    by (metis continuous_open_preimage open_interior vimage_def)
  then have x_int_T: "x \<in> interior ?T"
    by (metis (no_types) Collect_conj_eq Collect_mem_eq Int_Collect fx_int_S' interior_eq x_int_S)
  moreover have  Dg_on_fT: "g field_differentiable_on f`?T"
   by (metis (no_types, lifting) Dg_on_S' field_differentiable_on_subset image_Collect_subsetI interior_subset)
  moreover have Df_on_T: "f field_differentiable_on ?T"
    using  field_differentiable_on_subset Df_on_S
    by (metis Collect_subset interior_subset)
  moreover have "\<forall>x \<in> interior ?T. deriv (\<lambda>x. g (f x)) x = deriv g (f x) * deriv f x"
  proof
    fix x
    assume x_int_T: "x \<in> interior ?T"
    have "f field_differentiable at x"
      by (metis (no_types, lifting) Df_on_T at_within_interior field_differentiable_on_def
          interior_subset subsetD x_int_T)
    moreover have "g field_differentiable at (f x)"
      by (metis (no_types, lifting) Dg_on_S' at_within_interior field_differentiable_on_def
          interior_subset mem_Collect_eq subsetD x_int_T)
    ultimately have "deriv (g \<circ> f) x = deriv g (f x) * deriv f x"
      using deriv_chain[of f x g] by simp
    then show "deriv (\<lambda>x. g (f x)) x = deriv g (f x) * deriv f x"
      by (simp add: comp_def)
  qed
  ultimately show ?thesis
    using eventually_nhds by blast
qed

lemma eventually_deriv_compose':
  assumes "f twice_field_differentiable_at x"
      and "g twice_field_differentiable_at (f x)"
    shows "\<forall>\<^sub>F x in nhds x. deriv (\<lambda>x. g (f x)) x = deriv g (f x) * deriv f x"
  using assms eventually_deriv_compose twice_field_differentiable_at_def by blast

text\<open>Composition of twice differentiable functions is twice differentiable.\<close>
lemma twice_field_differentiable_at_compose:
  assumes "f twice_field_differentiable_at x"
      and "g twice_field_differentiable_at (f x)"
    shows "(\<lambda>x. g (f x)) twice_field_differentiable_at x"
proof -
  obtain S S'
   where Df_on_S:  "f field_differentiable_on S" and x_int_S: "x \<in> interior S"
     and Dg_on_S': "g field_differentiable_on S'" and fx_int_S': "f x \<in> interior S'"
    using assms twice_field_differentiable_at_def by blast

  let ?T = "{x \<in> interior S. f x \<in> interior S'}"

  have "continuous_on (interior S) f"
    by (meson Df_on_S continuous_on_eq_continuous_within continuous_on_subset field_differentiable_imp_continuous_at
         field_differentiable_on_def interior_subset)
  then have "open (interior S \<inter> {x. f x \<in> interior S'})"
    by (metis continuous_open_preimage open_interior vimage_def)
  then have x_int_T: "x \<in> interior ?T"
    by (metis (no_types) Collect_conj_eq Collect_mem_eq Int_Collect fx_int_S' interior_eq x_int_S)

  have  Dg_on_fT: "g field_differentiable_on f`?T"
    by (metis (no_types, lifting) Dg_on_S' field_differentiable_on_subset image_Collect_subsetI interior_subset)

  have Df_on_T: "f field_differentiable_on ?T"
    using  field_differentiable_on_subset Df_on_S
    by (metis Collect_subset interior_subset)

  have "(\<lambda>x. g (f x)) field_differentiable_on ?T"
    unfolding field_differentiable_on_def
  proof
    fix x assume x_int: "x \<in> {x \<in> interior S. f x \<in> interior S'}"
    have "f field_differentiable at x"
      by (metis Df_on_S at_within_interior field_differentiable_on_def interior_subset mem_Collect_eq subsetD x_int)
    moreover have "g field_differentiable at (f x)"
      by (metis Dg_on_S' at_within_interior field_differentiable_on_def interior_subset mem_Collect_eq subsetD x_int)
    ultimately have "(g \<circ> f) field_differentiable at x"
      by (simp add: field_differentiable_compose)
    then have "(\<lambda>x. g (f x)) field_differentiable at x"
      by (simp add: comp_def)
    then show "(\<lambda>x. g (f x)) field_differentiable at x within {x \<in> interior S. f x \<in> interior S'}"
      using field_differentiable_at_within by blast
  qed
  moreover have "deriv (\<lambda>x. g (f x)) field_differentiable at x"
  proof -
    have "(\<lambda>x. deriv g (f x)) field_differentiable at x"
      by (metis DERIV_chain2 assms deriv_field_differentiable_at field_differentiable_def once_field_differentiable_at)
    then have "(\<lambda>x. deriv g (f x) * deriv f x) field_differentiable at x"
      using assms field_differentiable_mult[of "\<lambda>x. deriv g (f x)"]
      by (simp add: deriv_field_differentiable_at)
    moreover have "deriv (deriv (\<lambda>x. g (f x))) x = deriv (\<lambda>x. deriv g (f x) * deriv f x) x"
      using assms Df_on_S x_int_S deriv_cong_ev eventually_deriv_compose by fastforce
    ultimately show ?thesis
      using assms eventually_deriv_compose DERIV_deriv_iff_field_differentiable Df_on_S x_int_S
            DERIV_cong_ev[of x x "deriv (\<lambda>x. g (f x))" "\<lambda>x. deriv g (f x) * deriv f x"]
      by blast
  qed
  ultimately show ?thesis
    using twice_field_differentiable_at_def x_int_T by blast
qed

subsubsection\<open>Constant\<close>
lemma twice_field_differentiable_at_const [simp, intro]:
  "(\<lambda>x. a) twice_field_differentiable_at x"
  by (auto intro: exI [of _ UNIV] simp add: twice_field_differentiable_at_def field_differentiable_on_def)

subsubsection\<open>Identity\<close>
lemma twice_field_differentiable_at_ident [simp, intro]:
  "(\<lambda>x. x) twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. (\<lambda>x. x) field_differentiable at x"
   and "deriv ((\<lambda>x. x)) field_differentiable at x"
    by simp_all
  then show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by fastforce
qed

subsubsection\<open>Constant Multiplication\<close>
lemma twice_field_differentiable_at_cmult [simp, intro]:
"(*) k twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. (*) k field_differentiable at x"
    by simp
  moreover have "deriv ((*) k) field_differentiable at x"
    by simp
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by fastforce
qed

lemma twice_field_differentiable_at_uminus [simp, intro]:
  "uminus twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. uminus field_differentiable at x"
    by (simp add: field_differentiable_minus)
  moreover have "deriv uminus field_differentiable at x"
    by simp
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by auto
qed

lemma twice_field_differentiable_at_uminus_fun [intro]:
  assumes "f twice_field_differentiable_at x"
    shows "(\<lambda>x. - f x) twice_field_differentiable_at x"
  by (simp add: assms twice_field_differentiable_at_compose)

subsubsection\<open>Real Scaling\<close>

lemma deriv_scaleR_right_id [simp]:
  "(deriv ((*\<^sub>R) k)) = (\<lambda>z. k *\<^sub>R 1)"
  using DERIV_imp_deriv has_field_derivative_scaleR_right DERIV_ident by blast

lemma deriv_deriv_scaleR_right_id [simp]:
  "deriv (deriv ((*\<^sub>R) k)) = (\<lambda>z. 0)"
  by simp

lemma deriv_scaleR_right:
  "f field_differentiable (at z) \<Longrightarrow> deriv (\<lambda>x. k *\<^sub>R f x) z = k *\<^sub>R deriv f z"
  by (simp add: DERIV_imp_deriv field_differentiable_derivI has_field_derivative_scaleR_right)

lemma field_differentiable_scaleR_right [intro]:
  "f field_differentiable F \<Longrightarrow> (\<lambda>x. c *\<^sub>R f x) field_differentiable F"
  using field_differentiable_def has_field_derivative_scaleR_right by blast

lemma has_field_derivative_scaleR_deriv_right:
  assumes "f twice_field_differentiable_at z"
  shows "((\<lambda>x. k *\<^sub>R deriv f x) has_field_derivative k *\<^sub>R deriv (deriv f) z) (at z)"
  by (simp add: DERIV_deriv_iff_field_differentiable assms deriv_field_differentiable_at has_field_derivative_scaleR_right)

lemma deriv_scaleR_deriv_right:
  assumes "f twice_field_differentiable_at z"
  shows "deriv (\<lambda>x. k *\<^sub>R deriv f x) z = k *\<^sub>R deriv (deriv f) z"
  using assms deriv_scaleR_right twice_field_differentiable_at_def by blast

lemma twice_field_differentiable_at_scaleR [simp, intro]:
  "(*\<^sub>R) k twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. (*\<^sub>R) k field_differentiable at x"
    by (simp add: field_differentiable_scaleR_right)
  moreover have "deriv ((*\<^sub>R) k) field_differentiable at x"
    by simp
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by auto
qed

lemma twice_field_differentiable_at_scaleR_fun [simp, intro]:
  assumes "f twice_field_differentiable_at x"
  shows "(\<lambda>x. k *\<^sub>R f x) twice_field_differentiable_at x"
  by (simp add: assms twice_field_differentiable_at_compose)

subsubsection\<open>Addition\<close>

lemma eventually_deriv_add:
  assumes "f twice_field_differentiable_at x"
      and "g twice_field_differentiable_at x"
    shows "\<forall>\<^sub>F x in nhds x. deriv (\<lambda>x. f x + g x) x = deriv f x + deriv g x"
proof -
  obtain S where Df_on_S: "f field_differentiable_on S" and x_int_S: "x \<in> interior S"
    using assms twice_field_differentiable_at_def by blast
  obtain S' where Dg_on_S: "g field_differentiable_on S'" and x_int_S': "x \<in> interior S'"
    using assms twice_field_differentiable_at_def by blast
  have "x \<in> interior (S \<inter> S')"
     by (simp add: x_int_S x_int_S')
  moreover have Df_on_SS': "f field_differentiable_on (S \<inter> S')"
     by (meson Df_on_S IntD1 field_differentiable_on_def field_differentiable_within_subset inf_sup_ord(1))
  moreover have Dg_on_SS': "g field_differentiable_on (S \<inter> S')"
     by (meson Dg_on_S IntD2 field_differentiable_on_def field_differentiable_within_subset inf_le2)
  moreover have "open (interior (S \<inter> S'))"
    by blast
  moreover have "\<forall>x\<in> interior (S \<inter> S'). deriv (\<lambda>x. f x + g x) x = deriv f x + deriv g x"
    by (metis (full_types) Df_on_SS' Dg_on_SS' at_within_interior deriv_add field_differentiable_on_def in_mono interior_subset)
  ultimately show ?thesis
    using eventually_nhds by blast
qed

lemma twice_field_differentiable_at_add [intro]:
  assumes "f twice_field_differentiable_at x"
      and "g twice_field_differentiable_at x"
    shows "(\<lambda>x. f x + g x) twice_field_differentiable_at x"
proof -
  obtain S S'
   where Df_on_S:  "f field_differentiable_on S" and x_int_S: "x \<in> interior S"
     and Dg_on_S': "g field_differentiable_on S'" and x_int_S': " x \<in> interior S'"
    using assms twice_field_differentiable_at_def by blast

  let ?T = "interior (S \<inter> S')"

  have x_int_T: "x \<in> interior ?T"
     by (simp add: x_int_S x_int_S')

  have Df_on_T: "f field_differentiable_on ?T"
    by (meson Df_on_S field_differentiable_on_subset inf_sup_ord(1) interior_subset)
  have  Dg_on_fT: "g field_differentiable_on ?T"
    by (meson Dg_on_S' field_differentiable_on_subset interior_subset le_infE)

   have "(\<lambda>x. f x + g x) field_differentiable_on ?T"
     unfolding field_differentiable_on_def
  proof
    fix x assume x_in_T: "x \<in> ?T"
    have "f field_differentiable at x"
      by (metis x_in_T Df_on_T at_within_open field_differentiable_on_def open_interior)
    moreover have "g field_differentiable at x"
      by (metis x_in_T Dg_on_fT at_within_open field_differentiable_on_def open_interior)
    ultimately have "(\<lambda>x. f x + g x) field_differentiable at x"
      by (simp add: field_differentiable_add)
    then show "(\<lambda>x. f x + g x) field_differentiable at x within ?T"
      using field_differentiable_at_within by blast
  qed
  moreover have "deriv (\<lambda>x. f x + g x) field_differentiable at x"
  proof -
    have "deriv (\<lambda>x. f x + g x) x = deriv f x + deriv g x"
      by (simp add: assms once_field_differentiable_at)
    moreover have "(\<lambda>x. deriv f x + deriv g x) field_differentiable at x"
      by (simp add: field_differentiable_add assms deriv_field_differentiable_at)
    ultimately show ?thesis
      using assms DERIV_deriv_iff_field_differentiable
            DERIV_cong_ev[of x x "deriv (\<lambda>x. f x + g x)" "\<lambda>x. deriv f x + deriv g x"]
      by (simp add: eventually_deriv_add field_differentiable_def)
  qed
  ultimately show ?thesis
    using twice_field_differentiable_at_def x_int_T by blast
qed

lemma deriv_add_id_const [simp]:
  "deriv (\<lambda>x. x + a) = (\<lambda>z. 1)"
  using ext trans[OF deriv_add] by force

lemma deriv_deriv_add_id_const [simp]:
  "deriv (deriv (\<lambda>x. x + a)) z = 0"
  by simp

lemma twice_field_differentiable_at_cadd [simp]:
  "(\<lambda>x. x + a) twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. (\<lambda>x. x + a) field_differentiable at x"
    by (simp add: field_differentiable_add)
  moreover have "deriv ((\<lambda>x. x + a)) field_differentiable at x"
    by (simp add: ext)
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by auto
qed

subsubsection\<open>Linear Function\<close>
lemma twice_field_differentiable_at_linear [simp, intro]:
  "(\<lambda>x. k * x + a) twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. (\<lambda>x. k * x + a) field_differentiable at x"
    by (simp add: field_differentiable_add)
  moreover have "deriv ((\<lambda>x. k * x + a)) field_differentiable at x"
  proof -
    have "deriv ((\<lambda>x. k * x + a)) = (\<lambda>x. k)"
      by (simp add: ext)
    then show ?thesis
      by simp
  qed
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by auto
qed

lemma twice_field_differentiable_at_linearR [simp, intro]:
  "(\<lambda>x. k *\<^sub>R x + a) twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. (\<lambda>x. k *\<^sub>R x + a) field_differentiable at x"
    by (simp add: field_differentiable_scaleR_right field_differentiable_add)
  moreover have "deriv ((\<lambda>x. k *\<^sub>R x + a)) field_differentiable at x"
  proof -
    have "deriv ((\<lambda>x. k *\<^sub>R x + a)) = (\<lambda>x. k *\<^sub>R 1)"
      by (simp add: ext once_field_differentiable_at)
    then show ?thesis
      by simp
  qed
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by auto
qed

subsubsection\<open>Multiplication\<close>

lemma eventually_deriv_mult:
  assumes "f twice_field_differentiable_at x"
      and "g twice_field_differentiable_at x"
    shows "\<forall>\<^sub>F x in nhds x. deriv (\<lambda>x. f x * g x) x = f x * deriv g x + deriv f x * g x"
proof -
  obtain S and S'
    where "f field_differentiable_on S"   and in_S:  "x \<in> interior S"
      and "g field_differentiable_on S'"  and in_S': "x \<in> interior S'"
    using assms twice_field_differentiable_at_def by blast
  then have Df_on_SS': "f field_differentiable_on (S \<inter> S')"
        and Dg_on_SS': "g field_differentiable_on (S \<inter> S')"
    using field_differentiable_on_subset by blast+

  have "\<forall>x\<in> interior (S \<inter> S'). deriv (\<lambda>x. f x * g x) x = f x * deriv g x + deriv f x * g x"
  proof
    fix x assume "x \<in> interior (S \<inter> S')"
    then have "f field_differentiable (at x)"
          and "g field_differentiable (at x)"
      using Df_on_SS' Dg_on_SS' field_differentiable_on_def at_within_interior interior_subset subsetD by metis+
    then show "deriv (\<lambda>x. f x * g x) x = f x * deriv g x + deriv f x * g x"
      by simp
  qed
  moreover have "x \<in> interior (S \<inter> S')"
    by (simp add: in_S in_S')
  moreover have "open (interior (S \<inter> S'))"
    by blast
  ultimately show ?thesis
    using eventually_nhds by blast
qed

lemma twice_field_differentiable_at_mult [intro]:
  assumes "f twice_field_differentiable_at x"
      and "g twice_field_differentiable_at x"
    shows "(\<lambda>x. f x * g x) twice_field_differentiable_at x"
proof -
  obtain S S'
   where Df_on_S:  "f field_differentiable_on S" and x_int_S: "x \<in> interior S"
     and Dg_on_S': "g field_differentiable_on S'" and x_int_S': " x \<in> interior S'"
    using assms twice_field_differentiable_at_def by blast

  let ?T = "interior (S \<inter> S')"

  have x_int_T: "x \<in> interior ?T"
     by (simp add: x_int_S x_int_S')

  have Df_on_T: "f field_differentiable_on ?T"
    by (meson Df_on_S field_differentiable_on_subset inf_sup_ord(1) interior_subset)
  have  Dg_on_fT: "g field_differentiable_on ?T"
    by (meson Dg_on_S' field_differentiable_on_subset interior_subset le_infE)

   have "(\<lambda>x. f x * g x) field_differentiable_on ?T"
     unfolding field_differentiable_on_def
  proof
    fix x assume x_in_T: "x \<in> ?T"
    have "f field_differentiable at x"
      by (metis x_in_T Df_on_T at_within_open field_differentiable_on_def open_interior)
    moreover have "g field_differentiable at x"
      by (metis x_in_T Dg_on_fT at_within_open field_differentiable_on_def open_interior)
    ultimately have "(\<lambda>x. f x * g x) field_differentiable at x"
      by (simp add: field_differentiable_mult)
    then show "(\<lambda>x. f x * g x) field_differentiable at x within ?T"
      using field_differentiable_at_within by blast
  qed
  moreover have "deriv (\<lambda>x. f x * g x) field_differentiable at x"
  proof -
    have "deriv (\<lambda>x. f x * g x) x = f x * deriv g x + deriv f x * g x"
      by (simp add: assms once_field_differentiable_at)
    moreover have "(\<lambda>x. f x * deriv g x + deriv f x * g x) field_differentiable at x"
      by (rule field_differentiable_add, simp_all add: field_differentiable_mult assms once_field_differentiable_at deriv_field_differentiable_at)
    ultimately show ?thesis
      using assms DERIV_deriv_iff_field_differentiable
            DERIV_cong_ev[of x x "deriv (\<lambda>x. f x * g x)" "\<lambda>x. f x * deriv g x + deriv f x * g x"]
      by (simp add: eventually_deriv_mult field_differentiable_def)
  qed
  ultimately show ?thesis
    using twice_field_differentiable_at_def x_int_T by blast
qed

subsubsection\<open>Sine and Cosine\<close>

lemma deriv_sin [simp]: "deriv sin a = cos a"
  by (simp add: DERIV_imp_deriv)

lemma deriv_sinf [simp]: "deriv sin = (\<lambda>x. cos x)"
  by auto

lemma deriv_cos [simp]: "deriv cos a = - sin a"
  by (simp add: DERIV_imp_deriv)

lemma deriv_cosf [simp]: "deriv cos = (\<lambda>x. - sin x)"
  by auto

lemma deriv_sin_minus [simp]:
  "deriv (\<lambda>x. - sin x) a = - deriv (\<lambda>x. sin x) a"
  by (simp add: DERIV_imp_deriv Deriv.field_differentiable_minus)

lemma twice_field_differentiable_at_sin [simp, intro]:
  "sin twice_field_differentiable_at x"
  by (auto intro!: exI [of _ UNIV] simp add: field_differentiable_at_sin
      field_differentiable_on_def twice_field_differentiable_at_def field_differentiable_at_cos)

lemma twice_field_differentiable_at_sin_fun [intro]:
  assumes "f twice_field_differentiable_at x"
  shows   "(\<lambda>x. sin (f x)) twice_field_differentiable_at x"
  by (simp add: assms twice_field_differentiable_at_compose)

lemma twice_field_differentiable_at_cos [simp, intro]:
  "cos twice_field_differentiable_at x"
  by (auto intro!: exI [of _ UNIV] simp add:  field_differentiable_within_sin field_differentiable_minus
      field_differentiable_on_def twice_field_differentiable_at_def field_differentiable_at_cos)

lemma twice_field_differentiable_at_cos_fun [intro]:
  assumes "f twice_field_differentiable_at x"
  shows   "(\<lambda>x. cos (f x)) twice_field_differentiable_at x"
  by (simp add: assms twice_field_differentiable_at_compose)

subsubsection\<open>Exponential\<close>

lemma deriv_exp [simp]: "deriv exp x = exp x"
  using DERIV_exp DERIV_imp_deriv by blast

lemma deriv_expf [simp]: "deriv exp = exp"
  by (simp add: ext)

lemma deriv_deriv_exp [simp]: "deriv (deriv exp) x = exp x"
  by simp

lemma twice_field_differentiable_at_exp [simp, intro]:
  "exp twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. exp field_differentiable at x"
   and "deriv exp field_differentiable at x"
    by (simp_all add: field_differentiable_within_exp)
  then show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by auto
qed

lemma twice_field_differentiable_at_exp_fun [simp, intro]:
  assumes "f twice_field_differentiable_at x"
  shows "(\<lambda>x. exp (f x)) twice_field_differentiable_at x"
  by (simp add: assms twice_field_differentiable_at_compose)

subsubsection\<open>Square Root\<close>

lemma deriv_real_sqrt [simp]: "x > 0 \<Longrightarrow> deriv sqrt x = inverse (sqrt x) / 2"
  using DERIV_imp_deriv DERIV_real_sqrt by blast

lemma has_real_derivative_inverse_sqrt:
  assumes "x > 0"
  shows "((\<lambda>x. inverse (sqrt x) / 2) has_real_derivative - (inverse (sqrt x ^ 3) / 4)) (at x)"
proof -
  have inv_sqrt_mult: "(inverse (sqrt x)/2) * (sqrt x * 2) = 1"
    using assms by simp
  have inv_sqrt_mult2: "(- inverse ((sqrt x)^3)/2)* x * (sqrt x * 2) = -1"
    using assms by (simp add: field_simps power3_eq_cube)
  then show ?thesis
    using assms by (safe intro!: DERIV_imp_deriv derivative_eq_intros)
        (auto intro: derivative_eq_intros inv_sqrt_mult [THEN ssubst] inv_sqrt_mult2 [THEN ssubst]
              simp add: divide_simps power3_eq_cube)
qed

lemma deriv_deriv_real_sqrt':
  assumes "x > 0"
  shows "deriv (\<lambda>x. inverse (sqrt x) / 2) x = - inverse ((sqrt x)^3)/4"
  by (simp add: DERIV_imp_deriv assms has_real_derivative_inverse_sqrt)

lemma has_real_derivative_deriv_sqrt:
  assumes "x > 0"
  shows "(deriv sqrt has_real_derivative - inverse (sqrt x ^ 3) / 4) (at x)"
proof -
  have "((\<lambda>x. inverse (sqrt x) / 2) has_real_derivative - inverse (sqrt x ^ 3) / 4) (at x)"
    using assms has_real_derivative_inverse_sqrt by auto
  moreover
  {fix xa :: real
   assume "xa \<in> {0<..}"
   then have "inverse (sqrt xa) / 2 = deriv sqrt xa"
     by simp
  }
  ultimately show ?thesis
    using has_field_derivative_transform_within_open [where S="{0 <..}" and f="(\<lambda>x. inverse (sqrt x) / 2)"]
    by (meson assms greaterThan_iff open_greaterThan)
qed

lemma deriv_deriv_real_sqrt [simp]:
  assumes "x > 0"
  shows "deriv(deriv sqrt) x = - inverse ((sqrt x)^3)/4"
  using DERIV_imp_deriv assms has_real_derivative_deriv_sqrt by blast

lemma twice_field_differentiable_at_sqrt [simp, intro]:
  assumes "x > 0"
    shows "sqrt twice_field_differentiable_at x"
proof -
  have "sqrt field_differentiable_on {0<..}"
    by (metis DERIV_real_sqrt at_within_open field_differentiable_def field_differentiable_on_def
        greaterThan_iff open_greaterThan)
  moreover have "x \<in> interior {0<..}"
    by (metis assms greaterThan_iff interior_interior interior_real_atLeast)
  moreover have "deriv sqrt field_differentiable at x"
    using assms field_differentiable_def has_real_derivative_deriv_sqrt by blast
  ultimately show ?thesis
    using twice_field_differentiable_at_def by blast
qed

lemma twice_field_differentiable_at_sqrt_fun [intro]:
  assumes "f twice_field_differentiable_at x"
    and "f x > 0"
  shows "(\<lambda>x. sqrt (f x)) twice_field_differentiable_at x"
  by (simp add: assms(1) assms(2) twice_field_differentiable_at_compose)

subsubsection\<open>Natural Power\<close>

lemma field_differentiable_power [simp]:
  "(\<lambda>x. x ^ n) field_differentiable at x"
  using DERIV_power DERIV_ident field_differentiable_def
  by blast

lemma deriv_power_fun [simp]:
  assumes "f field_differentiable at x"
    shows "deriv (\<lambda>x. f x ^ n) x = of_nat n * deriv f x * f x ^ (n - 1)"
  using DERIV_power[of f "deriv f x"]
  by (simp add:  DERIV_imp_deriv assms field_differentiable_derivI mult.assoc [symmetric])

lemma deriv_power [simp]:
  "deriv (\<lambda>x. x ^ n) x = of_nat n * x ^ (n - 1)"
  using DERIV_power[of "\<lambda>x. x" 1] DERIV_imp_deriv by force

lemma deriv_deriv_power [simp]:
  "deriv (deriv (\<lambda>x. x ^ n)) x = of_nat n * of_nat (n - Suc 0) * x ^ (n - 2)"
proof -
  have "(\<lambda>x. x ^ (n - 1)) field_differentiable at x"
    by simp
  then have "deriv (\<lambda>x. of_nat n * x ^ (n - 1)) x = of_nat n * of_nat (n - Suc 0) * x ^ (n - 2)"
    by (simp add: diff_diff_add mult.assoc numeral_2_eq_2)
  then show ?thesis
    by (simp add: ext[OF deriv_power])
qed

lemma twice_field_differentiable_at_power [simp, intro]:
  "(\<lambda>x. x ^ n) twice_field_differentiable_at x"
proof -
  have "\<forall>x\<in>UNIV. (\<lambda>x. x ^ n) field_differentiable at x"
    by simp
  moreover have "deriv ((\<lambda>x. x ^ n)) field_differentiable at x"
  proof -
    have "deriv ((\<lambda>x. x ^ n)) = (\<lambda>x. of_nat n * x ^ (n - 1))"
      by (simp add: ext)
    then show ?thesis
      using field_differentiable_mult[of "\<lambda>x. of_nat n" x UNIV "\<lambda>x. x ^ (n - 1)"]
      by (simp add: field_differentiable_caratheodory_at)
  qed
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by force
qed

lemma twice_field_differentiable_at_power_fun [intro]:
  assumes "f twice_field_differentiable_at x"
    shows "(\<lambda>x. f x ^ n) twice_field_differentiable_at x"
  by (blast intro: assms twice_field_differentiable_at_compose [OF _ twice_field_differentiable_at_power])

subsubsection\<open>Inverse\<close>

lemma eventually_deriv_inverse:
  assumes "x \<noteq> 0"
    shows "\<forall>\<^sub>F x in nhds x. deriv inverse x = - 1 / (x ^ 2)"
proof -
  obtain T where open_T: "open T" and "\<forall>z\<in>T. z \<noteq> 0" and x_in_T: "x \<in> T"
    using assms t1_space by blast

  then have "\<forall>x \<in> T. deriv inverse x = - 1 / (x ^ 2)"
    by simp
  then show ?thesis
    using eventually_nhds open_T x_in_T by blast
qed

lemma deriv_deriv_inverse [simp]:
  assumes "x \<noteq> 0"
  shows "deriv (deriv inverse) x = 2 * inverse (x ^ 3)"
proof -
  have "deriv (\<lambda>x. inverse (x ^ 2)) x = - (of_nat 2 * x) / ((x ^ 2) ^ 2)"
    using assms by simp
  moreover have "(\<lambda>x. inverse (x ^ 2)) field_differentiable at x"
    using assms by (simp add: field_differentiable_inverse)
  ultimately have "deriv (\<lambda>x. - (inverse (x ^ 2))) x = of_nat 2 * x / (x ^ 4)"
    using deriv_chain[of "\<lambda>x. inverse (x ^ 2)" x]
    by (simp add: comp_def field_differentiable_minus field_simps)
  then have "deriv (\<lambda>x. - 1 / (x ^ 2)) x = 2 * inverse (x ^ 3)"
    by (simp add: power4_eq_xxxx power3_eq_cube field_simps)
  then show ?thesis
    using assms eventually_deriv_inverse deriv_cong_ev by fastforce
qed

lemma twice_field_differentiable_at_inverse [simp, intro]:
  assumes "x \<noteq> 0"
  shows "inverse twice_field_differentiable_at x"
proof -
  obtain T where zero_T: "0 \<notin> T" and x_in_T: "x \<in> T" and open_T: "open T"
    using assms t1_space by blast
  then have "T \<subseteq> {z. z \<noteq> 0}"
    by blast
  then have "\<forall>x\<in>T. inverse field_differentiable at x within T"
    using DERIV_inverse field_differentiable_def by blast
  moreover have "deriv inverse field_differentiable at x"
  proof -
    have "(\<lambda>x. - inverse (x ^ 2)) field_differentiable at x"
      using assms by (simp add: field_differentiable_inverse field_differentiable_minus)
    then have "(\<lambda>x. - 1 / (x ^ 2)) field_differentiable at x"
      by (simp add: inverse_eq_divide)
    then show ?thesis
      using eventually_deriv_inverse[OF assms]
      by (simp add: DERIV_cong_ev field_differentiable_def)
  qed
  moreover have "x \<in> interior T"
    by (simp add: x_in_T open_T interior_open)
  ultimately show ?thesis
    unfolding twice_field_differentiable_at_def field_differentiable_on_def
    by blast
qed

lemma twice_field_differentiable_at_inverse_fun [simp, intro]:
  assumes "f twice_field_differentiable_at x"
          "f x \<noteq> 0"
  shows "(\<lambda>x. inverse (f x)) twice_field_differentiable_at x"
  by (simp add: assms twice_field_differentiable_at_compose)

lemma twice_field_differentiable_at_divide [intro]:
  assumes "f twice_field_differentiable_at x"
      and "g twice_field_differentiable_at x"
      and "g x \<noteq> 0"
    shows "(\<lambda>x. f x / g x) twice_field_differentiable_at x"
  by (simp add: assms divide_inverse twice_field_differentiable_at_mult)

subsubsection\<open>Polynomial\<close>

lemma twice_field_differentiable_at_polyn [simp, intro]:
  fixes coef :: "nat \<Rightarrow> 'a :: {real_normed_field}"
    and n :: nat
  shows "(\<lambda>x. \<Sum>i<n. coef i * x ^ i) twice_field_differentiable_at x"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case hyp: (Suc n)
  show ?case
  proof (simp, rule twice_field_differentiable_at_add)
    show "(\<lambda>x. \<Sum>i<n. coef i * x ^ i) twice_field_differentiable_at x"
      by (rule hyp)
    show "(\<lambda>x. coef n * x ^ n) twice_field_differentiable_at x"
      using twice_field_differentiable_at_compose[of "\<lambda>x. x ^ n" x "(*) (coef n)"]
      by simp
  qed
qed

lemma twice_field_differentiable_at_polyn_fun [simp]:
  fixes coef :: "nat \<Rightarrow> 'a :: {real_normed_field}"
    and n :: nat
  assumes "f twice_field_differentiable_at x"
  shows "(\<lambda>x. \<Sum>i<n. coef i * f x ^ i) twice_field_differentiable_at x"
  by (blast intro: assms twice_field_differentiable_at_compose [OF _ twice_field_differentiable_at_polyn])

end
