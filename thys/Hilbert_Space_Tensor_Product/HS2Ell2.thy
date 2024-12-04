section \<open>\<open>HS2Ell2\<close> -- Representing any Hilbert space as $\ell_2(X)$\<close>

theory HS2Ell2
  imports Complex_Bounded_Operators.Complex_L2 Misc_Tensor_Product_BO
begin

unbundle cblinfun_notation

typedef (overloaded) 'a::\<open>{chilbert_space, not_singleton}\<close> chilbert2ell2 = \<open>some_chilbert_basis :: 'a set\<close>
  using some_chilbert_basis_nonempty by auto

definition ell2_to_hilbert where \<open>ell2_to_hilbert = cblinfun_extension (range ket) (Rep_chilbert2ell2 o inv ket)\<close>

lemma ell2_to_hilbert_ket: \<open>ell2_to_hilbert *\<^sub>V ket x = Rep_chilbert2ell2 x\<close>
proof -
  have \<open>cblinfun_extension_exists (range ket) (Rep_chilbert2ell2 o inv ket)\<close>
  proof (rule cblinfun_extension_exists_ortho[where B=1])
    fix x y :: "'b chilbert2ell2 ell2"
    assume "x \<in> range ket" "y \<in> range ket" "x \<noteq> y"
    then obtain x' y' where x'_y': "x = ket x'" "y = ket y'" "x' \<noteq> y'"
      by auto
    have "is_orthogonal (Rep_chilbert2ell2 x') (Rep_chilbert2ell2 y')"
      by (meson Rep_chilbert2ell2 Rep_chilbert2ell2_inject \<open>x' \<noteq> y'\<close> is_ortho_set_def is_ortho_set_some_chilbert_basis)
    thus "is_orthogonal ((Rep_chilbert2ell2 \<circ> inv ket) x) ((Rep_chilbert2ell2 \<circ> inv ket) y)"
      using x'_y' by auto
  qed (auto simp: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
  from cblinfun_extension_apply[OF this]
  have "cblinfun_extension (range ket) (Rep_chilbert2ell2 \<circ> inv ket) *\<^sub>V (ket x) = 
          (Rep_chilbert2ell2 \<circ> inv ket) (ket x)"
    by blast
  thus ?thesis
    by (simp add: ell2_to_hilbert_def)
qed

lemma norm_ell2_to_hilbert: \<open>norm ell2_to_hilbert = 1\<close>
proof (rule order.antisym)
  show \<open>norm ell2_to_hilbert \<le> 1\<close>
    unfolding ell2_to_hilbert_def
  proof (rule cblinfun_extension_exists_ortho_norm[where B=1])
    fix x y :: "'b chilbert2ell2 ell2"
    assume "x \<in> range ket" "y \<in> range ket" "x \<noteq> y"
    then obtain x' y' where x'_y': "x = ket x'" "y = ket y'" "x' \<noteq> y'"
      by auto
    have "is_orthogonal (Rep_chilbert2ell2 x') (Rep_chilbert2ell2 y')"
      by (meson Rep_chilbert2ell2 Rep_chilbert2ell2_inject \<open>x' \<noteq> y'\<close> is_ortho_set_def is_ortho_set_some_chilbert_basis)
    thus "is_orthogonal ((Rep_chilbert2ell2 \<circ> inv ket) x) ((Rep_chilbert2ell2 \<circ> inv ket) y)"
      using x'_y' by auto
  qed (auto simp: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
  show \<open>norm ell2_to_hilbert \<ge> 1\<close>
    by (rule cblinfun_norm_geqI[where x=\<open>ket undefined\<close>])
       (auto simp: ell2_to_hilbert_ket Rep_chilbert2ell2 is_normal_some_chilbert_basis)
qed

lemma unitary_ell2_to_hilbert[simp]: \<open>unitary ell2_to_hilbert\<close>
proof (rule surj_isometry_is_unitary)
  show \<open>isometry (ell2_to_hilbert :: 'a chilbert2ell2 ell2 \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  proof (rule orthogonal_on_basis_is_isometry)
    show \<open>ccspan (range ket) = top\<close>
      by auto
    fix x y :: \<open>'a chilbert2ell2 ell2\<close>
    assume \<open>x \<in> range ket\<close> \<open>y \<in> range ket\<close>
    then obtain x' y' where [simp]: \<open>x = ket x'\<close> \<open>y = ket y'\<close>
      by auto
    show \<open>(ell2_to_hilbert *\<^sub>V x) \<bullet>\<^sub>C (ell2_to_hilbert *\<^sub>V y) = x \<bullet>\<^sub>C y\<close>
    proof (cases \<open>x'=y'\<close>)
      case True
      hence "Rep_chilbert2ell2 y' \<bullet>\<^sub>C Rep_chilbert2ell2 y' = 1 "
        using Rep_chilbert2ell2 cnorm_eq_1 is_normal_some_chilbert_basis by blast
      then show ?thesis using True
        by (auto simp: ell2_to_hilbert_ket)
    next
      case False
      hence "is_orthogonal (Rep_chilbert2ell2 x') (Rep_chilbert2ell2 y') "
        by (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inject is_ortho_set_def is_ortho_set_some_chilbert_basis)
      then show ?thesis
        using False by (auto simp: ell2_to_hilbert_ket cinner_ket)
    qed
  qed
  have \<open>cblinfun_apply ell2_to_hilbert ` range ket \<supseteq> some_chilbert_basis\<close>
    by (metis Rep_chilbert2ell2_cases UNIV_I ell2_to_hilbert_ket image_eqI subsetI)
  then have \<open>ell2_to_hilbert *\<^sub>S top \<ge> ccspan some_chilbert_basis\<close> (is \<open>_ \<ge> \<dots>\<close>)
    by (smt (verit, del_insts) cblinfun_image_ccspan ccspan_mono ccspan_range_ket)
  also have \<open>\<dots> = top\<close>
    by simp
  finally show \<open>ell2_to_hilbert *\<^sub>S top = top\<close>
    by (simp add: top.extremum_unique)
qed

lemma ell2_to_hilbert_adj_ket: \<open>ell2_to_hilbert* *\<^sub>V \<psi> = ket (Abs_chilbert2ell2 \<psi>)\<close> if \<open>\<psi> \<in> some_chilbert_basis\<close>
  using ell2_to_hilbert_ket unitary_ell2_to_hilbert
  by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply that type_definition.Abs_inverse type_definition_chilbert2ell2 unitaryD1)


definition \<open>cr_chilbert2ell2_ell2 x y \<longleftrightarrow> ell2_to_hilbert *\<^sub>V x = y\<close>


lemma bi_unique_cr_chilbert2ell2_ell2[transfer_rule]: \<open>bi_unique cr_chilbert2ell2_ell2\<close>
  by (metis (no_types, opaque_lifting) bi_unique_def cblinfun_apply_cblinfun_compose cr_chilbert2ell2_ell2_def id_cblinfun_apply unitaryD1 unitary_ell2_to_hilbert)
lemma bi_total_cr_chilbert2ell2_ell2[transfer_rule]: \<open>bi_total cr_chilbert2ell2_ell2\<close>
  by (metis (no_types, opaque_lifting) bi_total_def cblinfun_apply_cblinfun_compose cr_chilbert2ell2_ell2_def id_cblinfun_apply unitaryD2 unitary_ell2_to_hilbert)

named_theorems c2l2l2

lemma c2l2l2_cinner[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(cr_chilbert2ell2_ell2 ===> cr_chilbert2ell2_ell2 ===> (=)) cinner cinner\<close>
proof -
  have *: \<open>ket x \<bullet>\<^sub>C ket y = (ell2_to_hilbert *\<^sub>V ket x) \<bullet>\<^sub>C (ell2_to_hilbert *\<^sub>V ket y)\<close> for x y :: \<open>'a chilbert2ell2\<close>
    by (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inverse cinner_adj_right ell2_to_hilbert_adj_ket ell2_to_hilbert_ket)
  have \<open>x \<bullet>\<^sub>C y = (ell2_to_hilbert *\<^sub>V x) \<bullet>\<^sub>C (ell2_to_hilbert *\<^sub>V y) \<close> for x y :: \<open>'a chilbert2ell2 ell2\<close>
    apply (rule fun_cong[where x=x])
    apply (rule bounded_antilinear_equal_ket)
      apply (intro bounded_linear_intros)
     apply (intro bounded_linear_intros)
    apply (rule fun_cong[where x=y])
    apply (rule bounded_clinear_equal_ket)
      apply (intro bounded_linear_intros)
     apply (intro bounded_linear_intros)
    by (simp add: *)
  then show ?thesis
    by (auto intro!: rel_funI simp: cr_chilbert2ell2_ell2_def)
qed

lemma c2l2l2_norm[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(cr_chilbert2ell2_ell2 ===> (=)) norm norm\<close>
  apply (subst norm_eq_sqrt_cinner[abs_def])
  apply (subst (2) norm_eq_sqrt_cinner[abs_def])
  using c2l2l2_cinner[transfer_rule] apply fail?
  by transfer_prover

lemma c2l2l2_scaleC[c2l2l2]:
  includes lifting_syntax
  shows \<open>((=) ===> cr_chilbert2ell2_ell2 ===> cr_chilbert2ell2_ell2) scaleC scaleC\<close>
proof -
  have \<open>ell2_to_hilbert *\<^sub>V c *\<^sub>C x = c *\<^sub>C (ell2_to_hilbert *\<^sub>V x)\<close> for c and x :: \<open>'a chilbert2ell2 ell2\<close>
    by (simp add: cblinfun.scaleC_right)
  then show ?thesis
    by (auto intro!: rel_funI simp: cr_chilbert2ell2_ell2_def)
qed

(* lemma c2l2l2_infsum'[c2l2l2]:
  includes lifting_syntax
  shows \<open>((R ===> cr_chilbert2ell2_ell2) ===> (rel_set R) ===> cr_chilbert2ell2_ell2) infsum infsum\<close>
  by - *)

lemma c2l2l2_zero[c2l2l2]: 
  includes lifting_syntax
  shows \<open>cr_chilbert2ell2_ell2 0 0\<close>
  unfolding cr_chilbert2ell2_ell2_def by simp

lemma c2l2l2_is_ortho_set[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_chilbert2ell2_ell2 ===> (=)) is_ortho_set (is_ortho_set :: 'a::{chilbert_space,not_singleton} set \<Rightarrow> bool)\<close>
  unfolding is_ortho_set_def
  using c2l2l2[where 'a='a, transfer_rule] apply fail?
  by transfer_prover


lemma c2l2l2_ccspan[c2l2l2]:
  includes lifting_syntax
  shows \<open>(rel_set cr_chilbert2ell2_ell2 ===> rel_ccsubspace cr_chilbert2ell2_ell2) ccspan ccspan\<close>
proof (rule rel_funI, rename_tac A B)
  fix A and B :: \<open>'a set\<close>
  assume \<open>rel_set cr_chilbert2ell2_ell2 A B\<close>
  then have \<open>B = ell2_to_hilbert ` A\<close>
    by (metis (no_types, lifting) bi_unique_cr_chilbert2ell2_ell2 bi_unique_rel_set_lemma cr_chilbert2ell2_ell2_def image_cong)
  then have \<open>space_as_set (ccspan B) = ell2_to_hilbert ` space_as_set (ccspan A)\<close>
    by (subst space_as_set_image_commute[where V=\<open>ell2_to_hilbert*\<close>])
       (auto intro: unitaryD2 simp: cblinfun_image_ccspan)
  then have \<open>rel_set cr_chilbert2ell2_ell2 (space_as_set (ccspan A)) (space_as_set (ccspan B))\<close>
    by (smt (verit, best) cr_chilbert2ell2_ell2_def image_iff rel_setI)
  then show \<open>rel_ccsubspace cr_chilbert2ell2_ell2 (ccspan A) (ccspan B)\<close>
    by (simp add: rel_ccsubspace_def)
qed


lemma ell2_to_hilbert_adj_ell2_to_hilbert [simp]: "ell2_to_hilbert* *\<^sub>V ell2_to_hilbert *\<^sub>V x = x"
  using unitary_ell2_to_hilbert unfolding unitary_def
  by (metis cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply)

lemma ell2_to_hilbert_ell2_to_hilbert_adj [simp]: "ell2_to_hilbert *\<^sub>V ell2_to_hilbert* *\<^sub>V x = x"
  using unitary_ell2_to_hilbert unfolding unitary_def
  by (metis cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply)

lemma bi_total_rel_ccsubspace_cr_chilbert2ell2_ell2[transfer_rule]:
  \<open>bi_total (rel_ccsubspace cr_chilbert2ell2_ell2)\<close>
  apply (rule bi_totalI)
  subgoal
   by (rule left_total_rel_ccsubspace[where U=ell2_to_hilbert and V=\<open>ell2_to_hilbert*\<close>])
      (auto simp: cr_chilbert2ell2_ell2_def)[3]
  subgoal
   by (rule right_total_rel_ccsubspace[where U=\<open>ell2_to_hilbert*\<close> and V=\<open>ell2_to_hilbert\<close>])
      (auto simp: cr_chilbert2ell2_ell2_def)
  done

lemma c2l2l2_top[c2l2l2]:
  includes lifting_syntax
  shows \<open>(rel_ccsubspace cr_chilbert2ell2_ell2) top top\<close>
  unfolding rel_ccsubspace_def
  by (simp add: UNIV_transfer bi_total_cr_chilbert2ell2_ell2)

lemma c2l2l2_is_onb[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_chilbert2ell2_ell2 ===> (=)) is_onb is_onb\<close>
  unfolding is_onb_def
  using c2l2l2[where 'a='a, transfer_rule] apply fail?
  by transfer_prover

unbundle no_cblinfun_notation

end
