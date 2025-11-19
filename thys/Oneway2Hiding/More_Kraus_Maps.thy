theory More_Kraus_Maps

imports Kraus_Maps.Kraus_Maps
  O2H_Additional_Lemmas
begin

unbundle cblinfun_syntax
unbundle lattice_syntax

text \<open>Fst on kraus families.\<close>


lemma inj_Fst_alt:
  assumes "c\<noteq>0"
  shows "a \<otimes>\<^sub>o c = b \<otimes>\<^sub>o c \<Longrightarrow> a = b"
  using inj_tensor_left[OF assms] unfolding inj_def by auto

lift_definition kf_Fst :: "('a ell2, 'c ell2, unit) kraus_family \<Rightarrow> 
  (('a \<times> 'b) ell2, ('c \<times> 'b) ell2, unit) kraus_family" is 
  "\<lambda>E. (\<lambda>(x,_). (x \<otimes>\<^sub>o id_cblinfun, ())) ` E"
proof (rename_tac \<EE>, intro CollectI)
  fix \<EE> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2 \<times> unit) set\<close> 
  assume \<open>\<EE> \<in> Collect kraus_family\<close>
  then have \<open>kraus_family \<EE>\<close> by auto
  define f :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2 \<times> unit) \<Rightarrow> _\<close> where \<open>f = (\<lambda>(E,x). (E \<otimes>\<^sub>o id_cblinfun, ()))\<close>
  define Fst where \<open>Fst = f ` \<EE>\<close>
  show \<open>kraus_family Fst\<close>
  proof (intro kraus_familyI)
    from \<open>kraus_family \<EE>\<close>
    obtain B where B: \<open>(\<Sum>(E, x)\<in>S. E* o\<^sub>C\<^sub>L E) \<le> B\<close> if \<open>finite S\<close> and \<open>S \<subseteq> \<EE>\<close> for S
      apply atomize_elim
      by (auto simp: kraus_family_def bdd_above_def)
    from B[of \<open>{}\<close>] have [simp]: \<open>B \<ge> 0\<close> by simp
    have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) \<le> B \<otimes>\<^sub>o id_cblinfun\<close> if \<open>finite U\<close> and \<open>U \<subseteq> Fst\<close> for U
    proof -
      from that
      obtain V where V_subset: \<open>V \<subseteq> \<EE>\<close> and [simp]: \<open>finite V\<close> and \<open>U = f ` V\<close> 
        apply (simp only: Fst_def flip: f_def)
        by (meson finite_subset_image)
      have \<open>inj_on f V\<close> by (auto intro!: inj_onI simp: f_def inj_Fst_alt[OF id_cblinfun_not_0])
      have \<open>(\<Sum>(G, z)\<in>U. G* o\<^sub>C\<^sub>L G) = (\<Sum>(G, z)\<in>f ` V. G* o\<^sub>C\<^sub>L G)\<close> 
        using \<open>U = f ` V\<close> by (auto)
      also have \<open>\<dots> = (\<Sum>(E,x)\<in>V. (E \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L (E \<otimes>\<^sub>o id_cblinfun))\<close>
        by (subst sum.reindex) (use \<open>inj_on f V\<close> in \<open>auto simp: case_prod_unfold f_def\<close>)
      also have \<open>\<dots> = (\<Sum>(E,x)\<in>V. (E* o\<^sub>C\<^sub>L E)) \<otimes>\<^sub>o id_cblinfun\<close>
        by (subst tensor_op_cbilinear.sum_left)
          (simp add: case_prod_unfold comp_tensor_op tensor_op_adjoint)
      also have \<open>\<dots> \<le> B \<otimes>\<^sub>o id_cblinfun\<close>
        using V_subset by (auto intro!: tensor_op_mono B)
      finally show ?thesis by-
    qed
    then show \<open>bdd_above ((\<lambda>F. \<Sum>(E, x)\<in>F. E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Fst})\<close> 
      by fast
    show \<open>0 \<notin> fst ` Fst\<close>  (is \<open>?zero \<notin> _\<close>)
    proof (rule notI)
      assume \<open>?zero \<in> fst ` Fst\<close>
      then have \<open>?zero \<in> (\<lambda>x. fst x \<otimes>\<^sub>o id_cblinfun) ` \<EE>\<close>
        by (simp add: Fst_def f_def image_image case_prod_unfold)
      then obtain E where \<open>E \<in> \<EE>\<close> and \<open>?zero = fst E \<otimes>\<^sub>o id_cblinfun\<close>
        by blast
      then have \<open>fst E = 0\<close>
        by (metis id_cblinfun_not_0 tensor_op_nonzero)
      with \<open>E \<in> \<EE>\<close>
      show False
        using \<open>kraus_family \<EE>\<close>
        by (simp add: kraus_family_def)
    qed
  qed
qed


(* TODO remove *)
lemma summable_on_in_kf_Fst:
  fixes f :: "'c \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2"
    and b :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2"
  shows "summable_on_in cweak_operator_topology (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) (Rep_kraus_family G)"
proof -
  have "bdd_above (sum (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ` {F. finite F \<and> F \<subseteq> Rep_kraus_family G})"
    by (intro summable_wot_bdd_above[OF kf_bound_summable positive_cblinfun_squareI])
      (auto simp add: case_prod_beta)
  then obtain B where B: \<open>(\<Sum>x\<in>S. fst x* o\<^sub>C\<^sub>L fst x) \<le> B\<close> if \<open>finite S\<close> and 
    \<open>S \<subseteq> (Rep_kraus_family G)\<close> for S
    apply atomize_elim unfolding bdd_above_def by (auto simp: case_prod_beta)
  have bound: "(\<Sum>x\<in>F. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) \<le> B \<otimes>\<^sub>o id_cblinfun" 
    if "finite F" "F \<subseteq> (Rep_kraus_family G)" for F
    by (subst tensor_op_cbilinear.sum_left[symmetric], intro tensor_op_mono_left)
      (auto simp add: B that) 
  have pos: "x \<in> (Rep_kraus_family G) \<Longrightarrow> 0 \<le> (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun" for x 
    using positive_cblinfun_squareI  positive_id_cblinfun tensor_op_pos by blast
  show ?thesis by (auto intro!: summable_wot_boundedI[OF bound pos]) 
qed

(* TODO remove *)
lemma infsum_in_kf_Fst:
  fixes f :: "'c \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2"
    and b :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2"
  shows "infsum_in cweak_operator_topology (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) (Rep_kraus_family G) \<le> 
      (infsum_in cweak_operator_topology (\<lambda>x. fst x* o\<^sub>C\<^sub>L fst x) (Rep_kraus_family G)) \<otimes>\<^sub>o id_cblinfun"
proof -
  have sum: "summable_on_in cweak_operator_topology (\<lambda>x. fst x* o\<^sub>C\<^sub>L fst x) (Rep_kraus_family G)"
    using kf_bound_summable 
    by (metis (mono_tags, lifting) cond_case_prod_eta fst_conv) 
  have pos_f: "x \<in> Rep_kraus_family G \<Longrightarrow> 0 \<le> fst x* o\<^sub>C\<^sub>L fst x" for x 
    using positive_cblinfun_squareI by blast
  have pos: "x \<in> Rep_kraus_family G \<Longrightarrow> 0 \<le> (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun" for x 
    by (simp add: positive_cblinfun_squareI tensor_op_pos)
  define s where "s = infsum_in cweak_operator_topology (\<lambda>x. fst x* o\<^sub>C\<^sub>L fst x) (Rep_kraus_family G)"
  have "sum (\<lambda>x. fst x* o\<^sub>C\<^sub>L fst x) F \<le> s" if "finite F" and "F \<subseteq> (Rep_kraus_family G)" for F 
    unfolding s_def 
    using that infsum_wot_is_Sup[OF sum pos_f] unfolding is_Sup_def by auto 
  then have "sum (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) F \<le> s \<otimes>\<^sub>o id_cblinfun" 
    if "finite F" and "F \<subseteq> Rep_kraus_family G" for F 
    apply (subst tensor_op_cbilinear.sum_left[symmetric])
    apply (intro tensor_op_mono_left[OF _ positive_id_cblinfun])
    by (use that in \<open>auto\<close>)
  moreover have "is_Sup (sum (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) ` 
    {F. finite F \<and> F \<subseteq> (Rep_kraus_family G)}) 
    (infsum_in cweak_operator_topology (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) (Rep_kraus_family G))"
    by (intro infsum_wot_is_Sup[OF summable_on_in_kf_Fst pos], auto)
  ultimately have "infsum_in cweak_operator_topology (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) 
    (Rep_kraus_family G) \<le> s \<otimes>\<^sub>o id_cblinfun"
    by (smt (verit, ccfv_threshold) image_iff is_Sup_def mem_Collect_eq)
  then show ?thesis unfolding s_def by auto
qed

lemma kf_bound_kf_Fst:
  "kf_bound (kf_Fst F:: (('a \<times> 'b) ell2, ('c \<times> 'b) ell2, unit) kraus_family) \<le> 
  kf_bound F \<otimes>\<^sub>o id_cblinfun"
proof -
  have inj: "inj_on (\<lambda>(x, _). (x \<otimes>\<^sub>o id_cblinfun, ())) (Rep_kraus_family F)" 
    unfolding inj_on_def by (auto simp add: inj_Fst_alt[OF id_cblinfun_not_0])
  have "infsum_in cweak_operator_topology (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun) (Rep_kraus_family F) \<le>
    infsum_in cweak_operator_topology (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x)) (Rep_kraus_family F) \<otimes>\<^sub>o id_cblinfun"
    by (rule infsum_in_kf_Fst) 
  then have "infsum_in cweak_operator_topology (\<lambda>x. (fst x* o\<^sub>C\<^sub>L fst x) \<otimes>\<^sub>o id_cblinfun)(Rep_kraus_family F)
    \<le> infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family F) \<otimes>\<^sub>o id_cblinfun"
    by (metis (mono_tags, lifting) infsum_in_cong prod.case_eq_if)
  then have "infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) ((\<lambda>(x,_). 
    (x \<otimes>\<^sub>o (id_cblinfun ::'b update), ())) ` (Rep_kraus_family F)) \<le>
    (infsum_in cweak_operator_topology (\<lambda>(E, x). E* o\<^sub>C\<^sub>L E) (Rep_kraus_family F)) \<otimes>\<^sub>o id_cblinfun"
    by (subst infsum_in_reindex[OF inj]) 
      (auto simp add: o_def case_prod_beta tensor_op_adjoint comp_tensor_op)
  then show ?thesis 
    by (simp add: kf_Fst.rep_eq kf_bound.rep_eq)
qed

lemma sandwich_tc_kf_apply_Fst:
  "sandwich_tc (Snd (Q::'d update)) (kf_apply (kf_Fst F:: 
 (('a\<times>'d) ell2, ('a\<times>'d) ell2, unit) kraus_family) \<rho>) = 
 kf_apply (kf_Fst F) (sandwich_tc (Snd Q) \<rho>)"
proof -
  have sand: "sandwich_tc (Snd Q) (sandwich_tc a \<rho>) =
        sandwich_tc a (sandwich_tc (Snd Q) \<rho>)"
    if "(a, ()) \<in> Rep_kraus_family (kf_Fst F)" for a
  proof -
    obtain x where a: "a = x \<otimes>\<^sub>o id_cblinfun" 
      using \<open>(a, ()) \<in> Rep_kraus_family (kf_Fst F)\<close> unfolding kf_Fst.rep_eq by auto
    show ?thesis unfolding a sandwich_tc_compose'[symmetric] Snd_def by (auto simp add: comp_tensor_op)
  qed
  have 1: "sum (sandwich_tc (Snd Q) o (\<lambda>E. (sandwich_tc (fst E) \<rho>))) F' = 
    sandwich_tc (Snd Q) (\<Sum>E\<in>F'. sandwich_tc (fst E) \<rho>)"
    if "finite F'" "F' \<subseteq> Rep_kraus_family (kf_Fst F :: 
    (('a\<times>'d) ell2, ('a\<times>'d) ell2, unit) kraus_family)" for F'
    by (auto simp add: sandwich_tc_sum sandwich_tc_tensor intro!: sum.cong)
  have 2: "isCont (sandwich_tc (Snd Q)) 
    (\<Sum>\<^sub>\<infinity>E\<in>Rep_kraus_family (kf_Fst F). sandwich_tc (fst E) \<rho>)"
    using isCont_sandwich_tc by auto
  have 3: " (\<lambda>E. sandwich_tc (fst E) \<rho>) summable_on Rep_kraus_family (kf_Fst F)"
    by (metis (no_types, lifting) cond_case_prod_eta fst_conv kf_apply_summable)
  then show ?thesis unfolding kf_apply.rep_eq
    by (subst infsum_comm_additive_general[OF 1 2 3, symmetric]) 
      (auto intro!: infsum_cong simp add: sand)
qed

text \<open>kraus family Fst is trace preserving.\<close>


lemma kf_apply_Fst_tensor:
  \<open>kf_apply (kf_Fst \<EE> ::(('c \<times> 'b) ell2, ('a \<times> 'b) ell2, unit) kraus_family) 
  (tc_tensor \<rho> \<sigma>) = tc_tensor (kf_apply \<EE> \<rho>) \<sigma>\<close>
proof -
  have inj: \<open>inj_on (\<lambda>(E, x). (E \<otimes>\<^sub>o id_cblinfun, ())) (Rep_kraus_family \<EE>)\<close>
    unfolding inj_on_def by (auto simp add: inj_Fst_alt[OF id_cblinfun_not_0])
  have [simp]: \<open>bounded_linear (\<lambda>x. tc_tensor x \<sigma>)\<close>
    by (intro bounded_linear_intros)
  have [simp]: \<open>bounded_linear (tc_tensor (sandwich_tc E \<rho>))\<close> for E
    by (intro bounded_linear_intros)
  have sum2: \<open>(\<lambda>(E, x). sandwich_tc E \<rho>) summable_on Rep_kraus_family \<EE>\<close>
    using kf_apply_summable by blast

  have \<open>kf_apply (kf_Fst \<EE> ::(('c \<times> 'b) ell2, ('a \<times> 'b) ell2, unit) kraus_family) 
    (tc_tensor \<rho> \<sigma>)
      = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc (E \<otimes>\<^sub>o id_cblinfun) (tc_tensor \<rho> \<sigma>))\<close>
    unfolding kf_apply.rep_eq kf_Fst.rep_eq
    by (subst infsum_reindex[OF inj]) (simp add: case_prod_unfold o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) \<sigma>)\<close>
    by (simp add: sandwich_tc_tensor)
  finally have \<open>kf_apply (kf_Fst \<EE> ::(('c \<times> 'b) ell2, ('a \<times> 'b) ell2, unit) kraus_family) 
    (tc_tensor \<rho> \<sigma>) = (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. tc_tensor (sandwich_tc E \<rho>) \<sigma>)\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (\<Sum>\<^sub>\<infinity>(E,x)\<in>Rep_kraus_family \<EE>. sandwich_tc E \<rho>) \<sigma>\<close>
    by (subst infsum_bounded_linear[where h=\<open>\<lambda>x. tc_tensor x \<sigma>\<close>, symmetric])
      (use sum2 in \<open>auto simp add: o_def case_prod_unfold\<close>)
  also have \<open>\<dots> = tc_tensor (kf_apply \<EE> \<rho>) \<sigma>\<close>
    by (simp add: kf_apply_def case_prod_unfold)
  finally show ?thesis by auto
qed

lemma partial_trace_ignore_trace_preserving_map_Fst:
  assumes \<open>kf_trace_preserving \<EE>\<close>
  shows \<open>partial_trace (kf_apply (kf_Fst \<EE>) \<rho>) = 
         kf_apply \<EE> (partial_trace \<rho>)\<close>
proof (rule fun_cong[where x=\<rho>], rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
  show \<open>bounded_clinear (\<lambda>a. partial_trace (kf_apply (kf_Fst \<EE>) a))\<close>
    by (intro bounded_linear_intros)
  show \<open>bounded_clinear (\<lambda>a. kf_apply \<EE> (partial_trace a))\<close>
    by (intro bounded_linear_intros)
  fix \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('c ell2, 'c ell2) trace_class\<close>
  from assms
  show \<open>partial_trace (kf_apply (kf_Fst \<EE>) (tc_tensor \<rho> \<sigma>)) =
        kf_apply \<EE> (partial_trace (tc_tensor \<rho> \<sigma>))\<close>
    by (simp add: kf_apply_Fst_tensor kf_apply_scaleC partial_trace_tensor)
qed

lemma trace_preserving_kf_Fst:
  assumes "km_trace_preserving (kf_apply E)"
  shows "km_trace_preserving (kf_apply (
    kf_Fst E ::(('a \<times> 'c) ell2, ('a \<times> 'c) ell2, unit) kraus_family))"
proof - 
  have bounded: "bounded_clinear (\<lambda>\<rho>. trace_tc (kf_apply (kf_Fst E) \<rho>))"
    by (simp add: bounded_clinear_compose kf_apply_bounded_clinear)
  have trace: "trace_tc (kf_apply (kf_Fst E :: 
    (('a \<times> 'c) ell2, ('a \<times> 'c) ell2, unit) kraus_family) (tc_tensor x y)) =
    trace_tc (tc_tensor x y)" for x y using assms
    apply (simp add: kf_apply_Fst_tensor tc_tensor.rep_eq trace_tc.rep_eq trace_tensor km_trace_preserving_def) 
    by (metis kf_trace_preserving_def trace_tc.rep_eq)

  have "(\<lambda>\<rho>. trace_tc (kf_apply (kf_Fst E :: 
    (('a \<times> 'c) ell2, ('a \<times> 'c) ell2, unit) kraus_family) \<rho>)) = trace_tc"
    by (rule eq_from_separatingI2[OF separating_set_bounded_clinear_tc_tensor])
      (auto simp add: bounded trace)
  then show ?thesis
    using assms unfolding km_trace_preserving_def
    by (metis kf_trace_preserving_def)
qed


text \<open>Summability on Kraus maps\<close>

lemma finite_kf_apply_has_sum:
  assumes "(f has_sum x) A"
  shows "((kf_apply \<FF> o f) has_sum kf_apply \<FF> x) A"
  unfolding o_def by (intro has_sum_bounded_linear[OF _ assms]) 
    (auto simp add: bounded_clinear.bounded_linear kf_apply_bounded_clinear)

lemma finite_kf_apply_abs_summable_on:
  assumes "f abs_summable_on A"
  shows "(kf_apply \<FF> o f) abs_summable_on A"
  by (intro abs_summable_on_bounded_linear) 
    (auto simp add: assms bounded_clinear.bounded_linear kf_apply_bounded_clinear)

unbundle no cblinfun_syntax
unbundle no lattice_syntax


end