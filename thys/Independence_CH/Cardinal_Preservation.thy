section\<open>Preservation of cardinals in generic extensions\<close>

theory Cardinal_Preservation
  imports
    Forcing_Main
begin

context forcing_data1

begin

lemma antichain_abs' [absolut]:
  "\<lbrakk> A\<in>M \<rbrakk> \<Longrightarrow> antichain\<^bsup>M\<^esup>(P,leq,A) \<longleftrightarrow> antichain(P,leq,A)"
  unfolding antichain_rel_def antichain_def compat_def
  using transitivity[of _ A]
  by (auto simp add:absolut)

lemma inconsistent_imp_incompatible:
  assumes "p \<tturnstile> \<phi> env" "q \<tturnstile> Neg(\<phi>) env" "p\<in>P" "q\<in>P"
    "arity(\<phi>) \<le> length(env)" "\<phi> \<in> formula" "env \<in> list(M)"
  shows "p \<bottom> q"
proof
  assume "compat(p,q)"
  then
  obtain d where "d \<preceq> p" "d \<preceq> q" "d \<in> P" by blast
  moreover
  note assms
  moreover from calculation
  have "d \<tturnstile> \<phi> env" "d \<tturnstile> Neg(\<phi>) env"
    using strengthening_lemma by simp_all
  ultimately
  show "False"
    using Forces_Neg[of d env \<phi>] refl_leq
    by (auto dest:transitivity; drule_tac bspec; auto dest:transitivity)
qed

notation check (\<open>_\<^sup>v\<close> [101] 100)

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>


locale G_generic2 = G_generic1 + forcing_data2
locale G_generic2_AC = G_generic1_AC + G_generic2

locale G_generic3 = G_generic2 + forcing_data3
locale G_generic3_AC = G_generic2_AC + G_generic3

locale G_generic3_AC_CH = G_generic3_AC + M_ZFC2_ground_CH_trans

sublocale G_generic3_AC \<subseteq> ext:M_ZFC2_trans "M[G]"
  using ground_replacements3 replacement_assm_MG
  by unfold_locales simp_all

lemma (in forcing_data1) forces_neq_apply_imp_incompatible:
  assumes
    "p \<tturnstile> \<cdot>0`1 is 2\<cdot> [f,a,b\<^sup>v]"
    "q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f,a,b'\<^sup>v]"
    "b \<noteq> b'"
    \<comment> \<open>More general version: taking general names
       \<^term>\<open>b\<^sup>v\<close> and \<^term>\<open>b'\<^sup>v\<close>, satisfying
       \<^term>\<open>p \<tturnstile> \<cdot>\<not>\<cdot>0 = 1\<cdot>\<cdot> [b\<^sup>v, b'\<^sup>v]\<close> and
       \<^term>\<open>q \<tturnstile> \<cdot>\<not>\<cdot>0 = 1\<cdot>\<cdot> [b\<^sup>v, b'\<^sup>v]\<close>.\<close>
    and
    types:"f\<in>M" "a\<in>M" "b\<in>M" "b'\<in>M" "p\<in>P" "q\<in>P"
  shows
    "p \<bottom> q"
proof -
  {
    fix G
    assume "M_generic(G)"
    then
    interpret G_generic1 _ _ _ _ _ G by unfold_locales
    include G_generic1_lemmas
    assume "q\<in>G"
    with assms \<open>M_generic(G)\<close>
    have "M[G], map(val(G),[f,a,b'\<^sup>v]) \<Turnstile> \<cdot>0`1 is 2\<cdot>"
      using truth_lemma[of "\<cdot>0`1 is 2\<cdot>" "[f,a,b'\<^sup>v]"]
      by (auto simp add:ord_simp_union arity_fun_apply_fm
          fun_apply_type)
    with \<open>b \<noteq> b'\<close> types
    have "M[G], map(val(G),[f,a,b\<^sup>v]) \<Turnstile> \<cdot>\<not>\<cdot>0`1 is 2\<cdot>\<cdot>"
      using GenExtI by auto
  }
  with types
  have "q \<tturnstile> \<cdot>\<not>\<cdot>0`1 is 2\<cdot>\<cdot> [f,a,b\<^sup>v]"
    using definition_of_forcing[where \<phi>="\<cdot>\<not>\<cdot>0`1 is 2\<cdot>\<cdot>" ]
    by (auto simp add:ord_simp_union arity_fun_apply_fm)
  with \<open>p \<tturnstile> \<cdot>0`1 is 2\<cdot> [f,a,b\<^sup>v]\<close> and types
  show "p \<bottom> q"
    using inconsistent_imp_incompatible
    by (simp add:ord_simp_union arity_fun_apply_fm fun_apply_type)
qed

context M_ctm2_AC
begin

\<comment> \<open>Simplifying simp rules (because of the occurrence of
   \<^term>\<open>setclass\<close>)\<close>
lemmas sharp_simps = Card_rel_Union Card_rel_cardinal_rel Collect_abs
  Cons_abs Cons_in_M_iff Diff_closed Equal_abs Equal_in_M_iff Finite_abs
  Forall_abs Forall_in_M_iff Inl_abs Inl_in_M_iff Inr_abs Inr_in_M_iff
  Int_closed Inter_abs Inter_closed M_nat Member_abs Member_in_M_iff
  Memrel_closed Nand_abs Nand_in_M_iff Nil_abs Nil_in_M Ord_cardinal_rel
  Pow_rel_closed Un_closed Union_abs Union_closed and_abs and_closed
  apply_abs apply_closed bij_rel_closed bijection_abs bool_of_o_abs
  bool_of_o_closed cadd_rel_0 cadd_rel_closed cardinal_rel_0_iff_0
  cardinal_rel_closed cardinal_rel_idem cartprod_abs cartprod_closed
  cmult_rel_0 cmult_rel_1 cmult_rel_closed comp_closed composition_abs
  cons_abs cons_closed converse_abs converse_closed csquare_lam_closed
  csquare_rel_closed depth_closed domain_abs domain_closed eclose_abs
  eclose_closed empty_abs field_abs field_closed finite_funspace_closed
  finite_ordinal_abs formula_N_abs formula_N_closed formula_abs
  formula_case_abs formula_case_closed formula_closed
  formula_functor_abs fst_closed function_abs function_space_rel_closed
  hd_abs image_abs image_closed inj_rel_closed injection_abs inter_abs
  irreflexive_abs is_depth_apply_abs is_eclose_n_abs is_funspace_abs
  iterates_closed length_abs length_closed lepoll_rel_refl
  limit_ordinal_abs linear_rel_abs list_N_abs list_N_closed list_abs
  list_case'_closed list_case_abs list_closed list_functor_abs
  mem_bij_abs mem_eclose_abs mem_inj_abs mem_list_abs membership_abs
  minimum_closed nat_case_abs nat_case_closed nonempty not_abs
  not_closed nth_abs number1_abs number2_abs number3_abs omega_abs
  or_abs or_closed order_isomorphism_abs ordermap_closed
  ordertype_closed ordinal_abs pair_abs pair_in_M_iff powerset_abs
  pred_closed pred_set_abs quasilist_abs quasinat_abs radd_closed
  rall_abs range_abs range_closed relation_abs restrict_closed
  restriction_abs rex_abs rmult_closed rtrancl_abs rtrancl_closed
  rvimage_closed separation_closed setdiff_abs singleton_abs
  singleton_in_M_iff snd_closed strong_replacement_closed subset_abs
  succ_in_M_iff successor_abs successor_ordinal_abs sum_abs sum_closed
  surj_rel_closed surjection_abs tl_abs trancl_abs trancl_closed
  transitive_rel_abs transitive_set_abs typed_function_abs union_abs
  upair_abs upair_in_M_iff vimage_abs vimage_closed well_ord_abs
  mem_formula_abs nth_closed Aleph_rel_closed csucc_rel_closed
  Card_rel_Aleph_rel

declare sharp_simps[simp del, simplified setclass_iff, simp]

lemmas sharp_intros = nat_into_M Aleph_rel_closed Card_rel_Aleph_rel

declare sharp_intros[rule del, simplified setclass_iff, intro]

end \<comment> \<open>\<^locale>\<open>M_ctm2_AC\<close>\<close>

context G_generic3_AC begin

context
  includes G_generic1_lemmas
begin

lemmas mg_sharp_simps = ext.Card_rel_Union ext.Card_rel_cardinal_rel
  ext.Collect_abs ext.Cons_abs ext.Cons_in_M_iff ext.Diff_closed
  ext.Equal_abs ext.Equal_in_M_iff ext.Finite_abs ext.Forall_abs
  ext.Forall_in_M_iff ext.Inl_abs ext.Inl_in_M_iff ext.Inr_abs
  ext.Inr_in_M_iff ext.Int_closed ext.Inter_abs ext.Inter_closed
  ext.M_nat ext.Member_abs ext.Member_in_M_iff ext.Memrel_closed
  ext.Nand_abs ext.Nand_in_M_iff ext.Nil_abs ext.Nil_in_M
  ext.Ord_cardinal_rel ext.Pow_rel_closed ext.Un_closed
  ext.Union_abs ext.Union_closed ext.and_abs ext.and_closed
  ext.apply_abs ext.apply_closed ext.bij_rel_closed
  ext.bijection_abs ext.bool_of_o_abs ext.bool_of_o_closed
  ext.cadd_rel_0 ext.cadd_rel_closed ext.cardinal_rel_0_iff_0
  ext.cardinal_rel_closed ext.cardinal_rel_idem ext.cartprod_abs
  ext.cartprod_closed ext.cmult_rel_0 ext.cmult_rel_1
  ext.cmult_rel_closed ext.comp_closed ext.composition_abs
  ext.cons_abs ext.cons_closed ext.converse_abs ext.converse_closed
  ext.csquare_lam_closed ext.csquare_rel_closed ext.depth_closed
  ext.domain_abs ext.domain_closed ext.eclose_abs ext.eclose_closed
  ext.empty_abs ext.field_abs ext.field_closed
  ext.finite_funspace_closed ext.finite_ordinal_abs ext.formula_N_abs
  ext.formula_N_closed ext.formula_abs ext.formula_case_abs
  ext.formula_case_closed ext.formula_closed ext.formula_functor_abs
  ext.fst_closed ext.function_abs ext.function_space_rel_closed
  ext.hd_abs ext.image_abs ext.image_closed ext.inj_rel_closed
  ext.injection_abs ext.inter_abs ext.irreflexive_abs
  ext.is_depth_apply_abs ext.is_eclose_n_abs ext.is_funspace_abs
  ext.iterates_closed ext.length_abs ext.length_closed
  ext.lepoll_rel_refl ext.limit_ordinal_abs ext.linear_rel_abs
  ext.list_N_abs ext.list_N_closed ext.list_abs
  ext.list_case'_closed ext.list_case_abs ext.list_closed
  ext.list_functor_abs ext.mem_bij_abs ext.mem_eclose_abs
  ext.mem_inj_abs ext.mem_list_abs ext.membership_abs
  ext.nat_case_abs ext.nat_case_closed
  ext.nonempty ext.not_abs ext.not_closed ext.nth_abs
  ext.number1_abs ext.number2_abs ext.number3_abs ext.omega_abs
  ext.or_abs ext.or_closed ext.order_isomorphism_abs
  ext.ordermap_closed ext.ordertype_closed ext.ordinal_abs
  ext.pair_abs ext.pair_in_M_iff ext.powerset_abs ext.pred_closed
  ext.pred_set_abs ext.quasilist_abs ext.quasinat_abs
  ext.radd_closed ext.rall_abs ext.range_abs ext.range_closed
  ext.relation_abs ext.restrict_closed ext.restriction_abs
  ext.rex_abs ext.rmult_closed ext.rtrancl_abs ext.rtrancl_closed
  ext.rvimage_closed ext.separation_closed ext.setdiff_abs
  ext.singleton_abs ext.singleton_in_M_iff ext.snd_closed
  ext.strong_replacement_closed ext.subset_abs ext.succ_in_M_iff
  ext.successor_abs ext.successor_ordinal_abs ext.sum_abs
  ext.sum_closed ext.surj_rel_closed ext.surjection_abs ext.tl_abs
  ext.trancl_abs ext.trancl_closed ext.transitive_rel_abs
  ext.transitive_set_abs ext.typed_function_abs ext.union_abs
  ext.upair_abs ext.upair_in_M_iff ext.vimage_abs ext.vimage_closed
  ext.well_ord_abs ext.mem_formula_abs ext.nth_closed ext.Aleph_rel_closed
  ext.csucc_rel_closed ext.Card_rel_Aleph_rel

\<comment> \<open>The following was motivated by the fact that
    @{thm [source] ext.apply_closed} did not simplify appropriately.\<close>
declare mg_sharp_simps[simp del, simplified setclass_iff, simp]

lemmas mg_sharp_intros = ext.nat_into_M ext.Aleph_rel_closed
  ext.Card_rel_Aleph_rel

declare mg_sharp_intros[rule del, simplified setclass_iff, intro]

\<comment> \<open>Kunen IV.2.31\<close>
lemma forces_below_filter:
  assumes "M[G], map(val(G),env) \<Turnstile> \<phi>" "p \<in> G"
    "arity(\<phi>) \<le> length(env)" "\<phi> \<in> formula" "env \<in> list(M)"
  shows "\<exists>q\<in>G. q \<preceq> p \<and> q \<tturnstile> \<phi> env"
proof -
  note assms
  moreover from this
  obtain r where "r \<tturnstile> \<phi> env" "r\<in>G"
    using generic truth_lemma[of \<phi> env]
    by blast
  moreover from this and \<open>p\<in>G\<close>
  obtain q where "q \<preceq> p" "q \<preceq> r" "q \<in> G" by auto
  ultimately
  show ?thesis
    using strengthening_lemma[of r \<phi> _ env] by blast
qed

subsection\<open>Preservation by ccc forcing notions\<close>

lemma ccc_fun_closed_lemma_aux:
  assumes "f_dot\<in>M" "p\<in>M" "a\<in>M" "b\<in>M"
  shows "{q \<in> P . q \<preceq> p \<and> (M, [q, P, leq, \<one>, f_dot, a\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))} \<in> M"
  using separation_forces[where env="[f_dot, a\<^sup>v, b\<^sup>v]" and \<phi>="\<cdot>0`1 is 2\<cdot>",simplified]
    assms G_subset_M[THEN subsetD] generic
    separation_in lam_replacement_constant lam_replacement_identity
    lam_replacement_product
    separation_conj arity_fun_apply_fm union_abs1
  by simp_all

lemma ccc_fun_closed_lemma_aux2:
  assumes "B\<in>M" "f_dot\<in>M" "p\<in>M" "a\<in>M"
  shows "(##M)(\<lambda>b\<in>B. {q \<in> P . q \<preceq> p \<and> (M, [q, P, leq, \<one>, f_dot, a\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))})"
proof -
  have "separation(##M, \<lambda>z. M, [snd(z), P, leq, \<one>, f_dot, \<tau>, fst(z)\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))"
    if "\<tau>\<in>M" for \<tau>
  proof -
    let ?f_fm="snd_fm(1,0)"
    let ?g_fm="hcomp_fm(check_fm(6),fst_fm,2,0)"
    note assms
    moreover
    have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
      using arity_fun_apply_fm union_abs1 arity_forces[of "\<cdot>0`1 is 2\<cdot> "]
      by simp
    moreover
    have "?f_fm \<in> formula" "arity(?f_fm) \<le> 7" "?g_fm \<in> formula" "arity(?g_fm) \<le> 8"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    ultimately
    show ?thesis
      using separation_sat_after_function assms that sats_fst_fm
        snd_abs sats_snd_fm sats_check_fm check_abs fst_abs
      unfolding hcomp_fm_def
      by simp
  qed
  with assms
  show ?thesis
    using lam_replacement_imp_lam_closed separation_conj separation_in
      lam_replacement_product lam_replacement_constant transitivity[of _ B]
      lam_replacement_snd lam_replacement_Collect' ccc_fun_closed_lemma_aux
    by simp
qed

lemma ccc_fun_closed_lemma:
  assumes "A\<in>M" "B\<in>M" "f_dot\<in>M" "p\<in>M"
  shows "(\<lambda>a\<in>A. {b\<in>B. \<exists>q\<in>P. q \<preceq> p \<and> (q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v])}) \<in> M"
proof -
  have "separation(##M, \<lambda>z. M, [snd(z), P, leq, \<one>, f_dot, fst(fst(z))\<^sup>v, snd(fst(z))\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))"
  proof -
    let ?f_fm="snd_fm(1,0)"
    let ?g="\<lambda>z . fst(fst(fst(z)))\<^sup>v"
    let ?g_fm="hcomp_fm(check_fm(6),hcomp_fm(fst_fm,fst_fm),2,0)"
    let ?h_fm="hcomp_fm(check_fm(7),hcomp_fm(snd_fm,fst_fm),3,0)"
    note assms
    moreover
    have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
      using arity_fun_apply_fm union_abs1 arity_forces[of "\<cdot>0`1 is 2\<cdot> "]
      by simp
    moreover
    have "?f_fm \<in> formula" "arity(?f_fm) \<le> 6" "?g_fm \<in> formula" "arity(?g_fm) \<le> 7"
      "?h_fm \<in> formula" "arity(?h_fm) \<le> 8"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    ultimately
    show ?thesis
      using separation_sat_after_function3 assms sats_check_fm check_abs
        fst_abs snd_abs
      unfolding hcomp_fm_def
      by simp
  qed
  moreover
  have 1:"separation(##M, \<lambda>z. M, [snd(z), P, leq, \<one>, f_dot, \<tau>, fst(z)\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))"
    if "\<tau>\<in>M" for \<tau>
  proof -
    let ?f_fm="snd_fm(1,0)"
    let ?g_fm="hcomp_fm(check_fm(6),fst_fm,2,0)"
    note assms
    moreover
    have "arity(forces(\<cdot>0`1 is 2\<cdot> )) \<le> 7"
      using arity_forces[of "\<cdot>0`1 is 2\<cdot> "] arity_fun_apply_fm union_abs1
      by simp
    moreover
    have "?f_fm \<in> formula" "arity(?f_fm) \<le> 7" "?g_fm \<in> formula" "arity(?g_fm) \<le> 8"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    ultimately
    show ?thesis
      using separation_sat_after_function that fst_abs snd_abs sats_check_fm check_abs
      unfolding hcomp_fm_def
      by simp
  qed
  moreover note assms
  ultimately
  show ?thesis
    using lam_replacement_imp_lam_closed lam_replacement_Collect' transitivity[of _ A]
      lam_replacement_constant lam_replacement_identity lam_replacement_snd
      lam_replacement_product separation_conj separation_in separation_bex separation_iff'
    by simp
qed

\<comment> \<open>Kunen IV.3.5\<close>
lemma ccc_fun_approximation_lemma:
  notes le_trans[trans]
  assumes "ccc\<^bsup>M\<^esup>(P,leq)" "A\<in>M" "B\<in>M" "f\<in>M[G]" "f : A \<rightarrow> B"
  shows
    "\<exists>F\<in>M. F : A \<rightarrow> Pow\<^bsup>M\<^esup>(B) \<and> (\<forall>a\<in>A. f`a \<in> F`a \<and> |F`a|\<^bsup>M\<^esup> \<le> \<omega>)"
proof -
  from \<open>f\<in>M[G]\<close>
  obtain f_dot where "f = val(G,f_dot)" "f_dot\<in>M" using GenExtD by force
  with assms
  obtain p where "p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]" "p\<in>G" "p\<in>M"
    using G_subset_M truth_lemma[of "\<cdot>0:1\<rightarrow>2\<cdot>" "[f_dot, A\<^sup>v, B\<^sup>v]"]
    by (auto simp add:ord_simp_union arity_typed_function_fm
        \<comment> \<open>NOTE: type-checking is not performed here by the Simplifier\<close>
        typed_function_type)
  define F where "F\<equiv>\<lambda>a\<in>A. {b\<in>B. \<exists>q\<in>P. q \<preceq> p \<and> (q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v])}"
  from assms \<open>f_dot\<in>_\<close> \<open>p\<in>M\<close>
  have "F \<in> M"
    unfolding F_def using ccc_fun_closed_lemma by simp
  moreover from calculation
  have "f`a \<in> F`a" if "a \<in> A" for a
  proof -
    note \<open>f: A \<rightarrow> B\<close> \<open>a \<in> A\<close>
    moreover from this
    have "f ` a \<in> B" by simp
    moreover
    note \<open>f\<in>M[G]\<close> \<open>A\<in>M\<close>
    moreover from calculation
    have "M[G], [f, a, f`a] \<Turnstile> \<cdot>0`1 is 2\<cdot>"
      by (auto dest:transitivity)
    moreover
    note \<open>B\<in>M\<close> \<open>f = val(G,f_dot)\<close>
    moreover from calculation
    have "a\<in>M" "val(G, f_dot)`a\<in>M"
      by (auto dest:transitivity)
    moreover
    note \<open>f_dot\<in>M\<close> \<open>p\<in>G\<close>
    ultimately
    obtain q where "q \<preceq> p" "q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, (f`a)\<^sup>v]" "q\<in>G"
      using forces_below_filter[of "\<cdot>0`1 is 2\<cdot>" "[f_dot, a\<^sup>v, (f`a)\<^sup>v]" p]
      by (auto simp add: ord_simp_union arity_fun_apply_fm
          fun_apply_type)
    with \<open>f`a \<in> B\<close>
    have "f`a \<in> {b\<in>B . \<exists>q\<in>P. q \<preceq> p \<and> q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]}"
      by blast
    with \<open>a\<in>A\<close>
    show ?thesis unfolding F_def by simp
  qed
  moreover
  have "|F`a|\<^bsup>M\<^esup> \<le> \<omega> \<and> F`a\<in>M" if "a \<in> A" for a
  proof -
    let ?Q="\<lambda>b. {q\<in>P. q \<preceq> p \<and> (q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v])}"
    from \<open>F \<in> M\<close> \<open>a\<in>A\<close> \<open>A\<in>M\<close>
    have "F`a \<in> M" "a\<in>M"
      using transitivity[OF _ \<open>A\<in>M\<close>] by simp_all
    moreover
    have 2:"\<And>x. x\<in>F`a \<Longrightarrow> x\<in>M"
      using transitivity[OF _ \<open>F`a\<in>M\<close>] by simp
    moreover
    have 3:"\<And>x. x\<in>F`a \<Longrightarrow> (##M)(?Q(x))"
      using ccc_fun_closed_lemma_aux[OF \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close> 2] transitivity[of _ "F`a"]
      by simp
    moreover
    have 4:"lam_replacement(##M,\<lambda>b. {q \<in> P . q \<preceq> p \<and> (M, [q, P, leq, \<one>, f_dot, a\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> ))})"
      using ccc_fun_closed_lemma_aux2[OF _ \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close>]
        lam_replacement_iff_lam_closed[THEN iffD2]
        ccc_fun_closed_lemma_aux[OF  \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close>]
      by simp
    ultimately
    interpret M_Pi_assumptions_choice "##M" "F`a" ?Q
      using Pi_replacement1[OF _ 3] lam_replacement_Sigfun[OF 4]
        lam_replacement_imp_strong_replacement
        ccc_fun_closed_lemma_aux[OF \<open>f_dot\<in>M\<close> \<open>p\<in>M\<close> \<open>a\<in>M\<close>]
        lam_replacement_hcomp2[OF lam_replacement_constant 4 _ _
          lam_replacement_minimum,unfolded lam_replacement_def]
      by unfold_locales simp_all
    from \<open>F`a \<in> M\<close>
    interpret M_Pi_assumptions2 "##M" "F`a" ?Q "\<lambda>_ . P"
      using lam_replacement_imp_strong_replacement[OF
          lam_replacement_Sigfun[OF lam_replacement_constant]]
        Pi_replacement1 transitivity[of _ "F`a"]
      by unfold_locales simp_all
    from \<open>p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]\<close> \<open>a\<in>A\<close>
    have "\<exists>y. y \<in> ?Q(b)" if "b \<in> F`a" for b
      using that unfolding F_def by auto
    then
    obtain q where "q \<in> Pi\<^bsup>M\<^esup>(F`a,?Q)" "q\<in>M" using AC_Pi_rel by auto
    moreover
    note \<open>F`a \<in> M\<close>
    moreover from calculation
    have "q : F`a \<rightarrow>\<^bsup>M\<^esup> P"
      using Pi_rel_weaken_type def_function_space_rel by auto
    moreover from calculation
    have "q : F`a \<rightarrow> range(q)" "q : F`a \<rightarrow> P" "q : F`a \<rightarrow>\<^bsup>M\<^esup> range(q)"
      using mem_function_space_rel_abs range_of_fun by simp_all
    moreover
    have "q`b \<bottom> q`c" if "b \<in> F`a" "c \<in> F`a" "b \<noteq> c"
      \<comment> \<open>For the next step, if the premise \<^term>\<open>b \<noteq> c\<close> is first,
        the proof breaks down badly\<close>
      for b c
    proof -
      from \<open>b \<in> F`a\<close> \<open>c \<in> F`a\<close> \<open>q \<in> Pi\<^bsup>M\<^esup>(F`a,?Q)\<close> \<open>q\<in>M\<close>
      have "q`b \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]"
        "q`c \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, c\<^sup>v]"
        using mem_Pi_rel_abs[of q] apply_type[of _ _  ?Q]
        by simp_all
      with \<open>b \<noteq> c\<close> \<open>q : F`a \<rightarrow> P\<close> \<open>a\<in>A\<close> \<open>b\<in>_\<close> \<open>c\<in>_\<close>
        \<open>A\<in>M\<close> \<open>f_dot\<in>M\<close> \<open>F`a\<in>M\<close>
      show ?thesis
        using forces_neq_apply_imp_incompatible
          transitivity[of _ A] transitivity[of _ "F`a"]
        by auto
    qed
    moreover from calculation
    have "antichain(P,leq,range(q))"
      using Pi_range_eq[of _  _ "\<lambda>_ . P"]
      unfolding antichain_def compat_in_def by auto
    moreover from this and \<open>q\<in>M\<close>
    have "antichain\<^bsup>M\<^esup>(P,leq,range(q))"
      by (simp add:absolut del:P_in_M)
    moreover from calculation
    have "q`b \<noteq> q`c" if "b \<noteq> c" "b \<in> F`a" "c \<in> F`a" for b c
      using that Incompatible_imp_not_eq apply_type
        mem_function_space_rel_abs by simp
    ultimately
    have "q \<in> inj\<^bsup>M\<^esup>(F`a,range(q))"
      using def_inj_rel by auto
    with \<open>F`a \<in> M\<close> \<open>q\<in>M\<close>
    have "|F`a|\<^bsup>M\<^esup> \<le> |range(q)|\<^bsup>M\<^esup>"
      using def_lepoll_rel
      by (rule_tac lepoll_rel_imp_cardinal_rel_le) auto
    also from \<open>antichain\<^bsup>M\<^esup>(P,leq,range(q))\<close> \<open>ccc\<^bsup>M\<^esup>(P,leq)\<close> \<open>q\<in>M\<close>
    have "|range(q)|\<^bsup>M\<^esup> \<le> \<omega>"
      using def_ccc_rel by simp
    finally
    show ?thesis using \<open>F`a\<in>M\<close> by auto
  qed
  moreover from this
  have "F`a\<in>M" if "a\<in>A" for a
    using that by simp
  moreover from this \<open>B\<in>M\<close>
  have "F : A \<rightarrow> Pow\<^bsup>M\<^esup>(B)"
    using Pow_rel_char
    unfolding F_def by (rule_tac lam_type) auto
  ultimately
  show ?thesis by auto
qed

end \<comment> \<open>G\_generic1\_lemmas bundle\<close>

end \<comment> \<open>\<^locale>\<open>G_generic3_AC\<close>\<close>

end