section\<open>Further instances of axiom-schemes\<close>

theory ZF_Trans_Interpretations
  imports
    Internal_ZFC_Axioms
    Succession_Poset
begin

locale M_ZF3 = M_ZF2 +
  assumes
    replacement_ax3:
    "replacement_assm(M,env,replacement_is_order_body_fm)"
    "replacement_assm(M,env,wfrec_replacement_order_pred_fm)"
    "replacement_assm(M,env,replacement_is_jump_cardinal_body_fm)"
    "replacement_assm(M,env,replacement_is_aleph_fm)"
    and
    LambdaPair_in_M_replacement3:
    "replacement_assm(M,env,LambdaPair_in_M_fm(is_inj_fm(0,1,2),0))"

definition instances3_fms where "instances3_fms \<equiv>
  { replacement_is_order_body_fm,
    wfrec_replacement_order_pred_fm,
    replacement_is_jump_cardinal_body_fm,
    replacement_is_aleph_fm,
    LambdaPair_in_M_fm(is_inj_fm(0,1,2),0) }"

txt\<open>This set has 5 internalized formulas.\<close>

lemmas replacement_instances3_defs =
  replacement_is_order_body_fm_def wfrec_replacement_order_pred_fm_def
  replacement_is_jump_cardinal_body_fm_def
  replacement_is_aleph_fm_def

declare (in M_ZF3) replacement_instances3_defs [simp]

locale M_ZF3_trans = M_ZF2_trans + M_ZF3

locale M_ZFC3 = M_ZFC2 + M_ZF3

locale M_ZFC3_trans = M_ZFC2_trans + M_ZF3_trans

locale M_ctm3 = M_ctm2 + M_ZF3_trans + M_ZF2_trans

locale M_ctm3_AC = M_ctm3 + M_ctm1_AC + M_ZFC3_trans

locale forcing_data3 = forcing_data2 + M_ctm3_AC

lemmas (in M_ZF2_trans) separation_instances =
  separation_well_ord
  separation_obase_equals separation_is_obase
  separation_PiP_rel separation_surjP_rel
  separation_radd_body separation_rmult_body

lemma (in M_ZF3_trans) lam_replacement_inj_rel:
  shows
    "lam_replacement(##M, \<lambda>p. inj\<^bsup>##M\<^esup>(fst(p),snd(p)))"
  using lam_replacement_iff_lam_closed[THEN iffD2,of "\<lambda>p. inj\<^bsup>M\<^esup>(fst(p),snd(p))"]
    LambdaPair_in_M[where \<phi>="is_inj_fm(0,1,2)" and is_f="is_inj(##M)" and env="[]",OF
      is_inj_fm_type _ is_inj_iff_sats[symmetric] inj_rel_iff,simplified]
    arity_is_inj_fm[of 0 1 2] ord_simp_union transitivity fst_snd_closed
    inj_rel_closed zero_in_M LambdaPair_in_M_replacement3
  by simp

arity_theorem for "is_transitive_fm"
arity_theorem for "is_linear_fm"
arity_theorem for "is_wellfounded_on_fm"
arity_theorem for "is_well_ord_fm"

arity_theorem for "pred_set_fm"
arity_theorem for "image_fm"
definition omap_wfrec_body where
  "omap_wfrec_body(A,r) \<equiv> (\<cdot>\<exists>\<cdot>image_fm(2, 0, 1) \<and>
               pred_set_fm
                (succ(succ(succ(succ(succ(succ(succ(succ(succ(A))))))))), 3,
                 succ(succ(succ(succ(succ(succ(succ(succ(succ(r))))))))), 0) \<cdot>\<cdot>)"

lemma type_omap_wfrec_body_fm :"A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow> omap_wfrec_body(A,r)\<in>formula"
  unfolding omap_wfrec_body_def by simp

lemma arity_aux : "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow> arity(omap_wfrec_body(A,r)) = (9+\<^sub>\<omega>A) \<union> (9+\<^sub>\<omega>r)"
  unfolding omap_wfrec_body_def
  using arity_image_fm arity_pred_set_fm pred_Un_distrib union_abs2[of 3] union_abs1
  by (simp add:FOL_arities, auto simp add:Un_assoc[symmetric] union_abs1)

lemma arity_omap_wfrec: "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow>
  arity(is_wfrec_fm(omap_wfrec_body(A,r),succ(succ(succ(r))), 1, 0)) =
  (4+\<^sub>\<omega>A) \<union> (4+\<^sub>\<omega>r)"
  using Arities.arity_is_wfrec_fm[OF _ _ _ _ _ arity_aux,of A r "3+\<^sub>\<omega>r" 1 0] pred_Un_distrib
    union_abs1 union_abs2 type_omap_wfrec_body_fm
  by auto

lemma arity_isordermap: "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow>d\<in>nat\<Longrightarrow>
   arity(is_ordermap_fm(A,r,d)) = succ(d) \<union> (succ(A) \<union> succ(r))"
  unfolding is_ordermap_fm_def
  using arity_lambda_fm[where i="(4+\<^sub>\<omega>A) \<union> (4+\<^sub>\<omega>r)",OF _ _ _ _ arity_omap_wfrec,
      unfolded omap_wfrec_body_def] pred_Un_distrib union_abs1
  by auto

lemma arity_is_ordertype: "A\<in>nat \<Longrightarrow> r\<in>nat \<Longrightarrow>d\<in>nat\<Longrightarrow>
   arity(is_ordertype_fm(A,r,d)) = succ(d) \<union> (succ(A) \<union> succ(r))"
  unfolding is_ordertype_fm_def
  using arity_isordermap arity_image_fm pred_Un_distrib FOL_arities
  by auto

arity_theorem for "is_order_body_fm"

lemma arity_is_order_body: "arity(is_order_body_fm(2,0,1)) = 3"
  using arity_is_order_body_fm arity_is_ordertype ord_simp_union
  by (simp add:FOL_arities)

lemma (in M_ZF3_trans) replacement_is_order_body:
  "X\<in>M \<Longrightarrow> strong_replacement(##M, is_order_body(##M,X))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,X] \<Turnstile> is_order_body_fm(2,0,1)",THEN iffD1])
   apply(rule_tac is_order_body_iff_sats[where env="[_,_,X]",symmetric])
          apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax3(1)[unfolded replacement_assm_def, rule_format, where env="[X]",simplified])
    apply(simp_all add: arity_is_order_body )
  done

lemma (in M_pre_cardinal_arith) is_order_body_abs :
  "M(X) \<Longrightarrow> M(x) \<Longrightarrow> M(z) \<Longrightarrow> is_order_body(M, X, x, z) \<longleftrightarrow>
   M(z) \<and> M(x) \<and> x\<in>Pow_rel(M,X\<times>X) \<and> well_ord(X, x) \<and> z = ordertype(X, x)"
  using well_ord_abs is_well_ord_iff_wellordered is_ordertype_iff' ordertype_rel_abs
    well_ord_is_linear subset_abs Pow_rel_char
  unfolding is_order_body_def
  by simp


definition H_order_pred where
  "H_order_pred(A,r) \<equiv>  \<lambda>x f . f `` Order.pred(A, x, r)"

relationalize "H_order_pred" "is_H_order_pred"

lemma (in M_basic) H_order_pred_abs :
  "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(x) \<Longrightarrow> M(f) \<Longrightarrow> M(z) \<Longrightarrow>
    is_H_order_pred(M,A,r,x,f,z) \<longleftrightarrow> z = H_order_pred(A,r,x,f)"
  unfolding is_H_order_pred_def H_order_pred_def
  by simp

synthesize "is_H_order_pred" from_definition assuming "nonempty"

lemma (in M_ZF3_trans) wfrec_replacement_order_pred:
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> wfrec_replacement(##M, \<lambda>x g z. is_H_order_pred(##M,A,r,x,g,z) , r)"
  unfolding wfrec_replacement_def is_wfrec_def M_is_recfun_def is_H_order_pred_def
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,r,A] \<Turnstile> order_pred_wfrec_body_fm(3,2,1,0)",THEN iffD1])
   apply(subst order_pred_wfrec_body_def[symmetric])
   apply(rule_tac order_pred_wfrec_body_iff_sats[where env="[_,_,r,A]",symmetric])
           apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax3(2)[unfolded replacement_assm_def, rule_format, where env="[r,A]",simplified])
    apply(simp_all add: arity_order_pred_wfrec_body_fm ord_simp_union)
  done

lemma (in M_ZF3_trans) wfrec_replacement_order_pred':
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> wfrec_replacement(##M, \<lambda>x g z. z = H_order_pred(A,r,x,g) , r)"
  using wfrec_replacement_cong[OF H_order_pred_abs[of A r,rule_format] refl,THEN iffD1,
      OF _ _ _ _ _ wfrec_replacement_order_pred[of A r]]
  by simp

sublocale M_ZF3_trans \<subseteq> M_pre_cardinal_arith "##M"
  using separation_instances wfrec_replacement_order_pred'[unfolded H_order_pred_def]
    replacement_is_order_eq_map[unfolded order_eq_map_def] banach_replacement
  by unfold_locales simp_all

lemma (in M_ZF3_trans) replacement_ordertype:
  "X\<in>M \<Longrightarrow> strong_replacement(##M, \<lambda>x z. z \<in> M \<and> x \<in> M \<and> x \<in> Pow\<^bsup>M\<^esup>(X \<times> X) \<and> well_ord(X, x) \<and> z = ordertype(X, x))"
  using strong_replacement_cong[THEN iffD1,OF _ replacement_is_order_body,simplified] is_order_body_abs
  unfolding is_order_body_def
  by simp

lemma arity_is_jump_cardinal_body: "arity(is_jump_cardinal_body'_fm(0,1)) = 2"
  unfolding is_jump_cardinal_body'_fm_def
  using arity_is_ordertype arity_is_well_ord_fm arity_is_Pow_fm arity_cartprod_fm
    arity_Replace_fm[where i=5] ord_simp_union FOL_arities
  by simp

lemma (in M_ZF3_trans) replacement_is_jump_cardinal_body:
  "strong_replacement(##M, is_jump_cardinal_body'(##M))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f] \<Turnstile> is_jump_cardinal_body'_fm(0,1)",THEN iffD1])
   apply(rule_tac is_jump_cardinal_body'_iff_sats[where env="[_,_]",symmetric])
        apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax3(3)[unfolded replacement_assm_def, rule_format, where env="[]",simplified])
   apply(simp_all add: arity_is_jump_cardinal_body )
  done

lemma (in M_pre_cardinal_arith) univalent_aux2: "M(X) \<Longrightarrow> univalent(M,Pow_rel(M,X\<times>X),
  \<lambda>r z. M(z) \<and> M(r) \<and> is_well_ord(M, X, r) \<and> is_ordertype(M, X, r, z))"
  using is_well_ord_iff_wellordered
    is_ordertype_iff[of _ X]
    trans_on_subset[OF well_ord_is_trans_on]
    well_ord_is_wf[THEN wf_on_subset_A] mem_Pow_rel_abs
  unfolding univalent_def
  by (simp)

lemma (in M_pre_cardinal_arith) is_jump_cardinal_body_abs :
  "M(X) \<Longrightarrow> M(c) \<Longrightarrow> is_jump_cardinal_body'(M, X, c) \<longleftrightarrow> c = jump_cardinal_body'_rel(M,X)"
  using well_ord_abs is_well_ord_iff_wellordered is_ordertype_iff' ordertype_rel_abs
    well_ord_is_linear subset_abs Pow_rel_iff Replace_abs[of "Pow_rel(M,X\<times>X)",OF _ _
      univalent_aux2]
  unfolding is_jump_cardinal_body'_def jump_cardinal_body'_rel_def
  by simp

lemma (in M_ZF3_trans) replacement_jump_cardinal_body:
  "strong_replacement(##M, \<lambda>x z. z \<in> M \<and> x \<in> M \<and> z = jump_cardinal_body(##M, x))"
  using strong_replacement_cong[THEN iffD1,OF _ replacement_is_jump_cardinal_body,simplified]
    jump_cardinal_body_eq is_jump_cardinal_body_abs
  by simp

sublocale M_ZF3_trans \<subseteq> M_pre_aleph "##M"
  using replacement_ordertype replacement_jump_cardinal_body HAleph_wfrec_repl
  by unfold_locales (simp_all add: transrec_replacement_def
      wfrec_replacement_def is_wfrec_def M_is_recfun_def flip:setclass_iff)

arity_theorem intermediate for "is_HAleph_fm"
lemma arity_is_HAleph_fm: "arity(is_HAleph_fm(2, 1, 0)) = 3"
  using arity_fun_apply_fm[of "11" 0 1,simplified]
    arity_is_HAleph_fm' arity_ordinal_fm arity_is_If_fm
    arity_empty_fm arity_is_Limit_fm
    arity_is_If_fm
    arity_is_Limit_fm arity_empty_fm
    arity_Replace_fm[where i="12" and v=10 and n=3]
    pred_Un_distrib ord_simp_union
  by (simp add:FOL_arities)

lemma arity_is_Aleph: "arity(is_Aleph_fm(0, 1)) = 2"
  unfolding is_Aleph_fm_def
  using arity_transrec_fm[OF _ _ _ _ arity_is_HAleph_fm] ord_simp_union
  by simp

lemma (in M_ZF3_trans) replacement_is_aleph:
  "strong_replacement(##M, \<lambda>x y. Ord(x) \<and> is_Aleph(##M,x,y))"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x y. M,[x,y] \<Turnstile> And(ordinal_fm(0),is_Aleph_fm(0,1))",THEN iffD1])
   apply (auto simp add: ordinal_iff_sats[where env="[_,_]",symmetric])
    apply(rule_tac is_Aleph_iff_sats[where env="[_,_]",THEN iffD2],simp_all add:zero_in_M)
   apply(rule_tac is_Aleph_iff_sats[where env="[_,_]",THEN iffD1],simp_all add:zero_in_M)
  apply(rule_tac replacement_ax3(4)[unfolded replacement_assm_def, rule_format, where env="[]",simplified])
   apply(simp_all add:arity_is_Aleph FOL_arities arity_ordinal_fm ord_simp_union is_Aleph_fm_type)
  done

lemma (in M_ZF3_trans) replacement_aleph_rel:
  shows  "strong_replacement(##M, \<lambda>x y. Ord(x) \<and> y = \<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>)"
  using strong_replacement_cong[THEN iffD2,OF _ replacement_is_aleph,where P1="\<lambda>x y . Ord(x) \<and> y=Aleph_rel(##M,x)"]
    is_Aleph_iff
  by auto

sublocale M_ZF3_trans \<subseteq> M_aleph "##M"
  by (unfold_locales,simp add: replacement_aleph_rel)

sublocale M_ZF2_trans \<subseteq> M_FiniteFun "##M"
  using separation_cons_like_rel separation_is_function
  by unfold_locales simp

sublocale M_ZFC1_trans \<subseteq> M_AC "##M"
  using choice_ax by (unfold_locales, simp_all)

sublocale M_ZFC3_trans \<subseteq> M_cardinal_AC "##M" ..

(* TopLevel *)

lemma (in M_ZF2_trans) separation_cardinal_rel_lesspoll_rel:
  "(##M)(\<kappa>) \<Longrightarrow> separation(##M, \<lambda>x. x \<prec>\<^bsup>M\<^esup> \<kappa>)"
  using separation_in_ctm[where \<phi>="( \<cdot>0 \<prec> 1\<cdot> )" and env="[\<kappa>]"]
    is_lesspoll_iff nonempty
    arity_is_cardinal_fm arity_is_lesspoll_fm arity_is_bij_fm ord_simp_union
  by (simp add:FOL_arities)

sublocale M_ZFC3_trans \<subseteq> M_library "##M"
  using separation_cardinal_rel_lesspoll_rel
  by unfold_locales simp_all

locale M_ZF4 = M_ZF3 +
  assumes
    ground_replacements4:
    "ground_replacement_assm(M,env,replacement_is_order_body_fm)"
    "ground_replacement_assm(M,env,wfrec_replacement_order_pred_fm)"
    "ground_replacement_assm(M,env,replacement_is_jump_cardinal_body_fm)"
    "ground_replacement_assm(M,env,replacement_is_aleph_fm)"
    "ground_replacement_assm(M,env,LambdaPair_in_M_fm(is_inj_fm(0,1,2),0))"
    "ground_replacement_assm(M,env,wfrec_Hfrc_at_fm)"
    "ground_replacement_assm(M,env,list_repl1_intf_fm)"
    "ground_replacement_assm(M,env,list_repl2_intf_fm)"
    "ground_replacement_assm(M,env,formula_repl2_intf_fm)"
    "ground_replacement_assm(M,env,eclose_repl2_intf_fm)"
    "ground_replacement_assm(M,env,powapply_repl_fm)"
    "ground_replacement_assm(M,env,phrank_repl_fm)"
    "ground_replacement_assm(M,env,wfrec_rank_fm)"
    "ground_replacement_assm(M,env,trans_repl_HVFrom_fm)"
    "ground_replacement_assm(M,env,wfrec_Hcheck_fm)"
    "ground_replacement_assm(M,env,repl_PHcheck_fm)"
    "ground_replacement_assm(M,env,check_replacement_fm)"
    "ground_replacement_assm(M,env,G_dot_in_M_fm)"
    "ground_replacement_assm(M,env,repl_opname_check_fm)"
    "ground_replacement_assm(M,env,tl_repl_intf_fm)"
    "ground_replacement_assm(M,env,formula_repl1_intf_fm)"
    "ground_replacement_assm(M,env,eclose_repl1_intf_fm)"
    "ground_replacement_assm(M,env,replacement_is_omega_funspace_fm)"
    "ground_replacement_assm(M,env,replacement_HAleph_wfrec_repl_body_fm)"
    "ground_replacement_assm(M,env,replacement_is_fst2_snd2_fm)"
    "ground_replacement_assm(M,env,replacement_is_sndfst_fst2_snd2_fm)"
    "ground_replacement_assm(M,env,replacement_is_order_eq_map_fm)"
    "ground_replacement_assm(M,env,replacement_transrec_apply_image_body_fm)"
    "ground_replacement_assm(M,env,banach_replacement_iterates_fm)"
    "ground_replacement_assm(M,env,replacement_is_trans_apply_image_fm)"
    "ground_replacement_assm(M,env,banach_iterates_fm)"
    "ground_replacement_assm(M,env,dcwit_repl_body_fm(6,5,4,3,2,0,1))"
    "ground_replacement_assm(M,env,Lambda_in_M_fm(fst_fm(0,1),0))"
    "ground_replacement_assm(M,env,Lambda_in_M_fm(big_union_fm(0,1),0))"
    "ground_replacement_assm(M,env,Lambda_in_M_fm(is_cardinal_fm(0,1),0))"
    "ground_replacement_assm(M,env,Lambda_in_M_fm(snd_fm(0,1),0))"
    "ground_replacement_assm(M,env,LambdaPair_in_M_fm(image_fm(0,1,2),0))"
    "ground_replacement_assm(M,env,LambdaPair_in_M_fm(setdiff_fm(0,1,2),0))"
    "ground_replacement_assm(M,env,LambdaPair_in_M_fm(minimum_fm(0,1,2),0))"
    "ground_replacement_assm(M,env,LambdaPair_in_M_fm(upair_fm(0,1,2),0))"
    "ground_replacement_assm(M,env,LambdaPair_in_M_fm(is_RepFun_body_fm(0,1,2),0))"
    "ground_replacement_assm(M,env,LambdaPair_in_M_fm(composition_fm(0,1,2),0))"
    "ground_replacement_assm(M,env,Lambda_in_M_fm(is_converse_fm(0,1),0))"
    "ground_replacement_assm(M,env,Lambda_in_M_fm(domain_fm(0,1),0))"

definition instances4_fms where "instances4_fms \<equiv>
  { ground_repl_fm(replacement_is_order_body_fm),
    ground_repl_fm(wfrec_replacement_order_pred_fm),
    ground_repl_fm(replacement_is_jump_cardinal_body_fm),
    ground_repl_fm(replacement_is_aleph_fm),
    ground_repl_fm(LambdaPair_in_M_fm(is_inj_fm(0,1,2),0)),
    ground_repl_fm(wfrec_Hfrc_at_fm),
    ground_repl_fm(list_repl1_intf_fm),
    ground_repl_fm(list_repl2_intf_fm),
    ground_repl_fm(formula_repl2_intf_fm),
    ground_repl_fm(eclose_repl2_intf_fm),
    ground_repl_fm(powapply_repl_fm),
    ground_repl_fm(phrank_repl_fm),
    ground_repl_fm(wfrec_rank_fm),
    ground_repl_fm(trans_repl_HVFrom_fm),
    ground_repl_fm(wfrec_Hcheck_fm),
    ground_repl_fm(repl_PHcheck_fm),
    ground_repl_fm(check_replacement_fm),
    ground_repl_fm(G_dot_in_M_fm),
    ground_repl_fm(repl_opname_check_fm),
    ground_repl_fm(tl_repl_intf_fm),
    ground_repl_fm(formula_repl1_intf_fm),
    ground_repl_fm(eclose_repl1_intf_fm),
    ground_repl_fm(replacement_is_omega_funspace_fm),
    ground_repl_fm(replacement_HAleph_wfrec_repl_body_fm),
    ground_repl_fm(replacement_is_fst2_snd2_fm),
    ground_repl_fm(replacement_is_sndfst_fst2_snd2_fm),
    ground_repl_fm(replacement_is_order_eq_map_fm),
    ground_repl_fm(replacement_transrec_apply_image_body_fm),
    ground_repl_fm(banach_replacement_iterates_fm),
    ground_repl_fm(replacement_is_trans_apply_image_fm),
    ground_repl_fm(banach_iterates_fm),
    ground_repl_fm(dcwit_repl_body_fm(6,5,4,3,2,0,1)),
    ground_repl_fm(Lambda_in_M_fm(fst_fm(0,1),0)),
    ground_repl_fm(Lambda_in_M_fm(big_union_fm(0,1),0)),
    ground_repl_fm(Lambda_in_M_fm(is_cardinal_fm(0,1),0)),
    ground_repl_fm(Lambda_in_M_fm(snd_fm(0,1),0)),
    ground_repl_fm(LambdaPair_in_M_fm(image_fm(0,1,2),0)),
    ground_repl_fm(LambdaPair_in_M_fm(setdiff_fm(0,1,2),0)),
    ground_repl_fm(LambdaPair_in_M_fm(minimum_fm(0,1,2),0)),
    ground_repl_fm(LambdaPair_in_M_fm(upair_fm(0,1,2),0)),
    ground_repl_fm(LambdaPair_in_M_fm(is_RepFun_body_fm(0,1,2),0)),
    ground_repl_fm(LambdaPair_in_M_fm(composition_fm(0,1,2),0)),
    ground_repl_fm(Lambda_in_M_fm(is_converse_fm(0,1),0)),
    ground_repl_fm(Lambda_in_M_fm(domain_fm(0,1),0)) }"

txt\<open>This set has 44 internalized formulas, corresponding to the total count
of previous replacement instances.\<close>

definition overhead where
  "overhead \<equiv> instances1_fms \<union> instances2_fms \<union> instances3_fms \<union> instances4_fms"

txt\<open>Hence, the “overhead” to force $\CH$ and its negation consists
of 88 replacement instances.\<close>

lemma instances3_fms_type[TC] : "instances3_fms \<subseteq> formula"
  unfolding instances3_fms_def replacement_is_order_body_fm_def
    wfrec_replacement_order_pred_fm_def replacement_is_jump_cardinal_body_fm_def
    replacement_is_aleph_fm_def
  by (auto simp del: Lambda_in_M_fm_def
      ccc_fun_closed_lemma_aux2_fm_def ccc_fun_closed_lemma_fm_def)

lemma overhead_type: "overhead \<subseteq> formula"
  using instances1_fms_type instances2_fms_type
  unfolding overhead_def instances3_fms_def instances4_fms_def
    replacement_instances1_defs replacement_instances2_defs replacement_instances3_defs
  using ground_repl_fm_type Lambda_in_M_fm_type
  by (auto simp del: Lambda_in_M_fm_def
      ccc_fun_closed_lemma_aux2_fm_def ccc_fun_closed_lemma_fm_def)

locale M_ZF4_trans = M_ZF3_trans + M_ZF4

locale M_ZFC4 = M_ZFC3 + M_ZF4

locale M_ZFC4_trans = M_ZFC3_trans + M_ZF4_trans

locale M_ctm4 = M_ctm3 + M_ZF4_trans

locale M_ctm4_AC = M_ctm4 + M_ctm1_AC + M_ZFC4_trans

locale forcing_data4 = forcing_data3 + M_ctm4_AC

lemma M_satT_imp_M_ZF2: "(M \<Turnstile> ZF) \<Longrightarrow> M_ZF2(M)"
proof -
  assume "M \<Turnstile> ZF"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  {
    fix \<phi> env
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    moreover from \<open>M \<Turnstile> ZF\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
      unfolding ZF_def ZF_schemes_def by auto
    moreover from calculation
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff by simp_all
  }
  with fin
  show "M_ZF2(M)"
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

lemma M_satT_imp_M_ZFC2:
  shows "(M \<Turnstile> ZFC) \<longrightarrow> M_ZFC2(M)"
proof -
  have "(M \<Turnstile> ZF) \<and> choice_ax(##M) \<longrightarrow> M_ZFC2(M)"
    using M_satT_imp_M_ZF2[of M] unfolding M_ZF2_def M_ZFC1_def M_ZFC2_def
      M_ZC_basic_def M_ZF1_def M_AC_def by auto
  then
  show ?thesis
    unfolding ZFC_def by auto
qed

lemma M_satT_instances12_imp_M_ZF2:
  assumes "(M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms})"
  shows "M_ZF2(M)"
proof -
  from assms
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_fin_def Zermelo_fms_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  moreover
  {
    fix \<phi> env
    from \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms}\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      unfolding Zermelo_fms_def ZF_def instances1_fms_def
        instances2_fms_def by auto
    moreover
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    ultimately
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      using sats_ZF_separation_fm_iff by simp_all
  }
  moreover
  {
    fix \<phi> env
    assume "\<phi> \<in> instances1_fms \<union> instances2_fms" "env\<in>list(M)"
    moreover from this and \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms \<union> instances2_fms}\<close>
    have "M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>" by auto
    ultimately
    have "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of \<phi>] instances1_fms_type instances2_fms_type by auto
  }
  ultimately
  show ?thesis
    unfolding instances1_fms_def instances2_fms_def
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

lemma (in M_Z_basic) M_satT_Zermelo_fms: "M \<Turnstile> \<cdot>Z\<cdot>"
  using upair_ax Union_ax power_ax extensionality foundation_ax
    infinity_ax separation_ax sats_ZF_separation_fm_iff
  unfolding Zermelo_fms_def ZF_fin_def
  by auto

lemma (in M_ZFC1) M_satT_ZC: "M \<Turnstile> ZC"
  using upair_ax Union_ax power_ax extensionality foundation_ax
    infinity_ax separation_ax sats_ZF_separation_fm_iff choice_ax
  unfolding ZC_def Zermelo_fms_def ZF_fin_def
  by auto

locale M_ZF = M_Z_basic +
  assumes
    replacement_ax:"replacement_assm(M,env,\<phi>)"

lemma M_satT_imp_M_ZF: " M \<Turnstile> ZF \<Longrightarrow> M_ZF(M)"
proof -
  assume "M \<Turnstile> ZF"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  {
    fix \<phi> env
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    moreover from \<open>M \<Turnstile> ZF\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
      unfolding ZF_def ZF_schemes_def by auto
    moreover from calculation
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff by simp_all
  }
  with fin
  show "M_ZF(M)"
    unfolding M_ZF_def M_Z_basic_def M_ZF_axioms_def replacement_assm_def by simp
qed

lemma (in M_ZF) M_satT_ZF: "M \<Turnstile> ZF"
  using upair_ax Union_ax power_ax extensionality foundation_ax
    infinity_ax separation_ax sats_ZF_separation_fm_iff
    replacement_ax sats_ZF_replacement_fm_iff
  unfolding ZF_def ZF_schemes_def ZF_fin_def replacement_assm_def
  by auto

lemma M_ZF_iff_M_satT: "M_ZF(M) \<longleftrightarrow> (M \<Turnstile> ZF)"
  using M_ZF.M_satT_ZF M_satT_imp_M_ZF
  by auto

locale M_ZFC = M_ZF + M_ZC_basic

lemma M_ZFC_iff_M_satT:
  notes iff_trans[trans]
  shows "M_ZFC(M) \<longleftrightarrow> (M \<Turnstile> ZFC)"
proof -
  have "M_ZFC(M) \<longleftrightarrow> (M \<Turnstile> ZF) \<and> choice_ax(##M)"
    using M_ZF_iff_M_satT
    unfolding M_ZFC_def M_ZC_basic_def M_AC_def M_ZF_def by auto
  also
  have " \<dots> \<longleftrightarrow> M \<Turnstile> ZFC"
    unfolding ZFC_def by auto
  ultimately
  show ?thesis by simp
qed

lemma M_satT_imp_M_ZF4: "(M \<Turnstile> ZF) \<longrightarrow> M_ZF4(M)"
proof
  assume "M \<Turnstile> ZF"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  {
    fix \<phi> env
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    moreover from \<open>M \<Turnstile> ZF\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
      unfolding ZF_def ZF_schemes_def by auto
    moreover from calculation
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff by simp_all
  }
  with fin
  show "M_ZF4(M)"
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

lemma M_satT_imp_M_ZFC4:
  shows "(M \<Turnstile> ZFC) \<longrightarrow> M_ZFC4(M)"
proof -
  have "(M \<Turnstile> ZF) \<and> choice_ax(##M) \<longrightarrow> M_ZFC4(M)"
    using M_satT_imp_M_ZF4[of M] unfolding M_ZF4_def M_ZFC1_def M_ZFC4_def
      M_ZF3_def M_ZFC3_def M_ZF2_def M_ZFC2_def
      M_ZC_basic_def M_ZF1_def M_AC_def by auto
  then
  show ?thesis
    unfolding ZFC_def by auto
qed

lemma M_satT_overhead_imp_M_ZF4:
  "(M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}) \<longrightarrow> M_ZFC4(M)"
proof
  assume "M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)" "choice_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZC_def ZF_fin_def Zermelo_fms_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  moreover
  {
    fix \<phi> env
    from \<open>M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      unfolding ZC_def Zermelo_fms_def ZF_def overhead_def instances1_fms_def
        instances2_fms_def instances3_fms_def instances4_fms_def by auto
    moreover
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    ultimately
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      using sats_ZF_separation_fm_iff by simp_all
  }
  moreover
  {
    fix \<phi> env
    assume "\<phi> \<in> overhead" "env\<in>list(M)"
    moreover from this and \<open>M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}\<close>
    have "M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>" by auto
    ultimately
    have "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of \<phi>] overhead_type by auto
  }
  ultimately
  show "M_ZFC4(M)"
    unfolding overhead_def instances1_fms_def
      instances2_fms_def instances3_fms_def instances4_fms_def
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

end