section\<open>Further instances of axiom-schemes\<close>

theory ZF_Trans_Interpretations
  imports
    Internal_ZFC_Axioms
    Replacement_Instances

begin

locale M_ZF2 = M_ZF1 +
  assumes
    replacement_ax2:
    "replacement_assm(M,env,ordtype_replacement_fm)"
    "replacement_assm(M,env,wfrec_ordertype_fm)"
    "replacement_assm(M,env,wfrec_Aleph_fm)"
    "replacement_assm(M,env,omap_replacement_fm)"

definition instances2_fms where "instances2_fms \<equiv>
  { ordtype_replacement_fm,
    wfrec_ordertype_fm,
    wfrec_Aleph_fm,
    omap_replacement_fm }"

lemmas replacement_instances2_defs =
  ordtype_replacement_fm_def wfrec_ordertype_fm_def
  wfrec_Aleph_fm_def omap_replacement_fm_def

declare (in M_ZF2) replacement_instances2_defs [simp]

locale M_ZF2_trans = M_ZF1_trans + M_ZF2

locale M_ZFC2 = M_ZFC1 + M_ZF2

locale M_ZFC2_trans = M_ZFC1_trans + M_ZF2_trans + M_ZFC2

locale M_ZF2_ground_notCH = M_ZF2 + M_ZF_ground_notCH

locale M_ZF2_ground_notCH_trans = M_ZF2_trans + M_ZF2_ground_notCH + M_ZF_ground_notCH_trans

locale M_ZFC2_ground_notCH = M_ZFC2 + M_ZF2_ground_notCH

locale M_ZFC2_ground_notCH_trans = M_ZFC2_trans + M_ZFC2_ground_notCH + M_ZF2_ground_notCH_trans

locale M_ZFC2_ground_CH_trans = M_ZFC2_ground_notCH_trans + M_ZF_ground_CH_trans

locale M_ctm2 = M_ctm1 + M_ZF2_ground_notCH_trans

locale M_ctm2_AC = M_ctm2 + M_ctm1_AC + M_ZFC2_ground_notCH_trans

locale M_ctm2_AC_CH = M_ctm2_AC + M_ZFC2_ground_CH_trans

lemmas (in M_ZF1_trans) separation_instances =
  separation_well_ord_iso
  separation_obase_equals separation_is_obase
  separation_PiP_rel separation_surjP_rel
  separation_radd_body separation_rmult_body

context M_ZF2_trans
begin

lemma replacement_HAleph_wfrec_repl_body:
  "B\<in>M \<Longrightarrow> strong_replacement(##M, HAleph_wfrec_repl_body(##M,B))"
  using strong_replacement_rel_in_ctm[where \<phi>="HAleph_wfrec_repl_body_fm(2,0,1)" and env="[B]"]
    zero_in_M arity_HAleph_wfrec_repl_body_fm replacement_ax2(3) ord_simp_union
  by simp

lemma HAleph_wfrec_repl:
  "(##M)(sa) \<Longrightarrow>
        (##M)(esa) \<Longrightarrow>
        (##M)(mesa) \<Longrightarrow>
        strong_replacement
         (##M,
          \<lambda>x z. \<exists>y[##M].
                   pair(##M, x, y, z) \<and>
                   (\<exists>f[##M].
                       (\<forall>z[##M].
                           z \<in> f \<longleftrightarrow>
                           (\<exists>xa[##M].
                               \<exists>y[##M].
                                  \<exists>xaa[##M].
                                     \<exists>sx[##M].
                                        \<exists>r_sx[##M].
                                           \<exists>f_r_sx[##M].
                                              pair(##M, xa, y, z) \<and>
                                              pair(##M, xa, x, xaa) \<and>
                                              upair(##M, xa, xa, sx) \<and>
                                              pre_image(##M, mesa, sx, r_sx) \<and> restriction(##M, f, r_sx, f_r_sx) \<and> xaa \<in> mesa \<and> is_HAleph(##M, xa, f_r_sx, y))) \<and>
                       is_HAleph(##M, x, f, y)))"
  using replacement_HAleph_wfrec_repl_body unfolding HAleph_wfrec_repl_body_def by simp

lemma replacement_is_order_eq_map:
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> strong_replacement(##M, order_eq_map(##M,A,r))"
  using strong_replacement_rel_in_ctm[where \<phi>="order_eq_map_fm(2,3,0,1)" and env="[A,r]"  and f="order_eq_map(##M,A,r)"]
    order_eq_map_iff_sats[where env="[_,_,A,r]"] zero_in_M fst_snd_closed pair_in_M_iff
    arity_order_eq_map_fm ord_simp_union replacement_ax2(4)
  by simp

end \<comment> \<open>\<^locale>\<open>M_ZF2_trans\<close>\<close>

definition omap_wfrec_body where
  "omap_wfrec_body(A,r) \<equiv> (\<cdot>\<exists>\<cdot>image_fm(2, 0, 1) \<and> pred_set_fm(A #+ 9, 3, r #+ 9, 0) \<cdot>\<cdot>)"

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

lemma arity_is_order_body: "arity(is_order_body_fm(1,0)) = 2"
   using arity_is_order_body_fm arity_is_ordertype ord_simp_union
   by (simp add:FOL_arities)


lemma (in M_ZF2_trans) replacement_is_order_body:
  "strong_replacement(##M, \<lambda>x z . \<exists>y[##M]. is_order_body(##M,x,y) \<and> z = \<langle>x,y\<rangle>)"
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f] \<Turnstile> (\<cdot>\<exists> \<cdot>is_order_body_fm(1,0) \<and> pair_fm(1,0,2) \<cdot>\<cdot>)",THEN iffD1])
   apply(simp add: is_order_body_iff_sats[where env="[_,_]",symmetric])
   apply(simp_all add:zero_in_M )
  apply(rule_tac replacement_ax2(1)[unfolded replacement_assm_def, rule_format, where env="[]",simplified])
    apply(simp_all add:arity_is_order_body arity pred_Un_distrib ord_simp_union)
  done

definition H_order_pred where
  "H_order_pred(A,r) \<equiv>  \<lambda>x f . f `` Order.pred(A, x, r)"

relationalize "H_order_pred" "is_H_order_pred"

lemma (in M_basic) H_order_pred_abs :
  "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(x) \<Longrightarrow> M(f) \<Longrightarrow> M(z) \<Longrightarrow>
    is_H_order_pred(M,A,r,x,f,z) \<longleftrightarrow> z = H_order_pred(A,r,x,f)"
  unfolding is_H_order_pred_def H_order_pred_def
  by simp

synthesize "is_H_order_pred" from_definition assuming "nonempty"

lemma (in M_ZF2_trans) wfrec_replacement_order_pred:
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> wfrec_replacement(##M, \<lambda>x g z. is_H_order_pred(##M,A,r,x,g,z) , r)"
  unfolding wfrec_replacement_def is_wfrec_def M_is_recfun_def is_H_order_pred_def
  apply(rule_tac strong_replacement_cong[
        where P="\<lambda> x f. M,[x,f,r,A] \<Turnstile> order_pred_wfrec_body_fm(3,2,1,0)",THEN iffD1])
   apply(subst order_pred_wfrec_body_def[symmetric])
   apply(rule_tac order_pred_wfrec_body_iff_sats[where env="[_,_,r,A]",symmetric])
           apply(simp_all add:zero_in_M)
  apply(rule_tac replacement_ax2(2)[unfolded replacement_assm_def, rule_format, where env="[r,A]",simplified])
    apply(simp_all add: arity_order_pred_wfrec_body_fm ord_simp_union)
  done

lemma (in M_ZF2_trans) wfrec_replacement_order_pred':
  "A\<in>M \<Longrightarrow> r\<in>M \<Longrightarrow> wfrec_replacement(##M, \<lambda>x g z. z = H_order_pred(A,r,x,g) , r)"
  using wfrec_replacement_cong[OF H_order_pred_abs[of A r,rule_format] refl,THEN iffD1,
      OF _ _ _ _ _ wfrec_replacement_order_pred[of A r]]
  by simp

sublocale M_ZF2_trans \<subseteq> M_pre_cardinal_arith "##M"
  using separation_instances wfrec_replacement_order_pred'[unfolded H_order_pred_def]
    replacement_is_order_eq_map[unfolded order_eq_map_def]
  by unfold_locales simp_all


definition is_well_ord_fst_snd where
  "is_well_ord_fst_snd(A,x) \<equiv> (\<exists>a[A]. \<exists>b[A]. is_well_ord(A,a,b) \<and> is_snd(A, x, b) \<and> is_fst(A, x, a))"

synthesize "is_well_ord_fst_snd" from_definition assuming "nonempty"
arity_theorem for "is_well_ord_fst_snd_fm"

lemma (in M_ZF2_trans) separation_well_ord: "separation(##M, \<lambda>x. is_well_ord(##M,fst(x), snd(x)))"
  using arity_is_well_ord_fst_snd_fm is_well_ord_iff_sats[symmetric] nonempty
    fst_closed snd_closed fst_abs snd_abs
    separation_in_ctm[where env="[]" and \<phi>="is_well_ord_fst_snd_fm(0)"]
  by(simp_all add: is_well_ord_fst_snd_def)


sublocale M_ZF2_trans \<subseteq> M_pre_aleph "##M"
  using HAleph_wfrec_repl replacement_is_order_body
    separation_well_ord separation_Pow_rel
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

lemma arity_is_Aleph[arity]: "arity(is_Aleph_fm(0, 1)) = 2"
  unfolding is_Aleph_fm_def
  using arity_transrec_fm[OF _ _ _ _ arity_is_HAleph_fm] ord_simp_union
  by simp

definition bex_Aleph_rel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "bex_Aleph_rel(M,x) \<equiv> \<lambda>y. \<exists>z\<in>x. y = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"

relationalize "bex_Aleph_rel" "is_bex_Aleph"

schematic_goal sats_is_bex_Aleph_fm_auto:
  "a \<in> nat \<Longrightarrow> c \<in> nat \<Longrightarrow> env \<in> list(A) \<Longrightarrow>
  a < length(env) \<Longrightarrow> c < length(env) \<Longrightarrow> 0 \<in> A \<Longrightarrow>
  is_bex_Aleph(##A, nth(a, env), nth(c, env)) \<longleftrightarrow> A, env \<Turnstile> ?fm(a, c)"
  unfolding is_bex_Aleph_def
  by (rule iff_sats | simp)+

synthesize_notc "is_bex_Aleph" from_schematic

lemma is_bex_Aleph_fm_type [TC]:
    "x \<in> \<omega> \<Longrightarrow> z \<in> \<omega> \<Longrightarrow> is_bex_Aleph_fm(x, z) \<in> formula"
  unfolding is_bex_Aleph_fm_def by simp

lemma sats_is_bex_Aleph_fm:
    "x \<in> \<omega> \<Longrightarrow>
    z \<in> \<omega> \<Longrightarrow> x < length(env) \<Longrightarrow> z < length(env) \<Longrightarrow>
    env \<in> list(Aa) \<Longrightarrow>
    0 \<in> Aa \<Longrightarrow>
    (Aa, env \<Turnstile> is_bex_Aleph_fm(x, z)) \<longleftrightarrow>
    is_bex_Aleph(##Aa,nth(x, env), nth(z, env))"
  using sats_is_bex_Aleph_fm_auto unfolding is_bex_Aleph_def is_bex_Aleph_fm_def
  by simp

lemma is_bex_Aleph_iff_sats [iff_sats]:
    "nth(x, env) = xa \<Longrightarrow>
    nth(z, env) = za \<Longrightarrow>
    x \<in> \<omega> \<Longrightarrow>
    z \<in> \<omega> \<Longrightarrow> x < length(env) \<Longrightarrow> z < length(env) \<Longrightarrow>
    env \<in> list(Aa) \<Longrightarrow>
    0 \<in> Aa \<Longrightarrow>
    is_bex_Aleph(##Aa, xa, za) \<longleftrightarrow>
    Aa, env \<Turnstile> is_bex_Aleph_fm(x, z)"
  using sats_is_bex_Aleph_fm by simp

arity_theorem for "is_bex_Aleph_fm"

lemma (in M_ZF1_trans) separation_is_bex_Aleph:
  assumes "(##M)(A)"
  shows "separation(##M,is_bex_Aleph(##M, A))"
  using assms separation_in_ctm[where env="[A]" and \<phi>="is_bex_Aleph_fm(1,0)",
      OF _ _ _ is_bex_Aleph_iff_sats[symmetric],
      of "\<lambda>_.A"]
    nonempty arity_is_bex_Aleph_fm is_bex_Aleph_fm_type
  by (simp add:ord_simp_union)

lemma (in M_pre_aleph) bex_Aleph_rel_abs:
  assumes "Ord(u)" "M(u)" "M(v)"
  shows "is_bex_Aleph(M, u, v) \<longleftrightarrow> bex_Aleph_rel(M,u,v)"
  unfolding is_bex_Aleph_def bex_Aleph_rel_def
  using assms is_Aleph_iff transM[of _ u] Ord_in_Ord
  by simp

lemma (in M_ZF2_trans) separation_bex_Aleph_rel:
  "Ord(x) \<Longrightarrow> (##M)(x) \<Longrightarrow> separation(##M, bex_Aleph_rel(##M,x))"
  using separation_is_bex_Aleph bex_Aleph_rel_abs
    separation_cong[where P="is_bex_Aleph(##M,x)" and M="##M",THEN iffD1]
  unfolding bex_Aleph_rel_def
  by simp

sublocale M_ZF2_trans \<subseteq> M_aleph "##M"
  using separation_bex_Aleph_rel[unfolded bex_Aleph_rel_def]
  by unfold_locales

sublocale M_ZF1_trans \<subseteq> M_FiniteFun "##M"
  using separation_is_function separation_omfunspace
  by unfold_locales simp

sublocale M_ZFC2_trans \<subseteq> M_cardinal_AC "##M"
  using lam_replacement_minimum
  by unfold_locales simp

(* TopLevel *)

lemma (in M_ZF1_trans) separation_cardinal_rel_lesspoll_rel:
  "(##M)(\<kappa>) \<Longrightarrow> separation(##M, \<lambda>x. x \<prec>\<^bsup>M\<^esup> \<kappa>)"
  using separation_in_ctm[where \<phi>="( \<cdot>0 \<prec> 1\<cdot> )" and env="[\<kappa>]"]
    is_lesspoll_iff nonempty
    arity_is_cardinal_fm arity_is_lesspoll_fm arity_is_bij_fm ord_simp_union
  by (simp add:FOL_arities)

sublocale M_ZFC2_trans \<subseteq> M_library "##M"
  using separation_cardinal_rel_lesspoll_rel lam_replacement_minimum
  by unfold_locales simp_all

locale M_ZF3 = M_ZF2 +
  assumes
    ground_replacements3:
    "ground_replacement_assm(M,env,ordtype_replacement_fm)"
    "ground_replacement_assm(M,env,wfrec_ordertype_fm)"
    "ground_replacement_assm(M,env,eclose_abs_fm)"
    "ground_replacement_assm(M,env,wfrec_rank_fm)"
    "ground_replacement_assm(M,env,transrec_VFrom_fm)"
    "ground_replacement_assm(M,env,eclose_closed_fm)"
    "ground_replacement_assm(M,env,wfrec_Aleph_fm)"
    "ground_replacement_assm(M,env,omap_replacement_fm)"

definition instances3_fms where "instances3_fms \<equiv>
  { ground_repl_fm(ordtype_replacement_fm),
    ground_repl_fm(wfrec_ordertype_fm),
    ground_repl_fm(eclose_abs_fm),
    ground_repl_fm(wfrec_rank_fm),
    ground_repl_fm(transrec_VFrom_fm),
    ground_repl_fm(eclose_closed_fm),
    ground_repl_fm(wfrec_Aleph_fm),
    ground_repl_fm(omap_replacement_fm) }"

text\<open>This set has $8$ internalized formulas, corresponding to the total
count of previous replacement instances (apart from those $5$ in
\<^term>\<open>instances_ground_fms\<close> and \<^term>\<open>instances_ground_notCH_fms\<close>,
and \<^term>\<open>dc_abs_fm\<close>).\<close>

definition overhead where
  "overhead \<equiv> instances1_fms \<union> instances_ground_fms"

definition overhead_notCH where
  "overhead_notCH \<equiv> overhead \<union> instances2_fms \<union>
     instances3_fms \<union> instances_ground_notCH_fms"

definition overhead_CH where
  "overhead_CH \<equiv> overhead_notCH \<union> { dc_abs_fm }"

text\<open>Hence, the “overhead” to create a proper extension of a ctm by forcing
consists of $7$ replacement instances. To force $\neg\CH$,
21 instances are need, and one further instance is required to
force $\CH$.\<close>

lemma instances2_fms_type[TC] : "instances2_fms \<subseteq> formula"
  unfolding instances2_fms_def replacement_instances2_defs
  by (auto simp del: Lambda_in_M_fm_def)

lemma overhead_type: "overhead \<subseteq> formula"
  using instances1_fms_type instances_ground_fms_type
  unfolding overhead_def replacement_instances1_defs
  by simp

lemma overhead_notCH_type: "overhead_notCH \<subseteq> formula"
  using overhead_type
  unfolding overhead_notCH_def recursive_construction_abs_fm_def
    recursive_construction_fm_def instances_ground_notCH_fms_def
    instances2_fms_def instances3_fms_def
  by (auto simp: replacement_instances1_defs
      replacement_instances2_defs simp del: Lambda_in_M_fm_def)

lemma overhead_CH_type: "overhead_CH \<subseteq> formula"
  using overhead_notCH_type unfolding overhead_CH_def dc_abs_fm_def
  by auto

locale M_ZF3_trans = M_ZF2_trans + M_ZF3

locale M_ZFC3 = M_ZFC2 + M_ZF3

locale M_ZFC3_trans = M_ZFC2_trans + M_ZF3_trans + M_ZFC3

locale M_ctm3 = M_ctm2 + M_ZF3_trans

locale M_ctm3_AC = M_ctm3 + M_ctm1_AC + M_ZFC3_trans

lemma M_satT_imp_M_ZF2: "(M \<Turnstile> ZF) \<Longrightarrow> M_ZF1(M)"
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
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff
      unfolding replacement_assm_def by simp_all
  }
  with fin
  show "M_ZF1(M)"
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

lemma M_satT_imp_M_ZFC1:
  shows "(M \<Turnstile> ZFC) \<longrightarrow> M_ZFC1(M)"
proof -
  have "(M \<Turnstile> ZF) \<and> choice_ax(##M) \<longrightarrow> M_ZFC1(M)"
    using M_satT_imp_M_ZF2[of M]
    unfolding M_ZFC1_def M_ZC_basic_def M_ZF1_def M_AC_def
    by auto
  then
  show ?thesis
    unfolding ZFC_def by auto
qed

lemma M_satT_instances1_imp_M_ZF1:
  assumes "(M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms })"
  shows "M_ZF1(M)"
proof -
  from assms
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_fin_def Zermelo_fms_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  moreover
  {
    fix \<phi> env
    from \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms }\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      unfolding Zermelo_fms_def ZF_def instances1_fms_def
      by auto
    moreover
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    ultimately
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      using sats_ZF_separation_fm_iff by simp_all
  }
  moreover
  {
    fix \<phi> env
    assume "\<phi> \<in> instances1_fms" "env\<in>list(M)"
    moreover from this and \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms }\<close>
    have "M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>" by auto
    ultimately
    have "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of \<phi>] instances1_fms_type
      unfolding replacement_assm_def by auto
  }
  ultimately
  show ?thesis
    unfolding instances1_fms_def
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

theorem M_satT_imp_M_ZF_ground_trans:
  assumes "Transset(M)" "M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}"
  shows "M_ZF_ground_trans(M)"
proof -
  from \<open>M \<Turnstile> \<cdot>Z\<cdot> \<union> _\<close>
  have "M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> instances1_fms }"
       "M \<Turnstile> {\<cdot>Replacement(p)\<cdot> . p \<in> instances_ground_fms }"
    unfolding overhead_def by auto
  then
  interpret M_ZF1 M
    using M_satT_instances1_imp_M_ZF1
    by simp
  from \<open>Transset(M)\<close>
  interpret M_ZF1_trans M
    using M_satT_imp_M_ZF2
    by unfold_locales
  {
    fix \<phi> env
    assume "\<phi> \<in> instances_ground_fms" "env\<in>list(M)"
    moreover from this and \<open>M \<Turnstile> {\<cdot>Replacement(p)\<cdot> . p \<in> instances_ground_fms}\<close>
    have "M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>" by auto
    ultimately
    have "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of \<phi>] instances_ground_fms_type
      unfolding replacement_assm_def by auto
  }
  then
  show ?thesis
    unfolding instances_ground_fms_def
    by unfold_locales (simp_all add:replacement_assm_def)
qed

theorem M_satT_imp_M_ZF_ground_notCH_trans:
  assumes
    "Transset(M)"
    "M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}"
  shows "M_ZF_ground_notCH_trans(M)"
proof -
  from assms
  interpret M_ZF_ground_trans M
    using M_satT_imp_M_ZF_ground_trans unfolding overhead_notCH_def by force
  {
    fix \<phi> env
    assume "\<phi> \<in> instances_ground_notCH_fms" "env\<in>list(M)"
    moreover from this and assms
    have "M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>"
      unfolding overhead_notCH_def by auto
    ultimately
    have "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of \<phi>] instances_ground_notCH_fms_type
      unfolding replacement_assm_def by auto
  }
  then
  show ?thesis
    by unfold_locales (simp_all add:replacement_assm_def instances_ground_notCH_fms_def)
qed

theorem M_satT_imp_M_ZF_ground_CH_trans:
  assumes
    "Transset(M)"
    "M \<Turnstile> \<cdot>Z\<cdot> \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_CH }"
  shows "M_ZF_ground_CH_trans(M)"
proof -
  from assms
  interpret M_ZF_ground_notCH_trans M
    using M_satT_imp_M_ZF_ground_notCH_trans unfolding overhead_CH_def by auto
  {
    fix env
    assume "env \<in> list(M)"
    moreover from assms
    have "M, [] \<Turnstile> \<cdot>Replacement(dc_abs_fm)\<cdot>"
      unfolding overhead_CH_def by auto
    ultimately
    have "arity(dc_abs_fm) \<le> succ(succ(length(env)))
      \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,dc_abs_fm,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of dc_abs_fm]
      unfolding replacement_assm_def
      by (auto simp:dc_abs_fm_def)
  }
  then
  show ?thesis
    by unfold_locales (simp_all add:replacement_assm_def)
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

sublocale M_ZF \<subseteq> M_ZF3
  using replacement_ax
  by unfold_locales (simp_all add:ground_replacement_assm_def)

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
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff
      unfolding replacement_assm_def by simp_all
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

sublocale M_ZFC \<subseteq> M_ZFC3
  by unfold_locales

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

lemma M_satT_imp_M_ZF3: "(M \<Turnstile> ZF) \<longrightarrow> M_ZF3(M)"
proof
  assume "M \<Turnstile> ZF"
  then
  interpret M_ZF M
    using M_satT_imp_M_ZF by simp
  show "M_ZF3(M)"
    by unfold_locales
qed

lemma M_satT_imp_M_ZFC3:
  shows "(M \<Turnstile> ZFC) \<longrightarrow> M_ZFC3(M)"
proof
  assume "M \<Turnstile> ZFC"
  then
  interpret M_ZFC M
    using M_ZFC_iff_M_satT  by simp
  show "M_ZFC3(M)"
    by unfold_locales
qed

lemma M_satT_overhead_imp_M_ZF3:
  "(M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}) \<longrightarrow> M_ZFC3(M)"
proof
  assume "M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)" "choice_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZC_def ZF_fin_def Zermelo_fms_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  moreover
  {
    fix \<phi> env
    from \<open>M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))"
      unfolding ZC_def Zermelo_fms_def ZF_def by auto
    moreover
    assume "\<phi> \<in> formula" "env\<in>list(M)"
    ultimately
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      using sats_ZF_separation_fm_iff by simp_all
  }
  moreover
  {
    fix \<phi> env
    assume "\<phi> \<in> overhead_notCH" "env\<in>list(M)"
    moreover from this and \<open>M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}\<close>
    have "M, [] \<Turnstile> \<cdot>Replacement(\<phi>)\<cdot>" by auto
    ultimately
    have "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_replacement_fm_iff[of \<phi>] overhead_notCH_type
      unfolding replacement_assm_def by auto
  }
  ultimately
  show "M_ZFC3(M)"
    unfolding overhead_def overhead_notCH_def instances1_fms_def
      instances2_fms_def instances3_fms_def
    by unfold_locales (simp_all add:replacement_assm_def ground_replacement_assm_def)
qed

end