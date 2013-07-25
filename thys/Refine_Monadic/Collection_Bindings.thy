header {* \isaheader{ICF Bindings} *}
theory Collection_Bindings
imports "../Collections/Collections" Refine
begin
text {*
  This theory sets up some lemmas that automate refinement proofs using
  the Isabelle Collection Framework (ICF).
  *}


lemma (in set) drh[refine_dref_RELATES]: 
  "RELATES (build_rel \<alpha> invar)" by (simp add: RELATES_def)
lemma (in map) drh[refine_dref_RELATES]: 
  "RELATES (build_rel \<alpha> invar)" by (simp add: RELATES_def)

lemma (in uprio) drh[refine_dref_RELATES]: "RELATES (build_rel \<alpha> invar)" 
  by (simp add: RELATES_def)
lemma (in prio) drh[refine_dref_RELATES]: "RELATES (build_rel \<alpha> invar)" 
  by (simp add: RELATES_def)


lemmas (in StdSet) [refine_hsimp] = correct
lemmas (in StdMap) [refine_hsimp] = correct

lemma (in set_sel') pick_ref[refine_hsimp]:
  "\<lbrakk> invar s; \<alpha> s \<noteq> {}\<rbrakk> \<Longrightarrow> the (sel' s (\<lambda>_. True)) \<in> \<alpha> s"
  by (auto elim!: sel'E)

text {* Wrapper to prevent higher-order unification problems *}
definition [simp, code_unfold]: "IT_tag x \<equiv> x"

lemma (in set_iteratei) it_is_iterator[refine_transfer]:
  "invar s \<Longrightarrow> set_iterator (IT_tag iteratei s) (\<alpha> s)"
  unfolding IT_tag_def by (rule iteratei_rule)

lemma (in map_iteratei) it_is_iterator[refine_transfer]:
  "invar m \<Longrightarrow> set_iterator (IT_tag iteratei m) (map_to_set (\<alpha> m))"
  unfolding IT_tag_def by (rule iteratei_rule)

text {*
  This definition is handy to be used on the abstract level.
*}
definition "prio_pop_min q \<equiv> do {
    ASSERT (dom q \<noteq> {});
    SPEC (\<lambda>(e,w,q'). 
      q'=q(e:=None) \<and> 
      q e = Some w \<and> 
      (\<forall> e' w'. q e' = Some w' \<longrightarrow> w\<le>w')
    )
  }"

lemma (in uprio_pop) prio_pop_min_refine[refine]:
  "(q,q')\<in>build_rel \<alpha> invar \<Longrightarrow> RETURN (pop q) 
    \<le> \<Down> (rprod Id (rprod Id (build_rel \<alpha> invar))) 
    (prio_pop_min q')"
  unfolding prio_pop_min_def
  apply refine_rcg
  apply clarsimp
  apply (erule (1) popE)
  apply (rule pw_leI)
  apply (auto simp: refine_pw_simps intro: ranI)
  done


lemma dres_ne_bot_iterate[refine_transfer]:
  assumes B: "set_iterator (IT_tag it r) S"
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "IT_tag it r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
  apply (rule_tac I="\<lambda>_ s. s\<noteq>dSUCCEED" in set_iterator_rule_P[OF B])
  apply (rule dres_ne_bot_basic A | assumption)+
  done

subsubsection {* Monotonicity for Iterators *}

lemma it_mono_aux:
  assumes COND: "\<And>\<sigma> \<sigma>'. \<sigma>\<le>\<sigma>' \<Longrightarrow> c \<sigma> \<noteq> c \<sigma>' \<Longrightarrow> \<sigma>=bot \<or> \<sigma>'=top "
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes B: "(\<sigma>::'a::{order_bot,order_top}) \<le> \<sigma>'"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l c f \<sigma> \<le> foldli l c f' \<sigma>'"
proof -
  { fix l 
    have "foldli l c f bot = bot" by (induct l) (auto simp: STRICT)
  } note [simp] = this
  { fix l 
    have "foldli l c f' top = top" by (induct l) (auto simp: STRICT)
  } note [simp] = this

  show ?thesis
    using B
    apply (induct l arbitrary: \<sigma> \<sigma>')
    apply (auto simp: A STRICT dest: COND)
    done
qed


lemma it_mono_aux_dres':
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l (dres_case True True c) f \<sigma> 
    \<le> foldli l (dres_case True True c) f' \<sigma>"
  apply (rule it_mono_aux)
  apply (simp_all split: dres.split_asm add: STRICT A)
  done

lemma it_mono_aux_dres:
  assumes A: "\<And>a x. f a x \<le> f' a x"
  shows "foldli l (dres_case True True c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> foldli l (dres_case True True c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
  apply (rule it_mono_aux_dres')
  apply (simp_all)
  apply (rule dbind_mono)
  apply (simp_all add: A)
  done
  
lemma iteratei_mono':
  assumes L: "set_iteratei \<alpha> invar it"
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  assumes I: "invar s"
  shows "IT_tag it s (dres_case True True c) f \<sigma> 
    \<le> IT_tag it s (dres_case True True c) f' \<sigma>"
  proof -
    from set_iteratei.iteratei_rule[OF L, OF I, unfolded set_iterator_foldli_conv]
    obtain l0 where l0_props: "distinct l0" "\<alpha> s = set l0" "it s = foldli l0" by blast
 
    from it_mono_aux_dres' [of f f' l0 c \<sigma>]
    show ?thesis
      unfolding IT_tag_def l0_props(3)
      by (simp add: STRICT A)
  qed

lemma iteratei_mono:
  assumes L: "set_iteratei \<alpha> invar it"
  assumes A: "\<And>a x. f a x \<le> f' a x"
  assumes I: "invar s"
  shows "IT_tag it s (dres_case True True c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> IT_tag it s (dres_case True True c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
 proof -
    from set_iteratei.iteratei_rule[OF L, OF I, unfolded set_iterator_foldli_conv]
    obtain l0 where l0_props: "distinct l0" "\<alpha> s = set l0" "it s = foldli l0" by blast
 
    from it_mono_aux_dres [of f f' l0 c \<sigma>]
    show ?thesis
      unfolding IT_tag_def l0_props(3)
      by (simp add: A)
  qed

lemmas [refine_mono] = iteratei_mono[OF ls_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF lsi_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF rs_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF ahs_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF ias_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF ts_iteratei_impl]
  
end
