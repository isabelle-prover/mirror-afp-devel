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


definition lift_set_iterator ::
  "('s,'x,'\<sigma>) iteratori \<Rightarrow> 's \<Rightarrow> ('x,'\<sigma>) iteratori_tmpl"
  where [simp, code_unfold]: 
  "lift_set_iterator it s \<equiv> (\<lambda>c f \<sigma>0. it c f s \<sigma>0)"

definition lift_map_iterator ::
  "('s,'k,'v,'\<sigma>) map_iteratori \<Rightarrow> 's \<Rightarrow> ('k\<times>'v,'\<sigma>) iteratori_tmpl"
  where [simp, code_unfold]: 
  "lift_map_iterator it s \<equiv> (\<lambda>c f \<sigma>0. it c (\<lambda>k v \<sigma>. f (k,v) \<sigma>) s \<sigma>0)"

lemma (in set_iteratei) it_is_iteratori[refine_transfer]:
  "invar s \<Longrightarrow> set_iteratori (lift_set_iterator iteratei s) (\<alpha> s)"
  apply simp
  apply unfold_locales
  apply (rule iteratei_rule)
  apply auto
  done

lemma map_is_iteratori_aux: 
  "kvset m \<inter> ((it-{k})\<times>UNIV) = (kvset m\<inter>it\<times>UNIV) - {(k,the (m k))}"
  by (auto simp add: kvset_def)

(*
  "invar s \<Longrightarrow> set_iteratori 
                 ((\<lambda>c f \<sigma>0. iterator_tag iteratei c (\<lambda>k v \<sigma>. f (k,v) \<sigma>) s \<sigma>0))
                 (kvset (\<alpha> s))"
*)

lemma (in map_iteratei) it_is_iteratori[refine_transfer]:
  "invar s \<Longrightarrow> set_iteratori 
                 (lift_map_iterator iteratei s)
                 (kvset (\<alpha> s))"
  apply simp
  apply unfold_locales
  apply (rule_tac I="\<lambda>it \<sigma>. I (kvset (\<alpha> s) \<inter> it\<times>UNIV) \<sigma>" in iteratei_rule_P)
  apply simp
  apply simp
  apply (simp add: map_is_iteratori_aux)
  apply simp
  apply simp
  apply (rule disjI2)
  apply (rule_tac x="kvset (\<alpha> s) \<inter> it\<times>UNIV" in exI)
  apply (simp)
  apply auto
  apply (subgoal_tac "(x,the (\<alpha> s x))\<in>kvset (\<alpha> s)")
  apply blast
  apply (auto simp: kvset_def)
  done

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
  assumes B: "set_iteratori (lift_set_iterator it r) S"
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "lift_set_iterator it r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
proof -
  interpret set_iteratori "(lift_set_iterator it r)" S 
    using B .
  show ?thesis
    apply (rule_tac I="\<lambda>_ s. s\<noteq>dSUCCEED" in iterate_rule_P)
    apply (rule dres_ne_bot_basic A | assumption)+
    done
qed

subsubsection {* Monotonicity for Iterators *}

locale set_listable_iteratei = finite_set +
  constrains \<alpha> :: "'s \<Rightarrow> 'x set"
  fixes iteratei :: "('s,'x,'\<sigma>) iteratori"
  fixes it_seq :: "'s \<Rightarrow> 'x list"
  assumes distinct: "invar s \<Longrightarrow> distinct (it_seq s)"
  assumes is_set: "invar s \<Longrightarrow> set (it_seq s) = \<alpha> s"
  assumes listable: 
    "invar s \<Longrightarrow> iteratei c f s \<sigma>0 = Dlist_add.iteratei_aux c f (it_seq s) \<sigma>0"

sublocale set_listable_iteratei < set_iteratei \<alpha> invar iteratei
  apply unfold_locales
  apply (unfold listable is_set[symmetric])
  apply (rule Dlist_add.iteratei_aux_correct)
  apply (simp_all add: distinct)
  done


lemma it_mono_aux:
  assumes COND: "\<And>\<sigma> \<sigma>'. \<sigma>\<le>\<sigma>' \<Longrightarrow> c \<sigma> \<noteq> c \<sigma>' \<Longrightarrow> \<sigma>=bot \<or> \<sigma>'=top "
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes B: "\<sigma>\<le>\<sigma>'"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "iteratei_aux c f l \<sigma> \<le> iteratei_aux c f' l \<sigma>'"
proof -
  { fix l 
    have "iteratei_aux c f l bot = bot" by (induct l) (auto simp: STRICT)
  } note [simp] = this
  { fix l 
    have "iteratei_aux c f' l top = top" by (induct l) (auto simp: STRICT)
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
  shows "iteratei_aux (dres_case True True c) f l \<sigma> 
    \<le> iteratei_aux (dres_case True True c) f' l \<sigma>"
  apply (rule it_mono_aux)
  apply (simp_all split: dres.split_asm add: STRICT A)
  done

lemma it_mono_aux_dres:
  assumes A: "\<And>a x. f a x \<le> f' a x"
  shows "iteratei_aux (dres_case True True c) (\<lambda>x s. dbind s (f x)) l \<sigma> 
    \<le> iteratei_aux (dres_case True True c) (\<lambda>x s. dbind s (f' x)) l \<sigma>"
  apply (rule it_mono_aux_dres')
  apply (simp_all)
  apply (rule dbind_mono)
  apply (simp_all add: A)
  done
  
lemma listable_mono':
  assumes L: "set_listable_iteratei \<alpha> invar it seq"
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  assumes I: "invar s"
  shows "it (dres_case True True c) f s \<sigma> 
    \<le> it (dres_case True True c) f' s \<sigma>"
  apply (unfold set_listable_iteratei.listable[OF L, OF I])
  apply (rule it_mono_aux_dres')
  apply (simp_all add: STRICT A)
  done

lemma listable_mono:
  assumes L: "set_listable_iteratei \<alpha> invar it seq"
  assumes A: "\<And>a x. f a x \<le> f' a x"
  assumes I: "invar s"
  shows "(lift_set_iterator it s) 
      (dres_case True True c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> (lift_set_iterator it s) 
      (dres_case True True c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
  apply simp
  apply (unfold set_listable_iteratei.listable[OF L, OF I])
  apply (rule it_mono_aux_dres)
  apply (simp_all add: A)
  done

lemma ls_it_listable: 
  "set_listable_iteratei ls_\<alpha> ls_invar ls_iteratei ls_to_list"
  apply (unfold_locales)
  apply (simp add: ls_to_list_def)
  apply (simp add: ls_correct)
  apply (simp add: ls_iteratei_def iteratei_def ls_to_list_def)
  done

lemmas [refine_mono] = listable_mono[OF ls_it_listable]

(* TODO: Prove other iterators from ICF as monotonic (via listable!) *)
  
end
