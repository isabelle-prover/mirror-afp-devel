header {* More Linear Combinations *}

theory MoreLinearCombinations
imports Main
  "~~/src/HOL/Algebra/Module"
  "~~/src/HOL/Algebra/Coset"
  RingModuleFacts
  MoreMonoidSums
  FunctionLemmas
  LinearCombinations
begin

lemma (in mod_hom) lincomb_comp:
  fixes A B a b
  assumes fa: "finite A" and ca: "A\<subseteq>carrier M" and a:"a\<in>A\<rightarrow>carrier R" and 
    h1: "B = {f v | v. v\<in>A}" and h2: "\<And> w. w\<in> B\<Longrightarrow> (b w = (\<Oplus>\<^bsub>R\<^esub> v\<in> (f-`{w})\<inter>A . a v))"
      (is "\<And> w. w\<in> B\<Longrightarrow> (b w = ?bsum w)")
  shows "f (module.lincomb M a A) = module.lincomb N b B"  
proof - 
  from assms have 1: "f (\<Oplus>\<^bsub>M\<^esub>v\<in>A. a v \<odot>\<^bsub>M\<^esub> v) = (\<Oplus>\<^bsub>N\<^esub>v\<in>A. f (a v \<odot>\<^bsub>M\<^esub> v))"
    apply (intro hom_sum) 
    by auto
  from assms have 2: "(\<Oplus>\<^bsub>N\<^esub>v\<in>A. f (a v \<odot>\<^bsub>M\<^esub> v)) =(\<Oplus>\<^bsub>N\<^esub>v\<in>A. (a v \<odot>\<^bsub>N\<^esub> (f v)))"
    apply (intro finsum_cong') 
    by (auto intro!:f_smult)
  have 3: "\<And>v. v\<in>A \<Longrightarrow> finsum R a (f -` {f v} \<inter> A) \<odot>\<^bsub>N\<^esub> f v =
         (\<Oplus>\<^bsub>N\<^esub>w\<in>f -` {f v} \<inter> A. f (a w \<odot>\<^bsub>M\<^esub> v))"
  proof - 
    fix v
    assume 31: "v\<in>A"
    from assms 31 have 32: "(\<Oplus>\<^bsub>N\<^esub>w\<in>f -` {f v} \<inter> A. f (a w \<odot>\<^bsub>M\<^esub> v)) 
      = (\<Oplus>\<^bsub>N\<^esub>w\<in>f -` {f v} \<inter> A. (a w) \<odot>\<^bsub>N\<^esub> (f v))"
      by (auto intro!: finsum_cong' f_smult)
    from assms 31 have 33: "finsum R a (f -` {f v} \<inter> A) \<odot>\<^bsub>N\<^esub> f v
      = (\<Oplus>\<^bsub>N\<^esub>w\<in>f -` {f v} \<inter> A. (a w) \<odot>\<^bsub>N\<^esub> (f v))"
      apply (intro finsum_smult_r) by auto
    from 32 33 show "?thesis v" by auto
  qed

  from assms 3 have 4: "(\<Oplus>\<^bsub>N\<^esub>w\<in>A. a w \<odot>\<^bsub>N\<^esub> (f w)) = (\<Oplus>\<^bsub>N\<^esub>w\<in>B. b w \<odot>\<^bsub>N\<^esub> w)"
    apply (intro finsum_comp) apply auto
    apply (rename_tac v) apply (subst h2) apply force
    apply (subgoal_tac "finsum R a (f -` {f v} \<inter> A) \<odot>\<^bsub>N\<^esub> f v 
        = (\<Oplus>\<^bsub>N\<^esub>w\<in>f -` {f v} \<inter> A. a w \<odot>\<^bsub>N\<^esub> f v)")
      apply (subgoal_tac "(\<Oplus>\<^bsub>N\<^esub>w\<in>f -` {f v} \<inter> A. a w \<odot>\<^bsub>N\<^esub> f v)
        = (\<Oplus>\<^bsub>N\<^esub>w\<in>f -` {f v} \<inter> A. a w \<odot>\<^bsub>N\<^esub> f v)")
        apply clarsimp(* only apply to first goal *)
      apply (intro finsum_cong') 
      apply clarsimp 
      apply auto[1]
      apply auto[1]
      apply auto[1]
(*apply auto works but it rewrites ALL goals, and 
I don't want it to rewrite the last goal.*)
    apply (intro finsum_smult_l)
    by auto
  from 1 2 4 show ?thesis 
  apply (unfold lincomb_def M.lincomb_def) by auto
qed

