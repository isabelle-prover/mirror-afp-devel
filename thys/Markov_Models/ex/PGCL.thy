(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section {* Probabilistic Guarded Command Language (pGCL) *}

theory PGCL
  imports "../Markov_Decision_Process"
begin

datatype 's pgcl =
    Skip
  | Abort
  | Assign "'s \<Rightarrow> 's"
  | Seq "'s pgcl" "'s pgcl"
  | Par "'s pgcl" "'s pgcl"
  | If "'s \<Rightarrow> bool" "'s pgcl" "'s pgcl"
  | Prob "bool pmf" "'s pgcl" "'s pgcl"
  | While "'s \<Rightarrow> bool" "'s pgcl"

primrec wp :: "'s pgcl \<Rightarrow> ('s \<Rightarrow> ereal) \<Rightarrow> ('s \<Rightarrow> ereal)" where
  "wp Skip f          = f"
| "wp Abort f         = (\<lambda>_. 0)"
| "wp (Assign u) f    = f \<circ> u"
| "wp (Seq c\<^sub>1 c\<^sub>2) f    = wp c\<^sub>1 (wp c\<^sub>2 f)"
| "wp (If b c\<^sub>1 c\<^sub>2) f   = (\<lambda>s. if b s then wp c\<^sub>1 f s else wp c\<^sub>2 f s)"
| "wp (Par c\<^sub>1 c\<^sub>2) f    = wp c\<^sub>1 f \<sqinter> wp c\<^sub>2 f"
| "wp (Prob p c\<^sub>1 c\<^sub>2) f = (\<lambda>s. pmf p True * wp c\<^sub>1 f s + pmf p False * wp c\<^sub>2 f s)"
| "wp (While b c) f   = lfp (\<lambda>X s. if b s then wp c ((\<lambda>_. 0) \<squnion> X) s else f s)"

lemma wp_mono: "mono (wp c)"
  by (induction c)
     (auto simp: mono_def le_fun_def min_le_iff_disj intro: order_trans
           intro!: ereal_add_mono ereal_mult_left_mono pmf_nonneg max.coboundedI2
                   lfp_mono[THEN le_funD])

lemma wp_nonneg: "(\<And>x. 0 \<le> f x) \<Longrightarrow> 0 \<le> wp c f s"
proof (induction c arbitrary: f s)
  case (While g c)
  have "(\<lambda>_. 0) \<le> lfp (\<lambda>X s. if g s then wp c ((\<lambda>_. 0) \<squnion> X) s else f s)"
  proof (intro lfp_greatest)
    fix u assume "(\<lambda>s. if g s then wp c ((\<lambda>_. 0) \<squnion> u) s else f s) \<le> u" then show "(\<lambda>_. 0) \<le> u"
      by (rule order_trans[rotated]) (auto simp: le_fun_def While)
  qed
  then show ?case
    by (simp add: le_fun_def)
qed (auto intro!: ereal_add_nonneg_nonneg ereal_0_le_mult pmf_nonneg)

abbreviation det :: "'s pgcl \<Rightarrow> 's \<Rightarrow> ('s pgcl \<times> 's) pmf set" ("\<lless> _, _ \<ggreater>") where
  "det c s \<equiv> {return_pmf (c, s)}" 

fun step :: "('s pgcl \<times> 's) \<Rightarrow> ('s pgcl \<times> 's) pmf set" where
  "step (Skip, s)        = \<lless>Skip, s\<ggreater>"
| "step (Abort, s)       = \<lless>Abort, s\<ggreater>"
| "step (Assign u, s)    = \<lless>Skip, u s\<ggreater>"
| "step (Seq c\<^sub>1 c\<^sub>2, s)    = (map_pmf (\<lambda>(p1', s'). (if p1' = Skip then c\<^sub>2 else Seq p1' c\<^sub>2, s'))) ` step (c\<^sub>1, s)"
| "step (If b c\<^sub>1 c\<^sub>2, s)   = (if b s then \<lless>c\<^sub>1, s\<ggreater> else \<lless>c\<^sub>2, s\<ggreater>)"
| "step (Par c\<^sub>1 c\<^sub>2, s)    = \<lless>c\<^sub>1, s\<ggreater> \<union> \<lless>c\<^sub>2, s\<ggreater>"
| "step (Prob p c\<^sub>1 c\<^sub>2, s) = {map_pmf (\<lambda>b. if b then (c\<^sub>1, s) else (c\<^sub>2, s)) p}"
| "step (While b c, s)   = (if b s then \<lless>Seq c (While b c), s\<ggreater> else \<lless>Skip, s\<ggreater>)"

lemma step_finite: "finite (step x)"
  by (induction x rule: step.induct) simp_all

lemma step_non_empty: "step x \<noteq> {}"
  by (induction x rule: step.induct) simp_all

interpretation step: Markov_Decision_Process step
  proof qed (rule step_non_empty)

definition rF :: "('s \<Rightarrow> ereal) \<Rightarrow> (('s pgcl \<times> 's) stream \<Rightarrow> ereal) \<Rightarrow> ('s pgcl \<times> 's) stream \<Rightarrow> ereal" where
  "rF f F \<omega> = 0 \<squnion> (if fst (shd \<omega>) = Skip then f (snd (shd \<omega>)) else F (stl \<omega>))"

abbreviation r :: "('s \<Rightarrow> ereal) \<Rightarrow> ('s pgcl \<times> 's) stream \<Rightarrow> ereal" where
  "r f \<equiv> lfp (rF f)"

lemma continuous_rF: "sup_continuous (rF f)"
  unfolding rF_def[abs_def]
  by (auto simp: sup_continuous_def fun_eq_iff SUP_sup_distrib[symmetric]
           simp del: sup_ereal_def
           split: prod.splits pgcl.splits)

lemma mono_rF: "mono (rF f)"
  using continuous_rF by (rule sup_continuous_mono)

lemma r_unfold: "r f \<omega> = 0 \<squnion> (if fst (shd \<omega>) = Skip then f (snd (shd \<omega>)) else r f (stl \<omega>))"
  by (subst lfp_unfold[OF mono_rF]) (simp add: rF_def)

lemma mono_r: "F \<le> G \<Longrightarrow> r F \<omega> \<le> r G \<omega>"
  by (rule le_funD[of _ _ \<omega>], rule lfp_mono)
     (auto intro!: lfp_mono simp: rF_def le_fun_def max.coboundedI2)

lemma measurable_rF: 
  assumes F[measurable]: "F \<in> borel_measurable step.St"
  shows "rF f F \<in> borel_measurable step.St"
  unfolding rF_def[abs_def]
  apply measurable
  apply (rule measurable_compose[OF measurable_shd])
  apply measurable []
  apply (rule measurable_compose[OF measurable_stl])
  apply measurable []
  apply (rule predE)
  apply (rule measurable_compose[OF measurable_shd])
  apply measurable
  done

lemma measurable_r[measurable]: "r f \<in> borel_measurable step.St"
  using continuous_rF measurable_rF by (rule borel_measurable_lfp)

lemma mono_r': "mono (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>D)"
  by (auto intro!: monoI le_funI INF_mono[OF bexI] nn_integral_mono simp: le_fun_def)

lemma E_inf_r:
  "step.E_inf s (r f) =
    lfp (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>D) s"
proof -
  have "step.E_inf s (r f) =
    lfp (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. 0 \<squnion> (if fst t = Skip then f (snd t) else F t) \<partial>D) s"
    unfolding rF_def[abs_def]
  proof (rule step.E_inf_lfp[THEN fun_cong])
    let ?F = "\<lambda>t x. 0 \<squnion> (if fst t = Skip then f (snd t) else x)"
    show "(\<lambda>(s, x). ?F s x) \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
      apply (simp add: measurable_split_conv split_beta')
      apply (intro borel_measurable_max borel_measurable_const measurable_If predE
         measurable_compose[OF measurable_snd] measurable_compose[OF measurable_fst])
      apply measurable
      done
    show "\<And>s. sup_continuous (?F s)"
      by (auto simp: sup_continuous_def SUP_sup_distrib[symmetric]
               simp del: sup_ereal_def split: prod.split pgcl.split)
    show "\<And>F cfg. (\<integral>\<^sup>+\<omega>. ?F (state cfg) (F \<omega>) \<partial>step.T cfg) =
      ?F (state cfg) (nn_integral (step.T cfg) F)"
      by (auto simp: max_absorb2 nn_integral_nonneg split: pgcl.split prod.split)
         (auto simp: nn_integral_max_0)
  qed (rule step_finite)
  then show ?thesis
    by (simp add: nn_integral_max_0)
qed

lemma E_inf_r_unfold:
  "step.E_inf s (r f) = (\<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else step.E_inf t (r f)) \<partial>D)"
  unfolding E_inf_r by (simp add: lfp_unfold[OF mono_r'])

lemma E_inf_r_induct[consumes 1, case_names step]:
  assumes "P s y"
  assumes *: "\<And>F s y. P s y \<Longrightarrow>
    (\<And>s y. P s y \<Longrightarrow> F s \<le> y) \<Longrightarrow> (\<And>s. F s \<le> step.E_inf s (r f)) \<Longrightarrow>
    (\<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>D) \<le> y"
  shows "step.E_inf s (r f) \<le> y"
  using `P s y`
  unfolding E_inf_r
proof (induction arbitrary: s y rule: lfp_ordinal_induct[OF mono_r'[where f=f]])
  case (1 F) with *[of s y F] show ?case  
    unfolding le_fun_def E_inf_r[where f=f, symmetric] by simp
qed (auto intro: SUP_least)

lemma E_inf_Skip: "0 \<le> f s \<Longrightarrow> step.E_inf (Skip, s) (r f) = f s"
  by (subst E_inf_r_unfold) (simp add: min_absorb1)

lemma E_inf_Seq:
  assumes [simp]: "\<And>x. 0 \<le> f x"
  shows "step.E_inf (Seq a b, s) (r f) = step.E_inf (a, s) (r (\<lambda>s. step.E_inf (b, s) (r f)))"
proof (rule antisym)
  show "step.E_inf (Seq a b, s) (r f) \<le> step.E_inf (a, s) (r (\<lambda>s. step.E_inf (b, s) (r f)))"
  proof (coinduction arbitrary: a s rule: E_inf_r_induct)
    case step then show ?case
      by (rewrite in "_ \<le> \<hole>" E_inf_r_unfold)
         (force intro!: INF_mono[OF bexI] nn_integral_mono intro: le_infI2
                simp: E_inf_Skip simp del: inf_ereal_def)
  qed
  show "step.E_inf (a, s) (r (\<lambda>s. step.E_inf (b, s) (r f))) \<le> step.E_inf (Seq a b, s) (r f)"
  proof (coinduction arbitrary: a s rule: E_inf_r_induct)
    case step then show ?case
      by (rewrite in "_ \<le> \<hole>" E_inf_r_unfold)
         (force intro!: INF_mono[OF bexI] nn_integral_mono intro: le_infI2
                simp: E_inf_Skip simp del: inf_ereal_def)
   qed
qed

lemma E_inf_While:
  assumes f[simp]: "\<And>x. 0 \<le> f x"
  shows "step.E_inf (While g c, s) (r f) =
    lfp (\<lambda>F s. if g s then step.E_inf (c, s) (r (sup (\<lambda>_. 0) F)) else f s) s"
proof (rule antisym)
  have E_inf_While_step: "\<And>s f. (\<And>x. 0 \<le> f x) \<Longrightarrow> step.E_inf (While g c, s) (r f) =
    (if g s then step.E_inf (c, s) (r (\<lambda>s. step.E_inf (While g c, s) (r f))) else f s)"
    by (rewrite E_inf_r_unfold) (simp add: min_absorb1 step.E_inf_nonneg E_inf_Seq)

  have "mono (\<lambda>F s. if g s then step.E_inf (c, s) (r (sup (\<lambda>_. 0) F)) else f s)" (is "mono ?F")
    by (auto intro!: mono_r step.E_inf_mono simp: mono_def le_fun_def max.coboundedI2)
  then show "lfp ?F s \<le> step.E_inf (While g c, s) (r f)"
  proof (induction arbitrary: s rule: lfp_ordinal_induct[consumes 1])
    case mono then show ?case
      by (rewrite E_inf_While_step)
         (auto simp: step.E_inf_nonneg intro!: step.E_inf_mono mono_r le_funI min.coboundedI2)
  qed (auto intro: SUP_least)

  def w \<equiv> "\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then if g (snd t) then (sup (\<lambda>_. 0) F) (c, snd t) else f (snd t) else F t) \<partial>D"
  have "mono w"
    by (auto simp: w_def mono_def le_fun_def intro!: INF_mono[OF bexI] nn_integral_mono max.coboundedI2) []
  have w_nonneg: "\<And>s. 0 \<le> lfp w s"
    by (rewrite lfp_unfold[OF \<open>mono w\<close>]) (auto simp: w_def intro!: INF_greatest nn_integral_nonneg)

  def d \<equiv> c 
  def t \<equiv> "Seq d (While g c)"
  then have "(t = While g c \<and> d = c \<and> g s) \<or> t = Seq d (While g c)"
    by auto
  then have "step.E_inf (t, s) (r f) \<le> lfp w (d, s)"
  proof (coinduction arbitrary: t d s rule: E_inf_r_induct)
    case (step F t d s)
    from step(1)
    show ?case
    proof (elim conjE disjE)
      assume "d = c" "t = While g c" "g s" then show ?thesis
        by (rewrite nn_integral_max_0[symmetric])
           (auto simp: min.absorb1 step.E_inf_nonneg intro!: min.coboundedI2 step w_nonneg)
    next
      { fix s have "\<not> g s \<Longrightarrow> F (While g c, s) \<le> f s"
          using step(3)[of "(While g c, s)"] by (simp add: E_inf_While_step) }
      note [simp] = this
      assume "t = Seq d (While g c)" then show ?thesis
        using w_nonneg
        by (rewrite lfp_unfold[OF \<open>mono w\<close>])
           (auto simp: max.absorb2 w_def intro!: INF_mono[OF bexI] nn_integral_mono step)
    qed
  qed
  also have "lfp w = lfp (\<lambda>F s. step.E_inf s (r (\<lambda>s. if g s then (sup (\<lambda>_. 0) F) (c, s) else f s)))"
    unfolding E_inf_r w_def
    by (rule lfp_lfp[symmetric]) (auto simp: le_fun_def intro!: INF_mono[OF bexI] nn_integral_mono max.coboundedI2)
  finally have "step.E_inf (While g c, s) (r f) \<le> (if g s then \<dots> (c, s) else f s)"
    unfolding t_def d_def by (rewrite E_inf_r_unfold) (simp add: min.absorb1 step.E_inf_nonneg)
  also have "\<dots> = lfp ?F s"
    by (rewrite lfp_rolling[symmetric, of "\<lambda>F s. if g s then F (c, s) else f s"
          "\<lambda>F s. step.E_inf s (r (sup (\<lambda>_. 0) F))"])
       (auto simp: mono_def le_fun_def sup_apply[abs_def] if_distrib[of "max 0"] max.coboundedI2 max.absorb2
                intro!: step.E_inf_mono mono_r cong del: if_cong)
  finally show "step.E_inf (While g c, s) (r f) \<le> \<dots>"
    .
qed

lemma E_inf_r_eq_wp: "(\<And>s. 0 \<le> f s) \<Longrightarrow> step.E_inf (c, s) (r f) = wp c f s"
proof (induction c arbitrary: f s)
  case Skip then show ?case
    by (simp add: E_inf_Skip)
next
  case Abort then show ?case
  proof (intro antisym)
    have "lfp (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>D) \<le>
      (\<lambda>s. if \<exists>t. s = (Abort, t) then 0 else \<top>)"
      by (intro lfp_lowerbound) (auto simp: le_fun_def)
    then show "step.E_inf (Abort, s) (r f) \<le> wp Abort f s"
      by (auto simp: E_inf_r le_fun_def split: split_if_asm)
  qed (simp add: step.E_inf_nonneg)
next
  case Assign then show ?case
    by (rewrite E_inf_r_unfold) (simp add: min_absorb1)
next
  case (If b c1 c2) then show ?case
    by (rewrite E_inf_r_unfold)
       (auto simp add: min.absorb1 step.E_inf_nonneg wp_nonneg)
next
  case (Prob p c1 c2) then show ?case
    apply (rewrite E_inf_r_unfold)
    apply (auto simp add: min.absorb2 step.E_inf_nonneg wp_nonneg min.commute)
    apply (rewrite nn_integral_measure_pmf_support[of "UNIV::bool set"])
    apply (auto simp: wp_nonneg UNIV_bool ac_simps)
    done
next
  case (Par c1 c2) then show ?case
    by (rewrite E_inf_r_unfold)
       (auto simp add: min.absorb2 step.E_inf_nonneg wp_nonneg min.commute)
next
  case (Seq c1 c2) then show ?case
    by (simp add: E_inf_Seq wp_nonneg)
next
  case (While g c) then show ?case
    apply (simp add: E_inf_While wp_nonneg)
    apply (rewrite While)
    apply auto
    done
qed

end
