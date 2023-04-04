subsection \<open>Permission Heaps\<close>

theory FractionalHeap
  imports Main PosRat PartialMap
begin

type_synonym ('l, 'v) fract_heap = "'l \<rightharpoonup> prat \<times> 'v"

definition compatible_fractions :: "('l, 'v) fract_heap \<Rightarrow> ('l, 'v) fract_heap \<Rightarrow> bool" where
  "compatible_fractions h h' \<longleftrightarrow>
  (\<forall>l p p'. h l = Some p \<and> h' l = Some p' \<longrightarrow> pgte pwrite (padd (fst p) (fst p')))"

definition same_values :: "('l, 'v) fract_heap \<Rightarrow> ('l, 'v) fract_heap \<Rightarrow> bool" where
  "same_values h h' \<longleftrightarrow> (\<forall>l p p'. h l = Some p \<and> h' l = Some p' \<longrightarrow> snd p = snd p')"

fun fadd_options :: "(prat \<times> 'v) option \<Rightarrow> (prat \<times> 'v) option \<Rightarrow> (prat \<times> 'v) option"
  where
  "fadd_options None x = x"
| "fadd_options x None = x"
| "fadd_options (Some x) (Some y) = Some (padd (fst x) (fst y), snd x)"


lemma fadd_options_cancellative:
  assumes "fadd_options a x = fadd_options b x"
  shows "a = b"
proof (cases x)
  case None
  then show ?thesis
    by (metis assms fadd_options.elims option.simps(3))
next
  case (Some xx)
  then have "x = Some xx" by simp
  then show ?thesis
    apply (cases a)
     apply (cases b)
      apply simp
    apply (metis assms fadd_options.simps(1) fadd_options.simps(3) fst_conv not_pgte_charact option.sel padd_comm pgt_implies_pgte sum_larger)
     apply (cases b)
     apply (metis assms fadd_options.simps(1) fadd_options.simps(3) fst_conv not_pgte_charact option.sel padd_comm pgt_implies_pgte sum_larger)

  proof -
    fix aa bb assume "a = Some aa" "b = Some bb"
    then have "snd aa = snd bb"
      using Some assms by auto
    moreover have "fst aa = fst bb"
      using padd_cancellative[of "padd (fst aa) (fst xx)" "fst bb" "fst xx" "fst aa"]
        Some \<open>a = Some aa\<close> \<open>b = Some bb\<close> assms fadd_options.simps(3) fst_conv option.inject
      by auto
    ultimately show "a = b"
      by (simp add: \<open>a = Some aa\<close> \<open>b = Some bb\<close> prod_eq_iff)
  qed
qed


definition compatible_fract_heaps :: "('l, 'v) fract_heap \<Rightarrow> ('l, 'v) fract_heap \<Rightarrow> bool" where
  "compatible_fract_heaps h h' \<longleftrightarrow> compatible_fractions h h' \<and> same_values h h'"

lemma compatible_fract_heapsI:
  assumes "\<And>l p p'. h l = Some p \<and> h' l = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
      and "\<And>l p p'. h l = Some p \<and> h' l = Some p' \<Longrightarrow> snd p = snd p'"
    shows "compatible_fract_heaps h h'"
  by (simp add: assms(1) assms(2) compatible_fract_heaps_def compatible_fractions_def same_values_def)

lemma compatible_fract_heapsE:
  assumes "compatible_fract_heaps h h'"
      and "h l = Some p \<and> h' l = Some p'"
    shows "pgte pwrite (padd (fst p) (fst p'))"
      and "snd p = snd p'"
   apply (meson assms(1) assms(2) compatible_fract_heaps_def compatible_fractions_def)
  by (meson assms(1) assms(2) compatible_fract_heaps_def same_values_def)

lemma compatible_fract_heaps_comm:
  assumes "compatible_fract_heaps h h'"
  shows "compatible_fract_heaps h' h"
proof (rule compatible_fract_heapsI)
  show "\<And>l p p'. h' l = Some p \<and> h l = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
    by (metis assms compatible_fract_heapsE(1) padd_comm)
  show "\<And>l p p'. h' l = Some p \<and> h l = Some p' \<Longrightarrow> snd p = snd p'"
    using assms compatible_fract_heapsE(2) by fastforce
qed


text \<open>The following definition only makes sense if h and h' are compatible\<close>

definition add_fh :: "('l, 'v) fract_heap \<Rightarrow> ('l, 'v) fract_heap \<Rightarrow> ('l, 'v) fract_heap" where
  "add_fh h h' l = fadd_options (h l) (h' l)"

definition full_ownership :: "('l, 'v) fract_heap \<Rightarrow> bool" where
  "full_ownership h \<longleftrightarrow> (\<forall>l p. h l = Some p \<longrightarrow> fst p = pwrite)"

lemma full_ownershipI:
  assumes "\<And>l p. h l = Some p \<Longrightarrow> fst p = pwrite"
  shows "full_ownership h"
  by (simp add: assms full_ownership_def)

fun apply_opt where
  "apply_opt f None = None"
| "apply_opt f (Some x) = Some (f x)"

definition normalize :: "('l, 'v) fract_heap \<Rightarrow> ('l \<rightharpoonup> 'v)" where
  "normalize h l = apply_opt snd (h l)"

lemma normalize_eq:
  "normalize h l = None \<longleftrightarrow> h l = None"
  "normalize h l = Some v \<longleftrightarrow> (\<exists>p. h l = Some (p, v))" (is "?A \<longleftrightarrow> ?B")
   apply (metis FractionalHeap.normalize_def apply_opt.elims option.distinct(1))
proof
  show "?B \<Longrightarrow> ?A"
    by (metis FractionalHeap.normalize_def apply_opt.simps(2) snd_eqD)
  assume ?A then have "h l \<noteq> None"
    by (metis FractionalHeap.normalize_def apply_opt.simps(1) option.distinct(1))
  then obtain p where "h l = Some p"
    by blast
  then show ?B
    by (metis FractionalHeap.normalize_def \<open>FractionalHeap.normalize h l = Some v\<close> \<open>h l \<noteq> None\<close> apply_opt.elims option.inject prod.exhaust_sel)
qed


definition fpdom where
  "fpdom h = {x. \<exists>v. h x = Some (pwrite, v)}"

lemma compatible_then_dom_disjoint:
  assumes "compatible_fract_heaps h1 h2"
  shows "dom h1 \<inter> fpdom h2 = {}"
    and "dom h2 \<inter> fpdom h1 = {}"
proof -
  have r: "\<And>h1 h2. compatible_fract_heaps h1 h2 \<Longrightarrow> dom h1 \<inter> fpdom h2 = {}"
  proof -
    fix h1 h2 assume asm0: "compatible_fract_heaps h1 h2"
    show "dom h1 \<inter> fpdom h2 = {}"
    proof
      show "dom h1 \<inter> fpdom h2 \<subseteq> {}"
      proof
        fix x assume "x \<in> dom h1 \<inter> fpdom h2"
        then have "x \<in> dom h1 \<and> x \<in> fpdom h2" by auto
        then have "h1 x \<noteq> None \<and> h2 x \<noteq> None"
          using domIff fpdom_def[of h2] mem_Collect_eq option.discI
          by auto
        then obtain a b where "h1 x = Some a" "h2 x = Some b" by auto
        then have "fst b = pwrite \<and> pgte pwrite (padd (fst a) (fst b))"
          using \<open>x \<in> dom h1 \<and> x \<in> fpdom h2\<close> asm0 compatible_fract_heapsE(1) fpdom_def[of h2] fst_conv mem_Collect_eq option.sel
          by fastforce
        then show "x \<in> {}"
          by (metis not_pgte_charact padd_comm sum_larger)
      qed
    qed (simp)
  qed
  then show "dom h1 \<inter> fpdom h2 = {}"
    using assms by blast
  show "dom h2 \<inter> fpdom h1 = {}"
    by (simp add: assms compatible_fract_heaps_comm r)
qed

lemma compatible_dom_sum:
  assumes "compatible_fract_heaps h1 h2"
  shows "dom (add_fh h1 h2) = dom h1 \<union> dom h2" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    show "x \<in> ?A"
    proof (cases "x \<in> dom h1")
      case True
      then show ?thesis using add_fh_def[of h1 h2] domI domIff fadd_options.elims
        by metis
    next
      case False
      then have "x \<in> dom h2"
        using \<open>x \<in> dom h1 \<union> dom h2\<close> by auto
      then show ?thesis using add_fh_def[of h1 h2] domI domIff fadd_options.elims
        by metis
    qed
  qed
  show "?A \<subseteq> ?B"
    using UnI1[of _ "dom h1" "dom h2"] UnI2[of _ "dom h1" "dom h2"] add_fh_def[of h1 h2] domIff fadd_options.simps(1) subset_iff[of ?A ?B]
    dom_map_add map_add_None
    by metis
qed

lemma add_fh_asso:
  "add_fh (add_fh a b) c = add_fh a (add_fh b c)"
proof (rule ext)
  fix x
  show "add_fh (add_fh a b) c x = add_fh a (add_fh b c) x"
  proof (cases "a x")
    case None
    then show ?thesis
      by (simp add: add_fh_def)
  next
    case (Some aa)
    then have "a x = Some aa" by simp
    then show ?thesis
    proof (cases "b x")
      case None
      then show ?thesis
        by (simp add: Some add_fh_def)
    next
      case (Some bb)
      then have "b x = Some bb" by simp
      then show ?thesis
      proof (cases "c x")
        case None
        then show ?thesis
          by (simp add: Some \<open>a x = Some aa\<close> add_fh_def)
      next
        case (Some cc)
        then have "add_fh (add_fh a b) c x = Some (padd (padd (fst aa) (fst bb)) (fst cc), snd aa)"
          by (simp add: \<open>a x = Some aa\<close> \<open>b x = Some bb\<close> add_fh_def)
        moreover have "add_fh a (add_fh b c) x = Some (padd (fst aa) (padd (fst bb) (fst cc)), snd aa)"
          by (simp add: Some \<open>a x = Some aa\<close> \<open>b x = Some bb\<close> add_fh_def)
        ultimately show ?thesis
          by (simp add: padd_asso)
      qed
    qed
  qed
qed

lemma add_fh_update:
  assumes "b x = None"
  shows "add_fh (a(x \<mapsto> p)) b = (add_fh a b)(x \<mapsto> p)"
proof (rule ext)
  fix l show "add_fh (a(x \<mapsto> p)) b l = ((add_fh a b)(x \<mapsto> p)) l"
    apply (cases "l = x")
    apply (simp add: add_fh_def assms)
    by (simp add: add_fh_def)
qed

end