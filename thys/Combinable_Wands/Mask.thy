subsection \<open>Permission masks: Maps from heap locations to permission amounts\<close>

theory Mask
  imports PosRat
begin

subsubsection \<open>Definitions\<close>

type_synonym field = string
type_synonym address = nat
type_synonym heap_loc = "address \<times> field"

type_synonym mask = "heap_loc \<Rightarrow> prat"
type_synonym bmask = "heap_loc \<Rightarrow> bool"

definition null where "null = 0"

definition full_mask :: "mask" where
  "full_mask hl = (if fst hl = null then pnone else pwrite)"


definition multiply_mask :: "prat \<Rightarrow> mask \<Rightarrow> mask" where
  "multiply_mask p \<pi> hl = pmult p (\<pi> hl)"

fun empty_mask where
  "empty_mask hl = pnone"

fun empty_bmask where
  "empty_bmask hl = False"

fun add_acc where "add_acc \<pi> hl p = \<pi>(hl := padd (\<pi> hl) p)"

inductive rm_acc where
  "\<pi> hl = padd p r \<Longrightarrow> rm_acc \<pi> hl p (\<pi>(hl := r))"

fun add_masks where
  "add_masks \<pi>' \<pi> hl = padd (\<pi>' hl) (\<pi> hl)"

definition greater_mask where
  "greater_mask \<pi>' \<pi> \<longleftrightarrow> (\<exists>r. \<pi>' = add_masks \<pi> r)"

fun uni_mask where
  "uni_mask hl p = empty_mask(hl := p)"

fun valid_mask :: "mask \<Rightarrow> bool" where
  "valid_mask \<pi> \<longleftrightarrow> (\<forall>hl. pgte pwrite (\<pi> hl)) \<and> (\<forall>f. \<pi> (null, f) = pnone)"

definition valid_null :: "mask \<Rightarrow> bool" where
  "valid_null \<pi> \<longleftrightarrow> (\<forall>f. \<pi> (null, f) = pnone)"

definition equal_on_mask where
  "equal_on_mask \<pi> h h' \<longleftrightarrow> (\<forall>hl. ppos (\<pi> hl) \<longrightarrow> h hl = h' hl)"

definition equal_on_bmask where
  "equal_on_bmask \<pi> h h' \<longleftrightarrow> (\<forall>hl. \<pi> hl \<longrightarrow> h hl = h' hl)"

definition big_add_masks where
  "big_add_masks \<Pi> \<Pi>' h = add_masks (\<Pi> h) (\<Pi>' h)"

definition big_greater_mask where
  "big_greater_mask \<Pi> \<Pi>' \<longleftrightarrow> (\<forall>h. greater_mask (\<Pi> h) (\<Pi>' h))"

definition greater_bmask where
  "greater_bmask H H' \<longleftrightarrow> (\<forall>h. H' h \<longrightarrow> H h)"

definition update_dm where
  "update_dm dm \<pi> \<pi>' hl \<longleftrightarrow> (dm hl \<or> pgt (\<pi> hl) (\<pi>' hl))"

fun pre_get_m where "pre_get_m \<phi> = fst \<phi>"
fun pre_get_h where "pre_get_h \<phi> = snd \<phi>"
fun srm_acc where "srm_acc \<phi> hl p = (rm_acc (pre_get_m \<phi>) hl p, pre_get_h \<phi>)"


datatype val = Bool (the_bool: bool) | Address (the_address: address) | Rat (the_rat: prat)

definition upper_bounded :: "mask \<Rightarrow> prat \<Rightarrow> bool" where
  "upper_bounded \<pi> p \<longleftrightarrow> (\<forall>hl. pgte p (\<pi> hl))"




subsubsection \<open>Lemmas\<close>

lemma ssubsetI:
  assumes "\<And>\<pi> h. (\<pi>, h) \<in> A \<Longrightarrow> (\<pi>, h) \<in> B"
  shows "A \<subseteq> B"
  using assms by auto

lemma double_inclusion:
  assumes "A \<subseteq> B"
      and "B \<subseteq> A"
    shows "A = B"
  using assms by blast

lemma add_masks_comm:
  "add_masks a b = add_masks b a"
proof (rule ext)
  fix x show "add_masks a b x = add_masks b a x"
    by (metis Rep_prat_inverse add.commute add_masks.simps padd.rep_eq)
qed

lemma add_masks_asso:
  "add_masks (add_masks a b) c = add_masks a (add_masks b c)"
proof (rule ext)
  fix x show "add_masks (add_masks a b) c x = add_masks a (add_masks b c) x"
    by (metis Rep_prat_inverse add.assoc add_masks.simps padd.rep_eq)
qed

lemma minus_empty:
  "\<pi> = add_masks \<pi> empty_mask"
proof (rule ext)
  fix x show "\<pi> x = add_masks \<pi> empty_mask x"
    by (metis Rep_prat_inverse add.right_neutral add_masks.simps empty_mask.simps padd.rep_eq pnone.rep_eq)
qed

lemma add_acc_uni_mask:
  "add_acc \<pi> hl p = add_masks \<pi> (uni_mask hl p)"
proof (rule ext)
  fix x show "add_acc \<pi> hl p x = add_masks \<pi> (uni_mask hl p) x"
    by (metis (no_types, opaque_lifting) add_acc.simps add_masks.simps fun_upd_apply minus_empty uni_mask.simps)
qed

lemma add_masks_equiv_valid_null:
  "valid_null (add_masks a b) \<longleftrightarrow> valid_null a \<and> valid_null b"
  by (metis (mono_tags, lifting) add_masks.simps padd_zero valid_null_def)

lemma valid_maskI:
  assumes "\<And>hl. pgte pwrite (\<pi> hl)"
      and "\<And>f. \<pi> (null, f) = pnone"
    shows "valid_mask \<pi>"
  by (simp add: assms(1) assms(2))

lemma greater_mask_equiv_def:
  "greater_mask \<pi>' \<pi> \<longleftrightarrow> (\<forall>hl. pgte (\<pi>' hl) (\<pi> hl))"
  (is "?A \<longleftrightarrow> ?B")
proof (rule iffI)
  show "?A \<Longrightarrow> ?B"
  proof (clarify)
    fix hl assume "greater_mask \<pi>' \<pi>"
    then obtain r where "\<pi>' = add_masks \<pi> r"
      using greater_mask_def by blast
    then show "pgte (\<pi>' hl) (\<pi> hl)"
      using Rep_prat padd.rep_eq pgte.rep_eq by auto
  qed
  show "?B \<Longrightarrow> ?A"
  proof -
    assume ?B
    let ?r = "\<lambda>hl. (SOME p. \<pi>' hl = padd (\<pi> hl) p)"
    have "\<pi>' = add_masks \<pi> ?r"
    proof (rule ext)
      fix hl
      have "\<pi>' hl = padd (\<pi> hl) (?r hl)"
        by (meson \<open>\<forall>hl. pgte (\<pi>' hl) (\<pi> hl)\<close> p_greater_exists someI_ex)
      then show "\<pi>' hl = add_masks \<pi> ?r hl"
        by auto
    qed
    then show ?A
      using greater_mask_def by blast
  qed
qed

lemma greater_maskI:
  assumes "\<And>hl. pgte (\<pi>' hl) (\<pi> hl)"
  shows "greater_mask \<pi>' \<pi>"
  by (simp add: assms greater_mask_equiv_def)

lemma greater_mask_properties:
  "greater_mask \<pi> \<pi>"
  "greater_mask a b \<and> greater_mask b c \<Longrightarrow> greater_mask a c"
  "greater_mask \<pi>' \<pi> \<and> greater_mask \<pi> \<pi>' \<Longrightarrow> \<pi> = \<pi>'"
  apply (simp add: greater_maskI pgte.rep_eq)
  apply (metis add_masks_asso greater_mask_def)
proof (rule ext)
  fix x assume "greater_mask \<pi>' \<pi> \<and> greater_mask \<pi> \<pi>'"
  then show "\<pi> x = \<pi>' x"
    by (meson greater_mask_equiv_def pgte_antisym)
qed

lemma greater_mask_decomp:
  assumes "greater_mask a (add_masks b c)"
  shows "\<exists>a1 a2. a = add_masks a1 a2 \<and> greater_mask a1 b \<and> greater_mask a2 c"
  by (metis add_masks_asso assms greater_mask_def greater_mask_properties(1))

lemma valid_empty:
  "valid_mask empty_mask"
  by (metis empty_mask.simps le_add_same_cancel1 p_greater_exists padd.rep_eq pgte.rep_eq pnone.rep_eq valid_mask.simps)

lemma upper_valid_aux:
  assumes "valid_mask a"
      and "a = add_masks b c"
    shows "valid_mask b"
proof (rule valid_maskI)
  show "\<And>hl. pgte pwrite (b hl)"
    using assms(1) assms(2) p_greater_exists padd_asso by fastforce
  fix f show " b (null, f) = pnone"
    by (metis add_masks_comm assms(1) assms(2) empty_mask.simps greater_mask_def greater_mask_equiv_def minus_empty pgte_antisym valid_mask.simps)
qed

lemma upper_valid:
  assumes "valid_mask a"
      and "a = add_masks b c"
    shows "valid_mask b \<and> valid_mask c"
  using add_masks_comm assms(1) assms(2) upper_valid_aux by blast

lemma equal_on_bmaskI:
  assumes "\<And>hl. \<pi> hl \<Longrightarrow> h hl = h' hl"
  shows "equal_on_bmask \<pi> h h'"
  using assms equal_on_bmask_def by blast

lemma big_add_greater:
  "big_greater_mask (big_add_masks A B) B"
  by (metis add_masks_comm big_add_masks_def big_greater_mask_def greater_mask_def)

lemma big_greater_iff:
  "big_greater_mask A B \<Longrightarrow> (\<exists>C. A = big_add_masks B C)"
proof -
  assume "big_greater_mask A B"
  let ?C = "\<lambda>h. SOME r. A h = add_masks (B h) r"
  have "A = big_add_masks B ?C"
  proof (rule ext)
    fix x
    have "A x = add_masks (B x) (?C x)"
    proof (rule ext)
      fix xa 
      have "A x = add_masks (B x) (SOME r. A x = add_masks (B x) r)"
        by (metis (mono_tags, lifting) \<open>big_greater_mask A B\<close> big_greater_mask_def greater_mask_def someI_ex)
      then show "A x xa = add_masks (B x) (SOME r. A x = add_masks (B x) r) xa"
        by auto
    qed
    then show "A x = big_add_masks B (\<lambda>h. SOME r. A h = add_masks (B h) r) x"
      by (metis (no_types, lifting) big_add_masks_def)
  qed
  then show "\<exists>C. A = big_add_masks B C"
    by fast
qed

lemma big_add_masks_asso:
  "big_add_masks A (big_add_masks B C) = big_add_masks (big_add_masks A B) C"
proof (rule ext)
  fix x show "big_add_masks A (big_add_masks B C) x = big_add_masks (big_add_masks A B) C x"
    by (simp add: add_masks_asso big_add_masks_def)
qed

lemma big_add_mask_neutral:
  "big_add_masks \<Pi> (\<lambda>_. empty_mask) = \<Pi>"
proof (rule ext)
  fix x show "big_add_masks \<Pi> (\<lambda>_. empty_mask) x = \<Pi> x"
    by (metis big_add_masks_def minus_empty)
qed

lemma sym_equal_on_mask:
  "equal_on_mask \<pi> a b \<longleftrightarrow> equal_on_mask \<pi> b a"
proof -
  have "\<And>a b. equal_on_mask \<pi> a b \<Longrightarrow> equal_on_mask \<pi> b a"
    by (simp add: equal_on_mask_def)
  then show ?thesis by blast
qed

lemma greater_mask_uni_equiv:
  "greater_mask \<pi> (uni_mask hl r) \<longleftrightarrow> pgte (\<pi> hl) r"
  by (metis add_masks_comm fun_upd_apply greater_mask_def greater_mask_equiv_def minus_empty uni_mask.simps)

lemma greater_mask_uniI:
  assumes "pgte (\<pi> hl) r"
  shows "greater_mask \<pi> (uni_mask hl r)"
  using greater_mask_uni_equiv assms by metis

lemma greater_bmask_refl:
  "greater_bmask H H"
  by (simp add: greater_bmask_def)

lemma greater_bmask_trans:
  assumes "greater_bmask A B"
      and "greater_bmask B C"
    shows "greater_bmask A C"
  by (metis assms(1) assms(2) greater_bmask_def)

lemma update_dm_same:
  "update_dm dm \<pi> \<pi> = dm"
proof (rule ext)
  fix x show "update_dm dm \<pi> \<pi> x = dm x"
    by (simp add: pgt.rep_eq update_dm_def)
qed

lemma update_trans:
  assumes "greater_mask \<pi> \<pi>'"
      and "greater_mask \<pi>' \<pi>''"
  shows "update_dm (update_dm dm \<pi> \<pi>') \<pi>' \<pi>'' = update_dm dm \<pi> \<pi>''"
proof (rule ext)
  fix hl show "update_dm (update_dm dm \<pi> \<pi>') \<pi>' \<pi>'' hl = update_dm dm \<pi> \<pi>'' hl"
  proof -
    have "update_dm (update_dm dm \<pi> \<pi>') \<pi>' \<pi>'' hl \<longleftrightarrow> (update_dm dm \<pi> \<pi>') hl \<or> pgt (\<pi>' hl) (\<pi>'' hl)"
      using update_dm_def by metis
    also have "... \<longleftrightarrow> dm hl \<or> pgt (\<pi> hl) (\<pi>' hl) \<or> pgt (\<pi>' hl) (\<pi>'' hl)"
      using update_dm_def by metis
    moreover have "update_dm dm \<pi> \<pi>'' hl \<longleftrightarrow> dm hl \<or> pgt (\<pi> hl) (\<pi>'' hl)"
      using update_dm_def by metis
    moreover have "pgt (\<pi> hl) (\<pi>' hl) \<or> pgt (\<pi>' hl) (\<pi>'' hl) \<longleftrightarrow> pgt (\<pi> hl) (\<pi>'' hl)"
    proof
      show "pgt (\<pi> hl) (\<pi>' hl) \<or> pgt (\<pi>' hl) (\<pi>'' hl) \<Longrightarrow> pgt (\<pi> hl) (\<pi>'' hl)"
        by (metis assms(1) assms(2) greater_mask_equiv_def greater_mask_properties(2) not_pgte_charact pgte_antisym)
      show "pgt (\<pi> hl) (\<pi>'' hl) \<Longrightarrow> pgt (\<pi> hl) (\<pi>' hl) \<or> pgt (\<pi>' hl) (\<pi>'' hl)"
        by (metis assms(1) greater_mask_equiv_def not_pgte_charact pgte_antisym)
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma equal_on_bmask_greater:
  assumes "equal_on_bmask \<pi>' h h'"
      and "greater_bmask \<pi>' \<pi>"
    shows "equal_on_bmask \<pi> h h'"
  by (metis (mono_tags, lifting) assms(1) assms(2) equal_on_bmask_def greater_bmask_def)

lemma update_dm_equal_bmask:
  assumes "\<pi> = add_masks \<pi>' m"   
  shows "equal_on_bmask (update_dm dm \<pi> \<pi>') h' h \<longleftrightarrow> equal_on_mask m h h' \<and> equal_on_bmask dm h h'"
proof -
  have "equal_on_bmask (update_dm dm \<pi> \<pi>') h' h \<longleftrightarrow> (\<forall>hl. update_dm dm \<pi> \<pi>' hl \<longrightarrow> h' hl = h hl)"
    by (simp add: equal_on_bmask_def)
  moreover have "\<And>hl. update_dm dm \<pi> \<pi>' hl \<longleftrightarrow> dm hl \<or> pgt (\<pi> hl) (\<pi>' hl)"
    by (simp add: update_dm_def)
  moreover have "(\<forall>hl. update_dm dm \<pi> \<pi>' hl \<longrightarrow> h' hl = h hl) \<longleftrightarrow> equal_on_mask m h h' \<and> equal_on_bmask dm h h'"
  proof
    show "\<forall>hl. update_dm dm \<pi> \<pi>' hl \<longrightarrow> h' hl = h hl \<Longrightarrow> equal_on_mask m h h' \<and> equal_on_bmask dm h h'"
      by (simp add: assms equal_on_bmask_def equal_on_mask_def padd.rep_eq pgt.rep_eq ppos.rep_eq update_dm_def)
    assume "equal_on_mask m h h' \<and> equal_on_bmask dm h h'"
    then have "\<And>hl. update_dm dm \<pi> \<pi>' hl \<Longrightarrow> h' hl = h hl"
      by (metis (full_types) add.right_neutral add_masks.simps assms dual_order.strict_iff_order equal_on_bmask_def equal_on_mask_def padd.rep_eq pgt.rep_eq pnone.rep_eq ppos_eq_pnone update_dm_def)
    then show "\<forall>hl. update_dm dm \<pi> \<pi>' hl \<longrightarrow> h' hl = h hl"
      by simp
  qed
  then show ?thesis
    by (simp add: calculation)
qed

lemma const_sum_mask_greater:
  assumes "add_masks a b = add_masks c d"
      and "greater_mask a c"
    shows "greater_mask d b"
proof (rule ccontr)
  assume "\<not> greater_mask d b"
  then obtain hl where "\<not> pgte (d hl) (b hl)"
    using greater_mask_equiv_def by blast
  then have "pgt (b hl) (d hl)"
    using not_pgte_charact by auto
  then have "pgt (padd (a hl) (b hl)) (padd (c hl) (d hl))"
    by (metis assms(2) greater_mask_equiv_def padd_comm pgte_pgt)
  then show "False"
    by (metis add_masks.simps assms(1) not_pgte_charact order_refl pgte.rep_eq)
qed

lemma add_masks_cancellative:
  assumes "add_masks b c = add_masks b d"
    shows "c = d"
proof (rule ext)
  fix x show "c x = d x"
    by (metis assms(1) const_sum_mask_greater greater_mask_properties(1) greater_mask_properties(3))
qed

lemma equal_on_maskI:
  assumes "\<And>hl. ppos (\<pi> hl) \<Longrightarrow> h hl = h' hl"
  shows "equal_on_mask \<pi> h h'"
  by (simp add: assms equal_on_mask_def)

lemma greater_equal_on_mask:
  assumes "equal_on_mask \<pi>' h h'"
      and "greater_mask \<pi>' \<pi>"
    shows "equal_on_mask \<pi> h h'"
proof (rule equal_on_maskI)
  fix hl assume asm: "ppos (\<pi> hl)"
  then show "h hl = h' hl"
    by (metis assms(1) assms(2) equal_on_mask_def greater_mask_equiv_def less_le_trans pgte.rep_eq ppos.rep_eq)
qed

lemma equal_on_mask_sum:
  "equal_on_mask \<pi>1 h h' \<and> equal_on_mask \<pi>2 h h' \<longleftrightarrow> equal_on_mask (add_masks \<pi>1 \<pi>2) h h'"
proof
  show "equal_on_mask (add_masks \<pi>1 \<pi>2) h h' \<Longrightarrow> equal_on_mask \<pi>1 h h' \<and> equal_on_mask \<pi>2 h h'"
    using add_masks_comm greater_equal_on_mask greater_mask_def by blast
  assume asm0: "equal_on_mask \<pi>1 h h' \<and> equal_on_mask \<pi>2 h h'"
  show "equal_on_mask (add_masks \<pi>1 \<pi>2) h h'"
  proof (rule equal_on_maskI)
    fix hl assume "ppos (add_masks \<pi>1 \<pi>2 hl)"
    then show "h hl = h' hl"
    proof (cases "ppos (\<pi>1 hl)")
      case True
      then show ?thesis
        by (meson asm0 equal_on_mask_def)
    next
      case False
      then show ?thesis
        by (metis asm0 \<open>ppos (add_masks \<pi>1 \<pi>2 hl)\<close> add_masks.simps equal_on_mask_def padd_zero ppos_eq_pnone)
    qed
  qed
qed

lemma valid_larger_mask:
  "valid_mask \<pi> \<longleftrightarrow> greater_mask full_mask \<pi> "
  by (metis fst_eqD full_mask_def greater_maskI greater_mask_def not_one_le_zero not_pgte_charact pgt_implies_pgte pgte.rep_eq pnone.rep_eq pwrite.rep_eq surjective_pairing upper_valid_aux valid_mask.elims(1))

lemma valid_mask_full_mask:
  "valid_mask full_mask"
  using greater_mask_properties(1) valid_larger_mask by blast

lemma mult_greater:
  assumes "greater_mask a b"
  shows "greater_mask (multiply_mask p a) (multiply_mask p b)"
  by (metis (full_types) assms greater_mask_equiv_def multiply_mask_def p_greater_exists pmult_distr)

lemma mult_write_mask:
  "multiply_mask pwrite \<pi> = \<pi>"
proof (rule ext)
  fix x show "multiply_mask pwrite \<pi> x = \<pi> x"
    by (simp add: multiply_mask_def pmult_special(1))
qed

lemma mult_distr_masks:
  "multiply_mask a (add_masks b c) = add_masks (multiply_mask a b) (multiply_mask a c)"
proof (rule ext)
  fix x show "multiply_mask a (add_masks b c) x = add_masks (multiply_mask a b) (multiply_mask a c) x"
    by (simp add: multiply_mask_def pmult_distr)
qed

lemma mult_add_states:
  "multiply_mask (padd a b) \<pi> = add_masks (multiply_mask a \<pi>) (multiply_mask b \<pi>)"
proof (rule ext)
  fix x show "multiply_mask (padd a b) \<pi> x = add_masks (multiply_mask a \<pi>) (multiply_mask b \<pi>) x"    
    by (simp add: multiply_mask_def pmult_comm pmult_distr)
qed

lemma upper_boundedI:
  assumes "\<And>hl. pgte p (\<pi> hl)"
  shows "upper_bounded \<pi> p"
  by (simp add: assms upper_bounded_def)

lemma upper_bounded_smaller:
  assumes "upper_bounded \<pi> a"
  shows "upper_bounded (multiply_mask p \<pi>) (pmult p a)"  
  by (metis assms multiply_mask_def p_greater_exists pmult_distr upper_bounded_def)

lemma upper_bounded_bigger:
  assumes "upper_bounded \<pi> a"
      and "pgte b a"
    shows "upper_bounded \<pi> b"
  by (meson assms(1) assms(2) order_trans pgte.rep_eq upper_bounded_def)


lemma valid_mult:
  assumes "valid_mask \<pi>"
      and "pgte pwrite p"
    shows "valid_mask (multiply_mask p \<pi>)"
proof (rule valid_maskI)
  have "upper_bounded \<pi> pwrite"
    using assms(1) upper_bounded_def by auto
  then have "upper_bounded (multiply_mask p \<pi>) (pmult p pwrite)"
    by (simp add: upper_bounded_smaller)
  then show "\<And>hl. pgte pwrite (multiply_mask p \<pi> hl)"
    by (metis assms(2) pmult_comm pmult_special(1) upper_bounded_bigger upper_bounded_def)
  show "\<And>f. multiply_mask p \<pi> (null, f) = pnone"
    by (metis Rep_prat_inverse add_0_left assms(1) multiply_mask_def padd.rep_eq padd_cancellative pmult_distr pnone.rep_eq valid_mask.elims(1))
qed

lemma valid_sum:
  assumes "valid_mask a"
      and "valid_mask b"
      and "upper_bounded a ma"
      and "upper_bounded b mb"
      and "pgte pwrite (padd ma mb)"
    shows "valid_mask (add_masks a b)"
      and "upper_bounded (add_masks a b) (padd ma mb)"
proof (rule valid_maskI)
  show "\<And>hl. pgte pwrite (add_masks a b hl)"
  proof -
    fix hl 
    have "pgte (padd ma mb) (add_masks a b hl)"
      by (metis (mono_tags, lifting) add_masks.simps add_mono_thms_linordered_semiring(1) assms(3) assms(4) padd.rep_eq pgte.rep_eq upper_bounded_def)
    then show "pgte pwrite (add_masks a b hl)"
      by (meson assms(5) dual_order.trans pgte.rep_eq)
  qed
  show "\<And>f. add_masks a b (null, f) = pnone"
    by (metis Rep_prat_inverse add_0_left add_masks.simps assms(1) assms(2) padd.rep_eq pnone.rep_eq valid_mask.simps)
  show "upper_bounded (add_masks a b) (padd ma mb)"
    using add_mono_thms_linordered_semiring(1) assms(3) assms(4) padd.rep_eq pgte.rep_eq upper_bounded_def by fastforce
qed

lemma valid_multiply:
  assumes "valid_mask a"
      and "upper_bounded a ma"
      and "pgte pwrite (pmult ma p)"
    shows "valid_mask (multiply_mask p a)"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) multiply_mask_def pmult_comm pmult_special(2) upper_bounded_bigger upper_bounded_def upper_bounded_smaller valid_mask.elims(1))

lemma greater_mult:
  assumes "greater_mask a b"
  shows "greater_mask (multiply_mask p a) (multiply_mask p b)"
  by (metis Rep_prat assms greater_mask_equiv_def mem_Collect_eq mult_left_mono multiply_mask_def pgte.rep_eq pmult.rep_eq)

end