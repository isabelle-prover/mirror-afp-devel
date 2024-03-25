section \<open>Combinable Magic Wands\<close>

text \<open>Note that, in this theory, assertions are represented as semantic assertions, i.e., as the set of states in which they hold.\<close>

theory CombinableWands
  imports PartialHeapSA
begin             

subsection \<open>Definitions\<close>

type_synonym sem_assertion = "state set"

fun multiply :: "prat \<Rightarrow> state \<Rightarrow> state" where
  "multiply p \<phi> = Abs_state (multiply_mask p (get_m \<phi>), get_h \<phi>)"

text \<open>Because we work in an intuitionistic setting, a fraction of an assertion is defined using the upper-closure operator.\<close>

fun multiply_sem_assertion :: "prat \<Rightarrow> sem_assertion \<Rightarrow> sem_assertion" where
  "multiply_sem_assertion p P = PartialSA.upper_closure (multiply p ` P)"

definition combinable :: "sem_assertion \<Rightarrow> bool" where
  "combinable P \<longleftrightarrow> (\<forall>\<alpha> \<beta>. ppos \<alpha> \<and> ppos \<beta> \<and> pgte pwrite (padd \<alpha> \<beta>) \<longrightarrow> (multiply_sem_assertion \<alpha> P) \<otimes> (multiply_sem_assertion \<beta> P) \<subseteq> multiply_sem_assertion (padd \<alpha> \<beta>) P)"

definition scaled where
  "scaled \<phi> = { multiply p \<phi> |p. ppos p \<and> pgte pwrite p }"

definition comp_min_mask :: "mask \<Rightarrow> (mask \<Rightarrow> mask)" where
  "comp_min_mask b a hl = pmin (a hl) (comp_one (b hl))"

definition scalable where
  "scalable w a \<longleftrightarrow> (\<forall>\<phi> \<in> scaled w. \<not> a |#| \<phi>)"

definition R where
  "R a w = (if scalable w a then w else Abs_state (comp_min_mask (get_m a) (get_m w), get_h w))"

definition cwand where
  "cwand A B = { w |w. \<forall>a x. a \<in> A \<and> Some x = R a w \<oplus> a \<longrightarrow> x \<in> B }"

definition wand :: "sem_assertion \<Rightarrow> sem_assertion \<Rightarrow> sem_assertion" where
  "wand A B = { w |w. \<forall>a x. a \<in> A \<and> Some x = w \<oplus> a \<longrightarrow> x \<in> B }"

definition intuitionistic where
  "intuitionistic A \<longleftrightarrow> (\<forall>a b. a \<succeq> b \<and> b \<in> A \<longrightarrow> a \<in> A)"

definition binary_mask :: "mask \<Rightarrow> mask" where
  "binary_mask \<pi> l = (if \<pi> l = pwrite then pwrite else pnone)"

definition binary :: "sem_assertion \<Rightarrow> bool" where
  "binary A \<longleftrightarrow> (\<forall>\<phi> \<in> A. Abs_state (binary_mask (get_m \<phi>), get_h \<phi>) \<in> A)"




subsection Lemmas


lemma wand_equiv_def:
  "wand A B = { \<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B }"
proof
  show "wand A B \<subseteq> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}"
  proof
    fix w assume "w \<in> wand A B"
    have "A \<otimes> {w} \<subseteq> B"
    proof
      fix x assume "x \<in> A \<otimes> {w}"
      then show "x \<in> B"
        using PartialSA.add_set_elem \<open>w \<in> wand A B\<close> commutative wand_def by auto
    qed
    then show "w \<in> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}"
      by simp
  qed
  show "{\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B} \<subseteq> wand A B"
  proof
    fix w assume "w \<in> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}"
    have "\<And>a x. a \<in> A \<and> Some x = w \<oplus> a \<Longrightarrow> x \<in> B"
    proof -
      fix a x assume "a \<in> A \<and> Some x = w \<oplus> a"
      then have "x \<in> A \<otimes> {w}"
        using PartialSA.add_set_elem PartialSA.commutative by auto
      then show "x \<in> B"
        using \<open>w \<in> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}\<close> by blast
    qed
    then show "w \<in> wand A B"
      using wand_def by force
  qed
qed

lemma w_in_scaled:
  "w \<in> scaled w"
proof -
  have "multiply pwrite w = w"
    by (simp add: Rep_state_inverse mult_write_mask)
  then show ?thesis
    by (metis (mono_tags, lifting) half_between_0_1 half_plus_half mem_Collect_eq not_pgte_charact pgt_implies_pgte ppos_add scaled_def)
qed

lemma non_scalable_instantiate:
  assumes "\<not> scalable w a"
  shows "\<exists>p. ppos p \<and> pgte pwrite p \<and> a |#| multiply p w"
  using assms scalable_def scaled_def by auto

lemma compatible_same_mask:
  assumes "valid_mask (add_masks a w)"
  shows "w = comp_min_mask a w"
proof (rule ext)
  fix x
  have "pgte pwrite (padd (a x) (w x))"
    by (metis add_masks.simps assms valid_mask.elims(1))
  moreover have "padd (a x) (comp_one (a x)) = pwrite"
    by (meson assms padd_comp_one upper_valid_aux valid_mask.elims(1))
  then have "pgte (comp_one (a x)) (w x)"
    by (metis add_le_cancel_left calculation padd.rep_eq pgte.rep_eq)
  then show "w x = comp_min_mask a w x"
    by (metis comp_min_mask_def pmin_comm pmin_is)
qed

lemma R_smaller:
  "w \<succeq> R a w"
proof (cases "scalable w a")
  case True
  then show ?thesis
    by (simp add: PartialSA.succ_refl R_def)
next
  case False
  then have "R a w = Abs_state (comp_min_mask (get_m a) (get_m w), get_h w)"
    by (meson R_def)
  moreover have "greater_mask (get_m w) (comp_min_mask (get_m a) (get_m w))"
  proof (rule greater_maskI)
    fix hl show "pgte (get_m w hl) (comp_min_mask (get_m a) (get_m w) hl)"
      by (simp add: comp_min_mask_def pmin_greater)
  qed
  ultimately show ?thesis
    by (metis Abs_state_cases larger_heap_refl Rep_state_cases Rep_state_inverse fst_conv get_h_m greaterI greater_mask_def mem_Collect_eq snd_conv valid_state_decompose)
qed

lemma R_compatible_same:
  assumes "a |#| w"
  shows "R a w = w"
proof -
  have "\<not> scalable w a"
    using assms scalable_def w_in_scaled by blast
  then have "R a w = Abs_state (comp_min_mask (get_m a) (get_m w), get_h w)"
    using R_def by auto
  then show ?thesis
    by (metis PartialSA.defined_def Rep_state_inverse assms compatible_same_mask get_h.simps get_m.simps plus_ab_defined prod.collapse)
qed

lemma in_cwand:
  assumes "\<And>a x. a \<in> A \<and> Some x = R a w \<oplus> a \<Longrightarrow> x \<in> B"
  shows "w \<in> cwand A B"
  using assms cwand_def by force

lemma wandI:
  assumes "\<And>a x. a \<in> A \<and> Some x = a \<oplus> w \<Longrightarrow> x \<in> B"
  shows "w \<in> wand A B"
proof -
  have "A \<otimes> {w} \<subseteq> B"
  proof (rule subsetI)
    fix x assume "x \<in> A \<otimes> {w}"
    then obtain a where "Some x = a \<oplus> w" "a \<in> A"
      using PartialSA.add_set_elem by auto
    then show "x \<in> B"
      using assms by blast
  qed
  then show ?thesis
    using wand_equiv_def by force
qed

lemma non_scalable_R_charact:
  assumes "\<not> scalable w a"
  shows "get_m (R a w) = comp_min_mask (get_m a) (get_m w) \<and> get_h (R a w) = get_h w"
proof -
  have "R a w = Abs_state (comp_min_mask (get_m a) (get_m w), get_h w)"
    using R_def assms by auto
  moreover have "valid_state (comp_min_mask (get_m a) (get_m w), get_h w)"
  proof (rule valid_stateI)
    show "valid_mask (comp_min_mask (get_m a) (get_m w))"
    proof (rule valid_maskI)
      show "\<And>f. comp_min_mask (get_m a) (get_m w) (null, f) = pnone"
        by (metis (no_types, opaque_lifting) PartialSA.unit_neutral add_masks.simps comp_min_mask_def option.distinct(1) p_greater_exists padd_zero plus_ab_defined pmin_greater valid_mask.simps)
      fix hl show "pgte pwrite (comp_min_mask (get_m a) (get_m w) hl)"
        by (metis PartialSA.unit_neutral comp_min_mask_def greater_mask_def greater_mask_equiv_def option.distinct(1) plus_ab_defined pmin_greater upper_valid_aux valid_mask.simps)
    qed
    fix hl assume "ppos (comp_min_mask (get_m a) (get_m w) hl)"
    show "get_h w hl \<noteq> None"
      by (metis Rep_state \<open>ppos (comp_min_mask (get_m a) (get_m w) hl)\<close> comp_min_mask_def get_h.simps get_pre(2) mem_Collect_eq p_greater_exists pmin_greater ppos_add prod.collapse valid_heap_def valid_state.simps)
  qed
  ultimately show ?thesis
    by (metis Rep_state_cases Rep_state_inverse fst_conv get_h.simps get_m.simps mem_Collect_eq snd_conv)
qed

lemma valid_bin:
  "valid_state (binary_mask (get_m a), get_h a)"
proof (rule valid_stateI)
  show "valid_mask (binary_mask (get_m a))"
    by (metis PartialSA.unit_neutral binary_mask_def minus_empty option.discI plus_ab_defined unit_charact(2) valid_mask.elims(2) valid_mask.elims(3))
  show "\<And>hl. ppos (binary_mask (get_m a) hl) \<Longrightarrow> get_h a hl \<noteq> None"
    by (metis Rep_prat Rep_state binary_mask_def get_h.simps get_pre(2) leD mem_Collect_eq pnone.rep_eq ppos.rep_eq prod.collapse valid_heap_def valid_state.simps)
qed

lemma in_multiply_sem:
  assumes "x \<in> multiply_sem_assertion p A"
  shows "\<exists>a \<in> A. x \<succeq> multiply p a"
  using PartialSA.sep_algebra_axioms assms greater_def sep_algebra.upper_closure_def by fastforce

lemma get_h_multiply:
  assumes "pgte pwrite p"
  shows "get_h (multiply p x) = get_h x"
  using Abs_state_inverse assms multiply_valid by auto

lemma in_multiply_refl:
  assumes "x \<in> A"
  shows "multiply p x \<in> multiply_sem_assertion p A"
  using PartialSA.succ_refl PartialSA.upper_closure_def assms by fastforce

lemma get_m_smaller:
  assumes "pgte pwrite p"
  shows "get_m (multiply p a) hl = pmult p (get_m a hl)"
  using Abs_state_inverse assms multiply_mask_def multiply_valid by auto

lemma get_m_smaller_mask:
  assumes "pgte pwrite p"
  shows "get_m (multiply p a) = multiply_mask p (get_m a)"
  using Abs_state_inverse assms multiply_mask_def multiply_valid by auto

lemma multiply_order:
  assumes "pgte pwrite p"
      and "a \<succeq> b"
    shows "multiply p a \<succeq> multiply p b"
proof (rule greaterI)
  show "larger_heap (get_h (multiply p a)) (get_h (multiply p b))"
    using assms(1) assms(2) get_h_multiply larger_implies_larger_heap by presburger
  show "greater_mask (get_m (multiply p a)) (get_m (multiply p b))"
    by (metis assms(1) assms(2) get_m_smaller_mask greater_maskI larger_implies_greater_mask_hl mult_greater)
qed

lemma multiply_twice:
  assumes "pgte pwrite a \<and> pgte pwrite b"
  shows "multiply a (multiply b x) = multiply (pmult a b) x"
proof -
  have "get_h (multiply (pmult a b) x) = get_h x"
    by (metis assms get_h_multiply p_greater_exists padd_asso pmult_order pmult_special(1))
  moreover have "get_h (multiply a (multiply b x)) = get_h x"
    using assms get_h_multiply by presburger
  moreover have "get_m (multiply a (multiply b x)) = get_m (multiply (pmult a b) x)"
  proof (rule ext)
    fix l
    have "pgte pwrite (pmult a b)" using multiply_smaller_pwrite assms by simp
    then have "get_m (multiply (pmult a b) x) l = pmult (pmult a b) (get_m x l)"
      using get_m_smaller by blast
    then show "get_m (multiply a (multiply b x)) l = get_m (multiply (pmult a b) x) l"
      by (metis Rep_prat_inverse assms get_m_smaller mult.assoc pmult.rep_eq)
  qed
  ultimately show ?thesis
    using state_ext by presburger
qed

lemma valid_mask_add_comp_min:
  assumes "valid_mask a"
      and "valid_mask b"
  shows "valid_mask (add_masks (comp_min_mask b a) b)"
proof (rule valid_maskI)
  show "\<And>f. add_masks (comp_min_mask b a) b (null, f) = pnone"
  proof -
    fix f
    have "comp_min_mask b a (null, f) = pnone"
      by (metis assms(1) comp_min_mask_def p_greater_exists padd_zero pmin_greater valid_mask.simps)
    then show "add_masks (comp_min_mask b a) b (null, f) = pnone"
      by (metis add_masks.simps assms(2) padd_zero valid_mask.simps)
  qed
  fix hl show "pgte pwrite (add_masks (comp_min_mask b a) b hl)"
  proof (cases "pgte (a hl) (comp_one (b hl))")
    case True
    then have "add_masks (comp_min_mask b a) b hl = padd (comp_one (b hl)) (b hl)"
      by (simp add: comp_min_mask_def pmin_is)
    then have "add_masks (comp_min_mask b a) b hl = pwrite"
      by (metis assms(2) padd_comm padd_comp_one valid_mask.simps)
    then show ?thesis
      by (simp add: pgte.rep_eq)
  next
    case False
    then have "comp_min_mask b a hl = a hl"
      by (metis comp_min_mask_def not_pgte_charact pgt_implies_pgte pmin_comm pmin_is)
    then have "add_masks (comp_min_mask b a) b hl = padd (a hl) (b hl)"
      by auto
    moreover have "pgte (padd (comp_one (b hl)) (b hl)) (padd (a hl) (b hl))"
      using False padd.rep_eq pgte.rep_eq by force
    moreover have "padd (comp_one (b hl)) (b hl) = pwrite"
      by (metis assms(2) padd_comm padd_comp_one valid_mask.simps)
    ultimately show ?thesis by simp
  qed
qed



subsection \<open>The combinable wand is stronger than the original wand\<close>

lemma cwand_stronger:
  "cwand A B \<subseteq> wand A B"
proof
  fix w assume asm0: "w \<in> cwand A B"
  then have r: "\<And>a x. a \<in> A \<and> Some x = R a w \<oplus> a \<Longrightarrow> x \<in> B"
    using cwand_def by blast
  show "w \<in> wand A B"
  proof (rule wandI)
    fix a x assume asm1: "a \<in> A \<and> Some x = a \<oplus> w"
    then have "R a w = w"
      by (metis PartialSA.defined_def R_compatible_same option.distinct(1))
    then show "x \<in> B"
      by (metis PartialSA.commutative asm1 r)
  qed
qed


subsection \<open>The combinable wand is the same as the original wand when the left-hand side is binary\<close>

lemma binary_same:
  assumes "binary A"
      and "intuitionistic B"
  shows "wand A B \<subseteq> cwand A B"
proof (rule subsetI)
  fix w assume "w \<in> wand A B"
  then have asm0: "A \<otimes> {w} \<subseteq> B"
    by (simp add: wand_equiv_def)
  show "w \<in> cwand A B"
  proof (rule in_cwand)
    fix a x assume asm1: "a \<in> A \<and> Some x = R a w \<oplus> a"
    show "x \<in> B"
    proof (cases "scalable w a")
      case True
      then show ?thesis
        by (metis PartialSA.commutative PartialSA.defined_def R_def asm1 option.distinct(1) scalable_def w_in_scaled)
    next
      case False
      then have r0: "get_m (R a w) = comp_min_mask (get_m a) (get_m w) \<and> get_h (R a w) = get_h w"
        using non_scalable_R_charact by blast
      moreover have "Abs_state (binary_mask (get_m a), get_h a) \<in> A"
        using asm1 assms(1) binary_def by blast
      moreover have "greater_mask (add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a))
  (add_masks (binary_mask (get_m a)) (get_m w))"
      proof (rule greater_maskI)
        fix hl show "pgte (add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a) hl) (add_masks (binary_mask (get_m a)) (get_m w) hl)"
        proof (cases "get_m a hl = pwrite")
          case True
          obtain \<phi> where "\<phi> \<in> scaled w" "a |#| \<phi>" using False scalable_def[of w a]
            by blast
          then obtain p where "ppos p" "pgte pwrite p" "multiply p w |#| a"
            using PartialSA.commutative PartialSA.defined_def mem_Collect_eq scaled_def by auto
          have "get_m w hl = pnone"
          proof (rule ccontr)
            assume "get_m w hl \<noteq> pnone"
            then have "ppos (get_m w hl)"
              by (metis less_add_same_cancel1 not_pgte_charact p_greater_exists padd.rep_eq padd_zero pgt.rep_eq ppos.rep_eq)
            moreover have "get_m (multiply p \<phi>) = multiply_mask p (get_m \<phi>)"
              using multiply_valid[of p \<phi>] multiply.simps[of p \<phi>]
              by (metis Rep_state_cases Rep_state_inverse \<open>pgte pwrite p\<close> fst_conv get_pre(2) mem_Collect_eq)
            then have "ppos (get_m (multiply p w) hl)" using pmult_ppos
              by (metis Rep_state_cases Rep_state_inverse \<open>pgte pwrite p\<close> \<open>ppos p\<close> calculation fst_conv get_pre(2) mem_Collect_eq multiply.simps multiply_mask_def multiply_valid)
            then have "pgt (padd (get_m (multiply p w) hl) (get_m a hl)) pwrite"
              by (metis True add_le_same_cancel2 leD not_pgte_charact padd.rep_eq pgte.rep_eq ppos.rep_eq)
            then have "\<not> valid_mask (add_masks (get_m (multiply p w)) (get_m a))"
              by (metis add_masks.elims not_pgte_charact valid_mask.elims(1))
            then show False
              using PartialSA.defined_def \<open>multiply p w |#| a\<close> plus_ab_defined by blast
          qed
          then show ?thesis
            by (metis Rep_prat_inverse add.right_neutral add_masks.simps binary_mask_def p_greater_exists padd.rep_eq padd_comm pnone.rep_eq)
        next
          case False
          then have "add_masks (binary_mask (get_m a)) (get_m w) hl = get_m w hl"
            by (metis Rep_prat_inject add.right_neutral add_masks.simps binary_mask_def padd.rep_eq padd_comm pnone.rep_eq)
          then show ?thesis
          proof (cases "pgte (get_m w hl) (comp_one (get_m a hl))")
            case True
            then have "comp_min_mask (get_m a) (get_m w) hl = comp_one (get_m a hl)"
              using comp_min_mask_def pmin_is by presburger
            then have "add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a) hl = pwrite"
              by (metis PartialSA.unit_neutral add_masks.simps add_masks_comm minus_empty option.distinct(1) padd_comp_one plus_ab_defined unit_charact(2) valid_mask.simps)
            then show ?thesis
              by (metis PartialSA.unit_neutral \<open>add_masks (binary_mask (get_m a)) (get_m w) hl = get_m w hl\<close> minus_empty option.distinct(1) plus_ab_defined unit_charact(2) valid_mask.simps)
          next
            case False
            then have "comp_min_mask (get_m a) (get_m w) hl = get_m w hl"
              by (metis comp_min_mask_def not_pgte_charact pgt_implies_pgte pmin_comm pmin_is)
            then show ?thesis
              using \<open>add_masks (binary_mask (get_m a)) (get_m w) hl = get_m w hl\<close> p_greater_exists by auto
          qed
        qed
      qed
      then have "valid_mask (add_masks (binary_mask (get_m a)) (get_m w))"
        by (metis asm1 calculation(1) greater_mask_def option.distinct(1) plus_ab_defined upper_valid_aux)
      moreover have "compatible_heaps (get_h a) (get_h w)"
        by (metis PartialSA.commutative asm1 r0 option.simps(3) plus_ab_defined)
      then obtain xx where "Some xx = Abs_state (binary_mask (get_m a), get_h a) \<oplus> w"
        using Abs_state_inverse calculation compatible_def fst_conv plus_def valid_bin by auto
      then have "xx \<in> B" using asm0
        by (meson PartialSA.add_set_elem \<open>Abs_state (binary_mask (get_m a), get_h a) \<in> A\<close> singletonI subset_iff)
      moreover have "x \<succeq> xx"
      proof (rule greaterI)
        show "greater_mask (get_m x) (get_m xx)"
          using Abs_state_inverse \<open>Some xx = Abs_state (binary_mask (get_m a), get_h a) \<oplus> w\<close> asm1 \<open>greater_mask (add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a)) (add_masks (binary_mask (get_m a)) (get_m w))\<close> calculation(1) plus_charact(1) valid_bin by auto
        show "larger_heap (get_h x) (get_h xx)"
        proof (rule larger_heapI)
          fix hl xa assume "get_h xx hl = Some xa"
          then show "get_h x hl = Some xa"
            by (metis PartialSA.commutative Rep_state_cases Rep_state_inverse \<open>Some xx = Abs_state (binary_mask (get_m a), get_h a) \<oplus> w\<close> asm1 calculation(1) get_h.simps mem_Collect_eq plus_charact(2) snd_conv valid_bin)
        qed
      qed
      ultimately show ?thesis
        using assms(2) intuitionistic_def by blast
    qed
  qed
qed


subsection \<open>The combinable wand is combinable\<close>

lemma combinableI:
  assumes "\<And>a b. ppos a \<and> ppos b \<and> padd a b = pwrite \<Longrightarrow> (multiply_sem_assertion a (cwand A B)) \<otimes> (multiply_sem_assertion b (cwand A B)) \<subseteq> cwand A B"
  shows "combinable (cwand A B)"
proof -
  have "\<And>a b. ppos a \<and> ppos b \<and> pgte pwrite (padd a b) \<Longrightarrow> (multiply_sem_assertion a (cwand A B)) \<otimes> (multiply_sem_assertion b (cwand A B)) \<subseteq> multiply_sem_assertion (padd a b) (cwand A B)"
  proof -    
    fix a b assume asm0: "ppos a \<and> ppos b \<and> pgte pwrite (padd a b)"
    then have "pgte pwrite a \<and> pgte pwrite b"
      using padd.rep_eq pgte.rep_eq ppos.rep_eq by auto
    show "(multiply_sem_assertion a (cwand A B)) \<otimes> (multiply_sem_assertion b (cwand A B)) \<subseteq> multiply_sem_assertion (padd a b) (cwand A B)"
    proof
      fix x assume "x \<in> multiply_sem_assertion a (cwand A B) \<otimes> multiply_sem_assertion b (cwand A B)"
      then obtain xa xb where "Some x = xa \<oplus> xb" "xa \<in> multiply_sem_assertion a (cwand A B)" "xb \<in> multiply_sem_assertion b (cwand A B)"
        by (meson PartialSA.add_set_elem)
      then obtain wa wb where "wa \<in> cwand A B" "wb \<in> cwand A B" "xa \<succeq> multiply a wa" "xb \<succeq> multiply b wb"
        by (meson in_multiply_sem)
      let ?a = "pdiv a (padd a b)"
      let ?b = "pdiv b (padd a b)"
      have r0: "pgte pwrite ?a \<and> pgte pwrite ?b"
        using asm0 p_greater_exists padd_comm pdiv_smaller ppos_add by blast
      have "multiply ?a wa |#| multiply ?b wb"
      proof (rule compatibleI)
        show "compatible_heaps (get_h (multiply (pdiv a (padd a b)) wa)) (get_h (multiply (pdiv b (padd a b)) wb))"
        proof -
          have "compatible_heaps (get_h (multiply a wa)) (get_h (multiply b wb))"
            by (metis PartialSA.asso2 PartialSA.asso3 PartialSA.greater_equiv PartialSA.minus_some \<open>Some x = xa \<oplus> xb\<close> \<open>xa \<succeq> multiply a wa\<close> \<open>xb \<succeq> multiply b wb\<close> option.simps(3) plus_ab_defined)
          moreover have "get_h (multiply (pdiv a (padd a b)) wa) = get_h (multiply a wa) \<and> get_h (multiply (pdiv b (padd a b)) wb) = get_h (multiply b wb)"
          proof -
            have "pgte pwrite a \<and> pgte pwrite b"
              by (metis asm0 p_greater_exists padd_asso padd_comm)
            moreover have "pgte pwrite ?a \<and> pgte pwrite ?b"
              using asm0 p_greater_exists padd_comm pdiv_smaller ppos_add by blast
            ultimately show ?thesis
              using get_h_multiply by presburger
          qed
          then show ?thesis
            using calculation by presburger
        qed
        show "valid_mask (add_masks (get_m (multiply (pdiv a (padd a b)) wa)) (get_m (multiply (pdiv b (padd a b)) wb)))"
        proof (rule valid_maskI)
          show "\<And>f. add_masks (get_m (multiply (pdiv a (padd a b)) wa)) (get_m (multiply (pdiv b (padd a b)) wb)) (null, f) = pnone"
            by (metis PartialSA.unit_neutral add_masks_equiv_valid_null option.distinct(1) plus_ab_defined valid_mask.simps valid_null_def)
          fix hl have "add_masks (get_m (multiply (pdiv a (padd a b)) wa)) (get_m (multiply (pdiv b (padd a b)) wb)) hl
                      = padd (pmult ?a (get_m wa hl)) (pmult ?b (get_m wb hl))"
          proof -
            have "get_m (multiply ?a wa) hl = pmult ?a (get_m wa hl)"
              using Abs_state_inverse r0 multiply_mask_def multiply_valid by auto
            moreover have "get_m (multiply ?b wb) hl = pmult ?b (get_m wb hl)"
              using Abs_state_inverse r0 multiply_mask_def multiply_valid by auto
            ultimately show ?thesis by simp
          qed
          moreover have "pgte pwrite (padd (pmult ?a (get_m wa hl)) (pmult ?b (get_m wb hl)))"
          proof (rule padd_one_ineq_sum)
            show "pgte pwrite (get_m wa hl)"
              by (metis PartialSA.unit_neutral option.discI plus_ab_defined upper_valid_aux valid_mask.simps)
            show "pgte pwrite (get_m wb hl)"
              by (metis PartialSA.unit_neutral option.discI plus_ab_defined upper_valid_aux valid_mask.simps)
            show "padd (pdiv a (padd a b)) (pdiv b (padd a b)) = pwrite"
              using asm0 sum_coeff by blast
          qed
          ultimately show "pgte pwrite (add_masks (get_m (multiply (pdiv a (padd a b)) wa)) (get_m (multiply (pdiv b (padd a b)) wb)) hl)"
            by presburger
        qed
      qed
      then obtain xx where xx_def: "Some xx = multiply ?a wa \<oplus> multiply ?b wb"        
        using PartialSA.defined_def by auto
      moreover have inclusion: "(multiply_sem_assertion ?a (cwand A B)) \<otimes> (multiply_sem_assertion ?b (cwand A B)) \<subseteq> cwand A B"
      proof (rule assms)
        show "ppos (pdiv a (padd a b)) \<and> ppos (pdiv b (padd a b)) \<and> padd (pdiv a (padd a b)) (pdiv b (padd a b)) = pwrite"
          using asm0 padd.rep_eq pdiv.rep_eq ppos.rep_eq sum_coeff by auto
      qed
      ultimately have "xx \<in> cwand A B"
      proof -
        have "multiply ?a wa \<in> multiply_sem_assertion ?a (cwand A B)"
          using \<open>wa \<in> cwand A B\<close> in_multiply_refl by presburger
        moreover have "multiply ?b wb \<in> multiply_sem_assertion ?b (cwand A B)"
          by (meson \<open>wb \<in> cwand A B\<close> in_multiply_refl)
        ultimately show ?thesis
          using PartialSA.add_set_def xx_def inclusion by fastforce
      qed
      moreover have "x \<succeq> multiply (padd a b) xx"
      proof (rule greaterI)
        have "valid_state (multiply_mask (padd a b) (get_m xx), get_h xx)"
          using asm0 multiply_valid by blast
        show "larger_heap (get_h x) (get_h (multiply (padd a b) xx))"
        proof -
          have "get_h (multiply (padd a b) xx) = get_h xx"
            using asm0 get_h_multiply by blast
          moreover have "get_h xx = get_h wa ++ get_h wb"
            by (metis xx_def asm0 get_h_multiply p_greater_exists padd_comm plus_charact(2) sum_coeff)
          moreover have "get_h x = get_h xa ++ get_h xb"
            using \<open>Some x = xa \<oplus> xb\<close> plus_charact(2) by presburger
          moreover have "get_h wa = get_h (multiply a wa) \<and> get_h wb = get_h (multiply b wb)"
            by (metis asm0 get_h_multiply order_trans p_greater_exists padd_comm pgte.rep_eq)
          moreover have "larger_heap (get_h xa) (get_h wa) \<and> larger_heap (get_h xb) (get_h wb)"
            using \<open>xa \<succeq> multiply a wa\<close> \<open>xb \<succeq> multiply b wb\<close> calculation(4) larger_implies_larger_heap by presburger
          ultimately show ?thesis
            by (metis \<open>Some x = xa \<oplus> xb\<close> larger_heaps_sum_ineq option.simps(3) plus_ab_defined)
        qed
        show "greater_mask (get_m x) (get_m (multiply (padd a b) xx))"
        proof (rule greater_maskI)
          fix hl
          have "pgte (get_m x hl) (padd (get_m xa hl) (get_m xb hl))"
            using \<open>Some x = xa \<oplus> xb\<close> pgte.rep_eq plus_charact(1) by auto
          moreover have "pgte (get_m xa hl) (get_m (multiply a wa) hl) \<and> pgte (get_m xb hl) (get_m (multiply b wb) hl)"
            using \<open>xa \<succeq> multiply a wa\<close> \<open>xb \<succeq> multiply b wb\<close> larger_implies_greater_mask_hl by blast
          moreover have "get_m (multiply (padd a b) xx) hl = pmult (padd a b) (get_m xx hl)"
            by (metis Rep_state_cases Rep_state_inverse \<open>valid_state (multiply_mask (padd a b) (get_m xx), get_h xx)\<close> fst_conv get_pre(2) mem_Collect_eq multiply.simps multiply_mask_def)
          moreover have "... = padd (pmult (pmult (padd a b) ?a) (get_m wa hl)) (pmult (pmult (padd a b) ?b) (get_m wb hl))"
          proof -
            have "get_m (multiply ?a wa) hl = pmult ?a (get_m wa hl)"
              by (metis Abs_state_inverse asm0 fst_conv get_pre(2) mem_Collect_eq multiply.simps multiply_mask_def multiply_valid p_greater_exists sum_coeff)
            moreover have "get_m (multiply ?b wb) hl = pmult ?b (get_m wb hl)"
              by (metis Abs_state_inverse asm0 fst_conv get_pre(2) mem_Collect_eq multiply.simps multiply_mask_def multiply_valid p_greater_exists padd_comm pdiv_smaller ppos_add)
            ultimately have "get_m xx hl = padd (pmult ?a (get_m wa hl)) (pmult ?b (get_m wb hl))"
              using xx_def plus_charact(1) by fastforce
            then show ?thesis
              by (simp add: pmult_padd)
          qed
          moreover have "... = padd (pmult a (get_m wa hl)) (pmult b (get_m wb hl))"
            using asm0 pmult_pdiv_cancel ppos_add by presburger
          moreover have "get_m (multiply a wa) hl = pmult a (get_m wa hl) \<and> get_m (multiply b wb) hl = pmult b (get_m wb hl)"
          proof -
            have "valid_mask (multiply_mask a (get_m wa))"
              using asm0 mult_add_states multiply_valid upper_valid_aux valid_state.simps by blast
            moreover have "valid_mask (multiply_mask b (get_m wb))"
              using asm0 mult_add_states multiply_valid upper_valid valid_state.simps by blast
            ultimately show ?thesis
              by (metis (no_types, lifting) Abs_state_inverse asm0 fst_conv get_pre(2) mem_Collect_eq multiply.simps multiply_mask_def multiply_valid order_trans p_greater_exists padd_comm pgte.rep_eq)
          qed
          ultimately show "pgte (get_m x hl) (get_m (multiply (padd a b) xx) hl)"
            by (simp add: padd.rep_eq pgte.rep_eq)
        qed
      qed
      ultimately show "x \<in> multiply_sem_assertion (padd a b) (cwand A B)"
        by (metis PartialSA.up_closed_def PartialSA.upper_closure_up_closed in_multiply_refl multiply_sem_assertion.simps)
    qed
  qed
  then show ?thesis
    using combinable_def by presburger
qed

lemma combinable_cwand:
  assumes "combinable B"
      and "intuitionistic B"
    shows "combinable (cwand A B)"
proof (rule combinableI)
  fix \<alpha> \<beta> assume asm0: "ppos \<alpha> \<and> ppos \<beta> \<and> padd \<alpha> \<beta> = pwrite"
  then have "pgte pwrite \<alpha> \<and> pgte pwrite \<beta>"
    by (metis p_greater_exists padd_comm)
  show "multiply_sem_assertion \<alpha> (cwand A B) \<otimes> multiply_sem_assertion \<beta> (cwand A B) \<subseteq> cwand A B"
  proof
    fix w assume asm: "w \<in> multiply_sem_assertion \<alpha> (cwand A B) \<otimes> multiply_sem_assertion \<beta> (cwand A B)"
    then obtain xa xb where "Some w = xa \<oplus> xb" "xa \<in> multiply_sem_assertion \<alpha> (cwand A B)" "xb \<in> multiply_sem_assertion \<beta> (cwand A B)"
      by (meson PartialSA.add_set_elem)
    then obtain wa wb where "wa \<in> cwand A B" "wb \<in> cwand A B" "xa \<succeq> multiply \<alpha> wa" "xb \<succeq> multiply \<beta> wb"
      by (meson in_multiply_sem)
    then obtain r: "\<And>a x. a \<in> A \<and> Some x = R a wa \<oplus> a \<Longrightarrow> x \<in> B" "\<And>a x. a \<in> A \<and> Some x = R a wb \<oplus> a \<Longrightarrow> x \<in> B"
      using cwand_def by blast
    show "w \<in> cwand A B"
    proof (rule in_cwand)
      fix a x assume asm1: "a \<in> A \<and> Some x = R a w \<oplus> a"
      have "\<not> scalable w a"
      proof (rule ccontr)
        assume "\<not> \<not> scalable w a"
        then have "R a w = w \<and> \<not> a |#| R a w"
          by (simp add: R_def scalable_def w_in_scaled)
        then show False
          using PartialSA.commutative PartialSA.defined_def asm1 by auto
      qed
      then have r3: "get_h (R a w) = get_h w \<and> get_m (R a w) = comp_min_mask (get_m a) (get_m w)"
        using non_scalable_R_charact by blast
      moreover obtain p where "a |#| multiply p w" "ppos p \<and> pgte pwrite p"
        using \<open>\<not> scalable w a\<close> non_scalable_instantiate by blast
      moreover have "\<not> scalable wa a"
      proof -
        have "a |#| multiply (pmult \<alpha> p) wa"
        proof -
          have "w \<succeq> xa" using \<open>Some w = xa \<oplus> xb\<close> using PartialSA.greater_def by blast
          then have "multiply p w \<succeq> multiply p xa"
            using calculation(3) multiply_order by blast
          then have "multiply p w \<succeq> multiply (pmult \<alpha> p) wa"
          proof -
            have "multiply p w \<succeq> multiply p (multiply \<alpha> wa)"
              using PartialSA.succ_trans \<open>w \<succeq> xa\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> calculation(3) multiply_order by blast
            then show ?thesis
              using \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> calculation(3) multiply_twice pmult_comm by auto
          qed
          then show ?thesis
            using PartialSA.asso3 PartialSA.defined_def PartialSA.minus_some calculation(2) by fastforce
        qed
        moreover have "ppos (pmult \<alpha> p) \<and> pgte pwrite (pmult \<alpha> p)"
          by (metis Rep_prat_inverse \<open>ppos p \<and> pgte pwrite p\<close> add.right_neutral asm0 dual_order.strict_iff_order padd.rep_eq pgte.rep_eq pmult_comm pmult_ppos pmult_special(2) pnone.rep_eq ppos.rep_eq ppos_eq_pnone padd_one_ineq_sum)
        ultimately show ?thesis
          using scalable_def scaled_def by auto
      qed
      then have r1: "get_h (R a wa) = get_h wa \<and> get_m (R a wa) = comp_min_mask (get_m a) (get_m wa)"
        using non_scalable_R_charact by blast
      moreover have "R a wa |#| a"
      proof (rule compatibleI)
        have "larger_heap (get_h w) (get_h xa) \<and> larger_heap (get_h xa) (get_h wa)"
          by (metis PartialSA.commutative PartialSA.greater_equiv \<open>Some w = xa \<oplus> xb\<close> \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_h_multiply larger_implies_larger_heap)
        then show "compatible_heaps (get_h (R a wa)) (get_h a)"
          by (metis asm1 calculation(1) calculation(4) larger_heap_comp option.distinct(1) plus_ab_defined)
        show "valid_mask (add_masks (get_m (R a wa)) (get_m a))"
          by (metis PartialSA.unit_neutral calculation(4) minus_empty option.distinct(1) plus_ab_defined unit_charact(2) valid_mask_add_comp_min)
      qed
      then obtain ba where "Some ba = R a wa \<oplus> a"
        using PartialSA.defined_def by auto

      moreover have "\<not> scalable wb a"
      proof -
        have "a |#| multiply (pmult \<beta> p) wb"
        proof -
          have "w \<succeq> xb" using \<open>Some w = xa \<oplus> xb\<close>
            using PartialSA.greater_equiv by blast
          then have "multiply p w \<succeq> multiply p xb"
            using calculation(3) multiply_order by blast
          then have "multiply p w \<succeq> multiply (pmult \<beta> p) wb"
          proof -
            have "multiply p w \<succeq> multiply p (multiply \<beta> wb)"
              using PartialSA.succ_trans \<open>w \<succeq> xb\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> calculation(3) multiply_order by blast
            then show ?thesis
              using \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> calculation(3) multiply_twice pmult_comm by auto
          qed
          then show ?thesis
            using PartialSA.asso3 PartialSA.defined_def PartialSA.minus_some calculation(2) by fastforce
        qed
        moreover have "ppos (pmult \<beta> p) \<and> pgte pwrite (pmult \<beta> p)"
          by (simp add: \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>ppos p \<and> pgte pwrite p\<close> asm0 multiply_smaller_pwrite pmult_ppos)
        ultimately show ?thesis
          using scalable_def scaled_def by auto
      qed
      then have r2: "get_h (R a wb) = get_h wb \<and> get_m (R a wb) = comp_min_mask (get_m a) (get_m wb)"
        using non_scalable_R_charact by blast
      moreover have "R a wb |#| a"
      proof (rule compatibleI)
        have "larger_heap (get_h w) (get_h xb) \<and> larger_heap (get_h xb) (get_h wb)"
          using \<open>Some w = xa \<oplus> xb\<close> \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_h_multiply larger_heap_def larger_implies_larger_heap plus_charact(2) by fastforce
        then show "compatible_heaps (get_h (R a wb)) (get_h a)"
          by (metis asm1 calculation(1) calculation(6) larger_heap_comp option.simps(3) plus_ab_defined)
        show "valid_mask (add_masks (get_m (R a wb)) (get_m a))"
          by (metis PartialSA.unit_neutral calculation(6) minus_empty option.distinct(1) plus_ab_defined unit_charact(2) valid_mask_add_comp_min)
      qed
      then obtain bb where "Some bb = R a wb \<oplus> a"
        using PartialSA.defined_def by auto

      moreover obtain ya where "Some ya = R a wa \<oplus> a"
        using calculation(5) by auto
      then have "ya \<in> B"
        using asm1 r(1) by blast
      then have "multiply \<alpha> ya \<in> multiply_sem_assertion \<alpha> B"
        using in_multiply_refl by blast
      moreover obtain yb where "Some yb = R a wb \<oplus> a"
        using calculation(7) by auto
      then have "yb \<in> B"
        using asm1 r(2) by blast
      then have "multiply \<beta> yb \<in> multiply_sem_assertion \<beta> B"
        using in_multiply_refl by blast
      moreover have "(multiply \<alpha> ya) |#| (multiply \<beta> yb)"
      proof (rule compatibleI)
        have "get_h ya = get_h wa ++ get_h a"
          using \<open>Some ya = R a wa \<oplus> a\<close> r1 plus_charact(2) by presburger
        then have "get_h (multiply \<alpha> ya) = get_h wa ++ get_h a"
          using \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> get_h_multiply by presburger
        moreover have "get_h yb = get_h wb ++ get_h a"
          using \<open>Some yb = R a wb \<oplus> a\<close> r2 plus_charact(2) by presburger
        then have "get_h (multiply \<beta> yb) = get_h wb ++ get_h a"
          using \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> get_h_multiply by presburger
        moreover have "compatible_heaps (get_h wa) (get_h wb)"
        proof (rule compatible_heapsI)
          fix hl a b assume "get_h wa hl = Some a" "get_h wb hl = Some b"
          then have "get_h xa hl = Some a" "get_h xb hl = Some b"
           apply (metis (full_types) \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_h_multiply larger_heap_def larger_implies_larger_heap)
            by (metis \<open>get_h wb hl = Some b\<close> \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_h_multiply larger_heap_def larger_implies_larger_heap)
          moreover have "compatible_heaps (get_h xa) (get_h xb)"
            by (metis \<open>Some w = xa \<oplus> xb\<close> option.simps(3) plus_ab_defined)
          ultimately show "a = b"
            by (metis compatible_heaps_def compatible_options.simps(1))
        qed
        ultimately show "compatible_heaps (get_h (multiply \<alpha> ya)) (get_h (multiply \<beta> yb))"
          by (metis PartialSA.commutative PartialSA.core_is_smaller \<open>Some ya = R a wa \<oplus> a\<close> \<open>Some yb = R a wb \<oplus> a\<close>
              r1 r2 compatible_heaps_sum core_defined(1) core_defined(2) option.distinct(1) plus_ab_defined)
        show "valid_mask (add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)))"
        proof (rule valid_maskI)
          show "\<And>f. add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)) (null, f) = pnone"
            by (metis (no_types, opaque_lifting) PartialSA.core_is_smaller add_masks.simps core_defined(2) minus_empty not_None_eq plus_ab_defined valid_mask.simps)
          fix hl 
          have "add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)) hl = padd (pmult \<alpha> (get_m ya hl)) (pmult \<beta> (get_m yb hl))"
            using \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> get_m_smaller by auto
          moreover have "get_m ya hl = padd (get_m (R a wa) hl) (get_m a hl) \<and> get_m yb hl = padd (get_m (R a wb) hl) (get_m a hl)"
            using \<open>Some ya = R a wa \<oplus> a\<close> \<open>Some yb = R a wb \<oplus> a\<close> plus_charact(1) by auto          
          ultimately show "pgte pwrite (add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)) hl)"
            by (metis PartialSA.unit_neutral asm0 option.distinct(1) padd_one_ineq_sum plus_ab_defined plus_charact(1) valid_mask.simps)
        qed
      qed
      then obtain y where "Some y = multiply \<alpha> ya \<oplus> multiply \<beta> yb"
        using PartialSA.defined_def by auto
      moreover have "x \<succeq> y"
      proof (rule greaterI)
        have "get_h y = get_h ya ++ get_h yb"
          using \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> calculation(10) get_h_multiply plus_charact(2) by presburger
        moreover have "get_h ya = get_h wa ++ get_h a"
          using \<open>Some ya = R a wa \<oplus> a\<close> r1 plus_charact(2) by presburger
        moreover have "get_h yb = get_h wb ++ get_h a"
          using \<open>Some yb = R a wb \<oplus> a\<close> r2 plus_charact(2) by presburger
        moreover have "larger_heap (get_h x) (get_h wa)"
        proof -
          have "larger_heap (get_h x) (get_h xa)"
            by (metis PartialSA.greater_def \<open>Some w = xa \<oplus> xb\<close> r3 asm1 larger_heap_trans larger_implies_larger_heap)
          moreover have "larger_heap (get_h xa) (get_h wa)"
            by (metis \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_h_multiply larger_implies_larger_heap)
          ultimately show ?thesis
            using larger_heap_trans by blast
        qed
        moreover have "larger_heap (get_h x) (get_h wb)"
        proof -
          have "larger_heap (get_h x) (get_h xb)"
            by (metis PartialSA.greater_def PartialSA.greater_equiv \<open>Some w = xa \<oplus> xb\<close> r3 asm1 larger_heap_trans larger_implies_larger_heap)
          moreover have "larger_heap (get_h xb) (get_h wb)"
            by (metis \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_h_multiply larger_implies_larger_heap)
          ultimately show ?thesis
            using larger_heap_trans by blast
        qed
        moreover have "larger_heap (get_h x) (get_h a)"
          using PartialSA.greater_equiv asm1 larger_implies_larger_heap by blast
        ultimately show "larger_heap (get_h x) (get_h y)"          
          by (simp add: larger_heap_plus)
        show "greater_mask (get_m x) (get_m y)"
        proof (rule greater_maskI)
          fix hl 
          have "get_m x hl = padd (get_m (R a w) hl) (get_m a hl)"
            using asm1 plus_charact(1) by auto
          moreover have "get_m y hl = padd (pmult \<alpha> (padd (get_m (R a wa) hl) (get_m a hl))) (pmult \<beta> (padd (get_m (R a wb) hl) (get_m a hl)))"
            by (metis \<open>Some y = multiply \<alpha> ya \<oplus> multiply \<beta> yb\<close> \<open>Some ya = R a wa \<oplus> a\<close> \<open>Some yb = R a wb \<oplus> a\<close> \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> add_masks.simps get_m_smaller plus_charact(1))

          moreover have equ: "padd (pmult \<alpha> (padd (get_m (R a wa) hl) (get_m a hl))) (pmult \<beta> (padd (get_m (R a wb) hl) (get_m a hl)))
= padd (padd (pmult \<alpha> (get_m a hl)) (pmult \<beta> (get_m a hl))) (padd (pmult \<alpha> (get_m (R a wa) hl)) (pmult \<beta> (get_m (R a wb) hl)))"
            using padd_asso padd_comm pmult_distr by force

          have "pgte (get_m (R a w) hl) (padd (pmult \<alpha> (get_m (R a wa) hl)) (pmult \<beta> (get_m (R a wb) hl)))"
          proof (cases "pgte (get_m w hl) (comp_one (get_m a hl))")
            case True
            then have "get_m (R a w) hl = (comp_one (get_m a hl))"
              using r3 comp_min_mask_def pmin_is by presburger
            moreover have "pgte (comp_one (get_m a hl)) (get_m (R a wa) hl)"
              by (metis r1 comp_min_mask_def pmin_comm pmin_greater)
            then have "pgte (pmult \<alpha> (comp_one (get_m a hl))) (pmult \<alpha> (get_m (R a wa) hl))"
              by (metis pmult_comm pmult_order)
            moreover have "pgte (comp_one (get_m a hl)) (get_m (R a wb) hl)"
              by (metis r2 comp_min_mask_def pmin_comm pmin_greater)
            then have "pgte (pmult \<beta> (comp_one (get_m a hl))) (pmult \<beta> (get_m (R a wb) hl))"
              by (metis pmult_comm pmult_order)
            ultimately show ?thesis
              using \<open>pgte (comp_one (get_m a hl)) (get_m (R a wa) hl)\<close> \<open>pgte (comp_one (get_m a hl)) (get_m (R a wb) hl)\<close> asm0 padd_one_ineq_sum by presburger
          next
            case False
            then have "get_m (R a w) hl = get_m w hl"
              by (metis r3 comp_min_mask_def not_pgte_charact pgt_implies_pgte pmin_comm pmin_is)
            moreover have "pgte (get_m w hl) (padd (pmult \<alpha> (get_m wa hl)) (pmult \<beta> (get_m wb hl)))"
            proof -
              have "pgte (get_m w hl) (padd (get_m xa hl) (get_m xb hl))"
                using \<open>Some w = xa \<oplus> xb\<close> not_pgte_charact pgt_implies_pgte plus_charact(1) by auto
              moreover have "pgte (get_m xa hl) (pmult \<alpha> (get_m wa hl))"
                by (metis \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_m_smaller larger_implies_greater_mask_hl)
              moreover have "pgte (get_m xb hl) (pmult \<beta> (get_m wb hl))"
                by (metis \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_m_smaller larger_implies_greater_mask_hl)
              ultimately show ?thesis
                by (simp add: padd.rep_eq pgte.rep_eq)
            qed
            moreover have "pgte (pmult \<alpha> (get_m wa hl)) (pmult \<alpha> (get_m (R a wa) hl))"
              by (metis R_smaller larger_implies_greater_mask_hl pmult_comm pmult_order)
            moreover have "pgte (pmult \<beta> (get_m wb hl)) (pmult \<beta> (get_m (R a wb) hl))"
              by (metis R_smaller larger_implies_greater_mask_hl pmult_comm pmult_order)
            ultimately show ?thesis
              using padd.rep_eq pgte.rep_eq by force
          qed
          moreover have "get_m x hl = padd (get_m (R a w) hl) (get_m a hl)"
            using calculation(1) by auto
          moreover have "get_m y hl = padd (pmult \<alpha> (get_m ya hl)) (pmult \<beta> (get_m yb hl))"
            using \<open>Some y = multiply \<alpha> ya \<oplus> multiply \<beta> yb\<close> \<open>pgte pwrite \<alpha> \<and> pgte pwrite \<beta>\<close> get_m_smaller plus_charact(1) by auto
          moreover have "padd (pmult \<alpha> (get_m ya hl)) (pmult \<beta> (get_m yb hl)) = 
padd (pmult \<alpha> (padd (get_m (R a wa) hl) (get_m a hl))) (pmult \<beta> (padd (get_m (R a wb) hl) (get_m a hl)))"
            using calculation(2) calculation(5) by presburger
          moreover have "... = padd (pmult (padd \<alpha> \<beta>) (get_m a hl)) (padd (pmult \<alpha> (get_m (R a wa) hl)) (pmult \<beta> (get_m (R a wb) hl)))"
            by (metis equ pmult_comm pmult_distr)
          ultimately show "pgte (get_m x hl) (get_m y hl)"
            using asm0 p_greater_exists padd_asso padd_comm pmult_special(1) by force
        qed
      qed
      ultimately have "y \<in> multiply_sem_assertion \<alpha> B \<otimes> multiply_sem_assertion \<beta> B"
        using PartialSA.add_set_elem by blast
      then have "y \<in> multiply_sem_assertion pwrite B"
        by (metis asm0 assms(1) combinable_def not_pgte_charact pgt_implies_pgte subsetD)
      then obtain b where "y \<succeq> multiply pwrite b" "b \<in> B"
        using in_multiply_sem by blast
      then have "multiply pwrite b = b"
        by (metis Rep_state_inverse get_h_m mult_write_mask multiply.simps)
      then have "y \<in> B"
        by (metis \<open>b \<in> B\<close> \<open>y \<succeq> multiply pwrite b\<close> assms(2) intuitionistic_def)
      show "x \<in> B"
        using \<open>x \<succeq> y\<close> \<open>y \<in> B\<close> assms(2) intuitionistic_def by blast
    qed
  qed
qed





subsection Theorems

text \<open>The following theorem is crucial to use the package logic~\<^cite>\<open>"Dardinier22"\<close> to automatically
compute footprints of combinable wands.\<close>

theorem R_mono_transformer:
  "PartialSA.mono_transformer (R a)"
proof -
  have "R a unit = unit"
    by (simp add: PartialSA.succ_antisym PartialSA.unit_smaller R_smaller)
  moreover have "\<And>\<phi> \<phi>'. \<phi>' \<succeq> \<phi> \<Longrightarrow> R a \<phi>' \<succeq> R a \<phi>"
  proof -
    fix \<phi> \<phi>'
    assume "\<phi>' \<succeq> \<phi>"
    show "R a \<phi>' \<succeq> R a \<phi>"
    proof (cases "scalable \<phi>' a")
      case True
      then show ?thesis
        by (metis PartialSA.succ_trans R_def R_smaller \<open>\<phi>' \<succeq> \<phi>\<close>)
    next
      case False
      then obtain p where "ppos p" "pgte pwrite p" "multiply p \<phi>' |#| a"
        by (metis PartialSA.commutative PartialSA.defined_def non_scalable_instantiate)
      then have "multiply p \<phi> |#| a"
        using PartialSA.smaller_compatible \<open>\<phi>' \<succeq> \<phi>\<close> multiply_order by blast
      then have "\<not> scalable \<phi> a"
        using PartialSA.commutative PartialSA.defined_def \<open>pgte pwrite p\<close> \<open>ppos p\<close> scalable_def scaled_def by auto

      moreover have "greater_mask (comp_min_mask (get_m a) (get_m \<phi>')) (comp_min_mask (get_m a) (get_m  \<phi>))"
      proof (rule greater_maskI)
        fix hl show "pgte (comp_min_mask (get_m a) (get_m \<phi>') hl) (comp_min_mask (get_m a) (get_m \<phi>) hl)"
        proof (cases "pgte (get_m \<phi>' hl) (comp_one (get_m a hl))")
          case True
          then show ?thesis
            by (metis comp_min_mask_def pmin_comm pmin_greater pmin_is)
        next
          case False
          then show ?thesis
            by (metis PartialSA.succ_trans R_smaller \<open>\<phi>' \<succeq> \<phi>\<close> calculation comp_min_mask_def larger_implies_greater_mask_hl non_scalable_R_charact not_pgte_charact pgt_implies_pgte pmin_comm pmin_is)
        qed
      qed
      ultimately show ?thesis
        using False \<open>\<phi>' \<succeq> \<phi>\<close> greaterI larger_implies_larger_heap non_scalable_R_charact by presburger
    qed
  qed
  ultimately show ?thesis
    by (simp add: PartialSA.mono_transformer_def)
qed

theorem properties_of_combinable_wands:
  assumes "intuitionistic B"
    shows "combinable B \<Longrightarrow> combinable (cwand A B)"
      and "cwand A B \<subseteq> wand A B"
      and "binary A \<Longrightarrow> cwand A B = wand A B"
  by (simp_all add: assms combinable_cwand cwand_stronger binary_same dual_order.eq_iff)


end
