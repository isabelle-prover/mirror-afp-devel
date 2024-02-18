section\<open>BL-chains\<close>

text\<open>BL-chains generate the variety of BL-algebras, the algebraic counterpart
 of the Basic Fuzzy Logic (see \<^cite>\<open>"HAJEK1998"\<close>). As mentioned in the abstract, this formalization
 is based on the proof for BL-chains found in \<^cite>\<open>"BUSANICHE2005"\<close>. We define @{text "BL-chain"} and
 @{text "bounded tower of irreducible hoops"} and formalize the main result on that paper (Theorem 3.4).\<close>

theory BL_Chains
  imports Totally_Ordered_Hoops 

begin

subsection\<open>Definitions\<close>

locale bl_chain = totally_ordered_hoop + 
  fixes zeroA :: "'a" ("0\<^sup>A")
  assumes zero_closed: "0\<^sup>A \<in> A"
  assumes zero_first: "x \<in> A \<Longrightarrow> 0\<^sup>A \<le>\<^sup>A x"

locale bounded_tower_of_irr_hoops = tower_of_irr_hoops +
  fixes zeroI ("0\<^sup>I") 
  fixes zeroS ("0\<^sup>S")
  assumes I_zero_closed : "0\<^sup>I \<in> I"
  and zero_first: "i \<in> I \<Longrightarrow> 0\<^sup>I \<le>\<^sup>I i"
  and first_zero_closed: "0\<^sup>S \<in> UNI 0\<^sup>I"
  and first_bounded: "x \<in> UNI 0\<^sup>I \<Longrightarrow> IMP 0\<^sup>I 0\<^sup>S x = 1\<^sup>S"
begin

abbreviation (uni_zero)
  uni_zero :: "'b set"  ("\<bbbA>\<^sub>0\<^sub>I")
  where "\<bbbA>\<^sub>0\<^sub>I \<equiv> UNI 0\<^sup>I"

abbreviation (imp_zero)
  imp_zero :: "['b, 'b] \<Rightarrow> 'b"  ("((_)/ \<rightarrow>\<^sup>0\<^sup>I / (_))" [61,61] 60)
  where "x \<rightarrow>\<^sup>0\<^sup>I y \<equiv> IMP 0\<^sup>I x y"

end

context bl_chain
begin

subsection\<open>First element of @{term I}\<close>

definition zeroI :: "'a set" ("0\<^sup>I")
  where "0\<^sup>I = \<pi> 0\<^sup>A"

lemma I_zero_closed: "0\<^sup>I \<in> I"
  using index_set_def zeroI_def zero_closed by auto

lemma I_has_first_element:
  assumes "i \<in> I" "i \<noteq> 0\<^sup>I"
  shows "0\<^sup>I <\<^sup>I i"
proof -
  have "x \<le>\<^sup>A y" if "i <\<^sup>I 0\<^sup>I" "x \<in> i" "y \<in> 0\<^sup>I" for x y
    using I_zero_closed assms(1) index_order_strict_def that by fastforce
  then
  have "x \<le>\<^sup>A 0\<^sup>A" if "i <\<^sup>I 0\<^sup>I" "x \<in> i" for x
    using classes_not_empty zeroI_def zero_closed that by simp
  moreover
  have "0\<^sup>A \<le>\<^sup>A x" if "x \<in> i" for x
    using assms(1) that in_mono indexes_subsets zero_first by meson
  ultimately
  have "x = 0\<^sup>A" if "i <\<^sup>I 0\<^sup>I" "x \<in> i" for x
    using assms(1) indexes_subsets ord_antisymm zero_closed that by blast
  moreover
  have "0\<^sup>A \<in> 0\<^sup>I"
    using classes_not_empty zeroI_def zero_closed by simp
  ultimately
  have "i \<inter> 0\<^sup>I \<noteq> \<emptyset>" if "i <\<^sup>I 0\<^sup>I"
    using assms(1) indexes_not_empty that by force
  moreover
  have "i <\<^sup>I 0\<^sup>I \<or> 0\<^sup>I <\<^sup>I i"
    using I_zero_closed assms trichotomy by auto
  ultimately
  show ?thesis
    using I_zero_closed assms(1) indexes_disjoint by auto
qed

subsection\<open>Main result for BL-chains\<close>

definition zeroS :: "'a" ("0\<^sup>S")
  where "0\<^sup>S = 0\<^sup>A"

abbreviation (uniA_zero)
  uniA_zero :: "'a set" ("(\<bbbA>\<^sub>0\<^sub>I)")
  where "\<bbbA>\<^sub>0\<^sub>I \<equiv> UNI\<^sub>A 0\<^sup>I"

abbreviation (impA_zero_xy)
  impA_zero_xy :: "['a, 'a] \<Rightarrow> 'a"  ("((_)/ \<rightarrow>\<^sup>0\<^sup>I / (_))" [61, 61] 60)
  where "x \<rightarrow>\<^sup>0\<^sup>I y \<equiv> IMP\<^sub>A 0\<^sup>I x y"

lemma tower_is_bounded:
  shows "bounded_tower_of_irr_hoops I (\<le>\<^sup>I) (<\<^sup>I) UNI\<^sub>A MUL\<^sub>A IMP\<^sub>A 1\<^sup>S 0\<^sup>I 0\<^sup>S"
proof
  show "0\<^sup>I \<in> I"
    using I_zero_closed by simp
next
  show "0\<^sup>I \<le>\<^sup>I i" if "i \<in> I" for i
    using I_has_first_element index_ord_reflex index_order_strict_def that by blast
next
  show "0\<^sup>S \<in> \<bbbA>\<^sub>0\<^sub>I"
    using classes_not_empty universes_def zeroI_def zeroS_def zero_closed by simp
next
  show "0\<^sup>S \<rightarrow>\<^sup>0\<^sup>I x = 1\<^sup>S" if "x \<in> \<bbbA>\<^sub>0\<^sub>I" for x
    using I_zero_closed universes_subsets hoop_order_def imp_map_def sum_one_def
          zeroS_def zero_first that
    by simp
qed

lemma ordinal_sum_is_bl_totally_ordered:
  shows "bl_chain A_SUM.sum_univ A_SUM.sum_mult A_SUM.sum_imp 1\<^sup>S 0\<^sup>S"
proof
  show "A_SUM.hoop_order x y \<or> A_SUM.hoop_order y x"
    if "x \<in> A_SUM.sum_univ" "y \<in> A_SUM.sum_univ" for x y
    using ordinal_sum_is_totally_ordered_hoop totally_ordered_hoop.total_order that
    by meson
next
  show "0\<^sup>S \<in> A_SUM.sum_univ"
    using zeroS_def zero_closed by simp
next
  show "A_SUM.hoop_order 0\<^sup>S x" if "x \<in> A_SUM.sum_univ" for x
    using A_SUM.hoop_order_def eq_imp hoop_order_def sum_one_def zeroS_def zero_closed
          zero_first that
    by simp
qed

theorem bl_chain_is_equal_to_ordinal_sum_of_bounded_tower_of_irr_hoops:
  shows eq_universe: "A = A_SUM.sum_univ"
  and eq_mult: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x *\<^sup>A y = A_SUM.sum_mult x y"
  and eq_imp: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<rightarrow>\<^sup>A y = A_SUM.sum_imp x y"
  and eq_zero: "0\<^sup>A = 0\<^sup>S"
  and eq_one: "1\<^sup>A = 1\<^sup>S"
proof
  show "A \<subseteq> A_SUM.sum_univ"
    by auto
next
  show "A_SUM.sum_univ \<subseteq> A"
    by auto
next
  show "x *\<^sup>A y = A_SUM.sum_mult x y" if "x \<in> A" "y \<in> A" for x y
    using eq_mult that by blast
next
  show "x \<rightarrow>\<^sup>A y = A_SUM.sum_imp x y" if "x \<in> A" "y \<in> A" for x y
    using eq_imp that by blast
next
  show "0\<^sup>A = 0\<^sup>S"
    using zeroS_def by simp
next
  show "1\<^sup>A = 1\<^sup>S"
    using sum_one_def by simp
qed

end

subsection\<open>Converse of main result for BL-chains\<close>

context bounded_tower_of_irr_hoops
begin

text\<open>We show that the converse of the main result holds if @{term "0\<^sup>S \<noteq> 1\<^sup>S"}. If @{term "0\<^sup>S = 1\<^sup>S"}
then the converse may not be true. For example, take a trivial hoop @{text A} and an arbitrary
not bounded Wajsberg hoop @{text B} such that @{text "A \<inter> B = {1}"}. The ordinal sum of both hoops is equal to
@{text B} and therefore not bounded.\<close>

proposition ordinal_sum_of_bounded_tower_of_irr_hoops_is_bl_chain:
  assumes "0\<^sup>S \<noteq> 1\<^sup>S" 
  shows "bl_chain S (*\<^sup>S) (\<rightarrow>\<^sup>S) 1\<^sup>S 0\<^sup>S"
proof
  show "hoop_order a b \<or> hoop_order b a" if "a \<in> S" "b \<in> S" for a b
  proof -
    from that
    consider (1) "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "floor a = floor b"
      | (2) "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "floor a <\<^sup>I floor b \<or> floor b <\<^sup>I floor a"
      | (3) "a = 1\<^sup>S \<or> b = 1\<^sup>S"
      using floor.cases floor_prop trichotomy by metis
    then
    show ?thesis
    proof(cases)
      case 1
      then
      have "a \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a \<and> b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
        using "1" floor_prop by metis
      moreover
      have "totally_ordered_hoop (\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a) (*\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a) (\<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a) 1\<^sup>S"
        using "1"(1) family_of_irr_hoops totally_ordered_irreducible_hoop.axioms(1)
              floor_prop
        by meson
      ultimately
      have "a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b = 1\<^sup>S \<or> b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a = 1\<^sup>S"
        using hoop.hoop_order_def totally_ordered_hoop.total_order
              totally_ordered_hoop_def
        by meson
      moreover
      have "a \<rightarrow>\<^sup>S b = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b \<and> b \<rightarrow>\<^sup>S a = b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a"
        using "1" by auto
      ultimately
      show ?thesis
        using hoop_order_def by force
    next
      case 2
      then
      show ?thesis
        using sum_imp.simps(2) hoop_order_def by blast
    next
      case 3
      then
      show ?thesis
        using that ord_top by auto
    qed
  qed
next
  show "0\<^sup>S \<in> S"
    using first_zero_closed I_zero_closed sum_subsets by auto
next
  show "hoop_order 0\<^sup>S a" if "a \<in> S" for a 
  proof -
    have zero_dom: "0\<^sup>S \<in> \<bbbA>\<^sub>0\<^sub>I \<and> 0\<^sup>S \<in> S-{1\<^sup>S}"
      using I_zero_closed sum_subsets assms first_zero_closed by blast
    moreover
    have "floor 0\<^sup>S \<le>\<^sup>I floor x" if "0\<^sup>S \<in> S-{1\<^sup>S}" "x \<in> S-{1\<^sup>S}" for x
      using I_zero_closed floor_prop floor_unique that(2) zero_dom zero_first
      by metis
    ultimately
    have "floor 0\<^sup>S \<le>\<^sup>I floor x" if "x \<in> S-{1\<^sup>S}" for x
      using that by blast
    then
    consider (1) "0\<^sup>S \<in> S-{1\<^sup>S}" "a \<in> S-{1\<^sup>S}" "floor 0\<^sup>S = floor a"
      | (2) "0\<^sup>S \<in> S-{1\<^sup>S}" "a \<in> S-{1\<^sup>S}" "floor 0\<^sup>S <\<^sup>I floor a"
      | (3) "a = 1\<^sup>S"
      using \<open>a \<in> S\<close> floor.cases floor_prop strict_order_equiv_not_converse 
            trichotomy zero_dom
      by metis
    then
    show "hoop_order 0\<^sup>S a"
    proof(cases)
      case 1
      then
      have "0\<^sup>S \<in> \<bbbA>\<^sub>0\<^sub>I \<and> a \<in> \<bbbA>\<^sub>0\<^sub>I"
        using I_zero_closed first_zero_closed floor_prop floor_unique by metis
      then
      have "0\<^sup>S \<rightarrow>\<^sup>S a = 0\<^sup>S \<rightarrow>\<^sup>0\<^sup>I a \<and> 0\<^sup>S \<rightarrow>\<^sup>0\<^sup>I a = 1\<^sup>S"
        using "1" I_zero_closed sum_imp.simps(1) first_bounded floor_prop floor_unique
        by metis
      then
      show ?thesis
        using hoop_order_def by blast
    next
      case 2
      then
      show ?thesis
        using sum_imp.simps(2,5) hoop_order_def by meson
    next
      case 3
      then
      show ?thesis
        using ord_top zero_dom by auto
    qed
  qed
qed

end

end