(*  Title:      Composition Series
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory CompositionSeries
imports
  "SimpleGroups"
  "MaximalNormalSubgroups"
begin

section {* Normal series and Composition series *}

subsection {* Preliminaries *}

text {* A subgroup which is unique in cardinality is normal: *}

lemma (in group) unique_sizes_subgrp_normal:
  assumes fin:"finite (carrier G)"
  assumes "\<exists>!Q. Q \<in> subgroups_of_size q"
  shows "(THE Q. Q \<in> subgroups_of_size q) \<lhd> G"
proof -
  from assms obtain Q where "Q \<in> subgroups_of_size q" by auto
  def Q \<equiv> "THE Q. Q \<in> subgroups_of_size q"
  with assms have Qsize:"Q \<in> subgroups_of_size q" using theI by metis
  hence QG:"subgroup Q G" and cardQ:"card Q = q" unfolding subgroups_of_size_def by auto
  from QG have "Q \<lhd> G" apply(rule normalI)
  proof
    fix g
    assume g:"g \<in> carrier G"
    hence invg:"inv g \<in> carrier G" by (metis inv_closed)
    with fin Qsize have "conjugation_action q (inv g) Q \<in> subgroups_of_size q" by (metis conjugation_is_size_invariant)
    with g Qsize have "(inv g) <# (Q #> inv (inv g)) \<in> subgroups_of_size q" unfolding conjugation_action_def by auto
    with invg g have "inv g <# (Q #> g) = Q" by (metis Qsize assms(2) inv_inv)
    with QG QG g show "Q #> g = g <# Q" by (rule conj_wo_inv)
  qed
  with Q_def show ?thesis by simp
qed

text {* A group whose order is the product of two distinct
primes $p$ and $q$ where $p < q$ has a unique subgroup of size $q$: *}

lemma (in group) pq_order_unique_subgrp:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "\<exists>!Q. Q \<in> (subgroups_of_size q)"
proof -
  from primep primeq pq have nqdvdp:"\<not> (q dvd p)" by (metis less_not_refl3 prime_def)
  def calM \<equiv> "{s. s \<subseteq> carrier G \<and> card s = q ^ 1}"
  def RelM \<equiv> "{(N1, N2). N1 \<in> calM \<and> N2 \<in> calM \<and> (\<exists>g\<in>carrier G. N1 = N2 #> g)}"
  interpret syl: snd_sylow G q 1 p calM RelM
    unfolding snd_sylow_def sylow_def snd_sylow_axioms_def sylow_axioms_def
    using is_group primeq orderG finite nqdvdp calM_def RelM_def by auto
  obtain Q where Q:"Q \<in> subgroups_of_size q" by (metis (lifting, mono_tags) mem_Collect_eq power_one_right subgroups_of_size_def syl.sylow_thm)
  thus ?thesis 
  proof (rule ex1I)
     fix P
     assume P:"P \<in> subgroups_of_size q"
     have "card (subgroups_of_size q) mod q = 1" by (metis power_one_right syl.p_sylow_mod_p)     
     moreover have "card (subgroups_of_size q) dvd p" by (metis power_one_right syl.num_sylow_dvd_remainder)
     ultimately have "card (subgroups_of_size q) = 1" using pq primep by (metis Divides.mod_less prime_def)
     with Q P show "P = Q" by (auto simp:card_Suc_eq)
  qed
qed

text {* ... And this unique subgroup is normal. *}

corollary (in group) pq_order_subgrp_normal:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "(THE Q. Q \<in> subgroups_of_size q) \<lhd> G"
using assms by (metis pq_order_unique_subgrp unique_sizes_subgrp_normal)

text {* The trivial subgroup is normal in every group. *}

lemma (in group) trivial_subgroup_is_normal:
  shows "{\<one>} \<lhd> G"
unfolding normal_def normal_axioms_def r_coset_def l_coset_def by (auto intro: normalI subgroupI simp: is_group)

subsection {* Normal Series *}

text {* We define a normal series as a locale which fixes one group
@{term G} and a list @{term \<GG>} of subsets of @{term G}'s carrier. This list
must begin with the trivial subgroup, end with the carrier of the group itself
and each of the list items must be a normal subgroup of its successor. *}

locale normal_series = group +
  fixes \<GG>
  assumes notempty:"\<GG> \<noteq> []"
  assumes hd:"hd \<GG> = {\<one>}"
  assumes last:"last \<GG> = carrier G"
  assumes normal:"\<And>i. i + 1 < length \<GG> \<Longrightarrow> (\<GG> ! i) \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>"

lemma (in normal_series) is_normal_series: "normal_series G \<GG>" by (rule normal_series_axioms)

text {* For every group there is a "trivial" normal series consisting
only of the group itself and its trivial subgroup. *}

lemma (in group) trivial_normal_series:
  shows "normal_series G [{\<one>}, carrier G]"
unfolding normal_series_def normal_series_axioms_def
using is_group trivial_subgroup_is_normal by auto

text {* We can also show that the normal series presented above is the only such with
a length of two: *}

lemma (in normal_series) length_two_unique:
  assumes "length \<GG> = 2"
  shows "\<GG> = [{\<one>}, carrier G]"
proof(rule nth_equalityI)
  from assms show "length \<GG> = length [{\<one>}, carrier G]" by auto
next
  show "\<forall>i<length \<GG>. \<GG> ! i = [{\<one>}, carrier G] ! i"
  proof(rule allI, rule impI)
    fix i
    assume i:"i < length \<GG>"
    with assms have "i = 0 \<or> i = 1" by auto
    thus "\<GG> ! i = [{\<one>}, carrier G] ! i"
    proof(rule disjE)
      assume i:"i = 0"
      hence "\<GG> ! i = hd \<GG>" by (metis hd_conv_nth notempty)
      thus "\<GG> ! i = [{\<one>}, carrier G] ! i" using hd i by simp
    next
      assume i:"i = 1"
      with assms have "\<GG> ! i = last \<GG>" by (metis diff_add_inverse last_conv_nth nat_1_add_1 notempty)
      thus "\<GG> ! i = [{\<one>}, carrier G] ! i" using last i by simp
    qed
  qed
qed

text {* We can construct new normal series by expanding existing ones: If we
append the carrier of a group @{term G} to a normal series for a normal subgroup
@{term "H \<lhd> G"} we receive a normal series for @{term G}. *}

lemma (in group) normal_series_extend:
  assumes normal:"normal_series (G\<lparr>carrier := H\<rparr>) \<HH>"
  assumes HG:"H \<lhd> G"
  shows "normal_series G (\<HH> @ [carrier G])"
proof -
  from normal interpret normalH: normal_series "(G\<lparr>carrier := H\<rparr>)" \<HH>.
  from normalH.hd have "hd \<HH> = {\<one>}" by simp
  with normalH.notempty have hdTriv:"hd (\<HH> @ [carrier G]) = {\<one>}" by (metis hd_append2)
  show ?thesis unfolding normal_series_def normal_series_axioms_def using is_group
  proof auto
    fix x
    assume "x \<in> hd (\<HH> @ [carrier G])"
    with hdTriv show "x = \<one>" by simp
  next
    from hdTriv show  "\<one> \<in> hd (\<HH> @ [carrier G])" by simp
  next
    fix i
    assume i:"i < length \<HH>"
    show "(\<HH> @ [carrier G]) ! i \<lhd> G\<lparr>carrier := (\<HH> @ [carrier G]) ! Suc i\<rparr>"
    proof (cases "i + 1 < length \<HH>")
      case True
      with normalH.normal have "\<HH> ! i \<lhd> G\<lparr>carrier := \<HH> ! (i + 1)\<rparr>" by auto
      with i have "(\<HH> @ [carrier G]) ! i \<lhd> G\<lparr>carrier := \<HH> ! (i + 1)\<rparr>" using nth_append by metis
      with True show "(\<HH> @ [carrier G]) ! i \<lhd> G\<lparr>carrier := (\<HH> @ [carrier G]) ! (Suc i)\<rparr>" using nth_append Suc_eq_plus1 by metis
    next
      case False
      with i have i2:"i + 1 = length \<HH>" by simp
      from i have "(\<HH> @ [carrier G]) ! i = \<HH> ! i" by (metis nth_append)
      also from i2 normalH.notempty have "... = last \<HH>" by (metis add_diff_cancel_right' last_conv_nth)
      also from normalH.last have "... = H" by simp
      finally have "(\<HH> @ [carrier G]) ! i = H".
      moreover from i2 have "(\<HH> @ [carrier G]) ! (i + 1) = carrier G" by (metis nth_append_length)
      ultimately show ?thesis using HG by auto
    qed
  qed
qed

text {* All entries of a normal series for $G$ are subgroups of $G$. *}

lemma (in normal_series) normal_series_subgroups:
  shows "i < length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G"
proof -
  have "i + 1 < length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G"
  proof (induction "length \<GG> - (i + 2)" arbitrary: i)
    case 0
    hence i:"i + 2 = length \<GG>" using assms by simp
    hence ii:"i + 1 = length \<GG> - 1" using assms by force
    from i normal have "\<GG> ! i \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>" by auto
    with ii last notempty show "subgroup (\<GG> ! i) G" using last_conv_nth normal_imp_subgroup by fastforce
  next
    case (Suc k)
    from Suc(3)  normal have i:"subgroup (\<GG> ! i) (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)" using normal_imp_subgroup by auto
    from Suc(2) have k:"k = length \<GG> - ((i + 1) + 2)" by arith
    with Suc have "subgroup (\<GG> ! (i + 1)) G" by simp
    with i show "subgroup (\<GG> ! i) G" by (metis is_group subgroup.subgroup_of_subgroup)
  qed
  moreover have "i + 1 = length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G"
    using last notempty last_conv_nth by (metis add_diff_cancel_right' subgroup_self)
  ultimately show "i < length \<GG> \<Longrightarrow> subgroup (\<GG> ! i) G" by force
qed

text {* The second to last entry of a normal series is a normal subgroup of G. *}

lemma (in normal_series) normal_series_snd_to_last:
  shows "\<GG> ! (length \<GG> - 2) \<lhd> G"
proof (cases "2 \<le> length \<GG>")
  case False
  with notempty have length:"length \<GG> = 1" by (metis Suc_eq_plus1 leI length_0_conv less_2_cases plus_nat.add_0)
  with hd have "\<GG> ! (length \<GG> - 2) = {\<one>}" using hd_conv_nth notempty by auto
  with length show ?thesis by (metis trivial_subgroup_is_normal)
next
  case True
  hence "(length \<GG> - 2) + 1 < length \<GG>" by arith
  with normal last have "\<GG> ! (length \<GG> - 2) \<lhd> G\<lparr>carrier := \<GG> ! ((length \<GG> - 2) + 1)\<rparr>" by auto
  have "1 + (1 + (length \<GG> - (1 + 1))) = length \<GG>"
    using True le_add_diff_inverse by presburger
  then have "\<GG> ! (length \<GG> - 2) \<lhd> G\<lparr>carrier :=  \<GG> ! (length \<GG> - 1)\<rparr>"
    by (metis `\<GG> ! (length \<GG> - 2) \<lhd> G \<lparr>carrier := \<GG> ! (length \<GG> - 2 + 1)\<rparr>` add.commute add_diff_cancel_left' one_add_one)
  with notempty last show ?thesis using last_conv_nth by force
qed

text {* Just like the expansion of normal series, every prefix of a normal series is again a normal series. *}

lemma (in normal_series) normal_series_prefix_closed:
  assumes "i \<le> length \<GG>" and "0 < i"
  shows "normal_series (G\<lparr>carrier := \<GG> ! (i - 1)\<rparr>) (take i \<GG>)"
unfolding normal_series_def normal_series_axioms_def
using assms
apply (auto del:equalityI)
 apply (metis diff_Suc_Suc diff_is_0_eq' gr_implies_not0 minus_nat.diff_0 normal_series_subgroups not0_implies_Suc not_less_eq subgroup_imp_group zero_less_diff)
proof -
  from assms have "hd (take i \<GG>) = (take i \<GG>) ! 0" by (metis gr_implies_not0 hd_conv_nth notempty take_eq_Nil)
  also from assms have "... = \<GG> ! 0" by (metis nth_take)
  also from hd have "... = {\<one>}" by (metis hd_conv_nth notempty)
  finally show "hd (take i \<GG>) = {\<one>}".
next
  from assms have "last (take i \<GG>) = (take i \<GG>) ! (length (take i \<GG>) - 1)" by (metis last_conv_nth neq0_conv notempty take_eq_Nil)
  also from assms have "... = (take i \<GG>) ! (i - 1)" by (metis length_take min.absorb2)
  also from assms have "... = \<GG> ! (i - 1)" by (metis diff_less nth_take zero_less_one)
  finally show "last (take i \<GG>) = \<GG> ! (i - Suc 0)" by simp
next
  fix j
  assume j:"Suc j < i"
  hence "j + 1 < length \<GG>" using assms by simp
  with normal show "\<GG> ! j \<lhd> G\<lparr>carrier := \<GG> ! (Suc j)\<rparr>" by auto
qed

text {* If a group's order is the product of two distinct primes @{term p} and @{term q}, where
@{term "p < q"}, we can construct a normal series using the only subgroup of size  @{term q}. *}

lemma (in group) pq_order_normal_series:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "normal_series G [{\<one>}, (THE H. H \<in> subgroups_of_size q), carrier G]"
proof -
  def H \<equiv> "(THE H. H \<in> subgroups_of_size q)"
  with assms have HG:"H \<lhd> G" by (metis pq_order_subgrp_normal)
  then interpret groupH: group "G\<lparr>carrier := H\<rparr>" unfolding normal_def by (metis subgroup_imp_group)
  have "normal_series (G\<lparr>carrier := H\<rparr>) [{\<one>}, H]"  using groupH.trivial_normal_series by auto
  with HG show ?thesis unfolding H_def by (metis append_Cons append_Nil normal_series_extend)
qed

text {* The following defines the list of all quotient groups of the normal series: *}

definition (in normal_series) quotients
  where "quotients = map (\<lambda>i. G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i) [0..<((length \<GG>) - 1)]"

text {* The list of quotient groups has one less entry than the series itself: *}

lemma (in normal_series) quotients_length:
  shows "length quotients + 1 = length \<GG>"
proof -
  have "length quotients + 1 = length [0..<((length \<GG>) - 1)] + 1" unfolding quotients_def by simp
  also have "... = (length \<GG> - 1) + 1" by (metis diff_zero length_upt)
  also with notempty have "... = length \<GG>"
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma (in normal_series) last_quotient:
  assumes "length \<GG> > 1"
  shows "last quotients = G Mod \<GG> ! (length \<GG> - 1 - 1)"
proof -
  from assms have lsimp:"length \<GG> - 1 - 1 + 1 = length \<GG> - 1" by auto
  from assms have "quotients \<noteq> []" unfolding quotients_def by auto
  hence "last quotients = quotients ! (length quotients - 1)" by (metis last_conv_nth)
  also have "\<dots> = quotients ! (length \<GG> - 1 - 1)" by (metis add_diff_cancel_left' quotients_length add.commute)
  also have "\<dots> = G\<lparr>carrier := \<GG> ! ((length \<GG> - 1 - 1) + 1)\<rparr> Mod \<GG> ! (length \<GG> - 1 - 1)"
    unfolding quotients_def using assms by auto
  also have "\<dots> = G\<lparr>carrier := \<GG> ! (length \<GG> - 1)\<rparr> Mod \<GG> ! (length \<GG> - 1 - 1)" using lsimp by simp
  also have "\<dots> = G Mod \<GG> ! (length \<GG> - 1 - 1)" using last last_conv_nth notempty by force
  finally show ?thesis .
qed

text {* The next lemma transports the constituting properties of a normal series
along an isomorphism of groups. *}

lemma (in normal_series) normal_series_iso:
  assumes H:"group H"
  assumes iso:"\<Psi> \<in> G \<cong> H"
  shows "normal_series H (map (image \<Psi>) \<GG>)"
apply (simp add: normal_series_def normal_series_axioms_def)
using H notempty apply simp
proof (rule conjI)
  from H is_group iso have group_hom:"group_hom G H \<Psi>" unfolding group_hom_def group_hom_axioms_def iso_def by auto
  have "hd (map (image \<Psi>) \<GG>) = \<Psi> ` {\<one>}" by (metis hd_map hd notempty)
  also have "\<dots> = {\<Psi> \<one>}" by (metis image_empty image_insert)
  also have "\<dots> = {\<one>\<^bsub>H\<^esub>}" using group_hom group_hom.hom_one by auto
  finally show "hd (map (op ` \<Psi>) \<GG>) = {\<one>\<^bsub>H\<^esub>}".
next
  show "last (map (op ` \<Psi>) \<GG>) = carrier H \<and> (\<forall>i. Suc i < length \<GG> \<longrightarrow> \<Psi> ` \<GG> ! i \<lhd> H\<lparr>carrier := \<Psi> ` \<GG> ! Suc i\<rparr>)"
  proof (auto del: equalityI)
    have "last (map (op ` \<Psi>) \<GG>) = \<Psi> ` (carrier G)" using last last_map notempty by metis
    also have "\<dots> = carrier H" using iso unfolding iso_def bij_betw_def by simp
    finally show "last (map (op ` \<Psi>) \<GG>) = carrier H".
  next
    fix i
    assume i:"Suc i < length \<GG>"
    hence norm:"\<GG> ! i \<lhd> G\<lparr>carrier := \<GG> ! Suc i\<rparr>" using normal by simp
    moreover have "restrict \<Psi> (\<GG> ! Suc i) \<in> (G\<lparr>carrier := \<GG> ! Suc i\<rparr>) \<cong> H\<lparr>carrier := \<Psi> ` \<GG> ! Suc i\<rparr>"
      by (metis H i is_group iso iso_restrict normal_series_subgroups)
    moreover have "group (G\<lparr>carrier := \<GG> ! Suc i\<rparr>)" by (metis i normal_series_subgroups subgroup_imp_group)
    moreover hence "subgroup (\<GG> ! Suc i) G" by (metis i normal_series_subgroups)
    hence "subgroup (\<Psi> ` \<GG> ! Suc i) H" by (metis H is_group iso iso_subgroup)
    hence "group (H\<lparr>carrier := \<Psi> ` \<GG> ! Suc i\<rparr>)" by (metis H subgroup.subgroup_is_group)
    ultimately have "restrict \<Psi> (\<GG> ! Suc i) ` \<GG> ! i \<lhd> H\<lparr>carrier := \<Psi> ` \<GG> ! Suc i\<rparr>"
      using is_group H iso_normal_subgroup by auto
    moreover from norm have "\<GG> ! i \<subseteq> \<GG> ! Suc i" unfolding normal_def subgroup_def by auto
    hence "{y. \<exists>x\<in>\<GG> ! i. y = (if x \<in> \<GG> ! Suc i then \<Psi> x else undefined)} = {y. \<exists>x\<in>\<GG> ! i. y = \<Psi> x}" by auto
    ultimately show "\<Psi> ` \<GG> ! i \<lhd> H\<lparr>carrier := \<Psi> ` \<GG> ! Suc i\<rparr>" unfolding restrict_def image_def by auto
  qed
qed

subsection {* Composition Series *}

text {* A composition series is a normal series where all consecutive factor groups are simple: *}

locale composition_series = normal_series +
  assumes simplefact:"\<And>i. i + 1 <  length \<GG> \<Longrightarrow> simple_group (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)"

lemma (in composition_series) is_composition_series:
  shows "composition_series G \<GG>"
by (rule composition_series_axioms)

text {* A composition series for a group $G$ has length one if and only if $G$ is the trivial group. *}

lemma (in composition_series) composition_series_length_one:
  shows "(length \<GG> = 1) = (\<GG> = [{\<one>}])"
proof
  assume "length \<GG> = 1"
  with hd have "length \<GG> = length [{\<one>}] \<and> (\<forall>i < length \<GG>. \<GG> ! i = [{\<one>}] ! i)" using hd_conv_nth notempty by force
  thus "\<GG> = [{\<one>}]" using list_eq_iff_nth_eq by blast
next
  assume "\<GG> = [{\<one>}]"
  thus "length \<GG> = 1" by simp
qed

lemma (in composition_series) composition_series_triv_group:
  shows "(carrier G = {\<one>}) = (\<GG> = [{\<one>}])"
proof
  assume G:"carrier G = {\<one>}"
  have "length \<GG> = 1"
  proof (rule ccontr)
    assume "length \<GG> \<noteq> 1"
    with notempty have length:"length \<GG> \<ge> 2" by (metis Suc_eq_plus1 length_0_conv less_2_cases not_less plus_nat.add_0)
    with simplefact hd hd_conv_nth notempty have "simple_group (G\<lparr>carrier := \<GG> ! 1\<rparr> Mod {\<one>})" by force
    moreover have SG:"subgroup (\<GG> ! 1) G" using length normal_series_subgroups by auto
    hence "group (G\<lparr>carrier := \<GG> ! 1\<rparr>)" by (metis subgroup_imp_group)
    ultimately have  "simple_group (G\<lparr>carrier := \<GG> ! 1\<rparr>)" using group.trivial_factor_iso simple_group.iso_simple by fastforce
    moreover from SG G have "carrier (G\<lparr>carrier := \<GG> ! 1\<rparr>) = {\<one>}" unfolding subgroup_def by auto
    ultimately show False using simple_group.simple_not_triv by force
  qed
  thus "\<GG> = [{\<one>}]" by (metis composition_series_length_one)
next
  assume "\<GG> = [{\<one>}]"
  with last show "carrier G = {\<one>}" by auto
qed

text {* The inner elements of a composition series may not consist of the trivial subgroup or the
group itself. *}

lemma (in composition_series) inner_elements_not_triv:
  assumes "i + 1 < length \<GG>"
  assumes "i > 0"
  shows "\<GG> ! i \<noteq> {\<one>}"
proof
  from assms have "(i - 1) + 1 < length \<GG>" by simp
  hence simple:"simple_group (G\<lparr>carrier := \<GG> ! ((i - 1) + 1)\<rparr> Mod \<GG> ! (i - 1))" using simplefact by auto
  assume i:"\<GG> ! i = {\<one>}"
  moreover from assms have "(i - 1) + 1 = i" by auto
  ultimately have "G\<lparr>carrier := \<GG> ! ((i - 1) + 1)\<rparr> Mod \<GG> ! (i - 1) = G\<lparr>carrier := {\<one>}\<rparr> Mod \<GG> ! (i - 1)" using i by auto
  hence "order (G\<lparr>carrier := \<GG> ! ((i - 1) + 1)\<rparr> Mod \<GG> ! (i - 1)) = 1" unfolding FactGroup_def order_def RCOSETS_def by force
  thus "False" using i simple unfolding simple_group_def simple_group_axioms_def by auto
qed

text {* A composition series of a simple group always is its trivial one. *}

lemma (in composition_series) composition_series_simple_group:
  shows "(simple_group G) = (\<GG> = [{\<one>}, carrier G])"
proof
  assume "\<GG> = [{\<one>}, carrier G]"
  with simplefact have "simple_group (G Mod {\<one>})" by auto
  moreover have "the_elem \<in> (G Mod {\<one>}) \<cong> G" by (rule trivial_factor_iso)
  ultimately show "simple_group G" by (metis is_group simple_group.iso_simple)
next
  assume simple:"simple_group G"
  have "length \<GG> > 1"
  proof (rule ccontr)
    assume "\<not> 1 < length \<GG>"
    hence "length \<GG> = 1" by (metis add.commute nat_less_cases not_add_less1 quotients_length) 
    hence "carrier G = {\<one>}" using hd last by (metis composition_series_length_one composition_series_triv_group)
    hence "order G = 1" unfolding order_def by auto
    with simple show "False" unfolding simple_group_def simple_group_axioms_def by auto
  qed
  moreover have "length \<GG> \<le> 2"
  proof (rule ccontr)
    def k \<equiv> "length \<GG> - 2"
    assume "\<not> (length \<GG> \<le> 2)"
    hence gt2:"length \<GG> > 2" by simp
    hence ksmall:"k + 1 < length \<GG>" unfolding k_def by auto
    from gt2 have carrier:"\<GG> ! (k + 1) = carrier G" using notempty last last_conv_nth k_def
      by (metis Nat.add_diff_assoc Nat.diff_cancel `\<not> length \<GG> \<le> 2` add.commute nat_le_linear one_add_one)
    from normal ksmall have "\<GG> ! k \<lhd> G\<lparr> carrier := \<GG> ! (k + 1)\<rparr>" by simp
    from simplefact ksmall have simplek:"simple_group (G\<lparr>carrier := \<GG> ! (k + 1)\<rparr> Mod \<GG> ! k)" by simp
    from simplefact ksmall have simplek':"simple_group (G\<lparr>carrier := \<GG> ! ((k - 1) + 1)\<rparr> Mod \<GG> ! (k - 1))" by auto
    have "\<GG> ! k \<lhd> G" using carrier k_def gt2 normal ksmall by force
    with simple have "(\<GG> ! k) = carrier G \<or> (\<GG> ! k) = {\<one>}" unfolding simple_group_def simple_group_axioms_def by simp
    thus "False"
    proof (rule disjE)
      assume "\<GG> ! k = carrier G"
      hence "G\<lparr>carrier := \<GG> ! (k + 1)\<rparr> Mod \<GG> ! k = G Mod (carrier G)" using carrier by auto
      with simplek self_factor_not_simple show "False" by auto
    next
      assume "\<GG> ! k = {\<one>}"
      with ksmall k_def gt2 show "False" using inner_elements_not_triv by auto
    qed
  qed
  ultimately have "length \<GG> = 2" by simp
  thus "\<GG> = [{\<one>}, carrier G]" by (rule length_two_unique)
qed

text {* Two consecutive elements in a composition series are distinct. *}

lemma (in composition_series) entries_distinct:
  assumes finite:"finite (carrier G)"
  assumes i:"i + 1 < length \<GG>"
  shows "\<GG> ! i \<noteq> \<GG> ! (i + 1)"
proof
  from finite have "finite  (\<GG> ! (i + 1))" 
    using i normal_series_subgroups subgroup_imp_subset rev_finite_subset by metis
  hence fin:"finite (carrier (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>))" by auto
  from i have norm:"\<GG> ! i \<lhd> (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)" by (rule normal)
  assume "\<GG> ! i = \<GG> ! (i + 1)"
  hence "\<GG> ! i = carrier (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)" by auto
  hence "carrier ((G\<lparr>carrier := (\<GG> ! (i + 1))\<rparr>) Mod (\<GG> ! i)) = {\<one>\<^bsub>(G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>) Mod \<GG> ! i\<^esub>}"
    using norm fin normal.fact_group_trivial_iff by metis
  hence "\<not> simple_group ((G\<lparr>carrier := (\<GG> ! (i + 1))\<rparr>) Mod (\<GG> ! i))" by (metis simple_group.simple_not_triv)
  thus False by (metis i simplefact)
qed

text {* The normal series for groups of order @{term "p * q"} is even a composition series: *}

lemma (in group) pq_order_composition_series:
  assumes finite:"finite (carrier G)"
  assumes orderG:"order G = q * p"
  assumes primep:"prime p" and primeq:"prime q" and pq:"p < q"
  shows "composition_series G [{\<one>}, (THE H. H \<in> subgroups_of_size q), carrier G]"
unfolding composition_series_def composition_series_axioms_def
apply(auto)
using assms apply(rule pq_order_normal_series)
proof -
  def H \<equiv> "THE H. H \<in> subgroups_of_size q"
  from assms have exi:"\<exists>!Q. Q \<in> (subgroups_of_size q)" by (auto simp: pq_order_unique_subgrp)
  hence Hsize:"H \<in> subgroups_of_size q" unfolding H_def using theI' by metis
  hence HsubG:"subgroup H G" unfolding subgroups_of_size_def by auto
  then interpret Hgroup: group "G\<lparr>carrier := H\<rparr>" by (metis subgroup_imp_group)
  fix i
  assume "i < Suc (Suc 0)"
  hence "i = 0 \<or> i = 1" by auto
  thus "simple_group (G\<lparr>carrier := [H, carrier G] ! i\<rparr> Mod [{\<one>}, H, carrier G] ! i)"
  proof
    assume i:"i = 0"
    from Hsize have orderH:"order (G\<lparr>carrier := H\<rparr>) = q" unfolding subgroups_of_size_def order_def by simp
    hence "order (G\<lparr>carrier := H\<rparr> Mod {\<one>}) = q" unfolding FactGroup_def using card_rcosets_triv order_def
      by (metis Hgroup.card_rcosets_triv HsubG finite monoid.cases_scheme monoid.select_convs(2) partial_object.select_convs(1) partial_object.update_convs(1) subgroup_finite)
    have "normal {\<one>} (G\<lparr>carrier := H\<rparr>)" by (metis Hgroup.is_group Hgroup.normal_inv_iff HsubG group.trivial_subgroup_is_normal is_group singleton_iff subgroup.one_closed subgroup.subgroup_of_subgroup)
    hence "group (G\<lparr>carrier := H\<rparr> Mod {\<one>})" by (metis normal.factorgroup_is_group)
    with orderH primeq have "simple_group (G\<lparr>carrier := H\<rparr> Mod {\<one>})" by (metis `order (G\<lparr>carrier := H\<rparr> Mod {\<one>}) = q` group.prime_order_simple)
    with i show ?thesis by simp
  next
    assume i:"i = 1"
    from assms exi have "H \<lhd> G" unfolding H_def by (metis pq_order_subgrp_normal)
    hence groupGH:"group (G Mod H)" by (metis normal.factorgroup_is_group)
    from primeq have "q \<noteq> 0" by (metis zero_not_prime_nat)
    from HsubG finite orderG have "card (rcosets H) * card H = q * p" unfolding subgroups_of_size_def using lagrange by simp
    with Hsize have "card (rcosets H) * q = q * p" unfolding subgroups_of_size_def by simp
    with `q \<noteq> 0` have "card (rcosets H) = p" by auto
    hence "order (G Mod H) = p" unfolding order_def FactGroup_def by auto
    with groupGH primep have "simple_group (G Mod H)" by (metis group.prime_order_simple)
    with i show ?thesis by auto
  qed
qed

text {* Prefixes of composition series are also composition series. *}

lemma (in composition_series) composition_series_prefix_closed:
  assumes "i \<le> length \<GG>" and "0 < i"
  shows "composition_series (G\<lparr>carrier := \<GG> ! (i - 1)\<rparr>) (take i \<GG>)"
unfolding composition_series_def composition_series_axioms_def
proof auto
  from assms show "normal_series (G\<lparr>carrier := \<GG> ! (i - Suc 0)\<rparr>) (take i \<GG>)" by (metis One_nat_def normal_series_prefix_closed)
next
  fix j
  assume j:"Suc j < length \<GG>" "Suc j < i"
  with simplefact show "simple_group (G\<lparr>carrier := \<GG> ! Suc j\<rparr> Mod \<GG> ! j)" by (metis Suc_eq_plus1)
qed

text {* The second element in a composition series is simple group. *}

lemma (in composition_series) composition_series_snd_simple:
  assumes "2 \<le> length \<GG>"
  shows "simple_group (G\<lparr>carrier := \<GG> ! 1\<rparr>)"
proof -
  from assms interpret compTake: composition_series "G\<lparr>carrier := \<GG> ! 1\<rparr>" "take 2 \<GG>" by (metis add_diff_cancel_right' composition_series_prefix_closed one_add_one zero_less_numeral)
  from assms have "length (take 2 \<GG>) = 2" by (metis add_diff_cancel_right' append_take_drop_id diff_diff_cancel length_append length_drop)
  hence "(take 2 \<GG>) = [{\<one>\<^bsub>(G\<lparr>carrier := \<GG> ! 1\<rparr>)\<^esub>}, carrier (G\<lparr>carrier := \<GG> ! 1\<rparr>)]" by (rule compTake.length_two_unique)
  thus ?thesis by (metis compTake.composition_series_simple_group)
qed

text {* As a stronger way to state the previous lemma: An entry of a composition series is 
  simple if and only if it is the second one. *}

lemma (in composition_series) composition_snd_simple_iff:
  assumes "i < length \<GG>"
  shows "(simple_group (G\<lparr>carrier :=  \<GG> ! i\<rparr>)) = (i = 1)"
proof
  assume simpi:"simple_group (G\<lparr>carrier := \<GG> ! i\<rparr>)"
  hence "\<GG> ! i \<noteq> {\<one>}" using simple_group.simple_not_triv by force
  hence "i \<noteq> 0" using hd hd_conv_nth notempty by auto
  then interpret compTake: composition_series "G\<lparr>carrier := \<GG> ! i\<rparr>" "take (Suc i) \<GG>"
    using assms composition_series_prefix_closed by (metis diff_Suc_1 less_eq_Suc_le zero_less_Suc)
  from simpi have "(take (Suc i) \<GG>) = [{\<one>\<^bsub>G\<lparr>carrier := \<GG> ! i\<rparr>\<^esub>}, carrier (G\<lparr>carrier := \<GG> ! i\<rparr>)]"
    by (metis compTake.composition_series_simple_group)
  hence "length (take (Suc i) \<GG>) = 2" by auto
  hence "min (length \<GG>) (Suc i) = 2" by (metis length_take)
  with assms have "Suc i = 2" by force
  thus "i = 1" by simp
next
  assume i:"i = 1"
  with assms have "2 \<le> length \<GG>" by simp
  with i show "simple_group (G\<lparr>carrier := \<GG> ! i\<rparr>)" by (metis composition_series_snd_simple)
qed

text {* The second to last entry of a normal series is not only a normal subgroup but
  actually even a \emph{maximal} normal subgroup. *}

lemma (in composition_series) snd_to_last_max_normal:
  assumes finite:"finite (carrier G)"
  assumes length:"length \<GG> > 1"
  shows "max_normal_subgroup (\<GG> ! (length \<GG> - 2)) G"
unfolding max_normal_subgroup_def max_normal_subgroup_axioms_def
proof (auto del: equalityI)
  show "\<GG> ! (length \<GG> - 2) \<lhd> G" by (rule normal_series_snd_to_last)
next 
  def G' \<equiv> "\<GG> ! (length \<GG> - 2)"
  from length have length21:"length \<GG> - 2 + 1 = length \<GG> - 1" by arith
  from length have "length \<GG> - 2 + 1 < length \<GG>" by arith
  with simplefact have "simple_group (G\<lparr>carrier := \<GG> ! ((length \<GG> - 2) + 1)\<rparr> Mod G')" unfolding G'_def by auto
  with length21 have simple_last:"simple_group (G Mod G')" using last notempty last_conv_nth by fastforce
  {
    assume snd_to_last_eq:"G' = carrier G"
    hence "carrier (G Mod G') = {\<one>\<^bsub>G Mod G'\<^esub>}"
    using normal_series_snd_to_last finite normal.fact_group_trivial_iff unfolding G'_def by metis
    with snd_to_last_eq have "\<not> simple_group (G Mod G')" by (metis self_factor_not_simple)
    with simple_last show False unfolding G'_def by auto
  }
  {
    have G'G:"G' \<lhd> G" unfolding G'_def by (rule normal_series_snd_to_last)
    fix J
    assume J:"J \<lhd> G" "J \<noteq> G'" "J \<noteq> carrier G" "G' \<subseteq> J"
    hence JG'GG':"rcosets\<^bsub>(G\<lparr>carrier := J\<rparr>)\<^esub> G' \<lhd> G Mod G'"  using normality_factorization normal_series_snd_to_last unfolding G'_def by auto
    from G'G J(1,4) have G'J:"G' \<lhd> (G\<lparr>carrier := J\<rparr>)" by (metis normal_imp_subgroup normal_restrict_supergroup)
    from finite J(1) have finJ:"finite J" by (auto simp: normal_imp_subgroup subgroup_finite)
    from JG'GG' simple_last have "rcosets\<^bsub>G\<lparr>carrier := J\<rparr>\<^esub> G' = {\<one>\<^bsub>G Mod G'\<^esub>} \<or> rcosets\<^bsub>G\<lparr>carrier := J\<rparr>\<^esub> G' = carrier (G Mod G')"
      unfolding simple_group_def simple_group_axioms_def by auto
    thus False 
    proof
      assume "rcosets\<^bsub>G\<lparr>carrier := J\<rparr>\<^esub> G' = {\<one>\<^bsub>G Mod G'\<^esub>}"
      hence "rcosets\<^bsub>G\<lparr>carrier := J\<rparr>\<^esub> G' = {\<one>\<^bsub>(G\<lparr>carrier := J\<rparr>) Mod G'\<^esub>}" unfolding FactGroup_def by simp
      hence "G' = J" using G'J finJ normal.fact_group_trivial_iff unfolding FactGroup_def by fastforce
      with J(2) show False by simp
    next
      assume facts_eq:"rcosets\<^bsub>G\<lparr>carrier := J\<rparr>\<^esub> G' = carrier (G Mod G')"
      have "J = carrier G"
      proof
        show "J \<subseteq> carrier G" using J(1) normal_imp_subgroup subgroup_imp_subset by force
      next
        show "carrier G \<subseteq> J"
        proof
          fix x
          assume x:"x \<in> carrier G"
          hence "G' #> x \<in> carrier (G Mod G')" unfolding FactGroup_def RCOSETS_def by auto
          hence "G' #> x \<in> rcosets\<^bsub>G\<lparr>carrier := J\<rparr>\<^esub> G'" using facts_eq by auto
          then obtain j where j:"j \<in> J" "G' #> x = G' #> j" unfolding RCOSETS_def r_coset_def by force
          hence "x \<in> G' #> j" using G'G normal_imp_subgroup x repr_independenceD by fastforce
          then obtain g' where g':"g' \<in> G'" "x = g' \<otimes> j" unfolding r_coset_def by auto
          hence "g' \<in> J" using G'J normal_imp_subgroup subgroup_imp_subset by force
          with g'(2) j(1) show  "x \<in> J" using J(1) normal_imp_subgroup subgroup.m_closed by fastforce
        qed
      qed
      with J(3) show False by simp
    qed
  }
qed

text {* For the next lemma we need a few facts about removing adjacent duplicates. *}

lemma remdups_adj_obtain_adjacency:
  assumes "i + 1 < length (remdups_adj xs)" "length xs > 0"
  obtains j where "j + 1 < length xs"
    "(remdups_adj xs) ! i = xs ! j" "(remdups_adj xs) ! (i + 1) = xs ! (j + 1)"
using assms proof (induction xs arbitrary: i thesis)
  case Nil
  hence False by (metis length_greater_0_conv)
  thus thesis..
next
  case (Cons x xs)
  hence "xs \<noteq> []" using Divides.div_less Suc_eq_plus1 Zero_not_Suc div_eq_dividend_iff list.size(3,4) plus_nat.add_0 remdups_adj.simps(2) by metis
  then obtain y xs' where xs:"xs = y # xs'" by (metis list.exhaust)
  from `xs \<noteq> []` have lenxs:"length xs > 0" by simp
  from xs have rem:"remdups_adj (x # xs) = (if x = y then remdups_adj (y # xs') else x # remdups_adj (y # xs'))" using remdups_adj.simps(3) by auto
  show thesis
  proof (cases "x = y")
    case True
    with rem xs have rem2:"remdups_adj (x # xs) = remdups_adj xs" by auto
    with Cons(3) have "i + 1 < length (remdups_adj xs)" by simp
    with Cons.IH lenxs obtain k where j:"k + 1 < length xs" "remdups_adj xs ! i = xs ! k"
        "remdups_adj xs ! (i + 1) = xs ! (k + 1)" by auto
    thus thesis using Cons(2) rem2 by auto
  next
    case False
    with rem xs have rem2:"remdups_adj (x # xs) = x # remdups_adj xs" by auto
    show thesis
    proof (cases i)
      case 0
      have "0 + 1 < length (x # xs)" using lenxs by auto
      moreover have "remdups_adj (x # xs) ! i = (x # xs) ! 0"
      proof -
        have "remdups_adj (x # xs) ! i = (x # remdups_adj (y # xs')) ! 0" using xs rem2 0 by simp
        also have "\<dots> = x" by simp
        also have "\<dots> = (x # xs) ! 0" by simp
        finally show ?thesis.
      qed
      moreover have "remdups_adj (x # xs) ! (i + 1) = (x # xs) ! (0 + 1)"
      proof -
        have "remdups_adj (x # xs) ! (i + 1) = (x # remdups_adj (y # xs')) ! 1" using xs rem2 0 by simp
        also have "\<dots> = remdups_adj (y # xs') ! 0" by simp
        also have "\<dots> = (y # (remdups (y # xs'))) ! 0" by (metis nth_Cons' remdups_adj_Cons_alt)
        also have "\<dots> = y" by simp
        also have "\<dots> = (x # xs) ! (0 + 1)" unfolding xs by simp
        finally show ?thesis.
      qed
      ultimately show thesis by (rule Cons.prems(1))
    next
      case (Suc k)
      with Cons(3) have "k + 1 < length (remdups_adj (x # xs)) - 1" by auto
      also have "\<dots> \<le> length (remdups_adj xs) + 1 - 1" by (metis One_nat_def le_refl list.size(4) rem2)
      also have "\<dots> = length (remdups_adj xs)" by simp
      finally have "k + 1 < length (remdups_adj xs)".
      with Cons.IH lenxs obtain j where j:"j + 1 < length xs" "remdups_adj xs ! k = xs ! j"
        "remdups_adj xs ! (k + 1) = xs ! (j + 1)" by auto
      from j(1) have "Suc j + 1 < length (x # xs)" by simp
      moreover have "remdups_adj (x # xs) ! i = (x # xs) ! (Suc j)"
      proof -
        have "remdups_adj (x # xs) ! i = (x # remdups_adj xs) ! i" using rem2 by simp
        also have "\<dots> = (remdups_adj xs) ! k" using Suc by simp
        also have "\<dots> = xs ! j" using j(2) .
        also have "\<dots> = (x # xs) ! (Suc j)" by simp
        finally show ?thesis .
      qed
      moreover have "remdups_adj (x # xs) ! (i + 1) = (x # xs) ! (Suc j + 1)"
      proof -
        have "remdups_adj (x # xs) ! (i + 1) = (x # remdups_adj xs) ! (i + 1)" using rem2 by simp
        also have "\<dots> = (remdups_adj xs) ! (k + 1)" using Suc by simp
        also have "\<dots> = xs ! (j + 1)" using j(3).
        also have "\<dots> = (x # xs) ! (Suc j + 1)" by simp
        finally show ?thesis.
      qed
      ultimately show thesis by (rule Cons.prems(1))
    qed
  qed
qed

lemma hd_remdups_adj[simp]: "hd (remdups_adj xs) = hd xs"
  by (induction xs rule: remdups_adj.induct) simp_all

lemma remdups_adj_adjacent:
  "Suc i < length (remdups_adj xs) \<Longrightarrow> remdups_adj xs ! i \<noteq> remdups_adj xs ! Suc i"
proof (induction xs arbitrary: i rule: remdups_adj.induct)
  case (3 x y xs i)
  thus ?case by (cases i, cases "x = y") (simp, auto simp: hd_conv_nth[symmetric])
qed simp_all

text {* Intersecting each entry of a composition series with a normal subgroup of $G$ and removing
  all adjacent duplicates yields another composition series. *}

lemma (in composition_series) intersect_normal:
  assumes finite:"finite (carrier G)"
  assumes KG:"K \<lhd> G"
  shows "composition_series (G\<lparr>carrier := K\<rparr>) (remdups_adj (map (\<lambda>H. K \<inter> H) \<GG>))"
unfolding composition_series_def composition_series_axioms_def normal_series_def normal_series_axioms_def
apply (auto simp only: conjI del: equalityI)
proof -
  show "group (G\<lparr>carrier := K\<rparr>)" using KG normal_imp_subgroup subgroup_imp_group by auto
next
  --  {* Show, that removing adjacent duplicates doesn't result in an empty list. *}
  assume "remdups_adj (map (op \<inter> K) \<GG>) = []"
  hence "map (op \<inter> K) \<GG> = []" by (metis remdups_adj_Nil_iff)
  hence "\<GG> = []" by (metis Nil_is_map_conv)
  with notempty show False..
next
  -- {* Show, that the head of the reduced list is still the trivial group *}
  have "\<GG> = {\<one>} # tl \<GG>" using notempty hd by (metis list.sel(1,3) neq_Nil_conv)
  hence "map (op \<inter> K) \<GG> = map (op \<inter> K) ({\<one>} # tl \<GG>)" by simp
  hence "remdups_adj (map (op \<inter> K) \<GG>) = remdups_adj ((K \<inter> {\<one>}) # (map (op \<inter> K) (tl \<GG>)))" by simp
  also have "\<dots> = (K \<inter> {\<one>}) # tl (remdups_adj ((K \<inter> {\<one>}) # (map (op \<inter> K) (tl \<GG>))))" by simp
  finally have "hd (remdups_adj (map (op \<inter> K) \<GG>)) = K \<inter> {\<one>}" using list.sel(1) by metis
  thus "hd (remdups_adj (map (op \<inter> K) \<GG>)) = {\<one>\<^bsub>G\<lparr>carrier := K\<rparr>\<^esub>}" 
    using KG normal_imp_subgroup subgroup.one_closed by force
next
  -- {* Show that the last entry is really @{text "K \<inter> G"}. Since we don't have a lemma ready to talk about the
    last entry of a reduced list, we reverse the list twice. *}
  have "rev \<GG> = (carrier G) # tl (rev \<GG>)" by (metis list.sel(1,3) last last_rev neq_Nil_conv notempty rev_is_Nil_conv rev_rev_ident)
  hence "rev (map (op \<inter> K) \<GG>) = map (op \<inter> K) ((carrier G) # tl (rev \<GG>))" by (metis rev_map)
  hence rev:"rev (map (op \<inter> K) \<GG>) = (K \<inter> (carrier G)) # (map (op \<inter> K) (tl (rev \<GG>)))" by simp
  have "last (remdups_adj (map (op \<inter> K) \<GG>)) = hd (rev (remdups_adj (map (op \<inter> K) \<GG>)))"
    by (metis hd_rev map_is_Nil_conv notempty remdups_adj_Nil_iff)
  also have "\<dots> = hd (remdups_adj (rev (map (op \<inter> K) \<GG>)))" by (metis remdups_adj_rev)
  also have "\<dots> = hd (remdups_adj ((K \<inter> (carrier G)) # (map (op \<inter> K) (tl (rev \<GG>)))))" by (metis rev)
  also have "\<dots> = hd ((K \<inter> (carrier G)) # (remdups_adj ((K \<inter> (carrier G)) # (map (op \<inter> K) (tl (rev \<GG>))))))" by (metis list.sel(1) remdups_adj_Cons_alt)
  also have "\<dots> = K" using KG normal_imp_subgroup subgroup_imp_subset by force
  finally show "last (remdups_adj (map (op \<inter> K) \<GG>)) = carrier (G\<lparr>carrier := K\<rparr>)" by auto
next
  -- {* The induction step, using the second isomorphism theorem for groups. *}
  fix j
  assume j:"j + 1 < length (remdups_adj (map (op \<inter> K) \<GG>))"
  have KGnotempty:"(map (op \<inter> K) \<GG>) \<noteq> []" using notempty by (metis Nil_is_map_conv)
  with j obtain i where i:"i + 1 < length (map (op \<inter> K) \<GG>)"
    "(remdups_adj (map (op \<inter> K) \<GG>)) ! j = (map (op \<inter> K) \<GG>) ! i"
    "(remdups_adj (map (op \<inter> K) \<GG>)) ! (j + 1) = (map (op \<inter> K) \<GG>) ! (i + 1)"
    using remdups_adj_obtain_adjacency by force
  from i(1) have i':"i + 1 < length \<GG>" by (metis length_map)
  hence GiSi:"\<GG> ! i \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>" by (metis normal)
  hence GiSi':"\<GG> ! i \<subseteq> \<GG> ! (i + 1)" using normal_imp_subgroup subgroup_imp_subset by force
  from i' have finGSi:"finite (\<GG> ! (i + 1))" using  normal_series_subgroups finite by (metis subgroup_finite)
  from GiSi KG i' normal_series_subgroups have GSiKnormGSi:"\<GG> ! (i + 1) \<inter> K \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>"
    using second_isomorphism_grp.normal_subgrp_intersection_normal
    unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def by auto
  with GiSi have "\<GG> ! i \<inter> (\<GG> ! (i + 1) \<inter> K) \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>"
    by (metis group.normal_subgroup_intersect group.subgroup_imp_group i' is_group is_normal_series normal_series.normal_series_subgroups)
  hence "K \<inter> (\<GG> ! i \<inter> \<GG> ! (i + 1)) \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>" by (metis inf_commute inf_left_commute)
  hence KGinormGSi:"K \<inter> \<GG> ! i \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>" using GiSi' by (metis le_iff_inf)
  moreover have "K \<inter> \<GG> ! i \<subseteq> K \<inter> \<GG> ! (i + 1)" using GiSi' by auto
  moreover have groupGSi:"group (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)" using i normal_series_subgroups subgroup_imp_group by auto
  moreover have subKGSiGSi:"subgroup (K \<inter> \<GG> ! (i + 1)) (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)" by (metis GSiKnormGSi inf_sup_aci(1) normal_imp_subgroup)
  ultimately have fstgoal:"K \<inter> \<GG> ! i \<lhd> G\<lparr>carrier := \<GG> ! (i + 1), carrier := K \<inter> \<GG> ! (i + 1)\<rparr>"
    using group.normal_restrict_supergroup by force
  thus "remdups_adj (map (op \<inter> K) \<GG>) ! j \<lhd> G\<lparr>carrier := K, carrier := remdups_adj (map (op \<inter> K) \<GG>) ! (j + 1)\<rparr>"
    using i by auto
  from simplefact have Gisimple:"simple_group (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)" using i' by simp
  hence Gimax:"max_normal_subgroup (\<GG> ! i) (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)"
    using normal.max_normal_simple_quotient GiSi finGSi by force
  from GSiKnormGSi GiSi have "\<GG> ! i <#>\<^bsub>G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>\<^esub> \<GG> ! (i + 1) \<inter> K \<lhd> (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>)"
    using groupGSi group.normal_subgroup_set_mult_closed by simp
  hence "\<GG> ! i <#> \<GG> ! (i + 1) \<inter> K \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>" unfolding set_mult_def by auto
  hence "\<GG> ! i <#> K \<inter> \<GG> ! (i + 1) \<lhd> G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>" using inf_commute by metis
  moreover have "\<GG> ! i \<subseteq> \<GG> ! i <#>\<^bsub>G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>\<^esub> K \<inter> \<GG> ! (i + 1)"
    using second_isomorphism_grp.H_contained_in_set_mult
    unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def
    using subKGSiGSi GiSi normal_imp_subgroup by fastforce
  hence "\<GG> ! i \<subseteq> \<GG> ! i <#> K \<inter> \<GG> ! (i + 1)" unfolding set_mult_def by auto
  ultimately have KGdisj:"\<GG> ! i <#> K \<inter> \<GG> ! (i + 1) = \<GG> ! i \<or> \<GG> ! i <#> K \<inter> \<GG> ! (i + 1) = \<GG> ! (i + 1)"
    using Gimax unfolding max_normal_subgroup_def max_normal_subgroup_axioms_def
    by auto
  obtain \<phi> where "\<phi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (\<GG> ! i \<inter> (K \<inter> \<GG> ! (i + 1))))
    \<cong> (G\<lparr>carrier := \<GG> ! i <#>\<^bsub>G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>\<^esub> K \<inter> \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)"
    using second_isomorphism_grp.normal_intersection_quotient_isom
    unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def
    using GiSi subKGSiGSi normal_imp_subgroup  by fastforce
  hence "\<phi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! (i + 1) \<inter> \<GG> ! i))
    \<cong> (G\<lparr>carrier := \<GG> ! i <#>\<^bsub>G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>\<^esub> K \<inter> \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)" by (metis inf_commute)
  hence "\<phi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> (\<GG> ! (i + 1) \<inter> \<GG> ! i)))
    \<cong> (G\<lparr>carrier := \<GG> ! i <#>\<^bsub>G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>\<^esub> K \<inter> \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)" by (metis Int_assoc)
  hence "\<phi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i))
    \<cong> (G\<lparr>carrier := \<GG> ! i <#>\<^bsub>G\<lparr>carrier := \<GG> ! (i + 1)\<rparr>\<^esub> K \<inter> \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)" by (metis GiSi' Int_absorb2 Int_commute)
  hence \<phi>:"\<phi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)) \<cong> (G\<lparr>carrier := \<GG> ! i <#> K \<inter> \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)"
    unfolding set_mult_def by auto
  from fstgoal have KGsiKGigroup:"group (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i))" using normal.factorgroup_is_group by auto
  from KGdisj show "simple_group (G\<lparr>carrier := K, carrier := remdups_adj (map (op \<inter> K) \<GG>) ! (j + 1)\<rparr> Mod remdups_adj (map (op \<inter> K) \<GG>) ! j)"
  proof auto
    have groupGi:"group (G\<lparr>carrier := \<GG> ! i\<rparr>)" using i' normal_series_subgroups subgroup_imp_group by auto
    assume "\<GG> ! i <#> K \<inter> \<GG> ! Suc i = \<GG> ! i"
    with \<phi> have "\<phi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)) \<cong> (G\<lparr>carrier := \<GG> ! i\<rparr> Mod \<GG> ! i)" by auto
    moreover obtain \<psi> where "\<psi> \<in> (G\<lparr>carrier := \<GG> ! i\<rparr> Mod (carrier (G\<lparr>carrier := \<GG> ! i\<rparr>))) \<cong> (G\<lparr>carrier := {\<one>\<^bsub>G\<lparr>carrier := \<GG> ! i\<rparr>\<^esub>}\<rparr>)"
      using group.self_factor_iso groupGi by force
    ultimately obtain \<pi> where "\<pi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)) \<cong> (G\<lparr>carrier := {\<one>}\<rparr>)"
      using KGsiKGigroup group.iso_trans by fastforce
    hence "order (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)) = order (G\<lparr>carrier := {\<one>}\<rparr>)" by (metis iso_order_closed)
    hence "order (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)) = 1" unfolding order_def by auto
    hence "carrier (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)) = {\<one>\<^bsub>G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)\<^esub>}"
      using group.order_one_triv_iff KGsiKGigroup by auto
    moreover from fstgoal have "K \<inter> \<GG> ! i \<lhd> G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr>" by auto
    moreover from finGSi have "finite (carrier (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr>))" by auto
    ultimately have "K \<inter> \<GG> ! i = carrier (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr>)" by (metis normal.fact_group_trivial_iff)
    hence "(remdups_adj (map (op \<inter> K) \<GG>)) ! j = (remdups_adj (map (op \<inter> K) \<GG>)) ! (j + 1)" using i by auto
    with j have False using remdups_adj_adjacent KGnotempty Suc_eq_plus1 by metis
    thus "simple_group (G\<lparr>carrier := remdups_adj (map (op \<inter> K) \<GG>) ! Suc j\<rparr> Mod remdups_adj (map (op \<inter> K) \<GG>) ! j)"..
  next
    assume "\<GG> ! i <#> K \<inter> \<GG> ! Suc i = \<GG> ! Suc i"
    moreover with \<phi> have "\<phi> \<in> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i)) \<cong> (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i)"by auto
    then obtain \<phi>' where "\<phi>' \<in> (G\<lparr>carrier := \<GG> ! (i + 1)\<rparr> Mod \<GG> ! i) \<cong> (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i))"
      using KGsiKGigroup group.iso_sym by auto
    with Gisimple KGsiKGigroup have "simple_group (G\<lparr>carrier := K \<inter> \<GG> ! (i + 1)\<rparr> Mod (K \<inter> \<GG> ! i))" by (metis simple_group.iso_simple)
    with i show "simple_group (G\<lparr>carrier := remdups_adj (map (op \<inter> K) \<GG>) ! Suc j\<rparr> Mod remdups_adj (map (op \<inter> K) \<GG>) ! j)" by auto
  qed
qed

lemma (in group) composition_series_extend:
  assumes "composition_series (G\<lparr>carrier := H\<rparr>) \<HH>"
  assumes "simple_group (G Mod H)" "H \<lhd> G"
  shows "composition_series G (\<HH> @ [carrier G])"
unfolding composition_series_def composition_series_axioms_def
proof auto
  from assms(1) interpret comp\<HH>: composition_series "G\<lparr>carrier := H\<rparr>" \<HH> .
  show "normal_series G (\<HH> @ [carrier G])" using  assms(3) comp\<HH>.is_normal_series by (metis normal_series_extend)
  fix i
  assume i:"i < length \<HH>"
  show "simple_group (G\<lparr>carrier := (\<HH> @ [carrier G]) ! Suc i\<rparr> Mod (\<HH> @ [carrier G]) ! i)"
  proof (cases "i = length \<HH> - 1")
    case True
    hence "(\<HH> @ [carrier G]) ! Suc i = carrier G" by (metis i diff_Suc_1 lessE nth_append_length)
    moreover have "(\<HH> @ [carrier G]) ! i = \<HH> ! i"by (metis butlast_snoc i nth_butlast)
    hence "(\<HH> @ [carrier G]) ! i = H" using True last_conv_nth comp\<HH>.notempty comp\<HH>.last by auto
    ultimately show ?thesis using assms(2) by auto
  next
    case False
    hence "Suc i < length \<HH>" using i by auto
    hence "(\<HH> @ [carrier G]) ! Suc i = \<HH> ! Suc i" using nth_append by metis
    moreover from i have "(\<HH> @ [carrier G]) ! i = \<HH> ! i" using nth_append by metis
    ultimately show ?thesis using `Suc i < length \<HH>` comp\<HH>.simplefact by auto
  qed
qed

lemma (in composition_series) entries_mono:
  assumes "i \<le> j" "j < length \<GG>"
  shows "\<GG> ! i \<subseteq> \<GG> ! j"
using assms proof (induction "j - i" arbitrary: i j)
  case 0
  hence "i = j" by auto
  thus "\<GG> ! i \<subseteq> \<GG> ! j" by auto
next
  case (Suc k i j)
  hence i':"i + (Suc k) = j" "i + 1 < length \<GG>" by auto
  hence ij:"i + 1 \<le> j" by auto
  have "\<GG> ! i \<subseteq> \<GG> ! (i + 1)" using i' normal normal_imp_subgroup subgroup_imp_subset by force
  moreover have "j - (i + 1) = k" "j < length \<GG>" using Suc assms by auto
  hence "\<GG> ! (i + 1) \<subseteq> \<GG> ! j" using Suc(1) ij by auto
  ultimately show "\<GG> ! i \<subseteq> \<GG> ! j" by simp
qed

end
