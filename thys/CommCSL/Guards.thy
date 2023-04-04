subsection \<open>Consistency\<close>

theory Guards
  imports StateModel CommCSL AbstractCommutativity
begin

text \<open>A state is "consistent" iff:
1. All its permissions are full
2. Has unique guards iff has shared guard
3. The values in the fractional heaps are "reachable" wrt to the sequence and multiset of actions
4. Has exactly guards for the names in "scope"\<close>

definition reachable :: "('i, 'a, 'v) single_context \<Rightarrow> 'v \<Rightarrow> ('i, 'a) heap \<Rightarrow> bool" where
  "reachable scont v0 h \<longleftrightarrow> (\<forall>sargs uargs. get_gs h = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h k = Some (uargs k))
\<longrightarrow> reachable_value (saction scont) (uaction  scont) v0 sargs uargs (view scont (normalize (get_fh h))))"

lemma reachableI:
  assumes "\<And>sargs uargs. get_gs h = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h k = Some (uargs k))
\<Longrightarrow> reachable_value (saction scont) (uaction  scont) v0 sargs uargs (view scont (normalize (get_fh h)))"
  shows "reachable scont v0 h"
  by (metis assms reachable_def)

lemma reachableE:
  assumes "reachable scont v0 h"
  and "get_gs h = Some (pwrite, sargs)"
  and "\<And>k. get_gu h k = Some (uargs k)"
  shows "reachable_value (saction scont) (uaction  scont) v0 sargs uargs (view scont (normalize (get_fh h)))"
by (meson assms reachable_def)

definition all_guards :: "('i, 'a) heap \<Rightarrow> bool" where
  "all_guards h \<longleftrightarrow> (\<exists>v. get_gs h = Some (pwrite, v)) \<and> (\<forall>k. get_gu h k \<noteq> None)"

lemma no_guardI:
  assumes "get_gs h = None"
      and "\<And>k. get_gu h k = None"
    shows "no_guard h"
  using assms(1) assms(2) no_guard_def by blast

definition semi_consistent :: "('i, 'a, 'v) single_context \<Rightarrow> 'v \<Rightarrow> ('i, 'a) heap \<Rightarrow> bool" where
  "semi_consistent \<Gamma> v0 h \<longleftrightarrow> all_guards h \<and> reachable \<Gamma> v0 h"

lemma semi_consistentE:
  assumes "semi_consistent \<Gamma> v0 h"
  shows "\<exists>sargs uargs. get_gs h = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h k = Some (uargs k))
  \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (normalize (get_fh h)))"
proof -
  let ?uargs = "\<lambda>k. (SOME x. get_gu h k = Some x)"
  have "\<And>k. get_gu h k = Some (?uargs k)"
  proof -
    fix k have "\<exists>x. get_gu h k = Some x"
      by (meson all_guards_def assms option.exhaust_sel semi_consistent_def)
    then show "get_gu h k = Some (?uargs k)"
      by fastforce
  qed
  moreover obtain sargs where "get_gs h = Some (pwrite, sargs)"
    by (meson all_guards_def assms semi_consistent_def)
  ultimately have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs ?uargs (view \<Gamma> (normalize (get_fh h)))"
    by (meson assms reachableE semi_consistent_def)
  then show ?thesis
    using \<open>\<And>k. get_gu h k = Some (SOME x. get_gu h k = Some x)\<close> \<open>get_gs h = Some (pwrite, sargs)\<close> by fastforce
qed

lemma semi_consistentI:
  assumes "all_guards h"
      and "reachable \<Gamma> v0 h"
    shows "semi_consistent \<Gamma> v0 h"
  by (simp add: assms(1) assms(2) semi_consistent_def)

lemma no_guard_then_smaller_same:
  assumes "Some h = Some a \<oplus> Some b"
      and "no_guard h"
    shows "no_guard a"
proof (rule no_guardI)
  show "get_gs a = None"
    by (metis add_gs.elims assms(1) assms(2) no_guard_def option.simps(3) plus_extract(2))
  fix k
  have "get_gu h k = None"
    by (meson assms(2) no_guard_def)
  then show "get_gu a k = None"
    by (metis assms(1) full_uguard_sum_same option.exhaust)
qed

lemma all_guardsI:
  assumes "\<And>k. get_gu h k \<noteq> None"
       and "\<exists>v. get_gs h = Some (pwrite, v)"
     shows "all_guards h"
  using all_guards_def assms(1) assms(2) by blast

lemma all_guards_same:
  assumes "all_guards a"
      and "Some h = Some a \<oplus> Some b"
    shows "all_guards h"
proof (rule all_guardsI)
  show "\<exists>v. get_gs h = Some (pwrite, v)"
    using all_guards_def assms(1) assms(2) full_sguard_sum_same by blast
  fix k have "get_gu a k \<noteq> None"
    by (meson all_guards_def assms(1))
  then show "get_gu h k \<noteq> None"
    apply (cases "get_gu b k")
     apply (metis assms(2) full_uguard_sum_same not_Some_eq)
    by (metis assms(2) full_uguard_sum_same option.discI plus_comm)
qed

definition empty_unique where
  "empty_unique _ = None"

definition remove_guards :: "('i, 'a) heap \<Rightarrow> ('i, 'a) heap" where
  "remove_guards h = (get_fh h, None, empty_unique)"

lemma remove_guards_smaller:
  "h \<succeq> remove_guards h"
proof -
  have "remove_guards h ## (Map.empty, get_gs h, get_gu h)"
  proof (rule compatibleI)
    show "compatible_fract_heaps (get_fh (remove_guards h)) (get_fh (Map.empty, get_gs h, get_gu h))"
      using compatible_fract_heapsI by force
    show "\<And>k. get_gu (remove_guards h) k = None \<or> get_gu (Map.empty, get_gs h, get_gu h) k = None"
      by (simp add: empty_unique_def remove_guards_def)
    show "\<And>p p'. get_gs (remove_guards h) = Some p \<and> get_gs (Map.empty, get_gs h, get_gu h) = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
      by (simp add: remove_guards_def)
  qed
  then obtain x where "Some x = Some (remove_guards h) \<oplus> Some (Map.empty, get_gs h, get_gu h)"
    by auto
  moreover have "x = h"
  proof (rule heap_ext)
    show "get_fh x = get_fh h"
      by (metis add_fh_map_empty add_get_fh calculation fst_conv get_fh.elims remove_guards_def)
    show "get_gs x = get_gs h"
      by (metis calculation fst_eqD get_gs.elims plus_comm remove_guards_def snd_eqD sum_gs_one_none)
    show "get_gu x = get_gu h"
    proof (rule ext)
      fix k
      have "get_gu (remove_guards h) k = None"
        by (simp add: empty_unique_def remove_guards_def)       
      then show "get_gu x k = get_gu h k"
        by (metis (mono_tags, lifting) add_gu_def add_gu_single.simps(1) calculation get_gu.elims plus_extract(3) snd_eqD)
    qed
  qed
  ultimately show ?thesis
    using larger_def by blast
qed

lemma no_guard_remove:
  assumes "Some a = Some b \<oplus> Some c"
      and "no_guard c"
    shows "get_gs a = get_gs b"
      and "get_gu a = get_gu b"
  using assms(1) assms(2) no_guard_def sum_gs_one_none apply blast
proof (rule ext)
  fix k
  have "get_gu c k = None"
    by (meson assms(2) no_guard_def)
  then show "get_gu a k = get_gu b k"
    by (metis (no_types, lifting) add_gu_def add_gu_single.simps(1) assms(1) plus_comm plus_extract(3))
qed

lemma full_guard_comp_then_no:
  assumes "a ## b"
      and "all_guards a"
    shows "no_guard b"
proof (rule no_guardI)
  show "\<And>k. get_gu b k = None"
    by (meson all_guards_def assms(1) assms(2) compatible_def)
  show "get_gs b = None"
  proof (rule ccontr)
    assume "get_gs b \<noteq> None"
    then obtain gb where "get_gs b = Some gb"
      by blast
    moreover obtain v where "get_gs a = Some (pwrite, v)"
      by (meson all_guards_def assms(2))
    moreover have "pgt (padd pwrite (fst gb)) pwrite"
      using sum_larger by auto
    ultimately show False
      by (metis assms(1) compatible_def fst_eqD not_pgte_charact)
  qed
qed

lemma sum_of_no_guards:
  assumes "no_guard a"
      and "no_guard b"
      and "Some x = Some a \<oplus> Some b"
    shows "no_guard x"
  by (metis assms(1) assms(2) assms(3) no_guard_def no_guard_remove(1) no_guard_remove(2))

lemma no_guard_remove_guards:
  "no_guard (remove_guards h)"
  by (simp add: empty_unique_def no_guard_def remove_guards_def)

lemma get_fh_remove_guards:
  "get_fh (remove_guards h) = get_fh h"
  by (simp add: remove_guards_def)

definition pair_sat :: "(store \<times> ('i, 'a) heap) set \<Rightarrow> (store \<times> ('i, 'a) heap) set \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> bool" where
  "pair_sat S S' Q \<longleftrightarrow> (\<forall>\<sigma> \<sigma>'. \<sigma> \<in> S \<and> \<sigma>' \<in> S' \<longrightarrow> \<sigma>, \<sigma>' \<Turnstile> Q)"

lemma pair_satI:
  assumes "\<And>s h s' h'. (s, h) \<in> S \<and> (s', h') \<in> S' \<Longrightarrow> (s, h), (s', h') \<Turnstile> Q"
  shows "pair_sat S S' Q"
  by (simp add: assms pair_sat_def)

lemma pair_sat_smallerI:
  assumes "\<And>\<sigma> \<sigma>'. \<sigma> \<in> S \<and> \<sigma>' \<in> S' \<Longrightarrow> \<sigma>, \<sigma>' \<Turnstile> Q"
  shows "pair_sat S S' Q"
  by (simp add: assms pair_sat_def)

lemma pair_satE:
  assumes "pair_sat S S' Q"
      and "(s, h) \<in> S \<and> (s', h') \<in> S'"
    shows "(s, h), (s', h') \<Turnstile> Q"
  using assms(1) assms(2) pair_sat_def by blast

definition add_states :: "(store \<times> ('i, 'a) heap) set \<Rightarrow> (store \<times> ('i, 'a) heap) set \<Rightarrow> (store \<times> ('i, 'a) heap) set" where
  "add_states S1 S2 = {(s, H) |s H h1 h2. Some H = Some h1 \<oplus> Some h2 \<and> (s, h1) \<in> S1 \<and> (s, h2) \<in> S2}"

lemma add_states_sat_star:
  assumes "pair_sat SA SA' A"
      and "pair_sat SB SB' B"
    shows "pair_sat (add_states SA SB) (add_states SA' SB') (Star A B)"
proof (rule pair_satI)
  fix s h s' h'
  assume asm0: "(s, h) \<in> add_states SA SB \<and> (s', h') \<in> add_states SA' SB'"
  then obtain ha hb ha' hb' where "(s, ha) \<in> SA" "(s, hb) \<in> SB" "(s', ha') \<in> SA'" "(s', hb') \<in> SB'"
  "Some h = Some ha \<oplus> Some hb" "Some h' = Some ha' \<oplus> Some hb'"
    using add_states_def[of SA SB] add_states_def[of SA' SB'] fst_eqD mem_Collect_eq snd_conv
    by auto
  then show "(s, h), (s', h') \<Turnstile> Star A B"
    by (meson assms(1) assms(2) hyper_sat.simps(4) pair_sat_def)
qed

lemma add_states_subset:
  assumes "S1 \<subseteq> S1'"
  shows "add_states S1 S2 \<subseteq> add_states S1' S2"
proof
  fix x assume "x \<in> add_states S1 S2"
  then show "x \<in> add_states S1' S2"
    using add_states_def[of S1 S2] add_states_def[of S1' S2] assms mem_Collect_eq[of x] subsetD[of S1 S1']
    by blast
qed

lemma add_states_comm:
  "add_states S1 S2 = add_states S2 S1"
proof -
  have "\<And>S1 S2. add_states S1 S2 \<subseteq> add_states S2 S1"
  proof -
    fix S1 S2
    show "add_states S1 S2 \<subseteq> add_states S2 S1"
    proof
      fix x assume "x \<in> add_states S1 S2"
      then obtain h1 h2 where "Some (snd x) = Some h1 \<oplus> Some h2" "(fst x, h1) \<in> S1" "(fst x, h2) \<in> S2"
        using add_states_def[of S1 S2] fst_conv mem_Collect_eq[of x] snd_eqD
        by auto
      moreover have "Some (snd x) = Some h2 \<oplus> Some h1"
        by (simp add: calculation(1) plus_comm)
      ultimately show "x \<in> add_states S2 S1"
        using add_states_def[of S2 S1] mem_Collect_eq[of x] surjective_pairing[of x] by blast
    qed
  qed
  then show ?thesis by blast
qed

lemma magic_lemma:
  assumes "Some x1 = Some a1 \<oplus> Some j1"
      and "Some x2 = Some a2 \<oplus> Some j2"
      and "(s1, x1), (s2, x2) \<Turnstile> Star A J"
      and "(s1, j1), (s2, j2) \<Turnstile> J"
      and "precise J"
    shows "(s1, a1), (s2, a2) \<Turnstile> A"
proof -
  obtain a1' a2' j1' j2' where "Some x1 = Some a1' \<oplus> Some j1'"
   "Some x2 = Some a2' \<oplus> Some j2'" "(s1, j1'), (s2, j2') \<Turnstile> J"  "(s1, a1'), (s2, a2') \<Turnstile> A"
    using assms(3) hyper_sat.simps(4) by blast
  have "j1 = j1' \<and> j2 = j2'"
    using assms(5)
  proof (rule preciseE)
    show "x1 \<succeq> j1' \<and> x1 \<succeq> j1 \<and> x2 \<succeq> j2' \<and> x2 \<succeq> j2"
      by (metis \<open>Some x1 = Some a1' \<oplus> Some j1'\<close> \<open>Some x2 = Some a2' \<oplus> Some j2'\<close> assms(1) assms(2) larger_def plus_comm)
    show "(s1, j1'), (s2, j2') \<Turnstile> J \<and> (s1, j1), (s2, j2) \<Turnstile> J"
      by (simp add: \<open>(s1, j1'), (s2, j2') \<Turnstile> J\<close> assms(4))
  qed
  then have "a1 = a1' \<and> a2 = a2'"
    using \<open>Some x1 = Some a1' \<oplus> Some j1'\<close> \<open>Some x2 = Some a2' \<oplus> Some j2'\<close> addition_cancellative assms(1) assms(2) by blast
  then show ?thesis
    using \<open>(s1, a1'), (s2, a2') \<Turnstile> A\<close> by blast
qed


lemma full_no_guard_same_normalize:
  assumes "full_ownership (get_fh h) \<and> no_guard h"
      and "full_ownership (get_fh h') \<and> no_guard h'"
      and "normalize (get_fh h) = normalize (get_fh h')"
    shows "h = h'"
proof (rule heap_ext)
  show "get_gu h = get_gu h'"
    apply (rule ext)
    by (metis assms(1) assms(2) no_guard_def)
  show "get_gs h = get_gs h'"
    by (metis assms(1) assms(2) no_guard_def)
  show "get_fh h = get_fh h'"
  proof (rule ext)
    fix l show "get_fh h l = get_fh h' l"
      apply (cases "get_fh h l")
      apply (metis FractionalHeap.normalize_eq(1) assms(3))
      apply (cases "get_fh h' l")
      apply (metis FractionalHeap.normalize_eq(1) assms(3))
      by (metis FractionalHeap.normalize_def apply_opt.simps(2) assms(1) assms(2) assms(3) full_ownership_def prod.collapse)
  qed
qed

lemma get_fh_same_then_remove_guards_same:
  assumes "get_fh a = get_fh b"
  shows "remove_guards a = remove_guards b"
  by (metis assms remove_guards_def)


lemma remove_guards_sum:
  assumes "Some x = Some a \<oplus> Some b"
  shows "Some (remove_guards x) = Some (remove_guards a) \<oplus> Some (remove_guards b)"
proof -
  have "remove_guards a ## remove_guards b"
    by (metis (no_types, lifting) assms compatible_def compatible_eq get_fh_remove_guards no_guard_def no_guard_remove_guards option.distinct(1))
  then obtain y where "Some y = Some (remove_guards a) \<oplus> Some (remove_guards b)"
    by auto
  moreover have "remove_guards x = y"
    by (metis (no_types, lifting) \<open>remove_guards a ## remove_guards b\<close> add_get_fh assms calculation get_fh_remove_guards get_gu.simps no_guard_def no_guard_remove(1) no_guard_remove(2) no_guard_remove_guards option.inject plus.simps(3) plus_extract(2) remove_guards_def snd_eqD)
  ultimately show ?thesis by blast
qed

lemma no_guard_smaller:
  assumes "a \<succeq> b"
  shows "remove_guards a \<succeq> remove_guards b"
using assms larger_def remove_guards_sum by blast

definition add_empty_guards :: "('i, 'a) heap \<Rightarrow> ('i, 'a) heap" where
  "add_empty_guards h = (get_fh h, Some (pwrite, {#}), (\<lambda>_. Some []))"

lemma no_guard_map_empty_compatible:
  assumes "no_guard a"
      and "get_fh b = Map.empty"
    shows "a ## b"
  by (metis (no_types, lifting) assms(1) assms(2) compatible_def compatible_fract_heapsI no_guard_def option.simps(3))

lemma no_guard_add_empty_is_add:
  assumes "no_guard h"
  shows "Some (add_empty_guards h) = Some h \<oplus> Some (Map.empty, Some (pwrite, {#}), (\<lambda>_. Some []))"
proof -
  obtain x where "Some x = Some h \<oplus> Some (Map.empty, Some (pwrite, {#}), (\<lambda>_. Some []))"
    by (simp add: assms no_guard_map_empty_compatible)
  moreover have "add_empty_guards h = x"
  proof (rule heap_ext)
    show "get_fh (add_empty_guards h) = get_fh x"
      by (metis add_empty_guards_def add_fh_map_empty add_get_fh calculation fst_conv get_fh.elims)
    show "get_gs (add_empty_guards h) = get_gs x"
      by (metis add_empty_guards_def assms calculation get_gs.elims no_guard_remove(1) plus_comm snd_eqD)
    show "get_gu (add_empty_guards h) = get_gu x"
      by (metis add_empty_guards_def assms calculation get_gu.elims no_guard_remove(2) plus_comm snd_eqD)
  qed
  ultimately show ?thesis by blast
qed

lemma no_guard_and_sat_p_empty_guards:
  assumes "(s, h), (s', h') \<Turnstile> A"
      and "no_guard h \<and> no_guard h'"
    shows "(s, add_empty_guards h), (s', add_empty_guards h') \<Turnstile> Star A EmptyFullGuards"
proof -
  have "(s, (Map.empty, Some (pwrite, {#}), (\<lambda>_. Some []))), (s', (Map.empty, Some (pwrite, {#}), (\<lambda>_. Some []))) \<Turnstile> EmptyFullGuards"
    by simp
  then show ?thesis
    using assms(1) assms(2) hyper_sat.simps(4) no_guard_add_empty_is_add by blast
qed

lemma no_guard_add_empty_guards_sum:
  assumes "no_guard x"
      and "Some x = Some a \<oplus> Some b"
    shows "Some (add_empty_guards x) = Some (add_empty_guards a) \<oplus> Some b"
  using assms(1) assms(2) no_guard_add_empty_is_add[of a] no_guard_add_empty_is_add[of x]
    no_guard_then_smaller_same[of x a b] plus_asso plus_comm
  by (metis (no_types, lifting))

lemma semi_consistent_empty_no_guard_initial_value:
  assumes "no_guard h"
  shows "semi_consistent \<Gamma> (view \<Gamma> (FractionalHeap.normalize (get_fh h))) (add_empty_guards h)"
proof (rule semi_consistentI)
  show "all_guards (add_empty_guards h)"
    by (simp add: add_empty_guards_def all_guards_def)
  show "reachable \<Gamma> (view \<Gamma> (FractionalHeap.normalize (get_fh h))) (add_empty_guards h)"
  proof (rule reachableI)
    fix sargs uargs
    assume asm0: "get_gs (add_empty_guards h) = Some (pwrite, sargs) \<and> (\<forall>k. get_gu (add_empty_guards h) k = Some (uargs k))"
    then have "sargs = {#} \<and> uargs = (\<lambda>k. [])"
      by (metis add_empty_guards_def fst_conv get_gs.simps get_gu.simps option.sel snd_conv)
    then show "reachable_value (saction \<Gamma>) (uaction \<Gamma>) (view \<Gamma> (FractionalHeap.normalize (get_fh h))) sargs uargs
        (view \<Gamma> (FractionalHeap.normalize (get_fh (add_empty_guards h))))"
      by (simp add: Self add_empty_guards_def)
  qed
qed

lemma no_guards_remove_same:
  assumes "no_guard h"
  shows "h = remove_guards (add_empty_guards h)"
  by (metis add_empty_guards_def addition_cancellative assms fst_conv get_fh.elims get_fh_remove_guards no_guard_add_empty_is_add no_guard_remove_guards)

lemma no_guards_remove:
  "no_guard h \<longleftrightarrow> h = remove_guards h"
  by (metis get_fh_remove_guards no_guard_remove_guards no_guards_remove_same remove_guards_def)

definition add_sguard_to_no_guard :: "('i, 'a) heap \<Rightarrow> prat \<Rightarrow> 'a multiset \<Rightarrow> ('i, 'a) heap" where
  "add_sguard_to_no_guard h \<pi> ms = (get_fh h, Some (\<pi>, ms), (\<lambda>_. None))"


lemma get_fh_add_sguard:
  "get_fh (add_sguard_to_no_guard h \<pi> ms) = get_fh h"
  by (simp add: add_sguard_to_no_guard_def)

lemma add_sguard_as_sum:
  assumes "no_guard h"
  shows "Some (add_sguard_to_no_guard h \<pi> ms) = Some h \<oplus> Some (Map.empty, Some (\<pi>, ms), (\<lambda>_. None))"
proof -
  obtain x where "Some x = Some h \<oplus> Some (Map.empty, Some (\<pi>, ms), (\<lambda>_. None))"
    by (simp add: assms no_guard_map_empty_compatible)
  moreover have "x = add_sguard_to_no_guard h \<pi> ms"
  proof (rule heap_ext)
    show "get_fh x = get_fh (add_sguard_to_no_guard h \<pi> ms)"
      by (metis add_fh_map_empty add_get_fh calculation fst_conv get_fh.elims get_fh_add_sguard)
    show "get_gs x = get_gs (add_sguard_to_no_guard h \<pi> ms)"
      by (metis add_sguard_to_no_guard_def assms calculation get_gs.elims no_guard_def plus_comm snd_eqD sum_gs_one_none)
    show "get_gu x = get_gu (add_sguard_to_no_guard h \<pi> ms)"
      by (metis add_sguard_to_no_guard_def assms calculation get_gu.simps no_guard_remove(2) plus_comm snd_conv)
  qed
  ultimately show ?thesis by blast
qed

definition add_uguard_to_no_guard :: "'i \<Rightarrow> ('i, 'a) heap \<Rightarrow> 'a list \<Rightarrow> ('i, 'a) heap" where
  "add_uguard_to_no_guard k h l = (get_fh h, None, (\<lambda>_. None)(k := Some l))"


lemma get_fh_add_uguard:
  "get_fh (add_uguard_to_no_guard k h l) = get_fh h"
  by (simp add: add_uguard_to_no_guard_def)

lemma prove_sum:
  assumes "a ## b"
      and "\<And>x. Some x = Some a \<oplus> Some b \<Longrightarrow> x = y"
    shows "Some y = Some a \<oplus> Some b"
  using assms(1) assms(2) by fastforce

lemma add_uguard_as_sum:
  assumes "no_guard h"
  shows "Some (add_uguard_to_no_guard k h l) = Some h \<oplus> Some (Map.empty, None, (\<lambda>_. None)(k := Some l))"
proof (rule prove_sum)
  show "h ## (Map.empty, None, [k \<mapsto> l])"
    by (simp add: assms no_guard_map_empty_compatible)
  fix x assume asm0: "Some x = Some h \<oplus> Some (Map.empty, None, [k \<mapsto> l])"
  show "x = add_uguard_to_no_guard k h l"
  proof (rule heap_ext)
    show "get_fh x = get_fh (add_uguard_to_no_guard k h l)"
      by (metis add_fh_map_empty add_get_fh asm0 fst_conv get_fh.elims get_fh_add_uguard)
    show "get_gs x = get_gs (add_uguard_to_no_guard k h l)"
      by (metis add_uguard_to_no_guard_def asm0 assms get_gs.elims no_guard_def plus_comm snd_eqD sum_gs_one_none)
    show "get_gu x = get_gu (add_uguard_to_no_guard k h l)"
      by (metis add_uguard_to_no_guard_def asm0 assms get_gu.elims no_guard_remove(2) plus_comm snd_eqD)
  qed
qed


lemma no_guard_and_no_heap:
  assumes "Some h = Some p \<oplus> Some g"
      and "no_guard p"
      and "get_fh g = Map.empty"
    shows "remove_guards h = p"
proof (rule heap_ext)
  show "get_fh (remove_guards h) = get_fh p"
  proof -
    have "get_fh (remove_guards h) = get_fh h"
      using get_fh_remove_guards by blast
    moreover have "get_fh h = add_fh (get_fh p) (get_fh g)"
      using add_get_fh assms(1) by blast
    ultimately show ?thesis
      by (metis assms(1) assms(3) ext get_fh.simps sum_second_none_get_fh)
  qed
  show "get_gs (remove_guards h) = get_gs p"
    by (metis assms(2) no_guard_def no_guard_remove_guards)
  show "get_gu (remove_guards h) = get_gu p"
    by (metis \<open>get_fh (remove_guards h) = get_fh p\<close> assms(2) get_fh_remove_guards no_guards_remove remove_guards_def)
qed


lemma decompose_guard_remove_easy:
  "Some h = Some (remove_guards h) \<oplus> Some (Map.empty, get_gs h, get_gu h)"
proof (rule prove_sum)
  show "remove_guards h ## (Map.empty, get_gs h, get_gu h)"
    by (simp add: no_guard_map_empty_compatible no_guard_remove_guards)
  fix x assume asm0: "Some x = Some (remove_guards h) \<oplus> Some (Map.empty, get_gs h, get_gu h)"
  show "x = h"
  proof (rule heap_ext)
    show "get_fh x = get_fh h"
      by (metis add_fh_map_empty add_get_fh asm0 fst_conv get_fh.elims get_fh_remove_guards)
    show "get_gs x = get_gs h"
      by (metis asm0 fst_conv get_gs.simps no_guard_remove(1) no_guard_remove_guards plus_comm snd_conv)
    show "get_gu x = get_gu h"
      by (metis asm0 get_gu.elims no_guard_remove(2) no_guard_remove_guards plus_comm snd_eqD)
  qed
qed


lemma all_guards_no_guard_propagates:
  assumes "all_guards x"
      and "Some x = Some a \<oplus> Some b"
      and "no_guard a"
    shows "all_guards b"
  by (metis all_guards_def assms(1) assms(2) assms(3) no_guard_def no_guard_remove(2) plus_comm sum_gs_one_none)

lemma all_guards_exists_uargs:
  assumes "all_guards x"
  shows "\<exists>uargs. \<forall>k. get_gu x k = Some (uargs k)"
proof -
  let ?uargs = "\<lambda>k. the (get_gu x k)"
  have "\<And>k. get_gu x k = Some (?uargs k)"
    by (metis all_guards_def assms option.collapse)
  then show ?thesis
    by fastforce
qed

lemma all_guards_sum_known_one:
  assumes "Some x = Some a \<oplus> Some b"
      and "all_guards x"
      and "\<And>k. get_gu a k = None"
      and "get_gs a = Some (\<pi>, ms)"
    shows "\<exists>\<pi>' msf uargs. (\<forall>k. get_gu b k = Some (uargs k)) \<and>
  ((\<pi> = pwrite \<and> get_gs b = None \<and> msf = {#}) \<or> (pwrite = padd \<pi> \<pi>' \<and> get_gs b = Some (\<pi>', msf)))"
proof (cases "\<pi> = pwrite")
  case True
  then have "get_gs b = None"
    using add_gs.simps(2)[of "(\<pi>, ms)"] add_gs_cancellative add_gs_comm assms(1) assms(4) full_sguard_sum_same
      plus_extract(2)[of x a b]
    by metis
  moreover obtain uargs where "\<And>k. get_gu x k = Some (uargs k)"
    using all_guards_exists_uargs assms(2) by blast
  moreover have "\<And>k. get_gu b k = Some (uargs k)"
  proof -
    fix k
    have "get_gu a k = None"
      using assms(3) by auto
    then show "get_gu b k = Some (uargs k)"
      by (metis (no_types, opaque_lifting) add_gu_def add_gu_single.simps(1) assms(1) calculation(2) plus_extract(3))
  qed
  ultimately show ?thesis
    using True by blast
next
  case False
  then obtain \<pi>' msf where "get_gs b = Some (\<pi>', msf)"
    by (metis all_guards_def assms(1) assms(2) assms(4) fst_conv option.exhaust_sel option.sel prod.exhaust_sel sum_gs_one_none)
  moreover obtain v where "get_gs x = Some (pwrite, v)"
    by (meson all_guards_def assms(2))
  ultimately have "pwrite = padd \<pi> \<pi>'"
    by (metis Pair_inject assms(1) assms(4) option.inject sum_gs_one_some)
  then show ?thesis
    by (metis (mono_tags, opaque_lifting) \<open>get_gs b = Some (\<pi>', msf)\<close> add_gu_def add_gu_single.simps(1) all_guards_exists_uargs assms(1) assms(2) assms(3) plus_extract(3))
qed

fun add_pwrite_option where
  "add_pwrite_option None = None"
| "add_pwrite_option (Some x) = Some (pwrite, x)"

definition denormalize :: "normal_heap \<Rightarrow> ('i, 'a) heap" where
  "denormalize H = ((\<lambda>l. add_pwrite_option (H l)), None, (\<lambda>_. None))"

lemma denormalize_properties:
  shows "no_guard (denormalize H)"
    and "full_ownership (get_fh (denormalize H))"
    and "normalize (get_fh (denormalize H)) = H"
    and "full_ownership (get_fh h) \<and> no_guard h \<Longrightarrow> denormalize (normalize (get_fh h)) = h"
    and "full_ownership (get_fh h) \<Longrightarrow> denormalize (normalize (get_fh h)) = remove_guards h"
      apply (simp add: denormalize_def no_guardI)
  using full_ownershipI[of "get_fh (denormalize H)"] add_pwrite_option.elims denormalize_def fst_conv get_fh.elims option.distinct(1) option.sel apply metis
proof -
  show "normalize (get_fh (denormalize H)) = H"
  proof (rule ext)
    fix l show "normalize (get_fh (denormalize H)) l = H l"
      by (metis FractionalHeap.normalize_eq(1) FractionalHeap.normalize_eq(2) add_pwrite_option.elims denormalize_def fst_conv get_fh.elims)
  qed
  show "full_ownership (get_fh h) \<and> no_guard h \<Longrightarrow> denormalize (FractionalHeap.normalize (get_fh h)) = h"
  proof -
    assume asm0: "full_ownership (get_fh h) \<and> no_guard h"
    show "denormalize (FractionalHeap.normalize (get_fh h)) = h"
    proof (rule heap_ext)
      show "get_fh (denormalize (FractionalHeap.normalize (get_fh h))) = get_fh h"
      proof (rule ext)
        fix x show "get_fh (denormalize (FractionalHeap.normalize (get_fh h))) x = get_fh h x"
        proof (cases "get_fh h x")
          case None
          then show ?thesis
            by (metis FractionalHeap.normalize_eq(1) add_pwrite_option.simps(1) denormalize_def fst_conv get_fh.elims)
        next
          case (Some p)
          then have "fst p = pwrite"
            by (meson asm0 full_ownership_def)
          then show ?thesis
            by (metis FractionalHeap.normalize_eq(2) Some add_pwrite_option.simps(2) denormalize_def fst_conv get_fh.elims prod.collapse)
        qed
      qed
      show "get_gs (denormalize (FractionalHeap.normalize (get_fh h))) = get_gs h"
        by (metis asm0 denormalize_def fst_conv get_gs.elims no_guard_def snd_eqD)
      show "get_gu (denormalize (FractionalHeap.normalize (get_fh h))) = get_gu h"
        by (metis \<open>get_fh (denormalize (FractionalHeap.normalize (get_fh h))) = get_fh h\<close> \<open>get_gs (denormalize (FractionalHeap.normalize (get_fh h))) = get_gs h\<close> asm0 denormalize_def full_no_guard_same_normalize get_gu.simps no_guard_def snd_conv)
    qed
  qed
  assume asm0: "full_ownership (get_fh h)"
  show "denormalize (FractionalHeap.normalize (get_fh h)) = remove_guards h"
  proof (rule heap_ext)
    show "get_fh (denormalize (FractionalHeap.normalize (get_fh h))) = get_fh (remove_guards h)"
    proof (rule ext)
      fix x show "get_fh (denormalize (FractionalHeap.normalize (get_fh h))) x = get_fh (remove_guards h) x"
      proof (cases "get_fh h x")
        case None
        then show ?thesis
          by (metis FractionalHeap.normalize_eq(1) add_pwrite_option.simps(1) denormalize_def fst_eqD get_fh.elims get_fh_remove_guards)
      next
        case (Some p)
        then have "fst p = pwrite"
          by (meson asm0 full_ownership_def)
        then show ?thesis
          by (metis FractionalHeap.normalize_eq(2) Some add_pwrite_option.simps(2) denormalize_def fst_conv get_fh.elims get_fh_remove_guards prod.collapse)
      qed
    qed
    show "get_gs (denormalize (FractionalHeap.normalize (get_fh h))) = get_gs (remove_guards h)"
      by (simp add: denormalize_def remove_guards_def)
    show "get_gu (denormalize (FractionalHeap.normalize (get_fh h))) = get_gu (remove_guards h)"
      by (metis \<open>get_fh (denormalize (FractionalHeap.normalize (get_fh h))) = get_fh (remove_guards h)\<close> \<open>get_gs (denormalize (FractionalHeap.normalize (get_fh h))) = get_gs (remove_guards h)\<close> asm0 denormalize_def full_no_guard_same_normalize get_fh_remove_guards get_gu.simps no_guard_def no_guard_remove_guards snd_conv)
  qed
qed

lemma no_guard_then_sat_star_uguard:
  assumes "no_guard h \<and> no_guard h'"
      and "(s, h), (s', h') \<Turnstile> Q"
    shows "(s, add_uguard_to_no_guard k h (e s)), (s', add_uguard_to_no_guard k h' (e s')) \<Turnstile> Star Q (UniqueGuard k e)"
proof -
  obtain "Some (add_uguard_to_no_guard k h (e s)) = Some h \<oplus> Some (Map.empty, None, [k \<mapsto> e s])"
    "Some (add_uguard_to_no_guard k h' (e s')) = Some h' \<oplus> Some (Map.empty, None, [k \<mapsto> e s'])"
    by (simp add: add_uguard_as_sum assms(1))
  moreover have "(s, (Map.empty, None, [k \<mapsto> e s])), (s', (Map.empty, None, [k \<mapsto> e s'])) \<Turnstile> UniqueGuard k e"
    by simp
  ultimately show ?thesis using assms(2) by fastforce
qed


lemma no_guard_then_sat_star:
  assumes "no_guard h \<and> no_guard h'"
      and "(s, h), (s', h') \<Turnstile> Q"
    shows "(s, add_sguard_to_no_guard h \<pi> (ms s)), (s', add_sguard_to_no_guard h' \<pi> (ms s')) \<Turnstile> Star Q (SharedGuard \<pi> ms)"
proof -
  obtain "Some (add_sguard_to_no_guard h \<pi> (ms s)) = Some h \<oplus> Some (Map.empty, Some (\<pi>, ms s), (\<lambda>_. None))"
    "Some (add_sguard_to_no_guard h' \<pi> (ms s')) = Some h' \<oplus> Some (Map.empty, Some (\<pi>, ms s'), (\<lambda>_. None))"
    using add_sguard_as_sum assms(1) by blast
  moreover have "(s, (Map.empty, Some (\<pi>, ms s), (\<lambda>_. None))), (s', (Map.empty, Some (\<pi>, ms s'), (\<lambda>_. None))) \<Turnstile> SharedGuard \<pi> ms"
    by simp
  ultimately show ?thesis using assms(2) by fastforce
qed


end