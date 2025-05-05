theory Grounded_Multiset_Extension
  imports 
    Grounded_Order 
    Multiset_Extension
    Natural_Functor_To_Multiset
begin

section \<open>Grounded Multiset Extensions\<close>

locale functional_substitution_multiset_extension =
  sub: strict_order where less = "(\<prec>) :: 'sub \<Rightarrow> 'sub \<Rightarrow> bool" +
  multiset_extension where to_mset = to_mset +
  functional_substitution_lifting where id_subst = id_subst and to_set = to_set +
  natural_functor_to_multiset where to_set = to_set and to_mset = to_mset
for
  to_mset :: "'expr \<Rightarrow> 'sub multiset" and
  id_subst :: "'var \<Rightarrow> 'base" and
  to_set :: "'expr \<Rightarrow> 'sub set"
begin

(* TODO *)
no_notation less_eq (infix "\<preceq>" 50)
notation sub.less_eq (infix "\<preceq>" 50)

lemma lesseq_if_all_lesseq:
  assumes "\<forall>sub \<in># to_mset expr. sub \<cdot>\<^sub>s \<sigma>' \<preceq> sub \<cdot>\<^sub>s \<sigma>"
  shows "expr \<cdot> \<sigma>' \<preceq>\<^sub>m expr \<cdot> \<sigma>"
  using multp_image_lesseq_if_all_lesseq[OF sub.asymp sub.transp assms] inj_to_mset
  unfolding multiset_extension_def subst_def inj_def
  by (auto simp: to_mset_map)

lemma less_if_all_lesseq_ex_less:
  assumes
    "\<forall>sub\<in>#to_mset expr. sub \<cdot>\<^sub>s \<sigma>' \<preceq> sub \<cdot>\<^sub>s \<sigma>"
    "\<exists>sub\<in>#to_mset expr. sub \<cdot>\<^sub>s \<sigma>' \<prec> sub \<cdot>\<^sub>s \<sigma>"
  shows
    "expr \<cdot> \<sigma>' \<prec>\<^sub>m expr \<cdot> \<sigma>"
  using multp_image_less_if_all_lesseq_ex_less[OF sub.asymp sub.transp assms]
  unfolding multiset_extension_def subst_def to_mset_map.

end

locale grounded_multiset_extension =
  grounding_lifting where
  id_subst = "id_subst :: 'var \<Rightarrow> 'base" and to_set = "to_set :: 'expr \<Rightarrow> 'sub set" and
  to_set_ground = to_set_ground +
  functional_substitution_multiset_extension where to_mset = to_mset
for
  to_mset :: "'expr \<Rightarrow> 'sub multiset" and
  to_set_ground :: "'expr\<^sub>G \<Rightarrow> 'sub\<^sub>G set"
begin

sublocale strict_order_restriction "(\<prec>\<^sub>m)" from_ground
  by unfold_locales (rule inj_from_ground)

end

locale ground_total_multiset_extension =
  grounded_multiset_extension +
  sub: total_strict_order_restriction where lift = "sub_from_ground"
begin

sublocale sub: grounded_restricted_total_strict_order where
  subst = sub_subst and vars = sub_vars and to_ground = sub_to_ground and
  from_ground = sub_from_ground
  by unfold_locales

sublocale grounded_restricted_total_strict_order where
  subst = subst and vars = vars and to_ground = to_ground and
  from_ground = from_ground and less = "(\<prec>\<^sub>m)"
proof unfold_locales
  have "totalp_on {expr. set_mset expr \<subseteq> range sub_from_ground} (multp (\<prec>))"
    using sub.totalp totalp_on_multp
    by force

  then have "totalp_on {expr. set_mset (to_mset expr) \<subseteq> range sub_from_ground} (\<prec>\<^sub>m)"
    using inj_to_mset
    unfolding inj_def multiset_extension_def totalp_on_def
    by blast

  then show "totalp_on (range from_ground) (\<prec>\<^sub>m)"
    unfolding multiset_extension_def totalp_on_def from_ground_def
    by (simp add: image_mono to_mset_to_set)
qed

end

locale based_grounded_multiset_extension =
  based_functional_substitution_lifting where base_vars = base_vars +
  grounded_multiset_extension +
  base: strict_order where less = base_less
for
  base_vars :: "'base \<Rightarrow> 'var set" and
  base_less :: "'base \<Rightarrow> 'base \<Rightarrow> bool"

subsection \<open>Ground substitution stability\<close>

locale ground_subst_stable_multiset_extension =
  grounded_multiset_extension +
  sub: ground_subst_stable_grounded_order where
  less = less and subst = sub_subst and vars = sub_vars and from_ground = sub_from_ground and
  to_ground = sub_to_ground
begin

sublocale ground_subst_stable_grounded_order where
  less = "(\<prec>\<^sub>m)" and subst = subst and vars = vars and from_ground = from_ground and
  to_ground = to_ground
proof unfold_locales

  fix expr\<^sub>1 expr\<^sub>2 \<gamma>

  assume grounding: "is_ground (expr\<^sub>1 \<cdot> \<gamma>)" "is_ground (expr\<^sub>2 \<cdot> \<gamma>)" and less: "expr\<^sub>1 \<prec>\<^sub>m expr\<^sub>2"

  show "expr\<^sub>1 \<cdot> \<gamma> \<prec>\<^sub>m expr\<^sub>2 \<cdot> \<gamma>"
  proof(
      unfold multiset_extension_def subst_def to_mset_map,
      rule multp_map_strong[OF sub.transp _ less[unfolded multiset_extension_def]])

    show "monotone_on (set_mset (to_mset expr\<^sub>1 + to_mset expr\<^sub>2)) (\<prec>) (\<prec>) (\<lambda>sub. sub \<cdot>\<^sub>s \<gamma>)"
      using grounding monotone_onI sub.ground_subst_stability
      by (metis (mono_tags, lifting) to_mset_to_set to_set_is_ground_subst union_iff)
  qed
qed

end

subsection \<open>Substitution update stability\<close>

locale subst_update_stable_multiset_extension =
  based_grounded_multiset_extension +
  sub: subst_update_stable_grounded_order where
  vars = sub_vars and subst = sub_subst and to_ground = sub_to_ground and
  from_ground = sub_from_ground
begin

(* TODO *)
no_notation less_eq (infix "\<preceq>" 50)

sublocale subst_update_stable_grounded_order where
  less = "(\<prec>\<^sub>m)"  and vars = vars and subst = subst and from_ground = from_ground and
  to_ground = to_ground
proof unfold_locales
  fix update x \<gamma> expr

  assume assms:
    "base.is_ground update" "base_less update (\<gamma> x)" "is_ground (expr \<cdot> \<gamma>)" "x \<in> vars expr"

  moreover then have "\<forall>sub \<in># to_mset expr. sub \<cdot>\<^sub>s \<gamma>(x := update) \<preceq> sub \<cdot>\<^sub>s \<gamma>"
    using
      sub.subst_update_stability
      sub.subst_reduntant_upd
      to_mset_to_set
      to_set_is_ground_subst
    by blast

  moreover have "\<exists>sub \<in># to_mset expr. sub \<cdot>\<^sub>s \<gamma>(x := update) \<prec> (sub \<cdot>\<^sub>s \<gamma>)"
    using sub.subst_update_stability assms
    unfolding vars_def subst_def to_mset_to_set
    by fastforce

  ultimately show "expr \<cdot> \<gamma>(x := update) \<prec>\<^sub>m expr \<cdot> \<gamma>"
    using less_if_all_lesseq_ex_less
    by blast
qed

end

end
