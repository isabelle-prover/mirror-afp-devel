theory Nonground_Order_Generic
  imports
    Nonground_Clause_Generic
    Nonground_Term_Order
    Term_Order_Lifting
    Ground_Order_Generic
begin

section \<open>Nonground Order\<close>

locale nonground_order_lifting =
  grounding_lifting +
  order: ground_total_multiset_extension +
  order: ground_subst_stable_multiset_extension +
  order: subst_update_stable_multiset_extension

locale nonground_term_based_order_lifting =
  "term": nonground_term +
  nonground_order_lifting where
  id_subst = Var and comp_subst = "(\<odot>)" and base_vars = term.vars and base_less = less\<^sub>t and
  base_subst = "(\<cdot>t)"
for less\<^sub>t

locale nonground_order_generic =
  nonground_term_with_context where
  Var = "Var :: 'v \<Rightarrow> 't" and term_to_ground = "term_to_ground :: 't \<Rightarrow> 'f gterm" and
  apply_context = "apply_context :: 'c \<Rightarrow> 't \<Rightarrow> 't" +
 
  nonground_clause_generic where
  atom_subst = atom_subst and atom_from_ground = atom_from_ground +

  restricted_term_order_lifting where
  pos_to_mset = pos_to_mset and restriction = "range term.from_ground" +

  clause: nonground_term_based_order_lifting where
  less = "(\<prec>\<^sub>l)" and sub_subst = literal.subst and sub_vars = literal.vars and
  sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and
  map = image_mset and to_set = set_mset and to_ground_map = image_mset and
  from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset and
  to_mset = "\<lambda>x. x" +

  "term": nonground_term_order +

  ground: atom_to_mset where pos_to_mset = ground_pos_to_mset and neg_to_mset = ground_neg_to_mset
for 
  pos_to_mset :: "'a \<Rightarrow> 't multiset" and 
  atom_subst :: "'a \<Rightarrow> ('v \<Rightarrow> 't) \<Rightarrow> 'a" and
  atom_from_ground :: "'a\<^sub>G \<Rightarrow> 'a" and
  ground_pos_to_mset ground_neg_to_mset :: "'a\<^sub>G \<Rightarrow> 'f gterm multiset" +
assumes
  ground_pos_to_mset:
  "\<And>a. image_mset term.from_ground (ground_pos_to_mset a) = pos_to_mset (atom_from_ground a)" and
  ground_neg_to_mset:
  "\<And>a. image_mset term.from_ground (ground_neg_to_mset a) = neg_to_mset (atom_from_ground a)"
begin

(* TODO: Find way to not have this twice *)
notation term.order.less\<^sub>G (infix "\<prec>\<^sub>t\<^sub>G" 50)
notation term.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>t\<^sub>G" 50)

(* TODO: Find way to call clause.order.sub = literal.order *)
notation clause.order.sub.less\<^sub>G (infix "\<prec>\<^sub>l\<^sub>G" 50)
notation clause.order.sub.less_eq\<^sub>G (infix "\<preceq>\<^sub>l\<^sub>G" 50)

notation clause.order.less\<^sub>G (infix "\<prec>\<^sub>c\<^sub>G" 50)
notation clause.order.less_eq\<^sub>G (infix "\<preceq>\<^sub>c\<^sub>G" 50)

lemma obtain_maximal_literal:
  assumes
    not_empty: "C \<noteq> {#}" and
    grounding: "clause.is_ground (C \<cdot> \<gamma>)"
  obtains l
  where "is_maximal l C" "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
proof-

  have grounding_not_empty: "C \<cdot> \<gamma> \<noteq> {#}"
    using not_empty
    by simp

  obtain l where
    l_in_C: "l \<in># C" and
    l_grounding_is_maximal: "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
    using
      ex_maximal_in_mset_wrt[OF
        literal.order.transp_on_less literal.order.asymp_on_less grounding_not_empty]
      maximal_in_clause
    unfolding clause.subst_def
    by (metis (mono_tags, lifting) image_iff multiset.set_map)

  show ?thesis
  proof(cases "is_maximal l C")
    case True

    with l_grounding_is_maximal that
    show ?thesis
      by blast
  next
    case False
    then obtain l' where
      l'_in_C: "l' \<in># C" and
      l_less_l': "l \<prec>\<^sub>l l'"
      unfolding is_maximal_def
      using l_in_C
      by blast

    note literals_in_C = l_in_C l'_in_C
    note literals_grounding = literals_in_C[THEN clause.to_set_is_ground_subst[OF _ grounding]]

    have "l \<cdot>l \<gamma> \<prec>\<^sub>l l' \<cdot>l \<gamma>"
      using clause.order.sub.ground_subst_stability[OF literals_grounding l_less_l'] .

    then have False
     using
       l_grounding_is_maximal
       clause.subst_in_to_set_subst[OF l'_in_C]
     unfolding is_maximal_def
     by force

    then show ?thesis..
  qed
qed

lemma obtain_strictly_maximal_literal:
  assumes
   grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   ground_strictly_maximal: "is_strictly_maximal l\<^sub>G (C \<cdot> \<gamma>)"
 obtains l where
   "is_strictly_maximal l C" "l\<^sub>G = l \<cdot>l \<gamma>"
proof-

  have grounding_not_empty: "C \<cdot> \<gamma> \<noteq> {#}"
    using is_strictly_maximal_not_empty[OF ground_strictly_maximal].

  have l\<^sub>G_in_grounding: "l\<^sub>G \<in># C \<cdot> \<gamma>"
    using strictly_maximal_in_clause[OF ground_strictly_maximal].

  obtain l where
    l_in_C: "l \<in># C" and
    l\<^sub>G [simp]: "l\<^sub>G = l \<cdot>l \<gamma>"
    using l\<^sub>G_in_grounding
    unfolding clause.subst_def
    by blast

  show ?thesis
  proof(cases "is_strictly_maximal l C")
    case True
    show ?thesis
      using that[OF True l\<^sub>G].
  next
    case False

    then obtain l' where
      l'_in_C: "l' \<in># C - {# l #}" and
      l_less_eq_l': "l \<preceq>\<^sub>l l'"
      unfolding is_strictly_maximal_def
      using l_in_C
      by blast

    note l_grounding =
       clause.to_set_is_ground_subst[OF l_in_C grounding]

    have l'_grounding: "literal.is_ground (l' \<cdot>l \<gamma>)"
      using l'_in_C grounding
      by (meson clause.to_set_is_ground_subst in_diffD)

    have "l \<cdot>l \<gamma> \<preceq>\<^sub>l l' \<cdot>l \<gamma>"
      using
        clause.order.sub.less_eq.ground_subst_stability[OF l_grounding l'_grounding l_less_eq_l'].

    then have False
      using clause.subst_in_to_set_subst[OF l'_in_C] ground_strictly_maximal
      unfolding is_strictly_maximal_def subst_clause_remove1_mset[OF l_in_C]
      by simp

    then show ?thesis..
  qed
qed

lemma is_maximal_if_grounding_is_maximal:
  assumes
   l_in_C: "l \<in># C" and
   C_grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   l_grounding_is_maximal: "is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
 shows
   "is_maximal l C"
proof(rule ccontr)
  assume "\<not> is_maximal l C"

  then obtain l' where l_less_l': "l \<prec>\<^sub>l l'" and l'_in_C: "l' \<in># C"
    using l_in_C
    unfolding is_maximal_def
    by blast

  have l'_grounding: "literal.is_ground (l' \<cdot>l \<gamma>)"
    using clause.to_set_is_ground_subst[OF l'_in_C C_grounding].

  have l_grounding: "literal.is_ground (l \<cdot>l \<gamma>)"
    using clause.to_set_is_ground_subst[OF l_in_C C_grounding].

  have l'_\<gamma>_in_C_\<gamma>: "l' \<cdot>l \<gamma> \<in># C \<cdot> \<gamma>"
    using clause.subst_in_to_set_subst[OF l'_in_C].

  have "l \<cdot>l \<gamma> \<prec>\<^sub>l l' \<cdot>l \<gamma>"
    using clause.order.sub.ground_subst_stability[OF l_grounding l'_grounding l_less_l'].

  then have "\<not> is_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
    using l'_\<gamma>_in_C_\<gamma>
    unfolding is_maximal_def literal.subst_comp_subst
    by fastforce

  then show False
    using l_grounding_is_maximal..
qed

lemma is_strictly_maximal_if_grounding_is_strictly_maximal:
  assumes
   l_in_C: "l \<in># C" and
   grounding: "clause.is_ground (C \<cdot> \<gamma>)" and
   grounding_strictly_maximal: "is_strictly_maximal (l \<cdot>l \<gamma>) (C \<cdot> \<gamma>)"
 shows
   "is_strictly_maximal l C"
  using
    is_maximal_if_grounding_is_maximal[OF
      l_in_C
      grounding
      is_maximal_if_is_strictly_maximal[OF grounding_strictly_maximal]
    ]
    grounding_strictly_maximal
  unfolding
    is_strictly_maximal_def is_maximal_def
    subst_clause_remove1_mset[OF l_in_C, symmetric]
    reflclp_iff
  by (metis in_diffD clause.subst_in_to_set_subst)

lemma unique_maximal_in_ground_clause:
  assumes
    "clause.is_ground C"
    "is_maximal l C"
    "is_maximal l' C"
  shows
    "l = l'"
  using assms clause.to_set_is_ground clause.order.sub.not_less_eq
  unfolding is_maximal_def reflclp_iff
  by meson

lemma unique_strictly_maximal_in_ground_clause:
  assumes
    "clause.is_ground C"
    "is_strictly_maximal l C"
    "is_strictly_maximal l' C"
  shows
    "l = l'"
  using assms unique_maximal_in_ground_clause
  by blast

 (* TODO: order.order *)
thm literal.order.order.strict_iff_order

abbreviation ground_is_maximal where
  "ground_is_maximal l\<^sub>G C\<^sub>G \<equiv> is_maximal (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"

abbreviation ground_is_strictly_maximal where
  "ground_is_strictly_maximal l\<^sub>G C\<^sub>G \<equiv>
     is_strictly_maximal (literal.from_ground l\<^sub>G) (clause.from_ground C\<^sub>G)"

sublocale ground: ground_order_generic where
  less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)" and pos_to_mset = ground_pos_to_mset and neg_to_mset = ground_neg_to_mset
rewrites
  less\<^sub>l\<^sub>G_rewrite [simp]:
  "multiset_extension.multiset_extension (\<prec>\<^sub>t\<^sub>G) ground.literal_to_mset = (\<prec>\<^sub>l\<^sub>G)" and
  less\<^sub>c\<^sub>G_rewrite [simp]: "multiset_extension.multiset_extension (\<prec>\<^sub>l\<^sub>G) (\<lambda>x. x) = (\<prec>\<^sub>c\<^sub>G)" and
  is_maximal_rewrite [simp]: "\<And>l\<^sub>G C\<^sub>G. ground.is_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_maximal l\<^sub>G C\<^sub>G" and
  is_strictly_maximal_rewrite [simp]:
  "\<And>l\<^sub>G C\<^sub>G. ground.is_strictly_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_strictly_maximal l\<^sub>G C\<^sub>G" and
  "ground.literal_order_restriction = UNIV"
proof (unfold_locales; (rule ground.inj_pos_to_mset ground.inj_neg_to_mset ground.pos_neg_neq)?)

  interpret ground: ground_order_generic where
    less\<^sub>t = "(\<prec>\<^sub>t\<^sub>G)" and pos_to_mset = ground_pos_to_mset and neg_to_mset = ground_neg_to_mset
    using ground.inj_pos_to_mset ground.inj_neg_to_mset ground.pos_neg_neq
    by unfold_locales auto

  interpret multiset_extension "(\<prec>\<^sub>t\<^sub>G)" ground.literal_to_mset
    by unfold_locales

  interpret relation_restriction
    "(\<lambda>b1 b2. multp (\<prec>\<^sub>t) (literal_to_mset b1) (literal_to_mset b2))" literal.from_ground
    by unfold_locales

  have literal_to_mset: "literal_to_mset (map_literal atom_from_ground l) =
            image_mset term.from_ground (ground.literal_to_mset l)" for l
    by (cases l) (auto simp: ground_pos_to_mset ground_neg_to_mset)

  show less\<^sub>l\<^sub>G_rewrite: "ground.literal.order.multiset_extension = (\<prec>\<^sub>l\<^sub>G)"
    unfolding
      ground.literal.order.multiset_extension_def 
      literal.order.multiset_extension_def
      R\<^sub>r_def
    unfolding 
      literal.from_ground_def 
      literal_to_mset
      term.order.less\<^sub>G_def
    using 
      multp_image_mset_image_msetI[OF _ term.order.transp]
      multp_image_mset_image_msetD[OF _ term.order.transp]
      term.inj_from_ground 
    by metis

  fix l\<^sub>G C\<^sub>G
  show "ground.is_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_maximal l\<^sub>G C\<^sub>G"
    unfolding
      ground.is_maximal_def
      is_maximal_def
      less\<^sub>l\<^sub>G_rewrite
      clause.order.sub.restriction.is_maximal_in_mset_iff
      clause.order.sub.less\<^sub>r_def
    by (simp add: clause.to_set_from_ground image_iff)

  show "ground.is_strictly_maximal l\<^sub>G C\<^sub>G \<longleftrightarrow> ground_is_strictly_maximal l\<^sub>G C\<^sub>G"
    unfolding
      ground.is_strictly_maximal_def
      is_strictly_maximal_def
      less\<^sub>l\<^sub>G_rewrite
      clause.order.sub.restriction.is_strictly_maximal_in_mset_iff
      clause.order.sub.less\<^sub>r_def
      reflclp_iff
    by (metis (lifting) clause.ground_sub_in_ground clause.sub_in_ground_is_ground 
        clause_from_ground_remove1_mset literal.obtain_grounding)

  show "{b. set_mset (ground.literal_to_mset b) \<subseteq> UNIV} = UNIV"
    by auto
next

  interpret multiset_extension "(\<prec>\<^sub>l\<^sub>G)" "\<lambda>x. x"
    by unfold_locales

  interpret relation_restriction "multp (\<prec>\<^sub>l)" clause.from_ground
    by unfold_locales

  show less\<^sub>c\<^sub>G_rewrite: "(\<prec>\<^sub>m) = (\<prec>\<^sub>c\<^sub>G)"
    unfolding multiset_extension_def clause.order.multiset_extension_def R\<^sub>r_def
    unfolding clause.order.sub.less\<^sub>G_def clause.from_ground_def
    by (metis literal.inj_from_ground literal.order.transp multp_image_mset_image_msetD
        multp_image_mset_image_msetI)
qed

lemma less\<^sub>c_add_mset:
  assumes "l \<prec>\<^sub>l l'" "C \<preceq>\<^sub>c C'"
  shows "add_mset l C \<prec>\<^sub>c add_mset l' C'"
  using assms multp_add_mset_reflclp[OF literal.order.asymp literal.order.transp]
  unfolding less\<^sub>c_def
  by blast

lemmas less\<^sub>c_add_same [simp] =
  multp_add_same[OF literal.order.asymp literal.order.transp, folded less\<^sub>c_def]

end

end
