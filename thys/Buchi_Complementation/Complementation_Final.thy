section {* Complementation to Explicit Büchi Automaton *}

theory Complementation_Final
imports
  "Complementation_Implement"
  "Transition_Systems_and_Automata.BA_Translate"
  "HOL-Library.Permutation"
begin

  lemma complement_3_finite[simp]:
    assumes "finite (nodes A)"
    shows "finite (nodes (complement_3 A))"
  proof -
    have "(nodes (complement_3 A), nodes (complement_2 A)) \<in> \<langle>Id\<rangle> set_rel"
      using complement_3_refine by parametricity auto
    also have "(nodes (complement_2 A), nodes (complement_1 A)) \<in> \<langle>Id\<rangle> set_rel"
      using complement_2_refine by parametricity auto
    also have "(nodes (complement_1 A), nodes (complement A)) \<in> \<langle>cs_rel\<rangle> set_rel"
      using complement_1_refine by parametricity auto
    finally have 1: "(nodes (complement_3 A), nodes (complement A)) \<in> \<langle>cs_rel\<rangle> set_rel" by simp
    have "finite (nodes (complement A))" using complement_finite assms(1) by this
    then show "finite (nodes (complement_3 A))"
      using finite_set_rel_transfer_back[OF 1 cs_rel_inv_single_valued] by simp
  qed
  lemma complement_3_language[simp]:
    assumes "finite (nodes A)"
    shows "language (complement_3 A) = streams (alphabet A) - language A"
  proof -
    have "(language (complement_3 A), language (complement_2 A)) \<in> \<langle>\<langle>Id\<rangle> stream_rel\<rangle> set_rel"
      using complement_3_refine by parametricity auto
    also have "(language (complement_2 A), language (complement_1 A)) \<in> \<langle>\<langle>Id\<rangle> stream_rel\<rangle> set_rel"
      using complement_2_refine by parametricity auto
    also have "(language (complement_1 A), language (complement A)) \<in> \<langle>\<langle>Id\<rangle> stream_rel\<rangle> set_rel"
      using complement_1_refine by parametricity auto
    also have "language (complement A) = streams (alphabet A) - language A"
      using complement_language assms(1) by this
    finally show "language (complement_3 A) = streams (alphabet A) - language A" by simp
  qed

  definition list_hash :: "('a :: hashable) list \<Rightarrow> uint32" where
    "list_hash xs \<equiv> fold (bitXOR \<circ> hashcode) xs 0"

  lemma list_hash_eq:
    assumes "distinct xs" "distinct ys" "set xs = set ys"
    shows "list_hash xs = list_hash ys"
  proof -
    have "remdups xs <~~> remdups ys" using eq_set_perm_remdups assms(3) by this
    then have "xs <~~> ys" using assms(1, 2) by (simp add: distinct_remdups_id)
    then have "fold (bitXOR \<circ> hashcode) xs a = fold (bitXOR \<circ> hashcode) ys a" for a
    proof (induct arbitrary: a)
      case (swap y x l)
      have "x XOR y XOR a = y XOR x XOR a" for x y by (transfer) (simp add: word_bw_lcs(3))
      then show ?case by simp
    qed simp+
    then show ?thesis unfolding list_hash_def by this
  qed

  definition state_hash :: "nat \<Rightarrow> (nat \<times> item) list \<Rightarrow> nat" where
    "state_hash n p \<equiv> nat_of_hashcode (list_hash p) mod n"

  lemma state_hash_bounded_hashcode[autoref_ga_rules]: "is_bounded_hashcode state_rel
    (gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list)) (list_map_lookup (=))
    (prod_eq (=) (\<longleftrightarrow>))) state_hash"
  proof
    show [param]: "(gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list)) (list_map_lookup (=))
      (prod_eq (=) (\<longleftrightarrow>)), (=)) \<in> state_rel \<rightarrow> state_rel \<rightarrow> bool_rel" by autoref
    show "state_hash n xs = state_hash n ys" if "xs \<in> Domain state_rel" "ys \<in> Domain state_rel"
      "gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list))
      (list_map_lookup (=)) (prod_eq (=) (=)) xs ys" for xs ys n
    proof -
      have 1: "distinct (map fst xs)" "distinct (map fst ys)"
        using that(1, 2) unfolding list_map_rel_def list_map_invar_def by (auto simp: in_br_conv)
      have 2: "distinct xs" "distinct ys" using 1 by (auto intro: distinct_mapI)
      have 3: "(xs, map_of xs) \<in> state_rel" "(ys, map_of ys) \<in> state_rel"
        using 1 unfolding list_map_rel_def list_map_invar_def by (auto simp: in_br_conv)
      have 4: "(gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list)) (list_map_lookup (=))
        (prod_eq (=) (\<longleftrightarrow>)) xs ys, map_of xs = map_of ys) \<in> bool_rel" using 3 by parametricity
      have 5: "map_to_set (map_of xs) = map_to_set (map_of ys)" using that(3) 4 by simp
      have 6: "set xs = set ys" using map_to_set_map_of 1 5 by blast
      show "state_hash n xs = state_hash n ys" unfolding state_hash_def using list_hash_eq 2 6 by metis
    qed
    show "state_hash n x < n" if "1 < n" for n x using that unfolding state_hash_def by simp
  qed

  schematic_goal complement_impl:
    assumes [simp]: "finite (nodes A)"
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>Id, nat_rel, unit_rel\<rangle> bai_ba_rel"
    shows "(?f :: ?'c, to_baei (complement_3 A)) \<in> ?R"
    by autoref
  concrete_definition complement_impl uses complement_impl[unfolded autoref_tag_defs]

  theorem
    assumes "finite (nodes A)"
    assumes "(Ai, A) \<in> \<langle>Id, nat_rel, unit_rel\<rangle> bai_ba_rel"
    shows "language (bae_ba (bae (complement_impl Ai))) = streams (alphabet A) - language A"
  proof -
    have "(language ((bae_ba \<circ> bae) (complement_impl Ai)), language (id (complement_3 A))) \<in>
      \<langle>\<langle>Id_on (alphabet (complement_3 A))\<rangle> stream_rel\<rangle> set_rel"
      using complement_impl.refine[OF assms, unfolded to_baei_def id_apply] by parametricity
    also have "language (id (complement_3 A)) = streams (alphabet A) - language A"
      using assms(1) by simp
    finally show ?thesis by simp
  qed

  definition s where
    "s a p \<equiv> if p = 0
      then (if a = ''a'' then [0, 1, 2] else [1])
      else (if a = ''a'' then [1] else [])"
  definition Ai where
    "Ai \<equiv> \<lparr> alphabeti = [''a'', ''b''], initiali = [0], succi = s, acceptingi = \<lambda> p. False \<rparr>"

  (* TODO: look through code
    - equality on maps needs a lot of lookups, make sure those are fast,
    - make sure we don't use slow generic algorithms when fast specializations are possible *)
  (* TODO: the reachability analysis should only be done once *)
  export_code complement_impl in SML module_name Complementation

  (* TODO: is it supposed to be this many states/transitions?
    maybe we can also do some crude optimizations about reachability *)
  value "length (transei (complement_impl Ai))"
  (*value "length (remdups (map fst (transei (complement_impl Ai))))"*)

end