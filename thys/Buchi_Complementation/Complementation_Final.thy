section {* Complementation to Explicit Büchi Automaton *}

theory Complementation_Final
imports
  "Complementation_Implement"
  "Transition_Systems_and_Automata.NBA_Translate"
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

(*
  definition list_hash :: "('a :: hashable) list \<Rightarrow> uint32" where
    "list_hash xs \<equiv> fold (bitXOR \<circ> hashcode) xs 0"
*)

  definition "hci k \<equiv> uint32_of_nat k * 1103515245 + 12345"
  definition "hc \<equiv> \<lambda> (p, q, b). hci p + hci q * 31 + (if b then 1 else 0)"
  definition list_hash :: "(nat \<times> item) list \<Rightarrow> uint32" where
    "list_hash xs \<equiv> fold (bitXOR \<circ> hc) xs 0"

  lemma list_hash_eq:
    assumes "distinct xs" "distinct ys" "set xs = set ys"
    shows "list_hash xs = list_hash ys"
  proof -
    have "remdups xs <~~> remdups ys" using eq_set_perm_remdups assms(3) by this
    then have "xs <~~> ys" using assms(1, 2) by (simp add: distinct_remdups_id)
    then have "fold (bitXOR \<circ> hc) xs a = fold (bitXOR \<circ> hc) ys a" for a
    proof (induct arbitrary: a)
      case (swap y x l)
      have "x XOR y XOR a = y XOR x XOR a" for x y by (transfer) (simp add: word_bw_lcs(3))
      then show ?case by simp
    qed simp+
    then show ?thesis unfolding list_hash_def by this
  qed

  definition state_hash :: "nat \<Rightarrow> Complementation_Implement.state \<Rightarrow> nat" where
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
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(?f :: ?'c, RETURN (to_nbaei (complement_3 A))) \<in> ?R"
    by (autoref_monadic (plain))
  concrete_definition complement_impl uses complement_impl[unfolded autoref_tag_defs]

  theorem
    assumes "finite (nodes A)"
    assumes "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "language (nbae_nba (nbaei_nbae (complement_impl Ai))) = streams (alphabet A) - language A"
  proof -
    have "(language ((nbae_nba \<circ> nbaei_nbae) (complement_impl Ai)), language (id (complement_3 A))) \<in>
      \<langle>\<langle>Id_on (alphabet (complement_3 A))\<rangle> stream_rel\<rangle> set_rel"
      using complement_impl.refine[OF assms, unfolded to_nbaei_def id_apply, THEN RETURN_nres_relD]
      by parametricity
    also have "language (id (complement_3 A)) = streams (alphabet A) - language A"
      using assms(1) by simp
    finally show ?thesis by simp
  qed

  definition s where
    "s n a p \<equiv> if p = 0
      then (if a = ''a'' then [0 ..< n] else [1])
      else (if a = ''a'' then [1 ..< n] else [])"
  definition "Ai n \<equiv> nbai [''a'', ''b''] [0] (s n) bot"

  definition "test n \<equiv> length (transei (complement_impl (Ai n)))"

  (* TODO: maybe we can also do some crude optimizations about reachability *)
  export_code complement_impl nat_of_integer integer_of_nat test
    in SML module_name Complementation file "code/Complementation_Export.sml"

  value "succi (complement_6 (Ai 3) 3) ''a'' (initiali (complement_6 (Ai 3) 3) ! 0) ! 7"
  value "succi (complement_6 (Ai 3) 3) ''a'' (initiali (complement_6 (Ai 3) 3) ! 0) ! 27"
  value "hashcode (1 :: nat, 1 :: nat, False)"
  value "hashcode (0 :: nat, 0 :: nat, True)"
  value "(1 :: nat) XOR 66"
  value "hashcode (1 :: nat, 3 :: nat, False)"
  value "hashcode (0 :: nat, 6 :: nat, True)"
  value "(132 :: nat) XOR 199"
  value "list_hash (succi (complement_6 (Ai 3) 3) ''a'' (initiali (complement_6 (Ai 3) 3) ! 0) ! 7)"

end