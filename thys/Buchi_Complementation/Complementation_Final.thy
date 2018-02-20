section {* Complementation to Explicit Büchi Automaton *}

theory Complementation_Final
imports
  "Complementation_Implement"
  "Transition_Systems_and_Automata.BA_Translate"
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

  term list_map_rel
  definition state_hash :: "nat \<Rightarrow> (nat \<times> item) list \<Rightarrow> nat" where
    "state_hash n p \<equiv> undefined"

  (* TODO: bot is a terrible hash function *)
  lemma [autoref_ga_rules]: "is_bounded_hashcode
    state_rel
    (gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list)) (list_map_lookup HOL.eq) (prod_eq HOL.eq HOL.eq))
    bot"
    apply rule
    subgoal by autoref
    subgoal unfolding bot_fun_def bot_nat_def by simp
    subgoal unfolding bot_fun_def bot_nat_def by simp
    done

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
      then (if a = ''a'' then [0, 1] else [1])
      else (if a = ''a'' then [1] else [])"
  definition Ai where
    "Ai \<equiv> \<lparr> alphabeti = [''a'', ''b''], initiali = [0], succi = s, acceptingi = \<lambda> p. False \<rparr>"

  (* TODO: look through code
    - equality on maps needs a lot of lookups, make sure those are fast,
    - make sure we don't use slow generic algorithms when fast specializations are possible *)
  (* TODO: the reachability analysis should only be done once *)
  export_code complement_impl in SML module_name Complementation

  (* TODO: is it supposed to be this many states/transitions?
    make sure that we generate only one representative per equivalence class (maybe prove?)
    maybe we can also do some crude optimizations *)
  value "length (transei (complement_impl Ai))"
  value "length (remdups (map fst (transei (complement_impl Ai))))"

end