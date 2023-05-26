theory Tree_Automata_Impl
  imports Tree_Automata_Abstract_Impl
   "HOL-Library.List_Lexorder"
   "HOL-Library.AList_Mapping"
   Tree_Automata_Class_Instances_Impl
   Containers.Containers
begin

definition map_val_of_list :: "('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c list) \<Rightarrow> 'b list \<Rightarrow> ('a, 'c list) mapping" where
  "map_val_of_list ek ev xs = foldr (\<lambda>x m. Mapping.update (ek x) (ev x @ case_option Nil id (Mapping.lookup m (ek x))) m) xs Mapping.empty"

abbreviation "map_of_list ek ev xs \<equiv> map_val_of_list ek (\<lambda> x. [ev x]) xs"

lemma map_val_of_list_tabulate_conv:
  "map_val_of_list ek ev xs = Mapping.tabulate (sort (remdups (map ek xs))) (\<lambda> k. concat (map ev (filter (\<lambda> x. k = ek x) xs)))"
  unfolding map_val_of_list_def
proof (induct xs)
  case (Cons x xs) then show ?case
    by (intro mapping_eqI) (auto simp: lookup_combine lookup_update' lookup_empty lookup_tabulate image_iff)
qed (simp add: empty_Mapping tabulate_Mapping)

lemmas map_val_of_list_simp = map_val_of_list_tabulate_conv lookup_tabulate
subsection \<open>Setup for the list implementation of reachable states\<close>

definition reach_infer0_cont where
  "reach_infer0_cont \<Delta> =
     map r_rhs (filter (\<lambda> r. case r of TA_rule f ps p \<Rightarrow> ps = []) (sorted_list_of_fset \<Delta>))"

definition reach_infer1_cont :: "('q :: linorder, 'f :: linorder) ta_rule fset \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> 'q \<Rightarrow> 'q fset \<Rightarrow> 'q list" where
  "reach_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon> =
    (let rules = sorted_list_of_fset \<Delta> in
     let eps   = sorted_list_of_fset \<Delta>\<^sub>\<epsilon> in
     let mapp_r = map_val_of_list fst snd (concat (map (\<lambda> r. map (\<lambda> q. (q, [r])) (r_lhs_states r)) rules)) in
     let mapp_e = map_of_list fst snd eps in
    (\<lambda> p bs.
    (map r_rhs (filter (\<lambda> r. case r of TA_rule f qs q \<Rightarrow>
      fset_of_list qs |\<subseteq>| finsert p bs) (case_option Nil id (Mapping.lookup mapp_r p)))) @
      case_option Nil id (Mapping.lookup mapp_e p)))"

locale reach_rules_fset =
  fixes \<Delta> :: "('q :: linorder, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
begin

sublocale reach_horn "TA \<Delta> \<Delta>\<^sub>\<epsilon>" .

lemma infer1:
  "infer1 p (fset bs) = set (reach_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon> p bs)"
  unfolding reach_infer1 reach_infer1_cont_def set_append Un_assoc[symmetric] Let_def
  unfolding sorted_list_of_fset_simps union_fset
  apply (intro arg_cong2[of _ _ _ _ "(\<union>)"])
  subgoal
    apply (auto simp: fset_of_list_elem less_eq_fset.rep_eq fset_of_list.rep_eq image_iff
      map_val_of_list_simp split!: ta_rule.splits)
    apply (metis list.set_intros(1) ta_rule.sel(2, 3))
    apply (metis in_set_simps(2) ta_rule.exhaust_sel)
    done
  subgoal
    apply (simp add: image_def Bex_def map_val_of_list_simp)
    done
  done

sublocale l: horn_fset "reach_rules (TA \<Delta> \<Delta>\<^sub>\<epsilon>)" "reach_infer0_cont \<Delta>" "reach_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon>"
  apply (unfold_locales)
  unfolding reach_infer0 reach_infer0_cont_def
  subgoal
    apply (auto simp: image_iff ta_rule.case_eq_if Bex_def fset_of_list_elem)
    apply force
    apply (metis ta_rule.collapse)+
    done
  subgoal using infer1
    apply blast
    done
  done

lemmas infer = l.infer0 l.infer1
lemmas saturate_impl_sound = l.saturate_impl_sound
lemmas saturate_impl_complete = l.saturate_impl_complete

end

definition "reach_cont_impl \<Delta> \<Delta>\<^sub>\<epsilon> =
   horn_fset_impl.saturate_impl (reach_infer0_cont \<Delta>) (reach_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon>)"

lemma reach_fset_impl_sound:
  "reach_cont_impl \<Delta> \<Delta>\<^sub>\<epsilon> = Some xs \<Longrightarrow> fset xs = ta_reach (TA \<Delta> \<Delta>\<^sub>\<epsilon>)"
  using reach_rules_fset.saturate_impl_sound unfolding reach_cont_impl_def
  unfolding reach_horn.reach_sound .

lemma reach_fset_impl_complete:
  "reach_cont_impl \<Delta> \<Delta>\<^sub>\<epsilon> \<noteq> None"
proof -
  have "finite (ta_reach (TA \<Delta> \<Delta>\<^sub>\<epsilon>))"
    unfolding ta_reach_reachable by simp
  then show ?thesis unfolding reach_cont_impl_def
    by (intro reach_rules_fset.saturate_impl_complete)
      (auto simp: reach_horn.reach_sound)
qed

lemma reach_impl [code]:
  "ta_reachable (TA \<Delta> \<Delta>\<^sub>\<epsilon>) = the (reach_cont_impl \<Delta> \<Delta>\<^sub>\<epsilon>)"
  using reach_fset_impl_sound[of \<Delta> \<Delta>\<^sub>\<epsilon>]
  by (auto simp add: ta_reach_reachable reach_fset_impl_complete fset_of_list_elem)

subsection \<open>Setup for list implementation of productive states\<close>
definition productive_infer1_cont :: "('q :: linorder, 'f :: linorder) ta_rule fset \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> 'q \<Rightarrow> 'q fset \<Rightarrow> 'q list" where
  "productive_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon> =
    (let rules = sorted_list_of_fset \<Delta> in
     let eps   = sorted_list_of_fset \<Delta>\<^sub>\<epsilon> in
     let mapp_r = map_of_list (\<lambda> r. r_rhs r) r_lhs_states rules in
     let mapp_e = map_of_list snd fst eps in
    (\<lambda> p bs.
     (case_option Nil id (Mapping.lookup mapp_e p)) @
     concat (case_option Nil id (Mapping.lookup mapp_r p))))"

locale productive_rules_fset =
  fixes \<Delta> :: "('q :: linorder, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>\<epsilon> :: "('q \<times> 'q) fset" and P :: "'q fset"
begin

sublocale productive_horn "TA \<Delta> \<Delta>\<^sub>\<epsilon>" P .

lemma infer1:
  "infer1 p (fset bs) = set (productive_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon> p bs)"
  unfolding productive_infer1 productive_infer1_cont_def set_append Un_assoc[symmetric]
  unfolding union_fset sorted_list_of_fset_simps Let_def set_append
  apply (intro arg_cong2[of _ _ _ _ "(\<union>)"])
  subgoal
    by (simp add: image_def Bex_def map_val_of_list_simp)
  subgoal
    apply (auto simp: map_val_of_list_simp image_iff)
    apply (metis ta_rule.sel(2, 3))
    apply (metis ta_rule.collapse)
    done
  done

sublocale l: horn_fset "productive_rules P (TA \<Delta> \<Delta>\<^sub>\<epsilon>)" "sorted_list_of_fset P" "productive_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon>"
  apply (unfold_locales)
  using infer1 productive_infer0 fset_of_list.rep_eq
  by fastforce+

lemmas infer = l.infer0 l.infer1
lemmas saturate_impl_sound = l.saturate_impl_sound
lemmas saturate_impl_complete = l.saturate_impl_complete

end

definition "productive_cont_impl P \<Delta> \<Delta>\<^sub>\<epsilon> =
   horn_fset_impl.saturate_impl (sorted_list_of_fset P) (productive_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon>)"

lemma productive_cont_impl_sound:
  "productive_cont_impl P \<Delta> \<Delta>\<^sub>\<epsilon> = Some xs \<Longrightarrow> fset xs = ta_productive_ind P (TA \<Delta> \<Delta>\<^sub>\<epsilon>)"
  using productive_rules_fset.saturate_impl_sound unfolding productive_cont_impl_def
  unfolding productive_horn.productive_sound .

lemma productive_cont_impl_complete:
  "productive_cont_impl P \<Delta> \<Delta>\<^sub>\<epsilon> \<noteq> None"
proof -
  have "finite (ta_productive_ind  P (TA \<Delta> \<Delta>\<^sub>\<epsilon>))"
    unfolding ta_productive_ind by simp
  then show ?thesis unfolding productive_cont_impl_def
    by (intro productive_rules_fset.saturate_impl_complete)
      (auto simp: productive_horn.productive_sound)
qed

lemma productive_impl [code]:
  "ta_productive P (TA \<Delta> \<Delta>\<^sub>\<epsilon>) = the (productive_cont_impl P \<Delta> \<Delta>\<^sub>\<epsilon>)"
  using productive_cont_impl_complete[of P \<Delta>] productive_cont_impl_sound[of P \<Delta>]
  by (auto simp add: ta_productive_ind fset_of_list_elem)

subsection \<open>Setup for the implementation of power set construction states\<close>


abbreviation "r_statesl r \<equiv> length (r_lhs_states r)"

definition ps_reachable_states_list where
  "ps_reachable_states_list mapp_r mapp_e f ps =
   (let R = filter (\<lambda> r. list_all2 (|\<in>|) (r_lhs_states r) ps)
      (case_option Nil id (Mapping.lookup mapp_r (f, length ps))) in
    let S = map r_rhs R in
    S @ concat (map (case_option Nil id \<circ> Mapping.lookup mapp_e) S))"

lemma ps_reachable_states_list_sound:
  assumes "length ps = n"
  and mapp_r: "case_option Nil id (Mapping.lookup mapp_r (f, n)) =
     filter (\<lambda>r. r_root r = f \<and> r_statesl r = n) (sorted_list_of_fset \<Delta>)"
  and mapp_e: "\<And>p. case_option Nil id (Mapping.lookup mapp_e p) =
     map snd (filter (\<lambda> q. fst q = p) (sorted_list_of_fset (\<Delta>\<^sub>\<epsilon>|\<^sup>+|)))"
  shows "fset_of_list (ps_reachable_states_list mapp_r mapp_e f (map ex ps)) =
   ps_reachable_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>) f (map ex ps)" (is "?Ls = ?Rs")
proof -
  have *: "length ps = n" "length (map ex ps) = n" using assms by auto
  {fix q assume "q |\<in>| ?Ls"
    then obtain qs p where "TA_rule f qs p |\<in>| \<Delta>" "length ps = length qs"
       "list_all2 (|\<in>|) qs (map ex ps)" "p = q \<or> (p, q) |\<in>| \<Delta>\<^sub>\<epsilon>|\<^sup>+|"
      unfolding ps_reachable_states_list_def Let_def comp_def assms(1, 2, 3) *
      by (force simp add: fset_of_list_elem image_iff fBex_def) 
    then have "q |\<in>| ?Rs"
      by (force simp add: ps_reachable_states_fmember image_iff)}
  moreover
    {fix q assume "q |\<in>| ?Rs"
       then obtain qs p where "TA_rule f qs p |\<in>| \<Delta>" "length ps = length qs"
         "list_all2 (|\<in>|) qs (map ex ps)" "p = q \<or> (p, q) |\<in>| \<Delta>\<^sub>\<epsilon>|\<^sup>+|"
         by (auto simp add: ps_reachable_states_fmember list_all2_iff)
       then have "q |\<in>| ?Ls"
         unfolding ps_reachable_states_list_def Let_def * comp_def assms(2, 3)
         by (force simp add: fset_of_list_elem image_iff)}
  ultimately show ?thesis by blast
qed


lemma rule_target_statesI:
  "\<exists> r |\<in>| \<Delta>. r_rhs r = q \<Longrightarrow> q |\<in>| rule_target_states \<Delta>"
  by auto

definition ps_states_infer0_cont :: "('q :: linorder, 'f :: linorder) ta_rule fset \<Rightarrow>
   ('q \<times> 'q) fset \<Rightarrow> 'q FSet_Lex_Wrapper list" where
   "ps_states_infer0_cont \<Delta> \<Delta>\<^sub>\<epsilon> =
     (let sig = filter (\<lambda> r. r_lhs_states r = []) (sorted_list_of_fset \<Delta>) in
        filter (\<lambda> p. ex p \<noteq> {||}) (map (\<lambda> r. Wrapp (ps_reachable_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>) (r_root r) [])) sig))"

definition ps_states_infer1_cont :: "('q :: linorder , 'f :: linorder) ta_rule fset \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow>
   'q FSet_Lex_Wrapper \<Rightarrow> 'q FSet_Lex_Wrapper fset \<Rightarrow> 'q FSet_Lex_Wrapper list" where
  "ps_states_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon> =
    (let sig = remdups (map (\<lambda> r. (r_root r, r_statesl r)) (filter (\<lambda> r. r_lhs_states r \<noteq> []) (sorted_list_of_fset \<Delta>))) in
     let arities = remdups (map snd sig) in
     let etr   = sorted_list_of_fset (\<Delta>\<^sub>\<epsilon>|\<^sup>+|) in
     let mapp_r = map_of_list (\<lambda> r. (r_root r, r_statesl r)) id (sorted_list_of_fset \<Delta>) in
     let mapp_e = map_of_list fst snd etr in
    (\<lambda> p bs.
      (let states = sorted_list_of_fset (finsert p bs) in
       let arity_to_states_map = Mapping.tabulate arities (\<lambda> n. list_of_permutation_element_n p n states) in
       let res = map (\<lambda> (f, n).
         map (\<lambda> s. let rules = the (Mapping.lookup mapp_r (f, n)) in
            Wrapp (fset_of_list (ps_reachable_states_list mapp_r mapp_e f (map ex s))))
           (the (Mapping.lookup arity_to_states_map n)))
          sig in
      filter (\<lambda> p. ex p \<noteq> {||}) (concat res))))"

locale ps_states_fset =
  fixes \<Delta> :: "('q :: linorder, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
begin

sublocale ps_states_horn "TA \<Delta> \<Delta>\<^sub>\<epsilon>" .

lemma infer0: "infer0 = set (ps_states_infer0_cont \<Delta> \<Delta>\<^sub>\<epsilon>)"
  unfolding ps_states_horn.ps_construction_infer0
  unfolding ps_states_infer0_cont_def Let_def
  using ps_reachable_states_fmember
  by (auto simp add: image_def Ball_def Bex_def)
     (metis list_all2_Nil2 ps_reachable_states_fmember ta.sel(1) ta_rule.sel(1, 2))

lemma r_lhs_states_nConst:
  "r_lhs_states r \<noteq> [] \<Longrightarrow> r_statesl r \<noteq> 0" for r by auto


lemma filter_empty_conv':
  "[] = filter P xs \<longleftrightarrow> (\<forall>x\<in>set xs. \<not> P x)"
  by (metis filter_empty_conv)

lemma infer1:
  "infer1 p (fset bs) = set (ps_states_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon> p bs)" (is "?Ls = ?Rs")
proof -
  let ?mapp_r = "map_of_list (\<lambda>r. (r_root r, r_statesl r)) (\<lambda>x. x) (sorted_list_of_fset \<Delta>)"
  let ?mapp_e = "map_of_list fst snd (sorted_list_of_fset (\<Delta>\<^sub>\<epsilon>|\<^sup>+|))"
  have mapr: "case_option Nil id (Mapping.lookup ?mapp_r (f, n)) =
     filter (\<lambda>r. r_root r = f \<and> r_statesl r = n) (sorted_list_of_fset \<Delta>)" for f n
    by (auto simp: map_val_of_list_simp image_iff filter_empty_conv' intro: filter_cong)
  have epsr: "\<And>p. case_option Nil id (Mapping.lookup ?mapp_e p) =
     map snd (filter (\<lambda> q. fst q = p) (sorted_list_of_fset (\<Delta>\<^sub>\<epsilon>|\<^sup>+|)))"
    by (auto simp: map_val_of_list_simp image_iff filter_empty_conv) metis
  have *: "p \<in> set qs \<Longrightarrow> x |\<in>| ps_reachable_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>) f (map ex qs) \<Longrightarrow>
    (\<exists> ps q. TA_rule f ps q |\<in>| \<Delta> \<and> length ps = length qs)" for x f qs
    by (auto simp: ps_reachable_states_fmember list_all2_conv_all_nth)
  {fix q assume "q \<in> ?Ls"
    then obtain f qss where sp: "q = Wrapp (ps_reachable_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>) f (map ex qss))"
      "ps_reachable_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>) f (map ex qss) \<noteq> {||}" "p \<in> set qss" "set qss \<subseteq> insert p (fset bs)"
      by (auto simp add: ps_construction_infer1 ps_reachable_states_fmember)
    from sp(2, 3) obtain ps p' where r: "TA_rule f ps p' |\<in>| \<Delta>" "length ps = length qss" using *
      by blast
    then have mem: "qss \<in> set (list_of_permutation_element_n p (length ps) (sorted_list_of_fset (finsert p bs)))" using sp(2-)
      by (auto simp: list_of_permutation_element_n_iff)
         (meson in_set_idx insertE set_list_subset_eq_nth_conv)
    then have "q \<in> ?Rs" using sp r
      unfolding ps_construction_infer1 ps_states_infer1_cont_def Let_def
      apply (simp add: lookup_tabulate ps_reachable_states_fmember image_iff)
      apply (rule_tac x = "f ps \<rightarrow> p'" in exI)
      apply (auto simp: Bex_def ps_reachable_states_list_sound[OF _ mapr epsr] intro: exI[of _ qss])
      done}
  moreover
  {fix q assume ass: "q \<in> ?Rs"
    then obtain r qss where "r |\<in>| \<Delta>" "r_lhs_states r \<noteq> []" "qss \<in> set (list_of_permutation_element_n p (r_statesl r) (sorted_list_of_fset (finsert p bs)))"
      "q = Wrapp (ps_reachable_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>) (r_root r) (map ex qss))"
      unfolding ps_states_infer1_cont_def Let_def
      by (auto simp add: lookup_tabulate ps_reachable_states_fmember image_iff
         ps_reachable_states_list_sound[OF _ mapr epsr] split: if_splits)
    moreover have "q \<noteq> Wrapp {||}" using ass
      by (auto simp: ps_states_infer1_cont_def Let_def)
    ultimately have "q \<in> ?Ls" unfolding ps_construction_infer1
      apply (auto simp: list_of_permutation_element_n_iff intro!: exI[of _ "r_root r"] exI[of _ qss])
      apply (metis in_set_idx)
      done}
  ultimately show ?thesis by blast
qed


sublocale l: horn_fset "ps_states_rules (TA \<Delta> \<Delta>\<^sub>\<epsilon>)" "ps_states_infer0_cont \<Delta> \<Delta>\<^sub>\<epsilon>" "ps_states_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon>"
  apply (unfold_locales)
  using infer0 infer1
  by fastforce+

lemmas infer = l.infer0 l.infer1
lemmas saturate_impl_sound = l.saturate_impl_sound
lemmas saturate_impl_complete = l.saturate_impl_complete


end

definition "ps_states_fset_impl \<Delta> \<Delta>\<^sub>\<epsilon> =
   horn_fset_impl.saturate_impl (ps_states_infer0_cont \<Delta> \<Delta>\<^sub>\<epsilon>) (ps_states_infer1_cont \<Delta> \<Delta>\<^sub>\<epsilon>)"

lemma ps_states_fset_impl_sound:
  assumes "ps_states_fset_impl \<Delta> \<Delta>\<^sub>\<epsilon> = Some xs"
  shows "xs = ps_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>)"
  using ps_states_fset.saturate_impl_sound[OF assms[unfolded ps_states_fset_impl_def]]
  using ps_states_horn.ps_states_sound[of "TA \<Delta> \<Delta>\<^sub>\<epsilon>"]
  by (auto simp: fset_of_list_elem ps_states.rep_eq fset_of_list.rep_eq)

lemma ps_states_fset_impl_complete:
  "ps_states_fset_impl \<Delta> \<Delta>\<^sub>\<epsilon> \<noteq> None"
proof -
  let ?R = "ps_states (TA \<Delta> \<Delta>\<^sub>\<epsilon>)"
  let ?S = "horn.saturate (ps_states_rules (TA \<Delta> \<Delta>\<^sub>\<epsilon>))"
  have "?S \<subseteq> fset ?R"
    using ps_states_horn.ps_states_sound
    by (simp add: ps_states_horn.ps_states_sound ps_states.rep_eq)
  from finite_subset[OF this] show ?thesis
  unfolding ps_states_fset_impl_def
  by (intro ps_states_fset.saturate_impl_complete) simp
qed

lemma ps_ta_impl [code]:
  "ps_ta (TA \<Delta> \<Delta>\<^sub>\<epsilon>) =
    (let xs = the (ps_states_fset_impl \<Delta> \<Delta>\<^sub>\<epsilon>) in
      TA (ps_rules (TA \<Delta> \<Delta>\<^sub>\<epsilon>) xs) {||})"
  using ps_states_fset_impl_complete
  using ps_states_fset_impl_sound
  unfolding ps_ta_def Let_def
  by (metis option.exhaust_sel)

lemma ps_reg_impl [code]:
  "ps_reg (Reg Q (TA \<Delta> \<Delta>\<^sub>\<epsilon>)) =
    (let xs = the (ps_states_fset_impl \<Delta> \<Delta>\<^sub>\<epsilon>) in
     Reg (ffilter (\<lambda> S. Q |\<inter>| ex S \<noteq> {||}) xs)
         (TA (ps_rules (TA \<Delta> \<Delta>\<^sub>\<epsilon>) xs) {||}))"
  using ps_states_fset_impl_complete[of \<Delta> \<Delta>\<^sub>\<epsilon>]
  using ps_states_fset_impl_sound[of \<Delta> \<Delta>\<^sub>\<epsilon>]
  unfolding ps_reg_def ps_ta_Q\<^sub>f_def Let_def
  unfolding ps_ta_def Let_def
  using eq_ffilter by auto

lemma prod_ta_zip [code]:
  "prod_ta_rules (\<A> :: ('q1 :: linorder, 'f :: linorder) ta) (\<B> :: ('q2 :: linorder, 'f :: linorder) ta) =
   (let sig = sorted_list_of_fset (ta_sig \<A> |\<inter>| ta_sig \<B>) in
    let mapA = map_of_list (\<lambda>r. (r_root r, r_statesl r)) id (sorted_list_of_fset (rules \<A>)) in
    let mapB = map_of_list (\<lambda>r. (r_root r, r_statesl r)) id (sorted_list_of_fset (rules \<B>)) in
    let merge = (\<lambda> (ra, rb). TA_rule (r_root ra) (zip (r_lhs_states ra) (r_lhs_states rb)) (r_rhs ra, r_rhs rb)) in
      fset_of_list (
      concat (map (\<lambda> (f, n). map merge
        (List.product (the (Mapping.lookup mapA (f, n))) (the (Mapping.lookup mapB (f, n))))) sig)))"
 (is "?Ls = ?Rs")
proof -
  have [simp]: "distinct (sorted_list_of_fset (ta_sig \<A>))"  "distinct (sorted_list_of_fset (ta_sig \<B>))"
    by (simp_all add: distinct_sorted_list_of_fset)
  have *: "sort (remdups (map (\<lambda>r. (r_root r, r_statesl r)) (sorted_list_of_fset (rules \<A>)))) = sorted_list_of_fset (ta_sig \<A>)"
   "sort (remdups (map (\<lambda>r. (r_root r, r_statesl r)) (sorted_list_of_fset (rules \<B>)))) = sorted_list_of_fset (ta_sig \<B>)"
     by (auto simp: ta_sig_def sorted_list_of_fset_fimage_dist)
  {fix r assume ass: "r |\<in>| ?Ls"
    then obtain f qs q where [simp]: "r = f qs \<rightarrow> q" by auto
    then have "(f, length qs) |\<in>| ta_sig \<A> |\<inter>| ta_sig \<B>" using ass by auto
    then have "r |\<in>| ?Rs" using ass unfolding map_val_of_list_tabulate_conv *
      by (auto simp: Let_def fset_of_list_elem image_iff case_prod_beta lookup_tabulate intro!: bexI[of _ "(f, length qs)"])
         (metis (no_types, lifting) length_map ta_rule.sel(1 - 3) zip_map_fst_snd)}
    moreover
    {fix r assume ass: "r |\<in>| ?Rs" then have "r |\<in>| ?Ls" unfolding map_val_of_list_tabulate_conv *
        by (auto simp: fset_of_list_elem finite_Collect_prod_ta_rules lookup_tabulate)
           (metis ta_rule.collapse)}
  ultimately show ?thesis by blast
qed

(*
export_code ta_der in Haskell
export_code ta_reachable in Haskell
export_code ta_productive in Haskell
export_code trim_ta in Haskell
export_code ta_restrict in Haskell
export_code ps_reachable_states in Haskell
export_code prod_ta_rules in Haskell
export_code ps_ta in Haskell
export_code ps_reg in Haskell
export_code reg_intersect in Haskell
*)

end