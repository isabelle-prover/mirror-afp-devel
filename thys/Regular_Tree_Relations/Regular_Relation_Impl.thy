theory Regular_Relation_Impl
  imports Tree_Automata_Impl
    Regular_Relation_Abstract_Impl
    Horn_Fset
begin

section \<open>Computing the epsilon transitions for the composition of GTT's\<close>

definition \<Delta>\<^sub>\<epsilon>_infer0_cont where
  "\<Delta>\<^sub>\<epsilon>_infer0_cont \<Delta>\<^sub>A \<Delta>\<^sub>B =
    (let arules = filter (\<lambda> r. r_lhs_states r = []) (sorted_list_of_fset \<Delta>\<^sub>A) in
     let brules = filter (\<lambda> r. r_lhs_states r = []) (sorted_list_of_fset \<Delta>\<^sub>B) in
    (map (map_prod r_rhs r_rhs) (filter (\<lambda>(ra, rb). r_root ra = r_root rb) (List.product arules brules))))"

definition \<Delta>\<^sub>\<epsilon>_infer1_cont where
  "\<Delta>\<^sub>\<epsilon>_infer1_cont \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> =
   (let (arules, aeps) = (sorted_list_of_fset \<Delta>\<^sub>A, sorted_list_of_fset \<Delta>\<^sub>A\<^sub>\<epsilon>) in
    let (brules, beps) = (sorted_list_of_fset \<Delta>\<^sub>B, sorted_list_of_fset \<Delta>\<^sub>B\<^sub>\<epsilon>) in
    let prules = List.product arules brules in
   (\<lambda> pq bs.
      map (map_prod r_rhs r_rhs) (filter (\<lambda>(ra, rb). case (ra, rb) of (TA_rule f ps p, TA_rule g qs q) \<Rightarrow>
        f = g \<and> length ps = length qs \<and> (fst pq, snd pq) \<in> set (zip ps qs) \<and>
        set (zip ps qs) \<subseteq> insert (fst pq, snd pq) (fset bs)) prules) @
      map (\<lambda>(p, p'). (p', snd pq)) (filter (\<lambda>(p, p') \<Rightarrow> p = fst pq) aeps) @
      map (\<lambda>(q, q'). (fst pq, q')) (filter (\<lambda>(q, q') \<Rightarrow> q = snd pq) beps)))"


locale \<Delta>\<^sub>\<epsilon>_fset =
  fixes \<Delta>\<^sub>A :: "('q :: linorder, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>A\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
    and \<Delta>\<^sub>B :: "('q, 'f) ta_rule fset" and \<Delta>\<^sub>B\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
begin

abbreviation A where "A \<equiv> TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>"
abbreviation B where "B \<equiv> TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>"

sublocale \<Delta>\<^sub>\<epsilon>_horn A B .

sublocale l: horn_fset "\<Delta>\<^sub>\<epsilon>_rules A B" "\<Delta>\<^sub>\<epsilon>_infer0_cont \<Delta>\<^sub>A \<Delta>\<^sub>B" "\<Delta>\<^sub>\<epsilon>_infer1_cont \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>"
  apply (unfold_locales)
  unfolding \<Delta>\<^sub>\<epsilon>_horn.\<Delta>\<^sub>\<epsilon>_infer0 \<Delta>\<^sub>\<epsilon>_horn.\<Delta>\<^sub>\<epsilon>_infer1 \<Delta>\<^sub>\<epsilon>_infer0_cont_def \<Delta>\<^sub>\<epsilon>_infer1_cont_def set_append Un_assoc[symmetric]
  unfolding sorted_list_of_fset_simps union_fset
  subgoal
    apply (auto split!: prod.splits ta_rule.splits simp: comp_def fset_of_list_elem r_rhs_def
       map_prod_def fSigma.rep_eq image_def Bex_def)
    apply (metis ta_rule.exhaust_sel)
    done
  unfolding Let_def prod.case set_append Un_assoc
  apply (intro arg_cong2[of _ _ _ _ "(\<union>)"])
  subgoal
    apply (auto split!: prod.splits ta_rule.splits)
    apply (smt (verit, del_insts) Pair_inject map_prod_imageI mem_Collect_eq ta_rule.inject ta_rule.sel(3))
    done
by (force simp add: image_def split!: prod.splits)+

lemmas infer = l.infer0 l.infer1
lemmas saturate_impl_sound = l.saturate_impl_sound
lemmas saturate_impl_complete = l.saturate_impl_complete

end

definition \<Delta>\<^sub>\<epsilon>_impl where
  "\<Delta>\<^sub>\<epsilon>_impl \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> = horn_fset_impl.saturate_impl (\<Delta>\<^sub>\<epsilon>_infer0_cont \<Delta>\<^sub>A \<Delta>\<^sub>B) (\<Delta>\<^sub>\<epsilon>_infer1_cont \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>)"

lemma \<Delta>\<^sub>\<epsilon>_impl_sound:
  assumes "\<Delta>\<^sub>\<epsilon>_impl \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> = Some xs"
  shows "xs = \<Delta>\<^sub>\<epsilon> (TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>) (TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>)"
  using \<Delta>\<^sub>\<epsilon>_fset.saturate_impl_sound[OF assms[unfolded \<Delta>\<^sub>\<epsilon>_impl_def]]
  unfolding \<Delta>\<^sub>\<epsilon>_horn.\<Delta>\<^sub>\<epsilon>_sound[symmetric]
  by (auto simp flip: \<Delta>\<^sub>\<epsilon>.rep_eq)

lemma \<Delta>\<^sub>\<epsilon>_impl_complete:
  fixes \<Delta>\<^sub>A :: "('q :: linorder, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>B :: "('q, 'f) ta_rule fset"
    and \<Delta>\<^sub>\<epsilon>\<^sub>A :: "('q \<times> 'q) fset" and \<Delta>\<^sub>\<epsilon>\<^sub>B :: "('q \<times> 'q) fset"
  shows "\<Delta>\<^sub>\<epsilon>_impl \<Delta>\<^sub>A \<Delta>\<^sub>\<epsilon>\<^sub>A \<Delta>\<^sub>B \<Delta>\<^sub>\<epsilon>\<^sub>B \<noteq> None" unfolding \<Delta>\<^sub>\<epsilon>_impl_def
  by (intro \<Delta>\<^sub>\<epsilon>_fset.saturate_impl_complete)
     (auto simp flip: \<Delta>\<^sub>\<epsilon>_horn.\<Delta>\<^sub>\<epsilon>_sound)

lemma \<Delta>\<^sub>\<epsilon>_impl [code]:
  "\<Delta>\<^sub>\<epsilon> (TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>) (TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>) = the (\<Delta>\<^sub>\<epsilon>_impl \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>)"
  using \<Delta>\<^sub>\<epsilon>_impl_complete[of \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>] \<Delta>\<^sub>\<epsilon>_impl_sound[of \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>]
  by force

section \<open>Computing the epsilon transitions for the transitive closure of GTT's\<close>

definition \<Delta>_trancl_infer0 where
  "\<Delta>_trancl_infer0 \<Delta>\<^sub>A \<Delta>\<^sub>B = \<Delta>\<^sub>\<epsilon>_infer0_cont \<Delta>\<^sub>A \<Delta>\<^sub>B"

definition \<Delta>_trancl_infer1 :: "('q :: linorder , 'f  :: linorder) ta_rule fset \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow>  ('q, 'f) ta_rule fset \<Rightarrow> ('q \<times> 'q) fset
  \<Rightarrow> 'q \<times> 'q \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> ('q \<times> 'q) list" where
  "\<Delta>_trancl_infer1 \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> pq bs =
    \<Delta>\<^sub>\<epsilon>_infer1_cont \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> pq bs @
    sorted_list_of_fset (
      (\<lambda>(r, p'). (r, snd pq)) |`| (ffilter (\<lambda>(r, p') \<Rightarrow> p' = fst pq) bs) |\<union>|
      (\<lambda>(q', r). (fst pq, r)) |`| (ffilter (\<lambda>(q', r) \<Rightarrow> q' = snd pq) (finsert pq bs)))"

locale \<Delta>_trancl_list =
  fixes \<Delta>\<^sub>A :: "('q :: linorder, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>A\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
    and \<Delta>\<^sub>B :: "('q, 'f) ta_rule fset" and \<Delta>\<^sub>B\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
begin

abbreviation A where "A \<equiv> TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>"
abbreviation B where "B \<equiv> TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>"

sublocale \<Delta>_trancl_horn A B .

sublocale l: horn_fset "\<Delta>_trancl_rules A B"
   "\<Delta>_trancl_infer0 \<Delta>\<^sub>A \<Delta>\<^sub>B" "\<Delta>_trancl_infer1 \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>"
  apply (unfold_locales)
  unfolding \<Delta>_trancl_rules_def horn_infer0_union horn_infer1_union
    \<Delta>_trancl_infer0_def \<Delta>_trancl_infer1_def \<Delta>\<^sub>\<epsilon>_fset.infer set_append
  by (auto simp flip: ex_simps(1) simp: horn.infer0_def horn.infer1_def intro!: arg_cong2[of _ _ _ _ "(\<union>)"])

lemmas saturate_impl_sound = l.saturate_impl_sound
lemmas saturate_impl_complete = l.saturate_impl_complete

end

definition "\<Delta>_trancl_impl \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> =
   horn_fset_impl.saturate_impl (\<Delta>_trancl_infer0 \<Delta>\<^sub>A \<Delta>\<^sub>B) (\<Delta>_trancl_infer1 \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>)"

lemma \<Delta>_trancl_impl_sound:
  assumes "\<Delta>_trancl_impl \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> = Some xs"
  shows "xs = \<Delta>_trancl (TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>) (TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>)"
  using \<Delta>_trancl_list.saturate_impl_sound[OF assms[unfolded \<Delta>_trancl_impl_def]]
  unfolding \<Delta>_trancl_horn.\<Delta>_trancl_sound[symmetric] \<Delta>_trancl.rep_eq[symmetric]
  by auto

lemma \<Delta>_trancl_impl_complete:
  fixes \<Delta>\<^sub>A :: "('q :: linorder, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>B :: "('q, 'f) ta_rule fset"
    and \<Delta>\<^sub>A\<^sub>\<epsilon> :: "('q \<times> 'q) fset" and \<Delta>\<^sub>B\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
  shows "\<Delta>_trancl_impl \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> \<noteq> None"
  unfolding \<Delta>_trancl_impl_def
  by (intro \<Delta>_trancl_list.saturate_impl_complete)
     (auto simp flip: \<Delta>_trancl_horn.\<Delta>_trancl_sound)

lemma \<Delta>_trancl_impl [code]:
  "\<Delta>_trancl (TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>) (TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>) = (the (\<Delta>_trancl_impl \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>))"
  using \<Delta>_trancl_impl_complete[of \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>]
  using \<Delta>_trancl_impl_sound[of \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>]
  by force

section \<open>Computing the epsilon transitions for the transitive closure of pair automata\<close>

definition \<Delta>_Atr_infer1_cont :: "('q :: linorder \<times> 'q) fset \<Rightarrow> ('q, 'f :: linorder) ta_rule fset \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow>
  ('q, 'f) ta_rule fset \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> 'q \<times> 'q \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> ('q \<times> 'q) list" where
  "\<Delta>_Atr_infer1_cont Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> =
  (let G = sorted_list_of_fset (the (\<Delta>\<^sub>\<epsilon>_impl \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>)) in
  (\<lambda> pq bs.
    (let bs_list = sorted_list_of_fset bs in
      map (\<lambda> (p, q). (fst p, snd pq))  (filter (\<lambda> (p, q). snd p = fst q \<and> snd q = fst pq) (List.product bs_list G)) @
      map (\<lambda> (p, q). (fst pq, snd q))  (filter (\<lambda> (p, q). snd p = fst q \<and> fst p = snd pq) (List.product G bs_list)) @
      map (\<lambda> (p, q). (fst pq, snd pq)) (filter (\<lambda> (p, q). snd pq = p \<and> fst pq = q) G))))"

locale \<Delta>_Atr_fset =
  fixes Q :: "('q :: linorder \<times> 'q) fset" and  \<Delta>\<^sub>A :: "('q, 'f :: linorder) ta_rule fset" and \<Delta>\<^sub>A\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
    and \<Delta>\<^sub>B :: "('q, 'f) ta_rule fset" and \<Delta>\<^sub>B\<^sub>\<epsilon> :: "('q \<times> 'q) fset"
begin

abbreviation A where "A \<equiv> TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>"
abbreviation B where "B \<equiv> TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>"

sublocale \<Delta>_Atr_horn Q A B .

lemma infer1:
  "infer1 pq (fset bs) = set (\<Delta>_Atr_infer1_cont Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> pq bs)"
proof -
  have "{(p, snd pq) | p q. (p, q) \<in> (fset bs) \<and> (q, fst pq) |\<in>| \<Delta>\<^sub>\<epsilon> B A} \<union>
   {(fst pq, v) | q r v. (snd pq, r) |\<in>| \<Delta>\<^sub>\<epsilon> B A \<and> (r, v) \<in> (fset bs)} \<union>
   {(fst pq, snd pq) | q . (snd pq, fst pq) |\<in>| \<Delta>\<^sub>\<epsilon> B A} = set (\<Delta>_Atr_infer1_cont Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> pq bs)"
    unfolding \<Delta>_Atr_infer1_cont_def set_append Un_assoc[symmetric] Let_def
    unfolding sorted_list_of_fset_simps union_fset
    apply (intro arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (simp_all add: fSigma_repeq flip: \<Delta>\<^sub>\<epsilon>_impl fset_of_list_elem)
    apply force+
    done
  then show ?thesis
    using \<Delta>_Atr_horn.\<Delta>_Atr_infer1[of Q A B pq "fset bs"]
    by simp
qed

sublocale l: horn_fset "\<Delta>_Atr_rules Q A B" "sorted_list_of_fset Q" "\<Delta>_Atr_infer1_cont Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>"
  apply (unfold_locales)
  unfolding \<Delta>_Atr_horn.\<Delta>_Atr_infer0 fset_of_list.rep_eq
  using infer1
  by auto

lemmas infer = l.infer0 l.infer1
lemmas saturate_impl_sound = l.saturate_impl_sound
lemmas saturate_impl_complete = l.saturate_impl_complete

end

definition "\<Delta>_Atr_impl Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> =
   horn_fset_impl.saturate_impl (sorted_list_of_fset Q) (\<Delta>_Atr_infer1_cont Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>)"

lemma \<Delta>_Atr_impl_sound:
  assumes "\<Delta>_Atr_impl Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> = Some xs"
  shows "xs = \<Delta>_Atrans Q (TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>) (TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>)"
  using \<Delta>_Atr_fset.saturate_impl_sound[OF assms[unfolded \<Delta>_Atr_impl_def]]
  unfolding \<Delta>_Atr_horn.\<Delta>_Atr_sound[symmetric] \<Delta>_Atrans.rep_eq[symmetric]
  by (simp add: fset_inject)
  
lemma \<Delta>_Atr_impl_complete:
  shows "\<Delta>_Atr_impl Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon> \<noteq> None" unfolding \<Delta>_Atr_impl_def
  by (intro \<Delta>_Atr_fset.saturate_impl_complete)
     (auto simp: finite_\<Delta>_Atrans_set simp flip: \<Delta>_Atr_horn.\<Delta>_Atr_sound)

lemma \<Delta>_Atr_impl [code]:
  "\<Delta>_Atrans Q (TA \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon>) (TA \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>) = (the (\<Delta>_Atr_impl Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>))"
  using \<Delta>_Atr_impl_complete[of Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>] \<Delta>_Atr_impl_sound[of Q \<Delta>\<^sub>A \<Delta>\<^sub>A\<^sub>\<epsilon> \<Delta>\<^sub>B \<Delta>\<^sub>B\<^sub>\<epsilon>]
  by force

section \<open>Computing the Q infinity set for the infinity predicate automaton\<close>

definition Q_infer0_cont  :: "('q :: linorder, 'f :: linorder option \<times> 'g :: linorder option) ta_rule fset \<Rightarrow> ('q \<times> 'q) list" where
  "Q_infer0_cont \<Delta> = concat (sorted_list_of_fset (
     (\<lambda> r. case r of TA_rule f ps p \<Rightarrow> map (\<lambda> x. Pair x p) ps) |`|
     (ffilter (\<lambda> r. case r of TA_rule f ps p \<Rightarrow> fst f = None \<and> snd f \<noteq> None \<and> ps \<noteq> []) \<Delta>)))"

definition Q_infer1_cont :: "('q ::linorder \<times> 'q) fset \<Rightarrow> 'q \<times> 'q \<Rightarrow> ('q \<times> 'q) fset \<Rightarrow> ('q \<times> 'q) list" where
  "Q_infer1_cont \<Delta>\<epsilon> =
  (let eps = sorted_list_of_fset \<Delta>\<epsilon> in
  (\<lambda> pq bs.
    let bs_list = sorted_list_of_fset bs in
    map (\<lambda> (q, r). (fst pq, r)) (filter (\<lambda> (q, r) \<Rightarrow> q = snd pq) eps) @
    map (\<lambda>(r, p'). (r, snd pq)) (filter (\<lambda>(r, p') \<Rightarrow> p' = fst pq) bs_list) @
    map (\<lambda>(q', r). (fst pq, r)) (filter (\<lambda>(q', r) \<Rightarrow> q' = snd pq) (pq # bs_list))))"

locale Q_fset =
  fixes \<Delta> :: "('q :: linorder, 'f :: linorder option \<times> 'g :: linorder option) ta_rule fset" and \<Delta>\<epsilon> :: "('q \<times> 'q) fset"
begin

abbreviation A where "A \<equiv> TA \<Delta> \<Delta>\<epsilon>"
sublocale Q_horn A .

sublocale l: horn_fset "Q_inf_rules A" "Q_infer0_cont \<Delta>" "Q_infer1_cont \<Delta>\<epsilon>"
  apply (unfold_locales)
  unfolding Q_horn.Q_infer0 Q_horn.Q_infer1 Q_infer0_cont_def Q_infer1_cont_def set_append Un_assoc[symmetric]
  unfolding sorted_list_of_fset_simps union_fset
  subgoal
    apply (auto simp add: Bex_def split!: ta_rule.splits)
    apply (rule_tac x = "TA_rule (lift_None_Some f) ps p" in exI)
    apply (force dest: in_set_idx)+
    done
  unfolding Let_def set_append Un_assoc
  by (intro arg_cong2[of _ _ _ _ "(\<union>)"]) auto

lemmas saturate_impl_sound = l.saturate_impl_sound
lemmas saturate_impl_complete = l.saturate_impl_complete

end

definition Q_impl where
  "Q_impl \<Delta> \<Delta>\<epsilon> = horn_fset_impl.saturate_impl (Q_infer0_cont \<Delta>) (Q_infer1_cont \<Delta>\<epsilon>)"

lemma Q_impl_sound:
  "Q_impl \<Delta> \<Delta>\<epsilon> = Some xs \<Longrightarrow> fset xs = Q_inf (TA \<Delta> \<Delta>\<epsilon>)"
  using Q_fset.saturate_impl_sound unfolding Q_impl_def Q_horn.Q_sound .

lemma Q_impl_complete:
  "Q_impl \<Delta> \<Delta>\<epsilon> \<noteq> None"
proof -
  let ?A = "TA \<Delta> \<Delta>\<epsilon>"
  have *: "Q_inf ?A \<subseteq> fset (\<Q> ?A |\<times>| \<Q> ?A)"
    by (auto simp add: Q_inf_states_ta_states(1, 2) subrelI)
  have "finite (Q_inf ?A)"
    by (intro finite_subset[OF *]) simp
  then show ?thesis unfolding Q_impl_def
    by (intro Q_fset.saturate_impl_complete) (auto simp: Q_horn.Q_sound)
qed


definition "Q_infinity_impl \<Delta> \<Delta>\<epsilon> = (let Q = the (Q_impl \<Delta> \<Delta>\<epsilon>) in
   snd |`| ((ffilter (\<lambda> (p, q). p = q) Q) |O| Q))"

lemma Q_infinity_impl_fmember:
  "q |\<in>| Q_infinity_impl \<Delta> \<Delta>\<epsilon> \<longleftrightarrow> (\<exists> p. (p, p) |\<in>| the (Q_impl \<Delta> \<Delta>\<epsilon>) \<and>
    (p, q) |\<in>| the (Q_impl \<Delta> \<Delta>\<epsilon>))"
  unfolding Q_infinity_impl_def
  by (auto simp: Let_def image_iff Bex_def) fastforce

lemma loop_sound_correct [simp]:
  "fset (Q_infinity_impl \<Delta> \<Delta>\<epsilon>) = Q_inf_e (TA \<Delta> \<Delta>\<epsilon>)"
proof -
  obtain Q where [simp]: "Q_impl \<Delta> \<Delta>\<epsilon> = Some Q" using Q_impl_complete[of \<Delta> \<Delta>\<epsilon>]
    by blast
  have "fset Q = (Q_inf (TA \<Delta> \<Delta>\<epsilon>))"
    using Q_impl_sound[of \<Delta> \<Delta>\<epsilon>]
    by (auto simp: fset_of_list.rep_eq)
  then show ?thesis
    by (force simp: Q_infinity_impl_fmember Let_def fset_of_list_elem
          fset_of_list.rep_eq)
qed

lemma fQ_inf_e_code [code]:
  "fQ_inf_e (TA \<Delta> \<Delta>\<epsilon>) = Q_infinity_impl \<Delta> \<Delta>\<epsilon>"
  using loop_sound_correct
  by (auto simp add: fQ_inf_e.rep_eq)


end