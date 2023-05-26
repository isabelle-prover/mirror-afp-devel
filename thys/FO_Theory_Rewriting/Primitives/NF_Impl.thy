theory NF_Impl
  imports NF
    Type_Instances_Impl
begin

subsubsection \<open>Implementation of normal form construction\<close>
(* Implementation *)
fun supteq_list :: "('f, 'v) Term.term \<Rightarrow> ('f, 'v) Term.term list"
where
  "supteq_list (Var x) = [Var x]" |
  "supteq_list (Fun f ts) = Fun f ts # concat (map supteq_list ts)"

fun supt_list :: "('f, 'v) Term.term \<Rightarrow> ('f, 'v) Term.term list"
where
  "supt_list (Var x) = []" |
  "supt_list (Fun f ts) = concat (map supteq_list ts)"

lemma supteq_list [simp]:
  "set (supteq_list t) = {s. t \<unrhd> s}"
proof (rule set_eqI, simp)
  fix s
  show "s \<in> set(supteq_list t) = (t \<unrhd> s)"
  proof (induct t, simp add: supteq_var_imp_eq)
    case (Fun f ss)
    show ?case
    proof (cases "Fun f ss = s", (auto)[1])
      case False
      show ?thesis
      proof
        assume "Fun f ss \<unrhd> s"
        with False have sup: "Fun f ss \<rhd> s" using supteq_supt_conv by auto
        obtain C where "C \<noteq> \<box>" and "Fun f ss = C\<langle>s\<rangle>" using sup by auto
        then obtain b D a where "Fun f ss = Fun f (b @ D\<langle>s\<rangle> # a)" by (cases C, auto)
        then have D: "D\<langle>s\<rangle> \<in> set ss" by auto
        with Fun[OF D] ctxt_imp_supteq[of D s] obtain t where "t \<in> set ss" and "s \<in> set (supteq_list t)" by auto
        then show "s \<in> set (supteq_list (Fun f ss))" by auto
      next
        assume "s \<in> set (supteq_list (Fun f ss))"
        with False obtain t where t: "t \<in> set ss" and "s \<in> set (supteq_list t)" by auto
        with Fun[OF t] have "t \<unrhd> s" by auto
        with t show "Fun f ss \<unrhd> s" by auto
      qed
    qed
  qed
qed

lemma supt_list_sound [simp]:
  "set (supt_list t) = {s. t \<rhd> s}"
  by (cases t) auto

fun mergeP_impl where
  "mergeP_impl Bot t = True"
| "mergeP_impl t Bot = True"
| "mergeP_impl (BFun f ss) (BFun g ts) =
  (if f = g \<and> length ss = length ts then list_all (\<lambda> (x, y). mergeP_impl x y) (zip ss ts)  else False)"

lemma [simp]: "mergeP_impl s Bot = True" by (cases s) auto 

lemma [simp]: "mergeP_impl s t \<longleftrightarrow> (s, t) \<in> mergeP" (is "?LS = ?RS")
proof
  show "?LS \<Longrightarrow> ?RS"
    by (induct rule: mergeP_impl.induct, auto split: if_splits intro!: step)
      (smt length_zip list_all_length mergeP.step min_less_iff_conj nth_mem nth_zip old.prod.case)
next
  show "?RS \<Longrightarrow> ?LS" by (induct rule: mergeP.induct, auto simp add: list_all_length)
qed

fun bless_eq_impl where
  "bless_eq_impl Bot t = True"
| "bless_eq_impl (BFun f ss) (BFun g ts) =
  (if f = g \<and> length ss = length ts then list_all (\<lambda> (x, y). bless_eq_impl x y) (zip ss ts) else False)"
| "bless_eq_impl _ _ = False"


lemma [simp]: "bless_eq_impl s t \<longleftrightarrow> (s, t) \<in> bless_eq" (is "?RS = ?LS")
proof
  show "?LS \<Longrightarrow> ?RS" by (induct rule: bless_eq.induct, auto simp add: list_all_length)
next
  show "?RS \<Longrightarrow> ?LS"
    by (induct rule: bless_eq_impl.induct, auto split: if_splits intro!: bless_eq.step)
      (metis (full_types) length_zip list_all_length min_less_iff_conj nth_mem nth_zip old.prod.case)
qed

definition "psubt_bot_impl R \<equiv> remdups (map term_to_bot_term (concat (map supt_list R)))"
lemma psubt_bot_impl[simp]: "set (psubt_bot_impl R) = psubt_lhs_bot (set R)"
  by (induct R, auto simp: psubt_bot_impl_def)

definition "states_impl R = List.insert Bot (map the (removeAll None
    (closure_impl (lift_f_total mergeP_impl (\<up>)) (map Some (psubt_bot_impl R)))))"

lemma states_impl [simp]: "set (states_impl R) = states (set R)"
proof -
  have [simp]: "lift_f_total mergeP_impl (\<up>) = lift_f_total (\<lambda> x y. mergeP_impl x y) (\<up>)" by blast
  show ?thesis unfolding states_impl_def states_def
    using lift_total.cl.closure_impl
    by (simp add: lift_total.cl.pred_closure_lift_closure) 
qed

abbreviation check_intance_lhs where
  "check_intance_lhs qs f R \<equiv> list_all (\<lambda> u. \<not> bless_eq_impl u (BFun f qs)) R"

definition min_elem where
  "min_elem s ss = (let ts = filter (\<lambda> x. bless_eq_impl x s) ss in
      foldr (\<up>) ts Bot)"

lemma bound_impl [simp, code]:
  "bound_max s (set ss) = min_elem s ss"
proof -
  have [simp]: "{y. lift_total.lifted_less_eq y (Some s) \<and> y \<in> Some ` set ss} = Some ` {x \<in> set ss. x \<le>\<^sub>b s}"
    by auto
  then show ?thesis
    using lift_total.supremum_impl[of "filter (\<lambda> x. bless_eq_impl x s) ss"]
    using lift_total.supremum_smaller_exists_unique[of "set ss" s]
    by (auto simp: min_elem_def Let_def lift_total.lift_ord.smaller_subset_def)
qed


definition nf_rule_impl where
  "nf_rule_impl S R SR h = (let (f, n) = h in
     let states = List.n_lists n S in
     let nlhs_inst = filter (\<lambda> qs. check_intance_lhs qs f R) states in
     map (\<lambda> qs. TA_rule f qs (min_elem (BFun f qs) SR)) nlhs_inst)"

abbreviation nf_rules_impl where
  "nf_rules_impl R \<F> \<equiv> concat (map (nf_rule_impl (states_impl R) (map term_to_bot_term R) (psubt_bot_impl R)) \<F>)"

(* Section proves that the implementation constructs the same rule set *)

lemma nf_rules_in_impl:
  assumes "TA_rule f qs q |\<in>| nf_rules (fset_of_list R) (fset_of_list \<F>)"
  shows "TA_rule f qs q |\<in>| fset_of_list (nf_rules_impl R \<F>)"
proof -
  have funas: "(f, length qs) \<in> set \<F>" and st: "fset_of_list qs |\<subseteq>| fstates (fset_of_list R)"
   and nlhs: "\<not>(\<exists> s \<in> (set R). s\<^sup>\<bottom> \<le>\<^sub>b BFun f qs)"
   and min: "q = bound_max (BFun f qs) (psubt_lhs_bot (set R))"
    using assms by (auto simp add: nf_rules_fmember simp flip: fset_of_list_elem)
  then have st_impl: "qs |\<in>| fset_of_list (List.n_lists (length qs) (states_impl R))"
    by (auto simp add: fset_of_list_elem subset_code(1) set_n_lists
        fset_of_list.rep_eq less_eq_fset.rep_eq fstates.rep_eq)
  from nlhs have nlhs_impl: "check_intance_lhs qs f (map term_to_bot_term R)"
    by (auto simp: list.pred_set)
  have min_impl: "q = min_elem (BFun f qs) (psubt_bot_impl R)"
    using bound_impl min
    by (auto simp flip: psubt_bot_impl)
  then show ?thesis using funas nlhs_impl funas st_impl unfolding nf_rule_impl_def
    by (auto simp: fset_of_list_elem)
qed


lemma nf_rules_impl_in_rules:
  assumes "TA_rule f qs q |\<in>| fset_of_list (nf_rules_impl R \<F>)"
  shows "TA_rule f qs q |\<in>| nf_rules (fset_of_list R) (fset_of_list \<F>)"
proof -
  have funas: "(f, length qs) \<in> set \<F>"
   and st_impl: "qs |\<in>| fset_of_list (List.n_lists (length qs) (states_impl R))"
   and nlhs_impl: "check_intance_lhs qs f (map term_to_bot_term R)"
   and min: "q = min_elem (BFun f qs) (psubt_bot_impl R)" using assms
    by (auto simp add: set_n_lists nf_rule_impl_def fset_of_list_elem)    
  from st_impl have st: "fset_of_list qs |\<subseteq>| fstates (fset_of_list R)"
    by (force simp: set_n_lists fset_of_list_elem fstates.rep_eq fset_of_list.rep_eq)
  from nlhs_impl have nlhs: "\<not>(\<exists> l \<in> (set R). l\<^sup>\<bottom> \<le>\<^sub>b BFun f qs)"
    by auto (metis (no_types, lifting) Ball_set_list_all in_set_idx length_map nth_map nth_mem)
  have "q = bound_max (BFun f qs) (psubt_lhs_bot (set R))"
    using bound_impl min
    by (auto simp flip: psubt_bot_impl)
  then show ?thesis using funas st nlhs
    by (auto simp add: nf_rules_fmember fset_of_list_elem fset_of_list.rep_eq)
qed

lemma rule_set_eq:
  shows "nf_rules (fset_of_list R) (fset_of_list \<F>) = fset_of_list (nf_rules_impl R \<F>)" (is "?Ls = ?Rs")
proof -
  {fix r assume "r |\<in>| ?Ls" then have "r |\<in>| ?Rs"
      using nf_rules_in_impl[where ?R = R and ?\<F> = \<F>]
      by (cases r) auto}
  moreover
  {fix r assume "r |\<in>| ?Rs" then have "r |\<in>| ?Ls"
      using nf_rules_impl_in_rules[where ?R = R and ?\<F> = \<F>]
      by (cases r) auto}
  ultimately show ?thesis by blast
qed

(* Code equation for normal form TA *)

lemma fstates_code[code]:
  "fstates R = fset_of_list (states_impl (sorted_list_of_fset R))"
  by (auto simp: fstates.rep_eq fset_of_list.rep_eq)

lemma nf_ta_code [code]:
  "nf_ta R \<F> = TA (fset_of_list (nf_rules_impl (sorted_list_of_fset R) (sorted_list_of_fset \<F>))) {||}"
  unfolding nf_ta_def using rule_set_eq[of "sorted_list_of_fset R" "sorted_list_of_fset \<F>"]
  by (intro TA_equalityI) auto

(*
export_code nf_ta in Haskell
*)

end