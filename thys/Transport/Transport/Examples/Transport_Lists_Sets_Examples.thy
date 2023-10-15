\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Example Transports Between Lists and Sets\<close>
theory Transport_Lists_Sets_Examples
  imports
    Transport_Prototype
    Transport_Syntax
    "HOL-Library.FSet"
begin

paragraph \<open>Summary\<close>
text \<open>Introductory examples from \<^cite>\<open>"transport"\<close>.
Transports between lists and (finite) sets. Refer to the paper for more details.\<close>

context
  includes galois_rel_syntax transport_syntax
begin

paragraph \<open>Introductory examples from paper\<close>

text \<open>Left and right relations.\<close>

definition "LFSL xs xs' \<equiv> fset_of_list xs = fset_of_list xs'"
abbreviation (input) "(LFSR :: 'a fset \<Rightarrow> _) \<equiv> (=)"
definition "LSL xs xs' \<equiv> set xs = set xs'"
abbreviation (input) "(LSR :: 'a set \<Rightarrow> _) \<equiv> (=\<^bsub>finite :: 'a set \<Rightarrow> bool\<^esub>)"

interpretation t : transport LSL R l r for LSL R l r .

text \<open>Proofs of equivalences.\<close>

lemma list_fset_PER [per_intro]: "(LFSL \<equiv>\<^bsub>PER\<^esub> LFSR) fset_of_list sorted_list_of_fset"
  unfolding LFSL_def by fastforce

lemma list_set_PER [per_intro]: "(LSL \<equiv>\<^bsub>PER\<^esub> LSR) set sorted_list_of_set"
  unfolding LSL_def by fastforce

text \<open>We can rewrite the Galois relators in the following theorems to the relator of the paper.\<close>

definition "LFS xs s \<equiv> fset_of_list xs = s"
definition "LS xs s \<equiv> set xs = s"

lemma LFSL_Galois_eq_LFS: "(\<^bsub>LFSL\<^esub>\<lessapprox>\<^bsub>LFSR sorted_list_of_fset\<^esub>) \<equiv> LFS"
  unfolding LFS_def LFSL_def by (intro eq_reflection ext) (auto)
lemma LFSR_Galois_eq_inv_LFS: "(\<^bsub>LFSR\<^esub>\<lessapprox>\<^bsub>LFSL fset_of_list\<^esub>) \<equiv> LFS\<inverse>"
  unfolding LFS_def LFSL_def by (intro eq_reflection ext) (auto)
lemma LSL_Galois_eq_LS: "(\<^bsub>LSL\<^esub>\<lessapprox>\<^bsub>LSR sorted_list_of_set\<^esub>) \<equiv> LS"
  unfolding LS_def LSL_def by (intro eq_reflection ext) (auto)

declare LFSL_Galois_eq_LFS[trp_relator_rewrite, trp_uhint]
  LFSR_Galois_eq_inv_LFS[trp_relator_rewrite, trp_uhint]
  LSL_Galois_eq_LS[trp_relator_rewrite, trp_uhint]

definition "max_list xs \<equiv> foldr max xs (0 :: nat)"

text \<open>Proof of parametricity for @{term max_list}.\<close>

lemma max_max_list_removeAll_eq_maxlist:
  assumes "x \<in> set xs"
  shows "max x (max_list (removeAll x xs)) = max_list xs"
  unfolding max_list_def using assms by (induction xs)
  (simp_all, (metis max.left_idem removeAll_id max.left_commute)+)

lemma max_list_parametric [trp_in_dom]: "(LSL \<Rrightarrow> (=)) max_list max_list"
proof (intro Dep_Fun_Rel_relI)
  fix xs xs' :: "nat list" assume "LSL xs xs'"
  then have "finite (set xs)" "set xs = set xs'" unfolding LSL_def by auto
  then show "max_list xs = max_list xs'"
  proof (induction "set xs"  arbitrary: xs xs' rule: finite_induct)
    case (insert x F)
    then have "F = set (removeAll x xs)" by auto
    moreover from insert have "... = set (removeAll x xs')" by auto
    ultimately have "max_list (removeAll x xs) = max_list (removeAll x xs')"
      (is "?lhs = ?rhs") using insert by blast
    then have "max x ?lhs = max x ?rhs" by simp
    then show ?case
      using insert max_max_list_removeAll_eq_maxlist insertI1 by metis
  qed auto
qed

lemma LFSL_eq_LSL: "LFSL \<equiv> LSL"
  unfolding LFSL_def LSL_def by (intro eq_reflection ext) (auto simp: fset_of_list_elem)

lemma max_list_parametricfin [trp_in_dom]: "(LFSL \<Rrightarrow> (=)) max_list max_list"
  using max_list_parametric by (simp only: LFSL_eq_LSL)

text \<open>Transport from lists to finite sets.\<close>

trp_term max_fset :: "nat fset \<Rightarrow> nat" where x = max_list
  and L = "(LFSL \<Rrightarrow> (=))"
  by trp_prover

text \<open>Use @{command print_theorems} to show all theorems. Here's the correctness theorem:\<close>
lemma "(LFS \<Rrightarrow> (=)) max_list max_fset" by (trp_hints_resolve max_fset_related')

lemma [trp_in_dom]: "(LFSR \<Rrightarrow> (=)) max_fset max_fset" by simp

text \<open>Transport from lists to sets.\<close>

trp_term max_set :: "nat set \<Rightarrow> nat" where x = max_list
  by trp_prover

lemma "(LS \<Rrightarrow> (=)) max_list max_set" by (trp_hints_resolve max_set_related')

text \<open>The registration of symmetric equivalence rules is not done by default as of now,
but that would not be a problem in principle.\<close>

lemma list_fset_PER_sym [per_intro]:
  "(LFSR \<equiv>\<^bsub>PER\<^esub> LFSL) sorted_list_of_fset fset_of_list"
  by (subst transport.partial_equivalence_rel_equivalence_right_left_iff_partial_equivalence_rel_equivalence_left_right)
  (fact list_fset_PER)

text \<open>Transport from finite sets to lists.\<close>

trp_term max_list' :: "nat list \<Rightarrow> nat" where x = max_fset
  by trp_prover

lemma "(LFS\<inverse> \<Rrightarrow> (=)) max_fset max_list'" by (trp_hints_resolve max_list'_related')

text \<open>Transporting higher-order functions.\<close>

lemma map_parametric [trp_in_dom]:
  "(((=) \<Rrightarrow> (=)) \<Rrightarrow> LSL \<Rrightarrow> LSL) map map"
  unfolding LSL_def by (intro Dep_Fun_Rel_relI) simp

lemma [trp_uhint]: "P \<equiv> (=) \<Longrightarrow> P \<equiv> (=) \<Rrightarrow> (=)" by simp
lemma [trp_uhint]: "P \<equiv> \<top> \<Longrightarrow> (=\<^bsub>P :: 'a \<Rightarrow> bool\<^esub>) \<equiv> ((=) :: 'a \<Rightarrow> _)" by simp

(*sorted_list_of_fset requires a linorder, but in theory,
we could use a different transport function to avoid that constraint*)
trp_term map_set :: "('a :: linorder \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('b :: linorder) set"
  where x = "map :: ('a :: linorder \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> ('b :: linorder) list"
  by trp_prover

lemma "(((=) \<Rrightarrow> (=)) \<Rrightarrow> LS \<Rrightarrow> LS) map map_set" by (trp_hints_resolve map_set_related')


lemma filter_parametric [trp_in_dom]:
  "(((=) \<Rrightarrow> (\<longleftrightarrow>)) \<Rrightarrow> LSL \<Rrightarrow> LSL) filter filter"
  unfolding LSL_def by (intro Dep_Fun_Rel_relI) simp

trp_term filter_set :: "('a :: linorder \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where x = "filter :: ('a :: linorder \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  by trp_prover

lemma "(((=) \<Rrightarrow> (=)) \<Rrightarrow> LS \<Rrightarrow> LS) filter filter_set" by (trp_hints_resolve filter_set_related')

lemma append_parametric [trp_in_dom]:
  "(LSL \<Rrightarrow> LSL \<Rrightarrow> LSL) append append"
  unfolding LSL_def by (intro Dep_Fun_Rel_relI) simp

trp_term append_set :: "('a :: linorder) set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where x = "append :: ('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  by trp_prover

lemma "(LS \<Rrightarrow> LS \<Rrightarrow> LS) append append_set" by (trp_hints_resolve append_set_related')

text \<open>The prototype also provides a simplified definition.\<close>
lemma "append_set s s' \<equiv> set (sorted_list_of_set s) \<union> set (sorted_list_of_set s')"
  by (fact append_set_app_eq)

lemma "finite s \<Longrightarrow> finite s' \<Longrightarrow> append_set s s' = s \<union> s'"
  by (auto simp: append_set_app_eq)

end


end
