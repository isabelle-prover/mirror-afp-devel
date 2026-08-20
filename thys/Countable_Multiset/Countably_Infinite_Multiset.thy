section \<open>Countably Infinite Multisets\<close>

theory Countably_Infinite_Multiset
imports Countable_Multiset
begin

typedef 'a cinfmset = \<open>{M :: 'a cmset. cminfinite M}\<close>
  by (auto intro!: exI[of _ \<open>cmconst _\<close>])

setup_lifting type_definition_cinfmset

lift_bnf (no_warn_wits) 'a cinfmset
  for map: cinfmimage rel: cinfmrel
  by (auto simp: cminfinite_cmimage)

lift_definition cinfmcount :: \<open>'a cinfmset \<Rightarrow> 'a \<Rightarrow> enat\<close> is cmcount .

context begin
interpretation cmset_as_typedef .
lift_definition cinfmreplace :: \<open>'a cinfmset \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a cinfmset\<close> is cmreplace
  by (rule cminfinite_cmreplace)

lemma set_infmset_alt: \<open>set_cinfmset xs = {a. cinfmcount xs a \<noteq> 0}\<close>
  unfolding set_cinfmset_def cinfmcount_def cmset_alt
  by auto

lemma set_cinfset_cinfmreplace: 
  \<open>set_cinfmset (cinfmreplace M x y) \<subseteq> set_cinfmset M \<union> {y}\<close>
  including cmset.lifting
proof transfer
  fix M :: \<open>'a cmset\<close> and x y
  assume \<open>cminfinite M\<close>
  show \<open>cmset (cmreplace M x y) \<subseteq> cmset M \<union> {y}\<close>
    by transfer auto
qed
end

lemma inj_cinfmcount: \<open>inj cinfmcount\<close>
  unfolding inj_on_def cinfmcount_def map_fun_def o_apply id_apply
  by (simp add: Rep_cinfmset_inject inj_cmcount inj_eq)

lemma in_range_cinfmcount:
  \<open>countable {x. f x \<noteq> 0} \<Longrightarrow> (\<exists>x. f x = \<infinity>) \<or> infinite {x. f x \<noteq> 0} \<Longrightarrow> f \<in> range cinfmcount\<close>
  by (drule in_range_cmcount) (smt (verit, best) Collect_cong Rep_cinfmset_cases UNIV_I cinfmcount.rep_eq cminfinite_alt image_iff mem_Collect_eq)

lemma cinfmcount_cinfmimage[simp]: 
  \<open>cinfmcount (cinfmimage f M) b = isum (cinfmcount M) {a. f a = b}\<close>
  by transfer (rule cmcount_cmimage)

lemma countable_nonzero_cinfmcount: \<open>countable {x. cinfmcount M x \<noteq> 0}\<close>
  by transfer (rule countable_nonzero_cmcount)

lemma infinite_nonzero_cinfmcount: \<open>(\<exists>x. cinfmcount M x = \<infinity>) \<or> infinite {x. cinfmcount M x \<noteq> 0}\<close>
  by transfer (simp add: cminfinite_alt)

lemma type_definition_cinfmset: \<open>type_definition cinfmcount (inv cinfmcount) {f. countable {x. f x \<noteq> 0} \<and> ((\<exists>x. f x = \<infinity>) \<or> infinite {x. f x \<noteq> 0})}\<close>
  by standard (auto simp: inj_cinfmcount in_range_cinfmcount inv_f_f f_inv_into_f countable_nonzero_cinfmcount infinite_nonzero_cinfmcount)

lifting_update cinfmset.lifting
lifting_forget cinfmset.lifting

definition get_cinfmset :: \<open>'a cinfmset \<Rightarrow> nat \<Rightarrow> 'a\<close> where
  \<open>get_cinfmset M i = lnth (rep_cmset (Rep_cinfmset M)) i\<close>

context includes cinfmset.lifting begin
interpretation cmset_as_Quotient .
lemma get_cinfmset_inject:
  \<open>\<forall>i. get_cinfmset M i = get_cinfmset N i \<Longrightarrow> M = N\<close>
  unfolding get_cinfmset_def
proof transfer
  fix M N :: \<open>'a cmset\<close>
  assume \<open>cminfinite M\<close> \<open>cminfinite N\<close>
    \<open>\<forall>i. lnth (rep_cmset M) i = lnth (rep_cmset N) i\<close>
  then have \<open>rep_cmset M = rep_cmset N\<close>
    by (simp add: cminfinite.rep_eq linfinite_eq_llength lnth_equalityI)
  then show \<open>M = N\<close>
    by (metis UNIV_I cmcount.rep_eq inj_cmcount inj_on_def)
qed

end

end
