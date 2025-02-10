(*<*)
theory Regex_Proof_Object
imports Regex_Proof_System
begin
(*>*)

datatype (spatms: 'a) rsproof = SSkip nat nat | STest 'a | SPlusL "'a rsproof" | SPlusR "'a rsproof"
  | STimes "'a rsproof" "'a rsproof" | SStar_eps nat | SStar "'a rsproof list"
datatype (vpatms: 'a) rvproof = VSkip nat nat | VTest 'a | VTest_neq nat nat | VPlus "'a rvproof" "'a rvproof"
  | VTimes "(bool * 'a rvproof) list" | VStar "'a rvproof list" | VStar_gt nat nat

lemma size_hd_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (hd xs) < size_list size xs"
  by (cases xs) auto
lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto
lemma size_rsproof_estimation[termination_simp]: "x \<in> spatms p \<Longrightarrow> y < f x \<Longrightarrow> y < size_rsproof f p"
  by (induct p) (auto simp: termination_simp)
lemma size_rsproof_estimation'[termination_simp]: "x \<in> spatms p \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_rsproof f p"
  by (induct p) (auto simp: termination_simp)
lemma size_rvproof_estimation[termination_simp]: "x \<in> vpatms p \<Longrightarrow> y < f x \<Longrightarrow> y < size_rvproof f p"
  by (induct p) (auto simp: termination_simp sum_set_defs split: sum.splits)
lemma size_rvproof_estimation'[termination_simp]: "x \<in> vpatms p \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_rvproof f p"
  by (induct p) (auto simp: termination_simp)

fun rs_at where
  "rs_at test (SSkip k n) = (k, k + n)"
| "rs_at test (STest x) = (test x, test x)"
| "rs_at test (SPlusL p) = rs_at test p"
| "rs_at test (SPlusR p) = rs_at test p"
| "rs_at test (STimes p1 p2) = (fst (rs_at test p1), snd (rs_at test p2))"
| "rs_at test (SStar_eps n) = (n, n)"
| "rs_at test (SStar ps) = (if ps = [] then (0,0) else (fst (rs_at test (hd ps)), snd (rs_at test (last ps))))"

lemma rs_at_cong[fundef_cong]:
  "p = p' \<Longrightarrow> (\<And>x. x \<in> spatms p \<Longrightarrow> t x = t' x) \<Longrightarrow> rs_at t p = rs_at t' p'"
proof (induct p arbitrary: p')
  case (SStar ps)
  then show ?case using hd_in_set[of ps] last_in_set[of ps]
    by fastforce
qed auto

function(sequential) rv_at where
  "rv_at test (VSkip n n') = (n, n')"
| "rv_at test (VTest p) = (test p, test p)"
| "rv_at test (VTest_neq n n') = (n, n')"
| "rv_at test (VPlus p1 p2) = rv_at test p1"
| "rv_at test (VTimes ps) = (if ps = [] then (0,0) else (fst (rv_at test (snd (hd ps))), snd (rv_at test (snd (last ps)))))"
| "rv_at test (VStar ps) = (Min (set (map (fst \<circ> (rv_at test)) ps)), Max (set (map (snd \<circ> (rv_at test)) ps)))"
| "rv_at test (VStar_gt n n') = (n, n')"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(_, vp). size vp)")
  (auto intro: less_SucI list.set_sel(1) size_list_estimation last_in_set simp: termination_simp)

lemma rv_at_cong[fundef_cong]:
  "p = p' \<Longrightarrow> (\<And>x. x \<in> vpatms p \<Longrightarrow> t x = t' x) \<Longrightarrow> rv_at t p = rv_at t' p'"
proof (induct t p arbitrary: p' rule: rv_at.induct)
  case (5 t ps)
  then show ?case using hd_in_set[of ps] last_in_set[of ps]
    by (cases "hd ps"; cases "last ps"; fastforce)
next
  case (6 t ps)
  then show ?case
    by (force intro!: arg_cong[where f=Min] arg_cong[where f=Max] image_cong)
qed auto

(*<*)
end
(*>*)
