theory Orders
imports
  "Well_Quasi_Orders"
  "Well_Partial_Orders"
begin

text {*If the strict part of a quasi-order @{term Q} is a
well-partial-order, then @{term Q} is a well-quasi-order.*}
lemma wpo_on_imp_wqo_on:
  fixes P Q
  defines "P \<equiv> strict Q"
  assumes "wpo_on P A" and "qo_on Q A"
  shows "wqo_on Q A"
proof
  from `qo_on Q A` show "transp_on Q A"
    unfolding qo_on_def by blast
  from `qo_on Q A` have "reflp_on Q A"
    unfolding qo_on_def by blast
  moreover have "almost_full_on P\<^sup>=\<^sup>= A"
    by (rule `wpo_on P A` [THEN wpo_on_imp_almost_full_on])
  ultimately show "almost_full_on Q A"
    unfolding P_def reflp_on_def almost_full_on_def good_def
    by (auto) (metis)
qed

end

