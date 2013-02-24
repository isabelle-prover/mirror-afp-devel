theory "FMap-Utils"
imports "FMap-Nominal-HOLCF" "HOLCF-Fix-Join-Nominal" "DistinctVars"
begin

default_sort type

text {* Lemmas relating @{theory FMap} to the other auxillary theories. *}

lemma fdom_fix_join_compat:
  assumes "fix_on_cond S (bottom_of S) (\<lambda>\<rho>'. \<rho> \<squnion> F \<rho>')"
  assumes "\<rho>' \<in> fix_join_compat \<rho> F"
  shows "fdom \<rho>' = fdom \<rho>"
  by (metis assms(2) bottom_of_fjc fmap_below_dom subpcpo.bottom_of_minimal subpcpo_fjc to_bot_minimal)

lemma sharp_star_Env': "atom ` heapVars \<Gamma> \<sharp>* (\<rho> :: 'var::{cont_pt,at_base} f\<rightharpoonup> 'value::{pure_cpo,Nonempty_Meet_cpo,pcpo}) \<longleftrightarrow> heapVars \<Gamma> \<inter> fdom \<rho> = {}"
  by(induct \<Gamma>, auto simp add: fresh_star_def sharp_Env)
end
