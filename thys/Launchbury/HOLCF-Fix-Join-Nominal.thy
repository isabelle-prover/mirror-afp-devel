theory "HOLCF-Fix-Join-Nominal"
imports "HOLCF-Fix-Join" "HOLCF-Set-Nominal" "FMap-Nominal-HOLCF"
begin

lemma fix_join_cond_eqvt[eqvt]:
  shows "fix_join_cond \<rho> (F::'a::{subpcpo_partition,cont_pt} \<Rightarrow> 'a) \<Longrightarrow> fix_join_cond (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> F)"
  apply (erule fix_join_cond.induct)
  apply (rule fix_join_condI)
  apply (erule cont_eqvt)
  apply (erule_tac x = i in meta_allE) 
  apply (drule compatible_eqvt[where \<pi> = \<pi>], perm_simp, assumption)
  done

lemma fix_join_compat_eqvt:
  fixes \<rho> :: "'a::{Bounded_Nonempty_Meet_cpo,subpcpo_partition,cont_pt}"
  assumes "fix_join_cond \<rho> F"
  shows "\<pi> \<bullet> fix_join_compat \<rho> F = fix_join_compat (\<pi> \<bullet> \<rho>) (\<pi> \<bullet> F)"
proof-
  show ?thesis
    apply (auto simp add: permute_set_eq)
    apply (subst (asm) perm_cont_simp[symmetric, of _ _ \<pi>])
    apply (subst (asm) fix_on_eqvt[OF fix_on_cond_fjc[OF assms(1), unfolded bottom_of_fjc]])
    apply simp
    
    apply (subst  perm_cont_simp[symmetric, of _ _ "\<pi>"])
    apply (subst  fix_on_eqvt[OF fix_on_cond_fjc[OF assms(1), unfolded bottom_of_fjc]])
    apply simp
    done
qed
end
