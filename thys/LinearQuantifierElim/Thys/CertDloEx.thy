(* FIXME dead code? *)

theory CertDloEx imports CertDlo
begin

lemma "z < u \<and> y < z \<and> x < y \<longrightarrow> u \<noteq> (x::real)"
apply reify
apply(rule refute_I)
apply(rule cyclic_dnfD)
 apply evaluation
apply (simp add: DLO.nnf.simps)
apply (simp add: cyclic_dnf_def)
apply(rule_tac x = "[[0,3,2,1]]" in exI)
apply evaluation
done

lemma "(x::real) < y \<and> y < z \<longrightarrow> x < z"
apply reify
apply(rule refute_I)
apply(rule cyclic_dnfD)
 apply evaluation
apply (simp add:DLO.nnf.simps cyclic_dnf_def)
apply(rule_tac x = "[[0,1,2],[0,1,2]]" in exI)
apply evaluation
done

end