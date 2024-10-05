\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Syntax Bundles for Transport\<close>
theory Transport_Syntax
  imports
    Transport_Base
begin

abbreviation "Galois_infix x L R r y \<equiv> galois_rel.Galois L R r x y"
abbreviation (input) "ge_Galois R r L \<equiv> galois_rel.ge_Galois_left L R r"
abbreviation (input) "ge_Galois_infix y R r L x \<equiv> ge_Galois R r L y x"

bundle galois_rel_syntax
begin
  notation galois_rel.Galois (\<open>'((\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>)')\<close>)
  notation Galois_infix (\<open>(_) (\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>) (_)\<close> [51,51,51,51,51] 50)
  notation ge_Galois (\<open>'((\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>)')\<close>)
  notation ge_Galois_infix (\<open>(_) (\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>) (_)\<close> [51,51,51,51,51] 50)
end

bundle transport_syntax
begin
  notation transport.preorder_equivalence (infix \<open>\<equiv>\<^bsub>pre\<^esub>\<close> 50)
  notation transport.partial_equivalence_rel_equivalence (infix \<open>\<equiv>\<^bsub>PER\<^esub>\<close> 50)
end

end