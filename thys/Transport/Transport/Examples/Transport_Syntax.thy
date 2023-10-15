\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Syntax Bundles for Transport\<close>
theory Transport_Syntax
  imports
    Transport
begin

abbreviation "Galois_infix x L R r y \<equiv> galois_rel.Galois L R r x y"
abbreviation (input) "ge_Galois R r L \<equiv> galois_rel.ge_Galois_left L R r"
abbreviation (input) "ge_Galois_infix y R r L x \<equiv> ge_Galois R r L y x"

bundle galois_rel_syntax
begin
  notation galois_rel.Galois ("'((\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>)')")
  notation Galois_infix ("(_) (\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>) (_)" [51,51,51,51,51] 50)
  notation ge_Galois ("'((\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>)')")
  notation ge_Galois_infix ("(_) (\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>) (_)" [51,51,51,51,51] 50)
end
bundle no_galois_rel_syntax
begin
  no_notation galois_rel.Galois ("'((\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>)')")
  no_notation Galois_infix ("(_) (\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>) (_)" [51,51,51,51,51] 50)
  no_notation ge_Galois ("'((\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>)')")
  no_notation ge_Galois_infix ("(_) (\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>) (_)" [51,51,51,51,51] 50)
end

bundle transport_syntax
begin
  notation transport.preorder_equivalence (infix "\<equiv>\<^bsub>pre\<^esub>" 50)
  notation transport.partial_equivalence_rel_equivalence (infix "\<equiv>\<^bsub>PER\<^esub>" 50)
end
bundle no_transport_syntax
begin
  no_notation transport.preorder_equivalence (infix "\<equiv>\<^bsub>pre\<^esub>" 50)
  no_notation transport.partial_equivalence_rel_equivalence (infix "\<equiv>\<^bsub>PER\<^esub>" 50)
end


end