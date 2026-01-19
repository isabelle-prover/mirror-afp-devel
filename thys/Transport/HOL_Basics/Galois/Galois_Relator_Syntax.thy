\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Syntax Bundles for Galois Relator\<close>
theory Galois_Relator_Syntax
  imports
    Galois_Relator_Base
begin

abbreviation "Galois_infix x L R r y \<equiv> galois_rel.Galois L R r x y"
abbreviation (input) "ge_Galois R r L \<equiv> galois_rel.ge_Galois_left L R r"
abbreviation (input) "ge_Galois_infix y R r L x \<equiv> ge_Galois R r L y x"

bundle galois_rel_Galois_syntax
begin
  notation (input) galois_rel.Galois (\<open>'((\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>)')\<close>)
  notation (output) galois_rel.Galois (\<open>'((\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>('(_')) ('(_'))\<^esub>)')\<close>)
  notation (input) Galois_infix (\<open>_ (\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>(_) (_)\<^esub>) _\<close> [51,0,0,51] 50)
  notation (output) Galois_infix (\<open>_ (\<^bsub>_\<^esub>)\<lessapprox>(\<^bsub>('(_')) ('(_'))\<^esub>) _\<close> [51,0,0,51] 50)
  notation (input) ge_Galois (\<open>'((\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>)')\<close>)
  notation (output) ge_Galois (\<open>'((\<^bsub>('(_')) ('(_'))\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>)')\<close>)
  notation (input) ge_Galois_infix (\<open>_ (\<^bsub>(_) (_)\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>) _\<close>  [51,0,0,51] 50)
  notation (output) ge_Galois_infix (\<open>_ (\<^bsub>('(_')) ('(_'))\<^esub>)\<greaterapprox>(\<^bsub>_\<^esub>) _\<close>  [51,0,0,51] 50)
end

end