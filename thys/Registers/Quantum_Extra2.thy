section \<open>More derived facts about quantum registers\<close>

text \<open>This theory contains some derived facts that cannot be placed in theory \<open>Quantum_Extra\<close> 
      because they depend on \<open>Laws_Complement_Quantum\<close>.\<close>

theory Quantum_Extra2
  imports
    Laws_Complement_Quantum
    Quantum
begin

definition empty_var :: \<open>'a::{CARD_1,enum} update \<Rightarrow> 'b::finite update\<close> where
  "empty_var a = one_dim_iso a *\<^sub>C id_cblinfun"

lemma is_unit_register_empty_var[register]: \<open>is_unit_register empty_var\<close>
proof -
  have [simp]: \<open>register empty_var\<close>
    unfolding register_def empty_var_def
    by (simp add: clinearI scaleC_left.add)
  have [simp]: \<open>compatible empty_var id\<close>
    by (auto intro!: compatibleI simp: empty_var_def)
  have [simp]: \<open>iso_register (empty_var;id)\<close>
    by (auto intro!: same_range_equivalent range_eqI[where x=\<open>id_cblinfun \<otimes>\<^sub>o _\<close>] 
        simp del: id_cblinfun_eq_1 simp flip: iso_register_equivalent_id simp: register_pair_apply)
  show ?thesis
    by (auto intro!: complementsI simp: is_unit_register_def)
qed

instance complement_domain :: (type, type) default ..

end
