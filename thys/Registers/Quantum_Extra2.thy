section \<open>More derived facts about quantum registers\<close>

text \<open>This theory contains some derived facts that cannot be placed in theory \<open>Quantum_Extra\<close> 
      because they depend on \<open>Laws_Complement_Quantum\<close>.\<close>

theory Quantum_Extra2
  imports
    Laws_Complement_Quantum
    Quantum
begin

unbundle register_syntax

definition empty_var :: \<open>'a::{CARD_1,enum} update \<Rightarrow> 'b update\<close> where
  "empty_var a = one_dim_iso a *\<^sub>C id_cblinfun"

lemma is_unit_register_empty_var[register]: \<open>is_unit_register empty_var\<close> (is \<open>is_unit_register ?e\<close>)
proof -
  note continuous_map_compose[trans]
  have \<open>continuous_map weak_star_topology euclidean (id :: 'a update \<Rightarrow> _)\<close>
    by simp
  also have \<open>continuous_map euclidean euclidean one_dim_iso\<close>
    by (simp add: clinear_continuous_at continuous_at_imp_continuous_on)
  also have \<open>continuous_map euclidean euclidean (\<lambda>a. a *\<^sub>C id_cblinfun)\<close>
    by (simp add: continuous_at_imp_continuous_on)
  also have \<open>continuous_map euclidean weak_star_topology (id :: 'b update \<Rightarrow> _)\<close>
    by (metis comp_id fun.map_ident weak_star_topology_weaker_than_euclidean)
  finally have \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>a :: 'a update. one_dim_iso a *\<^sub>C id_cblinfun :: 'b update)\<close>
    by (simp add: o_def)
  then have [simp]: \<open>register ?e\<close>
    unfolding register_def empty_var_def
    by (simp add: clinearI scaleC_left.add)
  have [simp]: \<open>compatible ?e id\<close>
    by (auto intro!: compatibleI simp: empty_var_def)
  have [simp]: \<open>iso_register (?e; id)\<close>
    by (auto intro!: same_range_equivalent range_eqI[where x=\<open>id_cblinfun \<otimes>\<^sub>o _\<close>] 
        simp del: id_cblinfun_eq_1 simp flip: iso_register_equivalent_id simp: register_pair_apply)
  show ?thesis
    by (auto intro!: complementsI simp: is_unit_register_def)
qed

instance complement_domain_simple :: (type, type) default ..

unbundle no register_syntax

end
