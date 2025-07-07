theory Definition_Pure_O2H

imports Definition_O2H 
  Run_Adversary

begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax

subsection \<open>Locale for the pure O2H setting\<close>

text \<open>For the pure state case, we define a separate locale for the pure one-way to hiding lemma.\<close>

locale pure_o2h = o2h_setting "TYPE('x)" "TYPE('y::group_add)" "TYPE('mem)" "TYPE('l)" +
  \<comment> \<open>We fix the oracle function \<open>H\<close>, a subset of the oracle domain \<open>S\<close> and the sequence of 
  operations the adversary $A$ undertakes in the function \<open>UA\<close>.\<close>
  fixes H :: \<open>'x \<Rightarrow> ('y::group_add)\<close> 
    and S :: \<open>'x \<Rightarrow> bool\<close> 
    and UA :: \<open>nat \<Rightarrow> 'mem update\<close> 

\<comment> \<open>All operations by the adversary $A$ must be isometries.\<close>
assumes norm_UA: \<open>\<And>i. i<d+1 \<Longrightarrow> norm (UA i) \<le> 1\<close> 
begin

text \<open>Given the initial register state \<open>init\<close>, \<open>run_A\<close> returns the register state after 
performing the algorithm describing the adversary $A$.\<close>
definition \<open>run_A = run_pure_adv d UA (\<lambda>_. id_cblinfun::'mem update) init X Y H\<close>
  (* An adversary run looks like this:
  init \<Rightarrow> UA \<Rightarrow> Uquery H \<Rightarrow> UA \<Rightarrow> Uquery H \<Rightarrow> \<dots> \<Rightarrow> Uquery H \<Rightarrow> UA *)

lemma norm_UA_Suc: "n <d \<Longrightarrow> norm (UA (Suc n)) \<le> 1"
  by (simp add: norm_UA)

lemma norm_UA_0_init:
  "norm (UA 0 *\<^sub>V init) \<le> 1"
  using norm_UA[of 0] norm_init d_gr_0 
  by (metis basic_trans_rules(23) mult_cancel_left2 norm_cblinfun semiring_norm(174) zero_less_Suc)

lemma tensor_proj_UA_tensor_commute:
  "(id_cblinfun \<otimes>\<^sub>o proj_classical_set A) o\<^sub>C\<^sub>L (UA (Suc n) \<otimes>\<^sub>o id_cblinfun) =
   (UA (Suc n) \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o proj_classical_set A)"
  by (auto intro!: tensor_ell2_extensionality simp add: tensor_op_ell2)


end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax

end