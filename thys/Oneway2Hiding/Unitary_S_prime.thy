theory Unitary_S_prime
  imports Definition_O2H
begin

unbundle cblinfun_syntax
unbundle lattice_syntax

context o2h_setting
begin

subsection \<open>Towards the Definition of \<open>U_S'\<close>\<close>

text \<open>For the definition of \<open>U_S'\<close>, we need a counting function on the additional register.
We model this with the function \<open>c_add\<close> that works on \<open>nat\<close> as a addition of $1$ modulo $d+1$
(as long as we stay under the query depth $d$) and as an identity otherwise.\<close>
definition c_add :: "nat \<Rightarrow> nat" where
  "c_add c = (if c<d+1 then (c+1) mod (d+1) else c)"

lemma surj_c_add_c_valid: "c_add ` {..<d+1} = {..<d+1}"
proof -
  have "x \<in> (\<lambda>x. Suc x mod Suc d) ` {..<Suc d}" if "x < Suc d" for x 
  proof (cases "x=0")
    case True
    then show ?thesis by (simp add: True lessThan_Suc)
  next
    case False
    then show ?thesis by (intro image_eqI[of _  _ "x-1"])(use False that in \<open>auto\<close>)
  qed
  then show ?thesis unfolding c_add_def by auto
qed

text \<open>\<open>c_add\<close> needs to be bijective, so that the resulting operator is unitary.\<close>

lemma inj_c_add: "inj c_add"
proof -
  have "x = y" if "c_add x = c_add y" "x<d+1" "y<d+1" for x y
  proof -
    have "c_add x = (if x = d then 0 else x+1)" using that c_add_def by force
    moreover have "c_add y = (if y = d then 0 else y+1)" using that c_add_def by force
    ultimately have "(if x = d then 0 else x+1) = (if y = d then 0 else y+1)" using that by auto
    then show ?thesis by (metis Suc_eq_plus1 diff_add_inverse2 nat.simps(3))
  qed
  moreover have False if "c_add x = c_add y" "x<d+1" "y\<ge>d+1" for x y
    using c_add_def surj_c_add_c_valid that
    by (metis add_pos_nonneg d_gr_0 mod_less_divisor not_less zero_less_one_class.zero_le_one)
  moreover have "x = y" if "c_add x = c_add y" "x\<ge>d+1" "y\<ge>d+1" for x y
    using c_add_def that by auto 
  ultimately show ?thesis unfolding inj_def by (metis not_less)
qed

lemma surj_c_add: "c_add ` UNIV = UNIV"
  using surj_c_add_c_valid c_add_def by auto

lemma bij_c_add: "bij c_add"
  by (subst (2) surj_c_add[symmetric])
    (auto simp add: inj_c_add intro: inj_on_imp_bij_betw)

lemma c_add_0: "c_add 0 \<noteq> 0"
  unfolding c_add_def by (simp add: d_gr_0) 

text \<open>Finally, we can define the operator for the adversary $B_{count}$.\<close>

definition "Uc = classical_operator (Some o c_add)" 

lemma Uc_exists: 
  "classical_operator_exists (Some o c_add)"
  by (intro classical_operator_exists_inj, subst inj_map_def) 
    (use inj_c_add in \<open>auto simp add: inj_on_def\<close>)

lemma unitary_Uc:
  "unitary Uc"
  unfolding Uc_def by (auto intro!: unitary_classical_operator simp add: bij_c_add)

lemma Uc_ket_d:
  "Uc *\<^sub>V ket d = ket 0"
  unfolding Uc_def by (subst classical_operator_ket[OF Uc_exists]) 
    (simp add: c_add_def Suc_lessD)

lemma Uc_ket_less:
  assumes "n<d"
  shows "Uc *\<^sub>V ket n = ket (n+1)"
  unfolding Uc_def by (subst classical_operator_ket[OF Uc_exists]) 
    (simp add: c_add_def Suc_lessD assms) 

lemma Uc_ket_leq:
  assumes "n<d+1"
  shows "Uc *\<^sub>V ket n = ket ((n+1) mod (d+1))"
proof (cases "n=d")
  case True show ?thesis by (use Uc_ket_d in \<open>auto simp add: True\<close>) 
next
  case False show ?thesis by (use Uc_ket_less assms False in \<open>auto\<close>)
qed 

lemma Uc_ket_greater:
  assumes "n>d"
  shows "Uc *\<^sub>V ket n = ket n"
  unfolding Uc_def by (subst classical_operator_ket[OF Uc_exists])
    (use c_add_def assms in \<open>auto\<close>) 

lemma Uc_ket_range: 
  "(Uc *\<^sub>V ket y) \<in> range ket" unfolding Uc_def
  by (subst classical_operator_ket[OF Uc_exists])(auto)

lemma Uc_ket_range_valid: 
  assumes "y<d+1"
  shows "(Uc *\<^sub>V ket y) \<in> ket ` {..<d+1}" unfolding Uc_def 
  by (subst classical_operator_ket[OF Uc_exists])(use assms in \<open>auto simp add: c_add_def\<close>)


text \<open>Using the operator \<open>Uc\<close>, we define the unitary $U_{S}'$. Whenever, we queried an element
in the set $S$, we add a count in the counting register, otherwise not.
The linear operator \<open>Uc\<close> works only on the second register part (the counting register).\<close>

definition U_S' :: \<open>('x \<Rightarrow> bool) \<Rightarrow> ('mem \<times> nat) update\<close> where
  \<open>U_S' S = S_embed S \<otimes>\<^sub>o Uc + not_S_embed S \<otimes>\<^sub>o id_cblinfun\<close> 

lemma unitary_U_S':
  "unitary (U_S' S)"
  unfolding U_S'_def unitary_def proof (safe, goal_cases)
  case 1 
  have  "S_embed S \<otimes>\<^sub>o id_cblinfun + not_S_embed S \<otimes>\<^sub>o id_cblinfun = id_cblinfun"
    by (auto simp add: tensor_op_left_add[symmetric])
  then have "((S_embed S)* \<otimes>\<^sub>o Uc* + (not_S_embed S)* \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L 
    (S_embed S \<otimes>\<^sub>o Uc + not_S_embed S \<otimes>\<^sub>o id_cblinfun) = id_cblinfun" 
    by (auto simp add: cblinfun_compose_add_right cblinfun_compose_add_left 
        comp_tensor_op S_embed_adj tensor_op_ell2 unitary_Uc not_S_embed_adj not_S_embed_idem)
  then show ?case by (auto simp add: cblinfun.add_left cblinfun.add_right 
        tensor_ell2_ket[symmetric] adj_plus tensor_op_adjoint)
next
  case 2 
  have  "S_embed S \<otimes>\<^sub>o id_cblinfun + not_S_embed S \<otimes>\<^sub>o id_cblinfun = id_cblinfun"
    by (auto simp add: tensor_op_left_add[symmetric])
  then have "(S_embed S \<otimes>\<^sub>o Uc + not_S_embed S \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L 
    ((S_embed S)* \<otimes>\<^sub>o Uc* + (not_S_embed S)* \<otimes>\<^sub>o id_cblinfun) = id_cblinfun" 
    by (auto simp add: cblinfun_compose_add_right cblinfun_compose_add_left 
        comp_tensor_op S_embed_adj tensor_op_ell2 unitary_Uc not_S_embed_adj not_S_embed_idem)
  then show ?case by (auto simp add: cblinfun.add_left cblinfun.add_right 
        tensor_ell2_ket[symmetric] adj_plus tensor_op_adjoint)
qed

lemma iso_U_S': "isometry (U_S' S)"
  by (simp add: unitary_U_S')

lemma U_S'_ket_split:
  "U_S' S *\<^sub>V ket (x,y) = (S_embed S *\<^sub>V ket x) \<otimes>\<^sub>s (Uc *\<^sub>V ket y) + (not_S_embed S *\<^sub>V ket x) \<otimes>\<^sub>s ket y"
  unfolding U_S'_def
  by (auto simp add: plus_cblinfun.rep_eq tensor_ell2_ket[symmetric] tensor_op_ell2)

lemma norm_U_S': 
  assumes "i < Suc d" shows "norm (U_S' S) = 1"
  by (simp add: iso_U_S' norm_isometry)


text \<open>We ensure that the $\Phi s$ is the same as the left part of $\Psi_{count}$ 
(ie.\ \<open>run_B_count\<close>) with right part $\mid 0 \rangle$.\<close>

lemma \<Psi>s_U_S'_Proj_ket_upto:
  assumes "i<d"
  shows "tensor_ell2_right (ket 0)* o\<^sub>C\<^sub>L (U_S' S o\<^sub>C\<^sub>L Proj_ket_set {..<i+1}) = 
  not_S_embed S o\<^sub>C\<^sub>L tensor_ell2_right (ket 0)*"
proof (intro equal_ket, safe, goal_cases)
  case (1 a b)
  have split_a: "ket a = S_embed S (ket a) + not_S_embed S (ket a)" 
    using S_embed_not_S_embed_add by auto
  have "(tensor_ell2_right (ket 0)* o\<^sub>C\<^sub>L (U_S' S o\<^sub>C\<^sub>L Proj_ket_set {..<i+1})) *\<^sub>V ket (a, b) = 
    (not_S_embed S o\<^sub>C\<^sub>L tensor_ell2_right (ket 0)*) *\<^sub>V ket (a, b)" (is "?left = ?right")
    if "b < i+1" 
  proof -
    have "b < d" using assms that by linarith
    then have "c_add b \<noteq> 0" unfolding c_add_def using c_add_0 c_add_def not_less_eq by force
    have proj: "proj_classical_set {..<i+1} *\<^sub>V ket b = ket b" 
      using that unfolding proj_classical_set_def by (simp add: Proj_fixes_image ccspan_superset')
    have "?left = (tensor_ell2_right (ket 0)* o\<^sub>C\<^sub>L U_S' S) *\<^sub>V ket (a, b)" 
      using proj by (auto simp add: Proj_ket_set_def tensor_ell2_ket[symmetric] tensor_op_ell2)
    also have "\<dots> = tensor_ell2_right (ket 0)* *\<^sub>V 
        ((S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s Uc *\<^sub>V ket b + ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket b))" 
      using U_S'_ket_split by auto
    also have "\<dots> = tensor_ell2_right (ket 0)* *\<^sub>V ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket b)"
    proof -
      have "tensor_ell2_right (ket 0)* *\<^sub>V ((S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s Uc *\<^sub>V ket b) = 0"
        by (simp add: Uc_ket_less \<open>b < d\<close>)
      then show ?thesis by (simp add: cblinfun.real.add_right)
    qed
      (*Compatibility of X is assumed!*)
    also have "\<dots> = ?right" 
      by (auto simp add: tensor_ell2_ket[symmetric] cinner_ket)
    finally show ?thesis by blast
  qed
  moreover have "(tensor_ell2_right (ket 0)* o\<^sub>C\<^sub>L (U_S' S o\<^sub>C\<^sub>L Proj_ket_set {..<i+1})) *\<^sub>V ket (a, b) = 
    (not_S_embed S o\<^sub>C\<^sub>L tensor_ell2_right (ket 0)*) *\<^sub>V ket (a, b)" (is "?left = ?right")
    if "\<not> (b < i+1)"
  proof -
    have "b\<noteq>0" using that by auto
    have proj: "Proj (ccspan (ket ` {..<i+1})) *\<^sub>V ket b = 0"
      using that
      by (metis lessThan_iff proj_classical_set_def proj_classical_set_not_elem)
    then have "?left = 0" by (auto simp add: Proj_ket_set_def tensor_ell2_ket[symmetric] 
          tensor_op_ell2 proj_classical_set_def)
    moreover have "?right = 0" by (auto simp add: \<open>b\<noteq>0\<close> tensor_ell2_ket[symmetric] cinner_ket)
    ultimately show ?thesis by auto
  qed
  ultimately show ?case by (cases "b < i+1", auto)
qed



end

unbundle no cblinfun_syntax
unbundle no lattice_syntax

end