theory Unitary_S

imports Definition_O2H

begin

unbundle cblinfun_syntax
unbundle lattice_syntax

context o2h_setting
begin
subsection \<open>Linear operator \<open>US\<close>\<close>

definition Ub :: "nat \<Rightarrow> 'l update" where
  "Ub i = classical_operator (Some o (flip i))" 

lemma Ub_exists: "classical_operator_exists (Some \<circ> flip i)"
  by (intro classical_operator_exists_inj, subst inj_map_total)
    (simp add: inj_flip)

lemma isometry_Ub:
  "isometry (Ub k)"
  unfolding Ub_def by (auto simp add: inj_flip)

lemma Ub_ket_range: "(Ub i *\<^sub>V ket y) \<in> range ket" unfolding Ub_def
  by (simp add: classical_operator_ket[OF Ub_exists])

lemma Ub_ket:
  "Ub k *\<^sub>V (ket x) = ket (flip k x)"
  unfolding Ub_def by (simp add: classical_operator_ket[OF Ub_exists])

text \<open>Using the operator \<open>Ub\<close>, we define the unitary $U_{S}$. Whenever we queried an element
in the set $S$, we add a bit-flip in the register \<open>'l\<close>, otherwise not.
The linear operator \<open>Ub\<close> works only on the second register part (the counting register).
This is the operator between the oracle queries while running \<open>B\<close>.\<close> 
definition US :: \<open>('x \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> ('mem \<times> 'l) update\<close> where 
  \<open>US S k = S_embed S \<otimes>\<^sub>o Ub k + not_S_embed S \<otimes>\<^sub>o id_cblinfun\<close>

lemma isometry_US:
  "isometry (US S k)" 
proof -
  have  "S_embed S \<otimes>\<^sub>o id_cblinfun + not_S_embed S \<otimes>\<^sub>o id_cblinfun = id_cblinfun"
    by (auto simp add: tensor_op_left_add[symmetric])
  then have "((S_embed S)* \<otimes>\<^sub>o (Ub k)* + (not_S_embed S)* \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L 
    (S_embed S \<otimes>\<^sub>o (Ub k) + not_S_embed S \<otimes>\<^sub>o id_cblinfun) = id_cblinfun" 
    by (auto simp add: cblinfun_compose_add_right cblinfun_compose_add_left 
        comp_tensor_op S_embed_adj tensor_op_ell2 isometry_Ub not_S_embed_adj not_S_embed_idem)
  then show ?thesis unfolding US_def isometry_def 
    by (auto simp add: cblinfun.add_left cblinfun.add_right 
        tensor_ell2_ket[symmetric] adj_plus tensor_op_adjoint)
qed

lemma US_ket_split:
  "(US S k) *\<^sub>V ket (x,y) = (S_embed S *\<^sub>V ket x) \<otimes>\<^sub>s ((Ub k) *\<^sub>V ket y) + (not_S_embed S *\<^sub>V ket x) \<otimes>\<^sub>s ket y"
  unfolding US_def
  by (auto simp add: plus_cblinfun.rep_eq tensor_ell2_ket[symmetric] tensor_op_ell2)

lemma US_ket_only01:
  "US S k (v \<otimes>\<^sub>s ket n) = (not_S_embed S *\<^sub>V v) \<otimes>\<^sub>s ket n + (S_embed S *\<^sub>V v) \<otimes>\<^sub>s ket (flip k n)"
  unfolding US_def by (auto simp add: cblinfun.add_left tensor_op_ell2 Ub_ket)

lemma norm_US: 
  assumes "i < Suc d" shows "norm (US S i) = 1"
  by (simp add: isometry_US norm_isometry)

text \<open>Projection upto bit i\<close>

text \<open>How the counting unitary \<open>Ub\<close> behaves with respect to projections on the counting register.\<close>

lemma proj_classical_set_not_blog_Ub:
  assumes "n<d"
  shows "proj_classical_set (- Collect blog) o\<^sub>C\<^sub>L Ub n = 
       Ub n o\<^sub>C\<^sub>L proj_classical_set (- Collect blog)" 
proof (intro equal_ket, goal_cases)
  case (1 x)
  show ?case proof (cases "blog x")
    case True
    then show ?thesis by (simp add: blog_flip[OF \<open>n<d\<close>] True Ub_ket proj_classical_set_not_elem)
  next
    case False
    then show ?thesis by (simp add: Ub_ket not_blog_flip[OF \<open>n<d\<close>] proj_classical_set_elem)
  qed
qed

(* has_bits {n..<d} \<equiv> {l. l\<in>len_d_lists \<and> True \<in> (\<lambda>i.l!i) ` {n..<d}}*)

lemma proj_classical_set_over_Ub:
  assumes "n\<le>d" "m<d"
  shows "proj_classical_set (list_to_l ` has_bits {n..<d}) o\<^sub>C\<^sub>L Ub m = 
       Ub m o\<^sub>C\<^sub>L proj_classical_set (flip m ` list_to_l ` has_bits {n..<d})"
proof (intro equal_ket, goal_cases)
  case (1 x)
  show ?case proof (cases "blog x")
    case True
    obtain j where "j\<in>len_d_lists" and x: "x = list_to_l j"
      by (metis True image_iff mem_Collect_eq surj_list_to_l)
    consider (elem) "flip m x \<in> list_to_l ` has_bits {n..<d}" | 
      (not_elem) "\<not> flip m x \<in> list_to_l ` has_bits {n..<d}" by auto
    then have ?thesis if "n<d" proof (cases)
      case elem 
      then have x_in: "x \<in> flip m ` list_to_l ` has_bits {n..<d}"
        using True assms(2) flip_flip by fastforce
      have "(proj_classical_set (list_to_l ` has_bits {n..<d}) o\<^sub>C\<^sub>L Ub m) *\<^sub>V ket x = ket (flip m x)"
        by (simp add: Ub_ket local.elem proj_classical_set_elem)
      moreover have "(Ub m o\<^sub>C\<^sub>L proj_classical_set (flip m ` list_to_l ` has_bits {n..<d})) *\<^sub>V ket x = 
        ket (flip m x)"
        using proj_classical_set_elem[OF x_in] by (auto simp add: Ub_ket)
      ultimately show ?thesis by metis
    next
      case not_elem
      then have x_in: "x \<notin> flip m ` list_to_l ` has_bits {n..<d}" using flip_flip[OF \<open>m<d\<close>]
        by (metis True imageE inj_def inj_flip)
      have "(proj_classical_set (list_to_l ` has_bits {n..<d}) o\<^sub>C\<^sub>L Ub m) *\<^sub>V ket x = 0"
        by (simp add: Ub_ket not_elem proj_classical_set_not_elem)
      moreover have "(Ub m o\<^sub>C\<^sub>L proj_classical_set (flip m ` list_to_l ` has_bits {n..<d})) *\<^sub>V ket x = 0"
        using proj_classical_set_not_elem[OF x_in] by (auto simp add: Ub_ket)
      ultimately show ?thesis by metis
    qed
    moreover have ?thesis if "n=d" unfolding that using True 
      by (auto simp add: Ub_ket proj_classical_set_not_elem)
    ultimately show ?thesis using assms by linarith
  next
    case False
    have "proj_classical_set (list_to_l ` has_bits {n..<d}) *\<^sub>V ket (flip m x) = 0" 
      by (intro proj_classical_set_not_elem)(metis (no_types, lifting) False 
          image_iff mem_Collect_eq not_blog_flip[OF \<open>m<d\<close>] has_bits_def surj_list_to_l)
    then have left: "(proj_classical_set (list_to_l ` has_bits {n..<d}) o\<^sub>C\<^sub>L Ub m) *\<^sub>V ket x = 0"
      by (auto simp add: Ub_ket) 
    have right: "proj_classical_set (flip m ` list_to_l ` has_bits {n..<d}) *\<^sub>V ket x = 0" 
      by (intro proj_classical_set_not_elem) (smt (verit, del_insts) False assms(2) blog.simps 
          imageE image_eqI mem_Collect_eq has_bits_def surj_list_to_l)
    show ?thesis unfolding left using right by auto
  qed
qed

lemma \<Psi>s_US_Proj_ket_upto:
  assumes "i<d"
  shows "tensor_ell2_right (ket empty)* o\<^sub>C\<^sub>L ((US S i) o\<^sub>C\<^sub>L Proj_ket_upto (has_bits_upto i)) = 
  not_S_embed S o\<^sub>C\<^sub>L tensor_ell2_right (ket empty)*"
proof (intro equal_ket, safe, goal_cases)
  case (1 a b)
  have split_a: "ket a = S_embed S (ket a) + not_S_embed S (ket a)" 
    using S_embed_not_S_embed_add by auto
  have ?case (is "?left = ?right") if "b \<in> list_to_l ` has_bits_upto i" 
  proof -
    have "Proj (ccspan (ket ` list_to_l ` has_bits_upto i)) *\<^sub>V ket b = ket b" 
      using that by (simp add: Proj_fixes_image ccspan_superset')
    then have proj: "proj_classical_set (list_to_l ` has_bits_upto i) *\<^sub>V ket b = ket b"
      unfolding proj_classical_set_def by auto
    have "?left = (tensor_ell2_right (ket empty)* o\<^sub>C\<^sub>L (US S i)) *\<^sub>V ket (a, b)" 
      using proj by (auto simp add: Proj_ket_upto_def Proj_ket_set_def tensor_ell2_ket[symmetric] 
          tensor_op_ell2)
    also have "\<dots> = tensor_ell2_right (ket empty)* *\<^sub>V 
        ((S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s (Ub i) *\<^sub>V ket b + ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket b))" 
      using US_ket_split by auto
    also have "\<dots> = tensor_ell2_right (ket empty)* *\<^sub>V ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket b)"
    proof -
      obtain bs where b: "bs\<in> has_bits_upto i" "b = list_to_l bs" 
        using \<open>b \<in> list_to_l ` has_bits_upto i\<close> by auto
      then have bs: "length bs = d" "\<not> (bs!(d-i-1))" unfolding has_bits_upto_def len_d_lists_def 
        using assms b(1) has_bits_upto_elem by auto
      then have "bit b i = bit empty i" unfolding b(2) 
        by (subst bit_list_to_l) (auto simp add: \<open>i<d\<close>)
      then have "flip i b \<noteq> empty" using assms bit_flip_same blog.intros(1) not_blog_flip by blast
      then have "tensor_ell2_right (ket empty)* *\<^sub>V ((S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s (Ub i) *\<^sub>V ket b) = 0"
        by (simp add: Ub_def classical_operator_ket[OF Ub_exists])
      then show ?thesis by (simp add: cblinfun.real.add_right)
    qed
      (*Compatibility of X is assumed!*)
    also have "\<dots> = ?right" 
      by (auto simp add: tensor_ell2_ket[symmetric] cinner_ket)
    finally show ?thesis by blast
  qed
  moreover have ?case (is "?left = ?right") if "\<not> (b \<in> list_to_l ` has_bits_upto i)" "blog b"
  proof -
    have "b \<noteq> empty" using that empty_list_to_l_has_bits_upto by force
    have "b \<notin> list_to_l ` has_bits_upto i" using that by auto
    then have proj: "proj_classical_set (list_to_l ` has_bits_upto i) *\<^sub>V ket b = 0"
      unfolding proj_classical_set_def by (intro Proj_0_compl, intro mem_ortho_ccspanI) auto
    then have "?left = 0" 
      by (auto simp add: Proj_ket_upto_def Proj_ket_set_def tensor_ell2_ket[symmetric] 
          tensor_op_ell2)
    moreover have "?right = 0" using  \<open>b \<noteq> empty\<close>
      by (auto simp add: tensor_ell2_ket[symmetric] cinner_ket)
    ultimately show ?thesis by auto
  qed
  moreover have ?case (is "?left = ?right") if "\<not> blog b" 
  proof -
    have "b \<noteq> empty" using that blog.intros(1) by auto
    have "b \<notin> list_to_l ` has_bits_upto i"
      using has_bits_upto_def surj_list_to_l that by fastforce
    then have proj: "proj_classical_set (list_to_l ` has_bits_upto i) *\<^sub>V ket b = 0"
      unfolding proj_classical_set_def by (intro Proj_0_compl, intro mem_ortho_ccspanI) auto
    then have "?left = 0" 
      by (auto simp add: Proj_ket_upto_def Proj_ket_set_def tensor_ell2_ket[symmetric] 
          tensor_op_ell2)
    moreover have "?right = 0" using \<open>b \<noteq> empty\<close> 
      by (auto simp add:  tensor_ell2_ket[symmetric] cinner_ket)
    ultimately show ?thesis by auto
  qed
  ultimately show ?case by (cases "b \<in> list_to_l ` has_bits_upto i", auto)
qed

end

unbundle no cblinfun_syntax
unbundle no lattice_syntax


end