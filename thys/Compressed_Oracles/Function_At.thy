section \<open>\<open>Function_At\<close> -- Function values as individual registers\<close>

theory Function_At
imports Registers.Quantum_Extra Misc_Compressed_Oracle
begin

unbundle no m_inv_syntax

typedef ('a,'b) punctured_function = \<open>extensional (-{undefined}) :: ('a\<Rightarrow>'b) set\<close>
  by auto
setup_lifting type_definition_punctured_function
instance punctured_function :: (finite, finite) finite
  apply standard apply (rule finite_imageD[where f=Rep_punctured_function])
  by (auto simp add: Rep_punctured_function_inject inj_on_def)

lift_definition fix_punctured_function :: \<open>'a \<Rightarrow> ('b \<times> ('a,'b) punctured_function) \<Rightarrow> ('a\<Rightarrow>'b)\<close> is
  \<open>\<lambda>x (y, f). (Fun.swap x undefined f) (x := y)\<close>.

lift_definition puncture_function :: \<open>'a \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b \<times> ('a,'b) punctured_function\<close> is
  \<open>\<lambda>x f. (f x, (Fun.swap x undefined f) (undefined := undefined))\<close>
  by (simp add: Compl_eq_Diff_UNIV) 

lemma puncture_function_recombine:
  \<open>(y, snd (puncture_function x f)) = puncture_function x (f(x:=y))\<close>
  apply transfer
  by (auto intro!: ext simp: Transposition.transpose_def)
  
lemma snd_puncture_function_upd: \<open>snd (puncture_function x (f(x:=y))) = snd (puncture_function x f)\<close>
  apply transfer
  by (auto intro!: ext simp: Transposition.transpose_def)

lemma puncture_function_split: \<open>puncture_function x f = (f x, snd (puncture_function x f))\<close>
  using puncture_function_recombine[where x=x and f=f and y=\<open>f x\<close>]
  by simp

lemma puncture_function_inverse[simp]: \<open>fix_punctured_function x (puncture_function x f) = f\<close>
  apply transfer by (auto intro!: ext simp: Transposition.transpose_def)

lemma fix_punctured_function_inverse[simp]: \<open>puncture_function x (fix_punctured_function x yf) = yf\<close>
  apply transfer 
  by (auto intro!: ext simp: Transposition.transpose_def extensional_def)

lemma bij_fix_punctured_function[simp]: \<open>bij (fix_punctured_function x)\<close>
  by (metis bijI' fix_punctured_function_inverse puncture_function_inverse)

lemma inj_fix_punctured_function[simp]: \<open>inj (fix_punctured_function x)\<close>
  by (simp add: bij_is_inj)

lemma surj_fix_punctured_function[simp]: \<open>surj (fix_punctured_function x)\<close>
  by (simp add: bij_is_surj)

text \<open>The following \<^term>\<open>function_at_U x\<close> provides an unitary isomorphism between \<^typ>\<open>('a \<Rightarrow> 'b) ell2\<close> (superposition of functions)
and \<^typ>\<open>('b \<times> ('a, 'b) punctured_function) ell2\<close> (superposition of pairs of the value of 
the function at \<^term>\<open>x\<close> and the rest of the function).
This allows to then apply a some operation to the first part of that pair and thus lifting it to an application to the whole function.
(The "rest of the function" part is to be considered opaque.)\<close>

definition function_at_U :: \<open>'a \<Rightarrow> ('b \<times> ('a, 'b) punctured_function) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<Rightarrow> 'b) ell2\<close> where
 \<open>function_at_U x = classical_operator (Some o fix_punctured_function x)\<close>

lemma unitary_function_at_U[simp]: \<open>unitary (function_at_U x)\<close>
  by (auto simp: function_at_U_def intro!: unitary_classical_operator)

lemma function_at_U_ket[simp]: \<open>function_at_U x *\<^sub>V ket y = ket (fix_punctured_function x y)\<close>
  by (simp add: function_at_U_def classical_operator_ket classical_operator_exists_inj)

lemma function_at_U_adj_ket[simp]: \<open>(function_at_U x)* *\<^sub>V ket y = ket (puncture_function x y)\<close>
  apply (simp add: function_at_U_def inv_map_total classical_operator_ket classical_operator_exists_inj)
  by (metis (no_types, lifting) bij_betw_inv_into bij_def bij_fix_punctured_function classical_operator_exists_inj classical_operator_ket inj_map_total inv_f_f o_def option.case(2) puncture_function_inverse)

text \<open>The reference \<open>function_at x\<close> lifts an operation \<^term>\<open>U\<close> on \<^typ>\<open>'a ell2\<close> to an operation on \<^typ>\<open>('a \<Rightarrow> 'b) ell2\<close> (superposition of functions).
The resulting operation applies \<^term>\<open>U\<close> only to the \<^term>\<open>x\<close>-output of the function.\<close>

definition function_at :: \<open>'a \<Rightarrow> ('b update \<Rightarrow> ('a\<Rightarrow>'b) update)\<close> where
 \<open>function_at x = sandwich (function_at_U x) o Fst\<close>

lemma Rep_ell2_function_at_ket:
  \<open>Rep_ell2 (function_at x U *\<^sub>V ket f) g = 
      of_bool (snd (puncture_function x f) = snd (puncture_function x g)) * Rep_ell2 (U *\<^sub>V ket (f x)) (g x)\<close>
proof -
  have \<open>Rep_ell2 (function_at x U *\<^sub>V ket f) g = Rep_ell2 (function_at_U x *\<^sub>V (U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (puncture_function x f)) g\<close>
    by (simp add: function_at_def Fst_def sandwich_apply)
  also have \<open>\<dots> = (function_at_U x* *\<^sub>V ket g) \<bullet>\<^sub>C ((U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (puncture_function x f))\<close>
    by (metis cinner_adj_left cinner_ket_left)
  also have \<open>\<dots> = (ket (puncture_function x g)) \<bullet>\<^sub>C ((U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (puncture_function x f))\<close>
    by (simp add: function_at_def)
  also have \<open>\<dots> = (ket (g x, snd (puncture_function x g))) \<bullet>\<^sub>C ((U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (f x, snd (puncture_function x f)))\<close>
    by (simp flip: puncture_function_split)
  also have \<open>\<dots> = of_bool (snd (puncture_function x f) = snd (puncture_function x g)) * (ket (g x) \<bullet>\<^sub>C (U *\<^sub>V ket (f x)))\<close>
    by (simp add: tensor_op_ell2 cinner_ket flip: tensor_ell2_ket)
  also have \<open>\<dots> = of_bool (snd (puncture_function x f) = snd (puncture_function x g)) * Rep_ell2 (U *\<^sub>V ket (f x)) (g x)\<close>
    by (simp add: cinner_ket_left)
  finally show ?thesis
    by -
qed


lemma function_at_ket:
  shows \<open>function_at x U *\<^sub>V ket f = (\<Sum>\<^sub>\<infinity>y\<in>UNIV. Rep_ell2 (U *\<^sub>V ket (f x)) y *\<^sub>C ket (f (x := y)))\<close>
proof -
  have \<open>function_at x U *\<^sub>V ket f = function_at_U x *\<^sub>V (U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (puncture_function x f)\<close>
    by (simp add: function_at_def Fst_def sandwich_apply)
  also have \<open>\<dots> = function_at_U x *\<^sub>V (U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (f x, snd (puncture_function x f))\<close>
    by (metis puncture_function_split)
  also have \<open>\<dots> = function_at_U x *\<^sub>V ((U *\<^sub>V ket (f x)) \<otimes>\<^sub>s ket (snd (puncture_function x f)))\<close>
    by (simp add: tensor_op_ket)
  also have \<open>\<dots> = function_at_U x *\<^sub>V ((\<Sum>\<^sub>\<infinity>y\<in>UNIV. Rep_ell2 (U *\<^sub>V ket (f x)) y *\<^sub>C ket y) \<otimes>\<^sub>s ket (snd (puncture_function x f)))\<close>
    by (simp flip: ell2_decompose_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>UNIV. Rep_ell2 (U *\<^sub>V ket (f x)) y *\<^sub>C (function_at_U x *\<^sub>V (ket y \<otimes>\<^sub>s ket (snd (puncture_function x f)))))\<close>
    by (simp del: function_at_U_ket 
        add: tensor_ell2_scaleC1 invertible_cblinfun_isometry infsum_cblinfun_apply_invertible infsum_tensor_ell2_left
        flip: cblinfun.scaleC_right)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>UNIV. Rep_ell2 (U *\<^sub>V ket (f x)) y *\<^sub>C ket (f (x := y)))\<close>
    by (simp add: puncture_function_recombine tensor_ell2_ket)
  finally show ?thesis
    by -
qed

lemma register_function_at[simp, register]: \<open>register (function_at x :: 'b update \<Rightarrow> ('a\<Rightarrow>'b) update)\<close> for x :: 'a
  by (auto simp add: function_at_def unitary_sandwich_register)

lemma function_at_comm:
  fixes U V :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> and x y :: 'a
  assumes \<open>x \<noteq> y\<close>
  shows \<open>function_at x U o\<^sub>C\<^sub>L function_at y V = function_at y V o\<^sub>C\<^sub>L function_at x U\<close>
proof -
  define reorder where \<open>reorder = classical_operator (Some o (\<lambda>(f :: 'a \<Rightarrow> 'b, a, b). (f(x:=a, y:=b), f x, f y)))\<close>

  have selfinv: \<open>(\<lambda>(f, a, b). (f(x := a, y := b), f x, f y)) o (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y)) = id\<close>
    using assms by (auto intro!: ext)
  have bij: \<open>bij (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y))\<close>
    using o_bij selfinv by blast
  have inv: \<open>inv (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y)) = (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y))\<close>
  using inv_unique_comp selfinv by blast
  have inj_map: \<open>inj_map (Some o (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y)))\<close>
    by (simp add: inj_map_total bij_is_inj[OF bij])
  have inv: \<open>inv_map (Some o (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y))) = (Some o (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y)))\<close>
    by (simp add: inv_map_total bij_is_surj bij inv)
  have reorder_exists: \<open>classical_operator_exists (Some o (\<lambda>(f, a, b). (f(x := a, y := b), f x, f y)))\<close>
    using inj_map by (rule classical_operator_exists_inj)

  have [simp]: \<open>reorder* = reorder\<close>
    by (simp add: reorder_def classical_operator_adjoint[OF inj_map] inv)
  have [simp]: \<open>reorder (ket f \<otimes>\<^sub>s ket a \<otimes>\<^sub>s ket b) = ket (f(x:=a, y:=b), f x, f y)\<close> for f a b
    by (simp add: reorder_def tensor_ell2_ket classical_operator_ket[OF reorder_exists])
  have [simp]: \<open>isometry reorder\<close>
    using inj_map_total isometry_classical_operator inj_map reorder_def by blast

  have sandwichU: \<open>sandwich reorder (function_at x U \<otimes>\<^sub>o id_cblinfun) = id_cblinfun \<otimes>\<^sub>o (U \<otimes>\<^sub>o id_cblinfun)\<close>
  proof  (rule equal_ket, rule cinner_ket_eqI, rename_tac fab gcd)
    fix fab gcd :: \<open>('a \<Rightarrow> 'b) \<times> 'b \<times> 'b\<close>
    obtain f a b where [simp]: \<open>fab = (f,a,b)\<close>
      by (auto simp: prod_eq_iff)
    obtain g c d where [simp]: \<open>gcd = (g,c,d)\<close>
      by (auto simp: prod_eq_iff)
    have fg_rewrite: \<open>f = g \<and> b = d \<longleftrightarrow> 
        snd (puncture_function x (f(x := a, y := b))) = snd (puncture_function x (g(x := c, y := d))) \<and> f x = g x \<and> f y = g y\<close>
      using assms
      by (smt (verit, del_insts) array_rules(3) fun_upd_idem fun_upd_twist puncture_function_inverse puncture_function_recombine snd_puncture_function_upd)
    have \<open>ket gcd \<bullet>\<^sub>C ((sandwich reorder *\<^sub>V function_at x U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket fab)
      = ket (g(x:=c, y:=d), g x, g y) \<bullet>\<^sub>C ((function_at x U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (f(x:=a, y:=b), f x, f y))\<close>
      by (simp add: sandwich_apply flip: cinner_adj_left tensor_ell2_ket)
    also have \<open>\<dots> = (ket (g(x:=c, y:=d)) \<bullet>\<^sub>C (function_at x U *\<^sub>V ket (f(x:=a, y:=b))))
                     * of_bool (f x = g x \<and> f y = g y)\<close>
      by (auto simp add: tensor_op_ell2 simp flip: tensor_ell2_ket)
    also have \<open>\<dots> = Rep_ell2 (U *\<^sub>V ket a) c * of_bool (f = g \<and> b = d)\<close>
      using assms by (auto simp add: cinner_ket_left Rep_ell2_function_at_ket fg_rewrite)
    also have \<open>\<dots> = ket gcd \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket fab)\<close>
      by (auto simp add: tensor_op_ell2 cinner_ket_left[of c] simp flip: tensor_ell2_ket)
    finally show \<open>ket gcd \<bullet>\<^sub>C ((sandwich reorder *\<^sub>V function_at x U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket fab) =
                ket gcd \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o U \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket fab)\<close>
      by -
  qed

  have sandwichV: \<open>sandwich reorder (function_at y V \<otimes>\<^sub>o id_cblinfun) = id_cblinfun \<otimes>\<^sub>o (id_cblinfun \<otimes>\<^sub>o V)\<close>
  proof  (rule equal_ket, rule cinner_ket_eqI, rename_tac fab gcd)
    fix fab gcd :: \<open>('a \<Rightarrow> 'b) \<times> 'b \<times> 'b\<close>
    obtain f a b where [simp]: \<open>fab = (f,a,b)\<close>
      by (auto simp: prod_eq_iff)
    obtain g c d where [simp]: \<open>gcd = (g,c,d)\<close>
      by (auto simp: prod_eq_iff)
    have fg_rewrite: \<open>f = g \<and> a = c \<longleftrightarrow> 
        snd (puncture_function y (f(x := a, y := b))) = snd (puncture_function y (g(x := c, y := d))) \<and> f x = g x \<and> f y = g y\<close>
      using assms
      by (metis array_rules(3) fun_upd_idem fun_upd_twist puncture_function_inverse puncture_function_recombine snd_puncture_function_upd)
    have \<open>ket gcd \<bullet>\<^sub>C ((sandwich reorder *\<^sub>V function_at y V \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket fab)
      = ket (g(x:=c, y:=d), g x, g y) \<bullet>\<^sub>C ((function_at y V \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (f(x:=a, y:=b), f x, f y))\<close>
      by (simp add: sandwich_apply flip: cinner_adj_left tensor_ell2_ket)
    also have \<open>\<dots> = (ket (g(x:=c, y:=d)) \<bullet>\<^sub>C (function_at y V *\<^sub>V ket (f(x:=a, y:=b))))
                     * of_bool (f x = g x \<and> f y = g y)\<close>
      by (auto simp add: tensor_op_ell2 simp flip: tensor_ell2_ket)
    also have \<open>\<dots> = Rep_ell2 (V *\<^sub>V ket b) d * of_bool (f = g \<and> a = c)\<close>
      using assms by (auto simp add: cinner_ket_left Rep_ell2_function_at_ket fg_rewrite)
    also have \<open>\<dots> = ket gcd \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o V) *\<^sub>V ket fab)\<close>
      by (auto simp add: tensor_op_ell2 cinner_ket_left[of d] simp flip: tensor_ell2_ket)
    finally show \<open>ket gcd \<bullet>\<^sub>C ((sandwich reorder *\<^sub>V function_at y V \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket fab) =
                ket gcd \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o V) *\<^sub>V ket fab)\<close>
      by -
  qed

  have \<open>sandwich reorder ((function_at x U \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (function_at y V \<otimes>\<^sub>o id_cblinfun))
      = sandwich reorder ((function_at y V \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (function_at x U \<otimes>\<^sub>o id_cblinfun))\<close>
    apply (simp add: sandwichU sandwichV flip: sandwich_arg_compose)
    by (simp add: comp_tensor_op)
  then have \<open>(function_at x U \<otimes>\<^sub>o (id_cblinfun :: ('b \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'b) ell2)) o\<^sub>C\<^sub>L (function_at y V \<otimes>\<^sub>o id_cblinfun) = (function_at y V \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (function_at x U \<otimes>\<^sub>o id_cblinfun)\<close>
    by (smt (verit, best) \<open>isometry reorder\<close> cblinfun_compose_id_left cblinfun_compose_id_right compatible_ac_rules(2) isometryD sandwich_apply)
  then have \<open>(function_at x U o\<^sub>C\<^sub>L function_at y V) \<otimes>\<^sub>o (id_cblinfun :: ('b \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'b) ell2) = (function_at y V o\<^sub>C\<^sub>L function_at x U) \<otimes>\<^sub>o id_cblinfun\<close>
    by (simp add: comp_tensor_op)
  then show \<open>function_at x U o\<^sub>C\<^sub>L function_at y V = function_at y V o\<^sub>C\<^sub>L function_at x U\<close>
    apply (rule injD[OF inj_tensor_left, rotated])
    by simp
qed

  

lemma compatible_function_at[simp]: 
  assumes \<open>x \<noteq> y\<close>
  shows \<open>compatible (function_at x) (function_at y)\<close>
proof (rule compatibleI)
  show \<open>register (function_at x)\<close>
    by simp
  show \<open>register (function_at y)\<close>
    by simp
  fix a b :: \<open>'b update\<close>
  show \<open>function_at x a o\<^sub>C\<^sub>L function_at y b = function_at y b o\<^sub>C\<^sub>L function_at x a\<close>
    using assms by (rule function_at_comm)
qed

lemma inv_fix_punctured_function[simp]: \<open>inv (fix_punctured_function x) = puncture_function x\<close>
  by (simp add: inv_equality)

lemma bij_puncture_function[simp]: \<open>bij (puncture_function x)\<close>
  by (metis bij_betw_inv_into bij_fix_punctured_function inv_fix_punctured_function)

lemma fst_puncture_function[simp]: \<open>fst (puncture_function x H) = H x\<close>
  apply transfer by simp

subsection \<open>\<open>apply_every\<close>\<close>

text \<open>Analogue to classical \<^term>\<open>\<lambda>(M::'a set) (u::'a \<Rightarrow> 'b \<Rightarrow> 'b) (f::'a \<Rightarrow> 'b) (x::'a). if x\<in>M then u x (f x) else f x\<close>.

Note that the definition only makes sense when \<^term>\<open>M\<close> is finite.
In fact, a definition that works for infinite \<^term>\<open>M\<close> is impossible as the following example shows:
Let \<^term>\<open>H\<close> denote the Hadamard matrix. Let \<^term>\<open>M=(UNIV :: nat set)\<close>.
Then, by symmetry, a meaningful definition of \<^term>\<open>apply_every\<close> would have that \<^term>\<open>apply_every M H (ket (\<lambda>_. 0))\<close>
would be a vector in \<^typ>\<open>(nat => bit) ell2\<close> with all coefficients equal.
But the only such vector is \<^term>\<open>0\<close>. But a meaningful definition should not map \<^term>\<open>ket (\<lambda>_. 0)\<close> to \<^term>\<open>0\<close>.\<close>

definition apply_every where \<open>apply_every M U = (if finite M then Finite_Set.fold (\<lambda>x a. function_at x (U x) o\<^sub>C\<^sub>L a) id_cblinfun M else 0)\<close>

lemma apply_every_empty[simp]: \<open>apply_every {} U = id_cblinfun\<close>
  by (simp add: apply_every_def)

interpretation apply_every_aux: comp_fun_commute \<open>(\<lambda>x. (o\<^sub>C\<^sub>L) (function_at x (U x)))\<close>
  apply standard
  apply (rule ext)
  apply (case_tac \<open>x=y\<close>)
  by (auto simp flip: cblinfun_compose_assoc swap_registers_left)

lemma apply_every_unitary: \<open>unitary (apply_every M U)\<close> if  \<open>finite M\<close> and [simp]: \<open>\<And>x. x\<in>M \<Longrightarrow> unitary (U x)\<close>
proof -
  show ?thesis
    using that
  proof induction
    case empty
    then show ?case 
      by simp
  next
    case (insert x F)
    then have *: \<open>apply_every (insert x F) U = function_at x (U x) o\<^sub>C\<^sub>L apply_every F U\<close>
      by (simp add: apply_every_def)
    show ?case
      by (simp add: * register_unitary insert)
  qed
qed

lemma apply_every_comm: \<open>apply_every M U o\<^sub>C\<^sub>L V = V o\<^sub>C\<^sub>L apply_every M U\<close>
  if \<open>finite M\<close> and \<open>\<And>x. x\<in>M \<Longrightarrow> function_at x (U x) o\<^sub>C\<^sub>L V = V o\<^sub>C\<^sub>L function_at x (U x)\<close>
  unfolding apply_every_def using that
proof induction
  case empty
  show ?case
    by simp
next
  case (insert x F)
  then show ?case
    apply (simp add: insert cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc  insert.prems)
qed

lemma apply_every_infinite: \<open>apply_every M U = 0\<close> if \<open>infinite M\<close>
  using that by (simp add: apply_every_def)


lemma apply_every_split: \<open>apply_every M U o\<^sub>C\<^sub>L apply_every N U = apply_every (M \<union> N) U\<close> if \<open>M \<inter> N = {}\<close> for M N U
proof -
  wlog finiteM: \<open>finite M\<close>
    using negation
    by (simp add: apply_every_infinite)
  wlog finiteN: \<open>finite N\<close> keeping finiteM
    using negation
    by (simp add: apply_every_infinite)
  define f :: \<open>'a \<Rightarrow> ('a \<Rightarrow> 'b) update \<Rightarrow> ('a \<Rightarrow> 'b) update\<close> where \<open>f x = (o\<^sub>C\<^sub>L) (function_at x (U x))\<close> for x
  define fM fN where \<open>fM = Finite_Set.fold f id_cblinfun M\<close> and \<open>fN = Finite_Set.fold f id_cblinfun N\<close>
  have \<open>apply_every (M \<union> N) U = apply_every (N \<union> M) U\<close>
    by (simp add: Un_commute)
  also have \<open>\<dots> = Finite_Set.fold f (Finite_Set.fold f id_cblinfun N) M\<close>
    unfolding apply_every_def
    apply (subst apply_every_aux.fold_set_union_disj)
    using finiteM finiteN that by (auto simp add: f_def[abs_def])
  also have \<open>\<dots> = fM o\<^sub>C\<^sub>L fN\<close>
    unfolding fM_def fN_def[symmetric]
    using finiteM
    apply (induction M)
    by (auto simp add: f_def[abs_def] cblinfun_compose_assoc)
  also have \<open>\<dots> = apply_every M U o\<^sub>C\<^sub>L apply_every N U\<close>
    by (simp add: apply_every_def fN_def fM_def f_def[abs_def] finiteN finiteM)
  finally show ?thesis
    by simp
qed

lemma apply_every_single[simp]: \<open>apply_every {x} U = function_at x (U x)\<close>
  by (simp add: apply_every_def)

lemma apply_every_insert: \<open>apply_every (insert x M) U = function_at x (U x) o\<^sub>C\<^sub>L apply_every M U\<close> if \<open>x \<notin> M\<close> and \<open>finite M\<close>
  using that by (simp add: apply_every_def)

lemma apply_every_mult: \<open>apply_every M U o\<^sub>C\<^sub>L apply_every M V = apply_every M (\<lambda>x. U x o\<^sub>C\<^sub>L V x)\<close>
proof (induction rule:infinite_finite_induct)
  case (infinite M)
  then show ?case
    by (simp add: apply_every_infinite)
next
  case empty
  show ?case 
    by simp
next
  case (insert x F)
  have \<open>apply_every (insert x F) U o\<^sub>C\<^sub>L apply_every (insert x F) V
      = function_at x (U x) o\<^sub>C\<^sub>L (apply_every F U o\<^sub>C\<^sub>L function_at x (V x)) o\<^sub>C\<^sub>L apply_every F V\<close>
    using insert by (simp add: apply_every_insert cblinfun_compose_assoc)
  also have \<open>\<dots> = (function_at x (U x) o\<^sub>C\<^sub>L function_at x (V x)) o\<^sub>C\<^sub>L (apply_every F U o\<^sub>C\<^sub>L apply_every F V)\<close>
    apply (subst apply_every_comm)
      apply (fact insert)
    using insert apply (metis (no_types, lifting) compatible_function_at swap_registers)
    by (simp add: cblinfun_compose_assoc)
  also have \<open>\<dots> = (function_at x (U x o\<^sub>C\<^sub>L V x)) o\<^sub>C\<^sub>L (apply_every F U o\<^sub>C\<^sub>L apply_every F V)\<close>
    by (simp add: register_mult)
  also have \<open>\<dots> = (function_at x (U x o\<^sub>C\<^sub>L V x)) o\<^sub>C\<^sub>L (apply_every F (\<lambda>x. U x o\<^sub>C\<^sub>L V x))\<close>
    using insert.IH by presburger
  also have \<open>\<dots> = (apply_every (insert x F) (\<lambda>x. U x o\<^sub>C\<^sub>L V x))\<close>
    using insert.hyps by (simp add: apply_every_insert)
  finally show ?case
    by -
qed

lemma apply_every_id[simp]: \<open>apply_every M (\<lambda>_. id_cblinfun) = id_cblinfun\<close> if \<open>finite M\<close>
  using that apply induction
  by (auto simp: apply_every_insert)

lemma apply_every_function_at_comm:
  assumes \<open>x \<notin> M\<close>
  shows \<open>function_at x U o\<^sub>C\<^sub>L apply_every M f = apply_every M f o\<^sub>C\<^sub>L function_at x U\<close>
  using assms apply (induction rule: infinite_finite_induct)
    apply (simp add: apply_every_infinite)
   apply simp
  apply (simp add: apply_every_insert function_at_comm[where x=x] 
      flip: cblinfun_compose_assoc)
  by (simp add: cblinfun_compose_assoc)

lemma apply_every_adj: \<open>(apply_every M f)* = apply_every M (\<lambda>i. (f i)*)\<close>
  apply (induction rule: infinite_finite_induct)
    apply (simp add: apply_every_infinite)
   apply simp
  by (simp add: apply_every_insert apply_every_function_at_comm register_adjoint)

end
