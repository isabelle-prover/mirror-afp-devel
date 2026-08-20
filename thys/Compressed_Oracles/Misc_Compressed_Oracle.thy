section \<open>\<open>Misc_Compressed_Oracle\<close> -- Miscellaneous required theorems\<close>

theory Misc_Compressed_Oracle
  imports Registers.Quantum_Extra2
begin

declare [[simproc del: Laws_Quantum.compatibility_warn]]

unbundle cblinfun_syntax
unbundle register_syntax


subsection Misc

lemma assoc_ell2'_ket[simp]: \<open>assoc_ell2* *\<^sub>V ket (x,y,z) = ket ((x,y),z)\<close>
  by (metis assoc_ell2'_tensor tensor_ell2_ket)

lemma assoc_ell2_ket[simp]: \<open>assoc_ell2 *\<^sub>V ket ((x,y),z) = ket (x,y,z)\<close>
  by (metis assoc_ell2_tensor tensor_ell2_ket)

lemma sandwich_tensor: 
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::finite ell2\<close> and b :: \<open>'b::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2\<close> 
  assumes \<open>unitary a\<close> \<open>unitary b\<close>
  shows "cblinfun_apply (sandwich (a \<otimes>\<^sub>o b)) = cblinfun_apply (sandwich a) \<otimes>\<^sub>r cblinfun_apply (sandwich b)"
  apply (rule tensor_extensionality)
  by (auto simp: unitary_sandwich_register assms sandwich_apply register_tensor_is_register comp_tensor_op tensor_op_adjoint unitary_tensor_op)

(* Move next to id_tensor_sandwich, rename accordingly *)
lemma sandwich_grow_left: 
  fixes a :: \<open>'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2\<close>
  assumes "unitary a"
  shows "sandwich a \<otimes>\<^sub>r id = sandwich (a \<otimes>\<^sub>o (id_cblinfun :: (_::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L _)))"
  by (simp add: unitary_sandwich_register assms sandwich_tensor id_def)

lemma Snd_apply_tensor_ell2[simp]: \<open>Snd a *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = \<psi> \<otimes>\<^sub>s (a *\<^sub>V \<phi>)\<close>
  by (simp add: Snd_def tensor_op_ell2)

ML \<open>
fun register_n_of_m n m = let
  val _ = n > 0 orelse error "register_n_of_m: n<=0"
  val _ = m >= n orelse error "register_n_of_m: n>m"
  val id_op = Const(\<^const_name>\<open>id_cblinfun\<close>,dummyT)
  val tensor_op = Const(\<^const_name>\<open>tensor_op\<close>,dummyT)
  fun add_ids 0 t = t
    | add_ids i t = tensor_op $ id_op $ add_ids (i-1) t
  val body = if n=m then add_ids (n-1) (Bound 0)
                    else add_ids (n-1) (tensor_op $ Bound 0 $ add_ids (m-n-1) id_op)
in 
  Abs("a", dummyT, body)
end
;;
register_n_of_m 5 5 |> Syntax.string_of_term \<^context> |> writeln
\<close>

ML \<open>
fun dest_numeral_syntax (Const(\<^const_syntax>\<open>Num.num.One\<close>, _)) = 1
  | dest_numeral_syntax (Const(\<^const_syntax>\<open>Num.num.Bit0\<close>, _) $ bs) = 2 * dest_numeral_syntax bs
  | dest_numeral_syntax (Const (\<^const_syntax>\<open>Num.num.Bit1\<close>, _) $ bs) = 2 * dest_numeral_syntax bs + 1
  | dest_numeral_syntax (Const ("_constrain", _) $ t $ _) = dest_numeral_syntax t
  | dest_numeral_syntax t = raise TERM ("dest_numeral_syntax", [t]);

fun dest_number_syntax (Const (\<^const_syntax>\<open>Groups.zero_class.zero\<close>, _)) = 0
  | dest_number_syntax (Const (\<^const_syntax>\<open>Groups.one_class.one\<close>, _)) = 1
  | dest_number_syntax (Const (\<^const_syntax>\<open>Num.numeral_class.numeral\<close>, _) $ t) =
      dest_numeral_syntax t
  | dest_number_syntax (Const (\<^const_syntax>\<open>Groups.uminus_class.uminus\<close>, _) $ t) =
      ~ (dest_number_syntax t)
  | dest_number_syntax (Const ("_constrain", _) $ t $ _) = dest_number_syntax t
  | dest_number_syntax t = raise TERM ("dest_number_syntax", [t])
\<close>


syntax "_register_n_of_m" :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'b\<close> ("[_\<^sub>_]")
parse_translation \<open>[(\<^syntax_const>\<open>_register_n_of_m\<close>, fn ctxt => fn [nt,mt] => let
  val n = dest_number_syntax nt
  val m = dest_number_syntax mt
  in register_n_of_m n m end
)]\<close>
ML \<open>
Syntax.read_term \<^context> "[8\<^sub>9]" |> Thm.cterm_of \<^context>
\<close>

lemma sum_if: \<open>(\<Sum>x\<in>X. P (if Q x then a x else b x)) = (\<Sum>x\<in>X. if Q x then P (a x) else P (b x))\<close>
  by (smt (verit) Finite_Cartesian_Product.sum_cong_aux)

lemma sum_if': \<open>(\<Sum>x\<in>X. P (if Q x then a x else b x) x) = (\<Sum>x\<in>X. if Q x then P (a x) x else P (b x) x)\<close>
  by (smt (verit) Finite_Cartesian_Product.sum_cong_aux)

(* (* Not used *)
lemma sum_sum_eq_Some: \<open>(\<Sum>x\<in>UNIV. \<Sum>y\<in>Y. if x=Some y then a x y else 0) = (\<Sum>y\<in>Y. a (Some y) y)\<close> *)

lemma bij_plus: \<open>bij ((+) y)\<close> for y :: \<open>_::group_add\<close>
  by simp

lemma tensor_ell2_diff2: \<open>tensor_ell2 a (b - c) = tensor_ell2 a b - tensor_ell2 a c\<close>
  by (metis add_diff_cancel_right' diff_add_cancel tensor_ell2_add2)
lemma tensor_ell2_diff1: \<open>tensor_ell2 (a - b) c = tensor_ell2 a c - tensor_ell2 b c\<close>
  by (metis add_right_cancel diff_add_cancel tensor_ell2_add1)

lemma aminus_bminusc: \<open>a - (b - c) = a - b + c\<close> for a b c :: \<open>_ :: ab_group_add\<close>
  by simp

lemma sum_case': 
  fixes a :: \<open>_ \<Rightarrow> _ \<Rightarrow> _::ab_group_add\<close>
  assumes \<open>finite X\<close>
  shows \<open>(\<Sum>x\<in>X. P (case Q x of Some z \<Rightarrow> a z x | None \<Rightarrow> b x)) 
  = (\<Sum>x\<in>X \<inter> {x. Q x \<noteq> None}. P (a (the (Q x)) x)) + (\<Sum>x\<in>X \<inter> {x. Q x = None}. P (b x))\<close> 
  (is "?lhs=?rhs")
proof -
  have \<open>?lhs = (\<Sum>x\<in>X \<inter> (Q -` Some ` UNIV). P (case Q x of Some z \<Rightarrow> a z x | None \<Rightarrow> b x)) + (\<Sum>x\<in>X \<inter> (Q -` {None}). P (case Q x of Some z \<Rightarrow> a z x | None \<Rightarrow> b x))\<close>
    apply (subst sum.union_disjoint[symmetric])
    using assms apply auto
    by (metis Int_UNIV_right Int_Un_distrib UNIV_option_conv insert_union vimage_UNIV vimage_Un)
  also have \<open>\<dots> = ?rhs\<close>
    apply (rule arg_cong2[where f=plus])
     apply (rule sum.cong)
      apply auto[2]
    apply (rule sum.cong)
    by auto
  finally show ?thesis
    by -
qed


lemma register_isometry:
  assumes "register F"
  assumes "isometry a"
  shows "isometry (F a)"
  using assms by (smt (verit, best) register_def isometry_def)

lemma register_coisometry:
  assumes "register F"
  assumes "isometry (a*)"
  shows "isometry (F a*)"
  using assms by (smt (verit, best) register_def isometry_def)

lemma card_complement:
  fixes M :: \<open>'a::finite set\<close>
  shows \<open>card (-M) = CARD('a) - card M\<close>
  by (simp add: Compl_eq_Diff_UNIV card_Diff_subset)

lemma register_minus: \<open>register F \<Longrightarrow> F (a - b) = F a - F b\<close>
  using clinear_register complex_vector.linear_diff by blast

lemma vimage_singleton_inj: \<open>inj f \<Longrightarrow> f -` {f x} = {x}\<close>
  using inj_vimage_singleton subset_singletonD by fastforce

lemma has_ell2_norm_0[iff]: \<open>has_ell2_norm (\<lambda>x. 0)\<close>
  by (metis eq_onp_same_args zero_ell2.rsp)

lemma ell2_norm_0I[simp]: \<open>ell2_norm (\<lambda>x. 0) = 0\<close>
  using ell2_norm_0 by blast

lemma ran_smaller_dom: \<open>finite (dom m) \<Longrightarrow> card (ran m) \<le> card (dom m)\<close>
  apply (rule surj_card_le[where f=\<open>the o m\<close>], simp)
  unfolding dom_def ran_def by force


lemma option_sum_split: \<open>(\<Sum>x\<in>X. f x) = (\<Sum>x\<in>Some -` X. f (Some x)) + (if None \<in> X then f None else 0)\<close> if \<open>finite X\<close> for f X
  apply (subst asm_rl[of \<open>X = (Some ` Some -` X) \<union> ({None} \<inter> X)\<close>])
   apply auto[1]
  apply (subst sum.union_disjoint)
     apply (auto simp: that)[3]
  apply (subst sum.reindex)
  by auto

lemma sum_sum_if_eq: \<open>(\<Sum>x\<in>X. \<Sum>y\<in>Y x. if x=a then f x y else 0) = (if a\<in>X then (\<Sum>y\<in>Y a. f a y) else 0)\<close> if \<open>finite X\<close> for X Y f
  by (subst sum_single[where i=a], auto simp: that)

lemma sum_if_eq_else: \<open>(\<Sum>x\<in>X. if x=a then 0 else f x) = (\<Sum>x\<in>X-{a}. f x)\<close> for X f
  apply (cases \<open>finite X\<close>)
   apply (rule sum.mono_neutral_cong_right)
  by auto

(* lemma sum_if_eq_else': \<open>(\<Sum>x\<in>X. if a=x then 0 else f x) = (\<Sum>x\<in>X-{a}. f x)\<close> for X f
  apply (cases \<open>finite X\<close>)
   apply (rule sum.mono_neutral_cong_right)
  by auto *)

lemma fun_upd_comp_left:
  assumes \<open>inj g\<close>
  shows \<open>(f \<circ> g)(x := y) = f(g x := y) o g\<close>
  by (auto simp: fun_upd_def assms inj_eq)


definition reg_1_3 :: \<open>_ \<Rightarrow> ('a::finite \<times> 'b::finite \<times> 'c::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b \<times> 'c) ell2\<close> where \<open>reg_1_3 = Fst\<close>
lemma register_1_3[simp]: \<open>register reg_1_3\<close>
  by (simp add: reg_1_3_def)

lemma comp_reg_1_3[simp]: \<open>(F;G) o reg_1_3 = F\<close> if [register]: \<open>compatible F G\<close>
  by (simp add: reg_1_3_def register_pair_Fst)

definition reg_2_3 :: \<open>_ \<Rightarrow> ('a::finite \<times> 'b::finite \<times> 'c::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b \<times> 'c) ell2\<close> where \<open>reg_2_3 = Snd o Fst\<close>
lemma register_2_3[simp]: \<open>register reg_2_3\<close>
  by (simp add: reg_2_3_def)
lemma comp_reg_2_3[simp]: \<open>(F;(G;H)) o reg_2_3 = G\<close> if [register]: \<open>compatible F G\<close> \<open>compatible F H\<close> \<open>compatible G H\<close>
  by (simp add: reg_2_3_def register_pair_Fst register_pair_Snd flip: comp_assoc)


definition reg_3_3 :: \<open>_ \<Rightarrow> ('a::finite \<times> 'b::finite \<times> 'c::finite) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b \<times> 'c) ell2\<close> where \<open>reg_3_3 = Snd o Snd\<close>
lemma register_3_3[simp]: \<open>register reg_3_3\<close>
  by (simp add: reg_3_3_def)
lemma comp_reg_3_3[simp]: \<open>(F;(G;H)) o reg_3_3 = H\<close> if [register]: \<open>compatible F G\<close> \<open>compatible F H\<close> \<open>compatible G H\<close>
  by (simp add: reg_3_3_def register_pair_Snd flip: comp_assoc)

lemma [simp]: \<open>mutually compatible (reg_1_3, reg_2_3, reg_3_3)\<close>
  by (auto simp add: reg_1_3_def reg_2_3_def reg_3_3_def)

lemma pair_o_tensor_right:
  assumes [simp]: \<open>compatible F G\<close> \<open>register H\<close>
  shows \<open>(F; G o H) = (F; G) o (id \<otimes>\<^sub>r H)\<close>
  by (auto simp: pair_o_tensor)

lemma register_tensor_distrib_right:
  assumes [simp]: \<open>register F\<close> \<open>register H\<close> \<open>register L\<close>
  shows \<open>F \<otimes>\<^sub>r (H o L) = (F \<otimes>\<^sub>r H) o (id \<otimes>\<^sub>r L)\<close>
  apply (subst register_tensor_distrib)
  by auto

lemma sandwich_apply':
  \<open>sandwich U A *\<^sub>V \<psi> = U *\<^sub>V A *\<^sub>V U* *\<^sub>V \<psi>\<close>
  unfolding sandwich_apply by simp

lemma csubspace_set_sum: 
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> csubspace (A x)\<close>
  shows \<open>csubspace (\<Sum>x\<in>X. A x)\<close>
  using assms
  apply (induction X rule:infinite_finite_induct)
  by (auto simp: csubspace_set_plus)

lemma Rep_ell2_vector_to_cblinfun_ket: \<open>Rep_ell2 \<psi> x = bra x *\<^sub>V \<psi>\<close>
  by (simp add: cinner_ket_left)

lemma trunc_ell2_insert: \<open>trunc_ell2 (insert x M) \<psi> = Rep_ell2 \<psi> x *\<^sub>C ket x + trunc_ell2 M \<psi>\<close> if \<open>x \<notin> M\<close>
  using trunc_ell2_union_disjoint[where M=\<open>{x}\<close> and N=M and \<psi>=\<psi>] that
  by (auto simp: trunc_ell2_singleton)

lemma trunc_ell2_in_cspan:
  assumes \<open>finite S\<close>
  shows \<open>trunc_ell2 S \<psi> \<in> cspan (ket ` S)\<close>
  using assms 
proof induction
  case empty
  show ?case
    by simp
next
  case (insert x F)
  then have \<open>Rep_ell2 \<psi> x *\<^sub>C ket x + trunc_ell2 F \<psi> \<in> cspan (insert (ket x) (ket ` F))\<close>
    by (metis add_diff_cancel_left' complex_vector.span_breakdown_eq)
  with insert show ?case
    by (auto simp: trunc_ell2_insert)
qed

lemma space_ccspan_ket: \<open>space_as_set (ccspan (ket ` M)) = {\<psi>. \<forall>x \<in> -M. Rep_ell2 \<psi> x = 0}\<close>
proof (intro Set.set_eqI iffI; rename_tac \<psi>)
  fix \<psi>
  assume \<psi>_in_ccspan: \<open>\<psi> \<in> space_as_set (ccspan (ket ` M))\<close>
  have \<open>Rep_ell2 \<psi> x = 0\<close> if \<open>x \<in> -M\<close> for x
  proof -
    have \<open>Rep_ell2 \<psi> x = vector_to_cblinfun (ket x)* *\<^sub>V \<psi>\<close>
      by (simp add: Rep_ell2_vector_to_cblinfun_ket)
    also have \<open>\<dots> \<in> vector_to_cblinfun (ket x)* ` space_as_set (ccspan (ket ` M))\<close>
      using \<psi>_in_ccspan by blast
    also have \<open>\<dots> \<subseteq> space_as_set (vector_to_cblinfun (ket x)* *\<^sub>S ccspan (ket ` M))\<close>
      by (simp add: cblinfun_image.rep_eq closure_subset)
    also have \<open>\<dots> = space_as_set (ccspan (vector_to_cblinfun (ket x)* ` ket ` M))\<close>
      by (simp add: cblinfun_image_ccspan)
    also have \<open>\<dots> = space_as_set (ccspan (if M={} then {} else {0}))\<close>
      apply (rule arg_cong[where f=\<open>\<lambda>x. space_as_set (ccspan x)\<close>])
      using \<open>x \<in> -M\<close> apply auto
      by (metis imageI orthogonal_ket)
    also have \<open>\<dots> = 0\<close>
      by simp
    finally show \<open>Rep_ell2 \<psi> x = 0\<close>
      by auto
  qed
  then show \<open>\<psi> \<in> {\<psi>. \<forall>x\<in>- M. Rep_ell2 \<psi> x = 0}\<close>
    by simp
next
  fix \<psi>
  assume \<open>\<psi> \<in> {\<psi>. \<forall>x\<in>- M. Rep_ell2 \<psi> x = 0}\<close>
  then have \<open>\<psi> = trunc_ell2 M \<psi>\<close>
    by (auto intro!: Rep_ell2_inject[THEN iffD1] ext simp: trunc_ell2.rep_eq)
  then have lim: \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top M)\<close>
    using trunc_ell2_lim[of \<psi> M]
    by auto
  have \<open>trunc_ell2 S \<psi> \<in> cspan (ket ` S)\<close> if \<open>finite S\<close> for S
    by (simp add: that trunc_ell2_in_cspan)
  also have \<open>\<dots>S \<subseteq> space_as_set (ccspan (ket ` M))\<close> if \<open>finite S\<close> and \<open>S \<subseteq> M\<close> for S
    by (metis ccspan.rep_eq closure_subset complex_vector.span_mono dual_order.trans image_mono that(2))
  finally show \<open>\<psi> \<in> space_as_set (ccspan (ket ` M))\<close>
    apply (rule_tac Lim_in_closed_set[OF _ _ _ lim])
    by (auto intro!: eventually_finite_subsets_at_top_weakI)
qed

lemma space_as_set_ccspan_memberI: \<open>\<psi> \<in> space_as_set (ccspan X)\<close> if \<open>\<psi> \<in> X\<close>
  using that apply transfer
  by (meson closure_subset complex_vector.span_superset subset_iff)

lemma closure_subset_remove_closure: \<open>X \<subseteq> closure Y \<Longrightarrow> closure X \<subseteq> closure Y\<close>
  using closure_minimal by blast

lemma closure_cspan_closure: \<open>closure (cspan (closure X)) = closure (cspan X)\<close>
  for X :: \<open>'a::complex_normed_vector set\<close>
  apply (rule antisym)
   apply (meson closure_subset_remove_closure closure_is_csubspace closure_mono complex_vector.span_minimal 
      complex_vector.span_superset complex_vector.subspace_span)
  by (simp add: closure_mono closure_subset complex_vector.span_mono)

lemma closure_Sup_closure: \<open>closure (Sup (closure ` X)) = closure (Sup X)\<close>
  by (auto simp: hull_def closure_hull)

lemma cspan_closure_cspan: \<open>cspan (closure (cspan X)) = closure (cspan X)\<close>
  for X :: \<open>'a::complex_normed_vector set\<close>
  by (metis (full_types) closure_cspan_closure closure_subset complex_vector.span_span complex_vector.span_superset subset_antisym)

lemma cblinfun_image_SUP: \<open>A *\<^sub>S (SUP x\<in>X. I x) = (SUP x\<in>X. A *\<^sub>S I x)\<close>
proof (rule antisym)
  show \<open>A *\<^sub>S (SUP x\<in>X. I x) \<le> (SUP x\<in>X. A *\<^sub>S I x)\<close>
  proof (transfer, rule closure_subset_remove_closure)
    fix A :: \<open>'b \<Rightarrow> 'a\<close> and I :: \<open>'c \<Rightarrow> 'b set\<close> and X
    assume [simp]: \<open>bounded_clinear A\<close>
    assume \<open>pred_fun top closed_csubspace I\<close>
    then have [simp]: \<open>closed_csubspace (I x)\<close> for x
      by simp
    have \<open>A ` closure (cspan (\<Union>x\<in>X. I x)) \<subseteq> closure (A ` cspan (\<Union>x\<in>X. I x))\<close>
      apply (rule closure_bounded_linear_image_subset)
      by (simp add: bounded_clinear.bounded_linear)
    also have \<open>\<dots> = closure (cspan (A ` (\<Union>x\<in>X. I x)))\<close>
      by (simp add: bounded_clinear.clinear complex_vector.linear_span_image)
    also have \<open>\<dots> = closure (cspan (\<Union>x\<in>X. A ` I x))\<close>
      by (metis image_UN)
    also have \<open>\<dots> = closure (cspan (closure (\<Union>x\<in>X. A ` I x)))\<close>
      using closure_cspan_closure by blast
    also have \<open>\<dots> = closure (cspan (closure (\<Union>x\<in>X. closure (A ` I x))))\<close>
      apply (subst closure_Sup_closure[symmetric])
      by (simp add: image_image)
    also have \<open>\<dots> = closure (cspan (\<Union>x\<in>X. closure (A ` I x)))\<close>
      using closure_cspan_closure by blast
    finally show \<open>A ` closure (cspan (\<Union> (I ` X))) \<subseteq> closure (cspan (\<Union>x\<in>X. closure (A ` I x)))\<close>
      by -
  qed

  show \<open>(SUP x\<in>X. A *\<^sub>S I x) \<le> A *\<^sub>S (SUP x\<in>X. I x)\<close>
    by (simp add: SUP_least SUP_upper cblinfun_image_mono)
qed

lemma cspan_Sup_cspan: \<open>cspan (Sup (cspan ` X)) = cspan (Sup X)\<close>
  by (auto simp: hull_def complex_vector.span_def)

lemma ccspan_Sup: \<open>ccspan (\<Union>X) = Sup (ccspan ` X)\<close>
proof (transfer fixing: X)
  have \<open>closure (cspan (\<Union>X)) = closure (cspan (\<Union> (cspan ` X)))\<close>
    by (simp add: cspan_Sup_cspan)
  also have \<open>\<dots> = closure (cspan (closure (\<Union> (cspan ` X))))\<close>
    using closure_cspan_closure by blast
  also have \<open>\<dots> = closure (cspan (closure (\<Union> (closure ` cspan ` X))))\<close>
    by (metis closure_Sup_closure)
  also have \<open>\<dots> = closure (cspan (\<Union> (closure ` cspan ` X)))\<close>
    by (meson closure_cspan_closure)
  also have \<open>\<dots> = closure (cspan (\<Union>G\<in>X. closure (cspan G)))\<close>
    by (metis image_image)
  finally show \<open>closure (cspan (\<Union> X)) = closure (cspan (\<Union>G\<in>X. closure (cspan G)))\<close>
    by -
qed

lemma ccspan_space_as_set[simp]: \<open>ccspan (space_as_set S) = S\<close>
  apply transfer
  by (metis closed_csubspace_def closure_closed complex_vector.span_eq_iff)

lemma cblinfun_image_Sup: \<open>A *\<^sub>S Sup II = (SUP I\<in>II. A *\<^sub>S I)\<close>
  using cblinfun_image_SUP[where X=II and I=id and A=A]
  by simp

lemma space_as_set_mono: \<open>I \<le> J \<Longrightarrow> space_as_set I \<le> space_as_set J\<close>
  by (simp add: less_eq_ccsubspace.rep_eq)

lemma square_into_sum: 
  fixes X Y and f :: \<open>_ \<Rightarrow> real\<close>
  assumes \<open>\<And>x. f x \<ge> 0\<close>
  shows \<open>(\<Sum>x\<in>X. f x)\<^sup>2 \<le> card X * (\<Sum>x\<in>X. (f x)\<^sup>2)\<close>
proof -
  have \<open>(\<Sum>x\<in>X. f x)\<^sup>2 = (\<Sum>x\<in>X. f x * 1)\<^sup>2\<close>
    by simp
  also have \<open>\<dots> \<le> (\<Sum>x\<in>X. (f x)\<^sup>2) * (\<Sum>x\<in>X. 1\<^sup>2)\<close>
    by (rule Cauchy_Schwarz_ineq_sum)
  also have \<open>\<dots> = (\<Sum>x\<in>X. (f x)\<^sup>2) * (card X)\<close>
    by simp
  also have \<open>\<dots> = card X * (\<Sum>x\<in>X. (f x)\<^sup>2)\<close>
    by auto
  finally show ?thesis
    by -
qed

lemma bound_coeff_sum2: 
  fixes X Y and f :: \<open>'a \<Rightarrow> complex\<close>
  assumes [simp]: \<open>finite Y\<close>
  assumes XY: \<open>X \<subseteq> Y\<close>
  assumes sum1: \<open>(\<Sum>x\<in>Y. (cmod (f x))\<^sup>2) \<le> 1\<close>
  assumes k: \<open>\<And>x. x \<in> X \<Longrightarrow> card {y. g x = g y \<and> y \<in> X} \<le> k\<close>
  shows \<open>norm (\<Sum>x\<in>X. f x *\<^sub>C ket (g x)) \<le> sqrt k\<close>
proof -
  define eq where \<open>eq = {(x,y). g x = g y \<and> x \<in> X \<and> y \<in> X}\<close>
  have [simp]: \<open>equiv X eq\<close>
    by (auto simp: eq_def equiv_def refl_on_def sym_def trans_def)
  have [simp]: \<open>finite X\<close>
    using \<open>finite Y\<close> XY infinite_super by blast
  then have [simp]: \<open>finite (X // eq)\<close>
    by (simp add: equiv_type finite_quotient)
  have [simp]: \<open>x \<in> X // eq \<Longrightarrow> finite x\<close> for x
    by (meson \<open>equiv X eq\<close> \<open>finite X\<close> equiv_def finite_equiv_class refl_on_def)
  have card_c: \<open>c \<in> X//eq \<Longrightarrow> card c \<le> k\<close> for c
    using k
    by (auto simp: Image_def quotient_def eq_def)

  define g' where \<open>g' c = g (SOME x. x\<in>c)\<close> for c :: \<open>'a set\<close>
  have g_g': \<open>c \<in> X//eq \<Longrightarrow> x \<in> c \<Longrightarrow> g x = g' c\<close> for x c
    apply (simp add: g'_def quotient_def eq_def)
    by (metis (mono_tags, lifting) mem_Collect_eq verit_sko_ex)
  have g'_inj: \<open>c \<in> X//eq \<Longrightarrow> d \<in> X//eq \<Longrightarrow> g' c = g' d \<Longrightarrow> c = d\<close> (is \<open>PROP ?goal\<close>) for c d
  proof -
    have aux1: \<open>\<And>x xa xb.
       g (SOME x. g xb = g x \<and> x \<in> X) = g (SOME x. g xa = g x \<and> x \<in> X) \<Longrightarrow>
       xa \<in> X \<Longrightarrow> xb \<in> X \<Longrightarrow> g xa = g xb\<close>
      by (metis (mono_tags, lifting) verit_sko_ex)
    have aux2: \<open>\<And>x xa xb.
       g (SOME xa. g x = g xa \<and> xa \<in> X) = g (SOME x. g xb = g x \<and> x \<in> X) \<Longrightarrow>
       x \<in> X \<Longrightarrow> xb \<in> X \<Longrightarrow> g x = g xb\<close>
      by (metis (mono_tags, lifting) someI2)
    show \<open>PROP ?goal\<close>
      by (auto intro: aux1 aux2 simp add: g'_def quotient_def eq_def image_iff)
  qed

  have SIGMA: \<open>(SIGMA x:X // eq. x) = (\<lambda>x. (eq``{x},x)) ` X\<close>
    by (auto simp: quotient_def eq_def)

  have \<open>(norm (\<Sum>x\<in>X. f x *\<^sub>C ket (g x)))\<^sup>2 = (norm (\<Sum>c\<in>X//eq. \<Sum>x\<in>c. f x *\<^sub>C ket (g x)))\<^sup>2\<close>
    apply (subst sum.Sigma)
      apply auto[2]
    apply (subst SIGMA)
    apply (subst sum.reindex)
    using inj_on_def by auto
  also have \<open>\<dots> = (norm (\<Sum>c\<in>X//eq. \<Sum>x\<in>c. f x *\<^sub>C ket (g' c)))\<^sup>2\<close>
    by (simp add: g_g')
  also have \<open>\<dots> = (norm (\<Sum>c\<in>X//eq. (\<Sum>x\<in>c. f x) *\<^sub>C ket (g' c)))\<^sup>2\<close>
    by (simp add: scaleC_sum_left)
  also have \<open>\<dots> = (\<Sum>c\<in>X//eq. (norm ((\<Sum>x\<in>c. f x) *\<^sub>C ket (g' c)))\<^sup>2)\<close>
    apply (rule pythagorean_theorem_sum)
    by (auto dest: g'_inj)
  also have \<open>\<dots> = (\<Sum>c\<in>X//eq. (cmod (\<Sum>x\<in>c. f x))\<^sup>2)\<close>
    by force
  also have \<open>\<dots> \<le> (\<Sum>c\<in>X//eq. (\<Sum>x\<in>c. cmod (f x))\<^sup>2)\<close>
    by (simp add: power_mono sum_mono sum_norm_le)
  also have \<open>\<dots> \<le> (\<Sum>c\<in>X//eq. card c * (\<Sum>x\<in>c. (cmod (f x))\<^sup>2))\<close>
    apply (rule sum_mono)
    apply (rule square_into_sum)
    by simp
  also have \<open>\<dots> \<le> (\<Sum>c\<in>X//eq. k * (\<Sum>x\<in>c. (cmod (f x))\<^sup>2))\<close>
    apply (rule sum_mono)
    apply (rule mult_right_mono)
    by (simp_all add: card_c sum_nonneg)
  also have \<open>\<dots> = k * (\<Sum>c\<in>X//eq. (\<Sum>x\<in>c. (cmod (f x))\<^sup>2))\<close>
    by (rule sum_distrib_left[symmetric])
  also have \<open>\<dots> \<le> k * (\<Sum>x\<in>X. (cmod (f x))\<^sup>2)\<close>
    apply (subst sum.Sigma)
      apply auto[2]
    apply (subst SIGMA)
    apply (subst sum.reindex)
    using inj_on_def by auto
  also have \<open>\<dots> \<le> k * (\<Sum>x\<in>Y. (cmod (f x))\<^sup>2)\<close>
    apply (rule mult_left_mono)
     apply (rule sum_mono2)
    using XY by auto
  also have \<open>\<dots> \<le> k\<close>
    using sum1
    by (metis mult.right_neutral mult_left_mono of_nat_0_le_iff)
  finally show ?thesis
    using real_le_rsqrt by blast
qed


lemma norm_ortho_sum_bound:
  fixes X
  assumes bound: \<open>\<And>x. x\<in>X \<Longrightarrow> norm (\<psi> x) \<le> b'\<close>
  assumes b'geq0: \<open>b' \<ge> 0\<close>
  assumes ortho: \<open>\<And>x y. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> x\<noteq>y \<Longrightarrow> is_orthogonal (\<psi> x) (\<psi> y)\<close>
  assumes b'b: \<open>sqrt (card X) * b' \<le> b\<close>
  shows \<open>norm (\<Sum>x\<in>X. \<psi> x) \<le> b\<close>
proof (cases \<open>finite X\<close>)
  case True
  have \<open>b \<ge> 0\<close>
    by (metis b'b b'geq0 mult_nonneg_nonneg of_nat_0_le_iff order_trans real_sqrt_ge_0_iff)
  have \<open>(norm (\<Sum>x\<in>X. \<psi> x))\<^sup>2 = (\<Sum>a\<in>X. (norm (\<psi> a))\<^sup>2)\<close>
    apply (subst pythagorean_theorem_sum)
    using assms True by auto
  also have \<open>\<dots> \<le> (\<Sum>a\<in>X. b'\<^sup>2)\<close>
    by (meson bound norm_ge_zero power_mono sum_mono)
  also have \<open>\<dots> \<le> (sqrt (card X) * b')\<^sup>2\<close>
    by (simp add: power_mult_distrib)
  also have \<open>\<dots> \<le> b\<^sup>2\<close>
    by (meson b'b b'geq0 mult_nonneg_nonneg of_nat_0_le_iff power_mono real_sqrt_ge_0_iff)
  finally show ?thesis
    apply (rule_tac power2_le_imp_le)
    apply force
    using \<open>0 \<le> b\<close> by force
next
  case False
  then show ?thesis
    using assms by auto
qed

lemma compatible_project1: \<open>compatible F G\<close>
  if \<open>compatible F (G;H)\<close> and [register]: \<open>compatible G H\<close> for F G H
proof (rule compatibleI)
  show \<open>register F\<close>
    using compatible_register1 that(1) by blast
  show \<open>register G\<close>
    using compatible_register1 that(2) by blast
  fix a b
  from \<open>compatible F (G;H)\<close>
  have \<open>F a o\<^sub>C\<^sub>L (G;H) (b \<otimes>\<^sub>o id_cblinfun) = (G;H) (b \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L F a\<close>
    using swap_registers by blast
  then show \<open>F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a\<close>
    by (simp add: register_pair_apply)
qed

lemma compatible_project2: \<open>compatible F H\<close>
  if \<open>compatible F (G;H)\<close> and [register]: \<open>compatible G H\<close> for F G H
proof (rule compatibleI)
  show \<open>register F\<close>
    using compatible_register1 that(1) by blast
  show \<open>register H\<close>
    using compatible_register2 that(2) by blast
  fix a b
  from \<open>compatible F (G;H)\<close>
  have \<open>F a o\<^sub>C\<^sub>L (G;H) (id_cblinfun \<otimes>\<^sub>o b) = (G;H) (id_cblinfun \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L F a\<close>
    using swap_registers by blast
  then show \<open>F a o\<^sub>C\<^sub>L H b = H b o\<^sub>C\<^sub>L F a\<close>
    by (simp add: register_pair_apply)
qed

(* typedef 'a with_default = \<open>UNIV :: 'a set\<close>
  by simp
instantiation with_default :: (type) default begin
lift_definition default :: \<open>'a with_default\<close> is undefined.
instance..
end *)


(* TODO remove (keep proj_ket_x_y_ofbool) *)
lemma proj_ket_x_y: \<open>proj (ket x) *\<^sub>V (ket y) = 0\<close> if \<open>x \<noteq> y\<close>
  by (metis kernel_Proj kernel_memberD mem_ortho_ccspanI orthogonal_ket singletonD that)

lemma proj_ket_x_y_ofbool: \<open>proj (ket x) *\<^sub>V (ket y) = of_bool (x=y) *\<^sub>C ket y\<close>
  by (simp add: Proj_fixes_image ccspan_superset' proj_ket_x_y)

lemma proj_x_x[simp]: \<open>proj x *\<^sub>V x = x\<close>
  by (meson Proj_fixes_image ccspan_superset insert_subset)

lemma in_ortho_ccspan: \<open>y \<in> space_as_set (- ccspan X)\<close> if \<open>\<forall>x\<in>X. is_orthogonal y x\<close>
  using that apply transfer
  by (metis orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_of_cspan)
  

lemma swap_sandwich_swap_ell2: "swap = sandwich swap_ell2"
  apply (rule tensor_extensionality)
    apply (auto simp: sandwich_apply unitary_sandwich_register)[2]
  apply (rule tensor_ell2_extensionality)
  by simp

lemma is_Proj_sandwich: \<open>is_Proj (sandwich U P)\<close> if \<open>isometry U\<close> and \<open>is_Proj P\<close>
  for P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and U :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using that
  by (simp add: is_Proj_algebraic sandwich_apply
      lift_cblinfun_comp[OF isometryD] lift_cblinfun_comp[OF is_Proj_idempotent]
      flip: cblinfun_compose_assoc)

lemma is_Proj_swap[simp]: \<open>is_Proj (swap P)\<close> if \<open>is_Proj P\<close>
  using that
  by (simp add: swap_sandwich_swap_ell2 is_Proj_sandwich)


lemma iso_register_complement_pair: \<open>iso_register (complement X; X)\<close> if \<open>register X\<close>
  using complement_is_complement complements_def complements_sym that by blast

lemma swap_Snd: \<open>swap (Snd x) = Fst x\<close>
  by (simp add: Fst_def Snd_def)


lemma sandwich_butterfly: \<open>sandwich a (butterfly g h) = butterfly (a g) (a h)\<close>
  by (simp add: butterfly_comp_cblinfun cblinfun_comp_butterfly sandwich_apply)

lemma register0:
  assumes \<open>register Q\<close>
  shows \<open>Q a = 0 \<longleftrightarrow> a = 0\<close>
  by (metis assms norm_eq_zero register_norm)

lemma le_back_subst:
  assumes \<open>a \<le> c\<close>
  assumes \<open>a = b\<close>
  shows \<open>b \<le> c\<close>
  using assms by simp

lemma le_back_subst_le:
  fixes a b c :: \<open>_ :: order\<close>
  assumes \<open>a \<le> c\<close>
  assumes \<open>b \<le> a\<close>
  shows \<open>b \<le> c\<close>
  using assms by order

lemma arg_cong4: \<open>f a b c d = f a' b' c' d'\<close> if \<open>a = a'\<close> and \<open>b = b'\<close> and \<open>c = c'\<close> and \<open>d = d'\<close>
  using that by simp


(* 
lemma convex_on_cong:
  assumes \<open>S = T\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  shows \<open>convex_on S f \<longleftrightarrow> convex_on T g\<close>
proof -
  have \<open>f (u *\<^sub>R x + v *\<^sub>R y) = g (u *\<^sub>R x + v *\<^sub>R y)\<close>
    if \<open>convex T\<close> and \<open>x \<in> T\<close> and \<open>y \<in> T\<close> and \<open>u \<ge> 0\<close> and \<open>v \<ge> 0\<close> and \<open>u + v = 1\<close>
    for x y u v
    by (simp add: assms(1,2) convexD that(1,2,3,4,5,6))
  then show ?thesis
    by (auto simp: convex_on_def assms)
qed

lemma concave_on_cong:
  assumes \<open>S = T\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x = g x\<close>
  shows \<open>concave_on S f \<longleftrightarrow> concave_on T g\<close>
  unfolding concave_on_def
  apply (rule convex_on_cong)
  using assms by simp_all
 *)



subsection \<open>Controlled operations\<close>

(* TODO document *)

definition controlled_op :: \<open>('a \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2)) \<Rightarrow> (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'c) ell2)\<close> where
  \<open>controlled_op A = infsum_in cstrong_operator_topology (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o A x) UNIV\<close>

(* definition controlled_op :: \<open>('a \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2)) \<Rightarrow> (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'c) ell2)\<close> where
  \<open>controlled_op A = (\<Sum>x\<in>UNIV. selfbutter (ket x) \<otimes>\<^sub>o A x)\<close> *)

(* TODO move *)
lemma trunc_ell2_prod_tensor: \<open>trunc_ell2 (A\<times>B) (g \<otimes>\<^sub>s h) = trunc_ell2 A g \<otimes>\<^sub>s trunc_ell2 B h\<close>
  apply transfer'
  by auto

(* TODO move *)
lemma trunc_ell2_ket: \<open>trunc_ell2 S (ket x) = of_bool (x\<in>S) *\<^sub>C ket x\<close>
  apply transfer'
  by auto

(* TODO move *)
lemma summable_on_in_0[iff]: \<open>summable_on_in T (\<lambda>x. 0) A\<close> if \<open>0 \<in> topspace T\<close>
  using has_sum_in_0[of T A \<open>\<lambda>_. 0\<close>] summable_on_in_def that by blast

lemma sum_of_bool_scaleC: \<open>(\<Sum>x\<in>S. of_bool (x=a) *\<^sub>C f x) = (if a\<in>S \<and> finite S then f a else 0)\<close>
  for f :: \<open>_ \<Rightarrow> _::complex_vector\<close>
  apply (cases \<open>finite S\<close>)
   apply (subst sum_single[where i=a])
  by auto

lemma
  fixes A :: \<open>'x \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)\<close>
  (* assumes \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close> *)
  assumes \<open>\<And>x. norm (A x) \<le> B\<close>
  shows controlled_op_has_sum_aux: \<open>has_sum_in cstrong_operator_topology (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o A x) UNIV (controlled_op A)\<close>
    and controlled_op_norm_leq: \<open>norm (controlled_op A) \<le> B\<close>
proof -
  have [iff]: \<open>B \<ge> 0\<close>
    using assms[of undefined] norm_ge_zero[of \<open>A undefined\<close>]
    by argo

  define A' where \<open>A' x = selfbutter (ket x) \<otimes>\<^sub>o A x\<close> for x
  have A'summ: \<open>(\<lambda>x. A' x *\<^sub>V h) summable_on UNIV\<close> for h
  proof -
    wlog [iff]: \<open>B \<noteq> 0\<close>
      using negation assms by (simp add: A'_def)
    have \<open>\<exists>P. eventually P (finite_subsets_at_top UNIV) \<and> (\<forall>F G. P F \<and> P G \<longrightarrow> dist (\<Sum>x\<in>F. A' x *\<^sub>V h) (\<Sum>x\<in>G. A' x *\<^sub>V h) < e)\<close> if \<open>e > 0\<close> for e
    proof -
      have \<open>((\<lambda>S. trunc_ell2 S h) \<longlongrightarrow> h) (finite_subsets_at_top UNIV)\<close>
        by (rule trunc_ell2_lim_at_UNIV)
      from tendsto_iff[THEN iffD1, OF this, rule_format, of \<open>e/B\<close>]
      have \<open>\<forall>\<^sub>F S in finite_subsets_at_top UNIV. dist (trunc_ell2 S h) h < e/B\<close>
        using \<open>B \<noteq> 0\<close> \<open>B \<ge> 0\<close> that by force
      then obtain S where [iff]: \<open>finite S\<close> and S_prop: \<open>norm (trunc_ell2 S h - h) < e/B\<close> for G
        apply atomize_elim
        by (force simp add: eventually_finite_subsets_at_top dist_norm)
      define P :: \<open>'x set \<Rightarrow> bool\<close> where \<open>P F \<longleftrightarrow> finite F \<and>  F \<supseteq> fst ` S\<close> for F
      have evP: \<open>eventually P (finite_subsets_at_top UNIV)\<close>
        by (auto intro!: exI[of _ \<open>fst`S\<close>] \<open>finite S\<close> simp add: eventually_finite_subsets_at_top P_def[abs_def])
      have \<open>dist (\<Sum>x\<in>F. A' x *\<^sub>V h) (\<Sum>x\<in>G. A' x *\<^sub>V h) < e\<close> if \<open>P F\<close> and \<open>P G\<close> for F G
      proof -
        have [iff]: \<open>finite F\<close> \<open>finite G\<close>
          using that by (simp_all add: P_def)
        define FG where \<open>FG = sym_diff F G\<close>
        then have [iff]: \<open>finite FG\<close>
          by simp
        define h' where \<open>h' x = (tensor_ell2_left (ket x)*) h\<close> for x
        have A'h: \<open>A' x *\<^sub>V h = ket x \<otimes>\<^sub>s (A x *\<^sub>V h' x)\<close> for x
          unfolding h'_def
          apply (rule fun_cong[of _ _ h])
          apply (rule bounded_clinear_equal_ket)
            apply (auto intro!: bounded_linear_intros)[2]
          by (auto simp add: A'_def tensor_op_ket tensor_op_ell2 cinner_ket simp flip: tensor_ell2_ket)
        have \<open>(dist (\<Sum>x\<in>F. A' x *\<^sub>V h) (\<Sum>x\<in>G. A' x *\<^sub>V h))\<^sup>2 = (norm ((\<Sum>x\<in>F. A' x *\<^sub>V h) - (\<Sum>x\<in>G. A' x *\<^sub>V h)))\<^sup>2\<close>
          by (simp add: dist_norm)
        also have \<open>\<dots> = (norm ((\<Sum>x\<in>FG. (if x\<in>F then 1 else -1) *\<^sub>C (A' x *\<^sub>V h))))\<^sup>2\<close>
          apply (rule arg_cong[where f=\<open>\<lambda>x. (norm x)\<^sup>2\<close>])
          apply (rewrite at F at \<open>\<Sum>x\<in>\<hole>. _\<close> to \<open>(F-G)\<union>(F\<inter>G)\<close> DEADID.rel_mono_strong, blast)
          apply (rewrite at G at \<open>\<Sum>x\<in>\<hole>. _\<close> to \<open>(G-F)\<union>(F\<inter>G)\<close> DEADID.rel_mono_strong, blast)
          apply (rewrite at FG at \<open>\<Sum>x\<in>\<hole>. _\<close> FG_def)
          apply (subst sum_Un, simp, simp)
          apply (subst sum_Un, simp, simp)
          apply (subst sum_Un, simp, simp)
          apply (rewrite at \<open>(\<Sum>x\<in>F - G. (if x \<in> F then 1 else - 1) *\<^sub>C (A' x *\<^sub>V h))\<close> to \<open>(\<Sum>x\<in>F-G. A' x *\<^sub>V h)\<close> sum.cong, simp, simp)
          apply (rewrite at \<open>(\<Sum>x\<in>G - F. (if x \<in> F then 1 else - 1) *\<^sub>C (A' x *\<^sub>V h))\<close> to \<open>(\<Sum>x\<in>G-F. - (A' x *\<^sub>V h))\<close> sum.cong, simp, simp)
          apply (rewrite at \<open>(F - G) \<inter> (G - F)\<close> to \<open>{}\<close> DEADID.rel_mono_strong, blast)
          apply (rewrite at \<open>(F - G) \<inter> (F \<inter> G)\<close> to \<open>{}\<close> DEADID.rel_mono_strong, blast)
          apply (rewrite at \<open>(G - F) \<inter> (F \<inter> G)\<close> to \<open>{}\<close> DEADID.rel_mono_strong, blast)
          by (simp add: sum_negf)
        also have \<open>\<dots> = (\<Sum>x\<in>FG. (norm ((if x \<in> F then 1 else - 1) *\<^sub>C (A' x *\<^sub>V h)))\<^sup>2)\<close>
          apply (rule pythagorean_theorem_sum)
           apply (simp add: A'_def butterfly_adjoint tensor_op_adjoint comp_tensor_op cinner_ket
              flip: cinner_adj_right cblinfun_apply_cblinfun_compose)
          by (simp add: FG_def)
        also have \<open>\<dots> = (\<Sum>x\<in>FG. (norm (A' x *\<^sub>V h))\<^sup>2)\<close>
          apply (rule sum.cong, simp)
          by (simp add: norm_scaleC)
        also have \<open>\<dots> = (\<Sum>x\<in>FG. (norm (A x *\<^sub>V h' x))\<^sup>2)\<close>
          by (simp add: A'h norm_tensor_ell2)
        also have \<open>\<dots> \<le> (\<Sum>x\<in>FG. (B * norm (h' x))\<^sup>2)\<close>
          using assms
          by (auto intro!: sum_mono power_mono norm_cblinfun[THEN order_trans] mult_right_mono)
        also have \<open>\<dots> = B\<^sup>2 * (\<Sum>x\<in>FG. (norm (h' x))\<^sup>2)\<close>
          by (simp add: sum_distrib_left power_mult_distrib)
        also have \<open>\<dots> = B\<^sup>2 * (\<Sum>x\<in>FG. (norm (ket x \<otimes>\<^sub>s h' x))\<^sup>2)\<close>
          by (simp add: norm_tensor_ell2 norm_ket)
        also have \<open>\<dots> = B\<^sup>2 * (norm (\<Sum>x\<in>FG. ket x \<otimes>\<^sub>s h' x))\<^sup>2\<close>
          apply (subst pythagorean_theorem_sum)
          by (simp_all add: FG_def)
        also have \<open>\<dots> = B\<^sup>2 * (norm (trunc_ell2 (FG\<times>UNIV) h))\<^sup>2\<close>
          apply (rule arg_cong[where f=\<open>\<lambda>x. _ * (norm x)\<^sup>2\<close>])
          apply (rule cinner_ket_eqI)
          apply (rename_tac ab)
        proof -
          fix ab :: \<open>'x \<times> 'a\<close>
          obtain a b where ab: \<open>ab = (a,b)\<close>
            by (auto simp: prod_eq_iff)
          have \<open>ket ab \<bullet>\<^sub>C (\<Sum>x\<in>FG. ket x \<otimes>\<^sub>s h' x) = (\<Sum>x\<in>FG. ket ab \<bullet>\<^sub>C (ket x \<otimes>\<^sub>s h' x))\<close>
            using cinner_sum_right by blast
          also have \<open>\<dots> = of_bool (a\<in>FG) * (ket b \<bullet>\<^sub>C h' a)\<close>
            apply (subst sum_single[where i=a])
            by (auto simp add: ab simp flip: tensor_ell2_ket)
          also have \<open>\<dots> = of_bool (a\<in>FG) * Rep_ell2 h (a, b)\<close>
            by (simp add: h'_def cinner_adj_right tensor_ell2_ket cinner_ket_left)
          also have \<open>\<dots> = ket ab \<bullet>\<^sub>C trunc_ell2 (FG \<times> UNIV) h\<close>
            by (simp add: ab cinner_ket_left trunc_ell2.rep_eq)
          finally show \<open>ket ab \<bullet>\<^sub>C (\<Sum>x\<in>FG. ket x \<otimes>\<^sub>s h' x) = ket ab \<bullet>\<^sub>C trunc_ell2 (FG \<times> UNIV) h\<close>
            by -
        qed
        also have \<open>\<dots> \<le> B\<^sup>2 * (norm (trunc_ell2 (-S) h))\<^sup>2\<close>
          apply (rule mult_left_mono[rotated], simp)
          apply (rule power_mono[rotated], simp)
          apply (rule trunc_ell2_norm_mono)
          using \<open>P F\<close> \<open>P G\<close> by (force simp: P_def FG_def)
        also have \<open>\<dots> = B\<^sup>2 * (norm (trunc_ell2 S h - h))\<^sup>2\<close>
          by (smt (verit, best) norm_id_minus_trunc_ell2 norm_minus_commute trunc_ell2_uminus)
        also have \<open>\<dots> < B\<^sup>2 * (e/B)\<^sup>2\<close>
          apply (rule mult_strict_left_mono[rotated], simp)
          apply (rule power_strict_mono[rotated], simp, simp)
          by (rule S_prop)
        also have \<open>\<dots> = e\<^sup>2\<close>
          by (simp add: power_divide)
        finally show ?thesis
          by (smt (verit, del_insts) \<open>0 < e\<close> power_mono)
      qed
      with evP show ?thesis
        by blast
    qed
    then show ?thesis
      unfolding summable_on_def has_sum_def filterlim_def
      apply (rule_tac convergent_filter_iff[THEN iffD1])
      apply (subst convergent_filter_iff_cauchy)
      by (rule cauchy_filter_metric_filtermapI)
  qed
  define C where \<open>C h = (\<Sum>\<^sub>\<infinity>x. A' x *\<^sub>V h)\<close> for h
  then have C_hassum: \<open>((\<lambda>x. A' x *\<^sub>V h) has_sum (C h)) UNIV\<close> for h
    using A'summ by auto

  have norm_C: \<open>norm (C g) \<le> B * norm g\<close> for g
  proof -
    define g' where \<open>g' x = (tensor_ell2_left (ket x)*) g\<close> for x
    have A'g: \<open>A' x *\<^sub>V g = ket x \<otimes>\<^sub>s (A x *\<^sub>V g' x)\<close> for x
      unfolding g'_def
      apply (rule fun_cong[of _ _ g])
      apply (rule bounded_clinear_equal_ket)
        apply (simp add: cblinfun.bounded_clinear_right) 
       apply (metis bounded_clinear_compose bounded_clinear_tensor_ell21 cblinfun.bounded_clinear_right) 
      by (auto simp add: A'_def tensor_op_ket tensor_op_ell2 cinner_ket simp flip: tensor_ell2_ket)
    have norm_trunc: \<open>norm (trunc_ell2 F (C g)) \<le> B * norm g\<close> if \<open>finite F\<close> for F
    proof -
      define S where \<open>S = fst ` F\<close>
      then have [iff]: \<open>finite S\<close>
        using that by blast
      have \<open>(norm (trunc_ell2 F (C g)))\<^sup>2 \<le> (norm (trunc_ell2 (S \<times> UNIV) (C g)))\<^sup>2\<close>
        apply (rule power_mono[rotated], simp)
        apply (rule trunc_ell2_norm_mono)
        by (force simp: S_def)
      also have \<open>\<dots> = (norm (\<Sum>x\<in>S. ket x \<otimes>\<^sub>s (A x *\<^sub>V g' x)))\<^sup>2\<close>
      proof (rule arg_cong[where f=\<open>\<lambda>x. (norm x)\<^sup>2\<close>])
        have \<open>trunc_ell2 (S\<times>UNIV) (C g) = (\<Sum>\<^sub>\<infinity>x. trunc_ell2 (S\<times>UNIV) (A' x *\<^sub>V g))\<close>
          apply (simp add: C_def)
          apply (rule infsum_bounded_linear[symmetric])
           apply (intro bounded_clinear.bounded_linear bounded_clinear_trunc_ell2)
          using A'summ by -
        also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>S. ket x \<otimes>\<^sub>s (A x *\<^sub>V g' x))\<close>
          apply (rule infsum_cong_neutral)
          by (auto simp add: A'g trunc_ell2_prod_tensor trunc_ell2_ket)
        also have \<open>\<dots> = (\<Sum>x\<in>S. ket x \<otimes>\<^sub>s (A x *\<^sub>V g' x))\<close>
          by (auto intro!: infsum_finite simp: that)
        finally show \<open>trunc_ell2 (S \<times> UNIV) (C g) = (\<Sum>x\<in>S. ket x \<otimes>\<^sub>s A x *\<^sub>V g' x)\<close>
          by -
      qed
      also have \<open>\<dots> = (\<Sum>x\<in>S. (norm (ket x \<otimes>\<^sub>s A x *\<^sub>V g' x))\<^sup>2)\<close>
        apply (subst pythagorean_theorem_sum)
        by auto
      also have \<open>\<dots> = (\<Sum>x\<in>S. (norm (A x *\<^sub>V g' x))\<^sup>2)\<close>
        by (simp add: norm_tensor_ell2)
      also have \<open>\<dots> \<le> (\<Sum>x\<in>S. (B * norm (g' x))\<^sup>2)\<close>
        using assms
        by (auto intro!: sum_mono power_mono norm_cblinfun[THEN order_trans] mult_right_mono)
      also have \<open>\<dots> = (\<Sum>x\<in>S. (norm (g' x))\<^sup>2) * B\<^sup>2\<close>
        by (simp add: power_mult_distrib mult.commute sum_distrib_left)
      also have \<open>\<dots> = (\<Sum>x\<in>S. (norm (ket x \<otimes>\<^sub>s g' x))\<^sup>2) * B\<^sup>2\<close>
        by (simp add: norm_tensor_ell2)
      also have \<open>\<dots> = (norm (\<Sum>x\<in>S. ket x \<otimes>\<^sub>s g' x))\<^sup>2 * B\<^sup>2\<close>
        apply (subst pythagorean_theorem_sum[symmetric])
        by (auto simp add: g'_def)
      also have \<open>\<dots> \<le> (norm g)\<^sup>2 * B\<^sup>2\<close>
      proof -
        have \<open>(\<Sum>x\<in>S. ket x \<otimes>\<^sub>s g' x) = trunc_ell2 (S\<times>UNIV) g\<close>
          unfolding g'_def
          apply (rule fun_cong[where x=g])
          apply (rule bounded_clinear_equal_ket)
            apply (auto intro!: bounded_linear_intros)[2]
          by (auto intro!: simp: cinner_ket trunc_ell2_prod_tensor trunc_ell2_ket
              tensor_ell2_scaleC2 sum_of_bool_scaleC
              simp flip: tensor_ell2_ket
              split!: if_split_asm)
        then show ?thesis
          by (auto intro!: trunc_ell2_reduces_norm mult_right_mono power_mono sum_nonneg norm_ge_zero zero_le_power2)
      qed
      also have \<open>\<dots> \<le> (norm g * B)\<^sup>2\<close>
        by (simp add: power_mult_distrib)
      finally show ?thesis
        by (metis Extra_Ordered_Fields.sign_simps(5) \<open>0 \<le> B\<close> norm_ge_zero power2_le_imp_le zero_compare_simps(4))
    qed
    have \<open>((\<lambda>F. trunc_ell2 F (C g)) \<longlongrightarrow> C g) (finite_subsets_at_top UNIV)\<close>
      by (rule trunc_ell2_lim_at_UNIV)
    then have \<open>((\<lambda>F. norm (trunc_ell2 F (C g))) \<longlongrightarrow> norm (C g)) (finite_subsets_at_top UNIV)\<close>
      by (rule tendsto_norm)
    then show \<open>norm (C g) \<le> B * norm g\<close>
      apply (rule tendsto_upperbound)
      using norm_trunc by (auto intro!: eventually_finite_subsets_at_top_weakI simp: )
  qed
  
  have \<open>bounded_clinear C\<close>
  proof (intro bounded_clinearI allI)
    fix g h :: \<open>('x \<times> 'a) ell2\<close> and c :: complex
    from C_hassum[of g] C_hassum[of h]
    have \<open>((\<lambda>x. A' x *\<^sub>V g + A' x *\<^sub>V h) has_sum C g + C h) UNIV\<close>
      by (simp add: has_sum_add)
    with C_hassum[of \<open>g + h\<close>]
    show \<open>C (g + h) = C g + C h\<close>
      by (metis (no_types, lifting) cblinfun.add_right has_sum_cong infsumI)
    from C_hassum[of g]
    have \<open>((\<lambda>x. c *\<^sub>C (A' x *\<^sub>V g)) has_sum c *\<^sub>C C g) UNIV\<close>
      by (metis cblinfun_scaleC_right.rep_eq has_sum_cblinfun_apply)
    with C_hassum[of \<open>c *\<^sub>C g\<close>]
    show \<open>C (c *\<^sub>C g) = c *\<^sub>C C g\<close>
      by (metis (no_types, lifting) cblinfun.scaleC_right has_sum_cong infsumI)
    from norm_C show \<open>norm (C g) \<le> norm g * B\<close>
      by (simp add: sign_simps(5))
  qed
  define D where \<open>D = CBlinfun C\<close>
  with \<open>bounded_clinear C\<close> have DC: \<open>D *\<^sub>V f = C f\<close> for f
    by (simp add: bounded_clinear_CBlinfun_apply)
  have D_hassum: \<open>has_sum_in cstrong_operator_topology A' UNIV D\<close>
    using C_hassum by (simp add: has_sum_in_cstrong_operator_topology DC)
  then show \<open>has_sum_in cstrong_operator_topology A' UNIV (controlled_op A)\<close>
    using controlled_op_def A'_def
    by (metis (no_types, lifting) has_sum_in_infsum_in hausdorff_sot infsum_in_cong summable_on_in_def)
  with D_hassum have DA: \<open>D = controlled_op A\<close>
    apply (rule_tac has_sum_in_unique)
    by auto
  show \<open>norm (controlled_op A) \<le> B\<close>
    apply (rule norm_cblinfun_bound, simp)
    using norm_C by (simp add: DC flip: DA)
qed

lemma controlled_op_has_sum:
  fixes A :: \<open>'x \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)\<close>
  assumes \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close>
  shows \<open>has_sum_in cstrong_operator_topology (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o A x) UNIV (controlled_op A)\<close>
proof -
  from assms obtain B where \<open>norm (A x) \<le> B\<close> for x
    by (auto intro!: simp: bdd_above_def)
  then show ?thesis
    by (rule controlled_op_has_sum_aux)
qed

hide_fact controlled_op_has_sum_aux

lemma controlled_op_summable:
  fixes A :: \<open>'x \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2)\<close>
  assumes \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close>
  shows \<open>summable_on_in cstrong_operator_topology (\<lambda>x. selfbutter (ket x) \<otimes>\<^sub>o A x) UNIV\<close>
  using controlled_op_has_sum[OF assms] summable_on_in_def by blast

(* TODO move *)
lemma infsum_sot_cblinfun_apply:
  assumes \<open>summable_on_in cstrong_operator_topology f UNIV\<close>
  shows \<open>infsum_in cstrong_operator_topology f UNIV *\<^sub>V \<psi> = (\<Sum>\<^sub>\<infinity>x. f x *\<^sub>V \<psi>)\<close>
  by (metis assms has_sum_in_cstrong_operator_topology has_sum_in_infsum_in hausdorff_sot infsumI)


lemma controlled_op_ket[simp]:
  assumes \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close>
  shows \<open>controlled_op A *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>) = ket x \<otimes>\<^sub>s (A x *\<^sub>V \<psi>)\<close>
proof -
  have \<open>controlled_op A *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>) = (\<Sum>\<^sub>\<infinity>y. (selfbutter (ket y) \<otimes>\<^sub>o A y) *\<^sub>V (ket x \<otimes>\<^sub>s \<psi>))\<close>
    by (simp add: controlled_op_def assms infsum_sot_cblinfun_apply controlled_op_summable)
  also have \<open>\<dots> = ket x \<otimes>\<^sub>s (A x *\<^sub>V \<psi>)\<close>
    apply (subst infsum_single[where i=x])
    by (simp_all add: tensor_op_ell2 cinner_ket)
  finally show ?thesis
    by -
qed

lemma controlled_op_ket'[simp]: 
  assumes \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close>
  shows \<open>controlled_op A *\<^sub>V (ket (x, y)) = ket x \<otimes>\<^sub>s (A x *\<^sub>V ket y)\<close>
  by (metis assms controlled_op_ket tensor_ell2_ket)

lemma controlled_op_compose[simp]: 
  assumes [simp]: \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close>
  assumes [simp]: \<open>bdd_above (range (\<lambda>x. norm (B x)))\<close>
  shows \<open>controlled_op A o\<^sub>C\<^sub>L controlled_op B = controlled_op (\<lambda>x. A x o\<^sub>C\<^sub>L B x)\<close>
proof -
  from assms(1) obtain a where \<open>norm (A x) \<le> a\<close> for x
    by (auto simp: bdd_above_def)
  moreover from assms(2) obtain b where \<open>norm (B x) \<le> b\<close> for x
    by (auto simp: bdd_above_def)
  ultimately  have [simp]: \<open>bdd_above (range (\<lambda>x. norm (A x o\<^sub>C\<^sub>L B x)))\<close>
    apply (rule_tac bdd_aboveI[of _ \<open>a*b\<close>])
    by (smt (verit, ccfv_SIG) Multiseries_Expansion_Bounds.mult_monos(1) imageE norm_cblinfun_compose
        norm_ge_zero)
  show ?thesis
    apply (rule equal_ket)
    apply (case_tac x)
    by simp
qed

lemma controlled_op_adj[simp]:
  assumes [simp]: \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close>
  shows \<open>(controlled_op A)* = controlled_op (\<lambda>x. (A x)*)\<close>
  apply (rule cinner_ket_adjointI[symmetric])
  by (auto intro!: simp: controlled_op_ket cinner_adj_left
      simp flip: tensor_ell2_ket)

lemma controlled_op_id[simp]: \<open>controlled_op (\<lambda>_. id_cblinfun) = id_cblinfun\<close>
  apply (rule equal_ket)
  apply (case_tac x)
  by (simp add: tensor_ell2_ket)

lemma controlled_op_unitary[simp]: \<open>unitary (controlled_op U)\<close> if [simp]: \<open>\<And>x. unitary (U x)\<close>
proof -
  have [iff]: \<open>bdd_above (range (\<lambda>x. norm (U x)))\<close>
    by (simp add: norm_isometry)
  show ?thesis
    unfolding unitary_def by auto
qed

lemma controlled_op_is_Proj[simp]: \<open>is_Proj (controlled_op P)\<close> if [simp]: \<open>\<And>x. is_Proj (P x)\<close>
proof -
  have [iff]: \<open>bdd_above (range (\<lambda>x. norm (P x)))\<close>
    using norm_is_Proj[OF that]
    by (auto intro!: bdd_aboveI simp: )
  show ?thesis
    using that unfolding is_Proj_algebraic by auto
qed

lemma controlled_op_comp_butter: 
  assumes \<open>bdd_above (range (\<lambda>x. norm (A x)))\<close>
  shows \<open>controlled_op A o\<^sub>C\<^sub>L Fst (selfbutter (ket x)) = Snd (A x) o\<^sub>C\<^sub>L Fst (selfbutter (ket x))\<close>
  using assms by (auto intro!: equal_ket simp: Fst_def tensor_op_ket cinner_ket)

(* TODO move *)
lemma norm_ell2_finite: \<open>norm \<psi> = sqrt (\<Sum>i\<in>UNIV. (cmod (Rep_ell2 \<psi> i))\<^sup>2)\<close> for \<psi> :: \<open>_::finite ell2\<close>
  apply transfer
  by (simp add: ell2_norm_finite)

lemma controlled_op_ket_swap[simp]: 
  assumes \<open>bdd_above (range (\<lambda>x. norm (U x)))\<close>
  shows \<open>swap (controlled_op U) *\<^sub>V (A \<otimes>\<^sub>s ket x) = (U x *\<^sub>V A) \<otimes>\<^sub>s ket x\<close>
  by (simp add: assms swap_sandwich_swap_ell2 sandwich_apply)

lemma controlled_op_const: \<open>controlled_op (\<lambda>_. P) = Snd P\<close>
  by (auto intro!: equal_ket simp: Snd_def tensor_op_ell2 simp flip: tensor_ell2_ket)



subsection \<open>Superpositions\<close>

lift_definition uniform_superpos :: \<open>'a set \<Rightarrow> 'a ell2\<close> is \<open>\<lambda>A x. complex_of_real (of_bool (x \<in> A) / sqrt (of_nat (card A)))\<close>
proof (rename_tac A)
  fix A :: \<open>'a set\<close>
  show \<open>has_ell2_norm (\<lambda>x. complex_of_real (of_bool (x \<in> A) / sqrt (real (card A))))\<close>
  proof (cases \<open>finite A\<close>)
    case True
    show ?thesis
      unfolding has_ell2_norm_def
      apply (rule finite_nonzero_values_imp_summable_on)
      using True by auto
  next
    case False
    then show ?thesis
      by simp
  qed
qed

lemma norm_uniform_superpos: \<open>norm (uniform_superpos A) = 1\<close> if \<open>finite A\<close> and \<open>A \<noteq> {}\<close>
proof (transfer' fixing: A)
  have \<open>ell2_norm (\<lambda>x. complex_of_real (of_bool (x \<in> A) / sqrt (real (card A))))
      = sqrt (\<Sum>\<^sub>\<infinity>x. (cmod (complex_of_real (of_bool (x \<in> A) / sqrt (real (card A)))))\<^sup>2)\<close>
    by (simp add: ell2_norm_def)
  also have \<open>\<dots> = sqrt (\<Sum>\<^sub>\<infinity>x\<in>A. (cmod (complex_of_real (1 / sqrt (real (card A)))))\<^sup>2)\<close>
    apply (rule arg_cong[where f=sqrt])
    apply (rule infsum_cong_neutral)
    by auto
  also have \<open>\<dots> = sqrt (\<Sum>x\<in>A. (cmod (complex_of_real (1 / sqrt (real (card A)))))\<^sup>2)\<close>
    by simp
  also have \<open>\<dots> = sqrt (real (card A) * (cmod (1 / complex_of_real (sqrt (real (card A)))))\<^sup>2)\<close>
    by (simp add: that)
  also have \<open>\<dots> = sqrt (real (card A) * ((1 / sqrt (real (card A)))\<^sup>2))\<close>
    by (simp add: cmod_def)
  also have \<open>\<dots> = 1\<close>
    using that 
    by (simp add: power_one_over)
  finally show \<open>ell2_norm (\<lambda>x. complex_of_real (of_bool (x \<in> A) / sqrt (real (card A)))) = 1\<close>
    by -
qed

lemma uniform_superpos_infinite: \<open>uniform_superpos A = 0\<close> if \<open>infinite A\<close>
  apply (transfer' fixing: A)
  using that
  by simp

lemma uniform_superpos_empty: \<open>uniform_superpos A = 0\<close> if \<open>A = {}\<close>
  apply (transfer' fixing: A)
  using that
  by simp

text \<open>Alternative definition.\<close>
lemma uniform_superpos_def2: \<open>uniform_superpos A = (\<Sum>f\<in>A. ket f /\<^sub>C csqrt (card A))\<close>
proof -
  wlog [simp]: \<open>finite A\<close> \<open>A \<noteq> {}\<close>
    using negation uniform_superpos_empty uniform_superpos_infinite by force
  show ?thesis
  proof (rule cinner_ket_eqI)
    fix f
    show \<open>ket f \<bullet>\<^sub>C (uniform_superpos A) = ket f \<bullet>\<^sub>C (\<Sum>f\<in>A. ket f /\<^sub>C csqrt (card A))\<close>
    proof (cases \<open>f \<in> A\<close>)
      case True
      then have \<open>ket f \<bullet>\<^sub>C (uniform_superpos A) = 1 / csqrt (card A)\<close>
        apply (subst cinner_ket_left)
        apply (transfer fixing: f)
        by auto
      moreover have \<open>ket f \<bullet>\<^sub>C (\<Sum>f\<in>A. ket f /\<^sub>C csqrt (card A)) = 1 / csqrt (card A)\<close>
        apply (subst cinner_sum_right)
        apply (subst sum_single[where i=f])
        using True by (auto simp: inverse_eq_divide)
      finally show ?thesis
        by simp
    next
      case False
      then have \<open>ket f \<bullet>\<^sub>C (uniform_superpos A) = 0\<close>
        apply (subst cinner_ket_left)
        apply (transfer fixing: f)
        by auto
      moreover have \<open>ket f \<bullet>\<^sub>C (\<Sum>f\<in>A. ket f /\<^sub>C csqrt (card A)) = 0\<close>
        apply (subst cinner_sum_right)
        apply (rule sum.neutral)
        using False by auto
      finally show ?thesis
        by simp
    qed
  qed
qed


subsection \<open>Lifting ell2 to option type\<close>

lift_definition lift_ell2' :: \<open>'a ell2 \<Rightarrow> 'a option ell2\<close> is \<open>\<lambda>\<psi> x. case x of Some x' \<Rightarrow> \<psi> x' | None \<Rightarrow> 0\<close>
proof -
  fix \<psi> :: \<open>'a \<Rightarrow> complex\<close>
  assume \<open>has_ell2_norm \<psi>\<close>
  then have \<open>(\<lambda>x. norm ((\<psi> x)\<^sup>2)) summable_on UNIV\<close>
    by (simp add: has_ell2_norm_def)
  then have \<open>(\<lambda>x. case x of Some x' \<Rightarrow> norm ((\<psi> x')\<^sup>2) | None \<Rightarrow> 0) o Some summable_on UNIV\<close>
    by (metis comp_eq_dest_lhs option.simps(5) summable_on_cong)
  then have \<open>(\<lambda>x. case x of Some x' \<Rightarrow> norm ((\<psi> x')\<^sup>2) | None \<Rightarrow> 0) summable_on Some ` UNIV\<close>
    by (meson inj_Some summable_on_reindex)
  then have \<open>(\<lambda>x. case x of Some x' \<Rightarrow> norm ((\<psi> x')\<^sup>2) | None \<Rightarrow> 0) summable_on UNIV\<close>
    apply (rule summable_on_cong_neutral[THEN iffD1, rotated -1])
    by (auto simp add: notin_range_Some)
  then show \<open>has_ell2_norm (case_option 0 \<psi>)\<close>
    apply (simp add: has_ell2_norm_def)
    by (metis (mono_tags, lifting) norm_zero option.case_eq_if summable_on_cong zero_power2)
qed

lemma clinear_lift_ell2': \<open>clinear lift_ell2'\<close>
  apply (rule clinearI; transfer)
  by (auto intro!: ext simp add: option.case_eq_if)

lemma lift_ell2'_norm[simp]: \<open>norm (lift_ell2' \<psi>) = norm \<psi>\<close>
proof transfer
  fix \<psi> :: \<open>'a \<Rightarrow> complex\<close>
  have \<open>(ell2_norm \<psi>)\<^sup>2 = infsum (\<lambda>x. (norm (\<psi> x))\<^sup>2) UNIV\<close>
    apply (simp add: ell2_norm_def)
    by (meson infsum_nonneg zero_le_power2)
  also have \<open>\<dots> = infsum ((\<lambda>x. case x of Some x' \<Rightarrow> (norm (\<psi> x'))\<^sup>2 | None \<Rightarrow> 0) o Some) UNIV\<close>
    apply (rule infsum_cong) by auto
  also have \<open>\<dots> = infsum (\<lambda>x. case x of Some x' \<Rightarrow> (norm (\<psi> x'))\<^sup>2 | None \<Rightarrow> 0) (Some ` UNIV)\<close>
    by (simp add: infsum_reindex)
  also have \<open>\<dots> = infsum (\<lambda>x. case x of Some x' \<Rightarrow> (norm (\<psi> x'))\<^sup>2 | None \<Rightarrow> 0) UNIV\<close>
    apply (rule infsum_cong_neutral)
    by (auto simp add: notin_range_Some)
  also have \<open>\<dots> = (ell2_norm (case_option 0 \<psi>))\<^sup>2\<close>
    apply (simp add: ell2_norm_def)
    by (smt (verit, ccfv_SIG) infsum_nonneg infsum_cong norm_zero option.case_eq_if real_sqrt_pow2_iff zero_le_power2 zero_power2)
  finally show \<open>ell2_norm (case_option 0 \<psi>) = ell2_norm \<psi>\<close>
    by (simp add: ell2_norm_geq0)
qed

lemma bounded_clinear_lift_ell2'[bounded_clinear, simp]: \<open>bounded_clinear lift_ell2'\<close>
  by (metis bounded_clinear.intro bounded_clinear_axioms.intro clinear_lift_ell2' lift_ell2'_norm mult.commute mult_1 order.refl)

lift_definition lift_ell2 :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a option ell2\<close> is lift_ell2'
  by simp

definition lift_op :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('a option ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b option ell2)\<close> where
  \<open>lift_op A = (lift_ell2 o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L lift_ell2*) + butterfly (ket None) (ket None)\<close>

lemma lift_ell2_ket[simp]: \<open>lift_ell2 *\<^sub>V ket x = ket (Some x)\<close>
  unfolding lift_ell2.rep_eq apply transfer
  by (auto intro!: ext simp: of_bool_def split!: option.split if_split_asm)

lemma isometry_lift_ell2[simp]: \<open>isometry lift_ell2\<close>
  apply (rule norm_preserving_isometry)
  by (simp add: lift_ell2.rep_eq)

lemma lift_op_adj: \<open>(lift_op A)* = lift_op (A*)\<close>
  unfolding lift_op_def
  apply (simp add: adj_plus)
  by (simp add: cblinfun_assoc_left(1))

lemma bra_None_lift_ell2: \<open>bra None o\<^sub>C\<^sub>L lift_ell2 = 0\<close>
  apply (rule cblinfun_eqI)
  apply (simp add: lift_ell2.rep_eq)
  apply transfer
  by (simp add: infsum_0)

lemma lift_op_mult: \<open>lift_op A o\<^sub>C\<^sub>L lift_op B = lift_op (A o\<^sub>C\<^sub>L B)\<close>
proof -
  have \<open>lift_op A o\<^sub>C\<^sub>L lift_op B = 
          (lift_ell2 o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L (lift_ell2* o\<^sub>C\<^sub>L lift_ell2) o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L lift_ell2*)
        + (lift_ell2 o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L (bra None o\<^sub>C\<^sub>L lift_ell2)* o\<^sub>C\<^sub>L bra None)
        + (vector_to_cblinfun (ket None) o\<^sub>C\<^sub>L (bra None o\<^sub>C\<^sub>L lift_ell2) o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L lift_ell2*)
        + butterfly (ket None) (ket None)\<close>
    unfolding lift_op_def 
    apply (simp add: adj_plus cblinfun_compose_add_right cblinfun_compose_add_left del: isometryD)
    apply (simp add: butterfly_def cblinfun_compose_assoc del: isometryD)
    by (metis butterfly_def cblinfun_comp_butterfly)
  also have \<open>\<dots> = (lift_ell2 o\<^sub>C\<^sub>L (A o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L lift_ell2*) + butterfly (ket None) (ket None)\<close>
    by (simp add: bra_None_lift_ell2 cblinfun_compose_assoc)
  also have \<open>\<dots> = lift_op (A o\<^sub>C\<^sub>L B)\<close>
    by (simp add: lift_op_def)
  finally show ?thesis
    by -
qed

lemma lift_ell2_adj_None[simp]: \<open>lift_ell2* *\<^sub>V ket None = 0\<close>
  by (simp add: cinner_adj_right cinner_ket_eqI lift_ell2_ket)

lemma lift_ell2_adj_Some[simp]: \<open>lift_ell2* *\<^sub>V ket (Some x) = ket x\<close>
  by (simp add: cinner_adj_right cinner_ket cinner_ket_eqI lift_ell2_ket)

lemma lift_op_id[simp]: \<open>lift_op id_cblinfun = id_cblinfun\<close>
  apply (rule equal_ket, case_tac x)
  by (auto simp: lift_op_def cblinfun.add_left cblinfun_compose_add_right lift_ell2_adj_None lift_ell2_ket)

lemma isometry_lift_op[simp]: \<open>isometry (lift_op A)\<close> if \<open>isometry A\<close>
  by (simp add: isometry_def lift_op_mult lift_op_adj isometryD[OF that])

lemma unitary_lift_op[simp]: \<open>unitary (lift_op A)\<close> if \<open>unitary A\<close>
  by (metis isometry_lift_op lift_op_adj that unitary_twosided_isometry)

lemma lift_op_None[simp]: \<open>lift_op A *\<^sub>V ket None = ket None\<close>
  unfolding lift_op_def by (auto simp: cblinfun.add_left)

lemma lift_op_Some[simp]: \<open>lift_op A *\<^sub>V ket (Some x) = lift_ell2 *\<^sub>V A *\<^sub>V ket x\<close>
  unfolding lift_op_def by (auto simp: cblinfun.add_left)

(* TODO should be already declared like that in Registers *)
declare register_tensor_is_register[simp]

lemma sum_sqrt: \<open>(\<Sum>i<n. sqrt i) \<le> 2/3 * (sqrt n)^3\<close> for n :: nat
proof (induction n)
  case 0
  show ?case
    by simp
next
  case (Suc n)
  have \<open>(\<Sum>i<Suc n. sqrt i) \<le>  2/3 * sqrt (real n) ^ 3 + sqrt n\<close>
    using Suc
    by simp
  also have \<open>\<dots> \<le> 2/3 * sqrt (Suc n) ^ 3\<close>
  proof -
    define x :: real where \<open>x = n\<close>
    define f where \<open>f z = 2/3 * (sqrt z)^3\<close> for z
    have f': \<open>(f has_real_derivative sqrt z) (at z)\<close> if \<open>z > 0\<close> for z
      apply (rule ssubst[of \<open>sqrt z\<close>, rotated])
      unfolding f_def
       apply (rule that DERIV_real_sqrt derivative_eq_intros refl)+
      using that
      apply simp
      by (smt (verit, del_insts) Extra_Ordered_Fields.sign_simps(5) nonzero_eq_divide_eq sqrt_divide_self_eq)
    have cont: \<open>continuous_on {x..x+1} f\<close>
      unfolding f_def
      by (intro continuous_intros)
    have \<open>x \<ge> 0\<close>
      using x_def by auto
    obtain l z where \<open>x < z\<close> \<open>z < x + 1\<close> and f'l: \<open>(f has_real_derivative l) (at z)\<close> and fdelta: \<open>f (x + 1) - f x = (x + 1 - x) * l\<close>
      apply atomize_elim
      apply (subst ex_comm)
      apply (rule MVT)
        apply simp
       apply (rule cont)
      using f'
      by (smt (verit, best) \<open>0 \<le> x\<close> real_differentiable_def)
    then have \<open>z > 0\<close>
      using \<open>0 \<le> x\<close> by linarith
    from f'[OF this] f'l have [simp]: \<open>l = sqrt z\<close>
      using DERIV_unique by blast
    from fdelta
    have \<open>f (x + 1) - f x \<ge> sqrt x\<close>
      using \<open>x < z\<close> by auto
    then show ?thesis
      unfolding x_def f_def
      by (smt (verit, best) Num.of_nat_simps(3))
  qed
  finally show ?case
    by -
qed

lemma register_inj':
  assumes \<open>register Q\<close>
  shows \<open>Q a = Q b \<longleftrightarrow> a = b\<close>
  using register_inj[OF assms] by blast

lemma norm_cblinfun_apply_leq1I:
  assumes \<open>norm U \<le> 1\<close>
  assumes \<open>norm \<psi> \<le> 1\<close>
  shows \<open>norm (U *\<^sub>V \<psi>) \<le> 1\<close>
  by (smt (verit, best) assms(1,2) mult_left_le_one_le norm_cblinfun norm_ge_zero)

lemma times_sqrtn_div_n[simp]:
  assumes \<open>n \<ge> 0\<close>
  shows \<open>a * sqrt n / n = a / sqrt n\<close>
  by (metis assms divide_divide_eq_right real_div_sqrt)


lemma Proj_tensor_Proj: \<open>Proj I \<otimes>\<^sub>o Proj J = Proj (I \<otimes>\<^sub>S J)\<close>
  by (simp add: Proj_on_own_range is_Proj_tensor_op
      tensor_ccsubspace_via_Proj)

lemma extend_mult_rule: \<open>a * b = c \<Longrightarrow> a * (b * d) = c * d\<close> for a b c d :: \<open>_::semigroup_mult\<close>
  by (metis Groups.mult_ac(1))


end
