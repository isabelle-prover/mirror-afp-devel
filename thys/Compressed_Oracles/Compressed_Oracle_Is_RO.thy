section \<open>\<open>Compressed_Oracle_Is_RO\<close> -- Equivalence of compressed oracle and regular random oracle\<close>

theory Compressed_Oracle_Is_RO imports
    Registers.Pure_States
    CO_Operations
begin

lemma swap_function_oracle_measure_generic:
  fixes standard_query
  fixes X :: \<open>'x update \<Rightarrow> 'mem update\<close> and Y :: \<open>'y::ab_group_add update \<Rightarrow> 'mem update\<close>
  assumes std_query_Some: \<open>\<And>H x y z. H x = Some z \<Longrightarrow> standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close> (* e.g. standard_query_ket_full_Some *)
  assumes [register]: \<open>compatible X Y\<close>
  shows \<open>(Fst o X; (Fst o Y; Snd)) standard_query o\<^sub>C\<^sub>L Snd (proj (ket (Some o h)))
            = Fst ((X;Y) (function_oracle h)) o\<^sub>C\<^sub>L Snd (proj (ket (Some o h)))\<close>
proof -
  note [[simproc del: Laws_Quantum.compatibility_warn]]
  let ?goal = ?thesis
  have [register]: \<open>register (Fst o X; (Fst o Y; Snd :: _ \<Rightarrow> ('mem \<times> ('x \<rightharpoonup> 'y)) update))\<close>
    by simp
  from register_decomposition[OF this]
  have \<open>let 'd::type = register_decomposition_basis (Fst o X; (Fst o Y; Snd :: _ \<Rightarrow> ('mem \<times> ('x \<rightharpoonup> 'y)) update)) in ?thesis\<close>
  proof with_type_mp
    case with_type_mp
    then obtain U :: \<open>(('x \<times> 'y \<times> ('x \<Rightarrow> 'y option)) \<times> 'd) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('mem \<times> ('x \<Rightarrow> 'y option)) ell2\<close> 
      where \<open>unitary U\<close> and unwrap: \<open>(Fst \<circ> X;(Fst \<circ> Y;Snd)) \<theta> = sandwich U *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by blast
    have unwrap_Snd: \<open>Snd a = sandwich U *\<^sub>V ((id_cblinfun \<otimes>\<^sub>o (id_cblinfun \<otimes>\<^sub>o a)) \<otimes>\<^sub>o id_cblinfun)\<close> for a
      apply (rewrite at Snd to \<open>(Fst \<circ> X;(Fst \<circ> Y;Snd)) o Snd o Snd\<close> DEADID.rel_mono_strong)
       apply (simp add: register_pair_Snd)
      by (simp add: unwrap Snd_def)
    have unwrap_Fst_XY: \<open>(Fst o (X;Y)) a = sandwich U *\<^sub>V assoc (a \<otimes>\<^sub>o id_cblinfun) \<otimes>\<^sub>o id_cblinfun\<close>
      for a
      apply (rewrite at \<open>Fst o (X;Y)\<close> to \<open>(Fst \<circ> X;(Fst \<circ> Y;Snd)) o assoc o Fst\<close> DEADID.rel_mono_strong)
       apply (simp add: register_pair_Fst register_comp_pair)
      by (simp add: only: o_apply unwrap Fst_def)

    have \<open>standard_query \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L
          (id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o proj (ket (Some \<circ> h))) \<otimes>\<^sub>o id_cblinfun =
          assoc (function_oracle h \<otimes>\<^sub>o id_cblinfun) \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L
          (id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o proj (ket (Some \<circ> h))) \<otimes>\<^sub>o id_cblinfun\<close>
      by (auto intro!: equal_ket
          simp: tensor_op_ket tensor_ell2_ket proj_ket_x_y_ofbool std_query_Some assoc_ell2_sandwich
          sandwich_apply function_oracle_apply)
    then show ?goal
      by (auto intro!: arg_cong[where f=\<open>sandwich U\<close>]
          simp add: unwrap unwrap_Snd unwrap_Fst_XY[unfolded o_def] sandwich_arg_compose \<open>unitary U\<close>)
  qed
  from this[cancel_with_type]
  show ?goal
    by -
qed


lemma standard_query_for_fixed_func_generic:
  fixes standard_query
  fixes X :: \<open>'x update \<Rightarrow> 'mem update\<close> and Y :: \<open>'y::ab_group_add update \<Rightarrow> 'mem update\<close>
  assumes \<open>\<And>H x y z. H x = Some z \<Longrightarrow> standard_query *\<^sub>V (ket (x,y,H)) = ket (x, y + z, H)\<close> (* e.g. standard_query_ket_full_Some *)
  assumes \<open>compatible X Y\<close>
  shows \<open>(Fst o X; (Fst o Y; Snd)) standard_query *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))
            = Fst ((X;Y) (function_oracle h)) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
proof -
  have \<open>(Fst o X; (Fst o Y; Snd)) standard_query *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))
      = (Fst o X; (Fst o Y; Snd)) standard_query *\<^sub>V Snd (proj (ket (Some o h))) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
    by (simp add: proj_ket_x_y_ofbool)
  also have \<open>\<dots> = Fst ((X;Y) (function_oracle h)) *\<^sub>V Snd (proj (ket (Some o h))) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
    apply (subst cblinfun_apply_cblinfun_compose[symmetric])+
    by (simp_all add: assms swap_function_oracle_measure_generic)
  also have \<open>\<dots> = Fst ((X;Y) (function_oracle h)) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket (Some \<circ> h))\<close>
    by (simp add: Proj_fixes_image ccspan.rep_eq complex_vector.span_base flip: cblinfun_apply_cblinfun_compose)
  finally show ?thesis
    by -
qed





end