theory Refine_Vector_List
  imports
  "Ordinary_Differential_Equations.Reachability_Analysis"
  "Affine_Arithmetic.Affine_Arithmetic"
  "HOL-ODE-Refinement.Autoref_Misc" (* TODO: what is still needed there? *)
  "HOL-ODE-Refinement.Weak_Set"
  "Runge_Kutta"
begin

subsection \<open>Id on euclidean space, real etc\<close>

consts i_rnv::interface
abbreviation "rnv_rel \<equiv> (Id::('a::real_normed_vector\<times>_) set)"
lemmas [autoref_rel_intf] = REL_INTFI[of rnv_rel i_rnv]

subsection \<open>list vector relation\<close>

definition lv_rel::"(real list \<times> 'a::executable_euclidean_space) set"
  where "lv_rel = br eucl_of_list (\<lambda>xs. length xs = DIM('a))"

lemmas [autoref_rel_intf] = REL_INTFI[of lv_rel i_rnv]

lemma lv_rel_sv[relator_props]: "single_valued lv_rel"
  by (auto simp: lv_rel_def)

context begin interpretation autoref_syn .

lemma lv_rel_le[autoref_rules]: "(list_all2 (\<lambda>x y. x \<le> y), op \<le>) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel"
  by (auto simp: lv_rel_def br_def eucl_le[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id)
     (metis distinct_Basis_list index_nth_id length_Basis_list nth_Basis_list_in_Basis)

lemma lv_rel_inf[autoref_rules]: "(map2 min, inf) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_inf[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id inf_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_sup[autoref_rules]: "(map2 max, sup) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_add[autoref_rules]: "(map2 op +, op +) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def algebra_simps
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_minus[autoref_rules]: "(map2 op -, op -) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def algebra_simps
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_scaleR[autoref_rules]: "(\<lambda>r. map (scaleR r), scaleR) \<in> rnv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_uminus[autoref_rules]: "(map uminus, uminus) \<in> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_sup[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_abs[autoref_rules]: "(map abs, abs) \<in> lv_rel \<rightarrow> lv_rel"
  by (auto simp: lv_rel_def br_def eucl_abs[where 'a='a] eucl_of_list_inner list_all2_conv_all_nth
      index_nth_id sup_real_def
      intro!: euclidean_eqI[where 'a='a])

lemma lv_rel_inner[autoref_rules]: "(inner_lv_rel, op \<bullet>) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> rnv_rel"
  by (subst euclidean_inner[abs_def], subst sum_list_Basis_list[symmetric])
    (auto simp: lv_rel_def br_def eucl_of_list_inner sum_list_sum_nth index_nth_id inner_lv_rel_def)

definition "mig_real a b = (if a \<le> 0 \<and> 0 \<le> b \<or> b \<le> 0 \<and> 0 \<le> a then 0 else min (abs a) (abs b))"
definition "mig_componentwise a b = (\<Sum>i\<in>Basis. mig_real (a \<bullet> i) (b \<bullet> i) *\<^sub>R i)"
definition "mig_lv a b = (map2 mig_real a b)"
lemma length_mig_lv[simp]: "length (mig_lv a b) = min (length a) (length b)"
  by (auto simp: mig_lv_def)
lemma mig_lv_nth: "mig_real (a ! i) (b ! i) = mig_lv a b ! i" if "i < length a" "i < length b"
  by (auto simp: mig_lv_def that)

lemma mig_real_abs_le: "\<bar>mig_real a b\<bar> \<le> \<bar>x\<bar>" if "x \<in> {a .. b}" for x::real
  using that
  by (auto simp: mig_real_def abs_real_def)

lemma norm_eucl_L2: "norm x = sqrt (\<Sum>i\<in>Basis. (x \<bullet> i)\<^sup>2)"
  unfolding norm_conv_dist by (subst euclidean_dist_l2)  (simp add: setL2_def)

lemma mig_componentwise_inner_Basis: "mig_componentwise a b \<bullet> i = mig_real (a \<bullet> i) (b \<bullet> i)"
  if "i \<in> Basis"
  using that
  by (auto simp: mig_componentwise_def)

lemma norm_mig_componentwise_le: "norm (mig_componentwise a b) \<le> norm x" if "x \<in> {a .. b}" for
  a::"'a::ordered_euclidean_space"
  apply (rule norm_le_in_cubeI)
  apply (simp add: mig_componentwise_inner_Basis)
  apply (rule mig_real_abs_le)
  using that
  by (auto simp: eucl_le[where 'a='a])

lemma mig_componentwise_autoref[autoref_rules]:
  "(mig_lv, mig_componentwise) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  unfolding lv_rel_def
  by (auto simp: mig_componentwise_def euclidean_eq_iff[where 'a='a] eucl_of_list_inner mig_lv_nth
      br_def)

primrec vecsumlist' where
  "vecsumlist' 0 xs       = []"
| "vecsumlist' (Suc i) xs = sum_list (map hd xs)#vecsumlist' i (map tl xs)"

lemma vecsumlist':
  assumes "\<And>xs. xs \<in> set xss \<Longrightarrow> i \<le> length xs"
  shows "vecsumlist' i xss = map (\<lambda>i. sum_list (map (\<lambda>xs. xs ! i) xss)) [0..<i]"
  using assms
proof (induction i arbitrary: xss)
  case 0
  then show ?case by simp
next
  case (Suc i)
  from Suc.prems have xss_ne: "x \<in> set xss \<Longrightarrow> x \<noteq> []" for x
    by force
  show ?case
    apply simp
    apply (subst Suc.IH)
    subgoal using Suc.prems by force
    apply (auto intro!: nth_equalityI)
    using xss_ne
    apply (auto simp: nth_Cons nth_append o_def split: nat.splits)
    apply (meson hd_conv_nth sum_list_cong)
    apply (meson hd_conv_nth sum_list_cong)
    apply (meson Misc.nth_tl sum_list_cong)
    by (metis (no_types, lifting) Misc.nth_tl Suc_leI le_neq_implies_less sum_list_cong)
qed

lemma inner_sum_list_left: "sum_list xs \<bullet> b = (\<Sum>x\<leftarrow>xs. x \<bullet> b)"
  by (auto simp: sum_list_sum_nth inner_sum_left)

definition [simp]: "DIM_eq (TYPE('a::executable_euclidean_space)) n \<longleftrightarrow> DIM('a) = n"
abbreviation "DIM_precond TYPE('a) n \<equiv> DIM_eq TYPE('a::executable_euclidean_space) n"

lemma [autoref_rules]: "(sum_list, sum_list) \<in> \<langle>rnv_rel\<rangle>list_rel \<rightarrow> rnv_rel"
  by auto

lemma lv_rel_sum_list[autoref_rules]:
  assumes "DIM_precond TYPE('a::executable_euclidean_space) n"
  shows "(vecsumlist' n, sum_list) \<in> \<langle>lv_rel::(real list \<times> 'a) set\<rangle>list_rel \<rightarrow> lv_rel"
proof
  fix xss and XS::"'a list"
  assume xss: "(xss, XS) \<in> \<langle>lv_rel\<rangle>list_rel"
  then have "\<And>xs. xs \<in> set xss \<Longrightarrow> DIM('a) \<le> length xs"
    by (auto simp: lv_rel_def list_rel_def in_set_conv_nth br_def dest!: list_all2_nthD )
  from vecsumlist'[OF this, of xss] assms xss
  show "(vecsumlist' n xss, sum_list XS) \<in> lv_rel"
    apply (auto simp: lv_rel_def br_def)
    apply (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_list_inner inner_sum_list_left)
    apply (rule sum_list_nth_eqI)
     apply (auto simp: list_all2_iff list_rel_def in_set_zip Ball_def)
    apply (drule_tac x = "xss ! na" in spec)
    apply (drule_tac x = "XS ! na" in spec)
    apply (auto simp: eucl_of_list_inner)
    done
qed

lemma lv_rel_eq[autoref_rules]: "(op =, op =) \<in> lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel"
  by (auto simp: lv_rel_def br_def euclidean_eq_iff[where 'a='a] eucl_of_list_inner
      intro!: nth_equalityI)
     (metis distinct_Basis_list index_nth_id length_Basis_list nth_Basis_list_in_Basis)

lemma lv_rel_zero[autoref_rules]:
  assumes "DIM_precond TYPE('a::executable_euclidean_space) n"
  shows "(replicate n 0, 0::'a) \<in> lv_rel"
  using assms
  by (auto simp: lv_rel_def br_def eucl_of_list_inner intro!: euclidean_eqI[where 'a='a])

definition "Basis_list_impl n = (let zs = replicate n 0 in map (\<lambda>i. zs[i:=1]) [0..<n])"
lemma lv_rel_Basis_list[autoref_rules]:
  assumes "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  shows "(Basis_list_impl n, Basis_list::'a list) \<in> \<langle>lv_rel\<rangle>list_rel"
  using assms
  by (auto simp: list_rel_def lv_rel_def eucl_of_list_inner inner_Basis nth_eq_iff_index
      Basis_list_impl_def
      intro!: brI list_all2_all_nthI euclidean_eqI[where 'a='a])

definition "lv_ivl xrs yrs = {zrs. list_all2 (op \<le>) xrs zrs \<and> list_all2 (op \<le>) zrs yrs}"

lemma lv_relI:
  "length x = DIM('a) \<Longrightarrow> (x, eucl_of_list x::'a::executable_euclidean_space) \<in> lv_rel"
  by (auto simp: lv_rel_def br_def)

lemma eucl_of_list_image_lv_ivl:
  assumes [simp]: "length xrs = DIM('a)" "length yrs = DIM('a)"
  shows "eucl_of_list ` (lv_ivl xrs yrs) =
    {eucl_of_list xrs .. eucl_of_list yrs::'a::executable_euclidean_space}"
  apply (auto simp: list_all2_iff lv_ivl_def eucl_le[where 'a='a] eucl_of_list_inner Ball_def
      in_set_zip)
  apply (metis Basis_list index_less_size_conv length_Basis_list)
   apply (metis Basis_list index_less_size_conv length_Basis_list)
  apply (rule image_eqI)
   apply (rule eucl_of_list_list_of_eucl[symmetric])
  using nth_Basis_list_in_Basis apply fastforce
  done

end

end