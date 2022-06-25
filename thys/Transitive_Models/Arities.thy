section\<open>Arities of internalized formulas\<close>
theory Arities
  imports
    Discipline_Base
begin

lemmas FOL_arities [simp del, arity] = arity_And arity_Or arity_Implies arity_Iff arity_Exists

declare pred_Un_distrib[arity_aux]

context
  notes FOL_arities[simp]
begin

lemma arity_upair_fm [arity] : "\<lbrakk>  t1\<in>nat ; t2\<in>nat ; up\<in>nat  \<rbrakk> \<Longrightarrow>
  arity(upair_fm(t1,t2,up)) = \<Union> {succ(t1),succ(t2),succ(up)}"
  unfolding  upair_fm_def
  using union_abs1 union_abs2 pred_Un
  by auto

end

lemma Un_trasposition_aux1: "r \<union> s \<union> r = r \<union> s" by auto

lemma Un_trasposition_aux2:
  "r \<union> (s \<union> (r \<union> u))= r \<union> (s \<union> u)"
  "r \<union> (s \<union> (t \<union> (r \<union> u)))= r \<union> (s \<union> (t \<union> u))" by auto

txt\<open>Using the previous lemmas to guide the automatic arity calculation.\<close>

context
  notes Un_assoc[symmetric,simp] Un_trasposition_aux1[simp]
begin

arity_theorem for "pair_fm"
arity_theorem for "composition_fm"
arity_theorem for "domain_fm"
arity_theorem for "range_fm"
arity_theorem for "union_fm"
arity_theorem for "image_fm"
arity_theorem for "pre_image_fm"
arity_theorem for "big_union_fm"
arity_theorem for "fun_apply_fm"
arity_theorem for "field_fm"
arity_theorem for "empty_fm"
arity_theorem for "cons_fm"
arity_theorem for "succ_fm"
arity_theorem for "number1_fm"
arity_theorem for "function_fm"
arity_theorem for "relation_fm"
arity_theorem for "restriction_fm"
arity_theorem for "typed_function_fm"
arity_theorem for "subset_fm"
arity_theorem for "transset_fm"
arity_theorem for "ordinal_fm"
arity_theorem for "limit_ordinal_fm"
arity_theorem for "finite_ordinal_fm"
arity_theorem for "omega_fm"
arity_theorem for "cartprod_fm"
arity_theorem for "singleton_fm"
arity_theorem for "Memrel_fm"
arity_theorem for "quasinat_fm"

end \<comment> \<open>context\<close>

context
  notes FOL_arities[simp]
begin

lemma arity_is_recfun_fm [arity]:
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; Z\<in>nat;i\<in>nat\<rbrakk> \<Longrightarrow>  arity(p) = i \<Longrightarrow>
  arity(is_recfun_fm(p,v,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union> pred(pred(pred(pred(i))))"
  unfolding is_recfun_fm_def
  using arity_upair_fm arity_pair_fm arity_pre_image_fm arity_restriction_fm
    union_abs2 pred_Un_distrib
  by auto

lemma arity_is_wfrec_fm [arity]:
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; Z\<in>nat ; i\<in>nat\<rbrakk> \<Longrightarrow> arity(p) = i \<Longrightarrow>
    arity(is_wfrec_fm(p,v,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union> pred(pred(pred(pred(pred(i)))))"
  unfolding is_wfrec_fm_def
  using arity_succ_fm  arity_is_recfun_fm
    union_abs2 pred_Un_distrib
  by auto

lemma arity_is_nat_case_fm [arity]:
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; Z\<in>nat; i\<in>nat\<rbrakk> \<Longrightarrow> arity(p) = i \<Longrightarrow>
    arity(is_nat_case_fm(v,p,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union> pred(pred(i))"
  unfolding is_nat_case_fm_def
  using arity_succ_fm arity_empty_fm arity_quasinat_fm
    union_abs2 pred_Un_distrib
  by auto

lemma arity_iterates_MH_fm [arity]:
  assumes "isF\<in>formula" "v\<in>nat" "n\<in>nat" "g\<in>nat" "z\<in>nat" "i\<in>nat"
    "arity(isF) = i"
  shows "arity(iterates_MH_fm(isF,v,n,g,z)) =
           succ(v) \<union> succ(n) \<union> succ(g) \<union> succ(z) \<union> pred(pred(pred(pred(i))))"
proof -
  let ?\<phi> = "Exists(And(fun_apply_fm(succ(succ(succ(g))), 2, 0), Forall(Implies(Equal(0, 2), isF))))"
  let ?ar = "succ(succ(succ(g))) \<union> pred(pred(i))"
  from assms
  have "arity(?\<phi>) =?ar" "?\<phi>\<in>formula"
    using arity_fun_apply_fm
      union_abs1 union_abs2 pred_Un_distrib succ_Un_distrib Un_assoc[symmetric]
    by simp_all
  then
  show ?thesis
    unfolding iterates_MH_fm_def
    using arity_is_nat_case_fm[OF \<open>?\<phi>\<in>_\<close> _ _ _ _ \<open>arity(?\<phi>) = ?ar\<close>] assms pred_succ_eq pred_Un_distrib
    by auto
qed

lemma arity_is_iterates_fm [arity]:
  assumes "p\<in>formula" "v\<in>nat" "n\<in>nat" "Z\<in>nat" "i\<in>nat"
    "arity(p) = i"
  shows "arity(is_iterates_fm(p,v,n,Z)) = succ(v) \<union> succ(n) \<union> succ(Z) \<union>
          pred(pred(pred(pred(pred(pred(pred(pred(pred(pred(pred(i)))))))))))"
proof -
  let ?\<phi> = "iterates_MH_fm(p, 7+\<^sub>\<omega>v, 2, 1, 0)"
  let ?\<psi> = "is_wfrec_fm(?\<phi>, 0, succ(succ(n)),succ(succ(Z)))"
  from \<open>v\<in>_\<close>
  have "arity(?\<phi>) = (8+\<^sub>\<omega>v) \<union> pred(pred(pred(pred(i))))" "?\<phi>\<in>formula"
    using assms arity_iterates_MH_fm union_abs2
    by simp_all
  then
  have "arity(?\<psi>) = succ(succ(succ(n))) \<union> succ(succ(succ(Z))) \<union> (3+\<^sub>\<omega>v) \<union>
      pred(pred(pred(pred(pred(pred(pred(pred(pred(i)))))))))"
    using assms arity_is_wfrec_fm[OF \<open>?\<phi>\<in>_\<close> _ _ _ _ \<open>arity(?\<phi>) = _\<close>] union_abs1 pred_Un_distrib
    by auto
  then
  show ?thesis
    unfolding is_iterates_fm_def
    using arity_Memrel_fm arity_succ_fm assms union_abs1 pred_Un_distrib
    by auto
qed

lemma arity_eclose_n_fm [arity]:
  assumes "A\<in>nat" "x\<in>nat" "t\<in>nat"
  shows "arity(eclose_n_fm(A,x,t)) = succ(A) \<union> succ(x) \<union> succ(t)"
proof -
  let ?\<phi> = "big_union_fm(1,0)"
  have "arity(?\<phi>) = 2" "?\<phi>\<in>formula"
    using arity_big_union_fm union_abs2
    by auto
  with assms
  show ?thesis
    unfolding eclose_n_fm_def
    using arity_is_iterates_fm[OF \<open>?\<phi>\<in>_\<close> _ _ _,of _ _ _ 2]
    by auto
qed

lemma arity_mem_eclose_fm [arity]:
  assumes "x\<in>nat" "t\<in>nat"
  shows "arity(mem_eclose_fm(x,t)) = succ(x) \<union> succ(t)"
proof -
  let ?\<phi>="eclose_n_fm(x +\<^sub>\<omega> 2, 1, 0)"
  from \<open>x\<in>nat\<close>
  have "arity(?\<phi>) = x+\<^sub>\<omega>3"
    using arity_eclose_n_fm union_abs2
    by simp
  with assms
  show ?thesis
    unfolding mem_eclose_fm_def
    using arity_finite_ordinal_fm union_abs2 pred_Un_distrib
    by simp
qed

lemma arity_is_eclose_fm [arity]:
  "\<lbrakk>x\<in>nat ; t\<in>nat\<rbrakk> \<Longrightarrow> arity(is_eclose_fm(x,t)) = succ(x) \<union> succ(t)"
  unfolding is_eclose_fm_def
  using arity_mem_eclose_fm union_abs2 pred_Un_distrib
  by auto

lemma arity_Collect_fm [arity]:
  assumes "x \<in> nat" "y \<in> nat" "p\<in>formula"
  shows "arity(Collect_fm(x,p,y)) = succ(x) \<union> succ(y) \<union> pred(arity(p))"
  unfolding Collect_fm_def
  using assms pred_Un_distrib
  by auto

schematic_goal arity_least_fm':
  assumes
    "i \<in> nat" "q \<in> formula"
  shows
    "arity(least_fm(q,i)) \<equiv> ?ar"
  unfolding least_fm_def
  using assms pred_Un_distrib arity_And arity_Or arity_Neg arity_Implies arity_ordinal_fm
    arity_empty_fm Un_assoc[symmetric] Un_commute
  by auto

lemma arity_least_fm [arity]:
  assumes
    "i \<in> nat" "q \<in> formula"
  shows
    "arity(least_fm(q,i)) = succ(i) \<union> pred(arity(q))"
  using assms arity_least_fm'
  by auto

lemma arity_Replace_fm [arity]:
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; i\<in>nat\<rbrakk> \<Longrightarrow> arity(p) = i \<Longrightarrow>
    arity(Replace_fm(v,p,n)) = succ(n) \<union> succ(v) \<union> pred(pred(i))"
  unfolding Replace_fm_def
  using union_abs2 pred_Un_distrib
  by auto

lemma arity_lambda_fm [arity]:
  "\<lbrakk>p\<in>formula; v\<in>nat ; n\<in>nat; i\<in>nat\<rbrakk> \<Longrightarrow>  arity(p) = i \<Longrightarrow>
    arity(lambda_fm(p,v,n)) = succ(n) \<union> (succ(v) \<union> (pred^3(i)))"
  unfolding lambda_fm_def
  using arity_pair_fm pred_Un_distrib union_abs1 union_abs2
  by simp

lemma arity_transrec_fm [arity]:
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; i\<in>nat\<rbrakk> \<Longrightarrow> arity(p) = i \<Longrightarrow>
     arity(is_transrec_fm(p,v,n)) = succ(v) \<union> succ(n) \<union> (pred^8(i))"
  unfolding is_transrec_fm_def
  using arity Un_assoc[symmetric] pred_Un_distrib
  by simp

lemma arity_wfrec_replacement_fm :
  "\<lbrakk>p\<in>formula ; v\<in>nat ; n\<in>nat; Z\<in>nat ; i\<in>nat\<rbrakk> \<Longrightarrow> arity(p) = i \<Longrightarrow>
    arity(Exists(And(pair_fm(1,0,2),is_wfrec_fm(p,v,n,Z))))
   = 2 \<union> v \<union> n \<union> Z \<union> (pred^6(i))"
  unfolding is_wfrec_fm_def
  using arity_succ_fm  arity_is_recfun_fm union_abs2 pred_Un_distrib arity_pair_fm
  by auto

end \<comment> \<open>@{thm [source] FOL_arities}\<close>

declare arity_subset_fm [simp del] arity_ordinal_fm[simp del, arity] arity_transset_fm[simp del]

context
  notes Un_assoc[symmetric,simp] Un_trasposition_aux1[simp]
begin
arity_theorem for "rtran_closure_mem_fm"
arity_theorem for "rtran_closure_fm"
arity_theorem for "tran_closure_fm"
end

context
  notes Un_assoc[simp] Un_trasposition_aux2[simp]
begin
arity_theorem for "injection_fm"
arity_theorem for "surjection_fm"
arity_theorem for "bijection_fm"
arity_theorem for "order_isomorphism_fm"
end

arity_theorem for "Inl_fm"
arity_theorem for "Inr_fm"
arity_theorem for "pred_set_fm"

end