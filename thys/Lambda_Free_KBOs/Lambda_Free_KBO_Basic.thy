(*  Title:       A Basic Knuth-Bendix Order for Lambda-Free Higher-Order Terms
    Author:      Heiko Becker <heikobecker92@gmail.com>, 2016
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Uwe Waldmann <waldmann at mpi-inf.mpg.de>, 2016
    Author:      Daniel Wand <dwand at mpi-inf.mpg.de>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>A Basic Knuth-Bendix Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_KBO_Basic
imports Lambda_Free_KBO_Std
begin

locale kbo_basic_basis = gt_sym "op >\<^sub>s"
    for gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) +
  fixes
    wt_sym :: "'s \<Rightarrow> nat" and
    \<epsilon> :: nat ("\<epsilon>") and
    ground_heads_var :: "'v \<Rightarrow> 's set" and
    extf :: "'s \<Rightarrow> (('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm list \<Rightarrow>
      bool"
  assumes
    \<epsilon>_gt_0: "\<epsilon> > 0" and
    wt_sym_ge_\<epsilon>: "wt_sym f \<ge> \<epsilon>" and
    ground_heads_var_nonempty: "ground_heads_var x \<noteq> {}" and
    extf_ext_irrefl_before_trans: "ext_irrefl_before_trans (extf f)" and
    extf_ext_compat_list_strong: "ext_compat_list_strong (extf f)" and
    extf_ext_hd_or_tl: "ext_hd_or_tl (extf f)"
begin

lemma wt_sym_gt_0: "wt_sym f > 0"
  by (rule less_le_trans[OF \<epsilon>_gt_0 wt_sym_ge_\<epsilon>])

end

sublocale kbo_basic_basis < kbo_std_basis _ _ "\<lambda>_. \<infinity>" "\<lambda>_. \<infinity>" _ _ 0
  unfolding kbo_std_basis_def kbo_std_basis_axioms_def
  by (auto simp: wt_sym_gt_0 \<epsilon>_gt_0 wt_sym_ge_\<epsilon> less_not_refl2 ground_heads_var_nonempty
    gt_sym_axioms ground_heads_def ground_heads_axioms_def extf_ext_irrefl_before_trans
    extf_ext_compat_list_strong extf_ext_hd_or_tl)

locale kbo_basic = kbo_basic_basis _ _ _ ground_heads_var
  for ground_heads_var :: "'v \<Rightarrow> 's set"

sublocale kbo_basic < kbo_std: kbo_std _ _ _ 0 _ "\<lambda>_. \<infinity>" "\<lambda>_. \<infinity>"
  by (simp add: \<epsilon>_gt_0 kbo_std_def kbo_std_basis_axioms)

context kbo_basic
begin

fun wt :: "('s, 'v) tm \<Rightarrow> nat" where
  "wt (Hd \<zeta>) = (LEAST w. \<exists>f \<in> ground_heads \<zeta>. w = wt_sym f)"
| "wt (App s t) = wt s + wt t"

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_wt: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t > wt s \<Longrightarrow> t >\<^sub>t s"
| gt_diff: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t >\<^sub>h\<^sub>d head s \<Longrightarrow> t >\<^sub>t s"
| gt_same: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t = head s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head s). extf f (op >\<^sub>t) (args t) (args s)) \<Longrightarrow> t >\<^sub>t s"

lemma arity_hd_eq_inf[simp]: "arity_hd \<zeta> = \<infinity>"
  by (cases \<zeta>) auto

lemma waryI[intro, simp]: "wary s"
  by (simp add: wary_inf_ary)

lemma basic_wt_eq_wt: "wt s = kbo_std.wt s"
  by (induct s) auto

lemma
  basic_gt_and_gt_le_gt: "(\<lambda>t s. t >\<^sub>t s \<and> local.kbo_std.gt t s) \<le> kbo_std.gt" and
  gt_and_basic_gt_le_basic_gt: "(\<lambda>t s. local.kbo_std.gt t s \<and> t >\<^sub>t s) \<le> op >\<^sub>t"
  by auto

lemma basic_gt_iff_lt: "t >\<^sub>t s \<longleftrightarrow> kbo_std.gt t s"
proof
  assume "t >\<^sub>t s"
  thus "kbo_std.gt t s"
  proof induct
    case gt_wt
    thus ?case
      by (auto intro: kbo_std.gt_wt simp: basic_wt_eq_wt[symmetric])
  next
    case gt_diff
    thus ?case
      by (auto intro: kbo_std.gt_diff simp: basic_wt_eq_wt[symmetric])
  next
    case gt_same
    thus ?case
      using extf_mono[OF basic_gt_and_gt_le_gt]
      by (force simp: basic_wt_eq_wt[symmetric] intro!: kbo_std.gt_same)
  qed
next
  assume "kbo_std.gt t s"
  thus "t >\<^sub>t s"
  proof induct
    case gt_wt_t_s: gt_wt
    thus ?case
      by (auto intro: gt_wt simp: basic_wt_eq_wt[symmetric])
  next
    case gt_unary_t_s: (gt_unary t s)
    have False
      using gt_unary_t_s(4) by (metis less_nat_zero_code wt_sym_gt_0)
    thus ?case
      by satx
  next
    case gt_diff_t_s: gt_diff
    thus ?case
      by (auto intro: gt_diff simp: basic_wt_eq_wt[symmetric])
  next
    case gt_same_t_s: gt_same
    thus ?case
      using extf_mono[OF gt_and_basic_gt_le_basic_gt]
      by (auto intro!: gt_same simp: basic_wt_eq_wt[symmetric])
  qed
qed

theorem gt_irrefl: "\<not> s >\<^sub>t s"
  unfolding basic_gt_iff_lt by (rule kbo_std.gt_irrefl[simplified])

theorem gt_trans: "u >\<^sub>t t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> u >\<^sub>t s"
  unfolding basic_gt_iff_lt by (rule kbo_std.gt_trans[simplified])

theorem gt_compat_fun: "t' >\<^sub>t t \<Longrightarrow> App s t' >\<^sub>t App s t"
  unfolding basic_gt_iff_lt by (rule kbo_std.gt_compat_fun[simplified])

theorem gt_compat_arg: "s' >\<^sub>t s \<Longrightarrow> App s' t >\<^sub>t App s t"
  unfolding basic_gt_iff_lt by (rule kbo_std.gt_compat_arg[simplified])

theorem gt_proper_sub: "proper_sub s t \<Longrightarrow> t >\<^sub>t s"
  unfolding basic_gt_iff_lt by (rule kbo_std.gt_proper_sub[simplified])

theorem gt_subst: "wary_subst \<rho> \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s"
  unfolding basic_gt_iff_lt by (rule kbo_std.gt_subst[simplified])

theorem gt_wf: "wfP (\<lambda>s t. t >\<^sub>t s)"
  unfolding basic_gt_iff_lt[abs_def] by (rule kbo_std.gt_wf[simplified])

end

end
