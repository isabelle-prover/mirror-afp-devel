(* TODO: 
   Beginning taken from "Functional_Ordered_Resolution_Prover.IsaFoR_Term"
   Try to rename Name clash, such that a copy is not needed *)
theory IsaFoR_KBO
  imports
    Knuth_Bendix_Order.KBO
    
    VeriComp.Well_founded

    IsaFoR_Nonground_Clause_With_Equality
    IsaFoR_Nonground_Context
    Nonground_Order_With_Equality

    Selection_Function_Select_Max
begin

record 'f weights =
  w :: "'f \<times> nat \<Rightarrow> nat"
  w0 :: nat
  pr_strict :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool"
  least :: "'f \<Rightarrow> bool"
  scf :: "'f \<times> nat \<Rightarrow> nat \<Rightarrow> nat"

class weighted =
  fixes weights :: "'a weights"
  assumes weights_adm:
    "admissible_kbo
       (w weights) (w0 weights) (pr_strict weights) ((pr_strict weights)\<^sup>=\<^sup>=) (least weights) (scf weights)"
  and pr_strict_total: "fi = gj \<or> pr_strict weights fi gj \<or> pr_strict weights gj fi"
  and pr_strict_asymp: "asymp (pr_strict weights)"
  and scf_ok: "i < n \<Longrightarrow> scf weights (f, n) i \<le> 1"

instantiation unit :: weighted begin

definition weights_unit :: "unit weights" where "weights_unit =
  \<lparr>w = Suc \<circ> snd, w0 = 1, pr_strict = \<lambda>(_, n) (_, m). n > m, least = \<lambda>_. True, scf = \<lambda>_ _. 1\<rparr>"

instance
  by (intro_classes, unfold_locales) (auto simp: weights_unit_def SN_iff_wf irreflp_def
      intro!: wf_subset[OF wf_inv_image[OF wf], of _ snd])
end

global_interpretation KBO:
  admissible_kbo
    "w (weights :: 'f :: weighted weights)" "w0 (weights :: 'f :: weighted weights)"
    "pr_strict weights" "((pr_strict weights)\<^sup>=\<^sup>=)" "least weights" "scf weights"
    defines weight = KBO.weight
    and kbo = KBO.kbo
  by (simp add: weights_adm)

lemma kbo_code[code]: "kbo s t =
  (let wt = weight t; ws = weight s in
  if vars_term_ms (KBO.SCF t) \<subseteq># vars_term_ms (KBO.SCF s) \<and> wt \<le> ws
  then
    (if wt < ws then (True, True)
    else
      (case s of
        Var y \<Rightarrow> (False, case t of Var x \<Rightarrow> True | Fun g ts \<Rightarrow> ts = [] \<and> least weights g)
      | Fun f ss \<Rightarrow>
          (case t of
            Var x \<Rightarrow> (True, True)
          | Fun g ts \<Rightarrow>
              if pr_strict weights (f, length ss) (g, length ts) then (True, True)
              else if (f, length ss) = (g, length ts) then lex_ext_unbounded kbo ss ts
              else (False, False))))
  else (False, False))"
  by (subst KBO.kbo.simps) (auto simp: Let_def split: term.splits)

definition "less_kbo s t = fst (kbo t s)"

lemma less_kbo_gtotal: "Term.ground s \<Longrightarrow> Term.ground t \<Longrightarrow> s = t \<or> less_kbo s t \<or> less_kbo t s"
  unfolding less_kbo_def using KBO.S_ground_total
  by (metis pr_strict_total subset_UNIV)

lemma less_kbo_subst:
  fixes \<sigma> :: "('f :: weighted, 'v) subst"
  shows "less_kbo s t \<Longrightarrow> less_kbo (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  unfolding less_kbo_def by (rule KBO.S_subst)

lemma wfP_less_kbo: "wfP less_kbo"
proof -
  have "SN {(x, y). fst (kbo x y)}"
    using pr_strict_asymp by (fastforce simp: asympI irreflp_def intro!: KBO.S_SN scf_ok)
  then show ?thesis
    unfolding SN_iff_wf wfp_def by (rule wf_subset) (auto simp: less_kbo_def)
qed

subsection\<open>Setup weights for nat\<close>

abbreviation pr_strict :: "('f :: wellorder \<times> nat) \<Rightarrow> _ \<Rightarrow> bool" where
  "pr_strict \<equiv> lex_prodp ((<) :: 'f \<Rightarrow> 'f \<Rightarrow> bool) ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"

lemma wfp_pr_strict: "wfp pr_strict"
  by (simp add: lex_prodp_wfP)

abbreviation least where
  "least x \<equiv> \<forall>y. x \<le> y"

abbreviation weights where 
  "weights \<equiv> \<lparr>w =  \<lambda>_. 1, w0 = 1, pr_strict = pr_strict\<inverse>\<inverse>, least = least, scf = \<lambda>_ _. 1\<rparr>"

instantiation nat :: weighted begin

definition weights_nat :: "nat weights" where
  "weights_nat \<equiv> weights"

instance
proof -

  have "SN {(fn  :: nat \<times> nat, gm). fst gm < fst fn \<or> fst gm = fst fn \<and> snd gm < snd fn}"
  proof (fold lex_prodp_def, rule wf_imp_SN)
  
    show "wf ({(fn, gm). pr_strict gm fn}\<inverse>)"
      using wfp_pr_strict
      by (simp add: converse_def wfp_def)
  qed

  then show "OFCLASS(nat, weighted_class)"
    by (intro_classes, unfold weights_nat_def lex_prodp_def admissible_kbo_def) 
       (auto simp: order.order_iff_strict)
qed

end

subsection\<open>Interpret non-ground order with KBO\<close>

interpretation KBO: context_compatible_nonground_order where
  less\<^sub>t = "less_kbo :: ('f :: weighted, 'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool" and
  comp_subst = "(\<circ>\<^sub>s)" and id_subst = Var and term_subst = "(\<cdot>)" and term_vars = term.vars and
  apply_subst = apply_subst and subst_update = fun_upd and compose_context = "(\<circ>\<^sub>c)" and
  term_from_ground = term.from_ground and term_to_ground = term.to_ground and
  hole = \<box> and apply_context = ctxt_apply_term and occurences = occurences and ground_hole = \<box> and
  apply_ground_context = apply_ground_context and compose_ground_context = "(\<circ>\<^sub>c)" and
  term_is_ground = term.is_ground and context_is_ground = context.is_ground and
  context_vars = context.vars and context_subst = context.subst and
  context_from_ground = context.from_ground and context_to_ground = context.to_ground
proof unfold_locales
   show "transp less_kbo"
    using KBO.S_trans
    unfolding transp_def less_kbo_def
    by blast
next
  show "asymp less_kbo"
    using wfp_imp_asymp wfP_less_kbo
    by blast
next
  show "wfp_on (range term.from_ground) less_kbo"
    using wfp_on_subset[OF wfP_less_kbo subset_UNIV] .
next
  show "totalp_on (range term.from_ground) less_kbo"
    using less_kbo_gtotal
    unfolding totalp_on_def Term.ground_vars_term_empty term.is_ground_iff_range_from_ground
    by (metis term.is_ground_iff_range_from_ground)
next
  fix
    c :: "('f, 'v) context" and
    t\<^sub>1 t\<^sub>2 :: "('f, 'v) term"
 
  assume "less_kbo t\<^sub>1 t\<^sub>2"

  then show "less_kbo c\<langle>t\<^sub>1\<rangle> c\<langle>t\<^sub>2\<rangle>"
    unfolding less_kbo_def
    by (rule KBO.S_ctxt)
next
  fix
    t\<^sub>1 t\<^sub>2 :: "('f, 'v) term" and
    \<gamma> :: "('f, 'v) subst"

  assume "less_kbo t\<^sub>1 t\<^sub>2"

  then show "less_kbo (t\<^sub>1 \<cdot> \<gamma>) (t\<^sub>2 \<cdot> \<gamma>)"
    by (rule less_kbo_subst)
next
  fix t and c :: "('f, 'v) context"
  assume "c \<noteq> \<box>"

  then show "less_kbo t c\<langle>t\<rangle>"
    unfolding less_kbo_def
    by (intro KBO.S_supt nectxt_imp_supt_ctxt)
qed

end
