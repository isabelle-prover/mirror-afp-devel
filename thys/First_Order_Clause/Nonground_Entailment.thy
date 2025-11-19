theory Nonground_Entailment
  imports
    Nonground_Context
    Nonground_Clause_With_Equality
    Ground_Term_Rewrite_System
    Entailment_Lifting
    Fold_Extra
begin

section \<open>Entailment\<close>

context nonground_clause
begin

lemma not_literal_entails [simp]:
  "\<not> upair ` I \<TTurnstile>l Neg a \<longleftrightarrow> upair ` I \<TTurnstile>l Pos a"
  "\<not> upair ` I \<TTurnstile>l Pos a \<longleftrightarrow> upair ` I \<TTurnstile>l Neg a"
  by auto

lemmas literal_entails_unfolds =
  not_literal_entails
  true_lit_simps

end

locale clause_entailment =
  nonground_clause where
  term_vars = "term_vars :: 't \<Rightarrow> 'v set" and term_to_ground = "term_to_ground :: 't \<Rightarrow> 't\<^sub>G" +

  nonground_term_with_context +

  ground_term_rewrite_system where
  apply_context = apply_ground_context and compose_context = compose_ground_context and
  hole = ground_hole +

  fixes I :: "'t\<^sub>G rel"
  assumes
    trans: "trans I" and
    sym: "sym I" and
    compatible_with_ground_context: "compatible_with_context I"
begin

lemma symmetric_context_congruence:
  assumes "(t, t') \<in> I"
  shows "(c\<langle>t\<rangle>\<^sub>G, t'') \<in> I \<longleftrightarrow> (c\<langle>t'\<rangle>\<^sub>G, t'') \<in> I"
  by (meson assms compatible_with_ground_context compatible_with_contextD sym trans symD transE)

lemma symmetric_upair_context_congruence:
  assumes "Upair t t' \<in> upair ` I"
  shows "Upair c\<langle>t\<rangle>\<^sub>G t'' \<in>  upair ` I \<longleftrightarrow> Upair c\<langle>t'\<rangle>\<^sub>G t'' \<in>  upair ` I"
  using assms uprod_mem_image_iff_prod_mem[OF sym] symmetric_context_congruence
  by simp

lemma upair_compatible_with_gctxtI [intro]:
  "Upair t t' \<in> upair ` I \<Longrightarrow> Upair c\<langle>t\<rangle>\<^sub>G c\<langle>t'\<rangle>\<^sub>G \<in> upair ` I"
  using compatible_with_ground_context
  unfolding compatible_with_context_def
  by (simp add: sym)

sublocale "term": symmetric_base_entailment where vars = "term.vars :: 't \<Rightarrow> 'v set" and
  comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and to_ground = term.to_ground and
  from_ground = term.from_ground
proof unfold_locales
  fix \<gamma> and t t' update x

  assume
    update_is_ground: "term.is_ground update" and
    var_grounding: "term.is_ground (x \<cdot>v \<gamma>)" and
    var_update: "(term.to_ground (x \<cdot>v \<gamma>), term.to_ground update) \<in> I" and
    term_grounding: "term.is_ground (t \<cdot>t \<gamma>)" and
    updated_term: "(term.to_ground (t \<cdot>t \<gamma>\<lbrakk>x := update\<rbrakk>), t') \<in> I"

  from term_grounding updated_term
  show "(term.to_ground (t \<cdot>t \<gamma>), t') \<in> I"
  proof (induction "occurences t x" arbitrary: t)
    case 0

    then have "x \<notin> term.vars t"
      using context.context_Var occurences
      by auto

    then have "t \<cdot>t \<gamma>\<lbrakk>x := update\<rbrakk> = t \<cdot>t \<gamma>"
      using term.subst_reduntant_upd
      by presburger

    with 0 show ?case
      by argo
  next
    case (Suc n)

    obtain c where t: "t = c\<langle>term.Var x\<rangle>"
      using Suc.hyps(2)
      by (metis context.context_Var vars_occurences zero_less_Suc)

    let ?t' = "c\<langle>update\<rangle>"

    have "(term.to_ground (?t' \<cdot>t \<gamma>), t') \<in> I"
    proof (rule Suc.hyps)
      show "n = occurences ?t' x"
        using Suc.hyps(2) occurences t update_is_ground 
        by auto
    next
      show "term.is_ground (?t' \<cdot>t \<gamma>)"
        using Suc.prems(1) t update_is_ground 
        by auto
    next
      show "(term.to_ground (?t' \<cdot>t \<gamma>\<lbrakk>x := update\<rbrakk>), t') \<in> I"
        using Suc.prems(2) update_is_ground
        unfolding t
        by auto
    qed

    then show ?case
      using symmetric_context_congruence update_is_ground var_update
      unfolding t
      by auto
  qed
qed (rule sym)

sublocale atom: symmetric_entailment where
  comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars and subst = "(\<cdot>a)" and
  vars = atom.vars and base_to_ground = term.to_ground and base_from_ground = term.from_ground and
  I = I and entails_def = "\<lambda>a. atom.to_ground a \<in> upair ` I"
proof unfold_locales
  fix a :: "'t atom" and \<gamma> x update P

  assume assms:
    "term.is_ground update"
    "term.is_ground (x \<cdot>v \<gamma>)"
    "(term.to_ground (x \<cdot>v \<gamma>), term.to_ground update) \<in> I"
    "atom.is_ground (a \<cdot>a \<gamma>)"
    "(atom.to_ground (a \<cdot>a \<gamma>\<lbrakk>x := update\<rbrakk>) \<in> upair ` I)"

  show "(atom.to_ground (a \<cdot>a \<gamma>) \<in> upair ` I)"
  proof(cases a)
    case (Upair t t')

    moreover have
      "(term.to_ground (t' \<cdot>t \<gamma>), term.to_ground (t \<cdot>t \<gamma>)) \<in> I \<longleftrightarrow>
       (term.to_ground (t \<cdot>t \<gamma>), term.to_ground (t' \<cdot>t \<gamma>)) \<in> I"
      by (metis local.sym symD)

    ultimately show ?thesis
      using assms
      unfolding atom.to_ground_def atom.subst_def atom.vars_def
      by(auto simp: sym term.simultaneous_congruence)
  qed
qed (simp_all add: sym)

sublocale literal: entailment_lifting_conj where
  comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars and sub_subst = "(\<cdot>a)" and
  sub_vars = atom.vars and base_to_ground = term.to_ground and
  base_from_ground = term.from_ground and I = I and sub_entails = atom.entails and
  map = "map_literal" and to_set = "set_literal" and is_negated = is_neg and
  entails_def = "\<lambda>l. upair ` I \<TTurnstile>l literal.to_ground l"
proof unfold_locales
  fix l :: "'t atom literal"

  show "(upair ` I \<TTurnstile>l literal.to_ground l) =
    (if is_neg l then Not else (\<lambda>x. x))
      (Finite_Set.fold (\<and>) True ((\<lambda>a. atom.to_ground a \<in> upair ` I) ` set_literal l))"
    unfolding literal.vars_def literal.to_ground_def
    by(cases l)(auto)

qed auto

sublocale clause: entailment_lifting_disj where
  comp_subst = "(\<odot>)" and base_subst = "(\<cdot>t)" and base_vars = term.vars and
  base_to_ground = term.to_ground and base_from_ground = term.from_ground and I = I and
  sub_subst = "(\<cdot>l)" and sub_vars = literal.vars and sub_entails = literal.entails and
  map = image_mset and to_set = set_mset and is_negated = "\<lambda>_. False" and
  entails_def = "\<lambda>C. upair ` I \<TTurnstile> clause.to_ground C"
proof unfold_locales
  fix C :: "'t clause"

  show "upair ` I \<TTurnstile> clause.to_ground C \<longleftrightarrow>
    (if False then Not else (\<lambda>x. x)) (Finite_Set.fold (\<or>) False (literal.entails ` set_mset C))"
    unfolding clause.to_ground_def
    by (induction C) auto

qed auto

lemma literal_compatible_with_gctxtI [intro]:
   "literal.entails (t \<approx> t') \<Longrightarrow> literal.entails (c\<langle>t\<rangle> \<approx> c\<langle>t'\<rangle>)"
  by (simp add: upair_compatible_with_gctxtI)

lemma symmetric_literal_context_congruence:
  assumes "Upair t t' \<in> upair ` I"
  shows
    "upair ` I \<TTurnstile>l c\<langle>t\<rangle>\<^sub>G \<approx> t'' \<longleftrightarrow> upair ` I \<TTurnstile>l c\<langle>t'\<rangle>\<^sub>G \<approx> t''"
    "upair ` I \<TTurnstile>l c\<langle>t\<rangle>\<^sub>G !\<approx> t'' \<longleftrightarrow> upair ` I \<TTurnstile>l c\<langle>t'\<rangle>\<^sub>G !\<approx> t''"
  using assms symmetric_upair_context_congruence
  by auto

end

end
