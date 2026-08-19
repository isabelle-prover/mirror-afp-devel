section \<open>Equality-saturation explanation certificates\<close>

theory Equality_Saturation_Checker
  imports
    First_Order_Rewriting.Trs
    First_Order_Terms.Term_Impl
begin

text \<open>
  This development deliberately reuses the first-order terms, substitutions,
  positions, and contexts from the AFP session
  \<^session>\<open>First_Order_Terms\<close>.  It uses the rewrite relation from
  \<^session>\<open>First_Order_Rewriting\<close>.  In particular, the semantic target of
  the checker is the existing conversion relation
  \<^term>\<open>(rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*\<close>; no separate term language or
  equational calculus is introduced here.

  What is specific to equality saturation is the certificate boundary.  A
  certificate is a flat path whose steps either apply a numbered input rule at
  an AFP position, or reuse a numbered equality recorded by an earlier checked
  e-class merge.  Recorded merges are concrete term equalities, as in an
  e-graph, and therefore need no substitution when reused.
\<close>

datatype direction = Forward | Backward

fun orient_pair :: "direction \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a" where
  "orient_pair Forward ab = ab"
| "orient_pair Backward (a, b) = (b, a)"

datatype ('f, 'v) certificate_step =
    Rule_At pos nat direction "('f, 'v) subst"
  | Merge_At pos nat direction

fun apply_step ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    ('f, 'v) certificate_step \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) term option" where
  "apply_step R \<Gamma> (Rule_At p i d \<sigma>) t =
     (if i < length R \<and> p \<in> poss t \<and>
          t |_ p = fst (orient_pair d (R ! i)) \<cdot> \<sigma>
      then Some (replace_at t p (snd (orient_pair d (R ! i)) \<cdot> \<sigma>))
      else None)"
| "apply_step R \<Gamma> (Merge_At p i d) t =
     (if i < length \<Gamma> \<and> p \<in> poss t \<and>
          t |_ p = fst (orient_pair d (\<Gamma> ! i))
      then Some (replace_at t p (snd (orient_pair d (\<Gamma> ! i))))
      else None)"

fun apply_steps ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    ('f, 'v) certificate_step list \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) term option" where
  "apply_steps R \<Gamma> [] t = Some t"
| "apply_steps R \<Gamma> (st # sts) t =
     (case apply_step R \<Gamma> st t of
        None \<Rightarrow> None
      | Some u \<Rightarrow> apply_steps R \<Gamma> sts u)"

definition check_explanation ::
  "('f, 'v) rule list \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    ('f, 'v) certificate_step list \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) term \<Rightarrow> bool" where
  "check_explanation R \<Gamma> sts t u \<longleftrightarrow>
     apply_steps R \<Gamma> sts t = Some u"

subsection \<open>Soundness in the AFP rewrite relation\<close>

lemma lift_conversion_at_position:
  assumes p: "p \<in> poss t"
    and sub: "t |_ p = s"
    and conv: "(s, u) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
  shows "(t, replace_at t p u) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  have "((ctxt_of_pos_term p t)\<langle>s\<rangle>,
         (ctxt_of_pos_term p t)\<langle>u\<rangle>) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule conversion_ctxt_closed[OF conv])
  moreover have "(ctxt_of_pos_term p t)\<langle>s\<rangle> = t"
    using ctxt_supt_id[OF p] sub by simp
  ultimately show ?thesis by simp
qed

lemma oriented_rule_conversion:
  assumes i: "i < length R"
  shows "(fst (orient_pair d (R ! i)) \<cdot> \<sigma>,
          snd (orient_pair d (R ! i)) \<cdot> \<sigma>)
         \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  obtain l r where lr: "R ! i = (l, r)" by (cases "R ! i")
  have "R ! i \<in> set R" by (rule nth_mem[OF i])
  then have mem: "(l, r) \<in> set R" using lr by simp
  have step: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep (set R)"
    by (rule rstep_subst[OF rstep_rule[OF mem]])
  show ?thesis
  proof (cases d)
    case Forward
    with lr step show ?thesis
      unfolding conversion_def by auto
  next
    case Backward
    with lr step show ?thesis
      unfolding conversion_def by auto
  qed
qed

lemma apply_step_sound:
  assumes merges:
    "\<forall>ab \<in> set \<Gamma>. (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and step: "apply_step R \<Gamma> st t = Some u"
  shows "(t, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
proof (cases st)
  case (Rule_At p i d \<sigma>)
  from step Rule_At have i: "i < length R" and p: "p \<in> poss t"
    and sub: "t |_ p = fst (orient_pair d (R ! i)) \<cdot> \<sigma>"
    and u: "u = replace_at t p (snd (orient_pair d (R ! i)) \<cdot> \<sigma>)"
    by (auto split: if_splits)
  have "(fst (orient_pair d (R ! i)) \<cdot> \<sigma>,
         snd (orient_pair d (R ! i)) \<cdot> \<sigma>)
        \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule oriented_rule_conversion[OF i])
  from lift_conversion_at_position[OF p sub this] u show ?thesis by simp
next
  case (Merge_At p i d)
  from step Merge_At have i: "i < length \<Gamma>" and p: "p \<in> poss t"
    and sub: "t |_ p = fst (orient_pair d (\<Gamma> ! i))"
    and u: "u = replace_at t p (snd (orient_pair d (\<Gamma> ! i)))"
    by (auto split: if_splits)
  have mem: "\<Gamma> ! i \<in> set \<Gamma>" by (rule nth_mem[OF i])
  obtain a b where ab: "\<Gamma> ! i = (a, b)" by (cases "\<Gamma> ! i")
  have base:
    "(a, b) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    using merges mem ab by fastforce
  have oriented:
    "(fst (orient_pair d (\<Gamma> ! i)), snd (orient_pair d (\<Gamma> ! i)))
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  proof (cases d)
    case Forward
    with base ab show ?thesis by simp
  next
    case Backward
    have "(b, a) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
      using base
      by (rule conversion_sym[unfolded sym_def, rule_format])
    with Backward ab show ?thesis by simp
  qed
  from lift_conversion_at_position[OF p sub oriented] u show ?thesis by simp
qed

lemma apply_steps_sound:
  assumes merges:
    "\<forall>ab \<in> set \<Gamma>. (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and run: "apply_steps R \<Gamma> sts t = Some u"
  shows "(t, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  using run
proof (induction sts arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons st sts)
  from Cons.prems obtain v where
    first: "apply_step R \<Gamma> st t = Some v" and
    rest: "apply_steps R \<Gamma> sts v = Some u"
    by (auto split: option.splits)
  have tv: "(t, v) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule apply_step_sound[OF merges first])
  have vu: "(v, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule Cons.IH[OF rest])
  from tv vu show ?case
    unfolding conversion_def by (rule rtrancl_trans)
qed

theorem check_explanation_sound:
  assumes "\<forall>ab \<in> set \<Gamma>.
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and "check_explanation R \<Gamma> sts t u"
  shows "(t, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  using apply_steps_sound[OF assms(1) assms(2)[unfolded check_explanation_def]] .

corollary check_rule_explanation_sound:
  assumes "check_explanation R [] sts t u"
  shows "(t, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  by (rule check_explanation_sound[OF _ assms]) simp

end
