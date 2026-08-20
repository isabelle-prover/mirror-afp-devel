section \<open>Certified acyclic e-graphs\<close>

theory Certified_Acyclic_EGraph
  imports Acyclic_EGraph_Extraction
begin

text \<open>
  The dynamic program establishes global optimality over the represented terms
  of an acyclic e-class DAG.  This theory additionally checks that every e-node
  in a class is equal to a canonical e-node for that class.

  Canonical terms are built bottom-up from the first e-node of every class.
  The certificate list for a class is aligned with its e-node list; each flat
  explanation must transform the canonical term into the corresponding e-node
  instantiated with canonical child terms.  Congruence of AFP conversions then
  extends these finite certificates to every recursive combination represented
  by the DAG.
\<close>

type_synonym 'f dag_class_certificates =
  "('f, unit) certificate_step list list"

type_synonym 'f dag_certificates =
  "'f dag_class_certificates list"

fun canonical_prefix ::
  "'f acyclic_egraph \<Rightarrow> nat \<Rightarrow> ('f, unit) term list"
  where
  "canonical_prefix G 0 = []"
| "canonical_prefix G (Suc i) =
    (let memo = canonical_prefix G i
     in memo @ [instantiate_enode memo (hd (G ! i))])"

definition canonical_eclass ::
  "'f acyclic_egraph \<Rightarrow> nat \<Rightarrow> ('f, unit) term option"
  where
  "canonical_eclass G i =
    (if wf_acyclic_egraph G \<and> i < length G
     then Some (canonical_prefix G (length G) ! i)
     else None)"

definition check_dag_class ::
  "('f, unit) rule list \<Rightarrow> ('f, unit) term list \<Rightarrow>
    'f dag_eclass \<Rightarrow> 'f dag_class_certificates \<Rightarrow> bool"
  where
  "check_dag_class R memo cls certs \<longleftrightarrow>
    cls \<noteq> [] \<and>
    list_all2
      (\<lambda>node sts.
        check_explanation R [] sts
          (instantiate_enode memo (hd cls))
          (instantiate_enode memo node))
      cls certs"

definition check_certified_egraph ::
  "('f, unit) rule list \<Rightarrow> 'f acyclic_egraph \<Rightarrow>
    'f dag_certificates \<Rightarrow> bool"
  where
  "check_certified_egraph R G certs \<longleftrightarrow>
    wf_acyclic_egraph G \<and>
    length certs = length G \<and>
    list_all
      (\<lambda>i. check_dag_class R (canonical_prefix G i)
        (G ! i) (certs ! i))
      [0..<length G]"

lemma canonical_prefix_length [simp]:
  "length (canonical_prefix G n) = n"
  by (induction n) (simp_all add: Let_def)

lemma canonical_prefix_nth_stable:
  assumes "j < n"
  shows "canonical_prefix G n ! j = canonical_prefix G (Suc j) ! j"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "j = n")
    case True
    then show ?thesis by simp
  next
    case False
    with Suc.prems have jn: "j < n" by simp
    then have "j < length (canonical_prefix G n)" by simp
    then have "canonical_prefix G (Suc n) ! j = canonical_prefix G n ! j"
      unfolding canonical_prefix.simps Let_def
      by (rule nth_append_left)
    also have "\<dots> = canonical_prefix G (Suc j) ! j"
      by (rule Suc.IH[OF jn])
    finally show ?thesis .
  qed
qed

lemma canonical_prefix_step:
  "canonical_prefix G (Suc i) ! i =
    instantiate_enode (canonical_prefix G i) (hd (G ! i))"
proof -
  let ?memo = "canonical_prefix G i"
  have len: "i = length ?memo" by simp
  have "(?memo @ [instantiate_enode ?memo (hd (G ! i))]) ! i =
      instantiate_enode ?memo (hd (G ! i))"
    using len by (metis nth_append_length)
  then show ?thesis by (simp add: Let_def)
qed

lemma checked_egraph_wf:
  "check_certified_egraph R G certs \<Longrightarrow> wf_acyclic_egraph G"
  unfolding check_certified_egraph_def by simp

lemma checked_dag_class_at:
  assumes checked: "check_certified_egraph R G certs"
    and i: "i < length G"
  shows "check_dag_class R (canonical_prefix G i)
    (G ! i) (certs ! i)"
  using checked i
  unfolding check_certified_egraph_def
  by (auto simp: list_all_iff)

lemma check_dag_class_certificate:
  assumes checked: "check_dag_class R memo cls certs"
    and node: "node \<in> set cls"
  obtains sts where
    "check_explanation R [] sts
      (instantiate_enode memo (hd cls))
      (instantiate_enode memo node)"
proof -
  from node obtain n where n: "n < length cls" and nth: "cls ! n = node"
    unfolding set_conv_nth by blast
  from checked have related:
    "list_all2
      (\<lambda>node sts.
        check_explanation R [] sts
          (instantiate_enode memo (hd cls))
          (instantiate_enode memo node))
      cls certs"
    unfolding check_dag_class_def by simp
  from list_all2_nthD[OF related n] nth have
    "check_explanation R [] (certs ! n)
      (instantiate_enode memo (hd cls))
      (instantiate_enode memo node)"
    by simp
  from that[OF this] show thesis .
qed

lemma conversion_Fun_list_all2:
  assumes
    "list_all2
      (\<lambda>s t. (s, t) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*) ss ts"
  shows "(Fun f ss, Fun f ts) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*"
proof (rule all_ctxt_closedD[OF all_ctxt_closed_rstep_conversion])
  show "(f, length ts) \<in> UNIV" by simp
  show "length ss = length ts"
    using list_all2_lengthD[OF assms] .
  fix i
  assume "i < length ss"
  from list_all2_nthD[OF assms this]
  show "(ss ! i, ts ! i) \<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" .
qed auto

theorem checked_egraph_representation_sound:
  assumes checked: "check_certified_egraph R G certs"
    and i: "i < length G"
    and represented: "represents_eclass G i t"
  shows "(canonical_prefix G (Suc i) ! i, t)
    \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  using i represented
proof (induction i arbitrary: t rule: less_induct)
  case (less i)
  let ?memo = "canonical_prefix G i"
  let ?cls = "G ! i"
  from less.prems(2) obtain f children ts where
    t: "t = Fun f ts" and node: "(f, children) \<in> set ?cls" and
    related: "list_all2 (represents_eclass G) children ts"
    using less.prems(1) by (cases rule: represents_eclass.cases) auto
  have wf: "wf_acyclic_egraph G"
    by (rule checked_egraph_wf[OF checked])
  have children_lt: "\<forall>j \<in> set children. j < i"
    using wf less.prems(1) node unfolding wf_acyclic_egraph_def by auto
  have canonical_children:
    "list_all2
      (\<lambda>s u. (s, u) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*)
      (map ((!) ?memo) children) ts"
  proof (rule list_all2_all_nthI)
    show "length (map ((!) ?memo) children) = length ts"
      using list_all2_lengthD[OF related] by simp
    fix n
    assume n: "n < length (map ((!) ?memo) children)"
    then have nc: "n < length children" by simp
    let ?j = "children ! n"
    have j_mem: "?j \<in> set children" using nc by simp
    with children_lt have ji: "?j < i" by blast
    with less.prems(1) have jG: "?j < length G" by simp
    have child_rep: "represents_eclass G ?j (ts ! n)"
      using list_all2_nthD[OF related nc] .
    have conv:
      "(canonical_prefix G (Suc ?j) ! ?j, ts ! n)
        \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
      by (rule less.IH[OF ji jG child_rep])
    have "?memo ! ?j = canonical_prefix G (Suc ?j) ! ?j"
      by (rule canonical_prefix_nth_stable[OF ji])
    with conv show
      "(map ((!) ?memo) children ! n, ts ! n)
        \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
      using nc by simp
  qed
  have node_to_term:
    "(instantiate_enode ?memo (f, children), t)
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
  proof -
    have "(Fun f (map ((!) ?memo) children), Fun f ts)
        \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
      by (rule conversion_Fun_list_all2[OF canonical_children])
    then show ?thesis
      using t unfolding instantiate_enode_def by simp
  qed
  have class_checked:
    "check_dag_class R ?memo ?cls (certs ! i)"
    by (rule checked_dag_class_at[OF checked less.prems(1)])
  from check_dag_class_certificate[OF class_checked node]
  obtain sts where cert:
    "check_explanation R [] sts
      (instantiate_enode ?memo (hd ?cls))
      (instantiate_enode ?memo (f, children))" .
  have class_to_node:
    "(instantiate_enode ?memo (hd ?cls),
      instantiate_enode ?memo (f, children))
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule check_rule_explanation_sound[OF cert])
  from class_to_node node_to_term have
    "(instantiate_enode ?memo (hd ?cls), t)
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding conversion_def by (rule rtrancl_trans)
  then show ?case unfolding canonical_prefix_step .
qed

theorem checked_egraph_eclass_sound:
  assumes checked: "check_certified_egraph R G certs"
    and i: "i < length G"
    and s: "represents_eclass G i s"
    and t: "represents_eclass G i t"
  shows "(s, t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  have source_s:
    "(canonical_prefix G (Suc i) ! i, s)
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule checked_egraph_representation_sound[OF checked i s])
  have source_t:
    "(canonical_prefix G (Suc i) ! i, t)
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule checked_egraph_representation_sound[OF checked i t])
  have s_source:
    "(s, canonical_prefix G (Suc i) ! i)
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    using source_s
    by (rule conversion_sym[unfolded sym_def, rule_format])
  from s_source source_t show ?thesis
    unfolding conversion_def by (rule rtrancl_trans)
qed

theorem certified_egraph_extraction_correct:
  assumes checked: "check_certified_egraph R G certs"
    and i: "i < length G"
  obtains source chosen where
    "canonical_eclass G i = Some source"
    "extract_eclass w G i = Some chosen"
    "(source, chosen) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    "represents_eclass G i chosen"
    "\<And>u. represents_eclass G i u \<Longrightarrow>
      term_cost w chosen \<le> term_cost w u"
proof -
  have wf: "wf_acyclic_egraph G"
    by (rule checked_egraph_wf[OF checked])
  let ?source = "canonical_prefix G (length G) ! i"
  from extract_eclass_global_minimum[OF wf i, of w]
  obtain chosen where
    extracted: "extract_eclass w G i = Some chosen" and
    represented: "represents_eclass G i chosen" and
    minimal: "\<And>u. represents_eclass G i u \<Longrightarrow>
      term_cost w chosen \<le> term_cost w u"
    by blast
  have source: "canonical_eclass G i = Some ?source"
    using wf i unfolding canonical_eclass_def by simp
  have stable:
    "?source = canonical_prefix G (Suc i) ! i"
    by (rule canonical_prefix_nth_stable[OF i])
  have sound:
    "(?source, chosen) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    unfolding stable
    by (rule checked_egraph_representation_sound[
          OF checked i represented])
  from that[OF source extracted sound represented minimal] show thesis .
qed

end
