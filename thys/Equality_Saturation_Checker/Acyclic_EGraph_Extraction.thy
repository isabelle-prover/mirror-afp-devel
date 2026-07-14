section \<open>Acyclic e-graph extraction\<close>

theory Acyclic_EGraph_Extraction
  imports Extraction_Certificates
begin

text \<open>
  A finite acyclic e-graph is represented by a list of e-classes in
  topological order.  An e-node consists of a function symbol and indexes of
  child classes.  Every child index must be smaller than the index of the
  containing class.  Thus the list representation is both finite and a
  certificate of acyclicity.  E-graph expressions are ground terms; atoms such
  as source-language variables are represented by nullary function symbols, as
  in egg's recursive-expression format.

  The represented terms of a class include every e-node in that class and
  every combination of terms represented by its child classes.  Extraction
  below is a bottom-up dynamic program: after finding an optimum for each
  earlier class, it instantiates every e-node with those optima and retains a
  minimum-cost result.
\<close>

type_synonym 'f dag_enode = "'f \<times> nat list"
type_synonym 'f dag_eclass = "'f dag_enode list"
type_synonym 'f acyclic_egraph = "'f dag_eclass list"

definition wf_acyclic_egraph :: "'f acyclic_egraph \<Rightarrow> bool" where
  "wf_acyclic_egraph G \<longleftrightarrow>
    (\<forall>i < length G.
      G ! i \<noteq> [] \<and>
      (\<forall>node \<in> set (G ! i). \<forall>j \<in> set (snd node). j < i))"

inductive represents_eclass ::
  "'f acyclic_egraph \<Rightarrow> nat \<Rightarrow> ('f, unit) term \<Rightarrow> bool"
  for G where
  represents_node:
    "i < length G \<Longrightarrow>
     (f, children) \<in> set (G ! i) \<Longrightarrow>
     list_all2 (represents_eclass G) children ts \<Longrightarrow>
     represents_eclass G i (Fun f ts)"

definition instantiate_enode ::
  "('f, unit) term list \<Rightarrow> 'f dag_enode \<Rightarrow> ('f, unit) term"
  where
  "instantiate_enode memo node =
    Fun (fst node) (map ((!) memo) (snd node))"

definition best_eclass_term ::
  "('f \<Rightarrow> nat) \<Rightarrow> ('f, unit) term list \<Rightarrow>
    'f dag_eclass \<Rightarrow> ('f, unit) term"
  where
  "best_eclass_term w memo cls =
    instantiate_enode memo
      (arg_min_list (term_cost w \<circ> instantiate_enode memo) cls)"

fun extract_prefix ::
  "('f \<Rightarrow> nat) \<Rightarrow> 'f acyclic_egraph \<Rightarrow> nat \<Rightarrow>
    ('f, unit) term list"
  where
  "extract_prefix w G 0 = []"
| "extract_prefix w G (Suc i) =
    (let memo = extract_prefix w G i
     in memo @ [best_eclass_term w memo (G ! i)])"

definition extract_egraph ::
  "('f \<Rightarrow> nat) \<Rightarrow> 'f acyclic_egraph \<Rightarrow>
    ('f, unit) term list option"
  where
  "extract_egraph w G =
    (if wf_acyclic_egraph G
     then Some (extract_prefix w G (length G))
     else None)"

definition extract_eclass ::
  "('f \<Rightarrow> nat) \<Rightarrow> 'f acyclic_egraph \<Rightarrow> nat \<Rightarrow>
    ('f, unit) term option"
  where
  "extract_eclass w G i =
    (if wf_acyclic_egraph G \<and> i < length G
     then Some (extract_prefix w G (length G) ! i)
     else None)"

lemma extract_prefix_length [simp]:
  "length (extract_prefix w G n) = n"
  by (induction n) (simp_all add: Let_def)

lemma extract_prefix_nth_stable:
  assumes "j < n"
  shows "extract_prefix w G n ! j = extract_prefix w G (Suc j) ! j"
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
    with Suc.prems have "j < n" by simp
    then have "j < length (extract_prefix w G n)" by simp
    then have "extract_prefix w G (Suc n) ! j = extract_prefix w G n ! j"
      unfolding extract_prefix.simps Let_def
      by (rule nth_append_left)
    also have "\<dots> = extract_prefix w G (Suc j) ! j"
      by (rule Suc.IH[OF \<open>j < n\<close>])
    finally show ?thesis .
  qed
qed

lemma arg_min_list_le:
  fixes score :: "'a \<Rightarrow> nat"
  assumes "xs \<noteq> []" and "x \<in> set xs"
  shows "score (arg_min_list score xs) \<le> score x"
proof -
  have "score (arg_min_list score xs) = Min (score ` set xs)"
    by (rule f_arg_min_list_f[OF assms(1)])
  also have "\<dots> \<le> score x"
    by (rule Min_le) (use assms in auto)
  finally show ?thesis .
qed

lemma sum_list_mono_list_all2:
  fixes xs ys :: "nat list"
  assumes "list_all2 (\<le>) xs ys"
  shows "sum_list xs \<le> sum_list ys"
  using assms by (induction rule: list_all2_induct) simp_all

lemma finite_list_all2_fibres:
  assumes "\<forall>x \<in> set xs. finite {y. P x y}"
  shows "finite {ys. list_all2 P xs ys}"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "{ys. list_all2 P (x # xs) ys} =
      (\<lambda>(y, ys). y # ys) ` ({y. P x y} \<times> {ys. list_all2 P xs ys})"
    by (auto simp: list_all2_Cons1)
  moreover have "finite ({y. P x y} \<times> {ys. list_all2 P xs ys})"
    using Cons by auto
  ultimately show ?case by simp
qed

theorem represented_eclass_finite:
  assumes wf: "wf_acyclic_egraph G" and i: "i < length G"
  shows "finite {t. represents_eclass G i t}"
proof -
  have finite_at:
    "k < length G \<Longrightarrow> finite {t. represents_eclass G k t}" for k
  proof (induction k rule: less_induct)
    case (less k)
    have class_wf:
      "G ! k \<noteq> [] \<and>
        (\<forall>node \<in> set (G ! k). \<forall>j \<in> set (snd node). j < k)"
      using wf less.prems unfolding wf_acyclic_egraph_def by blast
    have fibres:
      "finite {ts. list_all2 (represents_eclass G) children ts}"
      if node: "(f, children) \<in> set (G ! k)" for f children
    proof (rule finite_list_all2_fibres)
      show "\<forall>j \<in> set children. finite {t. represents_eclass G j t}"
      proof (intro ballI)
        fix j
        assume "j \<in> set children"
        with class_wf node have jk: "j < k" by auto
        with less.prems have "j < length G" by simp
        from less.IH[OF jk this] show "finite {t. represents_eclass G j t}" .
      qed
    qed
    have represented_union:
      "{t. represents_eclass G k t} =
        (\<Union>(f, children) \<in> set (G ! k).
          Fun f ` {ts. list_all2 (represents_eclass G) children ts})"
    proof (rule set_eqI, rule iffI)
      fix t
      assume "t \<in> {t. represents_eclass G k t}"
      then have rep: "represents_eclass G k t" by simp
      from rep obtain f children ts where
        t: "t = Fun f ts" and node: "(f, children) \<in> set (G ! k)" and
        related: "list_all2 (represents_eclass G) children ts"
        by (cases rule: represents_eclass.cases) auto
      from t node related show
        "t \<in> (\<Union>(f, children) \<in> set (G ! k).
          Fun f ` {ts. list_all2 (represents_eclass G) children ts})"
        by auto
    next
      fix t
      assume
        "t \<in> (\<Union>(f, children) \<in> set (G ! k).
          Fun f ` {ts. list_all2 (represents_eclass G) children ts})"
      then obtain f children ts where
        node: "(f, children) \<in> set (G ! k)" and
        related: "list_all2 (represents_eclass G) children ts" and
        t: "t = Fun f ts"
        by auto
      show "t \<in> {t. represents_eclass G k t}"
        using represents_eclass.represents_node[OF less.prems node related] t
        by simp
    qed
    show ?case unfolding represented_union using fibres by auto
  qed
  from finite_at[OF i] show ?thesis .
qed

lemma best_eclass_term_in:
  assumes "cls \<noteq> []"
  shows "best_eclass_term w memo cls
    = instantiate_enode memo
        (arg_min_list (term_cost w \<circ> instantiate_enode memo) cls)"
    and "arg_min_list (term_cost w \<circ> instantiate_enode memo) cls
      \<in> set cls"
  using assms unfolding best_eclass_term_def
  by (simp_all add: arg_min_list_in)

theorem extract_prefix_optimal:
  assumes wf: "wf_acyclic_egraph G" and i: "i < length G"
  shows
    "represents_eclass G i (extract_prefix w G (Suc i) ! i)"
    "\<And>t. represents_eclass G i t \<Longrightarrow>
      term_cost w (extract_prefix w G (Suc i) ! i) \<le> term_cost w t"
proof -
  have correct:
    "k < length G \<Longrightarrow>
      represents_eclass G k (extract_prefix w G (Suc k) ! k) \<and>
      (\<forall>t. represents_eclass G k t \<longrightarrow>
        term_cost w (extract_prefix w G (Suc k) ! k) \<le> term_cost w t)"
    for k
  proof (induction k rule: less_induct)
    case (less k)
    let ?memo = "extract_prefix w G k"
    let ?cls = "G ! k"
    let ?score = "term_cost w \<circ> instantiate_enode ?memo"
    let ?best = "arg_min_list ?score ?cls"
    have class_wf:
      "?cls \<noteq> [] \<and>
        (\<forall>node \<in> set ?cls. \<forall>j \<in> set (snd node). j < k)"
      using wf less.prems unfolding wf_acyclic_egraph_def by blast
    have best_mem: "?best \<in> set ?cls"
      by (rule arg_min_list_in[OF class_wf[THEN conjunct1]])
    obtain f children where best: "?best = (f, children)"
      by (cases ?best)
    have children_lt: "\<forall>j \<in> set children. j < k"
      using class_wf best_mem best by auto
    have child_rep:
      "list_all2 (represents_eclass G) children
        (map ((!) ?memo) children)"
    proof (rule list_all2_all_nthI)
      show "length children = length (map ((!) ?memo) children)" by simp
      fix n
      assume n: "n < length children"
      let ?j = "children ! n"
      have j_mem: "?j \<in> set children" using n by simp
      with children_lt have jk: "?j < k" by blast
      with less.prems have jG: "?j < length G" by simp
      have rep:
        "represents_eclass G ?j (extract_prefix w G (Suc ?j) ! ?j)"
        using less.IH[OF jk jG] by blast
      have "?memo ! ?j = extract_prefix w G (Suc ?j) ! ?j"
        by (rule extract_prefix_nth_stable[OF jk])
      with rep show
        "represents_eclass G (children ! n)
          (map ((!) ?memo) children ! n)"
        using n by simp
    qed
    have chosen:
      "extract_prefix w G (Suc k) ! k = instantiate_enode ?memo ?best"
    proof -
      have len: "k = length ?memo" by simp
      have "(?memo @ [instantiate_enode ?memo ?best]) ! k =
          instantiate_enode ?memo ?best"
        using len by (metis nth_append_length)
      then show ?thesis by (simp add: Let_def best_eclass_term_def)
    qed
    have rep:
      "represents_eclass G k (extract_prefix w G (Suc k) ! k)"
    proof -
      have node_best: "(f, children) \<in> set ?cls"
        using best_mem best by simp
      have "represents_eclass G k
          (Fun f (map ((!) ?memo) children))"
        by (rule represents_eclass.represents_node[
              OF less.prems node_best child_rep])
      then show ?thesis
        using chosen best unfolding instantiate_enode_def by simp
    qed
    have minimal:
      "term_cost w (extract_prefix w G (Suc k) ! k) \<le> term_cost w t"
      if t: "represents_eclass G k t" for t
    proof -
      from t obtain g cs ts where
        t_eq: "t = Fun g ts" and node: "(g, cs) \<in> set ?cls" and
        related: "list_all2 (represents_eclass G) cs ts"
        using less.prems by (cases rule: represents_eclass.cases) auto
      have candidate_le:
        "term_cost w (instantiate_enode ?memo ?best)
          \<le> term_cost w (instantiate_enode ?memo (g, cs))"
        using arg_min_list_le[OF class_wf[THEN conjunct1] node, of ?score]
        by simp
      have child_costs:
        "list_all2 (\<le>)
          (map (term_cost w) (map ((!) ?memo) cs))
          (map (term_cost w) ts)"
      proof (rule list_all2_all_nthI)
        show "length (map (term_cost w) (map ((!) ?memo) cs))
            = length (map (term_cost w) ts)"
          using list_all2_lengthD[OF related] by simp
        fix n
        assume n: "n < length (map (term_cost w) (map ((!) ?memo) cs))"
        then have ncs: "n < length cs" by simp
        let ?j = "cs ! n"
        have j_mem: "?j \<in> set cs" using ncs by simp
        from class_wf node j_mem have jk: "?j < k" by auto
        with less.prems have jG: "?j < length G" by simp
        have rep_child: "represents_eclass G ?j (ts ! n)"
          using list_all2_nthD[OF related ncs] .
        have le:
          "term_cost w (extract_prefix w G (Suc ?j) ! ?j)
            \<le> term_cost w (ts ! n)"
          using less.IH[OF jk jG] rep_child by blast
        have "?memo ! ?j = extract_prefix w G (Suc ?j) ! ?j"
          by (rule extract_prefix_nth_stable[OF jk])
        with le show
          "map (term_cost w) (map ((!) ?memo) cs) ! n
            \<le> map (term_cost w) ts ! n"
          using ncs list_all2_lengthD[OF related] by simp
      qed
      have instantiated_le:
        "term_cost w (instantiate_enode ?memo (g, cs)) \<le> term_cost w t"
        using sum_list_mono_list_all2[OF child_costs]
        unfolding instantiate_enode_def t_eq by simp
      from candidate_le instantiated_le show ?thesis
        unfolding chosen by simp
    qed
    show ?case using rep minimal by blast
  qed
  from correct[OF i] show
    "represents_eclass G i (extract_prefix w G (Suc i) ! i)" by blast
  from correct[OF i] show
    "term_cost w (extract_prefix w G (Suc i) ! i) \<le> term_cost w t"
    if "represents_eclass G i t" for t
    using that by blast
qed

theorem extract_eclass_global_minimum:
  assumes wf: "wf_acyclic_egraph G" and i: "i < length G"
  obtains t where
    "extract_eclass w G i = Some t"
    "represents_eclass G i t"
    "\<And>u. represents_eclass G i u \<Longrightarrow>
      term_cost w t \<le> term_cost w u"
proof -
  let ?t = "extract_prefix w G (length G) ! i"
  have stable:
    "?t = extract_prefix w G (Suc i) ! i"
    by (rule extract_prefix_nth_stable[OF i])
  have extracted: "extract_eclass w G i = Some ?t"
    using wf i unfolding extract_eclass_def by simp
  have represented: "represents_eclass G i ?t"
    unfolding stable by (rule extract_prefix_optimal(1)[OF wf i])
  have minimal:
    "term_cost w ?t \<le> term_cost w u"
    if "represents_eclass G i u" for u
    unfolding stable by (rule extract_prefix_optimal(2)[OF wf i that])
  from that[OF extracted represented minimal] show thesis .
qed

end
