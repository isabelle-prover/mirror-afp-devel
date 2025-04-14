section\<open>Labels and Overlaps\<close>

theory Labels_and_Overlaps
imports
  Orthogonal_PT 
  Well_Quasi_Orders.Almost_Full_Relations
begin

subsection\<open>Labeled Proof Terms\<close>

text\<open>The idea is to label function symbols in the source of a proof term that are affected by
a rule symbol @{term \<alpha>} with @{term \<alpha>} and the distance from the root to @{term \<alpha>}.
Therefore, a label is a pair consisting of a rule symbol and a natural number, or it can be 
@{term None}.
A labeled term is a term, where each function symbol additionally has a label associated with it.\<close>
type_synonym
  ('f, 'v) label = "(('f, 'v) prule \<times> nat) option"
type_synonym
  ('f, 'v) term_lab = "('f \<times> ('f, 'v) label, 'v) term"

fun label_term :: "('f, 'v) prule \<Rightarrow> nat \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term_lab"
  where
  "label_term \<alpha> i (Var x) = Var x"
| "label_term \<alpha> i (Fun f ts) = Fun (f, Some (\<alpha>, i)) (map (label_term \<alpha> (i+1)) ts)"

abbreviation labeled_lhs :: "('f, 'v) prule \<Rightarrow> ('f, 'v) term_lab"
  where "labeled_lhs \<alpha> \<equiv> label_term \<alpha> 0 (lhs \<alpha>)"

fun labeled_source :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) term_lab"
  where
  "labeled_source (Var x) = Var x"
| "labeled_source (Pfun f As) = Fun (f, None) (map labeled_source As)"
| "labeled_source (Prule \<alpha> As) = (labeled_lhs \<alpha>) \<cdot> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha>"

fun term_lab_to_term :: "('f, 'v) term_lab \<Rightarrow> ('f, 'v) term"
  where
  "term_lab_to_term (Var x) = Var x"
| "term_lab_to_term (Fun f ts) = Fun (fst f) (map term_lab_to_term ts)"

fun term_to_term_lab :: "('f, 'v) term \<Rightarrow> ('f, 'v) term_lab"
  where
  "term_to_term_lab (Var x) = Var x"
| "term_to_term_lab (Fun f ts) = Fun (f, None) (map term_to_term_lab ts)"

fun get_label :: "('f, 'v) term_lab \<Rightarrow> ('f, 'v) label"
  where
  "get_label (Var x) = None"
| "get_label (Fun f ts) = snd f"

fun labelposs :: "('f, 'v) term_lab \<Rightarrow> pos set"
where
   "labelposs (Var x) = {}"
 | "labelposs (Fun (f, None) ts) = (\<Union>i<length ts. {i # p | p. p \<in> labelposs (ts ! i)})"
 | "labelposs (Fun (f, Some l) ts) = {[]} \<union> (\<Union>i<length ts. {i # p | p. p \<in> labelposs (ts ! i)})"

abbreviation possL :: "('f, 'v) pterm \<Rightarrow> pos set"
  where "possL A \<equiv> labelposs (labeled_source A)"

lemma labelposs_term_to_term_lab: "labelposs (term_to_term_lab t) = {}"
  by(induct t) simp_all

lemma term_lab_to_term_lab[simp]: "term_lab_to_term (term_to_term_lab t) = t"
proof(induct t)
  case (Fun f ts)
  then show ?case
    unfolding term_lab_to_term.simps term_to_term_lab.simps fst_conv by (simp add: map_nth_eq_conv)
qed simp

lemma term_lab_to_term_subt_at:
  assumes "p \<in> poss t"
  shows "term_lab_to_term t |_p = term_lab_to_term (t|_p)"
  using assms proof(induct p arbitrary:t)
  case (Cons i p)
  from args_poss[OF Cons(2)] obtain f ts where f:"t = Fun f ts" and 
    p:"p \<in> poss (ts ! i)" and i:"i < length ts" by blast 
  from Cons(1)[OF p] i show ?case
    unfolding f term_lab_to_term.simps by simp
qed simp

lemma vars_term_labeled_lhs: "vars_term (label_term \<alpha> i t) = vars_term t"
  by (induct t arbitrary:i) simp_all

lemma vars_term_list_labeled_lhs: "vars_term_list (label_term \<alpha> i t) = vars_term_list t"
proof (induct t arbitrary:i)
  case (Fun f ts)
  show ?case unfolding label_term.simps vars_term_list.simps using Fun
    by (metis (mono_tags, lifting) length_map map_nth_eq_conv nth_mem)
qed (simp add: vars_term_list.simps(1))

lemma var_poss_list_labeled_lhs: "var_poss_list (label_term \<alpha> i t) = var_poss_list t"
proof (induct t arbitrary:i)
  case (Fun f ts)
  then have ts:"map (var_poss_list \<circ> label_term \<alpha> (i + 1)) ts = map var_poss_list ts"
    by auto
  then show ?case
    unfolding label_term.simps var_poss_list.simps map_map ts by simp
qed (simp add: poss_list.simps(1))

lemma var_labeled_lhs[simp]: "vars_distinct (label_term \<alpha> i t) = vars_distinct t"
  by (simp add: vars_term_list_labeled_lhs)

lemma labelposs_subt_at:
  assumes "q \<in> poss t" "p \<in> labelposs (t|_q)"
  shows "q@p \<in> labelposs t"
  using assms proof(induct t arbitrary:q)
  case (Fun f ts)
  then show ?case proof(cases q)
    case (Cons i q')
    with Fun(2) have i:"i < length ts" and q':"q' \<in> poss (ts!i)"
      by simp+
    with Fun(3) have "p \<in> labelposs ((ts!i)|_q')"
      unfolding Cons by simp
    with Fun(1) i q' have IH:"q'@p \<in> labelposs (ts!i)"
      using nth_mem by blast
    obtain f' lab where f:"f = (f', lab)"
      by fastforce
    then show ?thesis proof(cases lab)
      case None
      show ?thesis
        unfolding f Cons None labelposs.simps using i IH by simp
    next
      case (Some a)
      then show ?thesis
        unfolding f Cons Some labelposs.simps using i IH by simp
    qed
  qed simp
qed simp

lemma var_label_term:
  assumes "p \<in> poss t" and "t|_p = Var x"
  shows "label_term \<alpha> n t |_p = Var x"
  using assms proof(induct t arbitrary:p n)
  case (Fun f ts)
  then obtain i p' where p':"i < length ts" "p = i#p'" "p' \<in> poss (ts!i)"
    by auto
  then show ?case
    unfolding label_term.simps p'(2) subt_at.simps using Fun(1,3) p'(2) by force
qed simp

lemma get_label_label_term: 
  assumes "p \<in> fun_poss t"
  shows "get_label (label_term \<alpha> n t|_p) = Some (\<alpha>, n + size p)" 
  using assms proof(induct t arbitrary: n p)
  case (Fun f ts)
  show ?case proof(cases p)
    case (Cons i p')
    with Fun(2) have i:"i < length ts" and p':"p' \<in> fun_poss (ts!i)" by simp+
    with Fun(1) have "get_label (label_term \<alpha> (n+1) (ts!i) |_ p') = Some (\<alpha>, n + 1 + size p')" by simp
    then show ?thesis unfolding Cons label_term.simps subt_at.simps using i by auto 
  qed simp
qed simp

lemma linear_label_term:
  assumes "linear_term t"
  shows "linear_term (label_term \<alpha> n t)"
  using assms proof(induct t arbitrary:n)
  case (Fun f ts)
  from Fun(2) have "(is_partition (map vars_term ts))"
    by simp
  then have "is_partition (map vars_term (map (label_term \<alpha> (Suc n)) ts))"
    by (metis (mono_tags, lifting) length_map map_nth_eq_conv vars_term_labeled_lhs)
  moreover {fix t assume t:"t \<in> set ts"
    with Fun(2) have "linear_term t"
      by simp
    with Fun(1) have "linear_term (label_term \<alpha> (Suc n) t)"
      using t by blast
  }
  ultimately show ?case unfolding label_term.simps by simp
qed simp

lemma var_term_lab_to_term:
  assumes "p \<in> poss t" and "t|_p = Var x"
  shows "term_lab_to_term t |_p = Var x"
  using assms proof(induct t arbitrary:p)
  case (Fun f ts)
  then obtain i p' where p':"i < length ts" "p = i#p'" "p' \<in> poss (ts!i)"
    by auto
  then show ?case
    unfolding term_lab_to_term.simps p'(2) subt_at.simps using Fun(1,3) p'(2) by force
qed simp

lemma poss_term_lab_to_term[simp]: "poss t = poss (term_lab_to_term t)"
  by(induct t) auto

lemma fun_poss_term_lab_to_term[simp]: "fun_poss t = fun_poss (term_lab_to_term t)"
  by(induct t) auto

lemma vars_term_list_term_lab_to_term: "vars_term_list t = vars_term_list (term_lab_to_term t)"
proof(induct t)
  case (Var x)
  then show ?case
    by (simp add: vars_term_list.simps(1))
next
  case (Fun f ts)
  then show ?case unfolding vars_term_list.simps term_lab_to_term.simps
    by (smt (verit, best) length_map map_eq_conv' nth_map nth_mem)
qed

lemma vars_term_list_term_to_term_lab: "vars_term_list (term_to_term_lab t) = vars_term_list t"
proof(induct t)
  case (Var x)
  then show ?case
    by (simp add: vars_term_list.simps(1))
next
  case (Fun f ts)
  then show ?case unfolding vars_term_list.simps term_to_term_lab.simps
    by (metis (mono_tags, lifting) length_map map_nth_eq_conv nth_mem)
qed

lemma linear_term_to_term_lab:
  assumes "linear_term t"
  shows "linear_term (term_to_term_lab t)"
  using assms proof(induct t)
  case (Fun f ts)
  then show ?case unfolding term_to_term_lab.simps linear_term.simps
    by (smt (verit, best) imageE length_map list.set_map map_nth_eq_conv set_vars_term_list vars_term_list_term_to_term_lab)
qed simp

lemma var_poss_list_term_lab_to_term: "var_poss_list t = var_poss_list (term_lab_to_term t)"
proof(induct t)
  case (Var x)
  then show ?case
    by (simp add: poss_list.simps(1))
next
  case (Fun f ts)
  then have *:"(map var_poss_list ts) = (map var_poss_list (map term_lab_to_term ts))"
    by auto
  then show ?case unfolding term_lab_to_term.simps var_poss_list.simps length_map *
    by blast
qed

lemma label_poss_labeled_lhs:
  assumes "p \<in> fun_poss (label_term \<alpha> n t)"
  shows "p \<in> labelposs (label_term \<alpha> n t)"
  using assms proof(induct t arbitrary:p n)
  case (Fun f ts)
  then show ?case proof(cases p)
    case (Cons i p')
    from Fun(2) have i:"i < length ts"
      unfolding Cons by simp
    with Fun(2) have "p' \<in> fun_poss (label_term \<alpha> (n+1) (ts!i))"
      unfolding Cons by auto
    with i have "p' \<in> labelposs (label_term \<alpha> (n+1) (ts!i))"
      using Fun(1) by simp
    with i show ?thesis
      unfolding Cons label_term.simps labelposs.simps by simp
  qed simp
qed simp

lemma labeled_var:
  assumes "source A = Var x"
  shows "labeled_source A = Var x"
  using assms proof(induct A)
  case (Prule \<alpha> As)
  then show ?case proof(cases "As = []")
    case True
    from Prule(2) have "lhs \<alpha> = Var x"
      unfolding source.simps True list.map by simp
    with True show ?thesis
      by simp
  next
    case False
    then obtain a as where as:"As = a # as"
      using list.exhaust by blast
    from Prule(2) obtain y where y:"lhs \<alpha> = Var y"
      using is_Var_def by fastforce
    from Prule(2) have "source a = Var x"
      unfolding source.simps y as single_var by simp
    with Prule(1) as have "labeled_source a = Var x"
      by simp
    then show ?thesis
      unfolding labeled_source.simps as y single_var by simp
  qed
qed simp_all

lemma labelposs_subs_fun_poss: "labelposs t \<subseteq> fun_poss t"
proof(induct t)
  case (Fun fl ts)
  then show ?case  proof(cases "snd fl")
    case None
    then obtain f where f:"fl = (f, None)"
      by (metis prod.collapse)
    then have "labelposs (Fun fl ts) = (\<Union>i<length ts. {i # p |p. p \<in> labelposs (ts ! i)})"
      by simp
    also have "... \<subseteq> (\<Union>i<length ts. {i # p |p. p \<in> fun_poss (ts ! i)})" using Fun
      by (smt SUP_mono basic_trans_rules(31) lessThan_iff mem_Collect_eq nth_mem subsetI)
    finally show ?thesis
      by auto
  next
    case (Some l)
    then obtain f where f:"fl = (f, Some l)"
      by (metis prod.collapse)
    then have "labelposs (Fun fl ts) = {[]} \<union> (\<Union>i<length ts. {i # p |p. p \<in> labelposs (ts ! i)})"
      by simp
    also have "... \<subseteq> {[]} \<union> (\<Union>i<length ts. {i # p |p. p \<in> fun_poss (ts ! i)})" using Fun
      by (smt SUP_mono basic_trans_rules(31) lessThan_iff mem_Collect_eq nth_mem subsetI sup_mono)
    finally show ?thesis
      by auto
  qed
qed simp

lemma labelposs_subs_poss[simp]: "labelposs t \<subseteq> poss t"
  using labelposs_subs_fun_poss fun_poss_imp_poss by blast

lemma get_label_imp_labelposs:
  assumes "p \<in> poss t" and "get_label (t|_p) \<noteq> None"
  shows "p \<in> labelposs t"
  using assms proof(induct p arbitrary:t)
  case Nil
  then show ?case unfolding subt_at.simps
    by (smt UnCI get_label.elims insert_iff labelposs.elims prod.sel(2) term.distinct(1) term.inject(2))
next
  case (Cons i p)
  then obtain f ts where t:"t = Fun f ts" and "p \<in> poss (ts ! i)" and i:"i < length ts"
    using args_poss by blast
  with Cons(1,3) have "p \<in> labelposs (ts!i)"
    by simp
  with i have p:"i # p \<in> (\<Union>i<length ts. {i # p |p. p \<in> labelposs (ts ! i)})"
    by blast
  then show ?case proof(cases "snd f")
    case None
    with p show ?thesis unfolding t using labelposs.simps(2)
      by (metis (mono_tags, lifting) prod.collapse)
  next
    case (Some a)
    with p show ?thesis unfolding t using labelposs.simps(3)
      by (smt UN_iff Un_iff mem_Collect_eq prod.collapse)
  qed
qed

lemma labelposs_obtain_label:
  assumes "p \<in> labelposs t"
  shows "\<exists>\<alpha> m. get_label (t|_p) = Some(\<alpha>, m)"
  using assms proof(induct t arbitrary: p)
  case (Fun fl ts)
  then show ?case proof(cases p)
    case Nil
    {fix f assume f:"fl = (f, None)"
      from Fun(2) have False unfolding Nil f labelposs.simps(2)
        by blast
    }
    with Nil show ?thesis
      by (metis eq_snd_iff get_label.simps(2) option.exhaust subt_at.simps(1))
  next
    case (Cons i q)
    with Fun(2) have iq:"i # q \<in> labelposs (Fun fl ts)"
      by simp
    then have i:"i < length ts"
      using labelposs_subs_poss by fastforce
    with iq have "i # q \<in> {i # p |p. p \<in> labelposs (ts ! i)}" proof(cases "snd fl")
      case (Some a)
      then obtain f \<alpha> n where f:"fl = (f, Some (\<alpha>, n))"
        by (metis eq_snd_iff)
      from iq show ?thesis unfolding f labelposs.simps
        by blast
    qed (smt UN_iff labelposs.simps(2) list.inject mem_Collect_eq prod.collapse)
    with i Fun(1) Cons show ?thesis
      by simp
  qed
qed simp

lemma possL_obtain_label:
  assumes "p \<in> possL A"
  shows "\<exists>\<alpha> m. get_label ((labeled_source A)|_p) = Some(\<alpha>, m)"
  using assms labelposs_obtain_label by blast

lemma labeled_source_apply_subst:
  assumes "A \<in> wf_pterm R"
  shows "labeled_source (A \<cdot> \<sigma>) = (labeled_source A) \<cdot> (labeled_source \<circ> \<sigma>)"
using assms proof(induct A)
  case (3 \<alpha> As)
  have id:"\<forall> x \<in> vars_term (labeled_lhs \<alpha>). (\<langle>map (labeled_source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) x = (\<langle>map labeled_source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (labeled_source \<circ> \<sigma>)) x"
  proof-
    have vars:"vars_term (labeled_lhs \<alpha>) = set (var_rule \<alpha>)" using vars_term_labeled_lhs by simp
    { fix i assume i:"i < length (var_rule \<alpha>)"
      with 3 have "(\<langle>map (labeled_source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) = labeled_source ((As!i) \<cdot> \<sigma>)"
        by (simp add: mk_subst_distinct)
      also have "... = labeled_source (As!i) \<cdot> (labeled_source \<circ> \<sigma>)"
        using 3 i by (metis nth_mem)
      also have "... = (\<langle>map labeled_source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (labeled_source \<circ> \<sigma>)) ((var_rule \<alpha>)!i)"
        using 3 i unfolding subst_compose_def by (simp add: mk_subst_distinct)
      finally have "(\<langle>map (labeled_source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) = (\<langle>map labeled_source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (labeled_source \<circ> \<sigma>)) ((var_rule \<alpha>)!i)" .
    } with vars show ?thesis by (metis in_set_idx)
  qed
  have "labeled_source ((Prule \<alpha> As) \<cdot> \<sigma>) = (labeled_lhs \<alpha>) \<cdot> \<langle>map (labeled_source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>"
    unfolding eval_term.simps(2) by simp
  also have "... = (labeled_lhs \<alpha>) \<cdot> (\<langle>map labeled_source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (labeled_source \<circ> \<sigma>))"
    using id by (meson term_subst_eq)
  also have "... = (labeled_source (Prule \<alpha> As)) \<cdot> (labeled_source \<circ> \<sigma>)" by simp
  finally show ?case .
qed simp_all

lemma labelposs_apply_subst: 
  "labelposs (s \<cdot> \<sigma>) = labelposs s \<union> {p@q| p q x. p \<in> var_poss s \<and> s|_p = Var x \<and> q \<in> labelposs (\<sigma> x)}"
proof(induct s)
  case (Fun f ts)
  obtain f' l where f:"f = (f', l)" by fastforce 
  let ?lp1="\<Union>i<length ts. {i # p |p. p \<in> labelposs (ts ! i)}"
  let ?lp2="\<Union>i<length ts. {i#(p@q)| p q x. p \<in> var_poss (ts!i) \<and> (ts!i)|_p = Var x \<and> q \<in> labelposs (\<sigma> x)}"
  {fix i assume i:"i < length ts" 
    with Fun have "{i # p |p. p \<in> labelposs (ts ! i \<cdot> \<sigma>)} = {i # p| p. p \<in> labelposs (ts!i) \<union> {p@q| p q x. p \<in> var_poss (ts!i) \<and> (ts!i)|_p = Var x \<and> q \<in> labelposs (\<sigma> x)}}"
      by auto
    then have "{i # p |p. p \<in> labelposs (map (\<lambda>s. s \<cdot> \<sigma>) ts ! i)} = {i # p| p. p \<in> labelposs (ts!i)} \<union> {i#(p@q)| p q x. p \<in> var_poss (ts!i) \<and> (ts!i)|_p = Var x \<and> q \<in> labelposs (\<sigma> x)}" 
      unfolding Un_iff using i by auto 
  }note IH=this
  {fix i assume i:"i < length ts" 
    let ?l="{i#(p@q)| p q x. p \<in> var_poss (ts!i) \<and> (ts!i)|_p = Var x \<and> q \<in> labelposs (\<sigma> x)}" 
    let ?r="{p@q| p q x. p \<in> {i # p |p. p \<in> var_poss (ts ! i)} \<and> (Fun f ts)|_p = Var x \<and> q \<in> labelposs (\<sigma> x)}" 
    have "?l = ?r" proof
      show "?l \<subseteq> ?r"
        by (smt (verit, ccfv_SIG) Collect_mono_iff Cons_eq_appendI mem_Collect_eq subt_at.simps(2)) 
      show "?r \<subseteq> ?l"
        by (smt (verit, best) Collect_mono_iff Cons_eq_appendI mem_Collect_eq subt_at.simps(2)) 
    qed
  }
  then have lp2:"{p@q| p q x. p \<in> var_poss (Fun f ts) \<and> (Fun f ts)|_p = Var x \<and> q \<in> labelposs (\<sigma> x)} = ?lp2"
    unfolding var_poss.simps by auto
  show ?case proof(cases l)
    case None
    have "labelposs (Fun f ts \<cdot> \<sigma>) = ?lp1 \<union> ?lp2" 
      unfolding eval_term.simps f None labelposs.simps length_map using IH by auto
    moreover have "labelposs (Fun f ts) = ?lp1" 
      unfolding f None by simp
    ultimately show ?thesis using lp2 by simp
  next
    case (Some a)
    have "labelposs (Fun f ts \<cdot> \<sigma>) = {[]} \<union> ?lp1 \<union> ?lp2" 
      unfolding eval_term.simps f Some labelposs.simps length_map using IH by auto
    moreover have "labelposs (Fun f ts) = {[]} \<union> ?lp1" 
      unfolding f Some by simp
    ultimately show ?thesis using lp2 by simp
  qed
qed simp

lemma possL_apply_subst: (*not used right now*)
  assumes "A \<cdot> \<sigma> \<in> wf_pterm R" 
  shows "possL (A \<cdot> \<sigma>) = possL A \<union> {p@q| p q x. p \<in> var_poss (labeled_source A) \<and> (labeled_source A)|_p = Var x \<and> q \<in> possL (\<sigma> x)}"
proof-
  from assms have *:"labeled_source (A \<cdot> \<sigma>) = labeled_source A \<cdot> (labeled_source \<circ> \<sigma>)" 
    using labeled_source_apply_subst subst_imp_well_def by blast 
  then show ?thesis unfolding * labelposs_apply_subst
    by auto 
qed

lemma label_term_to_term[simp]: "term_lab_to_term (label_term \<alpha> n t) = t"
  by(induct t arbitrary:\<alpha> n)(simp_all add: map_nth_eq_conv)

lemma fun_poss_label_term: "p \<in> fun_poss (label_term \<beta> n t) \<longleftrightarrow> p \<in> fun_poss t"
proof
  {assume "p \<in> fun_poss (label_term \<beta> n t)"
    then show "p \<in> fun_poss t" proof(induct t arbitrary:n p)
      case (Fun f ts)
      then show ?case by(cases p) auto
    qed simp
  }
  {assume "p \<in> fun_poss t"
    then show "p \<in> fun_poss (label_term \<beta> n t)" proof(induct t arbitrary:n p)
      case (Fun f ts)
      then show ?case by(cases p) auto
    qed simp
  }
qed

lemma term_lab_to_term_subst: "term_lab_to_term (t \<cdot> \<sigma>) = term_lab_to_term t \<cdot> (term_lab_to_term \<circ> \<sigma>)"
proof(induct t)
  case (Fun f As)
  then show ?case unfolding eval_term.simps(2) term_lab_to_term.simps
    by fastforce
qed simp

lemma labeled_source_to_term[simp]: "term_lab_to_term (labeled_source A) = source A"
proof(induct A)
  case (Prule \<alpha> As)
  have "term_lab_to_term \<circ> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha> = \<langle>map (term_lab_to_term \<circ> labeled_source) As\<rangle>\<^sub>\<alpha>"
    by simp
  also have " ... = \<langle>map source As\<rangle>\<^sub>\<alpha>" using Prule
    by (metis (mono_tags, lifting) comp_apply map_eq_conv)
  finally show ?case unfolding labeled_source.simps source.simps
    by (simp add: term_lab_to_term_subst)
qed simp_all

lemma possL_subset_poss_source: "possL A \<subseteq> poss (source A)"
  using poss_term_lab_to_term labeled_source_to_term labelposs_subs_poss
  by metis

lemma labeled_source_pos:
  assumes "p \<in> poss s" and "term_lab_to_term t = s"
  shows "term_lab_to_term (t|_p) = s|_p"
using assms proof(induct p arbitrary:s t)
  case (Cons i p)
  from Cons(2) obtain f ss where s:"s = Fun f ss"
    using args_poss by blast
  with Cons(2) have p:"p \<in> poss (ss!i)"
    by force
  from Cons(3) s obtain label ts where t:"t = Fun (f, label) ts"
    by (metis args_poss local.Cons(2) poss_term_lab_to_term prod.collapse term.inject(2) term_lab_to_term.simps(2))
  with Cons(2,3) s have "term_lab_to_term (ts!i) = ss!i"
    by auto
  with Cons(1) p show ?case unfolding s t
    by simp
qed simp

lemma get_label_at_fun_poss_subst:
  assumes "p \<in> fun_poss t"
  shows "get_label ((t \<cdot> \<sigma>)|_p) = get_label (t|_p)"
  using assms fun_poss_fun_conv fun_poss_imp_poss by fastforce

lemma labeled_source_simple_pterm:"possL (to_pterm t) = {}"
  by(induct t)  simp_all

lemma label_term_increase:
  assumes "s = (label_term \<alpha> n t) \<cdot> \<sigma>" and "p \<in> fun_poss t"
  shows "get_label (s|_p) = Some (\<alpha>, n + length p)"
  using assms proof(induct p arbitrary: s t n)
  case Nil
  then obtain f ts where "t = Fun f ts"
    by (metis fun_poss_list.simps(1) in_set_simps(3) is_FunE is_Var_def set_fun_poss_list)
  with Nil(1) show ?case
    by simp
next
  case (Cons i p)
  then obtain f ts where f:"t = Fun f ts" and i:"i<length ts"
    by (meson args_poss fun_poss_imp_poss)
  with Cons(3) have p:"p \<in> fun_poss (ts!i)"
    by auto
  let ?s' = "(label_term \<alpha> (n+1) (ts!i)) \<cdot> \<sigma>"
  from Cons(1) p have "get_label (?s'|_ p) = Some (\<alpha>, n + 1 + length p)"
    by blast
  with i show ?case unfolding Cons(2) f
    by simp
qed

text\<open>The number attached to a labeled function symbol cannot exceed the depth of that function symbol.\<close>
lemma label_term_max_value:
  assumes "p \<in> poss (labeled_source A)" and "get_label ((labeled_source A)|_p) = Some (\<alpha>, n)"
    and "A \<in> wf_pterm R"
  shows "n \<le> length p"
  using assms proof(induct A arbitrary: p)
  case (Pfun f As)
  then show ?case proof(cases p)
    case (Cons i q)
    with Pfun(2) have i:"i < length As" by simp
    with Pfun(3) have lab:"get_label (labeled_source (As!i) |_ q) = Some (\<alpha>, n)"
      unfolding Cons by simp
    with Pfun(2) i have "q \<in> poss (labeled_source (As!i))"
      unfolding Cons by auto
    with Pfun(1,4) Cons i lab show ?thesis
      using nth_mem fun_well_arg by fastforce
  qed simp
next
  case (Prule \<beta> As)
  from Prule(2) consider "p \<in> fun_poss (labeled_lhs \<beta>)" | "(\<exists>p1 p2 x. p = p1@p2
                                        \<and> p1 \<in> poss (labeled_lhs \<beta>) \<and> (labeled_lhs \<beta>)|_p1 = Var x
                                        \<and> p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)
                                        \<and> (labeled_source (Prule \<beta> As))|_p = ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)|_p2)"
    unfolding labeled_source.simps by (meson poss_is_Fun_fun_poss poss_subst_choice)
  then show ?case proof(cases)
    case 1
    then have "p \<in> fun_poss (lhs \<beta>)"
      by (simp add: fun_poss_label_term)
    then have "get_label ((labeled_source (Prule \<beta> As))|_p) = Some (\<beta>, length p)"
      unfolding labeled_source.simps by (simp add: label_term_increase)
    with Prule(3) show ?thesis by auto
  next
    case 2
    then obtain p1 p2 x where p1p2:"p = p1 @ p2" and x:"p1 \<in> poss (labeled_lhs \<beta>) \<and> labeled_lhs \<beta> |_ p1 = Var x"
       and p2:"p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)"
       and lab:"labeled_source (Prule \<beta> As) |_ p = (\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x |_ p2"
      by blast
    from Prule(4) have l:"length As = length (var_rule \<beta>)"
      using wf_pterm.simps by fastforce
    from x have "x \<in> vars_term (lhs \<beta>)"
      by (metis subt_at_imp_supteq subteq_Var_imp_in_vars_term vars_term_labeled_lhs)
    with x obtain i where i:"i < length (var_rule \<beta>) \<and> (var_rule \<beta>)!i = x"
      by (metis in_set_conv_nth set_vars_term_list vars_term_list_vars_distinct)
    with l have *:"(\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x = labeled_source (As!i)"
      by (metis (no_types, lifting) length_map lhs_subst_var_i nth_map)
    with Prule(3) lab have "get_label ((labeled_source (As!i))|_p2) = Some (\<alpha>, n)"
      by simp
    with Prule(1,4) p2 * i l have "n \<le> length p2"
      by (metis fun_well_arg nth_mem)
    with * p1p2 lab i l show ?thesis by force
  qed
qed simp

text\<open>The labels decrease when moving up towards the root from a labeled function symbol.\<close>
lemma label_decrease:
  assumes "p@q \<in> poss (labeled_source A)"
    and "get_label ((labeled_source A)|_(p@q)) = Some (\<alpha>, length q + n)"
    and "A \<in> wf_pterm R"
  shows "get_label ((labeled_source A)|_p) = Some (\<alpha>, n)"
  using assms proof(induct A arbitrary: p q)
  case (Pfun f As)
  then show ?case proof(cases p)
    case Nil
    from Pfun(2,3) obtain i q' where iq':"q = i#q'" and i:"i < length As" and q':"q' \<in> poss (labeled_source (As!i))"
      unfolding Nil by auto
    with Pfun(2,3) have "get_label (labeled_source (As!i) |_ (q')) = Some (\<alpha>, length q + n)"
      unfolding Nil by auto
    with iq' q' have False
      using label_term_max_value Pfun(4) i fun_well_arg by (metis le_imp_less_Suc length_nth_simps(2) not_add_less1 nth_mem)
    then show ?thesis by simp
  next
    case (Cons i p')
    with Pfun(2) have ip':"p = i#p'" and i:"i < length As"
      by auto
    with Pfun(2) have p':"p'@q \<in> poss (labeled_source (As!i))"
      by simp
    from Pfun(3) i ip' have "get_label (labeled_source (As!i) |_ (p'@q)) = Some (\<alpha>, length q + n)"
      by simp
    with Pfun(1,4) p' i have "get_label ((labeled_source (As!i))|_p') = Some (\<alpha>, n)"
      by (metis fun_well_arg nth_mem)
    then show ?thesis
      using i ip' by fastforce
  qed
next
  case (Prule \<beta> As)
  from Prule(2) consider "p@q \<in> fun_poss (labeled_lhs \<beta>)" | "(\<exists>p1 p2 x. p@q = p1@p2
                                        \<and> p1 \<in> poss (labeled_lhs \<beta>) \<and> (labeled_lhs \<beta>)|_p1 = Var x
                                        \<and> p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)
                                        \<and> (labeled_source (Prule \<beta> As))|_(p@q) = ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)|_p2)"
    unfolding labeled_source.simps by (meson poss_is_Fun_fun_poss poss_subst_choice)
  then show ?case proof(cases)
    case 1
    then have lab:"get_label ((labeled_source (Prule \<beta> As))|_(p@q)) = Some (\<beta>, length p + length q)"
      by (simp add: fun_poss_label_term label_term_increase)
    from 1 have "p \<in> fun_poss (labeled_lhs \<beta>)" proof(cases q)
      case (Cons a list)
      then show ?thesis
        using 1 fun_poss_append_poss fun_poss_imp_poss by blast
    qed simp
    with Prule(3) lab show ?thesis
      by (simp add: fun_poss_label_term label_term_increase)
  next
    case 2
    then obtain p1 p2 x where p1p2:"p@q = p1 @ p2" and x:"p1 \<in> poss (labeled_lhs \<beta>) \<and> labeled_lhs \<beta> |_ p1 = Var x"
       and p2:"p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)"
       and lab:"labeled_source (Prule \<beta> As) |_(p@q) = (\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x |_ p2"
      by blast
    from Prule(4) have l:"length As = length (var_rule \<beta>)"
      using wf_pterm.simps by fastforce
    from x have "x \<in> vars_term (lhs \<beta>)"
      by (metis subt_at_imp_supteq subteq_Var_imp_in_vars_term vars_term_labeled_lhs)
    then obtain i where i:"i < length (var_rule \<beta>) \<and> (var_rule \<beta>)!i = x"
      by (metis in_set_idx set_vars_term_list vars_term_list_vars_distinct)
    with l have *:"(\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x = labeled_source (As!i)"
      by (metis (no_types, lifting) length_map lhs_subst_var_i nth_map)
    with Prule(3) lab have as_i:"get_label ((labeled_source (As!i))|_p2) = Some (\<alpha>, length q + n)"
      by simp
    have p1_above_p:"p1 \<le>\<^sub>p p" proof(rule ccontr)
      assume "\<not> p1 \<le>\<^sub>p p"
      with p1p2 have "length p < length p1"
        by (metis less_eq_pos_simps(1) pos_cases pos_less_eq_append_not_parallel prefix_smaller)
      with p1p2 have le:"length p2 < length q"
        using length_append by (metis add.commute less_add_eq_less)
      with as_i Prule(4) * i l p2 have "length q + n \<le> length p2"
        by (metis fun_well_arg label_term_max_value nth_mem)
      with le show False by linarith
    qed
    let ?p'="the (remove_prefix p1 p)"
    from p1_above_p p1p2 have p2':"p2 = ?p' @ q"
      by (metis append_assoc pos_diff_def prefix_pos_diff same_append_eq)
    then have lab':"labeled_source (Prule \<beta> As) |_(p1@?p') = (\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x |_?p'"
      using x p1p2 Prule(2) unfolding labeled_source.simps
      by (metis (mono_tags, lifting) labeled_source.simps(3) poss_append_poss eval_term.simps(1) subt_at_subst subterm_poss_conv)
    from p2' Prule(1,4) p2 * i l as_i have "get_label ((labeled_source (As!i))|_?p') = Some (\<alpha>, n)"
      by (metis fun_well_arg nth_mem)
    with lab' * show ?thesis
      by (metis p1_above_p pos_diff_def prefix_pos_diff)
  qed
qed simp

text\<open>If a function symbol is labeled with @{term "(\<alpha>, n)"}, then the function symbol @{term n}
positions above it is labeled with @{term "(\<alpha>, 0)"}.\<close>
lemma obtain_label_root:
  assumes "p \<in> poss (labeled_source A)"
    and "get_label ((labeled_source A)|_p) = Some (\<alpha>, n)"
    and "A \<in> wf_pterm R"
  shows "get_label ((labeled_source A)|_(take (length p - n) p)) = Some (\<alpha>, 0) \<and> take (length p - n) p \<in> poss (labeled_source A)"
proof-
  from assms have n:"n \<le> length p"
    using label_term_max_value by blast
  with assms show ?thesis
    by (metis (no_types, lifting) add.right_neutral append_take_drop_id diff_diff_cancel label_decrease length_drop poss_append_poss)
qed

lemma label_ctxt_apply_term:
  assumes "get_label (labeled_source A |_ p) = l" "q \<in> poss s"
  shows "get_label (labeled_source ((ctxt_of_pos_term q (to_pterm s)) \<langle>A\<rangle>) |_ (q@p)) = l" 
using assms(2) proof(induct s arbitrary:q)
  case (Var x)
  then have q:"q = []" by simp
  from assms(1) show ?case unfolding q by simp
next
  case (Fun f ts)
  then show ?case proof(cases q)
    case Nil
    from assms(1) show ?thesis unfolding Nil by simp
  next
    case (Cons i q')
    with Fun(2) have i:"i < length ts" and q':"q' \<in> poss (ts!i)" by auto
    with Fun(1) have "get_label (labeled_source (ctxt_of_pos_term q' (to_pterm (ts!i)))\<langle>A\<rangle> |_ (q' @ p)) = l" by simp 
    then show ?thesis 
      unfolding to_pterm.simps Cons ctxt_of_pos_term.simps labeled_source.simps append_Cons intp_actxt.simps subt_at.simps
      by (metis (no_types, lifting) Cons_nth_drop_Suc append_take_drop_id i length_append length_map less_imp_le_nat list.size(4) nth_append_take nth_map)
  qed 
qed

lemma single_redex_at_p_label:
  assumes "p \<in> poss s" and "is_Fun (lhs \<alpha>)" 
  shows "get_label (labeled_source (ll_single_redex s p \<alpha>) |_p) = Some(\<alpha>, 0)"
proof-
  from assms(2) obtain f ts where f:"lhs \<alpha> = Fun f ts"
    by blast 
  have "get_label (labeled_source (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>))))) = Some (\<alpha>, 0)" 
    unfolding f labeled_source.simps label_term.simps eval_term.simps get_label.simps by simp
  then show ?thesis 
    unfolding ll_single_redex_def using label_ctxt_apply_term[where p="[]"] assms(1)
    by (smt (verit) self_append_conv subt_at.simps(1))  
qed

text\<open>Whenever a function symbol at position @{term p} has label @{term "(\<alpha>, 0)"} or no label in 
@{term "labeled_source A"}, then we know that there exists a position @{term q} in @{term A} such 
that @{term "A|_q = \<alpha>(As)"} for appropriate @{term As}.
Moreover, taking the source of the context at position @{term q} must be the same as first computing 
the source of @{term A} and then taking the context at @{term p}.\<close>
context left_lin
begin
lemma poss_labeled_source:
 assumes "p \<in> poss (labeled_source A)"
    and "get_label ((labeled_source A)|_p) = Some (\<alpha>, 0)"
    and "A \<in> wf_pterm R"
  shows "\<exists>q \<in> poss A. ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term q A) \<and>
         A|_q = Prule \<alpha> (map (\<lambda>i. A|_(q@[i])) [0..<length (var_rule \<alpha>)])"
using assms proof(induct A arbitrary:p)
  case (Var x)
  then have "p = []" by simp
  with Var(2) have False unfolding labeled_source.simps  by simp
  then show ?case by blast
next
  case (Pfun f As)
  then show ?case proof(cases p)
    case (Cons i p')
    with Pfun(2) have ip':"p = i#p'" and i:"i < length As"
      by auto
    with Pfun(2) have p':"p' \<in> poss (labeled_source (As!i))"
      by simp
    from Pfun(3) i ip' have "get_label (labeled_source (As!i) |_ p') = Some (\<alpha>, 0)"
      by simp
    with Pfun(1,4) p' i obtain q where q:"q \<in> poss (As!i)" and "ctxt_of_pos_term p' (source (As!i)) = source_ctxt (ctxt_of_pos_term q (As!i))"
      and prule:"(As!i)|_q = Prule \<alpha> (map (\<lambda>j. (As!i)|_(q@[j])) [0..<length (var_rule \<alpha>)])"
      using nth_mem by blast
    then have "ctxt_of_pos_term p (source (Pfun f As)) = source_ctxt (ctxt_of_pos_term (i#q) (Pfun f As))"
      unfolding ip' using i by(simp add: take_map drop_map)
    then show ?thesis
      using q(1) i prule by fastforce
  qed simp
next
  case (Prule \<beta> As)
  have l:"length As = length (var_rule \<beta>)"
    using Prule(4) using wf_pterm.simps by fastforce
  from Prule(2) consider "p \<in> fun_poss (labeled_lhs \<beta>)" | "(\<exists>p1 p2 x. p = p1@p2
                                        \<and> p1 \<in> poss (labeled_lhs \<beta>) \<and> (labeled_lhs \<beta>)|_p1 = Var x
                                        \<and> p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)
                                        \<and> (labeled_source (Prule \<beta> As))|_p = ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)|_p2)"
    unfolding labeled_source.simps by (meson poss_is_Fun_fun_poss poss_subst_choice)
  then show ?case proof(cases)
    case 1
    then have "p \<in> fun_poss (lhs \<beta>)"
      by (simp add: fun_poss_label_term)
    then have "get_label ((labeled_source (Prule \<beta> As))|_p) = Some (\<beta>, length p)"
      unfolding labeled_source.simps by (simp add: label_term_increase)
    with Prule(3) have p:"p = []" and \<alpha>:"\<alpha> = \<beta>" by simp+
    have "As = (map (\<lambda>i. Prule \<beta> As |_ ([i])) [0..<length As])"
      by (simp add: map_nth)
    then have "As = (map (\<lambda>i. Prule \<beta> As |_ ([] @ [i])) [0..<length (var_rule \<alpha>)])"
      unfolding \<alpha> using l by force
    then show ?thesis unfolding p \<alpha> by auto
  next
    case 2
    then obtain p1 p2 x where p1p2:"p = p1 @ p2" and x:"p1 \<in> poss (labeled_lhs \<beta>) \<and> labeled_lhs \<beta> |_ p1 = Var x"
       and p2:"p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)"
       and lab:"labeled_source (Prule \<beta> As) |_ p = (\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x |_ p2"
      by blast
    from Prule(4) have l:"length As = length (var_rule \<beta>)"
      using wf_pterm.simps by fastforce
    from Prule(4) have "to_rule \<beta> \<in> R"
      using wf_pterm.cases by force
    with left_lin have lin:"linear_term (lhs \<beta>)"
      using left_linear_trs_def by fastforce
    from x have p1:"p1 \<in> poss (lhs \<beta>)" by simp
    then have p1':"p1 \<in> poss ((lhs \<beta>) \<cdot> \<langle>map source As\<rangle>\<^sub>\<beta>)" by simp
    from p1 x have x':"lhs \<beta> |_ p1 = Var x"
      by (metis label_term_to_term labeled_source_pos term_lab_to_term.simps(1))
    from p1 x' obtain i where i:"i < length (vars_term_list (lhs \<beta>))" "var_poss_list (lhs \<beta>) ! i = p1" "vars_term_list (lhs \<beta>) ! i = x"
      by (metis in_set_idx length_var_poss_list term.inject(1) var_poss_iff var_poss_list_sound vars_term_list_var_poss_list)
    with lin have i':"i < length (var_rule \<beta>) \<and> (var_rule \<beta>)!i = x"
      by (metis linear_term_var_vars_term_list)
    with l have *:"(\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x = labeled_source (As!i)"
      by (metis (no_types, lifting) length_map lhs_subst_var_i nth_map)
    with Prule(3) lab have "get_label ((labeled_source (As!i))|_p2) = Some (\<alpha>, 0)"
      by simp
    with Prule(1,4) p2 * i' l obtain q where q:"q\<in>poss (As!i)" "ctxt_of_pos_term p2 (source (As!i)) = source_ctxt (ctxt_of_pos_term q (As!i))"
      "(As!i) |_ q = Prule \<alpha> (map (\<lambda>j. (As!i) |_ (q @ [j])) [0..<length (var_rule \<alpha>)])"
      by (smt (verit, ccfv_SIG) fun_well_arg map_eq_conv nth_mem)
    have p1'':"(var_poss_list (lhs \<beta>) ! length (take i As)) = p1"
      using i l by (metis id_take_nth_drop length_take length_var_poss_list lin linear_term_var_vars_term_list nth_append_length)
    have x_sub:"Var x \<cdot> \<langle>map source As\<rangle>\<^sub>\<beta> = source (As!i)"
      by (metis (no_types, lifting) i' l length_map lhs_subst_var_i nth_map eval_term.simps(1))
    have "ctxt_of_pos_term p (source (Prule \<beta> As)) = source_ctxt (ctxt_of_pos_term (i#q) (Prule \<beta> As))" proof-
      {fix y assume "y \<in> vars_term (lhs \<beta>)" "y \<noteq> vars_term_list (lhs \<beta>) ! i"
        then obtain j where j:"j < length (var_rule \<beta>)" "y = (var_rule \<beta>) ! j" "j \<noteq> i"
          by (metis in_set_conv_nth lin linear_term_var_vars_term_list set_vars_term_list)
        have x:"(vars_term_list (lhs \<beta>) ! length (take i As)) = x"
          by (metis i' id_take_nth_drop l length_take lin linear_term_var_vars_term_list nth_append_length)
        from j have "(\<langle>map source (take i As @ Var x # drop (Suc i) As)\<rangle>\<^sub>\<beta>) y = source (As!j)"
          using apply_lhs_subst_var_rule l
          by (smt (verit, best) Cons_nth_drop_Suc append_Cons_nth_not_middle append_take_drop_id i' length_append length_map length_nth_simps(2) lin linear_term_var_vars_term_list nth_map x)
        then have "(\<langle>map source (take i As @ Var (vars_term_list (lhs \<beta>) ! length (take i As)) # drop (Suc i) As)\<rangle>\<^sub>\<beta>) y = (\<langle>map source As\<rangle>\<^sub>\<beta>) y"
          unfolding x by (metis (no_types, lifting) j(1,2) l length_map lhs_subst_var_i nth_map)
      }
      then have *:"ctxt_of_pos_term p1 (lhs \<beta>) \<cdot>\<^sub>c \<langle>map source As\<rangle>\<^sub>\<beta> =
          ctxt_of_pos_term p1 (lhs \<beta> \<cdot> \<langle>map source (take i As @ Var (vars_term_list (lhs \<beta>) ! length (take i As)) # drop (Suc i) As)\<rangle>\<^sub>\<beta>)"
        using i 
        unfolding ctxt_of_pos_term_subst[OF p1, symmetric]
        apply (intro ctxt_of_pos_term_hole_subst[OF lin, of i])
        subgoal by (metis length_var_poss_list)
        by auto
      then show ?thesis
        unfolding source.simps p1p2 ctxt_of_pos_term_append[OF p1'] ctxt_of_pos_term_subst[OF p1] subt_at_subst[OF p1] x' ctxt_of_pos_term.simps source_ctxt.simps Let_def x_sub q(2) * p1''
        by simp
    qed
    moreover from q(3) have "Prule \<beta> As |_ (i#q) = Prule \<alpha> (map (\<lambda>j. Prule \<beta> As |_ ((i#q) @ [j])) [0..<length (var_rule \<alpha>)])"
      by simp
    ultimately show ?thesis
      using i' q(1) l by (metis poss_Cons_poss term.sel(4))
  qed
qed

lemma poss_labeled_source_None:
 assumes "p \<in> poss (labeled_source A)"
    and "get_label ((labeled_source A)|_p) = None"
    and "A \<in> wf_pterm R"
  shows "\<exists>q \<in> poss A. ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term q A)"
using assms proof(induct A arbitrary:p)
  case (Pfun f As)
  then show ?case proof(cases p)
    case (Cons i p')
    with Pfun(2) have ip':"p = i#p'" and i:"i < length As"
      by auto
    with Pfun(2) have p':"p' \<in> poss (labeled_source (As!i))"
      by simp
    from Pfun(3) have "get_label (labeled_source (As ! i) |_ p') = None" 
      unfolding ip' labeled_source.simps using i by simp
    with Pfun(1,4) p' i obtain q where q:"q \<in> poss (As!i)" and "ctxt_of_pos_term p' (source (As!i)) = source_ctxt (ctxt_of_pos_term q (As!i))"
      using nth_mem by blast
    then have "ctxt_of_pos_term p (source (Pfun f As)) = source_ctxt (ctxt_of_pos_term (i#q) (Pfun f As))"
      unfolding ip' using i by(simp add: take_map drop_map)
    then show ?thesis
      using q(1) i by fastforce
  qed simp
next
  case (Prule \<beta> As)
  have l:"length As = length (var_rule \<beta>)"
    using Prule(4) using wf_pterm.simps by fastforce
  from Prule(2) consider "p \<in> fun_poss (labeled_lhs \<beta>)" | "(\<exists>p1 p2 x. p = p1@p2
                                        \<and> p1 \<in> poss (labeled_lhs \<beta>) \<and> (labeled_lhs \<beta>)|_p1 = Var x
                                        \<and> p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)
                                        \<and> (labeled_source (Prule \<beta> As))|_p = ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)|_p2)"
    unfolding labeled_source.simps by (meson poss_is_Fun_fun_poss poss_subst_choice)
  then show ?case proof(cases)
    case 1
    then have "p \<in> fun_poss (lhs \<beta>)"
      by (simp add: fun_poss_label_term)
    then have "get_label ((labeled_source (Prule \<beta> As))|_p) = Some (\<beta>, length p)"
      unfolding labeled_source.simps by (simp add: label_term_increase)
    then show ?thesis 
      using Prule(3) by simp
  next
    case 2
    then obtain p1 p2 x where p1p2:"p = p1 @ p2" and x:"p1 \<in> poss (labeled_lhs \<beta>) \<and> labeled_lhs \<beta> |_ p1 = Var x"
       and p2:"p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)"
       and lab:"labeled_source (Prule \<beta> As) |_ p = (\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x |_ p2"
      by blast
    from Prule(4) have l:"length As = length (var_rule \<beta>)"
      using wf_pterm.simps by fastforce
    from Prule(4) have "to_rule \<beta> \<in> R"
      using wf_pterm.cases by force
    with left_lin have lin:"linear_term (lhs \<beta>)"
      using left_linear_trs_def by fastforce
    from x have p1:"p1 \<in> poss (lhs \<beta>)" by simp
    then have p1':"p1 \<in> poss ((lhs \<beta>) \<cdot> \<langle>map source As\<rangle>\<^sub>\<beta>)" by simp
    from p1 x have x':"lhs \<beta> |_ p1 = Var x"
      by (metis label_term_to_term labeled_source_pos term_lab_to_term.simps(1))
    from p1 x' obtain i where i:"i < length (vars_term_list (lhs \<beta>))" "var_poss_list (lhs \<beta>) ! i = p1" "vars_term_list (lhs \<beta>) ! i = x"
      by (metis in_set_idx length_var_poss_list term.inject(1) var_poss_iff var_poss_list_sound vars_term_list_var_poss_list)
    with lin have i':"i < length (var_rule \<beta>) \<and> (var_rule \<beta>)!i = x"
      by (metis linear_term_var_vars_term_list)
    with l have *:"(\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x = labeled_source (As!i)"
      by (metis (no_types, lifting) length_map lhs_subst_var_i nth_map)
    with Prule(3) lab have "get_label ((labeled_source (As!i))|_p2) = None"
      by simp
    with Prule(1,4) p2 * i' l obtain q where q:"q\<in>poss (As!i)" "ctxt_of_pos_term p2 (source (As!i)) = source_ctxt (ctxt_of_pos_term q (As!i))"
      by (smt (verit, ccfv_SIG) fun_well_arg map_eq_conv nth_mem)
    have p1'':"(var_poss_list (lhs \<beta>) ! length (take i As)) = p1"
      using i l by (metis id_take_nth_drop length_take length_var_poss_list lin linear_term_var_vars_term_list nth_append_length)
    have x_sub:"Var x \<cdot> \<langle>map source As\<rangle>\<^sub>\<beta> = source (As!i)"
      by (metis (no_types, lifting) i' l length_map lhs_subst_var_i nth_map eval_term.simps(1))
    have "ctxt_of_pos_term p (source (Prule \<beta> As)) = source_ctxt (ctxt_of_pos_term (i#q) (Prule \<beta> As))" proof-
      {fix y assume "y \<in> vars_term (lhs \<beta>)" "y \<noteq> vars_term_list (lhs \<beta>) ! i"
        then obtain j where j:"j < length (var_rule \<beta>)" "y = (var_rule \<beta>) ! j" "j \<noteq> i"
          by (metis in_set_conv_nth lin linear_term_var_vars_term_list set_vars_term_list)
        have x:"(vars_term_list (lhs \<beta>) ! length (take i As)) = x"
          by (metis i' id_take_nth_drop l length_take lin linear_term_var_vars_term_list nth_append_length)
        from j have "(\<langle>map source (take i As @ Var x # drop (Suc i) As)\<rangle>\<^sub>\<beta>) y = source (As!j)"
          using apply_lhs_subst_var_rule l
          by (smt (verit, best) Cons_nth_drop_Suc append_Cons_nth_not_middle append_take_drop_id i' length_append length_map length_nth_simps(2) lin linear_term_var_vars_term_list nth_map x)
        then have "(\<langle>map source (take i As @ Var (vars_term_list (lhs \<beta>) ! length (take i As)) # drop (Suc i) As)\<rangle>\<^sub>\<beta>) y = (\<langle>map source As\<rangle>\<^sub>\<beta>) y"
          unfolding x by (metis (no_types, lifting) j(1,2) l length_map lhs_subst_var_i nth_map)
      }
      then have *:"ctxt_of_pos_term p1 (lhs \<beta>) \<cdot>\<^sub>c \<langle>map source As\<rangle>\<^sub>\<beta> =
          ctxt_of_pos_term p1 (lhs \<beta> \<cdot> \<langle>map source (take i As @ Var (vars_term_list (lhs \<beta>) ! length (take i As)) # drop (Suc i) As)\<rangle>\<^sub>\<beta>)"
        using i 
        unfolding ctxt_of_pos_term_subst[OF p1, symmetric]
        apply (intro ctxt_of_pos_term_hole_subst[OF lin, of i])
        subgoal by (metis length_var_poss_list)
        by auto
      then show ?thesis
        unfolding source.simps p1p2 ctxt_of_pos_term_append[OF p1'] ctxt_of_pos_term_subst[OF p1] subt_at_subst[OF p1] x' ctxt_of_pos_term.simps source_ctxt.simps Let_def x_sub q(2) * p1''
        by simp
    qed
    then show ?thesis
      using i' q(1) l by (metis poss_Cons_poss term.sel(4))
  qed
qed simp
end

text\<open>If we know that some part of a term does not contain labels (i.e., is coming from a simple
proof term @{term t}) then we know that the label originates below some variable position of @{term t}.\<close>
lemma labeled_source_to_pterm_subst:
  assumes p_pos:"p \<in> possL (to_pterm t \<cdot> \<sigma>)" and well:"\<forall>x \<in> vars_term t. \<sigma> x \<in> wf_pterm R"
  shows "\<exists>p1 p2 x \<gamma>. p1 \<in> poss t \<and> t|_p1 = Var x \<and> p1@p2 \<le>\<^sub>p p
      \<and> p2 \<in> possL (\<sigma> x) \<and> get_label ((labeled_source (\<sigma> x))|_p2) = Some (\<gamma>, 0) "
proof-
  {assume p:"p \<in> fun_poss (labeled_source (to_pterm t))"
    then have "get_label ((labeled_source (to_pterm t))|_p) = None"
      using labeled_source_simple_pterm by (metis empty_iff fun_poss_imp_poss get_label_imp_labelposs)
    moreover have "get_label ((labeled_source ((to_pterm t) \<cdot> \<sigma>))|_p) = get_label ((labeled_source (to_pterm t))|_p)"
      by (metis get_label_at_fun_poss_subst labeled_source_apply_subst p to_pterm_wf_pterm)
    ultimately have False using p_pos possL_obtain_label by fastforce
  }
  with p_pos obtain p1 r x where p:"p = p1@r" and p1:"p1 \<in> poss t" and t:"(labeled_source (to_pterm t))|_p1 = Var x"
    by (smt (z3) labeled_source_apply_subst labeled_source_to_term possL_subset_poss_source poss_subst_apply_term poss_term_lab_to_term source_to_pterm subset_eq to_pterm_wf_pterm)
  then have x:"t|_p1 = Var x"
    by (metis labeled_source_pos labeled_source_to_term source_to_pterm term_lab_to_term.simps(1))
  from p_pos have r_pos:"r \<in> poss (labeled_source (\<sigma> x))"
    unfolding p using p1 t labeled_source_apply_subst
    by (smt (z3) comp_apply labeled_source_to_term labelposs_subs_poss less_eq_pos_def less_eq_pos_simps(1) p poss_append_poss poss_term_lab_to_term source_to_pterm subset_eq eval_term.simps(1) subt_at_subst to_pterm_wf_pterm)
  from p_pos obtain \<gamma> n where lab:"get_label ((labeled_source (\<sigma> x))|_r) = Some (\<gamma>, n)"
    unfolding p labeled_source_apply_subst[OF to_pterm_wf_pterm] using t p1 p
    by (smt (verit, ccfv_SIG) comp_apply fun_poss_imp_poss labeled_source_to_term labelposs_obtain_label labelposs_subs_fun_poss poss_term_lab_to_term source_to_pterm subset_eq eval_term.simps(1) subt_at_subst subterm_poss_conv)
  let ?p2="take (length r - n) r"
  have "?p2 \<le>\<^sub>p r"  by (metis append_take_drop_id less_eq_pos_simps(1))
  then have "p1@?p2 \<le>\<^sub>p p" unfolding p by simp
  moreover have "get_label ((labeled_source (\<sigma> x))|_?p2) = Some (\<gamma>, 0) \<and> ?p2 \<in> poss (labeled_source (\<sigma> x))"
    using obtain_label_root[OF r_pos lab] well p1 x by (metis in_mono term.set_intros(3) vars_term_subt_at)
  moreover then have "?p2 \<in> possL (\<sigma> x)" using get_label_imp_labelposs by blast
  ultimately show ?thesis using p1 x by blast
qed

lemma labelposs_subst:
  assumes "p \<in> labelposs (t \<cdot> \<sigma>)"
  shows "p \<in> labelposs t \<or> (\<exists>p1 p2 x. p = p1@p2 \<and> p1 \<in> poss t \<and> t|_p1 = Var x \<and> p2 \<in> labelposs (\<sigma> x))"
  using assms proof(induct t arbitrary:p)
  case (Fun fl ts)
  then show ?case proof(cases p)
    case Nil
    from Fun(2) obtain f l where "fl = (f, Some l)"
      unfolding eval_term.simps Nil by (metis get_label.simps(2) labelposs_obtain_label subt_at.simps(1) surjective_pairing)
    then show ?thesis
      unfolding Nil by simp
  next
    case (Cons i p')
    from Fun(2) have i:"i < length ts"
      unfolding Cons eval_term.simps using labelposs_subs_poss by fastforce
    with Fun(2) have "p' \<in> labelposs (ts!i \<cdot> \<sigma>)"
      unfolding Cons eval_term.simps by (metis (no_types, lifting) get_label_imp_labelposs labelposs_obtain_label labelposs_subs_poss nth_map option.simps(3) poss_Cons_poss subset_eq subt_at.simps(2) term.sel(4))
    with Fun(1) i consider "p' \<in> labelposs (ts!i)" | "(\<exists>p1 p2 x. p' = p1 @ p2 \<and> p1 \<in> poss (ts!i) \<and> (ts!i) |_ p1 = Var x \<and> p2 \<in> labelposs (\<sigma> x))"
      by (meson nth_mem)
    then show ?thesis proof(cases)
      case 1
      with i show ?thesis unfolding Cons
        by (metis (no_types, lifting) get_label_imp_labelposs labelposs_obtain_label labelposs_subs_poss option.simps(3) poss_Cons_poss subsetD subt_at.simps(2) term.sel(4))
    next
      case 2
      then obtain p1 p2 x where p':"p' = p1 @ p2" and p1:"p1 \<in> poss (ts ! i)" "ts ! i |_ p1 = Var x" and "p2 \<in> labelposs (\<sigma> x)"
        by blast
      with i show ?thesis unfolding Cons
        by (metis append_Cons poss_Cons_poss subt_at.simps(2) term.sel(4))
    qed
  qed
qed simp

lemma set_labelposs_subst: (*can this be simplified using labelposs_apply_subst?*)
  "labelposs (t \<cdot> \<sigma>) = labelposs t \<union> (\<Union>i< length (vars_term_list t). {(var_poss_list t!i)@q | q. q \<in> labelposs (\<sigma> (vars_term_list t ! i))})" (is "?ps = ?qs")
proof
  {fix p assume "p \<in> ?ps"
    then consider "p \<in> labelposs t" | "(\<exists>p1 p2 x. p = p1@p2 \<and> p1 \<in> poss t \<and> t|_p1 = Var x \<and> p2 \<in> labelposs (\<sigma> x))"
      using labelposs_subst by blast
    then have "p \<in> ?qs" proof(cases)
      case 2
      then obtain p1 p2 x where "p = p1@p2 \<and> p1 \<in> poss t \<and> t|_p1 = Var x \<and> p2 \<in> labelposs (\<sigma> x)"
        by blast
      moreover then obtain i where i:"i < length (vars_term_list t)" "vars_term_list t ! i = x" "var_poss_list t ! i = p1"
        by (metis in_set_idx length_var_poss_list term.inject(1) var_poss_iff var_poss_list_sound vars_term_list_var_poss_list)
      ultimately have "p \<in> {var_poss_list t ! i @ q |q. q \<in> labelposs (\<sigma> (vars_term_list t ! i))}"
        by blast
      with i(1) show ?thesis
        by blast
    qed simp
  }
  then show "?ps \<subseteq> ?qs"
    by blast
  {fix q assume "q \<in> ?qs"
    then consider "q \<in> labelposs t" | "q \<in> (\<Union>i< length (vars_term_list t). {(var_poss_list t!i)@q | q. q \<in> labelposs (\<sigma> (vars_term_list t ! i))})"
      by blast
    then have "q \<in> ?ps" proof(cases)
      case 1
      then show ?thesis proof(induct t arbitrary:q)
        case (Fun f ts)
        then show ?case proof(cases q)
          case Nil
          with Fun(2) obtain f' lab where f':"f = (f', Some lab)"
            by (metis get_label.simps(2) labelposs_obtain_label prod.exhaust_sel subt_at.simps(1))
          show ?thesis unfolding Nil f' by simp
        next
          case (Cons i q')
          obtain f' lab where f':"f = (f', lab)"
            by fastforce
          show ?thesis proof(cases lab)
            case None
            from Fun(2) have i:"i < length ts"
              unfolding f' Cons None labelposs.simps by simp
            from Fun(2) have "q' \<in> labelposs (ts!i)"
              unfolding f' Cons None by simp
            with Fun(1) i have "q' \<in> labelposs (ts!i \<cdot> \<sigma>)"
              by simp
            with i show ?thesis
              unfolding f' Cons None eval_term.simps labelposs.simps by simp
          next
            case (Some a)
            from Fun(2) have i:"i < length ts"
              unfolding f' Cons Some labelposs.simps by simp
            from Fun(2) have "q' \<in> labelposs (ts!i)"
              unfolding f' Cons Some by simp
            with Fun(1) i have "q' \<in> labelposs (ts!i \<cdot> \<sigma>)"
              by simp
            with i show ?thesis
              unfolding f' Cons Some eval_term.simps labelposs.simps by simp
          qed
        qed
      qed simp
    next
      case 2
      then show ?thesis proof(induct t arbitrary:q)
        case (Var x)
        have "var_poss_list (Var x) = [[]]"
          unfolding poss_list.simps var_poss.simps by simp
        with Var show ?case unfolding vars_term_list.simps
          by (smt (verit, ccfv_SIG) One_nat_def UN_iff bot_nat_0.not_eq_extremum length_0_conv length_nth_simps(2) lessThan_iff mem_Collect_eq not_less_eq nth_Cons_0 self_append_conv2 eval_term.simps(1))
      next
        case (Fun fl ts)
        from Fun(2) obtain i q' where q:"q = var_poss_list (Fun fl ts) ! i @ q'" "q' \<in> labelposs (\<sigma> (vars_term_list (Fun fl ts) ! i))" and i:"i < length (vars_term_list (Fun fl ts))"
          by blast
        then have i':"i < length (var_poss_list (Fun fl ts))"
          by (metis length_var_poss_list)
        then obtain j r where j:"j < length ts" "var_poss_list (Fun fl ts) ! i = j#r"
          unfolding var_poss_list.simps by (smt (z3) add.left_neutral diff_zero length_map length_upt length_zip map_nth_eq_conv min.idem nth_concat_split nth_upt nth_zip prod.simps(2))
        with i obtain x where x:"Fun fl ts |_(j#r) = Var x"
          by (metis vars_term_list_var_poss_list)
        from j i' have "j#r \<in> var_poss (Fun fl ts)"
          by (metis nth_mem var_poss_list_sound)  
        then have "r \<in> var_poss (ts!j)"
          by simp
        then obtain i' where r:"i'<length (var_poss_list (ts!j))" "r = var_poss_list (ts!j) ! i'"
          by (metis in_set_conv_nth var_poss_list_sound)
        moreover then have "(vars_term_list (Fun fl ts) ! i) = (vars_term_list (ts!j) ! i')"
          using x by (metis i j(2) length_var_poss_list subt_at.simps(2) term.inject(1) vars_term_list_var_poss_list)
        ultimately have "r@q' \<in> (\<Union>i<length (vars_term_list (ts!j)). {var_poss_list (ts!j) ! i @ q |q. q \<in> labelposs (\<sigma> (vars_term_list (ts!j) ! i))})"
          using q(2) unfolding length_var_poss_list by auto
        with Fun(1) j(1) have r_pos:"r@q' \<in> labelposs ((ts!j) \<cdot> \<sigma>)"
          using nth_mem by blast
        obtain f lab where f:"fl = (f, lab)"
          using surjective_pairing by blast
        then show ?case proof(cases lab)
          case None
          from r_pos have "j#r@q' \<in> labelposs (Fun fl ts \<cdot> \<sigma>)"
            unfolding eval_term.simps f None labelposs.simps length_map using j(1) by simp
          then show ?thesis unfolding q j(2) by simp
        next
          case (Some a)
         from r_pos have "j#r@q' \<in> labelposs (Fun fl ts \<cdot> \<sigma>)"
            unfolding eval_term.simps f Some labelposs.simps length_map using j(1) by simp
          then show ?thesis unfolding q j(2) by simp
        qed
      qed
    qed
  }
  then show "?qs \<subseteq> ?ps"
    by blast
qed

text\<open>The labeled positions in a proof term @{term "Prule \<alpha> As"} are the function positions of 
@{term "lhs \<alpha>"} together with all labeled positions in the arguments @{term As}.\<close>
lemma possl_rule:
  assumes "length As = length (var_rule \<alpha>)" "linear_term (lhs \<alpha>)"
  shows "possL (Prule \<alpha> As) = fun_poss (lhs \<alpha>) \<union> (\<Union>i< (length As). {(var_poss_list (lhs \<alpha>)!i)@q | q. q \<in> possL(As!i)})"
proof-
  from assms(1,2) have l:"length (vars_term_list (labeled_lhs \<alpha>)) = length As"
    by (metis linear_term_var_vars_term_list vars_term_list_labeled_lhs)
  have "labelposs (labeled_lhs \<alpha>) = fun_poss (lhs \<alpha>)"
    by (metis fun_poss_term_lab_to_term label_poss_labeled_lhs label_term_to_term labelposs_subs_fun_poss subsetI subset_antisym)
  moreover from assms(1,2) have "i < length As \<Longrightarrow> (\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) (vars_term_list (labeled_lhs \<alpha>) ! i) = labeled_source (As!i)" for i
    using lhs_subst_var_i linear_term_var_vars_term_list by (smt (verit, best) length_map nth_map vars_term_list_labeled_lhs)
  ultimately show ?thesis using set_labelposs_subst[of "labeled_lhs \<alpha>"] unfolding l var_poss_list_labeled_lhs by force
qed

lemma labelposs_subs_fun_poss_source:
  assumes "p \<in> possL A"
  shows "p \<in> fun_poss (source A)"
proof-
  have "p \<in> fun_poss (labeled_source A)"
    using assms labelposs_subs_fun_poss by blast
  then show ?thesis using fun_poss_term_lab_to_term
    by auto
qed

text\<open>The labeled source of a context (obtained from some proof term @{term A}) applied to some proof 
term @{term B} is the labeled source of the context applied to the labeled source of the proof term 
@{term B}.\<close>
context left_lin
begin
lemma label_source_ctxt:
  assumes "A \<in> wf_pterm R"
  and "ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term p' A)"
  and "p \<in> poss (source A)" and "p' \<in> poss A"
  shows "labeled_source (ctxt_of_pos_term p' A)\<langle>B\<rangle> = (ctxt_of_pos_term p (labeled_source A))\<langle>labeled_source B\<rangle>"
  using assms proof(induct p' arbitrary:p A)
  case Nil
  then have p:"p = []"
    using hole_pos_ctxt_of_pos_term by force
  then show ?case by simp
next
  case (Cons i p')
  then obtain fl As where a:"A = Fun fl As" and i:"i < length As" and p':"p' \<in> poss (As!i)"
    by (meson args_poss)
  then show ?case proof(cases fl)
    case (Inl \<alpha>)
    from Cons(2) have l:"length As = length (var_rule \<alpha>)"
      unfolding a Inl using wf_pterm.cases by auto
    have "to_rule \<alpha> \<in> R"
      using Cons(2) unfolding a Inl using wf_pterm.cases by force
    with left_lin have lin:"linear_term (lhs \<alpha>)"
      using left_linear_trs_def by fastforce
    let ?p1="var_poss_list (lhs \<alpha>) ! i"
    from i l lin have p1:"(lhs \<alpha>)|_?p1 = Var (var_rule \<alpha> ! i)"
      by (metis linear_term_var_vars_term_list vars_term_list_var_poss_list)
    from i l have p1_pos:"?p1 \<in> poss (lhs \<alpha>)"
      by (metis comp_apply length_remdups_leq length_rev length_var_poss_list nth_mem order_less_le_trans var_poss_imp_poss var_poss_list_sound)
    let ?p2="hole_pos (source_ctxt (ctxt_of_pos_term p' (As ! i)))"
    have "hole_pos (source_ctxt (ctxt_of_pos_term (i # p') A)) = ?p1@?p2"
      unfolding a Inl source.simps ctxt_of_pos_term.simps source_ctxt.simps Let_def hole_pos_ctxt_compose using p1_pos Cons(5) a by force
    with Cons(3) have p:"p = ?p1@?p2"
      by (metis Cons.prems(3) hole_pos_ctxt_of_pos_term)
    have at_p1:"(source A)|_?p1 = source (As!i)"
      unfolding a Inl source.simps using p1
      by (smt (verit, best) Inl i l length_map lhs_subst_var_i nth_map p1_pos eval_term.simps(1) subt_at_subst)
    with Cons(4) have p2_pos:"?p2 \<in> poss (source (As!i))"
      unfolding p by simp
    from at_p1 have *:"ctxt_of_pos_term p (source A) = (ctxt_of_pos_term ?p1 (source A) \<circ>\<^sub>c (ctxt_of_pos_term ?p2 (source (As ! i))))"
      unfolding p using ctxt_of_pos_term_append using Cons.prems(3) p by fastforce
    from Cons(3) have "ctxt_of_pos_term ?p2 (source (As!i)) = source_ctxt (ctxt_of_pos_term p' (As!i))"
      unfolding * unfolding a Inl source.simps ctxt_of_pos_term.simps source_ctxt.simps Let_def using ctxt_comp_equals Cons(5) p1_pos
      by (smt (verit, ccfv_SIG) a ctxt_of_pos_term.simps(2) hole_pos.simps(2) hole_pos_ctxt_of_pos_term list.inject poss_imp_subst_poss)
    with Cons(1,2) i p2_pos p' a Inl have IH:"labeled_source (ctxt_of_pos_term p' (As!i))\<langle>B\<rangle> = (ctxt_of_pos_term ?p2 (labeled_source (As!i)))\<langle>labeled_source B\<rangle>"
      by (meson fun_well_arg nth_mem)
    then have list_IH:"map labeled_source (take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As) =
      map labeled_source (take i As) @ (ctxt_of_pos_term ?p2 (labeled_source (As ! i)))\<langle>labeled_source B\<rangle> # map labeled_source (drop (Suc i) As)"
      using i by fastforce
    from lin have lin':"linear_term (labeled_lhs \<alpha>)"
      using linear_label_term by blast
    from p1_pos have p1_pos:"?p1 \<in> poss (labeled_lhs \<alpha>)"
      by simp
    from p1 have x:"labeled_lhs \<alpha> |_ var_poss_list (lhs \<alpha>) ! i = Var (var_rule \<alpha> ! i)"
      by (metis label_term_to_term p1_pos poss_term_lab_to_term var_label_term)
    have "(\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>)((var_rule \<alpha> ! i) := (ctxt_of_pos_term ?p2 ((\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha> ! i)))\<langle>labeled_source B\<rangle>)
      = \<langle>(take i (map labeled_source As)) @ (ctxt_of_pos_term ?p2 (labeled_source (As!i)))\<langle>labeled_source B\<rangle> # (drop (Suc i) (map labeled_source As))\<rangle>\<^sub>\<alpha>"
      using i by (smt (verit, best) Cons.prems(4) a ctxt_of_pos_term.simps(2) hole_pos.simps(2) hole_pos_ctxt_of_pos_term id_take_nth_drop l length_map lhs_subst_upd lhs_subst_var_i list.inject nth_map take_map)
    then show ?thesis unfolding a Inl ctxt_of_pos_term.simps labeled_source.simps intp_actxt.simps p list_IH
      using replace_at_append_subst[OF lin' p1_pos x] by (smt (verit) drop_map take_map)
  next
    case (Inr f)
    from Cons(3,4,5) obtain p2 where p:"p = i#p2" and p2:"p2 \<in> poss (source (As!i))" and ctxt:"ctxt_of_pos_term p2 (source (As!i)) = source_ctxt (ctxt_of_pos_term p' (As!i))"
      unfolding a Inr source.simps ctxt_of_pos_term.simps source_ctxt.simps by (smt (verit, best) Cons.prems(2) Cons.prems(3) Inr a actxt.inject ctxt_of_pos_term.simps(2) i nth_map source_poss)
    from Cons(1,2) ctxt p2 p' have IH:"labeled_source (ctxt_of_pos_term p' (As!i))\<langle>B\<rangle> = (ctxt_of_pos_term p2 (labeled_source (As!i)))\<langle>labeled_source B\<rangle>"
      using a i nth_mem by blast
    then have list_IH:"map labeled_source (take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As) =
      map labeled_source (take i As) @ (ctxt_of_pos_term p2 (labeled_source (As ! i)))\<langle>labeled_source B\<rangle> # map labeled_source (drop (Suc i) As)"
      using i by fastforce
    show ?thesis unfolding a Inr ctxt_of_pos_term.simps p labeled_source.simps intp_actxt.simps list_IH
      by (simp add: drop_map i take_map)
  qed
qed
end

lemma labeled_ctxt_above:
  assumes "p \<in> poss A" and "r \<in> poss A" and "\<not> p \<le>\<^sub>p r"
  shows "get_label ((ctxt_of_pos_term p A)\<langle>labeled_source B\<rangle> |_r) = get_label (A |_r)"
using assms proof(induct A arbitrary:r p)
  case (Fun f As)
  then have "p \<noteq> []"
    by blast 
  with Fun(2) obtain i p' where i:"i < length As" and p':"p' \<in> poss (As!i)" and p:"p = i#p'" 
    by auto
  from Fun(4) consider "r <\<^sub>p p" | "r \<bottom> p"
    using parallel_pos by fastforce 
  then show ?case proof(cases)
    case 1
    then show ?thesis proof(cases r)
      case Nil
      show ?thesis unfolding p Nil by simp
    next
      case (Cons j r')
      from 1 have j:"j = i" 
        unfolding p Cons by simp 
      with Fun(1) have "get_label ((ctxt_of_pos_term p' (As!i))\<langle>labeled_source B\<rangle> |_ r') = get_label ((As!i) |_ r')" 
        using i p' Fun(3,4) unfolding Cons j p by simp 
      then show ?thesis 
        unfolding Cons p subt_at.simps ctxt_of_pos_term.simps intp_actxt.simps by (metis i j nat_less_le nth_append_take)
    qed
  next
    case 2
    then obtain j r' where r:"r = j#r'" 
      unfolding p by (metis parallel_pos.elims(2)) 
    then show ?thesis proof(cases "i = j")
      case True
      from Fun(1) 2 i have "get_label ((ctxt_of_pos_term p' (As!i))\<langle>labeled_source B\<rangle> |_ r') = get_label ((As!i) |_ r')"
        using Fun.prems(2) Fun.prems(3) True p p' r by force 
      then show ?thesis using p r True 
        by (metis "2" Fun.prems(1) Fun.prems(2) parallel_pos parallel_replace_at_subt_at) 
    next
      case False
      then show ?thesis 
        unfolding p r subt_at.simps ctxt_of_pos_term.simps intp_actxt.simps by (metis i nth_list_update upd_conv_take_nth_drop)
    qed
  qed
qed simp

text\<open>The labeled positions of a context (obtained from some proof term @{term A}) applied to some 
proof term @{term B} are the labeled positions of the context together with the labeled positions of 
the proof term @{term B}.\<close>
context left_lin
begin
lemma label_ctxt: (*maybe simplify using lemma above*) (*maybe not even needed anymore*)
  assumes "A \<in> wf_pterm R"
  and "ctxt_of_pos_term p (source A) = source_ctxt (ctxt_of_pos_term p' A)"
  and "p \<in> poss (source A)" and "p' \<in> poss A"
  shows "possL (ctxt_of_pos_term p' A)\<langle>B\<rangle> = {q. q \<in> possL A \<and> \<not>p \<le>\<^sub>p q} \<union> {p@q| q. q \<in> possL B}"
  using assms proof(induct p' arbitrary:p A)
  case Nil
  then have p:"p = []"
    using hole_pos_ctxt_of_pos_term by force
  then have "{q \<in> possL A. \<not> p \<le>\<^sub>p q} = {}"
    by simp
  then show ?case
    unfolding Nil ctxt_of_pos_term.simps p by simp
next
  case (Cons i p')
  then obtain fl As where a:"A = Fun fl As" and i:"i < length As" and p':"p' \<in> poss (As!i)"
    by (meson args_poss)
  then show ?case proof(cases fl)
    case (Inl \<alpha>)
    from Cons(2) have l:"length As = length (var_rule \<alpha>)"
      unfolding a Inl using wf_pterm.cases by auto
    have "to_rule \<alpha> \<in> R"
      using Cons(2) unfolding a Inl using wf_pterm.cases by force
    with left_lin have lin:"linear_term (lhs \<alpha>)"
      using left_linear_trs_def by fastforce
    let ?p1="var_poss_list (lhs \<alpha>) ! i"
    from i l lin have p1:"(lhs \<alpha>)|_?p1 = Var (var_rule \<alpha> ! i)"
      by (metis linear_term_var_vars_term_list vars_term_list_var_poss_list)
    from i l have p1_pos:"?p1 \<in> poss (lhs \<alpha>)"
      by (metis comp_apply length_remdups_leq length_rev length_var_poss_list nth_mem order_less_le_trans var_poss_imp_poss var_poss_list_sound)
    let ?p2="hole_pos (source_ctxt (ctxt_of_pos_term p' (As ! i)))"
    have "hole_pos (source_ctxt (ctxt_of_pos_term (i # p') A)) = ?p1@?p2"
      unfolding a Inl source.simps ctxt_of_pos_term.simps source_ctxt.simps Let_def hole_pos_ctxt_compose using p1_pos Cons(5) a by force
    with Cons(3) have p:"p = ?p1@?p2"
      by (metis Cons.prems(3) hole_pos_ctxt_of_pos_term)
    have at_p1:"(source A)|_?p1 = source (As!i)"
      unfolding a Inl source.simps using p1
      by (smt (verit, best) Inl i l length_map lhs_subst_var_i nth_map p1_pos eval_term.simps(1) subt_at_subst)
    with Cons(4) have p2_pos:"?p2 \<in> poss (source (As!i))"
      unfolding p by simp
    from at_p1 have *:"ctxt_of_pos_term p (source A) = (ctxt_of_pos_term ?p1 (source A) \<circ>\<^sub>c (ctxt_of_pos_term ?p2 (source (As ! i))))"
      unfolding p using ctxt_of_pos_term_append using Cons.prems(3) p by fastforce
    from Cons(3) have "ctxt_of_pos_term ?p2 (source (As!i)) = source_ctxt (ctxt_of_pos_term p' (As!i))"
      unfolding * unfolding a Inl source.simps ctxt_of_pos_term.simps source_ctxt.simps Let_def using ctxt_comp_equals Cons(5) p1_pos
      by (smt (verit, ccfv_SIG) a ctxt_of_pos_term.simps(2) hole_pos.simps(2) hole_pos_ctxt_of_pos_term list.inject poss_imp_subst_poss)
    with Cons(1,2) i p2_pos p' a Inl have IH:"possL (ctxt_of_pos_term p' (As!i))\<langle>B\<rangle> = {q \<in> possL (As!i). \<not> ?p2 \<le>\<^sub>p q} \<union> {?p2 @ q |q. q \<in> possL B}"
      by (meson fun_well_arg nth_mem)
    let ?a1="fun_poss (lhs \<alpha>)"
    let ?a2="(\<Union>j \<in> {k. k < length As \<and> k \<noteq> i}. {(var_poss_list (lhs \<alpha>)!j)@q | q. q \<in> possL(As!j)})"
    let ?a3="{?p1@q | q. q \<in> possL (As!i) \<and> \<not> ?p2 \<le>\<^sub>p q}"
    let ?a4="{?p1 @ ?p2 @ q |q. q \<in> possL B}"
    let ?b1="{q \<in> possL A. \<not> p \<le>\<^sub>p q}"
    have "?a1 \<union> ?a2 \<union> ?a3 = ?b1" proof
      {fix x assume x:"x \<in> ?a1"
        then have "\<not> ?p1 \<le>\<^sub>p x"
          by (metis append.right_neutral fun_poss_append_poss fun_poss_fun_conv fun_poss_imp_poss p1 prefix_pos_diff term.distinct(1))
        then have "\<not> p \<le>\<^sub>p x"
          unfolding p using less_eq_pos_simps(1) order_pos.order.trans by blast
        with x have "x \<in> ?b1"
          unfolding a Inl using possl_rule l lin by auto
      } moreover {fix x assume "x \<in> ?a2"
        then obtain j q where j:"j < length As" "j \<noteq> i" and q:"q \<in> possL (As ! j)" and x:"x = var_poss_list (lhs \<alpha>) ! j @ q"
          by blast
        from j have j':"j < length (var_poss_list (lhs \<alpha>))"
          using l lin by (metis length_var_poss_list linear_term_var_vars_term_list)
        with j(2) have "?p1 \<noteq> (var_poss_list (lhs \<alpha>)) !j"
          by (metis (mono_tags, lifting) distinct_remdups distinct_rev i j(1) l lin linear_term_var_vars_term_list nth_eq_iff_index_eq o_apply term.inject(1) vars_term_list_var_poss_list)
        with j' have "?p1 \<bottom> var_poss_list (lhs \<alpha>) ! j"
          using var_poss_parallel by (metis nth_mem p1 p1_pos var_poss_iff var_poss_list_sound)
        then have "\<not> p \<le>\<^sub>p x"
          unfolding p x using less_eq_pos_simps(1) order_pos.order_trans pos_less_eq_append_not_parallel by blast
        then have "x \<in> ?b1"
          unfolding a Inl possl_rule[OF l lin] x using j(1) q by blast
      } moreover {fix x assume "x \<in> ?a3"
        then obtain q where x:"x = ?p1@q" "q \<in> possL (As ! i)" "\<not> ?p2 \<le>\<^sub>p q"
          by blast
        from x(3) have "\<not> p \<le>\<^sub>p x"
          unfolding p x(1) using less_eq_pos_simps(2) by blast
        with x(2) have "x \<in> ?b1"
          unfolding a Inl possl_rule[OF l lin] x(1) using i by auto
      }
      ultimately show "?a1 \<union> ?a2 \<union> ?a3 \<subseteq> ?b1" by blast
      {fix x assume b1:"x \<in> ?b1"
        then consider "x \<in> fun_poss (lhs \<alpha>)" | "x \<in> (\<Union>i<length As. {var_poss_list (lhs \<alpha>) ! i @ q |q. q \<in> possL (As ! i)})"
          unfolding a Inl possl_rule[OF l lin] by blast
        then have "x \<in> ?a1 \<union> ?a2 \<union> ?a3" proof(cases)
          case 2
          then obtain j q where j:"j < length As" and x:"x = var_poss_list (lhs \<alpha>) ! j @ q" and q:"q \<in> possL (As!j)"
            by blast
          then show ?thesis proof(cases "j = i")
            case True
            from b1 have "\<not> ?p2 \<le>\<^sub>p q"
              unfolding p x True using less_eq_pos_simps(2) by blast
            then show ?thesis using j x q by auto
          qed auto
        qed simp
      }
      then show "?b1 \<subseteq> ?a1 \<union> ?a2 \<union> ?a3" by blast
    qed
    moreover have "possL (ctxt_of_pos_term (i # p') A)\<langle>B\<rangle> = ?a1 \<union> ?a2 \<union> ?a3 \<union> ?a4" proof-
      from l i have l':"length (take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As) = length (var_rule \<alpha>)"
        by simp
      have set:"{j. j < length As} = {j. j < length As \<and> j \<noteq> i} \<union> {i}"
        using i Collect_disj_eq by auto
      let ?args="(take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As)"
      {fix j assume "j < length As \<and> j \<noteq> i"
        with i have "?args ! j = As!j"
          by (meson nat_less_le nth_append_take_drop_is_nth_conv)
      } moreover have "?args!i = (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle>" using i
        by (simp add: nth_append_take)
      moreover from set have "(\<Union>j<length As. {var_poss_list (lhs \<alpha>) ! j @ q |q. q \<in> possL (?args ! j)}) =
                 (\<Union>j \<in> {j. j < length As \<and> j \<noteq> i}. {var_poss_list (lhs \<alpha>) ! j @ q |q. q \<in> possL (?args ! j)}) \<union> {?p1 @ q |q. q \<in> possL (?args!i)}"
        by force
      ultimately have "(\<Union>j<length As. {var_poss_list (lhs \<alpha>) ! j @ q |q. q \<in> possL (?args ! j)}) =
                 (\<Union>j \<in> {j. j < length As \<and> j \<noteq> i}. {var_poss_list (lhs \<alpha>) ! j @ q |q. q \<in> possL (As ! j)}) \<union> {?p1 @ q |q. q \<in> possL (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle>}"
        by simp
      moreover have "possL (ctxt_of_pos_term (i # p') A)\<langle>B\<rangle> = fun_poss (lhs \<alpha>) \<union>
                (\<Union>j<length As. {var_poss_list (lhs \<alpha>) ! j @ q |q. q \<in> possL (?args ! j)})"
        unfolding a Inl ctxt_of_pos_term.simps intp_actxt.simps using possl_rule[OF l' lin] i by force
      ultimately show ?thesis unfolding IH by auto
    qed
    ultimately show ?thesis using p by force
  next
    case (Inr f)
    from Cons(3,4,5) obtain p2 where p:"p = i#p2" and "p2 \<in> poss (source (As!i))" and ctxt:"ctxt_of_pos_term p2 (source (As!i)) = source_ctxt (ctxt_of_pos_term p' (As!i))"
      unfolding a Inr source.simps ctxt_of_pos_term.simps source_ctxt.simps by (smt (verit, best) Cons.prems(2) Cons.prems(3) Inr a actxt.inject ctxt_of_pos_term.simps(2) i nth_map source_poss)
    with Cons(1,2) i p' have IH:"possL (ctxt_of_pos_term p' (As!i))\<langle>B\<rangle> = {q \<in> possL (As!i). \<not> p2 \<le>\<^sub>p q} \<union> {p2 @ q |q. q \<in> possL B}"
      unfolding a Inr by (meson fun_well_arg nth_mem)
    let ?a2="(\<Union>j \<in> {k. k < length As \<and> k \<noteq> i}. {j # q | q. q \<in> possL(As!j)})"
    let ?a3="{i#q | q. q \<in> possL (As!i) \<and> \<not> p2 \<le>\<^sub>p q}"
    let ?a4="{i # p2 @ q |q. q \<in> possL B}"
    let ?b1="{q \<in> possL A. \<not> p \<le>\<^sub>p q}"
    have "?a2 \<union> ?a3 = ?b1" proof
      {fix x assume "x \<in> ?a2"
        then obtain j q where j:"j < length As" "j \<noteq> i" and q:"q \<in> possL (As ! j)" and x:"x = j # q"
          by blast
        from j q have "j#q \<in> possL A"
          unfolding a Inr by simp
        then have "x \<in> ?b1"
          unfolding x p using j(2) by simp
      } moreover {fix x assume "x \<in> ?a3"
        then obtain q where x:"x = i#q" "q \<in> possL (As ! i)" "\<not> p2 \<le>\<^sub>p q"
          by blast
        from x(3) have "\<not> p \<le>\<^sub>p x"
          unfolding p x(1) using less_eq_pos_simps(2) by simp
        with x(2) have "x \<in> ?b1"
          unfolding a Inr x(1) using i by auto
      }
      ultimately show "?a2 \<union> ?a3 \<subseteq> ?b1" by blast
      {fix x assume b1:"x \<in> ?b1"
        then have "x \<in> possL A"
          by simp
        then obtain j q where j:"j < length As" and x:"x = j # q" and q:"q \<in> possL (As!j)"
          unfolding a Inr labeled_source.simps labelposs.simps length_map by force
        then have "x \<in> ?a2 \<union> ?a3" proof(cases "j = i")
          case True
          with b1 have "\<not> p2 \<le>\<^sub>p q"
            unfolding p x using less_eq_pos_simps(2) by simp
          then show ?thesis using j x q b1 by auto
        qed simp
       }
      then show "?b1 \<subseteq> ?a2 \<union> ?a3" by blast
    qed
    moreover have "possL (ctxt_of_pos_term (i # p') A)\<langle>B\<rangle> = ?a2 \<union> ?a3 \<union> ?a4" proof-
      have l:"length (take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As) = length As"
        using i  by simp
      {fix j assume "j < length As"
        then have "(map labeled_source (take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As) ! j) = labeled_source ((take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As) ! j)"
          using nth_map l by metis
      }note map_lab=this
      have set:"{j. j < length As} = {j. j < length As \<and> j \<noteq> i} \<union> {i}"
        using i Collect_disj_eq by auto
      let ?args="(take i As @ (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle> # drop (Suc i) As)"
      {fix j assume "j < length As \<and> j \<noteq> i"
        with i have "?args ! j = As!j"
          by (meson nat_less_le nth_append_take_drop_is_nth_conv)
      } moreover have "?args!i = (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle>" using i
        by (simp add: nth_append_take)
      moreover from set have "(\<Union>j<length As. {j # q |q. q \<in> possL (?args ! j)}) =
                   (\<Union>j \<in> {j. j < length As \<and> j \<noteq> i}. {j # q |q. q \<in> possL (?args ! j)}) \<union> {i # q |q. q \<in> possL (?args!i)}"
        by force
      ultimately have "(\<Union>j<length As. {j # q |q. q \<in> possL (?args ! j)}) =
                 (\<Union>j \<in> {j. j < length As \<and> j \<noteq> i}. {j # q |q. q \<in> possL (As ! j)}) \<union> {i # q |q. q \<in> possL (ctxt_of_pos_term p' (As ! i))\<langle>B\<rangle>}"
        by simp
      moreover have "possL (ctxt_of_pos_term (i # p') A)\<langle>B\<rangle> = (\<Union>j<length As. {j # q |q. q \<in> possL (?args ! j)})"
        unfolding a Inr ctxt_of_pos_term.simps intp_actxt.simps labeled_source.simps labelposs.simps length_map l using map_lab by force
      ultimately show ?thesis unfolding IH by auto
    qed
    ultimately show ?thesis using p by force
  qed
qed

lemma single_redex_possL: (*helper lemma*)
  assumes "to_rule \<alpha> \<in> R" "p \<in> poss s" 
  shows "possL (ll_single_redex s p \<alpha>) = {p @ q |q. q \<in> fun_poss (lhs \<alpha>)}" 
proof- 
  let ?\<Delta>="ll_single_redex s p \<alpha>" 
  have *:"possL (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>)))) = labelposs (labeled_lhs \<alpha>)"
  proof-
    {fix x
      have "labelposs ((\<langle>map labeled_source (map (to_pterm \<circ> (\<lambda>pi. s |_ (p @ pi))) (var_poss_list (lhs \<alpha>)))\<rangle>\<^sub>\<alpha>) x) = {}"
        by (smt (verit) comp_apply labeled_source_simple_pterm labelposs.simps(1) length_map lhs_subst_not_var_i lhs_subst_var_i map_nth_eq_conv) 
    }
    then show ?thesis unfolding labeled_source.simps labelposs_apply_subst by blast
  qed
  have "possL ?\<Delta> = {q \<in> possL (to_pterm s). \<not> p \<le>\<^sub>p q} \<union> {p @ q |q. q \<in> possL (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>))))}"
    using label_ctxt assms by (simp add: ll_single_redex_def p_in_poss_to_pterm source_ctxt_to_pterm) 
  also have "...= {p @ q |q. q \<in> possL (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>))))}" 
    using labeled_source_simple_pterm by auto
  also have "...= {p @ q |q. q \<in> labelposs (labeled_lhs \<alpha>)}" 
    unfolding * by simp
  finally show ?thesis
    using label_poss_labeled_lhs labelposs_subs_fun_poss by fastforce 
qed
  

end

lemma labeled_poss_in_lhs:
  assumes p_pos:"p \<in> poss (source (Prule \<alpha> As))" and well:"Prule \<alpha> As \<in> wf_pterm R"
    and "get_label ((labeled_source (Prule \<alpha> As))|_p) = Some (\<alpha>, length p)" "is_Fun (lhs \<alpha>)"
  shows "p \<in> fun_poss (lhs \<alpha>)"
proof-
  from p_pos consider "p \<in> fun_poss (lhs \<alpha>)" | "\<exists>p1 p2 x. p = p1 @ p2 \<and> p1 \<in> poss (lhs \<alpha>) \<and> (lhs \<alpha>)|_p1 = Var x \<and> p2 \<in> poss ((\<langle>map source As\<rangle>\<^sub>\<alpha>) x)"
    unfolding source.simps using poss_subst_apply_term by metis
  then show ?thesis proof(cases)
    case 2
    then obtain p1 p2 x where p:"p = p1 @ p2" and p1:"p1 \<in> poss (lhs \<alpha>)" "(lhs \<alpha>)|_p1 = Var x" and p2:"p2 \<in> poss ((\<langle>map source As\<rangle>\<^sub>\<alpha>) x)"
      by blast
    then obtain i where i:"i < length (var_rule \<alpha>)" "var_rule \<alpha>!i = x"
      by (metis in_set_conv_nth set_vars_term_list subt_at_imp_supteq subteq_Var_imp_in_vars_term vars_term_list_vars_distinct)
    from p1 have p1_pos':"p1 \<in> poss (labeled_lhs \<alpha>)"
      by simp
    from p1 have p1_pos:"p1 \<in> poss (labeled_lhs \<alpha> \<cdot> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha>)"
      by (metis labeled_source.simps(3) labeled_source_to_term p p_pos poss_append_poss poss_term_lab_to_term)
    from p1 have x:"labeled_lhs \<alpha> |_p1 = Var x"
      by (metis fun_poss_term_lab_to_term label_term_to_term labeled_source_pos poss_simps(4) poss_term_lab_to_term term.sel(1) term_lab_to_term.simps(1) var_poss_iff)
    from well have l:"length As = length (var_rule \<alpha>)"
      using wf_pterm.cases by auto
    with well i have asi:"As!i \<in> wf_pterm R"
      by (metis fun_well_arg nth_mem)
    from l have lab:"labeled_source (Prule \<alpha> As) |_p = labeled_source (As!i) |_p2"
      unfolding p labeled_source.simps subt_at_append[OF p1_pos] subt_at_subst[OF p1_pos'] x using i
      by (metis (no_types, lifting) length_map lhs_subst_var_i nth_map eval_term.simps(1))
    moreover from assms(4) p1 have "length p2 < length p"
      unfolding p by auto
    moreover from p2 have "p2 \<in> poss (labeled_source (As!i))"
      using l i by (metis (no_types, lifting) labeled_source_to_term length_map lhs_subst_var_i nth_map poss_term_lab_to_term)
    ultimately have False using assms(3) asi by (simp add: label_term_max_value leD)
    then show ?thesis by simp
  qed simp
qed

context left_lin_no_var_lhs
begin 
lemma get_label_Prule: 
  assumes "Prule \<alpha> As \<in> wf_pterm R" and "p \<in> poss (source (Prule \<alpha> As))" and "get_label (labeled_source (Prule \<alpha> As) |_ p) = Some (\<beta>, 0)"
  shows "(p = [] \<and> \<alpha> = \<beta>) \<or> 
  (\<exists> p1 p2 i. p = p1@p2 \<and> i < length As \<and> var_poss_list (lhs \<alpha>)!i = p1 \<and> 
              p2 \<in> poss (source (As!i)) \<and> get_label (labeled_source (As!i)|_p2) = Some (\<beta>, 0))"
proof-
  from assms(1) have \<alpha>:"to_rule \<alpha> \<in> R"
    using wf_pterm.simps by fastforce 
  with no_var_lhs obtain f ts where lhs:"lhs \<alpha> = Fun f ts" by fastforce 
  from assms(1) have l1:"length (var_rule \<alpha>) = length As"
    using wf_pterm.cases by force 
  then have l2:"length (var_poss_list (lhs \<alpha>)) = length As" 
    using left_lin.length_var_rule[OF left_lin_axioms \<alpha>] by (simp add: length_var_poss_list) 
  from left_lin have var_rule:"var_rule \<alpha> = vars_term_list (lhs \<alpha>)"
    using \<alpha> left_linear_trs_def linear_term_var_vars_term_list by fastforce 
  then show ?thesis proof(cases "p=[]")
    case True
    from assms(3) have "\<beta> = \<alpha>" unfolding True labeled_source.simps lhs label_term.simps eval_term.simps subt_at.simps by simp
    then show ?thesis unfolding True by simp
  next
    case False
    from assms(3) have possL:"p \<in> possL (Prule \<alpha> As)"
      by (metis assms(2) get_label_imp_labelposs labeled_source_to_term option.distinct(1) poss_term_lab_to_term) 
    {assume "p \<in> fun_poss (lhs \<alpha>)" 
      then have "get_label (labeled_source (Prule \<alpha> As) |_ p) = Some (\<alpha>, length p)" 
        unfolding labeled_source.simps lhs using label_term_increase by (metis add_0) 
      with assms(3) False have False by simp
    }
    with assms(2) obtain p1 p2 x where p:"p = p1@p2" and p1:"p1 \<in> poss (lhs \<alpha>)" "lhs \<alpha> |_ p1 = Var x" and p2:"p2 \<in> poss ((\<langle>map source As\<rangle>\<^sub>\<alpha>) x)" 
      unfolding source.simps using poss_subst_apply_term[of p "lhs \<alpha>"] by metis 
    then have "p1 \<in> var_poss (lhs \<alpha>)" using var_poss_iff by blast 
    with p1 obtain i where i:"i < length As" "vars_term_list (lhs \<alpha>) !i = x" "var_poss_list (lhs \<alpha>) ! i = p1"
      using l2 by (metis in_set_conv_nth length_var_poss_list term.inject(1) var_poss_list_sound vars_term_list_var_poss_list) 
    with p2 l1 have p2_poss:"p2 \<in> poss (source (As!i))"
      by (smt (verit, del_insts) \<alpha> case_prodD left_lin left_linear_trs_def length_map lhs_subst_var_i linear_term_var_vars_term_list nth_map)
    from p1 have "labeled_source (Prule \<alpha> As) |_ p = ((\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) x)|_p2"
      unfolding labeled_source.simps p by (smt (verit) assms(2) eval_term.simps(1) label_term_to_term labeled_source.simps(3) labeled_source_to_term p poss_term_lab_to_term subt_at_subst subterm_poss_conv var_label_term)  
    moreover from var_rule have "map (\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) (vars_term_list (lhs \<alpha>)) = map labeled_source As"
      by (metis apply_lhs_subst_var_rule l1 length_map) 
    ultimately have "labeled_source (Prule \<alpha> As) |_ p = (labeled_source (As!i))|_p2" 
      using i by (metis map_nth_conv) 
    with assms(3) have "get_label (labeled_source (As ! i) |_ p2) = Some (\<beta>, 0)" by force
    with p2_poss i p show ?thesis by blast
  qed
qed
end

text\<open>If the labeled source of a proof term @{term A} has the shape @{term "t \<cdot> \<sigma>"} where all 
function symbols in @{term t} are unlabeled, then @{term A} matches @{term t} with some substitution 
@{term \<tau>}.\<close>
context no_var_lhs
begin
lemma pterm_source_substitution:
assumes "A \<in> wf_pterm R"
  and "source A = t \<cdot> \<sigma>" and "linear_term t"
  and "\<forall>p \<in> fun_poss t. p \<notin> possL A"
shows "A = (to_pterm t) \<cdot> (mk_subst Var (match_substs (to_pterm t) A))"
  using assms proof(induct A arbitrary:t \<sigma>)
  case (1 x)
  from 1(1) obtain y where y:"t = Var y"
    using subst_apply_eq_Var  by (metis source.simps(1))
  have match:"match_substs (Var y) (Var x) = [(y, Var x)]"
    unfolding match_substs_def vars_term_list.simps poss_list.simps by simp
  show ?case unfolding y to_pterm.simps match
    by simp
next
  case (2 As f)
  show ?case proof(cases t)
    case (Var x)
    have match:"match_substs (Var x) (Pfun f As) = [(x, Pfun f As)]"
      unfolding match_substs_def vars_term_list.simps poss_list.simps by simp
    then show ?thesis unfolding Var to_pterm.simps match by simp
  next
    case (Fun g ts)
    from 2(2) have f:"f = g"
      unfolding Fun by simp
    from 2(2) have l:"length ts = length As"
      unfolding Fun eval_term.simps using map_eq_imp_length_eq by fastforce
    {fix i assume i:"i < length As"
      from 2(2) i have "source (As!i) = (ts!i) \<cdot> \<sigma>"
        unfolding Fun f by (smt (verit, best) eval_term.simps(2) l nth_map source.simps(2) term.sel(4)) 
      moreover from 2(3) i l have lin_tsi:"linear_term (ts!i)"
        unfolding Fun by simp
      moreover have "(\<forall>p\<in>fun_poss (ts!i). p \<notin> possL (As!i))" proof
        fix p assume "p \<in> fun_poss (ts!i)"
        then have "i#p \<in> fun_poss (Fun f ts)"
          using i l by simp
        with 2(4) have "i#p \<notin> possL (Pfun f As)"
          unfolding Fun f by fastforce
        then show "p \<notin> possL (As!i)"
          using i unfolding labeled_source.simps labelposs.simps by simp
      qed
      ultimately have IH:"As!i = to_pterm (ts!i) \<cdot> mk_subst Var (match_substs (to_pterm (ts!i)) (As!i))"
        using 2(1) i nth_mem by blast
      have "As!i = to_pterm (ts!i) \<cdot> mk_subst Var (match_substs (to_pterm t) (Pfun g As))" proof-
        {fix x assume "x \<in> vars_term (to_pterm (ts!i))"
          then obtain j where j:"vars_term_list (ts!i) !j = x" "j < length (vars_term_list (ts!i))"
            by (metis in_set_conv_nth set_vars_term_list vars_to_pterm)
          then have j':"j < length (map ((|_) (As ! i)) (var_poss_list (to_pterm (ts ! i))))"
            by (metis length_map length_var_poss_list var_poss_list_to_pterm)
          let ?qj="var_poss_list (to_pterm (ts!i)) !j"
          have map_j:"(map ((|_) (As ! i)) (var_poss_list (to_pterm (ts ! i))))!j = (As!i)|_?qj"
            using j' by simp
          have "distinct (vars_term_list (ts!i))"
            using lin_tsi by (metis distinct_remdups distinct_rev linear_term_var_vars_term_list o_apply)
          then have dist1:"distinct (map fst (match_substs (to_pterm (ts!i)) (As!i)))"
            unfolding match_substs_def by (metis length_map length_var_poss_list map_fst_zip vars_to_pterm)
          have "distinct (vars_term_list t)"
            by (metis "2.prems"(2) distinct_remdups distinct_rev linear_term_var_vars_term_list o_apply)
          then have dist2:"distinct (map fst (match_substs (to_pterm t) (Pfun g As)))"
            unfolding match_substs_def by (metis length_map length_var_poss_list map_fst_zip vars_to_pterm)
          have "(x, (As!i)|_?qj) \<in> set (match_substs (to_pterm (ts!i)) (As!i))"
            unfolding match_substs_def using map_j j j' by (metis (no_types, lifting) in_set_conv_nth length_zip min_less_iff_conj nth_zip vars_to_pterm)
          then have sub1:"mk_subst Var (match_substs (to_pterm (ts!i)) (As!i)) x = As!i |_ ?qj"
            using dist1 map_of_eq_Some_iff unfolding mk_subst_def by simp
          let ?j'="(sum_list (map (length \<circ> vars_term_list) (take i ts)) + j)"
          have x2:"vars_term_list t ! ?j' = x"
            unfolding Fun vars_term_list.simps using j(1) by (smt (verit, best) concat_nth i j(2) l length_map map_map nth_map take_map)
          have lj':"?j' < length (vars_term_list (to_pterm t))" unfolding vars_to_pterm unfolding Fun to_pterm.simps vars_term_list.simps
            using i j(2) l concat_nth_length by (metis List.map.compositionality length_map nth_map take_map)
          then have j'_var_poss:"?j' < length (var_poss_list (to_pterm t))"
            by (metis length_var_poss_list)
          then have lj'':"?j' < length (map ((|_) (Pfun g As)) (var_poss_list (to_pterm t)))"
            by (metis length_map length_var_poss_list)
          have "var_poss_list (to_pterm t) ! ?j' = i#?qj"
          proof- (*Can structure be improved? The details provided here seem overkill.*)
            have l_zip:"i < length (zip [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)))"
              by (simp add: i l)
            have zip:"zip [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)) ! i = (i, var_poss_list (to_pterm (ts ! i)))"
              using nth_zip by (simp add: i l)
            have map2:"map2 (\<lambda>i. map ((#) i)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)) ! i ! j = i#?qj"
              unfolding nth_map[OF l_zip] zip using j' by auto
            from l_zip have i'':"i < length (map2 (\<lambda>x. map ((#) x)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)))"
              by simp
            have j'':"j < length (map2 (\<lambda>x. map ((#) x)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)) ! i)"
              unfolding nth_map[OF l_zip] zip using j(2) by (metis case_prod_conv length_map length_var_poss_list vars_to_pterm)
            {fix k assume k:"k < length ts"
              then have zip:"zip [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)) ! k = (k, var_poss_list (to_pterm (ts ! k)))"
                using nth_zip by simp
              then have "map2 (\<lambda>x. map ((#) x)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)) ! k =
                map ((#) k) (var_poss_list (to_pterm (ts ! k)))"
                using k by simp
              then have "length ((map2 (\<lambda>x. map ((#) x)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)))!k) =
                     length (vars_term_list (ts!k))"
                using  length_var_poss_list vars_to_pterm by (metis length_map)
              with k have "(map length (map2 (\<lambda>x. map ((#) x)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts))))!k =
                (map (length \<circ> vars_term_list) ts) ! k" by simp
            }
            moreover have "length (map length (map2 (\<lambda>x. map ((#) x)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)))) = length ts"
              by simp
            ultimately have "(map length (map2 (\<lambda>x. map ((#) x)) [0..<length (map to_pterm ts)] (map var_poss_list (map to_pterm ts)))) =
              (map (length \<circ> vars_term_list) ts)" by (simp add: map_nth_eq_conv)
            then show ?thesis
              unfolding Fun to_pterm.simps var_poss_list.simps using concat_nth[OF i'' j''] unfolding map2 take_map[symmetric] by simp
          qed
          with lj'' have "(map ((|_) (Pfun g As)) (var_poss_list (to_pterm t)))!?j' = Pfun g As |_ (i#?qj)"
            by force
          with x2 have "(x, Pfun g As |_(i#?qj)) \<in> set (match_substs (to_pterm t) (Pfun g As))"
            unfolding match_substs_def using lj' lj'' by (metis (no_types, lifting) in_set_conv_nth length_zip min_less_iff_conj nth_zip vars_to_pterm)
          then have sub2:"mk_subst Var (match_substs (to_pterm t) (Pfun g As)) x = Pfun g As |_ (i#?qj)"
            using dist2 map_of_eq_Some_iff unfolding mk_subst_def by simp
          from sub1 sub2 have "mk_subst Var (match_substs (to_pterm (ts!i)) (As!i)) x = mk_subst Var (match_substs (to_pterm t) (Pfun g As)) x"
            by simp
        }
        then show ?thesis using IH
          using term_subst_eq by force
      qed
    }
    then show ?thesis
      unfolding Fun f eval_term.simps to_pterm.simps using l by (metis (mono_tags, lifting) length_map map_nth_eq_conv)
  qed
next
  case (3 \<alpha> As)
  show ?case proof(cases t)
    case (Var x)
    have match:"match_substs (Var x) (Prule \<alpha> As) = [(x, Prule \<alpha> As)]"
      unfolding match_substs_def vars_term_list.simps poss_list.simps by simp
    then show ?thesis unfolding Var to_pterm.simps match by simp
  next
    case (Fun g ts)
    from 3(1) no_var_lhs obtain f ss where lhsa:"lhs \<alpha> = Fun f ss"
      by blast
    have "[] \<in> possL (Prule \<alpha> As)"
      unfolding labeled_source.simps lhsa label_term.simps labelposs.simps eval_term.simps by simp
    with 3(6) have False unfolding Fun by simp
    then show ?thesis by simp
  qed
qed

lemma unlabeled_source_to_pterm: (*this is redundant, basically same lemma as above \<rightarrow> get rid of one of them?*)
assumes "labeled_source A = s \<cdot> \<tau>"
    and "linear_term s" and "A \<in> wf_pterm R"
    and "labelposs s = {}"
  shows "\<exists>As. A = to_pterm (term_lab_to_term s) \<cdot> (mk_subst Var (zip (vars_term_list s) As)) \<and> length (vars_term_list s) = length As"
  using assms proof(induct s arbitrary:A)
  case (Var x)
  let ?As ="[A]"
  have "A = to_pterm (term_lab_to_term (Var x)) \<cdot> mk_subst Var (zip (vars_term_list (Var x)) ?As)"
    unfolding term_lab_to_term.simps to_pterm.simps vars_term_list.simps zip_Cons_Cons zip_Nil mk_subst_def by simp
  then show ?case
    by (smt (verit) length_nth_simps(1) list.size(4) vars_term_list.simps(1))
next
  case (Fun fl ts)
  from Fun(5) obtain f where f:"fl = (f, None)"
    by (metis empty_iff empty_pos_in_poss get_label.simps(2) get_label_imp_labelposs prod.exhaust_sel subt_at.simps(1))
  with Fun(2) have "\<exists>As. A = Pfun f As \<and> length As = length ts" proof(cases A)
    case (Pfun g As)
    from Fun(2) show ?thesis
      unfolding Pfun f labeled_source.simps using map_eq_imp_length_eq by auto
  next
    case (Prule \<alpha> As)
    from Fun(4) no_var_lhs obtain g ss where lhs:"lhs \<alpha> = Fun g ss"
      by (metis Inl_inject Prule case_prodD is_FunE is_Prule.simps(1) is_Prule.simps(3) term.distinct(1) term.sel(2) wf_pterm.simps)
    from Fun(2) show ?thesis
      unfolding Prule f lhs labeled_source.simps by force
  qed simp
  then obtain As where as:"A = Pfun f As" and l:"length As = length ts"
    by blast
  {fix i assume i:"i < length ts"
    with Fun(2) have "labeled_source (As!i) = (ts!i) \<cdot> \<tau>"
      unfolding as by (smt (verit, best) eval_term.simps(2) l labeled_source.simps(2) nth_map term.inject(2))
    moreover from i Fun(3) have "linear_term (ts!i)"
      by simp
    moreover from i Fun(4) have "As!i \<in> wf_pterm R"
      unfolding as by (metis l fun_well_arg nth_mem)
    moreover from i Fun(5) have "labelposs (ts!i) = {}"
      unfolding f labelposs.simps by blast
    ultimately have "\<exists>As'. (As!i) = to_pterm (term_lab_to_term (ts!i)) \<cdot> mk_subst Var (zip (vars_term_list (ts!i)) As') \<and> length (vars_term_list (ts!i)) = length As'"
      using Fun(1) i by force
  }
  then obtain As' where l'':"length As' = length ts"
    and IH:"(\<forall>i < length ts. (As!i) = to_pterm (term_lab_to_term (ts!i)) \<cdot> mk_subst Var (zip (vars_term_list (ts!i)) (As'!i)) \<and> length (vars_term_list (ts!i)) = length (As'!i))"
    using Ex_list_of_length_P[where P="\<lambda>As' i. As ! i = to_pterm (term_lab_to_term (ts ! i)) \<cdot> mk_subst Var (zip (vars_term_list (ts ! i)) As') \<and> length (vars_term_list (ts!i)) = length As'"] l by blast
  then have l':"length As' = length (map to_pterm (map term_lab_to_term ts))"
    by simp
  have vars_list:"map vars_term_list (map to_pterm (map term_lab_to_term ts)) = map vars_term_list ts"
    by (smt (verit, best) length_map map_nth_eq_conv vars_term_list_term_lab_to_term vars_to_pterm)
  have "map vars_term (map to_pterm (map term_lab_to_term ts)) = map vars_term ts"
    using vars_term_list_term_lab_to_term by (smt (verit, ccfv_threshold) length_map map_nth_eq_conv set_vars_term_list vars_to_pterm)
  then have part:"is_partition (map vars_term (map to_pterm (map term_lab_to_term ts)))"
    using Fun(3) by (metis linear_term.simps(2))
  have *:"\<forall>i < length ts. to_pterm (term_lab_to_term (ts!i)) \<cdot> mk_subst Var (concat (map2 zip (map vars_term_list (map to_pterm (map term_lab_to_term ts))) As')) = As!i"
    using mk_subst_partition_special[OF l' part] unfolding length_map using nth_map IH
    by (smt (verit, best) length_map vars_term_list_term_lab_to_term vars_to_pterm)
  from IH have "\<forall>i < length ts. length (vars_term_list (to_pterm (term_lab_to_term (ts! i)))) = length (As' ! i)"
    by (metis vars_term_list_term_lab_to_term vars_to_pterm)
  then have ls:"\<forall>i < length ts. length (map vars_term_list (map to_pterm (map term_lab_to_term ts)) ! i) = length (As' ! i)"
    using nth_map by simp
  then have cc:"concat (map2 zip (map vars_term_list (map to_pterm (map term_lab_to_term ts))) As') = zip (concat (map vars_term_list ts)) (concat As')"
    unfolding vars_list using concat_map2_zip by (metis l' length_map)
  have "A = to_pterm (term_lab_to_term (Fun fl ts)) \<cdot> mk_subst Var (zip (vars_term_list (Fun fl ts)) (concat As'))"
    unfolding f term_lab_to_term.simps to_pterm.simps fst_conv eval_term.simps as vars_term_list.simps cc[symmetric] using * by (simp add: l list_eq_iff_nth_eq)
  moreover have "length (vars_term_list (Fun fl ts)) = length (concat As')"
    unfolding vars_term_list.simps
    using l'' ls by (metis eq_length_concat_nth length_map vars_list)
  ultimately show ?case by auto
qed
end

lemma labels_intersect_label_term:
  assumes "term_lab_to_term A = t \<cdot> (term_lab_to_term \<circ> \<sigma>)"
    and "linear_term t"
  and "labelposs A \<inter> labelposs ((label_term \<alpha> n t) \<cdot> \<sigma>) = {}"
shows "\<exists>As. A = term_to_term_lab t \<cdot> (mk_subst Var (zip (vars_term_list t) As)) \<and> length As = length (vars_term_list t)"
  using assms proof(induct t arbitrary:A n)
  case (Var x)
  have "A = mk_subst Var (zip [x] [A]) x"
    unfolding mk_subst_def by simp
  then show ?case unfolding term_to_term_lab.simps eval_term.simps vars_term_list.simps by fastforce
next
  case (Fun f ts)
  from Fun(2) obtain lab ss where a:"A = Fun (f, lab) ss"
    using term_lab_to_term.simps by (smt (verit, ccfv_threshold) eroot.cases fst_conv old.prod.exhaust eval_term.simps(2) term.distinct(1) term.sel(2))
  from Fun(4) have lab:"lab = None"
    unfolding a using insertCI by auto
  from Fun(2) have l:"length ts = length ss"
    unfolding a by (metis length_map eval_term.simps(2) term.sel(4) term_lab_to_term.simps(2))
  {fix i assume i:"i < length ts"
    with Fun(2) have "term_lab_to_term (ss!i) = ts!i \<cdot> (term_lab_to_term \<circ> \<sigma>)"
      unfolding a term_lab_to_term.simps eval_term.simps fst_conv by (metis l nth_map term.inject(2))
    moreover from i Fun(3) have "linear_term (ts!i)"
      by simp
    moreover have "labelposs (ss!i) \<inter> labelposs (label_term \<alpha> (n+1) (ts!i) \<cdot> \<sigma>) = {}"
    proof-
      {fix q assume q1:"q \<in> labelposs (ss!i)" and q2:"q \<in> labelposs (label_term \<alpha> (n+1) (ts!i) \<cdot> \<sigma>)"
        from q1 i l have "i#q \<in> labelposs A"
          unfolding a lab label_term.simps labelposs.simps by simp
        moreover from q2 i have "i#q \<in> labelposs ((label_term \<alpha> n (Fun f ts)) \<cdot> \<sigma>)"
          unfolding label_term.simps eval_term.simps labelposs.simps length_map by simp
        ultimately have False
          using Fun(4) by blast
      }
      then show ?thesis
        by blast
    qed
    ultimately have "\<exists>As. ss!i = term_to_term_lab (ts!i) \<cdot> (mk_subst Var (zip (vars_term_list (ts!i)) As)) \<and> length As = length (vars_term_list (ts!i))"
      using Fun(1) i nth_mem by blast
  }
  then obtain Ass where l':"length Ass = length ts"
    and IH:"(\<forall>i < length ts. (ss!i) = (term_to_term_lab (ts!i)) \<cdot> mk_subst Var (zip (vars_term_list (ts!i)) (Ass!i)) \<and> length (Ass!i) = length (vars_term_list (ts!i)))"
    using Ex_list_of_length_P[where P="\<lambda>Ass i. ss ! i = (term_to_term_lab (ts ! i)) \<cdot> mk_subst Var (zip (vars_term_list (ts ! i)) Ass) \<and> length Ass = length (vars_term_list (ts!i))"] l by blast
  let ?As="concat Ass"
  from l' have l'':"length Ass = length (map term_to_term_lab ts)"
    by simp
  have vars_list:"map vars_term_list (map term_to_term_lab ts) = map vars_term_list ts"
    using vars_term_list_term_to_term_lab by auto
  have "map vars_term (map term_to_term_lab ts) = map vars_term ts"
    using vars_term_list_term_to_term_lab by (smt (verit, ccfv_threshold) length_map map_nth_eq_conv set_vars_term_list vars_to_pterm)
  then have part:"is_partition (map vars_term (map term_to_term_lab ts))"
    using Fun(3) by (metis linear_term.simps(2))
  have *:"\<forall>i < length ts. (term_to_term_lab (ts!i)) \<cdot> mk_subst Var (concat (map2 zip (map vars_term_list (map term_to_term_lab ts)) Ass)) = ss!i"
    using mk_subst_partition_special[OF l'' part] unfolding length_map using nth_map IH
    by (smt (verit, best) length_map vars_term_list_term_to_term_lab vars_to_pterm)
  from IH have "\<forall>i < length ts. length (vars_term_list (term_to_term_lab (ts! i))) = length (Ass ! i)"
    by (metis vars_term_list_term_to_term_lab)
  then have ls:"\<forall>i < length ts. length (map vars_term_list (map term_to_term_lab ts) ! i) = length (Ass ! i)"
    using nth_map by simp
  then have cc:"concat (map2 zip (map vars_term_list (map term_to_term_lab ts)) Ass) = zip (concat (map vars_term_list ts)) (concat Ass)"
    unfolding vars_list using concat_map2_zip by (metis l' length_map)
  have "A = term_to_term_lab (Fun f ts) \<cdot> mk_subst Var (zip (vars_term_list (Fun f ts)) ?As)"
    unfolding term_to_term_lab.simps eval_term.simps vars_term_list.simps a lab cc[symmetric] using * by (simp add: l list_eq_iff_nth_eq)
  moreover from IH l' have l'':"length ?As = length (vars_term_list (Fun f ts))"
    unfolding vars_term_list.simps by (simp add: eq_length_concat_nth)
  ultimately show ?case
    by blast
qed

lemma labeled_wf_pterm_rule_in_TRS:
  assumes "A \<in> wf_pterm R" and "p \<in> poss (labeled_source A)" 
    and "get_label (labeled_source A |_ p) = Some (\<alpha>, n)" 
  shows "to_rule \<alpha> \<in> R"
  using assms proof(induct A arbitrary: p n)
  case (2 ts f)
  from 2(2,3) obtain i p' where p:"p = i#p'" "i < length ts" "p' \<in> poss (labeled_source (ts!i))" "get_label (labeled_source (ts!i) |_ p') = Some (\<alpha>, n)" 
    unfolding labeled_source.simps get_label.simps by auto 
  with 2(1) show ?case
    using nth_mem by blast
next
  case (3 \<beta> As)
  from 3(4) consider "p \<in> fun_poss (labeled_lhs \<beta>)" | "(\<exists>p1 p2 x. p = p1@p2
                                        \<and> p1 \<in> poss (labeled_lhs \<beta>) \<and> (labeled_lhs \<beta>)|_p1 = Var x
                                        \<and> p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)
                                        \<and> (labeled_source (Prule \<beta> As))|_p = ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)|_p2)"
    unfolding labeled_source.simps by (meson poss_is_Fun_fun_poss poss_subst_choice)
  then show ?case proof(cases)
    case 1
    then have "p \<in> fun_poss (lhs \<beta>)"
      by (simp add: fun_poss_label_term)
    then have "get_label ((labeled_source (Prule \<beta> As))|_p) = Some (\<beta>, length p)"
      unfolding labeled_source.simps by (simp add: label_term_increase)
    with 3(1,5) show ?thesis by auto
  next
    case 2
    then obtain p1 p2 x where p1p2:"p = p1 @ p2" and x:"p1 \<in> poss (labeled_lhs \<beta>) \<and> labeled_lhs \<beta> |_ p1 = Var x"
       and p2:"p2 \<in> poss ((\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x)"
       and lab:"labeled_source (Prule \<beta> As) |_ p = (\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x |_ p2"
      by blast
    from x have "x \<in> vars_term (lhs \<beta>)"
      by (metis subt_at_imp_supteq subteq_Var_imp_in_vars_term vars_term_labeled_lhs)
    with x obtain i where i:"i < length (var_rule \<beta>) \<and> (var_rule \<beta>)!i = x"
      by (metis in_set_conv_nth set_vars_term_list vars_term_list_vars_distinct)
    with 3(2) have *:"(\<langle>map labeled_source As\<rangle>\<^sub>\<beta>) x = labeled_source (As!i)"
      by (metis (no_types, lifting) length_map lhs_subst_var_i nth_map)
    with 3(5) lab have "get_label ((labeled_source (As!i))|_p2) = Some (\<alpha>, n)"
      by simp
    with 3(3) p2 i 3(2) * show ?thesis by force
  qed
qed simp

context no_var_lhs
begin
lemma unlabeled_above_p:
  assumes "A \<in> wf_pterm R"
    and "p \<in> poss (source A)"
    and "\<forall> r. r <\<^sub>p p \<longrightarrow> r \<notin> possL A"
  shows "p \<in> poss A \<and> labeled_source A|_p = labeled_source (A|_p)"
  using assms proof(induct p arbitrary: A)
  case (Cons i p)
  from Cons(3) obtain f ts where f:"source A = Fun f ts" and i:"i < length ts" and p:"p \<in> poss (ts!i)"
    using args_poss by blast
  from Cons(4) have "[] \<notin> possL A"
    by (simp add: order_pos.less_le)
  then have no_lab:"get_label (labeled_source A) = None"
    by (metis empty_pos_in_poss get_label_imp_labelposs subt_at.simps(1))
  from Cons(3) obtain f' As where a:"A = Fun f' As"
    by (metis Cons_poss_Var eroot.cases source.simps(1))
  then have f':"f' = Inr f" proof(cases A)
    case (Pfun g Bs)
    then show ?thesis using f Pfun a by simp
  next
    case (Prule \<alpha> Bs)
    with Cons(2) obtain g ss where g:"lhs \<alpha> = Fun g ss"
      using no_var_lhs by (metis Inl_inject case_prodD is_Prule.simps(1) is_Prule.simps(3) term.collapse(2) term.distinct(1) term.sel(2) wf_pterm.simps) 
    then show ?thesis using no_lab unfolding Prule by simp
  qed simp
  from i a have i':"i < length As"
    using f f' by force
  from Cons(3) have "p \<in> poss (source (As!i))"
    unfolding a f' by auto
  moreover
  {fix r assume "r \<in> poss (source (As!i))" and le:"r <\<^sub>p p"
    then have "i#r \<in> poss (labeled_source A)"
      unfolding a f' using i' by simp
    moreover from le have "i#r <\<^sub>p i#p"
      by simp
    ultimately have "i#r \<notin> possL A"
      using Cons(4) by blast
    then have "r \<notin> possL (As!i)"
      unfolding a f' labeled_source.simps using i' by force
  }
  ultimately have "p \<in> poss (As!i) \<and> labeled_source (As!i) |_ p = labeled_source ((As!i) |_ p)"
    using Cons(1,2) i' unfolding a f' by (meson fun_well_arg nth_mem possL_subset_poss_source subsetD)
  with i' a f' show ?case
    by simp
qed simp
end

lemma (in single_redex) labeled_source_at_pq:"labeled_source (A|_q) = (labeled_source A)|_p"
  using a pq q p a_well proof(induct q arbitrary:p A)
  case Nil
  then have "p = []"
    by (simp add: subt_at_ctxt_of_pos_term subt_at_id_imp_eps)
  then show ?case
    by simp
next
  case (Cons i q)
  from Cons(4) obtain fs Bs where a:"A = Fun fs Bs" and i:"i < length Bs" and q:"q \<in> poss (Bs!i)"
    using args_poss by blast
  let ?As = "map (\<lambda>j. (Bs!i) |_ (q @ [j])) [0..<length (var_rule \<alpha>)]"
  have "(map (\<lambda>ia. A |_ ((i # q) @ [ia])) [0..<length (var_rule \<alpha>)]) = ?As"
    unfolding a by simp
  with a i q Cons(2,4) have bsi:"Bs!i = (ctxt_of_pos_term q (Bs!i))\<langle>Prule \<alpha> ?As\<rangle>"
    by (metis ctxt_supt_id subt_at.simps(2) subt_at_ctxt_of_pos_term)
  from Cons(6) have bi_well:"Bs ! i \<in> wf_pterm R"
    unfolding a by (meson fun_well_arg i nth_mem)
  show ?case proof(cases fs)
    case (Inl \<beta>)
    from Cons(6) have lin:"linear_term (lhs \<beta>)"
      unfolding a Inl using left_lin left_linear_trs_def term.inject(2) wf_pterm.cases by fastforce
    from Cons(6) have is_Fun:"is_Fun (lhs \<beta>)"
      unfolding a Inl using no_var_lhs using wf_pterm.cases by auto
    from Cons(6) have l_bs:"length Bs = length (var_rule \<beta>)"
      unfolding a Inl using wf_pterm.cases by auto
    obtain p1 p2 where p:"p = p1@p2" and p1:"p1 = var_poss_list (lhs \<beta>) ! i" and p2:"p2 \<in> poss (source (Bs!i))"
      using ctxt_rule_obtain_pos Cons(4,5,3) lin l_bs unfolding a Inl by metis
    have ctxt:"ctxt_of_pos_term p2 (source (Bs ! i)) = source_ctxt (ctxt_of_pos_term q (Bs ! i))"
    proof-
      from p1 have p1_pos:"p1 \<in> poss (lhs \<beta>)"
        using i l_bs lin by (metis length_var_poss_list linear_term_var_vars_term_list nth_mem var_poss_imp_poss var_poss_list_sound)
      from p1_pos have p1':"p1 \<in> poss (lhs \<beta> \<cdot> \<langle>map source Bs\<rangle>\<^sub>\<beta>)"
        by simp
      from p1 have p1'':"var_poss_list (lhs \<beta>) ! length (take i Bs) = p1"
        using i by force
      have *:"lhs \<beta> \<cdot> \<langle>map source Bs\<rangle>\<^sub>\<beta> |_ p1 = source (Bs!i)"
        unfolding p1 using l_bs i
        by (smt (verit) length_map lhs_subst_var_i lin linear_term_var_vars_term_list nth_map p1 p1_pos eval_term.simps(1) subt_at_subst vars_term_list_var_poss_list)
      from Cons(3) show ?thesis
        unfolding a Inl p source.simps ctxt_of_pos_term.simps source_ctxt.simps Let_def ctxt_of_pos_term_append[OF p1'] * p1''
        using ctxt_comp_equals[OF p1'] p1_pos using poss_imp_subst_poss by blast
    qed
    from Cons(1)[OF bsi ctxt q p2 bi_well] have IH:" labeled_source (Bs ! i |_ q) = labeled_source (Bs ! i) |_ p2"
      by presburger
    from p1 have "p1 = var_poss_list (labeled_lhs \<beta>) ! i"
      by (simp add: var_poss_list_labeled_lhs)
    moreover then have "(labeled_lhs \<beta>)|_p1 = Var (vars_term_list (lhs \<beta>)!i)"
      by (metis i l_bs lin linear_term_var_vars_term_list vars_term_list_labeled_lhs vars_term_list_var_poss_list)
    ultimately show ?thesis
      unfolding a Inl using i IH unfolding subt_at.simps p labeled_source.simps
      by (smt (verit, ccfv_threshold) apply_lhs_subst_var_rule filter_cong l_bs length_map length_var_poss_list lin linear_term_var_vars_term_list map_nth_conv nth_mem poss_imp_subst_poss eval_term.simps(1) subt_at_append subt_at_subst var_poss_imp_poss var_poss_list_sound vars_term_list_labeled_lhs)
  next
    case (Inr f)
    from Cons(3,5) obtain p' where p:"p = i#p'" and p':"p' \<in> poss (source (Bs!i))"
      by (metis Cons.prems(3) Inr a source_poss)
    from Cons(3) have ctxt:"ctxt_of_pos_term p' (source (Bs ! i)) = source_ctxt (ctxt_of_pos_term q (Bs ! i))"
      unfolding a Inr p by (simp add: i)
    from Cons(1)[OF bsi ctxt q p' bi_well] have IH:"labeled_source (Bs ! i |_ q) = labeled_source (Bs ! i) |_ p'"
      by presburger
    then show ?thesis
      unfolding a Inr p using i by simp
  qed
qed

context left_lin
begin
lemma single_redex_label:
  assumes "\<Delta> = ll_single_redex s p \<alpha>" "p \<in> poss s" "q \<in> poss (source \<Delta>)" "to_rule \<alpha> \<in> R" 
    and "get_label (labeled_source \<Delta> |_q) = Some (\<beta>, n)"
  shows "\<alpha> = \<beta> \<and> (\<exists>q'. q = p@q' \<and> length q' = n \<and> q' \<in> fun_poss (lhs \<alpha>))"
proof-
  from assms have wf:"\<Delta> \<in> wf_pterm R" 
    using single_redex_wf_pterm left_lin left_linear_trs_def by fastforce 
  from assms have "q \<in> possL \<Delta>"
    using get_label_imp_labelposs by force
  then obtain q' where q:"q = p@q'" and q':"q' \<in> fun_poss (lhs \<alpha>)" 
    unfolding assms(1) using single_redex_possL[OF assms(4,2)] by auto 
  from assms have "labeled_source \<Delta> = (ctxt_of_pos_term p (labeled_source (to_pterm s)))\<langle>labeled_source (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>))))\<rangle>" 
    using label_source_ctxt by (simp add: ll_single_redex_def p_in_poss_to_pterm source_ctxt_to_pterm) 
  then have "labeled_source \<Delta> |_q = labeled_source (Prule \<alpha> (map (to_pterm \<circ> (\<lambda>pi. s|_(p@pi))) (var_poss_list (lhs \<alpha>)))) |_q'" 
    unfolding q using assms(2) by (metis hole_pos_ctxt_of_pos_term hole_pos_poss labeled_source_to_term poss_term_lab_to_term replace_at_subt_at source_to_pterm subt_at_append) 
  then have "get_label (labeled_source \<Delta> |_q) = get_label (labeled_lhs \<alpha>|_q')" 
    using get_label_at_fun_poss_subst q' by force
  also have "... = Some (\<alpha>, size q')" 
    using get_label_label_term q' by fastforce
  finally show ?thesis using assms q q' by force
qed 
end


subsection\<open>Measuring Overlap\<close>
abbreviation measure_ov :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm \<Rightarrow> nat"
  where "measure_ov A B \<equiv> card ((possL A) \<inter> (possL B))"

lemma finite_labelposs: "finite (labelposs A)"
  by (meson finite_fun_poss labelposs_subs_fun_poss rev_finite_subset)

lemma finite_possL: "finite (possL A)"
  by (simp add: finite_labelposs)

lemma measure_ov_symm: "measure_ov A B = measure_ov B A"
  by (simp add: Int_commute)

lemma measure_lhs_subst:
  assumes l:"length As = length Bs"
  shows "card ((labelposs ((label_term \<alpha> j t) \<cdot> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha>)) \<inter>
         (labelposs (labeled_source (to_pterm t) \<cdot> \<langle>map labeled_source Bs\<rangle>\<^sub>\<alpha>)))
        = (\<Sum>x\<leftarrow>vars_term_list t. measure_ov ((\<langle>As\<rangle>\<^sub>\<alpha>) x) ((\<langle>Bs\<rangle>\<^sub>\<alpha>) x))"
  using assms proof(induct t arbitrary:j)
case (Var x)
  show ?case proof(cases "\<exists>i < length As. i < length (var_rule \<alpha>) \<and> x = (var_rule \<alpha>)!i")
    case True
    then obtain i where i:"x = (var_rule \<alpha>)!i" and il:"i < length As"  and il2:"i < length (var_rule \<alpha>)" by auto
    then have a:"(\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) x = labeled_source (As!i)"
      using lhs_subst_var_i by (metis (no_types, lifting) length_map nth_map)
    from i il il2 l have b:"(\<langle>map labeled_source Bs\<rangle>\<^sub>\<alpha>) x = labeled_source (Bs!i)"
      using lhs_subst_var_i  by (metis (no_types, lifting) length_map nth_map)
    from i show ?thesis unfolding vars_term_list.simps sum_list_elem
      unfolding to_pterm.simps label_term.simps labeled_source.simps eval_term.simps
      unfolding a b using lhs_subst_var_i l il il2 by metis
  next
    case False
    then have a:"(\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) x = Var x"
      using lhs_subst_not_var_i by (metis length_map)
    from False l have b:"(\<langle>map labeled_source Bs\<rangle>\<^sub>\<alpha>) x = Var x"
      using lhs_subst_not_var_i by (metis length_map)
    from False l have "possL ((\<langle>As\<rangle>\<^sub>\<alpha>) x) \<inter> possL ((\<langle>Bs\<rangle>\<^sub>\<alpha>) x) = {}"
      unfolding term.set(3) using lhs_subst_not_var_i
      by (metis inf.idem labeled_source.simps(1) labelposs.simps(1))
    then show ?thesis unfolding label_term.simps to_pterm.simps labeled_source.simps eval_term.simps a b
       by auto
  qed
next
  case (Fun f ts)
  let ?as="(map (\<lambda>t. t \<cdot> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) (map (label_term \<alpha> (j + 1)) ts))"
  let ?bs="(map (\<lambda>t. t \<cdot> \<langle>map labeled_source Bs\<rangle>\<^sub>\<alpha>) (map labeled_source (map to_pterm ts)))"
  let ?f="(\<lambda>i. ({i # p |p. p \<in> labelposs (?as ! i)} \<inter> {i # p |p. p \<in> labelposs (?bs ! i)}))"
  have "{[]} \<inter> (\<Union>i<length ts. {i # p |p. p \<in> labelposs (map (\<lambda>t. t \<cdot> \<langle>map labeled_source Bs\<rangle>\<^sub>\<alpha>) (map labeled_source (map to_pterm ts)) ! i)}) = {}"
    by blast
  then have *:"labelposs (label_term \<alpha> j (Fun f ts) \<cdot> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) \<inter> labelposs (labeled_source (to_pterm (Fun f ts)) \<cdot> \<langle>map labeled_source Bs\<rangle>\<^sub>\<alpha>)
      = (\<Union>i<length ts. (?f i))"
    unfolding label_term.simps to_pterm.simps labeled_source.simps eval_term.simps labelposs.simps by auto
  have "is_partition (map ?f [0..<length ts])" proof-
    {fix i j assume j:"j < length ts" and i:"i < j"
      have "?f i \<inter> ?f j = {}" unfolding Int_def using i
        by fastforce
    }
    then show ?thesis unfolding is_partition_def by auto
  qed
  moreover have "\<forall>i<length ts. finite (?f i)" by (simp add: finite_labelposs)
  ultimately have **:"card (\<Union>i<length ts. (?f i)) = (\<Sum>i<length ts. card (?f i))"
    unfolding * using card_Union_Sum by blast
  {fix i assume i:"i < length ts"
    have "?f i  = {i # p |p. p \<in> labelposs (?as ! i) \<inter> labelposs (?bs ! i)}"
      unfolding Int_def by blast
    then have "card (?f i) = card (labelposs (?as ! i) \<inter> labelposs (?bs ! i))"
      unfolding Setcompr_eq_image using card_image by (metis (no_types, lifting) inj_on_Cons1)
    with Fun i have "card (?f i) = (\<Sum>x\<leftarrow>vars_term_list (ts!i). measure_ov ((\<langle>As\<rangle>\<^sub>\<alpha>) x) ((\<langle>Bs\<rangle>\<^sub>\<alpha>) x))"
      by simp
  }
  then show ?case unfolding vars_term_list.simps * **
    by (simp add: sum_sum_concat)
qed

lemma measure_lhs_args_zero:
  assumes l:"length As = length Bs"
      and empty:"\<forall> i < length As. measure_ov (As!i) (Bs!i) = 0"
    shows "measure_ov (Prule \<alpha> As) ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>) = 0"
proof-
  let ?xs="vars_term_list (lhs \<alpha>)"
  have sum:"measure_ov (Prule \<alpha> As) ((to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>)
            = (\<Sum>x\<leftarrow>vars_term_list (lhs \<alpha>). measure_ov ((\<langle>As\<rangle>\<^sub>\<alpha>) x) ((\<langle>Bs\<rangle>\<^sub>\<alpha>) x))"
    using labeled_source_apply_subst measure_lhs_subst[OF l]
    by (metis (mono_tags, lifting) fun_mk_subst labeled_source.simps(1) labeled_source.simps(3) to_pterm_wf_pterm)
  {fix i assume i:"i < length ?xs"
    have "measure_ov ((\<langle>As\<rangle>\<^sub>\<alpha>) (?xs ! i)) ((\<langle>Bs\<rangle>\<^sub>\<alpha>) (?xs ! i)) = 0"
    proof(cases "(\<exists>j<length As. j < length (var_rule \<alpha>) \<and> (?xs!i) = var_rule \<alpha> ! j)")
      case True
      then obtain j where j:"j < length As" "j < length (var_rule \<alpha>)" and ij:"?xs!i = (var_rule \<alpha>)!j"
        by blast
      then show ?thesis
        unfolding ij using empty by (metis j l lhs_subst_var_i)
    next
      case False
      then have "(\<langle>As\<rangle>\<^sub>\<alpha>) (?xs!i) = Var (?xs!i)"
        using lhs_subst_not_var_i by metis
      moreover have "(\<langle>Bs\<rangle>\<^sub>\<alpha>) (?xs!i) = Var (?xs!i)"
        using l False lhs_subst_not_var_i by metis
      ultimately show ?thesis by simp
    qed}
  then show ?thesis
    using sum by (simp add: sum_list_zero)
qed

lemma measure_zero_subt_at:
  assumes "term_lab_to_term A = term_lab_to_term B"
    and "labelposs A \<inter> labelposs B = {}"
    and "p \<in> poss A"
  shows "labelposs (A|_p) \<inter> labelposs (B|_p) = {}"
  using assms proof(induct p arbitrary: A B)
  case (Cons i p)
  from Cons(4) obtain f a ts where a:"A = Fun (f, a) ts" and i:"i < length ts" and p:"p \<in> poss (ts!i)"
    using args_poss by (metis old.prod.exhaust)
  with Cons(2) obtain b ss where b:"B = Fun (f, b) ss"
    by (metis (no_types, opaque_lifting) Cons.prems(3) Term.term.simps(2) args_poss old.prod.exhaust poss_term_lab_to_term prod.sel(1) term_lab_to_term.simps(2))
  have ts:"(\<Union>i<length ts. {i # p | p. p \<in> labelposs (ts ! i)}) \<subseteq> labelposs A"  unfolding a by(cases a) auto
  have ss:"(\<Union>i<length ss. {i # p | p. p \<in> labelposs (ss ! i)}) \<subseteq> labelposs B"  unfolding b by(cases b) auto
  from ss ts b i Cons(2,3,4) have "labelposs (ts!i) \<inter> labelposs (ss!i) = {}" by auto
  with Cons(1,2) p i show ?case
    unfolding a b by (simp add: map_eq_conv')
qed simp

lemma empty_step_imp_measure_zero:
  assumes "is_empty_step A" 
  shows "measure_ov A B = 0"
  by (metis assms card_eq_0_iff inf_bot_left labeled_source_simple_pterm source_empty_step) 

lemma measure_ov_to_pterm:
  shows "measure_ov A (to_pterm t) = 0"
  by (simp add: labeled_source_simple_pterm) 

lemma measure_zero_imp_orthogonal: (*Interestingly this really needs left-linearity*)
  assumes R:"left_lin_no_var_lhs R" and S:"left_lin_no_var_lhs S"
  and "co_initial A B" "A \<in> wf_pterm R" "B \<in> wf_pterm S"
  and "measure_ov A B = 0"
shows "A \<bottom>\<^sub>p B"
  using assms(3-) proof(induct A arbitrary:B rule:subterm_induct)
  case (subterm A)
  then show ?case proof(cases A)
    case (Var x)
    with subterm show ?thesis proof(cases B)
      case (Prule \<alpha> Bs)
      from subterm(2) Var obtain y where y:"lhs \<alpha> = Var y"
        unfolding Prule by (metis source.simps(1) source.simps(3) subst_apply_eq_Var)
      from subterm(4) Prule S have "is_Fun (lhs \<alpha>)" 
        unfolding left_lin_no_var_lhs_def no_var_lhs_def
        by (metis Inl_inject case_prodD is_FunI is_Prule.simps(1) is_Prule.simps(3) is_VarI term.inject(2) wf_pterm.simps)  
      with y show ?thesis by simp
    qed (simp_all add: orthogonal.intros(1))
  next
    case (Pfun f As)
    note A=this
    with subterm show ?thesis proof(cases B)
      case (Pfun g Bs)
      from subterm(2) have f:"f = g"
        unfolding Pfun A by simp
      from subterm(2) have l:"length As = length Bs"
        unfolding A Pfun using map_eq_imp_length_eq by auto
      {fix i assume i:"i < length As"
        then have "As!i \<lhd> A"
          unfolding A by simp
        moreover from i subterm(2) l have "co_initial (As!i) (Bs!i)"
          by (metis (mono_tags, lifting) A Pfun nth_map source.simps(2) term.inject(2))
        moreover from i subterm(3) have "As!i \<in> wf_pterm R"
          using A by auto
        moreover from i subterm(4) l have "Bs!i \<in> wf_pterm S"
          using Pfun by auto
        moreover have "measure_ov (As!i) (Bs!i) = 0" proof-
          {fix p assume a:"p \<in> possL (As!i)" and b:"p \<in> possL (Bs!i)"
            with i have "i#p \<in> possL A"
              unfolding A labeled_source.simps labelposs.simps by simp
            moreover from b i l have "i#p \<in> possL B"
              unfolding Pfun labeled_source.simps labelposs.simps by simp
            ultimately have False using subterm(4)
              by (metis card_gt_0_iff disjoint_iff finite_Int finite_possL less_numeral_extra(3) subterm.prems(4))
          }
          then show ?thesis
            by (metis card.empty disjoint_iff)
        qed
        ultimately have "As!i \<bottom>\<^sub>p Bs!i"
          using subterm(1) by blast
      }
      then show ?thesis
        unfolding A Pfun f using l by auto
    next
      case (Prule \<beta> Bs)
      from subterm(4) S have lin:"linear_term (lhs \<beta>)"
        unfolding Prule left_lin_no_var_lhs_def left_lin_def left_linear_trs_def using wf_pterm.cases by fastforce
      have isfun:"is_Fun (lhs \<beta>)"
        using subterm(4) S no_var_lhs.lhs_is_Fun unfolding Prule left_lin_no_var_lhs_def by blast
      have "(lhs \<beta>) \<cdot> (term_lab_to_term \<circ> (\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>)) = lhs \<beta> \<cdot> \<langle>map source Bs\<rangle>\<^sub>\<beta>"
        by (metis label_term_to_term labeled_source.simps(3) labeled_source_to_term source.simps(3) term_lab_to_term_subst)
      with subterm(2) have co_init:"term_lab_to_term (labeled_source A) = lhs \<beta> \<cdot> (term_lab_to_term \<circ> \<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>)"
        unfolding Prule by simp
      from subterm(5) have "possL A \<inter> possL B = {}"
        by (simp add: finite_possL)
      then obtain \<tau> where "labeled_source A = term_to_term_lab (lhs \<beta>) \<cdot> \<tau>"
        unfolding labeled_source.simps(3) Prule using labels_intersect_label_term[OF co_init lin] by blast
      moreover have "labelposs (term_to_term_lab (lhs \<beta>)) = {}"
        using labelposs_term_to_term_lab by blast
      moreover from lin have "linear_term (term_to_term_lab (lhs \<beta>))"
        using linear_term_to_term_lab by blast
      moreover have "term_lab_to_term (term_to_term_lab (lhs \<beta>)) = lhs \<beta>"
        by simp
      ultimately obtain \<sigma> where sigma:"A = to_pterm (lhs \<beta>) \<cdot> \<sigma>"
        using no_var_lhs.unlabeled_source_to_pterm subterm(3) R unfolding left_lin_no_var_lhs_def by metis
      let ?As="map \<sigma> (var_rule \<beta>)"
      from sigma have a:"A = (to_pterm (lhs \<beta>)) \<cdot> \<langle>?As\<rangle>\<^sub>\<beta>"
        by (smt (verit, best) apply_lhs_subst_var_rule comp_apply length_map map_eq_conv set_remdups set_rev set_vars_term_list term_subst_eq vars_to_pterm)
      {fix i assume i:"i < length (var_rule \<beta>)"
        let ?xi="var_rule \<beta>!i"
        from i obtain i' where i':"i' < length (vars_term_list (lhs \<beta>))" "?xi = vars_term_list (lhs \<beta>)!i'"
          by (metis comp_apply in_set_conv_nth set_remdups set_rev)
        have l:"length Bs = length (var_rule \<beta>)"
          using subterm(4) unfolding Prule using wf_pterm.cases by force
        from i have asi:"?As!i = \<sigma> ?xi"
          by simp
        then have "?As!i \<lhd> A"
          using a sigma subst_image_subterm i' by (metis is_FunE isfun nth_mem set_vars_term_list to_pterm.simps(2) vars_to_pterm)
        moreover from i subterm(2) have "co_initial (?As!i) (Bs!i)"
          unfolding a Prule source.simps source_apply_subst[OF to_pterm_wf_pterm[of "lhs \<beta>"]] source_to_pterm using l
          by (smt (verit, best) apply_lhs_subst_var_rule comp_def i'(1) i'(2) length_map nth_map nth_mem set_vars_term_list term_subst_eq_conv)
        moreover have "measure_ov (?As!i) (Bs!i) = 0" proof-
          {fix p assume p:"p \<in> possL (?As!i)"
            let ?pi="var_poss_list (labeled_source (to_pterm (lhs \<beta>)))!i'"
            have pi:"?pi=var_poss_list (labeled_lhs \<beta>) !i'"
              by (simp add: var_poss_list_term_lab_to_term)
            have xi:"?xi=vars_term_list (labeled_lhs \<beta>) !i'"
              by (metis i'(2) vars_term_list_labeled_lhs)
            have xi':"?xi=vars_term_list (labeled_source (to_pterm (lhs \<beta>))) ! i'"
              using vars_term_list_term_lab_to_term i'(2) by (metis labeled_source_to_term source_to_pterm)
            have i'l:"i' < length (vars_term_list (labeled_lhs \<beta>))"
              by (simp add: i'(1) vars_term_list_labeled_lhs)
            have i'l':"i' < length (vars_term_list (labeled_source (to_pterm (lhs \<beta>))))"
              by (simp add: i'(1) vars_term_list_term_lab_to_term)
            have "(labeled_source (to_pterm (lhs \<beta>))) |_?pi = Var ?xi"
              using i' using i'l' vars_term_list_var_poss_list xi' by auto
            moreover have "possL A = labelposs ((labeled_source (to_pterm (lhs \<beta>))) \<cdot> (labeled_source \<circ> \<sigma>))"
              using labeled_source_apply_subst to_pterm_wf_pterm unfolding sigma by metis
            with p have "?pi@p \<in> possL A"
              unfolding set_labelposs_subst asi xi' using i'l' by fastforce
            with subterm(5) have "?pi@p \<notin> possL B"
              by (meson card_eq_0_iff disjoint_iff finite_Int finite_labelposs)
            moreover {assume "p \<in> possL (Bs!i)"
              then have "?pi@p \<in> {?pi @ q |q. q \<in> labelposs ((\<langle>map labeled_source Bs\<rangle>\<^sub>\<beta>) ?xi)}"
                by (smt (verit) Inl_inject Inr_Inl_False Prule apply_lhs_subst_var_rule i length_map map_nth_conv mem_Collect_eq subterm.prems(3) term.distinct(1) term.inject(2) wf_pterm.cases)
              then have "?pi@p \<in> possL B"
                unfolding Prule labeled_source.simps set_labelposs_subst xi pi using i'l by blast
            }
            ultimately have "p \<notin> possL (Bs!i)"
              by blast
          }
          then have "possL (?As!i) \<inter> possL (Bs!i) = {}"
            by blast
          then show ?thesis by simp
        qed
        ultimately have "?As!i \<bottom>\<^sub>p Bs!i"
          using subterm(1,3,4) i unfolding a Prule
          by (smt (verit, best) Inr_Inl_False Term.term.simps(4) length_map lhs_subst_args_wf_pterm nth_mem sum.inject(1) term.inject(2) wf_pterm.simps)
      }
      then show ?thesis unfolding a Prule using orthogonal.intros(4)[of ?As Bs]
        by (smt (verit, best) Prule Term.term.simps(4) in_set_zip length_map old.sum.inject(1) prod.case_eq_if subterm.prems(3) sum.distinct(1) term.inject(2) wf_pterm.cases)
    qed simp
  next
    case (Prule \<alpha> As)
    then have A:"A = Prule \<alpha> As"
      by simp
    from Prule subterm(3) R have lin:"linear_term (lhs \<alpha>)"
      unfolding left_lin_no_var_lhs_def left_lin_def left_linear_trs_def
      using wf_pterm.simps by fastforce
    obtain f ts where f:"lhs \<alpha> = Fun f ts"
      using subterm(3) R no_var_lhs.lhs_is_Fun unfolding left_lin_no_var_lhs_def Prule by blast
    show ?thesis proof(cases B)
      case (Var x)
      then show ?thesis
        by (metis source.simps(1) source_orthogonal subterm.prems(1) to_pterm.simps(1))
    next
      case (Pfun g Bs)
      have "(lhs \<alpha>) \<cdot> (term_lab_to_term \<circ> (\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>)) = lhs \<alpha> \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>"
        by (metis label_term_to_term labeled_source.simps(3) labeled_source_to_term source.simps(3) term_lab_to_term_subst)
      with subterm(2) have co_init:"term_lab_to_term (labeled_source B) = lhs \<alpha> \<cdot> (term_lab_to_term \<circ> \<langle>map labeled_source As\<rangle>\<^sub>\<alpha>)"
        unfolding Prule by simp
      from subterm(5) have "possL A \<inter> possL B = {}"
        by (simp add: finite_possL)
      then obtain \<tau> where "labeled_source B = term_to_term_lab (lhs \<alpha>) \<cdot> \<tau>"
        unfolding labeled_source.simps(3) Prule using labels_intersect_label_term[OF co_init lin] by blast
      moreover have "labelposs (term_to_term_lab (lhs \<alpha>)) = {}"
        using labelposs_term_to_term_lab by blast
      moreover from lin have "linear_term (term_to_term_lab (lhs \<alpha>))"
        using linear_term_to_term_lab by auto
      moreover have "term_lab_to_term (term_to_term_lab (lhs \<alpha>)) = lhs \<alpha>"
        by simp
      ultimately obtain \<sigma> where sigma:"B = to_pterm (lhs \<alpha>) \<cdot> \<sigma>"
        using no_var_lhs.unlabeled_source_to_pterm S subterm(4) unfolding left_lin_no_var_lhs_def by metis
      let ?Bs="map \<sigma> (var_rule \<alpha>)"
      from sigma have b:"B = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>?Bs\<rangle>\<^sub>\<alpha>"
        by (smt (verit, best) apply_lhs_subst_var_rule comp_apply length_map map_eq_conv set_remdups set_rev set_vars_term_list term_subst_eq vars_to_pterm)
      {fix i assume i:"i < length (var_rule \<alpha>)"
        let ?xi="var_rule \<alpha>!i"
        from i obtain i' where i':"i' < length (vars_term_list (lhs \<alpha>))" "?xi = vars_term_list (lhs \<alpha>)!i'"
          by (metis comp_apply in_set_conv_nth set_remdups set_rev)
        from i have asi:"?Bs!i = \<sigma> ?xi"
          by simp
        moreover have l:"length As = length (var_rule \<alpha>)"
          using subterm(3) unfolding A using wf_pterm.cases by force
        then have "As!i \<lhd> A"
          using i unfolding A by simp
        moreover from i subterm(2) have "co_initial (As!i) (?Bs!i)"
          unfolding b Prule source.simps source_apply_subst[OF to_pterm_wf_pterm[of "lhs \<alpha>"]] source_to_pterm using l
          by (smt (verit, best) apply_lhs_subst_var_rule comp_def i'(1) i'(2) length_map nth_map nth_mem set_vars_term_list term_subst_eq_conv)
        moreover have "measure_ov (As!i) (?Bs!i) = 0" proof-
          {fix p assume p:"p \<in> possL (?Bs!i)"
            let ?pi="var_poss_list (labeled_source (to_pterm (lhs \<alpha>)))!i'"
            have pi:"?pi=var_poss_list (labeled_lhs \<alpha>) !i'"
              by (simp add: var_poss_list_term_lab_to_term)
            have xi:"?xi=vars_term_list (labeled_lhs \<alpha>) !i'"
              by (metis i'(2) vars_term_list_labeled_lhs)
            have xi':"?xi=vars_term_list (labeled_source (to_pterm (lhs \<alpha>))) ! i'"
              using vars_term_list_term_lab_to_term i'(2) by (metis labeled_source_to_term source_to_pterm)
            have i'l:"i' < length (vars_term_list (labeled_lhs \<alpha>))"
              by (simp add: i'(1) vars_term_list_labeled_lhs)
            have i'l':"i' < length (vars_term_list (labeled_source (to_pterm (lhs \<alpha>))))"
              by (simp add: i'(1) vars_term_list_term_lab_to_term)
            have "(labeled_source (to_pterm (lhs \<alpha>))) |_?pi = Var ?xi"
              using i' using i'l' vars_term_list_var_poss_list xi' by auto
            moreover have "possL B = labelposs ((labeled_source (to_pterm (lhs \<alpha>))) \<cdot> (labeled_source \<circ> \<sigma>))"
              using labeled_source_apply_subst to_pterm_wf_pterm unfolding sigma by metis
            with p have "?pi@p \<in> possL B"
              unfolding set_labelposs_subst asi xi' using i'l' by fastforce
            with subterm(5) have "?pi@p \<notin> possL A"
              by (meson card_eq_0_iff disjoint_iff finite_Int finite_labelposs)
            moreover {assume "p \<in> possL (As!i)"
              then have "?pi@p \<in> {?pi @ q |q. q \<in> labelposs ((\<langle>map labeled_source As\<rangle>\<^sub>\<alpha>) ?xi)}"
                by (smt (verit) Inl_inject Inr_Inl_False Prule apply_lhs_subst_var_rule i length_map map_nth_conv mem_Collect_eq subterm.prems(2) term.distinct(1) term.inject(2) wf_pterm.cases)
              then have "?pi@p \<in> possL A"
                unfolding Prule labeled_source.simps set_labelposs_subst xi pi using i'l by blast
            }
            ultimately have "p \<notin> possL (As!i)"
              by blast
          }
          then have "possL (As!i) \<inter> possL (?Bs!i) = {}"
            by blast
          then show ?thesis by simp
        qed
        ultimately have "As!i \<bottom>\<^sub>p ?Bs!i"
          using subterm(1,3,4) i unfolding b Prule
          by (smt (verit, best) Inr_Inl_False Term.term.simps(4) length_map lhs_subst_args_wf_pterm nth_mem sum.inject(1) term.inject(2) wf_pterm.simps)
      }
      then show ?thesis unfolding b Prule using orthogonal.intros(3)[of As ?Bs]
        by (smt (verit, best) Prule Term.term.simps(4) in_set_zip length_map old.sum.inject(1) prod.case_eq_if subterm.prems(2) sum.distinct(1) term.inject(2) wf_pterm.cases)
    next
      case (Prule \<beta> Bs)
      from subterm(4) S obtain g ss where g:"lhs \<beta> = Fun g ss"
        unfolding Prule left_lin_no_var_lhs_def using no_var_lhs.lhs_is_Fun by blast
      have "[] \<in> possL A"
        unfolding A f labeled_source.simps label_term.simps eval_term.simps labelposs.simps by blast
      moreover have "[] \<in> possL B"
        unfolding Prule g labeled_source.simps label_term.simps eval_term.simps labelposs.simps by blast
      ultimately show ?thesis
        using subterm(5) by (simp add: disjoint_iff finite_labelposs)
    qed
  qed
qed

subsection\<open>Collecting Overlapping Positions\<close>
abbreviation overlaps_pos :: "('f, 'v) term_lab \<Rightarrow> ('f, 'v) term_lab  \<Rightarrow> (pos \<times> pos) set"
  where "overlaps_pos A B \<equiv> Set.filter (\<lambda>(p,q). get_label (A|_p) \<noteq> None \<and> get_label (B|_q) \<noteq> None \<and>
                  snd (the (get_label (A|_p))) = 0 \<and> snd (the (get_label (B|_q))) = 0 \<and>
                  (p <\<^sub>p q \<and> get_label (A|_q) \<noteq> None \<and> fst (the (get_label (A|_q))) = fst (the (get_label (A|_p))) \<and> snd (the (get_label (A|_q))) = length (the (remove_prefix p q)) \<or>
                  (q \<le>\<^sub>p p \<and> get_label (B|_p) \<noteq> None \<and> fst (the (get_label (B|_q))) = fst (the (get_label (B|_p))) \<and> snd (the (get_label (B|_p))) = length (the (remove_prefix q p)))))
                  (fun_poss A \<times> fun_poss B)"

lemma overlaps_pos_symmetric:
  assumes "(p,q) \<in> overlaps_pos A B"
  shows "(q,p) \<in> overlaps_pos B A"
  using SigmaI assms less_pos_def by auto

lemma overlaps_pos_intro:
  assumes "q@q' \<in> fun_poss A" and "q \<in> fun_poss B"
    and "get_label (A|_(q@q')) = Some (\<gamma>, 0)"
    and "get_label (B|_q) = Some (\<beta>, 0)"
    and "get_label (B|_(q@q')) = Some (\<beta>, length q')"
  shows "(q@q', q) \<in> overlaps_pos A B"
  using assms by force

text\<open>Define the partial order on overlaps\<close>
definition less_eq_overlap :: "pos \<times> pos \<Rightarrow> pos \<times> pos \<Rightarrow> bool" (infix "\<le>\<^sub>o" 50)
  where "p \<le>\<^sub>o q \<longleftrightarrow> (fst p \<le>\<^sub>p fst q) \<and> (snd p \<le>\<^sub>p snd q)"

definition less_overlap :: "pos \<times> pos \<Rightarrow> pos \<times> pos \<Rightarrow> bool" (infix "<\<^sub>o" 50)
  where "p <\<^sub>o q \<longleftrightarrow> p \<le>\<^sub>o q \<and> p \<noteq> q "

interpretation order_overlaps: order less_eq_overlap less_overlap
proof
  show "\<And>x. x \<le>\<^sub>o x"
    by (simp add: less_eq_overlap_def)
  show "\<And>x y z. x \<le>\<^sub>o y \<Longrightarrow> y \<le>\<^sub>o z \<Longrightarrow> x \<le>\<^sub>o z"
    by (smt (z3) less_eq_overlap_def less_overlap_def less_pos_def less_pos_def' less_pos_simps(5) order_pos.dual_order.trans)
  show  "\<And>x y. (x <\<^sub>o y) = strict (\<le>\<^sub>o) x y"
    using less_eq_overlap_def less_overlap_def by fastforce
  thus "\<And>x y. x \<le>\<^sub>o y \<Longrightarrow> y \<le>\<^sub>o x \<Longrightarrow> x = y"
    by (meson less_overlap_def)
qed

lemma overlaps_pos_finite: "finite (overlaps_pos A B)"
  by (meson finite_SigmaI finite_filter finite_fun_poss)

lemma labeled_sources_imp_measure_not_zero:
  assumes "p \<in> poss (labeled_source A)" "p \<in> poss (labeled_source B)"
  and "get_label ((labeled_source A)|_p) \<noteq> None \<and> get_label ((labeled_source B)|_p) \<noteq> None"
  shows "measure_ov A B > 0"
  using assms
  by (metis card_gt_0_iff disjoint_iff finite_Int finite_possL get_label_imp_labelposs)

lemma measure_zero_imp_empty_overlaps:
  assumes "measure_ov A B = 0" and co_init:"co_initial A B"
  shows "overlaps_pos (labeled_source A) (labeled_source B) = {}"
using assms(1) proof(rule contrapos_pp)
  {assume "overlaps_pos (labeled_source A) (labeled_source B) \<noteq> {}"
    then obtain p q where pq:"(p, q) \<in> overlaps_pos (labeled_source A) (labeled_source B)"
      by (meson equals0D pred_equals_eq2)
    then have "get_label ((labeled_source A)|_p) \<noteq> None \<and> get_label ((labeled_source B)|_q) \<noteq> None
            \<and> (get_label ((labeled_source A)|_q) \<noteq> None \<or> get_label ((labeled_source B)|_p) \<noteq> None)"
      by auto
    moreover from pq have "p \<in> poss (labeled_source A)" and "q \<in> poss (labeled_source B)"
      by (meson fun_poss_imp_poss mem_Sigma_iff member_filter)+
    ultimately show "measure_ov A B \<noteq> 0"
      using labeled_sources_imp_measure_not_zero co_init
      by (metis labeled_source_to_term less_numeral_extra(3) poss_term_lab_to_term)
  }
qed

lemma empty_overlaps_imp_measure_zero:
  assumes "A \<in> wf_pterm R" and "B \<in> wf_pterm S"
  and "overlaps_pos (labeled_source A) (labeled_source B) = {}"
  shows "measure_ov A B = 0"
  using assms(3) proof(rule contrapos_pp)
  {assume "measure_ov A B \<noteq> 0"
    then obtain p where p:"p \<in> possL A \<and> p \<in> possL B"
      using Int_emptyI by force
    then obtain \<alpha> n where a:"get_label ((labeled_source A)|_p) = Some(\<alpha>, n)"
      using possL_obtain_label by blast
    let ?p1="take (length p - n) p"
    obtain q1 where q1:"p = ?p1@q1"
      by (metis append_take_drop_id)
    from a p assms(1) have alpha:"get_label (labeled_source A |_ ?p1) = Some (\<alpha>, 0)" and "?p1 \<in> poss (labeled_source A)"
      using labelposs_subs_poss obtain_label_root by blast+
    then have p1_pos:"?p1 \<in> fun_poss (labeled_source A)"
      using get_label_imp_labelposs labelposs_subs_fun_poss by blast
    from p obtain \<beta> m where b:"get_label ((labeled_source B)|_p) = Some(\<beta>, m)"
      using possL_obtain_label by blast
    let ?p2="take (length p - m) p"
    obtain q2 where q2:"p = ?p2@q2"
      by (metis append_take_drop_id)
    from b p assms(2) have beta:"get_label (labeled_source B |_ ?p2) = Some (\<beta>, 0)" and "?p2 \<in> poss (labeled_source B)"
      using labelposs_subs_poss obtain_label_root by blast+
    then have p2_pos:"?p2 \<in> fun_poss (labeled_source B)"
      using get_label_imp_labelposs labelposs_subs_fun_poss by blast

    then show "overlaps_pos (labeled_source A) (labeled_source B) \<noteq> {}" proof(cases "?p1 \<le>\<^sub>p ?p2")
      case True
      then obtain p3 where p2:"?p2 = ?p1@p3"
        by (metis less_eq_pos_def)
      with q2 have "p = ?p1 @ p3 @ q2"
        by simp
      with q1 have p3:"q1 = p3@q2"
        by (metis same_append_eq)
      from a alpha q1 have "n = length q1"
        by (metis (no_types, lifting) add_diff_cancel_left' append_take_drop_id assms(1) label_term_max_value labelposs_subs_poss length_drop ordered_cancel_comm_monoid_diff_class.diff_add p same_append_eq subsetD)
      with p3 have "n = length p3 + length q2"
        by auto
      then have "get_label ((labeled_source A)|_(?p1@p3)) = Some (\<alpha>, length p3)"
        using label_decrease[of "?p1@p3" q2 A] p1_pos a assms(1)
        by (metis add.commute fun_poss_imp_poss fun_poss_term_lab_to_term labeled_source_to_term labelposs_subs_fun_poss_source p p2 q2)
      then have "(?p2, ?p1) \<in> overlaps_pos (labeled_source B) (labeled_source A)"
        using overlaps_pos_intro p1_pos p2_pos p2 alpha beta by simp
      then show ?thesis using overlaps_pos_symmetric by blast
    next
      case False
      with q1 q2 have "?p2 <\<^sub>p ?p1"
        by (metis less_eq_pos_simps(1) pos_cases pos_less_eq_append_not_parallel)
      then obtain p3 where p2:"?p1 = ?p2@p3"
        using less_pos_def' by blast
      with q1 have "p = ?p2 @ p3 @ q1"
        by simp
      with q2 have p3:"q2 = p3@q1"
        by (metis same_append_eq)
      from b beta q2 have "m = length q2"
        by (metis (no_types, lifting) add_diff_cancel_left' append_take_drop_id assms(2) label_term_max_value labelposs_subs_poss length_drop ordered_cancel_comm_monoid_diff_class.diff_add p same_append_eq subsetD)
      with p3 have "m = length p3 + length q1"
        by auto
      then have "get_label ((labeled_source B)|_(?p2@p3)) = Some (\<beta>, length p3)"
        using label_decrease[of "?p2@p3" q1 B] p2_pos b assms(2)
        by (metis add.commute fun_poss_imp_poss fun_poss_term_lab_to_term labeled_source_to_term labelposs_subs_fun_poss_source p p2 q1)
      then have "(?p1, ?p2) \<in> overlaps_pos (labeled_source A) (labeled_source B)"
        using overlaps_pos_intro p1_pos p2_pos p2 alpha beta by simp
      then show ?thesis by blast
    qed
  }
qed

lemma obtain_overlap:
  assumes "p \<in> possL A" "p \<in> possL B"
    and "get_label (labeled_source A|_p) = Some (\<gamma>, n)"
    and "get_label (labeled_source B|_p) = Some (\<delta>, m)"
    and "n \<le> length p" "m \<le> length p"
    and "r\<gamma> = take (length p - n) p"
    and "r\<delta> = take (length p - m) p"
    and "r\<delta> \<le>\<^sub>p r\<gamma>"
    and a_well:"A \<in> wf_pterm R" and b_well:"B \<in> wf_pterm S"
  shows "(r\<gamma>, r\<delta>) \<in> overlaps_pos (labeled_source A) (labeled_source B)"
proof-
  from assms(9) obtain r' where r':"r\<gamma> = r\<delta> @ r'"
    using prefix_pos_diff by metis
  have "r\<delta> @ r' \<in> fun_poss (labeled_source A)"
    using assms(1,7) unfolding r' by (metis append_take_drop_id fun_poss_append_poss' labelposs_subs_fun_poss subsetD)
  moreover have "r\<delta> \<in> fun_poss (labeled_source B)"
    using assms(2,4,8) by (metis append_take_drop_id fun_poss_append_poss' labelposs_subs_fun_poss subsetD)
  moreover have "get_label ((labeled_source A) |_ (r\<delta> @ r')) = Some (\<gamma>, 0)"
    using assms(1,3,5,7) a_well unfolding r' using label_decrease[of "take (length p - n) p" "drop (length p- n) p"]
    by (smt (verit, best) add.right_neutral add_diff_cancel_left' append_assoc append_take_drop_id labelposs_subs_poss le_add_diff_inverse2 length_drop subsetD)
  moreover have "get_label ((labeled_source B) |_ (r\<delta>)) = Some (\<delta>, 0)"
    using assms(2,4,6,8) b_well using label_decrease[of "take (length p - m) p" "drop (length p- m) p"]
    by (smt (verit, best) add.right_neutral add_diff_cancel_left' append_assoc append_take_drop_id labelposs_subs_poss le_add_diff_inverse2 length_drop subsetD)
  moreover have "get_label ((labeled_source B) |_ (r\<delta>@r')) = Some (\<delta>, length r')"
    using assms(2,4,6,8) b_well unfolding r' using label_decrease[of "take (length p - length r') p" "drop (length p- length r') p"]
    by (smt (verit, del_insts) Nat.add_diff_assoc add_diff_cancel_left' append.assoc append_take_drop_id assms(7) diff_diff_cancel diff_le_self fun_poss_imp_poss fun_poss_term_lab_to_term label_decrease labeled_source_to_term labelposs_subs_fun_poss_source le_add1 le_add_diff_inverse length_append length_take min.absorb2 r')
  ultimately show ?thesis using overlaps_pos_intro unfolding r'
    by (smt (verit, ccfv_threshold) append.assoc case_prodI fst_conv less_eq_pos_simps(1) mem_Sigma_iff member_filter option.distinct(1) option.sel remove_prefix_append snd_conv)
qed


end
