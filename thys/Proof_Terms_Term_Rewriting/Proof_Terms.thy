section\<open>Proof Terms\<close>

theory Proof_Terms
  imports 
    First_Order_Terms.Matching
    First_Order_Rewriting.Multistep
    Proof_Term_Utils
begin

subsection\<open>Definitions\<close>

text\<open>A rewrite rule consists of a pair of terms representing its left-hand side and right-hand side. 
We associate a rule symbol with each rewrite rule. \<close>
datatype ('f, 'v) prule = 
  Rule (lhs: "('f, 'v) term") (rhs: "('f, 'v) term") ("_ \<rightarrow> _" [51, 51] 52)

text\<open>Translate between @{type prule} defined here and @{type rule} as defined in IsaFoR.\<close>
abbreviation to_rule :: "('f, 'v) prule \<Rightarrow> ('f, 'v) rule" 
  where "to_rule r \<equiv> (lhs r, rhs r)"

text\<open>Proof terms are terms built from variables, function symbols, and rules.\<close>
type_synonym
  ('f, 'v) pterm = "(('f, 'v) prule + 'f, 'v) term"
type_synonym
  ('f, 'v) pterm_ctxt = "(('f, 'v) prule + 'f, 'v) ctxt"

text\<open>We provides an easier notation for proof terms (avoiding @{term Inl} and @{term Inr}).\<close>
abbreviation Prule :: "('f, 'v) prule \<Rightarrow> ('f, 'v) pterm list \<Rightarrow> ('f, 'v) pterm" 
  where "Prule \<alpha> As \<equiv> Fun (Inl \<alpha>) As"
abbreviation Pfun :: "'f  \<Rightarrow> ('f, 'v) pterm list \<Rightarrow> ('f, 'v) pterm" 
  where "Pfun f As \<equiv> Fun (Inr f) As"

text\<open>Also for contexts.\<close>
abbreviation Crule :: "('f, 'v) prule \<Rightarrow> ('f, 'v) pterm list \<Rightarrow> ('f, 'v) pterm_ctxt \<Rightarrow> ('f, 'v) pterm list \<Rightarrow>('f, 'v) pterm_ctxt" 
  where "Crule \<alpha> As1 C As2 \<equiv> More (Inl \<alpha>) As1 C As2"
abbreviation Cfun :: "'f  \<Rightarrow> ('f, 'v) pterm list \<Rightarrow> ('f, 'v) pterm_ctxt \<Rightarrow> ('f, 'v) pterm list \<Rightarrow>('f, 'v) pterm_ctxt" 
  where "Cfun f As1 C As2 \<equiv> More (Inr f) As1 C As2"

text \<open>Case analysis on proof terms.\<close>
lemma pterm_cases [case_names Var Pfun Prule, cases type: pterm]:
  "(\<And>x. A = Var x \<Longrightarrow> P) \<Longrightarrow> (\<And>f As. A = Pfun f As \<Longrightarrow> P) \<Longrightarrow> (\<And>\<alpha> As. A = Prule \<alpha> As \<Longrightarrow> P) \<Longrightarrow> P"
proof (cases A)
  case (Fun x21 x22)
  show "\<And>x21 x22. (\<And>x. A = Var x \<Longrightarrow> P) \<Longrightarrow> (\<And>f As. A = Pfun f As \<Longrightarrow> P) \<Longrightarrow> (\<And>\<alpha> As. A = Prule \<alpha> As \<Longrightarrow> P) \<Longrightarrow> A = Fun x21 x22 \<Longrightarrow> P" 
   using sum.exhaust by auto 
qed

text \<open>Induction scheme for proof terms.\<close> 
lemma
  fixes P :: "('f, 'v) pterm \<Rightarrow> bool"
  assumes "\<And>x. P (Var x)" 
  and "\<And>f As. (\<And>a. a \<in> set As \<Longrightarrow> P a) \<Longrightarrow> P (Pfun f As)"
  and "\<And>\<alpha> As. (\<And>a. a \<in> set As \<Longrightarrow> P a) \<Longrightarrow> P (Prule \<alpha> As)"
  shows pterm_induct [case_names Var Pfun Prule, induct type: "pterm"]: "P A"
  using assms proof(induct A)
  case (Fun f ts)
  then show ?case by(cases f) auto
qed simp

text \<open>Induction scheme for contexts of proof terms.\<close> 
lemma
  fixes P :: "('f, 'v) pterm_ctxt \<Rightarrow> bool"
  assumes "P \<box>" 
  and "\<And>f ss1 C ss2. P C \<Longrightarrow> P (Cfun f ss1 C ss2)"
  and "\<And>\<alpha> ss1 C ss2. P C \<Longrightarrow> P (Crule \<alpha> ss1 C ss2)"
  shows pterm_ctxt_induct [case_names Hole Cfun Crule, induct type: "pterm_ctxt"]: "P C"
  using assms proof(induct C)
  case (More f ss1 C ss2)
  then show ?case by(cases f) auto
qed

text \<open>Obtain the distinct variables occurring on the left-hand side of a rule in the order they appear.\<close>
abbreviation var_rule :: "('f, 'v) prule \<Rightarrow> 'v list" where "var_rule \<alpha> \<equiv> vars_distinct (lhs \<alpha>)"

abbreviation lhs_subst :: "('g, 'v) term list \<Rightarrow> ('f, 'v) prule \<Rightarrow> ('g, 'v) subst " ("\<langle>_\<rangle>\<^sub>_" [0,99])
  where "lhs_subst As \<alpha> \<equiv> mk_subst Var (zip (var_rule \<alpha>) As)"

text\<open>A proof term using only function symbols and variables is an empty step.\<close>
fun is_empty_step :: "('f, 'v) pterm \<Rightarrow> bool" where
  "is_empty_step (Var x) = True"
| "is_empty_step (Pfun f As) = list_all is_empty_step As"
| "is_empty_step (Prule \<alpha> As) = False"

fun is_Prule :: "('f, 'v) pterm \<Rightarrow> bool" where
  "is_Prule (Prule _ _) = True"
| "is_Prule _ = False"

text\<open>Source and target\<close>
fun source :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) term" where
  "source (Var x) = Var x"
| "source (Pfun f As) = Fun f (map source As)"
| "source (Prule \<alpha> As) = lhs \<alpha> \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha>" 

fun target :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) term" where
  "target (Var x) = Var x"
| "target (Pfun f As) = Fun f (map target As)"
| "target (Prule \<alpha> As) = rhs \<alpha> \<cdot> \<langle>map target As\<rangle>\<^sub>\<alpha>" 

text\<open>Source also works for proof term contexts in left-linear TRSs.\<close>
fun source_ctxt :: "('f, 'v) pterm_ctxt \<Rightarrow> ('f, 'v) ctxt" where
  "source_ctxt \<box> = \<box>"
| "source_ctxt (Cfun f As1 C As2) = More f (map source As1) (source_ctxt C) (map source As2)"
| "source_ctxt (Crule \<alpha> As1 C As2) = 
  (let ctxt_pos = (var_poss_list (lhs \<alpha>))!(length As1);
       placeholder = Var ((vars_term_list (lhs \<alpha>)) ! (length As1)) in 
   ctxt_of_pos_term (ctxt_pos) (lhs \<alpha> \<cdot> \<langle>map source (As1 @ ((placeholder # As2)))\<rangle>\<^sub>\<alpha>)) \<circ>\<^sub>c (source_ctxt C)" 

abbreviation "co_initial A B \<equiv> (source A = source B)" 

text \<open>Transform simple terms to proof terms.\<close>
fun to_pterm :: "('f, 'v) term \<Rightarrow> ('f, 'v) pterm" where 
  "to_pterm (Var x) = Var x"
| "to_pterm (Fun f ts) = Pfun f (map to_pterm ts)"

text\<open>Also for contexts.\<close>
fun to_pterm_ctxt :: "('f, 'v) ctxt \<Rightarrow> ('f, 'v) pterm_ctxt" where
  "to_pterm_ctxt \<box> = \<box>"
| "to_pterm_ctxt (More f ss1 C ss2) = Cfun f (map to_pterm ss1) (to_pterm_ctxt C) (map to_pterm ss2)"

subsection\<open>Frequently Used Locales/Contexts\<close>
text\<open>Often certain properties about proof terms only hold when the underlying TRS
does not contain variable left-hand sides and/or variables on the right 
are a subset of the variables on the left and/or the TRS is left-linear.\<close>
locale left_lin =
  fixes R :: "('f, 'v) trs"
  assumes left_lin:"left_linear_trs R" 

locale no_var_lhs =
  fixes R :: "('f, 'v) trs"
  assumes no_var_lhs:"Ball R (\<lambda>(l, r). is_Fun l)"

locale var_rhs_subset_lhs =
  fixes R :: "('f, 'v) trs"
  assumes varcond:"Ball R (\<lambda>(l, r). vars_term r \<subseteq> vars_term l)"

locale wf_trs = no_var_lhs + var_rhs_subset_lhs
locale left_lin_no_var_lhs = left_lin + no_var_lhs
locale left_lin_wf_trs = left_lin + wf_trs

context wf_trs
begin
lemma wf_trs_alt:
  shows "Trs.wf_trs R" 
  unfolding wf_trs_def' using no_var_lhs varcond by auto 
end

context left_lin
begin
lemma length_var_rule:
  assumes "to_rule \<alpha> \<in> R" 
  shows "length (var_rule \<alpha>) = length (vars_term_list (lhs \<alpha>))" 
  using assms
  by (metis case_prodD left_lin left_linear_trs_def linear_term_var_vars_term_list) 
end

subsection\<open>Proof Term Predicates\<close>
text \<open>The number of arguments of a well-defined proof term over a TRS @{term R} using a rule symbol 
@{term \<alpha>} corresponds to the number of variables in @{term "lhs \<alpha>"}. Also the rewrite rule for 
@{term \<alpha>} must belong to the TRS @{term R}.\<close>
inductive_set wf_pterm :: "('f, 'v) trs \<Rightarrow> ('f, 'v) pterm set"
  for R where
 [simp]: "Var x \<in> wf_pterm R"
|[intro]: "\<forall>t \<in> set ts. t \<in> wf_pterm R \<Longrightarrow>  Pfun f ts \<in> wf_pterm R"
|[intro]: "(lhs \<alpha>, rhs \<alpha>) \<in> R \<Longrightarrow> length As = length (var_rule \<alpha>) \<Longrightarrow> 
                \<forall>a \<in> set As. a \<in> wf_pterm R \<Longrightarrow> Prule \<alpha> As \<in> wf_pterm R"

inductive_set wf_pterm_ctxt :: "('f, 'v) trs \<Rightarrow> ('f, 'v) pterm_ctxt set"
  for R where
 [simp]: "\<box> \<in> wf_pterm_ctxt R"
|[intro]: "\<forall>s \<in> (set ss1) \<union> (set ss2). s \<in> wf_pterm R \<Longrightarrow> C \<in> wf_pterm_ctxt R \<Longrightarrow> 
           Cfun f ss1 C ss2 \<in> wf_pterm_ctxt R"
|[intro]: "(lhs \<alpha>, rhs \<alpha>) \<in> R \<Longrightarrow> (length ss1) + (length ss2) + 1 = length (var_rule \<alpha>) \<Longrightarrow> 
           \<forall>s \<in> (set ss1) \<union> (set ss2). s \<in> wf_pterm R \<Longrightarrow> C \<in> wf_pterm_ctxt R \<Longrightarrow>
           Crule \<alpha> ss1 C ss2 \<in> wf_pterm_ctxt R"

lemma fun_well_arg[intro]: 
  assumes "Fun f As \<in> wf_pterm R" "a \<in> set As"
  shows "a \<in> wf_pterm R" 
  using assms wf_pterm.cases by auto

lemma trs_well_ctxt_arg[intro]:
  assumes "More f ss1 C ss2 \<in> wf_pterm_ctxt R" "s \<in> (set ss1) \<union> (set ss2)"
  shows "s \<in> wf_pterm R"
  using assms wf_pterm_ctxt.cases  by blast 

lemma trs_well_ctxt_C[intro]:
  assumes "More f ss1 C ss2 \<in> wf_pterm_ctxt R"
  shows "C \<in> wf_pterm_ctxt R"
  using assms wf_pterm_ctxt.cases by auto

context no_var_lhs
begin
lemma lhs_is_Fun:
  assumes "Prule \<alpha> Bs \<in> wf_pterm R"
  shows "is_Fun (lhs \<alpha>)"
  by (metis Inl_inject assms case_prodD is_FunI is_Prule.simps(1) is_Prule.simps(3) is_VarI 
      no_var_lhs.no_var_lhs no_var_lhs_axioms term.inject(2) wf_pterm.simps)
end

lemma lhs_subst_var_well_def:
  assumes "\<forall>i < length As. As!i \<in> wf_pterm R" 
  shows "(\<langle>As\<rangle>\<^sub>\<alpha>) x \<in> wf_pterm R"
proof (cases "map_of (zip (var_rule \<alpha>) As) x")
  case None
  then show ?thesis unfolding mk_subst_def by simp
next
  case (Some a)
  then have "a \<in> set As"
    by (meson in_set_zipE map_of_SomeD) 
  with assms Some show ?thesis 
    unfolding mk_subst_def using in_set_idx by force
qed

lemma lhs_subst_well_def:
  assumes "\<forall>i < length As. As!i \<in> wf_pterm R" "B \<in> wf_pterm R"
  shows "B \<cdot> (\<langle>As\<rangle>\<^sub>\<alpha>) \<in> wf_pterm R"
  using assms proof(induction B arbitrary: As)
  case (Var x)
  then show ?case using lhs_subst_var_well_def by simp
next
  case (Pfun f Bs)
  from Pfun(3) have "\<forall>b \<in> set Bs. b \<in> wf_pterm R" 
    by blast 
  with Pfun show ?case by fastforce 
next
  case (Prule \<beta> Bs)
  from Prule(3) have "\<forall>b \<in> set Bs. b \<in> wf_pterm R" 
    by blast
  moreover have "length (map (\<lambda>t. t \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) Bs) = length (var_rule \<beta>)"
    using Prule(3) wf_pterm.simps by fastforce 
  moreover from Prule(3) have "to_rule \<beta> \<in> R"
    using Inl_inject sum.distinct(1) wf_pterm.cases by force 
  ultimately show ?case unfolding eval_term.simps(2) using Prule
    by (simp add: wf_pterm.intros(3)) 
qed

lemma subt_at_is_wf_pterm:
  assumes "p \<in> poss A" and "A \<in> wf_pterm R"
  shows "A|_p \<in> wf_pterm R"
  using assms proof(induct p arbitrary:A)
  case (Cons i p)
  then obtain f As where a:"A = Fun f As" and i:"i < length As" and p:"p \<in> poss (As!i)"
    using args_poss by blast 
  with Cons(3) have "As!i \<in> wf_pterm R"
    using nth_mem by blast 
  with Cons.hyps p a show ?case by simp
qed simp

lemma ctxt_of_pos_term_well:
  assumes "p \<in> poss A" and "A \<in> wf_pterm R"
  shows "ctxt_of_pos_term p A \<in> wf_pterm_ctxt R"
  using assms proof(induct p arbitrary:A)
  case (Cons i p)
  then obtain fs As where a:"A = Fun fs As" and i:"i < length As" and p:"p \<in> poss (As!i)"
    using args_poss by blast 
  with Cons(3) have as:"\<forall>j < length As. As!j \<in> wf_pterm R"
    using nth_mem by blast
  with Cons.hyps p i have IH:"ctxt_of_pos_term p (As!i) \<in> wf_pterm_ctxt R"
    by blast 
  then show ?case proof(cases fs)
    case (Inl \<alpha>)
    from Cons(3) have "to_rule \<alpha> \<in> R" unfolding a Inl
      using wf_pterm.cases by auto  
    moreover from Cons(3) i have "length (take i As) + length (drop (Suc i) As) + 1 = length (var_rule \<alpha>)" 
      unfolding a Inl using wf_pterm.cases by force 
    ultimately show ?thesis 
      unfolding a ctxt_of_pos_term.simps Inl using as IH wf_pterm_ctxt.intros(3)
      by (metis (no_types, opaque_lifting) UnE in_set_conv_nth in_set_dropD in_set_takeD)
  next
    case (Inr f)
    show ?thesis 
      unfolding a ctxt_of_pos_term.simps Inr using as IH wf_pterm_ctxt.intros(2)
      by (metis Cons.prems(2) UnE a fun_well_arg in_set_dropD in_set_takeD) 
  qed 
qed simp

text\<open>Every normal term is a well-defined proof term.\<close>
lemma to_pterm_wf_pterm[simp]: "to_pterm t \<in> wf_pterm R"
  by (induction t) (simp_all add: wf_pterm.intros(2,3))

lemma to_pterm_trs_ctxt:
  assumes "p \<in> poss (to_pterm s)"
  shows "ctxt_of_pos_term p (to_pterm s) \<in> wf_pterm_ctxt R"
  by (simp add: assms ctxt_of_pos_term_well)

lemma to_pterm_ctxt_wf_pterm_ctxt:
  shows "to_pterm_ctxt C \<in> wf_pterm_ctxt R"
proof(induct C)
  case (More f xs C ys)
  then show ?case unfolding to_pterm_ctxt.simps
    by (metis Un_iff fun_well_arg to_pterm.simps(2) to_pterm_wf_pterm wf_pterm_ctxt.intros(2))
qed simp

lemma ctxt_wf_pterm:
  assumes "A \<in> wf_pterm R" and "p \<in> poss A"
    and "B \<in> wf_pterm R"
  shows "(ctxt_of_pos_term p A)\<langle>B\<rangle> \<in> wf_pterm R"
  using assms proof(induct p arbitrary:A)
  case (Cons i p)
  from Cons(3) obtain f As where A:"A = Fun f As" "i < length As" "p \<in> poss (As!i)"
    using args_poss by blast 
  moreover with Cons(2) have "As!i \<in> wf_pterm R"
    using nth_mem by blast 
  ultimately have IH:"(ctxt_of_pos_term p (As!i))\<langle>B\<rangle> \<in> wf_pterm R" 
    using Cons.hyps assms(3) by presburger
  from Cons(2) have as:"\<forall>a \<in> set As. a \<in> wf_pterm R" 
    unfolding A by auto
  show ?case proof(cases f)
    case (Inl \<alpha>)
    from Cons(2) have alpha:"to_rule \<alpha> \<in> R" 
      unfolding A Inl using wf_pterm.simps by fastforce
    moreover from Cons(2) have "length As = length (var_rule \<alpha>)" 
      unfolding A Inl using wf_pterm.simps by fastforce
    ultimately show ?thesis 
      unfolding Inl A ctxt_of_pos_term.simps intp_actxt.simps using wf_pterm.intros(3)[OF alpha] IH as A(2)
      by (smt (verit, ccfv_SIG) id_take_nth_drop in_set_conv_nth le_simps(1) length_append list.size(4) nth_append_take nth_append_take_drop_is_nth_conv)   
  next
  case (Inr b)
  show ?thesis unfolding Inr A ctxt_of_pos_term.simps intp_actxt.simps using wf_pterm.intros(2) IH as A(2)
    by (smt (verit, ccfv_SIG) Cons_nth_drop_Suc append_take_drop_id in_set_conv_nth length_append length_nth_simps(2) less_imp_le_nat nth_append_take nth_append_take_drop_is_nth_conv)
  qed 
qed simp

subsection\<open>'Normal' Terms vs. Proof Terms\<close>

lemma to_pterm_empty: "is_empty_step (to_pterm t)"
proof (induction t)
  case (Fun f ts)
  then have "list_all is_empty_step (map to_pterm ts)" using list_all_iff by force 
  then show ?case by simp
qed simp

text\<open>Variables remain unchanged.\<close>
lemma vars_to_pterm: "vars_term_list (to_pterm t) = vars_term_list t" 
proof(induction t)
  case (Fun f ts)
  then have *:"map vars_term_list ts = map (vars_term_list \<circ> to_pterm) ts" by simp
  show ?case by (simp add: "*" vars_term_list.simps(2)) 
qed (simp add: vars_term_list.simps(1))

lemma poss_list_to_pterm: "poss_list t = poss_list (to_pterm t)"
proof(induction t)
  case (Fun f ts)
  then have *:"map poss_list ts = map (poss_list \<circ> to_pterm) ts" by simp
  show ?case by (simp add: "*" poss_list.simps(2)) 
qed (simp add: poss_list.simps(1))

lemma p_in_poss_to_pterm:
  assumes "p \<in> poss t"
  shows "p \<in> poss (to_pterm t)"
  using assms poss_list_to_pterm by (metis poss_list_sound)

lemma var_poss_to_pterm: "var_poss t = var_poss (to_pterm t)" 
proof(induction t)
  case (Fun f ts)
  then have *:"map var_poss ts = map (var_poss \<circ> to_pterm) ts" by simp
  then show ?case unfolding var_poss.simps to_pterm.simps
    by auto
qed simp

lemma var_poss_list_to_pterm: "var_poss_list (to_pterm t) = var_poss_list t"
proof(induct t)
  case (Fun f ts)
  then show ?case unfolding var_poss_list.simps to_pterm.simps
    by (metis (no_types, lifting) length_map map_nth_eq_conv nth_mem)
qed simp

text\<open>@{const to_pterm} distributes over application of substitution.\<close>
lemma to_pterm_subst: 
"to_pterm (t \<cdot> \<sigma>) = (to_pterm t) \<cdot> (to_pterm \<circ> \<sigma>)"
  by (induct t, auto)

text\<open>@{const to_pterm} distributes over context.\<close>
lemma to_pterm_ctxt_of_pos_apply_term:
  assumes "p \<in> poss s"
  shows "to_pterm ((ctxt_of_pos_term p s) \<langle>t\<rangle>) = (ctxt_of_pos_term p (to_pterm s))\<langle>to_pterm t\<rangle>"
  using assms proof(induct p arbitrary:s)
  case (Cons i p)
  then obtain f ss where s:"s = Fun f ss" and i:"i < length ss" and p:"p \<in> poss (ss!i)"
    using args_poss by blast
  then show ?case unfolding s to_pterm.simps ctxt_of_pos_term.simps intp_actxt.simps using Cons(1)
    by (simp add: drop_map take_map)
qed simp

text\<open>Linear terms become linear proof terms.\<close>
lemma to_pterm_linear:
  assumes "linear_term t"
  shows "linear_term (to_pterm t)"
  using assms proof(induction t)
  case (Fun f ts)
  have *:"map vars_term ts = map vars_term (map to_pterm ts)"
    by (metis (mono_tags, lifting) length_map map_nth_eq_conv set_vars_term_list vars_to_pterm)
  with Fun show ?case  by auto
qed simp

lemma lhs_subst_trivial: 
  shows "match (to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>) (to_pterm (lhs \<alpha>)) = Some \<langle>As\<rangle>\<^sub>\<alpha>"
  using match_trivial
  by (smt comp_def mem_Collect_eq mk_subst_not_mem set_remdups set_rev set_vars_term_list subsetI subst_domain_def vars_to_pterm)

lemma to_pterm_ctxt_apply_term:
  "to_pterm C\<langle>t\<rangle> = (to_pterm_ctxt C) \<langle>to_pterm t\<rangle>"
  by(induct C) simp_all


subsection\<open>Substitutions\<close>
lemma fun_mk_subst[simp]:
  assumes "\<forall>x. f (Var x) = Var x"
  shows "f \<circ> (mk_subst Var (zip vs ts)) = mk_subst Var (zip vs (map f ts))"
proof-
  have "\<forall>a. f (case map_of (zip vs ts) a of None \<Rightarrow> Var a | Some t \<Rightarrow> t)
          = (case map_of (zip vs ts) a of None \<Rightarrow> Var a | Some t \<Rightarrow> f t)" 
    using assms by (simp add: option.case_eq_if) 
  moreover have "\<forall>a. (case map_of (zip vs (map f ts)) a of None \<Rightarrow> Var a | Some x \<Rightarrow> x) 
                   = (case (map_of (zip vs ts)) a of None \<Rightarrow> Var a | Some t \<Rightarrow> f t)" 
    by (simp add:zip_map2 map_of_map option.case_eq_if option.map_sel)
  ultimately show ?thesis unfolding mk_subst_def unfolding comp_def by auto
qed

lemma apply_lhs_subst_var_rule:
  assumes "length ts = length (var_rule \<alpha>)"
  shows "map (\<langle>ts\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>) = ts"
  using assms by (simp add: mk_subst_distinct map_nth_eq_conv)

lemma match_lhs_subst:
  assumes "match B (to_pterm (lhs \<alpha>)) = Some \<sigma>"
  shows "\<exists>Bs. length Bs = length (var_rule \<alpha>) \<and> 
         B = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha> \<and> 
        (\<forall>x \<in> set (var_rule \<alpha>). \<sigma> x = (\<langle>Bs\<rangle>\<^sub>\<alpha>) x)" 
proof-
  obtain Bs where Bs:"length Bs = length (var_rule \<alpha>)" 
      "\<forall>i < length (var_rule \<alpha>). Bs!i = \<sigma> ((var_rule \<alpha>)!i)"
    using length_map nth_map by blast
  then have 2:"(\<forall>x \<in> set (var_rule \<alpha>). \<sigma> x = (\<langle>Bs\<rangle>\<^sub>\<alpha>) x)"
    by (smt apply_lhs_subst_var_rule in_set_idx nth_map)
  have v:"vars_term (to_pterm (lhs \<alpha>)) = set (var_rule \<alpha>)"
    by (metis comp_apply set_remdups set_rev set_vars_term_list vars_to_pterm) 
  from assms have "B = (to_pterm (lhs \<alpha>)) \<cdot> \<sigma>"
    using match_matches by blast 
  also have "\<dots> = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>Bs\<rangle>\<^sub>\<alpha>"
    by (intro term_subst_eq, insert 2 v, auto) 
  finally show ?thesis using Bs 2 by auto 
qed

lemma apply_subst_wf_pterm:
  assumes "A \<in> wf_pterm R"
    and "\<forall>x \<in> vars_term A. \<sigma> x \<in> wf_pterm R"
  shows "A \<cdot> \<sigma> \<in> wf_pterm R"
  using assms proof(induct A)
  case (2 ts f)
  {fix t assume t:"t \<in> set ts"
    with 2(2) have "(\<forall>x\<in>vars_term t. \<sigma> x \<in> wf_pterm R)"
      by (meson term.set_intros(4)) 
    with t 2(1) have "t \<cdot> \<sigma> \<in> wf_pterm R"
      by blast
  }
  then show ?case unfolding eval_term.simps by (simp add: wf_pterm.intros(2))
next
  case (3 \<alpha> As)
  {fix a assume a:"a \<in> set As"
    with 3(4) have "(\<forall>x\<in>vars_term a. \<sigma> x \<in> wf_pterm R)"
      by (meson term.set_intros(4)) 
    with a 3(3) have "a \<cdot> \<sigma> \<in> wf_pterm R"
      by blast
  }
  with 3(1,2) show ?case unfolding eval_term.simps by (simp add: wf_pterm.intros(3))
qed simp

lemma subst_well_def:
  assumes "B \<in> wf_pterm R" "A \<cdot> \<sigma> = B" "x \<in> vars_term A"
  shows "\<sigma> x \<in> wf_pterm R"
  using assms by (metis (no_types, lifting) poss_imp_subst_poss eval_term.simps(1) subt_at_is_wf_pterm subt_at_subst vars_term_poss_subt_at)

lemma lhs_subst_args_wf_pterm:
  assumes "to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha> \<in> wf_pterm R" and "length As = length (var_rule \<alpha>)"
  shows "\<forall>a \<in> set As. a \<in> wf_pterm R"
proof-
 from assms have "map (\<langle>As\<rangle>\<^sub>\<alpha>) (var_rule \<alpha>) = As"
    using apply_lhs_subst_var_rule by blast 
  with assms show ?thesis
    by (smt comp_apply in_set_idx map_nth_eq_conv nth_mem set_remdups set_rev set_vars_term_list subst_well_def vars_to_pterm) 
qed
 
lemma match_well_def:
  assumes "B \<in> wf_pterm R" "match B A = Some \<sigma>"
  shows "\<forall>i < length (vars_distinct A). \<sigma> ((vars_distinct A) ! i) \<in> wf_pterm R"
  using assms subst_well_def match_matches
  by (smt comp_apply nth_mem set_remdups set_rev set_vars_term_list)

lemma subst_imp_well_def:
  assumes "A \<cdot> \<sigma> \<in> wf_pterm R"
  shows "A \<in> wf_pterm R"
  using assms proof(induct A)
  case (Pfun f As)
  {fix i assume i:"i < length As"
    with Pfun(2) have "(As!i) \<cdot> \<sigma> \<in> wf_pterm R" 
      by auto
    with Pfun(1) i have "As!i \<in> wf_pterm R"
      by simp 
  }
  then show ?case using wf_pterm.intros(2)
    by (metis in_set_idx)
next
  case (Prule \<alpha> As)
  {fix i assume i:"i < length As"
    with Prule(2) have "(As!i) \<cdot> \<sigma> \<in> wf_pterm R" 
      by auto
    with Prule(1) i have "As!i \<in> wf_pterm R"
      by simp 
  }
  moreover from Prule(2) have "to_rule \<alpha> \<in> R" "length As = length (var_rule \<alpha>)"
    using wf_pterm.cases by force+
  ultimately show ?case using wf_pterm.intros(3) Prule(2) 
    by (metis in_set_idx)
qed simp

lemma lhs_subst_var_i:
  assumes "x = (var_rule \<alpha>)!i" and "i < length (var_rule \<alpha>)" and "i < length As"
  shows "(\<langle>As\<rangle>\<^sub>\<alpha>) x = As!i"
  using assms mk_subst_distinct distinct_remdups by (metis comp_apply distinct_rev)

lemma lhs_subst_not_var_i:
  assumes "\<not>(\<exists>i < length As. i < length (var_rule \<alpha>) \<and> x = (var_rule \<alpha>)!i)"
  shows "(\<langle>As\<rangle>\<^sub>\<alpha>) x = Var x"
  using assms proof(rule contrapos_np)
  {assume "(\<langle>As\<rangle>\<^sub>\<alpha>) x \<noteq> Var x"
    then obtain i where "i < length (zip (var_rule \<alpha>) As)" and "(var_rule \<alpha>)!i = x" 
      unfolding mk_subst_def by (smt assms imageE in_set_zip map_of_eq_None_iff option.case_eq_if) 
    then show "\<exists>i<length As. i < length (var_rule \<alpha>) \<and> x = var_rule \<alpha> ! i"
      by auto 
  }
qed

lemma lhs_subst_upd:
  assumes "length ss1 < length (var_rule \<alpha>)"
  shows "((\<langle>ss1 @ t # ss2\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!(length ss1) := s)) = \<langle>ss1 @ s # ss2\<rangle>\<^sub>\<alpha>"
proof
  fix x
  show "((\<langle>ss1 @ t # ss2\<rangle>\<^sub>\<alpha>)(var_rule \<alpha> ! length ss1 := s)) x = (\<langle>ss1 @ s # ss2\<rangle>\<^sub>\<alpha>) x" proof(cases "x = (var_rule \<alpha>)!(length ss1)")
    case True
    with assms have "((\<langle>ss1 @ t # ss2\<rangle>\<^sub>\<alpha>)(var_rule \<alpha> ! length ss1 := s)) x = s"
      by simp  
    moreover from assms have "(\<langle>ss1 @ s # ss2\<rangle>\<^sub>\<alpha>) x = s" unfolding True
      by (smt (verit, del_insts) add.commute add_Suc_right le_add_same_cancel2 le_imp_less_Suc length_append length_nth_simps(2) lhs_subst_var_i nth_append_length zero_order(1)) 
    ultimately show ?thesis by simp
  next
    case False
    then show ?thesis
      by (smt (verit, del_insts) append_Cons_nth_not_middle fun_upd_apply length_append length_nth_simps(2) lhs_subst_not_var_i lhs_subst_var_i) 
  qed
qed

lemma eval_lhs_subst:
  assumes l:"length (var_rule \<alpha>) = length As" 
  shows "(to_pterm (lhs \<alpha>)) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha> \<cdot> \<sigma> = (to_pterm (lhs \<alpha>)) \<cdot> \<langle>map (\<lambda>a. a \<cdot> \<sigma>) As\<rangle>\<^sub>\<alpha>" 
proof-
  {fix x assume "x \<in> vars_term (to_pterm (lhs \<alpha>))" 
    then obtain i where i:"i < length (var_rule \<alpha>)" "(var_rule \<alpha>) !i = x"
      using vars_to_pterm by (metis in_set_conv_nth set_vars_term_list vars_term_list_vars_distinct) 
    with l have "(\<langle>As\<rangle>\<^sub>\<alpha>) x = As!i"
      by (metis lhs_subst_var_i) 
    then have 1:"(\<langle>As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s \<sigma>) x = As!i \<cdot> \<sigma>"
      unfolding subst_compose_def by simp
    from i l have "(\<langle>map (\<lambda>a. a \<cdot> \<sigma>) As\<rangle>\<^sub>\<alpha>) x = map (\<lambda>a. a \<cdot> \<sigma>) As ! i" 
      using lhs_subst_var_i by (metis length_map) 
    with 1 i l have "(\<langle>As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s \<sigma>) x = (\<langle>map (\<lambda>a. a \<cdot> \<sigma>) As\<rangle>\<^sub>\<alpha>) x" by simp
  }
  then show ?thesis
    by (smt (verit, ccfv_SIG) eval_same_vars_cong subst_subst_compose) 
qed

lemma var_rule_pos_subst:
  assumes "i < length (var_rule \<alpha>)" "length ss = length (var_rule \<alpha>)" 
    and "p \<in> poss (lhs \<alpha>)" "Var ((var_rule \<alpha>)!i) = (lhs \<alpha>)|_p" 
  shows "lhs \<alpha> \<cdot> \<langle>ss\<rangle>\<^sub>\<alpha> |_ (p@q) = (ss!i)|_q"
proof-
  from assms(1,2) have "(\<langle>ss\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) = ss!i"
    using lhs_subst_var_i by force 
  with assms(3,4) show ?thesis by auto
qed

lemma lhs_subst_var_rule:
  assumes "vars_term t \<subseteq> vars_term (lhs \<alpha>)" 
  shows "t \<cdot> \<langle>map \<sigma> (var_rule \<alpha>)\<rangle>\<^sub>\<alpha> = t \<cdot> \<sigma>"
  using assms by (smt (verit, ccfv_SIG) apply_lhs_subst_var_rule comp_apply length_map map_eq_conv set_remdups set_rev set_vars_term_list subsetD term_subst_eq_conv)

subsection\<open>Contexts\<close>
lemma match_lhs_context:
  assumes "i < length (vars_term_list t) \<and> p = (var_poss_list t)!i"
    and "linear_term t"
    and "match (((ctxt_of_pos_term p (t \<cdot> \<sigma>)))\<langle>B\<rangle>) t = Some \<tau>"
shows "map \<tau> (vars_term_list t) = (map \<sigma> (vars_term_list t))[i := B] "
proof-
  from assms have "(ctxt_of_pos_term p (t \<cdot> \<sigma>))\<langle>B\<rangle> = t \<cdot> (\<sigma>(vars_term_list t!i := B))"
    using ctxt_apply_term_subst by blast
  with assms(3) have *:"(\<forall>x\<in>vars_term t. (\<sigma>(vars_term_list t!i := B)) x = \<tau> x)" 
    using match_complete' by (metis option.inject)
  from assms(2) have "distinct (vars_term_list t)"
    by (metis distinct_remdups distinct_rev linear_term_var_vars_term_list o_apply) 
  with * assms(1) show ?thesis
    by (smt (verit, ccfv_threshold) fun_upd_other fun_upd_same length_list_update length_map map_nth_eq_conv nth_eq_iff_index_eq nth_list_update nth_mem set_vars_term_list)
qed

lemma ctxt_lhs_subst:
  assumes i:"i < length (var_poss_list (lhs \<alpha>))" and l:"length As = length (var_rule \<alpha>)"
    and p1:"p1 = var_poss_list (lhs \<alpha>) ! i" and lin:"linear_term (lhs \<alpha>)" 
    and "p2 \<in> poss (As!i)"
  shows "(ctxt_of_pos_term (p1 @ p2) (to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>))\<langle>A\<rangle> = 
         (to_pterm (lhs \<alpha>)) \<cdot> \<langle>take i As @ (ctxt_of_pos_term p2 (As!i))\<langle>A\<rangle> # drop (Suc i) As\<rangle>\<^sub>\<alpha>"
proof-
  have l2:"length (var_poss_list (lhs \<alpha>)) = length (var_rule \<alpha>)" 
    using lin by (metis length_var_poss_list linear_term_var_vars_term_list) 
  from p1 i have p1_pos:"p1 \<in> poss (to_pterm (lhs \<alpha>))"
    by (metis nth_mem var_poss_imp_poss var_poss_list_sound var_poss_to_pterm) 
  have sub:"(to_pterm (lhs \<alpha>))|_p1 = Var (vars_term_list (lhs \<alpha>)!i)"
    by (metis i length_var_poss_list p1 var_poss_list_to_pterm vars_term_list_var_poss_list vars_to_pterm)
  have **: "(to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>)|_p1 = As!i" 
    unfolding subt_at_subst[OF p1_pos] sub eval_term.simps using i l l2 by (metis lhs_subst_var_i lin linear_term_var_vars_term_list) 
  then have *:"(ctxt_of_pos_term (p1 @ p2) (to_pterm (lhs \<alpha>) \<cdot> \<langle>As\<rangle>\<^sub>\<alpha>)) = ((ctxt_of_pos_term p1 (to_pterm (lhs \<alpha>))) \<cdot>\<^sub>c \<langle>As\<rangle>\<^sub>\<alpha>) \<circ>\<^sub>c (ctxt_of_pos_term p2 (As!i))"
    using ctxt_of_pos_term_append ctxt_of_pos_term_subst by (metis p1_pos poss_imp_subst_poss) 
  show ?thesis
    by (smt (verit, ccfv_threshold) * ** ctxt_ctxt_compose
        ctxt_subst_apply lhs_subst_upd append_Cons_nth_not_middle 
        i id_take_nth_drop l l2 less_imp_le_nat lin linear_term_var_vars_term_list 
        nth_append_take p1_pos sub to_pterm_linear
        ctxt_of_pos_term_append ctxt_supt_id eval_term.simps(1) poss_imp_subst_poss
        replace_at_append_subst subt_at_subst)
qed

lemma ctxt_rule_obtain_pos:
  assumes iq:"i#q \<in> poss (Prule \<alpha> As)"
    and p_pos:"p \<in> poss (source (Prule \<alpha> As))"
    and ctxt:"source_ctxt (ctxt_of_pos_term (i#q) (Prule \<alpha> As)) = ctxt_of_pos_term p (source (Prule \<alpha> As))"
    and lin:"linear_term (lhs \<alpha>)"
    and l:"length As = length (var_rule \<alpha>)" 
  shows "\<exists>p1 p2. p = p1@p2 \<and> p1 = var_poss_list (lhs \<alpha>)!i \<and> p2 \<in> poss (source (As!i))" 
proof-
  from iq have i:"i < length As"
    by simp 
  let ?p1="var_poss_list (lhs \<alpha>)!i"
  have p1:"(var_poss_list (lhs \<alpha>) ! length (take i As)) = ?p1"
    using i by fastforce 
  have p1_pos:"?p1 \<in> poss (lhs \<alpha>)"
    by (metis i l length_var_poss_list lin linear_term_var_vars_term_list nth_mem var_poss_imp_poss var_poss_list_sound)
  then have *:"source_ctxt (ctxt_of_pos_term (i # q) (Prule \<alpha> As)) = ((ctxt_of_pos_term ?p1 (lhs \<alpha>)) \<cdot>\<^sub>c \<langle>map source (take i As @ Var (vars_term_list (lhs \<alpha>) ! length (take i As)) # drop (Suc i) As)\<rangle>\<^sub>\<alpha>) \<circ>\<^sub>c
    source_ctxt (ctxt_of_pos_term q (As ! i))" 
    unfolding ctxt_of_pos_term.simps source_ctxt.simps Let_def p1 by (simp add: ctxt_of_pos_term_subst)
  from ctxt have "?p1  \<le>\<^sub>p p" 
    unfolding * using p1_pos p_pos unfolding source.simps using ctxt_subst_comp_pos by blast
  then obtain p2 where p:"p = ?p1@p2"
    using less_eq_pos_def by force 
  have "(lhs \<alpha>)|_?p1 = Var (vars_term_list (lhs \<alpha>) !i)"
    by (metis i l lin linear_term_var_vars_term_list vars_term_list_var_poss_list) 
  moreover have "Var (vars_term_list (lhs \<alpha>) !i) \<cdot> \<langle>map source As\<rangle>\<^sub>\<alpha> = source (As!i)"
    unfolding eval_term.simps using lhs_subst_var_i i l by (smt (verit, best) length_map lin linear_term_var_vars_term_list nth_map) 
  ultimately have "p2 \<in> poss (source (As!i))" 
    using p_pos unfolding p using p1_pos by auto 
  with p show ?thesis by simp
qed

subsection\<open>Source and Target\<close>
lemma source_empty_step:
  assumes "is_empty_step t"
  shows "to_pterm (source t) = t"
using assms by (induction t) (simp_all add: list_all_length map_nth_eq_conv)

lemma empty_coinitial:
  shows "co_initial A t \<Longrightarrow> is_empty_step t \<Longrightarrow> to_pterm (source A) = t"
  by (simp add: source_empty_step)

lemma source_to_pterm[simp]: "source (to_pterm t) = t"
  by (induction t) (simp_all add: map_nth_eq_conv)
  
lemma target_to_pterm[simp]: "target (to_pterm t) = t"
  by (induction t) (simp_all add: map_nth_eq_conv)

lemma vars_term_source:
  assumes "A \<in> wf_pterm R"
  shows "vars_term A = vars_term (source A)"
  using assms proof(induct A)
  case (3 \<alpha> As)
  show ?case proof
    {fix x assume "x \<in> vars_term (Prule \<alpha> As)"
      then obtain i where i:"i < length As" "x \<in> vars_term (As!i)"
        by (metis term.sel(4) var_imp_var_of_arg) 
      from i(1) 3(2) obtain j where j:"j < length (vars_term_list (lhs \<alpha>))" "vars_term_list (lhs \<alpha>)!j = var_rule \<alpha> !i"
        by (metis comp_apply in_set_idx nth_mem set_remdups set_rev)
      let ?p="(var_poss_list (lhs \<alpha>)!j)"
      from j have p:"?p \<in> poss (lhs \<alpha>)"
        by (metis in_set_conv_nth length_var_poss_list var_poss_imp_poss var_poss_list_sound) 
      with 3(2) i(1) j have "source (Prule \<alpha> As) |_ ?p = source (As!i)" 
        using mk_subst_distinct unfolding source.simps
        by (smt (verit, best) comp_apply distinct_remdups distinct_rev filter_cong length_map map_nth_conv mk_subst_same eval_term.simps(1) subt_at_subst vars_term_list_var_poss_list)  
      with 3(3) have "x \<in> vars_term (source (Prule \<alpha> As))"
        unfolding source.simps using vars_term_subt_at p
        by (smt (verit, ccfv_SIG) i nth_mem poss_imp_subst_poss subsetD)
    } 
    then show "vars_term (Prule \<alpha> As) \<subseteq> vars_term (source (Prule \<alpha> As))"
      by blast 
    {fix x assume "x \<in> vars_term (source (Prule \<alpha> As))"
      then obtain y where y:"y \<in> vars_term (lhs \<alpha>)"  "x \<in> vars_term ((\<langle>map source As\<rangle>\<^sub>\<alpha>) y)"
        using vars_term_subst by force 
      then obtain i where i:"i < length (var_rule \<alpha>)" "y = var_rule \<alpha>!i"
        by (metis in_set_idx set_vars_term_list vars_term_list_vars_distinct) 
      with y(2) 3(2) have "x \<in> vars_term (source (As!i))"
        by (simp add: mk_subst_distinct) 
      with 3 i(1) have "x \<in> vars_term (Prule \<alpha> As)"
        by (metis nth_mem term.set_intros(4))
    }
    then show "vars_term (source (Prule \<alpha> As)) \<subseteq> vars_term (Prule \<alpha> As)" 
      by blast
  qed
qed auto

context var_rhs_subset_lhs
begin
lemma vars_term_target:
  assumes "A \<in> wf_pterm R"
  shows "vars_term (target A) \<subseteq> vars_term A"
  using assms proof(induct A)
  case (3 \<alpha> As)
  show ?case proof
  fix x assume "x \<in> vars_term (target (Prule \<alpha> As))"
    then obtain y where y:"y \<in> vars_term (rhs \<alpha>)"  "x \<in> vars_term ((\<langle>map target As\<rangle>\<^sub>\<alpha>) y)"
      using vars_term_subst by force 
    then have "y \<in> vars_term (lhs \<alpha>)"
      using "3.hyps"(1) varcond by auto 
    then obtain i where i:"i < length (var_rule \<alpha>)" "y = var_rule \<alpha>!i"
      by (metis in_set_idx set_vars_term_list vars_term_list_vars_distinct) 
    with y(2) 3(2) have "x \<in> vars_term (target (As!i))"
      by (simp add: mk_subst_distinct) 
    with 3 i(1) show "x \<in> vars_term (Prule \<alpha> As)"
      by fastforce
  qed
qed auto
end

lemma linear_source_imp_linear_pterm:
  assumes "A \<in> wf_pterm R" "linear_term (source A)" 
  shows "linear_term A" 
  using assms proof(induct A)
  case (2 As f)
  then show ?case unfolding source.simps linear_term.simps using vars_term_source
    by (smt (verit, ccfv_SIG) in_set_idx length_map map_equality_iff nth_map nth_mem)
next
  case (3 \<alpha> As)
  {fix a assume a:"a \<in> set As"
    with 3(2) obtain i where i:"i < length (var_rule \<alpha>)" "As!i = a"
      by (metis in_set_idx) 
    let ?x="var_rule \<alpha> ! i"
    from i have "?x \<in> vars_term (lhs \<alpha>)"
      by (metis comp_apply nth_mem set_remdups set_rev set_vars_term_list)
    then obtain p where "p \<in> poss (lhs \<alpha>)" "lhs \<alpha> |_p = Var ?x"
      by (meson vars_term_poss_subt_at) 
    then have "source (Prule \<alpha> As) \<unrhd> source a" 
      unfolding source.simps using lhs_subst_var_i[of ?x \<alpha> i As] i 3(2)
      by (smt (verit, best) \<open>var_rule \<alpha> ! i \<in> vars_term (lhs \<alpha>)\<close> apply_lhs_subst_var_rule eval_term.simps(1) length_map map_nth_conv supteq_subst vars_term_supteq)
    then have "linear_term (source a)" 
      using 3(4) by (metis subt_at_linear supteq_imp_subt_at) 
    with 3(3) a have "linear_term a" by simp
  }
  moreover have "is_partition (map vars_term As)" proof-
    {fix i j assume i:"i < length As" and j:"j < length As" and ij:"i \<noteq> j"
      let ?x="var_rule \<alpha> ! i" and ?y="var_rule \<alpha> ! j" 
      from i j ij 3(2) have xy:"?x \<noteq> ?y"
        by (simp add: nth_eq_iff_index_eq) 
      from i 3(2) have "?x \<in> vars_term (lhs \<alpha>)"
        by (metis comp_apply nth_mem set_remdups set_rev set_vars_term_list)
      then obtain p where p:"p \<in> poss (lhs \<alpha>)" "lhs \<alpha> |_p = Var ?x"
        by (meson vars_term_poss_subt_at) 
      from j 3(2) have "?y \<in> vars_term (lhs \<alpha>)"
        by (metis comp_apply nth_mem set_remdups set_rev set_vars_term_list)
      then obtain q where q:"q \<in> poss (lhs \<alpha>)" "lhs \<alpha> |_q = Var ?y"
        by (meson vars_term_poss_subt_at) 
      from xy p q have "p \<bottom> q"
        using less_eq_pos_def parallel_pos by auto 
      moreover have "source (Prule \<alpha> As) |_p = source (As!i)" 
        unfolding source.simps by (metis (mono_tags, lifting) "3.hyps"(2) eval_term.simps(1) i length_map lhs_subst_var_i nth_map p subt_at_subst) 
      moreover have "source (Prule \<alpha> As) |_q = source (As!j)" 
        unfolding source.simps by (metis (mono_tags, lifting) "3.hyps"(2) eval_term.simps(1) j length_map lhs_subst_var_i nth_map q subt_at_subst) 
      ultimately have "vars_term (source (As!i)) \<inter> vars_term (source (As!j)) = {}" 
        using 3(4) by (metis linear_subterms_disjoint_vars p(1) poss_imp_subst_poss q(1) source.simps(3)) 
      then have "vars_term (As!i) \<inter> vars_term (As!j) = {}"
        using vars_term_source 3(3) i j using nth_mem by blast
    }
    then show ?thesis 
      unfolding is_partition_alt is_partition_alt_def by simp
    qed
  ultimately show ?case unfolding source.simps linear_term.simps by simp
qed simp

context var_rhs_subset_lhs
begin
lemma target_apply_subst:
  assumes "A \<in> wf_pterm R"
  shows "target (A \<cdot> \<sigma>) = (target A) \<cdot> (target \<circ> \<sigma>)"
using assms(1) proof(induct A)
  case (2 ts f)
  then have "(map target (map (\<lambda>t. t \<cdot> \<sigma>) ts)) = (map (\<lambda>t. t \<cdot> (target \<circ> \<sigma>)) (map target ts))"
    unfolding map_map o_def by auto
  then show ?case unfolding eval_term.simps target.simps by simp
next
  case (3 \<alpha> As)
  have id:"\<forall> x \<in> vars_term (rhs \<alpha>). (\<langle>map (target \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) x = (\<langle>map target As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (target \<circ> \<sigma>)) x"
    proof-
      have vars:"vars_term (rhs \<alpha>) \<subseteq> set (var_rule \<alpha>)" 
        using 3(1) varcond by auto
    { fix i assume i:"i < length (var_rule \<alpha>)"
      with 3 have "(\<langle>map (target \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) = target ((As!i) \<cdot> \<sigma>)" 
        by (simp add: mk_subst_distinct)
      also have "... = target (As!i) \<cdot> (target \<circ> \<sigma>)" 
        using 3 i by (metis nth_mem) 
      also have "... = (\<langle>map target As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (target \<circ> \<sigma>)) ((var_rule \<alpha>)!i)" 
        using 3 i unfolding subst_compose_def by (simp add: mk_subst_distinct)
      finally have "(\<langle>map (target \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) = (\<langle>map target As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (target \<circ> \<sigma>)) ((var_rule \<alpha>)!i)" .
    } with vars show ?thesis by (smt (z3) in_mono in_set_conv_nth) 
    qed
  have "target ((Prule \<alpha> As) \<cdot> \<sigma>) = (rhs \<alpha>) \<cdot> \<langle>map (target \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>" 
    unfolding eval_term.simps(2) by simp
  also have "... = (rhs \<alpha>) \<cdot> (\<langle>map target As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (target \<circ> \<sigma>))" 
    using id by (meson term_subst_eq)
  also have "... = (target (Prule \<alpha> As)) \<cdot> (target \<circ> \<sigma>)" by simp
  finally show ?case .
qed simp
end

context var_rhs_subset_lhs
begin
lemma tgt_subst_simp:
assumes "A \<in> wf_pterm R"
  shows "target (A \<cdot> \<sigma>) = target ((to_pterm (target A)) \<cdot> \<sigma>)"
  by (metis assms target_apply_subst target_to_pterm to_pterm_wf_pterm)
end

lemma target_empty_apply_subst:
  assumes "is_empty_step t"
  shows "target (t \<cdot> \<sigma>) = (target t) \<cdot> (target \<circ> \<sigma>)"
using assms proof(induction t)
  case (Var x)
  then show ?case by (metis comp_apply eval_term.simps(1) target.simps(1))
next
  case (Pfun f As)
  from Pfun(2) have "\<forall>a \<in> set As. is_empty_step a"
    by (simp add: Ball_set_list_all) 
  with Pfun(1) show ?case by simp
next
  case (Prule \<alpha> As)
  then show ?case
    using is_empty_step.simps(3) by blast
qed

lemma source_ctxt_comp:"source_ctxt (C1 \<circ>\<^sub>c C2) = source_ctxt C1 \<circ>\<^sub>c source_ctxt C2"
  by(induct C1) (simp_all add:ctxt_monoid_mult.mult_assoc)

lemma context_source: "source (A\<langle>B\<rangle>) = source (A\<langle>to_pterm (source B)\<rangle>)" 
proof(induct A rule:actxt.induct)
  case (More f ss1 A ss2)
  then show ?case by(cases f) simp_all
qed simp

lemma context_target: "target (A\<langle>B\<rangle>) = target (A\<langle>to_pterm (target B)\<rangle>)" 
proof(induct A rule:actxt.induct)
  case (More f ss1 A ss2)
  then show ?case by(cases f) simp_all
qed simp

lemma source_to_pterm_ctxt:
  "source ((to_pterm_ctxt C)\<langle>A\<rangle>) = C\<langle>source A\<rangle>"
  by (metis context_source source_to_pterm to_pterm_ctxt_apply_term)   

lemma target_to_pterm_ctxt:
  "target ((to_pterm_ctxt C)\<langle>A\<rangle>) = C\<langle>target A\<rangle>"   
  by (metis context_target target_to_pterm to_pterm_ctxt_apply_term)   

lemma source_ctxt_to_pterm: 
  assumes "p \<in> poss s"
  shows "source_ctxt (ctxt_of_pos_term p (to_pterm s)) = ctxt_of_pos_term p s" 
using assms proof(induct p arbitrary:s)
  case (Cons i p)
  then obtain f ss where s:"s = Fun f ss" and "i < length ss" and "p \<in> poss (ss!i)"
    using args_poss by blast 
  then show ?case 
    unfolding s to_pterm.simps ctxt_of_pos_term.simps source_ctxt.simps using Cons(1)
    by (smt (verit, best) drop_map nth_map source.simps(2) source_to_pterm take_map term.inject(2) to_pterm.simps(2))
qed simp

lemma to_pterm_ctxt_at_pos:
  assumes "p \<in> poss s"
  shows  "ctxt_of_pos_term p (to_pterm s) = to_pterm_ctxt (ctxt_of_pos_term p s)"
using assms proof(induct p arbitrary:s)
  case (Cons i p)
  then obtain f ss where s:"s = Fun f ss"
    using args_poss by blast 
  with Cons show ?case
    using drop_map s take_map by force
qed simp

lemma to_pterm_ctxt_hole_pos: "hole_pos C = hole_pos (to_pterm_ctxt C)"
  by(induct C) simp_all

lemma source_to_pterm_ctxt':
  assumes "q \<in> poss s"
  shows "source_ctxt (to_pterm_ctxt (ctxt_of_pos_term q s)) = ctxt_of_pos_term q s"
using assms proof(induct q arbitrary: s)
  case (Cons i q)
  then obtain f ss where s:"s = Fun f ss" and i:"i < length ss"
    by (meson args_poss) 
  with Cons have IH:"source_ctxt (to_pterm_ctxt (ctxt_of_pos_term q (ss!i))) = ctxt_of_pos_term q (ss!i)"
    by auto
  with i show ?case unfolding s ctxt_of_pos_term.simps to_pterm_ctxt.simps source_ctxt.simps
    using source_to_pterm by (metis source.simps(2) term.sel(4) to_pterm.simps(2)) 
qed simp

lemma to_pterm_ctxt_comp: "to_pterm_ctxt (C \<circ>\<^sub>c D) = to_pterm_ctxt C \<circ>\<^sub>c to_pterm_ctxt D"
  by(induct C) simp_all

lemma source_apply_subst: 
  assumes "A \<in> wf_pterm R"
  shows "source (A \<cdot> \<sigma>) = (source A) \<cdot> (source \<circ> \<sigma>)"
using assms proof(induct A)
  case (3 \<alpha> As)
  have id:"\<forall> x \<in> vars_term (lhs \<alpha>). (\<langle>map (source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) x = (\<langle>map source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (source \<circ> \<sigma>)) x"
    proof-
      have vars:"vars_term (lhs \<alpha>) = set (var_rule \<alpha>)" by simp
    { fix i assume i:"i < length (var_rule \<alpha>)"
      with 3 have "(\<langle>map (source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) = source ((As!i) \<cdot> \<sigma>)" 
        by (simp add: mk_subst_distinct)
      also have "... = source (As!i) \<cdot> (source \<circ> \<sigma>)" 
        using 3 i by (metis nth_mem) 
      also have "... = (\<langle>map source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (source \<circ> \<sigma>)) ((var_rule \<alpha>)!i)" 
        using 3 i unfolding subst_compose_def by (simp add: mk_subst_distinct)
      finally have "(\<langle>map (source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) = (\<langle>map source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (source \<circ> \<sigma>)) ((var_rule \<alpha>)!i)" .
    } with vars show ?thesis by (metis in_set_idx) 
  qed
  have "source ((Prule \<alpha> As) \<cdot> \<sigma>) = (lhs \<alpha>) \<cdot> \<langle>map (source \<circ> (\<lambda>t. t \<cdot> \<sigma>)) As\<rangle>\<^sub>\<alpha>" 
    unfolding eval_term.simps(2) by simp
  also have "... = (lhs \<alpha>) \<cdot> (\<langle>map source As\<rangle>\<^sub>\<alpha> \<circ>\<^sub>s (source \<circ> \<sigma>))" 
    using id by (meson term_subst_eq)
  also have "... = (source (Prule \<alpha> As)) \<cdot> (source \<circ> \<sigma>)" by simp
  finally show ?case .
qed simp_all

lemma ctxt_of_pos_term_at_var_subst: 
  assumes "linear_term t"
    and "p \<in> poss t" and "t|_p = Var x"
    and "\<forall>y \<in> vars_term t. y \<noteq> x \<longrightarrow> \<tau> y = \<sigma> y"
  shows "ctxt_of_pos_term p (t \<cdot> \<tau>) = ctxt_of_pos_term p (t \<cdot> \<sigma>)"
  using assms proof(induct t arbitrary:p)
  case (Fun f ts)
  from Fun(3,4) obtain i p' where p:"p = i#p'" and i:"i < length ts" and p':"p' \<in> poss (ts!i)"
    by auto 
  with Fun(4) have x:"ts!i |_p' = Var x" 
    by simp
  {fix j assume j:"j < length ts" "j \<noteq> i"
    from Fun(2) have "x \<notin> vars_term (ts!j)"
      by (metis i j p' subset_eq term.set_intros(3) var_in_linear_args vars_term_subt_at x)  
    with Fun(5) j have "ts!j \<cdot> \<tau> = ts!j \<cdot> \<sigma>"
      by (metis (no_types, lifting) nth_mem term.set_intros(4) term_subst_eq)
    then have "(map (\<lambda>t. t \<cdot> \<tau>) ts)!j = (map (\<lambda>t. t \<cdot> \<sigma>) ts)!j"
      by (simp add: j) 
  }note args=this
  from args have args1:"take i (map (\<lambda>t. t \<cdot> \<tau>) ts) = take i (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
     using nth_take_lemma[of i "(map (\<lambda>t. t \<cdot> \<tau>) ts)" "(map (\<lambda>t. t \<cdot> \<sigma>) ts)"] i by simp 
  from args have args2:"drop (Suc i) (map (\<lambda>t. t \<cdot> \<tau>) ts) = drop (Suc i) (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
     using nth_drop_equal[of "(map (\<lambda>t. t \<cdot> \<tau>) ts)" "(map (\<lambda>t. t \<cdot> \<sigma>) ts)" "Suc i"] i by simp 
  from Fun(1,2,5) i have IH:"ctxt_of_pos_term p' ((ts!i) \<cdot> \<tau>) = ctxt_of_pos_term p' ((ts!i) \<cdot> \<sigma>)"
    by (simp add: p' x)
  with args1 args2 show ?case 
    unfolding p eval_term.simps ctxt_of_pos_term.simps by (simp add: i)
qed simp

context left_lin
begin

lemma source_ctxt_apply_subst: 
  assumes "C \<in> wf_pterm_ctxt R"
  shows "source_ctxt (C \<cdot>\<^sub>c \<sigma>) = (source_ctxt C) \<cdot>\<^sub>c (source \<circ> \<sigma>)"
using assms proof(induct C)
  case (2 ss1 ss2 C f)
  then show ?case 
    unfolding source_ctxt.simps actxt.simps 2 using source_apply_subst by auto
next
  case (3 \<alpha> ss1 ss2 C)
  let ?p="(var_poss_list (lhs \<alpha>) ! length ss1)"
  let ?x="(vars_term_list (lhs \<alpha>) ! length ss1)"
  have var_at_p:"(lhs \<alpha>)|_?p = Var ?x"
    by (metis "3.hyps"(2) add_lessD1 length_remdups_leq length_rev less_add_one o_apply order_less_le_trans vars_term_list_var_poss_list) 
  from 3(2) have pos1:"?p \<in> poss (lhs \<alpha>)"
    by (metis add_lessD1 comp_apply length_remdups_leq length_rev length_var_poss_list less_add_one nth_mem order_less_le_trans var_poss_imp_poss var_poss_list_sound) 
  then have pos:"?p \<in> poss (lhs \<alpha> \<cdot> \<langle>map source (ss1 @ Var (vars_term_list (lhs \<alpha>) ! length ss1) # ss2)\<rangle>\<^sub>\<alpha>)"
    using poss_imp_subst_poss by blast 
  have lin:"linear_term (lhs \<alpha>)" 
    using 3(1) left_lin using left_linear_trs_def by fastforce 
  {fix y assume "y \<in> vars_term (lhs \<alpha>)" and x:"y \<noteq> ?x"
    then obtain i where i:"i < length (var_rule \<alpha>)" "var_rule \<alpha> ! i = y"
      by (metis in_set_idx lin linear_term_var_vars_term_list set_vars_term_list) 
    with x consider "i < length ss1" | "i > length ss1 \<and> i < length (var_rule \<alpha>)"
      using lin linear_term_var_vars_term_list nat_neq_iff by fastforce
    then have "(\<langle>map source (map (\<lambda>t. t \<cdot> \<sigma>) ss1 @ Var ?x # map (\<lambda>t. t \<cdot> \<sigma>) ss2)\<rangle>\<^sub>\<alpha>) y = ((\<langle>map source (ss1 @ Var ?x # ss2)\<rangle>\<^sub>\<alpha>) y) \<cdot> (source \<circ> \<sigma>)"
    proof(cases)
      case 1
      with i have "(\<langle>map source (map (\<lambda>t. t \<cdot> \<sigma>) ss1 @ Var ?x # map (\<lambda>t. t \<cdot> \<sigma>) ss2)\<rangle>\<^sub>\<alpha>) y = source ((ss1!i) \<cdot> \<sigma>)"
        by (smt (z3) "3.hyps"(2) One_nat_def add.right_neutral add_Suc_right append_Cons_nth_left comp_apply distinct_remdups distinct_rev length_append length_map length_nth_simps(2) map_nth_eq_conv mk_subst_same) 
      moreover from i 1 have "(\<langle>map source (ss1 @ Var ?x # ss2)\<rangle>\<^sub>\<alpha>) y = source (ss1!i)"
        by (smt (verit, ccfv_threshold) "3.hyps"(2) One_nat_def ab_semigroup_add_class.add_ac(1) append_Cons_nth_left comp_apply distinct_remdups distinct_rev length_append length_map list.size(4) map_nth_eq_conv mk_subst_distinct) 
      moreover have "ss1!i \<in> wf_pterm R" 
        using 3(3) 1 by (meson UnCI nth_mem) 
      ultimately show ?thesis 
        using source_apply_subst by auto
    next
      case 2
      let ?i="i - ((length ss1)+1)"
      have i':"?i < length ss2" 
        using 3(2) 2 by (simp add: less_diff_conv2) 
      have i1:"(map source (map (\<lambda>t. t \<cdot> \<sigma>) ss1 @ Var ?x # map (\<lambda>t. t \<cdot> \<sigma>) ss2))!i = source ((ss2!?i) \<cdot> \<sigma>)" proof-
        have i'':"i = length (map source (map (\<lambda>t. t \<cdot> \<sigma>) ss1 @ [Var ?x])) + ?i" 
          unfolding length_append length_map using "2" by force 
        show ?thesis unfolding map_append list.map 
          using i' i'' nth_append_length_plus[of "(map source (map (\<lambda>t. t \<cdot> \<sigma>) ss1 @ [Var (vars_term_list (lhs \<alpha>) ! length ss1)]))" "map source (map (\<lambda>t. t \<cdot> \<sigma>) ss2)"]
          by (smt (verit, del_insts) Cons_eq_appendI append_Nil append_assoc length_map list.simps(9) map_append nth_map) 
      qed
      have i2:"map source (ss1 @ Var ?x # ss2) ! i = source (ss2!?i)" proof-
        have i'':"i = length (map source (ss1 @ [Var ?x])) + ?i" 
          unfolding length_append length_map using "2" by force 
        show ?thesis unfolding map_append list.map 
          using i' i'' nth_append_length_plus[of "(map source (ss1 @ [Var (vars_term_list (lhs \<alpha>) ! length ss1)]))" "map source ss2"]
          by (smt (verit, del_insts) append.left_neutral append_Cons append_assoc length_map list.simps(9) map_append nth_map) 
      qed
      from i1 2 have "(\<langle>map source (map (\<lambda>t. t \<cdot> \<sigma>) ss1 @ Var ?x # map (\<lambda>t. t \<cdot> \<sigma>) ss2)\<rangle>\<^sub>\<alpha>) y = source ((ss2!?i) \<cdot> \<sigma>)"
        by (smt (verit, ccfv_threshold) "3.hyps"(2) One_nat_def ab_semigroup_add_class.add_ac(1) comp_def distinct_remdups distinct_rev i(2) length_append length_map list.size(4) mk_subst_distinct) 
      moreover from i2 2 have "(\<langle>map source (ss1 @ Var ?x # ss2)\<rangle>\<^sub>\<alpha>) y = source (ss2!?i)"
        by (metis (no_types, opaque_lifting) "3.hyps"(2) One_nat_def add.right_neutral add_Suc_right comp_apply distinct_remdups distinct_rev i(2) length_append length_map length_nth_simps(2) mk_subst_distinct)
      moreover have "ss2!?i \<in> wf_pterm R" 
        using 3(3) 2 \<open>?i < length ss2\<close>  by (metis UnCI nth_mem) 
      ultimately show ?thesis 
        using source_apply_subst by auto
    qed
  }
  then have "ctxt_of_pos_term ?p (lhs \<alpha> \<cdot> \<langle>map source (map (\<lambda>t. t \<cdot> \<sigma>) ss1 @ Var ?x # map (\<lambda>t. t \<cdot> \<sigma>) ss2)\<rangle>\<^sub>\<alpha>) = 
             ctxt_of_pos_term ?p (lhs \<alpha> \<cdot> \<langle>map source (ss1 @ Var ?x # ss2)\<rangle>\<^sub>\<alpha> \<cdot> (source \<circ> \<sigma>))"
    using ctxt_of_pos_term_at_var_subst[OF lin pos1 var_at_p] unfolding subst_subst by (smt (verit) subst_compose)
  then show ?case unfolding source_ctxt.simps actxt.simps Let_def 3 subst_compose_ctxt_compose_distrib length_map ctxt_of_pos_term_subst[OF pos, symmetric] 
    by presburger
qed simp

text\<open>Needs left-linearity to avoid multihole contexts.\<close>
lemma source_ctxt_apply_term: 
  assumes "C \<in> wf_pterm_ctxt R"
  shows "source (C\<langle>A\<rangle>) = (source_ctxt C)\<langle>source A\<rangle>"
using assms proof(induct C)
  case (3 \<alpha> ss1 ss2 C)
  from 3(1) left_lin have lin:"linear_term (lhs \<alpha>)"
    using left_linear_trs_def by fastforce 
  from 3(2) have len:"length ss1 < length (vars_term_list (lhs \<alpha>))"
    by (metis add_lessD1 less_add_one lin linear_term_var_vars_term_list)  
  have "(source_ctxt (Crule \<alpha> ss1 C ss2))\<langle>source A\<rangle> = 
      lhs \<alpha> \<cdot> \<langle>(map source ss1) @ (source_ctxt C)\<langle>source A\<rangle> # (map source ss2)\<rangle>\<^sub>\<alpha>"
    unfolding source_ctxt.simps Let_def intp_actxt.simps source.simps ctxt_ctxt_compose
    using ctxt_apply_term_subst[OF lin len] lhs_subst_upd
    by (smt (verit) len length_map lin linear_term_var_vars_term_list list.simps(9) map_append) 
  with 3(5) show ?case by simp 
qed simp_all
end

lemma rewrite_tgt:
  assumes rstep:"(t,v) \<in> (rstep R)\<^sup>*"
  shows "(target (C \<langle>(to_pterm t) \<cdot> \<sigma>\<rangle>), target (C \<langle>(to_pterm v) \<cdot> \<sigma>\<rangle>)) \<in> (rstep R)\<^sup>*"
proof(induct C)
  case Hole
  then show ?case
    by (simp add: local.rstep rsteps_closed_subst target_empty_apply_subst to_pterm_empty) 
next
  case (Cfun f ss1 C ss2)
  then show ?case by (simp add: ctxt_closed_one ctxt_closed_rsteps)
next
  case (Crule \<alpha> ss1 C ss2)
  {fix x assume "x \<in> vars_term (rhs \<alpha>)"
    from Crule have "((\<langle>map target (ss1 @ C\<langle>to_pterm t \<cdot> \<sigma>\<rangle> # ss2)\<rangle>\<^sub>\<alpha>) x, (\<langle>map target (ss1 @ C\<langle>to_pterm v \<cdot> \<sigma>\<rangle> # ss2)\<rangle>\<^sub>\<alpha>) x) \<in> (rstep R)\<^sup>*"
    proof(cases "x \<in> vars_term (lhs \<alpha>)")
      case True
      then obtain i where "i < length (vars_distinct (lhs \<alpha>))" "x = vars_distinct (lhs \<alpha>)!i"
        by (metis in_set_idx set_vars_term_list vars_term_list_vars_distinct)
      then show ?thesis using Crule
        by (smt (z3) append_Cons_nth_not_middle length_append length_map length_nth_simps(2) lhs_subst_not_var_i lhs_subst_var_i map_nth_eq_conv nth_append_length rtrancl.simps) 
    next
      case False
      then show ?thesis
        by (simp add: mk_subst_not_mem)
    qed
  }
  then show ?case by (simp add: subst_rsteps_imp_rsteps)
qed

subsection\<open>Additional Results\<close>

lemma length_args_well_Prule:
  assumes "Prule \<alpha> As \<in> wf_pterm R" "Prule \<alpha> Bs \<in> wf_pterm S"
  shows "length As = length Bs"
proof-
  from assms(1) have "length As = length (var_rule \<alpha>)" using wf_pterm.simps by fastforce
  moreover from assms(2) have "length Bs = length (var_rule \<alpha>)" using wf_pterm.simps by fastforce
  ultimately show ?thesis by simp
qed

lemma co_initial_Var:
  assumes "co_initial (Var x) B"
  shows "B = Var x \<or> (\<exists>\<alpha> b' y. B = Prule \<alpha> b' \<and> lhs \<alpha> = Var y)"
proof-
  {assume "B \<noteq> Var x"
    with assms obtain \<alpha> b' where "B = Prule \<alpha> b'"
      by (metis is_empty_step.elims(3) source.elims source_empty_step term.distinct(1))
    moreover with assms have "\<exists> y. lhs \<alpha> = Var y"
      by (metis source.simps(1) source.simps(3) subst_apply_eq_Var) 
    ultimately have "(\<exists>\<alpha> b' y. B = Prule \<alpha> b' \<and> lhs \<alpha> = Var y)"
      by blast 
  }
  then show ?thesis
    by blast
qed

lemma source_poss:
  assumes p:"p \<in> poss (source (Pfun f As))" and iq:"i#q \<in> poss (Pfun f As)"
    and ctxt:"source_ctxt (ctxt_of_pos_term (i#q) (Pfun f As)) = ctxt_of_pos_term p (source (Pfun f As))"
  shows "\<exists>p'. p = i#p' \<and> p' \<in> poss (source (As!i))"
proof-
  obtain p' where "hole_pos (source_ctxt (ctxt_of_pos_term (i#q) (Pfun f As))) = i#p'" 
                  "p' = hole_pos (source_ctxt (ctxt_of_pos_term q (As ! i)))"
    unfolding ctxt_of_pos_term.simps source_ctxt.simps take_map drop_map using iq by auto 
  with ctxt have "p = i#p'"
    by (metis hole_pos_ctxt_of_pos_term p) 
  with p show ?thesis
    by auto 
qed

lemma simple_pterm_match:
  assumes "source A = t \<cdot> \<sigma>"
    and "linear_term t"
    and "A \<cdot> \<tau>1 = to_pterm t \<cdot> \<tau>2"
  shows "matches A (to_pterm t)" 
  using assms proof(induct t arbitrary: A)
  case (Var x)
  then show ?case
    using matches_iff by force
next
  case (Fun f ts)
  from Fun(2,4) show ?case proof(cases A)
    case (Pfun g As)
    with Fun(2) have f:"f = g" by simp
    from Fun(2) have l:"length ts = length As" 
      unfolding Pfun source.simps f eval_term.simps by (simp add: map_equality_iff) 
    {fix i assume i:"i < length ts" 
      with Fun(2) have "source (As ! i) = ts ! i \<cdot> \<sigma>" 
        unfolding Pfun source.simps f eval_term.simps by (simp add: map_equality_iff)
      moreover from i Fun(4) have "As ! i \<cdot> \<tau>1 = to_pterm (ts ! i) \<cdot> \<tau>2" 
        unfolding Pfun f to_pterm.simps eval_term.simps using l map_nth_conv by fastforce 
      ultimately have "matches (As!i) (to_pterm (ts!i))" 
        using Fun(1)[of "ts!i" "As!i"] l i Fun(3) by force
      then have "\<exists>\<sigma>. As!i = (to_pterm (ts!i)) \<cdot> \<sigma>"
        by (metis matches_iff) 
    }note IH=this
    from Fun(3) have lin:"linear_term (to_pterm (Fun f ts))"
      using to_pterm_linear by blast 
    from linear_term_obtain_subst[OF lin[unfolded to_pterm.simps]] show ?thesis 
      unfolding Pfun f by (smt (verit, del_insts) IH l length_map matches_iff nth_map to_pterm.simps(2)) 
  qed simp_all
qed

subsection \<open>Proof Terms Represent Multi-Steps\<close>

context var_rhs_subset_lhs
begin
lemma mstep_to_pterm:
  assumes "(s, t) \<in> mstep R"
  shows "\<exists>A. A \<in> wf_pterm R \<and> source A = s \<and> target A = t"
  using assms(1) proof(induct)
  case (Var x)
  then show ?case
    by (meson source.simps(1) target.simps(1) wf_pterm.intros(1))
next
  case (args f n ss ts)
  then have "\<forall>i\<in>set [0..<n]. \<exists>a. a \<in> wf_pterm R \<and> source a = ss ! i \<and> target a = ts ! i"
    by simp 
  then obtain As where as:"length As = n \<and> (\<forall>i < n. (As!i) \<in> wf_pterm R \<and> source (As!i) = ss ! i \<and> target (As!i) = ts ! i)"  
    using obtain_list_with_property[where P="\<lambda>a i. a \<in> wf_pterm R \<and> source a = ss!i \<and> target a = ts!i" and xs="[0..<n]"]
    by (metis add.left_neutral diff_zero length_upt nth_upt set_upt)      
  with args(1) have "source (Pfun f As) = Fun f ss" 
    unfolding source.simps by (simp add: map_nth_eq_conv) 
  moreover from as args(2) have "target (Pfun f As) = Fun f ts" 
    unfolding target.simps by (simp add: map_nth_eq_conv) 
  ultimately show ?case 
    using as by (metis in_set_idx wf_pterm.intros(2))
next
  case (rule l r \<sigma> \<tau>)
  let ?\<alpha> ="(l \<rightarrow> r)"
  have "set (vars_distinct l) = vars_term l"
    by simp
  with rule(2) obtain As where as:"length As = length (vars_distinct l) \<and> 
     (\<forall>i < length (vars_distinct l). (As!i) \<in> wf_pterm R \<and> 
     source (As!i) = \<sigma> ((vars_distinct l) ! i) \<and> target (As!i) = \<tau> ((vars_distinct l) ! i))"  
    using obtain_list_with_property[where P="\<lambda>a x. a \<in> wf_pterm R \<and> source a = \<sigma> x \<and> target a = \<tau> x"] by blast
  with rule(1) have well:"Prule ?\<alpha> As \<in> wf_pterm R"
    by (metis in_set_idx prule.sel(1) prule.sel(2) wf_pterm.simps) 
  from as have "\<forall>x \<in> vars_term l. (\<langle>map source As\<rangle>\<^sub>?\<alpha>) x = \<sigma> x"
    by (smt (z3) apply_lhs_subst_var_rule in_set_idx length_map map_nth_conv prule.sel(1) set_vars_term_list vars_term_list_vars_distinct)
  then have s:"source (Prule ?\<alpha> As) = l \<cdot> \<sigma>"
    by (simp add: term_subst_eq_conv) 
  from as varcond have "\<forall>x \<in> vars_term r. (\<langle>map target As\<rangle>\<^sub>?\<alpha>) x = \<tau> x"
    by (smt (verit, best) apply_lhs_subst_var_rule fst_conv in_set_conv_nth length_map nth_map prule.sel(1) 
        rule.hyps(1) set_vars_term_list snd_conv split_beta subsetD vars_term_list_vars_distinct) 
  then have "target (Prule ?\<alpha> As) = r \<cdot> \<tau>" 
    by (simp add: term_subst_eq_conv) 
  with well s show ?case 
    by blast
qed
end

lemma pterm_to_mstep:
  assumes "A \<in> wf_pterm R"
  shows "(source A, target A) \<in> mstep R "
  using assms proof(induct)
  case (2 As f)
  then show ?case
    by (simp add: mstep.args)
next
  case (3 \<alpha> As)
  then have "\<forall>x\<in>vars_term (lhs \<alpha>). ((\<langle>map source As\<rangle>\<^sub>\<alpha>) x, (\<langle>map target As\<rangle>\<^sub>\<alpha>) x) \<in> mstep R"
    by (smt (verit, best) apply_lhs_subst_var_rule comp_def in_set_idx length_map map_nth_conv nth_mem set_remdups set_rev set_vars_term_list) 
  with 3(1) show ?case
    by (simp add: mstep.rule)
qed simp

lemma co_init_prule: 
  assumes "co_initial (Prule \<alpha> As) (Prule \<alpha> Bs)"
    and "Prule \<alpha> As \<in> wf_pterm R" and "Prule \<alpha> Bs \<in> wf_pterm R"
  shows "\<forall>i<length As. co_initial (As!i) (Bs!i)"
proof-
  from assms have l1:"length As = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  from assms have l2:"length Bs = length (var_rule \<alpha>)"
    using wf_pterm.simps by fastforce 
  {fix i assume i:"i < length As" and co:"\<not> (co_initial (As!i) (Bs!i))"
    then have "(\<langle>map source As\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i) \<noteq> (\<langle>map source Bs\<rangle>\<^sub>\<alpha>) ((var_rule \<alpha>)!i)"
      by (metis l1 l2 length_map lhs_subst_var_i nth_map) 
    with assms(1) have False unfolding source.simps
      by (smt (z3) comp_apply i l1 nth_mem set_remdups set_rev set_vars_term_list term_subst_eq_rev) 
  } then show ?thesis
    by blast 
qed

section\<open>Operations on Proof Terms\<close>
text\<open>The operations residual, deletion, and join on proof terms all fulfill 
@{text "A \<star> (source A) = A"} which implies several useful results.\<close>

locale op_proof_term = left_lin_no_var_lhs +
  fixes f :: "(('a, 'b) prule + 'a, 'b) Term.term \<Rightarrow> (('a, 'b) prule + 'a, 'b) Term.term \<Rightarrow> (('a, 'b) prule + 'a, 'b) Term.term option"
  assumes f_src:" A \<in> wf_pterm R \<Longrightarrow> f A (to_pterm (source A)) = Some A"
  and f_pfun:"f (Pfun g As)(Pfun g Bs) = (if length As = length Bs then
                                         (case those (map2 f As Bs) of
                                          Some xs \<Rightarrow> Some (Pfun g xs)
                                         | None \<Rightarrow> None) else None)"
  and f_prule:"f (Prule \<alpha> As) (Pfun g Bs) = (case match (Pfun g Bs)  (to_pterm (lhs \<alpha>)) of
                          None \<Rightarrow> None
                          | Some \<sigma> \<Rightarrow>
                            (case those (map2 f As (map \<sigma> (var_rule \<alpha>))) of
                              Some xs \<Rightarrow> Some (Prule \<alpha> xs)
                          | None \<Rightarrow> None))"
begin

notation
  f  ("'(\<star>')") and
  f  ("(_ \<star> _)"  [51, 51] 50)

lemma apply_f_ctxt: 
  assumes "C \<in> wf_pterm_ctxt R"
    and "A \<star> B = Some D"
  shows "C\<langle>A\<rangle> \<star> (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> = Some (C\<langle>D\<rangle>)"
  using assms proof(induct C rule:pterm_ctxt_induct)
  case (Cfun f ss1 C ss2)
   have l:"length ((map (to_pterm \<circ> source) ss1) @ (to_pterm_ctxt (source_ctxt C))\<langle>A\<rangle> # (map (to_pterm \<circ> source) ss2))
          = length (ss1 @ C\<langle>B\<rangle> # ss2)" by auto
   from Cfun(2) have well1:"\<forall>i < length ss1. (ss1!i) \<in> wf_pterm R" by auto
   from Cfun(2) have well2:"\<forall>i < length ss2. (ss2!i) \<in> wf_pterm R" by auto
   from Cfun have fC:"C\<langle>A\<rangle> \<star> (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> = Some (C\<langle>D\<rangle>)" 
     by auto
   from well1 have f1:"\<forall>i < length ss1. ((map2 (\<star>) ss1 (map (to_pterm \<circ> source) ss1))!i = Some (ss1!i))"
     using f_src to_pterm_empty by fastforce 
   from well2 have f2:"\<forall>i < length ss2. ((map2 (\<star>) ss2 (map (to_pterm \<circ> source) ss2))!i = Some (ss2!i))"
     using f_src to_pterm_empty by fastforce 
   {fix i assume i:"i < (length ss1) + (length ss2) +1"
     have "(map2 (\<star>) (ss1 @ (C\<langle>A\<rangle> # ss2))  
           (map (to_pterm \<circ> source) ss1 @ ((to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> # map (to_pterm \<circ> source) ss2)))!i 
           = Some ((ss1 @ C\<langle>D\<rangle> # ss2)!i)"
     proof-
       consider "i < length ss1" | "i = length ss1" | "i > length ss1"
         using nat_neq_iff by blast 
       then show ?thesis proof(cases)
         case 1
         then show ?thesis using f1
           by (simp add: append_Cons_nth_left)
       next
         case 2
         then show ?thesis using fC 
           by (simp add: append_Cons_nth_middle)
       next
         case 3
         with i have l:"(map (to_pterm \<circ> source) ss1 @ (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> # map (to_pterm \<circ> source) ss2)!i
                     = (map (to_pterm \<circ> source) ss2)!(i-(length ss1 + 1))"
           by (metis add.commute length_map less_SucI not_less_eq nth_append_Cons plus_1_eq_Suc)
         from 3 i have r:"(ss1 @ (C\<langle>to_pterm (source B)\<rangle> # ss2))!i = ss2!(i-(length ss1 + 1))"
           by (metis add.commute less_SucI not_less_eq nth_append_Cons plus_1_eq_Suc) 
         from l r 3 show ?thesis using f2
           by (smt One_nat_def add.right_neutral add_Suc add_Suc_right add_diff_inverse_nat add_less_cancel_left append_Cons_nth_right i length_append length_map length_zip list.size(4) min_less_iff_conj not_less_eq nth_map nth_zip)
       qed
     qed
   }
   with l have "those ((map2 (\<star>) (ss1 @ (C\<langle>A\<rangle> # ss2))  
              (map (to_pterm \<circ> source) ss1 @ ((to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> # map (to_pterm \<circ> source) ss2))))
            = Some (ss1 @ C\<langle>D\<rangle> # ss2)" by (simp add: those_some)
   with l show ?case using f_pfun by simp 
 next
   case (Crule \<alpha> ss1 C ss2)
   from Crule(2) have alpha:"to_rule \<alpha> \<in> R"
     using wf_pterm_ctxt.cases by auto 
   then have linear:"linear_term (lhs \<alpha>)"
     using left_lin left_linear_trs_def by fastforce
   then have linear':"linear_term (to_pterm (lhs \<alpha>))"
     using to_pterm_linear by blast
   have l1:"length ((map (to_pterm \<circ> source) ss1) @ (to_pterm_ctxt (source_ctxt C))\<langle>A\<rangle> # (map (to_pterm \<circ> source) ss2))
          = length (ss1 @ C\<langle>B\<rangle> # ss2)" by auto
   from Crule(2) have l2:"length (ss1 @ C\<langle>B\<rangle> # ss2) = length (var_rule \<alpha>)"
     using wf_pterm_ctxt.simps by fastforce
   from Crule(2) have well1:"\<forall>i < length ss1. (ss1!i) \<in> wf_pterm R" by auto
   from Crule(2) have well2:"\<forall>i < length ss2. (ss2!i) \<in> wf_pterm R" by auto
   from Crule have fC:"C\<langle>A\<rangle> \<star> (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> = Some (C\<langle>D\<rangle>)" 
     by auto
   from well1 have f1:"\<forall>i < length ss1. ((map2 (\<star>) ss1 (map (to_pterm \<circ> source) ss1))!i = Some (ss1!i))"
     using f_src to_pterm_empty by fastforce 
   from well2 have f2:"\<forall>i < length ss2. ((map2 (\<star>) ss2 (map (to_pterm \<circ> source) ss2))!i = Some (ss2!i))"
     using f_src to_pterm_empty by fastforce 
   {fix i assume i:"i < (length ss1) + (length ss2) +1"
     have "(map2 (\<star>) (ss1 @ (C\<langle>A\<rangle> # ss2)) (map (to_pterm \<circ> source) ss1 @ ((to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> # 
           (map (to_pterm \<circ> source) ss2))) )!i = Some ((ss1 @ C\<langle>D\<rangle> # ss2)!i)"
     proof-
       consider "i < length ss1" | "i = length ss1" | "i > length ss1"
         using nat_neq_iff by blast 
       then show ?thesis proof(cases)
         case 1
         then show ?thesis using f1
           by (simp add: append_Cons_nth_left)
       next
         case 2
         then show ?thesis using fC
           by (simp add: append_Cons_nth_middle)
       next
         case 3
         with i have l:"(map (to_pterm \<circ> source) ss1 @ (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> # map (to_pterm \<circ> source) ss2)!i
                     = (map (to_pterm \<circ> source) ss2)!(i-(length ss1 + 1))"
           by (metis add.commute length_map less_SucI not_less_eq nth_append_Cons plus_1_eq_Suc)
         from 3 i have r:"(ss1 @ (C\<langle>to_pterm (source B)\<rangle> # ss2))!i = ss2!(i-(length ss1 + 1))"
           by (metis add.commute less_SucI not_less_eq nth_append_Cons plus_1_eq_Suc) 
         from l r 3 show ?thesis using f2
           by (smt One_nat_def add.right_neutral add_Suc add_Suc_right add_diff_inverse_nat add_less_cancel_left append_Cons_nth_right i length_append length_map length_zip list.size(4) min_less_iff_conj not_less_eq nth_map nth_zip)
       qed
     qed
   }
   with l1 have IH:"those (map2 (\<star>) (ss1 @ (C\<langle>A\<rangle> # ss2)) (map (to_pterm \<circ> source) ss1 @ ((to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> # 
                         (map (to_pterm \<circ> source) ss2))) ) = Some (ss1 @ C\<langle>D\<rangle> # ss2)" by (simp add: those_some)
   let ?p = "(var_poss_list (lhs \<alpha>) ! length ss1)"
   let ?x = "vars_term_list (lhs \<alpha>) ! length ss1"
   let ?\<sigma> = "\<langle>map source (ss1 @ Var (vars_term_list (lhs \<alpha>) ! length ss1) # ss2)\<rangle>\<^sub>\<alpha>"
   from l2 linear have l3:"length ss1 < length (var_poss_list (lhs \<alpha>))"
     by (metis (no_types, lifting) add_Suc_right append_Cons_nth_left le_imp_less_Suc length_append length_var_poss_list linear_term_var_vars_term_list linorder_neqE_nat list.size(3) list.size(4) not_add_less1 nth_equalityI self_append_conv zero_order(1))
   then have "?p \<in> poss (lhs \<alpha>)"
     using nth_mem var_poss_imp_poss var_poss_list_sound by blast
   then have ctxt:"(to_pterm_ctxt (source_ctxt (Crule \<alpha> ss1 C ss2)))\<langle>B\<rangle> =
      (ctxt_of_pos_term ?p (to_pterm (lhs \<alpha>) \<cdot> (to_pterm \<circ> ?\<sigma>)))\<langle>(to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle>\<rangle>"
     unfolding source_ctxt.simps intp_actxt.simps Let_def ctxt_ctxt_compose to_pterm_ctxt_comp 
     using to_pterm_ctxt_at_pos[where ?p="?p" and ?s="lhs \<alpha> \<cdot> ?\<sigma>"] by (simp add: to_pterm_subst)
   from l3 have l4:"length ss1 < length (vars_term_list (to_pterm (lhs \<alpha>)))"
     by (metis length_var_poss_list vars_to_pterm) 
   have "(to_pterm_ctxt (source_ctxt (Crule \<alpha> ss1 C ss2)))\<langle>B\<rangle> = 
               to_pterm (lhs \<alpha>) \<cdot> ((to_pterm \<circ> ?\<sigma>)(?x := (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle>))"
     unfolding ctxt using ctxt_apply_term_subst[where ?p="?p" and ?t="to_pterm (lhs \<alpha>)" and ?i="length ss1" and ?s="(to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle>" and ?\<sigma>="(to_pterm \<circ> ?\<sigma>)"]
       linear' l4  var_poss_list_to_pterm vars_to_pterm by metis 
   then obtain \<tau> where \<tau>:"match (to_pterm_ctxt (source_ctxt (Crule \<alpha> ss1 C ss2)))\<langle>B\<rangle> (to_pterm (lhs \<alpha>)) = Some \<tau>" 
     unfolding ctxt using ctxt_apply_term_subst linear' match_complete' option.distinct(1) by force 
   have varr:"(var_rule \<alpha>) = vars_term_list (to_pterm (lhs \<alpha>))" 
     using linear linear_term_var_vars_term_list unfolding vars_to_pterm by force
   have "(map (to_pterm \<circ> ?\<sigma>) (vars_term_list (to_pterm (lhs \<alpha>)))) = map (to_pterm \<circ> source) (ss1 @ Var (vars_term_list (lhs \<alpha>) ! length ss1) # ss2)"
     using apply_lhs_subst_var_rule l2 unfolding varr[symmetric] by force
   then have "(map (to_pterm \<circ> ?\<sigma>) (vars_term_list (to_pterm (lhs \<alpha>))))[length ss1 := (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle>] = 
              (map (to_pterm \<circ> source) ss1 @ (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> # (map (to_pterm \<circ> source) ss2))"
     by (metis (no_types, lifting) length_map list.simps(9) list_update_length map_append) 
   with \<tau> have map_tau:"map \<tau> (var_rule \<alpha>) = (map (to_pterm \<circ> source) ss1 @ (to_pterm_ctxt (source_ctxt C))\<langle>B\<rangle> #
                                   (map (to_pterm \<circ> source) ss2))"  
     using match_lhs_context[where ?t="to_pterm (lhs \<alpha>)" and ?\<tau>=\<tau> and ?\<sigma>="(to_pterm \<circ> ?\<sigma>)"] 
       l4 var_poss_list_to_pterm linear' ctxt varr by metis
   from alpha no_var_lhs obtain f ts where f:"lhs \<alpha> = Fun f ts"
     by blast
   have "[] \<notin> var_poss (lhs \<alpha>)" 
     unfolding f var_poss.simps by force 
   then obtain i q where iq:"?p = i # q" using l3
     by (metis in_set_conv_nth subt_at.elims var_poss_list_sound)
   then obtain ts' where root_not_rule:"(to_pterm_ctxt (source_ctxt (Crule \<alpha> ss1 C ss2)))\<langle>B\<rangle> = Pfun f ts'"
     unfolding ctxt iq unfolding f by simp
   then show ?case 
     using \<tau> f_prule map_tau IH by force
 qed simp

end

end