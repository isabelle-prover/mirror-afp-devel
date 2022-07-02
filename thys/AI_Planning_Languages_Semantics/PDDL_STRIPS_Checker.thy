section \<open>Executable PDDL Checker\<close>
theory PDDL_STRIPS_Checker
imports
  PDDL_STRIPS_Semantics

  Error_Monad_Add
  "HOL.String"

  (*"HOL-Library.Code_Char"     TODO: This might lead to performance loss! CHECK! *)
  "HOL-Library.Code_Target_Nat"

  "HOL-Library.While_Combinator"

  "Containers.Containers"
begin

subsection \<open>Generic DFS Reachability Checker\<close>
text \<open>Used for subtype checks\<close>

definition "E_of_succ succ \<equiv> { (u,v). v\<in>set (succ u) }"
lemma succ_as_E: "set (succ x) = E_of_succ succ `` {x}"
  unfolding E_of_succ_def by auto

context
  fixes succ :: "'a \<Rightarrow> 'a list"
begin

  private abbreviation (input) "E \<equiv> E_of_succ succ"


definition "dfs_reachable D w \<equiv>
  let (V,w,brk) = while (\<lambda>(V,w,brk). \<not>brk \<and> w\<noteq>[]) (\<lambda>(V,w,_).
    case w of v#w \<Rightarrow>
    if D v then (V,v#w,True)
    else if v\<in>V then (V,w,False)
    else
      let V = insert v V in
      let w = succ v @ w in
      (V,w,False)
    ) ({},w,False)
  in brk"


context
  fixes w\<^sub>0 :: "'a list"
  assumes finite_dfs_reachable[simp, intro!]: "finite (E\<^sup>* `` set w\<^sub>0)"
begin

  private abbreviation (input) "W\<^sub>0 \<equiv> set w\<^sub>0"

definition "dfs_reachable_invar D V W brk \<longleftrightarrow>
    W\<^sub>0 \<subseteq> W \<union> V
  \<and> W \<union> V \<subseteq> E\<^sup>* `` W\<^sub>0
  \<and> E``V \<subseteq> W \<union> V
  \<and> Collect D \<inter> V = {}
  \<and> (brk \<longrightarrow> Collect D \<inter> E\<^sup>* `` W\<^sub>0 \<noteq> {})"

lemma card_decreases: "
   \<lbrakk>finite V; y \<notin> V; dfs_reachable_invar D V (Set.insert y W) brk \<rbrakk>
   \<Longrightarrow> card (E\<^sup>* `` W\<^sub>0 - Set.insert y V) < card (E\<^sup>* `` W\<^sub>0 - V)"
  apply (rule psubset_card_mono)
  apply (auto simp: dfs_reachable_invar_def)
  done

lemma all_neq_Cons_is_Nil[simp]: (* Odd term remaining in goal \<dots> *)
  "(\<forall>y ys. x2 \<noteq> y # ys) \<longleftrightarrow> x2 = []" by (cases x2) auto

lemma dfs_reachable_correct: "dfs_reachable D w\<^sub>0 \<longleftrightarrow> Collect D \<inter> E\<^sup>* `` set w\<^sub>0 \<noteq> {}"
  unfolding dfs_reachable_def
  apply (rule while_rule[where
    P="\<lambda>(V,w,brk). dfs_reachable_invar D V (set w) brk \<and> finite V"
    and r="measure (\<lambda>V. card (E\<^sup>* `` (set w\<^sub>0) - V)) <*lex*> measure length <*lex*> measure (\<lambda>True\<Rightarrow>0 | False\<Rightarrow>1)"
    ])
  subgoal by (auto simp: dfs_reachable_invar_def)
  subgoal
    apply (auto simp: neq_Nil_conv succ_as_E[of succ] split: if_splits)
    by (auto simp: dfs_reachable_invar_def Image_iff intro: rtrancl.rtrancl_into_rtrancl)
  subgoal by (fastforce simp: dfs_reachable_invar_def dest: Image_closed_trancl)
  subgoal by blast
  subgoal by (auto simp: neq_Nil_conv card_decreases)
  done

end

definition "tab_succ l \<equiv> Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l Mapping.empty)"


lemma Some_eq_map_option [iff]: "(Some y = map_option f xo) = (\<exists>z. xo = Some z \<and> f z = y)"
  by (auto simp add: map_option_case split: option.split)


lemma tab_succ_correct: "E_of_succ (tab_succ l) = set l"
proof -
  have "set (Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l m) u) = set l `` {u} \<union> set (Mapping.lookup_default [] m u)"
    for m u
    apply (induction l arbitrary: m)
    by (auto
      simp: Mapping.lookup_default_def Mapping.map_default_def Mapping.default_def
      simp: lookup_map_entry' lookup_update' keys_is_none_rep Option.is_none_def
      split: if_splits
    )
  from this[where m=Mapping.empty] show ?thesis
    by (auto simp: E_of_succ_def tab_succ_def lookup_default_empty)
qed

end

lemma finite_imp_finite_dfs_reachable:
  "\<lbrakk>finite E; finite S\<rbrakk> \<Longrightarrow> finite (E\<^sup>*``S)"
  apply (rule finite_subset[where B="S \<union> (Relation.Domain E \<union> Relation.Range E)"])
  apply (auto simp: intro: finite_Domain finite_Range elim: rtranclE)
  done

lemma dfs_reachable_tab_succ_correct: "dfs_reachable (tab_succ l) D vs\<^sub>0 \<longleftrightarrow> Collect D \<inter> (set l)\<^sup>*``set vs\<^sub>0 \<noteq> {}"
  apply (subst dfs_reachable_correct)
  by (simp_all add: tab_succ_correct finite_imp_finite_dfs_reachable)



subsection \<open>Implementation Refinements\<close>

subsubsection \<open>Of-Type\<close>

definition "of_type_impl G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))"


fun ty_term' where
  "ty_term' varT objT (term.VAR v) = varT v"
| "ty_term' varT objT (term.CONST c) = Mapping.lookup objT c"

lemma ty_term'_correct_aux: "ty_term' varT objT t = ty_term varT (Mapping.lookup objT) t"
  by (cases t) auto

lemma ty_term'_correct[simp]: "ty_term' varT objT = ty_term varT (Mapping.lookup objT)"
  using ty_term'_correct_aux by auto

context ast_domain begin

  definition "of_type1 pt T \<longleftrightarrow> pt \<in> subtype_rel\<^sup>* `` set (primitives T)"

  lemma of_type_refine1: "of_type oT T \<longleftrightarrow> (\<forall>pt\<in>set (primitives oT). of_type1 pt T)"
    unfolding of_type_def of_type1_def by auto

  definition "STG \<equiv> (tab_succ (map subtype_edge (types D)))"

  lemma subtype_rel_impl: "subtype_rel = E_of_succ (tab_succ (map subtype_edge (types D)))"
    by (simp add: tab_succ_correct subtype_rel_def)

  lemma of_type1_impl: "of_type1 pt T \<longleftrightarrow> dfs_reachable (tab_succ (map subtype_edge (types D))) ((=)pt) (primitives T)"
    by (simp add: subtype_rel_impl of_type1_def dfs_reachable_tab_succ_correct tab_succ_correct)

  lemma of_type_impl_correct: "of_type_impl STG oT T \<longleftrightarrow> of_type oT T"
    unfolding of_type1_impl STG_def of_type_impl_def of_type_refine1 ..

  definition mp_constT :: "(object, type) mapping" where
    "mp_constT = Mapping.of_alist (consts D)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_constT = constT"
    unfolding mp_constT_def constT_def
    by transfer (simp add: Map_To_Mapping.map_apply_def)






  text \<open>Lifting the subtype-graph through wf-checker\<close>
  context
    fixes ty_ent :: "'ent \<rightharpoonup> type"  \<comment> \<open>Entity's type, None if invalid\<close>
  begin

    definition "is_of_type' stg v T \<longleftrightarrow> (
      case ty_ent v of
        Some vT \<Rightarrow> of_type_impl stg vT T
      | None \<Rightarrow> False)"

    lemma is_of_type'_correct: "is_of_type' STG v T = is_of_type ty_ent v T"
      unfolding is_of_type'_def is_of_type_def of_type_impl_correct ..

    fun wf_pred_atom' where "wf_pred_atom' stg (p,vs) \<longleftrightarrow> (case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 (is_of_type' stg) vs Ts)"

    lemma wf_pred_atom'_correct: "wf_pred_atom' STG pvs = wf_pred_atom ty_ent pvs"
      by (cases pvs) (auto simp: is_of_type'_correct[abs_def] split:option.split)

    fun wf_atom' :: "_ \<Rightarrow> 'ent atom \<Rightarrow> bool" where
      "wf_atom' stg (atom.predAtm p vs) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_atom' stg (atom.Eq a b) = (ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None)"

    lemma wf_atom'_correct: "wf_atom' STG a = wf_atom ty_ent a"
      by (cases a) (auto simp: wf_pred_atom'_correct is_of_type'_correct[abs_def] split: option.splits)

    fun wf_fmla' :: "_ \<Rightarrow> ('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla' stg (Atom a) \<longleftrightarrow> wf_atom' stg a"
    | "wf_fmla' stg \<bottom> \<longleftrightarrow> True"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla' stg \<phi>"

    lemma wf_fmla'_correct: "wf_fmla' STG \<phi> \<longleftrightarrow> wf_fmla ty_ent \<phi>"
      by (induction \<phi> rule: wf_fmla.induct) (auto simp: wf_atom'_correct)

    fun wf_fmla_atom1' where
      "wf_fmla_atom1' stg (Atom (predAtm p vs)) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_fmla_atom1' stg _ \<longleftrightarrow> False"

    lemma wf_fmla_atom1'_correct: "wf_fmla_atom1' STG \<phi> = wf_fmla_atom ty_ent \<phi>"
      by (cases \<phi> rule: wf_fmla_atom.cases) (auto
        simp: wf_atom'_correct is_of_type'_correct[abs_def] split: option.splits)

    fun wf_effect' where
      "wf_effect' stg (Effect a d) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_fmla_atom1' stg ae)
        \<and> (\<forall>de\<in>set d.  wf_fmla_atom1' stg de)"

    lemma wf_effect'_correct: "wf_effect' STG e = wf_effect ty_ent e"
      by (cases e) (auto simp: wf_fmla_atom1'_correct)

  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>

  fun wf_action_schema' :: "_ \<Rightarrow> _ \<Rightarrow> ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema' stg conT (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyv = ty_term' (map_of params) conT
      in
        distinct (map fst params)
      \<and> wf_fmla' tyv stg pre
      \<and> wf_effect' tyv stg eff)"

  lemma wf_action_schema'_correct: "wf_action_schema' STG mp_constT s = wf_action_schema s"
    by (cases s) (auto simp: wf_fmla'_correct wf_effect'_correct)

  definition wf_domain' :: "_ \<Rightarrow> _ \<Rightarrow> bool" where
    "wf_domain' stg conT \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts D). wf_type T)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema' stg conT a)
    "

  lemma wf_domain'_correct: "wf_domain' STG mp_constT = wf_domain"
    unfolding wf_domain_def wf_domain'_def
    by (auto simp: wf_action_schema'_correct)


end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Application of Effects\<close>

context ast_domain begin
  text \<open>We implement the application of an effect by explicit iteration over
    the additions and deletions\<close>
  fun apply_effect_exec
    :: "object ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
  where
    "apply_effect_exec (Effect a d) s
      = fold (\<lambda>add s. Set.insert add s) a
          (fold (\<lambda>del s. Set.remove del s) d s)"

  lemma apply_effect_exec_refine[simp]:
    "apply_effect_exec (Effect (a) (d)) s
    = apply_effect (Effect (a) (d)) s"
  proof(induction a arbitrary: s)
    case Nil
    then show ?case
    proof(induction d arbitrary: s)
      case Nil
      then show ?case by auto
    next
      case (Cons a d)
      then show ?case
        by (auto simp add: image_def)
    qed
  next
    case (Cons a a)
    then show ?case
    proof(induction d arbitrary: s)
      case Nil
      then show ?case by (auto; metis Set.insert_def sup_assoc insert_iff)
    next
      case (Cons a d)
      then show ?case
        by (auto simp: Un_commute minus_set_fold union_set_fold)
    qed
  qed

  lemmas apply_effect_eq_impl_eq
    = apply_effect_exec_refine[symmetric, unfolded apply_effect_exec.simps]

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Well-Formedness\<close>

context ast_problem begin

  text \<open> We start by defining a mapping from objects to types. The container
    framework will generate efficient, red-black tree based code for that
    later. \<close>

  type_synonym objT = "(object, type) mapping"

  definition mp_objT :: "(object, type) mapping" where
    "mp_objT = Mapping.of_alist (consts D @ objects P)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_objT = objT"
    unfolding mp_objT_def objT_alt
    by transfer (simp add: Map_To_Mapping.map_apply_def)

  text \<open>We refine the typecheck to use the mapping\<close>

  definition "is_obj_of_type_impl stg mp n T = (
    case Mapping.lookup mp n of None \<Rightarrow> False | Some oT \<Rightarrow> of_type_impl stg oT T
  )"

  lemma is_obj_of_type_impl_correct[simp]:
    "is_obj_of_type_impl STG mp_objT = is_obj_of_type"
    apply (intro ext)
    apply (auto simp: is_obj_of_type_impl_def is_obj_of_type_def of_type_impl_correct split: option.split)
    done

  text \<open>We refine the well-formedness checks to use the mapping\<close>

  definition wf_fact' :: "objT \<Rightarrow> _ \<Rightarrow> fact \<Rightarrow> bool"
    where
    "wf_fact' ot stg \<equiv> wf_pred_atom' (Mapping.lookup ot) stg"

  lemma wf_fact'_correct[simp]: "wf_fact' mp_objT STG = wf_fact"
    by (auto simp: wf_fact'_def wf_fact_def wf_pred_atom'_correct[abs_def])


  definition "wf_fmla_atom2' mp stg f
    = (case f of formula.Atom (predAtm p vs) \<Rightarrow> (wf_fact' mp stg (p,vs)) | _ \<Rightarrow> False)"

  lemma wf_fmla_atom2'_correct[simp]:
    "wf_fmla_atom2' mp_objT STG \<phi> = wf_fmla_atom objT \<phi>"
    apply (cases \<phi> rule: wf_fmla_atom.cases)
    by (auto simp: wf_fmla_atom2'_def wf_fact_def split: option.splits)

  definition "wf_problem' stg conT mp \<equiv>
      wf_domain' stg conT
    \<and> distinct (map fst (objects P) @ map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> (\<forall>f\<in>set (init P). wf_fmla_atom2' mp stg f)
    \<and> wf_fmla' (Mapping.lookup mp) stg (goal P)"

  lemma wf_problem'_correct:
    "wf_problem' STG mp_constT mp_objT = wf_problem"
    unfolding wf_problem_def wf_problem'_def wf_world_model_def
    by (auto simp: wf_domain'_correct wf_fmla'_correct)


  text \<open>Instantiating actions will yield well-founded effects.
    Corollary of @{thm wf_instantiate_action_schema}.\<close>
  lemma wf_effect_inst_weak:
    fixes a args
    defines "ai \<equiv> instantiate_action_schema a args"
    assumes A: "action_params_match a args"
      "wf_action_schema a"
    shows "wf_effect_inst (effect ai)"
    using wf_instantiate_action_schema[OF A] unfolding ai_def[symmetric]
    by (cases ai) (auto simp: wf_effect_inst_alt)


end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>


context wf_ast_domain begin
  text \<open>Resolving an action yields a well-founded action schema.\<close>
  (* TODO: This must be implicitly proved when showing that plan execution
    preserves wf. Try to remove this redundancy!*)
  lemma resolve_action_wf:
    assumes "resolve_action_schema n = Some a"
    shows "wf_action_schema a"
  proof -
    from wf_domain have
      X1: "distinct (map ast_action_schema.name (actions D))"
      and X2: "\<forall>a\<in>set (actions D). wf_action_schema a"
      unfolding wf_domain_def by auto

    show ?thesis
      using assms unfolding resolve_action_schema_def
      by (auto simp add: index_by_eq_Some_eq[OF X1] X2)
  qed

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


subsubsection \<open>Execution of Plan Actions\<close>

text \<open>We will perform two refinement steps, to summarize redundant operations\<close>

text \<open>We first lift action schema lookup into the error monad. \<close>
context ast_domain begin
  definition "resolve_action_schemaE n \<equiv>
    lift_opt
      (resolve_action_schema n)
      (ERR (shows ''No such action schema '' o shows n))"
end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

context ast_problem begin

(*TODO: change to this valuation definition to hanlde equalities nicely
definition "valuation s \<equiv> \<lambda>x. case x of (atom.Atom P ARGS) \<Rightarrow>
                                                ((formula.Atom x) \<in> s)
                                    | (atom.Eq t1 t2) \<Rightarrow> (t1 = t2)"

primrec holds :: "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" where
"holds s (Atom k) = ((Atom k) \<in> s)" |
"holds _ \<bottom> = False" |
"holds s (Not F) = (\<not> (holds s F))" |
"holds s (And F G) = (holds s F \<and> holds s G)" |
"holds s (Or F G) = (holds s F \<or> holds s G)" |
"holds s (Imp F G) = (holds s F \<longrightarrow> holds s G)"

  lemma holds_for_valid_formulas:
        assumes "\<forall>x\<in>s. \<exists>x'. x = formula.Atom x'"
        shows "s \<TTurnstile> F \<Longrightarrow> holds s F"
        unfolding holds_def entailment_def
        using assms
        apply (induction F; auto)
        subgoal for x apply(cases x)*)


  text \<open>We define a function to determine whether a formula holds in
    a world model\<close>
  definition "holds M F \<equiv> (valuation M) \<Turnstile> F"

  text \<open>Justification of this function\<close>

  lemma holds_for_wf_fmlas:
    assumes "wm_basic s"
    shows "holds s F \<longleftrightarrow> close_world s \<TTurnstile> F"
    unfolding holds_def using assms valuation_iff_close_world
    by blast

  (*
  lemma holds_for_wf_fmlas:
    assumes "\<forall>x\<in>s. is_Atom x" "wf_fmla Q F"
    shows "holds s F \<longleftrightarrow> s \<TTurnstile> F"
    unfolding holds_def entailment_def valuation_def
    using assms
  proof (induction F)
    case (Atom x)
    then show ?case
      apply auto
      by (metis formula_semantics.simps(1) is_Atom.elims(2) valuation_def)
  next
    case (Or F1 F2)
    then show ?case
      apply simp apply (safe; clarsimp?)
      by (metis (mono_tags) is_Atom.elims(2) formula_semantics.simps(1))
  qed auto
  *)

  text \<open>The first refinement summarizes the enabledness check and the execution
    of the action. Moreover, we implement the precondition evaluation by our
     @{const holds} function. This way, we can eliminate redundant resolving
     and instantiation of the action.
  \<close>

  definition en_exE :: "plan_action \<Rightarrow> world_model \<Rightarrow> _+world_model" where
    "en_exE \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (wf_effect_inst (effect ai)) (ERRS ''Effect not well-formed'');
      check ( holds s (precondition ai)) (ERRS ''Precondition not satisfied'');
      Error_Monad.return (apply_effect (effect ai) s)
    }"

  text \<open>Justification of implementation.\<close>
  lemma (in wf_ast_problem) en_exE_return_iff:
    assumes "wm_basic s"
    shows "en_exE a s = Inr s'
      \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
    apply (cases a)
    using assms holds_for_wf_fmlas wf_domain
    unfolding plan_action_enabled_def execute_plan_action_def
      and execute_ground_action_def en_exE_def wf_domain_def
    by (auto
        split: option.splits
        simp: resolve_action_schemaE_def return_iff)

  text \<open>Next, we use the efficient implementation @{const is_obj_of_type_impl}
    for the type check, and omit the well-formedness check, as effects obtained
    from instantiating well-formed action schemas are always well-formed
    (@{thm [source] wf_effect_inst_weak}).\<close>
  abbreviation "action_params_match2 stg mp a args
    \<equiv> list_all2 (is_obj_of_type_impl stg mp)
        args (map snd (ast_action_schema.parameters a))"

  definition en_exE2
    :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> plan_action \<Rightarrow> world_model \<Rightarrow> _+world_model"
  where
    "en_exE2 G mp \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>M. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match2 G mp a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (holds M (precondition ai)) (ERRS ''Precondition not satisfied'');
      Error_Monad.return (apply_effect (effect ai) M)
    }"

  text \<open>Justification of refinement\<close>
  lemma (in wf_ast_problem) wf_en_exE2_eq:
    shows "en_exE2 STG mp_objT pa s = en_exE pa s"
    apply (cases pa; simp add: en_exE2_def en_exE_def Let_def)
    apply (auto
      simp: return_iff resolve_action_schemaE_def resolve_action_wf
      simp: wf_effect_inst_weak action_params_match_def
      split: error_monad_bind_split)
    done

  text \<open>Combination of the two refinement lemmas\<close>
  lemma (in wf_ast_problem) en_exE2_return_iff:
    assumes "wm_basic M"
    shows "en_exE2 STG mp_objT a M = Inr M'
      \<longleftrightarrow> plan_action_enabled a M \<and> M' = execute_plan_action a M"
    unfolding wf_en_exE2_eq
    apply (subst en_exE_return_iff)
    using assms
    by (auto)

  lemma (in wf_ast_problem) en_exE2_return_iff_compact_notation:
    "\<lbrakk>wm_basic s\<rbrakk> \<Longrightarrow>
      en_exE2 STG mp_objT a s = Inr s'
      \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
    using en_exE2_return_iff .

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

subsubsection \<open>Checking of Plan\<close>

context ast_problem begin

  text \<open>First, we combine the well-formedness check of the plan actions and
    their execution into a single iteration.\<close>
  fun valid_plan_from1 :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from1 s [] \<longleftrightarrow> close_world s \<TTurnstile> (goal P)"
  | "valid_plan_from1 s (\<pi>#\<pi>s)
      \<longleftrightarrow> plan_action_enabled \<pi> s
        \<and> (valid_plan_from1 (execute_plan_action \<pi> s) \<pi>s)"

  lemma valid_plan_from1_refine: "valid_plan_from s \<pi>s = valid_plan_from1 s \<pi>s"
  proof(induction \<pi>s arbitrary: s)
    case Nil
    then show ?case by (auto simp add: plan_action_path_def valid_plan_from_def)
  next
    case (Cons a \<pi>s)
    then show ?case
      by (auto
        simp: valid_plan_from_def plan_action_path_def plan_action_enabled_def
        simp: execute_ground_action_def execute_plan_action_def)
  qed

  text \<open>Next, we use our efficient combined enabledness check and execution
    function, and transfer the implementation to use the error monad: \<close>
  fun valid_plan_fromE
    :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> nat \<Rightarrow> world_model \<Rightarrow> plan \<Rightarrow> _+unit"
  where
    "valid_plan_fromE stg mp si s []
      = check (holds s (goal P)) (ERRS ''Postcondition does not hold'')"
  | "valid_plan_fromE stg mp si s (\<pi>#\<pi>s) = do {
        s \<leftarrow> en_exE2 stg mp \<pi> s
          <+? (\<lambda>e _. shows ''at step '' o shows si o shows '': '' o e ());
        valid_plan_fromE stg mp (si+1) s \<pi>s
      }"


  text \<open>For the refinement, we need to show that the world models only
    contain atoms, i.e., containing only atoms is an invariant under execution
    of well-formed plan actions.\<close>
  lemma (in wf_ast_problem) wf_actions_only_add_atoms:
    "\<lbrakk> wm_basic s; wf_plan_action a \<rbrakk>
      \<Longrightarrow> wm_basic (execute_plan_action a s)"
    using wf_problem wf_domain
    unfolding wf_problem_def wf_domain_def
    apply (cases a)
    apply (clarsimp
      split: option.splits
      simp: wf_fmla_atom_alt execute_plan_action_def wm_basic_def
      simp: execute_ground_action_def)
    subgoal for n args schema fmla
      apply (cases "effect (instantiate_action_schema schema args)"; simp)
      by (metis ground_action.sel(2) ast_domain.wf_effect.simps
            ast_domain.wf_fmla_atom_alt resolve_action_wf
            wf_ground_action.elims(2) wf_instantiate_action_schema)
    done

  text \<open>Refinement lemma for our plan checking algorithm\<close>
  lemma (in wf_ast_problem) valid_plan_fromE_return_iff[return_iff]:
    assumes "wm_basic s"
    shows "valid_plan_fromE STG mp_objT k s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from s \<pi>s"
    using assms unfolding valid_plan_from1_refine
  proof (induction stg\<equiv>STG mp\<equiv>mp_objT k s \<pi>s rule: valid_plan_fromE.induct)
    case (1 si s)
    then show ?case
      using wf_problem holds_for_wf_fmlas
      by (auto
        simp: return_iff Let_def wf_en_exE2_eq wf_problem_def
        split: plan_action.split)
  next
    case (2 si s \<pi> \<pi>s)
    then show ?case
      apply (clarsimp
        simp: return_iff en_exE2_return_iff
        split: plan_action.split)
      by (meson ast_problem.plan_action_enabled_def wf_actions_only_add_atoms)
  qed

  lemmas valid_plan_fromE_return_iff'[return_iff]
    = wf_ast_problem.valid_plan_fromE_return_iff[of P, OF wf_ast_problem.intro]

  (* TODO: This function is unused! *)
  (*fun apply_effect_exec''
    :: "object atom ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
    where
    "apply_effect_exec'' (Effect (adds) (dels)) s
      = fold (%add s. insert add s)
          (map formula.Atom adds)
          (fold (%del s. Set.remove del s) (map formula.Atom dels) s)"
  *)


end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

subsection \<open>Executable Plan Checker\<close>
text \<open>We obtain the main plan checker by combining the well-formedness check
  and executability check. \<close>


definition "check_all_list P l msg msgf \<equiv>
  forallM (\<lambda>x. check (P x) (\<lambda>_::unit. shows msg o shows '': '' o msgf x) ) l <+? snd"

lemma check_all_list_return_iff[return_iff]: "check_all_list P l msg msgf = Inr () \<longleftrightarrow> (\<forall>x\<in>set l. P x)"
  unfolding check_all_list_def
  by (induction l) (auto)

definition "check_wf_types D \<equiv> do {
  check_all_list (\<lambda>(_,t). t=''object'' \<or> t\<in>fst`set (types D)) (types D) ''Undeclared supertype'' (shows o snd)
}"

lemma check_wf_types_return_iff[return_iff]: "check_wf_types D = Inr () \<longleftrightarrow> ast_domain.wf_types D"
  unfolding ast_domain.wf_types_def check_wf_types_def
  by (force simp: return_iff)

definition "check_wf_domain D stg conT \<equiv> do {
  check_wf_types D;
  check (distinct (map (predicate_decl.pred) (predicates D))) (ERRS ''Duplicate predicate declaration'');
  check_all_list (ast_domain.wf_predicate_decl D) (predicates D) ''Malformed predicate declaration'' (shows o predicate.name o predicate_decl.pred);
  check (distinct (map fst (consts D))) (ERRS  ''Duplicate constant declaration'');
  check (\<forall>(n,T)\<in>set (consts D). ast_domain.wf_type D T) (ERRS ''Malformed type'');
  check (distinct (map ast_action_schema.name (actions D))  ) (ERRS ''Duplicate action name'');
  check_all_list (ast_domain.wf_action_schema' D stg conT) (actions D) ''Malformed action'' (shows o ast_action_schema.name)

}"



lemma check_wf_domain_return_iff[return_iff]:
  "check_wf_domain D stg conT = Inr () \<longleftrightarrow> ast_domain.wf_domain' D stg conT"
proof -
  interpret ast_domain D .
  show ?thesis
    unfolding check_wf_domain_def wf_domain'_def
    by (auto simp: return_iff)
qed

definition "prepend_err_msg msg e \<equiv> \<lambda>_::unit. shows msg o shows '': '' o e ()"

definition "check_wf_problem P stg conT mp \<equiv> do {
  let D = ast_problem.domain P;
  check_wf_domain D stg conT <+? prepend_err_msg ''Domain not well-formed'';
  check (distinct (map fst (objects P) @ map fst (consts D))) (ERRS ''Duplicate object declaration'');
  check ((\<forall>(n,T)\<in>set (objects P). ast_domain.wf_type D T)) (ERRS ''Malformed type'');
  check (distinct (init P)) (ERRS ''Duplicate fact in initial state'');
  check (\<forall>f\<in>set (init P). ast_problem.wf_fmla_atom2' P mp stg f) (ERRS ''Malformed formula in initial state'');
  check (ast_domain.wf_fmla' D (Mapping.lookup mp) stg (goal P)) (ERRS ''Malformed goal formula'')
}"

lemma check_wf_problem_return_iff[return_iff]:
  "check_wf_problem P stg conT mp = Inr () \<longleftrightarrow> ast_problem.wf_problem' P stg conT mp"
proof -
  interpret ast_problem P .
  show ?thesis
    unfolding check_wf_problem_def wf_problem'_def
    by (auto simp: return_iff)
qed

definition "check_plan P \<pi>s \<equiv> do {
  let stg=ast_domain.STG (ast_problem.domain P);
  let conT = ast_domain.mp_constT (ast_problem.domain P);
  let mp = ast_problem.mp_objT P;
  check_wf_problem P stg conT mp;
  ast_problem.valid_plan_fromE P stg mp 1 (ast_problem.I P) \<pi>s
} <+? (\<lambda>e. String.implode (e () ''''))"

text \<open>Correctness theorem of the plan checker: It returns @{term "Inr ()"}
  if and only if the problem is well-formed and the plan is valid.
\<close>
theorem check_plan_return_iff[return_iff]: "check_plan P \<pi>s = Inr ()
  \<longleftrightarrow> ast_problem.wf_problem P \<and> ast_problem.valid_plan P \<pi>s"
proof -
  interpret ast_problem P .
  show ?thesis
    unfolding check_plan_def
    by (auto
      simp: return_iff wf_world_model_def wf_fmla_atom_alt I_def wf_problem_def isOK_iff
      simp: wf_problem'_correct ast_problem.I_def ast_problem.valid_plan_def wm_basic_def
      )
qed



subsection \<open>Code Setup\<close>

text \<open>In this section, we set up the code generator to generate verified
  code for our plan checker.\<close>

subsubsection \<open>Code Equations\<close>
text \<open>We first register the code equations for the functions of the checker.
  Note that we not necessarily register the original code equations, but also
  optimized ones.
\<close>

lemmas wf_domain_code =
  ast_domain.sig_def
  ast_domain.wf_types_def
  ast_domain.wf_type.simps
  ast_domain.wf_predicate_decl.simps
  ast_domain.STG_def
  ast_domain.is_of_type'_def
  ast_domain.wf_atom'.simps
  ast_domain.wf_pred_atom'.simps
  ast_domain.wf_fmla'.simps
  ast_domain.wf_fmla_atom1'.simps
  ast_domain.wf_effect'.simps
  ast_domain.wf_action_schema'.simps
  ast_domain.wf_domain'_def
  ast_domain.subst_term.simps
  ast_domain.mp_constT_def
(*
  ast_domain.wf_domain_def
  ast_domain.wf_action_schema.simps
  ast_domain.wf_effect.simps
  ast_domain.wf_fmla.simps
  ast_domain.wf_atom.simps
  ast_domain.is_of_type_def
  ast_domain.of_type_code
*)

declare wf_domain_code[code]

lemmas wf_problem_code =
  ast_problem.wf_problem'_def
  ast_problem.wf_fact'_def
  (*ast_problem.objT_def*)
  ast_problem.is_obj_of_type_alt
  (*ast_problem.wf_object_def*)
  ast_problem.wf_fact_def
  ast_problem.wf_plan_action.simps
  (*ast_problem.wf_effect_inst_weak.simps*)

  ast_domain.subtype_edge.simps
declare wf_problem_code[code]

lemmas check_code =
  ast_problem.valid_plan_def
  ast_problem.valid_plan_fromE.simps
  ast_problem.en_exE2_def
  ast_problem.resolve_instantiate.simps
  ast_domain.resolve_action_schema_def
  ast_domain.resolve_action_schemaE_def
  ast_problem.I_def
  ast_domain.instantiate_action_schema.simps
  ast_domain.apply_effect_exec.simps
  (*ast_domain.apply_effect_exec'.simps*)
  ast_domain.apply_effect_eq_impl_eq
  (*ast_domain.apply_atomic.simps*)
  ast_problem.holds_def
  ast_problem.mp_objT_def
  ast_problem.is_obj_of_type_impl_def
  ast_problem.wf_fmla_atom2'_def
  valuation_def
declare check_code[code]

subsubsection \<open>Setup for Containers Framework\<close>

derive ceq predicate atom object formula
derive ccompare predicate atom object formula
derive (rbt) set_impl atom formula

derive (rbt) mapping_impl object

derive linorder predicate object atom "object atom formula"

subsubsection \<open>More Efficient Distinctness Check for Linorders\<close>
(* TODO: Can probably be optimized even more. *)
fun no_stutter :: "'a list \<Rightarrow> bool" where
  "no_stutter [] = True"
| "no_stutter [_] = True"
| "no_stutter (a#b#l) = (a\<noteq>b \<and> no_stutter (b#l))"

lemma sorted_no_stutter_eq_distinct: "sorted l \<Longrightarrow> no_stutter l \<longleftrightarrow> distinct l"
  apply (induction l rule: no_stutter.induct)
  apply (auto simp: )
  done

definition distinct_ds :: "'a::linorder list \<Rightarrow> bool"
  where "distinct_ds l \<equiv> no_stutter (quicksort l)"

lemma [code_unfold]: "distinct = distinct_ds"
  apply (intro ext)
  unfolding distinct_ds_def
  apply (auto simp: sorted_no_stutter_eq_distinct)
  done

subsubsection \<open>Code Generation\<close>

(* TODO/FIXME: Code_Char was removed from Isabelle-2018! 
  Check for performance regression of generated code!
*)
export_code
  check_plan
  nat_of_integer integer_of_nat Inl Inr
  predAtm Eq predicate Pred Either Var Obj PredDecl BigAnd BigOr
  formula.Not formula.Bot Effect ast_action_schema.Action_Schema
  map_atom Domain Problem PAction
  term.CONST term.VAR (* I want to export the entire type, but I can only export the constructor because term is already an isabelle keyword. *)
  String.explode String.implode
  in SML
  module_name PDDL_Checker_Exported
  file "PDDL_STRIPS_Checker_Exported.sml"

export_code ast_domain.apply_effect_exec in SML module_name ast_domain

(* Usage example from within Isabelle *)
(*
ML_val \<open>
  let
    val prefix="/home/lammich/devel/isabelle/planning/papers/pddl_validator/experiments/results/"

    fun check name =
      (name,@{code parse_check_dpp_impl}
        (file_to_string (prefix ^ name ^ ".dom.pddl"))
        (file_to_string (prefix ^ name ^ ".prob.pddl"))
        (file_to_string (prefix ^ name ^ ".plan")))

  in
    (*check "IPC5_rovers_p03"*)
    check "Test2_rover_untyped_pfile07"
  end
\<close>
*)
end \<comment> \<open>Theory\<close>
