theory Nonground_Abstract_Context
  imports 
    Abstract_Context
    Nonground_Context
    Multiset_Extra
begin

(* TODO: Put assumptions into own locale *) 
(* TODO: Interpret nonground_term with term_interpretation *) 
(* TODO: Create version with and without grounding *)
(* TODO: Could we make the liftings more general that they also works here? *)
locale nonground_abstract_context = 
  "term": nonground_term where apply_subst = apply_subst and term_to_ground = term_to_ground +

  extra: grounding where 
  is_ground = extra_is_ground and apply_subst = extra_apply_subst and subst = extra_subst and
  from_ground = extra_from_ground and to_ground = extra_to_ground and vars = extra_vars +


  ground: abstract_context where
  is_var = "\<lambda>_. False" and Fun = GFun and fun_sym = fun_sym\<^sub>G and extra = extra\<^sub>G and
  subterms = subterms\<^sub>G and size = size\<^sub>G +

  abstract_context where is_var = term.is_Var and Fun = Fun 
for 
  apply_subst :: "'v \<Rightarrow> 'subst \<Rightarrow> 't" and 
  Fun :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 't" and
  term_to_ground :: "'t \<Rightarrow> 't\<^sub>G" and

  extra_is_ground :: "'e \<Rightarrow> bool" and
  extra_to_ground :: "'e \<Rightarrow> 'e\<^sub>G" and
  extra_vars :: "'e \<Rightarrow> 'v\<^sub>e set" and
  extra_apply_subst extra_subst extra_from_ground and

  GFun :: "'f \<Rightarrow> 'e\<^sub>G \<Rightarrow> 't\<^sub>G list \<Rightarrow> 't\<^sub>G" and
  fun_sym\<^sub>G extra\<^sub>G subterms\<^sub>G size\<^sub>G +
assumes
  term_from_ground [simp]:
    "\<And>f e ts. 
      term.from_ground (GFun f e ts) = Fun f (extra_from_ground e) (map term.from_ground ts)" and
  term_to_ground [simp]:
    "\<And>f e ts. term.to_ground (Fun f e ts) = GFun f (extra_to_ground e) (map term.to_ground ts)" and
  term_is_ground [simp]:
    "\<And>f e ts.
      term.is_ground (Fun f e ts) \<longleftrightarrow> extra_is_ground e \<and> (\<forall>t \<in> set ts. term.is_ground t)" and
  term_vars [simp]: "\<And>f e ts. term.vars (Fun f e ts) = \<Union>(term.vars ` set ts)" and
  term_subst [simp]: "\<And>f e ts \<sigma>. Fun f e ts \<cdot>t \<sigma> = Fun f (extra_subst e \<sigma>) (map (\<lambda>t. t \<cdot>t \<sigma>) ts)"
begin

(* TODO: Extract *)
lemma var_all_subterms_eq:
  assumes "x \<in> term.vars t"
  shows "term.Var x \<in> all_subterms_eq t"
  using assms
proof (induction rule: all_subterms_eq.induct)
  case (1 t)

  then show ?case
  proof (cases "term.is_Var t")
    case True
    then show ?thesis
      using "1.prems" term.vars_id_subst 
      by auto
  next
    case False

    then obtain t' where "t' \<in> set (subterms t)"  "x \<in> term.vars t'"
      by (metis "1.prems" UN_iff interpret_term term_vars)

    then show ?thesis
      using 1(1)
      by (metis UN_I Un_iff all_subterms_eq.simps)
  qed
qed
  
lemma var_is_subterm:
  assumes "x \<in> term.vars t"
  shows "term.Var x \<unlhd> t"
  using var_all_subterms_eq[OF assms] all_subterms_eq_is_subterm_eq
  by auto

definition is_ground where
  "is_ground c \<equiv> (\<forall>t \<in> term_set c. term.is_ground t) \<and> (\<forall>e \<in> extra_set c. extra_is_ground e)"

definition subst (infixl "\<cdot>t\<^sub>c" 67) where
  "subst c \<sigma> \<equiv> map_context id (\<lambda>e. extra_subst e \<sigma>) (\<lambda>t. t \<cdot>t \<sigma>) c"

definition vars where
  "vars c \<equiv> \<Union>(term.vars ` term_set c)"

definition from_ground where
  "from_ground \<equiv> map_context id extra_from_ground term.from_ground"

definition to_ground where
  "to_ground \<equiv> map_context id extra_to_ground term.to_ground"

sublocale nonground_context where
  is_ground = is_ground and subst = subst and vars = vars and from_ground = from_ground and
  to_ground = to_ground and apply_context = apply_context and hole = \<box> and
  compose_context = "(\<circ>\<^sub>c)" and ground_hole = \<box> and compose_ground_context = "(\<circ>\<^sub>c)" and
  apply_ground_context = ground.apply_context
proof unfold_locales
  fix c :: "('f, 'e, 't) context" and t
  assume "c\<langle>t\<rangle> = t"

  then show "c = \<box>"
    using size_apply_context
    by (metis nat_neq_iff)
next
  fix c :: "('f, 'e, 't) context" and \<sigma> \<sigma>'

  show "c \<cdot>t\<^sub>c \<sigma> \<odot> \<sigma>' = c \<cdot>t\<^sub>c \<sigma> \<cdot>t\<^sub>c \<sigma>'"
    unfolding subst_def
    by (induction c) auto

  show "c \<cdot>t\<^sub>c id_subst = c"
    unfolding subst_def
    by (induction c) auto

  show "vars (c \<cdot>t\<^sub>c \<sigma>) = \<Union> (term.vars ` (\<lambda>x. apply_subst x \<sigma>) ` vars c)"
    unfolding vars_def subst_def
    using term.base_vars_subst
    by (induction c) auto
next
  fix c :: "('f, 'e, 't) context"
  assume is_ground: "is_ground c"

  then show "\<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c"
    unfolding is_ground_def subst_def
    by (induction c) (auto simp: map_idI)

  show "vars c = {}"
    using is_ground term.no_vars_if_is_ground
    unfolding is_ground_def vars_def
    by simp
next

  show "(\<exists>expr. \<not> is_ground expr) \<longleftrightarrow> term.exists_nonground"
    unfolding is_ground_def
    using term_is_ground
    by (metis list.set_intros(1) context.set_intros(5))
next
  fix c :: "('f, 'e, 't) context" and \<gamma>
  assume "is_ground (c \<cdot>t\<^sub>c \<gamma>)"

  then show "\<forall>x\<in>vars c. term.is_ground (apply_subst x \<gamma>)"
  proof (unfold is_ground_def subst_def vars_def, induction c)
    case Hole

    then show ?case
      by simp
  next
    case (More f e ls c rs)

    then show ?case
      by (metis (no_types, lifting) UN_iff context.set_map(3) rev_image_eqI term.variable_grounding)
  qed
next
  {
    fix c :: "('f, 'e, 't) context"
    assume c_is_ground: "is_ground c"

    have "\<exists>c\<^sub>G. from_ground c\<^sub>G = c"
    proof(intro exI)

      from c_is_ground
      show "from_ground (to_ground c) = c"
        unfolding is_ground_def from_ground_def to_ground_def
        by (induction c) (auto simp: map_idI)
    qed
  }

  moreover have "is_ground (from_ground c\<^sub>G)" for c\<^sub>G :: "('f, 'e\<^sub>G, 't\<^sub>G) context"
    unfolding is_ground_def from_ground_def
    by (induction c\<^sub>G) auto  

  ultimately show "{c :: ('f, 'e, 't) context. is_ground c} = range from_ground"
    by blast
next
  fix c\<^sub>G :: "('f, 'e\<^sub>G, 't\<^sub>G) context"

  show "to_ground (from_ground c\<^sub>G) = c\<^sub>G"
    unfolding to_ground_def from_ground_def
    by (induction c\<^sub>G) auto
next
  fix c t

  show "term.to_ground c\<langle>t\<rangle> = ground.apply_context (to_ground c) (term.to_ground t)"
    unfolding to_ground_def
    by (induction c) auto
next
  fix c\<^sub>G t\<^sub>G

  show "term.from_ground (ground.apply_context c\<^sub>G t\<^sub>G) = (from_ground c\<^sub>G)\<langle>term.from_ground t\<^sub>G\<rangle>"
    unfolding from_ground_def
    by (induction c\<^sub>G) auto
next
  fix c t

  show "term.is_ground c\<langle>t\<rangle> \<longleftrightarrow> is_ground c \<and> term.is_ground t"
    unfolding is_ground_def
    by (induction c) auto
next
  fix c\<^sub>G c'\<^sub>G :: "('f, 'e\<^sub>G, 't\<^sub>G) context"

  show "from_ground (c\<^sub>G \<circ>\<^sub>c c'\<^sub>G) = from_ground c\<^sub>G \<circ>\<^sub>c from_ground c'\<^sub>G"
    unfolding from_ground_def
    by (induction c\<^sub>G) auto
next
  fix c t

  show "term.vars c\<langle>t\<rangle> = vars c \<union> term.vars t"
    using term_vars
    unfolding vars_def
    by (induction c) auto
next
  fix c t \<sigma>

  show "c\<langle>t\<rangle> \<cdot>t \<sigma> = (c \<cdot>t\<^sub>c \<sigma>)\<langle>t \<cdot>t \<sigma>\<rangle>"
    unfolding subst_def
    by (induction c) auto
next
  fix x t
  assume "x \<in> term.vars t"

  then show "\<exists>c. t = c\<langle>term.Var x\<rangle>"
    unfolding is_subterm_iff_exists_context[symmetric]
    by (simp add: var_is_subterm)
next
  fix c :: "('f, 'e, 't) context" and \<mu> XX
  assume imgu: "term.is_imgu \<mu> XX" "finite XX" "\<forall>X\<in>XX. finite X"

  show "vars (c \<cdot>t\<^sub>c \<mu>) \<subseteq> vars c \<union> \<Union> (term.vars ` \<Union> XX)"
    using term.variables_in_base_imgu[OF imgu]
    unfolding vars_def subst_def
    by (smt (verit, ccfv_threshold) UN_iff Un_iff context.set_map(3) image_iff subset_eq)
next
  fix t \<gamma> c\<^sub>G t\<^sub>G
  assume t_\<gamma>: "t \<cdot>t \<gamma> = c\<^sub>G\<langle>t\<^sub>G\<rangle>" and t_grounding: "term.is_ground (t \<cdot>t \<gamma>)"

  {
    assume "\<nexists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G"

    with t_\<gamma> t_grounding have "\<exists>c c' x. t = c\<langle>term.Var x\<rangle> \<and> (c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c c' = c\<^sub>G"
    proof (induction c\<^sub>G arbitrary: t)
      case Hole
      then show ?case
        by (simp add: subst_def)
    next
      case (More f e ls c\<^sub>G rs)

      have t_\<gamma>: "t \<cdot>t \<gamma> = Fun f e (ls @ c\<^sub>G\<langle>t\<^sub>G\<rangle> # rs)"
        using More(2, 3)
        by simp

      show ?case
      proof (cases "term.is_Var t")
        case True

        then show ?thesis
          by (metis apply_hole compose_context.simps(1) context.map_disc_iff subst_def)
      next
        case False

        then obtain e' ts' where t: "t = Fun f e' ts'"
          by (metis More.prems(1) apply_context.simps(2) term_destruct term_fun_sym term_subst)

        have "map (\<lambda>t. t \<cdot>t \<gamma>) ts' = ls @ c\<^sub>G\<langle>t\<^sub>G\<rangle> # rs"
          using t_\<gamma>
          unfolding t term_subst
          by (metis subterms)

        then obtain rs' t' ls' where 
          ts': "ts' = ls' @ t' # rs'" and
          ls: "ls = map (\<lambda>t. t \<cdot>t \<gamma>) ls'" and
          t'_\<gamma>: "t' \<cdot>t \<gamma> = c\<^sub>G\<langle>t\<^sub>G\<rangle>" and
          rs: "rs = map (\<lambda>t. t \<cdot>t \<gamma>) rs'"
          by (smt (verit, ccfv_threshold) map_eq_Cons_conv map_eq_append_conv)

        have "\<exists>c c' x. t' = c\<langle>term.Var x\<rangle> \<and> (c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c c' = c\<^sub>G"
        proof (rule More.IH[OF t'_\<gamma>])

          show "term.is_ground (t' \<cdot>t \<gamma>)"
            using More.prems(2) t'_\<gamma> t_\<gamma> term_is_ground 
            by fastforce
        next

          show "\<nexists>c t''. t' = c\<langle>t''\<rangle> \<and> t'' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G"
          proof (rule notI)
            assume "\<exists>c t''. t' = c\<langle>t''\<rangle> \<and> t'' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G"

            then obtain c t'' where t': "t' = c\<langle>t''\<rangle>" and t''_\<gamma>: "t'' \<cdot>t \<gamma> = t\<^sub>G" and c: "c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G"
              by blast

            have "(More f e' ls' c rs') \<cdot>t\<^sub>c \<gamma> = More f e ls c\<^sub>G rs"
              using c t t_\<gamma> term_inject ls rs
              unfolding subst_def
              by auto

            then show False
              using More(4) t' t''_\<gamma> t ts'
              by auto
          qed
        qed

        then obtain c c' x where t': "t' = c\<langle>term.Var x\<rangle>" and c_c': "(c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c c' = c\<^sub>G"
          by blast

        show ?thesis
        proof (intro exI conjI)

          show "t = (More f e' ls' c rs')\<langle>term.Var x\<rangle>"
            by (simp add: t' t ts')
        next

          show "(More f e' ls' c rs' \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c c' = More f e ls c\<^sub>G rs"
            using t t_\<gamma> term_inject ls rs c_c'
            unfolding subst_def
            by auto
        qed
      qed
    qed
  }

  then show
    "(\<exists>c t'. t = c\<langle>t'\<rangle> \<and> t' \<cdot>t \<gamma> = t\<^sub>G \<and> c \<cdot>t\<^sub>c \<gamma> = c\<^sub>G) \<or>
     (\<exists>c c\<^sub>G' x. t = c\<langle>term.Var x\<rangle> \<and> c\<^sub>G = (c \<cdot>t\<^sub>c \<gamma>) \<circ>\<^sub>c c\<^sub>G')"
    by blast
qed

(* TODO: Extract *)
function vars_ms :: "'t \<Rightarrow> 'v multiset" where
  "vars_ms t =
    (if term.is_Var t then {# term.the_Var t #}
     else \<Sum>\<^sub># (mset (map vars_ms (subterms t))))"
  by auto

termination
proof (relation "measure size")
  fix t t'
  assume "t' \<in> set (subterms t)"

  then show "(t', t) \<in> measure size"
    using subterms_smaller
    by simp  
qed auto

declare vars_ms.simps [simp del]

lemma vars_ms_Var [simp]: 
  assumes "term.exists_nonground"
  shows "vars_ms (term.Var x) = {#x#}"
  using assms
  by
    (subst vars_ms.simps)
    (metis rename_def term.id_subst_rename term.inv_renaming term.neutral_is_right_invertible)

lemma vars_ms_Fun [simp]: 
  "vars_ms (Fun f e ts) = \<Sum>\<^sub># (mset (map vars_ms ts))"
  by (subst vars_ms.simps) (use term_destruct in auto)

lemma is_ground_vars_ms [simp]: 
  assumes "term.is_ground t"
  shows "vars_ms t = {#}"
  using assms
proof (induction rule: term_induct)
  case (1 t)

  then obtain f e ts where t: "t = Fun f e ts"
    by (metis ground.term_destruct term.to_ground_inverse term_from_ground)

  have "sum_list (map vars_ms ts) = {#}"
    using 1
    unfolding t
    by (smt (verit) map_eq_conv subterms sum_list_0 term_is_ground)

  then show ?case
    using 1
    unfolding t
    by auto
qed
  

lemma vars_ms_vars [simp]: "set_mset (vars_ms t) = term.vars t"
proof (induction rule: all_subterms_eq.induct)
  case (1 t)

  then show ?case
  proof (cases "term.exists_nonground")
    case True

    have [simp]: "vars_ms (term.Var x) = {#x#}" for x
      using True
      by simp

    have [simp]: "term.vars (term.Var x) = {x}" for x
      using True
      by (simp add: term.vars_id_subst)

    show ?thesis
    proof (cases "term.is_Var t")
      case is_Var: True

      then show ?thesis
        by auto
    next
      case is_Fun: False

      then obtain f e ts where t: "t = Fun f e ts"
        by (metis term_destruct)

      show ?thesis 
        using 1
        unfolding t
        by auto
    qed
  next
    case False

    then have "term.vars t = {}"
      by (metis term.no_vars_if_is_ground)

    then show ?thesis
      by (metis False set_mset_empty is_ground_vars_ms)
  qed
qed

abbreviation occurences where
  "occurences t x \<equiv> count (vars_ms t) x"

sublocale occurences where
  is_ground = is_ground and subst = subst and vars = vars and from_ground = from_ground and
  to_ground = to_ground and apply_context = apply_context and hole = \<box> and
  compose_context = "(\<circ>\<^sub>c)" and ground_hole = \<box> and compose_ground_context = "(\<circ>\<^sub>c)" and
  apply_ground_context = ground.apply_context and occurences = occurences
proof unfold_locales
  fix x c t
  assume "term.exists_nonground" "term.is_ground t"

  then show "occurences c\<langle>term.Var x\<rangle> x = Suc (local.occurences c\<langle>t\<rangle> x)"
    by (induction c) auto
next
  fix x t 

  show "x \<in> term.vars t \<longleftrightarrow> 0 < occurences t x"
    by auto
qed

end

end
