(*
  Formalization by Cárolos Laméris 
  
  Note that
    bojanczyk2014automata ~
    Bojańczyk, M., Klin, B., & Lasota, S. (2014).
    Automata theory in nominal sets.
    Logical Methods in Computer Science, 10.

    ( https://lmcs.episciences.org/1157 )
*)

section \<open>
Myhill-Nerode Theorem for $G$-automata
\<close>
text \<open>
We prove the Myhill-Nerode Theorem for $G$-automata / nominal $G$-automata
following the proofs from \cite{bojanczyk2014automata} (The standard Myhill-Nerode theorem is also
proved, as a special case of the $G$-Myhill-Nerode theorem).
Concretely, we formalize the following results from \cite{bojanczyk2014automata}:
lemmas: 3.4, 3.5, 3.6, 3.7, 4.8, 4.9;
proposition: 5.1;
theorems: 3.8 (Myhill-Nerode for $G$-automata), 5.2 (Myhill-Nerode for nominal $G$-automata).

Throughout this document, we maintain the following convention for isar proofs:
If we \texttt{obtain} some term \texttt{t} for which some result holds, we name it \texttt{H\_t}.
An assumption which is an induction hypothesis is named \texttt{A\_IH}
Assumptions start with an "\texttt{A}" and intermediate results start with a "\texttt{H}".
Typically we just name them via indexes, i.e. as \texttt{A\_i} and \texttt{H\_j}.
When encountering nested isar proofs we add an index for how nested the assumption / intermediate
result is.
For example if we have an isar proof in an isar proof in an isar proof, we would name assumptions
of the most nested proof \texttt{A3\_i}.
\<close>

theory Nominal_Myhill_Nerode
  imports
    Main 
    HOL.Groups
    HOL.Relation
    HOL.Fun
    "HOL-Algebra.Group_Action"
    "HOL-Library.Adhoc_Overloading"
    "HOL-Algebra.Elementary_Groups"

begin

text \<open>
\texttt{GMN\_simps} will contain selection of lemmas / definitions is updated through out
the document.
\<close>

named_theorems GMN_simps
lemmas GMN_simps

text \<open>
We will use the $\star$-symbol for the set of words of elements of a set, $A^{\star}$, the induced
group action on the set of words $\phi^{\star}$ and for the extended transition function
$\delta^{\star}$, thus we introduce the map \texttt{star} and apply \texttt{adhoc\_overloading} to
get the notation working in all three situations:
\<close>

consts star :: "'typ1 \<Rightarrow> 'typ2" ("_\<^sup>\<star>" [1000] 999)

abbreviation
  kleene_star_set :: "'alpha set \<Rightarrow> 'alpha list set"
  where "kleene_star_set A \<equiv> lists A"

adhoc_overloading
  star kleene_star_set

text \<open>
We use $\odot$ to convert between the definition of group actions via group homomoprhisms
and the infix group action notation from \cite{bojanczyk2014automata}:
\<close>

definition
  make_op :: "('grp \<Rightarrow> 'X \<Rightarrow> 'X) \<Rightarrow> 'X \<Rightarrow> 'grp \<Rightarrow> 'X" (infixl "(\<odot>\<index>)" 70)
  where " (\<odot> \<^bsub>\<phi>\<^esub>) \<equiv> (\<lambda>x. (\<lambda>g. \<phi> g x))"

lemmas make_op_def [simp, GMN_simps]

subsection \<open>
Extending Group Actions
\<close>

text \<open>
The following lemma is used for a proof in the locale \texttt{alt\_grp\_act}:
\<close>

lemma pre_image_lemma:
  "\<lbrakk>S \<subseteq> T; x \<in> T \<and> f \<in> Bij T; (restrict f S) ` S = S; f x \<in> S\<rbrakk> \<Longrightarrow> x \<in> S"
  apply (clarsimp simp add: extensional_def subset_eq Bij_def bij_betw_def restrict_def inj_on_def)
  by (metis imageE)

text \<open>
The locale \texttt{alt\_grp\_act} is just a renaming of the locale \texttt{group\_action}.
This was done to obtain more easy to interpret type names and context variables closer
to the notation of \cite{bojanczyk2014automata}:
\<close>

locale alt_grp_act = group_action G X \<phi>
  for
    G :: "('grp, 'b) monoid_scheme" and
    X :: "'X set" (structure) and
    \<phi>
begin

definition
  induced_star_map :: "('grp \<Rightarrow> 'X \<Rightarrow>'X) \<Rightarrow> 'grp \<Rightarrow> 'X list \<Rightarrow> 'X list"
  where "induced_star_map func = (\<lambda>g\<in>carrier G. (\<lambda>lst \<in> (lists X). map (func g) lst))"

text \<open>
Because the adhoc overloading is used within a locale, isues will be encountered later due to there
being multiple instances of the locale \texttt{alt\_grp\_act} in a single context:
\<close>

adhoc_overloading
  star induced_star_map

definition 
  induced_quot_map ::
  "'Y set \<Rightarrow> ('grp \<Rightarrow> 'Y \<Rightarrow> 'Y) \<Rightarrow> ('Y \<times>'Y) set \<Rightarrow> 'grp \<Rightarrow> 'Y set \<Rightarrow> 'Y set" ("[_]\<^sub>_\<index>" 60)
  where "([ func ]\<^sub>R \<^bsub>S\<^esub>) = (\<lambda>g\<in>carrier G. (\<lambda>x \<in> (S // R). R `` {(func g) (SOME z. z\<in>x)}))"

lemmas induced_star_map_def [simp, GMN_simps]
  induced_quot_map_def [simp, GMN_simps]

lemma act_maps_n_distrib:
  "\<forall>g\<in>carrier G. \<forall>w\<in>X\<^sup>\<star>. \<forall>v\<in>X\<^sup>\<star>. (\<phi>\<^sup>\<star>) g (w @ v) = ((\<phi>\<^sup>\<star>) g w) @ ((\<phi>\<^sup>\<star>) g v)"
  by (auto simp add: group_action_def group_hom_def group_hom_axioms_def hom_def)

lemma triv_act:
  "a \<in> X \<Longrightarrow> (\<phi> \<one>\<^bsub>G\<^esub>) a = a"
  using group_hom.hom_one[of "G" "BijGroup X" "\<phi>"] group_BijGroup[where S = "X"]
  apply (clarsimp simp add: group_action_def group_hom_def group_hom_axioms_def BijGroup_def)
  by (metis id_eq_one restrict_apply')

lemma triv_act_map:
  "\<forall>w\<in>X\<^sup>\<star>. ((\<phi>\<^sup>\<star>) \<one>\<^bsub>G\<^esub>) w = w"
  using triv_act
  apply clarsimp
  apply (rule conjI; rule impI)
   apply clarify
  using map_idI
   apply metis
  using group.subgroup_self group_hom group_hom.axioms(1) subgroup.one_closed
  by blast

proposition lists_a_Gset:
  "alt_grp_act G (X\<^sup>\<star>) (\<phi>\<^sup>\<star>)"
proof-
  have H_0: "\<And>g. g \<in> carrier G \<Longrightarrow>
    restrict (map (\<phi> g)) (kleene_star_set X) \<in> carrier (BijGroup (kleene_star_set X))"
  proof-
    fix g
    assume
      A1_0: "g \<in> carrier G"
    from A1_0 have H1_0: "inj_on (\<lambda>x. if x \<in> lists X then map (\<phi> g) x else undefined) (lists X)"
      apply (clarsimp simp add: inj_on_def)
      by (metis (mono_tags, lifting) inj_onD inj_prop list.inj_map_strong)
    from A1_0 have H1_1: "\<And>y z. \<forall>x\<in>set y. x \<in> X \<Longrightarrow> z \<in> set y \<Longrightarrow> \<phi> g z \<in> X"
      using element_image
      by blast
    have H1_2: "(inv \<^bsub>G\<^esub> g) \<in> carrier G"
      by (meson A1_0 group.inv_closed group_hom group_hom.axioms(1))
    have H1_3: "\<And>x. x \<in> lists X \<Longrightarrow>
    map (comp (\<phi> g) (\<phi> (inv \<^bsub>G\<^esub> g))) x = map (\<phi> (g \<otimes>\<^bsub>G\<^esub> (inv \<^bsub>G\<^esub> g))) x"
      using alt_grp_act_axioms
      apply (simp add: alt_grp_act_def group_action_def group_hom_def group_hom_axioms_def hom_def
          BijGroup_def)
      apply (rule meta_mp[of "\<And>x. x \<in> carrier G \<Longrightarrow> \<phi> x \<in> Bij X"])
       apply (metis A1_0 H1_2 composition_rule in_lists_conv_set)
      by blast
    from H1_2 have H1_4: "\<And>x. x \<in> lists X \<Longrightarrow> map (\<phi> (inv \<^bsub>G\<^esub> g)) x \<in> lists X"
      using surj_prop
      by fastforce
    have H1_5: "\<And>y. \<forall>x\<in>set y. x \<in> X \<Longrightarrow> y \<in> map (\<phi> g) ` lists X"
      apply (simp add: image_def)
      using H1_3 H1_4 
      by (metis A1_0 group.r_inv group_hom group_hom.axioms(1) in_lists_conv_set map_idI map_map
          triv_act)
    show "restrict (map (\<phi> g)) (lists X) \<in> carrier (BijGroup (lists X))"
      apply (clarsimp simp add: restrict_def BijGroup_def Bij_def
          extensional_def bij_betw_def) 
      apply (rule conjI)
      using H1_0
       apply simp
      using H1_1 H1_5
      by (auto simp add: image_def) 
  qed
  have H_1: "\<And>x y. \<lbrakk>x \<in> carrier G; y \<in> carrier G; x \<otimes>\<^bsub>G\<^esub> y \<in> carrier G\<rbrakk> \<Longrightarrow>
           restrict (map (\<phi> (x \<otimes>\<^bsub>G\<^esub> y))) (kleene_star_set X) =
           restrict (map (\<phi> x)) (kleene_star_set X) \<otimes>\<^bsub>BijGroup (kleene_star_set X)\<^esub>
           restrict (map (\<phi> y)) (kleene_star_set X)"
  proof-
    fix x y
    assume
      A1_0: "x \<in> carrier G" and
      A1_1: " y \<in> carrier G" and
      A1_2: "x \<otimes>\<^bsub>G\<^esub> y \<in> carrier G"
    have H1_0: "\<And>z. z \<in> carrier G \<Longrightarrow>
       bij_betw (\<lambda>x. if x \<in> lists X then map (\<phi> z) x else undefined) (lists X) (lists X)"
      using \<open>\<And>g. g \<in> carrier G \<Longrightarrow> restrict (map (\<phi> g)) (lists X) \<in> carrier (BijGroup (lists X))\<close>
      by (auto simp add: BijGroup_def Bij_def bij_betw_def inj_on_def)
    from A1_1 have H1_1: "\<And>lst. lst \<in> lists X \<Longrightarrow> (map (\<phi> y)) lst \<in> lists X"
      by (metis group_action.surj_prop group_action_axioms lists_image rev_image_eqI)
    have H1_2: "\<And>a. a \<in> lists X \<Longrightarrow> map (\<lambda>xb.
    if xb \<in> X
    then \<phi> x ((\<phi> y) xb)
    else undefined) a = map (\<phi> x) (map (\<phi> y) a)"
      by auto
    have H1_3: "(\<lambda>xa. if xa \<in> lists X then map (\<phi> (x \<otimes>\<^bsub>G\<^esub> y)) xa else undefined) =
    compose (lists X) (\<lambda>xa. if xa \<in> lists X then map (\<phi> x) xa else undefined)
    (\<lambda>x. if x \<in> lists X then map (\<phi> y) x else undefined)"
      using alt_grp_act_axioms
      apply (clarsimp simp add: compose_def alt_grp_act_def group_action_def
          group_hom_def group_hom_axioms_def hom_def BijGroup_def restrict_def)
      using A1_0 A1_1 H1_2 H1_1 bij_prop0
      by auto
    show "restrict (map (\<phi> (x \<otimes>\<^bsub>G\<^esub> y))) (lists X) =
  restrict (map (\<phi> x)) (lists X) \<otimes>\<^bsub>BijGroup (lists X)\<^esub>
  restrict (map (\<phi> y)) (lists X)"
      apply (clarsimp simp add: restrict_def BijGroup_def Bij_def extensional_def)
      apply (simp add: H1_3)
      using A1_0 A1_1 H1_0
      by auto
  qed
  show "alt_grp_act G (X\<^sup>\<star>) (\<phi>\<^sup>\<star>)"
    apply (clarsimp simp add: alt_grp_act_def group_action_def group_hom_def group_hom_axioms_def)
    apply (intro conjI)
    using group_hom group_hom_def
      apply (auto)[1]
     apply (simp add: group_BijGroup)
    apply (clarsimp simp add: hom_def)
    apply (intro conjI; clarify)
     apply (rule H_0)
     apply simp
    apply (rule conjI; rule impI)
     apply (rule H_1)
       apply simp+
    apply (rule meta_mp[of "\<And>x y. x \<in> carrier G \<Longrightarrow>
    y \<in> carrier G \<Longrightarrow> x \<otimes>\<^bsub>G\<^esub> y \<in> carrier G"])
     apply blast
    by (meson group.subgroup_self group_hom group_hom.axioms(1) subgroup.m_closed)
qed
end

lemma alt_group_act_is_grp_act [simp, GMN_simps]:
  "alt_grp_act = group_action"
  using alt_grp_act_def
  by blast

lemma prod_group_act:
  assumes
    grp_act_A: "alt_grp_act G A \<phi>" and
    grp_act_B: "alt_grp_act G B \<psi>"
  shows "alt_grp_act G (A\<times>B) (\<lambda>g\<in>carrier G. \<lambda>(a, b) \<in> (A \<times> B). (\<phi> g a, \<psi> g b))"
  apply (simp add: alt_grp_act_def group_action_def group_hom_def)
  apply (intro conjI)
  subgoal
    using grp_act_A grp_act_B
    by (auto simp add: alt_grp_act_def group_action_def group_hom_def)
  subgoal
    using grp_act_A grp_act_B
    by (auto simp add: alt_grp_act_def group_action_def group_hom_def group_BijGroup)
  apply (clarsimp simp add: group_hom_axioms_def hom_def BijGroup_def)
  apply (intro conjI; clarify)
  subgoal for g
    apply (clarsimp simp add: Bij_def bij_betw_def inj_on_def restrict_def extensional_def)
    apply (intro conjI)
    using grp_act_A
     apply (simp add: alt_grp_act_def group_action_def group_hom_def group_hom_axioms_def
        BijGroup_def hom_def Pi_def compose_def Bij_def bij_betw_def inj_on_def)
    using grp_act_B
     apply (simp add: alt_grp_act_def group_action_def group_hom_def group_hom_axioms_def
        BijGroup_def hom_def Pi_def compose_def Bij_def bij_betw_def inj_on_def)
    apply (rule meta_mp[of "\<phi> g \<in> Bij A \<and> \<psi> g \<in> Bij B"])
     apply (clarsimp simp add: Bij_def bij_betw_def)
    using grp_act_A grp_act_B
     apply (simp add: alt_grp_act_def group_action_def group_hom_def group_hom_axioms_def
        BijGroup_def hom_def Pi_def Bij_def)
    using grp_act_A grp_act_B
     apply (clarsimp simp add: compose_def restrict_def image_def alt_grp_act_def
        group_action_def group_hom_def group_hom_axioms_def BijGroup_def hom_def Pi_def Bij_def
        bij_betw_def)
     apply (rule subset_antisym)
      apply blast+
    by (metis alt_group_act_is_grp_act group_action.bij_prop0 grp_act_A grp_act_B)
  apply (intro conjI; intro impI)
   apply (clarify)
   apply (intro conjI; intro impI)
    apply (rule conjI)
  subgoal for x y
    apply unfold_locales
    apply (clarsimp simp add: Bij_def compose_def restrict_def bij_betw_def)
    apply (rule extensionalityI[where A = "A \<times> B"])
      apply (clarsimp simp add: extensional_def)
    using grp_act_A grp_act_B
     apply (simp add: alt_grp_act_def group_action_def group_hom_def group_hom_axioms_def
        BijGroup_def hom_def Pi_def Bij_def compose_def extensional_def)
    apply (simp add: fun_eq_iff; rule conjI; rule impI)
    using group_action.composition_rule[of G A \<phi>] group_action.composition_rule[of G B \<psi>] grp_act_A 
      grp_act_B   
     apply force
    by blast
    apply (simp add: \<open>\<And>g. g \<in> carrier G \<Longrightarrow> (\<lambda>(a, b)\<in>A \<times> B. (\<phi> g a, \<psi> g b)) \<in> Bij (A \<times> B)\<close>)
   apply (simp add: \<open>Group.group G\<close> group.subgroup_self subgroup.m_closed)
  by (simp add: \<open>\<And>g. g \<in> carrier G \<Longrightarrow> (\<lambda>(a, b)\<in>A \<times> B. (\<phi> g a, \<psi> g b)) \<in> Bij (A \<times> B)\<close>)+

subsection \<open>
Equivariance and Quotient Actions
\<close>

locale eq_var_subset = alt_grp_act G X \<phi>
  for
    G :: "('grp, 'b) monoid_scheme" and
    X :: "'X set" (structure) and
    \<phi> +
  fixes
    subset
  assumes
    is_subset: "subset \<subseteq> X" and
    is_equivar: "\<forall>g\<in>carrier G. (\<phi> g) ` subset = subset" 

text \<open>
The following lemmas are used for proofs in the locale \texttt{eq\_var\_rel}:
\<close>

lemma some_equiv_class_id:
  "\<lbrakk>equiv X R; w \<in> X // R; x \<in> w\<rbrakk> \<Longrightarrow> R `` {x} = R `` {SOME z. z \<in> w}"
  by (smt (z3) Eps_cong equiv_Eps_in equiv_class_eq_iff quotient_eq_iff)

lemma nested_somes:
  "\<lbrakk>equiv X R; w \<in> X // R\<rbrakk> \<Longrightarrow> (SOME z. z \<in> w) = (SOME z. z \<in> R``{(SOME z'. z' \<in> w)})"
  by (metis proj_Eps proj_def)

locale eq_var_rel = alt_grp_act G X \<phi>
  for
    G :: "('grp, 'b) monoid_scheme" and
    X :: "'X set" (structure) and
    \<phi> +
  fixes R 
  assumes
    is_subrel:
    "R \<subseteq> X \<times> X" and
    is_eq_var_rel:
    "\<And>a b. (a, b) \<in> R \<Longrightarrow> \<forall>g \<in> carrier G. (a \<odot>\<^bsub>\<phi>\<^esub> g, b \<odot>\<^bsub>\<phi>\<^esub> g) \<in> R"
begin

lemma is_eq_var_rel' [simp, GMN_simps]:
  "\<And>a b. (a, b) \<in> R \<Longrightarrow> \<forall>g \<in> carrier G. ((\<phi> g) a, (\<phi> g) b) \<in> R"
  using is_eq_var_rel
  by auto

lemma is_eq_var_rel_rev:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> g \<in> carrier G \<Longrightarrow> (a \<odot>\<^bsub>\<phi>\<^esub> g, b \<odot>\<^bsub>\<phi>\<^esub> g) \<in> R \<Longrightarrow> (a, b) \<in> R"
proof -
  assume
    A_0: "(a \<odot>\<^bsub>\<phi>\<^esub> g, b \<odot>\<^bsub>\<phi>\<^esub> g) \<in> R" and
    A_1: "a \<in> X" and
    A_2: "b \<in> X" and
    A_3: "g \<in> carrier G" 
  have H_0: " group_action G X \<phi>" and
    H_1: "R \<subseteq> X \<times> X" and
    H_2: "\<And>a b g. (a, b) \<in> R \<Longrightarrow> g \<in> carrier G \<Longrightarrow> (\<phi> g a, \<phi> g b) \<in> R" 
    by (simp add: group_action_axioms is_subrel)+
  from H_0 have H_3: "group G"
    by (auto simp add: group_action_def group_hom_def)
  have H_4: "(\<phi> (inv\<^bsub>G\<^esub> g) (\<phi> g a), \<phi> (inv\<^bsub>G\<^esub> g) (\<phi> g b)) \<in> R"
    apply (rule H_2)
    using A_0 apply simp
    by (simp add: A_3 H_3)
  from H_3 A_3 have H_5: "(inv\<^bsub>G\<^esub> g) \<in> carrier G"
    by auto
  hence H_6: "\<And>e. e \<in> X \<Longrightarrow> \<phi> (inv\<^bsub>G\<^esub> g) (\<phi> g e) = \<phi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> g) e"
    using H_0 A_3 group_action.composition_rule 
    by fastforce
  hence H_7: "\<And>e. e \<in> X \<Longrightarrow> \<phi> (inv\<^bsub>G\<^esub> g) (\<phi> g e) = \<phi> \<one>\<^bsub>G\<^esub> e"
    using H_3 A_3 group.l_inv
    by fastforce 
  hence H_8: "\<And>e. e \<in> X \<Longrightarrow> \<phi> (inv\<^bsub>G\<^esub> g) (\<phi> g e) = e"
    using H_0
    by (simp add: A_3 group_action.orbit_sym_aux)
  thus "(a, b) \<in> R"
    using A_1 A_2 H_4
    by simp
qed

lemma equiv_equivar_class_some_eq:
  assumes
    A_0: "equiv X R" and
    A_1: "w \<in> X // R" and
    A_2: "g \<in> carrier G"
  shows "([ \<phi> ]\<^sub>R) g w = R `` {(SOME z'. z' \<in> \<phi> g ` w)}"
proof-
  obtain z where H_z: "w = R `` {z} \<and> z \<in> w"
    by (metis A_0 A_1 equiv_class_self quotientE)
  have H_0: "\<And>x. (\<phi> g z, x) \<in> R \<Longrightarrow> x \<in> \<phi> g ` {y. (z, y) \<in> R}"
  proof-
    fix y
    assume
      A1_0: "(\<phi> g z, y) \<in> R"
    obtain y' where H2_y': "y' = \<phi> (inv\<^bsub>G\<^esub> g) y \<and> y' \<in> X" 
      using eq_var_rel_axioms
      apply (clarsimp simp add: eq_var_rel_def group_action_def group_hom_def) 
      by (meson A_0 eq_var_rel_axioms A_2 A1_0 equiv_class_eq_iff eq_var_rel.is_eq_var_rel
          group.inv_closed element_image) 
    from A_1 A_2 H2_y' have H2_0: "\<phi> g y' = y"
      apply (clarsimp simp add: eq_var_rel_def eq_var_rel_axioms_def)
      using A_2 A1_0 group_action.bij_prop1[where G = "G" and E = "X" and \<phi> = "\<phi>"]
      by (metis A_0 alt_group_act_is_grp_act alt_grp_act_axioms equiv_class_eq_iff orbit_sym_aux)
    from A_1 A_2 A1_0 have H2_1: "(z, y') \<in> R"
      by (metis H2_0 A_0 A_2 H2_y' H_z equiv_class_eq_iff is_eq_var_rel_rev
          quotient_eq_iff make_op_def)
    thus "y \<in> \<phi> g ` {v. (z, v) \<in> R}" 
      using H2_0
      by (auto simp add: image_def)
  qed
  have H_1: "\<phi> g ` (R `` {z}) = R `` {\<phi> g z}"
    apply (clarsimp simp add: Relation.Image_def)
    apply (rule subset_antisym; simp add: Set.subset_eq; rule allI; rule impI)
    using eq_var_rel_axioms A_2 eq_var_rel.is_eq_var_rel
     apply simp
    by (simp add: H_0)
  have H_2: "\<phi> g ` w \<in> X // R"
    using eq_var_rel_axioms A_1 A_2 H_1 
    by (metis A_0 H_z equiv_class_eq_iff quotientI quotient_eq_iff element_image)
  thus "([\<phi>]\<^sub>R) g w = R `` {SOME z'. z' \<in> \<phi> g ` w}"
    using A_0 A_1 A_2
    apply (clarsimp simp add: Image_def)
    apply (intro subset_antisym)
     apply (clarify)
    using A_0 H_z imageI insert_absorb insert_not_empty some_in_eq some_equiv_class_id 
     apply (smt (z3) A_1 Eps_cong Image_singleton_iff equiv_Eps_in)
    apply (clarify)
    by (smt (z3) Eps_cong equiv_Eps_in image_iff in_quotient_imp_closed quotient_eq_iff)
qed

lemma ec_er_closed_under_action:
  assumes
    A_0: "equiv X R" and
    A_1: "g \<in> carrier G" and
    A_2: "w \<in> X//R"
  shows "\<phi> g ` w \<in> X // R"
proof-
  obtain z where H_z: "R `` {z} = w \<and> z \<in> X"
    by (metis A_2 quotientE)
  have H_0: "equiv X R \<Longrightarrow> g \<in> carrier G \<Longrightarrow> w \<in> X // R \<Longrightarrow>
      {y. (\<phi> g z, y) \<in> R} \<subseteq> {y. \<exists>x. (z, x) \<in> R \<and> y = \<phi> g x}"
  proof (clarify)
    fix x
    assume
      A1_0: "equiv X R" and
      A1_1: "g \<in> carrier G" and
      A1_2: "w \<in> X // R" and
      A1_3: "(\<phi> g z, x) \<in> R"
    obtain x' where H2_x': "x = \<phi> g x' \<and> x' \<in> X" 
      using group_action_axioms
      by (metis A1_1 is_subrel A1_3 SigmaD2 group_action.bij_prop1 subsetD)
    thus "\<exists>y. (z, y) \<in> R \<and> x = \<phi> g y"
      using is_eq_var_rel_rev[where g = "g" and a = "z" and b = "x'"] A1_3
      by (auto simp add: eq_var_rel_def eq_var_rel_axioms_def A1_1 A1_2 group_action_axioms H_z
          H2_x')
  qed
  have H_1: "\<phi> g ` R `` {z} = R `` {\<phi> g z}"
    using A_0 A_1 A_2
    apply (clarsimp simp add: eq_var_rel_axioms_def eq_var_rel_def
        Image_def image_def)
    apply (intro subset_antisym)
     apply (auto)[1]
    by (rule H_0)
  thus "\<phi> g ` w \<in> X // R"
    using H_1 H_z
    by (metis A_1 quotientI element_image)
qed

text \<open>
The following lemma corresponds to the first part of lemma 3.5 from \cite{bojanczyk2014automata}:
\<close>

lemma quot_act_wd:
  "\<lbrakk>equiv X R; x \<in> X; g \<in> carrier G\<rbrakk> \<Longrightarrow> (R `` {x}) \<odot>\<^bsub>[\<phi>]\<^sub>R\<^esub> g = (R `` {x \<odot>\<^bsub>\<phi>\<^esub> g})"
  apply (clarsimp simp add: eq_var_rel_def eq_var_rel_axioms_def)
  apply (rule conjI; rule impI)
   apply (smt (verit, best) Eps_cong Image_singleton_iff eq_var_rel.is_eq_var_rel'
      eq_var_rel_axioms equiv_Eps_in equiv_class_eq)
  by (simp add: quotientI)+

text \<open>
The following lemma corresponds to the second part of lemma 3.5 from \cite{bojanczyk2014automata}:
\<close>

lemma quot_act_is_grp_act:
  "equiv X R \<Longrightarrow> alt_grp_act G (X // R) ([\<phi>]\<^sub>R)"
proof-
  assume A_0: "equiv X R"
  have H_0: "\<And>x. Group.group G \<Longrightarrow>
         Group.group (BijGroup X) \<Longrightarrow>
         R \<subseteq> X \<times> X \<Longrightarrow>
         \<phi> \<in> carrier G \<rightarrow> carrier (BijGroup X) \<Longrightarrow>
         \<forall>x\<in>carrier G. \<forall>y\<in>carrier G. \<phi> (x \<otimes>\<^bsub>G\<^esub> y) = \<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y \<Longrightarrow>
         x \<in> carrier G \<Longrightarrow> (\<lambda>xa\<in>X // R. R `` {\<phi> x (SOME z. z \<in> xa)}) \<in> carrier (BijGroup (X // R))"
  proof-
    fix g
    assume
      A1_0: "Group.group G" and
      A1_1: "Group.group (BijGroup X)" and
      A1_2: "\<phi> \<in> carrier G \<rightarrow> carrier (BijGroup X)" and
      A1_3: "\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. \<phi> (x \<otimes>\<^bsub>G\<^esub> y) = \<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y" and
      A1_4: "g \<in> carrier G"
    have H_0: "group_action G X \<phi>"
      apply (clarsimp simp add: group_action_def group_hom_def group_hom_axioms_def)
      apply (simp add: A1_0 A1_1)+
      apply (simp add: hom_def)
      apply (rule conjI)
      using A1_2
       apply blast
      by (simp add: A1_3)
    have H1_0: "\<And>x y. \<lbrakk>x \<in> X // R; y \<in> X // R; R `` {\<phi> g (SOME z. z \<in> x)} =
                                                     R `` {\<phi> g (SOME z. z \<in> y)}\<rbrakk> \<Longrightarrow> x \<subseteq> y"
    proof (clarify; rename_tac a)
      fix x y a
      assume
        A2_0: "x \<in> X // R" and
        A2_1: "y \<in> X // R" and
        A2_2: "R `` {\<phi> g (SOME z. z \<in> x)} = R `` {\<phi> g (SOME z. z \<in> y)}" and
        A2_3: "a \<in> x"
      obtain b where H2_b: "R `` {b} = y \<and> b \<in> X" 
        by (metis A2_1 quotientE)
      obtain a' b' where H2_a'_b': "a'\<in> x \<and> b'\<in> y \<and> R `` {\<phi> g a'} = R `` {\<phi> g b'}"
        by (metis A_0 A2_1 A2_2 A2_3 equiv_Eps_in some_eq_imp)
      from H2_a'_b' have H2_2: "(\<phi> g a', \<phi> g b') \<in> R"
        by (metis A_0 A1_4 A2_1 Image_singleton_iff eq_var_rel.is_eq_var_rel' eq_var_rel_axioms
            quotient_eq_iff)
      hence H2_0: "(\<phi> (inv\<^bsub>G\<^esub> g) (\<phi> g a'), \<phi> (inv\<^bsub>G\<^esub> g) (\<phi> g b')) \<in> R"
        by (simp add: A1_0 is_eq_var_rel A1_4)
      have H2_1: "a' \<in> X \<and> b' \<in> X" 
        using A_0 A2_0 A2_1 H2_a'_b' in_quotient_imp_subset
        by blast
      hence H2_2: "(a', b') \<in> R"
        using H2_0
        by (metis A1_4 H_0 group_action.orbit_sym_aux)
      have H2_3: "(a, a') \<in> R" 
        by (meson A_0 A2_0 A2_3 H2_a'_b' quotient_eq_iff)
      hence H2_4: "(b', a) \<in> R" 
        using H2_2
        by (metis A_0 A2_0 A2_1 A2_3 H2_a'_b' quotient_eqI quotient_eq_iff)
      thus "a \<in> y"
        by (metis A_0 A2_1 H2_a'_b' in_quotient_imp_closed)
    qed
    have H1_1: "\<And>x. x \<in> X // R \<Longrightarrow> \<exists>xa\<in>X // R. x = R `` {\<phi> g (SOME z. z \<in> xa)}"
    proof -
      fix x
      assume
        A2_0: "x \<in> X // R"
      have H2_0: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow> R `` {e} \<subseteq> R `` {\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) e)}"
      proof (rule subsetI)
        fix e y
        assume
          A3_0: "R `` {e} \<in> X // R" and
          A3_1: "y \<in> R `` {e}"
        have H3_0: "y \<in> X" 
          using A3_1 is_subrel
          by blast
        from H_0 have H3_1: "\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) y) = y"
          by (metis (no_types, lifting) A1_0 A1_4 H3_0 group.inv_closed group.inv_inv
              group_action.orbit_sym_aux)
        from A3_1 have H3_2: "(e, y) \<in> R"
          by simp
        hence H3_3: "((\<phi> (inv\<^bsub>G\<^esub> g) e), (\<phi> (inv\<^bsub>G\<^esub> g) y)) \<in> R"
          using is_eq_var_rel A1_4 A1_0
          by simp
        hence H3_4: "(\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) e), \<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) y)) \<in> R"
          using is_eq_var_rel A1_4 A1_0
          by simp
        hence H3_5: "(\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) e), y) \<in> R"
          using H3_1
          by simp
        thus "y \<in> R `` {\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) e)}"
          by simp
      qed
      hence H2_1: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow> R `` {e} = R `` {\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) e)}" 
        by (metis A_0 proj_def proj_in_iff equiv_class_eq_iff subset_equiv_class)
      have H2_2: "\<And>e f. R `` {e} \<in> X // R \<Longrightarrow> R `` {f} \<in> X // R \<Longrightarrow>
        R `` {e} = R `` {f} \<Longrightarrow> \<forall>f'\<in> R `` {f}. R `` {e} = R `` {f'}"
        by (metis A_0 Image_singleton_iff equiv_class_eq)
      have H2_3: "x \<in> X // R \<Longrightarrow> \<exists>e\<in>X. x = R `` {e}" 
        by (meson quotientE)
      have H2_4: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow> R `` {e} = R `` {\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) e)} \<and>
        (\<phi> (inv\<^bsub>G\<^esub> g) e) \<in> R `` {\<phi> (inv\<^bsub>G\<^esub> g) e}"
        by (smt (z3) A_0 A1_0 A1_4 H_0 H2_1 Image_singleton_iff equiv_class_eq_iff
            group.inv_closed group_action.element_image in_quotient_imp_non_empty
            subset_empty subset_emptyI)
      have H2_5: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow> \<forall>z\<in>R `` {\<phi> (inv\<^bsub>G\<^esub> g) e}. (\<phi> (inv\<^bsub>G\<^esub> g) e, z) \<in> R"
        by simp
      hence H2_6: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow>
        \<forall>z\<in>R `` {\<phi> (inv\<^bsub>G\<^esub> g) e}. (\<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) e), \<phi> g z) \<in> R"
        using is_eq_var_rel' A1_4 A1_0
        by blast
      hence H2_7: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow> \<forall>z\<in>R `` {\<phi> (inv\<^bsub>G\<^esub> g) e}. (e, \<phi> g z) \<in> R"
        using H2_1
        by blast
      hence H2_8: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow> \<forall>z\<in>R `` {\<phi> (inv\<^bsub>G\<^esub> g) e}. R `` {e} = R `` {\<phi> g z}"
        by (meson A_0 equiv_class_eq_iff)
      have H2_9: "\<And>e. R `` {e} \<in> X // R \<Longrightarrow>
      R `` {e} = R `` {\<phi> g (SOME z. z \<in> R `` {\<phi> (inv\<^bsub>G\<^esub> g) e})}"
      proof-
        fix e
        assume
          A3_0: "R `` {e} \<in> X // R"
        show "R `` {e} = R `` {\<phi> g (SOME z. z \<in> R `` {\<phi> (inv\<^bsub>G\<^esub> g) e})}"
          apply (rule someI2[where Q = "\<lambda>z. R `` {e} = R `` {\<phi> g z}" and
                P = "\<lambda>z. z \<in> R `` {\<phi> (inv\<^bsub>G\<^esub> g) e}" and a = "\<phi> (inv\<^bsub>G\<^esub> g) e"])
          using A3_0 H2_4
           apply blast
          using A3_0 H2_8
          by auto
      qed
      have H2_10: "\<forall>e. (R `` {e} \<in> X // R \<longrightarrow>
      (R `` {e} = R `` {\<phi> g (SOME z. z \<in> R `` {\<phi> (inv\<^bsub>G\<^esub> g) e})}))"
        using H2_9
        by auto
      hence H2_11: "\<forall>e. (R `` {e} \<in> X // R \<longrightarrow>
      (\<exists>xa\<in>X // R. R `` {e} = R `` {\<phi> g (SOME z. z \<in> xa)}))"
        using H2_8
        apply clarsimp
        by (smt (verit, best) A_0 H2_3 H2_5 H2_4 equiv_Eps_in equiv_class_eq_iff quotientI)
      have H2_12: "\<And>x. x \<in> X // R \<Longrightarrow> \<exists>e\<in>X. x = R `` {e} "
        by (meson quotientE)
      have H2_13: "\<And>x. x \<in> X // R \<Longrightarrow> \<exists>xa\<in>X // R. x = R `` {\<phi> g (SOME z. z \<in> xa)}"
        using H2_11 H2_12
        by blast
      show "\<exists>xa\<in>X // R. x = R `` {\<phi> g (SOME z. z \<in> xa)}"
        by (simp add: A2_0 H2_13)
    qed
    show "(\<lambda>x\<in>X // R. R `` {\<phi> g (SOME z. z \<in> x)}) \<in> carrier (BijGroup (X // R))"
      apply (clarsimp simp add: BijGroup_def Bij_def bij_betw_def)
      subgoal
        apply (clarsimp simp add: inj_on_def)
        apply (rule conjI)
         apply (clarsimp)
         apply (rule subset_antisym)
          apply (simp add: H1_0)
         apply (simp add: \<open>\<And>y x. \<lbrakk>x \<in> X // R;
          y \<in> X // R; R `` {\<phi> g (SOME z. z \<in> x)} = R `` {\<phi> g (SOME z. z \<in> y)}\<rbrakk> \<Longrightarrow> x \<subseteq> y\<close>)
        apply (rule subset_antisym; clarify)
        subgoal for x y
          by (metis A_0 is_eq_var_rel' A1_4 Eps_cong equiv_Eps_preserves equiv_class_eq_iff
              quotientI) 
        apply (clarsimp simp add: Set.image_def)
        by (simp add: H1_1)
      done
  qed
  have H_1: "\<And>x y. \<lbrakk>Group.group G; Group.group (BijGroup X); R \<subseteq> X \<times> X;
            \<phi> \<in> carrier G \<rightarrow> carrier (BijGroup X);
           \<forall>x\<in>carrier G. \<forall>y\<in>carrier G. \<phi> (x \<otimes>\<^bsub>G\<^esub> y) = \<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y;
           x \<in> carrier G; y \<in> carrier G; x \<otimes>\<^bsub>G\<^esub> y \<in> carrier G\<rbrakk> \<Longrightarrow>
           (\<lambda>xa\<in>X // R. R `` {(\<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y) (SOME z. z \<in> xa)}) =
           (\<lambda>xa\<in>X // R. R `` {\<phi> x (SOME z. z \<in> xa)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
           (\<lambda>x\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x)})"
  proof -
    fix x y 
    assume
      A1_1: "Group.group G" and
      A1_2: "Group.group (BijGroup X)" and
      A1_3: "\<phi> \<in> carrier G \<rightarrow> carrier (BijGroup X)" and
      A1_4: "\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. \<phi> (x \<otimes>\<^bsub>G\<^esub> y) = \<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y" and
      A1_5: "x \<in> carrier G" and
      A1_6: "y \<in> carrier G" and
      A1_7: "x \<otimes>\<^bsub>G\<^esub> y \<in> carrier G"
    have H1_0: "\<And>w::'X set. w \<in> X // R \<Longrightarrow>
    R `` {(\<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y) (SOME z. z \<in> w)} =
    ((\<lambda>v\<in>X // R. R `` {\<phi> x (SOME z. z \<in> v)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
    (\<lambda>x\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x)})) w"
    proof-
      fix w
      assume
        A2_0: "w \<in> X // R" 
      have H2_4: "\<phi> y ` w \<in> X // R"
        using ec_er_closed_under_action[where w = "w" and g = "y"]
        by (clarsimp simp add: group_hom_axioms_def hom_def A_0 A1_1 A1_2 is_eq_var_rel' A1_3 A1_4
            A1_6 A2_0) 
      hence H2_1: "R `` {(\<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y) (SOME z. z \<in> w)} =
      R `` {\<phi> (x \<otimes>\<^bsub>G\<^esub> y) (SOME z. z \<in> w)}"
        using A1_4 A1_5 A1_6
        by auto
      also have H2_2: "... = R `` {SOME z. z \<in> \<phi> (x \<otimes>\<^bsub>G\<^esub> y) ` w}"
        using A1_7 equiv_equivar_class_some_eq[where w = "w" and g = "x \<otimes>\<^bsub>G\<^esub> y"]
        by (clarsimp simp add: A1_7 A_0 A2_0 group_action_def group_hom_def group_hom_axioms_def
            hom_def)
      also have H2_3: "... = R `` {SOME z. z \<in> \<phi> x ` \<phi> y ` w}"
        apply (rule meta_mp[of "\<not>(\<exists>x. x \<in> w \<and> x \<notin> X)"])
        using A1_1 is_eq_var_rel' A1_3 A1_4 A1_5 A1_6 A2_0
         apply (clarsimp simp add: image_def BijGroup_def restrict_def compose_def Pi_def)
         apply (smt (z3) Eps_cong)
        apply (clarify) 
        using A_0 A2_0 in_quotient_imp_subset
        by auto
      also have H2_5: "... = R `` {\<phi> x (SOME z. z \<in> \<phi> y ` w)}"
        using equiv_equivar_class_some_eq[where w = "\<phi> y ` w" and g = "x"]
        apply (clarsimp simp add: A_0 group_action_def group_hom_def group_hom_axioms_def hom_def)
        by (simp add: A1_1 A1_2 is_eq_var_rel' A1_3 A1_4 A1_5 H2_4)
      also have H2_6: "... = R `` {\<phi> x (SOME z. z \<in> R``{(SOME z'. z' \<in> \<phi> y ` w)})}"
        using H2_4 nested_somes[where w = "\<phi> y ` w" and X = "X" and R = "R"] A_0
        by presburger
      also have H2_7: "... = R `` {\<phi> x (SOME z. z \<in> R `` {\<phi> y (SOME z'. z' \<in> w)})}"
        using equiv_equivar_class_some_eq[where g = "y" and w = "w"] H2_6
        by (simp add: A_0 group_action_def
            group_hom_def group_hom_axioms_def hom_def A1_1 A1_2 is_eq_var_rel' A1_3 A1_4 A2_0 A1_6) 
      also have H2_9: "... = ((\<lambda>v\<in>X // R. R `` {\<phi> x (SOME z. z \<in> v)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
      (\<lambda>x\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x)})) w"
      proof-
        have H3_0: "\<And>u. R `` {\<phi> y (SOME z. z \<in> w)} \<in> X // R \<Longrightarrow> u \<in> carrier G \<Longrightarrow>
        (\<lambda>v\<in>X // R. R `` {\<phi> u (SOME z. z \<in> v)}) \<in> Bij (X // R)"
        proof -
          fix u
          assume 
            A4_0: "R `` {\<phi> y (SOME z. z \<in> w)} \<in> X // R" and
            A4_1: "u \<in> carrier G"
          have H4_0: "\<forall>g \<in> carrier G.
          (\<lambda>x\<in>X // R. R `` {\<phi> g (SOME z. z \<in> x)}) \<in> carrier (BijGroup (X // R))"
            by (simp add: A_0 A1_1 A1_2 A1_3 A1_4 H_0 is_subrel)
          thus "(\<lambda>v\<in>X // R. R `` {\<phi> u (SOME z. z \<in> v)}) \<in> Bij (X // R)"
            by (auto simp add: BijGroup_def A4_1)
        qed
        have H3_1: "R `` {\<phi> y (SOME z. z \<in> w)} \<in> X // R"
        proof-
          have H4_0: "\<phi> y ` w \<in> X // R"
            using ec_er_closed_under_action
            by (simp add: H2_4)
          hence H4_1: "R `` {(SOME z. z \<in> \<phi> y ` w)} = \<phi> y ` w"
            apply (clarsimp simp add: image_def) 
            apply (rule subset_antisym)
            using A_0 equiv_Eps_in in_quotient_imp_closed
             apply fastforce
            using A_0 equiv_Eps_in quotient_eq_iff
            by fastforce
          have H4_2: "R `` {\<phi> y (SOME z. z \<in> w)} = R `` {(SOME z. z \<in> \<phi> y ` w)}"
            using equiv_equivar_class_some_eq[where g = "y" and w = "w"]
            by (metis A_0 A2_0 H4_0 H4_1 equiv_Eps_in imageI some_equiv_class_id)
          from H4_0 H4_1 H4_2 show "R `` {\<phi> y (SOME z. z \<in> w)} \<in> X // R"
            by auto
        qed
        show ?thesis
          apply (rule meta_mp[of "R `` {\<phi> y (SOME z. z \<in> w)} \<in> X // R"])
           apply (rule meta_mp[of "\<forall>u \<in> carrier G.
         (\<lambda>v\<in>X // R. R `` {\<phi> u (SOME z. z \<in> v)}) \<in> Bij (X // R)"])
          using A2_0 A1_5 A1_6
            apply ( simp add: BijGroup_def compose_def)
           apply clarify
          by (simp add: H3_0 H3_1)+
      qed
      finally show "R `` {(\<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y) (SOME z. z \<in> w)} =
      ((\<lambda>v\<in>X // R. R `` {\<phi> x (SOME z. z \<in> v)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
      (\<lambda>x\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x)})) w"
        by simp
    qed
    have H1_1: "\<And>w::'X set. w \<notin> X // R \<Longrightarrow>
    ((\<lambda>v\<in>X // R. R `` {\<phi> x (SOME z. z \<in> v)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
    (\<lambda>x\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x)})) w = undefined"
    proof -
      fix w
      assume
        A2_0: "w \<notin> X // R" 
      have H2_0: "\<And>u. u\<in> carrier G \<Longrightarrow> (\<lambda>v\<in>X // R. R `` {\<phi> u (SOME z. z \<in> v)}) \<in> Bij (X // R)"
        using H_0
        apply (clarsimp simp add: A_0 A1_1 A1_2 is_eq_var_rel' A1_3 A1_4 is_subrel)
        by (simp add: BijGroup_def)
      hence H2_1: "(\<lambda>x'\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x')}) \<in> Bij (X // R)"
        using A1_6
        by auto
      from H2_0 have H2_2: "(\<lambda>x'\<in>X // R. R `` {\<phi> x (SOME z. z \<in> x')}) \<in> Bij (X // R)"
        by (simp add: A1_5)
      thus "((\<lambda>v\<in>X // R. R `` {\<phi> x (SOME z. z \<in> v)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
      (\<lambda>x\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x)})) w = undefined"
        using H2_1 H2_2
        by (auto simp add: BijGroup_def compose_def A2_0)
    qed
    from H1_0 H1_1 have "\<And>w. (\<lambda>xa\<in>X // R. R `` {(\<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y) (SOME z. z \<in> xa)}) w =
    ((\<lambda>xa\<in>X // R. R `` {\<phi> x (SOME z. z \<in> xa)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
    (\<lambda>x'\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x')})) w"
      by auto
    thus "(\<lambda>xa\<in>X // R. R `` {(\<phi> x \<otimes>\<^bsub>BijGroup X\<^esub> \<phi> y) (SOME z. z \<in> xa)}) =
    (\<lambda>xa\<in>X // R. R `` {\<phi> x (SOME z. z \<in> xa)}) \<otimes>\<^bsub>BijGroup (X // R)\<^esub>
    (\<lambda>x\<in>X // R. R `` {\<phi> y (SOME z. z \<in> x)})"
      by (simp add: restrict_def)
  qed
  show ?thesis
    apply (clarsimp simp add: group_action_def group_hom_def)
    using eq_var_rel_axioms
    apply (clarsimp simp add: eq_var_rel_def eq_var_rel_axioms_def
        group_action_def group_hom_def)
    apply (rule conjI)
     apply (simp add: group_BijGroup)
    apply (clarsimp simp add: group_hom_axioms_def hom_def)
    apply (intro conjI)
     apply (rule funcsetI; simp)
     apply (simp add: H_0)
    apply (clarify; rule conjI; intro impI)
     apply (simp add: H_1)
    by (auto simp add: group.is_monoid monoid.m_closed)
qed
end

locale eq_var_func = GA_0: alt_grp_act G X \<phi> + GA_1: alt_grp_act G Y \<psi> 
  for
    G :: "('grp, 'b) monoid_scheme" and
    X :: "'X set" and
    \<phi> and
    Y :: "'Y set" and
    \<psi> +
  fixes
    f :: "'X \<Rightarrow> 'Y" 
  assumes
    is_ext_func_bet:
    "f \<in> (X \<rightarrow>\<^sub>E Y)" and
    is_eq_var_func:
    "\<And>a g. a \<in> X \<Longrightarrow> g \<in> carrier G \<Longrightarrow> f (a \<odot>\<^bsub>\<phi>\<^esub> g) = (f a) \<odot>\<^bsub>\<psi>\<^esub> g"
begin

lemma is_eq_var_func' [simp]:
  "a \<in> X \<Longrightarrow> g \<in> carrier G \<Longrightarrow> f (\<phi> g a) = \<psi> g (f a)"
  using is_eq_var_func
  by auto

end

lemma G_set_equiv:
  "alt_grp_act G A \<phi> \<Longrightarrow> eq_var_subset G A \<phi> A"
  by (auto simp add: eq_var_subset_def eq_var_subset_axioms_def group_action_def
      group_hom_def group_hom_axioms_def hom_def BijGroup_def Bij_def bij_betw_def)

subsection \<open>
Basic ($G$)-Automata Theory
\<close>


locale language = 
  fixes A :: "'alpha set" and
    L
  assumes
    is_lang: "L \<subseteq> A\<^sup>\<star>"

locale G_lang = alt_grp_act G A \<phi> + language A L 
  for
    G :: "('grp, 'b) monoid_scheme" and
    A :: "'alpha set" (structure) and
    \<phi> L +
  assumes
    L_is_equivar:
    "eq_var_subset G (A\<^sup>\<star>) (induced_star_map \<phi>) L"
begin
lemma G_lang_is_lang[simp]: "language A L"
  by (simp add: language_axioms)
end

sublocale G_lang \<subseteq> language
  by simp

fun give_input :: "('state \<Rightarrow> 'alpha \<Rightarrow> 'state) \<Rightarrow> 'state \<Rightarrow> 'alpha list \<Rightarrow> 'state"
  where "give_input trans_func s Nil = s"
  |   "give_input trans_func s (a#as) = give_input trans_func (trans_func s a) as"

adhoc_overloading
  star give_input

locale det_aut =
  fixes
    labels :: "'alpha set" and
    states :: "'state set" and
    init_state :: "'state" and
    fin_states :: "'state set" and
    trans_func :: "'state \<Rightarrow> 'alpha \<Rightarrow> 'state" ("\<delta>")
  assumes
    init_state_is_a_state:
    "init_state \<in> states" and
    fin_states_are_states:
    "fin_states \<subseteq> states" and
    trans_func_ext:
    "(\<lambda>(state, label). trans_func state label) \<in> (states \<times> labels) \<rightarrow>\<^sub>E states" 
begin

lemma trans_func_well_def:
  "\<And>state label. state \<in> states \<Longrightarrow> label \<in> labels \<Longrightarrow> (\<delta> state label) \<in> states"
  using trans_func_ext
  by auto

lemma give_input_closed:
  "input \<in> (labels\<^sup>\<star>) \<Longrightarrow> s \<in> states \<Longrightarrow> (\<delta>\<^sup>\<star>) s input \<in> states"
  apply (induction input arbitrary: s)
  by (auto simp add: trans_func_well_def)

lemma input_under_concat:
  "w \<in> labels\<^sup>\<star> \<Longrightarrow> v \<in> labels\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) s (w @ v) = (\<delta>\<^sup>\<star>) ((\<delta>\<^sup>\<star>) s w) v"
  apply (induction w arbitrary: s)
  by auto

lemma eq_pres_under_concat:
  assumes
    "w \<in> labels\<^sup>\<star>" and
    "w' \<in> labels\<^sup>\<star>" and
    "s \<in> states" and
    "(\<delta>\<^sup>\<star>) s w = (\<delta>\<^sup>\<star>) s w'"
  shows "\<forall>v \<in> labels\<^sup>\<star>. (\<delta>\<^sup>\<star>) s (w @ v) = (\<delta>\<^sup>\<star>) s (w' @ v)"
  using input_under_concat[where w = w and s = s] input_under_concat[where w = w' and s = s] assms
  by auto

lemma trans_to_charact:
  "\<And>s a w. \<lbrakk>s \<in> states; a \<in> labels; w \<in> labels\<^sup>\<star>; s = (\<delta>\<^sup>\<star>) i w\<rbrakk> \<Longrightarrow> (\<delta>\<^sup>\<star>) i (w @ [a]) = \<delta> s a"
proof-
  fix s a w
  assume
    A_0: "s \<in> states" and
    A_1: "a \<in> labels" and
    A_2: "w \<in> labels\<^sup>\<star>" and
    A_3: "s = (\<delta>\<^sup>\<star>) i w"
  have H_0: "trans_func s a = (\<delta>\<^sup>\<star>) s [a]"
    by auto
  from A_2 A_3 H_0 have H_1: "(\<delta>\<^sup>\<star>) s [a] = (\<delta>\<^sup>\<star>) ((\<delta>\<^sup>\<star>) i w) [a]"
    by simp
  from A_1 A_2 have H_2: "(\<delta>\<^sup>\<star>) ((\<delta>\<^sup>\<star>) i w) [a] = (\<delta>\<^sup>\<star>) i (w @ [a])"
    using input_under_concat
    by force
  show "(\<delta>\<^sup>\<star>) i (w @ [a]) = \<delta> s a"
    using A_1 H_0 A_3 H_1 H_2
    by force
qed

end

locale aut_hom = Aut0: det_aut A S\<^sub>0 i\<^sub>0 F\<^sub>0 \<delta>\<^sub>0 + Aut1: det_aut A S\<^sub>1 i\<^sub>1 F\<^sub>1 \<delta>\<^sub>1 for
  A :: "'alpha set" and
  S\<^sub>0 :: "'states_0 set" and
  i\<^sub>0 and F\<^sub>0 and \<delta>\<^sub>0 and
  S\<^sub>1 :: "'states_1 set" and
  i\<^sub>1 and F\<^sub>1 and \<delta>\<^sub>1 +
fixes f :: "'states_0 \<Rightarrow> 'states_1"
assumes
  hom_is_ext:
  "f \<in> S\<^sub>0 \<rightarrow>\<^sub>E S\<^sub>1" and
  pres_init:
  "f i\<^sub>0 = i\<^sub>1" and
  pres_final:
  "s \<in> F\<^sub>0 \<longleftrightarrow> f s \<in> F\<^sub>1 \<and> s \<in> S\<^sub>0" and
  pres_trans:
  "s\<^sub>0 \<in> S\<^sub>0 \<Longrightarrow> a \<in> A \<Longrightarrow> f (\<delta>\<^sub>0 s\<^sub>0 a) = \<delta>\<^sub>1 (f s\<^sub>0) a"
begin

lemma hom_translation:
  "input \<in> (A\<^sup>\<star>) \<Longrightarrow> s \<in> S\<^sub>0 \<Longrightarrow> (f ((\<delta>\<^sub>0\<^sup>\<star>) s input)) = ((\<delta>\<^sub>1\<^sup>\<star>) (f s) input)"
  apply (induction input arbitrary: s)
  by (auto simp add: Aut0.trans_func_well_def pres_trans)

lemma recognise_same_lang:
  "input \<in> A\<^sup>\<star> \<Longrightarrow> ((\<delta>\<^sub>0\<^sup>\<star>) i\<^sub>0 input) \<in> F\<^sub>0 \<longleftrightarrow> ((\<delta>\<^sub>1\<^sup>\<star>) i\<^sub>1 input) \<in> F\<^sub>1"
  using hom_translation[where input = input and s = i\<^sub>0]
  apply (clarsimp  simp add: Aut0.init_state_is_a_state pres_init pres_final)
  apply (induction input)
   apply (clarsimp simp add: Aut0.init_state_is_a_state)
  using Aut0.give_input_closed Aut0.init_state_is_a_state
  by blast

end

locale aut_epi = aut_hom + 
  assumes
    is_epi: "f ` S\<^sub>0 = S\<^sub>1"

locale det_G_aut =
  is_aut:       det_aut A S i F \<delta> +
  labels_a_G_set:   alt_grp_act G A \<phi> + 
  states_a_G_set:   alt_grp_act G S \<psi> +
  accepting_is_eq_var: eq_var_subset G S \<psi> F +
  init_is_eq_var:   eq_var_subset G S \<psi> "{i}" +
  trans_is_eq_var:   eq_var_func G "S \<times> A"
  "\<lambda>g\<in>carrier G. \<lambda>(s, a) \<in> (S \<times> A). (\<psi> g s, \<phi> g a)"
  S "\<psi>" "(\<lambda>(s, a) \<in> (S \<times> A). \<delta> s a)"
  for A :: "'alpha set" (structure) and
    S :: "'states set" and
    i F \<delta> and
    G :: "('grp, 'b) monoid_scheme" and
    \<phi> \<psi>
begin

adhoc_overloading
  star labels_a_G_set.induced_star_map

lemma give_input_eq_var:
  "eq_var_func G
 (A\<^sup>\<star> \<times> S) (\<lambda>g\<in>carrier G. \<lambda>(w, s) \<in> (A\<^sup>\<star> \<times> S). ((\<phi>\<^sup>\<star>) g w, \<psi> g s))
 S \<psi>
 (\<lambda>(w, s) \<in> (A\<^sup>\<star> \<times> S). (\<delta>\<^sup>\<star>) s w)"
proof-
  have H_0: "\<And>a w s g.
       (\<And>s. s \<in> S \<Longrightarrow> (\<phi>\<^sup>\<star>) g w \<in> A\<^sup>\<star> \<and> \<psi> g s \<in> S \<Longrightarrow>
       (\<delta>\<^sup>\<star>) (\<psi> g s) ((\<phi>\<^sup>\<star>) g w) = \<psi> g ((\<delta>\<^sup>\<star>) s w)) \<Longrightarrow>
       s \<in> S \<Longrightarrow>
       g \<in> carrier G \<Longrightarrow>
       a \<in> A \<Longrightarrow> \<forall>x\<in>set w. x \<in> A \<Longrightarrow> \<psi> g s \<in> S \<Longrightarrow> \<forall>x\<in>set ((\<phi>\<^sup>\<star>) g (a # w)). x \<in> A \<Longrightarrow>
       (\<delta>\<^sup>\<star>) (\<psi> g s) ((\<phi>\<^sup>\<star>) g (a # w)) = \<psi> g ((\<delta>\<^sup>\<star>) (\<delta> s a) w)"
  proof-
    fix a w s g
    assume
      A_IH: "(\<And>s. s \<in> S \<Longrightarrow>
             (\<phi>\<^sup>\<star>) g w \<in> A\<^sup>\<star> \<and> \<psi> g s \<in> S \<Longrightarrow>
             (\<delta>\<^sup>\<star>) (\<psi> g s) ((\<phi>\<^sup>\<star>) g w) = \<psi> g ((\<delta>\<^sup>\<star>) s w))" and
      A_0: "s \<in> S" and
      A_1: "\<psi> g s \<in> S" and
      A_2: "\<forall>x\<in>set ((\<phi>\<^sup>\<star>) g (a # w)). x \<in> A" and
      A_3: "g \<in> carrier G" and
      A_4: " a \<in> A" and
      A_5: "\<forall>x\<in>set w. x \<in> A"
    have H_0: "((\<phi>\<^sup>\<star>) g (a # w)) = (\<phi> g a) # (\<phi>\<^sup>\<star>) g w"
      using A_4 A_5 A_3
      by auto
    hence H_1: "(\<delta>\<^sup>\<star>) (\<psi> g s) ((\<phi>\<^sup>\<star>) g (a # w))
       = (\<delta>\<^sup>\<star>) (\<psi> g s) ((\<phi> g a) # (\<phi>\<^sup>\<star>) g w)"
      by simp
    have H_2: "...  = (\<delta>\<^sup>\<star>) ((\<delta>\<^sup>\<star>) (\<psi> g s) [\<phi> g a]) ((\<phi>\<^sup>\<star>) g w)"
      using is_aut.input_under_concat
      by simp
    have H_3: "(\<delta>\<^sup>\<star>) (\<psi> g s) [\<phi> g a] = \<psi> g (\<delta> s a)"
      using trans_is_eq_var.eq_var_func_axioms A_4 A_5 A_0 A_1 A_3 apply (clarsimp simp del:
          GMN_simps simp add: eq_var_func_def eq_var_func_axioms_def make_op_def)
      apply (rule meta_mp[of "\<psi> g s \<in> S \<and> \<phi> g a \<in> A \<and> s \<in> S \<and> a \<in> A"])
       apply presburger
      apply (clarify)
      using labels_a_G_set.element_image
      by presburger
    have H_4: "(\<delta>\<^sup>\<star>) (\<psi> g (\<delta> s a)) ((\<phi>\<^sup>\<star>) g w) = \<psi> g ((\<delta>\<^sup>\<star>) (\<delta> s a) w)"
      apply (rule A_IH[where s1 = "\<delta> s a"])
      subgoal
        using A_4 A_5 A_0
        by (auto simp add: is_aut.trans_func_well_def)
      using A_4 A_5 A_0 A_3 \<open>\<delta> s a \<in> S\<close> states_a_G_set.element_image
      by (metis A_2 Cons_in_lists_iff H_0 in_listsI)
    show "(\<delta>\<^sup>\<star>) (\<psi> g s) ((\<phi>\<^sup>\<star>) g (a # w)) = \<psi> g ((\<delta>\<^sup>\<star>) (\<delta> s a) w)"
      using H_0 H_1 H_2 H_3 H_4
      by presburger
  qed
  show ?thesis
    apply (subst eq_var_func_def)
    apply (subst eq_var_func_axioms_def)
    apply (rule conjI)
     apply (rule prod_group_act[where G = G and A = "A\<^sup>\<star>" and \<phi> = "(\<phi>\<^sup>\<star>)"
          and B = S     and \<psi> = \<psi>])
    using labels_a_G_set.lists_a_Gset
      apply blast
     apply (simp add: states_a_G_set.group_action_axioms)
    apply (rule conjI)
     apply (simp add: states_a_G_set.group_action_axioms)
    apply (rule conjI)
     apply (subst extensional_funcset_def)
     apply (subst restrict_def)
     apply (subst Pi_def)
     apply (subst extensional_def)
     apply (auto simp add: in_listsI is_aut.give_input_closed)[1]
    apply (subst restrict_def)
    apply (clarsimp simp del: GMN_simps simp add: make_op_def)
    apply (rule conjI; intro impI)
    subgoal for w s g
      apply (induction w arbitrary: s) 
       apply simp
      apply (clarsimp simp del: GMN_simps)
      by (simp add: H_0 del: GMN_simps)
    apply clarsimp
    by (metis (no_types, lifting) image_iff in_lists_conv_set labels_a_G_set.surj_prop list.set_map
        states_a_G_set.element_image)
qed

definition
  accepted_words :: "'alpha list set"
  where "accepted_words = {w. w \<in> A\<^sup>\<star> \<and> ((\<delta>\<^sup>\<star>) i w) \<in> F}"

lemma induced_g_lang:
  "G_lang G A \<phi> accepted_words"
proof-
  have H_0: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w \<in> F \<Longrightarrow> map (\<phi> g) w \<in> A\<^sup>\<star>"
    apply (clarsimp)
    using labels_a_G_set.element_image
    by blast
  have H_1: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i w \<in> F \<Longrightarrow> (\<delta>\<^sup>\<star>) i (map (\<phi> g) w) \<in> F"
  proof -
    fix g w
    assume
      A_0: "g \<in> carrier G" and
      A_1: "w \<in> A\<^sup>\<star>" and
      A_2: "(\<delta>\<^sup>\<star>) i w \<in> F"
    have H1_0: "\<psi> g ((\<delta>\<^sup>\<star>) i w) \<in> F"
      using accepting_is_eq_var.eq_var_subset_axioms
        A_0 A_2 accepting_is_eq_var.is_equivar
      by blast
    have H1_1: "\<psi> g i = i"
      using init_is_eq_var.eq_var_subset_axioms A_0
        init_is_eq_var.is_equivar
      by auto
    have H1_2: "\<And>w g. \<lbrakk>g \<in> carrier G; w \<in> A\<^sup>\<star>; (\<delta>\<^sup>\<star>) i w \<in> F\<rbrakk> \<Longrightarrow> (\<phi>\<^sup>\<star>) g w \<in> A\<^sup>\<star>"
      using H_0
      by auto
    from A_1 have H1_3: "w \<in> A\<^sup>\<star>"
      by auto
    show "(\<delta>\<^sup>\<star>) i (map (\<phi> g) w) \<in> F"
      using give_input_eq_var A_0 A_1 H1_1 H1_3
      apply (clarsimp simp del: GMN_simps simp add: eq_var_func_def eq_var_func_axioms_def
          make_op_def)
      using A_2 H1_0 is_aut.init_state_is_a_state H1_2
      by (smt (verit, best) H1_3 labels_a_G_set.induced_star_map_def restrict_apply)
  qed
  have H_2: "\<And>g x. g \<in> carrier G \<Longrightarrow> x \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i x \<in> F \<Longrightarrow>
            x \<in> map (\<phi> g) ` {w \<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w \<in> F}"
  proof-
    fix g w
    assume
      A_0: "g \<in> carrier G" and
      A_1: "w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w \<in> F" 
    have H_0: "\<And>g xa. g \<in> carrier G \<Longrightarrow> xa \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i xa \<in> F \<Longrightarrow> (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g xa) \<in> F" 
      using H_1
      by auto
    have H_1: "((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w) \<in> A\<^sup>\<star>"
      by (smt (verit) A_0 A_1 in_listsI alt_grp_act_def group_action.bij_prop1
          group_action.orbit_sym_aux labels_a_G_set.lists_a_Gset)
    have H_2: "(\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w) \<in> F"
      apply (rule H_0)
      using A_0 A_1
      by (meson group.inv_closed group_hom.axioms(1) labels_a_G_set.group_hom)+
    have H_3: "((\<phi>\<^sup>\<star>) g ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w))
     \<in> (\<phi>\<^sup>\<star>) g ` {w \<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w \<in> F}"
      using H_1 H_2
      by auto 
    have H_4: "((\<phi>\<^sup>\<star>) g ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w)) = w"
      using A_0 A_1  
      by (smt (verit) in_listsI alt_grp_act_def group_action.bij_prop1 group_action.orbit_sym_aux
          labels_a_G_set.lists_a_Gset)
    show "w \<in> map (\<phi> g) ` {w \<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w \<in> F}"
      using H_3 H_4 A_0
      by auto
  qed
  show ?thesis
    apply (clarsimp simp del: GMN_simps simp add: G_lang_def accepted_words_def G_lang_axioms_def)
    apply (rule conjI)
    using labels_a_G_set.alt_grp_act_axioms
     apply (auto)[1]
    apply (clarsimp simp del: GMN_simps simp add: eq_var_subset_def eq_var_subset_axioms_def)
    apply (intro conjI)
      apply (simp add: language.intro)
    using labels_a_G_set.alt_grp_act_axioms labels_a_G_set.lists_a_Gset
     apply blast
    apply (clarsimp simp del: GMN_simps)
    apply (rule subset_antisym; simp add: Set.subset_eq; rule allI; rule impI)
     apply (rule conjI)
      apply (simp add: H_0)
     apply (simp add: H_1)
    by (simp add: H_2)
qed
end

locale reach_det_aut =
  det_aut A S i F \<delta>  
  for A :: "'alpha set" (structure) and
    S :: "'states set" and
    i F \<delta> +
  assumes
    is_reachable:
    "s \<in> S \<Longrightarrow> \<exists>input \<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i input = s"

locale reach_det_G_aut =
  det_G_aut A S i F \<delta> G \<phi> \<psi> + reach_det_aut A S i F \<delta> 
  for A :: "'alpha set" (structure) and
    S :: "'states set" and
    i and F and \<delta> and
    G :: "('grp, 'b) monoid_scheme" and
    \<phi> \<psi> 
begin

text \<open>
To avoid duplicate variant of "star":
\<close>

no_adhoc_overloading
  star labels_a_G_set.induced_star_map
end

sublocale reach_det_G_aut \<subseteq> reach_det_aut
  using reach_det_aut_axioms
  by simp

locale G_aut_hom = Aut0: reach_det_G_aut A S\<^sub>0 i\<^sub>0 F\<^sub>0 \<delta>\<^sub>0 G \<phi> \<psi>\<^sub>0 +
  Aut1: reach_det_G_aut A S\<^sub>1 i\<^sub>1 F\<^sub>1 \<delta>\<^sub>1 G \<phi> \<psi>\<^sub>1 +
  hom_f: aut_hom A S\<^sub>0 i\<^sub>0 F\<^sub>0 \<delta>\<^sub>0 S\<^sub>1 i\<^sub>1 F\<^sub>1 \<delta>\<^sub>1 f +
  eq_var_f: eq_var_func G S\<^sub>0 \<psi>\<^sub>0 S\<^sub>1 \<psi>\<^sub>1 f for
  A :: "'alpha set" and
  S\<^sub>0 :: "'states_0 set" and
  i\<^sub>0 and F\<^sub>0 and \<delta>\<^sub>0 and
  S\<^sub>1 :: "'states_1 set" and
  i\<^sub>1 and F\<^sub>1 and \<delta>\<^sub>1 and
  G :: "('grp, 'b) monoid_scheme" and
  \<phi> \<psi>\<^sub>0 \<psi>\<^sub>1 f 

locale G_aut_epi = G_aut_hom + 
  assumes
    is_epi: "f ` S\<^sub>0 = S\<^sub>1"

locale det_aut_rec_lang = det_aut A S i F \<delta>  + language A L
  for A :: "'alpha set" (structure) and
    S :: "'states set" and
    i F \<delta> L + 
  assumes
    is_recognised:
    "w \<in> L \<longleftrightarrow> w \<in> A\<^sup>\<star> \<and> ((\<delta>\<^sup>\<star>) i w) \<in> F"

locale det_G_aut_rec_lang = det_G_aut A S i F \<delta> G \<phi> \<psi> + det_aut_rec_lang A S i F \<delta> L 
  for A :: "'alpha set" (structure) and
    S :: "'states set" and
    i F \<delta> and
    G :: "('grp, 'b) monoid_scheme" and
    \<phi> \<psi> L
begin

lemma lang_is_G_lang: "G_lang G A \<phi> L"
proof-
  have H0: "L = accepted_words"
    apply (simp add: accepted_words_def)
    apply (subst is_recognised [symmetric])
    by simp
  show "G_lang G A \<phi> L"
    apply (subst H0)
    apply (rule det_G_aut.induced_g_lang[of A S i F \<delta> G \<phi> \<psi>])
    by (simp add: det_G_aut_axioms)
qed  

text \<open>
To avoid ambiguous parse trees:
\<close>

no_notation trans_is_eq_var.GA_0.induced_quot_map ("[_]\<^sub>_\<index>" 60)
no_notation states_a_G_set.induced_quot_map ("[_]\<^sub>_\<index>" 60)

end

locale reach_det_aut_rec_lang = reach_det_aut A S i F \<delta> + det_aut_rec_lang A S i F \<delta> L
  for A :: "'alpha set" and
    S :: "'states set" and
    i F \<delta> and
    L :: "'alpha list set"

locale reach_det_G_aut_rec_lang = det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L +
  reach_det_G_aut A S i F \<delta> G \<phi> \<psi>
  for A :: "'alpha set" and
    S :: "'states set" and
    i F \<delta> and
    G :: "('grp, 'b) monoid_scheme" and
    \<phi> \<psi> and
    L :: "'alpha list set"

sublocale reach_det_G_aut_rec_lang \<subseteq> det_G_aut_rec_lang
  apply (simp add: det_G_aut_rec_lang_def)
  using reach_det_G_aut_rec_lang_axioms
  by (simp add: det_G_aut_axioms det_aut_rec_lang_axioms) 

locale det_G_aut_recog_G_lang = det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L + G_lang G A \<phi> L
  for A :: "'alpha set" (structure) and
    S :: "'states set" and
    i F \<delta> and
    G :: "('grp, 'b) monoid_scheme" and
    \<phi> \<psi> and
    L :: "'alpha list set"

sublocale det_G_aut_rec_lang \<subseteq> det_G_aut_recog_G_lang
  apply (simp add: det_G_aut_recog_G_lang_def)
  apply (rule conjI)
   apply (simp add: det_G_aut_rec_lang_axioms)
  by (simp add: lang_is_G_lang)

locale reach_det_G_aut_rec_G_lang = reach_det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L + G_lang G A \<phi> L
  for A :: "'alpha set" (structure) and
    S :: "'states set" and
    i F \<delta> and
    G :: "('grp, 'b) monoid_scheme" and
    \<phi> \<psi> L 

sublocale reach_det_G_aut_rec_lang \<subseteq> reach_det_G_aut_rec_G_lang
  apply (simp add: reach_det_G_aut_rec_G_lang_def)
  apply (rule conjI)
   apply (simp add: reach_det_G_aut_rec_lang_axioms)
  by (simp add: lang_is_G_lang)

lemma (in reach_det_G_aut)
  "reach_det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> accepted_words"
  apply (clarsimp simp del: simp add: reach_det_G_aut_rec_lang_def
      det_G_aut_rec_lang_def det_aut_rec_lang_axioms_def)
  apply (intro conjI)
    apply (simp add: det_G_aut_axioms)
   apply (clarsimp simp add: reach_det_G_aut_axioms accepted_words_def reach_det_aut_rec_lang_def)
   apply (simp add: det_aut_rec_lang_def det_aut_rec_lang_axioms.intro is_aut.det_aut_axioms
      language_def)
  by (simp add: reach_det_G_aut_axioms)

lemma (in det_G_aut) action_on_input:
  "\<And> g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> \<psi> g ((\<delta>\<^sup>\<star>) i w) = (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w)"
proof-
  fix g w
  assume
    A_0: "g \<in> carrier G" and
    A_1: "w \<in> A\<^sup>\<star>"
  have H_0: "(\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w) = (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w)"
    using A_0 init_is_eq_var.is_equivar
    by fastforce
  have H_1: "\<psi> g ((\<delta>\<^sup>\<star>) i w) = (\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w)"
    using A_0 A_1 give_input_eq_var
    apply (clarsimp simp del: GMN_simps simp add: eq_var_func_axioms_def eq_var_func_def
        make_op_def)
    apply (rule meta_mp[of "((\<phi>\<^sup>\<star>) g w) \<in> A\<^sup>\<star> \<and> \<psi> g i \<in> S"]) 
    using is_aut.init_state_is_a_state A_1
     apply presburger
    using det_G_aut_axioms
    apply (clarsimp simp add: det_G_aut_def) 
    apply (rule conjI; rule impI; rule conjI)
    using labels_a_G_set.element_image
       apply fastforce
    using is_aut.init_state_is_a_state states_a_G_set.element_image
    by blast+
  show "\<psi> g ((\<delta>\<^sup>\<star>) i w) = (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w)"
    using H_0 H_1
    by simp
qed

definition (in det_G_aut)
  reachable_states :: "'states set" ("S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h")
  where "S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h = {s . \<exists> w \<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w = s}"

definition (in det_G_aut)
  reachable_trans :: "'states \<Rightarrow> 'alpha \<Rightarrow> 'states" ("\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h")
  where "\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h s a = (\<lambda>(s', a') \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A. \<delta> s' a') (s, a)"

definition (in det_G_aut)
  reachable_action :: "'grp \<Rightarrow> 'states \<Rightarrow> 'states" ("\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h")
  where "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g s = (\<lambda>(g', s') \<in> carrier G \<times> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h. \<psi> g' s') (g, s)"

lemma (in det_G_aut) reachable_action_is_restict:
  "\<And>g s. g \<in> carrier G \<Longrightarrow> s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g s = \<psi> g s"
  by (auto simp add: reachable_action_def reachable_states_def)

lemma (in det_G_aut_rec_lang) reach_det_aut_is_det_aut_rec_L:
  "reach_det_G_aut_rec_lang A S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h i (F \<inter> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h) \<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h G \<phi> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h L"
proof-
  have H_0: "(\<lambda>(x, y). \<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h x y) \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A \<rightarrow>\<^sub>E S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
  proof-
    have H1_0: "(\<lambda>(x, y). \<delta> x y) \<in> extensional (S \<times> A)"
      using is_aut.trans_func_ext
      by (simp add: PiE_iff)
    have H1_1: "(\<lambda>(s', a') \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A. \<delta> s' a') \<in> extensional (S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A)"
      using H1_0
      by simp
    have H1_2: "(\<lambda>(s', a')\<in>S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A. \<delta> s' a') = (\<lambda>(x, y). \<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h x y)"
      by (auto simp add: reachable_trans_def)
    show "(\<lambda>(x, y). \<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h x y) \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A \<rightarrow>\<^sub>E S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      apply (clarsimp simp add: PiE_iff)
      apply (rule conjI)
       apply (clarify)
      using reachable_trans_def
       apply (simp add: reachable_states_def)[1]
       apply (metis Cons_in_lists_iff append_Nil2 append_in_lists_conv is_aut.give_input_closed
          is_aut.init_state_is_a_state is_aut.trans_to_charact)
      using H1_1 H1_2
      by simp
  qed
  have H_1: "\<And>g. g \<in> carrier G \<Longrightarrow>
    (\<And>s. \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g s = (if s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h then case (g, s) of (x, xa) \<Rightarrow> \<psi> x xa else undefined)) \<Longrightarrow>
    bij_betw (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
  proof-
    fix g
    assume
      A1_0: "g \<in> carrier G" and
      A1_1: "(\<And>s. \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g s =
        (if s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
        then case (g, s) of (x, xa) \<Rightarrow> \<psi> x xa
        else undefined))" 
    have H1_0: "\<And>r. r \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g) r \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      using A1_0
      apply (clarsimp simp add: reachable_states_def reachable_action_def)
      apply (rule meta_mp[of "\<And>w. w \<in> A\<^sup>\<star> \<Longrightarrow> ((\<phi>\<^sup>\<star>) g w) \<in> A\<^sup>\<star>"])
      using action_on_input[where g = g]
       apply (metis in_listsI) 
      by (metis alt_group_act_is_grp_act group_action.element_image labels_a_G_set.lists_a_Gset)
    have H1_1: "\<And>f T U. bij_betw f T T \<Longrightarrow> f ` U = U \<Longrightarrow> U \<subseteq> T \<Longrightarrow> bij_betw (restrict f U) U U"
      apply (clarsimp simp add: bij_betw_def inj_on_def image_def)
      by (meson in_mono)
    have H1_2: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g = restrict (\<psi> g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      using reachable_action_def A1_0
      by (auto simp add: restrict_def)
    have H1_3: "bij_betw (\<psi> g) S S \<Longrightarrow> (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g) ` S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h = S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
      \<Longrightarrow> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<subseteq> S \<Longrightarrow> bij_betw (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      by (metis H1_2 bij_betw_imp_inj_on inj_on_imp_bij_betw inj_on_restrict_eq inj_on_subset)
    have H1_4: "\<And>w s. s = (\<delta>\<^sup>\<star>) i w \<Longrightarrow>
         \<forall>x\<in>set w. x \<in> A \<Longrightarrow>
         \<exists>x. (\<exists>w\<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w = x) \<and> (\<delta>\<^sup>\<star>) i w = \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g x"
    proof-
      fix w s
      assume
        A2_0: "\<forall>x\<in>set w. x \<in> A" and
        A2_1: "s = (\<delta>\<^sup>\<star>) i w"
      have H2_0: "(inv \<^bsub>G\<^esub> g) \<in> carrier G"
        apply (rule meta_mp[of "group G"])
        using A1_0
         apply simp
        using det_G_aut_rec_lang_axioms
        by (auto simp add: det_G_aut_rec_lang_def
            det_aut_rec_lang_axioms_def det_G_aut_def group_action_def group_hom_def)
      have H2_1: "\<psi> (inv \<^bsub>G\<^esub> g) s = (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w)"
        apply (simp del: GMN_simps add: A2_1)
        apply (rule action_on_input[where g = "(inv \<^bsub>G\<^esub> g)" and w = w]) 
        using H2_0 A2_0
        by auto
      have H2_2: "((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w) \<in> A\<^sup>\<star>"
        using A2_0 H2_0 det_G_aut_rec_lang_axioms
        apply (clarsimp)
        using labels_a_G_set.surj_prop list.set_map
        by fastforce
      have H2_3: "\<exists>w\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w = \<psi> (inv \<^bsub>G\<^esub> g) s" 
        by (metis H2_1 H2_2)
      from H2_3 have H2_4: "\<psi> (inv \<^bsub>G\<^esub> g) s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
        by (simp add: reachable_states_def)
      have H2_5: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g (\<psi> (inv \<^bsub>G\<^esub> g) s) = \<psi> g (\<psi> (inv \<^bsub>G\<^esub> g) s)"
        apply (rule reachable_action_is_restict)
        using A1_0 H2_4
        by simp+
      have H2_6: "(\<delta>\<^sup>\<star>) i w = \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g (\<psi> (inv \<^bsub>G\<^esub> g) s)"
        apply (simp add: H2_5 A2_1) 
        by (metis A1_0 A2_0 in_listsI A2_1 H2_5 is_aut.give_input_closed
            is_aut.init_state_is_a_state states_a_G_set.bij_prop1 states_a_G_set.orbit_sym_aux)
      show " \<exists>x. (\<exists>w\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w = x) \<and> (\<delta>\<^sup>\<star>) i w = \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g x"
        using H2_3 H2_6
        by blast
    qed
    show "bij_betw (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      apply (rule H1_3)
        apply (simp add: A1_0 bij_betw_def states_a_G_set.inj_prop states_a_G_set.surj_prop)
       apply (clarsimp simp add: image_def H1_0)
       apply (rule subset_antisym; simp add: Set.subset_eq; clarify)
      using H1_0 
        apply auto[1]
      subgoal for s
        apply (clarsimp simp add: reachable_states_def)
        by (simp add: H1_4)
      apply (simp add: reachable_states_def Set.subset_eq; rule allI; rule impI)
      using is_aut.give_input_closed is_aut.init_state_is_a_state
      by auto
  qed
  have H_2: "group G"
    using det_G_aut_rec_lang_axioms
    by (auto simp add: det_G_aut_rec_lang_def det_G_aut_def group_action_def
        group_hom_def)
  have H_3: "\<And>g. g \<in> carrier G \<Longrightarrow> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g \<in> carrier (BijGroup S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h)"
    subgoal for g
      using reachable_action_def[where g = g]
      apply (simp add: BijGroup_def Bij_def extensional_def)
      by (simp add: H_1)
    done
  have H_4: "\<And>x y. x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (x \<otimes>\<^bsub>G\<^esub> y) = \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h x \<otimes>\<^bsub>BijGroup S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^esub>
                                                                           \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h y"
  proof -
    fix g h
    assume
      A1_0: "g \<in> carrier G" and
      A1_1: "h \<in> carrier G"
    have H1_0: "\<And>g . g \<in> carrier G \<Longrightarrow> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g = restrict (\<psi> g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      using reachable_action_def
      by (auto simp add: restrict_def)
    from H1_0 have H1_1: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (g \<otimes>\<^bsub>G\<^esub> h) = restrict (\<psi> (g \<otimes>\<^bsub>G\<^esub> h)) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      by (simp add: A1_0 A1_1 H_2 group.subgroup_self subgroup.m_closed)
    have H1_2: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g \<otimes>\<^bsub>BijGroup S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^esub> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h h = 
    (restrict (\<psi> g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h) \<otimes>\<^bsub>BijGroup S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^esub>
    (restrict (\<psi> h) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h)"
      using A1_0 A1_1 H1_0
      by simp
    have H1_3: "\<And>g. g \<in> carrier G \<Longrightarrow> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g \<in> carrier (BijGroup S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h)"
      by (simp add: H_3)
    have H1_4: "\<And>x y. x\<in>carrier G \<Longrightarrow> y\<in>carrier G \<Longrightarrow> \<psi> (x \<otimes>\<^bsub>G\<^esub> y) = \<psi> x \<otimes>\<^bsub>BijGroup S\<^esub> \<psi> y"
      using det_G_aut_axioms
      by (simp add: det_G_aut_def group_action_def group_hom_def group_hom_axioms_def hom_def)
    hence H1_5: "\<psi> (g \<otimes>\<^bsub>G\<^esub> h) = \<psi> g \<otimes>\<^bsub>BijGroup S\<^esub> \<psi> h"
      using A1_0 A1_1
      by simp
    have H1_6: "(\<lambda>x. if x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
                   then if (if x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
                            then \<psi> h x
                            else undefined) \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
                        then \<psi> g (if x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
                                  then \<psi> h x
                                  else undefined)
                        else undefined
                   else undefined) =
              (\<lambda>x. if x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
                   then \<psi> g (\<psi> h x) 
                   else undefined)" 
      apply (rule meta_mp[of "\<And>x. x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> (\<psi> h x) \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"])
      using H1_3[where g1 = h] A1_1 H1_0
      by (auto simp add: A1_1 BijGroup_def Bij_def bij_betw_def) 
    have H1_7: "... = (\<lambda>x. if x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h
                          then if x \<in> S
                               then \<psi> g (\<psi> h x)
                               else undefined
                          else undefined)"
      apply (clarsimp simp add: reachable_states_def) 
      by (metis is_aut.give_input_closed is_aut.init_state_is_a_state)
    have H1_8: "(restrict (\<psi> g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h) \<otimes>\<^bsub>BijGroup S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^esub> (restrict (\<psi> h) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h) =
     restrict (\<psi> (g \<otimes>\<^bsub>G\<^esub> h)) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      apply (rule meta_mp[of "\<And>g. g \<in> carrier G \<Longrightarrow> restrict (\<psi> g) S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<in> Bij S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<and>
      \<psi> g \<in> Bij S"])
       apply (clarsimp simp add: H1_5 BijGroup_def; intro conjI; intro impI)
      subgoal
        using A1_0 A1_1
        apply (clarsimp simp add: compose_def restrict_def)
        by (simp add: H1_6 H1_7) 
       apply (simp add: A1_0 A1_1)+
      subgoal for g
        using H1_3[where g1 = g] H1_0[of g]
        by (simp add: BijGroup_def states_a_G_set.bij_prop0)
      done
    show "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (g \<otimes>\<^bsub>G\<^esub> h) =
      \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g \<otimes>\<^bsub>BijGroup S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^esub> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h h"
      by (simp add: H1_1 H1_2 H1_8)
  qed
  have H_5: "\<And>w' w g. g \<in> carrier G \<Longrightarrow>
          (\<delta>\<^sup>\<star>) i w \<in> F \<Longrightarrow> \<forall>x\<in>set w. x \<in> A \<Longrightarrow> (\<delta>\<^sup>\<star>) i w' = (\<delta>\<^sup>\<star>) i w \<Longrightarrow> \<forall>x\<in>set w'. x \<in> A \<Longrightarrow>
          \<exists>w'\<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w' = \<psi> g ((\<delta>\<^sup>\<star>) i w)"
  proof -
    fix w' w g
    assume
      A1_0: "g \<in> carrier G" and
      A1_1: "(\<delta>\<^sup>\<star>) i w \<in> F" and
      A1_2: "\<forall>x\<in>set w. x \<in> A" and
      A1_3: "(\<delta>\<^sup>\<star>) i w' = (\<delta>\<^sup>\<star>) i w" and
      A1_4: "\<forall>x\<in>set w. x \<in> A"
    from A1_1 A1_2 have H1_0: "((\<delta>\<^sup>\<star>) i w) \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      using reachable_states_def
      by auto
    have H1_1: "\<psi> g ((\<delta>\<^sup>\<star>) i w) = ((\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w))"
      using give_input_eq_var
      apply (clarsimp simp add: eq_var_func_def eq_var_func_axioms_def simp del: GMN_simps)
      using A1_0 A1_2 action_on_input
      by blast
    have H1_2: "(\<phi>\<^sup>\<star>) g w \<in> A\<^sup>\<star>"
      using A1_0 A1_2
      by (metis in_listsI alt_group_act_is_grp_act group_action.element_image
          labels_a_G_set.lists_a_Gset)
    show "\<exists>wa\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i wa = \<psi> g ((\<delta>\<^sup>\<star>) i w)"
      by (metis H1_1 H1_2)
  qed
  have H_6: "alt_grp_act G S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
    apply (clarsimp simp add: group_action_def group_hom_def group_hom_axioms_def hom_def)
    apply (intro conjI)
       apply (simp add: H_2)
    subgoal 
      by (simp add: group_BijGroup)
     apply clarify
     apply (simp add: H_3)
    by (simp add: H_4)
  have H_7: "\<And>g w. g \<in> carrier G \<Longrightarrow> (\<delta>\<^sup>\<star>) i w \<in> F \<Longrightarrow> \<forall>x\<in>set w. x \<in> A \<Longrightarrow>
            \<exists>x. x \<in> F \<and> (\<exists>w\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w = x) \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g x"
  proof-
    fix g w
    assume
      A1_0: "g \<in> carrier G" and
      A1_1: "(\<delta>\<^sup>\<star>) i w \<in> F" and
      A1_2: "\<forall>x\<in>set w. x \<in> A"
    have H1_0: "(inv \<^bsub>G\<^esub> g) \<in> carrier G" 
      by (meson A1_0 group.inv_closed group_hom.axioms(1) labels_a_G_set.group_hom)
    have H1_1: "((\<delta>\<^sup>\<star>) i w) \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      using A1_1 A1_2 reachable_states_def
      by auto
    have H1_2: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w) = \<psi> (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w)"
      apply (rule reachable_action_is_restict)
      using H1_0 H1_1
      by auto
    have H1_3: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g (\<psi> (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w)) = ((\<delta>\<^sup>\<star>) i w)" 
      by (smt (verit) A1_0 H1_1 H_6 H1_2
          alt_group_act_is_grp_act group_action.bij_prop1 group_action.orbit_sym_aux)
    have H1_4: "\<psi> (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w) \<in> F"
      using A1_1 H1_0 accepting_is_eq_var.is_equivar
      by blast
    have H1_5: "\<psi> (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w) \<in> F \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g (\<psi> (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w))"
      using H1_4 H1_3 A1_0 A1_1 H1_0 H1_1 reachable_action_is_restict
      by (metis H_6 alt_group_act_is_grp_act
          group_action.element_image)
    have H1_6: "\<psi> (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w) = ((\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w))"
      using give_input_eq_var
      apply (clarsimp simp add: eq_var_func_def eq_var_func_axioms_def simp del: GMN_simps)
      using A1_2 H1_0 action_on_input
      by blast
    have H1_7: "(\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w \<in> A\<^sup>\<star>"
      by (metis A1_2 in_listsI H1_0 alt_group_act_is_grp_act group_action.element_image
          labels_a_G_set.lists_a_Gset)
    thus "\<exists>x. x \<in> F \<and> (\<exists>w\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w = x) \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g x"
      using H1_5 H1_6 H1_7
      by metis
  qed
  have H_8: "\<And>r a g . r \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> a \<in> A \<Longrightarrow> \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g r \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<and> \<phi> g a \<in> A \<Longrightarrow> g \<in> carrier G \<Longrightarrow>
            \<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g r) (\<phi> g a) = \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h r a)"
  proof-
    fix r a g
    assume
      A1_0: "r \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h" and
      A1_1: "a \<in> A" and
      A1_2: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g r \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<and> \<phi> g a \<in> A" and
      A1_3: "g \<in> carrier G"
    have H1_0: "r \<in> S \<and> \<psi> g r \<in> S"
      apply (rule conjI)
      subgoal
        using A1_0
        apply (clarsimp simp add: reachable_states_def) 
        by (simp add: in_listsI is_aut.give_input_closed is_aut.init_state_is_a_state)
      using \<open>r \<in> S\<close> A1_3 states_a_G_set.element_image
      by blast
    have H1_1: "\<And>a b g . a \<in> S \<and> b \<in> A \<Longrightarrow> g \<in> carrier G \<Longrightarrow>
        (if \<psi> g a \<in> S \<and> \<phi> g b \<in> A then \<delta> (\<psi> g a) (\<phi> g b) else undefined) =
        \<psi> g (\<delta> a b)"
      using det_G_aut_axioms A1_0 A1_1 A1_3
      apply (clarsimp simp add: det_G_aut_def eq_var_func_def eq_var_func_axioms_def) 
      by presburger+
    hence H1_2: "\<psi> g (\<delta> r a) = (\<delta> (\<psi> g r) (\<phi> g a))"
      using H1_1[where a1 = r and b1 = a and g1 = g] H1_0 A1_1 A1_2 A1_3
      by simp
    have H1_3: "\<And>a w. a \<in> A \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> \<exists>w'\<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w' = \<delta> ((\<delta>\<^sup>\<star>) i w) a"
    proof -(*(clarsimp simp add: reachable_states_def)*)
      fix a w
      assume
        A2_0: "a \<in> A" and
        A2_1: "w \<in> A\<^sup>\<star>" 
      have H2_0: "(w @ [a]) \<in> A\<^sup>\<star> \<and> (w @ [a]) \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i (w @ [a]) = \<delta> ((\<delta>\<^sup>\<star>) i w) a"
        by (simp add: is_aut.give_input_closed is_aut.trans_to_charact
            is_aut.init_state_is_a_state)
      show "\<exists>w'\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w' = \<delta> ((\<delta>\<^sup>\<star>) i w) a"
        using H2_0
        apply clarsimp 
        by (metis A2_0 A2_1 append_in_lists_conv lists.Cons lists.Nil)
    qed
    have H1_4: "\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h r a) = \<psi> g (\<delta> r a)"
      apply (clarsimp simp add: reachable_action_def reachable_trans_def)
      using A1_0 A1_1 A1_3 H1_0 H1_3 
      using reachable_states_def by fastforce
    have H1_5:"\<psi> g r = \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g r"
      using A1_0 A1_3
      by (auto simp add: reachable_action_def)
    hence H1_6: "\<psi> g r \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h"
      using A1_2
      by simp
    have H1_7: "\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g r) (\<phi> g a) = \<delta> (\<psi> g r) (\<phi> g a)"
      using A1_0 A1_1 A1_2 A1_3
      by (auto simp del: simp add:reachable_trans_def reachable_action_def )
    show "\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g r) (\<phi> g a) = \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h r a)"
      using H1_2 H1_4 H1_7
      by auto
  qed
  have H_9: "\<And>a w s. \<lbrakk>(\<And>s. s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> (\<delta>\<^sup>\<star>) s w = (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) s w);
       a \<in> A \<and> (\<forall>x\<in>set w. x \<in> A); s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<rbrakk> \<Longrightarrow> (\<delta>\<^sup>\<star>) (\<delta> s a) w = (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h s a) w"
  proof-
    fix a w s
    assume 
      A1_IH: "(\<And>s. s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> (\<delta>\<^sup>\<star>) s w = (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) s w)" and
      A1_0: "a \<in> A \<and> (\<forall>x\<in>set w. x \<in> A)" and
      A1_1: "s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h" 
    have H1_0: "\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h s a = \<delta> s a"
      using A1_1
      apply (clarsimp simp add: reachable_trans_def)
      apply (rule meta_mp[of "det_aut A S i F \<delta>"])
      using det_aut.trans_func_ext[where labels = A and states = S and
          init_state = i and fin_states = F and trans_func = \<delta>]
       apply (simp add: extensional_def)
      by (auto simp add: A1_0)
    show "(\<delta>\<^sup>\<star>) (\<delta> s a) w = (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h s a) w"
      apply (simp add: H1_0)
      apply (rule A1_IH[where s1 = "\<delta> s a"])
      using A1_0 A1_1
      apply (simp add: reachable_states_def)
      by (metis Cons_in_lists_iff append_Nil2 append_in_lists_conv is_aut.give_input_closed
          is_aut.init_state_is_a_state is_aut.trans_to_charact)
  qed
  show ?thesis
    apply (clarsimp simp del: GMN_simps simp add: reach_det_G_aut_rec_lang_def
        det_G_aut_rec_lang_def det_G_aut_def det_aut_def)
    apply (intro conjI)
    subgoal
      apply (simp add: reachable_states_def) 
      by (meson give_input.simps(1) lists.Nil)
           apply (simp add: H_0)
    using labels_a_G_set.alt_grp_act_axioms
          apply (auto)[1]
         apply (rule H_6)
    subgoal
      apply (clarsimp simp add: eq_var_subset_def eq_var_subset_axioms_def)
      apply (rule conjI)
      using H_6
       apply (auto)[1]
      apply (simp del: add: reachable_states_def)[1] 
      apply (clarify; rule subset_antisym; simp add: Set.subset_eq; clarify)
       apply (rule conjI)
      subgoal for g _ w
        apply (clarsimp simp add: reachable_action_def reachable_states_def) 
        using accepting_is_eq_var.is_equivar
        by blast
      subgoal for g _ w
        apply (clarsimp simp add: reachable_action_def reachable_states_def)
        apply (rule conjI; clarify)
         apply (auto)[2]
        by (simp add: H_5)
      apply (clarsimp simp add: reachable_states_def Int_def reachable_action_def ) 
      apply (clarsimp simp add: image_def)
      by (simp add: H_7)
    subgoal
      apply (clarsimp simp add: eq_var_subset_def)
      apply (rule conjI)
      using H_6
       apply (auto)[1]
      apply (clarsimp simp add: eq_var_subset_axioms_def) 
      apply (simp add: \<open>i \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<close>)
      apply (simp add: reachable_action_def)
      using \<open>i \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<close> init_is_eq_var.is_equivar
      by fastforce
    subgoal
      apply (clarsimp simp add: eq_var_func_def eq_var_func_axioms_def) 
      apply (intro conjI)
      using H_6 alt_grp_act.axioms
        labels_a_G_set.group_action_axioms prod_group_act labels_a_G_set.alt_grp_act_axioms
         apply blast
      using H_6
        apply (auto)[1]
       apply (rule funcsetI; clarsimp)
      subgoal for s a
        apply (clarsimp simp add: reachable_states_def reachable_trans_def)
        by (metis Cons_in_lists_iff append_Nil2 append_in_lists_conv in_listsI
            is_aut.give_input_closed is_aut.init_state_is_a_state is_aut.trans_to_charact)
      apply (intro allI; clarify; rule conjI; intro impI)
       apply (simp add: H_8)
      using G_set_equiv H_6 eq_var_subset.is_equivar
        labels_a_G_set.element_image
      by fastforce
     apply (rule meta_mp[of "\<And>w s. w \<in> A\<^sup>\<star> \<Longrightarrow> s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> (\<delta>\<^sup>\<star>) s w = (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) s w"])
    subgoal
      using det_G_aut_rec_lang_axioms
      apply (clarsimp simp add: det_aut_rec_lang_axioms_def det_aut_rec_lang_def
          det_G_aut_rec_lang_def det_aut_def)
      apply (intro conjI)
      using \<open>i \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<close> 
        apply blast 
      using H_0
       apply blast
      by (metis (mono_tags, lifting) \<open>i \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<close> mem_Collect_eq reachable_states_def)
    subgoal for w s
      apply (induction w arbitrary: s)
       apply (clarsimp)
      apply (simp add: in_lists_conv_set)
      by (simp add: H_9)
    apply (clarsimp simp add: reach_det_G_aut_def det_G_aut_def det_aut_def)
    apply (intro conjI)
           apply (simp add: \<open>i \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<close>)
          apply (simp add: H_0)
         apply (simp add: labels_a_G_set.group_action_axioms)
    using \<open>alt_grp_act G S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<close>
        apply (auto)[1]
       apply (simp add: \<open>eq_var_subset G S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (F \<inter> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h)\<close>)
      apply (simp add: \<open>eq_var_subset G S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h {i}\<close>)
    using \<open>eq_var_func G (S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A) (\<lambda>g\<in>carrier G. \<lambda>(s, a)\<in>S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A. (\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g s, \<phi> g a))
  S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h (\<lambda>(x, y)\<in>S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<times> A. \<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h x y)\<close>
     apply blast
    apply (simp add: reach_det_aut_axioms_def reach_det_aut_def reachable_states_def)
    apply (rule meta_mp[of "\<And>s input. s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow> input \<in> A\<^sup>\<star> \<Longrightarrow>
   (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) s input = (\<delta>\<^sup>\<star>) s input"])
    using \<open>i \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<close>
     apply (metis (no_types, lifting) \<open>(\<And>w s. \<lbrakk>w \<in> A\<^sup>\<star>; s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<rbrakk> \<Longrightarrow>
    (\<delta>\<^sup>\<star>) s w = (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) s w) \<Longrightarrow> det_aut_rec_lang A S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h i (F \<inter> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h) \<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h L\<close> det_aut_rec_lang_def
        reachable_states_def)
    by (simp add: \<open>\<And>w s. \<lbrakk>w \<in> A\<^sup>\<star>; s \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<rbrakk> \<Longrightarrow> (\<delta>\<^sup>\<star>) s w = (\<delta>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h\<^sup>\<star>) s w\<close>)
qed

subsection \<open>
Syntactic Automaton
\<close>
context language begin

definition
  rel_MN :: "('alpha list \<times> 'alpha list) set" ("\<equiv>\<^sub>M\<^sub>N")
  where "rel_MN = {(w, w') \<in> (A\<^sup>\<star>)\<times>(A\<^sup>\<star>). (\<forall>v \<in> A\<^sup>\<star>. (w @ v) \<in> L \<longleftrightarrow> (w' @ v) \<in> L)}"

lemma MN_rel_equival:
  "equiv (A\<^sup>\<star>) rel_MN"
  by (auto simp add: rel_MN_def equiv_def refl_on_def sym_def trans_def)

abbreviation
  MN_equiv
  where "MN_equiv \<equiv> A\<^sup>\<star> // rel_MN" 

definition
  alt_natural_map_MN :: "'alpha list \<Rightarrow> 'alpha list set " ("[_]\<^sub>M\<^sub>N")
  where "[w]\<^sub>M\<^sub>N = rel_MN `` {w}"

definition
  MN_trans_func :: "('alpha list set) \<Rightarrow> 'alpha \<Rightarrow> 'alpha list set" ("\<delta>\<^sub>M\<^sub>N")
  where "MN_trans_func W' a' =
     (\<lambda>(W,a) \<in> MN_equiv \<times> A. rel_MN `` {(SOME w. w \<in> W) @ [a]}) (W', a')"

abbreviation
  MN_init_state
  where "MN_init_state \<equiv> [Nil::'alpha list]\<^sub>M\<^sub>N"

abbreviation
  MN_fin_states
  where "MN_fin_states \<equiv> {v. \<exists>w\<in>L. v = [w]\<^sub>M\<^sub>N}"

lemmas 
  alt_natural_map_MN_def [simp, GMN_simps]
  MN_trans_func_def [simp, GMN_simps]
end

context G_lang begin
adhoc_overloading
  star induced_star_map

lemma MN_quot_act_wd:
  "w' \<in> [w]\<^sub>M\<^sub>N \<Longrightarrow> \<forall>g \<in> carrier G. (w' \<odot> \<^bsub>\<phi>\<^sup>\<star>\<^esub> g) \<in> [w \<odot> \<^bsub>\<phi>\<^sup>\<star>\<^esub> g]\<^sub>M\<^sub>N"
proof-
  assume A_0: "w' \<in> [w]\<^sub>M\<^sub>N"
  have H_0: "\<And>g. \<lbrakk>(w, w') \<in> \<equiv>\<^sub>M\<^sub>N; g \<in> carrier G; group_hom G (BijGroup A) \<phi>;
  group_hom G (BijGroup (A\<^sup>\<star>)) (\<lambda>g\<in>carrier G. restrict (map (\<phi> g)) (A\<^sup>\<star>)); L \<subseteq> A\<^sup>\<star>;
  \<forall>g\<in>carrier G. map (\<phi> g) ` (L \<inter> A\<^sup>\<star>) \<union> (\<lambda>x. undefined) ` (L \<inter> {x. x \<notin> A\<^sup>\<star>}) = L;
    \<forall>x\<in>set w. x \<in> A; w' \<in> A\<^sup>\<star>\<rbrakk> \<Longrightarrow> (map (\<phi> g) w, map (\<phi> g) w') \<in> \<equiv>\<^sub>M\<^sub>N"
  proof-
    fix g
    assume
      A1_0: "(w, w') \<in> \<equiv>\<^sub>M\<^sub>N" and
      A1_1: "g \<in> carrier G" and
      A1_2: "group_hom G (BijGroup A) \<phi>" and
      A1_3: "group_hom G (BijGroup (lists A)) (\<lambda>g\<in>carrier G. restrict (map (\<phi> g)) (lists A))" and
      A1_4: "L \<subseteq> lists A" and
      A1_5: "\<forall>g\<in>carrier G.
           map (\<phi> g) ` (L \<inter> lists A) \<union> (\<lambda>x. undefined) ` (L \<inter> {x. x \<notin> lists A}) = L" and
      A1_6: "\<forall>x\<in>set w. x \<in> A" and
      A1_7: "w' \<in> A\<^sup>\<star>"
    have H1_0: "\<And>v w w'. \<lbrakk>g \<in> carrier G; group_hom G (BijGroup A) \<phi>;
    group_hom G (BijGroup (lists A)) (\<lambda>g\<in>carrier G. restrict (map (\<phi> g)) (lists A));
    L \<subseteq> lists A; \<forall>g\<in>carrier G.
    {y. \<exists>x\<in>L \<inter> lists A. y = map (\<phi> g) x} \<union> {y. y = undefined \<and> (\<exists>x. x \<in> L \<and> x \<notin> lists A)} = L;
    \<forall>x\<in>set w. x \<in> A; \<forall>v\<in>lists A. (w @ v \<in> L) = (w' @ v \<in> L); \<forall>x\<in>set w'. x \<in> A; \<forall>x\<in>set v. x \<in> A;
    map (\<phi> g) w @ v \<in> L\<rbrakk> \<Longrightarrow> map (\<phi> g) w' @ v \<in> L"
    proof -
      fix v w w'
      assume
        A2_0: "g \<in> carrier G" and
        A2_1: "L \<subseteq> A\<^sup>\<star>" and
        A2_2: "group_hom G (BijGroup A) \<phi>" and
        A2_3: "group_hom G (BijGroup (A\<^sup>\<star>)) (\<lambda>g\<in>carrier G. restrict (map (\<phi> g)) (A\<^sup>\<star>))" and
        A2_4: "\<forall>g\<in>carrier G. {y. \<exists>x\<in>L \<inter> A\<^sup>\<star>. y = map (\<phi> g) x} \<union>
        {y. y = undefined \<and> (\<exists>x. x \<in> L \<and> x \<notin> A\<^sup>\<star>)} = L" and
        A2_5: "\<forall>x\<in>set w. x \<in> A" and
        A2_6: "\<forall>x\<in>set w'. x \<in> A" and
        A2_7: "\<forall>v\<in>A\<^sup>\<star>. (w @ v \<in> L) = (w' @ v \<in> L)" and
        A2_8: "\<forall>x\<in>set v. x \<in> A" and
        A2_9: "map (\<phi> g) w @ v \<in> L" 
      have H2_0: "\<forall>g\<in>carrier G. {y. \<exists>x\<in>L \<inter> A\<^sup>\<star>. y = map (\<phi> g) x} = L"
        using A2_1 A2_4 subset_eq
        by (smt (verit, ccfv_SIG) Collect_mono_iff sup.orderE)
      hence H2_1: "\<forall>g\<in>carrier G. {y. \<exists>x\<in>L. y = map (\<phi> g) x} = L"
        using A2_1 inf.absorb_iff1
        by (smt (verit, ccfv_SIG) Collect_cong)
      hence H2_2: "\<forall>g\<in>carrier G.\<forall>x\<in>L. map (\<phi> g) x \<in> L"
        by auto
      from A2_2 have H2_3: "\<forall>h\<in>carrier G. \<forall>a\<in>A. (\<phi> h) a \<in> A"
        by (auto simp add: group_hom_def BijGroup_def group_hom_axioms_def hom_def Bij_def
            bij_betw_def)
      from A2_8 have H2_4: "v \<in> lists A"
        by (simp add: in_listsI)
      hence H2_5: "\<forall>h\<in>carrier G. map (\<phi> h) v \<in> lists A"
        using H2_3
        by fastforce
      hence H2_6: "\<forall>h\<in>carrier G. (w @ (map (\<phi> h) v) \<in> L) = (w' @ (map (\<phi> h) v) \<in> L)"
        using A2_7
        by force
      hence H2_7: "(w @ (map (\<phi> (inv\<^bsub>G\<^esub> g)) v) \<in> L) = (w' @ (map (\<phi> (inv\<^bsub>G\<^esub> g)) v) \<in> L)"
        using A2_0
        by (meson A2_7 A2_1 append_in_lists_conv in_mono)
      have "(map (\<phi> g) w) \<in> (A\<^sup>\<star>)"
        using A2_0 A2_2 A2_5 H2_3
        by (auto simp add: group_hom_def group_hom_axioms_def hom_def BijGroup_def Bij_def
            bij_betw_def)
      hence H2_8: "\<forall>w\<in>A\<^sup>\<star>. \<forall>g\<in>carrier G. map (\<phi> (inv\<^bsub>G\<^esub> g)) ((map (\<phi> g) w) @ v) =
      w @ (map (\<phi> (inv\<^bsub>G\<^esub> g)) v)"
        using act_maps_n_distrib triv_act_map A2_0 A2_2 A2_3 H2_4
        apply (clarsimp)
        by (smt (verit, del_insts) comp_apply group_action.intro group_action.orbit_sym_aux map_idI)
      have H2_9: "map (\<phi> (inv\<^bsub>G\<^esub> g)) ((map (\<phi> g) w) @ v) \<in> L"
        using A2_9 H2_1 H2_2 A2_1
        apply clarsimp
        by (metis A2_0 A2_2 group.inv_closed group_hom.axioms(1) list.map_comp map_append)
      hence H2_10: "w @ (map (\<phi> (inv\<^bsub>G\<^esub> g)) v) \<in> L"
        using H2_8 A2_0
        by (auto simp add: A2_5 in_listsI)
      hence H2_11: "w' @ (map (\<phi> (inv\<^bsub>G\<^esub> g)) v) \<in> L"
        using H2_7
        by simp
      hence H2_12: "map (\<phi> (inv\<^bsub>G\<^esub> g)) ((map (\<phi> g) w') @ v) \<in> L"
        using A2_0 H2_8 A2_1 subsetD
        by (metis append_in_lists_conv)
      have H2_13: "\<forall>g\<in>carrier G. restrict (map (\<phi> g)) (A\<^sup>\<star>) \<in> Bij (A\<^sup>\<star>)"
        using alt_grp_act.lists_a_Gset[where G = "G" and X = "A" and \<phi> = "\<phi>"] A1_3 
        by (auto simp add: group_action_def
            group_hom_def group_hom_axioms_def Pi_def hom_def BijGroup_def)
      have H2_14: "\<forall>g\<in>carrier G. restrict (map (\<phi> g)) L ` L = L"
        using H2_2
        apply (clarsimp simp add: Set.image_def)
        using H2_1
        by blast
      have H2_15: "map (\<phi> g) w' \<in> lists A"
        using A2_0 A2_1 H2_13 H2_2 
        by (metis H2_11 append_in_lists_conv image_eqI lists_image subset_eq surj_prop)
      have H2_16: "inv\<^bsub>G\<^esub> g \<in> carrier G" 
        by (metis A2_0 A2_2 group.inv_closed group_hom.axioms(1))
      thus "map (\<phi> g) w' @ v \<in> L" 
        using A2_0 A2_1 A2_2 H2_4 H2_12 H2_13 H2_14 H2_15 H2_16 group.inv_closed group_hom.axioms(1)
          alt_grp_act.lists_a_Gset[where G = "G" and X = "A" and \<phi> = "\<phi>"] 
          pre_image_lemma[where S = "L" and T = "A\<^sup>\<star>" and f = "map (\<phi> (inv\<^bsub>G\<^esub> g))" and
            x = "((map (\<phi> g) w') @ v)"]
        apply (clarsimp simp add: group_action_def) 
        by (smt (verit, best) A2_1 FuncSet.restrict_restrict H2_14 H2_15 H2_16 H2_4
            append_in_lists_conv inf.absorb_iff2 map_append map_map pre_image_lemma restrict_apply'
            restrict_apply') 
    qed
    show "(map (\<phi> g) w, map (\<phi> g) w') \<in> \<equiv>\<^sub>M\<^sub>N"
      apply (clarsimp simp add: rel_MN_def Set.image_def)
      apply (intro conjI)
      using A1_1 A1_6 group_action.surj_prop group_action_axioms
        apply fastforce
      using A1_1 A1_7 image_iff surj_prop
       apply fastforce
      apply (clarify; rule iffI)
      subgoal for v
        apply (rule H1_0[where v1 ="v" and w1 = "w" and w'1 = "w'"])
        using A1_0 A1_1 A1_2 A1_3 A1_4 A1_5 A1_6 A1_7
        by (auto simp add: rel_MN_def Set.image_def)
      apply (rule H1_0[where w1 = "w'" and w'1 = "w"])
      using A1_0 A1_1 A1_2 A1_3 A1_4 A1_5 A1_6 A1_7
      by (auto simp add: rel_MN_def Set.image_def)
  qed
  show ?thesis
    using G_lang_axioms A_0
    apply (clarsimp simp add: G_lang_def G_lang_axioms_def eq_var_subset_def
        eq_var_subset_axioms_def alt_grp_act_def group_action_def)
    apply (intro conjI; clarify)
     apply (rule conjI; rule impI)
      apply (simp add: H_0)
    by (auto simp add: rel_MN_def)
qed

text \<open>
The following lemma corresponds to lemma 3.4 from \cite{bojanczyk2014automata}:
\<close>

lemma MN_rel_eq_var:
  "eq_var_rel G (A\<^sup>\<star>) (\<phi>\<^sup>\<star>) \<equiv>\<^sub>M\<^sub>N"
  apply (clarsimp simp add: eq_var_rel_def alt_grp_act_def eq_var_rel_axioms_def)
  apply (intro conjI)
    apply (metis L_is_equivar alt_grp_act.axioms eq_var_subset.axioms(1) induced_star_map_def)
  using L_is_equivar
   apply (simp add: rel_MN_def eq_var_subset_def eq_var_subset_axioms_def)
   apply fastforce
  apply (clarify)
  apply (intro conjI; rule impI; rule conjI; rule impI)
     apply (simp add: in_lists_conv_set)
     apply (clarsimp simp add: rel_MN_def)
     apply (intro conjI)
       apply (clarsimp simp add: rel_MN_def)
  subgoal for w v g w'
    using L_is_equivar
    apply (clarsimp simp add: restrict_def eq_var_subset_def eq_var_subset_axioms_def)
    by (meson element_image)
      apply(metis image_mono in_listsI in_mono list.set_map lists_mono subset_code(1) surj_prop)
     apply (clarify; rule iffI)
  subgoal for w v g u
    using G_lang_axioms MN_quot_act_wd[where w = "w" and w'= "v"]
    by (auto simp add: rel_MN_def G_lang_def G_lang_axioms_def
        eq_var_subset_def eq_var_subset_axioms_def Set.subset_eq element_image) 
  subgoal for w v g u
    using G_lang_axioms MN_quot_act_wd[where w = "w" and w'= "v"]
    by (auto simp add: rel_MN_def G_lang_def G_lang_axioms_def
        eq_var_subset_def eq_var_subset_axioms_def Set.subset_eq element_image) 
  using G_lang_axioms MN_quot_act_wd
  by (auto simp add: rel_MN_def G_lang_def G_lang_axioms_def
      eq_var_subset_def eq_var_subset_axioms_def Set.subset_eq element_image)

lemma quot_act_wd_alt_notation:
  "w \<in> A\<^sup>\<star> \<Longrightarrow> g \<in> carrier G \<Longrightarrow> ([w]\<^sub>M\<^sub>N) \<odot>\<^bsub>[\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>\<^esub> g = ([w \<odot>\<^bsub>\<phi>\<^sup>\<star>\<^esub> g]\<^sub>M\<^sub>N)"
  using eq_var_rel.quot_act_wd[where G = G and \<phi> = "\<phi>\<^sup>\<star>" and X = "A\<^sup>\<star>" and R = "\<equiv>\<^sub>M\<^sub>N" and x = w
      and g = g]
  by (simp del: GMN_simps add: alt_natural_map_MN_def MN_rel_eq_var MN_rel_equival)

lemma MN_trans_func_characterization:
  "v \<in> (A\<^sup>\<star>) \<Longrightarrow> a \<in> A \<Longrightarrow> \<delta>\<^sub>M\<^sub>N [v]\<^sub>M\<^sub>N a = [v @ [a]]\<^sub>M\<^sub>N"
proof-
  assume
    A_0: "v \<in> (A\<^sup>\<star>)" and
    A_1: "a \<in> A"
  have H_0: "\<And>u. u \<in> [v]\<^sub>M\<^sub>N \<Longrightarrow> (u @ [a]) \<in> [v @ [a]]\<^sub>M\<^sub>N"
    by (auto simp add: rel_MN_def A_1 A_0)
  hence H_1: "(SOME w. (v, w) \<in> \<equiv>\<^sub>M\<^sub>N) \<in> [v]\<^sub>M\<^sub>N \<Longrightarrow> ((SOME w. (v, w) \<in> \<equiv>\<^sub>M\<^sub>N) @ [a]) \<in> [v @ [a]]\<^sub>M\<^sub>N"
    by auto
  from A_0 have "(v, v) \<in> \<equiv>\<^sub>M\<^sub>N \<and> v \<in> [v]\<^sub>M\<^sub>N"
    by (auto simp add: rel_MN_def)
  hence H_2: "(SOME w. (v, w) \<in> \<equiv>\<^sub>M\<^sub>N) \<in> [v]\<^sub>M\<^sub>N"
    apply (clarsimp simp add: rel_MN_def)
    apply (rule conjI)
     apply (smt (verit, ccfv_SIG) A_0 in_listsD verit_sko_ex_indirect)
    by (smt (verit, del_insts) A_0 in_listsI tfl_some)
  hence H_3: " ((SOME w. (v, w) \<in> \<equiv>\<^sub>M\<^sub>N) @ [a]) \<in> [v @ [a]]\<^sub>M\<^sub>N"
    using H_1
    by simp
  thus "\<delta>\<^sub>M\<^sub>N [v]\<^sub>M\<^sub>N a = [v @ [a]]\<^sub>M\<^sub>N"
    using A_0 A_1 MN_rel_equival
    apply (clarsimp simp add: equiv_def)
    apply (rule conjI; rule impI)
     apply (metis MN_rel_equival equiv_class_eq)
    by (simp add: A_0 quotientI)
qed

lemma MN_trans_eq_var_func :
  "eq_var_func G
 (MN_equiv \<times> A) (\<lambda>g\<in>carrier G. \<lambda>(W, a) \<in> (MN_equiv \<times> A). (([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g W, \<phi> g a))
  MN_equiv ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)
  (\<lambda>(w, a) \<in> MN_equiv \<times> A. \<delta>\<^sub>M\<^sub>N w a)"
proof-
  have H_0: "alt_grp_act G MN_equiv ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>)"
    using MN_rel_eq_var MN_rel_equival eq_var_rel.quot_act_is_grp_act 
      alt_group_act_is_grp_act restrict_apply
    by fastforce
  have H_1: "\<And>a b g.
       a \<in> MN_equiv \<Longrightarrow>
       b \<in> A \<Longrightarrow>
       (([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g a \<in> MN_equiv \<and> \<phi> g b \<in> A \<longrightarrow>
       g \<in> carrier G \<longrightarrow> \<delta>\<^sub>M\<^sub>N (([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g a) (\<phi> g b) = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g (\<delta>\<^sub>M\<^sub>N a b)) \<and>
       ((([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g a \<in> MN_equiv \<longrightarrow> \<phi> g b \<notin> A) \<longrightarrow>
        g \<in> carrier G \<longrightarrow> undefined = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g (\<delta>\<^sub>M\<^sub>N a b))"
  proof -
    fix C a g
    assume
      A1_0: "C \<in> MN_equiv" and
      A1_1: "a \<in> A"
    have H1_0: "g \<in> carrier G \<Longrightarrow> \<phi> g a \<in> A" 
      by (meson A1_1 element_image)
    from A1_0 obtain c where H1_c: "[c]\<^sub>M\<^sub>N = C \<and> c \<in> A\<^sup>\<star>"
      by (auto simp add: quotient_def) 
    have H1_1: "g \<in> carrier G \<Longrightarrow> \<delta>\<^sub>M\<^sub>N (([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C) (\<phi> g a) = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (\<delta>\<^sub>M\<^sub>N [c]\<^sub>M\<^sub>N a)"
    proof-
      assume 
        A2_0: "g \<in> carrier G" 
      have H2_0: "\<phi> g a \<in> A"
        using H1_0 A2_0
        by simp
      have H2_1: "(\<phi>\<^sup>\<star>) g \<in> Bij (A\<^sup>\<star>)" using G_lang_axioms lists_a_Gset A2_0
        apply (clarsimp simp add: G_lang_def G_lang_axioms_def group_action_def
            group_hom_def hom_def group_hom_axioms_def BijGroup_def image_def)  
        by (meson Pi_iff restrict_Pi_cancel)
      hence H2_2: "(\<phi>\<^sup>\<star>) g c \<in> (A\<^sup>\<star>)"
        using H1_c
        apply (clarsimp simp add: Bij_def bij_betw_def inj_on_def Image_def image_def)
        apply (rule conjI; rule impI; clarify)
        using surj_prop
         apply fastforce
        using A2_0
        by blast
      from H1_c have H2_1: "([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g (\<equiv>\<^sub>M\<^sub>N `` {c}) = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C"
        by auto
      also have H2_2: "([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C = [(\<phi>\<^sup>\<star>) g c]\<^sub>M\<^sub>N"
        using eq_var_rel.quot_act_wd[where R = "\<equiv>\<^sub>M\<^sub>N" and G = G and X = "A\<^sup>\<star>" and \<phi> = "\<phi>\<^sup>\<star>" and g = g
            and x = c]
        by (clarsimp simp del: GMN_simps simp add: alt_natural_map_MN_def make_op_def MN_rel_eq_var
            MN_rel_equival H1_c A2_0 H2_1) 
      hence H2_3: "\<delta>\<^sub>M\<^sub>N (([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C) (\<phi> g a) = \<delta>\<^sub>M\<^sub>N ([(\<phi>\<^sup>\<star>) g c]\<^sub>M\<^sub>N) (\<phi> g a)" 
        using H2_2 
        by simp
      also have H2_4: "... = [((\<phi>\<^sup>\<star>) g c) @ [(\<phi> g a)]]\<^sub>M\<^sub>N"
        using MN_trans_func_characterization[where v = "(\<phi>\<^sup>\<star>) g c" and a = "\<phi> g a"] H1_c  A2_0
          G_set_equiv H2_0 eq_var_subset.is_equivar insert_iff lists_a_Gset
        by blast
      also have H2_5: "... = [(\<phi>\<^sup>\<star>) g (c @ [a])]\<^sub>M\<^sub>N"
        using A2_0 H1_c A1_1
        by auto
      also have H2_6: "... = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g [(c @ [a])]\<^sub>M\<^sub>N"
        apply (rule meta_mp[of "c @ [a] \<in> A\<^sup>\<star>"])
        using eq_var_rel.quot_act_wd[where R = "\<equiv>\<^sub>M\<^sub>N" and G = G and X = "A\<^sup>\<star>" and \<phi> = "\<phi>\<^sup>\<star>" and g = g
            and x = "c @ [a]"]
         apply (clarsimp simp del: GMN_simps simp add: make_op_def MN_rel_eq_var MN_rel_equival H1_c
            A2_0 H2_1) 
        using H1_c A1_1
        by auto 
      also have H2_7: "... = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (\<delta>\<^sub>M\<^sub>N [c]\<^sub>M\<^sub>N a)"
        using MN_trans_func_characterization[where v = "c" and a = "a"] H1_c A1_1
        by metis
      finally show "\<delta>\<^sub>M\<^sub>N (([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C) (\<phi> g a) = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (\<delta>\<^sub>M\<^sub>N [c]\<^sub>M\<^sub>N a)"
        using H2_1 
        by metis
    qed
    show "(([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C \<in> MN_equiv \<and> \<phi> g a \<in> A \<longrightarrow>
    g \<in> carrier G \<longrightarrow>
    \<delta>\<^sub>M\<^sub>N (([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C) (\<phi> g a) =
    ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g (\<delta>\<^sub>M\<^sub>N C a)) \<and>
    ((([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g C \<in> MN_equiv \<longrightarrow> \<phi> g a \<notin> A) \<longrightarrow>
    g \<in> carrier G \<longrightarrow> undefined = ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g (\<delta>\<^sub>M\<^sub>N C a))"
      apply (rule conjI; clarify)
      using H1_1 H1_c
       apply blast
      by (metis A1_0 H1_0 H_0 alt_group_act_is_grp_act
          group_action.element_image)
  qed
  show ?thesis
    apply (subst eq_var_func_def)
    apply (subst eq_var_func_axioms_def)
    apply (rule conjI)
    subgoal 
      apply (rule prod_group_act[where G = G and A = "MN_equiv" and \<phi> = "[(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>"
            and B = A     and \<psi> = \<phi>])
       apply (rule H_0)
      using G_lang_axioms
      by (auto simp add: G_lang_def G_lang_axioms_def)
    apply (rule conjI)
    subgoal
      using MN_rel_eq_var MN_rel_equival eq_var_rel.quot_act_is_grp_act
      using alt_group_act_is_grp_act restrict_apply
      by fastforce
    apply (rule conjI)
    subgoal
      apply (subst extensional_funcset_def)
      apply (subst restrict_def)
      apply (subst Pi_def)
      apply (subst extensional_def)
      apply (clarsimp)
      by (metis MN_rel_equival append_in_lists_conv equiv_Eps_preserves lists.Cons lists.Nil
          quotientI)
    apply (subst restrict_def)
    apply (clarsimp simp del: GMN_simps simp add: make_op_def)
    by (simp add: H_1 del: GMN_simps)
qed

lemma MN_quot_act_on_empty_str:
  "\<And>g. \<lbrakk>g \<in> carrier G; ([], x) \<in> \<equiv>\<^sub>M\<^sub>N\<rbrakk> \<Longrightarrow> x \<in> map (\<phi> g) ` \<equiv>\<^sub>M\<^sub>N `` {[]}"
proof-
  fix g
  assume
    A_0: "g \<in> carrier G" and
    A_1: "([], x) \<in> \<equiv>\<^sub>M\<^sub>N"
  from A_1 have H_0: "x \<in> (A\<^sup>\<star>)"
    by (auto simp add: rel_MN_def)
  from A_0 H_0 have H_1: "x = (\<phi>\<^sup>\<star>) g ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) x)"
    by (smt (verit) alt_grp_act_def group_action.bij_prop1 group_action.orbit_sym_aux lists_a_Gset) 
  have H_2: "inv \<^bsub>G \<^esub> g \<in> carrier G"
    using A_0 MN_rel_eq_var
    by (auto simp add: eq_var_rel_def eq_var_rel_axioms_def group_action_def group_hom_def)
  have H_3: "([], (\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) x) \<in> \<equiv>\<^sub>M\<^sub>N"
    using A_0 A_1 H_0 MN_rel_eq_var
    apply (clarsimp simp add: eq_var_rel_def eq_var_rel_axioms_def) 
    apply (rule conjI; clarify)
     apply (smt (verit, best) H_0 list.simps(8) lists.Nil)
    using H_2
    by simp
  hence H_4: "\<exists>y\<in>\<equiv>\<^sub>M\<^sub>N `` {[]}. x = map (\<phi> g) y"
    using A_0 H_0 H_1 H_2
    apply clarsimp
    by (metis H_0 Image_singleton_iff insert_iff insert_image lists_image surj_prop)
  thus "x \<in> map (\<phi> g) ` \<equiv>\<^sub>M\<^sub>N `` {[]}"
    by (auto simp add: image_def)
qed

lemma MN_init_state_equivar:
  "eq_var_subset G (A\<^sup>\<star>) (\<phi>\<^sup>\<star>) MN_init_state"
  apply (clarsimp simp add: eq_var_subset_def eq_var_subset_axioms_def)
  apply (intro conjI)
  using lists_a_Gset
    apply (auto)[1]
   apply (clarsimp)
  subgoal for w a
    by (auto simp add: rel_MN_def)
  apply (clarify; rule subset_antisym; simp add: Set.subset_eq; clarify)
   apply (clarsimp simp add: image_def Image_def Int_def) 
   apply (erule disjE)
  subgoal for g w
    using MN_rel_eq_var
    apply (clarsimp simp add: eq_var_rel_def eq_var_rel_axioms_def)
    by (metis (full_types, opaque_lifting) in_listsI list.simps(8) lists.Nil)
   apply (erule conjE)
   apply (auto simp add: \<open>\<And>a w. \<lbrakk>([], w) \<in> \<equiv>\<^sub>M\<^sub>N; a \<in> set w\<rbrakk> \<Longrightarrow> a \<in> A\<close>)[1]  
  apply (rule meta_mp[of "\<equiv>\<^sub>M\<^sub>N `` {[]} \<inter> lists A = \<equiv>\<^sub>M\<^sub>N `` {[]}"])
  using MN_quot_act_on_empty_str
   apply (clarsimp) 
  apply (rule subset_antisym; simp add: Set.subset_eq)
  by (simp add: \<open>\<And>w a. \<lbrakk>([], w) \<in> \<equiv>\<^sub>M\<^sub>N; a \<in> set w\<rbrakk> \<Longrightarrow> a \<in> A\<close> in_listsI)

lemma MN_init_state_equivar_v2:
  "eq_var_subset G (MN_equiv) ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star> \<^esub>) {MN_init_state}"
proof-
  have H_0: "\<forall>g\<in>carrier G. (\<phi>\<^sup>\<star>) g ` MN_init_state = MN_init_state \<Longrightarrow>
             \<forall>g\<in>carrier G. ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g MN_init_state = MN_init_state"
  proof (clarify)
    fix g 
    assume
      A_0: "g \<in> carrier G" 
    have H_0: "\<And>x. [x]\<^sub>M\<^sub>N = \<equiv>\<^sub>M\<^sub>N `` {x}"
      by simp
    have H_1: "([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g [[]]\<^sub>M\<^sub>N = [(\<phi>\<^sup>\<star>) g []]\<^sub>M\<^sub>N"
      using eq_var_rel.quot_act_wd[where R = "\<equiv>\<^sub>M\<^sub>N" and G = G and X = "A\<^sup>\<star>" and \<phi> = "\<phi>\<^sup>\<star>" and g = g
          and x = "[]"] MN_rel_eq_var MN_rel_equival
      by (clarsimp simp del: GMN_simps simp add: H_0 make_op_def A_0) 
    from A_0 H_1 show "([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g [[]]\<^sub>M\<^sub>N = [[]]\<^sub>M\<^sub>N"
      by auto
  qed
  show ?thesis
    using MN_init_state_equivar
    apply (clarsimp simp add: eq_var_subset_def simp del: GMN_simps)
    apply (rule conjI)
    subgoal
      by (metis MN_rel_eq_var MN_rel_equival eq_var_rel.quot_act_is_grp_act)
    apply (clarsimp del: subset_antisym simp del: GMN_simps simp add: eq_var_subset_axioms_def)
    apply (rule conjI)
     apply (auto simp add: quotient_def)[1]
    by (simp add: H_0 del: GMN_simps)
qed

lemma MN_final_state_equiv:
  "eq_var_subset G (MN_equiv) ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star> \<^esub>) MN_fin_states"
proof-
  have H_0: "\<And>g x w. g \<in> carrier G \<Longrightarrow> w \<in> L \<Longrightarrow> \<exists>wa\<in>L. ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g [w]\<^sub>M\<^sub>N = [wa]\<^sub>M\<^sub>N"
  proof-
    fix g w
    assume
      A1_0: "g \<in> carrier G" and 
      A1_1: "w \<in> L" 
    have H1_0: "\<And>v. v \<in> L \<Longrightarrow> (\<phi>\<^sup>\<star>) g v \<in> L"
      using A1_0 G_lang_axioms
      apply (clarsimp simp add: G_lang_def G_lang_axioms_def eq_var_subset_def
          eq_var_subset_axioms_def)
      by blast
    hence H1_1: "(\<phi>\<^sup>\<star>) g w \<in> L"
      using A1_1
      by simp
    from A1_1 have H1_2: "\<And>v. v \<in> [w]\<^sub>M\<^sub>N \<Longrightarrow> v \<in> L"
      apply (clarsimp simp add: rel_MN_def) 
      by (metis lists.simps self_append_conv)
    have H1_3: "([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g [w]\<^sub>M\<^sub>N = [(\<phi>\<^sup>\<star>) g w]\<^sub>M\<^sub>N"
      using eq_var_rel.quot_act_wd[where R = "\<equiv>\<^sub>M\<^sub>N" and G = G and X = "A\<^sup>\<star>" and \<phi> = "\<phi>\<^sup>\<star>" and g = g
          and x = "w"] MN_rel_eq_var MN_rel_equival G_lang_axioms
      by (clarsimp simp add: A1_0 A1_1 G_lang_axioms_def G_lang_def eq_var_subset_def
          eq_var_subset_axioms_def subset_eq) 
    show "\<exists>wa\<in>L. ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g [w]\<^sub>M\<^sub>N = [wa]\<^sub>M\<^sub>N"
      using H1_1 H1_3
      by blast
  qed
  have H_1: "\<And>g x w. g \<in> carrier G \<Longrightarrow> w \<in> L \<Longrightarrow> [w]\<^sub>M\<^sub>N \<in> ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g ` MN_fin_states"
  proof-
    fix g x w
    assume
      A1_0: "g \<in> carrier G" and 
      A1_1: "w \<in> L" 
    have H1_0: "\<And>v h. v \<in> L \<Longrightarrow> h \<in> carrier G \<Longrightarrow> (\<phi>\<^sup>\<star>) h v \<in> L"
      using G_lang_axioms
      apply (clarsimp simp add: G_lang_def G_lang_axioms_def eq_var_subset_def
          eq_var_subset_axioms_def)
      by blast
    have H1_1: "(\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w \<in> L" 
      apply (rule meta_mp[of "(inv \<^bsub>G\<^esub> g) \<in> carrier G"]) 
      using A1_1 H1_0
       apply blast using A1_0 
      by (metis group.inv_closed group_hom group_hom.axioms(1))
    have H1_2: "\<And>v. v \<in> [w]\<^sub>M\<^sub>N \<Longrightarrow> v \<in> L"
      using A1_1 apply (clarsimp simp add: rel_MN_def) 
      by (metis lists.simps self_append_conv)
    have H1_3: "([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g [(\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w]\<^sub>M\<^sub>N = [w]\<^sub>M\<^sub>N"
      apply (rule meta_mp[of "(\<phi>\<^sup>\<star>) g ((\<phi>\<^sup>\<star>) (inv\<^bsub>G\<^esub> g) w) = w"])
      using eq_var_rel.quot_act_wd[where R = "\<equiv>\<^sub>M\<^sub>N" and G = G and X = "A\<^sup>\<star>" and \<phi> = "\<phi>\<^sup>\<star>" and g = g
          and x = "(\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w"]
        MN_rel_eq_var MN_rel_equival G_lang_axioms H1_1
       apply (clarsimp simp del: GMN_simps simp add: make_op_def A1_0 A1_1 G_lang_axioms_def
          G_lang_def eq_var_subset_def eq_var_subset_axioms_def subset_eq)
      using A1_0 A1_1 H1_1 G_lang_axioms
       apply (clarsimp simp del: GMN_simps simp add: alt_natural_map_MN_def make_op_def
          G_lang_axioms_def G_lang_def eq_var_subset_def alt_grp_act_def)
      using group_action.orbit_sym_aux[where G = G and E = "A\<^sup>\<star>" and g = "(inv\<^bsub>G\<^esub> g)" and x = w
          and \<phi> = "\<phi>\<^sup>\<star>" and y = "((\<phi>\<^sup>\<star>) (inv\<^bsub>G\<^esub> g) w)"]
      by (smt (verit) A1_0 A1_1 L_is_equivar alt_group_act_is_grp_act
          eq_var_subset.is_subset group_action.bij_prop1 group_action.orbit_sym_aux insert_subset
          lists_a_Gset mk_disjoint_insert)
    show "[w]\<^sub>M\<^sub>N \<in> ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) g ` {v. \<exists>w\<in>L. v = [w]\<^sub>M\<^sub>N}"
      apply (clarsimp simp del: GMN_simps simp add: image_def) 
      using H1_1 H1_3
      by blast
  qed
  show ?thesis
    apply (clarsimp simp del: GMN_simps simp add: eq_var_subset_def) 
    apply (rule conjI)
    using MN_init_state_equivar_v2 eq_var_subset.axioms(1)
     apply blast
    apply (clarsimp simp del: GMN_simps simp add: eq_var_subset_axioms_def)
    apply (rule conjI; clarsimp simp del: GMN_simps)
    subgoal for w
      using G_lang_axioms
      by (auto simp add: quotient_def G_lang_axioms_def G_lang_def eq_var_subset_def
          eq_var_subset_axioms_def)
    apply (rule subset_antisym; simp add: Set.subset_eq del: GMN_simps; clarify)
     apply (simp add: H_0 del: GMN_simps)
    by (simp add: H_1 del: GMN_simps)
qed

interpretation syntac_aut :
  det_aut "A" "MN_equiv" "MN_init_state" "MN_fin_states" "MN_trans_func"
proof-
  have H_0: "\<And>state label. state \<in> MN_equiv \<Longrightarrow> label \<in> A \<Longrightarrow> \<delta>\<^sub>M\<^sub>N state label \<in> MN_equiv"
  proof -
    fix state label
    assume
      A_0: "state \<in> MN_equiv" and
      A_1: "label \<in> A" 
    obtain w where H_w: "state = [w]\<^sub>M\<^sub>N \<and> w \<in> A\<^sup>\<star>"
      by (metis A_0 alt_natural_map_MN_def quotientE)
    have H_0: "\<delta>\<^sub>M\<^sub>N [w]\<^sub>M\<^sub>N label = [w @ [label]]\<^sub>M\<^sub>N"
      using MN_trans_func_characterization[where v = w and a = label] H_w A_1
      by simp
    have H_1: "\<And>v. v \<in> A\<^sup>\<star> \<Longrightarrow> [v]\<^sub>M\<^sub>N \<in> MN_equiv"
      by (simp add: in_listsI quotientI)
    show "\<delta>\<^sub>M\<^sub>N state label \<in> MN_equiv"
      using H_w H_0 H_1 
      by (simp add: A_1)
  qed
  show "det_aut A MN_equiv MN_init_state MN_fin_states \<delta>\<^sub>M\<^sub>N"
    apply (clarsimp simp del: GMN_simps simp add: det_aut_def alt_natural_map_MN_def)
    apply (intro conjI)
      apply (auto simp add: quotient_def)[1]
    using G_lang_axioms
     apply (auto simp add: quotient_def G_lang_axioms_def G_lang_def
        eq_var_subset_def eq_var_subset_axioms_def)[1]
    apply (auto simp add: extensional_def PiE_iff simp del: MN_trans_func_def)[1]
        apply (simp add: H_0 del: GMN_simps)
    by auto
qed

corollary syth_aut_is_det_aut:
  "det_aut A MN_equiv MN_init_state MN_fin_states \<delta>\<^sub>M\<^sub>N"
  using local.syntac_aut.det_aut_axioms
  by simp

lemma give_input_transition_func:
  "w \<in> (A\<^sup>\<star>) \<Longrightarrow> \<forall>v \<in> (A\<^sup>\<star>). [v @ w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v]\<^sub>M\<^sub>N w"
proof-
  assume 
    A_0: "w \<in> A\<^sup>\<star>"
  have H_0: "\<And> a w v. \<lbrakk>a \<in> A; w \<in> A\<^sup>\<star>; \<forall>v\<in>A\<^sup>\<star>. [v @ w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v]\<^sub>M\<^sub>N w; v \<in> A\<^sup>\<star>\<rbrakk> \<Longrightarrow>
            [v @ a # w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v]\<^sub>M\<^sub>N (a # w)"
  proof-
    fix a w v
    assume
      A1_IH: "\<forall>v\<in> A\<^sup>\<star>. [v @ w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v]\<^sub>M\<^sub>N w" and
      A1_0: "a \<in> A" and
      A1_1: "v \<in> A\<^sup>\<star>" and
      A1_2: "w \<in> A\<^sup>\<star>"
    from A1_IH A1_1 A1_2 have H1_1: "[v @ w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v]\<^sub>M\<^sub>N w"
      by auto
    have H1_2: "[(v @ [a]) @ w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v @ [a]]\<^sub>M\<^sub>N w"
      apply (rule meta_mp[of "(v @ [a]) \<in> (A\<^sup>\<star>)"])
      using A1_IH A1_2 H1_1
       apply blast 
      using A1_0 A1_1
      by auto
    have H1_3: "\<delta>\<^sub>M\<^sub>N [v]\<^sub>M\<^sub>N a = [v @ [a]]\<^sub>M\<^sub>N"
      using MN_trans_func_characterization[where a = a] A1_0 A1_1
      by auto
    hence H1_4: "[v @ a # w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v @ [a]]\<^sub>M\<^sub>N w"
      using H1_2
      by auto
    also have H1_5: "... = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) (\<delta>\<^sub>M\<^sub>N [v]\<^sub>M\<^sub>N a) w"
      using H1_4 H1_3 A1_1
      by auto 
    thus "[v @ a # w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [v]\<^sub>M\<^sub>N (a # w)"
      using calculation
      by auto
  qed
  from A_0 show ?thesis
    apply (induction w)
     apply (auto)[1] 
    by (simp add: H_0 del: GMN_simps)
qed
  

lemma MN_unique_init_state:
  "w \<in> (A\<^sup>\<star>) \<Longrightarrow> [w]\<^sub>M\<^sub>N = (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) [Nil]\<^sub>M\<^sub>N w"
  using give_input_transition_func[where w = w] 
  by (metis append_self_conv2 lists.Nil)

lemma fin_states_rep_by_lang:
  "w \<in> A\<^sup>\<star> \<Longrightarrow> [w]\<^sub>M\<^sub>N \<in> MN_fin_states \<Longrightarrow> w \<in> L"
proof-
  assume
    A_0: "w \<in> A\<^sup>\<star>" and
    A_1: "[w]\<^sub>M\<^sub>N \<in> MN_fin_states"
  from A_1 have H_0: "\<exists>w'\<in>[w]\<^sub>M\<^sub>N. w' \<in> L"
    apply (clarsimp) 
    by (metis A_0 MN_rel_equival equiv_class_self proj_def proj_in_iff)
  from H_0 obtain w' where H_w': "w'\<in>[w]\<^sub>M\<^sub>N \<and> w' \<in> L" 
    by auto
  have H_1: "\<And>v. v \<in> A\<^sup>\<star> \<Longrightarrow> w'@v \<in> L \<Longrightarrow> w@v \<in> L"
    using H_w' A_1 A_0
    by (auto simp add: rel_MN_def)
  show "w \<in> L"
    using H_1 H_w'
    apply clarify 
    by (metis append_Nil2 lists.Nil)
qed

text \<open>
The following lemma corresponds to lemma 3.6 from \cite{bojanczyk2014automata}:
\<close>

lemma syntactic_aut_det_G_aut:
  "det_G_aut A MN_equiv MN_init_state MN_fin_states MN_trans_func G \<phi> ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)"
  apply (clarsimp simp add: det_G_aut_def simp del: GMN_simps)
  apply (intro conjI)
  using syth_aut_is_det_aut
       apply (auto)[1]
  using alt_grp_act_axioms
      apply (auto)[1]
  using MN_init_state_equivar_v2 eq_var_subset.axioms(1)
     apply blast
  using MN_final_state_equiv
    apply presburger
  using MN_init_state_equivar_v2
   apply presburger
  using MN_trans_eq_var_func
  by linarith

lemma syntactic_aut_det_G_aut_rec_L:
  "det_G_aut_rec_lang A MN_equiv MN_init_state MN_fin_states MN_trans_func G \<phi>
 ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) L"
  apply (clarsimp simp add: det_G_aut_rec_lang_def det_aut_rec_lang_axioms_def
      det_aut_rec_lang_def simp del: GMN_simps)
  apply (intro conjI)
  using syntactic_aut_det_G_aut syth_aut_is_det_aut
    apply (auto)[1]
  using syntactic_aut_det_G_aut syth_aut_is_det_aut
   apply (auto)[1]
  apply (rule allI; rule iffI)
   apply (rule conjI)
  using L_is_equivar eq_var_subset.is_subset image_iff image_mono insert_image insert_subset
    apply blast
  using MN_unique_init_state L_is_equivar eq_var_subset.is_subset
   apply blast
  using MN_unique_init_state fin_states_rep_by_lang in_lists_conv_set 
  by (smt (verit) mem_Collect_eq)

lemma syntact_aut_is_reach_aut_rec_lang:
  "reach_det_G_aut_rec_lang A MN_equiv MN_init_state MN_fin_states MN_trans_func G \<phi>
 ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) L"
  apply (clarsimp simp del: GMN_simps simp add: reach_det_G_aut_rec_lang_def
      det_G_aut_rec_lang_def det_aut_rec_lang_axioms_def reach_det_G_aut_def
      reach_det_aut_def reach_det_aut_axioms_def det_G_aut_def det_aut_rec_lang_def)
  apply (intro conjI)
  using syth_aut_is_det_aut
                 apply blast
  using alt_grp_act_axioms
                apply (auto)[1]
  subgoal
    using MN_init_state_equivar_v2 eq_var_subset.axioms(1)
    by blast
  using MN_final_state_equiv
              apply presburger
  using MN_init_state_equivar_v2
  subgoal
    by presburger
  using MN_trans_eq_var_func
            apply linarith
  using syth_aut_is_det_aut
           apply (auto)[1]
          apply (metis (mono_tags, lifting) G_lang.MN_unique_init_state G_lang_axioms
      det_G_aut_rec_lang_def det_aut_rec_lang.is_recognised syntactic_aut_det_G_aut_rec_L)
  using syth_aut_is_det_aut
         apply (auto)[1]
  using alt_grp_act_axioms
        apply (auto)[1]
  using \<open>alt_grp_act G MN_equiv ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>)\<close>
       apply blast
  using \<open>eq_var_subset G MN_equiv ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) MN_fin_states\<close>
      apply blast
  using \<open>eq_var_subset G MN_equiv ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>) {MN_init_state}\<close>
     apply blast
  using MN_trans_eq_var_func
    apply blast
  using syth_aut_is_det_aut
   apply auto[1]
  by (metis MN_unique_init_state alt_natural_map_MN_def quotientE)
end

subsection \<open>
Proving the Myhill-Nerode Theorem for $G$-Automata
\<close>
context det_G_aut begin
no_adhoc_overloading
  star labels_a_G_set.induced_star_map
end

context reach_det_G_aut_rec_lang begin
adhoc_overloading
  star labels_a_G_set.induced_star_map

definition
  states_to_words :: "'states \<Rightarrow> 'alpha list"
  where "states_to_words = (\<lambda>s \<in> S. SOME w. w \<in> A\<^sup>\<star> \<and> ((\<delta>\<^sup>\<star>) i w = s))"

definition
  words_to_syth_states :: "'alpha list \<Rightarrow> 'alpha list set"
  where "words_to_syth_states w = [w]\<^sub>M\<^sub>N"

definition
  induced_epi:: "'states \<Rightarrow> 'alpha list set"
  where "induced_epi = compose S words_to_syth_states states_to_words"

lemma induced_epi_wd1:
  "s \<in> S \<Longrightarrow> \<exists>w. w \<in> A\<^sup>\<star> \<and> ((\<delta>\<^sup>\<star>) i w = s)"
  using reach_det_G_aut_rec_lang_axioms is_reachable
  by auto

lemma induced_epi_wd2:
  "w \<in> A\<^sup>\<star> \<Longrightarrow> w' \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i w = (\<delta>\<^sup>\<star>) i w' \<Longrightarrow> [w]\<^sub>M\<^sub>N = [w']\<^sub>M\<^sub>N"
proof- 
  assume
    A_0: "w \<in> A\<^sup>\<star>" and
    A_1: "w' \<in> A\<^sup>\<star>" and
    A_2: "(\<delta>\<^sup>\<star>) i w = (\<delta>\<^sup>\<star>) i w'"
  have H_0: "\<And>v. v \<in> A\<^sup>\<star> \<Longrightarrow> w @ v \<in> L \<longleftrightarrow> w' @ v \<in> L"
    apply clarify 
    by (smt (z3) A_0 A_1 A_2 append_in_lists_conv is_aut.eq_pres_under_concat
        is_aut.init_state_is_a_state is_lang is_recognised subsetD)+
  show "[w]\<^sub>M\<^sub>N = [w']\<^sub>M\<^sub>N "
    apply (simp add: rel_MN_def)
    using H_0 A_0 A_1
    by auto
qed

lemma states_to_words_on_final:
  "states_to_words \<in> (F \<rightarrow> L)"
proof-
  have H_0: "\<And>x. x \<in> F \<Longrightarrow> x \<in> S \<Longrightarrow> (SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = x) \<in> L"
  proof-
    fix s
    assume
      A1_0: "s \<in> F"
    have H1_0: "\<exists>w. w \<in> lists A \<and> (\<delta>\<^sup>\<star>) i w = s"
      using A1_0 is_reachable 
      by (metis is_aut.fin_states_are_states subsetD)
    have H1_1: "\<And>w. w \<in> lists A \<and> (\<delta>\<^sup>\<star>) i w = s \<Longrightarrow> w \<in> L"
      using A1_0 is_recognised
      by auto
    show "(SOME w. w \<in> lists A \<and> (\<delta>\<^sup>\<star>) i w = s) \<in> L "
      by (metis (mono_tags, lifting) H1_0 H1_1 someI_ex)
  qed
  show ?thesis
    apply (clarsimp simp add: states_to_words_def)
    apply (rule conjI; rule impI)
     apply ( simp add: H_0)
    using is_aut.fin_states_are_states
    by blast
qed


lemma induced_epi_eq_var:
  "eq_var_func G S \<psi> MN_equiv ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) induced_epi"
proof-
  have H_0: "\<And> s g. \<lbrakk>s \<in> S; g \<in> carrier G; \<psi> g s \<in> S\<rbrakk> \<Longrightarrow>
    words_to_syth_states (states_to_words (\<psi> g s)) =
    ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (words_to_syth_states (states_to_words s))"
  proof-
    fix s g 
    assume
      A1_0: "s \<in> S" and
      A1_1: "g \<in> carrier G" and
      A1_2: "\<psi> g s \<in> S"
    have H1_0: "([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (words_to_syth_states (states_to_words s)) =
     [(\<phi>\<^sup>\<star>) g (SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s)]\<^sub>M\<^sub>N"
      apply (clarsimp simp del: GMN_simps simp add: words_to_syth_states_def
          states_to_words_def A1_0)
      apply (rule meta_mp[of "(SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s) \<in> A\<^sup>\<star>"])
      using quot_act_wd_alt_notation[where w = "(SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s)" and g = g] A1_1
       apply simp
      using A1_0
      by (metis (mono_tags, lifting) induced_epi_wd1 some_eq_imp)
    have H1_1: "\<And>g s' w'. \<lbrakk>s'\<in> S; w'\<in> A\<^sup>\<star>; g \<in> carrier G; (\<phi>\<^sup>\<star>) g w' \<in> A\<^sup>\<star> \<and> \<psi> g s' \<in> S\<rbrakk>
               \<Longrightarrow> (\<delta>\<^sup>\<star>) (\<psi> g s') ((\<phi>\<^sup>\<star>) g w') = \<psi> g ((\<delta>\<^sup>\<star>) s' w')"
      using give_input_eq_var
      apply (clarsimp simp del: GMN_simps simp add: eq_var_func_axioms_def eq_var_func_def
          make_op_def)
      by (meson in_listsI)
    have H1_2: "{w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g s} =
     {w'. \<exists>w \<in> A\<^sup>\<star>. (\<phi>\<^sup>\<star>) g w = w' \<and> (\<delta>\<^sup>\<star>) i w = s}"
    proof (rule subset_antisym; clarify)
      fix w'
      assume
        A2_0: "(\<delta>\<^sup>\<star>) i w' = \<psi> g s" and
        A2_1: "\<forall>x\<in>set w'. x \<in> A"
      have H2_0: "(inv \<^bsub>G\<^esub> g) \<in> carrier G"
        by (meson A1_1 group.inv_closed group_hom.axioms(1) states_a_G_set.group_hom)
      have H2_1: "(\<phi>\<^sup>\<star>) g ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w') = w'"
        by (smt (verit) A1_1 A2_1 alt_group_act_is_grp_act group_action.bij_prop1
            group_action.orbit_sym_aux in_listsI labels_a_G_set.lists_a_Gset)
      have H2_2: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w) = (\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w)"
        using init_is_eq_var.eq_var_subset_axioms init_is_eq_var.is_equivar
        by auto
      have H2_3: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w) = \<psi> g ((\<delta>\<^sup>\<star>) i w)"
        apply (rule H1_1[where s'1 = i]) 
           apply (simp add: A2_1 in_lists_conv_set H2_0 is_aut.init_state_is_a_state)+
        using is_aut.init_state_is_a_state labels_a_G_set.element_image
          states_a_G_set.element_image
        by blast
      have H2_4: "\<psi> (inv \<^bsub>G\<^esub> g) ((\<delta>\<^sup>\<star>) i w') = s"
        using A2_0 H2_0
        by (simp add: A1_0 A1_1 states_a_G_set.orbit_sym_aux)
      have H2_5: "(\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w') = s"
        apply (rule meta_mp[of "w'\<in> A\<^sup>\<star>"])
        using H2_0 H2_1 H2_4 A2_1 H2_2 H2_3
         apply presburger 
        using A2_1
        by auto
      have H2_6: "(\<phi>\<^sup>\<star>) (inv\<^bsub>G\<^esub> g) w' \<in> lists A "
        using H2_0 A2_1 
        by (metis alt_group_act_is_grp_act group_action.element_image in_listsI
            labels_a_G_set.lists_a_Gset)
      thus "\<exists>w\<in>lists A. (\<phi>\<^sup>\<star>) g w = w' \<and> (\<delta>\<^sup>\<star>) i w = s"
        using H2_1 H2_5 H2_6
        by blast
    next
      fix x w
      assume
        A2_0: "\<forall>x\<in>set w. x \<in> A" and
        A2_1: "s = (\<delta>\<^sup>\<star>) i w"
      show "(\<phi>\<^sup>\<star>) g w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w) = \<psi> g ((\<delta>\<^sup>\<star>) i w) "
        apply (rule conjI)
         apply (rule meta_mp[of "(inv \<^bsub>G\<^esub> g) \<in> carrier G"])
        using alt_group_act_is_grp_act group_action.element_image in_listsI
          labels_a_G_set.lists_a_Gset
          apply (metis A1_1 A2_0)
         apply (meson A1_1 group.inv_closed group_hom.axioms(1) states_a_G_set.group_hom)
        apply (rule meta_mp[of "\<psi> g i = i"])
        using H1_1[where s'1 = i and g1 = "g"]
         apply (metis A1_1 A2_0 action_on_input in_listsI)
        using init_is_eq_var.eq_var_subset_axioms init_is_eq_var.is_equivar
        by (simp add: A1_1)
    qed
    have H1_3: "\<exists>w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s" 
      using A1_0 is_reachable
      by auto
    have H1_4: "\<exists>w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g s"
      using A1_2 induced_epi_wd1
      by auto
    have H1_5: "[(\<phi>\<^sup>\<star>) g (SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s)]\<^sub>M\<^sub>N = [SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g s]\<^sub>M\<^sub>N" 
    proof (rule subset_antisym; clarify)
      fix w'
      assume
        A2_0: "w' \<in> [(\<phi>\<^sup>\<star>) g (SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s)]\<^sub>M\<^sub>N"
      have H2_0: "\<And>w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s \<Longrightarrow> w' \<in> [(\<phi>\<^sup>\<star>) g w]\<^sub>M\<^sub>N"
        using A2_0 H1_3 H1_2 H1_4 induced_epi_wd2 mem_Collect_eq tfl_some 
        by (smt (verit, best))  
      obtain w'' where H2_w'': "w' \<in> [(\<phi>\<^sup>\<star>) g w'']\<^sub>M\<^sub>N \<and> w'' \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w'' = s"
        using A2_0 H1_3 tfl_some
        by (metis (mono_tags, lifting))
      from H1_2 H2_w'' have H2_1: "(\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w'') = \<psi> g s"
        by blast
      have H2_2: "\<And>w. w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i w = \<psi> g s \<Longrightarrow> w' \<in> [w]\<^sub>M\<^sub>N"
      proof -
        fix w''
        assume
          A3_0: "w'' \<in> A\<^sup>\<star>" and
          A3_1: "(\<delta>\<^sup>\<star>) i w'' = \<psi> g s"
        have H3_0: "(inv \<^bsub>G\<^esub>g) \<in> carrier G" 
          by (metis A1_1 group.inv_closed group_hom.axioms(1) states_a_G_set.group_hom)
        from A3_0 H3_0 have H3_1: "(\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w'' \<in> A\<^sup>\<star>"
          by (metis alt_grp_act.axioms group_action.element_image 
              labels_a_G_set.lists_a_Gset)
        have H3_2: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w) = (\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w)"
          using init_is_eq_var.eq_var_subset_axioms init_is_eq_var.is_equivar
          by auto
        have H3_3: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w) = \<psi> g ((\<delta>\<^sup>\<star>) i w)"
          apply (rule H1_1[where s'1 = i]) 
             apply (simp add: A3_1 in_lists_conv_set H2_1 is_aut.init_state_is_a_state)+
          using is_aut.init_state_is_a_state labels_a_G_set.element_image
            states_a_G_set.element_image
          by blast
        have H3_4: "s = (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w'')"
          using A3_0 A3_1 H3_0 H3_2 H3_3 A1_0 A1_1 states_a_G_set.orbit_sym_aux
          by auto
        from H3_4 show " w' \<in> [w'']\<^sub>M\<^sub>N"
          by (metis (mono_tags, lifting) A1_1 G_set_equiv H2_1 H2_w'' \<open>(\<delta>\<^sup>\<star>) i w'' = \<psi> g s\<close> A3_0
              eq_var_subset.is_equivar image_eqI induced_epi_wd2
              labels_a_G_set.lists_a_Gset)
      qed
      from H2_2 show "w' \<in> [SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g s]\<^sub>M\<^sub>N"
        by (smt (verit) H1_4 some_eq_ex)
    next
      fix w'
      assume
        A2_0: "w' \<in> [SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<psi> g s]\<^sub>M\<^sub>N"
      obtain w'' where H2_w'': "w' \<in> [(\<phi>\<^sup>\<star>) g w'']\<^sub>M\<^sub>N \<and> w'' \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w'' = s"
        using A2_0 H1_3 tfl_some 
        by (smt (verit) H1_2 mem_Collect_eq)
      from H1_2 H2_w'' have H2_0: "(\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w'') = \<psi> g s"
        by blast
      have H2_1: "\<And>w. w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i w = s \<Longrightarrow> w' \<in> [(\<phi>\<^sup>\<star>) g w]\<^sub>M\<^sub>N"
      proof -
        fix w''
        assume
          A3_0: "w'' \<in> A\<^sup>\<star>" and
          A3_1: "(\<delta>\<^sup>\<star>) i w'' = s"
        have H3_0: "(inv \<^bsub>G\<^esub>g) \<in> carrier G" 
          by (metis A1_1 group.inv_closed group_hom.axioms(1) states_a_G_set.group_hom)
        have H3_1: "(\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w'' \<in> A\<^sup>\<star>"
          using A3_0 H3_0 
          by (metis alt_group_act_is_grp_act group_action.element_image labels_a_G_set.lists_a_Gset)
        have H3_2: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) g w) =
       (\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w)"
          using init_is_eq_var.eq_var_subset_axioms init_is_eq_var.is_equivar
          by auto
        have H3_3: "\<And>g w. g \<in> carrier G \<Longrightarrow> w \<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) (\<psi> g i) ((\<phi>\<^sup>\<star>) g w) = 
       \<psi> g ((\<delta>\<^sup>\<star>) i w)"
          apply (rule H1_1[where s'1 = i]) 
             apply (simp add: A3_1 in_lists_conv_set H2_0 is_aut.init_state_is_a_state)+
          using is_aut.init_state_is_a_state labels_a_G_set.element_image
            states_a_G_set.element_image
          by blast
        have H3_4: "\<psi> (inv \<^bsub>G\<^esub> g) s = (\<delta>\<^sup>\<star>) i ((\<phi>\<^sup>\<star>) (inv \<^bsub>G\<^esub> g) w'')"
          using A3_0 A3_1 H3_0 H3_2 H3_3
          by auto
        show "w' \<in> [(\<phi>\<^sup>\<star>) g w'']\<^sub>M\<^sub>N "
          using H3_4 H3_1 
          by (smt (verit, del_insts) A1_1 A3_0 A3_1 in_listsI H3_2 H3_3
              \<open>\<And>thesis. (\<And>w''. w' \<in> [(\<phi>\<^sup>\<star>) g w'']\<^sub>M\<^sub>N \<and> w'' \<in> A\<^sup>\<star> \<and>
              (\<delta>\<^sup>\<star>) i w'' = s \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
              alt_group_act_is_grp_act group_action.surj_prop image_eqI induced_epi_wd2
              labels_a_G_set.lists_a_Gset)
      qed
      show "w' \<in> [(\<phi>\<^sup>\<star>) g (SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s)]\<^sub>M\<^sub>N"
        using H2_1 H1_3
        by (metis (mono_tags, lifting) someI)
    qed
    show "words_to_syth_states (states_to_words (\<psi> g s)) =
    ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (words_to_syth_states (states_to_words s))"
      using H1_5
      apply (clarsimp simp del: GMN_simps simp add: words_to_syth_states_def states_to_words_def)
      apply (intro conjI; clarify; rule conjI)
      using H1_0
         apply (auto del: subset_antisym simp del: GMN_simps simp add: words_to_syth_states_def
          states_to_words_def)[1]
      using A1_2
        apply blast 
      using A1_0
       apply blast
      using A1_0
      by blast
  qed
  show ?thesis
    apply (clarsimp del: subset_antisym simp del: GMN_simps simp add: eq_var_func_def
        eq_var_func_axioms_def)
    apply (intro conjI)
    subgoal
      using states_a_G_set.alt_grp_act_axioms
      by auto
      apply (metis MN_rel_eq_var MN_rel_equival eq_var_rel.quot_act_is_grp_act)
     apply (clarsimp simp add: FuncSet.extensional_funcset_def Pi_def)
     apply (rule conjI)
      apply (clarify)
    subgoal for s
      using is_reachable[where s = s]
      apply (clarsimp simp add: induced_epi_def compose_def states_to_words_def
          words_to_syth_states_def)
      by (smt (verit) \<open>s \<in> S \<Longrightarrow> \<exists>input\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i input = s\<close> alt_natural_map_MN_def
          lists_eq_set quotientI rel_MN_def singleton_conv someI)
     apply (clarsimp simp del: GMN_simps simp add: induced_epi_def make_op_def
        compose_def)
    apply (clarify)
    apply (clarsimp simp del: GMN_simps simp add: induced_epi_def compose_def make_op_def)
    apply (rule conjI; rule impI)
     apply (simp add: H_0)
    using states_a_G_set.element_image
    by blast
qed

text \<open>
The following lemma corresponds to lemma 3.7 from \cite{bojanczyk2014automata}:
\<close>

lemma reach_det_G_aut_rec_lang:
  "G_aut_epi A S i F \<delta> MN_equiv MN_init_state MN_fin_states \<delta>\<^sub>M\<^sub>N G \<phi> \<psi> ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) induced_epi"
proof-
  have H_0: "\<And>s. s \<in> MN_equiv \<Longrightarrow> \<exists>input\<in> A\<^sup>\<star>. (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) MN_init_state input = s"
  proof-
    fix s
    assume
      A_0: "s \<in> MN_equiv"
    from A_0 have H_0: "\<exists>w. w \<in> A\<^sup>\<star> \<and> s = [w]\<^sub>M\<^sub>N"
      by (auto simp add: quotient_def)
    show "\<exists>input\<in>A\<^sup>\<star>. (\<delta>\<^sub>M\<^sub>N\<^sup>\<star>) MN_init_state input = s"
      using H_0 
      by (metis MN_unique_init_state)
  qed
  have H_1: "\<And>s\<^sub>0 a. s\<^sub>0 \<in> S \<Longrightarrow> a \<in> A \<Longrightarrow> induced_epi (\<delta> s\<^sub>0 a) = \<delta>\<^sub>M\<^sub>N (induced_epi s\<^sub>0) a"
  proof-
    fix s\<^sub>0 a
    assume
      A1_0: "s\<^sub>0 \<in> S" and
      A1_1: "a \<in> A" 
    obtain w where H1_w: "w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s\<^sub>0" 
      using A1_0 induced_epi_wd1
      by auto
    have H1_0: "[SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s\<^sub>0]\<^sub>M\<^sub>N = [w]\<^sub>M\<^sub>N"
      by (metis (mono_tags, lifting) H1_w induced_epi_wd2 some_eq_imp)
    have H1_1: "(\<delta>\<^sup>\<star>) i (SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<delta> s\<^sub>0 a) = (\<delta>\<^sup>\<star>) i (w @ [a])"
      using A1_0 A1_1 H1_w is_aut.trans_to_charact[where s = s\<^sub>0 and a = a and w = w] 
      by (smt (verit, del_insts) induced_epi_wd1 is_aut.trans_func_well_def tfl_some)
    have H1_2: "w @ [a] \<in> A\<^sup>\<star>" using H1_w A1_1 by auto
    have H1_3: "[(SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s\<^sub>0) @ [a]]\<^sub>M\<^sub>N = [w @ [a]]\<^sub>M\<^sub>N" 
      by (metis (mono_tags, lifting) A1_1 H1_0 H1_w MN_trans_func_characterization someI)
    have H1_4: "... = [SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<delta> s\<^sub>0 a]\<^sub>M\<^sub>N"
      apply (rule sym)
      apply (rule induced_epi_wd2[where w = "SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = \<delta> s\<^sub>0 a"
            and w'= "w @ [a]"])
        apply (metis (mono_tags, lifting) A1_0 A1_1 H1_w some_eq_imp H1_2 is_aut.trans_to_charact)
       apply (rule H1_2)
      using H1_1
      by simp
    show "induced_epi (\<delta> s\<^sub>0 a) = \<delta>\<^sub>M\<^sub>N (induced_epi s\<^sub>0) a"
      apply (clarsimp del: subset_antisym simp del: GMN_simps simp add: induced_epi_def
          words_to_syth_states_def states_to_words_def compose_def is_aut.trans_func_well_def)
      using A1_1 H1_w H1_0 H1_3 H1_4 MN_trans_func_characterization A1_0
        is_aut.trans_func_well_def
      by presburger
  qed
  have H_2: "induced_epi ` S = MN_equiv"
  proof-
    have H1_0: "\<forall>s \<in> S. \<exists>v\<in> A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i v = s \<and> [SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s]\<^sub>M\<^sub>N = [v]\<^sub>M\<^sub>N"
      by (smt (verit) is_reachable tfl_some)
    have H1_1: "\<And>v. v\<in> A\<^sup>\<star> \<Longrightarrow> (\<delta>\<^sup>\<star>) i v \<in> S" 
      using is_aut.give_input_closed
      by (auto simp add: is_aut.init_state_is_a_state)
    show ?thesis
      apply (clarsimp simp del: GMN_simps simp add: induced_epi_def words_to_syth_states_def
          states_to_words_def compose_def image_def)
      using H1_0 H1_1
      apply (clarsimp)
      apply (rule subset_antisym; simp del: GMN_simps add: Set.subset_eq)
       apply (metis (no_types, lifting) quotientI)
      by (metis (no_types, lifting) alt_natural_map_MN_def induced_epi_wd2 quotientE)
  qed
  show ?thesis
    apply (simp del: GMN_simps add: G_aut_epi_def G_aut_epi_axioms_def)
    apply (rule conjI)
    subgoal
      apply (clarsimp simp del: GMN_simps simp add: G_aut_hom_def aut_hom_def reach_det_G_aut_def
          is_reachable det_G_aut_def reach_det_aut_def reach_det_aut_axioms_def)
      apply (intro conjI)
                        apply (simp add: is_aut.det_aut_axioms)
      using labels_a_G_set.alt_grp_act_axioms
                       apply (auto)[1]
      using states_a_G_set.alt_grp_act_axioms
                      apply blast
                     apply (simp add: accepting_is_eq_var.eq_var_subset_axioms)
      using init_is_eq_var.eq_var_subset_axioms
                    apply (auto)[1]
                   apply (simp add: trans_is_eq_var.eq_var_func_axioms)
                  apply (simp add: is_aut.det_aut_axioms)
      using syth_aut_is_det_aut
                 apply simp
      using labels_a_G_set.alt_grp_act_axioms
                apply (auto)[1]
               apply (metis MN_rel_eq_var MN_rel_equival eq_var_rel.quot_act_is_grp_act)
      using MN_final_state_equiv
              apply presburger 
      using MN_init_state_equivar_v2
             apply presburger 
      using MN_trans_eq_var_func
            apply blast
      using syth_aut_is_det_aut
           apply auto[1]
          apply (clarify)
          apply (simp add: H_0 del: GMN_simps)
         apply (simp add: is_aut.det_aut_axioms)
      using syth_aut_is_det_aut
        apply blast
       apply (clarsimp del: subset_antisym simp del: GMN_simps simp add: aut_hom_axioms_def
          FuncSet.extensional_funcset_def Pi_def extensional_def)[1]
       apply (intro conjI)
           apply (clarify)
           apply (simp add: induced_epi_def)
           apply (simp add: induced_epi_def words_to_syth_states_def states_to_words_def
          compose_def)
           apply (rule meta_mp[of "(\<delta>\<^sup>\<star>) i Nil = i"])
      using induced_epi_wd2[where w = "Nil"]
            apply (auto simp add: is_aut.init_state_is_a_state del: subset_antisym)[2] 
      subgoal for x
        apply (rule quotientI)
        using is_reachable[where s = x] someI[where P = "\<lambda>w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = x"]      
        by blast
          apply (auto simp add: induced_epi_def words_to_syth_states_def states_to_words_def
          compose_def)[1]
         apply (simp add: induced_epi_def states_to_words_def compose_def
          is_aut.init_state_is_a_state)
         apply (metis (mono_tags, lifting) \<open>\<And>w'. \<lbrakk>[] \<in> A\<^sup>\<star>; w' \<in> A\<^sup>\<star>;
      (\<delta>\<^sup>\<star>) i [] = (\<delta>\<^sup>\<star>) i w'\<rbrakk> \<Longrightarrow> MN_init_state = [w']\<^sub>M\<^sub>N\<close>
          alt_natural_map_MN_def give_input.simps(1) lists.Nil some_eq_imp
          words_to_syth_states_def)
        apply (clarify)
      subgoal for s 
        apply (rule iffI)
         apply (smt (verit) Pi_iff compose_eq in_mono induced_epi_def is_aut.fin_states_are_states
            states_to_words_on_final words_to_syth_states_def)
        apply (clarsimp simp del: GMN_simps simp add: induced_epi_def words_to_syth_states_def
            states_to_words_def compose_def)
        apply (rule meta_mp[of "(SOME w. w \<in> A\<^sup>\<star> \<and> (\<delta>\<^sup>\<star>) i w = s) \<in> L"])
         apply (smt (verit) induced_epi_wd1 is_recognised someI)
        using fin_states_rep_by_lang is_reachable mem_Collect_eq
        by (metis (mono_tags, lifting))
       apply (clarsimp simp del: GMN_simps)
       apply (simp add: H_1)
      using induced_epi_eq_var
      by blast
    by (simp add: H_2)
qed

end

lemma (in det_G_aut) finite_reachable:
  "finite (orbits G S \<psi>) \<Longrightarrow> finite (orbits G S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h)"
proof-
  assume
    A_0: "finite (orbits G S \<psi>)"
  have H_0: "S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<subseteq> S" 
    apply (clarsimp simp add: reachable_states_def) 
    by (simp add: in_listsI is_aut.give_input_closed is_aut.init_state_is_a_state)
  have H_1: "{{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h} \<subseteq>
    {{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S}"
    by (smt (verit, best) Collect_mono_iff H_0 subsetD)
  have H_2: "\<And>x. x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<Longrightarrow>
     {\<psi> g x |g. g \<in> carrier G} = {\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g x |g. g \<in> carrier G}"
    using reachable_action_is_restict
    by (metis)
  hence H_3: "{{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h} =
    {{\<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h g x |g. g \<in> carrier G} |x. x \<in> S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h}" 
    by blast
  show "finite (orbits G S\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h \<psi>\<^sub>r\<^sub>e\<^sub>a\<^sub>c\<^sub>h)"
    using A_0 apply (clarsimp simp add: orbits_def orbit_def)
    using Finite_Set.finite_subset H_1 H_3
    by auto
qed

lemma (in det_G_aut)
  orbs_pos_card: "finite (orbits G S \<psi>) \<Longrightarrow> card (orbits G S \<psi>) > 0"
  apply (clarsimp simp add: card_gt_0_iff orbits_def)
  using is_aut.init_state_is_a_state
  by auto

lemma (in reach_det_G_aut_rec_lang) MN_B2T:
  assumes
    Fin: "finite (orbits G S \<psi>)"
  shows
    "finite (orbits G (language.MN_equiv A L) (([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)))"
proof- 
  have H_0: "finite {{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S}"
    using Fin
    by (auto simp add: orbits_def orbit_def)
  have H_1: "induced_epi ` S = MN_equiv"
    using reach_det_G_aut_rec_lang
    by (auto simp del: GMN_simps simp add: G_aut_epi_def G_aut_epi_axioms_def)
  have H_2: "\<And>B f. finite B \<Longrightarrow> finite {f b| b. b \<in> B} "
    by auto
  have H_3: "finite {{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S} \<Longrightarrow>
      finite {induced_epi ` b |b. b \<in> {{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S}}"
    using H_2[where f1 = "(\<lambda>x. induced_epi ` x)" and B1 = "{{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S}"]
    by auto
  have H_4: "\<And>s. s \<in> S \<Longrightarrow> \<exists>b. {induced_epi (\<psi> g s) |g. g \<in> carrier G}
              = {y. \<exists>x\<in>b. y = induced_epi x} \<and> (\<exists>x. b = {\<psi> g x |g. g \<in> carrier G} \<and> x \<in> S)"
  proof-
    fix s
    assume
      A2_0: "s \<in> S"
    have H2_0: "{induced_epi (\<psi> g s) |g. g \<in> carrier G} = {y. \<exists>x \<in> {\<psi> g s |g. g \<in> carrier G}. y =
    induced_epi x}"
      by blast
    have H2_1: "(\<exists>x. {\<psi> g s |g. g \<in> carrier G} = {\<psi> g x |g. g \<in> carrier G} \<and> x \<in> S)"
      using A2_0 
      by auto
    show "\<exists>b. {induced_epi (\<psi> g s) |g. g \<in> carrier G} =
    {y. \<exists>x\<in>b. y = induced_epi x} \<and> (\<exists>x. b = {\<psi> g x |g. g \<in> carrier G} \<and> x \<in> S)"
      using A2_0 H2_0 H2_1 
      by meson
  qed
  have H_5: "{induced_epi ` b |b. b \<in> {{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S}} =
  {{induced_epi (\<psi> g s) | g . g \<in> carrier G} |s. s \<in> S}"
    apply (clarsimp simp add: image_def)
    apply (rule subset_antisym; simp add: Set.subset_eq; clarify)
     apply auto[1]
    apply (simp)
    by (simp add: H_4)
  from H_3 H_5 have H_6: "finite {{\<psi> g x |g. g \<in> carrier G} |x. x \<in> S} \<Longrightarrow>
      finite {{induced_epi (\<psi> g s) | g . g \<in> carrier G} |s. s \<in> S}"
    by metis
  have H_7: "finite {{induced_epi (\<psi> g x) |g. g \<in> carrier G} |x. x \<in> S}"
    apply (rule H_6)
    by (simp add: H_0)
  have H_8: "\<And>x. x \<in> S \<Longrightarrow> {induced_epi (\<psi> g x) |g. g \<in> carrier G} =
  {([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (induced_epi x) |g. g \<in> carrier G}"
    using induced_epi_eq_var
    apply (simp del: GMN_simps add: eq_var_func_def eq_var_func_axioms_def make_op_def)
    by blast
  hence H_9: "{{induced_epi (\<psi> g x) |g. g \<in> carrier G} |x. x \<in> S} =
  {{([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (induced_epi x) |g. g \<in> carrier G} |x. x \<in> S}"
    by blast
  have H_10: "\<And>f g X B C. g ` B = C \<Longrightarrow>
             {{f x (g b)|x. x\<in>X}|b. b \<in> B} = {{f x c|x. x \<in> X}|c. c \<in> C}"
    by auto
  have H_11: "{{([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g (induced_epi x) |g. g \<in> carrier G} |x. x \<in> S} =
  {{([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g W |g. g \<in> carrier G} |W. W \<in> MN_equiv}"
    apply (rule H_10[where f2 = "([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)" and X2 = "carrier G" and g2 = induced_epi
          and B2 = S and C2 = MN_equiv])
    using H_1
    by simp
  have H_12: "{{([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>) g W |g. g \<in> carrier G} |W. W \<in> MN_equiv} =
  orbits G (language.MN_equiv A L) (([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>))"
    by (auto simp add: orbits_def orbit_def)
  show "finite (orbits G (language.MN_equiv A L) (([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)))"
    using H_9 H_11 H_12 H_7
    by presburger
qed

context det_G_aut_rec_lang begin

text \<open>
To avoid duplicate variant of "star":
\<close>

no_adhoc_overloading
  star labels_a_G_set.induced_star_map

end

context det_G_aut_rec_lang begin
adhoc_overloading
  star labels_a_G_set.induced_star_map
end


lemma (in det_G_aut_rec_lang) MN_prep:
  "\<exists>S'. \<exists>\<delta>'. \<exists>F'. \<exists>\<psi>'.
  (reach_det_G_aut_rec_lang A S' i F' \<delta>' G \<phi> \<psi>' L \<and>
  (finite (orbits G S \<psi>) \<longrightarrow> finite (orbits G S' \<psi>')))"
  by (meson G_lang_axioms finite_reachable reach_det_G_aut_rec_lang.intro
      reach_det_aut_is_det_aut_rec_L)

lemma (in det_G_aut_rec_lang) MN_fin_orbs_imp_fin_states:
  assumes
    Fin: "finite (orbits G S \<psi>)"
  shows
    "finite (orbits G (language.MN_equiv A L) (([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)))"
  using MN_prep 
  by (metis assms reach_det_G_aut_rec_lang.MN_B2T)

text \<open>
The following theorem corresponds to theorem 3.8 from \cite{bojanczyk2014automata}, i.e. the
Myhill-Nerode theorem for G-automata.
The left to right direction (see statement below) of the typical Myhill-Nerode theorem would
qantify over types (if some condition holds, then there exists some automaton accepting the
language). As it is not possible to qantify over types in this way, the equivalence is spit into
two directions. In the left to right direction, the explicit type of the syntactic automaton is
used. In the right to left direction some type, 's, is fixed.
As the two directions are split, the opertunity was taken to strengthen the right to left direction:
We do not assume the given automaton is reachable.

This splitting of the directions will be present in all other Myhill-Nerode theorems that will be
proved in this document.
\<close>

theorem (in G_lang) G_Myhill_Nerode :
  assumes
    "finite (orbits G A \<phi>)"
  shows
    G_Myhill_Nerode_LR: "finite (orbits G MN_equiv ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)) \<Longrightarrow>
     (\<exists>S F :: 'alpha list set set. \<exists>i :: 'alpha list set. \<exists>\<delta>. \<exists>\<psi>.
     reach_det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L \<and> finite (orbits G S \<psi>))" and
    G_Myhill_Nerode_RL: "(\<exists>S F :: 's set. \<exists>i :: 's. \<exists>\<delta>. \<exists>\<psi>.
     det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L \<and> finite (orbits G S \<psi>))
     \<Longrightarrow> finite (orbits G MN_equiv ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>))"
  subgoal
    using syntact_aut_is_reach_aut_rec_lang 
    by blast
  by (metis det_G_aut_rec_lang.MN_fin_orbs_imp_fin_states)

subsection \<open>
Proving the standard Myhill-Nerode Theorem
\<close>

text \<open>
Any automaton is a $G$-automaton with respect to the trivial group and action,
hence the standard Myhill-Nerode theorem is a special case of the $G$-Myhill-Nerode theorem.
\<close>

interpretation triv_act:
  alt_grp_act "singleton_group (undefined)" X "(\<lambda>x \<in> {undefined}. one (BijGroup X))"
  apply (simp add: group_action_def group_hom_def group_hom_axioms_def)
  apply (intro conjI)
   apply (simp add: group_BijGroup)
  using trivial_hom 
  by (smt (verit) carrier_singleton_group group.hom_restrict group_BijGroup restrict_apply
      singleton_group)

lemma (in det_aut) triv_G_aut:
  fixes triv_G
  assumes H_triv_G: "triv_G = (singleton_group (undefined))"
  shows "det_G_aut labels states init_state fin_states \<delta> 
  triv_G (\<lambda>x \<in> {undefined}. one (BijGroup labels)) (\<lambda>x \<in> {undefined}. one (BijGroup states))"
  apply (simp add: det_G_aut_def group_hom_def group_hom_axioms_def
      eq_var_subset_def eq_var_subset_axioms_def eq_var_func_def eq_var_func_axioms_def)
  apply (intro conjI)
             apply (rule det_aut_axioms)
            apply (simp add: assms triv_act.group_action_axioms)+
  using fin_states_are_states
          apply (auto)[1]
         apply (clarify; rule conjI; rule impI)
          apply (simp add: H_triv_G BijGroup_def image_def)
  using fin_states_are_states
          apply auto[1]
         apply (simp add: H_triv_G BijGroup_def image_def)
        apply (simp add: assms triv_act.group_action_axioms)
       apply (simp add: init_state_is_a_state)
      apply (clarify; rule conjI; rule impI)
       apply (simp add: H_triv_G BijGroup_def image_def init_state_is_a_state)+ 
     apply (clarsimp simp add: group_action_def BijGroup_def hom_def group_hom_def
      group_hom_axioms_def)
     apply (rule conjI)
      apply (smt (verit) BijGroup_def Bij_imp_funcset Id_compose SigmaE case_prod_conv
      group_BijGroup id_Bij restrict_ext restrict_extensional)
     apply (rule meta_mp[of "undefined \<otimes>\<^bsub>singleton_group undefined\<^esub> undefined = undefined"])
      apply (auto)[1]
     apply (metis carrier_singleton_group comm_groupE(1) singletonD singletonI
      singleton_abelian_group)
    apply (simp add: assms triv_act.group_action_axioms)
   apply (auto simp add: trans_func_well_def)[1] 
  by (clarsimp simp add: BijGroup_def trans_func_well_def H_triv_G) 

lemma triv_orbits:
  "orbits (singleton_group (undefined)) S (\<lambda>x \<in> {undefined}. one (BijGroup S)) =
   {{s} |s. s \<in> S}"
  apply (simp add: BijGroup_def singleton_group_def orbits_def orbit_def)
  by auto

lemma fin_triv_orbs:
  "finite (orbits (singleton_group (undefined)) S (\<lambda>x \<in> {undefined}. one (BijGroup S))) = finite S"
  apply (subst triv_orbits)
  apply (rule meta_mp[of "bij_betw (\<lambda>s \<in> S. {s}) S {{s} |s. s \<in> S}"])
  using bij_betw_finite
   apply (auto)[1]
  by (auto simp add: bij_betw_def image_def)

context language begin

interpretation triv_G_lang:
  G_lang "singleton_group (undefined)" A "(\<lambda>x \<in> {undefined}. one (BijGroup A))" L
  apply (simp add: G_lang_def G_lang_axioms_def eq_var_subset_def eq_var_subset_axioms_def)
  apply (intro conjI)
      apply (simp add: triv_act.group_action_axioms)
     apply (simp add: language_axioms)
  using triv_act.lists_a_Gset
    apply fastforce
   apply (rule is_lang)
  apply (clarsimp simp add: BijGroup_def image_def)
  apply (rule subset_antisym; simp add: Set.subset_eq; clarify)
  using is_lang
   apply (auto simp add: map_idI)[1] 
  using is_lang map_idI 
  by (metis in_listsD in_mono inf.absorb_iff1 restrict_apply)

definition triv_G :: "'grp monoid"
  where "triv_G = (singleton_group (undefined))"

definition triv_act :: "'grp \<Rightarrow> 'alpha \<Rightarrow> 'alpha"
  where "triv_act = (\<lambda>x \<in> {undefined}. \<one>\<^bsub>BijGroup A\<^esub>)"

corollary standard_Myhill_Nerode:
  assumes
    H_fin_alph: "finite A"
  shows
    standard_Myhill_Nerode_LR: "finite MN_equiv \<Longrightarrow>
     (\<exists>S F :: 'alpha list set set. \<exists>i :: 'alpha list set. \<exists>\<delta>.
     reach_det_aut_rec_lang A S i F \<delta> L \<and> finite S)" and
    standard_Myhill_Nerode_RL: "(\<exists>S F :: 's set. \<exists>i :: 's. \<exists>\<delta>.
     det_aut_rec_lang A S i F \<delta> L \<and> finite S) \<Longrightarrow> finite MN_equiv"
proof-
  assume
    A_0: "finite MN_equiv"
  have H_0: "reach_det_aut_rec_lang A MN_equiv MN_init_state MN_fin_states \<delta>\<^sub>M\<^sub>N L"
    using triv_G_lang.syntact_aut_is_reach_aut_rec_lang
    apply (clarsimp simp add: reach_det_G_aut_rec_lang_def det_G_aut_rec_lang_def
        reach_det_aut_rec_lang_def reach_det_aut_def reach_det_aut_axioms_def det_G_aut_def)
    by (smt (z3) alt_natural_map_MN_def quotientE triv_G_lang.MN_unique_init_state)
  show "\<exists>S F:: 'alpha list set set. \<exists>i :: 'alpha list set. \<exists>\<delta>.
  reach_det_aut_rec_lang A S i F \<delta> L \<and> finite S"
    using A_0 H_0 
    by auto
next
  assume
    A_0: "\<exists>S F:: 's set. \<exists>i :: 's. \<exists>\<delta>. det_aut_rec_lang A S i F \<delta> L \<and> finite S"
  obtain S F :: "'s set" and i :: "'s"  and \<delta>
    where H_MN: "det_aut_rec_lang A S i F \<delta> L \<and> finite S"
    using A_0
    by auto
  have H_0: "det_G_aut A S i F \<delta> triv_G (\<lambda>x\<in>{undefined}. \<one>\<^bsub>BijGroup A\<^esub>)
   (\<lambda>x\<in>{undefined}. \<one>\<^bsub>BijGroup S\<^esub>)"
    apply (rule det_aut.triv_G_aut[of A S i F \<delta> triv_G])
    using H_MN
     apply (simp add: det_aut_rec_lang_def)
    by (rule triv_G_def)
  have H_1: "det_G_aut_rec_lang A S i F \<delta> triv_G (\<lambda>x\<in>{undefined}. \<one>\<^bsub>BijGroup A\<^esub>)
   (\<lambda>x\<in>{undefined}. \<one>\<^bsub>BijGroup S\<^esub>) L"
    by (auto simp add: det_G_aut_rec_lang_def H_0 H_MN)
  have H_2: "(\<exists>S F:: 's set. \<exists>i :: 's. \<exists>\<delta> \<psi>.
         det_G_aut_rec_lang A S i F \<delta> (singleton_group undefined) (\<lambda>x\<in>{undefined}. \<one>\<^bsub>BijGroup A\<^esub>)
         \<psi> L \<and> finite (orbits (singleton_group undefined) S \<psi>))"
    using H_1
    by (metis H_MN fin_triv_orbs triv_G_def)
  have H_3: "finite (orbits triv_G A triv_act)"
    apply (subst triv_G_def; subst triv_act_def; subst fin_triv_orbs[of A])
    by (rule H_fin_alph)
  have H_4:"finite (orbits triv_G MN_equiv (triv_act.induced_quot_map (A\<^sup>\<star>)
     (triv_act.induced_star_map A triv_act) \<equiv>\<^sub>M\<^sub>N))"
    using H_3
    apply (simp add: triv_G_def triv_act_def del: GMN_simps)
    using triv_G_lang.G_Myhill_Nerode H_2
    by blast    
  have H_5:"triv_act.induced_star_map A triv_act = (\<lambda>x \<in> {undefined}. \<one>\<^bsub>BijGroup (A\<^sup>\<star>)\<^esub>)"
    apply (simp add: BijGroup_def restrict_def fun_eq_iff triv_act_def)
    by (clarsimp simp add: list.map_ident_strong)
  have H_6: "(triv_act.induced_quot_map (A\<^sup>\<star>) (triv_act.induced_star_map A
  triv_act) \<equiv>\<^sub>M\<^sub>N) = (\<lambda>x \<in> {undefined}. \<one>\<^bsub>BijGroup MN_equiv\<^esub>)"
    apply (subst H_5)
    apply (simp add: BijGroup_def fun_eq_iff Image_def)
    apply (rule allI; rule conjI; intro impI)
     apply (smt (verit) Collect_cong Collect_mem_eq Eps_cong MN_rel_equival equiv_Eps_in
        in_quotient_imp_closed quotient_eq_iff)
    using MN_rel_equival equiv_Eps_preserves
    by auto
  show "finite MN_equiv"
    apply (subst fin_triv_orbs [symmetric]; subst H_6 [symmetric]; subst triv_G_def [symmetric])
    by (rule H_4)
qed
end

section \<open>
Myhill-Nerode Theorem for Nominal $G$-Automata
\<close>

subsection \<open>
Data Symmetries, Supports and Nominal Actions
\<close>

text \<open>
The following locale corresponds to the definition 2.2 from \cite{bojanczyk2014automata}.
Note that we let $G$ be an arbitrary group instead of a subgroup of \texttt{BijGroup} $D$,
but assume there is a homomoprhism $\pi: G \to \texttt{BijGroup} D$.
By \texttt{group\_hom.img\_is\_subgroup} this is an equivalent definition:
\<close>

locale data_symm = group_action G D \<pi>
  for 
    G :: "('grp, 'b) monoid_scheme" and
    D :: "'D set" ("\<bbbD>") and
    \<pi> 

text \<open>
The following locales corresponds to definition 4.3 from \cite{bojanczyk2014automata}:
\<close>

locale supports = data_symm G D \<pi> + alt_grp_act G X \<phi> 
  for
    G :: "('grp, 'b) monoid_scheme" and
    D :: "'D set" ("\<bbbD>") and
    \<pi> and
    X :: "'X set" (structure) and
    \<phi> +
  fixes
    C :: "'D set" and
    x :: "'X"
  assumes
    is_in_set:
    "x \<in> X" and
    is_subset:
    "C \<subseteq> \<bbbD>" and
    supports:
    "g \<in> carrier G \<Longrightarrow> (\<forall>c. c \<in> C \<longrightarrow> \<pi> g c = c) \<Longrightarrow> x \<odot>\<^bsub>\<phi>\<^esub> g = x"
begin

text \<open>
The following lemma corresponds to lemma 4.9 from \cite{bojanczyk2014automata}:
\<close>

lemma image_supports:
  "\<And>g. g \<in> carrier G \<Longrightarrow> supports G D \<pi> X \<phi> (\<pi> g ` C) (x \<odot>\<^bsub>\<phi>\<^esub> g)"
proof-
  fix g
  assume 
    A_0: "g \<in> carrier G"
  have H_0: "\<And>h. data_symm G \<bbbD> \<pi> \<Longrightarrow>
         group_action G X \<phi> \<Longrightarrow>
         x \<in> X \<Longrightarrow>
         C \<subseteq> \<bbbD> \<Longrightarrow>
         \<forall>g. g \<in> carrier G \<longrightarrow> (\<forall>c. c \<in> C \<longrightarrow> \<pi> g c = c) \<longrightarrow> \<phi> g x = x \<Longrightarrow>
         h \<in> carrier G \<Longrightarrow> \<forall>c. c \<in> \<pi> g ` C \<longrightarrow> \<pi> h c = c \<Longrightarrow>
         \<phi> h (\<phi> g x) = \<phi> g x"
  proof-
    fix h
    assume
      A1_0: "data_symm G \<bbbD> \<pi>" and
      A1_1: "group_action G X \<phi>" and
      A1_2: "\<forall>g. g \<in> carrier G \<longrightarrow> (\<forall>c. c \<in> C \<longrightarrow> \<pi> g c = c) \<longrightarrow> \<phi> g x = x" and
      A1_3: "h \<in> carrier G" and
      A1_4: "\<forall>c. c \<in> \<pi> g ` C \<longrightarrow> \<pi> h c = c"
    have H1_0: "\<And>g. g \<in> carrier G \<Longrightarrow> (\<forall>c. c \<in> C \<longrightarrow> \<pi> g c = c) \<Longrightarrow> \<phi> g x = x"
      using A1_2
      by auto 
    have H1_1: "\<forall>c. c \<in> C \<longrightarrow> \<pi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h \<otimes>\<^bsub>G\<^esub> g) c = c \<Longrightarrow>
    \<phi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h \<otimes>\<^bsub>G\<^esub> g) x = x"
      apply (rule H1_0[of "((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h \<otimes>\<^bsub>G\<^esub> g)"])
       apply (meson A_0 A1_3 group.subgroupE(3) group.subgroup_self group_hom group_hom.axioms(1)
          subgroup.m_closed)
      by simp
    have H2: "\<pi> (((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h) \<otimes>\<^bsub>G\<^esub> g) = compose \<bbbD> (\<pi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h)) (\<pi> g)"
      using A1_0
      apply (clarsimp simp add: data_symm_def group_action_def BijGroup_def group_hom_def
          group_hom_axioms_def hom_def restrict_def)
      apply (rule meta_mp[of "\<pi> g \<in> Bij \<bbbD> \<and> \<pi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h) \<in> Bij \<bbbD>"])
       apply (smt (verit) A_0 A1_3 data_symm.axioms data_symm_axioms group.inv_closed
          group.surj_const_mult group_action.bij_prop0 image_eqI)
      apply (rule conjI)
      using A_0
       apply blast
      by (meson A_0 A1_3 data_symm.axioms data_symm_axioms group.subgroupE(3) group.subgroupE(4)
          group.subgroup_self group_action.bij_prop0)
    also have H1_3: "... = compose \<bbbD> (compose \<bbbD> (\<pi> (inv\<^bsub>G\<^esub> g) ) (\<pi> h)) (\<pi> g)"
      using A1_0
      apply (clarsimp simp add: data_symm_def group_action_def BijGroup_def comp_def
          group_hom_def group_hom_axioms_def hom_def restrict_def)
      apply (rule meta_mp[of "\<pi> (inv\<^bsub>G\<^esub> g) \<in> Bij \<bbbD> \<and> \<pi> h \<in> Bij \<bbbD>"])
       apply (simp add: A_0 A1_3)
      apply (rule conjI)
       apply (simp add: A_0 Pi_iff)
      using A1_3
      by blast
    also have H1_4: "... = compose \<bbbD> ((\<pi> (inv\<^bsub>G\<^esub> g)) \<circ> (\<pi> h)) (\<pi> g)"
      using A1_0
      apply (clarsimp simp add: data_symm_def group_action_def BijGroup_def comp_def group_hom_def
          group_hom_axioms_def hom_def restrict_def compose_def)
      using A_0 A1_3  
      by (meson data_symm.axioms data_symm_axioms group.inv_closed group_action.element_image)
    also have H1_5: "... = (\<lambda>d \<in> \<bbbD>. ((\<pi> (inv\<^bsub>G\<^esub> g)) \<circ> (\<pi> h) \<circ> (\<pi> g)) d)"
      by (simp add: compose_def)
    have H1_6: "\<And>c. c \<in> C \<Longrightarrow> ((\<pi> h) \<circ> (\<pi> g)) c = (\<pi> g) c"
      using A1_4
      by auto
    have H1_7: "\<And>c. c \<in> C \<Longrightarrow> ((\<pi> (inv\<^bsub>G\<^esub> g)) \<circ> (\<pi> h) \<circ> (\<pi> g)) c = c"
      using H1_6 A1_0
      apply (simp add: data_symm_def group_action_def BijGroup_def compose_def group_hom_def
          group_hom_axioms_def hom_def)
      by (meson A_0 data_symm.axioms data_symm_axioms group_action.orbit_sym_aux is_subset subsetD)
    have H1_8: "\<forall>c. c \<in> C \<longrightarrow> \<pi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h \<otimes>\<^bsub>G\<^esub> g) c = c"
      using H1_7 H1_5
      by (metis calculation is_subset restrict_apply' subsetD)
    have H1_9: "\<phi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h \<otimes>\<^bsub>G\<^esub> g) x = x"
      using H1_8
      by (simp add: H1_1)
    hence H1_10: "\<phi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> h \<otimes>\<^bsub>G\<^esub> g) x = \<phi> ((inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>G\<^esub> (h \<otimes>\<^bsub>G\<^esub> g)) x"
      by (smt (verit, ccfv_SIG) A_0 A1_3 group.inv_closed group.subgroupE(4) group.subgroup_self
          group_action.composition_rule group_action.element_image group_action_axioms group_hom
          group_hom.axioms(1) is_in_set)
    have H1_11: "... = ((\<phi> (inv\<^bsub>G\<^esub> g)) \<circ> (\<phi> (h \<otimes>\<^bsub>G\<^esub> g))) x"
      using A_0 A1_3 group.subgroupE(4) group.subgroup_self group_action.composition_rule
        group_action_axioms group_hom group_hom.axioms(1) is_in_set
      by fastforce
    have H1_12: "... = ((the_inv_into X (\<phi> g)) \<circ> (\<phi> (h \<otimes>\<^bsub>G\<^esub> g))) x"
      using A1_1
      apply (simp add: group_action_def)
      by (smt (verit) A_0 A1_3 group.inv_closed group.subgroupE(4) group.subgroup_self
          group_action.element_image group_action.inj_prop group_action.orbit_sym_aux
          group_action_axioms group_hom.axioms(1) is_in_set the_inv_into_f_f)
    have H1_13: "((the_inv_into X (\<phi> g)) \<circ> (\<phi> (h \<otimes>\<^bsub>G\<^esub> g))) x = x" 
      using H1_9 H1_10 H1_11 H1_12
      by auto
    hence H1_14: "(\<phi> (h \<otimes>\<^bsub>G\<^esub> g)) x = \<phi> g x"
      using H1_13
      by (metis A_0 A1_3 comp_apply composition_rule element_image f_the_inv_into_f inj_prop is_in_set
          surj_prop)
    show "\<phi> h (\<phi> g x) = \<phi> g x"
      using A1_3 A1_2 A_0 H1_14 composition_rule
      by (simp add: is_in_set)
  qed
  show "supports G D \<pi> X \<phi> (\<pi> g ` C) (x \<odot>\<^bsub>\<phi>\<^esub> g)"
    using supports_axioms
    apply (clarsimp simp add: supports_def supports_axioms_def)
    apply (intro conjI)
    using element_image is_in_set A_0
      apply blast
     apply (metis A_0 data_symm_def group_action.surj_prop image_mono is_subset)
    apply (rule allI; intro impI)
    apply (rename_tac h)
    by (simp add: H_0)
qed
end

locale nominal = data_symm G D \<pi> + alt_grp_act G X \<phi>
  for
    G :: "('grp, 'b) monoid_scheme" and
    D :: "'D set" ("\<bbbD>") and
    \<pi> and
    X :: "'X set" (structure) and
    \<phi> +
  assumes
    is_nominal:
    "\<And>g x. g \<in> carrier G \<Longrightarrow> x \<in> X \<Longrightarrow> \<exists>C. C \<subseteq> \<bbbD> \<and> finite C \<and> supports G \<bbbD> \<pi> X \<phi> C x"

locale nominal_det_G_aut = det_G_aut + 
  nominal G D \<pi> A \<phi> + nominal G D \<pi> S \<psi>
  for
    D :: "'D set" ("\<bbbD>") and
    \<pi> 

text \<open>
The following lemma corresponds to lemma 4.8 from \cite{bojanczyk2014automata}:
\<close>

lemma (in eq_var_func) supp_el_pres:
  "supports G D \<pi> X \<phi> C x \<Longrightarrow> supports G D \<pi> Y \<psi> C (f x)"
  apply (clarsimp simp add: supports_def supports_axioms_def)
  apply (rule conjI)
  using eq_var_func_axioms
   apply (simp add: eq_var_func_def eq_var_func_axioms_def)
  apply (intro conjI)
  using is_ext_func_bet 
   apply blast
  apply clarify
  by (metis is_eq_var_func')

lemma (in nominal) support_union_lem:
  fixes f sup_C col
  assumes H_f: "f = (\<lambda>x. (SOME C. C \<subseteq> \<bbbD> \<and> finite C \<and> supports G \<bbbD> \<pi> X \<phi> C x))"
    and H_col: "col \<subseteq> X \<and> finite col"
    and H_sup_C: "sup_C = \<Union>{Cx. Cx \<in> f ` col}"
  shows "\<And>x. x \<in> col \<Longrightarrow> sup_C \<subseteq> \<bbbD> \<and> finite sup_C \<and> supports G \<bbbD> \<pi> X \<phi> sup_C x"
proof - 
  fix x
  assume A_0: "x \<in> col"
  have H_0: "\<And>x. x \<in> X \<Longrightarrow> \<exists>C. C \<subseteq> \<bbbD> \<and> finite C \<and> supports G \<bbbD> \<pi> X \<phi> C x"
    using nominal_axioms 
    apply (clarsimp simp add: nominal_def nominal_axioms_def)
    using stabilizer_one_closed stabilizer_subset 
    by blast
  have H_1: "\<And>x. x \<in> col \<Longrightarrow> f x \<subseteq> \<bbbD> \<and> finite (f x) \<and> supports G \<bbbD> \<pi> X \<phi> (f x) x"
    apply (subst H_f)
    using someI_ex H_col H_f H_0
    by (metis (no_types, lifting) in_mono)
  have H_2: "sup_C \<subseteq> \<bbbD>"
    using H_1 
    by (simp add: H_sup_C UN_least)
  have H_3: "finite sup_C"
    using H_1 H_col H_sup_C
    by simp
  have H_4: "f x \<subseteq> sup_C"
    using H_1 H_sup_C A_0
    by blast
  have H_5: "\<And>g c. \<lbrakk>g \<in> carrier G; (c \<in> sup_C \<longrightarrow> \<pi> g c = c); c \<in> (f x)\<rbrakk> \<Longrightarrow> \<pi> g c = c"
    using H_4 H_1 A_0
    by (auto simp add: image_def supports_def supports_axioms_def) 
  have H_6: "supports G \<bbbD> \<pi> X \<phi> sup_C x"
    apply (simp add: supports_def supports_axioms_def)
    apply (intro conjI)
        apply (simp add: data_symm_axioms)
    using A_0 H_1 supports.axioms(2)
       apply fastforce
    using H_col A_0
      apply blast
     apply (rule H_2)
    apply (clarify)
    using supports_axioms_def[of G D \<pi> X \<phi> sup_C]
    apply (clarsimp)
    using H_1 A_0
    apply (clarsimp simp add: supports_def supports_axioms_def)
    using A_0 H_5
    by presburger
  show "sup_C \<subseteq> \<bbbD> \<and> finite sup_C \<and> supports G \<bbbD> \<pi> X \<phi> sup_C x"
    using H_2 H_3 H_6 by auto
qed

lemma (in nominal) set_of_list_nom:
  "nominal G D \<pi> (X\<^sup>\<star>) (\<phi>\<^sup>\<star>)"
proof-
  have H_0: "\<And>g x. g \<in> carrier G \<Longrightarrow> \<forall>x\<in>set x. x \<in> X \<Longrightarrow>
            \<exists>C\<subseteq>\<bbbD>. finite C \<and> supports G \<bbbD> \<pi> (X\<^sup>\<star>) (\<phi>\<^sup>\<star>) C x"
  proof-
    fix g w
    assume
      A1_0: "g \<in> carrier G" and
      A1_1: "\<forall>x\<in>set w. x \<in> X"
    have H1_0: "\<And>x. x \<in> X \<Longrightarrow> \<exists>C\<subseteq>\<bbbD>. finite C \<and> supports G \<bbbD> \<pi> X \<phi> C x"
      using A1_0 is_nominal by force
    define f where H1_f: "f = (\<lambda>x. (SOME C. C \<subseteq> \<bbbD> \<and>  finite C \<and> supports G \<bbbD> \<pi> X \<phi> C x))"
    define sup_C :: "'D set " where H1_sup_C: "sup_C = \<Union>{Cx. Cx \<in> f ` set w}"
    have H1_1: "\<And>x. x \<in> set w \<Longrightarrow> sup_C \<subseteq> \<bbbD> \<and> finite sup_C \<and> supports G \<bbbD> \<pi> X \<phi> sup_C x"
      apply (rule support_union_lem[where f = f and col = "set w"])
         apply (rule H1_f)
      using A1_0
        apply (simp add: A1_1 subset_code(1))
       apply (rule H1_sup_C)
      by simp
    have H1_2: "supports G \<bbbD> \<pi> (X\<^sup>\<star>) (\<phi>\<^sup>\<star>) sup_C w"
      apply (clarsimp simp add: supports_def supports_axioms_def simp del: GMN_simps)
      apply (intro conjI) 
          apply (simp add: data_symm_axioms)
      using lists_a_Gset
         apply (auto)[1]
        apply (simp add: A1_1 in_listsI)
      using H1_1 H1_sup_C
       apply blast
      apply (rule allI; intro impI)
      apply clarsimp
      apply (rule conjI)
      using H1_1
      by (auto simp add: supports_def supports_axioms_def map_idI)
    show "\<exists>C\<subseteq>\<bbbD>. finite C \<and> supports G \<bbbD> \<pi> (X\<^sup>\<star>) (\<phi>\<^sup>\<star>) C w"
      using nominal_axioms_def
      apply (clarsimp simp add: nominal_def simp del: GMN_simps)
      using H1_1 H1_2
      by (metis Collect_empty_eq H1_sup_C Union_empty empty_iff image_empty infinite_imp_nonempty
          subset_empty subset_emptyI supports.is_subset)
  qed
  show ?thesis
    apply (clarsimp simp add: nominal_def nominal_axioms_def simp del: GMN_simps)
    apply (intro conjI)
    using group.subgroupE(2) group.subgroup_self group_hom group_hom.axioms(1)
      apply (simp add: data_symm_axioms)
     apply (rule lists_a_Gset)
    apply (clarify)
    by (simp add: H_0 del: GMN_simps)
qed

subsection \<open>
Proving the Myhill-Nerode Theorem for Nominal $G$-Automata
\<close>

context det_G_aut begin
adhoc_overloading
  star labels_a_G_set.induced_star_map
end

lemma (in det_G_aut) input_to_init_eqvar:
  "eq_var_func G (A\<^sup>\<star>) (\<phi>\<^sup>\<star>) S \<psi> (\<lambda>w\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w)"
proof-
  have H_0: "\<And>a g. \<lbrakk>\<forall>x\<in>set a. x \<in> A; map (\<phi> g) a \<in> A\<^sup>\<star>; g \<in> carrier G\<rbrakk> \<Longrightarrow>
            (\<delta>\<^sup>\<star>) i (map (\<phi> g) a) = \<psi> g ((\<delta>\<^sup>\<star>) i a)"
  proof-
    fix w g
    assume
      A1_0: "\<forall>x\<in>set w. x \<in> A" and
      A1_1: "map (\<phi> g) w \<in> A\<^sup>\<star>" and
      A1_2: "g \<in> carrier G"
    have H1_0: "(\<delta>\<^sup>\<star>) (\<psi> g i) (map (\<phi> g) w) = \<psi> g ((\<delta>\<^sup>\<star>) i w)"
      using give_input_eq_var
      apply (clarsimp simp add: eq_var_func_axioms_def eq_var_func_def)
      using A1_0 A1_1 A1_2 in_listsI is_aut.init_state_is_a_state states_a_G_set.element_image 
      by (smt (verit, del_insts))
    have H1_1: "(\<psi> g i) = i"
      using A1_2 is_aut.init_state_is_a_state init_is_eq_var.is_equivar
      by force
    show "(\<delta>\<^sup>\<star>) i (map (\<phi> g) w) = \<psi> g ((\<delta>\<^sup>\<star>) i w)"
      using H1_0 H1_1
      by simp
  qed
  show ?thesis
    apply (clarsimp simp add: eq_var_func_def eq_var_func_axioms_def)
    apply (intro conjI)
    using labels_a_G_set.lists_a_Gset
       apply fastforce
      apply (simp add: states_a_G_set.group_action_axioms del: GMN_simps)
     apply (simp add: in_listsI is_aut.give_input_closed is_aut.init_state_is_a_state)
    apply clarify
    apply (rule conjI; intro impI)
     apply (simp add: H_0)
    using labels_a_G_set.surj_prop
    by fastforce
qed

lemma (in reach_det_G_aut) input_to_init_surj:
  "(\<lambda>w\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w) ` (A\<^sup>\<star>) = S" 
  using reach_det_G_aut_axioms
  apply (clarsimp simp add: image_def reach_det_G_aut_def reach_det_aut_def
      reach_det_aut_axioms_def)
  using is_aut.give_input_closed is_aut.init_state_is_a_state
  by blast

context reach_det_G_aut begin
adhoc_overloading
  star labels_a_G_set.induced_star_map
end

text \<open>
The following lemma corresponds to proposition 5.1 from \cite{bojanczyk2014automata}:
\<close>

proposition (in reach_det_G_aut) alpha_nom_imp_states_nom:
  "nominal G D \<pi> A \<phi> \<Longrightarrow> nominal G D \<pi> S \<psi>"
proof-
  assume
    A_0: "nominal G D \<pi> A \<phi>"
  have H_0: "\<And>g x. \<lbrakk>g \<in> carrier G; data_symm G D \<pi>; group_action G A \<phi>;
             \<forall>x. x \<in> A \<longrightarrow> (\<exists>C\<subseteq>D. finite C \<and> supports G D \<pi> A \<phi> C x); x \<in> S\<rbrakk>
           \<Longrightarrow> \<exists>C\<subseteq>D. finite C \<and> supports G D \<pi> S \<psi> C x"
  proof -
    fix g s
    assume
      A1_0: "g \<in> carrier G" and
      A1_1: "data_symm G D \<pi>" and
      A1_2: "group_action G A \<phi>" and
      A1_3: "\<forall>x. x \<in> A \<longrightarrow> (\<exists>C\<subseteq>D. finite C \<and> supports G D \<pi> A \<phi> C x)" and
      A1_4: "s \<in> S"
    have H1_0: "\<And>x. x \<in> (A\<^sup>\<star>) \<Longrightarrow> \<exists>C\<subseteq>D. finite C \<and> supports G D \<pi> (A\<^sup>\<star>) (\<phi>\<^sup>\<star>) C x"
      using nominal.set_of_list_nom[of G D \<pi> A \<phi>] A1_2
      apply (clarsimp simp add: nominal_def)
      by (metis A1_0 A1_1 A1_3 in_listsI labels_a_G_set.induced_star_map_def nominal_axioms_def)   
    define f where H1_f: "f = (\<lambda>w\<in>A\<^sup>\<star>. (\<delta>\<^sup>\<star>) i w)"      
    obtain w where H1_w0: "s = f w" and H1_w1: "w \<in> (A\<^sup>\<star>)"
      using input_to_init_surj A1_4
      apply (simp add: H1_f image_def)
      by (metis is_reachable)
    obtain C where H1_C: "finite C \<and> supports G D \<pi> (A\<^sup>\<star>) (labels_a_G_set.induced_star_map \<phi>) C w"
      by (meson H1_0 H1_w0 H1_w1)
    have H1_2: "supports G D \<pi> S \<psi> C s"
      apply (subst H1_w0)
      apply (rule eq_var_func.supp_el_pres[where X = "A\<^sup>\<star>" and \<phi> = "\<phi>\<^sup>\<star>"])
       apply (subst H1_f)
       apply (rule det_G_aut.input_to_init_eqvar[of A S i F \<delta> G \<phi> \<psi>])
      using reach_det_G_aut_axioms
       apply (simp add: reach_det_G_aut_def) 
      using H1_C
      by simp
    show "\<exists>C\<subseteq>D. finite C \<and> supports G D \<pi> S \<psi> C s"
      using H1_2 H1_C 
      by (meson supports.is_subset)
  qed
  show ?thesis
    apply (rule meta_mp[of "(\<exists>g. g \<in> carrier G)"])
    subgoal 
      using A_0 apply (clarsimp simp add: nominal_def nominal_axioms_def)
      apply (rule conjI)
      subgoal for g
        by (clarsimp simp add: states_a_G_set.group_action_axioms)
      apply clarify
      by (simp add: H_0)
    by (metis bot.extremum_unique ex_in_conv is_aut.init_state_is_a_state
        states_a_G_set.stabilizer_one_closed states_a_G_set.stabilizer_subset)
qed

text \<open>
The following theorem corresponds to theorem 5.2 from \cite{bojanczyk2014automata}:
\<close>

theorem (in G_lang) Nom_G_Myhill_Nerode:
  assumes
    orb_fin: "finite (orbits G A \<phi>)" and
    nom: "nominal G D \<pi> A \<phi>"
  shows
    Nom_G_Myhill_Nerode_LR: "finite (orbits G MN_equiv ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>)) \<Longrightarrow>
     (\<exists>S F :: 'alpha list set set. \<exists>i :: 'alpha list set. \<exists>\<delta>. \<exists>\<psi>.
     reach_det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L \<and> finite (orbits G S \<psi>)
     \<and> nominal_det_G_aut A S i F \<delta> G \<phi> \<psi> D \<pi>)" and
    Nom_G_Myhill_Nerode_RL: "(\<exists>S F :: 's set. \<exists>i :: 's. \<exists>\<delta>. \<exists>\<psi>.
     det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L \<and> finite (orbits G S \<psi>)
     \<and> nominal_det_G_aut A S i F \<delta> G \<phi> \<psi> D \<pi>)
    \<Longrightarrow> finite (orbits G MN_equiv ([(\<phi>\<^sup>\<star>)]\<^sub>\<equiv>\<^sub>M\<^sub>N \<^bsub>A\<^sup>\<star>\<^esub>))"
proof-
  assume
    A_0: "finite (orbits G MN_equiv ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>))"
  obtain S F :: "'alpha list set set" and i :: "'alpha list set" and \<delta> \<psi>
    where H_MN: "reach_det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L \<and> finite (orbits G S \<psi>)"
    using A_0 orb_fin G_Myhill_Nerode_LR
    by blast
  have H_0: "nominal G D \<pi> S \<psi>"
    using H_MN
    apply (clarsimp simp del: GMN_simps simp add: reach_det_G_aut_rec_lang_def)
    using nom reach_det_G_aut.alpha_nom_imp_states_nom 
    by metis
  show "\<exists>S F :: 'alpha list set set. \<exists>i :: 'alpha list set. \<exists>\<delta>. \<exists>\<psi>.
       reach_det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L \<and>
       finite (orbits G S \<psi>) \<and> nominal_det_G_aut A S i F \<delta> G \<phi> \<psi> D \<pi>"
    apply (simp add: nominal_det_G_aut_def reach_det_G_aut_rec_lang_def)
    using nom H_MN H_0
    apply (clarsimp simp add: reach_det_G_aut_rec_lang_def reach_det_G_aut_def
        reach_det_aut_axioms_def)
    by blast
next
  assume A0: "\<exists>S F i \<delta> \<psi>. det_G_aut_rec_lang A S i F \<delta> G \<phi> \<psi> L \<and> finite (orbits G S \<psi>)
                \<and> nominal_det_G_aut A S i F \<delta> G \<phi> \<psi> D \<pi>"
  show "finite (orbits G MN_equiv ([\<phi>\<^sup>\<star>]\<^sub>\<equiv>\<^sub>M\<^sub>N\<^bsub>A\<^sup>\<star>\<^esub>))"
    using A0 orb_fin
    by (meson G_Myhill_Nerode_RL)
qed
end