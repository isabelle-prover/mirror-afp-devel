section \<open>Cardinality and Finiteness\<close>

theory Cardinality
  imports Exponential_Objects
begin

text \<open>The definitions below correspond to Definition 2.6.1 in Halvorson.\<close>
definition is_finite :: "cset \<Rightarrow> bool"  where
   "is_finite X \<longleftrightarrow> (\<forall>m. (m : X \<rightarrow> X \<and> monomorphism m) \<longrightarrow> isomorphism m)"

definition is_infinite :: "cset \<Rightarrow> bool"  where
   "is_infinite X \<longleftrightarrow> (\<exists> m. m : X \<rightarrow> X \<and> monomorphism m \<and> \<not>surjective m)"

lemma either_finite_or_infinite:
  "is_finite X \<or> is_infinite X"
  using epi_mon_is_iso is_finite_def is_infinite_def surjective_is_epimorphism by blast

text \<open>The definition below corresponds to Definition 2.6.2 in Halvorson.\<close>
definition is_smaller_than :: "cset \<Rightarrow> cset \<Rightarrow> bool" (infix "\<le>\<^sub>c" 50) where
   "X \<le>\<^sub>c Y \<longleftrightarrow> (\<exists> m. m : X \<rightarrow> Y \<and> monomorphism m)"

text \<open>The purpose of the following lemma is simply to unify the two notations used in the book.\<close>
lemma subobject_iff_smaller_than:
  "(X \<le>\<^sub>c Y) = (\<exists>m. (X,m) \<subseteq>\<^sub>c Y)"
  using is_smaller_than_def subobject_of_def2 by auto

lemma set_card_transitive:
  assumes "A \<le>\<^sub>c B"
  assumes "B \<le>\<^sub>c C"
  shows   "A \<le>\<^sub>c C"
  by (typecheck_cfuncs, metis (full_types) assms cfunc_type_def comp_type composition_of_monic_pair_is_monic is_smaller_than_def)

lemma all_emptysets_are_finite:
  assumes "is_empty X"
  shows "is_finite X"
  by (metis assms epi_mon_is_iso epimorphism_def3 is_finite_def is_empty_def one_separator)

lemma emptyset_is_smallest_set:
  "\<emptyset> \<le>\<^sub>c X"
  using empty_subset is_smaller_than_def subobject_of_def2 by auto

lemma truth_set_is_finite:
  "is_finite \<Omega>"
  unfolding is_finite_def
proof(clarify)
  fix m 
  assume m_type[type_rule]: "m : \<Omega> \<rightarrow> \<Omega>"
  assume m_mono: "monomorphism m"
  have "surjective m"
    unfolding surjective_def
  proof(clarify)
    fix y
    assume "y \<in>\<^sub>c codomain m" 
    then have "y \<in>\<^sub>c \<Omega>"
      using cfunc_type_def m_type by force
    then show "\<exists>x. x \<in>\<^sub>c domain m \<and> m \<circ>\<^sub>c x = y"
      by (smt (verit, del_insts) cfunc_type_def codomain_comp domain_comp injective_def m_mono m_type monomorphism_imp_injective true_false_only_truth_values)
  qed
  then show "isomorphism m"
    by (simp add: epi_mon_is_iso m_mono surjective_is_epimorphism)
qed

lemma smaller_than_finite_is_finite:
  assumes "X \<le>\<^sub>c Y" "is_finite Y" 
  shows "is_finite X"
  unfolding is_finite_def
proof(clarify)
  fix x
  assume x_type: "x : X \<rightarrow> X"
  assume x_mono: "monomorphism x"

  obtain m where m_def: "m: X \<rightarrow> Y \<and> monomorphism m"
    using assms(1) is_smaller_than_def by blast
  obtain \<phi> where \<phi>_def: "\<phi> = into_super m \<circ>\<^sub>c (x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c try_cast m" 
    by auto

  have \<phi>_type: "\<phi> : Y \<rightarrow> Y"
    unfolding \<phi>_def
    using x_type m_def by (typecheck_cfuncs, blast)

  have "injective(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using cfunc_bowtieprod_inj id_isomorphism id_type iso_imp_epi_and_monic monomorphism_imp_injective x_mono x_type by blast
  then have mono1: "monomorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using injective_imp_monomorphism by auto
  have mono2: "monomorphism(try_cast m)"
    using m_def try_cast_mono by blast
  have mono3: "monomorphism((x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c try_cast m)"
    using cfunc_type_def composition_of_monic_pair_is_monic m_def mono1 mono2 x_type by (typecheck_cfuncs, auto)
  then have \<phi>_mono: "monomorphism \<phi>" 
    unfolding \<phi>_def
    using cfunc_type_def composition_of_monic_pair_is_monic 
          into_super_mono m_def mono3 x_type by (typecheck_cfuncs,auto)
  then have "isomorphism \<phi>" 
    using \<phi>_def \<phi>_type assms(2) is_finite_def by blast
  have iso_x_bowtie_id: "isomorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    by (typecheck_cfuncs, smt \<open>isomorphism \<phi>\<close> \<phi>_def comp_associative2 id_left_unit2 into_super_iso into_super_try_cast into_super_type isomorphism_sandwich m_def try_cast_type x_type)
  have "left_coproj X (Y \<setminus> (X,m)) \<circ>\<^sub>c x = (x \<bowtie>\<^sub>f id(Y \<setminus> (X,m))) \<circ>\<^sub>c left_coproj X (Y \<setminus> (X,m))"
    using x_type  
    by (typecheck_cfuncs, simp add: left_coproj_cfunc_bowtie_prod)
  have "epimorphism(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using iso_imp_epi_and_monic iso_x_bowtie_id by blast
  then have "surjective(x \<bowtie>\<^sub>f id(Y \<setminus> (X,m)))"
    using  epi_is_surj x_type by (typecheck_cfuncs, blast)
  then have "epimorphism x"
    using x_type cfunc_bowtieprod_surj_converse id_type surjective_is_epimorphism by blast
  then show "isomorphism x"
    by (simp add: epi_mon_is_iso x_mono)
qed

lemma larger_than_infinite_is_infinite:
  assumes "X \<le>\<^sub>c Y" "is_infinite X" 
  shows "is_infinite Y"
  using assms either_finite_or_infinite epi_is_surj is_finite_def is_infinite_def
    iso_imp_epi_and_monic smaller_than_finite_is_finite by blast

lemma iso_pres_finite:
  assumes "X \<cong> Y"
  assumes "is_finite X"
  shows "is_finite Y"
  using assms is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic isomorphic_is_symmetric smaller_than_finite_is_finite by blast

lemma not_finite_and_infinite:
  "\<not>(is_finite X \<and> is_infinite X)"
  using epi_is_surj is_finite_def is_infinite_def iso_imp_epi_and_monic by blast

lemma iso_pres_infinite:
  assumes "X \<cong> Y"
  assumes "is_infinite X"
  shows "is_infinite Y"
  using assms either_finite_or_infinite not_finite_and_infinite iso_pres_finite isomorphic_is_symmetric by blast

lemma size_2_sets:
"(X \<cong> \<Omega>) = (\<exists> x1. \<exists> x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2))"
proof 
  assume "X \<cong> \<Omega>"
  then obtain \<phi> where \<phi>_type[type_rule]: "\<phi> : X \<rightarrow> \<Omega>" and \<phi>_iso: "isomorphism \<phi>"
    using is_isomorphic_def by blast
  obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x1_def: "\<phi> \<circ>\<^sub>c x1 = \<t>" and
                     x2_type[type_rule]: "x2 \<in>\<^sub>c X" and x2_def: "\<phi> \<circ>\<^sub>c x2 = \<f>" and
                     distinct: "x1 \<noteq> x2"
    by (typecheck_cfuncs, smt (z3) \<phi>_iso cfunc_type_def comp_associative comp_type id_left_unit2 isomorphism_def true_false_distinct)
  then show  "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2)"
    by (smt (verit, best)  \<phi>_iso \<phi>_type cfunc_type_def comp_associative2 comp_type id_left_unit2 isomorphism_def true_false_only_truth_values)
next
  assume exactly_two: "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> (\<forall>x. x \<in>\<^sub>c X \<longrightarrow> x = x1 \<or> x = x2)"
  then obtain x1 x2  where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and x2_type[type_rule]: "x2 \<in>\<^sub>c X" and distinct: "x1 \<noteq> x2"
    by force
  have iso_type: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have surj: "surjective ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (typecheck_cfuncs, smt (verit, best) exactly_two cfunc_type_def coprod_case_bool_false
                coprod_case_bool_true distinct false_func_type surjective_def true_func_type)
  have inj: "injective ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) distinct case_bool_true_and_false comp_associative2 
        coprod_case_bool_false injective_def2 left_coproj_cfunc_coprod true_false_only_truth_values)
  then have "isomorphism ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (meson epi_mon_is_iso injective_imp_monomorphism singletonI surj surjective_is_epimorphism)
  then show "X \<cong> \<Omega>"
    using is_isomorphic_def iso_type isomorphic_is_symmetric by blast
qed

lemma size_2plus_sets:
  "(\<Omega> \<le>\<^sub>c X) = (\<exists> x1. \<exists> x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2)"
proof standard
  show "\<Omega> \<le>\<^sub>c X \<Longrightarrow> \<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2"
    by (meson comp_type false_func_type is_smaller_than_def monomorphism_def3 true_false_distinct true_func_type)
next
  assume "\<exists>x1 x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2"
  then obtain x1 x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and
                     x2_type[type_rule]: "x2 \<in>\<^sub>c X" and
                               distinct: "x1 \<noteq> x2"
    by blast  
  have mono_type: "((x1 \<amalg> x2) \<circ>\<^sub>c case_bool) : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have inj: "injective ((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    by (typecheck_cfuncs, smt (verit, ccfv_SIG) distinct case_bool_true_and_false comp_associative2 
        coprod_case_bool_false injective_def2 left_coproj_cfunc_coprod true_false_only_truth_values)    
  then show "\<Omega> \<le>\<^sub>c X"
    using injective_imp_monomorphism is_smaller_than_def mono_type by blast
qed

lemma not_init_not_term:
  "(\<not>(initial_object X) \<and> \<not>(terminal_object X)) = (\<exists> x1. \<exists> x2. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x1 \<noteq> x2)"
  by (metis is_empty_def initial_iso_empty iso_empty_initial iso_to1_is_term no_el_iff_iso_empty single_elem_iso_one terminal_object_def)

lemma sets_size_3_plus:
  "(\<not>(initial_object X) \<and> \<not>(terminal_object X) \<and> \<not>(X \<cong> \<Omega>)) = (\<exists> x1. \<exists> x2.  \<exists> x3. x1 \<in>\<^sub>c X \<and> x2 \<in>\<^sub>c X \<and> x3 \<in>\<^sub>c X \<and> x1 \<noteq> x2 \<and> x2 \<noteq> x3 \<and> x1 \<noteq> x3)"
  by (metis not_init_not_term size_2_sets)

text \<open>The next two lemmas below correspond to Proposition 2.6.3 in Halvorson.\<close>
lemma smaller_than_coproduct1:
  "X \<le>\<^sub>c X \<Coprod> Y"
  using is_smaller_than_def left_coproj_are_monomorphisms left_proj_type by blast

lemma  smaller_than_coproduct2:
  "X \<le>\<^sub>c Y \<Coprod> X"
  using is_smaller_than_def right_coproj_are_monomorphisms right_proj_type by blast

text \<open>The next two lemmas below correspond to Proposition 2.6.4 in Halvorson.\<close>
lemma smaller_than_product1:
  assumes "nonempty Y"
  shows "X \<le>\<^sub>c X \<times>\<^sub>c Y"
  unfolding is_smaller_than_def  
proof -
  obtain y where y_type: "y \<in>\<^sub>c Y"
  using assms nonempty_def by blast
  have map_type: "\<langle>id(X),y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> X \<times>\<^sub>c Y"
   using y_type cfunc_prod_type cfunc_type_def codomain_comp domain_comp id_type terminal_func_type by auto
  have mono: "monomorphism(\<langle>id X, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle>)"
    using map_type
  proof (unfold monomorphism_def3, clarify)
    fix g h A
    assume g_h_types: "g : A \<rightarrow> X" "h : A \<rightarrow> X"
    
    assume "\<langle>id\<^sub>c X,y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c g = \<langle>id\<^sub>c X,y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c h"
    then have "\<langle>id\<^sub>c X \<circ>\<^sub>c g, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c g\<rangle>  = \<langle>id\<^sub>c X \<circ>\<^sub>c h, y \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c h\<rangle>"
      using y_type g_h_types by (typecheck_cfuncs, smt cfunc_prod_comp comp_associative2 comp_type)
    then have "\<langle>g, y \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>\<rangle>  = \<langle>h, y \<circ>\<^sub>c \<beta>\<^bsub>A\<^esub>\<rangle>"
      using y_type g_h_types id_left_unit2 terminal_func_comp by (typecheck_cfuncs, auto)
    then show "g = h"
      using g_h_types y_type
      by (metis (full_types) comp_type left_cart_proj_cfunc_prod terminal_func_type)
  qed
  show "\<exists>m. m : X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism m"
    using mono map_type by auto
qed

lemma smaller_than_product2:
  assumes "nonempty Y"
  shows "X \<le>\<^sub>c Y \<times>\<^sub>c X"
  unfolding is_smaller_than_def  
proof - 
  have "X \<le>\<^sub>c X \<times>\<^sub>c Y"
    by (simp add: assms smaller_than_product1)
  then obtain m where m_def: "m : X \<rightarrow> X \<times>\<^sub>c Y \<and> monomorphism m"
    using is_smaller_than_def by blast
  obtain i  where "i : (X \<times>\<^sub>c Y) \<rightarrow> (Y \<times>\<^sub>c X) \<and> isomorphism i"
    using is_isomorphic_def product_commutes by blast
  then have "i \<circ>\<^sub>c m : X \<rightarrow>  (Y \<times>\<^sub>c X) \<and> monomorphism(i \<circ>\<^sub>c m)"
    using cfunc_type_def comp_type composition_of_monic_pair_is_monic iso_imp_epi_and_monic m_def by auto
  then show "\<exists>m. m : X \<rightarrow> Y \<times>\<^sub>c X \<and> monomorphism m"
    by blast
qed

lemma coprod_leq_product:
  assumes X_not_init: "\<not>(initial_object(X))" 
  assumes Y_not_init: "\<not>(initial_object(Y))" 
  assumes X_not_term: "\<not>(terminal_object(X))"
  assumes Y_not_term: "\<not>(terminal_object(Y))"
  shows "X \<Coprod> Y \<le>\<^sub>c X \<times>\<^sub>c Y"
proof - 
  obtain x1 x2 where x1x2_def[type_rule]:  "(x1 \<in>\<^sub>c X)" "(x2 \<in>\<^sub>c X)" "(x1 \<noteq> x2)"
    using is_empty_def X_not_init X_not_term iso_empty_initial iso_to1_is_term no_el_iff_iso_empty single_elem_iso_one by blast
  obtain y1 y2 where y1y2_def[type_rule]:  "(y1 \<in>\<^sub>c Y)" "(y2 \<in>\<^sub>c Y)" "(y1 \<noteq> y2)"
    using is_empty_def Y_not_init Y_not_term iso_empty_initial iso_to1_is_term no_el_iff_iso_empty single_elem_iso_one by blast
  then have y1_mono[type_rule]: "monomorphism(y1)"
    using element_monomorphism by blast
  obtain m where m_def: "m = \<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1)"
    by simp
  have type1: "\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> : X \<rightarrow> (X \<times>\<^sub>c Y)"
    by (meson cfunc_prod_type comp_type id_type terminal_func_type y1y2_def)
  have trycast_y1_type: "try_cast y1 : Y \<rightarrow> \<one> \<Coprod> (Y \<setminus> (\<one>,y1))"
    by (meson element_monomorphism try_cast_type y1y2_def)
  have y1'_type[type_rule]: "y1\<^sup>c : Y \<setminus> (\<one>,y1) \<rightarrow> Y"
    using complement_morphism_type one_terminal_object terminal_el_monomorphism y1y2_def by blast
  have type4: "\<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle> : Y \<setminus> (\<one>,y1) \<rightarrow> (X \<times>\<^sub>c Y)"
    using cfunc_prod_type comp_type terminal_func_type x1x2_def y1'_type by blast
  have type5: "\<langle>x2, y2\<rangle> \<in>\<^sub>c (X \<times>\<^sub>c Y)"
    by (simp add: cfunc_prod_type x1x2_def y1y2_def)
  then have type6: "\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle> :(\<one> \<Coprod> (Y \<setminus> (\<one>,y1))) \<rightarrow> (X \<times>\<^sub>c Y)"
    using cfunc_coprod_type type4 by blast
  then have type7: "((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) : Y \<rightarrow> (X \<times>\<^sub>c Y)"
    using comp_type trycast_y1_type by blast
  then have m_type: "m : X  \<Coprod> Y \<rightarrow> (X \<times>\<^sub>c Y)"
    by (simp add: cfunc_coprod_type m_def type1)

  have relative: "\<And>y. y \<in>\<^sub>c Y \<Longrightarrow> (y \<in>\<^bsub>Y\<^esub> (\<one>, y1)) = (y = y1)"
  proof(safe)
    fix y 
    assume y_type: "y \<in>\<^sub>c Y"
    show "y \<in>\<^bsub>Y\<^esub> (\<one>, y1) \<Longrightarrow> y = y1"
      by (metis cfunc_type_def factors_through_def id_right_unit2 id_type one_unique_element relative_member_def2)
  next 
    show "y1 \<in>\<^sub>c Y \<Longrightarrow> y1 \<in>\<^bsub>Y\<^esub> (\<one>, y1)"
      by (metis cfunc_type_def factors_through_def id_right_unit2 id_type relative_member_def2 y1_mono)
  qed


  have "injective(m)"
    unfolding injective_def
  proof(clarify)
    fix a b 
    assume "a \<in>\<^sub>c domain m" "b \<in>\<^sub>c domain m"
    then have a_type[type_rule]: "a \<in>\<^sub>c X  \<Coprod> Y" and b_type[type_rule]: "b \<in>\<^sub>c X  \<Coprod> Y"
      using m_type unfolding cfunc_type_def by auto
    assume eqs: "m \<circ>\<^sub>c a = m \<circ>\<^sub>c b"

      have m_leftproj_l_equals: "\<And> l. l  \<in>\<^sub>c X \<Longrightarrow> m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = \<langle>l, y1\<rangle>"
      proof-
        fix l 
        assume l_type: "l \<in>\<^sub>c X"
        have "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = (\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1)) \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l"
          by (simp add: m_def)
        also have "... = (\<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<amalg> ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c left_coproj X Y) \<circ>\<^sub>c l"
          using comp_associative2 l_type by (typecheck_cfuncs, blast)
        also have "... = \<langle>id(X), y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c l"
          by (typecheck_cfuncs, simp add: left_coproj_cfunc_coprod)
        also have "... = \<langle>id(X)\<circ>\<^sub>c l , (y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub>) \<circ>\<^sub>c l\<rangle>"
          using l_type cfunc_prod_comp by (typecheck_cfuncs, auto)
        also have "... = \<langle>l , y1 \<circ>\<^sub>c \<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c l\<rangle>"
          using l_type comp_associative2 id_left_unit2 by (typecheck_cfuncs, auto)
        also have "... = \<langle>l , y1\<rangle>"
          using l_type by (typecheck_cfuncs,metis id_right_unit2 id_type one_unique_element)
        finally show "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c l = \<langle>l,y1\<rangle>".
      qed

      have m_rightproj_y1_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y1 = \<langle>x2, y2\<rangle>"
      proof - 
        have "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y1 = (m \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c y1"
          using  comp_associative2 m_type by (typecheck_cfuncs, auto)
        also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c y1"
          using m_def right_coproj_cfunc_coprod type1 by (typecheck_cfuncs, auto)
        also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1 \<circ>\<^sub>c y1"
          using  comp_associative2 by (typecheck_cfuncs, auto)
        also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c left_coproj \<one> (Y \<setminus> (\<one>,y1))"
          using  try_cast_m_m y1_mono y1y2_def(1) by auto
        also have "... =  \<langle>x2, y2\<rangle>"
          using left_coproj_cfunc_coprod type4 type5 by blast
        finally show ?thesis.
      qed

      have m_rightproj_not_y1_equals: "\<And> r. r  \<in>\<^sub>c Y \<and> r \<noteq> y1 \<Longrightarrow>
            \<exists>k. k \<in>\<^sub>c Y \<setminus> (\<one>,y1) \<and> try_cast y1 \<circ>\<^sub>c r = right_coproj \<one> (Y \<setminus> (\<one>,y1)) \<circ>\<^sub>c k \<and> 
            m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
      proof clarify
        fix r 
        assume r_type: "r \<in>\<^sub>c Y"
        assume r_not_y1: "r \<noteq> y1"
        then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (\<one>,y1) \<and> try_cast y1 \<circ>\<^sub>c r = right_coproj \<one> (Y \<setminus> (\<one>,y1)) \<circ>\<^sub>c k"
          using r_type relative try_cast_not_in_X y1_mono y1y2_def(1) by blast
        have m_rightproj_l_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
             
        proof -
          have "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = (m \<circ>\<^sub>c right_coproj X Y) \<circ>\<^sub>c r"
            using r_type comp_associative2 m_type by (typecheck_cfuncs, auto)
          also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  try_cast y1) \<circ>\<^sub>c r"
            using m_def right_coproj_cfunc_coprod type1 by (typecheck_cfuncs, auto)
          also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c  (try_cast y1 \<circ>\<^sub>c r)"
            using r_type comp_associative2 by (typecheck_cfuncs, auto)
          also have "... = (\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c (right_coproj \<one> (Y \<setminus> (\<one>,y1)) \<circ>\<^sub>c k)"
            using k_def by auto
          also have "... = ((\<langle>x2, y2\<rangle> \<amalg> \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle>) \<circ>\<^sub>c right_coproj \<one> (Y \<setminus> (\<one>,y1))) \<circ>\<^sub>c k"
            using comp_associative2 k_def by (typecheck_cfuncs, blast)
          also have "... =  \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub>, y1\<^sup>c\<rangle> \<circ>\<^sub>c k"
            using right_coproj_cfunc_coprod type4 type5 by auto
          also have "... =  \<langle>x1 \<circ>\<^sub>c \<beta>\<^bsub>Y \<setminus> (\<one>,y1)\<^esub> \<circ>\<^sub>c k, y1\<^sup>c \<circ>\<^sub>c k \<rangle>"
            using cfunc_prod_comp comp_associative2 k_def by (typecheck_cfuncs, auto)
          also have "... =  \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            by (metis id_right_unit2 id_type k_def one_unique_element terminal_func_comp terminal_func_type x1x2_def(1))
          finally show ?thesis.
        qed
        then show "\<exists>k. k \<in>\<^sub>c Y \<setminus> (\<one>, y1) \<and>
          try_cast y1 \<circ>\<^sub>c r = right_coproj \<one> (Y \<setminus> (\<one>, y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c r = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              using k_def by blast
    qed
 
    show "a = b"
    proof(cases "\<exists>x. a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X")
      assume "\<exists>x. a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X"
      then obtain x where x_def: "a = left_coproj X Y \<circ>\<^sub>c x  \<and> x \<in>\<^sub>c X"
        by auto
      then have m_proj_a: "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c x = \<langle>x, y1\<rangle>"
        using m_leftproj_l_equals by (simp add: x_def)
      show "a = b"
      proof(cases "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X")
        assume "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
        then obtain c where c_def: "b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X"
          by auto
        then have "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c, y1\<rangle>"
          by (simp add: m_leftproj_l_equals)
        then show ?thesis
          using c_def element_pair_eq eqs m_proj_a x_def y1y2_def(1) by auto
      next
        assume "\<nexists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
        then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y"
          using b_type coprojs_jointly_surj by blast
        show "a = b"
        proof(cases "c = y1")
          assume "c = y1"       
          have m_rightproj_l_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x2, y2\<rangle>"
            by (simp add: \<open>c = y1\<close> m_rightproj_y1_equals)       
          then show ?thesis
            using \<open>c = y1\<close> c_def cart_prod_eq2 eqs m_proj_a x1x2_def(2) x_def y1y2_def(2) y1y2_def(3) by auto
        next
          assume "c \<noteq> y1"       
          then obtain k where k_def:  "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using c_def m_rightproj_not_y1_equals by blast                     
          then have "\<langle>x, y1\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
            using c_def eqs m_proj_a x_def by auto
          then have "(x = x1) \<and> (y1 = y1\<^sup>c \<circ>\<^sub>c k)"
            by (smt \<open>c \<noteq> y1\<close> c_def cfunc_type_def comp_associative comp_type element_pair_eq k_def m_rightproj_not_y1_equals monomorphism_def3 try_cast_m_m' try_cast_mono trycast_y1_type x1x2_def(1) x_def y1'_type y1_mono y1y2_def(1))
          then have False
            by (smt \<open>c \<noteq> y1\<close>  c_def comp_type complement_disjoint element_pair_eq id_right_unit2 id_type k_def m_rightproj_not_y1_equals x_def y1'_type y1_mono y1y2_def(1))
          then show ?thesis by auto
        qed
      qed
    next 
      assume "\<nexists>x. a = left_coproj X Y \<circ>\<^sub>c x \<and> x \<in>\<^sub>c X"
      then obtain y where y_def: "a = right_coproj X Y \<circ>\<^sub>c y \<and> y \<in>\<^sub>c Y"
        using a_type coprojs_jointly_surj by blast
      show "a = b"
      proof(cases "y = y1")
        assume "y = y1"
        then  have m_rightproj_y_equals: "m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x2, y2\<rangle>"
          using m_rightproj_y1_equals by blast
        then have "m \<circ>\<^sub>c a  = \<langle>x2, y2\<rangle>"
          using y_def by blast
        show "a = b"
        proof(cases "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c X")
          assume "\<exists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
          then obtain c where c_def: "b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
            by blast
          then show "a = b"
            using cart_prod_eq2 eqs m_leftproj_l_equals m_rightproj_y_equals x1x2_def(2) y1y2_def y_def by auto
        next
          assume "\<nexists>c. b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
          then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            using b_type coprojs_jointly_surj by blast
          show "a = b"
          proof(cases "c = y")
            assume "c = y"
            show "a = b"
              by (simp add: \<open>c = y\<close> c_def y_def)
          next
            assume "c \<noteq> y"
            then have "c \<noteq> y1"
              by (simp add: \<open>y = y1\<close>)
            then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (\<one>,y1) \<and> try_cast y1 \<circ>\<^sub>c c = right_coproj \<one> (Y \<setminus> (\<one>,y1)) \<circ>\<^sub>c k \<and> 
                 m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              using c_def m_rightproj_not_y1_equals by blast
            then have "\<langle>x2, y2\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
              using \<open>m \<circ>\<^sub>c a = \<langle>x2,y2\<rangle>\<close> c_def eqs by auto
            then have False
              using comp_type element_pair_eq k_def x1x2_def y1'_type y1y2_def(2) by auto
            then show ?thesis
              by simp
          qed
        qed
      next
        assume "y \<noteq> y1"
        then obtain k where k_def: "k \<in>\<^sub>c Y \<setminus> (\<one>,y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj \<one> (Y \<setminus> (\<one>,y1)) \<circ>\<^sub>c k \<and> 
          m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          using m_rightproj_not_y1_equals y_def by blast  
        then have "m \<circ>\<^sub>c a  = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
          using y_def by blast
        show "a = b"
        proof(cases "\<exists>c. b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y")
          assume "\<exists>c. b = right_coproj X Y \<circ>\<^sub>c c  \<and> c \<in>\<^sub>c Y"
          then obtain c where c_def: "b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            by blast  
          show "a = b"
          proof(cases "c = y1")
            assume "c = y1" 
            show "a = b"
              proof -
                obtain cc :: cfunc where
                  f1: "cc \<in>\<^sub>c Y \<setminus> (\<one>, y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj \<one> (Y \<setminus> (\<one>, y1)) \<circ>\<^sub>c cc \<and> m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c cc\<rangle>"
                  using \<open>\<And>thesis. (\<And>k. k \<in>\<^sub>c Y \<setminus> (\<one>, y1) \<and> try_cast y1 \<circ>\<^sub>c y = right_coproj \<one> (Y \<setminus> (\<one>, y1)) \<circ>\<^sub>c k \<and> m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c y = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
                have "\<langle>x2,y2\<rangle> = m \<circ>\<^sub>c a"
              using \<open>c = y1\<close> c_def eqs m_rightproj_y1_equals by presburger
              then show ?thesis
              using f1 cart_prod_eq2 comp_type x1x2_def y1'_type y1y2_def(2) y_def by force
              qed
          next
              assume "c \<noteq> y1"              
              then obtain k' where k'_def: "k' \<in>\<^sub>c Y \<setminus> (\<one>,y1) \<and> try_cast y1 \<circ>\<^sub>c c = right_coproj \<one> (Y \<setminus> (\<one>,y1)) \<circ>\<^sub>c k' \<and> 
              m \<circ>\<^sub>c right_coproj X Y \<circ>\<^sub>c c = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k'\<rangle>"
                using c_def m_rightproj_not_y1_equals by blast
              then have "\<langle>x1, y1\<^sup>c \<circ>\<^sub>c k'\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
                using c_def eqs k_def y_def by auto
              then have "(x1 = x1) \<and> (y1\<^sup>c \<circ>\<^sub>c k' = y1\<^sup>c \<circ>\<^sub>c k)"
                using  element_pair_eq k'_def k_def by (typecheck_cfuncs, blast)
              then have "k' = k"
                by (metis cfunc_type_def complement_morphism_mono k'_def k_def monomorphism_def y1'_type y1_mono)
              then have "c = y"
                by (metis c_def cfunc_type_def k'_def k_def monomorphism_def try_cast_mono trycast_y1_type y1_mono y_def)
              then show "a = b"
                by (simp add: c_def y_def)
          qed
        next
            assume "\<nexists>c. b = right_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c Y"
            then obtain c where c_def:  "b = left_coproj X Y \<circ>\<^sub>c c \<and> c \<in>\<^sub>c X"
              using b_type coprojs_jointly_surj by blast
            then have  "m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c, y1\<rangle>"
              by (simp add: m_leftproj_l_equals)      
            then have "\<langle>c, y1\<rangle> = \<langle>x1, y1\<^sup>c \<circ>\<^sub>c k\<rangle>"
                using \<open>m \<circ>\<^sub>c a = \<langle>x1,y1\<^sup>c \<circ>\<^sub>c k\<rangle>\<close> \<open>m \<circ>\<^sub>c left_coproj X Y \<circ>\<^sub>c c = \<langle>c,y1\<rangle>\<close> c_def eqs by auto      
            then have "(c = x1) \<and> (y1 = y1\<^sup>c \<circ>\<^sub>c k)"
              using c_def cart_prod_eq2 comp_type k_def x1x2_def(1) y1'_type y1y2_def(1) by auto 
            then have False
              by (metis cfunc_type_def complement_disjoint id_right_unit id_type k_def y1_mono y1y2_def(1))
            then show ?thesis
              by simp
        qed
      qed
    qed
  qed
  then have "monomorphism m"
    using injective_imp_monomorphism by auto 
  then show ?thesis
    using is_smaller_than_def m_type by blast
qed

lemma prod_leq_exp:
  assumes "\<not> terminal_object Y"
  shows "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
proof(cases "initial_object Y")
  show "initial_object Y \<Longrightarrow> X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
    by (metis X_prod_empty initial_iso_empty initial_maps_mono initial_object_def is_smaller_than_def iso_empty_initial isomorphic_is_reflexive isomorphic_is_transitive prod_pres_iso)
next
  assume "\<not> initial_object Y"
  then obtain y1 y2 where y1_type[type_rule]: "y1 \<in>\<^sub>c Y" and y2_type[type_rule]: "y2 \<in>\<^sub>c Y" and y1_not_y2: "y1 \<noteq> y2"
    using assms not_init_not_term by blast
  show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
  proof(cases "X \<cong> \<Omega>")
      assume "X \<cong> \<Omega>"
      have "\<Omega>  \<le>\<^sub>c  Y"
         using \<open>\<not> initial_object Y\<close> assms not_init_not_term size_2plus_sets by blast
      then obtain m where m_type[type_rule]: "m : \<Omega>  \<rightarrow>  Y" and m_mono: "monomorphism m"
        using is_smaller_than_def by blast
      then have m_id_type[type_rule]: "m \<times>\<^sub>f id(Y) : \<Omega> \<times>\<^sub>c Y \<rightarrow> Y \<times>\<^sub>c Y"
        by typecheck_cfuncs
      have m_id_mono: "monomorphism (m \<times>\<^sub>f id(Y))"
        by (typecheck_cfuncs, simp add: cfunc_cross_prod_mono id_isomorphism iso_imp_epi_and_monic m_mono)  
      obtain n where n_type[type_rule]: "n : Y \<times>\<^sub>c Y  \<rightarrow>  Y\<^bsup>\<Omega>\<^esup>" and n_mono: "monomorphism n"
        using is_isomorphic_def iso_imp_epi_and_monic isomorphic_is_symmetric sets_squared by blast
      obtain r where r_type[type_rule]: "r : Y\<^bsup>\<Omega>\<^esup>  \<rightarrow>  Y\<^bsup>X\<^esup>" and r_mono: "monomorphism r"
        by (meson \<open>X \<cong> \<Omega>\<close> exp_pres_iso_right is_isomorphic_def iso_imp_epi_and_monic isomorphic_is_symmetric)
      obtain q where q_type[type_rule]: "q : X \<times>\<^sub>c Y  \<rightarrow>  \<Omega> \<times>\<^sub>c Y" and q_mono: "monomorphism q"
        by (meson \<open>X \<cong> \<Omega>\<close> id_isomorphism id_type is_isomorphic_def iso_imp_epi_and_monic prod_pres_iso) 
      have rnmq_type[type_rule]: "r \<circ>\<^sub>c n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>"
        by typecheck_cfuncs
      have "monomorphism(r \<circ>\<^sub>c n \<circ>\<^sub>c (m \<times>\<^sub>f id(Y)) \<circ>\<^sub>c q)"
        by (typecheck_cfuncs, simp add: cfunc_type_def composition_of_monic_pair_is_monic m_id_mono n_mono q_mono r_mono)
      then show ?thesis
        by (meson is_smaller_than_def rnmq_type)
    next
      assume "\<not> X \<cong> \<Omega>"
      show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
      proof(cases "initial_object X")
        show "initial_object X \<Longrightarrow> X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
          by (metis is_empty_def initial_iso_empty initial_maps_mono initial_object_def 
              is_smaller_than_def isomorphic_is_transitive no_el_iff_iso_empty
              not_init_not_term prod_with_empty_is_empty2 product_commutes terminal_object_def)
      next
      assume "\<not> initial_object X"
      show "X \<times>\<^sub>c Y \<le>\<^sub>c Y\<^bsup>X\<^esup>"
      proof(cases "terminal_object X")
        assume "terminal_object X"
        then have "X \<cong> \<one>"
          by (simp add: one_terminal_object terminal_objects_isomorphic)
        have "X \<times>\<^sub>c Y \<cong> Y"
          by (simp add: \<open>terminal_object X\<close> prod_with_term_obj1)
        then have "X \<times>\<^sub>c Y \<cong> Y\<^bsup>X\<^esup>"
          by (meson \<open>X \<cong> \<one>\<close> exp_pres_iso_right exp_set_inj isomorphic_is_symmetric isomorphic_is_transitive exp_one)
        then show ?thesis
          using is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic by blast
      next
        assume "\<not> terminal_object X"

        obtain into where into_def: "into = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                               \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) "
          by simp
        then have into_type[type_rule]: "into : Y \<times>\<^sub>c (X \<times>\<^sub>c X) \<rightarrow> Y"
          by (simp, typecheck_cfuncs)
   

        obtain \<Theta> where \<Theta>_def: "\<Theta> = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X))\<^sup>\<sharp> \<circ>\<^sub>c swap X Y"
          by auto
  
        have \<Theta>_type[type_rule]: "\<Theta> : X \<times>\<^sub>c Y \<rightarrow> Y\<^bsup>X\<^esup>"
          unfolding \<Theta>_def by typecheck_cfuncs

        have f0: "\<And>x. \<And> y. \<And> z. x \<in>\<^sub>c X \<and> y \<in>\<^sub>c Y \<and> z \<in>\<^sub>c X \<Longrightarrow> (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
        proof(clarify)
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          show "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c X,\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c \<langle>y,\<langle>x,z\<rangle>\<rangle>"
          proof - 
            have "(\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c X,\<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = (\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id\<^sub>c X \<circ>\<^sub>c z,\<beta>\<^bsub>X\<^esub> \<circ>\<^sub>c z\<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_prod_comp)
            also have "... = (\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>z,id \<one>\<rangle>"
              by (typecheck_cfuncs, metis id_left_unit2 one_unique_element)
            also have "... = (\<Theta>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>x,y\<rangle>)) \<circ>\<^sub>c \<langle>z,id \<one>\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, presburger)
            also have "... = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c (id(X) \<times>\<^sub>f \<langle>x,y\<rangle>) \<circ>\<^sub>c \<langle>z,id \<one>\<rangle>"
              using comp_associative2 by (typecheck_cfuncs, auto)
            also have "... = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c \<langle>id(X) \<circ>\<^sub>c  z, \<langle>x,y\<rangle> \<circ>\<^sub>c  id \<one>\<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
            also have "... = \<Theta>\<^sup>\<flat> \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              by (typecheck_cfuncs, simp add: id_left_unit2 id_right_unit2)
            also have "... = ((into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X))\<^sup>\<sharp> \<circ>\<^sub>c swap X Y)\<^sup>\<flat> \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              by (simp add: \<Theta>_def)
            also have "... = ((into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X))\<^sup>\<sharp>\<^sup>\<flat> \<circ>\<^sub>c (id X \<times>\<^sub>f swap X Y)) \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              using inv_transpose_of_composition by (typecheck_cfuncs, presburger)
            also have "... = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X)) \<circ>\<^sub>c  (id X \<times>\<^sub>f swap X Y) \<circ>\<^sub>c \<langle>z,\<langle>x,y\<rangle>\<rangle>"
              by (typecheck_cfuncs, simp add: comp_associative2 inv_transpose_func_def3 transpose_func_def)
            also have "... = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X)) \<circ>\<^sub>c  \<langle>id X \<circ>\<^sub>c z, swap X Y \<circ>\<^sub>c \<langle>x,y\<rangle>\<rangle>"
              by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
            also have "... = (into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X)) \<circ>\<^sub>c  \<langle>z, \<langle>y,x\<rangle>\<rangle>"
              using id_left_unit2 swap_ap by (typecheck_cfuncs, presburger)
            also have "... = into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c swap X (Y \<times>\<^sub>c X) \<circ>\<^sub>c  \<langle>z, \<langle>y,x\<rangle>\<rangle>"
              by (typecheck_cfuncs, metis cfunc_type_def comp_associative)
            also have "... = into \<circ>\<^sub>c associate_right Y X X \<circ>\<^sub>c   \<langle>\<langle>y,x\<rangle>, z\<rangle>"
              using swap_ap by (typecheck_cfuncs, presburger)
            also have "... = into \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
              using associate_right_ap by (typecheck_cfuncs, presburger)
            finally show ?thesis.
          qed
        qed
  
        have f1: "\<And>x y. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y  \<Longrightarrow> (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y"
        proof - 
          fix x y 
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          have "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = into \<circ>\<^sub>c   \<langle>y, \<langle>x, x\<rangle>\<rangle>"
            by (simp add: f0 x_type y_type)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) \<circ>\<^sub>c   \<langle>y, \<langle>x, x\<rangle>\<rangle>"
            using cfunc_type_def comp_associative comp_type into_def by (typecheck_cfuncs, fastforce)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>id Y \<circ>\<^sub>c y, eq_pred X \<circ>\<^sub>c  \<langle>x, x\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
         also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>y, \<t>\<rangle>"
            by (typecheck_cfuncs, metis eq_pred_iff_eq id_left_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one>  \<circ>\<^sub>c  \<langle>y, left_coproj \<one> \<one>\<rangle>"
            by (typecheck_cfuncs, simp add: case_bool_true cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one>  \<circ>\<^sub>c  \<langle>y, left_coproj \<one> \<one> \<circ>\<^sub>c id \<one>\<rangle>"
            by (typecheck_cfuncs, metis id_right_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c left_coproj (Y \<times>\<^sub>c \<one>) (Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id \<one>\<rangle>"
            using dist_prod_coprod_left_ap_left by (typecheck_cfuncs, auto)
          also have "... = ((left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c left_coproj (Y \<times>\<^sub>c \<one>) (Y \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>y,id \<one>\<rangle>"
            by (typecheck_cfuncs, meson comp_associative2)
          also have "... = left_cart_proj Y \<one> \<circ>\<^sub>c \<langle>y,id \<one>\<rangle>"
            using left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          also have "... = y"
            by (typecheck_cfuncs, simp add: left_cart_proj_cfunc_prod)
          finally show "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c x = y".
        qed
  
        have f2: "\<And>x y z. x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y  \<Longrightarrow>  z \<in>\<^sub>c X \<Longrightarrow> z \<noteq> x \<Longrightarrow> y \<noteq> y1 \<Longrightarrow> (\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
        proof - 
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume y_type[type_rule]: "y \<in>\<^sub>c Y"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          assume "z \<noteq> x"
          assume "y \<noteq> y1"
          have "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
            by (simp add: f0 x_type y_type z_type)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) \<circ>\<^sub>c   \<langle>y, \<langle>x, z\<rangle>\<rangle>"
            using cfunc_type_def comp_associative comp_type into_def by (typecheck_cfuncs, fastforce)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>id Y \<circ>\<^sub>c y, eq_pred X \<circ>\<^sub>c  \<langle>x, z\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>y, \<f>\<rangle>"
            by (typecheck_cfuncs, metis \<open>z \<noteq> x\<close> eq_pred_iff_eq_conv id_left_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one>  \<circ>\<^sub>c  \<langle>y, right_coproj \<one> \<one>\<rangle>"
            by (typecheck_cfuncs, simp add: case_bool_false cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one>  \<circ>\<^sub>c  \<langle>y, right_coproj \<one> \<one> \<circ>\<^sub>c id \<one>\<rangle>"
            by (typecheck_cfuncs, simp add: id_right_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c \<one>) (Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y,id \<one>\<rangle>"
            using dist_prod_coprod_left_ap_right by (typecheck_cfuncs, auto)
          also have "... = ((left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c \<one>) (Y \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>y,id \<one>\<rangle>"
            by (typecheck_cfuncs, meson comp_associative2)
          also have "... = ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y,id \<one>\<rangle>"
            using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y,id \<one>\<rangle>"
            using comp_associative2 by (typecheck_cfuncs, force)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y  \<circ>\<^sub>c \<langle>y,y1\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<f>"
            by (typecheck_cfuncs, metis \<open>y \<noteq> y1\<close> eq_pred_iff_eq_conv)
          also have "... = y1"
            using case_bool_false right_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          finally show "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1".
        qed
        
        have f3: "\<And>x z. x \<in>\<^sub>c X \<Longrightarrow>  z \<in>\<^sub>c X \<Longrightarrow> z \<noteq> x \<Longrightarrow>  (\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
        proof - 
          fix x y z
          assume x_type[type_rule]: "x \<in>\<^sub>c X"
          assume z_type[type_rule]: "z \<in>\<^sub>c X"
          assume "z \<noteq> x"
          have "(\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = into \<circ>\<^sub>c   \<langle>y1, \<langle>x, z\<rangle>\<rangle>"
            by (simp add: f0 x_type y1_type z_type)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c (id Y \<times>\<^sub>f eq_pred X) \<circ>\<^sub>c   \<langle>y1, \<langle>x, z\<rangle>\<rangle>"
            using cfunc_type_def comp_associative comp_type into_def by (typecheck_cfuncs, fastforce)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>id Y \<circ>\<^sub>c y1, eq_pred X \<circ>\<^sub>c  \<langle>x, z\<rangle>\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one> \<circ>\<^sub>c (id Y \<times>\<^sub>f case_bool) \<circ>\<^sub>c  \<langle>y1, \<f>\<rangle>"
            by (typecheck_cfuncs, metis \<open>z \<noteq> x\<close> eq_pred_iff_eq_conv id_left_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one>  \<circ>\<^sub>c  \<langle>y1, right_coproj \<one> \<one>\<rangle>"
            by (typecheck_cfuncs, simp add: case_bool_false cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c dist_prod_coprod_left Y \<one> \<one>  \<circ>\<^sub>c  \<langle>y1, right_coproj \<one> \<one> \<circ>\<^sub>c id \<one>\<rangle>"
            by (typecheck_cfuncs, simp add: id_right_unit2)
          also have "... = (left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)))
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c \<one>) (Y \<times>\<^sub>c \<one>) \<circ>\<^sub>c \<langle>y1,id \<one>\<rangle>"
            using dist_prod_coprod_left_ap_right by (typecheck_cfuncs, auto)
          also have "... = ((left_cart_proj Y \<one> \<amalg> ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1))) 
                                 \<circ>\<^sub>c right_coproj (Y \<times>\<^sub>c \<one>) (Y \<times>\<^sub>c \<one>)) \<circ>\<^sub>c \<langle>y1,id \<one>\<rangle>"
            by (typecheck_cfuncs, meson comp_associative2)
          also have "... = ((y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1)) \<circ>\<^sub>c \<langle>y1,id \<one>\<rangle>"
            using right_coproj_cfunc_coprod by (typecheck_cfuncs, auto)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y \<circ>\<^sub>c (id Y \<times>\<^sub>f y1) \<circ>\<^sub>c \<langle>y1,id \<one>\<rangle>"
            using comp_associative2 by (typecheck_cfuncs, force)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c eq_pred Y  \<circ>\<^sub>c \<langle>y1,y1\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_right_unit2)
          also have "... = (y2 \<amalg> y1) \<circ>\<^sub>c case_bool \<circ>\<^sub>c \<t>"
            by (typecheck_cfuncs, metis eq_pred_iff_eq)
          also have "... = y2"
            using case_bool_true left_coproj_cfunc_coprod by (typecheck_cfuncs, presburger)
          finally show "(\<Theta> \<circ>\<^sub>c \<langle>x, y1\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2".
        qed
  
     have \<Theta>_injective: "injective(\<Theta>)"
       unfolding injective_def
     proof(clarify)
       fix xy st
       assume xy_type[type_rule]: "xy \<in>\<^sub>c domain \<Theta>"
       assume st_type[type_rule]: "st \<in>\<^sub>c domain \<Theta>"
       assume equals: "\<Theta> \<circ>\<^sub>c xy = \<Theta> \<circ>\<^sub>c st"
       obtain x y where x_type[type_rule]: "x \<in>\<^sub>c X" and y_type[type_rule]: "y \<in>\<^sub>c Y" and xy_def: "xy = \<langle>x,y\<rangle>"
         by (metis \<Theta>_type cart_prod_decomp cfunc_type_def xy_type)
       obtain s t where s_type[type_rule]: "s \<in>\<^sub>c X" and t_type[type_rule]: "t \<in>\<^sub>c Y" and st_def: "st = \<langle>s,t\<rangle>"
         by (metis \<Theta>_type cart_prod_decomp cfunc_type_def st_type)   
       have equals2: "\<Theta> \<circ>\<^sub>c \<langle>x,y\<rangle> = \<Theta> \<circ>\<^sub>c \<langle>s,t\<rangle>"
         using equals st_def xy_def by auto
       have "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
       proof(cases "y = y1")  
         assume "y = y1"
         show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
         proof(cases "t = y1")
           show "t = y1 \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
             by (typecheck_cfuncs, metis \<open>y = y1\<close> equals f1 f3 st_def xy_def y1_not_y2)
         next
           assume "t \<noteq> y1"
           show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
           proof(cases "s = x")
             show "s = x \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               by (typecheck_cfuncs, metis equals2 f1)
           next
             assume "s \<noteq> x"  (*This step, in particular, is why we require X to not be isomorphic to Omega*)
             obtain z where z_type[type_rule]: "z \<in>\<^sub>c X" and z_not_x: "z \<noteq> x" and z_not_s: "z \<noteq> s"
               by (metis \<open>\<not> X \<cong> \<Omega>\<close> \<open>\<not> initial_object X\<close> \<open>\<not> terminal_object X\<close> sets_size_3_plus)
             have t_sz: "(\<Theta> \<circ>\<^sub>c \<langle>s, t\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y1"
               by (simp add: \<open>t \<noteq> y1\<close> f2 s_type t_type z_not_s z_type)
             have y_xz: "(\<Theta> \<circ>\<^sub>c \<langle>x, y\<rangle>)\<^sup>\<flat> \<circ>\<^sub>c \<langle>id X, \<beta>\<^bsub>X\<^esub>\<rangle> \<circ>\<^sub>c z = y2"
               by (simp add: \<open>y = y1\<close> f3 x_type z_not_x z_type)    
             then have "y1 = y2"
               using equals2 t_sz by auto
             then have False
               using y1_not_y2 by auto
             then show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               by simp
           qed
         qed
       next
         assume "y \<noteq> y1"
         show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
         proof(cases "y = y2")
           assume "y = y2"
           show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
           proof(cases "t = y2", clarify)
             show "t = y2 \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,y2\<rangle>"
               by (typecheck_cfuncs, metis \<open>y = y2\<close> \<open>y \<noteq> y1\<close> equals f1 f2 st_def xy_def)
           next
             assume "t \<noteq> y2"
             show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
             proof(cases "x = s", clarify)
               show "x = s \<Longrightarrow> \<langle>s,y\<rangle> = \<langle>s,t\<rangle>"
                 by (metis equals2 f1 s_type t_type y_type)
             next
               assume "x \<noteq> s"
               show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               proof(cases "t = y1",clarify)
                 show "t = y1 \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,y1\<rangle>"
                   by (metis \<open>\<not> X \<cong> \<Omega>\<close> \<open>\<not> initial_object X\<close> \<open>\<not> terminal_object X\<close> \<open>y = y2\<close> \<open>y \<noteq> y1\<close> equals f2 f3 s_type sets_size_3_plus st_def x_type xy_def y2_type)
               next
                 assume "t \<noteq> y1"
                 show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
                   by (typecheck_cfuncs, metis \<open>t \<noteq> y1\<close> \<open>y \<noteq> y1\<close> equals f1 f2 st_def xy_def)
               qed
             qed
           qed
         next
           assume "y \<noteq> y2"
           show "\<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
           proof(cases "s = x", clarify)
             show "s = x \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>x,t\<rangle>"
               by (metis equals2 f1 t_type x_type y_type)
             show "s \<noteq> x \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>s,t\<rangle>"
               by (metis \<open>y \<noteq> y1\<close> \<open>y \<noteq> y2\<close> equals f1 f2 f3 s_type st_def t_type x_type xy_def y_type)
           qed
         qed
       qed
     then show "xy = st"
       by (typecheck_cfuncs, simp add:  st_def xy_def)
   qed
      then show ?thesis
        using \<Theta>_type injective_imp_monomorphism is_smaller_than_def by blast
    qed
  qed  
 qed
qed

lemma Y_nonempty_then_X_le_XtoY:
  assumes "nonempty Y"
  shows "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
proof - 
  obtain f where f_def: "f = (right_cart_proj Y X)\<^sup>\<sharp>"
    by blast
  then have f_type: "f : X \<rightarrow> X\<^bsup>Y\<^esup>"
    by (simp add: right_cart_proj_type transpose_func_type)
  have mono_f: "injective(f)"
    unfolding injective_def
  proof(clarify)
    fix x y 
    assume x_type: "x \<in>\<^sub>c domain f"
    assume y_type: "y \<in>\<^sub>c domain f"
    assume equals: "f \<circ>\<^sub>c x = f \<circ>\<^sub>c y"
    have x_type2 : "x \<in>\<^sub>c X"
      using cfunc_type_def f_type x_type by auto
    have y_type2 : "y \<in>\<^sub>c X"
      using cfunc_type_def f_type y_type by auto
    have "x \<circ>\<^sub>c (right_cart_proj Y \<one>) = (right_cart_proj Y X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      using right_cart_proj_cfunc_cross_prod x_type2 by (typecheck_cfuncs, auto)
    also have "... = ((eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    also have "... = (eval_func X Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f x))"
      using comp_associative2 f_type x_type2 by (typecheck_cfuncs, fastforce)
    also have "... = (eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c x))"
      using f_type identity_distributes_across_composition x_type2 by auto
    also have "... = (eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f (f \<circ>\<^sub>c y))"
      by (simp add: equals)
    also have "... = (eval_func X Y) \<circ>\<^sub>c ((id(Y) \<times>\<^sub>f f) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y))"
      using f_type identity_distributes_across_composition y_type2 by auto
    also have "... = ((eval_func X Y) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f f)) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      using comp_associative2 f_type y_type2 by (typecheck_cfuncs, fastforce)
    also have "... = (right_cart_proj Y X) \<circ>\<^sub>c (id(Y) \<times>\<^sub>f y)"
      by (typecheck_cfuncs, simp add: f_def transpose_func_def)
    also have "... = y \<circ>\<^sub>c (right_cart_proj Y \<one>)"
      using right_cart_proj_cfunc_cross_prod y_type2 by (typecheck_cfuncs, auto)
    ultimately show "x = y"
      using assms epimorphism_def3 nonempty_left_imp_right_proj_epimorphism right_cart_proj_type x_type2 y_type2 by fastforce
  qed
  then show "X \<le>\<^sub>c X\<^bsup>Y\<^esup>"
    using f_type injective_imp_monomorphism is_smaller_than_def by blast
qed

lemma non_init_non_ter_sets:
  assumes "\<not>(terminal_object X)"
  assumes "\<not>(initial_object X)"
  shows "\<Omega> \<le>\<^sub>c X" 
proof - 
  obtain x1 and x2 where x1_type[type_rule]: "x1 \<in>\<^sub>c X" and 
                         x2_type[type_rule]: "x2 \<in>\<^sub>c X" and
                                   distinct: "x1 \<noteq> x2"
    using is_empty_def assms iso_empty_initial iso_to1_is_term no_el_iff_iso_empty single_elem_iso_one by blast
  then have map_type: "(x1 \<amalg> x2) \<circ>\<^sub>c case_bool   : \<Omega> \<rightarrow> X"
    by typecheck_cfuncs
  have injective: "injective((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    unfolding injective_def
  proof(clarify)
    fix \<omega>1 \<omega>2 
    assume "\<omega>1 \<in>\<^sub>c domain (x1 \<amalg> x2 \<circ>\<^sub>c case_bool)"
    then have \<omega>1_type[type_rule]: "\<omega>1 \<in>\<^sub>c \<Omega>"
      using cfunc_type_def map_type by auto
    assume "\<omega>2 \<in>\<^sub>c domain (x1 \<amalg> x2 \<circ>\<^sub>c case_bool)"
    then have \<omega>2_type[type_rule]: "\<omega>2 \<in>\<^sub>c \<Omega>"
      using cfunc_type_def map_type by auto
    
    assume equals: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = (x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2"
    show "\<omega>1 = \<omega>2"
    proof(cases "\<omega>1 = \<t>", clarify)
      assume "\<omega>1 = \<t>"
      show "\<t> = \<omega>2"
      proof(rule ccontr)
        assume " \<t> \<noteq> \<omega>2"
        then have "\<f> = \<omega>2"
          using \<open>\<t> \<noteq> \<omega>2\<close> true_false_only_truth_values by (typecheck_cfuncs, blast)
        then have RHS: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x2"
          by (meson coprod_case_bool_false x1_type x2_type)
        have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x1"
          using \<open>\<omega>1 = \<t>\<close> coprod_case_bool_true x1_type x2_type by blast
        then show False
          using RHS distinct equals by force
      qed
    next
      assume "\<omega>1 \<noteq> \<t>"
      then have "\<omega>1 = \<f>"
        using  true_false_only_truth_values by (typecheck_cfuncs, blast)
      have "\<omega>2 = \<f>"
      proof(rule ccontr)
        assume "\<omega>2 \<noteq> \<f>"
        then have "\<omega>2 = \<t>"
          using  true_false_only_truth_values by (typecheck_cfuncs, blast)
        then have RHS: "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>2 = x2"
          using \<open>\<omega>1 = \<f>\<close> coprod_case_bool_false equals x1_type x2_type by auto
        have "(x1 \<amalg> x2 \<circ>\<^sub>c case_bool) \<circ>\<^sub>c \<omega>1 = x1"
          using \<open>\<omega>2 = \<t>\<close> coprod_case_bool_true equals x1_type x2_type by presburger
        then show False
          using RHS distinct equals by auto
      qed
      show "\<omega>1 = \<omega>2"
        by (simp add: \<open>\<omega>1 = \<f>\<close> \<open>\<omega>2 = \<f>\<close>)
    qed
  qed
  then have "monomorphism((x1 \<amalg> x2) \<circ>\<^sub>c case_bool)"
    using injective_imp_monomorphism by auto
  then show "\<Omega> \<le>\<^sub>c X"
    using  is_smaller_than_def map_type by blast
qed

lemma exp_preserves_card1:
  assumes "A \<le>\<^sub>c B"
  assumes "nonempty X"   
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
  unfolding is_smaller_than_def
proof -
  obtain x where x_type[type_rule]: "x \<in>\<^sub>c X"
    using assms(2) unfolding nonempty_def by auto
  obtain m where m_def[type_rule]: "m : A \<rightarrow> B" "monomorphism m"
    using assms(1) unfolding is_smaller_than_def by auto
  show "\<exists>m. m : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup> \<and> monomorphism m"
  proof (intro exI[where x="(((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>))
    \<circ>\<^sub>c dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) 
    \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id (X\<^bsup>A\<^esup>)))\<^sup>\<sharp>"], safe)

    show "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> : X\<^bsup>A\<^esup> \<rightarrow> X\<^bsup>B\<^esup>"
      by  typecheck_cfuncs
    then show "monomorphism
      (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
        dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
        swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)"
    proof (unfold monomorphism_def3, clarify)
      fix g h Z
      assume g_type[type_rule]: "g : Z \<rightarrow> X\<^bsup>A\<^esup>"
      assume h_type[type_rule]: "h : Z \<rightarrow> X\<^bsup>A\<^esup>"
      assume eq: "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
          dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
          swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c g
        =
          ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
          dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
          swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h"

      show "g = h"
      proof (typecheck_cfuncs, rule same_evals_equal[where Z=Z, where A=A, where X=X], clarify)
        show "eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f g = eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f h"
        proof (typecheck_cfuncs, rule one_separator[where X="A \<times>\<^sub>c Z", where Y="X"], clarify)
          fix az
          assume az_type[type_rule]: "az \<in>\<^sub>c A \<times>\<^sub>c Z"

          obtain a z where az_types[type_rule]: "a \<in>\<^sub>c A" "z \<in>\<^sub>c Z" and az_def: "az = \<langle>a,z\<rangle>"
            using cart_prod_decomp az_type by blast

          have "(eval_func X B) \<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c g)) = 
          (eval_func X B) \<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp> \<circ>\<^sub>c h))"
            using eq by simp
          then have "(eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) = 
          (eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            using identity_distributes_across_composition by (typecheck_cfuncs, auto)
          then have "((eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>))) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) = 
          ((eval_func X B)\<circ>\<^sub>c (id B \<times>\<^sub>f (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>))\<^sup>\<sharp>))) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            by (typecheck_cfuncs, smt eq inv_transpose_func_def3 inv_transpose_of_composition)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g)
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)"
            using   transpose_func_def by (typecheck_cfuncs,auto)
          then have "(((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>
          = (((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>"
            by auto
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  g) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c (id B \<times>\<^sub>f  h) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, z\<rangle>"
            by (typecheck_cfuncs, auto simp add: comp_associative2)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs, smt cfunc_cross_prod_comp_cfunc_prod id_left_unit2 id_type)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c (try_cast m \<times>\<^sub>f id\<^sub>c (X\<^bsup>A\<^esup>)) \<circ>\<^sub>c \<langle>m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs_prems, smt comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>try_cast m \<circ>\<^sub>c m \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>try_cast m \<circ>\<^sub>c m \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            using cfunc_cross_prod_comp_cfunc_prod id_left_unit2 by (typecheck_cfuncs_prems, smt)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>(try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>(try_cast m \<circ>\<^sub>c m) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs, auto simp add: comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a, g \<circ>\<^sub>c z\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c
            swap (A \<Coprod> (B \<setminus> (A, m))) (X\<^bsup>A\<^esup>) \<circ>\<^sub>c \<langle>left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a, h \<circ>\<^sub>c z\<rangle>"
            using m_def(2) try_cast_m_m by (typecheck_cfuncs, auto)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            dist_prod_coprod_left (X\<^bsup>A\<^esup>) A (B \<setminus> (A, m)) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z, left_coproj A (B \<setminus> (A,m)) \<circ>\<^sub>c a\<rangle>"
            using swap_ap by (typecheck_cfuncs, auto)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m))) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
          = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m))) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            using dist_prod_coprod_left_ap_left by (typecheck_cfuncs, auto)
          then have "((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m)))) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
          = ((eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<amalg> (x \<circ>\<^sub>c \<beta>\<^bsub>X\<^bsup>A\<^esup> \<times>\<^sub>c (B \<setminus> (A, m))\<^esub>) \<circ>\<^sub>c
            left_coproj (X\<^bsup>A\<^esup>\<times>\<^sub>cA) (X\<^bsup>A\<^esup>\<times>\<^sub>c(B \<setminus> (A,m)))) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
          then have "(eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
            = (eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A) \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: left_coproj_cfunc_coprod)
          then have "eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A \<circ>\<^sub>c \<langle>g \<circ>\<^sub>c z, a\<rangle>
            = eval_func X A \<circ>\<^sub>c swap (X\<^bsup>A\<^esup>) A \<circ>\<^sub>c \<langle>h \<circ>\<^sub>c z,a\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
          then have "eval_func X A \<circ>\<^sub>c \<langle>a, g \<circ>\<^sub>c z\<rangle> = eval_func X A \<circ>\<^sub>c \<langle>a, h \<circ>\<^sub>c z\<rangle>"
            by (typecheck_cfuncs_prems, auto simp add: swap_ap)
          then have "eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f g) \<circ>\<^sub>c \<langle>a, z\<rangle> = eval_func X A \<circ>\<^sub>c (id A \<times>\<^sub>f h) \<circ>\<^sub>c \<langle>a, z\<rangle>"
            by (typecheck_cfuncs, simp add: cfunc_cross_prod_comp_cfunc_prod id_left_unit2)
          then show "(eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f g) \<circ>\<^sub>c az = (eval_func X A \<circ>\<^sub>c id\<^sub>c A \<times>\<^sub>f h) \<circ>\<^sub>c az"
            unfolding az_def by (typecheck_cfuncs_prems, auto simp add: comp_associative2)
        qed
      qed
    qed
  qed
qed

lemma exp_preserves_card2:
  assumes "A \<le>\<^sub>c B"
  shows "A\<^bsup>X\<^esup> \<le>\<^sub>c B\<^bsup>X\<^esup>"
  unfolding is_smaller_than_def
proof -
  obtain m where m_def[type_rule]: "m : A \<rightarrow> B" "monomorphism m"
        using assms unfolding is_smaller_than_def by auto
  show "\<exists>m. m : A\<^bsup>X\<^esup> \<rightarrow> B\<^bsup>X\<^esup> \<and> monomorphism m"
  proof (intro exI[where x="(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>"], safe)
    show "(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> : A\<^bsup>X\<^esup> \<rightarrow> B\<^bsup>X\<^esup>"
      by typecheck_cfuncs
    then show "monomorphism((m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)"
    proof (unfold monomorphism_def3, clarify)
      fix g h Z
      assume g_type[type_rule]: "g : Z \<rightarrow> A\<^bsup>X\<^esup>"
      assume h_type[type_rule]: "h : Z \<rightarrow> A\<^bsup>X\<^esup>"

      assume eq: "(m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c g = (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp> \<circ>\<^sub>c h"
      show "g = h"
      proof (typecheck_cfuncs, rule same_evals_equal[where Z=Z, where A=X, where X=A], clarify)
          have "((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = 
                ((eval_func B X) \<circ>\<^sub>c (id X \<times>\<^sub>f (m \<circ>\<^sub>c eval_func A X)\<^sup>\<sharp>)) \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            by (typecheck_cfuncs, smt comp_associative2 eq inv_transpose_func_def3 inv_transpose_of_composition)
          then have "(m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = (m \<circ>\<^sub>c eval_func A X) \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            by (smt comp_type eval_func_type m_def(1) transpose_func_def)
          then have "m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g))  = m \<circ>\<^sub>c (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h))"
            by (typecheck_cfuncs, smt comp_associative2)
          then have "eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g)  = eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h)"
            using m_def monomorphism_def3 by (typecheck_cfuncs, blast)
          then show "(eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f g))  = (eval_func A X \<circ>\<^sub>c (id X \<times>\<^sub>f h))"
            by (typecheck_cfuncs, smt comp_associative2)
      qed
    qed
  qed
qed

lemma exp_preserves_card3:
  assumes "A \<le>\<^sub>c B"
  assumes "X \<le>\<^sub>c Y"
  assumes "nonempty(X)"
  shows "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
proof - 
  have leq1: "X\<^bsup>A\<^esup> \<le>\<^sub>c X\<^bsup>B\<^esup>"
    by (simp add: assms(1,3) exp_preserves_card1)    
  have leq2: "X\<^bsup>B\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    by (simp add: assms(2) exp_preserves_card2)
  show "X\<^bsup>A\<^esup> \<le>\<^sub>c Y\<^bsup>B\<^esup>"
    using leq1 leq2 set_card_transitive by blast
qed

end