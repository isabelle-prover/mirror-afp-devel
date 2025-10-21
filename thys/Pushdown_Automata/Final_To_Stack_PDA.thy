subsection \<open>Final Acceptance to Stack Acceptance\<close>

text \<open>Starting from a PDA that accepts by final state
we construct an equivalent PDA that accepts by empty stack,
following Kozen \cite{kozen2007automata}.\<close>

theory Final_To_Stack_PDA
imports Pushdown_Automata 
begin

datatype 'q st_extended = Old_st 'q | New_init | New_final 
datatype 's sym_extended = Old_sym 's | New_sym

lemma inj_Old_sym: "inj Old_sym"
by (meson injI sym_extended.inject)

instance st_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = Old_st q} \<union> {New_init, New_final}"
    by auto (metis st_extended.exhaust)
  show "finite (UNIV :: 'a st_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

instance sym_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>s. t = Old_sym s} \<union> {New_sym}"
    by auto (metis sym_extended.exhaust)
  show "finite (UNIV :: 'a sym_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

context pda begin

fun stack_of_final_delta :: "'q st_extended \<Rightarrow> 'a \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "stack_of_final_delta (Old_st q) a (Old_sym Z) = (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (\<delta> M q a Z)"
| "stack_of_final_delta  _ _ _ = {}"

fun stack_of_final_delta_eps :: "'q st_extended \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "stack_of_final_delta_eps (Old_st q) (Old_sym Z) = (if q \<in> final_states M then {(New_final, [Old_sym Z])} else {}) \<union> 
                                                        (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (\<delta>\<epsilon> M q Z)"
| "stack_of_final_delta_eps (Old_st q) New_sym = (if q \<in> final_states M then {(New_final, [New_sym])} else {})"
| "stack_of_final_delta_eps New_init New_sym = {(Old_st (init_state M), [Old_sym (init_symbol M), New_sym])}"
| "stack_of_final_delta_eps New_final _ = {(New_final, [])}"
| "stack_of_final_delta_eps _ _ = {}"

definition stack_of_final_pda :: "('q st_extended, 'a, 's sym_extended) pda" where
  "stack_of_final_pda \<equiv> \<lparr> init_state = New_init, init_symbol = New_sym, final_states = {New_final}, 
                    delta = stack_of_final_delta, delta_eps = stack_of_final_delta_eps\<rparr>"

lemma pda_final_to_stack:
  "pda stack_of_final_pda"
proof (standard, goal_cases)
  case (1 p x z)
  have "finite (stack_of_final_delta p x z)"
    by (induction p x z rule: stack_of_final_delta.induct) (auto simp: finite_delta)
  then show ?case
    by (simp add: stack_of_final_pda_def)
next
  case (2 p z)
  have "finite (stack_of_final_delta_eps p z)"
    by (induction p z rule: stack_of_final_delta_eps.induct) (auto simp: finite_delta_eps)
  then show ?case
    by (simp add: stack_of_final_pda_def)
qed

lemma stack_of_final_pda_trans:
  "(p, \<beta>) \<in> \<delta> M q a Z \<longleftrightarrow> 
          (Old_st p, map Old_sym \<beta>) \<in> \<delta> stack_of_final_pda (Old_st q) a (Old_sym Z)"
by (auto simp: stack_of_final_pda_def inj_map_eq_map[OF inj_Old_sym])

lemma stack_of_final_pda_eps:
  "(p, \<beta>) \<in> \<delta>\<epsilon> M q Z \<longleftrightarrow> (Old_st p, map Old_sym \<beta>) \<in> \<delta>\<epsilon> stack_of_final_pda (Old_st q) (Old_sym Z)"
by (auto simp: stack_of_final_pda_def inj_map_eq_map[OF inj_Old_sym] split: if_splits)

lemma stack_of_final_pda_step:
  "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
             pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, map Old_sym \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain Z \<alpha> where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and rule: 
              "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z) 
                 \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> \<delta> M p\<^sub>1 a Z)"
    using step\<^sub>1_rule_ext by auto
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta> @ map Old_sym \<alpha> \<and> 
                    (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> \<delta>\<epsilon> stack_of_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
                \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta> @ map Old_sym \<alpha> \<and> 
                    (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> \<delta> stack_of_final_pda (Old_st p\<^sub>1) a (Old_sym Z))"
    using stack_of_final_pda_trans stack_of_final_pda_eps by fastforce
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> stack_of_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, \<beta>) \<in> \<delta> stack_of_final_pda (Old_st p\<^sub>1) a (Old_sym Z))"  by blast
  with \<alpha>\<^sub>1_def show ?r
    using pda.step\<^sub>1_rule[OF pda_final_to_stack] by simp
next
  assume ?r
  then obtain Z \<alpha> where map_\<alpha>\<^sub>1_def: "map Old_sym \<alpha>\<^sub>1 = Old_sym Z # map Old_sym \<alpha>" and rule: 
        "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta>@ map Old_sym \<alpha> \<and> 
            (Old_st p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> stack_of_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
       \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta>@ map Old_sym \<alpha> \<and> 
            (Old_st p\<^sub>2,\<beta>) \<in> \<delta> stack_of_final_pda (Old_st p\<^sub>1) a (Old_sym Z))"
    using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by auto
  from map_\<alpha>\<^sub>1_def have \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z # \<alpha>"
    by (metis list.inj_map_strong list.simps(9) sym_extended.inject)
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta>@ map Old_sym \<alpha> \<and> 
                    (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> \<delta>\<epsilon> stack_of_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
                \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta>@ map Old_sym \<alpha> \<and> 
                    (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> \<delta> stack_of_final_pda (Old_st p\<^sub>1) a (Old_sym Z))"
    using append_eq_map_conv[where ?f = Old_sym] by metis
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2, \<beta>) \<in> \<delta>\<epsilon> M p\<^sub>1 Z)
               \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> \<delta> M p\<^sub>1 a Z)"
    using stack_of_final_pda_trans stack_of_final_pda_eps by (metis list.inj_map_strong sym_extended.inject map_append)
  with \<alpha>\<^sub>1_def show ?l
    using step\<^sub>1_rule by simp
qed

abbreviation \<alpha>_with_new :: "'s list \<Rightarrow> 's sym_extended list" where 
  "\<alpha>_with_new \<alpha> \<equiv> map Old_sym \<alpha> @ [New_sym]"

lemma stack_of_final_pda_step\<^sub>1_drop:
  assumes "pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) 
                                          (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
    shows "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms obtain Z \<alpha> where \<alpha>\<^sub>1_with_new_def: "\<alpha>_with_new \<alpha>\<^sub>1 = Z # \<alpha>" and rule: 
      "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>_with_new \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (Old_st p\<^sub>2, \<beta>) \<in> stack_of_final_delta_eps (Old_st p\<^sub>1) Z) 
          \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>_with_new \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (Old_st p\<^sub>2,\<beta>) \<in> stack_of_final_delta (Old_st p\<^sub>1) a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by (auto simp: stack_of_final_pda_def)
  from rule have "Z \<noteq> New_sym"
    by (induction "Old_st p\<^sub>1" Z rule: stack_of_final_delta_eps.induct) (auto, metis empty_iff fst_conv singletonD st_extended.simps(5))
  with \<alpha>\<^sub>1_with_new_def have "map Old_sym \<alpha>\<^sub>1 \<noteq> []" by auto
  with assms have "pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, map Old_sym \<alpha>\<^sub>1) 
                                            (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2)"
    using pda.step\<^sub>1_stack_drop[OF pda_final_to_stack] by blast
  thus ?thesis
    using stack_of_final_pda_step by simp
qed

lemma stack_of_final_pda_from_old:
  assumes "pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "(\<exists>p\<^sub>2'. p\<^sub>2 = Old_st p\<^sub>2') \<or> p\<^sub>2 = New_final"
proof -
  from assms obtain Z \<alpha> where rule: 
        "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2, \<beta>) \<in> stack_of_final_delta_eps (Old_st p\<^sub>1) Z) 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> stack_of_final_delta (Old_st p\<^sub>1) a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by (auto simp: stack_of_final_pda_def)+
  thus ?thesis 
    by (induction "Old_st p\<^sub>1" Z rule: stack_of_final_delta_eps.induct, auto) (metis empty_iff fst_conv singletonD)+
qed

lemma stack_of_final_pda_from_final:
  assumes "pda.step\<^sub>1 stack_of_final_pda (New_final, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>Z'. p\<^sub>2 = New_final \<and> w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>1 = Z'#\<alpha>\<^sub>2"
proof -
  from assms obtain Z \<alpha> where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and rule: 
        "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> stack_of_final_delta_eps New_final Z) 
          \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> stack_of_final_delta New_final a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by (auto simp: stack_of_final_pda_def)
  thus ?thesis 
    by (induction "New_final:: 'q st_extended" Z rule: stack_of_final_delta_eps.induct) auto
qed

lemma stack_of_final_pda_from_oldn:
  assumes "pda.steps stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. p\<^sub>2 = Old_st q' \<or> p\<^sub>2 = New_final"
proof (induction "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: pda.steps_induct2_bw[OF pda_final_to_stack])
  case (3 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
  then show ?case
    using stack_of_final_pda_from_final stack_of_final_pda_from_old by blast
qed (auto simp: assms)

lemma stack_of_final_pda_to_old:
  assumes "pda.step\<^sub>1 stack_of_final_pda (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "(\<exists>q'. p\<^sub>1 = Old_st q') \<or> p\<^sub>1 = New_init"
using assms stack_of_final_pda_from_final by (metis st_extended.exhaust)

lemma stack_of_final_pda_bottom_elem:
  assumes "pda.steps stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<gamma>)"
  shows "\<exists>\<alpha>. \<gamma> = \<alpha>_with_new \<alpha>"
proof (induction "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)" "(Old_st p\<^sub>2, w\<^sub>2, \<gamma>)" arbitrary: p\<^sub>2 w\<^sub>2 \<gamma> rule: pda.steps_induct2_bw[OF pda_final_to_stack])
  case (3 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 w\<^sub>3 \<alpha>\<^sub>3 p\<^sub>3)
  obtain p\<^sub>2' where p\<^sub>2_def: "p\<^sub>2 = Old_st p\<^sub>2'"
    using stack_of_final_pda_from_oldn[OF 3(1)] stack_of_final_pda_to_old[OF 3(2)] by blast
  with 3(3) have \<alpha>\<^sub>2_def: "\<exists>\<alpha>. \<alpha>\<^sub>2 = \<alpha>_with_new \<alpha>" by simp
  from p\<^sub>2_def 3(2) obtain Z \<alpha> where \<alpha>\<^sub>2_split: "\<alpha>\<^sub>2 = Z # \<alpha>" and rule:
    "(\<exists>\<beta>. w\<^sub>3 = w\<^sub>2 \<and> \<alpha>\<^sub>3 = \<beta> @ \<alpha> \<and> (Old_st p\<^sub>3, \<beta>) \<in> stack_of_final_delta_eps (Old_st p\<^sub>2') Z) 
     \<or> (\<exists>a \<beta>. w\<^sub>2 = a # w\<^sub>3 \<and> \<alpha>\<^sub>3 = \<beta> @ \<alpha> \<and> (Old_st p\<^sub>3, \<beta>) \<in> stack_of_final_delta (Old_st p\<^sub>2') a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by (auto simp: stack_of_final_pda_def)
  hence "\<exists>Z'. Z = Old_sym Z'"
    by (induction "Old_st p\<^sub>2'" Z rule: stack_of_final_delta_eps.induct) 
          (auto, meson empty_iff insert_iff prod.inject st_extended.distinct(3))
  with \<alpha>\<^sub>2_def \<alpha>\<^sub>2_split have "\<exists>\<gamma>. \<alpha> = \<alpha>_with_new \<gamma>"
    by (metis hd_append list.sel(1,3) map_tl sym_extended.simps(3) tl_append_if)
  with rule show ?case
    by (induction "Old_st p\<^sub>2'" Z rule: stack_of_final_delta_eps.induct, auto)
        (metis empty_iff fst_conv singleton_iff st_extended.distinct(3), metis map_append,
           metis map_append, metis empty_iff fst_conv singleton_iff st_extended.distinct(3))
qed (auto simp: assms)

lemma stack_of_final_pda_stepn:
  "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>(n) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> 
      pda.stepn stack_of_final_pda n (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
    from step\<^sub>n(3) have "pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2) (Old_st p\<^sub>3, w\<^sub>3, map Old_sym \<alpha>\<^sub>3)"
      using stack_of_final_pda_step by simp
    hence "pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2) (Old_st p\<^sub>3, w\<^sub>3, \<alpha>_with_new \<alpha>\<^sub>3)"
      using pda.step\<^sub>1_stack_app[OF pda_final_to_stack] by simp
    with step\<^sub>n(2) show ?case
      by (simp add: pda.step\<^sub>n[OF pda_final_to_stack])
  qed (simp add: pda.refl\<^sub>n[OF pda_final_to_stack])
next
  assume r: ?r thus ?l
  proof (induction n "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)" "(Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)" 
                 arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: pda.stepn.induct[OF pda_final_to_stack])
    case (3 n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 w\<^sub>3 p\<^sub>3 \<alpha>\<^sub>3)
    from 3(1) have steps_3_1: "pda.steps stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      using pda.stepn_steps[OF pda_final_to_stack] by blast
    obtain p\<^sub>2' where p\<^sub>2_def: "p\<^sub>2 = Old_st p\<^sub>2'"
      using stack_of_final_pda_from_oldn[OF steps_3_1] stack_of_final_pda_to_old[OF 3(3)] by blast
    with steps_3_1 obtain \<gamma> where \<alpha>\<^sub>2_def: "\<alpha>\<^sub>2 = \<alpha>_with_new \<gamma>"
      using stack_of_final_pda_bottom_elem by blast

    with p\<^sub>2_def 3(1,2) have "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2', w\<^sub>2, \<gamma>)" by simp

    moreover from p\<^sub>2_def \<alpha>\<^sub>2_def 3(3) have "pda.step\<^sub>1 M (p\<^sub>2', w\<^sub>2, \<gamma>) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
      using stack_of_final_pda_step\<^sub>1_drop by simp

    ultimately show ?case by simp
  qed (rule r, metis refl\<^sub>n list.inj_map_strong sym_extended.inject)
qed

lemma stack_of_final_pda_steps:
  "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>* (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
      pda.steps stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
using stack_of_final_pda_stepn pda.stepn_steps[OF pda_final_to_stack] stepn_steps by simp

lemma stack_of_final_pda_final_dump:
  "pda.steps stack_of_final_pda (New_final, w, \<gamma>) (New_final, w, [])"
proof (induction \<gamma>)
  case (Cons Z \<gamma>)
  have "(New_final, []) \<in> stack_of_final_delta_eps New_final Z" by simp
  hence "pda.step\<^sub>1 stack_of_final_pda (New_final, w, Z # \<gamma>) (New_final, w, \<gamma>)"
    using pda.step\<^sub>1_rule[OF pda_final_to_stack] by (simp add: stack_of_final_pda_def)
  with Cons.IH show ?case
    using pda.step\<^sub>1_steps[OF pda_final_to_stack] pda.steps_trans[OF pda_final_to_stack] by blast
qed (simp add: pda.steps_refl[OF pda_final_to_stack])

lemma stack_of_final_pda_first_step:
  assumes "pda.step\<^sub>1 stack_of_final_pda (New_init, w\<^sub>1, [New_sym]) (p\<^sub>2, w\<^sub>2, \<alpha>)"
  shows "p\<^sub>2 = Old_st (init_state M) \<and> w\<^sub>2 = w\<^sub>1 \<and> \<alpha> = [Old_sym (init_symbol M), New_sym]"
using assms pda.step\<^sub>1_rule[OF pda_final_to_stack] by (simp add: stack_of_final_pda_def)

lemma stack_of_final_pda_empty_only_final:
  assumes "pda.steps stack_of_final_pda (New_init, w\<^sub>1, [New_sym]) (q, w\<^sub>2, [])"
  shows "q = New_final"
proof -
  from assms have "pda.steps stack_of_final_pda (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym]) (q, w\<^sub>2, [])"
    using pda.steps_not_refl_split_first[OF pda_final_to_stack] stack_of_final_pda_first_step by blast
  thus ?thesis
    using stack_of_final_pda_bottom_elem[of "init_state M" w\<^sub>1 "[init_symbol M]" _ w\<^sub>2 "[]"]  stack_of_final_pda_from_oldn by fastforce
qed

lemma stack_of_final_pda_split_old_final:
  assumes "pda.stepn stack_of_final_pda (Suc n) (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (New_final :: 'q st_extended, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>q k \<gamma>. k \<le> n \<and> q \<in> final_states M \<and>
            pda.stepn stack_of_final_pda k (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st q, w\<^sub>2, \<gamma>) \<and>
            pda.step\<^sub>1 stack_of_final_pda (Old_st q, w\<^sub>2, \<gamma>) (New_final, w\<^sub>2, \<gamma>) \<and>
            pda.stepn stack_of_final_pda (n-k) (New_final, w\<^sub>2, \<gamma>) (New_final, w\<^sub>2, \<alpha>\<^sub>2)"
using assms proof (induction "Suc n" "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(New_final :: 'q st_extended, w\<^sub>2, \<alpha>\<^sub>2)" 
                          arbitrary: n w\<^sub>2 \<alpha>\<^sub>2 rule: pda.stepn.induct[OF pda_final_to_stack])
  case (3 n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 w\<^sub>3 \<alpha>\<^sub>3)
  then show ?case proof (cases n)
    case 0
    with 3(1) have p\<^sub>2_def: "Old_st p\<^sub>1 = p\<^sub>2" and w12: "w\<^sub>1 = w\<^sub>2" and a12: "\<alpha>\<^sub>1 = \<alpha>\<^sub>2"
      using pda.stepn_zeroE[OF pda_final_to_stack] by blast+
    from p\<^sub>2_def 3(3) obtain Z \<alpha> where \<alpha>\<^sub>2_def: "\<alpha>\<^sub>2 = Z # \<alpha>" and rule: 
            "(\<exists>\<beta>. w\<^sub>3 = w\<^sub>2 \<and> \<alpha>\<^sub>3 = \<beta>@\<alpha> \<and> (New_final,\<beta>) \<in> stack_of_final_delta_eps (Old_st p\<^sub>1) Z) 
               \<or> (\<exists>a \<beta>. w\<^sub>2 = a # w\<^sub>3 \<and> \<alpha>\<^sub>3 = \<beta>@\<alpha> \<and> (New_final,\<beta>) \<in> stack_of_final_delta (Old_st p\<^sub>1) a Z)"
      using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by (auto simp: stack_of_final_pda_def)
    from \<alpha>\<^sub>2_def rule have p\<^sub>1_final: "p\<^sub>1 \<in> final_states M" and w23: "w\<^sub>3 = w\<^sub>2" and a23: "\<alpha>\<^sub>3 = \<alpha>\<^sub>2"
      by (induction "Old_st p\<^sub>1" Z rule: stack_of_final_delta_eps.induct, auto)
         (meson empty_iff, meson empty_iff prod.inject singletonD, meson empty_iff, meson empty_iff prod.inject singletonD)

    from w12 w23 a12 a23 have "pda.stepn stack_of_final_pda 0 (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st p\<^sub>1, w\<^sub>3, \<alpha>\<^sub>3)"
      using pda.refl\<^sub>n[OF pda_final_to_stack] by simp

    moreover from 3(3) p\<^sub>2_def w23 a23 have "pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>1, w\<^sub>3, \<alpha>\<^sub>3) (New_final, w\<^sub>3, \<alpha>\<^sub>3)" by simp

    moreover from 0 have "pda.stepn stack_of_final_pda (n - 0) (New_final, w\<^sub>3, \<alpha>\<^sub>3) (New_final, w\<^sub>3, \<alpha>\<^sub>3)"
      using pda.refl\<^sub>n[OF pda_final_to_stack] by simp

    ultimately show ?thesis 
      using p\<^sub>1_final by blast
  next
    case (Suc n')
    then show ?thesis proof (cases "p\<^sub>2 = New_final")
      case True
      with Suc 3(1,2) obtain q k \<gamma> where k_less: "k \<le> n'" and q_final: "q \<in> final_states M" and
       stepn: "pda.stepn stack_of_final_pda k (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st q, w\<^sub>2, \<gamma>)" and
       step1: "pda.step\<^sub>1 stack_of_final_pda (Old_st q, w\<^sub>2, \<gamma>) (New_final, w\<^sub>2, \<gamma>)" and
       stepn': "pda.stepn stack_of_final_pda (n' - k) (New_final, w\<^sub>2, \<gamma>) (New_final, w\<^sub>2, \<alpha>\<^sub>2)" by blast
      from True 3(3) obtain Z' \<alpha>' where "\<alpha>\<^sub>2 = Z' # \<alpha>'" and rule: 
          "(\<exists>\<beta>. w\<^sub>3 = w\<^sub>2 \<and> \<alpha>\<^sub>3 = \<beta>@\<alpha>' \<and> (New_final,\<beta>) \<in> stack_of_final_delta_eps New_final Z') 
             \<or> (\<exists>a \<beta>. w\<^sub>2 = a # w\<^sub>3 \<and> \<alpha>\<^sub>3 = \<beta>@\<alpha>' \<and> (New_final,\<beta>) \<in> stack_of_final_delta New_final a Z')"
        using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by (auto simp: stack_of_final_pda_def)
      from rule have w23: "w\<^sub>3 = w\<^sub>2"
        by (induction "New_final :: 'q st_extended" Z' rule: stack_of_final_delta_eps.induct) auto

      moreover from k_less Suc have "k \<le> n" by simp

      moreover from stepn w23 have "pda.stepn stack_of_final_pda k (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st q, w\<^sub>3, \<gamma>)" by simp

      moreover from step1 w23 have "pda.step\<^sub>1 stack_of_final_pda (Old_st q, w\<^sub>3, \<gamma>) (New_final, w\<^sub>3, \<gamma>)" by simp

      moreover from stepn' 3(3) True w23 Suc k_less have "pda.stepn stack_of_final_pda (n - k) (New_final, w\<^sub>3, \<gamma>) (New_final, w\<^sub>3, \<alpha>\<^sub>3)"
        using pda.step\<^sub>n[OF pda_final_to_stack] by (simp add: Suc_diff_le)

      ultimately show ?thesis 
        using q_final by blast
    next
      case False
      with 3(1) obtain p\<^sub>2' where p\<^sub>2_def: "p\<^sub>2 = Old_st p\<^sub>2'"
        using stack_of_final_pda_from_oldn pda.stepn_steps[OF pda_final_to_stack] by blast
      from p\<^sub>2_def 3(3) obtain Z' \<alpha>' where "\<alpha>\<^sub>2 = Z' # \<alpha>'" and 
            "(\<exists>\<beta>. w\<^sub>3 = w\<^sub>2 \<and> \<alpha>\<^sub>3 = \<beta>@\<alpha>' \<and> (New_final,\<beta>) \<in> stack_of_final_delta_eps (Old_st p\<^sub>2') Z') 
               \<or> (\<exists>a \<beta>. w\<^sub>2 = a # w\<^sub>3 \<and> \<alpha>\<^sub>3 = \<beta>@\<alpha>' \<and> (New_final,\<beta>) \<in> stack_of_final_delta (Old_st p\<^sub>2') a Z')"
        using pda.step\<^sub>1_rule_ext[OF pda_final_to_stack] by (auto simp: stack_of_final_pda_def)
      hence p\<^sub>2_final: "p\<^sub>2' \<in> final_states M" and w23: "w\<^sub>3 = w\<^sub>2" and a23: "\<alpha>\<^sub>3 = \<alpha>\<^sub>2"
        by (induction "Old_st p\<^sub>2'" Z' rule: stack_of_final_delta_eps.induct, auto)
          (meson empty_iff, meson empty_iff prod.inject singletonD, meson empty_iff, meson empty_iff prod.inject singletonD)

      from 3(1) p\<^sub>2_def w23 a23 have "pda.stepn stack_of_final_pda n (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st p\<^sub>2', w\<^sub>3, \<alpha>\<^sub>3)" by simp

      moreover from 3(3) p\<^sub>2_def w23 a23 have "pda.step\<^sub>1 stack_of_final_pda (Old_st p\<^sub>2', w\<^sub>3, \<alpha>\<^sub>3) (New_final, w\<^sub>3, \<alpha>\<^sub>3)" by simp

      moreover have "pda.stepn stack_of_final_pda 0 (New_final, w\<^sub>3, \<alpha>\<^sub>3) (New_final, w\<^sub>3, \<alpha>\<^sub>3)"
        using pda.refl\<^sub>n[OF pda_final_to_stack] by simp

      ultimately show ?thesis 
        using p\<^sub>2_final by force
    qed
  qed
qed (simp add: assms)

lemma stack_of_final_pda_split_path:
  assumes "pda.stepn stack_of_final_pda (Suc (Suc n)) (New_init, w\<^sub>1, [New_sym]) (New_final, w\<^sub>2, \<gamma>)"
    shows "\<exists>q k \<alpha>. k \<le> n \<and> q \<in> final_states M \<and> pda.step\<^sub>1 stack_of_final_pda (New_init, w\<^sub>1, [New_sym]) 
                                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym]) \<and>
           pda.stepn stack_of_final_pda k (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                                               (Old_st q, w\<^sub>2, \<alpha>) \<and>
           pda.step\<^sub>1 stack_of_final_pda (Old_st q, w\<^sub>2, \<alpha>) (New_final, w\<^sub>2, \<alpha>) \<and>
           pda.stepn stack_of_final_pda (n-k) (New_final, w\<^sub>2, \<alpha>) (New_final, w\<^sub>2, \<gamma>)"
proof -
  from assms have fstep: "pda.step\<^sub>1 stack_of_final_pda (New_init, w\<^sub>1, [New_sym]) 
                                      (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])"
                 and stepn: "pda.stepn stack_of_final_pda (Suc n) 
                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                              (New_final, w\<^sub>2, \<gamma>)"
    using pda.stepn_split_first[OF pda_final_to_stack] stack_of_final_pda_first_step by blast+
  from stepn have "\<exists>q k \<alpha>. k \<le> n \<and> q \<in> final_states M \<and>
           pda.stepn stack_of_final_pda k (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                                               (Old_st q, w\<^sub>2, \<alpha>) \<and>
           pda.step\<^sub>1 stack_of_final_pda (Old_st q, w\<^sub>2, \<alpha>) (New_final, w\<^sub>2, \<alpha>) \<and>
           pda.stepn stack_of_final_pda (n-k) (New_final, w\<^sub>2, \<alpha>) (New_final, w\<^sub>2, \<gamma>)"
    using stack_of_final_pda_split_old_final by blast
  with fstep show ?thesis by blast
qed

lemma stack_of_final_pda_path_length:
  assumes "pda.stepn stack_of_final_pda n (New_init, w\<^sub>1, [New_sym]) (New_final, w\<^sub>2, \<gamma>)"
    shows "\<exists>n'. n = Suc (Suc n')"
proof -
  from assms obtain n' where n_def: "n = Suc n'" and 
            stepn': "pda.stepn stack_of_final_pda n' (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                                              (New_final, w\<^sub>2, \<gamma>)"
    using pda.stepn_not_refl_split_first[OF pda_final_to_stack] stack_of_final_pda_first_step by blast
  from stepn' obtain n'' where "n' = Suc n''"
    using pda.stepn_not_refl_split_first[OF pda_final_to_stack] by blast
  with n_def show ?thesis by simp
qed

lemma accepted_final_to_stack:
"(\<exists>q \<gamma>. q \<in> final_states M \<and> (init_state M, w, [init_symbol M]) \<leadsto>* (q, [], \<gamma>)) \<longleftrightarrow>
  (\<exists>q. pda.steps stack_of_final_pda (init_state stack_of_final_pda, w, [init_symbol stack_of_final_pda]) (q, [], []))" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain q \<gamma> where q_final: "q \<in> final_states M" and steps: "(init_state M, w, [init_symbol M]) \<leadsto>* (q, [], \<gamma>)" by blast
  obtain Z \<alpha> where map_\<gamma>_def: "\<alpha>_with_new \<gamma> = Z#\<alpha>"
    by (auto intro: list.exhaust_sel)
  from q_final have "(New_final, [Z]) \<in> stack_of_final_delta_eps (Old_st q) Z"
    by (induction "Old_st q" Z rule: stack_of_final_delta_eps.induct) auto

  with map_\<gamma>_def have "pda.step\<^sub>1 stack_of_final_pda (Old_st q, [], \<alpha>_with_new \<gamma>) (New_final, [], Z#\<alpha>)"
    using pda.step\<^sub>1_rule[OF pda_final_to_stack] by (simp add: stack_of_final_pda_def)

  moreover from steps have "pda.steps stack_of_final_pda (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym]) 
                                                    (Old_st q, [], \<alpha>_with_new \<gamma>)"
    using stack_of_final_pda_steps by simp

  moreover have "pda.step\<^sub>1 stack_of_final_pda (init_state stack_of_final_pda, w, [init_symbol stack_of_final_pda])
                                         (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym])"
    using pda.step\<^sub>1_rule[OF pda_final_to_stack] by (simp add: stack_of_final_pda_def)

  moreover have "pda.steps stack_of_final_pda (New_final, [], Z#\<alpha>) (New_final, [], [])"
    using stack_of_final_pda_final_dump by simp

  ultimately show ?r 
    using pda.step\<^sub>1_steps[OF pda_final_to_stack] pda.steps_trans[OF pda_final_to_stack] by metis
next
  assume ?r
  then obtain q where steps: "pda.steps stack_of_final_pda (New_init, w, [New_sym]) (q, [], [])"
    by (auto simp: stack_of_final_pda_def)
  hence q_def: "q = New_final"
    using stack_of_final_pda_empty_only_final by simp
  with steps obtain n where stepn: "pda.stepn stack_of_final_pda n (New_init, w, [New_sym]) (New_final, [], [])"
    using pda.stepn_steps[OF pda_final_to_stack] by blast
  then obtain n' where "n = Suc (Suc n')"
    using stack_of_final_pda_path_length by blast
  with stepn obtain p k \<alpha> where p_final: "p \<in> final_states M" and stepn': "pda.stepn stack_of_final_pda k 
                  (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym]) (Old_st p, [], \<alpha>)"
    using stack_of_final_pda_split_path by blast
  from stepn' obtain \<alpha>' where "\<alpha> = \<alpha>_with_new \<alpha>'"
    using stack_of_final_pda_bottom_elem pda.stepn_steps[OF pda_final_to_stack]
    by (metis (no_types, opaque_lifting) append_Cons append_Nil list.simps(8,9))
  with stepn' have "pda.stepn M k (init_state M, w, [init_symbol M]) (p, [], \<alpha>')"
    using stack_of_final_pda_stepn by simp
  with p_final show ?l
    using stepn_steps by blast
qed

lemma final_to_stack:
  "pda.accept_final M = pda.accept_stack stack_of_final_pda"
  unfolding accept_final_def pda.accept_stack_def[OF pda_final_to_stack] using accepted_final_to_stack by blast

end
end