theory Flatten_Iter
  imports
  Basic_Assn
  "Separation_Logic_Imperative_HOL.Imp_List_Spec"
  "HOL-Real_Asymp.Inst_Existentials"
begin


text "This locale takes an iterator that refines a list of elements that themselves
can be iterated and defines an iterator over the flattened list of lower level elements"

locale flatten_iter =
  inner_list: imp_list_iterate is_inner_list inner_is_it inner_it_init inner_it_has_next inner_it_next + 
  outer_list: imp_list_iterate is_outer_list outer_is_it outer_it_init outer_it_has_next outer_it_next 
  for is_outer_list :: "'l list \<Rightarrow> 'm \<Rightarrow> assn"
  and outer_is_it :: "'l list \<Rightarrow> 'm \<Rightarrow> 'l list \<Rightarrow> 'oit \<Rightarrow> assn"
  and outer_it_init :: "'m \<Rightarrow> ('oit) Heap"
  and outer_it_has_next :: "'oit \<Rightarrow> bool Heap"
  and outer_it_next :: "'oit \<Rightarrow> ('l\<times>'oit) Heap"
  and is_inner_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  and inner_is_it :: "'a list \<Rightarrow> 'l \<Rightarrow> 'a list \<Rightarrow> 'iit \<Rightarrow> assn"
  and inner_it_init :: "'l \<Rightarrow> ('iit) Heap"
  and inner_it_has_next :: "'iit \<Rightarrow> bool Heap"
  and inner_it_next :: "'iit \<Rightarrow> ('a\<times>'iit) Heap"
begin

fun is_flatten_list :: "'a list \<Rightarrow> 'm \<Rightarrow> assn" where
  "is_flatten_list ls lsi = (\<exists>\<^sub>A lsi' ls'.
    is_outer_list lsi' lsi * list_assn is_inner_list ls' lsi' * \<up>(ls = concat ls')
)"

lemma flatten_prec:
  "precise is_flatten_list"
  apply (intro preciseI)
  apply (auto)
proof (goal_cases)
  case (1 aa b p F F' lsi' ls' lsi'a ls'a)
  then have *:
      "\<exists>G G'. (aa, b) \<Turnstile> list_assn is_inner_list ls'a lsi'a * G \<and>\<^sub>A list_assn is_inner_list ls' lsi' * G'"
    by (smt (z3) assn_aci(10) assn_times_comm)

  have "lsi' = lsi'a"
    using 1
    by (metis outer_list.precise preciseD star_assoc)
  moreover have "length ls'a = length lsi'a" "length ls' = length lsi'" 
    using 1 by (auto simp add: mod_and_dist dest!: mod_starD list_assn_len)
  ultimately have "length ls' = length lsi'" "length lsi' = length lsi'a" "length lsi'a = length ls'a"
    by auto
  then show ?case
    using * \<open>lsi' = lsi'a\<close>
    proof(induction ls' lsi' lsi'a ls'a arbitrary: p rule: list_induct4)
      case Nil
      then show ?case by auto
    next
      case (Cons x xs y ys z zs w ws)
      then have "concat ws = concat xs"
        apply simp
        by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult.left_commute star_assoc)
      moreover have "x = w"
        using "Cons.prems" preciseD[OF inner_list.precise, where h="(aa,b)"]
        apply(simp)
        using assn_times_assoc by fastforce
      ultimately show ?case 
        by auto
    qed
qed

(*type_synonym flatten_it = "'iit \<times> 'oit"*)
fun is_flatten_it :: "'a list \<Rightarrow> 'm \<Rightarrow> 'a list \<Rightarrow> ('oit \<times> 'iit option) \<Rightarrow> assn"
  where 
"is_flatten_it ls lsi [] (oit, None) = 
        (\<exists>\<^sub>A lsi' lsi''.
          list_assn is_inner_list lsi'' lsi' *
           \<up>(ls = (concat lsi'')) *
          outer_is_it lsi' lsi [] oit
)" |
"is_flatten_it ls lsi ls2 (oit, Some iit) = 
        (\<exists>\<^sub>A lsi' ls2' ls1' lsi1 lsi2 lsim ls2m lsm ls1m.
          list_assn is_inner_list ls1' lsi1 *
          list_assn is_inner_list ls2' lsi2 *
           \<up>(ls2m \<noteq> [] \<and> ls2 = ls2m@(concat ls2') \<and> ls = (concat (ls1'@lsm#ls2'))) *
          outer_is_it lsi' lsi lsi2 oit *
          \<up>(lsm = ls1m@ls2m \<and> lsi'=(lsi1@lsim#lsi2)) *
          inner_is_it lsm lsim ls2m iit
)
" |
"is_flatten_it _ _ _ _ = false"

partial_function (heap) flatten_it_adjust:: "'oit \<Rightarrow> 'iit \<Rightarrow> ('oit \<times> 'iit option) Heap" where
"flatten_it_adjust oit iit = do {
      ihasnext \<leftarrow> inner_it_has_next iit;
      if ihasnext then
        return (oit, Some iit)
      else do {
        ohasnext \<leftarrow> outer_it_has_next oit;
        if \<not>ohasnext then
          return (oit, None)
        else do {
          (next, oit) \<leftarrow> outer_it_next oit;
          nextit \<leftarrow> inner_it_init next;
          flatten_it_adjust oit nextit
        }
      }
  }
"

thm list_assn_len

lemma flatten_it_adjust_rule: 
  " <list_assn is_inner_list ls1' ls1 * list_assn is_inner_list ls2' ls2 *
      outer_is_it (ls1@lsim#ls2) lsi ls2 oit * inner_is_it (lsm1@lsm2) lsim lsm2 iit>
  flatten_it_adjust oit iit
  <is_flatten_it (concat (ls1'@(lsm1@lsm2)#ls2')) lsi (concat (lsm2#ls2'))>\<^sub>t"
proof (induction ls2 arbitrary: ls1' ls1 ls2' lsim lsm1 lsm2 oit iit)
  case Nil
  then show ?case
  apply(subst flatten_it_adjust.simps)
  apply (sep_auto eintros del: exI heap add: inner_list.it_has_next_rule)
  apply(inst_existentials "(ls1 @ lsim # [])" ls2' ls1' ls1 "[]::'l list" lsim lsm2 "lsm1@lsm2")
  subgoal by auto
  subgoal by (sep_auto)
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  subgoal
    apply (vcg (ss))
    apply (sep_auto eintros del: exI)
    apply(inst_existentials "(ls1 @ [lsim])" "ls1'@[lsm1]")
    subgoal by auto
        subgoal
          apply(auto simp add: list_assn_app_one)
          using inner_list.quit_iteration
          by (smt (z3) assn_aci(9) assn_times_comm ent_true_drop(1) fr_refl)
  done
  done
next
  case (Cons a ls2)
  show ?case
  apply(subst flatten_it_adjust.simps)
  apply (sep_auto eintros del: exI heap add: inner_list.it_has_next_rule)
  apply(inst_existentials "(ls1 @ lsim # a # ls2)" ls2' ls1' ls1 "a #ls2" lsim lsm2 "lsm1@lsm2")
  subgoal by auto
  subgoal by (sep_auto)
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  subgoal by simp
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (case_tac ls2')
  apply simp_all
  apply (sep_auto eintros del: exI heap add: inner_list.it_init_rule)
  subgoal for x oit aa list xa
    supply R = "Cons.IH"[of "ls1'@[lsm1]" "ls1@[lsim]" list a oit "[]::'a list" aa xa, simplified]
    thm R
  find_theorems "_ \<Longrightarrow>\<^sub>A _" "<_>_<_>"
  supply Q = Hoare_Triple.cons_pre_rule[of 
"inner_is_it aa a aa xa * outer_is_it (ls1 @ lsim # a # ls2) lsi ls2 oit *
     inner_is_it lsm1 lsim [] iit *
     list_assn is_inner_list ls1' ls1 *
     list_assn is_inner_list list ls2 *
     true"
"list_assn is_inner_list ls1' ls1 * is_inner_list lsm1 lsim * list_assn is_inner_list list ls2 *
 outer_is_it (ls1 @ lsim # a # ls2) lsi ls2 oit *
 inner_is_it aa a aa
  xa * true"
]
  thm Q
  apply(rule Q)
  prefer 2
  subgoal by (sep_auto heap add: R intro: inner_list.quit_iteration)
  subgoal using inner_list.quit_iteration
    by (smt (z3) assn_aci(10) assn_times_comm ent_refl_true ent_star_mono_true)
  done
  done
qed

definition flatten_it_init :: "'m \<Rightarrow> _ Heap" 
  where "flatten_it_init l = do {
    oit \<leftarrow> outer_it_init l;
    ohasnext \<leftarrow> outer_it_has_next oit;
    if ohasnext then do {
       (next, oit) \<leftarrow> outer_it_next oit;
       nextit \<leftarrow> inner_it_init next;
       flatten_it_adjust oit nextit
    } else return (oit, None)
}"

lemma flatten_it_init_rule[sep_heap_rules]: 
    "<is_flatten_list l p> flatten_it_init p <is_flatten_it l p l>\<^sub>t"
  unfolding flatten_it_init_def
  apply simp
  apply(rule norm_pre_ex_rule)+
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  subgoal for lsi' ls' x xa
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply(case_tac lsi'; case_tac ls')
  apply simp+
  apply(rule impI)
  thm inner_list.it_init_rule
  apply (vcg heap add: inner_list.it_init_rule)
  subgoal for _ nxt oit a list aa lista xaa
  supply R = flatten_it_adjust_rule[of "[]" "[]" lista list a p oit "[]" aa xaa, simplified]
  thm R
  apply (sep_auto heap add: R)
  done
  done
  apply (sep_auto eintros del: exI)
  apply(inst_existentials "[]::'l list" "[]::'a list list" "[]::'a list list" "[]::'l list" "[]::'l list")
  apply simp_all
  done

definition flatten_it_next where 
  "flatten_it_next \<equiv> \<lambda>(oit,iit). do {
    (x, iit) \<leftarrow> inner_it_next (the iit);
    (oit, iit) \<leftarrow> flatten_it_adjust oit iit;
    return (x, (oit,iit))
  }"

lemma flatten_it_next_rule:
    " l' \<noteq> [] \<Longrightarrow>
    <is_flatten_it l p l' it> 
      flatten_it_next it 
    <\<lambda>(a,it'). is_flatten_it l p (tl l') it' * \<up>(a=hd l')>\<^sub>t"
  apply(subst flatten_it_next_def)
  thm inner_list.it_next_rule
  apply (vcg (ss))
  apply (vcg (ss))
  apply(case_tac iit; case_tac l')
  apply simp_all
  apply(rule norm_pre_ex_rule)+
  subgoal for oit iit a aa list lsi' ls2' ls1' lsi1 lsi2 lsim ls2m lsm ls1m
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(vcg (ss))
    apply(case_tac ls2m)
    apply simp_all
    subgoal for _ _ iita lista
  supply R = flatten_it_adjust_rule[of ls1' lsi1 ls2' lsi2 lsim p oit "ls1m@[aa]" "lista" iita, simplified]
  thm R
  apply (sep_auto heap add: R)
  done
  done
  done

definition flatten_it_has_next where
  "flatten_it_has_next \<equiv> \<lambda>(oit, iit). do {
    return (iit \<noteq> None)
}"

lemma flatten_it_has_next_rule[sep_heap_rules]: 
    "<is_flatten_it l p l' it> 
       flatten_it_has_next it 
     <\<lambda>r. is_flatten_it l p l' it * \<up>(r\<longleftrightarrow>l'\<noteq>[])>\<^sub>t"
  apply(subst flatten_it_has_next_def)
  apply(sep_auto)
  apply(case_tac iit, case_tac l')
  apply simp_all
  apply sep_auto
  done

declare mult.left_assoc[simp add]
lemma flatten_quit_iteration:
    "is_flatten_it l p l' it \<Longrightarrow>\<^sub>A is_flatten_list l p * true"
  apply(cases it)
  subgoal for oit iit
    apply(cases iit; cases l') 
  proof (goal_cases)
    case 1
    then show ?case
      apply (sep_auto eintros del: exI)
      subgoal for lsi' lsi''
        apply(inst_existentials lsi' lsi'')
        subgoal by auto
        subgoal by (metis (no_types, lifting) assn_aci(10) assn_times_comm fr_refl outer_list.quit_iteration)
        done
      done
  next
    case (2 lsim ll')
    then show ?case
      by (sep_auto eintros del: exI)
  next
    case (3 iit)
    then show ?case
      by (sep_auto eintros del: exI)
  next
  case (4 iit lsim ll')
    then show ?case
      apply (sep_auto eintros del: exI)
      subgoal for lsi' ls2' ls1' lsi1 lsi2 lsima ls2m lsm ls1m
        apply(inst_existentials "(lsi1 @ lsima # lsi2)" "ls1'@(ls1m@ls2m)#ls2'")
        subgoal by auto
            subgoal
              apply(rule impI; rule entails_preI)
              apply (auto dest!: mod_starD list_assn_len)
              apply(simp add:
                  mult.commute[where ?b="outer_is_it (lsi1 @ lsima # lsi2) p lsi2 oit"]
                  mult.commute[where ?b="is_outer_list (lsi1 @ lsima # lsi2) p"]
                  mult.left_assoc)
              apply(rule rem_true)
              supply R = ent_star_mono_true[of
                  "outer_is_it (lsi1 @ lsima # lsi2) p lsi2 oit"
                  "is_outer_list (lsi1 @ lsima # lsi2) p"
                  "list_assn is_inner_list ls1' lsi1 *
                         list_assn is_inner_list ls2' lsi2 *
                         inner_is_it (ls1m @ ls2m) lsima ls2m iit"
                  " list_assn is_inner_list ls1' lsi1 *
                         is_inner_list (ls1m @ ls2m) lsima *
                         list_assn is_inner_list ls2' lsi2"
              ,simplified]
              thm R
              apply(rule R)
              subgoal by (rule outer_list.quit_iteration)
              apply(simp add:
                  mult.commute[where ?b="inner_is_it (ls1m @ ls2m) lsima ls2m iit"]
                  mult.commute[where ?b="is_inner_list (ls1m @ ls2m) lsima"]
                  mult.left_assoc)
              apply(rule rem_true)
              supply R = ent_star_mono_true[of
                  "inner_is_it (ls1m @ ls2m) lsima ls2m iit"
                  "is_inner_list (ls1m @ ls2m) lsima"
                  "list_assn is_inner_list ls1' lsi1 *
                         list_assn is_inner_list ls2' lsi2"
                  " list_assn is_inner_list ls1' lsi1 *
                         list_assn is_inner_list ls2' lsi2"
              ,simplified]
              thm R
              apply(rule R)
              subgoal by (rule inner_list.quit_iteration)
              subgoal by sep_auto
              done
            done
          done
      qed
  done
declare mult.left_assoc[simp del]

interpretation flatten_it: imp_list_iterate is_flatten_list is_flatten_it flatten_it_init flatten_it_has_next flatten_it_next
  apply(unfold_locales)
  subgoal 
    by (rule flatten_prec)
  subgoal for l p
    by (rule flatten_it_init_rule[of l p])
  subgoal for  l' l p it
    thm flatten_it_next_rule
    by (rule flatten_it_next_rule[of l' l p it])
  subgoal for l p l' it
    by (rule flatten_it_has_next_rule[of l p l' it])
  subgoal for l p l' it
    by (rule flatten_quit_iteration[of l p l' it])
  done
end

end