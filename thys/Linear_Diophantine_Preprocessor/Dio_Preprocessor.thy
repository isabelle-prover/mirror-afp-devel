section \<open>A Combined Preprocessor\<close>

text \<open>We combine equality detection, equality elimination and tightening
  in one function that eliminates all explicit and implicit equations
  from a list of inequalities and equalities, to either detect unsat or
  to return an equivalent list of inequalities which all can be satisfied
  strictly in the rational numbers.\<close>

theory Dio_Preprocessor
  imports 
    Linear_Polynomial_Impl
    Linear_Diophantine_Solver_Impl
    Diophantine_Tightening
    Linear_Diophantine_Eq_Finder
begin

text \<open>Combine equality elimination and tightening in one algorithm\<close>
definition dio_elim_equations_and_tighten :: "var dleq list \<Rightarrow> var dlineq list \<Rightarrow> 
    (var dlineq list \<times> ((int,var)assign \<Rightarrow> (int,var)assign)) option" where
  "dio_elim_equations_and_tighten eqs ineqs = (case equality_elim_for_inequalities fresh_vars_nat eqs ineqs
     of None \<Rightarrow> None
     | Some (ineqs2, adj) \<Rightarrow> map_option (\<lambda> ineqs3. (ineqs3, adj)) (tighten_ineqs ineqs2))" 

lemma dio_elim_equations_and_tighten: assumes 
  res: "dio_elim_equations_and_tighten eqs ineqs = res"
  shows "res = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)" 
  "res = Some (ineqs', adj) \<Longrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> \<beta> = adj \<alpha> \<Longrightarrow> \<beta> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)" 
  "res = Some (ineqs' , adj) \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> \<nexists> \<alpha> . \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)"
  "res = Some (ineqs', adj) \<Longrightarrow> length ineqs' \<le> length ineqs" 
proof (atomize(full), goal_cases)
  case 1
  note res = res[unfolded dio_elim_equations_and_tighten_def]
  show ?case
  proof (cases "equality_elim_for_inequalities fresh_vars_nat eqs ineqs")
    case None
    from equality_elim_for_inequalities_nat(1)[OF None refl] None show ?thesis using res by auto
  next
    case (Some pair)
    obtain ineqs2 adj' where pair: "pair = (ineqs2, adj')" by force
    note Some = Some[unfolded pair]
    note res = res[unfolded Some option.simps split]
    note eq_elim = equality_elim_for_inequalities_nat(2-)[OF Some refl]
    show ?thesis
    proof (cases "tighten_ineqs ineqs2")
      case None
      with res eq_elim tighten_ineqs(1)[OF None] show ?thesis by auto
    next
      case (Some ineqs3)
      with res eq_elim tighten_ineqs(2)[OF Some] show ?thesis by force
    qed
  qed
qed

text \<open>Now all three preprocessing steps are combined.

  Since after an equality elimination the resulting inequalities might
  be tightened, it can happen that after the tightening new equalities are implied;
  therefore the whole process is performed recursively\<close>
function dio_preprocess_main :: "(int, var) lpoly list \<Rightarrow> ((int, var) lpoly list \<times> ((int,var)assign \<Rightarrow> (int,var)assign)) option" where
  "dio_preprocess_main ineqs = (case eq_finder_int ineqs of None \<Rightarrow> None
     | Some (eqs, ineqs') \<Rightarrow> (case eqs of [] \<Rightarrow> Some (ineqs', id)
      | _ \<Rightarrow> (case dio_elim_equations_and_tighten eqs ineqs' of None \<Rightarrow> None
      | Some (ineqs'', adj) \<Rightarrow> map_option (map_prod id (\<lambda> adj'. adj o adj')) (dio_preprocess_main ineqs''))))" 
  by pat_completeness auto

termination
proof (standard, rule wf_measure[of length], goal_cases)
  case (1 ineqs pair eqs ineqs' e eqs' pair' ineqs'' adj)
  from eq_finder_int(4)[OF 1(1), folded 1(2), OF refl]
    dio_elim_equations_and_tighten(4)[OF 1(4), folded 1(5), OF refl]
    1(3)
  show ?case by auto
qed

declare dio_preprocess_main.simps[simp del]

lemma dio_preprocess_main: assumes 
  res: "dio_preprocess_main ineqs = res"
  shows "res = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs)" 
  "res = Some (ineqs', adj) \<Longrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> (adj \<alpha>) \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs)" 
  "res = Some (ineqs' , adj) \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs)"
  "res = Some (ineqs', adj) \<Longrightarrow> \<exists> \<alpha>. \<alpha> \<Turnstile>\<^sub>c\<^sub>s (make_strict ` dlineq_to_constraint ` set ineqs')" 
proof (atomize(full), goal_cases)
  case 1
  show ?case using res
  proof (induction ineqs arbitrary: res ineqs' adj \<alpha> rule: dio_preprocess_main.induct)
    case (1 ineqs res ineqs' adj \<alpha>)
    note res = dio_preprocess_main.simps[of ineqs, unfolded "1.prems"]
    show ?case
    proof (cases "eq_finder_int ineqs")
      case None
      from res[unfolded None option.simps] eq_finder_int(1)[OF None] show ?thesis by auto
    next
      case (Some pair)
      obtain eqs1 ineqs1 where pair: "pair = (eqs1, ineqs1)" by force
      note Some = Some[unfolded pair]
      note res = res[unfolded Some option.simps split]
      note eqf = eq_finder_int(2,3)[OF Some refl]
      note IH = "1.IH"[OF Some refl]
      show ?thesis
      proof (cases eqs1)
        case Nil
        with res have "res = Some (ineqs1, id)" by auto
        with res eqf Nil show ?thesis by auto
      next
        case (Cons e eqs1')
        note res = res[unfolded Cons list.simps, folded Cons]
        note IH = IH[OF Cons]
        show ?thesis
        proof (cases "dio_elim_equations_and_tighten eqs1 ineqs1")
          case None
          note res = res[unfolded None option.simps]
          from dio_elim_equations_and_tighten(1)[OF None] res show ?thesis using eqf by auto
        next
          case (Some pair2)
          obtain ineqs2 adj2 where pair2: "pair2 = (ineqs2, adj2)" by force
          note Some = Some[unfolded this]
          note res = res[unfolded Some option.simps split]
          note IH = IH[OF Some refl refl]
          note elim = dio_elim_equations_and_tighten(2-3)[OF Some refl]
          note elim = elim(1)[OF _ refl] elim(2)
          show ?thesis 
          proof (cases "dio_preprocess_main ineqs2")
            case None
            with IH have "\<nexists>\<alpha>. \<forall>a\<in>set ineqs2. satisfies_dlineq \<alpha> a" by auto
            with elim res None eqf show ?thesis by auto
          next
            case (Some pair3)
            obtain ineqs3 adj3 where pair3: "pair3 = (ineqs3, adj3)" by force
            note Some = Some[unfolded this]
            from res[unfolded Some]
            have res: "res = Some (ineqs3, adj2 o adj3)" by auto
            from IH[of ineqs3 adj3] Some res IH elim eqf show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
qed

text \<open>The final preprocessing function just does some initial round of equality
  elimination and tightening before invoking the main algorithm which tries to
  detect and eliminate further implicit equalities.\<close>
definition dio_preprocess :: "var dleq list \<Rightarrow> var dlineq list \<Rightarrow> (var dlineq list \<times> ((int,var)assign \<Rightarrow> (int,var)assign)) option" where
  "dio_preprocess eqs ineqs = (case dio_elim_equations_and_tighten eqs ineqs of None \<Rightarrow> None
      | Some (ineqs', adj) \<Rightarrow> map_option (map_prod id (\<lambda> adj'. adj o adj')) (dio_preprocess_main ineqs'))" 

text \<open>The @{const dio_preprocess} algorithm eliminates all explicit and implicit equalities;
  in the negative outcome (None) we see
  (1) that the input constraints are unsat;
  and in the positive case (Some)
  (2) the resulting inequalities are equisatisfiable to the input constraints, 
  (3) the solutions can be transformed in one direction via an adjuster adj, and
  (4) all resulting inequalities can be satisfied strictly using rational numbers, 
      so no further equalities can be deduced using rational arithmetic reasoning.\<close>
lemma dio_preprocess: assumes res: "dio_preprocess eqs ineqs = res"
  shows "res = None \<Longrightarrow> \<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)" 
  "res = Some (ineqs', adj) \<Longrightarrow> (\<exists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs')) \<longleftrightarrow> (\<exists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs))"
  "res = Some (ineqs', adj) \<Longrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ineqs') \<Longrightarrow> (adj \<alpha>) \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (set eqs, set ineqs)" 
  "res = Some (ineqs', adj) \<Longrightarrow> \<exists> \<alpha>. \<alpha> \<Turnstile>\<^sub>c\<^sub>s (make_strict ` dlineq_to_constraint ` set ineqs')" 
proof (atomize(full), goal_cases)
  case 1
  note res = res[unfolded dio_preprocess_def]
  show ?case
  proof (cases "dio_elim_equations_and_tighten eqs ineqs")
    case None
    with dio_elim_equations_and_tighten(1)[OF None] res show ?thesis by auto
  next
    case (Some pair)
    obtain ineqs1 adj1 where "pair = (ineqs1, adj1)" by force
    note Some = Some[unfolded this]
    note res = res[unfolded Some option.simps split]
    note elim = dio_elim_equations_and_tighten(2-3)[OF Some refl]
    note elim = elim(1)[OF _ refl] elim(2)
    show ?thesis  
    proof (cases "dio_preprocess_main ineqs1")
      case None
      with dio_preprocess_main(1)[OF None] res elim show ?thesis by auto
    next
      case (Some pair2)
      obtain ineqs2 adj2 where "pair2 = (ineqs2, adj2)" by force
      note Some = Some[unfolded this]
      from res[unfolded Some]
      have res: "res = Some (ineqs2, adj1 \<circ> adj2)" by auto
      from dio_preprocess_main(2-4)[OF Some refl] elim res
      show ?thesis by fastforce
    qed
  qed
qed

end