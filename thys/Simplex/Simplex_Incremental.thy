(* Author: R. Thiemann *)
section \<open>The Incremental Simplex Algorithm\<close>

text \<open>In this theory we specify operations which permit to incrementally
  add constraints. To this end, first an indexed list of potential constraints is used
  to construct the initial state, and then one can activate indices, extract solutions or unsat cores,
  do backtracking, etc.\<close>

theory Simplex_Incremental
  imports Simplex
begin

subsection \<open>Lowest Layer: Fixed Tableau and Incremental Atoms\<close>

text \<open>Interface\<close>

locale Incremental_Atom_Ops = fixes 
  init_s :: "tableau \<Rightarrow> 's" and
  assert_s :: "('i,'a :: lrv) i_atom \<Rightarrow> 's \<Rightarrow> 'i list + 's" and
  check_s :: "'s \<Rightarrow> 's \<times> ('i list option)" and
  solution_s :: "'s \<Rightarrow> (var, 'a) mapping" and
  checkpoint_s :: "'s \<Rightarrow> 'c" and
  backtrack_s :: "'c \<Rightarrow> 's \<Rightarrow> 's" and
  precond_s :: "tableau \<Rightarrow> bool" and
  weak_invariant_s :: "tableau \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> 's \<Rightarrow> bool" and
  invariant_s :: "tableau \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> 's \<Rightarrow> bool" and
  checked_s :: "tableau \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> 's \<Rightarrow> bool"
assumes 
  assert_s_ok: "invariant_s t as s \<Longrightarrow> assert_s a s = Inr s' \<Longrightarrow> 
    invariant_s t (insert a as) s'" and
  assert_s_unsat: "invariant_s t as s \<Longrightarrow> assert_s a s = Unsat I \<Longrightarrow>
    minimal_unsat_core_tabl_atoms (set I) t (insert a as)" and
  check_s_ok: "invariant_s t as s \<Longrightarrow> check_s s = (s', None) \<Longrightarrow> 
    checked_s t as s'" and
  check_s_unsat: "invariant_s t as s \<Longrightarrow> check_s s = (s',Some I) \<Longrightarrow>
    weak_invariant_s t as s' \<and> minimal_unsat_core_tabl_atoms (set I) t as" and
  init_s: "precond_s t \<Longrightarrow> checked_s t {} (init_s t)" and
  solution_s: "checked_s t as s \<Longrightarrow> solution_s s = v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<and> \<langle>v\<rangle> \<Turnstile>\<^sub>a\<^sub>s Simplex.flat as" and
  backtrack_s: "checked_s t as s \<Longrightarrow> checkpoint_s s = c 
    \<Longrightarrow> weak_invariant_s t bs s' \<Longrightarrow> backtrack_s c s' = s'' \<Longrightarrow> as \<subseteq> bs \<Longrightarrow> invariant_s t as s''" and
  weak_invariant_s: "invariant_s t as s \<Longrightarrow> weak_invariant_s t as s" and
  checked_invariant_s: "checked_s t as s \<Longrightarrow> invariant_s t as s" 
begin

fun assert_all_s :: "('i,'a) i_atom list \<Rightarrow> 's \<Rightarrow> 'i list + 's" where
  "assert_all_s [] s = Inr s" 
| "assert_all_s (a # as) s = (case assert_s a s of Unsat I \<Rightarrow> Unsat I 
     | Inr s' \<Rightarrow> assert_all_s as s')" 

lemma assert_all_s_ok: "invariant_s t as s \<Longrightarrow> assert_all_s bs s = Inr s' \<Longrightarrow> 
    invariant_s t (set bs \<union> as) s'"
proof (induct bs arbitrary: s as)
  case (Cons b bs s as)
  from Cons(3) obtain s'' where ass: "assert_s b s = Inr s''" and rec: "assert_all_s bs s'' = Inr s'" 
    by (auto split: sum.splits)
  from Cons(1)[OF assert_s_ok[OF Cons(2) ass] rec]
  show ?case by auto
qed auto

lemma assert_all_s_unsat: "invariant_s t as s \<Longrightarrow> assert_all_s bs s = Unsat I \<Longrightarrow> 
   minimal_unsat_core_tabl_atoms (set I) t (as \<union> set bs)" 
proof (induct bs arbitrary: s as)
  case (Cons b bs s as)
  show ?case
  proof (cases "assert_s b s")
    case unsat: (Inl J)
    with Cons have J: "J = I" by auto
    from assert_s_unsat[OF Cons(2) unsat] J
    have min: "minimal_unsat_core_tabl_atoms (set I) t (insert b as)" by auto    
    show ?thesis 
      by (rule minimal_unsat_core_tabl_atoms_mono[OF _ min], auto)
  next
    case (Inr s')
    from Cons(1)[OF assert_s_ok[OF Cons(2) Inr]] Cons(3) Inr show ?thesis by auto
  qed
qed simp

end


text \<open>Implementation of the interface via the Simplex operations init, check, and assert-bound.\<close>

locale Incremental_State_Ops_Simplex = AssertBoundNoLhs assert_bound + Init init + Check check
  for assert_bound :: "('i,'a::lrv) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" and
    init :: "tableau \<Rightarrow> ('i,'a) state" and
    check :: "('i,'a) state \<Rightarrow> ('i,'a) state"
begin

definition weak_invariant_s where 
  "weak_invariant_s t (as :: ('i,'a)i_atom set) s = 
    (\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<and> 
     \<triangle> (\<T> s) \<and> 
     \<nabla> s \<and> 
     \<diamond> s \<and> 
     (\<forall> v :: (var \<Rightarrow> 'a). v \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t t) \<and>
     index_valid as s \<and>
     Simplex.flat as \<doteq> \<B> s \<and> 
     as \<Turnstile>\<^sub>i \<B>\<I> s)" 


definition invariant_s where 
  "invariant_s t (as :: ('i,'a)i_atom set) s = 
     (weak_invariant_s t as s \<and> \<not> \<U> s)" 

definition checked_s where 
  "checked_s t as s = (invariant_s t as s \<and> \<Turnstile> s)"  

definition assert_s where "assert_s a s = (let s' = assert_bound a s in
  if \<U> s' then Inl (the (\<U>\<^sub>c s')) else Inr s')"

definition check_s where "check_s s = (let s' = check s in 
  if \<U> s' then (s', Some (the (\<U>\<^sub>c s'))) else (s', None))" 

definition checkpoint_s where "checkpoint_s s = \<B>\<^sub>i s" 

fun backtrack_s :: "_ \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state" 
  where "backtrack_s (bl, bu) (State t bl_old bu_old v u uc) = State t bl bu v False None"

lemmas invariant_defs = weak_invariant_s_def invariant_s_def checked_s_def

lemma invariant_sD: assumes "invariant_s t as s" 
  shows "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"  
    "Simplex.flat as \<doteq> \<B> s" "as \<Turnstile>\<^sub>i \<B>\<I> s" "index_valid as s"
    "(\<forall> v :: (var \<Rightarrow> 'a). v \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t t)" 
  using assms unfolding invariant_defs by auto

lemma weak_invariant_sD: assumes "weak_invariant_s t as s" 
  shows "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"  
    "Simplex.flat as \<doteq> \<B> s" "as \<Turnstile>\<^sub>i \<B>\<I> s" "index_valid as s"
    "(\<forall> v :: (var \<Rightarrow> 'a). v \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t t)" 
  using assms unfolding invariant_defs by auto

lemma minimal_unsat_state_core_translation: assumes 
  unsat: "minimal_unsat_state_core (s :: ('i,'a::lrv)state)" and
  tabl: "\<forall>(v :: 'a valuation). v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t t" and
  index: "index_valid as s" and
  imp: "as \<Turnstile>\<^sub>i \<B>\<I> s" and
  I: "I = the (\<U>\<^sub>c s)" 
shows "minimal_unsat_core_tabl_atoms (set I) t as" 
  unfolding minimal_unsat_core_tabl_atoms_def
proof (intro conjI impI notI allI; (elim exE conjE)?)
  from unsat[unfolded minimal_unsat_state_core_def]
  have unsat: "unsat_state_core s" 
    and minimal: "distinct_indices_state s \<Longrightarrow> subsets_sat_core s" 
    by auto
  from unsat[unfolded unsat_state_core_def I[symmetric]]
  have Is: "set I \<subseteq> indices_state s" and unsat: "(\<nexists>v. (set I, v) \<Turnstile>\<^sub>i\<^sub>s s)" by auto
  from Is index show "set I \<subseteq> fst ` as"
    using index_valid_indices_state by blast
  {
    fix v
    assume t: "v \<Turnstile>\<^sub>t t" and as: "(set I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as" 
    from t tabl have t: "v \<Turnstile>\<^sub>t \<T> s" by auto
    then have "(set I, v) \<Turnstile>\<^sub>i\<^sub>s s" using as imp 
      using atoms_imply_bounds_index.simps satisfies_state_index.simps by blast
    with unsat show False by blast
  }
  {
    fix J
    assume dist: "distinct_indices_atoms as" 
      and J: "J \<subset> set I" 
    from J Is have J': "J \<subseteq> indices_state s" by auto
    from dist index have "distinct_indices_state s" by (metis index_valid_distinct_indices)
    with minimal have "subsets_sat_core s" .
    from this[unfolded subsets_sat_core_def I[symmetric], rule_format, OF J]
    obtain v where "(J, v) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s" by blast
    from satisfying_state_valuation_to_atom_tabl[OF J' this index dist] tabl
    show "\<exists>v. v \<Turnstile>\<^sub>t t \<and> (J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s as" by blast
  }
qed

sublocale Incremental_Atom_Ops 
  init assert_s check_s \<V> checkpoint_s backtrack_s \<triangle> weak_invariant_s invariant_s checked_s
proof (unfold_locales, goal_cases)
  case (1 t as s a s') (* assert ok *)
  from 1(2)[unfolded assert_s_def Let_def]
  have U: "\<not> \<U> (assert_bound a s)" and s': "s' = assert_bound a s" by (auto split: if_splits)
  note * = invariant_sD[OF 1(1)]
  from assert_bound_nolhs_tableau_id[OF *(1-5)]
  have T: "\<T> s' = \<T> s" unfolding s' by auto
  from *(3,9)
  have "\<triangle> (\<T> s')" "\<forall> v :: var \<Rightarrow> 'a. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t t" unfolding T by blast+
  moreover from assert_bound_nolhs_sat[OF *(1-5) U] 
  have " \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'" "\<diamond> s'" unfolding s' by auto
  moreover from assert_bound_nolhs_atoms_equiv_bounds[OF *(1-6), of a]
  have "Simplex.flat (insert a as) \<doteq> \<B> s'" unfolding s' by auto
  moreover from assert_bound_nolhs_atoms_imply_bounds_index[OF *(1-5,7)]
  have "insert a as \<Turnstile>\<^sub>i \<B>\<I> s'" unfolding s' .
  moreover from assert_bound_nolhs_tableau_valuated[OF *(1-5)]
  have "\<nabla> s'" unfolding s' .
  moreover from assert_bound_nolhs_index_valid[OF *(1-5,8)]
  have "index_valid (insert a as) s'" unfolding s' by auto
  moreover from U s' 
  have "\<not> \<U> s'" by auto
  ultimately show ?case unfolding invariant_defs by auto
next
  case (2 t as s a I) (* assert unsat *)
  from 2(2)[unfolded assert_s_def Let_def]
  obtain s' where s': "s' = assert_bound a s" and U: "\<U> (assert_bound a s)" 
    and I: "I = the (\<U>\<^sub>c s')"
    by (auto split: if_splits)
  note * = invariant_sD[OF 2(1)]
  from assert_bound_nolhs_tableau_id[OF *(1-5)]
  have T: "\<T> s' = \<T> s" unfolding s' by auto
  from *(3,9)
  have tabl: "\<forall> v :: var \<Rightarrow> 'a. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t t" unfolding T by blast+
  from assert_bound_nolhs_unsat[OF *(1-5,8) U] s'
  have unsat: "minimal_unsat_state_core s'" by auto
  from assert_bound_nolhs_index_valid[OF *(1-5,8)]
  have index: "index_valid (insert a as) s'" unfolding s' by auto
  from assert_bound_nolhs_atoms_imply_bounds_index[OF *(1-5,7)]
  have imp: "insert a as \<Turnstile>\<^sub>i \<B>\<I> s'" unfolding s' .
  from minimal_unsat_state_core_translation[OF unsat tabl index imp I]
  show ?case .
next
  case (3 t as s s') (* check ok *)
  from 3(2)[unfolded check_s_def Let_def]
  have U: "\<not> \<U> (check s)" and s': "s' = check s" by (auto split: if_splits)
  note * = invariant_sD[OF 3(1)]
  note ** = *(1,2,5,3,4)
  from check_tableau_equiv[OF **] *(9)
  have "\<forall>v :: _ \<Rightarrow> 'a. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t t" unfolding s' by auto
  moreover from check_tableau_index_valid[OF **] *(8)
  have "index_valid as s'" unfolding s' by auto
  moreover from check_tableau_normalized[OF **]
  have "\<triangle> (\<T> s')" unfolding s' .
  moreover from check_tableau_valuated[OF **]
  have "\<nabla> s'" unfolding s' .
  moreover from check_sat[OF ** U]
  have "\<Turnstile> s'" unfolding s'. 
  moreover from satisfies_satisfies_no_lhs[OF this] satisfies_consistent[of s'] this
  have " \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'" "\<diamond> s'" by blast+
  moreover from check_bounds_id[OF **] *(6)
  have "Simplex.flat as \<doteq> \<B> s'" unfolding s' by (auto simp: boundsu_def boundsl_def)
  moreover from check_bounds_id[OF **] *(7)
  have "as \<Turnstile>\<^sub>i \<B>\<I> s'" unfolding s' by (auto simp: boundsu_def boundsl_def indexu_def indexl_def)
  moreover from U 
  have "\<not> \<U> s'" unfolding s' .
  ultimately show ?case unfolding invariant_defs by auto
next
  case (4 t as s s' I) (* check Unsat *)
  from 4(2)[unfolded check_s_def Let_def]
  have s': "s' = check s" and U: "\<U> (check s)" 
    and I: "I = the (\<U>\<^sub>c s')"
    by (auto split: if_splits)
  note * = invariant_sD[OF 4(1)]
  note ** = *(1,2,5,3,4)
  from check_unsat[OF ** U]
  have unsat: "minimal_unsat_state_core s'" unfolding s' by auto
  from check_tableau_equiv[OF **] *(9)
  have tabl: "\<forall>v :: _ \<Rightarrow> 'a. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t t" unfolding s' by auto
  from check_tableau_index_valid[OF **] *(8)
  have index: "index_valid as s'" unfolding s' by auto
  from check_bounds_id[OF **] *(7)
  have imp: "as \<Turnstile>\<^sub>i \<B>\<I> s'" unfolding s' by (auto simp: boundsu_def boundsl_def indexu_def indexl_def)
  from check_bounds_id[OF **] *(6)
  have bequiv: "Simplex.flat as \<doteq> \<B> s'" unfolding s' by (auto simp: boundsu_def boundsl_def)
  have "weak_invariant_s t as s'" unfolding invariant_defs 
    using 
      check_tableau_normalized[OF **] 
      check_tableau_valuated[OF **]
      check_tableau[OF **]
    unfolding s'[symmetric]
    by (intro conjI index imp tabl bequiv, auto)
  with minimal_unsat_state_core_translation[OF unsat tabl index imp I]
  show ?case by auto
next
  case *: (5 t) (* init *)
  show ?case unfolding invariant_defs
    using 
      init_tableau_normalized[OF *] 
      init_index_valid[of _ t]
      init_atoms_imply_bounds_index[of t]
      init_satisfies[of t]
      init_atoms_equiv_bounds[of t]
      init_tableau_id[of t]
      init_unsat_flag[of t]
      init_tableau_valuated[of t]
      satisfies_consistent[of "init t"] satisfies_satisfies_no_lhs[of "init t"]
    by auto
next
  case (6 t as s v) (* solution *)
  then show ?case unfolding invariant_defs
    by (meson atoms_equiv_bounds.simps curr_val_satisfies_state_def satisfies_state_def)
next
  case (7 t as s c bs s' s'') (* checkpoint and backtrack *)
  from 7(1)[unfolded checked_s_def]
  have inv_s: "invariant_s t as s" and s: "\<Turnstile> s" by auto
  from 7(2) have c: "c = \<B>\<^sub>i s" unfolding checkpoint_s_def by auto 
  have s'': "\<T> s'' = \<T> s'" "\<V> s'' = \<V> s'" "\<B>\<^sub>i s'' = \<B>\<^sub>i s" "\<U> s'' = False" "\<U>\<^sub>c s'' = None"
    unfolding 7(4)[symmetric] c
    by (atomize(full), cases s', auto)
  then have BI: "\<B> s'' = \<B> s" "\<I> s'' = \<I> s" by (auto simp: boundsu_def boundsl_def indexu_def indexl_def)  
  note * = invariant_sD[OF inv_s]
  note ** = weak_invariant_sD[OF 7(3)]
  have "\<not> \<U> s''" unfolding s'' by auto
  moreover from **(2) 
  have "\<triangle> (\<T> s'')" unfolding s'' .
  moreover from **(3)
  have "\<nabla> s''" unfolding tableau_valuated_def s'' .
  moreover from **(8)
  have "\<forall>v :: _ \<Rightarrow> 'a. v \<Turnstile>\<^sub>t \<T> s'' = v \<Turnstile>\<^sub>t t" unfolding s'' .
  moreover from *(6)
  have "Simplex.flat as \<doteq> \<B> s''" unfolding BI .
  moreover from *(7)
  have "as \<Turnstile>\<^sub>i \<B>\<I> s''" unfolding BI .
  moreover from *(8)
  have "index_valid as s''" unfolding index_valid_def using s'' by auto
  moreover from **(3)
  have "\<nabla> s''" unfolding tableau_valuated_def s'' .
  moreover from satisfies_consistent[of s] s
  have "\<diamond> s''" unfolding bounds_consistent_def using BI by auto
  moreover
  from 7(5) *(6) **(5)
  have vB: "v \<Turnstile>\<^sub>b \<B> s' \<Longrightarrow> v \<Turnstile>\<^sub>b \<B> s''" for v 
    unfolding atoms_equiv_bounds.simps satisfies_atom_set_def BI
    by force
  from **(1) 
  have t: "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'" and b: "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>b \<B> s' \<parallel> - lvars (\<T> s')" 
    unfolding curr_val_satisfies_no_lhs_def by auto
  let ?v = "\<lambda> x. if x \<in> lvars (\<T> s') then case \<B>\<^sub>l s' x of None \<Rightarrow> the (\<B>\<^sub>u s' x) | Some b \<Rightarrow> b else \<langle>\<V> s'\<rangle> x" 
  have "?v \<Turnstile>\<^sub>b \<B> s'" unfolding satisfies_bounds.simps
  proof (intro allI)
    fix x :: var
    show "in_bounds x ?v (\<B> s')"
    proof (cases "x \<in> lvars (\<T> s')")
      case True
      with **(4)[unfolded bounds_consistent_def, rule_format, of x]
      show ?thesis by (cases "\<B>\<^sub>l s' x"; cases "\<B>\<^sub>u s' x", auto simp: bound_compare_defs)
    next
      case False
      with b 
      show ?thesis unfolding satisfies_bounds_set.simps by auto
    qed
  qed
  from vB[OF this] have v: "?v \<Turnstile>\<^sub>b \<B> s''" .
  have "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>b \<B> s'' \<parallel> - lvars (\<T> s')" unfolding satisfies_bounds_set.simps
  proof clarify
    fix x
    assume "x \<notin> lvars (\<T> s')" 
    with v[unfolded satisfies_bounds.simps, rule_format, of x]
    show "in_bounds x \<langle>\<V> s'\<rangle> (\<B> s'')" by auto
  qed
  with t have "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s''" unfolding curr_val_satisfies_no_lhs_def s''
    by auto
  ultimately show ?case unfolding invariant_defs by blast
qed (auto simp: invariant_defs)

end

subsection \<open>Intermediate Layer: Incremental Non-Strict Constraints\<close>

text \<open>Interface\<close>

locale Incremental_NS_Constraint_Ops = fixes 
  init_nsc :: "('i,'a :: lrv) i_ns_constraint list \<Rightarrow> 's" and
  assert_nsc :: "'i \<Rightarrow> 's \<Rightarrow> 'i list + 's" and
  check_nsc :: "'s \<Rightarrow> 's \<times> ('i list option)" and
  solution_nsc :: "'s \<Rightarrow> (var, 'a) mapping" and
  checkpoint_nsc :: "'s \<Rightarrow> 'c" and
  backtrack_nsc :: "'c \<Rightarrow> 's \<Rightarrow> 's" and
  weak_invariant_nsc :: "('i,'a) i_ns_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool" and
  invariant_nsc :: "('i,'a) i_ns_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool" and
  checked_nsc :: "('i,'a) i_ns_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool"
assumes 
  assert_nsc_ok: "invariant_nsc nsc J s \<Longrightarrow> assert_nsc j s = Inr s' \<Longrightarrow> 
    invariant_nsc nsc (insert j J) s'" and
  assert_nsc_unsat: "invariant_nsc nsc J s \<Longrightarrow> assert_nsc j s = Unsat I \<Longrightarrow>
    set I \<subseteq> insert j J \<and> minimal_unsat_core_ns (set I) (set nsc)" and
  check_nsc_ok: "invariant_nsc nsc J s \<Longrightarrow> check_nsc s = (s', None) \<Longrightarrow> 
    checked_nsc nsc J s'" and
  check_nsc_unsat: "invariant_nsc nsc J s \<Longrightarrow> check_nsc s = (s',Some I) \<Longrightarrow> 
    set I \<subseteq> J \<and> weak_invariant_nsc nsc J s' \<and> minimal_unsat_core_ns (set I) (set nsc)" and
  init_nsc: "checked_nsc nsc {} (init_nsc nsc)" and
  solution_nsc: "checked_nsc nsc J s \<Longrightarrow> solution_nsc s = v \<Longrightarrow> (J, \<langle>v\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set nsc" and
  backtrack_nsc: "checked_nsc nsc J s \<Longrightarrow> checkpoint_nsc s = c 
    \<Longrightarrow> weak_invariant_nsc nsc K s' \<Longrightarrow> backtrack_nsc c s' = s'' \<Longrightarrow> J \<subseteq> K \<Longrightarrow> invariant_nsc nsc J s''" and
  weak_invariant_nsc: "invariant_nsc nsc J s \<Longrightarrow> weak_invariant_nsc nsc J s" and
  checked_invariant_nsc: "checked_nsc nsc J s \<Longrightarrow> invariant_nsc nsc J s" 

text \<open>Implementation via the Simplex operation preprocess and the incremental operations for atoms.\<close>

fun create_map :: "('i \<times> 'a)list \<Rightarrow> ('i, ('i \<times> 'a) list)mapping" where
  "create_map [] = Mapping.empty" 
| "create_map ((i,a) # xs) = (let m = create_map xs in
     case Mapping.lookup m i of 
       None \<Rightarrow> Mapping.update i [(i,a)] m 
     | Some ias \<Rightarrow> Mapping.update i ((i,a) # ias) m)" 

definition list_map_to_fun :: "('i, ('i \<times> 'a) list)mapping \<Rightarrow> 'i \<Rightarrow> ('i \<times> 'a) list" where
  "list_map_to_fun m i = (case Mapping.lookup m i of None \<Rightarrow> [] | Some ias \<Rightarrow> ias)" 

lemma list_map_to_fun_create_map: "set (list_map_to_fun (create_map ias) i) = set ias \<inter> {i} \<times> UNIV" 
proof (induct ias)
  case Nil
  show ?case unfolding list_map_to_fun_def by auto
next
  case (Cons ja ias)
  obtain j a where ja: "ja = (j,a)" by force
  show ?case
  proof (cases "j = i")
    case False
    then have id: "list_map_to_fun (create_map (ja # ias)) i = list_map_to_fun (create_map ias) i" 
      unfolding ja list_map_to_fun_def
      by (auto simp: Let_def split: option.splits)
    show ?thesis unfolding id Cons unfolding ja using False by auto
  next
    case True
    with ja have ja: "ja = (i,a)" by auto
    have id: "list_map_to_fun (create_map (ja # ias)) i = ja # list_map_to_fun (create_map ias) i" 
      unfolding ja list_map_to_fun_def
      by (auto simp: Let_def split: option.splits)
    show ?thesis unfolding id using Cons unfolding ja by auto
  qed
qed

fun prod_wrap :: "('c \<Rightarrow> 's \<Rightarrow> 's \<times> ('i list option))
  \<Rightarrow> 'c \<times> 's \<Rightarrow> ('c \<times> 's) \<times> ('i list option)" where
  "prod_wrap f (asi,s) = (case f asi s of (s', info) \<Rightarrow> ((asi,s'), info))" 

lemma prod_wrap_def': "prod_wrap f (asi,s) = map_prod (Pair asi) id (f asi s)" 
  unfolding prod_wrap.simps by (auto split: prod.splits)


locale Incremental_Atom_Ops_For_NS_Constraint_Ops =
  Incremental_Atom_Ops init_s assert_s check_s solution_s checkpoint_s backtrack_s \<triangle>
  weak_invariant_s invariant_s checked_s
  + Preprocess preprocess
  for 
    init_s :: "tableau \<Rightarrow> 's" and
    assert_s :: "('i :: linorder,'a :: lrv) i_atom \<Rightarrow> 's \<Rightarrow> 'i list + 's" and
    check_s :: "'s \<Rightarrow> 's \<times> 'i list option" and
    solution_s :: "'s \<Rightarrow> (var, 'a) mapping" and
    checkpoint_s :: "'s \<Rightarrow> 'c" and
    backtrack_s :: "'c \<Rightarrow> 's \<Rightarrow> 's" and
    weak_invariant_s :: "tableau \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> 's \<Rightarrow> bool" and
    invariant_s :: "tableau \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> 's \<Rightarrow> bool" and
    checked_s :: "tableau \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> 's \<Rightarrow> bool" and
    preprocess :: "('i,'a) i_ns_constraint list \<Rightarrow> tableau \<times> ('i,'a) i_atom list \<times> ((var,'a)mapping \<Rightarrow> (var,'a)mapping) \<times> 'i list" 
begin

definition check_nsc where "check_nsc = prod_wrap (\<lambda> asitv. check_s)" 

definition assert_nsc where "assert_nsc i = (\<lambda> ((asi,tv,ui),s). 
  if i \<in> set ui then Unsat [i] else 
  case assert_all_s (list_map_to_fun asi i) s of Unsat I \<Rightarrow> Unsat I | Inr s' \<Rightarrow> Inr ((asi,tv,ui),s'))"

fun checkpoint_nsc where "checkpoint_nsc (asi_tv_ui,s) = checkpoint_s s" 
fun backtrack_nsc where "backtrack_nsc c (asi_tv_ui,s) = (asi_tv_ui, backtrack_s c s)" 
fun solution_nsc where "solution_nsc ((asi,tv,ui),s) = tv (solution_s s)" 

definition "init_nsc nsc = (case preprocess nsc of (t,as,trans_v,ui) \<Rightarrow> 
   ((create_map as, trans_v, remdups ui), init_s t))"

fun invariant_as_asi where "invariant_as_asi as asi tc tc' ui ui' = (tc = tc' \<and> set ui = set ui' \<and> 
    (\<forall> i. set (list_map_to_fun asi i) = (as \<inter> ({i} \<times> UNIV))))" 

fun weak_invariant_nsc where 
  "weak_invariant_nsc nsc J ((asi,tv,ui),s) = (case preprocess nsc of (t,as,tv',ui') \<Rightarrow> invariant_as_asi (set as) asi tv tv' ui ui' \<and> 
     weak_invariant_s t (set as \<inter> (J \<times> UNIV)) s \<and> J \<inter> set ui = {})" 

fun invariant_nsc where 
  "invariant_nsc nsc J ((asi,tv,ui),s) = (case preprocess nsc of (t,as,tv',ui') \<Rightarrow> invariant_as_asi (set as) asi tv tv' ui ui' \<and> 
     invariant_s t (set as \<inter> (J \<times> UNIV)) s \<and> J \<inter> set ui = {})" 

fun checked_nsc where 
  "checked_nsc nsc J ((asi,tv,ui),s) = (case preprocess nsc of (t,as,tv',ui') \<Rightarrow> invariant_as_asi (set as) asi tv tv' ui ui' \<and> 
     checked_s t (set as \<inter> (J \<times> UNIV)) s \<and> J \<inter> set ui = {})" 

lemma i_satisfies_atom_set_inter_right: "((I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s (ats \<inter> (J \<times> UNIV))) \<longleftrightarrow> ((I \<inter> J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s ats)" 
  unfolding i_satisfies_atom_set.simps
  by (rule arg_cong[of _ _ "\<lambda> x. v \<Turnstile>\<^sub>a\<^sub>s x"], auto)


lemma ns_constraints_ops: "Incremental_NS_Constraint_Ops init_nsc assert_nsc
  check_nsc solution_nsc checkpoint_nsc backtrack_nsc
  weak_invariant_nsc invariant_nsc checked_nsc"
proof (unfold_locales, goal_cases)
  case (1 nsc J S j S') (* assert ok *)
  obtain asi tv s ui where S: "S = ((asi,tv,ui),s)" by (cases S, auto)
  obtain t as tv' ui' where prep[simp]: "preprocess nsc = (t, as, tv', ui')" by (cases "preprocess nsc")
  note pre = 1[unfolded S assert_nsc_def]
  from pre(2) obtain s' where
    ok: "assert_all_s (list_map_to_fun asi j) s = Inr s'" and S': "S' = ((asi,tv,ui),s')" and j: "j \<notin> set ui" 
    by (auto split: sum.splits if_splits)
  from pre(1)[simplified]
  have inv: "invariant_s t (set as \<inter> J \<times> UNIV) s" 
    and asi: "set (list_map_to_fun asi j) = set as \<inter> {j} \<times> UNIV" "invariant_as_asi (set as) asi tv tv' ui ui'" "J \<inter> set ui = {}" by auto
  from assert_all_s_ok[OF inv ok, unfolded asi] asi(2-) j
  show ?case unfolding invariant_nsc.simps S' prep split
    by (metis Int_insert_left Sigma_Un_distrib1 inf_sup_distrib1 insert_is_Un)
next
  case (2 nsc J S j I) (* assert unsat *)
  obtain asi s tv ui where S: "S = ((asi,tv,ui),s)" by (cases S, auto)
  obtain t as tv' ui' where prep[simp]: "preprocess nsc = (t, as, tv', ui')" by (cases "preprocess nsc")
  note pre = 2[unfolded S assert_nsc_def split]
  show ?case
  proof (cases "j \<in> set ui")
    case False
    with pre(2) have unsat: "assert_all_s (list_map_to_fun asi j) s = Unsat I"  
      by (auto split: sum.splits)
    from pre(1)
    have inv: "invariant_s t (set as \<inter> J \<times> UNIV) s" 
      and asi: "set (list_map_to_fun asi j) = set as \<inter> {j} \<times> UNIV" by auto
    from assert_all_s_unsat[OF inv unsat, unfolded asi]
    have "minimal_unsat_core_tabl_atoms (set I) t (set as \<inter> J \<times> UNIV \<union> set as \<inter> {j} \<times> UNIV)" .
    also have "set as \<inter> J \<times> UNIV \<union> set as \<inter> {j} \<times> UNIV = set as \<inter> insert j J \<times> UNIV" by blast
    finally have unsat: "minimal_unsat_core_tabl_atoms (set I) t (set as \<inter> insert j J \<times> UNIV)" .
    hence I: "set I \<subseteq> insert j J" unfolding minimal_unsat_core_tabl_atoms_def by force
    with False pre have empty: "set I \<inter> set ui' = {}" by auto
    have "minimal_unsat_core_tabl_atoms (set I) t (set as)"
      by (rule minimal_unsat_core_tabl_atoms_mono[OF _ unsat], auto)
    from preprocess_minimal_unsat_core[OF prep this empty]
    have "minimal_unsat_core_ns (set I) (set nsc)" .
    then show ?thesis using I by blast
  next
    case True
    with pre(2) have I: "I = [j]" by auto
    from pre(1)[unfolded invariant_nsc.simps prep split invariant_as_asi.simps]
    have "set ui = set ui'" by simp
    with True have j: "j \<in> set ui'" by auto
    from preprocess_unsat_index[OF prep j]
    show ?thesis unfolding I by auto
  qed
next
  case (3 nsc J S S') (* check ok *)
  then show ?case using check_s_ok unfolding check_nsc_def
    by (cases S, auto split: prod.splits, blast)
next
  case (4 nsc J S S' I) (* check unsat *)
  obtain asi s tv ui where S: "S = ((asi,tv,ui),s)" by (cases S, auto)
  obtain t as tv' ui' where prep[simp]: "preprocess nsc = (t, as, tv', ui')" by (cases "preprocess nsc")
  from 4(2)[unfolded S check_nsc_def, simplified] 
  obtain s' where unsat: "check_s s = (s', Some I)" and S': "S' = ((asi, tv, ui), s')" 
    by (cases "check_s s", auto)
  note pre = 4[unfolded S check_nsc_def unsat, simplified]
  from pre have
    inv: "invariant_s t (set as \<inter> J \<times> UNIV) s" 
    by auto
  from check_s_unsat[OF inv unsat]
  have weak: "weak_invariant_s t (set as \<inter> J \<times> UNIV) s'" 
    and unsat: "minimal_unsat_core_tabl_atoms (set I) t (set as \<inter> J \<times> UNIV)" by auto
  hence I: "set I \<subseteq> J" unfolding minimal_unsat_core_tabl_atoms_def by force
  with pre have empty: "set I \<inter> set ui' = {}" by auto
  have "minimal_unsat_core_tabl_atoms (set I) t (set as)"
    by (rule minimal_unsat_core_tabl_atoms_mono[OF _ unsat], auto)
  from preprocess_minimal_unsat_core[OF prep this empty]
  have "minimal_unsat_core_ns (set I) (set nsc)" .
  then show ?case using I weak unfolding S' using pre by auto
next
  case (5 nsc) (* init *)
  obtain t as tv' ui' where prep[simp]: "preprocess nsc = (t, as, tv', ui')" by (cases "preprocess nsc")
  show ?case unfolding init_nsc_def  
    using init_s preprocess_tableau_normalized[OF prep] 
    by (auto simp: list_map_to_fun_create_map)
next
  case (6 nsc J S v) (* solution *)
  obtain asi s tv ui where S: "S = ((asi,tv,ui),s)" by (cases S, auto)
  obtain t as tv' ui' where prep[simp]: "preprocess nsc = (t, as, tv', ui')" by (cases "preprocess nsc")
  have "(J,\<langle>solution_s s\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as" "\<langle>solution_s s\<rangle> \<Turnstile>\<^sub>t t" 
    using 6 S solution_s[of t _ s] by auto
  from i_preprocess_sat[OF prep _ this]
  show ?case using 6 S by auto
next
  case (7 nsc J S c K S' S'') (* backtrack *)
  obtain t as tvp uip where prep[simp]: "preprocess nsc = (t, as, tvp, uip)" by (cases "preprocess nsc")
  obtain asi s tv ui where S: "S = ((asi,tv,ui),s)" by (cases S, auto)
  obtain asi' s' tv' ui' where S': "S' = ((asi',tv',ui'),s')" by (cases S', auto)
  obtain asi'' s'' tv'' ui'' where S'': "S'' = ((asi'',tv'',ui''),s'')" by (cases S'', auto)
  from backtrack_s[of t _ s c _ s' s''] 
  show ?case using 7 S S' S'' by auto
next
  case (8 nsc J S)
  then show ?case using weak_invariant_s by (cases S, auto)
next
  case (9 nsc J S)
  then show ?case using checked_invariant_s by (cases S, auto)
qed

end

subsection \<open>Highest Layer: Incremental Constraints\<close>

text \<open>Interface\<close>

locale Incremental_Simplex_Ops = fixes 
  init_cs :: "'i i_constraint list \<Rightarrow> 's" and
  assert_cs :: "'i \<Rightarrow> 's \<Rightarrow> 'i list + 's" and
  check_cs :: "'s \<Rightarrow> 's \<times> 'i list option" and
  solution_cs :: "'s \<Rightarrow> rat valuation" and
  checkpoint_cs :: "'s \<Rightarrow> 'c" and
  backtrack_cs :: "'c \<Rightarrow> 's \<Rightarrow> 's" and
  weak_invariant_cs :: "'i i_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool" and
  invariant_cs :: "'i i_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool" and
  checked_cs :: "'i i_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool"
assumes 
  assert_cs_ok: "invariant_cs cs J s \<Longrightarrow> assert_cs j s = Inr s' \<Longrightarrow> 
    invariant_cs cs (insert j J) s'" and
  assert_cs_unsat: "invariant_cs cs J s \<Longrightarrow> assert_cs j s = Unsat I \<Longrightarrow>
    set I \<subseteq> insert j J \<and> minimal_unsat_core (set I) cs" and
  check_cs_ok: "invariant_cs cs J s \<Longrightarrow> check_cs s = (s', None) \<Longrightarrow> 
    checked_cs cs J s'" and
  check_cs_unsat: "invariant_cs cs J s \<Longrightarrow> check_cs s = (s',Some I) \<Longrightarrow>
    weak_invariant_cs cs J s' \<and> set I \<subseteq> J \<and> minimal_unsat_core (set I) cs" and
  init_cs: "checked_cs cs {} (init_cs cs)" and
  solution_cs: "checked_cs cs J s \<Longrightarrow> solution_cs s = v \<Longrightarrow> (J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs" and
  backtrack_cs: "checked_cs cs J s \<Longrightarrow> checkpoint_cs s = c 
    \<Longrightarrow> weak_invariant_cs cs K s' \<Longrightarrow> backtrack_cs c s' = s'' \<Longrightarrow> J \<subseteq> K \<Longrightarrow> invariant_cs cs J s''" and
  weak_invariant_cs: "invariant_cs cs J s \<Longrightarrow> weak_invariant_cs cs J s" and
  checked_invariant_cs: "checked_cs cs J s \<Longrightarrow> invariant_cs cs J s" 

text \<open>Implementation via the Simplex-operation To-Ns and the Incremental Operations for Non-Strict Constraints\<close>

locale Incremental_NS_Constraint_Ops_To_Ns_For_Incremental_Simplex =
  Incremental_NS_Constraint_Ops init_nsc assert_nsc check_nsc solution_nsc checkpoint_nsc backtrack_nsc 
  weak_invariant_nsc invariant_nsc checked_nsc + To_ns to_ns from_ns
  for 
    init_nsc :: "('i,'a :: lrv) i_ns_constraint list \<Rightarrow> 's" and
    assert_nsc :: "'i \<Rightarrow> 's \<Rightarrow> 'i list + 's" and
    check_nsc :: "'s \<Rightarrow> 's \<times> 'i list option" and
    solution_nsc :: "'s \<Rightarrow> (var, 'a) mapping" and
    checkpoint_nsc :: "'s \<Rightarrow> 'c" and
    backtrack_nsc :: "'c \<Rightarrow> 's \<Rightarrow> 's" and
    weak_invariant_nsc :: "('i,'a) i_ns_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool" and
    invariant_nsc :: "('i,'a) i_ns_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool" and
    checked_nsc :: "('i,'a) i_ns_constraint list \<Rightarrow> 'i set \<Rightarrow> 's \<Rightarrow> bool" and
    to_ns :: "'i i_constraint list \<Rightarrow> ('i,'a) i_ns_constraint list" and
    from_ns :: "(var, 'a) mapping \<Rightarrow> 'a ns_constraint list \<Rightarrow> (var, rat) mapping"
begin

fun assert_cs where "assert_cs i (cs,s) = (case assert_nsc i s of 
    Unsat I \<Rightarrow> Unsat I 
  | Inr s' \<Rightarrow> Inr (cs, s'))" 

definition "init_cs cs = (let tons_cs = to_ns cs in (map snd (tons_cs), init_nsc tons_cs))" 

definition "check_cs s = prod_wrap (\<lambda> cs. check_nsc) s" 
fun checkpoint_cs where "checkpoint_cs (cs,s) = (checkpoint_nsc s)" 
fun backtrack_cs where "backtrack_cs c (cs,s) = (cs, backtrack_nsc c s)" 
fun solution_cs where "solution_cs (cs,s) = (\<langle>from_ns (solution_nsc s) cs\<rangle>)" 

fun weak_invariant_cs where 
  "weak_invariant_cs cs J (ds,s) = (ds = map snd (to_ns cs) \<and> weak_invariant_nsc (to_ns cs) J s)" 
fun invariant_cs where 
  "invariant_cs cs J (ds,s) = (ds = map snd (to_ns cs) \<and> invariant_nsc (to_ns cs) J s)" 
fun checked_cs where 
  "checked_cs cs J (ds,s) = (ds = map snd (to_ns cs) \<and> checked_nsc (to_ns cs) J s)" 

sublocale Incremental_Simplex_Ops 
  init_cs 
  assert_cs  
  check_cs 
  solution_cs 
  checkpoint_cs 
  backtrack_cs
  weak_invariant_cs 
  invariant_cs 
  checked_cs
proof (unfold_locales, goal_cases)
  case (1 cs J S j S') (* assert ok *)
  then obtain s where S: "S = (map snd (to_ns cs),s)" by (cases S, auto)
  note pre = 1[unfolded S assert_cs.simps]
  from pre(2) obtain s' where
    ok: "assert_nsc j s = Inr s'" and S': "S' = (map snd (to_ns cs),s')" 
    by (auto split: sum.splits)
  from pre(1)
  have inv: "invariant_nsc (to_ns cs) J s" by simp
  from assert_nsc_ok[OF inv ok] 
  show ?case unfolding invariant_cs.simps S' split by auto
next
  case (2 cs J S j I) (* assert unsat *)
  then obtain s where S: "S = (map snd (to_ns cs), s)" by (cases S, auto)
  note pre = 2[unfolded S assert_cs.simps]
  from pre(2) have unsat: "assert_nsc j s = Unsat I"  
    by (auto split: sum.splits)
  from pre(1) have inv: "invariant_nsc (to_ns cs) J s" by auto
  from assert_nsc_unsat[OF inv unsat]
  have "set I \<subseteq> insert j J" "minimal_unsat_core_ns (set I) (set (to_ns cs))" 
    by auto
  from to_ns_unsat[OF this(2)] this(1)
  show ?case by blast
next
  case (3 cs J S S') (* check ok *)
  then show ?case using check_nsc_ok unfolding check_cs_def
    by (cases S, auto split: prod.splits)
next
  case (4 cs J S S' I) (* check unsat *)
  then obtain s where S: "S = (map snd (to_ns cs),s)" by (cases S, auto)
  note pre = 4[unfolded S check_cs_def]
  from pre(2) obtain s' where unsat: "check_nsc s = (s',Some I)"
    and S': "S' = (map snd (to_ns cs),s')" 
    by (auto split: prod.splits)
  from pre(1) have inv: "invariant_nsc (to_ns cs) J s" by auto
  from check_nsc_unsat[OF inv unsat]
  have "set I \<subseteq> J" "weak_invariant_nsc (to_ns cs) J s'" 
    "minimal_unsat_core_ns (set I) (set (to_ns cs))" 
    unfolding minimal_unsat_core_ns_def by auto
  from to_ns_unsat[OF this(3)] this(1,2)
  show ?case unfolding S' using S by auto
next
  case (5 cs) (* init *)
  show ?case unfolding init_cs_def Let_def using init_nsc by auto
next
  case (6 cs J S v) (* solution *)
  then obtain s where S: "S = (map snd (to_ns cs),s)" by (cases S, auto)
  obtain w where w: "solution_nsc s = w" by auto
  note pre = 6[unfolded S solution_cs.simps w Let_def]
  from pre have
    inv: "checked_nsc (to_ns cs) J s" and
    v: "v = \<langle>from_ns w (map snd (to_ns cs))\<rangle>" by auto
  from solution_nsc[OF inv w] have w: "(J, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s  set (to_ns cs)" .
  from i_to_ns_sat[OF w]
  show ?case unfolding v .
next
  case (7 cs J S c K S' S'') (* backtrack *)
  then show ?case using backtrack_nsc[of "to_ns cs" J]
    by (cases S, cases S', cases S'', auto)
next
  case (8 cs J S)
  then show ?case using weak_invariant_nsc by (cases S, auto)
next
  case (9 cs J S)
  then show ?case using checked_invariant_nsc by (cases S, auto)
qed 

end


subsection \<open>Concrete Implementation\<close>

subsubsection \<open>Connecting all the locales\<close>

global_interpretation Incremental_State_Ops_Simplex_Default:
  Incremental_State_Ops_Simplex assert_bound_code init_state check_code 
  defines assert_s = Incremental_State_Ops_Simplex_Default.assert_s and
          check_s  = Incremental_State_Ops_Simplex_Default.check_s and 
          backtrack_s  = Incremental_State_Ops_Simplex_Default.backtrack_s and
          checkpoint_s = Incremental_State_Ops_Simplex_Default.checkpoint_s and
          weak_invariant_s = Incremental_State_Ops_Simplex_Default.weak_invariant_s and
          invariant_s = Incremental_State_Ops_Simplex_Default.invariant_s and
          checked_s = Incremental_State_Ops_Simplex_Default.checked_s and
          assert_all_s = Incremental_State_Ops_Simplex_Default.assert_all_s
  ..

(* RT: I don't know why the following two lemmas and the declare are required,
   and not done automatically via the global-interpretation *)
lemma Incremental_State_Ops_Simplex_Default_assert_all_s[simp]: 
  "Incremental_State_Ops_Simplex_Default.assert_all_s = assert_all_s"
  by (metis assert_all_s_def assert_s_def)

lemmas assert_all_s_code = Incremental_State_Ops_Simplex_Default.assert_all_s.simps[unfolded 
  Incremental_State_Ops_Simplex_Default_assert_all_s]

declare assert_all_s_code[code]


global_interpretation Incremental_Atom_Ops_For_NS_Constraint_Ops_Default: 
  Incremental_Atom_Ops_For_NS_Constraint_Ops init_state assert_s check_s \<V> 
  checkpoint_s backtrack_s weak_invariant_s invariant_s checked_s preprocess
  defines
    init_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.init_nsc and
    check_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.check_nsc and
    assert_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.assert_nsc and
    checkpoint_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.checkpoint_nsc and
    solution_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.solution_nsc and
    backtrack_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.backtrack_nsc and
    invariant_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.invariant_nsc and
    weak_invariant_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.weak_invariant_nsc and
    checked_nsc = Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.checked_nsc 
  ..

type_synonym 'i simplex_state' = "QDelta ns_constraint list 
  \<times> (('i, ('i \<times> QDelta atom) list) mapping \<times> ((var,QDelta)mapping \<Rightarrow> (var,QDelta)mapping) \<times> 'i list) 
  \<times> ('i, QDelta) state"


global_interpretation Incremental_Simplex:
  Incremental_NS_Constraint_Ops_To_Ns_For_Incremental_Simplex 
  init_nsc assert_nsc check_nsc solution_nsc checkpoint_nsc backtrack_nsc
  weak_invariant_nsc invariant_nsc checked_nsc to_ns from_ns
  defines 
    init_simplex' = Incremental_Simplex.init_cs and
    assert_simplex' = Incremental_Simplex.assert_cs and
    check_simplex' = Incremental_Simplex.check_cs and
    backtrack_simplex' = Incremental_Simplex.backtrack_cs and
    checkpoint_simplex' = Incremental_Simplex.checkpoint_cs and
    solution_simplex' = Incremental_Simplex.solution_cs and
    weak_invariant_simplex' = Incremental_Simplex.weak_invariant_cs and
    invariant_simplex' = Incremental_Simplex.invariant_cs and
    checked_simplex' = Incremental_Simplex.checked_cs 
proof -
  interpret Incremental_NS_Constraint_Ops init_nsc assert_nsc check_nsc solution_nsc checkpoint_nsc
    backtrack_nsc weak_invariant_nsc invariant_nsc checked_nsc
    using Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.ns_constraints_ops .
  show "Incremental_NS_Constraint_Ops_To_Ns_For_Incremental_Simplex init_nsc assert_nsc check_nsc
     solution_nsc checkpoint_nsc backtrack_nsc weak_invariant_nsc invariant_nsc checked_nsc to_ns from_ns" 
    ..
qed 

subsubsection \<open>An implementation which encapsulates the state\<close>

text \<open>In principle, we now already have a complete implementation of the incremental simplex algorithm with
  @{const init_simplex'}, @{const assert_simplex'}, etc. However, this implementation results in code where
  the interal type @{typ "'i simplex_state'"} becomes visible. Therefore, we now define all operations
  on a new type which encapsulates the internal construction.\<close>

datatype 'i simplex_state = Simplex_State "'i simplex_state'" 
datatype 'i simplex_checkpoint = Simplex_Checkpoint "(nat, 'i \<times> QDelta) mapping \<times> (nat, 'i \<times> QDelta) mapping" 

fun init_simplex where "init_simplex cs =
  (let tons_cs = to_ns cs
   in Simplex_State (map snd tons_cs,
       case preprocess tons_cs of (t, as, trans_v, ui) \<Rightarrow> ((create_map as, trans_v, remdups ui), init_state t)))" 

fun assert_simplex where "assert_simplex i (Simplex_State (cs, (asi, tv, ui), s)) =
  (if i \<in> set ui then Inl [i] else 
    case assert_all_s (list_map_to_fun asi i) s of 
      Inl y \<Rightarrow> Inl y | Inr s' \<Rightarrow> Inr (Simplex_State (cs, (asi, tv, ui), s')))" 

fun check_simplex where 
  "check_simplex (Simplex_State (cs, asi_tv, s)) = (case check_s s of (s', res) \<Rightarrow>
     (Simplex_State (cs, asi_tv, s'), res))"

fun solution_simplex where
  "solution_simplex (Simplex_State (cs, (asi, tv, ui), s)) = \<langle>from_ns (tv (\<V> s)) cs\<rangle>" 

fun checkpoint_simplex where "checkpoint_simplex (Simplex_State (cs, asi_tv, s)) = Simplex_Checkpoint (checkpoint_s s)" 

fun backtrack_simplex where
  "backtrack_simplex (Simplex_Checkpoint c) (Simplex_State (cs, asi_tv, s)) = Simplex_State (cs, asi_tv, backtrack_s c s)" 

subsubsection \<open>Soundness of the incremental simplex implementation\<close>

text \<open>First link the unprimed constants against their primed counterparts.\<close>
lemma init_simplex': "init_simplex cs = Simplex_State (init_simplex' cs)" 
  by (simp add: Let_def Incremental_Simplex.init_cs_def Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.init_nsc_def)

lemma assert_simplex': "assert_simplex i (Simplex_State s) = map_sum id Simplex_State (assert_simplex' i s)"
  by (cases s, cases "fst (snd s)", auto 
    simp add: Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.assert_nsc_def split: sum.splits)

lemma check_simplex': "check_simplex (Simplex_State s) = map_prod Simplex_State id (check_simplex' s)" 
  by (cases s, simp add: Incremental_Simplex.check_cs_def
    Incremental_Atom_Ops_For_NS_Constraint_Ops_Default.check_nsc_def split: prod.splits)

lemma solution_simplex': "solution_simplex (Simplex_State s) = solution_simplex' s" 
  by (cases s, auto)

lemma checkpoint_simplex': "checkpoint_simplex (Simplex_State s) = Simplex_Checkpoint (checkpoint_simplex' s)" 
  by (cases s, auto split: sum.splits)

lemma backtrack_simplex': "backtrack_simplex (Simplex_Checkpoint c) (Simplex_State s) = Simplex_State (backtrack_simplex' c s)" 
  by (cases s, auto split: sum.splits)

fun invariant_simplex where
  "invariant_simplex cs J (Simplex_State s) = invariant_simplex' cs J s" 

fun weak_invariant_simplex where
  "weak_invariant_simplex cs J (Simplex_State s) = weak_invariant_simplex' cs J s" 

fun checked_simplex where
  "checked_simplex cs J (Simplex_State s) = checked_simplex' cs J s" 

text \<open>Hide implementation\<close>

declare init_simplex.simps[simp del]
declare assert_simplex.simps[simp del]
declare check_simplex.simps[simp del]
declare solution_simplex.simps[simp del]
declare checkpoint_simplex.simps[simp del]
declare backtrack_simplex.simps[simp del]


text \<open>Soundness lemmas\<close>

lemma init_simplex: "checked_simplex cs {} (init_simplex cs)" 
  using Incremental_Simplex.init_cs by (simp add: init_simplex')

lemma assert_simplex_ok:
  "invariant_simplex cs J s \<Longrightarrow> assert_simplex j s = Inr s' \<Longrightarrow> invariant_simplex cs (insert j J) s'"  
proof (cases s)
  case s: (Simplex_State ss)
  show "invariant_simplex cs J s \<Longrightarrow> assert_simplex j s = Inr s' \<Longrightarrow> invariant_simplex cs (insert j J) s'"
    unfolding s invariant_simplex.simps assert_simplex' using Incremental_Simplex.assert_cs_ok[of cs J ss j]
    by (cases "assert_simplex' j ss", auto)
qed
  
lemma assert_simplex_unsat:
  "invariant_simplex cs J s \<Longrightarrow> assert_simplex j s = Inl I \<Longrightarrow> 
     set I \<subseteq> insert j J \<and> minimal_unsat_core (set I) cs" 
proof (cases s)
  case s: (Simplex_State ss)
  show "invariant_simplex cs J s \<Longrightarrow> assert_simplex j s = Inl I \<Longrightarrow> 
    set I \<subseteq> insert j J \<and> minimal_unsat_core (set I) cs"
    unfolding s invariant_simplex.simps assert_simplex' 
    using Incremental_Simplex.assert_cs_unsat[of cs J ss j]
    by (cases "assert_simplex' j ss", auto)
qed

lemma check_simplex_ok:
  "invariant_simplex cs J s \<Longrightarrow> check_simplex s = (s',None) \<Longrightarrow> checked_simplex cs J s'" 
proof (cases s)
  case s: (Simplex_State ss)
  show "invariant_simplex cs J s \<Longrightarrow> check_simplex s = (s',None) \<Longrightarrow> checked_simplex cs J s'"
    unfolding s invariant_simplex.simps check_simplex.simps check_simplex' using Incremental_Simplex.check_cs_ok[of cs J ss]
    by (cases "check_simplex' ss", auto)
qed

lemma check_simplex_unsat:
  "invariant_simplex cs J s \<Longrightarrow> check_simplex s = (s',Some I) \<Longrightarrow> 
     weak_invariant_simplex cs J s' \<and> set I \<subseteq> J \<and> minimal_unsat_core (set I) cs" 
proof (cases s)
  case s: (Simplex_State ss)
  show "invariant_simplex cs J s \<Longrightarrow> check_simplex s = (s',Some I) \<Longrightarrow> 
    weak_invariant_simplex cs J s' \<and> set I \<subseteq> J \<and> minimal_unsat_core (set I) cs"
    unfolding s invariant_simplex.simps check_simplex.simps check_simplex' 
    using Incremental_Simplex.check_cs_unsat[of cs J ss _ I]
    by (cases "check_simplex' ss", auto)
qed

lemma solution_simplex:
  "checked_simplex cs J s \<Longrightarrow> solution_simplex s = v \<Longrightarrow> (J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs" 
  using Incremental_Simplex.solution_cs[of cs J]
  by (cases s, auto simp: solution_simplex')

lemma backtrack_simplex:
  "checked_simplex cs J s \<Longrightarrow>
   checkpoint_simplex s = c \<Longrightarrow>
   weak_invariant_simplex cs K s' \<Longrightarrow> 
   backtrack_simplex c s' = s'' \<Longrightarrow> 
   J \<subseteq> K \<Longrightarrow> 
   invariant_simplex cs J s''" 
proof -
  obtain ss where ss: "s = Simplex_State ss" by (cases s, auto)
  obtain ss' where ss': "s' = Simplex_State ss'" by (cases s', auto)
  obtain ss'' where ss'': "s'' = Simplex_State ss''" by (cases s'', auto)
  obtain cc where cc: "c = Simplex_Checkpoint cc" by (cases c, auto)
  show "checked_simplex cs J s \<Longrightarrow>
   checkpoint_simplex s = c \<Longrightarrow>
   weak_invariant_simplex cs K s' \<Longrightarrow> 
   backtrack_simplex c s' = s'' \<Longrightarrow> 
   J \<subseteq> K \<Longrightarrow> 
   invariant_simplex cs J s''" 
    unfolding ss ss' ss'' cc checked_simplex.simps invariant_simplex.simps checkpoint_simplex' backtrack_simplex'
    using Incremental_Simplex.backtrack_cs[of cs J ss cc K ss' ss''] by simp
qed

lemma weak_invariant_simplex:
  "invariant_simplex cs J s \<Longrightarrow> weak_invariant_simplex cs J s" 
  using Incremental_Simplex.weak_invariant_cs[of cs J] by (cases s, auto)

lemma checked_invariant_simplex:
  "checked_simplex cs J s \<Longrightarrow> invariant_simplex cs J s" 
  using Incremental_Simplex.checked_invariant_cs[of cs J] by (cases s, auto)

declare checked_simplex.simps[simp del]
declare invariant_simplex.simps[simp del]
declare weak_invariant_simplex.simps[simp del]

text \<open>From this point onwards, one should not look into the types @{typ "'i simplex_state"}
  and @{typ "'i simplex_checkpoint"}.\<close>

text \<open>For convenience: an assert-all function which takes multiple indices.\<close>


fun assert_all_simplex :: "'i list \<Rightarrow> 'i simplex_state \<Rightarrow> 'i list + 'i simplex_state" where
  "assert_all_simplex [] s = Inr s" 
| "assert_all_simplex (j # J) s = (case assert_simplex j s of Unsat I \<Rightarrow> Unsat I 
     | Inr s' \<Rightarrow> assert_all_simplex J s')" 

lemma assert_all_simplex_ok: "invariant_simplex cs J s \<Longrightarrow> assert_all_simplex K s = Inr s' \<Longrightarrow> 
    invariant_simplex cs (J \<union> set K) s'"
proof (induct K arbitrary: s J)
  case (Cons k K s J)
  from Cons(3) obtain s'' where ass: "assert_simplex k s = Inr s''" and rec: "assert_all_simplex K s'' = Inr s'" 
    by (auto split: sum.splits)
  from Cons(1)[OF assert_simplex_ok[OF Cons(2) ass] rec]
  show ?case by auto
qed auto

lemma assert_all_simplex_unsat: "invariant_simplex cs J s \<Longrightarrow> assert_all_simplex K s = Unsat I \<Longrightarrow> 
    set I \<subseteq> set K \<union> J \<and> minimal_unsat_core (set I) cs"
proof (induct K arbitrary: s J)
  case (Cons k K s J)
  show ?case
  proof (cases "assert_simplex k s")
    case unsat: (Inl J')
    with Cons have J': "J' = I" by auto
    from assert_simplex_unsat[OF Cons(2) unsat]
    have "set J' \<subseteq> insert k J" "minimal_unsat_core (set J') cs" by auto
    then show ?thesis unfolding J' i_satisfies_cs.simps
      by auto
  next
    case (Inr s')
    from Cons(1)[OF assert_simplex_ok[OF Cons(2) Inr]] Cons(3) Inr show ?thesis by auto
  qed
qed simp

text \<open>The collection of soundness lemmas for the incremental simplex algorithm.\<close>

lemmas incremental_simplex = 
  init_simplex
  assert_simplex_ok
  assert_simplex_unsat
  assert_all_simplex_ok
  assert_all_simplex_unsat
  check_simplex_ok
  check_simplex_unsat
  solution_simplex
  backtrack_simplex
  checked_invariant_simplex
  weak_invariant_simplex

subsection \<open>Test Executability and Example for Incremental Interface\<close>

value (code) "let cs = [
    (1 :: int, LT (lp_monom 1 1) 4), \<comment> \<open>$x_1 < 4$\<close>
    (2, GT (lp_monom 2 1 - lp_monom 1 2) 0), \<comment> \<open>$2x_1 - x_2 > 0$\<close>
    (3, EQ (lp_monom 1 1 - lp_monom 2 2) 0), \<comment> \<open>$x_1 - 2x_2 = 0$\<close>
    (4, GT (lp_monom 2 2) 5), \<comment> \<open>$2x_2 > 5$\<close>
    (5, GT (lp_monom 3 0) 7), \<comment> \<open>$3x_0 > 7$\<close>
    (6, GT (lp_monom 3 3 + lp_monom (1/3) 2) 2)]; \<comment> \<open>$3x_3 + 1/3x_2 > 2$\<close>
    s1 = init_simplex cs; \<comment> \<open>initialize\<close>
    s2 = (case assert_all_simplex [1,2,3] s1 of Inr s \<Rightarrow> s | Unsat _ \<Rightarrow> undefined); \<comment> \<open>assert 1,2,3\<close>
    s3 = (case check_simplex s2 of (s,None) \<Rightarrow> s | _ \<Rightarrow> undefined); \<comment> \<open>check that 1,2,3 are sat.\<close>
    c123 = checkpoint_simplex s3; \<comment> \<open>after check, store checkpoint for backtracking\<close>
    s4 = (case assert_simplex 4 s2 of Inr s \<Rightarrow> s | Unsat _ \<Rightarrow> undefined); \<comment> \<open>assert 4\<close>
    (s5,I) = (case check_simplex s4 of (s,Some I) \<Rightarrow> (s,I) | _ \<Rightarrow> undefined); \<comment> \<open>checking detects unsat-core 1,3,4\<close>
    s6 = backtrack_simplex c123 s5; \<comment> \<open>backtrack to constraints 1,2,3\<close>
    s7 = (case assert_all_simplex [5,6] s6 of Inr s \<Rightarrow> s | Unsat _ \<Rightarrow> undefined); \<comment> \<open>assert 5,6\<close>
    s8 = (case check_simplex s7 of (s,None) \<Rightarrow> s | _ \<Rightarrow> undefined); \<comment> \<open>check that 1,2,3,5,6 are sat.\<close>
    sol = solution_simplex s8 \<comment> \<open>solution for 1,2,3,5,6\<close>
  in (I, map (\<lambda> x. (''x_'', x, ''='', sol x)) [0,1,2,3]) \<comment> \<open>output unsat core and solution\<close>" 
end