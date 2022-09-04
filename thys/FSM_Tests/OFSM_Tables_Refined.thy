section \<open>Alternative OFSM Table Computation\<close>

text \<open>The approach to computing OFSM tables presented in the imported theories is easy to use in 
      proofs but inefficient in practice due to repeated recomputation of the same tables.
      Thus, in the following we present a more efficient method for computing and storing tables.\<close>

theory OFSM_Tables_Refined
imports Minimisation Distinguishability 
begin

subsection \<open>Computing a List of all OFSM Tables\<close>

type_synonym ('a,'b,'c) ofsm_table = "('a, 'a set) mapping"

fun initial_ofsm_table :: "('a::linorder,'b,'c) fsm \<Rightarrow> ('a,'b,'c) ofsm_table" where
  "initial_ofsm_table M = Mapping.tabulate (states_as_list M) (\<lambda>q . states M)"


abbreviation "ofsm_lookup \<equiv> Mapping.lookup_default {}"

lemma initial_ofsm_table_lookup_invar: "ofsm_lookup (initial_ofsm_table M) q = ofsm_table M (\<lambda>q . states M) 0 q"
proof (cases "q \<in> states M")
  case True 
  then have "q \<in> list.set (states_as_list M)"
    using states_as_list_set by auto 
  then have "Mapping.lookup (initial_ofsm_table M) q = Some (states M)"
    unfolding initial_ofsm_table.simps
    by (simp add: lookup_tabulate) 
  then have "ofsm_lookup (initial_ofsm_table M) q = states M"
    by (simp add: lookup_default_def) 
  then show ?thesis 
    using True by auto
next
  case False
  then have "q \<notin> list.set (states_as_list M)"
    using states_as_list_set by auto 
  then have "Mapping.lookup (initial_ofsm_table M) q = None"
    unfolding initial_ofsm_table.simps
    by (simp add: lookup_tabulate) 
  then have "ofsm_lookup (initial_ofsm_table M) q = {}"
    by (simp add: lookup_default_def)
  then show ?thesis 
    using False by auto
qed


lemma initial_ofsm_table_keys_invar: "Mapping.keys (initial_ofsm_table M) = states M"
  using states_as_list_set[of M]
  by simp 


fun next_ofsm_table :: "('a::linorder,'b,'c) fsm \<Rightarrow> ('a,'b,'c) ofsm_table \<Rightarrow> ('a,'b,'c) ofsm_table" where
  "next_ofsm_table M prev_table = Mapping.tabulate (states_as_list M) (\<lambda> q . {q' \<in> ofsm_lookup prev_table q . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_lookup prev_table qT = ofsm_lookup prev_table qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None) })"

lemma h_obs_non_state :
  assumes "q \<notin> states M"
  shows "h_obs M q x y = None"
proof -
  have *:"\<And> x . h M (q,x) = {}"
    using assms fsm_transition_source
    unfolding h_simps 
    by force
  show ?thesis
    unfolding h_obs_simps Let_def *
    by (simp add: Set.filter_def) 
qed


lemma next_ofsm_table_lookup_invar: 
  assumes "\<And> q . ofsm_lookup prev_table q = ofsm_table M (\<lambda>q . states M) k q"
  shows "ofsm_lookup (next_ofsm_table M prev_table) q = ofsm_table M (\<lambda>q . states M) (Suc k) q"
proof (cases "q \<in> states M")
  case True 

  let ?prev_table = "ofsm_table M (\<lambda>q . states M) k"

  from True have "q \<in> list.set (states_as_list M)"
    using states_as_list_set by auto 
  then have "Mapping.lookup (next_ofsm_table M prev_table) q = Some {q' \<in> ofsm_lookup prev_table q . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_lookup prev_table qT = ofsm_lookup prev_table qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None) }"
    unfolding next_ofsm_table.simps
    by (meson lookup_tabulate states_as_list_distinct)
  then have "ofsm_lookup (next_ofsm_table M prev_table) q = {q' \<in> ofsm_lookup prev_table q . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_lookup prev_table qT = ofsm_lookup prev_table qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None) }"
    by (simp add: lookup_default_def)
  also have "\<dots> = {q' \<in> ?prev_table q . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ?prev_table qT = ?prev_table qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None) }" 
    unfolding assms by presburger
  also have "\<dots> = ofsm_table M (\<lambda>q . states M) (Suc k) q"
    unfolding ofsm_table.simps Let_def by presburger
  finally show ?thesis .
next
  case False
  then have "q \<notin> list.set (states_as_list M)"
    using states_as_list_set by auto 
  then have "Mapping.lookup (next_ofsm_table M prev_table) q = None"
    by (simp add: lookup_tabulate)
  then have "ofsm_lookup (next_ofsm_table M prev_table) q = {}"
    by (simp add: lookup_default_def)
  then show ?thesis
    unfolding ofsm_table_non_state[OF False] .
qed

lemma next_ofsm_table_keys_invar: "Mapping.keys (next_ofsm_table M prev_table) = states M"
  using states_as_list_set[of M]
  by simp 


fun compute_ofsm_table_list :: "('a::linorder,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) ofsm_table list" where
  "compute_ofsm_table_list M k = rev (foldr (\<lambda> _ prev . (next_ofsm_table M (hd prev)) # prev) [0..<k] [initial_ofsm_table M])"


lemma compute_ofsm_table_list_props:
  "length (compute_ofsm_table_list M k) = Suc k"
  "\<And> i q . i < Suc k \<Longrightarrow> ofsm_lookup ((compute_ofsm_table_list M k) ! i) q = ofsm_table M (\<lambda>q . states M) i q"
  "\<And> i . i < Suc k \<Longrightarrow> Mapping.keys ((compute_ofsm_table_list M k) ! i) = states M"
proof -

  define t where "t = (\<lambda> k . (foldr (\<lambda> _ prev . (next_ofsm_table M (hd prev)) # prev) (rev [0..<k]) [initial_ofsm_table M]))"

  have t_props:"length (t k) = Suc k
          \<and> (\<forall> i q . i < Suc k \<longrightarrow> ofsm_lookup (t k ! (k-i)) q = ofsm_table M (\<lambda>q . states M) i q)
          \<and> (\<forall> i . i < Suc k \<longrightarrow> Mapping.keys (t k ! i) = states M)"
  proof (induction k)
    case 0
    have "t 0 = [initial_ofsm_table M]"
      unfolding t_def by auto
    show ?case 
      unfolding \<open>t 0 = [initial_ofsm_table M]\<close>
      using initial_ofsm_table_lookup_invar[of M]
      using initial_ofsm_table_keys_invar[of M]
      by auto
  next
    case (Suc k)

    have "rev [0..<Suc k] = k # (rev [0..<k])"
      by auto
    have *: "t (Suc k) = (next_ofsm_table M (hd (t k))) # (t k)"
      unfolding t_def \<open>rev [0..<Suc k] = k # (rev [0..<k])\<close>
      by auto

    have IH1: "length (t k) = Suc k"
    and  IH2: "\<And>i q . i < Suc k \<Longrightarrow> ofsm_lookup (t k ! (k-i)) q = ofsm_table M (\<lambda>q. FSM.states M) i q"
    and  IH3: "\<And>i . i < Suc k \<Longrightarrow> Mapping.keys (t k ! i) = FSM.states M"
      using Suc.IH by blast+

    have "length (t (Suc k)) = Suc (Suc k)"
      using IH1 unfolding * by auto
    moreover have "\<And>i q . i < Suc (Suc k) \<Longrightarrow> ofsm_lookup (t (Suc k) ! ((Suc k)-i)) q = ofsm_table M (\<lambda>q. FSM.states M) i q"
    proof -
      fix i q assume "i < Suc (Suc k)"
      then consider "i = Suc k" | "i < Suc k"
        using less_Suc_eq by blast
      then show "ofsm_lookup (t (Suc k) ! ((Suc k)-i)) q = ofsm_table M (\<lambda>q. FSM.states M) i q" proof cases
        case 1
        then have "(t (Suc k) ! ((Suc k)-i)) = hd (t (Suc k))"
          by (metis "*" diff_self_eq_0 list.sel(1) nth_Cons_0)          
        then have "(t (Suc k) ! ((Suc k)-i)) = next_ofsm_table M (hd (t k))"
          unfolding * by (metis list.sel(1))
        then have "ofsm_lookup (t (Suc k) ! ((Suc k)-i)) q = ofsm_lookup (next_ofsm_table M (hd (t k))) q"
          by auto
        
        have "(hd (t k)) = (t k ! (k-k))"
          by (metis IH1 diff_self_eq_0 hd_conv_nth list.size(3) nat.simps(3))
        moreover have "k < Suc k" by auto
        ultimately have "ofsm_lookup (next_ofsm_table M (hd (t k))) q = ofsm_table M (\<lambda>q. FSM.states M) i q"
          by (metis "1" IH2 next_ofsm_table_lookup_invar) 
        then show ?thesis
          unfolding \<open>ofsm_lookup (t (Suc k) ! ((Suc k)-i)) q = ofsm_lookup (next_ofsm_table M (hd (t k))) q\<close> .
      next
        case 2
        then have "((Suc k)-i) > 0"
          by auto
        then have "(t (Suc k) ! ((Suc k)-i)) = t k ! (((Suc k)-i) - 1)"
          unfolding * by (meson nth_Cons_pos)
        then have "(t (Suc k) ! ((Suc k)-i)) = t k ! (k-i)"
          by auto
        show "ofsm_lookup (t (Suc k) ! ((Suc k)-i)) q = ofsm_table M (\<lambda>q. FSM.states M) i q"
          using IH2[OF 2]
          unfolding \<open>(t (Suc k) ! ((Suc k)-i)) = t k ! (k-i)\<close> by metis
      qed
    qed
    moreover have "\<And>i . i < Suc (Suc k) \<Longrightarrow> Mapping.keys (t (Suc k) ! i) = FSM.states M"
      by (metis "*" IH3 Suc_diff_1 Suc_less_eq less_Suc_eq_0_disj next_ofsm_table_keys_invar nth_Cons')
    ultimately show ?case
      by blast
  qed
          
  
  have *:"(compute_ofsm_table_list M k) = rev (t k)"
    unfolding compute_ofsm_table_list.simps t_def
    using foldr_length_helper[of "rev [0..<k]" "[0..<k]" "(\<lambda> prev . (next_ofsm_table M (hd prev)) # prev)", OF length_rev]
    by metis

  show "length (compute_ofsm_table_list M k) = Suc k"
    using t_props unfolding * length_rev by blast

  have "\<And> i . i < Suc k \<Longrightarrow> (rev (t k) ! i) = t k ! (k - i)"
    by (simp add: rev_nth t_props)
  then show "\<And>i q. i < Suc k \<Longrightarrow>
           ofsm_lookup (compute_ofsm_table_list M k ! i) q = ofsm_table M (\<lambda>q. FSM.states M) i q"
    unfolding * using t_props
    by presburger 

  show "\<And>i. i < Suc k \<Longrightarrow> Mapping.keys (compute_ofsm_table_list M k ! i) = FSM.states M"
    unfolding * using t_props \<open>\<And> i . i < Suc k \<Longrightarrow> (rev (t k) ! i) = t k ! (k - i)\<close>
    by simp 
qed
      
        
     

fun compute_ofsm_tables :: "('a::linorder,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> (nat, ('a,'b,'c) ofsm_table) mapping" where
  "compute_ofsm_tables M k = Mapping.bulkload (compute_ofsm_table_list M k)"

lemma compute_ofsm_tables_entries :
  assumes "i < Suc k"
  shows "(the (Mapping.lookup (compute_ofsm_tables M k) i)) = ((compute_ofsm_table_list M k) ! i)"
  using assms 
  unfolding compute_ofsm_tables.simps bulkload_def
  by (metis bulkload.rep_eq bulkload_def compute_ofsm_table_list_props(1) lookup.rep_eq option.sel)

lemma compute_ofsm_tables_lookup_invar :
  assumes "i < Suc k"
  shows "ofsm_lookup (the (Mapping.lookup (compute_ofsm_tables M k) i)) q = ofsm_table M (\<lambda>q . states M) i q"
  using compute_ofsm_table_list_props(2)[OF assms]
  unfolding compute_ofsm_tables_entries[OF assms] by metis

lemma compute_ofsm_tables_keys_invar :
  assumes "i < Suc k"
  shows "Mapping.keys (the (Mapping.lookup (compute_ofsm_tables M k) i)) = states M"
  using compute_ofsm_table_list_props(3)[OF assms]
  unfolding compute_ofsm_tables_entries[OF assms] by metis


subsection \<open>Finding Diverging Tables\<close>


lemma ofsm_table_fix_from_compute_ofsm_tables :
  assumes "q \<in> states M"
shows "ofsm_lookup (the (Mapping.lookup (compute_ofsm_tables M (size M - 1)) (size M - 1))) q = ofsm_table_fix M (\<lambda>q. FSM.states M) 0 q" 
proof -
  have "((\<lambda>q. FSM.states M) ` FSM.states M) = {states M}"
    using fsm_initial[of M] by auto
  then have "card ((\<lambda>q. FSM.states M) ` FSM.states M) = 1"
    by auto
  
  have "ofsm_lookup (the (Mapping.lookup (compute_ofsm_tables M (size M - 1)) (size M - 1))) q = ofsm_table M (\<lambda>q. FSM.states M) (FSM.size M - 1) q"
    using compute_ofsm_tables_lookup_invar[of "(size M - 1)" "(size M - 1)" M q]
    by linarith
  also have "\<dots> = ofsm_table_fix M (\<lambda>q. FSM.states M) 0 q"
    using ofsm_table_fix_partition_fixpoint[OF minimise_initial_partition _ assms(1), of "size M"]
    unfolding \<open>card ((\<lambda>q. FSM.states M) ` FSM.states M) = 1\<close>
    by blast
  finally show ?thesis .
qed

fun find_first_distinct_ofsm_table' :: "('a::linorder,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "find_first_distinct_ofsm_table' M q1 q2 = (let 
    tables = (compute_ofsm_tables M (size M - 1))
in if (q1 \<in> states M 
      \<and> q2 \<in> states M 
      \<and> (ofsm_lookup (the (Mapping.lookup tables (size M - 1))) q1
         \<noteq> ofsm_lookup (the (Mapping.lookup tables (size M - 1))) q2))
  then the (find_index (\<lambda> i . ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq> ofsm_lookup (the (Mapping.lookup tables i)) q2) [0..<size M])
  else 0)"





lemma find_first_distinct_ofsm_table_is_first' :
  assumes "q1 \<in> FSM.states M" 
      and "q2 \<in> FSM.states M"
      and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
    shows "(find_first_distinct_ofsm_table M q1 q2) = Min {k . ofsm_table M (\<lambda>q . states M) k q1 \<noteq> ofsm_table M (\<lambda>q . states M) k q2
                                                                \<and> (\<forall>k' . k' < k \<longrightarrow> ofsm_table M (\<lambda>q . states M) k' q1 = ofsm_table M (\<lambda>q . states M) k' q2)}"
(is "find_first_distinct_ofsm_table M q1 q2 = Min ?ks")
proof -
  have "find_first_distinct_ofsm_table M q1 q2 \<in> ?ks"
    using find_first_distinct_ofsm_table_is_first[OF assms]
    by blast 
  moreover have "\<And> k . k \<in> ?ks \<Longrightarrow> k = find_first_distinct_ofsm_table M q1 q2" 
    using calculation linorder_neqE_nat by blast
  ultimately have "?ks = {find_first_distinct_ofsm_table M q1 q2}"
    by blast
  then show ?thesis 
    by fastforce
qed

lemma find_first_distinct_ofsm_table'_is_first' :
  assumes "q1 \<in> FSM.states M" 
      and "q2 \<in> FSM.states M"
      and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
    shows "(find_first_distinct_ofsm_table' M q1 q2) = Min {k . ofsm_table M (\<lambda>q . states M) k q1 \<noteq> ofsm_table M (\<lambda>q . states M) k q2
                                                                \<and> (\<forall>k' . k' < k \<longrightarrow> ofsm_table M (\<lambda>q . states M) k' q1 = ofsm_table M (\<lambda>q . states M) k' q2)}"
(is "find_first_distinct_ofsm_table' M q1 q2 = Min ?ks")
      and "find_first_distinct_ofsm_table' M q1 q2 \<le> size M - 1"
proof -

  define tables where "tables = compute_ofsm_tables M (FSM.size M - 1)"

  have "ofsm_lookup (the (Mapping.lookup tables (FSM.size M - 1))) q1 \<noteq>
           ofsm_lookup (the (Mapping.lookup tables (FSM.size M - 1))) q2"
    unfolding tables_def                                        
    unfolding ofsm_table_fix_from_compute_ofsm_tables[OF assms(1)]
    unfolding ofsm_table_fix_from_compute_ofsm_tables[OF assms(2)]
    using assms(3) .

  then have "find_first_distinct_ofsm_table' M q1 q2 = the (find_index
                   (\<lambda>i. ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq>
                        ofsm_lookup (the (Mapping.lookup tables i)) q2)
                   [0..<FSM.size M])"
    unfolding find_first_distinct_ofsm_table'.simps
    using assms(1,2,3) 
    unfolding Let_def tables_def[symmetric]
    by presburger

  have "FSM.size M - 1 \<in> set [0..<FSM.size M]"
    using fsm_size_Suc[of M] by auto
  then have *:"\<exists> k \<in> set [0..<FSM.size M] . (\<lambda>i. ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq>
                        ofsm_lookup (the (Mapping.lookup tables i)) q2) k"
    using \<open>ofsm_lookup (the (Mapping.lookup tables (FSM.size M - 1))) q1 \<noteq>
           ofsm_lookup (the (Mapping.lookup tables (FSM.size M - 1))) q2\<close>
    by blast
  have "find_index
                   (\<lambda>i. ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq>
                        ofsm_lookup (the (Mapping.lookup tables i)) q2)
                   [0..<FSM.size M] \<noteq> None"
    using find_index_exhaustive[OF *] .
  then obtain k where *:"find_index
                   (\<lambda>i. ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq>
                        ofsm_lookup (the (Mapping.lookup tables i)) q2)
                   [0..<FSM.size M] = Some k"
    by blast
  then have "find_first_distinct_ofsm_table' M q1 q2 = k"
    unfolding \<open>find_first_distinct_ofsm_table' M q1 q2 = the (find_index
                   (\<lambda>i. ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq>
                        ofsm_lookup (the (Mapping.lookup tables i)) q2)
                   [0..<FSM.size M])\<close>
    by auto

  have "\<And> k' . k' \<le> k \<Longrightarrow> [0..<FSM.size M] ! k' = k'" 
    using find_index_index(1)[OF *]
    by (metis add.left_neutral diff_zero dual_order.trans length_upt not_le nth_upt) 
  then have "[0..<FSM.size M] ! k = k" and "\<And> k' . k' < k \<Longrightarrow> [0..<FSM.size M] ! k' = k'"
    by auto
  have "k < Suc (size M - 1)"
    using find_index_index(1)[OF *]
    by auto
  
  have "ofsm_lookup (the (Mapping.lookup tables k)) q1 \<noteq> ofsm_lookup (the (Mapping.lookup tables k)) q2"
    using find_index_index(2)[OF *] 
    unfolding \<open>[0..<FSM.size M] ! k = k\<close> .
  then have p1: "ofsm_table M (\<lambda>q . states M) k q1 \<noteq> ofsm_table M (\<lambda>q . states M) k q2"
    unfolding tables_def
    unfolding compute_ofsm_tables_lookup_invar[OF \<open>k < Suc (size M - 1)\<close>] .

    
  have "\<And> k' . k' < k \<Longrightarrow> ofsm_lookup (the (Mapping.lookup tables k')) q1 = ofsm_lookup (the (Mapping.lookup tables k')) q2"
    using \<open>\<And> k' . k' < k \<Longrightarrow> [0..<FSM.size M] ! k' = k'\<close>
    using find_index_index(3)[OF *] 
    by auto
  then have p2: "(\<forall>k' . k' < k \<longrightarrow> ofsm_table M (\<lambda>q . states M) k' q1 = ofsm_table M (\<lambda>q . states M) k' q2)"
    unfolding tables_def
    using compute_ofsm_tables_lookup_invar[of _ "(size M - 1)" M ] \<open>k < Suc (size M - 1)\<close>
    using less_trans by blast

  have "k \<in> ?ks"
    using p1 p2 by blast
  moreover have "\<And> k' . k' \<in> ?ks \<Longrightarrow> k' = k"
    using calculation linorder_neqE_nat by blast
  ultimately have "?ks = {k}"
    by blast
  then show "find_first_distinct_ofsm_table' M q1 q2 = Min ?ks" 
    unfolding \<open>find_first_distinct_ofsm_table' M q1 q2 = k\<close>
    by fastforce

  show "find_first_distinct_ofsm_table' M q1 q2 \<le> FSM.size M - 1"
    unfolding \<open>find_first_distinct_ofsm_table' M q1 q2 = k\<close>
    using \<open>k < Suc (size M - 1)\<close>
    by auto
qed

lemma find_first_distinct_ofsm_table'_max : 
  "find_first_distinct_ofsm_table' M q1 q2 \<le> size M - 1"
proof (cases "q1 \<in> states M 
      \<and> q2 \<in> states M 
      \<and> (ofsm_lookup (the (Mapping.lookup (compute_ofsm_tables M (size M - 1)) (size M - 1))) q1
         \<noteq> ofsm_lookup (the (Mapping.lookup (compute_ofsm_tables M (size M - 1)) (size M - 1))) q2)")
  case True
  then show ?thesis using find_first_distinct_ofsm_table'_is_first'(2)[of q1 M q2]
    using ofsm_table_fix_from_compute_ofsm_tables by blast
next
  case False
  then have "find_first_distinct_ofsm_table' M q1 q2 = 0"
    unfolding find_first_distinct_ofsm_table'.simps Let_def by meson
  then show ?thesis 
    by linarith
qed



lemma find_first_distinct_ofsm_table_alt_def:
  "find_first_distinct_ofsm_table M q1 q2 = find_first_distinct_ofsm_table' M q1 q2"
proof (cases "q1 \<in> states M \<and> q2 \<in> states M \<and> ((ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2))")
  case True
  then have **: "q1 \<in> states M"
       and  ***: "q2 \<in> states M"
       and  ****: "(ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2)"
    by blast+
  show ?thesis 
    unfolding find_first_distinct_ofsm_table'_is_first'[OF ** *** ****]
    unfolding find_first_distinct_ofsm_table_is_first'[OF ** *** ****]
    by presburger
next
  case False

  have "find_first_distinct_ofsm_table M q1 q2 = 0"
    by (meson False find_first_distinct_ofsm_table_gt.simps)
  moreover have "find_first_distinct_ofsm_table' M q1 q2 = 0"
  proof (cases "q1 \<in> states M \<and> q2 \<in> states M")
    case True
    then have **: "q1 \<in> states M"
         and  ***: "q2 \<in> states M"
      by blast+
    then have ****:"((ofsm_table_fix M (\<lambda>q . states M) 0 q1 = ofsm_table_fix M (\<lambda>q . states M) 0 q2))"
      using False by blast

    define tables where "tables = compute_ofsm_tables M (FSM.size M - 1)"

    have "ofsm_lookup (the (Mapping.lookup tables (FSM.size M - 1))) q1 =
             ofsm_lookup (the (Mapping.lookup tables (FSM.size M - 1))) q2"
      unfolding tables_def
      unfolding ofsm_table_fix_from_compute_ofsm_tables[OF **]
      unfolding ofsm_table_fix_from_compute_ofsm_tables[OF ***]
      using **** .
    then show ?thesis 
      unfolding find_first_distinct_ofsm_table'.simps Let_def tables_def[symmetric] by auto
  next
    case False
    then show ?thesis 
      unfolding find_first_distinct_ofsm_table'.simps Let_def 
      by meson
  qed
  ultimately show ?thesis
    by presburger
qed


subsection \<open>Refining the Computation of Distinguishing Traces via OFSM Tables\<close>

fun select_diverging_ofsm_table_io' :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) \<times> ('a option \<times> 'a option)" where
  "select_diverging_ofsm_table_io' M q1 q2 k = (let
      tables = (compute_ofsm_tables M (size M - 1));
      ins = inputs_as_list M;
      outs = outputs_as_list M;
      table = ofsm_lookup (the (Mapping.lookup tables (k-1)));
      f = (\<lambda> (x,y) . case (h_obs M q1 x y, h_obs M q2 x y) 
                   of
                      (Some q1', Some q2')  \<Rightarrow> if table q1' \<noteq> table q2'
                                                  then Some ((x,y),(Some q1', Some q2'))
                                                  else None |
                      (None,None)           \<Rightarrow> None |
                      (Some q1', None)      \<Rightarrow> Some ((x,y),(Some q1', None)) |
                      (None, Some q2')      \<Rightarrow> Some ((x,y),(None, Some q2')))
      in 
        hd (List.map_filter f (List.product ins outs)))" 

lemma select_diverging_ofsm_table_io_alt_def :
  assumes "k \<le> size M - 1"
  shows "select_diverging_ofsm_table_io M q1 q2 k = select_diverging_ofsm_table_io' M q1 q2 k"
proof -
  define tables where "tables = compute_ofsm_tables M (FSM.size M - 1)"
  define table where "table = ofsm_lookup (the (Mapping.lookup tables (k-1)))"

  have "k - 1 < Suc (size M - 1)"
    using assms by auto
  have "ofsm_table M (\<lambda>q . states M) (k-1) = table"
    unfolding table_def tables_def
    unfolding compute_ofsm_tables_lookup_invar[OF \<open>k - 1 < Suc (size M - 1)\<close>]
    by presburger

  show ?thesis 
    unfolding select_diverging_ofsm_table_io'.simps
              select_diverging_ofsm_table_io.simps
              Let_def
    unfolding tables_def[symmetric] table_def[symmetric]
    unfolding \<open>ofsm_table M (\<lambda>q . states M) (k-1) = table\<close>
    by meson
qed

fun assemble_distinguishing_sequence_from_ofsm_table' :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) list" where
  "assemble_distinguishing_sequence_from_ofsm_table' M q1 q2 0 = []" | 
  "assemble_distinguishing_sequence_from_ofsm_table' M q1 q2 (Suc k) = (case 
      select_diverging_ofsm_table_io' M q1 q2 (Suc k) 
    of
      ((x,y),(Some q1',Some q2')) \<Rightarrow> (x,y) # (assemble_distinguishing_sequence_from_ofsm_table' M q1' q2' k) |
      ((x,y),_)                   \<Rightarrow> [(x,y)])"

lemma assemble_distinguishing_sequence_from_ofsm_table_alt_def :
  assumes "k \<le> size M - 1"
  shows "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k = assemble_distinguishing_sequence_from_ofsm_table' M q1 q2 k"
using assms proof (induction k arbitrary: q1 q2)
  case 0
  show ?case 
    unfolding assemble_distinguishing_sequence_from_ofsm_table.simps
    unfolding assemble_distinguishing_sequence_from_ofsm_table'.simps    
    by presburger
next
  case (Suc k)
  then have "k \<le> FSM.size M - 1"
    by auto
  show ?case 
    unfolding assemble_distinguishing_sequence_from_ofsm_table.simps
    unfolding assemble_distinguishing_sequence_from_ofsm_table'.simps
    unfolding select_diverging_ofsm_table_io_alt_def[OF \<open>Suc k \<le> FSM.size M - 1\<close>]
    unfolding Suc.IH[OF \<open>k \<le> FSM.size M - 1\<close>]
    by meson
qed

fun get_distinguishing_sequence_from_ofsm_tables_refined :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list" where
  "get_distinguishing_sequence_from_ofsm_tables_refined M q1 q2 = (let
      k = find_first_distinct_ofsm_table' M q1 q2
  in assemble_distinguishing_sequence_from_ofsm_table' M q1 q2 k)"

lemma get_distinguishing_sequence_from_ofsm_tables_refined_alt_def :
  "get_distinguishing_sequence_from_ofsm_tables_refined M q1 q2 = get_distinguishing_sequence_from_ofsm_tables M q1 q2"
proof -
  define k where "k = find_first_distinct_ofsm_table' M q1 q2"
  then have "k \<le> size M - 1"
    using find_first_distinct_ofsm_table'_max by metis
  have "find_first_distinct_ofsm_table M q1 q2 = k"
    unfolding k_def find_first_distinct_ofsm_table_alt_def
    by meson
                                                           
  show ?thesis 
    unfolding get_distinguishing_sequence_from_ofsm_tables_refined.simps
    unfolding get_distinguishing_sequence_from_ofsm_tables.simps
    unfolding Let_def
    unfolding k_def[symmetric] \<open>find_first_distinct_ofsm_table M q1 q2 = k\<close>
    unfolding assemble_distinguishing_sequence_from_ofsm_table_alt_def[OF \<open>k \<le> size M - 1\<close>]
    by meson
qed

lemma get_distinguishing_sequence_from_ofsm_tables_refined_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "distinguishes M q1 q2 (get_distinguishing_sequence_from_ofsm_tables_refined M q1 q2)"
  unfolding get_distinguishing_sequence_from_ofsm_tables_refined_alt_def
  using get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms] .



fun select_diverging_ofsm_table_io_with_provided_tables :: "(nat, ('a,'b,'c) ofsm_table) mapping \<Rightarrow> ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) \<times> ('a option \<times> 'a option)" where
  "select_diverging_ofsm_table_io_with_provided_tables tables M q1 q2 k = (let
      ins = inputs_as_list M;
      outs = outputs_as_list M;
      table = ofsm_lookup (the (Mapping.lookup tables (k-1)));
      f = (\<lambda> (x,y) . case (h_obs M q1 x y, h_obs M q2 x y) 
                   of
                      (Some q1', Some q2')  \<Rightarrow> if table q1' \<noteq> table q2'
                                                  then Some ((x,y),(Some q1', Some q2'))
                                                  else None |
                      (None,None)           \<Rightarrow> None |
                      (Some q1', None)      \<Rightarrow> Some ((x,y),(Some q1', None)) |
                      (None, Some q2')      \<Rightarrow> Some ((x,y),(None, Some q2')))
      in 
        hd (List.map_filter f (List.product ins outs)))"

lemma select_diverging_ofsm_table_io_with_provided_tables_simp :
  "select_diverging_ofsm_table_io_with_provided_tables (compute_ofsm_tables M (size M - 1)) M = select_diverging_ofsm_table_io' M"
  unfolding select_diverging_ofsm_table_io_with_provided_tables.simps
            select_diverging_ofsm_table_io'.simps
            Let_def 
  by meson

fun assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables :: "(nat, ('a,'b,'c) ofsm_table) mapping \<Rightarrow> ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) list" where
  "assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables tables M q1 q2 0 = []" | 
  "assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables tables M q1 q2 (Suc k) = (case 
      select_diverging_ofsm_table_io_with_provided_tables tables M q1 q2 (Suc k) 
    of
      ((x,y),(Some q1',Some q2')) \<Rightarrow> (x,y) # (assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables tables M q1' q2' k) |
      ((x,y),_)                   \<Rightarrow> [(x,y)])"

lemma assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables_simp :
  "assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables (compute_ofsm_tables M (size M - 1)) M q1 q2 k= assemble_distinguishing_sequence_from_ofsm_table' M q1 q2 k"
proof (induction k arbitrary: q1 q2)
  case 0
  show ?case
    unfolding assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables.simps
              assemble_distinguishing_sequence_from_ofsm_table'.simps
              Let_def 
    by meson  
next
  case (Suc k')
  show ?case
    unfolding assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables.simps
    unfolding assemble_distinguishing_sequence_from_ofsm_table'.simps
    unfolding Let_def select_diverging_ofsm_table_io_with_provided_tables_simp Suc.IH
    by meson  
qed
  

lemma get_distinguishing_sequence_from_ofsm_tables_refined_code[code] :
  "get_distinguishing_sequence_from_ofsm_tables_refined M q1 q2 = (let
      tables = (compute_ofsm_tables M (size M - 1));
      k = (if (q1 \<in> states M 
                \<and> q2 \<in> states M 
                \<and> (ofsm_lookup (the (Mapping.lookup tables (size M - 1))) q1
                   \<noteq> ofsm_lookup (the (Mapping.lookup tables (size M - 1))) q2))
            then the (find_index (\<lambda> i . ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq> ofsm_lookup (the (Mapping.lookup tables i)) q2) [0..<size M])
            else 0)
  in assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables tables M q1 q2 k)"
  unfolding get_distinguishing_sequence_from_ofsm_tables_refined.simps
            find_first_distinct_ofsm_table'.simps
            Let_def 
            assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables_simp
  by meson

fun get_distinguishing_sequence_from_ofsm_tables_with_provided_tables :: "(nat, ('a,'b,'c) ofsm_table) mapping \<Rightarrow> ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list" where
  "get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2 = (let
      k = (if (q1 \<in> states M 
                \<and> q2 \<in> states M 
                \<and> (ofsm_lookup (the (Mapping.lookup tables (size M - 1))) q1
                   \<noteq> ofsm_lookup (the (Mapping.lookup tables (size M - 1))) q2))
            then the (find_index (\<lambda> i . ofsm_lookup (the (Mapping.lookup tables i)) q1 \<noteq> ofsm_lookup (the (Mapping.lookup tables i)) q2) [0..<size M])
            else 0)
  in assemble_distinguishing_sequence_from_ofsm_table_with_provided_tables tables M q1 q2 k)"

lemma get_distinguishing_sequence_from_ofsm_tables_with_provided_tables_simp :
  "get_distinguishing_sequence_from_ofsm_tables_with_provided_tables (compute_ofsm_tables M (size M - 1)) M = get_distinguishing_sequence_from_ofsm_tables_refined M"
  unfolding get_distinguishing_sequence_from_ofsm_tables_with_provided_tables.simps
            get_distinguishing_sequence_from_ofsm_tables_refined_code
            Let_def
  by meson


lemma get_distinguishing_sequence_from_ofsm_tables_precomputed:
  "get_distinguishing_sequence_from_ofsm_tables M = (let 
      tables = (compute_ofsm_tables M (size M - 1));
      distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                        (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
      distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2)
    in distHelper)"
proof -
  define distStates where "distStates = (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M)))"

  define distMap where distMap_orig: "distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables (compute_ofsm_tables M (size M - 1)) M q1 q2))
                                    distStates)"

  have "distinct distStates"
    unfolding distStates_def using states_as_list_distinct
    using distinct_filter distinct_product by blast 
  then have "distinct (map fst (map (\<lambda>(q1, q2). ((q1, q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2)) distStates))"
    unfolding map_pair_fst_helper .  
  then have distMap_def: "Mapping.lookup distMap = map_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2))
                                          distStates)"
    unfolding distMap_orig get_distinguishing_sequence_from_ofsm_tables_with_provided_tables_simp 
              get_distinguishing_sequence_from_ofsm_tables_refined_alt_def
    using mapping_of_map_of
    by blast     

  define distHelper where "distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2)"

  have "distHelper = get_distinguishing_sequence_from_ofsm_tables M"
  proof -
    have "\<And> q1 q2 . distHelper q1 q2 = get_distinguishing_sequence_from_ofsm_tables M q1 q2"
    proof -
      fix q1 q2
      show "distHelper q1 q2 = get_distinguishing_sequence_from_ofsm_tables M q1 q2" 
      proof (cases "q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2")
        case False
        then show ?thesis 
          unfolding distHelper_def by metis 
      next
        case True
        then have *:"(q1,q2) \<in> list.set distStates"
          using states_as_list_set unfolding distStates_def by fastforce
        
        have "distinct (map fst (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2)) distStates))"
        proof -
          have **: "(map fst (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2)) distStates)) = distStates"
          proof (induction distStates)
            case Nil
            then show ?case by auto
          next
            case (Cons a distStates)
            obtain x y where "a = (x,y)"
              using surjective_pairing by blast
            show ?case 
              using Cons unfolding \<open>a = (x,y)\<close> by auto
          qed

          show ?thesis
            unfolding **
            unfolding distStates_def
            by (simp add: distinct_product) 
        qed

        have "((q1,q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2) \<in> list.set (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2)) distStates)"
          using Util.map_set[OF *, of "(\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2))"]
          by force
        then have "the (Mapping.lookup distMap (q1,q2)) = get_distinguishing_sequence_from_ofsm_tables M q1 q2"
          unfolding distMap_def 
          unfolding Map.map_of_eq_Some_iff[OF \<open>distinct (map fst (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables M q1 q2)) distStates))\<close>, symmetric]
          by (metis option.sel)
        moreover have "distHelper q1 q2 = the (Mapping.lookup distMap (q1,q2))"
          using True unfolding distHelper_def by metis
        ultimately show ?thesis 
          by presburger
      qed
    qed
    then show ?thesis 
      by blast
  qed

  then show ?thesis
    unfolding distHelper_def distMap_orig distStates_def Let_def
    by presburger
qed 


lemma get_distinguishing_sequence_from_ofsm_tables_with_provided_tables_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "distinguishes M q1 q2 (get_distinguishing_sequence_from_ofsm_tables_with_provided_tables (compute_ofsm_tables M (size M - 1)) M q1 q2)"
  unfolding get_distinguishing_sequence_from_ofsm_tables_with_provided_tables_simp
  using get_distinguishing_sequence_from_ofsm_tables_refined_distinguishes[OF assms] .

subsection \<open>Refining Minimisation\<close>

fun minimise_refined :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> ('a set,'b,'c) fsm" where
  "minimise_refined M = (let
      tables = (compute_ofsm_tables M (size M - 1));
      eq_class = (ofsm_lookup (the (Mapping.lookup tables (size M - 1))));
      ts = (\<lambda> t . (eq_class (t_source t), t_input t, t_output t, eq_class (t_target t))) ` (transitions M);
      q0 = eq_class (initial M);
      eq_states = eq_class |`| fstates M;
      M' = create_unconnected_fsm_from_fsets q0 eq_states (finputs M) (foutputs M)
  in add_transitions M' ts)"

lemma minimise_refined_is_minimise[code] : "minimise M = minimise_refined M"
proof -
  define tables where "tables = compute_ofsm_tables M (FSM.size M - 1)"
  define eq_class_refined where "eq_class_refined = (ofsm_lookup (the (Mapping.lookup tables (size M - 1))))"
  define eq_class where "eq_class = ofsm_table_fix M (\<lambda>q . states M) 0"

  have "(size M - 1) < Suc (size M - 1)"
    by auto
  have "\<And> q . q \<in> states M \<Longrightarrow> eq_class q = eq_class_refined q"
    unfolding eq_class_def eq_class_refined_def tables_def
    unfolding compute_ofsm_tables_lookup_invar[OF \<open>(size M - 1) < Suc (size M - 1)\<close>]
    by (metis ofsm_table_fix_partition_fixpoint_trivial_partition)


  have ts: "(\<lambda> t . (eq_class (t_source t), t_input t, t_output t, eq_class (t_target t))) ` (transitions M)
        = (\<lambda> t . (eq_class_refined (t_source t), t_input t, t_output t, eq_class_refined (t_target t))) ` (transitions M)"
    using \<open>\<And> q . q \<in> states M \<Longrightarrow> eq_class q = eq_class_refined q\<close>[OF fsm_transition_source]
    using \<open>\<And> q . q \<in> states M \<Longrightarrow> eq_class q = eq_class_refined q\<close>[OF fsm_transition_target]
    by auto

  have q0: "eq_class (initial M) = eq_class_refined (initial M)"
    using \<open>\<And> q . q \<in> states M \<Longrightarrow> eq_class q = eq_class_refined q\<close>[OF fsm_initial] .

  have eq_states: "eq_class |`| fstates M = eq_class_refined |`| fstates M"
    using fstates_set[of M]
    using \<open>\<And> q . q \<in> states M \<Longrightarrow> eq_class q = eq_class_refined q\<close>
    by (metis fset.map_cong) 

  have M': "create_unconnected_fsm_from_fsets (eq_class (initial M)) (eq_class |`| fstates M) (finputs M) (foutputs M) 
            = create_unconnected_fsm_from_fsets (eq_class_refined (initial M)) (eq_class_refined |`| fstates M) (finputs M) (foutputs M)"
    unfolding q0 eq_states by meson
  
  have res: "add_transitions (create_unconnected_fsm_from_fsets (eq_class (initial M)) (eq_class |`| fstates M) (finputs M) (foutputs M)) ((\<lambda> t . (eq_class (t_source t), t_input t, t_output t, eq_class (t_target t))) ` (transitions M))
              = add_transitions (create_unconnected_fsm_from_fsets (eq_class_refined (initial M)) (eq_class_refined |`| fstates M) (finputs M) (foutputs M)) ((\<lambda> t . (eq_class_refined (t_source t), t_input t, t_output t, eq_class_refined (t_target t))) ` (transitions M))"
    unfolding M' ts by meson

  show ?thesis
    unfolding minimise.simps minimise_refined.simps Let_def
    unfolding eq_class_def[symmetric]
    unfolding tables_def[symmetric] eq_class_refined_def[symmetric]
    unfolding res 
    by meson
qed

end