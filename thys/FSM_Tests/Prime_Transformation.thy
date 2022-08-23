section \<open>Transformation to Language-Equivalent Prime FSMs\<close>

text \<open>This theory describes the transformation of FSMs into language-equivalent FSMs
      that are prime, that is: observable, minimal and initially connected.\<close>

theory Prime_Transformation
imports Minimisation Observability State_Cover OFSM_Tables_Refined "HOL-Library.List_Lexorder" Native_Word.Uint64
begin

subsection \<open>Helper Functions\<close>

text \<open>The following functions transform FSMs whose states are Sets or FSets into
      language-equivalent fsms whose states are lists.
      These steps are required in the chosen implementation of the transformation function, 
      as Sets or FSets are not instances of linorder.\<close>


lemma linorder_fset_list_bij : "bij_betw sorted_list_of_fset xs (sorted_list_of_fset ` xs)"
  unfolding bij_betw_def inj_on_def
  by (metis sorted_list_of_fset_simps(2))

lemma linorder_set_list_bij : 
  assumes "\<And> x . x \<in> xs \<Longrightarrow> finite x"
  shows "bij_betw sorted_list_of_set xs (sorted_list_of_set ` xs)" 
proof -
  have "\<And> x . x \<in> xs \<Longrightarrow> set (sorted_list_of_set x) = x"
    by (simp add: assms)
  then show ?thesis
    unfolding bij_betw_def inj_on_def
    by metis 
qed
  
definition fset_states_to_list_states :: "(('a::linorder) fset,'b,'c) fsm \<Rightarrow> ('a list,'b,'c) fsm" where
  "fset_states_to_list_states M = rename_states M sorted_list_of_fset"

definition set_states_to_list_states :: "(('a::linorder) set,'b,'c) fsm \<Rightarrow> ('a list,'b,'c) fsm" where
  "set_states_to_list_states M = rename_states M sorted_list_of_set"

lemma fset_states_to_list_states_language :
  "L (fset_states_to_list_states M) = L M"
  using rename_states_isomorphism_language[OF linorder_fset_list_bij] 
  unfolding fset_states_to_list_states_def .

lemma set_states_to_list_states_language :
  assumes "\<And> x . x \<in> states M \<Longrightarrow> finite x"
  shows "L (set_states_to_list_states M) = L M"
  using rename_states_isomorphism_language[OF linorder_set_list_bij[OF assms]] 
  unfolding set_states_to_list_states_def .

lemma fset_states_to_list_states_observable :
  assumes "observable M"
  shows "observable (fset_states_to_list_states M)" 
  using rename_states_observable[OF linorder_fset_list_bij assms]
  unfolding fset_states_to_list_states_def .

lemma set_states_to_list_states_observable :
  assumes "\<And> x . x \<in> states M \<Longrightarrow> finite x"
  assumes "observable M"
  shows "observable (set_states_to_list_states M)" 
  using rename_states_observable[OF linorder_set_list_bij[OF assms(1)] assms(2)]
  unfolding set_states_to_list_states_def by blast

lemma fset_states_to_list_states_minimal :
  assumes "minimal M"
  shows "minimal (fset_states_to_list_states M)" 
  using rename_states_minimal[OF linorder_fset_list_bij assms]
  unfolding fset_states_to_list_states_def .

lemma set_states_to_list_states_minimal :
  assumes "\<And> x . x \<in> states M \<Longrightarrow> finite x"
  assumes "minimal M"
  shows "minimal (set_states_to_list_states M)" 
  using rename_states_minimal[OF linorder_set_list_bij[OF assms(1)] assms(2)]
  unfolding set_states_to_list_states_def by blast


subsection \<open>The Transformation Algorithm\<close>
                                            
definition to_prime :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> (integer,'b,'c) fsm" where
  "to_prime M = restrict_to_reachable_states (
                  index_states_integer (
                    set_states_to_list_states (
                      minimise_refined (
                        index_states (
                          fset_states_to_list_states (
                            make_observable (
                              restrict_to_reachable_states M)))))))"

lemma to_prime_props :
  "L (to_prime M) = L M"
  "observable (to_prime M)"
  "minimal (to_prime M)"
  "reachable_states (to_prime M) = states (to_prime M)"
  "inputs (to_prime M) = inputs M"
  "outputs (to_prime M) = outputs M"
proof -

  define M1 where M1: "M1 = restrict_to_reachable_states M"
  define M2 where M2: "M2 = make_observable M1"
  define M3 where M3: "M3 = fset_states_to_list_states M2"
  define M4 where M4: "M4 = index_states M3"
  define M5 where M5: "M5 = minimise_refined M4"
  define M6 where M6: "M6 = set_states_to_list_states M5"
  define M7 where M7: "M7 = index_states_integer M6"
  define M8 where M8: "M8 = restrict_to_reachable_states M7"

  have "to_prime M = M8"
    unfolding M8 M7 M6 M5 M4 M3 M2 M1 to_prime_def by presburger

  have "observable M2"
    unfolding M2 
    using make_observable_language_observable(2) by blast
  then have "observable M3"
    unfolding M3 
    using fset_states_to_list_states_observable by blast
  then have "observable M4"
    unfolding M4
    using index_states_observable by blast
  then have "observable M5"
    unfolding M5
    unfolding minimise_refined_is_minimise[symmetric]
    using minimise_observable by blast
  then have "observable M6"
    unfolding M6 M5
    unfolding minimise_refined_is_minimise[symmetric]
    using minimise_states_finite[OF \<open>observable M4\<close>]
    using set_states_to_list_states_observable
    by metis
  then have "observable M7"
    unfolding M7
    using index_states_integer_observable by blast
  then show "observable (to_prime M)"
    unfolding \<open>to_prime M = M8\<close> M8
    using restrict_to_reachable_states_observable by blast


  have "L M = L M1"
    unfolding M1 restrict_to_reachable_states_language by simp
  also have "\<dots> = L M2"
    unfolding M2 make_observable_language_observable(1) by simp
  also have "\<dots> = L M3"
    unfolding M3 fset_states_to_list_states_language by simp
  also have "\<dots> = L M4"
    unfolding M4 index_states_language by simp
  also have "\<dots> = L M5"
    unfolding M5 unfolding minimise_refined_is_minimise[symmetric]
    using minimise_language[OF \<open>observable M4\<close>] by blast
  also have "\<dots> = L M6"
    unfolding M6 M5 unfolding minimise_refined_is_minimise[symmetric]
    using set_states_to_list_states_language[OF minimise_states_finite[OF \<open>observable M4\<close>]] by blast
  also have "\<dots> = L M7"
    unfolding M7 using index_states_integer_language by blast
  also have "\<dots> = L M8"
    unfolding M8 restrict_to_reachable_states_language by simp
  finally show "L (to_prime M) = L M"
    unfolding \<open>to_prime M = M8\<close> by blast


  have "minimal M5"
    unfolding M5 unfolding minimise_refined_is_minimise[symmetric]
    using minimise_minimal[OF \<open>observable M4\<close>] .
  then have "minimal M6"
    unfolding M6 M5 unfolding minimise_refined_is_minimise[symmetric]
    using set_states_to_list_states_minimal[OF minimise_states_finite[OF \<open>observable M4\<close>]] by blast
  then have "minimal M7"
    unfolding M7 using index_states_integer_minimal by blast
  then show "minimal (to_prime M)"
    unfolding \<open>to_prime M = M8\<close> M8
    using restrict_to_reachable_states_minimal by blast

  show "reachable_states (to_prime M) = states (to_prime M)"
    unfolding \<open>to_prime M = M8\<close> M8 restrict_to_reachable_states_reachable_states by presburger


  have "inputs M = inputs M1"
    unfolding M1 restrict_to_reachable_states_simps by simp
  also have "\<dots> = inputs M2"
    unfolding M2 make_observable_language_observable Let_def add_transitions_simps create_unconnected_fsm_simps by blast
  also have "\<dots> = inputs M3"
    unfolding M3 fset_states_to_list_states_def by simp
  also have "\<dots> = inputs M4"
    unfolding M4 index_states.simps by simp
  also have "\<dots> = inputs M5"
    unfolding M5 unfolding minimise_refined_is_minimise[symmetric]
    using minimise_props[OF \<open>observable M4\<close>] by blast
  also have "\<dots> = inputs M6"
    unfolding M6 M5 set_states_to_list_states_def by simp
  also have "\<dots> = inputs M7"
    unfolding M7 index_states.simps by simp
  also have "\<dots> = inputs M8"
    unfolding M8 restrict_to_reachable_states_simps by simp
  finally show "inputs (to_prime M) = inputs M"
    unfolding \<open>to_prime M = M8\<close> by blast


  have "outputs M = outputs M1"
    unfolding M1 restrict_to_reachable_states_simps by simp
  also have "\<dots> = outputs M2"
    unfolding M2 make_observable_language_observable Let_def add_transitions_simps create_unconnected_fsm_simps by blast
  also have "\<dots> = outputs M3"
    unfolding M3 fset_states_to_list_states_def by simp
  also have "\<dots> = outputs M4"
    unfolding M4 index_states.simps by simp
  also have "\<dots> = outputs M5"
    unfolding M5 unfolding minimise_refined_is_minimise[symmetric]
    using minimise_props[OF \<open>observable M4\<close>] by blast
  also have "\<dots> = outputs M6"
    unfolding M6 M5 set_states_to_list_states_def by simp
  also have "\<dots> = outputs M7"
    unfolding M7 index_states.simps by simp
  also have "\<dots> = outputs M8"
    unfolding M8 restrict_to_reachable_states_simps by simp
  finally show "outputs (to_prime M) = outputs M"
    unfolding \<open>to_prime M = M8\<close> by blast
qed


subsection \<open>Renaming states to Words\<close>


lemma uint64_nat_bij : "(x :: nat) < 2^64 \<Longrightarrow> nat_of_uint64 (uint64_of_nat x) = x"
  by transfer (simp add: unsigned_of_nat take_bit_nat_eq_self)

fun index_states_uint64 :: "('a::linorder,'b,'c) fsm \<Rightarrow> (uint64,'b,'c) fsm" where
  "index_states_uint64 M = rename_states M (uint64_of_nat \<circ> assign_indices (states M))"


lemma assign_indices_uint64_bij_betw : 
  assumes "size M < 2^64" 
  shows "bij_betw (uint64_of_nat \<circ> assign_indices (states M)) (FSM.states M) ((uint64_of_nat \<circ> assign_indices (states M)) ` FSM.states M)"
proof -
  have *: "inj_on (assign_indices (FSM.states M)) (FSM.states M)" 
    using assign_indices_bij[OF fsm_states_finite[of M]]
    unfolding bij_betw_def
    by auto
  moreover have "\<And> q . q \<in> states M \<Longrightarrow> assign_indices (states M) q < 2^64"
    using assms assign_indices_bij[OF fsm_states_finite[of M]]
    unfolding size_def
    by (meson bij_betwE lessThan_iff less_imp_le less_le_trans)
  ultimately have "inj_on (uint64_of_nat \<circ> assign_indices (states M)) (FSM.states M)"
    unfolding inj_on_def
    by (metis comp_apply uint64_nat_bij)
  then show ?thesis
    unfolding bij_betw_def
    by auto
qed


lemma index_states_uint64_language :
  assumes "size M < 2^64"
 shows  "L (index_states_uint64 M) = L M"
  using rename_states_isomorphism_language[of "uint64_of_nat \<circ> assign_indices (states M)" M, OF assign_indices_uint64_bij_betw[OF assms]]
  by auto

lemma index_states_uint64_observable :
  assumes "size M < 2^64" and "observable M"
  shows "observable (index_states_uint64 M)"
  using rename_states_observable[of "uint64_of_nat \<circ> assign_indices (states M)" M, OF assign_indices_uint64_bij_betw[OF assms(1)] assms(2)]
  unfolding index_states_uint64.simps .

lemma index_states_uint64_minimal :
  assumes "size M < 2^64" and "minimal M"
  shows "minimal (index_states_uint64 M)" 
  using rename_states_minimal[of "uint64_of_nat \<circ> assign_indices (states M)" M, OF assign_indices_uint64_bij_betw[OF assms(1)] assms(2)]
  unfolding index_states_uint64.simps .

(* TODO: remove superfluous restriction to reachable states *)
definition to_prime_uint64 :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> (uint64,'b,'c) fsm" where
  "to_prime_uint64 M = restrict_to_reachable_states (index_states_uint64 (to_prime M))"

lemma to_prime_uint64_props :
  assumes "size (to_prime M) < 2^64" 
shows 
  "L (to_prime_uint64 M) = L M"
  "observable (to_prime_uint64 M)"
  "minimal (to_prime_uint64 M)"
  "reachable_states (to_prime_uint64 M) = states (to_prime_uint64 M)"
  "inputs (to_prime_uint64 M) = inputs M"
  "outputs (to_prime_uint64 M) = outputs M"
    using restrict_to_reachable_states_reachable_states[of "index_states_uint64 (to_prime M)"]
    unfolding to_prime_uint64_def
    using index_states_uint64_language[OF assms] 
    unfolding restrict_to_reachable_states_language 
    using restrict_to_reachable_states_observable[OF index_states_uint64_observable[OF assms to_prime_props(2)]]
    using restrict_to_reachable_states_minimal[OF index_states_uint64_minimal[OF assms to_prime_props(3)]]
    unfolding index_states_uint64.simps
    unfolding restrict_to_reachable_states_simps
    unfolding rename_states_simps(3,4)
    unfolding to_prime_props(1,5,6)
    by blast+
 

end 