section \<open>DCFLs are Closed Under Complementation\<close>

theory DPDA_Complement_HU
  imports Det_Pushdown_Automata
begin

subsection \<open>Setup and Auxiliary Lemmas\<close>

context pda begin

definition steps1 :: "'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool" (infix "\<leadsto>+" 55) where
  "steps1 \<equiv> step\<^sub>1 ^++"

abbreviation no_step\<^sub>1 ("(_ \<leadsto>|)" [1000] 999) where
  "cf \<leadsto>| \<equiv> (\<forall>cf'. \<not>cf \<leadsto> cf')"

lemma steps1_induct[consumes 1, case_names base step]:
  assumes "x1 \<leadsto>+ x2"
      and "\<And>q w \<alpha> p u \<gamma>. (q, w, \<alpha>) \<leadsto> (p, u, \<gamma>) \<Longrightarrow> P (q, w, \<alpha>) (p, u, \<gamma>)"
      and "\<And>q w \<alpha> r v \<beta> p u \<gamma>. (q, w, \<alpha>) \<leadsto> (r, v, \<beta>) \<Longrightarrow> (r, v, \<beta>) \<leadsto>+ (p, u, \<gamma>) \<Longrightarrow> 
                P (r, v, \<beta>) (p, u, \<gamma>) \<Longrightarrow> P (q, w, \<alpha>) (p, u, \<gamma>)"
    shows "P x1 x2"
using assms[unfolded steps1_def]
proof(induction rule: converse_tranclp_induct)
  case base thus ?case by (metis prod_cases3)
next
  case step thus ?case by simp (metis prod_cases3 step\<^sub>1.simps)
qed

lemma steps1_converse_induct[consumes 1, case_names base step]:
  assumes "x1 \<leadsto>+ x2"
      and "\<And>q w \<alpha> p u \<gamma>. (q, w, \<alpha>) \<leadsto> (p, u, \<gamma>) \<Longrightarrow> P (q, w, \<alpha>) (p, u, \<gamma>)"
      and "\<And>q w \<alpha> r v \<beta> p u \<gamma>. (q, w, \<alpha>) \<leadsto>+ (r, v, \<beta>) \<Longrightarrow> (r, v, \<beta>) \<leadsto> (p, u, \<gamma>) \<Longrightarrow> 
                P (q, w, \<alpha>) (r, v, \<beta>) \<Longrightarrow> P (q, w, \<alpha>) (p, u, \<gamma>)"
    shows "P x1 x2"
  using assms[unfolded steps1_def]
proof(induction rule: tranclp_induct)
  case base
  then show ?case by (metis prod_cases3)
next
  case (step)
  then show ?case by simp (metis prod_cases3 step\<^sub>1.simps)
qed

lemma steps1_steps:
  "(q, w, \<alpha>) \<leadsto>+ (p, u, \<gamma>) \<Longrightarrow> (q, w, \<alpha>) \<leadsto>* (p, u, \<gamma>)"
  by (simp add: steps_def steps1_def)

lemma steps1_step:
  "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>) \<Longrightarrow> (q, w, \<alpha>) \<leadsto>+ (p, u, \<gamma>)"
  by (simp add: steps1_def tranclp.r_into_trancl)

lemma steps1_trans:
  "(q, w, \<alpha>) \<leadsto>+ (p, u, \<gamma>) \<Longrightarrow> (p, u, \<gamma>) \<leadsto>+ (r, v, \<beta>) \<Longrightarrow> (q, w, \<alpha>) \<leadsto>+ (r, v, \<beta>)"
using steps1_def by force

lemma steps_steps1:
  assumes "(q, w, \<alpha>) \<leadsto>* (p, u, \<gamma>)"
      and "(q, w, \<alpha>) \<noteq> (p, u, \<gamma>)"
    shows "(q, w, \<alpha>) \<leadsto>+ (p, u, \<gamma>)"
using assms unfolding steps_def steps1_def by (meson rtranclpD)

lemma steps1_split_last: "(\<exists>r v \<beta>. (q, w, \<alpha>) \<leadsto>* (r, v, \<beta>) \<and> (r, v, \<beta>) \<leadsto> (p, u, \<gamma>)) 
                                \<longleftrightarrow> (q, w, \<alpha>) \<leadsto>+ (p, u, \<gamma>)"
by (smt (verit, ccfv_threshold) rtranclp_into_tranclp1 step\<^sub>1.elims(2) steps1_def steps_def steps_refl tranclp.simps
      tranclp_into_rtranclp)

lemma split_path:
  assumes "(q, w, \<alpha>) \<leadsto>(n) (p, [], \<gamma>)"
      and "m \<le> n"
    shows "\<exists>r u \<beta>. (q, w, \<alpha>) \<leadsto>(m) (r, u, \<beta>) \<and> (r, u, \<beta>) \<leadsto>(n-m) (p, [], \<gamma>)"
using assms proof (induction "n-m" arbitrary: m)
  case (Suc x)
  from Suc.prems(2) consider (a) "m=n" | (b) "m<n" by linarith
  then show ?case
  proof cases
    case a
    with Suc.prems(1) show ?thesis by auto
  next
    case b
    with Suc.hyps(1)[of "Suc m"] Suc.hyps(2) Suc.prems(1) obtain r u \<beta>
      where p1: "(q, w, \<alpha>) \<leadsto>(Suc m) (r, u, \<beta>)" and p2: "(r, u, \<beta>) \<leadsto>(n - Suc m) (p, [], \<gamma>)" by fastforce
    from p1 obtain s v \<zeta> where *: "(q, w, \<alpha>) \<leadsto>(m) (s, v, \<zeta>)" and s: "(s, v, \<zeta>) \<leadsto> (r, u, \<beta>)"
      using stepn_split_last[of m q w \<alpha> r u \<beta>] by auto
    from s p2 b have **: "(s, v, \<zeta>) \<leadsto>(n - m) (p, [], \<gamma>)"
      using stepn_split_first[of s v \<zeta> "n - Suc m" p "[]" \<gamma>] Suc_diff_Suc by force
    from * ** show ?thesis by blast
  qed
qed auto

end

context dpda begin

lemma max_eps_steps:
  assumes "(q, w, \<alpha>) \<leadsto>(n) (p, u, \<gamma>)"
      and "(p, [], \<gamma>) \<leadsto>|"
      and "(q, w, \<alpha>) \<leadsto>(m) (r, u, \<beta>)"
    shows "m \<le> n"
proof (rule ccontr)
  assume "\<not> m \<le> n"
  then have n_less_m: "Suc n \<le> m" by simp
  from assms(1) obtain v where w_def: "w = v@u"
    using stepn_steps[of q w \<alpha> p u \<gamma>] decreasing_word[of q w \<alpha> p u \<gamma>] by blast
  from assms(3)[unfolded w_def] have p: "(q, v, \<alpha>) \<leadsto>(m) (r, [], \<beta>)"
    using stepn_word_app[of m q v \<alpha> r "[]" \<beta> u] by simp
  obtain s y \<zeta> where *: "(q, v, \<alpha>) \<leadsto>(Suc n) (s, y, \<zeta>)"
    using split_path[OF p n_less_m] by fastforce
  from assms(1)[unfolded w_def] have **: "(q, v, \<alpha>) \<leadsto>(n) (p, [], \<gamma>)" 
    using stepn_word_app[of n q v \<alpha> p "[]" \<gamma> u] by simp
  from * ** have "(p, [], \<gamma>) \<leadsto> (s, y, \<zeta>)"
    using stepn_split_last[of n q v \<alpha> s y \<zeta>] dpda_stepn_det[of n q v \<alpha> p "[]" \<gamma>] by metis
  with assms(2) show False by simp
qed

end

text \<open>In what follows, we show that the complement of a deterministic context-free language is also a 
      deterministic context-free language. For this purpose, we construct a deterministic pushdown automaton 
      that recognizes the complement language of a given deterministic pushdown automaton. The proof 
      follows that of Hopcroft and Ullman \cite{HopcroftU79}. The construction is divided into two parts: First, construct an equivalent 
      deterministic pushdown automaton that scans the entire input for all given input words, and then construct the automaton that recognizes the complement 
      language out of this automaton.\<close>


subsection \<open>Scan Construction\<close>

text \<open>To scan the entire input, we address two complications: ensuring that every configuration has a possible step and that 
      no configuration allows infinite epsilon steps. For the first problem, we introduce a new stack symbol to prevent the 
      stack from becoming empty and a dead state that the automaton moves to when there are no possible steps. For the second 
      problem, we introduce a new final state that the automaton moves to if an infinite number of epsilon steps pass through 
      a final state; otherwise, the automaton moves to the dead state.\<close>


subsubsection \<open>Definition\<close>

datatype 'q st_scan = St 'q | Q0' | D | F
datatype 's sym_scan = Sym 's | X0

lemma inj_Sym: "inj Sym"
  by (simp add: inj_def)

instance st_scan :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = St q} \<union> {Q0', D, F}"
    by auto (metis st_scan.exhaust)
  show "finite (UNIV :: 'a st_scan set)"
    by (simp add: * full_SetCompr_eq)
qed

instance sym_scan :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = Sym q} \<union> {X0}"
    by auto (metis sym_scan.exhaust)
  show "finite (UNIV :: 'a sym_scan set)"
    by (simp add: * full_SetCompr_eq)
qed

locale dpda_scan = dpda M for M :: "('q :: finite, 'a :: finite, 's :: finite) pda" 
begin

definition scan_dpda_final_states :: "'q st_scan set" where
  "scan_dpda_final_states \<equiv> St ` final_states M \<union> {F}"

fun scan_dpda_delta :: "'q st_scan \<Rightarrow> 'a \<Rightarrow> 's sym_scan \<Rightarrow> ('q st_scan \<times> 's sym_scan list) set" where
  "scan_dpda_delta (St q) a (Sym X) = (if \<delta> M q a X = {} \<and> \<delta>\<epsilon> M q X = {} then {(D, [Sym X])} 
                                            else (\<lambda>(q, \<alpha>). (St q, map Sym \<alpha>)) ` \<delta> M q a X)"
| "scan_dpda_delta (St q) _ X0 = {(D, [X0])}"
| "scan_dpda_delta D _ X = {(D, [X])}"
| "scan_dpda_delta _ _ _ = {}"

definition eps_nonfinal :: "'q \<Rightarrow> 's \<Rightarrow> bool" where
  "eps_nonfinal q X \<equiv> (\<forall>i. \<exists>p \<alpha>. (q, [], [X]) \<leadsto>(i) (p, [], \<alpha>) \<and> p \<notin> final_states M)"

definition eps_final :: "'q \<Rightarrow> 's \<Rightarrow> bool" where
  "eps_final q X \<equiv> (\<forall>i. \<exists>p \<alpha>. (q, [], [X]) \<leadsto>(i) (p, [], \<alpha>)) \<and> (\<exists>i p \<alpha>. (q, [], [X]) \<leadsto>(i) (p, [], \<alpha>) \<and> p \<in> final_states M)"

fun scan_dpda_delta_eps :: "'q st_scan \<Rightarrow> 's sym_scan \<Rightarrow> ('q st_scan \<times> 's sym_scan list) set" where
  "scan_dpda_delta_eps Q0' X0 = {(St (init_state M), [Sym (init_symbol M), X0])}"
| "scan_dpda_delta_eps (St q) (Sym X) = (if eps_nonfinal q X then {(D, [Sym X])} else
                                            if eps_final q X then {(F, [Sym X])} else
                                              (\<lambda>(q, \<alpha>). (St q, map Sym \<alpha>)) ` \<delta>\<epsilon> M q X)"
| "scan_dpda_delta_eps F X = {(D, [X])}"
| "scan_dpda_delta_eps _ _ = {}"

definition scan_dpda :: "('q st_scan, 'a, 's sym_scan) pda" where
  "scan_dpda =
  \<lparr> init_state = Q0',
    init_symbol = X0,
    final_states = scan_dpda_final_states, 
    delta = scan_dpda_delta, delta_eps = scan_dpda_delta_eps \<rparr>"


subsubsection \<open>Determinism\<close>

text \<open>The automaton @{const [source] scan_dpda} is deterministic:\<close>
lemma dpda_scan_dpda: "dpda scan_dpda"
proof (standard, goal_cases)
  case (1 p a Z)
  have "finite (scan_dpda_delta p a Z)" 
    by (induction p a Z rule: scan_dpda_delta.induct) (auto simp: finite_delta)
  then show ?case by (simp add: scan_dpda_def)
next
  case (2 p Z)
  have "finite (scan_dpda_delta_eps p Z)"
    by (induction p Z rule: scan_dpda_delta_eps.induct) (auto simp: finite_delta_eps)
  then show ?case by (simp add: scan_dpda_def)
next
  case (3 q a X)
  have "scan_dpda_delta q a X \<noteq> {} \<longrightarrow> scan_dpda_delta_eps q X = {}" 
  proof (induction q a X rule: scan_dpda_delta.induct)
    case (1 q a X)
    then show ?case proof
      assume a: "scan_dpda_delta (St q) a (Sym X) \<noteq> {}"
      have *: "\<delta>\<epsilon> M q X = {}" proof (rule ccontr)
        assume c: "\<delta>\<epsilon> M q X \<noteq> {}"
        from a c have "\<delta> M q a X \<noteq> {}" by simp
        hence "\<delta>\<epsilon> M q X = {}"
          using \<delta>_nonempty[of q a X] by satx
        with c show False by satx
      qed
      hence **: "(q, [], [X]) \<leadsto>|" by simp 
      from ** have ***: "\<not>eps_final q X"
        by (force simp: eps_final_def)
      from ** have ****: "\<not>eps_nonfinal q X"
        by (force simp: eps_nonfinal_def)
      from * *** **** show "scan_dpda_delta_eps (St q) (Sym X) = {}" by simp
    qed
  qed simp_all
  then show ?case by (simp add: scan_dpda_def)
next
  case (4 q a X)
  have "scan_dpda_delta q a X = {} \<or> (\<exists>p \<alpha>. scan_dpda_delta q a X = {(p, \<alpha>)})"
    by (induction q a X rule: scan_dpda_delta.induct, auto) (use \<delta>_singleton in force)+
  then show ?case by (simp add: scan_dpda_def)
next
  case (5 q X)
  have "scan_dpda_delta_eps q X = {} \<or> (\<exists>p \<alpha>. scan_dpda_delta_eps q X = {(p, \<alpha>)})"
    by (induction q X rule: scan_dpda_delta_eps.induct, auto) (use \<delta>\<epsilon>_singleton in force)+
  then show ?case by (simp add: scan_dpda_def)
qed


subsubsection \<open>Equivalence\<close>

sublocale scan: dpda scan_dpda
  using dpda_scan_dpda .

text \<open>We abbreviate the definitions of @{const [source] scan_dpda} with index \<open>s\<close>:\<close>
notation scan.step\<^sub>1 (infix "\<leadsto>\<^sub>s" 55)
notation scan.steps (infix "\<leadsto>\<^sub>s*" 55)
                                                           
abbreviation stack_with_X0 :: "'s list \<Rightarrow> 's sym_scan list" where 
  "stack_with_X0 \<alpha> \<equiv> map Sym \<alpha> @ [X0]"

lemma scan_dpda_first_step:
  assumes "(Q0', w, [X0]) \<leadsto>\<^sub>s (q, u, \<alpha>)"
  shows "q = St (init_state M) \<and> u = w \<and> \<alpha> = [Sym (init_symbol M), X0]"
  using assms scan.step\<^sub>1_rule by (simp add: scan_dpda_def)

lemma scan_dpda_step_from_St:
  assumes "(St q, w, \<alpha>) \<leadsto>\<^sub>s (p, u, \<gamma>)"
  shows "(\<exists>p'. p = St p') \<or> p = F \<or> p = D"
proof -
  from assms obtain X where
  "(\<exists>\<beta>. (p, \<beta>) \<in> scan_dpda_delta_eps (St q) X) \<or> (\<exists>a \<beta>. (p,\<beta>) \<in> scan_dpda_delta (St q) a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule_ext scan_dpda_def by fastforce
  then consider (a) ?a | (b) ?b by blast
  thus ?thesis
  proof cases
    case a
    then show ?thesis by (induction "St q" X rule: scan_dpda_delta_eps.induct) (auto split: if_splits)
  next
    case b
    then obtain a where "\<exists>\<beta>. (p, \<beta>) \<in> scan_dpda_delta (St q) a X" by blast
    then show ?thesis by (induction "St q" a X rule: scan_dpda_delta.induct) (auto split: if_splits)
  qed
qed

lemma scan_dpda_step_from_F:
  assumes "(F, w, \<alpha>) \<leadsto>\<^sub>s (q, u, \<gamma>)"
  shows "q = D"
  using assms scan.step\<^sub>1_rule_ext[of F w \<alpha> q u \<gamma>] scan_dpda_def by auto

lemma scan_dpda_step_to_F:
  assumes "(q, w, X#\<alpha>) \<leadsto>\<^sub>s (F, u, \<gamma>)"
  shows "u = w \<and> (\<exists>q' X'. q = St q' \<and> X = Sym X' \<and> eps_final q' X')"
proof -
  from assms have cases: "(\<exists>\<beta>. u = w \<and> \<gamma> = \<beta> @ \<alpha> \<and> (F, \<beta>) \<in> scan_dpda_delta_eps q X) 
                      \<or> (\<exists>a \<beta>. w = a # u \<and> \<gamma> = \<beta> @ \<alpha> \<and> (F, \<beta>) \<in> scan_dpda_delta q a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule[of q w X \<alpha> F u \<gamma>] scan_dpda_def by simp
  from cases consider (a) ?a | (b) ?b by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis by (induction q X rule: scan_dpda_delta_eps.induct) (auto split: if_splits)
  next
    case b
    then obtain a where "\<exists>\<beta>. w = a # u \<and> \<gamma> = \<beta> @ \<alpha> \<and> (F, \<beta>) \<in> scan_dpda_delta q a X" by blast
    then show ?thesis by (induction q a X rule: scan_dpda_delta.induct) (auto split: if_splits)
  qed
qed

lemma scan_dpda_step_from_D:
  assumes "(D, w, \<alpha>) \<leadsto>\<^sub>s (q, u, \<gamma>)"
  shows "q = D"
using assms scan.step\<^sub>1_rule_ext[of D w \<alpha> q u \<gamma>] scan_dpda_def by auto

lemma scan_dpda_steps_from_St:
  assumes "(St q, w, \<alpha>) \<leadsto>\<^sub>s* (p, u, \<gamma>)"
  shows "(\<exists>p'. p = St p') \<or> p = F \<or> p = D"
using assms by (induction "(St q, w, \<alpha>)" "(p, u, \<gamma>)" arbitrary: p u \<gamma> rule: scan.steps_induct2_bw, simp) 
 (use scan_dpda_step_from_St scan_dpda_step_from_F scan_dpda_step_from_D in blast)

lemma scan_dpda_step_to_St:
  assumes "(q, w, \<alpha>) \<leadsto>\<^sub>s (St p, u, \<gamma>)"
  shows "q = Q0' \<or> (\<exists>q'. q = St q')"
using assms scan_dpda_step_from_F[of w \<alpha> "St p" u \<gamma>] scan_dpda_step_from_D[of w \<alpha> "St p" u \<gamma>]
  by (metis st_scan.exhaust st_scan.simps(5))

lemma scan_dpda_stack_with_X0:
  assumes "(St q, w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (St p, u, \<gamma>)"
  shows "\<exists>\<gamma>'. \<gamma> = stack_with_X0 \<gamma>'"
using assms proof (induction "(St q, w, stack_with_X0 \<alpha>)" "(St p, u, \<gamma>)" arbitrary: p u \<gamma> rule: scan.steps_induct2_bw)
  case (step r u \<gamma> v \<beta>)
  from step(1,2) obtain r' where r_St[simp]: "r = St r'"
    using scan_dpda_steps_from_St[of q w "stack_with_X0 \<alpha>" r u \<gamma>] scan_dpda_step_to_St[of r u \<gamma> p v \<beta>] by blast
  from step(3)[OF r_St] obtain \<gamma>'' where \<gamma>_X0: "\<gamma> = stack_with_X0 \<gamma>''" by blast
  from step(2) obtain X \<gamma>' \<beta>' where \<gamma>_def: "\<gamma> = X#\<gamma>'" and \<beta>_def: "\<beta> = \<beta>' @ \<gamma>'" and
    cases: "(St p, \<beta>') \<in> scan_dpda_delta_eps (St r') X \<or> (\<exists>a. (St p, \<beta>') \<in> scan_dpda_delta (St r') a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule_ext[of r u \<gamma> "St p" v \<beta>] scan_dpda_def by auto
  from cases consider (a) ?a | (b) ?b by blast
  then have X_and_\<beta>'_def: "(\<exists>X'. X = Sym X') \<and> (\<exists>\<beta>''. \<beta>' = map Sym \<beta>'')"
  proof cases
    case a
    then show ?thesis by (induction "St r'" X rule: scan_dpda_delta_eps.induct) (auto split: if_splits)
  next
    case b
    then obtain a where "(St p, \<beta>') \<in> scan_dpda_delta (St r') a X" by blast
    then show ?thesis by (induction "St r'" a X rule: scan_dpda_delta.induct) (auto split: if_splits)
  qed
  from X_and_\<beta>'_def[THEN conjunct1] \<gamma>_X0 \<gamma>_def have "\<exists>\<gamma>'''. \<gamma>' = stack_with_X0 \<gamma>'''"
    by (metis hd_append list.sel(1,3) map_tl sym_scan.distinct(1) tl_append_if)
  with X_and_\<beta>'_def[THEN conjunct2] \<beta>_def show ?case
    by (metis append.assoc map_append)
qed blast

lemma scan_dpda_trans:
  assumes "(St q, map Sym \<alpha>) \<in> \<delta> scan_dpda (St p) a (Sym X)"
  shows "(q, \<alpha>) \<in> \<delta> M p a X"
using assms by (auto simp: scan_dpda_def inj_map_eq_map[OF inj_Sym] split: if_splits)

lemma scan_dpda_eps:
  assumes "(St q, map Sym \<alpha>) \<in> \<delta>\<epsilon> scan_dpda (St p) (Sym X)"
  shows "(q, \<alpha>) \<in> \<delta>\<epsilon> M p X"
using assms by (auto simp: scan_dpda_def inj_map_eq_map[OF inj_Sym] split: if_splits)

lemma scan_dpda_step: 
  assumes "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s (St p, u, map Sym \<gamma>)"
  shows "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>)"
proof -
  from assms obtain X \<alpha>' where \<alpha>Sym_def: "map Sym \<alpha> = Sym X # map Sym \<alpha>'" and rule:
  "(\<exists>\<beta>. u = w \<and> map Sym \<gamma> = \<beta> @ map Sym \<alpha>' \<and> (St p, \<beta>) \<in> \<delta>\<epsilon> scan_dpda (St q) (Sym X)) \<or>
         (\<exists>a \<beta>. w = a # u \<and> map Sym \<gamma> = \<beta> @ map Sym \<alpha>' \<and> (St p, \<beta>) \<in> \<delta> scan_dpda (St q) a (Sym X))"
    using scan.step\<^sub>1_rule_ext[of "St q" w "map Sym \<alpha>" "St p" u "map Sym \<gamma>"] by auto
  from \<alpha>Sym_def have \<alpha>_def: "\<alpha> = X#\<alpha>'"
    using inj_map_eq_map[OF inj_Sym] by auto
  from rule have "(\<exists>\<beta>. u = w \<and> map Sym \<gamma> = map Sym \<beta> @ map Sym \<alpha>' \<and> (St p, map Sym \<beta>) \<in> \<delta>\<epsilon> scan_dpda (St q) (Sym X)) \<or>
         (\<exists>a \<beta>. w = a # u \<and> map Sym \<gamma> = map Sym \<beta> @ map Sym \<alpha>' \<and> (St p, map Sym \<beta>) \<in> \<delta> scan_dpda (St q) a (Sym X))"
    using append_eq_map_conv[where ?f = Sym] by metis
  then have "(\<exists>\<beta>. u = w \<and> \<gamma> = \<beta>@\<alpha>' \<and> (p, \<beta>) \<in> \<delta>\<epsilon> M q X) \<or> (\<exists>a \<beta>. w = a#u \<and> \<gamma> = \<beta>@\<alpha>' \<and> (p, \<beta>) \<in> \<delta> M q a X)"
    using scan_dpda_trans scan_dpda_eps by (metis inj_Sym inj_map_eq_map map_append)
  with \<alpha>_def show ?thesis
    using step\<^sub>1_rule by simp
qed  

lemma scan_dpda_stepX0:
  assumes "(St q, w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s (St p, u, stack_with_X0 \<gamma>)"
  shows "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>)"
proof -
  from assms obtain X \<alpha>' where \<alpha>_def: "stack_with_X0 \<alpha> = X#\<alpha>'" and
    cases: "(\<exists>\<beta>. (St p, \<beta>) \<in> scan_dpda_delta_eps (St q) X) \<or> (\<exists>a \<beta>. (St p, \<beta>) \<in> scan_dpda_delta (St q) a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule_ext[of "St q" w "stack_with_X0 \<alpha>" "St p" u "stack_with_X0 \<gamma>"] scan_dpda_def by force
  from cases consider (a) ?a | (b) ?b by blast
  then have "\<exists>X'. X = Sym X'"
  proof cases
    case a
    then show ?thesis by (induction "St q" X rule: scan_dpda_delta_eps.induct) auto
  next
    case b
    then obtain a where "\<exists>\<beta>. (St p, \<beta>) \<in> scan_dpda_delta (St q) a X" by blast
    then show ?thesis by (induction "St q" a X rule: scan_dpda_delta.induct) auto
  qed
  with \<alpha>_def have "map Sym \<alpha> \<noteq> []" by auto
  then have "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s (St p, u, map Sym \<gamma>)"
    using scan.step\<^sub>1_stack_drop[OF assms] by simp
  then show ?thesis
    using scan_dpda_step by presburger
qed

text \<open>The original automaton can mimic the steps of the automaton @{const [source] scan_dpda} in the old states:\<close>
lemma scan_dpda_stepsX0:
  assumes "(St q, w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (St p, u, stack_with_X0 \<gamma>)"
  shows "(q, w, \<alpha>) \<leadsto>* (p, u, \<gamma>)"
using assms proof (induction "(St q, w, stack_with_X0 \<alpha>)" "(St p, u, stack_with_X0 \<gamma>)" arbitrary: p u \<gamma> rule: scan.steps_induct2_bw)
  case base
  then show ?case
    by (simp add: inj_Sym steps_refl)
next
  case (step r u \<beta> v)
  obtain r' where r_def: "r = St r'"
    using scan_dpda_steps_from_St[OF step(1)] scan_dpda_step_to_St[OF step(2)] by blast
  obtain \<beta>' where \<beta>_def: "\<beta> = stack_with_X0 \<beta>'"
    using scan_dpda_stack_with_X0[OF step(1)[simplified r_def]] by blast
  from step(3)[OF r_def \<beta>_def] have *: "(q, w, \<alpha>) \<leadsto>* (r', u, \<beta>')" .
  have **: "(r', u, \<beta>') \<leadsto> (p, v, \<gamma>)"
    using scan_dpda_stepX0[OF step(2)[simplified r_def \<beta>_def]] .
  show ?case
    using steps_trans[OF * step\<^sub>1_steps[OF **]] .
qed     

text \<open>If a pair of a state and a stack symbol allows infinite epsilon steps then the rest of the stack content stays untouched:\<close>
lemma stack_cycle_drop:    
  assumes "\<forall>i. \<exists>p \<alpha>. (q, [], [X]) \<leadsto>(i) (p, [], \<alpha>)"
      and "(q, [], X#\<gamma>) \<leadsto>* (r, [], \<beta>)"
    shows "\<exists>Y \<beta>'. \<beta> = Y # \<beta>' @ \<gamma> \<and> (q, [], [X]) \<leadsto>* (r, [], Y#\<beta>')"
using assms(2) proof (induction "(q, [] :: 'a list, X#\<gamma>)" "(r, [] :: 'a list, \<beta>)" arbitrary: r \<beta> rule: steps_induct2_bw)  
  case base
  then show ?case  
    by (simp add: steps_refl)
next 
  case (step p w \<alpha> r \<beta>)                 
  have w_def: "w = []"
    using decreasing_word[OF step(1)] by simp
  from step(3)[OF w_def] obtain Y \<beta>' where \<alpha>_def: "\<alpha> = Y # \<beta>' @ \<gamma>" and p1: "(q, [], [X]) \<leadsto>* (p, [], Y # \<beta>')" by blast
  from step(2) \<alpha>_def obtain \<beta>'' where \<beta>_def: "\<beta> = \<beta>'' @ \<beta>' @ \<gamma>"          
    using step\<^sub>1_rule[of p w Y "\<beta>' @ \<gamma>" r "[]" \<beta>] by blast
  from step(2)[unfolded w_def \<alpha>_def \<beta>_def] have p2: "(p, [], Y # \<beta>') \<leadsto> (r, [], \<beta>'' @ \<beta>')" 
    using step\<^sub>1_stack_drop[of p "[]" "Y # \<beta>'" \<gamma> r "[]" "\<beta>'' @ \<beta>'"] by simp 
  have *: "(q, [], [X]) \<leadsto>* (r, [], \<beta>'' @ \<beta>')"             
    using steps_trans[OF p1 step\<^sub>1_steps[OF p2]] .  
  from * obtain n where p3: "(q, [], [X]) \<leadsto>(n) (r, [], \<beta>'' @ \<beta>')"
    using stepn_steps[of q "[]" "[X]" r "[]" "\<beta>'' @ \<beta>'"] by presburger
  from assms(1) obtain s \<zeta> where p4: "(q, [], [X]) \<leadsto>(Suc n) (s, [], \<zeta>)" by presburger
  from p4 have **: "(r, [], \<beta>'' @ \<beta>') \<leadsto> (s, [], \<zeta>)"
    using stepn_split_last[of n q "[]" "[X]" s "[]" \<zeta>] dpda_stepn_det[OF p3] by auto
  from \<beta>_def * show ?case 
    using step\<^sub>1_nonempty_stack[OF **] by auto                                                                                    
qed                                 
                                                                     
text \<open>The automaton @{const [source] scan_dpda} can either mimic the steps of the original automaton or detect a cycle:\<close>
lemma scan_dpda_steps:
  assumes "(q, w, \<alpha>) \<leadsto>* (p, u, \<gamma>)"
  shows "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, u, map Sym \<gamma>) \<or>     
            (\<exists>r X \<beta>. (St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St r, u, Sym X # map Sym \<beta>) \<and> (r, [], X#\<beta>) \<leadsto>* (p, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>(i) (s, [], \<Delta>)))"
using assms proof (induction "(q, w, \<alpha>)" "(p, u, \<gamma>)" arbitrary: p u \<gamma> rule: steps_induct2_bw)
  case base
  then show ?case
    by (simp add: scan.steps_refl)
next
  case (step p u \<gamma> r v \<beta>)
  from step(2) obtain X \<gamma>' where \<gamma>_def: "\<gamma> = X#\<gamma>'" and 
      cases: "(\<exists>\<zeta>. v = u \<and> \<beta> = \<zeta> @ \<gamma>' \<and> (r, \<zeta>) \<in> \<delta>\<epsilon> M p X) \<or> (\<exists>a \<zeta>. u = a # v \<and> \<beta> = \<zeta> @ \<gamma>' \<and> (r, \<zeta>) \<in> \<delta> M p a X)" (is "?a \<or> ?b")
    using step\<^sub>1_rule_ext[of p u \<gamma> r v \<beta>] by blast
  from cases consider (a) ?a | (b) ?b by blast
  then show ?case
  proof cases
    case a    
    then obtain \<zeta> where v_def: "u = v" and \<beta>_def: "\<beta> = \<zeta> @ \<gamma>'" and elem: "(r, \<zeta>) \<in> \<delta>\<epsilon> M p X" by blast 
    from step(3) consider (a1) "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, u, map Sym \<gamma>)" |  
                          (a2) "\<exists>r X \<beta>. (St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St r, u, Sym X # map Sym \<beta>) \<and> (r, [], X # \<beta>) \<leadsto>* (p, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>(i) (s, [], \<Delta>))" by blast
    then show ?thesis
    proof cases    
      case a1   
      consider (a11) "\<forall>i. \<exists>s \<Delta>. (p, [], [X]) \<leadsto>(i) (s, [], \<Delta>)" | (a12) "\<not>(\<forall>i. \<exists>s \<Delta>. (p, [], [X]) \<leadsto>(i) (s, [], \<Delta>))" by blast
      then show ?thesis
      proof cases
        case a11     
        from a1[unfolded v_def \<gamma>_def] have *: "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, v, Sym X # map Sym \<gamma>')" by simp 
        from elem \<beta>_def have **: "(p, [], X # \<gamma>') \<leadsto>* (r, [], \<beta>)"
          using step\<^sub>1_rule[of p "[]" X \<gamma>' r "[]" \<beta>] step\<^sub>1_steps by blast 
        from * ** a11 show ?thesis by blast  
      next                  
        case a12                                                                  
        then have "\<not>eps_nonfinal p X \<and> \<not>eps_final p X"
          by (auto simp: eps_nonfinal_def eps_final_def)
        with elem have "(St r, map Sym \<zeta>) \<in> \<delta>\<epsilon> scan_dpda (St p) (Sym X)"
          by (auto simp: scan_dpda_def)
        with v_def \<gamma>_def \<beta>_def have *: "(St p, u, map Sym \<gamma>) \<leadsto>\<^sub>s (St r, v, map Sym \<beta>)"
          using scan.step\<^sub>1_rule[of "St p" u "Sym X" "map Sym \<gamma>'" "St r" u "map Sym \<zeta> @ map Sym \<gamma>'"] by simp
        show ?thesis
          using scan.steps_trans[OF a1 scan.step\<^sub>1_steps[OF *]] by satx  
      qed               
    next                                               
      case a2         
      then obtain s Y \<mu> where *: "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St s, u, Sym Y # map Sym \<mu>)" and spath: "(s, [], Y # \<mu>) \<leadsto>* (p, [], \<gamma>)"
                          and **: "\<forall>i. \<exists>t \<Delta>. (s, [], [Y]) \<leadsto>(i) (t, [], \<Delta>)" by blast 
      from elem \<gamma>_def \<beta>_def have ***:"(p, [], \<gamma>) \<leadsto> (r, [], \<beta>)"   
        using step\<^sub>1_rule[of p "[]" X \<gamma>' r "[]" \<beta>] by simp  
      have ****: "(s, [], Y # \<mu>) \<leadsto>* (r, [], \<beta>)"
        using steps_trans[OF spath step\<^sub>1_steps[OF ***]] .
      from *[unfolded v_def] ** **** show ?thesis by blast           
    qed                               
  next    
    case b  
    then obtain a \<zeta> where u_def: "u = a#v" and \<beta>_def: "\<beta> = \<zeta> @ \<gamma>'" and elem: "(r, \<zeta>) \<in> \<delta> M p a X" by blast
    from elem have eps_empty: "\<delta>\<epsilon> M p X = {}"               
      using \<delta>_nonempty[of p a X] by blast
    from step(3) consider (t) "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, u, map Sym \<gamma>)" 
      | (f) "\<exists>r X \<beta>. (St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St r, u, Sym X # map Sym \<beta>) \<and> (r, [], X # \<beta>) \<leadsto>* (p, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>(i) (s, [], \<Delta>))" by blast
    then have *: "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, u, map Sym \<gamma>)"         
    proof cases
      case t
      then show ?thesis .
    next
      case f
      then obtain s Y \<mu> where f1: "(s, [], Y # \<mu>) \<leadsto>* (p, [], \<gamma>)" and f2: "\<forall>i. \<exists>s' \<mu>'. (s, [], [Y]) \<leadsto>(i) (s', [], \<mu>')" by blast 
      with \<gamma>_def obtain \<gamma>'' where "(s, [], [Y]) \<leadsto>* (p, [], X#\<gamma>'')"  
        using stack_cycle_drop[OF f2 f1] by blast 
      then obtain n where f3: "(s, [], [Y]) \<leadsto>(n) (p, [], X#\<gamma>'')"
        using stepn_steps[of s "[]" "[Y]" p "[]" "X#\<gamma>''"] by presburger 
      from eps_empty have "(p, [], X#\<gamma>'') \<leadsto>|" by simp
      with f2 f3 max_eps_steps have False by (meson Suc_n_not_le_n)
      then show ?thesis ..          
    qed     
    from eps_empty have "(p, [], [X]) \<leadsto>|" by auto
    then have "\<not>eps_nonfinal p X \<and> \<not>eps_final p X"   
      unfolding eps_nonfinal_def eps_final_def using step\<^sub>1_stepn_one by blast
    with elem have "(St r, map Sym \<zeta>) \<in> \<delta> scan_dpda (St p) a (Sym X)" 
      by (auto simp: scan_dpda_def)
    with u_def \<gamma>_def \<beta>_def have **: "(St p, u, map Sym \<gamma>) \<leadsto>\<^sub>s (St r, v, map Sym \<beta>)"
      using scan.step\<^sub>1_rule[of "St p" u "Sym X" "map Sym \<gamma>'" "St r" v "map Sym \<beta>"] by simp  
    show ?thesis 
      using scan.steps_trans[OF * scan.step\<^sub>1_steps[OF **]] by simp  
  qed                           
qed

text \<open>The language of the automaton @{const [source] scan_dpda} and of the original automaton are the same, i.e. they are equivalent:\<close>
lemma lang_scan_dpda:
"scan.accept_final = accept_final"
proof
  show "scan.accept_final \<subseteq> accept_final"
  proof
    fix w
    assume "w \<in> scan.accept_final"
    then obtain q \<gamma> where q_final: "q \<in> scan_dpda_final_states" and scan_path: "(Q0', w, [X0]) \<leadsto>\<^sub>s* (q, [], \<gamma>)"
      unfolding scan.accept_final_def using scan_dpda_def by auto
    from q_final have cases: "(\<exists>q' \<in> final_states M. q = St q') \<or> q = F" (is "?a \<or> ?b")
      unfolding scan_dpda_final_states_def by auto
    then have "\<exists>p u \<alpha>. (Q0', w, [X0]) \<leadsto>\<^sub>s (p, u, \<alpha>) \<and> (p, u, \<alpha>) \<leadsto>\<^sub>s* (q, [], \<gamma>)"
      using scan.steps_not_refl_split_first[OF scan_path] by blast
    then have p: "(St (init_state M), w, [Sym (init_symbol M), X0]) \<leadsto>\<^sub>s* (q, [], \<gamma>)"
      using scan_dpda_first_step by blast
    from cases consider (a) ?a | (b) ?b by blast
    then show "w \<in> accept_final"
    proof cases
      case a
      then obtain q' where q_def: "q = St q'" and q'_final: "q' \<in> final_states M" by blast
      from p[simplified q_def] obtain \<gamma>' where \<gamma>_def: "\<gamma> = stack_with_X0 \<gamma>'"
        using scan_dpda_stack_with_X0[of "init_state M" w "[init_symbol M]" q' "[]" \<gamma>] by auto
      from p[simplified q_def \<gamma>_def] have "(init_state M, w, [init_symbol M]) \<leadsto>* (q', [], \<gamma>')"
        using scan_dpda_stepsX0[of "init_state M" w "[init_symbol M]" q' "[]" \<gamma>'] by simp
      with q'_final show ?thesis
        unfolding accept_final_def by blast
    next
      case b
      obtain p u \<alpha> where fss: "(St (init_state M), w, [Sym (init_symbol M), X0]) \<leadsto>\<^sub>s* (p, u, \<alpha>)" 
                                          and ls: "(p, u, \<alpha>) \<leadsto>\<^sub>s (F, [], \<gamma>)"
        using scan.steps_not_refl_split_last[OF p[simplified b]] by blast
      obtain X \<alpha>' where \<alpha>_def: "\<alpha> = X#\<alpha>'"
        using scan.step\<^sub>1_nonempty_stack[OF ls] by blast
      obtain p' X' where u_def: "u = []" and p_def: "p = St p'" and X_def: "X = Sym X'" and epath: "eps_final p' X'"
        using scan_dpda_step_to_F[OF ls[simplified \<alpha>_def]] by blast
      from fss[simplified p_def] obtain \<alpha>'' where \<alpha>_with_X0: "\<alpha> = stack_with_X0 \<alpha>''"
        using scan_dpda_stack_with_X0[of "init_state M" w "[init_symbol M]" p' u \<alpha>] by auto
      from fss[simplified p_def u_def \<alpha>_with_X0] have *: "(init_state M, w, [init_symbol M]) \<leadsto>* (p', [], \<alpha>'')"
        using scan_dpda_stepsX0[of "init_state M" w "[init_symbol M]" p' "[]" \<alpha>''] by simp
      from \<alpha>_def \<alpha>_with_X0 X_def obtain \<alpha>''' where \<alpha>''_def: "\<alpha>'' = X'#\<alpha>'''"
        by (metis Nil_is_map_conv append_Cons append_Nil hd_Cons_tl list.map_sel(1) list.sel(1) sym_scan.distinct(1) sym_scan.inject)
      from epath[unfolded eps_final_def] obtain i r \<beta> where path: "(p', [], [X']) \<leadsto>(i) (r, [], \<beta>)" and r_final: "r \<in> final_states M" by blast
      from path have "(p', [], [X']) \<leadsto>* (r, [], \<beta>)"
        using stepn_steps[of p' "[]" "[X']" r "[]" \<beta>] by auto
      with \<alpha>''_def have **: "(p', [], \<alpha>'') \<leadsto>* (r, [], \<beta>@\<alpha>''')"
        using steps_stack_app[of p' "[]" "[X']" r "[]" \<beta> \<alpha>'''] by simp
      from r_final show ?thesis
        unfolding accept_final_def using steps_trans[OF * **] by blast
    qed
  qed
next
  show "accept_final \<subseteq> scan.accept_final"
  proof
    fix w
    assume "w \<in> accept_final"
    then obtain q \<gamma> where q_final: "q \<in> final_states M" and p: "(init_state M, w, [init_symbol M]) \<leadsto>* (q, [], \<gamma>)" 
      unfolding accept_final_def by blast                                                        
    have fs: "(Q0', w, [X0]) \<leadsto>\<^sub>s (St (init_state M), w, [Sym (init_symbol M), X0])"
      using scan_dpda_def scan.step\<^sub>1_rule by auto
    from scan_dpda_steps[OF p] consider (a) "(St (init_state M), w, [Sym (init_symbol M)]) \<leadsto>\<^sub>s* (St q, [], map Sym \<gamma>)"
      | (b) "\<exists>r X \<beta>. (St (init_state M), w, [Sym (init_symbol M)]) \<leadsto>\<^sub>s* (St r, [], Sym X # map Sym \<beta>) \<and>
                                (r, [], X # \<beta>) \<leadsto>* (q, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>(i) (s, [], \<Delta>))" by auto
    then show "w \<in> scan.accept_final"
    proof cases
      case a
      have "(St (init_state M), w, [Sym (init_symbol M), X0]) \<leadsto>\<^sub>s* (St q, [], stack_with_X0 \<gamma>)"
        using scan.steps_stack_app[OF a] by simp
      then have "(Q0', w, [X0]) \<leadsto>\<^sub>s* (St q, [], stack_with_X0 \<gamma>)"
        using scan.step\<^sub>1_steps[OF fs] scan.steps_trans[of Q0' w "[X0]" "St (init_state M)" w "[Sym (init_symbol M), X0]" "St q" "[]" "stack_with_X0 \<gamma>"] by simp 
      with q_final show ?thesis
        unfolding scan.accept_final_def using scan_dpda_def scan_dpda_final_states_def by auto
    next
      case b
      then obtain r X \<beta> where pscan: "(St (init_state M), w, [Sym (init_symbol M)]) \<leadsto>\<^sub>s* (St r, [], Sym X # map Sym \<beta>)" and
        pr: "(r, [], X # \<beta>) \<leadsto>* (q, [], \<gamma>)" and cycle: "\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>(i) (s, [], \<Delta>)" by blast
      have *: "(St (init_state M), w, [Sym (init_symbol M), X0]) \<leadsto>\<^sub>s* (St r, [], stack_with_X0 (X # \<beta>))"
        using scan.steps_stack_app[OF pscan] by simp
      have r_final: "\<exists>\<gamma>'. (r, [], [X]) \<leadsto>* (q, [], \<gamma>')"
        using stack_cycle_drop[OF cycle pr] by auto
      from r_final q_final have e1: "\<not>eps_nonfinal r X"
        unfolding eps_nonfinal_def using stepn_steps[of r "[]" "[X]" q "[]"] dpda_stepn_det[of _ r "[]" "[X]" q "[]"] by blast
      from cycle r_final q_final have e2: "eps_final r X"
        unfolding eps_final_def using stepn_steps[of r "[]" "[X]" q "[]"] by blast
      from e1 e2 have "(St r, [], Sym X # map Sym \<beta>) \<leadsto>\<^sub>s (F, [], Sym X # map Sym \<beta>)"
        using scan_dpda_def scan.step\<^sub>1_rule[of "St r" "[]" "Sym X" "map Sym \<beta>" F "[]" "Sym X # map Sym \<beta>"] by simp
      then have **: "(St r, [], stack_with_X0 (X#\<beta>)) \<leadsto>\<^sub>s (F, [], stack_with_X0 (X#\<beta>))"
        using scan.steps_stack_app[of "St r" "[]" "Sym X # map Sym \<beta>" F "[]" "Sym X # map Sym \<beta>"] by simp
      from fs * ** have "(Q0', w, [X0]) \<leadsto>\<^sub>s* (F, [], stack_with_X0 (X # \<beta>))"
        using scan.step\<^sub>1_steps scan.steps_trans by metis
      then show ?thesis
        unfolding scan.accept_final_def using scan_dpda_def scan_dpda_final_states_def by auto 
    qed
  qed                                               
qed


subsubsection \<open>Scan Property\<close>

lemma D_consumes: "(D, w, X#\<alpha>) \<leadsto>\<^sub>s* (D, [], X#\<alpha>)"
proof (induction w)
  case Nil
  then show ?case
    by (simp add: scan.steps_refl)
next
  case (Cons a w)
  have "(D, [X]) \<in> scan_dpda_delta D a X" by simp
  then have *: "(D, a#w, X#\<alpha>) \<leadsto>\<^sub>s (D, w, X#\<alpha>)"
    using scan.step\<^sub>1_rule[of D "a#w" X \<alpha> D w "X#\<alpha>"] by (simp add: scan_dpda_def)
  show ?case
    using scan.steps_trans[OF scan.step\<^sub>1_steps[OF *] Cons] .
qed

definition eps_inf :: "'q \<Rightarrow> 's \<Rightarrow> bool" where
  "eps_inf q X \<equiv> \<forall>i. \<exists>p \<alpha>. (q, [], [X]) \<leadsto>(i) (p, [], \<alpha>)"

definition eps_infs :: "'q \<Rightarrow> 's list \<Rightarrow> bool" where
  "eps_infs q \<alpha> \<equiv> \<forall>i. \<exists>p \<gamma>. (q, [], \<alpha>) \<leadsto>(i) (p, [], \<gamma>)"

text \<open>If a pair of a state and a stack symbol does not allow infinite epsilon steps, then the stack symbol will be consumed:\<close>
lemma inf_consumes_sym:
  assumes "eps_infs q (X#\<alpha>)"
      and "\<not>eps_inf q X"
    shows "\<exists>p. (q, [], X#\<alpha>) \<leadsto>* (p, [], \<alpha>)"
proof (rule ccontr)
  assume asm: "\<nexists>p. (q, [], X#\<alpha>) \<leadsto>* (p, [], \<alpha>)"
  have "\<exists>p \<gamma>. (q, [], X#\<alpha>) \<leadsto>(i) (p, [], \<gamma>@\<alpha>) \<and> \<gamma> \<noteq> [] \<and> (q, [], [X]) \<leadsto>(i) (p, [], \<gamma>)" for i
  proof (induct i)
    case 0
    have "(q, [], X # \<alpha>) \<leadsto>(0) (q, [], [X] @ \<alpha>) \<and> [X] \<noteq> [] \<and> (q, [], [X]) \<leadsto>(0) (q, [], [X])" by simp
    then show ?case by metis
  next
    case (Suc i)
    then obtain p \<gamma> where p: "(q, [], X # \<alpha>) \<leadsto>(i) (p, [], \<gamma> @ \<alpha>)" and \<gamma>_def: "\<gamma> \<noteq> []" and p1: "(q, [], [X]) \<leadsto>(i) (p, [], \<gamma>)" by blast
    from assms(1)[unfolded eps_infs_def] obtain r \<beta> where *: "(q, [], X#\<alpha>) \<leadsto>(Suc i) (r, [], \<beta>)" by blast
    then have st: "(p, [], \<gamma>@\<alpha>) \<leadsto> (r, [], \<beta>)"
      using stepn_split_last[of i q "[]" "X#\<alpha>" r "[]" \<beta>] dpda_stepn_det[OF p] by auto
    from \<gamma>_def obtain Y \<gamma>' where \<gamma>_def2: "\<gamma> = Y#\<gamma>'"
      using list.exhaust by blast
    from st[unfolded \<gamma>_def2] obtain \<gamma>'' where \<beta>_def: "\<beta> = \<gamma>'' @ \<gamma>' @ \<alpha>"
      using step\<^sub>1_rule[of p "[]" Y "\<gamma>'@\<alpha>" r "[]" \<beta>] by auto
    from *[unfolded \<beta>_def] asm have **: "\<gamma>'' @ \<gamma>' \<noteq> []"
      using stepn_steps[of q "[]" "X#\<alpha>" r "[]" "\<gamma>'' @ \<gamma>' @ \<alpha>"] by force
    from st[unfolded \<beta>_def] \<gamma>_def have st1: "(p, [], \<gamma>) \<leadsto> (r, [], \<gamma>'' @ \<gamma>')"
      using step\<^sub>1_stack_drop[of p "[]" \<gamma> \<alpha> r "[]" "\<gamma>'' @ \<gamma>'"] by simp
    from p1 st1 have ***: "(q, [], [X]) \<leadsto>(Suc i) (r, [], \<gamma>'' @ \<gamma>')" by simp
    from *[unfolded \<beta>_def] ** *** show ?case
      by (metis append.assoc)
  qed
  then have "eps_inf q X"
    by (metis eps_inf_def)
  with assms(2) show False by satx
qed

lemma some_pair_inf:
  assumes "eps_infs q \<alpha>"
      and "\<And>p X \<gamma>. (q, [], \<alpha>) \<leadsto>* (p, [], X#\<gamma>) \<longrightarrow> \<not>eps_inf p X"
    shows False
using assms proof (induction \<alpha> arbitrary: q)
  case Nil
  then show ?case
    by (force simp: eps_infs_def)
next
  case (Cons X \<alpha>)
  from Cons(3)[of q X \<alpha>] have e: "\<not>eps_inf q X"
    by (simp add: steps_refl)
  obtain p where p: "(q, [], X#\<alpha>) \<leadsto>* (p, [], \<alpha>)"
    using inf_consumes_sym[OF Cons(2) e] by blast
  then obtain i where p1: "(q, [], X#\<alpha>) \<leadsto>(i) (p, [], \<alpha>)"
    using stepn_steps[of q "[]" "X#\<alpha>" p "[]" \<alpha>] by blast
  have *: "eps_infs p \<alpha>" unfolding eps_infs_def proof
    fix j
    from Cons(2)[unfolded eps_infs_def] obtain r \<beta> where p2: "(q, [], X#\<alpha>) \<leadsto>(i + j) (r, [], \<beta>)" by blast
    have "(p, [], \<alpha>) \<leadsto>(j) (r, [], \<beta>)"
      using split_path[OF p2, of i] dpda_stepn_det[OF p1] by auto
    then show "\<exists>r \<beta>. (p, [], \<alpha>) \<leadsto>(j) (r, [], \<beta>)" by blast
  qed
  from Cons(3) have **: "\<And>r Y \<gamma>. (p, [], \<alpha>) \<leadsto>* (r, [], Y # \<gamma>) \<longrightarrow> \<not> eps_inf r Y"
    using steps_trans[OF p] by blast
  from Cons(1)[OF * **] show ?case .
qed

text \<open>If a configuration allows infinite epsilon steps, it will eventually reach a pair of a 
      state and a stack symbol that allows infinite epsilon steps:\<close>
lemma inf_reaches:
  assumes "eps_infs q \<alpha>"
  shows "\<exists>p X \<gamma>. (q, [], \<alpha>) \<leadsto>* (p, [], X#\<gamma>) \<and> eps_inf p X"
using assms some_pair_inf by blast

lemma eps_inf_to_D:
  assumes "eps_inf q X"
  shows "(St q, w, Sym X # \<alpha>) \<leadsto>\<^sub>s* (D, [], Sym X # \<alpha>)"
proof -
  from assms consider (a) "eps_nonfinal q X" | (b) "\<not>eps_nonfinal q X \<and> eps_final q X"
    unfolding eps_inf_def eps_nonfinal_def eps_final_def by blast
  then show ?thesis proof cases
    case a
    then have "(D, [Sym X]) \<in> scan_dpda_delta_eps (St q) (Sym X)" by simp
    then have st: "(St q, w, Sym X # \<alpha>) \<leadsto>\<^sub>s (D, w, Sym X # \<alpha>)"
      using scan.step\<^sub>1_rule[of "St q" w "Sym X" \<alpha> D w "Sym X # \<alpha>"] by (simp add: scan_dpda_def)
    show ?thesis
      using scan.steps_trans[OF scan.step\<^sub>1_steps[OF st] D_consumes] .
  next
    case b
    then have "(F, [Sym X]) \<in> scan_dpda_delta_eps (St q) (Sym X)" by simp
    then have st1: "(St q, w, Sym X # \<alpha>) \<leadsto>\<^sub>s (F, w, Sym X # \<alpha>)"
      using scan.step\<^sub>1_rule[of "St q" w "Sym X" \<alpha> F w "Sym X # \<alpha>"] by (simp add: scan_dpda_def)
    have "(D, [Sym X]) \<in> scan_dpda_delta_eps F (Sym X)" by simp
    then have st2: "(F, w, Sym X # \<alpha>) \<leadsto>\<^sub>s (D, w, Sym X # \<alpha>)"
      using scan.step\<^sub>1_rule[of F w  "Sym X" \<alpha> D w "Sym X # \<alpha>"] by (simp add: scan_dpda_def)
    show ?thesis
      using scan.steps_trans[OF scan.step\<^sub>1_steps[OF st1] scan.steps_trans[OF scan.step\<^sub>1_steps[OF st2] D_consumes]] .
  qed
qed

lemma scan_dpda_eps_inf:
  assumes "(q, w, \<alpha>) \<leadsto>* (p, w, X#\<gamma>)"
      and "eps_inf p X"
    shows "\<exists>Y \<beta>. (St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (D, [], Sym Y # \<beta>)"
proof -
  consider (a) "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, w, Sym X # map Sym \<gamma>)" |
           (b) "\<exists>r Y \<beta>. (St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St r, w, Sym Y # map Sym \<beta>) \<and> (\<forall>i. \<exists>s \<zeta>. (r, [], [Y]) \<leadsto>(i) (s, [], \<zeta>))"
    using scan_dpda_steps[OF assms(1)] by auto
  then show ?thesis proof cases
    case a
    have *: "(St p, w, Sym X # map Sym \<gamma>) \<leadsto>\<^sub>s* (D, [], Sym X # map Sym \<gamma>)"
      using eps_inf_to_D[OF assms(2)] by simp
    show ?thesis
      using scan.steps_trans[OF a *] by blast
  next
    case b
    then obtain r Y \<beta> where p: "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St r, w, Sym Y # map Sym \<beta>)" and r_inf: "\<forall>i. \<exists>s \<zeta>. (r, [], [Y]) \<leadsto>(i) (s, [], \<zeta>)" by blast
    from r_inf have r_eps_inf: "eps_inf r Y"
      by (simp add: eps_inf_def)
    have *: "(St r, w, Sym Y # map Sym \<beta>) \<leadsto>\<^sub>s* (D, [], Sym Y # map Sym \<beta>)"
      using eps_inf_to_D[OF r_eps_inf] by simp
    show ?thesis
      using scan.steps_trans[OF p *] by blast
  qed
qed

lemma scan_dpda_neps_infs:
  assumes "\<not>eps_infs q \<alpha>"
  shows "\<exists>p \<gamma>. (St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, w, map Sym \<gamma>) \<and> (\<forall>X \<gamma>'. \<gamma> = X#\<gamma>' \<longrightarrow> \<delta>\<epsilon> M p X = {})"
proof -
  from assms[unfolded eps_infs_def] obtain i where "\<forall>p \<gamma>. \<not>(q, [], \<alpha>) \<leadsto>(i) (p, [], \<gamma>)" by blast
  then have "\<exists>j p \<gamma>. j < i \<and> (q, [], \<alpha>) \<leadsto>(j) (p, [], \<gamma>) \<and> (p, [], \<gamma>) \<leadsto>|" proof (induction i)
    case 0
    then show ?case
      by (auto simp: steps_refl)
  next
    case (Suc i)
    consider (a) "\<forall>p \<gamma>. \<not> (q, [], \<alpha>) \<leadsto>(i) (p, [], \<gamma>)" | (b) "\<exists>p \<gamma>. (q, [], \<alpha>) \<leadsto>(i) (p, [], \<gamma>)" by blast
    then show ?case proof cases
      case a
      from Suc(1)[OF a] show ?thesis
        by (auto simp: less_Suc_eq)
    next
      case b
      then obtain p \<gamma> where *: "(q, [], \<alpha>) \<leadsto>(i) (p, [], \<gamma>)" by blast
      with Suc(2) have **: "(p, [], \<gamma>) \<leadsto>|"
        using decreasing_word step\<^sub>1_steps by fastforce
      from * ** show ?thesis by blast
    qed
  qed
  then obtain j p \<gamma> where "j < i" and p: "(q, [], \<alpha>) \<leadsto>(j) (p, [], \<gamma>)" and nst: "(p, [], \<gamma>) \<leadsto>|" by blast
  from p have p1: "(q, [], \<alpha>) \<leadsto>* (p, [], \<gamma>)"
    using stepn_steps[of q "[]" \<alpha> p "[]" \<gamma>] by auto
  consider (a) "(St q, [], map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, [], map Sym \<gamma>)" |
           (b) "\<exists>r X \<beta>. (St q, [], map Sym \<alpha>) \<leadsto>\<^sub>s* (St r, [], Sym X # map Sym \<beta>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>(i) (s, [], \<Delta>))"
    using scan_dpda_steps[OF p1] by blast
  then show ?thesis proof cases
    case a
    then have *: "(St q, w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, w, map Sym \<gamma>)"
      using scan.steps_word_app[of "St q" "[]" "map Sym \<alpha>" "St p" "[]" "map Sym \<gamma>" w] by simp
    from nst have **: "\<forall>X \<gamma>'. \<gamma> = X # \<gamma>' \<longrightarrow> \<delta>\<epsilon> M p X = {}" by auto
    from * ** show ?thesis by blast
  next
    case b
    then obtain r X \<beta> where p2: "(St q, [], map Sym \<alpha>) \<leadsto>\<^sub>s* (St r, [], Sym X # map Sym \<beta>)" and cycle: "\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>(i) (s, [], \<Delta>)" by blast
    from p2 have p3: "(St q, [], stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (St r, [], stack_with_X0 (X#\<beta>))"
      using scan.steps_stack_app[where ?\<beta> = "[X0]"] by fastforce
    have "(q, [], \<alpha>) \<leadsto>* (r, [], X#\<beta>)"
      using scan_dpda_stepsX0[OF p3] .
    then obtain n where p4: "(q, [], \<alpha>) \<leadsto>(n) (r, [], X#\<beta>)"
      using stepn_steps[of q "[]" \<alpha> r "[]" "X#\<beta>"] by blast
    have "\<forall>k. \<exists>s \<Delta>. (q, [], \<alpha>) \<leadsto>(k) (s, [], \<Delta>)" proof
      fix k
      show "\<exists>s \<Delta>. (q, [], \<alpha>) \<leadsto>(k) (s, [], \<Delta>)" proof (cases "k < n")
        case True
        then have k_leq: "k \<le> n" by simp
        then obtain s u \<zeta> where *: "(q, [], \<alpha>) \<leadsto>(k) (s, u, \<zeta>)"
          using split_path[OF p4 k_leq] by blast
        from * have u_def: "u = []"
          using stepn_steps[of q "[]" \<alpha> s u \<zeta>] decreasing_word[of q "[]" \<alpha> s u \<zeta>] by auto
        from *[unfolded u_def] show ?thesis by blast
      next
        case False
        then have k_beq: "k \<ge> n" by simp
        with cycle obtain s \<zeta> where "(r, [], [X]) \<leadsto>(k-n) (s, [], \<zeta>)" by presburger
        then have p5: "(r, [], X#\<beta>) \<leadsto>(k-n) (s, [], \<zeta>@\<beta>)"
          using stepn_stack_app[where ?\<beta> = \<beta>] by fastforce
        from k_beq show ?thesis
          using stepn_trans[OF p4 p5] by auto 
      qed
    qed
    with assms show ?thesis
      by (simp add: eps_infs_def)
  qed
qed

lemma scan_dpda_scans_St:
"\<exists>p X \<gamma>. (St q, w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (p, [], X#\<gamma>) \<and> \<delta> scan_dpda p a X \<noteq> {}"
proof (induction w arbitrary: q \<alpha>)
  case Nil
  then show ?case proof (cases "eps_infs q \<alpha>")
    case True
    obtain p X \<gamma> where p: "(q, [], \<alpha>) \<leadsto>* (p, [], X#\<gamma>)" and eps_p: "eps_inf p X"
      using inf_reaches[OF True] by blast
    obtain Y \<beta> where "(St q, [], map Sym \<alpha>) \<leadsto>\<^sub>s* (D, [], Sym Y # \<beta>)"
      using scan_dpda_eps_inf[OF p eps_p] by blast
    then have *: "(St q, [], stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (D, [], Sym Y # \<beta> @ [X0])"
      using scan.steps_stack_app[where ?\<beta> = "[X0]"] by fastforce
    have **: "\<delta> scan_dpda D a (Sym Y) \<noteq> {}"
      by (simp add: scan_dpda_def)
    from * ** show ?thesis by blast
  next
    case False
    obtain p \<gamma> where p: "(St q, [], map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, [], map Sym \<gamma>)" and \<gamma>_nempty: "(\<forall>X \<gamma>'. \<gamma> = X#\<gamma>' \<longrightarrow> \<delta>\<epsilon> M p X = {})"
      using scan_dpda_neps_infs[OF False] by blast
    from p have p1: "(St q, [], stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (St p, [], stack_with_X0 \<gamma>)"
      using scan.steps_stack_app[where ?\<beta> = "[X0]"] by simp
    show ?thesis proof (cases \<gamma>)
      case Nil
      with p1 show ?thesis
        by (force simp: scan_dpda_def)
    next
      case (Cons X \<gamma>')
      with \<gamma>_nempty have "\<delta>\<epsilon> M p X = {}" by simp
      then have "\<delta> scan_dpda (St p) a (Sym X) \<noteq> {}"
        by (simp add: scan_dpda_def)
      with p1 Cons show ?thesis by auto
    qed
  qed
next
  case IH: (Cons b w)
  show ?case proof (cases "eps_infs q \<alpha>")
    case True
    obtain p X \<gamma> where p: "(q, [], \<alpha>) \<leadsto>* (p, [], X#\<gamma>)" and eps_p: "eps_inf p X"
      using inf_reaches[OF True] by blast
    from p have p1: "(q, b#w, \<alpha>) \<leadsto>* (p, b#w, X#\<gamma>)"
      using steps_word_app[of q "[]" \<alpha> p "[]" "X#\<gamma>" "b#w"] by simp
    obtain Y \<beta> where "(St q, b # w, map Sym \<alpha>) \<leadsto>\<^sub>s* (D, [], Sym Y # \<beta>)"
      using scan_dpda_eps_inf[OF p1 eps_p] by blast
    then have *: "(St q, b # w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (D, [], Sym Y # \<beta> @ [X0])"
      using scan.steps_stack_app[where ?\<beta> = "[X0]"] by fastforce
    have **: "\<delta> scan_dpda D a (Sym Y) \<noteq> {}"
      by (simp add: scan_dpda_def)
    from * ** show ?thesis by blast
  next
    case False
    obtain p \<gamma> where p: "(St q, b#w, map Sym \<alpha>) \<leadsto>\<^sub>s* (St p, b#w, map Sym \<gamma>)" and \<gamma>_nempty: "(\<forall>X \<gamma>'. \<gamma> = X#\<gamma>' \<longrightarrow> \<delta>\<epsilon> M p X = {})"
      using scan_dpda_neps_infs[OF False] by blast
    from p have p1: "(St q, b#w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (St p, b#w, stack_with_X0 \<gamma>)"
      using scan.steps_stack_app[where ?\<beta> = "[X0]"] by simp
    show ?thesis proof (cases \<gamma>)
      case Nil
      have "(D, [X0]) \<in> scan_dpda_delta (St p) b X0" by simp
      with Nil have st: "(St p, b#w, stack_with_X0 \<gamma>) \<leadsto>\<^sub>s (D, w, [X0])"
        using scan.step\<^sub>1_rule[of "St p" "b#w" X0 "[]" D w "[X0]"] by (simp add: scan_dpda_def)
      have *: "(St q, b#w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (D, [], [X0])"
        using scan.steps_trans[OF p1 scan.steps_trans[OF scan.step\<^sub>1_steps[OF st] D_consumes]] .
      have **: "\<delta> scan_dpda D a X0 \<noteq> {}"
        by (simp add: scan_dpda_def)
      from * ** show ?thesis by blast
    next
      case (Cons X \<gamma>')
      with \<gamma>_nempty have "\<delta>\<epsilon> M p X = {}" by simp
      then consider (a) "(D, [Sym X]) \<in> scan_dpda_delta (St p) b (Sym X)" | (b) "\<exists>r \<beta>. (St r, map Sym \<beta>) \<in> scan_dpda_delta (St p) b (Sym X)"
        by (cases "\<delta> M p b X = {}") fastforce+
      then show ?thesis proof cases
        case a
        with Cons have st: "(St p, b#w, stack_with_X0 \<gamma>) \<leadsto>\<^sub>s (D, w, stack_with_X0 \<gamma>)"
          using scan.step\<^sub>1_rule[of "St p" "b#w" "Sym X" "stack_with_X0 \<gamma>'" D w "stack_with_X0 \<gamma>"] by (simp add: scan_dpda_def)
        from Cons have *: "(St q, b#w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (D, [], stack_with_X0 \<gamma>)"
          using scan.steps_trans[OF p1 scan.steps_trans[OF scan.step\<^sub>1_steps[OF st]]] D_consumes[of w "Sym X" "stack_with_X0 \<gamma>'"] by simp
        have **: "\<delta> scan_dpda D a (Sym X) \<noteq> {}"
          by (simp add: scan_dpda_def)
        from * ** Cons show ?thesis by auto
      next
        case b
        then obtain r \<beta> where "(St r, map Sym \<beta>) \<in> scan_dpda_delta (St p) b (Sym X)" by blast
        with Cons have st: "(St p, b#w, stack_with_X0 \<gamma>) \<leadsto>\<^sub>s (St r, w, stack_with_X0 (\<beta>@\<gamma>'))"
          using scan.step\<^sub>1_rule[of "St p" "b#w" "Sym X" "stack_with_X0 \<gamma>'" "St r" w "stack_with_X0 (\<beta>@\<gamma>')"] by (simp add: scan_dpda_def)
        from IH have *: "\<exists>p X \<gamma>. (St r, w, stack_with_X0 (\<beta>@\<gamma>')) \<leadsto>\<^sub>s* (p, [], X # \<gamma>) \<and> \<delta> scan_dpda p a X \<noteq> {}" by presburger
        from * show ?thesis
          using scan.steps_trans[OF scan.steps_trans[OF p1 scan.step\<^sub>1_steps[OF st]]] by blast
      qed
    qed
  qed
qed

text \<open>For every input word, the automaton @{const [source] scan_dpda} scans the entire input and, moreover, 
      ends in a configuration where no epsilon step is possible:\<close>
lemma scan_dpda_scans:
"\<exists>q X \<alpha>. (init_state scan_dpda, w, [init_symbol scan_dpda]) \<leadsto>\<^sub>s* (q, [], X#\<alpha>) \<and> \<delta> scan_dpda q a X \<noteq> {}"
proof -
  have "(St (init_state M), stack_with_X0 [init_symbol M]) \<in> scan_dpda_delta_eps Q0' X0" by simp
  then have *: "(init_state scan_dpda, w, [init_symbol scan_dpda]) \<leadsto>\<^sub>s (St (init_state M), w, stack_with_X0 [init_symbol M])"
    using scan.step\<^sub>1_rule[of Q0' w X0 "[]" "St (init_state M)" w "stack_with_X0 [init_symbol M]"] by (simp add: scan_dpda_def)
  obtain p X \<gamma> where **: "(St (init_state M), w, stack_with_X0 [init_symbol M]) \<leadsto>\<^sub>s* (p, [], X#\<gamma>)" and d: "\<delta> scan_dpda p a X \<noteq> {}"
    using scan_dpda_scans_St[of "init_state M" w "[init_symbol M]"] by blast
  have "(init_state scan_dpda, w, [init_symbol scan_dpda]) \<leadsto>\<^sub>s* (p, [], X#\<gamma>)"
    using scan.steps_trans[OF scan.step\<^sub>1_steps[OF *] **] .
  with d show ?thesis by blast
qed

end


subsection \<open>Complement Construction\<close>

text \<open>After ensuring that the automaton scans its entire input word, we are left with constructing the deterministic 
      pushdown automaton that recognizes the complement language. The main idea is to keep track of whether a final 
      state has been visited since the last true step using a second component for states. If no final state has been 
      visited, the complement automaton enters a final state of its own just before the next true step.\<close>


subsubsection \<open>Definition\<close>

text \<open>An S1-state indicates that a final state has been visited since the last true step, whereas an S2-state indicates 
      that no final state has been visited since the last true step. S3-states are the final states of the complement automaton:\<close>
datatype 'q s123 = S1 'q | S2 'q | S3 'q

instance s123 :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = S1 q} \<union> {t. \<exists>q. t = S2 q} \<union> {t. \<exists>q. t = S3 q}"
    by auto (metis s123.exhaust)
  show "finite (UNIV :: 'a s123 set)"
    by (simp add: * full_SetCompr_eq)
qed

lemma inj_S1: "inj S1"
  by (simp add: inj_def)

lemma inj_S2: "inj S2"
  by (simp add: inj_def)

text \<open>We can now assume the scan property proved in the last subsection:\<close>
locale complement_dpda = dpda M for M :: "('q :: finite, 'a :: finite, 's :: finite) pda" +
  assumes M_path: "\<exists>q X \<alpha>. (init_state M, w, [init_symbol M]) \<leadsto>* (q, [], X#\<alpha>) \<and> \<delta> M q a X \<noteq> {}"
begin

definition comp_dpda_init_state :: "'q s123" where
  "comp_dpda_init_state \<equiv> if init_state M \<in> final_states M then S1 (init_state M) else S2 (init_state M)"

definition comp_dpda_final_states :: "'q s123 set" where
  "comp_dpda_final_states \<equiv> range S3"

fun comp_dpda_delta :: "'q s123 \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('q s123 \<times> 's list) set" where
  "comp_dpda_delta (S1 q) a X = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` \<delta> M q a X"
| "comp_dpda_delta (S3 q) a X = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` \<delta> M q a X"
| "comp_dpda_delta _ _ _ = {}"

fun comp_dpda_delta_eps :: "'q s123 \<Rightarrow> 's \<Rightarrow> ('q s123 \<times> 's list) set" where
  "comp_dpda_delta_eps (S1 q) X = (\<lambda>(p, \<alpha>). (S1 p, \<alpha>)) ` \<delta>\<epsilon> M q X"
| "comp_dpda_delta_eps (S2 q) X = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` \<delta>\<epsilon> M q X 
                                    \<union> (if \<exists>a. \<delta> M q a X \<noteq> {} then {(S3 q, [X])} else {})"
| "comp_dpda_delta_eps _ _ = {}"

definition comp_dpda :: "('q s123, 'a, 's) pda" where
  "comp_dpda =
  \<lparr> init_state = comp_dpda_init_state,
    init_symbol = init_symbol M,
    final_states = comp_dpda_final_states,
    delta = comp_dpda_delta, delta_eps = comp_dpda_delta_eps \<rparr>"


subsubsection \<open>Determinism\<close>

lemma image_singleton_if_inj:
  assumes "inj f"
  shows "(\<exists>x. A = {x}) \<longleftrightarrow> (\<exists>x. f ` A = {x})"
using assms by (metis image_empty image_insert image_inv_f_f)

text \<open>The automaton @{const [source] comp_dpda} is deterministic:\<close>
lemma dpda_comp_dpda: "dpda comp_dpda"
proof (standard, goal_cases)
  case (1 p a Z)
  have "finite (comp_dpda_delta p a Z)"
    by (induction p a Z rule: comp_dpda_delta.induct) (auto simp: finite_delta)
  then show ?case
    by (simp add: comp_dpda_def)
next
  case (2 p Z)
  have "finite (comp_dpda_delta_eps p Z)"
    by (induction p Z rule: comp_dpda_delta_eps.induct) (auto simp: finite_delta_eps)
  then show ?case
    by (simp add: comp_dpda_def)
next
  case (3 q a X)
  then show ?case
  proof
    assume "\<delta> comp_dpda q a X \<noteq> {}"
    then have "comp_dpda_delta q a X \<noteq> {}"
      by (simp add: comp_dpda_def)
    then have "comp_dpda_delta_eps q X = {}"
      by (induction q a X rule: comp_dpda_delta.induct) (auto simp: \<delta>_nonempty)
    then show "\<delta>\<epsilon> comp_dpda q X = {}"
      by (simp add: comp_dpda_def)
  qed
next
  case (4 q a X)
  let ?f = "(\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>))"
  have *: "inj ?f"
    by (simp add: inj_def)
  have "comp_dpda_delta q a X = {} \<or> (\<exists>p \<gamma>. comp_dpda_delta q a X = {(p, \<gamma>)})"
  proof (induction q a X rule: comp_dpda_delta.induct)
    case (1 q a X)
    then show ?case
      using \<delta>_singleton[of q a X] image_singleton_if_inj[OF *, of "\<delta> M q a X"] by simp 
  next
    case (2 q a X)
    then show ?case 
      using \<delta>_singleton[of q a X] image_singleton_if_inj[OF *, of "\<delta> M q a X"] by simp 
  qed simp
  then show ?case
    by (simp add: comp_dpda_def)
next
  case (5 q X)
  have "comp_dpda_delta_eps q X = {} \<or> (\<exists>p \<gamma>. comp_dpda_delta_eps q X = {(p, \<gamma>)})"
  proof (induction q X rule: comp_dpda_delta_eps.induct)
    case (1 q X)
    then show ?case
      using \<delta>\<epsilon>_singleton[of q X] by auto
  next
    case (2 q X)
    consider (a) "\<exists>a. \<delta> M q a X \<noteq> {}" | (b) "\<not>(\<exists>a. \<delta> M q a X \<noteq> {})" by blast
    then show ?case
    proof cases
      case a
      then have "\<delta>\<epsilon> M q X = {}"
        using \<delta>_nonempty[of q _ X] by blast
      then show ?thesis by simp
    next
      case b
      let ?f = "(\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>))"
      have *: "inj ?f"
        by (simp add: inj_def)
      from b show ?thesis
        using \<delta>\<epsilon>_singleton[of q X] image_singleton_if_inj[OF *, of "\<delta>\<epsilon> M q X"] by simp
    qed
  qed simp
  then show ?case
    by (simp add: comp_dpda_def)
qed


subsubsection \<open>Complementation\<close>

sublocale comp: dpda comp_dpda
  using dpda_comp_dpda . 

text \<open>We abbreviate the definitions of @{const [source] comp_dpda} with index \<open>c\<close>:\<close>
notation comp.step\<^sub>1 (infix "\<leadsto>\<^sub>c" 55)
notation comp.steps (infix "\<leadsto>\<^sub>c*" 55)
notation comp.stepsn ("(_ /\<leadsto>\<^sub>c'(_')/ _)" [55, 0, 55] 55)
notation comp.steps1 (infix "\<leadsto>\<^sub>c+" 55)

lemma comp_dpda_step_from_S1:
  assumes "(S1 q, [], \<alpha>) \<leadsto>\<^sub>c (p, [], \<gamma>)"
  shows "\<exists>p'. p = S1 p'"
using assms comp.step\<^sub>1_rule_ext[of "S1 q" "[]" \<alpha> p "[]" \<gamma>] by (auto simp: comp_dpda_def)

lemma comp_dpda_steps_from_S1:
  assumes "(S1 q, [], \<alpha>) \<leadsto>\<^sub>c* (p, [], \<gamma>)"
  shows "\<exists>p'. p = S1 p'"
using assms comp_dpda_step_from_S1 comp.decreasing_word 
  by (induction "(S1 q, [] :: 'a list, \<alpha>)" "(p, [] :: 'a list, \<gamma>)" arbitrary: p \<gamma> rule: comp.steps_induct2_bw) fastforce+

lemma comp_dpda_nonfinal_stepsS2:
  assumes "(q, [], \<alpha>) \<leadsto>* (p, [], \<gamma>)"
      and "\<And>r \<beta>. (q, [], \<alpha>) \<leadsto>* (r, [], \<beta>) \<longrightarrow> r \<notin> final_states M"
    shows "(S2 q, [], \<alpha>) \<leadsto>\<^sub>c* (S2 p, [], \<gamma>)"
using assms proof (induction "(q, [] :: 'a list, \<alpha>)" "(p, [] :: 'a list, \<gamma>)" arbitrary: q \<alpha> rule: steps_induct2)
  case 1
  then show ?case
    by (simp add: comp.steps_refl)
next
  case (2 q \<alpha> r u \<beta>)
  from 2(1) obtain X \<alpha>' \<zeta> where \<alpha>_def: "\<alpha> = X#\<alpha>'" and u_def: "u = []" and *: "\<beta> = \<zeta> @ \<alpha>'" and elem: "(r, \<zeta>) \<in> \<delta>\<epsilon> M q X"
    using step\<^sub>1_rule_ext[of q "[]" \<alpha> r u \<beta>] by blast
  from 2(4)[of r \<beta>] have "r \<notin> final_states M"
    using step\<^sub>1_steps[OF 2(1)[unfolded u_def]] by simp
  with elem have "(S2 r, \<zeta>) \<in> comp_dpda_delta_eps (S2 q) X" by force
  with \<alpha>_def * have **: "(S2 q, [], \<alpha>) \<leadsto>\<^sub>c (S2 r, [], \<beta>)"
    using comp.step\<^sub>1_rule[of "S2 q" "[]" X \<alpha>' "S2 r" "[]" \<beta>] by (simp add: comp_dpda_def)
  from 2(4) have nr: "\<And>s \<mu>. (r, [], \<beta>) \<leadsto>* (s, [], \<mu>) \<longrightarrow> s \<notin> final_states M"
    using steps_trans[OF step\<^sub>1_steps[OF 2(1)], unfolded u_def] by blast
  from 2(3)[OF u_def nr] have ***: "(S2 r, [], \<beta>) \<leadsto>\<^sub>c* (S2 p, [], \<gamma>)" .
  show ?case
    using comp.steps_trans[OF comp.step\<^sub>1_steps[OF **] ***] .
qed

text \<open>The automaton @{const [source] comp_dpda} mimics the steps of the original automaton in S2-states, 
      provided that the word read so far is not accepted:\<close>
lemma comp_dpda_nonfinal_steps:
  assumes "(q', w, \<alpha>) \<leadsto>* (p, u, \<gamma>)"
      and "w \<noteq> u"
      and "\<And>r \<beta>. (q', w, \<alpha>) \<leadsto>* (r, u, \<beta>) \<longrightarrow> r \<notin> final_states M"
      and "q = S1 q' \<or> q = S2 q'"
    shows "(q, w, \<alpha>) \<leadsto>\<^sub>c* (S2 p, u, \<gamma>)"
using assms proof (induction "(q', w, \<alpha>)" "(p, u, \<gamma>)" arbitrary: q q' w \<alpha> rule: steps_induct2)
  case (2 q' w \<alpha> r v \<beta>)
  from 2(1) obtain X \<alpha>' where \<alpha>_def: "\<alpha> = X#\<alpha>'" and cases:
      "(\<exists>\<zeta>. v = w \<and> \<beta> = \<zeta> @ \<alpha>' \<and> (r, \<zeta>) \<in> \<delta>\<epsilon> M q' X) \<or> (\<exists>a \<zeta>. w = a # v \<and> \<beta> = \<zeta> @ \<alpha>' \<and> (r, \<zeta>) \<in> \<delta> M q' a X)" (is "?a \<or> ?b")
    using step\<^sub>1_rule_ext[of q' w \<alpha> r v \<beta>] by blast
  from 2(5) have rp_nonfinal: "\<And>ra \<beta>'. (r, v, \<beta>) \<leadsto>* (ra, u, \<beta>') \<longrightarrow> ra \<notin> final_states M"
      using steps_trans[OF step\<^sub>1_steps[OF 2(1)]] by blast
  from cases consider (a) ?a | (b) ?b by blast
  then show ?case
  proof cases
    case a
    then obtain \<zeta> where *: "v = w" and **: "\<beta> = \<zeta> @ \<alpha>'" and elem: "(r, \<zeta>) \<in> \<delta>\<epsilon> M q' X" by blast
    from elem 2(6) have "(S1 r, \<zeta>) \<in> comp_dpda_delta_eps q X \<or> (S2 r, \<zeta>) \<in> comp_dpda_delta_eps q X" by force
    with * ** \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S1 r, v, \<beta>) \<or> (q, w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
      using comp.step\<^sub>1_rule[of q w X \<alpha>' _ v \<beta>] by (simp add: comp_dpda_def)
    from 2(4) * have v_neq: "v \<noteq> u" by simp
    from 2(3)[OF v_neq rp_nonfinal] have ****: "(S1 r, v, \<beta>) \<leadsto>\<^sub>c* (S2 p, u, \<gamma>)" by simp
    from 2(3)[OF v_neq rp_nonfinal] have *****: "(S2 r, v, \<beta>) \<leadsto>\<^sub>c* (S2 p, u, \<gamma>)" by simp
    from *** **** ***** show ?thesis
      using comp.step\<^sub>1_steps comp.steps_trans by blast
  next
    case b
    then obtain a \<zeta> where *: "w = a # v" and **: "\<beta> = \<zeta> @ \<alpha>'" and elem: "(r, \<zeta>) \<in> \<delta> M q' a X" by blast
    show ?thesis
    proof (cases "v = u")
      case True
      from 2(5) have r_nonfinal: "r \<notin> final_states M"
        using step\<^sub>1_steps[OF 2(1)[unfolded True]] by simp
      from 2(6) consider (s1) "q = S1 q'" | (s2) "q = S2 q'" by blast
      then have p1: "(q, w, \<alpha>) \<leadsto>\<^sub>c* (S2 r, v, \<beta>)"
      proof cases
        case s1
        with elem r_nonfinal have "(S2 r, \<zeta>) \<in> comp_dpda_delta q a X" by force
        with * ** \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
          using comp.step\<^sub>1_rule[of q w X \<alpha>' "S2 r" v \<beta>] by (simp add: comp_dpda_def)
        show ?thesis
          using comp.step\<^sub>1_steps[OF ***] .
      next
        case s2
        with elem have "(S3 q', [X]) \<in> comp_dpda_delta_eps q X" by auto
        with \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S3 q', w, \<alpha>)"
          using comp.step\<^sub>1_rule[of q w X \<alpha>' "S3 q'" w \<alpha>] by (simp add: comp_dpda_def)
        from elem r_nonfinal have "(S2 r, \<zeta>) \<in> comp_dpda_delta (S3 q') a X" by force
        with * ** \<alpha>_def have ****: "(S3 q', w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
          using comp.step\<^sub>1_rule[of "S3 q'" w X \<alpha>' "S2 r" v \<beta>] by (simp add: comp_dpda_def)
        show ?thesis
          using comp.steps_trans[OF comp.step\<^sub>1_steps[OF ***] comp.step\<^sub>1_steps[OF ****]] .
      qed
      from 2(2)[unfolded True] have a1: "(r, [], \<beta>) \<leadsto>* (p, [], \<gamma>)" 
        using steps_word_app[of r "[]" \<beta> p "[]" \<gamma> u] by simp
      from rp_nonfinal[unfolded True] have a2: "\<And>ra \<beta>'. (r, [], \<beta>) \<leadsto>* (ra, [], \<beta>') \<longrightarrow> ra \<notin> final_states M"
        using steps_word_app[of r "[]" \<beta> _ "[]" _ u] by simp
      have "(S2 r, [], \<beta>) \<leadsto>\<^sub>c* (S2 p, [], \<gamma>)"
        using comp_dpda_nonfinal_stepsS2[OF a1 a2] .
      with True have p2: "(S2 r, v, \<beta>) \<leadsto>\<^sub>c* (S2 p, u, \<gamma>)"
        using comp.steps_word_app[of "S2 r" "[]" \<beta> "S2 p" "[]" \<gamma> u] by simp
      show ?thesis
        using comp.steps_trans[OF p1 p2] .
    next
      case False
      from 2(6) consider (s1) "q = S1 q'" | (s2) "q = S2 q'" by blast
      then have p: "(q, w, \<alpha>) \<leadsto>\<^sub>c* (S1 r, v, \<beta>) \<or> (q, w, \<alpha>) \<leadsto>\<^sub>c* (S2 r, v, \<beta>)"
      proof (cases)
        case s1
        with elem have "(S1 r, \<zeta>) \<in> comp_dpda_delta q a X \<or> (S2 r, \<zeta>) \<in> comp_dpda_delta q a X" by force
        with * ** \<alpha>_def have "(q, w, \<alpha>) \<leadsto>\<^sub>c (S1 r, v, \<beta>) \<or> (q, w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
          using comp.step\<^sub>1_rule[of q w X \<alpha>' _ v \<beta>] by (simp add: comp_dpda_def)
        then show ?thesis
          using comp.step\<^sub>1_steps by blast
      next
        case s2
        with elem have "(S3 q', [X]) \<in> comp_dpda_delta_eps q X" by auto
        with \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S3 q', w, \<alpha>)"
          using comp.step\<^sub>1_rule[of q w X \<alpha>' "S3 q'" w \<alpha>] by (simp add: comp_dpda_def)
        from elem have "(S1 r, \<zeta>) \<in> comp_dpda_delta (S3 q') a X \<or> (S2 r, \<zeta>) \<in> comp_dpda_delta (S3 q') a X" by force
        with * ** \<alpha>_def have ****: "(S3 q', w, \<alpha>) \<leadsto>\<^sub>c (S1 r, v, \<beta>) \<or> (S3 q', w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
          using comp.step\<^sub>1_rule[of "S3 q'" w X \<alpha>' _ v \<beta>] by (simp add: comp_dpda_def)
        from *** **** show ?thesis
          using comp.step\<^sub>1_steps comp.steps_trans by metis
      qed
      from 2(3)[OF False rp_nonfinal] have p1: "(S1 r, v, \<beta>) \<leadsto>\<^sub>c* (S2 p, u, \<gamma>)" by simp
      from 2(3)[OF False rp_nonfinal] have p2: "(S2 r, v, \<beta>) \<leadsto>\<^sub>c* (S2 p, u, \<gamma>)" by simp
      from p p1 p2 show ?thesis
        using comp.steps_trans by blast
    qed
  qed
qed simp

text \<open>The automaton @{const [source] comp_dpda} transitions to an S1-state if the target state is a final state:\<close>
lemma comp_dpda_final_steps:
  assumes "(q', w, \<alpha>) \<leadsto>+ (p, u, \<gamma>)"
      and "p \<in> final_states M"
      and "q = S1 q' \<or> q = S2 q'"
    shows "(q, w, \<alpha>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)"
using assms proof (induction "(q', w, \<alpha>)" "(p, u, \<gamma>)" arbitrary: q q' w \<alpha> rule: steps1_induct)
  case (base q' w \<alpha>)
  from base(1) obtain X \<alpha>' where \<alpha>_def: "\<alpha> = X#\<alpha>'" and cases:
      "(\<exists>\<beta>. u = w \<and> \<gamma> = \<beta> @ \<alpha>' \<and> (p, \<beta>) \<in> \<delta>\<epsilon> M q' X) \<or> (\<exists>a \<beta>. w = a # u \<and> \<gamma> = \<beta> @ \<alpha>' \<and> (p, \<beta>) \<in> \<delta> M q' a X)" (is "?a \<or> ?b")
    using step\<^sub>1_rule_ext[of q' w \<alpha> p u \<gamma>] by blast
  from cases consider (a) ?a | (b) ?b by blast
  then show ?case
  proof cases
    case a
    then obtain \<beta> where *: "u = w" and **: "\<gamma> = \<beta> @ \<alpha>'" and elem: "(p, \<beta>) \<in> \<delta>\<epsilon> M q' X" by blast
    from base(2,3) elem have "(S1 p, \<beta>) \<in> comp_dpda_delta_eps q X" by force
    with * ** \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S1 p, u, \<gamma>)"
      using comp.step\<^sub>1_rule[of q w X \<alpha>' "S1 p" u \<gamma>] by (simp add: comp_dpda_def)
    show ?thesis
      using comp.steps1_step[OF ***] .
  next
    case b
    then obtain a \<beta> where *: "w = a # u" and **: "\<gamma> = \<beta> @ \<alpha>'" and elem: "(p, \<beta>) \<in> \<delta> M q' a X" by blast
    from base(3) consider (c) "q = S1 q'" | (d) "q = S2 q'" by blast
    then show ?thesis
    proof cases
      case c
      with elem base(2) have "(S1 p, \<beta>) \<in> comp_dpda_delta q a X" by force
      with * ** \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S1 p, u, \<gamma>)"
        using comp.step\<^sub>1_rule[of q w X \<alpha>' "S1 p" u \<gamma>] by (simp add: comp_dpda_def)
      show ?thesis
        using comp.steps1_step[OF ***] .
    next
      case d
      with elem have "(S3 q', [X]) \<in> comp_dpda_delta_eps q X" by auto
      with \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S3 q', w, \<alpha>)"
        using comp.step\<^sub>1_rule[of q w X \<alpha>' "S3 q'" w \<alpha>] by (simp add: comp_dpda_def)
      from elem base(2) have "(S1 p, \<beta>) \<in> comp_dpda_delta (S3 q') a X" by force
      with * ** \<alpha>_def have ****: "(S3 q', w, \<alpha>) \<leadsto>\<^sub>c (S1 p, u, \<gamma>)"
        using comp.step\<^sub>1_rule[of "S3 q'" w X \<alpha>' "S1 p" u \<gamma>] by (simp add: comp_dpda_def)
      show ?thesis
        using comp.steps1_trans[OF comp.steps1_step[OF ***] comp.steps1_step[OF ****]] .
    qed
  qed
next
  case (step q' w \<alpha> r v \<beta>)
  from step(1) obtain X \<alpha>' where \<alpha>_def: "\<alpha> = X#\<alpha>'" and cases:
      "(\<exists>\<beta>'. v = w \<and> \<beta> = \<beta>' @ \<alpha>' \<and> (r, \<beta>') \<in> \<delta>\<epsilon> M q' X) \<or> (\<exists>a \<beta>'. w = a # v \<and> \<beta> = \<beta>' @ \<alpha>' \<and> (r, \<beta>') \<in> \<delta> M q' a X)" (is "?c \<or> ?d")
    using step\<^sub>1_rule_ext[of q' w \<alpha> r v \<beta>] by blast
  from step(5) consider (a) "q = S1 q'" | (b) "q = S2 q'" by blast
  then show ?case
  proof cases
    case a
    from cases consider (c) ?c | (d) ?d by blast
    then show ?thesis
    proof cases
      case c
      then obtain \<zeta> where *: "v = w" and **: "\<beta> = \<zeta> @ \<alpha>'" and elem: "(r, \<zeta>) \<in> \<delta>\<epsilon> M q' X" by blast
      from elem a have "(S1 r, \<zeta>) \<in> comp_dpda_delta_eps q X" by auto
      with * ** \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S1 r, v, \<beta>)"
        using comp.step\<^sub>1_rule[of q w X \<alpha>' "S1 r" v \<beta>] by (simp add: comp_dpda_def)
      from step(3)[OF step(4)] have ****: "(S1 r, v, \<beta>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)" by simp
      show ?thesis
        using comp.steps1_trans[OF comp.steps1_step[OF ***] ****] .
    next
      case d
      then obtain a \<zeta> where *: "w = a # v" and **: "\<beta> = \<zeta> @ \<alpha>'" and elem: "(r, \<zeta>) \<in> \<delta> M q' a X" by blast
      from elem a have "(S1 r, \<zeta>) \<in> comp_dpda_delta q a X \<or> (S2 r, \<zeta>) \<in> comp_dpda_delta q a X" by force
      with * ** \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S1 r, v, \<beta>) \<or> (q, w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
        using comp.step\<^sub>1_rule[of q w X \<alpha>' _ v \<beta>] by (simp add: comp_dpda_def)
      from step(3)[OF step(4)] have ****: "(S1 r, v, \<beta>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)" by simp 
      from step(3)[OF step(4)] have *****: "(S2 r, v, \<beta>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)" by simp
      from *** **** ***** show ?thesis
        using comp.steps1_step comp.steps1_trans by blast
    qed
  next
    case b
    from cases consider (c) ?c | (d) ?d by blast
    then show ?thesis
    proof cases
      case c
      then obtain \<zeta> where *: "v = w" and **: "\<beta> = \<zeta> @ \<alpha>'" and elem: "(r, \<zeta>) \<in> \<delta>\<epsilon> M q' X" by blast
      from elem b have "(S1 r, \<zeta>) \<in> comp_dpda_delta_eps q X \<or> (S2 r, \<zeta>) \<in> comp_dpda_delta_eps q X" by force
      with * ** \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S1 r, v, \<beta>) \<or> (q, w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
        using comp.step\<^sub>1_rule[of q w X \<alpha>' _ v \<beta>] by (simp add: comp_dpda_def)
      from step(3)[OF step(4)] have ****: "(S1 r, v, \<beta>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)" by simp 
      from step(3)[OF step(4)] have *****: "(S2 r, v, \<beta>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)" by simp
      from *** **** ***** show ?thesis
        using comp.steps1_step comp.steps1_trans by blast
    next
      case d
      then obtain a \<zeta> where *: "w = a # v" and **: "\<beta> = \<zeta> @ \<alpha>'" and elem: "(r, \<zeta>) \<in> \<delta> M q' a X" by blast
      from elem b have "(S3 q', [X]) \<in> comp_dpda_delta_eps q X" by auto
      with \<alpha>_def have ***: "(q, w, \<alpha>) \<leadsto>\<^sub>c (S3 q', w, \<alpha>)"
        using comp.step\<^sub>1_rule[of q w X \<alpha>' "S3 q'" w \<alpha>] by (simp add: comp_dpda_def)
      from elem have "(S1 r, \<zeta>) \<in> comp_dpda_delta (S3 q') a X \<or> (S2 r, \<zeta>) \<in> comp_dpda_delta (S3 q') a X" by force
      with * ** \<alpha>_def have ****: "(S3 q', w, \<alpha>) \<leadsto>\<^sub>c (S1 r, v, \<beta>) \<or> (S3 q', w, \<alpha>) \<leadsto>\<^sub>c (S2 r, v, \<beta>)"
        using comp.step\<^sub>1_rule[of "S3 q'" w X \<alpha>' _ v \<beta>] by (simp add: comp_dpda_def)
      from step(3)[OF step(4)] have *****: "(S1 r, v, \<beta>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)" by simp
      from step(3)[OF step(4)] have ******: "(S2 r, v, \<beta>) \<leadsto>\<^sub>c+ (S1 p, u, \<gamma>)" by simp
      from *** **** ***** ****** show ?thesis
        using comp.steps1_step comp.steps1_trans by metis
    qed
  qed
qed

text \<open>If the automaton @{const [source] comp_dpda} ends up in an S3-state while reading a word, 
      then no state reached while reading that same word is final:\<close>
lemma comp_dpda_steps_nonfinalS1:
  assumes "(S1 q, w, \<alpha>) \<leadsto>\<^sub>c* (S3 p, [], \<gamma>)"
      and "(q, w, \<alpha>) \<leadsto>* (r, [], \<beta>)"
    shows "r \<notin> final_states M"
proof
  assume r_final: "r \<in> final_states M"
  from assms(1) obtain n where p1: "(S1 q, w, \<alpha>) \<leadsto>\<^sub>c(n) (S3 p, [], \<gamma>)"
    using comp.stepn_steps[of "S1 q" w \<alpha> "S3 p" "[]" \<gamma>] by blast
  have np: "comp.no_step\<^sub>1 (S3 p, [], \<gamma>)"
    using comp.step\<^sub>1_rule_ext[of "S3 p" "[]" \<gamma>] by (simp add: comp_dpda_def)
  have "(S1 q, w, \<alpha>) \<leadsto>\<^sub>c* (S1 r, [], \<beta>)"
  proof (cases "(q, w, \<alpha>) = (r, [], \<beta>)")
    case True
    then show ?thesis
      by (simp add: comp.steps_refl)
  next
    case False
    have q1: "(q, w, \<alpha>) \<leadsto>+ (r, [], \<beta>)"
      using steps_steps1[OF assms(2) False] .
    have q2: "(S1 q, w, \<alpha>) \<leadsto>\<^sub>c+ (S1 r, [], \<beta>)"
      using comp_dpda_final_steps[OF q1 r_final] by simp
    show ?thesis
      using comp.steps1_steps[OF q2] .
  qed
  then obtain m where p2: "(S1 q, w, \<alpha>) \<leadsto>\<^sub>c(m) (S1 r, [], \<beta>)"
    using comp.stepn_steps[of "S1 q" w \<alpha> "S1 r" "[]" \<beta>] by blast 
  have m_leq_n: "m \<le> n"
    using comp.max_eps_steps[OF p1 np p2] .
  have "(S1 r, [], \<beta>) \<leadsto>\<^sub>c(n - m) (S3 p, [], \<gamma>)"
    using comp.split_path[OF p1 m_leq_n] comp.dpda_stepn_det[OF p2] by blast
  then have *: "(S1 r, [], \<beta>) \<leadsto>\<^sub>c* (S3 p, [], \<gamma>)"
    using comp.stepn_steps[of "S1 r" "[]" \<beta> "S3 p" "[]" \<gamma>] by blast
  show False
    using comp_dpda_steps_from_S1[OF *] by simp
qed

lemma comp_dpda_steps_nonfinalS2:
  assumes "(S2 q, w, \<alpha>) \<leadsto>\<^sub>c* (S3 p, [], \<gamma>)"
      and "(q, w, \<alpha>) \<leadsto>+ (r, [], \<beta>)"
    shows "r \<notin> final_states M"
proof
  assume r_final: "r \<in> final_states M"
  from assms(1) obtain n where p1: "(S2 q, w, \<alpha>) \<leadsto>\<^sub>c(n) (S3 p, [], \<gamma>)"
    using comp.stepn_steps[of "S2 q" w \<alpha> "S3 p" "[]" \<gamma>] by blast
  have np: "comp.no_step\<^sub>1 (S3 p, [], \<gamma>)"
    using comp.step\<^sub>1_rule_ext[of "S3 p" "[]" \<gamma>] by (simp add: comp_dpda_def)
  obtain m where p2: "(S2 q, w, \<alpha>) \<leadsto>\<^sub>c(m) (S1 r, [], \<beta>)"
    using comp.steps1_steps[OF comp_dpda_final_steps[OF assms(2) r_final, of "S2 q", simplified]] comp.stepn_steps[of "S2 q" w \<alpha> "S1 r" "[]" \<beta>] by blast
  have m_leq_n: "m \<le> n"
    using comp.max_eps_steps[OF p1 np p2] .
  have "(S1 r, [], \<beta>) \<leadsto>\<^sub>c(n - m) (S3 p, [], \<gamma>)"
    using comp.split_path[OF p1 m_leq_n] comp.dpda_stepn_det[OF p2] by blast
  then have *: "(S1 r, [], \<beta>) \<leadsto>\<^sub>c* (S3 p, [], \<gamma>)"
    using comp.stepn_steps[of "S1 r" "[]" \<beta> "S3 p" "[]" \<gamma>] by blast
  show False
    using comp_dpda_steps_from_S1[OF *] by simp
qed

text \<open>The language of the automaton @{const [source] comp_dpda} is the complement language:\<close>
lemma lang_comp_dpda:
  "comp.accept_final = - accept_final"
proof
  show "comp.accept_final \<subseteq> - accept_final"
  proof
    fix w
    assume "w \<in> comp.accept_final"
    then obtain q \<gamma> where p: "(init_state comp_dpda, w, [init_symbol comp_dpda]) \<leadsto>\<^sub>c* (q, [], \<gamma>)" and q_final: "q \<in> final_states comp_dpda"
      unfolding comp.accept_final_def by blast
    from q_final obtain q' where q_def: "q = S3 q'"
      by (auto simp: comp_dpda_def comp_dpda_final_states_def)
    have "\<And>r \<beta>. (init_state M, w, [init_symbol M]) \<leadsto>* (r, [], \<beta>) \<longrightarrow> r \<notin> final_states M"
    proof
      fix r \<beta>
      assume asm: "(init_state M, w, [init_symbol M]) \<leadsto>* (r, [], \<beta>)"
      consider (a) "init_state M \<in> final_states M" | (b) "init_state M \<notin> final_states M" by satx
      then show "r \<notin> final_states M"
      proof cases
        case a
        with p q_def have *: "(S1 (init_state M), w, [init_symbol M]) \<leadsto>\<^sub>c* (S3 q', [], \<gamma>)"
          by (simp add: comp_dpda_def comp_dpda_init_state_def)
        show ?thesis
          using comp_dpda_steps_nonfinalS1[OF * asm] .
      next
        case b
        consider (c) "r = init_state M" | (d) "r \<noteq> init_state M" by satx
        then show ?thesis
        proof cases
          case c
          with b show ?thesis by simp
        next
          case d
          then have *: "(init_state M, w, [init_symbol M]) \<leadsto>+ (r, [], \<beta>)"
            using steps_steps1[OF asm] by simp
          from b p q_def have **: "(S2 (init_state M), w, [init_symbol M]) \<leadsto>\<^sub>c* (S3 q', [], \<gamma>)"
            by (simp add: comp_dpda_def comp_dpda_init_state_def)
          show ?thesis
            using comp_dpda_steps_nonfinalS2[OF ** *] .
        qed
      qed
    qed
    then show "w \<in> - accept_final"
      by (auto simp: accept_final_def)
  qed
next
  show "- accept_final \<subseteq> comp.accept_final"
  proof
    fix w
    assume "w \<in> - accept_final"
    then have nonfinal: "\<And>r \<beta>. (init_state M, w, [init_symbol M]) \<leadsto>* (r, [], \<beta>) \<longrightarrow> r \<notin> final_states M"
      by (auto simp: accept_final_def)
    from M_path[of w] obtain q X \<alpha> a where p: "(init_state M, w, [init_symbol M]) \<leadsto>* (q, [], X # \<alpha>)" and delta_M: "\<delta> M q a X \<noteq> {}" by blast
    consider (a) "w = []" | (b) "w \<noteq> []" by satx
    then have *: "(init_state comp_dpda, w, [init_symbol comp_dpda]) \<leadsto>\<^sub>c* (S2 q, [], X#\<alpha>)"
    proof cases
      case a
      from nonfinal[unfolded a] have "init_state M \<notin> final_states M"
        using steps_refl[of "init_state M" "[]" "[init_symbol M]"] by simp
      with a show ?thesis
        using comp_dpda_nonfinal_stepsS2[OF p[unfolded a] nonfinal[unfolded a]] by (simp add: comp_dpda_def comp_dpda_init_state_def)
    next
      case b
      with p nonfinal show ?thesis
        using comp_dpda_nonfinal_steps[of "init_state M" w "[init_symbol M]" q "[]" "X#\<alpha>"] by (simp add: comp_dpda_def comp_dpda_init_state_def)
    qed
    from delta_M have **: "(S2 q, [], X#\<alpha>) \<leadsto>\<^sub>c (S3 q, [], X#\<alpha>)"
      using comp.step\<^sub>1_rule[of "S2 q" "[]" X \<alpha> "S3 q" "[]" "X#\<alpha>"] comp_dpda_def by auto
    have "(init_state comp_dpda, w, [init_symbol comp_dpda]) \<leadsto>\<^sub>c* (S3 q, [], X # \<alpha>)"
      using comp.steps_trans[OF * comp.step\<^sub>1_steps[OF **]] .
    then show "w \<in> comp.accept_final"
      using comp.accept_final_def comp_dpda_def comp_dpda_final_states_def by force
  qed
qed

end

text \<open>By constructing the two automata one after another, we get the final lemma stating that deterministic 
      context-free languages are closed under complementation:\<close>
lemma complement_dpda:
  assumes "dpda (M :: ('q :: finite, 'a :: finite, 's :: finite) pda)"
  shows "\<exists>M' :: ('q st_scan s123, 'a, 's sym_scan) pda.
    dpda M' \<and> pda.accept_final M' = - pda.accept_final M"
proof -
  let ?SM = "dpda_scan.scan_dpda M :: ('q st_scan, 'a, 's sym_scan) pda"
  have dpda_sm: "dpda ?SM"
    using assms dpda_scan.dpda_scan_dpda dpda_scan_def by blast
  have *: "\<And>a w. \<exists>q X \<alpha>. pda.steps ?SM (init_state ?SM, w, [init_symbol ?SM]) (q, [], X#\<alpha>) \<and> delta ?SM q a X \<noteq> {}"
    using assms dpda_scan.scan_dpda_scans dpda_scan_def by blast
  have L1: "pda.accept_final ?SM = pda.accept_final M"
    using assms dpda_scan.lang_scan_dpda dpda_scan.intro by auto
  let ?CM = "complement_dpda.comp_dpda ?SM :: ('q st_scan s123, 'a, 's sym_scan) pda"
  from dpda_sm * have dpda_cm: "dpda ?CM"
    using complement_dpda.dpda_comp_dpda complement_dpda.intro complement_dpda_axioms_def by blast
  from dpda_sm * have L2: "pda.accept_final ?CM = UNIV - pda.accept_final ?SM"
    using complement_dpda.lang_comp_dpda complement_dpda_axioms_def complement_dpda_def by blast
  from dpda_cm L1 L2 show ?thesis by blast
qed

end