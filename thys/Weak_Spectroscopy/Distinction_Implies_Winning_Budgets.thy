(* License: LGPL *)

section \<open>Correctness\<close>

text \<open>
  Energy levels where the defender wins in the spectroscopy game and equivalences coincide in the following sense:
  There exists a formula \<open>\<phi>\<close> distinguishing a process \<open>p\<close> from a set of processes \<open>Q\<close> with expressiveness price of at most \<open>e\<close> if and only if \<open>e\<close> is in attacker's winning budget of \<open>Attacker_Immediate p Q\<close>.

  The proof is split into two directions, closely following the structure of \<^cite>\<open>bj2023silentStepSpectroscopyArxiv\<close>.
  The forward direction is given by the lemma \<open>distinction_implies_winning_budgets\<close> combined with the upwards closure of winning budgets.
  To show the other direction, one can construct a (strategy) formula with an appropriate price using the constructive proof of \<open>winning_budget_implies_strategy_formula\<close>.
\<close>

subsection \<open>Distinction Implies Winning Budgets\<close>

theory Distinction_Implies_Winning_Budgets
  imports Spectroscopy_Game Expressiveness_Price
begin

context lts_tau
begin

text \<open>
  We prove that if a formula distinguishes process \<open>p\<close> from a set of process \<open>Q\<close>, then the price of this formula is in attacker's winning budgets.
\<close>

lemma distinction_implies_winning_budgets_empty_Q:
  assumes
    \<open>distinguishes_from \<phi> p {}\<close>
  shows
    \<open>spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p {})\<close>
  using assms
proof -
  have \<open>spectroscopy_moves (Defender_Conj p {}) p' = None\<close> for p'
    by(rule spectroscopy_moves.elims, auto)
  moreover have \<open>spectroscopy_defender (Defender_Conj p {})\<close> by simp
  ultimately have conj_win: \<open>spectro_att_wins (expressiveness_price \<phi>) (Defender_Conj p {})\<close>
    by (simp add: weak_spectroscopy_game.attacker_wins.Defense)
  from late_inst_conj[of p \<open>{}\<close> p \<open>{}\<close>] have next_move0:
    \<open>spectroscopy_moves (Attacker_Delayed p {}) (Defender_Conj p {}) = id_up\<close> by force
  from delay[of p \<open>{}\<close> p \<open>{}\<close>] have next_move1:
    \<open>spectroscopy_moves (Attacker_Immediate p {}) (Attacker_Delayed p {}) = id_up\<close> by force
  moreover have \<open>weak_spectroscopy_game.attacker (Attacker_Immediate p {})\<close> by simp
  ultimately show ?thesis
    using weak_spectroscopy_game.attacker_wins.Attack next_move0 next_move1
    by (metis conj_win option.distinct(1) option.sel spectroscopy_defender.simps(4))
qed

lemma distinction_implies_winning_budgets:
  assumes
    \<open>distinguishes_from \<phi> p Q\<close>
  shows
    \<open>spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q)\<close>
proof -
  have
    \<open> (\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
             \<longrightarrow> spectro_att_wins (expressiveness_price \<phi>)(Attacker_Immediate p Q))
    \<and>
      ((\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
          \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
      \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
          Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
          \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Defender_Conj p Q))
      \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
          Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> (\<forall>q \<in> Q. \<nexists>q'. q \<mapsto> \<tau> q')
          \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
      \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
          hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
           Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)
          \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)))
    \<and>
      (\<forall>p q. hml_srbb_conj.distinguishes \<psi> p q
             \<longrightarrow> spectro_att_wins (expr_pr_conjunct \<psi>) (Attacker_Conjunct p q))\<close>
    for \<phi> \<chi> \<psi>
  proof -
    fix \<phi> \<chi> \<psi>
    show \<open>(\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
               \<longrightarrow> spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q))
      \<and>
        ((\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
            \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
            \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Defender_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> (\<forall>q \<in> Q. \<nexists>q'. q \<mapsto> \<tau> q')
            \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
            hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
             Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)
            \<longrightarrow> spectro_att_wins (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)))
      \<and>
        (\<forall>p q. hml_srbb_conj.distinguishes \<psi> p q
               \<longrightarrow> spectro_att_wins (expr_pr_conjunct \<psi>) (Attacker_Conjunct p q))\<close>
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct[of _ _ _ \<phi> \<chi> \<psi>])
      case TT
      then show ?case
      proof (clarify)
        fix Q p
        assume \<open>Q \<noteq> {}\<close> \<open>distinguishes_from TT p Q\<close>
        hence \<open>\<exists>q. q \<in> Q\<close>
          by blast
        then obtain q where \<open>q \<in> Q\<close> by auto
        hence \<open>distinguishes TT p q\<close>
          using \<open>distinguishes_from TT p Q\<close> distinguishes_from_def by auto
        with verum_never_distinguishes
        show \<open>spectro_att_wins (expressiveness_price TT) (Attacker_Immediate p Q)\<close>
          by blast
      qed
    next
      case (Internal \<chi>)
      show ?case
      proof (clarify)
        fix Q p
        assume \<open>Q \<noteq> {}\<close> \<open>distinguishes_from (Internal \<chi>) p Q\<close>
        then have
          \<open>\<exists>p'. p \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>\<close>
          \<open>\<forall>q \<in> Q. (\<nexists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)\<close>
          by auto
        hence \<open>\<forall>q \<in> Q. (\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>(hml_srbb_inner_models q' \<chi>))\<close> by auto
        then have \<open>\<forall>q \<in> Q. (\<forall>q'\<in>Q'. q \<Zsurj> q' \<longrightarrow> \<not>(hml_srbb_inner_models q' \<chi>))\<close>
          for Q' by blast
        then have \<open>Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(hml_srbb_inner_models q' \<chi>))\<close>
          for Q' using \<open>Q \<noteq> {}\<close> by blast
        define Q\<tau> where \<open>Q\<tau> \<equiv> silent_reachable_set Q\<close>
        with \<open>\<And>Q'. Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(hml_srbb_inner_models q' \<chi>))\<close>
        have \<open>\<forall>q' \<in> Q\<tau>. \<not>(hml_srbb_inner_models q' \<chi>)\<close>
          using sreachable_set_is_sreachable by presburger
        have \<open>Q\<tau> \<Zsurj>S Q\<tau>\<close> unfolding Q\<tau>_def
          by (metis silent_reachable_trans sreachable_set_is_sreachable
              silent_reachable.intros(1))
        from \<open>\<exists>p'. p \<Zsurj> p' \<and> (hml_srbb_inner_models p' \<chi>)\<close>
        obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        from this(1) have \<open>p \<Zsurj>L p'\<close> using silent_reachable_impl_loopless by blast
        have \<open>Q\<tau> \<noteq> {}\<close>
          using silent_reachable.intros(1) sreachable_set_is_sreachable Q\<tau>_def \<open>Q \<noteq> {}\<close>
          by fastforce
        from \<open>hml_srbb_inner_models p' \<chi>\<close> \<open>\<forall>q' \<in> Q\<tau>. \<not>(hml_srbb_inner_models q' \<chi>)\<close>
          have \<open>hml_srbb_inner.distinguishes_from \<chi> p' Q\<tau>\<close> by simp
        with \<open>Q\<tau> \<Zsurj>S Q\<tau>\<close> \<open>Q\<tau> \<noteq> {}\<close> Internal
        have \<open>spectro_att_wins (expr_pr_inner \<chi>) (Attacker_Delayed p' Q\<tau>)\<close>
          by blast
        moreover have \<open>expr_pr_inner \<chi> = expressiveness_price (Internal \<chi>)\<close> by simp
        ultimately have \<open>spectro_att_wins (expressiveness_price (Internal \<chi>))
            (Attacker_Delayed p' Q\<tau>)\<close> by simp
        hence \<open>spectro_att_wins (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)\<close>
        proof(induct rule: silent_reachable_loopless.induct[of \<open>p\<close> \<open>p'\<close>, OF \<open>p \<Zsurj>L p'\<close>])
          case (1 p)
          thus ?case by simp
        next
          case (2 p p' p'')
          hence \<open>spectro_att_wins (expressiveness_price (Internal \<chi>))
                                  (Attacker_Delayed p' Q\<tau>)\<close>
            by simp
          moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q\<tau>) (Attacker_Delayed p' Q\<tau>)
            = id_up\<close> using spectroscopy_moves.simps(2) \<open>p \<noteq> p'\<close> \<open>p \<mapsto>\<tau> p'\<close> by auto
          moreover have \<open>weak_spectroscopy_game.attacker (Attacker_Delayed p Q\<tau>)\<close> by simp
          ultimately show ?case
            using weak_spectroscopy_game.attacker_wins_Ga_with_id_step by auto
        qed
        have  \<open>Q \<Zsurj>S Q\<tau>\<close>
          using Q\<tau>_def sreachable_set_is_sreachable by simp
        hence \<open>spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q\<tau>) = id_up\<close>
          using spectroscopy_moves.simps(1) by simp
        with \<open>spectro_att_wins (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)\<close>
        show \<open>spectro_att_wins (expressiveness_price (Internal \<chi>)) (Attacker_Immediate p Q)\<close>
          using weak_spectroscopy_game.attacker_wins_Ga_with_id_step
          by (metis option.discI option.sel spectroscopy_defender.simps(1))
        qed
    next
      case (ImmConj I \<psi>s)
      show ?case
      proof (clarify)
        fix Q p
        assume \<open>Q \<noteq> {}\<close> and \<open>distinguishes_from (ImmConj I \<psi>s) p Q\<close>
        from this(2) have \<open>\<forall>q\<in>Q. p \<Turnstile>SRBB ImmConj I \<psi>s \<and> \<not> q \<Turnstile>SRBB ImmConj I \<psi>s\<close>
          unfolding distinguishes_from_def distinguishes_def by blast
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i)
            \<and> \<not>hml_srbb_conjunct_models q (\<psi>s i)\<close>
          by simp
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          using hml_srbb_conj.distinguishes_def by simp
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I. ((\<psi>s i) \<in> range \<psi>s)
            \<and> hml_srbb_conj.distinguishes (\<psi>s i) p q\<close> by blast
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I.
            spectro_att_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Conjunct p q)\<close>
          using ImmConj by blast
        hence a_clause_wina:
          \<open>\<forall>q\<in>Q. \<exists>i\<in>I.
            spectro_att_wins (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0)
                             (Attacker_Conjunct p q)\<close>
          using expressiveness_price_ImmConj_geq_parts
            weak_spectroscopy_game.win_a_upwards_closure by fast
        from this \<open>Q \<noteq> {}\<close> have \<open>I \<noteq> {}\<close> by blast
        hence subtracts:
          \<open>subtract_fn 0 0 1 0 1 0 0 0 (expressiveness_price (ImmConj I \<psi>s))
              = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0)\<close>
          \<open>subtract_fn 0 0 1 0 0 0 0 0 (expressiveness_price (ImmConj I \<psi>s)
                                       - E 0 0 0 0 1 0 0 0)
              = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0)\<close>
          by (simp add: \<open>I \<noteq> {}\<close>)+
        have def_conj: \<open>spectroscopy_defender (Defender_Conj p Q)\<close> by simp
        have \<open>spectroscopy_moves (Defender_Conj p Q) N \<noteq> None
              \<Longrightarrow> N = Attacker_Conjunct (attacker_state N) (defender_state N)\<close> for N
          by (metis spectroscopy_moves.simps(29,30,33,34,58,62)
              spectroscopy_position.exhaust_sel)
        hence move_kind: \<open>spectroscopy_moves (Defender_Conj p Q) N \<noteq> None
            \<Longrightarrow> \<exists>q\<in>Q. N = Attacker_Conjunct p q\<close> for N
          using conj_answer by metis
        hence update: \<open>\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<Longrightarrow>
          weak_spectroscopy_game.weight (Defender_Conj p Q) g' = subtract_fn 0 0 1 0 0 0 0 0\<close>
          by fastforce
        hence move_wina: \<open>\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
          \<Longrightarrow> (subtract_fn 0 0 1 0 0 0 0 0) (expressiveness_price (ImmConj I \<psi>s)
                - E 0 0 0 0 1 0 0 0)
              = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0)
           \<and>  spectro_att_wins (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0) g'\<close>
          using move_kind a_clause_wina subtracts by blast
        from weak_spectroscopy_game.attacker_wins.Defense[OF def_conj] update move_wina have
          def_conj_wina:
            \<open>spectro_att_wins (expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0)
                              (Defender_Conj p Q)\<close>
          by (metis (lifting))
        have imm_to_conj:
            \<open>spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p Q) \<noteq> None\<close>
          by (simp add: \<open>Q \<noteq> {}\<close>)
        have imm_to_conj_wgt:
          \<open>weak_spectroscopy_game.weight (Attacker_Immediate p Q) (Defender_Conj p Q)
                                         (expressiveness_price (ImmConj I \<psi>s))
          = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0)\<close>
          using \<open>Q \<noteq> {}\<close> leq_components subtracts(1) by force
        from weak_spectroscopy_game.Attack[OF _ imm_to_conj imm_to_conj_wgt] def_conj_wina
        show
          \<open>spectro_att_wins (expressiveness_price (ImmConj I \<psi>s)) (Attacker_Immediate p Q)\<close>
          by simp
      qed
    next
      case (Obs \<alpha> \<phi>)
      have
        \<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q
        \<longrightarrow> Q \<Zsurj>S Q \<longrightarrow> spectro_att_wins (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>))
                                         (Attacker_Delayed p Q)\<close>
      proof(clarify)
        fix p Q
        assume
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close>
          \<open> \<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close>
        have \<open>\<exists>p' Q'. p \<mapsto>a \<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q'
              \<and> spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q')\<close>
        proof(cases \<open>\<alpha> = \<tau>\<close>)
          case True
          with \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close>
          have dist_unfold:  \<open>((\<exists>p'. p \<mapsto>\<tau> p' \<and> p' \<Turnstile>SRBB \<phi>) \<or> p \<Turnstile>SRBB \<phi>)\<close> by simp
          then obtain p' where \<open>p' \<Turnstile>SRBB \<phi>\<close> \<open>p \<mapsto>a \<alpha> p'\<close>
            unfolding True by blast
          from \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> have
            \<open>\<forall>q\<in>Q. (\<not> q \<Turnstile>SRBB \<phi>) \<and> (\<nexists>q'. q \<mapsto>\<tau> q' \<and> q' \<Turnstile>SRBB \<phi>)\<close>
            using True by auto
          hence \<open>\<forall>q\<in>Q. \<not>q \<Turnstile>SRBB \<phi>\<close>
            using \<open>\<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close> by fastforce
          hence \<open>distinguishes_from \<phi> p' Q\<close>
            using \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
          with Obs have \<open>spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q)\<close>
            using \<open>Q \<noteq> {}\<close> by blast
          moreover have \<open>Q \<mapsto>aS \<alpha> Q\<close>
            unfolding True
            using \<open>\<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close> silent_reachable_append_\<tau>
              silent_reachable.intros(1) by blast
          ultimately show ?thesis using \<open>p \<mapsto>a \<alpha> p'\<close> by blast
        next
          case False
          with \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close>
          obtain p'' where \<open>(p \<mapsto>\<alpha> p'') \<and> (p'' \<Turnstile>SRBB \<phi>)\<close> by auto
          let ?Q' = \<open>step_set Q \<alpha>\<close>
          from \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close>
          have \<open>\<forall>q\<in>?Q'. \<not> q \<Turnstile>SRBB \<phi>\<close>
            using \<open>Q \<noteq> {}\<close> and step_set_is_step_set
            by force
          from \<open>\<forall>q\<in>step_set Q \<alpha>. \<not> q \<Turnstile>SRBB \<phi>\<close> \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile>SRBB \<phi>\<close>
          have \<open>distinguishes_from \<phi> p'' ?Q'\<close> by simp
          hence \<open>spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p'' ?Q')\<close>
            by (metis Obs distinction_implies_winning_budgets_empty_Q)
          moreover have \<open>p \<mapsto>\<alpha> p''\<close> using \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile>SRBB \<phi>\<close> by simp
          moreover have \<open>Q \<mapsto>aS \<alpha> ?Q'\<close> by (simp add: False lts.step_set_is_step_set)
          ultimately show ?thesis by blast
        qed
        then obtain p' Q' where p'_Q': \<open>p \<mapsto>a \<alpha> p'\<close> \<open>Q \<mapsto>aS \<alpha> Q'\<close> and
          wina: \<open>spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q')\<close> by blast
        have attacker: \<open>weak_spectroscopy_game.attacker (Attacker_Delayed p Q)\<close> by simp
        have
          \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') =
            (if \<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q' then subtract 1 0 0 0 0 0 0 0 else None)\<close>
          for p Q p' Q' by simp
        from this[of p Q p' Q'] have
          \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') =
               subtract 1 0 0 0 0 0 0 0\<close> using p'_Q' by auto
        with expr_obs_phi[of \<alpha> \<phi>] show
          \<open>spectro_att_wins (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q)\<close>
          using weak_spectroscopy_game.Attack[OF attacker _ _ wina]
          by (smt (verit, best) option.sel option.simps(3))
      qed
      then show ?case by fastforce
    next
      case (Conj I \<psi>s)
      have main_case:
        \<open>\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Conj I \<psi>s = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q
        \<longrightarrow> spectro_att_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
      proof clarify
        fix p Q
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q\<close>
        hence distinctions: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          by auto
        hence inductive_wins: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q
            \<and> spectro_att_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Conjunct p q)\<close>
          using Conj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  hml_srbb_conj.distinguishes \<psi> p q
            \<and> spectro_att_wins (expr_pr_conjunct \<psi>) (Attacker_Conjunct p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>Q. \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> hml_srbb_conj.distinguishes (\<psi>qs q ) p q
            \<and> spectro_att_wins (expr_pr_conjunct (\<psi>qs q)) (Attacker_Conjunct p q)\<close>
          by (smt (verit))
        have conjuncts_present:
            \<open>\<forall>q\<in>Q. expr_pr_conjunct (\<psi>qs q) \<in> expr_pr_conjunct ` (\<psi>qs ` Q)\<close>
          using \<open>Q \<noteq> {}\<close> by blast
        define e' where \<open>e' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>qs ` Q))))\<close>
        from conjuncts_present have \<open>\<forall>q\<in>Q. (expr_pr_conjunct (\<psi>qs q)) \<le> e'\<close>
          unfolding e'_def
          by (metis SUP_upper energy.sel leq_components)
        with \<psi>qs_spec weak_spectroscopy_game.win_a_upwards_closure
          have clause_win: \<open>\<forall>q\<in>Q. spectro_att_wins e' (Attacker_Conjunct p q)\<close> by blast
        define eu' where \<open>eu' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` Q \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e' \<le> eu'\<close> unfolding e'_def eu'_def leq_components
          by (simp add: Sup_subset_mono image_mono)
        define e where \<open>e = E
          (modal_depth e')
          (br_conj_depth e')
          (1 + conj_depth e')
          (st_conj_depth e')
          (imm_conj_depth e')
          (pos_conjuncts e')
          (neg_conjuncts e')
          (neg_depth e')\<close>
        have \<open>e' = e - (E 0 0 1 0 0 0 0 0)\<close> unfolding e_def e'_def by simp
        hence \<open>Some e' = (subtract_fn 0 0 1 0 0 0 0 0) e\<close>
          by (auto, smt (verit) add_increasing2 e_def energy.sel
              energy_leq_cases i0_lb le_numeral_extra(4))
        have expr_lower: \<open>(E 0 0 1 0 0 0 0 0) \<le> expr_pr_inner (Conj I \<psi>s)\<close>
          using case_assms(1) subset_form by auto
        have eu'_comp: \<open>eu' = (expr_pr_inner (Conj I \<psi>s)) - (E 0 0 1 0 0 0 0 0)\<close>
          unfolding eu'_def
          by (auto simp add: bot_enat_def image_image)
        with expr_lower have eu'_characterization:
            \<open>Some eu' = (subtract_fn 0 0 1 0 0 0 0 0) (expr_pr_inner (Conj I \<psi>s))\<close>
          by presburger
        have \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
        \<longrightarrow> (\<exists>q\<in>Q. (Attacker_Conjunct p q) = g')
            \<and> spectroscopy_moves (Defender_Conj p Q) g' = Some (subtract_fn 0 0 1 0 0 0 0 0)\<close>
        proof clarify
          fix g' upd
          assume upd_def: \<open>spectroscopy_moves (Defender_Conj p Q) g' = Some upd\<close>
          hence \<open>\<And>px q. g' = Attacker_Conjunct px q
            \<Longrightarrow> p = px \<and> q \<in> Q \<and> upd = (subtract_fn 0 0 1 0 0 0 0 0)\<close>
            by (metis (mono_tags, lifting) local.conj_answer option.sel option.simps(3))
          with upd_def show
            \<open>(\<exists>q\<in>Q. Attacker_Conjunct p q = g')
            \<and> spectroscopy_moves (Defender_Conj p Q) g' = Some (subtract_fn 0 0 1 0 0 0 0 0)\<close>
            by (cases g', auto)
        qed
        hence \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
          \<longrightarrow> (\<exists>e'. (the (spectroscopy_moves (Defender_Conj p Q) g')) e = Some e'
                \<and> spectro_att_wins e' g')\<close>
          unfolding e_def
          using clause_win \<open>Some e' = (subtract_fn 0 0 1 0 0 0 0 0) e\<close> e_def by force
        hence \<open>spectro_att_wins e (Defender_Conj p Q)\<close>
          unfolding e_def using weak_spectroscopy_game.attacker_wins.Defense
          by auto
        moreover have \<open>e \<le> expr_pr_inner (Conj I \<psi>s)\<close>
          using \<open>e' \<le> eu'\<close> eu'_characterization \<open>Some e' = (subtract_fn 0 0 1 0 0 0 0 0) e\<close>
            expr_lower case_assms(1) subset_form e_def
          by (smt (verit, ccfv_threshold) eu'_comp add_diff_cancel_enat
              add_mono_thms_linordered_semiring(1) enat.simps(3) enat_defs(2) energy.sel
              expr_pr_inner.simps idiff_0_right inst_conj_depth_inner.simps(2) le_numeral_extra(4)
              leq_components minus_energy_def not_one_le_zero)
        ultimately show
          \<open>spectro_att_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
          using weak_spectroscopy_game.win_a_upwards_closure by blast
      qed
      moreover have
        \<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q
          \<longrightarrow> Q \<Zsurj>S Q  \<longrightarrow> spectro_att_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s))
                                            (Attacker_Delayed p Q)\<close>
      proof clarify
        fix p Q
        assume
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q\<close>
        hence
          \<open>spectro_att_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
          using main_case by blast
        moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p Q) = id_up\<close>
          by auto
        ultimately show
          \<open>spectro_att_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s))
                            (Attacker_Delayed p Q)\<close>
          by (metis weak_spectroscopy_game.attacker_wins_Ga_with_id_step option.discI
                option.sel spectroscopy_defender.simps(4))
      qed
      ultimately show ?case by fastforce
    next
      case (StableConj I \<psi>s)
      \<comment>\<open>The following proof is virtually the same as for \<open>Conj I \<psi>s\<close>\<close>
      have main_case: \<open>(\<forall>\<Psi>_I \<Psi> p Q. StableConj I \<psi>s = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q \<longrightarrow>
           (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> spectro_att_wins (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q))\<close>
      proof clarify
        fix p Q
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q\<close>
          \<open>\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q'\<close>
        hence distinctions: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          by (metis hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_from_def
                hml_srbb_inner_models.simps(3))
        hence inductive_wins: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q
            \<and> spectro_att_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Conjunct p q)\<close>
          using StableConj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  hml_srbb_conj.distinguishes \<psi> p q
            \<and> spectro_att_wins (expr_pr_conjunct \<psi>) (Attacker_Conjunct p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>Q. \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> hml_srbb_conj.distinguishes (\<psi>qs q ) p q
            \<and> spectro_att_wins (expr_pr_conjunct (\<psi>qs q)) (Attacker_Conjunct p q)\<close>
          by (smt (verit))
        have conjuncts_present:
            \<open>\<forall>q\<in>Q. expr_pr_conjunct (\<psi>qs q) \<in> expr_pr_conjunct ` (\<psi>qs ` Q)\<close>
          using \<open>Q \<noteq> {}\<close> by blast
        define e' where \<open>e' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>qs ` Q))))\<close>
        from conjuncts_present have \<open>\<forall>q\<in>Q. (expr_pr_conjunct (\<psi>qs q)) \<le> e'\<close> unfolding e'_def
          by (smt (verit, best) SUP_upper energy.sel energy.simps(3) energy_leq_cases image_iff)
        with \<psi>qs_spec weak_spectroscopy_game.win_a_upwards_closure
          have clause_win: \<open>\<forall>q\<in>Q. spectro_att_wins e' (Attacker_Conjunct p q)\<close> by blast
        define eu' where \<open>eu' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` Q \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e' \<le> eu'\<close> unfolding e'_def eu'_def
          by (simp add: Sup_subset_mono image_mono)
        define e where \<open>e = E
          (modal_depth e')
          (br_conj_depth e')
          (conj_depth e')
          (1 + st_conj_depth e')
          (imm_conj_depth e')
          (pos_conjuncts e')
          (neg_conjuncts e')
          (neg_depth e')\<close>
        have \<open>e' = e - (E 0 0 0 1 0 0 0 0)\<close> unfolding e_def e'_def by auto
        hence \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0) e\<close>
          by (metis e_def energy.sel energy_leq_cases i0_lb le_iff_add)
        have expr_lower: \<open>(E 0 0 0 1 0 0 0 0) \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
          using case_assms(1) subset_form by force
        have eu'_comp: \<open>eu' = (expr_pr_inner (StableConj I \<psi>s)) - (E 0 0 0 1 0 0 0 0)\<close>
          unfolding eu'_def using energy.sel
          by (auto simp add: bot_enat_def, (metis (no_types, lifting) SUP_cong image_image)+)
        with expr_lower have eu'_characterization:
            \<open>Some eu' = (subtract_fn 0 0 0 1 0 0 0 0) (expr_pr_inner (StableConj I \<psi>s))\<close>
          by presburger
        have \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None
        \<longrightarrow> (\<exists>q\<in>Q. (Attacker_Conjunct p q) = g')
              \<and> spectroscopy_moves (Defender_Stable_Conj p Q) g' = (subtract 0 0 0 1 0 0 0 0)\<close>
        proof clarify
          fix g' upd
          assume upd_def: \<open>spectroscopy_moves (Defender_Stable_Conj p Q) g' = Some upd\<close>
          hence \<open>\<And>px q. g' = Attacker_Conjunct px q
            \<Longrightarrow> p = px \<and> q \<in> Q \<and> upd = (subtract_fn 0 0 0 1 0 0 0 0)\<close>
            by (metis (no_types, lifting) local.conj_s_answer option.discI option.inject)
          with upd_def case_assms(1) show
            \<open>(\<exists>q\<in>Q. Attacker_Conjunct p q = g')
              \<and> spectroscopy_moves (Defender_Stable_Conj p Q) g' = (subtract 0 0 0 1 0 0 0 0)\<close>
            by (cases g', auto)
        qed
        hence \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None
          \<longrightarrow> (\<exists>e'. (the (spectroscopy_moves (Defender_Stable_Conj p Q) g')) e = Some e'
                \<and> spectro_att_wins e' g')\<close>
          unfolding e_def
          using clause_win \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0) e\<close> e_def by force
        hence \<open>spectro_att_wins e (Defender_Stable_Conj p Q)\<close>
          unfolding e_def
          by (auto simp add: weak_spectroscopy_game.attacker_wins.Defense)
        moreover have \<open>e \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
          using \<open>e' \<le> eu'\<close> eu'_characterization expr_lower case_assms(1) subset_form
          unfolding e_def eu'_comp minus_energy_def leq_components
          by (metis add_diff_assoc_enat add_diff_cancel_enat add_left_mono enat.simps(3)
                enat_defs(2) energy.sel idiff_0_right)
        ultimately show
            \<open>spectro_att_wins (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q)\<close>
          using weak_spectroscopy_game.win_a_upwards_closure  by blast
      qed
      moreover have \<open>(\<forall>p Q. Q \<noteq> {}
        \<longrightarrow> hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
        \<longrightarrow> spectro_att_wins (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q))\<close>
      proof clarify
        \<comment> \<open>This is where things are more complicated than in the Conj-case.
            (We have to differentiate situations where the stability requirement
            finishes the distinction.)\<close>
        fix p Q
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q\<close>
          \<open>\<forall>q'\<in>Q. \<exists>q\<in>Q. q \<Zsurj> q'\<close>
          \<open>\<forall>q\<in>Q. \<forall>q'. q \<Zsurj> q' \<longrightarrow> q' \<in> Q\<close>
        define Q' where \<open>Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}\<close>
        with case_assms(2) have Q'_spec:
            \<open>hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q'\<close> \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close>
          unfolding hml_srbb_inner.distinguishes_from_def by auto
        hence move:
            \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = id_up\<close>
          unfolding Q'_def by auto
        show \<open>spectro_att_wins (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q)\<close>
        proof (cases \<open>Q' = {}\<close>)
          case True
          hence
            \<open>spectroscopy_moves (Defender_Stable_Conj p Q') (Defender_Conj p {})
            = (subtract 0 0 0 1 0 0 0 0)\<close> by auto
          moreover have
            \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q') g' \<noteq> None
              \<longrightarrow> g' = (Defender_Conj p {})\<close>
          proof clarify
            fix g' u
            assume
              \<open>spectroscopy_moves (Defender_Stable_Conj p Q') g' = Some u\<close>
            with True show \<open>g' = Defender_Conj p {}\<close>
              by (induct g', auto, metis option.discI, metis empty_iff option.discI)
          qed
          ultimately have win_transfer:
            \<open>\<forall>e. E 0 0 0 1 0 0 0 0 \<le> e
              \<and> spectro_att_wins (e - E 0 0 0 1 0 0 0 0) (Defender_Conj p {})
              \<longrightarrow> spectro_att_wins e (Defender_Stable_Conj p Q')\<close>
            using weak_spectroscopy_game.attacker_wins.Defense
            by (smt (verit, ccfv_SIG)  option.sel spectroscopy_defender.simps(7))
          have \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p {}) g' = None\<close>
          proof
            fix g'
            show \<open>spectroscopy_moves (Defender_Conj p {}) g' = None\<close> by (induct g', auto)
          qed
          hence \<open>\<forall>e. spectro_att_wins e (Defender_Conj p {})\<close>
            using weak_spectroscopy_game.attacker_wins.Defense by fastforce
          moreover have
              \<open>\<forall>e. (subtract_fn 0 0 0 1 0 0 0 0) e \<noteq> None \<longrightarrow> e \<ge> (E 0 0 0 1 0 0 0 0)\<close>
            using minus_energy_def by presburger
          ultimately have \<open>\<forall>e. e \<ge> (E 0 0 0 1 0 0 0 0)
            \<longrightarrow> spectro_att_wins e (Defender_Stable_Conj p Q')\<close>
            using win_transfer by presburger
          moreover have \<open>expr_pr_inner (StableConj I \<psi>s) \<ge> (E 0 0 0 1 0 0 0 0)\<close>
            by auto
          ultimately show ?thesis
            by (metis move weak_spectroscopy_game.attacker_wins_Ga_with_id_step option.discI
                option.sel spectroscopy_defender.simps(4))
        next
          case False
          with move show ?thesis
            using main_case Q'_spec weak_spectroscopy_game.attacker_wins_Ga_with_id_step
            unfolding Q'_def
            by (metis (mono_tags, lifting) mem_Collect_eq option.distinct(1) option.sel
                spectroscopy_defender.simps(4))
        qed
      qed
      ultimately show ?case by blast
    next
      case (BranchConj \<alpha> \<phi> I \<psi>s)
      have main_case:
        \<open>\<forall>p Q p' Q_\<alpha>.
          hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> p \<mapsto>a \<alpha> p'
          \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow> Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)
          \<longrightarrow> spectro_att_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s))
              (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
      proof ((rule allI)+, (rule impI)+)
        fix p Q p' Q_\<alpha>
        assume case_assms:
          \<open>hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q\<close>
          \<open>p \<mapsto>a \<alpha> p'\<close>
          \<open>p' \<Turnstile>SRBB \<phi>\<close>
          \<open>Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)\<close>
        from case_assms(1) have distinctions:
          \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)).
            \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          using srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch
            hml_srbb_inner.distinction_unlifting unfolding hml_srbb_inner.distinguishes_def
          by (metis Int_Collect)
        hence inductive_wins: \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)).
          \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q
            \<and> spectro_att_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Conjunct p q)\<close>
          using BranchConj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  hml_srbb_conj.distinguishes \<psi> p q
            \<and> spectro_att_wins (expr_pr_conjunct \<psi>) (Attacker_Conjunct p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)).
            \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> hml_srbb_conj.distinguishes (\<psi>qs q ) p q
              \<and> spectro_att_wins (expr_pr_conjunct (\<psi>qs q)) (Attacker_Conjunct p q)\<close>
          by (smt (verit))
        have conjuncts_present:
          \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)). expr_pr_conjunct (\<psi>qs q)
            \<in> expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)))\<close>
          by blast
        define e'0 where \<open>e'0 = E
          (Sup (modal_depth   ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (conj_depth ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (neg_depth ` (expr_pr_conjunct `
            (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))\<close>
        from conjuncts_present have branch_answer_bound:
            \<open>\<forall>q \<in> Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>). expr_pr_conjunct (\<psi>qs q) \<le> e'0\<close>
          using e'0_def SUP_upper energy.sel energy.simps(3) energy_leq_cases image_iff
          by (smt (z3))
        with \<psi>qs_spec weak_spectroscopy_game.win_a_upwards_closure have
          conj_wins: \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)).
            spectro_att_wins e'0 (Attacker_Conjunct p q)\<close> by blast
        define eu'0 where \<open>eu'0 = E
          (Sup (modal_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (st_conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (imm_conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (pos_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)) \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e'0 \<le> eu'0\<close> unfolding e'0_def eu'0_def
          by (metis (mono_tags, lifting) Sup_subset_mono energy.sel energy_leq_cases image_mono)
        have no_q_way: \<open>\<forall>q\<in>Q_\<alpha>. \<nexists>q'. q \<mapsto> \<alpha> q' \<and> hml_srbb_models q' \<phi>\<close>
          using case_assms(4)
          by fastforce
        define Q' where \<open>Q' \<equiv> (soft_step_set Q_\<alpha> \<alpha>)\<close>
        hence \<open>distinguishes_from \<phi> p' Q'\<close>
          using case_assms(2,3) no_q_way soft_step_set_is_soft_step_set mem_Collect_eq
          unfolding case_assms(4)
          by fastforce
        with BranchConj have win_a_branch:
          \<open>spectro_att_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q')\<close>
          using distinction_implies_winning_budgets_empty_Q by (cases \<open>Q' = {}\<close>) auto
        have \<open>expr_pr_inner (Obs \<alpha> \<phi>) \<ge> (E 1 0 0 0 0 0 0 0)\<close> by auto
        hence \<open>(subtract_fn 1 0 0 0 0 0 0 0) (expr_pr_inner (Obs \<alpha> \<phi>))
            = Some (expressiveness_price \<phi>)\<close>
          using expr_obs_phi by auto
        with win_a_branch have win_a_step:
          \<open>spectro_att_wins (the ((subtract_fn 1 0 0 0 0 0 0 0) (expr_pr_inner (Obs \<alpha> \<phi>))))
                            (Attacker_Immediate p' Q')\<close> by auto
        define e' where \<open>e' = E
          (Sup (modal_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (br_conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (st_conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (imm_conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup ({1 + modal_depth_srbb \<phi>}
             \<union> (pos_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I))))))
          (Sup (neg_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (neg_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))\<close>
        have \<open>eu'0 \<le> e'\<close> unfolding e'_def eu'0_def
          by (auto, meson sup.cobounded2 sup.coboundedI2)
        have \<open>spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
              = Some (subtract_fn 1 0 0 0 0 0 0 0)\<close> by simp
        with win_a_step weak_spectroscopy_game.attacker_wins.Attack have obs_later_win:
            \<open>spectro_att_wins (expr_pr_inner (Obs \<alpha> \<phi>)) (Attacker_Branch p' Q')\<close>
          by force
        hence e'_win: \<open>spectro_att_wins e' (Attacker_Branch p' Q')\<close>
          unfolding e'_def using weak_spectroscopy_game.win_a_upwards_closure
          by auto
        have depths: \<open>1 + modal_depth_srbb \<phi> = modal_depth (expr_pr_inner (Obs \<alpha> \<phi>))\<close> by simp
        have six_e': \<open>pos_conjuncts e' = Sup ({1 + modal_depth_srbb \<phi>}
            \<union> (pos_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))\<close>
          using energy.sel(6) unfolding e'_def by blast
        hence six_e'_simp: \<open>pos_conjuncts e' = Sup ({1 + modal_depth_srbb \<phi>}
            \<union> (pos_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
          by (auto simp add: modal_depth_dominates_pos_conjuncts add_increasing
              sup.absorb2 sup.coboundedI1)
        hence \<open>pos_conjuncts e' \<le> modal_depth e'\<close>
          unfolding e'_def
          by (auto, smt (verit) SUP_mono energy.sel(1) energy.sel(6) image_iff
                    modal_depth_dominates_pos_conjuncts sup.coboundedI2)
        hence \<open>modal_depth (the (min1_6 e')) = (pos_conjuncts e')\<close>
          by simp
        with six_e' have min_e'_def: \<open>min1_6 e' = Some (E
          (Sup ({1 + modal_depth_srbb \<phi>} \<union> pos_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (st_conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (imm_conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup ({1 + modal_depth_srbb \<phi>}
              \<union> (pos_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I))))))
          (Sup (neg_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (neg_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I))))))\<close>
          using e'_def min1_6_def six_e'_simp
          by (smt (z3) energy.case_eq_if energy.sel min_1_6_simps(1))
        hence \<open>expr_pr_inner (Obs \<alpha> \<phi>) \<le> the (min1_6 e')\<close>
          by force
        hence obs_win: \<open>spectro_att_wins (the (min1_6 e')) (Attacker_Branch p' Q')\<close>
          using obs_later_win weak_spectroscopy_game.win_a_upwards_closure  by blast
        define e where \<open>e = E
          (modal_depth e')
          (1 + br_conj_depth e')
          (1 + conj_depth e')
          (st_conj_depth e')
          (imm_conj_depth e')
          (pos_conjuncts e')
          (neg_conjuncts e')
          (neg_depth e')\<close>
        have \<open>e' = e - (E 0 1 1 0 0 0 0 0)\<close> unfolding e_def e'_def by auto
        hence e'_comp: \<open>Some e' = (subtract_fn 0 1 1 0 0 0 0 0) e\<close>
          by (metis e_def energy.sel energy_leq_cases i0_lb le_iff_add)
        have expr_lower: \<open>(E 0 1 1 0 0 0 0 0) \<le> expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)\<close>
          using case_assms subset_form by auto
        have e'_minus: \<open>e' = expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s) - E 0 1 1 0 0 0 0 0\<close>
          unfolding e'_def using energy.sel
          by (auto simp add: bot_enat_def sup.left_commute,
             (metis (no_types, lifting) SUP_cong image_image)+)
        with expr_lower have e'_characterization:
            \<open>Some e' = (subtract_fn 0 1 1 0 0 0 0 0) (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s))\<close>
          by presburger
        have moves: \<open>\<forall>g'. spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' \<noteq> None
        \<longrightarrow> (((Attacker_Branch p' Q' = g')
            \<and> (spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g'
                = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)))
          \<or> ((\<exists>q\<in>(Q - Q_\<alpha>). Attacker_Conjunct p q = g'
            \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g'
                = (subtract 0 1 1 0 0 0 0 0))))\<close>
        proof clarify
          fix g' u
          assume no_subtr_move:
            \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = Some u\<close>
            \<open>\<not> (\<exists>q\<in>Q - Q_\<alpha>. Attacker_Conjunct p q = g'
                  \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g'
                    = subtract 0 1 1 0 0 0 0 0)\<close>
          hence \<open>g' = Attacker_Branch p' Q'\<close>
            unfolding Q'_def using soft_step_set_is_soft_step_set no_subtr_move local.br_answer
            by (cases g', auto, (metis (no_types, lifting)  option.discI)+)
          moreover have \<open>Attacker_Branch p' Q' = g'
              \<longrightarrow> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g'
                  = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)\<close>
            unfolding Q'_def using soft_step_set_is_soft_step_set by auto
          ultimately show \<open>Attacker_Branch p' Q' = g'
              \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g'
                = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)\<close>
            by blast
        qed
        have obs_e:
          \<open>\<exists>e'. (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6) e = Some e'
            \<and> spectro_att_wins e' (Attacker_Branch p' Q')\<close>
          using obs_win e'_comp min_e'_def
          by (smt (verit, best) bind.bind_lunit min_1_6_some option.collapse)
        have \<open>\<forall>q\<in>(Q - Q_\<alpha>).
          spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) (Attacker_Conjunct p q)
          = (subtract 0 1 1 0 0 0 0 0)
          \<longrightarrow> spectro_att_wins e'0 (Attacker_Conjunct p q)\<close>
          using conj_wins \<open>eu'0 \<le> e'\<close> case_assms(4) by blast
        with obs_e moves have move_wins:
          \<open>\<forall>g'. spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' \<noteq> None
          \<longrightarrow> (\<exists>e'. (the (spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g')) e
                    = Some e' \<and> spectro_att_wins e' g')\<close>
          using  \<open>eu'0 \<le> e'\<close> e'_comp \<open>e'0 \<le> eu'0\<close> weak_spectroscopy_game.win_a_upwards_closure
         by (smt (verit, ccfv_SIG) option.sel)
        moreover have \<open>expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s) = e\<close>
          using e'_characterization e'_minus unfolding e_def by force
        ultimately show \<open>spectro_att_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s))
                                          (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
          using weak_spectroscopy_game.attacker_wins.Defense spectroscopy_defender.simps(5)
          by metis
      qed
      moreover have
        \<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q
           \<longrightarrow> spectro_att_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q)\<close>
      proof clarify
        fix p Q
        assume case_assms:
          \<open>hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q\<close>
        from case_assms(1) obtain p' where p'_spec: \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close>
          unfolding hml_srbb_inner.distinguishes_from_def
              and distinguishes_def by auto
        define Q_\<alpha> where \<open>Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)\<close>
        have \<open>spectro_att_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s))
                               (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
          using main_case case_assms(1) p'_spec Q_\<alpha>_def by blast
        moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q)
                                          (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) = id_up\<close>
          using p'_spec Q_\<alpha>_def by auto
        ultimately show
            \<open>spectro_att_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q)\<close>
          using weak_spectroscopy_game.attacker_wins_Ga_with_id_step by auto
      qed
      ultimately show ?case by blast
    next
      case (Pos \<chi>)
      show ?case
      proof clarify
        fix p q
        assume case_assms: \<open>hml_srbb_conj.distinguishes (Pos \<chi>) p q\<close>
        then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>p' \<in> hml_srbb_inner.model_set \<chi>\<close>
          unfolding hml_srbb_conj.distinguishes_def by auto
        moreover have q_reach: \<open>silent_reachable_set {q} \<inter> hml_srbb_inner.model_set \<chi> = {}\<close>
          using case_assms sreachable_set_is_sreachable
          unfolding hml_srbb_conj.distinguishes_def by force
        ultimately have distinction:
            \<open>hml_srbb_inner.distinguishes_from \<chi> p' (silent_reachable_set {q})\<close>
          unfolding hml_srbb_inner.distinguishes_from_def by auto
        have q_reach_nonempty:
            \<open>silent_reachable_set {q} \<noteq> {}\<close>
            \<open>silent_reachable_set {q} \<Zsurj>S silent_reachable_set {q} \<close>
          unfolding silent_reachable_set_def
          using silent_reachable.intros(1) silent_reachable_trans by auto
        hence \<open>spectro_att_wins (expr_pr_inner \<chi>)
                                (Attacker_Delayed p' (silent_reachable_set {q}))\<close>
          using distinction Pos by blast
        from p'_spec(1) this have
            \<open>spectro_att_wins (expr_pr_inner \<chi>) (Attacker_Delayed p (silent_reachable_set {q}))\<close>
          by (induct, auto,
              metis weak_spectroscopy_game.attacker_wins_Ga_with_id_step procrastination
                option.distinct(1) option.sel spectroscopy_defender.simps(4))
        moreover have \<open>spectroscopy_moves (Attacker_Conjunct p q)
            (Attacker_Delayed p (silent_reachable_set {q})) = Some min1_6\<close>
          using q_reach_nonempty sreachable_set_is_sreachable by fastforce
        moreover have \<open>the (min1_6 (expr_pr_conjunct (Pos \<chi>))) \<ge> expr_pr_inner \<chi>\<close>
          unfolding min1_6_def
          by (auto simp add: energy_leq_cases modal_depth_dominates_pos_conjuncts)
        ultimately show \<open>spectro_att_wins (expr_pr_conjunct (Pos \<chi>)) (Attacker_Conjunct p q)\<close>
          using weak_spectroscopy_game.attacker_wins.simps
            weak_spectroscopy_game.win_a_upwards_closure  spectroscopy_defender.simps(3)
          by (metis (no_types, lifting) min_1_6_some option.discI option.exhaust_sel option.sel)
      qed
    next
      case (Neg \<chi>)
      show ?case
      proof clarify
        fix p q
        assume case_assms: \<open>hml_srbb_conj.distinguishes (Neg \<chi>) p q\<close>
        then obtain q' where q'_spec: \<open>q \<Zsurj> q'\<close> \<open>q' \<in> hml_srbb_inner.model_set \<chi>\<close>
          unfolding hml_srbb_conj.distinguishes_def by auto
        moreover have p_reach: \<open>silent_reachable_set {p} \<inter> hml_srbb_inner.model_set \<chi> = {}\<close>
          using case_assms sreachable_set_is_sreachable
          unfolding hml_srbb_conj.distinguishes_def by force
        ultimately have distinction:
            \<open>hml_srbb_inner.distinguishes_from \<chi> q' (silent_reachable_set {p})\<close>
          unfolding hml_srbb_inner.distinguishes_from_def by auto
        have \<open>p \<noteq> q\<close> using case_assms unfolding hml_srbb_conj.distinguishes_def by auto
        have p_reach_nonempty:
            \<open>silent_reachable_set {p} \<noteq> {}\<close>
            \<open>silent_reachable_set {p} \<Zsurj>S silent_reachable_set {p}\<close>
          unfolding silent_reachable_set_def
          using silent_reachable.intros(1) silent_reachable_trans by auto
        hence \<open>spectro_att_wins (expr_pr_inner \<chi>)
                                (Attacker_Delayed q' (silent_reachable_set {p}))\<close>
          using distinction Neg by blast
        from q'_spec(1) this have
            \<open>spectro_att_wins (expr_pr_inner \<chi>) (Attacker_Delayed q (silent_reachable_set {p}))\<close>
          by (induct, auto,
              metis weak_spectroscopy_game.attacker_wins_Ga_with_id_step procrastination
                option.distinct(1) option.sel spectroscopy_defender.simps(4))
        moreover have \<open>spectroscopy_moves (Attacker_Conjunct p q)
              (Attacker_Delayed q (silent_reachable_set {p}))
             = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)\<close>
          using p_reach_nonempty sreachable_set_is_sreachable \<open>p \<noteq> q\<close> by fastforce
        moreover have \<open>the (min1_7 (expr_pr_conjunct (Neg \<chi>) - E 0 0 0 0 0 0 0 1))
            \<ge> (expr_pr_inner \<chi>)\<close>
          using min1_7_def energy_leq_cases
          by (simp add: modal_depth_dominates_neg_conjuncts)
        moreover from this have
          \<open>\<exists>e'. Some e' = (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)
             (expr_pr_conjunct (Neg \<chi>)) \<and> e' \<ge> (expr_pr_inner \<chi>)\<close>
          unfolding min_1_7_subtr_simp by auto
        ultimately show \<open>spectro_att_wins (expr_pr_conjunct (Neg \<chi>)) (Attacker_Conjunct p q)\<close>
          using weak_spectroscopy_game.attacker_wins.Attack
            weak_spectroscopy_game.win_a_upwards_closure  spectroscopy_defender.simps(3)
          by (metis (no_types, lifting) option.discI option.sel)
      qed
    qed
  qed
  thus ?thesis
    by (metis assms distinction_implies_winning_budgets_empty_Q)
qed

end

end