(* License: LGPL *)

subsection \<open>Strategy Formulas\<close>

theory Strategy_Formulas
    imports Spectroscopy_Game Expressiveness_Price
begin

text \<open>
  Strategy formulas express attacker strategies in HML. They bridge between HML formulas, the spectroscopy game and winning budgets. We show that, if some energy \<open>e\<close> suffices for the attacker to win, there exists a strategy formula with expressiveness price \<open>\<le> e\<close>. We also prove that this formula actually distinguishes the processes of the attacker position.
\<close>

context lts_tau
begin

inductive
  strategy_formula
  :: \<open>('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool\<close>
and
  strategy_formula_inner
  :: \<open>('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool\<close>
and
  strategy_formula_conjunct
  :: \<open>('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool\<close>
where
  delay:  \<open>strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)\<close>
    if \<open>\<exists>Q'.
      spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') = id_up
      \<and> spectro_att_wins e (Attacker_Delayed p Q')
      \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>\<close>
|
  procrastination:  \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close>
    if \<open>\<exists>p'.
        spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = id_up
        \<and> spectro_att_wins e (Attacker_Delayed p' Q)
        \<and> strategy_formula_inner (Attacker_Delayed p' Q) e \<chi>\<close>
|
  observation:  \<open>strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)\<close>
    if \<open>\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')
       = (subtract 1 0 0 0 0 0 0 0)
        \<and> spectro_att_wins (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q')
        \<and> strategy_formula (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<phi>
        \<and> p \<mapsto>a\<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q'\<close>
|
  early_conj:  \<open>strategy_formula (Attacker_Immediate p Q) e \<phi>\<close>
    if \<open>\<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')
          = (subtract 0 0 0 0 1 0 0 0)
            \<and> spectro_att_wins (e - E 0 0 0 0 1 0 0 0) (Defender_Conj p' Q')
            \<and> strategy_formula (Defender_Conj p' Q') (e - E 0 0 0 0 1 0 0 0) \<phi>\<close>
|
  late_conj:  \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close>
    if \<open>(spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p Q)
       = id_up \<and> (spectro_att_wins e (Defender_Conj p Q))
         \<and> strategy_formula_inner (Defender_Conj p Q) e \<chi>)\<close>
|
  conj:  \<open>strategy_formula_inner (Defender_Conj p Q) e (Conj Q \<Phi>)\<close>
    if \<open>\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p q)
        = (subtract 0 0 1 0 0 0 0 0)
          \<and> (spectro_att_wins (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Conjunct p q))
          \<and> strategy_formula_conjunct (Attacker_Conjunct p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)\<close>
|
  imm_conj:  \<open>strategy_formula (Defender_Conj p Q) e (ImmConj Q \<Phi>)\<close>
    if \<open>\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p q)
        = (subtract 0 0 1 0 0 0 0 0)
          \<and> (spectro_att_wins (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Conjunct p q))
          \<and> strategy_formula_conjunct (Attacker_Conjunct p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)\<close>
|
  pos:  \<open>strategy_formula_conjunct (Attacker_Conjunct p q) e (Pos \<chi>)\<close>
    if \<open>(\<exists>Q'. spectroscopy_moves (Attacker_Conjunct p q) (Attacker_Delayed p Q')
      = Some min1_6 \<and> spectro_att_wins (the (min1_6 e)) (Attacker_Delayed p Q')
        \<and> strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>)\<close>
|
  neg:  \<open>strategy_formula_conjunct (Attacker_Conjunct p q) e (Neg \<chi>)\<close>
    if \<open>\<exists>P'. (spectroscopy_moves (Attacker_Conjunct p q) (Attacker_Delayed q P')
      = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)
        \<and> spectro_att_wins (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed q P'))
        \<and> strategy_formula_inner (Attacker_Delayed q P')
                                 (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<chi>\<close>
|
  stable:  \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close>
    if \<open>(\<exists>Q'. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q')
      = id_up \<and> spectro_att_wins e (Defender_Stable_Conj p Q')
        \<and> strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi>)\<close>
|
  stable_conj:  \<open>strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)\<close>
    if \<open>\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Conjunct p q)
      = (subtract 0 0 0 1 0 0 0 0)
        \<and> spectro_att_wins (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Conjunct p q)
        \<and> strategy_formula_conjunct (Attacker_Conjunct p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q)\<close>
|
  branch:  \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close>
    if \<open>\<exists>p' Q' \<alpha> Q\<alpha>. spectroscopy_moves (Attacker_Delayed p Q)
                      (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = id_up
          \<and> spectro_att_wins e (Defender_Branch p \<alpha> p' Q' Q\<alpha>)
          \<and> strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi>\<close>
|
  branch_conj:
    \<open>strategy_formula_inner (Defender_Branch p \<alpha> p' Q Q\<alpha>) e (BranchConj \<alpha> \<phi> Q \<Phi>)\<close>
    if \<open>\<exists>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p' Q')
          = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)
            \<and> spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
            = subtract 1 0 0 0 0 0 0 0
            \<and> (spectro_att_wins (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0)
                  (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q')
                               (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0) \<phi>\<close>
        \<open>\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Conjunct p q)
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> spectro_att_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Conjunct p q)
          \<and> strategy_formula_conjunct (Attacker_Conjunct p q) (e - E 0 1 1 0 0 0 0 0) (\<Phi> q)\<close>

lemma winning_budget_implies_strategy_formula:
  assumes
    \<open>spectro_att_wins e g\<close>
  shows
    \<open>case g of
      Attacker_Immediate p Q \<Rightarrow> \<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e
    | Attacker_Delayed p Q \<Rightarrow> \<exists>\<chi>. strategy_formula_inner g e \<chi> \<and> expr_pr_inner \<chi> \<le> e
    | Attacker_Conjunct p q \<Rightarrow>
        \<exists>\<psi>. strategy_formula_conjunct g e \<psi> \<and> expr_pr_conjunct \<psi> \<le> e
    | Defender_Conj p Q \<Rightarrow> \<exists>\<chi>. strategy_formula_inner g e \<chi> \<and> expr_pr_inner \<chi> \<le> e
    | Defender_Stable_Conj p Q \<Rightarrow> \<exists>\<chi>. strategy_formula_inner g e \<chi>  \<and> expr_pr_inner \<chi> \<le> e
    | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow>
        \<exists>\<chi>. strategy_formula_inner g e \<chi> \<and> expr_pr_inner \<chi> \<le> e
    | Attacker_Branch p Q \<Rightarrow>
        \<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (e - E 1 0 0 0 0 0 0 0) \<phi>
          \<and> expressiveness_price \<phi> \<le> e - E 1 0 0 0 0 0 0 0\<close>
  using assms
proof(induction rule: weak_spectroscopy_game.attacker_wins.induct)
  case (Attack g g' e e')
  then show ?case
  proof (induct g)
    case (Attacker_Immediate p Q)
    hence move: \<open>
      (\<exists>p Q. g' = Defender_Conj p Q) \<longrightarrow>
        (\<exists>\<phi>. strategy_formula_inner g' (the (weak_spectroscopy_game.weight g g' e)) \<phi>
          \<and> expr_pr_inner \<phi> \<le> weak_spectroscopy_game.updated g g' e) \<and>
      (\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
        (\<exists>\<phi>. strategy_formula_inner g' (the (weak_spectroscopy_game.weight g g' e)) \<phi>
          \<and> expr_pr_inner \<phi> \<le> weak_spectroscopy_game.updated g g' e)\<close>
      using weak_spectroscopy_game.attacker_wins.cases
      by simp
    from move Attacker_Immediate have move_cases:
        \<open>(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Conj p' Q'))\<close>
      using spectroscopy_moves.simps
      by (smt (verit, del_insts) spectroscopy_defender.elims(2,3))
    show ?case using move_cases
    proof(rule disjE)
      assume \<open>\<exists>p' Q'. g' = Attacker_Delayed p' Q'\<close>
      then obtain p' Q' where g'_att_del: \<open>g' = Attacker_Delayed p' Q'\<close> by blast
      have e_comp:
        \<open>the (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')) e
          = Some e\<close>
        by (smt (verit, ccfv_threshold) Spectroscopy_Game.lts_tau.delay g'_att_del
              Attacker_Immediate move option.exhaust_sel option.inject)
      have \<open>p' = p\<close>
        by (metis g'_att_del Attacker_Immediate(2) spectroscopy_moves.simps(1))
      moreover have \<open>(spectro_att_wins e (Attacker_Delayed p Q'))\<close>
        using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>p' = p\<close> Attacker_Immediate
          weak_spectroscopy_game.win_a_upwards_closure e_comp
        by simp
      ultimately have \<open>(\<exists>\<chi>.
        strategy_formula_inner g'
          (the (weak_spectroscopy_game.weight (Attacker_Immediate p Q) g' e)) \<chi> \<and>
        expr_pr_inner \<chi> \<le> weak_spectroscopy_game.updated (Attacker_Immediate p Q) g' e)\<close>
        using g'_att_del Attacker_Immediate by fastforce
      then obtain \<chi> where
          \<open>(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)\<close>
        using \<open>p' = p\<close> e_comp g'_att_del by auto
      hence \<open>\<exists>Q'. spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') = id_up
        \<and> (spectro_att_wins e (Attacker_Delayed p Q'))
        \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>\<close>
        using g'_att_del
        by (smt (verit) Spectroscopy_Game.lts_tau.delay
              \<open>spectro_att_wins e (Attacker_Delayed p Q')\<close> Attacker_Immediate)
      hence \<open>strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)\<close>
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay by blast
      moreover have \<open>expressiveness_price (Internal \<chi>) \<le> e\<close>
        using \<open>(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)\<close>
        by auto
      ultimately show ?case by auto
    next
      assume \<open>\<exists>p' Q'. g' = Defender_Conj p' Q'\<close>
      then obtain p' Q' where g'_def_conj: \<open>g' = Defender_Conj p' Q'\<close> by blast
      hence M: \<open>spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')
          = (subtract 0 0 0 0 1 0 0 0)\<close>
        using local.f_or_early_conj Attacker_Immediate by presburger
      hence Qp': \<open>Q\<noteq>{}\<close> \<open>Q = Q'\<close> \<open>p = p'\<close>
        using Attack.hyps(2) Attacker_Immediate g'_def_conj local.f_or_early_conj by metis+
      from M have M':
        \<open>weak_spectroscopy_game.updated (Attacker_Immediate p Q) (Defender_Conj p' Q') e
                = e - (E 0 0 0 0 1 0 0 0)\<close>
        using Attack.hyps(3) g'_def_conj Attacker_Immediate
        by (smt (verit) option.distinct(1) option.sel)
      hence M'': \<open>(spectro_att_wins (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q'))\<close>
        using g'_def_conj Qp' Attacker_Immediate weak_spectroscopy_game.win_a_upwards_closure
        by force
      with g'_def_conj have IH_case: \<open>\<exists>\<chi>.
        strategy_formula_inner g'
          (weak_spectroscopy_game.updated (Attacker_Immediate p Q) g' e) \<chi>
        \<and> expr_pr_inner \<chi> \<le> weak_spectroscopy_game.updated (Attacker_Immediate p Q) g' e\<close>
        using Attacker_Immediate by auto
      hence \<open>\<exists>\<chi>. strategy_formula_inner (Defender_Conj p Q) (e - E 0 0 0 0 1 0 0 0) \<chi>
          \<and>  expr_pr_inner \<chi> \<le> (e - E 0 0 0 0 1 0 0 0)\<close>
        using \<open>spectro_att_wins (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q')\<close> IH_case
          Qp' M' g'_def_conj by auto
      then obtain \<chi> where S:
          \<open>strategy_formula_inner (Defender_Conj p Q) (e - E 0 0 0 0 1 0 0 0) \<chi>
          \<and> expr_pr_inner \<chi> \<le> e - E 0 0 0 0 1 0 0 0\<close>
        by blast
      hence \<open>\<exists>\<psi>. \<chi> = Conj Q \<psi>\<close>
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj
           g'_def_conj Attacker_Immediate
        unfolding Qp'
        by (smt (verit) spectroscopy_moves.simps(64,70) spectroscopy_position.distinct(17)
              spectroscopy_position.inject(5) strategy_formula_inner.cases)
      then obtain \<psi> where \<open>\<chi> = Conj Q \<psi>\<close> by auto
      hence \<open>strategy_formula (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) (ImmConj Q \<psi>)\<close>
        using S strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj
          strategy_formula_strategy_formula_inner_strategy_formula_conjunct.imm_conj
          Qp' Attacker_Immediate unfolding g'_def_conj
        by (smt (verit) lts_tau.spectroscopy_moves.simps(70) hml_srbb_inner.inject(2)
              spectroscopy_position.distinct(17,37) strategy_formula_inner.cases)
      hence SI: \<open>strategy_formula (Attacker_Immediate p Q) e (ImmConj Q \<psi>)\<close>
        using delay early_conj Qp'
        by (metis (no_types, lifting) M'' local.f_or_early_conj)
      have \<open>expr_pr_inner (Conj Q \<psi>) \<le> (e - (E 0 0 0 0 1 0 0 0))\<close>
         using S \<open>\<chi> = Conj Q \<psi>\<close> by simp
      hence \<open>expressiveness_price (ImmConj Q \<psi>) \<le> e\<close> using expr_imm_conj Qp'
        by (smt (verit) M g'_def_conj Attacker_Immediate option.sel option.simps(3))
      thus ?thesis using SI by auto
    qed
  next
    case (Attacker_Branch p Q)
    hence g'_def: \<open>g' = Attacker_Immediate p Q\<close> using br_acct
      by (induct g', auto) (metis option.discI)+
    hence move:
      \<open>spectroscopy_moves (Attacker_Branch p Q) g' = subtract 1 0 0 0 0 0 0 0\<close> by simp
    then obtain \<phi> where
      \<open>strategy_formula g' (weak_spectroscopy_game.updated (Attacker_Branch p Q) g' e) \<phi> \<and>
       expressiveness_price \<phi> \<le> weak_spectroscopy_game.updated (Attacker_Branch p Q) g' e\<close>
      using Attacker_Branch g'_def by auto
    hence \<open>(strategy_formula (Attacker_Immediate p Q) (e - E 1 0 0 0 0 0 0 0) \<phi>)
        \<and> expressiveness_price \<phi> \<le> e - E 1 0 0 0 0 0 0 0\<close>
      using move Attacker_Branch unfolding g'_def
      by (smt (verit, del_insts) option.distinct(1) option.sel)
    then show ?case by auto
  next
    case (Attacker_Conjunct p q)
    hence \<open>(\<exists>p' Q'. g' = (Attacker_Delayed p' Q'))\<close>
      using Attack.hyps spectroscopy_moves.simps
      by (smt (verit, del_insts) spectroscopy_defender.elims(1))
    then obtain p' Q' where
      g'_att_del: \<open>g' = Attacker_Delayed p' Q'\<close> by blast
    show ?case
    proof(cases \<open>p = p'\<close>)
      case True
      hence \<open>{q} \<Zsurj>S Q'\<close>
        using g'_att_del local.pos_neg_clause Attacker_Conjunct by presburger
      hence post_win:
        \<open>(the (spectroscopy_moves (Attacker_Conjunct p q) g') e) = min1_6 e\<close>
         \<open>(spectro_att_wins (the (min1_6 e)) (Attacker_Delayed p Q'))\<close>
        using \<open>{q} \<Zsurj>S Q'\<close> Attacker_Conjunct weak_spectroscopy_game.win_a_upwards_closure
        unfolding True g'_att_del
        by auto
      then obtain \<chi> where \<chi>_spec:
        \<open>strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>\<close>
        \<open>expr_pr_inner \<chi> \<le> the (min1_6 e)\<close>
        using Attacker_Conjunct Attack True post_win unfolding g'_att_del
        by (smt (verit) option.sel spectroscopy_position.simps(51))
      hence
        \<open>spectroscopy_moves (Attacker_Conjunct p q) (Attacker_Delayed p Q') = Some min1_6\<close>
        \<open>spectro_att_wins (the (min1_6 e)) (Attacker_Delayed p Q')\<close>
        \<open>strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>\<close>
        using \<open>{q} \<Zsurj>S Q'\<close> local.pos_neg_clause post_win by auto
      hence \<open>strategy_formula_conjunct (Attacker_Conjunct p q) e (Pos \<chi>)\<close>
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay pos
        by blast
      thus ?thesis
        using \<chi>_spec expr_pos by fastforce
      next
        case False
        hence Qp': \<open>{p} \<Zsurj>S Q'\<close> \<open>p' = q\<close>
          using  local.pos_neg_clause Attacker_Conjunct unfolding g'_att_del
          by presburger+
        hence move: \<open>spectroscopy_moves (Attacker_Conjunct p q) (Attacker_Delayed p' Q')
          = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)\<close>
          using False by auto
        hence win:
          \<open>spectro_att_wins (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed p' Q')\<close>
          using Attacker_Conjunct unfolding g'_att_del
          by (smt (verit) bind.bind_lunit bind.bind_lzero option.distinct(1) option.sel)
        hence \<open>\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p' Q')
                    (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<phi>
          \<and> expr_pr_inner \<phi> \<le> the (min1_7 (e - E 0 0 0 0 0 0 0 1))\<close>
          using Attack Attacker_Conjunct move unfolding g'_att_del
          by (smt (verit, del_insts) bind.bind_lunit bind_eq_None_conv option.discI
                option.sel spectroscopy_position.simps(51))
        then obtain \<chi> where \<chi>_spec:
            \<open>strategy_formula_inner (Attacker_Delayed p' Q')
                                    (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<chi>\<close>
            \<open>expr_pr_inner \<chi> \<le> the (min1_7 (e - E 0 0 0 0 0 0 0 1))\<close>
          by blast
        hence \<open>strategy_formula_conjunct (Attacker_Conjunct p q) e (Neg \<chi>)\<close>
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
            neg Qp' win move by blast
        thus ?thesis
          using \<chi>_spec Attacker_Conjunct expr_neg move
          unfolding g'_att_del
          by (smt (verit, best) bind.bind_lunit bind_eq_None_conv option.distinct(1)
              option.sel spectroscopy_position.simps(52))
      qed
  next
    case (Attacker_Delayed p Q)
    then consider
      (Att_Del) \<open>\<exists>p Q. g' = Attacker_Delayed p Q\<close> |
      (Att_Imm) \<open>\<exists>p' Q'. g' = Attacker_Immediate p' Q'\<close> |
      (Def_Conj) \<open>\<exists>p Q. g' = Defender_Conj p Q\<close> |
      (Def_St_Conj) \<open>\<exists>p Q. g' = Defender_Stable_Conj p Q\<close> |
      (Def_Branch) \<open>\<exists>p' \<alpha> p'' Q' Q\<alpha>. g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>\<close>
      by (cases g', auto)
    then show ?case
    proof (cases)
      case Att_Del
      then obtain p' Q' where
        g'_att_del: \<open>g' = Attacker_Delayed p' Q'\<close> by blast
      have Qp': \<open>Q' = Q\<close> \<open>p \<noteq> p'\<close> \<open>p \<mapsto> \<tau> p'\<close>
        using Attacker_Delayed g'_att_del Spectroscopy_Game.lts_tau.procrastination
        by metis+
      hence e_comp: \<open>(the (spectroscopy_moves (Attacker_Delayed p Q) g') e) = Some e\<close>
        using g'_att_del
        by simp
      hence att_win: \<open>(spectro_att_wins e (Attacker_Delayed p' Q'))\<close>
        using g'_att_del Qp' Attacker_Delayed weak_spectroscopy_game.attacker_wins.Defense e_comp
        by (metis option.sel)
      have \<open>(weak_spectroscopy_game.updated (Attacker_Delayed p Q) g' e) = e\<close>
        using g'_att_del Attacker_Delayed e_comp by fastforce
      then obtain \<chi> where \<chi>_spec:
          \<open>strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e\<close>
        using Attacker_Delayed g'_att_del by auto
      hence \<open>\<exists>p'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = id_up
         \<and>  spectro_att_wins e (Attacker_Delayed p' Q)
         \<and> strategy_formula_inner (Attacker_Delayed p' Q) e \<chi>\<close>
        using e_comp g'_att_del Qp' local.procrastination Attack.hyps att_win
          Spectroscopy_Game.lts_tau.procrastination
        by metis
      hence \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close>
        using procrastination by blast
      moreover have \<open>expr_pr_inner \<chi> \<le> e\<close>
        using \<chi>_spec by blast
      ultimately show ?thesis by auto
    next
      case Att_Imm
      then obtain p' Q' where
        g'_att_imm: \<open>g' = Attacker_Immediate p' Q'\<close> by blast
      hence move: \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') \<noteq> None\<close>
        using Attacker_Delayed by blast
      hence \<open>\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q'\<close> unfolding spectroscopy_moves.simps(3) by presburger
      then obtain \<alpha> where \<alpha>_prop: \<open>p \<mapsto>a \<alpha> p'\<close> \<open>Q \<mapsto>aS \<alpha> Q'\<close> by blast
      moreover then have weight:
        \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')
          = subtract 1 0 0 0 0 0 0 0\<close>
        by (simp, metis)
      moreover then have update:
        \<open>weak_spectroscopy_game.updated (Attacker_Delayed p Q) g' e
          = e - (E 1 0 0 0 0 0 0 0)\<close>
        using g'_att_imm Attacker_Delayed
        by (smt (verit, del_insts) option.distinct(1) option.sel)
      moreover then obtain \<chi> where \<chi>_prop:
        \<open>strategy_formula (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<chi>\<close>
        \<open>expressiveness_price \<chi> \<le> e - E 1 0 0 0 0 0 0 0\<close>
        using Attacker_Delayed g'_att_imm
        by auto
      moreover have \<open>spectro_att_wins (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')\<close>
        using weak_spectroscopy_game.attacker_wins.Attack Attack.hyps(4)
          Attacker_Delayed.prems(3) calculation(4) g'_att_imm
        by force
      ultimately have \<open>strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<chi>)\<close>
        using local.observation[of p Q e \<chi> \<alpha>] by blast
      moreover have \<open>expr_pr_inner (Obs \<alpha> \<chi>) \<le> e\<close>
        using expr_obs \<chi>_prop Attacker_Delayed g'_att_imm weight update
        by (smt (verit) option.sel)
      ultimately show ?thesis by auto
    next
      case Def_Conj
      then obtain p' Q' where
        g'_def_conj: \<open>g' = Defender_Conj p' Q'\<close> by blast
      hence  \<open>p = p'\<close> \<open>Q = Q'\<close>
        using local.late_inst_conj Attacker_Delayed by presburger+
      hence
        \<open>the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q')) e = Some e\<close>
        by fastforce
      hence
          \<open>spectro_att_wins e (Defender_Conj p' Q')\<close>
          \<open>weak_spectroscopy_game.updated g g' e = e\<close>
        using Attacker_Delayed Attack unfolding g'_def_conj by simp+
      then obtain \<chi> where
        \<chi>_prop: \<open>strategy_formula_inner (Defender_Conj p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e\<close>
        using Attack g'_def_conj by auto
      hence
        \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q') = id_up
        \<and> spectro_att_wins e (Defender_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Conj p' Q') e \<chi>\<close>
        by (simp add: \<open>Q = Q'\<close> \<open>spectro_att_wins e (Defender_Conj p' Q')\<close> \<open>p = p'\<close>)
      then show ?thesis
        using \<chi>_prop \<open>Q = Q'\<close> \<open>spectro_att_wins e (Defender_Conj p' Q')\<close> \<open>p = p'\<close> late_conj
        by fastforce
    next
      case Def_St_Conj
      then obtain p' Q' where g'_def: \<open>g' = Defender_Stable_Conj p' Q'\<close> by blast
      hence pQ': \<open>p = p'\<close> \<open>Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}\<close> \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close>
        using local.late_stbl_conj Attacker_Delayed
        by meson+
      hence \<open>the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q')) e
          = Some e\<close>
        by auto
      hence \<open>spectro_att_wins e (Defender_Stable_Conj p' Q')\<close>
          \<open>weak_spectroscopy_game.updated g g' e = e\<close>
        using Attacker_Delayed Attack unfolding g'_def by force+
      then obtain \<chi> where \<chi>_prop:
        \<open>strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>\<close> \<open>expr_pr_inner \<chi> \<le> e\<close>
        using Attack g'_def by auto
      have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') = id_up
        \<and> spectro_att_wins e (Defender_Stable_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>\<close>
        using Attack \<chi>_prop \<open>spectro_att_wins e (Defender_Stable_Conj p' Q')\<close> late_stbl_conj
          pQ' g'_def
        by force
      thus ?thesis using local.stable[of p Q e \<chi>] pQ' \<chi>_prop by fastforce
    next
      case Def_Branch
      then obtain p' \<alpha> p'' Q' Q\<alpha> where
        g'_def_br: \<open>g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>\<close> by blast
      hence pQ': \<open>p = p'\<close> \<open>Q' = Q - Q\<alpha>\<close> \<open>p \<mapsto>a \<alpha> p''\<close> \<open>Q\<alpha> \<subseteq> Q\<close>
        using br_conj Attacker_Delayed by metis+
      hence
        \<open>the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)) e
          = Some e\<close>
        by auto
      hence post:
          \<open>spectro_att_wins e (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)\<close>
          \<open>weak_spectroscopy_game.updated g g' e = e\<close>
        using Attack option.inject Attacker_Delayed unfolding g'_def_br by auto
      then obtain \<chi> where \<chi>_prop:
          \<open>strategy_formula_inner (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) e \<chi>\<close>
          \<open>expr_pr_inner \<chi> \<le> e\<close>
        using g'_def_br Attack Attacker_Delayed
        by auto
      hence \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p'' Q' Q\<alpha>) = id_up
         \<and> spectro_att_wins e (Defender_Branch p \<alpha> p'' Q' Q\<alpha>)
         \<and> strategy_formula_inner (Defender_Branch p \<alpha> p'' Q' Q\<alpha>) e \<chi>\<close>
        using g'_def_br local.branch Attack post pQ' by simp
      hence \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close>
        using Attack Attacker_Delayed local.br_conj branch
        unfolding g'_def_br by fastforce
      thus ?thesis using \<chi>_prop
        by fastforce
    qed
  qed force+
next
  case (Defense g e)
  thus ?case
  proof (induct g)
    case (Defender_Branch p \<alpha> p' Q Qa)
    hence conjs:
      \<open>\<forall>q\<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Conjunct p q)
        = subtract 0 1 1 0 0 0 0 0\<close>
      by simp
    obtain e' where e'_spec:
      \<open>\<forall>q\<in>Q. weak_spectroscopy_game.weight (Defender_Branch p \<alpha> p' Q Qa)
            (Attacker_Conjunct p q) e = Some e'
        \<and> spectro_att_wins e' (Attacker_Conjunct p q)
        \<and> (\<exists>\<psi>. strategy_formula_conjunct (Attacker_Conjunct p q) e' \<psi>
            \<and> expr_pr_conjunct \<psi> \<le> e')\<close>
      using conjs Defender_Branch option.distinct(1) option.sel
      by (smt (z3) spectroscopy_position.simps(52))
    hence e'_def: \<open>Q \<noteq> {} \<Longrightarrow> e' = e - E 0 1 1 0 0 0 0 0\<close> using conjs
        by (smt (verit) all_not_in_conv option.distinct(1) option.sel)
    then obtain \<Phi> where \<Phi>_spec:
      \<open>\<forall>q \<in> Q. strategy_formula_conjunct (Attacker_Conjunct p q) e' (\<Phi> q)
        \<and> expr_pr_conjunct (\<Phi> q) \<le> e'\<close>
      using e'_spec by metis
    have obs: \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa)
          (Attacker_Branch p' (soft_step_set Qa \<alpha>))
        = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)\<close>
      by (simp add: soft_step_set_is_soft_step_set)
    have \<open>\<forall>p Q. Attacker_Branch p' (soft_step_set Qa \<alpha>) = Attacker_Branch p Q
      \<longrightarrow> p = p' \<and> Q = soft_step_set Qa \<alpha>\<close> by blast
    with option.discI[OF obs] obtain e'' where
      \<open>\<exists>\<phi>. strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
           (e'' - E 1 0 0 0 0 0 0 0) \<phi>
        \<and> expressiveness_price \<phi> \<le> e'' - E 1 0 0 0 0 0 0 0\<close>
      using Defense.IH option.distinct(1) option.sel
      by (smt (verit, best) Defender_Branch.prems(2) spectroscopy_position.simps(53))
    then obtain \<phi> where
      \<open>strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
        (weak_spectroscopy_game.updated (Defender_Branch p \<alpha> p' Q Qa)
          (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi>\<close>
      \<open>expressiveness_price \<phi>
        \<le> weak_spectroscopy_game.updated (Defender_Branch p \<alpha> p' Q Qa)
            (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0\<close>
      using Defender_Branch.prems(2) option.discI[OF obs]
      by (smt (verit, best) option.sel spectroscopy_position.simps(53))
    hence obs_strat:
      \<open>strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
          (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0) \<phi>\<close>
      \<open>expressiveness_price \<phi> \<le> (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0)\<close>
      by (smt (verit, best) Defender_Branch.prems(2) bind.bind_lunit bind.bind_lzero obs
          option.distinct(1) option.sel)+
    have \<open>spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>))
        (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
       = (subtract 1 0 0 0 0 0 0 0)\<close> by simp
    obtain e'' where win_branch:
        \<open>Some e'' = min1_6 (e - E 0 1 1 0 0 0 0 0)\<close>
        \<open>spectro_att_wins e'' (Attacker_Branch p' (soft_step_set Qa \<alpha>))\<close>
      using Defender_Branch
      by (smt (verit, ccfv_threshold) bind.bind_lunit bind_eq_None_conv obs
            option.discI option.sel)
    then obtain g'' where g''_spec:
      \<open>spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' \<noteq> None\<close>
      \<open>spectro_att_wins (weak_spectroscopy_game.updated
        (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' (the (min1_6 (e - E 0 1 1 0 0 0 0 0))))
         g''\<close>
      using weak_spectroscopy_game.attacker_wins.cases
      by (metis spectroscopy_defender.simps(2) option.sel)
    hence move_immediate:
      \<open>g'' = (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
      \<and> spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>))
          (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) = subtract 1 0 0 0 0 0 0 0\<close>
      using br_acct
      by (cases g'', auto) (metis option.discI)+
    then obtain e''' where win_immediate:
      \<open>Some e''' = subtract_fn 1 0 0 0 0 0 0 0 e''\<close>
      \<open>spectro_att_wins e''' (Attacker_Immediate p' (soft_step_set Qa \<alpha>))\<close>
      using g''_spec win_branch option.distinct(1) option.sel spectroscopy_defender.elims(1)
        spectroscopy_defender.simps(2)
        weak_spectroscopy_game.attacker_wins.cases[OF win_branch(2)]
      by (smt (verit, del_insts) local.br_acct spectroscopy_moves.simps(23,53,57,61,66,72))
    hence strat:
        \<open>strategy_formula_inner (Defender_Branch p \<alpha> p' Q Qa) e (BranchConj \<alpha> \<phi> Q \<Phi>)\<close>
      using branch_conj obs move_immediate obs_strat \<Phi>_spec conjs e'_def e'_spec
      by (smt (verit, best) option.distinct(1) option.sel win_branch(1))
    have \<open>E 1 0 0 0 0 0 0 0 \<le> e''\<close> using win_branch g''_spec
      by (metis option.distinct(1) win_immediate(1))
    hence above_one: \<open>0 < min (modal_depth e) (pos_conjuncts e)\<close>
      using win_immediate win_branch
      by (metis energy.sel(1) energy.sel(6) gr_zeroI idiff_0_right leq_components
            min_1_6_simps(1) minus_energy_def not_one_le_zero option.sel)
    have \<open>\<forall>q \<in> Q. expr_pr_conjunct (\<Phi> q) \<le> (e - (E 0 1 1 0 0 0 0 0))\<close>
      using \<Phi>_spec e'_def by blast
    moreover have \<open>expressiveness_price \<phi>
        \<le> the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0\<close>
      using obs_strat(2) by blast
    moreover hence \<open>modal_depth_srbb \<phi> \<le> min (modal_depth e) (pos_conjuncts e) - 1\<close>
      by simp
    hence \<open>1 + modal_depth_srbb \<phi> \<le> min (modal_depth e) (pos_conjuncts e)\<close>
      by (metis above_one add.right_neutral add_diff_cancel_enat
            add_mono_thms_linordered_semiring(1) enat.simps(3) enat_defs(2) ileI1
            le_iff_add plus_1_eSuc(1))
    moreover hence \<open>1 + modal_depth_srbb \<phi> \<le> pos_conjuncts e\<close> by simp
    ultimately have \<open>expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) \<le> e\<close>
      using expr_br_conj e'_def obs Defender_Branch(2) win_branch(1) win_immediate(1)
      by (smt (verit, best) bind_eq_None_conv option.distinct(1) option.sel option.simps(3))
    then show ?case using strat by force
  next
    case (Defender_Conj p Q)
    hence moves:
      \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
        \<longrightarrow> (\<exists>e'. weak_spectroscopy_game.weight (Defender_Conj p Q) g' e = Some e'
            \<and> spectro_att_wins e' g')
          \<and> (\<exists>q. g' = (Attacker_Conjunct p q))\<close>
      using local.conj_answer
        lts_tau.spectroscopy_defender.elims spectroscopy_moves.simps(30,33,34,47,58,62)
      by (smt (verit, best))
    show ?case
    proof (cases \<open>Q = {}\<close>)
      case True
      then obtain \<Phi> where \<open>\<forall>q \<in> Q.
        spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p q)
           = subtract 0 0 1 0 0 0 0 0
        \<and> spectro_att_wins (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Conjunct p q)
        \<and> strategy_formula_conjunct (Attacker_Conjunct p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)\<close>
        by (auto simp add: emptyE)
      hence Strat: \<open>strategy_formula_inner (Defender_Conj p Q) e (Conj {} \<Phi>)\<close>
        using \<open>Q = {}\<close> conj by blast
      hence
        \<open>modal_depth_srbb_inner (Conj Q \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)\<close>
        \<open>branch_conj_depth_inner (Conj Q \<Phi>) = Sup ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q)\<close>
        \<open>inst_conj_depth_inner (Conj Q \<Phi>) = 0\<close>
        \<open>st_conj_depth_inner (Conj Q \<Phi>) = Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q)\<close>
        \<open>imm_conj_depth_inner (Conj Q \<Phi>) = Sup ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q)\<close>
        \<open>max_pos_conj_depth_inner (Conj Q \<Phi>) = Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q)\<close>
        \<open>max_neg_conj_depth_inner (Conj Q \<Phi>) = Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q)\<close>
        \<open>neg_depth_inner (Conj Q \<Phi>) = Sup ((neg_depth_conjunct \<circ> \<Phi>) ` Q)\<close>
        using \<open>Q = {}\<close> by auto
      hence
        \<open>modal_depth_srbb_inner (Conj Q \<Phi>) = 0\<close>
        \<open>branch_conj_depth_inner (Conj Q \<Phi>) = 0\<close>
        \<open>inst_conj_depth_inner (Conj Q \<Phi>) = 0\<close>
        \<open>st_conj_depth_inner (Conj Q \<Phi>) = 0\<close>
        \<open>imm_conj_depth_inner (Conj Q \<Phi>) = 0\<close>
        \<open>max_pos_conj_depth_inner (Conj Q \<Phi>) = 0\<close>
        \<open>max_neg_conj_depth_inner (Conj Q \<Phi>) = 0\<close>
        \<open>neg_depth_inner (Conj Q \<Phi>) = 0\<close>
        using \<open>Q = {}\<close> by (simp add: bot_enat_def)+
      hence \<open>expr_pr_inner (Conj Q \<Phi>) = (E 0 0 0 0 0 0 0 0)\<close>
        using \<open>Q = {}\<close> by force
      hence price: \<open>expr_pr_inner (Conj Q \<Phi>) \<le> e\<close>
        by auto
      with Strat price True show ?thesis by auto
    next
      case False
      hence fa_q: \<open>\<forall>q \<in> Q. \<exists>e'.
        Some e' = subtract_fn 0 0 1 0 0 0 0 0 e
        \<and> spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p q)
            = subtract 0 0 1 0 0 0 0 0
        \<and> spectro_att_wins e' (Attacker_Conjunct p q)\<close>
        using moves local.conj_answer option.distinct(1)
        by (smt (z3) option.sel)
      have q_ex_e': \<open>\<forall>q \<in> Q.  \<exists>e'.
           spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p q)
            = subtract 0 0 1 0 0 0 0 0
        \<and> Some e' = subtract_fn 0 0 1 0 0 0 0 0 e
        \<and> spectro_att_wins e' (Attacker_Conjunct p q)
        \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Conjunct p q) e' \<phi>
            \<and> expr_pr_conjunct \<phi> \<le> e')\<close>
      proof safe
        fix q
        assume \<open>q \<in> Q\<close>
        then obtain e' where e'_spec:
          \<open>Some e' = subtract_fn 0 0 1 0 0 0 0 0 e\<close>
          \<open>spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p q)
            = subtract 0 0 1 0 0 0 0 0\<close>
          \<open>spectro_att_wins e' (Attacker_Conjunct p q)\<close>
          using fa_q by blast
        hence \<open>weak_spectroscopy_game.weight (Defender_Conj p Q) (Attacker_Conjunct p q) e
            = Some e'\<close>
          by simp
        then have \<open>\<exists>\<psi>. strategy_formula_conjunct (Attacker_Conjunct p q) e' \<psi>
            \<and> expr_pr_conjunct \<psi> \<le> e'\<close>
          using Defender_Conj e'_spec
          by (smt (verit, best) option.distinct(1) option.sel spectroscopy_position.simps(52))
        thus \<open>\<exists>e'. spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p q)
                = subtract 0 0 1 0 0 0 0 0
          \<and> Some e' = subtract_fn 0 0 1 0 0 0 0 0 e
          \<and> spectro_att_wins e' (Attacker_Conjunct p q)
          \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Conjunct p q) e' \<phi>
              \<and> expr_pr_conjunct \<phi> \<le> e')\<close>
          using e'_spec by blast
      qed
      hence \<open>\<exists>\<Phi>. \<forall>q \<in> Q.
        spectro_att_wins (e - E 0 0 1 0 0 0 0 0) (Attacker_Conjunct p q)
        \<and> (strategy_formula_conjunct (Attacker_Conjunct p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)
        \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))\<close>
        by (metis (no_types, opaque_lifting) option.distinct(1) option.inject)
      then obtain \<Phi> where IH:
        \<open>\<forall>q \<in> Q. spectro_att_wins (e - E 0 0 1 0 0 0 0 0) (Attacker_Conjunct p q)
          \<and> (strategy_formula_conjunct (Attacker_Conjunct p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)
          \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))\<close> by auto
      hence \<open>strategy_formula_inner (Defender_Conj p Q) e (Conj Q \<Phi>)\<close>
        by (simp add: conj)
      moreover have \<open>expr_pr_inner (Conj Q \<Phi>) \<le> e\<close>
        using IH expr_conj \<open>Q \<noteq> {}\<close> q_ex_e'
        by (metis (no_types, lifting) equals0I option.distinct(1))
      ultimately show ?thesis by auto
    qed
  next
    case (Defender_Stable_Conj p Q)
    hence cases:
      \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None \<longrightarrow>
       (\<exists>e'. weak_spectroscopy_game.weight (Defender_Stable_Conj p Q) g' e = Some e'
        \<and> spectro_att_wins e' g')
        \<and> ((\<exists>p' q. g' = Attacker_Conjunct p' q) \<or> (\<exists>p' Q'. g' = Defender_Conj p' Q'))\<close>
      by (metis (no_types, opaque_lifting)
            spectroscopy_defender.elims(2,3) spectroscopy_moves.simps(35,36,37,38,74))
    show ?case
    proof(cases \<open>Q = {}\<close>)
      case True
      then obtain e' where e'_spec:
        \<open>weak_spectroscopy_game.weight (Defender_Stable_Conj p Q) (Defender_Conj p Q) e
          = Some e'\<close>
        \<open>e' = e - (E 0 0 0 1 0 0 0 0)\<close>
        \<open>spectro_att_wins e' (Defender_Conj p Q)\<close>
        using cases local.empty_stbl_conj_answer
        by (smt (verit, best) option.discI option.sel)
      then obtain \<Phi> where \<Phi>_prop: \<open>strategy_formula_inner (Defender_Conj p Q) e' (Conj Q \<Phi>)\<close>
        using conj True by blast
      hence strategy: \<open>strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)\<close>
        by (simp add: True stable_conj)
      have \<open>E 0 0 0 1 0 0 0 0 \<le> e\<close> using e'_spec
        using option.sel True by fastforce
      moreover have \<open>expr_pr_inner (StableConj Q \<Phi>) = E 0 0 0 1 0 0 0 0\<close>
        using True by (simp add: bot_enat_def)
      ultimately have \<open>expr_pr_inner (StableConj Q \<Phi>) \<le> e\<close> by simp
      with strategy show ?thesis by auto
    next
      case False
      then obtain e' where e'_spec:
        \<open>e' = e - (E 0 0 0 1 0 0 0 0)\<close>
        \<open>\<forall>q \<in> Q. weak_spectroscopy_game.weight (Defender_Stable_Conj p Q)
            (Attacker_Conjunct p q) e = Some e'
          \<and> spectro_att_wins e' (Attacker_Conjunct p q)\<close>
        using cases local.conj_s_answer
        by (smt (verit, del_insts) option.distinct(1) option.sel)
      hence IH: \<open>\<forall>q \<in> Q. \<exists>\<psi>.
        strategy_formula_conjunct (Attacker_Conjunct p q) e' \<psi> \<and>
        expr_pr_conjunct \<psi> \<le> e'\<close>
        using Defender_Stable_Conj local.conj_s_answer
        by (smt (verit, best) option.distinct(1) option.inject spectroscopy_position.simps(52))
      hence \<open>\<exists>\<Phi>. \<forall>q \<in> Q.
        strategy_formula_conjunct (Attacker_Conjunct p q) e' (\<Phi> q) \<and>
        expr_pr_conjunct (\<Phi> q) \<le> e'\<close>
        by meson
      then obtain \<Phi> where \<Phi>_prop: \<open>\<forall>q \<in> Q.
        strategy_formula_conjunct (Attacker_Conjunct p q) e' (\<Phi> q)
        \<and> expr_pr_conjunct (\<Phi> q) \<le> e'\<close>
        by blast
      have \<open>E 0 0 0 1 0 0 0 0 \<le> e\<close>
        using e'_spec False by fastforce
      hence \<open>expr_pr_inner (StableConj Q \<Phi>) \<le> e\<close>
        using expr_st_conj e'_spec \<Phi>_prop False by metis
      moreover have \<open>strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)\<close>
        using \<Phi>_prop e'_spec stable_conj
        unfolding e'_spec by fastforce
      ultimately show ?thesis by auto
    qed
  qed force+
qed

lemma strategy_formulas_distinguish:
  shows
    \<open>(strategy_formula g e \<phi> \<longrightarrow>
      (case g of
        Attacker_Immediate p Q \<Rightarrow>  distinguishes_from \<phi> p Q
      | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q
      | _ \<Rightarrow> True))
      \<and>
      (strategy_formula_inner g e \<chi> \<longrightarrow>
      (case g of
         Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
      | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto> \<tau> q)
          \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow>(p \<mapsto>a \<alpha> p')
          \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q\<union>Qa)
      | _ \<Rightarrow> True))
      \<and>
      (strategy_formula_conjunct g e \<psi> \<longrightarrow>
        (case g of
        Attacker_Conjunct p q \<Rightarrow> hml_srbb_conj.distinguishes \<psi> p q
      | _ \<Rightarrow> True))\<close>
proof(induction rule: strategy_formula_strategy_formula_inner_strategy_formula_conjunct.induct)
  case (delay p Q e \<chi>)
  then show ?case
    by (smt (verit) distinguishes_from_def option.discI silent_reachable.intros(1)
        silent_reachable_trans spectroscopy_moves.simps(1) spectroscopy_position.simps)
next
  case (procrastination p Q e \<chi>)
  from this obtain p' where IH:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = id_up \<and>
     spectro_att_wins e (Attacker_Delayed p' Q) \<and>
     strategy_formula_inner (Attacker_Delayed p' Q) e \<chi> \<and>
     (case Attacker_Delayed p' Q of Attacker_Delayed p Q \<Rightarrow>
        Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q |
        Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {}
          \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa) |
        Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q |
        Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q)
          \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q |
        _ \<Rightarrow> True)\<close> by fastforce
  hence D: \<open>Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p' Q\<close>
    using spectroscopy_position.simps(53) by fastforce
  from IH have \<open>p \<Zsurj>p'\<close>
    by (metis option.discI silent_reachable.intros(1)
          silent_reachable_append_\<tau> spectroscopy_moves.simps(2))
  hence \<open>Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q\<close> using D
    by (smt (verit) silent_reachable_trans distinguishes_from_def hml_srbb_models.simps(2))
  then show ?case by simp
next
  case (observation p Q e \<phi> \<alpha>)
  then obtain p' Q' where IH:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')
      = subtract 1 0 0 0 0 0 0 0 \<and>
     spectro_att_wins (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
     (strategy_formula (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
      (case Attacker_Immediate p' Q' of Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<phi> p Q
       | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q | _ \<Rightarrow> True)) \<and>
     p \<mapsto>a \<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q'\<close> by auto
  hence D: \<open>distinguishes_from \<phi> p' Q'\<close> by auto
  hence \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
  have observation: \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')
      = (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then (subtract 1 0 0 0 0 0 0 0) else None)\<close>
    for p p' Q Q' by simp
  from IH have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')
    = subtract 1 0 0 0 0 0 0 0\<close> by simp
  also have \<open>... \<noteq> None\<close> by blast
  finally have \<open>(\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q')\<close> unfolding observation by metis
  from IH have \<open>p \<mapsto>a \<alpha> p'\<close> and \<open>Q \<mapsto>aS \<alpha> Q'\<close>  by auto
  hence P: \<open>p \<Turnstile>SRBB (Internal (Obs \<alpha> \<phi>))\<close> using \<open>p' \<Turnstile>SRBB \<phi>\<close>
    using silent_reachable.intros(1) by auto
  have \<open>Q \<Zsurj>S Q \<longrightarrow> (\<forall>q\<in>Q. \<not>(q \<Turnstile>SRBB (Internal (Obs \<alpha> \<phi>))))\<close>
    by (simp, meson D \<open>Q \<mapsto>aS \<alpha> Q'\<close> distinguishes_from_def)
  hence \<open>Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal (hml_srbb_inner.Obs \<alpha> \<phi>)) p Q\<close>
    using P by fastforce
  then show ?case by simp
next
  case (early_conj Q p Q' e \<phi>)
  then show ?case
    by (simp, metis not_None_eq)
next
  case (late_conj p Q e \<chi>)
  then show ?case
    using silent_reachable.intros(1)
    by auto
next
  case (conj Q p e \<Phi>)
  then show ?case by auto
next
  case (imm_conj Q p e \<Phi>)
  then show ?case by auto
next
  case (pos p q e \<chi>)
  then show ?case using silent_reachable.refl
    by (simp) (metis option.discI silent_reachable_trans)
next
  case (neg p q e \<chi>)
  then obtain P' where IH:
    \<open>spectroscopy_moves (Attacker_Conjunct p q) (Attacker_Delayed q P')
      = Some (\<lambda>e. Option.bind (subtract_fn 0 0 0 0 0 0 0 1 e) min1_7)\<close>
    \<open>spectro_att_wins (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed q P') \<and>
     strategy_formula_inner (Attacker_Delayed q P')
                              (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<chi>  \<and>
     (case Attacker_Delayed q P' of
        Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
      | Defender_Branch p \<alpha> p' Q Qa
        \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa)
      | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Stable_Conj p Q
        \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | _ \<Rightarrow> True)\<close> by fastforce
  hence D: \<open>P' \<Zsurj>S P' \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) q P'\<close> by simp
  have \<open>{p} \<Zsurj>S P'\<close> using IH(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) not_Some_eq)
  have \<open>P' \<Zsurj>S P' \<longrightarrow> p \<in> P'\<close> using \<open>{p} \<Zsurj>S P'\<close>  by (simp add: silent_reachable.intros(1))
  hence \<open>hml_srbb_conj.distinguishes (hml_srbb_conjunct.Neg \<chi>) p q\<close> using D \<open>{p} \<Zsurj>S P'\<close>
    unfolding hml_srbb_conj.distinguishes_def distinguishes_from_def
    by (smt (verit) lts_tau.silent_reachable_trans hml_srbb_conjunct_models.simps(2)
          hml_srbb_models.simps(2) silent_reachable.refl)
  then show ?case by simp
next
  case (stable p Q e \<chi>)
  then obtain Q' where IH:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = id_up\<close>
     \<open>spectro_att_wins e (Defender_Stable_Conj p Q') \<and>
     strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi> \<and>
     (case Defender_Stable_Conj p Q' of
        Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
      | Defender_Branch p \<alpha> p' Q Qa
        \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa)
      | Defender_Conj p Q
        \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Stable_Conj p Q
        \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | _ \<Rightarrow> True)\<close> by auto
  hence \<open>(\<nexists>p''. p \<mapsto>\<tau> p'')\<close>
    by (metis local.late_stbl_conj option.distinct(1))
  from IH have \<open>(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q'\<close> by simp
  hence \<open>hml_srbb_inner.distinguishes_from \<chi> p Q'\<close> using \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close> by auto
  hence \<open>hml_srbb_inner_models p \<chi>\<close> by simp
  hence \<open>p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)\<close>
    using lts_tau.refl by force
  have \<open>Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q\<close>
  proof
    assume \<open>Q \<Zsurj>S Q\<close>
    have \<open>(\<forall>q \<in> Q. \<not>(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>)))\<close>
    proof (clarify)
      fix q
      assume \<open>q \<in> Q\<close> \<open>(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>))\<close>
      hence \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close> by simp
      then obtain q' where X: \<open>q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close> by auto
      hence \<open>q' \<in> Q\<close> using \<open>Q \<Zsurj>S Q\<close> \<open>q \<in> Q\<close> by blast
      then show \<open>False\<close>
      proof (cases \<open>q' \<in> Q'\<close>)
        case True \<comment> \<open>stable cases\<close>
        thus \<open>False\<close> using X \<open>hml_srbb_inner.distinguishes_from \<chi> p Q'\<close>
          by simp
      next
        case False \<comment> \<open>unstable cases\<close>
        from IH have \<open>strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi>\<close> by simp
        hence \<open>\<exists>\<Phi>. \<chi> = StableConj Q' \<Phi>\<close> using strategy_formula_inner.simps
          by (smt (verit) spectroscopy_defender.simps(4,7)
              spectroscopy_position.distinct(37,41) spectroscopy_position.inject(6))
        then obtain \<Phi> where P: \<open>\<chi> = (StableConj Q' \<Phi>)\<close> by auto
        from IH(1) have \<open>Q' = {q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}\<close>
          by (metis (full_types) local.late_stbl_conj option.distinct(1))
        hence \<open>\<exists>q''. q' \<mapsto>\<tau> q''\<close> using False \<open>q' \<in> Q\<close> by simp
        from X have \<open>hml_srbb_inner_models q' (StableConj Q' \<Phi>)\<close> using P by auto
        then show ?thesis using \<open>\<exists>q''. q' \<mapsto>\<tau> q''\<close> by simp
      qed
    qed
    thus \<open>distinguishes_from (hml_srbb.Internal \<chi>) p Q\<close>
      using \<open>p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)\<close> by simp
  qed
  then show ?case by simp
next
  case (stable_conj Q p e \<Phi>)
  hence IH: \<open>\<forall>q\<in> Q. hml_srbb_conj.distinguishes (\<Phi> q) p q\<close> by simp
  hence Q: \<open>\<forall>q \<in> Q. hml_srbb_conjunct_models p (\<Phi> q)\<close> by simp
  hence \<open>(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from (StableConj Q \<Phi>) p Q\<close>
    using IH by auto
  then show ?case by simp
next
  case (branch p Q e \<chi>)
  then obtain p' Q' \<alpha> Q\<alpha> where IH:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = id_up\<close>
    \<open>spectro_att_wins e (Defender_Branch p \<alpha> p' Q' Q\<alpha>) \<and>
     strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi> \<and>
     (case Defender_Branch p \<alpha> p' Q' Q\<alpha> of
        Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
      | Defender_Branch p \<alpha> p' Q Qa
        \<Rightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa)
      | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Stable_Conj p Q
        \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | _ \<Rightarrow> True)\<close> by blast
  from IH(1) have \<open>p \<mapsto>a \<alpha> p'\<close>
    by (metis local.br_conj option.distinct(1))
  from IH have \<open>p \<mapsto>a \<alpha> p' \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q' \<union> Q\<alpha>)\<close> by simp
  hence D: \<open>hml_srbb_inner.distinguishes_from \<chi> p (Q' \<union> Q\<alpha>)\<close> using \<open>p \<mapsto>a \<alpha> p'\<close> by auto
  from IH have \<open>Q' = Q - Q\<alpha> \<and> p \<mapsto>a \<alpha> p' \<and> Q\<alpha> \<subseteq> Q\<close>
    by (metis (no_types, lifting) br_conj option.discI)
  hence \<open>Q=(Q' \<union> Q\<alpha>)\<close> by auto
  then show ?case
    using D silent_reachable.refl by auto
next
  case (branch_conj p \<alpha> p' Q1 Q\<alpha> e \<psi> \<Phi>)
  hence A1: \<open>\<forall>q\<in>Q1. hml_srbb_conjunct_models p (\<Phi> q)\<close> by simp
  from branch_conj obtain Q' where IH:
    \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' Q1 Q\<alpha>) (Attacker_Branch p' Q')
      = Some (\<lambda>e. Option.bind (subtract_fn 0 1 1 0 0 0 0 0 e) min1_6)\<close>
    \<open>spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
      = subtract 1 0 0 0 0 0 0 0 \<and>
     spectro_att_wins (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0)
        (Attacker_Immediate p' Q') \<and>
     strategy_formula (Attacker_Immediate p' Q')
        (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0) \<psi> \<and>
     (case Attacker_Immediate p' Q' of
         Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<psi> p Q
       | Defender_Conj p Q \<Rightarrow> distinguishes_from \<psi> p Q | _ \<Rightarrow> True)\<close> by auto
  hence \<open>distinguishes_from \<psi> p' Q'\<close> by simp
  hence X: \<open>p' \<Turnstile>SRBB \<psi>\<close> by simp
  have Y: \<open>\<forall>q \<in> Q'. \<not>(q \<Turnstile>SRBB \<psi>)\<close> using \<open>distinguishes_from \<psi> p' Q'\<close> by simp
  have \<open>p \<mapsto>a \<alpha> p' \<longrightarrow> hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>)\<close>
  proof
    assume \<open>p \<mapsto>a \<alpha> p'\<close>
    hence \<open>p \<mapsto>a \<alpha> p'\<close> by simp
    with IH(1) have \<open>Q\<alpha> \<mapsto>aS \<alpha> Q'\<close>
      by (simp, metis option.discI)
    hence A2: \<open>hml_srbb_inner_models p (Obs \<alpha> \<psi>)\<close> using X \<open>p \<mapsto>a \<alpha> p'\<close>  by auto
    have A3: \<open>\<forall>q \<in> (Q1 \<union> Q\<alpha>). hml_srbb_inner.distinguishes (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q\<close>
    proof (safe)
      fix q
      assume \<open>q \<in> Q1\<close>
      hence  \<open>hml_srbb_conj.distinguishes (\<Phi> q) p q\<close> using branch_conj(2) by simp
      thus \<open>hml_srbb_inner.distinguishes (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q\<close>
        using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction \<open>q \<in> Q1\<close>
        by blast
    next
      fix q
      assume \<open>q \<in> Q\<alpha>\<close>
      hence \<open>\<not>(hml_srbb_inner_models q (Obs \<alpha> \<psi>))\<close>
        using Y \<open>Q\<alpha> \<mapsto>aS \<alpha> Q'\<close> by auto
      hence \<open>hml_srbb_inner.distinguishes (Obs \<alpha> \<psi>) p q\<close>
        using A2 by auto
      thus \<open>hml_srbb_inner.distinguishes (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q\<close>
        using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction by blast
    qed
    have \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<psi> Q1 \<Phi>)\<close>
      using A3 A2 by fastforce
    with A3 show \<open>hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>)\<close>
      by simp
  qed
  then show ?case by simp
qed

end

end
