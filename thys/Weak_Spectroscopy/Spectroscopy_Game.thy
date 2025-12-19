(* License: LGPL *)

section \<open>Weak Spectroscopy Game\<close>

theory Spectroscopy_Game
  imports Energy_Games Energy Labeled_Transition_Systems
begin

text \<open>
  The weak spectroscopy game is an energy game played over an LTS.
  The attacker's moves in the weak spectroscopy game depend on the transitions of the processes and the available energy.
  Intuitively, each move type corresponds to a production in the construction of distinguishing formulas; and each attacker position to a non-terminal in the underlying grammar.
\<close>

subsection \<open>Game Rules\<close>

datatype ('s, 'a) spectroscopy_position =
  Attacker_Immediate (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Attacker_Delayed (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Attacker_Conjunct (attacker_state: \<open>'s\<close>) (defender_state: \<open>'s\<close>) |
  Attacker_Branch (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |

  Defender_Conj (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Defender_Stable_Conj (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Defender_Branch (attacker_state: \<open>'s\<close>) (attack_action: \<open>'a\<close>)
                 (attacker_state_succ: \<open>'s\<close>) (defender_states: \<open>'s set\<close>)
                 (defender_branch_states: \<open>'s set\<close>)

context lts_tau
begin

text \<open>The names of moves of the weak spectroscopy game indicate the respective HML constructs they correspond to.\<close>
fun spectroscopy_moves :: \<open>('s, 'a) spectroscopy_position \<Rightarrow> ('s, 'a) spectroscopy_position
  \<Rightarrow> energy update option\<close>
where
  delay:
    \<open>spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')
     = (if p' = p \<and> Q \<Zsurj>S Q' then id_up else None)\<close> |

  procrastination:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q')
      = (if (Q' = Q \<and> p \<noteq> p' \<and> p \<mapsto> \<tau> p') then id_up else None)\<close> |

  observation:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')
      = (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then (subtract 1 0 0 0 0 0 0 0)
         else None)\<close> |

  f_or_early_conj:
    \<open>spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')
      =(if (Q\<noteq>{} \<and> Q = Q' \<and> p = p') then (subtract 0 0 0 0 1 0 0 0)
        else None)\<close> |

  late_inst_conj:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q')
      = (if p = p' \<and> Q = Q' then id_up else None)\<close> |

  conj_answer:
    \<open>spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p' q)
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 1 0 0 0 0 0) else None)\<close> |

  pos_neg_clause:
    \<open>spectroscopy_moves (Attacker_Conjunct p q) (Attacker_Delayed p' Q')
      = (if (p = p') then
          (if {q} \<Zsurj>S Q' then Some min1_6 else None)
         else (if {p} \<Zsurj>S Q' \<and> q=p'
               then Some (\<lambda>e. Option.bind (subtract_fn 0 0 0 0 0 0 0 1 e) min1_7)
               else None))\<close> |

  late_stbl_conj:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q')
      = (if (p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p''))
          then id_up else None)\<close> |

  conj_s_answer:
    \<open>spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Conjunct p' q)
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 0 1 0 0 0 0)
         else None)\<close> |

  empty_stbl_conj_answer:
    \<open>spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p' Q')
      = (if Q = {} \<and> Q = Q' \<and> p = p' then (subtract 0 0 0 1 0 0 0 0)
         else None)\<close> |

  br_conj:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)
      = (if (p = p' \<and> Q' = Q - Q\<alpha> \<and> p \<mapsto>a \<alpha> p'' \<and> Q\<alpha> \<subseteq> Q) then id_up
         else None)\<close> |

  br_answer:
    \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Conjunct p'' q)
      = (if (p = p'' \<and> q \<in> Q) then (subtract 0 1 1 0 0 0 0 0) else None)\<close> |

  br_obsv:
    \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p'' Q')
      = (if (p' = p'' \<and> Q\<alpha> \<mapsto>aS \<alpha> Q')
         then Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6) else None)\<close> |

  br_acct:
    \<open>spectroscopy_moves (Attacker_Branch p Q) (Attacker_Immediate p' Q')
      = (if p = p' \<and> Q = Q' then subtract 1 0 0 0 0 0 0 0 else None)\<close> |

  others: \<open>spectroscopy_moves _ _ = None\<close>

fun spectroscopy_defender where
  \<open>spectroscopy_defender (Attacker_Immediate _ _) = False\<close> |
  \<open>spectroscopy_defender (Attacker_Branch _ _) = False\<close> |
  \<open>spectroscopy_defender (Attacker_Conjunct _ _) = False\<close> |
  \<open>spectroscopy_defender (Attacker_Delayed _ _) = False\<close> |
  \<open>spectroscopy_defender (Defender_Branch _ _ _ _ _) = True\<close> |
  \<open>spectroscopy_defender (Defender_Conj _ _) = True\<close> |
  \<open>spectroscopy_defender (Defender_Stable_Conj _ _) = True\<close>

subsection \<open>Energy Game Properties\<close>

text \<open>Now, we are able to define the weak spectroscopy game on an arbitrary LTS.\<close>
sublocale weak_spectroscopy_game:
  energy_game \<open>spectroscopy_moves\<close> \<open>spectroscopy_defender\<close> \<open>(\<le>)\<close>
proof
  fix e e' ::energy
  show \<open>e \<le> e' \<Longrightarrow> e' \<le> e \<Longrightarrow> e = e'\<close> unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if energy.expand nle_le)
next
  fix g g' e e' eu eu'
  assume monotonicity_assms:
    \<open>spectroscopy_moves g g' \<noteq> None\<close>
    \<open>the (spectroscopy_moves g g') e = Some eu\<close>
    \<open>the (spectroscopy_moves g g') e' = Some eu'\<close>
    \<open>e \<le> e'\<close>
  show \<open>eu \<le> eu'\<close>
  proof (cases g)
    case (Attacker_Immediate p Q)
    with monotonicity_assms
    show ?thesis
      by (cases g', simp_all, (smt (z3) option.distinct(1) option.sel minus_component_leq)+)
  next
    case (Attacker_Branch p Q)
    with monotonicity_assms
    show ?thesis
      by (cases g', simp_all, (smt (z3) option.distinct(1) option.sel minus_component_leq)+)
  next
    case (Attacker_Conjunct p q)
    hence \<open>\<exists>p' Q'. g'= (Attacker_Delayed p' Q')\<close>
      using monotonicity_assms(1,2)
      by (induct, auto)
    hence \<open>spectroscopy_moves g g' = Some min1_6
      \<or> spectroscopy_moves g g'
        = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)\<close>
      using monotonicity_assms(1,2) Attacker_Conjunct
      by (smt (verit, ccfv_threshold) spectroscopy_moves.simps(7))
    thus ?thesis
    proof safe
      assume \<open>spectroscopy_moves g g' = Some min1_6\<close>
      thus ?thesis
        using monotonicity_assms min.mono
        unfolding leq_components
        by (metis min_1_6_simps option.sel)
    next
      assume \<open>spectroscopy_moves g g'
          = Some (\<lambda>e. Option.bind (if \<not> E 0 0 0 0 0 0 0 1 \<le> e
                                   then None else Some (e - E 0 0 0 0 0 0 0 1)) min1_7)\<close>
      thus ?thesis
        unfolding min_1_7_subtr_simp
        using monotonicity_assms
        by (smt (z3) enat_diff_mono energy.sel leq_components min.mono
            option.distinct(1) option.sel)
    qed
  next
    case (Attacker_Delayed p Q)
    hence \<open>(\<exists>p' Q'. g' = Attacker_Delayed p' Q') \<or>
      (\<exists>p' Q'. g' = Attacker_Immediate p' Q') \<or>
      (\<exists>p' Q'. g' = Defender_Conj p' Q') \<or>
      (\<exists>p' Q'. g' = Defender_Stable_Conj p' Q') \<or>
      (\<exists>p' p'' Q' \<alpha> Q\<alpha> . g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)\<close>
      using monotonicity_assms(1)
      by (induct, auto)
    thus ?thesis
    proof (safe)
      fix p' Q'
      assume \<open>g' = Attacker_Delayed p' Q'\<close>
      thus \<open>eu \<le> eu'\<close>
        using Attacker_Delayed monotonicity_assms local.procrastination
        by (metis option.sel)
    next
      fix p' Q'
      assume \<open>g' = Attacker_Immediate p' Q'\<close>
      hence \<open>spectroscopy_moves g g' = (subtract 1 0 0 0 0 0 0 0)\<close>
        using Attacker_Delayed monotonicity_assms local.observation
        by (clarify, presburger)
      thus \<open>eu \<le> eu'\<close>
        by (smt (verit, best) mono_subtract monotonicity_assms option.distinct(1) option.sel)
    next
      fix p' Q'
      assume \<open>g' = Defender_Conj p' Q'\<close>
      thus \<open>eu \<le> eu'\<close>
        using Attacker_Delayed monotonicity_assms local.late_inst_conj
        by (metis option.sel)
    next
      fix p' Q'
      assume \<open>g' = Defender_Stable_Conj p' Q'\<close>
      thus \<open>eu \<le> eu'\<close>
        using Attacker_Delayed monotonicity_assms local.late_stbl_conj
        by (metis (no_types, lifting) option.sel)
    next
      fix p' p'' Q' \<alpha> Q\<alpha>
      assume \<open>g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>\<close>
      thus \<open>eu \<le> eu'\<close>
        using Attacker_Delayed monotonicity_assms local.br_conj
        by (metis (no_types, lifting) option.sel)
    qed
  next
    case (Defender_Branch p a p' Q' Qa)
    with monotonicity_assms show ?thesis
      by (cases g', auto simp del: leq_components, unfold min_1_6_subtr_simp)
        (smt (z3) enat_diff_mono mono_subtract option.discI energy.sel
           leq_components min.mono option.distinct(1) option.inject)+
  next
    case (Defender_Conj p Q)
    with monotonicity_assms show ?thesis
      by (cases g', simp_all del: leq_components)
        (smt (verit, ccfv_SIG) mono_subtract option.discI option.sel)
  next
    case (Defender_Stable_Conj x71 x72)
    with monotonicity_assms show ?thesis
      by (cases g', simp_all del: leq_components)
       (smt (verit, ccfv_SIG) mono_subtract option.discI option.sel)+
  qed
next
  fix g g' e e'
  assume defender_win_min_assms:
    \<open>e \<le> e'\<close>
    \<open>spectroscopy_moves g g' \<noteq> None\<close>
    \<open>the (spectroscopy_moves g g') e' = None\<close>
  thus
    \<open>the (spectroscopy_moves g g') e = None\<close>
  proof (cases g)
    case (Attacker_Immediate p Q)
    with defender_win_min_assms show ?thesis
      by (cases g', auto simp del: leq_components)
        (smt (verit, best) option.distinct(1) option.inject order.trans)+
  next
    case (Attacker_Branch p Q)
    with defender_win_min_assms show ?thesis
      by (cases g', auto)
        (smt (verit, best) option.distinct(1) option.inject order.trans)+
  next
    case (Attacker_Conjunct p q)
    hence \<open>\<exists>p' Q'. g'= (Attacker_Delayed p' Q')\<close>
      using defender_win_min_assms(2) by (induct, auto)
    hence \<open>spectroscopy_moves g g' = Some min1_6
      \<or> spectroscopy_moves g g' = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)\<close>
      using defender_win_min_assms(2) Attacker_Conjunct
      by (smt (verit, ccfv_threshold) spectroscopy_moves.simps(7))
    thus ?thesis
    proof safe
      assume \<open>spectroscopy_moves g g' = Some min1_6\<close>
      thus \<open>the (spectroscopy_moves g g') e = None\<close>
        using defender_win_min_assms min_1_6_some by fastforce
    next
      assume \<open>spectroscopy_moves g g'
        = Some (\<lambda>e. Option.bind (if \<not> E 0 0 0 0 0 0 0 1 \<le> e
                                 then None else Some (e - E 0 0 0 0 0 0 0 1)) min1_7)\<close>
      thus \<open>the (spectroscopy_moves g g') e = None\<close>
        using defender_win_min_assms(1,3) bind.bind_lunit dual_order.trans min_1_7_some
        by (smt (verit, best) option.sel)
    qed
  next
    case (Attacker_Delayed p Q)
    hence \<open>(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or>
      (\<exists>p' Q'. g'=(Attacker_Immediate p' Q')) \<or>
      (\<exists>p' Q'. g'=(Defender_Conj p' Q')) \<or>
      (\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q')) \<or>
      (\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))\<close>
      using defender_win_min_assms(2) by (induct, auto)
    thus ?thesis
    proof (safe)
      fix p' Q'
      assume \<open>g' = Attacker_Delayed p' Q'\<close>
      hence False
        using Attacker_Delayed defender_win_min_assms(2,3) local.procrastination
        by (metis option.distinct(1) option.sel)
      thus \<open>the (spectroscopy_moves g (Attacker_Delayed p' Q')) e = None\<close> ..
    next
      fix p' Q'
      assume \<open>g' = Attacker_Immediate p' Q'\<close>
      moreover hence \<open>spectroscopy_moves g g' = (subtract 1 0 0 0 0 0 0 0)\<close>
        using Attacker_Delayed defender_win_min_assms(2,3) local.observation
        by (clarify, presburger)
      moreover hence \<open>\<not>E 1 0 0 0 0 0 0 0 \<le> e'\<close>
        using  defender_win_min_assms by force
      ultimately show  \<open>the (spectroscopy_moves g (Attacker_Immediate p' Q')) e = None\<close>
        using defender_win_min_assms(1) by force
    next
      fix p' Q'
      assume \<open>g' = Defender_Conj p' Q'\<close>
      hence False
        using Attacker_Delayed defender_win_min_assms(2,3) local.late_inst_conj
        by (metis option.distinct(1) option.sel)
      thus \<open>the (spectroscopy_moves g (Defender_Conj p' Q')) e = None\<close> ..
    next
      fix p' Q'
      assume \<open>g' = Defender_Stable_Conj p' Q'\<close>
      hence False
        using Attacker_Delayed defender_win_min_assms(2,3) local.late_stbl_conj
        by (metis (no_types, lifting) option.distinct(1) option.sel)
      thus \<open>the (spectroscopy_moves g (Defender_Stable_Conj p' Q')) e = None\<close> ..
    next
      fix p' p'' Q' \<alpha> Q\<alpha>
      assume \<open>g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>\<close>
      hence False
        using Attacker_Delayed defender_win_min_assms(2,3) local.br_conj
        by (metis (no_types, lifting) option.distinct(1) option.sel)
      thus \<open>the (spectroscopy_moves g (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)) e = None\<close> ..
    qed
  next
    case (Defender_Branch p a p' Q' Qa)
    hence \<open>(\<exists>q'\<in>Q'. g' = Attacker_Conjunct p q')
      \<or> (\<exists>Qa'. Qa \<mapsto>aS a Qa' \<and> g' = Attacker_Branch p' Qa')\<close>
      using defender_win_min_assms by (cases g', auto) (metis not_None_eq)+
    hence \<open>(spectroscopy_moves g g') = (subtract 0 1 1 0 0 0 0 0) \<or>
      (spectroscopy_moves g g') = Some (\<lambda>e. Option.bind (subtract_fn 0 1 1 0 0 0 0 0 e) min1_6)\<close>
      using Defender_Branch option.collapse[OF defender_win_min_assms(2)]
      by (cases g', auto)
    thus ?thesis
      using defender_win_min_assms min_1_6_some
      by (smt (verit, best) bind.bind_lunit option.distinct(1) dual_order.trans option.sel)
  next
    case (Defender_Conj p Q)
    with defender_win_min_assms show ?thesis
      by (cases g', auto)
        (smt (verit, best) option.distinct(1) option.inject order.trans)+
  next
    case (Defender_Stable_Conj x71 x72)
    with defender_win_min_assms show ?thesis
      by (cases g', simp_all del: leq_components)
         (smt (verit) dual_order.trans option.discI option.sel)+
  qed
qed

abbreviation \<open>spectro_att_wins \<equiv> weak_spectroscopy_game.attacker_wins\<close>

end \<comment> \<open>of \<^locale>\<open>lts_tau\<close>\<close>

end
