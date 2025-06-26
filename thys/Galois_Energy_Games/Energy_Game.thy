section \<open>Energy Games\<close>

theory Energy_Game
  imports Coinductive.Coinductive_List Open_Induction.Restricted_Predicates 
begin

text\<open>Energy games are two-player zero-sum games with perfect information played on labeled directed graphs. 
The labels contain information on how each edge affects the current energy.
We call the two players attacker and defender.
In this theory we give fundamental definitions of plays, energy levels and (winning) attacker strategies.
(This corresponds to section 2.1 and 2.2 in the preprint~\cite{preprint}.)\<close>

locale energy_game =
  fixes attacker ::  "'position set" and 
        weight :: "'position \<Rightarrow> 'position \<Rightarrow> 'label option" and
        application :: "'label \<Rightarrow> 'energy \<Rightarrow> 'energy option" 
begin 

abbreviation "positions \<equiv> {g. g \<in> attacker \<or> g \<notin> attacker}"
abbreviation "apply_w g g' \<equiv> application (the (weight g g'))"

text\<open>\subsubsection*{Plays}

A play is a possibly infinite walk in the underlying directed graph.\<close>

coinductive valid_play :: "'position llist \<Rightarrow> bool" where
  "valid_play LNil" |
  "valid_play (LCons v LNil)" |
  "\<lbrakk>weight v (lhd Ps) \<noteq> None; valid_play Ps; \<not>lnull Ps\<rbrakk>
    \<Longrightarrow> valid_play (LCons v Ps)"

text\<open>The following lemmas follow directly from the definition \<open>valid_play\<close>. 
In particular, a play is valid if and only if for each position there is an edge to its successor 
in the play. We show this using the coinductive definition by first establishing coinduction. \<close>

lemma valid_play_append:
  assumes "valid_play (LCons v Ps)" and "lfinite (LCons v Ps)" and 
          "weight (llast (LCons v Ps)) v' \<noteq> None" and "valid_play (LCons v' Ps')"
  shows "valid_play (lappend (LCons v Ps) (LCons v' Ps'))"
using assms proof(induction "list_of Ps" arbitrary: v Ps)
  case Nil
  then show ?case using valid_play.simps
    by (metis lappend_code(2) lappend_lnull1 lfinite_LCons lhd_LCons lhd_LCons_ltl list.distinct(1) list_of_LCons llast_singleton llist.collapse(1) llist.disc(2))
next
  case (Cons a x)
  then show ?case using valid_play.simps
    by (smt (verit) lappend_code(2) lfinite_LCons lfinite_llist_of lhd_lappend list_of_llist_of llast_LCons llist.discI(2) llist.distinct(1) llist_of.simps(2) llist_of_list_of ltl_simps(2) valid_play.intros(3))
qed

lemma valid_play_coinduct:
  assumes "Q p" and  
          "\<And>v Ps. Q (LCons v Ps) \<Longrightarrow> Ps\<noteq>LNil \<Longrightarrow> Q Ps \<and> weight v (lhd Ps) \<noteq> None"
  shows "valid_play p"
  using assms proof(coinduction arbitrary: p)
  case valid_play
  then show ?case 
  proof (cases "p = LNil")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis 
    proof(cases "(\<exists>v. p = LCons v LNil)")
      case True
      then show ?thesis by simp
    next
      case False
      hence "\<exists>v Ps. p = LCons v Ps \<and> \<not> lnull Ps" using \<open>\<not>p = LNil\<close>
        by (metis llist.collapse(1) not_lnull_conv)
      from this obtain v Ps where "p = LCons v Ps \<and> \<not> lnull Ps" by blast
      hence "Q Ps \<and> weight v (lhd Ps) \<noteq> None" using valid_play
        using llist.disc(1) by blast 
      then show ?thesis using valid_play.simps valid_play
        using \<open>p = LCons v Ps \<and> \<not> lnull Ps\<close> by blast 
    qed
  qed
qed

lemma valid_play_nth_not_None:
  assumes "valid_play p" and "Suc i < llength p"
  shows "weight (lnth p i) (lnth p (Suc i)) \<noteq> None"
proof- 
  have "\<exists>prefix p'. p = lappend prefix p' \<and> llength prefix = Suc i \<and> weight (llast prefix) (lhd p') \<noteq> None \<and> valid_play p'"
    using assms proof(induct i)
    case 0
    hence "\<exists>v Ps. p = LCons v Ps"
      by (metis llength_LNil neq_LNil_conv not_less_zero) 
    from this obtain v Ps where "p = LCons v Ps" by auto
    hence "p = lappend (LCons v LNil) Ps"
      by (simp add: lappend_code(2)) 
    have "llength (LCons v LNil) = Suc 0" using one_eSuc one_enat_def by simp
    have "weight v (lhd Ps) \<noteq> None" using 0 valid_play.simps \<open>p = LCons v Ps\<close>
      by (smt (verit) One_nat_def add.commute gen_llength_code(1) gen_llength_code(2) less_numeral_extra(4) lhd_LCons llength_code llist.distinct(1) ltl_simps(2) one_enat_def plus_1_eq_Suc) 
    hence "p = lappend (LCons v LNil) Ps \<and> llength (LCons v LNil) = Suc 0 \<and> weight (llast (LCons v LNil)) (lhd Ps) \<noteq> None" using \<open>p = LCons v Ps\<close>
      using \<open>p = lappend (LCons v LNil) Ps\<close> \<open>llength (LCons v LNil) = Suc 0\<close>
      by simp
    hence "p = lappend (LCons v LNil) Ps \<and> llength (LCons v LNil) = Suc 0 \<and> weight (llast (LCons v LNil)) (lhd Ps) \<noteq> None \<and> valid_play Ps" using valid_play.simps 0
      by (metis (no_types, lifting) \<open>p = LCons v Ps\<close> llist.distinct(1) ltl_simps(2)) 
    then show ?case by blast
  next
    case (Suc l)
    hence "\<exists>prefix p'. p = lappend prefix p' \<and> llength prefix = enat (Suc l) \<and> weight (llast prefix) (lhd p') \<noteq> None \<and> valid_play p'"
      using Suc_ile_eq order_less_imp_le by blast
    from this obtain prefix p' where P: "p = lappend prefix p' \<and> llength prefix = enat (Suc l) \<and> weight (llast prefix) (lhd p') \<noteq> None \<and> valid_play p'" by auto
    have "p = lappend (lappend prefix (LCons (lhd p') LNil)) (ltl p') \<and> llength (lappend prefix (LCons (lhd p') LNil)) = enat (Suc (Suc l)) \<and> weight (llast (lappend prefix (LCons (lhd p') LNil))) (lhd (ltl p')) \<noteq> None \<and> valid_play (ltl p')"
    proof
      show "p = lappend (lappend prefix (LCons (lhd p') LNil)) (ltl p')" using P
        by (metis Suc.prems(2) enat_ord_simps(2) lappend_LNil2 lappend_snocL1_conv_LCons2 lessI llist.exhaust_sel order.asym) 
      show "llength (lappend prefix (LCons (lhd p') LNil)) = enat (Suc (Suc l)) \<and>
    weight (llast (lappend prefix (LCons (lhd p') LNil))) (lhd (ltl p')) \<noteq> None \<and> valid_play (ltl p')"
      proof
        have "llength (lappend prefix (LCons (lhd p') LNil)) = 1+ (llength prefix)"
          by (smt (verit, best) add.commute epred_1 epred_inject epred_llength llength_LNil llength_eq_0 llength_lappend llist.disc(2) ltl_simps(2) zero_neq_one)
        thus "llength (lappend prefix (LCons (lhd p') LNil)) = enat (Suc (Suc l))" using P
          by (simp add: one_enat_def) 
        show "weight (llast (lappend prefix (LCons (lhd p') LNil))) (lhd (ltl p')) \<noteq> None \<and> valid_play (ltl p') "
        proof
          show "weight (llast (lappend prefix (LCons (lhd p') LNil))) (lhd (ltl p')) \<noteq> None" using P valid_play.simps
            by (metis Suc.prems(2) \<open>llength (lappend prefix (LCons (lhd p') LNil)) = 1 + llength prefix\<close> \<open>llength (lappend prefix (LCons (lhd p') LNil)) = enat (Suc (Suc l))\<close> \<open>p = lappend (lappend prefix (LCons (lhd p') LNil)) (ltl p')\<close> add.commute enat_add_mono eq_LConsD lappend_LNil2 less_numeral_extra(4) llast_lappend_LCons llast_singleton llength_eq_enat_lfiniteD ltl_simps(1))
          show "valid_play (ltl p')" using P valid_play.simps
            by (metis (full_types) energy_game.valid_play.intros(1) ltl_simps(1) ltl_simps(2)) 
        qed
      qed
    qed
    then show ?case by blast
  qed
  thus ?thesis
    by (smt (z3) assms(2) cancel_comm_monoid_add_class.diff_cancel eSuc_enat enat_ord_simps(2) lappend_eq_lappend_conv lappend_lnull2 lessI lhd_LCons_ltl linorder_neq_iff llast_conv_lnth lnth_0 lnth_lappend the_enat.simps)
qed

lemma valid_play_nth:
  assumes "\<And>i. enat (Suc i) < llength p 
               \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None"
  shows "valid_play p"
  using assms proof(coinduction arbitrary: p rule: valid_play_coinduct)
  show "\<And>v Ps p.
       LCons v Ps = p \<Longrightarrow>
       \<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None \<Longrightarrow>
       Ps \<noteq> LNil \<Longrightarrow>
       (\<exists>p. Ps = p \<and> (\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None)) \<and>
       weight v (lhd Ps) \<noteq> None"
  proof-
    fix v Ps p
    show "LCons v Ps = p \<Longrightarrow>
       \<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None \<Longrightarrow>
       Ps \<noteq> LNil \<Longrightarrow>
       (\<exists>p. Ps = p \<and> (\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None)) \<and>
       weight v (lhd Ps) \<noteq> None"
    proof-
      assume "LCons v Ps = p"
      show "\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None \<Longrightarrow>
       Ps \<noteq> LNil \<Longrightarrow>
       (\<exists>p. Ps = p \<and> (\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None)) \<and>
       weight v (lhd Ps) \<noteq> None"
      proof-
        assume A: "\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None"
        show "Ps \<noteq> LNil \<Longrightarrow>
       (\<exists>p. Ps = p \<and> (\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None)) \<and>
       weight v (lhd Ps) \<noteq> None"
        proof-
          assume "Ps \<noteq> LNil"
          show "(\<exists>p. Ps = p \<and> (\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None)) \<and>
       weight v (lhd Ps) \<noteq> None"
          proof
            show "\<exists>p. Ps = p \<and> (\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None)"
            proof
              have "(\<forall>i. enat (Suc i) < llength Ps \<longrightarrow> weight (lnth Ps i) (lnth Ps (Suc i)) \<noteq> None)"
              proof
                fix i 
                show "enat (Suc i) < llength Ps \<longrightarrow> weight (lnth Ps i) (lnth Ps (Suc i)) \<noteq> None "
                proof
                  assume "enat (Suc i) < llength Ps"
                  hence "enat (Suc (Suc i)) < llength (LCons v Ps)"
                    by (metis ldropn_Suc_LCons ldropn_eq_LNil linorder_not_le) 
                  have "(lnth Ps i) = (lnth (LCons v Ps) (Suc i))" by simp
                  have "(lnth Ps (Suc i)) = (lnth (LCons v Ps) (Suc (Suc i)))" by simp
                  thus "weight (lnth Ps i) (lnth Ps (Suc i)) \<noteq> None"
                    using A \<open>(lnth Ps i) = (lnth (LCons v Ps) (Suc i))\<close>
                    using \<open>LCons v Ps = p\<close> \<open>enat (Suc (Suc i)) < llength (LCons v Ps)\<close> by auto
                qed
              qed
              thus "Ps = Ps \<and> (\<forall>i. enat (Suc i) < llength Ps \<longrightarrow> weight (lnth Ps i) (lnth Ps (Suc i)) \<noteq> None)"
                by simp
            qed
            have "v = lnth (LCons v Ps) 0" by simp
            have "lhd Ps = lnth (LCons v Ps) (Suc 0)" using lnth_def \<open>Ps \<noteq> LNil\<close>
              by (metis llist.exhaust_sel lnth_0 lnth_Suc_LCons) 
            thus "weight v (lhd Ps) \<noteq> None"
              using \<open>v = lnth (LCons v Ps) 0\<close> A
              by (metis \<open>LCons v Ps = p\<close> \<open>Ps \<noteq> LNil\<close> \<open>\<exists>p. Ps = p \<and> (\<forall>i. enat (Suc i) < llength p \<longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None)\<close> gen_llength_code(1) ldropn_0 ldropn_Suc_LCons ldropn_eq_LConsD llist.collapse(1) lnth_Suc_LCons not_lnull_conv)
          qed
        qed
      qed
    qed
  qed
qed

text\<open>\subsubsection*{Energy Levels}

The energy level of a play is calculated by repeatedly updating the current energy according to the 
edges in the play.
The final energy level of a finite play is \<open>energy_level e p (the_enat (llength p -1))\<close> where \<open>e\<close> is the initial energy.\<close>

fun energy_level:: "'energy \<Rightarrow> 'position llist \<Rightarrow> nat \<Rightarrow> 'energy option" where 
 "energy_level e p 0 = (if p = LNil then None else Some e)" |
 "energy_level e p (Suc i) = 
          (if (energy_level e p i) = None \<or> llength p \<le> (Suc i) then None 
           else apply_w (lnth p i)(lnth p (Suc i)) (the (energy_level e p i)))"

text\<open>We establish some (in)equalities to simplify later proofs.\<close>

lemma energy_level_cons:
  assumes "valid_play (LCons v Ps)"  and "\<not>lnull Ps" and 
          "apply_w v (lhd Ps) e \<noteq> None" and "enat i < (llength Ps)"
  shows "energy_level (the (apply_w v (lhd Ps) e)) Ps i 
         = energy_level e (LCons v Ps) (Suc i)"
  using assms proof(induction i arbitrary: e Ps rule: energy_level.induct)
  case (1 e p) 
  then show ?case using energy_level.simps
    by (smt (verit) ldropn_Suc_LCons ldropn_eq_LNil le_zero_eq lhd_conv_lnth llength_eq_0 llist.distinct(1) lnth_0 lnth_Suc_LCons lnull_def option.collapse option.discI option.sel zero_enat_def)
next
  case (2 e p n)
  hence "enat n < (llength Ps)"
    using Suc_ile_eq nless_le by blast
  hence IA: "energy_level (the (apply_w v (lhd Ps) e)) Ps n = energy_level e (LCons v Ps) (Suc n)"
    using 2 by simp 
  have "(llength Ps) > Suc n" using \<open>enat (Suc n) < (llength Ps)\<close>
    by simp
  hence "llength (LCons v Ps) > (Suc (Suc n))"
    by (metis ldropn_Suc_LCons ldropn_eq_LNil linorder_not_less) 
  show "energy_level (the (apply_w v (lhd Ps) e)) Ps (Suc n) = energy_level e (LCons v Ps) (Suc (Suc n))" 
  proof(cases "energy_level e (LCons v Ps) (Suc (Suc n)) = None")
    case True
    hence "(energy_level e (LCons v Ps) (Suc n)) = None \<or> llength (LCons v Ps) \<le> (Suc (Suc n)) \<or> apply_w (lnth (LCons v Ps) (Suc n)) (lnth (LCons v Ps) (Suc (Suc n))) (the (energy_level e (LCons v Ps) (Suc n))) = None " 
      using energy_level.simps
      by metis
    hence  none: "(energy_level e (LCons v Ps) (Suc n)) = None \<or> apply_w (lnth (LCons v Ps) (Suc n)) (lnth (LCons v Ps) (Suc (Suc n))) (the (energy_level e (LCons v Ps) (Suc n))) = None " 
      using \<open>llength (LCons v Ps) > (Suc (Suc n))\<close>
      by (meson linorder_not_less)
    show ?thesis 
    proof(cases "(energy_level e (LCons v Ps) (Suc n)) = None")
      case True
      then show ?thesis using IA by simp 
    next
      case False
      hence "apply_w (lnth (LCons v Ps) (Suc n)) (lnth (LCons v Ps) (Suc (Suc n))) (the (energy_level e (LCons v Ps) (Suc n))) = None " 
        using none by auto
      hence "apply_w (lnth (LCons v Ps) (Suc n)) (lnth (LCons v Ps) (Suc (Suc n))) (the (energy_level (the (apply_w v (lhd Ps) e)) Ps n)) = None " 
        using IA by auto
      then show ?thesis by (simp add: IA)
    qed
  next
    case False
    then show ?thesis using IA
      by (smt (verit) \<open>enat (Suc n) < llength Ps\<close> energy_level.simps(2) lnth_Suc_LCons order.asym order_le_imp_less_or_eq)
  qed
qed

lemma energy_level_nth:
  assumes "energy_level e p m \<noteq> None" and "Suc i \<le> m"
  shows "apply_w (lnth p i) (lnth p (Suc i)) (the (energy_level e p i)) \<noteq> None 
         \<and> energy_level e p i \<noteq> None"
using assms proof(induct "m - (Suc i)" arbitrary: i)
  case 0
  then show ?case using energy_level.simps
    by (metis diff_diff_cancel minus_nat.diff_0)
next
  case (Suc x)
  hence "x = m - Suc (Suc i)"
    by (metis add_Suc_shift diff_add_inverse2 diff_le_self le_add_diff_inverse)
  hence "apply_w (lnth p (Suc i)) (lnth p (Suc (Suc i))) (the (energy_level e p (Suc i))) \<noteq> None \<and> (energy_level e p (Suc i)) \<noteq> None" using Suc
    by (metis diff_is_0_eq nat.distinct(1) not_less_eq_eq) 
  then show ?case using energy_level.simps by metis
qed

lemma energy_level_append: 
  assumes "lfinite p" and "i < the_enat (llength p)" and 
          "energy_level e p (the_enat (llength p) -1) \<noteq> None"
  shows "energy_level e p i = energy_level e (lappend p p') i"
proof-
  have A: "\<And>i. i < the_enat (llength p) \<Longrightarrow> energy_level e p i \<noteq> None" using energy_level_nth assms
    by (metis Nat.lessE diff_Suc_1 less_eq_Suc_le) 
  show ?thesis using assms A proof(induct i)
    case 0
    then show ?case using energy_level.simps
      by (metis LNil_eq_lappend_iff llength_lnull llist.disc(1) the_enat_0 verit_comp_simplify1(1)) 
  next
    case (Suc i)
    hence "energy_level e p i = energy_level e (lappend p p') i"
      by simp 
    have "Suc i < (llength p) \<and> energy_level e p i \<noteq> None" using Suc
      by (metis Suc_lessD enat_ord_simps(2) lfinite_conv_llength_enat the_enat.simps)
    hence "Suc i <  (llength (lappend p p')) \<and> energy_level e (lappend p p') i \<noteq> None" 
      using \<open>energy_level e p i = energy_level e (lappend p p') i\<close>
      by (metis dual_order.strict_trans1 enat_le_plus_same(1) llength_lappend)
    then show ?case unfolding energy_level.simps using \<open>Suc i < (llength p) \<and> energy_level e p i \<noteq> None\<close> \<open>energy_level e p i = energy_level e (lappend p p') i\<close>
    by (smt (verit) Suc_ile_eq energy_level.elims le_zero_eq linorder_not_less lnth_lappend1 nle_le the_enat.simps zero_enat_def)
  qed
qed

text\<open>\subsubsection*{Won Plays}

All infinite plays are won by the defender. Further, the attacker is energy-bound and the defender
wins if the energy level becomes \<open>None\<close>. Finite plays with an energy level that is not \<open>None\<close> are won by 
a player, if the other is stuck.\<close>

abbreviation "deadend g \<equiv> (\<forall>g'. weight g g' = None)"
abbreviation "attacker_stuck p \<equiv> (llast p)\<in> attacker \<and> deadend (llast p)"

definition defender_wins_play:: "'energy \<Rightarrow> 'position llist \<Rightarrow> bool" where
  "defender_wins_play e p \<equiv> lfinite p \<longrightarrow> 
         (energy_level e p (the_enat (llength p)-1) = None \<or> attacker_stuck p)"

subsection\<open>Energy-positional Strategies\<close>

text\<open>
Energy-positional strategies map pairs of energies and positions to a next position.
Further, we focus on attacker strategies, i.e.\ partial functions mapping attacker positions to successors.\<close>

definition attacker_strategy:: "('energy \<Rightarrow> 'position \<Rightarrow> 'position option) \<Rightarrow> bool" where 
  "attacker_strategy s = (\<forall>g e. (g \<in> attacker \<and> \<not> deadend g) \<longrightarrow> 
                           (s e g \<noteq> None \<and> weight g (the (s e g))  \<noteq> None))"

text\<open>We now define what it means for a play to be consistent with some strategy.\<close>

coinductive play_consistent_attacker::"('energy \<Rightarrow> 'position \<Rightarrow> 'position option) \<Rightarrow> 'position llist  \<Rightarrow> 'energy \<Rightarrow> bool" where
  "play_consistent_attacker _ LNil _" |
  "play_consistent_attacker _ (LCons v LNil) _" |
  "\<lbrakk>play_consistent_attacker s Ps (the (apply_w v (lhd Ps) e)); \<not>lnull Ps; 
    v \<in> attacker \<longrightarrow> (s e v) = Some (lhd Ps)\<rbrakk> 
    \<Longrightarrow> play_consistent_attacker s (LCons v Ps) e"

text\<open>The coinductive definition allows for coinduction.\<close>

lemma play_consistent_attacker_coinduct:
  assumes "Q s p e" and  
          "\<And>s v Ps e'. Q s (LCons v Ps) e' \<and> \<not>lnull Ps \<Longrightarrow> 
                        Q s Ps (the (apply_w v (lhd Ps) e')) \<and>
                        (v \<in> attacker \<longrightarrow> s e' v = Some (lhd Ps))"
  shows "play_consistent_attacker s p e"
  using assms proof(coinduction arbitrary: s p e)
  case play_consistent_attacker
  then show ?case 
  proof(cases "p = LNil")
    case True
    then show ?thesis by simp
  next
    case False
    hence "\<exists> v Ps. p = LCons v Ps"
      by (meson llist.exhaust) 
    from this obtain v Ps where "p = LCons v Ps" by auto
    then show ?thesis 
    proof(cases "Ps = LNil")
      case True
      then show ?thesis using \<open>p = LCons v Ps\<close> by simp 
    next
      case False
      hence "Q s Ps (the (apply_w v (lhd Ps) e)) \<and> (v \<in> attacker \<longrightarrow> s e v = Some (lhd Ps))"
        using assms
        using \<open>p = LCons v Ps\<close> llist.collapse(1) play_consistent_attacker(1) by blast 
      then show ?thesis using play_consistent_attacker play_consistent_attacker.simps
        by (metis (no_types, lifting) \<open>p = LCons v Ps\<close> lnull_def)
    qed
  qed
qed

text\<open>Adding a position to the beginning of a consistent play is simple by definition. 
It is harder to see, when a position can be added to the end of a finite play. For this we introduce the following lemma.\<close>

lemma play_consistent_attacker_append_one:
  assumes "play_consistent_attacker s p e" and "lfinite p" and 
          "energy_level e p (the_enat (llength p)-1) \<noteq> None" and 
          "valid_play (lappend p (LCons g LNil))" and "llast p \<in> attacker \<longrightarrow> 
           Some g = s (the (energy_level e p (the_enat (llength p)-1))) (llast p)" 
  shows "play_consistent_attacker s (lappend p (LCons g LNil)) e"
using assms proof(induct "the_enat (llength p)" arbitrary: p e)
  case 0
  then show ?case
    by (metis lappend_lnull1 length_list_of length_list_of_conv_the_enat llength_eq_0 play_consistent_attacker.simps zero_enat_def)
next
  case (Suc x)
  hence "\<exists>v Ps. p = LCons v Ps"
    by (metis Zero_not_Suc llength_LNil llist.exhaust the_enat_0) 
  from this obtain v Ps where "p = LCons v Ps" by auto

  have B: "play_consistent_attacker s (lappend Ps (LCons g LNil)) (the (apply_w v (lhd (lappend Ps (LCons g LNil)))e))" 
  proof(cases "Ps=LNil")
    case True
    then show ?thesis
      by (simp add: play_consistent_attacker.intros(2))
  next
    case False
    show ?thesis 
    proof(rule Suc.hyps)
      show "valid_play (lappend Ps (LCons g LNil))"
        by (metis (no_types, lifting) LNil_eq_lappend_iff Suc.prems(4) \<open>p = LCons v Ps\<close> lappend_code(2) llist.distinct(1) llist.inject valid_play.cases) 
      show "x = the_enat (llength Ps)"  using Suc \<open>p = LCons v Ps\<close>
        by (metis diff_add_inverse length_Cons length_list_of_conv_the_enat lfinite_ltl list_of_LCons ltl_simps(2) plus_1_eq_Suc) 
      show "play_consistent_attacker s Ps (the (apply_w v (lhd (lappend Ps (LCons g LNil))) e))"
        using False Suc.prems(1) \<open>p = LCons v Ps\<close> play_consistent_attacker.cases by fastforce
      show "lfinite Ps" using Suc \<open>p = LCons v Ps\<close> by simp

      hence EL: "energy_level (the (apply_w v (lhd (lappend Ps (LCons g LNil))) e)) Ps
     (the_enat (llength Ps) - 1) = energy_level e (LCons v (lappend Ps (LCons g LNil))) 
     (Suc (the_enat (llength Ps) - 1))"
      proof-
        have A: "valid_play (LCons v Ps) \<and>  \<not> lnull Ps \<and>  apply_w v (lhd Ps) e \<noteq> None \<and>
  enat (the_enat (llength Ps) - 1) < llength Ps"
        proof
          show "valid_play (LCons v Ps)" proof(rule valid_play_nth)
            fix i
            show "enat (Suc i) < llength (LCons v Ps) \<longrightarrow>
         weight (lnth (LCons v Ps) i) (lnth (LCons v Ps) (Suc i)) \<noteq> None "
            proof
              assume "enat (Suc i) < llength (LCons v Ps)"
              hence "(lnth (LCons v Ps) i) = (lnth (lappend p (LCons g LNil)) i)" using \<open>p = LCons v Ps\<close>
                by (metis Suc_ile_eq lnth_lappend1 order.strict_implies_order) 
              have "(lnth (LCons v Ps) (Suc i)) = (lnth (lappend p (LCons g LNil)) (Suc i))" using \<open>p = LCons v Ps\<close> \<open>enat (Suc i) < llength (LCons v Ps)\<close>
                by (metis lnth_lappend1) 

              from Suc have "valid_play (lappend p (LCons g LNil))" by simp
              hence "weight (lnth (lappend p (LCons g LNil)) i) (lnth (lappend p (LCons g LNil)) (Suc i)) \<noteq> None"
                using \<open>enat (Suc i) < llength (LCons v Ps)\<close> valid_play_nth_not_None
                by (metis Suc.prems(2) \<open>p = LCons v Ps\<close> llist.disc(2) lstrict_prefix_lappend_conv lstrict_prefix_llength_less min.absorb4 min.strict_coboundedI1) 

              thus "weight (lnth (LCons v Ps) i) (lnth (LCons v Ps) (Suc i)) \<noteq> None"
                using \<open>(lnth (LCons v Ps) (Suc i)) = (lnth (lappend p (LCons g LNil)) (Suc i))\<close> \<open>(lnth (LCons v Ps) i) = (lnth (lappend p (LCons g LNil)) i)\<close> by simp
            qed
          qed
          show "\<not> lnull Ps \<and> apply_w v (lhd Ps) e \<noteq> None \<and> enat (the_enat (llength Ps) - 1) < llength Ps"
          proof
            show "\<not> lnull Ps" using False by auto 
            show "apply_w v (lhd Ps) e \<noteq> None \<and> enat (the_enat (llength Ps) - 1) < llength Ps"
            proof
              show "apply_w v (lhd Ps) e \<noteq> None" using Suc
                by (smt (verit, ccfv_threshold) One_nat_def \<open>\<not> lnull Ps\<close> \<open>lfinite Ps\<close> \<open>p = LCons v Ps\<close> \<open>x = the_enat (llength Ps)\<close> diff_add_inverse energy_level.simps(1) energy_level_nth le_SucE le_add1 length_list_of length_list_of_conv_the_enat lhd_conv_lnth llength_eq_0 llist.discI(2) lnth_0 lnth_ltl ltl_simps(2) option.sel plus_1_eq_Suc zero_enat_def) 
              show "enat (the_enat (llength Ps) - 1) < llength Ps" using False
                by (metis \<open>\<not> lnull Ps\<close> \<open>lfinite Ps\<close> diff_Suc_1 enat_0_iff(2) enat_ord_simps(2) gr0_conv_Suc lessI lfinite_llength_enat llength_eq_0 not_gr_zero the_enat.simps)
            qed
          qed
        qed

        have "energy_level (the (apply_w v (lhd (lappend Ps (LCons g LNil))) e)) Ps
     (the_enat (llength Ps) - 1) = energy_level (the (apply_w v (lhd Ps) e)) Ps
     (the_enat (llength Ps) - 1)" using False
          by (simp add: lnull_def) 
        also have "... = energy_level e (LCons v Ps) (Suc (the_enat (llength Ps) - 1))" 
          using energy_level_cons A by simp
        also have "... = energy_level e (LCons v (lappend Ps (LCons g LNil))) 
     (Suc (the_enat (llength Ps) - 1))" using energy_level_append
          by (metis False One_nat_def Suc.hyps(2) Suc.prems(2) Suc.prems(3) \<open>lfinite Ps\<close> \<open>p = LCons v Ps\<close> \<open>x = the_enat (llength Ps)\<close> diff_Suc_less lappend_code(2) length_list_of length_list_of_conv_the_enat less_SucE less_Suc_eq_0_disj llength_eq_0 llist.disc(1) llist.expand nat_add_left_cancel_less plus_1_eq_Suc zero_enat_def) 
        finally show ?thesis .
      qed

      thus EL_notNone: "energy_level (the (apply_w v (lhd (lappend Ps (LCons g LNil))) e)) Ps
     (the_enat (llength Ps) - 1) \<noteq> None" 
        using Suc
        by (metis False One_nat_def Suc_pred \<open>p = LCons v Ps\<close> \<open>x = the_enat (llength Ps)\<close> diff_Suc_1' energy_level.simps(1) energy_level_append lappend_code(2) lessI not_less_less_Suc_eq not_one_less_zero option.distinct(1) zero_less_Suc zero_less_diff) 

      show "llast Ps \<in> attacker \<longrightarrow>
    Some g = s (the (energy_level (the (apply_w v (lhd (lappend Ps (LCons g LNil))) e)) Ps
             (the_enat (llength Ps) - 1)))(llast Ps)"
      proof
        assume "llast Ps \<in> attacker"
        have "llast Ps = llast p" using False \<open>p = LCons v Ps\<close>
          by (simp add: llast_LCons lnull_def)
        hence "llast p \<in> attacker" using \<open>llast Ps \<in> attacker\<close> by simp
        hence "Some g = s (the (energy_level e p (the_enat (llength p) - 1))) (llast p)" using Suc by simp
        hence "Some g = s (the (energy_level e (LCons v Ps) (the_enat (llength (LCons v Ps)) - 1))) (llast Ps)" using \<open>p = LCons v Ps\<close> \<open>llast Ps = llast p\<close> by simp

        have "apply_w v (lhd Ps) e \<noteq> None" using Suc
          by (smt (verit, best) EL EL_notNone False One_nat_def energy_level.simps(1) energy_level_nth le_add1 lhd_conv_lnth lhd_lappend llist.discI(2) llist.exhaust_sel lnth_0 lnth_Suc_LCons lnull_lappend option.sel plus_1_eq_Suc)
        thus  "Some g = s (the (energy_level (the (apply_w v (lhd (lappend Ps (LCons g LNil))) e)) Ps
             (the_enat (llength Ps) - 1)))(llast Ps)" using EL
          by (metis (no_types, lifting) False Suc.hyps(2) Suc.prems(2) Suc.prems(3) Suc_diff_Suc \<open>Some g = s (the (energy_level e (LCons v Ps) (the_enat (llength (LCons v Ps)) - 1))) (llast Ps)\<close> \<open>lfinite Ps\<close> \<open>p = LCons v Ps\<close> \<open>x = the_enat (llength Ps)\<close> cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 energy_level_append lappend_code(2) lessI lfinite.cases lfinite_conv_llength_enat linorder_neqE_nat llength_eq_0 llist.discI(2) not_add_less1 plus_1_eq_Suc the_enat.simps zero_enat_def) 
      qed
    qed
  qed

  have A: "\<not> lnull (lappend Ps (LCons g LNil)) \<and> (v \<in> attacker \<longrightarrow> (s e v = Some (lhd (lappend Ps (LCons g LNil)))))"
  proof
    show "\<not> lnull (lappend Ps (LCons g LNil))" by simp
    show "v \<in> attacker \<longrightarrow>
    s e v = Some (lhd (lappend Ps (LCons g LNil)))"
    proof
      assume "v \<in> attacker"
      show "s e v = Some (lhd (lappend Ps (LCons g LNil)))" using \<open>v \<in> attacker\<close> Suc
        by (smt (verit) One_nat_def \<open>p = LCons v Ps\<close> diff_add_0 energy_game.energy_level.simps(1) eq_LConsD length_Cons length_list_of_conv_the_enat lfinite_ltl lhd_lappend list.size(3) list_of_LCons list_of_LNil llast_singleton llist.disc(1) option.exhaust_sel option.inject play_consistent_attacker.cases plus_1_eq_Suc) 
    qed
  qed

  have "(lappend p (LCons g LNil)) = LCons v (lappend Ps (LCons g LNil))"
    by (simp add: \<open>p = LCons v Ps\<close>) 
  thus ?case using play_consistent_attacker.simps A B
    by meson
qed

text\<open>We now define attacker winning strategies, i.e.\ attacker strategies where the defender does not win any consistent plays w.r.t\ some initial energy and a starting position.\<close>

fun attacker_winning_strategy:: "('energy \<Rightarrow> 'position \<Rightarrow> 'position option) \<Rightarrow> 'energy \<Rightarrow> 'position \<Rightarrow> bool" where
  "attacker_winning_strategy s e g = (attacker_strategy s \<and> 
      (\<forall>p. (play_consistent_attacker s (LCons g p) e \<and> valid_play (LCons g p))
            \<longrightarrow> \<not>defender_wins_play e (LCons g p)))"

subsection\<open>Non-positional Strategies\<close>

text\<open>A non-positional strategy maps finite plays to a next position. We now introduce non-positional strategies to better characterise attacker winning budgets. 
These definitions closely resemble the definitions for energy-positional strategies.\<close>

definition attacker_nonpos_strategy:: "('position list \<Rightarrow> 'position option) \<Rightarrow> bool" where 
  "attacker_nonpos_strategy s = (\<forall>list \<noteq> []. ((last list) \<in> attacker 
   \<and> \<not>deadend (last list)) \<longrightarrow> s list \<noteq> None 
                               \<and> (weight (last list) (the (s list)))\<noteq>None)"

text\<open>We now define what it means for a play to be consistent with some non-positional strategy.\<close>

coinductive play_consistent_attacker_nonpos::"('position list \<Rightarrow> 'position option) \<Rightarrow> ('position llist) \<Rightarrow> ('position list) \<Rightarrow> bool" where
  "play_consistent_attacker_nonpos s LNil _" |
  "play_consistent_attacker_nonpos s (LCons v LNil) []" |
  "(last (w#l))\<notin>attacker 
  \<Longrightarrow> play_consistent_attacker_nonpos s (LCons v LNil) (w#l)" |
  "\<lbrakk>(last (w#l))\<in>attacker; the (s (w#l)) = v \<rbrakk> 
  \<Longrightarrow> play_consistent_attacker_nonpos s (LCons v LNil) (w#l)" |
  "\<lbrakk>play_consistent_attacker_nonpos s Ps (l@[v]); \<not>lnull Ps; v\<notin>attacker\<rbrakk>
   \<Longrightarrow> play_consistent_attacker_nonpos s (LCons v Ps) l" |
  "\<lbrakk>play_consistent_attacker_nonpos s Ps (l@[v]); \<not>lnull Ps; v\<in>attacker; 
    lhd Ps = the (s (l@[v]))\<rbrakk>
    \<Longrightarrow> play_consistent_attacker_nonpos s (LCons v Ps) l"

inductive_simps play_consistent_attacker_nonpos_cons_simp: 
  "play_consistent_attacker_nonpos s (LCons x xs) []"

text\<open>The definition allows for coinduction.\<close>

lemma play_consistent_attacker_nonpos_coinduct:
  assumes "Q s p l" and 
         base: "\<And>s v l. Q s (LCons v LNil) l \<Longrightarrow> (l = [] \<or> (last l) \<notin> attacker 
                \<or> ((last l)\<in>attacker \<and> the (s l) = v))" and 
         step: "\<And>s v Ps l. Q s (LCons v Ps) l \<and> Ps\<noteq>LNil 
                \<Longrightarrow> Q s Ps (l@[v]) \<and> (v\<in>attacker \<longrightarrow> lhd Ps = the (s (l@[v])))"
  shows "play_consistent_attacker_nonpos s p l"
  using assms proof(coinduction arbitrary: s p l)
  case play_consistent_attacker_nonpos
  then show ?case proof(cases "p=LNil")
    case True
    then show ?thesis by simp
  next
    case False
    hence "\<exists>v p'. p = LCons v p'"
      by (simp add: neq_LNil_conv)
    from this obtain v p' where "p=LCons v p'" by auto
    then show ?thesis proof(cases "p'=LNil")
      case True
      then show ?thesis
        by (metis \<open>p = LCons v p'\<close> neq_Nil_conv play_consistent_attacker_nonpos(1) play_consistent_attacker_nonpos(2))
    next
      case False
      then show ?thesis
        using \<open>p = LCons v p'\<close> assms(3) llist.expand play_consistent_attacker_nonpos(1) assms(2) by auto 
    qed
  qed
qed

text\<open>We now show that a position can be added to the end of a finite consitent play while remaining consistent.\<close>

lemma consistent_nonpos_append_defender:
  assumes "play_consistent_attacker_nonpos s (LCons v Ps) l" and 
          "llast (LCons v Ps) \<notin> attacker" and "lfinite (LCons v Ps)"
  shows "play_consistent_attacker_nonpos s (lappend (LCons v Ps) (LCons g' LNil)) l"
  using assms proof(induction "list_of Ps" arbitrary: v Ps l)
  case Nil
  hence v_append_Ps: "play_consistent_attacker_nonpos s (lappend (LCons v Ps) (LCons g' LNil)) l = play_consistent_attacker_nonpos s (LCons v (LCons g' LNil)) l"
    by (metis lappend_code(1) lappend_code(2) lfinite_LCons llist_of_eq_LNil_conv llist_of_list_of)

  from Nil.prems(1) have "play_consistent_attacker_nonpos s (LCons g' LNil) (l@[v])" using play_consistent_attacker_nonpos.intros Nil
    by (metis (no_types, lifting) lfinite_LCons list.exhaust_sel llast_singleton llist_of.simps(1) llist_of_list_of snoc_eq_iff_butlast)
  hence "play_consistent_attacker_nonpos s (LCons v (LCons g' LNil)) l" using play_consistent_attacker_nonpos.intros Nil
    by (metis lfinite_code(2) llast_singleton llist.disc(2) llist_of.simps(1) llist_of_list_of) 
  then show ?case using v_append_Ps by simp
next
  case (Cons a x)
  hence v_append_Ps: "play_consistent_attacker_nonpos s (lappend (LCons v Ps) (LCons g' LNil)) l = play_consistent_attacker_nonpos s (LCons v (lappend Ps (LCons g' LNil))) l"
    by simp

  from Cons have "\<not>lnull Ps"
    by (metis list.discI list_of_LNil llist.collapse(1)) 

  have "\<not> lnull (lappend Ps (LCons g' LNil))" by simp

  have "x = list_of (ltl Ps)" using Cons.hyps(2)
    by (metis Cons.prems(3) lfinite_code(2) list.sel(3) tl_list_of)
  have "llast (LCons (lhd Ps) (ltl Ps)) \<notin> attacker" using Cons.prems(2)
    by (simp add: \<open>\<not> lnull Ps\<close> llast_LCons) 
  have "lfinite (LCons (lhd Ps) (ltl Ps))" using Cons.prems(3) by simp
  have "play_consistent_attacker_nonpos s (LCons (lhd Ps) (ltl Ps)) (l @ [v])" using Cons.prems(1) play_consistent_attacker_nonpos.simps
    by (smt (verit, best) \<open>\<not> lnull Ps\<close> eq_LConsD lhd_LCons lhd_LCons_ltl ltl_simps(2))
  hence "play_consistent_attacker_nonpos s (lappend Ps (LCons g' LNil)) (l @ [v])" using Cons.hyps \<open>lfinite (LCons (lhd Ps) (ltl Ps))\<close> \<open>llast (LCons (lhd Ps) (ltl Ps)) \<notin> attacker\<close> \<open>x = list_of (ltl Ps)\<close>
    by (metis \<open>\<not> lnull Ps\<close> lhd_LCons_ltl)

  have "play_consistent_attacker_nonpos s (LCons v (lappend Ps (LCons g' LNil))) l" 
  proof(cases "v \<in> attacker")
    case True
    have "lhd Ps = the (s (l @ [v]))" using True Cons.prems(1) play_consistent_attacker_nonpos.simps
      by (smt (verit) \<open>\<not> lnull Ps\<close> llist.distinct(1) llist.inject lnull_def) 
    hence "lhd (lappend Ps (LCons g' LNil)) = the (s (l @ [v]))" by (simp add: \<open>\<not> lnull Ps\<close>) 

    then show ?thesis using play_consistent_attacker_nonpos.intros(6) True \<open>play_consistent_attacker_nonpos s (lappend Ps (LCons g' LNil)) (l @ [v])\<close> \<open>lhd (lappend Ps (LCons g' LNil)) = the (s (l @ [v]))\<close> \<open>\<not> lnull (lappend Ps (LCons g' LNil))\<close>
      by simp
  next
    case False
    then show ?thesis using play_consistent_attacker_nonpos.intros(5) False \<open>\<not> lnull (lappend Ps (LCons g' LNil))\<close> \<open>play_consistent_attacker_nonpos s (lappend Ps (LCons g' LNil)) (l @ [v])\<close>
      by simp
  qed
  then show ?case using v_append_Ps by simp
qed

lemma consistent_nonpos_append_attacker:
  assumes "play_consistent_attacker_nonpos s (LCons v Ps) l"  
          and "llast (LCons v Ps) \<in> attacker" and "lfinite (LCons v Ps)"
  shows "play_consistent_attacker_nonpos s (lappend  (LCons v Ps) (LCons (the (s (l@(list_of (LCons v Ps))))) LNil)) l"
  using assms proof(induction "list_of Ps" arbitrary: v Ps l)
  case Nil
  hence v_append_Ps: "play_consistent_attacker_nonpos s (lappend (LCons v Ps) (LCons (the (s (l@(list_of (LCons v Ps))))) LNil)) l 
        = play_consistent_attacker_nonpos s (LCons v (LCons (the (s (l@[v]))) LNil)) l"
    by (metis lappend_code(1) lappend_code(2) lfinite_code(2) list_of_LCons llist_of.simps(1) llist_of_list_of) 
  have "play_consistent_attacker_nonpos s (LCons v (LCons (the (s (l@[v]))) LNil)) l" using play_consistent_attacker_nonpos.intros Nil
    by (metis hd_Cons_tl lhd_LCons llist.disc(2)) 
  then show ?case using v_append_Ps by simp
next
  case (Cons a x)
  have v_append_Ps: "play_consistent_attacker_nonpos s (lappend (LCons v Ps) (LCons (the (s (l @ list_of (LCons v Ps)))) LNil)) l
                    = play_consistent_attacker_nonpos s (LCons v (lappend Ps (LCons (the (s (l @ [v]@list_of Ps))) LNil))) l"
    using Cons.prems(3) by auto
  have "x = list_of (ltl Ps)" using Cons.hyps(2)
    by (metis Cons.prems(3) lfinite_code(2) list.sel(3) tl_list_of) 
  have "play_consistent_attacker_nonpos s (LCons (lhd Ps) (ltl Ps)) (l@[v])" using Cons.prems(1) play_consistent_attacker_nonpos.simps
    by (smt (verit) Cons.hyps(2) eq_LConsD lhd_LCons list.discI list_of_LNil ltl_simps(2))
  have "llast (LCons (lhd Ps) (ltl Ps)) \<in> attacker" using Cons.prems(2)
    by (metis Cons.hyps(2) lhd_LCons_ltl list.distinct(1) list_of_LNil llast_LCons llist.collapse(1))
  have "lfinite (LCons (lhd Ps) (ltl Ps))" using Cons.prems(3) by simp
  hence "play_consistent_attacker_nonpos s (lappend Ps (LCons (the (s ((l @[v])@list_of Ps))) LNil)) (l@[v])"
    using Cons.hyps \<open>x = list_of (ltl Ps)\<close> \<open>play_consistent_attacker_nonpos s (LCons (lhd Ps) (ltl Ps)) (l@[v])\<close> 
    \<open>llast (LCons (lhd Ps) (ltl Ps)) \<in> attacker\<close>
    by (metis llist.exhaust_sel ltl_simps(1) not_Cons_self2)  
  hence "play_consistent_attacker_nonpos s (LCons v (lappend Ps (LCons (the (s ((l @[v])@(list_of Ps)))) LNil))) l"
    using play_consistent_attacker_nonpos.simps Cons
    by (smt (verit) lhd_LCons lhd_lappend list.discI list_of_LNil llist.distinct(1) lnull_lappend ltl_simps(2)) 
    
  then show ?case using v_append_Ps by simp
qed

text\<open>We now define non-positional attacker winning strategies, i.e. attacker strategies where the defender
 does not win any consistent plays w.r.t some initial energy and a starting position.\<close>

fun nonpos_attacker_winning_strategy:: "('position list \<Rightarrow> 'position option) \<Rightarrow>
  'energy \<Rightarrow> 'position \<Rightarrow> bool" where
  "nonpos_attacker_winning_strategy s e g = (attacker_nonpos_strategy s \<and> 
   (\<forall>p. (play_consistent_attacker_nonpos s (LCons g p) [] 
         \<and> valid_play (LCons g p)) \<longrightarrow> \<not>defender_wins_play e (LCons g p)))"

subsection\<open>Attacker Winning Budgets\<close>

text\<open>We now define attacker winning budgets utilising strategies.\<close>

fun winning_budget:: "'energy \<Rightarrow> 'position \<Rightarrow> bool" where
 "winning_budget e g = (\<exists>s. attacker_winning_strategy s e g)"

fun nonpos_winning_budget:: "'energy \<Rightarrow> 'position \<Rightarrow> bool" where
 "nonpos_winning_budget e g = (\<exists>s. nonpos_attacker_winning_strategy s e g)"

text\<open>Note that \<open>nonpos_winning_budget = winning_budget\<close> holds but is not proven in this theory.
Using this fact we can give an inductive characterisation of attacker winning budgets.
\<close>

inductive winning_budget_ind:: "'energy \<Rightarrow> 'position \<Rightarrow> bool" where
 defender: "winning_budget_ind e g" if 
 "g \<notin> attacker \<and> (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (apply_w g g' e\<noteq> None 
  \<and> winning_budget_ind (the (apply_w g g' e)) g'))" |
 attacker: "winning_budget_ind e g" if 
 "g \<in> attacker \<and> (\<exists>g'. weight g g' \<noteq> None \<and> apply_w g g' e\<noteq> None 
  \<and> winning_budget_ind (the (apply_w g g' e)) g')"

text\<open>Before proving some correspondence of those definitions we first note that attacker winning budgets
in monotonic energy games are upward-closed. We show this for two of the three definitions.\<close>

lemma upward_closure_wb_nonpos:
  assumes monotonic: "\<And>g g' e e'. weight g g' \<noteq> None 
          \<Longrightarrow> apply_w g g' e \<noteq> None \<Longrightarrow> leq e e' \<Longrightarrow> apply_w g g' e' \<noteq> None
          \<and> leq (the (apply_w g g' e)) (the (apply_w g g' e'))"
          and "leq e e'" and "nonpos_winning_budget e g"
  shows "nonpos_winning_budget e' g"
proof-
  from assms have "\<exists>s. nonpos_attacker_winning_strategy s e g" using nonpos_winning_budget.simps by simp
  from this obtain s where S: "nonpos_attacker_winning_strategy s e g" by auto
  have "nonpos_attacker_winning_strategy s e' g" unfolding nonpos_attacker_winning_strategy.simps 
  proof
    show "attacker_nonpos_strategy s" using S by simp
    show "\<forall>p. play_consistent_attacker_nonpos s (LCons g p) [] \<and> valid_play (LCons g p) \<longrightarrow> \<not> defender_wins_play e' (LCons g p)"
    proof
      fix p
      show "play_consistent_attacker_nonpos s (LCons g p) [] \<and> valid_play (LCons g p) \<longrightarrow> \<not> defender_wins_play e' (LCons g p) "
      proof
        assume P: "play_consistent_attacker_nonpos s (LCons g p) [] \<and> valid_play (LCons g p)"
        hence X: "lfinite (LCons g p) \<and> \<not> (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) = None \<or> llast (LCons g p) \<in> attacker \<and> deadend (llast (LCons g p)))" 
          using S unfolding nonpos_attacker_winning_strategy.simps defender_wins_play_def by simp
        have "lfinite (LCons g p) \<and> \<not> (energy_level e' (LCons g p) (the_enat (llength (LCons g p)) - 1) = None \<or> llast (LCons g p) \<in> attacker \<and> deadend (llast (LCons g p)))" 
        proof
          show "lfinite (LCons g p)" using P S unfolding nonpos_attacker_winning_strategy.simps defender_wins_play_def by simp
          have "energy_level e' (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None \<and> \<not>(llast (LCons g p) \<in> attacker \<and> deadend (llast (LCons g p)))"
          proof
            have E: "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P S unfolding nonpos_attacker_winning_strategy.simps defender_wins_play_def by simp
            have "\<And>len. len \<le> the_enat (llength (LCons g p)) - 1 \<longrightarrow> energy_level e' (LCons g p) len \<noteq> None \<and> (leq (the (energy_level e (LCons g p) len)) (the (energy_level e' (LCons g p) len)))" 
            proof
              fix len
              show "len \<le> the_enat (llength (LCons g p)) - 1 \<Longrightarrow> energy_level e' (LCons g p) len \<noteq> None \<and> leq (the (energy_level e (LCons g p) len)) (the (energy_level e' (LCons g p) len))"
              proof(induct len)
                case 0                
                then show ?case using energy_level.simps assms(2)
                  by (simp add: llist.distinct(1) option.discI option.sel)
              next
                case (Suc len)
                hence "energy_level e' (LCons g p) len \<noteq> None" by simp
                have W: "weight (lnth (LCons g p) len)(lnth (LCons g p) (Suc len)) \<noteq> None" using P Suc.prems valid_play.simps valid_play_nth_not_None
                  by (smt (verit) \<open>lfinite (LCons g p)\<close> diff_Suc_1 enat_ord_simps(2) le_less_Suc_eq less_imp_diff_less lfinite_llength_enat linorder_le_less_linear not_less_eq the_enat.simps)
                have A: "apply_w (lnth (LCons g p) len) (lnth (LCons g p) (Suc len)) (the (energy_level e (LCons g p) len)) \<noteq> None" 
                  using E Suc.prems energy_level_nth by blast
                have "llength (LCons g p) > Suc len" using Suc.prems
                  by (metis \<open>lfinite (LCons g p)\<close> diff_Suc_1 enat_ord_simps(2) less_imp_diff_less lfinite_conv_llength_enat nless_le not_le_imp_less not_less_eq the_enat.simps)
                hence "energy_level e' (LCons g p) (Suc len) = apply_w (lnth (LCons g p) len)(lnth (LCons g p) (Suc len)) (the (energy_level e' (LCons g p) len))"
                  using \<open>energy_level e' (LCons g p) len \<noteq> None\<close> energy_level.simps
                  by (meson leD) 
                then show ?case using A W Suc assms
                  by (smt (verit) E Suc_leD energy_level.simps(2) energy_level_nth)
              qed
            qed
            thus "energy_level e' (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" by simp
            show " \<not> (llast (LCons g p) \<in> attacker \<and> deadend (llast (LCons g p)))" using P S unfolding nonpos_attacker_winning_strategy.simps defender_wins_play_def by simp
          qed
          thus "\<not> (energy_level e' (LCons g p) (the_enat (llength (LCons g p)) - 1) = None \<or> llast (LCons g p) \<in> attacker \<and> deadend (llast (LCons g p)))"
            by simp
        qed
        thus "\<not> defender_wins_play e' (LCons g p)" unfolding defender_wins_play_def by simp
      qed
    qed
  qed
  thus ?thesis using nonpos_winning_budget.simps by auto
qed

lemma upward_closure_wb_ind:
  assumes monotonic: "\<And>g g' e e'. weight g g' \<noteq> None 
          \<Longrightarrow> apply_w g g' e \<noteq> None \<Longrightarrow> leq e e' \<Longrightarrow> apply_w g g' e' \<noteq> None
          \<and> leq (the (apply_w g g' e)) (the (apply_w g g' e'))" 
          and "leq e e'" and "winning_budget_ind e g"
  shows "winning_budget_ind e' g"
proof-
  define P where "P \<equiv> \<lambda> e g. (\<forall>e'. leq e e' \<longrightarrow> winning_budget_ind e' g)"
  have "P e g" using assms(3) proof (induct rule: winning_budget_ind.induct)
    case (defender g e)
    then show ?case using P_def
      using monotonic winning_budget_ind.defender by blast
  next
    case (attacker g e)
    then show ?case using P_def
      using monotonic winning_budget_ind.attacker by blast 
  qed

  thus ?thesis using assms(2) P_def  by blast
qed

text\<open>Now we prepare the proof of the inductive characterisation. For this we define an order and a set allowing for a well-founded induction.\<close>

definition strategy_order::  "('energy \<Rightarrow> 'position \<Rightarrow> 'position option) \<Rightarrow> 
  'position \<times> 'energy \<Rightarrow> 'position \<times> 'energy \<Rightarrow> bool" where
  "strategy_order s \<equiv> \<lambda>(g1, e1)(g2, e2).Some e1 = apply_w g2 g1 e2 \<and> 
    (if g2 \<in> attacker then Some g1 = s e2 g2 else weight g2 g1 \<noteq> None)"

definition reachable_positions:: "('energy \<Rightarrow> 'position \<Rightarrow> 'position option) \<Rightarrow> 'position \<Rightarrow> 'energy \<Rightarrow> ('position \<times> 'energy) set" where
  "reachable_positions s g e = {(g',e')| g' e'. 
    (\<exists>p. lfinite p \<and> llast (LCons g p) = g' \<and> valid_play (LCons g p) 
         \<and> play_consistent_attacker s (LCons g p) e 
         \<and> Some e' = energy_level e (LCons g p) (the_enat (llength p)))}"

lemma strategy_order_well_founded:
  assumes "attacker_winning_strategy s e g"
  shows "wfp_on (strategy_order s) (reachable_positions s g e)"
  unfolding Restricted_Predicates.wfp_on_def 
proof
  assume "\<exists>f. \<forall>i. f i \<in> reachable_positions s g e \<and> strategy_order s (f (Suc i)) (f i)"
  from this obtain f where F: "\<forall>i. f i \<in> reachable_positions s g e \<and> strategy_order s (f (Suc i)) (f i)" by auto

  define p where "p = lmap (\<lambda>i. fst (f i))(iterates Suc 0)"
  hence "\<And>i. lnth p i = fst (f i)"
    by simp 

  from p_def have "\<not>lfinite p" by simp

  have "\<And>i. enat (Suc i) < llength p \<Longrightarrow> weight (lnth p i) (lnth p (Suc i)) \<noteq> None"
  proof-
    fix i
    have "\<exists>g1 e1 g2 e2. (f i) = (g2, e2) \<and> f (Suc i) = (g1, e1)" using F reachable_positions_def by simp
    from this obtain g1 e1 g2 e2 where "(f i) = (g2, e2)" and "f (Suc i) = (g1, e1)"
      by blast
    assume "enat (Suc i) < llength p"

    have "weight g2 g1 \<noteq> None"  
    proof(cases "g2 \<in> attacker")
      case True
      then show ?thesis 
      proof(cases "deadend g2")        
        case True
        have "(g2, e2) \<in> reachable_positions s g e" using F by (metis \<open>f i = (g2, e2)\<close>) 
        hence "(\<exists>p'. (lfinite p' \<and> llast (LCons g p') = g2 
                                                    \<and> valid_play (LCons g p') 
                                                    \<and> play_consistent_attacker s (LCons g p') e) 
                                                    \<and> (Some e2 = energy_level e (LCons g p') (the_enat (llength p'))))"
          using reachable_positions_def by simp
        from this obtain p' where P': "(lfinite p' \<and> llast (LCons g p') = g2 
                                                    \<and> valid_play (LCons g p') 
                                                    \<and> play_consistent_attacker s (LCons g p') e) 
                                                    \<and> (Some e2 = energy_level e (LCons g p') (the_enat (llength p')))" by auto
        
        have "\<not>defender_wins_play e (LCons g p')" using assms unfolding attacker_winning_strategy.simps using P' by auto
        have "llast (LCons g p') \<in> attacker \<and> deadend (llast (LCons g p'))" using True \<open>g2 \<in> attacker\<close> P' by simp
        hence "defender_wins_play e (LCons g p')"
          unfolding defender_wins_play_def by simp
        hence "False" using \<open>\<not>defender_wins_play e (LCons g p')\<close> by simp
        then show ?thesis by simp
      next
        case False 
        from True have "Some g1 = s e2 g2" 
          using F unfolding strategy_order_def using  \<open>f (Suc i) = (g1, e1)\<close> \<open>(f i) = (g2, e2)\<close>
          by (metis (mono_tags, lifting) case_prod_conv)
        have "(\<forall>g e. (g \<in> attacker \<and> \<not> deadend g) \<longrightarrow> (s e g \<noteq> None \<and> weight g (the (s e g)) \<noteq> None))"
          using assms unfolding attacker_winning_strategy.simps attacker_strategy_def
          by simp
        hence "weight g2 (the (s e2 g2)) \<noteq> None" using False True
          by simp 
        then show ?thesis using \<open>Some g1 = s e2 g2\<close>
          by (metis option.sel)
      qed
    next
      case False
      then show ?thesis using F unfolding strategy_order_def using \<open>f (Suc i) = (g1, e1)\<close> \<open>(f i) = (g2, e2)\<close>
        by (metis (mono_tags, lifting) case_prod_conv)
    qed
    thus "weight (lnth p i) (lnth p (Suc i)) \<noteq> None" 
      using p_def \<open>f i = (g2, e2)\<close> \<open>f (Suc i) = (g1, e1)\<close> by simp
  qed

  hence "valid_play p" using valid_play_nth
    by simp

  have "(f 0) \<in> reachable_positions s g e" using F by simp
  hence "\<exists>g0 e0. f 0 = (g0,e0)" using reachable_positions_def by simp
  from this obtain g0 e0 where "f 0 = (g0,e0)" by blast
  hence "\<exists>p'. (lfinite p' \<and> llast (LCons g p') = g0 
                                                    \<and> valid_play (LCons g p') 
                                                    \<and> play_consistent_attacker s (LCons g p') e) 
                                                    \<and> (Some e0 = energy_level e (LCons g p') (the_enat (llength p')))"
    using \<open>(f 0) \<in> reachable_positions s g e\<close> unfolding reachable_positions_def by auto
  from this obtain p' where P': "(lfinite p' \<and> llast (LCons g p') = g0 
                                                    \<and> valid_play (LCons g p') 
                                                    \<and> play_consistent_attacker s (LCons g p') e) 
                                                    \<and> (Some e0 = energy_level e (LCons g p') (the_enat (llength p')))" by auto

  have "\<And>i. strategy_order s (f (Suc i)) (f i)" using F by simp
  hence "\<And>i. Some (snd (f (Suc i))) = apply_w (fst (f i)) (fst (f (Suc i))) (snd (f i))" using strategy_order_def
    by (simp add: case_prod_beta)
  hence "\<And>i. (snd (f (Suc i))) = the (apply_w (fst (f i)) (fst (f (Suc i))) (snd (f i)))"
    by (metis option.sel) 

  have "\<And>i. (energy_level e0 p i) = Some (snd (f i))"
  proof-
    fix i
    show "(energy_level e0 p i) = Some (snd (f i))"
    proof(induct i)
      case 0
      then show ?case using \<open>f 0 = (g0,e0)\<close> \<open>\<not> lfinite p\<close> by auto 
    next
      case (Suc i)
      have "Some (snd (f (Suc i))) = (apply_w (fst (f i)) (fst (f (Suc i))) (snd (f i)))" 
        using \<open>\<And>i. Some (snd (f (Suc i))) = apply_w (fst (f i)) (fst (f (Suc i))) (snd (f i))\<close> by simp
      also have "... = (apply_w (fst (f i)) (fst (f (Suc i))) ( the (energy_level e0 p i)))" using Suc by simp
      also have "... = (apply_w (lnth p i) (lnth p (Suc i)) ( the (energy_level e0 p i)))" using \<open>\<And>i. lnth p i = fst (f i)\<close> by simp
      also have "... = (energy_level e0 p (Suc i))" using energy_level.simps \<open>\<not> lfinite p\<close> Suc
        by (simp add: lfinite_conv_llength_enat) 
      finally show ?case
        by simp 
    qed
  qed

  define Q where "Q \<equiv> \<lambda> s p e0. \<not>lfinite p \<and> valid_play p \<and> (\<forall>i. (energy_level e0 p i) \<noteq> None \<and> ((lnth p i), the (energy_level e0 p i)) \<in> reachable_positions s g e 
            \<and> strategy_order s ((lnth p (Suc i)), the (energy_level e0 p (Suc i))) ((lnth p i), the (energy_level e0 p i)))"

  have Q: "\<not>lfinite p \<and> valid_play p \<and> (\<forall>i. (energy_level e0 p i) \<noteq> None \<and> ((lnth p i), the (energy_level e0 p i)) \<in> reachable_positions s g e 
            \<and> strategy_order s ((lnth p (Suc i)), the (energy_level e0 p (Suc i))) ((lnth p i), the (energy_level e0 p i)))"
  proof
    show "\<not> lfinite p " using \<open>\<not>lfinite p\<close> .
    show "valid_play p \<and>
    (\<forall>i. energy_level e0 p i \<noteq> None \<and>
         (lnth p i, the (energy_level e0 p i)) \<in> reachable_positions s g e \<and>
         strategy_order s (lnth p (Suc i), the (energy_level e0 p (Suc i)))
          (lnth p i, the (energy_level e0 p i)))"
    proof
      show "valid_play p" using \<open>valid_play p\<close> .
      show "\<forall>i. energy_level e0 p i \<noteq> None \<and>
        (lnth p i, the (energy_level e0 p i)) \<in> reachable_positions s g e \<and>
        strategy_order s (lnth p (Suc i), the (energy_level e0 p (Suc i)))
         (lnth p i, the (energy_level e0 p i)) "
      proof
        fix i
        show "energy_level e0 p i \<noteq> None \<and>
         (lnth p i, the (energy_level e0 p i)) \<in> reachable_positions s g e \<and>
         strategy_order s (lnth p (Suc i), the (energy_level e0 p (Suc i)))
          (lnth p i, the (energy_level e0 p i))"
        proof
          show "energy_level e0 p i \<noteq> None" using \<open>\<And>i. (energy_level e0 p i) = Some (snd (f i))\<close> by simp
          show "(lnth p i, the (energy_level e0 p i)) \<in> reachable_positions s g e \<and>
    strategy_order s (lnth p (Suc i), the (energy_level e0 p (Suc i)))
     (lnth p i, the (energy_level e0 p i)) "
          proof
            show "(lnth p i, the (energy_level e0 p i)) \<in> reachable_positions s g e"
              using \<open>\<And>i. (energy_level e0 p i) = Some (snd (f i))\<close> F \<open>\<And>i. lnth p i = fst (f i)\<close>
              by simp
            show "strategy_order s (lnth p (Suc i), the (energy_level e0 p (Suc i)))
     (lnth p i, the (energy_level e0 p i))"
              using \<open>\<And>i. strategy_order s (f (Suc i)) (f i)\<close> \<open>\<And>i. lnth p i = fst (f i)\<close> \<open>\<And>i. (energy_level e0 p i) = Some (snd (f i))\<close>
              by (metis option.sel split_pairs)
          qed
        qed
      qed
    qed
  qed

  hence "Q s p e0" using Q_def by simp

  have "\<And>s v Ps e'.
       (\<not> lfinite (LCons v Ps) \<and>
        valid_play (LCons v Ps) \<and>
        (\<forall>i. energy_level e' (LCons v Ps) i \<noteq> None \<and>
             (lnth (LCons v Ps) i, the (energy_level e' (LCons v Ps) i)) \<in> reachable_positions s g e \<and>
             strategy_order s (lnth (LCons v Ps) (Suc i), the (energy_level e' (LCons v Ps) (Suc i)))
              (lnth (LCons v Ps) i, the (energy_level e' (LCons v Ps) i)))) \<and>
       \<not> lnull Ps \<Longrightarrow>
       (\<not> lfinite Ps \<and>
        valid_play Ps \<and>
        (\<forall>i. energy_level (the (apply_w v (lhd Ps) e')) Ps i \<noteq> None \<and>
             (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)) \<in> reachable_positions s g e \<and>
             strategy_order s (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
              (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)))) \<and>
       (v \<in> attacker \<longrightarrow> s e' v = Some (lhd Ps)) \<and> (apply_w v (lhd Ps) e') \<noteq> None"
  proof-
    fix s v Ps e'
    assume A: "(\<not>lfinite (LCons v Ps) \<and> valid_play (LCons v Ps) \<and> (\<forall>i. energy_level e' (LCons v Ps) i \<noteq> None \<and>
            (lnth (LCons v Ps) i, the (energy_level e' (LCons v Ps) i))
            \<in> reachable_positions s g e \<and>
            strategy_order s (lnth (LCons v Ps) (Suc i), the (energy_level e' (LCons v Ps) (Suc i)))
             (lnth (LCons v Ps) i, the (energy_level e' (LCons v Ps) i)))) \<and>
       \<not> lnull Ps"

    show "(\<not>lfinite Ps \<and> valid_play Ps \<and> (\<forall>i. energy_level (the (apply_w v (lhd Ps) e')) Ps i \<noteq> None \<and>
            (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i))
            \<in> reachable_positions s g e \<and>
            strategy_order s
             (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
             (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)))) \<and>
       (v \<in> attacker \<longrightarrow> s e' v = Some (lhd Ps))\<and> (apply_w v (lhd Ps) e') \<noteq> None"
    proof
      show "\<not>lfinite Ps \<and>valid_play Ps \<and> (\<forall>i. energy_level (the (apply_w v (lhd Ps) e')) Ps i \<noteq> None \<and>
        (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i))
        \<in> reachable_positions s g e \<and>
        strategy_order s
         (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
         (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)))" 
      proof
        show "\<not> lfinite Ps" using A by simp
        show "valid_play Ps \<and>
    (\<forall>i. energy_level (the (apply_w v (lhd Ps) e')) Ps i \<noteq> None \<and>
         (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i))
         \<in> reachable_positions s g e \<and>
         strategy_order s
          (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
          (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)))"
        proof
          show "valid_play Ps" using A valid_play.simps
            by (metis llist.distinct(1) llist.inject) 
          show "\<forall>i. energy_level (the (apply_w v (lhd Ps) e')) Ps i \<noteq> None \<and>
        (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i))
        \<in> reachable_positions s g e \<and>
        strategy_order s
         (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
         (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)) "
          proof
            fix i
            show "energy_level (the (apply_w v (lhd Ps) e')) Ps i \<noteq> None \<and>
         (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i))
         \<in> reachable_positions s g e \<and>
         strategy_order s
          (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
          (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i))"
            proof
              from A have "energy_level e' (LCons v Ps) (Suc i) \<noteq> None" by blast
              from A have "valid_play (LCons v Ps) \<and> \<not> lnull Ps" by simp
              have "apply_w v (lhd Ps) e' \<noteq> None" using energy_level.simps
                by (metis A lhd_conv_lnth lnth_0 lnth_Suc_LCons option.sel) 
              from A have "enat i < (llength Ps)"
                by (meson Suc_ile_eq \<open>\<not> lfinite Ps\<close> enat_less_imp_le less_enatE lfinite_conv_llength_enat) 
              have EL: "energy_level (the (apply_w v (lhd Ps) e')) Ps i = energy_level e' (LCons v Ps) (Suc i)"
                using energy_level_cons \<open>valid_play (LCons v Ps) \<and> \<not> lnull Ps\<close> \<open>apply_w v (lhd Ps) e' \<noteq> None\<close>
                by (simp add: \<open>enat i < llength Ps\<close>)
              thus "energy_level (the (apply_w v (lhd Ps) e')) Ps i \<noteq> None"
                using \<open>energy_level e' (LCons v Ps) (Suc i) \<noteq> None\<close> by simp
              show "(lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)) \<in> reachable_positions s g e \<and>
    strategy_order s (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
     (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i))" 
              proof
                have "(lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)) = (lnth (LCons v Ps) (Suc i), the (energy_level e' (LCons v Ps) (Suc i)))" 
                  using EL by simp
                thus "(lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)) \<in> reachable_positions s g e"
                  using A by metis 
                have \<open>enat (Suc i) < llength Ps\<close>
                  using \<open>\<not> lfinite Ps\<close> enat_iless linorder_less_linear llength_eq_enat_lfiniteD by blast 
                hence "(lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
                       = (lnth (LCons v Ps) (Suc (Suc i)), the (energy_level e' (LCons v Ps) (Suc (Suc i))))" 
                  using energy_level_cons \<open>valid_play (LCons v Ps) \<and> \<not> lnull Ps\<close> \<open>apply_w v (lhd Ps) e' \<noteq> None\<close>
                  by (metis lnth_Suc_LCons)
                thus "strategy_order s (lnth Ps (Suc i), the (energy_level (the (apply_w v (lhd Ps) e')) Ps (Suc i)))
     (lnth Ps i, the (energy_level (the (apply_w v (lhd Ps) e')) Ps i)) " using A
                  by (metis EL lnth_Suc_LCons) 
              qed
            qed
          qed
        qed
      qed
      show "(v \<in> attacker \<longrightarrow> s e' v = Some (lhd Ps))\<and> (apply_w v (lhd Ps) e') \<noteq> None"
      proof
        show "v \<in> attacker \<longrightarrow> s e' v = Some (lhd Ps)" 
        proof
          assume "v \<in> attacker"
          from A have "strategy_order s (lnth (LCons v Ps) (Suc 0), the (energy_level e' (LCons v Ps) (Suc 0))) (lnth (LCons v Ps) 0, the (energy_level e' (LCons v Ps) 0))"
            by blast 
          hence "strategy_order s ((lhd Ps), the (energy_level e' (LCons v Ps) (Suc 0))) (v, the (energy_level e' (LCons v Ps) 0))"
            by (simp add: A lnth_0_conv_lhd)
          hence "strategy_order s ((lhd Ps), the (energy_level e' (LCons v Ps) (Suc 0))) (v, e')" using energy_level.simps
            by simp
          hence "(if v \<in> attacker then Some (lhd Ps) = s e' v else weight v (lhd Ps) \<noteq> None)" using strategy_order_def
            using split_beta split_pairs by auto
          thus "s e' v = Some (lhd Ps)" using \<open>v \<in> attacker\<close> by auto
        qed
        from A have "energy_level (the (apply_w v (lhd Ps) e')) Ps 0 \<noteq> None" by auto
        show "apply_w v (lhd Ps) e' \<noteq> None"
          by (metis A energy_level.simps(1) energy_level.simps(2) eq_LConsD lnth_0 lnth_Suc_LCons not_lnull_conv option.sel) 
      qed
    qed
  qed

  hence "(\<And>s v Ps e'.
        Q s (LCons v Ps) e' \<and> \<not> lnull Ps \<Longrightarrow> (apply_w v (lhd Ps) e') \<noteq> None \<and>
        Q s Ps (the (apply_w v (lhd Ps) e')) \<and> (v \<in> attacker \<longrightarrow> s e' v = Some (lhd Ps)))" using Q_def by blast

  hence "play_consistent_attacker s p e0" 
    using \<open>Q s p e0\<close> play_consistent_attacker_coinduct
    by metis

  have "valid_play (lappend (LCons g p') (ltl p)) \<and> play_consistent_attacker s (lappend (LCons g p') (ltl p)) e" 
  proof
    have "weight (llast (LCons g p')) (lhd (ltl p)) \<noteq> None" using P'
      by (metis \<open>\<And>i. lnth p i = fst (f i)\<close> \<open>\<not> lfinite p\<close> \<open>f 0 = (g0, e0)\<close> \<open>valid_play p\<close> fstI lfinite.simps lnth_0 ltl_simps(2) valid_play.cases) 
    show "valid_play (lappend (LCons g p') (ltl p))" using valid_play_append P'
      by (metis (no_types, lifting) \<open>\<not> lfinite p\<close> \<open>valid_play p\<close> \<open>weight (llast (LCons g p')) (lhd (ltl p)) \<noteq> None\<close> lfinite_LConsI lfinite_LNil llist.exhaust_sel ltl_simps(2) valid_play.simps) 

    have "energy_level e (LCons g p') (the_enat (llength p')) \<noteq> None"
      by (metis P' not_Some_eq) 
    hence A: "lfinite p' \<and> llast (LCons g p') = lhd p \<and> play_consistent_attacker s p (the (energy_level e (LCons g p') (the_enat (llength p'))))
             \<and> play_consistent_attacker s (LCons g p') e \<and> valid_play (LCons g p') \<and> energy_level e (LCons g p') (the_enat (llength p')) \<noteq> None"
      using P' \<open>play_consistent_attacker s p e0\<close> p_def  \<open>f 0 = (g0,e0)\<close>
      by (metis \<open>\<And>i. lnth p i = fst (f i)\<close> \<open>\<not> lfinite p\<close> fst_conv lhd_conv_lnth lnull_imp_lfinite option.sel)

    show "play_consistent_attacker s (lappend (LCons g p') (ltl p)) e"
      using A proof(induct "the_enat (llength p')" arbitrary: p' g e)
      case 0
      hence "(lappend (LCons g p') (ltl p)) = p"
        by (metis \<open>\<not> lfinite p\<close> gen_llength_code(1) lappend_code(1) lappend_code(2) lfinite_llength_enat lhd_LCons_ltl llast_singleton llength_LNil llength_code llength_eq_0 llist.collapse(1) the_enat.simps) 
      have "the (energy_level e (LCons g p') (the_enat (llength p'))) = e" using 0 energy_level.simps by auto
      then show ?case using \<open>(lappend (LCons g p') (ltl p)) = p\<close> 0 by simp
    next
      case (Suc x)
      hence "lhd p' = lhd (lappend (p') (ltl p))"
        using the_enat_0 by auto
      have "\<exists>Ps. (lappend (LCons g p') (ltl p)) = LCons g Ps"
        by simp 
      from this obtain Ps where "(lappend (LCons g p') (ltl p)) = LCons g Ps" by auto
      hence "(lappend (p') (ltl p)) = Ps" by simp
      
      have "g \<in> attacker \<longrightarrow> s e g = Some (lhd Ps)"
      proof
        assume "g \<in> attacker"
        show "s e g = Some (lhd Ps)" 
          using Suc
          by (metis Zero_not_Suc \<open>g \<in> attacker\<close> \<open>lappend p' (ltl p) = Ps\<close> \<open>lhd p' = lhd (lappend p' (ltl p))\<close> lhd_LCons llength_LNil llist.distinct(1) ltl_simps(2) play_consistent_attacker.cases the_enat_0) 
      qed
      have "play_consistent_attacker s (lappend (LCons (lhd p') (ltl p')) (ltl p)) (the (apply_w g (lhd p') e))" 
      proof-
        have "x = the_enat (llength (ltl p'))" using Suc
          by (metis One_nat_def diff_Suc_1' epred_enat epred_llength lfinite_conv_llength_enat the_enat.simps)
        have "lfinite  (ltl p') \<and>
    llast (LCons (lhd p') (ltl p')) = lhd p \<and>
    play_consistent_attacker s p
     (the (energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength  (ltl p'))))) \<and>
    play_consistent_attacker s (LCons (lhd p') (ltl p')) (the (apply_w g (lhd p') e)) 
      \<and> valid_play (LCons (lhd p') (ltl p')) \<and> energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength (ltl p'))) \<noteq> None"
        proof
          show "lfinite  (ltl p')" using Suc lfinite_ltl by simp 
          show "llast (LCons (lhd p') (ltl p')) = lhd p \<and>
    play_consistent_attacker s p
     (the (energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p'))
            (the_enat (llength (ltl p'))))) \<and>
    play_consistent_attacker s (LCons (lhd p') (ltl p')) (the (apply_w g (lhd p') e)) \<and> 
    valid_play (LCons (lhd p') (ltl p')) \<and> energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength (ltl p'))) \<noteq> None"
          proof
            show "llast (LCons (lhd p') (ltl p')) = lhd p" using Suc
              by (metis (no_types, lifting) \<open>x = the_enat (llength (ltl p'))\<close> llast_LCons2 llist.exhaust_sel ltl_simps(1) n_not_Suc_n) 
            show "play_consistent_attacker s p
     (the (energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p'))
            (the_enat (llength (ltl p'))))) \<and>
    play_consistent_attacker s (LCons (lhd p') (ltl p')) (the (apply_w g (lhd p') e)) \<and> 
    valid_play (LCons (lhd p') (ltl p')) \<and> energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength (ltl p'))) \<noteq> None"
            proof
              have "energy_level e (LCons g p') (the_enat (llength p')) \<noteq> None" using Suc
                by blast 
              hence "apply_w g (lhd p') e \<noteq> None"
                by (smt (verit) Suc.hyps(2) Suc_leI \<open>x = the_enat (llength (ltl p'))\<close> energy_level.simps(1) energy_level_nth llist.distinct(1) llist.exhaust_sel lnth_0 lnth_Suc_LCons ltl_simps(1) n_not_Suc_n option.sel zero_less_Suc)
              hence cons_assms: "valid_play (LCons g p') \<and> \<not> lnull p' \<and> apply_w g (lhd p') e \<noteq> None \<and> enat (the_enat (llength (ltl p'))) < llength p'"
                using Suc
                by (metis \<open>x = the_enat (llength (ltl p'))\<close> enat_ord_simps(2) lessI lfinite_conv_llength_enat lnull_def ltl_simps(1) n_not_Suc_n the_enat.simps) 

              have "(the (energy_level e (LCons g p') (the_enat (llength p')))) = 
                    (the (energy_level e (LCons g p') (Suc (the_enat (llength (ltl p'))))))"
                using Suc.hyps(2) \<open>x = the_enat (llength (ltl p'))\<close> by auto
              also have "... = (the (energy_level (the (apply_w g (lhd p') e)) p' (the_enat (llength (ltl p')))))"
                using energy_level_cons cons_assms by simp
              finally have EL: "(the (energy_level e (LCons g p') (the_enat (llength p')))) = 
                    (the (energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength (ltl p')))))"
                by (simp add: cons_assms)
              thus "play_consistent_attacker s p
     (the (energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p'))
            (the_enat (llength (ltl p')))))"
                using Suc by argo 
              show "play_consistent_attacker s (LCons (lhd p') (ltl p')) (the (apply_w g (lhd p') e))\<and> 
                  valid_play (LCons (lhd p') (ltl p')) \<and> energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength (ltl p'))) \<noteq> None"
              proof
                show " play_consistent_attacker s (LCons (lhd p') (ltl p')) (the (apply_w g (lhd p') e))"
                  using Suc
                  by (metis cons_assms lhd_LCons lhd_LCons_ltl llist.distinct(1) ltl_simps(2) play_consistent_attacker.simps) 
                show "valid_play (LCons (lhd p') (ltl p')) \<and> energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength (ltl p'))) \<noteq> None"
                proof 
                  show "valid_play (LCons (lhd p') (ltl p'))" using Suc
                    by (metis llist.distinct(1) llist.exhaust_sel llist.inject ltl_simps(1) valid_play.simps) 
                  show "energy_level (the (apply_w g (lhd p') e)) (LCons (lhd p') (ltl p')) (the_enat (llength (ltl p'))) \<noteq> None" 
                    using EL Suc
                    by (metis \<open>x = the_enat (llength (ltl p'))\<close> cons_assms energy_level_cons lhd_LCons_ltl) 
                qed
              qed
            qed
          qed
        qed
        thus ?thesis using \<open>x = the_enat (llength (ltl p'))\<close> Suc
          by blast 
      qed
      hence "play_consistent_attacker s Ps (the (apply_w g (lhd p') e))" 
        using \<open>(lappend (p') (ltl p)) = Ps\<close>
        by (metis Suc.hyps(2) diff_0_eq_0 diff_Suc_1 lhd_LCons_ltl llength_lnull n_not_Suc_n the_enat_0)
      then show ?case using play_consistent_attacker.simps \<open>g \<in> attacker \<longrightarrow> s e g = Some (lhd Ps)\<close> \<open>(lappend (LCons g p') (ltl p)) = LCons g Ps\<close>
        by (metis (no_types, lifting) Suc.prems \<open>\<not> lfinite p\<close> \<open>lappend p' (ltl p) = Ps\<close> \<open>lhd p' = lhd (lappend p' (ltl p))\<close> energy_level.simps(1) lappend_code(1) lhd_LCons llast_singleton llength_LNil llist.distinct(1) lnull_lappend ltl_simps(2) option.sel the_enat_0)
    qed
  qed

  hence "\<not>defender_wins_play e (lappend (LCons g p') (ltl p))" using assms unfolding attacker_winning_strategy.simps using P'
    by simp

  have "\<not>lfinite (lappend p' p)" using p_def by simp
  hence "defender_wins_play e (lappend (LCons g p') (ltl p))" using defender_wins_play_def by auto
  thus "False" using \<open>\<not>defender_wins_play e (lappend (LCons g p') (ltl p))\<close> by simp 
qed

text\<open>We now show that an energy-positional attacker winning strategy w.r.t.\ some energy $e$ and position $g$ 
guarantees that $e$ is in the attacker winning budget of $g$.\<close>

lemma winning_budget_implies_ind:
  assumes "winning_budget e g"
  shows "winning_budget_ind e g"
proof-
  define wb where "wb \<equiv> \<lambda>(g,e). winning_budget_ind e g"

  from assms have "\<exists>s. attacker_winning_strategy s e g" using winning_budget.simps by auto
  from this obtain s where S: "attacker_winning_strategy s e g" by auto
  hence "wfp_on (strategy_order s) (reachable_positions s g e)" 
    using strategy_order_well_founded by simp
  hence "inductive_on (strategy_order s) (reachable_positions s g e)"
    by (simp add: wfp_on_iff_inductive_on)

  hence "wb (g,e)" 
  proof(rule inductive_on_induct)
    show "(g,e) \<in> reachable_positions s g e"
      unfolding reachable_positions_def proof
      have "lfinite LNil \<and>
             llast (LCons g LNil) = g \<and>
             valid_play (LCons g LNil) \<and> play_consistent_attacker s (LCons g LNil) e \<and>
            Some e = energy_level e (LCons g LNil) (the_enat (llength LNil))"
        using valid_play.simps play_consistent_attacker.simps energy_level.simps
        by (metis lfinite_code(1) llast_singleton llength_LNil neq_LNil_conv the_enat_0) 
      thus "\<exists>g' e'.
       (g, e) = (g', e') \<and>
       (\<exists>p. lfinite p \<and>
             llast (LCons g p) = g' \<and>
             valid_play (LCons g p) \<and> play_consistent_attacker s (LCons g p) e \<and>
            Some e' = energy_level e (LCons g p) (the_enat (llength p)))"
        by (metis lfinite_code(1) llast_singleton llength_LNil the_enat_0)
    qed

    show "\<And>y. y \<in> reachable_positions s g e \<Longrightarrow>
         (\<And>x. x \<in> reachable_positions s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x) \<Longrightarrow> wb y"
    proof-
      fix y 
      assume "y \<in> reachable_positions s g e"
      hence "\<exists>e' g'. y = (g', e')" using reachable_positions_def by auto
      from this obtain e' g' where "y = (g', e')" by auto

      hence "(\<exists>p. lfinite p \<and> llast (LCons g p) = g' 
                                                    \<and> valid_play (LCons g p) 
                                                    \<and> play_consistent_attacker s (LCons g p) e
                                                    \<and> (Some e' = energy_level e (LCons g p) (the_enat (llength p))))"
        using \<open>y \<in> reachable_positions s g e\<close> unfolding reachable_positions_def
        by auto 
      from this obtain p where P: "(lfinite p \<and> llast (LCons g p) = g' 
                                                    \<and> valid_play (LCons g p) 
                                                    \<and> play_consistent_attacker s (LCons g p) e) 
                                                    \<and> (Some e' = energy_level e (LCons g p) (the_enat (llength p)))" by auto
       
      show "(\<And>x. x \<in> reachable_positions s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x) \<Longrightarrow> wb y"
      proof-
        assume ind: "(\<And>x. x \<in> reachable_positions s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x)"
        have "winning_budget_ind e' g'" 
        proof(cases "g' \<in> attacker")
          case True 
          then show ?thesis 
          proof(cases "deadend g'")
            case True (* wiederspruchsbeweis *)
            hence "attacker_stuck (LCons g p)" using \<open>g' \<in> attacker\<close> P
              by (meson S defender_wins_play_def attacker_winning_strategy.elims(2)) 
            hence "defender_wins_play e (LCons g p)" using defender_wins_play_def by simp
            have "\<not>defender_wins_play e (LCons g p)" using P S by simp
            then show ?thesis using \<open>defender_wins_play e (LCons g p)\<close> by simp
          next
            case False (* nehme s e' g' und wende ind.hyps. darauf an *)
            hence "(s e' g') \<noteq> None \<and> (weight g' (the (s e' g')))\<noteq>None" using S attacker_winning_strategy.simps
              by (simp add: True attacker_strategy_def)

            define x where "x = (the (s e' g'), the (apply_w g' (the (s e' g')) e'))"
            define p' where "p' =  (lappend p (LCons (the (s e' g')) LNil))"
            hence "lfinite p'" using P by simp
            have "llast (LCons g p') = the (s e' g')" using p'_def \<open>lfinite p'\<close>
              by (simp add: llast_LCons)

            have "the_enat (llength p') > 0" using P
              by (metis LNil_eq_lappend_iff \<open>lfinite p'\<close> bot_nat_0.not_eq_extremum enat_0_iff(2) lfinite_conv_llength_enat llength_eq_0 llist.collapse(1) llist.distinct(1) p'_def the_enat.simps) 
            hence "\<exists>i. Suc i = the_enat (llength p')"
              using less_iff_Suc_add by auto 
            from this obtain i where "Suc i = the_enat (llength p')" by auto
            hence "i = the_enat (llength p)" using p'_def P                     
              by (metis Suc_leI \<open>lfinite p'\<close> length_append_singleton length_list_of_conv_the_enat less_Suc_eq_le less_irrefl_nat lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend not_less_less_Suc_eq)
            hence "Some e' = (energy_level e (LCons g p) i)" using P by simp

            have A: "lfinite (LCons g p) \<and> i < the_enat (llength (LCons g p)) \<and> energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
            proof
              show "lfinite (LCons g p)" using P by simp
              show "i < the_enat (llength (LCons g p)) \<and> energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
              proof
                show "i < the_enat (llength (LCons g p))" using \<open>i = the_enat (llength p)\<close> P
                  by (metis \<open>lfinite (LCons g p)\<close> length_Cons length_list_of_conv_the_enat lessI list_of_LCons) 
                show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P \<open>i = the_enat (llength p)\<close>
                  using S defender_wins_play_def by auto
              qed
            qed

            hence "Some e' = (energy_level e (LCons g p') i)" using p'_def energy_level_append P \<open>Some e' = (energy_level e (LCons g p) i)\<close>
              by (metis lappend_code(2))
            hence "energy_level e (LCons g p') i \<noteq> None"
              by (metis option.distinct(1))

            have "enat (Suc i) = llength p'" using \<open>Suc i = the_enat (llength p')\<close>
              by (metis \<open>lfinite p'\<close> lfinite_conv_llength_enat the_enat.simps)
            also have "... < eSuc (llength p')"
              by (metis calculation iless_Suc_eq order_refl) 
            also have "... = llength (LCons g p')" using \<open>lfinite p'\<close> by simp
            finally have "enat (Suc i) < llength (LCons g p')".

            have "(lnth (LCons g p) i) = g'" using \<open>i = the_enat (llength p)\<close> P
              by (metis lfinite_conv_llength_enat llast_conv_lnth llength_LCons the_enat.simps) 
            hence "(lnth (LCons g p') i) = g'" using p'_def
              by (metis P \<open>i = the_enat (llength p)\<close> enat_ord_simps(2) energy_level.elims lessI lfinite_llength_enat lnth_0 lnth_Suc_LCons lnth_lappend1 the_enat.simps) 

            have "energy_level e (LCons g p') (the_enat (llength p')) = energy_level e (LCons g p') (Suc i)" 
              using \<open>Suc i = the_enat (llength p')\<close> by simp
            also have "... = apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) (the (energy_level e (LCons g p') i))" 
              using energy_level.simps \<open>enat (Suc i) < llength (LCons g p')\<close> \<open>energy_level e (LCons g p') i \<noteq> None\<close>
              by (meson leD)
            also have "... =  apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) e'" using \<open>Some e' = (energy_level e (LCons g p') i)\<close>
              by (metis option.sel) 
            also have "... =  apply_w (lnth (LCons g p') i) (the (s e' g')) e'" using p'_def \<open>enat (Suc i) = llength p'\<close>
              by (metis \<open>eSuc (llength p') = llength (LCons g p')\<close> \<open>llast (LCons g p') = the (s e' g')\<close> llast_conv_lnth) 
            also have  "... =  apply_w g' (the (s e' g')) e'" using \<open>(lnth (LCons g p') i) = g'\<close> by simp
            finally have "energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'" .
            
            have P': "lfinite p'\<and>
             llast (LCons g p') = (the (s e' g')) \<and>
             valid_play (LCons g p') \<and> play_consistent_attacker s (LCons g p') e \<and>
            Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
            proof
              show "lfinite p'" using p'_def P by simp
              show "llast (LCons g p') = the (s e' g') \<and>
    valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
              proof
                show "llast (LCons g p') = the (s e' g')" using p'_def \<open>lfinite p'\<close>
                  by (simp add: llast_LCons) 
                show "valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                proof
                  show "valid_play (LCons g p')" using p'_def P
                    using \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> valid_play.intros(2) valid_play_append by auto
                  show "play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                  proof
                    have "(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)" using p'_def
                      by simp
                    have "play_consistent_attacker s (lappend (LCons g p) (LCons (the (s e' g')) LNil)) e"
                    proof (rule play_consistent_attacker_append_one)
                      show "play_consistent_attacker s (LCons g p) e"
                        using P by auto
                      show "lfinite (LCons g p)" using P by auto
                      show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P
                        using A by auto 
                      show "valid_play (lappend (LCons g p) (LCons (the (s e' g')) LNil))" 
                        using \<open>valid_play (LCons g p')\<close> \<open>(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)\<close> by simp
                      show "llast (LCons g p) \<in> attacker \<longrightarrow>
    Some (the (s e' g')) =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                      proof
                        assume "llast (LCons g p) \<in> attacker"
                        show "Some (the (s e' g')) =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                          using \<open>llast (LCons g p) \<in> attacker\<close> P
                          by (metis One_nat_def \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> diff_Suc_1' eSuc_enat lfinite_llength_enat llength_LCons option.collapse option.sel the_enat.simps) 
                      qed
                    qed
                    thus "play_consistent_attacker s (LCons g p') e" using \<open>(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)\<close> by simp
                    
                    show "Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                      by (metis \<open>eSuc (llength p') = llength (LCons g p')\<close> \<open>enat (Suc i) = llength p'\<close> \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> \<open>play_consistent_attacker s (LCons g p') e\<close> \<open>valid_play (LCons g p')\<close> S defender_wins_play_def diff_Suc_1 eSuc_enat option.collapse attacker_winning_strategy.elims(2) the_enat.simps)
                  qed
                qed
              qed
            qed
            hence "x \<in> reachable_positions s g e" using reachable_positions_def x_def by auto

            have "(apply_w g' (the (s e' g')) e') \<noteq> None" using P'
              by (metis \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> option.distinct(1)) 
    
            have "Some (the (apply_w g' (the (s e' g')) e')) = apply_w g' (the (s e' g')) e' \<and> (if g' \<in> attacker then Some (the (s e' g')) = s e' g' else weight g' (the (s e' g')) \<noteq> None)"
              using \<open>(s e' g') \<noteq> None \<and> (weight g' (the (s e' g')))\<noteq>None\<close> \<open>(apply_w g' (the (s e' g')) e') \<noteq> None\<close> by simp
            hence "strategy_order s x y" unfolding strategy_order_def using x_def \<open>y = (g', e')\<close>
              by blast
            hence "wb x" using ind \<open>x \<in> reachable_positions s g e\<close> by simp
            hence "winning_budget_ind (the (apply_w g' (the (s e' g')) e')) (the (s e' g'))" using wb_def x_def by simp
            then show ?thesis using \<open>g' \<in> attacker\<close> winning_budget_ind.simps
              by (metis (mono_tags, lifting) \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> \<open>strategy_order s x y\<close> \<open>y = (g', e')\<close> old.prod.case option.distinct(1) strategy_order_def x_def) 
          qed
        next
          case False
          hence "g' \<notin> attacker \<and>
            (\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and> winning_budget_ind (the (apply_w g' g'' e')) g'')"
          proof
            show "\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and> winning_budget_ind (the (apply_w g' g'' e')) g''"
            proof
              fix g''
              show "weight g' g'' \<noteq> None \<longrightarrow>
           apply_w g' g'' e' \<noteq> None \<and> winning_budget_ind (the (apply_w g' g'' e')) g'' "
              proof
                assume "weight g' g'' \<noteq> None"
                show "apply_w g' g'' e' \<noteq> None \<and> winning_budget_ind (the (apply_w g' g'' e')) g''"
                proof
                  show "apply_w g' g'' e' \<noteq> None"
                  proof
                    assume "apply_w g' g'' e' = None"
                    define p' where "p' \<equiv> (LCons g (lappend p (LCons g'' LNil)))"
                    hence "lfinite p'" using P by simp
                    have "\<exists>i. llength p = enat i" using P
                      by (simp add: lfinite_llength_enat) 
                    from this obtain i where "llength p = enat i" by auto
                    hence "llength (lappend p (LCons g'' LNil)) = enat (Suc i)"
                      by (simp add: \<open>llength p = enat i\<close> eSuc_enat iadd_Suc_right)
                    hence "llength p' = eSuc (enat(Suc i))" using p'_def
                      by simp 
                    hence "the_enat (llength p') = Suc (Suc i)"
                      by (simp add: eSuc_enat)
                    hence "the_enat (llength p') - 1 = Suc i"
                      by simp 
                    hence "the_enat (llength p') - 1 = the_enat (llength (lappend p (LCons g'' LNil)))"
                      using \<open>llength (lappend p (LCons g'' LNil)) = enat (Suc i)\<close>
                      by simp

                    have "(lnth p' i) = g'" using p'_def \<open>llength p = enat i\<close> P
                      by (smt (verit) One_nat_def diff_Suc_1' enat_ord_simps(2) energy_level.elims lessI llast_conv_lnth llength_LCons lnth_0 lnth_LCons' lnth_lappend the_enat.simps)
                    have "(lnth p' (Suc i)) = g''" using p'_def \<open>llength p = enat i\<close>
                      by (metis \<open>llength p' = eSuc (enat (Suc i))\<close> lappend.disc(2) llast_LCons llast_conv_lnth llast_lappend_LCons llength_eq_enat_lfiniteD llist.disc(1) llist.disc(2))
                    have "p' = lappend (LCons g p) (LCons g'' LNil)" using p'_def by simp
                    hence "the (energy_level e p' i) = the (energy_level e (lappend (LCons g p) (LCons g'' LNil)) i)" by simp
                    also have "... = the (energy_level e (LCons g p) i)" using \<open>llength p = enat i\<close> energy_level_append P
                      by (metis diff_Suc_1 eSuc_enat lessI lfinite_LConsI llength_LCons option.distinct(1) the_enat.simps) 
                    also have "... = e'" using P
                      by (metis \<open>llength p = enat i\<close> option.sel the_enat.simps) 
                    finally have "the (energy_level e p' i) = e'" . 
                    hence "apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)) = None" using \<open>apply_w g' g'' e'=None\<close> \<open>(lnth p' i) = g'\<close> \<open>(lnth p' (Suc i)) = g''\<close> by simp

                    have "energy_level e p' (the_enat (llength p') - 1) = 
                          energy_level e p' (the_enat (llength (lappend p (LCons g'' LNil))))" 
                      using \<open>the_enat (llength p') - 1 = the_enat (llength (lappend p (LCons g'' LNil)))\<close>
                      by simp 
                    also have "... = energy_level e p' (Suc i)" using \<open>llength (lappend p (LCons g'' LNil)) = enat (Suc i)\<close> by simp
                    also have "... = (if energy_level e p' i = None \<or> llength p' \<le> enat (Suc i) then None
                                      else apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)))" using energy_level.simps by simp
                    also have "... = None " using \<open>apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)) = None\<close>
                      by simp
                    finally have "energy_level e p' (the_enat (llength p') - 1) = None" .
                    hence "defender_wins_play e p'" unfolding defender_wins_play_def by simp

                    have "valid_play p'"
                      by (metis P \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> \<open>weight g' g'' \<noteq> None\<close> energy_game.valid_play.intros(2) energy_game.valid_play_append lfinite_LConsI)


                    have "play_consistent_attacker s (lappend (LCons g p) (LCons g'' LNil)) e"
                    proof(rule play_consistent_attacker_append_one)
                      show "play_consistent_attacker s (LCons g p) e" 
                        using P by simp
                      show "lfinite (LCons g p)" using P by simp
                      show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                         using P
                         by (meson S defender_wins_play_def attacker_winning_strategy.elims(2))
                      show "valid_play (lappend (LCons g p) (LCons g'' LNil))"
                        using \<open>valid_play p'\<close> \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> by simp
                      show "llast (LCons g p) \<in> attacker \<longrightarrow>
    Some g'' =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                        using False P by simp
                    qed
                    hence "play_consistent_attacker s p' e"
                      using \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> by simp
                    hence "\<not>defender_wins_play e p'" using \<open>valid_play p'\<close> p'_def S by simp
                    thus "False" using \<open>defender_wins_play e p'\<close> by simp
                      (* widerspruch weil in reachable und sonst defender_wins_play *)
                  qed

                  define x where "x = (g'', the (apply_w g' g'' e'))"
                  have "wb x" 
                  proof(rule ind)
                    have "(\<exists>p. lfinite p \<and>
             llast (LCons g p) = g'' \<and>
             valid_play (LCons g p) \<and> play_consistent_attacker s (LCons g p) e \<and>
            Some (the (apply_w g' g'' e')) = energy_level e (LCons g p) (the_enat (llength p)))"
                    proof
                      define p' where "p' = lappend p (LCons g'' LNil)"
                      show "lfinite p' \<and>
     llast (LCons g p') = g'' \<and>
     valid_play (LCons g p') \<and> play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                      proof
                        show "lfinite p'" using P p'_def by simp
                        show "llast (LCons g p') = g'' \<and>
    valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                        proof
                          show "llast (LCons g p') = g''" using p'_def
                            by (metis \<open>lfinite p'\<close> lappend.disc_iff(2) lfinite_lappend llast_LCons llast_lappend_LCons llast_singleton llist.discI(2))
                          show "valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                          proof
                            show "valid_play (LCons g p')" using p'_def P
                              using \<open>weight g' g'' \<noteq> None\<close> lfinite_LCons valid_play.intros(2) valid_play_append by auto
                            show "play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p')) "
                            proof

                              have "play_consistent_attacker s (lappend (LCons g p) (LCons g'' LNil)) e"
                              proof(rule play_consistent_attacker_append_one)
                                show "play_consistent_attacker s (LCons g p) e" 
                                  using P by simp
                                show "lfinite (LCons g p)" using P by simp
                                show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                                  using P
                                  by (meson S defender_wins_play_def attacker_winning_strategy.elims(2))
                                show "valid_play (lappend (LCons g p) (LCons g'' LNil))"
                                  using \<open>valid_play (LCons g p')\<close> p'_def by simp
                                show "llast (LCons g p) \<in> attacker \<longrightarrow>
                                      Some g'' =
                                        s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                                  using False P by simp
                              qed
                              thus "play_consistent_attacker s (LCons g p') e" using p'_def
                                by (simp add: lappend_code(2)) 

                              have "\<exists>i. Suc i = the_enat (llength p')" using p'_def \<open>lfinite p'\<close>
                                by (metis P length_append_singleton length_list_of_conv_the_enat lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend)
                              from this obtain i where "Suc i = the_enat (llength p')" by auto
                              hence "i = the_enat (llength p)" using p'_def
                                by (smt (verit) One_nat_def \<open>lfinite p'\<close> add.commute add_Suc_shift add_right_cancel length_append length_list_of_conv_the_enat lfinite_LNil lfinite_lappend list.size(3) list.size(4) list_of_LCons list_of_LNil list_of_lappend plus_1_eq_Suc)  
                              hence "Suc i = llength (LCons g p)"
                                using P eSuc_enat lfinite_llength_enat by fastforce
                              have "(LCons g p') = lappend (LCons g p) (LCons g'' LNil)" using p'_def by simp
                              have A: "lfinite (LCons g p) \<and> i < the_enat (llength (LCons g p)) \<and>  energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                              proof
                                show "lfinite (LCons g p)" using P by simp
                                show " i < the_enat (llength (LCons g p)) \<and>
    energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None "
                                proof
                                  have "(llength p') = llength (LCons g p)" using p'_def
                                    by (metis P \<open>lfinite p'\<close> length_Cons length_append_singleton length_list_of lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend) 
                                  thus "i < the_enat (llength (LCons g p))" using \<open>Suc i = the_enat (llength p')\<close>
                                    using lessI by force 
                                  show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P
                                    by (meson S energy_game.defender_wins_play_def energy_game.play_consistent_attacker.intros(2) attacker_winning_strategy.simps)
                                qed
                              qed
                              hence "energy_level e (LCons g p') i \<noteq> None"
                                using energy_level_append
                                by (smt (verit) Nat.lessE Suc_leI \<open>LCons g p' = lappend (LCons g p) (LCons g'' LNil)\<close> diff_Suc_1 energy_level_nth)  
                              have "enat (Suc i) < llength (LCons g p')" 
                                using \<open>Suc i = the_enat (llength p')\<close>
                                by (metis Suc_ile_eq \<open>lfinite p'\<close> ldropn_Suc_LCons leI lfinite_conv_llength_enat lnull_ldropn nless_le the_enat.simps) 
                              hence  el_prems: "energy_level e (LCons g p') i \<noteq> None \<and> llength (LCons g p') > enat (Suc i)" using \<open>energy_level e (LCons g p') i \<noteq> None\<close> by simp

                              have "(lnth (LCons g p') i) = lnth (LCons g p) i" 
                                unfolding \<open>(LCons g p') = lappend (LCons g p) (LCons g'' LNil)\<close> using \<open>i = the_enat (llength p)\<close> lnth_lappend1
                                by (metis A enat_ord_simps(2) length_list_of length_list_of_conv_the_enat)
                              have "lnth (LCons g p) i = llast (LCons g p)" using \<open>Suc i = llength (LCons g p)\<close>
                                by (metis enat_ord_simps(2) lappend_LNil2 ldropn_LNil ldropn_Suc_conv_ldropn ldropn_lappend lessI less_not_refl llast_ldropn llast_singleton)
                              hence "(lnth (LCons g p') i) = g'" using P
                                by (simp add: \<open>lnth (LCons g p') i = lnth (LCons g p) i\<close>) 
                              have "(lnth (LCons g p') (Suc i)) = g''"
                                using p'_def \<open>Suc i = the_enat (llength p')\<close>
                                by (smt (verit) \<open>enat (Suc i) < llength (LCons g p')\<close> \<open>lfinite p'\<close> \<open>llast (LCons g p') = g''\<close> lappend_snocL1_conv_LCons2 ldropn_LNil ldropn_Suc_LCons ldropn_Suc_conv_ldropn ldropn_lappend2 lfinite_llength_enat llast_ldropn llast_singleton the_enat.simps wlog_linorder_le)

                              have "energy_level e (LCons g p) i = energy_level e (LCons g p') i" 
                                using energy_level_append A \<open>(LCons g p') = lappend (LCons g p) (LCons g'' LNil)\<close>
                                by presburger
                              hence "Some e' = (energy_level e (LCons g p') i)" 
                                using P \<open>i = the_enat (llength p)\<close>
                                by argo 

                              have "energy_level e (LCons g p') (the_enat (llength p')) = energy_level e (LCons g p') (Suc i)" using \<open>Suc i = the_enat (llength p')\<close> by simp
                              also have "... = apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) (the (energy_level e (LCons g p') i))" 
                                using energy_level.simps el_prems
                                by (meson leD) 
                              also have "... = apply_w g' g'' (the (energy_level e (LCons g p') i))" 
                                using \<open>(lnth (LCons g p') i) = g'\<close> \<open>(lnth (LCons g p') (Suc i)) = g''\<close> by simp
                              finally have "energy_level e (LCons g p') (the_enat (llength p')) = (apply_w g' g'' e')" 
                                using \<open>Some e' = (energy_level e (LCons g p') i)\<close>
                                by (metis option.sel) 
                              thus "Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                                by (simp add: \<open>apply_w g' g'' e' \<noteq> None\<close>)
                            qed
                          qed
                        qed
                      qed
                    qed

                    thus "x \<in> reachable_positions s g e"
                      using x_def reachable_positions_def
                      by (simp add: mem_Collect_eq) 

                    have "Some (the (apply_w g' g'' e')) = apply_w g' g'' e' \<and>
         (if g' \<in> attacker then Some g'' = s e' g' else weight g' g'' \<noteq> None)"
                    proof
                      show "Some (the (apply_w g' g'' e')) = apply_w g' g'' e'"
                        by (simp add: \<open>apply_w g' g'' e' \<noteq> None\<close>) 
                      show "(if g' \<in> attacker then Some g'' = s e' g' else weight g' g'' \<noteq> None)"
                        using False
                        by (simp add: \<open>weight g' g'' \<noteq> None\<close>) 
                    qed
                    thus "strategy_order s x y" using strategy_order_def x_def \<open>y = (g', e')\<close>
                      by simp
                  qed

                  thus "winning_budget_ind (the (apply_w g' g'' e')) g'' " using x_def wb_def
                    by force 
                qed
              qed
            qed
          qed
          thus ?thesis using winning_budget_ind.intros by blast
        qed
        thus "wb y" using \<open>y = (g', e')\<close> wb_def by simp
      qed
    qed
  qed
  thus ?thesis using wb_def by simp
qed

text \<open>We now prepare the proof of \<open>winning_budget_ind\<close> characterising subsets of \<open>winning_budget_nonpos\<close> for all positions.
For this we introduce a construction to obtain a non-positional attacker winning strategy from a strategy at a next position.\<close>

fun nonpos_strat_from_next:: "'position \<Rightarrow> 'position \<Rightarrow> 
  ('position list \<Rightarrow> 'position option) \<Rightarrow> ('position list \<Rightarrow> 'position option)" 
where
  "nonpos_strat_from_next g g' s [] = s []" |
  "nonpos_strat_from_next g g' s (x#xs) = (if x=g then (if xs=[] then Some g' 
                                           else s xs) else s (x#xs))"

lemma play_nonpos_consistent_next:
  assumes "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons g (LCons g' xs)) []" 
      and "g \<in> attacker" and "xs \<noteq> LNil"
  shows "play_consistent_attacker_nonpos s (LCons g' xs) []"
proof-
  have X: "\<And>l. l\<noteq>[] \<Longrightarrow>(((nonpos_strat_from_next g g' s) ([g] @ l)) = s l)" using nonpos_strat_from_next.simps by simp
  have A1: "\<And>s v l. play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons v LNil) ([g]@l) \<Longrightarrow> (l = [] \<or> (last l) \<notin> attacker \<or> ((last l)\<in>attacker \<and> the (s l) = v))" 
  proof-
    fix s v l
    assume "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons v LNil) ([g] @ l)"
    show "l = [] \<or> last l \<notin> attacker \<or> last l \<in> attacker \<and> the (s l) = v " 
    proof(cases "l=[]")
      case True
      then show ?thesis by simp
    next
      case False
      hence "l \<noteq> []" .
      then show ?thesis proof(cases "last l \<notin> attacker")
        case True
        then show ?thesis by simp
      next
        case False
        hence "the ((nonpos_strat_from_next g g' s) ([g] @ l)) = v"
          by (smt (verit) \<open>play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons v LNil) ([g] @ l)\<close> append_is_Nil_conv assms(2) eq_LConsD last.simps last_append lhd_LCons list.distinct(1) llist.disc(1) play_consistent_attacker_nonpos.simps) 
        hence "the (s l) = v" using X \<open>l \<noteq> []\<close> by auto
        then show ?thesis using False by simp
      qed
    qed
  qed

  have A2: "\<And>s v Ps l. play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons v Ps) ([g]@l) \<and> Ps\<noteq>LNil \<Longrightarrow> play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) Ps ([g]@(l@[v])) \<and> (v\<in>attacker \<longrightarrow> lhd Ps = the (s (l@[v])))" 
  proof-
    fix s v Ps l
    assume play_cons: "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons v Ps) ([g]@l) \<and> Ps\<noteq>LNil"
    show "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) Ps ([g]@(l@[v])) \<and> (v\<in>attacker \<longrightarrow> lhd Ps = the (s (l@[v])))" 
    proof
      show "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) Ps ([g]@(l@[v]))" using play_cons play_consistent_attacker_nonpos.simps
        by (smt (verit) append_assoc lhd_LCons llist.distinct(1) ltl_simps(2))
      show "v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v]))" 
      proof
        assume "v \<in> attacker"
        hence "lhd Ps = the ((nonpos_strat_from_next g g' s) ([g]@(l @ [v])))" using play_cons play_consistent_attacker_nonpos.simps
          by (smt (verit) append_assoc lhd_LCons llist.distinct(1) ltl_simps(2))
        thus "lhd Ps = the (s (l @ [v]))" using X by auto
      qed
    qed
  qed

  have "play_consistent_attacker_nonpos s xs [g']" proof (rule play_consistent_attacker_nonpos_coinduct)
    show "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) xs ([g]@[g'])" using assms(1)
      by (metis A2 append_Cons append_Nil assms(3) llist.distinct(1) play_consistent_attacker_nonpos_cons_simp) 
    show "\<And>s v l.
       play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons v LNil) ([g] @ l) \<Longrightarrow>
       l = [] \<or> last l \<notin> attacker \<or> last l \<in> attacker \<and> the (s l) = v" using A1 by auto
    show "\<And>s v Ps l.
       play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons v Ps) ([g] @ l) \<and> Ps \<noteq> LNil \<Longrightarrow>
       play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) Ps ([g] @ l @ [v]) \<and> (v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v])))" using A2 by auto
  qed

  thus ?thesis
    by (metis A2 append.left_neutral append_Cons assms(1) llist.distinct(1) lnull_def play_consistent_attacker_nonpos_cons_simp) 
qed

text\<open>We now introduce a construction to obtain a non-positional attacker winning strategy from a strategy at a previous position.\<close>

fun nonpos_strat_from_previous:: "'position \<Rightarrow> 'position \<Rightarrow> 
  ('position list \<Rightarrow> 'position option) \<Rightarrow> ('position list \<Rightarrow> 'position option)" 
where
  "nonpos_strat_from_previous g g' s [] = s []" |
  "nonpos_strat_from_previous g g' s (x#xs) = (if x=g' then s (g#(g'#xs)) 
                                               else s (x#xs))"

lemma play_nonpos_consistent_previous: 
  assumes "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) p ([g']@l)" 
          and "g\<in>attacker \<Longrightarrow> g'=the (s [g])"
  shows "play_consistent_attacker_nonpos s p ([g,g']@l)"
proof(rule play_consistent_attacker_nonpos_coinduct)
  show "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) p (tl([g,g']@l)) \<and> length ([g,g']@l) > 1 \<and> hd ([g,g']@l) = g \<and> hd (tl ([g,g']@l)) = g'" using assms(1) by simp
  have X: "\<And>l. nonpos_strat_from_previous g g' s ([g']@l) = s ([g,g']@l)" using nonpos_strat_from_previous.simps by simp
  have Y: "\<And>l. hd l \<noteq> g' \<Longrightarrow> nonpos_strat_from_previous g g' s l = s l" using nonpos_strat_from_previous.simps
    by (metis list.sel(1) neq_Nil_conv) 
  show "\<And>s v l.
       play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) (LCons v LNil) (tl l) \<and> 1 < length l \<and> hd l = g \<and> hd (tl l) = g' \<Longrightarrow>
       l = [] \<or> last l \<notin> attacker \<or> last l \<in> attacker \<and> the (s l) = v"
  proof-
    fix s v l
    assume A: "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) (LCons v LNil) (tl l) \<and> 1 < length l \<and> hd l = g \<and> hd (tl l) = g'"
    show "l = [] \<or> last l \<notin> attacker \<or> last l \<in> attacker \<and> the (s l) = v" 
    proof(cases "last l \<in> attacker")
      case True
      hence "last (tl l) \<in> attacker"
        by (metis A hd_Cons_tl last_tl less_Suc0 remdups_adj.simps(2) remdups_adj_singleton remdups_adj_singleton_iff zero_neq_one) 
      hence "the (nonpos_strat_from_previous g g' s (tl l)) = v" using play_consistent_attacker_nonpos.simps A
        by (smt (verit) length_tl less_numeral_extra(3) list.size(3) llist.disc(1) llist.distinct(1) llist.inject zero_less_diff)
      hence "the (s l) = v" using X A
        by (smt (verit, del_insts) One_nat_def hd_Cons_tl length_Cons less_numeral_extra(4) list.inject list.size(3) not_one_less_zero nonpos_strat_from_previous.elims) 
      then show ?thesis by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  show "\<And>s v Ps l.
       (play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) (LCons v Ps) (tl l) \<and>
        1 < length l \<and> hd l = g \<and> hd (tl l) = g') \<and>
       Ps \<noteq> LNil \<Longrightarrow>
       (play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) Ps (tl (l @ [v])) \<and>
        1 < length (l @ [v]) \<and> hd (l @ [v]) = g \<and> hd (tl (l @ [v])) = g') \<and>
       (v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v])))" 
  proof-
    fix s v Ps l
    assume A: "(play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) (LCons v Ps) (tl l) \<and>
        1 < length l \<and> hd l = g \<and> hd (tl l) = g') \<and> Ps \<noteq> LNil"
    show "(play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) Ps (tl (l @ [v])) \<and>
        1 < length (l @ [v]) \<and> hd (l @ [v]) = g \<and> hd (tl (l @ [v])) = g') \<and>
       (v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v])))" 
    proof 
      show "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) Ps (tl (l @ [v])) \<and>
    1 < length (l @ [v]) \<and> hd (l @ [v]) = g \<and> hd (tl (l @ [v])) = g'" 
      proof
        show "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) Ps (tl (l @ [v]))" using A play_consistent_attacker_nonpos.simps
          by (smt (verit) lhd_LCons list.size(3) llist.distinct(1) ltl_simps(2) not_one_less_zero tl_append2)
        show "1 < length (l @ [v]) \<and> hd (l @ [v]) = g \<and> hd (tl (l @ [v])) = g'" using A
          by (metis Suc_eq_plus1 add.comm_neutral add.commute append_Nil hd_append2 length_append_singleton less_numeral_extra(4) list.exhaust_sel list.size(3) tl_append2 trans_less_add2)
      qed
      show "v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v]))" 
      proof
        assume "v \<in> attacker"
        hence "lhd Ps = the ((nonpos_strat_from_previous g g' s) (tl (l @ [v])))" using A play_consistent_attacker_nonpos.simps
          by (smt (verit) lhd_LCons list.size(3) llist.distinct(1) ltl_simps(2) not_one_less_zero tl_append2)
        thus "lhd Ps = the (s (l @ [v]))" using X A
          by (smt (verit, ccfv_SIG) One_nat_def Suc_lessD \<open>play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) Ps (tl (l @ [v])) \<and> 1 < length (l @ [v]) \<and> hd (l @ [v]) = g \<and> hd (tl (l @ [v])) = g'\<close> butlast.simps(2) butlast_snoc hd_Cons_tl length_greater_0_conv list.inject nonpos_strat_from_previous.elims) 
   
      qed
    qed
  qed
qed

text\<open>With these constructions we can show that the winning budgets defined by non-positional strategies are a fixed point of the inductive characterisation.
\<close>
lemma nonpos_winning_budget_implies_inductive: 
  assumes "nonpos_winning_budget e g"
  shows "g \<in> attacker \<Longrightarrow> (\<exists>g'. (weight g g' \<noteq> None) \<and> (apply_w g g' e)\<noteq> None
         \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))" and 
        "g \<notin> attacker \<Longrightarrow> (\<forall>g'. (weight g g' \<noteq> None) \<longrightarrow> (apply_w g g' e)\<noteq> None
         \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))"
proof-
  from assms obtain s where S: "nonpos_attacker_winning_strategy s e g" unfolding nonpos_winning_budget.simps by auto
  show "g \<in> attacker \<Longrightarrow> (\<exists>g'. (weight g g' \<noteq> None) \<and> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))" 
  proof-
    assume "g\<in> attacker"
    have finite: "lfinite (LCons g LNil)" by simp
    have play_cons_g: "play_consistent_attacker_nonpos s (LCons g LNil) []"
      by (simp add: play_consistent_attacker_nonpos.intros(2)) 
    have valid_play_g: "valid_play (LCons g LNil)"
      by (simp add: valid_play.intros(2)) 
    hence "\<not>defender_wins_play e (LCons g LNil)" using nonpos_attacker_winning_strategy.simps S play_cons_g by auto
    hence "\<not> deadend g" using finite defender_wins_play_def
      by (simp add: \<open>g \<in> attacker\<close>) 
    hence "s [g] \<noteq> None" using nonpos_attacker_winning_strategy.simps attacker_nonpos_strategy_def S
      by (simp add: \<open>g \<in> attacker\<close>) 
    show "(\<exists>g'. (weight g g' \<noteq> None) \<and> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))" 
    proof
      show "weight g (the (s [g])) \<noteq> None \<and> apply_w g (the (s [g])) e \<noteq> None \<and> nonpos_winning_budget (the (apply_w g (the (s [g])) e)) (the (s [g]))"
      proof
        show "weight g (the (s [g])) \<noteq> None" using nonpos_attacker_winning_strategy.simps attacker_nonpos_strategy_def S \<open>\<not> deadend g\<close>
          using \<open>g \<in> attacker\<close> by (metis last_ConsL not_Cons_self2)
        show "apply_w g (the (s [g])) e \<noteq> None \<and>
              nonpos_winning_budget (the (apply_w g (the (s [g])) e)) (the (s [g]))" 
        proof
          show "apply_w g (the (s [g])) e \<noteq> None" 
          proof-
            have finite: "lfinite (LCons g (LCons (the (s [g])) LNil))" by simp
            have play_cons_g': "play_consistent_attacker_nonpos s (LCons g (LCons (the (s [g])) LNil)) []" using play_cons_g play_consistent_attacker_nonpos.intros
              by (metis append_Nil lhd_LCons llist.disc(2))
            have valid_play_g': "valid_play (LCons g (LCons (the (s [g])) LNil))" using valid_play.intros valid_play_g
              using \<open>weight g (the (s [g])) \<noteq> None\<close> by auto
            hence "\<not>defender_wins_play e (LCons g (LCons (the (s [g])) LNil))" using nonpos_attacker_winning_strategy.simps S play_cons_g' by auto
            hence notNone: "energy_level e (LCons g (LCons (the (s [g])) LNil)) 1 \<noteq> None" using finite defender_wins_play_def
              by (metis One_nat_def diff_Suc_1 length_Cons length_list_of_conv_the_enat lfinite_LConsI lfinite_LNil list.size(3) list_of_LCons list_of_LNil)
            hence "energy_level e (LCons g (LCons (the (s [g])) LNil)) 1 = apply_w (lnth (LCons g (LCons (the (s [g])) LNil)) 0)(lnth (LCons g (LCons (the (s [g])) LNil)) 1) (the (energy_level e (LCons g (LCons (the (s [g])) LNil)) 0))"
              using energy_level.simps by (metis One_nat_def) 
            hence "energy_level e (LCons g (LCons (the (s [g])) LNil)) 1 = apply_w g (the (s [g])) e" by simp
            thus "apply_w g (the (s [g])) e \<noteq> None" using notNone by simp
          qed

          show "nonpos_winning_budget (the (apply_w g (the (s [g])) e)) (the (s [g]))" 
            unfolding nonpos_winning_budget.simps proof
            show "nonpos_attacker_winning_strategy (nonpos_strat_from_previous g (the (s [g])) s) (the (apply_w g (the (s [g])) e)) (the (s [g]))" 
              unfolding nonpos_attacker_winning_strategy.simps proof
              show "attacker_nonpos_strategy (nonpos_strat_from_previous g (the (s [g])) s)" using S nonpos_strat_from_previous.simps
                by (smt (verit) nonpos_strat_from_previous.elims nonpos_attacker_winning_strategy.elims(2) attacker_nonpos_strategy_def last.simps list.distinct(1)) 
              show "\<forall>p. play_consistent_attacker_nonpos (nonpos_strat_from_previous g (the (s [g])) s) (LCons (the (s [g])) p) [] \<and>
                    valid_play (LCons (the (s [g])) p) \<longrightarrow>
                    \<not> defender_wins_play (the (apply_w g (the (s [g])) e)) (LCons (the (s [g])) p) " 
              proof 
                fix p 
                show "play_consistent_attacker_nonpos (nonpos_strat_from_previous g (the (s [g])) s) (LCons (the (s [g])) p) [] \<and>
                    valid_play (LCons (the (s [g])) p) \<longrightarrow>
                    \<not> defender_wins_play (the (apply_w g (the (s [g])) e)) (LCons (the (s [g])) p) "
                proof 
                  assume A: "play_consistent_attacker_nonpos (nonpos_strat_from_previous g (the (s [g])) s) (LCons (the (s [g])) p) [] \<and>
                    valid_play (LCons (the (s [g])) p)"

                  hence play_cons: "play_consistent_attacker_nonpos s (LCons g (LCons (the (s [g])) p)) []" 
                  proof(cases "p = LNil")
                    case True
                    then show ?thesis using nonpos_strat_from_previous.simps play_consistent_attacker_nonpos.simps
                      by (smt (verit) lhd_LCons llist.discI(2) self_append_conv2) 
                  next
                    case False
                    hence "play_consistent_attacker_nonpos (nonpos_strat_from_previous g (the (s [g])) s) p [(the (s [g]))]" using A play_consistent_attacker_nonpos.cases
                      using eq_Nil_appendI lhd_LCons by fastforce
                    have "(the (s [g])) \<in> attacker \<Longrightarrow> lhd p = the ((nonpos_strat_from_previous g (the (s [g])) s) [(the (s [g]))])" using A play_consistent_attacker_nonpos.cases
                      by (simp add: False play_consistent_attacker_nonpos_cons_simp)
                    hence "(the (s [g])) \<in> attacker \<Longrightarrow> lhd p = the (s [g,(the (s [g]))])" using nonpos_strat_from_previous.simps by simp
                    then show ?thesis using play_nonpos_consistent_previous
                      by (smt (verit, del_insts) False \<open>play_consistent_attacker_nonpos (nonpos_strat_from_previous g (the (s [g])) s) p [the (s [g])]\<close> append_Cons lhd_LCons llist.collapse(1) play_consistent_attacker_nonpos.intros(5) play_consistent_attacker_nonpos.intros(6) play_consistent_attacker_nonpos_cons_simp self_append_conv2) 
                  qed

                  from A have "valid_play (LCons g (LCons (the (s [g])) p))"
                    using \<open>weight g (the (s [g])) \<noteq> None\<close> valid_play.intros(3) by auto 
                  hence not_won: "\<not> defender_wins_play e (LCons g (LCons (the (s [g])) p))" using S play_cons by simp 
                  hence "lfinite (LCons g (LCons (the (s [g])) p))" using defender_wins_play_def by simp
                  hence finite: "lfinite (LCons (the (s [g])) p)" by simp

                  from not_won have no_deadend: "\<not>(llast (LCons (the (s [g])) p) \<in> attacker \<and> deadend (llast (LCons (the (s [g])) p)))"
                    by (simp add: defender_wins_play_def)

                  have suc: "Suc (the_enat (llength (LCons (the (s [g])) p)) - 1) = (the_enat (llength (LCons g (LCons (the (s [g])) p))) - 1)" using finite
                    by (smt (verit, ccfv_SIG) Suc_length_conv diff_Suc_1 length_list_of_conv_the_enat lfinite_LCons list_of_LCons)                
                  have " the_enat (llength (LCons (the (s [g])) p)) - 1 < the_enat (llength (LCons (the (s [g])) p))" using finite
                     by (metis (no_types, lifting) diff_less lfinite_llength_enat llength_eq_0 llist.disc(2) not_less_less_Suc_eq the_enat.simps zero_enat_def zero_less_Suc zero_less_one) 
                   hence cons_e_l:"valid_play (LCons g (LCons (the (s [g])) p)) \<and>  lfinite (LCons (the (s [g])) p) \<and>  \<not> lnull (LCons (the (s [g])) p) \<and>  apply_w g (lhd (LCons (the (s [g])) p)) e \<noteq> None \<and> the_enat (llength (LCons (the (s [g])) p)) - 1 < the_enat (llength (LCons (the (s [g])) p))"
                     using \<open>valid_play (LCons g (LCons (the (s [g])) p))\<close> finite \<open>apply_w g (the (s [g])) e \<noteq> None\<close> by simp 

                  from not_won have "energy_level e (LCons g (LCons (the (s [g])) p)) (the_enat (llength (LCons g (LCons (the (s [g])) p))) - 1) \<noteq> None"
                    by (simp add: defender_wins_play_def)
                  hence "energy_level (the (apply_w g (the (s [g])) e)) (LCons (the (s [g])) p) (the_enat (llength (LCons (the (s [g])) p)) - 1) \<noteq> None" 
                    using energy_level_cons cons_e_l suc
                    by (metis enat_ord_simps(2) eq_LConsD length_list_of length_list_of_conv_the_enat)

                  thus "\<not> defender_wins_play (the (apply_w g (the (s [g])) e)) (LCons (the (s [g])) p) " using finite no_deadend defender_wins_play_def by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  show "g \<notin> attacker \<Longrightarrow> (\<forall>g'. (weight g g' \<noteq> None) \<longrightarrow> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))"
  proof-
    assume "g\<notin>attacker"
    show "(\<forall>g'. (weight g g' \<noteq> None) \<longrightarrow> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))"
    proof
      fix g'
      show "(weight g g' \<noteq> None) \<longrightarrow> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g')"
      proof 
        assume "(weight g g' \<noteq> None)"
        show "(apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g')"
        proof
          have "valid_play (LCons g (LCons g' LNil))" using \<open>(weight g g' \<noteq> None)\<close>
            by (simp add: valid_play.intros(2) valid_play.intros(3))
          have "play_consistent_attacker_nonpos s (LCons g' LNil) [g]" using play_consistent_attacker_nonpos.intros(3)
            by (simp add: \<open>g \<notin> attacker\<close>)
          hence "play_consistent_attacker_nonpos s (LCons g (LCons g' LNil)) []" using \<open>g\<notin>attacker\<close> play_consistent_attacker_nonpos.intros(5) by simp
          hence "\<not>defender_wins_play e (LCons g (LCons g' LNil))" using \<open>valid_play (LCons g (LCons g' LNil))\<close> S by simp
          hence "energy_level e (LCons g (LCons g' LNil)) (the_enat (llength (LCons g (LCons g' LNil)))-1) \<noteq> None" using defender_wins_play_def by simp
          hence "energy_level e (LCons g (LCons g' LNil)) 1 \<noteq> None"
            by (metis One_nat_def diff_Suc_1 length_Cons length_list_of_conv_the_enat lfinite_LConsI lfinite_LNil list.size(3) list_of_LCons list_of_LNil)
          thus "apply_w g g' e \<noteq> None" using energy_level.simps
            by (metis One_nat_def lnth_0 lnth_Suc_LCons option.sel)
         
          show "(nonpos_winning_budget (the (apply_w g g' e)) g')"
            unfolding nonpos_winning_budget.simps proof
            show "nonpos_attacker_winning_strategy (nonpos_strat_from_previous g g' s) (the (apply_w g g' e)) g'"
              unfolding nonpos_attacker_winning_strategy.simps proof
              show "attacker_nonpos_strategy (nonpos_strat_from_previous g g' s)" using S
                by (smt (verit, del_insts) nonpos_strat_from_previous.elims nonpos_attacker_winning_strategy.elims(2) attacker_nonpos_strategy_def last_ConsR list.distinct(1)) 
              show "\<forall>p. play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) (LCons g' p) [] \<and> valid_play (LCons g' p) \<longrightarrow>
                    \<not> defender_wins_play (the (apply_w g g' e)) (LCons g' p)"
              proof
                fix p
                show "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) (LCons g' p) [] \<and> valid_play (LCons g' p) \<longrightarrow>
                      \<not> defender_wins_play (the (apply_w g g' e)) (LCons g' p) "
                proof
                  assume A: "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) (LCons g' p) [] \<and> valid_play (LCons g' p)" 
                  hence "valid_play (LCons g (LCons g' p))"
                    using \<open>weight g g' \<noteq> None\<close> valid_play.intros(3) by auto


                  from A have "play_consistent_attacker_nonpos (nonpos_strat_from_previous g g' s) p [g']"
                    using play_consistent_attacker_nonpos.intros(1) play_consistent_attacker_nonpos_cons_simp by auto
                  hence "play_consistent_attacker_nonpos s p [g,g']" using play_nonpos_consistent_previous \<open>g\<notin>attacker\<close>
                    by fastforce 
                  hence "play_consistent_attacker_nonpos s (LCons g (LCons g' p)) []"
                    by (smt (verit) A Cons_eq_appendI \<open>play_consistent_attacker_nonpos s (LCons g (LCons g' LNil)) []\<close> eq_Nil_appendI lhd_LCons llist.discI(2) llist.distinct(1) ltl_simps(2) play_consistent_attacker_nonpos.simps nonpos_strat_from_previous.simps(2))
                  hence not_won: "\<not>defender_wins_play e (LCons g (LCons g' p))" using S \<open>valid_play (LCons g (LCons g' p))\<close> by simp
                  hence finite: "lfinite (LCons g' p)"
                    by (simp add: defender_wins_play_def)

                  from not_won have no_deadend: "\<not>(llast (LCons g' p) \<in> attacker \<and> deadend (llast (LCons g' p)))" using defender_wins_play_def by simp
                    
                  have suc: "Suc ((the_enat (llength (LCons g' p)) - 1)) = (the_enat (llength (LCons g (LCons g' p))) - 1)" 
                    using finite
                    by (smt (verit, ccfv_SIG) Suc_length_conv diff_Suc_1 length_list_of_conv_the_enat lfinite_LCons list_of_LCons) 
                  from not_won have "energy_level e (LCons g (LCons g' p)) (the_enat (llength (LCons g (LCons g' p))) - 1) \<noteq> None" using defender_wins_play_def by simp
                  hence "energy_level (the (apply_w g g' e)) (LCons g' p) (the_enat (llength (LCons g' p)) - 1) \<noteq> None"
                    using suc energy_level_cons
                    by (smt (verit, best) One_nat_def Suc_diff_Suc Suc_lessD \<open>apply_w g g' e \<noteq> None\<close> \<open>valid_play (LCons g (LCons g' p))\<close> diff_zero enat_ord_simps(2) energy_level.elims lessI lfinite_conv_llength_enat lhd_LCons llist.discI(2) llist.distinct(1) local.finite option.collapse the_enat.simps zero_less_Suc zero_less_diff)
                    thus  " \<not> defender_wins_play (the (apply_w g g' e)) (LCons g' p)" using defender_wins_play_def finite no_deadend by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma inductive_implies_nonpos_winning_budget: 
  shows "g \<in> attacker \<Longrightarrow> (\<exists>g'. (weight g g' \<noteq> None) \<and> (apply_w g g' e)\<noteq> None
         \<and> (nonpos_winning_budget (the (apply_w g g' e)) g')) 
        \<Longrightarrow> nonpos_winning_budget e g" 
        and "g \<notin> attacker \<Longrightarrow> (\<forall>g'. (weight g g' \<noteq> None) 
        \<longrightarrow> (apply_w g g' e)\<noteq> None 
        \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))
        \<Longrightarrow> nonpos_winning_budget e g"
proof-
  assume "g \<in> attacker" 
  assume "(\<exists>g'. (weight g g' \<noteq> None) \<and> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))"

  from this obtain g' where A1: "(weight g g' \<noteq> None) \<and> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g')" by auto
  hence "\<exists>s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g'" using nonpos_winning_budget.simps by auto
  from this obtain s where s_winning: "nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g'" by auto
  have "nonpos_attacker_winning_strategy (nonpos_strat_from_next g g' s) e g" unfolding nonpos_attacker_winning_strategy.simps 
  proof
    show "attacker_nonpos_strategy (nonpos_strat_from_next g g' s)" 
      unfolding attacker_nonpos_strategy_def proof
      fix list 
      show "list \<noteq> [] \<longrightarrow>
       last list \<in> attacker \<and> \<not> deadend (last list) \<longrightarrow>
       nonpos_strat_from_next g g' s list \<noteq> None \<and> weight (last list) (the (nonpos_strat_from_next g g' s list)) \<noteq> None" 
      proof 
        assume "list \<noteq> []"
        show "last list \<in> attacker \<and> \<not> deadend (last list) \<longrightarrow>
               nonpos_strat_from_next g g' s list \<noteq> None \<and> weight (last list) (the (nonpos_strat_from_next g g' s list)) \<noteq> None" 
        proof 
          assume "last list \<in> attacker \<and> \<not> deadend (last list)"
          show "nonpos_strat_from_next g g' s list \<noteq> None \<and> weight (last list) (the (nonpos_strat_from_next g g' s list)) \<noteq> None "
          proof
            from s_winning have "attacker_nonpos_strategy s" by auto
            thus "nonpos_strat_from_next g g' s list \<noteq> None" using nonpos_strat_from_next.simps(2) \<open>list \<noteq> []\<close> \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close>
              by (smt (verit) nonpos_strat_from_next.elims attacker_nonpos_strategy_def last_ConsR option.discI)
            show "weight (last list) (the (nonpos_strat_from_next g g' s list)) \<noteq> None " using nonpos_strat_from_next.simps(2) \<open>list \<noteq> []\<close> \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close>
              by (smt (verit) A1 \<open>attacker_nonpos_strategy s\<close> nonpos_strat_from_next.elims attacker_nonpos_strategy_def last_ConsL last_ConsR option.sel)
          qed
        qed
      qed
    qed
    show "\<forall>p. play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons g p) [] \<and> valid_play (LCons g p) \<longrightarrow>
        \<not> defender_wins_play e (LCons g p) "
    proof
      fix p
      show "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons g p) [] \<and> valid_play (LCons g p) \<longrightarrow>
        \<not> defender_wins_play e (LCons g p)" 
      proof 
        assume A: "play_consistent_attacker_nonpos (nonpos_strat_from_next g g' s) (LCons g p)[] \<and> valid_play (LCons g p)"
        hence "play_consistent_attacker_nonpos s p []" 
        proof(cases "p=LNil")
          case True
          then show ?thesis
            by (simp add: play_consistent_attacker_nonpos.intros(1)) 
        next
          case False
          hence "\<exists>v p'. p=LCons v p'"
            by (meson llist.exhaust)
          from this obtain v p' where "p= LCons v p'" by auto
          then show ?thesis 
          proof(cases "p'=LNil")
            case True
            then show ?thesis
              by (simp add: \<open>p = LCons v p'\<close> play_consistent_attacker_nonpos.intros(2)) 
          next
            case False
            from \<open>p= LCons v p'\<close> have "v=g'" using A nonpos_strat_from_next.simps play_nonpos_consistent_previous \<open>g \<in> attacker\<close>
              by (simp add: play_consistent_attacker_nonpos_cons_simp)
            then show ?thesis using \<open>p= LCons v p'\<close> A nonpos_strat_from_next.simps play_nonpos_consistent_next
              using False \<open>g \<in> attacker\<close> by blast
          qed
        qed

        have "valid_play p" using A valid_play.simps
          by (metis eq_LConsD) 
        hence notNil: "p\<noteq>LNil \<Longrightarrow> \<not> defender_wins_play (the (apply_w g g' e)) p" using s_winning \<open>play_consistent_attacker_nonpos s p []\<close> nonpos_attacker_winning_strategy.elims
          by (metis A \<open>g \<in> attacker\<close> lhd_LCons not_lnull_conv option.sel play_consistent_attacker_nonpos_cons_simp nonpos_strat_from_next.simps(2))
        show " \<not> defender_wins_play e (LCons g p)" 
        proof(cases "p=LNil")
          case True
          hence "lfinite (LCons g p)" by simp
          have "llast  (LCons g p) = g" using True by simp
          hence not_deadend: "\<not> deadend (llast  (LCons g p))" using A1 by auto 
          have "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using True
            by (simp add: gen_llength_code(1) gen_llength_code(2) llength_code)
          then show ?thesis using defender_wins_play_def not_deadend \<open>lfinite (LCons g p)\<close> by simp
        next
          case False
          hence "\<not> defender_wins_play (the (apply_w g g' e)) p" using notNil by simp
          hence not: "lfinite p \<and> energy_level (the (apply_w g g' e)) p (the_enat (llength p) - 1) \<noteq> None \<and> \<not>(llast p \<in> attacker \<and> deadend (llast p))" using defender_wins_play_def
            by simp 
          hence "lfinite (LCons g p)" by simp

          from False have "llast (LCons g p) = llast p"
            by (meson llast_LCons llist.collapse(1)) 
          hence "\<not>(llast (LCons g p) \<in> attacker \<and> deadend (llast (LCons g p)))" using not by simp

          from  \<open>lfinite (LCons g p)\<close> have "the_enat (llength (LCons g p)) = Suc (the_enat (llength p))"
            by (metis eSuc_enat lfinite_LCons lfinite_conv_llength_enat llength_LCons the_enat.simps)
          hence E:"(the_enat (llength (LCons g p)) - 1) = Suc (the_enat (llength p) - 1)" using \<open>lfinite (LCons g p)\<close> False
            by (metis diff_Suc_1 diff_self_eq_0 gr0_implies_Suc i0_less less_enatE less_imp_diff_less lfinite_llength_enat llength_eq_0 llist.collapse(1) not the_enat.simps) 

          from False have "lhd p = g'" using A nonpos_strat_from_next.simps play_nonpos_consistent_previous \<open>g\<in>attacker\<close>
            by (simp add: play_consistent_attacker_nonpos_cons_simp)
          hence "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) = energy_level (the (apply_w g g' e)) p (the_enat (llength p) - 1)" 
            using energy_level_cons A not False A1 E
            by (metis \<open>the_enat (llength (LCons g p)) = Suc (the_enat (llength p))\<close> diff_Suc_1 enat_ord_simps(2) lessI lfinite_conv_llength_enat play_consistent_attacker_nonpos_cons_simp the_enat.simps)
          hence "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using not by auto 
          then show ?thesis using defender_wins_play_def \<open>lfinite (LCons g p)\<close> \<open>\<not>(llast (LCons g p) \<in> attacker \<and> deadend (llast (LCons g p)))\<close> by auto
        qed
      qed
    qed
  qed
  thus "nonpos_winning_budget e g" using nonpos_winning_budget.simps by auto
next
  assume "g \<notin> attacker"
  assume all: "(\<forall>g'. (weight g g' \<noteq> None) \<longrightarrow> (apply_w g g' e)\<noteq> None \<and> (nonpos_winning_budget (the (apply_w g g' e)) g'))"

  have valid: "attacker_nonpos_strategy (\<lambda>list. (case list of
              [] \<Rightarrow> None |
              [x] \<Rightarrow> (if x \<in> attacker \<and> \<not>deadend x then Some (SOME y. weight x y \<noteq> None) else None) |
              (x#(g'#xs)) \<Rightarrow> (if (x=g \<and> weight x g' \<noteq> None) then ((SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g' ) (g'#xs))
                              else (if (last (x#(g'#xs))) \<in> attacker \<and> \<not>deadend (last (x#(g'#xs))) then Some (SOME y. weight (last (x#(g'#xs))) y \<noteq> None) else None))))"
    unfolding attacker_nonpos_strategy_def proof
    fix list
    show "list \<noteq> [] \<longrightarrow>
       last list \<in> attacker \<and> \<not> deadend (last list) \<longrightarrow>
       (case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
        | x # g' # xs \<Rightarrow>
            if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
            else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                 then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) \<noteq>
       None \<and>
       weight (last list)
        (the (case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
              | x # g' # xs \<Rightarrow>
                  if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                  else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                       then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None)) \<noteq>
       None"
    proof
      assume "list \<noteq> []"
      show "last list \<in> attacker \<and> \<not> deadend (last list) \<longrightarrow>
    (case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
     | x # g' # xs \<Rightarrow>
         if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
         else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
              then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) \<noteq>
    None \<and>
    weight (last list)
     (the (case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
           | x # g' # xs \<Rightarrow>
               if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
               else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                    then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None)) \<noteq>
    None"
      proof 
        assume "last list \<in> attacker \<and> \<not> deadend (last list)"
        show "(case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
     | x # g' # xs \<Rightarrow>
         if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
         else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
              then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) \<noteq>
    None \<and>
    weight (last list)
     (the (case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
           | x # g' # xs \<Rightarrow>
               if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
               else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                    then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None)) \<noteq>
    None"
        proof
          show "(case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) \<noteq> None"
          proof(cases "length list = 1")
            case True
            then show ?thesis
              by (smt (verit) One_nat_def \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close> append_butlast_last_id append_eq_Cons_conv butlast_snoc length_0_conv length_Suc_conv_rev list.simps(4) list.simps(5) option.discI) 
          next
            case False
            hence "\<exists>x y xs. list = x # (y # xs)"
              by (metis One_nat_def \<open>list \<noteq> []\<close> length_Cons list.exhaust list.size(3))
            from this obtain x y xs where "list = x # (y # xs)" by auto
            then show ?thesis proof(cases "(x=g \<and> weight x y \<noteq> None)")
              case True
              hence A: "(case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) = (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y) (y#xs)"
                using \<open>list = x # y # xs\<close> list.simps(5) by fastforce

              from all True have "\<exists>s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y" by auto
              hence "nonpos_attacker_winning_strategy (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y) (the (apply_w g y e)) y" 
                using some_eq_ex by metis 
              hence "attacker_nonpos_strategy (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y)"
                by (meson nonpos_attacker_winning_strategy.simps)
              hence "(SOME s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y) (y#xs) \<noteq> None" 
                using \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close> \<open>list = x # (y # xs)\<close>
                by (simp add: list.distinct(1) attacker_nonpos_strategy_def) 

              then show ?thesis using A by simp
            next
              case False
              hence "(case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) = 
              Some (SOME z. weight (last (x # y # xs)) z \<noteq> None)"
                using \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close> \<open>list = x # y # xs\<close> by auto 
              then show ?thesis by simp 
            qed
          qed

          show "weight (last list)
                (the (case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                      | x # g' # xs \<Rightarrow>
                        if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                        else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                        then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None)) \<noteq> None"
          proof(cases "length list =1")
            case True
            hence "the (case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
           | x # g' # xs \<Rightarrow>
               if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
               else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                    then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) = (SOME y. weight (last list) y \<noteq> None)" 
              using \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close>
              by (smt (verit) Eps_cong One_nat_def \<open>(case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None | x # g' # xs \<Rightarrow> if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g' # xs) else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs)) then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) \<noteq> None\<close> last_snoc length_0_conv length_Suc_conv_rev list.case_eq_if list.sel(1) list.sel(3) option.sel self_append_conv2) 
            then show ?thesis
              by (smt (verit, del_insts) \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close> some_eq_ex)
          next
            case False
            hence "\<exists>x y xs. list = x # (y # xs)"
              by (metis One_nat_def \<open>list \<noteq> []\<close> length_Cons list.exhaust list.size(3))
            from this obtain x y xs where "list = x # (y # xs)" by auto
            then show ?thesis proof(cases "(x=g \<and> weight x y \<noteq> None)")
              case True
              hence "(case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) = (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y) (y#xs)"
                using \<open>list = x # y # xs\<close> list.simps(5) by fastforce

              from all True have "\<exists>s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y" by auto
              hence "nonpos_attacker_winning_strategy (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y) (the (apply_w g y e)) y" 
                using some_eq_ex by metis 
              then show ?thesis
                by (smt (verit) \<open>(case list of [] \<Rightarrow> None | [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None | x # g' # xs \<Rightarrow> if x = g \<and> weight x g' \<noteq> None then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g' # xs) else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs)) then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) = (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g y e)) y) (y # xs)\<close> \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close> \<open>list = x # y # xs\<close> attacker_nonpos_strategy_def nonpos_attacker_winning_strategy.elims(1) last_ConsR list.distinct(1))
            next
              case False
              hence "(case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None) = 
              Some (SOME z. weight (last (x # y # xs)) z \<noteq> None)"
                using \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close> \<open>list = x # y # xs\<close> by auto 
              then show ?thesis
                by (smt (verit, del_insts) \<open>last list \<in> attacker \<and> \<not> deadend (last list)\<close> \<open>list = x # y # xs\<close> option.sel verit_sko_ex_indirect)
            qed
          qed
        qed
      qed
    qed
  qed


  have winning: "(\<forall>p. (play_consistent_attacker_nonpos (\<lambda>list. (case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None)) (LCons g p) [] 
                \<and> valid_play (LCons g p)) \<longrightarrow> \<not> defender_wins_play e (LCons g p))" 
  proof
    fix p 
    show "(play_consistent_attacker_nonpos (\<lambda>list. (case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None)) (LCons g p) [] 
                \<and> valid_play (LCons g p)) \<longrightarrow> \<not> defender_wins_play e (LCons g p)"
    proof
      assume A: "(play_consistent_attacker_nonpos (\<lambda>list. (case list of [] \<Rightarrow> None | 
                [x] \<Rightarrow> if x \<in> attacker \<and> \<not> deadend x then Some (SOME y. weight x y \<noteq> None) else None
                | x # g' # xs \<Rightarrow>
                if (x=g \<and> weight x g' \<noteq> None) then (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g') (g'#xs)
                else if last (x # g' # xs) \<in> attacker \<and> \<not> deadend (last (x # g' # xs))
                      then Some (SOME y. weight (last (x # g' # xs)) y \<noteq> None) else None)) (LCons g p) [] 
                \<and> valid_play (LCons g p))"
      show "\<not> defender_wins_play e (LCons g p)"

      proof(cases "p = LNil")
        case True
        hence "lfinite (LCons g p)"
          by simp 
        from True have "llength (LCons g p) = enat 1"
          by (simp add: gen_llength_code(1) gen_llength_code(2) llength_code)
        hence "the_enat (llength (LCons g p))-1 = 0" by simp
        hence "energy_level e (LCons g p) (the_enat (llength (LCons g p))-1) = Some e" using energy_level.simps
          by simp 
        thus ?thesis using \<open>g \<notin> attacker\<close> \<open>lfinite (LCons g p)\<close> defender_wins_play_def
          by (simp add: True)
      next
        case False
        hence "weight g (lhd p) \<noteq> None" using A
          using llist.distinct(1) valid_play.cases by auto

        hence "\<exists>s. (nonpos_attacker_winning_strategy s (the (apply_w g (lhd p) e)) (lhd p)) \<and> play_consistent_attacker_nonpos s p []"
        proof-
          have "\<exists>s. (nonpos_attacker_winning_strategy s (the (apply_w g (lhd p) e)) (lhd p))" using \<open>weight g (lhd p) \<noteq> None\<close> all by simp
          hence a_win: "nonpos_attacker_winning_strategy (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g (lhd p) e)) (lhd p)) (the (apply_w g (lhd p) e)) (lhd p)"
            by (smt (verit, del_insts) list.simps(9) nat.case_distrib nat.disc_eq_case(1) neq_Nil_conv take_Suc take_eq_Nil2 tfl_some verit_sko_forall')
  
          define strat where Strat: "strat \<equiv> (SOME s. nonpos_attacker_winning_strategy s (the (apply_w g (lhd p) e)) (lhd p))"
          define strategy where Strategy: "strategy \<equiv> (\<lambda>list. (case list of
                          [] \<Rightarrow> None |
                          [x] \<Rightarrow> (if x \<in> attacker \<and> \<not>deadend x then Some (SOME y. weight x y \<noteq> None) else None) |
                          (x#(g'#xs)) \<Rightarrow> (if (x=g \<and> weight x g' \<noteq> None) then ((SOME s. nonpos_attacker_winning_strategy s (the (apply_w g g' e)) g' ) (g'#xs))
                              else (if (last (x#(g'#xs))) \<in> attacker \<and> \<not>deadend (last (x#(g'#xs))) then Some (SOME y. weight (last (x#(g'#xs))) y \<noteq> None) else None))))"

          hence "play_consistent_attacker_nonpos strategy (LCons g p) []" using A by simp
          hence strategy_cons: "play_consistent_attacker_nonpos strategy (ltl p) [g, lhd p]" using play_consistent_attacker_nonpos.simps
            by (smt (verit) False butlast.simps(2) last_ConsL last_ConsR lhd_LCons list.distinct(1) ltl_simps(2) play_consistent_attacker_nonpos_cons_simp snoc_eq_iff_butlast)

          have tail: "\<And>p'. strategy (g#((lhd p)#p')) = strat ((lhd p)#p')" unfolding Strategy Strat 
            by (simp add: \<open>weight g (lhd p) \<noteq> None\<close>)

          define Q where Q: "\<And>s P l. Q s P l \<equiv> play_consistent_attacker_nonpos strategy P (g#l)
                                                  \<and> l \<noteq> [] \<and> (\<forall>p'. strategy (g#((hd l)#p')) = s ((hd l)#p'))"

          have "play_consistent_attacker_nonpos strat (ltl p) [lhd p]" 
          proof(rule play_consistent_attacker_nonpos_coinduct)
            show "Q strat (ltl p) [lhd p]"
              unfolding Q using tail strategy_cons False play_consistent_attacker_nonpos_cons_simp by auto 

            show "\<And>s v l. Q s (LCons v LNil) l \<Longrightarrow> l = [] \<or> last l \<notin> attacker \<or> last l \<in> attacker \<and> the (s l) = v"
            proof-
              fix s v l
              assume "Q s (LCons v LNil) l" 
              have "l\<noteq>[] \<and> last l \<in> attacker \<Longrightarrow> the (s l) = v" 
              proof-
                assume "l\<noteq>[] \<and> last l \<in> attacker"
                hence "(\<forall>p'. strategy (g#((hd l)#p')) = s ((hd l)#p'))" using \<open>Q s (LCons v LNil) l\<close> Q by simp
                hence "s l = strategy (g#l)"
                  by (metis \<open>l \<noteq> [] \<and> last l \<in> attacker\<close> list.exhaust list.sel(1)) 

                from \<open>l\<noteq>[] \<and> last l \<in> attacker\<close> have "last (g#l) \<in> attacker" by simp
                from  \<open>Q s (LCons v LNil) l\<close> have "the (strategy (g#l)) = v" unfolding Q using play_consistent_attacker_nonpos.simps \<open>last (g#l) \<in> attacker\<close>
                  using eq_LConsD list.discI llist.disc(1) by blast
                thus "the (s l) = v" using \<open>s l = strategy (g#l)\<close> by simp
              qed
              thus "l = [] \<or> last l \<notin> attacker \<or> last l \<in> attacker \<and> the (s l) = v" by auto
            qed


            show "\<And>s v Ps l. Q s (LCons v Ps) l \<and> Ps \<noteq> LNil \<Longrightarrow> Q s Ps (l @ [v]) \<and> (v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v])))"
            proof-
              fix s v Ps l
              assume "Q s (LCons v Ps) l \<and> Ps \<noteq> LNil"
              hence A: "play_consistent_attacker_nonpos strategy (LCons v Ps) (g#l)
                                                  \<and> l\<noteq> [] \<and> (\<forall>p'. strategy (g#((hd l)#p')) = s ((hd l)#p'))" unfolding Q by simp

              show "Q s Ps (l @ [v]) \<and> (v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v])))"
              proof
                show "Q s Ps (l @ [v])"
                  unfolding Q proof
                  show "play_consistent_attacker_nonpos strategy Ps (g # l @ [v])"
                    using A play_consistent_attacker_nonpos.simps
                    by (smt (verit) Cons_eq_appendI lhd_LCons llist.distinct(1) ltl_simps(2)) 
                  have "(\<forall>p'. strategy (g # hd (l @ [v]) # p') = s (hd (l @ [v]) # p'))" using A by simp
                  thus "l @ [v] \<noteq> [] \<and> (\<forall>p'. strategy (g # hd (l @ [v]) # p') = s (hd (l @ [v]) # p')) " by auto
                qed

                show "(v \<in> attacker \<longrightarrow> lhd Ps = the (s (l @ [v])))"
                proof
                  assume "v \<in> attacker"
                  hence "the (strategy (g#(l@[v]))) = lhd Ps" using A play_consistent_attacker_nonpos.simps
                    by (smt (verit) Cons_eq_appendI \<open>Q s (LCons v Ps) l \<and> Ps \<noteq> LNil\<close> lhd_LCons llist.distinct(1) ltl_simps(2)) 

                  have "s (l @ [v]) = strategy (g#(l@[v]))" using A
                    by (metis (no_types, lifting) hd_Cons_tl hd_append2 snoc_eq_iff_butlast) 
                  thus "lhd Ps = the (s (l @ [v]))" using \<open>the (strategy (g#(l@[v]))) = lhd Ps\<close> by simp
              qed
            qed
          qed
        qed
        hence "play_consistent_attacker_nonpos strat p []" using play_consistent_attacker_nonpos.simps
          by (smt (verit) False \<open>g \<notin> attacker\<close> \<open>play_consistent_attacker_nonpos strategy (LCons g p) []\<close> append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR lhd_LCons lhd_LCons_ltl list.distinct(1) ltl_simps(2) play_consistent_attacker_nonpos_cons_simp tail)
        thus ?thesis using Strat a_win by blast
        qed

        from this obtain s where S: "(nonpos_attacker_winning_strategy s (the (apply_w g (lhd p) e)) (lhd p)) \<and> play_consistent_attacker_nonpos s p []" by auto
        have "valid_play p" using A
          by (metis llist.distinct(1) ltl_simps(2) valid_play.simps)
        hence "\<not>defender_wins_play (the (apply_w g (lhd p) e)) p" using S
          by (metis False nonpos_attacker_winning_strategy.elims(2) lhd_LCons llist.collapse(1) not_lnull_conv)
        hence P: "lfinite p \<and> (energy_level (the (apply_w g (lhd p) e)) p (the_enat (llength p)-1)) \<noteq> None \<and> \<not> ((llast p)\<in> attacker \<and> deadend (llast p))"
          using defender_wins_play_def by simp

        hence "\<exists>n. llength p = enat (Suc n)" using False
          by (metis lfinite_llength_enat llength_eq_0 lnull_def old.nat.exhaust zero_enat_def) 
        from this obtain n where "llength p = enat (Suc n)" by auto
        hence "llength (LCons g p) = enat (Suc (Suc n))"
          by (simp add: eSuc_enat) 
        hence "Suc (the_enat (llength p)-1) = (the_enat (llength (LCons g p))-1)" using \<open>llength p = enat (Suc n)\<close> by simp

        from \<open>weight g (lhd p) \<noteq> None\<close> have "(apply_w g (lhd p) e)\<noteq> None"
          by (simp add: all)
        hence "energy_level (the (apply_w g (lhd p) e)) p (the_enat (llength p)-1) = energy_level e (LCons g p) (the_enat (llength (LCons g p))-1)"
          using P energy_level_cons \<open>Suc (the_enat (llength p)-1) = (the_enat (llength (LCons g p))-1)\<close> A
          by (metis (no_types, lifting) False \<open>\<exists>n. llength p = enat (Suc n)\<close> diff_Suc_1 enat_ord_simps(2) lessI llist.collapse(1) the_enat.simps)
        hence "(energy_level e (LCons g p) (the_enat (llength (LCons g p))-1)) \<noteq> None" 
          using P by simp
        then show ?thesis using P
          by (simp add: False energy_game.defender_wins_play_def llast_LCons lnull_def) 
      qed
    qed
  qed
 
  show "nonpos_winning_budget e g" using nonpos_winning_budget.simps nonpos_attacker_winning_strategy.simps winning valid
    by blast 
qed

lemma winning_budget_ind_implies_nonpos:
  assumes "winning_budget_ind e g"
  shows "nonpos_winning_budget e g" 
proof-
  define f where "f = (\<lambda>p x1 x2.
            (\<exists>g e. x1 = e \<and>
                   x2 = g \<and>
                   g \<notin> attacker \<and>
                   (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                         apply_w g g' e \<noteq> None \<and> p (the (apply_w g g' e)) g')) \<or>
            (\<exists>g e. x1 = e \<and>
                   x2 = g \<and>
                   g \<in> attacker \<and>
                   (\<exists>g'. weight g g' \<noteq> None \<and>
                         apply_w g g' e \<noteq> None \<and> p (the (apply_w g g' e)) g')))"

  have "f nonpos_winning_budget = nonpos_winning_budget"
    unfolding f_def 
  proof
    fix e0 
    show "(\<lambda>x2. (\<exists>g e. e0 = e \<and>
                       x2 = g \<and>
                       g \<notin> attacker \<and>
                       (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                             apply_w g g' e \<noteq> None \<and>
                             nonpos_winning_budget (the (apply_w g g' e)) g')) \<or>
                (\<exists>g e. e0 = e \<and>
                       x2 = g \<and>
                       g \<in> attacker \<and>
                       (\<exists>g'. weight g g' \<noteq> None \<and>
                             apply_w g g' e \<noteq> None \<and>
                             nonpos_winning_budget (the (apply_w g g' e)) g'))) =
          nonpos_winning_budget e0"
    proof
      fix g0
      show "((\<exists>g e. e0 = e \<and>
                  g0 = g \<and>
                  g \<notin> attacker \<and>
                  (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                        apply_w g g' e \<noteq> None \<and>
                        nonpos_winning_budget (the (apply_w g g' e)) g')) \<or>
           (\<exists>g e. e0 = e \<and>
                  g0 = g \<and>
                  g \<in> attacker \<and>
                  (\<exists>g'. weight g g' \<noteq> None \<and>
                        apply_w g g' e \<noteq> None \<and>
                        nonpos_winning_budget (the (apply_w g g' e)) g'))) =
          nonpos_winning_budget e0 g0"
      proof
        assume " (\<exists>g e. e0 = e \<and>
           g0 = g \<and>
           g \<notin> attacker \<and>
           (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                 apply_w g g' e \<noteq> None \<and> nonpos_winning_budget (the (apply_w g g' e)) g')) \<or>
    (\<exists>g e. e0 = e \<and>
           g0 = g \<and>
           g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 apply_w g g' e \<noteq> None \<and> nonpos_winning_budget (the (apply_w g g' e)) g'))"
        thus "nonpos_winning_budget e0 g0" using inductive_implies_nonpos_winning_budget
          by blast
      next
        assume "nonpos_winning_budget e0 g0"
        thus " (\<exists>g e. e0 = e \<and>
           g0 = g \<and>
           g \<notin> attacker \<and>
           (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                 apply_w g g' e \<noteq> None \<and> nonpos_winning_budget (the (apply_w g g' e)) g')) \<or>
    (\<exists>g e. e0 = e \<and>
           g0 = g \<and>
           g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 apply_w g g' e \<noteq> None \<and> nonpos_winning_budget (the (apply_w g g' e)) g'))"
          using nonpos_winning_budget_implies_inductive
          by meson
      qed
    qed
  qed
  hence "lfp f \<le> nonpos_winning_budget " 
    using lfp_lowerbound
    by (metis order_refl)
  hence "winning_budget_ind \<le> nonpos_winning_budget"
    using f_def HOL.nitpick_unfold(211) by simp

  thus ?thesis using assms
    by blast 
qed

text\<open>Finally, we can state the inductive characterisation of attacker winning budgets assuming energy-positional determinacy.\<close>

lemma inductive_winning_budget:
  assumes "nonpos_winning_budget = winning_budget"
  shows "winning_budget = winning_budget_ind"
proof
  fix e
  show "winning_budget e = winning_budget_ind e"
  proof
    fix g 
    show "winning_budget e g = winning_budget_ind e g"
    proof
      assume "winning_budget e g"
      thus "winning_budget_ind e g"
        using winning_budget_implies_ind winning_budget.simps by auto 
    next
      assume "winning_budget_ind e g"
      hence "nonpos_winning_budget e g"
        using winning_budget_ind_implies_nonpos by simp
      thus "winning_budget e g" using assms by simp
    qed
  qed
qed

end
end