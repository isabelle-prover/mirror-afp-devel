section \<open>Minimisation by OFSM Tables\<close>

text \<open>This theory presents the classical algorithm for transforming observable FSMs into 
      language-equivalent observable and minimal FSMs in analogy to the minimisation of
      finite automata.\<close>


theory Minimisation
imports FSM 
begin


subsection \<open>OFSM Tables\<close>

text \<open>OFSM tables partition the states of an FSM based on an initial partition and an iteration
      counter.
      States are in the same element of the 0th table iff they are in the same element of the
      initial partition.
      States q1, q2 are in the same element of the (k+1)-th table if they are in the same element of
      the k-th table and furthermore for each IO pair (x,y) either (x,y) is not in the language of
      both q1 and q2 or it is in the language of both states and the states q1', q2' reached via
      (x,y) from q1 and q2, respectively, are in the same element of the k-th table.\<close>


fun ofsm_table :: "('a,'b,'c) fsm \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "ofsm_table M f 0 q = (if q \<in> states M then f q else {})" |
  "ofsm_table M f (Suc k) q = (let 
      prev_table = ofsm_table M f k 
    in {q' \<in> prev_table q . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> prev_table qT = prev_table qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None) })"


lemma ofsm_table_non_state :
  assumes "q \<notin> states M"
  shows "ofsm_table M f k q = {}"
using assms by (induction k; auto)

lemma ofsm_table_subset: 
  assumes "i \<le> j"
  shows "ofsm_table M f j q \<subseteq> ofsm_table M f i q"
proof -
  have *: "\<And> k . ofsm_table M f (Suc k) q \<subseteq> ofsm_table M f k q"
  proof -
    fix k show "ofsm_table M f (Suc k) q \<subseteq> ofsm_table M f k q"
    proof (cases k)
      case 0
      show ?thesis unfolding 0 ofsm_table.simps Let_def by blast
    next
      case (Suc k')
      
      show ?thesis 
        unfolding Suc ofsm_table.simps Let_def by force
    qed
  qed
  
  show ?thesis
    using assms 
  proof (induction j)
    case 0
    then show ?case by auto
  next
    case (Suc x)
    then show ?case using *[of x]
      using le_SucE by blast 
  qed
qed


lemma ofsm_table_case_helper :
  "(case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)
   = ((\<exists> qT qT' . h_obs M q x y = Some qT \<and> h_obs M q' x y = Some qT' \<and> ofsm_table M f k qT = ofsm_table M f k qT') \<or> (h_obs M q x y = None \<and> h_obs M q' x y = None))"
proof -
  have *: "\<And> a b P . (case a of Some a' \<Rightarrow> (case b of Some b' \<Rightarrow> P a' b' | None \<Rightarrow> False) | None \<Rightarrow> b = None)
    = ((\<exists> a' b' . a = Some a' \<and> b = Some b' \<and> P a' b') \<or> (a = None \<and> b = None))"
    (is "\<And> a b P . ?P1 a b P = ?P2 a b P")
  proof 
    fix a b P
    show "?P1 a b P \<Longrightarrow> ?P2 a b P" using case_optionE[of "b = None" "\<lambda>a' . (case b of Some b' \<Rightarrow> P a' b' | None \<Rightarrow> False)" a]
      by (metis case_optionE) 
    show "?P2 a b P \<Longrightarrow> ?P1 a b P" by auto
  qed
  
  show ?thesis 
    using *[of "h_obs M q' x y" "\<lambda>qT qT' . ofsm_table M f k qT = ofsm_table M f k qT'" "h_obs M q x y"] .
qed


lemma ofsm_table_case_helper_neg :
  "(\<not> (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None))
   = ((\<exists> qT qT' . h_obs M q x y = Some qT \<and> h_obs M q' x y = Some qT' \<and> ofsm_table M f k qT \<noteq> ofsm_table M f k qT') \<or> (h_obs M q x y = None \<longleftrightarrow> h_obs M q' x y \<noteq> None))"
  unfolding ofsm_table_case_helper by force 



lemma ofsm_table_fixpoint :
  assumes "i \<le> j"
  and     "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f (Suc i) q = ofsm_table M f i q"
  and     "q \<in> states M"
shows "ofsm_table M f j q = ofsm_table M f i q"
proof -

  have *: "\<And> k . k \<ge> i \<Longrightarrow> (\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f (Suc k) q = ofsm_table M f k q)"
  proof -
    
    fix k :: nat assume "k \<ge> i" 
    then show "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f (Suc k) q = ofsm_table M f k q"
    proof (induction k)
      case 0
      then show ?case using assms(2) by auto
    next
      case (Suc k)

      show "ofsm_table M f (Suc (Suc k)) q = ofsm_table M f (Suc k) q" 
      proof (cases "i = Suc k")
        case True
        then show ?thesis using assms(2)[OF \<open>q \<in> states M\<close>] by simp
      next
        case False
        then have "i \<le> k"
          using \<open>i \<le> Suc k\<close> by auto

        have h_obs_state: "\<And> q x y qT . h_obs M q x y = Some qT \<Longrightarrow> qT \<in> states M"
          using h_obs_state by fastforce

        show ?thesis 
        proof (rule ccontr) 
          assume "ofsm_table M f (Suc (Suc k)) q \<noteq> ofsm_table M f (Suc k) q"
          moreover have "ofsm_table M f (Suc (Suc k)) q \<subseteq> ofsm_table M f (Suc k) q"
            using ofsm_table_subset
            by (metis (full_types) Suc_n_not_le_n nat_le_linear) 
          ultimately obtain q' where "q' \<notin> {q' \<in> ofsm_table M f (Suc k) q . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f (Suc k) qT = ofsm_table M f (Suc k) qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None) }"
                                 and "q' \<in> ofsm_table M f (Suc k) q"
            using ofsm_table.simps(2)[of M f "Suc k" q] unfolding Let_def by blast
          then have "\<not>(\<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f (Suc k) qT = ofsm_table M f (Suc k) qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None))"
            by blast
          then obtain x y where "x \<in> inputs M" and "y \<in> outputs M" and "\<not> (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f (Suc k) qT = ofsm_table M f (Suc k) qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
            by blast            
          then consider "\<exists> qT qT' . h_obs M q x y = Some qT \<and> h_obs M q' x y = Some qT' \<and> ofsm_table M f (Suc k) qT \<noteq> ofsm_table M f (Suc k) qT'" |
                        "(h_obs M q x y = None \<longleftrightarrow> h_obs M q' x y \<noteq> None)"
            unfolding ofsm_table_case_helper_neg by blast 
          then show False proof cases
            case 1
            then obtain qT qT' where "h_obs M q x y = Some qT" and "h_obs M q' x y = Some qT'" and "ofsm_table M f (Suc k) qT \<noteq> ofsm_table M f (Suc k) qT'"
              by blast
            then have "ofsm_table M f k qT \<noteq> ofsm_table M f k qT'"
              using Suc.IH[OF h_obs_state[OF \<open>h_obs M q x y = Some qT\<close>] \<open>i \<le> k\<close>]
                    Suc.IH[OF h_obs_state[OF \<open>h_obs M q' x y = Some qT'\<close>] \<open>i \<le> k\<close>]
              by fast
            moreover have "q' \<in> ofsm_table M f k q"
              using ofsm_table_subset[of k "Suc k"] \<open>q' \<in> ofsm_table M f (Suc k) q\<close> by force
            ultimately have "ofsm_table M f (Suc k) q \<noteq> ofsm_table M f k q"
              using \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> \<open>h_obs M q x y = Some qT\<close> \<open>h_obs M q' x y = Some qT'\<close>
              unfolding ofsm_table.simps(2) Let_def by force
            then show ?thesis 
              using Suc.IH[OF Suc.prems(1) \<open>i \<le> k\<close>] by simp 
          next
            case 2
            then have "\<not> (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
              unfolding ofsm_table_case_helper_neg by blast
            moreover have "q' \<in> ofsm_table M f k q"
              using ofsm_table_subset[of k "Suc k"] \<open>q' \<in> ofsm_table M f (Suc k) q\<close> by force
            ultimately have "ofsm_table M f (Suc k) q \<noteq> ofsm_table M f k q"
              using \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> 
              unfolding ofsm_table.simps(2) Let_def by force
            then show ?thesis 
              using Suc.IH[OF Suc.prems(1) \<open>i \<le> k\<close>] by simp
          qed
        qed
      qed
    qed
  qed
  
  show ?thesis
    using assms(1) proof (induction "j")
    case 0
    then show ?case by auto
  next
    case (Suc j) 
    
    show ?case proof (cases "i = Suc j")
      case True
      then show ?thesis by simp
    next
      case False
      then have "i \<le> j"
        using Suc.prems(1) by auto
      then have "ofsm_table M f j q = ofsm_table M f i q"
        using Suc.IH by auto
      moreover have "ofsm_table M f (Suc j) q = ofsm_table M f j q"
        using *[OF \<open>i\<le>j\<close> \<open>q\<in>states M\<close>] by assumption
      ultimately show ?thesis 
        by blast
    qed
  qed
qed


(* restricts the range of the supplied function to the states of the FSM - required for (easy) termination *)
function ofsm_table_fix :: "('a,'b,'c) fsm \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "ofsm_table_fix M f k = (let
    cur_table = ofsm_table M (\<lambda>q. f q \<inter> states M) k;
    next_table = ofsm_table M (\<lambda>q. f q \<inter> states M) (Suc k)
  in if (\<forall> q \<in> states M . cur_table q = next_table q)
    then cur_table
    else ofsm_table_fix M f (Suc k))"
  by pat_completeness auto
termination   
proof -
  {
    fix M :: "('a,'b,'c) fsm"
    and f :: "('a \<Rightarrow> 'a set)"
    and k :: nat 
  
    define f' where f': "f' = (\<lambda>q. f q \<inter> states M)"
    
    assume "\<exists>q\<in>FSM.states M. ofsm_table M (\<lambda>q. f q \<inter> states M) k q \<noteq> ofsm_table M (\<lambda>q. f q \<inter> states M) (Suc k) q"
    then obtain q where "q \<in> states M"
                    and "ofsm_table M f' k q \<noteq> ofsm_table M f' (Suc k) q"
      unfolding f' by blast
  
    have *: "\<And> k . (\<Sum>q\<in>FSM.states M. card (ofsm_table M f' k q)) = card (ofsm_table M f' k q) + (\<Sum>q\<in>FSM.states M - {q}. card (ofsm_table M f' k q))"
      using \<open>q \<in> states M\<close> by (meson fsm_states_finite sum.remove)
  
    have "\<And> q . ofsm_table M f' (Suc k) q \<subseteq> ofsm_table M f' k q"
      using ofsm_table_subset[of k "Suc k" M ] by auto
    moreover have "\<And> q . finite (ofsm_table M f' k q)"
    proof -
      fix q 
      have "ofsm_table M (\<lambda>q. f q \<inter> states M) k q \<subseteq> ofsm_table M (\<lambda>q. f q \<inter> states M) 0 q"
        using ofsm_table_subset[of 0 k M "(\<lambda>q. f q \<inter> FSM.states M)" q] by auto
      then have "ofsm_table M f' k q \<subseteq> states M"
        unfolding f'
        using ofsm_table_non_state[of q M "(\<lambda>q. f q \<inter> FSM.states M)" k]
        by force 
      then show "finite (ofsm_table M f' k q)"
        using fsm_states_finite finite_subset by auto 
    qed
    ultimately have "\<And> q . card (ofsm_table M f' (Suc k) q) \<le> card (ofsm_table M f' k q)"
      by (simp add: card_mono)
    then have "(\<Sum>q\<in>FSM.states M - {q}. card (ofsm_table M f' (Suc k) q)) \<le> (\<Sum>q\<in>FSM.states M - {q}. card (ofsm_table M f' k q))"
      by (simp add: sum_mono)
    moreover have "card (ofsm_table M f' (Suc k) q) < card (ofsm_table M f' k q)"
      using \<open>ofsm_table M f' k q \<noteq> ofsm_table M f' (Suc k) q\<close> \<open>ofsm_table M f' (Suc k) q \<subseteq> ofsm_table M f' k q\<close> \<open>finite (ofsm_table M f' k q)\<close>
      by (metis psubsetI psubset_card_mono)    
    ultimately have "(\<Sum>q\<in>FSM.states M. card (ofsm_table M (\<lambda>q. f q \<inter> states M) (Suc k) q)) < (\<Sum>q\<in>FSM.states M. card (ofsm_table M (\<lambda>q. f q \<inter> states M) k q))"
      unfolding f'[symmetric] *
      by linarith 
  } note t = this

  show ?thesis
    apply (relation "measure (\<lambda> (M, f, k) . \<Sum> q \<in> states M . card (ofsm_table M (\<lambda>q. f q \<inter> states M) k q))")
    apply (simp del: h_obs.simps ofsm_table.simps)+
    by (erule t) 
qed


lemma ofsm_table_restriction_to_states :
  assumes "\<And> q . q \<in> states M \<Longrightarrow> f q \<subseteq> states M"
  and     "q \<in> states M"
shows "ofsm_table M f k q = ofsm_table M (\<lambda>q . f q \<inter> states M) k q"
using assms(2) proof (induction k arbitrary: q)
  case 0
  then show ?case using assms(1) by auto
next
  case (Suc k)

  have "\<And> x y q q' . (case h_obs M q x y of None \<Rightarrow> h_obs M q' x y = None | Some qT \<Rightarrow> (case h_obs M q' x y of None \<Rightarrow> False | Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT'))
                      = (case h_obs M q x y of None \<Rightarrow> h_obs M q' x y = None | Some qT \<Rightarrow> (case h_obs M q' x y of None \<Rightarrow> False | Some qT' \<Rightarrow> ofsm_table M (\<lambda>q . f q \<inter> states M) k qT = ofsm_table M (\<lambda>q . f q \<inter> states M) k qT'))"
        (is "\<And> x y q q' . ?C1 x y q q' = ?C2 x y q q' ")
  proof -
    fix x y q q'  
    show "?C1 x y q q' = ?C2 x y q q'"
      using Suc.IH[OF h_obs_state, of q x y]
      using Suc.IH[OF h_obs_state, of q' x y] 
      by (cases "h_obs M q x y"; cases "h_obs M q' x y"; auto)
  qed
  then show ?case
    unfolding ofsm_table.simps Let_def Suc.IH[OF Suc.prems] 
    by blast
qed


lemma ofsm_table_fix_length :
  assumes "\<And> q . q \<in> states M \<Longrightarrow> f q \<subseteq> states M"
  obtains k where "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M f 0 q = ofsm_table M f k q" and "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> k \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f k q"
proof -
  
  have "\<exists> k . \<forall> q \<in> states M . \<forall> k' \<ge> k . ofsm_table M f k' q = ofsm_table M f k q"
  proof -

    have "\<exists> fp . \<forall> q  k' . q \<in> states M \<longrightarrow> k' \<ge> (fp q) \<longrightarrow> ofsm_table M f k' q = ofsm_table M f (fp q) q"
    proof 
      fix q
      let ?assignK = "\<lambda> q . SOME k .  \<forall> k' \<ge> k . ofsm_table M f k' q = ofsm_table M f k q"

      have "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> ?assignK q \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f (?assignK q) q"
      proof -
        fix q k' assume "q \<in> states M" and "k' \<ge> ?assignK q"
        then have p1: "finite (ofsm_table M f 0 q)"
          using fsm_states_finite assms(1)
          using infinite_super by fastforce 
    
        have "\<exists> k . \<forall> k' \<ge> k . ofsm_table M f k' q = ofsm_table M f k q"
          using finite_subset_mapping_limit[of "\<lambda> k . ofsm_table M f k q", OF p1 ofsm_table_subset] by metis
        have "\<forall> k' \<ge> (?assignK q) . ofsm_table M f k' q = ofsm_table M f (?assignK q) q" 
          using someI_ex[of "\<lambda> k . \<forall> k' \<ge> k . ofsm_table M f k' q = ofsm_table M f k q", OF \<open>\<exists> k . \<forall> k' \<ge> k . ofsm_table M f k' q = ofsm_table M f k q\<close>] by assumption
        then show "ofsm_table M f k' q = ofsm_table M f (?assignK q) q" 
          using \<open>k' \<ge> ?assignK q\<close> by blast
      qed
      then show "\<forall>q k'. q \<in> states M \<longrightarrow> ?assignK q \<le> k' \<longrightarrow> ofsm_table M f k' q = ofsm_table M f (?assignK q) q" 
        by blast
    qed
    then obtain assignK where assignK_prop: "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> assignK q \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f (assignK q) q" 
      by blast

    have "finite (assignK ` states M)"
      by (simp add: fsm_states_finite) 
    moreover have "assignK ` FSM.states M \<noteq> {}"
      using fsm_initial by auto
    ultimately obtain k where "k \<in> (assignK ` states M)" and "\<And> k' . k' \<in> (assignK ` states M) \<Longrightarrow> k' \<le> k"
      using Max_elem[OF \<open>finite (assignK ` states M)\<close> \<open>assignK ` FSM.states M \<noteq> {}\<close>] by (meson eq_Max_iff)

    have "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> k \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f k q"
    proof -
      fix q k' assume "k' \<ge> k" and "q \<in> states M"
      then have "k' \<ge> assignK q"
        using \<open>\<And> k' . k' \<in> (assignK ` states M) \<Longrightarrow> k' \<le> k\<close>
        using dual_order.trans by auto 
      then show "ofsm_table M f k' q = ofsm_table M f k q"
        using assignK_prop \<open>\<And>k'. k' \<in> assignK ` FSM.states M \<Longrightarrow> k' \<le> k\<close> \<open>q \<in> FSM.states M\<close> by blast
    qed
    then show ?thesis 
      by blast
  qed
  then obtain k where k_prop: "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> k \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f k q"
    by blast
  then have "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f k q = ofsm_table M f (Suc k) q"
    by (metis (full_types) le_SucI order_refl)

  
  let ?ks = "(Set.filter (\<lambda> k . \<forall> q \<in> states M . ofsm_table M f k q = ofsm_table M f (Suc k) q) {..k})"
  have f1: "finite ?ks"
    by simp
  moreover have f2: "?ks \<noteq> {}"
    using \<open>\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f k q = ofsm_table M f (Suc k) q\<close> unfolding Set.filter_def by blast
  ultimately obtain kMin where "kMin \<in> ?ks" and "\<And> k' . k' \<in> ?ks \<Longrightarrow> k' \<ge> kMin"
    using Min_elem[OF f1 f2] by (meson eq_Min_iff)

  have k1: "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f (Suc kMin) q = ofsm_table M f kMin q"
    using \<open>kMin \<in> ?ks\<close>
    by (metis (mono_tags, lifting) member_filter) 

  have k2: "\<And> k' . (\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f (Suc k') q) \<Longrightarrow> k' \<ge> kMin" 
  proof -
    fix k' assume "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f (Suc k') q"
    show "k' \<ge> kMin" proof (cases "k' \<in> ?ks")
      case True
      then show ?thesis using \<open>\<And> k' . k' \<in> ?ks \<Longrightarrow> k' \<ge> kMin\<close> by blast
    next
      case False
      then have "k' > k"
        using \<open>\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f (Suc k') q\<close> 
        unfolding member_filter atMost_iff
        by (meson not_less) 
      moreover have "kMin \<le> k"
        using \<open>kMin \<in> ?ks\<close> by auto
      ultimately show ?thesis 
        by auto
    qed 
  qed


  have "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M f 0 q = ofsm_table M (\<lambda> q . f q \<inter> states M) kMin q"
  proof -
    fix q assume "q \<in> states M"
    show "ofsm_table_fix M f 0 q = ofsm_table M (\<lambda> q . f q \<inter> states M) kMin q"
    proof (cases kMin)
      case 0

      have "\<forall>q\<in>FSM.states M. ofsm_table M (\<lambda>q. f q \<inter> FSM.states M) 0 q = ofsm_table M (\<lambda>q. f q \<inter> FSM.states M) (Suc 0) q"
        using k1 
        using ofsm_table_restriction_to_states[of M f _, OF assms(1) _ ]
        using "0" by blast 
      then show ?thesis 
        apply (subst ofsm_table_fix.simps)
        unfolding  "0" Let_def by force
    next
      case (Suc kMin')
      
      have *: "\<And> i . i < kMin \<Longrightarrow> \<not>(\<forall> q \<in> states M . ofsm_table M f i q = ofsm_table M f (Suc i) q)"
        using k2
        by (meson leD) 
      have "\<And> i . i < kMin \<Longrightarrow> ofsm_table_fix M f 0 = ofsm_table_fix M f (Suc i)"
      proof -
        fix i assume "i < kMin"
        then show "ofsm_table_fix M f 0 = ofsm_table_fix M f (Suc i)"
        proof (induction i)
          case 0
          show ?case 
            using *[OF 0]  ofsm_table_restriction_to_states[of _ f, OF assms(1) _ ] unfolding ofsm_table_fix.simps[of M f 0] Let_def
            by (metis (no_types, lifting))
        next
          case (Suc i)
          then have "i < kMin" by auto
  
          have "ofsm_table_fix M f (Suc i) = ofsm_table_fix M f (Suc (Suc i))"
            using *[OF \<open>Suc i < kMin\<close>] ofsm_table_restriction_to_states[of _ f, OF assms(1) _ ] unfolding ofsm_table_fix.simps[of M f "Suc i"] Let_def by metis
          then show ?case using Suc.IH[OF \<open>i < kMin\<close>]
            by presburger
        qed
      qed
      then have "ofsm_table_fix M f 0 = ofsm_table_fix M f kMin"
        using Suc by blast
      moreover have "ofsm_table_fix M f kMin q = ofsm_table M f kMin q"
      proof -
        have "\<forall>q\<in>FSM.states M. ofsm_table M (\<lambda>q. f q \<inter> FSM.states M) kMin q = ofsm_table M (\<lambda>q. f q \<inter> FSM.states M) (Suc kMin) q"
          using ofsm_table_restriction_to_states[of _ f, OF assms(1) _ ]
          using k1 by blast
        then show ?thesis
          using ofsm_table_restriction_to_states[of _ f, OF assms(1) _ ] \<open>q \<in> states M\<close>
          unfolding ofsm_table_fix.simps[of M f kMin] Let_def
          by presburger
      qed
      ultimately show ?thesis
        using ofsm_table_restriction_to_states[of _ f, OF assms(1) \<open>q \<in> states M\<close>] 
        by presburger
    qed
  qed
  moreover have "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> kMin \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f kMin q"
    using ofsm_table_fixpoint[OF _ k1 ] by blast
  ultimately show ?thesis 
    using that[of kMin] 
    using ofsm_table_restriction_to_states[of M f, OF assms(1) _ ] 
    by blast
qed

lemma ofsm_table_containment :
  assumes "q \<in> states M"
  and     "\<And> q . q \<in> states M \<Longrightarrow> q \<in> f q"
  shows "q \<in> ofsm_table M f k q"
proof (induction k)
  case 0
  then show ?case using assms by auto  
next
  case (Suc k)
  then show ?case 
    unfolding ofsm_table.simps Let_def option.case_eq_if 
    by auto
qed

lemma ofsm_table_states :
  assumes "\<And> q . q \<in> states M \<Longrightarrow> f q \<subseteq> states M"
  and     "q \<in> states M"
shows  "ofsm_table M f k q \<subseteq> states M" 
proof -
  have "ofsm_table M f k q \<subseteq> ofsm_table M f 0 q"
    using ofsm_table_subset[OF le0] by metis
  moreover have "ofsm_table M f 0 q \<subseteq> states M"
    using assms 
    unfolding ofsm_table.simps(1) by (metis (full_types))
  ultimately show ?thesis 
    by blast
qed


subsubsection \<open>Properties of Initial Partitions\<close>

definition equivalence_relation_on_states :: "('a,'b,'c) fsm \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "equivalence_relation_on_states M f = 
      (equiv (states M) {(q1,q2) | q1 q2 . q1 \<in> states M \<and> q2 \<in> f q1}
       \<and> (\<forall> q \<in> states M . f q \<subseteq> states M))"
  
lemma equivalence_relation_on_states_refl :
  assumes "equivalence_relation_on_states M f"
  and     "q \<in> states M"
shows "q \<in> f q"
  using assms unfolding equivalence_relation_on_states_def equiv_def refl_on_def by blast

lemma equivalence_relation_on_states_sym :
  assumes "equivalence_relation_on_states M f"
  and     "q1 \<in> states M"
  and     "q2 \<in> f q1"
shows "q1 \<in> f q2"
  using assms unfolding equivalence_relation_on_states_def equiv_def sym_def by blast

lemma equivalence_relation_on_states_trans :
  assumes "equivalence_relation_on_states M f"
  and     "q1 \<in> states M"
  and     "q2 \<in> f q1"
  and     "q3 \<in> f q2"
shows "q3 \<in> f q1"
proof -
  have "(q1,q2) \<in> {(q1,q2) | q1 q2 . q1 \<in> states M \<and> q2 \<in> f q1}"
    using assms(2,3) by blast
  then have "q2 \<in> states M" 
    using assms(1) unfolding equivalence_relation_on_states_def
    by auto 
  then have "(q2,q3) \<in> {(q1,q2) | q1 q2 . q1 \<in> states M \<and> q2 \<in> f q1}" 
    using assms(4) by blast
  moreover have "trans {(q1,q2) | q1 q2 . q1 \<in> states M \<and> q2 \<in> f q1}"
    using assms(1) unfolding equivalence_relation_on_states_def equiv_def by auto
  ultimately show ?thesis
    using \<open>(q1,q2) \<in> {(q1,q2) | q1 q2 . q1 \<in> states M \<and> q2 \<in> f q1}\<close>
    unfolding trans_def by blast
qed

lemma equivalence_relation_on_states_ran :
  assumes "equivalence_relation_on_states M f"
  and     "q \<in> states M"
shows "f q \<subseteq> states M"
  using assms unfolding equivalence_relation_on_states_def by blast


subsubsection \<open>Properties of OFSM tables for initial partitions based on equivalence relations\<close>

lemma h_obs_io :
  assumes "h_obs M q x y = Some q'"
  shows "x \<in> inputs M" and "y \<in> outputs M"
proof -
  have "snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)) \<noteq> {}"
    using assms unfolding h_obs_simps Let_def by auto
  then show "x \<in> inputs M" and "y \<in> outputs M"
    unfolding h_simps
    using fsm_transition_input fsm_transition_output
    by fastforce+
qed


lemma ofsm_table_language :
  assumes "q' \<in> ofsm_table M f k q"
  and     "length io \<le> k"
  and     "q \<in> states M"
  and     "equivalence_relation_on_states M f"
shows "is_in_language M q io \<longleftrightarrow> is_in_language M q' io"
and   "is_in_language M q io \<Longrightarrow> (after M q' io) \<in> f (after M q io)"
proof -
  have "(is_in_language M q io \<longleftrightarrow> is_in_language M q' io) \<and> (is_in_language M q io \<longrightarrow> (after M q' io) \<in> f (after M q io))"
    using assms(1,2,3)
  proof (induction k arbitrary: q q' io)
    case 0
    then have "io = []" by auto
    then show ?case 
      using "0.prems"(1,3) by auto
  next
    case (Suc k)

    show ?case proof (cases "length io \<le> k")
      case True
      have *: "q' \<in> ofsm_table M f k q"
        using \<open>q' \<in> ofsm_table M f (Suc k) q\<close> ofsm_table_subset
        by (metis (full_types) le_SucI order_refl subsetD)  
      show ?thesis using Suc.IH[OF * True \<open>q \<in> states M\<close>] by assumption
    next
      case False
      then have "length io = Suc k"
        using \<open>length io \<le> Suc k\<close> by auto
      then obtain ioT ioP where "io = ioT#ioP"
        by (meson length_Suc_conv)
      then have "length ioP \<le> k"
        using \<open>length io \<le> Suc k\<close> by auto

      obtain x y where "io = (x,y)#ioP"
        using \<open>io = ioT#ioP\<close> prod.exhaust_sel
        by fastforce 
        
      have "ofsm_table M f (Suc k) q = {q' \<in> ofsm_table M f k q . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None) }"
        unfolding ofsm_table.simps Let_def by blast
      then have "q' \<in> ofsm_table M f k q"
            and *: "\<And> x y . x \<in> inputs M \<Longrightarrow> y \<in> outputs M \<Longrightarrow> (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
        using \<open>q' \<in> ofsm_table M f (Suc k) q\<close> by blast+
      
      show ?thesis 
        unfolding \<open>io = (x,y)#ioP\<close> 
      proof -
        have "is_in_language M q ((x,y)#ioP) \<Longrightarrow> is_in_language M q' ((x,y)#ioP) \<and> after M q' ((x,y)#ioP) \<in> f (after M q ((x,y)#ioP))"
        proof -
          assume "is_in_language M q ((x,y)#ioP)"

          then obtain qT where "h_obs M q x y = Some qT" and "is_in_language M qT ioP"
            by (metis case_optionE is_in_language.simps(2))
          moreover have "(case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
            using *[of x y, OF h_obs_io[OF \<open>h_obs M q x y = Some qT\<close>]] .
          ultimately obtain qT' where "h_obs M q' x y = Some qT'" and "ofsm_table M f k qT = ofsm_table M f k qT'"
            using ofsm_table_case_helper[of M q' x y f k q] 
            unfolding ofsm_table.simps by force
          then have "qT' \<in> ofsm_table M f k qT"
            using ofsm_table_containment[OF h_obs_state equivalence_relation_on_states_refl[OF \<open>equivalence_relation_on_states M f\<close>]]
            by metis 

          have "(is_in_language M qT ioP) = (is_in_language M qT' ioP)" 
               "(is_in_language M qT ioP \<longrightarrow> after M qT' ioP \<in> f (after M qT ioP))"
            using Suc.IH[OF \<open>qT' \<in> ofsm_table M f k qT\<close> \<open>length ioP \<le> k\<close> h_obs_state[OF \<open>h_obs M q x y = Some qT\<close>]]
            by blast+

          have "(is_in_language M qT' ioP)"
            using \<open>(is_in_language M qT ioP) = (is_in_language M qT' ioP)\<close> \<open>is_in_language M qT ioP\<close>
            by auto
          then have "is_in_language M q' ((x,y)#ioP)"
            unfolding is_in_language.simps \<open>h_obs M q' x y = Some qT'\<close> by auto
          moreover have "after M q' ((x,y)#ioP) \<in> f (after M q ((x,y)#ioP))"
            unfolding after.simps \<open>h_obs M q' x y = Some qT'\<close> \<open>h_obs M q x y = Some qT\<close>
            using \<open>(is_in_language M qT ioP \<longrightarrow> after M qT' ioP \<in> f (after M qT ioP))\<close> \<open>is_in_language M qT ioP\<close>
            by auto
          ultimately show "is_in_language M q' ((x,y)#ioP) \<and> after M q' ((x,y)#ioP) \<in> f (after M q ((x,y)#ioP))"
            by blast
        qed
        moreover have "is_in_language M q' ((x,y)#ioP) \<Longrightarrow> is_in_language M q ((x,y)#ioP)"
        proof -
          assume "is_in_language M q' ((x,y)#ioP)"

          then obtain qT' where "h_obs M q' x y = Some qT'" and "is_in_language M qT' ioP"
            by (metis case_optionE is_in_language.simps(2))
          moreover have "(case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
            using *[of x y, OF h_obs_io[OF \<open>h_obs M q' x y = Some qT'\<close>]] .
          ultimately obtain qT where "h_obs M q x y = Some qT" and "ofsm_table M f k qT = ofsm_table M f k qT'"
            using ofsm_table_case_helper[of M q' x y f k q] 
            unfolding ofsm_table.simps by force
          then have "qT \<in> ofsm_table M f k qT'"
            using ofsm_table_containment[OF h_obs_state equivalence_relation_on_states_refl[OF \<open>equivalence_relation_on_states M f\<close>]] 
            by metis

          have "(is_in_language M qT ioP) = (is_in_language M qT' ioP)" 
            using Suc.IH[OF \<open>qT \<in> ofsm_table M f k qT'\<close> \<open>length ioP \<le> k\<close> h_obs_state[OF \<open>h_obs M q' x y = Some qT'\<close>]]
            by blast
          then have "is_in_language M qT ioP"
            using \<open>is_in_language M qT' ioP\<close>
            by auto
          then show "is_in_language M q ((x,y)#ioP)"
            unfolding is_in_language.simps \<open>h_obs M q x y = Some qT\<close> by auto
        qed
        ultimately show "is_in_language M q ((x, y) # ioP) = is_in_language M q' ((x, y) # ioP) \<and> (is_in_language M q ((x, y) # ioP) \<longrightarrow> after M q' ((x, y) # ioP) \<in> f (after M q ((x, y) # ioP)))"
          by blast
      qed
    qed
  qed
  then show "is_in_language M q io = is_in_language M q' io" and "(is_in_language M q io \<Longrightarrow> after M q' io \<in> f (after M q io))"
    by blast+
qed



lemma after_is_state_is_in_language :
  assumes "q \<in> states M"
  and     "is_in_language M q io"
  shows "FSM.after M q io \<in> states M" 
  using assms
proof (induction io arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a io)
  then obtain x y where "a = (x,y)" using prod.exhaust by metis
  show ?case 
    using \<open>is_in_language M q (a # io)\<close> Cons.IH[OF h_obs_state[of M q x y]]
    unfolding \<open>a = (x,y)\<close> 
    unfolding after.simps is_in_language.simps
    by (metis option.case_eq_if option.exhaust_sel) 
qed


lemma ofsm_table_elem :
  assumes "q \<in> states M"
  and     "q' \<in> states M"
  and     "equivalence_relation_on_states M f"
  and     "\<And> io . length io \<le> k \<Longrightarrow> is_in_language M q io \<longleftrightarrow> is_in_language M q' io"
  and     "\<And> io . length io \<le> k \<Longrightarrow> is_in_language M q io \<Longrightarrow> (after M q' io) \<in> f (after M q io)"
shows "q' \<in> ofsm_table M f k q"
  using assms(1,2,4,5) proof (induction k arbitrary: q q')
  case 0
  then show ?case by auto
next
  case (Suc k)
  
  have "q' \<in> ofsm_table M f k q"
    using Suc.IH[OF Suc.prems(1,2)] Suc.prems(3,4) by auto

  moreover have "\<And> x y . x \<in> inputs M \<Longrightarrow> y \<in> outputs M \<Longrightarrow> (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
  proof -
    fix x y assume "x \<in> inputs M" and "y \<in> outputs M"
    show "(case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
    proof (cases "\<exists> qT qT' . h_obs M q x y = Some qT \<and> h_obs M q' x y = Some qT'")
      case True
      then obtain qT qT' where "h_obs M q x y = Some qT" and "h_obs M q' x y = Some qT'"
        by blast

      have *: "\<And> io . length io \<le> k \<Longrightarrow> is_in_language M qT io = is_in_language M qT' io"
      proof -
        fix io :: "('b \<times> 'c) list " 
        assume "length io \<le> k"

        have "is_in_language M qT io = is_in_language M q ([(x,y)]@io)"
          using \<open>h_obs M q x y = Some qT\<close> by auto
        moreover have "is_in_language M qT' io = is_in_language M q' ([(x,y)]@io)"
          using \<open>h_obs M q' x y = Some qT'\<close> by auto
        ultimately show "is_in_language M qT io = is_in_language M qT' io" 
          using Suc.prems(3) \<open>length io \<le> k\<close>
          by (metis append.left_neutral append_Cons length_Cons not_less_eq_eq)
      qed

      have "ofsm_table M f k qT = ofsm_table M f k qT'"
      proof 

        have "qT \<in> states M"
          using h_obs_state[OF \<open>h_obs M q x y = Some qT\<close>] .          
        have "qT' \<in> states M"
          using h_obs_state[OF \<open>h_obs M q' x y = Some qT'\<close>] .

        show "ofsm_table M f k qT \<subseteq> ofsm_table M f k qT'"
        proof 
          fix s assume "s \<in> ofsm_table M f k qT"
          then have "s \<in> states M"
            using ofsm_table_subset[of 0 k M f qT] equivalence_relation_on_states_ran[OF assms(3) \<open>qT \<in> states M\<close>] \<open>qT \<in> states M\<close> by auto
          have **: "(\<And>io. length io \<le> k \<Longrightarrow> is_in_language M qT' io = is_in_language M s io)"
            using ofsm_table_language(1)[OF \<open>s \<in> ofsm_table M f k qT\<close> _ \<open>qT\<in> states M\<close> assms(3)] * by blast
          have ***: "(\<And>io. length io \<le> k \<Longrightarrow> is_in_language M qT' io \<Longrightarrow> after M s io \<in> f (after M qT' io))"
          proof -
            fix io assume "length io \<le> k" and "is_in_language M qT' io"
            then have "is_in_language M qT io"
              using * by blast
            then have "after M s io \<in> f (after M qT io)"
              using ofsm_table_language(2)[OF \<open>s \<in> ofsm_table M f k qT\<close> \<open>length io \<le> k\<close> \<open>qT\<in> states M\<close> assms(3)]
              by blast
            
            have "after M qT io = after M q ((x,y)#io)"
              using \<open>h_obs M q x y = Some qT\<close> by auto
            moreover have "after M qT' io = after M q' ((x,y)#io)"
              using \<open>h_obs M q' x y = Some qT'\<close> by auto
            moreover have "is_in_language M q ((x,y)#io)"
              using \<open>h_obs M q x y = Some qT\<close> \<open>is_in_language M qT io\<close> by auto
            ultimately have "after M qT' io \<in> f (after M qT io)"
              using Suc.prems(4) \<open>length io \<le> k\<close>
              by (metis Suc_le_mono length_Cons) 
            
            show "after M s io \<in> f (after M qT' io)"
              using equivalence_relation_on_states_trans[OF \<open>equivalence_relation_on_states M f\<close> after_is_state_is_in_language[OF \<open>qT' \<in> states M\<close> \<open>is_in_language M qT' io\<close>]
                                                            equivalence_relation_on_states_sym[OF \<open>equivalence_relation_on_states M f\<close>  after_is_state_is_in_language[OF \<open>qT \<in> states M\<close> \<open>is_in_language M qT io\<close>] 
                                                            \<open>after M qT' io \<in> f (after M qT io)\<close>] \<open>after M s io \<in> f (after M qT io)\<close>] .
          qed
          show "s \<in> ofsm_table M f k qT'"
            using Suc.IH[OF \<open>qT' \<in> states M\<close> \<open>s \<in> states M\<close> ** ***] by blast            
        qed

        show "ofsm_table M f k qT' \<subseteq> ofsm_table M f k qT"
        proof 
          fix s assume "s \<in> ofsm_table M f k qT'"
          then have "s \<in> states M"
            using ofsm_table_subset[of 0 k M f qT'] equivalence_relation_on_states_ran[OF assms(3) \<open>qT' \<in> states M\<close>] \<open>qT' \<in> states M\<close> by auto
          have **: "(\<And>io. length io \<le> k \<Longrightarrow> is_in_language M qT io = is_in_language M s io)"
            using ofsm_table_language(1)[OF \<open>s \<in> ofsm_table M f k qT'\<close> _ \<open>qT'\<in> states M\<close> assms(3)] * by blast
          have ***: "(\<And>io. length io \<le> k \<Longrightarrow> is_in_language M qT io \<Longrightarrow> after M s io \<in> f (after M qT io))"
          proof -
            fix io assume "length io \<le> k" and "is_in_language M qT io"
            then have "is_in_language M qT' io"
              using * by blast
            then have "after M s io \<in> f (after M qT' io)"
              using ofsm_table_language(2)[OF \<open>s \<in> ofsm_table M f k qT'\<close> \<open>length io \<le> k\<close> \<open>qT'\<in> states M\<close> assms(3)]
              by blast
            
            have "after M qT' io = after M q' ((x,y)#io)"
              using \<open>h_obs M q' x y = Some qT'\<close> by auto
            moreover have "after M qT io = after M q ((x,y)#io)"
              using \<open>h_obs M q x y = Some qT\<close> by auto
            moreover have "is_in_language M q' ((x,y)#io)"
              using \<open>h_obs M q' x y = Some qT'\<close> \<open>is_in_language M qT' io\<close> by auto
            ultimately have "after M qT io \<in> f (after M qT' io)"
              using Suc.prems(4) \<open>length io \<le> k\<close>
              by (metis Suc.prems(3) Suc_le_mono \<open>is_in_language M qT io\<close> \<open>qT \<in> FSM.states M\<close> after_is_state_is_in_language assms(3) equivalence_relation_on_states_sym length_Cons)
            
            show "after M s io \<in> f (after M qT io)"
              using equivalence_relation_on_states_trans[OF \<open>equivalence_relation_on_states M f\<close> after_is_state_is_in_language[OF \<open>qT \<in> states M\<close> \<open>is_in_language M qT io\<close>]
                                                            equivalence_relation_on_states_sym[OF \<open>equivalence_relation_on_states M f\<close>  after_is_state_is_in_language[OF \<open>qT' \<in> states M\<close> \<open>is_in_language M qT' io\<close>] 
                                                            \<open>after M qT io \<in> f (after M qT' io)\<close>] \<open>after M s io \<in> f (after M qT' io)\<close>] .
          qed
          show "s \<in> ofsm_table M f k qT"
            using Suc.IH[OF \<open>qT \<in> states M\<close> \<open>s \<in> states M\<close> ** ***] by blast            
        qed
      qed
      then show ?thesis
        unfolding \<open>h_obs M q x y = Some qT\<close> \<open>h_obs M q' x y = Some qT'\<close>
        by auto
    next
      case False
      have "h_obs M q x y = None \<and> h_obs M q' x y = None"
      proof (rule ccontr)  
        assume "\<not> (h_obs M q x y = None \<and> h_obs M q' x y = None)"
        then have "is_in_language M q [(x,y)] \<or> is_in_language M q' [(x,y)]"
          unfolding is_in_language.simps
          using option.disc_eq_case(2) by blast 
        moreover have "is_in_language M q [(x,y)] \<noteq> is_in_language M q' [(x,y)]"
          using False
          by (metis calculation case_optionE is_in_language.simps(2))
        moreover have "length [(x,y)] \<le> Suc k"
          by auto
        ultimately show False
          using Suc.prems(3) by blast
      qed
      then show ?thesis
        unfolding ofsm_table_case_helper
        by blast
    qed
  qed
  
  ultimately show ?case
    unfolding Suc ofsm_table.simps Let_def by force
qed


lemma ofsm_table_set :
  assumes "q \<in> states M"
  and     "equivalence_relation_on_states M f"
shows "ofsm_table M f k q = {q' . q' \<in> states M \<and> (\<forall> io . length io \<le> k \<longrightarrow> (is_in_language M q io \<longleftrightarrow> is_in_language M q' io) \<and> (is_in_language M q io \<longrightarrow> after M q' io \<in> f (after M q io)))}"
  using ofsm_table_language[OF _ _ assms(1,2) ] 
        ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(2)] assms(1)]
        ofsm_table_elem[OF assms(1) _ assms(2)]
  by blast

lemma ofsm_table_set_observable :
  assumes "observable M" and "q \<in> states M"
  and     "equivalence_relation_on_states M f"
shows "ofsm_table M f k q = {q' . q' \<in> states M \<and> (\<forall> io . length io \<le> k \<longrightarrow> (io \<in> LS M q \<longleftrightarrow> io \<in> LS M q') \<and> (io \<in> LS M q \<longrightarrow> after M q' io \<in> f (after M q io)))}"
  unfolding ofsm_table_set[OF assms(2,3)]
  unfolding is_in_language_iff[OF assms(1,2)]
  using is_in_language_iff[OF assms(1)]
  by blast 


lemma ofsm_table_eq_if_elem :
  assumes "q1 \<in> states M" and "q2 \<in> states M" and "equivalence_relation_on_states M f" 
  shows "(ofsm_table M f k q1 = ofsm_table M f k q2) = (q2 \<in> ofsm_table M f k q1)"
proof 
  show "ofsm_table M f k q1 = ofsm_table M f k q2 \<Longrightarrow> q2 \<in> ofsm_table M f k q1"
    using ofsm_table_containment[OF assms(2) equivalence_relation_on_states_refl[OF \<open>equivalence_relation_on_states M f\<close>]]
    by blast

  show "q2 \<in> ofsm_table M f k q1 \<Longrightarrow> ofsm_table M f k q1 = ofsm_table M f k q2"
  proof -
    assume *: "q2 \<in> ofsm_table M f k q1"

    have "ofsm_table M f k q1 = {q' \<in> FSM.states M. \<forall>io. length io \<le> k \<longrightarrow> (is_in_language M q1 io) = (is_in_language M q' io) \<and> (is_in_language M q1 io \<longrightarrow> after M q' io \<in> f (after M q1 io))}"
      using ofsm_table_set[OF assms(1,3)] by auto

    moreover have "ofsm_table M f k q2 = {q' \<in> FSM.states M. \<forall>io. length io \<le> k \<longrightarrow> (is_in_language M q1 io) = (is_in_language M q' io) \<and> (is_in_language M q1 io \<longrightarrow> after M q' io \<in> f (after M q1 io))}"
    proof -
      have "ofsm_table M f k q2 = {q' \<in> FSM.states M. \<forall>io. length io \<le> k \<longrightarrow> (is_in_language M q2 io) = (is_in_language M q' io) \<and> (is_in_language M q2 io \<longrightarrow> after M q' io \<in> f (after M q2 io))}"
        using ofsm_table_set[OF assms(2,3)] by auto  
      moreover have "\<And> io . length io \<le> k \<Longrightarrow> (is_in_language M q1 io) = (is_in_language M q2 io)"
        using ofsm_table_language(1)[OF * _ assms(1,3)] by blast
      moreover have "\<And> io q' . q' \<in> states M \<Longrightarrow> length io \<le> k \<Longrightarrow> (is_in_language M q2 io \<longrightarrow> after M q' io \<in> f (after M q2 io)) = (is_in_language M q1 io \<longrightarrow> after M q' io \<in> f (after M q1 io))"
        using ofsm_table_language(2)[OF * _ assms(1,3)]
        by (meson after_is_state_is_in_language assms(1) assms(2) assms(3) calculation(2) equivalence_relation_on_states_sym equivalence_relation_on_states_trans)
      ultimately show ?thesis
        by blast
    qed
    ultimately show ?thesis 
      by blast
  qed
qed



lemma ofsm_table_fix_language :
  fixes M :: "('a,'b,'c) fsm"
  assumes "q' \<in> ofsm_table_fix M f 0 q"
  and     "q \<in> states M"
  and     "observable M"
  and     "equivalence_relation_on_states M f"
shows "LS M q = LS M q'"
and   "io \<in> LS M q \<Longrightarrow> after M q' io \<in> f (after M q io)"
proof -

  obtain k where *:"\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M f 0 q = ofsm_table M f k q" 
             and **: "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> k \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f k q"
    using ofsm_table_fix_length[of M f,OF  equivalence_relation_on_states_ran[OF assms(4)]]  
    by blast

  have "q' \<in> ofsm_table M f k q"
    using * assms(1,2) by blast
  then have "q' \<in> states M"
    by (metis assms(2) assms(4) equivalence_relation_on_states_ran le0 ofsm_table.simps(1) ofsm_table_subset subset_iff)    
  
  have "\<And> k' . q' \<in> ofsm_table M f k' q"
  proof -
    fix k' show "q' \<in> ofsm_table M f k' q"
    proof (cases "k' \<le> k")
      case True
      show ?thesis using ofsm_table_subset[OF True, of M f q] \<open>q' \<in> ofsm_table M f k q\<close> by blast
    next
      case False
      then have "k \<le> k'"
        by auto
      show ?thesis 
        unfolding **[OF assms(2) \<open>k \<le> k'\<close>]
        using \<open>q' \<in> ofsm_table M f k q\<close> by assumption
    qed
  qed  
  
  have "\<And> io . io \<in> LS M q \<longleftrightarrow> io \<in> LS M q'"
  proof -
    fix io :: "('b \<times> 'c) list"
    show "io \<in> LS M q \<longleftrightarrow> io \<in> LS M q'"
      using ofsm_table_language(1)[OF \<open>q' \<in> ofsm_table M f (length io) q\<close> _ assms(2,4), of io] 
      using is_in_language_iff[OF assms(3,2)] is_in_language_iff[OF assms(3) \<open>q' \<in> states M\<close>]
      by blast
  qed
  then show "LS M q = LS M q'" 
    by blast

  show "io \<in> LS M q \<Longrightarrow> after M q' io \<in> f (after M q io)"
    using ofsm_table_language(2)[OF \<open>q' \<in> ofsm_table M f (length io) q\<close> _ assms(2,4), of io] 
    using is_in_language_iff[OF assms(3,2)] is_in_language_iff[OF assms(3) \<open>q' \<in> states M\<close>]
    by blast
qed




lemma ofsm_table_same_language :
  assumes "LS M q = LS M q'"
  and     "\<And> io . io \<in> LS M q \<Longrightarrow> after M q' io \<in> f (after M q io)"
  and     "observable M"
  and     "q' \<in> states M"
  and     "q \<in> states M"
  and     "equivalence_relation_on_states M f"
shows "ofsm_table M f k q = ofsm_table M f k q'"
  using assms(1,2,4,5) 
proof (induction k arbitrary: q q')
  case 0
  then show ?case
    by (metis after.simps(1) assms(6) from_FSM_language language_contains_empty_sequence ofsm_table.simps(1) ofsm_table_eq_if_elem)
next
  case (Suc k)
  
  have "ofsm_table M f (Suc k) q = {q'' \<in> ofsm_table M f k q' . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None) }"
    using Suc.IH[OF Suc.prems] unfolding ofsm_table.simps Suc Let_def Suc by simp
  
  moreover have "ofsm_table M f (Suc k) q'  = {q'' \<in> ofsm_table M f k q' . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q' x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None) }"
    unfolding ofsm_table.simps Suc Let_def 
    by auto

  moreover have "{q'' \<in> ofsm_table M f k q' . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None) }
        = {q'' \<in> ofsm_table M f k q' . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (case h_obs M q' x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None) }"
  proof -
    have "\<And> q'' x y . q'' \<in> ofsm_table M f k q' \<Longrightarrow> x \<in> inputs M \<Longrightarrow> y \<in> outputs M \<Longrightarrow> 
                    (case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None)
                    = (case h_obs M q' x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None)"
    proof -

      fix q'' x y assume "q'' \<in> ofsm_table M f k q'" and "x \<in> inputs M" and "y \<in> outputs M"

      have *:"(\<exists> qT . h_obs M q x y = Some qT) = (\<exists> qT' . h_obs M q' x y = Some qT')"
      proof -
        have "([(x,y)] \<in> LS M q) = ([(x,y)] \<in> LS M q')"
          using \<open>LS M q = LS M q'\<close> by auto
        then have "(\<exists> qT . (q, x, y, qT) \<in> FSM.transitions M) = (\<exists> qT' . (q', x, y, qT') \<in> FSM.transitions M)"
          unfolding LS_single_transition by force
        then show "(\<exists> qT . h_obs M q x y = Some qT) = (\<exists> qT' . h_obs M q' x y = Some qT')"
          unfolding h_obs_Some[OF \<open>observable M\<close>] using \<open>observable M\<close> unfolding observable_alt_def by blast
      qed

      have **: "(case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q' x y = None)"
      proof (cases "h_obs M q x y")
        case None
        then show ?thesis using * by auto
      next
        case (Some qT)
        show ?thesis proof (cases "h_obs M q' x y")
          case None
          then show ?thesis using * by auto
        next
          case (Some qT')

          have "(q,x,y,qT) \<in> transitions M"
            using \<open>h_obs M q x y = Some qT\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] by blast
          have "(q',x,y,qT') \<in> transitions M"
            using \<open>h_obs M q' x y = Some qT'\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] by blast


          have "LS M qT = LS M qT'"
            using observable_transition_target_language_eq[OF _ \<open>(q,x,y,qT) \<in> transitions M\<close> \<open>(q',x,y,qT') \<in> transitions M\<close> _ _ \<open>observable M\<close>]
                  \<open>LS M q = LS M q'\<close> 
            by auto
          moreover have "(\<And>io. io \<in> LS M qT \<Longrightarrow> after M qT' io \<in> f (after M qT io))"
          proof -
            fix io assume "io \<in> LS M qT"
            
            have "io \<in> LS M qT'"
              using \<open>io \<in> LS M qT\<close> calculation by auto

            have "after M qT io = after M q ((x,y)#io)"
              using after_h_obs_prepend[OF \<open>observable M\<close> \<open>h_obs M q x y = Some qT\<close> \<open>io \<in> LS M qT\<close>]
              by simp
            moreover have "after M qT' io = after M q' ((x,y)#io)"
              using after_h_obs_prepend[OF \<open>observable M\<close> \<open>h_obs M q' x y = Some qT'\<close> \<open>io \<in> LS M qT'\<close>]
              by simp
            moreover have "(x,y)#io \<in> LS M q"
              using \<open>h_obs M q x y = Some qT\<close> \<open>io \<in> LS M qT\<close> unfolding h_obs_language_iff[OF \<open>observable M\<close>] 
              by blast
            ultimately show "after M qT' io \<in> f (after M qT io)"
              using Suc.prems(2) by presburger
          qed

          ultimately have "ofsm_table M f k qT = ofsm_table M f k qT'"
            using Suc.IH[OF _ _ fsm_transition_target[OF \<open>(q',x,y,qT') \<in> transitions M\<close>] fsm_transition_target[OF \<open>(q,x,y,qT) \<in> transitions M\<close>]] 
            unfolding snd_conv 
            by blast
          then show ?thesis 
            using \<open>h_obs M q x y = Some qT\<close> \<open>h_obs M q' x y = Some qT'\<close> by auto
        qed
      qed
      
      

      show "(case h_obs M q x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None)
                    = (case h_obs M q' x y of Some qT \<Rightarrow> (case h_obs M q'' x y of Some qT' \<Rightarrow> ofsm_table M f k qT = ofsm_table M f k qT' | None \<Rightarrow> False) | None \<Rightarrow> h_obs M q'' x y = None)" (is "?P")

      proof (cases "h_obs M q x y")
        case None
        then have "h_obs M q' x y = None"
          using * by auto
        show ?thesis unfolding None \<open>h_obs M q' x y = None\<close> by auto
      next
        case (Some qT)
        then obtain qT' where "h_obs M q' x y = Some qT'"
          using \<open>(\<exists> qT . h_obs M q x y = Some qT) = (\<exists> qT' . h_obs M q' x y = Some qT')\<close> by auto
        
        show ?thesis 
        proof (cases "h_obs M q'' x y")
          case None
          then show ?thesis using *
            by (metis Some option.case_eq_if option.simps(5)) 
        next
          case (Some qT'')
          show ?thesis 
            using **
            unfolding Some \<open>h_obs M q x y = Some qT\<close> \<open>h_obs M q' x y = Some qT'\<close> by auto
        qed
      qed
    qed

    then show ?thesis
      by blast 
  qed

  ultimately show ?case by blast
qed


lemma ofsm_table_fix_set :
  assumes "q \<in> states M"
  and     "observable M"
  and     "equivalence_relation_on_states M f"
shows "ofsm_table_fix M f 0 q = {q' \<in> states M . LS M q' = LS M q \<and> (\<forall> io \<in> LS M q . after M q' io \<in> f (after M q io))}"
proof 

  have "ofsm_table_fix M f 0 q \<subseteq> ofsm_table M f 0 q"
    using ofsm_table_fix_length[of M f]
          ofsm_table_subset[OF zero_le, of M f _ q]
    by (metis assms(1) assms(3) equivalence_relation_on_states_ran)
  then have "ofsm_table_fix M f 0 q \<subseteq> states M"
    using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(3)] assms(1)] by blast
  then show "ofsm_table_fix M f 0 q \<subseteq> {q' \<in> states M . LS M q' = LS M q \<and> (\<forall> io \<in> LS M q . after M q' io \<in> f (after M q io))}"
    using ofsm_table_fix_language[OF _ assms] by blast

  show "{q' \<in> states M . LS M q' = LS M q \<and> (\<forall> io \<in> LS M q . after M q' io \<in> f (after M q io))} \<subseteq> ofsm_table_fix M f 0 q"
  proof 
    fix q' assume "q' \<in> {q' \<in> states M . LS M q' = LS M q \<and> (\<forall> io \<in> LS M q . after M q' io \<in> f (after M q io))}"
    then have "q' \<in> states M" and "LS M q' = LS M q" and "\<And> io .  io \<in> LS M q \<Longrightarrow> after M q' io \<in> f (after M q io)"
      by blast+

    then have "\<And> io .  io \<in> LS M q' \<Longrightarrow> after M q io \<in> f (after M q' io)"
      by (metis after_is_state assms(2) assms(3) equivalence_relation_on_states_sym) 

    obtain k where "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M f 0 q = ofsm_table M f k q" 
               and "\<And> q k' . q \<in> states M \<Longrightarrow> k' \<ge> k \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f k q"
      using ofsm_table_fix_length[of M f, OF equivalence_relation_on_states_ran[OF assms(3)]] by blast
    
    have "ofsm_table M f k q' = ofsm_table M f k q"
      using ofsm_table_same_language[OF \<open>LS M q' = LS M q\<close> \<open>\<And> io .  io \<in> LS M q' \<Longrightarrow> after M q io \<in> f (after M q' io)\<close> assms(2,1) \<open>q' \<in> states M\<close> assms(3)] 
      by blast
    then show "q' \<in> ofsm_table_fix M f 0 q"
      using ofsm_table_containment[OF \<open>q' \<in> states M\<close>, of f k]
      using \<open>\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M f 0 q = ofsm_table M f k q\<close>
      by (metis assms(1) assms(3) equivalence_relation_on_states_refl)
  qed
qed

lemma ofsm_table_fix_eq_if_elem :
  assumes "q1 \<in> states M" and "q2 \<in> states M" 
  and     "equivalence_relation_on_states M f"
  shows "(ofsm_table_fix M f 0 q1 = ofsm_table_fix M f 0 q2) = (q2 \<in> ofsm_table_fix M f 0 q1)"
proof 
  have "(\<And>q. q \<in> FSM.states M \<Longrightarrow> q \<in> f q)"
    using assms(3)
    by (meson equivalence_relation_on_states_refl) 

  show "ofsm_table_fix M f 0 q1 = ofsm_table_fix M f 0 q2 \<Longrightarrow> q2 \<in> ofsm_table_fix M f 0 q1" 
    using ofsm_table_containment[of _ M f, OF assms(2) \<open>(\<And>q. q \<in> FSM.states M \<Longrightarrow> q \<in> f q)\<close>]
    using ofsm_table_fix_length[of M f]
    by (metis assms(2) assms(3) equivalence_relation_on_states_ran)

  show "q2 \<in> ofsm_table_fix M f 0 q1 \<Longrightarrow> ofsm_table_fix M f 0 q1 = ofsm_table_fix M f 0 q2"
    using ofsm_table_eq_if_elem[OF assms(1,2,3)] 
    using ofsm_table_fix_length[of M f]
    by (metis assms(1) assms(2) assms(3) equivalence_relation_on_states_ran)    
qed




lemma ofsm_table_refinement_disjoint :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  and     "equivalence_relation_on_states M f"
  and     "ofsm_table M f k q1 \<noteq> ofsm_table M f k q2"
shows "ofsm_table M f (Suc k) q1 \<noteq> ofsm_table M f (Suc k) q2"
proof -
  have "ofsm_table M f (Suc k) q1 \<subseteq> ofsm_table M f k q1"
  and  "ofsm_table M f (Suc k) q2 \<subseteq> ofsm_table M f k q2"
    using ofsm_table_subset[of k "Suc k" M f] 
    by fastforce+
  moreover have "ofsm_table M f k q1 \<inter> ofsm_table M f k q2 = {}"
  proof (rule ccontr)
    assume "ofsm_table M f k q1 \<inter> ofsm_table M f k q2 \<noteq> {}"
    then obtain q where "q \<in> ofsm_table M f k q1"
                    and "q \<in> ofsm_table M f k q2"
      by blast
    then have "q \<in> states M"
      using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(3)] assms(1)] 
      by blast
    
    have "ofsm_table M f k q1 = ofsm_table M f k q2"
      using \<open>q \<in> ofsm_table M f k q1\<close> \<open>q \<in> ofsm_table M f k q2\<close>
      unfolding ofsm_table_eq_if_elem[OF assms(1) \<open>q \<in> states M\<close> assms(3), symmetric]
      unfolding ofsm_table_eq_if_elem[OF assms(2) \<open>q \<in> states M\<close> assms(3), symmetric]
      by blast
    then show False
      using assms(4) by simp
  qed
  ultimately show ?thesis
    by (metis Int_subset_iff all_not_in_conv assms(2) assms(3) ofsm_table_eq_if_elem subset_empty) 
qed

lemma ofsm_table_partition_finite :
  assumes "equivalence_relation_on_states M f"
shows "finite (ofsm_table M f k ` states M)"
  using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms]] 
        fsm_states_finite[of M] 
  unfolding finite_Pow_iff[of "states M", symmetric]
  by simp


lemma ofsm_table_refinement_card :
  assumes "equivalence_relation_on_states M f"
  and     "A \<subseteq> states M"
  and     "i \<le> j"
shows "card (ofsm_table M f j ` A) \<ge> card (ofsm_table M f i ` A)" 
proof -
  have "\<And> k . card (ofsm_table M f (Suc k) ` A) \<ge> card (ofsm_table M f k ` A)"
  proof -
    fix k show "card (ofsm_table M f (Suc k) ` A) \<ge> card (ofsm_table M f k ` A)"
    proof (rule ccontr)
    
      have "finite A"
        using fsm_states_finite[of M] assms(2)
        using finite_subset by blast 
    
      assume "\<not> card (ofsm_table M f k ` A) \<le> card (ofsm_table M f (Suc k) ` A)"
      then have "card (ofsm_table M f (Suc k) ` A) < card (ofsm_table M f k ` A)"
        by simp
      then obtain q1 q2 where "q1 \<in> A"
                          and "q2 \<in> A"
                          and "ofsm_table M f k q1 \<noteq> ofsm_table M f k q2"
                          and "ofsm_table M f (Suc k) q1 = ofsm_table M f (Suc k) q2"
        using finite_card_less_witnesses[OF \<open>finite A\<close>] by blast
      then show False
        using ofsm_table_refinement_disjoint[OF _ _ assms(1), of q1 q2 k]
        using assms(2)
        by blast
    qed
  qed
  then show ?thesis
    using lift_Suc_mono_le[OF _ assms(3), where f="\<lambda> k . card (ofsm_table M f k ` A)"]
    by blast
qed    

    

lemma ofsm_table_refinement_card_fix_Suc :
  assumes "equivalence_relation_on_states M f"
  and     "card (ofsm_table M f (Suc k) ` states M) = card (ofsm_table M f k ` states M)" 
  and     "q \<in> states M"
shows "ofsm_table M f (Suc k) q = ofsm_table M f k q"
proof (rule ccontr) 
  assume "ofsm_table M f (Suc k) q \<noteq> ofsm_table M f k q"
  then have "ofsm_table M f (Suc k) q \<subset> ofsm_table M f k q"
    using ofsm_table_subset
    by (metis Suc_leD order_refl psubsetI)
  then obtain q' where "q' \<in> ofsm_table M f k q"
                   and "q' \<notin> ofsm_table M f (Suc k) q"
    by blast

  then have "q' \<in> states M"
    using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(1)] assms(3)]  by blast

  have card_qq: "\<And> k . card (ofsm_table M f k ` states M) 
          = card (ofsm_table M f k ` (states M - \<Union>(ofsm_table M f k ` {q,q'}))) + card (ofsm_table M f k ` (\<Union>(ofsm_table M f k ` {q,q'})))"
  proof -
    fix k 
    have "states M = (states M - \<Union>(ofsm_table M f k ` {q,q'})) \<union> \<Union>(ofsm_table M f k ` {q,q'})"
      using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(1)] \<open>q \<in> states M\<close>]
      using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(1)] \<open>q' \<in> states M\<close>]
      by blast
    then have "finite (states M - \<Union>(ofsm_table M f k ` {q,q'}))" 
         and  "finite (\<Union>(ofsm_table M f k ` {q,q'}))"
      using fsm_states_finite[of M] finite_Un[of "(states M - \<Union>(ofsm_table M f k ` {q,q'}))" "\<Union>(ofsm_table M f k ` {q,q'})"] 
      by force+    
    then have *:"finite (ofsm_table M f k ` (states M - \<Union>(ofsm_table M f k ` {q,q'})))" 
         and  **:"finite (ofsm_table M f k ` \<Union>(ofsm_table M f k ` {q,q'}))"
      by blast+
    have ***:"(ofsm_table M f k ` (states M - \<Union>(ofsm_table M f k ` {q,q'}))) \<inter> (ofsm_table M f k ` \<Union>(ofsm_table M f k ` {q,q'})) = {}"
    proof (rule ccontr)
      assume "ofsm_table M f k ` (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'})) \<inter> ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'}) \<noteq> {}"
      then obtain Q where "Q \<in> ofsm_table M f k ` (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'}))"
                      and "Q \<in> ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'})"
        by blast

      obtain q1 where "q1 \<in> (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'}))"
                  and "Q = ofsm_table M f k q1"
        using \<open>Q \<in> ofsm_table M f k ` (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'}))\<close> by blast
      moreover obtain q2 where "q2 \<in> \<Union> (ofsm_table M f k ` {q, q'})"
                  and "Q = ofsm_table M f k q2"
        using \<open>Q \<in> ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'})\<close> by blast 
      ultimately have "ofsm_table M f k q1 = ofsm_table M f k q2"
        by auto

      have "q1 \<in> states M" and "q1 \<notin> \<Union> (ofsm_table M f k ` {q, q'})"
        using \<open>q1 \<in> (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'}))\<close>
        by blast+
      have "q2 \<in> states M"
        using \<open>q2 \<in> \<Union> (ofsm_table M f k ` {q, q'})\<close> \<open>states M = (states M - \<Union>(ofsm_table M f k ` {q,q'})) \<union> \<Union>(ofsm_table M f k ` {q,q'})\<close>
        by blast

      have "q1 \<in> ofsm_table M f k q2"
        using \<open>ofsm_table M f k q1 = ofsm_table M f k q2\<close>
        using ofsm_table_eq_if_elem[OF \<open>q2 \<in> states M\<close> \<open>q1 \<in> states M\<close> assms(1)] 
        by blast
      moreover have "q2 \<in> ofsm_table M f k q \<or> q2 \<in> ofsm_table M f k q'"
        using \<open>q2 \<in> \<Union> (ofsm_table M f k ` {q, q'})\<close> 
        by blast
      ultimately have "q1 \<in> \<Union> (ofsm_table M f k ` {q, q'})"
        unfolding ofsm_table_eq_if_elem[OF \<open>q \<in> states M\<close> \<open>q2 \<in> states M\<close> assms(1), symmetric]
        unfolding ofsm_table_eq_if_elem[OF \<open>q' \<in> states M\<close> \<open>q2 \<in> states M\<close> assms(1), symmetric]
        by blast
      then show False
        using \<open>q1 \<notin> \<Union> (ofsm_table M f k ` {q, q'})\<close>
        by blast
    qed
    
    show "card (ofsm_table M f k ` states M) 
          = card (ofsm_table M f k ` (states M - \<Union>(ofsm_table M f k ` {q,q'}))) + card (ofsm_table M f k ` (\<Union>(ofsm_table M f k ` {q,q'})))"
      using card_Un_disjoint[OF * ** ***]
      using \<open>states M = (states M - \<Union>(ofsm_table M f k ` {q,q'})) \<union> \<Union>(ofsm_table M f k ` {q,q'})\<close>
      by (metis image_Un)
  qed

  have s1: "\<And> k . (states M - \<Union>(ofsm_table M f k ` {q,q'})) \<subseteq> states M"
  and  s2: "\<And> k . (\<Union>(ofsm_table M f k ` {q,q'})) \<subseteq> states M"
    using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(1)] \<open>q \<in> states M\<close>]
    using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(1)] \<open>q' \<in> states M\<close>]
    by blast+

  have "card (ofsm_table M f (Suc k) ` states M) > card (ofsm_table M f k ` states M)"
  proof -
    have *: "\<Union> (ofsm_table M f (Suc k) ` {q, q'}) \<subseteq> \<Union> (ofsm_table M f k ` {q, q'})"
      using ofsm_table_subset
      by (metis SUP_mono' lessI less_imp_le_nat) 


    have "card (ofsm_table M f k ` (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'}))) \<le> card (ofsm_table M f (Suc k) ` (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'})))"
      using ofsm_table_refinement_card[OF assms(1), where i=k and j="Suc k", OF s1]
      using le_SucI by blast 
    moreover have "card (ofsm_table M f (Suc k) ` (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'}))) \<le> card (ofsm_table M f (Suc k) ` (FSM.states M - \<Union> (ofsm_table M f (Suc k) ` {q, q'})))"
      using *
      using fsm_states_finite[of M]
      by (meson Diff_mono card_mono finite_Diff finite_imageI image_mono subset_refl) 
    ultimately have "card (ofsm_table M f k ` (FSM.states M - \<Union> (ofsm_table M f k ` {q, q'}))) \<le> card (ofsm_table M f (Suc k) ` (FSM.states M - \<Union> (ofsm_table M f (Suc k) ` {q, q'})))"
      by presburger
    moreover have "card (ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'})) < card (ofsm_table M f (Suc k) ` \<Union> (ofsm_table M f (Suc k) ` {q, q'}))"
    proof -
      have *: "\<And> k . ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'}) = {ofsm_table M f k q, ofsm_table M f k q'}"
      proof -
        fix k show "ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'}) = {ofsm_table M f k q, ofsm_table M f k q'}"
        proof 
          show "ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'}) \<subseteq> {ofsm_table M f k q, ofsm_table M f k q'}"
          proof 
            fix Q assume "Q \<in> ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'})"
            then obtain qq where "Q = ofsm_table M f k qq"
                             and "qq \<in> \<Union> (ofsm_table M f k ` {q, q'})"
              by blast

            then have "qq \<in> ofsm_table M f k q \<or> qq \<in> ofsm_table M f k q'"
              by blast
            then have "qq \<in> states M"
              using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(1)]] \<open>q \<in> states M\<close> \<open>q' \<in> states M\<close>
              by blast
            
            have "ofsm_table M f k qq = ofsm_table M f k q \<or> ofsm_table M f k qq = ofsm_table M f k q'"
              using \<open>qq \<in> ofsm_table M f k q \<or> qq \<in> ofsm_table M f k q'\<close>
              using ofsm_table_eq_if_elem[OF _ \<open>qq \<in> states M\<close> assms(1)] \<open>q \<in> states M\<close> \<open>q' \<in> states M\<close>
              by blast
            then show "Q \<in> {ofsm_table M f k q, ofsm_table M f k q'}"
              using \<open>Q = ofsm_table M f k qq\<close> 
              by blast
          qed
          show "{ofsm_table M f k q, ofsm_table M f k q'} \<subseteq> ofsm_table M f k ` \<Union> (ofsm_table M f k ` {q, q'})"
            using ofsm_table_containment[of _ M f, OF _ equivalence_relation_on_states_refl[OF assms(1)]] \<open>q \<in> states M\<close> \<open>q' \<in> states M\<close>
            by blast
        qed
      qed

      have "ofsm_table M f k q = ofsm_table M f k q'"
        using \<open>q' \<in> ofsm_table M f k q\<close> 
        using ofsm_table_eq_if_elem[OF \<open>q \<in> states M\<close> \<open>q' \<in> states M\<close> assms(1)] 
        by blast
      moreover have "ofsm_table M f (Suc k) q \<noteq> ofsm_table M f (Suc k) q'"
        using \<open>q' \<notin> ofsm_table M f (Suc k) q\<close> 
        using ofsm_table_eq_if_elem[OF \<open>q \<in> states M\<close> \<open>q' \<in> states M\<close> assms(1)] 
        by blast 
      ultimately show ?thesis
        unfolding *
        by (metis card_insert_if finite.emptyI finite.insertI insert_absorb insert_absorb2 insert_not_empty lessI singleton_insert_inj_eq) 
    qed
    ultimately show ?thesis
      unfolding card_qq by presburger
  qed
  then show False
    using assms(2) by linarith
qed


lemma ofsm_table_refinement_card_fix :
  assumes "equivalence_relation_on_states M f"
  and     "card (ofsm_table M f j ` states M) = card (ofsm_table M f i ` states M)" 
  and     "q \<in> states M"
  and     "i \<le> j"
shows "ofsm_table M f j q = ofsm_table M f i q"
  using assms (2,4) proof (induction "j-i" arbitrary: i j)
  case 0
  then have "i = j" by auto
  then show ?case by auto
next
  case (Suc k)
  then have "j \<ge> Suc i" and "k = j - Suc i"
    by auto

  have *:"card (ofsm_table M f j ` FSM.states M) = card (ofsm_table M f (Suc i) ` FSM.states M)"
  and  **:"card (ofsm_table M f (Suc i) ` FSM.states M) = card (ofsm_table M f i ` FSM.states M)"
    using ofsm_table_refinement_card[OF assms(1), where A="states M"]
    by (metis Suc.prems(1) \<open>Suc i \<le> j\<close> eq_iff le_SucI)+

  
  show ?case
    using Suc.hyps(1)[OF \<open>k = j - Suc i\<close> * \<open>Suc i \<le> j\<close>]
    using ofsm_table_refinement_card_fix_Suc[OF assms(1) ** assms(3)]
    by blast
qed


lemma ofsm_table_partition_fixpoint_Suc :
  assumes "equivalence_relation_on_states M f"
  and     "q \<in> states M" 
shows "ofsm_table M f (size M - card (f ` states M)) q = ofsm_table M f (Suc (size M - card (f ` states M))) q"
proof -

  have "\<And> q . q \<in> states M \<Longrightarrow> f q = ofsm_table M f 0 q"
    unfolding ofsm_table.simps by auto

  define n where n: "n = (\<lambda> i . card (ofsm_table M f i ` states M))"

  have "\<And> i j . i \<le> j \<Longrightarrow> n i \<le> n j"
    unfolding n
    using ofsm_table_refinement_card[OF assms(1), where A="states M"]
    by blast
  moreover have "\<And> i j m . i < j \<Longrightarrow> n i = n j \<Longrightarrow> j \<le> m \<Longrightarrow> n i = n m"
  proof -
    fix i j m assume "i < j" and "n i = n j" and "j \<le> m"
    then have "Suc i \<le> j" and "i \<le> Suc i" and "i \<le> m"
      by auto

    have "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f j q = ofsm_table M f i q"
      using \<open>i < j\<close> \<open>n i = n j\<close> ofsm_table_refinement_card_fix[OF assms(1) _]
      unfolding n
      using less_imp_le_nat by presburger
    then have "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f (Suc i) q = ofsm_table M f i q"
      using ofsm_table_subset[OF \<open>Suc i \<le> j\<close>, of M f]
      using ofsm_table_subset[OF \<open>i \<le> Suc i\<close>, of M f]
      by blast
    then have "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table M f m q = ofsm_table M f i q"
      using ofsm_table_fixpoint[OF \<open>i \<le> m\<close>] 
      by metis
    then show "n i = n m"
      unfolding n
      by auto 
  qed
  moreover have "\<And> i . n i \<le> size M"
    unfolding n
    using ofsm_table_states[of M f, OF equivalence_relation_on_states_ran[OF assms(1)]]
    using fsm_states_finite[of M]
    by (simp add: card_image_le) 
  ultimately obtain k where "n (Suc k) = n k"
                        and "k \<le> size M - n 0"
    using monotone_function_with_limit_witness_helper[where f=n and k="size M"]
    by blast

  then show ?thesis
    unfolding n 
    using \<open>\<And> q . q \<in> states M \<Longrightarrow> f q = ofsm_table M f 0 q\<close>[symmetric]

    using ofsm_table_refinement_card_fix_Suc[OF assms(1) _ ]
    using ofsm_table_fixpoint[OF _ _ assms(2)]
    by (metis (mono_tags, lifting) image_cong nat_le_linear not_less_eq_eq)
qed

  

lemma ofsm_table_partition_fixpoint :
  assumes "equivalence_relation_on_states M f"
  and     "size M \<le> m"
  and     "q \<in> states M" 
shows "ofsm_table M f (m - card (f ` states M)) q = ofsm_table M f (Suc (m - card (f ` states M))) q"
proof -
  have *: "size M - card (f ` states M) \<le> m - card (f ` states M)"
    using assms(2) by simp
  have **: "(size M - card (f ` states M)) \<le> Suc (m - card (f ` states M))"
    using assms(2) by simp

  have ***: "\<And> q . q \<in> FSM.states M \<Longrightarrow> ofsm_table M f (FSM.size M - card (f ` FSM.states M)) q = ofsm_table M f (Suc (FSM.size M - card (f ` FSM.states M))) q"
    using ofsm_table_partition_fixpoint_Suc[OF assms(1)] .

  have "ofsm_table M f (m - card (f ` states M)) q = ofsm_table M f (FSM.size M - card (f ` FSM.states M)) q"
    using ofsm_table_fixpoint[OF * _ assms(3)] ***
    by blast
  moreover have "ofsm_table M f (Suc (m - card (f ` states M))) q = ofsm_table M f (FSM.size M - card (f ` FSM.states M)) q"
    using ofsm_table_fixpoint[OF ** _ assms(3), of f] *** 
    by blast
  ultimately show ?thesis
    by simp
qed



lemma ofsm_table_fix_partition_fixpoint :
  assumes "equivalence_relation_on_states M f"
  and     "size M \<le> m"
  and     "q \<in> states M"
shows "ofsm_table M f (m - card (f ` states M)) q = ofsm_table_fix M f 0 q" 
proof -

  obtain k where k1: "ofsm_table_fix M f 0 q = ofsm_table M f k q" 
             and k2: "\<And> k' . k' \<ge> k \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f k q"
    using ofsm_table_fix_length[of M f, OF equivalence_relation_on_states_ran[OF assms(1)]] 
          assms(3)
    by metis

  have m1: "\<And> k' . k' \<ge> m - card (f ` states M) \<Longrightarrow> ofsm_table M f k' q = ofsm_table M f (m - card (f ` states M)) q"
    using ofsm_table_partition_fixpoint[OF assms(1,2)]
    using ofsm_table_fixpoint[OF _ _ assms(3)]
    by presburger 

  show ?thesis proof (cases "k \<le> m - card (f ` states M)")
    case True
    show ?thesis
      using k1 k2[OF True] by simp
  next
    case False
    then have "k \<ge> m - card (f ` states M)"
      by auto
    then have "ofsm_table M f k q = ofsm_table M f (m - card (f ` states M)) q"
      using ofsm_table_partition_fixpoint[OF assms(1,2)]
      using ofsm_table_fixpoint[OF _ _ assms(3)]
      by presburger  
    then show ?thesis 
      using k1 by simp
  qed
qed

subsection \<open>A minimisation function based on OFSM-tables\<close>


lemma language_equivalence_classes_preserve_observability:
  assumes "transitions M' = (\<lambda> t . ({q \<in> states M . LS M q = LS M (t_source t)} , t_input t, t_output t, {q \<in> states M . LS M q = LS M (t_target t)})) ` transitions M"
  and     "observable M"
shows "observable M'"
proof -
  have "\<And> t1 t2 . t1 \<in> transitions M' \<Longrightarrow>
                   t2 \<in> transitions M' \<Longrightarrow>
                    t_source t1 = t_source t2 \<Longrightarrow> 
                    t_input t1 = t_input t2 \<Longrightarrow> 
                    t_output t1 = t_output t2 \<Longrightarrow>
                    t_target t1 = t_target t2"
  proof -
    fix t1 t2 assume "t1 \<in> transitions M'" and "t2 \<in> transitions M'" and "t_source t1 = t_source t2" and "t_input t1 = t_input t2" and "t_output t1 = t_output t2"

    
    obtain t1' where t1'_def: "t1 = ({q \<in> states M . LS M q = LS M (t_source t1')} , t_input t1', t_output t1', {q \<in> states M . LS M q = LS M (t_target t1')})"
                 and          "t1' \<in> transitions M"
      using \<open>t1 \<in> transitions M'\<close> assms(1) by auto
    obtain t2' where t2'_def: "t2 = ({q \<in> states M . LS M q = LS M (t_source t2')} , t_input t2', t_output t2', {q \<in> states M . LS M q = LS M (t_target t2')})"
                 and          "t2' \<in> transitions M"
      using \<open>t2 \<in> transitions M'\<close> assms(1) \<open>t_input t1 = t_input t2\<close> \<open>t_output t1 = t_output t2\<close> by auto

    have "{q \<in> FSM.states M. LS M q = LS M (t_source t1')} = {q \<in> FSM.states M. LS M q = LS M (t_source t2')}"
      using t1'_def t2'_def \<open>t_source t1 = t_source t2\<close>
      by (metis (no_types, lifting) fst_eqD)
    then have "LS M (t_source t1') = LS M (t_source t2')"
      using fsm_transition_source[OF \<open>t1' \<in> transitions M\<close>] fsm_transition_source[OF \<open>t2' \<in> transitions M\<close>] by blast
    then have "LS M (t_target t1') = LS M (t_target t2')"
      using observable_transition_target_language_eq[OF _ \<open>t1' \<in> transitions M\<close>  \<open>t2' \<in> transitions M\<close> _ _ \<open>observable M\<close>] 
      using \<open>t_input t1 = t_input t2\<close> \<open>t_output t1 = t_output t2\<close>
      unfolding t1'_def t2'_def  fst_conv snd_conv by blast
    then show "t_target t1 = t_target t2"
      unfolding t1'_def t2'_def snd_conv by blast
  qed
  then show ?thesis 
    unfolding observable.simps by blast
qed




lemma language_equivalence_classes_retain_language_and_induce_minimality :
  assumes "transitions M' = (\<lambda> t . ({q \<in> states M . LS M q = LS M (t_source t)} , t_input t, t_output t, {q \<in> states M . LS M q = LS M (t_target t)})) ` transitions M"
  and     "states M' = (\<lambda>q . {q' \<in> states M . LS M q = LS M q'}) ` states M"
  and     "initial M' = {q' \<in> states M . LS M q' = LS M (initial M)}"
  and     "observable M"
shows "L M = L M'"
and   "minimal M'"
proof -
  have "observable M'"
    using assms(1,4) language_equivalence_classes_preserve_observability by blast
        
  have ls_prop: "\<And> io q . q \<in> states M \<Longrightarrow> (io \<in> LS M q) \<longleftrightarrow> (io \<in> LS M' {q' \<in> states M . LS M q = LS M q'})"
  proof -
    fix io q assume "q \<in> states M" 
    then show "(io \<in> LS M q) \<longleftrightarrow> (io \<in> LS M' {q' \<in> states M . LS M q = LS M q'})"
    proof (induction io arbitrary: q)
      case Nil
      then show ?case using assms(2) by auto
    next
      case (Cons xy io)

      obtain x y where "xy = (x,y)"
        using surjective_pairing by blast
        
      have "xy#io \<in> LS M q \<Longrightarrow> xy#io \<in> LS M' {q' \<in> states M . LS M q = LS M q'}"
      proof -
        assume "xy#io \<in> LS M q"
        then obtain p where "path M q p" and "p_io p = xy#io"
          unfolding LS.simps mem_Collect_eq by (metis (no_types, lifting)) 

        let ?t = "hd p"
        let ?p = "tl p"
        let ?q' = "{q' \<in> states M . LS M (t_target ?t) = LS M q'}"

        have "p = ?t # ?p" and "p_io ?p = io" and "t_input ?t = x" and "t_output ?t = y"
          using \<open>p_io p = xy#io\<close> unfolding \<open>xy = (x,y)\<close> by auto
        moreover have "?t \<in> transitions M" and "path M (t_target ?t) ?p" and "t_source ?t = q"
          using \<open>path M q p\<close> path_cons_elim[of M q ?t ?p] calculation by auto
        ultimately have "[(x,y)] \<in> LS M q"
          unfolding LS_single_transition[of x y M q] by auto
        then have "io \<in> LS M (t_target ?t)"
          using observable_language_next[OF _ \<open>observable M\<close>, of "(x,y)" io, OF _ \<open>?t \<in> transitions M\<close>]
                \<open>xy#io \<in> LS M q\<close> 
          unfolding \<open>xy = (x,y)\<close> \<open>t_source ?t = q\<close> \<open>t_input ?t = x\<close> \<open>t_output ?t = y\<close> 
          by (metis \<open>?t \<in> FSM.transitions M\<close> from_FSM_language fsm_transition_target fst_conv snd_conv) 
        then have "io \<in> LS M' ?q'"
          using Cons.IH[OF fsm_transition_target[OF \<open>?t \<in> transitions M\<close>]] by blast
        then obtain p' where "path M' ?q' p'" and "p_io p' = io"
          by auto
        have *: "({q' \<in> states M . LS M q = LS M q'},x,y,{q' \<in> states M . LS M (t_target ?t) = LS M q'}) \<in> transitions M'"
          using \<open>?t \<in> transitions M\<close> \<open>t_source ?t = q\<close> \<open>t_input ?t = x\<close> \<open>t_output ?t = y\<close> 
          unfolding assms(1) by auto
        
        show "xy#io \<in> LS M' {q' \<in> states M . LS M q = LS M q'}"
          using LS_prepend_transition[OF * ] unfolding snd_conv fst_conv \<open>xy = (x,y)\<close>
          using \<open>io \<in> LS M' ?q'\<close> by blast
      qed
      moreover have "xy#io \<in> LS M' {q' \<in> states M . LS M q = LS M q'} \<Longrightarrow> xy#io \<in> LS M q"
      proof -
        let ?q = "{q' \<in> states M . LS M q = LS M q'}"
        assume "xy#io \<in> LS M' ?q"
        then obtain p where "path M' ?q p" and "p_io p = xy#io"
          unfolding LS.simps mem_Collect_eq by (metis (no_types, lifting)) 

        let ?t = "hd p"
        let ?p = "tl p"


        have "p = ?t # ?p" and "p_io ?p = io" and "t_input ?t = x" and "t_output ?t = y"
          using \<open>p_io p = xy#io\<close> unfolding \<open>xy = (x,y)\<close> by auto
        then have "path M' ?q (?t#?p)"
          using \<open>path M' ?q p\<close> by auto
        then have "?t \<in> transitions M'" and "path M' (t_target ?t) ?p" and "t_source ?t = ?q"
          by force+
        then have "io \<in> LS M' (t_target ?t)"
          using \<open>p_io ?p = io\<close> by auto

        
        
        obtain t0 where t0_def: "?t = (\<lambda> t . ({q \<in> states M . LS M q = LS M (t_source t)} , t_input t, t_output t, {q \<in> states M . LS M q = LS M (t_target t)})) t0"
                    and "t0 \<in> transitions M"
          using \<open>?t \<in> transitions M'\<close> 
          unfolding assms(1)
          by auto
        then have "t_source t0 \<in> ?q" 
          using \<open>t_source ?t = ?q\<close>
          by (metis (mono_tags, lifting) fsm_transition_source fst_eqD mem_Collect_eq) 
        then have "LS M q = LS M (t_source t0)"
          by auto
        moreover have "[(x,y)] \<in> LS M (t_source t0)"
          using t0_def \<open>t_input ?t = x\<close> \<open>t0 \<in> transitions M\<close> \<open>t_output ?t = y\<close> \<open>t_source t0 \<in> ?q\<close> unfolding LS_single_transition by auto
        ultimately obtain t where "t \<in> transitions M" and "t_source t = q" and "t_input t = x" and "t_output t = y"
          by (metis LS_single_transition)

        have "LS M (t_target t) = LS M (t_target t0)"
          using observable_transition_target_language_eq[OF _\<open>t \<in> transitions M\<close> \<open>t0 \<in> transitions M\<close> _ _ \<open>observable M\<close>]
          using \<open>LS M q = LS M (t_source t0)\<close> 
          unfolding \<open>t_source t = q\<close> \<open>t_input t = x\<close> \<open>t_output t = y\<close> 
          using t0_def \<open>t_input ?t = x\<close> \<open>t_output ?t = y\<close> 
          by auto
        moreover have "t_target ?t = {q' \<in> FSM.states M. LS M (t_target t) = LS M q'}"
          using calculation t0_def by fastforce
        ultimately have "io \<in> LS M (t_target t)"
          using Cons.IH[OF fsm_transition_target[OF \<open>t \<in> transitions M\<close>]]
                \<open>io \<in> LS M' (t_target ?t)\<close> 
          by auto
        then show "xy#io \<in> LS M q"
          unfolding \<open>t_source t = q\<close>[symmetric] \<open>xy = (x,y)\<close> 
          using \<open>t_input t = x\<close> \<open>t_output t = y\<close>
          using LS_prepend_transition \<open>t \<in> FSM.transitions M\<close> 
          by blast 
      qed

      ultimately show ?case 
        by blast
    qed
  qed

  have "L M' = LS M' {q' \<in> states M . LS M (initial M) = LS M q'}"
    using assms(3)
    by (metis (mono_tags, lifting) Collect_cong) 
  then show "L M = L M'"
    using ls_prop[OF fsm_initial] by blast

  show "minimal M'"
  proof -
    have"\<And> q q' . q \<in> states M' \<Longrightarrow> q' \<in> states M' \<Longrightarrow> LS M' q = LS M' q' \<Longrightarrow> q = q'"
    proof -
     
      fix q q' assume "q \<in> states M'" and "q' \<in> states M'" and "LS M' q = LS M' q'"
  
      obtain qM where "q = {q \<in> states M . LS M qM = LS M q}" and "qM \<in> states M"
        using \<open>q \<in> states M'\<close> assms(2) by auto
      obtain qM' where "q' = {q \<in> states M . LS M qM' = LS M q}" and "qM' \<in> states M"
        using \<open>q' \<in> states M'\<close> assms(2) by auto
  
      have "LS M qM = LS M' q"
        using ls_prop[OF \<open>qM \<in> states M\<close>] unfolding \<open>q = {q \<in> states M . LS M qM = LS M q}\<close> by blast
      moreover have "LS M qM' = LS M' q'"
        using ls_prop[OF \<open>qM' \<in> states M\<close>] unfolding \<open>q' = {q \<in> states M . LS M qM' = LS M q}\<close> by blast
      ultimately have "LS M qM = LS M qM'"
        using \<open>LS M' q = LS M' q'\<close> by blast
      then show "q = q'"
        unfolding \<open>q = {q \<in> states M . LS M qM = LS M q}\<close> \<open>q' = {q \<in> states M . LS M qM' = LS M q}\<close> by blast
    qed
    then show ?thesis
      unfolding minimal_alt_def by blast
  qed
qed



fun minimise :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> ('a set,'b,'c) fsm" where
  "minimise M = (let
      eq_class = ofsm_table_fix M (\<lambda>q . states M) 0;
      ts = (\<lambda> t . (eq_class (t_source t), t_input t, t_output t, eq_class (t_target t))) ` (transitions M);
      q0 = eq_class (initial M);
      eq_states = eq_class |`| fstates M;
      M' = create_unconnected_fsm_from_fsets q0 eq_states (finputs M) (foutputs M)
  in add_transitions M' ts)"


lemma minimise_initial_partition :
  "equivalence_relation_on_states M (\<lambda>q . states M)"
proof -
  let ?r = "{(q1,q2) | q1 q2 . q1 \<in> states M \<and> q2 \<in> (\<lambda>q . states M) q1}"

  have "refl_on (FSM.states M) ?r"
    unfolding refl_on_def by blast
  moreover have "sym ?r" 
    unfolding sym_def by blast
  moreover have "trans ?r"
    unfolding trans_def by blast
  ultimately show ?thesis
    unfolding equivalence_relation_on_states_def equiv_def by auto
qed


lemma minimise_props:
  assumes "observable M"
shows "initial (minimise M) = {q' \<in> states M . LS M q' = LS M (initial M)}"
and   "states (minimise M) = (\<lambda>q . {q' \<in> states M . LS M q = LS M q'}) ` states M"
and   "inputs (minimise M) = inputs M"
and   "outputs (minimise M) = outputs M"
and   "transitions (minimise M) = (\<lambda> t . ({q \<in> states M . LS M q = LS M (t_source t)} , t_input t, t_output t, {q \<in> states M . LS M q = LS M (t_target t)})) ` transitions M"
proof -

  let ?f = "\<lambda>q . states M"

  define eq_class where "eq_class = ofsm_table_fix M (\<lambda>q . states M) 0"
  moreover define M' where M'_def: "M' = create_unconnected_fsm_from_fsets (eq_class (initial M)) (eq_class |`| fstates M) (finputs M) (foutputs M)"
  ultimately have *: "minimise M = add_transitions M' ((\<lambda> t . (eq_class (t_source t), t_input t, t_output t, eq_class (t_target t))) ` (transitions M))"
    by auto


  have **: "\<And> q . q \<in> states M \<Longrightarrow> eq_class q = {q' \<in> FSM.states M. LS M q = LS M q'}"
    using ofsm_table_fix_set[OF _ assms minimise_initial_partition] \<open>eq_class = ofsm_table_fix M ?f 0\<close>  after_is_state[OF \<open>observable M\<close>] by blast
  then have ****: "\<And> q . q \<in> states M \<Longrightarrow> eq_class q = {q' \<in> FSM.states M. LS M q' = LS M q}"
    using ofsm_table_fix_set[OF _ assms] \<open>eq_class = ofsm_table_fix M ?f 0\<close> by blast
  
  have ***: "(eq_class (initial M)) |\<in>| (eq_class |`| fstates M)"
    using fsm_initial[of M] fstates_set by fastforce

  have m1:"initial M' = {q' \<in> states M . LS M q' = LS M (initial M)}"
    by (metis (mono_tags) "***" "****" M'_def create_unconnected_fsm_from_fsets_simps(1) fsm_initial)

  have m2: "states M' = (\<lambda>q . {q' \<in> states M . LS M q = LS M q'}) ` states M"
    unfolding M'_def
  proof -
    have "FSM.states (FSM.create_unconnected_fsm_from_fsets (eq_class (FSM.initial M)) (eq_class |`| fstates M) (finputs M) (foutputs M)) = eq_class ` FSM.states M"
      by (metis (no_types) "***" create_unconnected_fsm_from_fsets_simps(2) fset.set_map fstates_set)
    then show "FSM.states (FSM.create_unconnected_fsm_from_fsets (eq_class (FSM.initial M)) (eq_class |`| fstates M) (finputs M) (foutputs M)) = (\<lambda>a. {aa \<in> FSM.states M. LS M a = LS M aa}) ` FSM.states M"
      using "**" by force
  qed  

  have m3: "inputs M' = inputs M"
    using create_unconnected_fsm_from_fsets_simps(3)[OF ***] finputs_set unfolding M'_def by metis

  have m4: "outputs M' = outputs M"
    using create_unconnected_fsm_from_fsets_simps(4)[OF ***] foutputs_set unfolding M'_def by metis

  have m5: "transitions M' = {}"
    using create_unconnected_fsm_from_fsets_simps(5)[OF ***] unfolding M'_def by force

  let ?ts = "((\<lambda> t . (eq_class (t_source t), t_input t, t_output t, eq_class (t_target t))) ` (transitions M))"
  have wf: "\<And> t . t \<in>?ts \<Longrightarrow> t_source t \<in> states M' \<and> t_input t \<in> inputs M' \<and> t_output t \<in> outputs M' \<and> t_target t \<in> states M'"
  proof -
    fix t assume "t \<in> ?ts"
    then obtain tM where "tM \<in> transitions M"
                   and   *: "t = (\<lambda> t . (eq_class (t_source t), t_input t, t_output t, eq_class (t_target t))) tM"
      by blast

    have "t_source t \<in> states M'"
      using fsm_transition_source[OF \<open>tM \<in> transitions M\<close>]
      unfolding m2 * **[OF fsm_transition_source[OF \<open>tM \<in> transitions M\<close>]] by auto
    moreover have "t_input t \<in> inputs M'"
      unfolding m3 * using fsm_transition_input[OF \<open>tM \<in> transitions M\<close>] by auto
    moreover have "t_output t \<in> outputs M'"
      unfolding m4 * using fsm_transition_output[OF \<open>tM \<in> transitions M\<close>] by auto
    moreover have "t_target t \<in> states M'"
      using fsm_transition_target[OF \<open>tM \<in> transitions M\<close>]
      unfolding m2 * **[OF fsm_transition_target[OF \<open>tM \<in> transitions M\<close>]] by auto
    ultimately show "t_source t \<in> states M' \<and> t_input t \<in> inputs M' \<and> t_output t \<in> outputs M' \<and> t_target t \<in> states M'" 
      by simp
  qed


  show "initial (minimise M) = {q' \<in> states M . LS M q' = LS M (initial M)}"
    using add_transitions_simps(1)[OF wf] unfolding * m1 .

  show "states (minimise M) = (\<lambda>q . {q' \<in> states M . LS M q = LS M q'}) ` states M"
    using add_transitions_simps(2)[OF wf] unfolding * m2 .

  show "inputs (minimise M) = inputs M"
    using add_transitions_simps(3)[OF wf] unfolding * m3 .

  show "outputs (minimise M) = outputs M"
    using add_transitions_simps(4)[OF wf] unfolding * m4 .

  show "transitions (minimise M) = (\<lambda> t . ({q \<in> states M . LS M q = LS M (t_source t)} , t_input t, t_output t, {q \<in> states M . LS M q = LS M (t_target t)})) ` transitions M"
    using add_transitions_simps(5)[OF wf] ****[OF fsm_transition_source] ****[OF fsm_transition_target] unfolding * m5 by auto
qed


lemma minimise_observable:
  assumes "observable M"
shows "observable (minimise M)"
  using language_equivalence_classes_preserve_observability[OF minimise_props(5)[OF assms] assms]
  by assumption
        
lemma minimise_minimal:
  assumes "observable M"
shows "minimal (minimise M)"
  using language_equivalence_classes_retain_language_and_induce_minimality(2)[OF minimise_props(5,2,1)[OF assms]  assms] 
  by assumption

lemma minimise_language:
  assumes "observable M"
shows "L (minimise M) = L M"
  using language_equivalence_classes_retain_language_and_induce_minimality(1)[OF minimise_props(5,2,1)[OF assms]  assms] 
  by blast

lemma minimal_observable_code :
  assumes "observable M"
  shows "minimal M = (\<forall> q \<in> states M . ofsm_table_fix M (\<lambda>q . states M) 0 q = {q})"
proof 
  show "minimal M \<Longrightarrow> (\<forall> q \<in> states M . ofsm_table_fix M (\<lambda>q . states M) 0 q = {q})"
  proof 
    fix q assume "minimal M" and "q \<in> states M"
    then show "ofsm_table_fix M (\<lambda>q . states M) 0 q = {q}" 
      unfolding ofsm_table_fix_set[OF \<open>q \<in> states M\<close> \<open>observable M\<close> minimise_initial_partition]
                minimal_alt_def 
      using after_is_state[OF \<open>observable M\<close>]
      by blast
  qed

  show "\<forall>q\<in>FSM.states M. ofsm_table_fix M (\<lambda>q . states M) 0 q = {q} \<Longrightarrow> minimal M"
    using ofsm_table_fix_set[OF _ \<open>observable M\<close> minimise_initial_partition] after_is_state[OF \<open>observable M\<close>]
    unfolding minimal_alt_def 
    by blast
qed

lemma minimise_states_subset :
  assumes "observable M"
  and     "q \<in> states (minimise M)"
shows "q \<subseteq> states M" 
  using assms(2) 
  unfolding minimise_props[OF assms(1)]
  by auto 

lemma minimise_states_finite :
  assumes "observable M"
  and     "q \<in> states (minimise M)"
  shows "finite q"
  using minimise_states_subset[OF assms] fsm_states_finite[of M]
  using finite_subset by auto

end