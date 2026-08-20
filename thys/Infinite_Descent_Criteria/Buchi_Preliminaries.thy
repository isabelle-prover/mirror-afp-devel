(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsection "Buchi Complementation Extended"

text "A small extension to the B\"uchi Complementation AFP entry, including: useful definitions,
     results on omega lasso languages, finitely occuring predicates on streams and complement results"

theory Buchi_Preliminaries
imports Preliminaries  "Buchi_Complementation.Complementation_Final"
begin

(* PRELIMINARIES *)
(*run*)
lemmas run_def = nba.run_alt_def_snth   nba.target_alt_def  nba.states_alt_def

lemma runE_alpha:
  assumes "NBA.run A (x ||| r) p"
  shows "\<And>k. x !! k \<in> nba.alphabet A"
  using assms last_stake_Suc[of _ r]  unfolding run_def by(auto split:if_splits)

lemma runE_0:
  assumes "NBA.run A (x ||| r) p"
  shows "r !! 0  \<in> nba.transition A (x !! 0) p "
  using assms last_stake_Suc[of _ r]  unfolding run_def by(auto split:if_splits)

lemma runE_Suc:
  assumes "NBA.run A (x ||| r) p"
  shows "\<And>k. r !! Suc k  \<in> nba.transition A (x !! Suc k) (r !!k)"
  using assms last_stake_Suc[of _ r]  unfolding run_def by(auto split:if_splits)

lemma runE_Suc':
  assumes "NBA.run A (x ||| r) p" "k > 0"
  shows "r !! k  \<in> nba.transition A (x !! k) (r !! (k-1))"
  using assms(2)[unfolded gr0_conv_Suc] runE_Suc[OF assms(1)]  by auto

lemma runE_trans:
  assumes "NBA.run A (x ||| r) p"
  shows "k > 0 \<and> r !! k  \<in> nba.transition A (x !! k) (r !! (k-1)) \<or>
         k = 0 \<and> r !! k  \<in> nba.transition A (x !! k) p "
  apply(cases "k = 0")
  subgoal using runE_0[OF assms] by auto
  subgoal using runE_Suc'[OF assms] by auto .

(*Node*)
lemmas node_def = nba.nodes_alt_def[unfolded nba.reachable_alt_def nba.target_alt_def image_def Union_eq Bex_def]

lemma nodeI:
assumes "p \<in> nba.initial A"
        "(n = p \<and> NBA.path A [] p) \<or> (\<exists>r. r \<noteq>[] \<and> n = last (NGBA.states r p) \<and> NBA.path A r p)"
shows "n \<in> NBA.nodes A"
  unfolding node_def 
  apply(rule CollectI,rule exI[of _ "{y. \<exists>r. (r = [] \<longrightarrow> y = p \<and> NBA.path A [] p) \<and> (r \<noteq> [] \<longrightarrow> y = last (NGBA.states r p) \<and> NBA.path A r p)}"], intro conjI)
  subgoal using assms by auto
  subgoal apply(rule CollectI) using assms by auto .

lemma nodeI':
assumes "p \<in> nba.initial A"
        "(\<exists>r. r \<noteq>[] \<and> n = last (NGBA.states r p) \<and> NBA.path A r p)"
shows "n \<in> NBA.nodes A"
  unfolding node_def 
  apply(rule CollectI,rule exI[of _ "{y. \<exists>r. (r = [] \<longrightarrow> y = p \<and> NBA.path A [] p) \<and> (r \<noteq> [] \<longrightarrow> y = last (NGBA.states r p) \<and> NBA.path A r p)}"], intro conjI)
  subgoal using assms by auto
  subgoal apply(rule CollectI) using assms by auto .

lemma nba_path_singl:"fst a \<in> nba.alphabet A \<Longrightarrow> snd a \<in> nba.transition A (fst a) p \<Longrightarrow> NBA.path A [a] p" using nba.path.cons by auto

lemma nba_path_app_singl:"fst a \<in> nba.alphabet A \<Longrightarrow> snd a \<in> nba.transition A (fst a) (NGBA.target r p) \<Longrightarrow> NBA.path A r p \<Longrightarrow>  NBA.path A (r @ [a]) p"
  by (intro nba.path_append nba_path_singl, auto)

lemma target_last_states[simp]:"r\<noteq>[] \<Longrightarrow> NGBA.target r p = last (NGBA.states r p)"
  unfolding nba.target_alt_def nba.states_alt_def by auto

lemma target_emp[simp]:"NGBA.target [] p = p" unfolding nba.target_alt_def by auto
lemma last_states_singl[simp]:"last (NGBA.states [(x,s)] p) = s" unfolding nba.states_alt_def by auto
lemma last_states_app[simp]:"ra \<noteq> [] \<Longrightarrow> last (NGBA.states (ra @[(x,s)]) p) = s" unfolding nba.states_alt_def by auto


lemma run_nodes_closure: 
  assumes lang: "p \<in> nba.initial A" "NBA.run A (x ||| r) p"
  shows"\<And>x. r !! x \<in> NBA.nodes A"
  subgoal for x' proof(rule nodeI'[OF lang(1)],induct x')
    case 0
    then show ?case 
      apply(intro exI[of _ "[(shd x,shd r)]"])
      using runE_alpha[OF lang(2), of 0] runE_0[OF lang(2)] by auto 
  next
    case (Suc x')
    then obtain ra where ra:"ra \<noteq> []" "r !! x' = last (NGBA.states ra p)" "NBA.path A ra p" by auto
    then show ?case
    apply(intro exI[of _ "ra @ [(x !! Suc x', r !! Suc x')]"] conjI)
      subgoal by auto
      subgoal by auto
      subgoal apply (rule nba_path_app_singl)
        using runE_alpha[OF lang(2), of "Suc x'"] runE_Suc[OF lang(2), of x'] by auto .
  qed .


(**)

lemma map_snd_stake_szip:"map snd (stake k (x ||| y)) = stake k y" by(cases k, auto)
lemma szip_unfold:"(x' ||| r') = (shd x', shd r') ## (stl x' ||| stl r')" by auto

lemma len_stake_szip: "length (q # map snd (stake (Suc n) (x ||| r))) = Suc (Suc n)" by simp
lemma nth_stake_szip:"(q # map snd (stake (Suc n) (x ||| r))) ! Suc n = r !! n"
apply (induct n) by (auto,metis lessI stake.simps(2) stake_nth) 

lemma last_stake_szip:"last (q # map snd (stake (Suc n) (x ||| r))) = r !! n" 
using last_conv_nth[of "q # map snd (stake (Suc n) (x ||| r))",unfolded len_stake_szip diff_Suc_1 nth_stake_szip] by auto 


lemma fst_nth_zip:"fst ((x ||| r) !! k) = x !! k" by auto
lemma snd_nth_zip:"snd ((x ||| r) !! k) = r !! k" by auto

(*finitely occuring predicates*)


lemma fins_finite:"fins P x \<Longrightarrow> finite {m. P (x !! m)}"
  using infinite_iff_alw_ev
  unfolding infinite_iff_alw_ev[symmetric] by simp

(*A finitely occuring predicate on a stream implies that it either:
     never occurs, or, there is a maximum/last index where it occurs*)
lemma fins_imp:"fins P x \<Longrightarrow> alw (holds (\<lambda>x. \<not>P x)) x \<or> (\<exists>i. \<forall>k > i. P (x !! i) \<and> \<not>P (x !! k))"
  apply(drule fins_finite)
  apply(cases "{m. P (x !! m)} = {}")
  subgoal by(rule disjI1, unfold alw_holds_iff_snth, auto)
  subgoal apply(rule disjI2, frule Max_in, clarify)
    by(rule exI[of _ "Max {m. P (x !! m)}"], auto) .

(**)

lemma target_zip_nth:"n > 0 \<Longrightarrow> NGBA.target (stake n w || stake n r') i = r' !! (n-1)"
unfolding nba.target_alt_def nba.states_alt_def using last_conv_nth[of "i # map snd (stake n w || stake n r')"] by auto 

lemma infs_snthI: "(\<And>n. \<exists> k \<ge> n. P (w !! k)) \<Longrightarrow> infs P w"
  unfolding infs_snth by auto

(*Complement results*)
lemma complement_eq1:
  assumes "NBA.alphabet A \<subseteq> NBA.alphabet B"
  assumes "finite (NBA.nodes B)"
  shows "NBA.language A \<subseteq> NBA.language B \<longleftrightarrow> NBA.language A \<inter> NBA.language (complement B) = {}"
proof -
  have "NBA.language A \<subseteq> streams (NBA.alphabet B)"
    using streams_mono2 nba.language_alphabet assms(1) by blast
  then show ?thesis
    using assms(2) by (auto simp: complement_language)
qed

lemma complement_eq2:"(NBA.language A \<inter> NBA.language (complement B) = {}) = (NBA.language (intersect A (complement B)) = {})" by auto 

lemma complement_eq3:
  assumes "NBA.alphabet A \<subseteq> NBA.alphabet B"
  assumes "finite (NBA.nodes B)"
  shows "NBA.language A \<subseteq> NBA.language B = (NBA.language (intersect A (complement B)) = {})"
  unfolding complement_eq1[OF assms] complement_eq2 by auto


(*If a word is valid in a language then there is also a valid omega lasso*)
(*This proof uses the pigeonhole principle such that there is a repeated accepting state r !! x = r !! y with y>x*)
(*We take the omega lasso to be v = r!!0 ... r!!x and u = r!!(x+1) ... r!!y (or r!!x)*)

lemma omega_lasso_lang:"finite (NBA.nodes A) \<Longrightarrow> x \<in> NBA.language A \<Longrightarrow> \<exists>v u. v @- srepeat u \<in> NBA.language A \<and> u \<noteq> []" 
proof(erule nba.language_elim, unfold alw_ev_scons infs_infm Inf_many_def)
  fix r p
  assume finite:"finite (NBA.nodes A)" and
         lang:"p \<in> nba.initial A" "NBA.run A (x ||| r) p" "infinite {i. nba.accepting A (r !! i)}"

  (*using the finite node space (of card n), we generate a set of n+1 accepting indexes*)
  obtain n where n:"n = card (NBA.nodes A)" using finite by auto

  have p_in_A:"p \<in> NBA.nodes A" using lang(1,2) by (auto split:if_splits)
  hence pr_in_A:"\<And>x. r!! x \<in> NBA.nodes A" subgoal for x  using run_nodes_closure[OF lang(1,2)] by auto  .

  also have Suc_set:"n \<noteq> 0" unfolding n  using calculation local.finite by auto

  obtain AS where AS_finite:"finite AS" and AS_card:"card AS = Suc (Suc n)" and
                  AS_subseq:"AS \<subseteq> {i. nba.accepting A (r !! i)}"
    using infinite_arbitrarily_large[OF lang(3), of "Suc (Suc n)"] by auto

  hence AS_accept:"\<forall>i\<in>AS. nba.accepting A (r !! i)" using AS_subseq by auto

  hence AS_accept':"\<And>i. i \<in>AS \<Longrightarrow> nba.accepting A (r !! i)" by auto
  have "(!!) r ` AS \<subseteq> NBA.nodes A" using pr_in_A by auto

  hence "card ((!!) r ` AS) \<le> n" unfolding n by (simp add: card_mono finite)

  moreover have card:"card ((!!) r ` AS) < card AS" using AS_card calculation by auto

  (*Hence we can obtain the repeated state which is accepting*)
  ultimately obtain x' y' where xy:"r !! x' = r !! y'" "x' < y'" "nba.accepting A (r !! x')"
    using pigeonhole[of "\<lambda>k. r!!k", OF card, unfolded inj_on_def] AS_accept nat_neq_iff by metis

  hence infs_r:"infs (nba.accepting A) (srepeat (map_ind r x' y'))" 
    apply-apply(rule infs_snthI)
    subgoal for n apply(intro exI[of _ "n * (y'-x')"])
    unfolding srepeat_map_ind_snth_eq by auto .
  have y_ne:"y' > 0" using xy(2) by auto
  have Suc_xy':"Suc x' \<le> y'" using xy by auto
  obtain n where y':"y' = Suc n" using y_ne by(cases y', auto)

  have take_hd:"stake x' x || stake x' r = stake x' (x ||| r)" by auto
  have stake_red:"stake (Suc x') x @- srepeat (map_ind x (Suc x') (Suc y')) |||
      stake x' r @- srepeat (map_ind r x' y') = 
     (stake (Suc x') x || stake (Suc x') r) @- (srepeat  (map_ind x (Suc x') (Suc y')) ||| srepeat (map_ind r (Suc x') (Suc y')))"
    using tl_map_ind[OF xy(2), of r] hd_map_ind[OF xy(2), of r] 
          map_ind_Suc[OF Suc_xy', of r] xy(1)
    unfolding stake_Suc by (auto simp: )

  (*The omega lasso is then obtained as described above, with cases on x+1 = y, i.e. a self loop between the accepting state or otherwise*)
  show "\<exists>v u. v @- srepeat u \<in> NBA.language A \<and> u \<noteq> []"
  proof(cases "Suc x' = y'")
    case True (*case of a self loop*)
    hence rx_trans:"r !! x' \<in> nba.transition A (x !! Suc x') (r !! x')" using xy(1) runE_Suc[OF lang(2), of x'] by auto
    have stl_r:"r !! Suc x' = r !! x'" using True xy by auto
    show ?thesis 
    proof(intro exI2[of _ "stake (Suc x') x" "[x !! (Suc x')]"] conjI nba.language[of p A _ "stake x' r @- srepeat [r !! x']",OF lang(1)])
    let ?w = "stake (Suc x') x @- srepeat [x !! Suc x']"
    and ?r = "stake x' r @- srepeat [r !! x']"
    have stake_red:"?w ||| ?r = (stake (Suc x') x || stake (Suc x') r) @- (srepeat [x !! Suc x'] ||| srepeat [r !! Suc x'])"
      using xy(1) unfolding stake_Suc True[symmetric] by auto
    show "infs (nba.accepting A) (p ## ?r)"using infs_r unfolding True[symmetric] by auto
    show "[x !! Suc x'] \<noteq> []" by auto
    show "NBA.run A (?w ||| ?r) p"
    proof(unfold stake_red, rule nba.run_shift)
      show "NBA.path A (stake (Suc x') x || stake (Suc x') r) p" unfolding take_hd using nba.run_stake[OF lang(2), of "Suc x'"] by auto
      show "NBA.run A (srepeat [x !! Suc x'] ||| srepeat [r !! Suc x']) (NGBA.target (stake (Suc x') x || stake (Suc x') r) p)"
        unfolding target_zip_nth[of "Suc x'" x r p, OF zero_less_Suc, unfolded diff_Suc_1] stl_r 
        apply(rule nba.snth_run, intro conjI)
        subgoal using runE_alpha[OF lang(2), of "Suc x'"] by auto
        subgoal for k apply(induct k) using rx_trans  by auto .
    qed
  qed
  next
    case False (*When the path is not a self loop: x' \<rightarrow> x'+1 \<rightarrow> ... \<rightarrow> y'*)
    hence Suc_xy:"Suc x' < y'" using Suc_xy'[unfolded le_eq_less_or_eq] by auto
    show ?thesis proof(intro exI2[of _ "stake (Suc x') x" "map_ind x (Suc x') (Suc y')"] conjI
        nba.language[of p A _ "stake x' r @- srepeat (map_ind r x' y')",OF lang(1)])
    let ?w = "stake (Suc x') x @- srepeat (map_ind x (Suc x') (Suc y'))"
    and ?r = "stake x' r @- srepeat (map_ind r x' y')"

    show "infs (nba.accepting A) (p ## ?r)"using infs_r by auto
    show "map_ind x (Suc x') (Suc y') \<noteq> []" using map_ind_ne[of "Suc x'"] xy(2) by auto
    show "NBA.run A (?w ||| ?r) p"
    proof(unfold stake_red, rule nba.run_shift)
      (*ensuring the prefix is valid*)
      show "NBA.path A (stake (Suc x') x || stake (Suc x') r) p" unfolding take_hd using nba.run_stake[OF lang(2), of "Suc x'"] by auto

      have target_Suc:"NGBA.target (stake (Suc x') x || stake (Suc x') r) p = r !! x'"  using target_zip_nth[of "Suc x'" x r p] by auto

      have path_step:"NBA.path A [(stl x !! x', stl r !! x')] (r !! y')" 
      unfolding xy(1)[symmetric]  apply(rule nba_path_singl)
        subgoal using runE_alpha[OF lang(2), of "Suc x'"] by auto
        subgoal using runE_Suc[OF lang(2)] by auto .

      have SucX:"Suc x' < Suc y'" using Suc_xy by auto
      have SucX':"Suc x' \<le> y'" using Suc_xy by auto

      note transition_simp = snth_szip fst_conv snd_conv srepeat_map_ind_eq[OF SucX] nba.target_alt_def nba.states_alt_def map_snd_stake_szip
                             map_snd_zip_take  stake_cycle[OF map_ind_ne[OF SucX, of r]]

      (*showing the cycle is a valid run, it suffices to show that all k prefixes of the run are valid paths, which goes by induction on k*)
      show "NBA.run A (srepeat (map_ind x (Suc x') (Suc y')) ||| srepeat (map_ind r (Suc x') (Suc y'))) (NGBA.target (stake (Suc x') x || stake (Suc x') r) p)"
        apply(rule nba.stake_run, unfold target_Suc)
        subgoal for k apply(induct k)
          subgoal by auto
          subgoal for k apply(unfold stake_Suc, rule nba_path_app_singl)
            (*is in the alphabet*)
            subgoal using runE_alpha[OF lang(2)] by (auto simp: transition_simp)
            (*is transition, goes through by cases of modulo arithmetic*)
            subgoal unfolding transition_simp map_ind_len[OF SucX]
              using Suc_xy disj_mod[of k "Suc y' - Suc x'"] apply-apply(elim disjE)
              subgoal using runE_Suc[OF lang(2), of "x'"] by auto
              subgoal using last_replicate_map_ind[of "k div (y' - x')" _ _ r, OF _ SucX']
                            runE_Suc[OF lang(2), of "x'"] xy(1) by auto
              subgoal using last_take_nth_conv[of "k mod (y' - x')" "map_ind r (Suc x') (Suc y')"]
                            nth_map_ind[of "(k mod (y' - x') - Suc 0)" "Suc y'" "Suc x'" r, OF mod_bound[OF xy(2), of k]]
                            nth_upt[of "Suc x'" "(k mod (y' - x'))" "Suc y'", OF mod_arith1(3)[OF Suc_xy, of k]]
                            runE_Suc[OF lang(2), of "(x' + k mod (y' - x'))"] 
                unfolding add_Suc by auto .
            by auto . .
         qed
      qed
    qed
  qed
    
corollary omega_lasso_lang':"finite (NBA.nodes A) \<Longrightarrow> NBA.language A \<noteq> {} \<longleftrightarrow> (\<exists>v u. v @- srepeat u \<in> NBA.language A \<and> u \<noteq> [])"
  using omega_lasso_lang by auto
corollary omega_lasso_lang'':"finite (NBA.nodes A) \<Longrightarrow> NBA.language A = {} \<longleftrightarrow> (\<forall>v u. v @- srepeat u \<notin> NBA.language A)"
  using omega_lasso_lang by auto


(*Prop 1: Given two Buechi automata A1 and A2, 
  To prove "Lang(A1) subset Lang(A2)":
  it suffices that all omega-lasso words accepted by Lang(A1) is also accepted by Lang(A2), 
  where an infinite word w is called "omega-lasso" if it has the form v . u^omega, 
  i.e., some prefix followed by a (non-empty) omega-cycle.
*)


lemma prop1:
  assumes "NBA.alphabet A \<subseteq> NBA.alphabet B"
  assumes "finite (NBA.nodes A)" "finite (NBA.nodes B)"
  assumes "\<And>v u. u \<noteq> [] \<Longrightarrow> v @- srepeat u \<in> NBA.language A \<Longrightarrow> v @- srepeat u \<in> NBA.language B"
  shows "NBA.language A \<subseteq> NBA.language B"
proof(rule ccontr)
  assume "\<not> NBA.language A \<subseteq> NBA.language B"
  then obtain w where w_in:"w \<in> NBA.language A" and w_nin:"w \<notin> NBA.language B" by auto
  hence "w \<in> NBA.language (complement B)"
    using assms by (meson language_ranking nba.language_alphabet ranking_complement
        streams_mono subset_iff)

  also have fin:"finite (NBA.nodes (intersect A (complement B)))"
    using intersect_nodes_finite[OF assms(2) complement_finite[OF assms(3)]] by auto

  moreover have "NBA.language (intersect A (complement B)) \<noteq> {}" using calculation w_in by auto

  ultimately obtain v u where vu:"v @- srepeat u \<in> NBA.language (intersect A (complement B))" "u \<noteq>[]"
    using omega_lasso_lang'[OF fin] by auto

  hence "v @- srepeat u \<in> NBA.language A \<and> v @- srepeat u \<notin> NBA.language B"
    by (simp add: assms(3) complement_language)

  thus "HOL.False" using assms(4)[OF vu(2)] by auto
qed

corollary prop1':
  assumes "NBA.alphabet A \<subseteq> NBA.alphabet B"
  assumes "finite (NBA.nodes A)" "finite (NBA.nodes B)"
  assumes "\<not>(NBA.language A \<subseteq> NBA.language B)"
  shows "\<exists>v u. v @- srepeat u \<in> NBA.language A \<and> v @- srepeat u \<notin> NBA.language B \<and> u \<noteq> []"
        
  using prop1[OF assms(1,2,3)] assms(4) by auto

end 