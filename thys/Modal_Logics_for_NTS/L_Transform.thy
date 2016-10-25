theory L_Transform
imports
  Transition_System
  FL_Transition_System
begin

section \<open>\texorpdfstring{$L$}{L}-Transform\<close>

subsection \<open>States\<close>

text \<open>The intuition is that states of kind~@{text AC} can perform ordinary actions, and states of
kind~@{text EF} can commit effects.\<close>

datatype ('state,'effect) L_state =
    AC "'effect fs_set \<times> 'state"
  | EF "'effect fs_set \<times> 'state"

instantiation L_state :: (pt,pt) pt
begin

  fun permute_L_state :: "perm \<Rightarrow> ('a,'b) L_state \<Rightarrow> ('a,'b) L_state" where
    "p \<bullet> (AC x) = AC (p \<bullet> x)"
  | "p \<bullet> (EF x) = EF (p \<bullet> x)"

  instance
  proof
    fix x :: "('a,'b) L_state"
    show "0 \<bullet> x = x" by (cases x, simp_all)
  next
    fix p q and x :: "('a,'b) L_state"
    show "(p + q) \<bullet> x = p \<bullet> q \<bullet> x" by (cases x, simp_all)
  qed

end

declare permute_L_state.simps [eqvt]

lemma supp_AC [simp]: "supp (AC x) = supp x"
unfolding supp_def by simp

lemma supp_EF [simp]: "supp (EF x) = supp x"
unfolding supp_def by simp

instantiation L_state :: (fs,fs) fs
begin

  instance
  proof
    fix x :: "('a,'b) L_state"
    show "finite (supp x)"
      by (cases x) (simp add: finite_supp)+
  qed

end


subsection \<open>Actions and binding names\<close>

datatype ('act,'effect) L_action =
    Act 'act
  | Eff 'effect

instantiation L_action :: (pt,pt) pt
begin

  fun permute_L_action :: "perm \<Rightarrow> ('a,'b) L_action \<Rightarrow> ('a,'b) L_action" where
    "p \<bullet> (Act \<alpha>) = Act (p \<bullet> \<alpha>)"
  | "p \<bullet> (Eff f) = Eff (p \<bullet> f)"

  instance
  proof
    fix x :: "('a,'b) L_action"
    show "0 \<bullet> x = x" by (cases x, simp_all)
  next
    fix p q and x :: "('a,'b) L_action"
    show "(p + q) \<bullet> x = p \<bullet> q \<bullet> x" by (cases x, simp_all)
  qed

end

declare permute_L_action.simps [eqvt]

lemma supp_Act [simp]: "supp (Act \<alpha>) = supp \<alpha>"
unfolding supp_def by simp

lemma supp_Eff [simp]: "supp (Eff f) = supp f"
unfolding supp_def by simp

instantiation L_action :: (fs,fs) fs
begin

  instance
  proof
    fix x :: "('a,'b) L_action"
    show "finite (supp x)"
      by (cases x) (simp add: finite_supp)+
  qed

end

instantiation L_action :: (bn,fs) bn
begin

  fun bn_L_action :: "('a,'b) L_action \<Rightarrow> atom set" where
    "bn_L_action (Act \<alpha>) = bn \<alpha>"
  | "bn_L_action (Eff _) = {}"

  instance
  proof
    fix p and \<alpha> :: "('a,'b) L_action"
    show "p \<bullet> bn \<alpha> = bn (p \<bullet> \<alpha>)"
      by (cases \<alpha>) (simp add: bn_eqvt, simp)
  next
    fix \<alpha> :: "('a,'b) L_action"
    show "finite (bn \<alpha>)"
      by (cases \<alpha>) (simp add: bn_finite, simp)
  qed

end


subsection \<open>Satisfaction\<close>

context effect_nominal_ts
begin

  fun L_satisfies :: "('state,'effect) L_state \<Rightarrow> 'pred \<Rightarrow> bool" (infix "\<turnstile>\<^sub>L" 70) where
    "AC (_,P) \<turnstile>\<^sub>L \<phi> \<longleftrightarrow> P \<turnstile> \<phi>"
  | "EF _     \<turnstile>\<^sub>L \<phi> \<longleftrightarrow> False"

  lemma L_satisfies_eqvt: assumes "P\<^sub>L \<turnstile>\<^sub>L \<phi>" shows "(p \<bullet> P\<^sub>L) \<turnstile>\<^sub>L (p \<bullet> \<phi>)"
  proof (cases P\<^sub>L)
    case (AC FP)
    with assms have "snd FP \<turnstile> \<phi>"
      by (metis L_satisfies.simps(1) prod.collapse)
    then have "snd (p \<bullet> FP) \<turnstile> p \<bullet> \<phi>"
      by (metis satisfies_eqvt snd_eqvt)
    then show ?thesis
      using AC by (metis L_satisfies.simps(1) permute_L_state.simps(1) prod.collapse)
  next
    case EF
    with assms have "False"
      by simp
    then show ?thesis ..
  qed

end


subsection \<open>Transitions\<close>

context effect_nominal_ts
begin

  fun L_transition :: "('state,'effect) L_state \<Rightarrow> (('act,'effect) L_action, ('state,'effect) L_state) residual \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>L" 70) where
    "AC (F,P) \<rightarrow>\<^sub>L \<alpha>P' \<longleftrightarrow> (\<exists>\<alpha> P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> \<alpha>P' = \<langle>Act \<alpha>, EF (L (\<alpha>,F), P')\<rangle> \<and> bn \<alpha> \<sharp>* F)" -- \<open>note the freshness condition\<close>
  | "EF (F,P) \<rightarrow>\<^sub>L \<alpha>P' \<longleftrightarrow> (\<exists>f. f \<in>\<^sub>f\<^sub>s F \<and> \<alpha>P' = \<langle>Eff f, AC (F, \<langle>f\<rangle>P)\<rangle>)"

  lemma L_transition_eqvt: assumes "P\<^sub>L \<rightarrow>\<^sub>L \<alpha>\<^sub>LP\<^sub>L'" shows "(p \<bullet> P\<^sub>L) \<rightarrow>\<^sub>L (p \<bullet> \<alpha>\<^sub>LP\<^sub>L')"
  proof (cases P\<^sub>L)
    case AC
    {
      fix F P
      assume *: "P\<^sub>L = AC (F,P)"
      with assms obtain \<alpha> P' where trans: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" and \<alpha>P': "\<alpha>\<^sub>LP\<^sub>L' = \<langle>Act \<alpha>, EF (L (\<alpha>,F), P')\<rangle>" and fresh: "bn \<alpha> \<sharp>* F"
        by auto
      from trans have "p \<bullet> P \<rightarrow> \<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle>"
        by (simp add: transition_eqvt')
      moreover from \<alpha>P' have "p \<bullet> \<alpha>\<^sub>LP\<^sub>L' = \<langle>Act (p \<bullet> \<alpha>), EF (L (p \<bullet> \<alpha>, p \<bullet> F), p \<bullet> P')\<rangle>"
        by (simp add: L_eqvt')
      moreover from fresh have "bn (p \<bullet> \<alpha>) \<sharp>* (p \<bullet> F)"
        by (metis bn_eqvt fresh_star_permute_iff)
      ultimately have "p \<bullet> P\<^sub>L \<rightarrow>\<^sub>L p \<bullet> \<alpha>\<^sub>LP\<^sub>L'"
        using "*" by auto
    }
    with AC show ?thesis
      by (metis prod.collapse)
  next
    case EF
    {
      fix F P
      assume *: "P\<^sub>L = EF (F,P)"
      with assms obtain f where "f \<in>\<^sub>f\<^sub>s F" and "\<alpha>\<^sub>LP\<^sub>L' = \<langle>Eff f, AC (F, \<langle>f\<rangle>P)\<rangle>"
        by auto
      then have "(p \<bullet> f) \<in>\<^sub>f\<^sub>s (p \<bullet> F)" and "p \<bullet> \<alpha>\<^sub>LP\<^sub>L' = \<langle>Eff (p \<bullet> f), AC (p \<bullet> F, \<langle>p \<bullet> f\<rangle>(p \<bullet> P))\<rangle>"
        by simp+
      then have "p \<bullet> P\<^sub>L \<rightarrow>\<^sub>L p \<bullet> \<alpha>\<^sub>LP\<^sub>L'"
        using "*" L_transition.simps(2) Pair_eqvt permute_L_state.simps(2) by force
    }
    with EF show ?thesis
      by (metis prod.collapse)
  qed

  text \<open>The binding names in the alpha-variant that witnesses the $L$-transition may be chosen fresh
  for any finitely supported context.\<close>

  lemma L_transition_AC_strong:
    assumes "finite (supp X)" and "AC (F,P) \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle>"
    shows "\<exists>\<alpha> P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F), P')\<rangle> \<and> bn \<alpha> \<sharp>* X"
  using assms proof -
    from `AC (F,P) \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle>` obtain \<alpha> P' where transition: "P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" and alpha: "\<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F), P')\<rangle>" and fresh: "bn \<alpha> \<sharp>* F"
      by (metis L_transition.simps(1))
    let ?Act = "Act \<alpha> :: ('act,'effect) L_action" -- \<open>the type annotation prevents a type that is too polymorphic and doesn't fix~@{typ 'effect}\<close>
    have "finite (bn \<alpha>)"
      by (fact bn_finite)
    moreover note `finite (supp X)`
    moreover have "finite (supp (\<langle>?Act, EF (L (\<alpha>,F), P')\<rangle>, \<langle>\<alpha>,P'\<rangle>, F))"
      by (metis finite_Diff finite_UnI finite_supp supp_Pair supp_abs_residual_pair)
    moreover from fresh have "bn \<alpha> \<sharp>* (\<langle>?Act, EF (L (\<alpha>,F), P')\<rangle>, \<langle>\<alpha>,P'\<rangle>, F)"
      by (auto simp add: fresh_star_def fresh_def supp_Pair supp_abs_residual_pair)
    ultimately obtain p where fresh_X: "(p \<bullet> bn \<alpha>) \<sharp>* X" and "supp (\<langle>?Act, EF (L (\<alpha>,F), P')\<rangle>, \<langle>\<alpha>,P'\<rangle>, F) \<sharp>* p"
      by (metis at_set_avoiding2)
    then have "supp \<langle>?Act, EF (L (\<alpha>,F), P')\<rangle> \<sharp>* p" and "supp \<langle>\<alpha>,P'\<rangle> \<sharp>* p" and "supp F \<sharp>* p"
      by (metis fresh_star_Un supp_Pair)+
    then have "p \<bullet> \<langle>?Act, EF (L (\<alpha>,F), P')\<rangle> = \<langle>?Act, EF (L (\<alpha>,F), P')\<rangle>" and "p \<bullet> \<langle>\<alpha>,P'\<rangle> = \<langle>\<alpha>,P'\<rangle>" and "p \<bullet> F = F"
      by (metis supp_perm_eq)+
    then have "\<langle>Act (p \<bullet> \<alpha>), EF (L (p \<bullet> \<alpha>, F), p \<bullet> P')\<rangle> = \<langle>?Act, EF (L (\<alpha>,F), P')\<rangle>" and "\<langle>p \<bullet> \<alpha>, p \<bullet> P'\<rangle> = \<langle>\<alpha>,P'\<rangle>"
      using permute_L_action.simps(1) permute_L_state.simps(2) abs_residual_pair_eqvt L_eqvt' Pair_eqvt by auto
    then show "\<exists>\<alpha> P'. P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<and> \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F), P')\<rangle> \<and> bn \<alpha> \<sharp>* X"
      using transition and alpha and fresh_X by (metis bn_eqvt)
  qed

end


subsection \<open>\texorpdfstring{$L$}{L}-transform (interpretation) and bisimilarity\<close>

context effect_nominal_ts
begin

  interpretation L_transform: nominal_ts "op \<turnstile>\<^sub>L" "op \<rightarrow>\<^sub>L"
  by unfold_locales (fact L_satisfies_eqvt, fact L_transition_eqvt)

  notation L_transform.bisimilar (infix "\<sim>\<cdot>\<^sub>L" 100)

  text \<open>$F/L$-bisimilarity is equivalent to bisimilarity in the $L$-transform.\<close>

  inductive L_bisimilar :: "('state,'effect) L_state \<Rightarrow> ('state,'effect) L_state \<Rightarrow> bool" where
    "P \<sim>\<cdot>[F] Q \<Longrightarrow> L_bisimilar (EF (F,P)) (EF (F,Q))"
  | "P \<sim>\<cdot>[F] Q \<Longrightarrow> f \<in>\<^sub>f\<^sub>s F \<Longrightarrow> L_bisimilar (AC (F, \<langle>f\<rangle>P)) (AC (F, \<langle>f\<rangle>Q))"

  lemma L_bisimilar_is_bisimulation: "L_transform.is_bisimulation L_bisimilar"
  unfolding L_transform.is_bisimulation_def
  proof
    show "symp L_bisimilar"
      by (metis FL_bisimilar_symp L_bisimilar.cases L_bisimilar.intros symp_def)
  next
    have "\<forall>P\<^sub>L Q\<^sub>L. L_bisimilar P\<^sub>L Q\<^sub>L \<longrightarrow> (\<forall>\<phi>. P\<^sub>L \<turnstile>\<^sub>L \<phi> \<longrightarrow> Q\<^sub>L \<turnstile>\<^sub>L \<phi>)" (is ?S)
      using FL_bisimilar_is_L_bisimulation L_bisimilar.simps is_L_bisimulation_def by auto
    moreover have "\<forall>P\<^sub>L Q\<^sub>L. L_bisimilar P\<^sub>L Q\<^sub>L \<longrightarrow> (\<forall>\<alpha>\<^sub>L P\<^sub>L'. bn \<alpha>\<^sub>L \<sharp>* Q\<^sub>L \<longrightarrow> P\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> \<longrightarrow> (\<exists>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<and> L_bisimilar P\<^sub>L' Q\<^sub>L'))" (is ?T)
      proof (clarify)
        fix P\<^sub>L Q\<^sub>L \<alpha>\<^sub>L P\<^sub>L'
        assume L_bisim: "L_bisimilar P\<^sub>L Q\<^sub>L" and fresh\<^sub>L: "bn \<alpha>\<^sub>L \<sharp>* Q\<^sub>L" and trans\<^sub>L: "P\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle>"
        obtain Q\<^sub>L' where "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle>" and "L_bisimilar P\<^sub>L' Q\<^sub>L'"
          using L_bisim proof (rule L_bisimilar.cases)
            fix P F Q
            assume P\<^sub>L: "P\<^sub>L = EF (F, P)" and Q\<^sub>L: "Q\<^sub>L = EF (F, Q)" and bisim: "P \<sim>\<cdot>[F] Q"
            from P\<^sub>L and trans\<^sub>L obtain f where effect: "f \<in>\<^sub>f\<^sub>s F" and \<alpha>\<^sub>LP\<^sub>L': "\<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Eff f, AC (F, \<langle>f\<rangle>P)\<rangle>"
              using L_transition.simps(2) by blast
            from Q\<^sub>L and effect have "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>Eff f, AC (F, \<langle>f\<rangle>Q)\<rangle>"
              using L_transition.simps(2) by blast
            moreover from bisim and effect have "L_bisimilar (AC (F, \<langle>f\<rangle>P)) (AC (F, \<langle>f\<rangle>Q))"
              using L_bisimilar.intros(2) by blast
            moreover from \<alpha>\<^sub>LP\<^sub>L' have "\<alpha>\<^sub>L = Eff f" and "P\<^sub>L' = AC (F, \<langle>f\<rangle>P)"
              by (metis bn_L_action.simps(2) residual_empty_bn_eq_iff)+
            ultimately show "thesis"
              using `\<And>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<Longrightarrow> L_bisimilar P\<^sub>L' Q\<^sub>L' \<Longrightarrow> thesis` by blast
          next
            fix P F Q f
            assume P\<^sub>L: "P\<^sub>L = AC (F, \<langle>f\<rangle>P)" and Q\<^sub>L: "Q\<^sub>L = AC (F, \<langle>f\<rangle>Q)" and bisim: "P \<sim>\<cdot>[F] Q" and effect: "f \<in>\<^sub>f\<^sub>s F"
            have "finite (supp (\<langle>f\<rangle>Q, F))"
              by (fact finite_supp)
            with P\<^sub>L and trans\<^sub>L obtain \<alpha> P' where trans_P: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>" and \<alpha>\<^sub>LP\<^sub>L': "\<langle>\<alpha>\<^sub>L,P\<^sub>L'\<rangle> = \<langle>Act \<alpha>, EF (L (\<alpha>,F), P')\<rangle>" and fresh: "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F)"
              by (metis L_transition_AC_strong)
            from bisim and effect and fresh and trans_P obtain Q' where trans_Q: "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle>" and bisim': "P' \<sim>\<cdot>[L (\<alpha>,F)] Q'"
              by (metis FL_bisimilar_simulation_step)
            from fresh have "bn \<alpha> \<sharp>* F"
              by (meson fresh_PairD(2) fresh_star_def)
            with Q\<^sub>L and trans_Q have trans_Q\<^sub>L: "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>Act \<alpha>, EF (L (\<alpha>,F), Q')\<rangle>"
              by (metis L_transition.simps(1))

            from \<alpha>\<^sub>LP\<^sub>L' obtain p where p: "(\<alpha>\<^sub>L,P\<^sub>L') = p \<bullet> (Act \<alpha>, EF (L (\<alpha>,F), P'))" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> bn \<alpha>\<^sub>L"
              by (metis (no_types, lifting) bn_L_action.simps(1) residual_eq_iff_perm_renaming)
            from supp_p and fresh and fresh\<^sub>L and Q\<^sub>L have "supp p \<sharp>* (\<langle>f\<rangle>Q, F)"
              unfolding fresh_star_def by (metis (no_types, hide_lams) Un_iff fresh_Pair fresh_def subsetCE supp_AC)
            then have p_fQ: "p \<bullet> \<langle>f\<rangle>Q = \<langle>f\<rangle>Q" and p_F: "p \<bullet> F = F"
              by (simp add: fresh_star_def perm_supp_eq)+
            from p and p_F have "\<alpha>\<^sub>L = Act (p \<bullet> \<alpha>)" and "P\<^sub>L' = EF (L (p \<bullet> \<alpha>, F), p \<bullet> P')"
              by auto

            moreover from Q\<^sub>L and p_fQ and p_F have "p \<bullet> Q\<^sub>L = Q\<^sub>L"
              by simp
            with trans_Q\<^sub>L have "Q\<^sub>L \<rightarrow>\<^sub>L p \<bullet> \<langle>Act \<alpha>, EF (L (\<alpha>,F), Q')\<rangle>"
              by (metis L_transform.transition_eqvt)
            then have "Q\<^sub>L \<rightarrow>\<^sub>L \<langle>Act (p \<bullet> \<alpha>), EF (L (p \<bullet> \<alpha>, F), p \<bullet> Q')\<rangle>"
              using p_F by simp

            moreover from bisim' have "(p \<bullet> P') \<sim>\<cdot>[L (p \<bullet> \<alpha>, F)] (p \<bullet> Q')"
              by (metis FL_bisimilar_eqvt L_eqvt' p_F)
            then have "L_bisimilar (EF (L (p \<bullet> \<alpha>, F), p \<bullet> P')) (EF (L (p \<bullet> \<alpha>, F), p \<bullet> Q'))"
              by (metis L_bisimilar.intros(1))

            ultimately show thesis
                using `\<And>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<Longrightarrow> L_bisimilar P\<^sub>L' Q\<^sub>L' \<Longrightarrow> thesis` by blast
          qed
        then show "\<exists>Q\<^sub>L'. Q\<^sub>L \<rightarrow>\<^sub>L \<langle>\<alpha>\<^sub>L,Q\<^sub>L'\<rangle> \<and> L_bisimilar P\<^sub>L' Q\<^sub>L'"
          by auto
      qed
    ultimately show "?S \<and> ?T"
      by metis
  qed

  definition invL_FL_bisimilar :: "'effect first \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
    "invL_FL_bisimilar F P Q \<equiv> EF (F,P) \<sim>\<cdot>\<^sub>L EF(F,Q)"

  lemma invL_FL_bisimilar_is_L_bisimulation: "is_L_bisimulation invL_FL_bisimilar"
  unfolding is_L_bisimulation_def
  proof
    fix F
    have "symp (invL_FL_bisimilar F)" (is ?R)
      by (metis L_transform.bisimilar_symp invL_FL_bisimilar_def symp_def)
    moreover have "\<forall>P Q. invL_FL_bisimilar F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<phi>. \<langle>f\<rangle>P \<turnstile> \<phi> \<longrightarrow> \<langle>f\<rangle>Q \<turnstile> \<phi>))" (is ?S)
      proof (clarify)
        fix P Q f \<phi>
        assume bisim: "invL_FL_bisimilar F P Q" and effect: "f \<in>\<^sub>f\<^sub>s F" and satisfies: "\<langle>f\<rangle>P \<turnstile> \<phi>"
        from bisim have "EF (F,P) \<sim>\<cdot>\<^sub>L EF (F,Q)"
          by (metis invL_FL_bisimilar_def)
        moreover have "bn (Eff f) \<sharp>* EF (F,Q)"
          by (simp add: fresh_star_def)
        moreover from effect have "EF (F,P) \<rightarrow>\<^sub>L \<langle>Eff f, AC (F, \<langle>f\<rangle>P)\<rangle>"
          by (metis L_transition.simps(2))
        ultimately obtain Q\<^sub>L' where trans: "EF (F,Q) \<rightarrow>\<^sub>L \<langle>Eff f, Q\<^sub>L'\<rangle>" and L_bisim: "AC (F, \<langle>f\<rangle>P) \<sim>\<cdot>\<^sub>L Q\<^sub>L'"
          by (metis L_transform.bisimilar_simulation_step)
        from trans obtain f' where "\<langle>Eff f :: ('act,'effect) L_action, Q\<^sub>L'\<rangle> = \<langle>Eff f', AC (F, \<langle>f'\<rangle>Q)\<rangle>"
          by (metis L_transition.simps(2))
        then have Q\<^sub>L': "Q\<^sub>L' = AC (F, \<langle>f\<rangle>Q)"
          by (metis L_action.inject(2) bn_L_action.simps(2) residual_empty_bn_eq_iff)

        from satisfies have "AC (F, \<langle>f\<rangle>P) \<turnstile>\<^sub>L \<phi>"
          by (metis L_satisfies.simps(1))
        with L_bisim and Q\<^sub>L' have "AC (F, \<langle>f\<rangle>Q) \<turnstile>\<^sub>L \<phi>"
          by (metis L_transform.bisimilar_is_bisimulation L_transform.is_bisimulation_def)
        then show "\<langle>f\<rangle>Q \<turnstile> \<phi>"
          by (metis L_satisfies.simps(1))
      qed
    moreover have "\<forall>P Q. invL_FL_bisimilar F P Q \<longrightarrow> (\<forall>f. f \<in>\<^sub>f\<^sub>s F \<longrightarrow> (\<forall>\<alpha> P'. bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F) \<longrightarrow>
        \<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle> \<longrightarrow> (\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> invL_FL_bisimilar (L (\<alpha>, F)) P' Q')))" (is ?T)
      proof (clarify)
        fix P Q f \<alpha> P'
        assume bisim: "invL_FL_bisimilar F P Q" and effect: "f \<in>\<^sub>f\<^sub>s F" and fresh: "bn \<alpha> \<sharp>* (\<langle>f\<rangle>Q, F)" and trans: "\<langle>f\<rangle>P \<rightarrow> \<langle>\<alpha>,P'\<rangle>"
        from bisim have "EF (F,P) \<sim>\<cdot>\<^sub>L EF (F,Q)"
          by (metis invL_FL_bisimilar_def)
        moreover have "bn (Eff f) \<sharp>* EF (F,Q)"
          by (simp add: fresh_star_def)
        moreover from effect have "EF (F,P) \<rightarrow>\<^sub>L \<langle>Eff f, AC (F, \<langle>f\<rangle>P)\<rangle>"
          by (metis L_transition.simps(2))
        ultimately obtain Q\<^sub>L' where trans\<^sub>L: "EF (F,Q) \<rightarrow>\<^sub>L \<langle>Eff f, Q\<^sub>L'\<rangle>" and L_bisim: "AC (F, \<langle>f\<rangle>P) \<sim>\<cdot>\<^sub>L Q\<^sub>L'"
          by (metis L_transform.bisimilar_simulation_step)
        from trans\<^sub>L obtain f' where "\<langle>Eff f :: ('act,'effect) L_action, Q\<^sub>L'\<rangle> = \<langle>Eff f', AC (F, \<langle>f'\<rangle>Q)\<rangle>"
          by (metis L_transition.simps(2))
        then have Q\<^sub>L': "Q\<^sub>L' = AC (F, \<langle>f\<rangle>Q)"
          by (metis L_action.inject(2) bn_L_action.simps(2) residual_empty_bn_eq_iff)

        from L_bisim and Q\<^sub>L' have "AC (F, \<langle>f\<rangle>P) \<sim>\<cdot>\<^sub>L AC (F, \<langle>f\<rangle>Q)"
          by metis
        moreover from fresh have "bn (Act \<alpha>) \<sharp>* AC (F, \<langle>f\<rangle>Q)"
          by (simp add: fresh_def fresh_star_def supp_Pair)
        moreover from fresh have "bn \<alpha> \<sharp>* F"
          by (simp add: fresh_star_Pair)
        with trans have "AC (F, \<langle>f\<rangle>P) \<rightarrow>\<^sub>L \<langle>Act \<alpha>, EF (L (\<alpha>,F), P')\<rangle>"
          by (metis L_transition.simps(1))
        ultimately obtain Q\<^sub>L'' where trans\<^sub>L': "AC (F, \<langle>f\<rangle>Q) \<rightarrow>\<^sub>L \<langle>Act \<alpha>, Q\<^sub>L''\<rangle>" and L_bisim': "EF (L (\<alpha>,F), P') \<sim>\<cdot>\<^sub>L Q\<^sub>L''"
          by (metis L_transform.bisimilar_simulation_step)

        have "finite (supp (\<langle>f\<rangle>Q, F))"
          by (fact finite_supp)
        with trans\<^sub>L' obtain \<alpha>' Q' where trans': "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>',Q'\<rangle>" and alpha: "\<langle>Act \<alpha> :: ('act,'effect) L_action, Q\<^sub>L''\<rangle> = \<langle>Act \<alpha>', EF (L (\<alpha>',F), Q')\<rangle>" and fresh': "bn \<alpha>' \<sharp>* (\<langle>f\<rangle>Q, F)"
          by (metis L_transition_AC_strong)

        from alpha obtain p where p: "(Act \<alpha> :: ('act,'effect) L_action, Q\<^sub>L'') = p \<bullet> (Act \<alpha>', EF (L (\<alpha>',F), Q'))" and supp_p: "supp p \<subseteq> bn \<alpha> \<union> bn \<alpha>'"
          by (metis Un_commute bn_L_action.simps(1) residual_eq_iff_perm_renaming)
        from supp_p and fresh and fresh' have "supp p \<sharp>* (\<langle>f\<rangle>Q, F)"
          unfolding fresh_star_def by (metis (no_types, hide_lams) Un_iff subsetCE)
        then have p_fQ: "p \<bullet> \<langle>f\<rangle>Q = \<langle>f\<rangle>Q" and p_F: "p \<bullet> F = F"
          by (simp add: fresh_star_def perm_supp_eq)+
        from p and p_F have p_\<alpha>': "p \<bullet> \<alpha>' = \<alpha>" and Q\<^sub>L'': "Q\<^sub>L'' = EF (L (p \<bullet> \<alpha>', F), p \<bullet> Q')"
          by auto

        from trans' and p_fQ and p_\<alpha>' have "\<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>, p \<bullet> Q'\<rangle>"
          by (metis transition_eqvt')
        moreover from L_bisim' and Q\<^sub>L'' and p_\<alpha>' have "invL_FL_bisimilar (L (\<alpha>, F)) P' (p \<bullet> Q')"
          by (metis invL_FL_bisimilar_def)
        ultimately show "\<exists>Q'. \<langle>f\<rangle>Q \<rightarrow> \<langle>\<alpha>,Q'\<rangle> \<and> invL_FL_bisimilar (L (\<alpha>, F)) P' Q'"
          by metis
      qed
    ultimately show "?R \<and> ?S \<and> ?T"
      by metis
  qed

  theorem "P \<sim>\<cdot>[F] Q \<longleftrightarrow> EF (F,P) \<sim>\<cdot>\<^sub>L EF(F,Q)"
  proof
    assume "P \<sim>\<cdot>[F] Q"
    then have "L_bisimilar (EF (F,P)) (EF (F,Q))"
        by (metis L_bisimilar.intros(1))
    then show "EF (F,P) \<sim>\<cdot>\<^sub>L EF(F,Q)"
      by (metis L_bisimilar_is_bisimulation L_transform.bisimilar_def)
  next
    assume "EF (F, P) \<sim>\<cdot>\<^sub>L EF (F, Q)"
    then have "invL_FL_bisimilar F P Q"
      by (metis invL_FL_bisimilar_def)
    then show "P \<sim>\<cdot>[F] Q"
      by (metis invL_FL_bisimilar_is_L_bisimulation FL_bisimilar_def)
  qed

end

end
