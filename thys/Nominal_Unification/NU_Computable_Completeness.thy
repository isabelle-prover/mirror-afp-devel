(*<*)
theory NU_Computable_Completeness
  imports NU_Computable_Soundness
begin
(*>*)

section \<open>Completeness of the computable algorithm\<close>

text\<open>One unfolding of a failing \<open>sred_fun\<close> either hits a failure pattern or performs an \<open>s_red\<close> step
after which \<open>sred_fun\<close> still fails.\<close>

lemma sred_fun_unfold_none:
  assumes "sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) = None"
  shows "fail ((t1 \<approx>? t2) # xs, ys) \<or> 
         (\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None)"
proof -
  \<comment> \<open>Unfold \<open>sred_fun\<close> exactly once: H is the case distinction of the definition, whose 
     value is None. From now on \<open>sred_fun\<close> is never unfolded again.\<close>
  note H = trans[OF sred_fun.simps(2)[symmetric] assms]
  \<comment> \<open>The goal has two ways out: either the problem is a failure pattern (a fail fact),
     or one \<open>s_red\<close> step leads to a problem on which \<open>sred_fun\<close> still fails.\<close>
  show ?thesis
  proof (cases t1)
    case Unit
    show ?thesis
    proof (cases t2)
      case Unit
      \<comment> \<open>Rule \<open>unit_sred\<close>: the equation is removed, the recursive call fails.\<close>
      have "sred_fun ((xs, ys), nabla, [] \<bullet> s) = None"
        using H unfolding \<open>t1 = Unit\<close> \<open>t2 = Unit\<close> by (simp del: sred_fun.simps)
      then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
        using unit_sred unfolding \<open>t1 = Unit\<close> \<open>t2 = Unit\<close> by blast
      then show ?thesis by simp
    next
      case (Susp pi X)
      \<comment> \<open>Rule \<open>var_2_sred\<close>: X is instantiated with Unit, the recursive call fails.\<close>
      let ?\<sigma> = "[(X, swap (rev pi) Unit)]"
      have step: "((Unit \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
        using var_2_sred by (simp del: swap.simps)
      have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = None"
        using H unfolding \<open>t1 = Unit\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
      then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
        using step unfolding \<open>t1 = Unit\<close> \<open>t2 = Susp pi X\<close> by blast
      then show ?thesis by simp
    next
      case (Atom b)
      \<comment> \<open>Clash: Unit vs. Atom.\<close>
      have "fail ((Unit \<approx>? Atom b) # xs, ys)"
        using fail_sym[OF fail_atom_unit] by simp
      then show ?thesis unfolding \<open>t1 = Unit\<close> \<open>t2 = Atom b\<close>
        by simp
    next
      case (Paar v1 v2)
      \<comment> \<open>Clash: Unit vs. Paar.\<close>
      have "fail ((Unit \<approx>? Paar v1 v2) # xs, ys)"
        using fail_sym[OF fail_paar_unit] by simp
      then show ?thesis unfolding \<open>t1 = Unit\<close> \<open>t2 = Paar v1 v2\<close>
        by simp
    next
      case (Func G v)
      \<comment> \<open>Clash: Unit vs. Func.\<close>
      have "fail ((Unit \<approx>? Func G v) # xs, ys)"
        using fail_sym[OF fail_func_unit] by simp
      then show ?thesis unfolding \<open>t1 = Unit\<close> \<open>t2 = Func G v\<close>
        by simp
    next
      case (Abst b v)
      \<comment> \<open>Clash: Unit vs. Abst.\<close>
      have "fail ((Unit \<approx>? Abst b v) # xs, ys)"
        using fail_sym[OF fail_abst_unit] by simp
      then show ?thesis unfolding \<open>t1 = Unit\<close> \<open>t2 = Abst b v\<close>
        by simp
    qed
  next
    case (Atom a)
    show ?thesis
    proof (cases t2)
      case (Atom b)
      show ?thesis
      proof (cases "a = b")
        case True
        \<comment> \<open>Rule \<open>atom_sred\<close>: equal atoms are removed, the recursive call fails.\<close>
        have "sred_fun ((xs, ys), nabla, [] \<bullet> s) = None"
          using H unfolding \<open>t1 = Atom a\<close> \<open>t2 = Atom b\<close> \<open>a = b\<close> by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using atom_sred unfolding \<open>t1 = Atom a\<close> \<open>t2 = Atom b\<close> \<open>a = b\<close> by blast
        then show ?thesis by simp
      next
        case False
        \<comment> \<open>Clash: different atoms.\<close>
        have "fail ((Atom a \<approx>? Atom b) # xs, ys)"
          using False fail_diff_atoms by simp
        then show ?thesis unfolding \<open>t1 = Atom a\<close> \<open>t2 = Atom b\<close>
          by simp
      qed
    next
      case (Susp pi X)
      \<comment> \<open>Rule \<open>var_2_sred\<close>: X is instantiated with the (permuted) atom.\<close>
      let ?\<sigma> = "[(X, swap (rev pi) (Atom a))]"
      have step: "((Atom a \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
        using var_2_sred by (simp del: swap.simps)
      have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = None"
        using H unfolding \<open>t1 = Atom a\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
      then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
        using step unfolding \<open>t1 = Atom a\<close> \<open>t2 = Susp pi X\<close> by blast
      then show ?thesis by simp
    next
      case Unit
      \<comment> \<open>Clash: Atom vs. Unit.\<close>
      have "fail ((Atom a \<approx>? Unit) # xs, ys)"
        using fail_atom_unit by simp
      then show ?thesis unfolding \<open>t1 = Atom a\<close> \<open>t2 = Unit\<close>
        by simp
    next
      case (Paar v1 v2)
      \<comment> \<open>Clash: Atom vs. Paar.\<close>
      have "fail ((Atom a \<approx>? Paar v1 v2) # xs, ys)"
        using fail_atom_paar by simp
      then show ?thesis unfolding \<open>t1 = Atom a\<close> \<open>t2 = Paar v1 v2\<close>
        by simp
    next
      case (Func G v)
      \<comment> \<open>Clash: Atom vs. Func.\<close>
      have "fail ((Atom a \<approx>? Func G v) # xs, ys)"
        using fail_sym[OF fail_func_atom] by simp
      then show ?thesis unfolding \<open>t1 = Atom a\<close> \<open>t2 = Func G v\<close>
        by simp
    next
      case (Abst b v)
      \<comment> \<open>Clash: Atom vs. Abst.\<close>
      have "fail ((Atom a \<approx>? Abst b v) # xs, ys)"
        using fail_sym[OF fail_abst_atom] by simp
      then show ?thesis unfolding \<open>t1 = Atom a\<close> \<open>t2 = Abst b v\<close>
        by simp
    qed
  next
    case (Paar u1 u2)
    show ?thesis
    proof (cases t2)
      case (Paar v1 v2)
      \<comment> \<open>Rule \<open>paar_sred\<close>: split into two equations, the recursive call fails.\<close>
      have "sred_fun (((u1 \<approx>? v1) # (u2 \<approx>? v2) # xs, ys), nabla, [] \<bullet> s) = None"
        using H unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Paar v1 v2\<close> by (simp del: sred_fun.simps)
      then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
        using paar_sred unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Paar v1 v2\<close> by blast
      then show ?thesis by simp
    next
      case (Susp pi X)
      show ?thesis
      proof (cases "occurs X (Paar u1 u2)")
        case True
        \<comment> \<open>Occurs check fails.\<close>
        have "fail ((Susp pi X \<approx>? Paar u1 u2) # xs, ys)"
          using True fail_occur_paar by (simp split: if_splits)
        then have "fail ((Paar u1 u2 \<approx>? Susp pi X) # xs, ys)"
          using fail_sym by simp
        then show ?thesis unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Susp pi X\<close>
          by simp
      next
        case False
        \<comment> \<open>Rule \<open>var_2_sred\<close>: X is instantiated with the pair, the recursive call fails.\<close>
        let ?\<sigma> = "[(X, swap (rev pi) (Paar u1 u2))]"
        have step: "((Paar u1 u2 \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
          using False var_2_sred by (simp del: swap.simps)
        have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = None"
          using H False unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using step unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Susp pi X\<close> by blast
        then show ?thesis by simp
      qed
    next
      case Unit
      \<comment> \<open>Clash: Paar vs. Unit.\<close>
      have "fail ((Paar u1 u2 \<approx>? Unit) # xs, ys)"
        using fail_paar_unit by simp
      then show ?thesis unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Unit\<close>
        by simp
    next
      case (Atom b)
      \<comment> \<open>Clash: Paar vs. Atom.\<close>
      have "fail ((Paar u1 u2 \<approx>? Atom b) # xs, ys)"
        using fail_sym[OF fail_atom_paar] by simp
      then show ?thesis unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Atom b\<close>
        by simp
    next
      case (Func G v)
      \<comment> \<open>Clash: Paar vs. Func.\<close>
      have "fail ((Paar u1 u2 \<approx>? Func G v) # xs, ys)"
        using fail_sym[OF fail_func_paar] by simp
      then show ?thesis unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Func G v\<close>
        by simp
    next
      case (Abst b v)
      \<comment> \<open>Clash: Paar vs. Abst.\<close>
      have "fail ((Paar u1 u2 \<approx>? Abst b v) # xs, ys)"
        using fail_sym[OF fail_abst_paar] by simp
      then show ?thesis unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Abst b v\<close>
        by simp
    qed
  next
    case (Func F u)
    show ?thesis
    proof (cases t2)
      case (Func G v)
      show ?thesis
      proof (cases "F = G")
        case True
        \<comment> \<open>Rule \<open>func_sred\<close>: compare the arguments, the recursive call fails.\<close>
        have "sred_fun (((u \<approx>? v) # xs, ys), nabla, [] \<bullet> s) = None"
          using H unfolding \<open>t1 = Func F u\<close> \<open>t2 = Func G v\<close> \<open>F = G\<close> by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using func_sred unfolding \<open>t1 = Func F u\<close> \<open>t2 = Func G v\<close> \<open>F = G\<close> by blast
        then show ?thesis by simp
      next
        case False
        \<comment> \<open>Clash: different function symbols.\<close>
        have "fail ((Func F u \<approx>? Func G v) # xs, ys)"
          using False fail_diff_func by simp
        then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Func G v\<close>
          by simp
      qed
    next
      case (Susp pi X)
      show ?thesis
      proof (cases "occurs X (Func F u)")
        case True
        \<comment> \<open>Occurs check fails.\<close>
        have "fail ((Susp pi X \<approx>? Func F u) # xs, ys)"
          using True fail_occur_func by (simp split: if_splits)
        then have "fail ((Func F u \<approx>? Susp pi X) # xs, ys)"
          using fail_sym by simp
        then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Susp pi X\<close>
          by simp
      next
        case False
        \<comment> \<open>Rule \<open>var_2_sred\<close>: X is instantiated with the function application.\<close>
        let ?\<sigma> = "[(X, swap (rev pi) (Func F u))]"
        have step: "((Func F u \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
          using False var_2_sred by (simp del: swap.simps)
        have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = None"
          using H False unfolding \<open>t1 = Func F u\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using step unfolding \<open>t1 = Func F u\<close> \<open>t2 = Susp pi X\<close> by blast
        then show ?thesis by simp
      qed
    next
      case Unit
      \<comment> \<open>Clash: Func vs. Unit.\<close>
      have "fail ((Func F u \<approx>? Unit) # xs, ys)"
        using fail_func_unit by simp
      then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Unit\<close>
        by simp
    next
      case (Atom b)
      \<comment> \<open>Clash: Func vs. Atom.\<close>
      have "fail ((Func F u \<approx>? Atom b) # xs, ys)"
        using fail_func_atom by simp
      then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Atom b\<close>
        by simp
    next
      case (Paar v1 v2)
      \<comment> \<open>Clash: Func vs. Paar.\<close>
      have "fail ((Func F u \<approx>? Paar v1 v2) # xs, ys)"
        using fail_func_paar by simp
      then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Paar v1 v2\<close>
        by simp
    next
      case (Abst b v)
      \<comment> \<open>Clash: Func vs. Abst.\<close>
      have "fail ((Func F u \<approx>? Abst b v) # xs, ys)"
        using fail_func_abst by simp
      then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Abst b v\<close>
        by simp
    qed
  next
    case (Abst a u)
    show ?thesis
    proof (cases t2)
      case (Abst b v)
      show ?thesis
      proof (cases "a = b")
        case True
        \<comment> \<open>Rule \<open>abst_aa_sred\<close>: same binder, compare the bodies.\<close>
        have "sred_fun (((u \<approx>? v) # xs, ys), nabla, [] \<bullet> s) = None"
          using H unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> \<open>a = b\<close> by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using abst_aa_sred unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> \<open>a = b\<close> by blast
        then show ?thesis by simp
      next
        case False
        \<comment> \<open>Rule \<open>abst_ab_sred\<close>: different binders, swap in the right body and add \<open>a # v\<close>.\<close>
        have step: "((Abst a u \<approx>? Abst b v) # xs, ys) \<turnstile> [] \<leadsto> ((u \<approx>? swap [(a, b)] v) # xs, (a \<sharp>? v) # ys)"
          using False abst_ab_sred by simp
        have "sred_fun (((u \<approx>? swap [(a, b)] v) # xs, (a \<sharp>? v) # ys), nabla, [] \<bullet> s) = None"
          using H False unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using step unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> by blast
        then show ?thesis by simp
      qed
    next
      case (Susp pi X)
      show ?thesis
      proof (cases "occurs X (Abst a u)")
        case True
        \<comment> \<open>Occurs check fails.\<close>
        have "fail ((Susp pi X \<approx>? Abst a u) # xs, ys)"
          using True fail_occur_abst by (simp split: if_splits)
        then have "fail ((Abst a u \<approx>? Susp pi X) # xs, ys)"
          using fail_sym by simp
        then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Susp pi X\<close>
          by simp
      next
        case False
        \<comment> \<open>Rule \<open>var_2_sred\<close>: X is instantiated with the abstraction.\<close>
        let ?\<sigma> = "[(X, swap (rev pi) (Abst a u))]"
        have step: "((Abst a u \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
          using False var_2_sred by (simp del: swap.simps)
        have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = None"
          using H False unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using step unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Susp pi X\<close> by blast
        then show ?thesis by simp
      qed
    next
      case Unit
      \<comment> \<open>Clash: Abst vs. Unit.\<close>
      have "fail ((Abst a u \<approx>? Unit) # xs, ys)"
        using fail_abst_unit by simp
      then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Unit\<close>
        by simp
    next
      case (Atom b)
      \<comment> \<open>Clash: Abst vs. Atom.\<close>
      have "fail ((Abst a u \<approx>? Atom b) # xs, ys)"
        using fail_abst_atom by simp
      then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Atom b\<close>
        by simp
    next
      case (Paar v1 v2)
      \<comment> \<open>Clash: Abst vs. Paar.\<close>
      have "fail ((Abst a u \<approx>? Paar v1 v2) # xs, ys)"
        using fail_abst_paar by simp
      then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Paar v1 v2\<close>
        by simp
    next
      case (Func G v)
      \<comment> \<open>Clash: Abst vs. Func.\<close>
      have "fail ((Abst a u \<approx>? Func G v) # xs, ys)"
        using fail_sym[OF fail_func_abst] by simp
      then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Func G v\<close>
        by simp
    qed
  next
    case (Susp pi X)
    \<comment> \<open>Left-hand side is a suspension: unless both sides are suspensions of the same
       variable or the occurs check fails, the step is \<open>var_1_sred\<close>.\<close>
    have var_1: "\<not> occurs X t2 \<Longrightarrow> sred_fun (apply_subst [(X, swap (rev pi) t2)] (xs, ys), nabla, 
                           [(X, swap (rev pi) t2)] \<bullet> s) = None \<Longrightarrow> ?thesis"
    proof -
      assume nocc: "\<not> occurs X t2"
        and rec: "sred_fun (apply_subst [(X, swap (rev pi) t2)] (xs, ys), nabla, 
                           [(X, swap (rev pi) t2)] \<bullet> s) = None"
      have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
        using var_1_sred[OF nocc] rec unfolding \<open>t1 = Susp pi X\<close> by blast
      then show ?thesis by simp
    qed
    show ?thesis
    proof (cases t2)
      case (Susp pi2 Y)
      show ?thesis
      proof (cases "X = Y")
        case True
        \<comment> \<open>Rule \<open>susp_sred\<close>: same variable, freshness constraints for the disagreement set.\<close>
        have "sred_fun ((xs, map (\<lambda>a. a \<sharp>? Susp [] X) (ds_list pi pi2) @ ys), nabla, [] \<bullet> s) = None"
          using H unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Susp pi2 Y\<close> \<open>X = Y\<close>[symmetric] 
          by (simp del: sred_fun.simps)
        then have "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
          using susp_sred unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Susp pi2 Y\<close> \<open>X = Y\<close>[symmetric] by blast
        then show ?thesis by simp
      next
        case False
        \<comment> \<open>Different variables: \<open>var_1_sred\<close>, the occurs check holds trivially.\<close>
        have nocc: "\<not> occurs X t2"
          using False unfolding \<open>t2 = Susp pi2 Y\<close> by simp
        have rec: "sred_fun (apply_subst [(X, swap (rev pi) t2)] (xs, ys), nabla,
                             [(X, swap (rev pi) t2)] \<bullet> s) = None"
          using H False unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Susp pi2 Y\<close>
          by (simp del: sred_fun.simps)
        show ?thesis
          using var_1[OF nocc rec] by simp
      qed
    next
      case Unit
      \<comment> \<open>Rule \<open>var_1_sred\<close>: X is instantiated with Unit.\<close>
      show ?thesis
        using H by (intro var_1) (simp_all add: \<open>t1 = Susp pi X\<close> \<open>t2 = Unit\<close> del: sred_fun.simps)
    next
      case (Atom b)
      \<comment> \<open>Rule \<open>var_1_sred\<close>: X is instantiated with the (permuted) atom.\<close>
      show ?thesis
        using H by (intro var_1) (simp_all add: \<open>t1 = Susp pi X\<close> \<open>t2 = Atom b\<close> del: sred_fun.simps)
    next
      case (Paar v1 v2)
      show ?thesis
      proof (cases "occurs X (Paar v1 v2)")
        case True
        \<comment> \<open>Occurs check fails.\<close>
        have "fail ((Susp pi X \<approx>? Paar v1 v2) # xs, ys)"
          using True fail_occur_paar by (simp split: if_splits)
        then show ?thesis unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Paar v1 v2\<close>
          by simp
      next
        case False
        \<comment> \<open>Rule \<open>var_1_sred\<close>: X is instantiated with the pair.\<close>
        show ?thesis
          using H False by (intro var_1) (simp_all add: \<open>t1 = Susp pi X\<close> \<open>t2 = Paar v1 v2\<close> del: sred_fun.simps)
      qed
    next
      case (Func G v)
      show ?thesis
      proof (cases "occurs X (Func G v)")
        case True
        \<comment> \<open>Occurs check fails.\<close>
        have "fail ((Susp pi X \<approx>? Func G v) # xs, ys)"
          using True fail_occur_func by (simp split: if_splits)
        then show ?thesis unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Func G v\<close>
          by simp
      next
        case False
        \<comment> \<open>Rule \<open>var_1_sred\<close>: X is instantiated with the function application.\<close>
        show ?thesis
          using H False by (intro var_1) (simp_all add: \<open>t1 = Susp pi X\<close> \<open>t2 = Func G v\<close> del: sred_fun.simps)
      qed
    next
      case (Abst b v)
      show ?thesis
      proof (cases "occurs X (Abst b v)")
        case True
        \<comment> \<open>Occurs check fails.\<close>
        have "fail ((Susp pi X \<approx>? Abst b v) # xs, ys)"
          using True fail_occur_abst by (simp split: if_splits)
        then show ?thesis unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Abst b v\<close>
          by simp
      next
        case False
        \<comment> \<open>Rule \<open>var_1_sred\<close>: X is instantiated with the abstraction.\<close>
        show ?thesis
          using H False by (intro var_1) (simp_all add: \<open>t1 = Susp pi X\<close> \<open>t2 = Abst b v\<close> del: sred_fun.simps)
      qed
    qed
  qed
qed

text\<open>If \<open>sred_fun\<close> fails, the problem has no solution.\<close>

lemma sred_fun_none_empty:
  assumes "sred_fun (P, nabla, s) = None"
  shows "U P = {}"
  using assms
proof(induct P arbitrary: s rule: wf_induct[OF wf_rank_r])
  case (1 P)
  obtain eqs ys where P_def: "P = (eqs, ys)" by (cases P)
  show ?case
  proof(cases eqs)
    case Nil
    then show ?thesis using 1(2) P_def by simp
  next
    case (Cons e xs)
    obtain t1 t2 where e_def: "e = (t1 \<approx>? t2)" by (cases e)
    have H: "sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) = None"
      using 1(2) unfolding P_def Cons e_def by simp
    have "fail P \<or> (\<exists>\<sigma> Q. P \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None)"
      using sred_fun_unfold_none[OF H] unfolding P_def Cons e_def by simp
    then show ?thesis
    proof
      assume "fail P"
      then show ?thesis using fail_then_empty by simp
    next
      assume "\<exists>\<sigma> Q. P \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
      then obtain \<sigma> Q where step: "P \<turnstile> \<sigma> \<leadsto> Q" and rec: "sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
        by blast
      have "(Q, P) \<in> rank_r"
        using rank_r_sred[OF step] by simp
      hence "U Q = {}"
        using 1(1) rec by blast
      then show ?thesis 
        using u_empty_sred[OF step] by simp
    qed
  qed
qed

text\<open>If \<open>cred_fun\<close> fails, the (freshness) problem has no solution.\<close>

lemma cred_fun_none_empty:
  assumes "cred_fun ((xs, ys), nabla, s) = None" and "xs = []"
  shows "U ([], ys) = {}"
  using assms
proof(induct "((xs, ys), nabla, s)" arbitrary: xs ys nabla s rule: cred_fun.induct)
  case (1 xs a ys nabla s)
  then show ?case using u_empty_cred[OF unit_cred] by auto
next
  case (2 xs a t1 t2 ys nabla s)
  then show ?case using u_empty_cred[OF paar_cred] by auto
next
  case (3 xs a F t ys nabla s)
  then show ?case using u_empty_cred[OF func_cred] by auto
next
  case (4 xs a b t ys nabla s)
  then show ?case 
    using u_empty_cred[OF abst_aa_cred] u_empty_cred[OF abst_ab_cred]
    by (cases "a = b") auto
next
  case (5 xs a b ys nabla s)
  then show ?case 
    using u_empty_cred[OF atom_cred] fail_then_empty[OF fail_fresh_atom]
    by (cases "a = b") auto
next
  case (6 xs a pi X ys nabla s)
  then show ?case using u_empty_cred[OF susp_cred] by auto
next
  case (7 xs nabla s)
  then show ?case by simp
qed

lemma u_empty_sred_rtc:
  assumes "P1 \<turnstile> s \<leadsto>\<^sup>* P2" and "U P2 = {}"
  shows "U P1 = {}"
  using assms
proof(induct rule: sred_rtc.induct)
  case (sred_refl P1)
  then show ?case by simp
next
  case (sred_rtc_step P1 s1 P2 s2 P3)
  then have "U P2 = {}" by simp
  then show ?case using u_empty_sred[OF sred_rtc_step(1)] by simp
qed

text\<open>Completeness: whenever the algorithm fails, the problem has no solution.\<close>

theorem nomu_unify_none:
  assumes "nomu_unify P = None"
  shows "U P = {}"
proof(cases "sred_fun (P, {}, [])")
  case None
  then show ?thesis using sred_fun_none_empty by blast
next
  case (Some R)
  then obtain xs ys nabla0 s0 where S: "sred_fun (P, {}, []) = Some ((xs, ys), nabla0, s0)"
    by (cases R) auto
  have "xs = []"
    using sred_fun_some_fst_empty[OF S] by simp
  obtain s1 where rtc: "P \<turnstile> s1 \<leadsto>\<^sup>* ([], ys)"
    using sred_fun_sred_rtc[OF S] \<open>xs = []\<close> by auto
  show ?thesis
  proof(cases "cred_fun (([], ys), nabla0, s0)")
    case None
    then have "U ([], ys) = {}" 
      using cred_fun_none_empty by blast
    then show ?thesis 
      using u_empty_sred_rtc[OF rtc] by simp
  next
    case (Some C)
    then obtain P1 nabla1 s1' where C: "cred_fun (([], ys), nabla0, s0) = Some (P1, nabla1, s1')"
      by (cases C) auto
    have "P1 = ([],[])"
      using cred_fun_some_fst[OF C] cred_fun_some_snd_empty[OF C] by (cases P1) auto
    hence "nomu_unify P = Some (nabla1, s1')"
      using S C \<open>xs = []\<close> by simp
    then show ?thesis using assms by simp
  qed
qed

text\<open>Together with soundness: the algorithm fails exactly on the problems without solutions.\<close>

corollary nomu_unify_none_iff:
  shows "nomu_unify P = None \<longleftrightarrow> U P = {}"
proof
  assume "nomu_unify P = None"
  then show "U P = {}" using nomu_unify_none by simp
next
  assume "U P = {}"
  show "nomu_unify P = None"
  proof(rule ccontr)
    assume "nomu_unify P \<noteq> None"
    then obtain nabla s where "nomu_unify P = Some (nabla, s)" by auto
    then have "(nabla, s) \<in> U P" using nomu_unify_sound by simp
    then show False using \<open>U P = {}\<close> by simp
  qed
qed

text\<open>Completeness in the style of @{thm [source] completeness}: whenever a problem has a
solution, the algorithm returns a result that is an idempotent most general unifier.\<close>

theorem nomu_unify_complete:
  assumes "U P \<noteq> {}"
  shows "\<exists>nabla s. nomu_unify P = Some (nabla, s) \<and> mgu P (nabla, s) \<and> idem (nabla, s)"
proof-
  obtain nabla s where res: "nomu_unify P = Some (nabla, s)"
    using assms nomu_unify_none_iff by (cases "nomu_unify P") auto
  moreover have "mgu P (nabla, s)" "idem (nabla, s)"
    using nomu_unify_sound[OF res] by simp+
  ultimately show ?thesis using res by blast
qed


(*<*)
end
(*>*)
