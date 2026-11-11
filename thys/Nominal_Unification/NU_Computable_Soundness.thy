(*<*)
theory NU_Computable_Soundness
  imports NU_Computable
begin
(*>*)

section \<open>Soundness of the computable algorithm\<close>

text\<open>\<open>sred_fun\<close> is simulated by the reflexive-transitive closure of the equational reductions.\<close>

text\<open>One unfolding of \<open>sred_fun\<close> on a non-empty equation list corresponds to one \<open>s_red\<close> step.\<close>

lemma sred_fun_unfold_step:
  assumes "sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) = Some r"
  shows "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = Some r"
proof -
  \<comment> \<open>Unfold \<open>sred_fun\<close> exactly once: H is the case distinction of the definition, whose 
     value is Some r. From now on \<open>sred_fun\<close> is never unfolded again.\<close>
  note H = trans[OF sred_fun.simps(2)[symmetric] assms]
  show ?thesis
  proof (cases t1)
    case Unit
    show ?thesis
    proof (cases t2)
      case Unit
      \<comment> \<open>Rule \<open>unit_sred\<close>: the equation is simply removed.\<close>
      have step: "((Unit \<approx>? Unit) # xs, ys) \<turnstile> [] \<leadsto> (xs, ys)"
        using unit_sred by simp
      have "sred_fun ((xs, ys), nabla, [] \<bullet> s) = Some r"
        using H unfolding \<open>t1 = Unit\<close> \<open>t2 = Unit\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Unit\<close> \<open>t2 = Unit\<close> using step by blast
    next
      case (Susp pi X)
      \<comment> \<open>Rule \<open>var_2_sred\<close>: X is instantiated with Unit.\<close>
      let ?\<sigma> = "[(X, swap (rev pi) Unit)]"
      have step: "((Unit \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
        using var_2_sred by (simp del: swap.simps)
      have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = Some r"
        using H unfolding \<open>t1 = Unit\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Unit\<close> \<open>t2 = Susp pi X\<close> using step by blast
    qed (use H Unit in \<open>simp_all del: sred_fun.simps\<close>) \<comment> \<open>clashes: \<open>sred_fun\<close> returns None\<close>
  next
    case (Atom a)
    show ?thesis
    proof (cases t2)
      case (Atom b)
      \<comment> \<open>Rule \<open>atom_sred\<close>: only applicable (and only Some) when a = b.\<close>
      have "a = b"
        using H \<open>t1 = Atom a\<close> \<open>t2 = Atom b\<close> by (simp del: sred_fun.simps split: if_splits)
      have step: "((Atom a \<approx>? Atom a) # xs, ys) \<turnstile> [] \<leadsto> (xs, ys)"
        using atom_sred by simp
      have "sred_fun ((xs, ys), nabla, [] \<bullet> s) = Some r"
        using H unfolding \<open>t1 = Atom a\<close> \<open>t2 = Atom b\<close> \<open>a = b\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Atom a\<close> \<open>t2 = Atom b\<close> \<open>a = b\<close> using step by blast
    next
      case (Susp pi X)
      \<comment> \<open>Rule \<open>var_2_sred\<close>: X is instantiated with the (permuted) atom.\<close>
      let ?\<sigma> = "[(X, swap (rev pi) (Atom a))]"
      have step: "((Atom a \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
        using var_2_sred by (simp del: swap.simps)
      have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = Some r"
        using H unfolding \<open>t1 = Atom a\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Atom a\<close> \<open>t2 = Susp pi X\<close> using step by blast
    qed (use H Atom in \<open>simp_all del: sred_fun.simps\<close>)
  next
    case (Paar u1 u2)
    show ?thesis
    proof (cases t2)
      case (Paar v1 v2)
      \<comment> \<open>Rule \<open>paar_sred\<close>: the pair equation is split into two equations.\<close>
      have step: "((Paar u1 u2 \<approx>? Paar v1 v2) # xs, ys) \<turnstile> [] \<leadsto> ((u1 \<approx>? v1) # (u2 \<approx>? v2) # xs, ys)"
        using paar_sred by simp
      have "sred_fun (((u1 \<approx>? v1) # (u2 \<approx>? v2) # xs, ys), nabla, [] \<bullet> s) = Some r"
        using H unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Paar v1 v2\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Paar v1 v2\<close> using step by blast
    next
      case (Susp pi X)
      \<comment> \<open>Rule \<open>var_2_sred\<close>: Some is only returned when the occurs check succeeds.\<close>
      have nocc: "\<not> occurs X (Paar u1 u2)"
        using H \<open>t1 = Paar u1 u2\<close> \<open>t2 = Susp pi X\<close> by (auto simp del: sred_fun.simps split: if_splits)
      let ?\<sigma> = "[(X, swap (rev pi) (Paar u1 u2))]"
      have step: "((Paar u1 u2 \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
        using nocc var_2_sred by (simp del: swap.simps)
      have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = Some r"
        using H nocc unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Paar u1 u2\<close> \<open>t2 = Susp pi X\<close> using step by blast
    qed (use H Paar in \<open>simp_all del: sred_fun.simps\<close>)
  next
    case (Func F u)
    show ?thesis
    proof (cases t2)
      case (Func G v)
      \<comment> \<open>Rule \<open>func_sred\<close>: only applicable (and only Some) when F = G.\<close>
      have "F = G"
        using H \<open>t1 = Func F u\<close> \<open>t2 = Func G v\<close> by (simp del: sred_fun.simps split: if_splits)
      have step: "((Func F u \<approx>? Func F v) # xs, ys) \<turnstile> [] \<leadsto> ((u \<approx>? v) # xs, ys)"
        using func_sred by simp
      have "sred_fun (((u \<approx>? v) # xs, ys), nabla, [] \<bullet> s) = Some r"
        using H unfolding \<open>t1 = Func F u\<close> \<open>t2 = Func G v\<close> \<open>F = G\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Func G v\<close> \<open>F = G\<close> using step by blast
    next
      case (Susp pi X)
      \<comment> \<open>Rule \<open>var_2_sred\<close>: Some is only returned when the occurs check succeeds.\<close>
      have nocc: "\<not> occurs X (Func F u)"
        using H \<open>t1 = Func F u\<close> \<open>t2 = Susp pi X\<close> by (auto simp del: sred_fun.simps split: if_splits)
      let ?\<sigma> = "[(X, swap (rev pi) (Func F u))]"
      have step: "((Func F u \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
        using nocc var_2_sred by (simp del: swap.simps)
      have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = Some r"
        using H nocc unfolding \<open>t1 = Func F u\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Func F u\<close> \<open>t2 = Susp pi X\<close> using step by blast
    qed (use H Func in \<open>simp_all del: sred_fun.simps\<close>)
  next
    case (Abst a u)
    show ?thesis
    proof (cases t2)
      case (Abst b v)
      show ?thesis
      proof (cases "a = b")
        case True
        \<comment> \<open>Rule \<open>abst_aa_sred\<close>: same binder, compare the bodies.\<close>
        have step: "((Abst a u \<approx>? Abst a v) # xs, ys) \<turnstile> [] \<leadsto> ((u \<approx>? v) # xs, ys)"
          using abst_aa_sred by simp
        have "sred_fun (((u \<approx>? v) # xs, ys), nabla, [] \<bullet> s) = Some r"
          using H unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> \<open>a = b\<close> by (simp del: sred_fun.simps)
        then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> \<open>a = b\<close> using step by blast
      next
        case False
        \<comment> \<open>Rule \<open>abst_ab_sred\<close>: different binders, swap a and b in the right body
           and add the freshness constraint \<open>a # v\<close>.\<close>
        have step: "((Abst a u \<approx>? Abst b v) # xs, ys) \<turnstile> [] \<leadsto> ((u \<approx>? swap [(a, b)] v) # xs, (a \<sharp>? v) # ys)"
          using False abst_ab_sred by simp
        have "sred_fun (((u \<approx>? swap [(a, b)] v) # xs, (a \<sharp>? v) # ys), nabla, [] \<bullet> s) = Some r"
          using H False unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> by (simp del: sred_fun.simps)
        then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Abst b v\<close> using step by blast
      qed
    next
      case (Susp pi X)
      \<comment> \<open>Rule \<open>var_2_sred\<close>: Some is only returned when the occurs check succeeds.\<close>
      have nocc: "\<not> occurs X (Abst a u)"
        using H \<open>t1 = Abst a u\<close> \<open>t2 = Susp pi X\<close> by (auto simp del: sred_fun.simps split: if_splits)
      let ?\<sigma> = "[(X, swap (rev pi) (Abst a u))]"
      have step: "((Abst a u \<approx>? Susp pi X) # xs, ys) \<turnstile> ?\<sigma> \<leadsto> apply_subst ?\<sigma> (xs, ys)"
        using nocc var_2_sred by (simp del: swap.simps)
      have "sred_fun (apply_subst ?\<sigma> (xs, ys), nabla, ?\<sigma> \<bullet> s) = Some r"
        using H nocc unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Susp pi X\<close> by (simp del: sred_fun.simps)
      then show ?thesis unfolding \<open>t1 = Abst a u\<close> \<open>t2 = Susp pi X\<close> using step by blast
    qed (use H Abst in \<open>simp_all del: sred_fun.simps\<close>)
  next
    case (Susp pi X)
    \<comment> \<open>Left-hand side is a suspension: unless both sides are suspensions of the same
       variable, the step is always \<open>var_1_sred\<close> (X is instantiated with the right side).\<close>
    have var_1: "sred_fun (apply_subst [(X, swap (rev pi) t2)] (xs, ys), nabla, 
                           [(X, swap (rev pi) t2)] \<bullet> s) = Some r \<Longrightarrow> \<not> occurs X t2 \<Longrightarrow> ?thesis"
    proof -
      assume rec: "sred_fun (apply_subst [(X, swap (rev pi) t2)] (xs, ys), nabla, 
                             [(X, swap (rev pi) t2)] \<bullet> s) = Some r"
        and nocc: "\<not> occurs X t2"
      have "((Susp pi X \<approx>? t2) # xs, ys) \<turnstile> [(X, swap (rev pi) t2)] \<leadsto> apply_subst [(X, swap (rev pi) t2)] (xs, ys)"
        using nocc var_1_sred by simp
      then show ?thesis unfolding \<open>t1 = Susp pi X\<close> using rec by blast
    qed
    show ?thesis
    proof (cases t2)
      case (Susp pi2 Y)
      show ?thesis
      proof (cases "X = Y")
        case True
        \<comment> \<open>Rule \<open>susp_sred\<close>: same variable, generate freshness constraints for the 
           disagreement set of the two permutations.\<close>
        have step: "((Susp pi X \<approx>? Susp pi2 X) # xs, ys) \<turnstile> [] \<leadsto> 
                      (xs, map (\<lambda>a. a \<sharp>? Susp [] X) (ds_list pi pi2) @ ys)"
          using susp_sred by simp
        have "sred_fun ((xs, map (\<lambda>a. a \<sharp>? Susp [] X) (ds_list pi pi2) @ ys), nabla, [] \<bullet> s) = Some r"
          using H unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Susp pi2 Y\<close> \<open>X = Y\<close>[symmetric] 
          by (simp del: sred_fun.simps)
        then show ?thesis unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Susp pi2 Y\<close> \<open>X = Y\<close>[symmetric] 
          using step by blast
      next
        case False
        \<comment> \<open>Different variables: \<open>var_1_sred\<close>, the occurs check holds trivially.\<close>
        have rec: "sred_fun (apply_subst [(X, swap (rev pi) t2)] (xs, ys), nabla,
                             [(X, swap (rev pi) t2)] \<bullet> s) = Some r"
          using H False unfolding \<open>t1 = Susp pi X\<close> \<open>t2 = Susp pi2 Y\<close>
          by (simp del: sred_fun.simps)
        have nocc: "\<not> occurs X t2"
          using False unfolding \<open>t2 = Susp pi2 Y\<close> by simp
        show ?thesis
          using var_1[OF rec nocc] by simp
      qed
    qed (use H Susp in \<open>(intro var_1; simp del: sred_fun.simps split: if_splits)\<close>)+
  qed
qed

text\<open>Whenever \<open>sred_fun\<close> succeeds, the first (equation) list of the resulting problem is empty:
all equations have been solved, only freshness constraints remain.\<close>

lemma sred_fun_some_fst_empty:
  assumes "sred_fun (P, nabla, s) = Some (P', nabla', s')"
  shows "fst P' = []"
  using assms
proof(induct P arbitrary: s rule: wf_induct[OF wf_rank_r])
  case (1 P)
  obtain eqs ys where P_def: "P = (eqs, ys)" by (cases P)
  show ?case
  proof(cases eqs)
    case Nil
    \<comment> \<open>No equations left: \<open>sred_fun\<close> returns the problem unchanged.\<close>
    then show ?thesis using 1(2) P_def by auto
  next
    case (Cons e xs)
    \<comment> \<open>One equation is processed by an \<open>s_red\<close> step, after which \<open>sred_fun\<close> still succeeds
       on a problem of smaller rank: apply the induction hypothesis.\<close>
    obtain t1 t2 where e_def: "e = (t1 \<approx>? t2)" by (cases e)
    obtain \<sigma> Q where step: "P \<turnstile> \<sigma> \<leadsto> Q" and rec: "sred_fun (Q, nabla, \<sigma> \<bullet> s) = Some (P', nabla', s')"
      using sred_fun_unfold_step 1(2) unfolding P_def Cons e_def by blast
    have "(Q, P) \<in> rank_r"
      using rank_r_sred[OF step] by simp
    then show ?thesis 
      using 1(1) rec by blast
  qed
qed

lemma sred_fun_sred_rtc:
  assumes "sred_fun (P, nabla, s) = Some (P', nabla', s')"
  shows "nabla' = nabla \<and> (\<exists>s1. P \<turnstile> s1 \<leadsto>\<^sup>* P' \<and> s' = s1 \<bullet> s)"
  using assms
proof(induct P arbitrary: s rule: wf_induct[OF wf_rank_r])
  case (1 P)
  obtain eqs ys where P_def: "P = (eqs, ys)" by (cases P)
  show ?case
  proof(cases eqs)
    case Nil
    then show ?thesis using 1(2) P_def by force
  next
    case (Cons e xs)
    obtain t1 t2 where e_def: "e = (t1 \<approx>? t2)" by (cases e)
    obtain \<sigma> Q where step: "P \<turnstile> \<sigma> \<leadsto> Q" and rec: "sred_fun (Q, nabla, \<sigma> \<bullet> s) = Some (P', nabla', s')"
      using sred_fun_unfold_step 1(2) unfolding P_def Cons e_def by blast
    have "(Q, P) \<in> rank_r"
      using rank_r_sred[OF step] by simp
    hence "nabla' = nabla \<and> (\<exists>s1. Q \<turnstile> s1 \<leadsto>\<^sup>* P' \<and> s' = s1 \<bullet> (\<sigma> \<bullet> s))"
      using 1(1) rec by blast
    then show ?thesis
      using sred_rtc_step[OF step] comp_assoc by metis
  qed
qed

text\<open>\<open>cred_fun\<close> is simulated by the reflexive-transitive closure of the freshness reductions.\<close>

lemma cred_fun_cred_rtc:
  assumes "cred_fun ((xs, ys), nabla, s) = Some (P', nabla', s')" and "xs = []"
  shows "s' = s \<and> (\<exists>n1. ([], ys) \<turnstile> n1 \<rightarrow>\<^sup>* P' \<and> nabla' = n1 \<union> nabla)"
  using assms
proof(induct "((xs, ys), nabla, s)" arbitrary: xs ys nabla s rule: cred_fun.induct)
  case (1 xs a ys nabla s)
  then show ?case using cred_rtc_step[OF unit_cred] by (auto simp: Un_assoc)
next
  case (2 xs a t1 t2 ys nabla s)
  then show ?case using cred_rtc_step[OF paar_cred] by (auto simp: Un_assoc)
next
  case (3 xs a F t ys nabla s)
  then show ?case using cred_rtc_step[OF func_cred] by (auto simp: Un_assoc)
next
  case (4 xs a b t ys nabla s)
  then show ?case 
    using cred_rtc_step[OF abst_aa_cred] cred_rtc_step[OF abst_ab_cred]
    by (cases "a = b") (auto simp: Un_assoc)
next
  case (5 xs a b ys nabla s)
  then show ?case using cred_rtc_step[OF atom_cred] by (auto simp: Un_assoc split: if_splits)
next
  case (6 xs a pi X ys nabla s)
  then show ?case using cred_rtc_step[OF susp_cred] by (auto simp: Un_assoc)
next
  case (7 xs nabla s)
  then show ?case by force
qed

lemma cred_fun_some_fst:
  assumes "cred_fun ((xs, ys), nabla, s) = Some (P', nabla', s')"
  shows "fst P' = xs"
  using assms 
  by (induct "((xs, ys), nabla, s)" arbitrary: xs ys nabla s rule: cred_fun.induct, auto split: if_splits)

text\<open>Gluing the closures of the equational and freshness reductions into \<open>red_plus\<close>.\<close>

lemma sred_rtc_red_plus_append:
  assumes "P1 \<turnstile> s \<leadsto>\<^sup>* P2" and "P2 \<Turnstile> (nabla, []) \<Rightarrow> P3"
  shows "P1 \<Turnstile> (nabla, s) \<Rightarrow> P3"
  using assms by (induct rule: sred_rtc.induct) auto

lemma cred_rtc_red_plus:
  assumes "P1 \<turnstile> nabla \<rightarrow>\<^sup>* P2"
  shows "(P1 = P2 \<and> nabla = {}) \<or> P1 \<Turnstile> (nabla, []) \<Rightarrow> P2"
  using assms
proof(induct rule: cred_rtc.induct)
  case (cred_refl P1)
  then show ?case by simp
next
  case (cred_rtc_step P1 nabla1 P2 nabla2 P3)
  show ?case
  proof(cases "P2 = P3 \<and> nabla2 = {}")
    case True
    then show ?thesis using cred_single[OF cred_rtc_step(1)] by simp
  next
    case False
    hence "P2 \<Turnstile> (nabla2, []) \<Rightarrow> P3" 
      using cred_rtc_step(3) False by auto
    then show ?thesis using cred_step[OF cred_rtc_step(1)] by simp
  qed
qed

text\<open>A successful run of the algorithm corresponds to a sequence of equational reductions 
followed by a sequence of freshness reductions ending in the empty problem.\<close>

lemma nomu_unify_some_rtc:
  assumes "nomu_unify P = Some (nabla, s)"
  shows "\<exists>P3. P \<turnstile> s \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla \<rightarrow>\<^sup>* ([],[])"
proof-
  obtain R where R: "red_plus_fun (P, {}, []) = Some R"
    using assms by (cases "red_plus_fun (P, {}, [])") auto
  obtain xs ys nabla0 s0 where S: "sred_fun (P, {}, []) = Some ((xs, ys), nabla0, s0)"
    using R by (cases "sred_fun (P, {}, [])") auto
  have "xs = []"
    using sred_fun_some_fst_empty[OF S] by simp
  obtain P1 nabla1 s1 where C: "cred_fun (([], ys), nabla0, s0) = Some (P1, nabla1, s1)"
    using R S \<open>xs = []\<close> by (cases R) auto
  have "P1 = ([],[])"
    using cred_fun_some_fst[OF C] cred_fun_some_snd_empty[OF C] by (cases P1) auto
  hence "nabla1 = nabla" "s1 = s"
    using assms R S C \<open>xs = []\<close> by auto
  obtain s2 where "nabla0 = {}" "P \<turnstile> s2 \<leadsto>\<^sup>* ([], ys)" "s0 = s2"
    using sred_fun_sred_rtc[OF S] \<open>xs = []\<close> by auto
  moreover obtain n where "s1 = s0" "([], ys) \<turnstile> n \<rightarrow>\<^sup>* P1" "nabla1 = n \<union> nabla0"
    using cred_fun_cred_rtc[OF C] by auto
  ultimately show ?thesis
    using \<open>P1 = ([],[])\<close> \<open>nabla1 = nabla\<close> \<open>s1 = s\<close> by auto
qed

text\<open>For a non-trivial problem, a successful run of the algorithm corresponds to a \<open>red_plus\<close> 
derivation to the empty problem.\<close>

lemma nomu_unify_some_red_plus:
  assumes "nomu_unify P = Some (nabla, s)" and "P \<noteq> ([],[])"
  shows "P \<Turnstile> (nabla, s) \<Rightarrow> ([],[])"
proof-
  obtain P3 where sred: "P \<turnstile> s \<leadsto>\<^sup>* P3" and cred: "P3 \<turnstile> nabla \<rightarrow>\<^sup>* ([],[])"
    using nomu_unify_some_rtc[OF assms(1)] by blast
  show ?thesis
  proof(cases "P3 = ([],[]) \<and> nabla = {}")
    case True
    then show ?thesis 
      using sred_rtc_to_redplus[of P "([],[])" s] sred assms(2) by simp
  next
    case False
    then have "P3 \<Turnstile> (nabla, []) \<Rightarrow> ([],[])" 
      using cred_rtc_red_plus[OF cred] by metis
    then show ?thesis 
      using sred_rtc_red_plus_append[OF sred] by simp
  qed
qed

text\<open>Soundness: whenever the algorithm returns a result, it is an idempotent most general 
unifier of the input problem.\<close>

theorem nomu_unify_sound:
  assumes "nomu_unify P = Some (nabla, s)"
  shows "(nabla, s) \<in> U P \<and> mgu P (nabla, s) \<and> idem (nabla, s)"
proof(cases "P = ([],[])")
  case True
  have "nabla = {}" and "s = []"
    using assms True by simp_all
  then show ?thesis
    using True subst_equ_refl
    unfolding all_solutions_def mgu_def idem_def ext_subst_def by auto
next
  case False
  have red: "P \<Turnstile> (nabla, s) \<Rightarrow> ([],[])"
    using nomu_unify_some_red_plus[OF assms False] by simp
  have "(nabla, s) \<in> U P"
    using P1_from_P2_red_plus[OF red _ ext_subst_id, of "{}"]
    by (simp add: all_solutions_def[of "([],[])"])
  moreover have "mgu P (nabla, s) \<and> idem (nabla, s)"
    using mgu[OF red] by simp
  ultimately show ?thesis by simp
qed

(*<*)
end
(*>*)
