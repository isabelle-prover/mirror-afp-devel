section \<open>Linear Diophantine Equation Solver\<close>

text \<open>We verify Griggio's algorithm to eliminate equations or detect unsatisfiability.\<close>

subsection \<open>Abstract Algorithm\<close>

theory Linear_Diophantine_Solver
  imports 
    Diophantine_Eqs_and_Ineqs
    "HOL.Map" 
begin
 
lift_definition normalize_dleq :: "'v dleq \<Rightarrow> int \<times> 'v dleq" is 
  "\<lambda> c. (Gcd (range c), \<lambda> x. c x div Gcd (range c))" 
  apply simp
  subgoal by (rule finite_subset, auto)
  done

lemma normalize_dleq_gcd: assumes "normalize_dleq p = (g,q)" 
  and "p \<noteq> 0" 
shows "g = Gcd (insert (constant_l p) (coeff_l p ` vars_l p))"
  and "g \<ge> 1"
  and "normalize_dleq q = (1,q)"     
  using assms
proof (atomize (full), transfer, goal_cases)
  case (1 p g q)
  let ?G = "insert (p None) ((\<lambda>x. p (Some x)) ` {x. p (Some x) \<noteq> 0})" 
  let ?g = "Gcd (range p)" 
  have "Gcd ?G = Gcd (insert 0 ?G)" by auto
  also have "insert 0 ?G = insert 0 (range p)" 
  proof - 
    {
      fix y
      assume *: "y \<in> insert 0 (range p)" "y \<notin> insert 0 ?G" 
      then obtain z where "y = p z" by auto
      with * have False by (cases z, auto)
    }
    thus ?thesis by auto
  qed
  also have "Gcd \<dots> = Gcd (range p)" by auto
  finally have eq: "Gcd ?G = ?g" .
  
  from 1 obtain x where px: "p x \<noteq> 0" by auto
  then obtain y where "y \<in> range p" "y \<noteq> 0" by auto
  hence g0: "?g \<noteq> 0" by auto
  moreover have "?g \<ge> 0" by simp
  ultimately have g1: "?g \<ge> 1" by linarith

  from 1 have gg: "g = ?g" by auto

  let ?gq = "Gcd (range q)" 
  from 1 have q: "q = (\<lambda>x. p x div ?g)" by auto
  have dvd: "?g dvd p x" for x by auto
  define gp where "gp = ?g" 
  define gq where "gq = ?gq" 
  note hide = gp_def[symmetric] gq_def[symmetric]
  have "?gq \<ge> 0" by simp
  then consider (0) "?gq = 0" | (1) "?gq = 1" | (large) "?gq \<ge> 2" by linarith
  hence gq1: "?gq = 1"
  proof cases
    case 0
    hence "range q \<subseteq> {0}" by simp
    moreover from px dvd[of x] have "q x \<noteq> 0" unfolding q
      using dvd_div_eq_0_iff by blast
    ultimately show ?thesis by auto
  next
    case large
    hence gq0: "?gq \<noteq> 0" by linarith
    define prod where "prod = ?gq * ?g" 
    {
      fix y
      have "?gq dvd q y" by simp
      then obtain fq where qy: "q y = ?gq * fq" by blast
      from dvd[of y] obtain fp where py: "p y = ?g * fp" by blast
      have "prod dvd p y" using fun_cong[OF q, of y] py qy gq0 g0 unfolding hide prod_def by auto
    }
    hence "prod dvd Gcd (range p)"
      by (simp add: dvd_Gcd_iff)
    from this[unfolded prod_def] g0 gq0 have "?gq dvd 1" by force
    hence "abs ?gq = 1" by simp
    with large show ?thesis by simp
  qed simp

  show ?case unfolding gg gq1
    by (intro conjI g1 eq[symmetric], auto)
qed
  
  

lemma vars_l_normalize: "normalize_dleq p = (g,q) \<Longrightarrow> vars_l q = vars_l p" 
proof (transfer, goal_cases)
  case (1 c g q)
  {
    fix x
    assume "c (Some x) \<noteq> 0" 
    moreover have "Gcd (range c) dvd c (Some x)" by simp
    ultimately have "c (Some x) div Gcd (range c) \<noteq> 0" by fastforce
  }
  thus ?case using 1 by auto
qed


lemma eval_normalize_dleq: "normalize_dleq p = (g,q) \<Longrightarrow> eval_l \<alpha> p = g * eval_l \<alpha> q" 
proof (subst (1 2) eval_l_mono[of "vars_l p"], goal_cases)
  case 1 show ?case by force
  case 2 thus ?case using vars_l_normalize by auto
  case 3 thus ?case by force
  case 4 thus ?case
  proof (transfer, goal_cases)
    case (1 c g d \<alpha>)
    show ?case
    proof (cases "range c \<subseteq> {0}")
      case True
      hence "c x = 0" for x using 1 by auto
      thus ?thesis using 1 by auto
    next
      case False
      let ?g = "Gcd (range c)" 
      from False have gcd: "?g \<noteq> 0" by auto
      hence mult: "c x div ?g * ?g = c x" for x by simp
      let ?expr = "c None div ?g + (\<Sum>x | c (Some x) \<noteq> 0. c (Some x) div ?g * \<alpha> x)" 
      have "?g * ?expr = ?expr * ?g" by simp
      also have "\<dots> = c None + (\<Sum>x | c (Some x) \<noteq> 0. c (Some x) * \<alpha> x)" 
        unfolding distrib_right mult sum_distrib_right
        by (simp add: ac_simps mult)
      finally show ?thesis using 1(3) by auto
    qed
  qed  
qed
 
lemma gcd_unsat_detection: assumes "g = Gcd (coeff_l p ` vars_l p)" 
  and "\<not> g dvd constant_l p" 
shows "\<not> satisfies_dleq \<alpha> p" 
proof
  assume "satisfies_dleq \<alpha> p" 
  from this[unfolded satisfies_dleq_def eval_l_def]
  have "(\<Sum>x\<in>vars_l p. coeff_l p x * \<alpha> x) = - constant_l p" by auto
  hence "(\<Sum>x\<in>vars_l p. coeff_l p x * \<alpha> x) dvd constant_l p" by auto
  moreover have "g dvd (\<Sum>x\<in>vars_l p. coeff_l p x * \<alpha> x)" 
    unfolding assms by (rule dvd_sum, simp)
  ultimately show False using assms by auto
qed


lemma substitute_l_in_equation: assumes "\<alpha> x = eval_l \<alpha> p" 
  shows "eval_l \<alpha> (substitute_l x p q) = eval_l \<alpha> q" 
    "satisfies_dleq \<alpha> (substitute_l x p q) \<longleftrightarrow> satisfies_dleq \<alpha> q" 
proof -
  show "eval_l \<alpha> (substitute_l x p q) = eval_l \<alpha> q" 
    unfolding eval_substitute_l unfolding assms(1)[symmetric] by auto
  thus "satisfies_dleq \<alpha> (substitute_l x p q) \<longleftrightarrow> satisfies_dleq \<alpha> q" 
    unfolding satisfies_dleq_def by auto
qed

type_synonym 'v dleq_sf = "'v \<times> (int,'v)lpoly" 

fun satisfies_dleq_sf:: "(int,'v) assign \<Rightarrow> 'v dleq_sf \<Rightarrow> bool" where
  "satisfies_dleq_sf \<alpha> (x,p) = (\<alpha> x = eval_l \<alpha> p)"

type_synonym 'v dleq_system = "'v dleq_sf set \<times> 'v dleq set" 

fun satisfies_system :: "(int,'v) assign \<Rightarrow> 'v dleq_system \<Rightarrow> bool" where
  "satisfies_system \<alpha> (S,E) = (Ball S (satisfies_dleq_sf \<alpha>) \<and> Ball E (satisfies_dleq \<alpha>))" 

fun invariant_system :: "'v dleq_system \<Rightarrow> bool" where
  "invariant_system (S,E) = (Ball (fst ` S) (\<lambda> x. x \<notin> \<Union> (vars_l ` (snd ` S \<union> E)) \<and> (\<exists>! e. (x,e) \<in> S)))"  

definition reorder_for_var where
  "reorder_for_var x p = (if coeff_l p x = 1 then - (p - var_l x) else p + var_l x)" 

lemma reorder_for_var: assumes "abs (coeff_l p x) = 1" 
  shows "satisfies_dleq \<alpha> p \<longleftrightarrow> satisfies_dleq_sf \<alpha> (x, reorder_for_var x p)" (is ?prop1)
    "vars_l (reorder_for_var x p) = vars_l p - {x}" (is ?prop2)
proof -
  from assms have "coeff_l p x = 1 \<or> coeff_l p x = -1" by auto
  hence "?prop1 \<and> ?prop2" 
  proof
    assume 1: "coeff_l p x = 1" 
    hence res: "reorder_for_var x p = - (p - var_l x)" unfolding reorder_for_var_def by auto
    have ?prop2 unfolding res vars_l_uminus using 1 by transfer auto
    moreover have ?prop1 unfolding satisfies_dleq_def res satisfies_dleq_sf.simps by auto
    ultimately show ?thesis by auto
  next
    assume m1: "coeff_l p x = -1" 
    hence res: "reorder_for_var x p = p + var_l x" unfolding reorder_for_var_def by auto
    have ?prop2 unfolding res using m1 by transfer auto
    moreover have ?prop1 unfolding satisfies_dleq_def res satisfies_dleq_sf.simps by auto
    ultimately show ?thesis by auto
  qed
  thus ?prop1 ?prop2 by blast+
qed 

lemma reorder_nontriv_var_sat: "\<exists> a. satisfies_dleq (\<alpha>(y := a)) (reorder_nontriv_var x p y)" 
proof -
  define X where "X = insert x (vars_l p) - {y}" 
  have X: "finite X" "y \<notin> X" "insert x (insert y (vars_l p)) = insert y X" unfolding X_def by auto
  have sum: "sum f (insert x (insert y (vars_l p))) = f y + sum f X" for f :: "_ \<Rightarrow> int" 
    unfolding X using X(1-2) by simp 
  show ?thesis
    unfolding satisfies_dleq_def
    apply (subst eval_l_mono[of "insert x (insert y (vars_l p))"])
      apply force
     apply (rule vars_reorder_non_triv)
    apply (unfold sum)
    apply (subst (1) coeff_l_reorder_nontriv_var)
    apply (subst sum.cong[OF refl, of _ _ "\<lambda> z. coeff_l (reorder_nontriv_var x p y) z * \<alpha> z"])
    subgoal using X by auto
    subgoal by simp algebra
    done
qed

lemma reorder_nontriv_var: assumes a: "a = coeff_l p x" "a \<noteq> 0" 
  and y: "y \<notin> vars_l p" 
  and q: "q = reorder_nontriv_var x p y" 
  and e: "e = reorder_for_var x q" 
  and r: "r = substitute_l x e p" 
shows "fun_of_lpoly r = (\<lambda> z. fun_of_lpoly p z mod a)(Some x := 0, Some y := a)" 
  "constant_l r = constant_l p mod a"
  "coeff_l r = (\<lambda> z. coeff_l p z mod a)(x := 0, y := a)"
proof -
  from a have xv: "x \<in> vars_l p" by (transfer, auto)
  with y have xy: "x \<noteq> y" by auto
  from q have q: "fun_of_lpoly q = (\<lambda>z. fun_of_lpoly p z div a)(Some x := 1, Some y := - 1)" 
    unfolding a by transfer
  hence "fun_of_lpoly e = (\<lambda>z. - (fun_of_lpoly p z div a))(Some x := 0, Some y := 1)" 
    unfolding e reorder_for_var_def using xy
    by (transfer, auto)
  thus main: "fun_of_lpoly r = (\<lambda> z. fun_of_lpoly p z mod a)(Some x := 0, Some y := a)" 
    unfolding r using a xy y
    by (transfer, auto simp: minus_mult_div_eq_mod) 
  from main show "constant_l r = constant_l p mod a" by transfer auto
  from main show "coeff_l r = (\<lambda> z. coeff_l p z mod a)(x := 0, y := a)" by transfer auto
qed

 
(* we deviate from the original algorithm, since we also substitute in the solved part in the
   griggio_solve rule; moreover we do not enforce that normalization uses a non-trivial gcd g *)
inductive griggio_equiv_step :: "'v dleq_system \<Rightarrow> 'v dleq_system \<Rightarrow> bool" where
  griggio_solve: "abs (coeff_l p x) = 1 \<Longrightarrow> e = reorder_for_var x p \<Longrightarrow> 
    griggio_equiv_step (S,insert p E) (insert (x, e) (map_prod id (substitute_l x e) ` S), substitute_l x e ` E)" 
| griggio_normalize: "normalize_dleq p = (g,q) \<Longrightarrow> g \<ge> 1 \<Longrightarrow>
    griggio_equiv_step (S,insert p E) (S, insert q E)" 
| griggio_trivial: "griggio_equiv_step (S, insert 0 E) (S, E)"

fun vars_system :: "'v dleq_system \<Rightarrow> 'v set" where
  "vars_system (S, E) = fst ` S \<union> \<Union> (vars_l ` (snd ` S \<union> E))" 

lemma griggio_equiv_step: assumes "griggio_equiv_step SE TF"
  shows "(satisfies_system \<alpha> SE \<longleftrightarrow> satisfies_system \<alpha> TF) \<and>
         (invariant_system SE \<longrightarrow> invariant_system TF) \<and>
         vars_system TF \<subseteq> vars_system SE" 
  using assms
proof induction
  case *: (griggio_solve p x e S E)
  from *(1) have xp: "x \<in> vars_l p" by transfer auto
  let ?E = "insert p E" 
  let ?T = "insert (x, e) (map_prod id (substitute_l x e) ` S)" 
  let ?F = "substitute_l x e ` E" 
  note reorder = reorder_for_var[OF *(1), folded *(2)]
  from reorder(1)[of \<alpha>] 
  have "satisfies_system \<alpha> (S, ?E) = satisfies_system \<alpha> (insert (x,e) S, E)" 
    unfolding satisfies_system.simps by auto
  also have "\<dots> = satisfies_system \<alpha> (?T, ?F)" 
  proof (cases "\<alpha> x = eval_l \<alpha> e")
    case True
    from substitute_l_in_equation[OF this] show ?thesis by auto
  qed auto
  finally have equiv: "satisfies_system \<alpha> (S, ?E) = satisfies_system \<alpha> (?T, ?F)" .
  moreover {
    assume inv: "invariant_system (S, ?E)" 
    have "invariant_system (?T, ?F)" 
      unfolding invariant_system.simps
    proof (intro ballI)
      fix y
      assume y: "y \<in> fst ` ?T" 
      from vars_substitute_l[of x e, unfolded reorder]
      have vars_subst: "vars_l (substitute_l x e q) \<subseteq> vars_l p - {x} \<union> (vars_l q - {x})" for q by auto
      from y have y: "y = x \<or> x \<noteq> y \<and> y \<in> fst ` S" by force
      thus "y \<notin> \<Union> (vars_l ` (snd ` ?T \<union> ?F)) \<and> (\<exists>!f. (y, f) \<in> ?T)" 
      proof
        assume y: "y = x" 
        hence "y \<notin> \<Union> (vars_l ` (snd ` ?T \<union> ?F))" using vars_subst reorder(2) by auto
        moreover have "\<exists>!f. (y, f) \<in> ?T" unfolding y 
        proof (intro ex1I[of _ e])
          fix f
          assume xf: "(x, f) \<in> ?T" 
          show "f = e" 
          proof (rule ccontr)
            assume "f \<noteq> e" 
            with xf have "x \<in> fst ` S" by force
            from inv[unfolded invariant_system.simps, rule_format, OF this]
            have "x \<notin> vars_l p" by auto
            with *(1) show False by transfer auto
          qed
        qed force
        ultimately show ?thesis by auto
      next
        assume "x \<noteq> y \<and> y \<in> fst ` S" 
        hence xy: "x \<noteq> y" and y: "y \<in> fst ` S" by auto                    
        from inv[unfolded invariant_system.simps, rule_format, OF y]
        have nmem: "y \<notin> \<Union> (vars_l ` (snd ` S \<union> insert p E))" and unique: "(\<exists>!f. (y, f) \<in> S)" by auto
        from unique have "\<exists>!f. (y, f) \<in> ?T" using xy by force
        moreover from nmem reorder(2) have "y \<notin> vars_l e" by auto
        with nmem vars_substitute_l[of x e]
        have "y \<notin> \<Union> (vars_l ` (snd ` ?T \<union> ?F))" by auto
        ultimately show ?thesis by auto
      qed
    qed
  }
  moreover
  have "vars_system (?T, ?F) \<subseteq> vars_system (S, ?E)"
    using reorder(2) vars_substitute_l[of x e] xp unfolding vars_system.simps 
      by (auto simp: rev_image_eqI) blast
  ultimately show ?case by auto
next
  case *: (griggio_normalize p g q S E)
  from vars_l_normalize[OF *(1)] have vars[simp]: "vars_l q = vars_l p" by auto
  from eval_normalize_dleq[OF *(1)] *(2) 
  have sat[simp]: "satisfies_dleq \<alpha> p = satisfies_dleq \<alpha> q" unfolding satisfies_dleq_def by auto
  show ?case by simp
next
  case griggio_trivial
  show ?case by (simp add: satisfies_dleq_def)
qed

inductive griggio_unsat :: "'v dleq \<Rightarrow> bool" where
  griggio_gcd_unsat: "\<not> Gcd (coeff_l p ` vars_l p) dvd constant_l p \<Longrightarrow> griggio_unsat p" 
| griggio_constant_unsat: "vars_l p = {} \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> griggio_unsat p" 

lemma griggio_unsat: assumes "griggio_unsat p"
  shows "\<not> satisfies_system \<alpha> (S, insert p E)" 
  using assms
proof induction
  case (griggio_gcd_unsat p)
  from gcd_unsat_detection[OF refl this]
  show ?case by auto
next
  case (griggio_constant_unsat p)
  hence "eval_l \<alpha> p \<noteq> 0" for \<alpha>
    unfolding eval_l_def
  proof (transfer, goal_cases)
    case (1 p \<alpha>)
    from 1(3) obtain x where "p x \<noteq> 0" by auto
    with 1 show ?case by (cases x, auto)
  qed
  thus ?case by (auto simp: satisfies_dleq_def)
qed

definition adjust_assign :: "'v dleq_sf list \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> ('v \<Rightarrow> int)" where
  "adjust_assign S \<alpha> x = (case map_of S x of Some p \<Rightarrow> eval_l \<alpha> p | None \<Rightarrow> \<alpha> x)" 

definition solution_subst :: "'v dleq_sf list \<Rightarrow> ('v \<Rightarrow> (int,'v)lpoly)" where
  "solution_subst S x = (case map_of S x of Some p \<Rightarrow> p | None \<Rightarrow> var_l x)" 

locale griggio_input = fixes
  V :: "'v :: linorder set" and
  E :: "'v dleq set" 
begin

fun invariant_state where 
  "invariant_state (Some (SF,X)) = (invariant_system SF 
     \<and> vars_system SF \<subseteq> V \<union> X
     \<and> V \<inter> X = {}
     \<and> (\<forall> \<alpha>. (satisfies_system \<alpha> SF \<longrightarrow> Ball E (satisfies_dleq \<alpha>))
           \<and> (Ball E (satisfies_dleq \<alpha>) \<longrightarrow> (\<exists> \<beta>. satisfies_system \<beta> SF \<and> (\<forall> x. x \<notin> X \<longrightarrow> \<alpha> x = \<beta> x)))))" 
| "invariant_state None = (\<forall> \<alpha>. \<not> Ball E (satisfies_dleq \<alpha>))" 

(* The following inference rules do not enforce a normalizing strategy,
   and impose less application conditions than the original algorithm of Griggio. 
   Termination will have to be handled in the implementation. *)
inductive_set griggio_step :: "('v dleq_system \<times> 'v set) option rel" where
  griggio_eq_step: "griggio_equiv_step SF TG \<Longrightarrow> (Some (SF,X), Some (TG, X)) \<in> griggio_step" 
| griggio_fail_step: "griggio_unsat p \<Longrightarrow> (Some ((S,insert p F),X), None) \<in> griggio_step" 
| griggio_complex_step: "coeff_l p x \<noteq> 0 
    \<Longrightarrow> q = reorder_nontriv_var x p y 
    \<Longrightarrow> e = reorder_for_var x q
    \<Longrightarrow> y \<notin> V \<union> X
    \<Longrightarrow> (Some ((S,insert p F),X), 
         Some ((insert (x,e) (map_prod id (substitute_l x e) ` S), substitute_l x e ` insert p F), insert y X)) 
        \<in> griggio_step" 

lemma griggio_step: assumes "(A,B) \<in> griggio_step" 
  and "invariant_state A"
shows "invariant_state B" 
  using assms
proof (induct rule: griggio_step.induct)
  case *: (griggio_eq_step SF TG X)
  from griggio_equiv_step[OF *(1)] *(2)
  show ?case by auto
next
  case *: (griggio_fail_step p S F X)
  from griggio_unsat[OF *(1)]
  have "\<not> satisfies_system \<alpha> (S, insert p F)" for \<alpha> by auto
  with *(2)[unfolded invariant_state.simps] have "\<not> Ball E (satisfies_dleq \<alpha>)" for \<alpha> by blast
  then show ?case by auto
next
  case *: (griggio_complex_step p x q y e X S F)
  have sat: "\<exists>a. satisfies_dleq (\<alpha>(y := a)) q" for \<alpha> 
    using reorder_nontriv_var_sat[of _ y x p] *(2) by auto
  have "invariant_state (Some ((S, insert p F), X))" by fact
  note inv = this[unfolded invariant_state.simps]
  let ?F = "insert q (insert p F)" 
  let ?Y = "insert y X" 
  let ?T = "insert (x, e) (map_prod id (substitute_l x e) ` S)" 
  let ?G = "substitute_l x e ` insert p F" 
  define SF where "SF = (S,?F)" 
  define TG where "TG = (?T,?G)" 
  define Y where "Y = ?Y" 
  from inv * have y: "y \<notin> vars_system (S, insert p F)" by blast
  have inv': "invariant_state (Some ((S, ?F), ?Y))" 
    unfolding invariant_state.simps
  proof (intro allI conjI impI)
    from inv \<open>y \<notin> V \<union> X\<close>
    show "V \<inter> insert y X = {}" by auto
    from *(1) have xp: "x \<in> vars_l p" by transfer auto
    with vars_reorder_non_triv[of x p y, folded *(2)] 
    have vq: "vars_l q \<subseteq> insert y (vars_l p)" by auto
    from inv have vSF: "vars_system (S, insert p F) \<subseteq> V \<union> X" by auto
    with vq show "vars_system (S, insert q (insert p F)) \<subseteq> V \<union> insert y X" by auto
    {
      fix \<alpha>
      assume "satisfies_system \<alpha> (S, insert q (insert p F))" 
      hence "satisfies_system \<alpha> (S, insert p F)" by auto
      with inv show "Ball E (satisfies_dleq \<alpha>)" by blast
    }
    {
      fix \<alpha>
      assume "Ball E (satisfies_dleq \<alpha>)" 
      with inv obtain \<beta> where sat2: "satisfies_system \<beta> (S, insert p F)"
        and eq: "\<And> z. z \<notin> X \<Longrightarrow> \<alpha> z = \<beta> z" by blast
      from sat[of \<beta>] obtain a where sat3: "satisfies_dleq (\<beta>(y := a)) q" by auto 
      let ?\<beta> = "\<beta>(y := a)" 
      show "\<exists>\<beta>. satisfies_system \<beta> (S, ?F) \<and> (\<forall>z. z \<notin> ?Y \<longrightarrow> \<alpha> z = \<beta> z)" 
      proof (intro exI[of _ ?\<beta>] conjI allI impI)
        show "z \<notin> ?Y \<Longrightarrow> \<alpha> z = ?\<beta> z" for z
          using eq[of z] by auto
        have "satisfies_system ?\<beta> (S, ?F) = satisfies_system ?\<beta> (S, insert p F)" using sat3 by auto
        also have "\<dots> = satisfies_system \<beta> (S, insert p F)" 
          unfolding satisfies_system.simps
        proof (intro arg_cong2[of _ _ _ _ conj] ball_cong refl)
          fix r
          assume "r \<in> insert p F" 
          with y have "y \<notin> vars_l r" by auto
          thus "satisfies_dleq ?\<beta> r = satisfies_dleq \<beta> r" 
            unfolding satisfies_dleq_def 
            by (subst eval_l_cong[of _ ?\<beta> \<beta>], auto)
        next
          fix zr 
          assume "zr \<in> S" 
          then obtain z r where zr: "zr = (z,r)" and "(z,r) \<in> S" by (cases zr, auto)
          hence "insert z (vars_l r) \<subseteq> V \<union> X" using vSF by force
          with *(4) have "z \<noteq> y" and "y \<notin> vars_l r" by auto
          thus "satisfies_dleq_sf ?\<beta> zr = satisfies_dleq_sf \<beta> zr" 
            unfolding satisfies_dleq_sf.simps zr
            by (subst eval_l_cong[of _ ?\<beta> \<beta>], auto)
        qed
        also have \<dots> by fact
        finally show "satisfies_system ?\<beta> (S, ?F)" .
      qed
    }
    from inv have "invariant_system (S, insert p F)" by auto
    with y vq
    show "invariant_system (S, ?F)" by auto
  qed
  have step: "griggio_equiv_step (S, ?F) (?T, ?G)" 
  proof (intro griggio_equiv_step.intros(1) *(3))
    show "\<bar>coeff_l q x\<bar> = 1" unfolding *(2) coeff_l_reorder_nontriv_var by simp
  qed
  from griggio_equiv_step[OF this] inv'
  show ?case unfolding SF_def[symmetric] TG_def[symmetric] Y_def[symmetric] by auto
qed

context
  assumes VE: "\<Union> (vars_l ` E) \<subseteq> V"
begin

lemma griggio_steps: assumes "(Some (({},E),{}), SFO) \<in> griggio_step^*" (is "(?I,_) \<in> _")
  shows "invariant_state SFO" 
proof -
  define I where "I = ?I"  
  have inv: "invariant_state I" unfolding I_def using VE by auto
  from assms[folded I_def] 
  show ?thesis 
  proof (induct)
    case base
    then show ?case using inv .
  next
    case step
    then show ?case using griggio_step[OF step(2)] by auto
  qed
qed

lemma griggio_fail: assumes "(Some (({},E),{}), None) \<in> griggio_step^*" 
  shows "\<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (E, {})" 
proof -
  from griggio_steps[OF assms] show ?thesis by auto
qed

(* preliminary result, does not perform substitutions, relationship of \<beta> and \<alpha> not clear *)
lemma griggio_success: assumes "(Some (({},E),{}), Some ((S,{}),X)) \<in> griggio_step^*" 
    and \<beta>: "\<beta> = adjust_assign S_list \<alpha>" "set S_list = S"  
  shows "\<beta> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (E, {})"   
proof -
  obtain LV RV where LV: "LV = fst ` S" (* left variables of solution *)
    and RV: "RV = \<Union> (vars_l ` snd ` S)"  (* right variables of solution *)
    by auto
  have id: "satisfies_system \<beta> (S, {}) = Ball S (satisfies_dleq_sf \<beta>)" for \<beta>
    by auto
  have id2: "vars_system (S, {}) = LV \<union> RV" 
    by (auto simp: LV RV)
  have id3: "invariant_system (S, {}) = (LV \<inter> RV = {} \<and> (\<forall>x\<in>LV. \<exists>!e. (x, e) \<in> S))" 
    by (auto simp: LV RV)
  from griggio_steps[OF assms(1)]
  have "invariant_state (Some ((S, {}), X))" .
  note inv = this[unfolded invariant_state.simps id id2 id3]
  from inv have "Ball S (satisfies_dleq_sf \<beta>) \<Longrightarrow> Ball E (satisfies_dleq \<beta>)" 
    by auto
  moreover {
    fix x e
    assume xe: "(x,e) \<in> S" 
    hence x: "x \<in> LV" by (force simp: LV) 
    with inv xe have "\<exists>! e. (x,e) \<in> S" by force
    with xe have "map_of S_list x = Some e" unfolding \<beta>(2)[symmetric] 
      by (metis map_of_SomeD weak_map_of_SomeI)
    hence "\<beta> x = eval_l \<alpha> e" unfolding \<beta> adjust_assign_def by simp
    also have "\<dots> = eval_l \<beta> e" 
    proof (rule eval_l_cong)
      fix y
      assume "y \<in> vars_l e" 
      with xe have "y \<in> RV" unfolding RV by force
      with inv have "y \<notin> LV" by auto
      thus "\<alpha> y = \<beta> y" unfolding \<beta>(2)[symmetric] \<beta>(1) adjust_assign_def LV 
        by (force split: option.splits dest: map_of_SomeD)
    qed
    finally have "satisfies_dleq_sf \<beta> (x,e)" by auto
  }
  ultimately show ?thesis by force
qed

text \<open>In the following lemma we not only show that the equations E are 
  solvable, but also how the solution S can be used to process other constraints.
  Assume \<open>P\<close> describes an indexed set of polynomials, and 
  \<open>f\<close> is a formula that describes how these polynomials must be
  evaluated, e.g., \<open>f i = (i 1 \<le> 0 \<and> i 2 > 5 * i 3)\<close> for some inequalities.

  Then \<open>f(P) \<and> E\<close> is equi-satisfiable to \<open>f(\<sigma>(P))\<close> where \<open>\<sigma>\<close> is a substitution computed from S,
  and \<open>adjust_assign S\<close> is used to translated a solution in one direction.\<close>
theorem griggio_success_translations: 
  fixes P :: "'i \<Rightarrow> (int,'v)lpoly" and f :: "('i \<Rightarrow> int) \<Rightarrow> bool" 
  assumes "(Some (({},E),{}), Some ((S,{}),X)) \<in> griggio_step^*"
    and \<sigma>: "\<sigma> = solution_subst S_list" 
    and S_list: "set S_list = S" 
  shows 
    (* f-solution with substituted polys can be translated to full solution of f and E *) 
    "f (\<lambda> i. eval_l \<alpha> (substitute_all_l \<sigma> (P i))) \<Longrightarrow>
    \<beta> = adjust_assign S_list \<alpha> \<Longrightarrow> 
    f (\<lambda> i. eval_l \<beta> (P i)) \<and> \<beta> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (E, {})" 
    (* solution of f and E system implies f-solution with substituted polys *) 
    "f (\<lambda> i. eval_l \<alpha> (P i)) \<and> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (E, {}) \<Longrightarrow>
    (\<And> i. vars_l (P i) \<subseteq> V) \<Longrightarrow>
    \<exists> \<gamma>. f (\<lambda> i. eval_l \<gamma> (substitute_all_l \<sigma> (P i)))" 
proof -
  assume sol: "f (\<lambda> i. eval_l \<alpha> (substitute_all_l \<sigma> (P i)))" 
    and \<beta>: "\<beta> = adjust_assign S_list \<alpha>" 
  from griggio_success[OF assms(1) \<beta> S_list]
  have solE: "\<beta> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (E, {})" by auto
  show "f (\<lambda> i. eval_l \<beta> (P i)) \<and> \<beta> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (E, {})" 
  proof (intro conjI[OF _ solE])
    {
      fix i
      have "eval_l \<alpha> (substitute_all_l \<sigma> (P i)) = eval_l \<beta> (P i)" 
        unfolding eval_substitute_all_l
      proof (rule eval_l_cong)
        fix x
        show "eval_l \<alpha> (\<sigma> x) = \<beta> x" unfolding \<sigma> \<beta> solution_subst_def adjust_assign_def
          by (auto split: option.splits)
      qed
    }
    with sol show "f (\<lambda> i. eval_l \<beta> (P i))" by auto
  qed
next
  assume f: "f (\<lambda>i. eval_l \<alpha> (P i)) \<and> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o (E, {})" 
    and vV: "\<And> i. vars_l (P i) \<subseteq> V" 
  from griggio_steps[OF assms(1)]
  have "invariant_state (Some ((S, {}), X))" .
  note inv = this[unfolded invariant_state.simps]
  from f inv obtain \<gamma> 
    where sat: "satisfies_system \<gamma> (S, {})" and ab: "\<And> x. x \<notin> X \<Longrightarrow> \<alpha> x = \<gamma> x" by blast
  from inv sat have E: "Ball E (satisfies_dleq \<gamma>)" by auto
  {
    fix i
    have "eval_l \<alpha> (P i) = eval_l \<gamma> (P i)" 
    proof (rule eval_l_cong)
      fix x
      show "x \<in> vars_l (P i) \<Longrightarrow> \<alpha> x = \<gamma> x" 
        by (rule ab, insert vV[of i] inv, auto)
    qed
  }
  with f have f: "f (\<lambda>i. eval_l \<gamma> (P i))" by auto
  {
    fix i
    have "eval_l (\<lambda>x. eval_l \<gamma> (\<sigma> x)) (P i) = eval_l \<gamma> (P i)"
    proof (intro eval_l_cong)
      fix x
      note defs = \<sigma> solution_subst_def 
      show "eval_l \<gamma> (\<sigma> x) = \<gamma> x" 
      proof (cases "x \<in> fst ` S")
        case False 
        thus ?thesis unfolding defs S_list[symmetric] 
          by (force split: option.splits dest: map_of_SomeD)
      next
        case True
        then obtain e where xe: "(x,e) \<in> S" by force
        have "\<exists>! e. (x,e) \<in> S" using inv True by auto
        with xe have "map_of S_list x = Some e" unfolding S_list[symmetric] 
          by (metis map_of_SomeD weak_map_of_SomeI)
        hence id: "\<sigma> x = e" unfolding defs by auto
        show ?thesis unfolding id using xe sat by auto
      qed
    qed
  }
  thus "\<exists>\<gamma>. f (\<lambda>i. eval_l \<gamma> (substitute_all_l \<sigma> (P i)))" 
    unfolding eval_substitute_all_l
    by (intro exI[of _ \<gamma>], insert f, auto)
qed

corollary griggio_success_equivalence: 
  fixes P :: "'i \<Rightarrow> (int,'v)lpoly" and f :: "('i \<Rightarrow> int) \<Rightarrow> bool" 
  assumes "(Some (({},E),{}), Some ((S,{}),X)) \<in> griggio_step^*"
    and \<sigma>: "\<sigma> = solution_subst S_list" 
    and S_list: "set S_list = S" 
    and vV: "\<And> i. vars_l (P i) \<subseteq> V" 
  shows 
    "(\<exists> \<alpha>. f (\<lambda> i. eval_l \<alpha> (substitute_all_l \<sigma> (P i))))
     \<longleftrightarrow> (\<exists> \<alpha>. f (\<lambda> i. eval_l \<alpha> (P i)) \<and> Ball E (satisfies_dleq \<alpha>))"
proof -
  note main = griggio_success_translations[OF assms(1,2) S_list, of f _ P]
  from main(1)[OF _ refl] main(2)[OF _ vV]
  show ?thesis by blast
qed

end (* assuming vars(E) \<subseteq> V *)
end (* fixing E and V *)


end