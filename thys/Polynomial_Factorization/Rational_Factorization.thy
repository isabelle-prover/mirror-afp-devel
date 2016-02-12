(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Rational Factorization\<close>

text \<open>We combine the rational root test, the factorization oracle, the
  formulas for explicit roots, and the Kronecker's factorization algorithm to provide a
  factorization algorithm for polynomial over rational numbers. Moreover, also the roots
  of a rational polynomial can be determined.

  The factorization provides three modes: one where an uncertified factorization is performed,
  one which tests on irreducibility, and one which combines the previous two modes.
  
  Note that in order to use this theory, one also has to load an factorization oracle, e.g., 
  the one in theory Berlekamp-Hensel-Factorization.\<close>

theory Rational_Factorization
imports
  Explicit_Roots
  Kronecker_Factorization
  Square_Free_Factorization
  Factorization_Oracle
  Rational_Root_Test
  Polynomial_Division
  "../Show/Show_Poly"
begin

function roots_of_rat_poly_main :: "rat poly \<Rightarrow> rat list" where 
  [code del]: "roots_of_rat_poly_main p = (let n = degree p in if n = 0 then [] else if n = 1 then [roots1 p]
  else if n = 2 then rat_roots2 p else 
  case rational_root_test p of None \<Rightarrow> [] | Some x \<Rightarrow> x # roots_of_rat_poly_main (p div [:-x,1:]))"
  by pat_completeness auto

termination by (relation "measure degree", 
  auto dest: rational_root_test(1) intro!: degree_div_less simp: poly_eq_0_iff_dvd)

lemma roots_of_rat_poly_main_code[code]: "roots_of_rat_poly_main p = (let n = degree p in if n = 0 then [] else if n = 1 then [roots1 p]
  else if n = 2 then rat_roots2 p else 
  case rational_root_test p of None \<Rightarrow> [] | Some x \<Rightarrow> x # roots_of_rat_poly_main (exact_div p [:-x,1:]))"
proof -
  note d = roots_of_rat_poly_main.simps[of p] Let_def
  show ?thesis
  proof (cases "rational_root_test p")
    case (Some x)
    let ?x = "[:-x,1:]"
    from rational_root_test(1)[OF Some] have  "?x dvd p" 
      by (simp add: poly_eq_0_iff_dvd)
    from dvd_mult_div_cancel[OF this]
    have pp: "exact_div p ?x = exact_div (?x * (p div ?x)) ?x" by simp
    also have "\<dots> = p div ?x"
      by (rule exact_div_left, auto)
    finally show ?thesis unfolding d Some by auto
  qed (simp add: d)
qed

lemma roots_of_rat_poly_main: "p \<noteq> 0 \<Longrightarrow> set (roots_of_rat_poly_main p) = {x. poly p x = 0}"
proof (induct p rule: roots_of_rat_poly_main.induct)
  case (1 p)
  note IH = 1(1)
  note p = 1(2)
  let ?n = "degree p"
  let ?rr = "roots_of_rat_poly_main"
  show ?case
  proof (cases "?n = 0")
    case True
    from roots0[OF p True] True show ?thesis by simp
  next
    case False note 0 = this
    show ?thesis
    proof (cases "?n = 1")
      case True
      from roots1[OF True] True show ?thesis by simp
    next
      case False note 1 = this
      show ?thesis
      proof (cases "?n = 2")
        case True
        from rat_roots2[OF True] True show ?thesis by simp
      next
        case False note 2 = this
        from 0 1 2 have id: "?rr p = (case rational_root_test p of None \<Rightarrow> [] | Some x \<Rightarrow> 
          x # ?rr (p div [: -x, 1 :]))" by simp
        show ?thesis
        proof (cases "rational_root_test p")
          case None
          from rational_root_test(2)[OF None] None id show ?thesis by simp
        next
          case (Some x)
          from rational_root_test(1)[OF Some] have "[: -x, 1:] dvd p"         
            by (simp add: poly_eq_0_iff_dvd)
          from dvd_mult_div_cancel[OF this]
          have pp: "p = [: -x, 1:] * (p div [: -x, 1:])" by simp
          with p have p: "p div [:- x, 1:] \<noteq> 0" by auto
          from arg_cong[OF pp, of "\<lambda> p. {x. poly p x = 0}"]
             rational_root_test(1)[OF Some] IH[OF refl 0 1 2 Some p]  show ?thesis
            unfolding id Some by auto
        qed
      qed
    qed
  qed
qed

declare roots_of_rat_poly_main.simps[simp del]

definition roots_of_rat_poly :: "rat poly \<Rightarrow> rat list" where
  "roots_of_rat_poly p \<equiv> let (c,pis) = yun_factorization gcd_rat_poly p in
    concat (map (roots_of_rat_poly_main o fst) pis)"

lemma roots_of_rat_poly: assumes p: "p \<noteq> 0"
  shows "set (roots_of_rat_poly p) = {x. poly p x = 0}"
proof -
  obtain c pis where yun: "yun_factorization gcd p = (c,pis)" by force
  from yun
  have res: "roots_of_rat_poly p = concat (map (roots_of_rat_poly_main \<circ> fst) pis)"
    by (auto simp: roots_of_rat_poly_def split: if_splits)
  note yun = square_free_factorizationD(1,2,4)[OF yun_factorization(1)[OF yun]]
  from yun(1) p have c: "c \<noteq> 0" by auto
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  have "{x. poly p x = 0} = {x. poly (\<Prod>(a, i)\<in>set pis. a ^ Suc i) x = 0}"
    unfolding p using c by auto
  also have "\<dots> = \<Union> ((\<lambda> p. {x. poly p x = 0}) ` fst ` set pis)" (is "_ = ?r")
    by (subst poly_setprod_0, force+)
  finally have r: "{x. poly p x = 0} = ?r" .
  {
    fix p i
    assume p: "(p,i) \<in> set pis"
    have "set (roots_of_rat_poly_main p) = {x. poly p x = 0}"
      by (rule roots_of_rat_poly_main, insert yun(2) p, force)
  } note main = this
  have "set (roots_of_rat_poly p) = \<Union> ((\<lambda> (p, i). set (roots_of_rat_poly_main p)) ` set pis)" 
    unfolding res o_def by auto
  also have "\<dots> = ?r" using main by auto
  finally show ?thesis unfolding r by simp
qed

definition root_free :: "'a :: comm_semiring_0 poly \<Rightarrow> bool" where
  "root_free p = (degree p = 1 \<or> (\<forall> x. poly p x \<noteq> 0))"

lemma irreducible_root_free: assumes irr: "irreducible p" shows "root_free p"
proof (cases "degree p = 1")
  case False
  {
    fix x
    assume "poly p x = 0"
    hence "[:-x,1:] dvd p" using poly_eq_0_iff_dvd by blast
    with False irr[unfolded irreducible_def] have False by auto
  }
  thus ?thesis unfolding root_free_def by auto
qed (auto simp: root_free_def)

partial_function (tailrec) factorize_root_free_main :: "rat poly \<Rightarrow> rat list \<Rightarrow> rat poly list \<Rightarrow> rat \<times> rat poly list" where
  [code]: "factorize_root_free_main p xs fs = (case xs of Nil \<Rightarrow> 
     let l = coeff p (degree p); q = smult (inverse l) p in (l, (if q = 1 then fs else q # fs) )
  | x # xs \<Rightarrow> 
    if poly p x = 0 then factorize_root_free_main (p div [:-x,1:]) (x # xs) ([:-x,1:] # fs)
    else factorize_root_free_main p xs fs)"

(* TODO: one might group identical roots *)
definition factorize_root_free :: "rat poly \<Rightarrow> rat \<times> rat poly list" where
  "factorize_root_free p = (if p = 0 then (0,[]) else
     factorize_root_free_main p (roots_of_rat_poly p) [])"

lemma factorize_root_free: assumes res: "factorize_root_free p = (c,qs)" 
  shows "p = smult c (listprod qs)" 
  "\<And> q. q \<in> set qs \<Longrightarrow> root_free q \<and> monic q"
proof -
  have "p = smult c (listprod qs) \<and> (\<forall> q \<in> set qs. root_free q \<and> monic q)"
  proof (cases "p = 0")
    case True
    thus ?thesis using res unfolding factorize_root_free_def by auto
  next
    case False
    def fs \<equiv> "[] :: rat poly list" 
    def xs \<equiv> "roots_of_rat_poly p"
    def q \<equiv> p
    obtain n  where n: "n = degree q + length xs" by auto 
    have prod: "p = q * listprod fs" unfolding q_def fs_def by auto
    have sub: "{x. poly q x = 0} \<subseteq> set xs" using roots_of_rat_poly[OF False] unfolding q_def xs_def by auto
    have fs: "\<And> q. q \<in> set fs \<Longrightarrow> root_free q \<and> monic q" unfolding fs_def by auto
    have res: "factorize_root_free_main q xs fs = (c,qs)" using res False 
      unfolding xs_def fs_def q_def factorize_root_free_def by auto
    from False have "q \<noteq> 0" unfolding q_def by auto
    from prod sub fs res n this show ?thesis
    proof (induct n arbitrary: q fs xs rule: wf_induct[OF wf_less])
      case (1 n q fs xs)
      note simp = factorize_root_free_main.simps[of q xs fs]
      note IH = 1(1)[rule_format]
      note 0 = 1(2-)[unfolded simp]
      show ?case
      proof (cases xs)
        case Nil
        note 0 = 0[unfolded Nil Let_def]
        hence no_rt: "\<And> x. poly q x \<noteq> 0" by auto
        hence q: "q \<noteq> 0" by auto
        let ?r = "smult (inverse c) q"
        def r \<equiv> ?r
        from 0(4-5) have c: "c = coeff q (degree q)" and qs: "qs = (if r = 1 then fs else r # fs)" by (auto simp: r_def)
        from q c qs 0(1) have c0: "c \<noteq> 0" and p: "p = smult c (listprod (r # fs))" by (auto simp: r_def)
        from p have p: "p = smult c (listprod qs)" unfolding qs by auto 
        from 0(2,5) c0 c have "root_free ?r" "monic ?r" 
          unfolding root_free_def by auto
        with 0(3) have "\<And> q. q \<in> set qs \<Longrightarrow> root_free q \<and> monic q" unfolding qs by (auto split: if_splits simp: r_def)
        with p show ?thesis by auto
      next
        case (Cons x xs)
        note 0 = 0[unfolded Cons]
        show ?thesis
        proof (cases "poly q x = 0")
          case True
          let ?q = "q div [:-x,1:]"
          let ?x = "[:-x,1:]" 
          let ?fs = "?x # fs"
          let ?xs = "x # xs"
          from True have q: "q = ?q * ?x"
            by (metis dvd_mult_div_cancel mult.commute poly_eq_0_iff_dvd)
          with 0(6) have q': "?q \<noteq> 0" by auto
          have deg: "degree q = Suc (degree ?q)" unfolding arg_cong[OF q, of degree] 
            by (subst degree_mult_eq[OF q'], auto)
          hence n: "degree ?q + length ?xs < n" unfolding 0(5) by auto
          from arg_cong[OF q, of poly] 0(2) have rt: "{x. poly ?q x = 0} \<subseteq> set ?xs" by auto
          have p: "p = ?q * listprod ?fs" unfolding listprod.Cons 0(1) mult.assoc[symmetric] q[symmetric] ..
          have "root_free ?x" unfolding root_free_def by auto
          with 0(3) have rf: "\<And> f. f \<in> set ?fs \<Longrightarrow> root_free f \<and> monic f" by auto
          from True 0(4) have res: "factorize_root_free_main ?q ?xs ?fs = (c,qs)" by simp
          show ?thesis
            by (rule IH[OF _ p rt rf res refl q'], insert n, auto)
        next
          case False
          with 0(4) have res: "factorize_root_free_main q xs fs = (c,qs)" by simp
          from 0(5) obtain m where m: "m = degree q + length xs" and n: "n = Suc m" by auto
          from False 0(2) have rt: "{x. poly q x = 0} \<subseteq> set xs" by auto
          show ?thesis by (rule IH[OF _ 0(1) rt 0(3) res m 0(6)], unfold n, auto)
        qed
      qed
    qed
  qed
  thus "p = smult c (listprod qs)" 
    "\<And> q. q \<in> set qs \<Longrightarrow> root_free q \<and> monic q" by auto
qed


definition rational_proper_factor :: "rat poly \<Rightarrow> rat poly option" where
  "rational_proper_factor p = (if degree p \<le> 1 then None
    else if degree p = 2 then (case rat_roots2 p of Nil \<Rightarrow> None | Cons x xs \<Rightarrow> Some [:-x,1 :])
    else if degree p = 3 then (case rational_root_test p of None \<Rightarrow> None | Some x \<Rightarrow> Some [:-x,1:])
    else kronecker_factorization_rat p)"

lemma degree_1_dvd_root: assumes q: "degree (q :: 'a :: field poly) = 1"
  and rt: "\<And> x. poly p x \<noteq> 0"
  shows "\<not> q dvd p"
proof -
  from degree1_coeffs[OF q] obtain a b where q: "q = [: b, a :]" and a: "a \<noteq> 0" by auto
  have q: "q = smult a [: - (- b / a), 1 :]" unfolding q 
    by (rule poly_eqI, unfold coeff_smult, insert a, auto simp: field_simps coeff_pCons
      split: nat.splits)
  show ?thesis unfolding q smult_dvd_iff poly_eq_0_iff_dvd[symmetric, of _ p] using a rt by auto
qed




lemma rational_proper_factor: 
  "degree p \<noteq> 0 \<Longrightarrow> rational_proper_factor p = None \<Longrightarrow> irreducible p" 
  "rational_proper_factor p = Some q \<Longrightarrow> q dvd p \<and> degree q \<ge> 1 \<and> degree q < degree p"
proof -
  let ?rp = "rational_proper_factor p"
  let ?rr = "rational_root_test"
  note d = rational_proper_factor_def[of p]
  have "(degree p \<noteq> 0 \<longrightarrow> ?rp = None \<longrightarrow> irreducible p) \<and> 
        (?rp = Some q \<longrightarrow> q dvd p \<and> degree q \<ge> 1 \<and> degree q < degree p)"
  proof (cases "degree p = 0")
    case True
    thus ?thesis unfolding d by auto
  next
    case False note 0 = this
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence "?rp = None" unfolding d by auto
      with linear_irreducible[OF True] show ?thesis by auto
    next
      case False note 1 = this
      show ?thesis
      proof (cases "degree p = 2")
        case True
        hence rp: "?rp = (case rat_roots2 p of Nil \<Rightarrow> None | Cons x xs \<Rightarrow> Some [:-x,1 :])" unfolding d by auto
        show ?thesis
        proof (cases "rat_roots2 p")
          case Nil
          with rp have rp: "?rp = None" by auto
          from Nil rat_roots2[OF True] have nex: "\<not> (\<exists> x. poly p x = 0)" by auto
          have "irreducible p"
          proof (rule irreducibleI)
            fix q :: "rat poly"
            assume "degree q \<noteq> 0" "degree q < degree p"
            with True have dq: "degree q = 1" by auto
            show "\<not> q dvd p" 
              by (rule degree_1_dvd_root[OF dq], insert nex, auto)
          qed (insert True, auto)
          with rp show ?thesis by auto
        next
          case (Cons x xs)
          from Cons rat_roots2[OF True] have "poly p x = 0" by auto
          from this[unfolded poly_eq_0_iff_dvd] have x: "[: -x , 1 :] dvd p" by auto
          from Cons rp have rp: "?rp = Some ([: - x, 1 :])" by auto
          show ?thesis using True x unfolding rp by auto
        qed
      next
        case False note 2 = this
        show ?thesis
        proof (cases "degree p = 3")
          case True
          hence rp: "?rp = (case ?rr p of None \<Rightarrow> None | Some x \<Rightarrow> Some [:- x, 1:])" unfolding d by auto
          show ?thesis
          proof (cases "?rr p")
            case None
            from rational_root_test(2)[OF None] have nex: "\<not> (\<exists> x. poly p x = 0)" by auto
            from rp[unfolded None] have rp: "?rp = None" by auto
            have "irreducible p"
            proof (rule irreducibleI2)
              fix q :: "rat poly"
              assume "degree q \<ge> 1" "degree q \<le> degree p div 2"
              with True have dq: "degree q = 1" by auto
              show "\<not> q dvd p" 
                by (rule degree_1_dvd_root[OF dq], insert nex, auto)
            qed (insert True, auto)
            with rp show ?thesis by auto
          next
            case (Some x)
            from rational_root_test(1)[OF Some] have "poly p x = 0" .
            from this[unfolded poly_eq_0_iff_dvd] have x: "[: -x , 1 :] dvd p" by auto
            from Some rp have rp: "?rp = Some ([: - x, 1 :])" by auto
            show ?thesis using True x unfolding rp by auto
          qed
        next
          case False note 3 = this
          let ?kp = "kronecker_factorization_rat p"
          from 0 1 2 3 have d4: "degree p \<ge> 4" and d1: "degree p \<ge> 1" by auto
          hence rp: "?rp = ?kp" using d4 d by auto
          show ?thesis
          proof (cases ?kp)
            case None
            with rp kronecker_factorization_rat(2)[OF None d1] show ?thesis by auto
          next
            case (Some q)
            with rp kronecker_factorization_rat(1)[OF Some] show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
  thus "degree p \<noteq> 0 \<Longrightarrow> rational_proper_factor p = None \<Longrightarrow> irreducible p" 
    "rational_proper_factor p = Some q \<Longrightarrow> q dvd p \<and> degree q \<ge> 1 \<and> degree q < degree p" by auto
qed

function factorize_rat_poly_main :: "rat \<Rightarrow> rat poly list \<Rightarrow> rat poly list \<Rightarrow> rat \<times> rat poly list" where
  "factorize_rat_poly_main c irr [] = (c,irr)"
| "factorize_rat_poly_main c irr (p # ps) = (if degree p = 0 
    then factorize_rat_poly_main (c * coeff p 0) irr ps 
    else (case rational_proper_factor p of 
      None \<Rightarrow> factorize_rat_poly_main c (p # irr) ps
    | Some q \<Rightarrow> factorize_rat_poly_main c irr (q # p div q # ps)))"
  by pat_completeness auto

definition "factorize_rat_poly_main_wf_rel = inv_image (mult1 {(x, y). x < y}) (\<lambda>(c, irr, ps). mset (map degree ps))"

lemma wf_factorize_rat_poly_main_wf_rel: "wf factorize_rat_poly_main_wf_rel"
  unfolding factorize_rat_poly_main_wf_rel_def using wf_mult1[OF wf_less] by auto

lemma factorize_rat_poly_main_wf_rel_sub: "((a,b,ps), (c,d,p # ps)) \<in> factorize_rat_poly_main_wf_rel"
  unfolding factorize_rat_poly_main_wf_rel_def 
  by (auto simp: mult1_def) (metis add.right_neutral count_empty not_less0)

lemma factorize_rat_poly_main_wf_rel_two: assumes "degree q < degree p" "degree r < degree p"
  shows "((a,b,q # r # ps), (c,d,p # ps)) \<in> factorize_rat_poly_main_wf_rel"
  unfolding factorize_rat_poly_main_wf_rel_def mult1_def
  using add_eq_conv_ex assms ab_semigroup_add_class.add_ac
    by fastforce

termination 
proof (relation factorize_rat_poly_main_wf_rel,
  rule wf_factorize_rat_poly_main_wf_rel, rule factorize_rat_poly_main_wf_rel_sub, 
  rule factorize_rat_poly_main_wf_rel_sub, rule factorize_rat_poly_main_wf_rel_two)
  fix p q
  assume rf: "rational_proper_factor p = Some q" and dp: "degree p \<noteq> 0"
  from rational_proper_factor(2)[OF rf] 
  have dvd: "q dvd p" and deg: "1 \<le> degree q" "degree q < degree p" by auto
  show "degree q < degree p" by fact
  from dvd have "p = q * (p div q)" by auto
  from arg_cong[OF this, of degree]
  have "degree p = degree q + degree (p div q)"
    by (subst degree_mult_eq[symmetric], insert dp, auto)
  with deg
  show "degree (p div q) < degree p" by simp
qed  

declare factorize_rat_poly_main.simps[simp del]

lemma factorize_rat_poly_main: assumes "factorize_rat_poly_main c irr ps = (d,qs)"
  and "Ball (set irr) irreducible"
  shows "Ball (set qs) irreducible \<and> smult c (listprod (irr @ ps)) = smult d (listprod qs)"
  using assms
proof (induct c irr ps rule: factorize_rat_poly_main.induct)
  case (1 c irr)
  thus ?case by (auto simp: factorize_rat_poly_main.simps)
next
  case (2 c irr p ps)
  note IH = 2(1-3)
  note res = 2(4)[unfolded factorize_rat_poly_main.simps(2)[of c irr p ps]]
  note irr = 2(5)
  let ?f = factorize_rat_poly_main
  show ?case
  proof (cases "degree p = 0")
    case True
    with res have res: "?f (c * coeff p 0) irr ps = (d,qs)" by simp
    from degree0_coeffs[OF True] obtain a where p: "p = [: a :]" by auto
    from IH(1)[OF True res irr]
    show ?thesis using p by simp
  next
    case False
    note IH = IH(2-)[OF False]
    from False have "(degree p = 0) = False" by auto
    note res = res[unfolded this if_False]
    let ?rf = "rational_proper_factor p"
    show ?thesis
    proof (cases ?rf)
      case None
      with res have res: "?f c (p # irr) ps = (d,qs)" by auto
      from rational_proper_factor(1)[OF `degree p \<noteq> 0` None] 
      have irp: "irreducible p" by auto
      from IH(1)[OF None res] irr irp show ?thesis by (auto simp: ac_simps)
    next
      case (Some q)
      def pq \<equiv> "p div q" 
      from Some res have res: "?f c irr (q # pq # ps) = (d,qs)" unfolding pq_def by auto
      from rational_proper_factor(2)[OF Some] have "q dvd p" by auto
      hence p: "p = q * pq" unfolding pq_def by auto
      from IH(2)[OF Some, folded pq_def, OF res irr] show ?thesis unfolding p 
        by (auto simp: ac_simps)
    qed
  qed
qed

definition exp_const_poly :: "'a :: field \<times> 'a poly list \<Rightarrow> nat \<Rightarrow> 'a :: field \<times> ('a poly \<times> nat) list" where
  "exp_const_poly cps n \<equiv> case cps of (c,ps) \<Rightarrow> (c ^ n, map (\<lambda> p. (p,n)) ps)"

lemma exp_const_poly: assumes "exp_const_poly (c,ps) n = (d,qns)"
  shows "(smult c (listprod ps)) ^ n = smult d (listprod (map (\<lambda> (q,i). q ^ i) qns))"
  "map fst qns = ps" "snd ` set qns \<subseteq> {n}"
proof -
  from assms[unfolded exp_const_poly_def split] have d: "d = c ^ n"
    and qns: "qns = map (\<lambda>p. (p, n)) ps" by auto
  show "map fst qns = ps" unfolding qns by (rule nth_equalityI, auto)
  show "snd ` set qns \<subseteq> {n}" unfolding qns by auto
  show "(smult c (listprod ps)) ^ n = smult d (listprod (map (\<lambda> (q,i). q ^ i) qns))"
    unfolding smult_power d qns map_map o_def split listprod_power by simp
qed

datatype factorization_mode = Uncertified_Factorization | Full_Factorization | Check_Irreducible
  | Check_Root_Free

text \<open>@{const Uncertified_Factorization}: just apply oracle @{const factorization_oracle_rat_poly}, 
     result will be a factorization, but not guaranteed into irreducible factors.

  @{const Full_Factorization}: first apply oracle, and then factor in a certified (and slow) way into
     irreducible factors with @{const factorize_rat_poly_main}.

  @{const Check_Irreducible}: don't apply oracle and just check irreducibility via 
     @{const factorize_rat_poly_main}. Useful if
     one already knows that input is factor that was obtained from oracle.

  @{const Check_Root_Free}: don't apply oracle and just check that there all factors are linear or root free 
     @{const factorize_root_free}. Useful if
     one already knows that input is factor that was obtained from oracle.
  \<close>

context
  fixes mode :: factorization_mode
begin

definition initial_factorization_rat :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "initial_factorization_rat p = (
    if mode = Check_Irreducible \<or> mode = Check_Root_Free then (if p = 0 then (0,[]) else (1,[(p,1)]))
    else 
    case factorization_oracle_rat_poly p of 
      (c,pis) \<Rightarrow> if p = smult c ((\<Prod>(q, i)\<leftarrow>pis. q ^ i)) \<and> list_all (\<lambda> (p,i). i \<noteq> 0 \<and> p \<noteq> 0) pis 
      then (c,pis) 
      else Code.abort (String.implode (''error in factorization-oracle on input '' @
        show_poly p)) (\<lambda> _. case yun_factorization gcd_rat_poly p of 
        (c,pis) \<Rightarrow> (c, map (\<lambda> (p,i). (p, Suc i)) pis)))"

lemma initial_factorization_rat: assumes res: "initial_factorization_rat p = (c,qis)"
  shows "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" "(q,i) \<in> set qis \<Longrightarrow> i \<noteq> 0 \<and> q \<noteq> 0"
proof -
  obtain d pis where fo: "factorization_oracle_rat_poly p = (d,pis)" by force
  note res = res[unfolded initial_factorization_rat_def fo split]
  have "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i) \<and> ((q,i) \<in> set qis \<longrightarrow> i \<noteq> 0 \<and> q \<noteq> 0)" 
  proof (cases "mode = Check_Irreducible \<or> mode = Check_Root_Free")
    case True
    with res show ?thesis by (cases "p = 0", auto)
  next
    case False note mode = this
    show ?thesis
    proof (cases "p = smult d (\<Prod>(q, i)\<leftarrow>pis. q ^ i) \<and> list_all (\<lambda> (p,i). i \<noteq> 0 \<and> p \<noteq> 0) pis")
      case True
      with mode res have id: "c = d" "qis = pis" by auto
      with True show ?thesis by (auto simp: list_all_iff)
    next
      case False
      obtain d pis where yun: "yun_factorization gcd p = (d,pis)" by force
      with res False mode have id: "c = d" "qis = map (\<lambda> (p,i). (p, Suc i)) pis" by auto
      from square_free_factorizationD(1,2,5)[OF yun_factorization(1)[OF yun]]
      have p: "p = smult d (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" and pis: "distinct pis" 
        and nz: "\<And> p i. (p,i) \<in> set pis \<Longrightarrow> p \<noteq> 0" by fastforce+
      have "(\<Prod>(a, i)\<in>set pis. a ^ Suc i) = (\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i)"
        by (rule setprod.distinct_set_conv_list[OF pis])
      also have "\<dots> = (\<Prod>(a, i)\<leftarrow>qis. a ^ i)" unfolding id
        by (induct pis, auto)
      finally have p: "p = smult d (\<Prod>(a, i)\<leftarrow>qis. a ^ i)" unfolding p by auto
      with id nz show ?thesis by auto
    qed
  qed
  thus "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" "(q,i) \<in> set qis \<Longrightarrow> i \<noteq> 0 \<and> q \<noteq> 0" by blast+
qed

definition factorize_rat_poly_start :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "factorize_rat_poly_start p \<equiv> let
    (c,pi) = initial_factorization_rat p
    in if mode = Full_Factorization \<or> mode = Check_Irreducible then let
    powers = map (\<lambda> (p,i). exp_const_poly (factorize_rat_poly_main 1 [] [p]) i) pi;
    const = c * listprod (map fst powers);
    polys = concat (map snd powers)
    in (const, polys) else 
    if mode = Check_Root_Free then let
      (c,ps) = factorize_root_free p 
      in (c,map (\<lambda> q. (q,1)) ps)
    else (c,pi)"

lemma factorize_rat_poly_start: assumes "factorize_rat_poly_start p = (c,qis)"
  shows 
  "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" 
  "(q,i) \<in> set qis \<Longrightarrow> 
    (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and>
    (mode = Check_Root_Free \<longrightarrow> root_free q \<and> monic q) \<and> i \<noteq> 0 \<and> q \<noteq> 0"
proof -
  obtain c1 pi where init: "initial_factorization_rat p = (c1,pi)" by force
  from initial_factorization_rat[OF this] have p: "p = smult c1 (\<Prod>(a, i)\<leftarrow>pi. a ^ i)"
    and i: "\<And> q i. (q,i) \<in> set pi \<Longrightarrow> i \<noteq> 0 \<and> q \<noteq> 0" by auto
  note res = assms[unfolded factorize_rat_poly_start_def Let_def init split]
  have "(p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)) \<and> 
    ((q,i) \<in> set qis \<longrightarrow> (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and>
    (mode = Check_Root_Free \<longrightarrow> root_free q \<and> monic q) \<and> i \<noteq> 0 \<and> q \<noteq> 0)"
  proof (cases "mode = Uncertified_Factorization")
    case True
    with p i res
    show ?thesis by auto 
  next
    case False note UF = this
    show ?thesis
    proof (cases "mode = Full_Factorization \<or> mode = Check_Irreducible")
      case True
      def powers \<equiv> "map (\<lambda>(p, i). exp_const_poly (factorize_rat_poly_main 1 [] [p]) i) pi"    
      from res[folded powers_def] True have c: "c = c1 * listprod (map fst powers)" 
        and qis: "qis = concat (map snd powers)" by auto  
      def left \<equiv> "\<lambda> x :: rat poly \<times> nat. (case x of (a,i) \<Rightarrow> a ^ i)"
      def right \<equiv> "\<lambda> x :: rat \<times> (rat poly \<times> nat) list. case x of (c,ps) \<Rightarrow> smult c (\<Prod>(a, i) \<leftarrow> ps. a ^ i)"
      {
        fix j
        assume "j < length powers"
        hence j: "j < length pi" unfolding powers_def by auto
        obtain a i where pij: "pi ! j = (a,i)" by force
        with j have "(a,i) \<in> set pi" unfolding set_conv_nth by force
        from i[OF this] have i: "i \<noteq> 0" by blast
        have powj: "powers ! j = exp_const_poly (factorize_rat_poly_main 1 [] [a]) i" 
          unfolding powers_def nth_map[OF j] pij by auto
        obtain d irr where fact: "factorize_rat_poly_main 1 [] [a] = (d,irr)" by force
        from factorize_rat_poly_main[OF this] have irr: "Ball (set irr) irreducible"
          and a: "a = smult d (listprod irr)" by auto
        obtain e qs where exp: "exp_const_poly (d, irr) i = (e,qs)" by force
        note exp' = exp_const_poly[OF exp]
        have "left (pi ! j) = right (powers ! j)"
          "Ball (fst ` set (snd (powers ! j))) irreducible"
          "Ball (snd ` set (snd (powers ! j))) (\<lambda> x. x \<noteq> 0)"
          unfolding pij powj split fact left_def right_def unfolding a exp split using exp' irr i by force+
      } note powers = this
      {
        fix q i
        assume "(q,i) \<in> set qis" 
        from this[unfolded qis] obtain ps where 
          ps: "ps \<in> snd ` set powers" and qi: "(q,i) \<in> set ps" by auto
        from ps obtain pair where "pair \<in> set powers"  and "ps = snd pair" by auto
        hence "(fst pair, ps) \<in> set powers" by auto
        then obtain j where j: "j < length powers" and pj: "powers ! j = (fst pair, ps)" 
          unfolding set_conv_nth by auto
        from powers[OF j, unfolded pj] qi
        have "irreducible q \<and> i \<noteq> 0" by auto
        hence "irreducible q \<and> i \<noteq> 0 \<and> q \<noteq> 0" unfolding irreducible_def by auto
      } note irr = this
      have len: "length pi = length powers" unfolding powers_def by auto
      hence id: "(\<Prod>(a, i)\<leftarrow>pi. a ^ i) = 
        smult (listprod (map fst powers)) (\<Prod>(q, i)\<leftarrow>concat (map snd powers). q ^ i)"
        using powers(1)
      proof (induct pi powers rule: list_induct2)
        case (Cons x pi y powers)
        have IH: "(\<Prod>(a, i)\<leftarrow>pi. a ^ i) = 
          smult (listprod (map fst powers)) (\<Prod>(q, i)\<leftarrow>concat (map snd powers). q ^ i)"
          by (rule Cons(2), insert Cons(3)[of "Suc i" for i], auto)
        from Cons(3)[of 0] have precond: "left x = right y" by auto
        obtain p n where x: "x = (p,n)" by force
        obtain c ps where y: "y = (c,ps)" by force    
        from precond[unfolded left_def right_def x y split]
        have precond: "p ^ n = smult c (\<Prod>(x, y)\<leftarrow>ps. x ^ y)" by auto
        have id: "(\<Prod>a\<leftarrow>x # pi. case a of (a, i) \<Rightarrow> a ^ i)  = p ^ n * (\<Prod>(a, i)\<leftarrow>pi. a ^ i)"
          unfolding x by simp      
        show ?case unfolding id precond IH y by (auto simp: ac_simps)
      qed (simp add: one_poly_def)
      show ?thesis using irr unfolding p c qis id using True by auto
    next
      case False
      with UF have RF: "mode = Check_Root_Free" by (cases mode, auto)
      note res = res[unfolded RF]
      from res
      obtain qs where fact: "factorize_root_free p = (c,qs)" by (auto split: prod.splits)
      with res have qis: "qis = map (\<lambda> q. (q,1)) qs" by auto
      note fact = factorize_root_free[OF fact] 
      {
        fix q
        assume "q \<in> set qs"
        from fact(2)[OF this] have "q \<noteq> 0" by auto
      }
      thus ?thesis unfolding RF qis using fact by (auto simp: o_def)
    qed
  qed
  thus "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" 
    "(q,i) \<in> set qis \<Longrightarrow> 
    (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and>
    (mode = Check_Root_Free \<longrightarrow> root_free q \<and> monic q) \<and> i \<noteq> 0 \<and> q \<noteq> 0" by blast+
qed

fun normalize_factorization :: "'a :: field \<times> ('a poly \<times> nat) list \<Rightarrow> 'a \<times> ('a poly \<times> nat) list" where
  "normalize_factorization (c,[]) = (c,[])"
| "normalize_factorization (c,((p,n) # ps)) = (let 
     d = coeff p (degree p);
     q = smult (inverse d) p;
     (e,res) = normalize_factorization (c * d ^ n,ps)
   in (e, (q,n) # res))"

lemma normalize_factorization: assumes "normalize_factorization (c,pis) = (d,qis)"
  and "\<And> p i. (p,i) \<in> set pis \<Longrightarrow> p \<noteq> 0"
  shows "smult c (\<Prod>(q, i)\<leftarrow>pis. q ^ i) = smult d (\<Prod>(q, i)\<leftarrow>qis. q ^ i) \<and> 
    (\<forall> q i. (q,i) \<in> set qis \<longrightarrow> monic q \<and> (\<exists> p a. (p,i) \<in> set pis \<and> q = smult a p \<and> a \<noteq> 0))"
  using assms
proof (induct "length pis" arbitrary: c pis d qis)
  case (0 pis c d qis)
  thus ?case by auto
next
  case (Suc l ppis c d qis)
  from Suc(2) obtain pn pis where ppis: "ppis = pn # pis" by (cases ppis, auto)
  obtain p n where pn: "pn = (p,n)" by force
  from Suc(2) ppis have "l = length pis" by auto
  note IH = Suc(1)[OF this]
  def cp \<equiv> "coeff p (degree p)"
  def q \<equiv> "smult (inverse cp) p"
  from Suc(4)[unfolded ppis pn] have "p \<noteq> 0" by auto
  hence cp: "inverse cp \<noteq> 0" unfolding cp_def by auto
  obtain e ris where nf: "normalize_factorization (c * cp ^ n, pis) = (e,ris)" by force
  have p: "p = smult cp q" and q: "q = smult (inverse cp) p" unfolding cp_def q_def
    by (auto simp: field_simps)
  have m: "monic q" unfolding q_def cp_def using `p \<noteq> 0` by auto
  from Suc(3)[unfolded ppis pn normalize_factorization.simps Let_def nf split cp_def[symmetric]]
  have d: "d = e" and qis: "qis = (q, n) # ris" unfolding cp_def q_def by auto
  from IH[OF nf Suc(4)[unfolded ppis]] have id: "smult (c * cp ^ n) (\<Prod>(x, y)\<leftarrow>pis. x ^ y) = smult e (\<Prod>(x, y)\<leftarrow>ris. x ^ y)"
    and ris: "\<And> q i. (q, i) \<in> set ris \<Longrightarrow> monic q \<and> (\<exists>p a. (p, i) \<in> set pis \<and> q = smult a p \<and> a \<noteq> 0)" by force+
  have "smult c (\<Prod>(x, y)\<leftarrow>ppis. x ^ y) = smult c (p ^ n * (\<Prod>(x, y)\<leftarrow>pis. x ^ y))"
    unfolding ppis pn by auto
  also have "p ^ n = smult (cp ^ n) (q ^ n)" unfolding p smult_power ..
  also have "smult c (\<dots> * (\<Prod>(x, y)\<leftarrow>pis. x ^ y)) = q ^ n * smult (c * cp ^ n) (\<Prod>(x, y)\<leftarrow>pis. x ^ y)"
    by (simp add: ac_simps)
  also have "\<dots> = smult d (\<Prod>(x, y)\<leftarrow>qis. x ^ y)" unfolding id qis d by simp
  finally have id: "smult c (\<Prod>(x, y)\<leftarrow>ppis. x ^ y) = smult d (\<Prod>(x, y)\<leftarrow>qis. x ^ y)" by simp
  show ?case unfolding id  
  proof (rule conjI[OF refl], intro allI impI)
    fix qq i
    assume "(qq, i) \<in> set qis"
    hence "qq = q \<and> i = n \<or> (qq,i) \<in> set ris" unfolding qis by auto
    thus "monic qq \<and> (\<exists>p a. (p, i) \<in> set ppis \<and> qq = smult a p \<and> a \<noteq> 0)"      
    proof
      assume "qq = q \<and> i = n"
      hence id: "qq = q" "i = n" by auto
      show ?thesis unfolding id qis ppis pn using cp 
        by (intro conjI[OF m], unfold q, intro exI[of _ p], intro exI[of _ "inverse cp"], auto)
    next
      assume "(qq,i) \<in> set ris"
      with ris[OF this] show ?thesis unfolding ppis by auto
    qed 
  qed
qed
  

definition factorize_rat_poly :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "factorize_rat_poly p = (if p = 0 then (0,[]) else (let 
      main = factorize_rat_poly_start p 
    in if mode = Check_Root_Free then main else normalize_factorization main))"
                                                             
lemma factorize_rat_poly: assumes fp: "factorize_rat_poly p = (c,qis)"
  shows 
  "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" (is "?one") 
  "\<And> q i. (q,i) \<in> set qis \<Longrightarrow> 
    (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
    (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> i \<noteq> 0 \<and> monic q" 
proof -
  obtain d pis where fps: "factorize_rat_poly_start p = (d,pis)" by force
  note fp = fp[unfolded factorize_rat_poly_def fps Let_def]
  note fact = factorize_rat_poly_start[OF fps]
  {
    assume p0: "p \<noteq> 0"
    have "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i) \<and> (\<forall> q i. (q,i) \<in> set qis \<longrightarrow>
      (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
      (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> i \<noteq> 0 \<and> monic q)"
    proof (cases "mode = Check_Root_Free")
      case True
      with fp fact p0 show ?thesis by auto
    next
      case False
      with fp p0 have nf: "normalize_factorization (d, pis) = (c, qis)" by auto
      with fact 
      have p: "p = smult d (\<Prod>(q, i)\<leftarrow>pis. q ^ i)"
        and irr: "\<And> q i. (q, i) \<in> set pis \<Longrightarrow> (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow>  irreducible q) \<and> i \<noteq> 0" 
        and nz: "\<And> q i. (q,i) \<in> set pis \<Longrightarrow> q \<noteq> 0" by auto
      from normalize_factorization[OF nf nz]
      have id: "smult d (\<Prod>(q, i)\<leftarrow>pis. q ^ i) = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)"
        and qis: "\<And> q i. (q, i) \<in> set qis \<Longrightarrow> monic q \<and> (\<exists>p a. (p, i) \<in> set pis \<and> q = smult a p \<and> a \<noteq> 0)"
        by force+
      have p: "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" unfolding p id ..
      {
        fix q i
        assume "(q,i) \<in> set qis"
        from qis[OF this] obtain p a where m: "monic q" and
          mem: "(p, i) \<in> set pis" and q: "q = smult a p" and a: "a \<noteq> 0" by auto
        from irr[OF mem] have irr: "mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible p" and i: "i \<noteq> 0" by auto
        have "mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q" unfolding q using irr a by auto
      }
      with p False qis irr
      show ?thesis by auto
    qed 
  } note main = this
  show "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" using main fp by (cases "p = 0", auto)
  show "\<And> q i. (q,i) \<in> set qis \<Longrightarrow> 
    (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
    (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> i \<noteq> 0 \<and> monic q" using main fp by (cases "p = 0", auto)
qed  
    
lemma factorize_rat_poly_0[simp]: "factorize_rat_poly 0 = (0,[])" 
  unfolding factorize_rat_poly_def by simp

end
end