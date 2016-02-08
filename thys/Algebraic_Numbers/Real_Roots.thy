(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Real Roots\<close>

text \<open>This theory contains an algorithm to determine the set of real roots of a 
  rational polynomial. It further contains an algorithm which tries to determine the
  real roots of real-valued polynomial, which incorporates Yun-factorization and 
  closed formulas for polynomials of degree 2.\<close>

theory Real_Roots
imports 
  Real_Algebraic_Numbers
begin

hide_const (open) order

partial_function (tailrec) roots_of_rai_main :: 
  "rat poly \<Rightarrow> root_info \<Rightarrow> (rat \<Rightarrow> rat \<Rightarrow> nat) \<Rightarrow> (rat \<times> rat)list \<Rightarrow> rai_intern_flat list \<Rightarrow> rai_intern_flat list" where
  [code]: "roots_of_rai_main p ri cr lrs rais = (case lrs of Nil \<Rightarrow> rais
  | (l,r) # lrs \<Rightarrow> let c = cr l r in 
    if c = 0 then roots_of_rai_main p ri cr lrs rais
    else if c = 1 then case tighten_poly_bounds_for_x cr 0 l r of (l,r) 
      \<Rightarrow> roots_of_rai_main p ri cr lrs ((Monic_Root_Free, ri, p, l, r) # rais)
    else let m = (l + r) / 2 in roots_of_rai_main p ri cr ((m,r) # (l,m) # lrs) rais)"

definition root_bounds :: "rat poly \<Rightarrow> rat \<times> rat" where 
  "root_bounds p \<equiv> let 
     n = degree p;
     m = rat_of_nat n * max_list_non_empty (map abs (coeffs p));
     M = of_int (ceiling m) (* one could also choose m, but M is a less complex number *)
   in (-M,M)"

definition roots_of_rai_intern_monic_irr :: "rat poly \<Rightarrow> rai_intern list" where
  "roots_of_rai_intern_monic_irr p = (if degree p = 1
    then [of_rat_rai_fun (- coeff p 0) ] else 
    let ri = count_roots_interval_rat p;
        cr = root_info.l_r ri
      in map (rai_normalize No_Guarantee o Some) (roots_of_rai_main p ri cr [root_bounds p] []))"

lemma root_bounds: assumes "root_bounds p = (l,r)" and mon: "monic p"
  shows "rpoly p x = 0 \<Longrightarrow> real_of_rat l \<le> x \<and> x \<le> of_rat r" "l \<le> r"
proof (rule ccontr)
  let ?r = real_of_rat
  let ?p = "map_poly ?r p"
  def n \<equiv> "degree p"
  def list \<equiv> "map abs (coeffs p)"
  def m' \<equiv> "max_list_non_empty list"
  def m \<equiv> "rat_of_nat n * max_list_non_empty list"
  def M \<equiv> "rat_of_int (ceiling m)"
  have mm': "m = of_nat n * m'" unfolding m'_def m_def of_nat_mult by auto
  from assms(1)[unfolded root_bounds_def Let_def]
  have lr: "l = - M" "r = M" unfolding M_def m_def n_def list_def by auto
  have "coeff p n \<in> insert 0 (set (coeffs p))" using range_coeff[of p] by auto
  with mon[folded n_def] have "1 \<in> set (coeffs p)" by auto
  hence "abs 1 \<in> set list" unfolding list_def set_map by force
  hence "1 \<in> set list" by auto
  from max_list_non_empty[OF this] have m': "m' \<ge> 1" unfolding m'_def by auto
  hence "m \<ge> 0" unfolding m'_def m_def by auto
  hence "M \<ge> 0" unfolding M_def by auto
  thus "l \<le> r" unfolding lr by auto
  assume rt: "rpoly p x = 0"
  {
    assume "n = 0"
    from degree0_coeffs[OF this[unfolded n_def]] obtain a where p: "p = [:a:]" by auto
    with rt have "a = 0" by (auto simp: eval_poly_def)
    with p have "p = 0" by auto
    with mon have False by auto
  }
  hence n: "n > 0" by auto
  from m' have m: "m \<ge> 1" unfolding mm' using n by auto
  have Mm: "M \<ge> m" unfolding M_def by linarith
  assume not: "\<not> (?r l \<le> x \<and> x \<le> ?r r)"
  from not[unfolded lr] have "x > ?r M \<or> x < ?r (- M)" by auto
  with m have "abs x > ?r M" by auto
  moreover have "?r M \<ge> ?r m" unfolding of_rat_less_eq M_def by linarith
  ultimately have gt: "abs x > ?r m" by auto
  also have "?r m \<ge> 1" using m by auto
  ultimately have x1: "abs x > 1" by arith
  have "rpoly p x = (\<Sum>i\<le>n. x ^ i * ?r (coeff p i))" 
    by (subst eval_poly_as_setsum, auto simp: n_def)
  also have "{.. n} = insert n {..< n}" by auto
  also have "(\<Sum>i\<in>insert n {..<n}. x ^ i * ?r (coeff p i)) 
    = x^n * ?r (coeff p n) + (\<Sum>i<n. x ^ i * ?r (coeff p i))"
    by (subst setsum.insert_remove, auto)
  finally have "rpoly p x = x^n + (\<Sum>i<n. x ^ i * ?r (coeff p i))" using mon unfolding n_def by auto
  from arg_cong[OF this, of abs, unfolded rt]
  have "abs x^n = abs (\<Sum>i<n. x ^ i * ?r (coeff p i))" by (auto simp: power_abs[symmetric])
  also have "\<dots> \<le> (\<Sum>i<n. abs x ^ i * abs (?r (coeff p i)))"
    by (rule order.trans[OF setsum_abs], auto simp: abs_mult power_abs)
  also have "\<dots> \<le> (\<Sum>i<n. abs x ^ i * ?r m')"
  proof (rule setsum_mono)
    fix i
    have mem: "coeff p i \<in> insert 0 (set (coeffs p))" using range_coeff[of p] by auto
    hence "?r (abs (coeff p i)) \<le> ?r m'"
    proof (cases "coeff p i = 0")
      case True
      thus ?thesis using m' by auto
    next
      case False
      with mem have "coeff p i \<in> set (coeffs p)" by auto
      hence "abs (coeff p i) \<in> set list" unfolding list_def o_def by auto
      from max_list_non_empty[OF this] have ineq: "?r (abs (coeff p i)) \<le> ?r m'"
        unfolding m'_def of_rat_less_eq by auto
      show ?thesis
        by (rule order_trans[OF _ ineq], unfold of_rat_less_eq, linarith)
    qed
    thus "i \<in> {..<n} \<Longrightarrow> \<bar>x\<bar> ^ i * \<bar>?r (coeff p i)\<bar> \<le> \<bar>x\<bar> ^ i * ?r m'"
      by (intro mult_mono, auto)
  qed
  also have "\<dots> \<le> (\<Sum>i<n. abs x ^ (n - 1) * ?r m')"
    by (rule setsum_mono, rule mult_mono, insert x1 m', auto)
  also have "\<dots> = (abs x ^ (n - 1) * ?r m') * (\<Sum>i<n. 1)"
    by auto
  also have "(\<Sum>i<n. (1 :: real)) = real_of_nat n" by simp
  also have "abs x ^ n = abs x ^ (n - 1) * abs x" using n by (cases n, auto)
  finally have "\<bar>x\<bar> ^ (n-1) * \<bar>x\<bar> \<le> \<bar>x\<bar> ^ (n - 1) * ?r m" unfolding mm' by (simp add: ac_simps)
  also have "\<bar>x\<bar> ^ (n - 1) * ?r m < \<bar>x\<bar> ^ (n - 1) * \<bar>x\<bar>"
    by (rule linordered_semiring_strict_class.mult_le_less_imp_less[OF order_refl gt], 
      insert x1 m, auto)
  finally show False by simp
qed

lemma roots_of_rai_intern_monic_irr: assumes mrf: "poly_type_cond ty p" "ty \<le> Monic_Root_Free"
  shows "rai_real ` set (roots_of_rai_intern_monic_irr p) = {x. rpoly p x = 0}" (is "?one")
    "Ball (set (roots_of_rai_intern_monic_irr p)) rai_cond" (is "?two")
proof -
  let ?rr = "set (roots_of_rai_intern_monic_irr p)"
  note d = roots_of_rai_intern_monic_irr_def
  from poly_type_cond_RF_D[OF mrf] have mon: "monic p" and rf: "root_free p" by auto
  let ?mode = No_Guarantee
  let ?norm = "rai_normalize ?mode"
  have "?one \<and> ?two"
  proof (cases "degree p = 1")
    case True
    def c \<equiv> "coeff p 0"
    from True have rr: "?rr = {of_rat_rai_fun (-c)}" unfolding d c_def by auto
    from degree1_coeffs[OF True] mon have p: "p = [:c,1:]" unfolding c_def by auto
    show ?thesis unfolding rr unfolding p using of_rat_rai_main[of _ "-c", OF refl]
      by (auto simp: eval_poly_def)
  next
    case False
    let ?r = real_of_rat
    let ?rp = "map_poly ?r"
    def ri \<equiv> "count_roots_interval_rat p"
    def cr \<equiv> "root_info.l_r ri"
    def bnds \<equiv> "[root_bounds p]"
    def empty \<equiv> "Nil :: rai_intern_flat list"
    have empty: "Ball (Some ` set empty) rai_cond" unfolding empty_def by auto
    from mon have p: "p \<noteq> 0" by auto
    from count_roots_interval_rat[OF this] have ri: "root_info_cond ri p" unfolding ri_def .    
    from False 
    have rr: "?rr = (?norm o Some) ` set (roots_of_rai_main p ri cr bnds empty)"
      unfolding d ri_def cr_def Let_def bnds_def empty_def by auto
    from root_bounds(2)[OF _ mon]
    have bnds: "\<And> l r. (l,r) \<in> set bnds \<Longrightarrow> l \<le> r" unfolding bnds_def by auto
    have "\<And> x. rpoly p x = 0 \<Longrightarrow> ?r (fst (root_bounds p)) \<le> x \<and> x \<le> ?r (snd (root_bounds p))"
      using root_bounds[of p] mon by (cases "root_bounds p", auto)
    hence rts: "{x. rpoly p x = 0} 
      = rai_real ` (?norm o Some) ` set empty \<union> {x. \<exists> l r. root_cond (p,l,r) x \<and> (l,r) \<in> set bnds}" 
      unfolding empty_def bnds_def by (force simp: root_cond_def)
    def delta \<equiv> "rpoly_root_delta p"
    note delta = rpoly_root_delta[OF p, folded delta_def]
    def rel' \<equiv> "({(x, y). 0 \<le> y \<and> delta_gt delta x y})^-1"
    def mm \<equiv> "\<lambda>bnds. mset (map (\<lambda> (l,r). ?r r - ?r l) bnds)"
    def rel \<equiv> "inv_image (mult1 rel') mm"
    have wf: "wf rel" unfolding rel_def rel'_def
      by (rule wf_inv_image[OF wf_mult1[OF SN_imp_wf[OF delta_gt_SN[OF delta(1)]]]])
    let ?main = "roots_of_rai_main p ri cr"    
    have "(rai_real \<circ> Some) ` set (?main bnds empty) =
      (rai_real \<circ> Some) ` set empty \<union>
      {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set bnds} \<and>
      Ball (Some ` set (?main bnds empty)) rai_cond" (is "?one' \<and> ?two'")
      using empty bnds
    proof (induct bnds arbitrary: empty rule: wf_induct[OF wf])
      case (1 lrss rais)
      note rais = 1(2)[rule_format]
      note lrs = 1(3)
      note IH = 1(1)[rule_format]      
      note simp = roots_of_rai_main.simps[of p ri cr lrss rais]
      show ?case
      proof (cases lrss)
        case Nil
        with rais show ?thesis unfolding simp by auto
      next
        case (Cons lr lrs)
        obtain l r where lr': "lr = (l,r)" by force
        {
          fix lr'
          assume lt: "\<And> l' r'. (l',r') \<in> set lr' \<Longrightarrow> 
            l' \<le> r' \<and> delta_gt delta (?r r - ?r l) (?r r' - ?r l')"
          have l: "mm (lr' @ lrs) = mm lrs + mm lr'" unfolding mm_def by (auto simp: ac_simps)
          have r: "mm lrss = mm lrs + {# ?r r - ?r l #}" unfolding Cons lr' rel_def mm_def
            by auto
          have "(mm (lr' @ lrs), mm lrss) \<in> mult1 rel'" unfolding l r mult1_def
          proof (rule, unfold split, intro exI conjI, rule refl, rule refl, intro allI impI)
            fix d
            assume "d \<in># mm lr'"
            then obtain l' r' where d: "d = ?r r' - ?r l'" and lr': "(l',r') \<in> set lr'"
              unfolding mm_def in_multiset_in_set by auto
            from lt[OF lr']
            show "(d, ?r r - ?r l) \<in> rel'"  unfolding d rel'_def 
              by (auto simp: of_rat_less_eq)
          qed
          hence "(lr' @ lrs, lrss) \<in> rel" unfolding rel_def by auto
        } note rel = this
        from rel[of Nil] have easy_rel: "(lrs,lrss) \<in> rel" by auto
        def c \<equiv> "cr l r"
        from simp Cons lr' have simp: "?main lrss rais = 
          (if c = 0 then ?main lrs rais else if c = 1 then case tighten_poly_bounds_for_x cr 0 l r of 
            (l',r') \<Rightarrow> ?main lrs ((Monic_Root_Free, ri, p, l', r') # rais)
               else let m = (l + r) / 2 in ?main ((m, r) # (l, m) # lrs) rais)"
          unfolding c_def simp Cons lr' by auto
        note lrs = lrs[unfolded Cons lr']        
        from lrs have lr: "l \<le> r" by auto
        from root_info_condD(1)[OF ri lr, folded cr_def] 
        have c: "c = card {x. root_cond (p,l,r) x}" unfolding c_def by auto
        let ?rt = "\<lambda> lrs. {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set lrs}"
        have rts: "?rt lrss = ?rt lrs \<union> {x. root_cond (p,l,r) x}" (is "?rt1 = ?rt2 \<union> ?rt3")
          unfolding Cons lr' by auto
        show ?thesis 
        proof (cases "c = 0")
          case True          
          with simp have simp: "?main lrss rais = ?main lrs rais" by simp
          from finite_rpoly_roots[OF p] True[unfolded c] have empty: "?rt3 = {}"
            unfolding root_cond_def[abs_def] split by simp
          with rts have rts: "?rt1 = ?rt2" by auto
          show ?thesis unfolding simp rts 
            by (rule IH[OF easy_rel rais lrs], auto)
        next
          case False
          have un: "poly_type_cond Monic_Root_Free p"
            by (rule poly_type_cond_mono[OF mrf(2,1)])
          show ?thesis
          proof (cases "c = 1")
            case True
            obtain l' r' where tb: "tighten_poly_bounds_for_x cr 0 l r = (l',r')" by force 
            let ?rai = "(Monic_Root_Free,ri,p,l',r')"            
            from True simp tb have simp: "?main lrss rais = ?main lrs (?rai # rais)" by auto
            from card_1_Collect_ex1[OF c[symmetric, unfolded True]] 
            have rc1: "\<exists>!x. root_cond (p, l, r) x" .
            hence ur: "unique_root (p,l,r)" unfolding unique_root_def .
            have p0: "\<And> x. poly p x \<noteq> 0" using rf `degree p \<noteq> 1` unfolding root_free_def by auto
            from tighten_poly_bounds_for_x[OF ur p0 refl ri _ tb, folded cr_def, OF refl]
            have lr': "l \<le> l'" "r' \<le> r" and lr'': "l' \<le> r'" and rc: "root_cond (p,l',r') (the_unique_root (p,l,r))" 
              and zero: "\<not> (l' \<le> 0 \<and> 0 \<le> r')" by auto
            from zero lr'' have sgn: "sgn r' \<noteq> 0" "sgn l' = sgn r'" unfolding sgn_rat_def
              by (cases "r' = 0", auto)
            from unique_root_sub_interval[OF ur rc lr'] have ur': "unique_root (p,l',r')"
              and id: "the_unique_root (p,l',r') = the_unique_root (p,l,r)" by auto
            have "rai_cond (Some ?rai)" by (auto simp: rai_cond_def p un ur' ri sgn)
            with rais have rais: "\<And> x. x \<in> Some ` set (?rai # rais) \<Longrightarrow> rai_cond x" by auto
            have rt3: "?rt3 = {rai_real (Some ?rai)}" using rc1 unfolding 
              rai_real_def option.simps split id 
              using the_unique_root(5) the_unique_root_def ur by force
            have "(rai_real \<circ> Some) ` set (roots_of_rai_main p ri cr lrs (?rai # rais)) =
              (rai_real \<circ> Some) ` set (?rai # rais) \<union> ?rt2 \<and>
              Ball (Some ` set (roots_of_rai_main p ri cr lrs (?rai # rais))) rai_cond"
              (is "?one \<and> ?two")
              by (rule IH[OF easy_rel, of "?rai # rais", OF rais lrs], auto)
            hence ?one ?two by blast+
            show ?thesis unfolding simp rts rt3 
              by (rule conjI[OF _ `?two`], unfold `?one`, auto)
          next
            case False
            let ?m = "(l+r)/2"
            let ?lrs = "[(?m,r),(l,?m)] @ lrs"
            from False `c \<noteq> 0` have simp: "?main lrss rais = ?main ?lrs rais"
              unfolding simp by (auto simp: Let_def)
            from False `c \<noteq> 0` have "c \<ge> 2" by auto
            from delta(2)[OF this[unfolded c]] have delta: "delta \<le> ?r (r - l) / 4" by auto
            have lrs: "\<And> l r. (l,r) \<in> set ?lrs \<Longrightarrow> l \<le> r"
              using lr lrs by (fastforce simp: field_simps)
            have "(?lrs,lrss) \<in> rel"
            proof (rule rel, intro conjI)
              fix l' r'
              assume mem: "(l', r') \<in> set [(?m,r),(l,?m)]"
              from mem lr show "l' \<le> r'" by auto
              from mem have diff: "?r r' - ?r l' = (?r r - ?r l) / 2" by auto 
               (metis eq_diff_eq minus_diff_eq mult_2_right of_rat_add of_rat_diff,
                metis of_rat_add of_rat_mult of_rat_numeral_eq)
              show "delta_gt delta (?r r - ?r l) (?r r' - ?r l')" unfolding diff
                delta_gt_def by (rule order.trans[OF delta], insert lr, 
                auto simp: field_simps of_rat_diff of_rat_less_eq)
            qed
            note IH = IH[OF this, of rais, OF rais lrs] 
            have "(rai_real \<circ> Some) ` set (?main ?lrs rais) =
              (rai_real \<circ> Some) ` set rais \<union> ?rt ?lrs \<and>
              Ball (Some ` set (?main ?lrs rais)) rai_cond"
              (is "?one \<and> ?two")
              by (rule IH)
            hence ?one ?two by blast+
            have cong: "\<And> a b c. b = c \<Longrightarrow> a \<union> b = a \<union> c" by auto
            have id: "?rt ?lrs = ?rt lrs \<union> ?rt [(?m,r),(l,?m)]" by auto
            show ?thesis unfolding rts simp `?one` id
            proof (rule conjI[OF cong[OF cong]])
              have "\<And> x. root_cond (p,l,r) x = (root_cond (p,l,?m) x \<or> root_cond (p,?m,r) x)"
                unfolding root_cond_def by auto
              hence id: "Collect (root_cond (p,l,r)) = {x. (root_cond (p,l,?m) x \<or> root_cond (p,?m,r) x)}" 
                by auto
              show "?rt [(?m,r),(l,?m)] = Collect (root_cond (p,l,r))" unfolding id list.simps by blast
              show "\<forall> a \<in> Some ` set (?main ?lrs rais). rai_cond a" using `?two` by auto
            qed
          qed
        qed
      qed
    qed
    hence idd: "?one'" and cond: ?two' by blast+
    def res \<equiv> "set (roots_of_rai_main p ri cr bnds empty)"
    have e: "set empty = {}" unfolding empty_def by auto
    from idd[folded res_def] e have idd: "(rai_real \<circ> Some) ` res = {} \<union> {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set bnds}"
      by auto
    {
      fix un ri p l r
      assume *: "\<forall>x\<in>res. rai_cond (Some x)" "(un, ri, p, l, r) \<in> res"
      from *(1)[rule_format, OF *(2)]
      have "rai_cond (Some (un, ri, p, l, r))" .
      from rai_normalize[OF this, of ?mode] *(2) have " rai_real (Some (un, ri, p, l, r)) \<in> rai_real ` (\<lambda>x. ?norm (Some x)) ` res"       
        using image_iff by fastforce
    } note normalize = this
    show ?thesis unfolding rr unfolding rts id e using cond 
      unfolding res_def[symmetric] image_empty e idd[symmetric] o_def using normalize
      by (auto dest: rai_normalize)
  qed
  thus ?one ?two by blast+
qed

definition roots_of_rai_intern :: "rat poly \<Rightarrow> rai_intern list" where
  "roots_of_rai_intern p = concat (map roots_of_rai_intern_monic_irr 
    (concat (map (factors_of_rat_poly Check_Root_Free) (factors_of_rat_poly Uncertified_Factorization p))))"

lemma roots_of_rai_intern: 
  shows "p \<noteq> 0 \<Longrightarrow> rai_real ` set (roots_of_rai_intern p) = {x. rpoly p x = 0}" 
    "Ball (set (roots_of_rai_intern p)) rai_cond"
proof -
  let ?rr = "roots_of_rai_intern p"
  let ?mode1 = Uncertified_Factorization
  let ?mode2 = Check_Root_Free
  note d = roots_of_rai_intern_def
  note frp1 = factors_of_rat_poly[of ?mode1]
  note frp2 = factors_of_rat_poly[of ?mode2]
  {
    fix q r
    assume "q \<in> set ?rr"
    then obtain r s where 
      s: "s \<in> set (factors_of_rat_poly ?mode1 p)" and
      r: "r \<in> set (factors_of_rat_poly ?mode2 s)" and       
      q: "q \<in> set (roots_of_rai_intern_monic_irr r)"
      unfolding d by auto
    from frp2(1)[OF refl r] have "poly_type_cond Monic_Root_Free r" 
      by (auto simp: poly_type_cond_def)
    from roots_of_rai_intern_monic_irr[OF this] q
    have "rai_cond q" by auto
  }
  thus "Ball (set ?rr) rai_cond" by auto
  assume p: "p \<noteq> 0" 
  have "rai_real ` set ?rr = (\<Union> ((\<lambda> p. rai_real ` set (roots_of_rai_intern_monic_irr p)) ` 
    (\<Union> ((\<lambda> p. set (factors_of_rat_poly ?mode2 p)) ` set (factors_of_rat_poly ?mode1 p)))))"
    (is "_ = ?rrr")
    unfolding d set_concat set_map by auto
  also have "\<dots> = {x. rpoly p x = 0}"
  proof -
    {
      fix x
      assume "x \<in> ?rrr"
      then obtain q r s where 
        s: "s \<in> set (factors_of_rat_poly ?mode1 p)" and
        r: "r \<in> set (factors_of_rat_poly ?mode2 s)" and       
        q: "q \<in> set (roots_of_rai_intern_monic_irr r)" and
        x: "x = rai_real q" by auto
      from frp1(1)[OF refl s] have s0: "s \<noteq> 0" by auto
      from frp2(1)[OF refl r] have mrf: "poly_type_cond Monic_Root_Free r" "Monic_Root_Free \<le> Monic_Root_Free" 
        by (auto simp: poly_type_cond_def)
      from roots_of_rai_intern_monic_irr[OF mrf] q have rt: "rpoly r x = 0" unfolding x by auto
      from frp2(2)[OF refl s0, of x] rt r have rt: "rpoly s x = 0" by auto
      from frp1(2)[OF refl p, of x] rt s have rt: "rpoly p x = 0" by auto
    }
    moreover
    {
      fix x :: real
      assume rt: "rpoly p x = 0"
      from rt frp1(2)[OF refl p, of x] obtain s where s: "s \<in> set (factors_of_rat_poly ?mode1 p)" 
        and rt: "rpoly s x = 0" by auto
      from frp1(1)[OF refl s] have s0: "s \<noteq> 0" by auto
      from rt frp2(2)[OF refl s0, of x] obtain r where r: "r \<in> set (factors_of_rat_poly ?mode2 s)" 
        and rt: "rpoly r x = 0" by auto
      from frp2(1)[OF refl r] have mrf: "poly_type_cond Monic_Root_Free r" "Monic_Root_Free \<le> Monic_Root_Free" 
        by (auto simp: poly_type_cond_def)    
      from roots_of_rai_intern_monic_irr(1)[OF mrf] rt obtain q where 
        q: "q \<in> set (roots_of_rai_intern_monic_irr r)" and
        x: "x = rai_real q" by auto
      have "x \<in> ?rrr" unfolding x using q r s by auto
    }
    ultimately show ?thesis by auto
  qed
  finally show "rai_real ` set ?rr = {x. rpoly p x = 0}" by auto
qed

lift_definition roots_of_rai :: "rat poly \<Rightarrow> real_alg_intern list" is roots_of_rai_intern
  by (insert roots_of_rai_intern, auto simp: list_all_iff)

lemma roots_of_rai: "p \<noteq> 0 \<Longrightarrow> real_of_rai ` set (roots_of_rai p) = {x. rpoly p x = 0}"
  by (transfer, insert roots_of_rai_intern, auto)
  
definition roots_of_radtc :: "rat poly \<Rightarrow> real_alg_dtc list" where
  "roots_of_radtc p = map radtc_of_rai (roots_of_rai p)"

lemma roots_of_radtc: 
  "p \<noteq> 0 \<Longrightarrow> real_of_radtc ` set (roots_of_radtc p) = {x. rpoly p x = 0}" 
  unfolding roots_of_radtc_def set_map[symmetric]
  by (auto simp: o_def roots_of_rai)

lift_definition roots_of_real_alg :: "rat poly \<Rightarrow> real_alg list" is roots_of_radtc . 

lemma roots_of_real_alg: 
  "p \<noteq> 0 \<Longrightarrow> real_of ` set (roots_of_real_alg p) = {x. rpoly p x = 0}" 
  by (transfer', insert roots_of_radtc, auto)

text \<open>It follows an implementation for @{const roots_of_rai}, which is not directly available as code equation.\<close>
context
begin
private typedef rai_list = "{xs. Ball (set xs) rai_cond}" by (intro exI[of _ Nil], auto)

setup_lifting type_definition_rai_list

private lift_definition roots_of_rai_list :: "rat poly \<Rightarrow> rai_list" is roots_of_rai_intern
  by (insert roots_of_rai_intern, auto)
private lift_definition rai_list_nil :: "rai_list \<Rightarrow> bool" is "\<lambda> xs. case xs of Nil \<Rightarrow> True | _ \<Rightarrow> False" .

private fun rai_list_hd_intern :: "rai_intern list \<Rightarrow> rai_intern" where
  "rai_list_hd_intern (Cons x xs) = x"
| "rai_list_hd_intern Nil = None"

private lift_definition rai_list_hd :: "rai_list \<Rightarrow> real_alg_intern" is rai_list_hd_intern
proof (goal_cases)
  case (1 xs)
  thus ?case by (cases xs, auto)
qed

private lift_definition rai_list_tl :: "rai_list \<Rightarrow> rai_list" is tl 
proof (goal_cases)
  case (1 xs)
  thus ?case by (cases xs, auto)
qed

private lift_definition rai_list_length :: "rai_list \<Rightarrow> nat" is length .

private lemma rai_list_length[simp]: "\<not> rai_list_nil xs \<Longrightarrow> rai_list_length (rai_list_tl xs) < rai_list_length xs"
  by (transfer, auto split: list.splits)

private function rai_list_convert :: "rai_list \<Rightarrow> real_alg_intern list" where
  "rai_list_convert xs = (if rai_list_nil xs then [] else rai_list_hd xs 
    # rai_list_convert (rai_list_tl xs))" by pat_completeness auto

termination by (relation "measure rai_list_length", auto)

private definition roots_of_rai_impl :: "rat poly \<Rightarrow> real_alg_intern list" where
  "roots_of_rai_impl p = rai_list_convert (roots_of_rai_list p)"

private lift_definition rai_list_convert_id :: "rai_list \<Rightarrow> real_alg_intern list" is id
  by (auto simp: list_all_iff)

lemma rai_list_convert: "rai_list_convert xs = rai_list_convert_id xs"
proof (induct xs rule: wf_induct[OF wf_measure[of rai_list_length], rule_format])
  case (1 xs)
  show ?case
  proof (cases "rai_list_nil xs")
    case True
    hence "rai_list_convert xs = []" by auto
    also have "[] = rai_list_convert_id xs" using True
      by (transfer', auto split: list.splits)
    finally show ?thesis .
  next
    case False
    hence "rai_list_convert xs = rai_list_hd xs # rai_list_convert (rai_list_tl xs)" by simp
    also have "rai_list_convert (rai_list_tl xs) = rai_list_convert_id (rai_list_tl xs)"
      by (rule 1, insert False, simp)
    also have "rai_list_hd xs # \<dots> = rai_list_convert_id xs" using False
      by (transfer', auto split: list.splits)
    finally show ?thesis .
  qed
qed

private lemma [code]: "roots_of_rai p = roots_of_rai_impl p" 
  unfolding roots_of_rai_impl_def rai_list_convert
  by (transfer, simp)
end

text \<open>Determine real roots of a rational polynomial, 
   intended for polynomials of degree 3 or higher,
   for lower degree polynomials use @{const roots1} or @{const rroots2}.
   Internally, Yun-factorization and factorization of rational polynomials will be applied.\<close>
definition real_roots_of_rat_poly3 :: "rat poly \<Rightarrow> real list" where
  "real_roots_of_rat_poly3 p = map real_of (roots_of_real_alg p)"

definition real_roots_of_rat_poly_all :: "rat poly \<Rightarrow> real list" where
  "real_roots_of_rat_poly_all p = (let n = degree p in 
    if n \<ge> 3 then real_roots_of_rat_poly3 p
    else if n = 1 then [roots1 (map_poly of_rat p)] else if n = 2 then rroots2 (map_poly of_rat p)
    else [])"


lemma real_roots_of_rat_poly3: 
  "p \<noteq> 0 \<Longrightarrow> set (real_roots_of_rat_poly3 p) = {x. rpoly p x = 0}" 
  unfolding real_roots_of_rat_poly3_def using roots_of_real_alg by auto

lemma real_roots_of_rat_poly_all: assumes p: "p \<noteq> 0"
  shows "set (real_roots_of_rat_poly_all p) = {x. rpoly p x = 0}" (is "?l = ?r")
proof -
  note d = real_roots_of_rat_poly_all_def Let_def
  show ?thesis
  proof (cases "degree p \<ge> 3")
    case True
    with real_roots_of_rat_poly3[OF p] show ?thesis unfolding d by auto
  next
    case False
    let ?p = "map_poly real_of_rat p"
    have r: "?r = {x. poly ?p x = 0}" unfolding poly_real_of_rat_poly ..
    have deg: "degree ?p = degree p" 
      by (simp add: degree_map_poly)
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence l: "?l = {roots1 ?p}" unfolding d by auto
      from True have "degree ?p = 1" unfolding deg by auto
      from roots1[OF this] show ?thesis unfolding r l by simp
    next
      case False
      show ?thesis 
      proof (cases "degree p = 2")
        case True
        hence l: "?l = set (rroots2 ?p)" unfolding d by auto
        from True have "degree ?p = 2" unfolding deg by auto
        from rroots2[OF this] show ?thesis unfolding r l by simp
      next
        case False
        with `degree p \<noteq> 1` `degree p \<noteq> 2` `\<not> (degree p \<ge> 3)` have True: "degree p = 0" by auto
        hence l: "?l = {}" unfolding d by auto
        from True have "degree ?p = 0" unfolding deg by auto
        from roots0[OF _ this] p show ?thesis unfolding r l by simp
      qed
    qed
  qed
qed

text \<open>It now comes the preferred function to compute real roots of a rational polynomial.\<close>
definition real_roots_of_rat_poly :: "rat poly \<Rightarrow> real list" where
  "real_roots_of_rat_poly p = (
    let ps = (if degree p \<ge> 3 then factors_of_rat_poly Uncertified_Factorization p else [p])
    in concat (map real_roots_of_rat_poly_all ps))"

lemma real_roots_of_rat_poly: assumes p: "p \<noteq> 0"
  shows "set (real_roots_of_rat_poly p) = {x. rpoly p x = 0}" (is "?l = ?r")
proof (cases "degree p \<ge> 3")
  case False
  hence "real_roots_of_rat_poly p = real_roots_of_rat_poly_all p"
    unfolding real_roots_of_rat_poly_def Let_def by auto
  with real_roots_of_rat_poly_all[OF p] show ?thesis by auto
next
  case True
  let ?mode = Uncertified_Factorization
  note factors_of_rat_poly = factors_of_rat_poly[of ?mode]
  {
    fix q
    assume "q \<in> set (factors_of_rat_poly ?mode p)"
    from factors_of_rat_poly(1)[OF refl this] have "q \<noteq> 0" by auto
    from real_roots_of_rat_poly_all[OF this]
    have "set (real_roots_of_rat_poly_all q) = {x. rpoly q x = 0}" by auto
  } note all = this
  from True have 
    "?l = (\<Union> ((\<lambda> p. set (real_roots_of_rat_poly_all p)) ` set (factors_of_rat_poly ?mode p)))"
    unfolding real_roots_of_rat_poly_def Let_def by auto    
  also have "\<dots> = (\<Union> ((\<lambda> p. {x. rpoly p x = 0}) ` set (factors_of_rat_poly ?mode p)))"
    using all by blast
  finally have l: "?l = (\<Union> ((\<lambda> p. {x. rpoly p x = 0}) ` set (factors_of_rat_poly ?mode p)))" .
  show ?thesis unfolding l factors_of_rat_poly(2)[OF refl p] by auto
qed

text \<open>The upcoming functions no longer demand a rational polynomial as input.\<close>

definition roots_of_real_main :: "real poly \<Rightarrow> real list" where 
  "roots_of_real_main p \<equiv> let n = degree p in 
    if n = 0 then [] else if n = 1 then [roots1 p] else if n = 2 then rroots2 p
    else (real_roots_of_rat_poly (map_poly to_rat p))"
  
definition roots_of_real_poly :: "real poly \<Rightarrow> real list option" where
  "roots_of_real_poly p \<equiv> let (c,pis) = yun_factorization gcd p in
    if (c \<noteq> 0 \<and> (\<forall> (p,i) \<in> set pis. degree p \<le> 2 \<or> (\<forall> x \<in> set (coeffs p). x \<in> \<rat>))) then 
    Some (concat (map (roots_of_real_main o fst) pis)) else None"

lemma roots_of_real_main: assumes p: "p \<noteq> 0" and deg: "degree p \<le> 2 \<or> set (coeffs p) \<subseteq> \<rat>"
  shows "set (roots_of_real_main p) = {x. poly p x = 0}" (is "?l = ?r")
proof -
  note d = roots_of_real_main_def Let_def
  show ?thesis 
  proof (cases "degree p = 0")
    case True
    hence "?l = {}" unfolding d by auto
    with roots0[OF p True] show ?thesis by auto
  next
    case False note 0 = this
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence "?l = {roots1 p}" unfolding d by auto
      with roots1[OF True] show ?thesis by auto
    next
      case False note 1 = this
      show ?thesis
      proof (cases "degree p = 2")
        case True
        hence "?l = set (rroots2 p)" unfolding d by auto
        with rroots2[OF True] show ?thesis by auto
      next
        case False note 2 = this
        let ?q = "map_poly to_rat p"
        from 0 1 2 have l: "?l = set (real_roots_of_rat_poly ?q)" unfolding d by auto
        from deg 0 1 2 have rat: "set (coeffs p) \<subseteq> \<rat>" by auto
        have "p = map_poly (of_rat o to_rat) p"
          by (rule sym, rule map_poly_eqI, insert rat, auto)
        also have "\<dots> = real_of_rat_poly ?q"
          by (subst map_poly_compose, auto simp: to_rat)
        finally have id: "{x. poly p x = 0} = {x. poly (real_of_rat_poly ?q) x = 0}" and q: "?q \<noteq> 0" 
          using p by auto
        from real_roots_of_rat_poly[OF q, folded id[unfolded poly_real_of_rat_poly] l] show ?thesis .
      qed
    qed
  qed
qed
  
lemma roots_of_real_poly: assumes rt: "roots_of_real_poly p = Some xs"
  shows "set xs = {x. poly p x = 0}"
proof -
  obtain c pis where yun: "yun_factorization gcd p = (c,pis)" by force
  from rt[unfolded roots_of_real_poly_def yun split Let_def]
  have c: "c \<noteq> 0" and pis: "\<And> p i. (p, i)\<in>set pis \<Longrightarrow> degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
    and xs: "xs = concat (map (roots_of_real_main \<circ> fst) pis)"
    by (auto split: if_splits)
  note yun = square_free_factorizationD(1,2,4)[OF yun_factorization(1)[OF yun]]
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  have "{x. poly p x = 0} = {x. poly (\<Prod>(a, i)\<in>set pis. a ^ Suc i) x = 0}"
    unfolding p using c by auto
  also have "\<dots> = \<Union> ((\<lambda> p. {x. poly p x = 0}) ` fst ` set pis)" (is "_ = ?r")
    by (subst poly_setprod_0, force+)
  finally have r: "{x. poly p x = 0} = ?r" .
  {
    fix p i
    assume p: "(p,i) \<in> set pis"
    have "set (roots_of_real_main p) = {x. poly p x = 0}"
      by (rule roots_of_real_main, insert yun(2)[OF p] pis[OF p], auto)
  } note main = this
  have "set xs = \<Union> ((\<lambda> (p, i). set (roots_of_real_main p)) ` set pis)" unfolding xs o_def
    by auto
  also have "\<dots> = ?r" using main by auto
  finally show ?thesis unfolding r by simp
qed

end