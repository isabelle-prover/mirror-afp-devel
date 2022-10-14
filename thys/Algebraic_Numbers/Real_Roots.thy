(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Real Roots\<close>

text \<open>This theory contains an algorithm to determine the set of real roots of a 
  rational polynomial. For polynomials with real coefficients, we refer to
  the AFP entry "Factor-Algebraic-Polynomial".\<close>

theory Real_Roots
  imports 
    Cauchy_Root_Bound
    Real_Algebraic_Numbers
begin

hide_const (open) UnivPoly.coeff
hide_const (open) Module.smult
  
partial_function (tailrec) roots_of_2_main :: 
  "int poly \<Rightarrow> root_info \<Rightarrow> (rat \<Rightarrow> rat \<Rightarrow> nat) \<Rightarrow> (rat \<times> rat)list \<Rightarrow> real_alg_2 list \<Rightarrow> real_alg_2 list" where
  [code]: "roots_of_2_main p ri cr lrs rais = (case lrs of Nil \<Rightarrow> rais
  | (l,r) # lrs \<Rightarrow> let c = cr l r in 
    if c = 0 then roots_of_2_main p ri cr lrs rais
    else if c = 1 then roots_of_2_main p ri cr lrs (real_alg_2'' ri p l r # rais)
    else let m = (l + r) / 2 in roots_of_2_main p ri cr ((m,r) # (l,m) # lrs) rais)"
  
definition roots_of_2_irr :: "int poly \<Rightarrow> real_alg_2 list" where
  "roots_of_2_irr p = (if degree p = 1
    then [Rational (Rat.Fract (- coeff p 0) (coeff p 1)) ] else 
    let ri = root_info p;
        cr = root_info.l_r ri;
        B = root_bound p
      in (roots_of_2_main p ri cr [(-B,B)] []))"
    
fun pairwise_disjoint :: "'a set list \<Rightarrow> bool" where
  "pairwise_disjoint [] = True" 
| "pairwise_disjoint (x # xs) = ((x \<inter> (\<Union> y \<in> set xs. y) = {}) \<and> pairwise_disjoint xs)" 

lemma roots_of_2_irr: assumes pc: "poly_cond p" and deg: "degree p > 0"
  shows "real_of_2 ` set (roots_of_2_irr p) = {x. ipoly p x = 0}" (is ?one)
    "Ball (set (roots_of_2_irr p)) invariant_2" (is ?two)
    "distinct (map real_of_2 (roots_of_2_irr p))" (is ?three)
proof -
  note d = roots_of_2_irr_def
  from poly_condD[OF pc] have mon: "lead_coeff p > 0" and irr: "irreducible p" by auto
  let ?norm = "real_alg_2'"
  have "?one \<and> ?two \<and> ?three"
  proof (cases "degree p = 1")
    case True
    define c where "c = coeff p 0"
    define d where "d = coeff p 1" 
    from True have rr: "roots_of_2_irr p = [Rational (Rat.Fract (- c) (d))]" unfolding d d_def c_def by auto
    from degree1_coeffs[OF True] have p: "p = [:c,d:]" and d: "d \<noteq> 0" unfolding c_def d_def by auto
    have *: "real_of_int c + x * real_of_int d = 0 \<Longrightarrow> x = - (real_of_int c / real_of_int d)" for x
      using d by (simp add: field_simps)
    show ?thesis unfolding rr using d * unfolding p using of_rat_1[of "Rat.Fract (- c) (d)"]
      by (auto simp: Fract_of_int_quotient hom_distribs)
  next
    case False
    let ?r = real_of_rat
    let ?rp = "map_poly ?r"
    let ?rr = "set (roots_of_2_irr p)"
    define ri where "ri = root_info p"
    define cr where "cr = root_info.l_r ri"
    define bnds where "bnds = [(-root_bound p, root_bound p)]"
    define empty where "empty = (Nil :: real_alg_2 list)"
    have empty: "Ball (set empty) invariant_2 \<and> distinct (map real_of_2 empty)" unfolding empty_def by auto
    from mon have p: "p \<noteq> 0" by auto
    from root_info[OF irr deg] have ri: "root_info_cond ri p" unfolding ri_def .    
    from False 
    have rr: "roots_of_2_irr p = roots_of_2_main p ri cr bnds empty"
      unfolding d ri_def cr_def Let_def bnds_def empty_def by auto
    note root_bound = root_bound[OF refl deg]
    from root_bound(2)
    have bnds: "\<And> l r. (l,r) \<in> set bnds \<Longrightarrow> l \<le> r" unfolding bnds_def by auto
    have "ipoly p x = 0 \<Longrightarrow> ?r (- root_bound p) \<le> x \<and> x \<le> ?r (root_bound p)" for x
      using root_bound(1)[of x] by (auto simp: hom_distribs)
    hence rts: "{x. ipoly p x = 0} 
      = real_of_2 ` set empty \<union> {x. \<exists> l r. root_cond (p,l,r) x \<and> (l,r) \<in> set bnds}" 
      unfolding empty_def bnds_def by (force simp: root_cond_def)
    define rts where "rts lr = Collect (root_cond (p,lr))" for lr 
    have disj: "pairwise_disjoint (real_of_2 ` set empty # map rts bnds)" 
      unfolding empty_def bnds_def by auto
    from deg False have deg1: "degree p > 1" by auto
    define delta where "delta = ipoly_root_delta p"
    note delta = ipoly_root_delta[OF p, folded delta_def]
    define rel' where "rel' = ({(x, y). 0 \<le> y \<and> delta_gt delta x y})^-1"
    define mm where "mm = (\<lambda>bnds. mset (map (\<lambda> (l,r). ?r r - ?r l) bnds))"
    define rel where "rel = inv_image (mult1 rel') mm"
    have wf: "wf rel" unfolding rel_def rel'_def
      by (rule wf_inv_image[OF wf_mult1[OF SN_imp_wf[OF delta_gt_SN[OF delta(1)]]]])
    let ?main = "roots_of_2_main p ri cr"    
    have "real_of_2 ` set (?main bnds empty) =
      real_of_2 ` set empty \<union>
      {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set bnds} \<and>
      Ball (set (?main bnds empty)) invariant_2 \<and> distinct (map real_of_2 (?main bnds empty))" (is "?one' \<and> ?two' \<and> ?three'")
      using empty bnds disj
    proof (induct bnds arbitrary: empty rule: wf_induct[OF wf])
      case (1 lrss rais)
      note rais = 1(2)[rule_format]
      note lrs = 1(3)
      note disj = 1(4)
      note IH = 1(1)[rule_format]
      note simp = roots_of_2_main.simps[of p ri cr lrss rais]
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
          proof (rule, unfold split, intro exI conjI, unfold add_mset_add_single[symmetric], rule refl, rule refl, intro allI impI)
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
        define c where "c = cr l r"
        from simp Cons lr' have simp: "?main lrss rais = 
          (if c = 0 then ?main lrs rais else if c = 1 then 
             ?main lrs (real_alg_2' ri p l r # rais)
               else let m = (l + r) / 2 in ?main ((m, r) # (l, m) # lrs) rais)"
          unfolding c_def simp Cons lr' using real_alg_2''[OF False] by auto
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
          from disj have disj: "pairwise_disjoint (real_of_2 ` set rais # map rts lrs)" 
            unfolding Cons by auto
          from finite_ipoly_roots[OF p] True[unfolded c] have empty: "?rt3 = {}"
            unfolding root_cond_def[abs_def] split by simp
          with rts have rts: "?rt1 = ?rt2" by auto
          show ?thesis unfolding simp rts 
            by (rule IH[OF easy_rel rais lrs disj], auto)
        next
          case False
          show ?thesis
          proof (cases "c = 1")
            case True
            let ?rai = "real_alg_2' ri p l r"
            from True simp have simp: "?main lrss rais = ?main lrs (?rai # rais)" by auto
            from card_1_Collect_ex1[OF c[symmetric, unfolded True]] 
            have ur: "unique_root (p,l,r)"  .            
            from real_alg_2'[OF ur pc ri]
            have rai: "invariant_2 ?rai" "real_of_2 ?rai = the_unique_root (p, l, r)" by auto
            with rais have rais: "\<And> x. x \<in> set (?rai # rais) \<Longrightarrow> invariant_2 x" 
              and dist: "distinct (map real_of_2 rais)" by auto
            have rt3: "?rt3 = {real_of_2 ?rai}" 
              using ur rai by (auto intro: the_unique_root_eqI theI')            
            have "real_of_2 ` set (roots_of_2_main p ri cr lrs (?rai # rais)) =
              real_of_2 ` set (?rai # rais) \<union> ?rt2 \<and>
              Ball (set (roots_of_2_main p ri cr lrs (?rai # rais))) invariant_2 \<and>
              distinct (map real_of_2 (roots_of_2_main p ri cr lrs (?rai # rais)))"
              (is "?one \<and> ?two \<and> ?three")
            proof (rule IH[OF easy_rel, of "?rai # rais", OF conjI lrs])
              show "Ball (set (real_alg_2' ri p l r # rais)) invariant_2" using rais by auto
              have "real_of_2 (real_alg_2' ri p l r) \<notin> set (map real_of_2 rais)"
                using disj rt3 unfolding Cons lr' rts_def by auto
              thus "distinct (map real_of_2 (real_alg_2' ri p l r # rais))" using dist by auto
              show "pairwise_disjoint (real_of_2 ` set (real_alg_2' ri p l r # rais) # map rts lrs)"
                using disj rt3 unfolding Cons lr' rts_def by auto
            qed auto
            hence ?one ?two ?three by blast+
            show ?thesis unfolding simp rts rt3 
              by (rule conjI[OF _ conjI[OF \<open>?two\<close> \<open>?three\<close>]], unfold \<open>?one\<close>, auto)
          next
            case False
            let ?m = "(l+r)/2"
            let ?lrs = "[(?m,r),(l,?m)] @ lrs"
            from False \<open>c \<noteq> 0\<close> have simp: "?main lrss rais = ?main ?lrs rais"
              unfolding simp by (auto simp: Let_def)
            from False \<open>c \<noteq> 0\<close> have "c \<ge> 2" by auto
            from delta(2)[OF this[unfolded c]] have delta: "delta \<le> ?r (r - l) / 4" by auto
            have lrs: "\<And> l r. (l,r) \<in> set ?lrs \<Longrightarrow> l \<le> r"
              using lr lrs by (fastforce simp: field_simps)
            have "?r ?m \<in> \<rat>" unfolding Rats_def by blast
            with poly_cond_degree_gt_1[OF pc deg1, of "?r ?m"]
            have disj1: "?r ?m \<notin> rts lr" for lr unfolding rts_def root_cond_def by auto
            have disj2: "rts (?m, r) \<inter> rts (l, ?m) = {}" using disj1[of "(l,?m)"] disj1[of "(?m,r)"] 
              unfolding rts_def root_cond_def by auto
            have disj3: "(rts (l,?m) \<union> rts (?m,r)) = rts (l,r)"
              unfolding rts_def root_cond_def by (auto simp: hom_distribs)
            have disj4: "real_of_2 ` set rais \<inter> rts (l,r) = {}" using disj unfolding Cons lr' by auto
            have disj: "pairwise_disjoint (real_of_2 ` set rais # map rts ([(?m, r), (l, ?m)] @ lrs))" 
              using disj disj2 disj3 disj4 by (auto simp: Cons lr')
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
            note IH = IH[OF this, of rais, OF rais lrs disj]
            have "real_of_2 ` set (?main ?lrs rais) =
              real_of_2 ` set rais \<union> ?rt ?lrs \<and>
              Ball (set (?main ?lrs rais)) invariant_2 \<and> distinct (map real_of_2 (?main ?lrs rais))"
              (is "?one \<and> ?two")
              by (rule IH)
            hence ?one ?two by blast+
            have cong: "\<And> a b c. b = c \<Longrightarrow> a \<union> b = a \<union> c" by auto
            have id: "?rt ?lrs = ?rt lrs \<union> ?rt [(?m,r),(l,?m)]" by auto
            show ?thesis unfolding rts simp \<open>?one\<close> id
            proof (rule conjI[OF cong[OF cong] conjI])
              have "\<And> x. root_cond (p,l,r) x = (root_cond (p,l,?m) x \<or> root_cond (p,?m,r) x)"
                unfolding root_cond_def by (auto simp:hom_distribs)
              hence id: "Collect (root_cond (p,l,r)) = {x. (root_cond (p,l,?m) x \<or> root_cond (p,?m,r) x)}" 
                by auto
              show "?rt [(?m,r),(l,?m)] = Collect (root_cond (p,l,r))" unfolding id list.simps by blast
              show "\<forall> a \<in> set (?main ?lrs rais). invariant_2 a" using \<open>?two\<close> by auto
              show "distinct (map real_of_2 (?main ?lrs rais))" using \<open>?two\<close> by auto
            qed
          qed
        qed
      qed
    qed
    hence idd: "?one'" and cond: ?two' ?three' by blast+
    define res where "res = roots_of_2_main p ri cr bnds empty"
    have e: "set empty = {}" unfolding empty_def by auto
    from idd[folded res_def] e have idd: "real_of_2 ` set res = {} \<union> {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set bnds}"
      by auto
    show ?thesis
      unfolding rr unfolding rts id e norm_def using cond 
      unfolding res_def[symmetric] image_empty e idd[symmetric] by auto
  qed
  thus ?one ?two ?three by blast+
qed
 
definition roots_of_2 :: "int poly \<Rightarrow> real_alg_2 list" where
  "roots_of_2 p = concat (map roots_of_2_irr 
     (factors_of_int_poly p))"
    
lemma roots_of_2:
  shows "p \<noteq> 0 \<Longrightarrow> real_of_2 ` set (roots_of_2 p) = {x. ipoly p x = 0}"
    "Ball (set (roots_of_2 p)) invariant_2"
    "distinct (map real_of_2 (roots_of_2 p))" 
proof -
  let ?rr = "roots_of_2 p"
  note d = roots_of_2_def
  note frp1 = factors_of_int_poly
  {
    fix q r
    assume "q \<in> set ?rr"
    then obtain s where 
      s: "s \<in> set (factors_of_int_poly p)" and
      q: "q \<in> set (roots_of_2_irr s)"
      unfolding d by auto
    from frp1(1)[OF refl s] have "poly_cond s" "degree s > 0" by (auto simp: poly_cond_def)
    from roots_of_2_irr[OF this] q
    have "invariant_2 q" by auto
  }
  thus "Ball (set ?rr) invariant_2" by auto
  {  
    assume p: "p \<noteq> 0" 
    have "real_of_2 ` set ?rr = (\<Union> ((\<lambda> p. real_of_2 ` set (roots_of_2_irr p)) ` 
      (set (factors_of_int_poly p))))"
      (is "_ = ?rrr")
      unfolding d set_concat set_map by auto
    also have "\<dots> = {x. ipoly p x = 0}"
    proof -
      {
        fix x
        assume "x \<in> ?rrr"
        then obtain q s where 
          s: "s \<in> set (factors_of_int_poly p)" and
          q: "q \<in> set (roots_of_2_irr s)" and
          x: "x = real_of_2 q" by auto
        from frp1(1)[OF refl s] have s0: "s \<noteq> 0" and pt: "poly_cond s" "degree s > 0"
          by (auto simp: poly_cond_def)
        from roots_of_2_irr[OF pt] q have rt: "ipoly s x = 0" unfolding x by auto
        from frp1(2)[OF refl p, of x] rt s have rt: "ipoly p x = 0" by auto
      }
      moreover
      {
        fix x :: real
        assume rt: "ipoly p x = 0"
        from rt frp1(2)[OF refl p, of x] obtain s where s: "s \<in> set (factors_of_int_poly p)" 
          and rt: "ipoly s x = 0" by auto
        from frp1(1)[OF refl s] have s0: "s \<noteq> 0" and ty: "poly_cond s" "degree s > 0"
          by (auto simp: poly_cond_def)
        from roots_of_2_irr(1)[OF ty] rt obtain q where 
          q: "q \<in> set (roots_of_2_irr s)" and
          x: "x = real_of_2 q" by blast
        have "x \<in> ?rrr" unfolding x using q s by auto
      }
      ultimately show ?thesis by auto
    qed
    finally show "real_of_2 ` set ?rr = {x. ipoly p x = 0}" by auto
  }
  show "distinct (map real_of_2 (roots_of_2 p))"
  proof (cases "p = 0")
    case True
    from factors_of_int_poly_const[of 0] True show ?thesis unfolding roots_of_2_def by auto
  next
    case p: False
    note frp1 = frp1[OF refl]
    let ?fp = "factors_of_int_poly p" 
    let ?cc = "concat (map roots_of_2_irr ?fp)" 
    show ?thesis unfolding roots_of_2_def distinct_conv_nth length_map
    proof (intro allI impI notI)
      fix i j
      assume ij: "i < length ?cc" "j < length ?cc" "i \<noteq> j" and id: "map real_of_2 ?cc ! i = map real_of_2 ?cc ! j"       
      from ij id have id: "real_of_2 (?cc ! i) = real_of_2 (?cc ! j)" by auto
      from nth_concat_diff[OF ij, unfolded length_map] obtain j1 k1 j2 k2 where 
        *: "(j1,k1) \<noteq> (j2,k2)"
        "j1 < length ?fp" "j2 < length ?fp" and
        "k1 < length (map roots_of_2_irr ?fp ! j1)"
        "k2 < length (map roots_of_2_irr ?fp ! j2)"
        "?cc ! i = map roots_of_2_irr ?fp ! j1 ! k1" 
        "?cc ! j = map roots_of_2_irr ?fp ! j2 ! k2" by blast
      hence **: "k1 < length (roots_of_2_irr (?fp ! j1))" 
        "k2 < length (roots_of_2_irr (?fp ! j2))" 
        "?cc ! i = roots_of_2_irr (?fp ! j1) ! k1"
        "?cc ! j = roots_of_2_irr (?fp ! j2) ! k2"
        by auto
      from * have mem: "?fp ! j1 \<in> set ?fp" "?fp ! j2 \<in> set ?fp" by auto
      from frp1(1)[OF mem(1)] frp1(1)[OF mem(2)]
      have pc1: "poly_cond (?fp ! j1)" "degree (?fp ! j1) > 0" and pc10: "?fp ! j1 \<noteq> 0" 
        and pc2: "poly_cond (?fp ! j2)" "degree (?fp ! j2) > 0" 
        by (auto simp: poly_cond_def)
      show False
      proof (cases "j1 = j2")
        case True
        with * have neq: "k1 \<noteq> k2" by auto
        from **[unfolded True] id *
        have "map real_of_2 (roots_of_2_irr (?fp ! j2)) ! k1 = real_of_2 (?cc ! j)" 
          "map real_of_2 (roots_of_2_irr (?fp ! j2)) ! k1 = real_of_2 (?cc ! j)"
          by auto
        hence "\<not> distinct (map real_of_2 (roots_of_2_irr (?fp ! j2)))" 
          unfolding distinct_conv_nth using * ** True by auto
        with roots_of_2_irr(3)[OF pc2] show False by auto
      next
        case neq: False
        with frp1(4)[of p] * have neq: "?fp ! j1 \<noteq> ?fp ! j2" unfolding distinct_conv_nth by auto
        let ?x = "real_of_2 (?cc ! i)" 
        define x where "x = ?x" 
        from ** have "x \<in> real_of_2 ` set (roots_of_2_irr (?fp ! j1))" unfolding x_def by auto
        with roots_of_2_irr(1)[OF pc1] have x1: "ipoly (?fp ! j1) x = 0" by auto
        from ** id have "x \<in> real_of_2 ` set (roots_of_2_irr (?fp ! j2))" unfolding x_def
          by (metis image_eqI nth_mem)
        with roots_of_2_irr(1)[OF pc2] have x2: "ipoly (?fp ! j2) x = 0" by auto
        have "ipoly p x = 0" using x1 mem unfolding roots_of_2_def by (metis frp1(2) p)
        from frp1(3)[OF p this] x1 x2 neq mem show False by blast
      qed
    qed
  qed
qed      

lift_definition (code_dt) roots_of_3 :: "int poly \<Rightarrow> real_alg_3 list" is roots_of_2
  by (insert roots_of_2, auto simp: list_all_iff)

lemma roots_of_3: 
  shows "p \<noteq> 0 \<Longrightarrow> real_of_3 ` set (roots_of_3 p) = {x. ipoly p x = 0}"
    "distinct (map real_of_3 (roots_of_3 p))" 
proof -
  show "p \<noteq> 0 \<Longrightarrow> real_of_3 ` set (roots_of_3 p) = {x. ipoly p x = 0}"
    by (transfer; intro roots_of_2, auto)
  show "distinct (map real_of_3 (roots_of_3 p))" 
    by (transfer; insert roots_of_2, auto)
qed

lift_definition roots_of_real_alg :: "int poly \<Rightarrow> real_alg list" is roots_of_3 . 

lemma roots_of_real_alg: 
  "p \<noteq> 0 \<Longrightarrow> real_of ` set (roots_of_real_alg p) = {x. ipoly p x = 0}" 
  "distinct (map real_of (roots_of_real_alg p))"
proof -
  show "p \<noteq> 0 \<Longrightarrow> real_of ` set (roots_of_real_alg p) = {x. ipoly p x = 0}"
    by (transfer', insert roots_of_3, auto)
  show "distinct (map real_of (roots_of_real_alg p))"      
    by (transfer, insert roots_of_3(2), auto)
qed

definition real_roots_of_int_poly :: "int poly \<Rightarrow> real list" where
  "real_roots_of_int_poly p = map real_of (roots_of_real_alg p)"

definition real_roots_of_rat_poly :: "rat poly \<Rightarrow> real list" where
  "real_roots_of_rat_poly p = map real_of (roots_of_real_alg (snd (rat_to_int_poly p)))"

abbreviation rpoly :: "rat poly \<Rightarrow> 'a :: field_char_0 \<Rightarrow> 'a"
where "rpoly f \<equiv> poly (map_poly of_rat f)"

lemma real_roots_of_int_poly: "p \<noteq> 0 \<Longrightarrow> set (real_roots_of_int_poly p) = {x. ipoly p x = 0}" 
  "distinct (real_roots_of_int_poly p)" 
  unfolding real_roots_of_int_poly_def using roots_of_real_alg[of p] by auto

lemma real_roots_of_rat_poly: "p \<noteq> 0 \<Longrightarrow> set (real_roots_of_rat_poly p) = {x. rpoly p x = 0}" 
  "distinct (real_roots_of_rat_poly p)"
proof -
  obtain c q where cq: "rat_to_int_poly p = (c,q)" by force
  from rat_to_int_poly[OF this]
  have pq: "p = smult (inverse (of_int c)) (of_int_poly q)" 
    and c: "c \<noteq> 0" by auto
  have id: "{x. rpoly p x = (0 :: real)} = {x. ipoly q x = 0}" 
    unfolding pq by (simp add: c of_rat_of_int_poly hom_distribs)
  show "distinct (real_roots_of_rat_poly p)" unfolding real_roots_of_rat_poly_def cq snd_conv 
    using roots_of_real_alg(2)[of q] .
  assume "p \<noteq> 0" 
  with pq c have q: "q \<noteq> 0" by auto
  show "set (real_roots_of_rat_poly p) = {x. rpoly p x = 0}" unfolding id
    unfolding real_roots_of_rat_poly_def cq snd_conv using roots_of_real_alg(1)[OF q]
    by auto
qed

end
