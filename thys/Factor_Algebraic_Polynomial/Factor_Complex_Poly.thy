section \<open>Factorization of Polynomials with Algebraic Coefficients\<close>

subsection \<open>Complex Algebraic Coefficients\<close>

theory Factor_Complex_Poly
  imports 
    Roots_of_Real_Complex_Poly
begin
hide_const (open) MPoly_Type.smult MPoly_Type.degree MPoly_Type.coeff MPoly_Type.coeffs

definition factor_complex_main :: "complex poly \<Rightarrow> complex \<times> (complex \<times> nat) list" where
  "factor_complex_main p \<equiv> let (c,pis) = yun_rf (yun_polys p) in
    (c, concat (map (\<lambda> (p,i). map (\<lambda> r. (r,i)) (roots_of_complex_rf_poly p)) pis))"

lemma roots_of_complex_poly_via_factor_complex_main: 
  "map fst (snd (factor_complex_main p)) = roots_of_complex_poly p"
proof (cases "p = 0")
  case True
  have [simp]: "yun_rf (yun_polys 0) = (0,[])"
    by (transfer, simp)
  show ?thesis 
    unfolding factor_complex_main_def Let_def roots_of_complex_poly_def True
    by simp
next
  case False
  hence p: "(p = 0) = False" by simp
  obtain c rts where yun: "yun_rf (yun_polys p) = (c,rts)" by force
  show ?thesis 
    unfolding factor_complex_main_def Let_def roots_of_complex_poly_def p if_False
      roots_of_complex_rf_polys_def polys_rf_def o_def yun split snd_conv map_map
    by (induct rts, auto simp: o_def)
qed

lemma distinct_factor_complex_main:
  "distinct (map fst (snd (factor_complex_main p)))" 
  unfolding roots_of_complex_poly_via_factor_complex_main
  by (rule distinct_roots_of_complex_poly)
    
lemma factor_complex_main: assumes rt: "factor_complex_main p = (c,xis)"
  shows "p = smult c (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)"
proof -
  obtain d pis where yun: "yun_factorization gcd p = (d,pis)" by force
  obtain d' pis' where yun_rf: "yun_rf (yun_polys p) = (d',pis')" by force
  let ?p = poly_rf
  let ?map = "map (\<lambda> (p,i). (?p p, i))" 
  from yun yun_rf have d': "d' = d" and pis: "pis = ?map pis'" 
    by (atomize(full), transfer, auto)  
  from rt[unfolded factor_complex_main_def yun_rf split Let_def d']
  have xis: "xis = concat (map (\<lambda>(p, i). map (\<lambda>r. (r, i)) (roots_of_complex_rf_poly p)) pis')"
    and d: "d = c"
    by (auto split: if_splits)
  note yun = yun_factorization[OF yun[unfolded d]]
  note yun = square_free_factorizationD[OF yun(1)] yun(2)[unfolded snd_conv]
  let ?exp = "\<lambda> pis. \<Prod>(x, i)\<leftarrow>concat
    (map (\<lambda>(p, i). map (\<lambda>r. (r, i)) (roots_of_complex_rf_poly p)) pis). [:- x, 1:] ^ Suc i"
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  also have "(\<Prod>(a, i)\<in>set pis. a ^ Suc i) = (\<Prod>(a, i)\<leftarrow>pis. a ^ Suc i)"
    by (rule prod.distinct_set_conv_list[OF yun(5)])
  also have "\<dots> = ?exp pis'" using yun(2,6) unfolding pis 
  proof (induct pis')
    case (Cons pi pis)
    obtain p i where pi: "pi = (p,i)" by force
    let ?rts = "roots_of_complex_rf_poly p"
    note Cons = Cons[unfolded pi]
    have IH: "(\<Prod>(a, i)\<leftarrow>?map pis. a ^ Suc i) = (?exp pis)"
      by (rule Cons(1)[OF Cons(2-3)], auto)
    from Cons(2-3)[of "?p p" i] have p: "square_free (?p p)" "degree (?p p) \<noteq> 0" "?p p \<noteq> 0" "monic (?p p)" by auto
    have "(\<Prod>(a, i)\<leftarrow>?map (pi # pis). a ^ Suc i) = ?p p ^ Suc i * (\<Prod>(a, i)\<leftarrow>?map pis. a ^ Suc i)"
      unfolding pi by simp
    also have "(\<Prod>(a, i)\<leftarrow>?map pis. a ^ Suc i) = ?exp pis" by (rule IH)
    finally have id: "(\<Prod>(a, i)\<leftarrow>?map (pi # pis). a ^ Suc i) = ?p p ^ Suc i * ?exp pis" by simp
    have "?exp (pi # pis) = ?exp [(p,i)] * ?exp pis" unfolding pi by simp
    also have "?exp [(p,i)] = (\<Prod>(x, i)\<leftarrow> (map (\<lambda>r. (r, i)) ?rts). [:- x, 1:] ^ Suc i)" 
      by simp
    also have "\<dots> = (\<Prod> x \<leftarrow> ?rts. [:- x, 1:])^Suc i"
      unfolding prod_list_power by (rule arg_cong[of _ _ prod_list], auto)
    also have "(\<Prod> x \<leftarrow> ?rts. [:- x, 1:]) = ?p p" 
    proof -
      from fundamental_theorem_algebra_factorized[of "?p p", unfolded \<open>monic (?p p)\<close>]
      obtain as where as: "?p p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by (metis smult_1_left)
      also have "\<dots> = (\<Prod>a\<in>set as. [:- a, 1:])"
      proof (rule sym, rule prod.distinct_set_conv_list, rule ccontr)
        assume "\<not> distinct as" 
        from not_distinct_decomp[OF this] obtain as1 as2 as3 a where
          a: "as = as1 @ [a] @ as2 @ [a] @ as3" by blast
        define q where "q = (\<Prod>a\<leftarrow>as1 @ as2 @ as3. [:- a, 1:])"
        have "?p p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by fact
        also have "\<dots> = (\<Prod>a\<leftarrow>([a] @ [a]). [:- a, 1:]) * q"
          unfolding q_def a map_append prod_list.append by (simp only: ac_simps)
        also have "\<dots> = [:-a,1:] * [:-a,1:] * q" by simp
        finally have "?p p = ([:-a,1:] * [:-a,1:]) * q" by simp
        hence "[:-a,1:] * [:-a,1:] dvd ?p p" unfolding dvd_def ..
        with \<open>square_free (?p p)\<close>[unfolded square_free_def, THEN conjunct2, rule_format, of "[:-a,1:]"] 
        show False by auto
      qed
      also have "set as = {x. poly (?p p) x = 0}" unfolding as poly_prod_list 
        by (simp add: o_def, induct as, auto)
      also have "\<dots> = set ?rts" by (simp add: roots_of_complex_rf_poly(1))
      also have "(\<Prod>a\<in>set ?rts. [:- a, 1:]) = (\<Prod>a\<leftarrow>?rts. [:- a, 1:])"
        by (rule prod.distinct_set_conv_list[OF roots_of_complex_rf_poly(2)])
      finally show ?thesis by simp
    qed
    finally have id2: "?exp (pi # pis) = ?p p ^ Suc i * ?exp pis" by simp
    show ?case unfolding id id2 ..
  qed simp
  also have "?exp pis' = (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)" unfolding xis ..
  finally show ?thesis unfolding p xis by simp
qed

definition factor_complex_poly :: "complex poly \<Rightarrow> complex \<times> (complex poly \<times> nat) list" where
  "factor_complex_poly p = (case factor_complex_main p of
     (c,ris) \<Rightarrow> (c, map (\<lambda> (r,i). ([:-r,1:],Suc i)) ris))"

lemma distinct_factor_complex_poly:
  "distinct (map fst (snd (factor_complex_poly p)))" 
proof -
  obtain c ris where main: "factor_complex_main p = (c,ris)" by force
  show ?thesis unfolding factor_complex_poly_def main split
    using distinct_factor_complex_main[of p, unfolded main]
    unfolding snd_conv o_def
    unfolding distinct_map by (force simp: inj_on_def)
qed


theorem factor_complex_poly: assumes fp: "factor_complex_poly p = (c,qis)"
  shows 
  "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" 
  "(q,i) \<in> set qis \<Longrightarrow> irreducible q \<and> i \<noteq> 0 \<and> monic q \<and> degree q = 1"
proof -
  from fp[unfolded factor_complex_poly_def]
  obtain pis where fp: "factor_complex_main p = (c,pis)"
    and qis: "qis = map (\<lambda>(r, i). ([:- r, 1:], Suc i)) pis"
    by (cases "factor_complex_main p", auto)
  from factor_complex_main[OF fp] have p: "p = smult c (\<Prod>(x, i)\<leftarrow>pis. [:- x, 1:] ^ Suc i)" .
  show "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" unfolding p qis
    by (rule arg_cong[of _ _ "\<lambda> p. smult c (prod_list p)"], auto)
  show "(q,i) \<in> set qis \<Longrightarrow> irreducible q \<and> i \<noteq> 0 \<and> monic q \<and> degree q = 1"
    using linear_irreducible_field[of q] unfolding qis by auto
qed

end