(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Factoring Rational Polynomials\<close>

text \<open>We combine the factorization algorithm for integer polynomials
  with Gauss Lemma to a factorization algorithm for rational polynomials.\<close>
theory Factorize_Rat_Poly
imports 
  Factorize_Int_Poly
begin

definition factorize_rat_poly :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "factorize_rat_poly f = (case rat_to_normalized_int_poly f of
     (c,g) \<Rightarrow> case factorize_int_poly g of (d,fs) \<Rightarrow> (c * rat_of_int d, 
     map (\<lambda> (fi,i). (map_poly rat_of_int fi, i)) fs))" 

lemma factorize_rat_poly: assumes res: "factorize_rat_poly f = (c,fs)"
shows "square_free_factorization f (c,fs)"
  "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi"
proof -
  let ?r = rat_of_int
  let ?rp = "map_poly ?r" 
  obtain d g where ri: "rat_to_normalized_int_poly f = (d,g)" by force
  obtain e gs where fi: "factorize_int_poly g = (e,gs)" by force
  from res[unfolded factorize_rat_poly_def ri fi split]
  have c: "c = d * ?r e" and fs: "fs = map (\<lambda> (fi,i). (?rp fi, i)) gs" by auto
  from factorize_int_poly[OF fi] have sff: "square_free_factorization g (e,gs)" 
    and irr: "\<And> fi i. (fi, i) \<in> set gs \<Longrightarrow> irreducible fi" by auto
  {
    fix fi i
    assume "(fi,i) \<in> set fs" 
    then obtain gi where fi: "fi = ?rp gi" and gi: "(gi,i) \<in> set gs" unfolding fs by auto
    from irr[OF gi] show irr: "irreducible fi" unfolding fi by (rule irreducible_int_rat)
  } note irr = this
  note sff' = square_free_factorizationD[OF sff]
  show "square_free_factorization f (c,fs)" unfolding square_free_factorization_def split
  proof (intro conjI impI allI)
    {
      fix a i
      assume ai: "(a,i) \<in> set fs" 
      from irr[OF this] show "degree a \<noteq> 0" "square_free a" 
        using irreducible_square_free irreducibleD by auto
      from ai obtain A where a: "a = ?rp A" and A: "(A,i) \<in> set gs" unfolding fs by auto
      fix b j
      assume "(b,j) \<in> set fs" and diff: "(a,i) \<noteq> (b,j)"
      from this(1) obtain B where b: "b = ?rp B" and B: "(B,j) \<in> set gs" unfolding fs by auto
      from diff[unfolded a b] ri.map_poly_inj have "(A,i) \<noteq> (B,j)" by auto
      from sff'(3)[OF A B this] have "coprime A B" .
      thus "coprime a b" unfolding a b using gcd_rat_to_gcd_int by auto
    }
    {
      assume "f = 0" with ri have *: "d = 1" "g = 0" unfolding rat_to_normalized_int_poly_def by auto
      with sff'(4)[OF *(2)] show "c = 0" "fs = []" unfolding c fs by auto
    }
    {
      fix n f 
      have "?rp (f ^ n) = (?rp f) ^ n"
        by (induct n, auto)
    } note exp = this
    show dist: "distinct fs" using sff'(5) unfolding fs distinct_map inj_on_def using ri.map_poly_inj by auto
    have "f = smult d (?rp g)" using rat_to_normalized_int_poly[OF ri] by auto
    also have "\<dots> = smult d (?rp (smult e (\<Prod>(a, i)\<in>set gs. a ^ Suc i)))" using sff'(1) by simp
    also have "\<dots> = smult c (?rp (\<Prod>(a, i)\<in>set gs. a ^ Suc i))" unfolding c by simp
    also have "?rp (\<Prod>(a, i)\<in>set gs. a ^ Suc i) = (\<Prod>(a, i)\<in>set fs. a ^ Suc i)"
      unfolding prod.distinct_set_conv_list[OF sff'(5)] prod.distinct_set_conv_list[OF dist]
      unfolding fs ri.map_poly_preserves_prod_list      
      by (rule arg_cong[where f = prod_list], insert exp, auto)
    finally show "f = smult c (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" by auto
  qed    
qed
  
end
