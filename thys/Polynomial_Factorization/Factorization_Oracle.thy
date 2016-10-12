section \<open>Factorization Oracle\<close>

text \<open>We define an overloaded constant which serves as an arbitrary factorization oracle
  for the rational factorization process. We provide three oracles.
  We implemented the Berlekamp-Hensel
  factorization algorithm, one can choose an external factorization algorithm,
  or one uses a hybrid approach where Berlekamp-Hensel is invoked on small inputs
  and the external one is invoked on larger ones. One just has to load exactly one of 
  the corresponding \emph{Select-\ldots-Factorization}-theory. 
  If this is not purely the Berlekamp-Hensel algorithm, one has to manually implement the
  external factorization algorithm or adapt the wrapper that invokes Mathematica.

  All of the oracles are invoked via a wrapper function which already performs a
  certified square-free factorization and the rational-to-integer factorization. 
  As a result, the oracle can assume to obtain a content-free, 
  square-free integer polynomial.\<close>

theory Factorization_Oracle
imports
  Gauss_Lemma
  Square_Free_Factorization
  Polynomial_Division
  "../Show/Show_Poly"
begin

text \<open>input to factorization-oracle: content-free and square-free, 
  non-zero-degree integer polynomial f,
  desired output: fully factored polynomial over the integers,
  required output: list of (non-zero-degree) factors whose product delivers the input.\<close>

consts factorization_oracle_int_poly :: "int list \<Rightarrow> int list list"

definition oracle_sound :: "int poly \<Rightarrow> int poly list \<Rightarrow> bool" where
  "oracle_sound p oracle_answer = (
     content p = 1 \<longrightarrow> square_free p \<longrightarrow> degree p \<noteq> 0 \<longrightarrow>
     p = prod_list oracle_answer \<and> (\<forall> f \<in> set oracle_answer. degree f \<noteq> 0))"

lemma oracle_soundD: "oracle_sound p oracle_answer \<Longrightarrow>
     content p = 1 \<Longrightarrow> square_free p \<Longrightarrow> degree p \<noteq> 0 \<Longrightarrow>
     p = prod_list oracle_answer \<and> (\<forall> f \<in> set oracle_answer. degree f \<noteq> 0)"
   unfolding oracle_sound_def by auto

definition oracle_check :: "int poly \<Rightarrow> int poly list \<Rightarrow> bool" where
  "oracle_check p ps = (p = prod_list ps \<and> (\<forall> p \<in> set ps. degree p \<noteq> 0))"

lemma oracle_check: "oracle_check p ps \<Longrightarrow> oracle_sound p ps"
  unfolding oracle_sound_def oracle_check_def by auto

definition oracle_wrapper :: "int poly \<Rightarrow> int poly list" where
  "oracle_wrapper p = (let 
    fs = factorization_oracle_int_poly (coeffs p);
    fs' = map poly_of_list fs;
    hs = (if oracle_check p fs' then fs' else Code.abort
      (String.implode
       (''error in factorization_oracle_int_poly on input '' @ show (coeffs p))) (\<lambda> _. [p]))
    in hs)"

lemma oracle_sound_id: "oracle_sound p [p]" unfolding oracle_sound_def by auto

lemma oracle_wrapper: "oracle_sound p (oracle_wrapper p)"
proof -
  def fs \<equiv> "factorization_oracle_int_poly (coeffs p)"
  def fs' \<equiv> "map poly_of_list fs"
  show ?thesis
  proof (cases "oracle_check p fs'")
    case True
    hence "oracle_wrapper p = fs'" unfolding oracle_wrapper_def Let_def fs_def fs'_def by auto
    from oracle_check[OF True, folded this] show ?thesis .
  next
    case False
    hence "oracle_wrapper p = [p]" unfolding oracle_wrapper_def Let_def fs_def fs'_def by auto
    thus ?thesis using oracle_sound_id by auto
  qed
qed

definition oracle_wrapper_rat :: "rat poly \<Rightarrow> rat \<times> rat poly list" where
  "oracle_wrapper_rat q \<equiv> let (b,f) = rat_to_normalized_int_poly q; 
       fs = oracle_wrapper f; (* this invokes the oracle and checks validity *) 
       gs = map (map_poly of_int) fs
     in (b, gs)"
    

text \<open>Factorization oracle for rational polynomials: a wrapper to the integer-factorization oracle.\<close>

definition factorization_oracle_rat_poly :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "factorization_oracle_rat_poly p = (let
     (a,psi) = yun_factorization gcd_rat_poly p;
     oracle = (\<lambda> (q,i). case oracle_wrapper_rat q of (b,fs) \<Rightarrow>  
         (b^Suc i, map (\<lambda> f. (f,i)) fs));
     pre_result = map oracle psi;
     factors = concat (map snd pre_result);
     b = a * prod_list (map fst pre_result)
   in (b,factors))"

text \<open>The wrapper ensures a valid factorization + square-free factors.\<close>

lemma factorization_oracle_rat_poly: assumes "factorization_oracle_rat_poly p = (c,fs)"
  shows "square_free_factorization p (c,fs)"
proof -
  obtain a psi where yun: "yun_factorization gcd p = (a,psi)" by force
  from yun_factorization[OF this] have sff: "square_free_factorization p (a,psi)" by auto
  obtain oracl where oracl: "oracl = (\<lambda> (q,i). case oracle_wrapper_rat q of (b,fs) \<Rightarrow>  
         (b^Suc i, map (\<lambda> f. (f,i)) fs))" by auto
  obtain pre_result where pre_result: "pre_result = map oracl psi" by blast
  from assms[unfolded factorization_oracle_rat_poly_def yun gcd_rat_poly split Let_def]
  have c: "c = a * prod_list (map fst pre_result)" and fs: "fs = concat (map snd pre_result)"
    unfolding pre_result oracl by auto
  show ?thesis
  proof (rule square_free_factorization_further_factorization[OF sff _ oracl pre_result c fs])
    fix a i d gs
    assume ai: "(a,i) \<in> set psi" and a: "oracle_wrapper_rat a = (d,gs)"
    obtain b fs where oracl: "oracl (a, i) = (b,fs)" by force
    obtain c g where rp: "rat_to_normalized_int_poly a = (c,g)" by force    
    from rat_to_normalized_int_poly[OF rp] have c0: "c \<noteq> 0" by auto
    let ?r = "map_poly rat_of_int"
    from a[unfolded oracl oracle_wrapper_rat_def rp Let_def split]
    have c: "c = d" and gs: "gs = map ?r (oracle_wrapper g)" by auto
    note rp = rat_to_normalized_int_poly[OF rp, unfolded c]
    note sff = square_free_factorizationD[OF sff]
    from sff(2)[OF ai] have da: "degree a \<noteq> 0" and a: "a \<noteq> 0" and sf: "square_free a" by auto
    interpret ri: inj_ring_hom ?r by (rule ri.inj_ring_hom_map_poly)
    from rp(1-2) da have dg: "degree g \<noteq> 0" by auto
    from sf rp(1) rp(2) have sfg: "square_free (?r g)" by simp
    hence "square_free g" unfolding square_free_def by (force simp: dvd_def)
    from oracle_soundD[OF oracle_wrapper rp(3)[OF a] this dg]
    have id: "prod_list (oracle_wrapper g) = g" and 
      deg: "\<And> f. f \<in> set (oracle_wrapper g) \<Longrightarrow> degree f \<noteq> 0"
      by auto
    show "a = smult d (prod_list gs) \<and> (\<forall>f\<in>set gs. degree f \<noteq> 0)" unfolding rp(1) gs
      using deg by (auto, subst ri.hom_prod_list[symmetric], unfold id, simp)
  qed
qed
  
lemma factorization_oracle_rat_poly_0[simp]: "factorization_oracle_rat_poly 0 = (0,[])"
  unfolding factorization_oracle_rat_poly_def by simp

end
