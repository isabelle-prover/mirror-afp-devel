section \<open>Factorization Oracle\<close>

text \<open>We define an overloaded constant which serves as an arbitrary factorization oracle
  for the rational factorization process. We provide three oracles.
  We implemented the Berlekamp-Hensel
  factorization algorithm, one can choose an external factorization algorithm,
  or one uses a hybrid approach where Berlekamp-Hensel is invoked on small inputs
  and the external one is invoked on larger ones. One just has to load exactly one of 
  the corresponding \emph{Select-\ldots-Factorization}-theory. 
  If this is not purely the Berlekamp-Hensel algorithm, one has to manually implement the
  external factorization algorithm.

  An example external oracle is available in Mathematica.hs.

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
     p = listprod oracle_answer \<and> (\<forall> f \<in> set oracle_answer. degree f \<noteq> 0))"

lemma oracle_soundD: "oracle_sound p oracle_answer \<Longrightarrow>
     content p = 1 \<Longrightarrow> square_free p \<Longrightarrow> degree p \<noteq> 0 \<Longrightarrow>
     p = listprod oracle_answer \<and> (\<forall> f \<in> set oracle_answer. degree f \<noteq> 0)"
   unfolding oracle_sound_def by auto

definition oracle_check :: "int poly \<Rightarrow> int poly list \<Rightarrow> bool" where
  "oracle_check p ps = (p = listprod ps \<and> (\<forall> p \<in> set ps. degree p \<noteq> 0))"

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
    

text \<open>Factorization oracle for rational polynomials: a wrapper to the integer-factorization oracle.\<close>

definition factorization_oracle_rat_poly :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "factorization_oracle_rat_poly p = (let
     (a,psi) = yun_factorization gcd_rat_poly p;
     oracle = (\<lambda> (q,i). let (b,f) = rat_to_normalized_int_poly q; 
       (* f is content-free, square-free, degree f \<noteq> 0 *)
         fs = oracle_wrapper f; (* this invokes the oracle and checks validity *) 
         gs = map (map_poly of_int) fs;
         hsi = map (\<lambda> h. (h,Suc i)) gs
       in (b^Suc i, hsi));
     pre_result = map oracle psi;
     factors = concat (map snd pre_result);
     b = a * listprod (map fst pre_result)
   in (b,factors))"

text \<open>The wrapper ensures a valid factorization + square-free factors.\<close>

lemma factorization_oracle_rat_poly: assumes "factorization_oracle_rat_poly p = (c,fs)"
  shows "p = smult c (\<Prod>(f, i)\<leftarrow>fs. f ^ i)"
    "\<And> f i. (f,i) \<in> set fs \<Longrightarrow> square_free f \<and> degree f \<noteq> 0 \<and> i \<noteq> 0"
proof -
  obtain a psi where yun: "yun_factorization gcd p = (a,psi)" by force
  from yun_factorization[OF this] have sff: "square_free_factorization p (a,psi)" by auto
  def oracl \<equiv> "(\<lambda> (q,i). let (b,f) = rat_to_normalized_int_poly q;
       fs = oracle_wrapper f;  
       gs = map (map_poly rat_of_int) fs;
       hsi = map (\<lambda> h. (h,Suc i)) gs
       in (b^Suc i, hsi))"
  def pre_result \<equiv> "map oracl psi"
  from assms[unfolded factorization_oracle_rat_poly_def yun gcd_rat_poly split Let_def]
  have c: "c = a * listprod (map fst pre_result)" and fs: "fs = concat (map snd pre_result)"
    unfolding pre_result_def oracl_def by auto
  note p = square_free_factorization_listprod[OF sff]
  note sff = square_free_factorizationD[OF sff]
  let ?id = "\<lambda> psi. (\<Prod>(a, i)\<leftarrow>psi. a ^ Suc i) =
    smult (listprod (map (fst o oracl) psi))
     (\<Prod>(x, y) \<leftarrow> (concat (map (snd o oracl) psi)). x ^ y)"
  let ?prop = "\<lambda> psi f i. (f, i) \<in> set (concat (map snd (map oracl psi))) \<longrightarrow>
           square_free f \<and> degree f \<noteq> 0 \<and> i \<noteq> 0"
  let ?rp = "map_poly rat_of_int"  
  interpret inj_ring_hom ?rp by (rule ri.inj_ring_hom_map_poly)
  have "?id psi \<and> (\<forall> f i. ?prop psi f i)"
    unfolding fs pre_result_def using sff(2)
  proof (induct psi)
    case (Cons ai psi)
    obtain a i where ai: "ai = (a,i)" by force
    note IH = Cons(1)[OF Cons(2)]
    from IH[of "\<lambda> _ x. x"] have id: "?id psi" and p: "\<And> f i. ?prop psi f i" by (auto simp: o_def)
    from Cons(2) ai have a: "square_free a" "degree a \<noteq> 0" by auto
    hence a0: "a \<noteq> 0" by auto
    obtain b fs where oracl: "oracl (a, i) = (b,fs)" by force
    obtain c g where rp: "rat_to_normalized_int_poly a = (c,g)" by force    
    from rat_to_normalized_int_poly[OF rp] have c0: "c \<noteq> 0" by auto
    let ?g = "map_poly rat_of_int g"
    from oracl[unfolded oracl_def split rp Let_def]
    have b: "b = c ^ Suc i" and fs: "fs = map (\<lambda>h. (h, Suc i)) (map ?rp (oracle_wrapper g))" by auto
    def ii \<equiv> "Suc i" def og \<equiv> "map ?rp (oracle_wrapper g)"
    note rp = rat_to_normalized_int_poly[OF rp]
    from rp a0 a have g: "content g = 1" "degree g \<noteq> 0" "g \<noteq> 0" by auto
    from square_free_smult[OF _ a(1)[unfolded rp(1)], of "inverse c"] c rp(2) 
    have sfgg: "square_free ?g" by simp
    hence sfg: "square_free g" unfolding square_free_def dvd_def by force
    have g2: "listprod (oracle_wrapper g) = g" "\<And> f. f\<in>set (oracle_wrapper g) \<Longrightarrow> degree f \<noteq> 0"
      using oracle_soundD[OF oracle_wrapper g(1) sfg g(2)] by auto
    have "a * a ^ i = a ^ Suc i" by simp
    also have "a ^ Suc i = smult b (?g ^ Suc i)" unfolding rp(1) smult_power b ..
    also have "?g = ?rp (listprod (oracle_wrapper g))" unfolding g2 ..
    also have "\<dots> ^ Suc i = (\<Prod>(x, y)\<leftarrow>fs. x ^ y)" unfolding fs ii_def[symmetric]
      hom_listprod listprod_power og_def[symmetric]
      by (induct og, auto)
    finally have id2: "a * a ^ i = smult b (\<Prod>(x, y)\<leftarrow>fs. x ^ y)" .
    have *: "(\<Prod>(a, i)\<leftarrow>(a, i) # psi. a ^ Suc i) = a ^ Suc i * (\<Prod>(a, i)\<leftarrow>psi. a ^ Suc i)" by simp
    have id: "?id (ai # psi)" unfolding ai * id
      by (simp add: oracl id2 ac_simps)
    show ?case unfolding id
    proof (rule conjI, force simp: o_def, intro allI)
      fix f j
      have "?prop [(a,i)] f j" 
      proof (intro impI, goal_cases)
        case 1
        hence fj: "(f, j) \<in> set fs" using oracl by simp
        from this[unfolded fs] obtain h where j: "j \<noteq> 0" and h: "h \<in> set (oracle_wrapper g)"
          and f: "f = map_poly rat_of_int h" by auto
        from g2(2)[OF h] have "degree h \<noteq> 0" .
        with f have df: "degree f \<noteq> 0" by auto
        from listprod_dvd[OF h, unfolded g2(1)] have "h dvd g" .
        hence "f dvd ?g" unfolding f dvd_def by auto
        from square_free_factor[OF this sfgg] j df
        show ?case by auto
      qed
      with p show "?prop (ai # psi) f j" unfolding ai by auto
    qed
  qed simp
  thus "p = smult c (\<Prod>(f, i)\<leftarrow> fs. f ^ i)"  
    "\<And> f i. (f,i) \<in> set fs \<Longrightarrow> square_free f \<and> degree f \<noteq> 0 \<and> i \<noteq> 0" 
    unfolding p c fs pre_result_def by auto
qed
  
lemma factorization_oracle_rat_poly_0[simp]: "factorization_oracle_rat_poly 0 = (0,[])"
  unfolding factorization_oracle_rat_poly_def by simp

end
