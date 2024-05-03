section \<open>Hilbert's 10th Problem to Linear Inequality\<close>

theory Hilbert10_to_Inequality
  imports 
    Preliminaries_on_Polynomials_1
begin

definition hilbert10_problem :: "int mpoly \<Rightarrow> bool" where
  "hilbert10_problem p = (\<exists> \<alpha>. insertion \<alpha> p = 0)" 

text \<open>A polynomial is positive, if every coefficient is positive.
  Since the \<open>@{const coeff}\<close>-function of \<open>'a mpoly\<close> maps a coefficient
  to every monomial, this means that positiveness is expressed as
  @{term "coeff p m \<noteq> 0 \<longrightarrow> coeff p m > 0"} for monomials \<open>m\<close>. 
  However, this condition is equivalent to just demand @{term "coeff p m \<ge> 0"}
  for all \<open>m\<close>.

  This is the reason why \<open>positive polynomials\<close> are defined in the same way
  as one would define \<open>non-negative polynomials\<close>.\<close>
definition positive_poly :: "'a :: linordered_idom mpoly \<Rightarrow> bool" where
  "positive_poly p = (\<forall> m. coeff p m \<ge> 0)" 

definition positive_interpr :: "(var \<Rightarrow> 'a :: linordered_idom) \<Rightarrow> bool" where
  "positive_interpr \<alpha> = (\<forall> x. \<alpha> x > 0)" 

definition positive_poly_problem :: "'a :: linordered_idom mpoly \<Rightarrow> 'a mpoly \<Rightarrow> bool" where
  "positive_poly p \<Longrightarrow> positive_poly q \<Longrightarrow> positive_poly_problem p q = 
    (\<exists> \<alpha>. positive_interpr \<alpha> \<and> insertion \<alpha> p \<ge> insertion \<alpha> q)" 

datatype flag = Positive | Negative | Zero

fun flag_of :: "'a :: {ord,zero} \<Rightarrow> flag" where
  "flag_of x = (if x < 0 then Negative else if x > 0 then Positive else Zero)" 

definition subst_flag :: "var set \<Rightarrow> (var \<Rightarrow> flag) \<Rightarrow> var \<Rightarrow> 'a :: comm_ring_1 mpoly" where
  "subst_flag V flag x = (if x \<in> V then (case flag x of
      Positive \<Rightarrow> Var x
    | Negative \<Rightarrow> - Var x
    | Zero \<Rightarrow> 0)
     else 0)" 

definition assignment_flag :: "var set \<Rightarrow> (var \<Rightarrow> flag) \<Rightarrow> (var \<Rightarrow> 'a :: comm_ring_1) \<Rightarrow> (var \<Rightarrow> 'a)" where
  "assignment_flag V flag \<alpha> x = (if x \<in> V then (case flag x of
      Positive \<Rightarrow> \<alpha> x
    | Negative \<Rightarrow> - \<alpha> x
    | Zero \<Rightarrow> 1)
    else 1)"

definition correct_flags :: "var set \<Rightarrow> (var \<Rightarrow> flag) \<Rightarrow> (var \<Rightarrow> 'a :: ordered_comm_ring) \<Rightarrow> bool" where
  "correct_flags V flag \<alpha> = (\<forall> x \<in> V. flag x = flag_of (\<alpha> x))" 

lemma correct_flag_substitutions: fixes p :: "'a :: linordered_idom mpoly" 
  assumes "vars p \<subseteq> V" 
    and beta: "\<beta> = assignment_flag V flag \<alpha>" 
    and sigma: "\<sigma> = subst_flag V flag" 
    and q: "q = substitute \<sigma> p"  
    and corr: "correct_flags V flag \<alpha>"
  shows "insertion \<beta> q = insertion \<alpha> p" "positive_interpr \<beta>"
proof -
  show "insertion \<beta> q = insertion \<alpha> p" unfolding q insertion_substitute
  proof (rule insertion_irrelevant_vars)
    fix x
    assume "x \<in> vars p" 
    with assms have x: "x \<in> V" by auto
    with corr have flag: "flag x = flag_of (\<alpha> x)" unfolding correct_flags_def by auto
    
    show "insertion \<beta> (\<sigma> x) = \<alpha> x" 
      unfolding beta sigma assignment_flag_def subst_flag_def using x flag
      by (cases "flag x", auto split: if_splits simp: insertion_Var insertion_uminus)
  qed
  show "positive_interpr \<beta>" using corr
    unfolding positive_interpr_def beta assignment_flag_def correct_flags_def
    by auto
qed

definition hilbert_encode1 :: "int mpoly \<Rightarrow> int mpoly list" where
  "hilbert_encode1 r = (let r2 = r^2;
     V = vars_list r2;
     flag_lists = product_lists (map (\<lambda> x. map (\<lambda> f. (x,f)) [Positive,Negative,Zero]) V);
     subst = (\<lambda> fl. subst_flag (set V) (\<lambda> x. case map_of fl x of Some f \<Rightarrow> f | None \<Rightarrow> Zero))
    in map (\<lambda> fl. substitute (subst fl) r2) flag_lists)"  

lemma hilbert_encode1: 
  "hilbert10_problem r \<longleftrightarrow> (\<exists> p \<in> set (hilbert_encode1 r). \<exists> \<alpha>. positive_interpr \<alpha> \<and> insertion \<alpha> p \<le> 0)" 
proof 
  define r2 where "r2 = r^2" 
  define V where "V = vars_list r2" 
  define flag_list where "flag_list = product_lists (map (\<lambda> x. map (\<lambda> f. (x,f)) [Positive,Negative,Zero]) V)" 
  define subst where "subst = (\<lambda> fl. subst_flag (set V) (\<lambda> x. case map_of fl x of Some f \<Rightarrow> f | None \<Rightarrow> Zero) :: var \<Rightarrow> int mpoly)" 
  have hilb_enc: "hilbert_encode1 r = map (\<lambda> fl. substitute (subst fl) r2) flag_list" 
    unfolding subst_def flag_list_def V_def r2_def Let_def hilbert_encode1_def ..
  have "hilbert10_problem r \<longleftrightarrow> (\<exists> \<alpha>. insertion \<alpha> r = 0)" unfolding hilbert10_problem_def by auto
  also have "\<dots> \<longleftrightarrow> (\<exists> \<alpha>. (insertion \<alpha> r)^2 \<le> 0)" 
    by (intro ex_cong1, auto)
  also have "\<dots> \<longleftrightarrow> (\<exists> \<alpha>. insertion \<alpha> r2 \<le> 0)" 
    by (intro ex_cong1, auto simp: power2_eq_square insertion_mult r2_def)
  finally have hilb: "hilbert10_problem r = (\<exists>\<alpha>. insertion \<alpha> r2 \<le> 0)" (is "?h1 = ?h2") .
  let ?r1 = "(\<exists> p \<in> set (hilbert_encode1 r). \<exists> \<alpha>. positive_interpr \<alpha> \<and> insertion \<alpha> p \<le> 0)" 
  {
    assume ?r1
    from this[unfolded hilb_enc]
    show "hilbert10_problem r" unfolding hilb by (auto simp add: insertion_substitute)
  }
  {
    assume ?h1
    with hilb obtain \<alpha> where solution: "insertion \<alpha> r2 \<le> 0" by auto
    define fl where "fl = map (\<lambda> x. (x, flag_of (\<alpha> x))) V" 
    define flag where "flag = (\<lambda> x. case map_of fl x of Some f \<Rightarrow> f | None \<Rightarrow> Zero)" 
    have vars: "vars r2 \<subseteq> set V" unfolding V_def by simp
    have fl: "fl \<in> set flag_list" unfolding flag_list_def product_lists_set fl_def
      apply (simp add: list_all2_map2 list_all2_map1, intro list_all2_refl)
      by auto
    have mem: "substitute (subst_flag (set V) flag) r2 \<in> set (hilbert_encode1 r)" 
      unfolding hilb_enc subst_def flag_def using fl by auto
    have corr: "correct_flags (set V) flag \<alpha>" unfolding correct_flags_def flag_def fl_def
      by (auto split: option.splits dest!: map_of_SomeD simp: map_of_eq_None_iff image_comp)
    show ?r1 using solution correct_flag_substitutions[OF vars refl refl refl corr]
      by (intro bexI[OF _ mem], auto)
  }
qed

lemma pos_neg_split: "mpoly_coeff_filter (\<lambda> x. (x :: 'a :: linordered_idom) > 0) p + mpoly_coeff_filter (\<lambda> x. x < 0) p = p" (is "?l + ?r = p")
proof -
  {
    fix m
    let ?c = "coeff p m" 
    have "coeff (?l + ?r) m = coeff ?l m + coeff ?r m" by (simp add: coeff_add)
    also have "\<dots> = coeff p m" unfolding mpoly_coeff_filter 
      by (cases "?c < 0"; cases "?c > 0"; cases "?c = 0", auto)
    finally have "coeff (?l + ?r) m = coeff p m" .
  }
  thus ?thesis using coeff_eq by blast
qed

definition hilbert_encode2 :: "int mpoly \<Rightarrow> int mpoly \<times> int mpoly" where
  "hilbert_encode2 p = 
     (- mpoly_coeff_filter (\<lambda> x. x < 0) p, mpoly_coeff_filter (\<lambda> x. x > 0) p)" 

lemma hilbert_encode2: assumes "hilbert_encode2 p = (r,s)" 
  shows "positive_poly r" "positive_poly s" "insertion \<alpha> p \<le> 0 \<longleftrightarrow> insertion \<alpha> r \<ge> insertion \<alpha> s" 
proof -
  from assms[unfolded hilbert_encode2_def, simplified]
  have s: "s = mpoly_coeff_filter (\<lambda> x. x > 0) p" 
    and r: "r = - mpoly_coeff_filter (\<lambda> x. x < 0) p" (is "_ = - ?q") by auto
  have "p = s + ?q" unfolding s using pos_neg_split[of p] by simp
  also have "\<dots> = s - r" unfolding s r by simp
  finally have "insertion \<alpha> p \<le> 0 \<longleftrightarrow> insertion \<alpha> (s - r) \<le> 0" by simp
  also have "insertion \<alpha> (s - r) = insertion \<alpha> s - insertion \<alpha> r" 
    by (metis add_uminus_conv_diff insertion_add insertion_uminus)
  finally show "insertion \<alpha> p \<le> 0 \<longleftrightarrow> insertion \<alpha> r \<ge> insertion \<alpha> s" by auto
  show "positive_poly s" unfolding positive_poly_def s using mpoly_coeff_filter[of "(\<lambda> x. x > 0)" p]
    by (auto simp: when_def)
  show "positive_poly r" unfolding positive_poly_def r coeff_uminus using mpoly_coeff_filter[of "(\<lambda> x. x < 0)" p]
    by (auto simp: when_def)
qed

definition hilbert_encode :: "int mpoly \<Rightarrow> (int mpoly \<times> int mpoly)list" where
  "hilbert_encode = map hilbert_encode2 o hilbert_encode1" 

text \<open>Lemma 2.2 in paper\<close>

lemma hilbert_encode_positive: "hilbert10_problem p 
  \<longleftrightarrow> (\<exists> (r,s) \<in> set (hilbert_encode p). positive_poly_problem r s)"
proof -
  have "hilbert10_problem p \<longleftrightarrow> (\<exists>p'\<in>set (hilbert_encode1 p). \<exists>\<alpha>. positive_interpr \<alpha> \<and> insertion \<alpha> p' \<le> 0)" 
    using hilbert_encode1[of p] by blast
  also have "\<dots> \<longleftrightarrow> (\<exists> (r,s) \<in> set (hilbert_encode p). positive_poly_problem r s)" (is "?l = ?r")
  proof
    assume ?l
    then obtain p' \<alpha> where mem: "p'\<in>set (hilbert_encode1 p)" and sol: "positive_interpr \<alpha>" "insertion \<alpha> p' \<le> 0" by blast
    obtain r s where 2: "hilbert_encode2 p' = (r,s)" by force
    from mem 2 have mem: "(r,s) \<in> set (hilbert_encode p)" unfolding hilbert_encode_def o_def by force
    from hilbert_encode2[OF 2] sol have "positive_poly_problem r s" using positive_poly_problem_def[of r s] by force
    with mem show ?r by blast
  next
    assume ?r
    then obtain r s where mem: "(r,s) \<in> set (hilbert_encode p)" and sol: "positive_poly_problem r s" by auto
    from mem[unfolded hilbert_encode_def o_def] obtain p' where 
      mem: "p' \<in> set (hilbert_encode1 p)" 
      and "hilbert_encode2 p' = (r,s)" by force
    from hilbert_encode2[OF this(2)] sol positive_poly_problem_def[of r s]
    have "(\<exists>\<alpha>. positive_interpr \<alpha> \<and> insertion \<alpha> p' \<le> 0)" by auto
    with mem hilbert_encode1[of p] show ?l by auto
  qed
  finally show ?thesis .
qed

end
