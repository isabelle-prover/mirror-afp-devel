section \<open>Separation of Roots: Sturm\<close>

text \<open>We adapt the existing theory on Sturm's theorem to work on rational numbers instead of real 
  numbers. The reason is that we want to implement real numbers as real algebraic numbers with the
  help of Sturm's theorem to separate the roots. To this end, we just copy the definitions of
  of the algorithms w.r.t. Sturm and let them be executed on rational numbers. We then
  prove that corresponds to a homomorphism and therefore can transfer the existing soundness results.\<close>

theory Sturm_Rat
imports 
  "../Sturm_Sequences/Sturm_Theorem"
  Algebraic_Numbers_Prelim
begin

subsection \<open>Interface for Separating Roots\<close>

text \<open>For a given rational polynomial, we need to know how many real roots are in a given closed interval,
  and how many real roots are in an interval $(-\infty,r]$.\<close>

datatype root_info = Root_Info (l_r: "rat \<Rightarrow> rat \<Rightarrow> nat") (inf_r: "rat \<Rightarrow> nat")
hide_const (open) l_r
hide_const (open) inf_r

definition count_roots_interval :: "real poly \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> nat) \<times> (real \<Rightarrow> nat)" where
  "count_roots_interval p = (let ps = sturm_squarefree p
    in ((\<lambda> a b. sign_changes ps a - sign_changes ps b + (if poly p a = 0 then 1 else 0)),
       (\<lambda> a. sign_changes_neg_inf ps - sign_changes ps a)))"

lemma count_roots_interval: assumes p: "p \<noteq> 0" 
  and cr: "count_roots_interval p = (cr,nr)"
  shows "a \<le> b \<Longrightarrow> cr a b = (card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0})"
    "nr a = card {x. x \<le> a \<and> poly p x = 0}"
proof -
  have id: "a \<le> b \<Longrightarrow> { x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = 
    { x. a < x \<and> x \<le> b \<and> poly p x = 0} \<union> (if poly p a = 0 then {a} else {})" 
    (is "_ \<Longrightarrow> _ = ?R \<union> ?S") using not_less by force
  have RS: "finite ?R" "finite ?S" "?R \<inter> ?S = {}"  using p by (auto simp: poly_roots_finite)   
  show "a \<le> b \<Longrightarrow> cr a b = (card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0})"
    "nr a = card {x. x \<le> a \<and> poly p x = 0}" using cr unfolding arg_cong[OF id, of card] card_Un_disjoint[OF RS] 
    count_roots_interval_def count_roots_between_correct[symmetric]
    count_roots_below_correct[symmetric] count_roots_below_def
    count_roots_between_def Let_def using p by auto
qed

definition root_cond :: "rat poly \<times> rat \<times> rat \<Rightarrow> real \<Rightarrow> bool" where
  "root_cond plr x = (case plr of (p,l,r) \<Rightarrow> of_rat l \<le> x \<and> x \<le> of_rat r \<and> rpoly p x = 0)"

definition root_info_cond :: "root_info \<Rightarrow> rat poly \<Rightarrow> bool" where
  "root_info_cond ri p \<equiv> (\<forall> a b. a \<le> b \<longrightarrow> root_info.l_r ri a b = card {x. root_cond (p,a,b) x})
    \<and> (\<forall> a. root_info.inf_r ri a = card {x. x \<le> real_of_rat a \<and> rpoly p x = 0})"

lemma root_info_condD: "root_info_cond ri p \<Longrightarrow> a \<le> b \<Longrightarrow> root_info.l_r ri a b = card {x. root_cond (p,a,b) x}"
  "root_info_cond ri p \<Longrightarrow> root_info.inf_r ri a = card {x. x \<le> real_of_rat a \<and> rpoly p x = 0}"
  unfolding root_info_cond_def by auto

definition count_roots_interval_rat :: "rat poly \<Rightarrow> root_info" where
  [code del]: "count_roots_interval_rat  p = (let pp = real_of_rat_poly p;
    (cr,nr) = count_roots_interval pp
  in Root_Info (\<lambda> a b. cr (of_rat a) (of_rat b)) (\<lambda> a. nr (of_rat a)))"

definition count_roots_rat :: "rat poly \<Rightarrow> nat" where
  [code del]: "count_roots_rat  p = (count_roots (real_of_rat_poly p))"

lemma count_roots_interval_rat: assumes p: "p \<noteq> 0" 
  shows "root_info_cond (count_roots_interval_rat p) p"
proof -  
  let ?p = "real_of_rat_poly p"
  let ?r = real_of_rat
  let ?ri = "count_roots_interval_rat p"
  from p have p: "?p \<noteq> 0" using real_of_rat_poly_0 by auto
  obtain cr nr where cr: "count_roots_interval ?p = (cr,nr)" by force
  have "?ri = Root_Info (\<lambda>a b. cr (?r a) (?r b)) (\<lambda>a. nr (?r a))"
    unfolding count_roots_interval_rat_def Let_def cr by auto
  hence id: "root_info.l_r ?ri = (\<lambda>a b. cr (?r a) (?r b))" "root_info.inf_r ?ri = (\<lambda>a. nr (?r a))"
    by auto
  note cr = count_roots_interval[OF p cr]
  show ?thesis unfolding root_info_cond_def id
  proof (intro conjI impI allI)
    fix a
    show "nr (?r a) = card {x. x \<le> (?r a) \<and> rpoly p x = 0}"
      using cr(2)[of "?r a"] by (simp add: poly_real_of_rat_poly)
  next
    fix a b :: rat
    assume ab: "a \<le> b"
    from ab have ab: "?r a \<le> ?r b" by (simp add: of_rat_less_eq)
    from cr(1)[OF this] show "cr (?r a) (?r b) = card (Collect (root_cond (p, a, b)))"
      unfolding root_cond_def[abs_def] split 
      poly_real_of_rat_poly by simp
  qed
qed

lemma count_roots_rat: "count_roots_rat p = card {x. rpoly p x = (0 :: real)}"
  unfolding count_roots_rat_def count_roots_correct poly_real_of_rat_poly ..

subsection \<open>Implementing Sturm on Rational Polynomials\<close>

function sturm_aux_rat where
"sturm_aux_rat (p :: rat poly) q =
    (if degree q = 0 then [p,q] else p # sturm_aux_rat q (-(p mod q)))"
  by (pat_completeness, simp_all)
termination by (relation "measure (degree \<circ> snd)",
                simp_all add: o_def degree_mod_less')

lemma sturm_aux_rat: "sturm_aux (real_of_rat_poly p) (real_of_rat_poly q) = 
  map real_of_rat_poly (sturm_aux_rat p q)"
proof (induct p q rule: sturm_aux_rat.induct)
  case (1 p q)
  note deg = rpoly.degree_map_poly
  show ?case 
    unfolding sturm_aux.simps[of "real_of_rat_poly p"] sturm_aux_rat.simps[of p]
    unfolding rpoly.degree_map_poly rpoly.map_poly_mod[symmetric] rpoly.map_poly_uminus[symmetric]
    using 1 by (cases "degree q = 0", auto)
qed

lemma pderiv_rat: "pderiv (real_of_rat_poly p) = real_of_rat_poly (pderiv p)"
proof (induct p rule: pderiv.induct)
  case (1 a p)
  show ?case 
    unfolding pderiv.simps
      rpoly.map_poly_pCons_hom
      rpoly.map_poly_0_iff using 1 by (cases "p = 0", auto)
qed

definition sturm_rat where "sturm_rat p = sturm_aux_rat p (pderiv p)"

lemma sturm_rat: "sturm (real_of_rat_poly p) = map real_of_rat_poly (sturm_rat p)"
  unfolding sturm_rat_def sturm_def pderiv_rat sturm_aux_rat ..

definition sturm_squarefree_rat where
  "sturm_squarefree_rat p = sturm_rat (p div (gcd_rat_poly p (pderiv p)))"

lemma sturm_squarefree_rat: "sturm_squarefree (real_of_rat_poly p) 
  = map real_of_rat_poly (sturm_squarefree_rat p)"
  unfolding sturm_squarefree_rat_def sturm_squarefree_def gcd_rat_poly
    rpoly.map_poly_gcd[symmetric] rpoly.map_poly_div[symmetric] pderiv_rat sturm_rat ..

definition poly_inf_rat :: "rat poly \<Rightarrow> rat" where 
  "poly_inf_rat p \<equiv> sgn (coeff p (degree p))"

definition poly_neg_inf_rat :: "rat poly \<Rightarrow> rat" where 
  "poly_neg_inf_rat p \<equiv> if even (degree p) then sgn (coeff p (degree p))
                                       else -sgn (coeff p (degree p))"

lemma poly_inf_rat: "poly_inf (real_of_rat_poly p) = real_of_rat (poly_inf_rat p)"
  unfolding poly_inf_def poly_inf_rat_def rpoly.degree_map_poly rpoly.coeff_map_poly_hom
    real_of_rat_sgn by simp

lemma poly_neg_inf_rat: "poly_neg_inf (real_of_rat_poly p) = real_of_rat (poly_neg_inf_rat p)"
  unfolding poly_neg_inf_def poly_neg_inf_rat_def rpoly.degree_map_poly rpoly.coeff_map_poly_hom
    real_of_rat_sgn by simp

definition sign_changes_rat where
"sign_changes_rat ps (x::rat) =
    length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map (\<lambda>p. sgn (poly p x)) ps))) - 1"

definition sign_changes_inf_rat where
  "sign_changes_inf_rat ps = 
    length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map poly_inf_rat ps))) - 1"

definition sign_changes_neg_inf_rat where
  "sign_changes_neg_inf_rat ps = 
      length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map poly_neg_inf_rat ps))) - 1"

lemma real_of_rat_list_neq: "list_neq (map real_of_rat xs) 0 
  = map real_of_rat (list_neq xs 0)"
  by (induct xs, auto)

lemma real_of_rat_remdups_adj: "remdups_adj (map real_of_rat xs) = map real_of_rat (remdups_adj xs)"
  by (induct xs rule: remdups_adj.induct, auto)

lemma sign_changes_rat: "sign_changes (map real_of_rat_poly ps) (real_of_rat x)
  = sign_changes_rat ps x" (is "?l = ?r")
proof - 
  def xs \<equiv> "list_neq (map (\<lambda>p. sgn (poly p x)) ps) 0"
  have "?l = length (remdups_adj (list_neq (map real_of_rat (map (\<lambda>xa.  (sgn (poly xa x))) ps)) 0)) - 1"
    unfolding sign_changes_def
    unfolding map_map o_def real_of_rat_sgn poly_real_of_rat_poly rpoly.eval_poly_poly ..
  also have "\<dots> = ?r" unfolding sign_changes_rat_def real_of_rat_list_neq 
    unfolding real_of_rat_remdups_adj by simp
  finally show ?thesis .
qed

lemma sign_changes_neg_inf_rat: "sign_changes_neg_inf (map real_of_rat_poly ps)
  =  sign_changes_neg_inf_rat ps" (is "?l = ?r")
proof - 
  have "?l = length (remdups_adj (list_neq (map real_of_rat (map poly_neg_inf_rat ps)) 0)) - 1"
    unfolding sign_changes_neg_inf_def
    unfolding map_map o_def real_of_rat_sgn poly_real_of_rat_poly rpoly.eval_poly_poly 
      poly_neg_inf_rat ..
  also have "\<dots> = ?r" unfolding sign_changes_neg_inf_rat_def real_of_rat_list_neq 
    unfolding real_of_rat_remdups_adj by simp
  finally show ?thesis .
qed

lemma sign_changes_inf_rat: "sign_changes_inf (map real_of_rat_poly ps)
  =  sign_changes_inf_rat ps" (is "?l = ?r")
proof - 
  have "?l = length (remdups_adj (list_neq (map real_of_rat (map poly_inf_rat ps)) 0)) - 1"
    unfolding sign_changes_inf_def
    unfolding map_map o_def real_of_rat_sgn poly_real_of_rat_poly rpoly.eval_poly_poly 
      poly_inf_rat ..
  also have "\<dots> = ?r" unfolding sign_changes_inf_rat_def real_of_rat_list_neq 
    unfolding real_of_rat_remdups_adj by simp
  finally show ?thesis .
qed

lemma count_roots_interval_rat_code[code]:
  "count_roots_interval_rat p = (let ps = sturm_squarefree_rat p
    in Root_Info 
      (\<lambda> a b. sign_changes_rat ps a - sign_changes_rat ps b + (if poly p a = 0 then 1 else 0))
      (\<lambda> a. sign_changes_neg_inf_rat ps - sign_changes_rat ps a))"
  unfolding count_roots_interval_rat_def Let_def count_roots_interval_def split
    sturm_squarefree_rat sign_changes_rat poly_real_of_rat_poly rpoly.eval_poly_poly rpoly.hom_0_iff
    sign_changes_neg_inf_rat
    by simp

lemma count_roots_rat_code[code]:
  "count_roots_rat p = (if real_of_rat_poly p = 0 then 0 else let ps = sturm_squarefree_rat p
    in sign_changes_neg_inf_rat ps - sign_changes_inf_rat ps)"
  unfolding count_roots_rat_def Let_def sturm_squarefree_rat count_roots_def
    rpoly.eval_poly_poly rpoly.hom_0_iff sign_changes_neg_inf_rat sign_changes_inf_rat
    by simp

end