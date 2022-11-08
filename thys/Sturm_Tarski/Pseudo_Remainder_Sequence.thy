(*
  File:    Pseudo_Remainder_Sequence.thy
  Author:  Wenda Li
*)

section \<open>An implementation for calculating pseudo remainder sequences\<close>

theory Pseudo_Remainder_Sequence
  imports Sturm_Tarski
    "HOL-Computational_Algebra.Computational_Algebra"
    
    (*TODO: we should consider to move this to the standard library*)
    "Polynomial_Interpolation.Ring_Hom_Poly"
begin

subsection \<open>Misc\<close>

function spmods :: "'a::idom poly \<Rightarrow> 'a poly \<Rightarrow> ('a poly) list" where
  "spmods p q= (if p=0 then [] else 
      let 
        m=(if even(degree p+1-degree q) then -1 else -lead_coeff q) 
      in     
        Cons p (spmods q (smult m (pseudo_mod p q))))"
by auto
termination
 apply (relation "measure (\<lambda>(p,q).if p=0 then 0 else if q=0 then 1 else 2+degree q)")
 by (simp_all add: degree_pseudo_mod_less)

declare spmods.simps[simp del]

lemma spmods_0[simp]:
  "spmods 0 q = []"
  "spmods p 0 = (if p=0 then [] else [p])"
by (auto simp:spmods.simps)

lemma spmods_nil_eq:"spmods p q = [] \<longleftrightarrow> (p=0)"
  by (metis list.distinct(1) spmods.elims)

lemma changes_poly_at_alternative: 
  "changes_poly_at ps a= changes (map (\<lambda>p. sign(poly p a)) ps)" 
  "changes_poly_at ps a= changes (map (\<lambda>p. sgn(poly p a)) ps)" 
  unfolding changes_poly_at_def
  subgoal by (subst changes_map_sign_eq) (auto simp add:comp_def) 
  subgoal by (subst changes_map_sgn_eq) (auto simp add:comp_def)
  done

lemma smods_smult_length: 
  assumes "a\<noteq>0" "b\<noteq>0"
  shows "length (smods p q) = length (smods (smult a p) (smult b q))" using assms
proof (induct "smods p q"  arbitrary:p q a b )
  case Nil
  thus ?case by (simp split:if_splits)
next
  case (Cons x xs)
  hence "p\<noteq>0" by auto
  define r where "r\<equiv>- (p mod q)"
  have "smods q r = xs" using Cons.hyps(2) `p\<noteq>0` unfolding r_def by auto
  hence "length (smods q r) = length (smods (smult b q) (smult a r))"
    using Cons.hyps(1)[of q r b a] Cons by auto
  moreover have "smult a p\<noteq>0" using `a\<noteq>0` `p\<noteq>0` by auto
  moreover have "-((smult a p) mod (smult b q)) = (smult a r)" 
    by (simp add: Cons.prems(2) mod_smult_left mod_smult_right r_def)
  ultimately show ?case
    unfolding r_def by auto
qed

lemma smods_smult_nth[rule_format]:
  fixes p q::"real poly"
  assumes "a\<noteq>0" "b\<noteq>0"
  defines "xs\<equiv>smods p q" and "ys\<equiv>smods (smult a p) (smult b q)"
  shows "\<forall>n<length xs. ys!n = (if even n then smult a (xs!n)  else smult b (xs!n))" using assms
proof (induct "smods p q"  arbitrary:p q a b xs ys)
  case Nil
  thus ?case by (simp split:if_splits)
next
  case (Cons x xs)
  hence "p\<noteq>0" by auto
  define r where "r\<equiv>- (p mod q)"
  have xs:"xs=smods q r" "p#xs=smods p q" using Cons.hyps(2) `p\<noteq>0` unfolding r_def by auto
  define ys where "ys\<equiv>smods (smult b q) (smult a r)"
  have "- ((smult a p) mod (smult b q)) = smult a r"
    by (simp add: Cons.hyps(4) mod_smult_left mod_smult_right r_def)
  hence ys:"smult a p # ys = smods (smult a p) (smult b q)" using `p\<noteq>0` `a\<noteq>0` 
    unfolding ys_def r_def by auto
  have hyps:"\<And>n. n<length xs \<Longrightarrow> ys ! n = (if even n then smult b (xs ! n) else smult a (xs ! n))"
    using Cons.hyps(1)[of q r b a,folded xs ys_def] `a\<noteq>0` `b\<noteq>0` by auto
  thus ?case
    apply (fold xs ys)
    apply auto
    by (case_tac n,auto)+
qed

lemma smods_smult_sgn_map_eq:
  fixes x::real
  assumes "m>0"
  defines "f\<equiv>\<lambda>p. sgn(poly p x)"
  shows "map f (smods p (smult m q)) = map f (smods p q)"
        "map sgn_pos_inf (smods p (smult m q)) = map sgn_pos_inf (smods p q)"
        "map sgn_neg_inf (smods p (smult m q)) = map sgn_neg_inf (smods p q)"
proof -
  define xs ys where "xs\<equiv>smods p q" and "ys\<equiv>smods p (smult m q)" 
  have "m\<noteq>0" using `m>0` by simp
  have len_eq:"length xs =length ys"
    using smods_smult_length[of 1 m] `m>0` unfolding xs_def ys_def by auto
  moreover have 
    "(map f xs) ! i = (map f ys) ! i"
    "(map sgn_pos_inf xs) ! i = (map sgn_pos_inf ys) ! i"
    "(map sgn_neg_inf xs) ! i = (map sgn_neg_inf ys) ! i"
     when "i<length xs" for i
  proof -
    note nth_eq=smods_smult_nth[OF one_neq_zero `m\<noteq>0`,of _ p q,unfolded smult_1_left, 
        folded xs_def ys_def,OF `i<length xs` ]
    then show "map f xs ! i = map f ys ! i"
          "(map sgn_pos_inf xs) ! i = (map sgn_pos_inf ys) ! i"
          "(map sgn_neg_inf xs) ! i = (map sgn_neg_inf ys) ! i"
      using that
      unfolding f_def using len_eq `m>0`
      by (auto simp add:sgn_mult sgn_pos_inf_def sgn_neg_inf_def lead_coeff_smult)  
  qed
  ultimately show "map f (smods p (smult m q)) = map f (smods p q)"
    "map sgn_pos_inf (smods p (smult m q)) = map sgn_pos_inf (smods p q)"
    "map sgn_neg_inf (smods p (smult m q)) = map sgn_neg_inf (smods p q)"
    apply (fold xs_def ys_def)
    by (auto intro: nth_equalityI)
qed

lemma changes_poly_at_smods_smult:
  assumes "m>0"  
  shows "changes_poly_at (smods p (smult m q)) x =changes_poly_at (smods p q) x "
  using smods_smult_sgn_map_eq[OF `m>0`]
  by (metis changes_poly_at_alternative(2))

lemma spmods_smods_sgn_map_eq:
  fixes p q::"real poly" and x::real
  defines "f\<equiv>\<lambda>p. sgn (poly p x)"
  shows "map f (smods p q) = map f (spmods p q)" 
        "map sgn_pos_inf (smods p q) = map sgn_pos_inf (spmods p q)"
        "map sgn_neg_inf (smods p q) = map sgn_neg_inf (spmods p q)"
proof (induct "spmods p q" arbitrary:p q)
  case Nil
  hence "p=0" using spmods_nil_eq by metis
  thus "map f (smods p q) = map f (spmods p q)" 
       "map sgn_pos_inf (smods p q) = map sgn_pos_inf (spmods p q)"
       "map sgn_neg_inf (smods p q) = map sgn_neg_inf (spmods p q)"
    by auto
next
  case (Cons p' xs)
  hence "p\<noteq>0" by auto
  define r where "r\<equiv>- (p mod q)"
  define exp where " exp\<equiv>degree p +1 - degree q"
  define m where "m\<equiv>(if even exp then 1 else lead_coeff q) 
      * (lead_coeff q ^ exp)"
  have xs1:"p#xs=spmods p q"  
    by (metis (no_types) Cons.hyps(4) list.distinct(1) list.inject  spmods.simps)
  have xs2:"xs=spmods q (smult m r)" when "q\<noteq>0" 
  proof -
    define m' where  "m'\<equiv>if even exp then - 1 else - lead_coeff q"
    have "smult m' (pseudo_mod p q) = smult m r" 
      unfolding m_def m'_def r_def 
      apply (subst pseudo_mod_mod[symmetric])
      using that exp_def by auto    
    thus ?thesis using `p\<noteq>0` xs1 unfolding r_def 
      by (simp add:spmods.simps[of p q,folded exp_def, folded m'_def] del:spmods.simps)
  qed
  define ys where "ys\<equiv>smods q r"
  have ys:"p#ys=smods p q" using `p\<noteq>0` unfolding ys_def r_def by auto
  have qm:"q\<noteq>0 \<Longrightarrow> m>0" 
    using `p\<noteq>0` unfolding m_def
    apply auto  
    subgoal by (simp add: zero_less_power_eq)
    subgoal using zero_less_power_eq by fastforce
    done
  show "map f (smods p q) = map f (spmods p q)"
  proof (cases "q\<noteq>0")
    case True
    then have "map f (spmods q (smult m r)) = map f (smods q r)"
      using smods_smult_sgn_map_eq(1)[of m x q r,folded f_def] qm 
        Cons.hyps(1)[OF xs2,folded f_def] 
      by simp  
    thus ?thesis
      apply (fold xs1 xs2[OF True] ys ys_def)
      by auto
  next
    case False
    thus ?thesis by auto
  qed
  show "map sgn_pos_inf (smods p q) = map sgn_pos_inf (spmods p q)"
  proof (cases "q\<noteq>0")
    case True
    then have "map sgn_pos_inf (spmods q (smult m r)) = map sgn_pos_inf (smods q r)"
      using Cons.hyps(2)[OF xs2,folded f_def] qm[OF True] 
        smods_smult_sgn_map_eq(2)[of m  q r,folded f_def] by auto
    thus ?thesis
      apply (fold xs1 xs2[OF True] ys ys_def)
      by (simp add:f_def)
  next
    case False
    thus ?thesis by auto
  qed 
  show "map sgn_neg_inf (smods p q) = map sgn_neg_inf (spmods p q)"
  proof (cases "q\<noteq>0")
    case True
    then have "map sgn_neg_inf (spmods q (smult m r)) = map sgn_neg_inf (smods q r)"
      using Cons.hyps(3)[OF xs2,folded f_def] qm[OF True] 
        smods_smult_sgn_map_eq(3)[of m  q r,folded f_def] by auto
    thus ?thesis
      apply (fold xs1 xs2[OF True] ys ys_def)  
      by (simp add:f_def)
  next
    case False
    thus ?thesis by auto
  qed 
qed

subsection \<open>Converting @{typ "rat poly"} to @{typ "int poly"} by clearing the denominators\<close>

definition int_of_rat::"rat \<Rightarrow> int" where
  "int_of_rat = inv of_int"

lemma of_rat_inj[simp]: "inj of_rat"
by (simp add: linorder_injI)

lemma (in ring_char_0) of_int_inj[simp]: "inj of_int"
  by (simp add: inj_on_def)

lemma int_of_rat_id: "int_of_rat o of_int = id" 
  unfolding int_of_rat_def
  by auto

lemma int_of_rat_0[simp]:"int_of_rat 0 = 0" 
  by (metis id_apply int_of_rat_id o_def of_int_0)

lemma int_of_rat_inv:"r\<in>\<int> \<Longrightarrow> of_int (int_of_rat r) = r"
unfolding int_of_rat_def
by (simp add: Ints_def f_inv_into_f)

lemma int_of_rat_0_iff:"x\<in>\<int> \<Longrightarrow> int_of_rat x = 0 \<longleftrightarrow> x = 0" 
using int_of_rat_inv by force

lemma [code]:"int_of_rat r = (let (a,b) = quotient_of r in 
          if b=1 then a else Code.abort (STR ''Failed to convert rat to int'') 
          (\<lambda>_. int_of_rat r))"
  apply (auto simp add:split_beta int_of_rat_def)
  by (metis Fract_of_int_quotient inv_f_eq of_int_inj of_int_rat quotient_of_div surjective_pairing)  

definition de_lcm::"rat poly \<Rightarrow> int" where
  "de_lcm p = Lcm(set(map (\<lambda>x. snd (quotient_of x)) (coeffs p)))"

lemma de_lcm_pCons:"de_lcm (pCons a p) = lcm (snd (quotient_of a)) (de_lcm p)"
  unfolding de_lcm_def
  by (cases "a=0\<and>p=0",auto)

lemma de_lcm_0[simp]:"de_lcm 0 = 1" unfolding de_lcm_def by auto

lemma de_lcm_pos[simp]:"de_lcm p > 0"
  apply (induct p)
  apply (auto simp add:de_lcm_pCons)
  by (metis lcm_pos_int less_numeral_extra(3) quotient_of_denom_pos')+  

lemma de_lcm_ints: 
  fixes x::rat
  shows "x\<in>set (coeffs p) \<Longrightarrow> rat_of_int (de_lcm p) * x \<in> \<int>"
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  define a1 a2 where "a1\<equiv>fst (quotient_of a)" and "a2\<equiv>snd (quotient_of a)"
  have a:"a=(rat_of_int a1)/(rat_of_int a2)" and "a2>0" 
    using quotient_of_denom_pos'[of a] unfolding a1_def a2_def
    by (auto simp add: quotient_of_div)
  define mp1 where "mp1\<equiv>a2 div gcd (de_lcm p) a2"
  define mp2 where "mp2\<equiv>de_lcm p div gcd a2 (de_lcm p) "
  have lcm_times1:"lcm a2 (de_lcm p) = de_lcm p * mp1"
    using lcm_altdef_int[of "de_lcm p" a2,folded mp1_def] `a2>0` 
    unfolding mp1_def 
    apply (subst div_mult_swap)
    by (auto simp add: abs_of_pos gcd.commute lcm_altdef_int mult.commute)
  have lcm_times2:"lcm a2 (de_lcm p) = a2 * mp2"
    using lcm_altdef_int[of a2 "de_lcm p",folded mp1_def] `a2>0` 
    unfolding mp2_def by (subst div_mult_swap, auto simp add:abs_of_pos)
  show ?case
  proof (cases "x \<in> set (coeffs p)")    
    case True
    show ?thesis using pCons(2)[OF True]
      by (smt Ints_mult Ints_of_int a2_def de_lcm_pCons lcm_times1 
            mult.assoc mult.commute of_int_mult)
  next
    case False
    then have "x=a" 
      using pCons cCons_not_0_eq coeffs_pCons_eq_cCons insert_iff list.set(2) not_0_cCons_eq 
      by fastforce
    show ?thesis unfolding `x=a` de_lcm_pCons
      apply (fold a2_def,unfold a)
      by (simp add: de_lcm_pCons lcm_times2 of_rat_divide)
  qed
qed

definition clear_de::"rat poly \<Rightarrow> int poly" where
  "clear_de p = (SOME q. (map_poly of_int q) = smult (of_int (de_lcm p)) p)"

lemma clear_de:"of_int_poly(clear_de p) = smult (of_int (de_lcm p)) p"
proof -
  have "\<exists>q. (of_int_poly q) = smult (of_int (de_lcm p)) p" 
  proof (induct p)
    case 0
    show ?case by (metis map_poly_0 smult_0_right)
  next
    case (pCons a p)
    then obtain q1::"int poly" where q1:"of_int_poly q1 = smult (rat_of_int (de_lcm p)) p"
      by auto
    define a1 a2 where "a1\<equiv>fst (quotient_of a)" and "a2\<equiv>snd (quotient_of a)"
    have a:"a=(rat_of_int a1)/ (rat_of_int a2)" and "a2>0" 
        using quotient_of_denom_pos' quotient_of_div 
        unfolding a1_def a2_def by auto 
    define mp1 where "mp1\<equiv>a2 div gcd (de_lcm p) a2"
    define mp2 where "mp2\<equiv>de_lcm p div gcd a2 (de_lcm p) "
    have lcm_times1:"lcm a2 (de_lcm p) = de_lcm p * mp1"
      using lcm_altdef_int[of "de_lcm p" a2,folded mp1_def] `a2>0` 
      unfolding mp1_def 
      by (subst div_mult_swap, auto simp add: abs_of_pos gcd.commute lcm_altdef_int mult.commute)
    have lcm_times2:"lcm a2 (de_lcm p) = a2 * mp2"
      using lcm_altdef_int[of a2 "de_lcm p",folded mp1_def] `a2>0` 
      unfolding mp2_def by (subst div_mult_swap, auto simp add:abs_of_pos)
    define q2 where "q2\<equiv>pCons (mp2 * a1) (smult mp1 q1)"
    have "of_int_poly q2 = smult (rat_of_int (de_lcm (pCons a p))) (pCons a p)" using `a2>0`  
      apply (simp add:de_lcm_pCons )
      apply (fold a2_def)
      apply (unfold a)
      apply (subst lcm_times2,subst lcm_times1)
      by (simp add: Polynomial.map_poly_pCons mult.commute of_int_hom.map_poly_hom_smult q1 q2_def)
    then show ?case by auto
  qed
  then show ?thesis unfolding clear_de_def  by (meson someI_ex)
qed

lemma clear_de_0[simp]:"clear_de 0 = 0" 
  using clear_de[of 0] by auto

lemma [code abstract]: "coeffs (clear_de p) = 
    (let lcm = de_lcm p in map (\<lambda>x. int_of_rat (of_int lcm * x)) (coeffs p))"
proof -
  define mul where "mul\<equiv>rat_of_int (de_lcm p)"
  have "map_poly int_of_rat (of_int_poly q) = q" for q
    apply (subst map_poly_map_poly) 
    by (auto simp add:int_of_rat_id)
  then have clear_eq:"clear_de p = map_poly int_of_rat (smult (of_int (de_lcm p)) p)"
    using arg_cong[where f="map_poly int_of_rat",OF clear_de] 
    by auto
  show ?thesis
  proof (cases "p=0")
    case True
    then show ?thesis by auto
  next
    case False
    define g where "g\<equiv>(\<lambda>x. int_of_rat (rat_of_int (de_lcm p) * x))"
    have "de_lcm p \<noteq> 0" using de_lcm_pos by (metis less_irrefl)
    moreover have "last (coeffs p) \<noteq>0" 
      by (simp add: False last_coeffs_eq_coeff_degree)
    have False when asm:"last (map g (coeffs p)) =0" 
    proof -
      have "coeffs p \<noteq>[]" using False by auto
      hence "g (last (coeffs p)) = 0" using asm last_map[of "coeffs p" g] by auto
      hence "last (coeffs p) = 0"
        unfolding g_def using `coeffs p \<noteq>[]` `de_lcm p \<noteq> 0`
        apply (subst (asm) int_of_rat_0_iff)
        by (auto intro!: de_lcm_ints )
      thus False using `last (coeffs p) \<noteq>0` by simp
    qed
    ultimately show ?thesis
      apply (auto simp add: coeffs_smult clear_eq comp_def smult_conv_map_poly map_poly_map_poly coeffs_map_poly)  
      apply (fold g_def)
      by (metis False Ring_Hom_Poly.coeffs_map_poly coeffs_eq_Nil last_coeffs_eq_coeff_degree 
          last_map)
    qed
qed


subsection \<open>Sign variations for pseudo-remainder sequences\<close>

locale order_hom =
  fixes hom :: "'a :: ord \<Rightarrow> 'b :: ord"
  assumes hom_less: "x < y \<longleftrightarrow> hom x < hom y"
   and hom_less_eq: "x \<le> y \<longleftrightarrow> hom x \<le> hom y"

locale linordered_idom_hom = order_hom hom + inj_idom_hom hom 
  for hom :: "'a :: linordered_idom \<Rightarrow> 'b :: linordered_idom" 
begin

lemma sgn_sign:"sgn (hom x) = of_int (sign x)"
  by (simp add: sign_def hom_less sgn_if)

end
             
locale hom_pseudo_smods= comm_semiring_hom hom 
    + r1:linordered_idom_hom R\<^sub>1 + r2:linordered_idom_hom R\<^sub>2
  for hom::"'a::linordered_idom \<Rightarrow> 'b::{comm_semiring_1,linordered_idom}"
    and R\<^sub>1::"'a \<Rightarrow> real" 
    and R\<^sub>2::"'b \<Rightarrow> real" +
  assumes R_hom:"R\<^sub>1 x = R\<^sub>2 (hom x)"
begin

(*
  hom    R2

'a \<rightarrow> 'b \<rightarrow> real
      rat/float
int
p
      x
*)

lemma map_poly_R_hom_commute:
  "poly (map_poly R\<^sub>1 p) (R\<^sub>2 x) = R\<^sub>2 (poly (map_poly hom p) x)"
apply (induct p)
using r2.hom_add r2.hom_mult R_hom by auto

definition changes_hpoly_at::"'a poly list \<Rightarrow> 'b \<Rightarrow> int" where
  "changes_hpoly_at ps a= changes (map (\<lambda>p. eval_poly hom p a) ps)" 

lemma changes_hpoly_at_Nil[simp]: "changes_hpoly_at [] a = 0"
  unfolding changes_hpoly_at_def by simp

definition changes_itv_spmods:: "'b \<Rightarrow> 'b \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_itv_spmods a b p q= (let ps = spmods p q in 
        changes_hpoly_at ps a - changes_hpoly_at ps b)"

definition changes_gt_spmods:: "'b \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_gt_spmods a p q= (let ps = spmods p q in 
        changes_hpoly_at ps a - changes_poly_pos_inf ps)"

definition changes_le_spmods:: "'b \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> int" where
  "changes_le_spmods b p q= (let ps = spmods p q in 
        changes_poly_neg_inf ps - changes_hpoly_at ps b)"

definition changes_R_spmods:: "'a poly \<Rightarrow> 'a poly \<Rightarrow>  int" where
  "changes_R_spmods p q= (let ps= spmods p q in changes_poly_neg_inf ps 
      - changes_poly_pos_inf ps)"

lemma changes_spmods_smods:
  shows "changes_itv_spmods a b p q 
    = changes_itv_smods (R\<^sub>2 a) (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
  and "changes_R_spmods p q = changes_R_smods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
  and "changes_gt_spmods a p q = changes_gt_smods (R\<^sub>2 a) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
  and "changes_le_spmods b p q = changes_le_smods (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
proof -
  define pp qq where "pp = map_poly R\<^sub>1 p" and "qq = map_poly R\<^sub>1 q"

  have spmods_eq:"spmods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q) = map (map_poly R\<^sub>1) (spmods p q)" 
  proof (induct "spmods p q" arbitrary:p q )
    case Nil
    thus ?case by (metis list.simps(8) map_poly_0 spmods_nil_eq)
  next
    case (Cons p' xs)
    hence "p\<noteq>0" by auto
    define m where "m\<equiv>(if even (degree p + 1 - degree q) then - 1 else - lead_coeff q)"
    define r where "r\<equiv>smult m (pseudo_mod p q)"
    have xs1:"p#xs=spmods p q"  
      by (metis (no_types) Cons.hyps(2) list.distinct(1) list.inject  spmods.simps)
    have xs2:"xs=spmods q r" using xs1 \<open>p\<noteq>0\<close> r_def
      by (auto simp add:spmods.simps[of p q,folded exp_def,folded m_def])
    define ys where "ys\<equiv>spmods (map_poly R\<^sub>1 q) (map_poly R\<^sub>1 r)"
    have ys:"(map_poly R\<^sub>1 p)#ys=spmods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)" 
      using \<open>p\<noteq>0\<close> unfolding ys_def r_def 
      apply (subst (2) spmods.simps)
      unfolding m_def by (auto simp:r1.pseudo_mod_hom hom_distribs)
    show ?case using Cons.hyps(1)[OF xs2] 
      apply (fold xs1 xs2 ys ys_def)
      by auto
  qed

  have changes_eq_at:"changes_poly_at (smods pp qq) (R\<^sub>2 x) = changes_hpoly_at (spmods p q) x" 
    (is "?L=?R")
    for x
  proof -
    define ff where "ff = (\<lambda>p. sgn (poly p (R\<^sub>2 x)))"
    have "?L = changes (map ff (smods pp qq))"  
      using changes_poly_at_alternative unfolding ff_def by blast
    also have "... = changes (map ff (spmods pp qq))" 
      unfolding ff_def using spmods_smods_sgn_map_eq by simp
    also have "... = changes (map ff (map (map_poly R\<^sub>1) (spmods p q)))" 
      unfolding pp_def qq_def using spmods_eq by simp
    also have "... = ?R"
    proof -
      have "ff \<circ> map_poly R\<^sub>1 = sign \<circ> (\<lambda>p. eval_poly hom p x)" 
        unfolding ff_def comp_def
        by (simp add: map_poly_R_hom_commute poly_map_poly_eval_poly  r2.sgn_sign)
      then show ?thesis
        unfolding changes_hpoly_at_def
        apply (subst (2) changes_map_sign_of_int_eq)
        by (simp add:comp_def)
    qed
    finally show ?thesis .
  qed

  have changes_eq_neg_inf:
    "changes_poly_neg_inf (smods pp qq) = changes_poly_neg_inf (spmods p q)"
    (is "?L=?R")
  proof -
    have "?L = changes (map sgn_neg_inf (map (map_poly R\<^sub>1) (spmods p q)))"
      unfolding changes_poly_neg_inf_def spmods_smods_sgn_map_eq
      by (simp add: spmods_eq[folded pp_def qq_def])
    also have "... = changes (map (sgn_neg_inf \<circ> (map_poly R\<^sub>1)) (spmods p q))"
      using map_map by simp
    also have "... = changes (map ((sign:: _ \<Rightarrow> real) \<circ> sgn_neg_inf) (spmods p q))"
    proof - 
      have "(sgn_neg_inf \<circ> (map_poly R\<^sub>1)) = of_int o sign \<circ> sgn_neg_inf" 
        unfolding sgn_neg_inf_def comp_def
        by (auto simp:r1.sgn_sign)
      then show ?thesis by (simp add:comp_def)
    qed
    also have "... = changes (map sgn_neg_inf (spmods p q))"
      apply (subst (2) changes_map_sign_of_int_eq) 
      by (simp add:comp_def)
    also have "... = ?R"
      unfolding changes_poly_neg_inf_def by simp
    finally show ?thesis .
  qed

  have changes_eq_pos_inf:
    "changes_poly_pos_inf (smods pp qq) = changes_poly_pos_inf (spmods p q)"
    (is "?L=?R")
  proof -
    have "?L = changes (map sgn_pos_inf (map (map_poly R\<^sub>1) (spmods p q)))"
      unfolding changes_poly_pos_inf_def spmods_smods_sgn_map_eq
      by (simp add: spmods_eq[folded pp_def qq_def])
    also have "... = changes (map (sgn_pos_inf \<circ> (map_poly R\<^sub>1)) (spmods p q))"
      using map_map by simp
    also have "... = changes (map ((sign:: _ \<Rightarrow> real) \<circ> sgn_pos_inf) (spmods p q))"
    proof - 
      have "(sgn_pos_inf \<circ> (map_poly R\<^sub>1)) = of_int o sign \<circ> sgn_pos_inf" 
        unfolding sgn_pos_inf_def comp_def
        by (auto simp:r1.sgn_sign)
      then show ?thesis by (auto simp:comp_def)
    qed
    also have "... = changes (map sgn_pos_inf (spmods p q))"
      apply (subst (2) changes_map_sign_of_int_eq)
      by (simp add:comp_def)
    also have "... = ?R"
      unfolding changes_poly_pos_inf_def by simp
    finally show ?thesis .
  qed

  show "changes_itv_spmods a b p q 
          = changes_itv_smods (R\<^sub>2 a) (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_itv_spmods_def changes_itv_smods_def
    using changes_eq_at by (simp add: Let_def pp_def qq_def)
  show "changes_R_spmods p q = changes_R_smods (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_R_spmods_def changes_R_smods_def Let_def
    using changes_eq_neg_inf changes_eq_pos_inf 
    by (simp add: pp_def qq_def)
  show "changes_gt_spmods a p q = changes_gt_smods 
                (R\<^sub>2 a) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_gt_spmods_def changes_gt_smods_def Let_def
    using changes_eq_at changes_eq_pos_inf
    by (simp add: pp_def qq_def)
  show "changes_le_spmods b p q = changes_le_smods 
                (R\<^sub>2 b) (map_poly R\<^sub>1 p) (map_poly R\<^sub>1 q)"
    unfolding changes_le_spmods_def changes_le_smods_def Let_def
    using changes_eq_at changes_eq_neg_inf
    by (simp add: pp_def qq_def)
qed

end

end