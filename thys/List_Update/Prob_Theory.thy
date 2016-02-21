(*  Title:       Definition of Expectation and Distribution of uniformly distributed bit vectors
    Author:      Max Haslbeck
*)
theory Prob_Theory
imports Probability 
begin


adhoc_overloading Monad_Syntax.bind bind_pmf


lemma integral_map_pmf[simp]:
  fixes f::"real \<Rightarrow> real" 
  shows "(\<integral>x. f x \<partial>(map_pmf g M)) = (\<integral>x. f (g x) \<partial>M)"
   unfolding map_pmf_rep_eq
 using integral_distr[of g "(measure_pmf M)" "(count_space UNIV)" f] by auto

subsection "function @{text E}"


definition E :: "real pmf \<Rightarrow> real"  where
  "E M = (\<integral>x. x \<partial> measure_pmf M)"


translations
  "\<integral> x. f \<partial>M" <= "CONST lebesgue_integral M (\<lambda>x. f)"

notation (latex output) E  ("E[_]" [1] 100)

lemma E_const[simp]: "E (return_pmf a) = a"
unfolding E_def
unfolding return_pmf.rep_eq
by (simp add: integral_return)

lemma E_null[simp]: "E (return_pmf 0) = 0"
by auto

lemma E_finite_sum: "finite (set_pmf X) \<Longrightarrow> E X = (\<Sum>x\<in>(set_pmf X). x * pmf X x)" 
unfolding E_def apply(rule integral_measure_pmf) by (auto)


lemma E_of_const: "E(map_pmf (\<lambda>x. y) (X::real pmf)) = y" by auto 

lemma E_nonneg: 
  shows "(\<forall>x\<in>set_pmf X. 0\<le> x) \<Longrightarrow> 0 \<le> E X"         
unfolding E_def
using integral_nonneg by (simp add: AE_measure_pmf_iff integral_nonneg_AE)

lemma E_nonneg_fun: fixes f::"'a\<Rightarrow>real"
  shows "(\<forall>x\<in>set_pmf X. 0\<le>f x) \<Longrightarrow> 0 \<le> E (map_pmf f X)"   
using E_nonneg by auto
 
 
lemma E_cong:
  fixes f::"'a \<Rightarrow> real"
  shows "finite (set_pmf X) \<Longrightarrow> (\<forall>x\<in> set_pmf X. (f x) = (u x)) \<Longrightarrow> E (map_pmf f X) = E (map_pmf u X)"
unfolding E_def integral_map_pmf apply(rule integral_cong_AE)
apply(simp add: integrable_measure_pmf_finite)+
by (simp add: AE_measure_pmf_iff)
 
lemma E_mono3:
  fixes f::"'a \<Rightarrow> real"
  shows " integrable (measure_pmf X) f \<Longrightarrow>  integrable (measure_pmf X) u \<Longrightarrow> (\<forall>x\<in> set_pmf X. (f x) \<le> (u x)) \<Longrightarrow> E (map_pmf f X) \<le> E (map_pmf u X)"
unfolding E_def integral_map_pmf apply(rule integral_mono_AE)
by (auto simp add: AE_measure_pmf_iff)

lemma E_mono2:
  fixes f::"'a \<Rightarrow> real"
  shows "finite (set_pmf X) \<Longrightarrow> (\<forall>x\<in> set_pmf X. (f x) \<le> (u x)) \<Longrightarrow> E (map_pmf f X) \<le> E (map_pmf u X)"
unfolding E_def integral_map_pmf apply(rule integral_mono_AE)
apply(simp add: integrable_measure_pmf_finite)+
by (simp add: AE_measure_pmf_iff)

lemma E_linear_diff2: "finite (set_pmf A) \<Longrightarrow> E (map_pmf f A) - E (map_pmf g A) = E (map_pmf (\<lambda>x. (f x) - (g x)) A)"
unfolding E_def integral_map_pmf apply(rule integral_diff[of "measure_pmf A" f g, symmetric])
 by (simp_all add: integrable_measure_pmf_finite)

lemma E_linear_plus2: "finite (set_pmf A) \<Longrightarrow> E (map_pmf f A) + E (map_pmf g A) = E (map_pmf (\<lambda>x. (f x) + (g x)) A)"
unfolding E_def integral_map_pmf apply(rule integral_add[of "measure_pmf A" f g, symmetric])
 by (simp_all add: integrable_measure_pmf_finite)

lemma E_linear_setsum2: "finite (set_pmf D) \<Longrightarrow> E(map_pmf (\<lambda>x. (\<Sum>i<up. f i x)) D)
      = (\<Sum>i<(up::nat). E(map_pmf (f i) D))"
unfolding E_def integral_map_pmf apply(rule integral_setsum) by (simp add: integrable_measure_pmf_finite)

lemma E_linear_setsum_allg: "finite (set_pmf D) \<Longrightarrow> E(map_pmf (\<lambda>x. (\<Sum>i\<in> A. f i x)) D)
      = (\<Sum>i\<in> (A::'a set). E(map_pmf (f i) D))"
unfolding E_def integral_map_pmf apply(rule integral_setsum) by (simp add: integrable_measure_pmf_finite)



lemma E_finite_sum_fun: "finite (set_pmf X) \<Longrightarrow> 
    E (map_pmf f X) = (\<Sum>x\<in>set_pmf X. f x * pmf X x)"
proof -
  assume finite: "finite (set_pmf X)"
  have "E (map_pmf f X) = (\<integral>x. f x \<partial>measure_pmf X)"
      unfolding E_def by auto
  also have "\<dots> = (\<Sum>x\<in>set_pmf X. f x * pmf X x)"
    apply(rule integral_measure_pmf) by(auto simp add: finite)
  finally show ?thesis .
qed  

lemma E_bernoulli: "0\<le>p \<Longrightarrow> p\<le>1 \<Longrightarrow> 
        E (map_pmf f (bernoulli_pmf p)) = p*(f True) + (1-p)*(f False)"
unfolding E_def by (auto) 


subsection "function @{text bv}"

  fun bv:: "nat \<Rightarrow> bool list pmf" where
  "bv 0 = return_pmf []"
| "bv (Suc n) =  do {
                    (xs::bool list) \<leftarrow> bv n;
                    (x::bool) \<leftarrow> (bernoulli_pmf 0.5);
                    return_pmf (x#xs)
                  }"

lemma bv_finite: "finite (bv n)"
by (induct  n) auto

lemma len_bv_n: "\<forall>xs \<in> set_pmf (bv n). length xs = n"
apply(induct n) by auto

lemma bv_set: "set_pmf (bv n) = {x::bool list. length x = n}"
proof (induct n) 
  case (Suc n)
  then have "set_pmf (bv (Suc n)) = (\<Union>x\<in>{x. length x = n}. {True # x, False # x})"
    by(simp add: set_pmf_bernoulli UNIV_bool)
  also have "\<dots> = {x#xs| x xs. length xs = n}" by auto
  also have "\<dots> = {x. length x = Suc n} " using Suc_length_conv by fastforce
  finally show ?case .
qed (simp)

lemma len_not_in_bv: "length xs  \<noteq> n \<Longrightarrow> xs \<notin> set_pmf (bv n)"
by(auto simp: len_bv_n)

lemma not_n_bv_0: "length xs \<noteq> n \<Longrightarrow> pmf (bv n) xs = 0"
by (simp add: len_not_in_bv pmf_eq_0_set_pmf)

lemma bv_comp_bernoulli: "n < l
        \<Longrightarrow> map_pmf (\<lambda>y. y!n) (bv l) = bernoulli_pmf (5 / 10)"
proof (induct n arbitrary: l)
  fix l::nat
  assume "0 < l"
  then obtain m where "l = Suc m" by (metis Suc_pred)
  then have "bv l = bind_pmf (bv m) (\<lambda>xs. bind_pmf (bernoulli_pmf (5 / 10)) (\<lambda>x. return_pmf (x # xs)))" by auto
  then have "map_pmf (\<lambda>y. y!0) (bv l) 
          = map_pmf (\<lambda>y. y!0) (bind_pmf (bv m) (\<lambda>xs. bind_pmf (bernoulli_pmf (5 / 10)) (\<lambda>x. return_pmf (x # xs))))" by auto
  also     
  have "\<dots> =  (bind_pmf (bv m) (\<lambda>t. bind_pmf (bernoulli_pmf (5 / 10)) (\<lambda>x. map_pmf (\<lambda>y. y!0) (return_pmf (x # t)))))" by (auto simp: map_bind_pmf)
  also     
  have "\<dots> =  (bind_pmf (bv m) (\<lambda>t. bind_pmf (bernoulli_pmf (5 / 10)) (\<lambda>x. (return_pmf x))))" by auto
  also     
  have "\<dots> =  (bind_pmf (bv m) (\<lambda>t. (bernoulli_pmf (5 / 10))))" by (auto simp: bind_return_pmf')
  also     
  have "\<dots> =  bernoulli_pmf (5 / 10)" by auto
  finally show "map_pmf (\<lambda>y. y ! 0) (bv l) = bernoulli_pmf (5 / 10)" .
next      
  fix n l::nat
  assume iH: "(\<And>l. n < l \<Longrightarrow> map_pmf (\<lambda>y. y ! n) (bv l) = bernoulli_pmf (5 / 10))"
  assume snl: "Suc n < l"
  from snl have "0 < l" by auto
  then obtain m where lsm: "l = Suc m" by (metis Suc_pred)
  with snl have nltm: "n < m" by auto

  from lsm  have "map_pmf (\<lambda>y. y ! Suc n) (bv l)
      = map_pmf (\<lambda>y. y ! Suc n) (bind_pmf (bv m) (\<lambda>xs. bind_pmf (bernoulli_pmf (5 / 10)) (\<lambda>x. return_pmf (x # xs))))" by auto
  also 
  have "\<dots> = (bind_pmf (bv m) (\<lambda>t. bind_pmf (bernoulli_pmf (5 / 10)) (\<lambda>x. map_pmf (\<lambda>y. y! Suc n) (return_pmf (x # t)))))" by (auto simp add: map_bind_pmf)
  also 
  have "\<dots> = (bind_pmf (bv m) (\<lambda>t. bind_pmf (bernoulli_pmf (5 / 10)) (\<lambda>x. (return_pmf (t!n)))))" by auto
  also 
  have "\<dots> = (bind_pmf (bv m) (\<lambda>t. return_pmf (t!n)))" by auto
  also
  have "\<dots> =  map_pmf (\<lambda>x. x!n) (bind_pmf (bv m) (\<lambda>t. (return_pmf t)))" by (auto simp: map_bind_pmf)
  also
  have "\<dots> =  map_pmf (\<lambda>x. x!n) (bv m)" by (auto simp: bind_return_pmf')
  also
  have "\<dots> = bernoulli_pmf (5 / 10)" by (auto simp add: iH[of m, OF nltm])
  finally show "map_pmf (\<lambda>y. y ! Suc n) (bv l) = bernoulli_pmf (5 / 10)" .
qed

lemma pmf_2elemlist: "pmf (bv (Suc 0)) ([x]) = pmf (bv 0) [] * pmf (bernoulli_pmf (5 / 10)) x"
  unfolding bv.simps(2)[where n=0]
  unfolding pmf_bind pmf_return
  apply (subst integral_measure_pmf[where A="{[]}"])
  apply (auto) by (cases x) auto

lemma pmf_moreelemlist: "pmf (bv (Suc n)) (x#xs) = pmf (bv n) xs * pmf (bernoulli_pmf (5 / 10)) x"
  unfolding bv.simps(2)
  unfolding pmf_bind pmf_return
  apply (subst integral_measure_pmf[where A="{xs}"])
  apply auto apply (cases x) apply(auto) 
apply (meson indicator_simps(2) list.inject singletonD)
apply (meson indicator_simps(2) list.inject singletonD)
apply (cases x) by(auto) 

lemma list_pmf: "length xs = n \<Longrightarrow> pmf (bv n) xs = (1 / 2)^n"
proof(induct n arbitrary: xs)
  fix xs :: "bool list"
  assume "length xs = 0"
  then have "xs = []" by auto
  then show "pmf (bv 0) xs = (1 / 2) ^ 0" by(auto)
next 
  fix n
  fix xs :: "bool list"
  assume indh: "(\<And>xs. length xs = n \<Longrightarrow> pmf (bv n) xs = (1 / 2) ^ n)"
  assume ln: "length xs = Suc n"
  then obtain a as where split: "xs = a#as" by (metis Suc_length_conv)
  have "length as = n" using ln split by auto
  with indh have 1: "pmf (bv n) as = (1 / 2) ^ n" by auto
  
  from split pmf_moreelemlist[where n=n and x=a and xs=as] have
    "pmf (bv (Suc n)) xs = pmf (bv n) as * pmf (bernoulli_pmf (5 / 10)) a" by auto
  then have "pmf (bv (Suc n)) xs = (1 / 2) ^ n * 1 / 2" using 1 by auto
  then show "pmf (bv (Suc n)) xs = (1 / 2) ^ Suc n" by auto
qed

lemma bv_0_notlen: "pmf (bv n) xs = 0 \<Longrightarrow> length xs \<noteq> n "
by(auto simp: list_pmf)
 
lemma "length xs > n \<Longrightarrow> pmf (bv n) xs = 0"
apply(induct n arbitrary: xs) apply(simp)
proof -
  fix n
  fix xs :: "bool list"
  assume indh: "(\<And>xs. length xs > n \<Longrightarrow> pmf (bv n) xs = 0)"
  assume ln: "length xs > Suc n"
  then obtain a as where split: "xs = a#as" by (metis Suc_length_conv Suc_lessE)
  have "length as > n" using ln split by auto
  with indh have 1: "pmf (bv n) as = 0" by auto  
  from split pmf_moreelemlist[where n=n and x=a and xs=as] have
    "pmf (bv (Suc n)) xs = pmf (bv n) as * pmf (bernoulli_pmf (5 / 10)) a" by auto
  then have "pmf (bv (Suc n)) xs = 0 * 1 / 2" using 1 by auto
  then show "pmf (bv (Suc n)) xs = 0" by auto
qed

lemma map_hd_list_pmf: "map_pmf hd (bv (Suc n)) = bernoulli_pmf (5 / 10)"
  by (simp add: map_pmf_def bind_assoc_pmf bind_return_pmf bind_return_pmf')

lemma map_tl_list_pmf: "map_pmf tl (bv (Suc n)) = bv n"
  by (simp add: map_pmf_def bind_assoc_pmf bind_return_pmf bind_return_pmf' )



subsection "function @{text flip}"

fun flip :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where
  "flip _ [] = []"
| "flip 0 (x#xs) = (\<not>x)#xs"
| "flip (Suc n) (x#xs) = x#(flip n xs)"

lemma flip_length[simp]: "length (flip i xs) = length xs"
apply(induct xs arbitrary: i) apply(simp) apply(case_tac i) by(simp_all)

lemma flip_out_of_bounds: "y \<ge> length X \<Longrightarrow> flip y X = X"
apply(induct X arbitrary: y)
proof -
  case (Cons X Xs)
  hence "y > 0" by auto
  with Cons obtain y' where y1: "y = Suc y'" and y2: "y' \<ge> length Xs" by (metis Suc_pred' length_Cons not_less_eq_eq)
  then have "flip y (X # Xs) = X#(flip y' Xs)" by auto
  moreover from Cons y2 have "flip y' Xs = Xs" by auto
  ultimately show ?case by auto
qed simp


lemma flip_other: "y < length X \<Longrightarrow> z < length X \<Longrightarrow> z \<noteq> y \<Longrightarrow> flip z X ! y = X ! y"
apply(induct y arbitrary: X z) 
apply(simp) apply (metis flip.elims neq0_conv nth_Cons_0)
proof (case_tac z, goal_cases)
  case (1 y X z)
  then obtain a as where "X=a#as" using length_greater_0_conv by (metis (full_types) flip.elims)
  with 1(5) show ?case by(simp)
next
  case (2 y X z z')
  from 2 have 3: "z' \<noteq> y" by auto
  from 2(2) have "length X > 0" by auto
  then obtain a as where aas: "X = a#as" by (metis (full_types) flip.elims length_greater_0_conv)
  then have a: "flip (Suc z') X ! Suc y = flip z' as ! y"
    and b : "(X ! Suc y) = (as !  y)" by auto
  from 2(2) aas have 1: "y < length as" by auto
  from 2(3,5) aas have f2: "z' < length as" by auto
  note c=2(1)[OF 1 f2 3]

  have "flip z X ! Suc y = flip (Suc z') X ! Suc y" using 2 by auto
  also have "\<dots> = flip z' as ! y" by (rule a)
  also have "\<dots> = as ! y" by (rule c)
  also have "\<dots> = (X ! Suc y)" by (rule b[symmetric])
  finally show "flip z X ! Suc y = (X ! Suc y)" .
qed

lemma flip_itself: "y < length X \<Longrightarrow> flip y X ! y = (\<not> X ! y)"
apply(induct y arbitrary: X) 
apply(simp) apply (metis flip.elims nth_Cons_0 old.nat.distinct(2))
proof -
  fix y
  fix X::"bool list"
  assume iH: "(\<And>X. y < length X \<Longrightarrow> flip y X ! y = (\<not> X ! y))"
  assume len: "Suc y < length X"
  from len have "y < length X" by auto
  from len have "length X > 0" by auto
  then obtain z zs where zzs: "X = z#zs" by (metis (full_types) flip.elims length_greater_0_conv)
  then have a: "flip (Suc y) X ! Suc y = flip y zs ! y"
    and b : "(\<not> X ! Suc y) = (\<not> zs !  y)" by auto
  from len zzs have "y < length zs" by auto
  note c=iH[OF this]
  from a b c show "flip (Suc y) X ! Suc y = (\<not> X ! Suc y)" by auto
qed


lemma flip_twice: "flip i (flip i b) = b"
proof (cases "i < length b")
  case True
  then have A: "i < length (flip i b)" by simp
  show ?thesis apply(simp add: list_eq_iff_nth_eq) apply(clarify)
  proof (goal_cases)
    case (1 j)
    then show ?case
      apply(cases "i=j")
        using flip_itself[OF A] flip_itself[OF True] apply(simp)
        using flip_other True 1 by auto
  qed
qed (simp add: flip_out_of_bounds)
 



lemma flipidiflip: "y < length X \<Longrightarrow> e < length X  \<Longrightarrow> flip e X ! y = (if e=y then ~ (X ! y) else X ! y)"
apply(cases "e=y")
apply(simp add: flip_itself)
by(simp add: flip_other)
   

lemma bernoulli_Not: "map_pmf Not (bernoulli_pmf (1 / 2)) = (bernoulli_pmf (1 / 2))"
apply(rule pmf_eqI)
proof (case_tac i, goal_cases)
  case (1 i)
  then have "pmf (map_pmf Not (bernoulli_pmf (1 / 2))) i =
    pmf (map_pmf Not (bernoulli_pmf (1 / 2))) (Not False)" by auto
  also have "\<dots> = pmf (bernoulli_pmf (1 / 2)) False" apply (rule pmf_map_inj') apply(rule injI) by auto
  also have "\<dots> = pmf (bernoulli_pmf (1 / 2)) i" by auto
  finally show ?case .
next
  case (2 i)
  then have "pmf (map_pmf Not (bernoulli_pmf (1 / 2))) i =
    pmf (map_pmf Not (bernoulli_pmf (1 / 2))) (Not True)" by auto
  also have "\<dots> = pmf (bernoulli_pmf (1 / 2)) True" apply (rule pmf_map_inj') apply(rule injI) by auto
  also have "\<dots> = pmf (bernoulli_pmf (1 / 2)) i" by auto
  finally show ?case .
qed


lemma inv_flip_bv: "map_pmf (flip i) (bv n) = (bv n)"
apply(induct n arbitrary: i) apply(simp)
apply(simp) apply(simp only: map_bind_pmf)
proof (goal_cases)
   case (1 n i)
   have "bind_pmf (bv n) (\<lambda>x. bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. map_pmf (flip i) (return_pmf (xa # x))))
    = bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa .bind_pmf (bv n) (\<lambda>x. map_pmf (flip i) (return_pmf (xa # x))))"
    by(rule bind_commute_pmf) 
   also have "\<dots> = bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa . bind_pmf (bv n) (\<lambda>x. return_pmf (xa # x)))" 
   proof (cases i)
    case 0 
    then have "bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. bind_pmf (bv n) (\<lambda>x. map_pmf (flip i) (return_pmf (xa # x))))
        = bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. bind_pmf (bv n) (\<lambda>x. return_pmf ((\<not> xa) # x)))" by auto
    also have "\<dots>  = bind_pmf (bv n) (\<lambda>x. bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. return_pmf ((\<not> xa) # x)))" 
      by(rule bind_commute_pmf)
    also have "\<dots>
        = bind_pmf (bv n) (\<lambda>x. bind_pmf (map_pmf Not (bernoulli_pmf (1 / 2))) (\<lambda>xa. return_pmf (xa # x)))"
              by(auto simp add: bind_map_pmf)
    also have "\<dots> = bind_pmf (bv n) (\<lambda>x. bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. return_pmf (xa # x)))" by (simp only: bernoulli_Not)
    also have "\<dots> = bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. bind_pmf (bv n) (\<lambda>x. return_pmf (xa # x)))"
      by(rule bind_commute_pmf)
    finally show ?thesis .
   next
    case (Suc i')    
    have "bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. bind_pmf (bv n) (\<lambda>x. map_pmf (flip i) (return_pmf (xa # x))))
        = bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. bind_pmf (bv n) (\<lambda>x. return_pmf (xa # flip i' x)))" unfolding Suc by(simp)
    also have "\<dots> = bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. bind_pmf (map_pmf (flip i') (bv n)) (\<lambda>x. return_pmf (xa # x)))"
        by(auto simp add: bind_map_pmf)
    also have "\<dots> =  bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. bind_pmf (bv n) (\<lambda>x. return_pmf (xa # x)))" 
        using 1[of "i'"] by simp
    finally show ?thesis .
   qed
   also have "\<dots> = bind_pmf (bv n) (\<lambda>x. bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. return_pmf (xa # x)))" 
    by(rule bind_commute_pmf)
   finally show "bind_pmf (bv n) (\<lambda>x. bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. map_pmf (flip i) (return_pmf (xa # x))))
    = bind_pmf (bv n) (\<lambda>x. bind_pmf (bernoulli_pmf (1 / 2)) (\<lambda>xa. return_pmf (xa # x)))" .
qed



subsection "Example for pmf"

definition "twocoins =
                do {
                    x \<leftarrow> (bernoulli_pmf 0.4);
                    y \<leftarrow> (bernoulli_pmf 0.5);
                    return_pmf (x \<or> y)
                  }"
 
lemma experiment0_7: "pmf twocoins True = 0.7"
unfolding twocoins_def
  unfolding pmf_bind pmf_return
  apply (subst integral_measure_pmf[where A="{True, False}"]) 
  by auto 



end
