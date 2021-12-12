(*by Ammer*)
theory VEBT_Space imports VEBT_Definitions Complex_Main
begin

section \<open>Space Complexity and $buildup$ Time Consumption\<close>
subsection \<open>Space Comlexity of valid van Emde Boas Trees\<close>
text \<open>Space Complexity is linear in relation to universe sizes\<close>

context VEBT_internal begin

fun space:: "VEBT \<Rightarrow> nat" where
"space (Leaf a b) = 3"|
"space (Node info deg treeList summary) = 5 + space summary + length treeList + foldr (\<lambda> a b. a+b) (map space treeList) 0"

fun space':: "VEBT \<Rightarrow> nat" where
"space' (Leaf a b) = 4"|
"space' (Node info deg treeList summary) = 6 + space' summary + foldr (\<lambda> a b. a+b) (map space' treeList) 0"

text \<open>Count in reals\<close>

fun cnt:: "VEBT \<Rightarrow> real" where
"cnt (Leaf a b) = 1"|
"cnt (Node info deg treeList summary) = 1 + cnt summary + foldr (\<lambda> a b. a+b) (map cnt treeList) 0"

subsection \<open>Auxiliary Lemmas for List Summation\<close>

lemma list_every_elemnt_bound_sum_bound:"\<forall> x \<in> set xs. f x \<le> bound \<Longrightarrow>  foldr (\<lambda> a b. a+b) (map f xs) i \<le> length xs * bound + i"
  by(induction xs) auto 

lemma list_every_elemnt_bound_sum_bound_real:"\<forall> x \<in> set (xs::'a list). (f::'a\<Rightarrow>real) x \<le> (bound::real) \<Longrightarrow>  foldr (\<lambda> a b. a+b) (map f xs) i \<le> real(length xs) * bound + i"
  apply(induction xs) apply simp
  apply (simp add: algebra_simps)
  done

lemma foldr_one: "d \<le> foldr (+) ys (d::nat)"
  by (induction ys) auto

lemma foldr_zero: "\<forall> i < length xs. xs !  i > 0 \<Longrightarrow>
        foldr (\<lambda> a b. a+b) xs (d::nat) - d  \<ge> length xs"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  hence "\<forall>i<length xs. 0 < xs ! i" 
    by auto
  hence " length xs \<le> foldr (+) xs d - d" using Cons.IH by simp
  have "a \<ge> 1" 
    by (metis gr0_conv_Suc length_Cons less_one local.Cons(2) not_gr0 not_less nth_Cons_0)
  then show ?case
    by (metis Nat.add_diff_assoc \<open>length xs \<le> foldr (+) xs d - d\<close> add_mono_thms_linordered_semiring(1) foldr.simps(2) foldr_one length_Cons o_apply plus_1_eq_Suc)
qed

lemma foldr_mono: "length xs = length ys  \<Longrightarrow>\<forall> i < length xs. xs ! i < ys ! i \<Longrightarrow> c \<le> d \<Longrightarrow>
       foldr (\<lambda> a b. a+b) xs c  + length ys \<le> foldr (\<lambda> a b. a+b) ys (d::nat)"
proof(induction xs arbitrary: d c ys)
  case Nil
  then show ?case using length_0_conv list.size(3)  foldr_one by simp
next
  case (Cons a xs)
  then obtain y ys1 where "ys = y #ys1" 
    by (metis Suc_leI Suc_le_length_iff nth_equalityI)
  hence 0:"length xs = length ys1"
    using Cons.prems(1) by force
  hence 1:"\<forall>i<length xs. xs ! i < ys1 ! i" using Cons.prems(2)
    using \<open>ys = y # ys1\<close> by force
  hence 3: "\<forall>i<length ys1. ys1 ! i > 0"
    by (metis "0" less_nat_zero_code neq0_conv)
  have "foldr (+) (a # xs)c = a +foldr (+) xs (c)" by simp
  have "foldr (+) (ys) d = y +foldr (+) ys1 (d)" 
    by (simp add: \<open>ys = y # ys1\<close>)
  have 2:"a < y" using Cons.prems(2) \<open>ys = y # ys1\<close> 
    by (metis length_Cons nth_Cons_0 zero_less_Suc)
  have 4:"foldr (+) xs c \<le> foldr (+) ys1 d - length ys1" 
    using Cons.IH[of ys1 c d] 0 1 Cons.prems(3) by simp
  have "foldr (+) ys1 d \<ge> length ys1"using foldr_zero[of ys1 d]  3 by simp
  hence "a + foldr (+) xs c < y + foldr (+) ys1 d - length ys1 " using 2 foldr_zero[of ys1 d] 4  by simp
 then show ?case 
   using \<open>ys = y # ys1\<close> by auto
qed 

lemma two_realpow_ge_two :"(n::real)\<ge> 1 \<Longrightarrow> (2::real)^n \<ge> 2"  
  by (metis less_one not_less of_nat_1 of_nat_le_iff of_nat_numeral power_increasing power_one_right zero_neq_numeral)

lemma foldr0: "foldr (+) xs (c+d) = foldr (+) xs (d::real) + c"
  by(induction xs) auto

lemma  f_g_map_foldr_bound:" (\<forall> x \<in> set xs.  f x \<le> c * g x) 
 \<Longrightarrow> foldr (\<lambda> a b. a+b) (map f xs) d \<le> c * foldr (\<lambda> a b. a+b) (map g xs) (0::real) + d" 
  by(induction xs) (auto simp add: algebra_simps)

lemma real_nat_list: "real (foldr (+) ( map f xs) (c::nat)) 
     = foldr (+) (map (\<lambda> x. real(f x))xs) c"
  by(induction xs arbitrary: c) auto

subsection \<open>Actual Space Reasoning\<close>

lemma space_space': "space' t > space t" 
proof(induction t)
  case (Node info deg treeList summary)
  hence "\<forall> i < length treeList . (map space treeList)!i < ( map space' treeList)!i" 
    by simp
  hence 0:"foldr (+) (map space treeList) 0  + length treeList \<le> foldr (+) (map space' treeList) 0 "
    using foldr_mono[of "(map space treeList)"  "(map space' treeList)" 0 0] by simp  
  have 1:"space summary < space' summary" using Node by simp
  hence "foldr (+) (map space treeList) 0 + length treeList + space summary \<le>
         foldr (+) (map space' treeList) 0 + space' summary" using 0 by simp
  then show ?case using space'.simps(2)[of info deg treeList summary] 
       space.simps(2)[of info deg treeList summary] by simp
qed simp

lemma cnt_bound: 
  defines  "c \<equiv> 1.5" 
  shows "invar_vebt t n \<Longrightarrow> cnt t \<le> 2*((2^n - c)::real)"
proof(induction t n rule: invar_vebt.induct)
case (2 treeList n summary m deg)
  hence "\<forall>t\<in>set treeList.  (cnt t) \<le> 2 * (2 ^ n - c)" by simp
  hence " foldr (\<lambda> a b. a+b) (map cnt treeList) 0 \<le> 2^n*2 * ((2^n - c)::real)" 
    using list_every_elemnt_bound_sum_bound_real[of treeList cnt "2*((2^n - c)::real)" 0 ] 2
    by (auto simp add: algebra_simps)
  hence "cnt ( Node None deg treeList summary) \<le> 2*(2^n+1)*(2^n-c) + 1" using 2 
    by(auto simp add: algebra_simps)
  hence "cnt ( Node None deg treeList summary) \<le> 2*(2^(n+n) + (1-c)*2^n - c + 1/2)" 
    by(auto simp add: algebra_simps power_add) 
  moreover have "2*(2^(n+n) + (1-c)*2^n - c + 1/2) \<le> 2*(2^(n+n) + -0.5*1 - 1.5 + 1/2)" 
    by(auto simp add: algebra_simps two_realpow_ge_one c_def)
  moreover hence "2*(2^(n+n) + (1-c)*2^n - c + 1/2) \<le> 2*(2^(n+n)  -  1.5 )" 
    by(auto simp add: algebra_simps power_add)
  ultimately have  "cnt ( Node None deg treeList summary) \<le> 2*(2^(n+n)  -  1.5 )" by simp
  then show ?case  using c_def 2(5) 2(6) by simp
next
  case (3 treeList n summary m deg)
  hence "\<forall>t\<in>set treeList.  (cnt t) \<le> 2 * (2 ^ n - c)" by simp
  hence " foldr (\<lambda> a b. a+b) (map cnt treeList) 0 \<le> 2^(n+1)*2 * ((2^n - c)::real)" 
    using list_every_elemnt_bound_sum_bound_real[of treeList cnt "2*((2^n - c)::real)" 0 ] 3
    by (auto simp add: algebra_simps)
  moreover 
  hence "cnt ( Node None deg treeList summary) \<le> 2*(2^n*2^m - c* 2^(m) + 2^(m) - c  + 1/2)"
    using 3
    by (auto simp add: algebra_simps powr_add)
  moreover have "2*(2^n*2^m - c* 2^(m) + 2^(m) - c  + 1/2) =  2*(2^(n+m) + (1-c)* 2^(m) - c  + 1/2)"
    by (auto simp add: algebra_simps power_add) 
   moreover have " 2*(2^(n+m) + (1-c)* 2^(m) - c  + 1/2) \<le> 2*(2^(n+m) + -0.5*1 - 1.5 + 1/2)" 
     by(auto simp add: algebra_simps two_realpow_ge_one c_def)
  moreover hence "2*(2^(n+m) + (1-c)*2^m - c + 1/2) \<le> 2*(2^(n+m)  -  1.5 )" 
    by(auto simp add: algebra_simps power_add)
  ultimately have  "cnt ( Node None deg treeList summary) \<le> 2*(2^(n+m)  -  1.5 )" by simp
  then show ?case  using c_def 3(5) 3(6) by simp
next
  case (4 treeList n summary m deg mi ma)
hence "\<forall>t\<in>set treeList.  (cnt t) \<le> 2 * (2 ^ n - c)" by simp
  hence " foldr (\<lambda> a b. a+b) (map cnt treeList) 0 \<le> 2^n*2 * ((2^n - c)::real)" 
    using list_every_elemnt_bound_sum_bound_real[of treeList cnt "2*((2^n - c)::real)" 0 ] 4
    by (auto simp add: algebra_simps)
  hence "cnt ( Node (Some (mi, ma)) deg treeList summary) \<le> 2*(2^n+1)*(2^n-c) + 1" using 4 
    by(auto simp add: algebra_simps)
  hence "cnt ( Node None deg treeList summary) \<le> 2*(2^(n+n) + (1-c)*2^n - c + 1/2)" 
    by(auto simp add: algebra_simps power_add) 
  moreover have "2*(2^(n+n) + (1-c)*2^n - c + 1/2) \<le> 2*(2^(n+n) + -0.5*1 - 1.5 + 1/2)" 
    by(auto simp add: algebra_simps two_realpow_ge_one c_def)
  moreover hence "2*(2^(n+n) + (1-c)*2^n - c + 1/2) \<le> 2*(2^(n+n)  -  1.5 )" 
    by(auto simp add: algebra_simps power_add)
  ultimately have  "cnt ( Node None deg treeList summary) \<le> 2*(2^(n+n)  -  1.5 )" by simp
  then show ?case  using c_def 4 by simp
next
  case (5 treeList n summary m deg mi ma)
 hence "\<forall>t\<in>set treeList.  (cnt t) \<le> 2 * (2 ^ n - c)" by simp
  hence " foldr (\<lambda> a b. a+b) (map cnt treeList) 0 \<le> 2^(n+1)*2 * ((2^n - c)::real)" 
    using list_every_elemnt_bound_sum_bound_real[of treeList cnt "2*((2^n - c)::real)" 0 ] 5
    by (auto simp add: algebra_simps)
  moreover 
  hence "cnt ( Node (Some (mi, ma)) deg treeList summary) \<le> 2*(2^n*2^m - c* 2^(m) + 2^(m) - c  + 1/2)"
    using 5
    by (auto simp add: algebra_simps powr_add)
  moreover have "2*(2^n*2^m - c* 2^(m) + 2^(m) - c  + 1/2) =  2*(2^(n+m) + (1-c)* 2^(m) - c  + 1/2)"
    by (auto simp add: algebra_simps power_add) 
   moreover have " 2*(2^(n+m) + (1-c)* 2^(m) - c  + 1/2) \<le> 2*(2^(n+m) + -0.5*1 - 1.5 + 1/2)" 
     by(auto simp add: algebra_simps two_realpow_ge_one c_def)
  moreover hence "2*(2^(n+m) + (1-c)*2^m - c + 1/2) \<le> 2*(2^(n+m)  -  1.5 )" 
    by(auto simp add: algebra_simps power_add)
  ultimately have  "cnt ( Node None deg treeList summary) \<le> 2*(2^(n+m)  -  1.5 )" by simp
  then show ?case  using c_def 5 by simp
qed (simp add: cnt.simps c_def)

theorem cnt_bound': "invar_vebt t n \<Longrightarrow> cnt t \<le> 2 * (2 ^ n - 1)" 
  using cnt_bound by fastforce

lemma space_cnt: "space' t \<le> 6*cnt t" 
proof(induction t)
  case (Node info deg treeList summary)
 hence " \<forall>t\<in>set treeList.  space' t \<le> 6 * cnt t" by blast
  hence " foldr (\<lambda> a b. a+b) (map space' treeList) 0 \<le>
     6 *foldr (\<lambda> a b. a+b) (map cnt treeList) 0"  
    using  f_g_map_foldr_bound[of treeList space' 6 cnt 0]
    by(auto simp add: algebra_simps real_nat_list)
then show ?case
  using Node.IH(2) by force
qed simp

lemma space_2_pow_bound:  assumes "invar_vebt t n " shows "real (space' t) \<le> 12 * (2^n -1)" 
proof-
  have "space' t \<le> 6 * cnt t" 
    using space_cnt[of t] assms by simp
  moreover have "6 * cnt t \<le> 12 * (2^n -1)" 
    using cnt_bound'[of t n]  assms by simp
  ultimately show ?thesis by linarith
qed

lemma space'_bound: assumes "invar_vebt t n" "u = 2^n"
  shows "space' t \<le> 12 * u"
  using  space_2_pow_bound[of t n] 
proof -
have "real u - 1 = real (u - 1)"
by (simp add: assms(2) of_nat_diff)
then show ?thesis
  using \<open>invar_vebt t n \<Longrightarrow> real (space' t) \<le> 12 * (2 ^ n - 1)\<close> assms(1) assms(2) by auto
qed

text \<open>Main Theorem\<close>

theorem space_bound: assumes "invar_vebt t n" "u = 2^n"
  shows "space t \<le> 12 * u"
  by (metis assms(1) assms(2) dual_order.trans less_imp_le_nat space'_bound space_space')

subsection \<open>Complexity of Generation Time \<close>
text \<open>Space complexity is closely related to tree generation time complexity\<close>

text \<open>Time approximation for replicate function. $T_{replicate} \; n \; t \;x$ denotes runnig time of the $n$-times replication of $x$ into a list. 
$t$ models runtime for generation of a single $x$.\<close>

fun T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p::"nat \<Rightarrow> nat" where
"T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p 0 = 3"|
"T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p (Suc 0) = 3"|
"T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p  n = (if even n then 1 + (let half = n div 2 in 
                 9 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p half +  (2^half) * (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p half  + 1))
                else (let half = n div 2 in
                      11 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p (Suc half) +  (2^(Suc half))* (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p half + 1 )))"

fun T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d::"nat \<Rightarrow> nat" where
"T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d 0 = 4"|
"T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc 0) = 4"|
"T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d  n = (if even n then 1 + (let half = n div 2 in 
                 10 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d half +  (2^half) * (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d half))
                else (let half = n div 2 in
                      12 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc half) +  (2^(Suc half))* (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d half)))"

lemma buildup_build_time: "T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p  n < T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d  n"
proof(induction n rule: T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p.induct)
  case (3 va)
  then show ?case
  proof(cases "even (Suc (Suc va))")
    case True
    then show ?thesis 
      apply(subst T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p.simps)
      apply(subst T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d.simps) 
      using True apply simp
      by (smt (z3) "3.IH"(1) Suc_1 True add_mono_thms_linordered_semiring(1) distrib_left div2_Suc_Suc less_mult_imp_div_less linorder_not_le mult.commute mult_numeral_1_right nat_0_less_mult_iff nat_less_le nat_zero_less_power_iff nonzero_mult_div_cancel_left not_less_eq numerals(1) plus_1_eq_Suc zero_le_one)
  next
    case False
    hence *: "(let half = Suc (Suc va) div 2
          in 11 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p (Suc half) + 2 ^ Suc half * (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p half + 1))
           <  (let half = Suc (Suc va) div 2
            in 12 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc half) + 2 ^ Suc half * T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d half)"
      unfolding Let_def
    proof-
      assume "odd (Suc (Suc va))"
    have " 11 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p (Suc (Suc (Suc va) div 2))
          < 12 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc (Suc va) div 2))"
      using "3.IH"(3) False add_less_mono by presburger
    moreover have " 2 ^ Suc (Suc (Suc va) div 2) * (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p (Suc (Suc va) div 2) + 1)
                   \<le> 2 ^ Suc (Suc (Suc va) div 2) * T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2)"
      by (metis "3.IH"(4) False Suc_leI add.commute mult_le_mono2 plus_1_eq_Suc)
    ultimately show " 11 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p (Suc (Suc (Suc va) div 2)) +
                     2 ^ Suc (Suc (Suc va) div 2) * (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p (Suc (Suc va) div 2) + 1)
                     < 12 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc (Suc va) div 2)) +
                       2 ^ Suc (Suc (Suc va) div 2) * T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2)" 
      using add_mono_thms_linordered_field(3) by blast
  qed
    show ?thesis apply(subst T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p.simps)
      apply(subst T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d.simps) 
      using False *
      by simp
  qed
qed simp+
 

lemma listsum_bound: "(\<And> x. x \<in> set xs \<Longrightarrow> f x \<ge> (0::real)) \<Longrightarrow>
        foldr (+) (map f xs) y \<ge> y"
  apply(induction xs arbitrary: y)
  apply simp
  apply(subst list.map(2))
  apply(subst foldr.simps)
  apply (simp add: add_increasing)
  done

lemma cnt_non_neg: "cnt t \<ge> 0"
  by (induction t) (simp add: VEBT_internal.listsum_bound)+

lemma foldr_same: "(\<And> x y. x \<in> set (xs::real list) \<Longrightarrow> y \<in> set xs \<Longrightarrow> x = y) \<Longrightarrow>
                   (\<And> x . (x::real) \<in> set xs \<Longrightarrow> x = (y::real)) \<Longrightarrow> 
                   foldr (\<lambda> (a::real) (b::real). a+b) xs 0 = real (length xs) * y"
  apply(induction xs)
    apply simp
  apply(subst foldr.simps)
  unfolding comp_def
proof -
  fix a :: real and xsa :: "real list"
  assume a1: "\<lbrakk>\<And>x y. \<lbrakk>x \<in> set xsa; y \<in> set xsa\<rbrakk> \<Longrightarrow> x = y; \<And>x. x \<in> set xsa \<Longrightarrow> x = y\<rbrakk> \<Longrightarrow> foldr (+) xsa 0 = real (length xsa) * y"
  assume "\<And>x y. \<lbrakk>x \<in> set (a # xsa); y \<in> set (a # xsa)\<rbrakk> \<Longrightarrow> x = y"
assume a2: "\<And>x. x \<in> set (a # xsa) \<Longrightarrow> x = y"
  then have f3: "a = y"
    by simp
  then have "a * real (length xsa) = foldr (+) xsa 0"
    using a2 a1 by (metis (no_types) list.set_intros(2) mult.commute)
  then show "a + foldr (+) xsa 0 = real (length (a # xsa)) * y"
    using f3 by (simp add: distrib_left mult.commute)
qed 

lemma foldr_same_int: "(\<And> x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x = y) \<Longrightarrow>
                   (\<And> x . x \<in> set xs \<Longrightarrow> x = y) \<Longrightarrow> 
                   foldr (+) xs 0 =  (length xs) * y"
  apply(induction xs)
    apply simp
    apply(subst foldr.simps) 
    apply fastforce
  done

lemma t_build_cnt: "T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d n \<le> cnt (vebt_buildup n) * 13"  
proof(induction n rule: T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 va)
  then show ?case 
  proof(cases "even (Suc (Suc va))")
    case True
    hence *: "T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va)) = 11+
           T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2) +
         2 ^ (Suc (Suc va) div 2) * (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2))"
      apply(subst T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d.simps)
      by simp
    have " real (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (va div 2))) \<le> 13 * cnt (vebt_buildup (Suc (va div 2)))" 
      using "3.IH"(1) True by force
    moreover hence 1:"  2 ^ (Suc (Suc va) div 2)* (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2)) \<le>
                    2 ^ (Suc (Suc va) div 2) * ((cnt (vebt_buildup (Suc (Suc va) div 2)))*13)"
      using ordered_semiring_class.mult_mono[of "(T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2))" " ((cnt (vebt_buildup (Suc (Suc va) div 2)))*13)" 
            "2 ^ (Suc (Suc va) div 2)" "2 ^ (Suc (Suc va) div 2)"] by simp
    ultimately have " T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2) +
         2 ^ (Suc (Suc va) div 2) * (T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc va) div 2)) \<le> 
             cnt (vebt_buildup (Suc (Suc va) div 2))*13 + 
          2 ^ (Suc (Suc va) div 2) * ((cnt (vebt_buildup (Suc (Suc va) div 2)))*13)"
           by (smt (verit) "3.IH"(1) True of_nat_add)
         have 10: "(foldr (+) 
                 (replicate (l) ((cnt (vebt_buildup (Suc (Suc va) div 2)))
                  )) 0) = 
                   l * ((cnt (vebt_buildup (Suc (Suc va) div 2))))" for l
           using foldr_same[of "(replicate l (cnt (vebt_buildup (Suc (Suc va) div 2))))"
                             "cnt (vebt_buildup (Suc (Suc va) div 2))" ] 
              length_replicate by simp
         have " cnt (vebt_buildup (Suc (Suc va) div 2))*13 + 
          2 ^ (Suc (Suc va) div 2) * ((cnt (vebt_buildup (Suc (Suc va) div 2)))*13) + 11\<le>
          13* cnt (vebt_buildup (Suc (Suc va)))" 
          apply(subst vebt_buildup.simps)
      using True apply simp
      apply(subst sym[OF foldr_replicate]) 
    proof-
      assume "even va"
      have " 2* (2 ^ (va div 2) * cnt (vebt_buildup (Suc (va div 2)))) = 
             foldr (+) (replicate (2 * 2 ^ (va div 2)) (cnt (vebt_buildup (Suc (va div 2))))) 0"
        apply(rule sym)
        using 10 div2_Suc_Suc[of va] by simp
      then show "26 * (2 ^ (va div 2) * cnt (vebt_buildup (Suc (va div 2))))
    \<le> 2 + 13 * foldr (+) (replicate (2 * 2 ^ (va div 2)) (cnt (vebt_buildup (Suc (va div 2))))) 0"
        by simp
    qed
    then show ?thesis
      by (smt (verit, ccfv_SIG) "*" "1" "3.IH"(1) True numeral_Bit1 numeral_plus_numeral numeral_plus_one of_nat_add of_nat_numeral semiring_norm(2))
  next
    case False
    have "12 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc ( Suc (va div 2))) + 2 ^ Suc ( Suc ( va div 2)) * T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d ( Suc ( va div 2))
          \<le> cnt ( Node None (Suc (Suc va)) (replicate (2 ^ Suc ( Suc ( va div 2))) (vebt_buildup ( Suc ( va div 2))))
                     (vebt_buildup (Suc ( Suc ( va div 2))))) * 13" 
      apply(subst cnt.simps)
    proof-
       have 10: "(foldr (+) 
                 (replicate (l) ((cnt (vebt_buildup (Suc (Suc va) div 2)))
                  )) 0) = 
                   l * ((cnt (vebt_buildup (Suc (Suc va) div 2))))" for l
           using foldr_same[of "(replicate l (cnt (vebt_buildup (Suc (Suc va) div 2))))"
                             "cnt (vebt_buildup (Suc (Suc va) div 2))" ] 
              length_replicate by simp
        hence map_cnt: " foldr (+) (map cnt (replicate (2 ^ Suc (Suc (va div 2))) (vebt_buildup (Suc (va div 2))))) 0 = 
                 2 ^ Suc (Suc (va div 2)) * cnt (vebt_buildup (Suc (va div 2))) " by simp
        have "T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc (va div 2))) \<le> 13 * cnt (vebt_buildup (Suc (Suc (va div 2))))"
          using "3.IH"(3) False by force
        moreover have "T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (va div 2)) \<le> 13 * cnt(vebt_buildup (Suc (va div 2)))"
          using "3.IH"(4) False by force
        moreover have add_double_trans: "(a::real) \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 
                           i \<ge> 0\<Longrightarrow> a + c*i \<le> b + d*i" for a b c d i
          using mult_right_mono by fastforce
        ultimately have " real(T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc (va div 2)))) +  2 ^ Suc (Suc (va div 2)) * real( T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (va div 2))) \<le>
                13 * cnt (vebt_buildup (Suc (Suc (va div 2)))) + 
                    2 ^ Suc (Suc (va div 2)) * (13 * cnt(vebt_buildup (Suc (va div 2))))" 
          by (meson add_mono_thms_linordered_semiring(1) mult_mono of_nat_0_le_iff order_refl zero_le_numeral zero_le_power)
        hence 11:"(12 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc (va div 2))) +  2 ^ Suc (Suc (va div 2)) * T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (va div 2))) \<le>
               12 + 13 * cnt (vebt_buildup (Suc (Suc (va div 2)))) + 
                    2 ^ Suc (Suc (va div 2)) * 13 * cnt(vebt_buildup (Suc (va div 2)))"
          using algebra_simps by simp
        show " (12 + T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (Suc (va div 2))) +
      2 ^ Suc (Suc (va div 2)) * T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Suc (va div 2)))
    \<le> (1 + cnt (vebt_buildup (Suc (Suc (va div 2)))) +
        foldr (+) (map cnt (replicate (2 ^ Suc (Suc (va div 2))) (vebt_buildup (Suc (va div 2))))) 0) * 13" 
          apply(subst map_cnt)
          using 11 algebra_simps by simp
      qed        
  then show ?thesis
    apply(subst vebt_buildup.simps)
    apply(subst T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d.simps)
    using False by force
qed
qed

lemma t_buildup_cnt: "T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p  n \<le> cnt (vebt_buildup n) * 13"
  apply(rule order.trans[where b = "real(T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d n)"])
  apply(rule order.strict_implies_order)
  apply (simp add: VEBT_internal.buildup_build_time)
  apply(rule t_build_cnt)
 done

lemma count_buildup: "cnt (vebt_buildup n) \<le> 2 * 2^n"
  by (smt (verit, ccfv_threshold) VEBT_internal.cnt_bound' add.right_neutral add_less_mono buildup_gives_valid cnt.simps(1) even_Suc lessI odd_pos one_le_power plus_1_eq_Suc vebt_buildup.elims)

lemma count_buildup': "cnt (vebt_buildup n) \<le> 2 * (2::nat)^n"
   by (simp add: VEBT_internal.count_buildup)

theorem vebt_buildup_bound: "u = 2^n \<Longrightarrow> T\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d\<^sub>u\<^sub>p  n \<le> 26 * u"
  using count_buildup'[of n] t_buildup_cnt[of n] by linarith

text \<open>Count in natural numbers\<close>

fun cnt':: "VEBT \<Rightarrow> nat" where
"cnt' (Leaf a b) = 1"|
"cnt' (Node info deg treeList summary) = 1 + cnt' summary + foldr (\<lambda> a b. a+b) (map cnt' treeList) 0"

lemma cnt_cnt_eq:"cnt t = cnt' t"
  apply(induction t)
  apply auto
  apply (smt (z3) VEBT_internal.real_nat_list map_eq_conv of_nat_0)
  done

end
end