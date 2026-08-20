(*  Title:  AuxiliaryNSA.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>Various supporting lemmas\<close>

theory  AuxiliaryNSA
imports "HOL-Nonstandard_Analysis.HSeries" "Real_Power.Log" 
begin

text\<open>These results can be moved to the indicated theories.\<close>

text\<open>StarDef.thy lemmas\<close>
lemma Iset_star_of_empty [simp]: "Iset(star_of {}) = {}"
by (transfer empty_def) simp

lemma Iset_star_n_empty [simp]: "Iset (star_n (\<lambda>n. {})) = {}"
  by (simp add: star_of_def [symmetric])

lemma Iset_eq_cancel:
  "(Iset (star_n X) = Iset (star_n Y)) = (eventually (\<lambda>n. X n = Y n) \<U>)"
  by (simp add: transfer_set_eq)

lemma Collect_starP_starset_eq: "{x. (*p* P) x} = *s* {x. P x}"
by transfer simp

text\<open>Hypernat.thy lemmas\<close>

lemma Nats_hypnat_of_nat_iff: "(n \<in> Nats) = (\<exists>m. n = hypnat_of_nat m)"
  by (auto simp add: Nats_def)

lemma HNatInfinite_add_one_cancel:
   "N + 1 \<in> HNatInfinite \<Longrightarrow> N \<in> HNatInfinite"
  by (drule HNatInfinite_diff [of _ 1], auto)

lemma of_hypnat_of_nat [simp]: "of_hypnat(hypnat_of_nat n) = of_nat n"
  by (metis of_hypnat_def star_of_nat_def starfun_star_of)

lemma of_nat_hypreal_of_hypnat:
     "of_nat n = of_hypnat (hypnat_of_nat n)"
  by simp

lemma hSuc_eq_add_one:
  "\<And>n. hSuc n = n + 1"
by transfer simp

lemma HNatInfinite_hSuc_diff_one [simp]: 
  "N \<in> HNatInfinite \<Longrightarrow> hSuc (N - 1) = N"
by (metis hSuc_eq_add_one hypnat_le_add_diff_inverse2 one_le_HNatInfinite)

lemma HNatInfinite_atLeastAtMost_hSuc:
  "N \<in> HNatInfinite \<Longrightarrow> {M..<N} = {M..<hSuc(N - 1)}"
by (metis HNatInfinite_hSuc_diff_one)

text\<open>HyperDef.thy lemmas\<close>

lemma hypreal_of_nat_less_hypreal_of_hypnat_iff:
      "\<And>a b.(hypreal_of_nat a < of_hypnat b) = (hypnat_of_nat a < b)"
by (auto simp only: of_nat_hypreal_of_hypnat of_hypnat_less_iff)

lemma hypreal_of_nat_le_hypreal_of_hypnat_iff:
      "\<And>a b.(hypreal_of_nat a \<le> hypreal_of_hypnat b) = (hypnat_of_nat a \<le>  b)"
  by (auto simp only: of_nat_hypreal_of_hypnat of_hypnat_le_iff)

lemma hyperpow_zero [simp]: "x pow 0 = 1"
by (metis hyperpow_hypnat_of_nat power_0 star_of_simps(9))

lemma hyperpow_of_nat: "\<And>x. x pow of_nat n = x ^ n"
by transfer simp

lemma hyperpow_hSuc_zero [simp]:
  "\<And>N. (0::'a::{power, semiring_0} star) pow hSuc N = 0"
by transfer simp

lemma starfun_power: "\<And>n. (*f* (^) x) n = star_of x pow n"
by transfer simp

lemma hyperpow_diff:
  "\<And>x n k. n \<ge> k \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> ((x::'a::field star) pow n)/(x pow k) = x pow (n - k)"
  by transfer (metis power_diff)

lemma hyperpow_divide:
  "\<And>x y n. ((x::'a::field star)/y) pow n = (x pow n)/(y pow n)"
by transfer (metis power_divide)

lemma hyperpow_diff_cancel:
  "k \<le> n \<Longrightarrow> x pow k * (x::'a::monoid_mult star) pow (n - k) = x pow n"
  by (simp add: hyperpow_add [symmetric])

lemma hyperpow_0_left:
  "\<And>n. 0 pow n = (if n = 0 then 1 else (0::'a::{power, semiring_1} star))"
by transfer (simp add: power_0_left)

lemma hyperpow_eq_0_iff [simp]:
  "\<And>x n. (x pow n = 0) \<longleftrightarrow> 
           (x = (0::'a::{mult_zero,zero_neq_one,semiring_1_no_zero_divisors,power} star) \<and> n \<noteq> 0)"
  by transfer simp

lemma hyperpow_less_zero_eq:
  "\<And>x n. (x pow n < (0::'a::{linordered_idom} star)) = (\<not> 2 dvd n \<and> x < 0)"
by transfer (metis power_less_zero_eq)

lemma star_n_divide: "star_n X / star_n Y = star_n (\<lambda>n. X n / Y n)"
  by (simp add: star_divide_def starfun2_star_n)

text\<open>NSA.thy lemmas\<close>

lemma approx_zero_abs_zero_iff [iff]:
  "(abs x \<approx> 0) = ((x::hypreal) \<approx> 0)"
by (metis Infinitesimal_hrabs_iff mem_infmal_iff)

lemma Infinitesimal_divide_HFinite:
  "\<lbrakk> (x::'a::real_normed_div_algebra star) \<in> Infinitesimal; y \<in> HFinite - Infinitesimal \<rbrakk> 
       \<Longrightarrow> x/y \<in> Infinitesimal"
by (metis HFinite_inverse2 Infinitesimal_HFinite_mult divide_inverse)

lemma approx_1_not_Infinitesimal:
  "x \<approx> (1 ::'a::real_normed_div_algebra star) \<Longrightarrow> x \<notin> Infinitesimal"
  using approx_sym approx_trans mem_infmal_iff one_not_Infinitesimal 
  by blast

lemma HFinite_add_imp_HFinite:
  "\<lbrakk> x \<ge> (0::hypreal); y \<ge> 0; x + y \<in> HFinite \<rbrakk> \<Longrightarrow> y \<in> HFinite"
  using HFinite_not_HInfinite HInfinite_add_ge_zero2 not_HFinite_HInfinite 
  by blast

lemma Infinitesimal_hrealpow_cancel [simp]:
  assumes "n > 0" 
  shows "(x ^ n \<in> Infinitesimal) = ((x::'a::real_normed_div_algebra star) \<in> Infinitesimal)"
proof (insert assms, induct n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case
    using Infinitesimal_mult not_Infinitesimal_mult 
    by force 
qed

lemma hrealpow_approx:
   "\<lbrakk> (x::'a::{real_normed_algebra, one, monoid_mult} star) \<approx> b;  b \<in> HFinite \<rbrakk> \<Longrightarrow> x ^ n \<approx> b ^ n"
by (induct n, auto dest: hrealpow_HFinite approx_mult_HFinite [of x])

lemma hrealpow_approx_one:
   "(x::'a::{real_normed_algebra, one, monoid_mult} star) \<approx> 1 \<Longrightarrow> x ^ n \<approx> 1"
by (auto dest: hrealpow_approx)

lemma zero_not_HInfinite [simp]: "0 \<notin> HInfinite"
by (simp add: HFinite_not_HInfinite)

lemma HInfinite_hyperpow_not_zero:
  "(x::'a::{real_normed_field} star) \<in> HInfinite \<Longrightarrow> x pow n \<noteq> 0"
  by (metis hyperpow_not_zero zero_not_HInfinite)

lemma HFinite_divide:
  "\<lbrakk> (x::'a::real_normed_div_algebra star) \<in> HFinite; y \<notin> Infinitesimal \<rbrakk> \<Longrightarrow> x/y \<in> HFinite"
by (metis HFinite_mult Infinitesimal_inverse_HFinite divide_inverse)

lemma HFinite_hyperpow_HFinite:
  "\<lbrakk> (x::'a::{monoid_mult, real_normed_algebra} star) \<in> HFinite; n \<in> \<nat> \<rbrakk> \<Longrightarrow> x pow n \<in> HFinite"
  by (metis Nats_cases hrealpow_HFinite hyperpow_hypnat_of_nat of_nat_eq_star_of)

lemma hyperpow_approx:
      assumes HFinite_a: "a \<in> HFinite" 
      and approx_ab: "(a::hypreal) \<approx> b"
      shows "a pow of_nat n \<approx> b pow of_nat n"
by (metis HFinite_a approx_HFinite approx_ab hrealpow_approx hyperpow_of_nat)

lemma Infinitesimal_approx_hyperpow:
      assumes Infinitesimal_a: "a \<in> Infinitesimal" 
      and approx_ab: "(a::hypreal) \<approx> b"
      shows "a pow n \<approx> b pow n"
  by (metis Infinitesimal_a Infinitesimal_approx Infinitesimal_hyperpow Infinitesimal_monad_zero_iff 
      approx_ab approx_mem_monad_zero approx_monad_iff hyperpow_zero hypnat_neq0_conv)

lemma hnorm_hypreal_of_hypnat [simp]: 
  "\<And>n. hnorm (of_hypnat n::'a::real_normed_algebra_1 star) = of_hypnat n"
  by transfer simp

lemma HFinite_of_nat [simp]: "of_nat n \<in> HFinite"
by (metis HFinite_star_of star_of_nat_def)

lemma HInfinite_def2: "HInfinite = {x. \<forall>n \<in> Nats. hypreal_of_hypnat n < hnorm x}"
proof (auto simp add: HInfinite_def SHNat_eq SReal_def)
   fix x::"'a :: real_normed_vector star" and N
   assume "\<forall>r. (\<exists>ra. r = hypreal_of_real ra) \<longrightarrow> r < hnorm x" 
   then show "hypreal_of_nat N < hnorm x"
     using star_of_nat_def by blast
next
   fix x::"'a :: real_normed_vector star" and ra 
   assume "\<forall>n. (\<exists>N. n = hypnat_of_nat N) \<longrightarrow> hypreal_of_hypnat n < hnorm x"
   then show "hypreal_of_real ra < hnorm x"
     by (metis of_nat_hypreal_of_hypnat less_trans reals_Archimedean2 
          star_of_less star_of_nat_def)
 qed

lemma HFinite_def2: "HFinite = {x. \<exists>n \<in> Nats. hnorm x < hypreal_of_hypnat n}"
proof (auto simp add: HFinite_def)
  fix x::"'a :: real_normed_vector star" and r
  assume r: "r \<in> \<real>" and hnormx: "hnorm x < r"
  then obtain s where "r = of_real s"
    using Reals_cases by blast
  moreover obtain n where "s < of_nat n"
    using reals_Archimedean2 by blast
  ultimately have "hnorm x < hypreal_of_hypnat (of_nat n)"
    using hnormx
    by (metis dual_order.strict_trans of_hypnat_def of_nat_eq_star_of of_real_eq_star_of star_of_less
        starfun_star_of) 
  then show "\<exists>n\<in>\<nat>. hnorm x < hypreal_of_hypnat n"
    by fastforce
next
  fix x::"'a :: real_normed_vector star" and n
  assume n: "n \<in> \<nat>" and "hnorm x < hypreal_of_hypnat n"
  then have "hnorm x < hypreal_of_hypnat n"
    by blast
  moreover have "hypreal_of_hypnat n \<in> \<real>"
    using n by (auto simp add: SHNat_eq)
  ultimately show "\<exists>r\<in>\<real>. hnorm x < r"
    by fastforce
qed

lemma HFinite_less_Nat_Ex:
  "(x::hypreal) \<in> HFinite \<Longrightarrow> \<exists>n\<in>Nats. x < n"
  unfolding Nats_def HFinite_def2
  by simp (metis abs_ge_self order_less_le xt1(10))

lemma HNatInfinite_of_hypnat_HInfinite: 
  "x \<in> HNatInfinite \<Longrightarrow> (of_hypnat x :: 'a::real_normed_algebra_1 star) \<in> HInfinite"
proof (auto simp add: HInfinite_def2 Nats_def)
  fix n
  assume "x \<in> HNatInfinite" 
  then show "hypreal_of_nat n < hypreal_of_hypnat x"
    by (metis hypreal_of_nat_less_hypreal_of_hypnat_iff star_of_less_HNatInfinite)
qed

lemma HInfinite_ge_HNatInfinite:
  "\<lbrakk> n \<in> HNatInfinite; hypreal_of_hypnat n \<le> x \<rbrakk> \<Longrightarrow> x \<in> HInfinite"
  using HInfinite_ge_HInfinite HNatInfinite_of_hypnat_HInfinite of_hypnat_0_le_iff 
  by blast

lemma HNatInfinite_of_hypnat_HInfinite_iff:
  "(of_hypnat n :: 'a::real_normed_algebra_1 star) \<in> HInfinite = (n \<in> HNatInfinite)"
proof 
  assume "(of_hypnat n :: 'a::real_normed_algebra_1 star) \<in> HInfinite" 
  then show "n \<in> HNatInfinite" 
    by (auto simp add: HInfinite_def2 HNatInfinite_def)
next 
  assume "n \<in> HNatInfinite" 
  then show "(of_hypnat n :: 'a::real_normed_algebra_1 star) \<in> HInfinite" 
    using HNatInfinite_of_hypnat_HInfinite by blast
qed

lemma HNatInfinite_inverse_of_hypnat_Infinitesimal_iff:
  "N \<noteq> 0 \<Longrightarrow> (1/hypreal_of_hypnat N \<in> Infinitesimal) = (N \<in> HNatInfinite)"
  by (simp add: HNatInfinite_of_hypnat_HInfinite_iff divide_inverse inverse_Infinitesimal_iff_HInfinite)

lemma Nats_hypreal_of_hypnat_HFinite:
  "n \<in> Nats \<Longrightarrow> of_hypnat n \<in> HFinite"
  using Nats_hypnat_of_nat_iff by auto

lemma approx_divide_HFinite_diff_Infinitesimal: 
   "\<lbrakk>(x :: 'a::{real_normed_div_algebra, field} star) \<approx> y; 
     z \<in> HFinite - Infinitesimal
    \<rbrakk> \<Longrightarrow> x/z \<approx> y/z"
by (metis HFinite_inverse2 approx_mult1 divide_inverse)

lemma HFinite_diff:
  "\<lbrakk> x \<in> HFinite; y \<in> HFinite \<rbrakk> \<Longrightarrow> x - y \<in> HFinite"
by (metis HFinite_add HFinite_minus_iff add_uminus_conv_diff)

lemma Infinitesimal_interval2a:
     "\<lbrakk> e \<in> Infinitesimal; e' \<in> Infinitesimal;
        hnorm e' \<le> hnorm x ; hnorm x \<le> hnorm e \<rbrakk> \<Longrightarrow> x \<in> Infinitesimal"
  by (auto simp add: Infinitesimal_def)

lemma Infinitesimal_HInfinite_divide:
  "\<lbrakk> (x::'a::{real_normed_div_algebra, field} star) \<in> HFinite; y \<in> HInfinite \<rbrakk> \<Longrightarrow> x/y \<in> Infinitesimal"
by (simp add: HInfinite_inverse_Infinitesimal Infinitesimal_HFinite_mult2 divide_inverse)

lemma approx_divide_HInfinite: 
  "\<lbrakk>(x :: 'a::{real_normed_div_algebra, field} star) \<approx> y; z \<in> HInfinite\<rbrakk> \<Longrightarrow> x/z \<approx> y/z"
by (metis Infinitesimal_HInfinite_divide approx_minus_iff approx_star_of_HFinite 
          diff_divide_distrib mem_infmal_iff star_zero_def)

lemma approx_1_mult_HFinite_HFinite:
      assumes approx_1: "x \<approx> (1 ::'a::real_normed_div_algebra star)" 
      and HFinite_prod: "x*y \<in> HFinite"
      shows "y \<in> HFinite"
proof (rule ccontr)
  assume "y \<notin> HFinite" 
  then have HInfinite_y: "y \<in> HInfinite" 
    using HFinite_HInfinite_iff 
    by blast 
  have HFinite_x: "x \<in> HFinite" 
    by (metis approx_1 approx_star_of_HFinite star_one_def) 
  have "x \<notin> Infinitesimal" 
    using approx_1 approx_1_not_Infinitesimal 
    by blast
  then have "x * y \<in> HInfinite" 
    using  HInfinite_y HFinite_x HInfinite_HFinite_not_Infinitesimal_mult2 
           HInfinite_diff_HFinite_Infinitesimal_disj  
    by blast 
  thus "False" 
    using HFinite_not_HInfinite HFinite_prod 
    by blast 
qed

text\<open>Star.thy lemmas\<close>

instance star :: (semiring_modulo) semiring_modulo
  by (intro_classes, transfer) (simp add: div_mult_mod_eq)

declare of_bool_def [transfer_unfold] 

instance star :: (semiring_parity) semiring_parity
proof
  show "\<And>a ::'a :: semiring_parity star. a mod 2 = of_bool (\<not> 2 dvd a)"
    by transfer (simp add: mod2_eq_if)
next
  show "\<not> (2::'a :: semiring_parity star) dvd 1"
    by transfer simp
next 
  show "\<And>a ::'a :: semiring_parity star. 2 dvd a \<Longrightarrow> (1 + a) div 2 = a div 2"
    by transfer simp
qed

lemma starfun_starfun_n_eq:
  "*f* f = *fn* (\<lambda>n. f)"
  by (metis starfun_n_starfun)

lemma starfun_n_zero:
  "(*fn* (\<lambda>m n::'b. 0::'a::zero)) = (\<lambda>n. star_of 0)"
  by (metis starfun_const_fun starfun_starfun_n_eq)

lemma InternalFuns_starfun_n [simp]: "*fn* f \<in> InternalFuns"
by (force simp add: InternalFuns_def)

lemma InternalFuns_starfun [simp]: "*f* f \<in> InternalFuns"
by (simp add: starfun_starfun_n_eq)

lemma InternalFuns_starfun2 [simp]: "(*f2* f) a \<in> InternalFuns"
  by (metis InternalFuns_starfun_n star_cases starfun2_def starfun_n_def)

lemma starfun_n_hyperpow: "(\<lambda>n. (*f2* (^)) ((*fn* f) n) ((*fn* g) n)) z = (*fn* (\<lambda> i x. (f i x) ^ (g i x))) z"
proof (cases z)
  case (star_n X)
   assume Z: "z = star_n X"
   then have "(\<lambda>n. (*f2* (^)) ((*fn* f) n) ((*fn* g) n)) z = (*f2* (^)) ((*fn* f) (star_n X)) ((*fn* g) (star_n X))"
     by simp
   also have "\<dots> = (*f2* (^)) (star_n (\<lambda>n. f n (X n))) (star_n (\<lambda>n. g n (X n)))"
     by (simp add: Ifun_star_n starfun_n_def)
   also have "\<dots> = star_n (\<lambda>n. f n (X n) ^ g n (X n))"
     by (simp add: starfun2_star_n)
   also have "\<dots> =  (*fn* (\<lambda>i x. f i x ^ g i x)) (star_n X)"
     by (simp add: Ifun_star_n starfun_n_def)
   finally show ?thesis using Z [symmetric] by simp
 qed

lemma InternalFuns_hSuc [simp]: "hSuc \<in> InternalFuns"
by (simp add: hSuc_def)

lemma InternalSets_starset_n [simp]: "*sn* X \<in> InternalSets"
by (auto simp add: InternalSets_def)

lemma InternalSets_singleton [simp]: "{x} \<in> InternalSets"
proof -
  {fix X assume "x = star_n X" 
    have "{star_n X} = Iset (star_n (\<lambda>n. {X n}))"
    proof
       show "{star_n X} \<subseteq> Iset (star_n (\<lambda>n. {X n}))"
         by (simp add: Iset_star_n) 
    next 
      show "Iset (star_n (\<lambda>n. {X n})) \<subseteq> {star_n X}" 
      proof 
        fix y
        assume yin: "y \<in> Iset (star_n (\<lambda>n. {X n}))" 
        then show  "y \<in> {star_n X}"
          using yin 
          by (auto intro: star_cases [of y] 
                   simp add: Iset_def starP2_star_n star_n_eq_iff)
        qed
      qed
   }
   then show ?thesis
     by (force intro: star_cases simp add: InternalSets_def starset_n_def)
 qed

lemma starset_n_singleton [simp]: "*sn* (\<lambda>n. {X n}) =  {star_n X}"
proof  (auto simp add: starset_n_def)
  fix x
  assume xinX: "x \<in> Iset (star_n (\<lambda>n. {X n}))"
  then show "x = star_n X"
  proof (cases x)
    case (star_n Y)
    then show ?thesis 
      using xinX by (auto simp add: Iset_star_n star_n_eq_iff)
  qed  
next
  show "star_n X \<in> Iset (star_n (\<lambda>n. {X n}))"
    by (simp add: Iset_star_n)
qed

lemma starset_n_singleton2:"*sn* (\<lambda>n. {X n}) = {x. x = star_n X}"
by simp

lemma starset_n_empty [simp]: "*sn* (\<lambda>n. {}) = {}"
by (simp add: starset_n_def )

lemma InternalSets_empty [simp]: "{} \<in> InternalSets"
  by (metis InternalSets_starset_n starset_n_empty)

lemma starset_n_subset: 
   "(*sn* X \<subseteq> *sn* Y) = (eventually (\<lambda>n. X n \<subseteq> Y n) \<U>)"
proof 
  assume "*sn* X \<subseteq> *sn* Y" 
  then have "\<forall>x\<in>Iset (star_n X). x \<in> Iset (star_n Y)"
    by (simp add: set_mp starset_n_def)
  moreover 
   have "\<forall>Xa. star_n Xa \<in> Iset (star_n Y) = (\<forall>\<^sub>F n in \<U>. Xa n \<in> Y n)"
     by (simp add: Iset_star_n)
   ultimately have "\<forall>\<^sub>F n in \<U>. \<forall>x\<in>X n. x \<in> Y n" 
     by (force intro: transfer_ball [THEN meta_eq_to_obj_eq, THEN iffD1])
   then show "\<forall>\<^sub>F n in \<U>. X n \<subseteq> Y n" 
     by (simp add: subset_eq)
 next
   assume  subsetF: "\<forall>\<^sub>F n in \<U>. X n \<subseteq> Y n" 
   show "*sn* X \<subseteq> *sn* Y"
   proof 
     fix x
     assume xX: "x \<in> *sn* X"
     show "x \<in> *sn* Y"
     proof (cases x)
       case (star_n X)
       then show ?thesis 
         using xX subsetF by (auto elim: eventually_elim2 simp add: Iset_star_n starset_n_def)
     qed
   qed
 qed

lemma starfun_n_mult_star_n_right:
  "(*fn* F) n * star_n X = (*fn* (\<lambda>n m. F n m * X n)) n"
  by (cases n, simp add: Ifun_star_n star_n_mult starfun_n_def)

lemma starfun_n_mult_star_n_left:
  "star_n X  * (*fn* F) n = (*fn* (\<lambda>n m. X n * F n m)) n"
  by (cases n, simp add: Ifun_star_n star_n_mult starfun_n_def)

lemma starfun_n_diff:
     "(*fn* f) z - (*fn* g) z = (*fn* (\<lambda>i x. f i x - g i x)) z"
  by (cases z, simp add:  Ifun_star_n star_n_minus star_n_diff starfun_n_def)

lemma starfun_n_inverse: "inverse ((*fn* f) x) = (*fn* (\<lambda>i x. inverse ((f i) x))) x"
  by (cases x, simp add:  Ifun_star_n star_n_minus star_n_inverse starfun_n_def)

lemma InternalFuns_const_fun [simp]:
  "(\<lambda>n. c) \<in> InternalFuns"
proof (cases c, simp add: InternalFuns_def)
  case (star_n X)
  have "(\<lambda>n. c) = *fn* (\<lambda>m n. X m)" 
  proof 
    fix n :: "'c star"
    obtain N where "n = star_n N"
      using star_cases by blast 
    then show "c = (*fn* (\<lambda>m n. X m)) n"
      by (simp add: star_n starfun_n_def transfer_Ifun) 
  qed
  then show "\<exists>F. (\<lambda>n. star_n X) = *fn* F"
    using star_n by blast 
qed

lemma starfun_n_divide:
     "((*fn* f) z ::'a::division_ring star)/ (*fn* g) z = (*fn* (\<lambda>i x. f i x / g i x)) z"
  by (cases z, simp add: Ifun_star_n divide_inverse starfun_n_def star_n_inverse star_n_mult)

lemma InternalFuns_divide:
  "\<lbrakk> f \<in> InternalFuns; g \<in> InternalFuns \<rbrakk> 
       \<Longrightarrow> (\<lambda>n. (f n ::'a::division_ring star)/g n) \<in> InternalFuns"
by (auto simp add: InternalFuns_def starfun_n_divide)

lemma InternalFuns_id_fun [simp]: "(\<lambda>n. n) \<in> InternalFuns"
proof -
   have id: "(\<lambda>n. n) = (*fn* (\<lambda>n m. m))" 
     by (metis ext starfun_Id starfun_starfun_n_eq)
   then show ?thesis
     using InternalFuns_def by blast
 qed

(* This proof could be nicer, I guess *)
lemma FreeUltrafilterNat_star_n_Infinitesimal:
  assumes "eventually (\<lambda>n. norm (X n) < inverse(Suc n)) \<U>" 
  shows "star_n X \<in> Infinitesimal"
proof (auto simp add: Infinitesimal_def hnorm_def starfun Reals_def 
       star_of_def star_less_def starP2_star_n star_n_zero_num)
  fix r
  assume "\<forall>\<^sub>F n in \<U>. 0 < (r::real)" 
  moreover have "eventually (\<lambda>n. inverse (real (Suc n)) < r) \<U>" 
    using FreeUltrafilterNat_inverse_real_of_posnat calculation transfer_bool by blast 
  ultimately show "\<forall>\<^sub>F n in \<U>. norm (X n) < r" using assms 
    by (force elim: eventually_elim2)
qed

lemma starset_n_atLeastLessThan_eq:
  "*sn* (\<lambda>n. {(X n)..<(Y n)}) = {star_n X..<star_n Y}"
proof (auto simp add: starset_n_def)
  fix x
  assume x: "x \<in> Iset (star_n (\<lambda>n. {X n..<Y n}))" 
  then show "star_n X \<le> x"
  proof (cases x)
    case (star_n X)
    then show ?thesis 
      using x by (simp add: Iset_star_n eventually_mono star_n star_n_le)  
  qed
next
  fix x
  assume x: "x \<in> Iset (star_n (\<lambda>n. {X n..<Y n}))" 
  then show "x < star_n Y"
  proof (cases x)
    case (star_n X)
    then show ?thesis 
      using x by (simp add: Iset_star_n eventually_mono star_n_less) 
  qed
next
  fix x
  assume x: "star_n X \<le> x" "x < star_n Y"
  then show "x \<in> Iset (star_n (\<lambda>n. {X n..<Y n}))"
  proof (cases x)
    case (star_n X)
    then show ?thesis 
      using x by (simp add: Iset_star_n starP2_star_n star_n_less 
           star_le_def eventually_conj_iff) 
  qed
qed

lemma starset_n_atLeast_zero_LessThan_eq:
  "*sn* (\<lambda>n. {0..<(X n)}) = {0..<star_n X}"
by (simp add: starset_n_atLeastLessThan_eq [of "\<lambda>n. 0"] star_n_zero_num)

lemma starset_atLeastAtMost:
  "{of_nat m .. of_nat n} = *s* {m .. n}"
proof
  show "{of_nat m..of_nat n} \<subseteq> *s* {m..n}"
  proof 
    have "\<And>x. hypnat_of_nat m \<le> x \<and> x \<le> hypnat_of_nat n \<longrightarrow> x \<in> *s* {m..n}"
      by (transfer, simp)
    then
    show "\<And>x. x \<in> {of_nat m..of_nat n} \<Longrightarrow> x \<in> *s* {m..n}"
      by simp
  qed
next
  show "*s* {m..n} \<subseteq> {of_nat m..of_nat n}"
  proof 
    have "\<And>x. x \<in> *s* {m..n} \<Longrightarrow> hypnat_of_nat m \<le> x"
      by (transfer, simp)
    moreover have "\<And>x. x \<in> *s* {m..n} \<Longrightarrow> x \<le> hypnat_of_nat n"
      by (transfer, simp)
    ultimately show "\<And>x. x \<in> *s* {m..n} \<Longrightarrow> x \<in> {of_nat m..of_nat n}"
      by simp
  qed
qed

lemma starset_n_atLeastAtMost:
  "*sn* (\<lambda>n. {(X n)..(Y n)}) = {star_n X..star_n Y}"
proof (auto simp add: starset_n_def)
  fix x
  assume x_in_ISet: "x \<in> Iset (star_n (\<lambda>n. {X n..Y n}))"
  have "star_n X \<le> x \<and> x \<le> star_n Y"  
  proof (cases x)
    case (star_n X)
    then show ?thesis 
      using x_in_ISet 
      by (auto simp add: star_le_def starP2_star_n Iset_star_n
             eventually_conj_iff)
  qed
  then show "star_n X \<le> x" and "x \<le> star_n Y"
    by auto
next
  fix x
  assume x_bounds: "star_n X \<le> x" "x \<le> star_n Y"
  then show "x \<in> Iset (star_n (\<lambda>n. {X n..Y n}))"
  proof (cases x)
    case (star_n X)
    then show ?thesis 
      using x_bounds 
      by (auto simp add: star_le_def starP2_star_n Iset_star_n
             eventually_conj_iff)
  qed
qed

lemma starset_n_atLeast_zero_AtMost:
  "*sn* (\<lambda>n. {0..(X n)}) = {0..star_n X}"
by (simp add: starset_n_atLeastAtMost [of "\<lambda>n. 0"] star_n_zero_num)

lemma InternalSets_atLeastLessThan [simp]: "{M..<N} \<in> InternalSets"
  by (metis InternalSets_starset_n star_cases starset_n_atLeastLessThan_eq)


lemma InternalSets_atLeastAtMost [simp]: "{M..N} \<in> InternalSets"
proof -
  have "\<exists>f. {M..N} = *sn* f"
    by (metis star_cases starset_n_atLeastAtMost)
  then show ?thesis
    by (simp add: InternalSets_def)
qed

lemma le_inverse_HNatInfinite_Infinitesimal:
      "\<lbrakk>n \<in> HNatInfinite; hnorm x \<le> inverse (hypreal_of_hypnat n)\<rbrakk> \<Longrightarrow> x \<in> Infinitesimal"
by (metis HNatInfinite_inverse_Infinitesimal hnorm_le_Infinitesimal)

(* Adapted from a proof by Jessika Rockel*)
lemma InternalFuns_hyperpow: 
    "f \<in> InternalFuns \<Longrightarrow> (g:: 'a star \<Rightarrow> nat star) \<in> InternalFuns  
     \<Longrightarrow> (\<lambda>n. f n pow g n) \<in> InternalFuns"
proof (unfold hyperpow_def)
  assume "f \<in> InternalFuns" 
  then obtain f' where F':"f = *fn* f'"
    using InternalFuns_def by auto
  moreover assume"(g:: 'a star \<Rightarrow> nat star) \<in> InternalFuns"
  moreover then obtain g' where G':"g = *fn* g'"
    using InternalFuns_def by auto
  ultimately have "(\<lambda>n. (*f2* (^)) ((*fn* f') n) ((*fn* g') n)) 
                      = (*fn* (\<lambda> i x. (f' i x) ^ (g' i x)))" 
    using starfun_n_hyperpow by auto
  thus "(\<lambda>n. (*f2* (^)) (f n) (g n)) \<in> InternalFuns" 
    using F' G' InternalFuns_starfun_n by auto
qed

lemma InternalFuns_hyperpowf [simp]: 
  "f \<in> InternalFuns \<Longrightarrow> (\<lambda>n. x pow (f n)) \<in> InternalFuns"
  by (simp add: InternalFuns_hyperpow)

lemma InternalFuns_hyperpow_simple [simp]: "(\<lambda>n. x pow n) \<in> InternalFuns"
  by simp

text\<open>NatStar.thy lemmas\<close>

lemma InternalFuns_add:
  "\<lbrakk> f \<in> InternalFuns; g \<in> InternalFuns \<rbrakk> \<Longrightarrow> (\<lambda>n. f n + g n) \<in> InternalFuns"
by (auto simp add: InternalFuns_def starfun_n_add)

lemma InternalFuns_mult:
  "\<lbrakk> f \<in> InternalFuns; g \<in> InternalFuns \<rbrakk> \<Longrightarrow> (\<lambda>n. f n * g n) \<in> InternalFuns"
by (auto simp add: InternalFuns_def starfun_n_mult)

lemma InternalFuns_diff:
  "\<lbrakk> f \<in> InternalFuns; g \<in> InternalFuns \<rbrakk> \<Longrightarrow> (\<lambda>n. f n - g n) \<in> InternalFuns"
  by (auto simp add: InternalFuns_def starfun_n_diff)

lemma InternalFuns_minus:
  "f \<in> InternalFuns  \<Longrightarrow> (\<lambda>n. - f n ) \<in> InternalFuns"
by (auto simp add: InternalFuns_def starfun_n_minus)

lemma InternalFuns_mult_const_left:
  "f \<in> InternalFuns \<Longrightarrow> (\<lambda>n. c * f n) \<in> InternalFuns"
by (force dest: InternalFuns_mult [OF InternalFuns_const_fun])

lemma InternalFuns_mult_const_right:
  "f \<in> InternalFuns \<Longrightarrow> (\<lambda>n. f n * c) \<in> InternalFuns"
by (force dest: InternalFuns_mult [OF _ InternalFuns_const_fun])

lemma InternalFuns_mult_of_hypnat [simp]:
      "X \<in> InternalFuns \<Longrightarrow> (\<lambda>n. of_hypnat n * X n) \<in> InternalFuns"
by (auto simp add: InternalFuns_def of_hypnat_def starfun_starfun_n_eq starfun_n_mult)

lemma finite_InternalSets: 
  assumes "finite X" 
  shows "X \<in> InternalSets"
proof (insert assms, induct set: finite)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case 
    by (auto intro: insert_def [THEN ssubst] intro!: InternalSets_Un)
qed

lemma InternalFuns_of_hypnat: 
  assumes "f \<in> InternalFuns"
  shows "(\<lambda>n. of_hypnat (f n)) \<in> InternalFuns"
proof (insert assms, auto simp add: InternalFuns_def)
  fix F 
  have "(\<lambda>n. of_hypnat ((*fn* (F::nat \<Rightarrow> 'a \<Rightarrow> nat)) n)) = *fn* (\<lambda>n m. of_nat(F n m))"
  proof 
    fix n
    obtain N where "(n::'a star) = star_n N"
      using star_cases by blast  
    then show " of_hypnat ((*fn* F) n) = (*fn* (\<lambda>n m. of_nat (F n m))) n"
      by (simp add: starfun_n of_hypnat_def starfun)
  qed
  then show "\<exists>Fa. (\<lambda>n. of_hypnat ((*fn* F) n)) = *fn* Fa"
    by blast
qed

lemma insert_star_n_starset_n:
  "insert (star_n X) (*sn* A) = *sn* (\<lambda>n. insert (X n) (A n))"
proof (unfold insert_def)
  have "{x. x = star_n X} \<union> *sn* A = *sn* (\<lambda>n. {X n} \<union> A n)"
    by (simp only: starset_n_singleton2 [symmetric] starset_n_Un [symmetric])
  then show "{x. x = star_n X} \<union> *sn* A = *sn* (\<lambda>n. {x. x = X n} \<union> A n)"
    by simp
qed

lemma inj_starfun_n:
  "inj (*fn* f) =  (\<forall>\<^sub>F n in \<U>. inj (f n))"
proof  
  assume "inj (*fn* f)"
  then have "\<forall>x y. (*fn* f) x = (*fn* f) y \<longrightarrow> x = y "
    by (simp add: inj_eq)
  then have "\<forall>Y Ya. \<forall>\<^sub>F n in \<U>. f n (Y n) = f n (Ya n) \<longrightarrow> Y n = Ya n"
    by (metis  FreeUltrafilterNat.eventually_imp_iff star_n_eq_iff starfun_n)
  then show "\<forall>\<^sub>F n in \<U>. inj (f n)"
    by (auto simp add: inj_def FreeUltrafilterNat.eventually_all_iff)
next
  assume "\<forall>\<^sub>F n in \<U>. inj (f n)" 
  then have eventually_inj: "\<forall>Y Ya. \<forall>\<^sub>F n in \<U>. f n (Y n) = f n (Ya n) \<longrightarrow> Y n = Ya n"
    by (simp add: eventually_mono inj_def) 
  then show "inj (*fn* f)"
  proof(auto simp add: inj_def)
    fix x y
    assume "(*fn* f) x = (*fn* f) y"
    then show "x = y"
      using eventually_inj 
      by (metis not_eventually_impI star_cases star_n_eq_iff starfun_n)
  qed
qed


lemma surj_starfun_n:
  "surj (*fn* f) =  (\<forall>\<^sub>F n in \<U>. surj (f n))"
proof  
  assume "surj (*fn* f)"
  then have "\<forall>y. \<exists>x. y = (*fn* f) x"
    by (simp add: surjD)
  then have "\<forall>Y. \<exists>Ya. \<forall>\<^sub>F n in \<U>. Y n = f n (Ya n)"
    by (metis Ifun_star_n star_cases star_n_eq_iff starfun_n_def)
  then have "\<forall>Y. \<forall>\<^sub>F n in \<U>. \<exists>x. Y n = f n x"
    by (simp add: eventually_ex)
  then show "\<forall>\<^sub>F n in \<U>. surj (f n)"
    by (auto simp add: surj_def FreeUltrafilterNat.eventually_all_iff)
next
  assume "\<forall>\<^sub>F n in \<U>. surj (f n)" 
  then have eventually_surj: "\<forall>Y. \<exists>Ya. \<forall>\<^sub>F n in \<U>. Y n = f n (Ya n)"
    by (simp add: surj_def FreeUltrafilterNat.eventually_all_iff eventually_ex)
  then show "surj (*fn* f)"
  proof(auto simp add: surj_def)
    fix y 
    show "\<exists>x. y = (*fn* f) x"
      by (metis eventually_surj star_cases star_n_eq_iff starfun_n)
  qed
qed

lemma bij_starfun_n:
  "bij (*fn* f) =  (\<forall>\<^sub>F n in \<U>. bij (f n))"
  unfolding bij_def by (simp add: eventually_conj_iff inj_starfun_n surj_starfun_n)

lemma
  assumes "bij (*fn* f)" 
  shows "(inv (*fn* f)) = *fn* (\<lambda>n. inv (f n))"
proof
  have inj_fn: "inj (*fn* f)" 
    using assms bij_betw_def by blast 
  have surj_fn: "surj (*fn* f)" 
    using assms
    by (simp add: bij_betw_def)
  fix x
  have "(*fn* f) ((*fn* (\<lambda>n. inv (f n))) x) = x"
  proof (cases x)
    case (star_n X)
    then have " \<forall>\<^sub>F n in \<U>. f n (inv (f n) (X n)) = X n"
      using surj_fn 
      by (auto simp add:  surj_starfun_n eventually_mono surj_f_inv_f)
    then show ?thesis
      by (simp add: star_n star_n_eq_iff starfun_n) 
  qed
  then show "inv (*fn* f) x = (*fn* (\<lambda>n. inv (f n))) x"
    by (metis inj_fn inv_f_eq)
qed

lemma starfun_n_o:
  "(\<lambda>i. (*fn* F) ((*fn* G) i)) = (*fn* (\<lambda>i m. F i (G i m)))"
proof (rule ext)
  fix i
  show "(*fn* F) ((*fn* G) i) = (*fn* (\<lambda>i m. F i (G i m))) i"
    by (case_tac i, auto simp add: starfun_n)
qed

lemma starfun_starfun_n_o:
  "(\<lambda>i. (*f* f) ((*fn* F) i)) = (*fn* (\<lambda>i m. f (F i m)))"
by (simp add: starfun_starfun_n_eq starfun_n_o)

lemma InternalFuns_o2:
  "f \<in> InternalFuns \<Longrightarrow> g \<in> InternalFuns \<Longrightarrow> (\<lambda>n. f (g n)) \<in> InternalFuns"
  unfolding InternalFuns_def using starfun_n_o by blast

lemma InternalFuns_abs_starfun_n [simp]: 
  "(\<lambda>i. abs ((*fn* F) i)) \<in> InternalFuns"
by (metis InternalFuns_starfun_n starfun_rabs_hrabs starfun_starfun_n_o)

lemma InternalFuns_abs: 
  "f \<in> InternalFuns \<Longrightarrow> (\<lambda>i. abs (f i)) \<in> InternalFuns"
  by (metis InternalFuns_o2 InternalFuns_starfun starfun_rabs_hrabs)

text\<open>HSEQ.thy lemmas\<close>

(* Move to NSA.thy - not used?*)
lemma LIMSEQ_0_Infinitesimal:
  assumes "X \<longlonglongrightarrow> 0" 
  shows "star_n X \<in> Infinitesimal"
proof -
  have "\<forall>N\<in>HNatInfinite. (*f* X) N \<approx> 0" 
    using assms LIMSEQ_NSLIMSEQ NSLIMSEQ_D by fastforce 
  then have "\<forall>N\<in>HNatInfinite.
            \<forall>n. hnorm ((*f* X) N) < inverse (1 + hypreal_of_nat n)"
    using mem_infmal_iff [symmetric] Infinitesimal_hypreal_of_nat_iff by auto
  then have "\<forall>n. hnorm ((*f* X) whn) < inverse (1 + hypreal_of_nat n)" by force
  then show ?thesis 
    by (auto simp add: hypnat_omega_def starfun Infinitesimal_hypreal_of_nat_iff)
qed

text\<open>Alternative definitions for exponential and real powers 
     to replace the one in the AFP session eventually.\<close>

lemma powrat_def2: "x pow\<^sub>\<rat> r = root (nat (snd(quotient_of r))) (x powi (fst(quotient_of r)))"
proof (cases "r > 0")
  case True
  then have "x ^ nat (fst (quotient_of r)) = x powi fst (quotient_of r)"
    by (metis Fract_quotient_of order_less_le power_int_nonneg_exp quotient_of_denom_pos' zero_le_Fract_iff)
  then show ?thesis
    by (simp add: True powrat_def)
next
  case False
  then have "1 / x ^ nat (- fst (quotient_of r)) = x powi fst (quotient_of r)"
    by (metis Rat_cases add.inverse_inverse linorder_not_le nat_eq_iff2 neg_less_0_iff_less normalize_stable
        power_int_minus_divide power_int_of_nat prod.sel(1) quotient_of_Fract zero_less_Fract_iff)
  then show ?thesis
    by (simp add: False powrat_def)
qed

lemma powrat_powi: "x pow\<^sub>\<rat> (of_int n) = x powi n"
  by (simp add: powrat_def2)

lemma real_root_eq_powrat_inverse': "n > 0 \<Longrightarrow> x pow\<^sub>\<rat> (1 / of_nat n) = root n x"
  by (simp add: inverse_eq_divide real_root_eq_powrat_inverse)

lemma "a powa x = lim (\<lambda>n. a pow\<^sub>\<rat> (incseq_of x n))"
  by (simp add: Lim_def powa_def)


text\<open>Next two proofs by Zuzana Frankovska\<close> 
lemma HNatInfinite_pow_real_Infinitesimal:
  assumes "0 \<le> (x::real)" and "x < 1" and "N \<in> HNatInfinite"
  shows "(star_of x) pow N \<approx> 0"
proof -
  have "(*f* (\<lambda>n. x ^ n)) N \<approx> 0" 
    using NSLIMSEQ_def LIMSEQ_realpow_zero LIMSEQ_NSLIMSEQ_iff assms by force
  thus ?thesis using starfun_pow assms by simp
qed

lemma HNatInfinite_pow_Infinitesimal:
  assumes "0 < (x::hypreal)" and "x < 1" and "\<not>(x \<approx> 1)" and "N \<in> HNatInfinite"
  shows "x pow N \<approx> 0"
proof -
  from assms have "x \<in> HFinite"
    using HInfinite_gt_zero_gt_one not_HFinite_HInfinite order.asym by blast
  then obtain x' where st_x: "star_of x' \<approx> x" 
    using st_SReal st_approx_self SReal_iff by fastforce
  then have "x' \<noteq> 1" using assms(3) by auto
  then have "x' < 1" using st_x assms(2)
    by (metis star_of_1_le star_of_approx_one_iff approx_le_bound less_imp_le not_less)
  then  obtain y where y: "x' < y \<and> y < 1" 
    using dense by blast
  then have x_less_y: "x < star_of y"
    using st_x 
    by (metis Infinitesimal_add_hypreal_of_real_less approx_sym bex_Infinitesimal_iff2) 
  then have "x pow N \<le> star_of y pow N"
    by (simp add: assms(1) hyperpow_le less_imp_le)
  moreover have "0 < x pow N"
    by (simp add: assms(1) hyperpow_gt_zero)
  moreover have "star_of y pow N \<approx> 0"
    using assms(1,4) HNatInfinite_pow_real_Infinitesimal x_less_y y by auto
  ultimately show ?thesis
    using approx_le_bound approx_trans3 less_imp_le by blast 
qed 

lemma Infinitesimal_hyperpow_HNatInfinite:
  assumes "hnorm (x::'a::real_normed_div_algebra star) < 1"
  and "N \<in> HNatInfinite"
  and "\<not>(hnorm x \<approx> 1)"
shows "x pow N \<in> Infinitesimal"
proof -
  have "hnorm x pow N \<approx> 0" 
    using HNatInfinite_pow_Infinitesimal assms
    by force
  then show ?thesis
    by (metis Infinitesimal_hnorm_iff hnorm_hyperpow mem_infmal_iff) 
qed

text\<open>HSeries.thy lemmas\<close>

lemma NSsums_sumhr_HNatInfinite_approx_iff:
  "(f NSsums s) = (\<forall>N\<in>HNatInfinite. sumhr(0, N, f) \<approx> of_real s)"
by (simp add: NSsums_def sumhr_app NSLIMSEQ_def star_of_zero [symmetric] 
       atLeast0LessThan del: star_of_zero)

lemma sumhr_approx: 
  "sumhr (0, M, f) \<approx> sumhr (0, N, f) \<Longrightarrow> sumhr (M, N, f) \<approx> 0"
by (metis approx_zero_abs_zero_iff sumhr_hrabs_approx)

end
