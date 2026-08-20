(*  Title:  HyperBinomial.thy
    Author: Jacques D. Fleuriot, University of Edinburgh, 2026
*)

section\<open>The hyperfactorial and hyperbinomial coefficient functions\<close> 

theory HyperBinomial
imports FallFactorial HyperSum HyperArchimedean Internal
begin

subsection \<open>The hyperbinomial coefficients\<close>

definition
  hchoose :: "nat star \<Rightarrow> nat star \<Rightarrow> nat star"  (infixl "hchoose" 65) where
  hyperbinomial_def [transfer_unfold]:    "(hchoose) = *f2* (choose)"

lemma star_choose: "(star_n (N::nat\<Rightarrow>nat)) hchoose (star_n K) = star_n (\<lambda>n. N n choose K n)"
by (metis hyperbinomial_def starfun2_star_n)

lemma star_of_choose [simp]: "star_of (n choose k) = (star_of n) hchoose (star_of k)"
by transfer simp

lemma star_choose_zero_hypnat [simp]: "\<And>n. (n::hypnat) hchoose 0 = 1"
by transfer simp

lemma zero_star_choose_hypnat [simp]: "\<And>n k. n < (k::hypnat) \<Longrightarrow> n hchoose k = 0"
by transfer simp

lemma star_choose_reduce_hypnat:
  "\<And>n k. \<lbrakk>0 < (n::hypnat); 0 < k\<rbrakk> 
          \<Longrightarrow> n hchoose k = n - 1 hchoose k + (n - 1 hchoose (k - 1))"
by transfer (simp add: choose_reduce_nat)

lemma star_choose_plus_one_hypnat: "\<And>n k. ((n::hypnat) + 1) hchoose (k + 1) = 
    (n hchoose (k + 1)) + (n hchoose k)"
by transfer simp

lemma star_choose_hSuc_hypnat: "\<And>n k. (hSuc n) hchoose (hSuc k) = 
    (n hchoose (hSuc k)) + (n hchoose k)"
by transfer simp

lemma star_choose_self_hypnat [simp]: "\<And>n. ((n::hypnat) hchoose n) = 1"
by transfer simp

lemma star_choose_one_hypnat [simp]: "\<And>n. (n::hypnat) hchoose 1 = n"
by transfer simp

lemma star_plus_one_choose_self_hypnat [simp]: "\<And>n. (n::hypnat) + 1 hchoose n = n + 1"
by transfer simp

lemma hSuc_choose_self_hypnat [simp]: "\<And>n. (hSuc n) hchoose n = hSuc n"
by transfer simp

lemma choose_pos_nat [rule_format]: "\<And>k n. k <= (n::hypnat) \<Longrightarrow> (n hchoose k) > 0"
by transfer simp 

subsection \<open>The hyperfactorial function\<close>

definition
  hfact_def [transfer_unfold]:    "hfact \<equiv> *f* fact"

lemma star_choose_altdef_hypnat: 
  "\<And>n k. (k::hypnat) \<le> n \<Longrightarrow> n hchoose k = hfact n div (hfact k * hfact (n - k))"
  by transfer (blast intro: binomial_fact') 

lemma star_choose_dvd_hypnat: "\<And>n k. (k::hypnat) \<le> n \<Longrightarrow> hfact k * hfact (n - k) dvd hfact n"
by transfer (metis binomial_fact_lemma dvdI of_nat_fact of_nat_mult)

lemma hfact_of_nat: "hfact (hypnat_of_nat n) = of_nat (fact n)"
  by (simp add: hfact_def star_of_nat_def)

lemma HFinite_hfact_of_nat [simp]:
  "of_hypnat (hfact (hypnat_of_nat n)) \<in> HFinite"
  by (simp add: hfact_of_nat of_hypnat_def)

lemma hfact_nat_in_Nats: "n \<in> \<nat> \<Longrightarrow> hfact (n::hypnat)\<in> \<nat> "
  by (metis Nats_hypnat_of_nat_iff fact_in_Nats hfact_of_nat of_nat_fact)
                                      
lemma star_choose_le_hyperpow:
   "\<And>r n. r \<le> n \<Longrightarrow> n hchoose r \<le> n pow r"
by transfer (rule binomial_le_pow)


text \<open>The binomial theorem extended to hyperreal and hypernaturals, 
      characterized via hyperfinite sums\<close> 

lemma Iset_interval: 
     "Iset (star_n (\<lambda>n. {0..X n})) = {0..star_n X}"
  using starset_n_atLeast_zero_AtMost starset_n_def by blast

lemma n_star_interval_ultra: "eventually (\<lambda>n. (*ns* {0..star_n X}) n = {0..X n}) \<U>"
  by (simp add: Iset_interval [symmetric] n_starset_eq_ultra)

lemma lemma_starfun_n_binomial:
  "*fn* (\<lambda>n k. of_nat (Xb n choose k) * X n ^ k * Xa n ^ (Xb n - k)) = 
        (\<lambda>K. of_hypnat ((*f2* (choose)) (star_n Xb) K) * (*f2* (^)) (star_n X) K *
             (*f2* (^)) (star_n Xa) (star_n Xb - K))"
proof 
  fix K 
  show "(*fn* (\<lambda>n k. of_nat (Xb n choose k) * X n ^ k * Xa n ^ (Xb n - k))) K =
         of_hypnat ((*f2* (choose)) (star_n Xb) K) * (*f2* (^)) (star_n X) K *
         (*f2* (^)) (star_n Xa) (star_n Xb - K)"
  proof (cases K)
    case (star_n X)
    then show ?thesis
      by (simp add: starfun2_star_n star_n_diff of_hypnat_def starfun_star_n star_n_mult starfun_n)
  qed
qed

subsection \<open>The hyperbinomial theorem\<close>

lemma hyperbinomial_ring:
      "(a + b::'a::{comm_semiring_1,semiring_1_cancel} star) pow N = 
                hypersum (\<lambda>K. of_hypnat (N hchoose K) * a pow K * b pow (N - K)) {0..N}"
proof -
  obtain As Bs Ns where abN: "a = star_n As" "b = star_n Bs" "N = star_n Ns"
    by (meson star_cases)
  then have star_n_sum: 
          "\<forall>f. star_n (\<lambda>n. sum ((*nf* *fn* f) n) ((*ns* {0..star_n Ns}) n)) = 
               star_n (\<lambda>n. sum (f n) {0..Ns n})"
    by (metis (full_types) hypersum hypersum_def starset_n_atLeast_zero_AtMost)
  show ?thesis 
    by (simp add: abN star_n_sum hypersum_def hyperpow_def hyperbinomial_def atLeast0AtMost
                  lemma_starfun_n_binomial [symmetric] starfun2_star_n star_n_add binomial_ring)
qed

lemma hyperbinomial_simple: 
  "(1 + a::'a::{comm_semiring_1,semiring_1_cancel} star) pow N = 
           hypersum (\<lambda>i. of_hypnat (N hchoose i) * a pow i) {0..N}"
proof (subst add.commute)
  show "(a + 1) pow N = hypersum (\<lambda>i. of_hypnat (N hchoose i) * a pow i) {0..N}"
    by (simp add: hyperbinomial_ring)
qed

lemma lemma_InternalFuns_hyperbinomial:
  "hypreal_of_hypnat (star_n X hchoose star_n Xc) *
    star_n Xa pow star_n Xc * star_n Xb pow (star_n X - star_n Xc) =
   star_n (\<lambda>n. real (X n choose Xc n) * Xa n ^ Xc n * Xb n ^ (X n - Xc n))"
  by (simp add: starfun_n hyperpow star_choose of_hypnat_def 
        starfun star_mult_def star_diff_def starfun2_star_n)

lemma InternalFuns_hyperbinomial [simp]: 
    "(\<lambda>K. hypreal_of_hypnat (N hchoose K) * a pow K * b pow (N - K)) \<in> InternalFuns"
proof (simp add: InternalFuns_def)
  obtain As Bs Ns where AbN: "a = star_n As" "b = star_n Bs" "N = star_n Ns" 
    by (meson star_cases)
   show "\<exists>F. (\<lambda>K. hypreal_of_hypnat (N hchoose K) * a pow K * b pow (N - K)) = *fn* F"
    proof (rule exI [of _ "(\<lambda>n k. real (Ns n choose k) * As n ^ k * Bs n ^ (Ns n - k))"], rule ext)
      fix K
      obtain Ks where "(K::nat star) = star_n Ks"
        using star_cases by blast 
      then show "hypreal_of_hypnat (N hchoose K) * a pow K * b pow (N - K) =
                  (*fn* (\<lambda>n k. real (Ns n choose k) * As n ^ k *  Bs n ^ (Ns n - k))) K"
        by (simp add: AbN hyperbinomial_def hyperpow_def lemma_starfun_n_binomial)
    qed
  qed

subsection\<open>Nonstandard falling factorial\<close>

definition 
    hfallfactpow :: "'a::comm_ring_1 star \<Rightarrow> hypnat \<Rightarrow> 'a star" where
    [transfer_unfold]: "hfallfactpow a n = (*f2* fallfactpow) a n"

lemma hfallfactpow_0[simp]: "\<And>a. hfallfactpow a 0 = 1" 
by transfer simp

lemma hfallfactpow_1[simp]: "\<And>a. hfallfactpow a 1 = a" by transfer simp
lemma hfallfactpow_hSuc0[simp]: "\<And>a. hfallfactpow a (hSuc 0) = a" by transfer simp

lemma hfallfactpow_hSuc: "\<And>a n. hfallfactpow a (hSuc n) = hfallfactpow a n * (a - of_hypnat n)"
by transfer (simp add: fallfactpow_Suc)

lemma hfallfactpow_hSuc': "hfallfactpow a (n + 1) = hfallfactpow a n * (a - of_hypnat n)"
by (metis hSuc_eq_add_one hfallfactpow_hSuc)

lemma hfallfactpow_rec: "\<And>a n. hfallfactpow a (hSuc n) = a * hfallfactpow (a - 1) n"
by transfer (simp add: fallfactpow_rec)

lemma hfallfactpow_rec': "\<And>a n. hfallfactpow a (n + 1) = a * hfallfactpow (a - 1) n"
by (metis hSuc_eq_add_one hfallfactpow_rec)

lemma hfallfactpow_base_zero[simp]: "\<And>n. hfallfactpow 0 (hSuc n) = 0"
by transfer simp

lemma hfallfactpow_base_zero'[simp]: "\<And>n. hfallfactpow 0 (n + 1) = 0"
by (metis hSuc_eq_add_one hfallfactpow_base_zero)

lemma hfallfactpow_fact: "\<And>n. of_hypnat(hfact n) =  hfallfactpow (of_hypnat n) n"
by transfer (simp add: fallfactpow_fact)

lemma hfallfactpow_of_nat_eq_0_lemma:
  "\<And>k n. k > n \<Longrightarrow> hfallfactpow (of_hypnat n :: 'a:: idom star) k = 0"
by transfer simp

lemma hyperbinomial_hfallfactpow: 
 "\<And>k n. of_hypnat (n hchoose k) =
  (hfallfactpow (of_hypnat n) k ::'a::{field_char_0} star)/hfact k"
by transfer (metis binomial_fallfactpow_altdef_of_nat)

lemma hyperbinomial3:
      "(a + b::'a::{field_char_0} star) pow n = 
                hypersum (\<lambda>k. hfallfactpow (of_hypnat n) k / hfact k * a pow k * b pow (n - k)) {0..n}"
by (simp add: hyperbinomial_ring hyperbinomial_hfallfactpow)

lemma hfallfactpow_le_power_self [simp]:
  "\<And>k. hfallfactpow (of_hypnat k ::'a::{linordered_idom} star) k \<le> of_hypnat k pow k"
by transfer (metis fallfactpow_le_power_self)

lemma hfallfactpow_le_hyperpow:
  "\<And>k j. of_hypnat k \<le> j \<Longrightarrow> hfallfactpow (j::'a::{linordered_idom} star) k \<le> j pow k"
by transfer (metis fallfactpow_le_power)

lemma hfallfactpow_ge_zero [simp]:
  "\<And>k n. hfallfactpow (of_hypnat n) k \<ge> (0::'a::linordered_idom star)"
by transfer simp

(* Not proven in the Isabelle distribution? *)
lemma fact_Suc_ge_two_pow: "fact (n + 1) \<ge> (2::nat)^n"
proof (induct n)
  case 0 thus ?case 
    by simp
next
  case (Suc n)
  have "fact (Suc n + 1) = (Suc n + 1) * fact (Suc n)"
    by simp
  also have "...  \<ge> 2 * fact (Suc n)"
    by (simp add: mult_le_mono)
  also have "... \<ge> 2 * 2^n"
    using Suc by simp
  then show ?case
    by simp 
qed

lemma hfact_hSuc_ge_two_pow:
  "\<And>n. (hfact (n + 1) :: hypreal) \<ge> 2 pow n"
  by transfer (metis fact_Suc_ge_two_pow numeral_power_le_of_nat_cancel_iff of_nat_fact)
 
lemma HInfinite_diff_of_nat_divide_approx_one:
  assumes "x \<in> HInfinite" 
  shows "(x - of_nat k)/x \<approx> (1::'a::real_normed_field star)"
proof (cases "x=0")
  case True
  then show ?thesis
    using assms zero_not_HInfinite by blast 
next
  case False
  then have "(x - of_nat k)/x = 1 - of_nat k/x"
    by (simp add: diff_divide_eq_iff)
  moreover have "of_nat k/x \<approx> 0"
    by (metis HFinite_star_of Infinitesimal_HInfinite_divide assms mem_infmal_iff star_of_nat_def)      
  ultimately show ?thesis
    using approx_diff by force 
qed
  
lemma HInfinite_hfallfactpow_divide_hrealpow:
  assumes "j \<in> HInfinite"
  shows "hfallfactpow j (of_nat k)/(j ^ k) \<approx> (1::'a::real_normed_field star)" 
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  assume IH: "hfallfactpow j (of_nat k) / j ^ k \<approx> 1"
  have "(j - of_nat k)/ j \<approx> 1"
    by (simp add: HInfinite_diff_of_nat_divide_approx_one assms)
  then have "(hfallfactpow j (of_nat k) / j ^ k) * (j - of_nat k)/ j \<approx> 1"
    using IH approx_mult_HFinite
    by (metis (no_types, lifting) HFinite_1 mult.left_neutral times_divide_eq_right) 
  then show ?case 
    by (auto simp add: hfallfactpow_hSuc' mult.commute) 
qed

lemma HInfinite_hfallfactpow_divide_hyperpow_of_nat:
  "j \<in> HInfinite 
   \<Longrightarrow> hfallfactpow j (of_nat k)/(j pow of_nat k) \<approx> (1::'a::real_normed_field star)"
by (metis HInfinite_hfallfactpow_divide_hrealpow hyperpow_of_nat) 

lemma HInfinite_hfallfactpow_divide_hyperpow_Nats:
"\<lbrakk> k\<in>\<nat>; j\<in>HInfinite \<rbrakk> \<Longrightarrow> hfallfactpow j k/(j pow k) \<approx> (1::'a::real_normed_field star)"
by (metis HInfinite_hfallfactpow_divide_hyperpow_of_nat Nats_cases) 

text\<open>This is the one that we want to deal with Euler's claim that $(j - 1)(j - 2)...(j -k)/j^k = 1!$\<close>
lemma HNatInfinite_hfallfactpow_divide_hyperpow_of_nat:
  "j \<in> HNatInfinite 
   \<Longrightarrow> hfallfactpow (of_hypnat j) (of_nat k)/(of_hypnat j pow of_nat k) \<approx> (1::'a::real_normed_field star)"
by (metis HInfinite_hfallfactpow_divide_hyperpow_of_nat HNatInfinite_of_hypnat_HInfinite) 

lemma hfallfactpow_base_starfun2:
  "hfallfactpow a = (*f2* fallfactpow) a"
proof 
  fix x
  show "hfallfactpow a x = (*f2* fallfactpow) a x"
    by (simp add: hfallfactpow_def)
qed

lemma InternalFuns_hfallfactpow [simp]: "hfallfactpow a \<in> InternalFuns"
  by (simp add: hfallfactpow_base_starfun2)

lemma hfallfactpow_starfun2:
  "hfallfactpow = *f2* fallfactpow"
proof (rule ext)
  fix x 
  show "hfallfactpow (x::'a star)  = (*f2* fallfactpow) x "
    by (simp add: hfallfactpow_base_starfun2) 
qed

lemma InternalFuns2_hfallfactpow [simp]: "hfallfactpow \<in> InternalFuns2"
  by (auto simp add: InternalFuns2_def hfallfactpow_starfun2 starfun2_eq_starfun2n)

lemma InternalFuns2_hfallfactpow_base [simp]: "(\<lambda>n. hfallfactpow a) \<in> InternalFuns2"
proof (cases a, simp add: InternalFuns2_def)
  case (star_n X)
  show "\<exists>F. (\<lambda>n. hfallfactpow (star_n X)) = *fn2* F"
  proof(rule exI [where x="(\<lambda>m n. fallfactpow (X m))"], (rule ext)+)
    fix n::"'c star" and x
    show "hfallfactpow (star_n X) x =
           (*fn2* (\<lambda>m n. fallfactpow (X m))) n x"
    proof (cases n, cases x)
      fix Xa Xaa
      assume nx: "n = star_n Xa" "x = star_n Xaa"
      then show ?thesis 
        by (auto simp add: hfallfactpow_def starfun2_star_n starfun2_n)
    qed
  qed
qed
  
lemma hfallfactpow: "hfallfactpow (star_n X) (star_n Y) = star_n (\<lambda>n. fallfactpow (X n) (Y n))"
by (auto simp add:  hfallfactpow_def starfun2_star_n)

lemma InternalFuns_hfallfactpow_fun:
  assumes "f \<in> InternalFuns" 
  shows "(\<lambda>n. hfallfactpow a (f n)) \<in> InternalFuns"
proof (insert assms, cases a, simp add: InternalFuns_def)
  case (star_n X)
  show "\<exists>F. (\<lambda>n. hfallfactpow (star_n X) (f n)) = *fn* F"
    by (metis (no_types) InternalFuns_hfallfactpow InternalFuns_starfun_n_starfun assms starfun_n_o)
qed

lemma InternalFuns_hfallfactpow_divide:
  "(\<lambda>k. (hfallfactpow (of_hypnat j) k/(of_hypnat j pow k)) :: 'a :: {comm_ring_1, division_ring} star ) \<in> InternalFuns"
  by (simp add: InternalFuns_divide)

lemma hfact:
  "hfact (star_n X) = star_n(\<lambda>n. fact (X n))"
by (auto simp add: hfact_def starfun star_n_eq_iff)

lemma InternalFuns_hfact_fun [simp]: 
  "f \<in> InternalFuns \<Longrightarrow> (\<lambda>n. hfact (f n)) \<in> InternalFuns"
  by (metis (no_types) InternalFuns_starfun InternalFuns_starfun_n InternalFuns_starfun_n_starfun 
      hfact_def starfun_n_o)

lemma InternalFuns_hfact [simp]: "(\<lambda>n. hfact n) \<in> InternalFuns"
by (simp add: hfact_def)

lemma InternalFuns2_hfact [simp]: "(\<lambda>m. hfact) \<in> InternalFuns2"
proof (simp add: InternalFuns2_def hfact_def)
  show "\<exists>F. (\<lambda>m. *f* fact) = *fn2* F"
  proof(rule exI [where x="\<lambda>m n p. fact p"], (rule ext)+)
    fix m::"'c star" and x 
    show "(*f* fact) x = (*fn2* (\<lambda>m n. fact)) m x"
    proof(cases m, cases x) 
      fix X Xa
      assume "m = star_n X" "x = star_n Xa"
      then show ?thesis 
        by (auto simp add:  starfun2_n starfun)
    qed
  qed
qed

lemma Infinitesimal_hyperpow_star_of_less_one:
  assumes "hnorm ((star_of x)::'a::real_normed_algebra_1 star) < 1"
          "n \<in> HNatInfinite" 
  shows "((star_of x)::'a::real_normed_algebra_1 star) pow n \<in> Infinitesimal"
proof -
  have "(^) x \<longlonglongrightarrow> 0" using LIMSEQ_power_zero 
    using assms star_of_less_1 by fastforce 
  then have "star_of x pow n \<approx> 0"
    by (metis LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_def assms(2) star_zero_def starfun_power) 
  then show ?thesis
    by (simp add: mem_infmal_iff)
qed

(* not used  *)
lemma InternalFuns_abs_pow_fun: 
  assumes Int_f: "f \<in> InternalFuns" shows "(\<lambda>n. \<bar>x pow f n\<bar>) \<in> InternalFuns"
  by (simp add: InternalFuns_abs  assms)

lemma hfact_gt_zero [simp]: "\<And>n. (0 :: 'a :: linordered_semidom star) < hfact (n::hypnat)"
by transfer simp

lemma hypnat_fact_zero [simp] : "hfact (0 :: nat star) = 1"
by transfer simp

subsection\<open>Nonstandard version of Pochammer's symbol i.e. the rising factorial\<close>

definition
  hpochhammer :: "'a::comm_semiring_1 star \<Rightarrow> hypnat \<Rightarrow> 'a star" where
  [transfer_unfold]: "hpochhammer x n = (*f2* pochhammer) x n"

(* Move to LibBinomial? *)
lemma fact_fact_pochhammer_mult:
  "n \<ge> k \<Longrightarrow> fact n = (fact k) * pochhammer (k + 1) (n - k)"
  by (metis add.commute id_apply le_add_diff_inverse of_nat_eq_id pochhammer_fact pochhammer_product')

lemma fact_fact_hpochhammer_mult:
  "\<And>n k. n \<ge> k \<Longrightarrow> hfact n = (hfact k) * hpochhammer (k + 1) (n - k)"
by transfer (metis fact_fact_pochhammer_mult)

lemma power_le_pochhammer:
  assumes "0 \<le> x" 
  shows "(x ^ n :: 'a :: linordered_semidom) \<le> pochhammer x n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "x ^ n * x \<le> pochhammer x n * (x + of_nat n)"
    by (simp add: assms mult_mono')       
  then show ?case
    by (simp add: mult.commute pochhammer_Suc)
qed 

lemma hyperpow_le_hpochhammer:
  "\<And>x n. 0 \<le> x \<Longrightarrow> (x pow n :: 'a :: linordered_semidom star) \<le> hpochhammer x n"
by transfer (metis power_le_pochhammer)

lemma of_nat_pochhammer_of_nat:
  assumes "0 \<le> z" shows "of_nat (pochhammer (nat z) n) = pochhammer (of_int z) n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by (simp add: pochhammer_Suc assms)
qed

lemma of_hypnat_hpochhammer_of_hypnat:
  "\<And>z n. 0 \<le> z \<Longrightarrow> of_hypnat (hpochhammer (hypnat z) n) = hpochhammer (of_hypint z) n"
by transfer (metis of_nat_pochhammer_of_nat)

lemma hyperpow_divide_fact_le_lemma':
  assumes "y \<in> HFinite" 
  and "(0 :: real star) < y" 
  and "hypnat (hfloor y + 1) \<le> n"
  shows "\<bar>y pow n\<bar> / hypreal_of_hypnat (hfact n)
         \<le> y pow n /
            ((hypreal_of_hypint (hfloor y) + 2) pow
             (n - hypnat (hfloor y + 1)) *
             hypreal_of_hypnat (hfact (hypnat (hfloor y + 1))))"
proof - 
  have hpow_gt_zero: "0 < y pow n"
    by (simp add: assms(2) hyperpow_gt_zero)
  have hfl_y_2_ge_0: "0 < hypreal_of_hypint (hfloor y) + 2"
    by (simp add: add_nonneg_pos assms(2) less_imp_le)
  have hfl_y_ge0: "0 \<le> hfloor y"
    by (simp add: assms(2) less_imp_le)
  then have "hpochhammer (hypreal_of_hypint (hfloor y) + 2)
         (n - hypnat (hfloor y + 1))
        \<le> hypreal_of_hypnat
            (hpochhammer (hypnat (hfloor y + 1) + 1)
              (n - hypnat (hfloor y + 1)))"
    using hypnat_add_one of_hypint_add_one of_hypnat_hpochhammer_of_hypnat
    by (metis (no_types, lifting) add_nonneg_nonneg add.assoc le_less one_add_one zero_less_one)
  moreover have "(hypreal_of_hypint (hfloor y) + 2) pow (n - hypnat (hfloor y + 1)) 
                 \<le> hpochhammer (hypreal_of_hypint (hfloor y) + 2)
                      (n - hypnat (hfloor y + 1))"
    using hfl_y_2_ge_0 hyperpow_le_hpochhammer less_imp_le by blast
  ultimately have "(hypreal_of_hypint (hfloor y) + 2) pow (n - hypnat (hfloor y + 1))
                    \<le> hypreal_of_hypnat (hpochhammer (hypnat (hfloor y + 1) + 1) (n - hypnat (hfloor y + 1)))"
    by linarith
  then have "(hypreal_of_hypint (hfloor y) + 2) pow (n - hypnat (hfloor y + 1)) *
              hypreal_of_hypnat (hfact (hypnat (hfloor y + 1)))
             \<le> hypreal_of_hypnat (hfact n)"
    using fact_fact_hpochhammer_mult [of "hypnat (hfloor y + 1)" n, OF assms(3)]
    by simp
  moreover have "0 < (hypreal_of_hypint (hfloor y) + 2) pow
         (n - hypnat (hfloor y + 1)) *
         hypreal_of_hypnat (hfact (hypnat (hfloor y + 1)))"
  proof -
    have "hypreal_of_hypnat (hfact (hypnat (hfloor y + 1))) > 0"
      using hfact_gt_zero of_hypnat_0_less_iff by blast
    moreover have "(hypreal_of_hypint (hfloor y) + 2) pow (n - hypnat (hfloor y + 1)) > 0"
      by (simp add: hfl_y_2_ge_0 hyperpow_gt_zero)
    ultimately show ?thesis
      using zero_less_mult_iff by blast 
  qed
   ultimately show ?thesis
     by (simp add: divide_left_mono hpow_gt_zero less_imp_le) 
 qed

(* Needed? *)
lemma hfloor_one_minus_epsilon: "hfloor(1 - \<epsilon>) = 0"
proof (rule hfloor_unique)
  have "\<epsilon> < 1" using Infinitesimal_less_SReal by auto
  then show "hypreal_of_hypint 0 \<le> 1 - \<epsilon>" by simp 
next 
  show "1 - \<epsilon> < hypreal_of_hypint 0 + 1"
    by (simp add: epsilon_gt_zero)
qed

lemma hypreal_hfloor_approx_zero [simp]: "\<lbrakk> (x::hypreal) \<approx> 0; x > 0 \<rbrakk> \<Longrightarrow> hfloor x = 0"
by (metis Infinitesimal_less_SReal Reals_1 hfloor_less_zero le_less less_add_one 
    less_add_same_cancel1 mem_infmal_iff not_less zero_less_hfloor)

lemma hfloor_approx_zero [simp]: "x \<approx> 0 \<Longrightarrow> hfloor (hnorm x) = 0"
by (metis approx_hnorm hfloor_zero hnorm_eq_zero hypreal_hfloor_approx_zero zero_less_hnorm_iff)


lemma InternalFuns_expf_term' [simp]:
  "(\<lambda>N. y pow N / hypreal_of_hypnat (hfact N)) \<in> InternalFuns"
  by (simp add: InternalFuns_divide InternalFuns_of_hypnat)

lemma InternalFuns_expf_term [simp]:
  "(\<lambda>N. y pow N / (hfact N :: real star)) \<in> InternalFuns"
  by (simp add: InternalFuns_divide)

lemma HyperSummable_hyperpow_divide_fact_Infinitesimal:
  assumes HFinite_y: "(y::hypreal) \<in> HFinite" 
  and y_gt_0: "y > 0"
  and y_approx_0: "y \<approx> 0"
shows "HyperSummable (\<lambda>N. y pow N/of_hypnat(hfact N))"
proof -
  have "(\<lambda>N. y pow N / hypreal_of_hypnat (hfact N)) \<in> InternalFuns"
    by simp
  moreover have "(\<lambda>n. y pow hypnat (hfloor y) /
             hypreal_of_hypint (hfact (hypnat (hfloor y))) *
             ((y / hypreal_of_hypint (hfloor y + 1)) pow n /
              (y / hypreal_of_hypint (hfloor y + 1)) pow
              hypnat (hfloor y)))
        \<in> InternalFuns"
    using y_gt_0 y_approx_0 by simp
  moreover have "\<exists>k\<in>\<nat>. \<forall>n\<ge>k. hnorm (y pow n / hypreal_of_hypnat (hfact n))
                     \<le> y pow hypnat (hfloor y) /
                        hypreal_of_hypint
                         (hfact (hypnat (hfloor y))) *
                        ((y / hypreal_of_hypint (hfloor y + 1)) pow
                         n /
                         (y / hypreal_of_hypint (hfloor y + 1)) pow
                         hypnat (hfloor y))"
  proof (rule_tac bexI [of _ "hypnat (hfloor y)"],safe)
    fix n
    assume "hypnat (hfloor y) \<le> n"
    have "0 < y pow n"
      by (simp add: hyperpow_gt_zero y_gt_0) 
    moreover have " 1 \<le> hypreal_of_hypnat (hfact n)"
      using zero_less_hfloor by fastforce
    ultimately have "y pow n / hypreal_of_hypnat (hfact n) \<le> y pow n"
      using divide_left_mono by fastforce
    then show "hnorm (y pow n / hypreal_of_hypnat (hfact n))
         \<le> y pow hypnat (hfloor y) /
            hypreal_of_hypint (hfact (hypnat (hfloor y))) *
            ((y / hypreal_of_hypint (hfloor y + 1)) pow n /
             (y / hypreal_of_hypint (hfloor y + 1)) pow
             hypnat (hfloor y))"
      by (simp add: \<open>0 < y pow n\<close> abs_of_pos y_approx_0 y_gt_0)
   next
    show "hypnat (hfloor y) \<in> \<nat>"
      using HFinite_hypnat_hfloor_Nat HFinite_y by blast
  qed
  moreover have " HyperSummable (\<lambda>n. y pow hypnat (hfloor y) /
             hypreal_of_hypint (hfact (hypnat (hfloor y))) *
             ((y / hypreal_of_hypint (hfloor y + 1)) pow n /
              (y / hypreal_of_hypint (hfloor y + 1)) pow
              hypnat (hfloor y)))"
  proof -
    have "(\<lambda>n. (y / hypreal_of_hypint (hfloor y + 1)) pow n /
             (y / hypreal_of_hypint (hfloor y + 1)) pow
             hypnat (hfloor y)) \<in> InternalFuns"
      using  y_gt_0 y_approx_0 by auto
    moreover have "y pow hypnat (hfloor y) /
        hypreal_of_hypint (hfact (hypnat (hfloor y))) \<in> HFinite"
      using y_approx_0 y_gt_0 by auto
    moreover have "(pow) (y / hypreal_of_hypint (hfloor y + 1)) \<in> InternalFuns"
      using InternalFuns_hyperpow_simple by blast
    moreover have "HyperSummable ((pow) (y / hypreal_of_hypint (hfloor y + 1)))"
      by (metis HyperSummable_geometric abs_of_pos add_cancel_right_left approx_trans3 div_by_1 
          hfloor_correct hfloor_one hypreal_hfloor_approx_zero hypreal_hnorm_def of_hypint_1 
          one_neq_zero y_approx_0 y_gt_0 zero_less_one)
    moreover have "(y / hypreal_of_hypint (hfloor y + 1)) pow hypnat (hfloor y) \<notin> Infinitesimal"
      using y_approx_0 y_gt_0 by auto
    ultimately show ?thesis
      using HyperSummable_HFinite_mult_left HyperSummable_divide by blast
  qed
  ultimately show ?thesis
    using HyperSummable_comparison_test by blast
qed

lemma HyperSummable_hyperpow_divide_fact_not_Infinitesimal:
  assumes HFinite_y: "(y::hypreal) \<in> HFinite" 
  and y_gt_0: "y > 0"
  and y_not_approx_0: "\<not> y \<approx> 0"
  shows "HyperSummable (\<lambda>N. y pow N/of_hypnat(hfact N))"
proof -
  have "(\<lambda>N. y pow N / hypreal_of_hypnat (hfact N)) \<in> InternalFuns"
    by simp
  moreover have "(\<lambda>n. y pow hypnat (hfloor y + 1) /
             hypreal_of_hypnat (hfact (hypnat (hfloor y + 1))) *
             ((y / hypreal_of_hypint (hfloor y + 2)) pow n /
              (y / hypreal_of_hypint (hfloor y + 2)) pow
              hypnat (hfloor y + 1))) \<in> InternalFuns"
    using y_gt_0 by (auto simp add: hyperpow_divide hyperpow_diff_cancel InternalFuns_divide 
         InternalFuns_mult_const_right InternalFuns_mult_const_left)
  moreover have "\<exists>k\<in>\<nat>. \<forall>n\<ge>k. hnorm (y pow n / hypreal_of_hypnat (hfact n))
                     \<le> y pow hypnat (hfloor y + 1) /
                        hypreal_of_hypnat
                         (hfact (hypnat (hfloor y + 1))) *
                        ((y / hypreal_of_hypint (hfloor y + 2)) pow
                         n /
                         (y / hypreal_of_hypint (hfloor y + 2)) pow
                         hypnat (hfloor y + 1))"
  proof (rule bexI [of _ "hypnat ((hfloor y) + 1)"],safe)
    fix n
    have "y / hypreal_of_hypint (hfloor y + 2) \<noteq> 0"
      by (metis divide_eq_0_iff le_less less_add_same_cancel1 not_less of_hypint_0_eq_iff y_gt_0 
          zero_le_hfloor zero_less_numeral)
     moreover assume  ge_floor: "hypnat (hfloor y + 1) \<le> n"
     ultimately have "(y / hypreal_of_hypint (hfloor y + 2)) pow n /
          (y / hypreal_of_hypint (hfloor y + 2)) pow
          hypnat (hfloor y + 1) =
          (y / hypreal_of_hypint (hfloor y + 2)) pow
          (n - hypnat (hfloor y + 1))"
       using hyperpow_diff 
       by blast
     moreover have "\<bar>y pow n\<bar> / hypreal_of_hypnat (hfact n)
        \<le> y pow hypnat (hfloor y + 1) *
           (y / (hypreal_of_hypint (hfloor y) + 2)) pow
           (n - hypnat (hfloor y + 1)) /
           hypreal_of_hypnat (hfact (hypnat (hfloor y + 1)))"
       by (simp add: HFinite_y ge_floor hyperpow_diff_cancel hyperpow_divide hyperpow_divide_fact_le_lemma' y_gt_0)
     ultimately show " hnorm (y pow n / hypreal_of_hypnat (hfact n))
         \<le> y pow hypnat (hfloor y + 1) /
            hypreal_of_hypnat (hfact (hypnat (hfloor y + 1))) *
            ((y / hypreal_of_hypint (hfloor y + 2)) pow n /
             (y / hypreal_of_hypint (hfloor y + 2)) pow
             hypnat (hfloor y + 1))"
       by simp
   next
     show "hypnat (hfloor y + 1) \<in> \<nat>"
      using HFinite_hypnat_hfloor_Nat HFinite_y
      by (metis HFinite_1 HFinite_add hfloor_add_one)
  qed
  moreover have "(\<lambda>n. (y / hypreal_of_hypint (hfloor y + 2)) pow n /
         (y / hypreal_of_hypint (hfloor y + 2)) pow
         hypnat (hfloor y + 1))
    \<in> InternalFuns"
    using InternalFuns_const_fun InternalFuns_divide InternalFuns_hyperpow_simple 
    by blast
  moreover have "y pow hypnat (hfloor y + 1) /
                 hypreal_of_hypnat (hfact (hypnat (hfloor y + 1))) \<in> HFinite"
    using HFinite_divide hypnat_add_distrib HFinite_hyperpow_HFinite 
          HFinite_hypnat_hfloor_Nat neq_iff  assms  hfloor_of_hypnat 
          hfact_gt_zero hypreal_hfloor_approx_zero mem_infmal_iff of_hypnat_0_less_iff
    by (metis HFinite_1 HFinite_add hfloor_add_one)
  moreover have "(pow) (y / hypreal_of_hypint (hfloor y + 2)) \<in> InternalFuns"
    by simp
  moreover have "HyperSummable ((pow) (y / hypreal_of_hypint (hfloor y + 2)))"
  proof -
    have gt0: "0 < hypreal_of_hypint (hfloor y) + 2"
      by (simp add: add_nonneg_pos less_imp_le y_gt_0)
    then have " hnorm (y / (hypreal_of_hypint (hfloor y) + 2)) < 1"
      using assms add_le_cancel_left hfloor_less_cancel less_hfloor_iff one_le_numeral
      by (metis abs_of_pos divide_less_eq_1_pos divide_pos_pos hypreal_hnorm_def)
    moreover have "\<not> hnorm (y / (hypreal_of_hypint (hfloor y) + 2)) \<approx> 1"
    proof 
      assume "hnorm (y / (hypreal_of_hypint (hfloor y) + 2)) \<approx> 1"
      then have "y / (hypreal_of_hypint (hfloor y) + 2) \<approx> 1"
        by (simp add: abs_of_pos gt0 y_gt_0)
      moreover have "hypreal_of_hypint (hfloor y) + 2 \<in> HFinite"
        using assms 
        by (metis HFinite_add HFinite_bounded HFinite_numeral 
                  hfloor_add_one_gt_zero hfloor_correct hypint_le_add1_eq_le of_hypint_0_le_iff)
      ultimately have "y \<approx> hypreal_of_hypint (hfloor y) + 2"
        using gt0 assms approx_mult2 
        by fastforce
      moreover have "hpart y \<approx> 2"
        using approx_add_left_iff hypreal_eq_hfloor_hpart_add
        by (metis calculation)
      ultimately show False
        by (metis add.commute add_cancel_right_left approx_add_left_cancel 
            approx_le_bound approx_sym hfloor_one hpart_le_one hypreal_hfloor_approx_zero 
            one_add_one one_le_numeral zero_less_one zero_neq_one)
    qed
    ultimately show ?thesis
      by (simp add: HyperSummable_geometric)
  qed
  moreover have "(y / hypreal_of_hypint (hfloor y + 2)) pow hypnat (hfloor y + 1) \<notin> Infinitesimal" 
  proof
    have "(hypreal_of_hypint (hfloor(y)) + 2) pow hypnat (hfloor(y) + (1 :: int star)) \<in> HFinite"
      by (metis HFinite_1 HFinite_HInfinite_iff HFinite_add HFinite_hyperpow_HFinite 
          HFinite_hypnat_hfloor_Nat HFinite_numeral HFinite_y hfloor_add_one hypreal_HInfinite_hfloor_cancel)
    moreover assume contra: "(y / hypreal_of_hypint (hfloor y + 2)) pow hypnat (hfloor y + 1) \<in> Infinitesimal"
    ultimately have "y pow hypnat (hfloor y + 1) /
     (hypreal_of_hypint (hfloor y) + 2) pow hypnat (hfloor y + 1) *
     (hypreal_of_hypint (hfloor y) + 2) pow hypnat (hfloor y + 1) \<in> Infinitesimal"
      by (metis Infinitesimal_HFinite_mult hyperpow_divide of_hypint_add of_hypint_numeral)
    then have "y pow hypnat (hfloor y + 1) \<in> Infinitesimal"
      by (metis add_nonneg_pos hyperpow_gt_zero less_imp_le nonzero_mult_div_cancel_right of_hypint_0_le_iff 
          order_less_irrefl times_divide_eq_left y_gt_0 zero_le_hfloor zero_less_numeral) 
    moreover have "hypnat ((hfloor y) + (1 :: int star)) \<in> \<nat>"
      by (metis HFinite_1 HFinite_add HFinite_hypnat_hfloor_Nat HFinite_y hfloor_add_one)
    moreover have "hypnat (hfloor y + 1) \<noteq> 0"
      using y_gt_0 by force
    moreover have "hypreal_of_hypint (hfloor y) + 2 \<noteq> 0"
      by (metis add_nonneg_pos less_imp_le less_numeral_extra(3) of_hypint_0_le_iff y_gt_0 
          zero_le_hfloor zero_less_numeral)
    ultimately show False 
      using assms Nats_hypnat_of_nat_iff hrealpow_hyperpow_Infinitesimal_iff [symmetric] 
            mem_infmal_iff [symmetric] not_gr0 Infinitesimal_hrealpow_cancel star_of_simps(9) 
      by metis
  qed
  ultimately show ?thesis 
    using HyperSummable_HFinite_mult_left 
            [of _ "(y pow hypnat ((hfloor y) + 1))/of_hypnat(hfact (hypnat ((hfloor y) + 1)))"]
          HyperSummable_divide 
          HyperSummable_comparison_test 
    by blast
qed

lemma HyperSummable_hyperpow_divide_fact_pos:
  "\<lbrakk> (y::hypreal) \<in> HFinite; y > 0 \<rbrakk> \<Longrightarrow> HyperSummable (\<lambda>N. y pow N/of_hypnat(hfact N))"
by (blast intro: HyperSummable_hyperpow_divide_fact_Infinitesimal 
            HyperSummable_hyperpow_divide_fact_not_Infinitesimal)


lemma HyperSummable_hyperpow_divide_fact_neg:
  assumes "(y::hypreal) \<in> HFinite" 
  and "y < 0"
  shows "HyperSummable (\<lambda>N. y pow N/of_hypnat(hfact N))"
proof -
  have "(\<lambda>N. y pow N / hypreal_of_hypnat (hfact N)) \<in> InternalFuns"
    by simp
  moreover have "(\<lambda>N. (- y) pow N / hypreal_of_hypnat (hfact N)) \<in> InternalFuns"
    by simp
  moreover have "\<exists>k\<in>\<nat>. \<forall>n\<ge>k. hnorm (y pow n / hypreal_of_hypnat (hfact n))
                     \<le> (- y) pow n / hypreal_of_hypnat (hfact n)"
    using abs_of_neg eq_iff hyperpow_hrabs
    by (metis Nats_1 assms(2) hnorm_divide hnorm_hypreal_of_hypnat hypreal_hnorm_def)
  moreover have "HyperSummable (\<lambda>N. (- y) pow N / hypreal_of_hypnat (hfact N))"
    by (simp add: HFinite_minus_iff HyperSummable_hyperpow_divide_fact_pos assms(1) assms(2))
  ultimately show ?thesis
    using HyperSummable_comparison_test by blast
qed

lemma InternalFuns_star_choose: "(hchoose) k \<in> InternalFuns"
  by (simp add: hyperbinomial_def)

lemma InternalFuns_star_choose_from [simp]: "(\<lambda>n. n hchoose k) \<in> InternalFuns"
proof (cases k, simp add: hyperbinomial_def InternalFuns_def)
  case (star_n X)
  show "\<exists>F. (\<lambda>n. (*f2* (choose)) n (star_n X)) = *fn* F"
  proof (rule exI [where x="\<lambda>n m. m choose (X n)"], rule ext)
    fix n :: hypnat
    obtain Y where "n = star_n Y"
      using star_cases by auto
    then show "(*f2* (choose)) n (star_n X) = (*fn* (\<lambda>n m. m choose X n)) n"
      by (auto simp add: starfun2_star_n starfun_n)
  qed
qed


lemma hypnat_fact_not_zero [simp]: "hfact n \<noteq> (0::hypnat)"
by (metis hfact_gt_zero hypnat_not_less0)

lemma hfact_nonzero [simp]: 
  "\<And>k. hfact k \<noteq> (0::'a::{semiring_char_0,semiring_no_zero_divisors} star)"
by transfer simp

lemma HyperSummable_geometric':
  assumes "hnorm (x::'a::{real_normed_field} star) < 1"
          "\<not>hnorm x \<approx> 1"
        shows "HyperSummable (\<lambda>N. x pow (hSuc N))"
  by (simp add: HyperSummable_geometric HyperSummable_shift_hSuc assms)

lemma HyperSummable_hyperpow_divide_fact_zero:
  "HyperSummable (\<lambda>n. 0 pow n / hypreal_of_hypnat (hfact n))"
proof -
  {fix n  
  assume infinite_n: "n \<in> HNatInfinite"
  then have internalf: "(\<lambda>n. 0 pow n / hypreal_of_hypnat (hfact n)) \<in> InternalFuns"
    using InternalFuns_expf_term' by blast
  moreover have "n > 0" using infinite_n
    by (simp add: zero_less_HNatInfinite) 
  moreover have "hypersum (\<lambda>n. 0 pow n / hypreal_of_hypnat (hfact n)) {0..<n} \<approx> 1"
  proof -
    have "hypersum (\<lambda>i. 0 pow hSuc i / hypreal_of_hypnat (hfact (hSuc i)))  {0..<n - 1} \<approx> 0"
      by simp
    then have "hypersum (\<lambda>n. 0 pow n / hypreal_of_hypnat (hfact n)) {hSuc 0..<hSuc (n - 1)} \<approx> 0"
      using  hypersum_shift_bounds_hSuc_ivl [OF internalf] by simp
    then have "hypersum (\<lambda>n. 0 pow n / hypreal_of_hypnat (hfact n)) {hSuc 0..<n} \<approx> 0"
      by (simp add: infinite_n)
    then have "0 pow 0 / hypreal_of_hypnat (hfact 0) +
         hypersum (\<lambda>n. 0 pow n / hypreal_of_hypnat (hfact n))
          {hSuc 0..<n} \<approx>
         1"
      using approx_minus_iff by force
    then show ?thesis
      by (simp add: calculation(2) hypersum_head_upt_hSuc) 
  qed}
  then show ?thesis
    using HyperSummable_def2 by blast 
qed
  
lemma HyperSummable_exp':
  "(y::hypreal) \<in> HFinite  \<Longrightarrow> HyperSummable (\<lambda>N. y pow N/of_hypnat(hfact N))"
by (metis (no_types) HyperSummable_hyperpow_divide_fact_pos 
       HyperSummable_hyperpow_divide_fact_neg HyperSummable_hyperpow_divide_fact_zero 
       linorder_cases)

lemma of_hypnat_hfact:
  "\<And>n. of_hypnat(hfact n) = hfact n"
by transfer simp

lemma HyperSummable_exp:
  "(y::hypreal) \<in> HFinite  \<Longrightarrow> HyperSummable (\<lambda>N. y pow N/hfact N)"
proof -
    assume fin: "(y::hypreal) \<in> HFinite"
    have "HyperSummable (\<lambda>N. y pow N/of_hypnat (hfact N)) = HyperSummable (\<lambda>N. y pow N/hfact N)"
          by (subst of_hypnat_hfact) simp
    thus ?thesis using HyperSummable_exp' fin by blast
qed

lemma lemma_n_starfun_extract_binomial_hfallfactpow:
  "eventually (\<lambda>n. ((*nf* (\<lambda>k. of_hypnat ((*f2* (choose)) (star_n Xb) k) *
                               (*f2* fallfactpow) (star_n X) (star_n Xb - k) *
                               (*f2* fallfactpow) (star_n Xa) k)) n) = 
                   (\<lambda>k. of_nat(Xb n choose k) * 
                       fallfactpow (X n) (Xb n - k) * 
                       fallfactpow (Xa n) k)) \<U>"
proof -
  have "(\<lambda>k. of_hypnat ((*f2* (choose)) (star_n Xb) k) *
         (*f2* fallfactpow) (star_n X) (star_n Xb - k) *
         (*f2* fallfactpow) (star_n Xa) k)
        \<in> InternalFuns"
    by (metis (no_types) InternalFuns_hfallfactpow_fun InternalFuns_mult InternalFuns_of_hypnat 
        InternalFuns_starfun2 hfallfactpow_starfun2 star_diff_def)
  moreover have "(\<lambda>k. of_hypnat ((*f2* (choose)) (star_n Xb) k) *
                      (*f2* fallfactpow) (star_n X) (star_n Xb - k) *
                      (*f2* fallfactpow) (star_n Xa) k) =
                *fn* (\<lambda>n k. of_nat (Xb n choose k) *
                            fallfactpow (X n) (Xb n - k) *
                            fallfactpow (Xa n) k)"
  proof 
    fix k 
     obtain Xc :: "nat \<Rightarrow> nat" where "k = star_n Xc"
      using star_cases by auto
    then 
    show "of_hypnat ((*f2* (choose)) (star_n Xb) k) *
         (*f2* fallfactpow) (star_n X) (star_n Xb - k) *
         (*f2* fallfactpow) (star_n Xa) k =
         (*fn* (\<lambda>n k. of_nat (Xb n choose k) *
                      fallfactpow (X n) (Xb n - k) *
                      fallfactpow (Xa n) k)) k"
      by (auto simp add: starfun2_star_n star_n_diff star_n_mult 
          of_hypnat_def starfun_star_n starfun_n)
  qed
  ultimately show ?thesis
    using starfun_n_eq_cancel n_starfun_starfun_n_eq_ultra by auto
qed

lemma hyperbinomial_fallfactpow_ring:
  "hfallfactpow (a + b :: 'a::{comm_ring_1} star) n =
  (hypersum (\<lambda>k. of_hypnat(n hchoose k) * hfallfactpow a (n - k) * hfallfactpow b k)) {0..n}"
proof (cases a, cases b, cases n)
  fix X Xa Xb 
  assume star_assms: "a = star_n X" "b = star_n Xa" "n = star_n Xb"
  then have ev: "eventually (\<lambda>n. ((*nf* (\<lambda>k. of_hypnat ((*f2* (choose)) (star_n Xb) k) *
                       (*f2* fallfactpow) (star_n X) (star_n Xb - k) *
                       (*f2* fallfactpow) (star_n Xa) k)) n) = 
                 (\<lambda>k. of_nat(Xb n choose k) * fallfactpow (X n) (Xb n - k) * fallfactpow (Xa n) k)) \<U>"
    by (simp add: lemma_n_starfun_extract_binomial_hfallfactpow) 
  moreover
  {fix x
    assume "(*nf* (\<lambda>k. of_hypnat ((*f2* (choose)) (star_n Xb) k) *
                   (*f2* fallfactpow) (star_n X) (star_n Xb - k) *
                   (*f2* fallfactpow) (star_n Xa) k))x =
            (\<lambda>k. of_nat (Xb x choose k) * fallfactpow (X x) (Xb x - k) *
                 fallfactpow (Xa x) k)"
    and "(*ns* {0..star_n Xb}) x = {0..Xb x}"
    then have "fallfactpow (X x + Xa x) (Xb x) =
           sum ((*nf* (\<lambda>k. of_hypnat
                            ((*f2* (choose)) (star_n Xb) k) *
                           (*f2* fallfactpow) (star_n X)
                            (star_n Xb - k) *
                           (*f2* fallfactpow) (star_n Xa) k))
                 x) ((*ns* {0..star_n Xb}) x)"
      using binomial_fallfactpow_ring by auto
  }
  then have "\<forall>\<^sub>F x in \<U>.
              (*ns* {0..star_n Xb}) x = {0..Xb x} \<longrightarrow>
              fallfactpow (X x + Xa x) (Xb x) =
              sum ((*nf* (\<lambda>k. of_hypnat
                               ((*f2* (choose)) (star_n Xb) k) *
                              (*f2* fallfactpow) (star_n X)
                               (star_n Xb - k) *
                              (*f2* fallfactpow) (star_n Xa) k))
                    x) ((*ns* {0..star_n Xb}) x)"
    using eventually_mono [OF ev] 
    by simp
  then have "\<forall>\<^sub>F x in \<U>.
              fallfactpow (X x + Xa x) (Xb x) =
              sum ((*nf* (\<lambda>k. of_hypnat
                               ((*f2* (choose)) (star_n Xb) k) *
                              (*f2* fallfactpow) (star_n X)
                               (star_n Xb - k) *
                              (*f2* fallfactpow) (star_n Xa) k))
                    x) ((*ns* {0..star_n Xb}) x)"
    by (rule eventually_mp [OF _ n_star_interval_ultra])
  then show ?thesis using star_assms
    by (simp add: hfallfactpow_starfun2 hyperbinomial_def hypersum_def star_add_def star_n_eq_iff starfun2_star_n) 
qed


lemma hyperbinomial_fallfactpow_ring2:
  "\<And>a b n. hfallfactpow (a + b :: 'a::{comm_ring_1} star) n =
  (hypersum (\<lambda>k. of_hypnat(n hchoose k) * hfallfactpow a k * hfallfactpow b (n - k))) {0..n}"
  by (subst add.commute, simp add: hyperbinomial_fallfactpow_ring mult.commute mult.left_commute)

lemma hyperbinomial_hfact:
 "\<And>n k. k \<le> n \<Longrightarrow> of_hypnat (n hchoose k) = (hfact n :: 'a:: field_char_0 star) / (hfact k * hfact (n - k))"
by (transfer, metis binomial_fact)

lemma hypersum_cong:
      assumes ifun_g: "g \<in> InternalFuns" 
      and ifun_h: "h \<in> InternalFuns" 
      and iset_A: "A \<in> InternalSets"
      and "A = B" 
      and g_h: "\<And>x. x \<in> B \<Longrightarrow> g x = h x"
      shows "hypersum g A = hypersum h B"
proof -
   obtain As Bs where isets: "A = *sn* As" "B = *sn* Bs"  "\<forall>\<^sub>F n in \<U>. As n = Bs n" 
      using iset_A `A = B` by (force simp add: InternalSets_def)
   obtain G H where ifuns: "g = *fn* G" "h = *fn* H" using ifun_g ifun_h by (force simp add: InternalFuns_def)
   {fix X assume "star_n X \<in> *sn* Bs" 
    then have "(*fn* G)(star_n X) = (*fn* H)(star_n X)" using g_h isets ifuns by blast
    then have "\<forall>\<^sub>F n in \<U>. (G n)(X n) = (H n)(X n)" by (simp add: star_n_eq_iff starfun_n)
   }
  then have "\<forall>X. \<forall>\<^sub>F n in \<U>. (X n) \<in> (Bs n) \<longrightarrow> (G n)(X n) = (H n)(X n)"
      by (simp add: FreeUltrafilterNat.eventually_imp_iff starset_n_star_n)
  then have ultra_g_h: "\<forall>\<^sub>F n in \<U>. \<forall>x. x \<in> (Bs n) \<longrightarrow> (G n) x = (H n) x"
      by (simp add: FreeUltrafilterNat.eventually_all_iff)
  have "\<forall>\<^sub>F n in \<U>. (As n = Bs n \<and> (\<forall>x. x \<in> (Bs n) \<longrightarrow> (G n) x = (H n) x)
                         \<longrightarrow> sum (G n) (As n) = sum (H n) (Bs n))"
       by simp
   then have "\<forall>\<^sub>F n in \<U>. sum (G n) (As n) = sum (H n) (Bs n)"
       using eventually_elim2 isets(3) ultra_g_h by fastforce
   thus ?thesis using isets(1,2) ifuns 
       by (auto simp only: hypersum star_n_eq_iff )
qed     

lemma hyperbinomial_vandermonde:
  "(r + s) pow k/hfact k = 
   hypersum (\<lambda>i. (r::'a :: field_char_0 star) pow i / hfact i *  s pow (k - i) / hfact (k - i)) {0..k}"
proof - 
   have ifun_a: "(\<lambda>i. of_hypnat (k hchoose i) * r pow i * s pow (k - i)) \<in> InternalFuns"
     by (simp add: InternalFuns_diff InternalFuns_mult InternalFuns_of_hypnat InternalFuns_star_choose) 
   have ifun_b: "(\<lambda>i. r pow i * s pow (k - i) / (hfact i * hfact (k - i))) \<in> InternalFuns"
     by (simp add: InternalFuns_diff InternalFuns_divide InternalFuns_mult)
   then have ifun_c: "(\<lambda>i. hfact k * r pow i * s pow (k - i) / (hfact i * hfact (k - i))) \<in> InternalFuns"
     by (simp add: InternalFuns_diff InternalFuns_divide InternalFuns_mult)
    have "(r + s) pow k  =  hypersum (\<lambda>i. of_hypnat (k hchoose i) * r pow i * s pow (k - i)) {0..k}"
     using hyperbinomial_ring by blast
    also have  "\<dots> = hypersum (\<lambda>i. hfact k / (hfact i * hfact (k - i)) * r pow i * s pow (k - i)) {0..k}"
       using ifun_a ifun_c by (auto intro!: hypersum_cong simp add: hyperbinomial_hfact)
    also have "\<dots> =  hfact k * hypersum (\<lambda>i. r pow i * s pow (k - i) / (hfact i * hfact (k - i))) {0..k}"
       using  ifun_b by (subst hypersum_right_distrib, auto simp add: field_simps)   
   ultimately show ?thesis by auto
qed


lemma hyperbinomial_hfallfactpow_vandermonde:
  "hfallfactpow (r + s) k/hfact k = 
   hypersum (\<lambda>i. hfallfactpow (r::'a :: field_char_0 star)  i / hfact i *  hfallfactpow s  (k - i) / hfact (k - i)) {0..k}"
proof - 
   have ifun_a: "(\<lambda>i. of_hypnat (k hchoose i) * hfallfactpow r i *  hfallfactpow s (k - i)) \<in> InternalFuns"
     by (simp add: InternalFuns_diff InternalFuns_hfallfactpow_fun InternalFuns_mult InternalFuns_of_hypnat
         InternalFuns_star_choose) 
   have ifun_b: "(\<lambda>i. hfallfactpow r i * hfallfactpow s (k - i) / (hfact i * hfact (k - i))) \<in> InternalFuns"
     by (simp add: InternalFuns_divide InternalFuns_hfallfactpow_fun InternalFuns_mult star_class_defs(4))
   then have ifun_c: "(\<lambda>i. hfact k * hfallfactpow r i * hfallfactpow s (k - i) / (hfact i * hfact (k - i))) \<in> InternalFuns"
     by (simp add: InternalFuns_diff InternalFuns_divide InternalFuns_hfallfactpow_fun InternalFuns_mult)
   have "hfallfactpow (r + s) k  =  hypersum (\<lambda>i. of_hypnat (k hchoose i) * hfallfactpow r i * hfallfactpow s (k - i)) {0..k}"
     using hyperbinomial_fallfactpow_ring2 by blast      
   also have  "\<dots> = hypersum (\<lambda>i. hfact k / (hfact i * hfact (k - i)) * hfallfactpow r i * hfallfactpow s (k - i)) {0..k}"
       using ifun_a ifun_c by (auto intro!: hypersum_cong simp add: hyperbinomial_hfact)
   also have "\<dots> =  hfact k * hypersum (\<lambda>i. hfallfactpow r i * hfallfactpow s (k - i) / (hfact i * hfact (k - i))) {0..k}"
       using  ifun_b by (subst hypersum_right_distrib, auto simp add: field_simps)   
   ultimately show ?thesis by auto
qed

lemma hyperbinomial_fallfactpow_ring3:
  "hfallfactpow (a + b :: 'a::{field_char_0} star) n =
  (hypersum (\<lambda>k. hfallfactpow (of_hypnat n) k / hfact k * hfallfactpow a (n - k) * hfallfactpow b k)) {0..n}"
proof -
  have "(\<lambda>k. of_hypnat (n hchoose k) * hfallfactpow a (n - k) * hfallfactpow b k) \<in> InternalFuns"
    by (simp add: InternalFuns_hfallfactpow_fun InternalFuns_mult InternalFuns_of_hypnat 
          InternalFuns_star_choose star_diff_def)
  moreover have "(\<lambda>k. hfallfactpow (of_hypnat n) k * hfallfactpow a (n - k) * hfallfactpow b k / of_hypnat (hfact k)) \<in> InternalFuns"
    by (simp add: InternalFuns_divide InternalFuns_mult InternalFuns_o2 InternalFuns_of_hypnat star_diff_def)
  ultimately show ?thesis
    by (force intro!: hypersum_cong simp add: hyperbinomial_fallfactpow_ring hyperbinomial_hfallfactpow)
qed

text\<open>Setting up a few lemmas to prove properties about infinitesimal exponents\<close>  

lemma binomial_expand_first_two_terms:
  "0 \<le> u \<Longrightarrow> \<exists>x\<ge>0. (1+ (u::'a::{linordered_idom,power}))^n = 1 + of_nat n * u + x"
by (induct n, auto simp add: algebra_simps)

lemma hyperbinomial_expand_first_two_terms:
   "\<And>u n. 0 \<le> u \<Longrightarrow> \<exists>x\<ge>0. (1 + (u::'a::{linordered_idom,power} star)) pow n = 1 + of_hypnat n * u + x"
by transfer (erule binomial_expand_first_two_terms)

lemma hyperbinomial_expand_first_two_terms':
   "\<And>u n. 0 \<le> u \<Longrightarrow> \<exists>x\<ge>0. ((u::'a::{linordered_idom,power} star) + 1) pow n = 1 + of_hypnat n * u + x"
  by (metis add.commute hyperbinomial_expand_first_two_terms)

end 

