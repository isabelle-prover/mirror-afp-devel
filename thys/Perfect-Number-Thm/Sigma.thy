header{*Sum of divisors function*}

theory Sigma
imports PerfectBasics Infinite_Set
begin

definition divisors :: "nat => nat set" where
"divisors (m::nat) == {(n::nat) . (n::nat) dvd m}"

definition sigma :: "nat => nat" where
"sigma m == \<Sum> n  |n dvd m . n"

lemma sigma_divisors: "sigma(n) = \<Sum> (divisors(n))"
by (auto simp: sigma_def divisors_def)

lemma divisors_eq_dvd[iff]: "(a:divisors(n)) = (a dvd n)"
by(simp add: divisors_def)

lemma mult_divisors: "(a::nat)*b=c==>a: divisors c"
by (unfold divisors_def dvd_def,blast)
lemma mult_divisors2: "(a::nat)*b=c==>b: divisors c"
by (unfold divisors_def dvd_def,auto)

lemma divisorsfinite[simp]:
   assumes "n>0"
   shows "finite (divisors n)"
proof -
  from assms have  "divisors n = {m . m dvd n & m <= n}"
    by (auto simp only:divisors_def dvd_imp_le)
  hence "divisors n <= {m . m<=n}" by auto
  thus "finite (divisors n)"
    by (metis Collect_def finite_Collect_le_nat finite_subset) 
qed

lemma divs_of_zero_UNIV[simp]: "divisors(0) = UNIV"
by(auto simp add: divisors_def)

lemma sigma0[simp]: "sigma(0) = 0"
by (simp add: sigma_def)
lemma sigma1[simp]: "sigma(1) = 1"
by (simp add: sigma_def)

lemma prime_divisors: "prime (p::nat) <-> divisors p = {1,p} & p>1"
by (auto simp add: divisors_def prime_def)

lemma prime_imp_sigma: "prime (p::nat) ==> sigma(p) = p+1"
proof -
  assume "prime (p::nat)"
  hence "p>1 \<and> divisors(p) = {1,p}" by (simp add: prime_divisors)
  hence "p>1 \<and> sigma(p) = \<Sum> {1,p}" by (auto simp only: sigma_divisors divisors_def)
  thus "sigma(p) = p+1" by simp
qed

lemma sigma_third_divisor:
  assumes  "1 < a" "a < n" "a : divisors n"
  shows "1+a+n <= sigma(n)"
proof -
  from assms have "finite {1,a,n} & finite (divisors n) & {1,a,n} <= divisors n" by auto
  hence "\<Sum> {1,a,n} <= \<Sum> (divisors n)" by (simp only: setsum_mono2)
  hence "\<Sum> {1,a,n} <= sigma n" by (simp add: sigma_divisors)
  with assms show "?thesis" by auto
qed

lemma divisor_imp_smeq: "a : divisors (Suc n) ==> a <= Suc n"
apply (auto simp add: divisors_def)
apply (metis Suc_neq_Zero divides_ge)
done

lemma sigma_imp_divisors: "sigma(n)=n+1 ==> n>1 & divisors n = {n,1}"
proof
  assume ass:"sigma(n)=n+1"
  hence "n~=0 & n~=1"
    by (metis Suc_eq_plus1 n_not_Suc_n sigma0 sigma1)
  thus conc1: "n>1" by simp

  show "divisors n = {n,1}" (*TODO: use sigma_third_divisor *)
  proof (rule ccontr)
    assume "divisors n ~= {n,1}"
    with conc1 have "divisors n ~= {n,1} & 1<n" by auto
    moreover
    from ass conc1 have "1 : divisors(n) & n : divisors n & ~0 : divisors n"
      by (simp add: dvd_def divisors_def)
    ultimately
    have  "(EX a. a~=n & a~=1 & 1<n & a : divisors n) & 0 ~: divisors n" by auto
    hence "(EX a. a~=n & a~=1 & 1<n & a~=0 & a : divisors n)" by metis
    hence "EX a . a~=n & a~=1 & 1~=n & a~=0 & finite {1,a,n} & finite (divisors n) & {1,a,n} <= divisors n" by auto
    hence "EX a. a~=n & a~=1 & 1~=n & a~=0 & \<Sum> {1,a,n} <= sigma n"
      by (metis setsum_mono2_nat sigma_divisors)
    hence "EX a. a~=0 & (1+a+n) <= sigma n" by auto
    hence "1+n<sigma n" by auto (*TODO: this step can be deleted, should i?*)
    with ass show "False" by auto
  qed
qed


lemma sigma_imp_prime: "sigma(n)=n+1 ==> prime n"
proof -
  assume ass: "sigma(n)=n+1"
  hence "n>1 & divisors(n)={1,n}" by (metis insert_commute sigma_imp_divisors)
  thus "prime n" by (simp add: prime_divisors)
qed

lemma pr_pow_div_eq_sm_pr_pow: 
  assumes prime: "prime p"
  shows "{d . d dvd p^n} = {p^f| f . f<=n}"
proof
  show "{p^f | f . f<=n} <= { d .  d dvd p^n}"
  proof
    fix x
    assume "x: {p ^ f | f . f <= n}"
    hence "EX i . x = p^i & i<= n"   by auto
    with prime have  "x dvd p^n" by (auto simp add: divides_primepow)
    thus "x : { d . d dvd p^n}" by auto
  qed
  next
  show "{d. d dvd p ^ n} <= {p ^ f | f . f <= n}"
  proof
    fix x
    assume "x : {d . d dvd p^n}"
    hence "x dvd p^n" by auto
    with prime obtain "i" where  "i <= n & x = p^i"
      by (auto simp only: divides_primepow)
    hence "x = p^i & i <=n" by auto
    thus "x : { p^f | f . f<=n }" by auto
  qed
qed

lemma rewrite_sum_of_powers:
assumes p: "(p::nat)>1"
shows "(\<Sum> {p^m | m . m<=(n::nat)}) = (\<Sum> i = 0 .. n . p^i)" (is "?l = ?r")
proof -
  have "?l = setsum (%x. x) {(op ^ p) m |m . m<= n}" by auto
  also have "... = setsum (%x. x) ((op ^ p)`{m . m<= n})"
    by(rule seteq_imp_setsumeq) auto
  moreover with p have "inj_on (op ^p) {m . m<=n}"
    by (auto simp add: inj_on_def)
  ultimately have "?l = setsum (op ^ p) {m . m<=n}"
    by(auto simp only: setsum_reindex_id id_def)
  moreover have "{m::nat . m<=n} = {0..n}" by auto
  ultimately show "?l = (\<Sum> i = 0 .. n . p^i)" by auto
qed

theorem sigma_primepower:
  "prime p ==> (p - 1)*sigma(p^(e::nat)) = (p^(e+1) - 1)"
proof -
  assume "prime p"
  hence "sigma(p^(e::nat)) = (\<Sum>i=0 .. e . p^i)"
    by (simp add: pr_pow_div_eq_sm_pr_pow sigma_def rewrite_sum_of_powers prime_def)
  thus "(p - 1)*sigma(p^e)=p^(e+1) - 1" by (simp only: simplify_sum_of_powers)
qed

lemma sigma_prime_power_two: "sigma(2^(n::nat)) = 2^(n+1) - 1"
proof -
  have "(2 - 1)*sigma(2^(n::nat))=2^(n+1) - 1"
    by (auto simp only: sigma_primepower two_is_prime)
  thus ?thesis by simp
qed

lemma sigma_finite_set1[simp]:
assumes m0: "(m::nat)>0" and p1: "p>1"
shows "finite {p ^ f * b | f b . f <= n & b dvd m}" 
proof -
  have "{p^f * b | f b . f <= n & b dvd m} <= {0 .. p^n*m}"
    by auto (metis dvd_imp_le m0 mult_le_mono nat_less_le p1 power_increasing)
  thus "finite {p^f * b | f b . f <= n & b dvd m}" by (simp add: finite_subset)
qed


lemma sigma_finite_set2[simp]:
assumes m0: "m>0"
shows "m>0 ==> finite {(x::nat) * b |b. b dvd m}"
proof -
  from m0 have "finite (divisors m)" by simp
  hence "finite ((op * x)`(divisors m))" by auto
  moreover have "{x * b |b. b dvd m} = (op * x)`(divisors m)"
    by (auto simp add: divisors_def)
  ultimately show "?thesis" by auto
qed


lemma prodsums_eq_sumprods_help2:
assumes ndvd: "~ p dvd m" and p1: "p>(1::nat)"
shows "\<Sum> ({p^f*b |f b. f <= n & b dvd m} Int {p^f*b |f b. f = Suc n & b dvd m})
       = 0"
proof -
  have  "!!b f ba. [| f <= n; p * p ^ n * b = p ^ f * ba; b dvd m; ba dvd m |] ==> False"
  proof -
    fix b ba f
    assume ass: "f <= n" "p * p ^ n * b = p ^ f * ba" "b dvd m" "ba dvd m"
    then obtain e where edef: "f+e = Suc n"
      by (metis Suc_eq_plus1 le_add_diff_inverse trans_le_add1)
    hence"p^(Suc n) = p^(f+e)" by auto
    hence "p^(Suc n) = p^f*p^e" by (simp only: power_add) 
    with ass have "p^f*p^e * b = p ^ f * ba"  by auto
    with p1 have "p^e*b=ba" by auto
    moreover from edef ass have "e>0" by auto
    ultimately have "p dvd ba" by auto
    with ass have "p dvd m" by (metis dvd.order_trans )
    with ndvd show "False" by auto
  qed
  thus "?thesis" by (auto simp: Int_def intro!: setsum_0_if_empty)
qed

lemma sum_pow_plus_suc_eq_sum_upto_suc:
  assumes p:"(p::nat)>1"
  shows "\<Sum>{p ^ f |f. f <= n} + p^(Suc n)= \<Sum>{p ^ f |f. f <= Suc n}"
     (is "?lhs = ?rhs")
proof -
  have "?lhs =  (\<Sum> i = 0 .. n . p^i) + p^(Suc n)"
    by (simp only: rewrite_sum_of_powers[OF p]) (*TOASK: how to do this with something similar to subst?*)
  hence "?lhs =  (\<Sum> i = 0 .. Suc n . p^i)" by simp
  thus "?lhs =  ?rhs" by (subst rewrite_sum_of_powers[OF p])
qed

lemma rewrite_power_times_sum:
assumes "(p::nat) > 1"
shows "p^x*(\<Sum>{b. b dvd m}) = \<Sum> {p^f*b | f b . f = x & b dvd m}" (is "?l = ?r")
proof -
  have "?l = setsum (op * (p^x)) {b . b dvd m}"
    by (auto simp add: setsum_right_distrib)
  moreover from `p>1` have "inj_on (op * (p^x)) {b . b dvd m}"
    by(simp add: inj_on_def)
  ultimately also have  "?l = (setsum id ((op * (p^x))` {b. b dvd m}))"
    by (auto simp only: setsum_reindex_id)
  thus "?thesis" by (auto simp add:conj_commute image_def)
qed



(* TODO: betere afkortingen maken *)
lemma prodsums_eq_sumprods_help: 
assumes "(m::nat)>0" and "(p::nat)>1" and "coprime p m"
shows "\<Sum>{p^f*b | f b. f <= n & b dvd m} + p^(Suc n)*(\<Sum>{b. b dvd m}) =
       \<Sum>{p^f*b | f b . f <= Suc n & b dvd m}"
      (is "\<Sum> ?lhsa + ?lhsb = \<Sum> ?rhs")
proof -
  from `p>1` have "?lhsb = (\<Sum> {p^f*b | f b . f=Suc n & b dvd m})" (is "?lhsb = \<Sum> ?lhsbn" )
    by (auto simp only: rewrite_power_times_sum)
  moreover from `m>0` `p>1` have "finite ?lhsa" by simp
  moreover from `m>0` have "finite ?lhsbn" by simp
  ultimately have "\<Sum> ?lhsa + ?lhsb = \<Sum>(?lhsa Un ?lhsbn) + \<Sum>(?lhsa Int ?lhsbn)"
    by (auto, auto simp only: setsum_Un_Int)
  moreover {
    have "\<Sum> (?lhsa Un ?lhsbn) =
          \<Sum> ({x . (EX f b. (x = p ^ f * b & f <= n & b dvd m) \<or>
                           (x = p^f*b & f=Suc n & b dvd m))})"
      by(rule seteq_imp_setsumeq, auto simp del:power_Suc)
    also have "... = \<Sum> {p ^ f * b | f b . (f <= n \<or> f=Suc n) & b dvd m}"
      by(rule seteq_imp_setsumeq) auto
    finally have "\<Sum>(?lhsa Un ?lhsbn) = \<Sum>{p^f * b |f b. f <= Suc n & b dvd m}"
      by (simp only: le_Suc_eq) }
  moreover {
    from `coprime p m` `p>1` have "~ p dvd m"
      by (metis coprime_def dvd_div_mult_self gcd_mult' nat_less_le)
    with `p>1` have "~ p dvd m" "p>1" by auto
    hence " \<Sum> (?lhsa Int ?lhsbn) = 0" by (rule prodsums_eq_sumprods_help2) }
  ultimately show "?thesis" by auto
qed


lemma prodsums_eq_sumprods:
assumes "p > Suc 0" and "coprime p m" and "m > 0"
shows "(\<Sum>{p^f|f. f<=n})*(\<Sum>{b. b dvd m}) = (\<Sum> {p^f*b| f b. f <= n & b dvd m})"
proof (induct n)
  case 0 show ?case by auto
next
  case (Suc n)
  let ?lhs = "\<Sum>{p^f |f. f <= n} * \<Sum>{b. b dvd m}"
  let ?rhs = "\<Sum>{p^f * b |f b. f <= n & b dvd m}"
  show ?case (is "?lhsn = ?rhsn")
  proof -
    from Suc have "?lhs + p^(Suc n)*(\<Sum>{b. b dvd m}) =
                   ?rhs + p^(Suc n)*(\<Sum>{b. b dvd m})" by auto
    moreover
    { have "\<Sum>{p^f |f. f <= n} * \<Sum>{b. b dvd m} + p^(Suc n)*(\<Sum>{b. b dvd m})
          =(\<Sum>{p^f |f. f <= n} + p^(Suc n))*(\<Sum>{b. b dvd m})"
        by (simp add: add_mult_distrib)
      with `p>Suc 0`
      have "\<Sum>{p^f|f. f<=n} * \<Sum>{b. b dvd m} + p^(Suc n)*(\<Sum>{b. b dvd m})= ?lhsn"
        by (simp only: sum_pow_plus_suc_eq_sum_upto_suc prime_def)
    }
    moreover from `m>0` `p>Suc 0` `coprime p m`
    have "\<Sum>{p^f*b |f b. f <= n & b dvd m} + p^(Suc n)*(\<Sum>{b. b dvd m}) = ?rhsn"
      by (subst prodsums_eq_sumprods_help,auto)
    ultimately show  ?case by simp
  qed
qed


lemma rewrite_for_sigma_semimultiplicative:
assumes "prime p"
shows "{p^f*b |f b. f<=n & b dvd m} = {a*b |a b. a dvd (p^n) & b dvd m}"
proof
  show "{p^f * b |f b. f <= n & b dvd m} <= {a*b |a b. a dvd p ^ n & b dvd m}"
  proof
    fix x
    assume "x : {p ^ f * b | f b. f <= n & b dvd m}"
    then obtain b f where "x = p^f*b & f <= n & b dvd m" by auto
    with `prime p` show "x : {a * b |a b. a dvd p ^ n & b dvd m}"
      by (auto simp add: divides_primepow)
  qed
next
  show "{a*b |a b. a dvd p ^ n & b dvd m} <= {p^f * b |f b. f <= n & b dvd m}"
    using `prime p` by auto (metis assms divides_primepow)
qed


lemma div_decomp_comp:
  "coprime m n \<Longrightarrow> a dvd m*n <-> (EX b c . a = b * c & b dvd m & c dvd n)"
by (auto simp only: division_decomp mult_dvd_mono)

(*TODO logischer volgorde maken *)
theorem sigma_semimultiplicative:
  assumes p: "prime p" and cop: "coprime p m" and m0:"m>0"
  shows "sigma (p^n) * sigma m = sigma (p^n * m)" (is "?l = ?r")
proof -
  from cop have cop2: "coprime (p^n) m"
    by (auto simp add: coprime_exp coprime_commute)
  have "?l = (\<Sum> {a . a dvd p^n})*(\<Sum> {b . b dvd m})" by (simp add: sigma_def)
  also from p have "... = (\<Sum> {p^f| f . f<=n})*(\<Sum> {b . b dvd m})"
    by (simp add: pr_pow_div_eq_sm_pr_pow)
  also from m0 p cop  have "... = (\<Sum> {p^f*b| f b . f<=n & b dvd m})"
    by (auto simp add: prodsums_eq_sumprods prime_def)
  also have "... = (\<Sum> {a*b| a b . a dvd (p^n) & b dvd m})"
    by(rule seteq_imp_setsumeq,rule rewrite_for_sigma_semimultiplicative[OF p])
  finally have "?l = \<Sum>{c. c dvd (p^n*m)}" by (subst div_decomp_comp[OF cop2])
  thus "?l = sigma (p^n*m)" by (auto simp add: sigma_def)
qed

end