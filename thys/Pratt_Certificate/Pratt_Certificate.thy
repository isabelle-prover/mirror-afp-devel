theory Pratt_Certificate
imports
  Complex_Main
  Lehmer.Lehmer
  "HOL-Library.Code_Target_Numeral"
begin

definition mod_exp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where [code_abbrev]: "mod_exp b e m = (b ^ e) mod m"

lemma mod_exp_code [code]:
  "mod_exp b e m = 
    (if e = 0 then if m = 1 then 0 else 1 
     else if even e then mod_exp ((b * b) mod m) (e div 2) m
     else (b * mod_exp ((b * b) mod m) (e div 2) m) mod m)"
  by (auto simp add: mod_exp_def power2_eq_square mod_Suc power_mod power_mult
    mod_mult_right_eq elim: evenE oddE)

(* 
  Need to use @{term "b*b::nat"} here instead of squaring, otherwise code_unfold produces
  infinite recursion
  FIXME: Better performance using divMod or bit tests/bit shifts. Tail-recursive would also be good.
*)

lemma eval_mod_exp [simp]:
  "mod_exp b 0 (Suc 0) = 0"
  "m \<noteq> 1 \<Longrightarrow> mod_exp b 0 m = 1"
  "mod_exp b 1 m = b mod m"
  "mod_exp b (Suc 0) m = b mod m"
  "mod_exp b (numeral (num.Bit0 n)) m = mod_exp (b\<^sup>2 mod m) (numeral n) m"
  "mod_exp b (numeral (num.Bit1 n)) m = b * mod_exp (b\<^sup>2 mod m) (numeral n) m mod m"
proof -
  have "1 mod m = 1" if "m \<noteq> 1" using that 
    by (cases m) auto
  show "m \<noteq> 1 \<Longrightarrow> mod_exp b 0 m = 1" "mod_exp b 0 (Suc 0) = 0"
    by (cases m) (simp_all add: mod_exp_def)
  show "mod_exp b 1 m = b mod m" by (simp add: mod_exp_def)
  show "mod_exp b (Suc 0) m = b mod m" by (simp add: mod_exp_def)
  have "numeral (num.Bit0 n) = (2 * numeral n :: nat)"
    by (subst numeral.numeral_Bit0) (simp del: arith_simps)
  also have "mod_exp b \<dots> m = mod_exp (b\<^sup>2 mod m) (numeral n) m"
    by (simp only: mod_exp_def power_mult mod_simps)
  finally show "mod_exp b (numeral (num.Bit0 n)) m = mod_exp (b\<^sup>2 mod m) (numeral n) m" by simp
  have "numeral (num.Bit1 n) = Suc (2 * numeral n :: nat)"
    by (subst numeral.numeral_Bit1) (simp del: arith_simps)
  also have "mod_exp b \<dots> m = b * mod_exp (b\<^sup>2 mod m) (numeral n) m mod m"
    by (simp only: mod_exp_def power_mult power_Suc mod_simps)
  finally show "mod_exp b (numeral (num.Bit1 n)) m = b * mod_exp (b\<^sup>2 mod m) (numeral n) m mod m" .
qed


section {* Pratt's Primality Certificates *}
text_raw {* \label{sec:pratt} *}

text {*
  This work formalizes Pratt's proof system as described in his article
  ``Every Prime has a Succinct Certificate''\cite{pratt1975certificate}.
  The proof system makes use of two types of predicates:
  \begin{itemize}
    \item $\text{Prime}(p)$: $p$ is a prime number
    \item $(p, a, x)$: @{text "\<forall>q \<in> prime_factors(x). [a^((p - 1) div q) \<noteq> 1] (mod p)"}
  \end{itemize}
  We represent these predicates with the following datatype:
*}

datatype pratt = Prime nat | Triple nat nat nat

text {*
  Pratt describes an inference system consisting of the axiom $(p, a, 1)$
  and the following inference rules:
  \begin{itemize}
  \item R1: If we know that $(p, a, x)$ and @{text "[a^((p - 1) div q) \<noteq> 1] (mod p)"} hold for some
              prime number $q$ we can conclude $(p, a, qx)$ from that.
  \item R2: If we know that $(p, a, p - 1)$ and  @{text "[a^(p - 1) = 1] (mod p)"} hold, we can
              infer $\text{Prime}(p)$.
  \end{itemize}
  Both rules follow from Lehmer's theorem as we will show later on.

  A list of predicates (i.e., values of type @{type pratt}) is a \emph{certificate}, if it is
  built according to the inference system described above. I.e., a list @{term "x # xs :: pratt list"}
  is a certificate if @{term "xs :: pratt list"} is a certificate and @{term "x :: pratt"} is
  either an axiom or all preconditions of @{term "x :: pratt"} occur in @{term "xs :: pratt list"}.

  We call a certificate @{term "xs :: pratt list"} a \emph{certificate for @{term p}},
  if @{term "Prime p"} occurs in @{term "xs :: pratt list"}.

  The function @{text valid_cert} checks whether a list is a certificate.
*}

fun valid_cert :: "pratt list \<Rightarrow> bool" where
  "valid_cert [] = True"
| R2: "valid_cert (Prime p#xs) \<longleftrightarrow> 1 < p \<and> valid_cert xs
    \<and> (\<exists> a . [a^(p - 1) = 1] (mod p) \<and> Triple p a (p - 1) \<in> set xs)"
| R1: "valid_cert (Triple p a x # xs) \<longleftrightarrow> p > 1 \<and> 0 < x  \<and> valid_cert xs \<and> (x=1 \<or>
    (\<exists>q y. x = q * y \<and> Prime q \<in> set xs \<and> Triple p a y \<in> set xs
      \<and> [a^((p - 1) div q) \<noteq> 1] (mod p)))"

text {*
  We define a function @{term size_cert} to measure the size of a certificate, assuming
  a binary encoding of numbers. We will use this to show that there is a certificate for a
  prime number $p$ such that the size of the certificate is polynomially bounded in the size
  of the binary representation of $p$.
*}
fun size_pratt :: "pratt \<Rightarrow> real" where
  "size_pratt (Prime p) = log 2 p" |
  "size_pratt (Triple p a x) = log 2 p + log 2 a + log 2 x"

fun size_cert :: "pratt list \<Rightarrow> real" where
  "size_cert [] = 0" |
  "size_cert (x # xs) = 1 + size_pratt x + size_cert xs"


subsection {* Soundness *}

text {*
  In Section \ref{sec:pratt} we introduced the predicates $\text{Prime}(p)$ and $(p, a, x)$.
  In this section we show that for a certificate every predicate occurring in this certificate
  holds. In particular, if $\text{Prime}(p)$ occurs in a certificate, $p$ is prime.
*}

lemma prime_factors_one [simp]: shows "prime_factors (Suc 0) = {}"
  using prime_factorization_1 [where ?'a = nat] by simp

lemma prime_factors_of_prime: fixes p :: nat assumes "prime p" shows "prime_factors p = {p}"
  using assms by (fact prime_prime_factors)

theorem pratt_sound:
  assumes 1: "valid_cert c"
  assumes 2: "t \<in> set c"
  shows "(t = Prime p \<longrightarrow> prime p) \<and>
         (t = Triple p a x \<longrightarrow> ((\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x))"
using assms
proof (induction c arbitrary: p a x t)
  case Nil then show ?case by force
  next
  case (Cons y ys)
  { assume "y=Triple p a x" "x=1"
    then have "(\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x" by simp
    }
  moreover
  { assume x_y: "y=Triple p a x" "x~=1"
    hence "x>0" using Cons.prems by auto
    obtain q z where "x=q*z" "Prime q \<in> set ys \<and> Triple p a z \<in> set ys"
               and cong:"[a^((p - 1) div q) \<noteq> 1] (mod p)" using Cons.prems x_y by auto
    then have factors_IH:"(\<forall> r \<in> prime_factors z . [a^((p - 1) div r) \<noteq> 1] (mod p))" "prime q" "z>0"
      using Cons.IH Cons.prems `x>0` `y=Triple p a x`
      by force+
    then have "prime_factors x = prime_factors z \<union> {q}"  using `x =q*z` `x>0`
      by (simp add: prime_factors_product prime_factors_of_prime)
    then have "(\<forall> q \<in> prime_factors x . [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0 < x"
      using factors_IH cong by (simp add: `x>0`)
    }
  ultimately have y_Triple:"y=Triple p a x \<Longrightarrow> (\<forall> q \<in> prime_factors x .
                                                [a^((p - 1) div q) \<noteq> 1] (mod p)) \<and> 0<x" by linarith
  { assume y: "y=Prime p" "p>2" then
    obtain a where a:"[a^(p - 1) = 1] (mod p)" "Triple p a (p - 1) \<in> set ys"
      using Cons.prems by auto
    then have Bier:"(\<forall>q\<in>prime_factors (p - 1). [a^((p - 1) div q) \<noteq> 1] (mod p))"
      using Cons.IH Cons.prems(1) by (simp add:y(1))
    then have "prime p" using lehmers_theorem[OF _ _a(1)] `p>2` by fastforce
    }
  moreover
  { assume "y=Prime p" "p=2" hence "prime p" by simp }
  moreover
  { assume "y=Prime p" then have "p>1"  using Cons.prems  by simp }
  ultimately have y_Prime:"y = Prime p \<Longrightarrow> prime p" by linarith

  show ?case
  proof (cases "t \<in> set ys")
    case True
      show ?thesis using Cons.IH[OF _ True] Cons.prems(1) by (cases y) auto
    next
    case False
      thus ?thesis using Cons.prems(2) y_Prime y_Triple by force
  qed
qed



subsection {* Completeness *}

text {*
  In this section we show completeness of Pratt's proof system, i.e., we show that for
  every prime number $p$ there exists a certificate for $p$. We also give an upper
  bound for the size of a minimal certificate

  The prove we give is constructive. We assume that we have certificates for all prime
  factors of $p - 1$ and use these to build a certificate for $p$ from that. It is
  important to note that certificates can be concatenated.
*}

lemma valid_cert_appendI:
  assumes "valid_cert r"
  assumes "valid_cert s"
  shows "valid_cert (r @ s)"
  using assms
proof (induction r)
  case (Cons y ys) then show ?case by (cases y) auto
qed simp

lemma valid_cert_concatI: "(\<forall>x \<in> set xs . valid_cert x) \<Longrightarrow> valid_cert (concat xs)"
  by (induction xs) (auto simp add: valid_cert_appendI)

lemma size_pratt_le:
 fixes d::real
 assumes "\<forall> x \<in> set c. size_pratt x \<le> d"
 shows "size_cert c \<le> length c * (1 + d)" using assms
 by (induction c) (simp_all add: algebra_simps)

fun build_fpc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> pratt list" where
  "build_fpc p a r [] = [Triple p a r]" |
  "build_fpc p a r (y # ys) = Triple p a r # build_fpc p a (r div y) ys"

text {*
  The function @{term build_fpc} helps us to construct a certificate for $p$ from
  the certificates for the prime factors of $p - 1$. Called as
  @{term "build_fpc p a (p - 1) qs"} where $@{term "qs"} = q_1 \ldots q_n$
  is prime decomposition of $p - 1$ such that $q_1 \cdot \dotsb \cdot q_n = @{term "p - 1 :: nat"}$,
  it returns the following list of predicates:
  \[
  (p,a,p-1), (p,a,\frac{p - 1}{q_1}), (p,a,\frac{p - 1}{q_1 q_2}), \ldots, (p,a,\frac{p-1}{q_1 \ldots q_n}) = (p,a,1)
  \]

  I.e., if there is an appropriate $a$ and and a certificate @{term rs} for all
  prime factors of $p$, then we can construct a certificate for $p$ as
  @{term [display] "Prime p # build_fpc p a (p - 1) qs @ rs"}
*}

text {*
  The following lemma shows that @{text "build_fpc"} extends a certificate that
  satisfies the preconditions described before to a correct certificate.
*}

lemma correct_fpc:
  assumes "valid_cert xs" "p > 1"
  assumes "prod_list qs = r" "r \<noteq> 0"
  assumes "\<forall> q \<in> set qs . Prime q \<in> set xs"
  assumes "\<forall> q \<in> set qs . [a^((p - 1) div q) \<noteq> 1] (mod p)"
  shows "valid_cert (build_fpc p a r qs @ xs)"
  using assms
proof (induction qs arbitrary: r)
  case Nil thus ?case by auto
next
  case (Cons y ys)
  have "prod_list ys = r div y" using Cons.prems by auto
  then have T_in: "Triple p a (prod_list ys) \<in> set (build_fpc p a (r div y) ys @ xs)"
    by (cases ys) auto

  have "valid_cert (build_fpc p a (r div y) ys @ xs)"
    using Cons.prems by (intro Cons.IH) auto
  then have "valid_cert (Triple p a r # build_fpc p a (r div y) ys @ xs)"
    using `r \<noteq> 0` T_in Cons.prems by auto
  then show ?case by simp
qed

lemma length_fpc:
  "length (build_fpc p a r qs) = length qs + 1" by (induction qs arbitrary: r) auto

lemma div_gt_0:
  fixes m n :: nat assumes "m \<le> n" "0 < m" shows "0 < n div m"
proof -
  have "0 < m div m" using `0 < m` div_self by auto
  also have "m div m \<le> n div m" using `m \<le> n` by (rule div_le_mono)
  finally show ?thesis .
qed

lemma size_pratt_fpc:
  assumes "a \<le> p" "r \<le> p" "0 < a" "0 < r" "0 < p" "prod_list qs = r"
  shows "\<forall>x \<in> set (build_fpc p a r qs) . size_pratt x \<le> 3 * log 2 p" using assms
proof (induction qs arbitrary: r)
  case Nil
  then have "log 2 a \<le> log 2 p" "log 2 r \<le> log 2 p" by auto
  then show ?case by simp
next
  case (Cons q qs)
  then have "log 2 a \<le> log 2 p" "log 2 r \<le> log 2 p" by auto
  then have  "log 2 a + log 2 r \<le> 2 * log 2 p" by arith
  moreover have "r div q > 0" using Cons.prems by (fastforce intro: div_gt_0)
  moreover hence "prod_list qs = r div q" using Cons.prems(6) by auto
  moreover have "r div q \<le> p" using `r\<le>p` div_le_dividend[of r q] by linarith
  ultimately show ?case using Cons by simp
qed

lemma concat_set:
  assumes "\<forall> q \<in> qs . \<exists> c \<in> set cs . Prime q \<in> set c"
  shows "\<forall> q \<in> qs . Prime q \<in> set (concat cs)"
  using assms by (induction cs) auto

lemma p_in_prime_factorsE:
  fixes n :: nat
  assumes "p \<in> prime_factors n" "0 < n"
  obtains "2 \<le> p" "p \<le> n" "p dvd n" "prime p"
proof
  from assms show "prime p" by auto
  then show "2 \<le> p" by (auto dest: prime_gt_1_nat)

  from assms show "p dvd n" by auto
  then show "p \<le> n" using  `0 < n` by (rule dvd_imp_le)
qed

lemma prime_factors_list_prime:
  fixes n :: nat
  assumes "prime n"
  shows "\<exists> qs. prime_factors n = set qs \<and> prod_list qs = n \<and> length qs = 1"
  using assms by (auto simp add: prime_factorization_prime intro: exI [of _ "[n]"])

lemma prime_factors_list:
  fixes n :: nat assumes "3 < n" "\<not> prime n"
  shows "\<exists> qs. prime_factors n = set qs \<and> prod_list qs = n \<and> length qs \<ge> 2"
  using assms
proof (induction n rule: less_induct)
  case (less n)
    obtain p where "p \<in> prime_factors n" using `n > 3` prime_factors_elem by force
    then have p':"2 \<le> p" "p \<le> n" "p dvd n" "prime p"
      using `3 < n` by (auto elim: p_in_prime_factorsE)
    { assume "n div p > 3" "\<not> prime (n div p)"
      then obtain qs
        where "prime_factors (n div p) = set qs" "prod_list qs = (n div p)" "length qs \<ge> 2"
        using p' by atomize_elim (auto intro: less simp: div_gt_0)
      moreover
      have "prime_factors (p * (n div p)) = insert p (prime_factors (n div p))"
        using `3 < n` `2 \<le> p` `p \<le> n` `prime p`
      by (auto simp: prime_factors_product div_gt_0 prime_factors_of_prime)
      ultimately
      have "prime_factors n = set (p # qs)" "prod_list (p # qs) = n" "length (p#qs) \<ge> 2"
        using `p dvd n` by simp_all
      hence ?case by blast
    }
    moreover
    { assume "prime (n div p)"
      then obtain qs
        where "prime_factors (n div p) = set qs" "prod_list qs = (n div p)" "length qs = 1"
        using prime_factors_list_prime by blast
      moreover
      have "prime_factors (p * (n div p)) = insert p (prime_factors (n div p))"
        using `3 < n` `2 \<le> p` `p \<le> n` `prime p`
      by (auto simp: prime_factors_product div_gt_0 prime_factors_of_prime)
      ultimately
      have "prime_factors n = set (p # qs)" "prod_list (p # qs) = n" "length (p#qs) \<ge> 2"
        using `p dvd n` by simp_all
      hence ?case by blast
    } note case_prime = this
    moreover
    { assume "n div p = 1"
      hence "n = p" using `n>3`  using One_leq_div[OF `p dvd n`] p'(2) by force
      hence ?case using `prime p` `\<not> prime n` by auto
    }
    moreover
    { assume "n div p = 2"
      hence ?case using case_prime by force
    }
    moreover
    { assume "n div p = 3"
      hence ?case using p' case_prime by force
    }
    ultimately show ?case using p' div_gt_0[of p n] case_prime by fastforce

qed

lemma prod_list_ge:
  fixes xs::"nat list"
  assumes "\<forall> x \<in> set xs . x \<ge> 1"
  shows "prod_list xs \<ge> 1" using assms by (induction xs) auto

lemma sum_list_log:
  fixes b::real
  fixes xs::"nat list"
  assumes b: "b > 0" "b \<noteq> 1"
  assumes xs:"\<forall> x \<in> set xs . x \<ge> b"
  shows "(\<Sum>x\<leftarrow>xs. log b x) = log b (prod_list xs)"
  using assms
proof (induction xs)
  case Nil
    thus ?case by simp
  next
  case (Cons y ys)
    have "real (prod_list ys) > 0" using prod_list_ge Cons.prems by fastforce
    thus ?case using log_mult[OF Cons.prems(1-2)] Cons by force
qed

lemma concat_length_le:
  fixes g :: "nat \<Rightarrow> real"
  assumes "\<forall> x \<in> set xs . real (length (f x)) \<le> g x"
  shows "length (concat (map f xs)) \<le> (\<Sum>x\<leftarrow>xs. g x)" using assms
  by (induction xs) force+

lemma prime_gt_3_impl_p_minus_one_not_prime:
  fixes p::nat
  assumes "prime p" "p>3"
  shows "\<not> prime (p - 1)"
proof
  assume "prime (p - 1)"
  have "\<not> even p" using assms by (simp add: prime_odd_nat)
  hence "2 dvd (p - 1)" by presburger
  then obtain q where "p - 1 = 2 * q" ..
  then have "2 \<in> prime_factors (p - 1)" using `p>3`
    by (auto simp: prime_factorization_times_prime)
  thus False using prime_factors_of_prime `p>3` `prime (p - 1)` by auto
qed

text {*
  We now prove that Pratt's proof system is complete and derive upper bounds for
  the length and the size of the entries of a minimal certificate.
*}

theorem pratt_complete':
  assumes "prime p"
  shows "\<exists>c. Prime p \<in> set c \<and> valid_cert c \<and> length c \<le> 6*log 2 p - 4 \<and> (\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 p)" using assms
proof (induction p rule: less_induct)
  case (less p)
  from \<open>prime p\<close> have "p > 1" by (rule prime_gt_1_nat)
  then consider "p = 2" | " p = 3" | "p > 3" by force
  thus ?case
  proof cases
    assume [simp]: "p = 2"
    have "Prime p \<in> set [Prime 2, Triple 2 1 1]" by simp
    thus ?case by fastforce
  next
    assume [simp]: "p = 3"
    let ?cert = "[Prime 3, Triple 3 2 2, Triple 3 2 1, Prime 2, Triple 2 1 1]"

    have "length ?cert \<le> 6*log 2 p - 4 \<longleftrightarrow> 3 \<le> 2 * log 2 3" by simp
    also have "2 * log 2 3 = log 2 (3 ^ 2 :: real)" by (subst log_nat_power) simp_all
    also have "\<dots> = log 2 9" by simp
    also have "3 \<le> log 2 9 \<longleftrightarrow> True" by (subst le_log_iff) simp_all
    finally show ?case
      by (intro exI[where x = "?cert"]) (simp add: cong_def)
  next
    assume "p > 3"
    have qlp: "\<forall>q \<in> prime_factors (p - 1) . q < p" using `prime p`
      by (metis One_nat_def Suc_pred le_imp_less_Suc lessI less_trans p_in_prime_factorsE prime_gt_1_nat zero_less_diff)
    hence factor_certs:"\<forall>q \<in> prime_factors (p - 1) . (\<exists>c . ((Prime q \<in> set c) \<and> (valid_cert c)
                                                      \<and> length c \<le> 6*log 2 q - 4) \<and> (\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 q))"
      by (auto intro: less.IH)
    obtain a where a:"[a^(p - 1) = 1] (mod p) \<and> (\<forall> q. q \<in> prime_factors (p - 1)
              \<longrightarrow> [a^((p - 1) div q) \<noteq> 1] (mod p))" and a_size: "a > 0" "a < p"
      using converse_lehmer[OF `prime p`] by blast

    have "\<not> prime (p - 1)" using `p>3` prime_gt_3_impl_p_minus_one_not_prime `prime p` by auto
    have "p \<noteq> 4" using `prime p` by auto
    hence "p - 1 > 3" using `p > 3` by auto

    then obtain qs where prod_qs_eq:"prod_list qs = p - 1"
        and qs_eq:"set qs = prime_factors (p - 1)" and qs_length_eq: "length qs \<ge> 2"
      using prime_factors_list[OF _ `\<not> prime (p - 1)`] by auto
    obtain f where f:"\<forall>q \<in> prime_factors (p - 1) . \<exists> c. f q = c
                     \<and> ((Prime q \<in> set c) \<and> (valid_cert c) \<and> length c \<le> 6*log 2 q - 4)
                     \<and> (\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 q)"
      using factor_certs by metis
    let ?cs = "map f qs"
    have cs: "\<forall>q \<in> prime_factors (p - 1) . (\<exists>c \<in> set ?cs . (Prime q \<in> set c) \<and> (valid_cert c)
                                           \<and> length c \<le> 6*log 2 q - 4
                                           \<and> (\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 q))"
      using f qs_eq by auto

    have cs_cert_size: "\<forall>c \<in> set ?cs . \<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 p"
    proof
      fix c assume "c \<in> set (map f qs)"
      then obtain q where "c = f q" and "q \<in> set qs" by auto
      hence *:"\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 q" using f qs_eq by blast
      have "q < p" "q > 0" using qlp `q \<in> set qs` qs_eq prime_factors_gt_0_nat by auto
      show "\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 p"
      proof
        fix x assume "x \<in> set c"
        hence "size_pratt x \<le> 3 * log 2 q" using * by fastforce
        also have "\<dots> \<le> 3 * log 2 p" using `q < p` `q > 0` `p > 3` by simp
        finally show "size_pratt x \<le> 3 * log 2 p" .
      qed
    qed

    have cs_valid_all: "\<forall>c \<in> set ?cs . valid_cert c"
      using f qs_eq by fastforce

    have "\<forall>x \<in> set (build_fpc p a (p - 1) qs). size_pratt x \<le> 3 * log 2 p"
      using cs_cert_size a_size `p > 3` prod_qs_eq by (intro size_pratt_fpc) auto
    hence "\<forall>x \<in> set (build_fpc p a (p - 1) qs @ concat ?cs) . size_pratt x \<le> 3 * log 2 p"
      using cs_cert_size by auto
    moreover
    have "Triple p a (p - 1) \<in> set (build_fpc p a (p - 1) qs @ concat ?cs)" by (cases qs) auto
    moreover
    have "valid_cert ((build_fpc p a (p - 1) qs)@ concat ?cs)"
    proof (rule correct_fpc)
      show "valid_cert (concat ?cs)"
        using cs_valid_all by (auto simp: valid_cert_concatI)
      show "prod_list qs = p - 1" by (rule prod_qs_eq)
      show "p - 1 \<noteq> 0" using prime_gt_1_nat[OF `prime p`] by arith
      show "\<forall> q \<in> set qs . Prime q \<in> set (concat ?cs)"
        using concat_set[of "prime_factors (p - 1)"] cs qs_eq by blast
      show "\<forall> q \<in> set qs . [a^((p - 1) div q) \<noteq> 1] (mod p)" using qs_eq a by auto
    qed (insert \<open>p > 3\<close>, simp_all)
    moreover
    { let ?k = "length qs"

      have qs_ge_2:"\<forall>q \<in> set qs . q \<ge> 2" using qs_eq
        by (auto intro: prime_ge_2_nat)

      have "\<forall>x\<in>set qs. real (length (f x)) \<le> 6 * log 2 (real x) - 4" using f qs_eq by blast
      hence "length (concat ?cs) \<le> (\<Sum>q\<leftarrow>qs. 6*log 2 q - 4)" using concat_length_le
        by fast
      hence "length (Prime p # ((build_fpc p a (p - 1) qs)@ concat ?cs))
            \<le> ((\<Sum>q\<leftarrow>(map real qs). 6*log 2 q - 4) + ?k + 2)"
            by (simp add: o_def length_fpc)
      also have "\<dots> = (6*(\<Sum>q\<leftarrow>(map real qs). log 2 q) + (-4 * real ?k) + ?k + 2)"
        by (simp add: o_def sum_list_subtractf sum_list_triv sum_list_const_mult)
      also have "\<dots> \<le> 6*log 2 (p - 1) - 4" using `?k\<ge>2` prod_qs_eq sum_list_log[of 2 qs] qs_ge_2
        by force
      also have "\<dots> \<le> 6*log 2 p - 4" using log_le_cancel_iff[of 2 "p - 1" p] `p>3` by force
      ultimately have "length (Prime p # ((build_fpc p a (p - 1) qs)@ concat ?cs))
                       \<le> 6*log 2 p - 4" by linarith }
    ultimately obtain c where c:"Triple p a (p - 1) \<in> set c" "valid_cert c"
                               "length (Prime p #c) \<le> 6*log 2 p - 4"
                               "(\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 p)" by blast
    hence "Prime p \<in> set (Prime p # c)" "valid_cert (Prime p # c)"
         "(\<forall> x \<in> set (Prime p # c). size_pratt x \<le> 3 * log 2 p)"
    using a `prime p` by (auto simp: Primes.prime_gt_Suc_0_nat)
    thus ?case using c by blast
  qed
qed

text {*
  We now recapitulate our results. A number $p$ is prime if and only if there
  is a certificate for $p$. Moreover, for a prime $p$ there always is a certificate
  whose size is polynomially bounded in the logarithm of $p$.
*}

corollary pratt:
  "prime p \<longleftrightarrow> (\<exists>c. Prime p \<in> set c \<and> valid_cert c)"
  using pratt_complete' pratt_sound(1) by blast

corollary pratt_size:
  assumes "prime p"
  shows "\<exists>c. Prime p \<in> set c \<and> valid_cert c \<and> size_cert c \<le> (6 * log 2 p - 4) * (1 + 3 * log 2 p)"
proof -
  obtain c where c: "Prime p \<in> set c" "valid_cert c"
      and len: "length c \<le> 6*log 2 p - 4" and "(\<forall> x \<in> set c. size_pratt x \<le> 3 * log 2 p)"
    using pratt_complete' assms by blast
  hence "size_cert c \<le> length c * (1 + 3 * log 2 p)" by (simp add: size_pratt_le)
  also have "\<dots> \<le> (6*log 2 p - 4) * (1 + 3 * log 2 p)" using len by simp
  finally show ?thesis using c by blast
qed



subsection \<open>Proof Method Setup\<close>

text \<open>
  Using the following `lazy disjunction', we can force the simplifier to fully simplify the 
  first operand of the disjunction first and not evaluate the second one at all if the first 
  one simplifies to @{term True}. This improved performance three-fold in our simple test.
\<close>

definition LAZY_DISJ where
  "LAZY_DISJ a b \<longleftrightarrow> a \<or> b"

lemma eval_LAZY_DISJ [simp]: "LAZY_DISJ False b = b" "LAZY_DISJ True b = True"
  by (simp_all add: LAZY_DISJ_def)

lemma LAZY_DISJ_cong [cong]: "a = a' \<Longrightarrow> LAZY_DISJ a b = LAZY_DISJ a' b"
  by simp


text \<open>
  The following alternative definitions of valid certificates are better suited for 
  evaluation by the simplifier than the original ones.
\<close>

context
begin

lemma valid_cert_Cons1:
  "valid_cert (Prime p#xs) \<longleftrightarrow>
     p > 1 \<and> (\<exists>t\<in>set xs. case t of Prime _ \<Rightarrow> False | 
     Triple p' a x \<Rightarrow> p' = p \<and> x = p - 1 \<and> mod_exp a (p-1) p = 1 ) \<and> valid_cert xs"
  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs by (auto simp: mod_exp_def cong_def split: pratt.splits)
next
  assume ?rhs
  hence "p > 1" "valid_cert xs" by blast+
  moreover from \<open>?rhs\<close> obtain t where "t \<in> set xs" "case t of Prime _ \<Rightarrow> False | 
     Triple p' a x \<Rightarrow> p' = p \<and> x = p - 1 \<and> [a^(p-1) = 1] (mod p)" 
     by (auto simp: cong_def mod_exp_def cong: pratt.case_cong)
  ultimately show ?lhs by (cases t) auto
qed

private lemma Suc_0_mod_eq_Suc_0_iff:
  "Suc 0 mod n = Suc 0 \<longleftrightarrow> n \<noteq> Suc 0"
proof -
  consider "n = 0" | "n = Suc 0" | "n > 1" by (cases n) auto
  thus ?thesis by cases auto
qed

private lemma Suc_0_eq_Suc_0_mod_iff:
  "Suc 0 = Suc 0 mod n \<longleftrightarrow> n \<noteq> Suc 0"
  using Suc_0_mod_eq_Suc_0_iff by (simp add: eq_commute)

lemma valid_cert_Cons2:
  "valid_cert (Triple p a x # xs) \<longleftrightarrow> x > 0 \<and> p > 1 \<and> (LAZY_DISJ (x = 1) (
     (\<exists>t\<in>set xs. case t of Prime _ \<Rightarrow> False |
        Triple p' a' y \<Rightarrow> p' = p \<and> a' = a \<and> y dvd x \<and> 
        (let q = x div y in Prime q \<in> set xs \<and> mod_exp a ((p-1) div q) p \<noteq> 1)))) \<and> valid_cert xs"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  from \<open>?lhs\<close> have pos: "x > 0" and gt_1: "p > 1" and valid: "valid_cert xs" by simp_all
  show ?rhs
  proof (cases "x = 1")
    case True
    with \<open>?lhs\<close> show ?thesis by auto
  next
    case False
    with \<open>?lhs\<close> have "(\<exists>q y. x = q * y \<and> Prime q \<in> set xs \<and> Triple p a y \<in> set xs
      \<and> [a^((p - 1) div q) \<noteq> 1] (mod p))" by auto
    then guess q y by (elim exE conjE) note qy = this
    hence "(\<exists>t\<in>set xs. case t of Prime _ \<Rightarrow> False |
        Triple p' a' y \<Rightarrow> p' = p \<and> a' = a \<and> y dvd x \<and> 
        (let q = x div y in Prime q \<in> set xs \<and> mod_exp a ((p-1) div q) p \<noteq> 1))"
    using pos gt_1 by (intro bexI [of _ "Triple p a y"]) 
      (auto simp: Suc_0_mod_eq_Suc_0_iff Suc_0_eq_Suc_0_mod_iff cong_def mod_exp_def)
    with pos gt_1 valid show ?thesis unfolding LAZY_DISJ_def by blast
  qed
next
  assume ?rhs
  hence pos: "x > 0" and gt_1: "p > 1" and valid: "valid_cert xs" by simp_all
  show ?lhs
  proof (cases "x = 1")
    case True
    with \<open>?rhs\<close> show ?thesis by auto
  next
    case False
    with \<open>?rhs\<close> obtain t where t: "t \<in> set xs" "case t of Prime x \<Rightarrow> False
         | Triple p' a' y \<Rightarrow> p' = p \<and> a' = a \<and> y dvd x \<and> (let q = x div y
              in Prime q \<in> set xs \<and> mod_exp a ((p - 1) div q) p \<noteq> 1)" by auto
    then obtain y where y: "t = Triple p a y" "y dvd x" "let q = x div y in Prime q \<in> set xs \<and> 
                              mod_exp a ((p - 1) div q) p \<noteq> 1" 
      by (cases t rule: pratt.exhaust) auto
    with gt_1 have y': "let q = x div y in Prime q \<in> set xs \<and> [a^((p - 1) div q) \<noteq> 1] (mod p)"
      by (auto simp: cong_def Let_def mod_exp_def Suc_0_mod_eq_Suc_0_iff Suc_0_eq_Suc_0_mod_iff)
    define q where "q = x div y"
    have "\<exists>q y. x = q * y \<and> Prime q \<in> set xs \<and> Triple p a y \<in> set xs
                     \<and> [a^((p - 1) div q) \<noteq> 1] (mod p)"
      by (rule exI[of _ q], rule exI[of _ y]) (insert t y y', auto simp: Let_def q_def)
    with pos gt_1 valid show ?thesis unfolding LAZY_DISJ_def by simp
  qed
qed

declare valid_cert.simps(2,3) [simp del]

lemmas eval_valid_cert = valid_cert.simps(1) valid_cert_Cons1 valid_cert_Cons2

private lemma bex_simps_lazy: "Bex {} P = False" "Bex (insert x A) P = LAZY_DISJ (P x) (Bex A P)"
  unfolding LAZY_DISJ_def by simp_all

lemma pratt_primeI:
  assumes "valid_cert xs" "Prime p \<in> set xs"
  shows   "prime p"
  using pratt_sound[OF assms] by simp

ML_file "pratt.ML"

end


method_setup pratt = \<open>
  Scan.option (Scan.lift (Args.bracks Pratt.parse_cert)) >> 
    (SIMPLE_METHOD o HEADGOAL oo Pratt.pratt_tac true)
\<close> "Prove primality of natural numbers using Pratt certificates."


text \<open>
  The following two theorems serve as regression tests -- the first one computes the 
  certificate in ML automatically, whereas the second one uses a pre-computed certificate.
  The first example should not take more than a few seconds; the second one no more than 
  30 seconds or so.
\<close>

lemma "prime (2503 :: nat)"
  by pratt

lemma "prime (131059 :: nat)"
  by (pratt [131059, (131059, 2, 131058), (131059, 2, 65529), (131059, 2, 21843),
              (131059, 2, 7281), (131059, 2, 2427), (131059, 2, 809), (131059, 2, 1), 809,
              (809, 3, 808), (809, 3, 404), (809, 3, 202), (809, 3, 101), (809, 3, 1), 101,
              (101, 2, 100), (101, 2, 50), (101, 2, 25), (101, 2, 5), (101, 2, 1), 5,
              (5, 2, 4), (5, 2, 2), (5, 2, 1), 3, (3, 2, 2), (3, 2, 1), 2, (2, 1, 1)])
  

end
