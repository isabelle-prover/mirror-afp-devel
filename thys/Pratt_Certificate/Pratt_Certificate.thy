theory Pratt_Certificate
imports
  Complex_Main
  "../Lehmer/Lehmer"
begin

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
| R1: "valid_cert (Triple p a x # xs) \<longleftrightarrow> 0 < x  \<and> valid_cert xs \<and> (x=1 \<or>
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


section {* Soundness *}

text {*
  In Section \ref{sec:pratt} we introduced the predicates $\text{Prime}(p)$ and $(p, a, x)$.
  In this section we show that for a certificate every predicate occuring in this certificate
  holds. In particular, if $\text{Prime}(p)$ occurs in a certificate, $p$ is prime.
*}

lemma prime_factors_one[simp]: shows "prime_factors (Suc 0) = {}"
  by (auto simp add:prime_factors_altdef2_nat)

lemma prime_factors_prime: fixes p :: nat assumes "prime p" shows "prime_factors p = {p}"
proof
  have "0 < p" using assms by (simp add: prime_gt_0_nat) 
  then show "{p} \<subseteq> prime_factors p" using assms by (auto simp add: prime_factors_altdef2_nat)
  { fix q assume "q \<in> prime_factors p"
    then have "q dvd p" "prime q" using `0<p` by (auto simp add:prime_factors_altdef2_nat)
    with assms have "q=p" by (auto simp: prime_def)
    }
  then
  show "prime_factors p \<subseteq> {p}" by auto
qed

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
      by (simp add:prime_factors_product_nat prime_factors_prime)
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



section {* Completeness *}

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
  assumes "valid_cert xs"
  assumes "listprod qs = r" "r \<noteq> 0"
  assumes "\<forall> q \<in> set qs . Prime q \<in> set xs"
  assumes "\<forall> q \<in> set qs . [a^((p - 1) div q) \<noteq> 1] (mod p)"
  shows "valid_cert (build_fpc p a r qs @ xs)"
  using assms
proof (induction qs arbitrary: r)
  case Nil thus ?case by auto
next
  case (Cons y ys)
  have "listprod ys = r div y" using Cons.prems by auto
  then have T_in: "Triple p a (listprod ys) \<in> set (build_fpc p a (r div y) ys @ xs)"
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
  assumes "a \<le> p" "r \<le> p" "0 < a" "0 < r" "0 < p" "listprod qs = r"
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
  moreover hence "listprod qs = r div q" using Cons.prems(6) by auto
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

  from assms show "p dvd n" by (intro prime_factors_dvd_nat)
  then show "p \<le> n" using  `0 < n` by (rule dvd_imp_le)
qed

lemma prime_factors_list_prime:
  fixes n :: nat
  assumes "prime n"
  shows "\<exists> qs. prime_factors n = set qs \<and> listprod qs = n \<and> length qs = 1"
proof -
    have "prime_factors n = set [n]" using prime_factors_prime assms by force
    thus ?thesis by fastforce
qed

lemma prime_factors_list:
  fixes n :: nat assumes "3 < n" "\<not> prime n"
  shows "\<exists> qs. prime_factors n = set qs \<and> listprod qs = n \<and> length qs \<ge> 2"
  using assms
proof (induction n rule: less_induct)
  case (less n)
    obtain p where "p \<in> prime_factors n" using `n > 3` prime_factors_elem by force
    then have p':"2 \<le> p" "p \<le> n" "p dvd n" "prime p"
      using `3 < n` by (auto elim: p_in_prime_factorsE)
    { assume "n div p > 3" "\<not> prime (n div p)"
      then obtain qs
        where "prime_factors (n div p) = set qs" "listprod qs = (n div p)" "length qs \<ge> 2"
        using p' by atomize_elim (auto intro: less simp: div_gt_0)
      moreover
      have "prime_factors (p * (n div p)) = insert p (prime_factors (n div p))"
        using `3 < n` `2 \<le> p` `p \<le> n` `prime p`
      by (auto simp: prime_factors_product_nat div_gt_0 prime_factors_prime)
      ultimately
      have "prime_factors n = set (p # qs)" "listprod (p # qs) = n" "length (p#qs) \<ge> 2"
        using `p dvd n` by (simp_all add: dvd_mult_div_cancel)
      hence ?case by blast
    }
    moreover
    { assume "prime (n div p)"
      then obtain qs
        where "prime_factors (n div p) = set qs" "listprod qs = (n div p)" "length qs = 1"
        using prime_factors_list_prime by blast
      moreover
      have "prime_factors (p * (n div p)) = insert p (prime_factors (n div p))"
        using `3 < n` `2 \<le> p` `p \<le> n` `prime p`
      by (auto simp: prime_factors_product_nat div_gt_0 prime_factors_prime)
      ultimately
      have "prime_factors n = set (p # qs)" "listprod (p # qs) = n" "length (p#qs) \<ge> 2"
        using `p dvd n` by (simp_all add: dvd_mult_div_cancel)
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

lemma listprod_ge:
  fixes xs::"nat list"
  assumes "\<forall> x \<in> set xs . x \<ge> 1"
  shows "listprod xs \<ge> 1" using assms by (induction xs) auto

lemma listsum_log:
  fixes b::real
  fixes xs::"nat list"
  assumes b: "b > 0" "b \<noteq> 1"
  assumes xs:"\<forall> x \<in> set xs . x \<ge> b"
  shows "(\<Sum>x\<leftarrow>xs. log b x) = log b (listprod xs)"
  using assms
proof (induction xs)
  case Nil
    thus ?case by simp
  next
  case (Cons y ys)
    have "real (listprod ys) > 0" using listprod_ge Cons.prems by fastforce
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
  hence "2 \<in> prime_factors (p - 1)" using `p>3` by (auto simp: prime_factors_altdef2_nat)
  thus False using prime_factors_prime `p>3` `prime (p - 1)` by auto
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
  { assume [simp]: "p = 2"
    have "Prime p \<in> set [Prime 2, Triple 2 1 1]" by simp
    then have ?case by fastforce }
  moreover
  { assume [simp]: "p = 3"
    let ?cert = "[Prime 3, Triple 3 2 2, Triple 3 2 1, Prime 2, Triple 2 1 1]"

    have "length ?cert \<le> 6*log 2 p - 4
          \<longleftrightarrow> 2 powr 9 \<le> 2 powr (log 2 p * 6)" by auto
    also have "\<dots> \<longleftrightarrow> True"
      by (simp add: powr_powr[symmetric] powr_numeral)
    finally have ?case
      by (intro exI[where x="?cert"]) (simp add: cong_nat_def)
  }
  moreover
  { assume "p > 3"
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

    then obtain qs where prod_qs_eq:"listprod qs = p - 1"
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
      show "listprod qs = p - 1" by (rule prod_qs_eq)
      show "p - 1 \<noteq> 0" using prime_gt_1_nat[OF `prime p`] by arith
      show "\<forall> q \<in> set qs . Prime q \<in> set (concat ?cs)"
        using concat_set[of "prime_factors (p - 1)"] cs qs_eq by blast
      show "\<forall> q \<in> set qs . [a^((p - 1) div q) \<noteq> 1] (mod p)" using qs_eq a by auto
    qed
    moreover
    { let ?k = "length qs"

      have qs_ge_2:"\<forall>q \<in> set qs . q \<ge> 2" using qs_eq
        by (simp add: prime_factors_prime_nat prime_ge_2_nat)

      have "\<forall>x\<in>set qs. real (length (f x)) \<le> 6 * log 2 (real x) - 4" using f qs_eq by blast
      hence "length (concat ?cs) \<le> (\<Sum>q\<leftarrow>qs. 6*log 2 q - 4)" using concat_length_le
        by fast
      hence "length (Prime p # ((build_fpc p a (p - 1) qs)@ concat ?cs))
            \<le> ((\<Sum>q\<leftarrow>(map real qs). 6*log 2 q - 4) + ?k + 2)"
            by (simp add: o_def length_fpc)
      also have "\<dots> = (6*(\<Sum>q\<leftarrow>(map real qs). log 2 q) + (-4 * real ?k) + ?k + 2)"
        by (simp add: o_def listsum_subtractf listsum_triv listsum_const_mult)
      also have "\<dots> \<le> 6*log 2 (p - 1) - 4" using `?k\<ge>2` prod_qs_eq listsum_log[of 2 qs] qs_ge_2
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
    hence ?case using c by blast
  }
  moreover have "p\<ge>2" using less by (simp add: prime_ge_2_nat)
  ultimately show ?case using less by fastforce
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

end
