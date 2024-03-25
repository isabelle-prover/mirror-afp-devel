theory Correct_new

imports Crypto_Scheme_new
    Delta_Correct
    MLWE

begin
unbundle %invisible lifting_syntax
no_adhoc_overloading %invisible Monad_Syntax.bind bind_pmf
declare %invisible [[names_short]]

section \<open>$\delta$-Correctness of Kyber without Compression of the Public Key\<close>

text \<open>The functions \<open>key_gen_new\<close>, \<open>encrypt_new\<close> and \<open>decrypt\<close> are deterministic functions that 
calculate the output of the Kyber algorithms for a given input. To completely model the Kyber 
algorithms, we need to model the random choice of the input as well. 
This results in probabilistic programs that first choose the input according the the input 
distributions and then calculate the output.
Probabilistic programs are modeled by the Giry monad of \<open>pmf\<close>'s. The correspond to the 
probability mass functions of the output.\<close>

subsection \<open>Definition of Probabilistic Kyber without Key Compression and $\delta$\<close>

text \<open>The correctness of Kyber is formulated in a locale that defines the necessary assumptions 
on the parameter set. For the correctness analysis we need to import the definitions of
the probability distribution $\beta_\eta$ from the module-LWE and the Kyber locale itself.
Moreover, we fix the compression depths for the outputs $u$ and $v$.
Note that in this case the output $t$ of the key generation is uncompressed.\<close>

locale kyber_cor_new = mlwe: module_lwe "(TYPE('a ::qr_spec))" "TYPE('k::finite)" k  +
kyber_spec _ _ _ _ "(TYPE('a ::qr_spec))" "TYPE('k::finite)"  +
fixes type_a :: "('a :: qr_spec) itself" 
  and type_k :: "('k ::finite) itself" 
  and du dv ::nat
begin

text \<open>We define types for the private and public keys, as well as plain and cipher texts.
The public key consists of a matrix $A \in R_q^{k\times k}$ and a vector $t\in R_q^k$.
The private key is the secret vector $s \in R_q$ such that there is an error vector $e\in R_q^k$ 
such that $A\cdot s + e = t$ (uncompressed).
The plaintext consists of a bitstring (ie.\ a list of booleans).
The ciphertext is an element of $R_q^{k+1}$represented by a vector $u$ in $R_q^k$ and a value
$v \in R_q$ (both compressed).\<close>


type_synonym ('b,'l) pk = "((('b,'l) vec,'l) vec) \<times> (('b,'l) vec)"
type_synonym ('b,'l) sk = "('b,'l) vec"
type_synonym plain = bitstring
type_synonym ('b,'l) cipher = "('b,'l) vec \<times> 'b"

text \<open>First, we need to show properties on the probability distributions needed. 
\<open>beta\<close> is the centered binomial distribution defined in \<open>mlwe\<close>.\<close>

lemma finite_bit_set:
"finite mlwe.bit_set"
unfolding mlwe.bit_set_def
  by (simp add: finite_lists_length_eq)


lemma finite_beta:
"finite (set_pmf mlwe.beta)"
unfolding mlwe.beta_def
  by (meson UNIV_I finite_qr finite_subset subsetI)


lemma finite_beta_vec:
"finite (set_pmf mlwe.beta_vec)"
unfolding mlwe.beta_vec_def
  by (meson finite_UNIV_vec finite_subset top.extremum)

text \<open>Next, we define the key generation, encryption and decryption as probabilistic programs
which first generate random variables according to their distributions and then call the 
key generation, encryption or decryption functions accordingly.
Since we look at Kyber without compression of the public key, the output of the key generation
is uncompressed.

Note that in comparison to Kyber with public key compression, we do not need to output the
error term $e$. Since $t$ is uncompressed, we can easily recompute $e$ using the secret key $s$.\<close>

definition pmf_key_gen  where
"pmf_key_gen = do {
  A \<leftarrow> pmf_of_set (UNIV:: (('a qr,'k) vec,'k) vec set);
  s \<leftarrow> mlwe.beta_vec;
  e \<leftarrow> mlwe.beta_vec;
  let t = key_gen_new A s e;
  return_pmf ((A, t), s)
}"

definition pmf_encrypt where
"pmf_encrypt pk m = do{
  r \<leftarrow> mlwe.beta_vec;
  e1 \<leftarrow> mlwe.beta_vec;
  e2 \<leftarrow> mlwe.beta;
  let c = encrypt_new (snd pk) (fst pk) r e1 e2 du dv m;
  return_pmf c
}"

text \<open>\<open>Msgs\<close> is the space of all possible messages to be encrypted. It is non-empty and finite.\<close>

definition 
"Msgs = {m::'a qr. set ((coeffs \<circ> of_qr) m) \<subseteq> {0,1}}"

lemma finite_Msgs:
"finite Msgs"
unfolding Msgs_def
  by (meson finite_qr rev_finite_subset subset_UNIV)

lemma Msgs_nonempty:
"Msgs \<noteq> {}" 
proof -
  have "to_qr (Poly [0]) \<in> Msgs" unfolding Msgs_def by auto
  then show ?thesis by auto
qed

text \<open>Since Kyber is a PKE, we can instantiate the PKE correctness locale with the Kyber 
algorithms without compression of the public key.\<close>

no_adhoc_overloading Monad_Syntax.bind bind_pmf

sublocale pke_delta_correct pmf_key_gen pmf_encrypt 
  "(\<lambda> sk c. decrypt (fst c) (snd c) sk du dv)" Msgs .

adhoc_overloading Monad_Syntax.bind bind_pmf

text \<open>In order to measure and estimate the errors introduced by the compression and decompression 
of the output of the encryption, we introduce \<open>error_dist_vec\<close> on vectors and \<open>error_dist_poly\<close> 
on polynomials.\<close>

definition 
"error_dist_vec d = do{
  y \<leftarrow> pmf_of_set (UNIV :: ('a qr,'k) vec set);
  return_pmf (decompress_vec d (compress_vec d y)-y)
}"

definition 
"error_dist_poly d = do{
  y \<leftarrow> pmf_of_set (UNIV :: 'a qr set);
  return_pmf (decompress_poly d (compress_poly d y)-y)
}"

text \<open>The functions \<open>w_distrib'\<close>, \<open>w_distrib\<close> and \<open>delta\<close> define the originally claimed $\delta$ 
for the correctness of Kyber. 
However, the \<open>delta\<close>-correctness of Kyber could not be formalized. 

The reason is that the values of \<open>cu\<close> and \<open>cv\<close> in \<open>w_distrib'\<close> rely on the compression error 
of uniformly random generated values. In truth, these values are not uniformly generated but 
instances of the module-LWE. 
\<open>delta\<close> also adds the additional error due to the module-learning with error instances.
However, we cannot use the module-LWE assumption to reduce these 
values to uniformly generated ones since we would lose all information about the secret key 
otherwise. This is needed to perform the decryption in order to check whether the original message 
and the decryption of the ciphertext are indeed the same.

Therefore, we modified the given $\delta$ and defined a new value \<open>delta'\<close> in order to prove at 
least \<open>delta'\<close>-correctness.\<close>

definition w_distrib' where
"w_distrib' s e = do{
  r \<leftarrow> mlwe.beta_vec;
  e1 \<leftarrow> mlwe.beta_vec;
  e2 \<leftarrow> mlwe.beta;
  cu \<leftarrow> error_dist_vec du;
  cv \<leftarrow> error_dist_poly dv;
  let w = (scalar_product e r + e2 + cv - scalar_product s e1 - scalar_product s cu);
  return_pmf (abs_infty_poly w \<ge> round (q/4))}"

definition w_distrib where
"w_distrib = do{
  s \<leftarrow> mlwe.beta_vec;
  e \<leftarrow> mlwe.beta_vec;
  w_distrib' s e}"

definition delta where
"delta Adv0 Adv1 = pmf w_distrib True + mlwe.advantage Adv0 + mlwe.advantage1 Adv1"

text \<open>This is the modified $\delta'$ which makes the correctness arguments to go through.\<close>

text \<open>The functions \<open>w_kyber\<close>, \<open>delta'\<close> and \<open>delta_kyber\<close> define the modified $\delta$ 
for the correctness proof. Note the in \<open>w_kyber\<close>, the values \<open>yu\<close> and \<open>yv\<close> are generated 
according to their corresponding module-LWE instances and are not uniformly random.
\<open>delta'\<close> is still dependent on the public and secret keys and the message.
This dependency is eliminated in \<open>delta_kyber\<close> by taking the expectation over the key pair and 
the maximum over all messages, similar to the definition of $\delta$-correctness.\<close>

definition w_kyber where
"w_kyber A s e m = do{
  r \<leftarrow> mlwe.beta_vec;
  e1 \<leftarrow> mlwe.beta_vec;
  e2 \<leftarrow> mlwe.beta;
  let t = A *v s + e;
  let yu = transpose A *v r + e1; 
  let yv = (scalar_product t r + e2 + 
           to_module (round (real_of_int q / 2)) * m);
  let cu = compress_error_vec du yu;
  let cv = compress_error_poly dv yv;
  let w = (scalar_product e r + e2 + cv - scalar_product s e1 - scalar_product s cu);
  return_pmf (abs_infty_poly w \<ge> round (q/4))}"

definition delta' where
"delta' sk pk m = pmf (w_kyber (fst pk) sk (snd pk - (fst pk) *v sk) m) True"

definition delta_kyber where
"delta_kyber = measure_pmf.expectation pmf_key_gen
     (\<lambda>(pk, sk). MAX m\<in>Msgs. delta' sk pk m)"

subsection \<open>$\delta$-Correctness Proof\<close>

text \<open>The idea to bound the probabilistic Kyber algorithms by \<open>delta_kyber\<close> is the following:
First use the deterministic part given by \<open>Crypto_Scheme_new.kyber_new_correct\<close> to bound
the correctness by \<open>delta'\<close> depending on a fixed key pair and message.
Then bound the message by the maximum over all messages.
Finally bound the key pair by using the expectation over the key pair.
The result is that the correctness error of the Kyber PKE is bounded by \<open>delta_kyber\<close>.\<close>

text \<open>First of all, we rewrite the deterministic part of the correctness proof \<open>kyber_new_correct\<close>
from \<open>Crypto_Scheme_new\<close>.\<close>

lemma kyber_new_correct_alt:
  fixes A s r e e1 e2 cu cv t u v
  assumes t_def:   "t = key_gen_new A s e"
  and u_v_def: "(u,v) = encrypt_new t A r e1 e2 du dv m"
  and cu_def:  "cu = compress_error_vec du  ((transpose A) *v r + e1)"
  and cv_def:  "cv = compress_error_poly dv  (scalar_product t r + e2 + 
                 to_module (round((real_of_int q)/2)) * m)"
  and error: "decrypt u v s du dv \<noteq> m"
  and m01:     "set ((coeffs \<circ> of_qr) m) \<subseteq> {0,1}"
  shows "abs_infty_poly (scalar_product e r + e2 + cv - scalar_product s e1 - 
           scalar_product s cu) \<ge> round (real_of_int q / 4)"
using kyber_new_correct[OF assms(1-4) _ m01]
using assms(5) by linarith

text \<open>Then we show the correctness in the probabilistic program for a fixed key pair and message.
The bound we use is \<open>delta'\<close>.\<close>

lemma correct_key_gen:
fixes A s e m
assumes pk_sk: "(pk, sk) = ((A, key_gen_new A s e), s)"
  and m_Msgs: "m\<in>Msgs"
shows "pmf (do{c \<leftarrow> pmf_encrypt pk m;
  return_pmf (decrypt (fst c) (snd c) sk du dv \<noteq> m)}) True \<le> delta' sk pk m"
proof -
  have "s = sk" using assms(1) by blast
  define ind1 where "ind1 = (\<lambda> r e1 e2. indicat_real 
    {e2. decrypt (fst (encrypt_new (snd pk) (fst pk) r e1 e2 du dv m))
    (snd (encrypt_new (snd pk) (fst pk) r e1 e2 du dv m)) sk du dv \<noteq> m} e2)" 
  define ind2 where "ind2 = (\<lambda>r e1 e2. indicat_real {e2. (round (real_of_int q / 4)
    \<le> abs_infty_poly (scalar_product (snd pk - fst pk *v sk) r + e2 +
         compress_error_poly dv (scalar_product (snd pk) r + e2 +
         to_module (round (real_of_int q / 2)) * m) - scalar_product sk e1 - 
         scalar_product sk (compress_error_vec du (r v* fst pk + e1))))} e2)"
  have "ind1 r e1 e2 \<le> ind2 r e1 e2 "
    for r e1 e2
  proof (cases "ind1 r e1 e2 = 0")
    case True
    show ?thesis unfolding True by (auto simp add: ind2_def sum_nonneg)
  next
    case False
    then have one: "ind1 r e1 e2 = 1" unfolding ind1_def indicator_def by simp
    define u where "u = fst (encrypt_new (snd pk) (fst pk) r e1 e2 du dv m)"
    define v where "v = snd (encrypt_new (snd pk) (fst pk) r e1 e2 du dv m)"
    define cu  where "cu = compress_error_vec du ((transpose (fst pk)) *v r + e1)"
    define cv where "cv = compress_error_poly dv (scalar_product (snd pk) r + e2 + 
       to_module (round((real_of_int q)/2)) * m)"
    define e' where "e' = (snd pk) -(fst pk) *v sk"
    have m: "set ((coeffs \<circ> of_qr) m) \<subseteq> {0, 1}" using \<open>m\<in>Msgs\<close> unfolding Msgs_def by simp
    have cipher: "(u,v) = encrypt_new (snd pk) (fst pk) r e1 e2 du dv m"
      unfolding u_def v_def by simp
    have decrypt: "decrypt u v s du dv \<noteq> m" using one
      using assms(1) u_def v_def ind1_def by force
    have two: "ind2 r e1 e2 = 1" unfolding ind2_def
      using kyber_new_correct_alt[OF _ cipher cu_def cv_def decrypt m, of e']
      unfolding \<open>s=sk\<close> by (simp add: cu_def cv_def e'_def key_gen_new_def pk_sk)
    show ?thesis using one two by simp
  qed
  then have "(\<Sum>e2\<in>UNIV. pmf mlwe.beta e2 * ind1 r e1 e2)
    \<le> (\<Sum>e2\<in>UNIV. pmf mlwe.beta e2 *  ind2 r e1 e2)"
    for r e1
  by (intro sum_mono) (simp add: mult_left_mono)
  then have "(\<Sum>e1\<in>UNIV. pmf mlwe.beta_vec e1 * (\<Sum>e2\<in>UNIV. pmf mlwe.beta e2 * ind1 r e1 e2))
    \<le> (\<Sum>e1\<in>UNIV. pmf mlwe.beta_vec e1 * (\<Sum>e2\<in>UNIV. pmf mlwe.beta e2 * 
       ind2 r e1 e2))"
    for r 
  by (intro sum_mono) (simp add: mult_left_mono)
  then have "(\<Sum>r\<in>UNIV. pmf mlwe.beta_vec r * (\<Sum>e1\<in>UNIV. pmf mlwe.beta_vec e1 * 
      (\<Sum>e2\<in>UNIV. pmf mlwe.beta e2 * ind1 r e1 e2)))
    \<le> (\<Sum>r\<in>UNIV. pmf mlwe.beta_vec r * (\<Sum>e1\<in>UNIV. pmf mlwe.beta_vec e1 * (\<Sum>e2\<in>UNIV. pmf mlwe.beta e2 * 
       ind2 r e1 e2 )))"
  by (intro sum_mono) (simp add: mult_left_mono) 
  then show ?thesis unfolding delta'_def w_kyber_def pmf_encrypt_def Let_def ind1_def ind2_def
  by (simp add: bind_assoc_pmf pmf_bind integral_measure_pmf[of UNIV] sum_distrib_left)
qed

text \<open>Now take the maximum over all messages. We rewrite this in order to be able to instantiate 
it nicely.\<close>

lemma correct_key_gen_max:
fixes A s e m
assumes "(pk, sk) = ((A, key_gen_new A s e), s)"
  and "m\<in>Msgs"
shows "pmf (do{c \<leftarrow> pmf_encrypt pk m;
  return_pmf (decrypt (fst c) (snd c) sk du dv \<noteq> m)}) True \<le> (MAX m'\<in>Msgs. delta' sk pk m')"
using correct_key_gen[OF assms] 
by (meson Lattices_Big.linorder_class.Max.coboundedI assms(2) basic_trans_rules(23) 
  finite_Msgs finite_imageI image_eqI)

lemma correct_max:
fixes A s e
assumes "(pk, sk) = ((A, key_gen_new A s e), s)"
shows "(MAX m\<in>Msgs. pmf (do{c \<leftarrow> pmf_encrypt pk m;
  return_pmf (decrypt (fst c) (snd c) sk du dv \<noteq> m)}) True) \<le> (MAX m'\<in>Msgs. delta' sk pk m')"
using correct_key_gen_max[OF assms]
by (simp add: Msgs_nonempty finite_Msgs)

lemma correct_max':
fixes pk sk
shows "(MAX m\<in>Msgs. pmf (do{c \<leftarrow> pmf_encrypt pk m;
  return_pmf (decrypt (fst c) (snd c) sk du dv \<noteq> m)}) True) \<le> 
  (MAX m'\<in>Msgs. delta' sk pk m')"
using correct_max[of pk sk] unfolding key_gen_new_def 
by (metis (no_types, lifting) Groups.ab_semigroup_add_class.add.commute 
  Product_Type.old.prod.exhaust diff_add_cancel)


text \<open>Finally show the overall bound \<open>delta_kyber\<close> for the correctness error of the Kyber PKE
without compression of the public key.\<close>

lemma expect_correct:
"expect_correct \<le> delta_kyber"
unfolding expect_correct_def delta_kyber_def using correct_max'
proof (subst integral_measure_pmf[of UNIV], goal_cases)
  case 3
  then show ?case proof (subst integral_measure_pmf[of UNIV], goal_cases)
  case 3
  then show ?case 
    by (intro sum_mono, unfold real_scaleR_def, intro mult_left_mono)  auto 
  qed (auto simp add: finite_prod)
qed (auto simp add: finite_prod)

text \<open>This yields the overall \<open>delta_kyber\<close>-correctness of Kyber without compression of the 
public key.\<close>

lemma delta_correct_kyber:
"delta_correct delta_kyber"
using expect_correct delta_correct_def by auto

no_adhoc_overloading %invisible Monad_Syntax.bind bind_pmf


end
end