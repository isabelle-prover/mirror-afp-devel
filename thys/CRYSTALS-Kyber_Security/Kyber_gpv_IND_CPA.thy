theory Kyber_gpv_IND_CPA


imports "Game_Based_Crypto.CryptHOL_Tutorial"
        Correct_new

begin
unbundle %invisible lifting_syntax
declare %invisible [[names_short]]

section \<open>IND-CPA Security of Kyber\<close>

text \<open>The IND-CPA security of the Kyber PKE is based on the module-LWE.
It takes the length \<open>len_plain\<close> of the plaintexts in the security games as an input.
Note that the security proof is for the uncompressed scheme only! That means that the output 
of the key generation is not compressed and the input of the encryption is not 
decompressed.
The compression/decompression would entail that the decompression of the value \<open>t\<close> from the 
key generation is not distributed uniformly at random any more (because of the compression error).
This prohibits the second reduction to module-LWE.
In order to avoid this, the compression and decompression in key generation and encryption 
have been omitted from the second round of the NIST standardisation process onwards.\<close>

locale kyber_new_security =  kyber_cor_new _ _ _ _ _ _ "TYPE('a::qr_spec)" "TYPE('k::finite)" +
  ro: random_oracle len_plain
for len_plain :: nat +
fixes type_a :: "('a :: qr_spec) itself" 
  and type_k :: "('k ::finite) itself"
begin

text \<open>The given plaintext as a bitstring needs to be converted to an element in $R_q$.
The bitstring is respresented as an integer value by interpreting the bitstring as a binary number.
The integer is then converted to an element in $R_q$ by the function \<open>to_module\<close>.
Conversely, the bitstring representation can by extracted from the coefficient of the 
element in $R_q$.\<close>

definition bitstring_to_int:
"bitstring_to_int msg = (\<Sum>i<length msg. if msg!i then  2^i else 0)"
       
definition plain_to_msg :: "bitstring \<Rightarrow> 'a qr" where
"plain_to_msg msg = to_module (bitstring_to_int msg)"

definition msg_to_plain :: "'a qr \<Rightarrow> bitstring" where
"msg_to_plain msg = map (\<lambda>i. i=0) (coeffs (of_qr msg))"

subsection \<open>Instantiation of \<open>ind_cpa\<close> Locale with Kyber\<close>

text \<open>We only look at the uncompressed version of Kyber. 
As the IND-CPA locale works over the generative probabilistic values type \<open>gpv\<close>,
we need to lift our definitions to \<open>gpv\<close>'s.\<close>

text \<open>The lifting of the key generation:\<close>

definition gpv_key_gen where
"gpv_key_gen = lift_spmf (spmf_of_pmf pmf_key_gen)"

lemma spmf_pmf_of_set_UNIV:
"spmf_of_set (UNIV:: (('a qr,'k) vec,'k) vec set) =  
  spmf_of_pmf (pmf_of_set (UNIV:: (('a qr,'k) vec,'k) vec set))"
unfolding spmf_of_set_def by simp

lemma key_gen:
"gpv_key_gen = lift_spmf ( do {
    A \<leftarrow> spmf_of_set (UNIV:: (('a qr, 'k) vec, 'k) vec set);
    s \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    e \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    let t = key_gen_new A s e;
    return_spmf ((A, t),s)
  })"
unfolding gpv_key_gen_def pmf_key_gen_def unfolding spmf_pmf_of_set_UNIV 
unfolding bind_spmf_of_pmf by (auto simp add: spmf_of_pmf_bind)

text \<open>The lifting of the encryption:\<close>

definition gpv_encrypt ::
    "('a qr, 'k) pk \<Rightarrow> plain \<Rightarrow> (('a qr, 'k) vec \<times> 'a qr, 'b, 'c) gpv" where
"gpv_encrypt pk m = lift_spmf (spmf_of_pmf (pmf_encrypt pk (plain_to_msg m)))"

text \<open>The lifting of the decryption:\<close>

definition gpv_decrypt :: 
  "('a qr, 'k) sk \<Rightarrow> ('a qr, 'k) cipher \<Rightarrow> (plain, ('a qr,'k) vec, bitstring) gpv" where
"gpv_decrypt sk cipher = lift_spmf (do {
    let msg' = decrypt (fst cipher) (snd cipher) sk du dv ;
    return_spmf (msg_to_plain (msg'))
  })"

text \<open>In order to verify that the plaintexts given by the adversary in the IND-CPA security game
have indeed the same length, we define the test \<open>valid_plains\<close>.\<close>

definition valid_plains :: "plain \<Rightarrow> plain \<Rightarrow> bool" where
"valid_plains msg1 msg2 \<longleftrightarrow> (length msg1 = len_plain \<and> length msg2 = len_plain)"

text \<open>Now we can instantiate the IND-CPA locale with the lifted Kyber algorithms.\<close>

sublocale ind_cpa: ind_cpa_pk "gpv_key_gen" "gpv_encrypt" "gpv_decrypt" valid_plains .


subsection \<open>Reduction Functions\<close>

text \<open>Since we lifted the key generation and encryption functions to \<open>gpv\<close>'s, we need to show 
that they are lossless, i.e., that they have no failure.\<close>

lemma lossless_key_gen[simp]: "lossless_gpv \<I>_full gpv_key_gen" 
unfolding gpv_key_gen_def by auto

lemma lossless_encrypt[simp]: "lossless_gpv \<I>_full (gpv_encrypt pk m)" 
unfolding gpv_encrypt_def by auto

lemma lossless_decrypt[simp]: "lossless_gpv \<I>_full (gpv_decrypt sk cipher)" 
unfolding gpv_decrypt_def by auto

lemma finite_UNIV_lossless_spmf_of_set:
assumes "finite (UNIV :: 'b set)"
shows "lossless_gpv \<I>_full (lift_spmf (spmf_of_set (UNIV :: 'b set)))"
using assms by simp

text \<open>The reduction functions give the concrete reduction of a IND-CPA adversary to a 
module-LWE adversary. 
The first function is for the reduction in the key generation using $m=k$, whereas the 
second reduction is used in the encryption with $m=k+1$ (using the option type).\<close>

fun kyber_reduction1 ::
"(('a qr, 'k) pk, plain, ('a qr, 'k) cipher, ('a qr,'k) vec, bitstring, 'state) ind_cpa.adversary
  \<Rightarrow> ('a qr, 'k,'k) mlwe.adversary"
where
  "kyber_reduction1 (\<A>\<^sub>1, \<A>\<^sub>2) A t = do {
    (((msg1, msg2), \<sigma>), s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial;
    try_spmf (do {
      _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
      b \<leftarrow> coin_spmf;
      (c, s1) \<leftarrow> exec_gpv ro.oracle (gpv_encrypt (A,t) (if b then msg1 else msg2)) s;
      (b', s2) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s1;
      return_spmf (b' = b)
    }) (coin_spmf)
  }"

fun kyber_reduction2 ::
"(('a qr, 'k) pk, plain, ('a qr, 'k) cipher, ('a qr,'k) vec, bitstring, 'state) ind_cpa.adversary
  \<Rightarrow> ('a qr, 'k,'k option) mlwe.adversary"
where
  "kyber_reduction2 (\<A>\<^sub>1, \<A>\<^sub>2) A' t' = do {
    let A = transpose (\<chi> i. A' $ (Some i));
    let t = A' $ None;
    (((msg1, msg2), \<sigma>),s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial;
    try_spmf (do {
      _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
      b \<leftarrow> coin_spmf;
      let msg = (if b then msg1 else msg2);
      let u = (\<chi> i. t' $ (Some i));
      let v = (t' $ None) + to_module (round((real_of_int q)/2)) * (plain_to_msg msg);
      (b', s1) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 (compress_vec du u, compress_poly dv v) \<sigma>) s;
      return_spmf (b'=b)
    }) (coin_spmf)
  }"

subsection \<open>IND-CPA Security Proof\<close>

text \<open>The following theorem states that if the adversary against the IND-CPA game is lossless
(that is it does not act maliciously), then the advantage in the IND-CPA game can be bounded by 
two advantages against the module-LWE game.
Under the module-LWE hardness assumption, the advantage against the module-LWE is negligible.

The proof proceeds in several steps, also called game-hops.
Initially, the IND-CPA game is considered. Then we gradually alter the games and show that
either the alteration has no effect on the resulting probabilities or we can bound the change 
by an advantage against the module-LWE.
In the end, the game is a simple coin toss, which we know has probability $0.5$ to guess the 
correct outcome.
Finally, we can estimate the advantage against IND-CPA using the game-hops found before,
and bounding it against the advantage against module-LWE.\<close>

theorem concrete_security_kyber:
assumes lossless: "ind_cpa.lossless \<A>"
shows "ind_cpa.advantage (ro.oracle, ro.initial) \<A> \<le> 
  mlwe.advantage (kyber_reduction1 \<A>) + mlwe.advantage' (kyber_reduction2 \<A>)"
proof -
  note [cong del] = if_weak_cong 
   and [split del] = if_split
   and [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD
         map_spmf_bind_spmf bind_spmf_const 
   and [if_distribs] = if_distrib[where f="\<lambda>x. try_spmf x _"] 
        if_distrib[where f="weight_spmf"] 
        if_distrib[where f="\<lambda>r. scale_spmf r _"]

text \<open>First of all, we can split the IND-CPA adversary \<open>\<A>\<close> into two parts, namely the adversary 
who returns two messages \<open>\<A>\<^sub>1\<close> and the adversary who returns a guess \<open>\<A>\<^sub>2\<close>.\<close>

  obtain \<A>\<^sub>1 \<A>\<^sub>2 where \<A> [simp]: "\<A> = (\<A>\<^sub>1, \<A>\<^sub>2)" by (cases "\<A>")
  from lossless have lossless1 [simp]: "\<And>pk. lossless_gpv \<I>_full (\<A>\<^sub>1 pk)"
    and lossless2 [simp]: "\<And>\<sigma> cipher. lossless_gpv \<I>_full (\<A>\<^sub>2 \<sigma> cipher)"
    by(auto simp add: ind_cpa.lossless_def)

text \<open>The initial game \<open>game\<^sub>0\<close> is an equivalent formulation of the IND-CPA game.\<close>

  define game\<^sub>0  where
  "game\<^sub>0 = do {
      A \<leftarrow> spmf_of_set (UNIV:: (('a qr, 'k) vec, 'k) vec set);
      s \<leftarrow> spmf_of_pmf mlwe.beta_vec;
      e \<leftarrow> spmf_of_pmf mlwe.beta_vec;
      let pk = (A, A *v s + e);
      b \<leftarrow> coin_spmf;
      (((msg1, msg2), \<sigma>),s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 pk) ro.initial;
    if valid_plains msg1 msg2
    then do {
      (c, s1) \<leftarrow> exec_gpv ro.oracle (gpv_encrypt pk (if b then msg1 else msg2)) s;
      (b', s2) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s1;
      return_spmf (b' = b)
      } 
    else  coin_spmf
    }"

  have ind_cpa_game_eq_game\<^sub>0: "run_gpv ro.oracle (ind_cpa.game \<A>) ro.initial = game\<^sub>0" 
  proof -
    have *: "bind_pmf pmf_key_gen (\<lambda>x. return_spmf (x, ro.initial)) \<bind>
      (\<lambda>x. f (fst (fst x)) (snd x)) =
    spmf_of_set UNIV \<bind> (\<lambda>A. bind_pmf mlwe.beta_vec (\<lambda>s. bind_pmf mlwe.beta_vec
    (\<lambda>e. f (A, A *v s + e) ro.initial)))" for f 
    unfolding pmf_key_gen_def spmf_pmf_of_set_UNIV bind_spmf_of_pmf key_gen_new_def Let_def
    by (simp add: bind_spmf_pmf_assoc bind_assoc_pmf bind_return_pmf)
    show ?thesis using *[of "(\<lambda>pk state. exec_gpv ro.oracle (\<A>\<^sub>1 pk) state \<bind>
          (\<lambda>xa. if valid_plains (fst (fst (fst xa))) (snd (fst (fst xa)))
                then coin_spmf \<bind> (\<lambda>xb. exec_gpv ro.oracle (gpv_encrypt pk
                     (if xb then fst (fst (fst xa)) else snd (fst (fst xa)))) (snd xa) \<bind>
                     (\<lambda>x. exec_gpv ro.oracle (\<A>\<^sub>2 (fst x) (snd (fst xa))) (snd x) \<bind>
                     (\<lambda>x. return_spmf (fst x = xb))))
                else coin_spmf))"]
    unfolding \<A> ind_cpa.game.simps unfolding game\<^sub>0_def gpv_key_gen_def 
    apply (simp add: split_def try_spmf_bind_spmf_lossless try_bind_assert_spmf key_gen_def Let_def
      bind_commute_spmf[of coin_spmf] if_distrib_bind_spmf2
      try_gpv_bind_lossless try_bind_assert_gpv lift_bind_spmf comp_def
      if_distrib_exec_gpv exec_gpv_bind_lift_spmf exec_gpv_bind if_distrib_map_spmf 
      del: bind_spmf_const) 
    apply simp
    done
  qed

text \<open>We define encapsulate the module-LWE instance for generating a public key $t$ in the 
key generation by the function \<open>is_pk\<close>. The game \<open>game\<^sub>1\<close> depends on a function that generates a 
public key. 
Indeed, \<open>game\<^sub>0\<close> corresponds to \<open>game\<^sub>1 is_pk\<close>.\<close>

  define is_pk :: "('a qr,'k) pk spmf" where "is_pk =  do { 
    A \<leftarrow> spmf_of_set (UNIV:: (('a qr, 'k) vec, 'k) vec set);
    s \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    e \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    return_spmf (A, A *v s + e)}"

  define game\<^sub>1 where
  "game\<^sub>1 f = do {
      pk \<leftarrow> f;
      b \<leftarrow> coin_spmf;
      (((msg1, msg2), \<sigma>), s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 pk) ro.initial;
    if valid_plains msg1 msg2
    then do {
      (c, s1) \<leftarrow> exec_gpv ro.oracle (gpv_encrypt pk (if b then msg1 else msg2)) s;
      (b', s2) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s1;
      return_spmf (b' = b)
      } 
    else  coin_spmf
    }" for f :: "('a qr,'k) pk spmf"
  
  have game\<^sub>0_eq_game\<^sub>1_is_pk: "game\<^sub>0 = game\<^sub>1 is_pk" 
  by (simp add: game\<^sub>1_def game\<^sub>0_def is_pk_def Let_def o_def split_def if_distrib_map_spmf 
    bind_spmf_pmf_assoc bind_assoc_pmf bind_return_pmf)

text \<open>In contrast to the generation of the public key as a module-LWE instance as in \<open>is_pk\<close>,
the function \<open>rand_pk\<close> generates a uniformly random public key.
We can now use this to do a reduction step to a module-LWE advantage.
\<open>game\<^sub>1 is_pk\<close> corresponds to a module-LWE game with module-LWE instance.
\<open>game\<^sub>1 rand_pk\<close> corresponds to a module-LWE game with random instance.
The difference of their probabilities can then be bounded by the module-LWE advantage in 
lemma \<open>reduction1\<close>.
The reduction function used in this case is \<open>kyber_reduction1\<close>.\<close>

  define rand_pk :: "('a qr,'k) pk spmf" where 
  "rand_pk =  bind_spmf (spmf_of_set UNIV) (\<lambda>A. spmf_of_set UNIV \<bind> (\<lambda>t. return_spmf (A, t)))"

  have red11: "game\<^sub>1 is_pk = mlwe.game (kyber_reduction1 \<A>)"
  proof -
    have "spmf_of_set UNIV \<bind> (\<lambda>y. spmf_of_pmf mlwe.beta_vec \<bind> (\<lambda>ya. spmf_of_pmf mlwe.beta_vec \<bind>
      (\<lambda>yb. exec_gpv ro.oracle (\<A>\<^sub>1 (y, y *v ya + yb)) ro.initial \<bind>
      (\<lambda>yc. if valid_plains (fst (fst (fst yc))) (snd (fst (fst yc)))
            then coin_spmf \<bind>
                 (\<lambda>b. exec_gpv ro.oracle (gpv_encrypt (y, y *v ya + yb)
                      (if b then fst (fst (fst yc)) else snd (fst (fst yc)))) (snd yc) \<bind>
                 (\<lambda>p. exec_gpv ro.oracle (\<A>\<^sub>2 (fst p) (snd (fst yc))) (snd p) \<bind>
                 (\<lambda>p. return_spmf (fst p = b))))
            else coin_spmf)))) =
    spmf_of_set UNIV \<bind>(\<lambda>A. spmf_of_pmf mlwe.beta_vec \<bind>(\<lambda>s. spmf_of_pmf mlwe.beta_vec \<bind>
    (\<lambda>e. exec_gpv ro.oracle (\<A>\<^sub>1 (A, A *v s + e)) ro.initial \<bind>
    (\<lambda>p. if valid_plains (fst (fst (fst p))) (snd (fst (fst p)))
         then coin_spmf \<bind>
              (\<lambda>x. TRY exec_gpv ro.oracle (gpv_encrypt (A, A *v s + e)
                   (if x then fst (fst (fst p)) else snd (fst (fst p)))) (snd p) \<bind>
              (\<lambda>pa. exec_gpv ro.oracle (\<A>\<^sub>2 (fst pa) (snd (fst p))) (snd pa) \<bind>
              (\<lambda>p. return_spmf (fst p = x))) ELSE coin_spmf)
         else coin_spmf))))" 
    apply (subst try_spmf_bind_spmf_lossless)
      subgoal by (subst lossless_exec_gpv, auto)
      subgoal apply (subst try_spmf_bind_spmf_lossless)
        subgoal by (subst lossless_exec_gpv, auto)
        subgoal by (auto simp add: bind_commute_spmf
        [of "spmf_of_set (UNIV :: ('a qr, 'k option) vec set)"])
      done
    done
    then show ?thesis unfolding  mlwe.game_def game\<^sub>1_def is_pk_def
    by (simp add: try_bind_assert_spmf bind_commute_spmf[of "coin_spmf"] split_def 
      if_distrib_bind_spmf2 try_spmf_bind_spmf_lossless 
      bind_spmf_pmf_assoc bind_assoc_pmf bind_return_pmf del: bind_spmf_const) simp
  qed

  have red12: "game\<^sub>1 rand_pk = mlwe.game_random (kyber_reduction1 \<A>)"
  proof -
    have "spmf_of_set UNIV \<bind> (\<lambda>y. spmf_of_set UNIV \<bind>
      (\<lambda>ya. exec_gpv ro.oracle (\<A>\<^sub>1 (y, ya)) ro.initial \<bind>
      (\<lambda>yb. if valid_plains (fst (fst (fst yb))) (snd (fst (fst yb)))
            then coin_spmf \<bind>
                 (\<lambda>b. exec_gpv ro.oracle (gpv_encrypt (y, ya)
                      (if b then fst (fst (fst yb)) else snd (fst (fst yb)))) (snd yb) \<bind>
                 (\<lambda>p. exec_gpv ro.oracle (\<A>\<^sub>2 (fst p) (snd (fst yb))) (snd p) \<bind>
                 (\<lambda>p. return_spmf (fst p = b))))
            else coin_spmf))) =
    spmf_of_set UNIV \<bind> (\<lambda>A. spmf_of_set UNIV \<bind>
      (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>1 (A, b)) ro.initial \<bind>
      (\<lambda>p. if valid_plains (fst (fst (fst p))) (snd (fst (fst p)))
           then coin_spmf \<bind>
                (\<lambda>x. TRY exec_gpv ro.oracle (gpv_encrypt (A, b)
                         (if x then fst (fst (fst p)) else snd (fst (fst p)))) (snd p) \<bind>
                (\<lambda>pa. exec_gpv ro.oracle (\<A>\<^sub>2 (fst pa) (snd (fst p))) (snd pa) \<bind>
                (\<lambda>p. return_spmf (fst p = x))) ELSE coin_spmf)
           else coin_spmf)))" 
    apply (subst try_spmf_bind_spmf_lossless)
      subgoal by (subst lossless_exec_gpv, auto)
      subgoal apply (subst try_spmf_bind_spmf_lossless)
        subgoal by (subst lossless_exec_gpv, auto)
        subgoal by (auto simp add: bind_commute_spmf
        [of "spmf_of_set (UNIV :: ('a qr, 'k option) vec set)"])
      done
    done
    then show ?thesis unfolding  mlwe.game_random_def game\<^sub>1_def rand_pk_def
    by (simp add: try_bind_assert_spmf bind_commute_spmf[of "coin_spmf"] split_def 
      if_distrib_bind_spmf2 try_spmf_bind_spmf_lossless 
      bind_spmf_pmf_assoc bind_assoc_pmf bind_return_pmf
      del: bind_spmf_const) simp
  qed

  have reduction1: "\<bar>spmf (game\<^sub>1 is_pk) True - spmf (game\<^sub>1 rand_pk) True\<bar> \<le> 
    mlwe.advantage (kyber_reduction1 \<A>)"
  unfolding mlwe.advantage_def red11 red12 by auto

text \<open>Again, we rewrite our current game such that:
\begin{itemize}
\item the generation of the public key is outsourced to a sampling function \<open>?sample\<close>
\item the encryption is outsourced to a input function
\item \<open>is_encrypt\<close> is the appropriate input function for the encryption
\item \<open>rand_encrypt\<close> is the appropriate input function for a uniformly random $u$ and $v'$ 
\end{itemize}
Note that the addition of the message is not changed yet.\<close>

  define is_encrypt where
  "is_encrypt A t msg = do {
    r \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    e1 \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    e2 \<leftarrow> spmf_of_pmf mlwe.beta;
    let (u,v) = ((((transpose A) *v r + e1), (scalar_product t r + e2 + 
      to_module (round((real_of_int q)/2)) * (plain_to_msg msg))));
    return_spmf (compress_vec du u, compress_poly dv v)
  }" for A ::"(('a qr,'k) vec,'k)vec" and t :: "('a qr,'k) vec" and msg :: bitstring

  define rand_encrypt where
  "rand_encrypt A t msg = do {
    u \<leftarrow> spmf_of_set (UNIV :: ('a qr,'k) vec set);
    v \<leftarrow> spmf_of_set (UNIV :: 'a qr set);
    let v' = v + to_module (round((real_of_int q)/2)) * (plain_to_msg msg);
    return_spmf (compress_vec du u, compress_poly dv v')
  }" for A ::"(('a qr,'k) vec,'k)vec" and t :: "('a qr,'k) vec" and msg :: bitstring

  let ?sample = "\<lambda>f. bind_spmf (spmf_of_set (UNIV:: (('a qr, 'k) vec, 'k) vec set))
      (\<lambda>A. bind_spmf (spmf_of_set (UNIV:: ('a qr, 'k) vec set)) (f A))"

  define game\<^sub>2 where
  "game\<^sub>2 f A t = bind_spmf coin_spmf
    (\<lambda>b. bind_spmf (exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial)
           (\<lambda>(((msg1, msg2), \<sigma>), s).
               if valid_plains msg1 msg2
               then let msg = if b then msg1 else msg2
                    in bind_spmf (f A t msg)
                       (\<lambda>c. bind_spmf (exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s)
                              (\<lambda>(b', s1). return_spmf (b' = b)))
               else coin_spmf))" 
    for f and A :: "(('a qr, 'k) vec, 'k) vec" and t :: "('a qr, 'k) vec"

text \<open>Then \<open>game\<^sub>1 rand_encrypt\<close> is the same as sampling via \<open>?sample\<close> and \<open>game\<^sub>2 is_encrypt\<close>.\<close>

  have game\<^sub>1_rand_pk_eq_game\<^sub>2_is_encrypt: "game\<^sub>1 rand_pk = ?sample (game\<^sub>2 is_encrypt)" 
  unfolding game\<^sub>1_def rand_pk_def game\<^sub>2_def is_encrypt_def
  by (simp add: game\<^sub>1_def game\<^sub>2_def rand_pk_def is_encrypt_def gpv_encrypt_def 
    encrypt_new_def pmf_encrypt_def Let_def o_def split_def if_distrib_map_spmf 
    bind_spmf_pmf_assoc bind_assoc_pmf bind_return_pmf)

text \<open>To make the reduction work, we need to rewrite \<open>is_encrypt\<close> and \<open>rand_encrypt\<close> such that 
$u$ and $v$ are in one vector only (since both need to be multiplied with $r$, thus we cannot 
split the module-LWE instances). This can be done using the option type to allow for one more 
index in the vector over the option type.\<close>

  define is_encrypt1 where
  "is_encrypt1 A t msg = do {
    r \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    e1 \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    e2 \<leftarrow> spmf_of_pmf mlwe.beta;
    let (e :: ('a qr, 'k option) vec) = (\<chi> i. if i= None then e2 else e1 $ (the i));
    let (A' :: (('a qr,'k) vec, 'k option) vec) = 
      (\<chi> i. if i = None then t else (transpose A) $ (the i));
    let c = A' *v r + e;
    let (u :: ('a qr, 'k) vec) = (\<chi> i. (c $ (Some i)));
    let (v :: 'a qr) = (c $ None +
      to_module (round((real_of_int q)/2)) * (plain_to_msg msg));
    return_spmf (compress_vec du u, compress_poly dv v)
  }" for A :: "(('a qr, 'k) vec, 'k) vec" and t :: "('a qr,'k) vec" and msg :: bitstring

  define rand_encrypt1 where
  "rand_encrypt1 A t msg = do {
    u' \<leftarrow> spmf_of_set (UNIV :: ('a qr,'k) vec set);
    v' \<leftarrow> spmf_of_set (UNIV :: 'a qr set);
    let (v :: 'a qr) = (v' +
      to_module (round((real_of_int q)/2)) * (plain_to_msg msg));
    return_spmf (compress_vec du u', compress_poly dv v)
  }" for A ::"(('a qr,'k) vec,'k)vec" and t :: "('a qr,'k) vec" and msg :: bitstring

text \<open>Indeed, these functions are the same as the previously defined \<open>is_encrypt\<close> and 
\<open>rand_encrypt\<close>.\<close>

  have is_encrypt1: "is_encrypt A t msg = is_encrypt1 A t msg" for A t msg
  unfolding is_encrypt_def is_encrypt1_def Let_def
  by (simp add: split_def plus_vec_def matrix_vector_mult_def scalar_product_def)

  have rand_encrypt1: "rand_encrypt A t msg = rand_encrypt1 A t msg" for A t msg 
    unfolding rand_encrypt_def rand_encrypt1_def Let_def by simp
 
text \<open>We also need to rewrite \<open>game\<^sub>2\<close> to work over the option type, i.e., that $A$ and $t$ are
put in one matix $A'$. Then, \<open>is_encrypt'\<close> is an adaption to \<open>is_encrypt\<close> working with $A'$
instead of $a$ and $t$ separately.\<close>

  define game\<^sub>3 where
  "game\<^sub>3 f = do {
    b \<leftarrow> coin_spmf;
    A' \<leftarrow> spmf_of_set (UNIV :: (('a qr,'k) vec, 'k option) vec set);
    let A = transpose (vec_lambda (\<lambda> i. vec_nth A' (Some i)));
    let t = vec_nth A' None;
    (((msg1, msg2), \<sigma>),s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 (A,t)) ro.initial;
    if valid_plains msg1 msg2
    then do {
      let msg = (if b then msg1 else msg2);
      c \<leftarrow> f A';
      let (u :: ('a qr, 'k) vec) = vec_lambda (\<lambda> i. (vec_nth c (Some i)));
      let (v :: 'a qr) = (vec_nth c None +
      to_module (round((real_of_int q)/2)) * (plain_to_msg msg));
      (b', s1) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 (compress_vec du u, compress_poly dv v) \<sigma>) s;
      return_spmf (b' = b)
    } 
  else  coin_spmf
  }" for f


  define is_encrypt' where
  "is_encrypt' A' = bind_spmf (spmf_of_pmf mlwe.beta_vec)
    (\<lambda>r. bind_spmf (mlwe.beta_vec')
    (\<lambda>e. return_spmf (A' *v r + e)))" for A' ::"(('a qr,'k) vec,'k option) vec"


text \<open>We can write the distribution of the error and the public key as one draw from a
probability distribution over the option type.
We need this in order to show \<open>?sample (game\<^sub>2 is_encrypt) = game\<^sub>3 (is_encrypt')\<close>.
This corresponds to the module-LWE instance in the module-LWE advantage.\<close>

  have e_distrib: "do {
    e1 \<leftarrow> spmf_of_pmf mlwe.beta_vec;
    e2 \<leftarrow> spmf_of_pmf mlwe.beta;
    let (e' :: ('a qr, 'k option) vec) = 
      (\<chi> i. if i = None then e2 else vec_nth e1 (the i)); 
    return_spmf e'
  } = mlwe.beta_vec'" 
  unfolding mlwe.beta_vec' mlwe.beta_vec_def replicate_spmf_def
  by (simp add: bind_commute_pmf[of "mlwe.beta"] bind_assoc_pmf bind_pmf_return_spmf 
    bind_return_pmf)


  have pk_distrib: "do {
    A \<leftarrow> spmf_of_set (UNIV);
    t \<leftarrow> spmf_of_set (UNIV);
    let (A' :: (('a qr,'k) vec, 'k option) vec) = 
      (\<chi> i. if i = None then t else transpose A $ (the i));
    return_spmf A'} = 
    spmf_of_set (UNIV)"
  proof (intro spmf_eqI, goal_cases)
    case (1 A')
    let ?P = "(\<lambda> (A,t). (\<chi> i. if i = None then t else transpose A $ (the i)))
      :: ((('a qr, 'k) vec, 'k) vec \<times> ('a qr, 'k) vec) \<Rightarrow> (('a qr, 'k) vec, 'k option) vec"
    define a where "a = transpose (\<chi> i. vec_nth A' (Some i))"
    define b where "b = A' $ None"
    have "(\<chi> i. if i = None then b else transpose a $ the i) = A'" 
      unfolding a_def b_def 
      by (smt (verit, ccfv_SIG) Cart_lambda_cong Option.option.collapse 
        transpose_transpose vec_lambda_eta vector_component_simps(5))
    moreover have "aa = a \<and> bb = b" if "(\<chi> i. if i = None then bb else transpose aa $ the i) = A'" 
      for aa bb using a_def b_def that by force
    ultimately have "\<exists>! (A, t). ?P(A,t) = A'"
      unfolding Ex1_def by (auto simp add: split_def)
    then have "(\<Sum>x \<in> UNIV. indicat_real {Some A'} (Some (?P (fst x, snd x)))) = 1"
      by (subst indicator_def, subst ex1_sum, simp_all add: split_def finite_Prod_UNIV)
    then have "(\<Sum>A\<in>UNIV. \<Sum>t\<in>UNIV. indicat_real {Some A'} 
      (Some (?P (A,t)))) = 1" 
    by (subst sum_cartesian_product'[symmetric]) (simp add: split_def )
    then show ?case by (simp add: spmf_bind spmf_of_set integral_spmf_of_set)
  qed

  have game\<^sub>2_eq_game\<^sub>3_is_encrypt: 
    "?sample (game\<^sub>2 is_encrypt) = game\<^sub>3 (is_encrypt')"
  proof -
    have "?sample (game\<^sub>2 is_encrypt) = 
      (spmf_of_set UNIV \<bind>
      (\<lambda>A. spmf_of_set UNIV \<bind>
      (\<lambda>t. let  A' = \<chi> i. if i = None then t else transpose A $ the i in
        return_spmf A'))) \<bind> 
       (\<lambda>A'. let A = transpose (\<chi> i. vec_nth A' (Some i));
                t = A' $ None
        in coin_spmf \<bind>
      (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
      (\<lambda>(((msg1, msg2), \<sigma>), s). if valid_plains msg1 msg2
          then let msg = if b then msg1 else msg2
               in spmf_of_pmf mlwe.beta_vec \<bind>
                  (\<lambda>r. spmf_of_pmf mlwe.beta_vec \<bind>
                  (\<lambda>e1. spmf_of_pmf mlwe.beta \<bind>
                  (\<lambda>e2. let e = \<chi> i. if i = None then e2 else e1 $ the i;
                            c = A' *v r + e; u = compress_vec du (\<chi> i. c $ Some i);
                            v = compress_poly dv (c $ None + to_module 
                                (round (real_of_int q / 2)) * plain_to_msg msg)
                         in return_spmf (u, v)))) \<bind>
                            (\<lambda>c. exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s \<bind> 
                            (\<lambda>(b', s1). return_spmf (b' = b)))
          else coin_spmf)))"
    unfolding is_encrypt1 unfolding game\<^sub>2_def is_encrypt1_def Let_def by simp
    also have " \<dots> = spmf_of_set UNIV \<bind>
      (\<lambda>A'. let A = transpose (\<chi> i. vec_nth A' (Some i));
                t = A' $ None
        in coin_spmf \<bind>
      (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
      (\<lambda>(((msg1, msg2), \<sigma>), s). if valid_plains msg1 msg2
          then let msg = if b then msg1 else msg2
               in spmf_of_pmf mlwe.beta_vec \<bind>
                  (\<lambda>r. 
            (spmf_of_pmf mlwe.beta_vec \<bind>
            (\<lambda>e1. spmf_of_pmf mlwe.beta \<bind>
            (\<lambda>e2. let e = \<chi> i. if i = None then e2 else e1 $ the i 
            in return_spmf e))) \<bind>
                  (\<lambda>e. let c = A' *v r + e; u = compress_vec du (\<chi> i. c $ Some i);
                           v = compress_poly dv (c $ None + to_module 
                                (round (real_of_int q / 2)) * plain_to_msg msg)
                         in return_spmf (u, v))) \<bind>
                            (\<lambda>c. exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s \<bind> 
                            (\<lambda>(b', s1). return_spmf (b' = b)))
          else coin_spmf)))"
      by (subst pk_distrib) (simp add: Let_def del: bind_spmf_of_pmf)
    also have " \<dots> = spmf_of_set UNIV \<bind>
      (\<lambda>A'. let A = transpose (\<chi> i. vec_nth A' (Some i));
                t = A' $ None
        in coin_spmf \<bind>
      (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
      (\<lambda>(((msg1, msg2), \<sigma>),s). if valid_plains msg1 msg2
          then let msg = if b then msg1 else msg2
               in spmf_of_pmf mlwe.beta_vec \<bind>
                  (\<lambda>r. mlwe.beta_vec' \<bind>
                  (\<lambda>e. let c = A' *v r + e; u = compress_vec du (\<chi> i. c $ Some i);
                           v = compress_poly dv (c $ None + to_module 
                                (round (real_of_int q / 2)) * plain_to_msg msg)
                         in return_spmf (u, v))) \<bind>
                            (\<lambda>c. exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s \<bind> 
                            (\<lambda>(b', s1). return_spmf (b' = b)))
          else coin_spmf)))"
      unfolding e_distrib by simp
    also have "\<dots> = game\<^sub>3 is_encrypt'"
      unfolding game\<^sub>3_def is_encrypt'_def 
      by (simp add: bind_commute_spmf[of "coin_spmf"]  bind_spmf_pmf_assoc)
    finally show ?thesis
      by blast
  qed

text \<open>We can write the distribution of the cipher test as one draw from a
probability distribution over the option type as well.
Using this, we can show \<open>?sample (game\<^sub>2 rand_encrypt) = game\<^sub>3 (\<lambda>_. spmf_of_set UNIV)\<close>.
This corresponds to the uniformly random instance in the module-LWE advantage.\<close>

  have cipher_distrib:
    "do{
      u \<leftarrow> spmf_of_set (UNIV:: ('a qr, 'k) vec set);
      v \<leftarrow> spmf_of_set (UNIV:: 'a qr set);
      return_spmf (u, v)
    } = do{
      c \<leftarrow> spmf_of_set (UNIV:: ('a qr, 'k option) vec set);
      let u = \<chi> i. c $ Some i;
          v = c $ None in
      return_spmf (u,v)
    }" for msg :: bitstring
  proof (intro spmf_eqI, unfold Let_def, goal_cases)
    case (1 w)
    have "(\<Sum>x\<in>UNIV. \<Sum>xa\<in>UNIV. indicat_real {Some w} (Some (x, xa))) = 1" 
    proof -
      have "(\<Sum>x\<in>UNIV. \<Sum>xa\<in>UNIV. indicat_real {Some w} (Some (x, xa))) = 
            (\<Sum>x\<in>UNIV. indicat_real {Some w} (Some x))"
      by (subst sum_cartesian_product'[symmetric]) simp
      also have "\<dots> = 1" unfolding indicator_def 
        using finite_cartesian_product[OF finite_UNIV_vec finite_qr]
        by (subst ex1_sum) simp_all
      finally show ?thesis by blast
    qed
    moreover have "(\<Sum>x\<in>UNIV. indicat_real {Some w} (Some (\<chi> i. x $ Some i, x $ None))) = 1" 
    proof (unfold indicator_def, subst ex1_sum, goal_cases)
      case 1
      define x where "x = (\<chi> i. if i = None then snd w else fst w $ (the i))"
      have "Some (\<chi> i. x $ Some i, x $ None) \<in> {Some w}" by (simp add: x_def)
      moreover have "(\<forall>y. Some (\<chi> i. y $ Some i, y $ None) \<in> {Some w} \<longrightarrow> y = x)"
      by (metis (mono_tags) Option.option.exhaust Option.option.sel Product_Type.prod.sel(1) 
        Product_Type.prod.sel(2) calculation singletonD vec_lambda_unique)
      ultimately show ?case unfolding Ex1_def by (intro exI) simp
    qed  simp_all
    ultimately show ?case 
      by (simp add: spmf_bind integral_spmf_of_set)
  qed

  have game\<^sub>2_eq_game\<^sub>3_rand_encrypt: 
    "?sample (game\<^sub>2 rand_encrypt) = game\<^sub>3 (\<lambda>_. spmf_of_set UNIV)"
  proof -
    have "?sample (game\<^sub>2 rand_encrypt) = 
      (spmf_of_set UNIV \<bind>
      (\<lambda>A. spmf_of_set UNIV \<bind>
      (\<lambda>t. let  A' = \<chi> i. if i = None then t else transpose A $ the i in
        return_spmf A'))) \<bind> 
       (\<lambda>A'. let A = transpose (\<chi> i. vec_nth A' (Some i));
                t = A' $ None
        in coin_spmf \<bind>
      (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
      (\<lambda>(((msg1, msg2), \<sigma>),s). if valid_plains msg1 msg2
          then let msg = if b then msg1 else msg2
               in rand_encrypt1 A t msg \<bind>
                            (\<lambda>c. exec_gpv ro.oracle (\<A>\<^sub>2 c \<sigma>) s \<bind> 
                            (\<lambda>(b', s1). return_spmf (b' = b)))
          else coin_spmf)))"
    unfolding rand_encrypt1 unfolding game\<^sub>2_def Let_def by simp
    also have " \<dots> = spmf_of_set UNIV \<bind>
      (\<lambda>A'. let A = transpose (\<chi> i. A' $ (Some i));
                t = A' $ None
        in coin_spmf \<bind>
      (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
      (\<lambda>(((msg1, msg2), \<sigma>),s). if valid_plains msg1 msg2
          then let msg = if b then msg1 else msg2
               in do{ u \<leftarrow> spmf_of_set (UNIV:: ('a qr, 'k) vec set);
                      v \<leftarrow> spmf_of_set (UNIV:: 'a qr set);
                      return_spmf (u, v)} \<bind>
                  (\<lambda>(u,v). let v' = (v + to_module (round((real_of_int q)/2)) * 
                                    (plain_to_msg msg))
                        in exec_gpv ro.oracle (\<A>\<^sub>2 (compress_vec du u, 
                             compress_poly dv v') \<sigma>) s \<bind> 
                          (\<lambda>(b',s1). return_spmf (b' = b)))
          else coin_spmf)))"
      unfolding rand_encrypt1_def by (subst pk_distrib)(simp add: Let_def del: bind_spmf_of_pmf)
    also have " \<dots> = spmf_of_set UNIV \<bind>
      (\<lambda>A'. let A = transpose (\<chi> i. vec_nth A' (Some i));
                t = A' $ None
        in coin_spmf \<bind>
      (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
      (\<lambda>(((msg1, msg2), \<sigma>),s). if valid_plains msg1 msg2
          then let msg = if b then msg1 else msg2
               in do{ c \<leftarrow> spmf_of_set (UNIV:: ('a qr, 'k option) vec set);
                      let u = \<chi> i. c $ Some i; v = c $ None in
                      return_spmf (u,v) } \<bind>
                  (\<lambda>(u,v). let v' = (v + to_module (round((real_of_int q)/2)) * 
                                    (plain_to_msg msg))
                        in exec_gpv ro.oracle (\<A>\<^sub>2 (compress_vec du u, 
                            compress_poly dv v') \<sigma>) s \<bind> 
                          (\<lambda>(b',s1). return_spmf (b' = b)))
          else coin_spmf)))"
      unfolding cipher_distrib by simp
    also have "\<dots> = game\<^sub>3 (\<lambda>_. spmf_of_set UNIV)"
      unfolding game\<^sub>3_def by (simp add: bind_commute_spmf[of "coin_spmf"])
    finally show ?thesis
      by blast
  qed

text \<open>Now, we establish the correspondence between the games in the module-LWE advantage and 
\<open>game\<^sub>3\<close>. Here, the rewriting needed to be done manually for some parts, as the automation could not 
handle it (commutativity only between certain \<open>pmf\<close>s).\<close>

  have game\<^sub>3_eq_mlwe_game': "game\<^sub>3 is_encrypt' = mlwe.game' (kyber_reduction2 \<A>)" 
  proof -
    have "mlwe.game' (kyber_reduction2 \<A>) = 
      spmf_of_set UNIV \<bind> (\<lambda>A. spmf_of_pmf mlwe.beta_vec \<bind>
      (\<lambda>s. exec_gpv ro.oracle (\<A>\<^sub>1 (transpose (\<chi> i. A $ Some i), A $ None)) ro.initial \<bind>
      (\<lambda>y. if valid_plains (fst (fst (fst y))) (snd (fst (fst y)))
           then coin_spmf \<bind>
                 (\<lambda>ya. mlwe.beta_vec' \<bind>
                 (\<lambda>e. TRY exec_gpv ro.oracle (\<A>\<^sub>2 (
                      compress_vec du (\<chi> i. (A *v s) $ Some i + e $ Some i),
                      compress_poly dv ((A *v s) $ None + e $ None + 
                      to_module (round (real_of_int q / 2)) *
                      plain_to_msg (if ya then fst (fst (fst y)) else snd (fst (fst y)))))
                      (snd (fst y))) (snd y) \<bind>
                      (\<lambda>p. return_spmf (fst p = ya)) ELSE coin_spmf))
           else coin_spmf)))"
    unfolding  mlwe.game'_def 
    by (simp add: try_bind_assert_spmf split_def bind_commute_spmf[of "mlwe.beta_vec'"]
      if_distrib_bind_spmf2 try_spmf_bind_spmf_lossless del: bind_spmf_const) simp
    also have "\<dots> =
    spmf_of_set (UNIV :: (('a qr,'k) vec, 'k option) vec set) \<bind>
    (\<lambda>A. spmf_of_pmf mlwe.beta_vec \<bind>
    (\<lambda>s. exec_gpv ro.oracle (\<A>\<^sub>1 (transpose (\<chi> i. A $ Some i), A $ None)) ro.initial \<bind>
    (\<lambda>y. if valid_plains (fst (fst (fst y))) (snd (fst (fst y)))
         then mlwe.beta_vec' \<bind>
              (\<lambda>e. coin_spmf \<bind>
              (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>2 (
                   compress_vec du (\<chi> i. (A *v s) $ Some i + e $ Some i),
                   compress_poly dv ((A *v s) $ None + e $ None +
                   to_module (round (real_of_int q / 2)) *
                   plain_to_msg (if b then fst (fst (fst y)) else snd (fst (fst y)))))
                   (snd (fst y))) (snd y) \<bind>
              (\<lambda>p. return_spmf (fst p = b))))
         else  coin_spmf)))"
    apply (subst try_spmf_bind_spmf_lossless) 
      subgoal by (subst lossless_exec_gpv, auto)
      subgoal by (auto simp add: bind_commute_spmf[of "mlwe.beta_vec'"])
    done
    also have "\<dots> = 
    spmf_of_set (UNIV :: (('a qr,'k) vec, 'k option) vec set) \<bind>
    (\<lambda>A. exec_gpv ro.oracle (\<A>\<^sub>1 (transpose (\<chi> i. A $ Some i), A $ None)) ro.initial \<bind>
    (\<lambda>p. if valid_plains (fst (fst (fst p))) (snd (fst (fst p)))
         then spmf_of_pmf mlwe.beta_vec \<bind>
              (\<lambda>s. mlwe.beta_vec' \<bind>
              (\<lambda>e. coin_spmf \<bind>
              (\<lambda>b. exec_gpv ro.oracle (\<A>\<^sub>2  (
                       compress_vec du (\<chi> i. (A *v s) $ Some i + e $ Some i),
                       compress_poly dv ((A *v s) $ None + e $ None +
                        to_module (round (real_of_int q / 2)) *
                        plain_to_msg (if b then fst (fst (fst p)) else snd (fst (fst p)))))
                      (snd (fst p))) (snd p) \<bind>
              (\<lambda>b'. return_spmf (fst b' = b)))))
          else coin_spmf))" 
    apply (subst bind_commute_spmf[of "spmf_of_pmf mlwe.beta_vec"])+
    apply (subst if_distrib_bind_spmf2)
    apply (subst bind_commute_spmf[of "spmf_of_pmf mlwe.beta_vec"])+
    by (simp add: split_def del: bind_spmf_const)
    also have "\<dots> = game\<^sub>3 is_encrypt'"
    unfolding game\<^sub>3_def is_encrypt'_def Let_def split_def
    apply (subst bind_commute_spmf[of "coin_spmf"])+
    apply (subst if_distrib_bind_spmf2)
    apply (subst bind_commute_spmf[of "coin_spmf"])+
    apply (simp add: try_bind_assert_spmf split_def bind_commute_spmf[of "coin_spmf"] 
      if_distrib_bind_spmf2 bind_spmf_pmf_assoc del: bind_spmf_const) 
    by simp
    ultimately show ?thesis by force
  qed

  have game\<^sub>3_eq_mlwe_game_random': 
    "game\<^sub>3 (\<lambda>_. spmf_of_set UNIV) = mlwe.game_random' (kyber_reduction2 \<A>)"
  proof -
    have *: "mlwe.game_random' (kyber_reduction2 \<A>) = 
    spmf_of_set UNIV \<bind>
    (\<lambda>A. exec_gpv ro.oracle (\<A>\<^sub>1 (transpose (\<chi> i. A $ Some i), A $ None)) ro.initial \<bind>
    (\<lambda>y. if valid_plains (fst (fst (fst y))) (snd (fst (fst y)))
         then spmf_of_set UNIV \<bind>
              (\<lambda>b. TRY coin_spmf \<bind>
              (\<lambda>ba. exec_gpv ro.oracle (\<A>\<^sub>2 (compress_vec du (\<chi> i. b $ Some i), 
                 compress_poly dv (b $ None +
                 to_module (round (real_of_int q / 2)) * plain_to_msg
                 (if ba then fst (fst (fst y)) else snd (fst (fst y))))) (snd (fst y))) (snd y) \<bind>
              (\<lambda>p. return_spmf (fst p = ba))) ELSE coin_spmf)
         else  coin_spmf))"
    unfolding  mlwe.game_random'_def 
    using bind_commute_spmf[of "spmf_of_set (UNIV :: ('a qr, 'k option) vec set)"] 
    by (simp add: try_bind_assert_spmf split_def 
      bind_commute_spmf[of "spmf_of_set (UNIV :: ('a qr, 'k option) vec set)"]
      if_distrib_bind_spmf2 del: bind_spmf_const) simp
    also have "\<dots> =
    spmf_of_set UNIV \<bind>
    (\<lambda>A. exec_gpv ro.oracle  (\<A>\<^sub>1 (transpose (\<chi> i. A $ Some i), A $ None)) ro.initial \<bind>
    (\<lambda>p. if valid_plains (fst (fst (fst p))) (snd (fst (fst p)))
         then coin_spmf \<bind>
              (\<lambda>ba. spmf_of_set UNIV \<bind>
              (\<lambda>b. exec_gpv ro.oracle  (\<A>\<^sub>2 (compress_vec du (\<chi> i. b $ Some i),
                        compress_poly dv (b $ None + to_module 
                        (round (real_of_int q / 2)) * plain_to_msg (if ba then fst (fst (fst p)) 
                        else snd (fst (fst p))))) (snd (fst p))) (snd p) \<bind>
              (\<lambda>b'. return_spmf (fst b' = ba))))
         else coin_spmf))" 
    apply (subst try_spmf_bind_spmf_lossless, simp) 
    apply (subst try_spmf_bind_spmf_lossless)
      subgoal by (subst lossless_exec_gpv, auto)
      subgoal by (auto simp add: bind_commute_spmf
        [of "spmf_of_set (UNIV :: ('a qr, 'k option) vec set)"])
    done
    then show ?thesis unfolding game\<^sub>3_def *
    by (simp add: try_bind_assert_spmf split_def bind_commute_spmf[of "coin_spmf"] 
      if_distrib_bind_spmf2 del: bind_spmf_const) simp
  qed

text \<open>This finishes the second reduction step. In this case, the reduction function was 
\<open>kyber_reduction2\<close>.\<close>

  have reduction2: "\<bar>spmf (game\<^sub>3 is_encrypt') True - spmf (game\<^sub>3 (\<lambda>_. spmf_of_set UNIV)) True\<bar> \<le> 
    mlwe.advantage' (kyber_reduction2 \<A>)"
  unfolding game\<^sub>3_eq_mlwe_game' game\<^sub>3_eq_mlwe_game_random' mlwe.advantage'_def 
  by simp

text \<open>Now that $u$ and $v$ are generated uniformly at random, we need to show that adding the 
message will again result in a uniformly random variable. The reason is that we work over the
finite space $R_q$.
\<open>game\<^sub>4\<close> is the game where the message is no longer added, but the ciphertext is uniformly at 
random.\<close>

  define game\<^sub>4 where
  "game\<^sub>4 = do {
    b \<leftarrow> coin_spmf;
    A' \<leftarrow> spmf_of_set (UNIV :: (('a qr,'k) vec, 'k option) vec set);
    let A = transpose (\<chi> i. vec_nth A' (Some i));
    let t = A' $ None;
    (((msg1, msg2), \<sigma>), s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 (A,t)) ro.initial;
    if valid_plains msg1 msg2
    then do {
      let msg = (if b then msg1 else msg2);
      c \<leftarrow> spmf_of_set UNIV;
      let u = (\<chi> i. c $ Some i); 
      let v = c $ None;
      (b', s1) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 (compress_vec du u, compress_poly dv v) \<sigma>) s;
      return_spmf (b' = b)
    } 
  else  coin_spmf
  }"

text \<open>Adding the message does not change the uniform distribution.
This is needed to show that \<open>game\<^sub>3 (\<lambda>_. spmf_of_set UNIV) = game\<^sub>4\<close>.\<close>

  have indep_of_msg:
    "do {c \<leftarrow> spmf_of_set UNIV;
         let u = \<chi> i. c $ Some i;
             v = c $ None + to_module (round (real_of_int q / 2)) * plain_to_msg msg
          in return_spmf (u, v)} = 
    do {c \<leftarrow> spmf_of_set UNIV;
        let u = \<chi> i. c $ Some i; v = c $ None
         in return_spmf (u, v)}" for msg::bitstring
  proof (intro spmf_eqI, goal_cases)
    case (1 y)
    define msg' where "msg' = to_module (round (real_of_int q / 2)) * plain_to_msg msg" 
    have "(\<Sum>x\<in>UNIV. of_bool ((\<chi> i. x $ Some i, x $ None + msg') = y)) = 1" 
    proof (intro ex1_sum, goal_cases)
      case 1
      define x where "x = (\<chi> i. if i = None then snd y - msg' else (fst y) $ (the i))"
      have "(\<chi> i. x $ Some i, x $ None + msg') = y" unfolding x_def by simp
      moreover have "(\<forall>ya. (\<chi> i. ya $ Some i, ya $ None + msg') = y \<longrightarrow> ya = x)" 
        unfolding x_def
        by (metis (mono_tags, lifting) Groups.group_add_class.add.right_cancel 
          Option.option.exhaust calculation fst_conv snd_conv vec_lambda_unique x_def)
      ultimately show ?case unfolding Ex1_def by (intro exI) simp
    qed (simp add: finite_vec)
    moreover have "\<dots> = (\<Sum>x\<in>UNIV. of_bool ((\<chi> i. x $ Some i, x $ None) = y))"
    proof (subst ex1_sum, goal_cases)
      case 1
      define x where "x = (\<chi> i. if i = None then snd y else (fst y) $ (the i))"
      have "(\<chi> i. x $ Some i, x $ None) = y" unfolding x_def by simp
      moreover have "(\<forall>ya. (\<chi> i. ya $ Some i, ya $ None) = y \<longrightarrow> ya = x)" 
        unfolding x_def
        by (metis (mono_tags, lifting)
          Option.option.exhaust calculation fst_conv snd_conv vec_lambda_unique x_def)
      ultimately show ?case unfolding Ex1_def by (intro exI) simp
    qed (simp_all add: finite_vec)
    ultimately have "(\<Sum>x\<in>UNIV. of_bool ((\<chi> i. x $ Some i, x $ None + msg') = y)) =
    (\<Sum>x\<in>UNIV. of_bool ((\<chi> i. x $ Some i, x $ None) = y))"
      by (smt (verit))
    then show ?case unfolding msg'_def[symmetric] 
      by (simp add: spmf_bind integral_spmf_of_set indicator_def del: sum_of_bool_eq)
  qed

  have game\<^sub>3_eq_game\<^sub>4: "game\<^sub>3 (\<lambda>_. spmf_of_set UNIV) = game\<^sub>4" 
  proof -
    have "game\<^sub>3 (\<lambda>_. spmf_of_set UNIV) = coin_spmf \<bind>
      (\<lambda>b. spmf_of_set UNIV \<bind>
      (\<lambda>A'. let A = transpose (\<chi> i. A' $ Some i); t = A' $ None
            in exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
               (\<lambda>(((msg1, msg2), \<sigma>),s).
               if valid_plains msg1 msg2
               then let msg = if b then msg1 else msg2 in 
       do {c \<leftarrow> spmf_of_set UNIV;
         let u = \<chi> i. c $ Some i;
             v = c $ None + to_module (round (real_of_int q / 2)) * plain_to_msg msg
          in return_spmf (u, v)} \<bind>  
                  (\<lambda> (u,v). exec_gpv ro.oracle 
                    (\<A>\<^sub>2 (compress_vec du u, compress_poly dv v) \<sigma>) s \<bind> 
                  (\<lambda>(b', s1). return_spmf (b' = b)))
               else coin_spmf)))"
      unfolding game\<^sub>3_def by simp
    also have "\<dots> = coin_spmf \<bind>
      (\<lambda>b. spmf_of_set UNIV \<bind>
      (\<lambda>A'. let A = transpose (\<chi> i. A' $ Some i); t = A' $ None
            in exec_gpv ro.oracle (\<A>\<^sub>1 (A, t)) ro.initial \<bind>
               (\<lambda>(((msg1, msg2), \<sigma>), s).
               if valid_plains msg1 msg2
               then let msg = if b then msg1 else msg2 in 
       do {c \<leftarrow> spmf_of_set UNIV;
        let u = \<chi> i. c $ Some i; v = c $ None
        in return_spmf (u, v)} \<bind>  
                  (\<lambda> (u,v). exec_gpv ro.oracle (\<A>\<^sub>2 
                    (compress_vec du u, compress_poly dv v) \<sigma>) s \<bind> 
                  (\<lambda>(b', s1). return_spmf (b' = b)))
               else coin_spmf)))" 
      unfolding indep_of_msg by simp
    also have "\<dots> = game\<^sub>4" 
      unfolding game\<^sub>4_def by simp
    finally show ?thesis by blast
  qed

text \<open>Finally, we can show that \<open>game\<^sub>4\<close> is the same as a coin flip. Therefore,
the probability to return true is exactly $0.5$.\<close>

  have game\<^sub>4_eq_coin: "game\<^sub>4 = coin_spmf"
  proof -
    have "game\<^sub>4 = spmf_of_set UNIV \<bind>
    (\<lambda>y. exec_gpv ro.oracle (\<A>\<^sub>1 (transpose (\<chi> i. y $ Some i), y $ None)) ro.initial \<bind>
    (\<lambda>y. if valid_plains (fst (fst (fst y))) (snd (fst (fst y)))
         then spmf_of_set UNIV \<bind>
              (\<lambda>ya. exec_gpv ro.oracle (\<A>\<^sub>2 (compress_vec du (\<chi> i. ya $ Some i), 
                    compress_poly dv (ya $ None)) (snd (fst y))) (snd y) \<bind>
              (\<lambda>y. coin_spmf))
         else coin_spmf))"
    unfolding game\<^sub>4_def by (simp add: bind_commute_spmf[of "coin_spmf"] split_def 
      if_distrib_bind_spmf2 bind_coin_spmf_eq_const bind_spmf_coin del: bind_spmf_const)
    also have "\<dots> = spmf_of_set UNIV \<bind>
    (\<lambda>y. exec_gpv ro.oracle (\<A>\<^sub>1 (transpose (\<chi> i. y $ Some i), y $ None)) ro.initial \<bind>
    (\<lambda>y. if valid_plains (fst (fst (fst y))) (snd (fst (fst y)))
         then coin_spmf
         else coin_spmf))"
    by (subst bind_spmf_coin) (subst lossless_exec_gpv, auto)
    also have "\<dots> = spmf_of_set UNIV \<bind>
    (\<lambda>y. exec_gpv ro.oracle (\<A>\<^sub>1 (transpose (\<chi> i. y $ Some i), y $ None)) ro.initial \<bind>
    (\<lambda>y. coin_spmf))"
      by simp
    also have "\<dots> = coin_spmf"
      by (subst bind_spmf_coin) (subst lossless_exec_gpv, auto)
    finally show ?thesis by auto
  qed

  have spmf_game\<^sub>4: "spmf (game\<^sub>4) True = 1/2" unfolding game\<^sub>4_eq_coin 
    spmf_coin_spmf by simp

text \<open>In the end, we assemble all the steps proven before in order to bound the advantage against
IND-CPA.\<close>

  have "ind_cpa.advantage (ro.oracle, ro.initial) \<A> = \<bar>spmf (game\<^sub>0) True - 1/2\<bar>" 
    unfolding ind_cpa.advantage.simps ind_cpa_game_eq_game\<^sub>0 ..
  also have "\<dots> \<le> \<bar>spmf (game\<^sub>1 is_pk) True - spmf (game\<^sub>1 rand_pk) True\<bar> + 
                  \<bar>spmf (game\<^sub>1 rand_pk) True - 1/2\<bar>"
    unfolding game\<^sub>0_eq_game\<^sub>1_is_pk by simp
  also have "\<dots> \<le> mlwe.advantage (kyber_reduction1 \<A>) + \<bar>spmf (game\<^sub>1 rand_pk) True - 1/2\<bar>"
    by (simp add: reduction1 \<A>[symmetric] del: \<A>)
  also have "\<dots> \<le> mlwe.advantage (kyber_reduction1 \<A>) + 
    \<bar>spmf (?sample (game\<^sub>2 is_encrypt)) True - spmf (?sample (game\<^sub>2 is_encrypt)) True \<bar> + 
    \<bar>spmf (?sample (game\<^sub>2 is_encrypt)) True - 1/2\<bar>"
    using game\<^sub>1_rand_pk_eq_game\<^sub>2_is_encrypt by simp
  also have "\<dots> \<le> mlwe.advantage (kyber_reduction1 \<A>) + 
    \<bar>spmf (game\<^sub>3 is_encrypt') True - spmf (game\<^sub>3 (\<lambda>_. spmf_of_set UNIV)) True \<bar> + 
    \<bar>spmf (game\<^sub>3 (\<lambda>_. spmf_of_set UNIV)) True - 1/2\<bar>"
    using game\<^sub>2_eq_game\<^sub>3_is_encrypt game\<^sub>2_eq_game\<^sub>3_rand_encrypt by simp
  also have "\<dots> \<le> mlwe.advantage (kyber_reduction1 \<A>) + 
    mlwe.advantage' (kyber_reduction2 \<A>) + 
    \<bar>spmf (game\<^sub>3 (\<lambda>_. spmf_of_set UNIV)) True - 1/2\<bar>"
    using reduction2 by simp
  also have "\<dots> \<le> mlwe.advantage (kyber_reduction1 \<A>) + 
    mlwe.advantage' (kyber_reduction2 \<A>) + 
    \<bar>spmf (game\<^sub>4) True - 1/2\<bar>"
    unfolding game\<^sub>3_eq_game\<^sub>4 by simp
  also have "\<dots> \<le> mlwe.advantage (kyber_reduction1 \<A>) + 
    mlwe.advantage' (kyber_reduction2 \<A>)"
    unfolding spmf_game\<^sub>4 by simp
  finally show ?thesis by simp

qed


end

end