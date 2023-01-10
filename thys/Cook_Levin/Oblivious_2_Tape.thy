section \<open>Existence of two-tape oblivious Turing machines\label{s:oblivious-two-tape}\<close>

theory Oblivious_2_Tape
  imports Oblivious_Polynomial NP
begin


text \<open>
In this section we show that for every polynomial-time multi-tape Turing machine
there is a polynomial-time two-tape oblivious Turing machine that computes the
same function and halts with its output tape head in cell number~1.

Consider a $k$-tape Turing machine $M$ with polynomially bounded running time
$T$. We construct a two-tape oblivious Turing machine $S$ simulating $M$ as
follows.

Lemma @{thm [source] polystructor} from the previous section provides us with a
polynomial-time two-tape oblivious TM and a function $f(n) \geq T(n)$ such that
the TM outputs $\mathbf{1}^{f(n)}$ for all inputs of length $n$.

Executing this TM is the first thing our simulator does. The $f(n)$
symbols~@{text \<one>} mark the space $S$ is going to use. Every cell $i=0, \dots,
f(n) - 1$ of this space is to store a symbol that encodes a $(2k + 2)$-tuple
consisting of:

\begin{itemize}
\item $k$ symbols from $M$'s alphabet representing the contents of all the
  $i$-th cells on the $k$ tapes of $M$;
\item $k$ flags (called ``head flags'') signalling which of the $k$ tape heads
  of $M$ is in cell $i$;
\item a flag (called ``counter flag'') initialized with 0;
\item a flag (called ``start flag'') signalling whether $i = 0$.
\end{itemize}

Together the counter flags are a unary counter from 0 to $f(n)$. They are
toggled from left to right. The start flags never change. The symbols and the
head flags represent the $k$ tapes of $M$ at some step of the execution.  By
choice of $f$ the TM $M$ cannot use more than $f(n)$ cells on any tape. So the
space marked with @{text \<one>} symbols on the simulator's output tape suffices.

Next the simulator initializes the space of @{text \<one>} symbols with code symbols
representing the start configuration of $M$ for the input given to the
simulator.

Then the main loop of the simulation performs $f(n)$ iterations. In each
iteration $S$ performs one step of $M$'s computation. In order to do this it
performs several left-to-right and right-to-left sweeps over all the $f(n)$
cells in the formatted section of the output tape.  A sweep will move the output
tape head one cell right (respectively left) in each step.  In this way the
simulator's head positions at any time will only depend on $f(n)$, and hence
on $n$. Thus the machine will be oblivious. Moreover $f(n) \ge T(n)$, and so $M$
will be in the halting state after $f(n)$ iterations of the simulation. Counting
the iterations to $f(n)$ is achieved via the counter flags. 

Finally the simulator extracts from each code symbol the symbol corresponding to
$M$'s output tape, thus reconstructing the output of $M$ on the simulator's
output tape. Thanks to the start flags, the simulator can easily locate the
leftmost cell and put the output tape head one to the right of it, as required.

The construction heavily uses the memorization-in-states technique (see
Chapter~\ref{s:tm-memorizing}). At first the machine features $2k + 1$
memorization tapes in addition to the input tape and output tape. The purpose of
those tapes is to store $M$'s state and the symbols under the tape heads of $M$
in the currently simulated step of $M$'s execution, as well as the $k$ symbols
to be written write and head movements to be executed by the simulator.
\<close>

text \<open>
The next predicate expresses that a Turing machine halts within a time bound
depending on the length of the input. We did not have a need for this fairly
basic predicate yet, because so far we were always interested in the halting
configuration, too, and so the predicate @{const computes_in_time} sufficed.

\null
\<close>

definition time_bound :: "machine \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "time_bound M k T \<equiv>
    \<forall>zs. bit_symbols zs \<longrightarrow> fst (execute M (start_config k zs) (T (length zs))) = length M"

lemma time_bound_ge:
  assumes "time_bound M k T" and "\<forall>n. fmt n \<ge> T n"
  shows "time_bound M k fmt"
  using time_bound_def assms by (metis execute_after_halting_ge)

text \<open>
The time bound also bounds the position of all the tape heads.
\<close>

lemma head_pos_le_time_bound:
  assumes "turing_machine k G M"
    and "time_bound M k T"
    and "bit_symbols zs"
    and "j < k"
  shows "execute M (start_config k zs) t <#> j \<le> T (length zs)"
  using assms time_bound_def[of M k T] execute_after_halting_ge head_pos_le_time[OF assms(1,4)]
  by (metis (no_types, lifting) nat_le_linear)

text \<open>
The entire construction will take place in a locale that assumes a
polynomial-time $k$-tape Turing machine $M$.
\<close>

locale two_tape =
  fixes M :: machine and k G :: nat and T :: "nat \<Rightarrow> nat"
  assumes tm_M: "turing_machine k G M"
    and poly_T: "big_oh_poly T"
    and time_bound_T: "time_bound M k T"
begin

lemma k_ge_2: "k \<ge> 2"
  using tm_M turing_machine_def by simp

lemma G_ge_4: "G \<ge> 4"
  using tm_M turing_machine_def by simp

text \<open>
The construction of the simulator relies on the formatted space on the output
tape to be large enough to hold the input. The size of the formatted space
depends on the time bound $T$, which might be less than the length of the input.
To ensure that the formatted space is large enough we increase the time bound
while keeping it polynomial. The new bound is $T'$:
\<close>

definition T' :: "nat \<Rightarrow> nat" where
  "T' n \<equiv> T n + n"

lemma poly_T': "big_oh_poly T'"
proof -
  have "big_oh_poly (\<lambda>n. n)"
    using big_oh_poly_poly[of 1] by simp
  then show ?thesis
    using T'_def big_oh_poly_sum[OF poly_T] by presburger
qed

lemma time_bound_T': "time_bound M k T'"
  using T'_def time_bound_ge[OF time_bound_T, of T'] by simp


subsection \<open>Encoding multiple tapes into one\<close>

text \<open>
The symbols on the output tape of the simulator are supposed to encode a $(2k +
2)$-tuple, where the first $k$ elements assume one of the values in $\{0, \dots,
G - 1\}$, whereas the other $k + 2$ are flags with two possible values only. For
uniformity we define an encoding where all elements range over $G$ values and
that works for tuples of every length.
\<close>

fun encode :: "nat list \<Rightarrow> nat" where
  "encode [] = 0" |
  "encode (x # xs) = x + G * encode xs"

text \<open>
For every $m \in \nat$, the enocoding is a bijective mapping from $\{0, \dots,
G - 1\}^m$ to $\{0, \dots, G^m - 1\}$.
\<close>

lemma encode_surj:
  assumes "n < G ^ m"
  shows "\<exists>xs. length xs = m \<and> (\<forall>x\<in>set xs. x < G) \<and> encode xs = n"
  using assms
proof (induction m arbitrary: n)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  define q where "q = n div G"
  define r where "r = n mod G"
  have "q < G ^ m"
    using Suc q_def
    by (auto simp add: less_mult_imp_div_less power_commutes)
  then obtain xs' where xs': "length xs' = m" "\<forall>x\<in>set xs'. x < G" "encode xs' = q"
    using Suc by auto
  have "r < G"
    using r_def G_ge_4 by simp
  have "encode (r # xs') = n"
    using xs'(3) q_def r_def G_ge_4 by simp
  moreover have "\<forall>x\<in>set (r # xs'). x < G"
    using xs'(2) `r < G` by simp
  moreover have "length (r # xs') = Suc m"
    using xs'(1) by simp
  ultimately show ?case
    by blast
qed

lemma encode_inj:
  assumes "\<forall>x\<in>set xs. x < G"
    and "length xs = m"
    and "\<forall>y\<in>set ys. y < G"
    and "length ys = m"
    and "encode xs = encode ys"
  shows "xs = ys"
  using assms
proof (induction m arbitrary: xs ys)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  obtain x xs' y ys' where xy: "xs = x # xs'" "ys = y # ys'"
    using Suc by (metis Suc_length_conv)
  then have len: "length xs' = m" "length ys' = m"
    using Suc by simp_all
  have *: "x + G * encode xs' = y + G * encode ys'"
    using Suc xy by simp
  moreover have "(x + G * encode xs') mod G = x"
    by (simp add: Suc.prems(1) xy(1))
  moreover have "(y + G * encode ys') mod G = y"
    by (simp add: Suc.prems(3) xy(2))
  ultimately have "x = y"
    by simp
  with * have "G * encode xs' = G * encode ys'"
    by simp
  then have "encode xs' = encode ys'"
    using G_ge_4 by simp
  with len Suc xy have "xs' = ys'"
    by simp
  then show ?case
    using `x = y` xy by simp
qed

lemma encode_less:
  assumes "\<forall>x\<in>set xs. x < G"
  shows "encode xs < G ^ (length xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then have "x < G"
    by simp
  have "encode (x # xs) = x + G * encode xs"
    by simp
  also have "... \<le> x + G * (G ^ (length xs) - 1)"
    using Cons by simp
  also have "... = x + G * G ^ (length xs) - G"
    by (simp add: right_diff_distrib')
  also have "... < G * G ^ (length xs)"
    using `x < G` less_imp_Suc_add by fastforce
  also have "... = G ^ (Suc (length xs))"
    by simp
  finally have "encode (x # xs) < G ^ (length (x # xs))"
    by simp
  then show ?case .
qed

text \<open>
Decoding a number into an $m$-tuple of numbers is then a well-defined operation.
\<close>

definition decode :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "decode m n \<equiv> THE xs. encode xs = n \<and> length xs = m \<and> (\<forall>x\<in>set xs. x < G)"

lemma decode:
  assumes "n < G ^ m"
  shows encode_decode: "encode (decode m n) = n"
    and length_decode: "length (decode m n) = m"
    and decode_less_G: "\<forall>x\<in>set (decode m n). x < G"
proof -
  have "\<exists>xs. length xs = m \<and> (\<forall>x\<in>set xs. x < G) \<and> encode xs = n"
    using assms encode_surj by simp
  then have *: "\<exists>!xs. encode xs = n \<and> length xs = m \<and> (\<forall>x\<in>set xs. x < G)"
    using encode_inj by auto
  let ?xs = "decode m n"
  let ?P = "\<lambda>xs. encode xs = n \<and> length xs = m \<and> (\<forall>x\<in>set xs. x < G)"
  have "encode ?xs = n \<and> length ?xs = m \<and> (\<forall>x\<in>set ?xs. x < G)"
    using * theI'[of ?P] decode_def by simp
  then show "encode (decode m n) = n" and "length (decode m n) = m" and "\<forall>x\<in>set (decode m n). x < G"
    by simp_all
qed

lemma decode_encode: "\<forall>x\<in>set xs. x < G \<Longrightarrow> decode (length xs) (encode xs) = xs"
proof -
  fix xs :: "nat list"
  assume a: "\<forall>x\<in>set xs. x < G"
  then have "encode xs < G ^ (length xs)"
    using encode_less by simp
  show "decode (length xs) (encode xs) = xs"
    unfolding decode_def
  proof (rule the_equality)
   show "encode xs = encode xs \<and> length xs = length xs \<and> (\<forall>x\<in>set xs. x < G)"
     using a by simp
   show "\<And>ys. encode ys = encode xs \<and> length ys = length xs \<and> (\<forall>x\<in>set ys. x < G) \<Longrightarrow> ys = xs"
     using a encode_inj by simp
  qed
qed

text \<open>
The simulator will access and update components of the encoded symbol.
\<close>

definition encode_nth :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "encode_nth m n j \<equiv> decode m n ! j"

definition encode_upd :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "encode_upd m n j x \<equiv> encode ((decode m n) [j:=x])"

lemma encode_nth_less:
  assumes "n < G ^ m" and "j < m"
  shows "encode_nth m n j < G"
  using assms encode_nth_def decode_less_G length_decode by simp

text \<open>
For the symbols the simulator actually uses, we fix $m = 2k + 2$ and reserve the
symbols $\triangleright$ and $\Box$, effectively shifting the symbols by two. We
call the symbols $\{2, \dots, G^{2k+2} + 2\}$ ``code symbols''.
\<close>

definition enc :: "symbol list \<Rightarrow> symbol" where
  "enc xs \<equiv> encode xs + 2"

definition dec :: "symbol \<Rightarrow> symbol list" where
  "dec n \<equiv> decode (2 * k + 2) (n - 2)"

lemma dec:
  assumes "n > 1" and "n < G ^ (2 * k + 2) + 2"
  shows enc_dec: "enc (dec n) = n"
    and length_dec: "length (dec n) = 2 * k + 2"
    and dec_less_G: "\<forall>x\<in>set (dec n). x < G"
proof -
  show "enc (dec n) = n"
    using enc_def dec_def encode_decode assms by simp
  show "length (dec n) = 2 * k + 2"
    using enc_def dec_def length_decode assms by simp
  show "\<forall>x\<in>set (dec n). x < G"
    using enc_def dec_def decode_less_G assms
    by (metis Suc_leI less_diff_conv2 one_add_one plus_1_eq_Suc)
qed

lemma dec_enc: "\<forall>x\<in>set xs. x < G \<Longrightarrow> length xs = 2 * k + 2 \<Longrightarrow> dec (enc xs) = xs"
  unfolding enc_def dec_def using decode_encode by fastforce

definition enc_nth :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "enc_nth n j \<equiv> dec n ! j"

lemma enc_nth: "\<forall>x\<in>set xs. x < G \<Longrightarrow> length xs = 2 * k + 2 \<Longrightarrow> enc_nth (enc xs) j = xs ! j"
  unfolding enc_nth_def by (simp add: dec_enc)

lemma enc_nth_dec:
  assumes "n > 1" and "n < G ^ (2 * k + 2) + 2"
  shows "enc_nth n j = (dec n) ! j"
  using assms enc_nth dec by metis

abbreviation is_code :: "nat \<Rightarrow> bool" where
  "is_code n \<equiv> n < G ^ (2 * k + 2) + 2 \<and> 1 < n"

lemma enc_nth_less:
  assumes "is_code n" and "j < 2 * k + 2"
  shows "enc_nth n j < G"
  using assms enc_nth_def by (metis dec_less_G in_set_conv_nth length_dec)

lemma enc_less: "\<forall>x\<in>set xs. x < G \<Longrightarrow> length xs = 2 * k + 2 \<Longrightarrow> enc xs < G ^ (2 * k + 2) + 2"
  using encode_less enc_def by fastforce

definition enc_upd :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "enc_upd n j x \<equiv> enc ((dec n) [j:=x])"

lemma enc_upd_is_code:
  assumes "is_code n" and "j < 2 * k + 2" and "x < G"
  shows "is_code (enc_upd n j x)"
proof -
  let ?ys = "(dec n) [j:=x]"
  have "\<forall>h\<in>set (dec n). h < G"
    using assms(1,2) dec_less_G by auto
  then have "\<forall>h\<in>set ?ys. h < G"
    using assms(3)
    by (metis in_set_conv_nth length_list_update nth_list_update_eq nth_list_update_neq)
  moreover have "length ?ys = 2 * k + 2"
    using assms length_dec by simp
  ultimately have "enc ?ys < G ^ (2 * k + 2) + 2"
    using enc_less by simp
  then show ?thesis
    using enc_upd_def enc_def by simp
qed

text \<open>
The code symbols require the simulator to have an alphabet of at least size
$G^{2k + 2} + 2$. On top of that we want to store on a memorization tape the
state that $M$ is in. So the alphabet must have at least @{term "length M + 1"}
symbols. Both conditions are met by the simulator having an alphabet of size
$G'$:
\<close>

definition G' :: nat where
  "G' \<equiv> G ^ (2 * k + 2) + 2 + length M"

lemma G'_ge_6: "G' \<ge> 6"
proof -
  have "4 ^ 2 > (5::nat)"
    by simp
  then have "G ^ 2 > (5::nat)"
    using G_ge_4 less_le_trans power2_nat_le_eq_le by blast
  then have "G ^ (2 * k + 2) > (5::nat)"
    using k_ge_2 G_ge_4
    by (metis (no_types, opaque_lifting) dec_induct le_add2 order_less_le_subst1 pow_mono zero_less_Suc zero_less_numeral)
  then show ?thesis
    using G'_def by simp
qed

corollary G'_ge: "G' \<ge> 4" "G' \<ge> 5"
  using G'_ge_6 by simp_all

lemma G'_ge_G: "G' \<ge> G"
proof -
  have "G ^ 2 \<ge> G"
    by (simp add: power2_nat_le_imp_le)
  then have "G ^ (2 * k + 2) \<ge> G"
    by simp
  then show ?thesis using G'_def
    by linarith
qed

corollary enc_less_G': "\<forall>x\<in>set xs. x < G \<Longrightarrow> length xs = 2 * k + 2 \<Longrightarrow> enc xs < G'"
  using enc_less G'_def by fastforce

lemma enc_greater: "enc xs > 1"
  using enc_def by simp


subsection \<open>Construction of the simulator Turing machine\<close>

text \<open>
The simulator is a sequence of three Turing machines: The ``formatter'', which
initializes the output tape; the loop, which simulates the TM $M$ for
polynomially many steps; and a cleanup TM, which makes the output tape look like
the output tape of $M$. All these machines are discussed in order in the
following subsections.

The simulator will start with $2k + 1$ memorization tapes for a total of $2k +
3$ tapes. The simulation action will take place on the output tape.
\<close>


subsubsection \<open>Initializing the simulator's tapes\<close>

text \<open>
The function @{const T'} is polynomially bounded and therefore there is a
polynomial-time two-tape oblivious Turing machine that outputs at least $T'(n)$
symbols~@{text \<one>} on an input of length $n$, as we have proven in the previous
section (lemma~@{thm [source] polystructor}). We now obtain such a Turing
machine together with its running time bound and trace. This TM will be one of
our blocks for building the simulator TM. We will call it the ``formatter''.

\null
\<close>

definition fmt_es_pM :: "(nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> (nat \<times> nat) list) \<times> machine" where
  "fmt_es_pM \<equiv> SOME tec.
    turing_machine 2 G' (snd (snd tec)) \<and>
    big_oh_poly (\<lambda>n. length ((fst (snd tec)) n)) \<and>
    big_oh_poly (fst tec) \<and>
    (\<forall>n. T' n \<le> (fst tec) n) \<and>
    (\<forall>zs. proper_symbols zs \<longrightarrow> traces (snd (snd tec)) (start_tapes_2 zs) ((fst (snd tec)) (length zs)) (one_tapes_2 zs ((fst tec) (length zs))))"

lemma polystructor':
  fixes GG :: nat and g :: "nat \<Rightarrow> nat"
  assumes "big_oh_poly g" and "GG \<ge> 5"
  shows "\<exists>f_es_M.
    turing_machine 2 GG (snd (snd f_es_M)) \<and>
    big_oh_poly (\<lambda>n. length ((fst (snd f_es_M)) n)) \<and>
    big_oh_poly (fst f_es_M) \<and>
    (\<forall>n. g n \<le> (fst f_es_M) n) \<and>
    (\<forall>zs. proper_symbols zs \<longrightarrow> traces (snd (snd f_es_M)) (start_tapes_2 zs) ((fst (snd f_es_M)) (length zs)) (one_tapes_2 zs ((fst f_es_M) (length zs))))"
  using polystructor[OF assms] by auto

lemma fmt_es_pM: "turing_machine 2 G' (snd (snd fmt_es_pM)) \<and>
    big_oh_poly (\<lambda>n. length ((fst (snd fmt_es_pM)) n)) \<and>
    big_oh_poly (fst fmt_es_pM) \<and>
    (\<forall>n. T' n \<le> (fst fmt_es_pM) n) \<and>
    (\<forall>zs. proper_symbols zs \<longrightarrow> traces (snd (snd fmt_es_pM)) (start_tapes_2 zs) ((fst (snd fmt_es_pM)) (length zs)) (one_tapes_2 zs ((fst fmt_es_pM) (length zs))))"
  using fmt_es_pM_def polystructor'[OF poly_T' G'_ge(2)]
    someI_ex[of "\<lambda>tec.
      turing_machine 2 G' (snd (snd tec)) \<and>
      big_oh_poly (\<lambda>n. length ((fst (snd tec)) n)) \<and>
      big_oh_poly (fst tec) \<and>
      (\<forall>n. T' n \<le> (fst tec) n) \<and>
      (\<forall>zs. proper_symbols zs \<longrightarrow> traces (snd (snd tec)) (start_tapes_2 zs) ((fst (snd tec)) (length zs)) (one_tapes_2 zs ((fst tec) (length zs))))"]
  by simp

definition fmt :: "nat \<Rightarrow> nat" where
  "fmt \<equiv> fst fmt_es_pM"

definition es_fmt :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "es_fmt \<equiv> fst (snd fmt_es_pM)"

definition tm_fmt :: "machine" where
  "tm_fmt \<equiv> snd (snd fmt_es_pM)"

text \<open>
The formatter TM is @{const tm_fmt}, the number of @{text \<one>} symbols written to
the output tape on input of length $n$ is @{term "fmt n"}, and the trace on
inputs of length $n$ is @{term "es_fmt n"}.
\<close>

lemma fmt:
  "turing_machine 2 G' tm_fmt"
  "big_oh_poly (\<lambda>n. length (es_fmt n))"
  "big_oh_poly fmt"
  "\<And>n. T' n \<le> fmt n"
  "\<And>zs. proper_symbols zs \<Longrightarrow>
    traces tm_fmt (start_tapes_2 zs) (es_fmt (length zs)) (one_tapes_2 zs (fmt (length zs)))"
  unfolding fmt_def es_fmt_def tm_fmt_def using fmt_es_pM by simp_all

lemma fmt_ge_n: "fmt n \<ge> n"
  using fmt(4) T'_def by (metis dual_order.strict_trans2 le_less_linear not_add_less2)

text \<open>
The formatter is a two-tape TM. The first incarnation of the simulator will have
two tapes and $2k + 1$ memorization tapes.  So for now we formally need to
extend the formatter to $2k + 3$ tapes:
\<close>

definition "tm1 \<equiv> append_tapes 2 (2 * k + 3) tm_fmt"

lemma tm1_tm: "turing_machine (2 * k + 3) G' tm1"
  unfolding tm1_def using append_tapes_tm by (simp add: fmt(1))

text \<open>
Next we replace all non-blank symbols on the output tape by code symbols
representing the tuple of $2k + 2$ zeros.
\<close>

definition "tm1_2 \<equiv> tm_const_until 1 1 {\<box>} (enc (replicate k 0 @ replicate k 0 @ [0, 0]))"

lemma tm1_2_tm: "turing_machine (2 * k + 3) G' tm1_2"
  unfolding tm1_2_def
  using G'_ge
proof (intro tm_const_until_tm, auto)
  show "enc (replicate k 0 @ replicate k 0 @ [0, 0]) < G'"
    using G_ge_4 by (intro enc_less_G', auto)
qed

definition "tm2 \<equiv> tm1 ;; tm1_2"

lemma tm2_tm: "turing_machine (2 * k + 3) G' tm2"
  unfolding tm2_def using tm1_tm tm1_2_tm by simp

definition "tm3 \<equiv> tm2 ;; tm_start 1"

lemma tm3_tm: "turing_machine (2 * k + 3) G' tm3"
  unfolding tm3_def using tm2_tm tm_start_tm G'_ge by simp

text \<open>
Back at the start symbol of the output tape, we replace it by the code symbol
for the tuple $1^k1^k01$. The first $k$ ones represent that initially the $k$
tapes of $M$ have the start symbol (numerically 1) in the leftmost cell.  The
second run of $k$ ones represent that initially all $k$ tapes have their tape
heads in the leftmost cell. The following 0 is the first bit of the unary
counter, currently set to zero. The final flag~1  signals that this is the
leftmost cell. Unlike the start symbols this signal flag cannot be overwritten
by $M$.
\<close>

definition "tm4 \<equiv> tm3 ;; tm_write 1 (enc (replicate k 1 @ replicate k 1 @ [0, 1]))"

lemma tm3_4_tm: "turing_machine (2 * k + 3) G' (tm_write 1 (enc (replicate k 1 @ replicate k 1 @ [0, 1])))"
  using G'_ge enc_less_G' G_ge_4 tm_write_tm by simp

lemma tm4_tm: "turing_machine (2 * k + 3) G' tm4"
  unfolding tm4_def using tm3_tm tm3_4_tm by simp

definition "tm5 \<equiv> tm4 ;; tm_right 1"

lemma tm5_tm: "turing_machine (2 * k + 3) G' tm5"
  unfolding tm5_def using tm4_tm by (simp add: G'_ge(1) tm_right_tm)

text \<open>
So far the simulator's output tape encodes $k$ tapes that are empty but for the
start symbols. To represent the start configuration of $M$, we need to copy the
contents of the input tape to the output tape. The following TM moves the work
head to the first blank while copying the input tape content. Here we exploit
$T'(n) \geq n$, which implies that the formatted section is long enough to hold
the input.
\<close>

definition "tm5_6 \<equiv> tm_trans_until 0 1 {0} (\<lambda>h. enc (h mod G # replicate (k - 1) 0 @ replicate k 0 @ [0, 0]))"

definition "tm6 \<equiv> tm5 ;; tm5_6"

lemma tm5_6_tm: "turing_machine (2 * k + 3) G' tm5_6"
  unfolding tm5_6_def
proof (rule tm_trans_until_tm, auto simp add: G'_ge(1) G_ge_4 k_ge_2 enc_less_G')
  show "\<And>h. h < G' \<Longrightarrow> enc (h mod G # replicate (k - Suc 0) 0 @ replicate k 0 @ [0, 0]) < G'"
    using G_ge_4 k_ge_2 enc_less_G' by simp
qed

lemma tm6_tm: "turing_machine (2 * k + 3) G' tm6"
  unfolding tm6_def using tm5_tm tm5_6_tm by simp

text \<open>
Since we have overwritten the leftmost cell of the output tape with some code
symbol, we cannot return to it using @{const tm_start}. But we can use @{const
tm_left_until} with a special set of symbols:
\<close>

abbreviation StartSym :: "symbol set" where
  "StartSym \<equiv> {y. y < G ^ (2 * k + 2) + 2 \<and> y > 1 \<and> dec y ! (2 * k + 1) = 1}"

abbreviation "tm_left_until1 \<equiv> tm_left_until StartSym 1"

lemma tm_left_until1_tm: "turing_machine (2 * k + 3) G' tm_left_until1"
  using tm_left_until_tm G'_ge(1) k_ge_2 by simp

definition "tm7 \<equiv> tm6 ;; tm_left_until1"

lemma tm7_tm: "turing_machine (2 * k + 3) G' tm7"
  unfolding tm7_def using tm6_tm tm_left_until1_tm by simp

text \<open>
Tape number $2$ is meant to memorize $M$'s state during the simulation.
Initially the state is the start state, that is, zero.
\<close>

definition "tm8 \<equiv> tm7 ;; tm_write 2 0"

lemma tm8_tm: "turing_machine (2 * k + 3) G' tm8"
  unfolding tm8_def using tm7_tm tm_write_tm k_ge_2 G'_ge(1) by simp

text \<open>
We also initialize memorization tapes $3, \dots, 2k + 2$ to zero. This concludes
the initialization of the simulator's tapes.
\<close>

definition "tm9 \<equiv> tm8 ;; tm_write_many {3..<2 * k + 3} 0"

lemma tm9_tm: "turing_machine (2 * k + 3) G' tm9"
  unfolding tm9_def using tm8_tm tm_write_many_tm k_ge_2 G'_ge(1) by simp


subsubsection \<open>The loop\<close>

text \<open>
The core of the simulator is a loop whose body is executed @{term "fmt n"} many
times. Each iteration simulates one step of the Turing machine $M$.  For the
analysis of the loop we describe the $2k + 3$ tapes in the form @{term "[a, b,
c] @ map f1 [0..<k] @ map f2 [0..<k]"}.
\<close>

lemma threeplus2k_2:
  assumes "3 \<le> j \<and> j < k + 3"
  shows "([a, b, c] @ map f1 [0..<k] @ map f2 [0..<k]) ! j = f1 (j - 3)"
  using assms by (simp add: nth_append less_diff_conv2 numeral_3_eq_3)

lemma threeplus2k_3:
  assumes "k + 3 \<le> j \<and> j < 2 * k + 3"
  shows "([a, b, c] @ map f1 [0..<k] @ map f2 [0..<k]) ! j = f2 (j - k - 3)"
  using assms by (simp add: nth_append less_diff_conv2 numeral_3_eq_3)

text \<open>
To ensure the loop runs for @{term "fmt n"} iterations we increment the unary
counter in the code symbols in each iteration. The loop terminates when there
are no more code symbols with an unset counter flag. The TM that prepares the
loop condition sweeps the output tape left-to-right searching for the first symbol
that is either blank or has an unset counter flag. The condition then checks for
which of the two cases occurred. This is the condition TM: \<close>

definition "tmC \<equiv> tm_right_until 1 {y. y < G ^ (2 * k + 2) + 2 \<and> (y = 0 \<or> dec y ! (2 * k) = 0)}"

lemma tmC_tm: "turing_machine (2 * k + 3) G' tmC"
  using tmC_def tm_right_until_tm using G'_ge(1) by simp

text \<open>
At the start of the iteration, the memorization tape~2 has the state of $M$, and
all other memorization tapes contain $0$. The output tape head is at the leftmost
code symbol with unset counter flag. The first order of business is to move back
to the beginning of the output tape.
\<close>

definition "tmL1 \<equiv> tm_left_until1"

lemma tmL1_tm: "turing_machine (2 * k + 3) G' tmL1"
  unfolding tmL1_def using tm6_tm tm_left_until1_tm by simp

text \<open>
Then the output tape head sweeps right until it encounters a blank. During the
sweep the Turing machine checks for any set head flags, and if it finds the one
for tape $j$ set, it memorizes the symbol for tape $j$ on tape $3 + k + j$.  The
next command performs this operation:
\<close>

definition cmdL2 :: command where
  "cmdL2 rs \<equiv>
    (if rs ! 1 = \<box>
     then (1, zip rs (replicate (2*k+3) Stay))
     else
      (0,
       [(rs!0, Stay), (rs!1, Right), (rs!2, Stay)] @
       (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
       (map (\<lambda>j. (if 1 < rs ! 1 \<and> rs ! 1 < G^(2*k+2)+2 \<and> enc_nth (rs!1) (k+j) = 1 then enc_nth (rs!1) j else rs!(3+k+j), Stay)) [0..<k])))"

lemma cmdL2_at_eq_0:
  assumes "rs ! 1 = 0" and "j < 2 * k + 3" and "length rs = 2 * k + 3"
  shows "snd (cmdL2 rs) ! j = (rs ! j, Stay)"
  using assms by (simp add: cmdL2_def)

lemma cmdL2_at_3:
  assumes "rs ! 1 \<noteq> \<box>" and "3 \<le> j \<and> j < k + 3"
  shows "cmdL2 rs [!] j = (rs ! j, Stay)"
  using cmdL2_def assms threeplus2k_2
  by (metis (no_types, lifting) le_add_diff_inverse2 snd_conv)

lemma cmdL2_at_4:
  assumes "rs ! 1 \<noteq> \<box>" and "k + 3 \<le> j \<and> j < 2 * k + 3"
  shows "cmdL2 rs [!] j =
     (if 1 < rs ! 1 \<and> rs ! 1 < G^(2*k+2)+2 \<and> enc_nth (rs ! 1) (j-3) = 1
      then enc_nth (rs ! 1) (j-k-3)
      else rs ! j, Stay)"
  unfolding cmdL2_def using assms threeplus2k_3[OF assms(2), of "(rs ! 0, Stay)"] by simp

lemma cmdL2_at_4'':
  assumes "rs ! 1 \<noteq> \<box>"
    and "k + 3 \<le> j \<and> j < 2 * k + 3"
    and "\<not> (1 < rs ! 1 \<and> rs ! 1 < G^(2*k+2)+2)"
  shows "cmdL2 rs [!] j = (rs ! j, Stay)"
proof -
  have "cmdL2 rs [!] j =
      (if 1 < rs ! 1 \<and> rs ! 1 < G^(2*k+2)+2 \<and> enc_nth (rs!1) (j-3) = 1 then enc_nth (rs!1) (j-k-3) else rs!j, Stay)"
    using assms cmdL2_at_4 by blast
  then show ?thesis
    using assms(3) by auto
qed

lemma turing_command_cmdL2: "turing_command (2 * k + 3) 1 G' cmdL2"
proof
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> length ([!!] cmdL2 gs) = length gs"
    unfolding cmdL2_def by simp
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> 0 < 2 * k + 3 \<Longrightarrow> cmdL2 gs [.] 0 = gs ! 0"
    unfolding cmdL2_def by simp
  show "cmdL2 gs [.] j < G'"
      if "length gs = 2 * k + 3" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G'" "j < length gs"
      for gs j
  proof (cases "gs ! 1 = 0")
    case True
    then have "cmdL2 gs = (1, zip gs (replicate (2*k+3) Stay))"
      unfolding cmdL2_def by simp
    have "cmdL2 gs [.] j = gs ! j"
      using that(1,3) by (simp add: \<open>cmdL2 gs = (1, zip gs (replicate (2 * k + 3) Stay))\<close>)
    then show ?thesis
      using that(2,3) by simp
  next
    case False
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using \<open>j < length gs\<close> \<open>length gs = 2 * k + 3\<close> by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        by (simp add: cmdL2_def that(1) that(2))
    next
      case 2
      then show ?thesis
        unfolding cmdL2_def using False that by auto
    next
      case 3
      then show ?thesis
        unfolding cmdL2_def using False that by auto
    next
      case 4
      then have "snd (cmdL2 gs) ! j = (gs ! j, Stay)"
        unfolding cmdL2_def using False that threeplus2k_2[OF 4, of "(gs ! 0, Stay)"] by simp
      then show ?thesis
        using that by (simp add: \<open>snd (cmdL2 gs) ! j = (gs ! j, Stay)\<close>)
    next
      case 5
      show ?thesis
      proof (cases "1 < gs ! 1 \<and> gs ! 1 < G ^ (2*k+2) + 2")
        case True
        then have *: "cmdL2 gs [.] j = (if enc_nth (gs ! 1) (j-3) = 1 then enc_nth (gs ! 1) (j-k-3) else gs ! j)"
          using 5 False by (simp add: cmdL2_at_4)
        let ?n = "gs ! 1"
        have len: "length (dec ?n) = 2 * k + 2" and less_G: "\<forall>x\<in>set (dec ?n). x < G"
          using True length_dec dec_less_G by (simp, blast)
        have **: "enc_nth ?n (j-k-3) = dec ?n ! (j-k-3)"
          using enc_nth_dec True by simp
        then have "dec ?n ! (j-k-3) < G"
          using less_G 5 len by auto
        then have "dec ?n ! (j-k-3) < G'"
          using G'_ge_G by simp
        moreover have "gs ! j < G'"
          using that by simp
        ultimately show ?thesis
          using * ** by simp
      next
        case 6: False
        have "cmdL2 gs [!] j = (gs ! j, Stay)"
          using cmdL2_at_4''[OF False 5 6] by simp
        then show ?thesis
          using that by (simp add: \<open>snd (cmdL2 gs) ! j = (gs ! j, Stay)\<close>)
      qed
    qed
  qed
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> [*] (cmdL2 gs) \<le> 1"
    using cmdL2_def by simp
qed

definition "tmL1_2 \<equiv> [cmdL2]"

lemma tmL1_2_tm: "turing_machine (2 * k + 3) G' tmL1_2"
  using tmL1_2_def using turing_command_cmdL2 G'_ge by auto

definition "tmL2 \<equiv> tmL1 ;; tmL1_2"

lemma tmL2_tm: "turing_machine (2 * k + 3) G' tmL2"
  by (simp add: tmL1_2_tm tmL1_tm tmL2_def)

text \<open>
The memorization tapes $3, \dots, 2 + k$ will store the head movements for
tapes $0, \dots, k - 1$ of $M$. The directions are encoded as symbols thus:
\<close>

definition direction_to_symbol :: "direction \<Rightarrow> symbol" where
  "direction_to_symbol m \<equiv> (case m of Left \<Rightarrow> \<box> | Stay \<Rightarrow> \<triangleright> | Right \<Rightarrow> \<zero>)"

lemma direction_to_symbol_less: "direction_to_symbol m < 3"
  using direction_to_symbol_def by (cases m) simp_all

text \<open>
At this point in the iteration the memorization tapes $k + 3, \dots, 2k+2$
contain the symbols under the $k$ tape heads of $M$, and tape $2$ contains the
state $M$ is in. Therefore all information is available to determine the actions
$M$ is taking in the step currently simulated.  The next command has the entire
behavior of $M$ ``hard-coded'' and causes the actions to be stored on
memorization tapes $3, \dots, 2k+2$: the output symbols on the tapes $k + 3,
\dots, 2k + 2$, and the $k$ head movements on the tapes $3, \dots, k + 2$. The
follow-up state will again be memorized on tape $2$. All this happens in one
step of the simulator machine.
\<close>

definition cmdL3 :: command where
  "cmdL3 rs \<equiv>
   (1,
    [(rs ! 0, Stay),
     (rs ! 1, Stay),
     (if rs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) rs). h < G)
      then fst ((M ! (rs ! 2)) (drop (k + 3) rs))
      else rs ! 2, Stay)] @
    map
      (\<lambda>j. (if rs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) rs). h < G) then direction_to_symbol ((M ! (rs ! 2)) (drop (k + 3) rs) [~] j) else 1, Stay))
      [0..<k] @
    map (\<lambda>j. (if rs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) rs). h < G) then ((M ! (rs ! 2)) (drop (k + 3) rs) [.] j) else rs ! (k + 3 + j), Stay)) [0..<k])"

lemma cmdL3_at_2a:
  assumes "gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G)"
  shows "cmdL3 gs [!] 2 = (fst ((M ! (gs ! 2)) (drop (k + 3) gs)), Stay)"
  using cmdL3_def assms by simp

lemma cmdL3_at_2b:
  assumes "\<not> (gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G))"
  shows "cmdL3 gs [!] 2 = (gs ! 2, Stay)"
  using cmdL3_def assms by auto

lemma cmdL3_at_3a:
  assumes "3 \<le> j \<and> j < k + 3"
    and "gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G)"
  shows "cmdL3 gs [!] j = (direction_to_symbol ((M ! (gs ! 2)) (drop (k + 3) gs) [~] (j - 3)), Stay)"
  using cmdL3_def assms(2) threeplus2k_2[OF assms(1), of "(gs ! 0, Stay)"] by simp

lemma cmdL3_at_3b:
  assumes "3 \<le> j \<and> j < k + 3"
    and "\<not> (gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G))"
  shows "cmdL3 gs [!] j = (1, Stay)"
  using cmdL3_def assms(2) threeplus2k_2[OF assms(1), of "(gs ! 0, Stay)"] by auto

lemma cmdL3_at_4a:
  assumes "k + 3 \<le> j \<and> j < 2 * k + 3"
    and "gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G)"
  shows "cmdL3 gs [!] j = ((M ! (gs ! 2)) (drop (k + 3) gs) [.] (j - k - 3), Stay)"
  using cmdL3_def assms(2) threeplus2k_3[OF assms(1), of "(gs ! 0, Stay)"] by simp

lemma cmdL3_at_4b:
  assumes "k + 3 \<le> j \<and> j < 2 * k + 3"
    and "\<not> (gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G))"
  shows "cmdL3 gs [!] j = (gs ! j, Stay)"
  using assms cmdL3_def threeplus2k_3[OF assms(1), of "(gs ! 0, Stay)"] by auto

lemma cmdL3_if_comm:
  assumes "length gs = 2 * k + 3" and "gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G)"
  shows "length ([!!] (M ! (gs ! 2)) (drop (k + 3) gs)) = k"
    and "\<And>j. j < k \<Longrightarrow> (M ! (gs ! 2)) (drop (k + 3) gs) [.] j < G"
proof -
  let ?rs = "drop (k + 3) gs"
  let ?cmd = "M ! (gs ! 2)"
  have *: "turing_command k (length M) G ?cmd"
    using assms(2) tm_M turing_machineD(3) by simp
  then show "length ([!!] ?cmd ?rs) = k"
    using turing_commandD(1) assms(1) by simp
  have "\<And>i. i < length ?rs \<Longrightarrow> ?rs ! i < G"
    using assms(2) nth_mem by blast
  then show "\<And>j. j < k \<Longrightarrow> (M ! (gs ! 2)) (drop (k + 3) gs) [.] j < G"
    using * turing_commandD(2) assms by simp
qed

lemma turing_command_cmdL3: "turing_command (2 * k + 3) 1 G' cmdL3"
proof
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> length ([!!] cmdL3 gs) = length gs"
    using cmdL3_def by simp
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> 0 < 2 * k + 3 \<Longrightarrow> cmdL3 gs [.] 0 = gs ! 0"
    using cmdL3_def by simp
  show "cmdL3 gs [.] j < G'"
    if "length gs = 2 * k + 3" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G'" "j < length gs"
    for gs j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using \<open>j < length gs\<close> \<open>length gs = 2 * k + 3\<close> by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using that cmdL3_def by simp
    next
      case 2
      then show ?thesis
        using that cmdL3_def by simp
    next
      case 3
      then show ?thesis
      proof (cases "gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G)")
        case True
        have "length (drop (k + 3) gs) = k"
          using that(1) by simp
        then have "fst ((M ! (gs ! 2)) (drop (k + 3) gs)) \<le> length M"
          using True turing_commandD(4) tm_M turing_machineD(3) by blast
        moreover have "cmdL3 gs [.] j = fst ((M ! (gs ! 2)) (drop (k + 3) gs))"
          using cmdL3_def True 3 by simp
        ultimately show ?thesis
          using G'_def by simp
      next
        case False
        then have "cmdL3 gs [.] j = gs ! 2"
          using cmdL3_def 3 by auto
        then show ?thesis
          using 3 that(2,3) by simp
      qed
    next
      case 4
      then show ?thesis
      proof (cases "gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G)")
        case True
        then have "cmdL3 gs [.] j = direction_to_symbol ((M ! (gs ! 2)) (drop (k + 3) gs) [~] (j - 3))"
          using cmdL3_at_3a 4 by simp
        then have "cmdL3 gs [.] j < 3"
          using direction_to_symbol_less by simp
        then show ?thesis
          using G'_ge by simp
      next
        case False
        then show ?thesis
          using cmdL3_at_3b[OF 4] G'_ge by simp
      qed
    next
      case 5
      then show ?thesis
      proof (cases "gs ! 2 < length M \<and> (\<forall>h\<in>set (drop (k + 3) gs). h < G)")
        case True
        then have "cmdL3 gs [.] j = (M ! (gs ! 2)) (drop (k + 3) gs) [.] (j - k - 3)"
          using cmdL3_at_4a[OF 5] by simp
        then have "cmdL3 gs [.] j < G"
          using cmdL3_if_comm True 5 that(1) by auto
        then show ?thesis
          using G'_ge_G by simp
      next
        case False
        then have "cmdL3 gs [.] j = gs ! j"
          using cmdL3_at_4b[OF 5] by simp
        then show ?thesis
          using that by simp
      qed
    qed
  qed
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> [*] (cmdL3 gs) \<le> 1"
    using cmdL3_def by simp
qed

definition "tmL2_3 \<equiv> [cmdL3]"

lemma tmL2_3_tm: "turing_machine (2 * k + 3) G' tmL2_3"
  unfolding tmL2_3_def using G'_ge(1) turing_command_cmdL3 by auto

definition "tmL3 \<equiv> tmL2 ;; tmL2_3"

lemma tmL3_tm: "turing_machine (2 * k + 3) G' tmL3"
  by (simp add: tmL2_3_tm tmL2_tm tmL3_def)

text \<open>
Next the output tape head sweeps left to the beginning of the tape, otherwise
doing nothing.
\<close>

definition "tmL4 \<equiv> tmL3 ;; tm_left_until1"

lemma tmL4_tm: "turing_machine (2 * k + 3) G' tmL4"
  using tmL3_tm tmL4_def tmL1_def tm_left_until1_tm by simp

text \<open>
The next four commands @{term cmdL4}, @{term cmdL5}, @{term cmdL6}, @{term
cmdL7} are parameterized by $jj = 0, \dots, k - 1$. Their job is applying the
write operation and head movement for tape $jj$ of $M$. The entire block of
commands will then be executed $k$ times, once for each $jj$.

The first of these commands sweeps right again and applies the write operation
for tape $jj$, which is memorized on tape $3 + k + jj$. To this end it checks for head flags and
updates the code symbol component $jj$ with the contents of tape $3+k+jj$ when
the head flag for tape $jj$ is set.
\<close>

definition "cmdL5 jj rs \<equiv>
  if rs ! 1 = \<box>
  then (1, zip rs (replicate (2*k+3) Stay))
  else
   (0,
    [(rs ! 0, Stay),
     (if is_code (rs ! 1) \<and> rs ! (3+k+jj) < G \<and> enc_nth (rs ! 1) (k+jj) = 1
      then enc_upd (rs ! 1) jj (rs ! (3+k+jj))
      else rs ! 1,
      Right),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k]))"

lemma cmdL5_eq_0:
  assumes "j < 2 * k + 3" and "length gs = 2 * k + 3" and "gs ! 1 = 0"
  shows "cmdL5 jj gs [!] j = (gs ! j, Stay)"
  unfolding cmdL5_def using assms by simp

lemma cmdL5_at_0:
  assumes "gs ! 1 \<noteq> 0"
  shows "cmdL5 jj gs [!] 0 = (gs ! 0, Stay)"
  unfolding cmdL5_def using assms by simp

lemma cmdL5_at_1:
  assumes "gs ! 1 \<noteq> 0"
    and "is_code (gs ! 1) \<and> gs ! (3+k+jj) < G \<and> enc_nth (gs!1) (k+jj) = 1"
  shows "cmdL5 jj gs [!] 1 = (enc_upd (gs!1) jj (gs!(3+k+jj)), Right)"
  unfolding cmdL5_def using assms by simp

lemma cmdL5_at_1_else:
  assumes "gs ! 1 \<noteq> 0"
    and "\<not> (is_code (gs ! 1) \<and> gs ! (3+k+jj) < G \<and> enc_nth (gs!1) (k+jj) = 1)"
  shows "cmdL5 jj gs [!] 1 = (gs ! 1, Right)"
  unfolding cmdL5_def using assms by auto

lemma cmdL5_at_2:
  assumes "gs ! 1 \<noteq> 0"
  shows "cmdL5 jj gs [!] 2 = (gs ! 2, Stay)"
  unfolding cmdL5_def using assms by simp

lemma cmdL5_at_3:
  assumes "gs ! 1 \<noteq> 0" and "3 \<le> j \<and> j < 3 + k"
  shows "cmdL5 jj gs [!] j = (gs ! j, Stay)"
  unfolding cmdL5_def using assms threeplus2k_2[where ?a="(gs ! 0, Stay)"] by simp

lemma cmdL5_at_4:
  assumes "gs ! 1 \<noteq> 0" and "3 + k \<le> j \<and> j < 2 * k + 3"
  shows "cmdL5 jj gs [!] j = (gs ! j, Stay)"
  unfolding cmdL5_def using assms threeplus2k_3[where ?a="(gs ! 0, Stay)"] by simp

lemma turing_command_cmdL5:
  assumes "jj < k"
  shows "turing_command (2 * k + 3) 1 G' (cmdL5 jj)"
proof
  show "length gs = 2 * k + 3 \<Longrightarrow> length ([!!] cmdL5 jj gs) = length gs" for gs
    unfolding cmdL5_def by (cases "gs!1=0") simp_all
  show goal2: "length gs = 2 * k + 3 \<Longrightarrow> 0 < 2 * k + 3 \<Longrightarrow> cmdL5 jj gs [.] 0 = gs ! 0" for gs
    unfolding cmdL5_def by (cases "gs ! 1=0") simp_all
  show "cmdL5 jj gs [.] j < G'"
    if "length gs = 2 * k + 3" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G'" "j < length gs"
    for gs j
  proof (cases "gs ! 1 = 0")
    case True
    then show ?thesis
      using that cmdL5_eq_0 by simp
  next
    case False
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `length gs = 2 * k + 3` `j < length gs` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using that goal2 by simp
    next
      case 2
      show ?thesis
      proof (cases "1 < gs ! 1 \<and> gs ! 1 < G^(2*k+2)+2 \<and> gs ! (3+k+jj) < G \<and> enc_nth (gs ! 1) (k+jj) = 1")
        case True
        then have *: "cmdL5 jj gs [.] j = enc_upd (gs ! 1) jj (gs ! (3+k+jj))"
          using 2 cmdL5_at_1[OF False] by simp
        let ?n = "gs ! 1"
        let ?xs = "dec ?n"
        let ?ys = "(dec ?n) [jj:=gs!(3+k+jj)]"
        have "gs ! (3+k+jj) < G"
          using True by simp
        moreover have "\<forall>h\<in>set (dec ?n). h < G"
          using True dec_less_G by auto
        ultimately have "\<forall>h\<in>set ?ys. h < G"
          by (metis in_set_conv_nth length_list_update nth_list_update_eq nth_list_update_neq)
        moreover have "length ?ys = 2 * k + 2"
          using True length_dec by simp
        ultimately have "enc ?ys < G ^ (2 * k + 2) + 2"
          using enc_less by simp
        then show ?thesis
          using * by (simp add: enc_upd_def G'_def)
      next
        case b: False
        then show ?thesis
          using that cmdL5_at_1_else[OF False] 2 by simp
      qed
    next
      case 3
      then show ?thesis
        using that cmdL5_at_2[OF False] by simp
    next
      case 4
      then show ?thesis
        using that cmdL5_at_3[OF False] by simp
    next
      case 5
      then show ?thesis
        using that cmdL5_at_4[OF False] by simp
    qed
  qed
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> [*] (cmdL5 jj gs) \<le> 1"
    using cmdL5_def by (metis (no_types, lifting) One_nat_def fst_conv le_eq_less_or_eq plus_1_eq_Suc trans_le_add2)

qed

definition tmL45 :: "nat \<Rightarrow> machine" where
  "tmL45 jj \<equiv> [cmdL5 jj]"

lemma tmL45_tm:
  assumes "jj < k"
  shows "turing_machine (2 * k + 3) G' (tmL45 jj)"
  using assms G'_ge turing_command_cmdL5 tmL45_def by auto

text \<open>
We move the output tape head one cell to the left.
\<close>

definition "tmL46 jj \<equiv> tmL45 jj ;; tm_left 1"

lemma tmL46_tm:
  assumes "jj < k"
  shows "turing_machine (2 * k + 3) G' (tmL46 jj)"
  using assms G'_ge tm_left_tm tmL45_tm tmL46_def tmL45_def by simp

text \<open>
The next command sweeps left and applies the head movement for tape $jj$ if this
is a movement to the left. To this end it checks for a set head flag in
component $k + jj$ of the code symbol and clears it. It also memorizes that it
just cleared the head flag by changing the symbol on memorization tape $3 + jj$
to the number $3$, which is not used to encode any actual head movement. In the
next step of the sweep it will recognize this $3$ and set the head flag in
component $k + jj$ of the code symbol. The net result is that the head flag for
tape $jj$ has moved one cell to the left.
\<close>

abbreviation is_beginning :: "symbol \<Rightarrow> bool" where
  "is_beginning y \<equiv> is_code y \<and> dec y ! (2 * k + 1) = 1"

definition cmdL7 :: "nat \<Rightarrow> command" where
  "cmdL7 jj rs \<equiv>
 (if is_beginning (rs ! 1) then 1 else 0,
  if rs ! (3 + jj) = \<box> \<and> enc_nth (rs ! 1) (k + jj) = 1 \<and> is_code (rs ! 1) \<and> \<not> is_beginning (rs ! 1) then
   [(rs ! 0, Stay),
    (enc_upd (rs ! 1) (k + jj) 0, Left),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (if j = jj then 3 else rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])
  else if rs ! (3 + jj) = 3 \<and> is_code (rs ! 1) then
   [(rs ! 0, Stay),
    (enc_upd (rs ! 1) (k + jj) 1, Left),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (if j = jj then 0 else rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])
  else
   [(rs ! 0, Stay),
    (rs ! 1, Left),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k]))"

abbreviation "condition7a gs jj \<equiv>
  gs ! (3 + jj) = 0 \<and> enc_nth (gs ! 1) (k + jj) = 1 \<and> is_code (gs ! 1) \<and> \<not> is_beginning (gs ! 1)"
abbreviation "condition7b gs jj \<equiv>
  \<not> condition7a gs jj \<and> gs ! (3 + jj) = 3 \<and> is_code (gs ! 1)"
abbreviation "condition7c gs jj \<equiv>
  \<not> condition7a gs jj \<and> \<not> condition7b gs jj"

lemma turing_command_cmdL7:
  assumes "jj < k"
  shows "turing_command (2 * k + 3) 1 G' (cmdL7 jj)"
proof
  show "length ([!!] cmdL7 jj gs) = length gs" if "length gs = 2 * k + 3" for gs
  proof -
    consider "condition7a gs jj" | "condition7b gs jj" | "condition7c gs jj"
      by blast
    then show ?thesis
      unfolding cmdL7_def using that by (cases) simp_all
  qed
  show goal2: "0 < 2 * k + 3 \<Longrightarrow> cmdL7 jj gs [.] 0 = gs ! 0" if "length gs = 2 * k + 3" for gs
  proof -
    consider "condition7a gs jj" | "condition7b gs jj" | "condition7c gs jj"
      by blast
    then show ?thesis
      unfolding cmdL7_def using that by (cases) simp_all
  qed
  show "cmdL7 jj gs [.] j < G'"
    if gs: "j < length gs" "length gs = 2 * k + 3" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G'"
    for gs j
  proof -
    consider "condition7a gs jj" | "condition7b gs jj" | "condition7c gs jj"
      by blast
    then show ?thesis
    proof (cases)
      case 1
      then have *: "snd (cmdL7 jj gs) =
        [(gs ! 0, Stay),
         (enc_upd (gs ! 1) (k + jj) 0, Left),
         (gs ! 2, Stay)] @
         (map (\<lambda>j. (if j = jj then 3 else gs ! (j + 3), Stay)) [0..<k]) @
         (map (\<lambda>j. (gs ! (3 + k + j), Stay)) [0..<k])"
        unfolding cmdL7_def by simp
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using gs by linarith
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using that by (simp add: goal2)
      next
        case 2
        then have "is_code (gs ! 1)"
          using 1 by blast
        moreover have "k + jj < 2 * k + 2"
          using assms by simp
        moreover have "0 < G"
          using G_ge_4 by simp
        ultimately have "is_code (enc_upd (gs ! 1) (k + jj) 0)"
          using enc_upd_is_code by simp
        then have "is_code (cmdL7 jj gs [.] j)"
          using * 2 by simp
        then show ?thesis
          using G'_ge_G G'_def by simp
      next
        case 3
        then show ?thesis
          using * gs by simp
      next
        case 4
        then show ?thesis
          using * gs G'_ge threeplus2k_2[where ?a="(gs ! 0, Stay)"] by simp
      next
        case 5
        then show ?thesis
          using * gs G'_ge threeplus2k_3[where ?a="(gs ! 0, Stay)"] by simp
      qed
    next
      case case2: 2
      then have *: "snd (cmdL7 jj gs) =
        [(gs ! 0, Stay),
         (enc_upd (gs ! 1) (k + jj) 1, Left),
         (gs ! 2, Stay)] @
         (map (\<lambda>j. (if j = jj then 0 else gs ! (j + 3), Stay)) [0..<k]) @
         (map (\<lambda>j. (gs ! (3 + k + j), Stay)) [0..<k])"
        unfolding cmdL7_def by simp
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using gs by linarith
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using that by (simp add: goal2)
      next
        case 2
        then have "is_code (gs ! 1)"
          using case2 by simp
        moreover have "k + jj < 2 * k + 2"
          using assms by simp
        moreover have "1 < G"
          using G_ge_4 by simp
        ultimately have "is_code (enc_upd (gs ! 1) (k + jj) 1)"
          using enc_upd_is_code by simp
        then have "is_code (cmdL7 jj gs [.] j)"
          using * 2 by simp
        then show ?thesis
          using G'_ge_G G'_def by simp
      next
        case 3
        then show ?thesis
          using * gs by simp
      next
        case 4
        then show ?thesis
          using * gs G'_ge threeplus2k_2[where ?a="(gs ! 0, Stay)"] by simp
      next
        case 5
        then show ?thesis
          using * gs G'_ge threeplus2k_3[where ?a="(gs ! 0, Stay)"] by simp
      qed
    next
      case case3: 3
      then have *: "snd (cmdL7 jj gs) =
        [(gs ! 0, Stay),
         (gs ! 1, Left),
         (gs ! 2, Stay)] @
         (map (\<lambda>j. (gs ! (j + 3), Stay)) [0..<k]) @
         (map (\<lambda>j. (gs ! (3 + k + j), Stay)) [0..<k])"
        unfolding cmdL7_def by auto
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using gs by linarith
      then show ?thesis
        using * gs G'_ge threeplus2k_2[where ?a="(gs ! 0, Stay)"] threeplus2k_3[where ?a="(gs ! 0, Stay)"]
        by (cases) simp_all
    qed
  qed
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> [*] (cmdL7 jj gs) \<le> 1"
    using cmdL7_def by simp
qed

definition tmL67 :: "nat \<Rightarrow> machine" where
  "tmL67 jj \<equiv> [cmdL7 jj]"

lemma tmL67_tm:
  assumes "jj < k"
  shows "turing_machine (2 * k + 3) G' (tmL67 jj)"
  using assms G'_ge tmL67_def turing_command_cmdL7 by auto

definition "tmL47 jj \<equiv> tmL46 jj ;; tmL67 jj"

lemma tmL47_tm:
  assumes "jj < k"
  shows "turing_machine (2 * k + 3) G' (tmL47 jj)"
  using assms G'_ge tm_left_tm tmL46_tm tmL47_def tmL67_tm by simp

text \<open>
Next we are sweeping right again and perform the head movement for tape $jj$
if this is a movement to the right. This works the same as the left movements
in @{const cmdL7}.
\<close>

definition cmdL8 :: "nat \<Rightarrow> command" where
  "cmdL8 jj rs \<equiv>
 (if rs ! 1 = \<box> then 1 else 0,
  if rs ! (3 + jj) = 2 \<and> enc_nth (rs ! 1) (k + jj) = 1 \<and> is_code (rs ! 1) then
   [(rs ! 0, Stay),
    (enc_upd (rs ! 1) (k + jj) 0, Right),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (if j = jj then 3 else rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])
  else if rs ! (3 + jj) = 3 \<and> is_code (rs ! 1) then
   [(rs ! 0, Stay),
    (enc_upd (rs ! 1) (k + jj) 1, Right),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (if j = jj then 2 else rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])
  else if rs ! 1 = 0 then
   [(rs ! 0, Stay),
    (rs ! 1, Stay),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])
  else
   [(rs ! 0, Stay),
    (rs ! 1, Right),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k]))"

abbreviation "condition8a gs jj \<equiv>
  gs ! (3 + jj) = 2 \<and> enc_nth (gs ! 1) (k + jj) = 1 \<and> is_code (gs ! 1)"
abbreviation "condition8b gs jj \<equiv>
  \<not> condition8a gs jj \<and> gs ! (3 + jj) = 3 \<and> is_code (gs ! 1)"
abbreviation "condition8c gs jj \<equiv>
  \<not> condition8a gs jj \<and> \<not> condition8b gs jj \<and> gs ! 1 = 0"
abbreviation "condition8d gs jj \<equiv>
  \<not> condition8a gs jj \<and> \<not> condition8b gs jj \<and> \<not> condition8c gs jj"

lemma turing_command_cmdL8:
  assumes "jj < k"
  shows "turing_command (2 * k + 3) 1 G' (cmdL8 jj)"
proof
  show "length ([!!] cmdL8 jj gs) = length gs" if "length gs = 2 * k + 3" for gs
  proof -
    consider "condition8a gs jj" | "condition8b gs jj" | "condition8c gs jj" | "condition8d gs jj"
      by blast
    then show ?thesis
      unfolding cmdL8_def using that by (cases) simp_all
  qed
  show goal2: "0 < 2 * k + 3 \<Longrightarrow> cmdL8 jj gs [.] 0 = gs ! 0" if "length gs = 2 * k + 3" for gs
  proof -
    consider "condition8a gs jj" | "condition8b gs jj" | "condition8c gs jj" | "condition8d gs jj"
      by blast
    then show ?thesis
      unfolding cmdL8_def using that by (cases) simp_all
  qed
  show "cmdL8 jj gs [.] j < G'"
    if gs: "j < length gs" "length gs = 2 * k + 3" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G'"
    for gs j
  proof -
    consider "condition8a gs jj" | "condition8b gs jj" | "condition8c gs jj" | "condition8d gs jj"
      by blast
    then show ?thesis
    proof (cases)
      case 1
      then have *: "snd (cmdL8 jj gs) =
        [(gs ! 0, Stay),
         (enc_upd (gs ! 1) (k + jj) 0, Right),
         (gs ! 2, Stay)] @
         (map (\<lambda>j. (if j = jj then 3 else gs ! (j + 3), Stay)) [0..<k]) @
         (map (\<lambda>j. (gs ! (3 + k + j), Stay)) [0..<k])"
        unfolding cmdL8_def by simp
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using gs by linarith
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using that by (simp add: goal2)
      next
        case 2
        then have "is_code (gs ! 1)"
          using 1 by blast
        moreover have "k + jj < 2 * k + 2"
          using assms by simp
        moreover have "0 < G"
          using G_ge_4 by simp
        ultimately have "is_code (enc_upd (gs ! 1) (k + jj) 0)"
          using enc_upd_is_code by simp
        then have "is_code (cmdL8 jj gs [.] j)"
          using * 2 by simp
        then show ?thesis
          using G'_ge_G G'_def by simp
      next
        case 3
        then show ?thesis
          using * gs by simp
      next
        case 4
        then show ?thesis
          using * gs G'_ge threeplus2k_2[where ?a="(gs ! 0, Stay)"] by simp
      next
        case 5
        then show ?thesis
          using * gs G'_ge threeplus2k_3[where ?a="(gs ! 0, Stay)"] by simp
      qed
    next
      case case2: 2
      then have *: "snd (cmdL8 jj gs) =
        [(gs ! 0, Stay),
         (enc_upd (gs ! 1) (k + jj) 1, Right),
         (gs ! 2, Stay)] @
         (map (\<lambda>j. (if j = jj then 2 else gs ! (j + 3), Stay)) [0..<k]) @
         (map (\<lambda>j. (gs ! (3 + k + j), Stay)) [0..<k])"
        unfolding cmdL8_def by simp
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using gs by linarith
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using that by (simp add: goal2)
      next
        case 2
        then have "is_code (gs ! 1)"
          using case2 by simp
        moreover have "k + jj < 2 * k + 2"
          using assms by simp
        moreover have "1 < G"
          using G_ge_4 by simp
        ultimately have "is_code (enc_upd (gs ! 1) (k + jj) 1)"
          using enc_upd_is_code by simp
        then have "is_code (cmdL8 jj gs [.] j)"
          using * 2 by simp
        then show ?thesis
          using G'_ge_G G'_def by simp
      next
        case 3
        then show ?thesis
          using * gs by simp
      next
        case 4
        then show ?thesis
          using * gs G'_ge threeplus2k_2[where ?a="(gs ! 0, Stay)"] by simp
      next
        case 5
        then show ?thesis
          using * gs G'_ge threeplus2k_3[where ?a="(gs ! 0, Stay)"] by simp
      qed
    next
      case 3
      then have *: "snd (cmdL8 jj gs) =
        [(gs ! 0, Stay),
         (gs ! 1, Stay),
         (gs ! 2, Stay)] @
         (map (\<lambda>j. (gs ! (j + 3), Stay)) [0..<k]) @
         (map (\<lambda>j. (gs ! (3 + k + j), Stay)) [0..<k])"
        unfolding cmdL8_def by auto
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using gs by linarith
      then show ?thesis
        using * gs G'_ge threeplus2k_2[where ?a="(gs ! 0, Stay)"] threeplus2k_3[where ?a="(gs ! 0, Stay)"]
        by (cases) simp_all
    next
      case 4
      then have *: "snd (cmdL8 jj gs) =
        [(gs ! 0, Stay),
         (gs ! 1, Right),
         (gs ! 2, Stay)] @
         (map (\<lambda>j. (gs ! (j + 3), Stay)) [0..<k]) @
         (map (\<lambda>j. (gs ! (3 + k + j), Stay)) [0..<k])"
        unfolding cmdL8_def by auto
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using gs by linarith
      then show ?thesis
        using * gs G'_ge threeplus2k_2[where ?a="(gs ! 0, Stay)"] threeplus2k_3[where ?a="(gs ! 0, Stay)"]
        by (cases) simp_all
    qed
  qed
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> [*] (cmdL8 jj gs) \<le> 1"
    using cmdL8_def by simp
qed

definition tmL78 :: "nat \<Rightarrow> machine" where
  "tmL78 jj \<equiv> [cmdL8 jj]"

lemma tmL78_tm:
  assumes "jj < k"
  shows "turing_machine (2 * k + 3) G' (tmL78 jj)"
  using assms G'_ge tmL78_def turing_command_cmdL8 by auto

definition "tmL48 jj \<equiv> tmL47 jj ;; tmL78 jj"

lemma tmL48_tm:
  assumes "jj < k"
  shows "turing_machine (2 * k + 3) G' (tmL48 jj)"
  using assms G'_ge tm_left_tm tmL47_tm tmL48_def tmL78_tm by simp

text \<open>
The last command in the command sequence is moving back to the beginning of the
output tape.
\<close>

definition "tmL49 jj \<equiv> tmL48 jj ;; tm_left_until1"

text \<open>
The Turing machine @{term "tmL49 jj"} is then repeated for the parameters $jj =
0, \dots, k - 1$ in order to simulate the actions of $M$ on all tapes.
\<close>

lemma tmL49_tm: "jj < k \<Longrightarrow> turing_machine (2 * k + 3) G' (tmL49 jj)"
  using tmL48_tm tmL49_def tmL1_def tm_left_until1_tm by simp

fun tmL49_upt :: "nat \<Rightarrow> machine" where
  "tmL49_upt 0 = []" |
  "tmL49_upt (Suc j) = tmL49_upt j ;; tmL49 j"

lemma tmL49_upt_tm:
  assumes "j \<le> k"
  shows "turing_machine (2 * k + 3) G' (tmL49_upt j)"
  using assms
proof (induction j)
  case 0
  then show ?case
    using G'_ge(1) turing_machine_def by simp
next
  case (Suc j)
  then show ?case
    using assms tmL49_tm by simp
qed

definition "tmL9 \<equiv> tmL4 ;; tmL49_upt k"

lemma tmL9_tm: "turing_machine (2 * k + 3) G' tmL9"
  unfolding tmL9_def using tmL49_upt_tm tmL4_tm by simp

text \<open>
At this point in the iteration we have completed one more step in the execution
of $M$. We mark this be setting one more counter flag, namely the one in the
leftmost code symbol where the flag is still unset. To find the first unset
counter flag, we reuse @{term tmC}.
\<close>

definition "tmL10 \<equiv> tmL9 ;; tmC"

lemma tmL10_tm: "turing_machine (2 * k + 3) G' tmL10"
  unfolding tmL10_def using tmL9_tm tmC_tm by simp

text \<open>
Then we set the counter flag, unless we have reached a blank symbol.
\<close>

definition cmdL11 :: command where
  "cmdL11 rs \<equiv>
   (1,
    [(rs ! 0, Stay),
     if is_code (rs ! 1) then (enc_upd (rs ! 1) (2 * k) 1, Stay) else (rs ! 1, Stay),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k]))"

lemma turing_command_cmdL11: "turing_command (2 * k + 3) 1 G' cmdL11"
proof
  show "length gs = 2 * k + 3 \<Longrightarrow> length ([!!] cmdL11 gs) = length gs" for gs
    unfolding cmdL11_def by (cases "gs ! 1 = 0") simp_all
  show goal2: "length gs = 2 * k + 3 \<Longrightarrow> 0 < 2 * k + 3 \<Longrightarrow> cmdL11 gs [.] 0 = gs ! 0" for gs
    unfolding cmdL11_def by (cases "gs ! 1 = 0") simp_all
  show "cmdL11 gs [.] j < G'"
    if "length gs = 2 * k + 3" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G'" "j < length gs"
    for gs j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `length gs = 2 * k + 3` `j < length gs` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using that goal2 by simp
    next
      case 2
      show ?thesis
      proof (cases "is_code (gs ! 1)")
        case True
        then have *: "cmdL11 gs [.] j = enc_upd (gs ! 1) (2 * k) 1"
          using 2 cmdL11_def by simp
        then have "is_code (cmdL11 gs [.] j)"
          using enc_upd_is_code[OF True] G_ge_4 by simp
        then show ?thesis
          using G'_def by simp
      next
        case False
        then show ?thesis
          using that cmdL11_def 2 by auto
      qed
    next
      case 3
      then show ?thesis
        using that cmdL11_def by simp
    next
      case 4
      then show ?thesis
        using that cmdL11_def threeplus2k_2[OF 4, of "(gs ! 0, Stay)"] by simp
    next
      case 5
      then show ?thesis
        using that cmdL11_def threeplus2k_3[OF 5, of "(gs ! 0, Stay)"] by simp
    qed
  qed
  show "\<And>gs. length gs = 2 * k + 3 \<Longrightarrow> [*] (cmdL11 gs) \<le> 1"
    using cmdL11_def by simp
qed

definition "tmL11 \<equiv> tmL10 ;; [cmdL11] "

lemma tmL1011_tm: "turing_machine (2 * k + 3) G' [cmdL11]"
  using cmdL11_def turing_command_cmdL11 G'_ge by auto

lemma tmL11_tm: "turing_machine (2 * k + 3) G' tmL11"
  using tmL11_def tmL1011_tm G'_ge tmL10_tm by simp

text \<open>
And we move back to the beginning of the output tape again.
\<close>

definition "tmL12 \<equiv> tmL11 ;; tm_left_until1"

lemma tmL12_tm: "turing_machine (2 * k + 3) G' tmL12"
  using tmL11_tm tmL12_def tm_left_until1_tm by simp

text \<open>
Now, at the end of the iteration we set the memorization tapes $3, \dots, 2k+2$,
that is, all but the one memorizing the state of $M$, to $0$. This makes for a
simpler loop invariant than having the leftover symbols there.
\<close>

definition "tmL13 \<equiv> tmL12 ;; tm_write_many {3..<2 * k + 3} 0"

lemma tmL13_tm: "turing_machine (2 * k + 3) G' tmL13"
  unfolding tmL13_def using tmL12_tm tm_write_many_tm k_ge_2 G'_ge(1) by simp

text \<open>
This is the entire loop. It terminates once there are no unset counter flags
anymore.
\<close>

definition "tmLoop \<equiv> WHILE tmC ; \<lambda>rs. rs ! 1 > \<box> DO tmL13 DONE"

lemma tmLoop_tm: "turing_machine (2 * k + 3) G' tmLoop"
  using tmLoop_def turing_machine_loop_turing_machine tmC_tm tmL13_tm by simp

definition "tm10 \<equiv> tm9 ;; tmLoop"

lemma tm10_tm: "turing_machine (2 * k + 3) G' tm10"
  using tm10_def tmLoop_tm tm9_tm by simp


subsubsection \<open>Cleaning up the output\<close>

text \<open>
Now the simulation proper has ended, but the output tape does not yet look quite
like the output tape of $M$. It remains to extract the component~$1$ from all
the code symbols on the output tape. The simulator does this while sweeping left.
Formally, ``extracting component~1'' means this:
\<close>

abbreviation ec1 :: "symbol \<Rightarrow> symbol" where
  "ec1 h \<equiv> if is_code h then enc_nth h 1 else \<box>"

lemma ec1: "ec1 h < G'" if "h < G'" for h
proof (cases "is_code h")
  case True
  then show ?thesis
    using enc_nth_less G'_ge_G by fastforce
next
  case False
  then show ?thesis
    using that by auto
qed

definition "tm11 \<equiv> tm10 ;; tm_ltrans_until 1 1 StartSym ec1"

lemma tm11_tm: "turing_machine (2 * k + 3) G' tm11"
proof -
  have "turing_machine (2 * k + 3) G' (tm_ltrans_until 1 1 StartSym ec1)"
    using G'_ge ec1 by (intro tm_ltrans_until_tm) simp_all
  then show ?thesis
    using tm10_tm tm11_def by simp
qed

text \<open>
The previous TM, @{term "tm_ltrans_until 1 1 StartSym ec1"}, halts as soon as it
encounters a code symbol with the start flag set, without applying the
extraction function. Applying the function to this final code symbol, which is
at the leftmost cell of the tape, is the last step of the simulator machine.
\<close>

definition "tm12 \<equiv> tm11 ;; tm_rtrans 1 ec1"

lemma tm12_tm: "turing_machine (2 * k + 3) G' tm12"
  unfolding tm12_def using tm_rtrans_tm tm11_tm ec1 G'_ge by simp


subsection \<open>Semantics of the Turing machine\<close>

text \<open>
This section establishes not only the configurations of the simulator but also
the traces. For every Turing machine and command defined in the previous
subsection, there will be a corresponding trace and a tape list representing the
simulator's configuration after the command or TM has been applied.
\<close>

text \<open>
For most of the time, the simulator's output tape will have no start symbol, and
so the next definition will be more suited to describing it than the customary
@{const contents}.
\<close>

definition contents' :: "symbol list \<Rightarrow> (nat \<Rightarrow> symbol)" where
  "contents' ys x \<equiv> if x < length ys then ys ! x else 0"

lemma contents'_eqI:
  assumes "\<And>x. x < length ys \<Longrightarrow> zs x = ys ! x"
    and "\<And>x. x \<ge> length ys \<Longrightarrow> zs x = 0"
  shows "zs = contents' ys"
  using contents'_def assms by auto

lemma contents_contents': "\<lfloor>ys\<rfloor> = contents' (1 # ys)"
  using contents_def contents'_def by auto

lemma contents'_at_ge:
  assumes "i \<ge> length ys"
  shows "contents' ys i = 0"
  using assms contents'_def by simp

text \<open>
In the following context @{term zs} represents the input for $M$ and hence for
the simulator.
\<close>

context
  fixes zs :: "symbol list"
  assumes zs: "bit_symbols zs"
begin

lemma zs_less_G: "\<forall>i<length zs. zs ! i < G"
  using zs G_ge_4 by auto

lemma zs_proper: "proper_symbols zs"
  using zs by auto

abbreviation "n \<equiv> length zs"

abbreviation "TT \<equiv> Suc (fmt n)"


subsubsection \<open>Initializing the simulator's tapes\<close>

definition tps0 :: "tape list" where
  "tps0 \<equiv>
    [(\<lfloor>zs\<rfloor>, 0),
     (\<lfloor>[]\<rfloor>, 0)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

lemma tps0_start_config: "start_config (2 * k + 3) zs = (0, tps0)"
  unfolding tps0_def contents_def onesie_def start_config_def by auto

definition tps1 :: "tape list" where
  "tps1 \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lfloor>replicate (fmt n) 3\<rfloor>, 1)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

definition "es1 \<equiv> es_fmt n"

lemma tm1: "traces tm1 tps0 es1 tps1"
proof -
  let ?tps = "replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"
  have 1: "tps0 = start_tapes_2 zs @ ?tps"
    using contents_def tps0_def start_tapes_2_def by auto
  have 2: "tps1 = one_tapes_2 zs (fmt n) @ ?tps"
    using contents_def tps1_def one_tapes_2_def by simp
  have "length (start_tapes_2 zs) = 2"
    using start_tapes_2_def by simp
  moreover have "traces tm_fmt (start_tapes_2 zs) (es_fmt n) (one_tapes_2 zs (fmt n))"
    using fmt zs by fastforce
  moreover have "turing_machine 2 G' tm_fmt" using fmt(1) .
  ultimately have
    "traces (append_tapes 2 (2 + length ?tps) tm_fmt) (start_tapes_2 zs @ ?tps) (es_fmt n) (one_tapes_2 zs (fmt n) @ ?tps)"
    using traces_append_tapes by blast
  then have
    "traces (append_tapes 2 (2 * k + 3) tm_fmt) (start_tapes_2 zs @ ?tps) (es_fmt n) (one_tapes_2 zs (fmt n) @ ?tps)"
    by (simp add: numeral_3_eq_3)
  then have "traces (append_tapes 2 (2 * k + 3) tm_fmt) tps0 (es_fmt n) tps1"
    using 1 2 by simp
  then show ?thesis
    using tm1_def es1_def by simp
qed

definition "es1_2 \<equiv> map (\<lambda>i. (1, 1 + Suc i)) [0..<fmt n] @ [(1, 1 + fmt n)]"

definition "es2 \<equiv> es1 @ es1_2"

lemma len_es2: "length es2 = length (es_fmt n) + TT"
  using es2_def es1_def by (simp add: es1_2_def)

definition tps2 :: "tape list" where
  "tps2 \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lfloor>replicate (fmt n) (enc (replicate k 0 @ replicate k 0 @ [0, 0]))\<rfloor>, TT)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

lemma tm2: "traces tm2 tps0 es2 tps2"
  unfolding tm2_def es2_def
proof (rule traces_sequential)
  show "traces tm1 tps0 es1 tps1" using tm1 .
  show "traces tm1_2 tps1 es1_2 tps2"
    unfolding tm1_2_def es1_2_def
  proof (rule traces_tm_const_until_11I[where ?n="fmt n" and ?G=G'])
    show "1 < length tps1"
      using tps1_def by simp
    show "enc (replicate k 0 @ replicate k 0 @ [0, 0]) < G'"
      using G_ge_4 by (intro enc_less_G') simp_all
    show "rneigh (tps1 ! 1) {0} (fmt n)"
      using tps1_def contents_def by (intro rneighI) simp_all
    show "map (\<lambda>i. (1, 1 + Suc i)) [0..<fmt n] @ [(1, 1 + fmt n)] =
        map (\<lambda>i. (tps1 :#: 0, tps1 :#: 1 + Suc i)) [0..<fmt n] @ [(tps1 :#: 0, tps1 :#: 1 + fmt n)]"
      using tps1_def contents_def by simp
    show "tps2 =
        tps1 [1 := constplant (tps1 ! 1) (enc (replicate k 0 @ replicate k 0 @ [0, 0])) (fmt n)]"
      using tps2_def tps1_def contents_def constplant by auto
  qed
qed

definition "es3 \<equiv> es2 @ map (\<lambda>i. (1, i)) (rev [0..<TT]) @ [(1, 0)]"

definition tps3 :: "tape list" where
  "tps3 \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lfloor>replicate (fmt n) (enc (replicate k 0 @ replicate k 0 @ [0, 0]))\<rfloor>, 0)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

lemma tm3: "traces tm3 tps0 es3 tps3"
  unfolding tm3_def es3_def
proof (rule traces_sequential)
  show "traces tm2 tps0 es2 tps2" using tm2 .
  show "traces (tm_start 1) tps2 (map (\<lambda>i. (1, i)) (rev [0..<TT]) @ [(1, 0)]) tps3"
    using tps3_def tps2_def enc_greater by (intro traces_tm_start_1I) simp_all
qed

definition "es4 \<equiv> es3 @ [(1, 0)]"

lemma len_es4: "length es4 = length (es_fmt n) + 2 * TT + 2"
  using es4_def es3_def len_es2 by simp

definition tps4 :: "tape list" where
  "tps4 \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (contents'
       ((enc (replicate k 1 @ replicate k 1 @ [0, 1])) #
        replicate (fmt n) (enc (replicate k 0 @ replicate k 0 @ [0, 0]))), 0)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

lemma tm4: "traces tm4 tps0 es4 tps4"
  unfolding tm4_def es4_def
proof (rule traces_sequential)
  show "traces tm3 tps0 es3 tps3" using tm3 .
  show "traces (tm_write 1 (enc (replicate k 1 @ replicate k 1 @ [0, 1]))) tps3 [(1, 0)] tps4"
  proof (rule traces_tm_write_1I)
    show "1 < length tps3"
      using tps3_def by simp
    show "[(1, 0)] = [(tps3 :#: 0, tps3 :#: 1)]"
      using tps3_def by simp
    show "tps4 = tps3[1 := tps3 ! 1 |:=| enc (replicate k 1 @ replicate k 1 @ [0, 1])]"
      using tps3_def tps4_def contents'_def contents_contents' by auto
  qed
qed

definition "es5 \<equiv> es4 @ [(1, 1)]"

lemma len_es5: "length es5 = length (es_fmt n) + 2 * TT + 3"
  using es5_def len_es4 by simp

definition tps5 :: "tape list" where
  "tps5 \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (contents'
       ((enc (replicate k 1 @ replicate k 1 @ [0, 1])) #
        replicate (fmt n) (enc (replicate k 0 @ replicate k 0 @ [0, 0]))), 1)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

lemma tm5: "traces tm5 tps0 es5 tps5"
  unfolding tm5_def es5_def
proof (rule traces_sequential)
  show "traces tm4 tps0 es4 tps4"
    using tm4 .
  show "traces (tm_right 1) tps4 [(1, 1)] tps5"
    using tps4_def tps5_def by (intro traces_tm_right_1I) simp_all
qed

text \<open>
Since the simulator simulates $M$ on @{term zs}, its tape contents are typically
described in terms of configurations of $M$. So the following definition
is actually more like an abbreviation.
\<close>

definition "exec t \<equiv> execute M (start_config k zs) t"

lemma exec_pos_less_TT:
  assumes "j < k"
  shows "exec t <#> j < TT"
proof -
  have "exec t <#> j \<le> T' n"
    using head_pos_le_time_bound[OF tm_M time_bound_T' zs assms] exec_def by simp
  then show ?thesis
    by (meson fmt(4) le_imp_less_Suc le_trans)
qed

lemma tps_ge_TT_0:
  assumes "i \<ge> TT"
  shows "(exec t <:> 1) i = 0"
proof (induction t)
  case 0
  have "exec 0 = start_config k zs"
    using exec_def by simp
  then show ?case
    using start_config1 assms tm_M turing_machine_def by simp
next
  case (Suc t)
  have *: "exec (Suc t) = exe M (exec t)"
    using exec_def by simp
  show ?case
  proof (cases "fst (exec t) \<ge> length M")
    case True
    then have "exec (Suc t) = exec t"
      using * exe_def by simp
    then show ?thesis
      using Suc by simp
  next
    case False
    then have "exec (Suc t) <:> 1 = sem (M ! (fst (exec t))) (exec t) <:> 1"
        (is "_ = sem ?cmd ?cfg <:> 1")
      using exe_lt_length * by simp
    also have "... = fst (map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd (read (snd ?cfg)))) (snd ?cfg)) ! 1)"
      using sem' by simp
    also have "... = fst (act (snd (?cmd (read (snd ?cfg))) ! 1) (snd ?cfg ! 1))"
      (is "_ = fst (act ?h (snd ?cfg ! 1))")
    proof -
      have "||?cfg|| = k"
        using exec_def tm_M execute_num_tapes[OF tm_M] start_config_length turing_machine_def
        by simp
      moreover from this have "length (snd (?cmd (read (snd ?cfg)))) = k"
        by (metis False turing_commandD(1) linorder_not_less read_length tm_M turing_machineD(3))
      moreover have "k > 1"
         using k_ge_2 by simp
      ultimately show ?thesis
        by simp
    qed
    finally have "exec (Suc t) <:> 1 = fst (act ?h (?cfg <!> 1))" .
    moreover have "i \<noteq> snd (?cfg <!> 1)"
      using assms by (metis Suc_1 exec_pos_less_TT lessI less_irrefl less_le_trans tm_M turing_machine_def)
    ultimately have "(exec (Suc t) <:> 1) i = fst (?cfg <!> 1) i"
      using act_changes_at_most_pos by (metis prod.collapse)
    then show ?thesis
      using Suc.IH by simp
  qed
qed

text \<open>
The next definition is central to how we describe the simulator's output tape.
The basic idea is that it describes the tape during the simulation of the $t$-th
step of executing $M$ on input @{term zs}. Recall that $TT$ is the length of the
formatted part on the simulator's output tape. The $i$-th cell of the output
tape contains: (1) $k$ symbols corresponding to the symbols in the $i$-th cell
of the $k$ tapes of $M$ after $t$ steps; (2) $k$ flags indicating which of the
$k$ tape heads is in position $i$; (3) a unary counter representing the number
$t$; (4) a flag indicating whether $i = 0$. This is the situation at the
beginning of the $t$-iteration of the simulator's main loop. During this
iteration the tape changes slightly: some symbols and head positions may already
represent the situation after $t+1$ steps of $M$, that is, the $t$-th step has
been partially simulated already.

To account for this, there is the @{term xs} parameter. It is meant to be set to
a list of $k$ pairs. Let the $j$-th element of this list be $(a, b)$.  on $M$'s
tape $j$ has already been simulated. In other words, the output tape reflects
the situation after $t + a$ steps. Likewise $b$ will be either None or 0 or 1.
If it is 0 or 1, it means the flag represents the head position of tape $j$
after $t + b$ steps. If it is None, it means that all head flags for tape $k$
are currently zero, representing a ``tape without head''.  This situation occurs
every time the simulator has cleared the head flag representing the position
after $t$ steps, bus has not set the flag for the head position after $t+1$
steps yet.

Therefore, at the beginning of the $t$-t iteration of the simulator's loop
@{term xs} consists of $k$ pairs $(0, 0)$. During the iteration every pair will
eventually become $(0, 0)$.
\<close>

definition zip_cont :: "nat \<Rightarrow> (nat \<times> nat option) list \<Rightarrow> (nat \<Rightarrow> symbol)" where
  "zip_cont t xs i \<equiv>
    if i < TT then enc
     (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])
    else 0"

text \<open>
Some auxiliary lemmas for accessing elements of lists of certain shape:
\<close>

lemma less_k_nth: "j < k \<Longrightarrow> (map f1 [0..<k] @ map f2 [0..<k] @ [a, b]) ! j = f1 j"
  by (simp add: nth_append)

lemma less_2k_nth: "k \<le> j \<Longrightarrow> j < 2 * k \<Longrightarrow> (map f1 [0..<k] @ map f2 [0..<k] @ [a, b]) ! j = f2 (j - k)"
proof -
  assume a: "k \<le> j" "j < 2 * k"
  have b: "(map f1 [0..<k] @ map f2 [0..<k]) ! (k + l) = f2 l" if "l < k" for l
    by (simp add: nth_append that)
  have "(map f1 [0..<k] @ map f2 [0..<k]) ! j = f2 (j - k)"
  proof -
    obtain l where l: "l < k" "k + l = j"
      using a le_Suc_ex by auto
    then have "(map f1 [0..<k] @ map f2 [0..<k]) ! (k + l) = f2 l"
      using b by auto
    with l show ?thesis
      by auto
  qed
  moreover have "(map f1 [0..<k] @ map f2 [0..<k] @ [a, b]) = (map f1 [0..<k] @ map f2 [0..<k]) @ [a, b]"
    by simp
  moreover have "length (map f1 [0..<k] @ map f2 [0..<k]) = 2 * k"
    by simp
  ultimately show ?thesis
    using a by (metis nth_append)
qed

lemma twok_nth: "(map f1 [0..<k] @ map f2 [0..<k] @ [a, b]) ! (2 * k) = a"
proof -
  have "map f1 [0..<k] @ map f2 [0..<k] @ [a, b] = (map f1 [0..<k] @ map f2 [0..<k]) @ [a, b]"
    by simp
  moreover have "length (map f1 [0..<k] @ map f2 [0..<k]) = 2 * k"
    by simp
  ultimately show ?thesis
    by (metis nth_append_length)
qed

lemma twok1_nth: "(map f1 [0..<k] @ map f2 [0..<k] @ [a, b]) ! (2 * k + 1) = b"
proof -
  have "map f1 [0..<k] @ map f2 [0..<k] @ [a, b] = (map f1 [0..<k] @ map f2 [0..<k]) @ [a, b]"
    by simp
  moreover have "length (map f1 [0..<k] @ map f2 [0..<k]) = 2 * k"
    by simp
  ultimately show ?thesis
    by (metis One_nat_def nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
qed

lemma zip_cont_less_G:
  assumes "i < TT"
  shows "\<forall>x\<in>set (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0]). x < G"
    (is "\<forall>x\<in>set(?us @ ?vs @ [?a, ?b]). x < G")
proof -
  let ?ys = "?us @ ?vs @ [?a, ?b]"
  let ?f1 = "(\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i)"
  let ?f2 = "(\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0)"
  have "?ys ! j < G" if "j < 2 * k + 2" for j
  proof -
    consider "j < k" | "k \<le> j \<and> j < 2 * k" | "j = 2 * k" | "j = 2 * k + 1"
      using `j < 2 * k + 2` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "?us ! j = (execute M (start_config k zs) (t + fst (xs ! j)) <:> j) i"
        using exec_def by simp
      then show ?thesis
        using tape_alphabet[OF tm_M] zs_less_G by (simp add: "1" nth_append)
    next
      case 2
      then have "?ys ! j = (case snd (xs ! (j-k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j-k) then 1 else 0)"
        by (simp add: less_2k_nth)
      then have "?ys ! j \<le> 1"
        by (cases "snd (xs ! (j - k))") auto
      then show ?thesis
        using G_ge_4 by simp
    next
      case 3
      then have "?ys ! j \<le> 1"
        by (simp add: twok_nth)
      then show ?thesis
        using G_ge_4 by simp
    next
      case 4
      then have "?ys ! j = (if i = 0 then 1 else 0)"
        using twok1_nth[of ?f1 ?f2 ?a ?b] by simp
      then show ?thesis
        using G_ge_4 by simp
    qed
  qed
  moreover have "length ?ys = 2 * k + 2"
    by simp
  ultimately show "\<forall>x\<in>set ?ys. x < G"
    by (metis (no_types, lifting) in_set_conv_nth)
qed

lemma dec_zip_cont:
  assumes "i < TT"
  shows "dec (zip_cont t xs i) =
     (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])"
    (is "_ = ?ys")
proof -
  have "\<forall>x\<in>set ?ys. x < G"
    using zip_cont_less_G[OF assms] by simp
  moreover have len: "length ?ys = 2 * k + 2"
    by simp
  ultimately have "dec (enc ?ys) = ?ys"
    using dec_enc by simp
  then show ?thesis
    using zip_cont_def assms by simp
qed

lemma zip_cont_gt_1:
  assumes "i < TT"
  shows "zip_cont t xs i > 1"
  using assms enc_greater zip_cont_def by simp

lemma zip_cont_less:
  assumes "i < TT"
  shows "zip_cont t xs i < G ^ (2 * k + 2) + 2"
  using assms enc_less zip_cont_less_G zip_cont_def by simp

lemma zip_cont_eq_0:
  assumes "i \<ge> TT"
  shows "zip_cont t xs i = 0"
  using assms zip_cont_def by simp

lemma dec_zip_cont_less_k:
  assumes "i < TT" and "j < k"
  shows "dec (zip_cont t xs i) ! j = (exec (t + fst (xs ! j)) <:> j) i"
  using dec_zip_cont[OF assms(1)] using assms(2) less_k_nth by (simp add: less_k_nth)

lemma dec_zip_cont_less_2k:
  assumes "i < TT" and "j \<ge> k" and "j < 2 * k"
  shows "dec (zip_cont t xs i) ! j =
    (case snd (xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
  using dec_zip_cont[OF assms(1)] assms(2,3) by (simp add: less_2k_nth)

lemma dec_zip_cont_2k:
  assumes "i < TT"
  shows "dec (zip_cont t xs i) ! (2 * k) = (if i < t then 1 else 0)"
  using dec_zip_cont[OF assms(1)] by (simp add: twok_nth)

lemma dec_zip_cont_2k1:
  assumes "i < TT"
  shows "dec (zip_cont t xs i) ! (2 * k + 1) = (if i = 0 then 1 else 0)"
  using dec_zip_cont[OF assms(1)] twok1_nth by force

lemma zip_cont_eqI:
  assumes "i < TT"
    and "\<And>j. j < k \<Longrightarrow> (exec (t + fst (xs ! j)) <:> j) i = (exec (t + fst (xs' ! j)) <:> j) i"
    and "\<And>j. j < k \<Longrightarrow>
      (case snd (xs ! j) of None \<Rightarrow> (0::nat) | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) =
      (case snd (xs' ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0)"
  shows "zip_cont t xs i = zip_cont t xs' i"
proof -
  have *: "map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> (0::nat) | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] =
      map (\<lambda>j. case snd (xs' ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k]"
    using assms(3) by simp
  have "zip_cont t xs i = enc
     (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])"
    using assms zip_cont_def by simp
  also have "... = enc
     (map (\<lambda>j. (exec (t + fst (xs' ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])"
    using assms(2) by (smt atLeastLessThan_iff map_eq_conv set_upt)
  also have "... = enc
     (map (\<lambda>j. (exec (t + fst (xs' ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (xs' ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])"
    using * by metis
  finally show ?thesis
    using zip_cont_def by auto
qed

lemma zip_cont_nth_eqI:
  assumes "i < TT"
    and "\<And>j. j < k \<Longrightarrow> (exec (t + fst (xs ! j)) <:> j) i = (exec (t + fst (xs' ! j)) <:> j) i"
    and "\<And>j. j < k \<Longrightarrow> snd (xs ! j) = snd (xs' ! j)"
  shows "zip_cont t xs i = zip_cont t xs' i"
  using assms zip_cont_eqI by presburger

lemma begin_tape_zip_cont:
  "begin_tape {y. y < G ^ (2 * k + 2) + 2 \<and> 1 < y \<and> dec y ! (2 * k + 1) = 1} (zip_cont t xs, i)"
    (is "begin_tape ?ys _")
proof -
  let ?y = "zip_cont t xs 0"
  have "?y \<in> ?ys"
  proof -
    have *: "?y = enc
      (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) 0) [0..<k] @
       map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if 0 = exec (t + d) <#> j then 1 else 0) [0..<k] @
       [if 0 < t then 1 else 0, 1])"
      (is "_ = enc ?z")
      using zip_cont_def by simp
    then have 1: "?y > 1"
      using enc_greater by simp
    have "?z ! (2 * k + 1) = 1"
      using twok1_nth by fast
    then have 2: "dec ?y ! (2 * k + 1) = 1"
      using dec_zip_cont by simp
    have "?y < G ^ (2 * k + 2) + 2"
      using enc_less * zip_cont_less_G[of 0] by simp
    then show ?thesis
      using 1 2 by simp
  qed
  moreover have "zip_cont t xs i \<notin> ?ys" if "i > 0" for i
  proof (cases "i < TT")
    case True
    then have "dec (zip_cont t xs i) =
      (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i) [0..<k] @
       map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
       [if i < t then 1 else 0, 0])"
      using dec_zip_cont that by simp
    then have "dec (zip_cont t xs i) ! (2 * k + 1) = 0"
      using twok1_nth by force
    then show ?thesis
      by simp
  next
    case False
    then have "zip_cont t xs i = 0"
      using zip_cont_def by simp
    then show ?thesis
      by simp
  qed
  ultimately show ?thesis
    using begin_tapeI by simp
qed

definition "es6 \<equiv> es5 @ map (\<lambda>i. (1 + Suc i, 1 + Suc i)) [0..<n] @ [(1 + n, 1 + n)]"

lemma len_es6: "length es6 = length (es_fmt n) + 2 * TT + n + 4"
  using es6_def len_es5 by simp

definition tps6 :: "tape list" where
  "tps6 \<equiv>
    [(\<lfloor>zs\<rfloor>, n + 1),
     (zip_cont 0 (replicate k (0, Some 0)), n + 1)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

lemma tm6: "traces tm6 tps0 es6 tps6"
  unfolding tm6_def es6_def
proof (rule traces_sequential)
  show "traces tm5 tps0 es5 tps5"
    using tm5 .
  show "traces
     tm5_6
     tps5
     (map (\<lambda>i. (1 + Suc i, 1 + Suc i)) [0..<n] @ [(1 + n, 1 + n)])
     tps6"
     unfolding tm5_6_def
  proof (rule traces_tm_trans_until_01I[where ?n=n])
    show "1 < length tps5"
      using tps5_def by simp
    show "rneigh (tps5 ! 0) {0} n"
      using tps5_def contents_def zs_proper by (intro rneighI) auto
    show "map (\<lambda>i. (1 + Suc i, 1 + Suc i)) [0..<n] @ [(1 + n, 1 + n)] =
        map (\<lambda>i. (tps5 :#: 0 + Suc i, tps5 :#: 1 + Suc i)) [0..<n] @ [(tps5 :#: 0 + n, tps5 :#: 1 + n)]"
      using tps5_def by simp
    show "tps6 = tps5
        [0 := tps5 ! 0 |+| n,
         1 := transplant (tps5 ! 0) (tps5 ! 1) (\<lambda>h. enc (h mod G # replicate (k - 1) 0 @ replicate k 0 @ [0, 0])) n]"
    proof -
      define f where "f = (\<lambda>h. enc (h mod G # replicate (k - 1) 0 @ replicate k 0 @ [0, 0]))"
      let ?tp1 = "tps5 ! 0"
      let ?tp2 = "tps5 ! 1"
      let ?xs = "replicate k (0::nat, Some 0::nat option)"
      have rhs_less_TT: "zip_cont 0 ?xs i = enc
             (map (\<lambda>j. (start_config k zs <:> j) i) [0..<k] @
              map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] @
              [0, if i = 0 then 1 else 0])"
          if "i < TT" for i
      proof -
        have "zip_cont 0 ?xs i = enc
             (map (\<lambda>j. (exec (0 + fst (?xs ! j)) <:> j) i) [0..<k] @
              map (\<lambda>j. case snd (?xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (0 + d) <#> j then 1 else 0) [0..<k] @
              [if i < 0 then 1 else 0,
               if i = 0 then 1 else 0])"
          using that zip_cont_def by simp
        moreover have "map (\<lambda>j. (exec (0 + fst (?xs ! j)) <:> j) i) [0..<k] = map (\<lambda>j. (exec 0 <:> j) i) [0..<k]"
          by simp
        ultimately have "zip_cont 0 ?xs i = enc
             (map (\<lambda>j. (exec 0 <:> j) i) [0..<k] @
              map (\<lambda>j. case snd (?xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (0 + d) <#> j then 1 else 0) [0..<k] @
              [if i < 0 then 1 else 0,
               if i = 0 then 1 else 0])"
          by metis
        also have "... = enc
             (map (\<lambda>j. (exec 0 <:> j) i) [0..<k] @
              map (\<lambda>j. if i = exec 0 <#> j then 1 else 0) [0..<k] @
              [if i < 0 then 1 else 0,
               if i = 0 then 1 else 0])"
        proof -
          have 1: "map (\<lambda>j. case snd (?xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (0 + d) <#> j then 1 else 0) [0..<k] =
              map (\<lambda>j. if i = exec 0 <#> j then 1 else 0) [0..<k]"
            by simp
          show ?thesis
            by (simp add: 1)
        qed
        finally show ?thesis
          using exec_def by simp
      qed

      have "(if snd ?tp2 \<le> i \<and> i < snd ?tp2 + n then f (fst ?tp1 (snd ?tp1 + i - snd ?tp2)) else fst ?tp2 i) =
            zip_cont 0 (replicate k (0, Some 0)) i"
          (is "?lhs = ?rhs")
          for i
      proof (cases "1 \<le> i \<and> i < 1 + n")
        case True
        then have "snd ?tp2 \<le> i \<and> i < snd ?tp2 + n"
          using tps5_def by simp
        then have "?lhs = f (fst ?tp1 (snd ?tp1 + i - snd ?tp2))"
          by simp
        then have "?lhs = f (fst ?tp1 i)"
          using tps5_def by simp
        then have "?lhs = f (zs ! (i - 1))" (is "_ = f (zs ! ?i)")
          using tps5_def contents_def True by simp
        moreover have "zs ! ?i < G"
          using True zs_less_G by auto
        ultimately have lhs: "?lhs = enc (zs ! ?i # replicate (k - 1) 0 @ replicate k 0 @ [0, 0])"
          using f_def by simp

        have "TT > n"
          using fmt_ge_n by (simp add: le_imp_less_Suc)
        then have "i < TT"
          using True by simp
        then have rhs: "?rhs = enc
             (map (\<lambda>j. (start_config k zs <:> j) i) [0..<k] @
              map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] @
              [0, 0])"
          using True rhs_less_TT by simp

        have "map (\<lambda>j. (start_config k zs <:> j) i) [0..<k] = zs ! ?i # replicate (k - 1) 0" (is "?l = ?r")
        proof (intro nth_equalityI)
          show "length ?l = length ?r"
            using k_ge_2 by simp
          show "?l ! j = ?r ! j" if "j < length ?l" for j
          proof (cases "j = 0")
            case c1: True
            have "(start_config k zs <:> 0) i = zs ! ?i"
              using start_config_def True by simp
            then show ?thesis
              using c1 that by auto
          next
            case c2: False
            then have "(start_config k zs <:> j) i = 0"
              using start_config_def True that by simp
            then show ?thesis
              using c2 that by simp
          qed
        qed
        moreover have "map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] = replicate k 0"
        proof -
          have "start_config k zs <#> j = 0" if "j < k" for j
            using that start_config_pos by auto
          then have "map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] = map (\<lambda>j. 0) [0..<k]"
            using True by simp
          then show ?thesis
            by (simp add: map_replicate_trivial)
        qed
        ultimately show "?lhs = ?rhs"
          using lhs rhs by (metis Cons_eq_appendI)
      next
        case outside: False
        show ?thesis
        proof (cases "i = 0")
          case True
          then have lhs: "?lhs = enc (replicate k 1 @ replicate k 1 @ [0, 1])"
            using tps5_def contents'_def by simp
          moreover have "?rhs = enc
                (map (\<lambda>j. (start_config k zs <:> j) i) [0..<k] @
                 map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] @
                 [0, 1])"
            using rhs_less_TT True by simp
          moreover have "map (\<lambda>j. (start_config k zs <:> j) i) [0..<k] = replicate k 1" (is "?l = ?r")
          proof (rule nth_equalityI)
            show "length ?l = length ?r"
              by simp
            then show "?l ! j = ?r ! j" if "j < length ?l" for j
              using start_config_def True that start_config2 by simp
          qed
          moreover have "map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] = replicate k 1" (is "?l = ?r")
          proof (rule nth_equalityI)
            show "length ?l = length ?r"
              by simp
            show "?l ! j = ?r ! j" if "j < length ?l" for j
              using True start_config_pos that by auto
          qed
          ultimately show ?thesis
            by metis
        next
          case False
          then have "i > n"
            using outside by simp
          then have lhs: "?lhs = fst ?tp2 i"
            using tps5_def by simp
          then show ?thesis
          proof (cases "i < TT")
            case True
            moreover have "i > 0"
              using False by simp
            ultimately have lhs: "?lhs = enc (replicate k 0 @ replicate k 0 @ [0, 0])"
              using lhs tps5_def contents'_def by simp

            have "?rhs = enc
                (map (\<lambda>j. (start_config k zs <:> j) i) [0..<k] @
                 map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] @
                 [0, 0])"
              using True False rhs_less_TT by simp
            moreover have "map (\<lambda>j. (start_config k zs <:> j) i) [0..<k] = replicate k 0" (is "?l = ?r")
            proof (rule nth_equalityI)
              show "length ?l = length ?r"
                by simp
              show "?l ! j = ?r ! j" if "j < length ?l" for j
              proof (cases "j = 0")
                case True
                then show ?thesis
                  using that start_config_def `i > n` by simp
              next
                case False
                then show ?thesis
                  using that start_config_def `i > 0` by simp
              qed
            qed
            moreover have "map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] = replicate k 0"
            proof -
              have "start_config k zs <#> j = 0" if "j < k" for j
                using that start_config_pos by auto
              then have "map (\<lambda>j. if i = start_config k zs <#> j then 1 else 0) [0..<k] = map (\<lambda>j. 0) [0..<k]"
                by (simp add: False)
              then show ?thesis
                by (simp add: map_replicate_trivial)
            qed
            ultimately show ?thesis
              using lhs by metis
          next
            case False
            then have "i \<ge> TT"
              by simp
            moreover have "length (enc (replicate k 1 @ replicate k 1 @ [0, 1]) # replicate (fmt n) (enc (replicate k 0 @ replicate k 0 @ [0, 0]))) = TT"
              by simp
            ultimately have "?lhs = 0"
              using lhs contents'_at_ge by (simp add: tps5_def)
            moreover have "?rhs = 0"
              using zip_cont_def `i \<ge> TT` by simp
            ultimately show ?thesis
              by simp
          qed
        qed
      qed
      then have "(\<lambda>i. if snd ?tp2 \<le> i \<and> i < snd ?tp2 + n then f (fst ?tp1 (snd ?tp1 + i - snd ?tp2)) else fst ?tp2 i) =
            zip_cont 0 (replicate k (0, Some 0))"
        by simp
      moreover have "transplant (tps5 ! 0) (tps5 ! 1) (\<lambda>h. enc (h mod G # replicate (k - 1) 0 @ replicate k 0 @ [0, 0])) n =
          (\<lambda>i. if snd ?tp2 \<le> i \<and> i < snd ?tp2 + n then f (fst ?tp1 (snd ?tp1 + i - snd ?tp2)) else fst ?tp2 i,
            snd ?tp2 + n)"
        using transplant_def f_def by auto
      ultimately have "transplant (tps5 ! 0) (tps5 ! 1) (\<lambda>h. enc (h mod G # replicate (k - 1) 0 @ replicate k 0 @ [0, 0])) n =
          (zip_cont 0 (replicate k (0, Some 0)), n + 1)"
        using tps5_def by simp
      then have "tps6 ! 1 = transplant (tps5 ! 0) (tps5 ! 1) (\<lambda>h. enc (h mod G # replicate (k - 1) 0 @ replicate k 0 @ [0, 0])) n"
        using tps6_def by simp
      moreover have "tps6 ! 0 = tps5 ! 0 |+| n"
        using tps6_def tps5_def by simp
      ultimately show ?thesis
        using tps5_def tps6_def by simp
    qed
  qed
qed

definition tps7 :: "tape list" where
  "tps7 \<equiv>
    [(\<lfloor>zs\<rfloor>, n + 1),
     (zip_cont 0 (replicate k (0, Some 0)), 0)] @
    replicate (2 * k + 1) (\<lceil>\<triangleright>\<rceil>)"

definition "es7 \<equiv> es6 @ map (\<lambda>i. (n + 1, i)) (rev [0..<n + 1]) @ [(n + 1, 0)]"

lemma len_es7: "length es7 = length (es_fmt n) + 2 * TT + 2 * n + 6"
  using es7_def len_es6 by simp

lemma tm7: "traces tm7 tps0 es7 tps7"
  unfolding tm7_def es7_def
proof (rule traces_sequential)
  show "traces tm6 tps0 es6 tps6"
    using tm6 .
  show "traces tm_left_until1 tps6 (map (Pair (n + 1)) (rev [0..<n + 1]) @ [(n + 1, 0)]) tps7"
  proof (rule traces_tm_left_until_1I)
    show "1 < length tps6"
      using tps6_def by simp
    show "map (Pair (n + 1)) (rev [0..<n + 1]) @ [(n + 1, 0)] =
        map (Pair (tps6 :#: 0)) (rev [0..<tps6 :#: 1]) @ [(tps6 :#: 0, 0)]"
      using tps6_def by simp
    show "tps7 = tps6[1 := tps6 ! 1 |#=| 0]"
      using tps6_def tps7_def by simp
    show "begin_tape StartSym (tps6 ! 1)"
      using begin_tape_zip_cont tps6_def by simp
  qed
qed

definition tps8 :: "tape list" where
  "tps8 \<equiv>
    [(\<lfloor>zs\<rfloor>, n + 1),
     (zip_cont 0 (replicate k (0, Some 0)), 0),
     \<lceil>\<box>\<rceil>] @
    replicate (2 * k) (\<lceil>\<triangleright>\<rceil>)"

definition "es8 \<equiv> es7 @ [(n + 1, 0)]"

lemma len_es8: "length es8 = length (es_fmt n) + 2 * TT + 2 * n + 7"
  using es8_def len_es7 by simp

lemma tm8: "traces tm8 tps0 es8 tps8"
  unfolding tm8_def es8_def
proof (rule traces_sequential)
  show "traces tm7 tps0 es7 tps7"
    using tm7 .
  show "traces (tm_write 2 0) tps7 [(n + 1, 0)] tps8"
  proof (rule traces_tm_write_ge2I)
    show "(2::nat) \<le> 2"
      by simp
    show "2 < length tps7" "[(n + 1, 0)] = [(tps7 :#: 0, tps7 :#: 1)]"
      using tps7_def by simp_all
    show "tps8 = tps7[2 := tps7 ! 2 |:=| 0]"
    proof (rule nth_equalityI)
      show "length tps8 = length (tps7[2 := tps7 ! 2 |:=| 0])"
        using tps7_def tps8_def by simp
      show "tps8 ! i = tps7[2 := tps7 ! 2 |:=| 0] ! i" if "i < length tps8" for i
      proof -
        consider "i = 0" | "i = 1" | "i = 2" | "i > 2"
          by linarith
        then show ?thesis
        proof (cases)
          case 1
          then show ?thesis
            using tps7_def tps8_def by simp
        next
          case 2
          then show ?thesis
            using tps7_def tps8_def by simp
        next
          case 3
          then have *: "tps8 ! i = \<lceil>\<box>\<rceil>"
            using tps8_def by simp
          have "(tps7 ! 2) |:=| \<box> = \<lceil>\<box>\<rceil>"
            using tps7_def onesie_write by simp
          then have "(tps7[2 := tps7 ! 2 |:=| \<box>]) ! 2 = \<lceil>\<box>\<rceil>"
            using tps7_def by simp
          then show ?thesis
            using 3 * by simp
        next
          case 4
          then have "tps8 ! i = \<lceil>\<triangleright>\<rceil>"
            using tps8_def that by simp
          moreover have "tps7 ! i = \<lceil>\<triangleright>\<rceil>"
            using tps7_def that "4" tps8_def by auto
          ultimately show ?thesis
            by (simp add: "4" less_not_refl3)
        qed
      qed
    qed
  qed
qed

definition tps9 :: "tape list" where
  "tps9 \<equiv>
    [(\<lfloor>zs\<rfloor>, n + 1),
     (zip_cont 0 (replicate k (0, Some 0)), 0),
     \<lceil>\<box>\<rceil>] @
    replicate (2 * k) (\<lceil>\<box>\<rceil>)"

definition "es9 \<equiv> es8 @ [(n + 1, 0)]"

lemma len_es9: "length es9 = length (es_fmt n) + 2 * TT + 2 * n + 8"
  using es9_def len_es8 by simp

lemma tm9: "traces tm9 tps0 es9 tps9"
  unfolding tm9_def es9_def
proof (rule traces_sequential[OF tm8])
  show "traces (tm_write_many {3..<2 * k + 3} 0) tps8 [(n + 1, 0)] tps9"
  proof (rule traces_tm_write_manyI[where ?k="2*k+3"])
    show "0 \<notin> {3..<2 * k + 3}"
      by simp
    show "\<forall>j\<in> {3..<2 * k + 3}. j < 2 * k + 3"
      by simp
    show "2 \<le> 2 * k + 3"
      by simp
    show "length tps8 = 2 * k + 3" "length tps9 = 2 * k + 3"
      using tps8_def tps9_def by simp_all
    show "[(n + 1, 0)] = [(tps8 :#: 0, tps8 :#: 1)]"
      using tps8_def by simp
    show "tps9 ! j = tps8 ! j" if "j < 2 * k + 3" "j \<notin> {3..<2 * k + 3}" for j
    proof -
      have "j < 3"
        using that by simp
      then show ?thesis
        using tps8_def tps9_def by (metis (no_types, lifting) length_Cons list.size(3) nth_append numeral_3_eq_3)
    qed
    show "tps9 ! j = tps8 ! j |:=| 0" if "j \<in> {3..<2 * k + 3}" for j
    proof -
      have j: "j \<ge> 3" "j < 2 * k + 3"
        using that by simp_all
      then have "tps8 ! j = \<lceil>\<triangleright>\<rceil>"
        using tps8_def by simp
      moreover have "tps9 ! j = \<lceil>\<box>\<rceil>"
        using j tps9_def by simp
      ultimately show ?thesis
        by (simp add: onesie_write)
    qed
  qed
qed

subsubsection \<open>The loop\<close>

text \<open>
Immediately before and during the loop the tapes will have the shape below.  The
input tape will stay unchanged. The output tape will contain the $k$ encoded
tapes of $M$. The first memorization tape will contain $M$'s state. The
following $k$ memorization tapes will store information about head movements.
The final $k$ memorization tapes will have information about read or
to-be-written symbols.
\<close>

definition tpsL :: "nat \<Rightarrow> (nat \<times> nat option) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> symbol) \<Rightarrow> tape list" where
  "tpsL t xs i q mvs symbs \<equiv>
    (\<lfloor>zs\<rfloor>, n + 1) #
    (zip_cont t xs, i) #
    \<lceil>fst (exec (t + q))\<rceil> #
    map (onesie \<circ> mvs) [0..<k] @
    map (onesie \<circ> symbs) [0..<k]"

lemma length_tpsL [simp]: "length (tpsL t xs i q mvs symbs) = 2 * k + 3"
  using tpsL_def by simp

lemma tpsL_pos_0: "tpsL t xs i q mvs symbs :#: 0 = n + 1"
  unfolding tpsL_def by simp

lemma tpsL_pos_1: "tpsL t xs i q mvs symbs :#: 1 = i"
  unfolding tpsL_def by simp

lemma read_tpsL_0: "read (tpsL t xs i q mvs symbs) ! 0 = \<box>"
  unfolding tpsL_def using contents_def read_def by simp

lemma read_tpsL_1: "read (tpsL t xs i q mvs symbs) ! 1 =
  (if i < TT then enc
    (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i) [0..<k] @
     map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
     [if i < t then 1 else 0,
      if i = 0 then 1 else 0])
   else 0)"
  unfolding tpsL_def zip_cont_def using read_def by simp

lemma read_tpsL_1_nth_less_k:
  assumes "i < TT" and "j < k"
  shows "enc_nth (read (tpsL t xs i q mvs symbs) ! 1) j = (exec (t + fst (xs ! j)) <:> j) i"
  using assms read_tpsL_1 dec_zip_cont_less_k enc_nth_def zip_cont_def by auto

lemma read_tpsL_1_nth_less_2k:
  assumes "i < TT" and "k \<le> j" and "j < 2 * k"
  shows "enc_nth (read (tpsL t xs i q mvs symbs) ! 1) j =
    (case snd (xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
  using assms read_tpsL_1 dec_zip_cont_less_2k enc_nth_def zip_cont_def by simp

lemma read_tpsL_1_nth_2k:
  assumes "i < TT"
  shows "enc_nth (read (tpsL t xs i q mvs symbs) ! 1) (2 * k) = (if i < t then 1 else 0)"
  using assms read_tpsL_1 dec_zip_cont_2k enc_nth_def zip_cont_def by simp

lemma read_tpsL_1_nth_2k1:
  assumes "i < TT"
  shows "enc_nth (read (tpsL t xs i q mvs symbs) ! 1) (2 * k + 1) = (if i = 0 then 1 else 0)"
  using assms read_tpsL_1 dec_zip_cont_2k1 enc_nth_def zip_cont_def by simp

lemma read_tpsL_1_bounds:
  assumes "i < TT"
  shows "read (tpsL t xs i q mvs symbs) ! 1 > 1"
    and "read (tpsL t xs i q mvs symbs) ! 1 < G ^ (2 * k + 2) + 2"
proof -
  have "read (tpsL t xs i q mvs symbs) ! 1 = zip_cont t xs i"
    using tpsL_def read_def by simp
  then show "read (tpsL t xs i q mvs symbs) ! 1 > 1"
      and "read (tpsL t xs i q mvs symbs) ! 1 < G ^ (2 * k + 2) + 2"
    using zip_cont_gt_1[OF assms] zip_cont_less[OF assms] by simp_all
qed

lemma read_tpsL_2: "read (tpsL t xs i q mvs symbs) ! 2 = fst (exec (t + q))"
  unfolding tpsL_def using contents_def read_def by simp

lemma read_tpsL_3:
  assumes "3 \<le> j" and "j < k + 3"
  shows "read (tpsL t xs i q mvs symbs) ! j = mvs (j - 3)"
proof -
  define j' where "j' = j - 3"
  then have "j' < k"
    using assms by simp
  have "read (tpsL t xs i q mvs symbs) ! j =
      (map (tape_read \<circ> (onesie \<circ> mvs)) [0..<k] @
       map (tape_read \<circ> (onesie \<circ> symbs)) [0..<k]) !
      (j - Suc (Suc (Suc 0)))"
    unfolding tpsL_def read_def using assms by simp
  also have "... =
    (map (tape_read \<circ> (onesie \<circ> mvs)) [0..<k] @
     map (tape_read \<circ> (onesie \<circ> symbs)) [0..<k]) ! j'"
    by (simp add: j'_def numeral_3_eq_3)
  also have "... = mvs j'"
    using `j' < k` by (simp add: nth_append)
  finally have "read (tpsL t xs i q mvs symbs) ! j = mvs j'" .
  then show ?thesis
    using j'_def by simp
qed

lemma read_tpsL_3':
  assumes "j < k"
  shows "read (tpsL t xs i q mvs symbs) ! (j + 3) = mvs j"
  using assms read_tpsL_3 by simp

lemma read_tpsL_4:
  assumes "k + 3 \<le> j" and "j < 2 * k + 3"
  shows "read (tpsL t xs i q mvs symbs) ! j = symbs (j - k - 3)"
proof -
  define j' where "j' = j - 3"
  then have j': "k \<le> j'" "j' < k + k"
    using assms by simp_all
  have "read (tpsL t xs i q mvs symbs) ! j =
      (map (tape_read \<circ> (onesie \<circ> mvs)) [0..<k] @
       map (tape_read \<circ> (onesie \<circ> symbs)) [0..<k]) !
      (j - Suc (Suc (Suc 0)))"
    unfolding tpsL_def read_def using assms by simp
  also have "... =
    (map (tape_read \<circ> (onesie \<circ> mvs)) [0..<k] @
     map (tape_read \<circ> (onesie \<circ> symbs)) [0..<k]) ! j'"
    by (simp add: j'_def numeral_3_eq_3)
  also have "... = symbs (j' - k)"
    using j' by (simp add: nth_append)
  finally have "read (tpsL t xs i q mvs symbs) ! j = symbs (j' - k)" .
  then show ?thesis
    using j'_def using diff_commute by auto
qed

lemma map_const_upt: "map (onesie \<circ> (\<lambda>_. c)) [0..<k] = replicate k \<lceil>c\<rceil>"
  by (metis List.map.compositionality map_replicate map_replicate_trivial)

text \<open>
After the initialization, that is, right before the loop, the simulator's tapes
look like this:
\<close>

lemma tps9_tpsL: "tps9 = tpsL 0 (replicate k (0, Some 0)) 0 0 (\<lambda>j. 0) (\<lambda>j. 0)"
proof -
  have "fst (exec 0) = 0"
    using exec_def by (simp add: start_config_def)
  then have "tpsL 0 (replicate k (0, Some 0)) 0 0 (\<lambda>j. 0) (\<lambda>j. 0) =
    (\<lfloor>zs\<rfloor>, n + 1) #
    (zip_cont 0 (replicate k (0, Some 0)), 0) #
    \<lceil>\<box>\<rceil> #
    replicate k (\<lceil>\<box>\<rceil>) @
    replicate k (\<lceil>\<box>\<rceil>)"
    using tpsL_def map_const_upt by simp
  then show ?thesis
    using tps9_def by (metis Cons_eq_appendI mult_2 replicate_add self_append_conv2)
qed

lemma tpsL_0: "tpsL t xs i q mvs symbs ! 0 = (\<lfloor>zs\<rfloor>, n + 1)"
  using tpsL_def by simp

lemma tpsL_1: "tpsL t xs i q mvs symbs ! 1 = (zip_cont t xs, i)"
  using tpsL_def by simp

lemma tpsL_2: "tpsL t xs i q mvs symbs ! 2 = \<lceil>fst (exec (t + q))\<rceil>"
  using tpsL_def by simp

lemma tpsL_mvs: "j < k \<Longrightarrow> tpsL t xs i q mvs symbs ! (3 + j) = \<lceil>mvs j\<rceil>"
  using tpsL_def by (simp add: nth_append)

lemma tpsL_mvs': "3 \<le> j \<Longrightarrow> j < 3 + k \<Longrightarrow> tpsL t xs i q mvs symbs ! j = \<lceil>mvs (j - 3)\<rceil>"
  using tpsL_mvs by (metis add.commute le_add_diff_inverse less_diff_conv2)

lemma tpsL_symbs:
  assumes "j < k"
  shows "tpsL t xs i q mvs symbs ! (3 + k + j) = \<lceil>symbs j\<rceil>"
  using tpsL_def assms by (simp add: nth_append)

lemma tpsL_symbs':
  assumes "3 + k \<le> j" and "j < 2 * k + 3"
  shows "tpsL t xs i q mvs symbs ! j = \<lceil>symbs (j - k - 3)\<rceil>"
proof -
  have "j - (k + 3) < k"
    using assms(1) assms(2) by linarith
  then show ?thesis
    using assms(1) tpsL_symbs by fastforce
qed

text \<open>The condition: less than $TT$ steps simulated.\<close>

definition tpsC0 :: "nat \<Rightarrow> tape list" where
  "tpsC0 t \<equiv> tpsL t (replicate k (0, Some 0)) 0 0 (\<lambda>j. 0) (\<lambda>j. 0)"

definition "tpsC1 t \<equiv> tpsL t (replicate k (0, Some 0)) t 0 (\<lambda>j. 0) (\<lambda>j. 0)"

definition "esC t \<equiv> map (\<lambda>i. (n + 1, Suc i)) [0..<t] @ [(n + 1, t)]"

lemma set_filter_upt: "x \<in> set (filter f [0..<N]) \<Longrightarrow> x < N"
  by simp

lemma set_filter_upt': "x \<in> set (filter f [0..<N]) \<Longrightarrow> f x"
  by simp

text \<open>
We will use this TM at the end of the loop again. Therefore we
prove a more general result than necessary at this point.
\<close>

lemma tmC_general:
  assumes "t \<le> TT"
    and "tps = tpsL t xs 0 i mvs symbs"
    and "tps' = tpsL t xs t i mvs symbs"
  shows "traces tmC tps (esC t) tps'"
  unfolding tmC_def
proof (rule traces_tm_right_until_1I[where ?n="t"])
  show "1 < length tps"
    using assms(2) by simp
  show "tps' = tps[1 := tps ! 1 |+| t]"
    using assms(2,3) tpsL_def by simp
  show "esC t =
      map (\<lambda>i. (tps :#: 0, tps :#: 1 + Suc i)) [0..<t] @ [(tps :#: 0, tps :#: 1 + t)]"
    using esC_def assms(2) tpsL_def by simp
  show "rneigh (tps ! 1) {y. y < G ^ (2 * k + 2) + 2 \<and> (y = 0 \<or> dec y ! (2 * k) = 0)} t"
    (is "rneigh _ ?s t")
  proof (rule rneighI)
    have 1: "tps ! 1 = (zip_cont t xs, 0)"
      using assms(2) tpsL_def by simp
    have s: "?s = {y. y = 0 \<or> (dec y ! (2 * k) = 0 \<and> y < G ^ (2 * k + 2) + 2)}" (is "_ = ?r")
      by auto
    show "(tps ::: 1) (tps :#: 1 + t) \<in> ?s"
    proof (cases "t = TT")
      case True
      then have "tps :#: 1 + t = TT"
        using assms(2) tpsL_def by simp
      moreover have "(tps ::: 1) TT = 0"
        using assms(2) tpsL_def zip_cont_def by simp
      ultimately show ?thesis
        by auto
    next
      case False
      with assms have "t < TT"
        by simp
      let ?y = "(tps ::: 1) t"
      have "dec ?y ! (2 * k) = 0"
        using assms(2) tpsL_def dec_zip_cont[OF `t < TT`] by (simp add: twok_nth)
      moreover have "?y < G ^ (2 * k + 2) + 2"
        using assms(2) tpsL_def `t < TT` zip_cont_less by simp
      ultimately have "?y \<in> ?s"
        using s by simp
      then show ?thesis
        using 1 by simp
    qed
    show "(tps ::: 1) (tps :#: 1 + m) \<notin> ?s" (is "?y \<notin> ?s") if "m < t" for m
    proof -
      have "m < TT"
        using that assms by simp
      then have "dec ?y ! (2 * k) = 1"
        using tpsC0_def tpsL_def dec_zip_cont[OF `m < TT`] that
        by (metis (no_types, lifting) "1" add_cancel_right_left dec_zip_cont_2k prod.sel(1) prod.sel(2))
      moreover from `m < TT` have "?y > 1"
        using 1 zip_cont_gt_1 by simp
      ultimately show ?thesis
        using s by simp
    qed
  qed
qed

corollary tmC:
  assumes "t \<le> TT"
  shows "traces tmC (tpsC0 t) (esC t) (tpsC1 t)"
  using tmC_general tpsC0_def tpsC1_def assms by simp

lemma tpsC1_at_T: "tpsC1 TT :.: 1 = 0"
  using tpsC1_def tpsL_def zip_cont_def by simp

lemma tpsC1_at_less_T: "t < TT \<Longrightarrow> tpsC1 t :.: 1 > 0"
proof -
  assume "t < TT"
  then have "tpsC1 t :.: 1 > 1"
    using tpsC1_def tpsL_def zip_cont_def enc_greater by simp
  then show ?thesis
    by simp
qed

text \<open>The body of the loop: simulating one step\<close>

definition "tpsL0 t \<equiv> tpsL t (replicate k (0, Some 0)) t 0 (\<lambda>j. 0) (\<lambda>j. 0)"

lemma tpsL0_eq_tpsC1: "tpsL0 t = tpsC1 t"
  using tpsL0_def tpsC1_def by simp

definition "esL1 t \<equiv> map (\<lambda>i. (n + 1, i)) (rev [0..<t]) @ [(n + 1, 0)]"

definition "tpsL1 t \<equiv> tpsL t (replicate k (0, Some 0)) 0 0 (\<lambda>j. 0) (\<lambda>j. 0)"

lemma tmL1: "traces tmL1 (tpsL0 t) (esL1 t) (tpsL1 t)"
  unfolding tmL1_def esL1_def
proof (rule traces_tm_left_until_1I)
  show "1 < length (tpsL0 t)"
    using tpsL0_def tpsL_def by simp
  show "map (Pair (n + 1)) (rev [0..<t]) @ [(n + 1, 0)] =
      map (Pair (tpsL0 t :#: 0)) (rev [0..<tpsL0 t :#: 1]) @ [(tpsL0 t :#: 0, 0)]"
    using tpsL0_def tpsL_def by simp
  show "tpsL1 t = (tpsL0 t)[1 := tpsL0 t ! 1 |#=| 0]"
    using tpsL0_def tpsL1_def tpsL_def by simp
  show "begin_tape StartSym (tpsL0 t ! 1)"
    using begin_tape_zip_cont tpsL0_def tpsL_def by simp
qed

text \<open>Collecting the read symbols of the simulated machines:\<close>

lemma sem_cmdL2_ge_TT:
  assumes "tps = tpsL t xs i q mvs symbs" and "i \<ge> TT"
  shows "sem cmdL2 (0, tps) = (1, tps)"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) cmdL2"
    using cmdL2_def by simp
  show len: "length tps = 2 * k + 3"
    using assms(1) by simp
  show "length tps = 2 * k + 3"
    using assms(1) by simp
  let ?rs = "read tps"
  show "fst (cmdL2 ?rs) = 1"
  proof -
    have "?rs ! 1 = \<box>"
      using assms read_tpsL_1 by auto
    then show ?thesis
      by (simp add: cmdL2_def)
  qed
  then show "act (cmdL2 ?rs [!] i) (tps ! i) = tps ! i" if "i < 2 * k + 3" for i
    using assms that
    by (metis (no_types, lifting) One_nat_def act_Stay cmdL2_at_eq_0 cmdL2_def len less_Suc_eq_0_disj
      less_numeral_extra(4) prod.sel(1) read_length)
qed

lemma sem_cmdL2_less_TT:
  assumes "tps = tpsL t xs i q mvs symbs"
    and "symbs = (\<lambda>j. if exec t <#> j < i then exec t <.> j else 0) "
    and "tps' = tpsL t xs (Suc i) q mvs symbs'"
    and "symbs' = (\<lambda>j. if exec t <#> j < Suc i then exec t <.> j else 0) "
    and "i < TT"
    and "xs = replicate k (0, Some 0)"
  shows "sem cmdL2 (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) cmdL2"
    using cmdL2_def by simp
  show len: "length tps = 2 * k + 3"
    using assms(1) by simp
  show len': "length tps' = 2 * k + 3"
    using assms(3) by simp
  define rs where "rs = read tps"
  then have rs_at_1: "rs ! 1 \<noteq> \<box>"
    using assms(1,5) read_tpsL_1 enc_greater by (metis (no_types, lifting) not_one_less_zero)
  then show "fst (cmdL2 (read tps)) = 0"
    by (simp add: cmdL2_def rs_def)
  show "act (cmdL2 (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    have snd: "snd (cmdL2 rs) =
      [(rs!0, Stay), (rs!1, Right), (rs!2, Stay)] @
       (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
       (map (\<lambda>j. (if 1 < rs ! 1 \<and> rs ! 1 < G^(2*k+2)+2 \<and> enc_nth (rs!1) (k+j) = 1 then enc_nth (rs!1) j else rs!(3+k+j), Stay)) [0..<k])"
      using rs_at_1 by (simp add: cmdL2_def)
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using \<open>j < 2 * k + 3\<close> by linarith
    then show ?thesis
    proof cases
      case 1
      then have "cmdL2 rs [!] j = (rs ! 0, Stay)"
        by (simp add: snd)
      then show ?thesis
        using act_Stay assms(1,3) tpsL_def "1" rs_def read_tpsL_0 by auto
    next
      case 2
      then have "cmdL2 rs [!] j = (rs ! 1, Right)"
        by (simp add: snd)
      then show ?thesis
        using act_Right assms(1,3) "2" rs_def
        by (metis Suc_eq_plus1 add.commute add_Suc fst_conv len less_add_Suc1 numeral_3_eq_3 sndI tpsL_1)
    next
      case 3
      then have "cmdL2 rs [!] j = (rs ! 2, Stay)"
        by (simp add: snd)
      then show ?thesis
        using act_Stay assms(1,3) "3" rs_def by (metis len that tpsL_2)
    next
      case 4
      then have "cmdL2 rs [!] j = (rs ! j, Stay)"
        using cmdL2_at_3 rs_at_1 by simp
      then show ?thesis
        using act_Stay assms(1,3) "4" rs_def by (metis add.commute len that tpsL_mvs')
    next
      case 5
      then have 1: "cmdL2 rs [!] j =
          (if 1 < rs ! 1 \<and> rs ! 1 < G^(2*k+2)+2 \<and> enc_nth (rs ! 1) (j - 3) = 1
           then enc_nth (rs ! 1) (j - k - 3)
           else rs ! j,
           Stay)"
        using cmdL2_at_4 rs_at_1 by simp
      have enc: "rs ! 1 = enc
            (map (\<lambda>j. (exec (t + fst (xs ! j)) <:> j) i) [0..<k] @
             map (\<lambda>j. case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
             [if i < t then 1 else 0,
              if i = 0 then 1 else 0])"
        using read_tpsL_1 assms(1,5) rs_def by simp
      have "rs ! 1 > 1" "rs ! 1 < G ^ (2 * k + 2) + 2"
        using rs_def assms(1,5) read_tpsL_1_bounds by simp_all
      then have cmd1: "cmdL2 rs [!] j =
          (if enc_nth (rs ! 1) (j - 3) = 1 then enc_nth (rs ! 1) (j - k - 3) else rs ! j, Stay)"
        using 1 by simp
      have "enc_nth (rs ! 1) (j - 3) =
          (case snd (xs ! (j - 3 - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - 3 - k) then 1 else 0)"
        using read_tpsL_1_nth_less_2k[where ?j="j - 3"] 5 assms(1,5) rs_def by auto
      then have "enc_nth (rs ! 1) (j - 3) = (if i = exec t <#> (j - 3 - k) then 1 else 0)"
        using 5 assms(6) by auto
      then have cmd2: "enc_nth (rs ! 1) (j - 3) = (if i = exec t <#> (j - k - 3) then 1 else 0)"
        by (metis diff_right_commute)
      let ?j = "j - k - 3"
      have "enc_nth (rs ! 1) ?j = (exec (t + fst (xs ! ?j)) <:> ?j) i"
        using read_tpsL_1_nth_less_k[where ?j="j - k - 3"] 5 assms(1,5) rs_def by auto
      then have "enc_nth (rs ! 1) ?j = (exec t <:> ?j) i"
        using assms(6) 5 by auto
      then have "cmdL2 rs [!] j =
          (if i = exec t <#> ?j then (exec t <:> ?j) i else rs ! j, Stay)"
        using cmd1 cmd2 by simp
      then have command: "cmdL2 rs [!] j =
          (if i = exec t <#> ?j then exec t <.> ?j else rs ! j, Stay)"
        by simp

      have tps: "tps ! j = \<lceil>if exec t <#> ?j < i then exec t <.> ?j else \<box>\<rceil>"
        using 5 assms(1,2) tpsL_symbs' by simp

      have tps': "tps' ! j = \<lceil>if exec t <#> ?j < Suc i then exec t <.> ?j else \<box>\<rceil>"
        using 5 assms(3,4) tpsL_symbs' by simp

      show "act (cmdL2 (read tps) [!] j) (tps ! j) = tps' ! j"
      proof (cases "exec t <#> ?j = i")
        case True
        then have "act (cmdL2 (read tps) [!] j) (tps ! j) = act (exec t <.> ?j, Stay) (tps ! j)"
          using rs_def command by simp
        also have "... = act (exec t <.> ?j, Stay) \<lceil>if exec t <#> ?j < i then exec t <.> ?j else \<box>\<rceil>"
          using tps by simp
        also have "... = \<lceil>exec t <.> ?j\<rceil>"
          using act_onesie by simp
        also have "... = \<lceil>if exec t <#> ?j < Suc i then exec t <.> ?j else \<box>\<rceil>"
          using True by simp
        also have "... = tps' ! j"
          using tps' by simp
        finally show ?thesis .
      next
        case False
        then have "act (cmdL2 (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
          using rs_def command by simp
        also have "... = tps ! j"
          using rs_def act_Stay by (simp add: "5" len)
        also have "... = \<lceil>if exec t <#> ?j < i then exec t <.> ?j else \<box>\<rceil>"
          using tps by simp
        also have "... = \<lceil>if exec t <#> ?j < Suc i then exec t <.> ?j else \<box>\<rceil>"
          using False by simp
        also have "... = tps' ! j"
          using tps' by simp
        finally show ?thesis .
      qed
    qed
  qed
qed

corollary sem_cmdL2_less_Tfmt:
  assumes "xs = replicate k (0, Some 0)" and "i < TT"
  shows "sem cmdL2
    (0, tpsL t xs i q mvs (\<lambda>j. if exec t <#> j < i then exec t <.> j else \<box>)) =
    (0, tpsL t xs (Suc i) q mvs (\<lambda>j. if exec t <#> j < Suc i then exec t <.> j else \<box>))"
  using sem_cmdL2_less_TT assms by simp

lemma execute_cmdL2_le_TT:
  assumes "tt \<le> TT" and "xs = replicate k (0, Some 0)" and "tps = tpsL t xs 0 q mvs (\<lambda>_. \<box>)"
  shows "execute tmL1_2 (0, tps) tt =
    (0, tpsL t xs tt q mvs (\<lambda>j. if exec t <#> j < tt then exec t <.> j else \<box>))"
  using assms(1)
proof (induction tt)
  case 0
  then show ?case
    using assms(3) by simp
next
  case (Suc tt)
  then have "execute tmL1_2 (0, tps) (Suc tt) = exe tmL1_2 (execute tmL1_2 (0, tps) tt)"
    by simp
  also have "... = exe tmL1_2 (0, tpsL t xs tt q mvs (\<lambda>j. if exec t <#> j < tt then exec t <.> j else \<box>))"
    using Suc by simp
  also have "... = sem cmdL2 (0, tpsL t xs tt q mvs (\<lambda>j. if exec t <#> j < tt then exec t <.> j else \<box>))"
    unfolding tmL1_2_def using Suc by (simp add: exe_lt_length)
  also have "... = (0, tpsL t xs (Suc tt) q mvs (\<lambda>j. if exec t <#> j < Suc tt then exec t <.> j else \<box>))"
    using sem_cmdL2_less_Tfmt[OF assms(2)] Suc by simp
  finally show ?case .
qed

lemma tpsL_symbs_eq:
  assumes "\<And>j. j < k \<Longrightarrow> symbs j = symbs' j"
  shows "tpsL t xs i q mvs symbs = tpsL t xs i q mvs symbs'"
  unfolding tpsL_def using assms by simp

lemma execute_cmdL2_Suc_TT:
  assumes "xs = replicate k (0, Some 0)" and "tps = tpsL t xs 0 q mvs (\<lambda>j. 0)" and "t < TT"
  shows "execute tmL1_2 (0, tps) (Suc TT) = (1, tpsL t xs TT q mvs (\<lambda>j. exec t <.> j))"
proof -
  have "execute tmL1_2 (0, tps) (Suc TT) = exe tmL1_2 (execute tmL1_2 (0, tps) TT)"
    by simp
  also have "... = exe tmL1_2 (0, tpsL t xs TT q mvs (\<lambda>j. if exec t <#> j < TT then exec t <.> j else \<box>))"
    using execute_cmdL2_le_TT[where ?tt=TT] assms(1,2) by simp
  also have "... = sem cmdL2 (0, tpsL t xs TT q mvs (\<lambda>j. if exec t <#> j < TT then exec t <.> j else \<box>))"
    unfolding tmL1_2_def by (simp add: exe_lt_length)
  also have "... = (1, tpsL t xs TT q mvs (\<lambda>j. if exec t <#> j < TT then exec t <.> j else \<box>))"
    using sem_cmdL2_ge_TT[where ?i=TT] by simp
  finally have "execute tmL1_2 (0, tps) (Suc TT) =
    (1, tpsL t xs TT q mvs (\<lambda>j. if exec t <#> j < TT then exec t <.> j else \<box>))" .
  moreover have "(\<lambda>j. if exec t <#> j < TT then exec t <.> j else \<box>) j = (\<lambda>j. exec t <.> j) j"
      if "j < k" for j
    using exec_pos_less_TT assms(3) that by simp
  ultimately show ?thesis
    using tpsL_symbs_eq by fastforce
qed

definition "esL1_2 \<equiv> map (\<lambda>i. (n + 1, Suc i)) [0..<TT] @ [(n + 1, TT)]"

lemma traces_tmL1_2:
  assumes "xs = replicate k (0, Some 0)" and "t < TT"
  shows "traces tmL1_2 (tpsL t xs 0 q mvs (\<lambda>_. \<box>)) esL1_2 (tpsL t xs TT q mvs (\<lambda>j. exec t <.> j))"
proof
  have len: "length esL1_2 = Suc TT"
    unfolding esL1_2_def by simp
  let ?tps = "tpsL t xs 0 q mvs (\<lambda>j. 0)"
  show "execute tmL1_2 (0, ?tps) (length esL1_2) =
      (length tmL1_2, tpsL t xs (Suc (fmt n)) q mvs (\<lambda>j. exec t <.> j))"
    using len execute_cmdL2_Suc_TT[OF assms(1) _ assms(2)] by (simp add: tmL1_2_def)
  show "\<And>i. i < length esL1_2 \<Longrightarrow>
        fst (execute tmL1_2 (0, ?tps) i) < length tmL1_2"
    using len tmL1_2_def execute_cmdL2_le_TT assms(1)
    by (metis (no_types, lifting) One_nat_def Pair_inject length_Cons less_Suc_eq_le
     less_one list.size(3) prod.collapse)
  show "snd (execute tmL1_2 (0, ?tps) (Suc i)) :#: 0 = fst (esL1_2 ! i) \<and>
        snd (execute tmL1_2 (0, ?tps) (Suc i)) :#: 1 = snd (esL1_2 ! i)"
    if "i < length esL1_2" for i
  proof (cases "i < TT")
    case True
    then have "execute tmL1_2 (0, ?tps) (Suc i) =
        (0, tpsL t xs (Suc i) q mvs (\<lambda>j. if exec t <#> j < Suc i then exec t <.> j else \<box>))"
      using execute_cmdL2_le_TT[of "Suc i" xs] assms by simp
    then have "snd (execute tmL1_2 (0, ?tps) (Suc i)) =
        tpsL t xs (Suc i) q mvs (\<lambda>j. if exec t <#> j < Suc i then exec t <.> j else \<box>)"
      by simp
    moreover have "esL1_2 ! i = (n + 1, Suc i)"
      unfolding esL1_2_def
      using True nth_append
      by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 add.commute add_Suc diff_zero
        length_map length_upt nth_map_upt)
    ultimately show ?thesis
      using tpsL_pos_0 tpsL_pos_1 by simp
  next
    case False
    then have "i = TT"
      using len that by simp
    then have "execute tmL1_2 (0, ?tps) (Suc i) = (1, tpsL t xs TT q mvs (\<lambda>j. exec t <.> j))"
      using execute_cmdL2_Suc_TT assms by simp
    moreover have "esL1_2 ! i = (n + 1, TT)"
      using `i = TT` esL1_2_def by (metis (no_types, lifting) diff_zero length_map length_upt nth_append_length)
    ultimately show ?thesis
      using tpsL_pos_0 tpsL_pos_1 by auto
  qed
qed

definition "esL2 t \<equiv> esL1 t @ esL1_2"

definition "tpsL2 t \<equiv> tpsL t (replicate k (0, Some 0)) TT 0 (\<lambda>_. \<box>) (\<lambda>j. exec t <.> j)"

lemma tmL2:
  assumes "t < TT"
  shows "traces tmL2 (tpsL0 t) (esL2 t) (tpsL2 t)"
  unfolding tmL2_def esL2_def
proof (rule traces_sequential[OF tmL1])
  show "traces tmL1_2 (tpsL1 t) esL1_2 (tpsL2 t)"
    using traces_tmL1_2[OF _ assms] by (simp add: tpsL1_def tpsL2_def)
qed

definition "sim_nextstate t \<equiv>
  (if fst (exec t) < length M
   then fst ((M ! (fst (exec t))) (config_read (exec t)))
   else fst (exec t))"

lemma sim_nextstate: "fst (exec (Suc t)) = sim_nextstate t"
proof (cases "fst (exec t) < length M")
  case True
  let ?cfg = "exec t"
  let ?rs = "config_read ?cfg"
  let ?cmd = "M ! (fst ?cfg)"
  have "exec (Suc t) = sem ?cmd ?cfg"
    using exec_def True by (simp add: exe_lt_length)
  then have 2: "fst (exec (Suc t)) = fst (sem ?cmd ?cfg)"
    by simp
  also have "... = fst (?cmd ?rs)"
    using sem' by simp
  also have "... = sim_nextstate t"
    using sim_nextstate_def True by simp
  finally show ?thesis .
next
  case False
  then show ?thesis
    using exec_def exe_def sim_nextstate_def by simp
qed

definition "sim_write t \<equiv>
  (if fst (exec t) < length M
   then map fst (snd ((M ! (fst (exec t))) (config_read (exec t))))
   else config_read (exec t))"

lemma sim_write_nth:
  assumes "fst (exec t) < length M" and "j < k"
  shows "sim_write t ! j = ((M ! (fst (exec t))) (config_read (exec t)) [.] j)"
proof -
  have "length (snd ((M ! (fst (exec t))) (config_read (exec t)))) = k"
    using assms turing_commandD(1) exec_def execute_num_tapes read_length start_config_length tm_M turing_machine_def
    by (metis add_gr_0 less_imp_add_positive nth_mem)
  then show ?thesis
    using sim_write_def assms by simp
qed

lemma sim_write_nth_else:
  assumes "\<not> (fst (exec t) < length M)"
  shows "sim_write t ! j = config_read (exec t) ! j"
  by (simp add: assms sim_write_def)

lemma sim_write_nth_less_G:
  assumes "j < k"
  shows "sim_write t ! j < G"
proof (cases "fst (exec t) < length M")
  case True
  then have *: "sim_write t ! j = (M ! (fst (exec t))) (config_read (exec t)) [.] j"
    using sim_write_nth assms by simp
  have "turing_command k (length M) G (M ! (fst (exec t)))"
    using tm_M True turing_machineD(3) by simp
  moreover have "\<forall>i<k. (config_read (exec t)) ! i < G"
    using read_alphabet exec_def tm_M by (simp add: zs_less_G)
  moreover have "length (config_read (exec t)) = k"
    by (metis Suc_1 exec_def execute_num_tapes start_config_length less_le_trans read_length
      turing_machine_def tm_M zero_less_Suc)
  ultimately have "(M ! (fst (exec t))) (config_read (exec t)) [.] j < G"
    using assms exec_def turing_commandD(2) by simp
  then show ?thesis
    using * by simp
next
  case False
  then show ?thesis
    using exec_def sim_write_nth_else assms tape_alphabet
    by (simp add: read_alphabet tm_M zs_less_G)
qed

lemma sim_write:
  assumes "j < k"
  shows "exec (Suc t) <:> j = (exec t <:> j)(exec t <#> j := sim_write t ! j)"
proof (cases "fst (exec t) < length M")
  case True
  let ?cfg = "exec t"
  let ?rs = "config_read ?cfg"
  let ?cmd = "M ! (fst ?cfg)"
  have len_rs: "length ?rs = k"
    using assms exec_def execute_num_tapes start_config_length read_length tm_M by simp
  have "turing_command k (length M) G ?cmd"
    using True tm_M turing_machineD(3) by simp
  then have len: "length (snd (?cmd ?rs)) = k"
    using len_rs turing_commandD(1) by simp

  have "sim_write t = map fst (snd (?cmd ?rs))"
    using sim_write_def True by simp
  then have 1: "sim_write t ! j = ?cmd ?rs [.] j"
    by (simp add: assms len)

  have 2: "exec (Suc t) = sem ?cmd ?cfg"
    using exec_def True by (simp add: exe_lt_length)

  have "snd (sem ?cmd ?cfg) = map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd ?rs)) (snd ?cfg))"
    using sem' by simp
  then have "snd (sem ?cmd ?cfg) ! j = (\<lambda>(a, tp). act a tp) ((snd (?cmd ?rs) ! j), (snd ?cfg ! j))"
    using len assms len_rs read_length by simp
  then have "sem ?cmd ?cfg <!> j = act (snd (?cmd ?rs) ! j) (?cfg <!> j)"
    by simp
  then have "sem ?cmd ?cfg <:> j = fst (act (snd (?cmd ?rs) ! j) (?cfg <!> j))"
    by simp
  then have "sem ?cmd ?cfg <:> j = (?cfg <:> j)(?cfg <#> j := fst (snd (?cmd ?rs) ! j))"
    using act by simp
  then have "sem ?cmd ?cfg <:> j = (?cfg <:> j)(?cfg <#> j := ?cmd ?rs [.] j)" .
  then show ?thesis
    using 1 2 by simp
next
  case False
  let ?cfg = "exec t"
  let ?rs = "config_read ?cfg"
  have len_rs: "length ?rs = k"
    using assms exec_def execute_num_tapes start_config_length read_length tm_M by simp
  then have 1: "sim_write t ! j = ?rs ! j"
    using False by (simp add: sim_write_def)

  have 2: "?rs ! j = exec t <.> j"
    using assms len_rs read_abbrev read_length by auto

  have "exec (Suc t) = exec t"
    using exec_def exe_def False by simp
  then have "exec (Suc t) <:> j = exec t <:> j"
    by simp

  then show ?thesis
    using 1 2 by simp
qed

corollary sim_write':
  assumes "j < k"
  shows "(exec (Suc t) <:> j) (exec t <#> j) = sim_write t ! j"
  using assms sim_write by simp

definition "sim_move t \<equiv> map direction_to_symbol
  (if fst (exec t) < length M
   then map snd (snd ((M ! (fst (exec t))) (config_read (exec t))))
   else replicate k Stay)"

lemma sim_move_nth:
  assumes "fst (exec t) < length M" and "j < k"
  shows "sim_move t ! j = direction_to_symbol ((M ! (fst (exec t))) (config_read (exec t)) [~] j)"
proof -
  have "k = ||execute M (start_config k zs) t||"
    by (metis (no_types) Suc_1 execute_num_tapes start_config_length less_le_trans tm_M turing_machine_def zero_less_Suc)
  then show ?thesis
    by (smt (verit, best) turing_commandD(1) assms(1,2) exec_def length_map nth_map read_length sim_move_def tm_M turing_machineD(3))
qed

lemma sim_move_nth_else:
  assumes "\<not> (fst (exec t) < length M)" and "j < k"
  shows "sim_move t ! j = 1"
  using assms sim_move_def direction_to_symbol_def by simp

lemma sim_move:
  assumes "j < k"
  shows "exec (Suc t) <#> j = exec t <#> j + sim_move t ! j - 1"
proof (cases "fst (exec t) < length M")
  case True
  let ?cfg = "exec t"
  let ?rs = "config_read ?cfg"
  let ?cmd = "M ! (fst ?cfg)"
  have len_rs: "length ?rs = k"
    using assms exec_def execute_num_tapes start_config_length read_length tm_M by simp
  have "turing_command k (length M) G ?cmd"
    using True tm_M turing_machineD(3) by simp
  then have len: "length (snd (?cmd ?rs)) = k"
    using len_rs turing_commandD(1) by simp

  have 1: "sim_move t ! j = direction_to_symbol (?cmd ?rs [~] j)"
    using assms sim_move_nth True by simp

  have "exec (Suc t) = sem ?cmd ?cfg"
    using exec_def True by (simp add: exe_lt_length)
  then have 2: "exec (Suc t) <#> j = sem ?cmd ?cfg <#> j"
    by simp

  have "snd (sem ?cmd ?cfg) = map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd ?rs)) (snd ?cfg))"
    using sem' by simp
  then have "snd (sem ?cmd ?cfg) ! j = (\<lambda>(a, tp). act a tp) ((snd (?cmd ?rs) ! j), (snd ?cfg ! j))"
    using len assms len_rs read_length by simp
  then have "sem ?cmd ?cfg <!> j = act (snd (?cmd ?rs) ! j) (?cfg <!> j)"
    by simp
  then have "sem ?cmd ?cfg <#> j = snd (act (snd (?cmd ?rs) ! j) (?cfg <!> j))"
    by simp
  then have "sem ?cmd ?cfg <#> j =
     (case ?cmd ?rs [~] j of Left \<Rightarrow> ?cfg <#> j - 1 | Stay \<Rightarrow> ?cfg <#> j | Right \<Rightarrow> ?cfg <#> j + 1)"
    using act by simp
  then show ?thesis
    using 1 2 direction_to_symbol_def by (cases "?cmd ?rs [~] j") simp_all
next
  case False
  then have "exec (Suc t) <#> j = exec t <#> j"
    using exec_def exe_def by simp
  moreover have "sim_move t ! j = 1"
    using direction_to_symbol_def sim_move_def assms False by simp
  ultimately show ?thesis
    by simp
qed

definition "tpsL3 t \<equiv> tpsL
  t
  (replicate k (0, Some 0))
  TT
  1
  (\<lambda>j. sim_move t ! j)
  (\<lambda>j. sim_write t ! j)"

lemma read_execute: "config_read (exec t) = map (\<lambda>j. (exec t) <.> j) [0..<k]"
  (is "?lhs = ?rhs")
proof (rule nth_equalityI)
  have len: "length ?lhs = k"
    by (metis Suc_1 exec_def execute_num_tapes start_config_length less_le_trans read_length
      tm_M turing_machine_def zero_less_Suc)
  then show "length ?lhs = length ?rhs"
    by simp
  show "?lhs ! i = ?rhs ! i" if "i < length ?lhs" for i
    using len read_abbrev read_length that by auto
qed

lemma sem_cmdL3: "sem cmdL3 (0, tpsL2 t) = (1, tpsL3 t)"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) cmdL3"
    using cmdL3_def by simp
  show len: "length (tpsL2 t) = 2 * k + 3"
    using tpsL2_def by simp
  show "length (tpsL3 t) = 2 * k + 3"
    using tpsL3_def by simp
  show "fst (cmdL3 (read (tpsL2 t))) = 1"
    by (simp add: cmdL3_def)
  show "act (cmdL3 (read (tpsL2 t)) [!] j) (tpsL2 t ! j) = tpsL3 t ! j" if "j < 2 * k + 3" for j
  proof -
    define rs where "rs = read (tpsL2 t)"
    then have rs2: "rs ! 2 = fst (exec t)"
      using tpsL2_def read_tpsL_2 by simp
    have "drop (k + 3) rs = map (\<lambda>j. exec t <.> j) [0..<k]" (is "?lhs = ?rhs")
    proof (rule nth_equalityI)
      show "length ?lhs = length ?rhs"
        using rs_def read_length tpsL2_def by simp
      then have len_lhs: "length ?lhs = k"
        by simp
      show "?lhs ! i = ?rhs ! i" if "i < length ?lhs" for i
      proof -
        have "i < k"
          using that len_lhs by simp
        have "length rs = 2 * k + 3"
          using rs_def read_length tpsL2_def by simp
        then have "?lhs ! i = rs ! (i + k + 3)"
          by (simp add: add.assoc add.commute)
        also have "... = exec t <.> i"
          unfolding rs_def tpsL2_def using read_tpsL_4[of "i + k + 3"] `i < k` by simp
        finally show ?thesis
          using `i < k` by simp
      qed
    qed
    then have drop: "drop (k + 3) rs = config_read (exec t)"
      using read_execute by simp
    then have drop_less_G: "\<forall>h\<in>set (drop (k + 3) rs). h < G"
      using exec_def tm_M read_alphabet_set zs_less_G by presburger

    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using \<open>j < 2 * k + 3\<close> by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "cmdL3 rs [!] j = (rs ! 0, Stay)"
        using cmdL3_def by simp
      moreover have "tpsL2 t ! j = (\<lfloor>zs\<rfloor>, n + 1)"
        using tpsL2_def 1 by (simp add: tpsL_0)
      moreover have "tpsL3 t ! j = (\<lfloor>zs\<rfloor>, n + 1)"
        using tpsL3_def 1 by (simp add: tpsL_0)
      ultimately show ?thesis
        using act_Stay by (metis 1 len rs_def that)
    next
      case 2
      then have "cmdL3 rs [!] j = (rs ! 1, Stay)"
        using cmdL3_def by simp
      moreover have "tpsL2 t ! j = (zip_cont t (replicate k (0, Some 0)), TT)"
        using tpsL2_def 2 tpsL_1 by simp
      moreover have "tpsL3 t ! j = (zip_cont t (replicate k (0, Some 0)), TT)"
        using tpsL3_def 2 tpsL_1 by simp
      ultimately show ?thesis
        using act_Stay by (metis 2 len rs_def that)
    next
      case 3
      show ?thesis
      proof (cases "rs ! 2 < length M")
        case True
        then have "cmdL3 rs [!] j = (fst ((M ! (rs ! 2)) (drop (k + 3) rs)), Stay)"
          using 3 drop_less_G cmdL3_at_2a by simp
        also have "... = (fst ((M ! (rs ! 2)) (config_read (exec t))), Stay)"
          using drop by simp
        also have "... = (fst (exec (Suc t)), Stay)"
          using True rs2 sim_nextstate sim_nextstate_def by auto
        finally have "cmdL3 rs [!] j = (fst (exec (Suc t)), Stay)" .
        then show ?thesis
          using tpsL2_def tpsL3_def tpsL_def 3 act_onesie rs_def by simp
      next
        case False
        then have "cmdL3 rs [!] j = (rs ! 2, Stay)"
          using 3 cmdL3_at_2b by simp
        moreover have "fst (exec (Suc t)) = rs ! 2"
          using False rs2 sim_nextstate sim_nextstate_def by auto
        ultimately have "cmdL3 rs [!] j = (fst (exec (Suc t)), Stay)"
          by simp
        then show ?thesis
          using tpsL2_def tpsL3_def tpsL_def 3 act_onesie rs_def by simp
      qed
    next
      case 4
      then have 1: "j - 3 < k"
        by auto
      have 2: "tpsL2 t ! j = \<lceil>\<box>\<rceil>"
        using tpsL2_def tpsL_mvs' 4 by simp
      have 3: "tpsL3 t ! j = \<lceil>sim_move t ! (j - 3)\<rceil>"
        using tpsL3_def tpsL_mvs' 4 by simp
      show ?thesis
      proof (cases "rs ! 2 < length M")
        case True
        then have "cmdL3 rs [!] j = (direction_to_symbol ((M ! (rs ! 2)) (drop (k + 3) rs) [~] (j - 3)), Stay)"
          using cmdL3_at_3a 4 drop_less_G by simp
        also have "... = (direction_to_symbol ((M ! (fst (exec t))) (config_read (exec t)) [~] (j - 3)), Stay)"
          using drop True rs2 by simp
        also have "... = (sim_move t ! (j - 3), Stay)"
          using sim_move_nth True 1 rs2 by simp
        finally have "cmdL3 rs [!] j = (sim_move t ! (j - 3), Stay)" .
        then show ?thesis
          using 2 3 act_onesie by (simp add: rs_def)
      next
        case False
        then have "cmdL3 rs [!] j = (1, Stay)"
          using cmdL3_at_3b 4 by simp
        then have "cmdL3 rs [!] j = (sim_move t ! (j - 3), Stay)"
          using sim_move_nth_else False 1 rs2 by simp
        then show ?thesis
          using 2 3 act_onesie by (simp add: rs_def)
      qed
    next
      case 5
      then have 1: "j - k - 3 < k"
        by auto
      have 2: "tpsL2 t ! j = \<lceil>exec t <.> (j - k - 3)\<rceil>"
        using tpsL2_def tpsL_symbs' 5 by simp
      have 3: "tpsL3 t ! j = \<lceil>sim_write t ! (j - k - 3)\<rceil>"
        using tpsL3_def tpsL_symbs' 5 by simp
      show ?thesis
      proof (cases "rs ! 2 < length M")
        case True
        then have "cmdL3 rs [!] j = ((M ! (rs ! 2)) (drop (k + 3) rs) [.] (j - k - 3), Stay)"
          using 5 cmdL3_at_4a drop_less_G by simp
        also have "... = ((M ! (fst (exec t))) (config_read (exec t)) [.] (j - k - 3), Stay)"
          using drop True rs2 by simp
        also have "... = (sim_write t ! (j - k - 3), Stay)"
          using sim_write_nth 5 rs2 True by auto
        finally have "cmdL3 rs [!] j = (sim_write t ! (j - k - 3), Stay)" .
        then show ?thesis
          using 2 3 act_onesie rs_def by simp
      next
        case False
        then have "cmdL3 rs [!] j = (rs ! j, Stay)"
          using 5 cmdL3_at_4b by simp
        also have "... = (exec t <.> (j - k - 3), Stay)"
          using tpsL2_def read_tpsL_4 5 rs_def by simp
        also have "... = (config_read (exec t) ! (j - k - 3), Stay)"
        proof -
          have "length [k..<j] - 3 < k"
            by (metis "1" length_upt)
          then show ?thesis
            using \<open>drop (k + 3) rs = map (\<lambda>j. exec t <.> j) [0..<k]\<close> drop by auto
        qed
        also have "... = (sim_write t ! (j - k - 3), Stay)"
          using sim_write_nth_else False rs2 by simp
        finally have "cmdL3 rs [!] j = (sim_write t ! (j - k - 3), Stay)" .
        then show ?thesis
          using 2 3 act_onesie rs_def by simp
      qed
    qed
  qed
qed

lemma execute_tmL2_3: "execute tmL2_3 (0, tpsL2 t) 1 = (1, tpsL3 t)"
proof -
  have "execute tmL2_3 (0, tpsL2 t) 1 = exe tmL2_3 (execute tmL2_3 (0, tpsL2 t) 0)"
    by simp
  also have "... = exe tmL2_3 (0, tpsL2 t)"
    by simp
  also have "... = sem cmdL3 (0, tpsL2 t)"
    using tmL2_3_def by (simp add: exe_lt_length)
  finally show ?thesis
    using sem_cmdL3 by simp
qed

definition "esL3 t \<equiv> esL2 t @ [(n + 1, TT)]"

lemma tmL3:
  assumes "t < TT"
  shows "traces tmL3 (tpsL0 t) (esL3 t) (tpsL3 t)"
  unfolding tmL3_def esL3_def
proof (rule traces_sequential[OF tmL2[OF assms]])
  show "traces tmL2_3 (tpsL2 t) [(n + 1, Suc (fmt n))] (tpsL3 t)"
  proof
    let ?es = "[(n + 1, TT)]"
    show "execute tmL2_3 (0, tpsL2 t) (length ?es) = (length tmL2_3, tpsL3 t)"
      using tmL2_3_def execute_tmL2_3 by simp
    show "\<And>i. i < length ?es \<Longrightarrow> fst (execute tmL2_3 (0, tpsL2 t) i) < length tmL2_3"
      using tmL2_3_def execute_tmL2_3 by simp
    show "(execute tmL2_3 (0, tpsL2 t) (Suc i)) <#> 0 = fst (?es ! i) \<and>
          (execute tmL2_3 (0, tpsL2 t) (Suc i)) <#> 1 = snd (?es ! i)"
        if "i < length ?es" for i
      using execute_tmL2_3 that tpsL3_def tpsL_pos_0 tpsL_pos_1
      by (metis One_nat_def fst_conv length_Cons less_one list.size(3) nth_Cons_0 snd_conv)
  qed
qed

definition "esL4 t \<equiv> esL3 t @ map (\<lambda>i. (n + 1, i)) (rev [0..<TT]) @ [(n + 1, 0)]"

lemma len_esL4: "length (esL4 t) = t + 2 * TT + 4"
  using esL4_def esL3_def esL2_def esL1_def esL1_2_def by simp

definition "tpsL4 t \<equiv> tpsL
  t
  (replicate k (0, Some 0))
  0
  1
  (\<lambda>j. sim_move t ! j)
  (\<lambda>j. sim_write t ! j)"

lemma tmL4:
  assumes "t < TT"
  shows "traces tmL4 (tpsL0 t) (esL4 t) (tpsL4 t)"
  unfolding tmL4_def esL4_def
proof (rule traces_sequential[where ?tps2.0="tpsL3 t"])
  show "traces tmL3 (tpsL0 t) (esL3 t) (tpsL3 t)" using tmL3 assms .
  show "traces tm_left_until1 (tpsL3 t) (map (Pair (n + 1)) (rev [0..<TT]) @ [(n + 1, 0)]) (tpsL4 t)"
  proof (rule traces_tm_left_until_1I)
    show "1 < length (tpsL3 t)"
      using tpsL3_def by simp
    show "begin_tape {y. y < G ^ (2 * k + 2) + 2 \<and> 1 < y \<and> dec y ! (2 * k + 1) = 1} (tpsL3 t ! 1)"
      using begin_tape_zip_cont tpsL3_def tpsL_def by simp
    show "map (Pair (n + 1)) (rev [0..<TT]) @ [(n + 1, 0)] =
        map (Pair (tpsL3 t :#: 0)) (rev [0..<tpsL3 t :#: 1]) @ [(tpsL3 t :#: 0, 0)]"
      using tpsL3_def tpsL_def by simp
    show "tpsL4 t = (tpsL3 t)[1 := tpsL3 t ! 1 |#=| 0]"
      using tpsL3_def tpsL4_def tpsL_def by simp
  qed
qed

lemma enc_upd_zip_cont_None_Some:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "i = (exec (Suc t) <#> jj)"
  shows "enc_upd (zip_cont t xs i) (k + jj) 1 = zip_cont t (xs[jj:=(1, Some 1)]) i"
proof -
  have "i < TT"
    using assms(1,4) exec_pos_less_TT by metis

  let ?n = "zip_cont t xs i"
  let ?xs = "xs[jj:=(1, Some 1)]"
  have "zip_cont t ?xs i = enc
     (map (\<lambda>j. (exec (t + fst (?xs ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (?xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])"
       (is "_ = enc ?ys")
    using zip_cont_def `i < TT` by simp
  moreover have "?ys = (dec ?n) [k+jj:=1]"
  proof (rule nth_equalityI)
    show len: "length ?ys = length ((dec ?n) [k+jj:=1])"
      by (simp add: \<open>i < TT\<close> dec_zip_cont)
    have lenys: "length ?ys = 2 * k + 2"
      by simp
    show "?ys ! j = (dec ?n) [k+jj:=1] ! j" if "j < length ?ys" for j
    proof -
      consider "j < k" | "k \<le> j \<and> j < 2 * k" | "j = 2 * k" | "j = 2 * k + 1"
        using lenys `j < length ?ys` by linarith
      then show ?thesis
      proof (cases)
        case 1
        then have "?ys ! j = (exec (t + fst (?xs ! j)) <:> j) i"
          using assms(2) by (simp add: less_k_nth)
        have "(dec ?n) [k+jj:=1] ! j = dec ?n ! j"
          using 1 by simp
        also have "... = (exec (t + fst (xs ! j)) <:> j) i"
          by (simp add: "1" \<open>i < TT\<close> dec_zip_cont_less_k)
        also have "... = (exec (t + fst (?xs ! j)) <:> j) i"
          using assms(1-3) by (metis fst_eqD nth_list_update)
        also have "... = ?ys ! j"
          using assms(2) 1 by (simp add: less_k_nth)
        finally show ?thesis
          by simp
      next
        case 2
        show ?thesis
        proof (cases "j = k + jj")
          case True
          then have "?ys ! j = (case snd (?xs ! jj) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> jj then 1 else 0)"
            using assms(2) 2 by (simp add: less_2k_nth)
          also have "... = (if i = exec (t + 1) <#> jj then 1 else 0)"
            by (simp add: assms(1) assms(2))
          also have "... = 1"
            using assms(1,4) by simp
          finally have "?ys ! j = 1" .
          moreover have "(dec ?n) [k+jj:=1] ! j = 1"
            using True len that by simp
          ultimately show ?thesis
            by simp
        next
          case False
          then have *: "?xs ! (j - k) = xs ! (j - k)"
            by (metis "2" add_diff_inverse_nat le_imp_less_Suc not_less_eq nth_list_update_neq)
          have "?ys ! j =
              (case snd (?xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using assms(2) 2 by (simp add: less_2k_nth)
          have "(dec ?n) [k+jj:=1] ! j = (dec ?n) ! j"
            using 2 False by simp
          also have "... =
              (case snd (xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using 2 `i < TT` dec_zip_cont_less_2k by simp
          also have "... = (case snd (?xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using * by simp
          also have "... = ?ys ! j"
            using assms(2) 2 by (simp add: less_2k_nth)
          finally show ?thesis
            by simp
        qed
      next
        case 3
        then have "?ys ! j = (if i < t then 1 else 0)"
          by (simp add: twok_nth)
        moreover have "(dec ?n) [k+jj:=1] ! j = (if i < t then 1 else 0)"
            using 3 assms(1) dec_zip_cont_2k `i < TT` by simp
        ultimately show ?thesis
          by simp
      next
        case 4
        then have "?ys ! j = (if i = 0 then 1 else 0)"
          using twok1_nth by fast
        moreover have "(dec ?n) [k+jj:=1] ! j = (if i = 0 then 1 else 0)"
            using 4 assms(1) dec_zip_cont_2k1 `i < TT` by simp
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  ultimately show ?thesis
    using enc_upd_def by simp
qed

lemma enc_upd_zip_cont_None_Some_Right:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "i = Suc (exec t <#> jj)"
    and "sim_move t ! jj = 2"
  shows "enc_upd (zip_cont t xs i) (k + jj) 1 = zip_cont t (xs[jj:=(1, Some 1)]) i"
proof -
  have "i = (exec (Suc t) <#> jj)"
    using assms sim_move by simp
  then show ?thesis
    using enc_upd_zip_cont_None_Some[OF assms(1-3)] by simp
qed

lemma enc_upd_zip_cont_None_Some_Left:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "Suc i = exec t <#> jj"
    and "sim_move t ! jj = 0"
  shows "enc_upd (zip_cont t xs i) (k + jj) 1 = zip_cont t (xs[jj:=(1, Some 1)]) i"
proof -
  have "i = (exec (Suc t) <#> jj)"
    using assms sim_move by simp
  then show ?thesis
    using enc_upd_zip_cont_None_Some[OF assms(1-3)] by simp
qed

lemma enc_upd_zip_cont_Some_None:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i = exec t <#> jj"
  shows "enc_upd (zip_cont t xs i) (k + jj) 0 = zip_cont t (xs[jj:=(1, None)]) i"
proof -
  have "i < TT"
    using assms(1,4) by (simp add: exec_pos_less_TT)
  let ?n = "zip_cont t xs i"
  let ?xs = "xs[jj:=(1, None)]"
  have "zip_cont t ?xs i = enc
     (map (\<lambda>j. (exec (t + fst (?xs ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (?xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])"
       (is "_ = enc ?ys")
    using zip_cont_def `i < TT` by simp
  moreover have "?ys = (dec ?n) [k+jj:=0]"
  proof (rule nth_equalityI)
    show len: "length ?ys = length ((dec ?n) [k+jj:=0])"
      by (simp add: \<open>i < TT\<close> dec_zip_cont)
    have lenys: "length ?ys = 2 * k + 2"
      by simp
    show "?ys ! j = (dec ?n) [k+jj:=0] ! j" if "j < length ?ys" for j
    proof -
      consider "j < k" | "k \<le> j \<and> j < 2 * k" | "j = 2 * k" | "j = 2 * k + 1"
        using lenys `j < length ?ys` by linarith
      then show ?thesis
      proof (cases)
        case 1
        then have "?ys ! j = (exec (t + fst (?xs ! j)) <:> j) i"
          using assms(2) by (simp add: less_k_nth)
        have "(dec ?n) [k+jj:=0] ! j = dec ?n ! j"
          using 1 by simp
        also have "... = (exec (t + fst (xs ! j)) <:> j) i"
          by (simp add: "1" \<open>i < TT\<close> dec_zip_cont_less_k)
        also have "... = (exec (t + fst (?xs ! j)) <:> j) i"
          using assms(1-3) by (metis fst_eqD nth_list_update)
        also have "... = ?ys ! j"
          using assms(2) 1 by (simp add: less_k_nth)
        finally show ?thesis
          by simp
      next
        case 2
        show ?thesis
        proof (cases "j = k + jj")
          case True
          then have "?ys ! j = (case snd (?xs ! jj) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> jj then 1 else 0)"
            using assms(2) 2 by (simp add: less_2k_nth)
          then have "?ys ! j = 0"
            using assms(1,2) by simp
          moreover have "(dec ?n) [k+jj:=0] ! j = 0"
            using True len that by simp
          ultimately show ?thesis
            by simp
        next
          case False
          then have *: "?xs ! (j - k) = xs ! (j - k)"
            by (metis "2" add_diff_inverse_nat le_imp_less_Suc not_less_eq nth_list_update_neq)
          have "?ys ! j =
              (case snd (?xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using assms(2) 2 by (simp add: less_2k_nth)
          have "(dec ?n) [k+jj:=0] ! j = (dec ?n) ! j"
            using 2 False by simp
          also have "... =
              (case snd (xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using 2 `i < TT` dec_zip_cont_less_2k by simp
          also have "... = (case snd (?xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using * by simp
          also have "... = ?ys ! j"
            using assms(2) 2 by (simp add: less_2k_nth)
          finally show ?thesis
            by simp
        qed
      next
        case 3
        then have "?ys ! j = (if i < t then 1 else 0)"
          by (simp add: twok_nth)
        moreover have "(dec ?n) [k+jj:=0] ! j = (if i < t then 1 else 0)"
            using 3 assms(1) dec_zip_cont_2k `i < TT` by simp
        ultimately show ?thesis
          by simp
      next
        case 4
        then have "?ys ! j = (if i = 0 then 1 else 0)"
          using twok1_nth by fast
        moreover have "(dec ?n) [k+jj:=0] ! j = (if i = 0 then 1 else 0)"
            using 4 assms(1) dec_zip_cont_2k1 `i < TT` by simp
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  ultimately show ?thesis
    using enc_upd_def by simp
qed

lemma zip_cont_nth_eq_updI1:
  assumes "i < TT"
    and "jj < k"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "(exec (Suc t) <:> jj) i = u"
  shows "enc_upd (zip_cont t xs i) jj u = zip_cont t (xs[jj:=(1, Some 0)]) i"
proof -
  let ?n = "zip_cont t xs i"
  let ?xs = "xs[jj:=(1, Some 0)]"
  have "zip_cont t ?xs i = enc
     (map (\<lambda>j. (exec (t + fst (?xs ! j)) <:> j) i) [0..<k] @
      map (\<lambda>j. case snd (?xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [if i < t then 1 else 0,
       if i = 0 then 1 else 0])"
       (is "_ = enc ?ys")
    using zip_cont_def assms(1) by simp
  moreover have "?ys = (dec ?n) [jj:=u]"
  proof (rule nth_equalityI)
    show len_eq: "length ?ys = length ((dec ?n) [jj:=u])"
      using assms(1) dec_zip_cont two_tape_axioms zs_proper zs_less_G by simp
    have lenys: "length ?ys = 2 * k + 2"
      by simp
    show "?ys ! j = (dec ?n) [jj:=u] ! j" if "j < length ?ys" for j
    proof -
      consider "j < k" | "k \<le> j \<and> j < 2 * k" | "j = 2 * k" | "j = 2 * k + 1"
        using lenys `j < length ?ys` by linarith
      then show ?thesis
      proof (cases)
        case 1
        then have *: "?ys ! j = (exec (t + fst (?xs ! j)) <:> j) i"
          by (simp add: less_k_nth)
        show ?thesis
        proof (cases "j = jj")
          case True
          then have "?ys ! j = (exec (Suc t) <:> j) i"
            using 1 assms(3) * by simp
          moreover have "(dec ?n) [jj:=u] ! j = u"
            using True len_eq that by simp
          ultimately show ?thesis
            using assms(5) True by simp
        next
          case False
          then have "(dec ?n) [jj:=u] ! j = (exec (t + fst (xs ! j)) <:> j) i"
            using dec_zip_cont_less_k 1 assms(1) by simp
          moreover have "?ys ! j = (exec (t + fst (xs ! j)) <:> j) i"
            using False * by simp
          ultimately show ?thesis
            by simp
        qed
      next
        case 2
        then have *: "?ys ! j =
            (case snd (?xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
          by (simp add: less_2k_nth)
        show ?thesis
        proof (cases "j = k + jj")
          case True
          then have "j - k = jj"
            by simp
          then have "snd (?xs ! (j - k)) = Some 0"
            using assms(2,3) by simp
          then have lhs: "?ys ! j = (if i = exec t <#> jj then 1 else 0)"
            using * True by simp
          have "(dec ?n) [jj:=u] ! j = (dec ?n) ! j"
            using True assms(2) by simp
          also have "...  =
              (case snd (xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using True 2 assms(1,4) dec_zip_cont_less_2k by simp
          also have "... = (if i = exec t <#> jj then 1 else 0)"
            using True assms(4) by simp
          finally have "(dec ?n) [jj:=u] ! j = (if i = exec t <#> jj then 1 else 0)" .
          then show ?thesis
            using lhs True by simp
        next
          case False
          then have "j - k \<noteq> jj"
            using 2 by auto
          then have "snd (?xs ! (j - k)) = snd (xs ! (j - k))"
            by simp
          then have lhs: "?ys ! j =
              (case snd (xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using * by simp
          have "(dec ?n) [jj:=u] ! j = (dec ?n) ! j"
            using 2 assms(2) by simp
          then have "(dec ?n) [jj:=u] ! j =
              (case snd (xs ! (j - k)) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> (j - k) then 1 else 0)"
            using False 2 assms(1) dec_zip_cont_less_2k by simp
          then show ?thesis
            using lhs by simp
        qed
      next
        case 3
        then have "?ys ! j = (if i < t then 1 else 0)"
          by (simp add: twok_nth)
        moreover have "(dec ?n) [jj:=u] ! j = (if i < t then 1 else 0)"
            using 3 assms(1,2) dec_zip_cont_2k by simp
        ultimately show ?thesis
          by simp
      next
        case 4
        then have "?ys ! j = (if i = 0 then 1 else 0)"
          using twok1_nth by fast
        moreover have "(dec ?n) [jj:=u] ! j = (if i = 0 then 1 else 0)"
            using 4 assms(1,2) dec_zip_cont_2k1 by simp
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  ultimately show ?thesis
    using enc_upd_def by simp
qed

lemma zip_cont_upd_eq:
  assumes "jj < k"
    and "i = exec t <#> jj"
    and "i < TT"
    and "xs ! jj = (0, Some 0)"
    and "length xs = k"
  shows "(zip_cont t xs)(i:=enc_upd (zip_cont t xs i) jj (sim_write t ! jj)) =
      zip_cont t (xs[jj:=(1, Some 0)])"
    (is "?lhs = ?rhs")
proof
  fix p
  consider "p < TT \<and> p \<noteq> i" | "p < TT \<and> p = i" | "p \<ge> TT"
    by linarith
  then show "?lhs p = ?rhs p"
  proof (cases)
    case 1
    then have "?lhs p = zip_cont t xs p"
      by simp
    moreover have "zip_cont t xs p = zip_cont t (xs[jj:=(1, Some 0)]) p"
    proof (rule zip_cont_nth_eqI)
      show "p < TT"
        using 1 by simp
      show "(exec (t + fst (xs ! j)) <:> j) p =
              (exec (t + fst (xs[jj := (1, Some 0)] ! j)) <:> j) p"
          if "j < k" for j
      proof (cases "j = jj")
        case True
        then have "fst (xs[jj := (1, Some 0)] ! j) = 1"
          using assms(1,5) by simp
        then have "(exec (t + fst (xs[jj := (1, Some 0)] ! j)) <:> j) p = (exec (Suc t) <:> j) p"
          by simp
        also have "... = (exec t <:> j) p"
          using assms(2) 1 by (simp add: True assms(1) sim_write)
        finally show ?thesis
          using assms(4) True by simp
      next
        case False
        then show ?thesis
          by simp
      qed
      show "snd (xs ! j) = snd (xs[jj := (1, Some 0)] ! j)" if "j < k" for j
        using assms(4,5) that by (cases "j = jj") simp_all
    qed
    ultimately show ?thesis
      by simp
  next
    case 2
    then have "?lhs p = enc_upd (zip_cont t xs i) jj (sim_write t ! jj)"
      by simp
    then show ?thesis
      using 2 assms(1,2,4,5) sim_write' zip_cont_nth_eq_updI1 by auto
  next
    case 3
    then show ?thesis
      using zip_cont_def assms(3) by auto
  qed
qed

lemma sem_cmdL5_neq_pos:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "snd (xs ! jj) = Some 0"
    and "i \<noteq> exec t <#> jj"
    and "i < TT"
    and "tps' = tpsL t xs (Suc i) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL5 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL5 jj)"
    using turing_command_cmdL5[OF assms(1)] turing_commandD(1) by simp
  show "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(6) by simp
  let ?rs = "read tps"
  have rs1: "?rs ! 1 \<noteq> \<box>"
    using read_tpsL_1_bounds assms(2,5) by (metis not_one_less_zero)
  then show "fst (cmdL5 jj ?rs) = 0"
    by (simp add: cmdL5_def)
  show "act (cmdL5 jj ?rs [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_0 by simp
      then show ?thesis
        using assms tpsL_0 1 by (metis act_Stay that length_tpsL)
    next
      case 2
      then have "enc_nth (?rs ! 1) (k + jj) = (if i = exec t <#> jj then 1 else 0)"
        using assms read_tpsL_1_nth_less_2k by simp
      then have "enc_nth (?rs ! 1) (k + jj) = 0"
        using assms(4) by simp
      then have "\<not> (1 < ?rs ! 1 \<and> ?rs ! 1 < G^(2*k+2)+2 \<and> ?rs ! (3+k+jj) < G \<and> enc_nth (?rs!1) (k+jj) = 1)"
        by simp
      then have "cmdL5 jj ?rs [!] 1 = (?rs ! 1, Right)"
        using cmdL5_at_1_else rs1 by simp
      then show ?thesis
        using assms tpsL_1 2 act_Right that length_tpsL by (metis Suc_eq_plus1 prod.sel(1) tpsL_pos_1)
    next
      case 3
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_2 by simp
      then show ?thesis
        using assms tpsL_2 3 by (metis act_Stay that length_tpsL)
    next
      case 4
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_3 by simp
      then have "act (cmdL5 jj ?rs [!] j) (tps ! j) = tps ! j"
        using act_Stay by (simp add: \<open>length tps = 2 * k + 3\<close> that)
      then show ?thesis
        using assms tpsL_mvs' by (simp add: "4" add.commute)
    next
      case 5
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_4 by simp
      then have "act (cmdL5 jj ?rs [!] j) (tps ! j) = tps ! j"
        using act_Stay by (simp add: \<open>length tps = 2 * k + 3\<close> that)
      then show ?thesis
        using assms tpsL_symbs' 5 by simp
    qed
  qed
qed

lemma sem_cmdL5_eq_pos:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "xs ! jj = (0, Some 0)"
    and "i = exec t <#> jj"
    and "tps' = tpsL t (xs[jj:=(1, Some 0)]) (Suc i) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
  shows "sem (cmdL5 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  have "i < TT"
    using exec_pos_less_TT assms(1,4) by simp
  show "proper_command (2 * k + 3) (cmdL5 jj)"
    using turing_command_cmdL5[OF assms(1)] turing_commandD(1) by simp
  show "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(5) by simp
  let ?rs = "read tps"
  have rs1: "?rs ! 1 \<noteq> \<box>"
    using read_tpsL_1_bounds assms(2) `i < TT` by (metis not_one_less_zero)
  then show "fst (cmdL5 jj ?rs) = 0"
    by (simp add: cmdL5_def)
  show "act (cmdL5 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_0 by simp
      then show ?thesis
        using assms tpsL_0 1 by (metis act_Stay that length_tpsL)
    next
      case 2
      then have "enc_nth (?rs ! 1) (k + jj) = (if i = exec t <#> jj then 1 else 0)"
        using assms `i < TT` read_tpsL_1_nth_less_2k by simp
      then have "enc_nth (?rs ! 1) (k + jj) = 1"
        using assms(4) by simp
      moreover have "1 < ?rs ! 1 \<and> ?rs ! 1 < G^(2*k+2)+2"
        using assms(2) `i < TT` read_tpsL_1_bounds by auto
      moreover have "?rs ! (3+k+jj) < G"
        using read_tpsL_4 assms sim_write_nth_less_G[OF assms(1)] by simp
      ultimately have
        "1 < ?rs ! 1 \<and> ?rs ! 1 < G^(2*k+2)+2 \<and> ?rs ! (3+k+jj) < G \<and> enc_nth (?rs!1) (k+jj) = 1"
        by simp
      then have "cmdL5 jj ?rs [!] 1 = (enc_upd (?rs!1) jj (?rs!(3+k+jj)), Right)"
        using cmdL5_at_1 rs1 by simp
      moreover have "?rs!(3+k+jj) = sim_write t ! jj"
        by (simp add: assms(1,2) read_tpsL_4)
      ultimately have *: "cmdL5 jj ?rs [!] 1 = (enc_upd (?rs ! 1) jj (sim_write t ! jj), Right)"
        by simp

      have "?rs ! 1 = zip_cont t xs i"
        using assms(2) read_tpsL_1 zip_cont_def by auto

      let ?tp = "act (enc_upd (?rs ! 1) jj (sim_write t ! jj), Right) (tps ! j)"
      have "?tp = tps' ! 1"
      proof -
        have "?tp = ((zip_cont t xs)(i:=enc_upd (?rs ! 1) jj (sim_write t ! jj)), Suc i)"
          using act_Right' assms tpsL_1
          by (metis "2" add.commute fst_conv plus_1_eq_Suc snd_conv)
        moreover have "tps' ! 1 = (zip_cont t (xs[jj:=(1, Some 0)]), Suc i)"
          using assms(5) tpsL_1 by simp
        moreover have "(zip_cont t xs)(i:=enc_upd (?rs ! 1) jj (sim_write t ! jj)) =
            zip_cont t (xs[jj:=(1, Some 0)])"
          using zip_cont_upd_eq assms `i < TT` \<open>read tps ! 1 = zip_cont t xs i\<close> by auto
        ultimately show ?thesis
          by auto
      qed
      then show ?thesis
        using 2 * by simp
    next
      case 3
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_2 by simp
      then show ?thesis
        using assms tpsL_2 3 by (metis act_Stay that length_tpsL)
    next
      case 4
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_3 by simp
      then have "act (cmdL5 jj ?rs [!] j) (tps ! j) = tps ! j"
        using act_Stay by (simp add: \<open>length tps = 2 * k + 3\<close> that)
      then show ?thesis
        using assms tpsL_mvs' by (simp add: "4" add.commute)
    next
      case 5
      then have "cmdL5 jj ?rs [!] j = (?rs ! j, Stay)"
        using rs1 cmdL5_at_4 by simp
      then have "act (cmdL5 jj ?rs [!] j) (tps ! j) = tps ! j"
        using act_Stay by (simp add: \<open>length tps = 2 * k + 3\<close> that)
      then show ?thesis
        using assms tpsL_symbs' 5 by simp
    qed
  qed
qed

lemma sem_cmdL5_eq_TT:
  assumes "jj < k" and "tps = tpsL t xs TT q mvs symbs"
  shows "sem (cmdL5 jj) (0, tps) = (1, tps)"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL5 jj)"
    using turing_command_cmdL5[OF assms(1)] turing_commandD(1) by simp
  show "length tps = 2 * k + 3"
    using assms(2) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  let ?rs = "read tps"
  have rs1: "?rs ! 1 = \<box>"
    using read_tpsL_1 assms(2) by simp
  then show "fst (cmdL5 jj ?rs) = 1"
    by (simp add: cmdL5_def)
  show "\<And>i. i < 2 * k + 3 \<Longrightarrow> act (cmdL5 jj ?rs [!] i) (tps ! i) = tps ! i"
    using len rs1 act_Stay cmdL5_eq_0 read_length by auto
qed

lemma execute_tmL45_1:
  assumes "tt \<le> exec t <#> jj"
    and "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL45 jj) (0, tps) tt = (0, tps')"
  using assms(1,5)
proof (induction tt arbitrary: tps')
  case 0
  then show ?case
    using assms(2-4) by simp
next
  case (Suc tt)
  then have tt_neq: "tt \<noteq> exec t <#> jj"
    by simp
  have tt_le: "tt \<le> exec t <#> jj"
    using Suc.prems by simp
  then have tt_less: "tt < TT"
    using exec_pos_less_TT assms(2) by (meson le_trans less_Suc_eq_le)
  define tps_tt where "tps_tt = tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  have "execute (tmL45 jj) (0, tps) (Suc tt) = exe (tmL45 jj) (execute (tmL45 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL45 jj) (0, tps_tt)"
    using Suc.IH assms(2-4) tt_le tps_tt_def by simp
  also have "... = sem (cmdL5 jj) (0, tps_tt)"
    using tmL45_def exe_lt_length by simp
  also have "... = (0, tpsL t xs (Suc tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using sem_cmdL5_neq_pos assms(2-4) tt_neq tt_less by (simp add: tps_tt_def)
  finally show ?case
    by (simp add: Suc.prems(2))
qed

lemma execute_tmL45_2:
  assumes "tt = exec t <#> jj"
    and "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t (xs[jj:=(1, Some 0)]) (Suc tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
  shows "execute (tmL45 jj) (0, tps) (Suc tt) = (0, tps')"
proof -
  have "execute (tmL45 jj) (0, tps) (Suc tt) = exe (tmL45 jj) (execute (tmL45 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL45 jj) (0, tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using execute_tmL45_1 assms by simp
  also have "... = sem (cmdL5 jj) (0, tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using tmL45_def exe_lt_length by simp
  also have "... = (0, tpsL t (xs[jj:=(1, Some 0)]) (Suc tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using sem_cmdL5_eq_pos[OF assms(2)] assms by simp
  finally show ?thesis
    using assms(5) by simp
qed

lemma execute_tmL45_3:
  assumes "tt \<ge> Suc (exec t <#> jj)"
    and "tt \<le> TT"
    and "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t (xs[jj:=(1, Some 0)]) tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
  shows "execute (tmL45 jj) (0, tps) tt = (0, tps')"
  using assms(1,2,6)
proof (induction tt arbitrary: tps' rule: nat_induct_at_least)
  case base
  then show ?case
    using assms(3-5,7) execute_tmL45_2 by simp
next
  case (Suc tt)
  then have tt: "tt < TT" "tt \<noteq> exec t <#> jj"
    by simp_all
  have "execute (tmL45 jj) (0, tps) (Suc tt) = exe (tmL45 jj) (execute (tmL45 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL45 jj) (0, tpsL t (xs[jj:=(1, Some 0)]) tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using Suc by simp
  also have "... = sem (cmdL5 jj) (0, tpsL t (xs[jj:=(1, Some 0)]) tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using tmL45_def exe_lt_length by simp
  also have "... = (0, tpsL t (xs[jj:=(1, Some 0)]) (Suc tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using sem_cmdL5_neq_pos tt by (simp add: assms(3) assms(7))
  finally show ?case
    using Suc(4) by presburger
qed

lemma execute_tmL45_4:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t (xs[jj:=(1, Some 0)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
  shows "execute (tmL45 jj) (0, tps) (Suc TT) = (1, tps')"
proof -
  have "execute (tmL45 jj) (0, tps) (Suc TT) = exe (tmL45 jj) (execute (tmL45 jj) (0, tps) TT)"
    by simp
  also have "... = exe (tmL45 jj) (0, tps')"
    using assms execute_tmL45_3 by (metis Suc_leI exec_pos_less_TT order_refl)
  also have "... = sem (cmdL5 jj) (0, tps')"
    using tmL45_def exe_lt_length by simp
  also have "... = (1, tps')"
    using sem_cmdL5_eq_TT assms(1,4) by simp
  finally show ?thesis .
qed

definition "esL45 \<equiv> map (\<lambda>i. (n + 1, Suc i)) [0..<TT] @ [(n + 1, TT)]"

lemma len_esL45: "length esL45 = Suc TT"
  using esL45_def by simp

lemma nth_map_upt_TT:
  fixes es
  assumes "es = map f [0..<TT] @ es'" and "i < TT"
  shows "es ! i = f i"
  using assms by (metis add.left_neutral diff_zero length_map length_upt nth_append nth_map nth_upt)

lemma tmL45:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t (xs[jj:=(1, Some 0)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL45 jj) tps esL45 tps'"
proof
  show "execute (tmL45 jj) (0, tps) (length esL45) = (length (tmL45 jj), tps')"
    using tmL45_def execute_tmL45_4 esL45_def assms by simp
  show "fst (execute (tmL45 jj) (0, tps) i) < length (tmL45 jj)" if "i < length esL45" for i
  proof -
    have "i \<le> TT"
      using esL45_def that by simp
    then consider "i \<le> exec t <#> jj" | "i = Suc (exec t <#> jj)" | "i > Suc (exec t <#> jj) \<and> i \<le> TT"
      by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using assms execute_tmL45_1 tmL45_def by simp
    next
      case 2
      then show ?thesis
        using assms execute_tmL45_2 tmL45_def by simp
    next
      case 3
      then show ?thesis
        using assms execute_tmL45_3 tmL45_def by simp
    qed
  qed
  show "execute (tmL45 jj) (0, tps) (Suc i) <#> 0 = fst (esL45 ! i) \<and>
        execute (tmL45 jj) (0, tps) (Suc i) <#> 1 = snd (esL45 ! i)"
    if "i < length esL45" for i
  proof -
    have "i \<le> TT"
      using esL45_def that by simp
    then consider "i < exec t <#> jj" | "i = exec t <#> jj" | "i \<ge> Suc (exec t <#> jj) \<and> i < TT" | "i = TT"
      by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "Suc i \<le> exec t <#> jj"
        by simp
      then have "i < TT"
        using exec_pos_less_TT by (metis \<open>i \<le> TT\<close> assms(1) nat_less_le not_less_eq_eq)
      then have "esL45 ! i = (n + 1, Suc i)"
        using esL45_def nth_map_upt_TT by auto
      then show ?thesis
        using assms execute_tmL45_1 tpsL_pos_0 tpsL_pos_1 by (metis \<open>Suc i \<le> exec t <#> jj\<close> fst_conv snd_conv)
    next
      case 2
      then have "i < TT"
        using exec_pos_less_TT by (simp add: assms(1))
      then have "esL45 ! i = (n + 1, Suc i)"
        using esL45_def nth_map_upt_TT by auto
      then show ?thesis
        using assms execute_tmL45_2 tpsL_pos_0 tpsL_pos_1 by (metis 2 fst_conv snd_conv)
    next
      case 3
      then have "esL45 ! i = (n + 1, Suc i)"
        using esL45_def nth_map_upt_TT by auto
      then show ?thesis
        using assms execute_tmL45_3 tpsL_pos_0 tpsL_pos_1 3
        by (metis Suc_leI fst_conv le_imp_less_Suc nat_less_le snd_conv)
    next
      case 4
      then have "esL45 ! i = (n + 1, TT)"
        using esL45_def by (simp add: nth_append)
      then show ?thesis
        using assms execute_tmL45_4 tpsL_pos_0 tpsL_pos_1 4 by simp
    qed
  qed
qed

definition "esL46 \<equiv> esL45 @ [(n + 1, fmt n)]"

lemma len_esL46: "length esL46 = TT + 2"
  using len_esL45 esL46_def by simp

lemma tmL46:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t (xs[jj:=(1, Some 0)]) (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL46 jj) tps esL46 tps'"
  unfolding tmL46_def esL46_def
proof (rule traces_sequential)
  let ?tps = "tpsL t (xs[jj:=(1, Some 0)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  show "traces (tmL45 jj) tps esL45 ?tps"
    using tmL45 assms by simp
  show "traces (tm_left 1) ?tps [(n + 1, fmt n)] tps'"
    using tpsL_pos_0 tpsL_pos_1 assms tpsL_def tpsL_1
    by (intro traces_tm_left_1I) simp_all
qed

lemma sem_cmdL7_nonleft_gt_0:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "i < TT"
    and "i > 0"
    and "sim_move t ! jj \<noteq> 0"
    and "tps' = tpsL t xs (i - 1) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL7 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL7 jj)"
    using turing_command_cmdL7[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(7) by simp
  define rs where "rs = read tps"
  then have "\<not> is_beginning (rs ! 1)"
    using read_tpsL_1_nth_2k1 assms
    by (metis enc_nth_dec nat_neq_iff numerals(1) zero_neq_numeral)
  then show "fst (cmdL7 jj rs) = 0"
    unfolding cmdL7_def by simp

  have "rs ! (3 + jj) = sim_move t ! jj"
    using rs_def assms(1,2) read_tpsL_3 by simp
  moreover have "sim_move t ! jj < 3"
    using sim_move_def assms(1) direction_to_symbol_less sim_move_nth sim_move_nth_else
    by (metis One_nat_def not_add_less2 not_less_eq numeral_3_eq_3 plus_1_eq_Suc)
  ultimately have "condition7c rs jj"
    using assms(6) by simp
  then have *: "snd (cmdL7 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Left),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL7_def by auto

  show "act (cmdL7 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,7) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (rs ! 1, Left) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps' ! 1"
        using act_Left len rs_def assms tpsL_1 by (metis 2 fst_conv that tpsL_pos_1)
      also have "... = tps' ! j"
        using 2 by simp
      finally show ?thesis .
    next
      case 3
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,7) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_mvs' 4 by simp
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma sem_cmdL7_nonleft_eq_0:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "sim_move t ! jj \<noteq> 0"
  shows "sem (cmdL7 jj) (0, tps) = (1, tps)"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL7 jj)"
    using turing_command_cmdL7[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps = 2 * k + 3"
    using assms(2) by simp

  define rs where "rs = read tps"
  then have "is_beginning (rs ! 1)"
    using read_tpsL_1_nth_2k1 assms enc_nth_def read_tpsL_1_bounds zero_less_Suc
    by simp
  then show "fst (cmdL7 jj (read tps)) = 1"
    using cmdL7_def rs_def by simp

  have "rs ! (3 + jj) = sim_move t ! jj"
    using rs_def assms(1,2) read_tpsL_3 by simp
  then have "condition7c rs jj"
    using sim_move direction_to_symbol_less sim_move_nth sim_move_nth_else assms(1,4)
    by (metis less_Suc_eq not_add_less2 numeral_3_eq_3 numeral_eq_iff numerals(1) plus_1_eq_Suc semiring_norm(86))
  then have *: "snd (cmdL7 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Left),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL7_def by auto

  show "act (cmdL7 jj (read tps) [!] j) (tps ! j) = tps ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using * act_Stay assms(2) rs_def by simp
    next
      case 2
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! 1, Left) (tps ! j)"
        using * rs_def by simp
      also have "... = tps ! j"
        using 2 assms(2) act_Left that length_tpsL tpsL_1 tpsL_pos_1 rs_def
        by (metis diff_is_0_eq' fst_conv less_numeral_extra(1) nat_less_le)
      finally show ?thesis
        by simp
    next
      case 3
      then show ?thesis
        using * act_Stay assms(2) rs_def by simp
    next
      case 4
      then show ?thesis
        using * act_Stay assms rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] len by simp
    next
      case 5
      then show ?thesis
        using * act_Stay assms rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] len by simp
    qed
  qed
qed

lemma execute_tmL67_nonleft_less:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "sim_move t ! jj \<noteq> 0"
    and "tt < TT"
    and "tps' = tpsL t xs (fmt n - tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL67 jj) (0, tps) tt = (0, tps')"
  using assms(5,6)
proof (induction tt arbitrary: tps')
  case 0
  then show ?case
    using assms(1-4) tmL67_def by simp
next
  case (Suc tt)
  have "execute (tmL67 jj) (0, tps) (Suc tt) = exe (tmL67 jj) (execute (tmL67 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL67 jj) (0, tpsL t xs (fmt n - tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using Suc by simp
  finally show ?case
    using assms(1-4) sem_cmdL7_nonleft_gt_0 tmL67_def exe_lt_length Suc by simp
qed

lemma execute_tmL67_nonleft_finish:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "sim_move t ! jj \<noteq> 0"
    and "tps' = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL67 jj) (0, tps) TT = (1, tps')"
  using assms execute_tmL67_nonleft_less sem_cmdL7_nonleft_eq_0 tmL67_def exe_lt_length
  by simp

definition "esL67 \<equiv> map (\<lambda>i. (n + 1, i)) (rev [0..<fmt n]) @ [(n + 1, 0)]"

lemma esL67_at_fmtn [simp]: "esL67 ! (fmt n) = (n + 1, 0)"
  using esL67_def by (simp add: nth_append)

lemma esL67_at_lt_fmtn [simp]: "i < fmt n \<Longrightarrow> esL67 ! i = (n + 1, fmt n - i - 1)"
proof -
  assume "i < fmt n"
  then have "(rev [0..<fmt n]) ! i = fmt n - 1 - i"
    by (metis Suc_diff_1 add.left_neutral bot_nat_0.extremum diff_diff_add diff_less_Suc diff_zero
      length_upt less_nat_zero_code nat_less_le nth_upt plus_1_eq_Suc rev_nth)
  moreover have "length (map (Pair (Suc n)) (rev [0..<fmt n])) = fmt n"
    by simp
  ultimately show ?thesis
    by (simp add: \<open>i < fmt n\<close> esL67_def nth_append)
qed

lemma tmL67_nonleft:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "sim_move t ! jj \<noteq> 0"
    and "tps' = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL67 jj) tps esL67 tps'"
proof
  have len: "length esL67 = TT"
    using esL67_def by simp
  then show 1: "execute (tmL67 jj) (0, tps) (length esL67) = (length (tmL67 jj), tps')"
    using assms tmL67_def execute_tmL67_nonleft_finish by simp
  show "\<And>i. i < length esL67 \<Longrightarrow>
        fst (execute (tmL67 jj) (0, tps) i) < length (tmL67 jj)"
    using len assms execute_tmL67_nonleft_less tmL67_def by simp
  show "(execute (tmL67 jj) (0, tps) (Suc i)) <#> 0 = fst (esL67 ! i) \<and>
        (execute (tmL67 jj) (0, tps) (Suc i)) <#> 1 = snd (esL67 ! i)"
      if "i < length esL67" for i
  proof (cases "i = fmt n")
    case True
    then show ?thesis
      using assms that 1 tpsL_pos_0 tpsL_pos_1 len by simp
  next
    case False
    then have "Suc i < TT"
      using that len by simp
    moreover from this have "esL67 ! i = (n + 1, fmt n - 1 - i)"
      by simp
    ultimately show ?thesis
      using tpsL_pos_0 tpsL_pos_1 assms(1-5) execute_tmL67_nonleft_less
      by (metis (no_types, lifting) diff_diff_left fst_conv plus_1_eq_Suc snd_conv)
  qed
qed

lemma sem_cmdL7_1:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i < TT"
    and "i > exec t <#> jj"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t xs (i - 1) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL7 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL7 jj)"
    using turing_command_cmdL7[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(8) by simp

  define rs where "rs = read tps"
  then have not_beginning: "\<not> is_beginning (rs ! 1)"
    using read_tpsL_1_nth_2k1 assms enc_nth_def read_tpsL_1_bounds zero_less_Suc
    by simp
  then show "fst (cmdL7 jj (read tps)) = 0"
    using cmdL7_def rs_def by simp

  have "rs ! (3 + jj) = \<box>"
    using rs_def read_tpsL_3 assms by simp
  moreover have "enc_nth (rs ! 1) (k + jj) = 0"
    using assms rs_def read_tpsL_1_nth_less_2k by simp
  ultimately have "condition7c rs jj"
    using not_beginning by simp
  then have *: "snd (cmdL7 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Left),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL7_def by auto

  show "act (cmdL7 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,8) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (rs ! 1, Left) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps' ! 1"
        using act_Left len rs_def assms tpsL_1 by (metis 2 fst_conv that tpsL_pos_1)
      also have "... = tps' ! j"
        using 2 by simp
      finally show ?thesis .
    next
      case 3
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,8) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,8) tpsL_mvs' 4 by simp
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,8) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL67_1:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "tt < TT - exec t <#> jj"
    and "tps' = tpsL t xs (fmt n - tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL67 jj) (0, tps) tt = (0, tps')"
  using assms(6,7)
proof (induction tt arbitrary: tps')
  case 0
  then show ?case
    by (simp add: assms(2))
next
  case (Suc tt)
  then have "execute (tmL67 jj) (0, tps) (Suc tt) = sem (cmdL7 jj) (execute (tmL67 jj) (0, tps) tt)"
    using exe_lt_length tmL67_def by simp
  then show ?case
    using assms(1-5) sem_cmdL7_1 Suc by simp
qed

lemma zip_cont_enc_upd_Some:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "i = exec (Suc t) <#> jj"
  shows "(zip_cont t xs)(i:=(enc_upd (zip_cont t xs i) (k + jj) 1)) = zip_cont t (xs[jj:=(1, Some 1)])"
    (is "?lhs = ?rhs")
proof
  fix p
  have "i < TT"
    using assms(1,4) exec_pos_less_TT by simp

  consider "p < TT \<and> p \<noteq> i" | "p < TT \<and> p = i" | "p \<ge> TT"
    by linarith
  then show "?lhs p = ?rhs p"
  proof (cases)
    case 1
    then have "?lhs p = zip_cont t xs p"
      by simp
    moreover have "zip_cont t xs p = zip_cont t (xs[jj:=(1, Some 1)]) p"
    proof (rule zip_cont_eqI)
      show "p < TT"
        using 1 by simp
      show "(exec (t + fst (xs ! j)) <:> j) p = (exec (t + fst (xs[jj := (1, Some 1)] ! j)) <:> j) p"
        if "j < k" for j
        using assms(1-3) by (cases "j = jj") simp_all
      show "(case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if p = (exec (t + d)) <#> j then 1 else 0) =
        (case snd (xs[jj := (1, Some 1)] ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if p = (exec (t + d)) <#> j then 1 else 0)"
          (is "?lhs = ?rhs")
        if "j < k" for j
      proof (cases "j = jj")
        case True
        then show ?thesis
          using 1 assms by simp
      next
        case False
        then show ?thesis
          by simp
      qed
    qed
    ultimately show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      using assms enc_upd_zip_cont_None_Some by simp
  next
    case 3
    then show ?thesis
      using `i < TT` zip_cont_eq_0 by simp
  qed
qed

lemma zip_cont_enc_upd_Some_Right:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "i = Suc (exec t <#> jj)"
    and "sim_move t ! jj = 2"
  shows "(zip_cont t xs)(i:=(enc_upd (zip_cont t xs i) (k + jj) 1)) = zip_cont t (xs[jj:=(1, Some 1)])"
proof -
  have "i = exec (Suc t) <#> jj"
    using assms sim_move by simp
  then show ?thesis
    using zip_cont_enc_upd_Some[OF assms(1-3)] by simp
qed

lemma zip_cont_enc_upd_Some_Left:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "Suc i = exec t <#> jj"
    and "sim_move t ! jj = 0"
  shows "(zip_cont t xs)(i:=(enc_upd (zip_cont t xs i) (k + jj) 1)) = zip_cont t (xs[jj:=(1, Some 1)])"
    (is "?lhs = ?rhs")
proof -
  have "i = exec (Suc t) <#> jj"
    using assms sim_move by simp
  then show ?thesis
    using zip_cont_enc_upd_Some[OF assms(1-3)] by simp
qed

lemma zip_cont_enc_upd_None:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i = exec t <#> jj"
  shows "(zip_cont t xs)(i:=(enc_upd (zip_cont t xs i) (k + jj) 0)) = zip_cont t (xs[jj:=(1, None)])"
    (is "?lhs = ?rhs")
proof
  fix p
  consider "p < TT \<and> p \<noteq> i" | "p < TT \<and> p = i" | "p \<ge> TT"
    by linarith
  then show "?lhs p = ?rhs p"
  proof (cases)
    case 1
    then have "?lhs p = zip_cont t xs p"
      by simp
    moreover have "zip_cont t xs p = zip_cont t (xs[jj:=(1, None)]) p"
    proof (rule zip_cont_eqI)
      show "p < TT"
        using 1 by simp
      show "(exec (t + fst (xs ! j)) <:> j) p = (exec (t + fst (xs[jj := (1, None)] ! j)) <:> j) p"
        if "j < k" for j
        using assms(1-3) by (cases "j = jj") simp_all
      show "(case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if p = (exec (t + d)) <#> j then 1 else 0) =
          (case snd (xs[jj := (1, None)] ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if p = (exec (t + d)) <#> j then 1 else 0)"
        if "j < k" for j
      using assms 1 by (cases "j = jj") simp_all
    qed
    ultimately show ?thesis
      by simp
  next
    case 2
    then have "?lhs p = enc_upd (zip_cont t xs i) (k + jj) 0"
      by simp
    moreover have "enc_upd (zip_cont t xs i) (k + jj) 0 = zip_cont t (xs[jj:=(1, None)]) i"
      using assms(1-4) enc_upd_zip_cont_Some_None by simp
    ultimately show ?thesis
      using 2 by simp
  next
    case 3
    moreover have "i < TT"
      using assms(4) by (simp add: assms(1) exec_pos_less_TT)
    ultimately show ?thesis
      using zip_cont_eq_0 by simp
  qed
qed

lemma sem_cmdL7_2a:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i = exec t <#> jj"
    and "i > 0"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, None)]) (i - 1) 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL7 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL7 jj)"
    using turing_command_cmdL7[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(8) by simp

  define rs where "rs = read tps"
  then have not_beginning: "\<not> is_beginning (rs ! 1)"
    using read_tpsL_1_nth_2k1 assms enc_nth_def read_tpsL_1_bounds zero_less_Suc exec_pos_less_TT
    by simp
  then show "fst (cmdL7 jj (read tps)) = 0"
    using cmdL7_def rs_def by simp

  have "i < TT"
    using assms(5) by (simp add: assms(1) exec_pos_less_TT)

  have "rs ! (3 + jj) = \<box>"
    using rs_def read_tpsL_3 assms by simp
  moreover have "enc_nth (rs ! 1) (k + jj) = 1"
    using assms rs_def read_tpsL_1_nth_less_2k[OF `i < TT`] by simp
  ultimately have "condition7a rs jj"
    using not_beginning `i < TT` assms(2) read_tpsL_1_bounds rs_def by simp
  then have *: "snd (cmdL7 jj rs) =
    [(rs ! 0, Stay),
     (enc_upd (rs ! 1) (k + jj) 0, Left),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (if j = jj then 3 else rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL7_def by auto

  show "act (cmdL7 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,8) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (enc_upd (rs ! 1) (k + jj) 0, Left) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps ! 1 |:=| (enc_upd (rs ! 1) (k + jj) 0) |-| 1"
        using act_Left' 2 len by simp
      also have "... = tps' ! 1"
        using assms zip_cont_enc_upd_None rs_def read_tpsL_1 tpsL_1 zip_cont_def by simp
      finally show ?thesis
        using 2 by simp
    next
      case 3
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,8) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      show ?thesis
      proof (cases "j = 3 + jj")
        case True
        then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (3, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by (smt (verit))
        also have "... = tps' ! j"
          using 4 assms(2,8) True act_onesie tpsL_mvs by simp
        finally show ?thesis .
      next
        case False
        then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by auto
        also have "... = tps' ! j"
          using 4 assms(2,8) False act_Stay len rs_def that tpsL_mvs'
          by (smt (z3) add.commute le_add_diff_inverse2)
        finally show ?thesis .
      qed
    next
      case 5
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,8) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL67_2a:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "exec t <#> jj > 0"
    and "tt = TT - exec t <#> jj"
    and "tps' = tpsL t (xs[jj:=(1, None)]) (fmt n - tt) 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL67 jj) (0, tps) tt = (0, tps')"
proof -
  have "tt > 0"
    using assms(1,7) exec_pos_less_TT by simp
  then have "tt - 1 < TT - exec t <#> jj"
    using assms(6,7) by simp
  then have *: "execute (tmL67 jj) (0, tps) (tt - 1) =
      (0, tpsL t xs (fmt n - tt + 1) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using assms execute_tmL67_1[where ?tt="tt - 1"] by simp
  have **: "fmt n - tt + 1 = exec t <#> jj"
    using assms(1,6,7) exec_pos_less_TT
    by (smt (z3) Nat.add_diff_assoc2 Suc_diff_Suc add.right_neutral add_Suc_right add_diff_cancel_right'
      diff_Suc_Suc diff_less le_add_diff_inverse2 nat_less_le plus_1_eq_Suc zero_less_Suc)
  have "execute (tmL67 jj) (0, tps) tt = exe (tmL67 jj) (execute (tmL67 jj) (0, tps) (tt - 1))"
     using `tt > 0` exe_lt_length by (metis One_nat_def Suc_diff_Suc diff_zero execute.simps(2))
  also have "... = sem (cmdL7 jj) (execute (tmL67 jj) (0, tps) (tt - 1))"
    using tmL67_def exe_lt_length * by simp
  also have "... = sem (cmdL7 jj) (0, tpsL t xs (fmt n - tt + 1) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using * by simp
  also have "... = (0, tpsL t (xs[jj:=(1, None)]) (fmt n - tt) 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using ** assms sem_cmdL7_2a[where ?i="fmt n - tt + 1"] by simp
  finally show ?thesis
    using assms(8) by simp
qed

lemma zip_cont_Some_Some:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i = exec t <#> jj"
    and "i = 0"
    and "sim_move t ! jj = 0"
  shows "zip_cont t xs = zip_cont t (xs[jj:=(1, Some 1)])"
    (is "?lhs = ?rhs")
proof
  fix p
  consider "p < TT" | "p \<ge> TT"
    by linarith
  then show "?lhs p = ?rhs p"
  proof (cases)
    case 1
    then have "?lhs p = zip_cont t xs p"
      by simp
    moreover have "zip_cont t xs p = zip_cont t (xs[jj:=(1, Some 1)]) p"
    proof (rule zip_cont_eqI)
      show "p < TT"
        using 1 by simp
      show "\<And>j. j < k \<Longrightarrow>
          ((exec (t + fst (xs ! j))) <:> j) p =
          ((exec (t + fst (xs[jj := (1, Some 1)] ! j))) <:> j) p"
        by (metis assms(2,3) fst_conv nth_list_update_eq nth_list_update_neq)
      show "\<And>j. j < k \<Longrightarrow>
          (case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if p = exec (t + d) <#> j then 1 else 0) =
          (case snd (xs[jj := (1, Some 1)] ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if p = exec (t + d) <#> j then 1 else 0)"
        using assms 1 sim_move
        by (metis (no_types, lifting) add.commute add.right_neutral diff_add_zero nth_list_update_eq
          nth_list_update_neq option.simps(5) plus_1_eq_Suc prod.sel(2))
    qed
    ultimately show ?thesis
      by simp
  next
    case 2
    then show ?thesis
      using zip_cont_eq_0 by simp
  qed
qed

lemma sem_cmdL7_2b:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i = exec t <#> jj"
    and "i = 0"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL7 jj) (0, tps) = (1, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL7 jj)"
    using turing_command_cmdL7[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(8) by simp

  define rs where "rs = read tps"
  then have is_beginning: "is_beginning (rs ! 1)"
    using read_tpsL_1_nth_2k1 assms(2,6) enc_nth_def read_tpsL_1_bounds rs_def by simp
  then show "fst (cmdL7 jj (read tps)) = 1"
    using assms(6) cmdL7_def rs_def by simp

  have "rs ! (3 + jj) = \<box>"
    by (simp add: rs_def assms add.commute read_tpsL_3')
  then have "condition7c rs jj"
    using is_beginning by simp
  then have *: "snd (cmdL7 jj rs) =
   [(rs ! 0, Stay),
    (rs ! 1, Left),
    (rs ! 2, Stay)] @
    (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
    (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL7_def by auto

  show "act (cmdL7 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,8) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (rs ! 1, Left) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps' ! 1"
        using zip_cont_Some_Some assms rs_def tpsL_1 "2" act_Left fst_conv len that tpsL_pos_1 by (metis zero_diff)
      finally show ?thesis
        using 2 by simp
    next
      case 3
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,8) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by auto
      also have "... = tps' ! j"
        using 4 assms(2,8) act_Stay len rs_def that tpsL_mvs' by (metis add.commute)
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,8) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL67_2b:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "exec t <#> jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL67 jj) (0, tps) TT = (1, tps')"
  using execute_tmL67_1 assms exe_lt_length tmL67_def sem_cmdL7_2b by simp

lemma tmL67_left_0:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "exec t <#> jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL67 jj) tps esL67 tps'"
proof
  show "execute (tmL67 jj) (0, tps) (length esL67) = (length (tmL67 jj), tps')"
    using esL67_def tmL67_def execute_tmL67_2b assms by simp
  show "\<And>i. i < length esL67 \<Longrightarrow>
        fst (execute (tmL67 jj) (0, tps) i) < length (tmL67 jj)"
    using esL67_def tmL67_def execute_tmL67_1 assms by simp
  show "execute (tmL67 jj) (0, tps) (Suc i) <#> 0 = fst (esL67 ! i) \<and>
        execute (tmL67 jj) (0, tps) (Suc i) <#> 1 = snd (esL67 ! i)"
    if "i < length esL67" for i
  proof (cases "i = fmt n")
    case True
    then have "Suc i = TT"
      by simp
    moreover have "esL67 ! i = (n + 1, 0)"
      using True esL67_def by (simp add: nth_append)
    ultimately show ?thesis
      using assms that tpsL_pos_0 tpsL_pos_1 by (metis execute_tmL67_2b fst_conv snd_conv)
  next
    case False
    then have "Suc i < TT"
      using that esL67_def by simp
    moreover from this have "esL67 ! i = (n + 1, fmt n - 1 - i)"
      by simp
    ultimately show ?thesis
      using tpsL_pos_0 tpsL_pos_1 assms(1-6) execute_tmL67_1
      by (metis (no_types, lifting) diff_diff_left fst_conv minus_nat.diff_0 plus_1_eq_Suc snd_conv)
  qed
qed

lemma sem_cmdL7_3:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "Suc i = exec t <#> jj"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) (i - 1) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL7 jj) (0, tps) = (if i = 0 then 1 else 0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL7 jj)"
    using turing_command_cmdL7[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(7) by simp

  define rs where "rs = read tps"
  show "fst (cmdL7 jj (read tps)) = (if i = 0 then 1 else 0)"
  proof (cases "i = 0")
    case True
    then have "is_beginning (rs ! 1)"
      using read_tpsL_1_nth_2k1 assms(2) enc_nth_def read_tpsL_1_bounds rs_def by simp
    then show ?thesis
      using True cmdL7_def rs_def by simp
  next
    case False
    then have "\<not> is_beginning (rs ! 1)"
      using read_tpsL_1_nth_2k1 assms enc_nth_def exec_pos_less_TT
      by (metis (no_types, lifting) Suc_le_lessD less_imp_le_nat less_numeral_extra(1) neq0_conv rs_def)
    then show ?thesis
      using False cmdL7_def rs_def by simp
  qed

  have "i < TT"
    using assms exec_pos_less_TT by (metis Suc_less_eq less_SucI)

  have "rs ! (3 + jj) = 3"
    by (simp add: rs_def assms(1,2) add.commute read_tpsL_3')
  moreover have "is_code (rs ! 1)"
    using assms rs_def read_tpsL_1_nth_less_2k `i < TT` read_tpsL_1_bounds by simp
  ultimately have "condition7b rs jj"
    using `i < TT` assms(2) read_tpsL_1_bounds rs_def by simp
  then have *: "snd (cmdL7 jj rs) =
    [(rs ! 0, Stay),
     (enc_upd (rs ! 1) (k + jj) 1, Left),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (if j = jj then 0 else rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL7_def by simp

  show "act (cmdL7 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,7) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (enc_upd (rs ! 1) (k + jj) 1, Left) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps ! 1 |:=| (enc_upd (rs ! 1) (k + jj) 1) |-| 1"
        using act_Left' 2 len by simp
      also have "... = tps' ! 1"
        using assms zip_cont_enc_upd_Some_Left rs_def read_tpsL_1 tpsL_1 zip_cont_def by simp
      finally show ?thesis
        using 2 by simp
    next
      case 3
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,7) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      show ?thesis
      proof (cases "j = 3 + jj")
        case True
        then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (0, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse
          by (smt (verit, ccfv_threshold))
        also have "... = tps' ! j"
          using 4 assms(1,2,6,7) 4 True act_onesie tpsL_mvs by simp
        finally show ?thesis .
      next
        case False
        then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by auto
        also have "... = tps' ! j"
          using 4 assms(2,7) False act_Stay len rs_def that tpsL_mvs'
          by (smt (z3) add.commute le_add_diff_inverse2)
        finally show ?thesis .
      qed
    next
      case 5
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL67_3:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "exec t <#> jj > 0"
    and "tt = TT - exec t <#> jj"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) (fmt n - Suc tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL67 jj) (0, tps) (Suc tt) = (if fmt n - tt = 0 then 1 else 0, tps')"
proof -
  let ?i = "fmt n - tt"
  let ?xs = "xs[jj:=(1, None)]"
  let ?tps = "tpsL t ?xs ?i 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  have 1: "Suc ?i = exec t <#> jj"
    using assms exec_pos_less_TT
    by (smt (z3) Suc_diff_le diff_diff_cancel diff_is_0_eq nat_less_le neq0_conv not_less_eq zero_less_diff)
  have 2: "?xs ! jj = (1, None)"
    by (simp add: assms(1) assms(3))
  have 3: "length ?xs = k"
    by (simp add: assms(3))
  have "execute (tmL67 jj) (0, tps) (Suc tt) = exe (tmL67 jj) (execute (tmL67 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL67 jj) (0, ?tps)"
    using assms execute_tmL67_2a by simp
  also have "... = sem (cmdL7 jj) (0, ?tps)"
    using tmL67_def exe_lt_length by simp
  also have "... = (if fmt n - tt = 0 then 1 else 0, tps')"
    using sem_cmdL7_3[OF assms(1) _ 3 2 1 assms(5)] assms(8) by simp
  finally show ?thesis
    by simp
qed

lemma sem_cmdL7_4:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 1)"
    and "Suc i < exec t <#> jj"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t xs (i - 1) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL7 jj) (0, tps) = (if i = 0 then 1 else 0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL7 jj)"
    using turing_command_cmdL7[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(7) by simp

  define rs where "rs = read tps"
  show "fst (cmdL7 jj (read tps)) = (if i = 0 then 1 else 0)"
  proof (cases "i = 0")
    case True
    then have "is_beginning (rs ! 1)"
      using read_tpsL_1_nth_2k1 assms(2) enc_nth_def read_tpsL_1_bounds rs_def by simp
    then show ?thesis
      using True cmdL7_def rs_def by simp
  next
    case False
    then have "\<not> is_beginning (rs ! 1)"
      using read_tpsL_1_nth_2k1 assms enc_nth_def exec_pos_less_TT read_tpsL_1 rs_def
      by (metis (no_types, lifting) less_2_cases_iff nat_1_add_1 not_less_eq plus_1_eq_Suc)
    then show ?thesis
      using False cmdL7_def rs_def by simp
  qed

  have "i < exec t <#> jj"
    using assms(5) by simp
  then have "i < TT"
    using assms(1) exec_pos_less_TT by (meson Suc_lessD less_trans_Suc)

  have "rs ! (3 + jj) = \<box>"
    using rs_def read_tpsL_3 assms by simp
  moreover have "enc_nth (rs ! 1) (k + jj) = 0"
    using assms rs_def read_tpsL_1_nth_less_2k[OF `i < TT`, of "k + jj"] sim_move by simp
  ultimately have "condition7c rs jj"
    by simp
  then have *: "snd (cmdL7 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Left),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL7_def by auto

  show "act (cmdL7 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,7) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (rs ! 1, Left) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps' ! 1"
        using assms rs_def tpsL_1 "2" act_Left fst_conv len that tpsL_pos_1 by metis
      finally show ?thesis
        using 2 by simp
    next
      case 3
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (cmdL7 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,7) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by auto
      also have "... = tps' ! j"
        using 4 assms(2,7) act_Stay len rs_def that tpsL_mvs' by (smt (z3) add.commute le_add_diff_inverse2)
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL7 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL67_4:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "exec t <#> jj > 0"
    and "tt \<ge> Suc (Suc (TT - exec t <#> jj))"
    and "tt \<le> TT"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) (fmt n - tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL67 jj) (0, tps) tt = (if TT - tt = 0 then 1 else 0, tps')"
  using assms(7,8,9)
proof (induction tt arbitrary: tps' rule: nat_induct_at_least)
  case base
  let ?tt = "TT - exec t <#> jj"
  let ?xs = "xs[jj:=(1, Some 1)]"
  let ?tps = "tpsL t ?xs (fmt n - Suc ?tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  have "execute (tmL67 jj) (0, tps) (Suc (Suc ?tt)) = exe (tmL67 jj) (execute (tmL67 jj) (0, tps) (Suc ?tt))"
    by simp
  also have "... = exe (tmL67 jj) (if fmt n - ?tt = 0 then 1 else 0, ?tps)"
    using execute_tmL67_3 assms by simp
  also have "... = sem (cmdL7 jj) (0, ?tps)"
    using tmL67_def base exe_lt_length by simp
  finally show ?case
    using sem_cmdL7_4 assms base.prems(2) by simp
next
  case (Suc tt)
  let ?tt = "TT - exec t <#> jj"
  let ?xs = "xs[jj:=(1, Some 1)]"
  let ?tps = "tpsL t ?xs (fmt n - tt) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  have "execute (tmL67 jj) (0, tps) (Suc tt) = exe (tmL67 jj) (execute (tmL67 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL67 jj) (if Suc (fmt n) - tt = 0 then 1 else 0, ?tps)"
    using Suc by simp
  also have "... = sem (cmdL7 jj) (0, ?tps)"
    using Suc.prems(1) exe_lt_length tmL67_def by auto
  finally show ?case
    using assms sem_cmdL7_4 Suc by simp
qed

lemma tmL67_left_gt_0:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "exec t <#> jj > 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL67 jj) tps esL67 tps'"
proof
  show 1: "execute (tmL67 jj) (0, tps) (length esL67) = (length (tmL67 jj), tps')"
  proof (cases "exec t <#> jj = 1")
    case True
    then show ?thesis
      using assms(7) execute_tmL67_3[OF assms(1-6)] esL67_def tmL67_def by simp
  next
    case False
    then have "TT \<ge> Suc (Suc (TT - exec t <#> jj))"
      using assms(1,6,7) exec_pos_less_TT
      by (metis Suc_leI add_diff_cancel_right' diff_diff_cancel diff_less nat_less_le plus_1_eq_Suc zero_less_Suc)
    then show ?thesis
      using assms(7) execute_tmL67_4[OF assms(1-6), where ?tt=TT] esL67_def tmL67_def by simp
  qed
  show "fst (execute (tmL67 jj) (0, tps) tt) < length (tmL67 jj)" if "tt < length esL67" for tt
  proof -
    have "tt < TT"
      using that esL67_def by simp
    then consider
        "tt < TT - exec t <#> jj"
      | "tt = TT - exec t <#> jj"
      | "tt = Suc (TT - exec t <#> jj)"
      | "tt \<ge> Suc (Suc (TT - exec t <#> jj))"
      by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using assms execute_tmL67_1 tmL67_def by simp
    next
      case 2
      then show ?thesis
        using assms execute_tmL67_2a tmL67_def by simp
    next
      case 3
      then show ?thesis
        using assms execute_tmL67_3 tmL67_def `tt < TT` by simp
    next
      case 4
      then show ?thesis
        using assms execute_tmL67_4 tmL67_def `tt < TT` by simp
    qed
  qed
  show "execute (tmL67 jj) (0, tps) (Suc tt) <#> 0 = fst (esL67 ! tt) \<and>
        execute (tmL67 jj) (0, tps) (Suc tt) <#> 1 = snd (esL67 ! tt)"
    if "tt < length esL67" for tt
  proof -
    have *: "Suc tt \<le> TT"
      using that esL67_def by simp
    then consider
        "Suc tt < TT - exec t <#> jj"
      | "Suc tt = TT - exec t <#> jj"
      | "Suc tt = Suc (TT - exec t <#> jj)"
      | "Suc tt \<ge> Suc (Suc (TT - exec t <#> jj))"
      using esL67_def `tt < length esL67` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using execute_tmL67_1[OF assms(1-5), where ?tt="Suc tt"] tmL67_def tpsL_pos_0 tpsL_pos_1 *
        by simp
    next
      case 2
      then show ?thesis
        using assms execute_tmL67_2a[OF assms(1-6), where ?tt="Suc tt"] tmL67_def tpsL_pos_0 tpsL_pos_1 *
        by simp
    next
      case 3
      then show ?thesis
        using assms(6) execute_tmL67_3[OF assms(1-6), where ?tt="tt"] tmL67_def tpsL_pos_0 tpsL_pos_1 *
        by (smt (verit, ccfv_threshold) add.commute diff_Suc_1 diff_diff_left diff_is_0_eq
          esL67_at_fmtn esL67_at_lt_fmtn nat_less_le plus_1_eq_Suc prod.collapse prod.inject)
    next
      case 4
      then show ?thesis
        using assms(7) execute_tmL67_4[OF assms(1-6) _ *] * tmL67_def tpsL_pos_0 tpsL_pos_1 1 esL67_at_fmtn esL67_at_lt_fmtn esL67_def
        by (smt (verit, best) One_nat_def Suc_diff_Suc add.commute diff_Suc_1 fst_conv le_neq_implies_less
          length_append length_map length_rev length_upt list.size(3) list.size(4) minus_nat.diff_0 not_less_eq
          plus_1_eq_Suc snd_conv)
    qed
  qed
qed

lemma tmL67_left:
  assumes "jj < k"
    and "tps = tpsL t xs (fmt n) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL67 jj) tps esL67 tps'"
  using assms tmL67_left_0 tmL67_left_gt_0 by (cases "exec t <#> jj = 0") simp_all

definition "esL47 \<equiv> esL46 @ esL67"

lemma len_esL47: "length esL47 = 2 * TT + 2"
  using len_esL46 esL47_def esL67_def by simp

lemma tmL47_nonleft:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "sim_move t ! jj \<noteq> 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 0)]) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL47 jj) tps esL47 tps'"
  unfolding tmL47_def esL47_def
  using assms
  by (intro traces_sequential[OF tmL46 tmL67_nonleft]) simp_all

lemma tmL47_left:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL47 jj) tps esL47 tps'"
  unfolding tmL47_def esL47_def
  using assms
  by (intro traces_sequential[OF tmL46 tmL67_left[where ?xs="xs[jj:=(1, Some 0)]"]]) simp_all

lemma sem_cmdL8_nonright:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "i < TT"
    and "sim_move t ! jj \<noteq> 2"
    and "tps' = tpsL t xs (Suc i) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL8 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL8 jj)"
    using turing_command_cmdL8[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(6) by simp
  define rs where "rs = read tps"
  then have "rs ! 1 \<noteq> \<box>"
    using assms by (metis not_one_less_zero read_tpsL_1_bounds(1))
  then show "fst (cmdL8 jj rs) = 0"
    unfolding cmdL8_def by simp

  have "rs ! (3 + jj) = sim_move t ! jj"
    using rs_def assms(1,2) read_tpsL_3 by simp
  moreover have "sim_move t ! jj < 3"
    using sim_move_def assms(1) direction_to_symbol_less sim_move_nth sim_move_nth_else
    by (metis One_nat_def not_add_less2 not_less_eq numeral_3_eq_3 plus_1_eq_Suc)
  ultimately have "condition8d rs jj"
    using assms(5) \<open>rs ! 1 \<noteq> \<box>\<close> by simp
  then have *: "snd (cmdL8 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Right),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL8_def by auto

  show "act (cmdL8 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        by (metis "*" act_Stay append.simps(2) assms(2) assms(6) len nth_Cons_0 rs_def that tpsL_0)
    next
      case 2
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (rs ! 1, Right) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps' ! 1"
        using act_Right len rs_def assms tpsL_1 that tpsL_pos_1
        by (metis "2" add.commute fst_conv plus_1_eq_Suc)
      also have "... = tps' ! j"
        using 2 by simp
      finally show ?thesis .
    next
      case 3
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,6) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,6) tpsL_mvs' 4 by simp
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,6) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma sem_cmdL8_TT:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "i = TT"
  shows "sem (cmdL8 jj) (0, tps) = (1, tps)"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL8 jj)"
    using turing_command_cmdL8[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps = 2 * k + 3"
    using assms(2) by simp
  define rs where "rs = read tps"
  then have "rs ! 1 = \<box>"
    using assms read_tpsL_1 by simp
  then show "fst (cmdL8 jj rs) = 1"
    unfolding cmdL8_def by simp

  have "rs ! (3 + jj) = sim_move t ! jj"
    using rs_def assms(1,2) read_tpsL_3 by simp
  moreover have "sim_move t ! jj < 3"
    using sim_move_def assms(1) direction_to_symbol_less sim_move_nth sim_move_nth_else
    by (metis One_nat_def not_add_less2 not_less_eq numeral_3_eq_3 plus_1_eq_Suc)
  ultimately have "condition8c rs jj"
    using \<open>rs ! 1 = \<box>\<close> by simp
  then have *: "snd (cmdL8 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Stay),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL8_def by simp

  show "act (cmdL8 jj (read tps) [!] j) (tps ! j) = tps ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
      using "*" act_Stay len rs_def
        threeplus2k_2[where ?a="(rs ! 0, Stay)"] threeplus2k_3[where ?a="(rs ! 0, Stay)"]
      by (cases) simp_all
  qed
qed

lemma execute_tmL78_nonright_le_TT:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "sim_move t ! jj \<noteq> 2"
    and "tt \<le> TT"
    and "tps' = tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL78 jj) (0, tps) tt = (0, tps')"
  using assms(5,6)
proof (induction tt arbitrary: tps')
  case 0
  then show ?case
    using assms(1-4) by simp
next
  case (Suc tt)
  then have "tt < TT"
    by simp
  have "execute (tmL78 jj) (0, tps) (Suc tt) = exe (tmL78 jj) (execute (tmL78 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL78 jj) (0, tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using Suc by simp
  also have "... = sem (cmdL8 jj) (0, tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using tmL78_def exe_lt_length by simp
  finally show ?case
    using sem_cmdL8_nonright[OF assms(1) _ assms(3) `tt < TT` assms(4)] Suc by simp
qed

lemma execute_tmL78_nonright_eq_Suc_TT:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "sim_move t ! jj \<noteq> 2"
    and "tps' = tpsL t xs TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL78 jj) (0, tps) (Suc TT) = (1, tps')"
  using assms sem_cmdL8_TT execute_tmL78_nonright_le_TT[where ?tt=TT] exe_lt_length tmL78_def
  by simp

definition "esL78 \<equiv> map (\<lambda>i. (n + 1, Suc i)) ([0..<TT]) @ [(n + 1, TT)]"

lemma tmL78_nonright:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "sim_move t ! jj \<noteq> 2"
    and "tps' = tpsL t xs TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL78 jj) tps esL78 tps'"
proof
  have len: "length esL78 = Suc TT"
    using esL78_def by simp
  then show 1: "execute (tmL78 jj) (0, tps) (length esL78) = (length (tmL78 jj), tps')"
    using assms tmL78_def execute_tmL78_nonright_eq_Suc_TT by simp
  show "\<And>i. i < length esL78 \<Longrightarrow>
        fst (execute (tmL78 jj) (0, tps) i) < length (tmL78 jj)"
    using len assms execute_tmL78_nonright_le_TT tmL78_def by simp
  show "(execute (tmL78 jj) (0, tps) (Suc i)) <#> 0 = fst (esL78 ! i) \<and>
        (execute (tmL78 jj) (0, tps) (Suc i)) <#> 1 = snd (esL78 ! i)"
      if "i < length esL78" for i
  proof (cases "i = TT")
    case True
    then have "esL78 ! i = (n + 1, TT)"
      using esL78_def by (simp add: nth_append)
    then show ?thesis
      using assms that tpsL_pos_0 tpsL_pos_1 len 1 True by simp
  next
    case False
    then have "i < TT"
      using that len by simp
    moreover from this have "esL78 ! i = (n + 1, Suc i)"
      using esL78_def nth_map_upt_TT by auto
    ultimately show ?thesis
      using tpsL_pos_0 tpsL_pos_1 assms(1-4) execute_tmL78_nonright_le_TT
      by (metis Suc_leI fst_conv snd_conv)
  qed
qed

lemma sem_cmdL8_1:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i < exec t <#> jj"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t xs (Suc i) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL8 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL8 jj)"
    using turing_command_cmdL8[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(7) by simp

  have "i < TT"
    using assms exec_pos_less_TT by (meson Suc_less_eq less_SucI less_trans_Suc)

  define rs where "rs = read tps"
  then have "rs ! 1 \<noteq> \<box>"
    using assms `i < TT` by (metis not_one_less_zero read_tpsL_1_bounds(1))
  then show "fst (cmdL8 jj rs) = 0"
    unfolding cmdL8_def by simp

  have "rs ! (3 + jj) = sim_move t ! jj"
    using rs_def assms(1,2) read_tpsL_3 by simp
  moreover have "sim_move t ! jj = 2"
    using sim_move_def assms(1,6) direction_to_symbol_less sim_move_nth sim_move_nth_else
    by simp
  moreover have "enc_nth (rs ! 1) (k + jj) = 0"
    using assms rs_def read_tpsL_1_nth_less_2k[OF `i < TT`, of "k + jj"] by simp
  ultimately have "condition8d rs jj"
    using assms \<open>rs ! 1 \<noteq> \<box>\<close> by simp
  then have *: "snd (cmdL8 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Right),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL8_def by auto

  show "act (cmdL8 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using "*" act_Stay append.simps(2) assms len nth_Cons_0 rs_def that tpsL_0 by metis
    next
      case 2
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (rs ! 1, Right) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps' ! 1"
        using act_Right len rs_def assms tpsL_1 that tpsL_pos_1
        by (metis "2" add.commute fst_conv plus_1_eq_Suc)
      also have "... = tps' ! j"
        using 2 by simp
      finally show ?thesis .
    next
      case 3
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,7) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_mvs' 4 by simp
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL78_1:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 2"
    and "tt \<le> exec t <#> jj"
    and "tps' = tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL78 jj) (0, tps) tt = (0, tps')"
  using assms(6,7)
proof (induction tt arbitrary: tps')
  case 0
  then show ?case
    using assms(1-5) by simp
next
  case (Suc tt)
  then have "tt < exec t <#> jj"
    by simp
  have "execute (tmL78 jj) (0, tps) (Suc tt) = exe (tmL78 jj) (execute (tmL78 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL78 jj) (0, tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using Suc by simp
  also have "... = sem (cmdL8 jj) (0, tpsL t xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j))"
    using exe_lt_length tmL78_def by simp
  finally show ?case
    using assms(1-5) sem_cmdL8_1[where ?i=tt] Suc by simp
qed

lemma sem_cmdL8_2:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "i = exec t <#> jj"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t (xs[jj:=(1, None)]) (Suc i) 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL8 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL8 jj)"
    using turing_command_cmdL8[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(7) by simp

  have "i < TT"
    using assms exec_pos_less_TT by (meson Suc_less_eq less_SucI less_trans_Suc)

  define rs where "rs = read tps"
  then have "rs ! 1 \<noteq> \<box>"
    using assms `i < TT` by (metis not_one_less_zero read_tpsL_1_bounds(1))
  then show "fst (cmdL8 jj rs) = 0"
    unfolding cmdL8_def by simp

  have "rs ! (3 + jj) = 2"
    using rs_def read_tpsL_3 assms by simp
  moreover have "enc_nth (rs ! 1) (k + jj) = 1"
    using assms rs_def read_tpsL_1_nth_less_2k[OF `i < TT`] by simp
  ultimately have "condition8a rs jj"
    using `i < TT` assms(2) read_tpsL_1_bounds rs_def by simp
  then have *: "snd (cmdL8 jj rs) =
    [(rs ! 0, Stay),
     (enc_upd (rs ! 1) (k + jj) 0, Right),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (if j = jj then 3 else rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL8_def by simp

  show "act (cmdL8 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,7) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (enc_upd (rs ! 1) (k + jj) 0, Right) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps ! 1 |:=| (enc_upd (rs ! 1) (k + jj) 0) |+| 1"
        using act_Right' 2 len by simp
      also have "... = tps' ! 1"
        using assms zip_cont_enc_upd_None rs_def read_tpsL_1 tpsL_1 zip_cont_def by simp
      finally show ?thesis
        using 2 by simp
    next
      case 3
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,7) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      show ?thesis
      proof (cases "j = 3 + jj")
        case True
        then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (3, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by (smt (verit))
        also have "... = tps' ! j"
          using 4 assms(2,7) True act_onesie tpsL_mvs by simp
        finally show ?thesis .
      next
        case False
        then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by auto
        also have "... = tps' ! j"
          using 4 assms(2,7) False act_Stay len rs_def that tpsL_mvs'
          by (smt (z3) add.commute le_add_diff_inverse2)
        finally show ?thesis .
      qed
    next
      case 5
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL78_2:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t (xs[jj:=(1, None)]) (Suc (exec t <#> jj)) 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL78 jj) (0, tps) (Suc (exec t <#> jj)) = (0, tps')"
  using assms exe_lt_length tmL78_def execute_tmL78_1 sem_cmdL8_2 by simp

lemma sem_cmdL8_3:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. if j = jj then 3 else sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, None)"
    and "i = Suc (exec t <#> jj)"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) (Suc i) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL8 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL8 jj)"
    using turing_command_cmdL8[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(7) by simp

  have "i < TT"
    using assms exec_pos_less_TT sim_move
    by (metis (no_types, lifting) add_2_eq_Suc' diff_Suc_1)
  moreover define rs where "rs = read tps"
  ultimately have "rs ! 1 \<noteq> \<box>"
    by (metis (no_types, lifting) assms(2) not_one_less_zero read_tpsL_1_bounds(1))
  then show "fst (cmdL8 jj (read tps)) = 0"
    using cmdL8_def rs_def by simp

  have "rs ! (3 + jj) = 3"
    by (simp add: rs_def assms(1,2) add.commute read_tpsL_3')
  moreover have "is_code (rs ! 1)"
    using assms rs_def read_tpsL_1_nth_less_2k `i < TT` read_tpsL_1_bounds by simp
  ultimately have "condition7b rs jj"
    using `i < TT` assms(2) read_tpsL_1_bounds rs_def by simp
  then have *: "snd (cmdL8 jj rs) =
    [(rs ! 0, Stay),
     (enc_upd (rs ! 1) (k + jj) 1, Right),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (if j = jj then 2 else rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL8_def by simp

  show "act (cmdL8 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 0) (tps ! 0)"
        by simp
      also have "... = act (rs ! 0, Stay) (tps ! 0)"
        using * rs_def by simp
      also have "... = tps ! 0"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 0"
        using assms(2,7) tpsL_0 by simp
      also have "... = tps' ! j"
        using 1 by simp
      finally show ?thesis .
    next
      case 2
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (enc_upd (rs ! 1) (k + jj) 1, Right) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps ! 1 |:=| (enc_upd (rs ! 1) (k + jj) 1) |+| 1"
        using act_Right' 2 len by simp
      also have "... = tps' ! 1"
        using assms zip_cont_enc_upd_Some_Right rs_def read_tpsL_1 tpsL_1 zip_cont_def by simp
      finally show ?thesis
        using 2 by simp
    next
      case 3
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,7) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      show ?thesis
      proof (cases "j = 3 + jj")
        case True
        then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (2, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4
          by (smt (verit, ccfv_SIG) diff_add_inverse)
        also have "... = tps' ! j"
          using 4 assms(1,2,6,7) 4 True act_onesie tpsL_mvs by simp
        finally show ?thesis .
      next
        case False
        then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
          using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] 4 diff_add_inverse by auto
        also have "... = tps' ! j"
          using 4 assms(2,7) False act_Stay len rs_def that tpsL_mvs'
          by (smt (z3) add.commute le_add_diff_inverse2)
        finally show ?thesis .
      qed
    next
      case 5
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,7) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL78_3:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) (Suc (Suc (exec t <#> jj))) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL78 jj) (0, tps) (Suc (Suc (exec t <#> jj))) = (0, tps')"
  using assms exe_lt_length tmL78_def execute_tmL78_2 sem_cmdL8_3 by simp

lemma sem_cmdL8_4:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 1)"
    and "i > Suc (exec t <#> jj)"
    and "i < TT"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t xs (Suc i) 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "sem (cmdL8 jj) (0, tps) = (0, tps')"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) (cmdL8 jj)"
    using turing_command_cmdL8[OF assms(1)] turing_commandD(1) by simp
  show len: "length tps = 2 * k + 3"
    using assms(2) by simp
  show "length tps' = 2 * k + 3"
    using assms(8) by simp

  define rs where "rs = read tps"
  then have "rs ! 1 \<noteq> \<box>"
    using assms by (metis not_one_less_zero read_tpsL_1_bounds(1))
  then show "fst (cmdL8 jj rs) = 0"
    unfolding cmdL8_def by simp

  have "rs ! (3 + jj) = sim_move t ! jj"
    using rs_def assms read_tpsL_3 by simp
  moreover have "sim_move t ! jj = 2"
    using sim_move_def assms(1,7) direction_to_symbol_less sim_move_nth sim_move_nth_else
    by simp
  moreover have "enc_nth (rs ! 1) (k + jj) = 0"
    using assms rs_def read_tpsL_1_nth_less_2k[OF assms(6), of "k + jj"] sim_move by simp
  ultimately have "condition8d rs jj"
    using assms \<open>rs ! 1 \<noteq> \<box>\<close> by simp
  then have *: "snd (cmdL8 jj rs) =
    [(rs ! 0, Stay),
     (rs ! 1, Right),
     (rs ! 2, Stay)] @
     (map (\<lambda>j. (rs ! (j + 3), Stay)) [0..<k]) @
     (map (\<lambda>j. (rs ! (3 + k + j), Stay)) [0..<k])"
    unfolding cmdL8_def by auto

  show "act (cmdL8 jj (read tps) [!] j) (tps ! j) = tps' ! j" if "j < 2 * k + 3" for j
  proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using "*" act_Stay append.simps(2) assms len nth_Cons_0 rs_def that tpsL_0 by metis
    next
      case 2
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 1) (tps ! 1)"
        by simp
      also have "... = act (rs ! 1, Right) (tps ! 1)"
        using * rs_def by simp
      also have "... = tps' ! 1"
        using act_Right len rs_def assms tpsL_1 that tpsL_pos_1 2
        by (metis add.commute fst_conv plus_1_eq_Suc)
      also have "... = tps' ! j"
        using 2 by simp
      finally show ?thesis .
    next
      case 3
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (cmdL8 jj (read tps) [!] 2) (tps ! 2)"
        by simp
      also have "... = act (rs ! 2, Stay) (tps ! 2)"
        using * rs_def by simp
      also have "... = tps ! 2"
        using act_Stay len rs_def by simp
      also have "... = tps' ! 2"
        using assms(2,8) tpsL_2 by simp
      also have "... = tps' ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,8) tpsL_mvs' 4 by simp
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL8 jj (read tps) [!] j) (tps ! j) = act (rs ! j, Stay) (tps ! j)"
        using * rs_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
      also have "... = tps ! j"
        using len act_Stay rs_def that by simp
      also have "... = tps' ! j"
        using assms(2,8) tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

lemma execute_tmL78_4:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 2"
    and "tt \<ge> Suc (Suc (exec t <#> jj))"
    and "tt \<le> TT"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL78 jj) (0, tps) tt = (0, tps')"
  using assms(6,7,8)
proof (induction tt arbitrary: tps' rule: nat_induct_at_least)
  case base
  then show ?case
    using assms(1-5) execute_tmL78_3 by simp
next
  case (Suc tt)
  then have "tt < TT"
    by simp
  let ?xs = "xs[jj:=(1, Some 1)]"
  let ?tps = "tpsL t ?xs tt 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  have "execute (tmL78 jj) (0, tps) (Suc tt) = exe (tmL78 jj) (execute (tmL78 jj) (0, tps) tt)"
    by simp
  also have "... = exe (tmL78 jj) (0, ?tps)"
    using Suc by simp
  also have "... = sem (cmdL8 jj) (0, ?tps)"
    using tmL78_def exe_lt_length by simp
  then show ?case
    using sem_cmdL8_4[where ?i=tt] assms Suc by simp
qed

lemma execute_tmL78_5:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "execute (tmL78 jj) (0, tps) (Suc TT) = (1, tps')"
proof -
  have *: "TT \<ge> Suc (Suc (exec t <#> jj))"
    using exec_pos_less_TT sim_move assms(1,5)
    by (metis Suc_leI add_2_eq_Suc' add_diff_cancel_left' plus_1_eq_Suc)
  have "execute (tmL78 jj) (0, tps) (Suc TT) = exe (tmL78 jj) (execute (tmL78 jj) (0, tps) TT)"
    by simp
  also have "... = exe (tmL78 jj) (0, tps')"
    using execute_tmL78_4[OF assms(1-5) *] assms(6) by simp
  also have "... = sem (cmdL8 jj) (0, tps')"
    using tmL78_def exe_lt_length by simp
  finally show ?thesis
    using assms(1,3,6) sem_cmdL8_TT by simp
qed

lemma tmL78_right:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL78 jj) tps esL78 tps'"
proof
  have len: "length esL78 = Suc TT"
    using esL78_def by simp
  show "execute (tmL78 jj) (0, tps) (length esL78) = (length (tmL78 jj), tps')"
    using len execute_tmL78_5 assms tmL78_def by simp
  show "fst (execute (tmL78 jj) (0, tps) tt) < length (tmL78 jj)"
    if "tt < length esL78" for tt
  proof -
    have "tt < Suc TT"
      using that len by simp
    then consider
        "tt \<le> exec t <#> jj"
      | "tt = Suc (exec t <#> jj)"
      | "tt = Suc (Suc (exec t <#> jj))"
      | "tt > Suc (Suc (exec t <#> jj))"
      by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using assms execute_tmL78_1 tmL78_def by simp
    next
      case 2
      then show ?thesis
        using assms execute_tmL78_2 tmL78_def by simp
    next
      case 3
      then show ?thesis
        using assms execute_tmL78_3 tmL78_def by simp
    next
      case 4
      then show ?thesis
        using assms execute_tmL78_4 tmL78_def `tt < Suc TT` by simp
    qed
  qed
  show "execute (tmL78 jj) (0, tps) (Suc tt) <#> 0 = fst (esL78 ! tt) \<and>
        execute (tmL78 jj) (0, tps) (Suc tt) <#> 1 = snd (esL78 ! tt)"
        if "tt < length esL78" for tt
  proof -
    have *: "Suc tt \<le> Suc TT"
      using that esL78_def by simp
    then consider
        "Suc tt \<le> exec t <#> jj"
      | "Suc tt = Suc (exec t <#> jj)"
      | "Suc tt = Suc (Suc (exec t <#> jj))"
      | "Suc tt > Suc (Suc (exec t <#> jj)) \<and> Suc tt \<le> TT"
      | "Suc tt = Suc TT"
       by linarith
    then show ?thesis
    proof (cases)
      case 1
      then have "esL78 ! tt = (n + 1, Suc tt)"
        using nth_map_upt_TT esL78_def by (metis "*" assms(1) exec_pos_less_TT nat_less_le not_less_eq_eq)
      then show ?thesis
        using execute_tmL78_1[OF assms(1-5), where ?tt="Suc tt"] tmL78_def tpsL_pos_0 tpsL_pos_1 * 1
        by simp
    next
      case 2
      then show ?thesis
        using assms execute_tmL78_2[OF assms(1-5)] tmL78_def tpsL_pos_0 tpsL_pos_1 *
        by (metis (no_types, lifting) esL78_def exec_pos_less_TT fst_conv nat.inject nth_map_upt_TT snd_conv)
    next
      case 3
      then have "tt < TT"
        by (metis add_2_eq_Suc' assms(1) assms(5) diff_Suc_1 exec_pos_less_TT sim_move)
      then have "esL78 ! tt = (n + 1, Suc tt)"
        using nth_map_upt_TT esL78_def by auto
      then show ?thesis
        using assms(6) execute_tmL78_3[OF assms(1-5)] tmL78_def tpsL_pos_0 tpsL_pos_1 *
        using 3 by simp
    next
      case 4
      then have **: "Suc tt \<ge> Suc (Suc (exec t <#> jj))"
        by simp
      show ?thesis
        using execute_tmL78_4[OF assms(1-5) **] tmL78_def tpsL_pos_0 tpsL_pos_1 esL78_def
        by (metis "4" Suc_le_lessD fst_conv nth_map_upt_TT snd_conv)
    next
      case 5
      then have "esL78 ! tt = (n + 1, TT)"
        using esL78_def by (simp add: nth_append)
      then show ?thesis
        using assms(6) execute_tmL78_5[OF assms(1-5)] tmL78_def tpsL_pos_0 tpsL_pos_1 esL78_def 5
        by simp
    qed
  qed
qed

lemma zip_cont_Stay:
  assumes "jj < k"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 1"
  shows "zip_cont t xs = zip_cont t (xs[jj:=(1, Some 1)])"
proof
  fix i
  let ?xs = "xs[jj := (1, Some 1)]"
  show "zip_cont t xs i = zip_cont t ?xs i"
  proof (cases "i < TT")
    case True
    then show ?thesis
    proof (rule zip_cont_eqI)
      show "\<And>j. j < k \<Longrightarrow>
          (exec (t + fst (xs ! j)) <:> j) i = (exec (t + fst (?xs ! j)) <:> j) i"
        using True assms nth_list_update fst_conv by metis
      show "\<And>j. j < k \<Longrightarrow>
          (case snd (xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) =
          (case snd (?xs ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0)"
        using assms sim_move
        by (metis (no_types, lifting) add.commute add.right_neutral add_diff_cancel_right'
          nth_list_update_eq nth_list_update_neq option.simps(5) plus_1_eq_Suc snd_conv)
    qed
  next
    case False
    then show ?thesis
      by (simp add: zip_cont_def)
  qed
qed

lemma tpsL_Stay:
  assumes "jj < k"
    and "tps = tpsL t xs i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (1, Some 0)"
    and "sim_move t ! jj = 1"
  shows "tps = tpsL t (xs[jj:=(1, Some 1)]) i 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
proof -
  let ?lhs = "((\<lfloor>zs\<rfloor>, n + 1) #
      (zip_cont t xs, i) #
      \<lceil>fst (exec (t + 1))\<rceil> #
      map (onesie \<circ> (!) (sim_move t)) [0..<k] @
      map (onesie \<circ> (!) (sim_write t)) [0..<k])"
  let ?xs = "xs[jj:=(1, Some 1)]"
  let ?rhs = "((\<lfloor>zs\<rfloor>, n + 1) #
      (zip_cont t ?xs, i) #
      \<lceil>fst (exec (t + 1))\<rceil> #
      map (onesie \<circ> (!) (sim_move t)) [0..<k] @
      map (onesie \<circ> (!) (sim_write t)) [0..<k])"
  have "?lhs = ?rhs"
  proof (intro nth_equalityI)
    show "length ?lhs = length ?rhs"
      by simp
    show "?lhs ! j = ?rhs ! j" if "j < length ?lhs" for j
    proof -
      consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
        using `j < length ?lhs` by fastforce
      then show ?thesis
        using zip_cont_Stay assms by (cases) auto
    qed
  qed
  then show ?thesis
    using assms tpsL_def by simp
qed

definition "esL48 \<equiv> esL47 @ esL78"

lemma len_esL48: "length esL48 = 3 * TT + 3"
  using len_esL47 esL48_def esL78_def by simp

lemma tmL48_left:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "sim_move t ! jj = 0"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL48 jj) tps esL48 tps'"
  unfolding tmL48_def esL48_def
  using assms
  by (intro traces_sequential[OF tmL47_left tmL78_nonright[where ?xs="xs[jj:=(1, Some 1)]"]]) simp_all

lemma tmL48_right:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "sim_move t ! jj = 2"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL48 jj) tps esL48 tps'"
  unfolding tmL48_def esL48_def
  using assms
  by (intro traces_sequential[OF tmL47_nonleft tmL78_right[where ?xs="xs[jj:=(1, Some 0)]"]]) simp_all

lemma tmL48_stay:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "sim_move t ! jj = 1"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL48 jj) tps esL48 tps'"
proof -
  let ?xs = "xs[jj:=(1, Some 0)]"
  let ?tps = "tpsL t ?xs TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  have "traces (tmL48 jj) tps esL48 ?tps"
    unfolding tmL48_def esL48_def
    using assms
    by (intro traces_sequential[OF tmL47_nonleft tmL78_nonright[where ?xs="?xs"]]) simp_all
  then show ?thesis
    using tpsL_Stay[where ?xs="?xs"] assms by simp
qed

lemma tmL48:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL48 jj) tps esL48 tps'"
proof -
  consider "sim_move t ! jj = 0" | "sim_move t ! jj = 1" | "sim_move t ! jj = 2"
    using direction_to_symbol_less sim_move_def assms(1) sim_move_nth sim_move_nth_else
    by (metis (no_types, lifting) One_nat_def Suc_1 less_Suc_eq less_nat_zero_code numeral_3_eq_3)
  then show ?thesis
    using assms tmL48_left tmL48_right tmL48_stay
    by (cases) simp_all
qed

definition "esL49 \<equiv> esL48 @ map (\<lambda>i. (n + 1, i)) (rev [0..<TT]) @ [(n + 1, 0)]"

lemma len_esL49: "length esL49 = 4 * TT + 4"
  using len_esL48 esL49_def by simp

lemma tmL49:
  assumes "jj < k"
    and "tps = tpsL t xs 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
    and "length xs = k"
    and "xs ! jj = (0, Some 0)"
    and "tps' = tpsL t (xs[jj:=(1, Some 1)]) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL49 jj) tps esL49 tps'"
  unfolding tmL49_def esL49_def
proof (rule traces_sequential)
  let ?tps = "tpsL t (xs[jj:=(1, Some 1)]) TT 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  show "traces (tmL48 jj) tps esL48 ?tps"
    using assms tmL48 by simp
  show "traces tm_left_until1 ?tps (map (Pair (n + 1)) (rev [0..<Suc (fmt n)]) @ [(n + 1, 0)]) tps'"
  proof (rule traces_tm_left_until_1I)
    show "1 < length ?tps"
      by simp
    show "begin_tape {y. y < G ^ (2 * k + 2) + 2 \<and> 1 < y \<and> dec y ! (2 * k + 1) = 1} (?tps ! 1)"
      using tpsL_1 begin_tape_zip_cont by simp
    show "map (Pair (n + 1)) (rev [0..<Suc (fmt n)]) @ [(n + 1, 0)] =
        map (Pair (?tps :#: 0)) (rev [0..< ?tps :#: 1]) @ [(?tps :#: 0, 0)]"
      using tpsL_pos_0 tpsL_pos_1 by presburger
    show "tps' = ?tps [1 := ?tps ! 1 |#=| 0]"
      using assms tpsL_def by simp
  qed
qed

definition xs49 :: "nat \<Rightarrow> (nat \<times> nat option) list" where
  "xs49 j \<equiv> replicate j (1, Some 1) @ replicate (k - j) (0, Some 0)"

lemma length_xs49: "j \<le> k \<Longrightarrow> length (xs49 j) = k"
  using xs49_def by simp

lemma xs49_less:
  assumes "j \<le> k" and "i < j"
  shows "xs49 j ! i = (1, Some 1)"
  unfolding xs49_def using assms by (simp add: nth_append)

lemma xs49_ge:
  assumes "j \<le> k" and "i \<ge> j" and "i < k"
  shows "xs49 j ! i = (0, Some 0)"
  unfolding xs49_def using assms by (simp add: nth_append)

lemma xs49_upd:
  assumes "j < k"
  shows "xs49 (Suc j) = (xs49 j)[j := (1, Some 1)]"
    (is "?lhs = ?rhs")
proof (rule nth_equalityI)
  show "length ?lhs = length ?rhs"
    by (simp add: Suc_leI assms length_xs49 less_imp_le_nat)
  show "\<And>i. i < length ?lhs \<Longrightarrow> ?lhs ! i = ?rhs ! i"
    using length_xs49 assms xs49_ge xs49_less
    by (metis less_Suc_eq less_or_eq_imp_le not_less nth_list_update)
qed

lemma tmL49_upt:
  assumes "j \<le> k"
    and "tps' = tpsL t (xs49 j) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL49_upt j) (tpsL4 t) (concat (replicate j esL49)) tps'"
  using assms
proof (induction j arbitrary: tps')
  case 0
  then show ?case
    using xs49_def tpsL4_def assms by auto
next
  case (Suc j)
  then have "j < k"
    by simp
  let ?tps = "tpsL t (xs49 j) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  have "tmL49_upt (Suc j) = tmL49_upt j ;; tmL49 j"
    by simp
  moreover have "concat (replicate (Suc j) esL49) = concat (replicate j esL49) @ esL49"
    by (smt (z3) append.assoc append_replicate_commute append_same_eq concat.simps(2) concat_append
      replicate.simps(2))
  moreover have "traces (tmL49_upt j ;; tmL49 j) (tpsL4 t) (concat (replicate j esL49) @ esL49) tps'"
  proof (rule traces_sequential)
    show "traces (tmL49_upt j) (tpsL4 t) (concat (replicate j esL49)) ?tps"
       using Suc by simp
    show "traces (tmL49 j) ?tps esL49 tps'"
      using tmL49[OF `j < k`, where ?tps="?tps"] length_xs49 xs49_upd Suc \<open>j < k\<close> xs49_ge
      by simp
  qed
  ultimately show ?case
    by simp
qed

definition "esL49_upt \<equiv> concat (replicate k esL49)"

lemma length_concat_replicate: "length (concat (replicate m xs)) = m * length xs"
  by (induction m) simp_all

lemma len_esL49_upt: "length esL49_upt = k * (4 * TT + 4)"
  using len_esL49 esL49_upt_def length_concat_replicate[of k esL49] by simp

corollary tmL49_upt':
  assumes "tps' = tpsL t (xs49 k) 0 1 (\<lambda>j. sim_move t ! j) (\<lambda>j. sim_write t ! j)"
  shows "traces (tmL49_upt k) (tpsL4 t) esL49_upt tps'"
  using tmL49_upt[of k] assms esL49_upt_def by simp

definition "esL9 t \<equiv> esL4 t @ esL49_upt"

lemma len_esL9: "length (esL9 t) = k * (4 * TT + 4) + t + 2 * TT + 4"
  using len_esL4 len_esL49_upt esL9_def by simp

lemma xs49_k: "xs49 k = replicate k (1, Some 1)"
  using xs49_def by simp

definition "tpsL9 t \<equiv> tpsL
  t
  (replicate k (1, Some 1))
  0
  1
  (\<lambda>j. sim_move t ! j)
  (\<lambda>j. sim_write t ! j)"

lemma tmL9:
  assumes "t < TT"
  shows "traces tmL9 (tpsL0 t) (esL9 t) (tpsL9 t)"
  unfolding tmL9_def esL9_def
  using assms tmL4 tmL49_upt'
  by (intro traces_sequential) (auto simp add: tpsL9_def xs49_k)

definition "esL10 t \<equiv> esL9 t @ esC t"

lemma len_esL10: "length (esL10 t) = k * (4 * TT + 4) + 2 * t + 2 * TT + 5"
  using len_esL9 len_esL9 esL10_def esC_def by simp

definition "tpsL10 t \<equiv> tpsL
  t
  (replicate k (1, Some 1))
  t
  1
  (\<lambda>j. sim_move t ! j)
  (\<lambda>j. sim_write t ! j)"

lemma tmL10:
  assumes "t < TT"
  shows "traces tmL10 (tpsL0 t) (esL10 t) (tpsL10 t)"
  unfolding tmL10_def esL10_def
proof (rule traces_sequential[OF tmL9[OF assms]])
  have "t \<le> TT"
    using assms by simp
  then show "traces tmC (tpsL9 t) (esC t) (tpsL10 t)"
    using tmC_general tpsL9_def tpsL10_def by simp
qed

definition "tpsL11 t \<equiv> tpsL
  (Suc t)
  (replicate k (0, Some 0))
  t
  0
  (\<lambda>j. sim_move t ! j)
  (\<lambda>j. sim_write t ! j)"

lemma enc_upd_2k:
  assumes "dec n = (map f [0..<k] @ map h [0..<k] @ [a, b])"
  shows "enc_upd n (2 * k) 1 = enc (map f [0..<k] @ map h [0..<k] @ [1, b])"
  using assms enc_upd_def by (metis append_assoc list_update_length nth_list_update_neq twok_nth)

lemma enc_upd_zip_cont:
  assumes "t < TT"
    and "xs1 = replicate k (1, Some 1)"
    and "xs0 = (replicate k (0, Some 0))"
  shows "enc_upd (zip_cont t xs1 t) (2 * k) 1 = zip_cont (Suc t) xs0 t"
proof -
  let ?n = "zip_cont t xs1 t"
  have xs1: "fst (xs1 ! j) = 1" "snd (xs1 ! j) = Some 1" if "j < k" for j
    using assms(2) that by simp_all
  have "zip_cont t xs1 t = enc
     (map (\<lambda>j. (exec (t + fst (xs1 ! j)) <:> j) t) [0..<k] @
      map (\<lambda>j. case snd (xs1 ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if t = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [0,
       if t = 0 then 1 else 0])"
    using zip_cont_def assms(1) by simp
  also have "... = enc
     (map (\<lambda>j. (exec (t + 1) <:> j) t) [0..<k] @
      map (\<lambda>j. case Some 1 of None \<Rightarrow> 0 | Some d \<Rightarrow> if t = exec (t + d) <#> j then 1 else 0) [0..<k] @
      [0,
       if t = 0 then 1 else 0])"
    using xs1 by (smt (z3) atLeastLessThan_iff map_eq_conv set_upt)
  finally have 1: "zip_cont t xs1 t = enc
     (map (\<lambda>j. (exec (Suc t) <:> j) t) [0..<k] @
      map (\<lambda>j. if t = exec (Suc t) <#> j then 1 else 0) [0..<k] @
      [0,
       if t = 0 then 1 else 0])"
       (is "_ = enc ?ys")
    by simp

  have xs0: "fst (xs0 ! j) = 0" "snd (xs0 ! j) = Some 0" if "j < k" for j
    using assms(3) that by simp_all
  have "zip_cont (Suc t) xs0 t = enc
     (map (\<lambda>j. (exec (Suc t + fst (xs0 ! j)) <:> j) t) [0..<k] @
      map (\<lambda>j. case snd (xs0 ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if t = exec (Suc t + d) <#> j then 1 else 0) [0..<k] @
      [1,
       if t = 0 then 1 else 0])"
    using zip_cont_def assms(1) by simp
  also have "... = enc
     (map (\<lambda>j. (exec (Suc t) <:> j) t) [0..<k] @
      map (\<lambda>j. case Some 0 of None \<Rightarrow> 0 | Some d \<Rightarrow> if t = exec (Suc t + d) <#> j then 1 else 0) [0..<k] @
      [1,
       if t = 0 then 1 else 0])"
    using xs0 by (smt (verit, ccfv_SIG) add.right_neutral atLeastLessThan_iff map_eq_conv set_upt)
  finally have 2: "zip_cont (Suc t) xs0 t = enc
     (map (\<lambda>j. (exec (Suc t) <:> j) t) [0..<k] @
      map (\<lambda>j. if t = exec (Suc t) <#> j then 1 else 0) [0..<k] @
      [1,
       if t = 0 then 1 else 0])"
       (is "_ = enc ?zs")
    by simp
  moreover have "?zs = ?ys [2 * k := 1]"
    by (smt (z3) Suc_1 append_assoc diff_zero length_append length_map length_upt list_update_length mult_Suc nat_mult_1)
  moreover have "?ys = dec ?n"
    using dec_zip_cont assms by simp
  ultimately show ?thesis
    using enc_upd_def 1 by presburger
qed

lemma enc_upd_zip_cont_upd:
  assumes "t < TT"
    and "xs1 = replicate k (1, Some 1)"
    and "xs0 = (replicate k (0, Some 0))"
  shows "(zip_cont t xs1) (t:=enc_upd (zip_cont t xs1 t) (2 * k) 1) = zip_cont (Suc t) xs0"
proof
  fix i
  consider "i = t" | "i \<noteq> t \<and> i < TT" | "i \<ge> TT"
    using assms(1) by linarith
  then show "((zip_cont t xs1)(t := enc_upd (zip_cont t xs1 t) (2 * k) 1)) i = zip_cont (Suc t) xs0 i"
  proof (cases)
    case 1
    then show ?thesis
      using enc_upd_zip_cont assms by simp
  next
    case 2
    then have "i \<noteq> t" "i < TT"
      by simp_all
    have xs1: "fst (xs1 ! j) = 1" "snd (xs1 ! j) = Some 1" if "j < k" for j
      using assms(2) that by simp_all
    have "zip_cont t xs1 i = enc
      (map (\<lambda>j. (exec (t + fst (xs1 ! j)) <:> j) i) [0..<k] @
       map (\<lambda>j. case snd (xs1 ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
       [if i < t then 1 else 0,
        if i = 0 then 1 else 0])"
      using zip_cont_def assms(1) `i < TT` by simp
    also have "... = enc
      (map (\<lambda>j. (exec (t + 1) <:> j) i) [0..<k] @
       map (\<lambda>j. case Some 1 of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (t + d) <#> j then 1 else 0) [0..<k] @
       [if i < t then 1 else 0,
        if i = 0 then 1 else 0])"
      using xs1 by (smt (z3) atLeastLessThan_iff map_eq_conv set_upt)
    finally have 1: "zip_cont t xs1 i = enc
      (map (\<lambda>j. (exec (Suc t) <:> j) i) [0..<k] @
       map (\<lambda>j. if i = exec (Suc t) <#> j then 1 else 0) [0..<k] @
       [if i < t then 1 else 0,
        if i = 0 then 1 else 0])"
      by simp

    have xs0: "fst (xs0 ! j) = 0" "snd (xs0 ! j) = Some 0" if "j < k" for j
      using assms(3) that by simp_all
    have "zip_cont (Suc t) xs0 i = enc
      (map (\<lambda>j. (exec (Suc t + fst (xs0 ! j)) <:> j) i) [0..<k] @
       map (\<lambda>j. case snd (xs0 ! j) of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (Suc t + d) <#> j then 1 else 0) [0..<k] @
       [if i < Suc t then 1 else 0,
        if i = 0 then 1 else 0])"
      using zip_cont_def[of "Suc t" "xs0" i] `i < TT` assms(1) by simp
    also have "... = enc
      (map (\<lambda>j. (exec (Suc t) <:> j) i) [0..<k] @
       map (\<lambda>j. case Some 0 of None \<Rightarrow> 0 | Some d \<Rightarrow> if i = exec (Suc t + d) <#> j then 1 else 0) [0..<k] @
       [if i < Suc t then 1 else 0,
        if i = 0 then 1 else 0])"
      using xs0 by (smt (verit, ccfv_SIG) add.right_neutral atLeastLessThan_iff map_eq_conv set_upt)
    finally have 2: "zip_cont (Suc t) xs0 i = enc
      (map (\<lambda>j. (exec (Suc t) <:> j) i) [0..<k] @
       map (\<lambda>j. if i = exec (Suc t) <#> j then 1 else 0) [0..<k] @
       [if i < t then 1 else 0,
        if i = 0 then 1 else 0])"
      using `i \<noteq> t` by simp
    then show ?thesis
      using 1 `i \<noteq> t` by simp
  next
    case 3
    then show ?thesis
      using zip_cont_def assms(1) by simp
  qed
qed

lemma sem_cmdL11:
  assumes "t < TT"
  shows "sem cmdL11 (0, tpsL10 t) = (1, tpsL11 t)"
proof (rule semI[of "2 * k + 3"])
  show "proper_command (2 * k + 3) cmdL11"
    using cmdL11_def by simp
  show len: "length (tpsL10 t) = 2 * k + 3" "length (tpsL11 t) = 2 * k + 3"
    using tpsL10_def tpsL11_def by simp_all
  show "fst (cmdL11 (read (tpsL10 t))) = 1"
    using cmdL11_def by simp
  let ?tps = "tpsL10 t"
  let ?xs = "replicate k (1::nat, Some 1::nat option)"
  have tps1: "?tps ! 1 = (zip_cont t ?xs, t)"
    using tpsL_1 tpsL10_def by simp
  have tps1': "tpsL11 t ! 1 = (zip_cont (Suc t) (replicate k (0, Some 0)), t)"
    using tpsL_1 tpsL11_def by simp
  let ?rs = "read ?tps"
  have "is_code (?rs ! 1)"
    using tpsL10_def assms read_tpsL_1_bounds by simp
  have rs1: "?rs ! 1 = zip_cont t ?xs t"
    using tps1 read_def tpsL_def tpsL10_def by force
  show " act (cmdL11 ?rs [!] j) (?tps ! j) = tpsL11 t ! j"
      if "j < 2 * k + 3" for j
    proof -
    consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < 2 * k + 3` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using tpsL10_def tpsL11_def read_tpsL_0 cmdL11_def act_Stay len(1) that tpsL_0
        by (smt (verit) append_Cons nth_Cons_0 prod.sel(2))
    next
      case 2
      then have "act (cmdL11 ?rs [!] j) (?tps ! j) = act (cmdL11 ?rs [!] 1) (?tps ! 1)"
        by simp
      also have "... = act (enc_upd (?rs ! 1) (2 * k) 1, Stay) (?tps ! 1)"
        using cmdL11_def `is_code (?rs ! 1)` by simp
      also have "... = (?tps ! 1) |:=| enc_upd (?rs ! 1) (2 * k) 1"
        by (simp add: act_Stay tps1 "2" act_Stay' len(1) that)
      also have "... = tpsL11 t ! 1"
        using enc_upd_zip_cont_upd rs1 tps1' tps1 assms by simp
      finally show ?thesis
        using 2 by simp
    next
      case 3
      then have "act (cmdL11 ?rs [!] j) ((?tps) ! j) = act (cmdL11 ?rs [!] 2) (?tps ! 2)"
        by simp
      also have "... = act (?rs ! 2, Stay) (?tps ! 2)"
        using cmdL11_def by simp
      also have "... = ?tps ! 2"
        using act_Stay len by simp
      also have "... = (tpsL11 t) ! 2"
        using tpsL_2 tpsL11_def tpsL10_def by simp
      also have "... = (tpsL11 t) ! j"
        using 3 by simp
      finally show ?thesis .
    next
      case 4
      then have "act (cmdL11 ?rs [!] j) (?tps ! j) = act (?rs ! j, Stay) (?tps ! j)"
        using cmdL11_def threeplus2k_2[where ?a="(?rs ! 0, Stay)"] by simp
      also have "... = (tpsL10 t) ! j"
        using len act_Stay that by simp
      also have "... = (tpsL11 t) ! j"
        using tpsL11_def tpsL10_def tpsL_mvs' 4 by simp
      finally show ?thesis .
    next
      case 5
      then have "act (cmdL11 ?rs [!] j) (?tps ! j) = act (?rs ! j, Stay) (?tps ! j)"
        using cmdL11_def threeplus2k_3[where ?a="(?rs ! 0, Stay)"] by simp
      also have "... = (tpsL10 t) ! j"
        using len act_Stay that by simp
      also have "... = (tpsL11 t) ! j"
        using tpsL11_def tpsL10_def tpsL_symbs' 5 by simp
      finally show ?thesis .
    qed
  qed
qed

definition "esL11 t \<equiv> esL10 t @ [(n + 1, t)]"

lemma len_esL11: "length (esL11 t) = k * (4 * TT + 4) + 2 * t + 2 * TT + 6"
  using len_esL10 esL11_def by simp

lemma tmL11:
  assumes "t < TT"
  shows "traces tmL11 (tpsL0 t) (esL11 t) (tpsL11 t)"
  unfolding tmL11_def esL11_def
proof (rule traces_sequential[OF tmL10[OF assms]])
  let ?cmd = "[cmdL11]"
  let ?es = "[(n + 1, t)]"
  show "traces ?cmd (tpsL10 t) ?es (tpsL11 t)"
  proof
    show 1: "execute ?cmd (0, tpsL10 t) (length ?es) = (length ?cmd, tpsL11 t)"
    proof -
      have "execute ?cmd (0, tpsL10 t) (length ?es) = exe ?cmd (0, tpsL10 t)"
        by simp
      also have "... = sem cmdL11 (0, tpsL10 t)"
        using exe_lt_length cmdL11_def by simp
      finally show ?thesis
        using sem_cmdL11[OF assms] by simp
    qed
    show "\<And>i. i < length [(n + 1, t)] \<Longrightarrow>
          fst (execute ?cmd (0, tpsL10 t) i) < length ?cmd"
      by simp
    show "\<And>i. i < length [(n + 1, t)] \<Longrightarrow>
          execute ?cmd (0, tpsL10 t) (Suc i) <#> 0 = fst (?es ! i) \<and>
          execute ?cmd (0, tpsL10 t) (Suc i) <#> 1 = snd (?es ! i)"
      using 1 tpsL11_def tpsL_pos_0 tpsL_pos_1
      by (metis One_nat_def add.commute fst_conv less_Suc0 list.size(3) list.size(4) nth_Cons_0 plus_1_eq_Suc snd_conv)
  qed
qed

definition "esL12 t \<equiv> esL11 t @ map (\<lambda>i. (n + 1, i)) (rev [0..<t]) @ [(n + 1, 0)]"

lemma len_esL12: "length (esL12 t) = k * (4 * TT + 4) + 3 * t + 2 * TT + 7"
  using len_esL11 esL12_def by simp

definition "tpsL12 t \<equiv> tpsL
  (Suc t)
  (replicate k (0, Some 0))
  0
  0
  (\<lambda>j. sim_move t ! j)
  (\<lambda>j. sim_write t ! j)"

lemma tmL12:
  assumes "t < TT"
  shows "traces tmL12 (tpsL0 t) (esL12 t) (tpsL12 t)"
  unfolding tmL12_def esL12_def
proof (rule traces_sequential[OF tmL11[OF assms]])
  show "traces tm_left_until1 (tpsL11 t) (map (Pair (n + 1)) (rev [0..<t]) @ [(n + 1, 0)]) (tpsL12 t)"
  proof (rule traces_tm_left_until_1I)
    show "1 < length (tpsL11 t)"
      using tpsL11_def by simp
    show "begin_tape {y. y < G ^ (2 * k + 2) + 2 \<and> 1 < y \<and> dec y ! (2 * k + 1) = 1} (tpsL11 t ! 1)"
      using tpsL_1 begin_tape_zip_cont tpsL11_def by simp
    show "map (Pair (n + 1)) (rev [0..<t]) @ [(n + 1, 0)] =
      map (Pair (tpsL11 t :#: 0)) (rev [0..<tpsL11 t :#: 1]) @ [(tpsL11 t :#: 0, 0)]"
      using tpsL_pos_0 tpsL_pos_1 tpsL11_def by simp
    show "tpsL12 t = (tpsL11 t)[1 := tpsL11 t ! 1 |#=| 0]"
      using tpsL12_def tpsL11_def tpsL_def by simp
  qed
qed

definition "tpsL13 t \<equiv> tpsL
    (Suc t)
    (replicate k (0, Some 0))
    0
    0
    (\<lambda>j. 0)
    (\<lambda>j. 0)"

definition "esL13 t \<equiv> esL12 t @ [(n + 1, 0)]"

lemma len_esL13: "length (esL13 t) = k * (4 * TT + 4) + 3 * t + 2 * TT + 8"
  using len_esL12 esL13_def by simp

lemma tmL13:
  assumes "t < TT"
  shows "traces tmL13 (tpsL0 t) (esL13 t) (tpsL13 t)"
  unfolding tmL13_def esL13_def
proof (rule traces_sequential[OF tmL12[OF assms]])
  show "traces (tm_write_many {3..<2 * k + 3} 0) (tpsL12 t) [(n + 1, 0)] (tpsL13 t)"
  proof (rule traces_tm_write_manyI[where ?k="2*k+3"])
    show "0 \<notin> {3..<2 * k + 3}"
      by simp
    show "\<forall>j\<in>{3..<2 * k + 3}. j < 2 * k + 3"
      by simp
    show "2 \<le> 2 * k + 3"
      by simp
    show "length (tpsL12 t) = 2 * k + 3" "length (tpsL13 t) = 2 * k + 3"
      using tpsL12_def tpsL13_def length_tpsL by simp_all
    show "tpsL13 t ! j = tpsL12 t ! j |:=| 0" if "j \<in> {3..<2 * k + 3}" for j
    proof (cases "j < k + 3")
      case True
      then have "3 \<le> j \<and> j < k + 3"
        using that by simp
      then show ?thesis
        using tpsL13_def tpsL12_def tpsL_mvs' onesie_write by simp
    next
      case False
      then have "k + 3 \<le> j \<and> j < 2 * k + 3"
        using that by simp
      then show ?thesis
        using tpsL13_def tpsL12_def tpsL_symbs' onesie_write by simp
    qed
    show "tpsL13 t ! j = tpsL12 t ! j" if "j < 2 * k + 3" "j \<notin> {3..<2 * k + 3}" for j
    proof -
      from that have "j < 3"
        by simp
      then show ?thesis
        using tpsL13_def tpsL12_def tpsL_def less_Suc_eq numeral_3_eq_3 by auto
    qed
    show "[(n + 1, 0)] = [(tpsL12 t :#: 0, tpsL12 t :#: 1)]"
      using tpsL12_def tpsL_pos_0 tpsL_pos_1 by simp
  qed
qed

corollary tmL13':
  assumes "t < TT"
  shows "traces tmL13 (tpsC1 t) (esL13 t) (tpsL13 t)"
  using tmL13 tpsC1_def tpsL0_def assms by simp

definition "esLoop_while t \<equiv>
  esC t @ [(tpsC1 t :#: 0, tpsC1 t :#: 1)] @ esL13 t @ [(tpsL13 t :#: 0, tpsL13 t :#: 1)]"

definition "esLoop_break \<equiv> (esC TT) @ [(tpsC1 TT :#: 0, tpsC1 TT :#: 1)]"

lemma len_esLoop_while: "length (esLoop_while t) = k * (4 * TT + 4) + 4 * t + 2 * TT + 11"
  using len_esL13 esC_def esLoop_while_def by simp

lemma tmLoop_while:
  assumes "t < TT"
  shows "trace tmLoop (0, tpsC0 t) (esLoop_while t) (0, tpsL13 t)"
  unfolding tmLoop_def
proof (rule tm_loop_sem_true_tracesI[OF tmC tmL13'])
  show "t \<le> TT" and "t < TT"
    using assms by simp_all
  show "0 < read (tpsC1 t) ! 1"
    using tpsC1_def read_tpsL_1_bounds(1) assms by (metis gr0I not_one_less_zero)
  show "esLoop_while t =
      esC t @ [(tpsC1 t :#: 0, tpsC1 t :#: 1)] @ esL13 t @ [(tpsL13 t :#: 0, tpsL13 t :#: 1)]"
    using esLoop_while_def by simp
qed

lemma tmLoop_while_end:
  "trace tmLoop (0, tpsC0 0) (concat (map esLoop_while [0..<TT])) (0, tpsC0 TT)"
proof (rule tm_loop_trace_simple)
  have "tpsL13 t = tpsC0 (Suc t)" if "t < TT" for t
    using tpsL13_def tpsC0_def by simp
  then show "trace tmLoop (0, tpsC0 i) (esLoop_while i) (0, tpsC0 (Suc i))" if "i < TT" for i
    using tmLoop_while that by simp
qed

lemma len_esLoop_break: "length esLoop_break = TT + 2"
  using esLoop_break_def esC_def by simp

lemma tmLoop_break: "traces tmLoop (tpsC0 TT) esLoop_break (tpsC1 TT)"
  unfolding tmLoop_def
proof (rule tm_loop_sem_false_traces[OF tmC])
  show "TT \<le> TT"
    by simp
  show "\<not> 0 < read (tpsC1 TT) ! 1"
    using read_tpsL_1 tpsC1_def by simp
  show "esLoop_break = esC (TT) @ [(tpsC1 TT :#: 0, tpsC1 TT :#: 1)]"
    using esLoop_break_def by simp
qed

definition "esLoop \<equiv> concat (map esLoop_while [0..<TT]) @ esLoop_break"

lemma len_esLoop1: "u \<le> TT \<Longrightarrow> length (concat (map esLoop_while [0..<u])) \<le> u * (k * (4 * TT + 4) + 4 * TT + 2 * TT + 11)"
  using len_esLoop_while by (induction u) simp_all

lemma len_esLoop2: "length (concat (map esLoop_while [0..<TT])) \<le> TT * (k * (4 * TT + 4) + 4 * TT + 2 * TT + 11)"
  using len_esLoop1[of TT] by simp

lemma len_esLoop3: "length esLoop \<le> TT * (k * (4 * TT + 4) + 4 * TT + 2 * TT + 11) + TT + 2"
  using len_esLoop2 esC_def esLoop_def esLoop_break_def by simp

lemma len_esLoop: "length esLoop \<le> 28 * k * TT * TT"
proof -
  have "length esLoop \<le> TT * (k * (4 * TT + 4) + 4 * TT + 2 * TT + 11) + TT + 2"
    using len_esLoop3 .
  also have "... = TT * (k * (4 * TT + 4) + 6 * TT + 11) + TT + 2"
    by simp
  also have "... \<le> TT * (k * (4 * TT + 4) + 6 * TT + 11) + 3 * TT"
    by simp
  also have "... = TT * k * (4 * TT + 4) + TT * 6 * TT + TT * 11 + 3 * TT"
    by algebra
  also have "... = TT * k * (4 * TT + 4) + TT * 6 * TT + 14 * TT"
    by simp
  also have "... = k * 4 * TT * TT + k * 4 * TT + 6 * TT * TT + 14 * TT"
    by algebra
  also have "... \<le> k * 4 * TT * TT + k * 4 * TT * TT + 6 * TT * TT + 14 * TT * TT"
    by simp
  also have "... = (k * 4 + k * 4 + 6 + 14) * TT * TT"
    by algebra
  also have "... = (k * 8 + 20) * TT * TT"
    by algebra
  also have "... \<le> 28 * k * TT * TT"
  proof -
    have "k * 8 + 20 \<le> 28 * k"
      using k_ge_2 by simp
    then show ?thesis
      by (meson mult_le_mono1)
  qed
  finally show ?thesis
    by simp
qed

lemma tmLoop: "traces tmLoop (tpsC0 0) esLoop (tpsC1 TT)"
  unfolding esLoop_def using traces_additive[OF tmLoop_while_end tmLoop_break] .

lemma tps9_tpsC0: "tps9 = tpsC0 0"
  using tps9_def tpsC0_def tps9_tpsL by simp

definition "es10 \<equiv> es9 @ esLoop"

lemma len_es10: "length es10 \<le> length (es_fmt n) + 40 * k * TT * TT"
proof -
  have "length es10 \<le> length (es_fmt n) + 2 * TT + 2 * n + 8 + 28 * k * TT * TT"
    using len_es9 len_esLoop es10_def by simp
  also have "... \<le> length (es_fmt n) + 2 * TT + 2 * TT + 8 + 28 * k * TT * TT"
  proof -
    have "2 * n \<le> 2 * TT"
      using fmt_ge_n Suc_mult_le_cancel1 le_SucI numeral_2_eq_2 by metis
    then show ?thesis
      by simp
  qed
  also have "... \<le> length (es_fmt n) + 12 * TT * TT + 28 * k * TT * TT"
    by simp
  also have "... \<le> length (es_fmt n) + 12 * k * TT * TT + 28 * k * TT * TT"
  proof -
    have "12 \<le> 12 * k"
      using k_ge_2 by simp
    then have "12 * TT * TT \<le> 12 * k * TT * TT"
      using mult_le_mono1 by presburger
    then show ?thesis
      by simp
  qed
  also have "... = length (es_fmt n) + 40 * k * TT * TT"
    by linarith
  finally show ?thesis .
qed

lemma tm10: "traces tm10 tps0 es10 (tpsC1 TT)"
  unfolding tm10_def es10_def
  using traces_sequential[OF tm9] tps9_tpsC0 tmLoop
  by simp


subsubsection \<open>Cleaning up the output\<close>

abbreviation "tps10 \<equiv> tpsC1 TT"

definition "es11 \<equiv> es10 @ map (\<lambda>i. (n + 1, i)) (rev [0..<TT]) @ [(n + 1, 0)]"

lemma len_es11: "length es11 \<le> length (es_fmt n) + 40 * k * TT * TT + Suc TT"
  using es11_def len_es10 by simp

definition "tps11 \<equiv> tps10[1 := ltransplant (tps10 ! 1) (tps10 ! 1) ec1 TT]"

lemma tm11: "traces tm11 tps0 es11 tps11"
  unfolding tm11_def es11_def
proof (rule traces_sequential[OF tm10])
  show "traces
     (tm_ltrans_until 1 1 StartSym ec1)
     (tpsC1 (Suc (fmt n)))
     (map (Pair (n + 1)) (rev [0..<Suc (fmt n)]) @ [(n + 1, 0)]) tps11"
  proof (rule traces_tm_ltrans_until_11I[where ?n=TT and ?G=G'])
    show "1 < length (tpsC1 (Suc (fmt n)))"
      using tpsC1_def by simp
    show "\<forall>h<G'. ec1 h < G'"
      using ec1 by simp
    show "lneigh (tps10 ! 1) StartSym TT"
      using begin_tape_def begin_tape_zip_cont tpsC1_def tpsL_def by (intro lneighI) simp_all
    show "Suc (fmt n) \<le> tpsC1 (Suc (fmt n)) :#: 1"
      using tpsC1_def tpsL_def by simp
    show "map (Pair (n + 1)) (rev [0..<TT]) @ [(n + 1, 0)] =
        map (\<lambda>i. (tps10 :#: 0, tps10 :#: 1 - Suc i)) [0..<TT] @ [(tps10 :#: 0, tps10 :#: 1 - TT)]"
    proof -
      have 1: "tps10 :#: 0 = n + 1"
        using tpsC1_def tpsL_pos_0 by simp
      moreover have 2: "tps10 :#: 1 = TT"
        using tpsC1_def tpsL_pos_1 by simp
      ultimately have "map (\<lambda>i. (tps10 :#: 0, tps10 :#: 1 - Suc i)) [0..<TT] = map (\<lambda>i. (n + 1, TT - Suc i)) [0..<TT]"
        by simp
      moreover have "map (\<lambda>i. (c1, c2 - Suc i)) [0..<c2] = map (Pair c1) (rev [0..<c2])" for c1 c2 :: nat
        by (intro nth_equalityI, simp)
         (metis (no_types, lifting) add_cancel_left_left add_lessD1 diff_less diff_zero
          length_map length_upt nth_map_upt rev_map rev_nth zero_less_Suc)
      ultimately have "map (\<lambda>i. (tps10 :#: 0, tps10 :#: 1 - Suc i)) [0..<TT] = map (Pair (n + 1)) (rev [0..<TT])"
        by metis
      then show ?thesis
        using 1 2 by simp
    qed
    show "tps11 = (tpsC1 TT) [1 := ltransplant (tpsC1 TT ! 1) (tpsC1 TT ! 1) ec1 TT]"
      using tps11_def by simp
  qed
qed

definition "es12 \<equiv> es11 @ [(n + 1, 1)]"

text \<open>
The upper bound on the length of the trace will help us establish an upper bound
of the total running time.
\<close>

lemma length_es12: "length es12 \<le> length (es_fmt n) + 43 * k * TT * TT"
proof -
  have "length es12 \<le> length (es_fmt n) + 40 * k * TT * TT + 3 * TT * TT"
    using es12_def len_es11 by simp
  moreover have "3 * TT * TT \<le> 3 * k * TT * TT"
  proof -
    have "3 \<le> 3 * k"
      using k_ge_2 by simp
    then show ?thesis
      by (meson mult_le_mono1)
  qed
  ultimately show ?thesis
    by linarith
qed

definition "tps12 \<equiv> tps11[1 := tps11 ! 1 |:=| (ec1 (tps11 :.: 1)) |+| 1]"

lemma tm12: "traces tm12 tps0 es12 tps12"
  unfolding tm12_def es12_def
proof (rule traces_sequential[OF tm11])
  show "traces (tm_rtrans 1 ec1) tps11 [(n + 1, 1)] tps12"
  proof (rule traces_tm_rtrans_1I)
    show "1 < length tps11"
      using tps11_def tpsC1_def by simp
    show "[(n + 1, 1)] = [(tps11 :#: 0, tps11 :#: 1 + 1)]"
      using tps11_def tpsC1_def tpsL_pos_0 tpsL_pos_1 ltransplant_def by simp
    show "tps12 = tps11[1 := tps11 ! 1 |:=| ec1 (tps11 :.: 1) |+| 1]"
      using tps12_def by simp
  qed
qed

lemma tps11_0: "(tps11 ::: 1) 0 = (zip_cont TT (replicate k (0, Some 0))) 0"
  using tps11_def tpsC1_def tpsL_def ltransplant_def by simp

lemma tps11_gr0_exec:
  assumes "i > 0"
  shows "(tps11 ::: 1) i = (exec TT <:> 1) i"
proof -
  let ?tp = "tps10 ! 1"
    let ?xs = "replicate k (0, Some 0)"
  have 1: "tps11 ! 1 = ltransplant ?tp ?tp ec1 TT"
    using tps11_def tpsC1_def tpsL_def by simp
  have 2: "tps10 :#: 1 = TT"
    using tpsC1_def tpsL_def by simp
  show ?thesis
  proof (cases "i \<le> TT")
    case le_TT: True
    then have "0 < i \<and> i \<le> TT"
      using assms by simp
    then have *: "(tps11 ::: 1) i = ec1 (fst ?tp i)"
      using 1 tpsC1_def tpsL_def ltransplant_def by simp
    show ?thesis
    proof (cases "i = TT")
      case True
      then have "\<not> is_code ((zip_cont TT ?xs) i)"
        by (simp add: zip_cont_eq_0)
      then have "(tps11 ::: 1) i = 0"
        using * 2 True tpsC1_at_T by simp
      moreover have "(exec TT <:> 1) TT = 0"
        using tps_ge_TT_0 by simp
      ultimately show ?thesis
        using True by simp
    next
      case False
      then have "i < TT"
        using le_TT by simp
      then have "fst ?tp i = (zip_cont TT ?xs) i"
        using tpsC1_def tpsL_def by simp
      then have "(tps11 ::: 1) i = ec1 ((zip_cont TT ?xs) i)"
        using * by simp
      moreover have "is_code ((zip_cont TT ?xs) i)"
        using zip_cont_gt_1 zip_cont_less `i < TT` by simp
      ultimately have "(tps11 ::: 1) i = enc_nth ((zip_cont TT ?xs) i) 1"
        by simp
      then have "(tps11 ::: 1) i = (exec TT <:> 1) i"
        using enc_nth_def dec_zip_cont_less_k[OF `i < TT`] k_ge_2 by simp
      then show ?thesis
        by simp
    qed
  next
    case False
    then have "(tps11 ::: 1) i = 0"
      using 1 tpsC1_def tpsL_def ltransplant_def zip_cont_eq_0 by force
    moreover have "(exec TT <:> 1) i = 0"
      using False tps_ge_TT_0 by simp
    ultimately show ?thesis
      by simp
  qed
qed

definition "tps12' \<equiv>
    [(\<lfloor>zs\<rfloor>, n + 1),
     (exec TT <:> 1, 1),
     \<lceil>fst (exec TT)\<rceil>] @
    map (\<lambda>i. \<lceil>\<box>\<rceil>) [0..<k] @
    map (\<lambda>i. \<lceil>\<box>\<rceil>) [0..<k]"

lemma tps12': "tps12' = tps12"
proof (rule nth_equalityI)
  show "length tps12' = length tps12"
    using tps12'_def tps12_def tps11_def tpsC1_def by simp
  show "tps12' ! j = tps12 ! j" if "j < length tps12'" for j
  proof -
    have "length tps12' = 2 * k + 3"
      using tps12'_def by simp
    then consider "j = 0" | "j = 1" | "j = 2" | "3 \<le> j \<and> j < k + 3" | "k + 3 \<le> j \<and> j < 2 * k + 3"
      using `j < length tps12'` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        unfolding tps12'_def tps12_def tps11_def tpsC1_def tpsL_def by simp
    next
      case 2
      then have lhs: "tps12' ! j = (\<lambda>i. (exec TT <:> 1) i, 1)"
        using tps12'_def by simp
      let ?tp = "tps10 ! 1"
      let ?xs = "replicate k (0, Some 0)"
      have "tps11 :#: 1 = 0"
        using tps11_def ltransplant_def tpsC1_def tpsL_pos_1 by simp
      have rhs: "tps12 ! j = (ltransplant ?tp ?tp ec1 TT) |:=| (ec1 (tps11 :.: 1)) |+| 1"
        using tps12_def 2 \<open>length tps12' = length tps12\<close> tps11_def that by simp
      have tps10: "tps10 ! j = (zip_cont TT ?xs, TT)"
        using tpsC1_def 2 tpsL_1 by simp
      show "tps12' ! j = tps12 ! j"
      proof
        show "tps12' :#: j = tps12 :#: j"
          using lhs rhs ltransplant_def tps10 2 by simp
        have tps12: "tps12 ! 1 = tps11 ! 1 |:=| (ec1 (tps11 :.: 1)) |+| 1"
          using tps12_def "2" \<open>length tps12' = length tps12\<close> that by auto
        have "(tps12' ::: 1) i = (tps12 ::: 1) i" for i
        proof (cases "i = 0")
          case True
          then have "(tps12 ::: 1) i = ec1 (tps11 :.: 1)"
            using tps12 `tps11 :#: 1 = 0` by simp
          moreover have "(tps11 :.: 1) = (zip_cont TT ?xs) 0"
            using tps11_0 `tps11 :#: 1 = 0` by simp
          ultimately have "(tps12 ::: 1) i = ec1 ((zip_cont TT ?xs) 0)"
            by simp
          moreover have "is_code ((zip_cont TT ?xs) 0)"
            using zip_cont_gt_1 zip_cont_less by simp
          ultimately have "(tps12 ::: 1) i = enc_nth ((zip_cont TT ?xs) 0) 1"
            by simp
          then have "(tps12 ::: 1) i = enc_nth (zip_cont TT ?xs i) 1"
            using True by simp
          then have "(tps12 ::: 1) i = (exec TT <:> 1) i"
            using enc_nth_def dec_zip_cont_less_k True k_ge_2 by simp
          then show ?thesis
            using tps12'_def by simp
        next
          case False
          then have "(tps12 ::: 1) i = (tps11 ::: 1) i"
            using tps12 `tps11 :#: 1 = 0` by simp
          then have "(tps12 ::: 1) i = (exec TT <:> 1) i"
            using False tps11_gr0_exec by simp
          moreover have "(tps12' ::: 1) i = (exec TT <:> 1) i"
            using tps12'_def by simp
          ultimately show ?thesis
            by simp
        qed
        then show "tps12' ::: j = tps12 ::: j"
          using 2 by auto
      qed
    next
      case 3
      then show ?thesis
        unfolding tps12'_def tps12_def tps11_def tpsC1_def tpsL_def by simp
    next
      case 4
      then show ?thesis
        unfolding tps12'_def tps12_def tps11_def tpsC1_def
        using tpsL_mvs' threeplus2k_2[where ?a="(\<lfloor>zs\<rfloor>, n + 1)"]
        by simp
    next
      case 5
      then show ?thesis
        unfolding tps12'_def tps12_def tps11_def tpsC1_def
        using tpsL_symbs' threeplus2k_3[where ?a="(\<lfloor>zs\<rfloor>, n + 1)"]
        by simp
    qed
  qed
qed

lemma tm12': "traces tm12 tps0 es12 tps12'"
  using tm12 tps12' by simp

end  (* context for zs *)


subsection \<open>Shrinking the Turing machine to two tapes\<close>

text \<open>
The simulator TM @{const tm12} has $2k + 3$ tapes, of which $2k + 1$ are
immobile and thus can be removed by the memorization-in-states technique,
resulting in a two-tape TM.
\<close>

lemma immobile_tm12:
  assumes "j > 1" and "j < 2 * k + 3"
  shows "immobile tm12 j (2 * k + 3)"
proof -
  have "immobile tm1 j (2 * k + 3)"
    unfolding tm1_def
    using immobile_append_tapes[of j "2*k+3", OF _ _ _ fmt(1)] assms
    by simp
  moreover have "immobile tm1_2 j (2 * k + 3)"
    using tm1_2_def tm_const_until_def immobile_tm_trans_until assms by simp
  ultimately have "immobile tm2 j (2 * k + 3)"
    using tm2_def immobile_sequential tm1_2_tm tm1_tm by simp
  then have "immobile tm3 j (2 * k + 3)"
    using tm3_def immobile_sequential[OF tm2_tm] tm_start_tm immobile_tm_start assms G'_ge by simp
  then have "immobile tm4 j (2 * k + 3)"
    using tm4_def immobile_sequential[OF tm3_tm tm3_4_tm] immobile_tm_write assms by simp
  then have "immobile tm5 j (2 * k + 3)"
    using tm5_def immobile_sequential[OF tm4_tm] G'_ge(1) immobile_tm_right tm_right_tm assms by simp
  then have "immobile tm6 j (2 * k + 3)"
    using tm6_def immobile_sequential[OF tm5_tm tm5_6_tm] immobile_tm_trans_until tm5_6_def assms by simp
  then have "immobile tm7 j (2 * k + 3)"
    using tm7_def immobile_sequential[OF tm6_tm tm_left_until1_tm] immobile_tm_left_until assms by simp
  then have "immobile tm8 j (2 * k + 3)"
    using tm8_def immobile_sequential[OF tm7_tm] immobile_tm_write assms G'_ge tm_write_tm by simp
  then have 9: "immobile tm9 j (2 * k + 3)"
    using tm9_def immobile_sequential[OF tm8_tm] immobile_tm_write_many tm_write_many_tm k_ge_2 G'_ge assms
    by simp

  have C: "immobile tmC j (2 * k + 3)"
    unfolding tmC_def tm_right_until_def tm_cp_until_def
    using tm_cp_until_tm immobile_tm_trans_until G'_ge(1) assms
    by simp

  have "cmdL2 rs [~] j = Stay" if "length rs = 2 * k + 3" for rs
  proof (cases "rs ! 1 = \<box>")
    case True
    then show ?thesis
      using cmdL2_def assms that by simp
  next
    case False
    then consider "j = 2" | "3 \<le> j \<and> j < 3 + k" | "3 + k \<le> j \<and> j < 2 * k + 3"
      using assms by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using cmdL2_def assms that by simp
    next
      case 2
      then show ?thesis
        using assms that cmdL2_at_3 False by simp
    next
      case 3
      then show ?thesis
        using assms that cmdL2_at_4 False by simp
    qed
  qed
  then have "immobile tmL1_2 j (2 * k + 3)"
    using tmL1_2_def by auto
  then have "immobile tmL2 j (2 * k + 3)"
    unfolding tmL2_def tmL1_def
    using tm_left_until1_tm immobile_tm_left_until tmL2_tm immobile_sequential tmL1_2_tm assms
    by auto
  moreover have "cmdL3 rs [~] j = Stay" if "length rs = 2 * k + 3" for rs
  proof -
    consider "j = 2" | "3 \<le> j \<and> j < 3 + k" | "3 + k \<le> j \<and> j < 2 * k + 3"
      using assms by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using cmdL3_def assms that by simp
    next
      case 2
      then show ?thesis
        using assms that cmdL3_at_3a cmdL3_at_3b
        by (metis (no_types, lifting) add.commute prod.sel(2))
    next
      case 3
      then show ?thesis
        using assms that cmdL3_at_4a cmdL3_at_4b
        by (metis (no_types, lifting) add.commute prod.sel(2))
    qed
  qed
  ultimately have "immobile tmL3 j (2 * k + 3)"
    unfolding tmL3_def
    using tmL2_tm immobile_sequential assms tmL2_3_def tmL2_3_tm immobile_def
    by simp
  then have L4: "immobile tmL4 j (2 * k + 3)"
    unfolding tmL4_def
    using tmL3_tm immobile_sequential assms tm_left_until1_tm immobile_tm_left_until
    by auto

  have "(cmdL5 jj) rs [~] j = Stay" if "length rs = 2 * k + 3" and "jj < k" for rs jj
  proof (cases "rs ! 1 = \<box>")
    case True
    then show ?thesis
      using cmdL5_eq_0 assms that by simp
  next
    case False
    then consider "j = 2" | "3 \<le> j \<and> j < 3 + k" | "3 + k \<le> j \<and> j < 2 * k + 3"
      using assms by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using that by (simp add: cmdL5_def)
    next
      case 2
      then show ?thesis
        using assms that cmdL5_at_3 False by simp
    next
      case 3
      then show ?thesis
        using assms that cmdL5_at_4 False by simp
    qed
  qed
  then have "immobile (tmL45 jj) j (2 * k + 3)" if "jj < k" for jj
    by (auto simp add: that tmL45_def)
  then have L46: "immobile (tmL46 jj) j (2 * k + 3)" if "jj < k" for jj
    using tmL46_def immobile_sequential[OF tmL45_tm] tm_left_tm immobile_tm_left assms that k_ge_2 G'_ge by simp

  have "(cmdL7 jj) rs [~] j = Stay" if "length rs = 2 * k + 3" and "jj < k" for rs jj
  proof -
    consider (a) "condition7a rs jj" | (b) "condition7b rs jj" | (c) "condition7c rs jj"
      by blast
    then show ?thesis
    proof (cases)
      case a
      consider "j = 2" | "3 \<le> j \<and> j < k + 3" | "3 + k \<le> j \<and> j < 2 * k + 3"
        using assms by linarith
      then show ?thesis
        using cmdL7_def a threeplus2k_2[of _ _ "(rs ! 0, Stay)"] threeplus2k_3[of _ _ "(rs ! 0, Stay)"]
        by (cases) simp_all
    next
      case b
      consider "j = 2" | "3 \<le> j \<and> j < k + 3" | "3 + k \<le> j \<and> j < 2 * k + 3"
        using assms by linarith
      then show ?thesis
        using cmdL7_def b threeplus2k_2[of _ _ "(rs ! 0, Stay)"] threeplus2k_3[of _ _ "(rs ! 0, Stay)"]
        by (cases) simp_all
    next
      case c
      consider "j = 2" | "3 \<le> j \<and> j < k + 3" | "3 + k \<le> j \<and> j < 2 * k + 3"
        using assms by linarith
      then show ?thesis
        using cmdL7_def c threeplus2k_2[of _ _ "(rs ! 0, Stay)"] threeplus2k_3[of _ _ "(rs ! 0, Stay)"]
        by (cases) simp_all
    qed
  qed
  then have "immobile (tmL67 jj) j (2 * k + 3)" if "jj < k" for jj
    by (auto simp add: that tmL67_def)
  then have L47: "immobile (tmL47 jj) j (2 * k + 3)" if "jj < k" for jj
    using tmL47_def immobile_sequential[OF tmL46_tm tmL67_tm] L46 assms that by simp

  have "(cmdL8 jj) rs [~] j = Stay" if "length rs = 2 * k + 3" and "jj < k" for rs jj
  proof -
    consider (a) "condition8a rs jj" | (b) "condition8b rs jj" | (c) "condition8c rs jj" | (d) "condition8d rs jj"
      by blast
    then show ?thesis
    proof (cases)
      case a
      consider "j = 2" | "3 \<le> j \<and> j < k + 3" | "3 + k \<le> j \<and> j < 2 * k + 3"
        using assms by linarith
      then show ?thesis
        using cmdL8_def a threeplus2k_2[of _ _ "(rs ! 0, Stay)"] threeplus2k_3[of _ _ "(rs ! 0, Stay)"]
        by (cases) simp_all
    next
      case b
      consider "j = 2" | "3 \<le> j \<and> j < k + 3" | "3 + k \<le> j \<and> j < 2 * k + 3"
        using assms by linarith
      then show ?thesis
        using cmdL8_def b threeplus2k_2[of _ _ "(rs ! 0, Stay)"] threeplus2k_3[of _ _ "(rs ! 0, Stay)"]
        by (cases) simp_all
    next
      case c
      consider "j = 2" | "3 \<le> j \<and> j < k + 3" | "3 + k \<le> j \<and> j < 2 * k + 3"
        using assms by linarith
      then show ?thesis
        using cmdL8_def c threeplus2k_2[of _ _ "(rs ! 0, Stay)"] threeplus2k_3[of _ _ "(rs ! 0, Stay)"]
        by (cases) simp_all
    next
      case d
      consider "j = 2" | "3 \<le> j \<and> j < k + 3" | "3 + k \<le> j \<and> j < 2 * k + 3"
        using assms by linarith
      then show ?thesis
        using cmdL8_def d threeplus2k_2[of _ _ "(rs ! 0, Stay)"] threeplus2k_3[of _ _ "(rs ! 0, Stay)"]
        by (cases) simp_all
    qed
  qed
  then have "immobile (tmL78 jj) j (2 * k + 3)" if "jj < k" for jj
    by (auto simp add: that tmL78_def)
  then have "immobile (tmL48 jj) j (2 * k + 3)" if "jj < k" for jj
    using tmL48_def immobile_sequential[OF tmL47_tm tmL78_tm] L47 assms that by simp
  then have L49: "immobile (tmL49 jj) j (2 * k + 3)" if "jj < k" for jj
    using tmL49_def immobile_sequential[OF tmL48_tm] tm_left_until1_tm immobile_tm_left_until assms that by simp

  have L49_upt: "immobile (tmL49_upt j') j (2 * k + 3)" if "j' \<le> k" for j'
    using that
  proof (induction j')
    case 0
    then show ?case
      by auto
  next
    case (Suc j')
    have "tmL49_upt (Suc j') = tmL49_upt j' ;; tmL49 j'"
      by simp
    moreover have "turing_machine (2*k+3) G' (tmL49_upt j')"
      using tmL49_upt_tm Suc by simp
    moreover have "immobile (tmL49_upt j') j (2*k+3)"
      using Suc by simp
    moreover have "turing_machine (2*k+3) G' (tmL49 j')"
      using tmL49_tm Suc by simp
    moreover have "immobile (tmL49 j') j (2*k+3)"
      using L49 Suc by simp
    ultimately show ?case
      using immobile_sequential by simp
  qed
  then have "immobile tmL9 j (2 * k + 3)"
    using tmL9_def immobile_sequential[OF tmL4_tm tmL49_upt_tm] L4 by simp
  then have L10: "immobile tmL10 j (2 * k + 3)"
    using tmL10_def immobile_sequential[OF tmL9_tm tmC_tm] C by simp

  have "cmdL11 rs [~] j = Stay" if "length rs = 2 * k + 3" and "jj < k" for rs jj
  proof -
    consider "j = 2" | "3 \<le> j \<and> j < 3 + k" | "3 + k \<le> j \<and> j < 2 * k + 3"
      using assms by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        by (simp add: cmdL11_def)
    next
      case 2
      then show ?thesis
        using cmdL11_def threeplus2k_2[where ?a="(rs ! 0, Stay)"] by simp
    next
      case 3
      then show ?thesis
        using cmdL11_def threeplus2k_3[where ?a="(rs ! 0, Stay)"] by simp
    qed
  qed
  then have "immobile [cmdL11] j (2 * k + 3)"
    using k_ge_2 assms by force
  then have "immobile tmL11 j (2 * k + 3)"
    using tmL11_def immobile_sequential[OF tmL10_tm tmL1011_tm] L10 by simp
  then have "immobile tmL12 j (2 * k + 3)"
    using tmL12_def immobile_sequential[OF tmL11_tm tm_left_until1_tm] immobile_tm_left_until assms by simp
  then have "immobile tmL13 j (2 * k + 3)"
    using tmL13_def immobile_sequential[OF tmL12_tm tm_write_many_tm] immobile_tm_write_many
      assms k_ge_2 G'_ge(1)
    by simp
  then have "immobile tmLoop j (2 * k + 3)"
    using tmLoop_def C immobile_loop[OF tmC_tm tmL13_tm] assms(2) by simp
  then have "immobile tm10 j (2 * k + 3)"
    using tm10_def immobile_sequential[OF tm9_tm tmLoop_tm] 9 by simp
  then have "immobile tm11 j (2 * k + 3)"
    using tm11_def immobile_sequential[OF tm10_tm tm_ltrans_until_tm] ec1 G'_ge immobile_tm_ltrans_until assms
    by simp
  then show "immobile tm12 j (2 * k + 3)"
    using tm12_def immobile_sequential[OF tm11_tm tm_rtrans_tm] ec1 G'_ge immobile_tm_rtrans assms by simp
qed

definition "tps12'' zs \<equiv>
  [(\<lfloor>zs\<rfloor>, length zs + 1),
   (exec zs (Suc (fmt (length zs))) <:> 1, 1)]"

lemma tps12'':
  assumes "bit_symbols zs"
  shows "tps12'' zs = take 2 (tps12' zs)"
  using tps12'_def tps12''_def assms by simp

text \<open>
This is the actual simulator Turing machine we are constructing in this section.
It is @{const tm12} stripped of all memorization tapes:
\<close>

definition "tmO2T \<equiv> icartesian (2 * k + 1) tm12 G'"

lemma tmO2T_tm: "turing_machine 2 G' tmO2T"
  unfolding tmO2T_def
  using immobile_tm12 tm12_tm icartesian_tm[of "2 * k + 1" G']
  by (metis (no_types, lifting) One_nat_def Suc_le_lessD add.assoc add_less_mono1 le_add2
    numeral_3_eq_3 one_add_one plus_1_eq_Suc)

text \<open>
The constructed two-tape Turing machine computes the same output as the original
Turing machine.
\<close>

lemma tmO2T:
  assumes "bit_symbols zs"
  shows "traces tmO2T (snd (start_config 2 zs)) (es12 zs) (tps12'' zs)"
proof -
  have *: "2 * k + 1 + 2 = 2 * k + 3"
    by simp
  then have "turing_machine (2 * k + 1 + 2) G' tm12"
    using tm12_tm by metis
  moreover have "\<And>j. j < 2 * k + 1 \<Longrightarrow> immobile tm12 (j + 2) (2 * k + 1 + 2)"
    using immobile_tm12 immobile_def by simp
  moreover have "\<forall>i<length zs. zs ! i < G'"
    using assms G'_ge_G zs_less_G by (meson order_less_le_trans)
  moreover have "traces tm12 (snd (start_config (2 * k + 1 + 2) zs)) (es12 zs) (tps12' zs)"
    using tm12' tps0_start_config assms * by (metis (no_types, lifting) prod.sel(2))
  ultimately show ?thesis
    using icartesian[of "2 * k + 1" G' tm12 zs "es12 zs" "tps12' zs"] tmO2T_def tps12'' assms by simp
qed


subsection \<open>Time complexity\<close>

text \<open>
This is the bound for the running time of @{const tmO2T}:
\<close>

definition TTT :: "nat \<Rightarrow> nat" where
  "TTT \<equiv> \<lambda>n. length (es_fmt n) + 43 * k * Suc (fmt n) * Suc (fmt n)"

lemma execute_tmO2T:
  assumes "bit_symbols zs"
  shows "execute tmO2T (start_config 2 zs) (TTT (length zs)) = (length tmO2T, tps12'' zs)"
proof -
  have "trace tmO2T (start_config 2 zs) (es12 zs) (length tmO2T, tps12'' zs)"
    using tmO2T assms traces_def start_config_def by simp
  then have "execute tmO2T (start_config 2 zs) (length (es12 zs)) = (length tmO2T, tps12'' zs)"
    using trace_def by simp
  moreover have "length (es12 zs) \<le> TTT (length zs)"
    using assms length_es12 TTT_def by simp
  ultimately show ?thesis
    by (metis execute_after_halting_ge fst_conv)
qed

text \<open>
The simulator TM @{const tmO2T} halts with the output tape head on cell~1.
\<close>

lemma execute_tmO2T_1:
  assumes "bit_symbols zs"
  shows "execute tmO2T (start_config 2 zs) (TTT (length zs)) <!> 1 =
    (execute M (start_config k zs) (T (length zs)) <:> 1, 1)"
proof -
  have "T (length zs) \<le> Suc (fmt (length zs))"
    by (metis add_leD1 le_Suc_eq fmt(4) T'_def)
  then have *: "execute M (start_config k zs) (T (length zs)) =
      execute M (start_config k zs) (Suc (fmt (length zs)))"
    using execute_after_halting_ge time_bound_T time_bound_def assms by (metis (no_types, lifting))

  have "execute tmO2T (start_config 2 zs) (TTT (length zs)) = (length tmO2T, tps12'' zs)"
    using assms execute_tmO2T by simp
  then have "execute tmO2T (start_config 2 zs) (TTT (length zs)) <!> 1 =
      (execute M (start_config k zs) (Suc (fmt (length zs))) <:> 1, 1)"
    using tps12''_def exec_def assms by simp
  then show ?thesis
    using * by simp
qed

lemma poly_TTT: "big_oh_poly TTT"
proof -
  have 1: "big_oh_poly (\<lambda>n. length (es_fmt n))"
    using fmt(2) by simp
  have "big_oh_poly (\<lambda>n. fmt n + 1)"
    using fmt(3) big_oh_poly_const big_oh_poly_sum by blast
  then have "big_oh_poly (\<lambda>n. Suc (fmt n))"
    by simp
  then have "big_oh_poly (\<lambda>n. Suc (fmt n) * Suc (fmt n))"
    using big_oh_poly_prod by blast
  moreover have "big_oh_poly (\<lambda>n. 43 * k)"
    using big_oh_poly_const by simp
  ultimately have "big_oh_poly (\<lambda>n. 43 * k * (Suc (fmt n) * Suc (fmt n)))"
    using big_oh_poly_prod by blast
  moreover have "(\<lambda>n. 43 * k * (Suc (fmt n) * Suc (fmt n))) = (\<lambda>n. 43 * k * Suc (fmt n) * Suc (fmt n))"
    by (metis (mono_tags, opaque_lifting) mult.assoc)
  ultimately have "big_oh_poly (\<lambda>n. 43 * k * Suc (fmt n) * Suc (fmt n))"
    by simp
  then have "big_oh_poly (\<lambda>n. length (es_fmt n) + 43 * k * Suc (fmt n) * Suc (fmt n))"
    using 1 big_oh_poly_sum by simp
  then show ?thesis
    unfolding TTT_def by simp
qed


subsection \<open>Obliviousness\<close>

text \<open>
The two-tape simulator machine is oblivious.
\<close>

lemma tmO2T_oblivious:
  assumes "length zs1 = length zs2" and "bit_symbols zs1" and "bit_symbols zs2"
  shows "es12 zs1 = es12 zs2"
proof -
  have "es1 zs1 = es1 zs2"
    using es1_def assms by simp

  moreover have "es1_2 zs1 = es1_2 zs2"
    using es1_2_def assms by (metis (no_types, lifting))
  ultimately have "es2 zs1 = es2 zs2"
    using es2_def assms by simp
  then have "es3 zs1 = es3 zs2"
    using es3_def assms by simp
  then have "es4 zs1 = es4 zs2"
    using es4_def assms by simp
  then have "es5 zs1 = es5 zs2"
    using es5_def assms by simp
  then have "es6 zs1 = es6 zs2"
    using es6_def assms by simp
  then have "es7 zs1 = es7 zs2"
    using es7_def assms by simp
  then have "es8 zs1 = es8 zs2"
    using es8_def assms by simp
  then have 9: "es9 zs1 = es9 zs2"
    using es9_def assms by simp

  have C: "esC zs1 t = esC zs2 t" for t
    using esC_def assms by simp
  then have Loop_break: "esLoop_break zs1 = esLoop_break zs2"
    using esLoop_break_def tpsC1_def tpsL_def assms by simp

  have "esL1 zs1 = esL1 zs2"
    using esL1_def assms by auto
  moreover have "esL1_2 zs1 = esL1_2 zs2"
    using esL1_2_def assms by simp
  ultimately have "esL2 zs1 = esL2 zs2"
    using esL2_def assms by auto
  then have "esL3 zs1 = esL3 zs2"
    using esL3_def assms by auto
  then have L4: "esL4 zs1 = esL4 zs2"
    using esL4_def assms by auto

  have "esL45 zs1 = esL45 zs2"
    using esL45_def assms by simp
  then have "esL46 zs1 = esL46 zs2"
    using esL46_def assms by simp
  moreover have "esL67 zs1 = esL67 zs2"
    using esL67_def assms by simp
  ultimately have "esL47 zs1 = esL47 zs2"
    using esL47_def assms by simp
  moreover have "esL78 zs1 = esL78 zs2"
    using esL78_def assms by simp
  ultimately have "esL48 zs1 = esL48 zs2"
    using esL48_def assms by simp
  then have "esL49 zs1 = esL49 zs2"
    using esL49_def assms by simp
  then have "esL49_upt zs1 = esL49_upt zs2"
    using esL49_upt_def assms by simp
  then have "esL9 zs1 = esL9 zs2"
    using esL9_def L4 assms by auto
  then have "esL10 zs1 = esL10 zs2"
    using esL10_def C assms by auto
  then have "esL11 zs1 = esL11 zs2"
    using esL11_def assms by auto
  then have "esL12 zs1 = esL12 zs2"
    using esL12_def assms by auto
  then have "esL13 zs1 = esL13 zs2"
    using esL13_def assms by auto
  then have "esLoop_while zs1 = esLoop_while zs2"
    using esLoop_while_def C tpsC1_def tpsL13_def tpsL_def assms by auto
  then have "esLoop zs1 = esLoop zs2"
    using esLoop_def Loop_break assms by auto
  then have "es10 zs1 = es10 zs2"
    using es10_def 9 assms by auto
  then have "es11 zs1 = es11 zs2"
    using es11_def assms by simp
  then show "es12 zs1 = es12 zs2"
    using es12_def assms by simp
qed

end  (* locale two_tape *)


section \<open>$\NP$ and obliviousness\label{s:oblivious-np}\<close>

text \<open>
This section presents the main result of this chapter: For every language $L \in
\NP$ there is a polynomial-time two-tape oblivious verifier TM that halts with
the output tape head on a \textbf{1} symbol iff.\ in the input $\langle x,
u\rangle$, the string $u$ is a certificate for $x$. The proof combines two
lemmas. First @{thm [source] NP_output_len_1}, which says that we can assume the
verifier outputs only one symbol (namely, \textbf{0} or \textbf{1}), and second
@{thm [source] two_tape.execute_tmO2T_1}, which says that the two-tape oblivious
TM halts with output tape head in cell~1. This cell will contain either
\textbf{0} or \textbf{1} by the first lemma.
\<close>

lemma NP_imp_oblivious_2tape:
  fixes L :: language
  assumes "L \<in> \<N>\<P>"
  obtains M G T p where
    "big_oh_poly T" and
    "polynomial p" and
    "turing_machine 2 G M" and
    "oblivious M" and
    "\<And>y. bit_symbols y \<Longrightarrow> fst (execute M (start_config 2 y) (T (length y))) = length M" and
    "\<And>x. x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> execute M (start_config 2 \<langle>x; u\<rangle>) (T (length \<langle>x; u\<rangle>)) <.> 1 = \<one>)"
proof -
  define Q where "Q = (\<lambda>L k G M p T fverify.
    turing_machine k G M \<and>
    polynomial p \<and>
    big_oh_poly T \<and>
    computes_in_time k M fverify T \<and>
    (\<forall>y. length (fverify y) = 1) \<and>
    (\<forall>x. (x \<in> L) = (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])))"
  have "\<N>\<P> = {L :: language. \<exists>k G M p T fverify. Q L k G M p T fverify}"
    unfolding NP_output_len_1 Q_def by simp
  then obtain k G M p T fverify where "Q L k G M p T fverify"
    using assms by blast
  then have alt:
    "turing_machine k G M"
    "polynomial p"
    "big_oh_poly T"
    "computes_in_time k M fverify T"
    "\<And>y. length (fverify y) = 1"
    "\<And>x. (x \<in> L) = (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])"
    using Q_def by simp_all

  have tm_M: "turing_machine k G M"
    using alt(1) .
  have poly_T: "big_oh_poly T"
    using alt(3) .
  have time_bound_T: "time_bound M k T"
    unfolding time_bound_def
  proof standard+
    fix zs
    assume zs: "bit_symbols zs"
    define x where "x = symbols_to_string zs"
    then have "zs = string_to_symbols x"
      using bit_symbols_to_symbols zs by simp
    then show "fst (execute M (start_config k zs) (T (length zs))) = length M"
      using computes_in_time_def alt(4)
      by (metis (no_types, lifting) execute_after_halting_ge length_map running_timeD(1))
  qed

  interpret two: two_tape M k G T
    using tm_M poly_T time_bound_T two_tape_def by simp

  let ?M = two.tmO2T
  let ?T = two.TTT
  let ?G = two.G'
  have "big_oh_poly ?T"
    using two.poly_TTT .
  moreover have "polynomial p"
    using alt(2) .
  moreover have "turing_machine 2 ?G ?M"
    using two.tmO2T_tm .
  moreover have "oblivious ?M"
  proof -
    let ?e = "\<lambda>n. two.es12 (replicate n 2)"
    have "\<exists>tps. trace ?M (start_config 2 zs) (?e (length zs)) (length ?M, tps)"
        if "bit_symbols zs" for zs
    proof -
      have "traces ?M (snd (start_config 2 zs)) (two.es12 zs) (two.tps12'' zs)"
        using that two.tmO2T by simp
      then have *: "trace ?M (start_config 2 zs) (two.es12 zs) (length ?M, two.tps12'' zs)"
        using start_config_def traces_def by simp

      let ?r = "replicate (length zs) 2"
      have "length zs = length ?r"
        by simp
      then have "two.es12 zs = two.es12 ?r"
        using two.tmO2T_oblivious that by (metis nth_replicate)
      then have "trace ?M (start_config 2 zs) (?e (length zs)) (length ?M, two.tps12'' zs)"
        using * by simp
      then show ?thesis
        by auto
    qed
    then show ?thesis
      using oblivious_def by fast
  qed
  moreover have "fst (execute ?M (start_config 2 y) (?T (length y))) = length ?M" if "bit_symbols y" for y
    using that two.execute_tmO2T by simp
  moreover have "x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> execute ?M (start_config 2 \<langle>x; u\<rangle>) (?T (length \<langle>x; u\<rangle>)) <.> 1 = \<one>)"
    (is "?lhs = ?rhs") for x
  proof
    show "?lhs \<Longrightarrow> ?rhs"
    proof -
      assume ?lhs
      then have "\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]"
        using alt(6) by simp
      then obtain u where u: "length u = p (length x)" "fverify \<langle>x, u\<rangle> = [\<bbbI>]"
        by auto

      let ?y = "fverify \<langle>x, u\<rangle>"
      let ?cfg = "execute M (start_config k \<langle>x; u\<rangle>) (T (length \<langle>x, u\<rangle>))"
      have "computes_in_time k M fverify T"
        using alt(4) by simp
      then have cfg: "?cfg <:> 1 = string_to_contents ?y"
        using computes_in_time_execute by simp

      have "bit_symbols \<langle>x; u\<rangle>"
        by simp
      then have "execute ?M (start_config 2 \<langle>x; u\<rangle>) (?T (length \<langle>x; u\<rangle>)) <!> 1 =
          (execute M (start_config k \<langle>x; u\<rangle>) (T (length \<langle>x; u\<rangle>)) <:> 1, 1)"
        using two.execute_tmO2T_1 by blast
      then have "execute ?M (start_config 2 \<langle>x; u\<rangle>) (?T (length \<langle>x; u\<rangle>)) <!> 1 =
          (string_to_contents ?y, 1)"
         using cfg by simp
      then have "execute ?M (start_config 2 \<langle>x; u\<rangle>) (?T (length \<langle>x; u\<rangle>)) <!> 1 =
          (string_to_contents [\<bbbI>], 1)"
        using u(2) by auto
      moreover have "|.| (string_to_contents [\<bbbI>], 1) = \<one>"
        by simp
      ultimately have "execute ?M (start_config 2 \<langle>x; u\<rangle>) (?T (length \<langle>x; u\<rangle>)) <.> 1 = \<one>"
        by simp
      then show ?thesis
        using u(1) by auto
    qed
    show "?rhs \<Longrightarrow> ?lhs"
    proof -
      assume ?rhs
      then obtain u where u:
        "length u = p (length x)"
        "execute ?M (start_config 2 \<langle>x; u\<rangle>) (?T (length \<langle>x; u\<rangle>)) <.> 1 = \<one>"
        by auto
      let ?zs = "\<langle>x; u\<rangle>"
      have "bit_symbols \<langle>x; u\<rangle>"
        by simp
      then have *: "execute ?M (start_config 2 ?zs) (?T (length ?zs)) <!> 1 =
          (execute M (start_config k ?zs) (T (length ?zs)) <:> 1, 1)"
        using two.execute_tmO2T_1 by blast

      let ?y = "fverify \<langle>x, u\<rangle>"
      let ?cfg = "execute M (start_config k ?zs) (T (length \<langle>x, u\<rangle>))"
      have "computes_in_time k M fverify T"
        using alt(4) by simp
      then have cfg: "?cfg <:> 1 = string_to_contents ?y"
        using computes_in_time_execute by simp
      then have "execute ?M (start_config 2 ?zs) (?T (length ?zs)) <!> 1 =
          (string_to_contents (fverify \<langle>x, u\<rangle>), 1)"
        using * by simp
      then have "execute ?M (start_config 2 ?zs) (?T (length ?zs)) <.> 1 =
          string_to_contents (fverify \<langle>x, u\<rangle>) 1"
        by simp
      then have **: "string_to_contents (fverify \<langle>x, u\<rangle>) 1 = \<one>"
        using u(2) by simp

      have "length (fverify \<langle>x, u\<rangle>) = 1"
        using alt(5) by simp
      then have "string_to_contents (fverify \<langle>x, u\<rangle>) 1 =
          (if fverify \<langle>x, u\<rangle> ! 0 then \<one> else \<zero>)"
        by simp
      then have "(if fverify \<langle>x, u\<rangle> ! 0 then \<one> else \<zero>) = \<one>"
        using ** by auto
      then have "fverify \<langle>x, u\<rangle> ! 0 = \<bbbI>"
        by (metis numeral_eq_iff semiring_norm(89))
      moreover have "y = [\<bbbI>]" if "length y = 1" and "y ! 0" for y
        using that by (metis (full_types) One_nat_def Suc_length_conv length_0_conv nth_Cons')
      ultimately have "fverify \<langle>x, u\<rangle> = [\<bbbI>]"
        using alt(5) by simp
      then show ?lhs
        using u(1) alt(6) by auto
    qed
  qed
  ultimately show ?thesis
    using that by simp
qed

end