chapter \<open>Time complexity\label{s:TC}\<close>

theory NP
  imports Elementary Composing Symbol_Ops
begin

text \<open>
In order to formulate the Cook-Levin theorem we need to formalize \SAT{} and
$\NP$-completeness. This chapter is devoted to the latter and hence introduces
the complexity class $\NP$ and the concept of polynomial-time many-one
reduction. Moreover, although not required for the Cook-Levin theorem, it
introduces the class $\mathcal{P}$ and contains a proof of $\mathcal{P}
\subseteq \NP$ (see Section~\ref{s:TC-subseteq}). The chapter concludes with
some easy results about $\mathcal{P}$, $\NP$ and reducibility in
Section~\ref{s:TC-more}.
\<close>


section \<open>The time complexity classes DTIME, $\mathcal{P}$, and $\NP$\label{s:TC-NP}\<close>

text \<open>
Arora and Barak~\cite[Definitions 1.12, 1.13]{ccama} define
$\mathrm{DTIME}(T(n))$ as the set of all languages that can be decided in time
$c \cdot T(n)$ for some $c > 0$ and $\mathcal{P} =
\bigcup_{c\geq1}\mathrm{DTIME}(n^c)$. However since $0^c = 0$ for $c\geq 1$,
this means that for a language $L$ to be in $\mathcal{P}$, the Turing machine
deciding $L$ must check the empty string in zero steps. For a Turing machine to
halt in zero steps, it must start in the halting state, which limits its
usefulness. Because of this technical issue we define $\mathrm{DTIME}(T(n))$ as
the set of all languages that can be decided with a running time in $O(T(n))$,
which seems a common enough alternative~\cite{lv-aikc,sipser2006,cz-dtime}.
\<close>

text \<open>
Languages are sets of strings, and deciding a language means computing its
characteristic function.
\<close>

type_synonym language = "string set"

definition characteristic :: "language \<Rightarrow> (string \<Rightarrow> string)" where
  "characteristic L \<equiv> (\<lambda>x. [x \<in> L])"

definition DTIME :: "(nat \<Rightarrow> nat) \<Rightarrow> language set" where
  "DTIME T \<equiv> {L. \<exists>k G M T'.
    turing_machine k G M \<and>
    big_oh T' T \<and>
    computes_in_time k M (characteristic L) T'}"

definition complexity_class_P :: "language set" ("\<P>") where
  "\<P> \<equiv> \<Union>c\<in>{1..}. DTIME (\<lambda>n. n ^ c)"

text \<open>
A language $L$ is in $\NP$ if there is a polynomial $p$ and a polynomial-time
Turing machine, called the \emph{verifier}, such that for all strings
$x\in\bbOI^*$,
\[
  x\in L \longleftrightarrow
    \exists u\in\bbOI^{p(|x|)}: M(\langle x, u\rangle) = \bbbI.
\]
The string $u$ does not seem to have a name in general, but in case the verifier
outputs $\bbbI$ on input $\langle x, u\rangle$ it is called a
\emph{certificate} for $x$~\cite[Definition~2.1]{ccama}.
\<close>

definition complexity_class_NP :: "language set" ("\<N>\<P>") where
  "\<N>\<P> \<equiv> {L. \<exists>k G M p T fverify.
    turing_machine k G M \<and>
    polynomial p \<and>
    big_oh_poly T \<and>
    computes_in_time k M fverify T \<and>
    (\<forall>x. x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]))}"

text \<open>
The definition of $\NP$ is the one place where we need an actual polynomial
function, namely $p$, rather than a function that is merely bounded by a
polynomial. This raises the question as to the definition of a polynomial
function. Arora and Barak~\cite{ccama} do not seem to give a definition in the
context of $\NP$ but explicitly state that polynomial functions are mappings
$\nat \to \nat$.  Presumably they also have the form $f(n) = \sum_{i=0}^d
a_i\cdot n^i$, as polynomials do.  We have filled in the gap in this definition
in Section~\ref{s:tm-basic-bigoh} by letting the coefficients $a_i$ be natural
numbers.

Regardless of whether this is the meaning intended by Arora and Barak, the
choice is justified because with it the verifier-based definition of $\NP$ is
equivalent to the original definition via nondeterministic Turing machines
(NTMs). In the usual equivalence proof (for example, Arora and
Barak~\cite[Theorem~2.6]{ccama}) a verifier TM and an NTM are constructed.

For the one direction, if a language is decided by a polynomial-time NTM then a
verifier TM can be constructed that simulates the NTM on input $x$ by using the
bits in the string $u$ for the nondeterministic choices. The strings $u$ have
the length $p(|x|)$. So for this construction to work, there must be a polynomial
$p$ that bounds the running time of the NTM. Clearly, a polynomial function with
natural coefficients exists with that property.

For the other direction, assume a language has a verifier TM where $p$ is a
polynomial function with natural coefficients. An NTM deciding this language
receives $x$ as input, then ``guesses'' a string $u$ of length $p(|x|)$, and
then runs the verifier on the pair $\langle x, u\rangle$. For this NTM to run in
polynomial time, $p$ must be computable in time polynomial in $|x|$. We have
shown this to be the case in lemma @{thm [source] transforms_tm_polynomialI} in
Section~\ref{s:tm-arithmetic-poly}.
\<close>

text \<open>
A language $L_1$ is polynomial-time many-one reducible to a language $L_2$ if
there is a polynomial-time computable function $f_\mathit{reduce}$ such that for all
$x$, $x\in L_1$ iff.\ $f_\mathit{reduce}(x) \in L_2$.
\<close>

definition reducible (infix "\<le>\<^sub>p" 50) where
  "L\<^sub>1 \<le>\<^sub>p L\<^sub>2 \<equiv> \<exists>k G M T freduce.
    turing_machine k G M \<and>
    big_oh_poly T \<and>
    computes_in_time k M freduce T \<and>
    (\<forall>x. x \<in> L\<^sub>1 \<longleftrightarrow> freduce x \<in> L\<^sub>2)"

abbreviation NP_hard :: "language \<Rightarrow> bool" where
  "NP_hard L \<equiv> \<forall>L'\<in>\<N>\<P>. L' \<le>\<^sub>p L"

definition NP_complete :: "language \<Rightarrow> bool" where
  "NP_complete L \<equiv> L \<in> \<N>\<P> \<and> NP_hard L"

text \<open>
Requiring $c \geq 1$ in the definition of $\mathcal{P}$ is not essential:
\<close>

lemma in_P_iff: "L \<in> \<P> \<longleftrightarrow> (\<exists>c. L \<in> DTIME (\<lambda>n. n ^ c))"
proof
  assume "L \<in> \<P>"
  then show "\<exists>c. L \<in> DTIME (\<lambda>n. n ^ c)"
    unfolding complexity_class_P_def using Suc_le_eq by auto
next
  assume "\<exists>c. L \<in> DTIME (\<lambda>n. n ^ c)"
  then obtain c where "L \<in> DTIME (\<lambda>n. n ^ c)"
    by auto
  then obtain k G M T where M:
    "turing_machine k G M"
    "big_oh T (\<lambda>n. n ^ c)"
    "computes_in_time k M (characteristic L) T"
    using DTIME_def by auto
  moreover have "big_oh T (\<lambda>n. n ^ Suc c)"
  proof -
    obtain c0 n0 :: nat where c0n0: "\<forall>n>n0. T n \<le> c0 * n ^ c"
      using M(2) big_oh_def by auto
    have "\<forall>n>n0. T n \<le> c0 * n ^ Suc c"
    proof standard+
      fix n assume "n0 < n"
      then have "n ^ c \<le> n ^ Suc c"
        using pow_mono by simp
      then show "T n \<le> c0 * n ^ Suc c"
        using c0n0 by (metis \<open>n0 < n\<close> add.commute le_Suc_ex mult_le_mono2 trans_le_add2)
    qed
    then show ?thesis
      using big_oh_def by auto
  qed
  ultimately have "\<exists>c>0. L \<in> DTIME (\<lambda>n. n ^ c)"
    using DTIME_def by blast
  then show "L \<in> \<P>"
    unfolding complexity_class_P_def by auto
qed


section \<open>Restricting verifiers to one-bit output\label{s:np-alt}\<close>

text \<open>
The verifier Turing machine in the definition of $\NP$ can output any symbol
sequence. In this section we restrict it to outputting only the symbol sequence
\textbf{1} or \textbf{0}. This is equivalent to the definition because it is
easy to check if a symbol sequence differs from \textbf{1} and if so change it
to \textbf{0}, as we show below.

The advantage of this restriction is that if we can make the TM halt with the
output tape head on cell number~1, the output tape symbol read in the final step
equals the output of the TM. We will exploit this in Chapter~\ref{s:Reducing},
where we show how to reduce any language $L\in\NP$ to \SAT{}.

The next Turing machine checks if the symbol sequence on tape $j$ differs from
the one-symbol sequence \textbf{1} and if so turns it into \textbf{0}. It thus
ensures that the tape contains only one bit symbol.

\null
\<close>

definition tm_make_bit :: "tapeidx \<Rightarrow> machine" where
  "tm_make_bit j \<equiv>
    tm_cr j ;;
    IF \<lambda>rs. rs ! j = \<one> THEN
      tm_right j ;;
      IF \<lambda>rs. rs ! j = \<box> THEN
        []
      ELSE
        tm_set j [\<zero>]
      ENDIF
    ELSE
      tm_set j [\<zero>]
    ENDIF"

lemma tm_make_bit_tm:
  assumes "G \<ge> 4" and "0 < j" and "j < k"
  shows "turing_machine k G (tm_make_bit j)"
  unfolding tm_make_bit_def
  using assms tm_right_tm tm_set_tm tm_cr_tm Nil_tm turing_machine_branch_turing_machine
  by simp

locale turing_machine_make_bit =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_cr j"
definition "tmT1 \<equiv> tm_right j"
definition "tmT12 \<equiv> IF \<lambda>rs. rs ! j = \<box> THEN [] ELSE tm_set j [\<zero>] ENDIF"
definition "tmT2 \<equiv> tmT1 ;; tmT12"
definition "tm12 \<equiv> IF \<lambda>rs. rs ! j = \<one> THEN tmT2 ELSE tm_set j [\<zero>] ENDIF"
definition "tm2 \<equiv> tm1 ;; tm12"

lemma tm2_eq_tm_make_bit: "tm2 \<equiv> tm_make_bit j"
  unfolding tm_make_bit_def tm2_def tm12_def tmT2_def tmT12_def tmT1_def tm1_def by simp

context
  fixes tps0 :: "tape list" and zs :: "symbol list"
  assumes jk: "j < length tps0"
    and zs: "proper_symbols zs"
  assumes tps0: "tps0 ::: j = \<lfloor>zs\<rfloor>"
begin

lemma clean: "clean_tape (tps0 ! j)"
  using zs tps0 contents_clean_tape' by simp

definition "tps1 \<equiv> tps0[j := (\<lfloor>zs\<rfloor>, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = tps0 :#: j + 2"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def by (tform tps: assms jk clean tps0 tps1_def)

definition "tpsT1 \<equiv> tps0[j := (\<lfloor>zs\<rfloor>, 2)]"

lemma tmT1 [transforms_intros]:
  assumes "ttt = 1"
  shows "transforms tmT1 tps1 ttt tpsT1"
  unfolding tmT1_def
proof (tform tps: assms tps1_def jk)
  show "tpsT1 = tps1[j := tps1 ! j |+| 1] "
    using tps1_def tpsT1_def jk
    by (metis Suc_1 fst_conv list_update_overwrite nth_list_update_eq plus_1_eq_Suc snd_conv)
qed

definition "tpsT2 \<equiv> tps0
  [j := if length zs \<le> 1 then (\<lfloor>zs\<rfloor>, 2) else (\<lfloor>[\<zero>]\<rfloor>, 1)]"

lemma tmT12 [transforms_intros]:
  assumes "ttt = 14 + 2 * length zs"
  shows "transforms tmT12 tpsT1 ttt tpsT2"
  unfolding tmT12_def
proof (tform tps: assms tpsT1_def tps0 jk zs)
  show "8 + tpsT1 :#: j + 2 * length zs + Suc (2 * length [\<zero>]) + 1 \<le> ttt"
    using tpsT1_def jk assms by simp
  have "read tpsT1 ! j = \<lfloor>zs\<rfloor> 2"
    using tpsT1_def jk tapes_at_read' by (metis fst_conv length_list_update nth_list_update_eq snd_conv)
  moreover have "\<lfloor>zs\<rfloor> 2 = \<box> \<longleftrightarrow> length zs \<le> 1"
    using zs contents_def
    by (metis Suc_1 diff_Suc_1 less_imp_le_nat linorder_le_less_linear not_less_eq_eq zero_neq_numeral)
  ultimately have "read tpsT1 ! j = \<box> \<longleftrightarrow> length zs \<le> 1"
    by simp
  then show
      "read tpsT1 ! j \<noteq> \<box> \<Longrightarrow> tpsT2 = tpsT1[j := (\<lfloor>[\<zero>]\<rfloor>, 1)]"
      "read tpsT1 ! j = \<box> \<Longrightarrow> tpsT2 = tpsT1"
    using tpsT1_def tpsT2_def jk by simp_all
qed

lemma tmT2 [transforms_intros]:
  assumes "ttt = 15 + 2 * length zs"
  shows "transforms tmT2 tps1 ttt tpsT2"
  unfolding tmT2_def by (tform time: assms)

definition "tps2 \<equiv> tps0
  [j := if zs = [\<one>] then (\<lfloor>zs\<rfloor>, 2) else (\<lfloor>[\<zero>]\<rfloor>, 1)]"

lemma tm12 [transforms_intros]:
  assumes "ttt = 17 + 2 * length zs"
  shows "transforms tm12 tps1 ttt tps2"
  unfolding tm12_def
proof (tform tps: assms tps0 jk zs tps1_def)
  have "read tps1 ! j = \<lfloor>zs\<rfloor> 1"
    using tps1_def jk tapes_at_read' by (metis fst_conv length_list_update nth_list_update_eq snd_conv)
  then have *: "read tps1 ! j = \<one> \<longleftrightarrow> \<lfloor>zs\<rfloor> 1 = \<one>"
    by simp
  show "read tps1 ! j \<noteq> \<one> \<Longrightarrow> tps2 = tps1[j := (\<lfloor>[\<zero>]\<rfloor>, 1)]"
    using * tps2_def tps1_def by auto
  show "tps2 = tpsT2" if "read tps1 ! j = \<one>"
  proof (cases "zs = [\<one>]")
    case True
    then show ?thesis
      using * tps2_def tpsT2_def by simp
  next
    case False
    then have "\<lfloor>zs\<rfloor> 1 = \<one>"
      using * that by simp
    then have "length zs > 1"
      using False contents_def contents_outofbounds
      by (metis One_nat_def Suc_length_conv diff_Suc_1 length_0_conv linorder_neqE_nat nth_Cons_0 zero_neq_numeral)
    then show ?thesis
      using * tps2_def tpsT2_def by auto
  qed
  show "8 + tps1 :#: j + 2 * length zs + Suc (2 * length [\<zero>]) + 1 \<le> ttt"
    using tps1_def jk assms by simp
qed

lemma tm2:
  assumes "ttt = 19 + 2 * length zs + tps0 :#: j"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: assms tps0 jk zs tps1_def)

end

end  (* locale *)

lemma transforms_tm_make_bitI [transforms_intros]:
  fixes j :: tapeidx 
  fixes tps tps' :: "tape list" and zs :: "symbol list" and ttt :: nat
  assumes "j < length tps" and "proper_symbols zs"
  assumes "tps ::: j = \<lfloor>zs\<rfloor>"
  assumes "ttt = 19 + 2 * length zs + tps :#: j"
  assumes "tps' = tps
    [j := if zs = [\<one>] then (\<lfloor>zs\<rfloor>, 2) else (\<lfloor>[\<zero>]\<rfloor>, 1)]"
  shows "transforms (tm_make_bit j) tps ttt tps'"
proof -
  interpret loc: turing_machine_make_bit j .
  show ?thesis
    using assms loc.tps2_def loc.tm2 loc.tm2_eq_tm_make_bit by simp
qed

lemma output_length_le_time:
  assumes "turing_machine k G M"
    and "tps ::: 1 = \<lfloor>zs\<rfloor>"
    and "proper_symbols zs"
    and "transforms M (snd (start_config k xs)) t tps"
  shows "length zs \<le> t"
proof -
  have 1: "execute M (start_config k xs) t = (length M, tps)"
    using assms transforms_def transits_def
    by (metis (no_types, lifting) execute_after_halting_ge fst_conv start_config_def sndI)
  moreover have "k > 1"
    using assms(1) turing_machine_def by simp
  ultimately have "((execute M (start_config k xs) t) <:> 1) i = \<box>" if "i > t" for i
    using assms blank_after_time that by (meson zero_less_one)
  then have "(tps ::: 1) i = \<box>" if "i > t" for i
    using 1 that by simp
  then have *: "\<lfloor>zs\<rfloor> i = \<box>" if "i > t" for i
    using assms(2) that by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> length zs \<le> t"
    then have "length zs > t"
      by simp
    then have "\<lfloor>zs\<rfloor> (Suc t) \<noteq> \<box>"
      using contents_inbounds assms(3) contents_def proper_symbols_ne0 by simp
    then show False
      using * by simp
  qed
qed

text \<open>
This is the alternative definition of $\NP$, which restricts the verifier
to output only strings of length one:
\<close>

lemma NP_output_len_1:
  "\<N>\<P> = {L. \<exists>k G M p T fverify.
    turing_machine k G M \<and>
    polynomial p \<and>
    big_oh_poly T \<and>
    computes_in_time k M fverify T \<and>
    (\<forall>y. length (fverify y) = 1) \<and>
    (\<forall>x. x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]))}"
  (is "_ = ?M")
proof
  show "?M \<subseteq> \<N>\<P>"
    using complexity_class_NP_def by fast
  define Q where "Q = (\<lambda>L k G M p T fverify.
    turing_machine k G M \<and>
    polynomial p \<and>
    big_oh_poly T \<and>
    computes_in_time k M fverify T \<and>
    (\<forall>x. (x \<in> L) = (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])))"
  have alt: "complexity_class_NP = {L::language. \<exists>k G M p T fverify. Q L k G M p T fverify}"
    unfolding complexity_class_NP_def Q_def by simp
  show "\<N>\<P> \<subseteq> ?M"
  proof
    fix L assume "L \<in> \<N>\<P>"
    then obtain k G M p T fverify where "Q L k G M p T fverify"
      using alt by blast
    then have ex:
      "turing_machine k G M \<and>
       polynomial p \<and>
       big_oh_poly T \<and>
       computes_in_time k M fverify T \<and>
       (\<forall>x. (x \<in> L) = (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]))"
      using Q_def by simp

    have "k \<ge> 2" and "G \<ge> 4"
      using ex turing_machine_def by simp_all

    define M' where "M' = M ;; tm_make_bit 1"
    define f' where "f' = (\<lambda>y. if fverify y = [\<bbbI>] then [\<bbbI>] else [\<bbbO>])"
    define T' where "T' = (\<lambda>n. 19 + 4 * T n)"

    have "turing_machine k G M'"
      unfolding M'_def using \<open>2 \<le> k\<close> \<open>4 \<le> G\<close> ex tm_make_bit_tm by simp
    moreover have "polynomial p"
      using ex by simp
    moreover have "big_oh_poly T'"
      using T'_def ex big_oh_poly_const big_oh_poly_prod big_oh_poly_sum by simp
    moreover have "computes_in_time k M' f' T'"
    proof
      fix y
      let ?cfg = "start_config k (string_to_symbols y)"
      obtain tps where
        1: "tps ::: 1 = string_to_contents (fverify y)" and
        2: "transforms M (snd ?cfg) (T (length y)) tps"
        using ex computes_in_timeD by blast
      have len_tps: "length tps \<ge> 2"
        by (smt (z3) "2" \<open>2 \<le> k\<close> ex execute_num_tapes start_config_length less_le_trans numeral_2_eq_2
          prod.sel(2) transforms_def transits_def zero_less_Suc)
      define zs where "zs = string_to_symbols (fverify y)"
      then have zs: "tps ::: 1 = \<lfloor>zs\<rfloor>" "proper_symbols zs"
        using 1 by auto
      have transforms_MI [transforms_intros]: "transforms M (snd ?cfg) (T (length y)) tps"
        using 2 by simp
      define tps' where
        "tps' = tps[1 := if zs = [\<one>] then (\<lfloor>zs\<rfloor>, 2) else (\<lfloor>[\<zero>]\<rfloor>, 1)]"

      have "transforms M' (snd ?cfg) (T (length y) + (19 + (tps :#: Suc 0 + 2 * length zs))) tps'"
        unfolding M'_def by (tform tps: zs len_tps tps'_def)
      moreover have "T (length y) + (19 + (tps :#: Suc 0 + 2 * length zs)) \<le> T' (length y)"
      proof -
        have "tps :#: Suc 0 \<le> T (length y)"
          using 2 transforms_def transits_def start_config_def ex head_pos_le_time `2 \<le> k`
          by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_le_lessD leD linorder_le_less_linear
            order_less_le_trans prod.sel(2))
        moreover have "length zs \<le> T (length y)"
          using zs 2 ex output_length_le_time by auto
        ultimately show ?thesis
          using T'_def 1 2 by simp
      qed
      ultimately have *: "transforms M' (snd ?cfg) (T' (length y)) tps'"
        using transforms_monotone by simp

      have "tps' ::: 1 = (if zs = [\<one>] then tps ::: 1 else \<lfloor>[\<zero>]\<rfloor>)"
        using tps'_def len_tps zs(1) by simp
      also have "... = (if zs = [\<one>] then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[\<zero>]\<rfloor>)"
        using zs(1) by simp
      also have "... = (if string_to_symbols (fverify y) = [3] then \<lfloor>[3]\<rfloor> else \<lfloor>[2]\<rfloor>)"
        using zs_def by simp
      also have "... = (if fverify y = [\<bbbI>] then \<lfloor>[\<one>]\<rfloor> else \<lfloor>[\<zero>]\<rfloor>)"
        by auto
      also have "... = (if fverify y = [\<bbbI>] then string_to_contents [\<bbbI>] else string_to_contents [\<bbbO>])"
        by auto
      also have "... = string_to_contents (if fverify y = [\<bbbI>] then [\<bbbI>] else [\<bbbO>])"
        by simp
      also have "... = string_to_contents (f' y)"
        using f'_def by auto
      finally have "tps' ::: 1 = string_to_contents (f' y)" .

      then show "\<exists>tps'. tps' ::: 1 = string_to_contents (f' y) \<and>
          transforms M' (snd ?cfg) (T' (length y)) tps'"
        using * by auto
    qed
    moreover have "\<forall>y. length (f' y) = 1"
      using f'_def by simp
    moreover have "(\<forall>x. x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> f' \<langle>x, u\<rangle> = [\<bbbI>]))"
      using ex f'_def by auto
    ultimately show "L \<in> ?M"
      by blast
  qed
qed



section \<open>$\mathcal{P}$ is a subset of $\NP$\label{s:TC-subseteq}\<close>

text \<open>
Let $L\in\mathcal{P}$ be a language and $M$ a Turing machine that decides $L$ in
polynomial time. To show $L\in\NP$ we could use a TM that extracts the first
element from the input $\langle x, u\rangle$ and runs $M$ on $x$. We do not have
to construct such a TM explicitly because we have shown that the extraction of
the first pair element is computable in polynomial time (lemma~@{thm [source]
tm_first_computes}), and by assumption the characteristic function of $L$ is
computable in polynomial time, too.  The composition of these two functions is
the verifier function required by the definition of $\NP$. And by lemma~@{thm
[source] computes_composed_poly} the composition of polynomial-time functions is
polynomial-time, too.

\null
\<close>

theorem P_subseteq_NP: "\<P> \<subseteq> \<N>\<P>"
proof
  fix L :: language
  assume "L \<in> \<P>"
  then obtain c where c: "L \<in> DTIME (\<lambda>n. n ^ c)"
    using complexity_class_P_def by auto
  then obtain k G M T' where M:
    "turing_machine k G M"
    "computes_in_time k M (characteristic L) T'"
    "big_oh T' (\<lambda>n. n ^ c)"
    using DTIME_def by auto
  then have 4: "big_oh_poly T'"
    using big_oh_poly_def by auto

  define f where "f = (\<lambda>x. symbols_to_string (first (bindecode (string_to_symbols x))))"
  define T :: "nat \<Rightarrow> nat" where "T = (\<lambda>n. 9 + 4 * n)"
  have 1: "turing_machine 3 6 tm_first"
    by (simp add: tm_first_tm)
  have 2: "computes_in_time 3 tm_first f T"
    using f_def T_def tm_first_computes by simp
  have 3: "big_oh_poly T"
  proof -
    have "big_oh_poly (\<lambda>n. 9)"
      using big_oh_poly_const by simp
    moreover have "big_oh_poly (\<lambda>n. 4 * n)"
      using big_oh_poly_const big_oh_poly_prod big_oh_poly_poly[of 1] by simp
    ultimately show ?thesis
      using big_oh_poly_sum T_def by simp
  qed

  define fverify where "fverify = characteristic L \<circ> f"
  then have *: "\<exists>T k G M. big_oh_poly T \<and> turing_machine k G M \<and> computes_in_time k M fverify T"
    using M 1 2 3 4 computes_composed_poly by simp

  then have fverify: "fverify \<langle>x, u\<rangle> = [x \<in> L]" for x u
    using f_def first_pair symbols_to_string_to_symbols fverify_def characteristic_def
    by simp

  define p :: "nat \<Rightarrow> nat" where "p = (\<lambda>_. 0)"
  then have "polynomial p"
    using const_polynomial by simp
  moreover have "\<forall>x. x \<in> L \<longleftrightarrow> (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])"
    using fverify p_def by simp
  ultimately show "L \<in> \<N>\<P>"
    using * complexity_class_NP_def by fast
qed


section \<open>More about $\mathcal{P}$, $\NP$, and reducibility\label{s:TC-more}\<close>

text \<open>
We prove some low-hanging fruits about the concepts introduced in this chapter.
None of the results are needed to show the Cook-Levin theorem.
\<close>

text \<open>
A language can be reduced to itself by the identity function. Hence reducibility
is a reflexive relation.

\null
\<close>

lemma reducible_refl: "L \<le>\<^sub>p L"
proof -
  let ?M = "tm_id"
  let ?T = "\<lambda>n. Suc (Suc n)"
  have "turing_machine 2 4 ?M"
    using tm_id_tm by simp
  moreover have "big_oh_poly ?T"
  proof -
    have "big_oh_poly (\<lambda>n. n + 2)"
      using big_oh_poly_const big_oh_poly_id big_oh_poly_sum by blast
    then show ?thesis
      by simp
  qed
  moreover have "computes_in_time 2 ?M id ?T"
    using computes_id by simp
  moreover have "\<forall>x. x \<in> L \<longleftrightarrow> id x \<in> L"
    by simp
  ultimately show "L \<le>\<^sub>p L"
    using reducible_def by metis
qed

text \<open>
Reducibility is also transitive. If $L_1 \leq_p L_2$ by a TM $M_1$ and $L_2
\leq_p L_3$ by a TM $M_2$ we merely have to run $M_2$ on the output of $M_1$ to
show that $L_1 \leq_p L_3$. Again this is merely the composition of two
polynomial-time computable functions.
\<close>

lemma reducible_trans:
  assumes "L\<^sub>1 \<le>\<^sub>p L\<^sub>2" and "L\<^sub>2 \<le>\<^sub>p L\<^sub>3"
  shows "L\<^sub>1 \<le>\<^sub>p L\<^sub>3"
proof -
  obtain k1 G1 M1 T1 f1 where 1:
     "turing_machine k1 G1 M1 \<and>
      big_oh_poly T1 \<and>
      computes_in_time k1 M1 f1 T1 \<and>
      (\<forall>x. x \<in> L\<^sub>1 \<longleftrightarrow> f1 x \<in> L\<^sub>2)"
    using assms(1) reducible_def by metis
  moreover obtain k2 G2 M2 T2 f2 where 2:
     "turing_machine k2 G2 M2 \<and>
      big_oh_poly T2 \<and>
      computes_in_time k2 M2 f2 T2 \<and>
      (\<forall>x. x \<in> L\<^sub>2 \<longleftrightarrow> f2 x \<in> L\<^sub>3)"
    using assms(2) reducible_def by metis
  ultimately obtain T k G M where
      "big_oh_poly T \<and> turing_machine k G M \<and> computes_in_time k M (f2 \<circ> f1) T"
    using computes_composed_poly by metis
  moreover have "\<forall>x. x \<in> L\<^sub>1 \<longleftrightarrow> f2 (f1 x) \<in> L\<^sub>3"
    using 1 2 by simp
  ultimately show ?thesis
    using reducible_def by fastforce
qed

text \<open>
The usual way to show that a language is $\NP$-hard is to reduce another $\NP$-hard
language to it.
\<close>

lemma ex_reducible_imp_NP_hard:
  assumes "NP_hard L'" and "L' \<le>\<^sub>p L"
  shows "NP_hard L"
  using reducible_trans assms by auto

text \<open>
The converse is also true because reducibility is a reflexive relation.
\<close>

lemma NP_hard_iff_reducible: "NP_hard L \<longleftrightarrow> (\<exists>L'. NP_hard L' \<and> L' \<le>\<^sub>p L)"
proof
  show "NP_hard L \<Longrightarrow> \<exists>L'. NP_hard L' \<and> L' \<le>\<^sub>p L"
    using reducible_refl by auto
  show "\<exists>L'. NP_hard L' \<and> L' \<le>\<^sub>p L \<Longrightarrow> NP_hard L"
    using ex_reducible_imp_NP_hard by blast
qed

lemma NP_complete_reducible:
  assumes "NP_complete L'" and "L \<in> \<N>\<P>" and "L' \<le>\<^sub>p L"
  shows "NP_complete L"
  using assms NP_complete_def reducible_trans by blast

text \<open>
In a sense the complexity class $\mathcal{P}$ is closed under reduction.
\<close>

lemma P_closed_reduction:
  assumes "L \<in> \<P>" and "L' \<le>\<^sub>p L"
  shows "L' \<in> \<P>"
proof -
  obtain c where c: "L \<in> DTIME (\<lambda>n. n ^ c)"
    using assms(1) complexity_class_P_def by auto
  then obtain k G M T where M:
    "turing_machine k G M"
    "computes_in_time k M (characteristic L) T"
    "big_oh T (\<lambda>n. n ^ c)"
    using DTIME_def by auto
  then have T: "big_oh_poly T"
    using big_oh_poly_def by auto

  obtain k' G' M' T' freduce where M':
    "turing_machine k' G' M'"
    "big_oh_poly T'"
    "computes_in_time k' M' freduce T'"
    "(\<forall>x. x \<in> L' \<longleftrightarrow> freduce x \<in> L)"
    using reducible_def assms(2) by auto

  obtain T2 k2 G2 M2 where M2:
    "big_oh_poly T2"
    "turing_machine k2 G2 M2"
    "computes_in_time k2 M2 (characteristic L \<circ> freduce) T2"
    using M T M' computes_composed_poly by metis

  obtain d where d: "big_oh T2 (\<lambda>n. n ^ d)"
    using big_oh_poly_def M2(1) by auto

  have "characteristic L \<circ> freduce = characteristic L'"
    using characteristic_def M'(4) by auto
  then have "\<exists>k G M T'. turing_machine k G M \<and> big_oh T' (\<lambda>n. n ^ d) \<and> computes_in_time k M (characteristic L') T'"
    using M2 d by auto
  then have "L' \<in> DTIME (\<lambda>n. n ^ d)"
    using DTIME_def by simp
  then show ?thesis
    using in_P_iff by auto
qed

text \<open>
The next lemmas are items~2 and~3 of Theorem~2.8 of the textbook~\cite{ccama}.
Item~1 is the transitivity of the reduction, already proved in lemma @{thm
[source] reducible_trans}.
\<close>

lemma P_eq_NP:
  assumes "NP_hard L" and "L \<in> \<P>"
  shows "\<P> = \<N>\<P>"
  using assms P_closed_reduction P_subseteq_NP by auto

lemma NP_complete_imp:
  assumes "NP_complete L"
  shows "L \<in> \<P> \<longleftrightarrow> \<P> = \<N>\<P>"
  using assms NP_complete_def P_eq_NP by auto

end
