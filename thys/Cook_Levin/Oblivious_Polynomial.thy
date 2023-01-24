section \<open>Constructing polynomials in polynomial time\label{s:oblivious-polynomial}\<close>

theory Oblivious_Polynomial
  imports Oblivious
begin

text \<open>
Our current goal is to simulate a polynomial time multi-tape TM on a two-tape
oblivious TM in polynomial time. To help with the obliviousness we first want to
mark on the simulator's output tape a space that is at least as large as the
space the simulated TM uses on any of its tapes but that still is only
polynomial in size. In this section we construct oblivious Turing machines for
that.

An upper bound for the size this space is provided by the simulated TM's running
time, which by assumption is polynomially bounded. So for our purposes any
polynomially bounded function that bounds the running time will do.

In this section we devise a family of two-tape oblivious TMs that contains for
every polynomial degree $d \ge 1$ a TM that writes $\mathbf{1}^{p(n)}$ to the
output tape for some polynomial $p$ with $p(n) \ge n^d$, where $n$ is the length
of the input to the TM. Together with a TM that appends a constant number $c$ of
ones we get a family of TMs, parameterized by $c$ and $d$, that runs in
polynomial time and writes more than $c + n^d$ symbols~\textbf{1} to the work
tape.

This meets our goal for this section because every polynomially bounded
function is bounded by a function of the form $n \mapsto c + n^d$ for some
$c, d\in\nat$.

The TMs in the family are built from three building block TMs. The first TM
initializes its output tape with $\mathbf{1}^n$ where $n$ is the length of the
input. The second TM multiplies the number of symbols on the output tape by
(roughly) the length of the input, turning a sequence $\mathbf{1}^m$ into
(roughly) $\mathbf{1}^{mn}$ for arbitrary $m$. The third TM appends
$\mathbf{1}^c$ for some constant $c$. By repeating the second TM we can achieve
arbitrarily high polynomial degrees.

All three TMs do essentially only one thing with the input, namely copying it to
the output tape while mapping all symbols to \textbf{1}, which is an operation
that depends only on the length of the input. Therefore all three TMs are
oblivious, and combining them also yields an oblivious TM.

The Turing machines require one extra symbol beyond the four default symbols,
but work for all alphabet sizes $G \ge 5$.

\null
\<close>

locale turing_machine_poly =
  fixes G :: nat
  assumes G: "G \<ge> 5"
begin

lemma G_ge4 [simp]: "G \<ge> 4"
  using G by linarith

abbreviation tps_ones :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tps_ones zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>i. if i = 0 then \<triangleright> else if i \<le> m then \<one> else \<box>, 1)]"


subsection \<open>Initializing the output tape\<close>

text \<open>
The first building block is a TM that ``copies'' the input to the output tape,
thereby replacing every symbol by the symbol \textbf{1}.
\<close>

definition tmA :: machine where
  "tmA \<equiv>
    tm_right 0 ;; tm_right 1 ;; tm_const_until 0 1 {\<box>} \<one> ;; tm_cr 0 ;; tm_cr 1"

lemma tmA_tm: "turing_machine 2 G tmA"
  unfolding tmA_def using tm_right_tm tm_const_until_tm tm_cr_tm G by simp

definition "tm1 \<equiv> tm_right 0"
definition "tm2 \<equiv> tm1 ;; tm_right 1"
definition "tm3 \<equiv> tm2 ;; tm_const_until 0 1 {\<box>} \<one>"
definition "tm4 \<equiv> tm3 ;; tm_cr 0"
definition "tm5 \<equiv> tm4 ;; tm_cr 1"

lemma tm5_eq_tmA: "tm5 = tmA"
  unfolding tmA_def tm5_def tm4_def tm3_def tm2_def tm1_def by simp

definition tps0 :: "symbol list \<Rightarrow> tape list" where
  "tps0 zs \<equiv>
    [(\<lfloor>zs\<rfloor>, 0),
     (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)]"

lemma length_tps0 [simp]: "length (tps0 n) = 2"
  unfolding tps0_def by simp

definition tps1 :: "symbol list \<Rightarrow> tape list" where
  "tps1 zs \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)]"

definition es1 :: "(nat \<times> nat) list" where
  "es1 \<equiv> [(1, 0)]"

lemma tm1: "traces tm1 (tps0 zs) es1 (tps1 zs)"
  unfolding tm1_def
  by (rule traces_tm_right_0I) (simp_all add: tps0_def tps1_def es1_def)

definition tps2 :: "symbol list \<Rightarrow> tape list" where
  "tps2 zs \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 1)]"

definition es2 :: "(nat \<times> nat) list" where
  "es2 \<equiv> es1 @ [(1, 1)]"

lemma length_es2: "length es2 = 2"
  unfolding es1_def es2_def by simp

lemma tm2: "traces tm2 (tps0 zs) es2 (tps2 zs)"
  unfolding tm2_def es2_def
proof (rule traces_sequential[OF tm1])
  show "traces (tm_right 1) (tps1 zs) [(1, 1)] (tps2 zs)"
    using tps1_def tps2_def by (intro traces_tm_right_1I) simp_all
qed

definition tps3 :: "symbol list \<Rightarrow> tape list" where
  "tps3 zs \<equiv>
    [(\<lfloor>zs\<rfloor>, length zs + 1),
     (\<lambda>i. if i = 0 then \<triangleright> else if i \<le> length zs then \<one> else \<box>, length zs + 1)]"

definition es23 :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "es23 n \<equiv> map (\<lambda>i. (i + 2, i + 2)) [0..<n] @ [(n + 1, n + 1)]"

definition es3 :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "es3 n \<equiv> es2 @ (es23 n)"

lemma length_es3: "length (es3 n) = n + 3"
  unfolding es3_def es23_def using length_es2 by simp

lemma tm3:
  assumes "proper_symbols zs"
  shows "traces tm3 (tps0 zs) (es3 (length zs)) (tps3 zs)"
  unfolding tm3_def es3_def
proof (rule traces_sequential[OF tm2])
  show "traces (tm_const_until 0 1 {\<box>} \<one>) (tps2 zs) (es23 (length zs)) (tps3 zs)"
  proof (rule traces_tm_const_until_01I)
    show "1 < length (tps2 zs)"
      using tps2_def by simp
    show "rneigh (tps2 zs ! 0) {\<box>} (length zs)"
      using rneigh_def contents_def tps2_def assms by auto
    show "es23 (length zs) =
        map (\<lambda>i. (tps2 zs :#: 0 + Suc i, tps2 zs :#: 1 + Suc i))
        [0..<length zs] @
        [(tps2 zs :#: 0 + length zs, tps2 zs :#: 1 + length zs)]"
      unfolding es23_def using tps2_def by simp
    show "tps3 zs = (tps2 zs)
        [0 := tps2 zs ! 0 |+| length zs,
         1 := constplant (tps2 zs ! 1) \<one> (length zs)]"
      using tps3_def tps2_def constplant by auto
  qed
qed

definition tps4 :: "symbol list \<Rightarrow> tape list" where
  "tps4 zs \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>i. if i = 0 then \<triangleright> else if i \<le> length zs then \<one> else \<box>, length zs + 1)]"

definition es34 :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "es34 n \<equiv> map (\<lambda>i. (i, n + 1)) (rev [0..<n + 1]) @ [(0, n + 1)] @ [(1, n + 1)]"

definition es4 :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "es4 n \<equiv> es3 n @ es34 n"

lemma length_es4: "length (es4 n) = 2 * n + 6"
  unfolding es4_def es34_def using length_es3 by simp

lemma tm4:
  assumes "proper_symbols zs"
  shows "traces tm4 (tps0 zs) (es4 (length zs)) (tps4 zs)"
  unfolding tm4_def es4_def
proof (rule traces_sequential[OF tm3])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_cr 0) (tps3 zs) (es34 (length zs)) (tps4 zs)"
  proof (rule traces_tm_cr_0I)
    show "1 < length (tps3 zs)"
      using tps3_def by simp
    show "clean_tape (tps3 zs ! 0)"
     using assms tps3_def by simp
    show "es34 (length zs) =
        map (\<lambda>i. (i, tps3 zs :#: 1)) (rev [0..<tps3 zs :#: 0]) @
        [(0, tps3 zs :#: 1), (1, tps3 zs :#: 1)]"
      using tps3_def es34_def by simp
    show "tps4 zs = (tps3 zs)[0 := tps3 zs ! 0 |#=| 1]"
      using tps3_def tps4_def by simp
  qed
qed

definition tps5 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tps5 zs m \<equiv> tps_ones zs m"

definition es45 :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "es45 n \<equiv> map (\<lambda>i. (1, i)) (rev [0..<n + 1]) @ [(1, 0)] @ [(1, 1)]"

definition es5 :: "nat \<Rightarrow> (nat \<times> nat) list" where
  "es5 n \<equiv> es4 n @ es45 n"

lemma length_es5: "length (es5 n) = 3 * n + 9"
  unfolding es5_def es45_def using length_es4 by simp

lemma tm5:
  assumes "proper_symbols zs"
  shows "traces tm5 (tps0 zs) (es5 (length zs)) (tps5 zs (length zs))"
  unfolding tm5_def es5_def
proof (rule traces_sequential[OF tm4])
  show "proper_symbols zs"
   using assms .
  show "traces (tm_cr 1) (tps4 zs) (es45 (length zs)) (tps5 zs (length zs))"
  proof (rule traces_tm_cr_1I)
    show "1 < length (tps4 zs)"
      using tps4_def by simp
    show "clean_tape (tps4 zs ! 1)"
      using tps4_def clean_tape_def by simp
    show "es45 (length zs) =
        map (Pair (tps4 zs :#: 0)) (rev [0..<tps4 zs :#: 1]) @
        [(tps4 zs :#: 0, 0), (tps4 zs :#: 0, 1)]"
      using tps4_def by (simp add: es45_def)
    show "tps5 zs (length zs) = (tps4 zs)[1 := tps4 zs ! 1 |#=| 1]"
      using tps4_def tps5_def by simp
  qed
qed

corollary tmA:
  assumes "proper_symbols zs"
  shows "traces tmA (tps0 zs) (es5 (length zs)) (tps_ones zs (length zs))"
  using tps5_def tm5_eq_tmA tm5 assms by simp

lemma length_tps_ones [simp]: "length (tps_ones zs m) = 2"
  by simp


subsection \<open>Multiplying by the input length\<close>

text \<open>
The next Turing machine turns a symbol sequence $\mathbf{1}^m$ on its output tape
into $\mathbf{1}^{m+1+mn}$ where $n$ is the length of the input.

The TM first appends to the output tape symbols a @{text "\<bar>"} symbol. Then it
performs a loop with $m$ iterations. In each iteration it replaces a @{text \<one>}
before the @{text "\<bar>"} by @{text \<zero>} in order to count the iterations. Then it
copies (replacing each symbol by @{text \<one>}) the input after the output tape
symbols. After the loop the output tape contains $\mathbf{0}^m|\mathbf{1}^{mn}$.
Finally the @{text "\<bar>"} and @{text \<zero>} symbols are replaced by @{text \<one>}
symbols, yielding the desired result.
\<close>

definition tmB :: machine where
  "tmB \<equiv>
    tm_right_until 1 {\<box>} ;;
    tm_write 1 \<bar> ;;
    tm_cr 1 ;;
    WHILE tm_right_until 1 {\<one>, \<bar>} ; \<lambda>rs. rs ! 1 = \<one> DO
       tm_write 1 \<zero> ;;
       tm_right_until 1 {0} ;;
       tm_const_until 0 1 {\<box>} \<one> ;;
       tm_cr 0 ;;
       tm_cr 1
    DONE ;;
    tm_write 1 \<one> ;;
    tm_cr 1 ;;
    tm_const_until 1 1 {\<one>} \<one> ;;
    tm_cr 1"

lemma tmB_tm: "turing_machine 2 G tmB"
  unfolding tmB_def
  using tm_right_until_tm tm_write_tm tm_cr_tm tm_const_until_tm G
    turing_machine_loop_turing_machine turing_machine_sequential_turing_machine
  by simp

definition "tmB1 \<equiv> tm_right_until 1 {\<box>}"
definition "tmB2 \<equiv> tmB1 ;; tm_write 1 \<bar>"
definition "tmB3 \<equiv> tmB2 ;; tm_cr 1"
definition "tmK1 \<equiv> tm_right_until 1 {\<one>, \<bar>}"
definition "tmL1 \<equiv> tm_write 1 \<zero>"
definition "tmL2 \<equiv> tmL1 ;; tm_right_until 1 {\<box>}"
definition "tmL3 \<equiv> tmL2 ;; tm_const_until 0 1 {\<box>} \<one>"
definition "tmL4 \<equiv> tmL3 ;; tm_cr 0"
definition "tmL5 \<equiv> tmL4 ;; tm_cr 1"
definition "tmLoop \<equiv> WHILE tmK1 ; \<lambda>rs. rs ! 1 = \<one> DO tmL5 DONE"
definition "tmB4 \<equiv> tmB3 ;; tmLoop"
definition "tmB5 \<equiv> tmB4 ;; tm_write 1 \<one>"
definition "tmB6 \<equiv> tmB5 ;; tm_cr 1"
definition "tmB7 \<equiv> tmB6 ;; tm_const_until 1 1 {\<one>} \<one>"
definition "tmB8 \<equiv> tmB7 ;; tm_cr 1"

lemma tmB_eq_tmB8: "tmB = tmB8"
  unfolding tmB_def tmB1_def tmB2_def tmB3_def tmK1_def tmL1_def tmL2_def tmL3_def
    tmL4_def tmL5_def tmLoop_def tmB4_def tmB5_def tmB6_def tmB7_def tmB8_def
  by simp

definition tpsB1 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsB1 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>i. if i = 0 then \<triangleright> else if i \<le> m then \<one> else \<box>, m + 1)]"

definition esB1 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB1 n m \<equiv> map (\<lambda>i. (1, 1 + Suc i)) [0..<m] @ [(1, 1 + m)]"

lemma length_esB1: "length (esB1 n m) = m + 1"
  using esB1_def by (metis Suc_eq_plus1 length_append_singleton length_map length_upt minus_nat.diff_0)

lemma tmB1:
  assumes "proper_symbols zs"
  shows "traces tmB1 (tps_ones zs m) (esB1 (length zs) m) (tpsB1 zs m)"
  unfolding tmB1_def
proof (rule traces_tm_right_until_1I[where ?n=m])
  show "1 < length (tps_ones zs m)"
    by simp
  show "rneigh (tps_ones zs m ! 1) {0} m"
    using rneighI by simp
  show "esB1 (length zs) m =
      map (\<lambda>i. (tps_ones zs m :#: 0, tps_ones zs m :#: 1 + Suc i)) [0..<m] @
      [(tps_ones zs m :#: 0, tps_ones zs m :#: 1 + m)]"
    by (simp add: esB1_def)
  show "tpsB1 zs m = (tps_ones zs m)[1 := tps_ones zs m ! 1 |+| m]"
    using tpsB1_def by simp
qed

definition tpsB2 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsB2 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>i. if i = 0 then \<triangleright> else if i \<le> m then \<one> else if i = m + 1 then \<bar> else \<box>, m + 1)]"

definition esB12 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB12 n m \<equiv> [(1, m + 1)]"

definition esB2 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB2 n m \<equiv> esB1 n m @ esB12 n m"

lemma length_esB2: "length (esB2 n m) = m + 2"
  by (simp add: esB12_def esB2_def length_esB1)

lemma tmB2:
  assumes "proper_symbols zs"
  shows "traces tmB2 (tps_ones zs m) (esB2 (length zs) m) (tpsB2 zs m)"
  unfolding tmB2_def esB2_def
proof (rule traces_sequential[OF tmB1])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_write 1 \<bar>) (tpsB1 zs m) (esB12 (length zs) m) (tpsB2 zs m)"
  proof (rule traces_tm_write_1I)
    show "1 < length (tpsB1 zs m)"
      using tpsB1_def by simp_all
    show "esB12 (length zs) m = [(tpsB1 zs m :#: 0, tpsB1 zs m :#: 1)]"
      using tpsB1_def by (simp add: esB12_def)
    show "tpsB2 zs m = (tpsB1 zs m)[1 := tpsB1 zs m ! 1 |:=| \<bar>]"
      using tpsB2_def tpsB1_def by auto
  qed
qed

definition tpsB3 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsB3 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>i. if i = 0 then \<triangleright> else if i \<le> m then \<one> else if i = m + 1 then \<bar> else 0, 1)]"

definition esB23 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB23 n m \<equiv> map (Pair 1) (rev [0..<m + 1]) @ [(1, 0), (1, 1)]"

definition esB3 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB3 n m \<equiv> esB2 n m @ esB23 n m"

lemma length_esB3: "length (esB3 n m) = 2 * m + 5"
  by (simp add: esB3_def length_esB2 esB23_def)

lemma tmB3:
  assumes "proper_symbols zs"
  shows "traces tmB3 (tps_ones zs m) (esB3 (length zs) m) (tpsB3 zs m)"
  unfolding tmB3_def esB3_def
proof (rule traces_sequential[OF tmB2])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_cr 1) (tpsB2 zs m) (esB23 (length zs) m) (tpsB3 zs m)"
  proof (rule traces_tm_cr_1I)
    show "1 < length (tpsB2 zs m)"
      using tpsB2_def by simp
    show "clean_tape (tpsB2 zs m ! 1)"
      using tpsB2_def clean_tape_def by simp
    show "esB23 (length zs) m =
        map (Pair (tpsB2 zs m :#: 0)) (rev [0..<tpsB2 zs m :#: 1]) @
        [(tpsB2 zs m :#: 0, 0), (tpsB2 zs m :#: 0, 1)]"
      by (simp add: esB23_def tpsB2_def)
    show "tpsB3 zs m = (tpsB2 zs m)[1 := tpsB2 zs m ! 1 |#=| 1]"
      using tpsB2_def tpsB3_def by simp
  qed
qed

definition tpsK0 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsK0 zs m i \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> i then \<zero>
           else if x \<le> m then \<one>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + i * length zs then \<one>
           else 0,
      1)]"

lemma tpsK0_eq_tpsB3: "tpsK0 zs m 0 = tpsB3 zs m"
  using tpsK0_def tpsB3_def by auto

definition tpsK1 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
 "tpsK1 zs m i \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> i then \<zero>
           else if x \<le> m then \<one>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + i * length zs then \<one>
           else 0,
      i + 1)]"

definition esK1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esK1 n m i \<equiv> map (\<lambda>i. (1, 1 + Suc i)) [0..<i] @ [(1, i + 1)]"

lemma length_esK1: "length (esK1 n m i) = i + 1"
  by (simp add: esK1_def)

lemma tmK1:
  assumes "proper_symbols zs" and "i < m"
  shows "traces tmK1 (tpsK0 zs m i) (esK1 (length zs) m i) (tpsK1 zs m i)"
  unfolding tmK1_def
proof (rule traces_tm_right_until_1I[where ?n=i])
  show "1 < length (tpsK0 zs m i)"
    using tpsK0_def by simp
  show "rneigh (tpsK0 zs m i ! 1) {\<one>, \<bar>} i"
    using tpsK0_def rneigh_def assms(2) by simp
  show "esK1 (length zs) m i =
      map (\<lambda>j. (tpsK0 zs m i :#: 0, tpsK0 zs m i :#: 1 + Suc j)) [0..<i] @
      [(tpsK0 zs m i :#: 0, tpsK0 zs m i :#: 1 + i)]"
    by (simp add: esK1_def tpsK0_def)
  show "tpsK1 zs m i = (tpsK0 zs m i)[1 := tpsK0 zs m i ! 1 |+| i]"
    by (simp add: tpsK1_def tpsK0_def)
qed

definition tpsL1 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
 "tpsL1 zs m i \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> i + 1 then \<zero>
           else if x \<le> m then \<one>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + i * length zs then \<one>
           else 0,
      i + 1)]"

definition esL1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL1 n m i \<equiv> [(1, i + 1)]"

lemma tmL1:
  assumes "proper_symbols zs"
  shows "traces tmL1 (tpsK1 zs m i) (esL1 (length zs) m i) (tpsL1 zs m i)"
  unfolding tmL1_def using G
  by (intro traces_tm_write_1I) (auto simp add: tpsL1_def tpsK1_def esL1_def)

definition tpsL2 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsL2 zs m i \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> i + 1 then \<zero>
           else if x \<le> m then \<one>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + i * length zs then \<one>
           else 0,
      m + 2 + i * length zs)]"

definition esL12 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL12 n m i \<equiv>
    map (\<lambda>j. (1, i + 1 + Suc j)) [0..<m + 2 + i * n - (i + 1)] @
    [(1, i + 1 + (m + 2 + i * n - (i + 1)))]"

definition esL2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL2 n m i \<equiv> esL1 n m i @ esL12 n m i"

lemma length_esL2: "i < m \<Longrightarrow> length (esL2 n m i) = 3 + m - i + i * n"
  by (auto simp add: esL2_def esL12_def esL1_def)

text \<open>
A simplified upper bound for the running time:
\<close>

corollary length_esL2': "i < m \<Longrightarrow> length (esL2 n m i) \<le> 3 + m + i * n"
  by (simp add: length_esL2)

lemma tmL2:
  assumes "proper_symbols zs" and "i < m"
  shows "traces tmL2 (tpsK1 zs m i) (esL2 (length zs) m i) (tpsL2 zs m i)"
  unfolding tmL2_def esL2_def
proof (rule traces_sequential[OF tmL1])
  show "proper_symbols zs"
    using assms(1) .
  show "traces (tm_right_until 1 {0}) (tpsL1 zs m i) (esL12 (length zs) m i) (tpsL2 zs m i)"
  proof (rule traces_tm_right_until_1I)
    show "1 < length (tpsL1 zs m i)"
      using tpsL1_def by simp
    show "rneigh (tpsL1 zs m i ! 1) {0} (m + 2 + i * length zs - (i + 1))"
      using rneigh_def assms(2) by (auto simp add: tpsL1_def)
    show "esL12 (length zs) m i =
        map (\<lambda>j. (tpsL1 zs m i :#: 0, tpsL1 zs m i :#: 1 + Suc j))
        [0..<m + 2 + i * length zs - (i + 1)] @
        [(tpsL1 zs m i :#: 0,
          tpsL1 zs m i :#: 1 + (m + 2 + i * length zs - (i + 1)))]"
      using assms(2) by (simp add: tpsL1_def esL12_def)
    show "tpsL2 zs m i = (tpsL1 zs m i) [1 := tpsL1 zs m i ! 1 |+| m + 2 + i * length zs - (i + 1)]"
      using assms(2) by (simp add: tpsL1_def tpsL2_def)
  qed
qed

definition tpsL3 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsL3 zs m i \<equiv>
    [(\<lfloor>zs\<rfloor>, length zs + 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> i + 1 then \<zero>
           else if x \<le> m then \<one>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + (i + 1) * length zs then \<one>
           else 0,
      m + 2 + (i + 1) * length zs)]"

definition esL23 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL23 n m i \<equiv>
    map (\<lambda>j. (1 + Suc j, m + 2 + i * n + Suc j)) [0..<n] @ [(1 + n, m + 2 + i * n + n)]"

definition esL3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL3 n m i \<equiv> esL2 n m i @ esL23 n m i"

lemma length_esL3: "i < m \<Longrightarrow> length (esL3 n m i) \<le> 4 + m + (i + 1) * n"
  by (auto simp add: esL3_def esL23_def) (metis group_cancel.add1 length_esL2')

lemma tmL3:
  assumes "proper_symbols zs" and "i < m"
  shows "traces tmL3 (tpsK1 zs m i) (esL3 (length zs) m i) (tpsL3 zs m i)"
  unfolding tmL3_def esL3_def
proof (rule traces_sequential[OF tmL2])
  show "proper_symbols zs" and "i < m"
    using assms .
  show "traces (tm_const_until 0 1 {\<box>} \<one>) (tpsL2 zs m i) (esL23 (length zs) m i) (tpsL3 zs m i)"
  proof (rule traces_tm_const_until_01I)
    show "1 < length (tpsL2 zs m i)"
      using tpsL2_def by simp
    show "rneigh (tpsL2 zs m i ! 0) {0} (length zs)"
      using assms(1) rneigh_def contents_def by (auto simp add: tpsL2_def)
    show "esL23 (length zs) m i =
      map (\<lambda>j. (tpsL2 zs m i :#: 0 + Suc j, tpsL2 zs m i :#: 1 + Suc j)) [0..<length zs] @
      [(tpsL2 zs m i :#: 0 + length zs, tpsL2 zs m i :#: 1 + length zs)]"
      using assms by (simp add: esL23_def tpsL2_def)
    show "tpsL3 zs m i = (tpsL2 zs m i)
      [0 := tpsL2 zs m i ! 0 |+| length zs,
       1 := constplant (tpsL2 zs m i ! 1) \<one> (length zs)]"
      using constplant assms by (auto simp add: tpsL2_def tpsL3_def)
  qed
qed

definition tpsL4 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsL4 zs m i \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> i + 1 then \<zero>
           else if x \<le> m then \<one>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + (i + 1) * length zs then \<one>
           else 0,
      m + 2 + (i + 1) * length zs)]"

definition esL34 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL34 n m i \<equiv>
    map (\<lambda>j. (j, m + 2 + (i + 1) * n)) (rev [0..<n + 1]) @ [(0, m + 2 + (i + 1) * n), (1, m + 2 + (i + 1) * n)]"

lemma length_esL34: "i < m \<Longrightarrow> length (esL34 n m i) = n + 3"
  unfolding esL34_def by simp

definition esL4 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL4 n m i \<equiv> esL3 n m i @ esL34 n m i"

lemma length_esL4: "i < m \<Longrightarrow> length (esL4 n m i) \<le> 7 + m + (i + 2) * n"
  using length_esL3 length_esL34
  by (auto simp add: esL4_def) (metis ab_semigroup_add_class.add_ac(1) group_cancel.add2)

lemma tmL4:
  assumes "proper_symbols zs" and "i < m"
  shows "traces tmL4 (tpsK1 zs m i) (esL4 (length zs) m i) (tpsL4 zs m i)"
  unfolding tmL4_def esL4_def
proof (rule traces_sequential[OF tmL3])
  show "proper_symbols zs" "i < m"
    using assms .
  show "traces (tm_cr 0) (tpsL3 zs m i) (esL34 (length zs) m i) (tpsL4 zs m i)"
  proof (rule traces_tm_cr_0I)
    show "1 < length (tpsL3 zs m i)"
      using tpsL3_def by simp
    show "clean_tape (tpsL3 zs m i ! 0)"
      using tpsL3_def assms(1) by simp
    show "esL34 (length zs) m i =
        map (\<lambda>j. (j, tpsL3 zs m i :#: 1)) (rev [0..<tpsL3 zs m i :#: 0]) @
        [(0, tpsL3 zs m i :#: 1), (1, tpsL3 zs m i :#: 1)]"
      by (simp add: esL34_def tpsL3_def)
    show "tpsL4 zs m i = (tpsL3 zs m i)[0 := tpsL3 zs m i ! 0 |#=| 1]"
      by (simp add: tpsL4_def tpsL3_def)
  qed
qed

definition tpsL5 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsL5 zs m i \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> i + 1 then \<zero>
           else if x \<le> m then \<one>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + (i + 1) * length zs then \<one>
           else 0,
      1)]"

definition esL45 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL45 n m i \<equiv> map (Pair 1) (rev [0..<m + 2 + (i + 1) * n]) @ [(1, 0), (1, 1)]"

definition esL5 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esL5 n m i \<equiv> esL4 n m i @ esL45 n m i"

lemma length_esL5: "i < m \<Longrightarrow> length (esL5 n m i) \<le> 11 + 2 * m + (2 * i + 3) * n"
proof -
  assume a: "i < m"
  have "length (esL5 n m i) = length (esL4 n m i) + length (esL45 n m i)"
    using esL5_def by simp
  also have "... \<le> 7 + m + (i + 2) * n + length (esL45 n m i)"
    using length_esL4[OF a] by simp
  also have "... = 7 + m + (i + 2) * n + (m + 2 + (i + 1) * n + 2)"
    using esL45_def by simp
  also have "... = 11 + 2 * m + (2 * i + 3) * n"
    by algebra
  finally show ?thesis .
qed

lemma tmL5:
  assumes "proper_symbols zs" and "i < m"
  shows "traces tmL5 (tpsK1 zs m i) (esL5 (length zs) m i) (tpsL5 zs m i)"
  unfolding tmL5_def esL5_def
proof (rule traces_sequential[OF tmL4])
  show "proper_symbols zs" "i < m"
    using assms .
  show "traces (tm_cr 1) (tpsL4 zs m i) (esL45 (length zs) m i) (tpsL5 zs m i)"
  proof (rule traces_tm_cr_1I)
    show "1 < length (tpsL4 zs m i)"
      using tpsL4_def by simp
    show "clean_tape (tpsL4 zs m i ! 1)"
      using tpsL4_def assms clean_tapeI by simp
    show "esL45 (length zs) m i =
        map (Pair (tpsL4 zs m i :#: 0)) (rev [0..<tpsL4 zs m i :#: 1]) @
        [(tpsL4 zs m i :#: 0, 0), (tpsL4 zs m i :#: 0, 1)]"
      by (simp add: esL45_def tpsL4_def)
    show "tpsL5 zs m i = (tpsL4 zs m i)[1 := tpsL4 zs m i ! 1 |#=| 1]"
      by (simp add: tpsL4_def tpsL5_def)
  qed
qed

definition esLoop_do :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esLoop_do n m i \<equiv> esK1 n m i @ [(1, i + 1)] @ esL5 n m i @ [(1, 1)]"

text \<open>
Using $i < m$ we get this upper bound for the running time of an iteration
independent of $i$.
\<close>

lemma length_esLoop_do: "i < m \<Longrightarrow> length (esLoop_do n m i) \<le> 14 + 3 * m + (2 * m + 3) * n"
proof -
  assume "i < m"
  have "length (esLoop_do n m i) = length (esK1 n m i) + length (esL5 n m i) + 2"
    unfolding esLoop_do_def by simp
  also have "... = i + 3 + (length (esL5 n m i))"
    using length_esK1 by simp
  also have "... \<le> i + 14 + 2 * m + (2 * i + 3) * n"
    using length_esL5[OF `i < m`] by (simp add: add.assoc)
  also have "... \<le> 14 + 3 * m + (2 * i + 3) * n"
    using `i < m` by simp
  also have "... \<le> 14 + 3 * m + (2 * m + 3) * n"
    using `i < m` by simp
  finally show ?thesis .
qed

lemma tmLoop_do:
  assumes "proper_symbols zs" and "i < m"
  shows "trace tmLoop (0, tpsK0 zs m i) (esLoop_do (length zs) m i) (0, tpsL5 zs m i)"
  unfolding tmLoop_def
proof (rule tm_loop_sem_true_tracesI[OF tmK1 tmL5])
  show "proper_symbols zs" "proper_symbols zs" "i < m" "i < m"
    using assms by simp_all
  show "read (tpsK1 zs m i) ! 1 = \<one>"
    using tpsK1_def assms(2) read_def by simp
  show "esLoop_do (length zs) m i =
      esK1 (length zs) m i @
      [(tpsK1 zs m i :#: 0, tpsK1 zs m i :#: 1)] @
      esL5 (length zs) m i @ [(tpsL5 zs m i :#: 0, tpsL5 zs m i :#: 1)]"
    by (simp add: esLoop_do_def esK1_def tpsK1_def esL5_def tpsL5_def)
qed

lemma tpsL5_eq_tpsK0:
  assumes "proper_symbols zs" and "i < m"
  shows "tpsL5 zs m i = tpsK0 zs m (Suc i)"
  using assms tpsL5_def tpsK0_def by auto

lemma tmLoop_iteration:
  assumes "proper_symbols zs" and "i < m"
  shows "trace tmLoop (0, tpsK0 zs m i) (esLoop_do (length zs) m i) (0, tpsK0 zs m (Suc i))"
  using assms tmLoop_do tpsL5_eq_tpsK0 by simp

definition esLoop_done :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esLoop_done n m \<equiv> concat (map (esLoop_do n m) [0..<m])"

lemma tmLoop_done:
  assumes "proper_symbols zs"
  shows "trace tmLoop (0, tpsK0 zs m 0) (esLoop_done (length zs) m) (0, tpsK0 zs m m)"
  using assms tm_loop_trace_simple by (simp add: tmLoop_iteration esLoop_done_def)

lemma length_esLoop_done: "length (esLoop_done n m) \<le> m * (14 + 3 * m + (2 * m + 3) * n)"
  using length_concat_le[OF length_esLoop_do] esLoop_done_def by simp

definition tpsK_break :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsK_break zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m then \<zero>
           else if x = m + 1 then \<bar>
           else if x \<le> m + 1 + m * length zs then \<one>
           else 0,
      m + 1)]"

definition esK_break :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esK_break n m \<equiv> map (\<lambda>i. (1, 1 + Suc i)) [0..<m] @ [(1, 1 + m)]"

lemma length_esK_break: "length (esK_break n m) = m + 1"
  unfolding esK_break_def by simp

lemma tmK1_break:
  assumes "proper_symbols zs"
  shows "traces tmK1 (tpsK0 zs m m) (esK_break (length zs) m) (tpsK_break zs m)"
  unfolding tmK1_def
proof (rule traces_tm_right_until_1I[where ?n=m])
  show "1 < length (tpsK0 zs m m)"
    using tpsK0_def by simp
  show "rneigh (tpsK0 zs m m ! 1) {\<one>, \<bar>} m"
    using rneigh_def by (simp add: tpsK0_def)
  show "esK_break (length zs) m =
      map (\<lambda>j. (tpsK0 zs m m :#: 0, tpsK0 zs m m :#: 1 + Suc j)) [0..<m] @
      [(tpsK0 zs m m :#: 0, tpsK0 zs m m :#: 1 + m)]"
    by (simp add: esK_break_def tpsK0_def)
  show "tpsK_break zs m = (tpsK0 zs m m)[1 := tpsK0 zs m m ! 1 |+| m]"
    by (auto simp add: tpsK_break_def tpsK0_def)
qed

definition esLoop_break :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esLoop_break n m \<equiv> esK_break n m @ [(1, m + 1)]"

lemma length_esLoop_break: "length (esLoop_break n m) = m + 2"
  unfolding esLoop_break_def using length_esK_break by simp

lemma tmLoop_break:
  assumes "proper_symbols zs"
  shows "traces tmLoop (tpsK0 zs m m) (esLoop_break (length zs) m) (tpsK_break zs m)"
  unfolding tmLoop_def esLoop_break_def
proof (rule tm_loop_sem_false_traces[OF tmK1_break])
  show "proper_symbols zs"
    using assms .
  show "read (tpsK_break zs m) ! 1 \<noteq> \<one>"
    using tpsK_break_def read_def by simp
  show "esK_break (length zs) m @ [(1, m + 1)] =
      esK_break (length zs) m @ [(tpsK_break zs m :#: 0, tpsK_break zs m :#: 1)]"
    by (simp add: esK_break_def tpsK_break_def)
qed

definition esLoop :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esLoop n m \<equiv> esLoop_done n m @ esLoop_break n m"

lemma length_esLoop: "length (esLoop n m) \<le> m * (14 + 3 * m + (2 * m + 3) * n) + m + 2"
  unfolding esLoop_def using length_esLoop_done by (simp add: length_esLoop_break)

lemma length_esLoop': "length (esLoop n m) \<le> 2 + 18 * m * m + 5 * m * m * n"
proof -
  have "length (esLoop n m) \<le> m * (14 + 3 * m + (2 * m + 3) * n) + m + 2"
    using length_esLoop .
  also have "... = 14 * m + 3 * m * m + (2 * m * m + 3 * m) * n + m + 2"
    by algebra
  also have "... \<le> 15 * m * m + 3 * m * m + (2 * m * m + 3 * m) * n + 2"
    by simp
  also have "... \<le> 2 + 18 * m * m + 5 * m * m * n"
    by simp
  finally show ?thesis .
qed

lemma tmLoop:
  assumes "proper_symbols zs"
  shows "traces tmLoop (tpsK0 zs m 0) (esLoop (length zs) m) (tpsK_break zs m)"
  unfolding esLoop_def using assms by (intro traces_additive[OF tmLoop_done tmLoop_break])

lemma tmLoop':
  assumes "proper_symbols zs"
  shows "traces tmLoop (tpsB3 zs m) (esLoop (length zs) m) (tpsK_break zs m)"
  using assms tmLoop tpsK0_eq_tpsB3 by simp

definition esB4 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB4 n m \<equiv> esB3 n m @ esLoop n m"

lemma length_esB4: "length (esB4 n m) \<le> 7 + 20 * m * m + 5 * m * m * n"
proof -
  have "length (esB4 n m) \<le> 2 * m + 5 + m * (14 + 3 * m + (2 * m + 3) * n) + m + 2"
    unfolding esB4_def
    using length_esB3 length_esLoop
    by (smt ab_semigroup_add_class.add_ac(1) add_less_cancel_left le_eq_less_or_eq length_append)
  also have "... = 2 * m + 5 + (14 * m + 3 * m * m + (2 * m * m + 3 * m) * n) + m + 2"
    by algebra
  also have "... = 7 + 17 * m + 3 * m * m + (2 * m * m + 3 * m) * n"
    by simp
  also have "... \<le> 7 + 17 * m + 3 * m * m + 5 * m * m * n"
    by simp
  also have "... \<le> 7 + 20 * m * m + 5 * m * m * n"
    by simp
  finally show ?thesis .
qed

lemma tmB4:
  assumes "proper_symbols zs"
  shows "traces tmB4 (tps_ones zs m) (esB4 (length zs) m) (tpsK_break zs m)"
  unfolding tmB4_def esB4_def
  using assms by (intro traces_sequential[OF tmB3 tmLoop'])

definition tpsB5 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsB5 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m then \<zero>
           else if x \<le> m + 1 + m * length zs then \<one>
           else 0,
      m + 1)]"

definition esB5 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB5 n m \<equiv> esB4 n m @ [(1, m + 1)]"

lemma length_esB5: "length (esB5 n m) \<le> 8 + 20 * m * m + 5 * m * m * n"
  unfolding esB5_def
  using length_esB4
  by (metis Suc_le_mono length_append_singleton one_plus_numeral plus_1_eq_Suc plus_nat.simps(2)
    semiring_norm(2) semiring_norm(4) semiring_norm(8))

lemma tmB5:
  assumes "proper_symbols zs"
  shows "traces tmB5 (tps_ones zs m) (esB5 (length zs) m) (tpsB5 zs m)"
  unfolding tmB5_def esB5_def
proof (rule traces_sequential[OF tmB4])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_write 1 \<one>) (tpsK_break zs m) [(1, m + 1)] (tpsB5 zs m)"
  proof (rule traces_tm_write_1I)
    show "1 < length (tpsK_break zs m)"
      using tpsK_break_def by simp_all
    show "[(1, m + 1)] = [(tpsK_break zs m :#: 0, tpsK_break zs m :#: 1)]"
      using tpsK_break_def by simp
    show "tpsB5 zs m = (tpsK_break zs m)[1 := tpsK_break zs m ! 1 |:=| \<one>]"
      by (auto simp add: tpsK_break_def tpsB5_def)
  qed
qed

definition tpsB6 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsB6 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m then \<zero>
           else if x \<le> m + 1 + m * length zs then \<one>
           else 0,
      1)]"

definition esB56 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB56 n m \<equiv> map (Pair 1) (rev [0..<m + 1]) @ [(1, 0), (1, 1)]"

definition esB6 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB6 n m \<equiv> esB5 n m @ esB56 n m"

lemma length_esB6: "length (esB6 n m) \<le> 11 + 21 * m * m + 5 * m * m * n"
proof -
  have "length (esB6 n m) \<le> 8 + 20 * m * m + 5 * m * m * n + m + 3"
    unfolding esB6_def esB56_def using length_esB5 by (simp add: ab_semigroup_add_class.add_ac(1))
  also have "... = 11 + 20 * m * m + 5 * m * m * n + m"
    by simp
  also have "... \<le> 11 + 21 * m * m + 5 * m * m * n"
    by simp
  finally show ?thesis .
qed

lemma tmB6:
  assumes "proper_symbols zs"
  shows "traces tmB6 (tps_ones zs m) (esB6 (length zs) m) (tpsB6 zs m)"
  unfolding tmB6_def esB6_def
proof (rule traces_sequential[OF tmB5])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_cr 1) (tpsB5 zs m) (esB56 (length zs) m) (tpsB6 zs m)"
  proof (rule traces_tm_cr_1I)
    show "1 < length (tpsB5 zs m)"
      using tpsB5_def by simp
    show "clean_tape (tpsB5 zs m ! 1)"
      using tpsB5_def clean_tape_def by simp
    show "esB56 (length zs) m =
        map (Pair (tpsB5 zs m :#: 0)) (rev [0..<tpsB5 zs m :#: 1]) @
        [(tpsB5 zs m :#: 0, 0), (tpsB5 zs m :#: 0, 1)]"
      by (simp add: esB56_def tpsB5_def)
    show "tpsB6 zs m = (tpsB5 zs m)[1 := tpsB5 zs m ! 1 |#=| 1]"
      by (simp add: tpsB6_def tpsB5_def)
  qed
qed

definition tpsB7 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsB7 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m + 1 + m * length zs then \<one>
           else 0,
      m + 1)]"

definition esB67 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB67 n m \<equiv> map (\<lambda>i. (1, 1 + Suc i)) [0..<m] @ [(1, 1 + m)]"

definition esB7 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB7 n m \<equiv> esB6 n m @ esB67 n m"

lemma length_esB7: "length (esB7 n m) \<le> 12 + 22 * m * m + 5 * m * m * n"
proof -
  have "length (esB7 n m) \<le> 11 + 21 * m * m + 5 * m * m * n + m + 1"
    unfolding esB7_def esB67_def
    using length_esB6
    by (smt add.commute add_Suc_right add_le_cancel_right length_append length_append_singleton
      length_map length_upt minus_nat.diff_0 plus_1_eq_Suc)
  also have "... \<le> 12 + 22 * m * m + 5 * m * m * n"
    by simp
  finally show ?thesis .
qed

lemma tmB7:
  assumes "proper_symbols zs"
  shows "traces tmB7 (tps_ones zs m) (esB7 (length zs) m) (tpsB7 zs m)"
  unfolding tmB7_def esB7_def
proof (rule traces_sequential[OF tmB6])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_const_until 1 1 {\<one>} \<one>) (tpsB6 zs m) (esB67 (length zs) m) (tpsB7 zs m)"
  proof (rule traces_tm_const_until_11I)
    show "1 < length (tpsB6 zs m)" "3 < G"
      using tpsB6_def G G_ge4 by simp_all
    show "rneigh (tpsB6 zs m ! 1) {\<one>} m"
      using tpsB6_def by (intro rneighI) auto
    show "esB67 (length zs) m =
        map (\<lambda>i. (tpsB6 zs m :#: 0, tpsB6 zs m :#: 1 + Suc i)) [0..<m] @
        [(tpsB6 zs m :#: 0, tpsB6 zs m :#: 1 + m)]"
      by (simp add: tpsB6_def esB67_def)
    show "tpsB7 zs m = (tpsB6 zs m) [1 := constplant (tpsB6 zs m ! 1) \<one> m]"
      using constplant by (auto simp add: tpsB7_def tpsB6_def)
  qed
qed

definition tpsB8 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsB8 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m + 1 + m * length zs then \<one>
           else 0,
      1)]"

definition esB78 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB78 n m \<equiv> map (Pair 1) (rev [0..<m + 1]) @ [(1, 0), (1, 1)]"

definition esB8 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esB8 n m \<equiv> esB7 n m @ esB78 n m"

lemma length_esB8: "length (esB8 n m) \<le> 15 + 23 * m * m + 5 * m * m * n"
proof -
  have "length (esB8 n m) \<le> 12 + 22 * m * m + 5 * m * m * n + m + 3"
    unfolding esB8_def esB78_def using length_esB7 by (simp add: ab_semigroup_add_class.add_ac(1))
  also have "... \<le> 15 + 23 * m * m + 5 * m * m * n"
    by simp
  finally show ?thesis .
qed

lemma tmB8:
  assumes "proper_symbols zs"
  shows "traces tmB8 (tps_ones zs m) (esB8 (length zs) m) (tpsB8 zs m)"
  unfolding tmB8_def esB8_def
proof (rule traces_sequential[OF tmB7])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_cr 1) (tpsB7 zs m) (esB78 (length zs) m) (tpsB8 zs m)"
  proof (rule traces_tm_cr_1I)
    show "1 < length (tpsB7 zs m)"
      using tpsB7_def by simp
    show "clean_tape (tpsB7 zs m ! 1)"
      using tpsB7_def clean_tape_def by simp
    show "esB78 (length zs) m =
        map (Pair (tpsB7 zs m :#: 0)) (rev [0..<tpsB7 zs m :#: 1]) @
        [(tpsB7 zs m :#: 0, 0), (tpsB7 zs m :#: 0, 1)]"
      by (simp add: esB78_def tpsB7_def)
    show "tpsB8 zs m = (tpsB7 zs m)[1 := tpsB7 zs m ! 1 |#=| 1]"
      by (simp add: tpsB8_def tpsB7_def)
  qed
qed

lemma tps_ones_eq_tpsB8: "tpsB8 zs m = tps_ones zs (1 + m * (length zs + 1))"
  using tpsB8_def by auto

lemma tmB:
  assumes "proper_symbols zs"
  shows "traces tmB (tps_ones zs m) (esB8 (length zs) m) (tps_ones zs (1 + m * (length zs + 1)))"
  using assms tps_ones_eq_tpsB8 tmB8 tmB_eq_tmB8 by simp


subsection \<open>Appending a fixed number of symbols\<close>

text \<open>
The next Turing machine appends a constant number $c$ of \textbf{1} symbols to
the output tape.
\<close>

definition tmC :: "nat \<Rightarrow> machine" where
  "tmC c \<equiv>
    tm_right_until 1 {\<box>} ;;
    tm_write_repeat 1 \<one> c ;;
    tm_cr 1"

lemma tmC_tm: "turing_machine 2 G (tmC c)"
  unfolding tmC_def using tm_right_until_tm tm_write_repeat_tm tm_cr_tm G
  by simp

definition "tmC1 \<equiv> tm_right_until 1 {\<box>}"
definition "tmC2 c \<equiv> tmC1 ;; tm_write_repeat 1 \<one> c"
definition "tmC3 c \<equiv> tmC2 c ;; tm_cr 1"

definition tpsC1 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsC1 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m then \<one>
           else 0,
      m + 1)]"

definition esC1 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esC1 n m \<equiv> map (\<lambda>i. (1, 1 + Suc i)) [0..<m] @ [(1, 1 + m)]"

lemma length_esC1: "length (esC1 n m) = m + 1"
  unfolding esC1_def by simp

lemma tmC1:
  assumes "proper_symbols zs"
  shows "traces tmC1 (tps5 zs m) (esC1 (length zs) m) (tpsC1 zs m)"
  unfolding tmC1_def
proof (rule traces_tm_right_until_1I[where ?n=m])
  show "1 < length (tps5 zs m)"
    using tps5_def by simp
  show "rneigh (tps5 zs m ! 1) {0} m"
    using rneigh_def tps5_def by simp
  show "esC1 (length zs) m =
      map (\<lambda>i. (tps5 zs m :#: 0, tps5 zs m :#: 1 + Suc i)) [0..<m] @
      [(tps5 zs m :#: 0, tps5 zs m :#: 1 + m)]"
    by (simp add: tps5_def esC1_def)
  show "tpsC1 zs m = (tps5 zs m)[1 := tps5 zs m ! 1 |+| m]"
    by (simp add: tps5_def tpsC1_def)
qed

definition tpsC2 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsC2 zs m c \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m + c then \<one>
           else 0,
      m + 1 + c)]"

definition esC12 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esC12 n m c \<equiv> map (\<lambda>i. (1, m + 1 + Suc i)) [0..<c]"

definition esC2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esC2 n m c \<equiv> esC1 n m @ esC12 n m c"

lemma length_esC2: "length (esC2 n m c) = m + 1 + c"
  unfolding esC2_def by (simp add: length_esC1 esC12_def)

lemma tmC2:
  assumes "proper_symbols zs"
  shows "traces (tmC2 c) (tps5 zs m) (esC2 (length zs) m c) (tpsC2 zs m c)"
  unfolding tmC2_def esC2_def
proof (rule traces_sequential[OF tmC1])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_write_repeat 1 \<one> c) (tpsC1 zs m) (esC12 (length zs) m c) (tpsC2 zs m c)"
  proof (rule traces_tm_write_repeat_1I)
    show "1 < length (tpsC1 zs m)"
      using tpsC1_def by simp
    show "esC12 (length zs) m c =
        map (\<lambda>i. (tpsC1 zs m :#: 0, tpsC1 zs m :#: 1 + Suc i)) [0..<c]"
      by (simp add: esC12_def tpsC1_def)
    show "tpsC2 zs m c = (tpsC1 zs m)[1 := overwrite (tpsC1 zs m ! 1) \<one> c]"
      by (auto simp add: tpsC2_def tpsC1_def overwrite_def)
  qed
qed

definition tpsC3 :: "symbol list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape list" where
  "tpsC3 zs m c \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lambda>x. if x = 0 then \<triangleright>
           else if x \<le> m + c then \<one>
           else 0,
      1)]"

definition esC23 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esC23 n m c \<equiv> map (Pair 1) (rev [0..<m + 1 + c]) @ [(1, 0), (1, 1)]"

definition esC3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "esC3 n m c \<equiv> esC2 n m c @ esC23 n m c"

lemma length_esC3: "length (esC3 n m c) = 2 * m + 2 * c + 4"
  unfolding esC3_def by (simp add: length_esC2 esC23_def)

lemma tmC3:
  assumes "proper_symbols zs"
  shows "traces (tmC3 c) (tps5 zs m) (esC3 (length zs) m c) (tpsC3 zs m c)"
  unfolding tmC3_def esC3_def
proof (rule traces_sequential[OF tmC2])
  show "proper_symbols zs"
    using assms .
  show "traces (tm_cr 1) (tpsC2 zs m c) (esC23 (length zs) m c) (tpsC3 zs m c)"
  proof (rule traces_tm_cr_1I)
    show "1 < length (tpsC2 zs m c)"
      using tpsC2_def by simp
    show "clean_tape (tpsC2 zs m c ! 1)"
      using tpsC2_def clean_tape_def by simp
    show "esC23 (length zs) m c =
        map (Pair (tpsC2 zs m c :#: 0)) (rev [0..<tpsC2 zs m c :#: 1]) @
        [(tpsC2 zs m c :#: 0, 0), (tpsC2 zs m c :#: 0, 1)]"
      by (simp add: tpsC2_def esC23_def)
    show "tpsC3 zs m c = (tpsC2 zs m c)[1 := tpsC2 zs m c ! 1 |#=| 1]"
      by (simp add: tpsC2_def tpsC3_def)
  qed
qed

lemma tpsC3_eq_tps5: "tpsC3 zs m c = tps5 zs (m + c)"
  by (simp add: tpsC3_def tps5_def)

lemma tmC3_eq_tmC: "tmC3 = tmC"
  unfolding tmC_def tmC3_def tmC2_def tmC1_def by simp

lemma tmC:
  assumes "proper_symbols zs"
  shows "traces (tmC c) (tps_ones zs m) (esC3 (length zs) m c) (tps_ones zs (m + c))"
  using tmC3[OF assms] tmC3_eq_tmC tpsC3_eq_tps5 tps5_def by simp


subsection \<open>Polynomials of higher degree\<close>

text \<open>
In order to construct polynomials of arbitrary degree, we repeat the TM @{term
tmB}.
\<close>

fun tm_degree :: "nat \<Rightarrow> machine" where
  "tm_degree 0 = []" |
  "tm_degree (Suc d) = tm_degree d ;; tmB"

lemma tm_degree_tm: "turing_machine 2 G (tm_degree d)"
proof (induction d)
  case 0
  then show ?case
    by (simp add: turing_machine_def)
next
  case (Suc d)
  then show ?case
    using turing_machine_def tmB_tm
    by (metis tm_degree.simps(2) turing_machine_sequential_turing_machine)
qed

text \<open>
The number of \textbf{1} symbols the TM @{term "tm_degree d"} outputs on an
input of length $n$:
\<close>

fun m_degree :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "m_degree n 0 = n" |
  "m_degree n (Suc d) = 1 + m_degree n d * (n + 1)"

fun es_degree :: "nat \<Rightarrow> nat \<Rightarrow> (nat * nat) list" where
  "es_degree n 0 = []" |
  "es_degree n (Suc d) = es_degree n d @ esB8 n (m_degree n d)"

lemma tm_degree:
  assumes "proper_symbols zs"
  shows "traces
    (tm_degree d)
    (tps_ones zs (length zs))
    (es_degree (length zs) d)
    (tps_ones zs (m_degree (length zs) d))"
proof (induction d)
  case 0
  then show ?case
    by fastforce
next
  case (Suc d)
  have "traces (tm_degree d ;; tmB)
    (tps_ones zs (length zs))
    (es_degree (length zs) d @ esB8 (length zs) (m_degree (length zs) d))
    (tps_ones zs (m_degree (length zs) (Suc d)))"
  proof (rule traces_sequential[OF Suc.IH])
   show "traces tmB (tps_ones zs (m_degree (length zs) d))
      (esB8 (length zs) (m_degree (length zs) d))
      (tps_ones zs (m_degree (length zs) (Suc d)))"
    using tmB[OF assms, of "m_degree (length zs) d"] m_degree.simps(2) by presburger
  qed
  then show ?case
    by simp
qed

text \<open>
A lower bound for the number of \textbf{1} symbols the TM @{term "tm_degree d"}
outputs:
\<close>

lemma m_degree_ge_pow: "m_degree n d \<ge> n ^ (Suc d)"
proof (induction d)
  case 0
  then show ?case
    by simp
next
  case (Suc d)
  have "m_degree n (Suc d) = 1 + m_degree n d * (n + 1)"
    by simp
  then have "m_degree n (Suc d) \<ge> 1 + n ^ Suc d * (n + 1)"
    using Suc by (simp add: add_mono_thms_linordered_semiring(1))
  then have "m_degree n (Suc d) \<ge> 1 + n ^ Suc d * n + n ^ Suc d"
    by simp
  then have "m_degree n (Suc d) \<ge> 1 + n ^ (Suc (Suc d)) + n ^ Suc d"
    by (metis power_Suc2)
  then show ?case
    by simp
qed

text \<open>
An upper bound for the number of \textbf{1} symbols the TM @{term "tm_degree d"}
outputs:
\<close>

lemma m_degree_poly: "big_oh_poly (\<lambda>n. m_degree n d)"
proof (induction d)
  case 0
  have "(\<lambda>n. m_degree n 0) = (\<lambda>n. n)"
    by simp
  then show ?case
    using big_oh_poly_poly[of 1] by simp
next
  case (Suc d)
  have "big_oh_poly (\<lambda>n. n + 1)"
    using big_oh_poly_sum[OF big_oh_poly_poly[of 1] big_oh_poly_const[of 1]]
    by simp
  then have "big_oh_poly (\<lambda>n. m_degree n d * (n + 1))"
    using big_oh_poly_prod[OF Suc] by blast
  then have "big_oh_poly (\<lambda>n. 1 + m_degree n d * (n + 1))"
    using big_oh_poly_sum[OF big_oh_poly_const[of 1]] by simp
  then show ?case
    by simp
qed

corollary m_degree_plus_const_poly: "big_oh_poly (\<lambda>n. m_degree n d + c)"
  using m_degree_poly big_oh_poly_sum big_oh_poly_const by simp

lemma length_es_degree: "big_oh_poly (\<lambda>n. length (es_degree n d))"
proof (induction d)
  case 0
  then show ?case
    using big_oh_poly_const by simp
next
  case (Suc d)
  have "big_oh_poly (\<lambda>n. length (esB8 n (m_degree n d)))"
  proof -
    let ?m = "\<lambda>n. m_degree n d"
    have "big_oh_poly ?m"
      using m_degree_poly by simp
    then have "big_oh_poly (\<lambda>n. 15 + 23 * ?m n * ?m n + 5 * ?m n * ?m n * n)"
      using big_oh_poly_sum big_oh_poly_const big_oh_poly_prod big_oh_poly_poly[of 1]
      by simp
    then show ?thesis
      using length_esB8 big_oh_poly_le by simp
  qed
  then show ?case
    using Suc big_oh_poly_sum by simp
qed

text \<open>
Putting together the TM @{const tmA}, the TM @{term "tm_degree d"} for some $d$,
and the TM @{term "tmC c"} for some $c$, we get a family of TMs parameterized by
$d$ and $c$. These TMs construct all the polynomials we need.
\<close>

definition tm_poly :: "nat \<Rightarrow> nat \<Rightarrow> machine" where
  "tm_poly d c \<equiv> tmA ;; (tm_degree d ;; tmC c)"

lemma tm_poly_tm: "turing_machine 2 G (tm_poly d c)"
  unfolding tm_poly_def using tmA_tm tm_degree_tm tmC_tm by simp

definition es_poly :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "es_poly n d c \<equiv> es5 n @ es_degree n d @ esC3 n (m_degree n d) c"

text \<open>
On an input of length $n$ the Turing machine @{term "tm_poly d c"} outputs
@{term "m_degree n d + c"} symbols~@{text \<one>}.
\<close>

lemma tm_poly:
  assumes "proper_symbols zs"
  shows "traces
    (tm_poly d c)
    (tps0 zs)
    (es_poly (length zs) d c)
    (tps_ones zs (m_degree (length zs) d + c))"
  unfolding tm_poly_def es_poly_def
  using assms traces_sequential[OF tmA] traces_sequential[OF tm_degree] tmC
  by simp

text \<open>
The Turing machines run in polynomial time because their traces have polynomial
length:
\<close>

lemma length_es_poly: "big_oh_poly (\<lambda>n. length (es_poly n d c))"
proof -
  have "big_oh_poly (\<lambda>n. length (es5 n))"
    using length_es5 big_oh_poly_const big_oh_poly_prod big_oh_poly_sum big_oh_poly_poly[of 1]
    by simp
  moreover have "big_oh_poly (\<lambda>n. length (esC3 n (m_degree n d) c))"
  proof -
    have *: "(\<lambda>n. length (esC3 n (m_degree n d) c)) = (\<lambda>n. 2 * (m_degree n d) + 2 * c + 4)"
      using length_esC3 by fast
    have "big_oh_poly (\<lambda>n. 2 * (m_degree n d) + 2 * c + 4)"
      using m_degree_poly big_oh_poly_const big_oh_poly_prod big_oh_poly_sum by simp
    then show ?thesis
      by (simp add: *)
  qed
  ultimately have "big_oh_poly (\<lambda>n. length (es5 n) + length (es_degree n d) + length (esC3 n (m_degree n d) c))"
    using length_es_degree big_oh_poly_sum by blast
  then show ?thesis
    by (simp add: es_poly_def add.assoc)
qed

text \<open>
The Turing machine @{term "tm_poly d c"} outputs @{term "m_degree n c + c"} many
@{text \<one>} symbols on an input of length $n$. Hence for every polynomially
bounded function $f$ there is such a Turing machine outputting at least $f(n)$
symbols @{text \<one>}.
\<close>

lemma m_degree_plus_const:
  assumes "big_oh_poly f"
  obtains d c where "\<forall>n. f n \<le> m_degree n d + c"
proof -
  obtain c m d where f: "\<forall>n>m. f n \<le> c * n ^ d"
    using assms big_oh_poly by auto
  let ?d = "Suc d"
  let ?k = "max c m"
  have "n ^ ?d \<ge> c * n ^ d" if "n > ?k" for n
    using that by simp
  moreover have "f n \<le> c * n ^ d" if "n > ?k" for n
    using f that by simp
  ultimately have 1: "f n \<le> n ^ ?d" if "n > ?k" for n
    using that using order_trans by blast
  define c' where "c' = Max {f n| n. n \<le> ?k}"
  moreover have "finite {f n| n. n \<le> ?k}"
    by simp
  ultimately have "c' \<ge> f n" if "n \<le> ?k" for n
    using that Max.bounded_iff by blast
  then have "f n \<le> n ^ ?d + c'" if "n \<le> ?k" for n
    by (simp add: that trans_le_add2)
  moreover have "f n \<le> n ^ ?d + c'" if "n > ?k" for n
    using that 1 by fastforce
  ultimately have "f n \<le> n ^ ?d + c'" for n
    using leI by blast
  then have "f n \<le> m_degree n d + c'" for n
    using m_degree_ge_pow by (meson le_diff_conv less_le_trans not_le)
  then show ?thesis
    using that by auto
qed

text \<open>
The Turing machines are oblivious.
\<close>

lemma tm_poly_oblivious: "oblivious (tm_poly d c)"
proof -
  have tm: "turing_machine 2 G (tm_poly d c)"
    using tm_poly_tm by simp
  have init: "(0, tps0 zs) = start_config 2 zs" for zs
    using tps0_def start_config_def contents_def by auto
  {
    fix zs
    assume "bit_symbols zs"
    then have proper: "proper_symbols zs"
      by auto
    define tps where "tps = tps_ones zs (m_degree (length zs) d + c)"
    moreover define e where "e = (\<lambda>n. es_poly n d c)"
    ultimately have "trace (tm_poly d c) (start_config 2 zs) (e (length zs)) (length (tm_poly d c), tps)"
      using tm_poly init proper by (simp add: traces_def)
  }
  then show ?thesis
    using tm oblivious_def by fast
qed

end  (* locale turing_machine_poly *)

definition start_tapes_2 :: "symbol list \<Rightarrow> tape list" where
  "start_tapes_2 zs \<equiv>
    [(\<lfloor>zs\<rfloor>, 0),
     (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)]"

definition one_tapes_2 :: "symbol list \<Rightarrow> nat \<Rightarrow> tape list" where
  "one_tapes_2 zs m \<equiv>
    [(\<lfloor>zs\<rfloor>, 1),
     (\<lfloor>replicate m \<one>\<rfloor>, 1)]"

text \<open>
The main result of this chapter. For every polynomially bounded function $g$
there is a polynomial-time two-tape oblivious Turing machine that outputs at
least $g(n)$ symbols~@{text \<one>} for every input length $n$.
\<close>

lemma polystructor:
  assumes "big_oh_poly g" and "G \<ge> 5"
  shows "\<exists>M es f.
    turing_machine 2 G M \<and>
    big_oh_poly (\<lambda>n. length (es n)) \<and>
    big_oh_poly f \<and>
    (\<forall>n. g n \<le> f n) \<and>
    (\<forall>zs. proper_symbols zs \<longrightarrow> traces M (start_tapes_2 zs) (es (length zs)) (one_tapes_2 zs (f (length zs))))"
proof -
  interpret turing_machine_poly G
    using assms(2) by (simp add: turing_machine_poly_def)
  obtain d c where dc: "\<forall>n. g n \<le> m_degree n d + c"
    using assms(1) m_degree_plus_const by auto
  define M where "M = tm_poly d c"
  define es where "es = (\<lambda>n. es_poly n d c)"
  define f where "f = (\<lambda>n. m_degree n d + c)"
  have "turing_machine 2 G M"
    using M_def tm_poly_tm assms(2) by simp
  moreover have "big_oh_poly (\<lambda>n. length (es n))"
    using es_def length_es_poly by simp
  moreover have "\<forall>n. g n \<le> f n"
    using f_def dc by simp
  moreover have "big_oh_poly f"
    using f_def m_degree_plus_const_poly by simp
  moreover have
    "\<forall>zs. proper_symbols zs \<longrightarrow> traces M (start_tapes_2 zs) (es (length zs)) (one_tapes_2 zs (f (length zs)))"
  proof (standard, standard)
    fix zs
    assume zs: "proper_symbols zs"
    have "traces M (tps0 zs) (es (length zs)) (tps_ones zs (f (length zs)))"
      unfolding M_def es_def f_def using tm_poly[OF zs, of d c] by simp
    moreover have "tps0 = start_tapes_2"
      using tps0_def start_tapes_2_def by presburger
    ultimately have "traces M (start_tapes_2 zs) (es (length zs)) (tps_ones zs (f (length zs)))"
      by simp
    moreover have "one_tapes_2 = tps_ones"
      using one_tapes_2_def contents_def by fastforce
    ultimately show "traces M (start_tapes_2 zs) (es (length zs)) (one_tapes_2 zs (f (length zs)))"
      by metis
  qed
  ultimately show ?thesis
    by auto
qed

end