section \<open>Mapping between a binary and a quaternary alphabet\label{s:tm-quaternary}\<close>

theory Two_Four_Symbols
  imports Arithmetic
begin

text \<open>
Functions are defined over bit strings. For Turing machines these bits are
represented by the symbols \textbf{0} and \textbf{1}. Sometimes we want a TM to
receive a pair of bit strings or output a list of numbers. Or we might want the
TM to interpret the input as a list of lists of numbers. All these objects can
naturally be represented over a four-symbol (quaternary) alphabet, as we have
seen for pairs in Section~\ref{s:tm-basic-pair} and for the lists in
Sections~\ref{s:tm-numlist} and~\ref{s:tm-numlistlist}.

To accommodate the aforementioned use cases, we define a straightforward mapping
between the binary alphabet \textbf{01} and the quaternary alphabet @{text
"\<zero>\<one>\<bar>\<sharp>"} and devise Turing machines to encode and decode symbol sequences.
\<close>


subsection \<open>Encoding and decoding\label{s:tm-quaternary-encoding}\<close>

text \<open>
The encoding maps:

\begin{tabular}{lcl}
    @{text \<zero>} & $\mapsto$ & @{text "\<zero>\<zero>"}\\
    @{text \<one>} & $\mapsto$ & @{text "\<zero>\<one>"}\\
    @{text "\<bar>"} & $\mapsto$ & @{text "\<one>\<zero>"}\\
    @{text \<sharp>} & $\mapsto$ & @{text "\<one>\<one>"}\\
\end{tabular}
\<close>

text \<open>
For example, the list $[6,0,1]$ is represented by the symbols @{text
"\<zero>\<one>\<one>\<bar>\<bar>\<one>\<bar>"}, which is encoded as @{text "\<zero>\<zero>\<zero>\<one>\<zero>\<one>\<one>\<zero>\<one>\<zero>\<zero>\<one>\<one>\<zero>"}.
Pairing this sequence with the symbol sequence @{text "\<zero>\<one>\<one>\<zero>"} yields @{text
"\<zero>\<zero>\<zero>\<one>\<zero>\<one>\<one>\<zero>\<one>\<zero>\<zero>\<one>\<one>\<zero>\<sharp>\<zero>\<one>\<one>\<zero>"}, which is encoded as @{text
"\<zero>\<zero>\<zero>\<zero>\<zero>\<zero>\<zero>\<one>\<zero>\<zero>\<zero>\<one>\<zero>\<one>\<zero>\<zero>\<zero>\<one>\<zero>\<zero>\<zero>\<zero>\<zero>\<one>\<zero>\<one>\<zero>\<zero>\<one>\<one>\<zero>\<zero>\<zero>\<one>\<zero>\<one>\<zero>\<zero>"}.

\null
\<close>

definition binencode :: "symbol list \<Rightarrow> symbol list" where
  "binencode ys \<equiv> concat (map (\<lambda>y. [tosym ((y - 2) div 2), tosym ((y - 2) mod 2)]) ys)"

lemma length_binencode [simp]: "length (binencode ys) = 2 * length ys"
  using binencode_def by (induction ys) simp_all

lemma binencode_snoc:
  "binencode (zs @ [\<zero>]) = binencode zs @ [\<zero>, \<zero>]"
  "binencode (zs @ [\<one>]) = binencode zs @ [\<zero>, \<one>]"
  "binencode (zs @ [\<bar>]) = binencode zs @ [\<one>, \<zero>]"
  "binencode (zs @ [\<sharp>]) = binencode zs @ [\<one>, \<one>]"
  using binencode_def by simp_all

lemma binencode_at_even:
  assumes "i < length ys"
  shows "binencode ys ! (2 * i) = 2 + (ys ! i - 2) div 2"
  using assms
proof (induction ys arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  have *: "binencode (y # ys) = [2 + (y - 2) div 2, 2 + (y - 2) mod 2] @ binencode ys"
    using binencode_def by simp
  show ?case
  proof (cases "i = 0")
    case True
    then show ?thesis
      using * by simp
  next
    case False
    then have "binencode (y # ys) ! (2 * i) = binencode ys ! (2 * i - 2)"
      using *
      by (metis One_nat_def length_Cons less_one list.size(3) mult_2 nat_mult_less_cancel_disj
        nth_append numerals(2) plus_1_eq_Suc)
    also have "... = binencode ys ! (2 * (i - 1))"
      using False by (simp add: right_diff_distrib')
    also have "... = 2 + (ys ! (i - 1) - 2) div 2"
      using False Cons by simp
    also have "... = 2 + ((y # ys) ! i - 2) div 2"
      using False by simp
    finally show ?thesis .
  qed
qed

lemma binencode_at_odd:
  assumes "i < length ys"
  shows "binencode ys ! (2 * i + 1) = 2 + (ys ! i - 2) mod 2"
  using assms
proof (induction ys arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys)
  have *: "binencode (y # ys) = [2 + (y - 2) div 2, 2 + (y - 2) mod 2] @ binencode ys"
    using binencode_def by simp
  show ?case
  proof (cases "i = 0")
    case True
    then show ?thesis
      using * by simp
  next
    case False
    then have "binencode (y # ys) ! (2 * i + 1) = binencode ys ! (2 * i + 1 - 2)"
      using * by simp
    also have "... = binencode ys ! (2 * (i - 1) + 1)"
      using False
      by (metis Nat.add_diff_assoc2 One_nat_def Suc_leI diff_mult_distrib2 mult_2 mult_le_mono2 nat_1_add_1 neq0_conv)
    also have "... = 2 + (ys ! (i - 1) - 2) mod 2"
      using False Cons by simp
    also have "... = 2 + ((y # ys) ! i - 2) mod 2"
      using False by simp
    finally show ?thesis .
  qed
qed

text \<open>
While @{const binencode} is defined for arbitrary symbol sequences, we only
consider sequences over @{text "\<zero>\<one>\<bar>\<sharp>"} to be binencodable.
\<close>

abbreviation binencodable :: "symbol list \<Rightarrow> bool" where
  "binencodable ys \<equiv> \<forall>i<length ys. 2 \<le> ys ! i \<and> ys ! i < 6"

lemma binencodable_append:
  assumes "binencodable xs" and "binencodable ys"
  shows "binencodable (xs @ ys)"
  using assms prop_list_append by (simp add: nth_append)

lemma bit_symbols_binencode:
  assumes "binencodable ys"
  shows "bit_symbols (binencode ys)"
proof -
  have "2 \<le> binencode ys ! i \<and> binencode ys ! i \<le> 3" if "i < length (binencode ys)" for i
  proof (cases "even i")
    case True
    then have len: "i div 2 < length ys"
      using length_binencode that by simp
    moreover have "2 * (i div 2) = i"
      using True by simp
    ultimately have "binencode ys ! i = 2 + (ys ! (i div 2) - 2) div 2"
      using binencode_at_even[of "i div 2" ys] by simp
    moreover have "2 \<le> ys ! (i div 2) \<and> ys ! (i div 2) < 6"
      using len assms by simp
    ultimately show ?thesis
      by auto
  next
    case False
    then have len: "i div 2 < length ys"
      using length_binencode that by simp
    moreover have "2 * (i div 2) + 1 = i"
      using False by simp
    ultimately have "binencode ys ! i = 2 + (ys ! (i div 2) - 2) mod 2"
      using binencode_at_odd[of "i div 2" ys] by simp
    moreover have "2 \<le> ys ! (i div 2) \<and> ys ! (i div 2) < 6"
      using len assms by simp
    ultimately show ?thesis
      by simp
  qed
  then show ?thesis
    by fastforce
qed

text \<open>
An encoded symbol sequence is of even length. When decoding a symbol sequence of
odd length, we ignore the last symbol. For example, @{text "\<zero>\<one>\<one>\<one>\<zero>\<zero>"} and
@{text "\<zero>\<one>\<one>\<one>\<zero>\<zero>\<one>"} are both decoded to @{text "\<one>\<sharp>\<zero>"}.

The bit symbol sequence @{term "[a, b]"} is decoded to this symbol:
\<close>

abbreviation decsym :: "symbol \<Rightarrow> symbol \<Rightarrow> symbol" where
  "decsym a b \<equiv> tosym (2 * todigit a + todigit b)"

definition bindecode :: "symbol list \<Rightarrow> symbol list" where
  "bindecode zs \<equiv> map (\<lambda>i. decsym (zs ! (2 * i)) (zs ! (Suc (2 * i)))) [0..<length zs div 2]"

lemma length_bindecode [simp]: "length (bindecode zs) = length zs div 2"
  using bindecode_def by simp

lemma bindecode_at:
  assumes "i < length zs div 2"
  shows "bindecode zs ! i = decsym (zs ! (2 * i)) (zs ! (Suc (2 * i)))"
  using assms bindecode_def by simp

lemma proper_bindecode: "proper_symbols (bindecode zs)"
  using bindecode_at by simp

lemma bindecode2345:
  assumes "bit_symbols zs"
  shows "\<forall>i<length (bindecode zs). bindecode zs ! i \<in> {2..<6}"
  using assms bindecode_at by simp

lemma bindecode_odd:
  assumes "length zs = 2 * n + 1"
  shows "bindecode zs = bindecode (take (2 * n) zs)"
proof -
  have 1: "take (2 * n) zs ! (2 * i) = zs ! (2 * i)" if "i < n" for i
    using assms that by simp
  have 2: "take (2 * n) zs ! (Suc (2 * i)) = zs ! (Suc (2 * i))" if "i < n" for i
    using assms that by simp
  have "bindecode (take (2 * n) zs) =
      map (\<lambda>i. decsym ((take (2 * n) zs) ! (2 * i)) ((take (2 * n) zs) ! (Suc (2 * i)))) [0..<length (take (2 * n) zs) div 2]"
    using bindecode_def by simp
  also have "... = map (\<lambda>i. decsym ((take (2 * n) zs) ! (2 * i)) ((take (2 * n) zs) ! (Suc (2 * i)))) [0..<n]"
    using assms by (simp add: min_absorb2)
  also have "... = map (\<lambda>i. decsym (zs ! (2 * i)) (zs ! (Suc (2 * i)))) [0..<n]"
    by simp
  also have "... = map (\<lambda>i. decsym (zs ! (2 * i)) (zs ! (Suc (2 * i)))) [0..<length zs div 2]"
    using assms by simp
  also have "... = bindecode zs"
    using bindecode_def by simp
  finally show ?thesis
    by simp
qed

lemma bindecode_append:
  assumes "even (length ys)" and "even (length zs)"
  shows "bindecode (ys @ zs) = bindecode ys @ bindecode zs"
    (is "?lhs = ?rhs")
proof (rule nth_equalityI)
  show 1: "length ?lhs = length ?rhs"
    using assms by simp
  show "?lhs ! i = ?rhs ! i" if "i < length ?lhs" for i
  proof (cases "i < length ys div 2")
    case True
    have "?lhs ! i = decsym ((ys @ zs) ! (2 * i)) ((ys @ zs) ! (Suc (2 * i)))"
      using that bindecode_at length_bindecode by simp
    also have "... = decsym (ys ! (2 * i)) ((ys @ zs) ! (Suc (2 * i)))"
      using True assms(1)
      by (metis Suc_1 dvd_mult_div_cancel nat_mult_less_cancel_disj nth_append zero_less_Suc)
    also have "... = decsym (ys ! (2 * i)) (ys ! (Suc (2 * i)))"
      using True assms(1)
      by (metis Suc_1 Suc_lessI Suc_mult_less_cancel1 dvd_mult_div_cancel dvd_triv_left even_Suc nth_append)
    also have "... = bindecode ys ! i"
      using True bindecode_at by simp
    also have "... = ?rhs ! i"
      by (simp add: True nth_append)
    finally show ?thesis .
  next
    case False
    let ?l = "length ys"
    have l: "length (bindecode ys) = ?l div 2"
      by simp
    have "?lhs ! i = decsym ((ys @ zs) ! (2 * i)) ((ys @ zs) ! (Suc (2 * i)))"
      using that bindecode_at length_bindecode by simp
    also have "... = decsym (zs ! (2 * i - ?l)) ((ys @ zs) ! (Suc (2 * i)))"
      using False assms
      by (metis dvd_mult_div_cancel nat_mult_less_cancel_disj nth_append)
    also have "... = decsym (zs ! (2 * i - ?l)) (zs ! (Suc (2 * i) - ?l))"
      using False assms
      by (metis (no_types, lifting) Suc_eq_plus1 add_lessD1 dvd_mult_div_cancel nat_mult_less_cancel_disj nth_append)
    also have "... = bindecode zs ! (i - ?l div 2)"
      using False bindecode_at that assms 1
       by (smt (z3) Suc_eq_plus1 add_diff_inverse_nat diff_add_inverse diff_mult_distrib2 dvd_mult_div_cancel
         left_add_mult_distrib length_append length_bindecode mult.commute nat_add_left_cancel_less)
    also have "... = (bindecode ys @ bindecode zs) ! i"
      using l False by (simp add: nth_append)
    finally show ?thesis .
  qed
qed

lemma bindecode_take_snoc:
  assumes "i < length zs div 2"
  shows "bindecode (take (2 * i) zs) @ [decsym (zs ! (2*i)) (zs ! (Suc (2*i)))] = bindecode (take (2 * Suc i) zs)"
proof -
  let ?ys = "take (2 * i) zs"
  let ?zs = "take 2 (drop (2 * i) zs)"
  have "?zs ! 0 = zs ! (2 * i)"
    using assms by simp
  moreover have "?zs ! 1 = zs ! (Suc (2 * i))"
    using assms by simp
  moreover have "length ?zs = 2"
    using assms by simp
  ultimately have "?zs = [zs ! (2 * i), zs ! (Suc (2 * i))]"
    by (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_1 diff_Suc_1 drop0
     length_0_conv length_drop lessI list.inject zero_less_Suc)
  moreover have "take (2 * i + 2) zs = ?ys @ ?zs"
    using assms take_add by blast
  ultimately have "take (2 * Suc i) zs = ?ys @ [zs ! (2 * i), zs ! (Suc (2 * i))]"
    by simp
  moreover have "even (length ?ys)"
  proof -
    have "length ?ys = 2 * i"
      using assms by simp
    then show ?thesis
      by simp
  qed
  ultimately have "bindecode (take (2 * Suc i) zs) = bindecode ?ys @ bindecode [zs ! (2 * i), zs ! (Suc (2 * i))]"
    using bindecode_append by simp
  then show ?thesis
    using bindecode_def by simp
qed

lemma bindecode_encode:
  assumes "binencodable ys"
  shows "bindecode (binencode ys) = ys"
proof (rule nth_equalityI)
  show 1: "length (bindecode (binencode ys)) = length ys"
    using binencode_def bindecode_def by fastforce
  show "bindecode (binencode ys) ! i = ys ! i" if "i < length (bindecode (binencode ys))" for i
  proof -
    have len: "i < length ys"
      using that 1 by simp
    let ?zs = "binencode ys"
    have "i < length ?zs div 2"
      using len by simp
    then have "bindecode ?zs ! i = decsym (?zs ! (2 * i)) (?zs ! (Suc (2 * i)))"
      using bindecode_def by simp
    also have "... = decsym (2 + (ys ! i - 2) div 2) (2 + (ys ! i - 2) mod 2)"
      using binencode_at_even[OF len] binencode_at_odd[OF len] by simp
    also have "... = ys ! i"
    proof -
      have "ys ! i = 2 \<or> ys ! i = 3 \<or> ys ! i = 4 \<or> ys ! i = 5"
        using assms len
        by (smt (z3) Suc_1 add_Suc_shift add_cancel_right_left eval_nat_numeral(3)
          less_Suc_eq numeral_3_eq_3 numeral_Bit0 verit_comp_simplify1(3))
      then show ?thesis
        by auto
    qed
    finally show "bindecode ?zs ! i = ys ! i" .
  qed
qed

lemma binencode_decode:
  assumes "bit_symbols zs" and "even (length zs)"
  shows "binencode (bindecode zs) = zs"
proof (rule nth_equalityI)
  let ?ys = "bindecode zs"
  show 1: "length (binencode ?ys) = length zs"
    using binencode_def bindecode_def assms(2) by fastforce
  show "binencode ?ys ! i = zs ! i" if "i < length (binencode ?ys)" for i
  proof -
    have ilen: "i < length zs"
      using 1 that by simp
    show ?thesis
    proof (cases "even i")
      case True
      let ?j = "i div 2"
      have jlen: "?j < length zs div 2"
        using ilen by (simp add: assms(2) less_mult_imp_div_less)
      then have ysj: "?ys ! ?j = decsym (zs ! (2 * ?j)) (zs ! (Suc (2 * ?j)))"
        using bindecode_def by simp
      have "binencode ?ys ! i = binencode ?ys ! (2 * ?j)"
        by (simp add: True)
      also have "... = 2 + (?ys ! ?j - 2) div 2"
        using binencode_at_even jlen by simp
      also have "... = zs ! (2 * ?j)"
        using ysj True assms(1) ilen by auto
      also have "... = zs ! i"
        using True by simp
      finally show "binencode ?ys ! i = zs ! i" .
    next
      case False
      let ?j = "i div 2"
      have jlen: "?j < length zs div 2"
        using ilen by (simp add: assms(2) less_mult_imp_div_less)
      then have ysj: "?ys ! ?j = decsym (zs ! (2 * ?j)) (zs ! (Suc (2 * ?j)))"
        using bindecode_def by simp
      have "binencode ?ys ! i = binencode ?ys ! (2 * ?j + 1)"
        by (simp add: False)
      also have "... = 2 + (?ys ! ?j - 2) mod 2"
        using binencode_at_odd jlen by simp
      also have "... = zs ! (2 * ?j + 1)"
        using ysj False assms(1) ilen by auto
      also have "... = zs ! i"
        using False by simp
      finally show "binencode ?ys ! i = zs ! i" .
    qed
  qed
qed

lemma binencode_inj:
  assumes "binencodable xs" and "binencodable ys" and "binencode xs = binencode ys"
  shows "xs = ys"
  using assms bindecode_encode by metis


subsection \<open>Turing machines for encoding and decoding\<close>

text \<open>
The next Turing machine implements @{const binencode} for @{const binencodable}
symbol sequences. It expects a symbol sequence @{term zs} on tape $j_1$ and
writes @{term "binencode zs"} to tape $j_2$.
\<close>

definition tm_binencode :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_binencode j1 j2 \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      IF \<lambda>rs. rs ! j1 = \<zero> THEN
        tm_print j2 [\<zero>, \<zero>]
      ELSE
        IF \<lambda>rs. rs ! j1 = \<one> THEN
          tm_print j2 [\<zero>, \<one>]
        ELSE
          IF \<lambda>rs. rs ! j1 = \<bar> THEN
            tm_print j2 [\<one>, \<zero>]
          ELSE
            tm_print j2 [\<one>, \<one>]
          ENDIF
        ENDIF
      ENDIF ;;
      tm_right j1
    DONE"

lemma tm_binencode_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "j1 < k" and "j2 < k" and "0 < j2"
  shows "turing_machine k G (tm_binencode j1 j2)"
proof -
  have *: "symbols_lt G [\<zero>, \<zero>]" "symbols_lt G [\<zero>, \<one>]" "symbols_lt G [\<one>, \<zero>]" "symbols_lt G [\<one>, \<one>]"
    using assms(2) by (simp_all add: nth_Cons')
  then have "turing_machine k G (tm_print j2 [\<zero>, \<zero>])"
    using tm_print_tm[OF assms(5,4,2)] assms by blast
  moreover have "turing_machine k G (tm_print j2 [\<zero>, \<one>])"
    using * tm_print_tm[OF assms(5,4,2)] assms by blast
  moreover have "turing_machine k G (tm_print j2 [\<one>, \<zero>])"
    using * tm_print_tm[OF assms(5,4,2)] assms by blast
  moreover have "turing_machine k G (tm_print j2 [\<one>, \<one>])"
    using * tm_print_tm[OF assms(5,4,2)] assms by blast
  ultimately show ?thesis
    unfolding tm_binencode_def
    using turing_machine_loop_turing_machine Nil_tm turing_machine_branch_turing_machine tm_right_tm assms
    by simp
qed

locale turing_machine_binencode =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> IF \<lambda>rs. rs ! j1 = \<bar> THEN tm_print j2 [\<one>, \<zero>] ELSE tm_print j2 [\<one>, \<one>] ENDIF"
definition "tm2 \<equiv> IF \<lambda>rs. rs ! j1 = \<one> THEN tm_print j2 [\<zero>, \<one>] ELSE tm1 ENDIF"
definition "tm3 \<equiv> IF \<lambda>rs. rs ! j1 = \<zero> THEN tm_print j2 [\<zero>, \<zero>] ELSE tm2 ENDIF"
definition "tm4 \<equiv> tm3 ;; tm_right j1"
definition "tm5 \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tm4 DONE"

lemma tm5_eq_tm_binencode: "tm5 = tm_binencode j1 j2"
  using tm5_def tm4_def tm3_def tm2_def tm1_def tm_binencode_def by simp

context
  fixes k :: nat and tps0 :: "tape list" and zs :: "symbol list"
  assumes jk: "k = length tps0" "j1 \<noteq> j2" "0 < j2" "j1 < k" "j2 < k"
  assumes zs: "binencodable zs"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
begin

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, Suc t),
     j2 := (\<lfloor>binencode (take t zs)\<rfloor>, Suc (2 * t))]"

lemma tpsL_0: "tpsL 0 = tps0"
  unfolding tpsL_def using tps0 jk
  by (metis One_nat_def length_0_conv length_binencode list_update_id mult_0_right take0)

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [j1 := (\<lfloor>zs\<rfloor>, Suc t),
     j2 := (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)]"

lemma read_tpsL:
  assumes "t < length zs"
  shows "read (tpsL t) ! j1 = zs ! t"
proof -
  have "tpsL t ! j1 = (\<lfloor>zs\<rfloor>, Suc t)"
    using tpsL_def jk by simp
  moreover have "j1 < length (tpsL t)"
    using tpsL_def jk by simp
  ultimately show "read (tpsL t) ! j1 = zs ! t"
    using assms tapes_at_read'
    by (metis Suc_leI contents_inbounds diff_Suc_1 fst_conv snd_conv zero_less_Suc)
qed

lemma tm1 [transforms_intros]:
  assumes "t < length zs" and "zs ! t = \<bar> \<or> zs ! t = \<sharp>"
  shows "transforms tm1 (tpsL t) 4 (tpsL1 t)"
  unfolding tm1_def
proof (tform tps: jk tpsL_def)
  have 1: "tpsL t ! j2 = (\<lfloor>binencode (take t zs)\<rfloor>, Suc (2 * t))"
    using tpsL_def jk by simp
  have 2: "length (binencode (take t zs)) = 2 * t"
    using assms(1) by simp
  have "inscribe (tpsL t ! j2) [\<one>, \<zero>] = (\<lfloor>binencode (take t zs) @ [\<one>, \<zero>]\<rfloor>, Suc (2 * t) + 2)"
    using inscribe_contents 1 2
    by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 add_Suc_shift list.size(3) list.size(4))
  moreover have "binencode (take t zs) @ [\<one>, \<zero>] = binencode (take (Suc t) zs)" if "zs ! t = \<bar>"
    using that assms(1) binencode_snoc by (metis take_Suc_conv_app_nth)
  ultimately have 5: "inscribe (tpsL t ! j2) [\<one>, \<zero>] = (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)"
      if "zs ! t = \<bar>"
    using that by simp
  have "inscribe (tpsL t ! j2) [\<one>, \<one>] = (\<lfloor>binencode (take t zs) @ [\<one>, \<one>]\<rfloor>, Suc (2 * t) + 2)"
    using inscribe_contents 1 2
    by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 add_Suc_shift list.size(3) list.size(4))
  moreover have "binencode (take t zs) @ [\<one>, \<one>] = binencode (take (Suc t) zs)" if "zs ! t = 5"
    using that assms(1) binencode_snoc by (metis take_Suc_conv_app_nth)
  ultimately have 6: "inscribe (tpsL t ! j2) [\<one>, \<one>] = (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)"
      if "zs ! t = \<sharp>"
    using that by simp
  have 7: "tpsL1 t = (tpsL t)[j2 := (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)]"
    unfolding tpsL1_def tpsL_def by (simp only: list_update_overwrite)
  then have 8: "tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<one>, \<zero>]]" if "zs ! t = \<bar>"
      using that 5 by simp
  have 9: "tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<one>, \<one>]]" if "zs ! t = \<sharp>"
      using that 6 7 by simp
  show "read (tpsL t) ! j1 = \<bar> \<Longrightarrow>
      tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<one>, \<zero>]]"
    using read_tpsL[OF assms(1)] 8 by simp
  show "read (tpsL t) ! j1 \<noteq> \<bar> \<Longrightarrow>
      tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<one>, \<one>]]"
    using read_tpsL[OF assms(1)] 9 assms(2) by simp
qed

lemma tm2 [transforms_intros]:
  assumes "t < length zs" and "zs ! t = \<bar> \<or> zs ! t = \<sharp> \<or> zs ! t = \<one>"
  shows "transforms tm2 (tpsL t) 5 (tpsL1 t)"
  unfolding tm2_def
proof (tform tps: tpsL_def jk assms(1))
  have 1: "tpsL t ! j2 = (\<lfloor>binencode (take t zs)\<rfloor>, Suc (2 * t))"
    using tpsL_def jk by simp
  have 2: "length (binencode (take t zs)) = 2 * t"
    using assms(1) by simp
  show "read (tpsL t) ! j1 \<noteq> \<one> \<Longrightarrow> zs ! t = \<bar> \<or> zs ! t = \<sharp>"
    using read_tpsL[OF assms(1)] assms(2) by simp
  show "tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<zero>, \<one>]]" if "read (tpsL t) ! j1 = \<one>"
  proof -
    have *: "zs ! t = \<one>"
      using read_tpsL[OF assms(1)] that by simp
    have "inscribe (tpsL t ! j2) [\<zero>, \<one>] = (\<lfloor>binencode (take t zs) @ [2, \<one>]\<rfloor>, Suc (2 * t) + 2)"
      using inscribe_contents 1 2
      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 add_Suc_shift list.size(3) list.size(4))
    moreover have "binencode (take t zs) @ [\<zero>, \<one>] = binencode (take (Suc t) zs)"
      using * assms(1) binencode_snoc by (metis take_Suc_conv_app_nth)
    ultimately have "inscribe (tpsL t ! j2) [\<zero>, \<one>] = (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)"
      by simp
    moreover have "tpsL1 t = (tpsL t)[j2 := (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)]"
      unfolding tpsL1_def tpsL_def by (simp only: list_update_overwrite)
    ultimately show "tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<zero>, \<one>]]"
      using that by simp
  qed
qed

lemma tm3 [transforms_intros]:
  assumes "t < length zs"
  shows "transforms tm3 (tpsL t) 6 (tpsL1 t)"
  unfolding tm3_def
proof (tform tps: jk assms tpsL_def)
  have 1: "tpsL t ! j2 = (\<lfloor>binencode (take t zs)\<rfloor>, Suc (2 * t))"
    using tpsL_def jk by simp
  have 2: "length (binencode (take t zs)) = 2 * t"
    using assms by simp
  show "read (tpsL t) ! j1 \<noteq> \<zero> \<Longrightarrow> zs ! t = \<bar> \<or> zs ! t = \<sharp> \<or> zs ! t = \<one>"
    using assms zs read_tpsL by auto
  show "tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<zero>, \<zero>]]" if "read (tpsL t) ! j1 = \<zero>"
  proof -
    have *: "zs ! t = \<zero>"
      using read_tpsL[OF assms] that by simp
    have "inscribe (tpsL t ! j2) [\<zero>, \<zero>] = (\<lfloor>binencode (take t zs) @ [\<zero>, \<zero>]\<rfloor>, Suc (2 * t) + 2)"
      using inscribe_contents 1 2
      by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 add_Suc_shift list.size(3) list.size(4))
    moreover have "binencode (take t zs) @ [\<zero>, \<zero>] = binencode (take (Suc t) zs)"
      using * assms binencode_snoc by (metis take_Suc_conv_app_nth)
    ultimately have "inscribe (tpsL t ! j2) [\<zero>, \<zero>] = (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)"
      by simp
    moreover have "tpsL1 t = (tpsL t)[j2 := (\<lfloor>binencode (take (Suc t) zs)\<rfloor>, Suc (2 * t) + 2)]"
      unfolding tpsL1_def tpsL_def by (simp only: list_update_overwrite)
    ultimately show "tpsL1 t = (tpsL t)[j2 := inscribe (tpsL t ! j2) [\<zero>, \<zero>]]"
      using that by simp
  qed
qed

lemma tm4 [transforms_intros]:
  assumes "t < length zs"
  shows "transforms tm4 (tpsL t) 7 (tpsL (Suc t))"
  unfolding tm4_def
proof (tform tps: assms tpsL1_def jk)
  have *: "tpsL1 t ! j1 = (\<lfloor>zs\<rfloor>, Suc t)"
    using tpsL1_def jk by simp
  show "tpsL (Suc t) = (tpsL1 t)[j1 := tpsL1 t ! j1 |+| 1]"
    using tpsL_def tpsL1_def using jk * by (auto simp add: list_update_swap[of _ j1])
qed

lemma tm5:
  assumes "ttt = 9 * length zs + 1"
  shows "transforms tm5 (tpsL 0) ttt (tpsL (length zs))"
  unfolding tm5_def
proof (tform)
  show "\<And>t. t < length zs \<Longrightarrow> read (tpsL t) ! j1 \<noteq> \<box>"
    using read_tpsL zs by auto
  show "\<not> read (tpsL (length zs)) ! j1 \<noteq> \<box>"
  proof -
    have "tpsL (length zs) ! j1 = (\<lfloor>zs\<rfloor>, Suc (length zs))"
      using tpsL_def jk by simp
    moreover have "j1 < length (tpsL (length zs))"
      using tpsL_def jk by simp
    ultimately have "read (tpsL (length zs)) ! j1 = tape_read (\<lfloor>zs\<rfloor>, Suc (length zs))"
      using tapes_at_read' by fastforce
    also have "... = \<box>"
      using contents_outofbounds by simp
    finally show ?thesis
      by simp
  qed
  show "length zs * (7 + 2) + 1 \<le> ttt"
    using assms by simp
qed

lemma tpsL: "tpsL (length zs) = tps0
  [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
   j2 := (\<lfloor>binencode zs\<rfloor>, Suc (2 * (length zs)))]"
  unfolding tpsL_def using tps0 jk by simp

lemma tm5':
  assumes "ttt = 9 * length zs + 1"
  shows "transforms tm5 tps0 ttt (tpsL (length zs))"
  using assms tm5 tpsL_0 by simp

end

end  (* locale turing_machine_binencode *)

lemma transforms_tm_binencodeI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k :: nat and zs :: "symbol list"
  assumes "k = length tps" "j1 \<noteq> j2" "0 < j2" "j1 < k" "j2 < k"
    and "binencodable zs"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 9 * length zs + 1"
  assumes "tps' \<equiv> tps
    [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
     j2 := (\<lfloor>binencode zs\<rfloor>, Suc (2 * (length zs)))]"
  shows "transforms (tm_binencode j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_binencode j1 j2 .
  show ?thesis
    using assms loc.tm5' loc.tm5_eq_tm_binencode loc.tpsL by simp
qed

text \<open>
The next command reads chunks of two symbols over @{text "\<zero>\<one>"} from one tape
and writes to another tape the corresponding symbol over @{text "\<zero>\<one>\<bar>\<sharp>"}.  The
first symbol of each chunk is memorized on the last tape.  If the end of the
input (that is, a blank symbol) is encountered, the command stops without
writing another symbol.
\<close>

definition cmd_bindec :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> command" where
  "cmd_bindec j1 j2 rs \<equiv>
    if rs ! j1 = 0 then (1, map (\<lambda>z. (z, Stay)) rs)
    else (0,
     map (\<lambda>i.
       if last rs = \<triangleright>
       then if i = j1 then (rs ! i, Right)
            else if i = j2 then (rs ! i, Stay)
            else if i = length rs - 1 then (tosym (todigit (rs ! j1)), Stay)
            else (rs ! i, Stay)
       else if i = j1 then (rs ! i, Right)
            else if i = j2 then (decsym (last rs) (rs ! j1), Right)
            else if i = length rs - 1 then (1, Stay)
            else (rs ! i, Stay))
     [0..<length rs])"

text \<open>
The Turing machine performing the decoding:
\<close>

definition tm_bindec :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_bindec j1 j2 = [cmd_bindec j1 j2]"

context
  fixes j1 j2 :: tapeidx and k :: nat
  assumes j_less: "j1 < k" "j2 < k"
    and j_gt: "0 < j2"
begin

lemma turing_command_bindec:
  assumes "G \<ge> 6"
  shows "turing_command (Suc k) 1 G (cmd_bindec j1 j2)"
proof
  show "\<And>gs. length gs = Suc k \<Longrightarrow> length ([!!] cmd_bindec j1 j2 gs) = length gs"
    using cmd_bindec_def by simp
  show "cmd_bindec j1 j2 gs [.] j < G"
      if "length gs = Suc k" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G" "j < length gs"
      for gs j
  proof (cases "gs ! j1 = \<box>")
    case True
    then show ?thesis
      using that cmd_bindec_def by simp
  next
    case else: False
    show ?thesis
    proof (cases "last gs = \<triangleright>")
      case True
      then have "snd (cmd_bindec j1 j2 gs) = map (\<lambda>i.
              if i = j1 then (gs ! i, Right)
              else if i = j2 then (gs ! i, Stay)
              else if i = length gs - 1 then (todigit (gs ! j1) + 2, Stay)
              else (gs ! i, Stay)) [0..<length gs]"
        using cmd_bindec_def else by simp
      then have "cmd_bindec j1 j2 gs [!] j =
            (if j = j1 then (gs ! j, Right)
              else if j = j2 then (gs ! j, Stay)
              else if j = length gs - 1 then (todigit (gs ! j1) + 2, Stay)
              else (gs ! j, Stay))"
        using that(3) by simp
      then have "cmd_bindec j1 j2 gs [.] j =
            (if j = j1 then gs ! j
              else if j = j2 then gs ! j
              else if j = length gs - 1 then todigit (gs ! j1) + 2
              else gs ! j)"
        by simp
      then show ?thesis
        using that assms by simp
    next
      case False
      then have "snd (cmd_bindec j1 j2 gs) = map (\<lambda>i.
            if i = j1 then (gs ! i, Right)
            else if i = j2 then (2 * todigit (last gs) + todigit (gs ! j1) + 2, Right)
            else if i = length gs - 1 then (1, Stay)
            else (gs ! i, Stay)) [0..<length gs]"
        using cmd_bindec_def else by simp
      then have "cmd_bindec j1 j2 gs [!] j =
          (if j = j1 then (gs ! j, Right)
            else if j = j2 then (2 * todigit (last gs) + todigit (gs ! j1) + 2, Right)
            else if j = length gs - 1 then (1, Stay)
            else (gs ! j, Stay))"
        using that(3) by simp
      then have "cmd_bindec j1 j2 gs [.] j =
          (if j = j1 then gs ! j
            else if j = j2 then 2 * todigit (last gs) + todigit (gs ! j1) + 2
            else if j = length gs - 1 then 1
            else gs ! j)"
        by simp
      moreover have "last gs < G"
        using that assms
        by (metis add_lessD1 diff_less last_conv_nth length_greater_0_conv less_numeral_extra(1)
          less_numeral_extra(4) list.size(3) plus_1_eq_Suc)
      ultimately show ?thesis
        using that assms by simp
    qed
  qed
  show "cmd_bindec j1 j2 gs [.] 0 = gs ! 0" if "length gs = Suc k" "0 < Suc k" for gs
  proof (cases "last gs = 1")
    case True
    moreover have "0 < length gs" "0 \<noteq> length gs - 1"
      using that j_less by simp_all
    ultimately show ?thesis
      using cmd_bindec_def by simp
  next
    case False
    moreover have "0 < length gs" "0 \<noteq> j2" "0 \<noteq> length gs - 1"
      using that j_gt j_less by simp_all
    ultimately show ?thesis
      using cmd_bindec_def by simp
  qed
  show "\<And>gs. length gs = Suc k \<Longrightarrow> [*] (cmd_bindec j1 j2 gs) \<le> 1"
    using cmd_bindec_def by simp
qed

lemma tm_bindec_tm: "G \<ge> 6 \<Longrightarrow> turing_machine (Suc k) G (tm_bindec j1 j2)"
  unfolding tm_bindec_def using j_less(2) j_gt turing_command_bindec cmd_bindec_def by auto

context
  fixes tps :: "tape list" and zs :: "symbol list"
  assumes j1_neq: "j1 \<noteq> j2"
    and lentps: "Suc k = length tps"
    and bs: "bit_symbols zs"
begin

lemma sem_cmd_bindec_gt:
  assumes "tps ! j1 = (\<lfloor>zs\<rfloor>, i)"
    and "i > length zs"
  shows "sem (cmd_bindec j1 j2) (0, tps) = (1, tps)"
proof (rule semI)
  show "proper_command (Suc k) (cmd_bindec j1 j2)"
    using cmd_bindec_def by simp
  show "length tps = Suc k"
    using lentps by simp
  show "length tps = Suc k"
    using lentps by simp
  have "read tps ! j1 = \<box>"
    using assms by (metis contents_outofbounds fst_conv j_less(1) lentps less_Suc_eq snd_conv tapes_at_read')
  moreover from this show "fst (cmd_bindec j1 j2 (read tps)) = 1"
    by (simp add: cmd_bindec_def)
  ultimately show "\<And>j. j < Suc k \<Longrightarrow> act (cmd_bindec j1 j2 (read tps) [!] j) (tps ! j) = tps ! j"
    using assms cmd_bindec_def act_Stay lentps read_length by simp
qed

lemma sem_cmd_bindec_1:
  assumes "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, i)"
    and "i > 0"
    and "i \<le> length zs"
    and "tps' = tps [j1 := tps ! j1 |+| 1, k := \<lceil>todigit (tps :.: j1) + 2\<rceil>]"
  shows "sem (cmd_bindec j1 j2) (0, tps) = (0, tps')"
proof (rule semI)
  show "proper_command (Suc k) (cmd_bindec j1 j2)"
    using cmd_bindec_def by simp
  show "length tps = Suc k"
    using lentps by simp
  show "length tps' = Suc k"
    using lentps assms(5) by simp
  have read: "read tps ! j1 \<noteq> \<box>"
    using assms(2,3,4) bs j_less(1) tapes_at_read'[of j1 tps] contents_inbounds[OF assms(3,4)] lentps
       proper_symbols_ne0[OF proper_bit_symbols[OF bs]]
    by (metis One_nat_def Suc_less_eq Suc_pred fst_conv le_imp_less_Suc less_SucI snd_eqD)
  then show "fst (cmd_bindec j1 j2 (read tps)) = 0"
    using cmd_bindec_def by simp
  show "act (cmd_bindec j1 j2 (read tps) [!] j) (tps ! j) = tps' ! j"
    if "j < Suc k" for j
  proof -
    let ?rs = "read tps"
    have "last ?rs = 1"
      using assms(1) lentps onesie_read read_length tapes_at_read'
      by (metis (mono_tags, lifting) last_length lessI)
    then have *: "snd (cmd_bindec j1 j2 ?rs) = map (\<lambda>i.
        if i = j1 then (?rs ! i, Right)
        else if i = j2 then (?rs ! i, Stay)
        else if i = length ?rs - 1 then (if ?rs ! j1 = \<one> then \<one> else \<zero>, Stay)
        else (?rs ! i, Stay)) [0..<length ?rs]"
      using read cmd_bindec_def by simp
    have "length ?rs = Suc k"
      by (simp add: lentps read_length)
    then have len: "j < length ?rs"
      using that by simp
    have k: "k = length ?rs - 1"
      by (simp add: \<open>length ?rs = Suc k\<close>)
    consider "j = j1" | "j \<noteq> j1 \<and> j = j2" | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j = k" | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j \<noteq> k"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then have "cmd_bindec j1 j2 ?rs [!] j = (?rs ! j1, Right)"
        using * len by simp
      then show ?thesis
        using act_Right 1 assms(5) j_less(1) lentps by simp
    next
      case 2
      then have "cmd_bindec j1 j2 ?rs [!] j = (?rs ! j2, Stay)"
        using * len by simp
      then show ?thesis
        using 2 act_Stay assms(5) j_less(2) lentps by simp
    next
      case 3
      then have "cmd_bindec j1 j2 ?rs [!] j = (todigit (?rs ! j1) + 2, Stay)"
        using k * len by simp
      then show ?thesis
        using 3 assms(1,5) act_onesie j_less(1) lentps tapes_at_read'
        by (metis length_list_update less_Suc_eq nth_list_update)
    next
      case 4
      then have "cmd_bindec j1 j2 ?rs [!] j = (?rs ! j, Stay)"
        using k * len that by simp
      then show ?thesis
        using 4 act_Stay assms(5) lentps that by simp
    qed
  qed
qed

lemma sem_cmd_bindec_23:
  assumes "tps ! k = \<lceil>s\<rceil>"
    and "s = \<zero> \<or> s = \<one>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, i)"
    and "i > 0"
    and "i \<le> length zs"
    and "tps' = tps
      [j1 := tps ! j1 |+| 1,
       j2 := tps ! j2 |:=| decsym s (tps :.: j1) |+| 1,
       k := \<lceil>\<triangleright>\<rceil>]"
  shows "sem (cmd_bindec j1 j2) (0, tps) = (0, tps')"
proof (rule semI)
  show "proper_command (Suc k) (cmd_bindec j1 j2)"
    using cmd_bindec_def by simp
  show "length tps = Suc k"
    using lentps by simp
  show "length tps' = Suc k"
    using lentps assms(6) by simp
  have read: "read tps ! j1 \<noteq> \<box>"
    using assms(3-5) bs tapes_at_read'[of j1 tps] contents_inbounds[OF assms(4,5)] lentps
    by (metis One_nat_def Suc_less_eq Suc_pred fst_conv j_less(1) le_imp_less_Suc
      less_imp_le_nat not_one_less_zero proper_bit_symbols snd_conv)
  show "fst (cmd_bindec j1 j2 (read tps)) = 0"
    using read cmd_bindec_def by simp
  show "act (cmd_bindec j1 j2 (read tps) [!] j) (tps ! j) = tps' ! j"
    if "j < Suc k" for j
  proof -
    let ?rs = "read tps"
    have "last ?rs \<noteq> 1"
      using assms(1,2) lentps onesie_read read_length tapes_at_read'
      by (metis Suc_1 diff_Suc_1 last_conv_nth lessI list.size(3) n_not_Suc_n numeral_One
        numeral_eq_iff old.nat.distinct(1) semiring_norm(86))
    then have *: "snd (cmd_bindec j1 j2 ?rs) = map (\<lambda>i.
        if i = j1 then (?rs ! i, Right)
        else if i = j2 then (2 * todigit (last ?rs) + todigit (?rs ! j1) + 2, Right)
        else if i = length ?rs - 1 then (1, Stay)
        else (?rs ! i, Stay)) [0..<length ?rs]"
      using read cmd_bindec_def by simp
    have lenrs: "length ?rs = Suc k"
      by (simp add: lentps read_length)
    then have len: "j < length ?rs"
      using that by simp
    have k: "k = length ?rs - 1"
      by (simp add: lenrs)
    consider "j = j1" | "j \<noteq> j1 \<and> j = j2" | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j = k" | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j \<noteq> k"
      by auto
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using * len act_Right assms(6) j_less(1) j1_neq lentps by simp
    next
      case 2
      then have "cmd_bindec j1 j2 ?rs [!] j = (2 * todigit (last ?rs) + todigit (?rs ! j1) + 2, Right)"
        using * len by simp
      moreover have "last ?rs = s"
        using assms(1,2) lenrs k onesie_read tapes_at_read'
        by (metis last_conv_nth length_0_conv lentps lessI old.nat.distinct(1))
      moreover have "?rs ! j1 = tps :.: j1"
        using j_less(1) lentps tapes_at_read' by simp
      ultimately show ?thesis
        using 2 assms(6) act_Right' j_less lentps by simp
    next
      case 3
      then show ?thesis
        using * len k act_onesie assms(1,6) lentps by simp
    next
      case 4
      then have "cmd_bindec j1 j2 ?rs [!] j = (?rs ! j, Stay)"
        using k * len by simp
      then show ?thesis
        using 4 act_Stay assms(6) lentps that by simp
    qed
  qed
qed

end  (* tps zs *)

lemma transits_tm_bindec:
  fixes tps :: "tape list" and zs :: "symbol list"
  assumes j1_neq: "j1 \<noteq> j2"
    and j1j2: "0 < j2" "j1 < k" "j2 < k"
    and lentps: "Suc k = length tps"
    and bs: "bit_symbols zs"
  assumes "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, 2 * i + 1)"
    and "tps ! j2 = (\<lfloor>bindecode (take (2 * i) zs)\<rfloor>, Suc i)"
    and "i < length zs div 2"
    and "tps' = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * (Suc i) + 1),
       j2 := (\<lfloor>bindecode (take (2 * Suc i) zs)\<rfloor>, Suc (Suc i))]"
  shows "transits (tm_bindec j1 j2) (0, tps) 2 (0, tps')"
proof -
  define tps1 where "tps1 = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * i + 2),
       k := \<lceil>todigit (tps :.: j1) + 2\<rceil>]"
  let ?i = "2 * i + 1"
  let ?M = "tm_bindec j1 j2"
  have ilen: "?i < length zs"
    using assms(10) by simp
  have "exe ?M (0, tps) = sem (cmd_bindec j1 j2) (0, tps)"
    using tm_bindec_def exe_lt_length by simp
  also have "... =
      (if ?i \<le> length zs then 0 else 1,
       tps[j1 := tps ! j1 |+| 1, k := \<lceil>todigit (tps :.: j1) + 2\<rceil>])"
      using ilen bs assms(7,8) sem_cmd_bindec_1 j1_neq lentps by simp
  also have "... = (0, tps[j1 := tps ! j1 |+| 1, k := \<lceil>todigit (tps :.: j1) + 2\<rceil>])"
    using ilen by simp
  also have "... = (0, tps1)"
    using tps1_def assms by simp
  finally have step1: "exe ?M (0, tps) = (0, tps1)" .

  let ?s = "tps1 :.: k"
  have "tps :.: j1 = zs ! (2 * i)"
    using assms(8) ilen by simp
  then have "?s = todigit (zs ! (2 * i)) + 2"
    using tps1_def lentps by simp
  then have "?s = zs ! (2 * i)"
    using ilen bs by (smt (z3) One_nat_def Suc_1 add_2_eq_Suc' add_lessD1 numeral_3_eq_3)
  moreover have "tps1 :.: j1 = zs ! ?i"
    using tps1_def ilen lentps j1j2 by simp
  ultimately have *: "decsym ?s (tps1 :.: j1) = decsym (zs ! (2*i)) (zs ! (Suc (2*i)))"
    by simp

  have "exe ?M (0, tps1) = sem (cmd_bindec j1 j2) (0, tps1)"
    using tm_bindec_def exe_lt_length by simp
  also have "... =
    (if Suc ?i \<le> length zs then 0 else 1,
     tps1[j1 := tps1 ! j1 |+| 1, j2 := tps1 ! j2 |:=| 2 * todigit ?s + todigit (tps1 :.: j1) + 2 |+| 1, k := \<lceil>\<triangleright>\<rceil>])"
  proof -
    have 1: "tps1 ! k = \<lceil>?s\<rceil>"
      using tps1_def lentps by simp
    have 2: "?s = 2 \<or> ?s = 3"
      using tps1_def lentps by simp
    have 3: "tps1 ! j1 = (\<lfloor>zs\<rfloor>, Suc ?i)"
      using tps1_def lentps Suc_1 add_Suc_right j_less(1) less_Suc_eq nat_neq_iff nth_list_update_eq nth_list_update_neq
      by simp
    have 4: "Suc ?i > 0"
      by simp
    have 5: "Suc k = length tps1"
      by (simp add: lentps tps1_def)
    show ?thesis
      using ilen sem_cmd_bindec_23[of tps1 zs ?s "Suc ?i", OF j1_neq 5 bs 1 2 3 4] by simp
  qed
  also have "... =
    (0, tps1[j1 := tps1 ! j1 |+| 1, j2 := tps1 ! j2 |:=| decsym ?s (tps1 :.: j1) |+| 1, k := \<lceil>\<triangleright>\<rceil>])"
    using assms(10) length_binencode by simp
  also have "... =
    (0, tps1[j1 := tps1 ! j1 |+| 1, j2 := tps1 ! j2 |:=| decsym (zs ! (2*i)) (zs ! (Suc (2*i))) |+| 1, k := \<lceil>\<triangleright>\<rceil>])"
      (is "_ = (0, ?tps)")
    using * by simp
  also have "... = (0, tps')"
  proof -
    have len': "length tps' = Suc k"
      using assms lentps by simp
    have len1: "length tps1 = Suc k"
      using assms lentps tps1_def by simp
    have 1: "?tps ! k = tps' ! k"
      using assms(7,11) by (simp add: j_less(1) j_less(2) len1 nat_neq_iff)
    have 2: "?tps ! j1 = tps' ! j1"
      using assms(11) j1_neq j_less(1) lentps tps1_def by simp
    have "?tps ! j2 = tps1 ! j2 |:=| decsym (zs ! (2*i)) (zs ! (Suc (2*i))) |+| 1"
      by (simp add: j_less(2) len1 less_Suc_eq nat_neq_iff)
    also have "... = tps ! j2 |:=| decsym (zs ! (2*i)) (zs ! (Suc (2*i))) |+| 1"
      using tps1_def j1_neq j_less(2) len1 by force
    also have "... = (\<lfloor>bindecode (take (2 * i) zs)\<rfloor>, Suc i) |:=| decsym (zs ! (2*i)) (zs ! (Suc (2*i))) |+| 1"
      using assms(9) j1_neq j_less(2) len1 tps1_def by simp
    also have "... = (\<lfloor>bindecode (take (2 * i) zs)\<rfloor>(Suc i := decsym (zs ! (2*i)) (zs ! (Suc (2*i)))), Suc (Suc i))"
      by simp
    also have "... = (\<lfloor>bindecode (take (2 * i) zs) @ [decsym (zs ! (2*i)) (zs ! (Suc (2*i)))]\<rfloor>, Suc (Suc i))"
      using contents_snoc[of "bindecode (take (2 * i) zs)"] ilen length_bindecode
    proof -
      have "length (bindecode (take (2 * i) zs)) = i"
        using ilen length_bindecode by simp
      then show ?thesis
        using contents_snoc[of "bindecode (take (2 * i) zs)"] by simp
    qed
    also have "... = (\<lfloor>bindecode (take (2 * Suc i) zs)\<rfloor>, Suc (Suc i))"
      using bindecode_take_snoc ilen by simp
    also have "... = tps' ! j2"
      by (metis assms(11) j_less(2) length_list_update lentps less_Suc_eq nth_list_update_eq)
    finally have "?tps ! j2 = tps' ! j2" .
    then show ?thesis
      using 1 2 assms(11) tps1_def by (smt (z3) list_update_id list_update_overwrite list_update_swap)
  qed
  finally have "exe ?M (0, tps1) = (0, tps')" .
  then have "execute ?M (0, tps) 2 = (0, tps')"
    using step1 by (simp add: numeral_2_eq_2)
  then show "transits (tm_bindec j1 j2) (0, tps) 2 (0, tps')"
    using execute_imp_transits by blast
qed

context
  fixes tps :: "tape list" and zs :: "symbol list"
  assumes j1_neq: "j1 \<noteq> j2"
    and j1j2: "0 < j2" "j1 < k" "j2 < k"
    and lentps: "Suc k = length tps"
    and bs: "bit_symbols zs"
begin

lemma transits_tm_bindec':
  assumes "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    and "i \<le> length zs div 2"
    and "tps' = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * i + 1),
       j2 := (\<lfloor>bindecode (take (2 * i) zs)\<rfloor>, Suc i)]"
  shows "transits (tm_bindec j1 j2) (0, tps) (2 * i) (0, tps')"
  using assms(4,5)
proof (induction i arbitrary: tps')
  case 0
  then show ?case
    using assms(2,3) by (metis One_nat_def add.commute div_mult_self1_is_m execute.simps(1)
      le_numeral_extra(3) length_bindecode length_greater_0_conv list.size(3) list_update_id
       mult_0_right plus_1_eq_Suc take0 transits_def zero_less_numeral)
next
  case (Suc i)
  define tpsi where "tpsi = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * i + 1),
       j2 := (\<lfloor>bindecode (take (2*i) zs)\<rfloor>, Suc i)]"
  then have "transits (tm_bindec j1 j2) (0, tps) (2 * i) (0, tpsi)"
    using Suc by simp
  moreover have "transits (tm_bindec j1 j2) (0, tpsi) 2 (0, tps')"
  proof -
    have 1: "tpsi ! k = \<lceil>\<triangleright>\<rceil>"
      using tpsi_def by (simp add: assms(1) j_less(1) j_less(2) less_not_refl3)
    have 2: "tpsi ! j1 = (\<lfloor>zs\<rfloor>, 2 * i + 1)"
      using tpsi_def by (metis j1_neq j_less(1) lentps less_Suc_eq nth_list_update_eq nth_list_update_neq)
    have 3: "tpsi ! j2 = (\<lfloor>bindecode (take (2 * i) zs)\<rfloor>, Suc i)"
      using tpsi_def by (metis j_less(2) length_list_update lentps less_Suc_eq nth_list_update_eq)
    have 4: "i < length zs div 2"
      using Suc by simp
    have 5: "tps' = tpsi
      [j1 := (\<lfloor>zs\<rfloor>, 2 * (Suc i) + 1),
       j2 := (\<lfloor>bindecode (take (2 * Suc i) zs)\<rfloor>, Suc (Suc i))]"
      using Suc tpsi_def by (metis (no_types, opaque_lifting) list_update_overwrite list_update_swap)
    have 6: "Suc k = length tpsi"
      using tpsi_def lentps by simp
    show ?thesis
      using transits_tm_bindec[OF j1_neq j1j2 6 bs 1 2 3 4 5] .
  qed
  ultimately show "transits (tm_bindec j1 j2) (0, tps) (2 * (Suc i)) (0, tps')"
    using transits_additive by fastforce
qed

corollary transits_tm_bindec'':
  assumes "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    and "l = length zs div 2"
    and "tps' = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * l + 1),
       j2 := (\<lfloor>bindecode (take (2 * l) zs)\<rfloor>, Suc l)]"
  shows "transits (tm_bindec j1 j2) (0, tps) (2 * l) (0, tps')"
  using assms transits_tm_bindec' by simp

text \<open>In case the input is of odd length, that is, malformed:\<close>

lemma transforms_tm_bindec_odd:
  assumes "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    and "tps' = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * l + 2),
       j2 := (\<lfloor>bindecode zs\<rfloor>, Suc l),
       k := \<lceil>todigit (last zs) + 2\<rceil>]"
    and "l = length zs div 2"
    and "Suc (2 * l) = length zs"
  shows "transforms (tm_bindec j1 j2) tps (2 * l + 2) tps'"
proof -
  let ?ys = "bindecode (take (2 * l) zs)"
  let ?i = "2 * l + 1"
  let ?M = "tm_bindec j1 j2"
  have ys: "?ys = bindecode zs"
    using bindecode_odd assms(6) by (metis Suc_eq_plus1)
  have "zs \<noteq> []"
    using assms(6) by auto
  define tps1 where "tps1 = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * l + 1),
       j2 := (\<lfloor>?ys\<rfloor>, Suc l)]"
  define tps2 where "tps2 = tps
    [j1 := (\<lfloor>zs\<rfloor>, 2 * l + 2),
     j2 := (\<lfloor>bindecode zs\<rfloor>, Suc l),
     k := \<lceil>todigit (tps1 :.: j1) + 2\<rceil>]"
  have "transits ?M (0, tps) (2 * l) (0, tps1)"
    using tps1_def assms transits_tm_bindec'' by simp
  moreover have "execute ?M (0, tps1) 1 = (0, tps2)"
  proof -
    have "execute ?M (0, tps1) 1 = exe ?M (0, tps1)"
      by simp
    also have "... = sem (cmd_bindec j1 j2) (0, tps1)"
      using exe_lt_length tm_bindec_def by simp
    also have "... = (0, tps1[j1 := tps1 ! j1 |+| 1, k := \<lceil>todigit (tps1 :.: j1) + 2\<rceil>])"
      (is "_ = (0, ?tps)")
    proof -
      have "tps1 ! j1 = (\<lfloor>zs\<rfloor>, ?i)"
        using lentps tps1_def j1_neq j_less by simp
      moreover have "?i > 0"
        by simp
      moreover have "tps1 ! k = tps ! k"
        using tps1_def by (simp add: j_less(1) j_less(2) nat_neq_iff)
      moreover have "?i \<le> length zs"
        by (simp add: assms(6))
      ultimately have "sem (cmd_bindec j1 j2) (0, tps1) = (0, ?tps)"
        using sem_cmd_bindec_1 assms(1,4) bit_symbols_binencode bs j1_neq lentps tps1_def
        by (metis length_list_update)
      then show ?thesis
        by simp
    qed
    also have "... = (0, tps2)"
    proof -
      have "tps2 ! j1 = ?tps ! j1"
        using tps1_def tps2_def j1_neq j_less(1) lentps by simp
      moreover have "tps2 ! j2 = ?tps ! j2"
        using tps1_def tps2_def j1_neq j_less(2) lentps ys by simp
      ultimately have "tps2 = ?tps"
        using tps2_def tps1_def j_less(1) lentps
        by (smt (z3) list_update_id list_update_overwrite list_update_swap)
      then show ?thesis
        by simp
    qed
    finally show ?thesis .
  qed
  ultimately have "transits ?M (0, tps) (2 * l + 1) (0, tps2)"
    using execute_imp_transits transits_additive by blast
  moreover have "execute ?M (0, tps2) 1 = (1, tps')"
  proof -
    have "execute ?M (0, tps2) 1 = exe ?M (0, tps2)"
      by simp
    also have "... = sem (cmd_bindec j1 j2) (0, tps2)"
      using exe_lt_length tm_bindec_def by simp
    also have "... = (1, tps2)"
    proof -
      have "2 * l + 2 > length zs"
        using assms(5,6) by simp
      moreover have "tps2 ! j1 = (\<lfloor>zs\<rfloor>, 2 * l + 2)"
        using tps2_def j1_neq j_less(1) lentps by simp
      ultimately show ?thesis
        using sem_cmd_bindec_gt[of tps2 zs "2 * l + 2"]
        by (metis bs j1_neq length_list_update lentps tps2_def)
    qed
    moreover have "tps2 = tps'"
    proof -
      have "tps1 :.: j1 = last zs"
        using tps1_def assms \<open>zs \<noteq> []\<close> contents_inbounds
        by (metis Suc_leI add.commute fst_conv j1_neq j_less(1) last_conv_nth lentps less_Suc_eq
          nth_list_update_eq nth_list_update_neq plus_1_eq_Suc snd_conv zero_less_Suc)
      then show ?thesis
        using tps2_def assms(4) by simp
    qed
    ultimately show ?thesis
      by simp
  qed
  ultimately have "transits ?M (0, tps) (2 * l + 2) (1, tps')"
    using execute_imp_transits transits_additive by (smt (z3) ab_semigroup_add_class.add_ac(1) nat_1_add_1)
  then show "transforms (tm_bindec j1 j2) tps (2 * l + 2) tps'"
    using transforms_def tm_bindec_def by simp
qed

text \<open>
In case the input is of even length, that is, properly encoded:
\<close>

lemma transforms_tm_bindec_even:
  assumes "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    and "tps' = tps
      [j1 := (\<lfloor>zs\<rfloor>, 2 * l + 1),
       j2 := (\<lfloor>bindecode zs\<rfloor>, Suc l)]"
    and "l = length zs div 2"
    and "2 * l = length zs"
  shows "transforms (tm_bindec j1 j2) tps (2 * l + 1) tps'"
proof -
  let ?ys = "bindecode (take (2 * l) zs)"
  let ?i = "2 * l + 1"
  let ?M = "tm_bindec j1 j2"
  have ys: "?ys = bindecode zs"
    using assms(6) by simp
  have "transits ?M (0, tps) (2 * l) (0, tps')"
    using assms transits_tm_bindec'' by simp
  moreover have "execute ?M (0, tps') 1 = (1, tps')"
  proof -
    have "execute ?M (0, tps') 1 = exe ?M (0, tps')"
      using assms(4) by simp
    also have "... = sem (cmd_bindec j1 j2) (0, tps')"
      using exe_lt_length tm_bindec_def by simp
    also have "... = (1, tps')"
    proof -
      have "tps' ! j1 = (\<lfloor>zs\<rfloor>, ?i)"
        using lentps assms(4) j1_neq j_less by simp
      moreover have "?i > length zs"
        using assms(6) by simp
      moreover have "tps' ! k = tps ! k"
        using assms(4) by (simp add: j_less(1) j_less(2) nat_neq_iff)
      ultimately have "sem (cmd_bindec j1 j2) (0, tps') = (1, tps')"
        using sem_cmd_bindec_gt assms(1,4) bit_symbols_binencode bs j1_neq lentps assms(4)
        by simp
      then show ?thesis
        by simp
    qed
    finally show ?thesis .
  qed
  ultimately have "transits ?M (0, tps) (2 * l + 1) (1, tps')"
    using execute_imp_transits transits_additive by blast
  then show "transforms (tm_bindec j1 j2) tps (2 * l + 1) tps'"
    using tm_bindec_def transforms_def by simp
qed

lemma transforms_tm_bindec:
  assumes "tps ! k = \<lceil>\<triangleright>\<rceil>"
    and "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
    and "tps' = tps
      [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
       j2 := (\<lfloor>bindecode zs\<rfloor>, Suc (length zs div 2)),
       k := \<lceil>if even (length zs) then 1 else (todigit (last zs) + 2)\<rceil>]"
  shows "transforms (tm_bindec j1 j2) tps (Suc (length zs)) tps'"
proof (cases "even (length zs)")
  case True
  then show ?thesis
    using transforms_tm_bindec_even[OF assms(1-3)] assms(1,4) j_less(1) j_less(2)
    by (smt (z3) Suc_eq_plus1 dvd_mult_div_cancel list_update_id list_update_swap nat_neq_iff)
next
  case False
  then show ?thesis
    using assms(4) transforms_tm_bindec_odd[OF assms(1-3)] by simp
qed

end  (* context tps zs *)

end  (* context j1 j2 k *)

text \<open>
Next we eliminate the memorization tape from @{const tm_bindec}.
\<close>

lemma transforms_cartesian_bindec:
  assumes "G \<ge> (6 :: nat)"
  assumes "j1 \<noteq> j2"
    and j1j2: "0 < j2" "j1 < k" "j2 < k"
    and "k = length tps"
    and "bit_symbols zs"
  assumes "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
  assumes "t = Suc (length zs)"
    and "tps' = tps
      [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
       j2 := (\<lfloor>bindecode zs\<rfloor>, Suc (length zs div 2))]"
  shows "transforms (cartesian (tm_bindec j1 j2) 4) tps t tps'"
proof (rule cartesian_transforms_onesie)
  show "turing_machine (Suc k) G (tm_bindec j1 j2)"
    using tm_bindec_tm assms(1) j1j2 by simp
  show "immobile (tm_bindec j1 j2) k (Suc k)"
  proof (standard+)
    fix q :: nat and rs :: "symbol list"
    assume "q < length (tm_bindec j1 j2)" "length rs = Suc k"
    then have *: "tm_bindec j1 j2 ! q = cmd_bindec j1 j2"
      using tm_bindec_def by simp
    moreover have "cmd_bindec j1 j2 rs [~] k = Stay"
      using cmd_bindec_def `length rs = Suc k` j1j2
      by (smt (verit, best) add_diff_inverse_nat diff_zero length_upt lessI less_nat_zero_code
        nat_neq_iff nth_map nth_upt prod.sel(2))
    ultimately show "(tm_bindec j1 j2 ! q) rs [~] k = Stay"
      using * by simp
  qed
  show "2 \<le> k"
    using j1j2 by linarith
  show "(1::nat) < 4"
    by simp
  show "length tps = k"
    using assms(3,6) by simp
  show "bounded_write (tm_bindec j1 j2) k 4"
  proof -
    { fix q :: nat and rs :: "symbol list"
      assume q: "q < length (tm_bindec j1 j2)" and rs: "length rs = Suc k"
      then have "tm_bindec j1 j2 ! q = cmd_bindec j1 j2"
        using tm_bindec_def by simp
      have "cmd_bindec j1 j2 rs [.] (length rs - 1) < 4 \<or> fst (cmd_bindec j1 j2 rs) = 1"
      proof (cases "rs ! j1 = 0")
        case True
        then show ?thesis
          using cmd_bindec_def by simp
      next
        case else: False
        show ?thesis
        proof (cases "last rs = 1")
          case True
          then have "snd (cmd_bindec j1 j2 rs) = map (\<lambda>i.
                  if i = j1 then (rs ! i, Right)
                  else if i = j2 then (rs ! i, Stay)
                  else if i = length rs - 1 then (todigit (rs ! j1) + 2, Stay)
                  else (rs ! i, Stay)) [0..<length rs]"
            using else cmd_bindec_def by simp
          then have "snd (cmd_bindec j1 j2 rs) ! k = (todigit (rs ! j1) + 2, Stay)"
            using rs j1j2
            by (smt (z3) add.left_neutral diff_Suc_1 diff_zero length_upt lessI nat_neq_iff nth_map nth_upt)
          then show ?thesis
            using rs by simp
        next
          case False
          then have "snd (cmd_bindec j1 j2 rs) = map (\<lambda>i.
                if i = j1 then (rs ! i, Right)
                else if i = j2 then (2 * todigit (last rs) + todigit (rs ! j1) + 2, Right)
                else if i = length rs - 1 then (1, Stay)
                else (rs ! i, Stay)) [0..<length rs]"
            using else cmd_bindec_def by simp
          then have "snd (cmd_bindec j1 j2 rs) ! k = (1, Stay)"
            using rs j1j2
            by (smt (z3) add.left_neutral diff_Suc_1 diff_zero length_upt lessI nat_neq_iff nth_map nth_upt)
          then show ?thesis
            using rs by simp
        qed
      qed
    }
    then show ?thesis
      using bounded_write_def tm_bindec_def by simp
  qed
  let ?c = "if even (length zs) then \<triangleright> else (todigit (last zs) + 2)"
  show "transforms (tm_bindec j1 j2) (tps @ [\<lceil>\<triangleright>\<rceil>]) t (tps' @ [\<lceil>?c\<rceil>])"
    (is "transforms _ ?tps t ?tps'")
  proof -
    have "?tps ! k = \<lceil>\<triangleright>\<rceil>"
      by (simp add: assms(6))
    moreover have "?tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
      by (metis assms(6) assms(8) j1j2(2) nth_append)
    moreover have "?tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
      by (metis assms(6) assms(9) j1j2(3) nth_append)
    moreover have "?tps' = ?tps
      [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
       j2 := (\<lfloor>bindecode zs\<rfloor>, Suc (length zs div 2)),
       k := \<lceil>?c\<rceil>]"
      by (metis (no_types, lifting) assms(6,11) j1j2(2,3) length_list_update list_update_append1 list_update_length)
    ultimately show ?thesis
      using transforms_tm_bindec[of j1 "k" j2 ?tps zs ?tps'] assms by simp
  qed
qed

text \<open>
The next Turing machine decodes a bit symbol sequence given on tape $j_1$ into a
quaternary symbol sequence output to tape $j_2$. It executes the previous TM
followed by carriage returns on the tapes $j_1$ and $j_2$.
\<close>

definition tm_bindecode :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_bindecode j1 j2 \<equiv> cartesian (tm_bindec j1 j2) 4 ;; tm_cr j1 ;; tm_cr j2"

lemma tm_bindecode_tm:
  fixes j1 j2 :: tapeidx and G k :: nat
  assumes "G \<ge> 6" and "j1 < k" and "j2 < k" and "0 < j2" and "j1 \<noteq> j2"
  shows "turing_machine k G (tm_bindecode j1 j2)"
  using assms tm_bindec_tm tm_bindecode_def cartesian_tm tm_cr_tm by simp

locale turing_machine_bindecode =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> cartesian (tm_bindec j1 j2) 4"
definition "tm2 \<equiv> tm1 ;; tm_cr j1"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"

lemma tm3_eq_tm_bindecode: "tm3 = tm_bindecode j1 j2"
  using tm1_def tm2_def tm3_def tm_bindecode_def by simp

context
  fixes tps0 :: "tape list" and zs :: "symbol list" and k :: nat
  assumes jk: "j1 < k" "j2 < k" "0 < j2" "j1 \<noteq> j2" "k = length tps0"
  assumes zs: "bit_symbols zs"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>[]\<rfloor>, 1)"
begin

definition "tps1 \<equiv> tps0
  [j1 := (\<lfloor>zs\<rfloor>, Suc (length zs)),
   j2 := (\<lfloor>bindecode zs\<rfloor>, Suc (length zs div 2))]"

lemma tm1 [transforms_intros]:
  assumes "t = Suc (length zs)"
  shows "transforms tm1 tps0 t tps1"
  unfolding tm1_def
  using transforms_cartesian_bindec assms jk tps0 zs tps1_def by blast

definition "tps2 \<equiv> tps0
  [j2 := (\<lfloor>bindecode zs\<rfloor>, Suc (length zs div 2))]"

lemma tm2 [transforms_intros]:
  assumes "t = 2 * length zs + 4"
  shows "transforms tm2 tps0 t tps2"
  unfolding tm2_def
proof (tform tps: assms)
  show "j1 < length tps1"
    using jk tps1_def by simp
  show "clean_tape (tps1 ! j1)"
    using jk zs clean_contents_proper tps1_def by fastforce
  show "tps2 = tps1[j1 := tps1 ! j1 |#=| 1]"
    using tps0 jk tps2_def tps1_def
    by (metis (no_types, lifting) fst_conv list_update_id list_update_overwrite list_update_swap nth_list_update_eq nth_list_update_neq)
  show "t = Suc (length zs) + (tps1 :#: j1 + 2)"
    using assms(1) jk tps1_def by simp
qed

definition "tps3 \<equiv> tps0
  [j2 := (\<lfloor>bindecode zs\<rfloor>, 1)]"

lemma tm3:
  assumes "t = 2 * length zs + 7 + length zs div 2"
  shows "transforms tm3 tps0 t tps3"
  unfolding tm3_def
proof (tform tps: jk tps2_def tps3_def assms)
  show "clean_tape (tps2 ! j2)"
    using jk bindecode_at tps2_def by simp
qed

lemma tm3':
  assumes "t = 7 + 3 * length zs"
  shows "transforms tm3 tps0 t tps3"
proof -
  have "7 + 3 * length zs \<ge> 2 * length zs + 7 + length zs div 2"
    by simp
  then show ?thesis
    using transforms_monotone tm3 assms tps3_def by simp
qed

end  (* context tps zs *)

end  (* locale turing_machine_bindecode *)

lemma transforms_tm_bindecodeI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps :: "tape list" and zs :: "symbol list" and k ttt :: nat
  assumes "j1 < k" and "j2 < k" and "0 < j2" and "j1 \<noteq> j2" and "k = length tps"
    and "bit_symbols zs"
  assumes
    "tps ! j1 = (\<lfloor>zs\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>[]\<rfloor>, 1)"
  assumes "ttt = 7 + 3 * length zs"
  assumes "tps' = tps
    [j2 := (\<lfloor>bindecode zs\<rfloor>, 1)]"
  shows "transforms (tm_bindecode j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_bindecode j1 j2 .
  show ?thesis
    using loc.tm3_eq_tm_bindecode loc.tm3' loc.tps3_def assms by simp
qed

end
