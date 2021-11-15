theory Lib_Word_toString
imports Lib_Numbers_toString
        Word_Lib.Word_Lemmas
begin

context unique_euclidean_semiring_numeral
begin

lemma exp_estimate [simp]:
  \<open>numeral Num.One \<le> 2 ^ n\<close>  (is \<open>?P1\<close>)
  \<open>numeral Num.One < 2 ^ n \<longleftrightarrow> 1 \<le> n\<close>  (is \<open>?P2\<close>)
  \<open>numeral (Num.Bit0 k) \<le> 2 ^ n \<longleftrightarrow> 1 \<le> n \<and> numeral k \<le> 2 ^ (n - 1)\<close>  (is \<open>?P3\<close>)
  \<open>numeral (Num.Bit0 k) < 2 ^ n \<longleftrightarrow> 1 \<le> n \<and> numeral k < 2 ^ (n - 1)\<close>  (is \<open>?P4\<close>)
  \<open>numeral (Num.Bit1 k) \<le> 2 ^ n \<longleftrightarrow> 1 \<le> n \<and> numeral k < 2 ^ (n - 1)\<close>  (is \<open>?P5\<close>)
  \<open>numeral (Num.Bit1 k) < 2 ^ n \<longleftrightarrow> 1 \<le> n \<and> numeral k < 2 ^ (n - 1)\<close>  (is \<open>?P6\<close>)
proof -
  show ?P1
    by simp
  show ?P2
    using one_less_power power_eq_if by auto

  let ?K = \<open>numeral k :: nat\<close>

  define m where \<open>m = n - 1\<close>
  then consider \<open>n = 0\<close> | \<open>n = Suc m\<close>
    by (cases n) simp_all
  note Suc = this

  have \<open>2 * ?K \<le> 2 * 2 ^ m \<longleftrightarrow> ?K \<le> 2 ^ m\<close>
    by linarith
  then have \<open>of_nat (2 * ?K) \<le> of_nat (2 * 2 ^ m) \<longleftrightarrow> of_nat ?K \<le> of_nat (2 ^ m)\<close>
    by (simp only: of_nat_le_iff)
  then show ?P3
    by (auto intro: Suc)

  have \<open>2 * ?K < 2 * 2 ^ m \<longleftrightarrow> ?K < 2 ^ m\<close>
    by linarith
  then have \<open>of_nat (2 * ?K) < of_nat (2 * 2 ^ m) \<longleftrightarrow> of_nat ?K < of_nat (2 ^ m)\<close>
    by (simp only: of_nat_less_iff)
  then show ?P4
    by (auto intro: Suc)

  have \<open>Suc (2 * ?K) \<le> 2 * 2 ^ m \<longleftrightarrow> ?K < 2 ^ m\<close>
    by linarith
  then have \<open>of_nat (Suc (2 * ?K)) \<le> of_nat (2 * 2 ^ m) \<longleftrightarrow> of_nat ?K < of_nat (2 ^ m)\<close>
    by (simp only: of_nat_le_iff of_nat_less_iff)
  then show ?P5
    by (auto intro: Suc)

  have \<open>Suc (2 * ?K) < 2 * 2 ^ m \<longleftrightarrow> ?K < 2 ^ m\<close>
    by linarith
  then have \<open>of_nat (Suc (2 * ?K)) < of_nat (2 * 2 ^ m) \<longleftrightarrow> of_nat ?K < of_nat (2 ^ m)\<close>
    by (simp only: of_nat_less_iff)
  then show ?P6
    by (auto intro: Suc)

qed

end


section\<open>Printing Machine Words\<close>

(*imitation of http://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle*)
(*parameters:
    lc = lower-case
    w  = word to print*)
definition string_of_word_single :: "bool \<Rightarrow> 'a::len word \<Rightarrow> string" where
  "string_of_word_single lc w \<equiv>
    (if
       w < 10
     then
       [char_of (48 + unat w)]
     else if
       w < 36
     then
       [char_of ((if lc then 87 else 55) + unat w)]
     else
       undefined)"

text\<open>Example:\<close>
lemma "let word_upto = ((\<lambda> i j. map (of_nat \<circ> nat) [i .. j]) :: int \<Rightarrow> int \<Rightarrow> 32 word list)
       in map (string_of_word_single False) (word_upto 1 35) =
  [''1'', ''2'', ''3'', ''4'', ''5'', ''6'', ''7'', ''8'', ''9'',
   ''A'', ''B'', ''C'', ''D'', ''E'', ''F'', ''G'', ''H'', ''I'',
   ''J'', ''K'', ''L'', ''M'', ''N'', ''O'', ''P'', ''Q'', ''R'',
   ''S'', ''T'', ''U'', ''V'', ''W'', ''X'', ''Y'', ''Z'']" by eval

(* parameters: lowercase, base, minimum length - 1, to-be-serialized word *) 
function string_of_word :: "bool \<Rightarrow> ('a :: len) word \<Rightarrow> nat \<Rightarrow> ('a :: len) word \<Rightarrow> string" where
  "string_of_word lc base ml w =
    (if
       base < 2 \<or> LENGTH('a) < 2
     then
       undefined
     else if
       w < base \<and> ml = 0
     then
       string_of_word_single lc w
     else
       string_of_word lc base (ml - 1) (w div base) @ string_of_word_single lc (w mod base)
     )"
by pat_completeness auto

definition "hex_string_of_word l \<equiv> string_of_word True (16 :: ('a::len) word) l"
definition "hex_string_of_word0 \<equiv> hex_string_of_word 0"
(* be careful though, these functions only make sense with words > length 4.
   With 4 bits, base 16 is not representable. *)
definition "dec_string_of_word0 \<equiv> string_of_word True 10 0"

termination string_of_word
	apply(relation "measure (\<lambda>(a,b,c,d). unat d + c)")
	 apply(rule wf_measure)
	apply(subst in_measure)
	apply(clarsimp)
	subgoal for base ml n
    apply(case_tac "ml \<noteq> 0")
     apply(simp add: less_eq_Suc_le unat_div)
    apply(simp)
    apply(subgoal_tac "(n div base) < n")
     apply(blast intro: unat_mono)
    apply(rule div_less_dividend_word)
     apply (auto simp add: not_less word_le_nat_alt)
  done
done

declare string_of_word.simps[simp del]

lemma "hex_string_of_word0 (0xdeadbeef42 :: 42 word) = ''deadbeef42''" by eval

lemma "hex_string_of_word 1 (0x1 :: 5 word) = ''01''" by eval
lemma "hex_string_of_word 8 (0xff::32 word) = ''0000000ff''" by eval

lemma "dec_string_of_word0 (8::32 word) = ''8''" by eval
lemma "dec_string_of_word0 (3::2 word) = ''11''" by eval
lemma "dec_string_of_word0 (-1::8 word) = ''255''" by eval

lemma string_of_word_single_atoi:
  "n < 10 \<Longrightarrow> string_of_word_single True n = [char_of (48 + unat n)]"
  by(simp add: string_of_word_single_def)

(*TODO: move!*)
lemma bintrunc_pos_eq: "x \<ge> 0 \<Longrightarrow> take_bit n x = x \<longleftrightarrow> x < 2^n" for x :: int
  by (simp add: take_bit_int_eq_self_iff)

(*The following lemma [symmetric] as [code_unfold] may give some cool speedup*)
lemma string_of_word_base_ten_zeropad:
  fixes w ::"'a::len word"
  assumes lena: "LENGTH('a) \<ge> 5" (*word must be long enough to encode 10 = 0xA*)
  shows "base = 10 \<Longrightarrow> zero = 0 \<Longrightarrow> string_of_word True base zero w = string_of_nat (unat w)"
proof(induction True base zero w rule: string_of_word.induct)
  case (1 base ml n)

  note  Word.word_less_no[simp del]
  note  Word.uint_bintrunc[simp del]

  define l where \<open>l = LENGTH('a) - 5\<close>
  with lena have l: \<open>LENGTH('a) = l + 5\<close>
    by simp

  have [simp]: \<open>take_bit LENGTH('a) (10 :: nat) = 10\<close>
    using lena by (auto simp add: take_bit_nat_eq_self_iff l Suc_lessI)

  have [simp]: \<open>take_bit LENGTH('a) (10 :: int) = 10\<close>
    using lena by (auto simp add: take_bit_int_eq_self_iff l)
      (smt (verit) zero_less_power)

  have unat_mod_ten: "unat (n mod 0xA) = unat n mod 10"
    by (simp add: nat_take_bit_eq unat_mod)
    
  have unat_div_ten: "(unat (n div 0xA)) = unat n div 10"
    by (simp add: nat_take_bit_eq unat_div)

  have n_less_ten_unat: "n < 0xA \<Longrightarrow> (unat n < 10)"
    by (simp add: unat_less_helper)

  have "0xA \<le> n \<Longrightarrow> 10 \<le> unat n" 
    by (simp add: nat_take_bit_eq word_le_nat_alt)

  hence n_less_ten_unat_not: "\<not> n < 0xA \<Longrightarrow> \<not> unat n < 10" by fastforce
  have not_wordlength_too_small: "\<not> LENGTH('a) < 2" using lena by fastforce
  have "2 \<le> (0xA::'a word)"
    by simp
  hence ten_not_less_two: "\<not> (0xA::'a word) < 2" by (simp add: Word.word_less_no Word.uint_bintrunc)
  with 1(2,3) have " \<not> (base < 2 \<or> LENGTH(32) < 2)"
    by(simp)
  with 1 not_wordlength_too_small have IH: "\<not> n < 0xA \<Longrightarrow> string_of_word True 0xA 0 (n div 0xA) = string_of_nat (unat (n div 0xA))"
    by(simp)
  show ?case
    apply(simp add: 1)
    apply(cases "n < 0xA")
     subgoal
     apply(subst(1) string_of_word.simps)
     apply(subst(1) string_of_nat.simps)
     apply(simp add: n_less_ten_unat)
       using lena apply(simp add: not_wordlength_too_small ten_not_less_two string_of_word_single_atoi)
       done
    using sym[OF IH] apply(simp)
    apply(subst(1) string_of_word.simps)
    apply(simp)
    apply(subst(1) string_of_nat.simps)
    apply(simp)
    apply (simp add: string_of_word_single_atoi Word.word_mod_less_divisor unat_div_ten unat_mod_ten)
    using \<open>10 \<le> n \<Longrightarrow> 10 \<le> unat n\<close> not_wordlength_too_small apply (auto simp add: not_less)
    done
qed

(*TODO: one for all words?*)
lemma dec_string_of_word0:
  "dec_string_of_word0 (w8:: 8 word) = string_of_nat (unat w8)"
  "dec_string_of_word0 (w16:: 16 word) = string_of_nat (unat w16)"
  "dec_string_of_word0 (w32:: 32 word) = string_of_nat (unat w32)"
  "dec_string_of_word0 (w64:: 64 word) = string_of_nat (unat w64)"
  "dec_string_of_word0 (w128:: 128 word) = string_of_nat (unat w128)"
  unfolding dec_string_of_word0_def
  using string_of_word_base_ten_zeropad by force+

end
