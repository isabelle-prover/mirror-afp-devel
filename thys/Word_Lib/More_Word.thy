
section \<open>Lemmas on words\<close>

theory More_Word
  imports
    "HOL-Library.Word"
    More_Divides
begin

lemma Suc_0_lt_2p_len_of: "Suc 0 < 2 ^ LENGTH('a :: len)"
  by (metis One_nat_def len_gt_0 lessI numeral_2_eq_2 one_less_power)

lemma unat_p2: "n < LENGTH('a :: len) \<Longrightarrow> unat (2 ^ n :: 'a word) = 2 ^ n"
  by transfer simp

lemma word_div_lt_eq_0:
  "x < y \<Longrightarrow> x div y = 0" for x :: "'a :: len word"
  by transfer simp

lemma word_div_eq_1_iff: "n div m = 1 \<longleftrightarrow> n \<ge> m \<and> unat n < 2 * unat (m :: 'a :: len word)"
  apply (simp only: word_arith_nat_defs word_le_nat_alt word_of_nat_eq_iff flip: nat_div_eq_Suc_0_iff)
  apply (simp flip: unat_div unsigned_take_bit_eq)
  done

end
