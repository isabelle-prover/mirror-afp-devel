
section \<open>Signed division on word\<close>

theory Signed_Division_Word
  imports "HOL-Library.Signed_Division" "HOL-Library.Word"
begin

instantiation word :: (len) signed_division
begin

lift_definition signed_divide_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k sdiv signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition signed_modulo_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k smod signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

instance ..

end

lemma sdiv_word_def [code]:
  \<open>v sdiv w = word_of_int (sint v sdiv sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma smod_word_def [code]:
  \<open>v smod w = word_of_int (sint v smod sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma sdiv_smod_id:
  \<open>(a sdiv b) * b + (a smod b) = a\<close>
  for a b :: \<open>'a::len word\<close>
  by (cases \<open>sint a < 0\<close>; cases \<open>sint b < 0\<close>) (simp_all add: signed_modulo_int_def sdiv_word_def smod_word_def)

(* Basic proofs that signed word div/mod operations are
 * truncations of their integer counterparts. *)

lemma signed_div_arith:
    "sint ((a::('a::len) word) sdiv b) = signed_take_bit (LENGTH('a) - 1) (sint a sdiv sint b)"
  apply transfer
  apply simp
  done

lemma signed_mod_arith:
    "sint ((a::('a::len) word) smod b) = signed_take_bit (LENGTH('a) - 1) (sint a smod sint b)"
  apply transfer
  apply simp
  done

end