(* SPDX-License-Identifier: BSD-3-Clause *)

section\<open>Increment and Decrement Machine Words Without Wrap-Around\<close>

theory Next_and_Prev
imports
  Aligned
begin

lemma take_bit_eq_mask_iff:
  \<open>take_bit n k = mask n \<longleftrightarrow> take_bit n (k + 1) = 0\<close>
  for k :: int
  apply auto
   apply (subst take_bit_add [symmetric])
   apply (simp add: mask_eq_exp_minus_1)
  apply (metis bintrunc_bintrunc diff_0 diff_add_cancel diff_minus_eq_add mask_eq_take_bit_minus_one take_bit_diff)
  done

lemma take_bit_eq_mask_iff_exp_dvd:
  \<open>take_bit n k = mask n \<longleftrightarrow> 2 ^ n dvd k + 1\<close>
  for k :: int
  by (simp add: take_bit_eq_mask_iff flip: take_bit_eq_0_iff)

lemma plus_one_helper[elim!]:
  "x < n + (1 :: 'a :: len word) \<Longrightarrow> x \<le> n"
  apply (simp add: word_less_nat_alt word_le_nat_alt field_simps)
  apply (case_tac "1 + n = 0")
   apply simp_all
  apply (subst(asm) unatSuc, assumption)
  apply arith
  done

lemma plus_one_helper2:
  "\<lbrakk> x \<le> n; n + 1 \<noteq> 0 \<rbrakk> \<Longrightarrow> x < n + (1 :: 'a :: len word)"
  by (simp add: word_less_nat_alt word_le_nat_alt field_simps
                unatSuc)

lemma less_x_plus_1:
  fixes x :: "'a :: len word" shows
  "x \<noteq> max_word \<Longrightarrow> (y < (x + 1)) = (y < x \<or> y = x)"
  apply (rule iffI)
   apply (rule disjCI)
   apply (drule plus_one_helper)
   apply simp
  apply (subgoal_tac "x < x + 1")
   apply (erule disjE, simp_all)
  apply (rule plus_one_helper2 [OF order_refl])
  apply (rule notI, drule max_word_wrap)
  apply simp
  done

lemma word_Suc_leq:
  fixes k::"'a::len word" shows "k \<noteq> max_word \<Longrightarrow> x < k + 1 \<longleftrightarrow> x \<le> k"
  using less_x_plus_1 word_le_less_eq by auto

lemma word_Suc_le:
   fixes k::"'a::len word" shows "x \<noteq> max_word \<Longrightarrow> x + 1 \<le> k \<longleftrightarrow> x < k"
  by (meson not_less word_Suc_leq)

lemma word_lessThan_Suc_atMost:
  \<open>{..< k + 1} = {..k}\<close> if \<open>k \<noteq> - 1\<close> for k :: \<open>'a::len word\<close>
  using that by (simp add: lessThan_def atMost_def word_Suc_leq)

lemma word_atLeastLessThan_Suc_atLeastAtMost:
  \<open>{l ..< u + 1} = {l..u}\<close> if \<open>u \<noteq> - 1\<close> for l :: \<open>'a::len word\<close>
  using that by (simp add: atLeastAtMost_def atLeastLessThan_def word_lessThan_Suc_atMost)

lemma word_atLeastAtMost_Suc_greaterThanAtMost:
  \<open>{m<..u} = {m + 1..u}\<close> if \<open>m \<noteq> - 1\<close> for m :: \<open>'a::len word\<close>
  using that by (simp add: greaterThanAtMost_def greaterThan_def atLeastAtMost_def atLeast_def word_Suc_le)

lemma word_atLeastLessThan_Suc_atLeastAtMost_union:
  fixes l::"'a::len word"
  assumes "m \<noteq> max_word" and "l \<le> m" and "m \<le> u"
  shows "{l..m} \<union> {m+1..u} = {l..u}"
  proof -
  from ivl_disj_un_two(8)[OF assms(2) assms(3)] have "{l..u} = {l..m} \<union> {m<..u}" by blast
  with assms show ?thesis by(simp add: word_atLeastAtMost_Suc_greaterThanAtMost)
  qed

lemma max_word_less_eq_iff [simp]:
  \<open>- 1 \<le> w \<longleftrightarrow> w = - 1\<close> for w :: \<open>'a::len word\<close>
  by (fact word_order.extremum_unique)

text \<open>Previous and next words addresses, without wrap around.\<close>

lift_definition word_next :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k. if 2 ^ LENGTH('a) dvd k + 1 then - 1 else k + 1\<close>
  by (simp flip: take_bit_eq_0_iff) (metis take_bit_add)

lift_definition word_prev :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k. if 2 ^ LENGTH('a) dvd k then 0 else k - 1\<close>
  by (simp flip: take_bit_eq_0_iff) (metis take_bit_diff)

lemma word_next_unfold:
  \<open>word_next w = (if w = - 1 then - 1 else w + 1)\<close>
  by transfer (simp add: take_bit_minus_one_eq_mask flip: take_bit_eq_mask_iff_exp_dvd)

lemma word_prev_unfold:
  \<open>word_prev w = (if w = 0 then 0 else w - 1)\<close>
  by transfer (simp flip: take_bit_eq_0_iff)

lemma [code]:
  \<open>Word.the_int (word_next w :: 'a::len word) =
    (if w = - 1 then Word.the_int w else Word.the_int w + 1)\<close>
  by transfer
    (simp add: take_bit_minus_one_eq_mask mask_eq_exp_minus_1 take_bit_incr_eq flip: take_bit_eq_mask_iff_exp_dvd) 

lemma [code]:
  \<open>Word.the_int (word_prev w :: 'a::len word) =
    (if w = 0 then Word.the_int w else Word.the_int w - 1)\<close>
  by transfer (simp add: take_bit_eq_0_iff take_bit_decr_eq)

lemma word_adjacent_union:
  "word_next e = s' \<Longrightarrow> s \<le> e \<Longrightarrow> s' \<le> e' \<Longrightarrow> {s..e} \<union> {s'..e'} = {s .. e'}"
  apply (simp add: word_next_unfold ivl_disj_un_two_touch split: if_splits)
  apply (drule sym)
  apply simp
  apply (subst word_atLeastLessThan_Suc_atLeastAtMost_union)
     apply (simp_all add: word_Suc_le)
  done

end
