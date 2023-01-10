section \<open>Lists of numbers\label{s:tm-numlist}\<close>

theory Lists_Lists
  imports Arithmetic
begin

text \<open>
In the previous section we defined a representation for numbers over the binary
alphabet @{text "{\<zero>,\<one>}"}. In this section we first introduce a representation
of lists of numbers as symbol sequences over the alphabet @{text "{\<zero>,\<one>,\<bar>}"}.
Then we define Turing machines for some operations over such lists.

As with the arithmetic operations, Turing machines implementing the operations
on lists usually expect the tape heads of the operands to be in position~1 and
guarantee to place the tape heads of the result in position~1. The exception are
Turing machines for iterating over lists; such TMs move the tape head to the
next list element.

A tape containing such representations corresponds to a variable of type @{typ
"nat list"}. A tape in the start configuration corresponds to the empty list of
numbers.
\<close>


subsection \<open>Representation as symbol sequence\label{s:tm-numlist-repr}\<close>

text \<open>
The obvious idea for representing a list of numbers is to write them one after
another separated by a fresh symbol, such as @{text "\<bar>"}. However since we
represent the number~0 by the empty symbol sequence, this would result in both
the empty list and the list containing only the number~0 to be represented by
the same symbol sequence, namely the empty one. To prevent this we use the
symbol @{text "\<bar>"} not as a separator but as a terminator; that is, we append it
to every number.  Consequently the empty symbol sequence represents the empty
list, whereas the list $[0]$ is represented by the symbol sequence @{text "\<bar>"}.
As another example, the list $[14,0,0,7]$ is represented by
@{text "\<zero>\<one>\<one>\<one>\<bar>\<bar>\<bar>\<one>\<one>\<one>\<bar>"}. As a side effect of using terminators instead of
separators, the representation of the concatenation of lists is just the
concatenation of the representations of the individual lists.  Moreover the
length of the representation is simply the sum of the individual representation
lengths. The number of @{text "\<bar>"} symbols equals the number of elements in the
list.
\<close>

text \<open>
This is how lists of numbers are represented as symbol sequences:
\<close>

definition numlist :: "nat list \<Rightarrow> symbol list" where
  "numlist ns \<equiv> concat (map (\<lambda>n. canrepr n @ [\<bar>]) ns)"

lemma numlist_Nil: "numlist [] = []"
  using numlist_def by simp

proposition "numlist [0] = [\<bar>]"
  using numlist_def by (simp add: canrepr_0)

lemma numlist_234: "set (numlist ns) \<subseteq> {\<zero>, \<one>, \<bar>}"
proof (induction ns)
  case Nil
  then show ?case
    using numlist_def by simp
next
  case (Cons n ns)
  have "numlist (n # ns) = canrepr n @ [\<bar>] @ concat (map (\<lambda>n. canrepr n @ [\<bar>]) ns)"
    using numlist_def by simp
  then have "numlist (n # ns) = canrepr n @ [\<bar>] @ numlist ns"
    using numlist_def by simp
  moreover have "set ([\<bar>] @ numlist ns) \<subseteq> {\<zero>, \<one>, \<bar>}"
    using Cons by simp
  moreover have "set (canrepr n) \<subseteq> {\<zero>, \<one>, \<bar>}"
    using bit_symbols_canrepr by (metis in_set_conv_nth insertCI subsetI)
  ultimately show ?case
    by simp
qed

lemma symbols_lt_numlist: "symbols_lt 5 (numlist ns)"
  using numlist_234
  by (metis empty_iff insert_iff nth_mem numeral_less_iff semiring_norm(68) semiring_norm(76) semiring_norm(79)
    semiring_norm(80) subset_code(1) verit_comp_simplify1(2))

lemma bit_symbols_prefix_eq:
  assumes "(x @ [\<bar>]) @ xs = (y @ [\<bar>]) @ ys" and "bit_symbols x" and "bit_symbols y"
  shows "x = y"
proof -
  have *: "x @ [\<bar>] @ xs = y @ [\<bar>] @ ys"
      (is "?lhs = ?rhs")
    using assms(1) by simp
  show "x = y"
  proof (cases "length x \<le> length y")
    case True
    then have "?lhs ! i = ?rhs ! i" if "i < length x" for i
      using that * by simp
    then have eq: "x ! i = y ! i" if "i < length x" for i
      using that True by (metis Suc_le_eq le_trans nth_append)
    have "?lhs ! (length x) = \<bar>"
      by (metis Cons_eq_appendI nth_append_length)
    then have "?rhs ! (length x) = \<bar>"
      using * by metis
    then have "length y \<le> length x"
      using assms(3)
      by (metis linorder_le_less_linear nth_append numeral_eq_iff semiring_norm(85) semiring_norm(87) semiring_norm(89))
    then have "length y = length x"
      using True by simp
    then show ?thesis
      using eq by (simp add: list_eq_iff_nth_eq)
  next
    case False
    then have "?lhs ! i = ?rhs ! i" if "i < length y" for i
      using that * by simp
    have "?rhs ! (length y) = \<bar>"
      by (metis Cons_eq_appendI nth_append_length)
    then have "?lhs ! (length y) = \<bar>"
      using * by metis
    then have "x ! (length y) = \<bar>"
      using False by (simp add: nth_append)
    then have False
      using assms(2) False
      by (metis linorder_le_less_linear numeral_eq_iff semiring_norm(85) semiring_norm(87) semiring_norm(89))
    then show ?thesis
      by simp
  qed
qed

lemma numlist_inj: "numlist ns1 = numlist ns2 \<Longrightarrow> ns1 = ns2"
proof (induction ns1 arbitrary: ns2)
  case Nil
  then show ?case
    using numlist_def by simp
next
  case (Cons n ns1)
  have 1: "numlist (n # ns1) = (canrepr n @ [\<bar>]) @ numlist ns1"
    using numlist_def by simp
  then have "numlist ns2 = (canrepr n @ [\<bar>]) @ numlist ns1"
    using Cons by simp
  then have "ns2 \<noteq> []"
    using numlist_Nil by auto
  then have 2: "ns2 = hd ns2 # tl ns2"
    using `ns2 \<noteq> []` by simp
  then have 3: "numlist ns2 = (canrepr (hd ns2) @ [\<bar>]) @ numlist (tl ns2)"
    using numlist_def by (metis concat.simps(2) list.simps(9))

  have 4: "hd ns2 = n"
    using bit_symbols_prefix_eq 1 3 by (metis Cons.prems canrepr bit_symbols_canrepr)
  then have "numlist ns2 = (canrepr n @ [\<bar>]) @ numlist (tl ns2)"
    using 3 by simp
  then have "numlist ns1 = numlist (tl ns2)"
    using 1 by (simp add: Cons.prems)
  then have "ns1 = tl ns2"
    using Cons by simp
  then show ?case
    using 2 4 by simp
qed

corollary proper_symbols_numlist: "proper_symbols (numlist ns)"
  using numlist_234 nth_mem by fastforce

text \<open>
The next property would not hold if we used separators between
elements instead of terminators after elements.
\<close>

lemma numlist_append: "numlist (xs @ ys) = numlist xs @ numlist ys"
  using numlist_def by simp

text \<open>
Like @{const nlength} for numbers, we have @{term nllength} for the length of
the representation of a list of numbers.
\<close>

definition nllength :: "nat list \<Rightarrow> nat" where
  "nllength ns \<equiv> length (numlist ns)"

lemma nllength: "nllength ns = (\<Sum>n\<leftarrow>ns. Suc (nlength n))"
  using nllength_def numlist_def by (induction ns) simp_all

lemma nllength_Nil [simp]: "nllength [] = 0"
  using nllength_def numlist_def by simp

lemma length_le_nllength: "length ns \<le> nllength ns"
  using nllength sum_list_mono[of ns "\<lambda>_. 1" "\<lambda>n. Suc (nlength n)"] sum_list_const[of 1 ns]
  by simp

lemma nllength_le_len_mult_max:
  fixes N :: nat and ns :: "nat list"
  assumes "\<forall>n\<in>set ns. n \<le> N"
  shows "nllength ns \<le> Suc (nlength N) * length ns"
proof -
  have "nllength ns = (\<Sum>n\<leftarrow>ns. Suc (nlength n))"
    using nllength by simp
  moreover have "Suc (nlength n) \<le> Suc (nlength N)" if "n \<in> set ns" for n
    using nlength_mono that assms by simp
  ultimately have "nllength ns \<le> (\<Sum>n\<leftarrow>ns. Suc (nlength N))"
    by (simp add: sum_list_mono)
  then show "nllength ns \<le> Suc (nlength N) * length ns"
    using sum_list_const by metis
qed

lemma nllength_upt_le_len_mult_max:
  fixes a b :: nat
  shows "nllength [a..<b] \<le> Suc (nlength b) * (b - a)"
  using nllength_le_len_mult_max[of "[a..<b]" b] by simp

lemma nllength_le_len_mult_Max: "nllength ns \<le> Suc (nlength (Max (set ns))) * length ns"
  using nllength_le_len_mult_max by simp

lemma member_le_nllength: "n \<in> set ns \<Longrightarrow> nlength n \<le> nllength ns"
  using nllength by (induction ns) auto

lemma member_le_nllength_1: "n \<in> set ns \<Longrightarrow> nlength n \<le> nllength ns - 1"
  using nllength by (induction ns) auto

lemma nllength_gr_0: "ns \<noteq> [] \<Longrightarrow> 0 < nllength ns"
  using nllength_def numlist_def by simp

lemma nlength_min_le_nllength: "n \<in> set ns \<Longrightarrow> m \<in> set ns \<Longrightarrow> nlength (min n m) \<le> nllength ns"
  using member_le_nllength by (simp add: min_def)

lemma take_drop_numlist:
  assumes "i < length ns"
  shows "take (Suc (nlength (ns ! i))) (drop (nllength (take i ns)) (numlist ns)) = canrepr (ns ! i) @ [\<bar>]"
proof -
  have "numlist ns = numlist (take i ns) @ numlist (drop i ns)"
    using numlist_append by (metis append_take_drop_id)
  moreover have "numlist (drop i ns) = numlist [ns ! i] @ numlist (drop (Suc i) ns)"
    using assms numlist_append by (metis Cons_nth_drop_Suc append_Cons self_append_conv2)
  ultimately have "numlist ns = numlist (take i ns) @ numlist [ns ! i] @ numlist (drop (Suc i) ns)"
    by simp
  then have "drop (nllength (take i ns)) (numlist ns) = numlist [ns ! i] @ numlist (drop (Suc i) ns)"
    by (simp add: nllength_def)
  then have "drop (nllength (take i ns)) (numlist ns) = canrepr (ns ! i) @ [\<bar>] @ numlist (drop (Suc i) ns)"
    using numlist_def by simp
  then show ?thesis
    by simp
qed

corollary take_drop_numlist':
  assumes "i < length ns"
  shows "take (nlength (ns ! i)) (drop (nllength (take i ns)) (numlist ns)) = canrepr (ns ! i)"
  using take_drop_numlist[OF assms] by (metis append_assoc append_eq_conv_conj append_take_drop_id)

corollary numlist_take_at_term:
  assumes "i < length ns"
  shows "numlist ns ! (nllength (take i ns) + nlength (ns ! i)) = \<bar>"
  using assms take_drop_numlist nllength_def numlist_append
  by (smt (z3) append_eq_conv_conj append_take_drop_id lessI nth_append_length nth_append_length_plus nth_take)

lemma numlist_take_at:
  assumes "i < length ns" and "j < nlength (ns ! i)"
  shows "numlist ns ! (nllength (take i ns) + j) = canrepr (ns ! i) ! j"
proof -
  have "ns = take i ns @ [ns ! i] @ drop (Suc i) ns"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "numlist ns = (numlist (take i ns) @ numlist [ns ! i]) @ numlist (drop (Suc i) ns)"
    using numlist_append by (metis append_assoc)
  moreover have "nllength (take i ns) + j < nllength (take i ns) + nllength [ns ! i]"
    using assms(2) nllength by simp
  ultimately have "numlist ns ! (nllength (take i ns) + j) =
      (numlist (take i ns) @ numlist [ns ! i]) ! (nllength (take i ns) + j)"
    by (metis length_append nllength_def nth_append)
  also have "... = numlist [ns ! i] ! j"
    by (simp add: nllength_def)
  also have "... = (canrepr (ns ! i) @ [\<bar>]) ! j"
    using numlist_def by simp
  also have "... = canrepr (ns ! i) ! j"
    using assms(2) by (simp add: nth_append)
  finally show ?thesis .
qed

lemma nllength_take_Suc:
  assumes "i < length ns"
  shows "nllength (take i ns) + Suc (nlength (ns ! i)) = nllength (take (Suc i) ns)"
proof -
  have "ns = take i ns @ [ns ! i] @ drop (Suc i) ns"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "numlist ns = numlist (take i ns) @ numlist [ns ! i] @ numlist (drop (Suc i) ns)"
    using numlist_append by metis
  then have "nllength ns = nllength (take i ns) + nllength [ns ! i] + nllength (drop (Suc i) ns)"
    by (simp add: nllength_def)
  moreover have "nllength ns = nllength (take (Suc i) ns) + nllength (drop (Suc i) ns)"
    using numlist_append by (metis append_take_drop_id length_append nllength_def)
  ultimately have "nllength (take (Suc i) ns) = nllength (take i ns) + nllength [ns ! i]"
    by simp
  then show ?thesis
    using nllength by simp
qed

lemma numlist_take_Suc_at_term:
  assumes "i < length ns"
  shows "numlist ns ! (nllength (take (Suc i) ns) - 1) = \<bar>"
proof -
  have "nllength (take (Suc i) ns) - 1 = nllength (take i ns) + nlength (ns ! i)"
    using nllength_take_Suc assms by (metis add_Suc_right diff_Suc_1)
  then show ?thesis
    using numlist_take_at_term assms by simp
qed

lemma nllength_take:
  assumes "i < length ns"
  shows "nllength (take i ns) + nlength (ns ! i) < nllength ns"
proof -
  have "ns = take i ns @ [ns ! i] @ drop (Suc i) ns"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "numlist ns = numlist (take i ns) @ numlist [ns ! i] @ numlist (drop (Suc i) ns)"
    using numlist_append by metis
  then have "nllength ns = nllength (take i ns) + nllength [ns ! i] + nllength (drop (Suc i) ns)"
    by (simp add: nllength_def)
  then have "nllength ns \<ge> nllength (take i ns) + nllength [ns ! i]"
    by simp
  then have "nllength ns \<ge> nllength (take i ns) + Suc (nlength (ns ! i))"
    using nllength by simp
  then show ?thesis
    by simp
qed

text \<open>
The contents of a tape starting with the start symbol @{text \<triangleright>} followed by the
symbol sequence representing a list of numbers:
\<close>

definition nlcontents :: "nat list \<Rightarrow> (nat \<Rightarrow> symbol)" ("\<lfloor>_\<rfloor>\<^sub>N\<^sub>L") where
  "\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L \<equiv> \<lfloor>numlist ns\<rfloor>"

lemma clean_tape_nlcontents: "clean_tape (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, i)"
  by (simp add: nlcontents_def proper_symbols_numlist)

lemma nlcontents_Nil: "\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L = \<lfloor>[]\<rfloor>"
  using nlcontents_def by (simp add: numlist_Nil)

lemma nlcontents_rneigh_4:
  assumes "i < length ns"
  shows "rneigh (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take i ns))) {\<bar>} (nlength (ns ! i))"
proof (rule rneighI)
  let ?tp = "(\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take i ns)))"
  show "fst ?tp (snd ?tp + nlength (ns ! i)) \<in> {\<bar>}"
  proof -
    have "snd ?tp + nlength (ns ! i) \<le> nllength ns"
      using nllength_take assms by (simp add: Suc_leI)
    then have "fst ?tp (snd ?tp + nlength (ns ! i)) = numlist ns ! (nllength (take i ns) + nlength (ns ! i))"
      using nlcontents_def contents_inbounds nllength_def by simp
    then show ?thesis
      using numlist_take_at_term assms by simp
  qed
  show "fst ?tp (snd ?tp + j) \<notin> {\<bar>}" if "j < nlength (ns ! i)" for j
  proof -
    have "snd ?tp + nlength (ns ! i) \<le> nllength ns"
      using nllength_take assms by (simp add: Suc_leI)
    then have "snd ?tp + j \<le> nllength ns"
      using that by simp
    then have "fst ?tp (snd ?tp + j) = numlist ns ! (nllength (take i ns) + j)"
      using nlcontents_def contents_inbounds nllength_def by simp
    then have "fst ?tp (snd ?tp + j) = canrepr (ns ! i) ! j"
      using assms that numlist_take_at by simp
    then show ?thesis
      using bit_symbols_canrepr that by fastforce
  qed
qed

lemma nlcontents_rneigh_04:
  assumes "i < length ns"
  shows "rneigh (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take i ns))) {\<box>, \<bar>} (nlength (ns ! i))"
proof (rule rneighI)
  let ?tp = "(\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take i ns)))"
  show "fst ?tp (snd ?tp + nlength (ns ! i)) \<in> {\<box>, \<bar>}"
  proof -
    have "snd ?tp + nlength (ns ! i) \<le> nllength ns"
      using nllength_take assms by (simp add: Suc_leI)
    then have "fst ?tp (snd ?tp + nlength (ns ! i)) = numlist ns ! (nllength (take i ns) + nlength (ns ! i))"
      using nlcontents_def contents_inbounds nllength_def by simp
    then show ?thesis
      using numlist_take_at_term assms by simp
  qed
  show "fst ?tp (snd ?tp + j) \<notin> {\<box>, \<bar>}" if "j < nlength (ns ! i)" for j
  proof -
    have "snd ?tp + nlength (ns ! i) \<le> nllength ns"
      using nllength_take assms by (simp add: Suc_leI)
    then have "snd ?tp + j \<le> nllength ns"
      using that by simp
    then have "fst ?tp (snd ?tp + j) = numlist ns ! (nllength (take i ns) + j)"
      using nlcontents_def contents_inbounds nllength_def by simp
    then have "fst ?tp (snd ?tp + j) = canrepr (ns ! i) ! j"
      using assms that numlist_take_at by simp
    then show ?thesis
      using bit_symbols_canrepr that by fastforce
  qed
qed

text \<open>
A tape storing a list of numbers, with the tape head in the first blank cell
after the symbols:
\<close>

abbreviation nltape :: "nat list \<Rightarrow> tape" where
  "nltape ns \<equiv> (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength ns))"

text \<open>
A tape storing a list of numbers, with the tape head on the first symbol
representing the $i$-th number, unless the $i$-th number is zero, in which case
the tape head is on the terminator symbol of this zero. If $i$ is out of bounds
of the list, the tape head is at the first blank after the list.
\<close>

abbreviation nltape' :: "nat list \<Rightarrow> nat \<Rightarrow> tape" where
  "nltape' ns i \<equiv> (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take i ns)))"

lemma nltape'_tape_read: "|.| (nltape' ns i) = \<box> \<longleftrightarrow> i \<ge> length ns"
proof -
  have "|.| (nltape' ns i) = \<box>" if "i \<ge> length ns" for i
  proof -
    have "nltape' ns i \<equiv> (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength ns))"
      using that by simp
    then show ?thesis
      using nlcontents_def contents_outofbounds nllength_def
      by (metis Suc_eq_plus1 add.left_neutral fst_conv less_Suc0 less_add_eq_less snd_conv)
  qed
  moreover have "|.| (nltape' ns i) \<noteq> \<box>" if "i < length ns" for i
    using that nlcontents_def contents_inbounds nllength_def nllength_take proper_symbols_numlist
    by (metis Suc_leI add_Suc_right diff_Suc_1 fst_conv less_add_same_cancel1 less_le_trans not_add_less2
      plus_1_eq_Suc snd_conv zero_less_Suc)
  ultimately show ?thesis
    by (meson le_less_linear)
qed


subsection \<open>Moving to the next element\<close>

text \<open>
The next Turing machine provides a means to iterate over a list of numbers.  If
the TM starts in a configuration where the tape $j_1$ contains a list of numbers
and the tape head is on the first symbol of the $i$-th element of this list,
then after the TM has finished, the $i$-th element will be written on tape
$j_2$ and the tape head on $j_1$ will have advanced by one list element. If
$i$ is the last element of the list, the tape head on $j_1$ will be on a blank
symbol. One can execute this TM in a loop until the tape head reaches a blank.
The TM is generic over a parameter $z$ representing the terminator symbol, so it
can be used for other kinds of lists, too (see Section~\ref{s:tm-numlistlist}).

\null
\<close>

definition tm_nextract :: "symbol \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_nextract z j1 j2 \<equiv>
    tm_erase_cr j2 ;;
    tm_cp_until j1 j2 {z} ;;
    tm_cr j2 ;;
    tm_right j1"

lemma tm_nextract_tm:
  assumes "G \<ge> 4" and "G > z" and "0 < j2" and "j2 < k" and "j1 < k" and "k \<ge> 2"
  shows "turing_machine k G (tm_nextract z j1 j2)"
  unfolding tm_nextract_def
  using assms tm_erase_cr_tm tm_cp_until_tm tm_cr_tm tm_right_tm
  by simp

text \<open>
The next locale is for the case @{text "z = \<bar>"}.

\null
\<close>

locale turing_machine_nextract_4 =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_erase_cr j2"
definition "tm2 \<equiv> tm1 ;; tm_cp_until j1 j2 {\<bar>}"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"
definition "tm4 \<equiv> tm3 ;; tm_right j1"

lemma tm4_eq_tm_nextract: "tm4 = tm_nextract \<bar> j1 j2"
  unfolding tm1_def tm2_def tm3_def tm4_def tm_nextract_def by simp

context
  fixes tps0 :: "tape list" and k idx dummy :: nat and ns :: "nat list"
  assumes jk: "j1 < k" "j2 < k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "length tps0 = k"
    and idx: "idx < length ns"
    and tps0:
      "tps0 ! j1 = nltape' ns idx"
      "tps0 ! j2 = (\<lfloor>dummy\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0[j2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 7 + 2 * nlength dummy"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk idx tps0 tps1_def assms)
  show "proper_symbols (canrepr dummy)"
    using proper_symbols_canrepr by simp
  show "tps1 = tps0[j2 := (\<lfloor>[]\<rfloor>, 1)]"
    using ncontents_0 tps1_def by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, nllength (take (Suc idx) ns)),
   j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, Suc (nlength (ns ! idx)))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 7 + 2 * nlength dummy + Suc (nlength (ns ! idx))"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk idx tps0 tps2_def tps1_def)
  show "rneigh (tps1 ! j1) {\<bar>} (nlength (ns ! idx))"
    using tps1_def tps0 jk by (simp add: idx nlcontents_rneigh_4)
  show "tps2 = tps1
    [j1 := tps1 ! j1 |+| nlength (ns ! idx),
     j2 := implant (tps1 ! j1) (tps1 ! j2) (nlength (ns ! idx))]"
     (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using tps1_def tps2_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      consider "i = j1" | "i = j2" | "i \<noteq> j1 \<and> i \<noteq> j2"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using tps0 that tps1_def tps2_def jk nllength_take_Suc[OF idx] idx by simp
      next
        case 2
        then have lhs: "?l ! i = (\<lfloor>ns ! idx\<rfloor>\<^sub>N, Suc (nlength (ns ! idx)))"
          using tps2_def jk by simp
        let ?i = "Suc (nllength (take idx ns))"
        have i1: "?i > 0"
          by simp
        have "nlength (ns ! idx) + (?i - 1) \<le> nllength ns"
          using idx by (simp add: add.commute less_or_eq_imp_le nllength_take)
        then have i2: "nlength (ns ! idx) + (?i - 1) \<le> length (numlist ns)"
          using nllength_def by simp
        have "?r ! i = implant (tps1 ! j1) (tps1 ! j2) (nlength (ns ! idx))"
          using 2 tps1_def jk by simp
        also have "... = implant (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, ?i) (\<lfloor>0\<rfloor>\<^sub>N, 1) (nlength (ns ! idx))"
          using tps1_def jk tps0 by simp
        also have "... =
          (\<lfloor>[] @ (take (nlength (ns ! idx)) (drop (?i - 1) (numlist ns)))\<rfloor>,
           Suc (length []) + nlength (ns ! idx))"
          using implant_contents[OF i1 i2] by (metis One_nat_def list.size(3) ncontents_0 nlcontents_def)
        finally have "?r ! i =
          (\<lfloor>[] @ (take (nlength (ns ! idx)) (drop (?i - 1) (numlist ns)))\<rfloor>,
           Suc (length []) + nlength (ns ! idx))" .
        then have "?r ! i = (\<lfloor>take (nlength (ns ! idx)) (drop (nllength (take idx ns)) (numlist ns))\<rfloor>, Suc (nlength (ns ! idx)))"
          by simp
        then have "?r ! i = (\<lfloor>canrepr (ns ! idx)\<rfloor>, Suc (nlength (ns ! idx)))"
          using take_drop_numlist'[OF idx] by simp
        then show ?thesis
          using lhs by simp
      next
        case 3
        then show ?thesis
          using that tps1_def tps2_def jk by simp
      qed
    qed
  qed
  show "ttt = 7 + 2 * nlength dummy + Suc (nlength (ns ! idx))"
    using assms(1) .
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, nllength (take (Suc idx) ns)),
   j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 11 + 2 * nlength dummy + 2 * (nlength (ns ! idx))"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: jk idx tps0 tps2_def tps3_def time: assms tps2_def jk)
  show "clean_tape (tps2 ! j2)"
    using tps2_def jk clean_tape_ncontents by simp
qed

definition "tps4 \<equiv> tps0
  [j1 := nltape' ns (Suc idx),
   j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"

lemma tm4:
  assumes "ttt = 12 + 2 * nlength dummy + 2 * (nlength (ns ! idx))"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: jk idx tps0 tps3_def tps4_def time: assms)
  show "tps4 = tps3[j1 := tps3 ! j1 |+| 1]"
    using tps3_def tps4_def jk tps0
    by (metis Suc_eq_plus1 fst_conv list_update_overwrite list_update_swap nth_list_update_eq nth_list_update_neq snd_conv)
qed

end  (* context *)

end  (* locale turing_machine_nextract *)

lemma transforms_tm_nextract_4I [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k idx dummy :: nat and ns :: "nat list"
  assumes "j1 < k" "j2 < k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "length tps = k"
    and "idx < length ns"
  assumes
    "tps ! j1 = nltape' ns idx"
    "tps ! j2 = (\<lfloor>dummy\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 12 + 2 * nlength dummy + 2 * (nlength (ns ! idx))"
  assumes "tps' = tps
    [j1 := nltape' ns (Suc idx),
     j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_nextract \<bar> j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_nextract_4 j1 j2 .
  show ?thesis
    using assms loc.tm4 loc.tps4_def loc.tm4_eq_tm_nextract by simp
qed


subsection \<open>Appending an element\<close>

text \<open>
The next Turing machine appends the number on tape $j_2$ to the list of numbers
on tape $j_1$.
\<close>

definition tm_append :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_append j1 j2 \<equiv>
    tm_right_until j1 {\<box>} ;;
    tm_cp_until j2 j1 {\<box>} ;;
    tm_cr j2 ;;
    tm_char j1 \<bar>"

lemma tm_append_tm:
  assumes "0 < j1" and "G \<ge> 5" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_append j1 j2)"
  unfolding tm_append_def
  using assms tm_right_until_tm tm_cp_until_tm tm_right_tm tm_char_tm tm_cr_tm
  by simp

locale turing_machine_append =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_right_until j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_cp_until j2 j1 {\<box>}"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"
definition "tm4 \<equiv> tm3 ;; tm_char j1 \<bar>"

lemma tm4_eq_tm_append: "tm4 = tm_append j1 j2"
  unfolding tm4_def tm3_def tm2_def tm1_def tm_append_def by simp

context
  fixes tps0 :: "tape list" and k i1 n :: nat and ns :: "nat list"
  assumes jk: "length tps0 = k" "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j1"
    and i1: "i1 \<le> Suc (nllength ns)"
    and tps0:
      "tps0 ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, i1)"
      "tps0 ! j2 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
begin

lemma k: "k \<ge> 2"
  using jk by simp

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (Suc (nllength ns) - i1)"
    and "tps' = tps0[j1 := nltape ns]"
  shows "transforms tm1 tps0 ttt tps'"
  unfolding tm1_def
proof (tform tps: jk k)
  let ?l = "Suc (nllength ns) - i1"
  show "rneigh (tps0 ! j1) {0} ?l"
  proof (rule rneighI)
    show "(tps0 ::: j1) (tps0 :#: j1 + ?l) \<in> {0}"
      using tps0 jk nlcontents_def nllength_def by simp
    show "(tps0 ::: j1) (tps0 :#: j1 + i) \<notin> {0}" if "i < Suc (nllength ns) - i1" for i
    proof -
      have "i1 + i < Suc (nllength ns)"
        using that i1 by simp
      then show ?thesis
        using proper_symbols_numlist nllength_def tps0 nlcontents_def contents_def
        by (metis One_nat_def Suc_le_eq diff_Suc_1 fst_eqD less_Suc_eq_0_disj less_nat_zero_code singletonD snd_eqD)
    qed
  qed
  show "ttt = Suc (Suc (nllength ns) - i1)"
    using assms(1) .
  show "tps' = tps0[j1 := tps0 ! j1 |+| Suc (nllength ns) - i1]"
    using assms(2) tps0 i1 by simp
qed

lemma tm2 [transforms_intros]:
  assumes "ttt = 3 + nllength ns - i1 + nlength n"
    and "tps' = tps0
      [j1 := (\<lfloor>numlist ns @ canrepr n\<rfloor>, Suc (nllength ns) + nlength n),
       j2 := (\<lfloor>n\<rfloor>\<^sub>N, Suc (nlength n))]"
  shows "transforms tm2 tps0 ttt tps'"
  unfolding tm2_def
proof (tform tps: jk tps0)
  let ?tps = "tps0[j1 := nltape ns]"
  have j1: "?tps ! j1 = nltape ns"
    by (simp add: jk)
  have j2: "?tps ! j2 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
    using tps0 jk by simp
  show "rneigh (tps0[j1 := nltape ns] ! j2) {0} (nlength n)"
  proof (rule rneighI)
    show "(?tps ::: j2) (?tps :#: j2 + nlength n) \<in> {0}"
      using j2 contents_outofbounds by simp
    show "\<And>i. i < nlength n \<Longrightarrow> (?tps ::: j2) (?tps :#: j2 + i) \<notin> {0}"
      using j2 tps0 bit_symbols_canrepr by fastforce
  qed
  show "tps' = tps0
    [j1 := nltape ns,
     j2 := ?tps ! j2 |+| nlength n,
     j1 := implant (?tps ! j2) (?tps ! j1) (nlength n)]"
    (is "_ = ?rhs")
  proof -
    have "implant (?tps ! j2) (?tps ! j1) (nlength n) = implant (\<lfloor>n\<rfloor>\<^sub>N, 1) (nltape ns) (nlength n)"
      using j1 j2 by simp
    also have "... = (\<lfloor>numlist ns @ (take (nlength n) (drop (1 - 1) (canrepr n)))\<rfloor>, Suc (length (numlist ns)) + nlength n)"
      using implant_contents nlcontents_def nllength_def by simp
    also have "... = (\<lfloor>numlist ns @ canrepr n\<rfloor>, Suc (length (numlist ns)) + nlength n)"
      by simp
    also have "... = (\<lfloor>numlist ns @ canrepr n\<rfloor>, Suc (nllength ns) + nlength n)"
      using nllength_def by simp
    also have "... = tps' ! j1"
      by (metis assms(2) jk(1,2,4) nth_list_update_eq nth_list_update_neq)
    finally have "implant (?tps ! j2) (?tps ! j1) (nlength n) = tps' ! j1" .
    then have "tps' ! j1 = implant (?tps ! j2) (?tps ! j1) (nlength n)"
      by simp
    then have "tps' ! j1 = ?rhs ! j1"
      by (simp add: jk)
    moreover have "tps' ! j2 = ?rhs ! j2"
      using assms(2) jk j2 by simp
    moreover have "tps' ! j = ?rhs ! j" if "j < length tps'" "j \<noteq> j1" "j \<noteq> j2" for j
      using that assms(2) by simp
    moreover have "length tps' = length ?rhs"
      using assms(2) by simp
    ultimately show ?thesis
      using nth_equalityI by blast
  qed
  show "ttt = Suc (Suc (nllength ns) - i1) + Suc (nlength n)"
    using assms(1) j1 tps0 i1 by simp
qed

definition "tps3 \<equiv> tps0
    [j1 := (\<lfloor>numlist ns @ canrepr n\<rfloor>, Suc (nllength ns) + nlength n)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 6 + nllength ns - i1 + 2 * nlength n"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: jk k)
  let ?tp1 = "(\<lfloor>numlist ns @ canrepr n\<rfloor>, Suc (nllength ns) + nlength n)"
  let ?tp2 = "(\<lfloor>n\<rfloor>\<^sub>N, Suc (nlength n))"
  show "clean_tape (tps0 [j1 := ?tp1, j2 := ?tp2] ! j2)"
    by (simp add: clean_tape_ncontents jk)
  show "tps3 = tps0[j1 := ?tp1, j2 := ?tp2, j2 := tps0 [j1 := ?tp1, j2 := ?tp2] ! j2 |#=| 1]"
    using tps3_def tps0 jk
    by (metis (no_types, lifting) add_Suc fst_conv length_list_update list_update_id list_update_overwrite
      list_update_swap nth_list_update_eq)
  show "ttt =
    3 + nllength ns - i1 + nlength n + (tps0[j1 := ?tp1, j2 := ?tp2] :#: j2 + 2)"
  proof -
    have "tps0[j1 := ?tp1, j2 := ?tp2] :#: j2 = Suc (nlength n)"
      by (simp add: jk)
    then show ?thesis
      using jk tps0 i1 assms(1) by simp
  qed
qed

definition "tps4 = tps0
    [j1 := (\<lfloor>numlist (ns @ [n])\<rfloor>, Suc (nllength (ns @ [n])))]"

lemma tm4:
  assumes "ttt = 7 + nllength ns - i1 + 2 * nlength n"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: jk tps0 tps3_def)
  show "ttt = 6 + nllength ns - i1 + 2 * nlength n + 1 "
      using i1 assms(1) by simp
  show "tps4 = tps3[j1 := tps3 ! j1 |:=| \<bar> |+| 1]"
    (is "tps4 = ?tps")
  proof -
    have "?tps = tps0[j1 := (\<lfloor>numlist ns @ canrepr n\<rfloor>, Suc (nllength ns + nlength n)) |:=| \<bar> |+| 1]"
      using tps3_def by (simp add: jk)
    moreover have "(\<lfloor>numlist ns @ canrepr n\<rfloor>, Suc (nllength ns + nlength n)) |:=| \<bar> |+| 1 =
        (\<lfloor>numlist (ns @ [n])\<rfloor>, Suc (nllength (ns @ [n])))"
      (is "?lhs = ?rhs")
    proof -
      have "?lhs = (\<lfloor>numlist ns @ canrepr n\<rfloor>(Suc (nllength ns + nlength n) := \<bar>), Suc (Suc (nllength ns + nlength n)))"
        by simp
      also have "... = (\<lfloor>numlist ns @ canrepr n\<rfloor>(Suc (nllength ns + nlength n) := \<bar>), Suc (nllength (ns @ [n])))"
        using nllength_def numlist_def by simp
      also have "... = (\<lfloor>(numlist ns @ canrepr n) @ [\<bar>]\<rfloor>, Suc (nllength (ns @ [n])))"
        using contents_snoc by (metis length_append nllength_def)
      also have "... = (\<lfloor>numlist ns @ canrepr n @ [\<bar>]\<rfloor>, Suc (nllength (ns @ [n])))"
        by simp
      also have "... = (\<lfloor>numlist (ns @ [n])\<rfloor>, Suc (nllength (ns @ [n])))"
        using numlist_def by simp
      finally show "?lhs = ?rhs" .
    qed
    ultimately show ?thesis
      using tps4_def by auto
  qed
qed

end

end  (* locale turing_machine_append *)

lemma tm_append [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps :: "tape list" and k i1 n :: nat and ns :: "nat list"
  assumes "0 < j1"
  assumes "length tps = k" "j1 < k" "j2 < k" "j1 \<noteq> j2" "i1 \<le> Suc (nllength ns)"
    and "tps ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, i1)"
    and "tps ! j2 = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 7 + nllength ns - i1 + 2 * nlength n"
    and "tps' = tps
      [j1 := nltape (ns @ [n])]"
  shows "transforms (tm_append j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_append j1 j2 .
  show ?thesis
    using loc.tm4 loc.tm4_eq_tm_append loc.tps4_def assms nlcontents_def by simp
qed


subsection \<open>Computing the length\<close>

text \<open>
The next Turing machine counts the number of terminator symbols $z$ on tape
$j_1$ and stores the result on tape $j_2$. Thus, if $j_1$ contains a list of
numbers, tape $j_2$ will contain the length of the list.
\<close>

definition tm_count :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_count j1 j2 z \<equiv>
    WHILE tm_right_until j1 {\<box>, z} ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      tm_incr j2 ;;
      tm_right j1
    DONE ;;
    tm_cr j1"

lemma tm_count_tm:
  assumes "0 < j2" and "j1 < k" and "j2 < k" and "j1 \<noteq> j2" and "G \<ge> 4"
  shows "turing_machine k G (tm_count j1 j2 z)"
  unfolding tm_count_def
  using turing_machine_loop_turing_machine tm_right_until_tm tm_incr_tm tm_cr_tm tm_right_tm assms
  by simp

locale turing_machine_count =
  fixes j1 j2 :: tapeidx
begin

definition "tmC \<equiv> tm_right_until j1 {\<box>, \<bar>}"
definition "tmB1 \<equiv> tm_incr j2"
definition "tmB2 \<equiv> tmB1 ;; tm_right j1"
definition "tmL \<equiv> WHILE tmC ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tmB2 DONE"
definition "tm2 \<equiv> tmL ;; tm_cr j1"

lemma tm2_eq_tm_count: "tm2 = tm_count j1 j2 \<bar>"
  unfolding tmB1_def tmB2_def tmC_def tmL_def tm2_def tm_count_def
  by simp

context
  fixes tps0 :: "tape list" and k :: nat and ns :: "nat list"
  assumes jk: "j1 < k" "j2 < k" "0 < j2" "j1 \<noteq> j2" "length tps0 = k"
    and tps0:
      "tps0 ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
      "tps0 ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition "tpsL t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take t ns))),
   j2 := (\<lfloor>t\<rfloor>\<^sub>N, 1)]"

definition "tpsC t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, if t < length ns then nllength (take (Suc t) ns) else Suc (nllength ns)),
   j2 := (\<lfloor>t\<rfloor>\<^sub>N, 1)]"

lemma tmC:
  assumes "t \<le> length ns"
    and "ttt = Suc (if t = length ns then 0 else nlength (ns ! t))"
  shows "transforms tmC (tpsL t) ttt (tpsC t)"
  unfolding tmC_def
proof (tform tps: jk tpsL_def tpsC_def)
  let ?n = "if t = length ns then 0 else nlength (ns ! t)"
  have *: "tpsL t ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take t ns)))"
    using tpsL_def jk by simp
  show "rneigh (tpsL t ! j1) {\<box>, \<bar>} ?n"
  proof (cases "t = length ns")
    case True
    then have "tpsL t ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength ns))" (is "_ = ?tp")
      using * by simp
    moreover from this have "fst ?tp (snd ?tp) \<in> {\<box>, \<bar>}"
      by (simp add: nlcontents_def nllength_def)
    moreover have "?n = 0"
      using True by simp
    ultimately show ?thesis
      using rneighI by simp
  next
    case False
    then have "tpsL t ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take t ns)))"
      using * by simp
    moreover have "?n = nlength (ns ! t)"
      using False by simp
    ultimately show ?thesis
      using nlcontents_rneigh_04 by (simp add: False assms(1) le_neq_implies_less)
  qed
  show "tpsC t = (tpsL t) [j1 := tpsL t ! j1 |+| (if t = length ns then 0 else nlength (ns ! t))]"
    (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using tpsC_def tpsL_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      consider "i = j1" | "i = j2" | "i \<noteq> j1 \<and> i \<noteq> j2"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        show ?thesis
        proof (cases "t = length ns")
          case True
          then show ?thesis
            using 1 by (simp add: jk(2,4) tpsC_def tpsL_def)
        next
          case False
          then have "t < length ns"
            using assms(1) by simp
          then show ?thesis
            using 1 nllength_take_Suc jk tpsC_def tpsL_def by simp
        qed
      next
        case 2
        then show ?thesis
          by (simp add: jk(2,4,5) tpsC_def tpsL_def)
      next
        case 3
        then show ?thesis
          by (simp add: jk(2,4) tpsC_def tpsL_def)
      qed
    qed
  qed
  show "ttt = Suc (if t = length ns then 0 else nlength (ns ! t))"
    using assms(2) .
qed

lemma tmC' [transforms_intros]:
  assumes "t \<le> length ns"
  shows "transforms tmC (tpsL t) (Suc (nllength ns)) (tpsC t)"
proof -
  have "Suc (if t = length ns then 0 else nlength (ns ! t)) \<le> Suc (if t = length ns then 0 else nllength ns)"
    using assms member_le_nllength by simp
  then have "Suc (if t = length ns then 0 else nlength (ns ! t)) \<le> Suc (nllength ns)"
    by auto
  then show ?thesis
    using tmC transforms_monotone assms by metis
qed

definition "tpsB1 t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, nllength (take (Suc t) ns)),
   j2 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1)]"

lemma tmB1 [transforms_intros]:
  assumes "t < length ns" and "ttt = 5 + 2 * nlength t"
  shows "transforms tmB1 (tpsC t) ttt (tpsB1 t)"
  unfolding tmB1_def by (tform tps: jk tpsC_def tpsB1_def assms)

definition "tpsB2 t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take (Suc t) ns))),
   j2 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1)]"

lemma tmB2:
  assumes "t < length ns" and "ttt = 6 + 2 * nlength t"
  shows "transforms tmB2 (tpsC t) ttt (tpsB2 t)"
  unfolding tmB2_def by (tform tps: jk tpsB1_def tpsB2_def assms)

lemma tpsB2_eq_tpsL: "tpsB2 t = tpsL (Suc t)"
  using tpsB2_def tpsL_def by simp

lemma tmB2' [transforms_intros]:
  assumes "t < length ns"
  shows "transforms tmB2 (tpsC t) (6 + 2 * nllength ns) (tpsL (Suc t))"
proof -
  have "nlength t \<le> nllength ns"
    using assms(1) length_le_nllength nlength_le_n by (meson le_trans less_or_eq_imp_le)
  then have "6 + 2 * nlength t \<le> 6 + 2 * nllength ns"
    by simp
  then show ?thesis
    using assms tmB2 transforms_monotone tpsB2_eq_tpsL by metis
qed

lemma tmL [transforms_intros]:
  assumes "ttt = 13 * nllength ns ^ 2 + 2"
  shows "transforms tmL (tpsL 0) ttt (tpsC (length ns))"
  unfolding tmL_def
proof (tform)
  show "read (tpsC t) ! j1 \<noteq> \<box>" if "t < length ns" for t
  proof -
    have "tpsC t ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, if t < length ns then nllength (take (Suc t) ns) else Suc (nllength ns))"
      using tpsC_def jk by simp
    then have *: "tpsC t ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, nllength (take (Suc t) ns))" (is "_ = ?tp")
      using that by simp
    have "fst ?tp (snd ?tp) = \<lfloor>ns\<rfloor>\<^sub>N\<^sub>L (nllength (take (Suc t) ns))"
      by simp
    also have "... = \<lfloor>numlist ns\<rfloor> (nllength (take (Suc t) ns))"
      using nlcontents_def by simp
    also have "... = numlist ns ! (nllength (take (Suc t) ns) - 1)"
      using nllength that contents_inbounds nllength_def nllength_take nllength_take_Suc
      by (metis Suc_leI add_Suc_right less_nat_zero_code not_less_eq)
    also have "... = 4"
      using numlist_take_Suc_at_term[OF that] by simp
    finally have "fst ?tp (snd ?tp) = \<bar>" .
    then have "fst ?tp (snd ?tp) \<noteq> \<box>"
      by simp
    then show ?thesis
      using * jk(1,5) length_list_update tapes_at_read' tpsC_def by metis
  qed
  show "\<not> read (tpsC (length ns)) ! j1 \<noteq> \<box>"
  proof -
    have "tpsC (length ns) ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength ns))" (is "_ = ?tp")
      using tpsC_def jk by simp
    moreover have "fst ?tp (snd ?tp) = 0"
      by (simp add: nlcontents_def nllength_def)
    ultimately have "read (tpsC (length ns)) ! j1 = \<box>"
      using jk(1,5) length_list_update tapes_at_read' tpsC_def by metis
    then show ?thesis
      by simp
  qed
  show "length ns * (Suc (nllength ns) + (6 + 2 * nllength ns) + 2) + Suc (nllength ns) + 1 \<le> ttt"
  proof -
    have "length ns * (Suc (nllength ns) + (6 + 2 * nllength ns) + 2) + Suc (nllength ns) + 1 =
        length ns * (9 + 3 * nllength ns) + nllength ns + 2"
      by simp
    also have "... \<le> nllength ns * (9 + 3 * nllength ns) + nllength ns + 2"
      by (simp add: length_le_nllength)
    also have "... = nllength ns * (10 + 3 * nllength ns) + 2"
      by algebra
    also have "... = 10 * nllength ns + 3 * nllength ns ^ 2 + 2"
      by algebra
    also have "... \<le> 10 * nllength ns ^ 2 + 3 * nllength ns ^ 2 + 2"
      by (meson add_mono_thms_linordered_semiring(1) le_eq_less_or_eq mult_le_mono2 power2_nat_le_imp_le)
    also have "... = 13 * nllength ns ^ 2 + 2"
      by simp
    finally show ?thesis
      using assms by simp
  qed
qed

definition "tps2 \<equiv> tps0
  [j2 := (\<lfloor>length ns\<rfloor>\<^sub>N, 1)]"

lemma tm2:
  assumes "ttt = 13 * nllength ns ^ 2 + 5 + nllength ns"
  shows "transforms tm2 (tpsL 0) ttt tps2"
  unfolding tm2_def
proof (tform tps: jk tpsC_def tps2_def)
  have *: "tpsC (length ns) ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength ns))"
    using jk tpsC_def by simp
  then show "clean_tape (tpsC (length ns) ! j1)"
    by (simp add: clean_tape_nlcontents)
  show "tps2 = (tpsC (length ns))[j1 := tpsC (length ns) ! j1 |#=| 1]"
    using jk tps0(1) tps2_def tpsC_def * by (metis fstI list_update_id list_update_overwrite list_update_swap)
  show "ttt = 13 * (nllength ns)\<^sup>2 + 2 + (tpsC (length ns) :#: j1 + 2)"
    using assms * by simp
qed

lemma tpsL_eq_tps0: "tpsL 0 = tps0"
  using tpsL_def tps0 by (metis One_nat_def list_update_id nllength_Nil take0)

lemma tm2':
  assumes "ttt = 14 * nllength ns ^ 2 + 5"
  shows "transforms tm2 tps0 ttt tps2"
proof -
  have "nllength ns \<le> nllength ns ^ 2"
    using power2_nat_le_imp_le by simp
  then have "13 * nllength ns ^ 2 + 5 + nllength ns \<le> ttt"
    using assms by simp
  then show ?thesis
    using assms tm2 transforms_monotone tpsL_eq_tps0 by simp
qed

end  (* context tps0 *)

end  (* locale *)

lemma transforms_tm_count_4I [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and ns :: "nat list"
  assumes "j1 < k" "j2 < k" "0 < j2" "j1 \<noteq> j2" "length tps = k"
  assumes
    "tps ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 14 * nllength ns ^ 2 + 5"
  assumes "tps' = tps[j2 := (\<lfloor>length ns\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_count j1 j2 \<bar>) tps ttt tps'"
proof -
  interpret loc: turing_machine_count j1 j2 .
  show ?thesis
    using loc.tm2_eq_tm_count loc.tm2' loc.tps2_def assms by simp
qed


subsection \<open>Extracting the $n$-th element\<close>

text \<open>
The next Turing machine expects a list on tape $j_1$ and an index $i$ on $j_2$
and writes the $i$-th element of the list to $j_2$, overwriting $i$.  The TM
does not terminate for out-of-bounds access, which of course we will never
attempt. Again the parameter $z$ is a generic terminator symbol.
\<close>

definition tm_nth_inplace :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_nth_inplace j1 j2 z \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j2 \<noteq> \<box> DO
      tm_decr j2 ;;
      tm_right_until j1 {z} ;;
      tm_right j1
    DONE ;;
    tm_cp_until j1 j2 {z} ;;
    tm_cr j2 ;;
    tm_cr j1"

lemma tm_nth_inplace_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j2" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_nth_inplace j1 j2 \<bar>)"
  unfolding tm_nth_inplace_def
  using assms tm_decr_tm tm_right_until_tm tm_right_tm tm_cp_until_tm tm_cr_tm Nil_tm
  by (simp add: assms(1) turing_machine_loop_turing_machine)

locale turing_machine_nth_inplace =
  fixes j1 j2 :: tapeidx
begin

definition "tmL1 \<equiv> tm_decr j2"
definition "tmL2 \<equiv> tmL1 ;; tm_right_until j1 {\<bar>}"
definition "tmL3 \<equiv> tmL2 ;; tm_right j1"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j2 \<noteq> \<box> DO tmL3 DONE"
definition "tm2 \<equiv> tmL ;; tm_cp_until j1 j2 {\<bar>}"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"
definition "tm4 \<equiv> tm3 ;; tm_cr j1"

lemma tm4_eq_tm_nth_inplace: "tm4 = tm_nth_inplace j1 j2 \<bar>"
  unfolding tmL1_def tmL2_def tmL3_def tmL_def tm2_def tm3_def tm4_def tm_nth_inplace_def
  by simp

context
  fixes tps0 :: "tape list" and k idx :: nat and ns :: "nat list"
  assumes jk: "j1 < k" "j2 < k" "0 < j2" "j1 \<noteq> j2" "length tps0 = k"
    and idx: "idx < length ns"
    and tps0:
      "tps0 ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
      "tps0 ! j2 = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
begin

definition "tpsL t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take t ns))),
   j2 := (\<lfloor>idx - t\<rfloor>\<^sub>N, 1)]"

definition "tpsL1 t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take t ns))),
   j2 := (\<lfloor>idx - t - 1\<rfloor>\<^sub>N, 1)]"

lemma tmL1 [transforms_intros]:
  assumes "ttt = 8 + 2 * nlength (idx - t)"
  shows "transforms tmL1 (tpsL t) ttt (tpsL1 t)"
  unfolding tmL1_def by (tform tps: tpsL_def tpsL1_def jk time: assms)

definition "tpsL2 t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, nllength (take (Suc t) ns)),
   j2 := (\<lfloor>idx - t - 1\<rfloor>\<^sub>N, 1)]"

lemma tmL2:
  assumes "t < length ns" and "ttt = 8 + 2 * nlength (idx - t) + Suc (nlength (ns ! t))"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def
proof (tform tps: jk tpsL1_def tpsL2_def time: assms(2))
  let ?l = "nlength (ns ! t)"
  show "rneigh (tpsL1 t ! j1) {\<bar>} ?l"
  proof -
    have "tpsL1 t ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take t ns)))"
      using tpsL1_def jk by (simp only: nth_list_update_eq nth_list_update_neq)
    then show ?thesis
      using assms(1) nlcontents_rneigh_4 by simp
  qed
  show "tpsL2 t = (tpsL1 t)[j1 := tpsL1 t ! j1 |+| nlength (ns ! t)]"
    (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using tpsL1_def tpsL2_def jk by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      consider "i = j1" | "i = j2" | "i \<noteq> j1 \<and> i \<noteq> j2"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using that tpsL1_def tpsL2_def jk nllength_take_Suc[OF assms(1)] by simp
      next
        case 2
        then show ?thesis
          using that tpsL1_def tpsL2_def jk
          by (simp only: nth_list_update_eq nth_list_update_neq' length_list_update)
      next
        case 3
        then show ?thesis
          using that tpsL1_def tpsL2_def jk
          by (simp only: nth_list_update_eq jk nth_list_update_neq' length_list_update)
      qed
    qed
  qed
qed

lemma tmL2' [transforms_intros]:
  assumes "t < length ns" and "ttt = 9 + 2 * nlength idx + nlength (Max (set ns))"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
proof -
  let ?ttt = "8 + 2 * nlength (idx - t) + Suc (nlength (ns ! t))"
  have "transforms tmL2 (tpsL t) ?ttt (tpsL2 t)"
    using tmL2 assms by simp
  moreover have "ttt \<ge> ?ttt"
  proof -
    have "nlength (idx - t) \<le> nlength idx"
      using nlength_mono by simp
    moreover have "nlength (ns ! t) \<le> nlength (Max (set ns))"
      using nlength_mono assms by simp
    ultimately show ?thesis
      using assms(2) by simp
  qed
  ultimately show ?thesis
    using transforms_monotone by simp
qed

definition "tpsL3 t \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take (Suc t) ns))),
   j2 := (\<lfloor>idx - t - 1\<rfloor>\<^sub>N, 1)]"

lemma tmL3:
  assumes "t < length ns" and "ttt = 10 + 2 * nlength idx + nlength (Max (set ns))"
  shows "transforms tmL3 (tpsL t) ttt (tpsL3 t)"
  unfolding tmL3_def
proof (tform tps: jk tpsL2_def tpsL3_def assms(1) time: assms(2))
  show "tpsL3 t = (tpsL2 t)[j1 := tpsL2 t ! j1 |+| 1]"
    using tpsL3_def tpsL2_def jk tps0
    by (metis Groups.add_ac(2) fst_conv list_update_overwrite list_update_swap nth_list_update nth_list_update_neq
      plus_1_eq_Suc snd_conv)
qed

lemma tpsL3_eq_tpsL: "tpsL3 t = tpsL (Suc t)"
  using tpsL3_def tpsL_def by simp

lemma tmL:
  assumes "ttt = idx * (12 + 2 * nlength idx + nlength (Max (set ns))) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL idx)"
  unfolding tmL_def
proof (tform)
  let ?t = "10 + 2 * nlength idx + nlength (Max (set ns))"
  show "\<And>t. t < idx \<Longrightarrow> transforms tmL3 (tpsL t) ?t (tpsL (Suc t))"
    using tmL3 tpsL3_eq_tpsL idx by simp
  show "read (tpsL t) ! j2 \<noteq> \<box>" if "t < idx" for t
  proof -
    have "tpsL t ! j2 = (\<lfloor>idx - t\<rfloor>\<^sub>N, 1)"
      using tpsL_def jk by simp
    then have "read (tpsL t) ! j2 = \<lfloor>idx - t\<rfloor>\<^sub>N 1"
      using tapes_at_read' jk tpsL_def by (metis fst_conv length_list_update snd_conv)
    moreover have "idx - t > 0"
      using that by simp
    ultimately show "read (tpsL t) ! j2 \<noteq> \<box>"
      using ncontents_1_blank_iff_zero by simp
  qed
  show "\<not> read (tpsL idx) ! j2 \<noteq> \<box>"
  proof -
    have "tpsL idx ! j2 = (\<lfloor>idx - idx\<rfloor>\<^sub>N, 1)"
      using tpsL_def jk by simp
    then have "read (tpsL idx) ! j2 = \<lfloor>idx - idx\<rfloor>\<^sub>N 1"
      using tapes_at_read' jk tpsL_def by (metis fst_conv length_list_update snd_conv)
    then show ?thesis
      using ncontents_1_blank_iff_zero by simp
  qed
  show "idx * (10 + 2 * nlength idx + nlength (Max (set ns)) + 2) + 1 \<le> ttt"
    using assms by simp
qed

definition "tps1 \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take idx ns))),
   j2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tps1_eq_tpsL: "tps1 = tpsL idx"
  using tps1_def tpsL_def by simp

lemma tps0_eq_tpsL: "tps0 = tpsL 0"
  using tps0 tpsL_def nllength_Nil by (metis One_nat_def list_update_id minus_nat.diff_0 take0)

lemma tmL' [transforms_intros]:
  assumes "ttt = idx * (12 + 2 * nlength idx + nlength (Max (set ns))) + 1"
  shows "transforms tmL tps0 ttt tps1"
  using tmL assms tps0_eq_tpsL tps1_eq_tpsL by simp

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, nllength (take (Suc idx) ns)),
   j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, Suc (nlength (ns ! idx)))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = idx * (12 + 2 * nlength idx + nlength (Max (set ns))) + 2 + nlength (ns ! idx)"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk tps2_def tps1_def time: assms)
  have "tps1 ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take idx ns)))"
    using tps1_def tps0 jk by simp
  then show "rneigh (tps1 ! j1) {\<bar>} (nlength (ns ! idx))"
    by (simp add: idx nlcontents_rneigh_4)
  show "tps2 = tps1
    [j1 := tps1 ! j1 |+| nlength (ns ! idx),
     j2 := implant (tps1 ! j1) (tps1 ! j2) (nlength (ns ! idx))]"
     (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using tps1_def tps2_def by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      consider "i = j1" | "i = j2" | "i \<noteq> j1 \<and> i \<noteq> j2"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using that tps1_def tps2_def jk nllength_take_Suc idx by simp
      next
        case 2
        then have lhs: "?l ! i = (\<lfloor>ns ! idx\<rfloor>\<^sub>N, Suc (nlength (ns ! idx)))"
          using tps2_def jk by simp
        let ?i = "Suc (nllength (take idx ns))"
        have i1: "?i > 0"
          by simp
        have "nlength (ns ! idx) + (?i - 1) \<le> nllength ns"
          using idx by (simp add: add.commute less_or_eq_imp_le nllength_take)
        then have i2: "nlength (ns ! idx) + (?i - 1) \<le> length (numlist ns)"
          using nllength_def by simp
        have "?r ! i = implant (tps1 ! j1) (tps1 ! j2) (nlength (ns ! idx))"
          using 2 tps1_def jk by simp
        also have "... = implant (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, ?i) (\<lfloor>0\<rfloor>\<^sub>N, 1) (nlength (ns ! idx))"
        proof -
          have "tps1 ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (take idx ns)))"
            using tps1_def jk by simp
          moreover have "tps1 ! j2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
            using tps1_def jk by simp
          ultimately show ?thesis
            by simp
        qed
        also have "... = (\<lfloor>[] @ (take (nlength (ns ! idx)) (drop (?i - 1) (numlist ns)))\<rfloor>, Suc (length []) + nlength (ns ! idx))"
          using implant_contents[OF i1 i2] by (metis One_nat_def list.size(3) ncontents_0 nlcontents_def)
        finally have "?r ! i = (\<lfloor>[] @ (take (nlength (ns ! idx)) (drop (?i - 1) (numlist ns)))\<rfloor>, Suc (length []) + nlength (ns ! idx))" .
        then have "?r ! i = (\<lfloor>take (nlength (ns ! idx)) (drop (nllength (take idx ns)) (numlist ns))\<rfloor>, Suc (nlength (ns ! idx)))"
          by simp
        then have "?r ! i = (\<lfloor>canrepr (ns ! idx)\<rfloor>, Suc (nlength (ns ! idx)))"
          using take_drop_numlist'[OF idx] by simp
        then show ?thesis
          using lhs by simp
      next
        case 3
        then show ?thesis
          using that tps1_def tps2_def jk by simp
      qed
    qed
  qed
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, nllength (take (Suc idx) ns)),
   j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = idx * (12 + 2 * nlength idx + nlength (Max (set ns))) + 5 + 2 * nlength (ns ! idx)"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
  by (tform tps: clean_tape_ncontents jk tps2_def tps3_def time: assms tps2_def jk)

definition "tps4 \<equiv> tps0
  [j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"

lemma tm4:
  assumes "ttt = idx * (12 + 2 * nlength idx + nlength (Max (set ns))) + 7 + 2 * nlength (ns ! idx) + nllength (take (Suc idx) ns)"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: clean_tape_nlcontents jk tps3_def tps4_def time: assms jk tps3_def)
  show "tps4 = tps3[j1 := tps3 ! j1 |#=| 1]"
    using tps4_def tps3_def jk tps0(1) list_update_id[of tps0 j1] by (simp add: list_update_swap)
qed

lemma tm4':
  assumes "ttt = 18 * nllength ns ^ 2 + 12"
  shows "transforms tm4 tps0 ttt tps4"
proof -
  let ?ttt = "idx * (12 + 2 * nlength idx + nlength (Max (set ns))) + 7 + 2 * nlength (ns ! idx) + nllength (take (Suc idx) ns)"

  have 1: "idx \<le> nllength ns"
    using idx length_le_nllength by (meson le_trans less_or_eq_imp_le)
  then have 2: "nlength idx \<le> nllength ns"
    using nlength_mono nlength_le_n by (meson dual_order.trans)
  have "ns \<noteq> []"
    using idx by auto
  then have 3: "nlength (Max (set ns)) \<le> nllength ns"
    using member_le_nllength by simp
  have 4: "nlength (ns ! idx) \<le> nllength ns"
    using idx member_le_nllength by simp
  have 5: "nllength (take (Suc idx) ns) \<le> nllength ns"
    by (metis Suc_le_eq add_Suc_right idx nllength_take nllength_take_Suc)

  have "?ttt \<le> idx * (12 + 2 * nllength ns + nllength ns) + 7 + 2 * nllength ns + nllength ns"
    using 2 3 4 5 by (meson add_le_mono le_eq_less_or_eq mult_le_mono2)
  also have "... = idx * (12 + 3 * nllength ns) + 7 + 3 * nllength ns"
    by simp
  also have "... \<le> idx * (12 + 3 * nllength ns) + (12 + 3 * nllength ns)"
    by simp
  also have "... = Suc idx * (12 + 3 * nllength ns)"
    by simp
  also have "... \<le> Suc (nllength ns) * (12 + 3 * nllength ns)"
    using 1 by simp
  also have "... = nllength ns * (12 + 3 * nllength ns) + (12 + 3 * nllength ns)"
    by simp
  also have "... = 12 * nllength ns + 3 * nllength ns ^ 2 + 12 + 3 * nllength ns"
    by algebra
  also have "... = 15 * nllength ns + 3 * nllength ns ^ 2 + 12"
    by simp
  also have "... \<le> 18 * nllength ns ^ 2 + 12"
    by (simp add: power2_eq_square)
  finally have "?ttt \<le> 18 * nllength ns ^ 2 + 12" .
  then show ?thesis
    using tm4 transforms_monotone assms by simp
qed

end  (* context tps0 *)

end  (* locale turing_machine_nth_inplace *)

lemma transforms_tm_nth_inplace_4I [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k idx :: nat and ns :: "nat list"
  assumes "j1 < k" "j2 < k" "0 < j2" "j1 \<noteq> j2" "length tps = k"
    and "idx < length ns"
  assumes
    "tps ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! j2 = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 18 * nllength ns ^ 2 + 12"
  assumes "tps' = tps
    [j2 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_nth_inplace j1 j2 \<bar>) tps ttt tps'"
proof -
  interpret loc: turing_machine_nth_inplace j1 j2 .
  show ?thesis
    using assms loc.tm4_eq_tm_nth_inplace loc.tm4' loc.tps4_def by simp
qed

text \<open>
The next Turing machine expects a list on tape $j_1$ and an index $i$ on tape
$j_2$. It writes the $i$-th element of the list to tape $j_3$. Like the previous
TM, it will not terminate on out-of-bounds access, and $z$ is a parameter for
the symbol that terminates the list elements.
\<close>

definition tm_nth :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> symbol \<Rightarrow> machine" where
  "tm_nth j1 j2 j3 z \<equiv>
    tm_copyn j2 j3 ;;
    tm_nth_inplace j1 j3 z"

lemma tm_nth_tm:
  assumes "k \<ge> 2" and "G \<ge> 4" and "0 < j2" "0 < j1" "j1 < k" "j2 < k" "0 < j3" "j3 < k" "j2 \<noteq> j3"
  shows "turing_machine k G (tm_nth j1 j2 j3 \<bar>)"
  unfolding tm_nth_def using tm_copyn_tm tm_nth_inplace_tm assms by simp

lemma transforms_tm_nth_4I [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and k idx :: nat and ns :: "nat list"
  assumes "j1 < k" "j2 < k" "j3 < k" "0 < j1" "0 < j2" "0 < j3" "j1 \<noteq> j2" "j2 \<noteq> j3" "j1 \<noteq> j3"
    and "length tps = k"
    and "idx < length ns"
  assumes
    "tps ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! j2 = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 21 * nllength ns ^ 2 + 26"
  assumes "tps' = tps
    [j3 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_nth j1 j2 j3 \<bar>) tps ttt tps'"
proof -
  let ?ttt = "14 + 3 * (nlength idx + nlength 0) + (18 * (nllength ns)\<^sup>2 + 12)"
  have "transforms (tm_nth j1 j2 j3 \<bar>) tps ?ttt tps'"
    unfolding tm_nth_def
  proof (tform tps: assms(1-11))
    show "tps ! j2 = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
      using assms by simp
    show "tps ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      using assms by simp
    show "tps[j3 := (\<lfloor>idx\<rfloor>\<^sub>N, 1)] ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
      using assms by simp
    then show "tps' = tps
      [j3 := (\<lfloor>idx\<rfloor>\<^sub>N, 1),
       j3 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1)]"
      using assms by (metis One_nat_def list_update_overwrite)
  qed
  moreover have "?ttt \<le> ttt"
  proof -
    have "nlength idx \<le> idx"
      using nlength_le_n by simp
    then have "nlength idx \<le> length ns"
      using assms(11) by simp
    then have "nlength idx \<le> nllength ns"
      using length_le_nllength by (meson order.trans)
    then have "nlength idx \<le> nllength ns ^ 2"
      by (meson le_refl order_trans power2_nat_le_imp_le)
    moreover have "?ttt = 3 * nlength idx + 18 * (nllength ns)\<^sup>2 + 26"
      by simp
    ultimately show ?thesis
      using assms(15) by simp
  qed
  ultimately show ?thesis
    using transforms_monotone by simp
qed


subsection \<open>Finding the previous position of an element\<close>

text \<open>
The Turing machine in this section implements a slightly peculiar functionality,
which we will start using only in Section~\ref{s:Reducing}. Given a list of
numbers and an index $i$ it determines the greatest index less than $i$ where
the list contains the same element as in position $i$. If no such element
exists, it returns $i$. Formally:
\<close>

definition previous :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "previous ns idx \<equiv>
    if \<exists>i<idx. ns ! i = ns ! idx
    then GREATEST i. i < idx \<and> ns ! i = ns ! idx
    else idx"

lemma previous_less:
  assumes "\<exists>i<idx. ns ! i = ns ! idx"
  shows "previous ns idx < idx \<and> ns ! (previous ns idx) = ns ! idx"
proof -
  let ?P = "\<lambda>i. i < idx \<and> ns ! i = ns ! idx"
  have "previous ns idx = (GREATEST i. ?P i)"
    using assms previous_def by simp
  moreover have "\<forall>y. ?P y \<longrightarrow> y \<le> idx"
    by simp
  ultimately show ?thesis
    using GreatestI_ex_nat[OF assms, of idx] by simp
qed

lemma previous_eq: "previous ns idx = idx \<longleftrightarrow> \<not> (\<exists>i<idx. ns ! i = ns ! idx)"
  using previous_def nat_less_le previous_less by simp

lemma previous_le: "previous ns idx \<le> idx"
  using previous_eq previous_less by (metis less_or_eq_imp_le)

text \<open>
The following Turing machine expects the list on tape $j_1$ and the index on
tape $j_2$. It outputs the result on tape $j_2 + 5$. The tapes $j_2 + 1, \dots,
j_2 + 4$ are scratch space.
\<close>

definition tm_prev :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_prev j1 j2 \<equiv>
    tm_copyn j2 (j2 + 5) ;;
    tm_nth j1 j2 (j2 + 1) \<bar> ;;
    WHILE tm_equalsn (j2 + 2) j2 (j2 + 4) ; \<lambda>rs. rs ! (j2 + 4) = \<box> DO
      tm_nth j1 (j2 + 2) (j2 + 3) \<bar> ;;
      tm_equalsn (j2 + 1) (j2 + 3) (j2 + 4) ;;
      tm_setn (j2 + 3) 0 ;;
      IF \<lambda>rs. rs ! (j2 + 4) \<noteq> \<box> THEN
        tm_setn (j2 + 4) 0 ;;
        tm_copyn (j2 + 2) (j2 + 5)
      ELSE
        []
      ENDIF ;;
      tm_incr (j2 + 2)
    DONE ;;
    tm_erase_cr (j2 + 1) ;;
    tm_erase_cr (j2 + 2) ;;
    tm_erase_cr (j2 + 4)"

lemma tm_prev_tm:
  assumes "k \<ge> j2 + 6" and "G \<ge> 4" and "j1 < j2" and "0 < j1"
  shows "turing_machine k G (tm_prev j1 j2)"
  unfolding tm_prev_def
  using assms tm_copyn_tm tm_nth_tm tm_equalsn_tm tm_setn_tm tm_incr_tm Nil_tm tm_erase_cr_tm
    turing_machine_loop_turing_machine turing_machine_branch_turing_machine
  by simp

locale turing_machine_prev =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_copyn j2 (j2 + 5)"
definition "tm2 \<equiv> tm1 ;; tm_nth j1 j2 (j2 + 1) \<bar>"
definition "tmC \<equiv> tm_equalsn (j2 + 2) j2 (j2 + 4)"
definition "tmB1 \<equiv> tm_nth j1 (j2 + 2) (j2 + 3) \<bar>"
definition "tmB2 \<equiv> tmB1 ;; tm_equalsn (j2 + 1) (j2 + 3) (j2 + 4)"
definition "tmB3 \<equiv> tmB2 ;; tm_setn (j2 + 3) 0"
definition "tmI1 \<equiv> tm_setn (j2 + 4) 0"
definition "tmI2 \<equiv> tmI1 ;; tm_copyn (j2 + 2) (j2 + 5)"
definition "tmI \<equiv> IF \<lambda>rs. rs ! (j2 + 4) \<noteq> \<box> THEN tmI2 ELSE [] ENDIF"
definition "tmB4 \<equiv> tmB3 ;; tmI"
definition "tmB5 \<equiv> tmB4 ;; tm_incr (j2 + 2)"
definition "tmL \<equiv> WHILE tmC ; \<lambda>rs. rs ! (j2 + 4) = \<box> DO tmB5 DONE"
definition "tm3 \<equiv> tm2 ;; tmL"
definition "tm4 \<equiv> tm3 ;; tm_erase_cr (j2 + 1)"
definition "tm5 \<equiv> tm4 ;; tm_erase_cr (j2 + 2)"
definition "tm6 \<equiv> tm5 ;; tm_erase_cr (j2 + 4)"

lemma tm6_eq_tm_prev: "tm6 = tm_prev j1 j2"
  unfolding tm_prev_def tm3_def tmL_def tmB5_def tmB4_def tmI_def tmI2_def tmI1_def tmB3_def
    tmB2_def tmB1_def tmC_def tm2_def tm1_def tm4_def tm5_def tm6_def
  by simp

context
  fixes tps0 :: "tape list" and k idx :: nat and ns :: "nat list"
  assumes jk: "0 < j1" "j1 < j2" "j2 + 6 \<le> k" "length tps0 = k"
    and idx: "idx < length ns"
    and tps0:
      "tps0 ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
      "tps0 ! j2 = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j2 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j2 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j2 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j2 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j2 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j2 + 5 := (\<lfloor>idx\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 14 + 3 * nlength idx"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def by (tform tps: jk idx tps0 tps1_def assms nlength_0)

definition "tps2 \<equiv> tps0
 [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
  j2 + 5 := (\<lfloor>idx\<rfloor>\<^sub>N, 1)]"

lemma tm2:
  assumes "ttt = 14 + 3 * nlength idx + (21 * (nllength ns)\<^sup>2 + 26)"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def by (tform tps: jk idx tps0 tps1_def tps2_def time: assms)

definition rv :: "nat \<Rightarrow> nat" where
  "rv t \<equiv> if \<exists>i<t. ns ! i = ns ! idx then GREATEST i. i < t \<and> ns ! i = ns ! idx else idx"

lemma rv_0: "rv 0 = idx"
  using rv_def by simp

lemma rv_le: "rv t \<le> max t idx"
proof (cases "\<exists>i<t. ns ! i = ns ! idx")
  case True
  let ?Q = "\<lambda>i. i < t \<and> ns ! i = ns ! idx"
  have rvt: "rv t = Greatest ?Q"
    using True rv_def by simp
  moreover have "?Q (Greatest ?Q)"
  proof (rule GreatestI_ex_nat)
    show "\<exists>k<t. ns ! k = ns ! idx"
      using True by simp
    show "\<And>y. y < t \<and> ns ! y = ns ! idx \<Longrightarrow> y \<le> t"
      by simp
  qed
  ultimately have "?Q (rv t)"
    by simp
  then have "rv t < t"
    by simp
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
    using rv_def by auto
qed

lemma rv_change:
  assumes "t < length ns" and "idx < length ns" and "ns ! t = ns ! idx"
  shows "rv (Suc t) = t"
proof -
  let ?P = "\<lambda>i. i < Suc t \<and> ns ! i = ns ! idx"
  have "rv (Suc t) = Greatest ?P"
    using assms(3) rv_def by auto
  moreover have "Greatest ?P = t"
  proof (rule Greatest_equality)
    show "t < Suc t \<and> ns ! t = ns ! idx"
      using assms(3) by simp
    show "\<And>y. y < Suc t \<and> ns ! y = ns ! idx \<Longrightarrow> y \<le> t"
      using assms by simp
  qed
  ultimately show ?thesis
    by simp
qed

lemma rv_keep:
  assumes "t < length ns" and "idx < length ns" and "ns ! t \<noteq> ns ! idx"
  shows "rv (Suc t) = rv t"
proof (cases "\<exists>i<Suc t. ns ! i = ns ! idx")
  case True
  let ?Q = "\<lambda>i. i < t \<and> ns ! i = ns ! idx"
  have ex: "\<exists>i<t. ns ! i = ns ! idx"
    using True assms(3) less_antisym by blast
  then have rvt: "rv t = Greatest ?Q"
    using rv_def by simp
  moreover have "?Q (Greatest ?Q)"
  proof (rule GreatestI_ex_nat)
    show "\<exists>k<t. ns ! k = ns ! idx"
      using ex .
    show "\<And>y. y < t \<and> ns ! y = ns ! idx \<Longrightarrow> y \<le> t"
      by simp
  qed
  ultimately have "?Q (rv t)"
    by simp

  let ?P = "\<lambda>i. i < Suc t \<and> ns ! i = ns ! idx"
  have "rv (Suc t) = Greatest ?P"
    using True rv_def by simp
  moreover have "Greatest ?P = rv t"
  proof (rule Greatest_equality)
    show "rv t < Suc t \<and> ns ! rv t = ns ! idx"
      using `?Q (rv t)` by simp
    show "y \<le> rv t" if "y < Suc t \<and> ns ! y = ns ! idx" for y
    proof -
      have "?Q y"
        using True assms(3) less_antisym that by blast
      moreover have "\<forall>y. ?Q y \<longrightarrow> y \<le> t"
        by simp
      ultimately have "y \<le> Greatest ?Q"
        using Greatest_le_nat[of ?Q] by blast
      then show ?thesis
        using rvt by simp
    qed
  qed
  ultimately show ?thesis
    by simp
next
  case False
  then show ?thesis
    using rv_def by auto
qed

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>rv t\<rfloor>\<^sub>N, 1)]"

lemma tpsL_eq_tps2: "tpsL 0 = tps2"
  using tpsL_def tps2_def tps0 jk rv_0
  by (metis add_eq_self_zero add_left_imp_eq gr_implies_not0 less_numeral_extra(1)
    list_update_id list_update_swap one_add_one)

definition tpsC :: "nat \<Rightarrow> tape list" where
  "tpsC t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 4 := (\<lfloor>t = idx\<rfloor>\<^sub>B, 1),
     j2 + 5 := (\<lfloor>rv t\<rfloor>\<^sub>N, 1)]"

lemma tmC:
  assumes "ttt = 3 * nlength (min t idx) + 7"
  shows "transforms tmC (tpsL t) ttt (tpsC t)"
  unfolding tmC_def by (tform tps: jk idx tps0 tpsL_def tpsC_def time: assms)

lemma tmC' [transforms_intros]:
  assumes "ttt = 3 * nllength ns ^ 2 + 7" and "t \<le> idx"
  shows "transforms tmC (tpsL t) ttt (tpsC t)"
proof -
  have "nlength (min t idx) \<le> nllength ns"
    using idx assms(2) by (metis le_trans length_le_nllength less_or_eq_imp_le min_absorb1 nlength_le_n)
  then have "nlength (min t idx) \<le> nllength ns ^ 2"
    by (metis le_square min.absorb2 min.coboundedI1 power2_eq_square)
  then have "3 * nlength (min t idx) + 7 \<le> 3 * nllength ns ^ 2 + 7"
    by simp
  then show ?thesis
    using tmC assms(1) transforms_monotone by blast
qed

lemma condition_tpsC: "(read (tpsC t)) ! (j2 + 4) \<noteq> \<box> \<longleftrightarrow> t = idx"
  using tpsC_def read_ncontents_eq_0 jk by simp

definition "tpsB1 t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 3 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1),
     j2 + 4 := (\<lfloor>t = idx\<rfloor>\<^sub>B, 1),
     j2 + 5 := (\<lfloor>rv t\<rfloor>\<^sub>N, 1)]"

lemma tmB1 [transforms_intros]:
  assumes "ttt = 21 * (nllength ns)\<^sup>2 + 26" and "t < idx"
  shows "transforms tmB1 (tpsC t) ttt (tpsB1 t)"
  unfolding tmB1_def by (tform tps: jk idx tps0 tpsC_def tpsB1_def time: assms idx)

definition "tpsB2 t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 3 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1),
     j2 + 4 := (\<lfloor>ns ! idx = ns ! t\<rfloor>\<^sub>B, 1),
     j2 + 5 := (\<lfloor>rv t\<rfloor>\<^sub>N, 1)]"

lemma tmB2:
  assumes "ttt = 21 * (nllength ns)\<^sup>2 + 26 + (3 * nlength (min (ns ! idx) (ns ! t)) + 7)"
    and "t < idx"
  shows "transforms tmB2 (tpsC t) ttt (tpsB2 t)"
  unfolding tmB2_def
proof (tform tps: tpsB1_def jk assms(2) time: assms(1))
  show "tpsB2 t = (tpsB1 t)[j2 + 4 := (\<lfloor>ns ! idx = ns ! t\<rfloor>\<^sub>B, 1)]"
    unfolding tpsB2_def tpsB1_def by (simp add: list_update_swap[of "j2 + 4"])
qed

lemma tmB2' [transforms_intros]:
  assumes "ttt = 24 * (nllength ns)\<^sup>2 + 33" and "t < idx"
  shows "transforms tmB2 (tpsC t) ttt (tpsB2 t)"
proof -
  let ?ttt = "21 * (nllength ns)\<^sup>2 + 26 + (3 * nlength (min (ns ! idx) (ns ! t)) + 7)"
  have "?ttt = 21 * (nllength ns)\<^sup>2 + 33 + 3 * nlength (min (ns ! idx) (ns ! t))"
    by simp
  also have "... \<le> 21 * (nllength ns)\<^sup>2 + 33 + 3 * nllength ns"
    using nlength_min_le_nllength idx assms(2) by simp
  also have "... \<le> 21 * (nllength ns)\<^sup>2 + 33 + 3 * nllength ns ^ 2"
    by (simp add: power2_eq_square)
  also have "... = 24 * (nllength ns)\<^sup>2 + 33"
    by simp
  finally have "?ttt \<le> 24 * (nllength ns)\<^sup>2 + 33" .
  then show ?thesis
    using assms tmB2 transforms_monotone by blast
qed

definition "tpsB3 t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 4 := (\<lfloor>ns ! idx = ns ! t\<rfloor>\<^sub>B, 1),
     j2 + 5 := (\<lfloor>rv t\<rfloor>\<^sub>N, 1)]"

lemma condition_tpsB3: "(read (tpsB3 t)) ! (j2 + 4) \<noteq> \<box> \<longleftrightarrow> ns ! idx = ns ! t"
  using tpsB3_def read_ncontents_eq_0 jk by simp

lemma tmB3 [transforms_intros]:
  assumes "ttt = 24 * (nllength ns)\<^sup>2 + 33 + (10 + 2 * nlength (ns ! t))" and "t < idx"
  shows "transforms tmB3 (tpsC t) ttt (tpsB3 t)"
  unfolding tmB3_def
proof (tform tps: assms(2) tpsB2_def jk time: assms(1))
  show "tpsB3 t = (tpsB2 t)[j2 + 3 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using tpsB2_def tpsB3_def tps0 by simp
    show "?l ! j = ?r ! j" if "j < length ?l" for j
    proof -
      consider "j = j1" | "j = j2" | "j = j2 + 1" | "j = j2 + 2" | "j = j2 + 3" | "j = j2 + 4" | "j = j2 + 5"
        | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j \<noteq> j2 + 1 \<and> j \<noteq> j2 + 2 \<and> j \<noteq> j2 + 3 \<and> j \<noteq> j2 + 4 \<and> j \<noteq> j2 + 5"
        by auto
      then show ?thesis
        using tpsB2_def tpsB3_def tps0 jk
        by (cases, simp_all only: nth_list_update_eq nth_list_update_neq length_list_update, metis nth_list_update_neq)
    qed
  qed
qed

definition "tpsI0 t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 4 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>rv t\<rfloor>\<^sub>N, 1)]"

definition "tpsI1 t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>rv t\<rfloor>\<^sub>N, 1)]"

lemma tmI1 [transforms_intros]:
  assumes "t < idx" and "ns ! idx = ns ! t"
  shows "transforms tmI1 (tpsB3 t) 12 (tpsI1 t)"
  unfolding tmI1_def
proof (tform tps: tpsB3_def jk assms(2) time: assms nlength_1_simp)
  show "tpsI1 t = (tpsB3 t)[j2 + 4 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using tpsB3_def tpsI1_def tps0 jk by simp
    show "?l ! j = ?r ! j" if "j < length ?l" for j
    proof -
      consider "j = j1" | "j = j2" | "j = j2 + 1" | "j = j2 + 2" | "j = j2 + 3" | "j = j2 + 4" | "j = j2 + 5"
        | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j \<noteq> j2 + 1 \<and> j \<noteq> j2 + 2 \<and> j \<noteq> j2 + 3 \<and> j \<noteq> j2 + 4 \<and> j \<noteq> j2 + 5"
        by auto
      then show ?thesis
        using tpsB3_def tpsI1_def tps0 jk
        by (cases, simp_all only: nth_list_update_eq nth_list_update_neq length_list_update, metis nth_list_update_neq)
    qed
  qed
qed

definition "tpsI2 t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>t\<rfloor>\<^sub>N, 1)]"

lemma tmI2 [transforms_intros]:
  assumes "ttt = 26 + 3 * nlength t + 3 * nlength (rv t)"
    and "t < idx"
    and "ns ! idx = ns ! t"
  shows "transforms tmI2 (tpsB3 t) ttt (tpsI2 t)"
  unfolding tmI2_def
proof (tform tps: assms(2,3) tpsI1_def jk time: assms(1))
  show "tpsI2 t = (tpsI1 t)[j2 + 5 := (\<lfloor>t\<rfloor>\<^sub>N, 1)]"
    (is "?l = ?r")
  proof (rule nth_equalityI)
    show "length ?l = length ?r"
      using tpsI1_def tpsI2_def tps0 by simp
    show "?l ! j = ?r ! j" if "j < length ?l" for j
    proof -
      consider "j = j1" | "j = j2" | "j = j2 + 1" | "j = j2 + 2" | "j = j2 + 3" | "j = j2 + 4" | "j = j2 + 5"
        | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j \<noteq> j2 + 1 \<and> j \<noteq> j2 + 2 \<and> j \<noteq> j2 + 3 \<and> j \<noteq> j2 + 4 \<and> j \<noteq> j2 + 5"
        by auto
      then show ?thesis
        using tpsI1_def tpsI2_def tps0 jk assms(2,3)
        by (cases, simp_all only: One_nat_def nth_list_update_eq nth_list_update_neq length_list_update list_update_overwrite)
    qed
  qed
qed

definition "tpsI t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>t\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>rv (Suc t)\<rfloor>\<^sub>N, 1)]"

lemma tmI [transforms_intros]:
  assumes "ttt = 28 + 6 * nllength ns" and "t < idx"
  shows "transforms tmI (tpsB3 t) ttt (tpsI t)"
  unfolding tmI_def
proof (tform tps: assms)
  let ?tT = "26 + 3 * nlength t + 3 * nlength (rv t)"
  have *: "(ns ! idx = ns ! t) = (read (tpsB3 t) ! (j2 + 4) \<noteq> \<box>)"
    using condition_tpsB3 by simp
  then show "read (tpsB3 t) ! (j2 + 4) \<noteq> \<box> \<Longrightarrow> ns ! idx = ns ! t"
    by simp
  have "ns ! idx = ns ! t \<Longrightarrow> rv (Suc t) = t"
    using rv_change idx assms(2) by simp
  then show "read (tpsB3 t) ! (j2 + 4) \<noteq> \<box> \<Longrightarrow> tpsI t = tpsI2 t"
    using tpsI_def tpsI2_def * by simp

  have "ns ! idx \<noteq> ns ! t \<Longrightarrow> rv (Suc t) = rv t"
    using rv_keep idx assms(2) by simp
  then have "ns ! idx \<noteq> ns ! t \<Longrightarrow> tpsI t = tpsB3 t"
    using tpsI_def tpsB3_def tps0 jk
    by (smt (verit, ccfv_SIG) add_left_imp_eq list_update_id list_update_swap numeral_eq_iff
      one_eq_numeral_iff semiring_norm(83) semiring_norm(87))
  then show "\<not> read (tpsB3 t) ! (j2 + 4) \<noteq> \<box> \<Longrightarrow> tpsI t = tpsB3 t"
    using * by simp
  show "26 + 3 * nlength t + 3 * nlength (rv t) + 2 \<le> ttt"
  proof -
    have "26 + 3 * nlength t + 3 * nlength (rv t) + 2 = 28 + 3 * nlength t + 3 * nlength (rv t)"
      by simp
    also have "... \<le> 28 + 3 * nlength idx + 3 * nlength (rv t)"
      using assms(2) nlength_mono by simp
    also have "... \<le> 28 + 3 * nlength idx + 3 * nlength idx"
    proof -
      have "rv t \<le> idx"
        using assms(2) rv_le by (metis less_or_eq_imp_le max_absorb2)
      then show ?thesis
        using nlength_mono by simp
    qed
    also have "... = 28 + 6 * nlength idx"
      by simp
    also have "... \<le> 28 + 6 * nllength ns"
    proof -
      have "nlength idx \<le> nlength (length ns)"
        using idx nlength_mono by simp
      then have "nlength idx \<le> length ns"
        using nlength_le_n by (meson le_trans)
      then have "nlength idx \<le> nllength ns"
        using length_le_nllength le_trans by blast
      then show ?thesis
        by simp
    qed
    finally show ?thesis
      using assms(1) by simp
  qed
qed

lemma tmB4:
  assumes "ttt = 71 + 24 * (nllength ns)\<^sup>2 + 2 * nlength (ns ! t) + 6 * nllength ns"
    and "t < idx"
  shows "transforms tmB4 (tpsC t) ttt (tpsI t)"
  unfolding tmB4_def by (tform tps: assms(2) jk time: assms(1))

lemma tmB4' [transforms_intros]:
  assumes "ttt = 71 + 32 * (nllength ns)\<^sup>2" and "t < idx"
  shows "transforms tmB4 (tpsC t) ttt (tpsI t)"
proof -
  let ?ttt = "71 + 24 * (nllength ns)\<^sup>2 + 2 * nlength (ns ! t) + 6 * nllength ns"
  have "?ttt \<le> 71 + 24 * (nllength ns)\<^sup>2 + 2 * nlength (ns ! t) + 6 * nllength ns ^ 2"
    by (metis add_mono_thms_linordered_semiring(2) le_square mult.commute mult_le_mono1 power2_eq_square)
  also have "... = 71 + 30 * (nllength ns)\<^sup>2 + 2 * nlength (ns ! t)"
    by simp
  also have "... \<le> 71 + 30 * (nllength ns)\<^sup>2 + 2 * nllength ns"
    using member_le_nllength assms(2) idx by simp
  also have "... \<le> 71 + 30 * (nllength ns)\<^sup>2 + 2 * nllength ns ^ 2"
    by (simp add: power2_eq_square)
  also have "... = 71 + 32 * (nllength ns)\<^sup>2"
    by simp
  finally have "?ttt \<le> 71 + 32 * (nllength ns)\<^sup>2" .
  then show ?thesis
    using assms tmB4 transforms_monotone by blast
qed

definition "tpsB5 t \<equiv> tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>rv (Suc t)\<rfloor>\<^sub>N, 1)]"

lemma tmB5:
  assumes "ttt = 76 + 32 * (nllength ns)\<^sup>2 + 2 * nlength t" and "t < idx"
  shows "transforms tmB5 (tpsC t) ttt (tpsB5 t)"
  unfolding tmB5_def
proof (tform tps: assms(2) tpsI_def jk time: assms(1))
  show "tpsB5 t = (tpsI t)[j2 + 2 := (\<lfloor>Suc t\<rfloor>\<^sub>N, 1)]"
    using tpsB5_def tpsI_def
    by (smt (z3) add_left_imp_eq list_update_overwrite list_update_swap numeral_eq_iff semiring_norm(89))
qed

lemma tmB5' [transforms_intros]:
  assumes "ttt = 76 + 34 * (nllength ns)\<^sup>2" and "t < idx"
  shows "transforms tmB5 (tpsC t) ttt (tpsL (Suc t))"
proof -
  have "76 + 32 * (nllength ns)\<^sup>2 + 2 * nlength t \<le> 76 + 32 * (nllength ns)\<^sup>2 + 2 * nllength ns"
    using assms(2) idx length_le_nllength nlength_le_n
    by (meson add_mono_thms_linordered_semiring(2) le_trans less_or_eq_imp_le mult_le_mono2)
  also have "... \<le> 76 + 32 * (nllength ns)\<^sup>2 + 2 * nllength ns ^ 2"
    by (simp add: power2_eq_square)
  also have "... \<le> 76 + 34 * (nllength ns)\<^sup>2"
    by simp
  finally have "76 + 32 * (nllength ns)\<^sup>2 + 2 * nlength t \<le> 76 + 34 * (nllength ns)\<^sup>2" .
  moreover have "tpsL (Suc t) = tpsB5 t"
    using tpsL_def tpsB5_def by simp
  ultimately show ?thesis
    using assms tmB5 transforms_monotone by fastforce
qed

lemma tmL [transforms_intros]:
  assumes "ttt = 125 * nllength ns ^ 3 + 8" and "iidx = idx"
  shows "transforms tmL (tpsL 0) ttt (tpsC iidx)"
  unfolding tmL_def
proof (tform tps: assms)
  let ?tC = "3 * nllength ns ^ 2 + 7"
  let ?tB5 = "76 + 34 * (nllength ns)\<^sup>2"
  show "\<And>t. t < iidx \<Longrightarrow> read (tpsC t) ! (j2 + 4) = \<box>"
    using condition_tpsC assms(2) by fast
  show "read (tpsC iidx) ! (j2 + 4) \<noteq> \<box>"
    using condition_tpsC assms(2) by simp
  have "iidx * (?tC + ?tB5 + 2) + ?tC + 1 = iidx * (37 * (nllength ns)\<^sup>2 + 85) + 3 * (nllength ns)\<^sup>2 + 8"
    by simp
  also have "... \<le> length ns * (37 * (nllength ns)\<^sup>2 + 85) + 3 * (nllength ns)\<^sup>2 + 8"
    using assms(2) idx by simp
  also have "... \<le> nllength ns * (37 * (nllength ns)\<^sup>2 + 85) + 3 * (nllength ns)\<^sup>2 + 8"
    using length_le_nllength by simp
  also have "... = 37 * nllength ns ^ 3 + 85 * nllength ns + 3 * (nllength ns)\<^sup>2 + 8"
    by algebra
  also have "... \<le> 37 * nllength ns ^ 3 + 85 * nllength ns + 3 * nllength ns ^ 3 + 8"
  proof -
    have "nllength ns ^ 2 \<le> nllength ns ^ 3"
      by (metis Suc_eq_plus1 add.commute eq_refl le_add2 neq0_conv numeral_3_eq_3 numerals(2)
        pow_mono power_eq_0_iff zero_less_Suc)
    then show ?thesis
      by simp
  qed
  also have "... \<le> 37 * nllength ns ^ 3 + 85 * nllength ns ^ 3 + 3 * nllength ns ^ 3 + 8"
    by (simp add: power3_eq_cube)
  also have "... = 125 * nllength ns ^ 3 + 8"
    by simp
  finally have "iidx * (?tC + ?tB5 + 2) + ?tC + 1 \<le> 125 * nllength ns ^ 3 + 8" .
  then show "iidx * (?tC + ?tB5 + 2) + ?tC + 1 \<le> ttt"
    using assms(1) by simp
qed

lemma tm2' [transforms_intros]:
  assumes "ttt = 14 + 3 * nlength idx + (21 * (nllength ns)\<^sup>2 + 26)"
  shows "transforms tm2 tps0 ttt (tpsL 0)"
  using tm2 assms tpsL_eq_tps2 by simp

lemma tm3 [transforms_intros]:
  assumes "ttt = 40 + (3 * nlength idx + 21 * (nllength ns)\<^sup>2) + (125 * nllength ns ^ 3 + 8)"
  shows "transforms tm3 tps0 ttt (tpsC idx)"
  unfolding tm3_def by (tform tps: assms jk)

lemma tpsC_idx:
  "tpsC idx = tps0
    [j2 + 1 := (\<lfloor>ns ! idx\<rfloor>\<^sub>N, 1),
     j2 + 2 := (\<lfloor>idx\<rfloor>\<^sub>N, 1),
     j2 + 4 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>if \<exists>i<idx. ns ! i = ns ! idx then GREATEST i. i < idx \<and> ns ! i = ns ! idx else idx\<rfloor>\<^sub>N, 1)]"
  using tpsC_def rv_def by simp

definition tps4 :: "tape list" where
  "tps4 \<equiv> tps0
    [j2 + 1 := (\<lfloor>[]\<rfloor>, 1),
     j2 + 2 := (\<lfloor>idx\<rfloor>\<^sub>N, 1),
     j2 + 4 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>if \<exists>i<idx. ns ! i = ns ! idx then GREATEST i. i < idx \<and> ns ! i = ns ! idx else idx\<rfloor>\<^sub>N, 1)]"

lemma tm4 [transforms_intros]:
  assumes "ttt = 55 + 3 * nlength idx + 21 * (nllength ns)\<^sup>2 + 125 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: assms tpsC_def tps4_def jk)
  show "proper_symbols (canrepr (ns ! idx))"
    using proper_symbols_canrepr by simp
  show "tps4 = (tpsC idx)[j2 + 1 := (\<lfloor>[]\<rfloor>, 1)]"
    using tpsC_idx tps4_def by (simp add: list_update_swap[of "Suc j2"])
qed

definition tps5 :: "tape list" where
  "tps5 \<equiv> tps0
    [j2 + 1 := (\<lfloor>[]\<rfloor>, 1),
     j2 + 2 := (\<lfloor>[]\<rfloor>, 1),
     j2 + 4 := (\<lfloor>1\<rfloor>\<^sub>N, 1),
     j2 + 5 := (\<lfloor>if \<exists>i<idx. ns ! i = ns ! idx then GREATEST i. i < idx \<and> ns ! i = ns ! idx else idx\<rfloor>\<^sub>N, 1)]"

lemma tm5 [transforms_intros]:
  assumes "ttt = 62 + 5 * nlength idx + 21 * (nllength ns)\<^sup>2 + 125 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: tps4_def tps5_def jk time: assms tps4_def jk)
  show "proper_symbols (canrepr idx)"
    using proper_symbols_canrepr by simp
qed

definition tps6 :: "tape list" where
  "tps6 \<equiv> tps0
    [j2 + 1 := (\<lfloor>[]\<rfloor>, 1),
     j2 + 2 := (\<lfloor>[]\<rfloor>, 1),
     j2 + 4 := (\<lfloor>[]\<rfloor>, 1),
     j2 + 5 := (\<lfloor>if \<exists>i<idx. ns ! i = ns ! idx then GREATEST i. i < idx \<and> ns ! i = ns ! idx else idx\<rfloor>\<^sub>N, 1)]"

lemma tm6:
  assumes "ttt = 71 + 5 * nlength idx + 21 * (nllength ns)\<^sup>2 + 125 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
  shows "transforms tm6 tps0 ttt tps6"
  unfolding tm6_def
proof (tform tps: tps5_def tps6_def jk time: assms tps5_def jk nlength_1_simp)
  show "proper_symbols (canrepr (Suc 0))"
    using proper_symbols_canrepr by simp
qed

definition tps6' :: "tape list" where
  "tps6' \<equiv> tps0
    [j2 + 5 := (\<lfloor>if \<exists>i<idx. ns ! i = ns ! idx then GREATEST i. i < idx \<and> ns ! i = ns ! idx else idx\<rfloor>\<^sub>N, 1)]"

lemma tps6'_eq_tps6: "tps6' = tps6"
  using tps6'_def tps6_def tps0 jk canrepr_0 by (metis (no_types, lifting) list_update_id)

lemma tm6':
  assumes "ttt = 71 + 153 * nllength ns ^ 3"
  shows "transforms tm6 tps0 ttt tps6'"
proof -
  let ?ttt = "71 + 5 * nlength idx + 21 * (nllength ns)\<^sup>2 + 125 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
  have "?ttt \<le> 71 + 5 * nlength idx + 21 * (nllength ns)^3 + 125 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
    using pow_mono[of 2 3 "nllength ns"] by fastforce
  also have "... = 71 + 5 * nlength idx + 146 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
    by simp
  also have "... \<le> 71 + 5 * nllength ns + 146 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
  proof -
    have "nlength idx \<le> nllength ns"
      using idx by (meson le_trans length_le_nllength nlength_le_n order.strict_implies_order)
    then show ?thesis
      by simp
  qed
  also have "... \<le> 71 + 5 * nllength ns ^ 3 + 146 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
    using linear_le_pow by simp
  also have "... = 71 + 151 * nllength ns ^ 3 + 2 * nlength (ns ! idx)"
    by simp
  also have "... \<le> 71 + 151 * nllength ns ^ 3 + 2 * nllength ns"
    using idx member_le_nllength by simp
  also have "... \<le> 71 + 151 * nllength ns ^ 3 + 2 * nllength ns^3"
    using linear_le_pow by simp
  also have "... = 71 + 153 * nllength ns ^ 3"
    by simp
  finally have "?ttt \<le> ttt"
    using assms by simp
  then have "transforms tm6 tps0 ttt tps6"
    using tm6 transforms_monotone by simp
  then show ?thesis
    using tps6'_eq_tps6 by simp
qed

end  (* context tps0 idx ns *)

end  (* locale turing_machine_prev *)

lemma transforms_tm_prevI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k idx :: nat and ns :: "nat list"
  assumes "0 < j1" "j1 < j2" "j2 + 6 \<le> k" "length tps = k"
    and "idx < length ns"
  assumes
    "tps ! j1 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! j2 = (\<lfloor>idx\<rfloor>\<^sub>N, 1)"
    "tps ! (j2 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j2 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j2 + 3) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j2 + 4) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j2 + 5) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 71 + 153 * nllength ns ^ 3"
  assumes "tps' = tps
    [j2 + 5 := (\<lfloor>previous ns idx\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_prev j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_prev j1 j2 .
  show ?thesis
    using assms loc.tm6_eq_tm_prev loc.tm6' loc.tps6'_def previous_def by simp
qed


subsection \<open>Checking containment in a list\<close>

text \<open>
A Turing machine that checks whether a number given on tape $j_2$ is contained
in the list of numbers on tape $j_1$. If so, it writes a~1 to tape $j_3$, and
otherwise leaves tape $j_3$ unchanged. So tape $j_3$ should be initialized
with~0.
\<close>

definition tm_contains :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_contains j1 j2 j3 \<equiv>
    WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO
      tm_nextract \<bar> j1 (j3 + 1) ;;
      tm_equalsn j2 (j3 + 1) (j3 + 2) ;;
      IF \<lambda>rs. rs ! (j3 + 2) \<noteq> \<box> THEN
        tm_setn j3 1
      ELSE
        []
      ENDIF ;;
      tm_setn (j3 + 1) 0 ;;
      tm_setn (j3 + 2) 0
    DONE ;;
    tm_cr j1"

lemma tm_contains_tm:
  assumes "0 < j1" "j1 \<noteq> j2" "j3 + 2 < k" "j1 < j3" "j2 < j3" and "k \<ge> 2" and "G \<ge> 5"
  shows "turing_machine k G (tm_contains j1 j2 j3)"
  unfolding tm_contains_def
  using tm_nextract_tm tm_equalsn_tm Nil_tm tm_setn_tm tm_cr_tm assms
    turing_machine_branch_turing_machine turing_machine_loop_turing_machine
  by simp

locale turing_machine_contains =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tmL1 \<equiv> tm_nextract \<bar> j1 (j3 + 1)"
definition "tmL2 \<equiv> tmL1 ;; tm_equalsn j2 (j3 + 1) (j3 + 2)"
definition "tmI \<equiv> IF \<lambda>rs. rs ! (j3 + 2) \<noteq> \<box> THEN tm_setn j3 1 ELSE [] ENDIF"
definition "tmL3 \<equiv> tmL2 ;; tmI"
definition "tmL4 \<equiv> tmL3 ;; tm_setn (j3 + 1) 0"
definition "tmL5 \<equiv> tmL4 ;; tm_setn (j3 + 2) 0"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! j1 \<noteq> \<box> DO tmL5 DONE"
definition "tm2 \<equiv> tmL ;; tm_cr j1"

lemma tm2_eq_tm_contains: "tm2 = tm_contains j1 j2 j3"
  unfolding tm2_def tmL_def tmL5_def tmL4_def tmL3_def tmI_def tmL2_def tmL1_def tm_contains_def
  by simp

context
  fixes tps0 :: "tape list" and k :: nat and ns :: "nat list" and needle :: nat
  assumes jk: "0 < j1" "j1 \<noteq> j2" "j3 + 2 < k" "j1 < j3" "j2 < j3" "length tps0 = k"
    and tps0:
      "tps0 ! j1 = nltape' ns 0"
      "tps0 ! j2 = (\<lfloor>needle\<rfloor>\<^sub>N, 1)"
      "tps0 ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j3 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition tpsL :: "nat \<Rightarrow> tape list" where
  "tpsL t \<equiv> tps0
    [j1 := nltape' ns t,
     j3 := (\<lfloor>\<exists>i<t. ns ! i = needle\<rfloor>\<^sub>B, 1)]"

lemma tpsL0: "tpsL 0 = tps0"
  unfolding tpsL_def using tps0 by (smt (verit) list_update_id not_less_zero)

definition tpsL1 :: "nat \<Rightarrow> tape list" where
  "tpsL1 t \<equiv> tps0
    [j1 := nltape' ns (Suc t),
     j3 := (\<lfloor>\<exists>i<t. ns ! i = needle\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1)]"

lemma tmL1 [transforms_intros]:
  assumes "ttt = 12 + 2 * nlength (ns ! t)" and "t < length ns"
  shows "transforms tmL1 (tpsL t) ttt (tpsL1 t)"
  unfolding tmL1_def
proof (tform tps: assms(2) tpsL_def tpsL1_def jk tps0)
  show "ttt = 12 + 2 * nlength 0 + 2 * nlength (ns ! t)"
    using assms(1) by simp
  show "tpsL1 t = (tpsL t)
    [j1 := nltape' ns (Suc t),
     j3 + 1 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL1_def tpsL_def using jk by (simp add: list_update_swap)
qed

definition tpsL2 :: "nat \<Rightarrow> tape list" where
  "tpsL2 t \<equiv> tps0
    [j1 := nltape' ns (Suc t),
     j3 := (\<lfloor>\<exists>i<t. ns ! i = needle\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>needle = ns ! t\<rfloor>\<^sub>B, 1)]"

lemma tmL2 [transforms_intros]:
  assumes "ttt = 12 + 2 * nlength (ns ! t) + (3 * nlength (min needle (ns ! t)) + 7)"
    and "t < length ns"
  shows "transforms tmL2 (tpsL t) ttt (tpsL2 t)"
  unfolding tmL2_def by (tform tps: assms tps0 tpsL1_def tpsL2_def jk)

definition tpsI :: "nat \<Rightarrow> tape list" where
  "tpsI t \<equiv> tps0
    [j1 := nltape' ns (Suc t),
     j3 := (\<lfloor>\<exists>i<Suc t. ns ! i = needle\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>ns ! t\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>needle = ns ! t\<rfloor>\<^sub>B, 1)]"

lemma tmI [transforms_intros]:
  assumes "ttt = 16" and "t < length ns"
  shows "transforms tmI (tpsL2 t) ttt (tpsI t)"
  unfolding tmI_def
proof (tform tps: tpsL2_def jk)
  show "10 + 2 * nlength (if \<exists>i<t. ns ! i = needle then 1 else 0) + 2 * nlength 1 + 2 \<le> ttt"
    using assms(1) nlength_1_simp nlength_0 by simp
  show "0 + 1 \<le> ttt"
    using assms(1) by simp

  have "tpsL2 t ! (j3 + 2) = (\<lfloor>needle = ns ! t\<rfloor>\<^sub>B, 1)"
    using tpsL2_def jk by simp
  then have *: "(read (tpsL2 t) ! (j3 + 2) = \<box>) = (needle \<noteq> ns ! t)"
    using jk read_ncontents_eq_0[of "tpsL2 t" "j3 + 2"] tpsL2_def by simp

  show "tpsI t = (tpsL2 t)[j3 := (\<lfloor>1\<rfloor>\<^sub>N, 1)]" if "read (tpsL2 t) ! (j3 + 2) \<noteq> \<box>"
  proof -
    have "needle = ns ! t"
      using * that by simp
    then have "\<exists>i<Suc t. ns ! i = needle"
      using assms(2) by auto
    then show ?thesis
      unfolding tpsI_def tpsL2_def using jk by (simp add: list_update_swap)
  qed
  show "tpsI t = tpsL2 t" if "\<not> read (tpsL2 t) ! (j3 + 2) \<noteq> \<box>"
  proof -
    have "needle \<noteq> ns ! t"
      using * that by simp
    then have "(\<exists>i<Suc t. ns ! i = needle) = (\<exists>i< t. ns ! i = needle)"
      using assms(2) less_Suc_eq by auto
    then show ?thesis
      unfolding tpsI_def tpsL2_def by simp
  qed
qed

lemma tmL3 [transforms_intros]:
  assumes "ttt = 28 + 2 * nlength (ns ! t) + (3 * nlength (min needle (ns ! t)) + 7)"
    and "t < length ns"
  shows "transforms tmL3 (tpsL t) ttt (tpsI t)"
  unfolding tmL3_def by (tform tps: assms)
definition tpsL4 :: "nat \<Rightarrow> tape list" where
  "tpsL4 t \<equiv> tps0
    [j1 := nltape' ns (Suc t),
     j3 := (\<lfloor>\<exists>i<Suc t. ns ! i = needle\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>needle = ns ! t\<rfloor>\<^sub>B, 1)]"

lemma tmL4 [transforms_intros]:
  assumes "ttt = 38 + 4 * nlength (ns ! t) + (3 * nlength (min needle (ns ! t)) + 7)"
    and "t < length ns"
  shows "transforms tmL4 (tpsL t) ttt (tpsL4 t)"
  unfolding tmL4_def
proof (tform tps: assms tpsI_def jk)
  show "tpsL4 t = (tpsI t)[j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL4_def tpsI_def by (simp add: list_update_swap)
qed

definition tpsL5 :: "nat \<Rightarrow> tape list" where
  "tpsL5 t \<equiv> tps0
    [j1 := nltape' ns (Suc t),
     j3 := (\<lfloor>\<exists>i<Suc t. ns ! i = needle\<rfloor>\<^sub>B, 1),
     j3 + 1 := (\<lfloor>0\<rfloor>\<^sub>N, 1),
     j3 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"

lemma tmL5:
  assumes "ttt = 48 + 4 * nlength (ns ! t) + (3 * nlength (min needle (ns ! t)) + 7) +
      2 * nlength (if needle = ns ! t then 1 else 0)"
    and "t < length ns"
  shows "transforms tmL5 (tpsL t) ttt (tpsL5 t)"
  unfolding tmL5_def
proof (tform tps: assms tpsL4_def jk)
  show "tpsL5 t = (tpsL4 t)[j3 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    unfolding tpsL5_def tpsL4_def by (simp add: list_update_swap)
qed

definition tpsL5' :: "nat \<Rightarrow> tape list" where
  "tpsL5' t \<equiv> tps0
    [j1 := nltape' ns (Suc t),
     j3 := (\<lfloor>\<exists>i<Suc t. ns ! i = needle\<rfloor>\<^sub>B, 1)]"

lemma tpsL5': "tpsL5' t = tpsL5 t"
  using tpsL5'_def tpsL5_def tps0 jk
  by (smt (verit, del_insts) One_nat_def less_Suc_eq less_add_same_cancel1 list_update_swap not_less_eq tape_list_eq zero_less_numeral)

lemma tmL5':
  assumes "ttt = 57 + 4 * nlength (ns ! t) + 3 * nlength (min needle (ns ! t))"
    and "t < length ns"
  shows "transforms tmL5 (tpsL t) ttt (tpsL5' t)"
proof -
  have "nlength (if needle = ns ! t then 1 else 0) \<le> 1"
    using nlength_1_simp by simp
  then have "48 + 4 * nlength (ns ! t) + (3 * nlength (min needle (ns ! t)) + 7) +
      2 * nlength (if needle = ns ! t then 1 else 0) \<le> ttt"
    using assms(1) by simp
  then show ?thesis
    using tpsL5' tmL5 transforms_monotone assms(2) by fastforce
qed

lemma tmL5'' [transforms_intros]:
  assumes "ttt = 57 + 7 * nllength ns" and "t < length ns"
  shows "transforms tmL5 (tpsL t) ttt (tpsL (Suc t))"
proof -
  have "nlength (ns ! t) \<le> nllength ns"
    using assms(2) by (simp add: member_le_nllength)
  moreover from this have "nlength (min needle (ns ! t)) \<le> nllength ns"
    using nlength_mono by (metis dual_order.trans min_def)
  ultimately have "ttt \<ge> 57 + 4 * nlength (ns ! t) + 3 * nlength (min needle (ns ! t))"
    using assms(1) by simp
  moreover have "tpsL5' t = tpsL (Suc t)"
    using tpsL5'_def tpsL_def by simp
  ultimately show ?thesis
    using tmL5' assms(2) transforms_monotone by fastforce
qed

lemma tmL [transforms_intros]:
  assumes "ttt = length ns * (59 + 7 * nllength ns) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL (length ns))"
  unfolding tmL_def
proof (tform)
  let ?t = "57 + 7 * nllength ns"
  show "length ns * (57 + 7 * nllength ns + 2) + 1 \<le> ttt"
    using assms by simp
  have *: "tpsL t ! j1 = nltape' ns t" for t
    using tpsL_def jk by simp
  moreover have "read (tpsL t) ! j1 = tpsL t :.: j1" for t
    using tapes_at_read'[of j1 "tpsL t"] tpsL_def jk by simp
  ultimately have "read (tpsL t) ! j1 = |.| (nltape' ns t)" for t
    by simp
  then have "read (tpsL t) ! j1 = \<box> \<longleftrightarrow> (t \<ge> length ns)" for t
    using nltape'_tape_read by simp
  then show
      "\<And>i. i < length ns \<Longrightarrow> read (tpsL i) ! j1 \<noteq> \<box>"
      "\<not> read (tpsL (length ns)) ! j1 \<noteq> \<box>"
    using * by simp_all
qed

definition tps2 :: "tape list" where
  "tps2 \<equiv> tps0
    [j1 := nltape' ns 0,
     j3 := (\<lfloor>\<exists>i<length ns. ns ! i = needle\<rfloor>\<^sub>B, 1)]"

lemma tm2:
  assumes "ttt = length ns * (59 + 7 * nllength ns) + nllength ns + 4"
  shows "transforms tm2 (tpsL 0) ttt tps2"
  unfolding tm2_def
proof (tform tps: tpsL_def jk)
  show "clean_tape (tpsL (length ns) ! j1)"
    using tpsL_def jk clean_tape_nlcontents by simp
  have "tpsL (length ns) ! j1 |#=| 1 = nltape' ns 0"
    using tpsL_def jk by simp
  then have "(tpsL (length ns))[j1 := tpsL (length ns) ! j1 |#=| 1] = (tpsL (length ns))[j1 := nltape' ns 0]"
    by simp
  then show "tps2 = (tpsL (length ns))[j1 := tpsL (length ns) ! j1 |#=| 1]"
    unfolding tps2_def tpsL_def using jk by (simp add: list_update_swap)
  have "tpsL (length ns) :#: j1 = Suc (nllength ns)"
    using tpsL_def jk by simp
  then show "ttt = length ns * (59 + 7 * nllength ns) + 1 +
      (tpsL (length ns) :#: j1 + 2)"
    using assms by simp
qed

definition tps2' :: "tape list" where
  "tps2' \<equiv> tps0
    [j3 := (\<lfloor>needle \<in> set ns\<rfloor>\<^sub>B, 1)]"

lemma tm2':
  assumes "ttt = 67 * nllength ns ^ 2 + 4"
  shows "transforms tm2 tps0 ttt tps2'"
proof -
  let ?t = "length ns * (59 + 7 * nllength ns) + nllength ns + 4"
  have "?t \<le> nllength ns * (59 + 7 * nllength ns) + nllength ns + 4"
    by (simp add: length_le_nllength)
  also have "... = 60 * nllength ns + 7 * nllength ns ^ 2 + 4"
    by algebra
  also have "... \<le> 60 * nllength ns ^ 2 + 7 * nllength ns ^ 2 + 4"
    using linear_le_pow by simp
  also have "... = 67 * nllength ns ^ 2 + 4"
    by simp
  finally have "?t \<le> 67 * nllength ns ^ 2 + 4" .
  moreover have "tps2' = tps2"
    unfolding tps2_def tps2'_def using tps0(1) by (smt (verit) in_set_conv_nth list_update_id)
  ultimately show ?thesis
    using tm2 assms transforms_monotone tpsL0 by simp
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_containsI [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k needle :: nat and ns :: "nat list"
  assumes "0 < j1" "j1 \<noteq> j2" "j3 + 2 < k" "j1 < j3" "j2 < j3" "length tps = k"
  assumes
    "tps ! j1 = nltape' ns 0"
    "tps ! j2 = (\<lfloor>needle\<rfloor>\<^sub>N, 1)"
    "tps ! j3 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 67 * nllength ns ^ 2 + 4"
  assumes "tps' = tps
    [j3 := (\<lfloor>needle \<in> set ns\<rfloor>\<^sub>B, 1)]"
  shows "transforms (tm_contains j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_contains j1 j2 j3 .
  show ?thesis
    using assms loc.tm2_eq_tm_contains loc.tps2'_def loc.tm2' by simp
qed


subsection \<open>Creating lists of consecutive numbers\<close>

text \<open>
The next TM accepts a number $start$ on tape $j_1$ and a number $delta$ on tape
$j_2$. It outputs the list $[start, \dots, start + delta - 1]$ on tape $j_3$.
\<close>

definition tm_range :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_range j1 j2 j3 \<equiv>
    tm_copyn j1 (j3 + 2) ;;
    tm_copyn j2 (j3 + 1) ;;
    WHILE [] ; \<lambda>rs. rs ! (j3 + 1) \<noteq> \<box> DO
      tm_append j3 (j3 + 2) ;;
      tm_incr (j3 + 2) ;;
      tm_decr (j3 + 1)
    DONE ;;
    tm_setn (j3 + 2) 0 ;;
    tm_cr j3"

lemma tm_range_tm:
  assumes "k \<ge> j3 + 3" and "G \<ge> 5" and "j1 \<noteq> j2" and "0 < j1" and "0 < j2" and "j1 < j3" and "j2 < j3"
  shows "turing_machine k G (tm_range j1 j2 j3)"
  unfolding tm_range_def
  using assms tm_copyn_tm tm_decr_tm tm_append_tm tm_setn_tm tm_incr_tm Nil_tm tm_cr_tm
    turing_machine_loop_turing_machine
  by simp

locale turing_machine_range =
  fixes j1 j2 j3 :: tapeidx
begin

definition "tm1 \<equiv> tm_copyn j1 (j3 + 2)"
definition "tm2 \<equiv> tm1 ;; tm_copyn j2 (j3 + 1)"
definition "tmB1 \<equiv> tm_append j3 (j3 + 2)"
definition "tmB2 \<equiv> tmB1 ;; tm_incr (j3 + 2)"
definition "tmB3 \<equiv> tmB2 ;; tm_decr (j3 + 1)"
definition "tmL \<equiv> WHILE [] ; \<lambda>rs. rs ! (j3 + 1) \<noteq> \<box> DO tmB3 DONE"
definition "tm3 \<equiv> tm2 ;; tmL"
definition "tm4 \<equiv> tm3 ;; tm_setn (j3 + 2) 0"
definition "tm5 \<equiv> tm4 ;; tm_cr j3"

lemma tm5_eq_tm_range: "tm5 = tm_range j1 j2 j3"
  unfolding tm_range_def tm5_def tm4_def tm3_def tmL_def tmB3_def tmB2_def tmB1_def tm2_def tm1_def
  by simp

context
  fixes tps0 :: "tape list" and k start delta :: nat
  assumes jk: "k \<ge> j3 + 3" "j1 \<noteq> j2" "0 < j1" "0 < j2" "0 < j3" "j1 < j3" "j2 < j3" "length tps0 = k"
    and tps0:
      "tps0 ! j1 = (\<lfloor>start\<rfloor>\<^sub>N, 1)"
      "tps0 ! j2 = (\<lfloor>delta\<rfloor>\<^sub>N, 1)"
      "tps0 ! j3 = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
      "tps0 ! (j3 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
      "tps0 ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0
  [j3 + 2 := (\<lfloor>start\<rfloor>\<^sub>N, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 14 + 3 * nlength start"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
  by (tform tps: nlength_0 assms tps0 tps1_def jk)

definition "tps2 \<equiv> tps0
  [j3 + 2 := (\<lfloor>start\<rfloor>\<^sub>N, 1),
   j3 + 1 := (\<lfloor>delta\<rfloor>\<^sub>N, 1)]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 28 + 3 * nlength start + 3 * nlength delta"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk tps0 tps1_def tps2_def)
  show "ttt = 14 + 3 * nlength start + (14 + 3 * (nlength delta + nlength 0))"
    using assms by simp
qed

definition "tpsL t \<equiv> tps0
  [j3 + 2 := (\<lfloor>start + t\<rfloor>\<^sub>N, 1),
   j3 + 1 := (\<lfloor>delta - t\<rfloor>\<^sub>N, 1),
   j3 := nltape [start..<start + t]]"

lemma tpsL_eq_tps2: "tpsL 0 = tps2"
  using tpsL_def tps2_def tps0 jk
  by (metis (mono_tags, lifting) One_nat_def Suc_n_not_le_n add_cancel_left_right eq_imp_le list_update_id
    list_update_swap minus_nat.diff_0 nllength_Nil not_numeral_le_zero upt_conv_Nil)

definition "tpsB1 t \<equiv> tps0
  [j3 + 2 := (\<lfloor>start + t\<rfloor>\<^sub>N, 1),
   j3 + 1 := (\<lfloor>delta - t\<rfloor>\<^sub>N, 1),
   j3 := nltape ([start..<start + t] @ [start + t])]"

lemma tmB1 [transforms_intros]:
  assumes "ttt = 6 + 2 * nlength (start + t)"
  shows "transforms tmB1 (tpsL t) ttt (tpsB1 t)"
  unfolding tmB1_def
proof (tform tps: tpsL_def tpsB1_def jk)
  show "ttt = 7 + nllength [start..<start + t] - Suc (nllength [start..<start + t]) + 2 * nlength (start + t)"
    using assms by simp
qed

definition "tpsB2 t \<equiv> tps0
  [j3 + 2 := (\<lfloor>Suc (start + t)\<rfloor>\<^sub>N, 1),
   j3 + 1 := (\<lfloor>delta - t\<rfloor>\<^sub>N, 1),
   j3 := nltape ([start..<start + t] @ [start + t])]"

lemma tmB2 [transforms_intros]:
  assumes "ttt = 11 + 4 * nlength (start + t)"
  shows "transforms tmB2 (tpsL t) ttt (tpsB2 t)"
  unfolding tmB2_def by (tform tps: tpsL_def tpsB1_def tpsB2_def jk time: assms)

definition "tpsB3 t \<equiv> tps0
  [j3 + 2 := (\<lfloor>Suc (start + t)\<rfloor>\<^sub>N, 1),
   j3 + 1 := (\<lfloor>delta - t - 1\<rfloor>\<^sub>N, 1),
   j3 := nltape ([start..<start + t] @ [start + t])]"

lemma tmB3:
  assumes "ttt = 19 + 4 * nlength (start + t) + 2 * nlength (delta - t)"
  shows "transforms tmB3 (tpsL t) ttt (tpsB3 t)"
  unfolding tmB3_def by (tform tps: tpsL_def tpsB2_def tpsB3_def jk time: assms)

lemma tpsB3: "tpsB3 t \<equiv> tpsL (Suc t)"
  using tpsB3_def tpsL_def by simp

lemma tmB3' [transforms_intros]:
  assumes "ttt = 19 + 6 * nlength (start + delta)" and "t < delta"
  shows "transforms tmB3 (tpsL t) ttt (tpsL (Suc t))"
proof -
  have "19 + 4 * nlength (start + t) + 2 * nlength (delta - t) \<le> 19 + 4 * nlength (start + t) + 2 * nlength delta"
    using nlength_mono by simp
  also have "... \<le> 19 + 4 * nlength (start + delta) + 2 * nlength delta"
    using assms(2) nlength_mono by simp
  also have "... \<le> 19 + 4 * nlength (start + delta) + 2 * nlength (start + delta)"
    using nlength_mono by simp
  also have "... = 19 + 6 * nlength (start + delta)"
    by simp
  finally have "19 + 4 * nlength (start + t) + 2 * nlength (delta - t) \<le> 19 + 6 * nlength (start + delta)" .
  then show ?thesis
    using tpsB3 tmB3 transforms_monotone assms(1) by metis
qed

lemma tmL:
  assumes "ttt = delta * (21 + 6 * nlength (start + delta)) + 1"
  shows "transforms tmL (tpsL 0) ttt (tpsL delta)"
  unfolding tmL_def
proof (tform)
  have "read (tpsL t) ! (j3 + 1) \<noteq> \<box> \<longleftrightarrow> t < delta" for t
    using tpsL_def read_ncontents_eq_0 jk by auto
  then show "\<And>t. t < delta \<Longrightarrow> read (tpsL t) ! (j3 + 1) \<noteq> \<box>" and "\<not> read (tpsL delta) ! (j3 + 1) \<noteq> \<box>"
    by simp_all
  show "delta * (19 + 6 * nlength (start + delta) + 2) + 1 \<le> ttt"
    using assms(1) by simp
qed

lemma tmL' [transforms_intros]:
  assumes "ttt = delta * (21 + 6 * nlength (start + delta)) + 1"
  shows "transforms tmL tps2 ttt (tpsL delta)"
  using tmL assms tpsL_eq_tps2 by simp

definition "tps3 \<equiv> tps0
  [j3 + 2 := (\<lfloor>start + delta\<rfloor>\<^sub>N, 1),
   j3 := nltape [start..<start + delta]]"

lemma tpsL_eq_tps3: "tpsL delta = tps3"
  using tps3_def tps0 jk tpsL_def
  by (smt (z3) One_nat_def add_left_imp_eq cancel_comm_monoid_add_class.diff_cancel list_update_id
    list_update_swap n_not_Suc_n numeral_2_eq_2)

lemma tm3:
  assumes "ttt = 29 + 3 * nlength start + 3 * nlength delta + delta * (21 + 6 * nlength (start + delta))"
  shows "transforms tm3 tps0 ttt (tpsL delta)"
  unfolding tm3_def by (tform time: assms)

lemma tm3' [transforms_intros]:
  assumes "ttt = 29 + 3 * nlength start + 3 * nlength delta + delta * (21 + 6 * nlength (start + delta))"
  shows "transforms tm3 tps0 ttt tps3"
  using assms tm3 tpsL_eq_tps3 by simp

definition "tps4 \<equiv> tps0
  [j3 := nltape [start..<start + delta]]"

lemma tm4:
  assumes "ttt = 39 + 3 * nlength start + 3 * nlength delta + delta * (21 + 6 * nlength (start + delta)) +
    2 * nlength (start + delta)"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps3_def tps4_def jk time: assms)
  show "tps4 = tps3[j3 + 2 := (\<lfloor>0\<rfloor>\<^sub>N, 1)]"
    using tps4_def tps3_def tps0 jk
    by (metis (mono_tags, lifting) Suc_neq_Zero add_cancel_right_right list_update_id list_update_overwrite
      list_update_swap numeral_2_eq_2)
qed

lemma tm4' [transforms_intros]:
  assumes "ttt = Suc delta * (39 + 8 * nlength (start + delta))"
  shows "transforms tm4 tps0 ttt tps4"
proof -
  let ?ttt = "39 + 3 * nlength start + 3 * nlength delta + delta * (21 + 6 * nlength (start + delta)) + 2 * nlength (start + delta)"
  have "?ttt \<le> 39 + 3 * nlength (start + delta) + 3 * nlength (start + delta) +
      delta * (21 + 6 * nlength (start + delta)) + 2 * nlength (start + delta)"
    using nlength_mono by (meson add_le_mono add_le_mono1 le_add2 nat_add_left_cancel_le nat_le_iff_add nat_mult_le_cancel_disj)
  also have "... = 39 + 8 * nlength (start + delta) + delta * (21 + 6 * nlength (start + delta))"
    by simp
  also have "... \<le> 39 + 8 * nlength (start + delta) + delta * (39 + 8 * nlength (start + delta))"
    by simp
  also have "... = Suc delta * (39 + 8 * nlength (start + delta))"
    by simp
  finally have "?ttt \<le> Suc delta * (39 + 8 * nlength (start + delta))" .
  then show ?thesis
    using assms tm4 transforms_monotone tps4_def by simp
qed

definition "tps5 \<equiv> tps0
  [j3 := (\<lfloor>[start..<start + delta]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm5:
  assumes "ttt = Suc delta * (39 + 8 * nlength (start + delta)) + Suc (Suc (Suc (nllength [start..<start + delta])))"
  shows "transforms tm5 tps0 ttt tps5"
  unfolding tm5_def
proof (tform tps: tps4_def tps5_def jk time: assms tps4_def jk)
  show "clean_tape (tps4 ! j3)"
    using tps4_def jk clean_tape_nlcontents by simp
qed

lemma tm5':
  assumes "ttt = Suc delta * (43 + 9 * nlength (start + delta))"
  shows "transforms tm5 tps0 ttt tps5"
proof -
  let ?ttt = "Suc delta * (39 + 8 * nlength (start + delta)) + Suc (Suc (Suc (nllength [start..<start + delta])))"
  have "nllength [start..<start + delta] \<le> Suc (nlength (start + delta)) * delta"
    using nllength_le_len_mult_max[of "[start..<start + delta]" "start + delta"] by simp
  then have "?ttt \<le> Suc delta * (39 + 8 * nlength (start + delta)) + 3 + Suc (nlength (start + delta)) * delta"
    by simp
  also have "... \<le> 3 + Suc delta * (39 + 8 * nlength (start + delta)) + Suc delta * Suc (nlength (start + delta))"
    by simp
  also have "... = 3 + Suc delta * (39 + 8 * nlength (start + delta) + Suc (nlength (start + delta)))"
    by algebra
  also have "... = 3 + Suc delta * (40 + 9 * nlength (start + delta))"
    by simp
  also have "... \<le> Suc delta * (43 + 9 * nlength (start + delta))"
    by simp
  finally have "?ttt \<le> Suc delta * (43 + 9 * nlength (start + delta))" .
  then show ?thesis
    using tm5 assms transforms_monotone by simp
qed

end  (* context tps0 *)

end  (* locale turing_machine_range *)

lemma transforms_tm_rangeI [transforms_intros]:
  fixes j1 j2 j3 :: tapeidx
  fixes tps tps' :: "tape list" and k start delta :: nat
  assumes "k \<ge> j3 + 3" "j1 \<noteq> j2" "0 < j1" "0 < j2" "j1 < j3" "j2 < j3" "length tps = k"
  assumes
    "tps ! j1 = (\<lfloor>start\<rfloor>\<^sub>N, 1)"
    "tps ! j2 = (\<lfloor>delta\<rfloor>\<^sub>N, 1)"
    "tps ! j3 = (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)"
    "tps ! (j3 + 1) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
    "tps ! (j3 + 2) = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  assumes "ttt = Suc delta * (43 + 9 * nlength (start + delta))"
  assumes "tps' = tps
    [j3 := (\<lfloor>[start..<start + delta]\<rfloor>\<^sub>N\<^sub>L, 1)]"
  shows "transforms (tm_range j1 j2 j3) tps ttt tps'"
proof -
  interpret loc: turing_machine_range j1 j2 j3 .
  show ?thesis
    using assms loc.tm5_eq_tm_range loc.tm5' loc.tps5_def by simp
qed


subsection \<open>Creating singleton lists\<close>

text \<open>
The next Turing machine appends the symbol \textbf{|} to the symbols on
tape~$j$. Thus it turns a number into a singleton list containing this number.
\<close>

definition tm_to_list :: "tapeidx \<Rightarrow> machine" where
  "tm_to_list j \<equiv>
    tm_right_until j {\<box>} ;;
    tm_write j \<bar> ;;
    tm_cr j"

lemma tm_to_list_tm:
  assumes "0 < j" and "j < k" and "G \<ge> 5"
  shows "turing_machine k G (tm_to_list j)"
  unfolding tm_to_list_def using tm_right_until_tm tm_write_tm tm_cr_tm assms by simp

locale turing_machine_to_list =
  fixes j :: tapeidx
begin

definition "tm1 \<equiv> tm_right_until j {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_write j \<bar>"
definition "tm3 \<equiv> tm2 ;; tm_cr j"

lemma tm3_eq_tm_to_list: "tm3 = tm_to_list j"
  using tm3_def tm2_def tm1_def tm_to_list_def by simp

context
  fixes tps0 :: "tape list" and k n :: nat
  assumes jk: "0 < j" "j < k" "length tps0 = k"
    and tps0: "tps0 ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
begin

definition "tps1 \<equiv> tps0[j := (\<lfloor>n\<rfloor>\<^sub>N, Suc (nlength n))]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (nlength n)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: assms tps1_def tps0 jk)
  show "rneigh (tps0 ! j) {0} (nlength n)"
  proof (rule rneighI)
    show "(tps0 ::: j) (tps0 :#: j + nlength n) \<in> {0}"
      using tps0 jk by simp
    show "\<And>n'. n' < nlength n \<Longrightarrow> (tps0 ::: j) (tps0 :#: j + n') \<notin> {0}"
      using assms tps0 jk bit_symbols_canrepr contents_def by fastforce
  qed
qed

definition "tps2 \<equiv> tps0[j := (\<lfloor>[n]\<rfloor>\<^sub>N\<^sub>L, Suc (nlength n))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = Suc (Suc (nlength n))"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: assms tps1_def tps0 jk)
  have "numlist [n] = canrepr n @ [\<bar>]"
    using numlist_def by simp
  then show "tps2 = tps1[j := tps1 ! j |:=| \<bar>]"
    using assms tps1_def tps2_def tps0 jk numlist_def nlcontents_def contents_snoc
    by simp
qed

definition "tps3 \<equiv> tps0[j := (\<lfloor>[n]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm3:
  assumes "ttt = 5 + 2 * nlength n"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def tps0 jk time: assms tps2_def jk)
  show "clean_tape (tps2 ! j)"
    using tps2_def jk clean_tape_nlcontents by simp
  show "tps3 = tps2[j := tps2 ! j |#=| 1]"
    using tps3_def tps2_def jk by simp
qed

end  (* context tps0 *)

end  (* locale turing_machine_tm_to_list *)

lemma transforms_tm_to_listI [transforms_intros]:
  fixes j :: tapeidx
  fixes tps tps' :: "tape list" and ttt k n :: nat
  assumes "0 < j" "j < k" "length tps = k"
  assumes "tps ! j = (\<lfloor>n\<rfloor>\<^sub>N, 1)"
  assumes "ttt = 5 + 2 * nlength n"
  assumes "tps' = tps[j := (\<lfloor>[n]\<rfloor>\<^sub>N\<^sub>L, 1)]"
  shows "transforms (tm_to_list j) tps ttt tps'"
proof -
  interpret loc: turing_machine_to_list j .
  show ?thesis
    using assms loc.tm3_eq_tm_to_list loc.tm3 loc.tps3_def by simp
qed


subsection \<open>Extending with a list\<close>

text \<open>
The next Turing machine extends the list on tape $j_1$ with the list on tape $j_2$.
We assume that the tape head on $j_1$ is already at the end of the list.
\<close>

definition tm_extend :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_extend j1 j2 \<equiv> tm_cp_until j2 j1 {\<box>} ;; tm_cr j2"

lemma tm_extend_tm:
  assumes "0 < j1" and "G \<ge> 4" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_extend j1 j2)"
  unfolding tm_extend_def using assms tm_cp_until_tm tm_cr_tm by simp

locale turing_machine_extend =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_cp_until j2 j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_cr j2"

lemma tm2_eq_tm_extend: "tm2 = tm_extend j1 j2"
  unfolding tm2_def tm2_def tm1_def tm_extend_def by simp

context
  fixes tps0 :: "tape list" and k :: nat and ns1 ns2 :: "nat list"
  assumes jk: "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = nltape ns1"
    "tps0 ! j2 = (\<lfloor>ns2\<rfloor>\<^sub>N\<^sub>L, 1)"
begin

definition "tps1 \<equiv> tps0
  [j1 := nltape (ns1 @ ns2),
   j2 := nltape ns2]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (nllength ns2)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps1_def tps0 jk)
  let ?n = "nllength ns2"
  show "rneigh (tps0 ! j2) {0} ?n"
  proof (rule rneighI)
    show "(tps0 ::: j2) (tps0 :#: j2 + nllength ns2) \<in> {0}"
      using tps0 nlcontents_def nllength_def jk by simp
    show "\<And>i. i < nllength ns2 \<Longrightarrow> (tps0 ::: j2) (tps0 :#: j2 + i) \<notin> {0}"
      using tps0 jk contents_def nlcontents_def nllength_def proper_symbols_numlist
      by fastforce
  qed
  show "ttt = Suc (nllength ns2)"
    using assms .
  show "tps1 = tps0
    [j2 := tps0 ! j2 |+| nllength ns2,
     j1 := implant (tps0 ! j2) (tps0 ! j1) (nllength ns2)]"
  proof -
    have "implant (\<lfloor>ns2\<rfloor>\<^sub>N\<^sub>L, 1) (nltape ns1) (nllength ns2) = nltape (ns1 @ ns2)"
      using nlcontents_def nllength_def implant_contents by (simp add: numlist_append)
    moreover have "tps1 ! j2 = tps0 ! j2 |+| nllength ns2"
      using tps0 jk tps1_def by simp
    ultimately show ?thesis
      using tps0 jk tps1_def by (metis fst_conv list_update_swap plus_1_eq_Suc snd_conv)
  qed
qed

definition "tps2 \<equiv> tps0[j1 := nltape (ns1 @ ns2)]"

lemma tm2:
  assumes "ttt = 4 + 2 * nllength ns2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps0 tps2_def tps1_def jk)
  show "clean_tape (tps1 ! j2)"
    using tps1_def jk clean_tape_nlcontents by simp
  show "ttt = Suc (nllength ns2) + (tps1 :#: j2 + 2)"
    using assms tps1_def jk by simp
  show "tps2 = tps1[j2 := tps1 ! j2 |#=| 1]"
    using tps1_def jk tps2_def tps0(2)
    by (metis fst_conv length_list_update list_update_id list_update_overwrite nth_list_update)
qed

end  (* context tps0 *)

end  (* locale turing_machine_extend *)

lemma transforms_tm_extendI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and ns1 ns2 :: "nat list"
  assumes "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "length tps = k"
  assumes
    "tps ! j1 = nltape ns1"
    "tps ! j2 = (\<lfloor>ns2\<rfloor>\<^sub>N\<^sub>L, 1)"
  assumes "ttt = 4 + 2 * nllength ns2"
  assumes "tps' = tps[j1 := nltape (ns1 @ ns2)]"
  shows "transforms (tm_extend j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_extend j1 j2 .
  show ?thesis
    using loc.tm2_eq_tm_extend loc.tm2 loc.tps2_def assms by simp
qed

text \<open>
An enhanced version of the previous Turing machine, the next one erases the list
on tape $j_2$ after appending it to tape $j_1$.
\<close>

definition tm_extend_erase :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_extend_erase j1 j2 \<equiv> tm_extend j1 j2 ;; tm_erase_cr j2"

lemma tm_extend_erase_tm:
  assumes "0 < j1" and "0 < j2" and "G \<ge> 4" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_extend_erase j1 j2)"
  unfolding tm_extend_erase_def using assms tm_extend_tm tm_erase_cr_tm by simp

lemma transforms_tm_extend_eraseI [transforms_intros]:
  fixes j1 j2 :: tapeidx 
  fixes tps tps' :: "tape list" and k :: nat and ns1 ns2 :: "nat list"
  assumes "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j2" "length tps = k"
  assumes
    "tps ! j1 = nltape ns1"
    "tps ! j2 = (\<lfloor>ns2\<rfloor>\<^sub>N\<^sub>L, 1)"
  assumes "ttt = 11 + 4 * nllength ns2 "
  assumes "tps' = tps
    [j1 := nltape (ns1 @ ns2),
     j2 := (\<lfloor>[]\<rfloor>, 1)]"
  shows "transforms (tm_extend_erase j1 j2) tps ttt tps'"
  unfolding tm_extend_erase_def
proof (tform tps: assms)
  let ?zs = "numlist ns2"
  show "tps[j1 := nltape (ns1 @ ns2)] ::: j2 = \<lfloor>?zs\<rfloor>"
    using assms by (simp add: nlcontents_def)
  show "proper_symbols ?zs"
    using proper_symbols_numlist by simp
  show "ttt = 4 + 2 * nllength ns2 +
      (tps[j1 := nltape (ns1 @ ns2)] :#: j2 + 2 * length (numlist ns2) + 6)"
    using assms nllength_def by simp
qed


section \<open>Lists of lists of numbers\label{s:tm-numlistlist}\<close>

text \<open>
In this section we introduce a representation for lists of lists of numbers as
symbol sequences over the quaternary alphabet @{text "\<zero>\<one>\<bar>\<sharp>"} and devise Turing
machines for the few operations on such lists that we need.

A tape containing such representations corresponds to a variable of type @{typ
"nat list list"}. A tape in the start configuration corresponds to the empty
list of lists of numbers.

Many proofs in this section are copied from the previous section with minor
modifications, mostly replacing the symbol @{text "\<bar>"} with @{text \<sharp>}.
\<close>


subsection \<open>Representation as symbol sequence\label{s:tm-numlistlist-repr}\<close>

text \<open>
We apply the same principle as for representing lists of numbers. To represent a
list of lists of numbers, every element, which is now a list of numbers, is
terminated by the symbol @{text \<sharp>}. In this way the empty symbol sequence
represents the empty list of lists of numbers.  The list $[[]]$ containing only
an empty list is represented by @{text \<sharp>} and the list $[[0]]$ containing only a
list containing only a~0 is represented by @{text "\<bar>\<sharp>"}. As another example, the
list $[[14,0,0,7],[],[0],[25]]$ is represented by @{text
"\<zero>\<one>\<one>\<one>\<bar>\<bar>\<bar>\<one>\<one>\<one>\<bar>\<sharp>\<sharp>\<bar>\<sharp>\<one>\<zero>\<zero>\<one>\<one>\<bar>\<sharp>"}. The number of @{text \<sharp>} symbols equals
the number of elements in the list.

\null
\<close>

definition numlistlist :: "nat list list \<Rightarrow> symbol list" where
  "numlistlist nss \<equiv> concat (map (\<lambda>ns. numlist ns @ [\<sharp>]) nss)"

lemma numlistlist_Nil: "numlistlist [] = []"
  using numlistlist_def by simp

proposition "numlistlist [[]] = [\<sharp>]"
  using numlistlist_def by (simp add: numlist_Nil)

lemma proper_symbols_numlistlist: "proper_symbols (numlistlist nss)"
proof (induction nss)
  case Nil
  then show ?case
    using numlistlist_def by simp
next
  case (Cons ns nss)
  have "numlistlist (ns # nss) = numlist ns @ [\<sharp>] @ concat (map (\<lambda>ns. numlist ns @ [\<sharp>]) nss)"
    using numlistlist_def by simp
  then have "numlistlist (ns # nss) = numlist ns @ [\<sharp>] @ numlistlist nss"
    using numlistlist_def by simp
  moreover have "proper_symbols (numlist ns)"
    using proper_symbols_numlist by simp
  moreover have "proper_symbols [\<sharp>]"
    by simp
  ultimately show ?case
    using proper_symbols_append Cons by presburger
qed

lemma symbols_lt_append:
  fixes xs ys :: "symbol list" and z :: symbol
  assumes "symbols_lt z xs" and "symbols_lt z ys"
  shows "symbols_lt z (xs @ ys)"
  using assms prop_list_append by (simp add: nth_append)

lemma symbols_lt_numlistlist:
  assumes "H \<ge> 6"
  shows "symbols_lt H (numlistlist nss)"
proof (induction nss)
  case Nil
  then show ?case
    using numlistlist_def by simp
next
  case (Cons ns nss)
  have "numlistlist (ns # nss) = numlist ns @ [\<sharp>] @ concat (map (\<lambda>ns. numlist ns @ [\<sharp>]) nss)"
    using numlistlist_def by simp
  then have "numlistlist (ns # nss) = numlist ns @ [\<sharp>] @ numlistlist nss"
    using numlistlist_def by simp
  moreover have "symbols_lt H (numlist ns)"
    using assms numlist_234 nth_mem by fastforce
  moreover have "symbols_lt H [\<sharp>]"
    using assms by simp
  ultimately show ?case
    using symbols_lt_append[of _ H] Cons by presburger
qed

lemma symbols_lt_prefix_eq:
  assumes "(x @ [\<sharp>]) @ xs = (y @ [\<sharp>]) @ ys" and "symbols_lt 5 x" and "symbols_lt 5 y"
  shows "x = y"
proof -
  have *: "x @ [\<sharp>] @ xs = y @ [\<sharp>] @ ys"
      (is "?lhs = ?rhs")
    using assms(1) by simp
  show "x = y"
  proof (cases "length x \<le> length y")
    case True
    then have "?lhs ! i = ?rhs ! i" if "i < length x" for i
      using that * by simp
    then have eq: "x ! i = y ! i" if "i < length x" for i
      using that True by (metis Suc_le_eq le_trans nth_append)
    have "?lhs ! (length x) = \<sharp>"
      by (metis Cons_eq_appendI nth_append_length)
    then have "?rhs ! (length x) = \<sharp>"
      using * by metis
    moreover have "y ! i \<noteq> \<sharp>" if "i < length y" for i
      using that assms(3) by auto
    ultimately have "length y \<le> length x"
      by (metis linorder_le_less_linear nth_append)
    then have "length y = length x"
      using True by simp
    then show ?thesis
      using eq by (simp add: list_eq_iff_nth_eq)
  next
    case False
    then have "?lhs ! i = ?rhs ! i" if "i < length y" for i
      using that * by simp
    have "?rhs ! (length y) = \<sharp>"
      by (metis Cons_eq_appendI nth_append_length)
    then have "?lhs ! (length y) = \<sharp>"
      using * by metis
    then have "x ! (length y) = \<sharp>"
      using False by (simp add: nth_append)
    then have False
      using assms(2) False
      by (simp add: order_less_le)
    then show ?thesis
      by simp
  qed
qed

lemma numlistlist_inj: "numlistlist ns1 = numlistlist ns2 \<Longrightarrow> ns1 = ns2"
proof (induction ns1 arbitrary: ns2)
  case Nil
  then show ?case
    using numlistlist_def by simp
next
  case (Cons n ns1)
  have 1: "numlistlist (n # ns1) = (numlist n @ [\<sharp>]) @ numlistlist ns1"
    using numlistlist_def by simp
  then have "numlistlist ns2 = (numlist n @ [\<sharp>]) @ numlistlist ns1"
    using Cons by simp
  then have "ns2 \<noteq> []"
    using numlistlist_Nil by auto
  then have 2: "ns2 = hd ns2 # tl ns2"
    using `ns2 \<noteq> []` by simp
  then have 3: "numlistlist ns2 = (numlist (hd ns2) @ [\<sharp>]) @ numlistlist (tl ns2)"
    using numlistlist_def by (metis concat.simps(2) list.simps(9))

  have 4: "hd ns2 = n"
    using symbols_lt_prefix_eq 1 3 symbols_lt_numlist numlist_inj Cons by metis
  then have "numlistlist ns2 = (numlist n @ [\<sharp>]) @ numlistlist (tl ns2)"
    using 3 by simp
  then have "numlistlist ns1 = numlistlist (tl ns2)"
    using 1 by (simp add: Cons.prems)
  then have "ns1 = tl ns2"
    using Cons by simp
  then show ?case
    using 2 4 by simp
qed

lemma numlistlist_append: "numlistlist (xs @ ys) = numlistlist xs @ numlistlist ys"
  using numlistlist_def by simp

text \<open>
Similar to @{text "\<lfloor>_\<rfloor>\<^sub>N"} and @{text "\<lfloor>_\<rfloor>\<^sub>N\<^sub>L"}, the tape contents for a list
of list of numbers:
\<close>

definition nllcontents :: "nat list list \<Rightarrow> (nat \<Rightarrow> symbol)" ("\<lfloor>_\<rfloor>\<^sub>N\<^sub>L\<^sub>L") where
  "\<lfloor>nss\<rfloor>\<^sub>N\<^sub>L\<^sub>L \<equiv> \<lfloor>numlistlist nss\<rfloor>"

lemma clean_tape_nllcontents: "clean_tape (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L\<^sub>L, i)"
  by (simp add: nllcontents_def proper_symbols_numlistlist)

lemma nllcontents_Nil: "\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L\<^sub>L = \<lfloor>[]\<rfloor>"
  using nllcontents_def by (simp add: numlistlist_Nil)

text \<open>
Similar to @{const nlength} and @{const nllength}, the length of the
representation of a list of lists of numbers:
\<close>

definition nlllength :: "nat list list \<Rightarrow> nat" where
  "nlllength nss \<equiv> length (numlistlist nss)"

lemma nlllength: "nlllength nss = (\<Sum>ns\<leftarrow>nss. Suc (nllength ns))"
  using nlllength_def numlistlist_def nllength_def by (induction nss) simp_all

lemma nlllength_Nil [simp]: "nlllength [] = 0"
  using nlllength_def numlistlist_def by simp

lemma nlllength_Cons: "nlllength (ns # nss) = Suc (nllength ns) + nlllength nss"
  by (simp add: nlllength)

lemma length_le_nlllength: "length nss \<le> nlllength nss"
  using nlllength sum_list_mono[of nss "\<lambda>_. 1" "\<lambda>ns. Suc (nllength ns)"] sum_list_const[of 1 nss]
  by simp

lemma member_le_nlllength_1: "ns \<in> set nss \<Longrightarrow> nllength ns \<le> nlllength nss - 1"
  using nlllength by (induction nss) auto

lemma nlllength_take:
  assumes "i < length nss"
  shows "nlllength (take i nss) + nllength (nss ! i) < nlllength nss"
proof -
  have "nss = take i nss @ [nss ! i] @ drop (Suc i) nss"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "numlistlist nss = numlistlist (take i nss) @ numlistlist [nss ! i] @ numlistlist (drop (Suc i) nss)"
    using numlistlist_append by metis
  then have "nlllength nss = nlllength (take i nss) + nlllength [nss ! i] + nlllength (drop (Suc i) nss)"
    by (simp add: nlllength_def)
  then have "nlllength nss \<ge> nlllength (take i nss) + nlllength [nss ! i]"
    by simp
  then have "nlllength nss \<ge> nlllength (take i nss) + Suc (nllength (nss ! i))"
    using nlllength by simp
  then show ?thesis
    by simp
qed

lemma take_drop_numlistlist:
  assumes "i < length ns"
  shows "take (Suc (nllength (ns ! i))) (drop (nlllength (take i ns)) (numlistlist ns)) = numlist (ns ! i) @ [\<sharp>]"
proof -
  have "numlistlist ns = numlistlist (take i ns) @ numlistlist (drop i ns)"
    using numlistlist_append by (metis append_take_drop_id)
  moreover have "numlistlist (drop i ns) = numlistlist [ns ! i] @ numlistlist (drop (Suc i) ns)"
    using assms numlistlist_append by (metis Cons_nth_drop_Suc append_Cons self_append_conv2)
  ultimately have "numlistlist ns = numlistlist (take i ns) @ numlistlist [ns ! i] @ numlistlist (drop (Suc i) ns)"
    by simp
  then have "drop (nlllength (take i ns)) (numlistlist ns) = numlistlist [ns ! i] @ numlistlist (drop (Suc i) ns)"
    by (simp add: nlllength_def)
  then have "drop (nlllength (take i ns)) (numlistlist ns) = numlist (ns ! i) @ [\<sharp>] @ numlistlist (drop (Suc i) ns)"
    using numlistlist_def by simp
  then show ?thesis
    by (simp add: nllength_def)
qed

corollary take_drop_numlistlist':
  assumes "i < length ns"
  shows "take (nllength (ns ! i)) (drop (nlllength (take i ns)) (numlistlist ns)) = numlist (ns ! i)"
  using take_drop_numlistlist[OF assms] nllength_def by (metis append_assoc append_eq_conv_conj append_take_drop_id)

corollary numlistlist_take_at_term:
  assumes "i < length ns"
  shows "numlistlist ns ! (nlllength (take i ns) + nllength (ns ! i)) = \<sharp>"
  using assms take_drop_numlistlist nlllength_def numlistlist_append
  by (smt (z3) append_eq_conv_conj append_take_drop_id lessI nllength_def nth_append_length nth_append_length_plus nth_take)

lemma nlllength_take_Suc:
  assumes "i < length ns"
  shows "nlllength (take i ns) + Suc (nllength (ns ! i)) = nlllength (take (Suc i) ns)"
proof -
  have "ns = take i ns @ [ns ! i] @ drop (Suc i) ns"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "numlistlist ns = numlistlist (take i ns) @ numlistlist [ns ! i] @ numlistlist (drop (Suc i) ns)"
    using numlistlist_append by metis
  then have "nlllength ns = nlllength (take i ns) + nlllength [ns ! i] + nlllength (drop (Suc i) ns)"
    by (simp add: nlllength_def)
  moreover have "nlllength ns = nlllength (take (Suc i) ns) + nlllength (drop (Suc i) ns)"
    using numlistlist_append by (metis append_take_drop_id length_append nlllength_def)
  ultimately have "nlllength (take (Suc i) ns) = nlllength (take i ns) + nlllength [ns ! i]"
    by simp
  then show ?thesis
    using nlllength by simp
qed

lemma numlistlist_take_at:
  assumes "i < length ns" and "j < nllength (ns ! i)"
  shows "numlistlist ns ! (nlllength (take i ns) + j) = numlist (ns ! i) ! j"
proof -
  have "ns = take i ns @ [ns ! i] @ drop (Suc i) ns"
    using assms by (metis Cons_eq_appendI append_self_conv2 id_take_nth_drop)
  then have "numlistlist ns = (numlistlist (take i ns) @ numlistlist [ns ! i]) @ numlistlist (drop (Suc i) ns)"
    using numlistlist_append by (metis append_assoc)
  moreover have "nlllength (take i ns) + j < nlllength (take i ns) + nlllength [ns ! i]"
    using assms(2) nlllength by simp
  ultimately have "numlistlist ns ! (nlllength (take i ns) + j) =
      (numlistlist (take i ns) @ numlistlist [ns ! i]) ! (nlllength (take i ns) + j)"
    by (metis length_append nlllength_def nth_append)
  also have "... = numlistlist [ns ! i] ! j"
    by (simp add: nlllength_def)
  also have "... = (numlist (ns ! i) @ [\<sharp>]) ! j"
    using numlistlist_def by simp
  also have "... = numlist (ns ! i) ! j"
    using assms(2) by (metis nllength_def nth_append)
  finally show ?thesis .
qed

lemma nllcontents_rneigh_5:
  assumes "i < length ns"
  shows "rneigh (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc (nlllength (take i ns))) {\<sharp>} (nllength (ns ! i))"
proof (rule rneighI)
  let ?tp = "(\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc (nlllength (take i ns)))"
  show "fst ?tp (snd ?tp + nllength (ns ! i)) \<in> {\<sharp>}"
  proof -
    have "snd ?tp + nllength (ns ! i) \<le> nlllength ns"
      using nlllength_take assms by (simp add: Suc_leI)
    then have "fst ?tp (snd ?tp + nllength (ns ! i)) =
        numlistlist ns ! (nlllength (take i ns) + nllength (ns ! i))"
      using nllcontents_def contents_inbounds nlllength_def by simp
    then show ?thesis
      using numlistlist_take_at_term assms by simp
  qed
  show "fst ?tp (snd ?tp + j) \<notin> {\<sharp>}" if "j < nllength (ns ! i)" for j
  proof -
    have "snd ?tp + nllength (ns ! i) \<le> nlllength ns"
      using nlllength_take assms by (simp add: Suc_leI)
    then have "snd ?tp + j \<le> nlllength ns"
      using that by simp
    then have "fst ?tp (snd ?tp + j) = numlistlist ns ! (nlllength (take i ns) + j)"
      using nllcontents_def contents_inbounds nlllength_def by simp
    then have "fst ?tp (snd ?tp + j) = numlist (ns ! i) ! j"
      using assms that numlistlist_take_at by simp
    moreover have "numlist (ns ! i) ! j \<noteq> \<sharp>"
      using numlist_234 that nllength_def nth_mem by fastforce
    ultimately show ?thesis
      by simp
  qed
qed

text \<open>
A tape containing a list of lists of numbers, with the tape head after all
the symbols:
\<close>

abbreviation nlltape :: "nat list list \<Rightarrow> tape" where
  "nlltape ns \<equiv> (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc (nlllength ns))"

text \<open>
Like before but with the tape head or at the beginning of the $i$-th list
element:
\<close>

abbreviation nlltape' :: "nat list list \<Rightarrow> nat \<Rightarrow> tape" where
  "nlltape' ns i \<equiv> (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc (nlllength (take i ns)))"

lemma nlltape'_0: "nlltape' ns 0 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
  using nlllength by simp

lemma nlltape'_tape_read: "|.| (nlltape' nss i) = 0 \<longleftrightarrow> i \<ge> length nss"
proof -
  have "|.| (nlltape' nss i) = 0" if "i \<ge> length nss" for i
  proof -
    have "nlltape' nss i \<equiv> (\<lfloor>nss\<rfloor>\<^sub>N\<^sub>L\<^sub>L, Suc (nlllength nss))"
      using that by simp
    then show ?thesis
      using nllcontents_def contents_outofbounds nlllength_def
      by (metis Suc_eq_plus1 add.left_neutral fst_conv less_Suc0 less_add_eq_less snd_conv)
  qed
  moreover have "|.| (nlltape' nss i) \<noteq> 0" if "i < length nss" for i
    using that nllcontents_def contents_inbounds nlllength_def nlllength_take proper_symbols_numlistlist
    by (metis Suc_leI add_Suc_right diff_Suc_1 fst_conv less_add_same_cancel1 less_le_trans not_add_less2
      plus_1_eq_Suc snd_conv zero_less_Suc)
  ultimately show ?thesis
    by (meson le_less_linear)
qed


subsection \<open>Appending an element\<close>

text \<open>
The next Turing machine is very similar to @{const tm_append}, just with
terminator symbol @{text \<sharp>} instead of @{text "\<bar>"}. It appends a list of
numbers given on tape $j_2$ to the list of lists of numbers on tape $j_1$.
\<close>

definition tm_appendl :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_appendl j1 j2 \<equiv>
    tm_right_until j1 {\<box>} ;;
    tm_cp_until j2 j1 {\<box>} ;;
    tm_cr j2 ;;
    tm_char j1 \<sharp>"

lemma tm_appendl_tm:
  assumes "0 < j1" and "G \<ge> 6" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_appendl j1 j2)"
  unfolding tm_appendl_def using assms tm_right_until_tm tm_cp_until_tm tm_char_tm tm_cr_tm by simp

locale turing_machine_appendl =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_right_until j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_cp_until j2 j1 {\<box>}"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"
definition "tm4 \<equiv> tm3 ;; tm_char j1 \<sharp>"

lemma tm4_eq_tm_append: "tm4 = tm_appendl j1 j2"
  unfolding tm4_def tm3_def tm2_def tm1_def tm_appendl_def by simp

context
  fixes tps0 :: "tape list" and k i1 :: nat and ns :: "nat list" and nss :: "nat list list"
  assumes jk: "length tps0 = k" "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j1"
    and i1: "i1 \<le> Suc (nlllength nss)"
  assumes tps0:
     "tps0 ! j1 = (\<lfloor>nss\<rfloor>\<^sub>N\<^sub>L\<^sub>L, i1)"
     "tps0 ! j2 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
begin

definition "tps1 \<equiv> tps0[j1 := nlltape nss]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (Suc (nlllength nss) - i1)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk)
  let ?l = "Suc (nlllength nss) - i1"
  show "rneigh (tps0 ! j1) {0} ?l"
  proof (rule rneighI)
    show "(tps0 ::: j1) (tps0 :#: j1 + ?l) \<in> {0}"
      using tps0 jk nllcontents_def nlllength_def by simp
    show "(tps0 ::: j1) (tps0 :#: j1 + i) \<notin> {0}" if "i < Suc (nlllength nss) - i1" for i
    proof -
      have "i1 + i < Suc (nlllength nss)"
        using that i1 by simp
      then show ?thesis
        using proper_symbols_numlistlist nlllength_def tps0 nllcontents_def contents_def
        by (metis One_nat_def Suc_leI diff_Suc_1 fst_conv less_Suc_eq_0_disj less_nat_zero_code singletonD snd_conv)
    qed
  qed
  show "ttt = Suc (Suc (nlllength nss) - i1)"
    using assms(1) .
  show "tps1 = tps0[j1 := tps0 ! j1 |+| Suc (nlllength nss) - i1]"
    using tps1_def tps0 i1 by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (nlllength nss) + nllength ns),
   j2 := (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength ns))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 3 + nlllength nss - i1 + nllength ns"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk tps1_def)
  have j1: "tps1 ! j1 = nlltape nss"
    using tps1_def by (simp add: jk)
  have j2: "tps1 ! j2 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
    using tps1_def tps0 jk by simp
  show "rneigh (tps1 ! j2) {0} (nllength ns)"
  proof (rule rneighI)
    show "(tps1 ::: j2) (tps1 :#: j2 + nllength ns) \<in> {0}"
      using j2 by (simp add: nlcontents_def nllength_def)
    show "\<And>i. i < nllength ns \<Longrightarrow> (tps1 ::: j2) (tps1 :#: j2 + i) \<notin> {0}"
      using j2 tps0 contents_def nlcontents_def nllength_def proper_symbols_numlist by fastforce
  qed
  show "tps2 = tps1
    [j2 := tps1 ! j2 |+| nllength ns,
     j1 := implant (tps1 ! j2) (tps1 ! j1) (nllength ns)]"
    (is "_ = ?rhs")
  proof -
    have "implant (tps1 ! j2) (tps1 ! j1) (nllength ns) = implant (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1) (nlltape nss) (nllength ns)"
      using j1 j2 by simp
    also have "... =
      (\<lfloor>numlistlist nss @ (take (nllength ns) (drop (1 - 1) (numlist ns)))\<rfloor>,
       Suc (length (numlistlist nss)) + nllength ns)"
      using implant_contents nlcontents_def nllength_def nllcontents_def nlllength_def by simp
    also have "... = (\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (length (numlistlist nss)) + nllength ns)"
      by (simp add: nllength_def)
    also have "... = (\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (nlllength nss) + nllength ns)"
      using nlllength_def by simp
    also have "... = tps2 ! j1"
      using jk tps2_def by (metis nth_list_update_eq nth_list_update_neq)
    finally have "implant (tps1 ! j2) (tps1 ! j1) (nllength ns) = tps2 ! j1" .
    then have "tps2 ! j1 = implant (tps1 ! j2) (tps1 ! j1) (nllength ns)"
      by simp
    then have "tps2 ! j1 = ?rhs ! j1"
      using tps1_def jk by (metis length_list_update nth_list_update_eq)
    moreover have "tps2 ! j2 = ?rhs ! j2"
      using tps2_def tps1_def jk j2 by simp
    moreover have "tps2 ! j = ?rhs ! j" if "j < length tps2" "j \<noteq> j1" "j \<noteq> j2" for j
      using that tps2_def tps1_def by simp
    moreover have "length tps2 = length ?rhs"
      using tps1_def tps2_def by simp
    ultimately show ?thesis
      using nth_equalityI by blast
  qed
  show "ttt = Suc (Suc (nlllength nss) - i1) + Suc (nllength ns)"
    using assms(1) j1 tps0 i1 by simp
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (nlllength nss) + nllength ns)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 6 + nlllength nss - i1 + 2 * nllength ns"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: jk i1 tps2_def)
  let ?tp1 = "(\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (nlllength nss + nllength ns))"
  let ?tp2 = "(\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, Suc (nllength ns))"
  show "clean_tape (tps2 ! j2)"
    using tps2_def jk by (simp add: clean_tape_nlcontents)
  show "tps3 = tps2[j2 := tps2 ! j2 |#=| 1]"
    using tps3_def tps2_def jk tps0(2)
    by (metis fst_eqD length_list_update list_update_overwrite list_update_same_conv nth_list_update)
  show "ttt = 3 + nlllength nss - i1 + nllength ns + (tps2 :#: j2 + 2)"
    using assms tps2_def jk tps0 i1 by simp
qed

definition "tps4 \<equiv> tps0
  [j1 := (\<lfloor>numlistlist (nss @ [ns])\<rfloor>, Suc (nlllength (nss @ [ns])))]"

lemma tm4:
  assumes "ttt = 7 + nlllength nss - i1 + 2 * nllength ns"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: jk tps3_def time: jk i1 assms)
  show "tps4 = tps3[j1 := tps3 ! j1 |:=| \<sharp> |+| 1]"
    (is "tps4 = ?tps")
  proof -
    have "tps3 ! j1 = (\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (nlllength nss) + nllength ns)"
      using tps3_def jk by simp
    then have "?tps = tps0[j1 := (\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (nlllength nss + nllength ns)) |:=| \<sharp> |+| 1]"
      using tps3_def by simp
    moreover have "(\<lfloor>numlistlist nss @ numlist ns\<rfloor>, Suc (nlllength nss + nllength ns)) |:=| \<sharp> |+| 1 =
        (\<lfloor>numlistlist (nss @ [ns])\<rfloor>, Suc (nlllength (nss @ [ns])))"
      (is "?lhs = ?rhs")
    proof -
      have "?lhs =
        (\<lfloor>numlistlist nss @ numlist ns\<rfloor>(Suc (nlllength nss + nllength ns) := \<sharp>),
         Suc (Suc (nlllength nss + nllength ns)))"
        by simp
      also have "... =
        (\<lfloor>numlistlist nss @ numlist ns\<rfloor>(Suc (nlllength nss + nllength ns) := \<sharp>),
         Suc (nlllength (nss @ [ns])))"
        using nlllength_def numlistlist_def nllength_def numlist_def by simp
      also have "... = (\<lfloor>(numlistlist nss @ numlist ns) @ [\<sharp>]\<rfloor>, Suc (nlllength (nss @ [ns])))"
        using contents_snoc nlllength_def nllength_def by (metis length_append)
      also have "... = (\<lfloor>numlistlist nss @ numlist ns @ [\<sharp>]\<rfloor>, Suc (nlllength (nss @ [ns])))"
        by simp
      also have "... = (\<lfloor>numlistlist (nss @ [ns])\<rfloor>, Suc (nlllength (nss @ [ns])))"
        using numlistlist_def by simp
      finally show "?lhs = ?rhs" .
    qed
    ultimately show ?thesis
      using tps4_def by auto
  qed
qed

end  (* context *)

end  (* locale turing_machine_appendl *)

lemma transforms_tm_appendlI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and ttt k i1 :: nat and ns :: "nat list" and nss :: "nat list list"
  assumes "0 < j1"
  assumes "length tps = k" "j1 < k" "j2 < k" "j1 \<noteq> j2"
    and "i1 \<le> Suc (nlllength nss)"
  assumes
    "tps ! j1 = (\<lfloor>nss\<rfloor>\<^sub>N\<^sub>L\<^sub>L, i1)"
    "tps ! j2 = (\<lfloor>ns\<rfloor>\<^sub>N\<^sub>L, 1)"
  assumes "ttt = 7 + nlllength nss - i1 + 2 * nllength ns"
  assumes "tps' = tps
    [j1 := nlltape (nss @ [ns])]"
  shows "transforms (tm_appendl j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_appendl j1 j2 .
  show ?thesis
    using loc.tps4_def loc.tm4 loc.tm4_eq_tm_append assms nllcontents_def by simp
qed

subsection \<open>Extending with a list\<close>

text \<open>
The next Turing machine extends a list of lists of numbers with another list of
lists of numbers. It is in fact the same TM as for extending a list of numbers
because in both cases extending means simply copying the contents from one tape
to another.  We introduce a new name for this TM and express the semantics in
terms of lists of lists of numbers.  The proof is almost the same except with
@{const nllength} replaced by @{const nlllength} and so on.
\<close>

definition tm_extendl :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_extendl \<equiv> tm_extend"

lemma tm_extendl_tm:
  assumes "0 < j1" and "G \<ge> 4" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_extendl j1 j2)"
  unfolding tm_extendl_def using assms tm_extend_tm by simp

locale turing_machine_extendl =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_cp_until j2 j1 {\<box>}"
definition "tm2 \<equiv> tm1 ;; tm_cr j2"

lemma tm2_eq_tm_extendl: "tm2 = tm_extendl j1 j2"
  unfolding tm2_def tm2_def tm1_def tm_extendl_def tm_extend_def by simp

context
  fixes tps0 :: "tape list" and k :: nat and nss1 nss2 :: "nat list list"
  assumes jk: "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "length tps0 = k"
  assumes tps0:
    "tps0 ! j1 = nlltape nss1"
    "tps0 ! j2 = (\<lfloor>nss2\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
begin

definition "tps1 \<equiv> tps0
  [j1 := nlltape (nss1 @ nss2),
   j2 := nlltape nss2]"

lemma tm1 [transforms_intros]:
  assumes "ttt = Suc (nlllength nss2)"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: tps1_def tps0 jk time: assms)
  let ?n = "nlllength nss2"
  show "rneigh (tps0 ! j2) {\<box>} ?n"
  proof (rule rneighI)
    show "(tps0 ::: j2) (tps0 :#: j2 + nlllength nss2) \<in> {\<box>}"
      using tps0 nllcontents_def nlllength_def jk by simp
    show "\<And>i. i < nlllength nss2 \<Longrightarrow> (tps0 ::: j2) (tps0 :#: j2 + i) \<notin> {\<box>}"
      using tps0 jk contents_def nllcontents_def nlllength_def proper_symbols_numlistlist
      by fastforce
  qed
  show "tps1 = tps0
    [j2 := tps0 ! j2 |+| nlllength nss2,
     j1 := implant (tps0 ! j2) (tps0 ! j1) (nlllength nss2)]"
  proof -
    have "implant (\<lfloor>nss2\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1) (nlltape nss1) (nlllength nss2) = nlltape (nss1 @ nss2)"
      using nllcontents_def nlllength_def implant_contents by (simp add: numlistlist_append)
    moreover have "tps1 ! j2 = tps0 ! j2 |+| nlllength nss2"
      using tps0 jk tps1_def by simp
    ultimately show ?thesis
      using tps0 jk tps1_def by (metis fst_conv list_update_swap plus_1_eq_Suc snd_conv)
  qed
qed

definition "tps2 \<equiv> tps0[j1 := nlltape (nss1 @ nss2)]"

lemma tm2:
  assumes "ttt = 4 + 2 * nlllength nss2"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps1_def tps2_def jk time: assms tps1_def jk)
  show "clean_tape (tps1 ! j2)"
    using tps1_def jk clean_tape_nllcontents by simp
  show "tps2 = tps1[j2 := tps1 ! j2 |#=| 1]"
    using tps1_def jk tps2_def tps0(2)
    by (metis fst_conv length_list_update list_update_id list_update_overwrite nth_list_update)
qed

end  (* context tps0 *)

end  (* locale turing_machine_extendl *)

lemma transforms_tm_extendlI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k :: nat and nss1 nss2 :: "nat list list"
  assumes "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "length tps = k"
  assumes
    "tps ! j1 = nlltape nss1"
    "tps ! j2 = (\<lfloor>nss2\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
  assumes "ttt = 4 + 2 * nlllength nss2"
  assumes "tps' = tps[j1 := nlltape (nss1 @ nss2)]"
  shows "transforms (tm_extendl j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_extendl j1 j2 .
  show ?thesis
    using loc.tm2_eq_tm_extendl loc.tm2 loc.tps2_def assms by simp
qed

text \<open>
The next Turing machine erases the appended list.
\<close>

definition tm_extendl_erase :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_extendl_erase j1 j2 \<equiv> tm_extendl j1 j2 ;; tm_erase_cr j2"

lemma tm_extendl_erase_tm:
  assumes "0 < j1" and "0 < j2" and "G \<ge> 4" and "j1 < k" and "j2 < k"
  shows "turing_machine k G (tm_extendl_erase j1 j2)"
  unfolding tm_extendl_erase_def using assms tm_extendl_tm tm_erase_cr_tm by simp

lemma transforms_tm_extendl_eraseI [transforms_intros]:
  fixes tps tps' :: "tape list" and j1 j2 :: tapeidx and ttt k :: nat and nss1 nss2 :: "nat list list"
  assumes "0 < j1" "j1 < k" "j2 < k" "j1 \<noteq> j2" "0 < j2" "length tps = k"
  assumes
    "tps ! j1 = nlltape nss1"
    "tps ! j2 = (\<lfloor>nss2\<rfloor>\<^sub>N\<^sub>L\<^sub>L, 1)"
  assumes "ttt = 11 + 4 * nlllength nss2 "
  assumes "tps' = tps
    [j1 := nlltape (nss1 @ nss2),
     j2 := (\<lfloor>[]\<rfloor>, 1)]"
  shows "transforms (tm_extendl_erase j1 j2) tps ttt tps'"
  unfolding tm_extendl_erase_def
proof (tform tps: assms)
  let ?zs = "numlistlist nss2"
  show "tps[j1 := nlltape (nss1 @ nss2)] ::: j2 = \<lfloor>?zs\<rfloor>"
    using assms by (simp add: nllcontents_def)
  show "proper_symbols ?zs"
    using proper_symbols_numlistlist by simp
  show "ttt = 4 + 2 * nlllength nss2 +
      (tps[j1 := nlltape (nss1 @ nss2)] :#: j2 + 2 * length (numlistlist nss2) + 6)"
    using assms nlllength_def by simp
qed


subsection \<open>Moving to the next element\<close>

text \<open>
Iterating over a list of lists of numbers works with the same Turing machine,
@{const tm_nextract}, as for lists of numbers. We just have to set the parameter
$z$ to the terminator symbol @{text \<sharp>}.  For the proof
we can also just copy from the previous section, replacing the symbol @{text "\<bar>"}
by @{text \<sharp>} and @{const nllength} by @{const nlllength}, etc.

\null
\<close>

locale turing_machine_nextract_5 =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_erase_cr j2"
definition "tm2 \<equiv> tm1 ;; tm_cp_until j1 j2 {\<sharp>}"
definition "tm3 \<equiv> tm2 ;; tm_cr j2"
definition "tm4 \<equiv> tm3 ;; tm_right j1"

lemma tm4_eq_tm_nextract: "tm4 = tm_nextract \<sharp> j1 j2"
  unfolding tm1_def tm2_def tm3_def tm4_def tm_nextract_def by simp

context
  fixes tps0 :: "tape list" and k idx :: nat and nss :: "nat list list" and dummy :: "nat list"
  assumes jk: "j1 < k" "j2 < k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "length tps0 = k"
    and idx: "idx < length nss"
    and tps0:
      "tps0 ! j1 = nlltape' nss idx"
      "tps0 ! j2 = (\<lfloor>dummy\<rfloor>\<^sub>N\<^sub>L, 1)"
begin

definition "tps1 \<equiv> tps0[j2 := (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = 7 + 2 * nllength dummy"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk idx tps0 tps1_def assms)
  show "proper_symbols (numlist dummy)"
    using proper_symbols_numlist by simp
  show "tps1 = tps0[j2 := (\<lfloor>[]\<rfloor>, 1)]"
    using tps1_def by (simp add: nlcontents_def numlist_Nil)
  show "tps0 ::: j2 = \<lfloor>numlist dummy\<rfloor>"
    using tps0 by (simp add: nlcontents_def)
  show "ttt = tps0 :#: j2 + 2 * length (numlist dummy) + 6"
    using tps0 assms nllength_def by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>nss\<rfloor>\<^sub>N\<^sub>L\<^sub>L, nlllength (take (Suc idx) nss)),
   j2 := (\<lfloor>nss ! idx\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (nss ! idx)))]"

lemma tm2 [transforms_intros]:
  assumes "ttt = 7 + 2 * nllength dummy + Suc (nllength (nss ! idx))"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: jk idx tps0 tps2_def tps1_def time: assms)
  show "rneigh (tps1 ! j1) {\<sharp>} (nllength (nss ! idx))"
    using tps1_def tps0 jk by (simp add: idx nllcontents_rneigh_5)
  show "tps2 = tps1
    [j1 := tps1 ! j1 |+| nllength (nss ! idx),
     j2 := implant (tps1 ! j1) (tps1 ! j2) (nllength (nss ! idx))]"
     (is "?l = ?r")
  proof (rule nth_equalityI)
    show len: "length ?l = length ?r"
      using tps1_def tps2_def jk by simp
    show "?l ! i = ?r ! i" if "i < length ?l" for i
    proof -
      consider "i = j1" | "i = j2" | "i \<noteq> j1 \<and> i \<noteq> j2"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          using tps0 that tps1_def tps2_def jk nlllength_take_Suc[OF idx] idx by simp
      next
        case 2
        then have lhs: "?l ! i = (\<lfloor>nss ! idx\<rfloor>\<^sub>N\<^sub>L, Suc (nllength (nss ! idx)))"
          using tps2_def jk by simp
        let ?i = "Suc (nlllength (take idx nss))"
        have i1: "?i > 0"
          by simp
        have "nllength (nss ! idx) + (?i - 1) \<le> nlllength nss"
          using idx nlllength_take by (metis add.commute diff_Suc_1 less_or_eq_imp_le)
        then have i2: "nllength (nss ! idx) + (?i - 1) \<le> length (numlistlist nss)"
          using nlllength_def by simp
        have "?r ! i = implant (tps1 ! j1) (tps1 ! j2) (nllength (nss ! idx))"
          using 2 tps1_def jk by simp
        also have "... = implant (\<lfloor>nss\<rfloor>\<^sub>N\<^sub>L\<^sub>L, ?i) (\<lfloor>[]\<rfloor>\<^sub>N\<^sub>L, 1) (nllength (nss ! idx))"
          using tps1_def jk tps0 by simp
        also have "... =
          (\<lfloor>[] @ (take (nllength (nss ! idx)) (drop (?i - 1) (numlistlist nss)))\<rfloor>,
           Suc (length []) + nllength (nss ! idx))"
          using implant_contents[OF i1 i2] nllcontents_def nlcontents_def numlist_Nil by (metis One_nat_def list.size(3))
        finally have "?r ! i =
          (\<lfloor>[] @ (take (nllength (nss ! idx)) (drop (?i - 1) (numlistlist nss)))\<rfloor>,
           Suc (length []) + nllength (nss ! idx))" .
        then have "?r ! i =
          (\<lfloor>take (nllength (nss ! idx)) (drop (nlllength (take idx nss)) (numlistlist nss))\<rfloor>,
           Suc (nllength (nss ! idx)))"
          by simp
        then have "?r ! i = (\<lfloor>numlist (nss ! idx)\<rfloor>, Suc (nllength (nss ! idx)))"
          using take_drop_numlistlist'[OF idx] by simp
        then show ?thesis
          using lhs nlcontents_def by simp
      next
        case 3
        then show ?thesis
          using that tps1_def tps2_def jk by simp
      qed
    qed
  qed
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>nss\<rfloor>\<^sub>N\<^sub>L\<^sub>L, nlllength (take (Suc idx) nss)),
   j2 := (\<lfloor>nss ! idx\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = 11 + 2 * nllength dummy + 2 * (nllength (nss ! idx))"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: jk idx tps0 tps2_def tps3_def assms)
  show "clean_tape (tps2 ! j2)"
    using tps2_def jk clean_tape_nlcontents by simp
qed

definition "tps4 \<equiv> tps0
  [j1 := nlltape' nss (Suc idx),
   j2 := (\<lfloor>nss ! idx\<rfloor>\<^sub>N\<^sub>L, 1)]"

lemma tm4:
  assumes "ttt = 12 + 2 * nllength dummy + 2 * (nllength (nss ! idx))"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def by (tform tps: jk idx tps0 tps3_def tps4_def assms)

end  (* context *)

end  (* locale turing_machine_nextract *)

lemma transforms_tm_nextract_5I [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes tps tps' :: "tape list" and k idx :: nat and nss :: "nat list list" and dummy :: "nat list"
  assumes "j1 < k" "j2 < k" "0 < j1" "0 < j2" "j1 \<noteq> j2" "length tps = k"
    and "idx < length nss"
  assumes
    "tps ! j1 = nlltape' nss idx"
    "tps ! j2 = (\<lfloor>dummy\<rfloor>\<^sub>N\<^sub>L, 1)"
  assumes "ttt = 12 + 2 * nllength dummy + 2 * (nllength (nss ! idx))"
  assumes "tps' = tps
    [j1 := nlltape' nss (Suc idx),
     j2 := (\<lfloor>nss ! idx\<rfloor>\<^sub>N\<^sub>L, 1)]"
  shows "transforms (tm_nextract \<sharp> j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_nextract_5 j1 j2 .
  show ?thesis
    using assms loc.tm4 loc.tps4_def loc.tm4_eq_tm_nextract by simp
qed

end
