(*  Title:      Bits_Int.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>More bit operations on integers\<close>

theory More_Bits_Int
imports
  "HOL-Word.Bits_Int"
  "HOL-Word.Bit_Comprehension"
begin

text \<open>Preliminaries\<close>

lemma last_rev' [simp]: "last (rev xs) = hd xs" \<comment> \<open>TODO define \<open>last []\<close> as \<open>hd []\<close>?\<close>
  by (cases xs) (simp add: last_def hd_def, simp)

lemma nat_LEAST_True: "(LEAST _ :: nat. True) = 0"
  by (rule Least_equality) simp_all

text \<open>
  Use this function to convert numeral @{typ integer}s quickly into @{typ int}s.
  By default, it works only for symbolic evaluation; normally generated code raises
  an exception at run-time. If theory \<open>Code_Target_Bits_Int\<close> is imported,
  it works again, because then @{typ int} is implemented in terms of @{typ integer}
  even for symbolic evaluation.
\<close>

definition int_of_integer_symbolic :: "integer \<Rightarrow> int"
  where "int_of_integer_symbolic = int_of_integer"

lemma int_of_integer_symbolic_aux_code [code nbe]:
  "int_of_integer_symbolic 0 = 0"
  "int_of_integer_symbolic (Code_Numeral.Pos n) = Int.Pos n"
  "int_of_integer_symbolic (Code_Numeral.Neg n) = Int.Neg n"
  by (simp_all add: int_of_integer_symbolic_def)

code_identifier
  code_module Bits_Int \<rightharpoonup>
  (SML) Bit_Operations and (OCaml) Bit_Operations and (Haskell) Bit_Operations and (Scala) Bit_Operations
| code_module More_Bits_Int \<rightharpoonup>
  (SML) Bit_Operations and (OCaml) Bit_Operations and (Haskell) Bit_Operations and (Scala) Bit_Operations
| constant take_bit \<rightharpoonup>
  (SML) Bit_Operations.take_bit and (OCaml) Bit_Operations.take_bit and (Haskell) Bit_Operations.take_bit and (Scala) Bit_Operations.take_bit


section \<open>Symbolic bit operations on numerals and @{typ int}s\<close>

fun bitOR_num :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "bitOR_num num.One num.One = num.One"
| "bitOR_num num.One (num.Bit0 n) = num.Bit1 n"
| "bitOR_num num.One (num.Bit1 n) = num.Bit1 n"
| "bitOR_num (num.Bit0 m) num.One = num.Bit1 m"
| "bitOR_num (num.Bit0 m) (num.Bit0 n) = num.Bit0 (bitOR_num m n)"
| "bitOR_num (num.Bit0 m) (num.Bit1 n) = num.Bit1 (bitOR_num m n)"
| "bitOR_num (num.Bit1 m) num.One = num.Bit1 m"
| "bitOR_num (num.Bit1 m) (num.Bit0 n) = num.Bit1 (bitOR_num m n)"
| "bitOR_num (num.Bit1 m) (num.Bit1 n) = num.Bit1 (bitOR_num m n)"

fun bitAND_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitAND_num num.One num.One = Some num.One"
| "bitAND_num num.One (num.Bit0 n) = None"
| "bitAND_num num.One (num.Bit1 n) = Some num.One"
| "bitAND_num (num.Bit0 m) num.One = None"
| "bitAND_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit1 m) num.One = Some num.One"
| "bitAND_num (num.Bit1 m) (num.Bit0 n) = map_option num.Bit0 (bitAND_num m n)"
| "bitAND_num (num.Bit1 m) (num.Bit1 n) = (case bitAND_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))"

fun bitXOR_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitXOR_num num.One num.One = None"
| "bitXOR_num num.One (num.Bit0 n) = Some (num.Bit1 n)"
| "bitXOR_num num.One (num.Bit1 n) = Some (num.Bit0 n)"
| "bitXOR_num (num.Bit0 m) num.One = Some (num.Bit1 m)"
| "bitXOR_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitXOR_num m n)"
| "bitXOR_num (num.Bit0 m) (num.Bit1 n) = Some (case bitXOR_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')"
| "bitXOR_num (num.Bit1 m) num.One = Some (num.Bit0 m)"
| "bitXOR_num (num.Bit1 m) (num.Bit0 n) = Some (case bitXOR_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')"
| "bitXOR_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (bitXOR_num m n)"

fun bitORN_num :: "num \<Rightarrow> num \<Rightarrow> num"
where
  "bitORN_num num.One num.One = num.One"
| "bitORN_num num.One (num.Bit0 m) = num.Bit1 m"
| "bitORN_num num.One (num.Bit1 m) = num.Bit1 m"
| "bitORN_num (num.Bit0 n) num.One = num.Bit0 num.One"
| "bitORN_num (num.Bit0 n) (num.Bit0 m) = Num.BitM (bitORN_num n m)"
| "bitORN_num (num.Bit0 n) (num.Bit1 m) = num.Bit0 (bitORN_num n m)"
| "bitORN_num (num.Bit1 n) num.One = num.One"
| "bitORN_num (num.Bit1 n) (num.Bit0 m) = Num.BitM (bitORN_num n m)"
| "bitORN_num (num.Bit1 n) (num.Bit1 m) = Num.BitM (bitORN_num n m)"

fun bitANDN_num :: "num \<Rightarrow> num \<Rightarrow> num option"
where
  "bitANDN_num num.One num.One = None"
| "bitANDN_num num.One (num.Bit0 n) = Some num.One"
| "bitANDN_num num.One (num.Bit1 n) = None"
| "bitANDN_num (num.Bit0 m) num.One = Some (num.Bit0 m)"
| "bitANDN_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (bitANDN_num m n)"
| "bitANDN_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (bitANDN_num m n)"
| "bitANDN_num (num.Bit1 m) num.One = Some (num.Bit0 m)"
| "bitANDN_num (num.Bit1 m) (num.Bit0 n) = (case bitANDN_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))"
| "bitANDN_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (bitANDN_num m n)"

lemma int_numeral_bitOR_num: "numeral n OR numeral m = (numeral (bitOR_num n m) :: int)"
by(induct n m rule: bitOR_num.induct) simp_all

lemma int_numeral_bitAND_num: "numeral n AND numeral m = (case bitAND_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(induct n m rule: bitAND_num.induct)(simp_all split: option.split)

lemma int_numeral_bitXOR_num:
  "numeral m XOR numeral n = (case bitXOR_num m n of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(induct m n rule: bitXOR_num.induct)(simp_all split: option.split)

lemma int_or_not_bitORN_num:
  "numeral n OR NOT (numeral m) = (- numeral (bitORN_num n m) :: int)"
  by (induction n m rule: bitORN_num.induct) (simp_all add: add_One BitM_inc_eq)

lemma int_and_not_bitANDN_num:
  "numeral n AND NOT (numeral m) = (case bitANDN_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
  by (induction n m rule: bitANDN_num.induct) (simp_all add: add_One BitM_inc_eq split: option.split)

lemma int_not_and_bitANDN_num:
  "NOT (numeral m) AND numeral n = (case bitANDN_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')"
by(simp add: int_and_not_bitANDN_num[symmetric] int_and_comm)


section \<open>Bit masks of type \<^typ>\<open>int\<close>\<close>

lemma bin_mask_conv_pow2:
  "mask n = 2 ^ n - (1 :: int)"
  by (fact mask_eq_exp_minus_1)
  
lemma bin_mask_ge0: "mask n \<ge> (0 :: int)"
  by (fact mask_nonnegative_int)

lemma and_bin_mask_conv_mod: "x AND mask n = x mod 2 ^ n"
  for x :: int
  by (simp flip: take_bit_eq_mod add: take_bit_eq_mask)

lemma bin_mask_numeral: 
  "mask (numeral n) = (1 :: int) + 2 * mask (pred_numeral n)"
  by (fact mask_numeral)

lemma bin_nth_mask [simp]: "bit (mask n :: int) i \<longleftrightarrow> i < n"
  by (simp add: bit_mask_iff)

lemma bin_sign_mask [simp]: "bin_sign (mask n) = 0"
  by (simp add: bin_sign_def bin_mask_conv_pow2)

lemma bin_mask_p1_conv_shift: "mask n + 1 = (1 :: int) << n"
  by (simp add: bin_mask_conv_pow2 shiftl_int_def)


section \<open>More on bit comprehension\<close>

inductive wf_set_bits_int :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" 
  for f :: "nat \<Rightarrow> bool"
where
  zeros: "\<forall>n' \<ge> n. \<not> f n' \<Longrightarrow> wf_set_bits_int f"
| ones: "\<forall>n' \<ge> n. f n' \<Longrightarrow> wf_set_bits_int f"

lemma wf_set_bits_int_simps: "wf_set_bits_int f \<longleftrightarrow> (\<exists>n. (\<forall>n'\<ge>n. \<not> f n') \<or> (\<forall>n'\<ge>n. f n'))"
by(auto simp add: wf_set_bits_int.simps)

lemma wf_set_bits_int_const [simp]: "wf_set_bits_int (\<lambda>_. b)"
by(cases b)(auto intro: wf_set_bits_int.intros)

lemma wf_set_bits_int_fun_upd [simp]: 
  "wf_set_bits_int (f(n := b)) \<longleftrightarrow> wf_set_bits_int f" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain n'
    where "(\<forall>n''\<ge>n'. \<not> (f(n := b)) n'') \<or> (\<forall>n''\<ge>n'. (f(n := b)) n'')"
    by(auto simp add: wf_set_bits_int_simps)
  hence "(\<forall>n''\<ge>max (Suc n) n'. \<not> f n'') \<or> (\<forall>n''\<ge>max (Suc n) n'. f n'')" by auto
  thus ?rhs by(auto simp only: wf_set_bits_int_simps)
next
  assume ?rhs
  then obtain n' where "(\<forall>n''\<ge>n'. \<not> f n'') \<or> (\<forall>n''\<ge>n'. f n'')" (is "?wf f n'")
    by(auto simp add: wf_set_bits_int_simps)
  hence "?wf (f(n := b)) (max (Suc n) n')" by auto
  thus ?lhs by(auto simp only: wf_set_bits_int_simps)
qed

lemma wf_set_bits_int_Suc [simp]:
  "wf_set_bits_int (\<lambda>n. f (Suc n)) \<longleftrightarrow> wf_set_bits_int f" (is "?lhs \<longleftrightarrow> ?rhs")
by(auto simp add: wf_set_bits_int_simps intro: le_SucI dest: Suc_le_D)

context
  fixes f
  assumes wff: "wf_set_bits_int f"
begin

lemma int_set_bits_unfold_BIT:
  "set_bits f = of_bool (f 0) + (2 :: int) * set_bits (f \<circ> Suc)"
using wff proof cases
  case (zeros n)
  show ?thesis
  proof(cases "\<forall>n. \<not> f n")
    case True
    hence "f = (\<lambda>_. False)" by auto
    thus ?thesis using True by(simp add: o_def)
  next
    case False
    then obtain n' where "f n'" by blast
    with zeros have "(LEAST n. \<forall>n'\<ge>n. \<not> f n') = Suc (LEAST n. \<forall>n'\<ge>Suc n. \<not> f n')"
      by(auto intro: Least_Suc)
    also have "(\<lambda>n. \<forall>n'\<ge>Suc n. \<not> f n') = (\<lambda>n. \<forall>n'\<ge>n. \<not> f (Suc n'))" by(auto dest: Suc_le_D)
    also from zeros have "\<forall>n'\<ge>n. \<not> f (Suc n')" by auto
    ultimately show ?thesis using zeros
      apply (simp (no_asm_simp) add: set_bits_int_def exI
        del: upt.upt_Suc flip: map_map split del: if_split)
      apply (simp only: map_Suc_upt upt_conv_Cons)
      apply simp
      done
  qed
next
  case (ones n)
  show ?thesis
  proof(cases "\<forall>n. f n")
    case True
    hence "f = (\<lambda>_. True)" by auto
    thus ?thesis using True by(simp add: o_def)
  next
    case False
    then obtain n' where "\<not> f n'" by blast
    with ones have "(LEAST n. \<forall>n'\<ge>n. f n') = Suc (LEAST n. \<forall>n'\<ge>Suc n. f n')"
      by(auto intro: Least_Suc)
    also have "(\<lambda>n. \<forall>n'\<ge>Suc n. f n') = (\<lambda>n. \<forall>n'\<ge>n. f (Suc n'))" by(auto dest: Suc_le_D)
    also from ones have "\<forall>n'\<ge>n. f (Suc n')" by auto
    moreover from ones have "(\<exists>n. \<forall>n'\<ge>n. \<not> f n') = False"
      by(auto intro!: exI[where x="max n m" for n m] simp add: max_def split: if_split_asm)
    moreover hence "(\<exists>n. \<forall>n'\<ge>n. \<not> f (Suc n')) = False"
      by(auto elim: allE[where x="Suc n" for n] dest: Suc_le_D)
    ultimately show ?thesis using ones
      apply (simp (no_asm_simp) add: set_bits_int_def exI split del: if_split)
      apply (auto simp add: Let_def hd_map map_tl[symmetric] map_map[symmetric] map_Suc_upt upt_conv_Cons signed_take_bit_Suc
        not_le simp del: map_map)
      done
  qed
qed

lemma bin_last_set_bits [simp]:
  "bin_last (set_bits f) = f 0"
  by (subst int_set_bits_unfold_BIT) simp_all

lemma bin_rest_set_bits [simp]:
  "bin_rest (set_bits f) = set_bits (f \<circ> Suc)"
  by (subst int_set_bits_unfold_BIT) simp_all

lemma bin_nth_set_bits [simp]:
  "bin_nth (set_bits f) m = f m"
using wff proof (induction m arbitrary: f)
  case 0 
  then show ?case
    by (simp add: More_Bits_Int.bin_last_set_bits)
next
  case Suc
  from Suc.IH [of "f \<circ> Suc"] Suc.prems show ?case
    by (simp add: More_Bits_Int.bin_rest_set_bits comp_def bit_Suc)
qed

end

end
