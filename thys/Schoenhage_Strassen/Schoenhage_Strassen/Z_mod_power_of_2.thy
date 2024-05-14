section "The Schoenhage-Strassen Algorithm"

subsection "Representing $\\mathbb{Z}_{2 ^ n}$"

theory Z_mod_power_of_2
  imports "Karatsuba.Nat_LSBF_TM" "Universal_Hash_Families.Universal_Hash_Families_More_Finite_Fields" "Karatsuba.Abstract_Representations_2" "HOL-Number_Theory.Number_Theory"
begin

context cring begin
lemma pow_one_imp_unit:
"(n::nat) > 0 \<Longrightarrow> a \<in> carrier R \<Longrightarrow> a [^] n = \<one> \<Longrightarrow> a \<in> Units R"
  using gr0_implies_Suc[of n] nat_pow_Suc2[of a]
  by (metis Units_one_closed nat_pow_closed unit_factor)
end

definition ensure_length where "ensure_length k xs = take k (fill k xs)"
lemma ensure_length_correct[simp]: "length (ensure_length k xs) = k" using fill_def ensure_length_def by simp
lemma to_nat_ensure_length: "Nat_LSBF.to_nat xs < 2 ^ n \<Longrightarrow> Nat_LSBF.to_nat (ensure_length n xs) = Nat_LSBF.to_nat xs"
  by (simp add: to_nat_take ensure_length_def)

locale int_lsbf_mod =
  fixes k :: nat
  assumes k_positive: "k > 0"
begin

abbreviation n where "n \<equiv> (2::nat) ^ k"

definition Zn where "Zn \<equiv> residue_ring (int n)"

lemma n_positive[simp]: "n > 0"
  by simp

sublocale residues n Zn
  apply unfold_locales
  subgoal using k_positive by simp
  subgoal by (rule Zn_def)
  done

definition to_residue_ring :: "nat_lsbf \<Rightarrow> int" where
"to_residue_ring xs = int (Nat_LSBF.to_nat xs) mod int n"

lemma to_residue_ring_in_carrier: "to_residue_ring xs \<in> carrier Zn"
  unfolding to_residue_ring_def res_carrier_eq by simp

definition from_residue_ring :: "int \<Rightarrow> nat_lsbf" where
"from_residue_ring x = fill k (Nat_LSBF.from_nat (nat x))"

definition reduce where
"reduce xs = ensure_length k xs"

lemma length_reduce: "length (reduce xs) = k"
  unfolding reduce_def using fill_def ensure_length_def by simp

lemma to_nat_reduce: "Nat_LSBF.to_nat (reduce xs) = Nat_LSBF.to_nat xs mod n"
proof (cases "length xs \<le> k")
  case True
  then have "reduce xs = fill k xs" unfolding reduce_def using fill_def ensure_length_def by simp
  also have "... = xs @ (replicate (k - length xs) False)" using fill_def by simp
  finally have "Nat_LSBF.to_nat (reduce xs) = Nat_LSBF.to_nat xs" by simp
  moreover have "Nat_LSBF.to_nat xs \<le> 2 ^ k - 1" using to_nat_length_upper_bound[of xs] True
    by (meson diff_le_mono le_trans one_le_numeral power_increasing)
  hence "Nat_LSBF.to_nat xs < 2 ^ k"
    using Nat.le_diff_conv2 by auto
  ultimately show ?thesis by simp
next
  case False
  then have "length (take k xs) = k" "fill k xs = xs" "xs = (take k xs) @ (drop k xs)" using fill_def by simp_all
  then have "Nat_LSBF.to_nat xs = Nat_LSBF.to_nat (take k xs) + n * Nat_LSBF.to_nat (drop k xs)"
    using to_nat_app[of "take k xs" "drop k xs"] by simp
  moreover have "Nat_LSBF.to_nat (take k xs) \<le> 2 ^ k - 1"
    using to_nat_length_upper_bound[of "take k xs"] \<open>length (take k xs) = k\<close> by simp
  hence "Nat_LSBF.to_nat (take k xs) < 2 ^ k"
    using Nat.le_diff_conv2 by auto
  ultimately show ?thesis unfolding reduce_def using fill_def ensure_length_def by simp
qed

(*fun to_ZMod where
"to_ZMod xs = ZMod n (int (to_nat xs))"
*)

definition add_mod where
"add_mod x y = reduce (add_nat x y)"

definition subtract_mod where
"subtract_mod xs ys =
  (if compare_nat xs ys then
    reduce (subtract_nat ((fill k xs) @ [True]) ys)
  else
    subtract_nat xs ys)"

lemma to_nat_add_mod: "Nat_LSBF.to_nat (add_mod x y) = (Nat_LSBF.to_nat x + Nat_LSBF.to_nat y) mod n"
  by (simp only: to_nat_reduce add_nat_correct add_mod_def)

lemma to_nat_subtract_mod: "length xs \<le> k \<Longrightarrow> length ys \<le> k \<Longrightarrow> int (Nat_LSBF.to_nat (subtract_mod xs ys)) = (int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)) mod n"
proof (cases "Nat_LSBF.to_nat xs \<le> Nat_LSBF.to_nat ys")
  case True
  assume "length xs \<le> k"
  assume "length ys \<le> k"
  then have "Nat_LSBF.to_nat ys \<le> n - 1"
    using to_nat_length_upper_bound[of ys]
    by (meson diff_le_mono le_trans one_le_numeral power_increasing)
  then have "Nat_LSBF.to_nat ys \<le> Nat_LSBF.to_nat xs + n" by simp

  have "int (Nat_LSBF.to_nat (subtract_nat (fill k xs @ [True]) ys) mod n)
    = int ((Nat_LSBF.to_nat xs + n - Nat_LSBF.to_nat ys) mod n)"
    by (simp add: subtract_nat_correct to_nat_app length_fill \<open>length xs \<le> k\<close>)
  also have "... = (int (Nat_LSBF.to_nat xs + n - Nat_LSBF.to_nat ys)) mod n"
    using zmod_int by simp
  also have "... = (int (Nat_LSBF.to_nat xs) + int n - int (Nat_LSBF.to_nat ys)) mod n"
    using \<open>Nat_LSBF.to_nat ys \<le> Nat_LSBF.to_nat xs + n\<close> by (simp add: of_nat_diff)
  also have "... = (int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)) mod n"
    by (metis diff_add_eq int_ops(3) mod_add_self2 of_nat_power)
  finally have "int (Nat_LSBF.to_nat (subtract_nat (fill k xs @ [True]) ys) mod n) = (int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)) mod n" .
  then show ?thesis
    by (simp add: subtract_mod_def compare_nat_correct to_nat_reduce True split: if_splits)
next
  case False
  assume "length xs \<le> k"
  then have "Nat_LSBF.to_nat xs \<le> n - 1" using to_nat_length_upper_bound[of xs]
    by (meson diff_le_mono le_trans one_le_numeral power_increasing)
  assume "length ys \<le> k"
  from False have "int (Nat_LSBF.to_nat (subtract_nat xs ys)) = int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)"
    by (simp add: subtract_nat_correct)
  moreover have "... \<in> {0..<n}"
  proof -
    have "int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys) \<le> int (Nat_LSBF.to_nat xs)" by simp
    also have "... \<le> n - 1" using \<open>Nat_LSBF.to_nat xs \<le> n - 1\<close> n_positive by simp
    also have "... < n" by simp
    finally have "int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys) < n" by simp
    moreover have "int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys) \<ge> 0" using \<open>\<not> Nat_LSBF.to_nat xs \<le> Nat_LSBF.to_nat ys\<close> by simp
    ultimately show ?thesis by simp
  qed
  ultimately have "int (Nat_LSBF.to_nat (subtract_nat xs ys)) = (int (Nat_LSBF.to_nat xs) - int (Nat_LSBF.to_nat ys)) mod n"
    by simp
  then show ?thesis by (simp add: subtract_mod_def compare_nat_correct to_nat_reduce False split: if_splits)
qed

lemma length_subtract_mod: "length xs \<le> k \<Longrightarrow> length ys \<le> k \<Longrightarrow> length (subtract_mod xs ys) \<le> k"
  unfolding subtract_mod_def
  apply (cases "compare_nat xs ys")
  using subtract_nat_aux[of xs ys]
  by (auto simp: Let_def reduce_def ensure_length_def)
  
lemma add_mod_correct: "to_residue_ring (add_mod x y) = to_residue_ring x \<oplus>\<^bsub>Zn\<^esub> to_residue_ring y"
proof -
  have "to_residue_ring (add_mod x y) = to_residue_ring (reduce (add_nat x y))"
    unfolding add_mod_def by simp
  also have "... = (Nat_LSBF.to_nat x + Nat_LSBF.to_nat y) mod n"
    using to_nat_reduce add_nat_correct to_residue_ring_def by simp
  also have "... = (int (Nat_LSBF.to_nat x) mod n + (int (Nat_LSBF.to_nat y) mod n)) mod n"
    by (simp add: zmod_int mod_add_eq)
  finally show ?thesis
    by (simp only: res_add_eq to_residue_ring_def)
qed

lemma subtract_mod_correct:
  assumes "length x \<le> k"
  assumes "length y \<le> k"
  assumes "n > 1"
  shows "to_residue_ring (subtract_mod x y) = to_residue_ring x \<ominus>\<^bsub>Zn\<^esub> to_residue_ring y"
proof -
  have "to_residue_ring (subtract_mod x y) = int (Nat_LSBF.to_nat (subtract_mod x y)) mod int n"
    unfolding to_residue_ring_def by argo
  also have "... = (int (Nat_LSBF.to_nat x) - (int (Nat_LSBF.to_nat y))) mod int n"
    by (simp add: to_nat_subtract_mod assms)
  also have "... = (to_residue_ring x + (- to_residue_ring y mod n)) mod n"
    unfolding diff_conv_add_uminus to_residue_ring_def
    by (simp add: mod_add_eq mod_diff_right_eq)
  also have "... = (to_residue_ring x + (\<ominus>\<^bsub>residue_ring n\<^esub> (to_residue_ring y mod n))) mod n"
    apply (intro_cong "[cong_tag_2 (mod), cong_tag_2 (+)]" more: refl)
    using residues.neg_cong[symmetric, of n] unfolding residues_def using \<open>n > 1\<close>
    by (metis int_ops(2) nat_int_comparison(2))
  also have "... = to_residue_ring x \<ominus>\<^bsub>residue_ring n\<^esub> (to_residue_ring y mod n)"
    unfolding a_minus_def
    by (simp add: residue_ring_def)
  also have "to_residue_ring y mod n = to_residue_ring y"
    using to_residue_ring_def by simp
  finally show ?thesis unfolding Zn_def .
qed

lemma length_from_residue_ring: "x < 2 ^ k \<Longrightarrow> length (from_residue_ring x) = k"
proof -
  assume "x < 2 ^ k"
  have "truncated (Nat_LSBF.from_nat (nat x))"
    using truncate_from_nat by simp
  moreover have "Nat_LSBF.to_nat (Nat_LSBF.from_nat (nat x)) = nat x"
    using nat_lsbf.to_from by simp
  ultimately have "length (Nat_LSBF.from_nat (nat x)) \<le> k" using \<open>x < 2 ^ k\<close> to_nat_length_bound_truncated
    by simp
  then show "length (from_residue_ring x) = k"
    unfolding from_residue_ring_def using length_fill by simp
qed

interpretation int_lsbf_mod: abstract_representation_2 from_residue_ring to_residue_ring "{0..<int n}"
  rewrites "int_lsbf_mod.reduce = reduce"
  and "int_lsbf_mod.representations = {x :: bool list. length x = k}"
proof -
  show "abstract_representation_2 from_residue_ring to_residue_ring {0..<int n}"
    apply unfold_locales
    unfolding to_residue_ring_def from_residue_ring_def by simp_all
  then interpret int_lsbf_mod: abstract_representation_2 from_residue_ring to_residue_ring "{0..<int n}" .
  show "int_lsbf_mod.reduce = reduce"
    unfolding int_lsbf_mod.reduce_def reduce_def
    apply (intro ext)
    apply (intro nat_lsbf_eqI)
    subgoal for x
      unfolding from_residue_ring_def to_nat_fill to_nat_from_nat
    proof -
      have "nat (to_residue_ring x) = nat (int (Nat_LSBF.to_nat x) mod int n)"
        by (simp add: from_residue_ring_def to_residue_ring_def ensure_length_def to_nat_take)
      also have "... = Nat_LSBF.to_nat x mod n"
        unfolding zmod_int[symmetric] nat_int by (rule refl)
      also have "... = Nat_LSBF.to_nat (ensure_length k x)"
        unfolding ensure_length_def by (simp add: to_nat_take)
      finally show "nat (to_residue_ring x) = ..." .
    qed
    subgoal for x
    proof -
      have "length (from_residue_ring (to_residue_ring x)) = k"
        apply (intro length_from_residue_ring)
        unfolding to_residue_ring_def
        using mod_less_divisor[OF n_positive] by simp
      then show ?thesis by simp
    qed
    done
  show "int_lsbf_mod.representations = {x :: bool list. length x = k}"
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> int_lsbf_mod.representations"
    then obtain y where "y < 2 ^ k" "x = from_residue_ring y"
      unfolding int_lsbf_mod.representations_def by auto
    then have "length x = k" by (simp add: length_from_residue_ring)
    then show "x \<in> {x. length x = k}" by simp
  next
    fix x :: "bool list"
    assume "x \<in> {x. length x = k}"
    then have "length x = k" by simp
    have "from_residue_ring (to_residue_ring x) = int_lsbf_mod.reduce x"
      using int_lsbf_mod.reduce_def by simp
    also have "... = reduce x" using \<open>int_lsbf_mod.reduce = reduce\<close> by simp
    also have "... = x" using \<open>length x = k\<close> unfolding reduce_def ensure_length_def fill_def by simp
    finally show "x \<in> int_lsbf_mod.representations"
      unfolding int_lsbf_mod.representations_def
      using int_lsbf_mod.to_type_in_represented_set
      by (metis imageI)
  qed
qed

lemma add_mod_closed: "length (add_mod x y) = k"
  using int_lsbf_mod.range_reduce add_mod_def by blast

end

end