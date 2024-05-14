theory "Z_mod_power_of_2_TM"
  imports Z_mod_power_of_2 "Karatsuba.Nat_LSBF_TM"
begin

definition ensure_length_tm :: "nat \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"ensure_length_tm k xs =1 fill_tm k xs \<bind> take_tm k"

lemma val_ensure_length_tm[simp, val_simp]: "val (ensure_length_tm k xs) = ensure_length k xs"
  unfolding ensure_length_tm_def ensure_length_def by simp

lemma time_ensure_length_tm[simp]: "time (ensure_length_tm k xs) = 7 + 2 * length xs + 2 * k"
  unfolding ensure_length_tm_def tm_time_simps val_fill_tm time_fill_tm time_take_tm
  length_fill'
  using add_min_max[of k "length xs"] by simp

context int_lsbf_mod
begin

definition reduce_tm :: "nat_lsbf \<Rightarrow> nat_lsbf tm" where
"reduce_tm xs =1 ensure_length_tm k xs"

lemma val_reduce_tm[simp, val_simp]: "val (reduce_tm xs) = reduce xs"
  unfolding reduce_tm_def reduce_def by simp

lemma time_reduce_tm[simp]: "time (reduce_tm xs) = 8 + 2 * length xs + 2 * k"
  unfolding reduce_tm_def by simp

definition add_mod_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"add_mod_tm xs ys =1 xs +\<^sub>n\<^sub>t ys \<bind> reduce_tm"

lemma val_add_mod_tm[simp, val_simp]: "val (add_mod_tm xs ys) = add_mod xs ys"
  unfolding add_mod_tm_def add_mod_def by simp

lemma time_add_mod_tm_le: "time (add_mod_tm xs ys) \<le> 14 + 4 * max (length xs) (length ys) + 2 * k"
  unfolding add_mod_tm_def tm_time_simps val_add_nat_tm time_reduce_tm
  apply (estimation estimate: time_add_nat_tm_le)
  apply (estimation estimate: length_add_nat_upper)
  by simp

definition subtract_mod_tm :: "nat_lsbf \<Rightarrow> nat_lsbf \<Rightarrow> nat_lsbf tm" where
"subtract_mod_tm xs ys =1 do {
  b \<leftarrow> xs \<le>\<^sub>n\<^sub>t ys;
  if b then do {
    fillx \<leftarrow> fill_tm k xs;
    fillx1 \<leftarrow> fillx @\<^sub>t [True];
    fillx1 -\<^sub>n\<^sub>t ys \<bind> reduce_tm
  } else xs -\<^sub>n\<^sub>t ys
}"

lemma val_subtract_mod_tm[simp, val_simp]: "val (subtract_mod_tm xs ys) = subtract_mod xs ys"
  unfolding subtract_mod_tm_def subtract_mod_def by simp

lemma time_subtract_mod_tm_le: "time (subtract_mod_tm xs ys) \<le> 118 + 51 * max k (max (length xs) (length ys))"
proof -
  define m where "m = max k (max (length xs) (length ys))"
  have 1: "max (length (fill k xs @ [True])) (length ys) \<le> m + 1"
    unfolding length_append length_fill' m_def by (auto simp add: max.assoc)
  have "time (subtract_mod_tm xs ys) = time (xs \<le>\<^sub>n\<^sub>t ys) +
    (if xs \<le>\<^sub>n ys
     then time (fill_tm k xs) +
          time ((fill k xs) @\<^sub>t [True]) +
          time ((fill k xs @ [True]) -\<^sub>n\<^sub>t ys) +
          time (reduce_tm ((fill k xs @ [True]) -\<^sub>n ys))
     else time (xs -\<^sub>n\<^sub>t ys)) + 1"
    (is "?t = _ + (if ?b then ?c else ?d) + 1")
    unfolding subtract_mod_tm_def tm_time_simps val_compare_nat_tm
  val_fill_tm val_append_tm val_subtract_nat_tm by simp
  moreover have "?c \<le> (2 * length xs + k + 5) +
      (max k (length xs) + 1) +
      (30 * m + 78) +
      (10 + 2 * m + 2 * k)"
    apply (intro add_mono)
    subgoal unfolding time_fill_tm by simp
    subgoal unfolding time_append_tm length_fill' by simp
    subgoal
      apply (estimation estimate: time_subtract_nat_tm_le)
      apply (itrans "30 * (m + 1) + 48")
      subgoal by (intro add_mono mult_le_mono2 order.refl 1)
      subgoal by simp
      done
    subgoal
      unfolding time_reduce_tm
      apply (estimation estimate: conjunct2[OF subtract_nat_aux])
      apply (estimation estimate: 1)
      by simp
    done
  moreover have "?d \<le> 30 * m + 78"
    apply (estimation estimate: time_subtract_nat_tm_le)
    unfolding m_def by simp
  ultimately have "?t \<le> time (xs \<le>\<^sub>n\<^sub>t ys) +
    ((2 * length xs + k + 5) +
      (max k (length xs) + 1) +
      (30 * m + 78) +
      (10 + 2 * m + 2 * k)) + 1"
    by simp
  also have "... \<le> (13 * m + 23) + ((2 * m + m + 5) + (m + 1) + (30 * m + 78) + (10 + 2 * m + 2 * m)) + 1"
    apply (intro add_mono order.refl)
    subgoal
      apply (estimation estimate: time_compare_nat_tm_le)
      apply (intro add_mono mult_le_mono2 order.refl)
      unfolding m_def by simp
    subgoal unfolding m_def by simp
    subgoal unfolding m_def by simp
    subgoal unfolding m_def by simp
    subgoal unfolding m_def by simp
    done
  also have "... = 118 + 51 * m" by simp
  finally show ?thesis unfolding m_def .
qed

end

end