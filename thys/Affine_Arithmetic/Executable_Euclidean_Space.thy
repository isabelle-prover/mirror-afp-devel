section {* Euclidean Space: Executability *}
theory Executable_Euclidean_Space
imports
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  Float_Real
begin

subsection {* Ordered representation of Basis and Rounding of Components *}

class executable_euclidean_space = ordered_euclidean_space +
  fixes Basis_list eucl_down eucl_truncate_down eucl_truncate_up
  assumes eucl_down_def:
    "eucl_down p b = (\<Sum>i \<in> Basis. round_down p (b \<bullet> i) *\<^sub>R i)"
  assumes eucl_truncate_down_def:
    "eucl_truncate_down q b = (\<Sum>i \<in> Basis. truncate_down q (b \<bullet> i) *\<^sub>R i)"
  assumes eucl_truncate_up_def:
    "eucl_truncate_up q b = (\<Sum>i \<in> Basis. truncate_up q (b \<bullet> i) *\<^sub>R i)"
  assumes Basis_list[simp]: "set Basis_list = Basis"
  assumes distinct_Basis_list[simp]: "distinct Basis_list"
begin

lemma length_Basis_list:
  "length Basis_list = card Basis"
  by (metis Basis_list distinct_Basis_list distinct_card)

end

lemma eucl_truncate_down_zero[simp]: "eucl_truncate_down p 0 = 0"
  by (auto simp: eucl_truncate_down_def truncate_down_zero)

lemma eucl_truncate_up_zero[simp]: "eucl_truncate_up p 0 = 0"
  by (auto simp: eucl_truncate_up_def)

subsection {* Instantiations *}

instantiation real::executable_euclidean_space
begin

definition Basis_list_real :: "real list" where
  "Basis_list_real = [1]"

definition "eucl_down prec b = round_down prec b"
definition "eucl_truncate_down prec b = truncate_down prec b"
definition "eucl_truncate_up prec b = truncate_up prec b"

instance proof qed (auto simp: Basis_list_real_def eucl_down_real_def eucl_truncate_down_real_def
  eucl_truncate_up_real_def)

end

instantiation prod::(executable_euclidean_space, executable_euclidean_space)
  executable_euclidean_space
begin

definition Basis_list_prod :: "('a \<times> 'b) list" where
  "Basis_list_prod =
    zip Basis_list (replicate (length (Basis_list::'a list)) 0) @
    zip (replicate (length (Basis_list::'b list)) 0) Basis_list"

definition "eucl_down p a = (eucl_down p (fst a), eucl_down p (snd a))"
definition "eucl_truncate_down p a = (eucl_truncate_down p (fst a), eucl_truncate_down p (snd a))"
definition "eucl_truncate_up p a = (eucl_truncate_up p (fst a), eucl_truncate_up p (snd a))"

instance
proof
  show "set Basis_list = (Basis::('a*'b) set)"
    by (auto simp: Basis_list_prod_def Basis_prod_def elim!: in_set_zipE)
      (auto simp: Basis_list[symmetric] in_set_zip in_set_conv_nth simp del: Basis_list)
  show "distinct (Basis_list::('a*'b)list)"
    using distinct_Basis_list[where 'a='a] distinct_Basis_list[where 'a='b]
    by (auto simp: Basis_list_prod_def Basis_list intro: distinct_zipI1 distinct_zipI2
      elim!: in_set_zipE)
qed
  (auto simp: eucl_down_prod_def eucl_truncate_down_prod_def eucl_truncate_up_prod_def
    setsum_Basis_prod_eq inner_add_left inner_setsum_left inner_Basis eucl_down_def
    eucl_truncate_down_def eucl_truncate_up_def
    intro!: euclidean_eqI[where 'a="'a*'b"])

end

lemma eucl_truncate_down_Basis[simp]:
  "i \<in> Basis \<Longrightarrow> eucl_truncate_down e x \<bullet> i = truncate_down e (x \<bullet> i)"
  by (simp add: eucl_truncate_down_def)

lemma eucl_truncate_down_correct:
  "dist (x::'a::executable_euclidean_space) (eucl_down e x) \<in>
    {0..sqrt (DIM('a)) * 2 powr of_int (- e)}"
proof -
  have "dist x (eucl_down e x) = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (eucl_down e x \<bullet> i))\<^sup>2)"
    unfolding euclidean_dist_l2[where 'a='a] setL2_def ..
  also have "\<dots> \<le> sqrt (\<Sum>i\<in>(Basis::'a set). ((2 powr of_int (- e))\<^sup>2))"
    apply (intro real_sqrt_le_mono setsum_mono power_mono)
    apply (auto simp: dist_real_def eucl_down_def simp del: of_int_minus)
    by (simp add: abs_round_down_le)
  finally show ?thesis
    by (simp add: real_sqrt_mult)
qed

lemma eucl_down: "eucl_down e (x::'a::executable_euclidean_space) \<le> x"
  by (auto simp add: eucl_le[where 'a='a] round_down eucl_down_def)

lemma eucl_truncate_down: "eucl_truncate_down e (x::'a::executable_euclidean_space) \<le> x"
  by (auto simp add: eucl_le[where 'a='a] truncate_down)

lemma eucl_truncate_down_le:
  "x \<le> y \<Longrightarrow> eucl_truncate_down w x \<le> (y::'a::executable_euclidean_space)"
  using eucl_truncate_down
  by (rule order.trans)

lemma eucl_truncate_up_Basis[simp]: "i \<in> Basis \<Longrightarrow> eucl_truncate_up e x \<bullet> i = truncate_up e (x \<bullet> i)"
  by (simp add: eucl_truncate_up_def truncate_up_def)

lemma eucl_truncate_up: "x \<le> eucl_truncate_up e (x::'a::executable_euclidean_space)"
  by (auto simp add: eucl_le[where 'a='a] round_up truncate_up_def)

lemma eucl_truncate_up_le: "x \<le> y \<Longrightarrow> x \<le> eucl_truncate_up e (y::'a::executable_euclidean_space)"
  using _ eucl_truncate_up
  by (rule order.trans)

lemma eucl_truncate_down_mono:
  fixes x::"'a::executable_euclidean_space"
  shows "x \<le> y \<Longrightarrow> eucl_truncate_down p x \<le> eucl_truncate_down p y"
  by (auto simp: eucl_le[where 'a='a] intro!: truncate_down_mono)

lemma eucl_truncate_up_mono:
  fixes x::"'a::executable_euclidean_space"
  shows "x \<le> y \<Longrightarrow> eucl_truncate_up p x \<le> eucl_truncate_up p y"
  by (auto simp: eucl_le[where 'a='a] intro!: truncate_up_mono)

lemma infnorm[code]:
  fixes x::"'a::executable_euclidean_space"
  shows "infnorm x = fold max (map (\<lambda>i. abs (x \<bullet> i)) Basis_list) 0"
  by (auto simp: Max.set_eq_fold[symmetric] infnorm_Max[symmetric] infnorm_pos_le
    intro!: max.absorb2[symmetric])

declare Inf_real_def[code del]
declare Sup_real_def[code del]
declare Inf_prod_def[code del]
declare Sup_prod_def[code del]
declare [[code abort: "Inf::real set \<Rightarrow> real"]]
declare [[code abort: "Sup::real set \<Rightarrow> real"]]
declare [[code abort: "Inf::('a::Inf * 'b::Inf) set \<Rightarrow> 'a * 'b"]]
declare [[code abort: "Sup::('a::Sup * 'b::Sup) set \<Rightarrow> 'a * 'b"]]

end

