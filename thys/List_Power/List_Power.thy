(*
Author: Tobias Nipkow
Based on the AFP entry Combinatorics_Words by Holub, Raška and Starosta
*)

section \<open>The Power Operator \<open>^^\<close> on Lists\<close>

theory List_Power
imports Main
begin

overloading pow_list == "compow :: nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
begin

primrec pow_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"pow_list 0 xs = []" |
"pow_list (Suc n) xs = xs @ pow_list n xs"

end

context
begin

interpretation monoid_mult "[]" "append"
  rewrites "power u n = u ^^ n"
proof-
  show "class.monoid_mult [] (@)"
    by (unfold_locales, simp_all)
  show "power.power [] (@) u n = u ^^ n"
    by(induction n) (auto simp add: power.power.simps)
qed

\<comment> \<open>inherited power properties\<close>

lemmas pow_list_zero = power.power_0 and
  pow_list_one = power_Suc0_right and
  pow_list_1 = power_one_right and
  pow_list_Nil = power_one and
  pow_list_2 = power2_eq_square and
  pow_list_Suc = power_Suc and
  pow_list_Suc2 = power_Suc2 and
  pow_list_comm = power_commutes and
  pow_list_add = power_add and
  pow_list_eq_if = power_eq_if and
  pow_list_mult = power_mult and
  pow_list_commuting_commutes = power_commuting_commutes

end

lemma pow_list_alt: "xs^^n = concat (replicate n xs)"
by (induct n) auto

lemma pow_list_single: "[a] ^^ m = replicate m a"
by(simp add: pow_list_alt)

lemma length_pow_list_single [simp]: "length([a] ^^ n) = n"
by (simp add: pow_list_single)

lemma nth_pow_list_single: "i < m \<Longrightarrow> ([a] ^^ m) ! i = a"
by (simp add: pow_list_single)

lemma pow_list_not_NilD: "xs ^^ m \<noteq> [] \<Longrightarrow> 0 < m"
by (cases m) auto

lemma length_pow_list:  "length(xs ^^ k) = k * length xs"
by (induction k) simp+

lemma pow_list_set: "set (w ^^ Suc k) = set w"
by (induction k)(simp_all)

lemma pow_list_slide: "xs @ (ys @ xs) ^^ n  @ ys = (xs @ ys)^^(Suc n)"
by (induction n) simp+

lemma hd_pow_list: "0 < n \<Longrightarrow> hd(xs ^^ n) = hd xs"
by(auto simp: pow_list_alt hd_append gr0_conv_Suc)

lemma rev_pow_list: "rev (xs ^^ m) = (rev xs) ^^ m"
by (induction m)(auto simp: pow_list_comm)

lemma eq_pow_list_iff_eq_exp[simp]: assumes "xs \<noteq> []" shows "xs ^^ k = xs ^^ m \<longleftrightarrow> k = m"
proof
  assume "k = m" thus "xs ^^ k = xs ^^ m" by simp
next
  assume "xs ^^ k = xs ^^ m"
  thus "k = m" using \<open>xs \<noteq> []\<close>[folded length_0_conv]
    by (metis length_pow_list mult_cancel2)
qed

lemma pow_list_Nil_iff_0: "xs \<noteq> [] \<Longrightarrow> xs ^^ m = [] \<longleftrightarrow> m = 0"
by (simp add: pow_list_eq_if)

lemma pow_list_Nil_iff_Nil: "0 < m \<Longrightarrow> xs ^^ m = [] \<longleftrightarrow>  xs = []"
by (cases xs) (auto simp add: pow_list_Nil pow_list_Nil_iff_0)

lemma pow_eq_eq:
  assumes "xs ^^ k = ys ^^ k" and "0 < k"
  shows "(xs::'a list) = ys"
proof-
  have "length xs = length ys"
    using assms(1) length_pow_list by (metis nat_mult_eq_cancel1[OF \<open>0 < k\<close>])
  thus ?thesis by (metis Suc_pred append_eq_append_conv assms(1,2) pow_list.simps(2))
qed

lemma map_pow_list[simp]: "map f (xs ^^ k) = (map f xs) ^^ k"
by (induction k) simp_all

lemma concat_pow_list: "concat (xs ^^ k) = (concat xs) ^^ k"
by (induction k) simp_all

lemma concat_pow_list_single[simp]: "concat ([a] ^^ k) = a ^^ k"
by (simp add: pow_list_alt)

lemma pow_list_single_Nil_iff: "[a] ^^ n = [] \<longleftrightarrow> n = 0"
by (simp add: pow_list_single)

lemma hd_pow_list_single: "k \<noteq> 0 \<Longrightarrow> hd ([a] ^^ k) = a"
by (cases k) simp+

lemma index_pow_mod: "i < length(xs ^^ k) \<Longrightarrow> (xs ^^ k)!i = xs!(i mod length xs)"
proof(induction k)
  have aux:  "length(xs ^^ Suc l) = length(xs ^^ l) + length xs" for l
    by simp
  have aux1: "length (xs ^^ l) \<le> i \<Longrightarrow> i < length(xs ^^ l) + length xs \<Longrightarrow>  i mod length xs = i -  length(xs^^l)" for l
    unfolding length_pow_list[of l xs]
     using less_diff_conv2[of "l * length xs" i "length xs", unfolded add.commute[of "length xs"  "l * length xs"]]
       le_add_diff_inverse[of "l*length xs" i]
    by (simp add: mod_nat_eqI)
  case (Suc k)
  show ?case
    unfolding aux sym[OF pow_list_Suc2[symmetric]] nth_append le_mod_geq
    using aux1[ OF _ Suc.prems[unfolded aux]]
      Suc.IH pow_list_Suc2[symmetric] Suc.prems[unfolded aux] leI[of i "length(xs ^^ k)"] by presburger
qed auto

lemma unique_letter_word: assumes "\<And>c. c \<in> set w \<Longrightarrow> c = a" shows "w = [a] ^^ length w"
  using assms proof (induction w)
  case (Cons b w)
  have "[a] ^^ length w = w" using Cons.IH[OF Cons.prems[OF list.set_intros(2)]]..
  then show "b # w = [a] ^^ length(b # w)"
    unfolding Cons.prems[OF list.set_intros(1)] by auto
qed simp

lemma count_list_pow_list: "count_list (w ^^ k) a = k * (count_list w a)"
by (induction k) simp+

lemma sing_pow_lists: "a \<in> A \<Longrightarrow> [a] ^^ n \<in> lists A"
by (induction n) auto

lemma one_generated_list_power: "u \<in> lists {x} \<Longrightarrow> \<exists>k. concat u = x ^^ k"
proof(induction u rule: lists.induct)
  case Nil
  then show ?case by (metis concat.simps(1) pow_list.simps(1))
next
  case Cons
  then show ?case by (metis concat.simps(2) pow_list_Suc singletonD)
qed

lemma pow_list_in_lists: "0 < k \<Longrightarrow> u ^^ k \<in> lists B \<Longrightarrow> u \<in> lists B"
by (metis Suc_pred in_lists_conv_set pow_list_set)

end
