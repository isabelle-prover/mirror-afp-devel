(* Title: Cyclic_Group.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section {* Cyclic groups *}

theory Cyclic_Group imports
  "HOL-Algebra.Coset"
begin

record 'a cyclic_group = "'a monoid" + 
  generator :: 'a ("\<^bold>g\<index>")

locale cyclic_group = group G
  for G :: "('a, 'b) cyclic_group_scheme" (structure)
  +
  assumes generator_closed [intro, simp]: "generator G \<in> carrier G"
  and generator: "carrier G \<subseteq> range (\<lambda>n :: nat. generator G (^)\<^bsub>G\<^esub> n)"
begin

lemma generatorE [elim?]:
  assumes "x \<in> carrier G"
  obtains n :: nat where "x = generator G (^) n"
using generator assms by auto

lemma inj_on_generator: "inj_on (op (^) \<^bold>g) {..<order G}"
proof(rule inj_onI)
  fix n m
  assume "n \<in> {..<order G}" "m \<in> {..<order G}"
  hence n: "n < order G" and m: "m < order G" by simp_all
  moreover
  assume "\<^bold>g (^) n = \<^bold>g (^) m"
  ultimately show "n = m"
  proof(induction n m rule: linorder_wlog)
    case sym thus ?case by simp
  next
    case (le n m)
    let ?d = "m - n"
    have "\<^bold>g (^) (int m - int n) = \<^bold>g (^) int m \<otimes> inv (\<^bold>g (^) int n)"
      by(simp add: int_pow_diff)
    also have "\<^bold>g (^) int m = \<^bold>g (^) int n" by(simp add: le.prems int_pow_int)
    also have "\<dots> \<otimes> inv (\<^bold>g (^) (int n)) = \<one>" by simp
    finally have "\<^bold>g (^) ?d = \<one>" using le.hyps by(simp add: of_nat_diff[symmetric] int_pow_int)
    { assume "n < m"
      have "carrier G \<subseteq> (\<lambda>n. \<^bold>g (^) n) ` {..<?d}"
      proof
        fix x
        assume "x \<in> carrier G"
        then obtain k :: nat where "x = \<^bold>g (^) k" ..
        also have "\<dots> = (\<^bold>g (^) ?d) (^) (k div ?d) \<otimes> \<^bold>g (^) (k mod ?d)"
          by(simp add: nat_pow_pow nat_pow_mult div_mult_mod_eq)
        also have "\<dots> = \<^bold>g (^) (k mod ?d)"
          using \<open>\<^bold>g (^) ?d = \<one>\<close> by simp
        finally show "x \<in> (\<lambda>n. \<^bold>g (^) n) ` {..<?d}" using `n < m` by auto
      qed
      hence "order G \<le> card ((\<lambda>n. \<^bold>g (^) n) ` {..<?d})"
        by(simp add: order_def card_mono)
      also have "\<dots> \<le> card {..<?d}" by(rule card_image_le) simp
      also have "\<dots> < order G" using `m < order G` by simp
      finally have False by simp }
    with \<open>n \<le> m\<close> show "n = m" by(auto simp add: order.order_iff_strict)
  qed
qed

lemma carrier_conv_generator: 
  "finite (carrier G) \<Longrightarrow> carrier G = (\<lambda>n. \<^bold>g (^) n) ` {..<order G}"
proof -
  assume "finite (carrier G)"
  moreover have "(\<lambda>n. \<^bold>g (^) n) ` {..<order G} \<subseteq> carrier G" by auto
  moreover have "card ((\<lambda>n. \<^bold>g (^) n) ` {..<order G}) \<ge> order G"
    using inj_on_generator by(simp add: card_image)
  ultimately show ?thesis unfolding order_def by(rule card_seteq[symmetric])
qed

lemma bij_betw_generator_carrier:
  "finite (carrier G) \<Longrightarrow> bij_betw (\<lambda>n :: nat. \<^bold>g (^) n) {..<order G} (carrier G)"
by(simp add: bij_betw_def inj_on_generator carrier_conv_generator)

end

lemma (in monoid) order_in_range_Suc: "order G \<in> range Suc \<longleftrightarrow> finite (carrier G)"
by(cases "order G")(auto simp add: order_def carrier_not_empty intro: card_ge_0_finite)

end
