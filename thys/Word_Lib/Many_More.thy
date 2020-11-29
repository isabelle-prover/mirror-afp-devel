
theory Many_More
  imports
    Main 
    "HOL-Library.Word"
    More_Word
begin

lemma nat_less_mult_monoish: "\<lbrakk> a < b; c < (d :: nat) \<rbrakk> \<Longrightarrow> (a + 1) * (c + 1) <= b * d"
  apply (drule Suc_leI)+
  apply (drule(1) mult_le_mono)
  apply simp
  done

lemma if_and_helper:
  "(If x v v') AND v'' = If x (v AND v'') (v' AND v'')"
  by (rule if_distrib)

lemma eq_eqI:
  "a = b \<Longrightarrow> (a = x) = (b = x)"
  by simp

lemma map2_Cons_2_3:
  "(map2 f xs (y # ys) = (z # zs)) = (\<exists>x xs'. xs = x # xs' \<and> f x y = z \<and> map2 f xs' ys = zs)"
  by (case_tac xs, simp_all)

lemma map2_xor_replicate_False:
  "map2 (\<lambda>x y. x \<longleftrightarrow> \<not> y) xs (replicate n False) = take n xs"
  apply (induct xs arbitrary: n, simp)
  apply (case_tac n; simp)
  done

lemma plus_Collect_helper:
  "(+) x ` {xa. P (xa :: 'a :: len word)} = {xa. P (xa - x)}"
  by (fastforce simp add: image_def)

lemma plus_Collect_helper2:
  "(+) (- x) ` {xa. P (xa :: 'a :: len word)} = {xa. P (x + xa)}"
  using plus_Collect_helper [of "- x" P] by (simp add: ac_simps)

lemma range_subset_eq2:
  "{a :: 'a :: len word .. b} \<noteq> {} \<Longrightarrow> ({a .. b} \<subseteq> {c .. d}) = (c \<le> a \<and> b \<le> d)"
  by simp

lemma nat_mod_power_lem:
  fixes a :: nat
  shows "1 < a \<Longrightarrow> a ^ n mod a ^ m = (if m \<le> n then 0 else a ^ n)"
  apply (clarsimp)
  apply (clarsimp simp add: le_iff_add power_add)
  done

lemma i_hate_words_helper:
  "i \<le> (j - k :: nat) \<Longrightarrow> i \<le> j"
  by simp

lemma i_hate_words:
  "unat (a :: 'a word) \<le> unat (b :: 'a :: len word) - Suc 0
    \<Longrightarrow> a \<noteq> -1"
  apply (frule i_hate_words_helper)
  apply (subst(asm) word_le_nat_alt[symmetric])
  apply (clarsimp simp only: word_minus_one_le)
  apply (simp only: linorder_not_less[symmetric])
  apply (erule notE)
  apply (rule diff_Suc_less)
  apply (subst neq0_conv[symmetric])
  apply (subst unat_eq_0)
  apply (rule notI, drule arg_cong[where f="(+) 1"])
  apply simp
  done

lemma If_eq_obvious:
  "x \<noteq> z \<Longrightarrow> ((if P then x else y) = z) = (\<not> P \<and> y = z)"
  by simp

lemma Some_to_the:
  "v = Some x \<Longrightarrow> x = the v"
  by simp

lemma dom_if_Some:
  "dom (\<lambda>x. if P x then Some (f x) else g x) = {x. P x} \<union> dom g"
  by fastforce

lemma dom_insert_absorb:
  "x \<in> dom f \<Longrightarrow> insert x (dom f) = dom f"
  by (fact insert_absorb)

lemma emptyE2:
  "\<lbrakk> S = {}; x \<in> S \<rbrakk> \<Longrightarrow> P"
  by simp

lemma ptr_add_image_multI:
  "\<lbrakk> \<And>x y. (x * val = y * val') = (x * val'' = y); x * val'' \<in> S \<rbrakk> \<Longrightarrow>
     ptr_add ptr (x * val) \<in> (\<lambda>p. ptr_add ptr (p * val')) ` S"
  by (auto simp add: image_iff) metis

lemmas map_prod_split_imageI'
  = map_prod_imageI[where f="case_prod f" and g="case_prod g"
                    and a="(a, b)" and b="(c, d)" for a b c d f g]
lemmas map_prod_split_imageI = map_prod_split_imageI'[simplified]

lemma dom_if:
  "dom (\<lambda>a. if a \<in> addrs then Some (f a) else g a)  = addrs \<union> dom g"
  by (auto simp: dom_def split: if_split)

lemmas arg_cong_Not = arg_cong [where f=Not]

lemma drop_append_miracle:
  "n = length xs \<Longrightarrow> drop n (xs @ ys) = ys"
  by simp

lemma foldr_does_nothing_to_xf:
  "\<lbrakk> \<And>x s. x \<in> set xs \<Longrightarrow> xf (f x s) = xf s \<rbrakk> \<Longrightarrow> xf (foldr f xs s) = xf s"
  by (induct xs, simp_all)

lemma mod_mod_power_int:
  fixes k :: int
  shows "k mod 2 ^ m mod 2 ^ n = k mod 2 ^ (min m n)"
  by (fact mod_exp_eq)

lemma le_step_down_nat:"\<lbrakk>(i::nat) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

lemma le_step_down_int:"\<lbrakk>(i::int) \<le> n; i = n \<longrightarrow> P; i \<le> n - 1 \<longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by arith

end
