(*Author: Giuliano Losa *)

header {* Definition and properties of the longest common postfix of a set of lists *}

theory LCP
imports Main "~~/src/HOL/Library/List_Prefix"
begin

text {* In the following, @{text ">>="} denotes list postfix *}

definition common_postfix_p :: "('a list) set => 'a list => bool" 
  -- {*Predicate that recognizes the common postfix of a set of lists*}
  -- {*The common postfix of the empty set is the empty list*}
  where
  "common_postfix_p \<equiv> \<lambda> xss xs . if xss = {} then xs = [] else ALL xs' . xs' \<in> xss \<longrightarrow> xs' >>= xs"

definition l_c_p_pred :: "'a list set \<Rightarrow> 'a list => bool"
  -- {*Predicate that recognizes the longest common postfix of a set of lists*}
  where
  "l_c_p_pred \<equiv> \<lambda> xss xs . common_postfix_p xss xs \<and> (ALL xs' . common_postfix_p xss xs' \<longrightarrow> xs >>= xs')"

definition l_c_p:: "'a list set \<Rightarrow> 'a list"
  -- {* The longest common postfix of a set of lists *}
  where
  "l_c_p \<equiv> \<lambda> xss . THE xs . l_c_p_pred xss xs"

lemma l_c_p_ok: "l_c_p_pred xss (l_c_p xss)"
  -- {*Proof that the definition of the longest common postfix of a set of lists is consistent*}
proof %invisible -
  have "\<exists>! x . l_c_p_pred xss x"
  proof (cases)
    assume "xss = {}"
    thus ?thesis by (auto simp add: l_c_p_pred_def common_postfix_p_def)
  next
    assume "xss \<noteq> {}"
    have "\<exists> x . l_c_p_pred xss x"
    proof -
        -- {*By contradiction*}
      { assume "\<forall> x . \<not> l_c_p_pred xss x"
        from `xss \<noteq> {}` obtain xs where "xs \<in> xss" by auto
        { fix n
          have "\<exists> xs . common_postfix_p xss xs \<and> length xs \<ge> n"
          proof (induct n)
            show "\<exists>xs . common_postfix_p xss xs \<and> 0 \<le> length xs" by (auto simp add:common_postfix_p_def)
          next
            fix m
            assume "\<exists> xs . common_postfix_p xss xs \<and> length xs \<ge> m"
            from this obtain xs where "common_postfix_p xss xs" and "length xs \<ge> m" by auto
            from `common_postfix_p xss xs` and  `\<forall> x . \<not> l_c_p_pred xss x` obtain xs' where "common_postfix_p xss xs'" and 1:"\<not> xs >>= xs'" by (auto simp add: l_c_p_pred_def)
            from `common_postfix_p xss xs` and `common_postfix_p xss xs'` have 2:"xs >>= xs' \<or> xs' >>= xs" apply (auto simp add:common_postfix_p_def postfix_def split: split_if_asm) by (metis append_eq_append_conv2)
            from 1 and 2 have "xs' >>= xs" and "xs \<noteq> xs'" by auto
            hence "length xs' > length xs" by (auto simp add:postfix_def)
            with `common_postfix_p xss xs'` and `length xs \<ge> m` show "\<exists> xs . common_postfix_p xss xs \<and> length xs \<ge> Suc m" by auto
          qed
        }
        from this[of "Suc (length xs)"] obtain xs' where "common_postfix_p xss xs'" and "length xs' > length xs" by auto
        with `xs \<in> xss` have False by (auto simp add:common_postfix_p_def postfix_def split:split_if_asm)
      }
      thus ?thesis by auto
    qed
    moreover have "\<forall> x y . l_c_p_pred xss x \<and> l_c_p_pred xss y \<longrightarrow> x = y" by (force simp add:l_c_p_pred_def postfix_def)
    ultimately show ?thesis by auto
  qed
  thus ?thesis by (auto simp add:l_c_p_def intro: theI'[of "l_c_p_pred xss"])
qed

lemma l_c_p_lemma: 
  -- {*A useful lemma*}
  "(ls \<noteq> {} \<and> (\<forall> l \<in> ls . (\<exists> l' . l = l' @ xs))) \<longrightarrow> l_c_p ls >>= xs"
proof %invisible -
  { assume "ls \<noteq> {}" and "\<forall> l \<in> ls . (\<exists> l' . l = l' @ xs)"
    hence "common_postfix_p ls xs" by (auto simp add:common_postfix_p_def postfix_def)
    with l_c_p_ok have "l_c_p ls >>= xs" by (auto simp add: l_c_p_pred_def)
  }
  thus ?thesis by auto
qed

lemma l_c_p_common_postfix: "common_postfix_p xss (l_c_p xss)" 
  using l_c_p_ok[of xss] by (auto simp add:l_c_p_pred_def)

lemma l_c_p_longest: "common_postfix_p xss xs \<longrightarrow> l_c_p xss >>= xs"
  using l_c_p_ok[of xss] by (auto simp add:l_c_p_pred_def)

end