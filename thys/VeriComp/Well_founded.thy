section \<open>Well-foundedness of Relations Defined as Predicate Functions\<close>

theory Well_founded
  imports Main
begin

subsection \<open>Lexicographic product\<close>

context
  fixes
    r1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    r2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

definition lex_prodp :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "lex_prodp x y \<equiv> r1 (fst x) (fst y) \<or> fst x = fst y \<and> r2 (snd x) (snd y)"

lemma lex_prodp_lex_prod:
  shows "lex_prodp x y \<longleftrightarrow> (x, y) \<in> lex_prod { (x, y). r1 x y } { (x, y). r2 x y }"
  by (auto simp: lex_prod_def lex_prodp_def)

lemma lex_prodp_wfP:
  assumes
    "wfp r1" and
    "wfp r2"
  shows "wfp lex_prodp"
proof (rule wfpUNIVI)
  show "\<And>P. \<forall>x. (\<forall>y. lex_prodp y x \<longrightarrow> P y) \<longrightarrow> P x \<Longrightarrow> (\<And>x. P x)"
  proof -
    fix P
    assume "\<forall>x. (\<forall>y. lex_prodp y x \<longrightarrow> P y) \<longrightarrow> P x"
    hence hyps: "(\<And>y1 y2. lex_prodp (y1, y2) (x1, x2) \<Longrightarrow> P (y1, y2)) \<Longrightarrow> P (x1, x2)" for x1 x2
      by fast
    show "(\<And>x. P x)"
      apply (simp only: split_paired_all)
      apply (atomize (full))
      apply (rule allI)
      apply (rule wfp_induct_rule[OF assms(1), of "\<lambda>y. \<forall>b. P (y, b)"])
      apply (rule allI)
      apply (rule wfp_induct_rule[OF assms(2), of "\<lambda>b. P (x, b)" for x])
      using hyps[unfolded lex_prodp_def, simplified]
      by blast
  qed
qed

end

subsection \<open>Lexicographic list\<close>

context
  fixes order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

inductive lexp :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  lexp_head: "order x y \<Longrightarrow> length xs = length ys \<Longrightarrow> lexp (x # xs) (y # ys)" |
  lexp_tail: "lexp xs ys \<Longrightarrow> lexp (x # xs) (x # ys)"

end

lemma lexp_prepend: "lexp order ys zs \<Longrightarrow> lexp order (xs @ ys) (xs @ zs)"
  by (induction xs) (simp_all add: lexp_tail)

lemma lexp_lex: "lexp order xs ys \<longleftrightarrow> (xs, ys) \<in> lex {(x, y). order x y}"
proof
  assume "lexp order xs ys"
  thus "(xs, ys) \<in> lex {(x, y). order x y}"
    by (induction xs ys rule: lexp.induct) simp_all
next
  assume "(xs, ys) \<in> lex {(x, y). order x y}"
  thus "lexp order xs ys"
    by (auto intro!: lexp_prepend intro: lexp_head simp: lex_conv)
qed

lemma lex_list_wfP: "wfP order \<Longrightarrow> wfP (lexp order)"
  by (simp add: lexp_lex wf_lex wfp_def)

end
