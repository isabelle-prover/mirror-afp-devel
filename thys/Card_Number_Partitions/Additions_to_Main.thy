(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* Additions to Isabelle's Main Theories *}

theory Additions_to_Main
imports Main
begin

subsection {* Addition to Finite-Set Theory *}

lemma bound_domain_and_range_impl_finitely_many_functions:
  "finite {f::nat\<Rightarrow>nat. (\<forall>i. f i \<le> n) \<and> (\<forall>i\<ge>m. f i = 0)}"
proof (induct m)
  case 0
  have eq: "{f. (\<forall>i. f i \<le> n) \<and> (\<forall>i. f i = 0)} = {(\<lambda>_. 0)}" by auto
  from this show ?case by auto (subst eq; auto)
next
  case (Suc m)
  let ?S = "(\<lambda>(y, f). f(m := y)) ` ({0..n} \<times> {f. (\<forall>i. f i \<le> n) \<and> (\<forall>i\<ge>m. f i = 0)})"
  {
    fix g
    assume "\<forall>i. g i \<le> n" "\<forall>i\<ge>Suc m. g i = 0"
    from this have "g \<in> ?S"
      by (auto intro: image_eqI[where x="(g m, g(m:=0))"])
  }
  from this have "{f. (\<forall>i. f i \<le> n) \<and> (\<forall>i\<ge>Suc m. f i = 0)} = ?S" by auto
  from this Suc show ?case by simp
qed

subsection {* Additions to Groups-Big Theory *}

lemma setsum_card_image:
  assumes "finite A"
  assumes "\<forall>s\<in>A. \<forall>t\<in>A. s \<noteq> t \<longrightarrow> (f s) \<inter> (f t) = {}"
  shows "setsum card (f ` A) = setsum (\<lambda>a. card (f a)) A"
using assms
proof (induct A)
  case empty
  from this show ?case by simp
next
  case (insert a A)
  show ?case
  proof cases
    assume "f a = {}"
    from this insert show ?case
      by (subst setsum.mono_neutral_right[where S="f ` A"]) auto
  next
    assume "f a \<noteq> {}"
    from this have "setsum card (insert (f a) (f ` A)) = card (f a) + setsum card (f ` A)"
      using insert by (subst setsum.insert) auto
    from this insert show ?case by simp
  qed
qed

lemma card_Union_image:
  assumes "finite S"
  assumes "\<forall>s\<in>f ` S. finite s"
  assumes "\<forall>s\<in>S. \<forall>t\<in>S. s \<noteq> t \<longrightarrow> (f s) \<inter> (f t) = {}"
  shows "card (\<Union>(f ` S)) = setsum (\<lambda>x. card (f x)) S"
proof -
  have "\<forall>A\<in>f ` S. \<forall>B\<in>f ` S. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    using assms(3) by (metis image_iff)
  from this have "card (\<Union>(f ` S)) = setsum card (f ` S)"
    using assms(1, 2) by (subst card_Union_disjoint) auto
  also have "... = setsum (\<lambda>x. card (f x)) S"
    using assms(1, 3) by (auto simp add: setsum_card_image)
  finally show ?thesis .
qed

subsection {* Addition to Set-Interval Theory *}

lemma setsum_atMost_remove_nat:
  assumes "k \<le> (n :: nat)"
  shows "(\<Sum>i\<le>n. f i) = f k + (\<Sum>i\<in>{..n}-{k}. f i)"
using assms by (auto simp add: setsum.remove[where x=k])

end
