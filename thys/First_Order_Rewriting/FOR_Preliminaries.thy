section\<open>Preliminaries\<close>
text\<open>This theory contains some auxiliary results previously located in Auxx.Util of IsaFoR.\<close>
theory FOR_Preliminaries
  imports
    Polynomial_Factorization.Missing_List 
    First_Order_Terms.Fun_More2
begin

lemma finite_imp_eq [simp]:
  "finite {x. P x \<longrightarrow> Q x} \<longleftrightarrow> finite {x. \<not> P x} \<and> finite {x. Q x}"
  by (auto simp: Collect_imp_eq Collect_neg_eq)

definition const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
  "const \<equiv> (\<lambda>x y. x)"

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)" where
  "flip f \<equiv> (\<lambda>x y. f y x)"
declare flip_def[simp]

lemma const_apply[simp]: "const x y = x"
  by (simp add: const_def)

lemma foldr_Cons_append_conv [simp]:
  "foldr (#) xs ys = xs @ ys"
  by (induct xs) simp_all

lemma foldl_flip_Cons[simp]:
  "foldl (flip (#)) xs ys = rev ys @ xs"
  by (induct ys arbitrary: xs) simp_all

text \<open>already present as @{thm [source] foldr_conv_foldl}, but
  direction seems odd\<close>
lemma foldr_flip_rev[simp]:
  "foldr (flip f) (rev xs) a = foldl f a xs"
  by (simp add: foldr_conv_foldl)

text \<open>already present as @{thm [source] foldl_conv_foldr}, but
  direction seems odd\<close>
lemma foldl_flip_rev[simp]:
  "foldl (flip f) a (rev xs) = foldr f xs a"
  by (simp add: foldl_conv_foldr)

fun debug :: "(String.literal \<Rightarrow> String.literal) \<Rightarrow> String.literal \<Rightarrow> 'a \<Rightarrow> 'a" where "debug i t x = x"


end
