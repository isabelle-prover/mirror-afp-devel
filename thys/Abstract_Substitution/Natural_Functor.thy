theory Natural_Functor \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  imports Main
begin

locale natural_functor =
  fixes
    map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" and
    to_set :: "'b \<Rightarrow> 'a set"
  assumes
    map_comp [simp]: "\<And>b f g. map f (map g b) = map (\<lambda>x. f (g x)) b" and
    map_ident [simp]: "\<And>b. map (\<lambda>x. x) b = b" and
    map_cong0 [cong]: "\<And>b f g. (\<And>a. a \<in> to_set b \<Longrightarrow> f a = g a) \<Longrightarrow> map f b = map g b" and
    to_set_map [simp]: "\<And>b f. to_set (map f b) = f ` to_set b" and
    exists_non_empty: "\<exists>b. to_set b \<noteq> {}"
begin

lemma map_id [simp]: "map id b = b"
  unfolding id_def
  using map_ident .

lemma map_cong [cong]: 
  assumes "b = b'" "\<And>a. a \<in> to_set b' \<Longrightarrow> f a = g a" 
  shows "map f b = map g b'"
  using map_cong0 assms
  by blast

lemma map_id_cong [simp]:
  assumes "\<And>a. a \<in> to_set b \<Longrightarrow> f a = a"
  shows "map f b = b"
  using assms
  by simp

lemma to_set_map_not_ident:
  assumes "a \<in> to_set b" "f a \<notin> to_set b"
  shows "map f b \<noteq> b"
  using assms
  by (metis rev_image_eqI to_set_map)

lemma map_in_to_set:
  assumes "map f b = b" "a \<in> to_set b"
  shows "f a \<in> to_set b"
  using assms 
  by (metis image_eqI to_set_map)

lemma exists_functor [intro]: "\<exists>b. a \<in> to_set b"
proof -

  obtain a' b where "a' \<in> to_set b"
    using exists_non_empty
    by blast

  then have "a \<in> to_set (map (\<lambda>_. a) b)"
    by auto
  
  then show ?thesis
    by blast
qed

lemma to_set_const [simp]: "to_set b \<noteq> {} \<Longrightarrow> to_set (map (\<lambda>_. a) b) = {a}"
  by auto

end

locale finite_natural_functor = natural_functor +
  assumes finite_to_set [intro]: "\<And>b. finite (to_set b)"

locale natural_functor_conversion =
  natural_functor +
  functor': natural_functor where map = map' and to_set = to_set'
  for map' :: "('b \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'd" and to_set' :: "'d \<Rightarrow> 'b set" +
  fixes
    map_to :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd" and
    map_from :: "('b \<Rightarrow> 'a) \<Rightarrow> 'd \<Rightarrow> 'c"
  assumes
    to_set_map_from [simp]: "\<And>f d. to_set (map_from f d) = f ` to_set' d" and
    to_set_map_to [simp]: "\<And>f c. to_set' (map_to f c) = f ` to_set c" and
    conversion_map_comp [simp]: "\<And>c f g. map_from f (map_to g c) = map (\<lambda>x. f (g x)) c" and
    conversion_map_comp' [simp]: "\<And>d f g. map_to f (map_from g d) = map' (\<lambda>x. f (g x)) d"

(* TODO: Integration with built-in functor command possible?

ML \<open>fun all_bnfs ctxt =
  ctxt |>
  Proof_Context.theory_of |>
  Theory.defs_of |> 
  Defs.all_specifications_of |>
  map_filter (fn ((kind, name), _) => if kind = Defs.Type then BNF_Def.bnf_of ctxt name else NONE)\<close>

declare [[ML_print_depth=100]]
ML \<open>all_bnfs @{context} |> map BNF_Def.T_of_bnf\<close>
 *)

end
