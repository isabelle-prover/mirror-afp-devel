theory Kruskal_New_Examples
imports
  Well_Quasi_Orders
  Kruskal_New
begin

lemma (in kruskal) kruskal:
  assumes "wqo_on P F"
  shows "wqo_on (emb P) terms"
  using almost_full_on_terms [of P] and assms by (metis transp_on_emb wqo_on_def)

datatype 'a tree = Node 'a "'a tree list"

fun node
where
  "node (Node f ts) = (f, length ts)"

fun succs
where
  "succs (Node f ts) = ts"

inductive_set trees for A
where
  "f \<in> A \<Longrightarrow> \<forall>t \<in> set ts. t \<in> trees A \<Longrightarrow> Node f ts \<in> trees A"

lemma [simp]:
  "trees UNIV = UNIV"
proof -
  { fix t :: "'a tree" and ts :: "'a tree list"
    have "t \<in> trees UNIV" and "\<forall>s \<in> set ts. s \<in> trees UNIV"
      by (induct t and ts) (auto intro: trees.intros) }
  then show ?thesis by auto
qed

interpretation kruskal_tree: kruskal size "A \<times> UNIV" Node node succs "trees A" for A
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: trees.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_tree.almost_full_on_terms

abbreviation tree_emb where
  "tree_emb P \<equiv> kruskal_tree.emb UNIV (prod_le P (\<lambda>_ _. True))"

lemma wqo_on_trees:
  assumes "wqo_on P UNIV"
  shows "wqo_on (tree_emb P) UNIV"
  using wqo_on_Sigma [OF assms wqo_on_UNIV, THEN kruskal_tree.kruskal] by simp

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

fun root
where
  "root (Fun f ts) = (f, length ts)"

fun args
where
  "args (Fun f ts) = ts"

inductive_set gterms for F
where
  "(f, n) \<in> F \<Longrightarrow> length ts = n \<Longrightarrow> \<forall>s \<in> set ts. s \<in> gterms F \<Longrightarrow> Fun f ts \<in> gterms F"

interpretation kruskal_term: kruskal size F Fun root args "gterms F" for F
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: gterms.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_term.almost_full_on_terms

inductive_set terms
where
  "\<forall>t \<in> set ts. t \<in> terms \<Longrightarrow> Fun f ts \<in> terms"

interpretation kruskal_variadic: kruskal size UNIV Fun root args terms
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: terms.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_variadic.almost_full_on_terms

datatype 'a exp = V 'a | C nat | Plus "'a exp" "'a exp"

datatype 'a symb = v 'a | c nat | p

fun mk
where
  "mk (v x) [] = V x" |
  "mk (c n) [] = C n" |
  "mk p [a, b] = Plus a b"

fun rt
where
  "rt (V x) = (v x, 0)" |
  "rt (C n) = (c n, 0)" |
  "rt (Plus a b) = (p, 2)"

fun ags
where
  "ags (V x) = []" |
  "ags (C n) = []" |
  "ags (Plus a b) = [a, b]"

inductive_set exps
where
  "V x \<in> exps" |
  "C n \<in> exps" |
  "a \<in> exps \<Longrightarrow> b \<in> exps \<Longrightarrow> Plus a b \<in> exps"

lemma [simp]:
  assumes "length ts = 2"
  shows "rt (mk p ts) = (p, 2)"
  using assms by (induct ts) (auto, case_tac ts, auto)

lemma [simp]:
  assumes "length ts = 2"
  shows "ags (mk p ts) = ts"
  using assms by (induct ts) (auto, case_tac ts, auto)

interpretation kruskal_exp: kruskal size
  "{(v x, 0) | x. True} \<union> {(c n, 0) | n. True} \<union> {(p, 2)}"
  mk rt ags exps
apply (unfold_locales)
apply auto
apply (case_tac [!] t rule: exps.cases)
by auto

thm kruskal_exp.almost_full_on_terms

hide_const (open) V C Plus v c p


end

