section \<open>Powerset\<close>
theory Powerset
  imports
    Main
    n_Sequences
    Common_Lemmas
    Filter_Bool_List
begin

subsection"Definition"

text "Pow A"
text "Cardinality: \<open>2 ^ card A\<close>"
text "Example: \<open>Pow {0,1} = {{}, {1}, {0}, {0, 1}}\<close>"

subsection"Algorithm"

fun all_bool_lists :: "nat \<Rightarrow> bool list list" where
  "all_bool_lists 0 = [[]]"
| "all_bool_lists (Suc x) = concat [[False#xs, True#xs] . xs \<leftarrow> all_bool_lists x]"

fun powerset_enum where
  "powerset_enum xs = [(filter_bool_list x xs) . x \<leftarrow> all_bool_lists (length xs)]"

subsection"Verification"

text "First we show the relevant theorems for \<open>all_bool_lists\<close>, then we'll transfer the
results to the enumeration algorithm for powersets."

lemma distinct_concat_aux: "distinct xs \<Longrightarrow> distinct (concat (map (\<lambda>xs. [False # xs, True # xs]) xs))"
  by (induct xs) auto

lemma distinct_all_bool_lists : "distinct (all_bool_lists x)"
  by (induct x) (auto simp add: distinct_concat_aux)

lemma all_bool_lists_correct: "set (all_bool_lists x) = {xs. length xs = x}"
proof(standard)
  show "set (all_bool_lists x) \<subseteq> {xs. length xs = x}"
    by (induct x) auto
next
  show "{xs. length xs = x} \<subseteq> set (all_bool_lists x)"
  proof(induct x)
    case 0
    then show ?case by simp
  next
    case (Suc x)
    have "length ys = Suc x \<Longrightarrow> \<exists>xs. ys = False # xs \<or> ys = True # xs" for ys
      by (metis (full_types) Suc_length_conv)
    then show ?case using Suc
      by fastforce
  qed
qed

subsubsection"Correctness"

theorem powerset_enum_correct: "set (map set (powerset_enum xs)) = Pow (set xs)"
proof(standard)
  show "set (map set (powerset_enum xs)) \<subseteq> Pow (set xs)"
    using filter_bool_list_not_elem by fastforce
next
  have "\<And>x. x \<subseteq> set xs \<Longrightarrow> x \<in> (\<lambda>x. set (filter_bool_list x xs)) ` {zs. length zs = length xs}"
    unfolding image_def using filter_bool_list_exist_length image_def by auto
  then show "Pow (set xs) \<subseteq> set (map set (powerset_enum xs))"
    using all_bool_lists_correct by auto
qed
  
subsubsection"Distinctness"

theorem powerset_enum_distinct_elem: "distinct xs \<Longrightarrow> ys \<in> set (powerset_enum xs) \<Longrightarrow> distinct ys"
  using filter_bool_list_distinct by auto 

theorem powerset_enum_distinct: "distinct xs \<Longrightarrow> distinct (powerset_enum xs)"
proof -
  assume dis: "distinct xs"
  then have " distinct (map (\<lambda>x. filter_bool_list x xs) (all_bool_lists (length xs)))"
    using distinct_map filter_bool_list_inj distinct_all_bool_lists
    by (metis all_bool_lists_correct)
  then show ?thesis
    using dis by simp
qed

subsubsection"Cardinality"

text "Cardinality for powersets is already shown in @{thm [source] card_Pow}."

subsection"Alternative algorithm with \<open>n_sequence_enum\<close>"

fun all_bool_lists2 :: "nat \<Rightarrow> bool list list" where
  "all_bool_lists2 n = n_sequence_enum [True, False] n"

lemma all_bool_lists2_distinct: "distinct (all_bool_lists2 n)"
  by (auto simp add: n_sequence_enum_distinct)

lemma all_bool_lists2_correct: "set (all_bool_lists n) = set (all_bool_lists2 n)"
  by (auto simp: all_bool_lists_correct n_sequence_enum_correct n_sequences_def)

end
