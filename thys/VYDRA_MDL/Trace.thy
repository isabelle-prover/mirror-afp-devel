(*<*)
theory Trace
  imports "HOL-Library.Stream" Timestamp
begin
(*>*)

section \<open>Infinite Traces\<close>

inductive sorted_list :: "'a :: order list \<Rightarrow> bool" where
  [intro]: "sorted_list []"
| [intro]: "sorted_list [x]"
| [intro]: "x \<le> y \<Longrightarrow> sorted_list (y # ys) \<Longrightarrow> sorted_list (x # y # ys)"

lemma sorted_list_app: "sorted_list xs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x \<le> y) \<Longrightarrow> sorted_list (xs @ [y])"
  by (induction xs rule: sorted_list.induct) auto

lemma sorted_list_drop: "sorted_list xs \<Longrightarrow> sorted_list (drop n xs)"
proof (induction xs arbitrary: n rule: sorted_list.induct)
  case (2 x n)
  then show ?case
    by (cases n) auto
next
  case (3 x y ys n)
  then show ?case
    by (cases n) auto
qed auto

lemma sorted_list_ConsD: "sorted_list (x # xs) \<Longrightarrow> sorted_list xs"
  by (auto elim: sorted_list.cases)

lemma sorted_list_Cons_nth: "sorted_list (x # xs) \<Longrightarrow> j < length xs \<Longrightarrow> x \<le> xs ! j"
  by (induction "x # xs" arbitrary: x xs j rule: sorted_list.induct)
     (fastforce simp: nth_Cons split: nat.splits)+

lemma sorted_list_atD: "sorted_list xs \<Longrightarrow> i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<le> xs ! j"
proof (induction xs arbitrary: i j rule: sorted_list.induct)
  case (2 x i j)
  then show ?case
    by (cases i) auto
next
  case (3 x y ys i j)
  have "x \<le> (x # y # ys) ! j"
    using 3(5) sorted_list_Cons_nth[OF sorted_list.intros(3)[OF 3(1,2)]]
    by (auto simp: nth_Cons split: nat.splits)
  then show ?case
    using 3
    by (cases i) auto
qed auto

coinductive ssorted :: "'a :: order stream \<Rightarrow> bool" where
  "shd s \<le> shd (stl s) \<Longrightarrow> ssorted (stl s) \<Longrightarrow> ssorted s"

lemma ssorted_siterate[simp]: "(\<And>n. n \<le> f n) \<Longrightarrow> ssorted (siterate f n)"
  by (coinduction arbitrary: n) auto

lemma ssortedD: "ssorted s \<Longrightarrow> s !! i \<le> stl s !! i"
  by (induct i arbitrary: s) (auto elim: ssorted.cases)

lemma ssorted_sdrop: "ssorted s \<Longrightarrow> ssorted (sdrop i s)"
  by (coinduction arbitrary: i s) (auto elim: ssorted.cases ssortedD)

lemma ssorted_monoD: "ssorted s \<Longrightarrow> i \<le> j \<Longrightarrow> s !! i \<le> s !! j"
proof (induct "j - i" arbitrary: j)
  case (Suc x)
  from Suc(1)[of "j - 1"] Suc(2-4) ssortedD[of s "j - 1"]
    show ?case by (cases j) (auto simp: le_Suc_eq Suc_diff_le)
qed simp

lemma sorted_stake: "ssorted s \<Longrightarrow> sorted_list (stake i s)"
proof (induct i arbitrary: s)
  case (Suc i)
  then show ?case
    by (cases i) (auto elim: ssorted.cases)
qed auto

lemma ssorted_monoI: "\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j \<Longrightarrow> ssorted s"
  by (coinduction arbitrary: s)
    (auto dest: spec2[of _ "Suc _" "Suc _"] spec2[of _ 0 "Suc 0"])

lemma ssorted_iff_mono: "ssorted s \<longleftrightarrow> (\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j)"
  using ssorted_monoI ssorted_monoD by metis

typedef (overloaded) ('a, 'b :: timestamp) trace = "{s :: ('a set \<times> 'b) stream.
  ssorted (smap snd s) \<and> (\<forall>x. x \<in> snd ` sset s \<longrightarrow> x \<in> tfin) \<and> (\<forall>i x. x \<in> tfin \<longrightarrow> (\<exists>j. \<not>snd (s !! j) \<le> snd (s !! i) + x))}"
  by (auto simp: \<iota>_mono \<iota>_tfin \<iota>_progressing stream.set_map
      intro!: exI[of _ "smap (\<lambda>n. ({}, \<iota> n)) nats"] ssorted_monoI)

setup_lifting type_definition_trace

lift_definition \<Gamma> :: "('a, 'b :: timestamp) trace \<Rightarrow> nat \<Rightarrow> 'a set" is
  "\<lambda>s i. fst (s !! i)" .
lift_definition \<tau> :: "('a, 'b :: timestamp) trace \<Rightarrow> nat \<Rightarrow> 'b" is
  "\<lambda>s i. snd (s !! i)" .

lemma \<tau>_mono[simp]: "i \<le> j \<Longrightarrow> \<tau> s i \<le> \<tau> s j"
  by transfer (auto simp: ssorted_iff_mono)

lemma \<tau>_fin: "\<tau> \<sigma> i \<in> tfin"
  by transfer auto

lemma ex_lt_\<tau>: "x \<in> tfin \<Longrightarrow> \<exists>j. \<not>\<tau> s j \<le> \<tau> s i + x"
  by transfer auto

lemma le_\<tau>_less: "\<tau> \<sigma> i \<le> \<tau> \<sigma> j \<Longrightarrow> j < i \<Longrightarrow> \<tau> \<sigma> i = \<tau> \<sigma> j"
  by (simp add: antisym)

lemma less_\<tau>D: "\<tau> \<sigma> i < \<tau> \<sigma> j \<Longrightarrow> i < j"
  by (meson \<tau>_mono less_le_not_le not_le_imp_less)

(*<*)
end
(*>*)
