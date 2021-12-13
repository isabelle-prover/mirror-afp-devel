
theory ListLexorder
imports Main
begin

section\<open>Detour: Lexicographic ordering for lists\<close>
text\<open>Simplicial complexes are defined as sets of sets.
To conveniently run computations on them, we convert those sets to lists via @{const sorted_list_of_set}.
This requires providing an arbitrary linear order for lists.
We pick a lexicographic order.\<close>

(* There's probably an easier way to get a sorted list of lists from a set of lists. Some lexicographic ordering does have to exist. No idea... *)

datatype 'a :: linorder linorder_list = LinorderList "'a list"

definition "linorder_list_unwrap L \<equiv> case L of LinorderList L \<Rightarrow> L" (* Meh, there is a way to get datatype to generate this. I forgot *)

fun less_eq_linorder_list_pre where
  "less_eq_linorder_list_pre (LinorderList []) (LinorderList []) = True" |
  "less_eq_linorder_list_pre (LinorderList []) _ = True" |
  "less_eq_linorder_list_pre _ (LinorderList []) = False" |
  "less_eq_linorder_list_pre (LinorderList (a # as)) (LinorderList (b # bs))
    = (if a = b then less_eq_linorder_list_pre (LinorderList as) (LinorderList bs) else a < b)"

instantiation linorder_list :: (linorder) linorder
begin
definition "less_linorder_list x y \<equiv>
              (less_eq_linorder_list_pre x y \<and> \<not> less_eq_linorder_list_pre y x)"
definition "less_eq_linorder_list x y \<equiv> less_eq_linorder_list_pre x y"
instance
proof (standard; unfold less_eq_linorder_list_def less_linorder_list_def)
  fix x y z
  show "less_eq_linorder_list_pre x x"
  proof(induction x)
    case (LinorderList xa)
    then show ?case by(induction xa; simp)
  qed
  show "less_eq_linorder_list_pre x y \<Longrightarrow> less_eq_linorder_list_pre y x \<Longrightarrow> x = y"
    by(induction x y rule: less_eq_linorder_list_pre.induct; simp split: if_splits)
  show "less_eq_linorder_list_pre x y \<or> less_eq_linorder_list_pre y x"
    by(induction x y rule: less_eq_linorder_list_pre.induct; auto)
  show "less_eq_linorder_list_pre x y \<Longrightarrow> less_eq_linorder_list_pre y z \<Longrightarrow> less_eq_linorder_list_pre x z"
  proof(induction x z arbitrary: y rule: less_eq_linorder_list_pre.induct)
    case (3 va vb)
    then show ?case
      using less_eq_linorder_list_pre.elims(2) by blast
  next
    case (4 a1 as b1 bs)
    obtain y1 ys where y: "y = LinorderList (y1 # ys)"
      using "4.prems"(1) less_eq_linorder_list_pre.elims(2) by blast
    then show ?case proof(cases "a1 = b1")
      case True
      have prems: "less_eq_linorder_list_pre (LinorderList as) (LinorderList ys)" "less_eq_linorder_list_pre (LinorderList ys) (LinorderList bs)"
        by (metis "4.prems" True y less_eq_linorder_list_pre.simps(4) not_less_iff_gr_or_eq)+
      note IH = "4.IH"[OF _ this]
      then show ?thesis
        using True by simp

    next
      case False
        then show ?thesis using "4.prems" less_trans y by (simp  split: if_splits)
      qed
  qed simp_all
qed simp

end

text\<open>The main product of this theory file:\<close>
definition "sorted_list_of_list_set L \<equiv>
  map linorder_list_unwrap (sorted_list_of_set (LinorderList ` L))"

lemma set_sorted_list_of_list_set[simp]:
  "finite L \<Longrightarrow> set (sorted_list_of_list_set L) = L"
  by(force simp add: sorted_list_of_list_set_def linorder_list_unwrap_def)

end