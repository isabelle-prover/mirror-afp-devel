(*<*)
theory Filtermap
  imports Trivia
begin
(*>*)

section \<open>Preliminaries\<close>

function filtermap ::
"('trans \<Rightarrow> bool) \<Rightarrow> ('trans \<Rightarrow> 'a) \<Rightarrow> 'trans list \<Rightarrow> 'a list"
where
"filtermap pred func [] = []"
|
"\<not> pred trn \<Longrightarrow> filtermap pred func (trn # tr) = filtermap pred func tr"
|
"pred trn \<Longrightarrow> filtermap pred func (trn # tr) = func trn # filtermap pred func tr"
by auto (metis list.exhaust)
termination by lexicographic_order

lemma filtermap_map_filter: "filtermap pred func xs = map func (filter pred xs)"
by (induction xs) auto

lemma filtermap_append: "filtermap pred func (tr @ tr1) = filtermap pred func tr @ filtermap pred func tr1"
proof(induction tr arbitrary: tr1)
  case (Cons trn tr)
  thus ?case by (cases "pred trn") auto
qed auto

lemma filtermap_Nil_list_ex: "filtermap pred func tr = [] \<longleftrightarrow> \<not> list_ex pred tr"
proof(induction tr)
  case (Cons trn tr)
  thus ?case by (cases "pred trn") auto
qed auto

lemma filtermap_Nil_never: "filtermap pred func tr = [] \<longleftrightarrow> never pred tr"
proof(induction tr)
  case (Cons trn tr)
  thus ?case by (cases "pred trn") auto
qed auto

lemma length_filtermap: "length (filtermap pred func tr) \<le> length tr"
proof(induction tr)
  case (Cons trn tr)
  thus ?case by (cases "pred trn") auto
qed auto

lemma filtermap_list_all[simp]: "filtermap pred func tr = map func tr \<longleftrightarrow> list_all pred tr"
proof(induction tr)
  case (Cons trn tr)
  thus ?case apply (cases "pred trn")
  by (simp_all) (metis impossible_Cons length_filtermap length_map)
qed auto

lemma filtermap_eq_Cons:
assumes "filtermap pred func tr = a # al1"
shows "\<exists> trn tr2 tr1.
   tr = tr2 @ [trn] @ tr1 \<and> never pred tr2 \<and> pred trn \<and> func trn = a \<and> filtermap pred func tr1 = al1"
using assms proof(induction tr arbitrary: a al1)
  case (Cons trn tr a al1)
  show ?case
  proof(cases "pred trn")
    case False
    hence "filtermap pred func tr = a # al1" using Cons by simp
    from Cons(1)[OF this] obtain trnn tr2 tr1 where
    1: "tr = tr2 @ [trnn] @ tr1 \<and> never pred tr2 \<and> pred trnn \<and> func trnn = a \<and>
     filtermap pred func tr1 = al1" by blast
    show ?thesis apply(rule exI[of _ trnn], rule exI[of _ "trn # tr2"], rule exI[of _ tr1])
    using Cons(2) 1 False by simp
  next
    case True
    hence "filtermap pred func tr = al1" using Cons by simp
    show ?thesis apply(rule exI[of _ trn], rule exI[of _ "[]"], rule exI[of _ tr])
    using Cons(2) True by simp
  qed
qed auto

lemma filtermap_eq_append:
assumes "filtermap pred func tr = al1 @ al2"
shows "\<exists> tr1 tr2. tr = tr1 @ tr2 \<and> filtermap pred func tr1 = al1 \<and> filtermap pred func tr2 = al2"
using assms proof(induction al1 arbitrary: tr)
  case Nil show ?case
  apply (rule exI[of _ "[]"], rule exI[of _ tr]) using Nil by auto
next
  case (Cons a al1 tr)
  hence "filtermap pred func tr = a # (al1 @ al2)" by simp
  from filtermap_eq_Cons[OF this] obtain trn tr2 tr1
  where tr: "tr = tr2 @ [trn] @ tr1" and n: "never pred tr2 \<and> pred trn \<and> func trn = a"
  and f: "filtermap pred func tr1 = al1 @ al2" by blast
  from Cons(1)[OF f] obtain tr11 tr22 where tr1: "tr1 = tr11 @ tr22"
  and f1: "filtermap pred func tr11 = al1" and f2: "filtermap pred func tr22 = al2" by blast
  show ?case apply (rule exI[of _ "tr2 @ [trn] @ tr11"], rule exI[of _ tr22])
  using n filtermap_Nil_never f1 f2 unfolding tr tr1 filtermap_append by auto
qed

lemma holds_filtermap_RCons[simp]:
"pred trn \<Longrightarrow> filtermap pred func (tr ## trn) = filtermap pred func tr ## func trn"
proof(induction tr)
  case (Cons trn1 tr)
  thus ?case by (cases "pred trn1") auto
qed auto

lemma not_holds_filtermap_RCons[simp]:
"\<not> pred trn \<Longrightarrow> filtermap pred func (tr ## trn) = filtermap pred func tr"
proof(induction tr)
  case (Cons trn1 tr)
  thus ?case by (cases "pred trn1") auto
qed auto

lemma filtermap_eq_RCons:
assumes "filtermap pred func tr = al1 ## a"
shows "\<exists> trn tr1 tr2.
   tr = tr1 @ [trn] @ tr2 \<and> never pred tr2 \<and> pred trn \<and> func trn = a \<and> filtermap pred func tr1 = al1"
using assms proof(induction tr arbitrary: a al1 rule: rev_induct)
  case (snoc trn tr a al1)
  show ?case
  proof(cases "pred trn")
    case False
    hence "filtermap pred func tr = al1 ## a" using snoc by simp
    from snoc(1)[OF this] obtain trnn tr2 tr1 where
    1: "tr = tr1 @ [trnn] @ tr2 \<and> never pred tr2 \<and> pred trnn \<and> func trnn = a \<and>
     filtermap pred func tr1 = al1" by blast
    show ?thesis apply(rule exI[of _ trnn], rule exI[of _ tr1], rule exI[of _ "tr2 ## trn"])
    using snoc(2) 1 False by simp
  next
    case True
    hence "filtermap pred func tr = al1" using snoc by simp
    show ?thesis apply(rule exI[of _ trn], rule exI[of _ tr], rule exI[of _ "[]"])
    using snoc(2) True by simp
  qed
qed auto

lemma filtermap_eq_Cons_RCons:
assumes "filtermap pred func tr = a # al1 ## b"
shows "\<exists> tra trna tr1 trnb trb.
   tr = tra @ [trna] @ tr1 @ [trnb] @ trb \<and>
   never pred tra \<and>
   pred trna \<and> func trna = a \<and>
   filtermap pred func tr1 = al1 \<and>
   pred trnb \<and> func trnb = b \<and>
   never pred trb"
proof-
  from filtermap_eq_Cons[OF assms] obtain trna tra tr2
  where 0: "tr = tra @ [trna] @ tr2 \<and> never pred tra \<and> pred trna \<and> func trna = a"
  and 1: "filtermap pred func tr2 = al1 ## b" by auto
  from filtermap_eq_RCons[OF 1] obtain trnb tr1 trb where
  2: "tr2 = tr1 @ [trnb] @ trb \<and> never pred trb \<and>
  pred trnb \<and> func trnb = b \<and> filtermap pred func tr1 = al1" by blast
  show ?thesis apply(rule exI[of _ tra], rule exI[of _ trna], rule exI[of _ tr1],
    rule exI[of _ trnb], rule exI[of _ trb])
  using 2 0 by auto
qed

lemma filter_Nil_never: "[] = filter pred xs \<Longrightarrow> never pred xs"
by (induction xs) (auto split: if_splits)

lemma never_Nil_filter: "never pred xs \<longleftrightarrow> [] = filter pred xs"
by (induction xs) (auto split: if_splits)

lemma snoc_eq_filterD:
  assumes "xs ## x = filter Q ys"
  obtains us vs where "ys = us @ x # vs" and "never Q vs" and "Q x" and "xs = filter Q us"
using assms proof (induction ys rule: rev_induct)
  case Nil then show ?case by auto
next
  case (snoc y ys)
    show ?case
    proof (cases)
      assume "Q y"
      moreover then have "x = y" using snoc.prems by auto
      ultimately show thesis using snoc(3) snoc(2) by auto
    next
      assume "\<not>Q y"
      show thesis
      proof (rule snoc.IH)
        show "xs ## x = filter Q ys" using \<open>\<not>Q y\<close> snoc(3) by auto
      next
        fix us vs
        assume "ys = us @ x # vs" and "never Q vs" and "Q x" and "xs = filter Q us"
        then show thesis using \<open>\<not>Q y\<close> snoc(2) by auto
      qed
    qed
qed

lemma filtermap_Cons2_eq:
     "filtermap pred func [x, x'] = filtermap pred func [y, y']
  \<Longrightarrow> filtermap pred func (x # x' # zs) = filtermap pred func (y # y' # zs)"
unfolding filtermap_append[of pred func "[x, x']" "zs", simplified]
          filtermap_append[of pred func "[y, y']" "zs", simplified]
by simp

lemma filtermap_Cons_cong:
   "filtermap pred func xs = filtermap pred func ys
\<Longrightarrow> filtermap pred func (x # xs) = filtermap pred func (x # ys)"
by (cases "pred x") auto

lemma set_filtermap:
"set (filtermap pred func xs) \<subseteq> {func x | x . x \<in>\<in> xs \<and> pred x}"
by (induct xs, simp) (case_tac "pred a", auto)

(*<*)
end
(*>*)
