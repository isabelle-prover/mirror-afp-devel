section \<open>Filtermap for Lazy Lists\<close>

theory List_Filtermap
  imports Main
begin

text \<open> This theory defines the filtermap operator for lazy lists, proves its basic properties, 
and proves coinductive criteria for the equqlity of two filtermapped lazy lsits. \<close>


subsection \<open> Preliminaries \<close>

(* Hiding the "filtermap" constant, which is the mapping operator for filters. *)
hide_const filtermap

(* Preliminaries *)

abbreviation never :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where "never U \<equiv> list_all (\<lambda> a. \<not> U a)"

lemma never_list_ex: "never pred xs \<longleftrightarrow> \<not> list_ex pred xs"
by (induction xs) auto


(* Right-Cons: *)

abbreviation Rcons (infix \<open>##\<close> 70) where "xs ## x \<equiv> xs @ [x]"

lemma two_singl_Rcons: "[a,b] = [a] ## b" by auto

lemma length_gt_1_Cons_snoc:
  assumes "length ys > 1"
  obtains x1 xs x2 where "ys = x1 # xs ## x2"
using assms
proof (cases ys)
  case (Cons x1 xs)
    with assms obtain xs' x2 where "xs = xs' ## x2" by (cases xs rule: rev_cases) auto
    with Cons show thesis by (intro that) auto
qed auto 

lemma right_cons_left[simp]: "i < length as \<Longrightarrow> (as ## a)!i = as!i"
by (metis butlast_snoc nth_butlast)+


subsection \<open> Filtermap \<close>

definition filtermap :: "('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a list" where 
"filtermap pred func xs \<equiv> map func (filter pred xs)"

lemma filtermap_Nil[simp]: 
"filtermap pred func [] = []"
unfolding filtermap_def by auto

lemma filtermap_Cons_not[simp]: 
"\<not> pred x \<Longrightarrow> filtermap pred func (x # xs) = filtermap pred func xs"
unfolding filtermap_def by auto

lemma filtermap_Cons[simp]: 
"pred x \<Longrightarrow> filtermap pred func (x # xs) = func x # filtermap pred func xs"
unfolding filtermap_def by auto

lemma filtermap_append: "filtermap pred func (xs @ xs1) = filtermap pred func xs @ filtermap pred func xs1"
proof(induction xs arbitrary: xs1)
  case (Cons x xs)
  thus ?case by (cases "pred x") auto
qed auto

lemma filtermap_Nil_list_ex: "filtermap pred func xs = [] \<longleftrightarrow> \<not> list_ex pred xs"
proof(induction xs)
  case (Cons x xs)
  thus ?case by (cases "pred x") auto
qed auto

lemma filtermap_Nil_never: "filtermap pred func xs = [] \<longleftrightarrow> never pred xs"
proof(induction xs)
  case (Cons x xs)
  thus ?case by (cases "pred x") auto
qed auto

lemma length_filtermap: "length (filtermap pred func xs) \<le> length xs"
proof(induction xs)
  case (Cons x xs)
  thus ?case by (cases "pred x") auto
qed auto

lemma filtermap_list_all[simp]: "filtermap pred func xs = map func xs \<longleftrightarrow> list_all pred xs"
proof(induction xs)
  case (Cons x xs)
  thus ?case apply (cases "pred x")
  by (simp_all) (metis impossible_Cons length_filtermap length_map)
qed auto

lemma filtermap_eq_Cons:
assumes "filtermap pred func xs = a # al1"
shows "\<exists> x xs2 xs1.
   xs = xs2 @ [x] @ xs1 \<and> never pred xs2 \<and> pred x \<and> func x = a \<and> filtermap pred func xs1 = al1"
using assms proof(induction xs arbitrary: a al1)
  case (Cons x xs a al1)
  show ?case
  proof(cases "pred x")
    case False
    hence "filtermap pred func xs = a # al1" using Cons by simp
    from Cons(1)[OF this] obtain xn xs2 xs1 where
    1: "xs = xs2 @ [xn] @ xs1 \<and> never pred xs2 \<and> pred xn \<and> func xn = a \<and>
     filtermap pred func xs1 = al1" by blast
    show ?thesis apply(rule exI[of _ xn], rule exI[of _ "x # xs2"], rule exI[of _ xs1])
    using Cons(2) 1 False by simp
  next
    case True
    hence "filtermap pred func xs = al1" using Cons by simp
    show ?thesis apply(rule exI[of _ x], rule exI[of _ "[]"], rule exI[of _ xs])
    using Cons(2) True by simp
  qed
qed auto

lemma filtermap_eq_append:
assumes "filtermap pred func xs = al1 @ al2"
shows "\<exists> xs1 xs2. xs = xs1 @ xs2 \<and> filtermap pred func xs1 = al1 \<and> filtermap pred func xs2 = al2"
using assms proof(induction al1 arbitrary: xs)
  case Nil show ?case
  apply (rule exI[of _ "[]"], rule exI[of _ xs]) using Nil by auto
next
  case (Cons a al1 xs)
  hence "filtermap pred func xs = a # (al1 @ al2)" by simp
  from filtermap_eq_Cons[OF this] obtain x xs2 xs1
  where xs: "xs = xs2 @ [x] @ xs1" and n: "never pred xs2 \<and> pred x \<and> func x = a"
  and f: "filtermap pred func xs1 = al1 @ al2" by blast
  from Cons(1)[OF f] obtain xs11 xs22 where xs1: "xs1 = xs11 @ xs22"
  and f1: "filtermap pred func xs11 = al1" and f2: "filtermap pred func xs22 = al2" by blast
  show ?case apply (rule exI[of _ "xs2 @ [x] @ xs11"], rule exI[of _ xs22])
  using n filtermap_Nil_never f1 f2 unfolding xs xs1 filtermap_append by auto
qed

lemma holds_filtermap_RCons[simp]:
"pred x \<Longrightarrow> filtermap pred func (xs ## x) = filtermap pred func xs ## func x"
proof(induction xs)
  case (Cons x xs)
  thus ?case by (cases "pred x") auto
qed auto

lemma not_holds_filtermap_RCons[simp]:
"\<not> pred x \<Longrightarrow> filtermap pred func (xs ## x) = filtermap pred func xs"
proof(induction xs)
  case (Cons x xs)
  thus ?case by (cases "pred x") auto
qed auto

lemma filtermap_eq_RCons:
assumes "filtermap pred func xs = al1 ## a"
shows "\<exists> x xs1 xs2.
   xs = xs1 @ [x] @ xs2 \<and> never pred xs2 \<and> pred x \<and> func x = a \<and> filtermap pred func xs1 = al1"
using assms proof(induction xs arbitrary: a al1 rule: rev_induct)
  case (snoc x xs a al1)
  show ?case
  proof(cases "pred x")
    case False
    hence "filtermap pred func xs = al1 ## a" using snoc by simp
    from snoc(1)[OF this] obtain xn xs2 xs1 where
    1: "xs = xs1 @ [xn] @ xs2 \<and> never pred xs2 \<and> pred xn \<and> func xn = a \<and>
     filtermap pred func xs1 = al1" by blast
    show ?thesis apply(rule exI[of _ xn], rule exI[of _ xs1], rule exI[of _ "xs2 ## x"])
    using snoc(2) 1 False by simp
  next
    case True
    hence "filtermap pred func xs = al1" using snoc by simp
    show ?thesis apply(rule exI[of _ x], rule exI[of _ xs], rule exI[of _ "[]"])
    using snoc(2) True by simp
  qed
qed auto

lemma filtermap_eq_Cons_RCons:
assumes "filtermap pred func xs = a # al1 ## b"
shows "\<exists> xsa xa xs1 xb xsb.
   xs = xsa @ [xa] @ xs1 @ [xb] @ xsb \<and>
   never pred xsa \<and>
   pred xa \<and> func xa = a \<and>
   filtermap pred func xs1 = al1 \<and>
   pred xb \<and> func xb = b \<and>
   never pred xsb"
proof-
  from filtermap_eq_Cons[OF assms] obtain xa xsa xs2
  where 0: "xs = xsa @ [xa] @ xs2 \<and> never pred xsa \<and> pred xa \<and> func xa = a"
  and 1: "filtermap pred func xs2 = al1 ## b" by auto
  from filtermap_eq_RCons[OF 1] obtain xb xs1 xsb where
  2: "xs2 = xs1 @ [xb] @ xsb \<and> never pred xsb \<and>
  pred xb \<and> func xb = b \<and> filtermap pred func xs1 = al1" by blast
  show ?thesis apply(rule exI[of _ xsa], rule exI[of _ xa], rule exI[of _ xs1],
    rule exI[of _ xb], rule exI[of _ xsb])
  using 2 0 by auto
qed

lemma filter_Nil_never: "[] = filter pred xs \<Longrightarrow> never pred xs"
by (induction xs) (auto split: if_splits)

lemma never_Nil_filter: "never pred xs \<longleftrightarrow> [] = filter pred xs"
by (induction xs) (auto split: if_splits)

lemma set_filtermap:
"set (filtermap pred func xs) \<subseteq> {func x | x . x \<in> set xs \<and> pred x}"
proof(induction xs)
  case (Cons x xs)
  thus ?case by (cases "pred x") auto
qed auto 


end 