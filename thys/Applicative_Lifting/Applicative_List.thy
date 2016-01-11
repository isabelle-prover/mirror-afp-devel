(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Lists\<close>

theory Applicative_List imports
  Applicative
  "~~/src/Tools/Adhoc_Overloading"
begin

definition "ap_list fs xs = List.bind fs (\<lambda>f. List.bind xs (\<lambda>x. [f x]))"

adhoc_overloading Applicative.ap ap_list

lemma Nil_ap[simp]: "ap_list [] xs = []"
unfolding ap_list_def by simp

lemma ap_Nil[simp]: "ap_list fs [] = []"
unfolding ap_list_def by (induction fs) simp_all

context begin interpretation applicative_syntax .

lemma cons_ap_list: "(f # fs) \<diamondop> xs = map f xs @ fs \<diamondop> xs"
unfolding ap_list_def by (induction xs) simp_all

lemma append_ap_distrib: "(fs @ gs) \<diamondop> xs = fs \<diamondop> xs @ gs \<diamondop> xs"
unfolding ap_list_def by (induction fs) simp_all

applicative list
for
  pure: "\<lambda>x. [x]"
  ap: ap_list
proof -
  fix x :: "'a list"
  show "[\<lambda>x. x] \<diamondop> x = x" unfolding ap_list_def by (induction x) simp_all
next
  fix g :: "('c \<Rightarrow> 'b) list" and f :: "('a \<Rightarrow> 'c) list" and x
  let ?B = "\<lambda>g f x. g (f x)"
  show "[?B] \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
  proof (induction g)
    case Nil show ?case by simp
  next
    case (Cons g gs)
    have g_comp: "[?B g] \<diamondop> f \<diamondop> x = [g] \<diamondop> (f \<diamondop> x)"
    proof (induction f)
      case Nil show ?case by simp
    next
      case (Cons f fs)
      have "[?B g] \<diamondop> (f # fs) \<diamondop> x = [g] \<diamondop> ([f] \<diamondop> x) @ [?B g] \<diamondop> fs \<diamondop> x"
        by (simp add: cons_ap_list)
      also have "... = [g] \<diamondop> ([f] \<diamondop> x) @ [g] \<diamondop> (fs \<diamondop> x)" using Cons.IH ..
      also have "... = [g] \<diamondop> ((f # fs) \<diamondop> x)" by (simp add: cons_ap_list)
      finally show ?case .
    qed
    have "[?B] \<diamondop> (g # gs) \<diamondop> f \<diamondop> x = [?B g] \<diamondop> f \<diamondop> x @ [?B] \<diamondop> gs \<diamondop> f \<diamondop> x"
      by (simp add: cons_ap_list append_ap_distrib)
    also have "... = [g] \<diamondop> (f \<diamondop> x) @ gs \<diamondop> (f \<diamondop> x)" using g_comp Cons.IH by simp
    also have "... = (g # gs) \<diamondop> (f \<diamondop> x)" by (simp add: cons_ap_list)
    finally show ?case .
  qed
next
  fix f :: "('a \<Rightarrow> 'b) list" and x
  show "f \<diamondop> [x] = [\<lambda>f. f x] \<diamondop> f" unfolding ap_list_def by simp
qed (simp add: cons_ap_list)

end

end