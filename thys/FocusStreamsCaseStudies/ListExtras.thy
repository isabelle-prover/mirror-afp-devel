(*<*)
(*
   Title:  Theory ListExtras.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)

header {* Auxiliary Theory ListExtras.thy*}

theory ListExtras 
imports Main
begin

definition
  disjoint :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
 "disjoint x y \<equiv>  (set x) \<inter> (set y) = {}"

primrec
  mem ::  "'a \<Rightarrow> 'a list \<Rightarrow> bool" (infixr "mem" 65)
where
  "x mem [] = False" |
  "x mem (y # l) = ((x = y) \<or> (x mem l))"

definition
  memS ::  "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
 "memS x l  \<equiv>  x \<in> (set l)"


lemma mem_memS_eq:  "x mem l \<equiv> memS x l"
proof (induct l)
  case Nil
  from this show ?case
  by (simp add: memS_def)
next
    fix a la case (Cons a la)
    from Cons show ?case
    by (simp add: memS_def)
 qed


lemma mem_set_1:
  assumes h1:"a mem l"
  shows "a \<in> set l"
using assms
proof (induct l)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed


lemma mem_set_2:
  assumes h1:"a \<in> set l"
  shows "a mem l"
using assms
proof (induct l)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed


lemma set_inter_mem: 
  assumes h1:"x mem l1"
      and h2:"x mem l2"
  shows "set l1 \<inter> set l2 \<noteq> {}"
using assms
proof (induct l1)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by (auto, simp add: mem_set_1)
 qed


lemma mem_notdisjoint: 
  assumes h1:"x mem l1"
      and h2:"x mem l2"
  shows "\<not> disjoint l1 l2"
proof 
  assume sg0:"disjoint l1 l2"
  from h1 and h2 have  sg1:"set l1 \<inter> set l2 \<noteq> {}"
    by (simp add: set_inter_mem)
  from h1 and h2 and sg1 and sg0 show "False"
   by (simp add: disjoint_def)
qed


lemma mem_notdisjoint2:
  assumes h1:"disjoint (schedule A) (schedule B)"
      and h2:"x mem schedule A"
  shows "\<not> x mem schedule B"
proof - 
  { assume a1:" x mem schedule B"
    from h2 and a1 have sg1:"\<not>  disjoint (schedule A) (schedule B)" 
      by (simp add: mem_notdisjoint)
    from h1 and sg1 have "False" by simp
   } from this have sg2:"\<not> x mem schedule B" by blast
  from this show ?thesis by simp
qed


lemma Add_Less: 
  assumes "0 < b"
  shows "(Suc a - b < Suc a) = True"
using assms by arith


lemma list_length_hint1: 
  assumes "l ~= []"
  shows "0 < length l" 
using assms by simp


lemma list_length_hint1a: 
  assumes "l ~= []"
  shows "0 < length l" 
using assms by simp


lemma list_length_hint2: 
  assumes h1:"length x  = Suc 0"
  shows "[hd x] = x"
using assms 
proof (induct x)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed


lemma list_length_hint2a: 
  assumes h1:"length l = Suc 0"
  shows "tl l = []"
using assms
proof (induct l)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed


lemma list_length_hint3: 
  assumes "length l = Suc 0"
  shows "l \<noteq> []"
using assms
proof (induct l)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed


lemma list_length_hint4: 
  assumes h1:"length x \<le> Suc 0"
      and h2:"x \<noteq> []"
   shows "length x = Suc 0"
using assms
proof (induct x)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed


lemma length_nonempty: 
  assumes h1:"x \<noteq> []" 
  shows "Suc 0 \<le> length x"
using assms
proof (induct x)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed 

lemma last_nth_length: 
  assumes "x \<noteq> []"
  shows "x ! ((length x) - Suc 0) = last x"
using assms
proof (induct x)
  case Nil
  from this show ?case
  by auto
next
  fix a la case (Cons a la)
  from Cons show ?case
  by auto
qed 


lemma list_nth_append0:
  assumes h1:"i < length x"
  shows "x ! i = (x @ z) ! i"
proof (cases i)
  assume "i=0" 
  with h1  show ?thesis by (simp add: nth_append)
next
  fix ii assume "i = Suc ii"
  with h1  show ?thesis  by (simp add: nth_append)
qed


lemma list_nth_append1:
  assumes h1:"i < length x"
  shows "(b # x) ! i = (b # x @ y) ! i"
proof -
  from h1 have sg1:"i < length (b # x)" by auto
  from this have sg2: "(b # x) ! i = ((b # x) @ y) ! i" 
    by (rule list_nth_append0)
  from this show ?thesis by simp
qed
  

lemma list_nth_append2:
  assumes h1:"i < Suc (length x)"
  shows "(b # x) ! i = (b # x @ a # y) ! i"
proof - 
  from h1 have sg1:"i < length (b # x)" by auto
  from this have sg2: "(b # x) ! i = ((b # x) @ (a # y)) ! i"
    by (rule list_nth_append0)
  from this show ?thesis by simp
qed


lemma list_nth_append3:
  assumes h1:"\<not> i < Suc (length x)"
      and h2:"i - Suc (length x) < Suc (length y)"
  shows "(a # y) ! (i - Suc (length x)) = (b # x @ a # y) ! i"
proof (cases i)
  assume "i=0" 
  with h1  show ?thesis by (simp add: nth_append)
next
  fix ii assume "i = Suc ii"
  with h1  show ?thesis  by (simp add: nth_append)
qed


lemma list_nth_append4:
  assumes h1:"i < Suc (length x + length y)"
      and h2:"\<not> i - Suc (length x) < Suc (length y)" 
  shows "False"
using assms  by arith


lemma list_nth_append5:
  assumes h1:"i - length x < Suc (length y)" 
      and h2:"\<not> i - Suc (length x) < Suc (length y)"
  shows "\<not>  i < Suc (length x + length y)"
using assms  by arith


lemma list_nth_append6:
  assumes h1:"\<not> i - length x < Suc (length y)"
      and h2:"\<not> i - Suc (length x) < Suc (length y)"
  shows "\<not> i < Suc (length x + length y)"
using assms by arith


lemma list_nth_append6a:
  assumes h1:"i < Suc (length x + length y)"
      and h2:"\<not> i - length x < Suc (length y)"
  shows "False"
using assms by arith 


lemma list_nth_append7:
  assumes h1:"i - length x < Suc (length y)"
      and h2:"i - Suc (length x) < Suc (length y)"
  shows "i < Suc (Suc (length x + length y))"
using assms  by arith


lemma list_nth_append8:
  assumes h1:"\<not> i < Suc (length x + length y)"
      and h2:"i < Suc (Suc (length x + length y))"
  shows "i = Suc (length x + length y)"
using assms  by arith


lemma list_nth_append9:
  assumes h1:"i - Suc (length x) < Suc (length y)"
  shows "i < Suc (Suc (length x + length y))"
using assms by arith
  

lemma list_nth_append10:
  assumes h1:"\<not> i < Suc (length x)"
      and h2:"\<not> i - Suc (length x) < Suc (length y)"
  shows "\<not> i < Suc (Suc (length x + length y))"
using assms by arith

end