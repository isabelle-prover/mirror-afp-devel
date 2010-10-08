header "Auxiliary Lemmas for Generic Algorithms on FingerTrees"
theory FTGAAdd
imports Main
begin


lemma distinct_sortet_list_app:
  "\<lbrakk>sorted xs; distinct xs; xs = as @ b # cs\<rbrakk>
  \<Longrightarrow> \<forall> x\<in> set cs. b < x"
  by (metis distinct.simps(2) distinct_append linorder_antisym_conv2 mem_def sorted_Cons sorted_append)

lemma distinct_sorted_list_lem1:
  assumes 
  "sorted xs"
  "sorted ys"
  "distinct xs"
  "distinct ys"
  " \<forall> x \<in> set xs. x < e"
  " \<forall> y \<in> set ys. e < y"
  shows 
  "sorted (xs @ e # ys)"
  "distinct (xs @ e # ys)"
proof -
  from assms (5,6)
  have "\<forall>x\<in>set xs. \<forall>y\<in>set ys. x \<le> y" by force
  thus "sorted (xs @ e # ys)"
    using assms
    by (auto simp add: sorted_append sorted_Cons)
  have "set xs \<inter> set ys = {}" using assms (5,6) by force
  thus "distinct (xs @ e # ys)"
    using assms
    by (auto simp add: distinct_append)
qed

lemma distinct_sorted_list_lem2:
  assumes 
  "sorted xs"
  "sorted ys"
  "distinct xs"
  "distinct ys"
  "e < e'"  
  " \<forall> x \<in> set xs. x < e"
  " \<forall> y \<in> set ys. e' < y"
  shows 
  "sorted (xs @ e # e' # ys)"
  "distinct (xs @ e # e' # ys)"
proof -
  have "sorted (e' # ys)"
    "distinct (e' # ys)"
    "\<forall> y \<in> set (e' # ys). e < y"
    using assms(2,4,5,7)
    by (auto simp add: sorted_Cons)
  thus "sorted (xs @ e # e' # ys)"
  "distinct (xs @ e # e' # ys)"
    using assms(1,3,6) distinct_sorted_list_lem1[of xs "e' # ys" e]  
    by auto
qed

lemma map_of_distinct_upd:
  "x \<notin> set (map fst xs) \<Longrightarrow> [x \<mapsto> y] ++ map_of xs = (map_of xs) (x \<mapsto> y)"
  by (induct xs) (auto simp add: fun_upd_twist)

lemma map_of_distinct_upd2:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ (x,y) # ys) = (map_of (xs @ ys))(x \<mapsto> y)"
  apply(insert assms)
  apply(induct xs)
  apply (auto simp add: expand_fun_eq)
  done

lemma map_of_distinct_upd3:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ (x,y) # ys) = (map_of (xs @ (x,y') # ys))(x \<mapsto> y)"
  apply(insert assms)
  apply(induct xs)
  apply (auto simp add: expand_fun_eq)
  done

lemma map_of_distinct_upd4:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ ys) = (map_of (xs @ (x,y) # ys))(x := None)"
  apply(insert assms)
  apply(induct xs)
  apply (auto simp add: expand_fun_eq)
  apply (auto simp add: map_of_eq_None_iff)
  done

lemma map_of_distinct_lookup:
  assumes "x \<notin> set(map fst xs)"
  "x \<notin> set (map fst ys)"
  shows "map_of (xs @ (x,y) # ys) x = Some y"
proof -
  have "map_of (xs @ (x,y) # ys) = (map_of (xs @ ys)) (x \<mapsto> y)"
    using assms map_of_distinct_upd2 by simp
  thus ?thesis
    by simp
qed

lemma ran_distinct: 
  assumes dist: "distinct (map fst al)" 
  shows "ran (map_of al) = snd ` set al"
using assms proof (induct al)
  case Nil then show ?case by simp
next
  case (Cons kv al)
  then have "ran (map_of al) = snd ` set al" by simp
  moreover from Cons.prems have "map_of al (fst kv) = None"
    by (simp add: map_of_eq_None_iff)
  ultimately show ?case by (simp only: map_of.simps ran_map_upd) simp
qed



end
