header "Permutation Lemmas"

theory PermutationLemmas = Permutation + Multiset:


  -- "following function is very close to that in multisets- now we can make the connection that x <~~> y iff the multiset of x is the same as that of y"

subsection "perm, count equivalence"

consts count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
primrec 
  "count x [] = 0"
  "count x (y#ys) = (if x=y then 1 else 0) + count x ys"

lemma perm_count: "A <~~> B \<Longrightarrow> (\<forall> x. count x A = count x B)"
  apply(erule perm.induct, auto) done

lemma count_0: "(\<forall>x. count x B = 0) = (B = [])"
  apply(induct B, auto) done

lemma count_Suc: "count a B = Suc m \<Longrightarrow> a : set B"
  apply(induct B, auto) apply(case_tac "a = aa")
  by auto

lemma list_decomp[rule_format]: "v \<in> set p --> (\<exists> xs ys. p = xs@(v#ys) \<and> v \<notin> set xs)"
  apply (induct p, force)
  apply (case_tac "v=a", force, auto)
  apply (rule_tac x="a#xs" in exI, auto)
  done

(*lemmas list_decomp' = list_decomp[simplified set_mem_eq[symmetric]]*)

lemma count_append: "count a (xs@ys) = count a xs + count a ys"
  apply(induct xs, auto) done

lemma count_perm: "!! B. (\<forall> x. count x A = count x B) \<Longrightarrow> A <~~> B"
  apply(induct A)
  apply(simp add: count_0)
proof -
  fix a list B
  assume a: "\<And>B. \<forall>x. count x list = count x B \<Longrightarrow> list <~~> B"
    and b: "\<forall>x. count x (a # list) = count x B"
  from b have "a : set B"
    apply auto
    apply (drule_tac x=a in spec, simp) apply(drule sym) apply(erule count_Suc) done
  from list_decomp[OF this] obtain xs ys where B: "B = xs@a#ys" by force
  let ?B' = "xs@ys"
  from b have "\<forall>x. count x list = count x ?B'"
    apply(simp add: count_append B) done
  from a[OF this] have c: "list <~~> xs@ys" .
  hence "a#list <~~> a#(xs@ys)" by rule
  also have "a#(xs@ys) <~~> xs@a#ys" by(rule perm_append_Cons)
  also (perm.trans) note B[symmetric]
  finally show "a # list <~~> B" .
qed

lemma perm_count_conv: "A <~~> B = (\<forall> x. count x A = count x B)"
  apply(blast intro!: perm_count count_perm) done 


subsection "Properties closed under Perm and Contr hold for x iff hold for remdups x"

  -- "FIXME some stuff may be useful elsewhere, particularly connection between remdups, lists, set and permutations"

lemma length_remdups_leq: "length (remdups x) <= length x"
  apply(induct x, auto) done

lemma length_remdups_eq[rule_format]: "(length (remdups x) = length x) --> remdups x = x"
  apply(induct x, auto) 
  apply(subgoal_tac "length (remdups x) <= length x")
  apply arith
  by(rule length_remdups_leq)

lemma remdups_neq': "! ws. length ws = n --> remdups ws ~= ws --> (? xs ys zs y. ws = xs@[y]@ys@[y]@zs)"
  apply (induct n, simp, rule)
  apply rule
  apply rule
  apply(case_tac ws) apply simp
  apply simp
  apply (case_tac "a : set list", simp)
   apply(frule_tac p=list in list_decomp) apply(elim exE conjE)
   apply(rule_tac x="[]" in exI) apply(rule_tac x=xs in exI) apply(rule_tac x=ys in exI) apply(rule_tac x=a in exI) apply simp
  apply simp
  apply(drule_tac x=list in spec) apply(erule impE) apply simp
  apply(erule impE) apply simp
  apply(erule exE) 
  apply (rule_tac x="a#xs" in exI, simp)
  done
  -- "and its this kind of lemma that really kills automation"

lemma remdups_neq: "remdups ws ~= ws ==> (? xs ys zs y. ws = xs@[y]@ys@[y]@zs)"
  apply(rule remdups_neq'[rule_format]) by auto

lemma remdups_append: "y : set ys --> remdups (ws@y#ys) = remdups (ws@ys)"
  apply (induct ws, simp)
  apply (case_tac "y = a", simp, simp)
  done

lemma perm_contr': assumes perm[rule_format]: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and contr'[rule_format]: "! x xs. P(x#x#xs) = P (x#xs)" 
  shows "! xs. length xs = n --> (P xs = P (remdups xs))"
  apply(induct n rule: nat_less_induct)
proof (safe)
  fix xs :: "'a list"
  assume a[rule_format]: "\<forall>m<length xs. \<forall>ys. length ys = m \<longrightarrow> P ys = P (remdups ys)"
  
  show "P xs = P (remdups xs)"
  proof (cases "remdups xs = xs")
    case True
    thus ?thesis by simp
  next
    case False 
    from remdups_neq[OF this] obtain ws ys zs y where xs: "xs = ws@[y]@ys@[y]@zs" by force
    have "P xs = P (ws@[y]@ys@[y]@zs)" by (simp add: xs)
    also have "... = P ([y,y]@ws@ys@zs)" 
      apply(rule perm) apply(rule iffD2[OF perm_count_conv]) apply rule apply(simp add: count_append) done
    also have "... = P ([y]@ws@ys@zs)" apply simp apply(rule contr') done
    also have "... = P (ws@ys@[y]@zs)" 
      apply(rule perm) apply(rule iffD2[OF perm_count_conv]) apply rule apply(simp add: count_append) done
    also have "... = P (remdups (ws@ys@[y]@zs))"
      apply(rule a) by(auto simp: xs)
    also have "(remdups (ws@ys@[y]@zs)) = (remdups xs)"
      apply(simp add: xs remdups_append) done 
    finally show "P xs = P (remdups xs)" .
  qed
qed

lemma perm_contr: assumes perm: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and contr': "! x xs. P(x#x#xs) = P (x#xs)" 
  shows "(P xs = P (remdups xs))"
  apply(rule perm_contr'[OF perm contr', rule_format]) by force


subsection "List properties closed under Perm, Weak and Contr are monotonic in the set of the list"

constdefs rem :: "'a => 'a list => 'a list"
  "rem x xs == filter (%y. y ~= x) xs"

lemma rem: "x ~: set (rem x xs)"
  apply(simp add: rem_def) done

lemma length_rem: "length (rem x xs) <= length xs"
  apply(simp add: rem_def) done

lemma remdups_nil[iff]: "(remdups x = []) = (x=[])"
  apply(induct x)
  by auto

lemma rem_notin: "x ~: set xs ==> rem x xs = xs"
  apply(simp add: rem_def)
  apply(rule filter_True)
  by force

lemma set_nil[iff]: "(set y = {}) = (y = [])"
  apply(induct y)
  by auto

lemma set_nil'[iff]: "({} = set y) = (y = [])"
  apply(induct y)
  by auto

lemma t: "y <= x ==> y < Suc x" by arith

lemma distinct_remdups_id: "distinct xs ==> remdups xs = xs"
by (induct xs, auto)

lemma remdups_decomp_hd: "remdups x = a#list ==> a ~: set list"
  apply(subgoal_tac "distinct (a#list)")
  apply(case_tac x) apply simp
  apply simp
  apply(drule sym) apply simp
  done

lemma remdups_decomp: "remdups x = x1@[a]@x2 ==> a ~: set x1 & a ~: set x2"
  apply(subgoal_tac "distinct (x1@[a]@x2)")
  apply simp
  apply(drule sym) apply simp
  done
  
lemma remdups_set: "! y. (remdups x <~~> remdups y) --> (set x = set y)"
  apply(rule length_induct[of _ x]) apply (rename_tac x, rule)
  apply (case_tac "remdups x", simp, simp)
  apply rule
  apply(subgoal_tac "a : set (remdups y)")
   apply(drule_tac list_decomp) apply(elim exE conjE)
   apply(drule_tac x="xs@ys" in spec) apply(erule impE) prefer 2
    apply(drule_tac x=list in spec) apply(erule impE) prefer 2
     apply(subgoal_tac "set x = set (remdups x)") apply(simp only:) apply simp apply(drule_tac sym) back back apply simp
      apply(subgoal_tac "set y = set (remdups y)") apply(simp only:) apply simp 
      apply(rule sym) apply(rule set_remdups)
     apply(rule sym) apply (rule set_remdups, simp) -- "FIXME Cons(a,list) <~~> y = list <~~> rem a y"  apply(subgoal_tac "remdups (xs@ys) = (xs@ys) & remdups list = list") 
     apply simp apply(rule_tac z=a in Permutation.cons_perm_imp_perm) apply(rule perm_sym) apply(subgoal_tac "xs @ a # ys <~~> a # xs @ ys")
      apply(rule trans) apply assumption apply assumption
     apply(rule perm_sym, rule perm_append_Cons)
    apply(subgoal_tac "distinct (remdups x) & distinct (remdups y)")
     apply(simp add: distinct_remdups_id)
    apply(blast intro: distinct_remdups)
   apply(subgoal_tac "length (remdups y) = length (remdups x)")
    apply simp
    apply(subgoal_tac "length (remdups x) <= length x")
     apply simp
    apply(rule length_remdups_leq)
   apply(rule perm_length) apply simp apply(rule perm_sym) apply simp
  apply(frule_tac x = a and xs = "a#list" in perm_mem) apply simp apply(simp add: set_mem_eq)
  done

lemma insert_ident: "a ~: X ==> a ~: Y ==> (insert a X = insert a Y) = (X = Y)"
  by force

lemma set_remdups: "! y. (set x = set y) --> (remdups x <~~> remdups y)"
  apply(rule length_induct[of _ x]) apply (rename_tac x, rule)
  apply (case_tac "remdups x", simp, simp)
  apply rule
  apply(subgoal_tac "a : set (remdups y)")
   apply(drule_tac list_decomp) apply(elim exE conjE)
   apply(drule_tac x=list in spec) apply(erule impE) prefer 2
    apply(drule_tac x="xs@ys" in spec) apply(erule impE) prefer 2
     apply simp
     apply(subgoal_tac "a#list <~~> a#xs@ys") 
      apply(rule trans) apply assumption
      apply(rule perm_append_Cons)
     apply(rule Cons)
    apply(subgoal_tac "distinct (a#list) & distinct (xs@a#ys)")
     apply(simp add: distinct_remdups_id)
    apply(drule_tac sym) apply(drule_tac sym) back apply simp
    apply(subgoal_tac "set (a#list) = set (xs@a#ys) & distinct (a#list) & distinct (xs@a#ys)")
     apply(elim conjE) apply simp apply(elim conjE) apply(simp add: insert_ident)
    apply(drule_tac sym) apply(drule_tac sym) back apply simp
   apply(subgoal_tac "length (a#list) <= length x")
    apply force
   apply(drule_tac sym) apply simp apply(rule length_remdups_leq)
  apply(subgoal_tac "set x = set (remdups x)") 
   apply force
  apply(rule sym) apply(rule set_remdups)
  done

lemma remdups_perm_set: "remdups x <~~> remdups y = (set x = set y)"
  using set_remdups remdups_set by blast

lemma perm_weak_filter': assumes perm[rule_format]: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and weak[rule_format]: "! x xs. P xs --> P (x#xs)"
  shows "! ys. P (ys@filter Q xs) --> P (ys@xs)"
  apply (induct xs, simp, rule)
  apply rule
  apply simp
  apply (case_tac "Q a", simp)
   apply(drule_tac x="ys@[a]" in spec) apply simp
  apply simp
  apply(drule_tac x="ys@[a]" in spec) apply simp
  apply(erule impE)
   apply(subgoal_tac "(ys @ a # filter Q xs) <~~> a#ys@filter Q xs")
    apply(simp add: perm)
    apply(rule weak) apply simp
   apply(rule perm_sym) apply(rule perm_append_Cons)
  .

lemma perm_weak_filter: assumes perm: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and weak: "! x xs. P xs --> P (x#xs)"
  shows "P (filter Q xs) ==> P xs"
  using perm_weak_filter'[OF perm weak, rule_format, of "[]", simplified]
  by blast

  -- "right, now in a position to prove that in presence of perm, contr and weak, set x leq set y and x : ded implies y : ded"

lemma perm_weak_contr_mono: 
  assumes perm: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and contr: "! x xs. P (x#x#xs) --> P (x#xs)"
  and weak: "! x xs. P xs --> P (x#xs)"
  and xy: "set x <= set y"
  and Px : "P x"
  shows "P y"
proof -
  from contr weak have contr': "! x xs. P(x#x#xs) = P (x#xs)" by blast

  def y' == "filter (% z. z : set x) y"
  from xy have "set x = set y'" apply(simp add: y'_def) apply blast done
  hence rxry': "remdups x <~~> remdups y'" by(simp add: remdups_perm_set)

  from Px perm_contr[OF perm contr'] have Prx: "P (remdups x)" by simp
  with rxry' have "P (remdups y')" by(simp add: perm)
  
  with perm_contr[OF perm contr'] have "P y'" by simp
  thus "P y" 
    apply(simp add: y'_def)
    apply(rule perm_weak_filter[OF perm weak]) .
qed


subsection "Following used in Soundness"

consts multiset_of_list :: "'a list \<Rightarrow> 'a multiset"
primrec 
  "multiset_of_list [] = {#}"
  "multiset_of_list (x#xs) = {#x#} + multiset_of_list xs"

lemma count_count[symmetric]: "count x A = Multiset.count (multiset_of_list A) x"
by (induct A, simp, simp)

lemma perm_multiset: "A <~~> B = (multiset_of_list A = multiset_of_list B)"
  apply(simp add: perm_count_conv)
  apply(simp add: multiset_eq_conv_count_eq)
  apply(simp add: count_count)
  done

lemma set_of_multiset_of_list: "set_of (multiset_of_list A) = set A"
by (induct A, auto)

lemma perm_set: "A <~~> B \<Longrightarrow> set A = set B"
  apply(simp add: perm_multiset)
  apply(subgoal_tac "set_of (multiset_of_list A) = set_of (multiset_of_list B)")
   apply(thin_tac "multiset_of_list A = multiset_of_list B")
   apply (simp add: set_of_multiset_of_list, simp)
  done


end