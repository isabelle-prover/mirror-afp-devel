subsection \<open>An Implementation of Linear Polynomials as Ordered Association Lists\<close>

theory Linear_Polynomial_Impl
  imports 
    "HOL-Library.AList" 
    Linear_Polynomial    
begin

typedef (overloaded) ('a :: zero,'v :: linorder) lpoly_impl =
    "{ (c :: 'a, vcs :: ('v \<times> 'a) list). 
        sorted (map fst vcs) \<and> 
        distinct (map fst vcs) \<and> 
        Ball (snd ` set vcs) ((\<noteq>) 0)}" 
  by (intro exI[of _ "(0,[])"], auto)

setup_lifting type_definition_lpoly_impl

definition lookup_0 :: "('a \<times> 'b :: zero)list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "lookup_0 xs x = (case map_of xs x of None \<Rightarrow> 0 | Some y \<Rightarrow> y)" 

lemma lookup_0_empty[simp]: "lookup_0 [] = (\<lambda> x. 0)" 
  by (intro ext, auto simp: lookup_0_def)

lemma lookup_0_single[simp]: "lookup_0 [(x,c)] = (\<lambda> y. 0)(x := c)" 
  by (intro ext, auto simp: lookup_0_def)

lemma finite_lookup_0[simp, intro]: "finite {x . lookup_0 xs x \<noteq> 0}" 
  unfolding lookup_0_def 
  by (rule finite_subset[OF _ finite_set, of _ "map fst xs"],
    force split: option.splits dest!: map_of_SomeD) 
  

lift_definition lpoly_of :: "('a :: zero, 'v :: linorder) lpoly_impl \<Rightarrow> ('a,'v)lpoly" is
  "\<lambda> (c, vcs) cx. case cx of None \<Rightarrow> c | Some x \<Rightarrow> lookup_0 vcs x"  
  apply clarsimp
  subgoal for c vcs 
    apply (rule finite_subset[of _ "insert None (Some ` {x. lookup_0 vcs x \<noteq> 0})"])
    subgoal apply (clarsimp split: option.splits) 
      subgoal for x by (cases x, auto)
      done
    subgoal by simp
    done
  done

code_datatype lpoly_of
  
lift_definition zero_lpoly_impl :: "('a :: zero, 'v :: linorder) lpoly_impl" is 
    "(0,[])" by auto

lemma zero_lpoly_impl[code]: "0 = lpoly_of zero_lpoly_impl" 
  by (transfer, auto split: option.splits)

lift_definition const_lpoly_impl :: "'a \<Rightarrow> ('a :: zero, 'v :: linorder) lpoly_impl" is 
    "\<lambda> c. (c,[])" by auto

lemma const_lpoly_impl[code]: "const_l c = lpoly_of (const_lpoly_impl c)" 
  by (transfer, auto split: option.splits)

lift_definition constant_lpoly_impl :: "('a :: zero, 'v :: linorder) lpoly_impl \<Rightarrow> 'a" is fst .

lemma constant_lpoly_impl[code]: "constant_l (lpoly_of p) = constant_lpoly_impl p"
  by (transfer, auto)

lift_definition var_lpoly_impl :: "'v :: linorder \<Rightarrow> ('a :: {comm_monoid_mult,zero_neq_one}, 'v) lpoly_impl" is
  "\<lambda> x. (0, [(x,1)])" by auto

lemma var_lpoly_impl[code]: "var_l x = lpoly_of (var_lpoly_impl x)" 
  by transfer (auto split: option.splits)

lift_definition uminus_lpoly_impl :: "('a :: ab_group_add, 'v :: linorder) lpoly_impl \<Rightarrow> ('a,'v) lpoly_impl" is
  "\<lambda> (c, vcs). (uminus c, map (map_prod id uminus) vcs)" 
  by force

lemma uminus_lpoly_impl[code]: "- lpoly_of p = lpoly_of (uminus_lpoly_impl p)" 
  by transfer (force split: option.split simp: map_of_eq_None_iff lookup_0_def eq_key_imp_eq_value)

fun merge_coeffs_main :: "('a :: zero \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('v :: linorder \<times> 'a) list \<Rightarrow> ('v \<times> 'a)list \<Rightarrow> ('v \<times> 'a)list" where
  "merge_coeffs_main f ((x,c) # xs) ((y,d) # ys) = (
     if x = y then (x,f c d) # merge_coeffs_main f xs ys
     else if x < y then (x,f c 0) # merge_coeffs_main f xs ((y,d) # ys)
     else (y,f 0 d) # merge_coeffs_main f ((x,c) # xs) ys)" 
| "merge_coeffs_main f [] ys = map (map_prod id (f 0)) ys" 
| "merge_coeffs_main f xs [] = map (map_prod id (\<lambda> x. f x 0)) xs" 

lemma merge_coeffs_main: assumes "sorted (map fst vxs)" "distinct (map fst vxs)" 
  "sorted (map fst vys)" "distinct (map fst vys)"
  and "f 0 0 = 0" 
shows "sorted (map fst (merge_coeffs_main f vxs vys)) 
  \<and> distinct (map fst (merge_coeffs_main f vxs vys))
  \<and> fst ` set (merge_coeffs_main f vxs vys) = fst ` set vxs \<union> fst ` set vys
  \<and> lookup_0 (merge_coeffs_main f vxs vys) x = f (lookup_0 vxs x) (lookup_0 vys x)"
  using assms
proof (induction f vxs vys rule: merge_coeffs_main.induct)
  case (1 f x c xs y d ys)
  let ?lhs = "merge_coeffs_main f ((x, c) # xs) ((y, d) # ys)" 
  consider (eq) "x = y" | (lt) "x \<noteq> y" "x < y" | (gt) "x \<noteq> y" "\<not> x < y" by linarith
  thus ?case 
  proof cases
    case eq
    from eq "1.prems" have "sorted (map fst xs)" "distinct (map fst xs)"
      "sorted (map fst ys)" "distinct (map fst ys)" "f 0 0 = 0" by auto
    note IH = "1.IH"(1)[OF eq this]  
    from eq have res: "?lhs = (x, f c d) # merge_coeffs_main f xs ys" by auto
    from eq "1.prems" IH show ?thesis unfolding res using IH
      apply (intro conjI)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (force simp: lookup_0_def map_of_eq_None_iff split: option.split dest: eq_key_imp_eq_value)
      done
  next
    case lt
    from lt "1.prems" have "sorted (map fst xs)" "distinct (map fst xs)"
      "sorted (map fst ((y, d) # ys))" "distinct (map fst ((y, d) # ys))" "f 0 0 = 0" by auto
    note IH = "1.IH"(2)[OF lt this]  
    from lt have res: "?lhs = (x, f c 0) # merge_coeffs_main f xs ((y, d) # ys)" by auto
    from lt "1.prems" IH show ?thesis unfolding res using IH
      apply (intro conjI)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (force simp: lookup_0_def map_of_eq_None_iff split: option.split dest: eq_key_imp_eq_value)
      done
  next
    case gt
    from gt "1.prems" have "sorted (map fst ((x, c) # xs))" "distinct (map fst ((x, c) # xs))"
      "sorted (map fst ys)" "distinct (map fst ys)" "f 0 0 = 0" by auto
    note IH = "1.IH"(3)[OF gt this]  
    from gt have res: "?lhs = (y, f 0 d) # merge_coeffs_main f ((x, c) # xs) ys" by auto
    from gt "1.prems" IH show ?thesis unfolding res using IH
      apply (intro conjI)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (force simp: lookup_0_def map_of_eq_None_iff split: option.split dest: eq_key_imp_eq_value)
      done
  qed
next
  case (2 f ys)
  then show ?case 
    apply (intro conjI)
    subgoal by force
    subgoal by force
    subgoal by force
    by (force simp: map_of_eq_None_iff lookup_0_def  split: option.split dest: eq_key_imp_eq_value)
next
  case (3 f v va)
  then show ?case 
    apply (intro conjI)
    subgoal by force
    subgoal by force
    subgoal by force
    by (force simp: map_of_eq_None_iff lookup_0_def  split: option.split dest: eq_key_imp_eq_value)
qed

definition filter_0 where "filter_0 = filter (\<lambda> p. snd p \<noteq> 0)" 

lemma filter_0: assumes "distinct (map fst xs)" "sorted (map fst xs)" 
  shows "lookup_0 (filter_0 xs) = lookup_0 xs" 
    "distinct (map fst (filter_0 xs))"
    "sorted (map fst (filter_0 xs))" 
    "Ball (snd ` set (filter_0 xs)) ((\<noteq>) 0)" 
  subgoal 
    apply (intro ext)
    apply (clarsimp simp: lookup_0_def filter_0_def split: option.split)
    apply (intro conjI impI allI)
    subgoal for x 
      by (smt (verit, ccfv_SIG) eq_snd_iff map_of_SomeD mem_Collect_eq not_None_eq set_filter weak_map_of_SomeI)
    subgoal for x y by (force dest: map_of_SomeD simp: map_of_eq_None_iff)  
    subgoal for x y z using assms 
      by (metis (no_types, lifting) eq_key_imp_eq_value map_of_SomeD mem_Collect_eq set_filter)
    done
  subgoal using assms(1) unfolding filter_0_def by (rule distinct_map_filter)
  subgoal using assms(2) unfolding filter_0_def by (rule sorted_filter)
  subgoal unfolding filter_0_def by auto
  done

definition merge_coeffs :: "('a :: zero \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('v :: linorder \<times> 'a) list \<Rightarrow> ('v \<times> 'a)list \<Rightarrow> ('v \<times> 'a)list" where
  "merge_coeffs f xs ys = filter_0 (merge_coeffs_main f xs ys)" 

lemma merge_coeffs: assumes "sorted (map fst vxs)" "distinct (map fst vxs)" 
  "sorted (map fst vys)" "distinct (map fst vys)"
  and "f 0 0 = 0" 
shows "sorted (map fst (merge_coeffs f vxs vys))" (is ?A)
    "distinct (map fst (merge_coeffs f vxs vys))" (is ?B)
   "Ball (snd ` set (merge_coeffs f vxs vys)) ((\<noteq>) 0)" (is ?C)
   "lookup_0 (merge_coeffs f vxs vys) x = f (lookup_0 vxs x) (lookup_0 vys x)" (is ?D)
proof -
  let ?m = "merge_coeffs_main f vxs vys" 
  from merge_coeffs_main[OF assms(1-4), of f, OF assms(5)]
  have "distinct (map fst ?m)" "sorted (map fst ?m)" "lookup_0 ?m x = f (lookup_0 vxs x) (lookup_0 vys x)"
    by auto
  from filter_0[OF this(1-2)] this(3)
  show ?A ?B ?C ?D
    unfolding merge_coeffs_def[symmetric] by auto
qed

lift_definition minus_lpoly_impl :: "('a :: ab_group_add, 'v :: linorder) lpoly_impl \<Rightarrow> ('a,'v) lpoly_impl \<Rightarrow> ('a,'v) lpoly_impl" is
  "\<lambda> (c, vxs) (d, vys). (c - d, merge_coeffs minus vxs vys)" 
  apply clarsimp
  subgoal for vxs vys
    using merge_coeffs[of vxs vys minus] by auto
  done

lemma minus_lpoly_impl[code]: "lpoly_of p - lpoly_of q = lpoly_of (minus_lpoly_impl p q)" 
  apply transfer
  apply clarsimp
  apply (intro ext)
  subgoal for a vxs b vys x
    using merge_coeffs[of vxs vys minus]
    by (cases x, auto)
  done
 
lift_definition plus_lpoly_impl :: "('a :: ab_group_add, 'v :: linorder) lpoly_impl \<Rightarrow> ('a,'v) lpoly_impl \<Rightarrow> ('a,'v) lpoly_impl" is
  "\<lambda> (c, vxs) (d, vys). (c + d, merge_coeffs plus vxs vys)" 
  apply clarsimp
  subgoal for vxs vys
    using merge_coeffs[of vxs vys plus] by auto
  done

lemma plus_lpoly_impl[code]: "lpoly_of p + lpoly_of q = lpoly_of (plus_lpoly_impl p q)" 
  apply transfer
  apply clarsimp
  apply (intro ext)
  subgoal for a vxs b vys x
    using merge_coeffs[of vxs vys plus]
    by (cases x, auto)
  done

lift_definition map_lpoly_impl :: "('a :: zero \<Rightarrow> 'a) \<Rightarrow> ('a,'v :: linorder)lpoly_impl \<Rightarrow> ('a,'v)lpoly_impl" is
  "\<lambda> f (c,vcs). (f c, filter_0 (map (map_prod id f) vcs))" 
  by clarsimp (intro conjI filter_0, auto simp: filter_0_def)

lemma map_lpoly_impl: "f 0 = 0 \<Longrightarrow> fun_of_lpoly (lpoly_of (map_lpoly_impl f p)) = (\<lambda> x. f (fun_of_lpoly (lpoly_of p) x))" 
  apply (intro ext)
  apply transfer
  apply clarsimp
  subgoal for x f c vcs
    apply (cases x)
    subgoal by simp
    subgoal for y
      apply (simp add: filter_0)
      by (force simp: lookup_0_def map_of_eq_None_iff dest: eq_key_imp_eq_value split: option.split)
    done
  done

definition "sdiv_lpoly_impl p x = map_lpoly_impl (\<lambda> y. y div x) p" 

lemma sdiv_lpoly_impl[code]: "sdiv_l (lpoly_of p) x = lpoly_of (sdiv_lpoly_impl p x)" 
  apply (intro lpoly_fun_of_eqI)
  apply (unfold sdiv_lpoly_impl_def, subst map_lpoly_impl, force)
  by transfer auto

definition "smult_lpoly_impl x p = map_lpoly_impl ((*) x) p" 

lemma smult_lpoly_impl[code]: "smult_l x (lpoly_of p) = lpoly_of (smult_lpoly_impl x p)" 
  apply (intro lpoly_fun_of_eqI)
  apply (unfold smult_lpoly_impl_def, subst map_lpoly_impl, force)
  by transfer auto

instantiation lpoly :: (type,type)equal begin 
definition equal_lpoly :: "('a, 'b) lpoly \<Rightarrow> ('a, 'b) lpoly \<Rightarrow> bool" where "equal_lpoly = (=)" 
instance
  by (intro_classes, auto simp: equal_lpoly_def)
end

instantiation lpoly_impl :: (zero,linorder)equal begin
lift_definition equal_lpoly_impl :: "('a, 'b) lpoly_impl \<Rightarrow> ('a, 'b) lpoly_impl \<Rightarrow> bool" 
  is "\<lambda> (c,xs) (d,ys). c = d \<and> xs = ys" .
instance
  by (intro_classes, transfer, auto)
end

lift_definition vars_coeffs_impl :: "('a :: zero, 'v :: linorder) lpoly_impl \<Rightarrow> ('v \<times> 'a) list" is snd .

lemma vars_coeffs_impl: 
  "set (vars_coeffs_impl p) = (\<lambda> v. (v, coeff_l (lpoly_of p) v)) ` vars_l (lpoly_of p)" (is ?A)
  "distinct (map fst (vars_coeffs_impl p))" (is ?B)
  "sorted (map fst (vars_coeffs_impl p))" (is ?C)
  "vars_l_list (lpoly_of p) = map fst (vars_coeffs_impl p)" (is ?D) 
  "vars_coeffs_impl p = map (\<lambda> v. (v, coeff_l (lpoly_of p) v)) (vars_l_list (lpoly_of p))" (is ?E) 
proof -
  show ?A ?B ?C
  proof (atomize(full), transfer, goal_cases)
    case (1 p)
    define vcs where "vcs = snd p" 
    with 1 have sort: "sorted (map fst vcs)" and
      dist: "distinct (map fst vcs)" and
      non0: "\<forall>y\<in>set vcs. snd y \<noteq> 0" by auto
    let ?set = "(\<lambda>x. (x, lookup_0 vcs x)) ` {x. lookup_0 vcs x \<noteq> 0}" 
    {
      fix x c
      {
        assume x: "(x,c) \<in> set vcs" 
        with non0 have c: "c \<noteq> 0" by auto
        with dist x have "lookup_0 vcs x = c" unfolding lookup_0_def by simp
        hence "(x,c) \<in> ?set" using c by auto
      }
      moreover
      {
        assume "(x,c) \<in> ?set" 
        hence look: "lookup_0 vcs x = c" and c: "c \<noteq> 0" by auto
        hence "(x,c) \<in> set vcs" unfolding lookup_0_def 
          by (cases "map_of vcs x"; force dest: map_of_SomeD)
      }
      ultimately have "(x,c) \<in> set vcs \<longleftrightarrow> (x,c) \<in> ?set" by auto
    }
    with 1 show ?case unfolding vcs_def by auto
  qed
  show ?D unfolding vars_l_list_def using \<open>?A\<close> \<open>?B\<close> \<open>?C\<close>
    by (metis (no_types, lifting) fst_eqD image_set list.map_comp list.map_ident_strong o_def sorted_distinct_set_unique sorted_list_of_set.distinct_sorted_key_list_of_set sorted_list_of_set.sorted_sorted_key_list_of_set vars_l_list vars_l_list_def)
  show ?E using \<open>?A\<close> \<open>?B\<close> \<open>?C\<close> \<open>?D\<close>
    by (smt (verit, ccfv_SIG) fst_conv image_iff list.map_comp list.map_ident_strong o_def)
qed

declare vars_coeffs_impl(4)[code]

declare eval_l_def[code del]

lemma eval_lpoly_impl[code]: "eval_l \<alpha> (lpoly_of p) = 
  constant_lpoly_impl p + (\<Sum>(x, c) \<leftarrow> vars_coeffs_impl p. c * \<alpha> x)" 
  unfolding eval_l_def constant_lpoly_impl 
  unfolding vars_coeffs_impl(5)
  unfolding vars_l_list[symmetric]
  apply (subst sum.distinct_set_conv_list)
  subgoal unfolding vars_l_list_def by simp
  subgoal unfolding map_map o_def split ..
  done

declare substitute_all_l_def[code del]

lemma substitute_all_impl[code]: "substitute_all_l \<sigma> (lpoly_of p) = 
  const_l (constant_lpoly_impl p) + (\<Sum>(x, c) \<leftarrow> vars_coeffs_impl p. smult_l c (\<sigma> x))" 
  unfolding substitute_all_l_def constant_lpoly_impl 
  unfolding vars_coeffs_impl(5)
  unfolding vars_l_list[symmetric]
  apply (subst sum.distinct_set_conv_list)
  subgoal unfolding vars_l_list_def by simp
  subgoal unfolding map_map o_def split ..
  done

lemma equal_lpoly_impl[code]: "HOL.equal (lpoly_of p) (lpoly_of q) = (p = q)"
proof (unfold equal_lpoly_def, standard)
  assume *: "lpoly_of p = lpoly_of q" 
  hence "vars_coeffs_impl p = vars_coeffs_impl q" 
    unfolding vars_coeffs_impl(5) by simp
  moreover from * have "constant_l (lpoly_of p) = constant_l (lpoly_of q)" by simp
  from this[unfolded constant_lpoly_impl] 
  have "constant_lpoly_impl p = constant_lpoly_impl q" .
  ultimately show "p = q" by transfer auto
qed auto

fun update_main :: "'v :: linorder \<Rightarrow> 'a :: zero \<Rightarrow> ('v \<times> 'a) list \<Rightarrow> ('v \<times> 'a) list" where
  "update_main x a ((y,b) # zs) = (if x > y then (y,b) # update_main x a zs
      else if x = y then (y, a) # zs else (x,a) # (y, b) # zs)"
| "update_main x a [] = [(x,a)]" 

lemma update_main: assumes "sorted (map fst vcs)" "distinct (map fst vcs)" "Ball (snd ` set vcs) ((\<noteq>) 0)" 
  and "vcs' = update_main x a vcs" 
  and a: "a \<noteq> 0" 
shows "sorted (map fst vcs')" "distinct (map fst vcs')" "Ball (snd ` set vcs') ((\<noteq>) 0)" 
  "fst ` set vcs' = insert x (fst ` set vcs)" 
  "lookup_0 vcs' z = ((lookup_0 vcs)(x := a)) z" 
  using assms(1-4)
proof (atomize(full), induct vcs arbitrary: vcs')
  case Nil
  thus ?case using a by auto
next
  case (Cons p vcs vcs1)
  obtain y b where p: "p = (y,b)" by force
  note Cons = Cons[unfolded p list.simps fst_conv]
  consider (gt) "x > y" | (lt) "x < y" | (eq) "x = y" by fastforce
  thus ?case 
  proof cases
    case gt
    define vcs2 where "vcs2 = update_main x a vcs" 
    from gt Cons have vcs1: "vcs1 = (y, b) # vcs2" unfolding vcs2_def by auto
    from Cons(2-) have *: 
      "sorted (map fst vcs)" 
      "distinct (map fst vcs)" 
      "\<forall>y\<in>snd ` set vcs. 0 \<noteq> y" by auto
    from Cons(1)[OF * vcs2_def] Cons(2-4) a gt
    show ?thesis unfolding p vcs1 by (auto simp: lookup_0_def)
  next
    case lt
    with Cons have vcs1: "vcs1 = (x,a) # (y,b) # vcs" by auto 
    from Cons(2-4) a lt
    show ?thesis unfolding p vcs1 by (auto simp: lookup_0_def)
  next
    case eq
    with Cons have vcs1: "vcs1 = (x,a) # vcs" by auto 
    from Cons(2-4) a eq
    show ?thesis unfolding p vcs1 by (auto simp: lookup_0_def)
  qed
qed

fun update_main_0 :: "'v :: linorder \<Rightarrow> ('v \<times> 'a) list \<Rightarrow> ('v \<times> 'a) list" where
  "update_main_0 x ((y,b) # zs) = (if x > y then (y,b) # update_main_0 x zs
      else if x = y then zs else (y, b) # zs)"
| "update_main_0 x [] = []" 
  
lemma update_main_0: assumes "sorted (map fst vcs)" "distinct (map fst vcs)" "Ball (snd ` set vcs) ((\<noteq>) 0)" 
  and "vcs' = update_main_0 x vcs" 
shows "sorted (map fst vcs')" "distinct (map fst vcs')" "Ball (snd ` set vcs') ((\<noteq>) 0)" 
  "fst ` set vcs' = fst ` set vcs - {x}" 
  "lookup_0 vcs' z = ((lookup_0 vcs)(x := 0)) z" 
  using assms(1-4)
proof (atomize(full), induct vcs arbitrary: vcs')
  case Nil
  hence vcs': "vcs' = []" by auto
  show ?case unfolding vcs' by auto
next
  case (Cons p vcs vcs1)
  obtain y b where p: "p = (y,b)" by force
  note Cons = Cons[unfolded p list.simps fst_conv]
  consider (gt) "x > y" | (lt) "x < y" | (eq) "x = y" by fastforce
  thus ?case 
  proof cases
    case gt
    define vcs2 where "vcs2 = update_main_0 x vcs" 
    from gt Cons have vcs1: "vcs1 = (y, b) # vcs2" unfolding vcs2_def by auto
    from Cons(2-) have *: 
      "sorted (map fst vcs)" 
      "distinct (map fst vcs)" 
      "\<forall>y\<in>snd ` set vcs. 0 \<noteq> y" by auto
    from Cons(1)[OF * vcs2_def] Cons(2-4) gt
    show ?thesis unfolding p vcs1 by (auto simp: lookup_0_def)
  next
    case lt
    with Cons have vcs1: "vcs1 = (y,b) # vcs" by auto 
    from Cons(2-4) lt
    show ?thesis unfolding p vcs1 by (auto simp: lookup_0_def split: option.split)
  next
    case eq
    with Cons have vcs1: "vcs1 = vcs" by auto 
    from Cons(2-4) eq
    show ?thesis unfolding p vcs1 by (force simp: lookup_0_def split: option.split)
  qed
qed
  

lift_definition update_lpoly_impl :: "'v :: linorder \<Rightarrow> 'a :: zero \<Rightarrow> ('a,'v)lpoly_impl \<Rightarrow> ('a,'v)lpoly_impl" is
  "\<lambda> x a (c, vs). if a = 0 then (c, update_main_0 x vs) else (c, update_main x a vs)" 
  apply clarsimp
  subgoal for x a c vs d vcs
  proof goal_cases
    case 1
    show ?case
    proof (cases "a = 0")
      case True
      hence vcs: "vcs = update_main_0 x vs" and c: "c = d" using 1 by auto
      from update_main_0[OF 1(2) 1(3) _ vcs] 1(4)
      show ?thesis using c by auto
    next
      case False
      hence vcs: "vcs = update_main x a vs" and c: "c = d" using 1 by auto
      from update_main[OF 1(2) 1(3) _ vcs False] 1(4)
      show ?thesis using c by auto
    qed
  qed
  done
  
lemma update_lpoly_impl: "fun_of_lpoly (lpoly_of (update_lpoly_impl x a p)) = (fun_of_lpoly (lpoly_of p))(Some x := a)" 
  apply (transfer, clarsimp, intro conjI ext impI)
  subgoal for x a z vs p
    using update_main_0(5)[of vs _ x, OF _ _ _ refl]
    by (cases p, auto)
  subgoal for x a z vs p
    using update_main(5)[of vs _ x a, OF _ _ _ refl]
    by (cases p, auto)
  done

lift_definition coeff_lpoly_impl :: "('a :: zero, 'v :: linorder)lpoly_impl \<Rightarrow> 'v \<Rightarrow> 'a" is
  "\<lambda> (c,p) x. lookup_0 p x" .

lemma coeff_lpoly_impl[code]: "coeff_l (lpoly_of p) x = coeff_lpoly_impl p x" 
  by (transfer, auto)

definition substitute_l_impl where
  "substitute_l_impl x p q = (let c = coeff_lpoly_impl q x in 
        plus_lpoly_impl (update_lpoly_impl x 0 q) (smult_lpoly_impl c p))" 

lemma substitute_l_impl[code]: 
  "substitute_l x (lpoly_of p) (lpoly_of q) = lpoly_of (substitute_l_impl x p q)" 
  unfolding substitute_l_impl_def Let_def 
  unfolding plus_lpoly_impl[symmetric] smult_lpoly_impl[symmetric] coeff_lpoly_impl[symmetric]
proof (intro lpoly_fun_of_eqI, goal_cases)
  case (1 y)
  show ?case using update_lpoly_impl[of x 0 q]
    by transfer auto
qed

definition reorder_nontriv_var_impl where
  "reorder_nontriv_var_impl x p y = (let c = coeff_lpoly_impl p x
      in update_lpoly_impl y (-1) (update_lpoly_impl x 1 (sdiv_lpoly_impl p c)))" 

lemma reorder_nontriv_var_impl[code]: 
  "reorder_nontriv_var x (lpoly_of p) y = lpoly_of (reorder_nontriv_var_impl x p y)" 
  unfolding reorder_nontriv_var_impl_def Let_def sdiv_lpoly_impl_def coeff_lpoly_impl[symmetric]
proof (intro lpoly_fun_of_eqI, goal_cases)
  case (1 z)
  show ?case unfolding update_lpoly_impl 
    apply (subst map_lpoly_impl, force)
    by transfer auto
qed

declare min_var_def[code del]

lemmas min_var_impl = min_var_def[of "lpoly_of p" for p,
    folded vars_coeffs_impl(5)]

declare min_var_impl[code]

declare gcd_coeffs_l_def[code del]

lemma Gcd_set: "Gcd (set (xs :: 'a :: semiring_Gcd list)) = gcd_list xs" 
  unfolding Gcd_set_eq_fold Gcd_fin.set_eq_fold[of xs] ..

lemma gcd_coeffs_impl[code]: 
  "gcd_coeffs_l (lpoly_of (p :: ('a :: semiring_Gcd,_)lpoly_impl)) = fold gcd (map snd (vars_coeffs_impl p)) 0" 
  unfolding gcd_coeffs_l_def vars_coeffs_impl(5) map_map o_def snd_conv
  unfolding vars_l_list[symmetric] image_set Gcd_set Gcd_fin.set_eq_fold ..

lift_definition change_const_impl :: "'a \<Rightarrow> ('a :: zero, 'v :: linorder)lpoly_impl \<Rightarrow> ('a, 'v)lpoly_impl" 
  is "\<lambda> c (d,vs). (c,vs)" by auto

lemma change_const_impl[code]: "change_const c (lpoly_of p) = lpoly_of (change_const_impl c p)" 
  by (intro lpoly_fun_of_eqI, transfer, auto)


end