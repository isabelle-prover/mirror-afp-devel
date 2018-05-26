(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Missing lemmas\<close>

text \<open>This theory contains many results that are important but not specific for our development. 
      They could be moved to the stardard library and some other AFP entries.\<close> 

theory Missing_Lemmas
  imports
    Berlekamp_Zassenhaus.Sublist_Iteration (* for thm upt_append *)
    Berlekamp_Zassenhaus.Square_Free_Int_To_Square_Free_GFp (* for thm large_mod_0 *)
    Algebraic_Numbers.Resultant
    Jordan_Normal_Form.Conjugate
    Jordan_Normal_Form.Missing_VectorSpace
    Jordan_Normal_Form.VS_Connect
    Berlekamp_Zassenhaus.Finite_Field_Factorization_Record_Based (* for transfer rules for thm vec_of_list_Nil *)
    Berlekamp_Zassenhaus.Berlekamp_Hensel (* for unique_factorization_m_factor *)
begin

no_notation test_bit (infixl "!!" 100)

hide_const(open) module.smult up_ring.monom up_ring.coeff

(**** The following lemmas that could be moved to HOL/Finite_Set.thy  ****)

(*This a generalization of comp_fun_commute. It is a similar definition, but restricted to a set. 
  When "A = UNIV::'a set", we have "comp_fun_commute_on f A = comp_fun_commute f"*)
locale comp_fun_commute_on = 
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and A::"'a set"
  assumes comp_fun_commute_restrict: "\<forall>y\<in>A. \<forall>x\<in>A. \<forall>z\<in>A. f y (f x z) = f x (f y z)"
  and f: "f : A \<rightarrow> A \<rightarrow> A" 
begin

lemma comp_fun_commute_on_UNIV:
  assumes "A = (UNIV :: 'a set)"
  shows "comp_fun_commute f"
  unfolding comp_fun_commute_def 
  using assms comp_fun_commute_restrict f by auto

lemma fun_left_comm: 
  assumes "y \<in> A" and "x \<in> A" and "z \<in> A" shows "f y (f x z) = f x (f y z)"
  using comp_fun_commute_restrict assms by auto

lemma commute_left_comp: 
  assumes "y \<in> A" and "x\<in>A" and "z\<in>A" and "g \<in> A \<rightarrow> A" 
  shows "f y (f x (g z)) = f x (f y (g z))"
  using assms by (auto simp add: Pi_def o_assoc comp_fun_commute_restrict)

lemma fold_graph_finite:
  assumes "fold_graph f z B y"
  shows "finite B"
  using assms by induct simp_all

lemma fold_graph_closed:
  assumes "fold_graph f z B y" and "B \<subseteq> A" and "z \<in> A"
  shows "y \<in> A"
  using assms 
proof (induct set: fold_graph)
  case emptyI
  then show ?case by auto
next
  case (insertI x B y)
  then show ?case using insertI f by auto
qed

lemma fold_graph_insertE_aux:
  "fold_graph f z B y \<Longrightarrow> a \<in> B \<Longrightarrow> z\<in>A
  \<Longrightarrow> B \<subseteq> A
  \<Longrightarrow>  \<exists>y'. y = f a y' \<and> fold_graph f z (B - {a}) y' \<and> y' \<in> A"
proof (induct set: fold_graph)
  case emptyI
  then show ?case by auto
next
  case (insertI x B y)
  show ?case
  proof (cases "x = a")
    case True 
    show ?thesis
    proof (rule exI[of _ y])
      have B: "(insert x B - {a}) = B" using True insertI by auto 
      have "f x y = f a y" by (simp add: True) 
      moreover have "fold_graph f z (insert x B - {a}) y" by (simp add: B insertI)
      moreover have "y \<in> A" using insertI fold_graph_closed[of z B] by auto
      ultimately show " f x y = f a y \<and> fold_graph f z (insert x B - {a}) y \<and> y \<in> A" by simp
    qed
  next
    case False
    then obtain y' where y: "y = f a y'" and y': "fold_graph f z (B - {a}) y'" and y'_in_A: "y' \<in> A"
      using insertI f by auto
    have "f x y = f a (f x y')"
      unfolding y 
    proof (rule fun_left_comm)
      show "x \<in> A" using insertI by auto
      show "a \<in> A" using insertI by auto
      show "y' \<in> A" using y'_in_A by auto
    qed  
    moreover have "fold_graph f z (insert x B - {a}) (f x y')"
      using y' and \<open>x \<noteq> a\<close> and \<open>x \<notin> B\<close>
      by (simp add: insert_Diff_if fold_graph.insertI)    
    moreover have "(f x y') \<in> A" using insertI f y'_in_A by auto
    ultimately show ?thesis using y'_in_A
      by auto
  qed
qed
    
lemma fold_graph_insertE:
  assumes "fold_graph f z (insert x B) v" and "x \<notin> B" and "insert x B \<subseteq> A" and "z\<in>A"
  obtains y where "v = f x y" and "fold_graph f z B y"
  using assms by (auto dest: fold_graph_insertE_aux [OF _ insertI1])

lemma fold_graph_determ: "fold_graph f z B x \<Longrightarrow> fold_graph f z B y \<Longrightarrow>  B \<subseteq> A \<Longrightarrow> z\<in>A \<Longrightarrow> y = x"
proof (induct arbitrary: y set: fold_graph)
  case emptyI
  then show ?case
    by (meson empty_fold_graphE)
next
  case (insertI x B y v)
  from \<open>fold_graph f z (insert x B) v\<close> and \<open>x \<notin> B\<close> and \<open>insert x B \<subseteq> A\<close> and  \<open>z \<in> A\<close>
  obtain y' where "v = f x y'" and "fold_graph f z B y'"
    by (rule fold_graph_insertE)
  from \<open>fold_graph f z B y'\<close> and \<open>insert x B \<subseteq> A\<close> have "y' = y" using insertI by auto    
  with \<open>v = f x y'\<close> show "v = f x y"
    by simp
qed

lemma fold_equality: "fold_graph f z B y \<Longrightarrow> B \<subseteq> A \<Longrightarrow> z \<in> A \<Longrightarrow> Finite_Set.fold f z B = y"
  by (cases "finite B") 
  (auto simp add: Finite_Set.fold_def intro: fold_graph_determ dest: fold_graph_finite)
    
lemma fold_graph_fold:
  assumes f: "finite B" and BA: "B\<subseteq>A" and z: "z \<in> A"
  shows "fold_graph f z B (Finite_Set.fold f z B)"
proof -
   have "\<exists>x. fold_graph f z B x"
    by (rule finite_imp_fold_graph[OF f])
  moreover note fold_graph_determ
  ultimately have "\<exists>!x. fold_graph f z B x" using f BA z by auto    
  then have "fold_graph f z B (The (fold_graph f z B))"
    by (rule theI')
  with assms show ?thesis
    by (simp add: Finite_Set.fold_def)
qed
  
(*This lemma is a generalization of thm comp_fun_commute.fold_insert*)
lemma fold_insert [simp]:
  assumes "finite B" and "x \<notin> B" and BA: "insert x B \<subseteq> A" and z: "z \<in> A"
  shows "Finite_Set.fold f z (insert x B) = f x (Finite_Set.fold f z B)"
  proof (rule fold_equality[OF _ BA z])
  from \<open>finite B\<close> have "fold_graph f z B (Finite_Set.fold f z B)"
   using BA fold_graph_fold z by auto
  hence "fold_graph f z (insert x B) (f x (Finite_Set.fold f z B))"
    using BA  fold_graph.insertI assms by auto
  then show "fold_graph f z (insert x B) (f x (Finite_Set.fold f z B))"
    by simp
qed
end

(*This lemma is a generalization of thm Finite_Set.fold_cong *)
lemma fold_cong:
  assumes f: "comp_fun_commute_on f A" and g: "comp_fun_commute_on g A"
    and "finite S"
    and cong: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
    and "s = t" and "S = T" 
    and SA: "S \<subseteq> A" and s: "s\<in>A"
  shows "Finite_Set.fold f s S = Finite_Set.fold g t T"
proof -
  have "Finite_Set.fold f s S = Finite_Set.fold g s S"
    using \<open>finite S\<close> cong SA s
  proof (induct S)
    case empty
    then show ?case by simp
  next
    case (insert x F)
    interpret f: comp_fun_commute_on f A by (fact f)
    interpret g: comp_fun_commute_on g A by (fact g)
    show ?case  using insert by auto
  qed
  with assms show ?thesis by simp
qed
                    
context comp_fun_commute_on
begin  

lemma comp_fun_Pi: "(\<lambda>x. f x ^^ g x) \<in> A \<rightarrow> A \<rightarrow> A"
proof -    
  have "(f x ^^ g x) y \<in> A" if y: "y \<in> A" and x: "x \<in> A" for x y
    using x y
   proof (induct "g x" arbitrary: g)
     case 0
     then show ?case by auto
   next
     case (Suc n g)
     define h where "h z = g z - 1" for z
     have hyp: "(f x ^^ h x) y \<in> A" 
       using h_def Suc.prems Suc.hyps diff_Suc_1 by metis
     have "g x = Suc (h x)" unfolding h_def
       using Suc.hyps(2) by auto     
     then show ?case using f x hyp unfolding Pi_def by auto
   qed 
  thus ?thesis by (auto simp add: Pi_def)
qed

(*This lemma is a generalization of thm comp_fun_commute.comp_fun_commute_funpow *)
lemma comp_fun_commute_funpow: "comp_fun_commute_on (\<lambda>x. f x ^^ g x) A"
proof -
  have f: " (f y ^^ g y) ((f x ^^ g x) z) = (f x ^^ g x) ((f y ^^ g y) z)"
    if x: "x\<in>A" and y: "y \<in> A" and z: "z \<in> A" for x y z
  proof (cases "x = y")
    case False
    show ?thesis
    proof (induct "g x" arbitrary: g)
      case (Suc n g)
      have hyp1: "(f y ^^ g y) (f x k) = f x ((f y ^^ g y) k)" if k: "k \<in> A" for k
      proof (induct "g y" arbitrary: g)
        case 0
        then show ?case by simp
      next
        case (Suc n g)       
        define h where "h z = g z - 1" for z
        with Suc have "n = h y"
          by simp
        with Suc have hyp: "(f y ^^ h y) (f x k) = f x ((f y ^^ h y) k)"
          by auto
        from Suc h_def have g: "g y = Suc (h y)"
          by simp
        have "((f y ^^ h y) k) \<in> A" using y k comp_fun_Pi[of h] unfolding Pi_def by auto
        then show ?case
          by (simp add: comp_assoc g hyp) (auto simp add: o_assoc comp_fun_commute_restrict x y k)
      qed
      define h where "h a = (if a = x then g x - 1 else g a)" for a
      with Suc have "n = h x"
        by simp
      with Suc have "(f y ^^ h y) ((f x ^^ h x) z) = (f x ^^ h x) ((f y ^^ h y) z)"
        by auto
      with False have Suc2: "(f x ^^ h x) ((f y ^^ g y) z) = (f y ^^ g y) ((f x ^^ h x) z)"
        using h_def by auto      
      from Suc h_def have g: "g x = Suc (h x)"
        by simp
      have "(f x ^^ h x) z \<in>A" using comp_fun_Pi[of h] x z unfolding Pi_def by auto
      hence *: "(f y ^^ g y) (f x ((f x ^^ h x) z)) = f x ((f y ^^ g y) ((f x ^^ h x) z))" 
        using hyp1 by auto
      thus ?case using g Suc2 by auto
    qed simp
  qed simp
  thus ?thesis by (auto simp add: comp_fun_commute_on_def comp_fun_Pi o_def)
qed

(*This lemma is a generalization of thm comp_fun_commute.fold_mset_add_mset*)
lemma fold_mset_add_mset: 
  assumes MA: "set_mset M \<subseteq> A" and s: "s \<in> A" and x: "x \<in> A"
  shows "fold_mset f s (add_mset x M) = f x (fold_mset f s M)"
proof -
  interpret mset: comp_fun_commute_on "\<lambda>y. f y ^^ count M y" A
    by (fact comp_fun_commute_funpow)
  interpret mset_union: comp_fun_commute_on "\<lambda>y. f y ^^ count (add_mset x M) y" A
    by (fact comp_fun_commute_funpow)
  show ?thesis
  proof (cases "x \<in> set_mset M")
    case False
    then have *: "count (add_mset x M) x = 1"
      by (simp add: not_in_iff)
     have "Finite_Set.fold (\<lambda>y. f y ^^ count (add_mset x M) y) s (set_mset M) =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s (set_mset M)"
       by (rule fold_cong[of _ A], auto simp add: assms False comp_fun_commute_funpow)
    with False * s MA x show ?thesis
      by (simp add: fold_mset_def del: count_add_mset)
  next
    case True
    let ?f = "(\<lambda>xa. f xa ^^ count (add_mset x M) xa)"
    let ?f2 = "(\<lambda>x. f x ^^ count M x)"
    define N where "N = set_mset M - {x}"
    have F: "Finite_Set.fold ?f s (insert x N) = ?f x (Finite_Set.fold ?f s N)" 
      by (rule mset_union.fold_insert, auto simp add: assms N_def)
    have F2: "Finite_Set.fold ?f2 s (insert x N) = ?f2 x (Finite_Set.fold ?f2 s N)"
      by (rule mset.fold_insert, auto simp add: assms N_def)
    from N_def True have *: "set_mset M = insert x N" "x \<notin> N" "finite N" by auto
    then have "Finite_Set.fold (\<lambda>y. f y ^^ count (add_mset x M) y) s N =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s N" 
      using MA N_def s 
      by (auto intro!: fold_cong comp_fun_commute_funpow)
    with * show ?thesis by (simp add: fold_mset_def del: count_add_mset, unfold F F2, auto)      
  qed
qed
end

(**** End of the lemmas that could be moved to HOL/Finite_Set.thy  ****)


(**** The following lemmas could be moved to HOL-Algebra  ****)
context abelian_monoid begin

definition sumlist
  where "sumlist xs \<equiv> foldr (\<oplus>) xs \<zero>"
  (* fold is not good as it reverses the list, although the most general locale for monoids with
     \<oplus> is already Abelian in Isabelle 2016-1. foldl is OK but it will not simplify Cons. *)

lemma [simp]:
  shows sumlist_Cons: "sumlist (x#xs) = x \<oplus> sumlist xs"
    and sumlist_Nil: "sumlist [] = \<zero>"
  by (simp_all add: sumlist_def)

lemma sumlist_carrier [simp]:
  assumes "set xs \<subseteq> carrier G" shows "sumlist xs \<in> carrier G"
  using assms by (induct xs, auto)

lemma sumlist_neutral:
  assumes "set xs \<subseteq> {\<zero>}" shows "sumlist xs = \<zero>"
proof (insert assms, induct xs)
  case (Cons x xs)
  then have "x = \<zero>" and "set xs \<subseteq> {\<zero>}" by auto
  with Cons.hyps show ?case by auto
qed simp

lemma sumlist_append:
  assumes "set xs \<subseteq> carrier G" and "set ys \<subseteq> carrier G"
  shows "sumlist (xs @ ys) = sumlist xs \<oplus> sumlist ys"
proof (insert assms, induct xs arbitrary: ys)
  case (Cons x xs)
  have "sumlist (xs @ ys) = sumlist xs \<oplus> sumlist ys"
    using Cons.prems by (auto intro: Cons.hyps)
  with Cons.prems show ?case by (auto intro!: a_assoc[symmetric])
qed auto

lemma sumlist_snoc:
  assumes "set xs \<subseteq> carrier G" and "x \<in> carrier G"
  shows "sumlist (xs @ [x]) = sumlist xs \<oplus> x"
  by (subst sumlist_append, insert assms, auto)

lemma sumlist_as_finsum:
  assumes "set xs \<subseteq> carrier G" and "distinct xs" shows "sumlist xs = (\<Oplus>x\<in>set xs. x)"
  using assms by (induct xs, auto intro:finsum_insert[symmetric])

lemma sumlist_map_as_finsum:
  assumes "f : set xs \<rightarrow> carrier G" and "distinct xs"
  shows "sumlist (map f xs) = (\<Oplus>x \<in> set xs. f x)"
  using assms by (induct xs, auto)

definition summset where "summset M \<equiv> fold_mset (\<oplus>) \<zero> M"

lemma summset_empty [simp]: "summset {#} = \<zero>" by (simp add: summset_def)

lemma fold_mset_add_carrier: "a \<in> carrier G \<Longrightarrow> set_mset M \<subseteq> carrier G \<Longrightarrow> fold_mset (\<oplus>) a M \<in> carrier G" 
proof (induct M arbitrary: a)
  case (add x M)
  thus ?case by 
    (subst comp_fun_commute_on.fold_mset_add_mset[of _ "carrier G"], unfold_locales, auto simp: a_lcomm)
qed simp

lemma summset_carrier[intro]: "set_mset M \<subseteq> carrier G \<Longrightarrow> summset M \<in> carrier G" 
  unfolding summset_def by (rule fold_mset_add_carrier, auto)  

lemma summset_add_mset[simp]:
  assumes a: "a \<in> carrier G" and MG: "set_mset M \<subseteq> carrier G"
  shows "summset (add_mset a M) = a \<oplus> summset M"
  using assms 
  by (auto simp add: summset_def)
   (rule comp_fun_commute_on.fold_mset_add_mset, unfold_locales, auto simp add: a_lcomm)    
 
lemma sumlist_as_summset:
  assumes "set xs \<subseteq> carrier G" shows "sumlist xs = summset (mset xs)"
  by (insert assms, induct xs, auto)

lemma sumlist_rev:
  assumes "set xs \<subseteq> carrier G"
  shows "sumlist (rev xs) = sumlist xs"
  using assms by (simp add: sumlist_as_summset)

lemma sumlist_as_fold:
  assumes "set xs \<subseteq> carrier G"
  shows "sumlist xs = fold (\<oplus>) xs \<zero>"
  by (fold sumlist_rev[OF assms], simp add: sumlist_def foldr_conv_fold)

end
(**** End of lemmas which could be moved to HOL-Algebra  ****)

(**** Could be merged to HOL/Rings.thy ****)

lemma (in zero_less_one) zero_le_one [simp]: "0 \<le> 1" by (rule less_imp_le, simp)
subclass (in zero_less_one) zero_neq_one by (unfold_locales, simp add: less_imp_neq)

class ordered_semiring_1 = Rings.ordered_semiring_0 + monoid_mult + zero_less_one
begin

subclass semiring_1..

lemma of_nat_ge_zero[intro!]: "of_nat n \<ge> 0"
  using add_right_mono[of _ _ 1] by (induct n, auto)

(* Following lemmas are moved from @{class ordered_idom}. *)
lemma zero_le_power [simp]: "0 \<le> a \<Longrightarrow> 0 \<le> a ^ n"
  by (induct n) simp_all

lemma power_mono: "a \<le> b \<Longrightarrow> 0 \<le> a \<Longrightarrow> a ^ n \<le> b ^ n"
  by (induct n) (auto intro: mult_mono order_trans [of 0 a b])

lemma one_le_power [simp]: "1 \<le> a \<Longrightarrow> 1 \<le> a ^ n"
  using power_mono [of 1 a n] by simp

lemma power_le_one: "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> a ^ n \<le> 1"
  using power_mono [of a 1 n] by simp

lemma power_gt1_lemma:
  assumes gt1: "1 < a"
  shows "1 < a * a ^ n"
proof -
  from gt1 have "0 \<le> a"
    by (fact order_trans [OF zero_le_one less_imp_le])
  from gt1 have "1 * 1 < a * 1" by simp
  also from gt1 have "\<dots> \<le> a * a ^ n"
    by (simp only: mult_mono \<open>0 \<le> a\<close> one_le_power order_less_imp_le zero_le_one order_refl)
  finally show ?thesis by simp
qed

lemma power_gt1: "1 < a \<Longrightarrow> 1 < a ^ Suc n"
  by (simp add: power_gt1_lemma)

lemma one_less_power [simp]: "1 < a \<Longrightarrow> 0 < n \<Longrightarrow> 1 < a ^ n"
  by (cases n) (simp_all add: power_gt1_lemma)

text \<open>Proof resembles that of \<open>power_strict_decreasing\<close>.\<close>
lemma power_decreasing: "n \<le> N \<Longrightarrow> 0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> a ^ N \<le> a ^ n"
proof (induct N)
  case 0
  then show ?case by simp
next
  case (Suc N)
  then show ?case
    apply (auto simp add: le_Suc_eq)
    apply (subgoal_tac "a * a^N \<le> 1 * a^n")
     apply simp
    apply (rule mult_mono)
       apply auto
    done
qed

text \<open>Proof again resembles that of \<open>power_strict_decreasing\<close>.\<close>
lemma power_increasing: "n \<le> N \<Longrightarrow> 1 \<le> a \<Longrightarrow> a ^ n \<le> a ^ N"
proof (induct N)
  case 0
  then show ?case by simp
next
  case (Suc N)
  then show ?case
    apply (auto simp add: le_Suc_eq)
    apply (subgoal_tac "1 * a^n \<le> a * a^N")
     apply simp
    apply (rule mult_mono)
       apply (auto simp add: order_trans [OF zero_le_one])
    done
qed

lemma power_Suc_le_self: "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> a ^ Suc n \<le> a"
  using power_decreasing [of 1 "Suc n" a] by simp

end

lemma prod_list_nonneg: "(\<And> x. (x :: 'a :: ordered_semiring_1) \<in> set xs \<Longrightarrow> x \<ge> 0) \<Longrightarrow> prod_list xs \<ge> 0"
  by (induct xs, auto)

subclass (in ordered_idom) ordered_semiring_1 by unfold_locales auto

(**** End of lemmas that could be moved to HOL/Rings.thy ****)

(* missing lemma on logarithms *)
lemma log_prod: assumes "0 < a" "a \<noteq> 1" "\<And> x. x \<in> X \<Longrightarrow> 0 < f x" 
  shows "log a (prod f X) = sum (log a o f) X" 
  using assms(3)
proof (induct X rule: infinite_finite_induct)
  case (insert x F)
  have "log a (prod f (insert x F)) = log a (f x * prod f F)" using insert by simp
  also have "\<dots> = log a (f x) + log a (prod f F)" 
    by (rule log_mult[OF assms(1-2) insert(4) prod_pos], insert insert, auto)
  finally show ?case using insert by auto
qed auto

(* TODO: Jordan_Normal_Form/Missing_Ring.ordered_idom should be redefined *)
subclass (in ordered_idom) zero_less_one by (unfold_locales, auto)
hide_fact Missing_Ring.zero_less_one

(**** The following lemmas could be part of the standard library ****)

instance real :: ordered_semiring_strict by (intro_classes, auto)
instance real :: linordered_idom..

(*This is a generalisation of thm less_1_mult*) 
lemma less_1_mult': 
  fixes a::"'a::linordered_semidom"
  shows "1 < a \<Longrightarrow> 1 \<le> b \<Longrightarrow> 1 < a * b"
  by (metis le_less less_1_mult mult.right_neutral)

lemma upt_minus_eq_append: "i\<le>j \<Longrightarrow> i\<le>j-k \<Longrightarrow> [i..<j] = [i..<j-k] @ [j-k..<j]"
proof (induct k)
  case (Suc k)
  have hyp: "[i..<j] = [i..<j - k] @ [j - k..<j]" using Suc.hyps Suc.prems by auto
  then show ?case
    by (metis Suc.prems(2) append.simps(1) diff_Suc_less nat_less_le neq0_conv upt_append upt_rec zero_diff)
qed auto

lemma list_trisect: "x < length lst \<Longrightarrow> [0..<length lst] = [0..<x]@x#[Suc x..<length lst]"
  by (induct lst, force, rename_tac a lst, case_tac "x = length lst", auto)

lemma filter_mset_inequality: "filter_mset f xs \<noteq> xs \<Longrightarrow> \<exists> x \<in># xs. \<not> f x" 
  by (induct xs, auto)

lemma id_imp_bij_betw:
  assumes f: "f : A \<rightarrow> A"
      and ff: "\<And>a. a \<in> A \<Longrightarrow> f (f a) = a"
  shows "bij_betw f A A"
  by (intro bij_betwI[OF f f], simp_all add: ff)

lemma if_distrib_ap:
  "(if x then y else z) u = (if x then y u else z u)" by auto

lemma range_subsetI:
  assumes "\<And>x. f x = g (h x)" shows "range f \<subseteq> range g"
  using assms by auto

lemma Gcd_uminus: 
  fixes A::"int set"
  assumes "finite A"
  shows "Gcd A = Gcd (uminus ` A)"
  using assms
  by (induct A, auto)

lemma aux_abs_int: fixes c :: int
  assumes "c \<noteq> 0" 
  shows "\<bar>x\<bar> \<le> \<bar>x * c\<bar>"
proof -
  have "abs x = abs x * 1" by simp
  also have "\<dots> \<le> abs x * abs c" 
    by (rule mult_left_mono, insert assms, auto)
  finally show ?thesis unfolding abs_mult by auto
qed

lemma mod_0_abs_less_imp_0:
  fixes a::int
  assumes a1: "[a = 0] (mod m)"
  and a2: "abs(a)<m"
  shows "a = 0"
proof -
  have "m\<ge>0" using assms by auto
  thus ?thesis  
    using assms unfolding cong_def
    using int_mod_pos_eq large_mod_0 zless_imp_add1_zle 
      by (metis abs_of_nonneg le_less not_less zabs_less_one_iff zmod_trival_iff)
qed

(* an intro version of sum_list_0 *)
lemma sum_list_zero:
  assumes "set xs \<subseteq> {0}" shows "sum_list xs = 0"
  using assms by (induct xs, auto)

(* About @{const max} *)
lemma max_idem [simp]: shows "max a a = a" by (simp add: max_def)

lemma hom_max:
  assumes "a \<le> b \<longleftrightarrow> f a \<le> f b"
  shows "f (max a b) = max (f a) (f b)" using assms by (auto simp: max_def)

lemma le_max_self:
  fixes a b :: "'a :: preorder"
  assumes "a \<le> b \<or> b \<le> a" shows "a \<le> max a b" and "b \<le> max a b"
  using assms by (auto simp: max_def)

lemma le_max:
  fixes a b :: "'a :: preorder"
  assumes "c \<le> a \<or> c \<le> b" and "a \<le> b \<or> b \<le> a" shows "c \<le> max a b"
  using assms(1) le_max_self[OF assms(2)] by (auto dest: order_trans)

fun max_list where
  "max_list [] = (THE x. False)" (* more convenient than "undefined" *)
| "max_list [x] = x"
| "max_list (x # y # xs) = max x (max_list (y # xs))"

declare max_list.simps(1) [simp del]
declare max_list.simps(2-3)[code]

lemma max_list_Cons: "max_list (x#xs) = (if xs = [] then x else max x (max_list xs))"
  by (cases xs, auto)

lemma max_list_mem: "xs \<noteq> [] \<Longrightarrow> max_list xs \<in> set xs"
  by (induct xs, auto simp: max_list_Cons max_def)

lemma mem_set_imp_le_max_list:
  fixes xs :: "'a :: preorder list"
  assumes "\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<le> b \<or> b \<le> a"
      and "a \<in> set xs"
  shows "a \<le> max_list xs"
proof (insert assms, induct xs arbitrary:a)
  case Nil
  with assms show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case False
    have "x \<le> max_list xs \<or> max_list xs \<le> x"
      apply (rule Cons(2)) using max_list_mem[of xs] False by auto
    note 1 = le_max_self[OF this]
    from Cons have "a = x \<or> a \<in> set xs" by auto
    then show ?thesis
    proof (elim disjE)
      assume a: "a = x"
      show ?thesis by (unfold a max_list_Cons, auto simp: False intro!: 1)
    next
      assume "a \<in> set xs"
      then have "a \<le> max_list xs" by (intro Cons, auto)
      with 1 have "a \<le> max x (max_list xs)" by (auto dest: order_trans)
      then show ?thesis by (unfold max_list_Cons, auto simp: False)
    qed
  qed (insert Cons, auto)
qed

lemma le_max_list:
  fixes xs :: "'a :: preorder list"
  assumes ord: "\<And>a b. a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<le> b \<or> b \<le> a"
      and ab: "a \<le> b"
      and b: "b \<in> set xs"
  shows "a \<le> max_list xs"
proof-
  note ab
  also have "b \<le> max_list xs"
    by (rule mem_set_imp_le_max_list, fact ord, fact b)
  finally show ?thesis.
qed

lemma max_list_le:
  fixes xs :: "'a :: preorder list"
  assumes a: "\<And>x. x \<in> set xs \<Longrightarrow> x \<le> a"
      and xs: "xs \<noteq> []"
  shows "max_list xs \<le> a"
  using max_list_mem[OF xs] a by auto

lemma max_list_as_Greatest:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<le> y \<or> y \<le> x"
  shows "max_list xs = (GREATEST a. a \<in> set xs)"
proof (cases "xs = []")
  case True
  then show ?thesis by (unfold Greatest_def, auto simp: max_list.simps(1))
next
  case False
  from assms have 1: "x \<in> set xs \<Longrightarrow> x \<le> max_list xs" for x
    by (auto intro: le_max_list)
  have 2: "max_list xs \<in> set xs" by (fact max_list_mem[OF False])
  have "\<exists>!x. x \<in> set xs \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y \<le> x)" (is "\<exists>!x. ?P x")
  proof (intro ex1I)
    from 1 2
    show "?P (max_list xs)" by auto
  next
    fix x assume 3: "?P x"
    with 1 have "x \<le> max_list xs" by auto
    moreover from 2 3 have "max_list xs \<le> x" by auto
    ultimately show "x = max_list xs" by auto
  qed
  note 3 = theI_unique[OF this,symmetric]
  from 1 2 show ?thesis
    by (unfold Greatest_def Cons 3, auto)
qed

lemma hom_max_list_commute:
  assumes "xs \<noteq> []"
      and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> h (max x y) = max (h x) (h y)"
  shows "h (max_list xs) = max_list (map h xs)"
  by (insert assms, induct xs, auto simp: max_list_Cons max_list_mem)


(*Efficient rev [i..<j]*)
primrec rev_upt :: "nat \<Rightarrow> nat \<Rightarrow> nat list" ("(1[_>.._])") where
rev_upt_0: "[0>..j] = []" |
rev_upt_Suc: "[(Suc i)>..j] = (if i \<ge> j then i # [i>..j] else [])"

lemma rev_upt_rec: "[i>..j] = (if i>j then [i>..Suc j] @ [j] else [])"
  by (induct i, auto)    

definition rev_upt_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "rev_upt_aux i j js = [i>..j] @ js"

lemma upt_aux_rec [code]:
  "rev_upt_aux i j js = (if j\<ge>i then js else rev_upt_aux i (Suc j) (j#js))"
  by (induct j, auto simp add: rev_upt_aux_def rev_upt_rec)

lemma rev_upt_code[code]: "[i>..j] = rev_upt_aux i j []"
  by(simp add: rev_upt_aux_def)    
  
lemma upt_rev_upt:
  "rev [j>..i] = [i..<j]"
  by (induct j, auto)
    
lemma rev_upt_upt:
  "rev [i..<j] = [j>..i]"
  by (induct j, auto) 

lemma length_rev_upt [simp]: "length [i>..j] = i - j"
  by (induct i) (auto simp add: Suc_diff_le)
    
lemma nth_rev_upt [simp]: "j + k < i \<Longrightarrow> [i>..j] ! k = i - 1 - k"
proof -
  assume jk_i: "j + k < i"
  have "[i>..j] = rev [j..<i]" using rev_upt_upt by simp
  also have "... ! k = [j..<i] ! (length [j..<i] - 1 - k)"
    by (rule nth_rev, insert jk_i, auto)
  also have "... = [j..<i] ! (i - j - 1 - k)" by auto
  also have "... = j + (i - j - 1 - k)" by (rule nth_upt, insert jk_i, auto)
  finally show ?thesis using jk_i by auto
qed    
  
lemma nth_map_rev_upt: 
  assumes i: "i < m-n"
  shows "(map f [m>..n]) ! i = f (m - 1 - i)"
proof -
  have "(map f [m>..n]) ! i = f ([m>..n] ! i)" by (rule nth_map, auto simp add: i)
  also have "... = f (m - 1 - i)"
  proof (rule arg_cong[of _ _ f], rule nth_rev_upt)
    show "n + i < m" using i by linarith
  qed
  finally show ?thesis .
qed

lemma coeff_mult_monom:
 "coeff (p * monom a d) i = (if d \<le> i then a * coeff p (i - d) else 0)"
  using coeff_monom_mult[of a d p] by (simp add: ac_simps)

(**** End of the lemmas which may be part of the standard library ****)


(**** The following lemmas could be part of Jordan_Normal_Form/Conjugate.thy ****)

(**** The following lemmas could be part of Jordan_Normal_Form/Matrix.thy ****)

(* adapting from Jordan_Normal_Form/Gram_Schmidt to a class-oriented manner *)
instantiation vec :: (conjugate) conjugate
begin

definition conjugate_vec :: "'a :: conjugate vec \<Rightarrow> 'a vec"
  where "conjugate v = vec (dim_vec v) (\<lambda>i. conjugate (v $ i))"

lemma conjugate_vCons [simp]:
  "conjugate (vCons a v) = vCons (conjugate a) (conjugate v)"
  by (auto simp: vec_Suc conjugate_vec_def)

lemma dim_vec_conjugate[simp]: "dim_vec (conjugate v) = dim_vec v"
  unfolding conjugate_vec_def by auto

lemma carrier_vec_conjugate[simp]: "v \<in> carrier_vec n \<Longrightarrow> conjugate v \<in> carrier_vec n"
  by (auto intro!: carrier_vecI)

lemma vec_index_conjugate[simp]:
  shows "i < dim_vec v \<Longrightarrow> conjugate v $ i = conjugate (v $ i)"
  unfolding conjugate_vec_def by auto

instance
proof
  fix v w :: "'a vec"
  show "conjugate (conjugate v) = v" by (induct v, auto simp: conjugate_vec_def)
  let ?v = "conjugate v"
  let ?w = "conjugate w"
  show "conjugate v = conjugate w \<longleftrightarrow> v = w"
  proof(rule iffI)
    assume cvw: "?v = ?w" show "v = w"
    proof(rule)
      have "dim_vec ?v = dim_vec ?w" using cvw by auto
      then show dim: "dim_vec v = dim_vec w" by simp
      fix i assume i: "i < dim_vec w"
      then have "conjugate v $ i = conjugate w $ i" using cvw by auto
      then have "conjugate (v$i) = conjugate (w $ i)" using i dim by auto
      then show "v $ i = w $ i" by auto
    qed
  qed auto
qed

end

lemma conjugate_add_vec:
  fixes v w :: "'a :: conjugatable_ring vec"
  assumes dim: "v : carrier_vec n" "w : carrier_vec n"
  shows "conjugate (v + w) = conjugate v + conjugate w"
  by (rule, insert dim, auto simp: conjugate_dist_add)

lemma uminus_conjugate_vec:
  fixes v w :: "'a :: conjugatable_ring vec"
  shows "- (conjugate v) = conjugate (- v)"
  by (rule, auto simp:conjugate_neg)

lemma conjugate_zero_vec[simp]:
  "conjugate (0\<^sub>v n :: 'a :: conjugatable_ring vec) = 0\<^sub>v n" by auto

lemma conjugate_vec_0[simp]:
  "conjugate (vec 0 f) = vec 0 f" by auto

lemma sprod_vec_0[simp]: "v \<bullet> vec 0 f = 0"
  by(auto simp: scalar_prod_def)

lemma conjugate_zero_iff_vec[simp]:
  fixes v :: "'a :: conjugatable_ring vec"
  shows "conjugate v = 0\<^sub>v n \<longleftrightarrow> v = 0\<^sub>v n"
  using conjugate_cancel_iff[of _ "0\<^sub>v n :: 'a vec"] by auto

lemma conjugate_smult_vec:
  fixes k :: "'a :: conjugatable_ring"
  shows "conjugate (k \<cdot>\<^sub>v v) = conjugate k \<cdot>\<^sub>v conjugate v"
  using conjugate_dist_mul by (intro eq_vecI, auto)

lemma conjugate_sprod_vec:
  fixes v w :: "'a :: conjugatable_ring vec"
  assumes v: "v : carrier_vec n" and w: "w : carrier_vec n"
  shows "conjugate (v \<bullet> w) = conjugate v \<bullet> conjugate w"
proof (insert w v, induct w arbitrary: v rule:carrier_vec_induct)
  case 0 then show ?case by (cases v, auto)
next
  case (Suc n b w) then show ?case
    by (cases v, auto dest: carrier_vecD simp:conjugate_dist_add conjugate_dist_mul)
qed 

abbreviation cscalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: conjugatable_ring" (infix "\<bullet>c" 70)
  where "(\<bullet>c) \<equiv> \<lambda>v w. v \<bullet> conjugate w"

lemma conjugate_conjugate_sprod[simp]:
  assumes v[simp]: "v : carrier_vec n" and w[simp]: "w : carrier_vec n"
  shows "conjugate (conjugate v \<bullet> w) = v \<bullet>c w"
  apply (subst conjugate_sprod_vec[of _ n]) by auto

lemma conjugate_vec_sprod_comm:
  fixes v w :: "'a :: {conjugatable_ring, comm_ring} vec"
  assumes "v : carrier_vec n" and "w : carrier_vec n"
  shows "v \<bullet>c w = (conjugate w \<bullet> v)"
  unfolding scalar_prod_def using assms by(subst sum_ivl_cong, auto simp: ac_simps)

lemma conjugate_square_ge_0_vec[intro!]:
  fixes v :: "'a :: conjugatable_ordered_ring vec"
  shows "v \<bullet>c v \<ge> 0"
proof (induct v)
  case vNil
  then show ?case by auto
next
  case (vCons a v)
  then show ?case using conjugate_square_positive[of a] by auto
qed

lemma conjugate_square_eq_0_vec[simp]:
  fixes v :: "'a :: {conjugatable_ordered_ring,semiring_no_zero_divisors} vec"
  assumes "v \<in> carrier_vec n"
  shows "v \<bullet>c v = 0 \<longleftrightarrow> v = 0\<^sub>v n"
proof (insert assms, induct rule: carrier_vec_induct)
  case 0
  then show ?case by auto
next
  case (Suc n a v)
  then show ?case
    using conjugate_square_positive[of a] conjugate_square_ge_0_vec[of v]
    by (auto simp: le_less add_nonneg_eq_0_iff zero_vec_Suc)
qed

lemma conjugate_square_greater_0_vec[simp]:
  fixes v :: "'a :: {conjugatable_ordered_ring,semiring_no_zero_divisors} vec"
  assumes "v \<in> carrier_vec n"
  shows "v \<bullet>c v > 0 \<longleftrightarrow> v \<noteq> 0\<^sub>v n"
  using assms by (auto simp: less_le)

lemma vec_conjugate_rat[simp]: "(conjugate :: rat vec \<Rightarrow> rat vec) = (\<lambda>x. x)" by force
lemma vec_conjugate_real[simp]: "(conjugate :: real vec \<Rightarrow> real vec) = (\<lambda>x. x)" by force

(**** End of the lemmas which could be part of Jordan_Normal_Form/Matrix.thy ****)

(**** The following lemmas could be moved to Algebraic_Numbers/Resultant.thy ****)
lemma vec_of_poly_0 [simp]: "vec_of_poly 0 = 0\<^sub>v 1" by (auto simp: vec_of_poly_def)

lemma vec_index_vec_of_poly [simp]: "i \<le> degree p \<Longrightarrow> vec_of_poly p $ i = coeff p (degree p - i)"
  by (simp add: vec_of_poly_def Let_def)

lemma poly_of_vec_vec: "poly_of_vec (vec n f) = Poly (rev (map f [0..<n]))"
proof (induct n arbitrary:f)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "map f [0..<Suc n] = f 0 # map (f \<circ> Suc) [0..<n]" by (simp add: map_upt_Suc del: upt_Suc)
  also have "Poly (rev \<dots>) = Poly (rev (map (f \<circ> Suc) [0..<n])) + monom (f 0) n"
    by (simp add: Poly_snoc smult_monom)
  also have "\<dots> = poly_of_vec (vec n (f \<circ> Suc)) + monom (f 0) n"
    by (fold Suc, simp)
  also have "\<dots> = poly_of_vec (vec (Suc n) f)"
    apply (unfold poly_of_vec_def Let_def dim_vec sum_lessThan_Suc)
    by (auto simp add: Suc_diff_Suc)
  finally show ?case..
qed

lemma sum_list_map_dropWhile0:
  assumes f0: "f 0 = 0"
  shows "sum_list (map f (dropWhile ((=) 0) xs)) = sum_list (map f xs)"
  by (induct xs, auto simp add: f0)

lemma coeffs_poly_of_vec:
  "coeffs (poly_of_vec v) = rev (dropWhile ((=) 0) (list_of_vec v))"
proof-
  obtain n f where v: "v = vec n f" by transfer auto
  show ?thesis by (simp add: v poly_of_vec_vec)
qed

lemma poly_of_vec_vCons:
 "poly_of_vec (vCons a v) = monom a (dim_vec v) + poly_of_vec v" (is "?l = ?r")
  by (auto intro: poly_eqI simp: coeff_poly_of_vec vec_index_vCons)

lemma poly_of_vec_as_Poly: "poly_of_vec v = Poly (rev (list_of_vec v))"
  by (induct v, auto simp:poly_of_vec_vCons Poly_snoc ac_simps)

lemma poly_of_vec_add:
  assumes "dim_vec a = dim_vec b"
  shows "poly_of_vec (a + b) = poly_of_vec a + poly_of_vec b"
  using assms
  by (auto simp add: poly_eq_iff coeff_poly_of_vec)

(*TODO: replace the one in Resultant.thy*)
lemma degree_poly_of_vec_less:
  assumes "0 < dim_vec v" and "dim_vec v \<le> n" shows "degree (poly_of_vec v) < n"
  using degree_poly_of_vec_less assms by (auto dest: less_le_trans)

lemma (in vec_module) poly_of_vec_finsum:
  assumes "f \<in> X \<rightarrow> carrier_vec n"
  shows "poly_of_vec (finsum V f X) = (\<Sum>i\<in>X. poly_of_vec (f i))"
proof (cases "finite X")
  case False then show ?thesis by auto
next
  case True show ?thesis
  proof (insert True assms, induct X rule: finite_induct)
    case IH: (insert a X)
    have [simp]: "f x \<in> carrier_vec n" if x: "x \<in> X" for x 
      using x IH.prems unfolding Pi_def by auto
    have [simp]: "f a \<in> carrier_vec n" using IH.prems unfolding Pi_def by auto
    have [simp]: "dim_vec (finsum V f X) = n" by simp
    have [simp]: "dim_vec (f a) = n" by simp
    show ?case
    proof (cases "a \<in> X")
      case True then show ?thesis by (auto simp: insert_absorb IH)
    next
      case False
      then have "(finsum V f (insert a X)) = f a + (finsum V f X)" 
        by (auto intro: finsum_insert IH)
      also have "poly_of_vec ... = poly_of_vec (f a) + poly_of_vec (finsum V f X)"
        by (rule poly_of_vec_add, simp)
      also have "... = (\<Sum>i\<in>insert a X. poly_of_vec (f i))"
        using IH False by (subst sum.insert, auto)
      finally show ?thesis .
    qed
  qed auto
qed

(*This function transforms a polynomial to a vector of dimension n*)  
definition "vec_of_poly_n p n =
  vec n (\<lambda>i. if i < n - degree p - 1 then 0 else coeff p (n - i - 1))"

(* TODO: make it abbreviation? *)
lemma vec_of_poly_as: "vec_of_poly_n p (Suc (degree p)) = vec_of_poly p"
  by (induct p, auto simp: vec_of_poly_def vec_of_poly_n_def)

lemma vec_of_poly_n_0 [simp]: "vec_of_poly_n p 0 = vNil"
  by (auto simp: vec_of_poly_n_def)

lemma vec_dim_vec_of_poly_n [simp]:
  "dim_vec (vec_of_poly_n p n) = n"
  "vec_of_poly_n p n \<in> carrier_vec n"
  unfolding vec_of_poly_n_def by auto

lemma dim_vec_of_poly [simp]: "dim_vec (vec_of_poly f) = degree f + 1"
  by (simp add: vec_of_poly_as[symmetric])

lemma vec_index_of_poly_n:
  assumes "i < n"
  shows "vec_of_poly_n p n $ i =
    (if i < n - Suc (degree p) then 0 else coeff p (n - i - 1))"
  using assms by (auto simp: vec_of_poly_n_def Let_def)

lemma vec_of_poly_n_pCons[simp]:
  shows "vec_of_poly_n (pCons a p) (Suc n) = vec_of_poly_n p n @\<^sub>v vec_of_list [a]" (is "?l = ?r")
proof (unfold vec_eq_iff, intro conjI allI impI)
  show "dim_vec ?l = dim_vec ?r" by auto
  show "i < dim_vec ?r \<Longrightarrow> ?l $ i = ?r $ i" for i
    by (cases "n - i", auto simp: coeff_pCons less_Suc_eq_le vec_index_of_poly_n)
qed

lemma vec_of_poly_pCons:
  shows "vec_of_poly (pCons a p) =
   (if p = 0 then vec_of_list [a] else vec_of_poly p @\<^sub>v vec_of_list [a])"
  by (cases "degree p", auto simp: vec_of_poly_as[symmetric])

lemma list_of_vec_of_poly [simp]:
  "list_of_vec (vec_of_poly p) = (if p = 0 then [0] else rev (coeffs p))"
  by (induct p, auto simp: vec_of_poly_pCons)

lemma poly_of_vec_of_poly_n:
  assumes p: "degree p<n"
  shows "poly_of_vec (vec_of_poly_n p n) = p"
proof - 
  have "vec_of_poly_n p n $ (n - Suc i) = coeff p i" if i: "i < n" for i    
  proof -
    have n: "n - Suc i < n" using i by auto
    have "vec_of_poly_n p n $ (n - Suc i) = 
      (if n - Suc i < n - Suc (degree p) then 0 else coeff p (n - (n - Suc i) - 1))"
      using vec_index_of_poly_n[OF n, of p] .
    also have "... = coeff p i" using i n le_degree by fastforce
    finally show ?thesis .
  qed
  moreover have "coeff p i = 0" if i2: "i \<ge> n" for i
    by (rule coeff_eq_0, insert i2 p, simp)
  ultimately show ?thesis
  using assms
  unfolding poly_eq_iff
  unfolding coeff_poly_of_vec by auto
qed

lemma vec_of_poly_n0[simp]: "vec_of_poly_n 0 n = 0\<^sub>v n" 
  unfolding vec_of_poly_n_def by auto

lemma vec_of_poly_n_add: "vec_of_poly_n (a + b) n = vec_of_poly_n a n + vec_of_poly_n b n"
proof (induct n arbitrary: a b)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by (cases a, cases b, auto)
qed

lemma vec_of_poly_n_poly_of_vec:
  assumes n: "dim_vec g = n"
  shows "vec_of_poly_n (poly_of_vec g) n = g"
proof (auto simp add: poly_of_vec_def vec_of_poly_n_def assms vec_eq_iff Let_def)
  have d: "degree (\<Sum>i<n. monom (g $ (n - Suc i)) i) = degree (poly_of_vec g)" 
    unfolding poly_of_vec_def Let_def n by auto
  fix i assume i1: "i < n - Suc (degree (\<Sum>i<n. monom (g $ (n - Suc i)) i))" 
    and i2: "i < n"
  have i3: "i < n - Suc (degree (poly_of_vec g))" 
    using i1 unfolding d by auto
  hence "dim_vec g - Suc i > degree (poly_of_vec g)"
    using n by linarith
  then show "g $ i = 0" using i1 i2 i3    
    by (metis (no_types, lifting) Suc_diff_Suc coeff_poly_of_vec diff_Suc_less 
        diff_diff_cancel leD le_degree less_imp_le_nat n neq0_conv)
next
  fix i assume "i < n"
  thus "coeff (\<Sum>i<n. monom (g $ (n - Suc i)) i) (n - Suc i) = g $ i"    
    by (metis (no_types) Suc_diff_Suc coeff_poly_of_vec diff_diff_cancel 
        diff_less_Suc less_imp_le_nat n not_less_eq poly_of_vec_def)
qed

lemma poly_of_vec_scalar_mult:
  assumes "degree b<n"
  shows "poly_of_vec (a \<cdot>\<^sub>v (vec_of_poly_n b n)) = smult a b"
  using assms
  by (auto simp add: poly_eq_iff coeff_poly_of_vec vec_of_poly_n_def coeff_eq_0)

(*TODO: replace the one in Resultant.thy*)
definition vec_of_poly_rev_shifted where
  "vec_of_poly_rev_shifted p n s j \<equiv>
   vec n (\<lambda>i. if i \<le> j \<and> j \<le> s + i then coeff p (s + i - j) else 0)"

lemma vec_of_poly_rev_shifted_dim[simp]: "dim_vec (vec_of_poly_rev_shifted p n s j) = n"
  unfolding vec_of_poly_rev_shifted_def by auto

lemma col_sylvester_sub: (* TODO: from this directly derive col_sylvester *)
  assumes j: "j < m + n"
  shows "col (sylvester_mat_sub m n p q) j =
    vec_of_poly_rev_shifted p n m j @\<^sub>v vec_of_poly_rev_shifted q m n j" (is "?l = ?r")
proof
  show "dim_vec ?l = dim_vec ?r" by simp
  fix i assume "i < dim_vec ?r" then have i: "i < m+n" by auto
  show "?l $ i = ?r $ i"
    unfolding vec_of_poly_rev_shifted_def
    apply (subst index_col) using i apply simp using j apply simp
    apply (subst sylvester_mat_sub_index) using i apply simp using j apply simp
    apply (cases "i < n") using i apply force using i
    apply (auto simp: not_less not_le intro!: coeff_eq_0)
    done
qed

lemma vec_of_poly_rev_shifted_scalar_prod:
  fixes p v
  defines "q \<equiv> poly_of_vec v"
  assumes m: "degree p \<le> m" and n: "dim_vec v = n"
  assumes j: "j < m+n"
  shows "vec_of_poly_rev_shifted p n m (n+m-Suc j) \<bullet> v = coeff (p * q) j" (is "?l = ?r")
proof -
  have id1: "\<And> i. m + i - (n + m - Suc j) = i + Suc j - n"
    using j by auto
  let ?g = "\<lambda> i. if i \<le> n + m - Suc j \<and> n - Suc j \<le> i then coeff p (i + Suc j - n) *  v $ i else 0"
  have "?thesis = ((\<Sum>i = 0..<n. ?g i) =          
        (\<Sum>i\<le>j. coeff p i * (if j - i < n then v $ (n - Suc (j - i)) else 0)))" (is "_ = (?l = ?r)")
    unfolding vec_of_poly_rev_shifted_def coeff_mult m scalar_prod_def n q_def
      coeff_poly_of_vec 
    by (subst sum.cong, insert id1, auto)
  also have "..." 
  proof -
    have "?r = (\<Sum>i\<le>j. (if j - i < n then coeff p i * v $ (n - Suc (j - i)) else 0))" (is "_ = sum ?f _")
      by (rule sum.cong, auto)
    also have "sum ?f {..j} = sum ?f ({i. i \<le> j \<and> j - i < n} \<union> {i. i \<le> j \<and> \<not> j - i < n})" 
      (is "_ = sum _ (?R1 \<union> ?R2)")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?f ?R1 + sum ?f ?R2"
      by (subst sum.union_disjoint, auto)
    also have "sum ?f ?R2 = 0"
      by (rule sum.neutral, auto)
    also have "sum ?f ?R1 + 0 = sum (\<lambda> i. coeff p i * v $ (i + n - Suc j)) ?R1"
      (is "_ = sum ?F _")
      by (subst sum.cong, auto simp: ac_simps)
    also have "\<dots> = sum ?F ((?R1 \<inter> {..m}) \<union> (?R1 - {..m}))"
      (is "_ = sum _ (?R \<union> ?R')")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?F ?R + sum ?F ?R'"
      by (subst sum.union_disjoint, auto)
    also have "sum ?F ?R' = 0"
    proof -
      { 
        fix x
        assume "x > m" 
        with m
        have "?F x = 0" by (subst coeff_eq_0, auto)
      }
      thus ?thesis
        by (subst sum.neutral, auto)
    qed
    finally have r: "?r = sum ?F ?R" by simp

    have "?l = sum ?g ({i. i < n \<and> i \<le> n + m - Suc j \<and> n - Suc j \<le> i} 
      \<union> {i. i < n \<and> \<not> (i \<le> n + m - Suc j \<and> n - Suc j \<le> i)})" 
      (is "_ = sum _ (?L1 \<union> ?L2)")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?g ?L1 + sum ?g ?L2"
      by (subst sum.union_disjoint, auto)
    also have "sum ?g ?L2 = 0"
      by (rule sum.neutral, auto)
    also have "sum ?g ?L1 + 0 = sum (\<lambda> i. coeff p (i + Suc j - n) * v $ i) ?L1"
      (is "_ = sum ?G _")
      by (subst sum.cong, auto)
    also have "\<dots> = sum ?G (?L1 \<inter> {i. i + Suc j - n \<le> m} \<union> (?L1 - {i. i + Suc j - n \<le> m}))"
      (is "_ = sum _ (?L \<union> ?L')")
      by (subst sum.cong, auto)
    also have "\<dots> = sum ?G ?L + sum ?G ?L'"
      by (subst sum.union_disjoint, auto)
    also have "sum ?G ?L' = 0"
    proof -
      {
        fix x
        assume "x + Suc j - n > m" 
        with m
        have "?G x = 0" by (subst coeff_eq_0, auto)
      }
      thus ?thesis
        by (subst sum.neutral, auto)
    qed
    finally have l: "?l = sum ?G ?L" by simp

    let ?bij = "\<lambda> i. i + n - Suc j"
    {
      fix x
      assume x: "j < m + n" "Suc (x + j) - n \<le> m" "x < n" "n - Suc j \<le> x" 
      define y where "y = x + Suc j - n"
      from x have "x + Suc j \<ge> n" by auto
      with x have xy: "x = ?bij y" unfolding y_def by auto
      from x have y: "y \<in> ?R" unfolding y_def by auto
      have "x \<in> ?bij ` ?R" unfolding xy using y by blast
    } note tedious = this
    show ?thesis unfolding l r
      by (rule sum.reindex_cong[of ?bij], insert j, auto simp: inj_on_def tedious)
  qed
  finally show ?thesis by simp
qed

lemma sylvester_sub_poly:
  fixes p q :: "'a :: comm_semiring_0 poly"
  assumes m: "degree p \<le> m"
  assumes n: "degree q \<le> n"
  assumes v: "v \<in> carrier_vec (m+n)"
  shows "poly_of_vec ((sylvester_mat_sub m n p q)\<^sup>T *\<^sub>v v) =
    poly_of_vec (vec_first v n) * p + poly_of_vec (vec_last v m) * q" (is "?l = ?r")
proof (rule poly_eqI)
  fix i
  let ?Tv = "(sylvester_mat_sub m n p q)\<^sup>T *\<^sub>v v"
  have dim: "dim_vec (vec_first v n) = n" "dim_vec (vec_last v m) = m" "dim_vec ?Tv = n + m" 
    using v by auto
  have if_distrib: "\<And> x y z. (if x then y else (0 :: 'a)) * z = (if x then y * z else 0)" 
    by auto
  show "coeff ?l i = coeff ?r i"
  proof (cases "i < m+n")
    case False
      hence i_mn: "i \<ge> m+n"
        and i_n: "\<And>x. x \<le> i \<and> x < n \<longleftrightarrow> x < n"
        and i_m: "\<And>x. x \<le> i \<and> x < m \<longleftrightarrow> x < m" by auto
      have "coeff ?r i =
            (\<Sum> x < n. vec_first v n $ (n - Suc x) * coeff p (i - x)) +
            (\<Sum> x < m. vec_last v m $ (m - Suc x) * coeff q (i - x))"
        (is "_ = sum ?f _ + sum ?g _")
        unfolding coeff_add coeff_mult Let_def 
        unfolding coeff_poly_of_vec dim if_distrib
        unfolding atMost_def
        apply(subst sum.inter_filter[symmetric],simp)
        apply(subst sum.inter_filter[symmetric],simp)
        unfolding mem_Collect_eq
        unfolding i_n i_m
        unfolding lessThan_def by simp
      also { fix x assume x: "x < n"
        have "coeff p (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x m by auto
        hence "?f x = 0" by auto
      } hence "sum ?f {..<n} = 0" by auto
      also { fix x assume x: "x < m"
        have "coeff q (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x n by auto
        hence "?g x = 0" by auto
      } hence "sum ?g {..<m} = 0" by auto
      finally have "coeff ?r i = 0" by auto
      also from False have "0 = coeff ?l i"
        unfolding coeff_poly_of_vec dim sum.distrib[symmetric] by auto
      finally show ?thesis by auto
    next case True
      hence "coeff ?l i = ((sylvester_mat_sub m n p q)\<^sup>T *\<^sub>v v) $ (n + m - Suc i)"
        unfolding coeff_poly_of_vec dim sum.distrib[symmetric] by auto
      also have "... = coeff (p * poly_of_vec (vec_first v n) + q * poly_of_vec (vec_last v m)) i"
        apply(subst index_mult_mat_vec) using True apply simp
        apply(subst row_transpose) using True apply simp
        apply(subst col_sylvester_sub)
        using True apply simp
        apply(subst vec_first_last_append[of v n m,symmetric]) using v apply(simp add: add.commute)
        apply(subst scalar_prod_append)
        apply (rule carrier_vecI,simp)+
        apply (subst vec_of_poly_rev_shifted_scalar_prod[OF m],simp) using True apply simp
        apply (subst add.commute[of n m])
        apply (subst vec_of_poly_rev_shifted_scalar_prod[OF n]) apply simp using True apply simp
        by simp
      also have "... =
        (\<Sum>x\<le>i. (if x < n then vec_first v n $ (n - Suc x) else 0) * coeff p (i - x)) +
        (\<Sum>x\<le>i. (if x < m then vec_last v m $ (m - Suc x) else 0) * coeff q (i - x))"
        unfolding coeff_poly_of_vec[of "vec_first v n",unfolded dim_vec_first,symmetric]
        unfolding coeff_poly_of_vec[of "vec_last v m",unfolded dim_vec_last,symmetric]
        unfolding coeff_mult[symmetric] by (simp add: mult.commute)
      also have "... = coeff ?r i"
        unfolding coeff_add coeff_mult Let_def
        unfolding coeff_poly_of_vec dim..
      finally show ?thesis.
  qed
qed

(**** End of the lemmas which could be moved to Algebraic_Numbers/Resultant.thy ****)

(**** The following lemmas could be moved to Computational_Algebra/Polynomial.thy ****)

lemma normalize_field [simp]: "normalize (a :: 'a :: {field, semiring_gcd}) = (if a = 0 then 0 else 1)"
  using unit_factor_normalize by fastforce

lemma content_field [simp]: "content (p :: 'a :: {field,semiring_gcd} poly) = (if p = 0 then 0 else 1)"
  by (induct p, auto simp: content_def)

lemma primitive_part_field [simp]: "primitive_part (p :: 'a :: {field,semiring_gcd} poly) = p"
  by (cases "p = 0", auto intro!: primitive_part_prim)

lemma primitive_part_dvd: "primitive_part a dvd a"
  by (metis content_times_primitive_part dvd_def dvd_refl mult_smult_right)

lemma degree_abs [simp]:
  "degree \<bar>p\<bar> = degree p" by (auto simp: abs_poly_def)

lemma degree_gcd1:
  assumes a_not0: "a \<noteq> 0" 
  shows "degree (gcd a b) \<le> degree a"
proof -
  let ?g = "gcd a b"
  have gcd_dvd_b: "?g dvd a" by simp
  from this obtain c where a_gc: "a = ?g * c" unfolding dvd_def by auto
  have g_not0: "?g \<noteq>0" using a_not0 a_gc by auto
  have c0: "c \<noteq> 0" using a_not0 a_gc by auto
  have "degree ?g \<le> degree (?g * c)" by (rule degree_mult_right_le[OF c0])
  also have "... = degree a" using a_gc by auto
  finally show ?thesis .  
qed

lemma primitive_part_neg [simp]:
  fixes a::"'a :: factorial_ring_gcd poly"
  shows "primitive_part (-a) = - primitive_part a"
proof -
  have "primitive_part (-a) = primitive_part (smult (-1) a)" by auto
  then show ?thesis unfolding primitive_part_smult
    by (simp add: is_unit_unit_factor)
qed

lemma content_uminus[simp]: 
  fixes f::"int poly"
  shows "content (-f) = content f"
proof -
  have "-f = - (smult 1 f)" by auto
  also have "... = smult (-1) f" using smult_minus_left by auto
  finally have "content (-f) = content (smult (-1) f)" by auto
  also have "... = normalize (- 1) * content f" unfolding content_smult ..
  finally show ?thesis by auto  
qed

lemma pseudo_mod_monic:
  fixes f g :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  defines "r \<equiv> pseudo_mod f g"
  assumes monic_g: "monic g"
  shows "\<exists>q.  f = g * q + r" "r = 0 \<or> degree r < degree g"
proof -
  let ?cg = "coeff g (degree g)"
  let ?cge = "?cg ^ (Suc (degree f) - degree g)"
  define a where "a = ?cge"
  from r_def[unfolded pseudo_mod_def] obtain q where pdm: "pseudo_divmod f g = (q, r)"
    by (cases "pseudo_divmod f g") auto
  have g: "g \<noteq> 0" using monic_g by auto
  from pseudo_divmod[OF g pdm] have id: "smult a f = g * q + r" and "r = 0 \<or> degree r < degree g"
    by (auto simp: a_def)
  have a1: "a = 1" unfolding a_def using monic_g by auto
  hence id2: "f = g * q + r" using id by auto  
  show "r = 0 \<or> degree r < degree g" by fact  
  from g have "a \<noteq> 0"
    by (auto simp: a_def)  
  with id2 show "\<exists>q. f = g * q + r"
    by auto
qed

lemma monic_imp_div_mod_int_poly_degree: 
  fixes p :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  assumes m: "monic u"
  shows "\<exists>q r. p = q*u + r \<and> (r = 0 \<or> degree r < degree u)" 
  using pseudo_mod_monic[OF m] using mult.commute by metis

corollary monic_imp_div_mod_int_poly_degree2: 
  fixes p :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  assumes m: "monic u" and deg_u: "degree u > 0"
  shows "\<exists>q r. p = q*u + r \<and> (degree r < degree u)"
proof -  
  obtain q r where "p = q * u + r" and r: "(r = 0 \<or> degree r < degree u)" 
      using monic_imp_div_mod_int_poly_degree[OF m, of p] by auto
    moreover have "degree r < degree u" using deg_u r by auto  
  ultimately show ?thesis by auto
qed
(**** End of the lemmas that could be moved to Computational_Algebra/Polynomial.thy ****)

(**** Lemmas which could be moved to Berlekamp_Zassenhaus/Unique_Factorization.thy ****)
lemma irreducible_uminus [simp]:
  fixes a::"'a::idom"
  shows "irreducible (-a) \<longleftrightarrow> irreducible a"
  using irreducible_mult_unit_left[of "-1::'a"] by auto

(**** End of the lemmas could be part of Berlekamp_Zassenhaus/Unique_Factorization.thy ****)


(**** Lemmas that could be moved to Berlekamp_Zassenhaus/Poly_Mod.thy ****)

context poly_mod
begin

lemma dvd_imp_dvdm:
  assumes "a dvd b" shows "a dvdm b"
  by (metis assms dvd_def dvdm_def)

lemma dvdm_add:
  assumes a: "u dvdm a"
  and b: "u dvdm b"
  shows "u dvdm (a+b)"
proof -
  obtain a' where a: "a =m u*a'" using a unfolding dvdm_def by auto
  obtain b' where b: "b =m u*b'" using b unfolding dvdm_def by auto
  have "Mp (a + b) = Mp (u*a'+u*b')" using a b
    by (metis poly_mod.plus_Mp(1) poly_mod.plus_Mp(2))
  also have "... = Mp (u * (a'+ b'))"
    by (simp add: distrib_left)
  finally show ?thesis unfolding dvdm_def by auto
qed


lemma monic_dvdm_constant:
  assumes uk: "u dvdm [:k:]"
  and u1: "monic u" and u2: "degree u > 0" 
  shows "k mod m = 0"
proof -
  have d1: "degree_m [:k:] = degree [:k:]"    
    by (metis degree_pCons_0 le_zero_eq poly_mod.degree_m_le)
  obtain h where h: "Mp [:k:] = Mp (u * h)"
    using uk unfolding dvdm_def by auto
  have d2: "degree_m [:k:] = degree_m (u*h)" using h by metis
  have d3: "degree (map_poly M (u * map_poly M h)) = degree (u * map_poly M h)" 
    by (rule degree_map_poly)
       (metis coeff_degree_mult leading_coeff_0_iff mult.right_neutral M_M Mp_coeff Mp_def u1)
  thus ?thesis using assms d1 d2 d3
    by (auto, metis M_def map_poly_pCons degree_mult_right_le h leD map_poly_0 
        mult_poly_0_right pCons_eq_0_iff M_0 Mp_def mult_Mp(2)) 
qed

lemma dvdm_imp_div_mod:
  assumes "u dvdm g"
  shows "\<exists>q r. g = q*u + smult m r"
proof -
  obtain q where q: "Mp g = Mp (u*q)" 
    using assms unfolding dvdm_def by fast
  have "(u*q) = Mp (u*q) + smult m (Dp (u*q))"
    by (simp add: poly_mod.Dp_Mp_eq[of "u*q"])
  hence uq: "Mp (u*q) = (u*q) - smult m (Dp (u*q))"
    by auto  
  have g: "g = Mp g + smult m (Dp g)"
    by (simp add: poly_mod.Dp_Mp_eq[of "g"])
  also have "... = poly_mod.Mp m (u*q) + smult m (Dp g)" using q by simp
  also have "... = u * q - smult m (Dp (u * q)) + smult m (Dp g)" 
    unfolding uq by auto
  also have "... = u * q + smult m (-Dp (u*q)) + smult m (Dp g)" by auto  
  also have "... = u * q + smult m (-Dp (u*q) + Dp g)" 
    unfolding smult_add_right by auto
  also have "... = q * u + smult m (-Dp (u*q) + Dp g)" by auto
  finally show ?thesis by auto
qed

lemma div_mod_imp_dvdm:
  assumes "\<exists>q r. b = q * a + Polynomial.smult m r"
  shows "a dvdm b"
proof -
  from assms  obtain q r where b:"b = a * q + smult m r"
    by (metis mult.commute)
  have a: "Mp (Polynomial.smult m r) = 0" by auto
  show ?thesis 
  proof (unfold dvdm_def, rule exI[of _ q])
    have "Mp (a * q + smult m r) = Mp (a * q + Mp (smult m r))" 
      using plus_Mp(2)[of "a*q" "smult m r"] by auto
    also have "... = Mp (a*q)" by auto
    finally show "eq_m b (a * q)" using b by auto
  qed
qed

corollary div_mod_iff_dvdm:
  shows "a dvdm b = (\<exists>q r. b = q * a + Polynomial.smult m r)"
  using div_mod_imp_dvdm dvdm_imp_div_mod by blast

lemma dvdmE:
  assumes "p dvdm q" and "\<And>r. q =m p * Mp r \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: dvdm_def)

lemma lead_coeff_monic_mult:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "monic p" shows "lead_coeff (p * q) = lead_coeff q"
  using assms by (simp add: lead_coeff_mult)

lemma degree_m_mult_eq:
  assumes p: "monic p" and q: "lead_coeff q mod m \<noteq> 0" and m1: "m > 1"
  shows "degree (Mp (p * q)) = degree p + degree q"
proof-
  have "lead_coeff (p * q) mod m \<noteq> 0"
    using q p by (auto simp: lead_coeff_monic_mult)
  with m1 show ?thesis
    by (auto simp: degree_m_eq intro!: degree_mult_eq)
qed

lemma dvdm_imp_degree_le:
  assumes pq: "p dvdm q" and p: "monic p" and q0: "Mp q \<noteq> 0" and m1: "m > 1"
  shows "degree p \<le> degree q"
proof-
  from q0
  have q: "lead_coeff (Mp q) mod m \<noteq> 0"
    by (metis Mp_Mp Mp_coeff leading_coeff_neq_0 M_def)
  from pq obtain r where Mpq: "Mp q = Mp (p * Mp r)" by (auto elim: dvdmE)
  with p q have "lead_coeff (Mp r) mod m \<noteq> 0"
    by (metis Mp_Mp Mp_coeff leading_coeff_0_iff mult_poly_0_right M_def)
  from degree_m_mult_eq[OF p this m1] Mpq
  have "degree p \<le> degree_m q" by simp
  thus ?thesis using degree_m_le le_trans by blast
qed

lemma dvdm_uminus [simp]:
  "p dvdm -q \<longleftrightarrow> p dvdm q"
  by (metis add.inverse_inverse dvdm_smult smult_1_left smult_minus_left)


(*TODO: simp?*)
lemma Mp_const_poly: "Mp [:a:] = [:a mod m:]"   
  by (simp add: Mp_def M_def Polynomial.map_poly_pCons)

end

context poly_mod_2
begin
lemma factorization_m_mem_dvdm: assumes fact: "factorization_m f (c,fs)" 
  and mem: "Mp g \<in># image_mset Mp fs" 
shows "g dvdm f" 
proof - 
  from fact have "factorization_m f (Mf (c, fs))" by auto
  then obtain l where f: "factorization_m f (l, image_mset Mp fs)" by (auto simp: Mf_def)
  from multi_member_split[OF mem] obtain ls where 
    fs: "image_mset Mp fs = {# Mp g #} + ls" by auto
  from f[unfolded fs split factorization_m_def] show "g dvdm f" 
    unfolding dvdm_def
    by (intro exI[of _ "smult l (prod_mset ls)"], auto simp del: Mp_smult 
        simp add: Mp_smult(2)[of _ "Mp g * prod_mset ls", symmetric], simp)
qed

lemma dvdm_degree: "monic u \<Longrightarrow> u dvdm f \<Longrightarrow> Mp f \<noteq> 0 \<Longrightarrow> degree u \<le> degree f"
  using dvdm_imp_degree_le m1 by blast
end

context poly_mod_prime
begin
lemma pl_dvdm_imp_p_dvdm:
  assumes l0: "l \<noteq> 0" 
  and pl_dvdm: "poly_mod.dvdm (p^l) a b"
  shows "a dvdm b"
proof -
  from l0 have l_gt_0: "l > 0" by auto
  with m1 interpret pl: poly_mod_2 "p^l" by (unfold_locales, auto)
  have p_rw: "p * p ^ (l - 1) = p ^ l" by (rule power_minus_simp[symmetric, OF l_gt_0])
  obtain q r where b: "b = q * a + smult (p^l) r" using pl.dvdm_imp_div_mod[OF pl_dvdm] by auto
  have "smult (p^l) r = smult p (smult (p ^ (l - 1)) r)" unfolding smult_smult p_rw ..
  hence b2: "b = q * a + smult p (smult (p ^ (l - 1)) r)" using b by auto
  show ?thesis
    by (rule div_mod_imp_dvdm, rule exI[of _ q], 
        rule exI[of _ "(smult (p ^ (l - 1)) r)"], auto simp add: b2)
qed

lemma coprime_exp_mod: "coprime lu p \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> lu mod p ^ n \<noteq> 0" 
  using prime by fastforce

(**** End of the lemmas that could be moved to Berlekamp_Zassenhaus/Poly_Mod.thy ****)

(**** Lemmas that could be moved to Berlekamp_Zassenhaus/Berlekamp_Hensel.thy ****)

lemma unique_factorization_m_factor_partition: assumes l0: "l \<noteq> 0" 
  and uf: "poly_mod.unique_factorization_m (p^l) f (lead_coeff f, mset gs)" 
  and f: "f = f1 * f2" 
  and cop: "coprime (lead_coeff f) p" 
  and sf: "square_free_m f" 
  and part: "partition (\<lambda>gi. gi dvdm f1) gs = (gs1, gs2)" 
shows "poly_mod.unique_factorization_m (p^l) f1 (lead_coeff f1, mset gs1)"
  "poly_mod.unique_factorization_m (p^l) f2 (lead_coeff f2, mset gs2)"
proof -
  interpret pl: poly_mod_2 "p^l" by (standard, insert m1 l0, auto)
  let ?I = "image_mset pl.Mp" 
  note Mp_pow [simp] = Mp_Mp_pow_is_Mp[OF l0 m1]
  have [simp]: "pl.Mp x dvdm u = (x dvdm u)" for x u unfolding dvdm_def using Mp_pow[of x]
    by (metis poly_mod.mult_Mp(1))
  have gs_split: "set gs = set gs1 \<union> set gs2" using part by auto
  from pl.unique_factorization_m_factor[OF prime uf[unfolded f] _ _ l0 refl, folded f, OF cop sf]
  obtain hs1 hs2 where uf': "pl.unique_factorization_m f1 (lead_coeff f1, hs1)" 
      "pl.unique_factorization_m f2 (lead_coeff f2, hs2)"
    and gs_hs: "?I (mset gs) = hs1 + hs2"
    unfolding pl.Mf_def split by auto
  have gs_gs: "?I (mset gs) = ?I (mset gs1) + ?I (mset gs2)" using part 
    by (auto, induct gs arbitrary: gs1 gs2, auto)
  with gs_hs have gs_hs12: "?I (mset gs1) + ?I (mset gs2) = hs1 + hs2" by auto
  note pl_dvdm_imp_p_dvdm = pl_dvdm_imp_p_dvdm[OF l0]
  note fact = pl.unique_factorization_m_imp_factorization[OF uf]
  have gs1: "?I (mset gs1) = {#x \<in># ?I (mset gs). x dvdm f1#}"
    using part by (auto, induct gs arbitrary: gs1 gs2, auto)
  also have "\<dots> = {#x \<in># hs1. x dvdm f1#} + {#x \<in># hs2. x dvdm f1#}" unfolding gs_hs by simp
  also have "{#x \<in># hs2. x dvdm f1#} = {#}" 
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    then obtain x where x: "x \<in># hs2" and dvd: "x dvdm f1" by fastforce
    from x gs_hs have "x \<in># ?I (mset gs)" by auto
    with fact[unfolded pl.factorization_m_def]
    have xx: "pl.irreducible\<^sub>d_m x" "monic x" by auto
    from square_free_m_prod_imp_coprime_m[OF sf[unfolded f]] 
    have cop_h_f: "coprime_m f1 f2" by auto  
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf'(2)], of x] x 
    have "pl.dvdm x f2" by auto
    hence "x dvdm f2" by (rule pl_dvdm_imp_p_dvdm)
    from cop_h_f[unfolded coprime_m_def, rule_format, OF dvd this] 
    have "x dvdm 1" by auto
    from dvdm_imp_degree_le[OF this xx(2) _ m1] have "degree x = 0" by auto
    with xx show False unfolding pl.irreducible\<^sub>d_m_def by auto
  qed
  also have "{#x \<in># hs1. x dvdm f1#} = hs1"
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    from filter_mset_inequality[OF this]
    obtain x where x: "x \<in># hs1" and dvd: "\<not> x dvdm f1" by blast
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf'(1)], 
      of x] x dvd 
    have "pl.dvdm x f1" by auto
    from pl_dvdm_imp_p_dvdm[OF this] dvd show False by auto
  qed
  finally have gs_hs1: "?I (mset gs1) = hs1" by simp
  with gs_hs12 have "?I (mset gs2) = hs2" by auto
  with uf' gs_hs1 have "pl.unique_factorization_m f1 (lead_coeff f1, ?I (mset gs1))"
     "pl.unique_factorization_m f2 (lead_coeff f2, ?I (mset gs2))" by auto
  thus "pl.unique_factorization_m f1 (lead_coeff f1, mset gs1)"
     "pl.unique_factorization_m f2 (lead_coeff f2, mset gs2)"
    unfolding pl.unique_factorization_m_def 
    by (auto simp: pl.Mf_def image_mset.compositionality o_def)
qed
end


(**** End of the lemmas that could be moved to Berlekamp_Zassenhaus/Berlekamp_Hensel.thy ****)

(**** Lemmas that could be moved to Jordan_Normal_Form/Missing_VectorSpace.thy 
      (or to VectorSpace/LinearCombinations.thy) ****)

definition find_indices where "find_indices x xs \<equiv> [i \<leftarrow> [0..<length xs]. xs!i = x]"

lemma find_indices_Nil [simp]:
  "find_indices x [] = []"
  by (simp add: find_indices_def)

lemma find_indices_Cons:
  "find_indices x (y#ys) = (if x = y then Cons 0 else id) (map Suc (find_indices x ys))"
apply (unfold find_indices_def length_Cons, subst upt_conv_Cons, simp)
apply (fold map_Suc_upt, auto simp: filter_map o_def) done

lemma find_indices_snoc [simp]:
  "find_indices x (ys@[y]) = find_indices x ys @ (if x = y then [length ys] else [])"
  by (unfold find_indices_def, auto intro!: filter_cong simp: nth_append)

lemma mem_set_find_indices [simp]: "i \<in> set (find_indices x xs) \<longleftrightarrow> i < length xs \<and> xs!i = x"
  by (auto simp: find_indices_def)

lemma distinct_find_indices: "distinct (find_indices x xs)"
  unfolding find_indices_def by simp 

context Module.module begin

definition lincomb_list
where "lincomb_list c vs = sumlist (map (\<lambda>i. c i \<odot>\<^bsub>M\<^esub> vs ! i) [0..<length vs])"

lemma lincomb_list_carrier:
  assumes "set vs \<subseteq> carrier M" and "c : {0..<length vs} \<rightarrow> carrier R"
  shows "lincomb_list c vs \<in> carrier M"
  by (insert assms, unfold lincomb_list_def, intro sumlist_carrier, auto intro!: smult_closed)

lemma lincomb_list_Nil [simp]: "lincomb_list c [] = \<zero>\<^bsub>M\<^esub>"
  by (simp add: lincomb_list_def)

lemma lincomb_list_Cons [simp]:
  "lincomb_list c (v#vs) = c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb_list (c o Suc) vs"
  by (unfold lincomb_list_def length_Cons, subst upt_conv_Cons, simp, fold map_Suc_upt, simp add: o_def)

lemma lincomb_list_eq_0:
  assumes "\<And>i. i < length vs \<Longrightarrow> c i \<odot>\<^bsub>M\<^esub> vs ! i = \<zero>\<^bsub>M\<^esub>"
  shows "lincomb_list c vs = \<zero>\<^bsub>M\<^esub>"
proof (insert assms, induct vs arbitrary:c)
  case (Cons v vs)
  from Cons.prems[of 0] have [simp]: "c 0 \<odot>\<^bsub>M\<^esub> v = \<zero>\<^bsub>M\<^esub>" by auto
  from Cons.prems[of "Suc _"] Cons.hyps have "lincomb_list (c \<circ> Suc) vs = \<zero>\<^bsub>M\<^esub>" by auto
  then show ?case by (simp add: o_def)
qed simp

definition mk_coeff where "mk_coeff vs c v \<equiv> R.sumlist (map c (find_indices v vs))"

lemma mk_coeff_carrier:
  assumes "c : {0..<length vs} \<rightarrow> carrier R" shows "mk_coeff vs c w \<in> carrier R"
  by (insert assms, auto simp: mk_coeff_def find_indices_def intro!:R.sumlist_carrier elim!:funcset_mem)

lemma mk_coeff_Cons:
  assumes "c : {0..<length (v#vs)} \<rightarrow> carrier R"
  shows "mk_coeff (v#vs) c = (\<lambda>w. (if w = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c o Suc) w)"
proof-
  from assms have "c o Suc : {0..<length vs} \<rightarrow> carrier R" by auto
  from mk_coeff_carrier[OF this] assms
  show ?thesis by (auto simp add: mk_coeff_def find_indices_Cons)
qed

lemma mk_coeff_0[simp]:
  assumes "v \<notin> set vs"
  shows "mk_coeff vs c v = \<zero>"
proof -
  have "(find_indices v vs) = []" using assms unfolding find_indices_def
    by (simp add: in_set_conv_nth)
  thus ?thesis  unfolding mk_coeff_def by auto
qed  

lemma lincomb_list_as_lincomb:
  assumes vs_M: "set vs \<subseteq> carrier M" and c: "c : {0..<length vs} \<rightarrow> carrier R"
  shows "lincomb_list c vs = lincomb (mk_coeff vs c) (set vs)"
proof (insert assms, induct vs arbitrary: c)
  case (Cons v vs)
  have mk_coeff_Suc_closed: "mk_coeff vs (c \<circ> Suc) a \<in> carrier R" for a
    apply (rule mk_coeff_carrier)
    using Cons.prems unfolding Pi_def by auto
  have x_in: "x \<in> carrier M" if x: "x\<in> set vs" for x using Cons.prems x by auto
  show ?case apply (unfold mk_coeff_Cons[OF Cons.prems(2)] lincomb_list_Cons)
    apply (subst Cons) using Cons apply (force, force)
  proof (cases "v \<in> set vs", auto simp:insert_absorb)
    case False
    let ?f = "(\<lambda>va. ((if va = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va)"
    have mk_0: "mk_coeff vs (c \<circ> Suc) v = \<zero>" using False by auto
    have [simp]: "(c 0 \<oplus> \<zero>) = c 0"
      using Cons.prems(2) by force
    have finsum_rw: "(\<Oplus>\<^bsub>M\<^esub>va\<in>insert v (set vs). ?f va) = (?f v) \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs). ?f va)"
    proof (rule finsum_insert, auto simp add: False, rule smult_closed, rule R.a_closed)
      fix x
      show "mk_coeff vs (c \<circ> Suc) x \<in> carrier R" 
        using mk_coeff_Suc_closed by auto
      show "c 0 \<odot>\<^bsub>M\<^esub> v \<in> carrier M"
      proof (rule smult_closed)
        show "c 0 \<in> carrier R"
          using Cons.prems(2) by fastforce
        show "v \<in> carrier M"
          using Cons.prems(1) by auto
      qed
      show "\<zero> \<in> carrier R"
        by simp
      assume x: "x \<in> set vs" show "x \<in> carrier M"
        using Cons.prems(1) x by auto
    qed
    have finsum_rw2: 
      "(\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs). ?f va) = (\<Oplus>\<^bsub>M\<^esub>va\<in>set vs. (mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va)"
    proof (rule finsum_cong2, auto simp add: False)
      fix i assume i: "i \<in> set vs"
      have "c \<circ> Suc \<in> {0..<length vs} \<rightarrow> carrier R" using Cons.prems by auto
      then have [simp]: "mk_coeff vs (c \<circ> Suc) i \<in> carrier R" 
        using mk_coeff_Suc_closed by auto
      have "\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) i = mk_coeff vs (c \<circ> Suc) i" by (rule R.l_zero, simp)
      then show "(\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) i) \<odot>\<^bsub>M\<^esub> i = mk_coeff vs (c \<circ> Suc) i \<odot>\<^bsub>M\<^esub> i" 
        by auto
      show "(\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) i) \<odot>\<^bsub>M\<^esub> i \<in> carrier M"
        using Cons.prems(1) i by auto
    qed
    show "c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb (mk_coeff vs (c \<circ> Suc)) (set vs) =
    lincomb (\<lambda>a. (if a = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) a) (insert v (set vs))" 
      unfolding lincomb_def
      unfolding finsum_rw mk_0 
      unfolding finsum_rw2 by auto
  next
    case True
    let ?f = "\<lambda>va. ((if va = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va"
    have rw: "(c 0 \<oplus> mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v 
      = (c 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v"      
      using Cons.prems(1) Cons.prems(2) atLeast0_lessThan_Suc_eq_insert_0 
      using mk_coeff_Suc_closed smult_l_distr by auto
    have rw2: "((mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va) = (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
    proof -
      have "(\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va) = (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs - {v}. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
        by (rule finsum_cong2, unfold Pi_def, auto simp add: mk_coeff_Suc_closed x_in)
      moreover have "(\<Oplus>\<^bsub>M\<^esub>v\<in>set vs. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v) = ((mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
        \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs - {v}. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
        by (rule M.add.finprod_split, auto simp add: mk_coeff_Suc_closed True x_in)
      ultimately show ?thesis by auto
    qed
    have "lincomb (\<lambda>a. (if a = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) a) (set vs) 
      = (\<Oplus>\<^bsub>M\<^esub>va\<in>set vs. ?f va)" unfolding lincomb_def ..
    also have "... = ?f v \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va)"
    proof (rule M.add.finprod_split)
      have c0_mkcoeff_in: "c 0 \<oplus> mk_coeff vs (c \<circ> Suc) v \<in> carrier R" 
      proof (rule R.a_closed)
        show "c 0 \<in> carrier R " using Cons.prems by auto
        show "mk_coeff vs (c \<circ> Suc) v \<in> carrier R"
          using mk_coeff_Suc_closed by auto
    qed
    moreover have "(\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va \<in> carrier M"
      if va: "va \<in> carrier M" for va 
      by (rule smult_closed[OF _ va], rule R.a_closed, auto simp add: mk_coeff_Suc_closed)
    ultimately show "?f ` set vs \<subseteq> carrier M" using Cons.prems(1) by auto        
      show "finite (set vs)" by simp
      show "v \<in> set vs" using True by simp
    qed
    also have "... = (c 0 \<oplus> mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va)" by auto
    also have "... = ((c 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va)" unfolding rw by simp
    also have "... = (c 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (((mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va))"
    proof (rule M.a_assoc)
      show "c 0 \<odot>\<^bsub>M\<^esub> v \<in> carrier M" 
        using Cons.prems(1) Cons.prems(2) by auto
      show "mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v \<in> carrier M"
        using Cons.prems(1) mk_coeff_Suc_closed by auto
      show "(\<Oplus>\<^bsub>M\<^esub>va\<in>set vs - {v}. ((if va = v then c 0 else \<zero>) 
        \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va) \<in> carrier M"
        by (rule M.add.finprod_closed) (auto simp add: mk_coeff_Suc_closed x_in)
    qed
    also have "... = c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
      unfolding rw2 ..
    also have "... = c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb (mk_coeff vs (c \<circ> Suc)) (set vs)" 
      unfolding lincomb_def ..
    finally show "c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb (mk_coeff vs (c \<circ> Suc)) (set vs) 
      = lincomb (\<lambda>a. (if a = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) a) (set vs)" ..         
  qed
qed simp

definition "span_list vs \<equiv> {lincomb_list c vs | c. c : {0..<length vs} \<rightarrow> carrier R}"

lemma in_span_listI:
  assumes "c : {0..<length vs} \<rightarrow> carrier R" and "v = lincomb_list c vs"
  shows "v \<in> span_list vs"
  using assms by (auto simp: span_list_def)

lemma in_span_listE:
  assumes "v \<in> span_list vs"
      and "\<And>c. c : {0..<length vs} \<rightarrow> carrier R \<Longrightarrow> v = lincomb_list c vs \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: span_list_def)

lemmas lincomb_insert2 = lincomb_insert[unfolded insert_union[symmetric]]

lemma lincomb_zero:
  assumes U: "U \<subseteq> carrier M" and a: "a : U \<rightarrow> {zero R}"
  shows "lincomb a U = zero M"
  using U a
proof (induct U rule: infinite_finite_induct)
  case empty show ?case unfolding lincomb_def by auto next
  case (insert u U)
    hence "a \<in> insert u U \<rightarrow> carrier R" using zero_closed by force
    thus ?case using insert by (subst lincomb_insert2; auto)
qed (auto simp: lincomb_def)

end

(**** End of lemmas that could be moved to Jordan_Normal_Form/Missing_VectorSpace.thy 
      (or to VectorSpace/LinearCombinations.thy) ****)

(**** Lemmas that could be moved to Jordan_Normal_Form/VS_Connect.thy  ****)
context vec_module
begin

lemma lincomb_list_as_mat_mult:
  assumes "\<forall>w \<in> set ws. dim_vec w = n"
  shows "lincomb_list c ws = mat_of_cols n ws *\<^sub>v vec (length ws) c" (is "?l ws c = ?r ws c")
proof (insert assms, induct ws arbitrary: c)
  case Nil
  then show ?case by (auto simp: mult_mat_vec_def scalar_prod_def)
next
  case (Cons w ws)
  { fix i assume i: "i < n"
    have "?l (w#ws) c = c 0 \<cdot>\<^sub>v w + mat_of_cols n ws *\<^sub>v vec (length ws) (c \<circ> Suc)"
      by (simp add: Cons o_def)
    also have "\<dots> $ i = ?r (w#ws) c $ i"
      using Cons i index_smult_vec
      by (simp add: mat_of_cols_Cons_index_0 mat_of_cols_Cons_index_Suc o_def vec_Suc mult_mat_vec_def row_def length_Cons)
    finally have "?l (w#ws) c $ i = \<dots>".
  }
  with Cons show ?case by (intro eq_vecI, auto)
qed

lemma lincomb_union2:
    assumes A: "A \<subseteq> carrier_vec n"
    and BA: "B \<subseteq> A" and fin_A: "finite A" 
    and f: "f \<in> A \<rightarrow> UNIV" shows "lincomb f A = lincomb f (A-B) + lincomb f B"
proof -
  have "A - B \<union> B = A" using BA by auto
  hence "lincomb f A = lincomb f (A - B \<union> B)"  by simp
  also have "... = lincomb f (A-B) + lincomb f B"
    by (rule lincomb_union, insert assms, auto intro: finite_subset)
  finally show ?thesis .
qed

lemma dim_sumlist:
  assumes "\<forall>x\<in>set xs. dim_vec x = n"
  shows "dim_vec (M.sumlist xs) = n" using assms by (induct xs, auto)

lemma sumlist_nth:
  assumes "\<forall>x\<in>set xs. dim_vec x = n" and "i<n"
  shows "(M.sumlist xs) $ i= sum (\<lambda>j. (xs ! j) $ i) {0..<length xs}"
  using assms
proof (induct xs rule: rev_induct)
  case (snoc a xs) 
  have [simp]: "x \<in> carrier_vec n" if x: "x\<in>set xs" for x 
    using snoc.prems x unfolding carrier_vec_def by auto
  have [simp]: "a \<in> carrier_vec n" 
    using snoc.prems unfolding carrier_vec_def by auto
  have hyp: "M.sumlist xs $ i = (\<Sum>j = 0..<length xs. xs ! j $ i)" 
    by (rule snoc.hyps, auto simp add: snoc.prems)  
  have "M.sumlist (xs @ [a]) = M.sumlist xs + M.sumlist [a]" 
    by (rule M.sumlist_append, auto simp add: snoc.prems)
  also have "... = M.sumlist xs + a" by auto
  also have "... $ i = (M.sumlist xs $ i) + (a $ i)" 
    by (rule index_add_vec(1), auto simp add: snoc.prems)
  also have "... =  (\<Sum>j = 0..<length xs. xs ! j $ i) + (a $ i)" unfolding hyp by simp
  also have "... = (\<Sum>j = 0..<length (xs @ [a]). (xs @ [a]) ! j $ i)"
    by (auto, rule sum.cong, auto simp add: nth_append)     
  finally show ?case .
qed auto

lemma lincomb_as_lincomb_list_distinct:
  assumes s: "set ws \<subseteq> carrier_vec n" and d: "distinct ws"
  shows "lincomb f (set ws) = lincomb_list (\<lambda>i. f (ws ! i)) ws"
proof (insert assms, induct ws)
  case Nil
  then show ?case by auto
next
  case (Cons a ws)
  have [simp]: "\<And>v. v \<in> set ws \<Longrightarrow> v \<in> carrier_vec n" using Cons.prems(1) by auto
  then have ws: "set ws \<subseteq> carrier_vec n" by auto
  have hyp: "lincomb f (set (ws)) = lincomb_list (\<lambda>i. f (ws ! i)) ws"
  proof (intro Cons.hyps ws)
    show "distinct ws" using Cons.prems(2) by auto
  qed  
  have "(map (\<lambda>i. f (ws ! i) \<cdot>\<^sub>v ws ! i) [0..<length ws]) = (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)"
    by (simp add: nth_map_conv)
  with ws have sumlist_rw: "sumlist (map (\<lambda>i. f (ws ! i) \<cdot>\<^sub>v ws ! i) [0..<length ws])
    = sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)"
    by (subst (1 2) sumlist_as_summset, auto)
  have "lincomb f (set (a # ws)) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set (a # ws). f v \<cdot>\<^sub>v v)" unfolding lincomb_def ..
  also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in> insert a (set ws). f v \<cdot>\<^sub>v v)" by simp
  also have "... = (f a \<cdot>\<^sub>v a) + (\<Oplus>\<^bsub>V\<^esub>v\<in> (set ws). f v \<cdot>\<^sub>v v)"
    by (rule finsum_insert, insert Cons.prems, auto)
  also have "... = f a \<cdot>\<^sub>v a + lincomb_list (\<lambda>i. f (ws ! i)) ws" using hyp lincomb_def by auto
  also have "... = f a \<cdot>\<^sub>v a + sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)" 
    unfolding lincomb_list_def sumlist_rw by auto
  also have "... = sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) (a # ws))"
  proof -
    let ?a = "(map (\<lambda>v. f v \<cdot>\<^sub>v v) [a])"
    have a: "a \<in> carrier_vec n" using Cons.prems(1) by auto
    have "f a \<cdot>\<^sub>v a = sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) [a])" using Cons.prems(1) by auto
    hence "f a \<cdot>\<^sub>v a + sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws) 
      = sumlist ?a + sumlist (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws)" by simp
    also have "... = sumlist (?a @ (map (\<lambda>v. f v \<cdot>\<^sub>v v) ws))"
      by (rule sumlist_append[symmetric], auto simp add: a)
    finally show ?thesis by auto
  qed
  also have "... = sumlist (map (\<lambda>i. f ((a # ws) ! i) \<cdot>\<^sub>v (a # ws) ! i) [0..<length (a # ws)])"
  proof -
    have u: "(map (\<lambda>i. f ((a # ws) ! i) \<cdot>\<^sub>v (a # ws) ! i) [0..<length (a # ws)]) 
        = (map (\<lambda>v. f v \<cdot>\<^sub>v v) (a # ws))"
    proof (rule nth_map_conv)
      show "length [0..<length (a # ws)] = length (a # ws)" by auto
      show "\<forall>i<length [0..<length (a # ws)]. f ((a # ws) ! ([0..<length (a # ws)] ! i)) \<cdot>\<^sub>v (a # ws) !
          ([0..<length (a # ws)] ! i) = f ((a # ws) ! i) \<cdot>\<^sub>v (a # ws) ! i"
        by (metis \<open>length [0..<length (a # ws)] = length (a # ws)\<close> add.left_neutral nth_upt)
    qed
    show ?thesis unfolding u ..
  qed
  also have "... = lincomb_list (\<lambda>i. f ((a # ws) ! i)) (a # ws)"
    unfolding lincomb_list_def ..
  finally show ?case .
qed

end

locale idom_vec = vec_module f_ty for f_ty :: "'a :: idom itself"
begin

lemma lin_dep_cols_imp_det_0':
  fixes ws
  defines "A \<equiv> mat_of_cols n ws"
  assumes dimv_ws: "\<forall>w\<in>set ws. dim_vec w = n"
  assumes A: "A \<in> carrier_mat n n" and ld_cols: "lin_dep (set (cols A))"
  shows  "det A = 0"
proof (cases "distinct ws")
  case False
  obtain i j where ij: "i\<noteq>j" and c: "col A i = col A j" and i: "i<n" and j: "j<n" 
    using False A unfolding A_def
    by (metis dimv_ws distinct_conv_nth carrier_matD(2) 
        col_mat_of_cols mat_of_cols_carrier(3) nth_mem carrier_vecI)
  show ?thesis by (rule det_identical_columns[OF A ij i j c])  
next
  case True
  have d1[simp]: "\<And>x. x \<in> set ws \<Longrightarrow> x \<in> carrier_vec n" using dimv_ws by auto 
  obtain A' f' v where f'_in: "f' \<in> A' \<rightarrow> UNIV" 
    and lc_f': "lincomb f' A' = 0\<^sub>v n" and f'_v: "f' v \<noteq> 0"
    and v_A': "v \<in> A'" and A'_in_rows: "A' \<subseteq> set (cols A)" 
    using ld_cols unfolding lin_dep_def by auto
  define f where "f \<equiv> \<lambda>x. if x \<notin> A' then 0 else f' x"
  have f_in: "f \<in> (set (cols A)) \<rightarrow> UNIV" using f'_in by auto
  have A'_in_carrier: "A' \<subseteq> carrier_vec n"
    by (metis (no_types) A'_in_rows A_def cols_dim carrier_matD(1) mat_of_cols_carrier(1) subset_trans)
  have lc_f: "lincomb f (set (cols A)) = 0\<^sub>v n"   
  proof -
    have l1: "lincomb f (set (cols A) - A') = 0\<^sub>v n"
      by (rule lincomb_zero, auto simp add: f_def, insert A cols_dim, blast)
    have l2: "lincomb f A' = 0\<^sub>v n " using lc_f' unfolding f_def using A'_in_carrier by auto
    have "lincomb f (set (cols A)) = lincomb f (set (cols A) - A') + lincomb f A'"
    proof (rule lincomb_union2 )
      show "set (cols A) \<subseteq> carrier_vec n"
        using A cols_dim by blast
      show "A' \<subseteq> set (cols A)"
        using A'_in_rows by blast
      show "finite (set (cols A))" by auto
      show "f \<in> set (cols A) \<rightarrow> UNIV" by auto     
    qed 
    also have "... =  0\<^sub>v n" using l1 l2 by auto
    finally show ?thesis .
  qed
  have v_in: "v \<in> (set (cols A))" using v_A' A'_in_rows by auto 
  have fv: "f v \<noteq> 0" using f'_v v_A' unfolding f_def by auto
  let ?c = "(\<lambda>i. f (ws ! i))"
  have "lincomb f (set ws) = lincomb_list ?c ws"
    by (rule lincomb_as_lincomb_list_distinct[OF _ True], auto)
  have "\<exists>v.  v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> A *\<^sub>v v = 0\<^sub>v n"
  proof (rule exI[of _ " vec (length ws) ?c"], rule conjI)
    show "vec (length ws) ?c \<in> carrier_vec n" using A A_def by auto
    have vec_not0: "vec (length ws) ?c \<noteq> 0\<^sub>v n"
    proof -
      obtain i where ws_i: "(ws ! i) = v" and i: "i<length ws" using v_in unfolding A_def        
        by (metis d1 cols_mat_of_cols in_set_conv_nth subset_eq)
      have "vec (length ws) ?c $ i = ?c i" by (rule index_vec[OF i])
      also have "... = f v" using ws_i by simp
      also have "... \<noteq> 0" using fv by simp
      finally show ?thesis
        using A A_def i by fastforce
    qed
    have "A *\<^sub>v vec (length ws) ?c = mat_of_cols n ws *\<^sub>v vec (length ws) ?c" unfolding A_def ..
    also have "... = lincomb_list ?c ws" by (rule lincomb_list_as_mat_mult[symmetric, OF dimv_ws])
    also have "... = lincomb f (set ws)" 
      by (rule lincomb_as_lincomb_list_distinct[symmetric, OF _ True], auto)
    also have "... =  0\<^sub>v n" 
      using lc_f unfolding A_def using A by (simp add: subset_code(1))
    finally show "vec (length ws) (\<lambda>i. f (ws ! i)) \<noteq> 0\<^sub>v n \<and> A *\<^sub>v vec (length ws) (\<lambda>i. f (ws ! i)) = 0\<^sub>v n"
      using vec_not0 by fast
  qed 
  thus ?thesis unfolding det_0_iff_vec_prod_zero[OF A] .
qed

lemma lin_dep_cols_imp_det_0:
  assumes A: "A \<in> carrier_mat n n" and ld: "lin_dep (set (cols A))"
  shows "det A = 0" 
proof -
  have col_rw: "(cols (mat_of_cols n (cols A))) = cols A"
    using A by auto
  have m: "mat_of_cols n (cols A) = A" using A by auto
  show ?thesis
  by (rule A lin_dep_cols_imp_det_0'[of "cols A", unfolded col_rw, unfolded m, OF _ A ld])
     (metis A cols_dim carrier_matD(1) subsetCE carrier_vecD)
qed

corollary lin_dep_rows_imp_det_0:
  assumes A: "A \<in> carrier_mat n n" and ld: "lin_dep (set (rows A))"
  shows "det A = 0" 
  by (subst det_transpose[OF A, symmetric], rule lin_dep_cols_imp_det_0, auto simp add: ld A)

lemma det_not_0_imp_lin_indpt_rows:
  assumes A: "A \<in> carrier_mat n n" and det: "det A \<noteq> 0"  
  shows "lin_indpt (set (rows A))"
    using lin_dep_rows_imp_det_0[OF A] det by auto

lemma upper_triangular_imp_lin_indpt_rows:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "lin_indpt (set (rows A))"
  using det_not_0_imp_lin_indpt_rows upper_triangular_imp_det_eq_0_iff assms
  by auto

(* Connection from set-based to list-based *)

lemma lincomb_as_lincomb_list:
  fixes ws f
  assumes s: "set ws \<subseteq> carrier_vec n"
  shows "lincomb f (set ws) = lincomb_list (\<lambda>i. if \<exists>j<i. ws!i = ws!j then 0 else f (ws ! i)) ws"
  using assms
proof (induct ws rule: rev_induct)
  case (snoc a ws)
  let ?f = "\<lambda>i. if \<exists>j<i. ws ! i = ws ! j then 0 else f (ws ! i)"
  let ?g = "\<lambda>i. (if \<exists>j<i. (ws @ [a]) ! i = (ws @ [a]) ! j then 0 else f ((ws @ [a]) ! i)) \<cdot>\<^sub>v (ws @ [a]) ! i"
  let ?g2= "(\<lambda>i. (if \<exists>j<i. ws ! i = ws ! j then 0 else f (ws ! i)) \<cdot>\<^sub>v ws ! i)"
  have [simp]: "\<And>v. v \<in> set ws \<Longrightarrow> v \<in> carrier_vec n" using snoc.prems(1) by auto
  then have ws: "set ws \<subseteq> carrier_vec n" by auto
  have hyp: "lincomb f (set ws) = lincomb_list ?f ws"
    by (intro snoc.hyps ws)  
  show ?case
  proof (cases "a\<in>set ws")
    case True    
    have g_length: "?g (length ws) = 0\<^sub>v n" using True
      by (auto, metis in_set_conv_nth nth_append)
    have "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [?g (length ws)]"
       by auto
    also have "... = (map ?g [0..<length ws]) @ [0\<^sub>v n]" using g_length by simp
    finally have map_rw: "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [0\<^sub>v n]" .
    have "M.sumlist (map ?g2 [0..<length ws]) = M.sumlist (map ?g [0..<length ws])"
      by (rule arg_cong[of _ _ "M.sumlist"], rule nth_map_conv, auto simp add: nth_append)
    also have "... =  M.sumlist (map ?g [0..<length ws]) + 0\<^sub>v n "
      by (metis M.r_zero calculation hyp lincomb_closed lincomb_list_def ws)
    also have "... = M.sumlist (map ?g [0..<length ws] @ [0\<^sub>v n])" 
      by (rule M.sumlist_snoc[symmetric], auto simp add: nth_append)
    finally have summlist_rw: "M.sumlist (map ?g2 [0..<length ws]) 
      = M.sumlist (map ?g [0..<length ws] @ [0\<^sub>v n])" .
    have "lincomb f (set (ws @ [a])) = lincomb f (set ws)" using True unfolding lincomb_def
      by (simp add: insert_absorb)
    thus ?thesis 
      unfolding hyp lincomb_list_def map_rw summlist_rw
      by auto
  next
    case False    
    have g_length: "?g (length ws) = f a \<cdot>\<^sub>v a" using False by (auto simp add: nth_append)
    have "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [?g (length ws)]"
       by auto
    also have "... = (map ?g [0..<length ws]) @ [(f a \<cdot>\<^sub>v a)]" using g_length by simp
    finally have map_rw: "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [(f a \<cdot>\<^sub>v a)]" .
    have summlist_rw: "M.sumlist (map ?g2 [0..<length ws]) = M.sumlist (map ?g [0..<length ws])"
      by (rule arg_cong[of _ _ "M.sumlist"], rule nth_map_conv, auto simp add: nth_append)
    have "lincomb f (set (ws @ [a])) = lincomb f (set (a # ws))" by auto
    also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in>set (a # ws). f v \<cdot>\<^sub>v v)" unfolding lincomb_def ..
    also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in> insert a (set ws). f v \<cdot>\<^sub>v v)" by simp    
    also have "... = (f a \<cdot>\<^sub>v a) + (\<Oplus>\<^bsub>V\<^esub>v\<in> (set ws). f v \<cdot>\<^sub>v v)"
    proof (rule finsum_insert)
      show "finite (set ws)" by auto
      show "a \<notin> set ws" using False by auto
      show "(\<lambda>v. f v \<cdot>\<^sub>v v) \<in> set ws \<rightarrow> carrier_vec n"
        using snoc.prems(1) by auto
      show "f a \<cdot>\<^sub>v a \<in> carrier_vec n" using snoc.prems by auto
    qed
    also have "... = (f a \<cdot>\<^sub>v a) + lincomb f (set ws)" unfolding lincomb_def ..
    also have "... = (f a \<cdot>\<^sub>v a) + lincomb_list ?f ws" using hyp by auto
    also have "... =  lincomb_list ?f ws  + (f a \<cdot>\<^sub>v a)"
      using M.add.m_comm lincomb_list_carrier snoc.prems by auto
    also have "... = lincomb_list (\<lambda>i. if \<exists>j<i. (ws @ [a]) ! i 
      = (ws @ [a]) ! j then 0 else f ((ws @ [a]) ! i)) (ws @ [a])" 
    proof (unfold lincomb_list_def map_rw summlist_rw, rule M.sumlist_snoc[symmetric])
      show "set (map ?g [0..<length ws]) \<subseteq> carrier_vec n" using snoc.prems
        by (auto simp add: nth_append)
      show "f a \<cdot>\<^sub>v a \<in> carrier_vec n"
        using snoc.prems by auto
    qed
    finally show ?thesis .
  qed
qed auto

lemma span_list_as_span:
  assumes "set vs \<subseteq> carrier_vec n"
  shows "span_list vs = span (set vs)"
  using assms
proof (auto simp: span_list_def span_def)
  fix f show "\<exists>a A. lincomb_list f vs = lincomb a A \<and> finite A \<and> A \<subseteq> set vs" 
    using assms lincomb_list_as_lincomb by auto
next
  fix f::"'a vec \<Rightarrow>'a" and A assume fA: "finite A" and A: "A \<subseteq> set vs" 
  have [simp]: "x \<in> carrier_vec n" if x: "x \<in> A" for x using A x assms by auto
  have [simp]:  "v \<in> carrier_vec n" if v: "v \<in> set vs" for v using assms v by auto
  have set_vs_Un: "((set vs) - A) \<union> A = set vs" using A by auto
  let ?f = "(\<lambda>x. if x\<in>(set vs) - A then 0 else f x)"
  have f0: "(\<Oplus>\<^bsub>V\<^esub>v\<in>(set vs) - A. ?f v \<cdot>\<^sub>v v) = 0\<^sub>v n" by (rule M.finsum_all0, auto)  
  have "lincomb f A = lincomb ?f A"
    by (auto simp add: lincomb_def intro!: finsum_cong2)
  also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in>(set vs) - A. ?f v \<cdot>\<^sub>v v) + (\<Oplus>\<^bsub>V\<^esub>v\<in>A. ?f v \<cdot>\<^sub>v v)" 
    unfolding f0 lincomb_def by auto
  also have "... = lincomb ?f (((set vs) - A) \<union> A)" 
    unfolding lincomb_def 
    by (rule M.finsum_Un_disjoint[symmetric], auto simp add: fA)
  also have "... = lincomb ?f (set vs)" using set_vs_Un by auto
  finally have "lincomb f A = lincomb ?f (set vs)" .    
  with lincomb_as_lincomb_list[OF assms] 
  show "\<exists>c. lincomb f A = lincomb_list c vs" by auto    
qed

lemma in_spanI[intro]:
  assumes "v = lincomb a A" "finite A" "A \<subseteq> W"
  shows "v \<in> span W"
unfolding span_def using assms by auto
lemma in_spanE:
  assumes "v \<in> span W"
  shows "\<exists> a A. v = lincomb a A \<and> finite A \<and> A \<subseteq> W"
using assms unfolding span_def by auto

declare in_own_span[intro]

lemma smult_in_span:
  assumes "W \<subseteq> carrier_vec n" and insp: "x \<in> span W"
  shows "c \<cdot>\<^sub>v x \<in> span W"
proof -
  from in_spanE[OF insp] obtain a A where a: "x = lincomb a A" "finite A" "A \<subseteq> W" by blast
  have "c \<cdot>\<^sub>v x = lincomb (\<lambda> x. c * a x) A" using a(1) unfolding lincomb_def a
    apply(subst finsum_smult) using assms a by (auto simp:smult_smult_assoc)
  thus "c \<cdot>\<^sub>v x \<in> span W" using a(2,3) by auto
qed

lemma span_subsetI: assumes ws: "ws \<subseteq> carrier_vec n" 
  "us \<subseteq> span ws" 
shows "span us \<subseteq> span ws" 
  by (simp add: assms(1) span_is_submodule span_is_subset subsetI ws)

end

context vec_space begin
sublocale idom_vec.

lemma sumlist_in_span: assumes W: "W \<subseteq> carrier_vec n"  
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> span W) \<Longrightarrow> sumlist xs \<in> span W" 
proof (induct xs)
  case Nil
  thus ?case using W by force
next
  case (Cons x xs)
  from span_is_subset2[OF W] Cons(2) have xs: "x \<in> carrier_vec n" "set xs \<subseteq> carrier_vec n" by auto
  from span_add1[OF W Cons(2)[of x] Cons(1)[OF Cons(2)]]
  have "x + sumlist xs \<in> span W" by auto
  also have "x + sumlist xs = sumlist ([x] @ xs)" 
    by (subst sumlist_append, insert xs, auto)
  finally show ?case by simp
qed

lemma span_span[simp]:
  assumes "W \<subseteq> carrier_vec n"
  shows "span (span W) = span W"
proof(standard,standard,goal_cases)
  case (1 x) with in_spanE obtain a A where a: "x = lincomb a A" "finite A" "A \<subseteq> span W" by blast
  from a(3) assms have AC:"A \<subseteq> carrier_vec n" by auto
  show ?case unfolding a(1)[unfolded lincomb_def]
  proof(insert a(3),atomize (full),rule finite_induct[OF a(2)],goal_cases)
    case 1
    then show ?case using span_zero by auto
  next
    case (2 x F)
    { assume F:"insert x F \<subseteq> span W"
      hence "a x \<cdot>\<^sub>v x \<in> span W" by (intro smult_in_span[OF assms],auto)
      hence "a x \<cdot>\<^sub>v x + (\<Oplus>\<^bsub>V\<^esub>v\<in>F. a v \<cdot>\<^sub>v v) \<in> span W"
        using span_add1 F 2 assms by auto
      hence "(\<Oplus>\<^bsub>V\<^esub>v\<in>insert x F. a v \<cdot>\<^sub>v v) \<in> span W"
        apply(subst M.finsum_insert[OF 2(1,2)]) using F assms by auto
    }
    then show ?case by auto
  qed
next
  case 2
  show ?case using assms by(intro in_own_span, auto)
qed


lemma upper_triangular_imp_basis:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "basis (set (rows A))"
  using upper_triangular_imp_distinct[OF assms]
  using upper_triangular_imp_lin_indpt_rows[OF assms] A
  by (auto intro: dim_li_is_basis simp: distinct_card dim_is_n set_rows_carrier)
end

(**** End of the lemmas that could be moved to Jordan_Normal_Form/VS_Connect.thy  ****)

(* To be categorized *)
lemma (in zero_hom) hom_upper_triangular:
  "A \<in> carrier_mat n n \<Longrightarrow> upper_triangular A \<Longrightarrow> upper_triangular (map_mat hom A)"
  by (auto simp: upper_triangular_def)

end
