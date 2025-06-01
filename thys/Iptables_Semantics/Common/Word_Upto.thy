section\<open>Word Upto\<close>
theory Word_Upto
imports Main
  IP_Addresses.Hs_Compat
  Word_Lib.Word_Lemmas
begin

definition word_range :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word list\<close>
  where \<open>word_range v w = sorted_list_of_set {v..w}\<close>

lemma word_range_code [code]:
  \<open>word_range v w = (if v = w then [v] else if v < w then v # word_range (v + 1) w else [])\<close>
proof (cases \<open>v < w\<close>)
  case True
  then have \<open>{v..w} = insert v {v + 1..w}\<close>
    by (auto simp add: eq_neg_iff_add_eq_0 less_is_non_zero_p1 word_Suc_le)
  moreover have \<open>v \<notin> {v + 1..w}\<close>
    using True by (auto simp add: plus_1_less)
  ultimately show ?thesis
    using True by (auto simp add: word_range_def plus_1_less intro!: insort_is_Cons)
next
  case False
  then show ?thesis
    by (simp add: word_range_def)
qed

lemma word_interval_eq_set_word_range [code_unfold]:
  \<open>{v..w} = set (word_range v w)\<close>
  by (simp add: word_range_def)


text\<open>Enumerate a range of machine words.\<close>

text\<open>enumerate from the back (inefficient)\<close>
function word_upto :: "'a word \<Rightarrow> 'a word \<Rightarrow> ('a::len) word list" where
"word_upto a b = (if a = b then [a] else word_upto a (b - 1) @ [b])"
by pat_completeness auto

(*by the way: does not terminate practically if b < a; will terminate after it
  reaches the word wrap-around!*)

termination word_upto
apply(relation "measure (unat \<circ> uncurry (-) \<circ> prod.swap)")
 apply(rule wf_measure; fail)
apply(simp)
apply(subgoal_tac "unat (b - a - 1) < unat (b - a)")
 apply(simp add: diff_right_commute; fail)
apply(rule measure_unat)
apply auto
done

declare word_upto.simps[simp del]
 

text\<open>enumerate from the front (more inefficient)\<close>
function word_upto' :: "'a word \<Rightarrow> 'a word \<Rightarrow> ('a::len) word list" where
"word_upto' a b = (if a = b then [a] else a # word_upto' (a + 1) b)"
by pat_completeness auto

termination word_upto'
apply(relation "measure (\<lambda> (a, b). unat (b - a))")
 apply(rule wf_measure; fail)
apply(simp)
apply(subgoal_tac "unat (b - a - 1) < unat (b - a)")
 apply (simp add: diff_diff_add; fail)
apply(rule measure_unat)
apply auto
done

declare word_upto'.simps[simp del]

lemma word_upto_cons_front[code]:
 "word_upto a b = word_upto' a b"
 proof(induction a b rule:word_upto'.induct)
 case (1 a b)
   have hlp1: "a \<noteq> b \<Longrightarrow> a # word_upto (a + 1) b = word_upto a b"
   apply(induction a b rule:word_upto.induct)
   apply simp
   apply(subst(1) word_upto.simps)
   apply(simp)
   apply safe
    apply(subst(1) word_upto.simps)
    apply (simp)
    apply(subst(1) word_upto.simps)
    apply (simp; fail)
   apply(case_tac "a \<noteq> b - 1")
    apply(simp)
    apply (metis Cons_eq_appendI word_upto.simps)
   apply(simp)
   done

   from 1[symmetric] show ?case
     apply(cases "a = b")
      subgoal
      apply(subst word_upto.simps)
      apply(subst word_upto'.simps)
      by(simp)
     apply(subst word_upto'.simps)
     by(simp add: hlp1)
 qed


(* Most of the lemmas I show about word_upto hold without a \<le> b,
   but I don't need that right now and it's giving me a headache *)


lemma word_upto_set_eq: "a \<le> b \<Longrightarrow> x \<in> set (word_upto a b) \<longleftrightarrow> a \<le> x \<and> x \<le> b"
proof
  show "a \<le> b \<Longrightarrow> x \<in> set (word_upto a b) \<Longrightarrow> a \<le> x \<and> x \<le> b"
    apply(induction a b rule: word_upto.induct)
    apply(case_tac "a = b")
     apply(subst(asm) word_upto.simps)
     apply(simp; fail)
    apply(subst(asm) word_upto.simps)
    apply(simp)
    apply(erule disjE)
     apply(simp; fail)
    proof(goal_cases)
     case (1 a b)
     from 1(2-3) have "b \<noteq> 0" by force
     from 1(2,3) have "a \<le> b - 1"
       by (simp add: word_le_minus_one_leq)
     from 1(1)[OF this 1(4)] show ?case by (metis dual_order.trans 1(2,3) less_imp_le measure_unat word_le_0_iff word_le_nat_alt)
    qed
next
  show "a \<le> x \<and> x \<le> b \<Longrightarrow> x \<in> set (word_upto a b)"
    apply(induction a b rule: word_upto.induct)
    apply(case_tac "a = b")
     apply(subst word_upto.simps)
     apply(simp; force)
    apply(subst word_upto.simps)
    apply(simp)
    apply(case_tac "x = b")
     apply(simp;fail)
    proof(goal_cases)
       case (1 a b)
       from 1(2-4) have "b \<noteq> 0" by force
       from 1(2,4) have "x \<le> b - 1"
         using le_step_down_word by auto
       from 1(1) this show ?case by simp
    qed
qed

lemma word_upto_distinct_hlp: "a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> b \<notin> set (word_upto a (b - 1))"
   apply(rule ccontr, unfold not_not)
   apply(subgoal_tac "a \<le> b - 1")
    apply(drule iffD1[OF word_upto_set_eq[of a "b -1" b]])
     apply(simp add: word_upto.simps)
    apply(subgoal_tac "b \<noteq> 0")
     apply(meson leD measure_unat word_le_nat_alt)
   apply(blast intro: iffD1[OF word_le_0_iff])
  using le_step_down_word apply blast
done

lemma distinct_word_upto: "a \<le> b \<Longrightarrow> distinct (word_upto a b)"
apply(induction a b rule: word_upto.induct)
apply(case_tac "a = b")
 apply(subst word_upto.simps)
 apply(simp; force)
apply(subst word_upto.simps)
apply(case_tac "a \<le> b - 1")
 apply(simp)
 apply(rule word_upto_distinct_hlp; simp)
apply(simp)
  apply(rule ccontr)
  apply (simp add: not_le antisym word_minus_one_le_leq)
done


lemma word_upto_eq_upto: "s \<le> e \<Longrightarrow> e \<le> unat (max_word :: 'l word) \<Longrightarrow>
       word_upto ((of_nat :: nat \<Rightarrow> ('l :: len) word) s) (of_nat e) = map of_nat (upt s (Suc e))"
proof(induction e)
  let ?mwon = "of_nat :: nat \<Rightarrow> 'l word"
  let ?mmw = "max_word :: 'l word"
  case (Suc e)
  show ?case
  proof(cases "?mwon s = ?mwon (Suc e)")
    case True
    have "s = Suc e" using le_unat_uoi Suc.prems True by metis
    with True show ?thesis by(subst word_upto.simps) (simp)
  next
    case False
    hence le: "s \<le> e" using le_SucE Suc.prems by blast
    have lm: "e \<le> unat ?mmw" using Suc.prems by simp
    have sucm: "(of_nat :: nat \<Rightarrow> ('l :: len) word) (Suc e) - 1 = of_nat e" using Suc.prems(2) by simp
    note mIH = Suc.IH[OF le lm]
    show ?thesis by(subst word_upto.simps) (simp add: False[simplified] Suc.prems mIH sucm)
  qed
qed(simp add: word_upto.simps)

lemma word_upto_alt: "(a :: ('l :: len) word) \<le> b \<Longrightarrow>
  word_upto a b = map of_nat (upt (unat a) (Suc (unat b)))"
proof -
   let ?mmw = "- 1 :: 'l word"
   assume le: "a \<le> b"
   hence nle: "unat a \<le> unat b" by(unat_arith)
   have lem: "unat b \<le> unat ?mmw" by (simp add: word_unat_less_le) 
   then show "word_upto a b = map of_nat [unat a..<Suc (unat b)]"
   using word_upto_eq_upto [OF nle lem] by simp
qed

lemma word_upto_upt:
  "word_upto a b = (if a \<le> b then map of_nat (upt (unat a) (Suc (unat b))) else word_upto a b)"
  using word_upto_alt by metis

lemma sorted_word_upto:
  fixes a b :: "('l :: len) word"
  assumes "a \<le> b"
  shows "sorted (word_upto a b)"
proof -
  define m and n where \<open>m = unat a\<close> and \<open>n = Suc (unat b)\<close>
  moreover have \<open>sorted_wrt (\<lambda>x y. (word_of_nat x :: 'l word) \<le> word_of_nat y) [m..<n]\<close>
  proof (rule sorted_wrt_mono_rel [of _ \<open>(\<le>)\<close>])
    show \<open>sorted [m..<n]\<close>
      by simp
    fix r s
    assume \<open>r \<in> set [m..<n]\<close> \<open>s \<in> set [m..<n]\<close> \<open>r \<le> s\<close>
    then have \<open>m \<le> r\<close> \<open>s < n\<close>
      by simp_all
    then have \<open>take_bit LENGTH('l) s = s\<close>
      by (auto simp add: m_def n_def less_Suc_eq_le unsigned_of_nat dest: le_unat_uoi)
    with \<open>r \<le> s\<close> show \<open>(word_of_nat r :: 'l word) \<le> word_of_nat s\<close>
      apply (simp add: of_nat_word_less_eq_iff)
      using take_bit_nat_less_eq_self apply (rule order_trans)
      apply assumption
      done
  qed
  then have \<open>sorted (map word_of_nat [m..<n] :: 'l word list)\<close>
    by (simp add: sorted_map)
  ultimately have \<open>sorted (map of_nat [unat a..<Suc (unat b)] :: 'l word list)\<close>
    by simp
  with assms show ?thesis
    by (simp only: word_upto_alt)
qed

end
