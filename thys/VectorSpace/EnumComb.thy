theory EnumComb
imports Main
        "~~/src/HOL/Library/FuncSet"
        "~~/src/HOL/Number_Theory/Binomial"
        Vectors
begin

abbreviation cardf::"'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "cardf A n \<equiv> (finite A \<and> card A = n)"

lemma disj_union_card:
  fixes A B f g C A' B'
  assumes uni: "C = A' \<union> B'" and disj: "A' \<inter> B' = {}"
    and f: "bij_betw f A A'" and g: "bij_betw g B B'" and fin_A: "finite A" and fin_B: "finite B"
  shows "cardf C (card A + card B)"
proof - 
  from assms show ?thesis
    apply (unfold bij_betw_def, auto)
    apply (subst Finite_Set.card_Un_disjoint)
    apply auto
    by (subst card_image, auto)+
qed


lemma inv_implies_bij:
  "inverses A B f f' \<Longrightarrow> bij_betw f A B"
  apply (unfold bij_betw_def, auto)
  apply (metis inj_on_inverseI)
  apply (unfold image_def, auto)
  by (rename_tac x, rule_tac x="f' x" in bexI, auto)


lemma update_nth:
  "\<And>n. (n<length l \<Longrightarrow> (l[n:=a])!i = (if i = n then a else l!i))"
by auto

lemma listsum_equiv:
  fixes l::"nat list"
  shows "int (listsum l) = (\<Sum>x\<leftarrow>l. (int x))"
  apply (induct l)
  by auto



lemma listsum_update:
  fixes i and l::"int list" and x
  assumes i:"i<length l"
  shows "listsum (l[i:=x]) = (listsum l) - (l!i) +  x"
using i proof (induct l arbitrary: i)
  case Nil
  from Nil.prems show ?case by auto
next
  case (Cons a l)
  thm Cons
  show ?case
  proof (cases i)
    case 0
    from Cons.prems "0" show ?thesis by auto
  next
    case (Suc j)
    from Suc have 1: "listsum ((a # l)[i := x]) = a + listsum ( l[i - 1 := x])"
      by auto
    moreover from Suc have 2: "listsum (a # l) - ((a # l) ! i) + x = a + listsum  l -  (l ! (i - 1)) + x"
      by auto
    moreover from Suc Cons.hyps Cons.prems have 3: "listsum ( l[i - 1 := x]) = listsum  l -  (l ! (i - 1)) + x" 
      by (intro Cons.hyps[where ?i = "i - 1"], auto)
    ultimately show ?thesis by auto
    qed
qed

lemma listsum_drop:
  fixes l::"int list"
  assumes "length l \<ge>1"  
  shows "listsum (tl l) = listsum l - (l!0)"
proof -
  show ?thesis
  proof (cases l)
    case Nil
    from Nil assms show ?thesis by auto
  next
    case (Cons a xs)
    show ?thesis apply (subst Cons)+ by auto
  qed
qed 

lemma cons_tail:
  fixes l::"int list"
  assumes "length l \<ge>1"  
  shows "l = (l!0)#(tl l)"
proof -
  show ?thesis
  proof (cases l)
    case Nil
    from Nil assms show ?thesis by auto
  next
    case (Cons a xs)
    show ?thesis apply (subst Cons)+ by auto
  qed
qed

lemma cons_prop:
  fixes l P a
  assumes "\<forall>i<length l. P (l!i)" and "P a"
  shows "\<And>i. i<length l + 1 \<Longrightarrow> P ((a#l)!i)"
proof - 
  fix i
  assume 1: " i<length l + 1"
  from 1 show "?thesis i" using assms 
    by (subst List.nth_Cons', auto)
qed

lemma tl_prop:
  fixes l P
  assumes l: "length l \<ge> 1" and P: "\<forall>i<length l. P (l!i)"
  shows "\<And>i. i<length l - 1 \<Longrightarrow> P ((tl l)!i)"
proof - 
  fix i
  assume 1: " i<length l - 1"
  from l have 2: "\<And>j. (j<length l - 1\<Longrightarrow> (tl l)!j = l! (j + 1))"
    apply (cases l)
    by auto
  from 1 show "?thesis i" using assms 
    by (subst 2, auto)
qed

  
lemma update_prop:
  fixes l P a j
  assumes P: "\<forall>i<length l. P (l!i)" and j: "j<length l" and a: "P a"
  shows "\<And>i. i<length l \<Longrightarrow> P ((l[j:=a])!i)"
proof - 
  fix i
  assume 1: " i<length l"
  from 1 show "?thesis i" using assms 
    by (subst update_nth, auto)
qed

lemma listsum_gt:
  fixes l::"int list" 
  assumes 1:"\<forall>i<length l. l!i\<ge>x"
  shows "listsum l \<ge> x * length l"
proof -
  from 1 have "listsum (map (\<lambda>j. x) l) \<le> listsum (map id l)"
    apply (intro List.listsum_mono, auto)
    by (metis in_set_conv_nth)
  moreover have "listsum (map (\<lambda>j. x) l) = x * length l"
    apply (induct l, auto)
    by (auto simp add: Int.int_distrib)
  moreover have "listsum (map id l) = listsum l" by auto
  ultimately show ?thesis by auto
qed

lemma lt_listsum:
  fixes l::"int list" and i
  assumes 1:"i<length l" and 2:"\<forall>i<length l. l!i\<ge>0"
  shows "l!i \<le> listsum l"
proof -
  from assms have "listsum (l[i:=0]) = listsum l - (l!i)"
    by (subst listsum_update, auto)
  moreover from 1 2 have "0*int (length (l[i:=0]))\<le>listsum (l[i:=0])"
    apply (intro listsum_gt, auto)
    by (subst update_nth, auto)
  ultimately show ?thesis by auto
qed

        
lemma ways_sum_rec:
  fixes m::nat and l::"int list" and N::int
  assumes "m\<ge>1"
  shows "cardf {l::int list. Avector  l {x::int. x\<ge>0} m \<and>  listsum l = N} 
    (card {l. Avector l {x::int. x\<ge>0} (m - 1) \<and>  listsum l = N} +
    card {l. Avector l {x::int. x\<ge>0} m \<and> listsum l =  N - 1})"
    (is "cardf ?C (card ?A + card ?B)")
proof - 
  let ?A'="{l. Avector l {x::int. x\<ge>0} m \<and> listsum l = N \<and> l ! 0 = 0}"
  let ?B'="{l. Avector l {x::int. x\<ge>0} m \<and> listsum l = N \<and> l ! 0 \<noteq> 0}"
  let ?f ="(\<lambda> l. 0#l)"
  let ?g ="(\<lambda> l. list_update l 0 (l ! 0 + 1))"
  have uni: "?C = ?A' \<union> ?B'"
    by auto
  moreover have disj: "?A' \<inter> ?B' = {}"
    by auto
  moreover have f: "bij_betw ?f ?A ?A'" using assms
    apply (intro inv_implies_bij[where ?f'=tl])
    apply auto
    apply (unfold Avector_def, auto)
    apply (intro cons_prop[where ?P = "\<lambda>x. x\<ge>0"], auto)
    apply (intro tl_prop[where ?P = "\<lambda>x. x\<ge>0"], auto)
    apply (subst listsum_drop, auto)
    by (subst (4) cons_tail, auto)
  moreover have g: "bij_betw ?g ?B ?B'" using assms
    apply (intro inv_implies_bij[where ?f'="(\<lambda> l. list_update l 0 (l ! 0 - 1))"], auto)
    apply (unfold Avector_def, auto)
    apply (intro update_prop[where ?P = "\<lambda>x. x\<ge>0"], auto)
    apply (drule_tac x="0" in spec, auto)
    apply (subst listsum_update, auto)
    apply (drule_tac x="0" in spec, auto)
    apply (intro update_prop[where ?P = "\<lambda>x. x\<ge>0"], auto)
    apply (drule_tac x="0" in spec, auto)
    by (subst listsum_update, auto)
  moreover have fin: "\<And>M N. finite (Avectors {x::int. 0 \<le> x \<and> x \<le> N} M)"
    by (intro Avectors_card[THEN conjunct1], auto)
  moreover have fin_A: "finite ?A" 
    apply (intro finite_subset[where ?A = "?A" and ?B = "Avectors {x. 0 \<le> x \<and> x \<le> N} (m - 1)"], 
      auto)
    apply (unfold Avectors_def Avector_def, auto)[1]
    apply (intro lt_listsum, auto) 
    by (intro fin)
  moreover have fin_B: "finite ?B"
    apply (intro finite_subset[where ?A = "?B" and ?B = "Avectors {x. 0 \<le> x \<and> x \<le> N - 1} (m)"], 
      auto)
    apply (unfold Avectors_def Avector_def, auto)[1]
    apply (rename_tac l i, subgoal_tac " l ! i \<le>listsum l")
    apply auto[1]
    apply (intro lt_listsum, auto)
(*this part is really silly, it rewrites \<le>N-1 as <N but I don't want it to!*)
    apply (subgoal_tac "finite (Avectors {x. 0 \<le> x \<and> x \<le> N - 1} (m))")
    apply auto[1]
    by (intro fin) 
  ultimately show ?thesis 
    by (intro disj_union_card, auto)
qed

lemma ways_sum:
  fixes N m::nat
  assumes m: "m\<ge>1"
  shows "cardf {l::int list. Avector l {x. x\<ge>0} m \<and> listsum l = N} (binomial (N + m - 1) N)"
    (is "cardf (?A m N) (binomial (N + m - 1) N)")
using m proof (induct "N + m - 1" arbitrary: N m)
-- "In the base case, the only solution is $[0]$."
  case 0
  have 0: "0 = N + m - 1 " by fact
  have 1: "\<And>l::int list. length l = Suc 0 \<and> listsum l = 0 \<Longrightarrow> l = [0]"
  proof -
    fix l::"int list"
    assume "length l = Suc 0 \<and> listsum l = 0"
    thus "?thesis l"
      by (cases l, auto)
  qed
  hence 2: "{l::int list. length l = Suc 0 \<and> 0 \<le> l ! 0 \<and> listsum l = 0}= {[0]}"
    by auto
  show "cardf {l::int list. Avector l {x. x\<ge>0} m \<and> listsum l = N} (binomial (N + m - 1) N)"
  proof -
    from 0 "0.prems" have "m=1 \<and> N=0" by auto
    from this 0 "0.prems"  show ?thesis
      apply safe
      apply (unfold Avector_def)
      by (simp,subst 2, simp)+
  qed
next
  case (Suc k)
  from Suc.prems have c: "cardf {l::int list. Avector l {x::int. x\<ge>0} m \<and> listsum l = int N}
    (card {l::int list. Avector l {x::int. x\<ge>0} (m - 1) \<and> listsum l =  int N} + 
      card {l::int list. Avector l {x::int. x\<ge>0} m \<and> listsum l =  (int N - 1)})"
    by (rule ways_sum_rec)
  
-- "Now basically just use the induction hypothesis, however we have to be careful about boundary
cases."  
  
  have c1: "card {l::int list. Avector l {x::int. x\<ge>0} (m - 1) \<and> listsum l =  int N} = 
    (binomial (N + (m - 1) - 1) N)"
  proof (cases "m = 1")
    case True
    moreover from Suc.hyps True have "N\<ge>1" by auto
    ultimately show ?thesis 
      by (unfold Avector_def, subst binomial_eq_0, auto)
  next
    case False
    thus ?thesis using Suc
      by (intro Suc.hyps(1)[THEN conjunct2], auto)
  qed

  from Suc have c2: "card {l::int list. Avector l {x::int. x\<ge>0} m \<and> listsum l =  (int N) - 1} = 
    (if N>0 then (binomial ((N - 1) + m - 1) (N - 1)) else 0)"
  proof -
    have int_sub: "N>0 \<Longrightarrow> int N - 1 = int (N - 1) " by auto

    from Suc have "N>0 \<Longrightarrow>
      card {l::int list. Avector l {x::int. x\<ge>0} m \<and> listsum l =  int N - 1} = 
      (binomial ((N - 1) + m - 1) (N - 1))"
      apply (subst int_sub, simp)
(*card {l. Avector l {x. 0 \<le> x} m \<and> listsum l = int N - 1} = N - 1 + m - 1 choose (N - 1)*)
      by (intro Suc.hyps(1)[THEN conjunct2], auto)

    moreover have "card {l::int list. Avector l {x::int. x\<ge>0} m \<and> listsum l =  - 1} = 0" 
    proof - 
      have show_empty: "\<And>A. A={} \<Longrightarrow> card A = 0" by auto
      {
        fix l::"int list" and m::nat
        assume asm: "length l = m \<and> (\<forall>i<m. 0 \<le> l ! i) \<and> listsum l = - 1"
        hence "listsum l \<ge>0 * int (length l)"
          by (intro listsum_gt, auto)
        hence "False" using asm by auto
      }
      hence "{l::int list. length l = m \<and> (\<forall>i<m. 0 \<le> l ! i) \<and> listsum l = - 1} = {}" by auto
      hence "{l::int list. Avector l {x::int. x\<ge>0} m \<and> listsum l =  - 1} = {}" 
        by (unfold Avector_def, auto)
      thus ?thesis by (rule show_empty)
    qed
    
    ultimately show ?thesis 
      by (unfold Avector_def, auto)
  qed

  from c Suc have add_card: "(card {l::int list. Avector l {x::int. x\<ge>0} (m - 1) \<and> listsum l =  int N} + 
      card {l::int list. Avector l {x::int. x\<ge>0} m \<and> listsum l =  (int N - 1)}) = (binomial (N + m - 1) N)"
    apply (subst c1 c2)+
    apply (auto split:split_if)
    by (subst (3) choose_reduce_nat, auto)
  
  thus ?case using c by auto
qed

end


