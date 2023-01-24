(*by Ammer*)
theory VEBT_Definitions imports
   Main
  "HOL-Library.Extended_Nat"
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.Code_Target_Nat"
  
begin
section \<open>Preliminaries and Preparations\<close>

subsection \<open>Data Type Definition\<close>

datatype VEBT = is_Node: Node (info:"(nat*nat) option")(deg: nat)(treeList: "VEBT list") (summary:VEBT) |
 is_Leaf: Leaf   bool     bool 

hide_const (open) info deg treeList summary

locale VEBT_internal begin

subsection \<open>Functions for obtaining high and low bits of an input number.\<close>

definition high :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "high x n = (x div (2^n))"

definition low :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "low x n = (x mod (2^n))"

subsection \<open>Some auxiliary lemmata\<close>

lemma inthall[termination_simp]: "(\<And> x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> n < length xs \<Longrightarrow> P (xs ! n)"
  apply(induction xs arbitrary: n)
  apply auto
  using less_Suc_eq_0_disj 
  apply auto
  done

lemma intind: "i < n \<Longrightarrow> P x \<Longrightarrow> P (replicate n x ! i)"
  by (metis in_set_replicate inthall length_replicate)

lemma concat_inth:"(xs @[x]@ys)! (length xs) = x" 
  by simp

lemma pos_n_replace: "n<length xs \<Longrightarrow> length xs = length (take n xs @ [y] @drop (Suc n) xs)" 
  by simp

lemma inthrepl: "i < n \<Longrightarrow> (replicate n x) ! i = x" by simp

lemma nth_repl: "m<length xs \<Longrightarrow> n <length xs \<Longrightarrow> m\<noteq> n \<Longrightarrow>(take n xs @ [x] @ drop (n+1) xs) ! m = xs ! m" 
  by (metis Suc_eq_plus1 append_Cons append_Nil nth_list_update_neq upd_conv_take_nth_drop)

lemma [termination_simp]:assumes "high x deg < length treeList"
  shows"size (treeList ! high x deg) < Suc (size_list size treeList + size s)"
proof-
  have "treeList ! high x deg \<in> set treeList"
    using assms by auto
  then show ?thesis
    using not_less_eq size_list_estimation by fastforce
qed

subsection \<open> Auxiliary functions for defining valid Van Emde Boas Trees\<close>

text \<open>This function checks whether an element occurs  in a Leaf\<close>

fun naive_member :: "VEBT \<Rightarrow> nat \<Rightarrow> bool" where
  "naive_member (Leaf a b) x = (if x = 0 then a else if x = 1 then b else False)"|
  "naive_member (Node _ 0 _ _) _ = False"|
  "naive_member (Node _ deg treeList s) x =  (let pos = high x (deg div 2) in
    (if pos < length treeList then naive_member (treeList ! pos) (low x (deg div 2)) else False))"

text \<open>Test for elements stored by using the provide min-max-fields\<close>

fun membermima :: "VEBT \<Rightarrow> nat \<Rightarrow> bool" where
  "membermima (Leaf _ _) _ = False"|
  "membermima (Node None 0 _ _ )_ =False"|
  "membermima (Node (Some (mi,ma)) 0 _ _) x = (x = mi \<or> x = ma)"|
  "membermima (Node (Some (mi, ma)) deg treeList _) x = (x = mi \<or> x = ma \<or> (
    let pos = high x ( deg div 2) in (if pos < length treeList  
    then membermima (treeList ! pos) (low x (deg div 2)) else False)))"|
  "membermima (Node None (deg) treeList _) x = (let pos = high x (deg div 2) in
    (if pos < length treeList then membermima (treeList ! pos) (low x (deg div 2)) else False))"

lemma length_mul_elem:"(\<forall> x \<in> set xs. length x = n) \<Longrightarrow> length (concat xs) = (length xs) * n"
  apply(induction xs)
   apply auto
  done

text \<open>We combine both auxiliary functions: The following test returns true if and only if an element occurs in the tree with respect to our interpretation no matter where it is stored.\<close>

definition both_member_options :: "VEBT \<Rightarrow> nat \<Rightarrow> bool" where
  "both_member_options t x = (naive_member t x \<or> membermima t x)"


end  
context begin
  interpretation VEBT_internal .
  
definition set_vebt :: "VEBT \<Rightarrow> nat set" where
  "set_vebt t = {x. both_member_options t x}"
end  
  
subsection \<open>Inductive Definition of semantically valid Vam Emde Boas Trees\<close>

text \<open>Invariant for verification proofs\<close>

context begin
  interpretation VEBT_internal .

inductive invar_vebt::"VEBT \<Rightarrow> nat \<Rightarrow> bool" where
 "invar_vebt (Leaf  a b) (Suc 0) "|
 "( \<forall> t \<in> set treeList. invar_vebt t n) \<Longrightarrow> invar_vebt summary m  \<Longrightarrow>  length treeList = 2^m 
 \<Longrightarrow> m = n \<Longrightarrow> deg = n + m \<Longrightarrow> (\<nexists> i. both_member_options summary i) 
 \<Longrightarrow>(\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x) 
 \<Longrightarrow> invar_vebt (Node None deg treeList summary) deg"|
 "( \<forall> t \<in> set treeList. invar_vebt t n) \<Longrightarrow> invar_vebt summary m 
 \<Longrightarrow>  length treeList = 2^m \<Longrightarrow> m = Suc n \<Longrightarrow> deg = n + m \<Longrightarrow> (\<nexists> i. both_member_options summary i)
 \<Longrightarrow> (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x) 
 \<Longrightarrow> invar_vebt (Node None deg treeList summary) deg"|
 "( \<forall> t \<in> set treeList. invar_vebt t n) \<Longrightarrow> invar_vebt summary m  \<Longrightarrow> length treeList = 2^m \<Longrightarrow> m = n
 \<Longrightarrow>deg = n + m\<Longrightarrow> (\<forall> i < 2^m. (\<exists> x. both_member_options (treeList ! i) x) \<longleftrightarrow> ( both_member_options summary i)) \<Longrightarrow>
                    (mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x)) \<Longrightarrow>
                      mi \<le> ma \<Longrightarrow> ma < 2^deg \<Longrightarrow>
                     (mi \<noteq> ma \<longrightarrow> 
                                 (\<forall> i < 2^m.  
                                            (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                            (\<forall> x. (high x n = i \<and> both_member_options (treeList ! i) (low x n)  ) \<longrightarrow> mi < x \<and> x \<le> ma) ) ) 
 \<Longrightarrow> invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg"|
 "( \<forall> t \<in> set treeList. invar_vebt t n) \<Longrightarrow>invar_vebt summary m  \<Longrightarrow>  length treeList = 2^m
 \<Longrightarrow>  m = Suc n \<Longrightarrow>deg = n + m\<Longrightarrow>(\<forall> i < 2^m. (\<exists> x. both_member_options (treeList ! i) x) \<longleftrightarrow> ( both_member_options summary i)) \<Longrightarrow>
                    (mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x)) \<Longrightarrow>
                      mi \<le> ma \<Longrightarrow> ma < 2^deg \<Longrightarrow>
                     (mi \<noteq> ma \<longrightarrow> 
                                 (\<forall> i < 2^m.  
                                            (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                            (\<forall> x. (high x n = i \<and> both_member_options (treeList ! i) (low x n)  ) \<longrightarrow> mi < x \<and> x \<le> ma)))
 \<Longrightarrow> invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg"

end 
 
context VEBT_internal begin

definition "in_children n treeList x \<equiv> both_member_options (treeList ! high x n) (low x n)"     

text \<open>functional validness definition\<close>
fun valid' :: "VEBT \<Rightarrow> nat \<Rightarrow> bool" where
  "valid' (Leaf _ _) d \<longleftrightarrow> d=1"
| "valid' (Node mima deg treeList summary) deg' \<longleftrightarrow>
  (
    deg=deg' \<and> (
    let n = deg div 2; m = deg - n in
      ( \<forall> t \<in> set treeList. valid' t n )
    \<and> valid' summary m
    \<and> length treeList = 2^m
    \<and> (
      case mima of
        None \<Rightarrow> (\<nexists> i. both_member_options summary i) \<and> (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x)
      | Some (mi,ma) \<Rightarrow> 
          mi \<le> ma \<and> ma<2^deg
        \<and> (\<forall> i < 2^m. (\<exists> x. both_member_options (treeList ! i) x) \<longleftrightarrow> ( both_member_options summary i))  
        \<and> (if mi=ma then (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x)
           else 
             in_children n treeList ma
           \<and> (\<forall>x < 2^deg. in_children n treeList x \<longrightarrow> mi<x \<and> x\<le>ma)
          )
    )
    )
  )
"  

text \<open>equivalence proofs\<close>

lemma high_bound_aux: "ma < 2^(n+m) \<Longrightarrow> high ma n < 2^m"
  unfolding high_def
  by (simp add: add.commute less_mult_imp_div_less power_add)

lemma valid_eq1:
  assumes "invar_vebt t d" 
  shows "valid' t d"
  using assms apply induction
  apply simp_all
  apply (auto simp: in_children_def dest: high_bound_aux) []  
  subgoal for treeList n summary m deg mi ma
    apply (intro allI impI conjI)
    apply (auto simp: in_children_def dest: high_bound_aux) []
    apply (metis add_Suc_right high_bound_aux power_Suc)   
    apply (auto simp: in_children_def dest: high_bound_aux) []
    apply (metis add_Suc_right high_bound_aux power_Suc)   
    apply (auto simp: in_children_def dest: high_bound_aux) []
    apply (metis add_Suc_right high_bound_aux power_Suc)
    done
  done 
  
lemma even_odd_cases:
  fixes x :: nat
  obtains n where "x=n+n" | n where "x = n + Suc n"
  apply (cases "even x"; simp)
  apply (metis add_self_div_2 div_add)
  by (metis add.commute mult_2 oddE plus_1_eq_Suc)
  
lemma valid_eq2: "valid' t d \<Longrightarrow> invar_vebt t d"  
  apply (induction t d rule: valid'.induct)
  apply (auto intro: invar_vebt.intros simp: Let_def split: option.splits)
  subgoal for deg treeList summary
    apply (rule even_odd_cases[of deg]; simp)
    apply (rule invar_vebt.intros(2); simp)
    apply (rule invar_vebt.intros(3); simp add: algebra_simps) by presburger
  subgoal for deg treeList summary mi ma
    apply (rule even_odd_cases[of deg]; simp)
    subgoal
      apply (rule invar_vebt.intros(4); simp?)
      apply (auto simp: in_children_def) []
       apply (meson le_less_linear le_less_trans)
      apply (metis div_eq_0_iff div_exp_eq gr_implies_not0 high_def)
       done
    subgoal
      apply (rule invar_vebt.intros(5); simp?)
      apply (auto) []
      apply (auto) []
      apply (auto simp: in_children_def) []
      apply (meson le_less_linear le_less_trans)
      apply (metis div_eq_0_iff add_Suc_right div_exp_eq high_def power_Suc power_eq_0_iff zero_neq_numeral)
      done
    done
  done
  
lemma valid_eq: "valid' t d \<longleftrightarrow> invar_vebt t d"
  using valid_eq1 valid_eq2 by auto

lemma [termination_simp]: assumes "odd (v::nat)" shows "v div 2 < v"
  by (simp add: assms odd_pos)

lemma [termination_simp]:assumes "n > 1" and " odd n" shows" Suc (n div 2) < n"
  by (metis Suc_lessI add_diff_cancel_left' assms(1) assms(2) div_eq_dividend_iff div_less_dividend even_Suc even_Suc_div_two odd_pos one_less_numeral_iff plus_1_eq_Suc semiring_norm(76) zero_less_diff)

end
  
subsection \<open>Function for generating an empty tree of arbitrary degree respectively order\<close>

context begin
interpretation VEBT_internal .

fun vebt_buildup :: "nat \<Rightarrow> VEBT" where
  "vebt_buildup 0 = Leaf False False"|
  "vebt_buildup (Suc 0) = Leaf False False"|
  "vebt_buildup n = (if even n then (let half = n div 2 in
                   Node None n (replicate (2^half) (vebt_buildup half)) (vebt_buildup half))
                else (let half = n div 2 in  
                  Node None n ( replicate (2^(Suc half)) (vebt_buildup half)) (vebt_buildup (Suc half))))"

end

context VEBT_internal begin                  
                  
lemma buildup_nothing_in_leaf: "\<not> naive_member (vebt_buildup n) x"
proof(induction arbitrary: x rule: vebt_buildup.induct)
  case 1
  then show ?case by simp
next
  case (2 v)
  then show ?case
    by simp
next
  case (3 n)
  let ?n = "Suc(Suc n)" 
  show ?case proof(cases "even ?n")
    case True
    let ?half = "?n div 2"
    have "\<not> naive_member (vebt_buildup ?half) y" for y
      using "3.IH"(1) True by blast 
    hence 0:"\<forall> t \<in> set  (replicate (2^?half) (vebt_buildup ?half)) . \<not> naive_member t  x"
      by simp
    have "naive_member (vebt_buildup ?n) x \<Longrightarrow> False"
    proof-
      assume "naive_member (vebt_buildup ?n) x"
      hence "high x ?half < 2^?half \<and>
               naive_member ((replicate (2^?half) (vebt_buildup ?half)) ! (high x ?half)) (low x ?half)"
        by (metis True vebt_buildup.simps(3) length_replicate naive_member.simps(3))
      hence "\<exists> t \<in> set  (replicate (2^?half) (vebt_buildup ?half)) . naive_member t  x " 
        by (metis \<open>\<And>y. \<not> naive_member (vebt_buildup (Suc (Suc n) div 2)) y\<close> nth_replicate)
      then show False using 0 by simp
    qed
    then show ?thesis
      by blast
  next
    case False
    let ?half = "?n div 2"
    have "\<not> naive_member (vebt_buildup ?half) y" for y
      using "3.IH" False by blast
    hence 0:"\<forall> t \<in> set  (replicate (2^(Suc ?half)) (vebt_buildup ?half)) . \<not> naive_member t  x"
      by simp
    have "naive_member (vebt_buildup ?n) x \<Longrightarrow> False"
    proof-
      assume "naive_member (vebt_buildup ?n) x"
      hence "high x ?half < 2^(Suc ?half) \<and>
               naive_member ((replicate (2^(Suc ?half)) (vebt_buildup ?half)) ! (high x ?half)) (low x ?half)"
        by (metis False vebt_buildup.simps(3) length_replicate naive_member.simps(3))
      hence "\<exists> t \<in> set  (replicate (2^(Suc ?half)) (vebt_buildup ?half)) . naive_member t  x "
        by (metis \<open>\<And>y. \<not> naive_member (vebt_buildup (Suc (Suc n) div 2)) y\<close> nth_replicate)
      then show False using 0 by simp
    qed
    then show ?thesis by force
  qed
qed


lemma buildup_nothing_in_min_max:"\<not> membermima (vebt_buildup n) x"
proof(induction arbitrary: x rule: vebt_buildup.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 va)
  let ?n = "Suc (Suc va)"
  let ?half = "?n div 2"
  show ?case proof(cases "even ?n")
    case True
    have "\<not> membermima (vebt_buildup ?half) y" for y
      using "3.IH"(1) True by blast 
    hence 0:"\<forall> t \<in> set  (replicate (2^?half) (vebt_buildup ?half)) . \<not> membermima t  x"
      by simp
    then show ?thesis 
      by (metis "3.IH"(1) True vebt_buildup.simps(3) inthrepl length_replicate membermima.simps(5))
  next
    case False
     have "\<not> membermima (vebt_buildup ?half) y" for y
      using "3.IH" False  by blast 
    moreover hence 0:"\<forall> t \<in> set  (replicate (2^(Suc ?half)) (vebt_buildup ?half)) . \<not> membermima t  x"
      by simp
    ultimately show ?thesis
      by (metis vebt_buildup.simps(3) inthrepl length_replicate membermima.simps(5))
  qed
qed
 
text \<open>The empty tree generated by $vebt_buildup$ is indeed a valid tree.\<close>

lemma buildup_gives_valid: "n>0  \<Longrightarrow> invar_vebt (vebt_buildup n) n"
proof( induction n rule: vebt_buildup.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case
    by (simp add: invar_vebt.intros(1))
next
  case (3 va)
  let ?n = "Suc (Suc va)" 
  let ?half = "?n div 2"  
  show ?case proof(cases "even ?n")
    case True
    hence a:"vebt_buildup ?n =  Node None ?n (replicate (2^?half) (vebt_buildup ?half)) (vebt_buildup ?half)" by simp
    moreover hence "invar_vebt (vebt_buildup ?half) ?half"
      using "3.IH"(1) True by auto
    moreover hence "( \<forall> t \<in> set (replicate (2^?half) (vebt_buildup ?half)). invar_vebt t ?half)" by simp
    moreover have "length (replicate (2^?half) (vebt_buildup ?half)) = 2^?half" by auto
    moreover have "?half+?half = ?n" 
      using True by auto
    moreover have " \<forall> t \<in> set (replicate (2^?half) (vebt_buildup ?half)). (\<nexists> x. both_member_options t x)" 
    proof
      fix t
      assume "t \<in> set (replicate (2^?half) (vebt_buildup ?half))"
      hence "t = (vebt_buildup ?half)" by simp
      thus "\<nexists> x. both_member_options t x"
        by (simp add: both_member_options_def buildup_nothing_in_leaf buildup_nothing_in_min_max)
    qed
    moreover have " (\<nexists> i. both_member_options (vebt_buildup ?half) i)"
      using both_member_options_def buildup_nothing_in_leaf buildup_nothing_in_min_max by blast
    ultimately have "invar_vebt  (Node None ?n (replicate (2^?half) (vebt_buildup ?half)) (vebt_buildup ?half)) ?n"
      using invar_vebt.intros(2)[of "replicate (2^?half) (vebt_buildup ?half)" ?half "vebt_buildup ?half" ?half ?n] 
      by simp
    then show ?thesis using a by auto 
  next 
    case False
    hence a:"vebt_buildup ?n =  Node None ?n (replicate (2^(Suc ?half)) (vebt_buildup ?half)) (vebt_buildup (Suc ?half))" by simp
    moreover hence "invar_vebt (vebt_buildup (Suc ?half)) (Suc ?half)"
      using "3.IH" False by auto
    moreover have "invar_vebt (vebt_buildup ?half) ?half"
      using "3.IH"(3) False by auto
    moreover hence "( \<forall> t \<in> set (replicate (2^(Suc ?half)) (vebt_buildup ?half)). invar_vebt t ?half)" by simp
    moreover have "length (replicate (2^(Suc ?half)) (vebt_buildup ?half)) = 2^(Suc ?half)" by auto
    moreover have "(Suc ?half)+?half = ?n" 
      using False by presburger
    moreover have " \<forall> t \<in> set (replicate (2^(Suc ?half)) (vebt_buildup ?half)). (\<nexists> x. both_member_options t x)" 
    proof
      fix t
      assume "t \<in> set (replicate (2^(Suc ?half)) (vebt_buildup ?half))"
      hence "t = (vebt_buildup ?half)" by simp
      thus "\<nexists> x. both_member_options t x"
        by (simp add: both_member_options_def buildup_nothing_in_leaf buildup_nothing_in_min_max)
    qed
    moreover have " (\<nexists> i. both_member_options (vebt_buildup (Suc ?half)) i)"
      using both_member_options_def buildup_nothing_in_leaf buildup_nothing_in_min_max by blast
    moreover have "?half + Suc ?half = ?n" 
      using calculation(6) by auto
    ultimately have "invar_vebt  (Node None ?n (replicate (2^(Suc ?half)) (vebt_buildup ?half)) (vebt_buildup (Suc ?half))) ?n"
      using invar_vebt.intros(3)[of "replicate (2^(Suc ?half)) (vebt_buildup ?half)" ?half "vebt_buildup (Suc ?half)" "Suc ?half" ?n ] 
      by simp 
    then show ?thesis using a by auto 
  qed
qed

lemma mi_ma_2_deg: assumes "invar_vebt (Node (Some (mi, ma)) deg treeList summary) n" shows "mi\<le> ma \<and> ma < 2^deg"
proof-
  from  assms show ?thesis proof cases qed blast+
qed

lemma deg_not_0: "invar_vebt t n \<Longrightarrow> n > 0"
  apply(induction t n rule: invar_vebt.induct)
      apply auto
  done

lemma set_n_deg_not_0:assumes " \<forall>t\<in>set treeList. invar_vebt t n"and" length treeList = 2^m "shows " n \<ge> 1"
proof-
  have "length treeList > 0"
    by (simp add: assms(2))
  then obtain t ts where "treeList = t#ts"
    by (metis list.size(3) neq_Nil_conv not_less0)
  hence "invar_vebt t n"
    by (simp add: assms(1))
  hence "n \<ge> 1" 
    using deg_not_0 by force
  thus ?thesis by simp
qed

lemma both_member_options_ding: assumes"invar_vebt (Node info deg treeList summary) n "and "x<2^deg"and"
 both_member_options (treeList ! (high x (deg div 2))) (low x (deg div 2))"shows "both_member_options  (Node info deg treeList summary) x"
proof-
  from assms(1) show ?thesis proof(induction "(Node info deg treeList summary)" n rule: invar_vebt.induct)
    case (2 n m)
    hence "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) \<or> 
           naive_member (treeList ! (high x (deg div 2))) (low x (deg div 2))"
      using assms(3) both_member_options_def by auto
    moreover  hence "deg > 1" 
      using "2.hyps"(2) "2.hyps"(5) "2.hyps"(6) deg_not_0 by force
    moreover have "high x (deg div 2)<2^m"
      by (metis "2.hyps"(5) "2.hyps"(6) div_eq_0_iff add_self_div_2 assms(2) div_exp_eq high_def power_not_zero)
    moreover have "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                    \<Longrightarrow> membermima (Node info deg treeList summary) x" using membermima.simps(5)[of "deg-1" treeList summary x]
      using "2.hyps"(4) "2.hyps"(9) \<open>1 < deg\<close> \<open>high x (deg div 2) < 2 ^ m\<close> zero_le_one by fastforce
    moreover have "naive_member  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                   \<Longrightarrow> naive_member (Node info deg treeList summary) x"
      by (smt "2.hyps"(4) Suc_diff_Suc \<open>1 < deg\<close> \<open>high x (deg div 2) < 2 ^ m\<close> diff_zero le_less_trans naive_member.simps(3) zero_le_one)
    ultimately show ?case
      using both_member_options_def by blast
  next
    case (3 n m)
    hence "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) \<or> 
           naive_member (treeList ! (high x (deg div 2))) (low x (deg div 2))"
      using assms(3) both_member_options_def by auto
    moreover  hence "deg > 1"
      by (metis "3.hyps"(1) "3.hyps"(2) "3.hyps"(4) "3.hyps"(5) "3.hyps"(6) One_nat_def Suc_lessI add_Suc add_gr_0 add_self_div_2 deg_not_0 le_imp_less_Suc plus_1_eq_Suc set_n_deg_not_0)
    moreover have "high x (deg div 2)<2^m"
      by (smt "3.hyps"(5) "3.hyps"(6) div_eq_0_iff add_Suc_right add_self_div_2 assms(2) diff_Suc_1 div_exp_eq div_mult_self1_is_m even_Suc high_def odd_add odd_two_times_div_two_nat one_add_one plus_1_eq_Suc power_not_zero zero_less_Suc)
    moreover have "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                   \<Longrightarrow> membermima (Node info deg treeList summary) x" using membermima.simps(5)[of "deg-1" treeList summary x]
      using "3.hyps"(4) "3.hyps"(9) \<open>1 < deg\<close> \<open>high x (deg div 2) < 2 ^ m\<close> zero_le_one by fastforce
    moreover have "naive_member  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                   \<Longrightarrow> naive_member (Node info deg treeList summary) x"
      by (smt "3.hyps"(4) Suc_diff_Suc \<open>1 < deg\<close> \<open>high x (deg div 2) < 2 ^ m\<close> diff_zero le_less_trans naive_member.simps(3) zero_le_one)
    ultimately show ?case
      using both_member_options_def by blast
  next
    case (4 n m mi ma)
    hence "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) \<or> 
           naive_member (treeList ! (high x (deg div 2))) (low x (deg div 2))"
      using assms(3) both_member_options_def by auto
    moreover  hence "deg > 1" 
      using "4.hyps"(2) "4.hyps"(5) "4.hyps"(6) deg_not_0 by force
    moreover have "high x (deg div 2)<2^m"
      by (metis "4.hyps"(5) "4.hyps"(6) div_eq_0_iff add_self_div_2 assms(2) div_exp_eq high_def power_not_zero)
    moreover have "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                   \<Longrightarrow> membermima (Node info deg treeList summary) x" using membermima.simps(5)[of "deg-1" treeList summary x]
      by (smt "4.hyps"(12) "4.hyps"(4) Suc_diff_Suc calculation(2) calculation(3) diff_zero le_less_trans membermima.simps(4) zero_le_one) 
    moreover have "naive_member  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                    \<Longrightarrow> naive_member (Node info deg treeList summary) x"
      by (metis "4.hyps"(4) calculation(2) calculation(3) gr_implies_not0 naive_member.simps(3) old.nat.exhaust)  ultimately show ?case
      using both_member_options_def by blast
  next
    case (5 n m mi ma)
    hence "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) \<or> 
           naive_member (treeList ! (high x (deg div 2))) (low x (deg div 2))"
      using assms(3) both_member_options_def by auto
    moreover  hence "deg > 1"
      by (metis "5.hyps"(1) "5.hyps"(2) "5.hyps"(4) "5.hyps"(5) "5.hyps"(6) One_nat_def Suc_lessI add_Suc add_gr_0 add_self_div_2 deg_not_0 le_imp_less_Suc plus_1_eq_Suc set_n_deg_not_0)
    moreover have "high x (deg div 2)<2^m" 
      by (metis "5.hyps"(5) "5.hyps"(6) div_eq_0_iff add_Suc_right add_self_div_2 assms(2) div_exp_eq even_Suc_div_two even_add high_def nat.simps(3) power_not_zero)
    moreover have "membermima  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                    \<Longrightarrow> membermima (Node info deg treeList summary) x" using membermima.simps(5)[of "deg-1" treeList summary x]
      by (smt "5.hyps"(12) "5.hyps"(4) Suc_diff_Suc calculation(2) calculation(3) diff_zero le_less_trans membermima.simps(4) zero_le_one)  
    moreover have "naive_member  (treeList ! (high x (deg div 2))) (low x (deg div 2)) 
                     \<Longrightarrow> naive_member (Node info deg treeList summary) x"
      using "5.hyps"(4) "5.hyps"(5) "5.hyps"(6) calculation(3) by auto
    ultimately show ?case
      using both_member_options_def by blast
  qed
qed

lemma exp_split_high_low: assumes "x < 2^(n+m)" and "n > 0" and "m> 0" 
  shows "high x n < 2^m" and "low x n < 2^n"
  using assms by (simp_all add: high_bound_aux low_def)

lemma low_inv: assumes "x< 2^n " shows "low (y*2^n + x) n = x" unfolding low_def 
  by (simp add: assms)

lemma high_inv: assumes "x< 2^n " shows "high (y*2^n + x) n = y" unfolding high_def 
  by (simp add: assms)

lemma both_member_options_from_chilf_to_complete_tree:
  assumes "high x (deg div 2) < length treeList" and "deg \<ge>1" and "both_member_options (treeList ! ( high x (deg div 2))) (low x (deg div 2))"
  shows "both_member_options (Node (Some (mi, ma)) deg treeList summary) x" 
proof-
  have "membermima (treeList ! ( high x (deg div 2))) (low x (deg div 2)) \<or>
        naive_member (treeList ! ( high x (deg div 2))) (low x (deg div 2))" using assms 
    using both_member_options_def by blast
  moreover  have "membermima (treeList ! ( high x (deg div 2))) (low x (deg div 2)) \<Longrightarrow>
        membermima (Node (Some (mi, ma)) deg treeList summary) x" 
    using membermima.simps(4)[of mi ma "deg-1" treeList summary x]
    by (metis Suc_1 Suc_leD assms(1) assms(2) le_add_diff_inverse plus_1_eq_Suc)
  moreover have "naive_member (treeList ! ( high x (deg div 2))) (low x (deg div 2)) \<Longrightarrow>
        naive_member (Node (Some (mi, ma)) deg treeList summary) x" 
    using naive_member.simps(3)[of "Some (mi, ma)" "deg-1" treeList summary x] 
    by (metis Suc_1 Suc_leD assms(1) assms(2) le_add_diff_inverse plus_1_eq_Suc)
  ultimately show ?thesis
    using both_member_options_def by blast
qed

lemma both_member_options_from_complete_tree_to_child:
  assumes "deg \<ge>1" and  "both_member_options (Node (Some (mi, ma)) deg treeList summary) x" 
  shows "both_member_options (treeList ! ( high x (deg div 2))) (low x (deg div 2)) \<or> x = mi \<or> x = ma" 
proof-
  have "naive_member (Node (Some (mi, ma)) deg treeList summary) x \<or>
       membermima (Node (Some (mi, ma)) deg treeList summary) x " 
    using assms(2) both_member_options_def by auto
  moreover have " naive_member (Node (Some (mi, ma)) deg treeList summary) x
                   \<Longrightarrow> naive_member (treeList ! ( high x (deg div 2))) (low x (deg div 2))" 
    using naive_member.simps(3)[of "Some (mi, ma)" "deg-1" treeList summary x] 
    by (metis assms(1) le_add_diff_inverse plus_1_eq_Suc)
  moreover have " membermima (Node (Some (mi, ma)) deg treeList summary) x
                  \<Longrightarrow> membermima (treeList ! ( high x (deg div 2))) (low x (deg div 2))\<or> x = mi \<or> x = ma" 
    by (smt (z3) assms(1) le_add_diff_inverse membermima.simps(4) plus_1_eq_Suc)
  ultimately show ?thesis 
    using both_member_options_def by presburger
qed

lemma pow_sum: "(divide::nat \<Rightarrow> nat \<Rightarrow> nat) ((2::nat) ^((a::nat)+(b::nat))) (2^a) = 2^b" 
  by (induction a) simp+

fun elim_dead::"VEBT \<Rightarrow> enat \<Rightarrow> VEBT" where
"elim_dead (Leaf a b) _ = Leaf a b "|
"elim_dead (Node info deg treeList summary) \<infinity> = 
 (Node info deg (map (\<lambda> t. elim_dead t (enat (2^(deg div 2)))) treeList)
 (elim_dead summary \<infinity>))"|
"elim_dead  (Node info deg treeList summary) (enat l) =
 (Node info deg (take (l div (2^(deg div 2))) (map (\<lambda> t. elim_dead t (enat (2^(deg div 2))))treeList)) 
                       (elim_dead summary ((enat (l div (2^(deg div 2))))))) "

lemma elimnum: "invar_vebt (Node info deg treeList summary) n \<Longrightarrow> 
     elim_dead (Node info deg treeList summary) (enat ((2::nat)^n)) = (Node info deg treeList summary)"
proof(induction rule: invar_vebt.induct)
  case (1 a b)
  then show ?case
    by simp
next
  case (2 treeList n summary m deg)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "2.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      using "2.IH"(1) by blast
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList" 
    by (simp add: "2.IH"(1) map_idI)
  have "deg div 2 = n" 
    by (simp add: "2.hyps"(3) "2.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "2.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "2"(4) by simp
  moreover hence " ( elim_dead summary ((enat ((2^deg) div (2^(deg div 2)))))) = summary" 
    using "2.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(3)[of None deg treeList summary "2^deg"]
    using \<open>deg div 2 = n\<close> by metis
next
  case (3 treeList n summary m deg)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "3.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      using "3.IH"(1) by blast
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList" 
    by (simp add: "3.IH"(1) map_idI)
  have "deg div 2 = n" 
    by (simp add: "3.hyps"(3) "3.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "3.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "3"(4) by simp
  moreover hence " ( elim_dead summary ((enat ((2^deg) div (2^(deg div 2)))))) = summary" using "3.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(3)[of None deg treeList summary "2^deg"]
    using \<open>deg div 2 = n\<close> by metis
next
  case (4 treeList n summary m deg mi ma)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "4.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      using "4.IH"(1) by blast
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList" 
    by (simp add: "4.IH"(1) map_idI)
  have "deg div 2 = n" 
    by (simp add: "4.hyps"(3) "4.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "4.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "4"(4) by simp
  moreover hence " ( elim_dead summary ((enat ((2^deg) div (2^(deg div 2)))))) = summary" using "4.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(3)[of "Some (mi, ma)" deg treeList summary "2^deg"]
    using \<open>deg div 2 = n\<close> by metis
next
  case (5 treeList n summary m deg mi ma)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "5.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      using "5.IH"(1) by blast
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList" 
    by (simp add: "5.IH"(1) map_idI)
  have "deg div 2 = n" 
    by (simp add: "5.hyps"(3) "5.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "5.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "5"(4) by simp
  moreover hence " ( elim_dead summary ((enat ((2^deg) div (2^(deg div 2)))))) = summary" using "5.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(3)[of "Some (mi, ma)" deg treeList summary "2^deg"]
    using \<open>deg div 2 = n\<close> by metis
qed

lemma elimcomplete: "invar_vebt (Node info deg treeList summary) n \<Longrightarrow> 
      elim_dead (Node info deg treeList summary) \<infinity> = (Node info deg treeList summary)"
proof(induction rule: invar_vebt.induct)
  case (1 a b)
  then show ?case
    by simp
next
  case (2 treeList n summary m deg)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "2.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      apply(cases "(treeList ! i)")
       apply (smt (z3) "2.IH"(1) \<open>treeList ! i \<in> set treeList\<close> elim_dead.simps(1) elimnum invar_vebt.cases)+
      done
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList"
    by (metis "2.hyps"(2) in_set_conv_nth map_idI)
  have "deg div 2 = n" 
    by (simp add: "2.hyps"(3) "2.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "2.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "2"(4) by simp
  moreover hence " ( elim_dead summary \<infinity>) = summary" using "2.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(2)[of None  deg treeList summary]
    using \<open>deg div 2 = n\<close> b by presburger
next
  case (3 treeList n summary m deg)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "3.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      apply(cases "(treeList ! i)")
       apply (smt (z3) "3.IH"(1) \<open>treeList ! i \<in> set treeList\<close> elim_dead.simps(1) elimnum invar_vebt.cases)+
      done
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList"
    by (metis "3.hyps"(2) in_set_conv_nth map_idI)
  have "deg div 2 = n" 
    by (simp add: "3.hyps"(3) "3.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "3.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "3"(4) by simp
  moreover hence " ( elim_dead summary \<infinity>) = summary" using "3.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(2)[of None  deg treeList summary]
    using \<open>deg div 2 = n\<close> b by presburger
next
  case (4 treeList n summary m deg mi ma)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "4.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      apply(cases "(treeList ! i)")
       apply (smt (z3) "4.IH"(1) \<open>treeList ! i \<in> set treeList\<close> elim_dead.simps(1) elimnum invar_vebt.cases)+
      done
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList"
    by (metis "4.hyps"(2) in_set_conv_nth map_idI)
  have "deg div 2 = n" 
    by (simp add: "4.hyps"(3) "4.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "4.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "4"(4) by simp
  moreover hence " ( elim_dead summary \<infinity>) = summary" using "4.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(2)[of "Some (mi, ma)"  deg treeList summary]
    using \<open>deg div 2 = n\<close> b by presburger
next
  case (5 treeList n summary m deg mi ma)
  have a:"i < 2^m \<longrightarrow> (elim_dead (treeList ! i) (enat( 2^n)) = treeList ! i)" for i
  proof
    assume  "i < 2^m"
    hence "treeList ! i \<in> set treeList" 
      by (simp add: "5.hyps"(2))
    thus "elim_dead (treeList ! i) (enat (2 ^ n)) = treeList ! i" 
      apply(cases "(treeList ! i)")
       apply (smt (z3) "5.IH"(1) \<open>treeList ! i \<in> set treeList\<close> elim_dead.simps(1) elimnum invar_vebt.cases)+
      done
  qed
  hence b:"map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList = treeList"
    by (metis "5.hyps"(2) in_set_conv_nth map_idI)
  have "deg div 2 = n" 
    by (simp add: "5.hyps"(3) "5.hyps"(4))
  hence "(2^m ::nat) = ( (2^deg) div (2^(deg div 2))::nat) " 
    using "5.hyps"(4) pow_sum by metis 
  hence "take (2^deg div (2^(deg div 2)))(map (\<lambda> t. elim_dead t (enat (2 ^ n))) treeList) = treeList"
    using b "5"(4) by simp
  moreover hence " ( elim_dead summary \<infinity>) = summary" using "5.IH"(2) 
    by (metis \<open>2 ^ m = 2 ^ deg div 2 ^ (deg div 2)\<close>)
  ultimately show ?case using  elim_dead.simps(2)[of "Some (mi, ma)"  deg treeList summary]
    using \<open>deg div 2 = n\<close> b by presburger
qed

end
end
