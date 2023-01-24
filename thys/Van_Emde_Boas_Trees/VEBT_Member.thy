(*by Ammer*)
theory VEBT_Member imports VEBT_Definitions
begin


section \<open>Member Function\<close>

context begin
interpretation VEBT_internal .

fun vebt_member :: "VEBT  \<Rightarrow> nat \<Rightarrow> bool" where
  "vebt_member (Leaf a b) x = (if x = 0 then a else if x = 1 then b else False)"|
  "vebt_member (Node None _ _ _) x = False"|
  "vebt_member (Node _ 0 _ _) x = False"|
  "vebt_member (Node _ (Suc 0) _ _) x = False"|
  "vebt_member (Node (Some (mi, ma)) deg treeList summary) x = (
    if x = mi then True else 
    if x = ma then True else 
    if x < mi then False else 
    if x > ma then False else (
     let h = high x (deg div 2);
         l = low x (deg div 2) in(
          if h < length treeList 
          then vebt_member (treeList ! h) l 
          else False))) "

end          
          
context VEBT_internal begin
          
lemma member_inv: 
  assumes "vebt_member  (Node (Some (mi, ma)) deg treeList summary) x " 
  shows "deg \<ge> 2 \<and>
         (x = mi \<or> x = ma \<or> (x < ma \<and> x > mi \<and>  high x (deg div 2) < length treeList \<and>
                                   vebt_member (treeList ! ( high x (deg div 2))) (low x (deg div 2))))"
proof(cases deg)
  case 0
  then show ?thesis using vebt_member.simps(3)[of "(mi, ma)" treeList summary x]
    using assms by blast
  next
  case (Suc nat)
  hence "deg = Suc nat" by simp
  then show ?thesis proof(cases nat)
    case 0
    then show ?thesis
      using Suc assms by auto
    next
    case (Suc nata)
    hence "deg \<ge> 2"
      by (simp add: \<open>deg = Suc nat\<close>)
    then show ?thesis 
      by (metis vebt_member.simps(5) Suc \<open>deg = Suc nat\<close> assms linorder_neqE_nat)
  qed
qed
  

definition bit_concat::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"bit_concat h l d = h*2^d + l"

lemma bit_split_inv: "bit_concat (high x d) (low x d) d = x" 
  unfolding bit_concat_def high_def low_def 
  by presburger

definition set_vebt'::"VEBT \<Rightarrow> nat set" where
  "set_vebt' t = {x. vebt_member t x}"

lemma Leaf_0_not: assumes "invar_vebt (Leaf a b) 0 "shows " False"
proof-
  from assms show ?thesis 
  proof(cases)
  qed
qed

lemma  valid_0_not: "invar_vebt t 0 \<Longrightarrow> False"
proof(induction t)
  case (Node info deg treeList summary)
  from this(3) have  "length treeList > 0" 
    apply cases 
    apply auto 
    done
  then obtain t where "t \<in> set treeList" by fastforce
  from Node(3) obtain n where "invar_vebt t n" 
    apply cases
    using Node.IH(2) apply auto 
    done
  from  Node(3) have  "n \<le> 0" 
    apply cases
    using Node.IH(2) apply auto 
    done
  hence "n = 0" by blast
  then show ?case 
    using Node.IH(1) \<open>t \<in> set treeList\<close> \<open>invar_vebt t n\<close> by blast
next
  case (Leaf x1 x2)
  then show ?case 
    using Leaf_0_not by blast
qed

theorem valid_tree_deg_neq_0: "(\<not> invar_vebt t 0)"
  using valid_0_not by blast

lemma deg_1_Leafy:  "invar_vebt t n \<Longrightarrow> n = 1 \<Longrightarrow> \<exists> a b. t = Leaf a b" 
  apply(induction rule: invar_vebt.induct)
  apply simp
  apply presburger
  apply (metis (full_types) Suc_eq_plus1 add_cancel_right_left in_set_replicate list.map_cong0 map_replicate_const nat_neq_iff not_add_less2 numeral_1_eq_Suc_0 numeral_2_eq_2 numerals(1) order_less_irrefl power_eq_0_iff valid_tree_deg_neq_0 zero_less_numeral)
  apply (metis odd_add odd_one)
  by (metis Suc_eq_plus1 add_cancel_right_left in_set_replicate list.map_cong0 map_replicate_const nat_neq_iff not_add_less2 numeral_2_eq_2 power_eq_0_iff valid_tree_deg_neq_0)

lemma deg_1_Leaf: "invar_vebt t 1 \<Longrightarrow>  \<exists> a b. t = Leaf a b"
  using deg_1_Leafy by blast

corollary deg1Leaf: "invar_vebt t 1 \<longleftrightarrow>  (\<exists> a b. t = Leaf a b)"
  using deg_1_Leaf invar_vebt.intros(1) by auto

lemma deg_SUcn_Node: assumes "invar_vebt tree (Suc (Suc n)) " shows 
                " \<exists> info treeList s. tree = Node info (Suc (Suc n)) treeList s" 
proof-
  from assms show ?thesis apply(cases) 
    apply blast+
   done
qed

lemma "invar_vebt (Node info deg treeList summary) deg \<Longrightarrow> deg > 1"
  by (metis VEBT.simps(4) deg_1_Leafy less_one linorder_neqE_nat valid_tree_deg_neq_0)

lemma deg_deg_n: assumes "invar_vebt (Node info deg treeList summary) n "shows" deg = n" 
proof-
  from assms show ?thesis proof(cases)
  qed blast+
qed

lemma member_valid_both_member_options: 
  "invar_vebt tree n \<Longrightarrow> vebt_member tree x \<Longrightarrow> (naive_member tree x \<or> membermima tree x)"
proof(induction tree n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
    using vebt_member.simps(1) naive_member.simps(1) by blast
next
  case (2 treeList n summary m deg)
  then show ?case by simp
next
  case (3 treeList n summary m deg)
  then show ?case 
    using vebt_member.simps(2) by blast
next
  case (4 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    using member_inv by blast
  then show ?case proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis
      by (metis (full_types) "4"(12) vebt_member.simps(3) membermima.simps(4) old.nat.exhaust)
  next
    case False
    hence 1:"mi < x \<and> x < ma \<and> (high x (deg div 2 )) < length treeList \<and> vebt_member (treeList ! (high x (deg div 2))) (low x (deg div 2))"
      using member_inv[of mi ma deg treeList summary x] "4"(12) by blast
    hence " (treeList ! (high x (deg div 2))) \<in> set treeList" 
      by (metis in_set_member inthall)
    hence "both_member_options  (treeList ! (high x (deg div 2))) (low x (deg div 2))" 
      using "1" "4.IH"(1) both_member_options_def by blast
    then show ?thesis 
      by (smt "1" "4"(1) "4"(6) \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> membermima.simps(4) naive_member.simps(3) old.nat.exhaust valid_tree_deg_neq_0 zero_eq_add_iff_both_eq_0)
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "deg \<ge> 2"
    using member_inv by presburger
  then show ?case proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis
      by (metis (full_types) "5"(12) vebt_member.simps(3) membermima.simps(4) old.nat.exhaust)
  next
    case False
    hence 1:"mi < x \<and> x < ma \<and> (high x (deg div 2 )) < length treeList \<and> vebt_member (treeList ! (high x (deg div 2))) (low x (deg div 2))"
      using member_inv[of mi ma deg treeList summary x] "5"(12) by blast
    hence " (treeList ! (high x (deg div 2))) \<in> set treeList" 
      by (metis in_set_member inthall)
    hence "both_member_options  (treeList ! (high x (deg div 2))) (low x (deg div 2))" 
      using "1" "5.IH"(1) both_member_options_def by blast
    then show ?thesis 
      by (smt "1" "5"(1) "5"(6) \<open>treeList ! high x (deg div 2) \<in> set treeList\<close> membermima.simps(4) naive_member.simps(3) old.nat.exhaust valid_tree_deg_neq_0 zero_eq_add_iff_both_eq_0)
  qed
qed
   
lemma  member_bound: "vebt_member tree x \<Longrightarrow> invar_vebt tree n  \<Longrightarrow> x < 2^n"
proof(induction tree x arbitrary: n rule: vebt_member.induct)
  case (1 a b x)
  then show ?case  by (metis vebt_member.simps(1) One_nat_def le_neq_implies_less nat_power_eq_Suc_0_iff 
                       numeral_eq_iff numerals(1) one_le_numeral one_le_power semiring_norm(85) valid_tree_deg_neq_0 
                       zero_less_numeral zero_less_power)
next
  case (2 uu uv uw x)
  then show ?case by simp
next
  case (3 v uy uz x)
  then show ?case by simp
next
  case (4 v vb vc x)
  then show ?case by simp
next
  case (5 mi ma va treeList summary x)
  hence 111: "n =  Suc (Suc va)" 
    using deg_deg_n by fastforce
  hence "ma < 2^n"
    using "5.prems"(2) mi_ma_2_deg by blast
  then show ?case
    by (metis "5.prems"(1) "5.prems"(2) le_less_trans less_imp_le_nat member_inv mi_ma_2_deg)
qed

theorem inrange: assumes "invar_vebt t n" shows " set_vebt' t \<subseteq> {0..2^n-1}"
proof
  fix x
  assume "x \<in> set_vebt' t"
  hence "vebt_member t x" 
    using set_vebt'_def by auto
    hence "x < 2^n" 
      using assms member_bound by blast
    then show "x \<in> {0..2^n-1}" by simp
  qed

theorem buildup_gives_empty: "set_vebt' (vebt_buildup n) = {}" 
  unfolding set_vebt'_def
  by (metis Collect_empty_eq vebt_member.simps(1) vebt_member.simps(2) vebt_buildup.elims)

fun minNull::"VEBT \<Rightarrow> bool" where
"minNull (Leaf False False) = True"|
"minNull (Leaf _ _ ) = False"|
"minNull (Node None _ _ _) = True"|
"minNull (Node (Some _) _ _ _) = False"

lemma min_Null_member: "minNull t \<Longrightarrow> \<not> vebt_member t x"
  apply(induction t) 
  using vebt_member.simps(2) minNull.elims(2) apply blast
  apply  auto
  done

lemma not_min_Null_member: "\<not> minNull t \<Longrightarrow> \<exists> y. both_member_options t y"
proof(induction t)
  case (Node info deg treeList summary)
  obtain mi ma where "info = Some(mi , ma)"
    by (metis Node.prems minNull.simps(4) not_None_eq surj_pair)
  then show ?case
    by (metis (full_types) both_member_options_def membermima.simps(3) membermima.simps(4) not0_implies_Suc)
next
  case (Leaf x1 x2)
  then show ?case 
    by (metis (full_types) both_member_options_def minNull.simps(1) naive_member.simps(1) zero_neq_one)
qed

lemma valid_member_both_member_options: "invar_vebt t n \<Longrightarrow>  both_member_options t x \<Longrightarrow> vebt_member t x"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case 
    by (simp add: both_member_options_def)
next
  case (2 treeList n summary m deg)
  hence 0: " ( \<forall> t \<in> set treeList. invar_vebt t n) " and 1:" invar_vebt summary n" and 2:" length treeList = 2^n" and
    3:" deg = 2*n" and 4:" (\<nexists> i. both_member_options summary i)" and 5:" (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y) " and 6: "n> 0"
          apply blast+
          apply (auto simp add: "2.hyps"(3) "2.hyps")  
          using "2.hyps"(1) "2.hyps"(3) neq0_conv valid_tree_deg_neq_0 by blast
  have "both_member_options (Node None deg treeList summary) x \<Longrightarrow> False"
  proof-
    assume "both_member_options (Node None deg treeList summary) x"
    hence "naive_member  (Node None deg treeList summary) x \<or> membermima  (Node None deg treeList summary) x" unfolding both_member_options_def by simp
    then show False 
    proof(cases  "naive_member  (Node None deg treeList summary) x")
      case True
      hence "high x n < length treeList \<and> naive_member (treeList ! (high x n)) (low x n)"
        by (metis "1" "2.hyps"(3) "2.hyps"(4) add_cancel_right_left add_self_div_2 naive_member.simps(3) old.nat.exhaust valid_tree_deg_neq_0)
      then show ?thesis 
        by (metis "5" both_member_options_def in_set_member inthall)
    next
      case False
      hence "membermima  (Node None deg treeList summary) x" 
        using \<open>naive_member (Node None deg treeList summary) x \<or> membermima (Node None deg treeList summary) x\<close> by blast
      moreover have "Suc (deg-1) =deg"
        by (simp add: "2.hyps"(4) "6")
      moreover hence "(let pos = high x (deg div 2) in if pos < length treeList then membermima (treeList ! pos) (low x (Suc (deg - 1) div 2)) else False)"
        using calculation(1) membermima.simps(5) by metis
      moreover hence " if  high x (deg div 2) < length treeList then membermima (treeList ! (  high x (deg div 2))) (low x(deg div 2)) else False"
        using calculation(2) by metis
      ultimately
      have " high x (deg div 2) < length treeList \<and> membermima (treeList ! (high x n)) (low x n)"
        by (metis "2.hyps"(3) "2.hyps"(4) add_self_div_2)
      then show ?thesis using "2.IH" "5" both_member_options_def in_set_member inthall
        by (metis "2.hyps"(3) "2.hyps"(4) add_self_div_2)
    qed
  qed
  then show ?case
    by (simp add: "2.prems")
next
  case (3 treeList n summary m deg)
  hence 0: " ( \<forall> t \<in> set treeList. invar_vebt t n) " and 1:" invar_vebt summary m" and 2:" length treeList = 2^m" and
    3:" deg = n+m" and 4:" (\<nexists> i. both_member_options summary i)" and 5:" (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y) " and 6: "n> 0" and 7: "m> 0"
    and 8: "n+1 = m"
            apply blast+
            apply (metis (full_types) "3.IH"(1) "3.hyps"(2) in_set_member inthall neq0_conv power_eq_0_iff valid_tree_deg_neq_0 zero_neq_numeral)
            apply (simp add: "3.hyps"(3))
            by (simp add: "3.hyps"(3))
  have "both_member_options (Node None deg treeList summary) x \<Longrightarrow> False"
  proof-
    assume "both_member_options (Node None deg treeList summary) x"
    hence "naive_member  (Node None deg treeList summary) x \<or> membermima  (Node None deg treeList summary) x" unfolding both_member_options_def by simp
    then show False 
    proof(cases  "naive_member  (Node None deg treeList summary) x")
      case True
      hence "high x n < length treeList \<and> naive_member (treeList ! (high x n)) (low x n)"
        by (metis "3" "3.hyps"(3) add_Suc_right add_self_div_2 even_Suc_div_two naive_member.simps(3) odd_add)
      then show ?thesis 
        by (metis "5" both_member_options_def in_set_member inthall)
    next
      case False
      hence "membermima  (Node None deg treeList summary) x" 
        using \<open>naive_member (Node None deg treeList summary) x \<or> membermima (Node None deg treeList summary) x\<close> by blast
      moreover have "Suc (deg-1) =deg"
        by (simp add: "3" "3.hyps"(3))
      moreover hence "(let pos = high x (deg div 2) in if pos < length treeList then membermima (treeList ! pos) (low x (Suc (deg - 1) div 2)) else False)"
        using calculation(1) membermima.simps(5) by metis
      moreover hence 11:" if  high x (deg div 2) < length treeList then membermima (treeList ! (  high x (deg div 2))) (low x(deg div 2)) else False"
        using calculation(2) by metis
      ultimately
      have " high x (deg div 2) < length treeList \<and> membermima (treeList ! (high x n)) (low x n)"
        by (metis "3" "3.hyps"(3) add_Suc_right add_self_div_2 even_Suc_div_two odd_add)
      then show ?thesis using "3.IH" "5" both_member_options_def in_set_member inthall 11 by metis
    qed
  qed
  then show ?case
    using "3.prems" by blast
next
  case (4 treeList n summary m deg mi ma)
  hence 0: "( \<forall> t \<in> set treeList. invar_vebt t n)" and 1: " invar_vebt summary n" and 2:"length treeList = 2^n" and 3:" deg = n+m" and "n=m" and
    4: "(\<forall> i < 2^n. (\<exists> y. both_member_options (treeList ! i) y) \<longleftrightarrow> ( both_member_options summary i))" and 
    5: "(mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y))" and 6:"mi \<le> ma  \<and> ma < 2^deg" and
    7: "(mi \<noteq> ma \<longrightarrow> (\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)))"
    using "4.prems" by auto
  hence "n>0"
    by (metis neq0_conv valid_tree_deg_neq_0)
  then show ?case proof(cases "x = mi \<or> x = ma")
    case True
    hence xmimastmt: "x = mi \<or> x=ma" by simp
    then show ?thesis using vebt_member.simps(5)[of mi ma "deg-2" treeList summary x]
      by (metis "3" "4.hyps"(3) \<open>0 < n\<close> add_diff_inverse_nat add_numeral_left add_self_div_2 div_if nat_neq_iff numerals(1) plus_1_eq_Suc semiring_norm(2))
  next
    case False
    hence xmimastmt: "x \<noteq> mi \<and> x\<noteq>ma" by simp
    hence "mi = ma \<Longrightarrow> False" 
    proof-
      assume "mi = ma"
      hence astmt: "(\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y)" using 5 by simp  
      have bstmt: "both_member_options  (Node (Some (mi, ma)) deg treeList summary) x" 
        by (simp add: "4.prems")
      then show False 
      proof(cases  "naive_member  (Node (Some (mi, ma)) deg treeList summary) x")
        case True
        hence "high x n < length treeList \<and> naive_member (treeList ! (high x n)) (low x n)"
          by (metis (no_types, opaque_lifting) "3" "4.hyps"(1) "4.hyps"(3) add_self_div_2 naive_member.simps(3) old.nat.exhaust valid_0_not zero_eq_add_iff_both_eq_0)
        then show ?thesis
          by (metis "5" \<open>mi = ma\<close> both_member_options_def in_set_member inthall)
      next
        case False
        hence "membermima  (Node (Some (mi, ma)) deg treeList summary) x" using bstmt unfolding both_member_options_def by blast
        hence " x = mi \<or> x = ma \<or> (if high x n < length treeList then  membermima (treeList ! (high x n)) (low x n) else False)" 
          using membermima.simps(4)[of mi ma "deg-1" treeList summary x] 
          by (metis "3" "4.hyps"(3) One_nat_def Suc_diff_Suc \<open>0 < n\<close> add_gr_0 add_self_div_2 diff_zero)
        hence " high x n < length treeList \<and> membermima (treeList ! (high x n)) (low x n)" using xmimastmt 
          by presburger
        then show ?thesis using both_member_options_def in_set_member inthall membermima.simps(4)[of mi ma n treeList summary x] astmt
          by metis
      qed
    qed
    hence "mi \<noteq> ma " by blast
    hence followstmt: "(\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma))"
      using 7 by simp
    have 10:"high x n < length treeList \<and> 
       (naive_member (treeList ! (high x n)) (low x n) \<or> membermima (treeList ! (high x n)) (low x n) )"
      by (smt "3" "4.hyps"(3) "4.prems" False One_nat_def Suc_leI \<open>0 < n\<close> add_gr_0 add_self_div_2 both_member_options_def le_add_diff_inverse membermima.simps(4) naive_member.simps(3) plus_1_eq_Suc)
    hence 11:"both_member_options (treeList ! (high x n)) (low x n)" 
      by (simp add: both_member_options_def)
    have 12:"high x n< 2^m" 
      using "10" "4.hyps"(2) by auto
    hence "mi < x \<and> x < ma" proof-
      have "(\<forall> y. (high y n = (high x n) \<and> both_member_options (treeList ! (high y n)) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)" 
        using "12" followstmt by auto
      then show ?thesis
        using "11" False order.not_eq_order_implies_strict by blast
    qed
    have "vebt_member (treeList ! (high x n)) (low x n)"
      by (metis"10" "11" "4.IH"(1) in_set_member inthall)
    then show ?thesis
      by (smt "10" "11" "12" "3" "4.hyps"(3) vebt_member.simps(5) One_nat_def Suc_leI \<open>0 < n\<close> add_Suc_right add_self_div_2 followstmt le_add_diff_inverse le_imp_less_Suc not_less_eq not_less_iff_gr_or_eq plus_1_eq_Suc)
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence 0: "( \<forall> t \<in> set treeList. invar_vebt t n)" and 1: " invar_vebt summary m" and 2:"length treeList = 2^m" and 3:" deg = n+m" and "Suc n=m" and
    4: "(\<forall> i < 2^m. (\<exists> y. both_member_options (treeList ! i) y) \<longleftrightarrow> ( both_member_options summary i))" and 
    5: "(mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y))" and 6:"mi \<le> ma  \<and> ma < 2^deg" and
    7: "(mi \<noteq> ma \<longrightarrow> (\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)))"
    using "5.prems" by auto
  hence "n>0"
    by (metis "5.hyps"(3) in_set_member inthall neq0_conv power_Suc0_right valid_tree_deg_neq_0 zero_neq_numeral)
  then show ?case proof(cases "x = mi \<or> x = ma")
    case True
    hence xmimastmt: "x = mi \<or> x=ma" by simp
    then show ?thesis using vebt_member.simps(5)[of mi ma "deg-2" treeList summary x]
      using "3" "5.hyps"(3) \<open>0 < n\<close> by auto
  next
    case False
    hence xmimastmt: "x \<noteq> mi \<and> x\<noteq>ma" by simp
    hence "mi = ma \<Longrightarrow> False" 
    proof-
      assume "mi = ma"
      hence astmt: "(\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y)" using 5 by simp  
      have bstmt: "both_member_options  (Node (Some (mi, ma)) deg treeList summary) x" 
        by (simp add: "5.prems")
      then show False 
      proof(cases  "naive_member  (Node (Some (mi, ma)) deg treeList summary) x")
        case True
        hence "high x n < length treeList \<and> naive_member (treeList ! (high x n)) (low x n)"
          by (metis "3" "5.hyps"(3) add_Suc_right add_self_div_2 even_Suc_div_two naive_member.simps(3) odd_add)
        then show ?thesis
          by (metis "5" \<open>mi = ma\<close> both_member_options_def in_set_member inthall)
      next
        case False
        hence "membermima  (Node (Some (mi, ma)) deg treeList summary) x" using bstmt unfolding both_member_options_def by blast
        hence " x = mi \<or> x = ma \<or> (if high x n < length treeList then  membermima (treeList ! (high x n)) (low x n) else False)" 
          using membermima.simps(4)[of mi ma "deg-1" treeList summary x]
          using "3" "5.hyps"(3) by auto
        hence " high x n < length treeList \<and> membermima (treeList ! (high x n)) (low x n)" using xmimastmt 
          by presburger
        then show ?thesis using both_member_options_def in_set_member inthall membermima.simps(4)[of mi ma n treeList summary x] astmt
          by metis
      qed
    qed
    hence "mi \<noteq> ma " by blast
    hence followstmt: "(\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma))"
      using 7 by simp
    have 10:"high x n < length treeList \<and> 
       (naive_member (treeList ! (high x n)) (low x n) \<or> membermima (treeList ! (high x n)) (low x n) )"
      by (smt "3" "5.hyps"(3) "5.prems" False add_Suc_right add_self_div_2 both_member_options_def even_Suc_div_two membermima.simps(4) naive_member.simps(3) odd_add)
    hence 11:"both_member_options (treeList ! (high x n)) (low x n)" 
      by (simp add: both_member_options_def)
    have 12:"high x n< 2^m" 
      using "10" "5.hyps"(2) by auto
    hence "mi < x \<and> x < ma" proof-
      have "(\<forall> y. (high y n = (high x n) \<and> both_member_options (treeList ! (high y n)) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)" 
        using "12" followstmt by auto
      then show ?thesis
        using "11" False order.not_eq_order_implies_strict by blast
    qed
    have "vebt_member (treeList ! (high x n)) (low x n)"
      by (metis "10" "11" "5.IH"(1) in_set_member inthall)
    then show ?thesis 
      by (smt "10" "11" "12" "3" "5.hyps"(3) vebt_member.simps(5) Suc_pred \<open>0 < n\<close> add_Suc_right add_self_div_2 even_Suc_div_two followstmt le_neq_implies_less not_less_iff_gr_or_eq odd_add)
  qed
qed

corollary both_member_options_equiv_member: assumes "invar_vebt t n"
  shows "both_member_options t x \<longleftrightarrow> vebt_member t x"
  using assms both_member_options_def member_valid_both_member_options valid_member_both_member_options by blast

lemma member_correct: "invar_vebt t n \<Longrightarrow> vebt_member t x \<longleftrightarrow> x \<in> set_vebt t "
  using both_member_options_equiv_member set_vebt_def  by auto

corollary set_vebt_set_vebt'_valid: assumes "invar_vebt t n" shows "set_vebt t =set_vebt' t"
  unfolding set_vebt_def set_vebt'_def
  apply auto 
  using assms valid_member_both_member_options apply auto[1]
  using assms both_member_options_equiv_member by auto

lemma set_vebt_finite: "invar_vebt t n \<Longrightarrow> finite (set_vebt' t)" 
  using finite_subset inrange by blast

lemma mi_eq_ma_no_ch:assumes "invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg " and " mi  = ma "
  shows  "(\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x ) \<and> (\<nexists> x. both_member_options summary x)"
proof-
  from assms(1) show ?thesis 
  proof(cases)
    case (4 n m)
    have 0:"\<forall>t\<in>set treeList. \<not> Ex (both_member_options t)" 
      by (simp add: "4"(7) assms(2))
    moreover have "both_member_options summary x \<Longrightarrow> False" for x
    proof-
      assume "both_member_options summary x "
      hence "vebt_member summary x" 
        using "4"(2) valid_member_both_member_options by auto
      moreover hence "x < 2^m" 
        using "4"(2) member_bound by auto
      ultimately have "\<exists> y. both_member_options (treeList ! (high x n)) y" 
        using  "0" "4"(3) "4"(4) "4"(6) \<open>both_member_options summary x\<close> inthall 
        by (metis nth_mem)
      then show ?thesis
        by (metis "0" "4"(3) "4"(4) div_eq_0_iff \<open>x < 2 ^ m\<close> high_def nth_mem zero_less_numeral zero_less_power)
    qed
    then show ?thesis 
      using calculation by blast
  next
    case (5 n m)
    have 0:"\<forall>t\<in>set treeList. \<not> Ex (both_member_options t)" 
      using "5"(7) assms(2) by blast
    moreover have "both_member_options summary x \<Longrightarrow> False" for x
    proof-
      assume "both_member_options summary x "
      hence "vebt_member summary x" 
        using "5"(2) valid_member_both_member_options by auto
      moreover hence "x < 2^m" 
        using "5"(2) member_bound by auto
      ultimately have "\<exists> y. both_member_options (treeList ! (high x n)) y" 
        using  "0" "5"(3) "5"(4) "5"(6) \<open>both_member_options summary x\<close> inthall 
        by (metis nth_mem)
      then show ?thesis 
        by (metis "0" "5"(3) "5"(6) \<open>both_member_options summary x\<close> \<open>x < 2 ^ m\<close> nth_mem)
    qed
    then show ?thesis 
      using calculation by blast
  qed
qed

end
end
