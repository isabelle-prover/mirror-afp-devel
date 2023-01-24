(*by Ammer*)
theory VEBT_Insert imports VEBT_Member
begin


section \<open>Insert Function\<close>

context begin
  interpretation VEBT_internal .

fun vebt_insert :: "VEBT \<Rightarrow> nat \<Rightarrow>VEBT" where
  "vebt_insert (Leaf a b) x = (if x=0 then Leaf True b else if x = 1 then Leaf a True else Leaf a b)"|
  "vebt_insert (Node info 0 ts s) x = (Node info 0 ts s)"|
  "vebt_insert (Node info (Suc 0) ts s) x = (Node info (Suc 0) ts s)"|
  "vebt_insert (Node None (Suc deg) treeList summary) x = 
              (Node (Some (x,x)) (Suc deg) treeList summary)"|
  "vebt_insert (Node (Some (mi,ma)) deg treeList summary) x = (     
     let xn = (if x < mi then mi else x); 
         minn = (if x < mi then x else mi);
         l  = low xn (deg div 2); 
         h = high xn (deg div 2) in ( 
         if h < length treeList \<and> \<not> (x = mi \<or> x = ma) then
                 Node (Some (minn, max xn ma)) deg (treeList[h:= vebt_insert (treeList ! h) l])
                        (if minNull (treeList ! h) then  vebt_insert summary h else summary)
         else  (Node (Some (mi, ma)) deg treeList summary)))"

end
         
context VEBT_internal begin
         
lemma insert_simp_norm: 
  assumes "high x (deg div 2) < length treeList " and  "(mi::nat)< x" and "deg\<ge> 2" and "x \<noteq> ma" 
  shows "vebt_insert (Node (Some (mi,ma)) deg treeList summary) x = 
                 Node (Some (mi, max x ma)) deg (treeList [(high x (deg div 2)):= vebt_insert (treeList ! (high x (deg div 2))) (low x (deg div 2))])
                       (if minNull (treeList ! (high x  (deg div 2))) then  vebt_insert summary (high x  (deg div 2)) else summary) " 
proof-
  have 11:"vebt_insert (Node (Some (mi,ma)) deg treeList summary) x = 
    (let xn = (if x < mi then mi else x); minn = (if x< mi then x else mi);
                  l= low xn (deg div 2); h = high xn (deg div 2)
                   in
              ( if h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                 Node (Some (minn, max xn ma)) deg (treeList [h:= vebt_insert (treeList ! h) l])
              (if minNull (treeList ! h) then  vebt_insert summary h else summary)
           else  (Node (Some (mi, ma)) deg treeList summary)))"
    using assms(3) vebt_insert.simps(5)[of mi ma "deg-2" treeList summary x]
    by (smt add_numeral_left le_add_diff_inverse numerals(1) plus_1_eq_Suc semiring_norm(2))
   have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x =
                 Node (Some (mi, max x ma)) deg (treeList[(high x (deg div 2)) := vebt_insert (treeList ! (high x (deg div 2))) (low x (deg div 2))])
                               (if minNull (treeList ! (high x (deg div 2))) then  vebt_insert summary (high x (deg div 2)) else summary)"
    using 11 apply (simp add: Let_def) 
    apply (auto simp add: If_def)
    using assms not_less_iff_gr_or_eq apply blast+
    done
  then show ?thesis by blast
qed

lemma insert_simp_excp: 
  assumes "high mi (deg div 2) < length treeList " and " (x::nat) < mi" and "deg\<ge> 2" and "x \<noteq> ma" 
  shows "vebt_insert (Node (Some (mi,ma)) deg treeList summary) x = 
                 Node (Some (x, max mi ma)) deg (treeList[(high mi  (deg div 2)) := vebt_insert (treeList ! (high mi  (deg div 2))) (low mi  (deg div 2))])
                 (if minNull (treeList ! (high mi  (deg div 2))) then  vebt_insert summary (high mi  (deg div 2)) else summary) " 
proof-
  have 11:"vebt_insert (Node (Some (mi,ma)) deg treeList summary) x = 
           ( let xn = (if x < mi then mi else x); minn = (if x< mi then x else mi);
                  l= low xn (deg div 2); h = high xn (deg div 2)
                   in
              ( if h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                 Node (Some (minn, max xn ma)) deg (treeList[h:=vebt_insert (treeList ! h) l])
                               (if minNull (treeList ! h) then  vebt_insert summary h else summary)
           else  (Node (Some (mi, ma)) deg treeList summary)))"
    using assms(3) vebt_insert.simps(5)[of mi ma "deg-2" treeList summary x]
    by (smt add_numeral_left le_add_diff_inverse numerals(1) plus_1_eq_Suc semiring_norm(2))
  have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x =
                 Node (Some (x, max mi ma)) deg ( treeList[ (high mi (deg div 2)) := vebt_insert (treeList ! (high mi (deg div 2))) (low mi (deg div 2))])
                               (if minNull (treeList ! (high mi (deg div 2))) then  vebt_insert summary (high mi (deg div 2)) else summary)"
   using 11 apply (simp add: Let_def) 
    apply (auto simp add: If_def)
    using assms not_less_iff_gr_or_eq apply blast+
    done
  then show ?thesis by blast
qed


lemma insert_simp_mima: assumes "x = mi \<or> x = ma" and "deg \<ge> 2" 
  shows "vebt_insert (Node (Some (mi,ma)) deg treeList summary) x =  (Node (Some (mi,ma)) deg treeList summary)"
proof -
  have 11:"vebt_insert (Node (Some (mi,ma)) deg treeList summary) x = 
    ( let xn = (if x < mi then mi else x); minn = (if x< mi then x else mi);
                  l= low xn (deg div 2); h = high xn (deg div 2)
                   in
              ( if h < length treeList \<and> \<not> (x = mi \<or> x = ma)then
                 Node (Some (minn, max xn ma)) deg (treeList[h:= vebt_insert (treeList ! h) l])
                               (if minNull (treeList ! h) then  vebt_insert summary h else summary)
    else  (Node (Some (mi, ma)) deg treeList summary)))" using assms vebt_insert.simps(5)[of mi ma "deg-2" treeList summary x]
    by (smt add_numeral_left le_add_diff_inverse numerals(1) plus_1_eq_Suc semiring_norm(2))
  then show ?thesis
    using assms(1) by auto   
qed 


lemma valid_insert_both_member_options_add: "invar_vebt t n \<Longrightarrow> x< 2^n \<Longrightarrow> both_member_options (vebt_insert t x) x"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case apply(cases x)
    by (auto simp add: both_member_options_def)
next
  case (2 treeList n summary m deg)
  hence "deg>1"
    using valid_tree_deg_neq_0 
    by (metis One_nat_def Suc_lessI add_gr_0 add_self_div_2 neq0_conv one_div_two_eq_zero)
  then show ?case using vebt_insert.simps(4)[of "deg-2" treeList summary x ] 
    by (smt Suc_1 Suc_leI add_numeral_left both_member_options_def le_add_diff_inverse membermima.simps(4) 
        numerals(1) plus_1_eq_Suc semiring_norm(2))
next
  case (3 treeList n summary m deg)
  hence "\<forall>t\<in>set treeList. invar_vebt t n" by blast
  hence "n > 0" using set_n_deg_not_0[of treeList n m] "3"(4)
    by linarith
  hence "deg \<ge> 2"
    by (simp add: "3.hyps"(3) "3.hyps"(4) Suc_leI)
  then show ?case using vebt_insert.simps(4)[of "deg-2" treeList summary x ] 
    by (smt Suc_1 Suc_leI add_numeral_left both_member_options_def le_add_diff_inverse membermima.simps(4) 
        numerals(1) plus_1_eq_Suc semiring_norm(2))
next
  case (4 treeList n summary m deg mi ma)
  hence "length treeList =2^n" by blast
  hence "high x n < length treeList"
    using "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) "4.prems" deg_not_0 exp_split_high_low(1) by auto
  hence "mi < 2^deg" 
    using "4.hyps"(7) "4.hyps"(8) le_less_trans by blast
  then show ?case 
  proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis using vebt_insert.simps(5)[of mi ma "deg-2" treeList summary x]
      by (smt "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) add_diff_inverse_nat add_numeral_left add_self_div_2 both_member_options_def div_if membermima.simps(4) numerals(1) plus_1_eq_Suc semiring_norm(2) valid_tree_deg_neq_0)
  next
    case False
    hence "\<not> (x = mi \<or> x = ma)" by simp
    then show ?thesis 
    proof(cases "x < mi")
      case True
      hence "high mi n < length treeList"
        using "4.hyps"(1) "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) \<open>mi < 2 ^ deg\<close> deg_not_0 exp_split_high_low(1) by auto
      hence "vebt_insert ( Node (Some (mi, ma)) deg treeList summary) x = 
                      Node (Some (x, max mi ma)) deg ( treeList[(high mi n):= vebt_insert (treeList ! (high mi n)) (low mi n)] )
                      (if minNull (treeList ! high mi n) then  vebt_insert summary (high mi n) else summary)" 
        by (metis "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) False True add_self_div_2 div_if insert_simp_excp not_less valid_tree_deg_neq_0)
      then show ?thesis
        by (smt "4.hyps"(1) "4.hyps"(4) Suc_pred add_diff_inverse_nat both_member_options_def membermima.simps(4) valid_tree_deg_neq_0 zero_eq_add_iff_both_eq_0)
    next
      case False
      hence "vebt_insert ( Node (Some (mi, ma)) deg treeList summary) x = 
                      Node (Some (mi, max x ma)) deg (treeList[ (high x n):=vebt_insert (treeList ! (high x n)) (low x n)])
                      (if minNull (treeList ! high x n) then  vebt_insert summary (high x n) else summary)" 
        by (metis "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) \<open>\<not> (x = mi \<or> x = ma)\<close> \<open>high x n < length treeList\<close> add_self_div_2 div_if insert_simp_norm linorder_neqE_nat not_less valid_tree_deg_neq_0)
      have "low x n < 2^n \<and> high x n < 2^n" 
        using "4.hyps"(2) "4.hyps"(3) \<open>high x n < length treeList\<close> low_def by auto
      have "invar_vebt (treeList ! (high x n)) n"
        by (metis "4.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
      hence "both_member_options (vebt_insert (treeList ! (high x n)) (low x n)) (low x n)"
        by (simp add: "4.IH"(1) \<open>high x n < length treeList\<close> low_def)
      have " (treeList[ (high x n):=vebt_insert (treeList ! (high x n)) (low x n)]) ! (high x n) = vebt_insert (treeList ! (high x n)) (low x n)" 
        by (simp add: \<open>high x n < length treeList\<close>)
      then show ?thesis 
        using both_member_options_ding[of "Some (mi, max x ma)" deg
        "(take (high x n) treeList @ [vebt_insert (treeList ! (high x n)) (low x n)] @ drop (high x n +1) treeList)" 
        "if minNull (treeList ! high x n) then  vebt_insert summary (high x n) else summary" n x] 
        by (metis "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) Suc_1 Suc_leD 
          \<open>vebt_insert (Node (Some (mi, ma)) deg treeList summary) x = Node (Some (mi, max x ma)) deg (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)]) (if minNull (treeList ! high x n) then vebt_insert summary (high x n) else summary)\<close> \<open>both_member_options (vebt_insert (treeList ! high x n) (low x n)) (low x n)\<close> \<open>low x n < 2 ^ n \<and> high x n < 2 ^ n\<close> \<open>invar_vebt (treeList ! high x n) n\<close> add_self_div_2 both_member_options_from_chilf_to_complete_tree deg_not_0 div_greater_zero_iff length_list_update)
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence "length treeList =2^m" by blast
  hence "high x n < length treeList"
    by (metis "5.hyps"(4) "5.prems" div_eq_0_iff div_exp_eq high_def length_0_conv length_greater_0_conv zero_less_numeral zero_less_power)
  hence "mi<2^deg" 
    using "5.hyps"(7) "5.hyps"(8) le_less_trans by blast
  then show ?case 
  proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis using vebt_insert.simps(5)[of mi ma "deg-2" treeList summary x]
      by (smt "5.hyps"(3) "5.hyps"(4) Suc_leI add_Suc_right add_diff_inverse_nat add_numeral_left both_member_options_def diff_is_0_eq' vebt_insert.simps(3) membermima.simps(4) not_add_less1 numerals(1) plus_1_eq_Suc semiring_norm(2))
  next
    case False
    hence "\<not> (x = mi \<or> x = ma)" by simp
    then show ?thesis 
    proof(cases "x < mi")
      case True
      hence "high mi n < length treeList"
        by (metis "5.hyps"(2) "5.hyps"(4) div_eq_0_iff \<open>mi < 2 ^ deg\<close> div_exp_eq high_def length_0_conv length_greater_0_conv zero_less_numeral zero_less_power)
      hence "vebt_insert ( Node (Some (mi, ma)) deg treeList summary) x = 
                      Node (Some (x, max mi ma)) deg ( treeList[ (high mi n):=vebt_insert (treeList ! (high mi n)) (low mi n)] )
                               (if minNull (treeList ! high mi n) then  vebt_insert summary (high mi n) else summary)" 
        using  insert_simp_excp[of mi deg treeList x ma summary] 
           "5"(1) "5.hyps"(3) "5.hyps"(4) False True add_Suc_right add_self_div_2
           append_Cons div_less even_Suc_div_two in_set_conv_decomp not_less odd_add valid_tree_deg_neq_0
        by (smt (z3) nth_mem)
      then show ?thesis
        by (simp add: "5.hyps"(3) "5.hyps"(4) both_member_options_def)
    next
      case False
      hence "vebt_insert ( Node (Some (mi, ma)) deg treeList summary) x = 
      Node (Some (mi, max x ma)) deg (treeList[(high x n):= vebt_insert (treeList ! (high x n)) (low x n)])
                               (if minNull (treeList ! high x n) then  vebt_insert summary (high x n) else summary)" 
        by (smt (z3) "5.IH"(1) "5.hyps"(3) "5.hyps"(4) \<open>\<not> (x = mi \<or> x = ma)\<close> \<open>high x n < length treeList\<close> add_Suc_right add_self_div_2 deg_not_0 div_greater_zero_iff even_Suc_div_two insert_simp_norm linorder_neqE_nat nth_mem odd_add)
      have "low x n < 2^n \<and> high x n < 2^m" 
        using "5.hyps"(2) "5.hyps"(3) \<open>high x n < length treeList\<close> low_def by auto
      have "invar_vebt (treeList ! (high x n)) n"
        by (metis "5.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
      hence "both_member_options (vebt_insert (treeList ! (high x n)) (low x n)) (low x n)"
        by (metis "5.IH"(1) \<open>high x n < length treeList\<close> \<open>low x n < 2 ^ n \<and> high x n < 2 ^ m\<close> inthall member_def) 
      have " (treeList[ (high x n):=vebt_insert (treeList ! (high x n)) (low x n)]) ! (high x n) = vebt_insert (treeList ! (high x n)) (low x n)" 
        by (meson \<open>high x n < length treeList\<close> nth_list_update_eq)
      then show ?thesis 
        using both_member_options_ding[of "Some (mi, max x ma)" deg
            "(treeList[ (high x n):=vebt_insert (treeList ! (high x n)) (low x n)])" 
            "if minNull (treeList ! high x n) then  vebt_insert summary (high x n) else summary" n x]
        using "5.hyps"(2) "5.hyps"(3) "5.hyps"(4) \<open>vebt_insert (Node (Some (mi, ma)) deg treeList summary) x = Node (Some (mi, max x ma)) deg (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)]) (if minNull (treeList ! high x n) then vebt_insert summary (high x n) else summary)\<close> \<open>both_member_options (vebt_insert (treeList ! high x n) (low x n)) (low x n)\<close> \<open>low x n < 2 ^ n \<and> high x n < 2 ^ m\<close> both_member_options_from_chilf_to_complete_tree by auto
    qed
  qed
qed

lemma valid_insert_both_member_options_pres: "invar_vebt t n \<Longrightarrow> x<2^n \<Longrightarrow> y < 2^n \<Longrightarrow> both_member_options t x
                \<Longrightarrow> both_member_options (vebt_insert t y) x"
proof(induction t n arbitrary: x y rule: invar_vebt.induct)
  case (1 a b)
  then show ?case by (simp add: both_member_options_def)
next
  case (2 treeList n summary m deg)
  then show ?case 
    using vebt_member.simps(2) invar_vebt.intros(2) valid_member_both_member_options by blast
next
  case (3 treeList n summary m deg)
  then show ?case
    using vebt_member.simps(2) invar_vebt.intros(3) valid_member_both_member_options by blast
next
  case (4 treeList n summary m deg mi ma)
  hence 00:"deg = n + m \<and> length treeList = 2^n \<and> n = m \<and> n \<ge> 1 \<and> deg \<ge> 2"
    by (metis One_nat_def Suc_leI add_mono_thms_linordered_semiring(1) deg_not_0 one_add_one)
  hence xyprop: "high x n < 2^m \<and> high y n < 2^m"
    by (metis "4.prems"(1) "4.prems"(2) high_def less_mult_imp_div_less mult_2 power2_eq_square power_even_eq)
  have "low x n <2^n \<and> low y n< 2^n" 
    by (simp add: low_def)
  hence "x = mi \<or> x = ma \<or> both_member_options (treeList ! (high x n)) (low x n)"
    by (smt "00" "4.prems"(3) add_Suc_right add_self_div_2 both_member_options_def le_add_diff_inverse membermima.simps(4) naive_member.simps(3) plus_1_eq_Suc)
  have 001:"invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" using invar_vebt.intros(4)[of treeList n summary m deg mi ma] "4" by simp
  then show ?case
  proof(cases "x = y")
    case True
    hence "both_member_options (vebt_insert (Node (Some (mi, ma)) deg treeList summary) y) y" 
      using 001 valid_insert_both_member_options_add[of "(Node (Some (mi, ma)) deg treeList summary)" deg y ]
      using "4.prems"(2) by blast
    then show ?thesis 
      by (simp add: True)
  next
    case False
    then show ?thesis 
    proof(cases "y = mi \<or> y = ma")
      case True
      have "Suc (Suc (deg -2)) = deg"
        using "00" by linarith
      hence "vebt_insert (Node (Some (mi, ma)) deg treeList summary) y = Node (Some (mi, ma)) deg treeList summary"
        using vebt_insert.simps(5)[of mi ma "deg-2" treeList summary x] 00  True insert_simp_mima by blast
      then show ?thesis
        by (simp add: "4.prems"(3))     
    next
      case False
      hence 0:"y \<noteq> mi \<and> y \<noteq> ma" by simp
      then show ?thesis 
      proof(cases "x = mi")
        case True
        hence 1:"x = mi" by simp
        then show ?thesis 
        proof(cases "x < y")
          case True
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (x, max y ma)) deg (treeList [ (high y n):=vebt_insert (treeList ! (high y n)) (low y n)] )
                               (if minNull (treeList ! (high y n)) then  vebt_insert summary (high y n) else summary)"
            using "00" "1" False True insert_simp_norm xyprop by auto
          then show ?thesis
            by (metis "001" Suc_pred both_member_options_def deg_not_0 membermima.simps(4))
        next
          case False
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (y, max x ma)) deg (treeList [ (high x n) :=vebt_insert (treeList ! (high x n)) (low x n)])
                               (if minNull (treeList ! (high x n)) then  vebt_insert summary (high x n) else summary)"
            by (metis "0" "00" False True add_self_div_2 insert_simp_excp linorder_neqE_nat xyprop)
          have 15: " invar_vebt (treeList ! (high x n)) n" 
            by (metis "4"(1) "4.hyps"(2) in_set_member inthall xyprop)
          hence 16: "both_member_options (vebt_insert (treeList ! high x n) (low x n)) (low x n)"
            using \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> valid_insert_both_member_options_add by blast
          then show ?thesis
            by (metis "00" "14" Suc_1 add_leD1 add_self_div_2 both_member_options_from_chilf_to_complete_tree length_list_update nth_list_update_eq plus_1_eq_Suc xyprop)

        qed
      next 
        case False
        hence "mi \<noteq> ma"
          using "001" "4.prems"(3) less_irrefl member_inv valid_member_both_member_options by fastforce
        hence "both_member_options (treeList !(high x n) ) (low x n) \<or> x = ma"
          using False \<open>x = mi \<or> x = ma \<or> both_member_options (treeList ! high x n) (low x n)\<close> by blast
        have "high ma n < 2^n" 
          by (metis "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) high_def less_mult_imp_div_less mult_2 power2_eq_square power_even_eq)
        hence "both_member_options (treeList !(high ma n) ) (low ma n)" 
          using "4.hyps"(3) "4.hyps"(9) \<open>mi \<noteq> ma\<close> by blast
        hence "both_member_options (treeList !(high x n) ) (low x n)"
          using \<open>both_member_options (treeList ! high x n) (low x n) \<or> x = ma\<close> by blast
        then show ?thesis 
        proof(cases "mi < y")
          case True
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (mi, max y ma)) deg (treeList[(high y n):=vebt_insert (treeList ! (high y n)) (low y n)])
                               (if minNull (treeList ! (high y n)) then  vebt_insert summary (high y n) else summary)"
            using "0" "00" True insert_simp_norm xyprop by auto
          have "invar_vebt (treeList ! (high x n)) n"
            by (metis "4.IH"(1) "4.hyps"(2) in_set_member inthall xyprop)
          then show ?thesis 
          proof(cases "high x n = high y n")
            case True
            have "both_member_options (vebt_insert (treeList ! (high y n)) (low y n)) (low x n)" 
              using "4.IH"(1) "4.hyps"(2) True \<open>both_member_options (treeList ! high x n) (low x n)\<close> \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> xyprop by auto
            then show ?thesis
              by (metis "00" "14" Suc_1 True add_leD1 add_self_div_2 both_member_options_from_chilf_to_complete_tree length_list_update nth_list_update_eq plus_1_eq_Suc xyprop)
          next
            case False
            have "(treeList[ (high y n):=vebt_insert (treeList ! (high y n)) (low y n)]) ! (high x n) = treeList ! (high x n)"
              using False by auto
            then show ?thesis 
              by (metis "00" "14" One_nat_def Suc_leD \<open>both_member_options (treeList ! high x n) (low x n)\<close> add_self_div_2 both_member_options_from_chilf_to_complete_tree length_list_update numeral_2_eq_2 xyprop)
          qed
        next
          case False 
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (y, max mi ma)) deg (treeList[ (high mi n):=vebt_insert (treeList ! (high mi n)) (low mi n)])
                               (if minNull (treeList ! (high mi n)) then  vebt_insert summary (high mi n) else summary)"
            using insert_simp_excp[of mi deg treeList y ma summary]
            by (smt "0" "00" "4.hyps"(7) "4.hyps"(8) False add_self_div_2 antisym_conv3 high_def le_less_trans less_mult_imp_div_less mult_2 power2_eq_square power_even_eq)
          have mimaprop: "high mi n < 2^n \<and> low mi n < 2^n"  
            by (metis "00" "4.hyps"(7) "4.hyps"(8) div_eq_0_iff div_exp_eq high_def le_less_trans low_def mod_less_divisor zero_less_numeral zero_less_power)
          have "invar_vebt (treeList ! (high x n)) n"
            by (metis "4.IH"(1) "4.hyps"(2) in_set_member inthall xyprop)      
          then show ?thesis 
          proof(cases "high x n = high mi n")
            case True
            have "both_member_options (vebt_insert (treeList ! (high mi n)) (low mi n)) (low x n)"
              by (metis "4.IH"(1) "4.hyps"(2) True \<open>both_member_options (treeList ! high x n) (low x n)\<close> \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> mimaprop nth_mem xyprop)
            then show ?thesis
              by (metis "00" "14" Suc_1 Suc_leD True add_self_div_2 both_member_options_from_chilf_to_complete_tree length_list_update nth_list_update_eq xyprop)
          next
            case False
            have "(treeList[(high mi n):=vebt_insert (treeList ! (high mi n)) (low mi n)]) ! (high x n) = treeList ! (high x n)" 
              using False by force
            then show ?thesis
              by (metis "00" "14" One_nat_def Suc_leD \<open>both_member_options (treeList ! high x n) (low x n)\<close> add_self_div_2 both_member_options_from_chilf_to_complete_tree length_list_update numeral_2_eq_2 xyprop)
          qed
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence 00:"deg = n + m \<and> length treeList = 2^m \<and> Suc n = m \<and> n \<ge> 1 \<and> deg \<ge> 2 \<and> n = deg div 2" 
    by (metis Suc_1 add_Suc_right add_mono_thms_linordered_semiring(1) add_self_div_2 even_Suc_div_two le_add1 odd_add plus_1_eq_Suc set_n_deg_not_0)
  hence xyprop: "high x n < 2^m \<and> high y n < 2^m"
    by (metis "5.prems"(1) "5.prems"(2) Suc_1 div_exp_eq div_if high_def nat.discI power_not_zero)
  have "low x n <2^n \<and> low y n< 2^n" 
    by (simp add: low_def)
  hence "x = mi \<or> x = ma \<or> both_member_options (treeList ! (high x n)) (low x n)"
    by (smt "00" "5.prems"(3) add_Suc_right add_self_div_2 both_member_options_def le_add_diff_inverse membermima.simps(4) naive_member.simps(3) plus_1_eq_Suc)
  have 001:"invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" 
    using invar_vebt.intros(5)[of treeList n summary m deg mi ma] "5" by simp
  then show ?case 
  proof(cases "x = y")
    case True
    hence "both_member_options (vebt_insert (Node (Some (mi, ma)) deg treeList summary) y) y" 
      using 001 valid_insert_both_member_options_add[of "(Node (Some (mi, ma)) deg treeList summary)" deg y ]
      using "5.prems"(2) by blast
    then show ?thesis 
      by (simp add: True)
  next
    case False
    then show ?thesis 
    proof(cases "y = mi \<or> y = ma")
      case True
      have "Suc (Suc (deg -2)) = deg"
        using "00" by linarith
      hence "vebt_insert (Node (Some (mi, ma)) deg treeList summary) y = Node (Some (mi, ma)) deg treeList summary"
        using vebt_insert.simps(5)[of mi ma "deg-2" treeList summary x] 00  True insert_simp_mima by blast
      then show ?thesis
        by (simp add: "5.prems"(3))     
    next
      case False
      hence 0:"y \<noteq> mi \<and> y \<noteq> ma" by simp
      then show ?thesis 
      proof(cases "x = mi")
        case True
        hence 1:"x = mi" by simp
        then show ?thesis 
        proof(cases "x < y")
          case True
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (x, max y ma)) deg (treeList[ (high y n):=vebt_insert (treeList ! (high y n)) (low y n)] )
                               (if minNull (treeList ! (high y n)) then  vebt_insert summary (high y n) else summary)"
            using "00" "1" False True insert_simp_norm xyprop by metis
          then show ?thesis
            by (metis "001" Suc_pred both_member_options_def deg_not_0 membermima.simps(4))
        next
          case False
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (y, max x ma)) deg (treeList[ (high x n):=vebt_insert (treeList ! (high x n)) (low x n)])
                               (if minNull (treeList ! (high x n)) then  vebt_insert summary (high x n) else summary)"
            by (metis "0" "00" False True add_self_div_2 insert_simp_excp linorder_neqE_nat xyprop)
          have 15: " invar_vebt (treeList ! (high x n)) n" 
            by (metis "5"(1) "5.hyps"(2) in_set_member inthall xyprop)
          hence 16: "both_member_options (vebt_insert (treeList ! high x n) (low x n)) (low x n)"
            using \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> valid_insert_both_member_options_add by blast
          then show ?thesis 
            by (metis "00" "14" Suc_1 add_leD1 both_member_options_from_chilf_to_complete_tree length_list_update nth_list_update_eq plus_1_eq_Suc xyprop)             
        qed
      next 
        case False
        hence "mi \<noteq> ma"
          using "001" "5.prems"(3) less_irrefl member_inv valid_member_both_member_options by fastforce
        hence "both_member_options (treeList !(high x n) ) (low x n) \<or> x = ma"
          using False \<open>x = mi \<or> x = ma \<or> both_member_options (treeList ! high x n) (low x n)\<close> by blast
        have "high ma n < 2^m"
          by (metis "00" "5.hyps"(8) div_eq_0_iff div_exp_eq high_def nat_zero_less_power_iff power_not_zero zero_power2)
        hence "both_member_options (treeList !(high ma n) ) (low ma n)" 
          using "5.hyps"(3) "5.hyps"(9) \<open>mi \<noteq> ma\<close> by blast
        hence "both_member_options (treeList !(high x n) ) (low x n)"
          using \<open>both_member_options (treeList ! high x n) (low x n) \<or> x = ma\<close> by blast
        then show ?thesis 
        proof(cases "mi < y")
          case True
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (mi, max y ma)) deg (treeList[(high y n):= vebt_insert (treeList ! (high y n)) (low y n)])
                               (if minNull (treeList ! (high y n)) then  vebt_insert summary (high y n) else summary)"
            by (metis "0" "00" True insert_simp_norm xyprop)
          have "invar_vebt (treeList ! (high x n)) n"
            by (metis "5.IH"(1) "5.hyps"(2) in_set_member inthall xyprop)
          then show ?thesis 
          proof(cases "high x n = high y n")
            case True
            have "both_member_options (vebt_insert (treeList ! (high y n)) (low y n)) (low x n)"
              by (metis "5.IH"(1) "5.hyps"(2) True \<open>both_member_options (treeList ! high x n) (low x n)\<close> \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> nth_mem xyprop)              
            then show ?thesis 
              by (metis "00" "14" Suc_1 True add_leD1 both_member_options_from_chilf_to_complete_tree length_list_update nth_list_update_eq plus_1_eq_Suc xyprop)
          next
            case False
            have "(treeList[ (high y n):=vebt_insert (treeList ! (high y n)) (low y n)] ) ! (high x n) = treeList ! (high x n)" 
              using False by force
            then show ?thesis
              by (metis "00" "14" One_nat_def Suc_leD \<open>both_member_options (treeList ! high x n) (low x n)\<close> both_member_options_from_chilf_to_complete_tree length_list_update numeral_2_eq_2 xyprop)
          qed
        next
          case False 
          have 14:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) y =
                 Node (Some (y, max mi ma)) deg (treeList[(high mi n):= vebt_insert (treeList ! (high mi n)) (low mi n)] )
                               (if minNull (treeList ! (high mi n)) then  vebt_insert summary (high mi n) else summary)"
            using insert_simp_excp[of mi deg treeList y ma summary]
            by (metis "0" "00" "5.hyps"(7) "5.hyps"(8) div_eq_0_iff False antisym_conv3 div_exp_eq high_def le_less_trans power_not_zero zero_neq_numeral)      
          have mimaprop: "high mi n < 2^m \<and> low mi n < 2^n" using exp_split_high_low[of mi n m] 00 "5"(9,10) by force
          have "invar_vebt (treeList ! (high x n)) n"
            by (metis "5.IH"(1) "5.hyps"(2) in_set_member inthall xyprop)      
          then show ?thesis 
          proof(cases "high x n = high mi n")
            case True
            have "both_member_options (vebt_insert (treeList ! (high mi n)) (low mi n)) (low x n)" 
              by (metis "5.IH"(1) "5.hyps"(2) True \<open>both_member_options (treeList ! high x n) (low x n)\<close> \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> mimaprop nth_mem)
            then show ?thesis 
              by (metis "00" "14" Suc_1 True add_leD1 both_member_options_from_chilf_to_complete_tree length_list_update nth_list_update_eq plus_1_eq_Suc xyprop)
          next
            case False
            have "(treeList[ (high mi n):=vebt_insert (treeList ! (high mi n)) (low mi n)]) ! (high x n) = treeList ! (high x n)" 
              by (metis False nth_list_update_neq)
            then show ?thesis 
              by (metis "00" "14" One_nat_def Suc_leD \<open>both_member_options (treeList ! high x n) (low x n)\<close> both_member_options_from_chilf_to_complete_tree length_list_update numeral_2_eq_2 xyprop)
          qed
        qed
      qed
    qed
  qed
qed

lemma post_member_pre_member:"invar_vebt t n \<Longrightarrow> x< 2^n \<Longrightarrow> y <2^n \<Longrightarrow> vebt_member (vebt_insert t x) y \<Longrightarrow> vebt_member t y \<or> x = y"
proof(induction t n arbitrary: x y rule: invar_vebt.induct)
  case (1 a b)  then show ?case by auto
next
  case (2 treeList n summary m deg)
  hence "deg \<ge> 2" 
    using deg_not_0 by fastforce
  then show ?case using vebt_insert.simps(4)[of "deg-2" treeList summary x] 
    by (metis (no_types, lifting) "2.prems"(3) vebt_member.simps(5) add_numeral_left le_add_diff_inverse member_inv numerals(1) plus_1_eq_Suc semiring_norm(2))
next
  case (3 treeList n summary m deg)
  hence "deg \<ge> 2" 
    by (metis vebt_member.simps(2) One_nat_def Suc_1 Suc_eq_plus1 add_mono_thms_linordered_semiring(1) vebt_insert.simps(3) le_Suc_eq le_add1 plus_1_eq_Suc)
  then show ?case using vebt_insert.simps(4)[of "deg-2" treeList summary x]
    by (metis (no_types, lifting) "3.prems"(3) vebt_member.simps(5) add_numeral_left le_add_diff_inverse member_inv numerals(1) plus_1_eq_Suc semiring_norm(2))
next
  case (4 treeList n summary m deg mi ma)
  hence 00:"deg = n+m \<and> n \<ge> 0 \<and> n = m \<and> deg \<ge> 2 \<and> length treeList =2^n"
    by (metis div_eq_0_iff add_self_div_2 deg_not_0 not_less zero_le)
  hence xyprop: "high x n < 2^n \<and> high y n < 2^n"
    using "4.hyps"(1) "4.prems"(1) "4.prems"(2) deg_not_0 exp_split_high_low(1) by blast
  have "low x n <2^n \<and> low y n< 2^n" 
    by (simp add: low_def)
  then show ?case 
  proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis
      using "00" "4.prems"(3) insert_simp_mima by auto
  next
    case False
    hence mimaxyprop: "\<not> (x = mi \<or> x = ma) \<and> high x n < 2^n \<and> high mi n < 2^n \<and> low x n <2^n \<and> low mi n < 2^n \<and> length treeList = 2^n" 
      using "00" "4.hyps"(1) "4.hyps"(7) "4.hyps"(8) \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> deg_not_0 exp_split_high_low(1) exp_split_high_low(2) le_less_trans xyprop by blast
    then show ?thesis 
    proof(cases "mi < x")
      case True
      hence "vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x =
                 Node (Some (mi, max x ma)) deg (treeList[(high x n) :=vebt_insert (treeList ! (high x n)) (low x n)])
                               (if minNull (treeList ! (high x n)) then  vebt_insert summary (high x n) else summary)" 
        using insert_simp_norm[of x n treeList mi ma summary] mimaxyprop "00" add_self_div_2 insert_simp_norm by metis
      then show ?thesis 
      proof(cases "y = mi \<or> y = max x ma")
        case True
        then show ?thesis 
        proof(cases "y = mi")
          case True
          then show ?thesis
            by (metis "00" vebt_member.simps(5) le0 not_less_eq_eq numeral_2_eq_2 old.nat.exhaust)
        next
          case False
          hence "y = max x ma" 
            using True by blast
          then show ?thesis 
          proof(cases "x < ma")
            case True
            then show ?thesis 
              by (metis (no_types, lifting) "00" vebt_member.simps(5) \<open>y = max x ma\<close> add_numeral_left le_add_diff_inverse max_less_iff_conj not_less_iff_gr_or_eq numerals(1) plus_1_eq_Suc semiring_norm(2))
          next
            case False
            then show ?thesis
              using \<open>y = max x ma\<close> by linarith
          qed
        qed
      next
        case False
        hence "vebt_member ((treeList[(high x n):= vebt_insert (treeList ! (high x n)) (low x n)]) ! (high y n)) (low y n)" 
          by (metis "4.hyps"(3) "4.hyps"(4) "4.prems"(3) \<open>vebt_insert (Node (Some (mi, ma)) deg treeList summary) x = Node (Some (mi, max x ma)) deg (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)]) (if minNull (treeList ! high x n) then vebt_insert summary (high x n) else summary)\<close> add_self_div_2 member_inv)
        then show ?thesis 
        proof(cases "high x n  = high y n")
          case True
          hence 000:"vebt_member (vebt_insert (treeList ! (high x n)) (low x n)) (low y n)"
            using \<open>vebt_member (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)] ! high y n) (low y n)\<close> mimaxyprop by auto
          have 001:"invar_vebt (treeList ! (high x n)) n \<and> treeList ! (high x n) \<in> set treeList " 
            by (simp add: "4.IH"(1) mimaxyprop)
          hence 002:"vebt_member (treeList ! (high x n)) (low y n) \<or> low y n = low x n" 
            using "000" "4.IH"(1) \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> by fastforce
          hence 003:"both_member_options (treeList ! (high x n)) (low y n) \<or> low y n = low x n"
            using \<open>invar_vebt (treeList ! high x n) n \<and> treeList ! high x n \<in> set treeList\<close> both_member_options_equiv_member by blast
          have 004:"naive_member (treeList ! (high x n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" 
            by (metis "00" Suc_le_D True add_self_div_2 mimaxyprop naive_member.simps(3) one_add_one plus_1_eq_Suc)
          hence 005:"both_member_options (Node (Some (mi , ma)) deg treeList summary) y \<or> x = y"
            by (metis "00" "001" "002" Suc_le_D True add_self_div_2 bit_split_inv both_member_options_def member_valid_both_member_options membermima.simps(4) mimaxyprop one_add_one plus_1_eq_Suc)
          then show ?thesis 
            by (smt "00" "001" "002" "003" "4"(11) "4"(8) vebt_member.simps(5) True add_numeral_left add_self_div_2 bit_split_inv le_add_diff_inverse mimaxyprop not_less not_less_iff_gr_or_eq numerals(1) plus_1_eq_Suc semiring_norm(2))
        next
          case False
          hence 000:"vebt_member (treeList ! (high y n)) (low y n)"
            using \<open>vebt_member (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)] ! high y n) (low y n)\<close> by auto
          moreover have 004:"naive_member (treeList ! (high y n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" 
            by (metis "00" Suc_le_D add_self_div_2 naive_member.simps(3) one_add_one plus_1_eq_Suc xyprop)
          moreover have 001:"invar_vebt (treeList ! (high y n)) n \<and> treeList ! (high y n) \<in> set treeList "
            by (metis (full_types) "4.IH"(1) "4.hyps"(2) "4.hyps"(3) inthall member_def xyprop)
          moreover have " both_member_options (Node (Some (mi , ma)) deg treeList summary) y"
            by (metis "00" "000" "001" "004" Suc_le_D add_self_div_2 both_member_options_def member_valid_both_member_options membermima.simps(4) one_add_one plus_1_eq_Suc xyprop)
          moreover have "vebt_member (Node (Some (mi, ma)) deg treeList summary) y" 
            using both_member_options_equiv_member[of "(Node (Some (mi, ma)) deg treeList summary)" deg y]
              invar_vebt.intros(4)[of treeList n summary m deg mi ma]
            using "4" calculation(4) by blast
          then show ?thesis  by simp
        qed
      qed
    next
      case False
      hence "x < mi"
        using mimaxyprop nat_neq_iff by blast
      hence "vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x =
                 Node (Some (x, max mi ma)) deg (treeList[ (high mi n):=vebt_insert (treeList ! (high mi n)) (low mi n)])
                      (if minNull (treeList ! (high mi n)) then  vebt_insert summary (high mi n) else summary)" 
        using insert_simp_excp[of mi n treeList x ma summary] mimaxyprop "00" add_self_div_2 insert_simp_excp by metis
      then show ?thesis 
      proof(cases "y = x \<or> y = max mi ma")
        case True
        then show ?thesis 
        proof(cases "y = x")
          case True
          then show ?thesis 
            by (simp add: "00")
        next
          case False
          hence "y = max mi ma" 
            using True by blast
          then show ?thesis 
          proof(cases "mi < ma")
            case True
            then show ?thesis  using "00" vebt_member.simps(5) \<open>y = max mi ma\<close> add_numeral_left
                le_add_diff_inverse max_less_iff_conj not_less_iff_gr_or_eq numerals(1) plus_1_eq_Suc semiring_norm(2)
              by (metis (no_types, lifting))
          next
            case False
            then show ?thesis
              by (metis "00" "4.hyps"(7) vebt_member.simps(5) \<open>y = max mi ma\<close> add_numeral_left le_add_diff_inverse max.absorb2 numerals(1) plus_1_eq_Suc semiring_norm(2))
          qed
        qed
      next
        case False
        hence "vebt_member ((treeList[(high mi n) :=vebt_insert (treeList ! (high mi n)) (low mi n)]) ! (high y n)) (low y n)"
          by (metis "4.hyps"(3) "4.hyps"(4) "4.prems"(3) \<open>vebt_insert (Node (Some (mi, ma)) deg treeList summary) x = Node (Some (x, max mi ma)) deg (treeList[high mi n := vebt_insert (treeList ! high mi n) (low mi n)]) (if minNull (treeList ! high mi n) then vebt_insert summary (high mi n) else summary)\<close> add_self_div_2 member_inv)
        then show ?thesis 
        proof(cases "high mi n  = high y n")
          case True
          hence 000:"vebt_member (vebt_insert (treeList ! (high mi n)) (low mi n)) (low y n)" 
            by (metis \<open>vebt_member (treeList[high mi n := vebt_insert (treeList ! high mi n) (low mi n)] ! high y n) (low y n)\<close> mimaxyprop nth_list_update_eq)
          have 001:"invar_vebt (treeList ! (high mi n)) n \<and> treeList ! (high mi n) \<in> set treeList"
            by (simp add: "4.IH"(1) mimaxyprop)
          hence 002:"vebt_member (treeList ! (high mi n)) (low y n) \<or> low y n = low mi n"
            using "000" "4.IH"(1) \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> mimaxyprop by fastforce
          hence 003:"both_member_options (treeList ! (high mi n)) (low y n) \<or> low y n = low mi n"
            using \<open>invar_vebt (treeList ! high mi n) n \<and> treeList ! high mi n \<in> set treeList\<close> both_member_options_equiv_member by blast
          have 004:"naive_member (treeList ! (high mi n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" using naive_member.simps(3)[of "Some (mi, ma)" "deg-1" treeList summary y] 
            using "00" True mimaxyprop by fastforce
          hence 005:"both_member_options (Node (Some (mi , ma)) deg treeList summary) y \<or> x = y" 
            by (metis "00" "001" "002" Suc_le_D True add_self_div_2 bit_split_inv both_member_options_def member_valid_both_member_options membermima.simps(4) mimaxyprop one_add_one plus_1_eq_Suc)
          then show ?thesis
            by (smt "00" "001" "002" "003" "4.hyps"(6) "4.hyps"(9) vebt_member.simps(5) True add_numeral_left add_self_div_2 bit_split_inv le_add_diff_inverse mimaxyprop not_less not_less_iff_gr_or_eq numerals(1) plus_1_eq_Suc semiring_norm(2))
        next
          case False
          hence 000:"vebt_member (treeList ! (high y n)) (low y n)" 
            using \<open>vebt_member (treeList[high mi n := vebt_insert (treeList ! high mi n) (low mi n)] ! high y n) (low y n)\<close> by auto
          moreover have 004:"naive_member (treeList ! (high y n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" 
            by (metis "00" Suc_le_D add_self_div_2 naive_member.simps(3) one_add_one plus_1_eq_Suc xyprop)
          moreover have 001:"invar_vebt (treeList ! (high y n)) n \<and> treeList ! (high y n) \<in> set treeList "
            by (metis (full_types) "4.IH"(1) "4.hyps"(2) "4.hyps"(3) inthall member_def xyprop)
          moreover have " both_member_options (Node (Some (mi , ma)) deg treeList summary) y"
            by (metis "00" "000" "001" "004" Suc_le_D add_self_div_2 both_member_options_def member_valid_both_member_options membermima.simps(4) one_add_one plus_1_eq_Suc xyprop)
          then show ?thesis using both_member_options_equiv_member[of "(Node (Some (mi, ma)) deg treeList summary)" deg y]
              invar_vebt.intros(4)[of treeList n summary m deg mi ma] "4" by blast   
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence 00:"deg = n+m \<and> n \<ge> 0 \<and> Suc n = m \<and> deg \<ge> 2 \<and> length treeList =2^m \<and> n \<ge> 1" 
    by (metis Suc_1 add_mono_thms_linordered_semiring(1) le_add1 plus_1_eq_Suc set_n_deg_not_0 zero_le)
  hence xyprop: "high x n < 2^m \<and> high y n < 2^m" 
    using "5.prems"(1) "5.prems"(2) exp_split_high_low(1) by auto
  have "low x n <2^n \<and> low y n< 2^n" 
    by (simp add: low_def)
  then show ?case 
  proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis
      using "00" "5.prems"(3) insert_simp_mima by auto
  next
    case False
    hence mimaxyprop: "\<not> (x = mi \<or> x = ma) \<and> high x n < 2^m \<and> high mi n < 2^m \<and> low x n <2^n \<and> low mi n < 2^n \<and> length treeList = 2^m" 
      using "00" "5"  \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> deg_not_0 exp_split_high_low(1) exp_split_high_low(2) le_less_trans xyprop 
      by (smt less_le_trans less_numeral_extra(1))
    then show ?thesis 
    proof(cases "mi < x")
      case True
      hence "vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x =
                 Node (Some (mi, max x ma)) deg (treeList[ (high x n):=vebt_insert (treeList ! (high x n)) (low x n)])
                               (if minNull (treeList ! (high x n)) then  vebt_insert summary (high x n) else summary)" 
        using insert_simp_norm[of x deg treeList mi ma summary] 
        by (smt "00" False add_Suc_right add_self_div_2 even_Suc_div_two odd_add xyprop)
      then show ?thesis 
      proof(cases "y = mi \<or> y = max x ma")
        case True
        then show ?thesis 
        proof(cases "y = mi")
          case True
          then show ?thesis
            by (metis "00" vebt_member.simps(5) le0 not_less_eq_eq numeral_2_eq_2 old.nat.exhaust)
        next
          case False
          hence "y = max x ma" 
            using True by blast
          then show ?thesis 
          proof(cases "x < ma")
            case True
            then show ?thesis 
              by (metis (no_types, lifting) "00" vebt_member.simps(5) \<open>y = max x ma\<close> add_numeral_left le_add_diff_inverse max_less_iff_conj not_less_iff_gr_or_eq numerals(1) plus_1_eq_Suc semiring_norm(2))
          next
            case False
            then show ?thesis
              using \<open>y = max x ma\<close> by linarith
          qed
        qed
      next
        case False
        hence "vebt_member ((treeList[ (high x n):=vebt_insert (treeList ! (high x n)) (low x n)]) ! (high y n)) (low y n)" 
          using "5.hyps"(3) "5.hyps"(4) "5.prems"(3) \<open>vebt_insert (Node (Some (mi, ma)) deg treeList summary) x = Node (Some (mi, max x ma)) deg (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)]) (if minNull (treeList ! high x n) then vebt_insert summary (high x n) else summary)\<close> add_Suc_right add_self_div_2 member_inv by force 
        then show ?thesis 
        proof(cases "high x n  = high y n")
          case True
          hence 000:"vebt_member (vebt_insert (treeList ! (high x n)) (low x n)) (low y n)"
            by (metis "5.hyps"(2) \<open>vebt_member (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)] ! high y n) (low y n)\<close> nth_list_update_eq xyprop)
          have 001:"invar_vebt (treeList ! (high x n)) n \<and> treeList ! (high x n) \<in> set treeList "
            by (simp add: "5.IH"(1) "5.hyps"(2) xyprop)
          hence 002:"vebt_member (treeList ! (high x n)) (low y n) \<or> low y n = low x n" 
            using "000" "5.IH"(1) \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> by fastforce
          hence 003:"both_member_options (treeList ! (high x n)) (low y n) \<or> low y n = low x n"
            using \<open>invar_vebt (treeList ! high x n) n \<and> treeList ! high x n \<in> set treeList\<close> both_member_options_equiv_member by blast
          have 004:"naive_member (treeList ! (high x n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" 
            using "00" True xyprop by auto
          hence 005:"both_member_options (Node (Some (mi , ma)) deg treeList summary) y \<or> x = y"
            by (smt "00" "001" "002" True add_Suc_right add_self_div_2 bit_split_inv both_member_options_def even_Suc_div_two member_valid_both_member_options membermima.simps(4) odd_add xyprop)
          then show ?thesis 
            using both_member_options_equiv_member[of "(Node (Some (mi, ma)) deg treeList summary)" deg y]
              invar_vebt.intros(5)[of treeList n summary m deg mi ma] "5" by blast      
        next
          case False
          hence 000:"vebt_member (treeList ! (high y n)) (low y n)"
            using \<open>vebt_member (treeList[high x n := vebt_insert (treeList ! high x n) (low x n)] ! high y n) (low y n)\<close> by fastforce
          moreover have 004:"naive_member (treeList ! (high y n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" 
            using "00" xyprop by auto
          moreover have 001:"invar_vebt (treeList ! (high y n)) n \<and> treeList ! (high y n) \<in> set treeList "
            by (metis (full_types) "5"inthall member_def xyprop)
          moreover have " both_member_options (Node (Some (mi , ma)) deg treeList summary) y" 
            using "00" "000" "001" both_member_options_def member_valid_both_member_options xyprop by fastforce
          moreover have "vebt_member (Node (Some (mi, ma)) deg treeList summary) y" 
            using both_member_options_equiv_member[of "(Node (Some (mi, ma)) deg treeList summary)" deg y]
              invar_vebt.intros(5)[of treeList n summary m deg mi ma] "5" calculation(4) by blast
          then show ?thesis  by simp
        qed 
      qed
    next
      case False
      hence "x < mi"
        using mimaxyprop nat_neq_iff by blast
      hence "vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x =
                 Node (Some (x, max mi ma)) deg (treeList[ (high mi n):=vebt_insert (treeList ! (high mi n)) (low mi n)])
                               (if minNull (treeList ! (high mi n)) then  vebt_insert summary (high mi n) else summary)" 
        using insert_simp_excp[of mi n treeList x ma summary] mimaxyprop "00" add_self_div_2 insert_simp_excp
        by (smt add_Suc_right even_Suc_div_two odd_add)
      then show ?thesis 
      proof(cases "y = x \<or> y = max mi ma")
        case True
        then show ?thesis 
        proof(cases "y = x")
          case True
          then show ?thesis 
            by (simp add: "00")
        next
          case False
          hence "y = max mi ma" 
            using True by blast
          then show ?thesis
          proof(cases "mi < ma")
            case True
            then show ?thesis  using "00" vebt_member.simps(5) \<open>y = max mi ma\<close> add_numeral_left
                le_add_diff_inverse max_less_iff_conj not_less_iff_gr_or_eq numerals(1) plus_1_eq_Suc semiring_norm(2)
              by (metis (no_types, lifting))
          next
            case False
            then show ?thesis
              by (metis "00" "5.hyps"(7) vebt_member.simps(5) \<open>y = max mi ma\<close> add_numeral_left le_add_diff_inverse max.absorb2 numerals(1) plus_1_eq_Suc semiring_norm(2))
          qed
        qed
      next
        case False
        hence "vebt_member ((treeList[(high mi n):=vebt_insert (treeList ! (high mi n)) (low mi n)]) ! (high y n)) (low y n)" 
          using "5.hyps"(3) "5.hyps"(4) "5.prems"(3) \<open>vebt_insert (Node (Some (mi, ma)) deg treeList summary) x = Node (Some (x, max mi ma)) deg (treeList[high mi n := vebt_insert (treeList ! high mi n) (low mi n)]) (if minNull (treeList ! high mi n) then vebt_insert summary (high mi n) else summary)\<close> member_inv by force
        then show ?thesis 
        proof(cases "high mi n  = high y n")
          case True
          hence 000:"vebt_member (vebt_insert (treeList ! (high mi n)) (low mi n)) (low y n)"
            by (metis \<open>vebt_member (treeList[high mi n := vebt_insert (treeList ! high mi n) (low mi n)] ! high y n) (low y n)\<close> mimaxyprop nth_list_update_eq)
          have 001:"invar_vebt (treeList ! (high mi n)) n \<and> treeList ! (high mi n) \<in> set treeList "
            by (simp add: "5.IH"(1) mimaxyprop)
          hence 002:"vebt_member (treeList ! (high mi n)) (low y n) \<or> low y n = low mi n"
            using "000" "5.IH"(1) \<open>low x n < 2 ^ n \<and> low y n < 2 ^ n\<close> mimaxyprop by fastforce
          hence 003:"both_member_options (treeList ! (high mi n)) (low y n) \<or> low y n = low mi n"
            using \<open>invar_vebt (treeList ! high mi n) n \<and> treeList ! high mi n \<in> set treeList\<close> both_member_options_equiv_member by blast
          have 004:"naive_member (treeList ! (high mi n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" using naive_member.simps(3)[of "Some (mi, ma)" "deg-1" treeList summary y] 
            using "00" True mimaxyprop by fastforce
          hence 005:"both_member_options (Node (Some (mi , ma)) deg treeList summary) y \<or> x = y" 
            by (smt "00" "001" "002" True add_Suc_right add_self_div_2 bit_split_inv both_member_options_def even_Suc_div_two member_valid_both_member_options membermima.simps(4) odd_add xyprop)
          then show ?thesis using  "00" "001" "002" "003" "5"(14) "5.hyps"(6) "5.hyps"(7) "5.hyps"(9) vebt_member.simps(5) True 
              add_Suc_right add_self_div_2 bit_split_inv even_Suc_div_two le_add_diff_inverse max.absorb2 
              mimaxyprop not_less_iff_gr_or_eq odd_add plus_1_eq_Suc 
            by (smt (z3) \<open>vebt_insert (Node (Some (mi, ma)) deg treeList summary) x = Node (Some (x, max mi ma)) deg (treeList[high mi n := vebt_insert (treeList ! high mi n) (low mi n)]) (if minNull (treeList ! high mi n) then vebt_insert summary (high mi n) else summary)\<close>)
        next
          case False
          hence 000:"vebt_member (treeList ! (high y n)) (low y n)" 
            using \<open>vebt_member (treeList[high mi n := vebt_insert (treeList ! high mi n) (low mi n)] ! high y n) (low y n)\<close> by auto
          moreover have 004:"naive_member (treeList ! (high y n)) (low y n) \<Longrightarrow>
              naive_member (Node (Some (mi , ma)) deg treeList summary) y" 
            using "00" xyprop by auto
          moreover have 001:"invar_vebt (treeList ! (high y n)) n \<and> treeList ! (high y n) \<in> set treeList "
            by (metis (full_types) "5.IH"(1) "5.hyps"(2) "5.hyps"(3) inthall member_def xyprop)
          moreover have " both_member_options (Node (Some (mi , ma)) deg treeList summary) y"
            using "00" "000" "001" both_member_options_def member_valid_both_member_options xyprop by fastforce
          then show ?thesis using both_member_options_equiv_member[of "(Node (Some (mi, ma)) deg treeList summary)" deg y]
              invar_vebt.intros(5)[of treeList n summary m deg mi ma] "5" by simp
        qed
      qed
    qed
  qed
qed

end
end
