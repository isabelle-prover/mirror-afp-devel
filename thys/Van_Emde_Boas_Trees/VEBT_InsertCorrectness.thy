(*by Ammer*)
theory VEBT_InsertCorrectness imports VEBT_Member VEBT_Insert
begin

context VEBT_internal begin

section \<open>Correctness of the Insert Operation\<close>

subsection \<open>Validness Preservation\<close>

theorem valid_pres_insert: "invar_vebt t n \<Longrightarrow> x< 2^n \<Longrightarrow> invar_vebt (vebt_insert t x) n"
proof(induction t n arbitrary: x rule: invar_vebt.induct)
  case (1 a b)
  then show ?case using vebt_insert.simps(1)[of a b x]
    by (simp add: invar_vebt.intros(1))
next
  case (2 treeList n summary m deg)
  hence 0: " ( \<forall> t \<in> set treeList. invar_vebt t n) " and 1:" invar_vebt summary n" and 2:" length treeList = 2^n" and
    3:" deg = 2*n" and 4:" (\<nexists> i. both_member_options summary i)" and 5:" (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x) " and 6: "n\<ge> 1"
    using "2.prems" by (auto simp add: Suc_leI deg_not_0)
  let  ?t = "Node None deg treeList summary"
  let ?tnew = "vebt_insert ?t x"
  have 6:"?tnew =  (Node (Some (x,x)) deg  treeList summary)" using vebt_insert.simps(4)[of "deg-2" treeList summary x]
    by (metis "1" "2.hyps"(3) "2.hyps"(4) add_2_eq_Suc add_diff_inverse_nat add_self_div_2 deg_not_0 div_less gr_implies_not0)
  have 7:"(x = x \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x))"
    using \<open>\<forall>t\<in>set treeList. \<nexists>x. both_member_options t x\<close> by blast
  have 8:"x \<le> x" by simp
  have 9:" x < 2^deg" 
    by (simp add: "2.prems")
  have 10:"(x \<noteq> x \<longrightarrow> (\<forall> i < 2^(2^n).  (high x deg = i \<longrightarrow> both_member_options (treeList ! i) (low x deg)) \<and>
                     (\<forall> y. (high y deg = i \<and> both_member_options (treeList ! i) (low y deg)  ) \<longrightarrow> x < y \<and> y \<le> x) ))" 
    by simp
  then show ?case using 0 1 2 3 4 5 6 7 8 9 10 invar_vebt.intros(4)[of treeList n summary m deg x x] 
    by (metis "2.hyps"(3) "2.hyps"(4) nth_mem)
next
  case (3 treeList n summary m deg)
  hence 0: " ( \<forall> t \<in> set treeList. invar_vebt t n) " and 1:" invar_vebt summary m" and 2:" length treeList = 2^m" and
    3:" deg = n+m" and 4:" (\<nexists> i. both_member_options summary i)" and 5:" (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x) " and 6: "n\<ge> 1"
    and 7: "Suc n = m" using "3.prems" apply auto
    by (metis "3.hyps"(2) One_nat_def set_n_deg_not_0)
  let  ?t = "Node None deg treeList summary"
  let ?tnew = "vebt_insert ?t x"
  have 6:"?tnew =  (Node (Some (x,x)) deg  treeList summary)" using vebt_insert.simps(4)[of "deg-2" treeList summary x] 
    by (smt "3" "3.hyps"(3) "6" Nat.add_diff_assoc One_nat_def Suc_le_mono add_diff_inverse_nat add_gr_0 add_numeral_left diff_is_0_eq' not_less not_less_iff_gr_or_eq numeral_2_eq_2 numerals(1) plus_1_eq_Suc semiring_norm(2))
  have 7:"(x = x \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> x. both_member_options t x))"
    using \<open>\<forall>t\<in>set treeList. \<nexists>x. both_member_options t x\<close> by blast
  have 8:"x \<le> x" by simp
  have 9:" x < 2^deg" 
    by (simp add: "3.prems")
  have 10:"(x \<noteq> x \<longrightarrow> (\<forall> i < 2^(2^n).  (high x deg = i \<longrightarrow> both_member_options (treeList ! i) (low x deg)) \<and>
                     (\<forall> y. (high y deg = i \<and> both_member_options (treeList ! i) (low y deg)  ) \<longrightarrow> x < y \<and> y \<le> x) ))" 
    by simp
  then show ?case using 0 1 2 3 4 5 6 7 8 9 10 invar_vebt.intros(5)[of treeList n summary m deg x x]  "3.hyps"(3) nth_mem by force
next
  case (4 treeList n summary m deg mi ma)
  hence myIHs: "x \<in> set treeList \<Longrightarrow> invar_vebt x n \<Longrightarrow> xa < 2 ^ n \<Longrightarrow> invar_vebt (vebt_insert x xa) n" for x xa by simp
  hence 0: "( \<forall> t \<in> set treeList. invar_vebt t n)" and 1: " invar_vebt summary m" and 2:"length treeList = 2^m" and 3:" deg = n+m" and 
    4: "(\<forall> i < 2^m. (\<exists> y. both_member_options (treeList ! i) y) \<longleftrightarrow> ( both_member_options summary i))" and 
    5: "(mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y))" and 6:"mi \<le> ma  \<and> ma < 2^deg" and
    7: "(mi \<noteq> ma \<longrightarrow> (\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)))"
    and 8: "n = m" and 9: "deg div 2 = n" using "4" add_self_div_2 by  blast+ 
  then show ?case  
  proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis using insert_simp_mima[of x mi ma deg treeList summary] 
        invar_vebt.intros(4)[of treeList n summary m deg mi ma] 
      by (smt "0" "1" "2" "3" "4" "4.hyps"(3) "4.hyps"(7) "4.hyps"(8) "5" "7" "9" deg_not_0 div_greater_zero_iff)     
  next
    case False
    hence mimaxrel: "x \<noteq> mi \<and> x \<noteq> ma" by simp
    then show ?thesis 
    proof(cases "mi < x")
      case True 
      hence abcdef: "mi < x" by simp
      let ?h = "high x n" and ?l="low x n"
      have highlowprop: "high x n < 2^m \<and> low x n < 2^n" 
        using "1" "3" "4.hyps"(3) "4.prems" deg_not_0 exp_split_high_low(1) exp_split_high_low(2) by blast
      have 10:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x = 
                 Node (Some (mi, max x ma)) deg  (treeList[?h:=vebt_insert (treeList ! ?h) ?l])
                               (if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary) " 
        using "2" "3" False True \<open>high x n < 2 ^ m \<and> low x n < 2  ^ n\<close> insert_simp_norm  by (metis "1" "4.hyps"(3) "9" deg_not_0 div_greater_zero_iff)
      let ?maxnew = "max x ma" and ?nextTreeList = "(take ?h treeList @ [vebt_insert (treeList ! ?h) ?l] @ drop (?h+1) treeList)" and
        ?nextSummary = "(if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary)"
      have 11: "( \<forall> t \<in> set ?nextTreeList. invar_vebt t n)" proof
        fix t
        assume " t \<in> set ?nextTreeList"
        hence 111:"t \<in> set (take ?h treeList) \<or> t \<in> set ([vebt_insert (treeList ! ?h) ?l] @ drop (?h+1) treeList)" by auto
        show "invar_vebt t n" 
        proof(cases "t \<in> set (take ?h treeList) ")
          case True
          then show ?thesis
            by (meson "0" in_set_takeD)
        next
          case False
          hence 1110: "t = vebt_insert (treeList ! ?h) ?l \<or> t \<in> set ( drop (?h+1) treeList)"
            using "111" by auto
          then show ?thesis 
          proof(cases "t =  vebt_insert (treeList ! ?h) ?l")
            case True
            have 11110: "invar_vebt (treeList ! ?h) n" 
              by (simp add: "2" "4.IH"(1) highlowprop)
            have 11111: "?l < 2^n"
              by (simp add: low_def)
            then show ?thesis using myIHs[of "treeList ! ?h"]
              by (simp add: "11110" "2" True highlowprop)
          next
            case False
            then show ?thesis
              by (metis "0" "1110" append_assoc append_take_drop_id in_set_conv_decomp)
          qed
        qed
      qed 
      have 12: "invar_vebt ?nextSummary n" 
      proof(cases "minNull (treeList ! high x n)")
        case True
        then show ?thesis
          using "4.IH"(2) "8" highlowprop by auto
      next
        case False
        then show ?thesis
          by (simp add: "1" "8")
      qed   
      have 13: "\<forall> i < 2^m. (\<exists> y. both_member_options (?nextTreeList ! i) y) \<longleftrightarrow> ( both_member_options ?nextSummary i)" 
      proof
        fix i
        show "i < 2 ^ m \<longrightarrow> (\<exists>y. both_member_options   ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
        proof
          assume "i< 2^m"
          show "(\<exists>y. both_member_options ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
          proof(cases "minNull (treeList ! high x n)")
            case True
            hence tc: "minNull (treeList ! high x n)" by simp
            hence nsprop: "?nextSummary = vebt_insert summary ?h" by simp
            have insprop:"?nextTreeList ! ?h = vebt_insert (treeList ! ?h) ?l"
              by (metis "2" Suc_eq_plus1 append_Cons highlowprop nth_list_update_eq self_append_conv2 upd_conv_take_nth_drop)
            then show ?thesis 
            proof(cases "i = ?h")
              case True
              have 161:"\<nexists> y. vebt_member (treeList ! ?h) y" 
                by (simp add: min_Null_member tc)
              hence 162:"\<nexists> y. both_member_options (treeList ! ?h) y"
                by (metis "2" "4.IH"(1) highlowprop nth_mem valid_member_both_member_options)
              hence 163:"\<not> both_member_options summary i"
                using "11" "2" "4" True \<open>i < 2 ^ m\<close> by blast
              have 164:"?nextTreeList ! i = vebt_insert (treeList ! ?h) ?l"
                using True insprop by simp
              have 165:"invar_vebt (vebt_insert (treeList ! ?h) ?l) n"
                by (simp add: "11")
              have 166:"both_member_options (vebt_insert (treeList ! ?h) ?l) ?l" using myIHs[of "treeList ! ?h" ?l] 
                by (metis "0" "2" highlowprop nth_mem valid_insert_both_member_options_add)
              have 167:"\<exists> y. both_member_options ((?nextTreeList) ! i) y "
                using "164" "166" by auto
              then show ?thesis
                using "1" "11" "2" True nsprop valid_insert_both_member_options_add highlowprop by auto
            next
              case False
              have "?nextTreeList ! i = treeList ! i" 
                by (metis "2" False \<open>i < 2 ^ m\<close> highlowprop nth_repl)
              have fstprop:"both_member_options ((?nextTreeList) ! i) y \<Longrightarrow> both_member_options (?nextSummary) i " for y 
                using "1" "4" \<open>(take (high x n) treeList @ [VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] @ drop (high x n + 1) treeList) ! i = treeList ! i\<close> \<open>i < 2 ^ m\<close> highlowprop valid_insert_both_member_options_pres by auto
              moreover  have" both_member_options (?nextSummary) i \<Longrightarrow> \<exists> y . both_member_options ((?nextTreeList) ! i) y "
              proof-
                assume  "both_member_options (?nextSummary) i "
                have "i \<noteq> high x n" 
                  by (simp add: False)
                hence "both_member_options summary i"
                  by (smt (z3) "1" "12" \<open>both_member_options (if minNull (treeList ! high x n) then VEBT_Insert.vebt_insert summary (high x n) else summary) i\<close> \<open>i < 2 ^ m\<close> both_member_options_equiv_member highlowprop post_member_pre_member)
                hence "\<exists> y. both_member_options (treeList ! i) y"
                  by (simp add: "4" \<open>i < 2 ^ m\<close>)
                then show ?thesis 
                  using \<open>(take (high x n) treeList @ [VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] @ drop (high x n + 1) treeList) ! i = treeList ! i\<close> by presburger
              qed
              ultimately show ?thesis by auto
            qed
          next
            case False
            hence "?nextSummary = summary" by simp
            hence "\<exists> y. both_member_options (treeList ! high x n) y"
              using not_min_Null_member False by blast
            hence "both_member_options summary (high x n)"
              using "4" highlowprop by blast
            hence " both_member_options (?nextTreeList ! high x n) ?l" 
              by (metis "0" "2" Suc_eq_plus1 append_Cons append_Nil highlowprop nth_list_update_eq nth_mem upd_conv_take_nth_drop valid_insert_both_member_options_add)
            then show ?thesis 
              by (smt (verit, best) "2" "4" False \<open>both_member_options summary (high x n)\<close> \<open>i < 2 ^ m\<close> highlowprop nth_repl)
          qed
        qed
      qed
      have 14: "(mi = max ma x \<longrightarrow> (\<forall> t \<in> set ?nextTreeList. \<nexists> y. both_member_options t y))"
        using True max_less_iff_conj by blast
      have 15: "mi \<le> max ma x  \<and> max ma x < 2^deg"
        using "4.hyps"(8) "4.prems" abcdef by auto 
      have 16:  "(mi \<noteq> max ma x \<longrightarrow> (\<forall> i < 2^m. (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> max ma x)))"
      proof
        assume "mi \<noteq> max ma x"
        show "(\<forall> i < 2^m. (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> max ma x))"
        proof
          fix i::nat
          show "i < 2 ^ m\<longrightarrow>
         (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
         (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x)"
          proof
            assume "i < 2^m"
            show " (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
         (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x)" 
            proof 
              show "(high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n))"
              proof
                assume "high (max ma x) n = i"
                show "both_member_options (?nextTreeList ! i) (low (max ma x) n)"
                proof(cases "high x n = high ma n")
                  case True
                  have "invar_vebt (treeList ! i ) n"
                    by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                  have "length ?nextTreeList = 2^m"
                    using "2" highlowprop by auto
                  hence "?nextTreeList ! i = vebt_insert (treeList ! i) (low x n)" 
                    using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                      "2" True \<open>high (max ma x) n = i\<close> \<open>i < 2 ^ m\<close> concat_inth  length_take max_def
                    by (metis Suc_eq_plus1 append_Cons append_Nil nth_list_update_eq upd_conv_take_nth_drop)
                  hence "vebt_member (?nextTreeList ! i) (low x n)" using  Un_iff \<open>i < 2 ^ m\<close>
                      \<open>invar_vebt (treeList ! i) n\<close> both_member_options_equiv_member highlowprop 
                      list.set_intros(1) set_append valid_insert_both_member_options_add
                    by (metis "11" True \<open>high (max ma x) n = i\<close> max_def)
                  then show ?thesis proof(cases "mi = ma")
                    case True
                    then show ?thesis 
                      by (metis \<open>(take (high x n) treeList @ [VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] @ drop (high x n + 1) treeList) ! i = VEBT_Insert.vebt_insert (treeList ! i) (low x n)\<close> \<open>mi \<noteq> max ma x\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop max_def valid_insert_both_member_options_add)
                  next
                    case False
                    hence "vebt_member (treeList ! i) (low ma n)" 
                      by (metis "7" True \<open>high (max ma x) n = i\<close> \<open>invar_vebt (treeList ! i) n\<close> both_member_options_equiv_member highlowprop linorder_cases max.absorb3 max.absorb4 mimaxrel)
                    hence "vebt_member (?nextTreeList ! i) (low ma n) \<or> (low ma n = low x n)" 
                      using post_member_pre_member[of " (treeList ! i)" n "low x n" "low  ma n" ]
                      by (metis "2" "4.IH"(1) \<open>(take (high x n) treeList @ [VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] @ drop (high x n + 1) treeList) ! i = VEBT_Insert.vebt_insert (treeList ! i) (low x n)\<close> \<open>i < 2 ^ m\<close> both_member_options_equiv_member highlowprop member_bound nth_mem valid_insert_both_member_options_pres)
                    then show ?thesis 
                      by (metis "2" "4.IH"(1) True \<open>(take (high x n) treeList @ [VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] @ drop (high x n + 1) treeList) ! i = VEBT_Insert.vebt_insert (treeList ! i) (low x n)\<close> \<open>high (max ma x) n = i\<close> both_member_options_equiv_member highlowprop max_def nth_mem valid_insert_both_member_options_add)
                  qed
                next
                  case False
                  then show ?thesis 
                  proof(cases "x < ma")
                    case True
                    then show ?thesis
                      by (metis "2" "7" False \<open>high (max ma x) n = i\<close> \<open>i < 2 ^ m\<close> abcdef highlowprop less_trans max.strict_order_iff nth_repl)
                  next
                    case False
                    hence "x > ma" 
                      using mimaxrel nat_neq_iff by blast
                    then show ?thesis
                      by (metis "2" "4.IH"(1) One_nat_def \<open>high (max ma x) n = i\<close> add.right_neutral add_Suc_right append_Cons highlowprop max.commute max.strict_order_iff nth_list_update_eq nth_mem self_append_conv2 upd_conv_take_nth_drop valid_insert_both_member_options_add)
                  qed
                qed
              qed
              show "(\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x)" 
              proof
                fix y
                show "high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x"
                proof
                  assume bb:"high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)"
                  show " mi < y \<and> y \<le> max ma x" 
                  proof(cases "i = high x n")
                    case True  
                    hence cc:" i = high x n" by simp
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = vebt_insert (treeList ! i) (low x n)" 
                      using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                      by (metis "2" Suc_eq_plus1 append_Cons append_self_conv2 cc highlowprop nth_list_update_eq upd_conv_take_nth_drop)
                    hence "invar_vebt (?nextTreeList ! i) n"
                      by (simp add: "11" True)
                    hence "vebt_member (treeList ! i) (low y n) \<or> (low y n) = (low x n)"
                      by (metis \<open>invar_vebt (treeList ! i) n\<close> aa bb highlowprop member_bound post_member_pre_member valid_member_both_member_options)
                    then show ?thesis 
                    proof(cases "low y n = low x n")
                      case True
                      hence "high x n = high y n \<and> low y n = low x n" 
                        by (simp add: bb cc) 
                      hence "x = y"
                        by (metis bit_split_inv)
                      then show ?thesis 
                        using abcdef by auto
                    next
                      case False 
                      hence "vebt_member (treeList ! i) (low y n)" 
                        using \<open>vebt_member (treeList ! i) (low y n) \<or> low y n = low x n\<close> by blast
                      hence "mi \<noteq> ma " using 5 inthall 
                        by (metis "2" \<open>i < 2 ^ m\<close> min_Null_member not_min_Null_member)
                      then show ?thesis
                        using "7" \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) (low y n)\<close> \<open>invar_vebt (treeList ! i) n\<close> bb both_member_options_equiv_member max.coboundedI1 by blast
                    qed
                  next 
                    case False
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = (treeList ! i)" 
                      by (metis "2" False \<open>i < 2 ^ m\<close> highlowprop nth_repl)
                    hence "both_member_options (treeList !i) (low y n)" 
                      using bb by auto
                    hence "mi \<noteq> ma " using 5 "2" \<open>i < 2 ^ m\<close> by force
                    then show ?thesis using 7
                      using \<open>both_member_options (treeList ! i) (low y n)\<close> \<open>i < 2 ^ m\<close> bb max.coboundedI1 by blast
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      then show ?thesis using invar_vebt.intros(4)[of ?nextTreeList  n ?nextSummary m deg mi "max ma x"]
        by (smt (z3) "10" "11" "12" "13" "15" "2" "3" "8" One_nat_def abcdef add.right_neutral add_Suc_right append_Cons highlowprop leD max.cobounded2 max.commute pos_n_replace self_append_conv2 upd_conv_take_nth_drop)
    next
      case False
      hence abcdef: "x < mi" 
        using antisym_conv3 mimaxrel by blast
      let ?h = "high mi n" and ?l="low mi n"
      have highlowprop: "high mi n < 2^m \<and> low mi n < 2^n" 
        using "1" "3" "4.hyps"(3) "4.hyps"(7) "4.hyps"(8) deg_not_0 exp_split_high_low(1) exp_split_high_low(2) le_less_trans by blast
      have 10:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x = 
                 Node (Some (x, max mi ma)) deg  (treeList[?h:=vebt_insert (treeList ! ?h) ?l])
                               (if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary) "
        by (metis "1" "2" "4.hyps"(3) "9" abcdef deg_not_0 div_greater_zero_iff highlowprop insert_simp_excp mimaxrel)   
      let ?maxnew = "max mi ma" and ?nextTreeList = "(treeList[ ?h :=vebt_insert (treeList ! ?h) ?l])" and
        ?nextSummary = "(if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary)"
      have 11: "( \<forall> t \<in> set ?nextTreeList. invar_vebt t n)" proof
        fix t
        assume " t \<in> set ?nextTreeList"
        then obtain i where "?nextTreeList ! i = t \<and> i < 2^m"
          by (metis "2" in_set_conv_nth length_list_update)
        show "invar_vebt t n" 
          by (metis "2" "4.IH"(1) \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = t \<and> i < 2 ^ m\<close> highlowprop nth_list_update_eq nth_list_update_neq nth_mem)       
      qed 
      have 12: "invar_vebt ?nextSummary n"
        using "1" "4.IH"(2) "8" highlowprop by presburger
      have 13: "\<forall> i < 2^m. (\<exists> y. both_member_options (?nextTreeList ! i) y) \<longleftrightarrow> ( both_member_options ?nextSummary i)"
      proof
        fix i
        show "i < 2 ^ m \<longrightarrow> (\<exists>y. both_member_options   ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
        proof
          assume "i< 2^m"
          show "(\<exists>y. both_member_options ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
          proof(cases "minNull (treeList ! high mi n)")
            case True
            hence tc: "minNull (treeList ! high mi n)" by simp
            hence nsprop: "?nextSummary = vebt_insert summary ?h" by simp
            have insprop:"?nextTreeList ! ?h = vebt_insert (treeList ! ?h) ?l"
              by (simp add: "2" highlowprop)
            then show ?thesis 
            proof(cases "i = ?h")
              case True
              have 161:"\<nexists> y. vebt_member (treeList ! ?h) y" 
                by (simp add: min_Null_member tc)
              hence 162:"\<nexists> y. both_member_options (treeList ! ?h) y"
                by (metis "2" "4.IH"(1) highlowprop nth_mem valid_member_both_member_options)
              hence 163:"\<not> both_member_options summary i"
                using "11" "2" "4" True \<open>i < 2 ^ m\<close> by blast
              have 164:"?nextTreeList ! i = vebt_insert (treeList ! ?h) ?l"
                using True insprop by simp
              have 165:"invar_vebt (vebt_insert (treeList ! ?h) ?l) n"
                by (simp add: "2" "4.IH"(1) highlowprop)
              have 166:"both_member_options (vebt_insert (treeList ! ?h) ?l) ?l" using myIHs[of "treeList ! ?h" ?l] 
                by (metis "0" "2" highlowprop in_set_member inthall valid_insert_both_member_options_add)
              have 167:"\<exists> y. both_member_options ((?nextTreeList) ! i) y "
                using "164" "166" by auto
              then show ?thesis
                using "1" "11" "2" True nsprop valid_insert_both_member_options_add highlowprop by auto
            next
              case False
              have "?nextTreeList ! i = treeList ! i" 
                using False by fastforce
              have fstprop:"both_member_options ((?nextTreeList) ! i) y \<Longrightarrow> both_member_options (?nextSummary) i " for y 
                using "1" "4" \<open>i < 2 ^ m\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = treeList ! i\<close> highlowprop valid_insert_both_member_options_pres by auto
              moreover  have" both_member_options (?nextSummary) i \<Longrightarrow> \<exists> y . both_member_options ((?nextTreeList) ! i) y "
              proof-
                assume  "both_member_options (?nextSummary) i "
                have "i \<noteq> high mi n" 
                  by (simp add: False)
                hence "both_member_options summary i"
                  by (smt (z3) "1" "12" \<open>both_member_options (if minNull (treeList ! high mi n) then VEBT_Insert.vebt_insert summary (high mi n) else summary) i\<close> \<open>i < 2 ^ m\<close> both_member_options_equiv_member highlowprop post_member_pre_member)
                hence "\<exists> y. both_member_options (treeList ! i) y"
                  by (simp add: "4" \<open>i < 2 ^ m\<close>)
                then show ?thesis 
                  by (simp add: \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = treeList ! i\<close>)
              qed
              ultimately show ?thesis by auto
            qed
          next
            case False
            hence "?nextSummary = summary" by simp
            hence "\<exists> y. both_member_options (treeList ! high mi n) y"
              using not_min_Null_member False by blast
            hence "both_member_options summary (high mi n)"
              using "4" highlowprop by blast
            hence " both_member_options (?nextTreeList ! high mi n) ?l"
              by (metis "0" "2" highlowprop nth_list_update_eq nth_mem valid_insert_both_member_options_add)
            then show ?thesis
              by (metis (full_types, opaque_lifting) "4" False \<open>both_member_options summary (high mi n)\<close> \<open>i < 2 ^ m\<close> nth_list_update_neq)            
          qed
        qed
      qed
      have 14: "(x = max ma mi \<longrightarrow> (\<forall> t \<in> set ?nextTreeList. \<nexists> y. both_member_options t y))" 
        using mimaxrel by linarith
      have 15: "x \<le> max ma mi  \<and> max ma mi < 2^deg"
        using "6" abcdef by linarith
      have 16:  "(x \<noteq> max ma mi \<longrightarrow> (\<forall> i < 2^m. (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> x < y \<and> y \<le> max ma mi)))"
      proof
        assume "x \<noteq> max ma mi"
        show "(\<forall> i < 2^m. (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> x < y \<and> y \<le> max ma mi))"
        proof
          fix i::nat
          show "i < 2 ^ m\<longrightarrow>
         (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
         (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi)"
          proof
            assume "i < 2^m"
            show " (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
         (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi)" 
            proof 
              show "(high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n))"
              proof
                assume "high (max ma mi) n = i"
                show "both_member_options (?nextTreeList ! i) (low (max ma mi) n)"
                proof(cases "high mi n = high ma n")
                  case True
                  have "invar_vebt (treeList ! i ) n"
                    by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                  have "length ?nextTreeList = 2^m"
                    using "2" highlowprop by auto
                  hence "?nextTreeList ! i = vebt_insert (treeList ! i) (low mi n)" 
                    using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                    by (metis "2" True \<open>high (max ma mi) n = i\<close> highlowprop max_def nth_list_update_eq)
                  hence "vebt_member (?nextTreeList ! i) (low mi n)" 
                    by (metis "11" "2" True \<open>high (max ma mi) n = i\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop max_def set_update_memI valid_insert_both_member_options_add valid_member_both_member_options)
                  then show ?thesis
                  proof(cases "mi = ma")
                    case True
                    then show ?thesis
                    using \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low mi n)\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop valid_insert_both_member_options_add by force
                  next
                    case False
                    hence "vebt_member (treeList ! i) (low ma n)"
                      using "6" "7" \<open>high (max ma mi) n = i\<close> \<open>i < 2 ^ m\<close> \<open>invar_vebt (treeList ! i) n\<close> both_member_options_equiv_member by auto
                    hence "vebt_member (?nextTreeList ! i) (low ma n) \<or> (low ma n = low mi n)" 
                      using post_member_pre_member[of " (treeList ! i)" n "low mi n" "low  ma n" ]
                    by (metis "11" "2" "7" True \<open>high (max ma mi) n = i\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low mi n)\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop max_def member_bound set_update_memI valid_insert_both_member_options_pres valid_member_both_member_options)
                    then show ?thesis
                      by (metis "11" "2" "4.hyps"(7) "7" False True \<open>high (max ma mi) n = i\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low mi n)\<close> both_member_options_equiv_member highlowprop less_irrefl max.commute max_def set_update_memI)
                  qed
                next
                  case False
                  hence "?nextTreeList ! i = treeList ! i"
                    by (metis "4.hyps"(7) \<open>high (max ma mi) n = i\<close> max.commute max_def nth_list_update_neq)
                  then show ?thesis
                    by (metis "4.hyps"(7) "7" False \<open>high (max ma mi) n = i\<close> \<open>i < 2 ^ m\<close> max.orderE)
                qed
              qed
              show "(\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi)" 
              proof
                fix y
                show "high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi"
                proof
                  assume bb:"high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)"
                  show " x < y \<and> y \<le> max ma mi" 
                  proof(cases "i = high mi n")
                    case True  
                    hence cc:" i = high mi n" by simp
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = vebt_insert (treeList ! i) (low mi n)" 
                      using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                      by (simp add: cc highlowprop)
                    hence "invar_vebt (?nextTreeList ! i) n" 
                      by (simp add: "2" "4.IH"(1) cc highlowprop)
                    hence "vebt_member (treeList ! i) (low y n) \<or> (low y n) = (low mi n)" 
                      by (metis \<open>invar_vebt (treeList ! i) n\<close> aa bb both_member_options_equiv_member highlowprop member_bound post_member_pre_member)
                    then show ?thesis 
                    proof(cases "low y n = low mi n")
                      case True
                      hence "high mi n = high y n \<and> low y n = low mi n" 
                        by (simp add: bb cc) 
                      hence "mi = y"
                        by (metis bit_split_inv)
                      then show ?thesis 
                        using abcdef by auto
                    next
                      case False 
                      hence "vebt_member (treeList ! i) (low y n)" 
                        using \<open>vebt_member (treeList ! i) (low y n) \<or> low y n = low mi n\<close> by blast
                      hence "mi \<noteq> ma " using 5 inthall 
                        by (metis "2" \<open>i < 2 ^ m\<close> min_Null_member not_min_Null_member)
                      then show ?thesis 
                        using "7"
                        by (metis \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) (low y n)\<close> \<open>invar_vebt (treeList ! i) n\<close> abcdef bb both_member_options_equiv_member max.absorb1 max.strict_order_iff max_less_iff_conj)
                    qed
                  next 
                    case False
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = (treeList ! i)" 
                      using False by auto
                    hence "both_member_options (treeList ! i) (low y n)" 
                      using bb by auto
                    hence "mi \<noteq> ma " using 5  "2" \<open>i < 2 ^ m\<close> by force
                    then show ?thesis using 7
                      by (metis \<open>both_member_options (treeList ! i) (low y n)\<close> \<open>i < 2 ^ m\<close> abcdef bb max.absorb1 max.strict_order_iff max_less_iff_conj)
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      then show ?thesis using invar_vebt.intros(4)[of ?nextTreeList n ?nextSummary m deg x "max ma mi"]
        by (smt (z3) "10" "11" "12" "13" "14" "15" "2" "3" "4.hyps"(3) "4.hyps"(7) length_list_update max.absorb1 max.absorb2)
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence myIHs: "x \<in> set treeList \<Longrightarrow> invar_vebt x n \<Longrightarrow> xa < 2 ^ n \<Longrightarrow> invar_vebt (vebt_insert x xa) n" for x xa by simp
  hence 0: "( \<forall> t \<in> set treeList. invar_vebt t n)" and 1: " invar_vebt summary m" and 2:"length treeList = 2^m" and 3:" deg = n+m" and 
    4: "(\<forall> i < 2^m. (\<exists> y. both_member_options (treeList ! i) y) \<longleftrightarrow> ( both_member_options summary i))" and 
    5: "(mi = ma \<longrightarrow> (\<forall> t \<in> set treeList. \<nexists> y. both_member_options t y))" and 6:"mi \<le> ma  \<and> ma < 2^deg" and
    7: "(mi \<noteq> ma \<longrightarrow> (\<forall> i < 2^m. (high ma n = i \<longrightarrow> both_member_options (treeList ! i) (low ma n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (treeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> ma)))"
    and 8: "Suc n = m" and 9: "deg div 2 = n" 
    using "5" add_self_div_2 apply blast+  by (simp add: "5.hyps"(3) "5.hyps"(4))
  then show ?case  
  proof(cases "x = mi \<or> x = ma")
    case True
    then show ?thesis using insert_simp_mima[of x mi ma deg treeList summary] 
        invar_vebt.intros(5)[of treeList n summary m deg mi ma] 
      by (smt "0" "1" "2" "3" "4" "5" "5.hyps"(3) "5.hyps"(7) "5.hyps"(8) "7" "9" div_less not_less not_one_le_zero set_n_deg_not_0)    
  next
    case False
    hence mimaxrel: "x \<noteq> mi \<and> x \<noteq> ma" by simp
    then show ?thesis 
    proof(cases "mi < x")
      case True 
      hence abcdef: "mi < x" by simp
      let ?h = "high x n" and ?l="low x n"
      have highlowprop: "high x n < 2^m \<and> low x n < 2^n" 
        by (metis "1" "2" "3" "5.IH"(1) "5.prems" div_eq_0_iff add_nonneg_eq_0_iff deg_not_0 div_exp_eq exp_split_high_low(2) high_def not_one_le_zero one_add_one power_not_zero set_n_deg_not_0 zero_le_one zero_neq_one)
      have 10:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x = 
                 Node (Some (mi, max x ma)) deg  (treeList[?h :=vebt_insert (treeList ! ?h) ?l])
                               (if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary) " 
        using "2" "3" False True \<open>high x n < 2 ^ m \<and> low x n < 2  ^ n\<close> insert_simp_norm 
        by (smt "5.IH"(1) "9" div_greater_zero_iff div_if less_Suc_eq_0_disj not_one_le_zero set_n_deg_not_0)
      let ?maxnew = "max x ma" and ?nextTreeList = "(treeList[ ?h :=vebt_insert (treeList ! ?h) ?l])" and
        ?nextSummary = "(if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary)"
      have 11: "( \<forall> t \<in> set ?nextTreeList. invar_vebt t n)" 
      proof
        fix t
        assume " t \<in> set ?nextTreeList"
        then obtain i where "i <2^m \<and> ?nextTreeList ! i = t" 
          by (metis "2" in_set_conv_nth length_list_update)
        show "invar_vebt t n" 
          by (metis "2" "5.IH"(1) \<open>i < 2 ^ m \<and> treeList[high x n := VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] ! i = t\<close> highlowprop nth_list_update_eq nth_list_update_neq nth_mem)
      qed 
      have 12: "invar_vebt ?nextSummary m" 
        by (simp add: "1" "5.IH"(2) highlowprop)
      have 13: "\<forall> i < 2^m. (\<exists> y. both_member_options (?nextTreeList ! i) y) \<longleftrightarrow> ( both_member_options ?nextSummary i)" 
      proof
        fix i
        show "i < 2 ^ m \<longrightarrow> (\<exists>y. both_member_options   ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
        proof
          assume "i< 2^m"
          show "(\<exists>y. both_member_options ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
          proof(cases "minNull (treeList ! high x n)")
            case True
            hence tc: "minNull (treeList ! high x n)" by simp
            hence nsprop: "?nextSummary = vebt_insert summary ?h" by simp
            have insprop:"?nextTreeList ! ?h = vebt_insert (treeList ! ?h) ?l"
              by (simp add: "2" highlowprop)
            then show ?thesis 
            proof(cases "i = ?h")
              case True
              have 161:"\<nexists> y. vebt_member (treeList ! ?h) y" 
                by (simp add: min_Null_member tc)
              hence 162:"\<nexists> y. both_member_options (treeList ! ?h) y"
                by (metis "0" "2" highlowprop nth_mem valid_member_both_member_options)
              hence 163:"\<not> both_member_options summary i"
                using "11" "2" "4" True \<open>i < 2 ^ m\<close> by blast
              have 164:"?nextTreeList ! i = vebt_insert (treeList ! ?h) ?l"
                using True insprop by simp
              have 165:"invar_vebt (vebt_insert (treeList ! ?h) ?l) n"
                by (simp add: "11" "2" highlowprop set_update_memI)
              have 166:"both_member_options (vebt_insert (treeList ! ?h) ?l) ?l" using myIHs[of "treeList ! ?h" ?l] 
                by (metis "0" "2" highlowprop in_set_member inthall valid_insert_both_member_options_add)
              have 167:"\<exists> y. both_member_options ((?nextTreeList) ! i) y "
                using "164" "166" by auto
              then show ?thesis
                using "1" "11" "2" True nsprop valid_insert_both_member_options_add highlowprop by auto
            next
              case False
              have "?nextTreeList ! i = treeList ! i" 
                using False by auto
              have fstprop:"both_member_options ((?nextTreeList) ! i) y \<Longrightarrow> both_member_options (?nextSummary) i " for y 
                using "1" "4" \<open>i < 2 ^ m\<close> \<open>treeList[high x n := VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] ! i = treeList ! i\<close> highlowprop valid_insert_both_member_options_pres by auto
              moreover  have" both_member_options (?nextSummary) i \<Longrightarrow> \<exists> y . both_member_options ((?nextTreeList) ! i) y "
              proof-
                assume  "both_member_options (?nextSummary) i "
                have "i \<noteq> high x n" 
                  by (simp add: False)
                hence "both_member_options summary i"
                  by (smt "1" "12" \<open>both_member_options (if minNull (treeList ! high x n) then vebt_insert summary (high x n) else summary) i\<close> \<open>i < 2 ^ m\<close> both_member_options_equiv_member highlowprop post_member_pre_member)
                hence "\<exists> y. both_member_options (treeList ! i) y"
                  by (simp add: "4" \<open>i < 2 ^ m\<close>)
                then show ?thesis 
                  by (simp add: \<open>treeList[high x n := VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] ! i = treeList ! i\<close>)
              qed
              ultimately show ?thesis by auto
            qed
          next
            case False
            hence "?nextSummary = summary" by simp
            hence "\<exists> y. both_member_options (treeList ! high x n) y"
              using not_min_Null_member False by blast
            hence "both_member_options summary (high x n)"
              using "4" highlowprop by blast
            hence " both_member_options (?nextTreeList ! high x n) ?l"
              by (metis "0" "2" highlowprop nth_list_update_eq nth_mem valid_insert_both_member_options_add)
            then show ?thesis
              by (metis (full_types) "4" False \<open>both_member_options summary (high x n)\<close> \<open>i < 2 ^ m\<close> nth_list_update_neq)
          qed 
        qed
      qed
      have 14: "(mi = max ma x \<longrightarrow> (\<forall> t \<in> set ?nextTreeList. \<nexists> y. both_member_options t y))"
        using True max_less_iff_conj by blast
      have 15: "mi \<le> max ma x  \<and> max ma x < 2^deg"
        using "5.hyps"(8) "5.prems" abcdef by auto 
      have 16:  "(mi \<noteq> max ma x \<longrightarrow> (\<forall> i < 2^m. (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> max ma x)))"
      proof
        assume "mi \<noteq> max ma x"
        show "(\<forall> i < 2^m. (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> mi < y \<and> y \<le> max ma x))"
        proof
          fix i::nat
          show "i < 2 ^ m\<longrightarrow>
                (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
                (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x)"
          proof
            assume "i < 2^m"
            show " (high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n)) \<and>
                   (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x)" 
            proof 
              show "(high (max ma x) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma x) n))"
              proof
                assume "high (max ma x) n = i"
                show "both_member_options (?nextTreeList ! i) (low (max ma x) n)"
                proof(cases "high x n = high ma n")
                  case True
                  have "invar_vebt (treeList ! i ) n"
                    by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                  have "length ?nextTreeList = 2^m"
                    using "2" highlowprop by auto
                  hence "?nextTreeList ! i = vebt_insert (treeList ! i) (low x n)"  
                    using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                    by (metis "2" False True \<open>high (max ma x) n = i\<close> highlowprop linorder_neqE_nat max.commute max.strict_order_iff nth_list_update_eq)
                  hence "vebt_member (?nextTreeList ! i) (low x n)" 
                    by (metis "11" "2" True \<open>high (max ma x) n = i\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop max_def set_update_memI valid_insert_both_member_options_add valid_member_both_member_options)
                  then show ?thesis
                  proof(cases "mi = ma")
                    case True
                    then show ?thesis
                      by (metis \<open>treeList[high x n := VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low x n)\<close> \<open>invar_vebt (treeList ! i) n\<close> abcdef highlowprop max.commute max.strict_order_iff valid_insert_both_member_options_add)
                  next
                    case False
                    hence "vebt_member (treeList ! i) (low ma n)"
                      by (metis "7" True \<open>high (max ma x) n = i\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop max_def valid_member_both_member_options)
                    hence "vebt_member (?nextTreeList ! i) (low ma n) \<or> (low ma n = low x n)" 
                      using post_member_pre_member[of " (treeList ! i)" n "low x n" "low  ma n" ] 
                      by (metis "1" "11" "2" "3" "5.hyps"(8) "7" False True \<open>treeList[high x n := VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low x n)\<close> \<open>invar_vebt (treeList ! i) n\<close> deg_not_0 exp_split_high_low(2) highlowprop nth_list_update_neq set_update_memI valid_insert_both_member_options_pres valid_member_both_member_options)
                    then show ?thesis
                      by (metis "11" "2" True \<open>high (max ma x) n = i\<close> \<open>treeList[high x n := VEBT_Insert.vebt_insert (treeList ! high x n) (low x n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low x n)\<close> \<open>invar_vebt (treeList ! i) n\<close> both_member_options_equiv_member highlowprop max_def set_update_memI valid_insert_both_member_options_add)
                  qed
                next
                  case False
                  then show ?thesis
                    by (metis "0" "2" "7" \<open>high (max ma x) n = i\<close> \<open>i < 2 ^ m\<close> \<open>mi \<noteq> max ma x\<close> highlowprop max_def nth_list_update_eq nth_list_update_neq nth_mem valid_insert_both_member_options_add)                  
                qed
              qed
              show "(\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x)" 
              proof
                fix y
                show "high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> mi < y \<and> y \<le> max ma x"
                proof
                  assume bb:"high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)"
                  show " mi < y \<and> y \<le> max ma x" 
                  proof(cases "i = high x n")
                    case True  
                    hence cc:" i = high x n" by simp
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = vebt_insert (treeList ! i) (low x n)" 
                      using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                      by (simp add: cc highlowprop)
                    hence "invar_vebt (?nextTreeList ! i) n"
                      by (simp add: "2" "5.IH"(1) cc highlowprop)
                    hence "vebt_member (treeList ! i) (low y n) \<or> (low y n) = (low x n)"
                      by (metis \<open>high y n = i \<and> both_member_options ((treeList[?h:=vebt_insert (treeList ! high x n) (low x n)]) ! i) (low y n)\<close>
                          \<open>invar_vebt (treeList ! i) n\<close> aa highlowprop member_bound post_member_pre_member valid_member_both_member_options)
                    then show ?thesis
                    proof(cases "low y n = low x n")
                      case True
                      hence "high x n = high y n \<and> low y n = low x n" 
                        by (simp add: bb cc) 
                      hence "x = y"
                        by (metis bit_split_inv)
                      then show ?thesis 
                        using abcdef by auto
                    next
                      case False 
                      hence "vebt_member (treeList ! i) (low y n)" 
                        using \<open>vebt_member (treeList ! i) (low y n) \<or> low y n = low x n\<close> by blast
                      hence "mi \<noteq> ma " using 5 inthall 
                        by (metis "2" \<open>i < 2 ^ m\<close> min_Null_member not_min_Null_member)
                      then show ?thesis
                        using "7" \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) (low y n)\<close> \<open>invar_vebt (treeList ! i) n\<close> bb both_member_options_equiv_member max.coboundedI1 by blast
                    qed
                  next 
                    case False
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = (treeList ! i)" 
                      using False by auto
                    hence "both_member_options (treeList ! i) (low y n)" 
                      using bb by auto
                    hence "mi \<noteq> ma " using 5 
                      using "2" \<open>i < 2 ^ m\<close> by fastforce
                    then show ?thesis using 7
                      using \<open>both_member_options (treeList ! i) (low y n)\<close> \<open>i < 2 ^ m\<close> bb max.coboundedI1 by blast
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      then show ?thesis using invar_vebt.intros(5)[of ?nextTreeList  n ?nextSummary m deg mi "max ma x"]
        by (smt (z3) "10" "11" "12" "13" "14" "15" "2" "3" "8" length_list_update max.commute)
    next
      case False
      hence abcdef: "x < mi" 
        using antisym_conv3 mimaxrel by blast
      let ?h = "high mi n" and ?l="low mi n"
      have highlowprop: "high mi n < 2^m \<and> low mi n < 2^n"  
        by (metis (full_types) "1" "2" "3" "5.IH"(1) "5.hyps"(7) "5.hyps"(8) deg_not_0 exp_split_high_low(1) exp_split_high_low(2) le_less_trans not_one_le_zero set_n_deg_not_0)
      have 10:"vebt_insert (Node (Some (mi,ma)) deg  treeList summary) x = 
                 Node (Some (x, max mi ma)) deg  (treeList[ ?h :=vebt_insert (treeList ! ?h) ?l])
                               (if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary) "
        by (metis "0" "2" "9" abcdef div_less highlowprop insert_simp_excp mimaxrel not_less not_one_le_zero set_n_deg_not_0)
      let ?maxnew = "max mi ma" and ?nextTreeList = "(treeList[ ?h:=vebt_insert (treeList ! ?h) ?l])" and
        ?nextSummary = "(if minNull (treeList ! ?h) then  vebt_insert summary ?h else summary)"
      have 11: "( \<forall> t \<in> set ?nextTreeList. invar_vebt t n)" 
      proof
        fix t
        assume " t \<in> set ?nextTreeList"
        then obtain i where "i < 2^m \<and> ?nextTreeList ! i = t"
          by (metis "2" in_set_conv_nth length_list_update)
        thus "invar_vebt t n"
          by (metis "2" "5.IH"(1) highlowprop nth_list_update_eq nth_list_update_neq nth_mem)
      qed 
      have 12: "invar_vebt ?nextSummary m"
        by (simp add: "1" "5.IH"(2) highlowprop)
      have 13: "\<forall> i < 2^m. (\<exists> y. both_member_options (?nextTreeList ! i) y) \<longleftrightarrow> ( both_member_options ?nextSummary i)"
      proof
        fix i
        show "i < 2 ^ m \<longrightarrow> (\<exists>y. both_member_options   ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
        proof
          assume "i< 2^m"
          show "(\<exists>y. both_member_options ((?nextTreeList) ! i) y) = both_member_options (?nextSummary) i "
          proof(cases "minNull (treeList ! high mi n)")
            case True
            hence tc: "minNull (treeList ! high mi n)" by simp
            hence nsprop: "?nextSummary = vebt_insert summary ?h" by simp
            have insprop:"?nextTreeList ! ?h = vebt_insert (treeList ! ?h) ?l"
              by (simp add: "2" highlowprop)
            then show ?thesis 
            proof(cases "i = ?h")
              case True
              have 161:"\<nexists> y. vebt_member (treeList ! ?h) y" 
                by (simp add: min_Null_member tc)
              hence 162:"\<nexists> y. both_member_options (treeList ! ?h) y" 
                by (metis "0" "2" highlowprop nth_mem valid_member_both_member_options)
              hence 163:"\<not> both_member_options summary i"
                using "11" "2" "4" True \<open>i < 2 ^ m\<close> by blast
              have 164:"?nextTreeList ! i = vebt_insert (treeList ! ?h) ?l"
                using True insprop by simp
              have 165:"invar_vebt (vebt_insert (treeList ! ?h) ?l) n" 
                by (simp add: "11" "2" highlowprop set_update_memI)
              have 166:"both_member_options (vebt_insert (treeList ! ?h) ?l) ?l" using myIHs[of "treeList ! ?h" ?l] 
                by (metis "0" "2" highlowprop in_set_member inthall valid_insert_both_member_options_add)
              have 167:"\<exists> y. both_member_options ((?nextTreeList) ! i) y "
                using "164" "166" by auto
              then show ?thesis
                using "1" "11" "2" True nsprop valid_insert_both_member_options_add highlowprop by auto
            next
              case False
              have "?nextTreeList ! i = treeList ! i" 
                by (metis False nth_list_update_neq)
              have fstprop:"both_member_options ((?nextTreeList) ! i) y \<Longrightarrow> both_member_options (?nextSummary) i " for y 
                using "1" "4" \<open>i < 2 ^ m\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = treeList ! i\<close> highlowprop valid_insert_both_member_options_pres by auto
              moreover  have" both_member_options (?nextSummary) i \<Longrightarrow> \<exists> y . both_member_options ((?nextTreeList) ! i) y "
              proof-
                assume  "both_member_options (?nextSummary) i "
                have "i \<noteq> high mi n" 
                  by (simp add: False)
                hence "both_member_options summary i"
                  by (smt (z3) "1" "12" \<open>both_member_options (if minNull (treeList ! high mi n) then VEBT_Insert.vebt_insert summary (high mi n) else summary) i\<close> \<open>i < 2 ^ m\<close> both_member_options_equiv_member highlowprop post_member_pre_member)
                hence "\<exists> y. both_member_options (treeList ! i) y"
                  by (simp add: "4" \<open>i < 2 ^ m\<close>)
                then show ?thesis 
                  by (simp add: \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = treeList ! i\<close>)
              qed
              ultimately show ?thesis by auto
            qed
          next
            case False
            hence "?nextSummary = summary" by simp
            hence "\<exists> y. both_member_options (treeList ! high mi n) y"
              using not_min_Null_member False by blast
            hence "both_member_options summary (high mi n)"
              using "4" highlowprop by blast
            hence " both_member_options (?nextTreeList ! high mi n) ?l"
              by (metis "0" "2" highlowprop nth_list_update_eq nth_mem valid_insert_both_member_options_add)
            then show ?thesis  
              by (metis (full_types) "4" False \<open>both_member_options summary (high mi n)\<close> \<open>i < 2 ^ m\<close> nth_list_update_neq)
          qed
        qed
      qed
      have 14: "(x = max ma mi \<longrightarrow> (\<forall> t \<in> set ?nextTreeList. \<nexists> y. both_member_options t y))" 
        using mimaxrel by linarith
      have 15: "x \<le> max ma mi  \<and> max ma mi < 2^deg"
        using "6" abcdef by linarith
      have 16:  "(x \<noteq> max ma mi \<longrightarrow> (\<forall> i < 2^m. (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> x < y \<and> y \<le> max ma mi)))"
      proof
        assume "x \<noteq> max ma mi"
        show "(\<forall> i < 2^m. (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
                                         (\<forall> y. (high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)  ) \<longrightarrow> x < y \<and> y \<le> max ma mi))"
        proof
          fix i::nat
          show "i < 2 ^ m\<longrightarrow>
                (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
                (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi)"
          proof
            assume "i < 2^m"
            show " (high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n)) \<and>
                   (\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi)" 
            proof 
              show "(high (max ma mi) n = i \<longrightarrow> both_member_options (?nextTreeList ! i) (low (max ma mi) n))"
              proof
                assume "high (max ma mi) n = i"
                show "both_member_options (?nextTreeList ! i) (low (max ma mi) n)"
                proof(cases "high mi n = high ma n")
                  case True
                  have "invar_vebt (treeList ! i ) n"
                    by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                  have "length ?nextTreeList = 2^m"
                    using "2" highlowprop by auto
                  hence "?nextTreeList ! i = vebt_insert (treeList ! i) (low mi n)" 
                    using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                    by (metis "2" "5.hyps"(7) True \<open>high (max ma mi) n = i\<close> highlowprop max.orderE nth_list_update_eq)
                  hence "vebt_member (?nextTreeList ! i) (low mi n)" 
                    by (metis "11" "2" True \<open>high (max ma mi) n = i\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop max_def set_update_memI valid_insert_both_member_options_add valid_member_both_member_options)
                  then show ?thesis
                  proof(cases "mi = ma")
                    case True
                    then show ?thesis
                      using \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low mi n)\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop valid_insert_both_member_options_add by auto
                  next
                    case False
                    hence "vebt_member (treeList ! i) (low ma n)"
                      using "6" "7" \<open>high (max ma mi) n = i\<close> \<open>i < 2 ^ m\<close> \<open>invar_vebt (treeList ! i) n\<close> both_member_options_equiv_member by auto
                    hence "vebt_member (?nextTreeList ! i) (low ma n) \<or> (low ma n = low mi n)" 
                      using post_member_pre_member[of " (treeList ! i)" n "low mi n" "low  ma n" ] 
                      by (metis "1" "11" "2" "3" "5.hyps"(8) "7" True \<open>high (max ma mi) n = i\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low mi n)\<close> \<open>invar_vebt (treeList ! i) n\<close> deg_not_0 exp_split_high_low(2) highlowprop max_def set_update_memI valid_insert_both_member_options_pres valid_member_both_member_options)
                    then show ?thesis 
                      by (metis "5.hyps"(7) "7" False \<open>high (max ma mi) n = i\<close> \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) (low ma n)\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = VEBT_Insert.vebt_insert (treeList ! i) (low mi n)\<close> \<open>invar_vebt (treeList ! i) n\<close> highlowprop max.absorb1 member_bound valid_insert_both_member_options_pres)
                  qed
                next
                  case False
                  hence "?nextTreeList ! i = treeList ! i" 
                    by (metis "5.hyps"(7) \<open>high (max ma mi) n = i\<close> max.commute max_def nth_list_update_neq)
                  then show ?thesis 
                  proof(cases "mi < ma")
                    case True
                    then show ?thesis 
                      by (metis "5.hyps"(7) "7" False \<open>high (max ma mi) n = i\<close> \<open>i < 2 ^ m\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = treeList ! i\<close> max.commute max_def)
                  next
                    case False
                    hence "mi \<ge> ma " by simp
                    hence "mi = ma"  
                      by (simp add: "6" eq_iff)
                    hence "\<not>both_member_options (treeList ! i) (low (max ma mi) n)" using 5  "2" \<open>i < 2 ^ m\<close> by auto
                    then show ?thesis
                      by (metis "11" "2" \<open>high (max ma mi) n = i\<close> \<open>mi = ma\<close> \<open>treeList[high mi n := VEBT_Insert.vebt_insert (treeList ! high mi n) (low mi n)] ! i = treeList ! i\<close> highlowprop max.idem nth_list_update_eq set_update_memI valid_insert_both_member_options_add)
                  qed
                qed
              qed
              show "(\<forall>y. high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi)" 
              proof
                fix y
                show "high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n) \<longrightarrow> x < y \<and> y \<le> max ma mi"
                proof
                  assume bb:"high y n = i \<and> both_member_options (?nextTreeList ! i) (low y n)"
                  show " x < y \<and> y \<le> max ma mi" 
                  proof(cases "i = high mi n")
                    case True  
                    hence cc:" i = high mi n" by simp
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = vebt_insert (treeList ! i) (low mi n)" 
                      using concat_inth[of "take (high x n) treeList" "vebt_insert (treeList ! i) (low x n)" "drop (high x n + 1) treeList"]
                      by (simp add: cc highlowprop)
                    hence "invar_vebt (?nextTreeList ! i) n"
                      by (simp add: "2" "5.IH"(1) \<open>i < 2 ^ m\<close> highlowprop)
                    hence "vebt_member (treeList ! i) (low y n) \<or> (low y n) = (low mi n)"
                      by (metis \<open>invar_vebt (treeList ! i) n\<close> aa bb both_member_options_equiv_member highlowprop member_bound post_member_pre_member)
                    then show ?thesis 
                    proof(cases "low y n = low mi n")
                      case True
                      hence "high mi n = high y n \<and> low y n = low mi n" 
                        by (simp add: bb cc) 
                      hence "mi = y"
                        by (metis bit_split_inv)
                      then show ?thesis 
                        using abcdef by auto
                    next
                      case False 
                      hence "vebt_member (treeList ! i) (low y n)" 
                        using \<open>vebt_member (treeList ! i) (low y n) \<or> low y n = low mi n\<close> by blast
                      hence "mi \<noteq> ma " using 5 inthall 
                        by (metis "2" \<open>i < 2 ^ m\<close> min_Null_member not_min_Null_member)
                      then show ?thesis 
                        using "7"
                        by (metis \<open>i < 2 ^ m\<close> \<open>vebt_member (treeList ! i) (low y n)\<close> \<open>invar_vebt (treeList ! i) n\<close> abcdef bb both_member_options_equiv_member max.absorb1 max.strict_order_iff max_less_iff_conj)
                    qed
                  next 
                    case False
                    have "invar_vebt (treeList ! i ) n"
                      by (metis "0" "2" \<open>i < 2 ^ m\<close> in_set_member inthall)
                    have "length ?nextTreeList = 2^m"
                      using "2" highlowprop by auto
                    hence aa:"?nextTreeList ! i = (treeList ! i)" 
                      using False by auto
                    hence "both_member_options (treeList ! i) (low y n)" 
                      using bb by auto
                    hence "mi \<noteq> ma " using 5 "2" \<open>i < 2 ^ m\<close> by fastforce
                    then show ?thesis using 7
                      by (metis \<open>both_member_options (treeList ! i) (low y n)\<close> \<open>i < 2 ^ m\<close> abcdef bb max.absorb1 max.strict_order_iff max_less_iff_conj)
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      then show ?thesis using invar_vebt.intros(5)[of ?nextTreeList n ?nextSummary m deg x "max ma mi"]
        by (smt (z3) "10" "11" "12" "13" "14" "15" "2" "3" "5.hyps"(7) "8" length_list_update max.absorb2 max.orderE)
    qed
  qed
qed

subsection \<open>Correctness with Respect to Set Interpretation\<close>

theorem insert_corr: 
  assumes "invar_vebt t n " and "x < 2^n "  
  shows " set_vebt' t \<union> {x} = set_vebt' (vebt_insert t x) "
proof
  show "set_vebt' t \<union> {x} \<subseteq> set_vebt' (vebt_insert t x)"
  proof
    fix y
    assume "y \<in> set_vebt' t \<union> {x}"
    show "y \<in>set_vebt' (vebt_insert t x)"
    proof(cases "x=y")
      case True
      then show ?thesis 
        by (metis (full_types) assms(1) assms(2) both_member_options_equiv_member mem_Collect_eq set_vebt'_def valid_insert_both_member_options_add valid_pres_insert)
    next
      case False
      have "vebt_member t y" 
        using False \<open>y \<in> set_vebt' t \<union> {x}\<close> set_vebt'_def by auto
      hence "vebt_member (vebt_insert t x) y" 
        by (meson assms(1) assms(2) both_member_options_equiv_member member_bound valid_insert_both_member_options_pres valid_pres_insert)
      then show ?thesis 
        by (simp add: set_vebt'_def)
    qed
  qed 
  show " set_vebt' (vebt_insert t x) \<subseteq> set_vebt' t \<union> {x} "
  proof
    fix y
    assume "y \<in> set_vebt' (vebt_insert t x)"
    show "y \<in>set_vebt' t \<union> {x}"
    proof(cases "x=y")
      case True
      then show ?thesis by simp
    next
      case False
      hence "vebt_member t y \<or> x=y" using post_member_pre_member 
        using \<open>y \<in> set_vebt' (vebt_insert t x)\<close> assms(1) assms(2) set_vebt'_def member_bound valid_pres_insert by fastforce
      hence "vebt_member t y" 
        by (simp add: False)
      hence "y \<in> set_vebt' t"
        by (simp add: set_vebt'_def)
      then show ?thesis by simp
    qed
  qed
qed

corollary insert_correct:  assumes "invar_vebt t n " and "x < 2^n "  shows 
  " set_vebt t \<union> {x} = set_vebt (vebt_insert t x) " 
  using assms(1) assms(2) insert_corr set_vebt_set_vebt'_valid valid_pres_insert by blast

fun insert'::"VEBT \<Rightarrow> nat \<Rightarrow> VEBT" where
  "insert' (Leaf a b) x = vebt_insert (Leaf a b) x"|
  "insert' (Node info deg treeList summary) x = 
   (if x \<ge> 2^deg then (Node info deg treeList summary ) 
                  else vebt_insert (Node info deg treeList summary) x)"

theorem insert'_pres_valid: assumes "invar_vebt t n" shows "invar_vebt (insert' t x) n"
  using assms  
  apply cases
  apply (metis One_nat_def deg1Leaf insert'.simps(1) vebt_insert.simps(1))
  apply (metis assms insert'.simps(2) leI valid_pres_insert)+
  done

theorem insert'_correct: assumes "invar_vebt t n" 
  shows "set_vebt (insert' t x) = (set_vebt t \<union> {x})\<inter>{0..2^n-1}"
proof(cases t)
  case (Node x11 x12 x13 x14)
  then show ?thesis 
  proof(cases "x < 2^n")
    case True
    hence "set_vebt (insert'  t x) = set_vebt(vebt_insert t x)" 
      by (metis Node assms deg_deg_n insert'.simps(2) leD)
    moreover hence "set_vebt(vebt_insert t x) = set_vebt t \<union> {x}" 
      using True assms insert_correct by auto
    moreover hence "set_vebt t \<union> {x} = (set_vebt t \<union> {x})\<inter>{0..2^n-1} " 
      by (metis Diff_Diff_Int True assms calculation(1) inf_le1 inrange le_inf_iff order_refl subset_antisym set_vebt'_def set_vebt_def set_vebt_set_vebt'_valid valid_pres_insert)
    ultimately  show ?thesis by simp
  next
    case False
    hence "set_vebt (insert'  t x) = set_vebt t" 
      by (metis Node assms deg_deg_n insert'.simps(2) leI)
    moreover hence "set_vebt t = (set_vebt t \<union> {x})\<inter>{0..2^n-1} "
      by (smt (z3) False Int_commute Int_insert_right_if0 Un_Int_assoc_eq assms atLeastAtMost_iff boolean_algebra_cancel.sup0 inf_bot_right inrange le_add_diff_inverse le_imp_less_Suc one_le_numeral one_le_power plus_1_eq_Suc sup_commute set_vebt_set_vebt'_valid)
    ultimately  show ?thesis by simp
  qed
next
  case (Leaf x21 x22)
  then show ?thesis 
    apply(auto simp add:  insert'.simps vebt_insert.simps set_vebt_def both_member_options_def)
    using assms
       apply cases
       apply simp+
    using assms 
      apply cases 
      apply simp+
    using assms 
      apply cases 
      apply simp+
    using assms 
      apply cases 
      apply simp+
    done
qed

end
end

