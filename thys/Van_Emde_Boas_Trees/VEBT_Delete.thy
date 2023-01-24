(*by Ammer*)
theory VEBT_Delete imports VEBT_Pred VEBT_Succ
begin

section \<open>Deletion\<close>

subsection \<open>Function Definition\<close>

context begin
  interpretation VEBT_internal .

fun vebt_delete :: "VEBT \<Rightarrow> nat \<Rightarrow> VEBT" where
  "vebt_delete (Leaf a b) 0 = Leaf False b"|
  "vebt_delete (Leaf a b) (Suc 0) = Leaf a False"|
  "vebt_delete (Leaf a b) (Suc (Suc n)) = Leaf a b"|
  "vebt_delete (Node None deg treeList summary) _ = (Node None deg treeList summary)"|
  "vebt_delete (Node (Some (mi, ma)) 0 trLst smry) x = (Node (Some (mi, ma)) 0 trLst smry) "|
  "vebt_delete (Node (Some (mi, ma)) (Suc 0) tr sm) x = (Node (Some (mi, ma)) (Suc 0) tr sm) "|
  "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =( 
           if (x < mi \<or> x > ma) then (Node (Some (mi, ma)) deg treeList summary)
           else if (x = mi \<and> x = ma) then (Node None deg treeList summary)
           else let xn = (if x = mi 
                          then the (vebt_mint summary) * 2^(deg div 2) 
                                + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                           else x);
                     minn = (if x = mi then xn else mi);
                     l = low xn (deg div 2);
                     h = high xn (deg div 2) in
                     if h < length treeList 
                     then(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in
                              if minNull newnode 
                              then( let sn = vebt_delete summary h in(
                                   Node (Some (minn, if xn  = ma then 
                                                       (let maxs = vebt_maxt sn in (
                                                        if maxs = None 
                                                        then minn 
                                                        else 2^(deg div 2) * the maxs 
                                                           + the (vebt_maxt (newlist ! the maxs))))
                                                     else ma)) deg newlist sn))
                              else (Node (Some (minn, (if xn = ma 
                                               then h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                               else ma))) deg newlist summary ))
                     else (Node (Some (mi, ma)) deg treeList summary))"

end


subsection \<open>Auxiliary Lemmas\<close>

context VEBT_internal begin

context begin

lemma delt_out_of_range: 
  assumes "x < mi \<or> x > ma" and "deg \<ge> 2" 
  shows
  "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =(Node (Some (mi, ma)) deg treeList summary)" 
  using vebt_delete.simps(7)[of mi ma "deg-2" treeList summary x]
  by (metis add_2_eq_Suc assms(1) assms(2) le_add_diff_inverse)

lemma del_single_cont: 
  assumes "x = mi \<and> x = ma" and "deg \<ge> 2" 
  shows  "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (Node None deg treeList summary)" 
  using vebt_delete.simps(7)[of mi ma "deg-2" treeList summary x]
  by (metis add_2_eq_Suc assms(1) assms(2) le_add_diff_inverse nat_less_le)

lemma del_in_range: 
  assumes "x \<ge> mi \<and> x \<le> ma" and "mi \<noteq> ma" and "deg \<ge> 2" 
  shows
  " vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = ( let xn = (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x);
                   minn = (if x = mi then xn else mi);
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode] in
                             if minNull newnode 
                             then(   
                                let sn = vebt_delete summary h in
                               (Node (Some (minn, if xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then minn 
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (minn, (if xn = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary )
                       )else 
                        (Node (Some (mi, ma)) deg treeList summary))"
  using vebt_delete.simps(7)[of mi ma "deg-2" treeList summary x] 
  by (smt (z3) add_2_eq_Suc assms(1) assms(2) assms(3) leD le_add_diff_inverse)

lemma del_x_not_mia:
  assumes "x > mi \<and> x \<le> ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high x (deg div 2) = h" and
  "low x (deg div 2) = l"and  "high x (deg div 2) < length treeList"
  shows
  " vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (
                  let  newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode] in
                             if minNull newnode 
                             then(   
                                let sn = vebt_delete summary h in
                               (Node (Some (mi, if x  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (mi, (if x = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary )
)"
  using del_in_range[of mi x ma deg treeList summary] unfolding Let_def
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) nat_less_le by fastforce

lemma del_x_not_mi: 
  assumes "x > mi \<and> x \<le> ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high x (deg div 2) = h" and
  "low x (deg div 2) = l"and " newnode = vebt_delete (treeList ! h) l" 
  and "newlist = treeList[h:= newnode]" and "high x (deg div 2) < length treeList"
  shows
  " vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (
                  if minNull newnode 
                             then(   
                                let sn = vebt_delete summary h in
                               (Node (Some (mi, if x  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (mi, (if x = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary )
)" using del_x_not_mia[of mi x ma deg h l treeList summary]
  by (smt (z3) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8))

lemma del_x_not_mi_new_node_nil: 
  assumes "x > mi \<and> x \<le> ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high x (deg div 2) = h" and
    "low x (deg div 2) = l"and " newnode = vebt_delete (treeList ! h) l" and "minNull newnode " and 
    "sn = vebt_delete summary h"  and "newlist =treeList[h:= newnode]" and  "high x (deg div 2) < length treeList"
  shows
  " vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  (Node (Some (mi, if x  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma))  deg newlist sn)"
  using del_x_not_mi[of mi x ma deg h l newnode treeList] 
  by (metis assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9))

lemma del_x_not_mi_newnode_not_nil:
  assumes "x > mi \<and> x \<le> ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high x (deg div 2) = h" and
    "low x (deg div 2) = l"and " newnode = vebt_delete (treeList ! h) l" and "\<not>  minNull newnode " and
     "newlist = treeList[h:= newnode]" and"high x (deg div 2) < length treeList"
  shows
  " vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =
                               (Node (Some (mi, (if x = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary )" 
  using del_x_not_mi[of mi x ma deg h l newnode treeList newlist summary] 
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) by auto

lemma del_x_mia: assumes "x = mi \<and> x < ma" and "mi \<noteq> ma"  and "deg \<ge> 2" 
  shows "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =( 
              let xn = the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary))); 
                                             minn = xn;
                   l = low xn (deg div 2);
                   h = high xn (deg div 2) in
                    if h < length treeList 
                       then(
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in
                             if minNull newnode 
                             then(   
                                let sn = vebt_delete summary h in
                               (Node (Some (minn, if xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then minn 
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (minn, (if xn = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary )
                       )else 
                        (Node (Some (mi, ma)) deg treeList summary)
           )"
  using del_in_range[of mi x ma deg treeList summary]
  using assms(1) assms(3) nat_less_le order_refl by fastforce

lemma del_x_mi: 
  assumes "x = mi \<and> x < ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high xn (deg div 2) = h" and
    "xn =  the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) "
    "low xn (deg div 2) = l"and  "high xn (deg div 2) < length treeList"
  shows
  "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =( 
                          let newnode = vebt_delete (treeList ! h) l;
                              newlist = treeList[h:= newnode]in
                             if minNull newnode 
                             then(   
                                let sn = vebt_delete summary h in
                               (Node (Some (xn, if xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (xn, (if xn = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary ))
          "
  using del_x_mia[of x mi ma deg treeList summary]
  by (smt (z3) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7))

lemma del_x_mi_lets_in: 
  assumes "x = mi \<and> x < ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high xn (deg div 2) = h" and
    "xn =  the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) "
    "low xn (deg div 2) = l"and  "high xn (deg div 2) < length treeList" and
    " newnode = vebt_delete (treeList ! h) l" and " newlist = treeList[h:= newnode]" 
  shows  "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =(      if minNull newnode 
                             then(   
                                let sn = vebt_delete summary h in
                               (Node (Some (xn, if xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (xn, (if xn = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary ))"
  using del_x_mi[of x mi ma deg xn h summary treeList l]
  by (smt (z3) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9))

lemma del_x_mi_lets_in_minNull: 
  assumes "x = mi \<and> x < ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high xn (deg div 2) = h" and
    "xn =  the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) "
    "low xn (deg div 2) = l"and  "high xn (deg div 2) < length treeList" and
    "newnode = vebt_delete (treeList ! h) l" and " newlist =treeList[h:= newnode]" and
    "minNull newnode " and " sn = vebt_delete summary h"
  shows
  "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =
                               (Node (Some (xn, if xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma))   deg newlist sn)"
  using del_x_mi_lets_in[of x mi ma deg xn h summary treeList l newnode newlist]
  by (metis assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9))

lemma del_x_mi_lets_in_not_minNull: 
  assumes "x = mi \<and> x < ma" and "mi \<noteq> ma"  and "deg \<ge> 2"  and "high xn (deg div 2) = h" and
    "xn =  the (vebt_mint summary) * 2^(deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) "
    "low xn (deg div 2) = l"and  "high xn (deg div 2) < length treeList" and
    " newnode = vebt_delete (treeList ! h) l" and " newlist = treeList[h:= newnode]" and
    "\<not>minNull newnode "
  shows
  "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =
                               (Node (Some (xn, (if xn = ma then
                                                    h * 2^(deg div 2) + the( vebt_maxt (newlist ! h))
                                                            else ma)))
                                 deg newlist summary )" 
  using del_x_mi_lets_in[of x mi ma deg xn h summary treeList l newnode newlist] 
  by (meson assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9))

theorem dele_bmo_cont_corr:"invar_vebt t n \<Longrightarrow> (both_member_options (vebt_delete t x) y \<longleftrightarrow> x \<noteq> y \<and> both_member_options t y)"
proof(induction t n arbitrary: x y rule: invar_vebt.induct)
  case (1 a b)
  have "(both_member_options (vebt_delete (Leaf a b) x) y) \<Longrightarrow> (x \<noteq> y \<and> both_member_options (Leaf a b) y)"
    by (metis One_nat_def both_member_options_def vebt_buildup.cases vebt_delete.simps(1) vebt_delete.simps(2) vebt_delete.simps(3) membermima.simps(1) naive_member.simps(1))
  moreover have "(x \<noteq> y \<and> both_member_options (Leaf a b) y) \<Longrightarrow>(both_member_options (vebt_delete (Leaf a b) x) y)" 
    by (metis One_nat_def both_member_options_def vebt_buildup.cases vebt_delete.simps(1) vebt_delete.simps(2) vebt_delete.simps(3) membermima.simps(1) naive_member.simps(1))
  ultimately show ?case by blast
next
  case (2 treeList n summary m deg)
  hence "deg \<ge> 2" 
    by (metis Suc_leI deg_not_0 dual_order.strict_trans2 less_add_same_cancel1 numerals(2))
  hence " (vebt_delete (Node None deg treeList summary) x) = (Node None deg treeList summary)" by simp
  moreover have "\<not>vebt_member (Node None deg treeList summary) y" by simp
  moreover hence "\<not>both_member_options (Node None deg treeList summary) y" 
    using invar_vebt.intros(2)[of treeList n summary m deg] 2 
    by (metis valid_member_both_member_options)
  moreover hence "\<not>both_member_options (vebt_delete (Node None deg treeList summary) x) y" by simp
  ultimately show ?case 
    by force
next
  case (3 treeList n summary m deg)
  hence "deg \<ge> 2" 
    by (metis One_nat_def add_mono le_add1 numeral_2_eq_2 plus_1_eq_Suc set_n_deg_not_0)
  hence " (vebt_delete (Node None deg treeList summary) x) = (Node None deg treeList summary)" by simp
  moreover have "\<not>vebt_member (Node None deg treeList summary) y" by simp
  moreover hence "\<not>both_member_options (Node None deg treeList summary) y" 
    using invar_vebt.intros(3)[of treeList n summary m deg] 3
    by (metis valid_member_both_member_options)
  moreover hence "\<not>both_member_options (vebt_delete (Node None deg treeList summary) x) y" by simp
  ultimately show ?case 
    by force
next
  case (4 treeList n summary m deg mi ma)
  hence tvalid: "invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" 
    using invar_vebt.intros(4)[of treeList n summary m deg mi ma] by simp
  hence "mi \<le> ma" and "deg div 2 = n" and "ma \<le> 2^deg" using 4 
    by  (auto simp add: "4.hyps"(3) "4.hyps"(4))
  hence dp:"deg \<ge> 2"
    using "4.hyps"(1) "4.hyps"(3) deg_not_0 div_greater_zero_iff by blast
  then show ?case proof(cases "x <mi \<or> x > ma")
    case True
    hence "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (Node (Some (mi, ma)) deg treeList summary)" 
      using delt_out_of_range[of x mi ma deg treeList summary]  \<open>2 \<le> deg\<close> by blast
    then show ?thesis 
      by (metis "4.hyps"(7) True tvalid leD member_inv not_less_iff_gr_or_eq valid_member_both_member_options)
  next
    case False
    hence "mi \<le> x \<and> x \<le> ma" by simp
    hence "x < 2^deg"
      using "4.hyps"(8) order.strict_trans1 by blast
    then show ?thesis 
    proof(cases "x = mi \<and> x = ma")
      case True
      hence "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (Node None deg treeList summary)"
        using del_single_cont[of x mi ma deg treeList summary] \<open>2 \<le> deg\<close> by blast
      moreover hence "invar_vebt (Node None deg treeList summary) deg" 
        using "4"(4) "4.IH"(1) "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) True mi_eq_ma_no_ch tvalid invar_vebt.intros(2) by force
      moreover hence "\<not> vebt_member (Node None deg treeList summary) y" by simp
      moreover hence "\<not>both_member_options (Node None deg treeList summary) y" 
        using calculation(2) valid_member_both_member_options by blast
      then show ?thesis 
        by (metis True calculation(1) member_inv not_less_iff_gr_or_eq tvalid valid_member_both_member_options)
    next
      case False
      hence mimapr:"mi < ma"
        by (metis "4.hyps"(7) \<open>mi \<le> x \<and> x \<le> ma\<close> le_antisym nat_less_le)
      then show ?thesis 
      proof(cases "x \<noteq> mi")
        case True
        hence xmi:"x \<noteq> mi" by simp
        let ?h ="high x n"
        let ?l = "low x n"
        have "?h < length treeList"
          using "4"(10) "4"(4) "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) \<open>mi \<le> x \<and> x \<le> ma\<close> deg_not_0 exp_split_high_low(1) by auto
        let ?newnode = "vebt_delete (treeList ! ?h) ?l" 
        let ?newlist = "treeList[?h:= ?newnode]"
        have "length treeList = length ?newlist" by simp
        hence hprolist: "?newlist ! ?h = ?newnode" 
          by (meson \<open>high x n < length treeList\<close> nth_list_update_eq)
        have nothprolist: "i \<noteq> ?h \<and> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by auto
        then show ?thesis 
        proof(cases "minNull ?newnode")
          case True
          let ?sn = "vebt_delete summary ?h"
          let ?newma= "(if x  = ma then (let maxs = vebt_maxt ?sn in  (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)"
          let ?delsimp =" (Node (Some (mi, ?newma))  deg ?newlist ?sn)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_not_mi_new_node_nil[of mi x ma deg ?h ?l ?newnode treeList ?sn summary ?newlist]
            by (metis True \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>mi < ma\<close> \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>x \<noteq> mi\<close> less_not_refl3 order.not_eq_order_implies_strict)
          moreover have "both_member_options (?delsimp) y \<Longrightarrow> (x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)"
          proof-
            assume "both_member_options (?delsimp) y"
            hence "y = mi \<or> y = ?newma \<or> 
                (both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist)" 
              using both_member_options_from_complete_tree_to_child[of deg mi ?newma ?newlist ?sn y] dp 
              by (smt (z3) Suc_1 Suc_le_D both_member_options_def membermima.simps(4) naive_member.simps(3))
            moreover have "y = mi \<Longrightarrow> ?thesis"
              by (meson \<open>x \<noteq> mi\<close> both_member_options_equiv_member vebt_mint.simps(3) mint_member tvalid)
            moreover have "y = ?newma \<Longrightarrow> ?thesis"
            proof-
              assume "y = ?newma"
              show ?thesis
              proof(cases "x =  ma")
                case True
                let ?maxs = "vebt_maxt ?sn"
                have "?newma = (if ?maxs = None then mi
                                else 2 ^ (deg div 2) * the ?maxs +   the (vebt_maxt
                   ((treeList[(high x n):= vebt_delete (treeList !  (high  x n)) (low x n)]) !
                    the ?maxs)))"   using True by force
                then show ?thesis 
                proof(cases "?maxs = None ")
                  case True
                  then show ?thesis 
                    using \<open>(if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma) = (if vebt_maxt (vebt_delete summary (high x n)) = None then mi else 2 ^ (deg div 2) * the (vebt_maxt (vebt_delete summary (high x n))) + the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! the (vebt_maxt (vebt_delete summary (high x n))))))\<close> \<open>y = (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma)\<close> calculation(2) by presburger
                next
                  case False
                  then obtain maxs where "Some maxs = ?maxs" by force
                  hence "both_member_options ?sn maxs" 
                    by (simp add: maxbmo)
                  hence "both_member_options summary maxs \<and> maxs \<noteq> ?h"
                    using "4.IH"(2) by blast
                  hence "?newlist ! the ?maxs = treeList ! maxs" 
                    by (metis "4.hyps"(1) \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> option.sel member_bound nothprolist valid_member_both_member_options)
                  have "maxs < 2^m" 
                    using "4.hyps"(1) \<open>both_member_options summary maxs \<and> maxs \<noteq> high x n\<close> member_bound valid_member_both_member_options by blast
                  hence "the (vebt_maxt  (?newlist ! the ?maxs)) = the (vebt_maxt (treeList ! maxs))" 
                    by (simp add: \<open>treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! the (vebt_maxt (vebt_delete summary (high x n))) = treeList ! maxs\<close>)
                  have "\<exists> z. both_member_options(treeList ! maxs) z" 
                    by (simp add: "4.hyps"(5) \<open>both_member_options summary maxs \<and> maxs \<noteq> high x n\<close> \<open>maxs < 2 ^ m\<close>)
                  moreover have "invar_vebt (treeList ! maxs) n" using 4 
                    by (metis \<open>maxs < 2 ^ m\<close> inthall member_def)
                  ultimately obtain maxi where "Some maxi  = (vebt_maxt (treeList ! maxs))" 
                    by (metis empty_Collect_eq maxt_corr_help_empty not_None_eq set_vebt'_def valid_member_both_member_options)
                  hence "maxi < 2^n" 
                    by (metis \<open>invar_vebt (treeList ! maxs) n\<close> maxt_member member_bound)
                  hence "both_member_options (treeList ! maxs) maxi" 
                    using \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> maxbmo by presburger
                  hence "2 ^ (deg div 2) * the ?maxs +  the
                   (vebt_maxt (?newlist !  the ?maxs)) = 2^n * maxs + maxi "
                    by (metis \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>deg div 2 = n\<close> \<open>the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! the (vebt_maxt (vebt_delete summary (high x n))))) = the (vebt_maxt (treeList ! maxs))\<close> option.sel)
                  hence "y =  2^n * maxs + maxi" 
                    using False True \<open>y = (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma)\<close> by fastforce
                  hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
                    by (metis "4.hyps"(2) Suc_1 \<open>both_member_options (treeList ! maxs) maxi\<close> \<open>deg div 2 = n\<close> \<open>maxi < 2 ^ n\<close> \<open>maxs < 2 ^ m\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp high_inv low_inv mult.commute plus_1_eq_Suc) 
                  moreover hence "y \<noteq> x" 
                    by (metis \<open>both_member_options summary maxs \<and> maxs \<noteq> high x n\<close> \<open>maxi < 2 ^ n\<close> \<open>y = 2 ^ n * maxs + maxi\<close> high_inv mult.commute)
                  ultimately show ?thesis by force
                qed
              next
                case False
                hence "?newma = ma" by simp
                moreover hence "y \<noteq> x" 
                  using False \<open>y = ?newma\<close> by presburger
                then show ?thesis 
                  by (metis False \<open>y =?newma\<close> both_member_options_equiv_member vebt_maxt.simps(3) maxt_member tvalid)
              qed
            qed
            moreover have "(both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist) \<Longrightarrow> ?thesis"
            proof-
              assume assm:"both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist"
              show ?thesis
              proof(cases "(high  y (deg div 2)) = ?h")
                case True
                hence "both_member_options ?newnode (low y (deg div 2)) " using hprolist   by (metis assm) 
                moreover hence "invar_vebt (treeList ! (high y (deg div 2))) n" 
                  by (metis "4.IH"(1) True \<open>high x n < length treeList\<close> inthall member_def)
                ultimately have "both_member_options (treeList ! ?h) (low y (deg div 2)) \<and> (low y (deg div 2)) \<noteq> (low x (deg div 2))"
                  by (metis "4.IH"(1) \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> inthall member_def)
                then show ?thesis 
                  by (metis Suc_1 True \<open>high x n < length treeList\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp plus_1_eq_Suc)
              next
                case False
                hence "x \<noteq> y"  
                  using \<open>deg div 2 = n\<close> by blast
                moreover hence "(?newlist ! (high  y (deg div 2))) = treeList ! (high y (deg div 2))" using nothprolist 
                  using "4.hyps"(2) False \<open>length treeList = length ?newlist\<close> assm by presburger
                moreover hence "both_member_options (treeList ! (high y (deg div 2)) ) (low y (deg div 2))" 
                  using assm by presburger
                moreover hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y" 
                  by (metis One_nat_def Suc_leD \<open>length treeList = length ?newlist\<close> assm both_member_options_from_chilf_to_complete_tree dp numeral_2_eq_2) 
                ultimately show ?thesis by blast
              qed
            qed
            ultimately show ?thesis by fastforce
          qed
          moreover have " (x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y) \<Longrightarrow> both_member_options (?delsimp) y"
          proof-
            assume "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)"
            hence aa:"x \<noteq> y" and bb:"y = mi \<or> y = ma \<or> (both_member_options (treeList ! (high y n)) (low y n) \<and> high y n < length treeList)" 
               apply auto[1]  by (metis Suc_1 \<open>deg div 2 = n\<close> \<open>x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            show "both_member_options (?delsimp) y"
            proof-
              have "y = mi \<Longrightarrow>both_member_options (?delsimp) y"
                by (metis Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4))
              moreover have "y = ma \<Longrightarrow> both_member_options (?delsimp) y"
                using aa maxbmo vebt_maxt.simps(3) by presburger
              moreover have "both_member_options (treeList ! (high y n)) (low y n) \<Longrightarrow>both_member_options (?delsimp) y "
              proof-
                assume assmy: "both_member_options (treeList ! (high y n)) (low y n)" 
                then show "both_member_options (?delsimp) y "
                proof(cases "high y n = ?h")
                  case True
                  moreover hence "?newlist ! (high y n) = ?newnode" 
                    using hprolist by auto
                  hence 0:"invar_vebt (treeList !(high y n)) n" using 4 
                    by (metis True \<open>high x n < length treeList\<close> inthall member_def)
                  moreover have 1:"low y n \<noteq> low x n" 
                    by (metis True aa bit_split_inv)
                  moreover have 11:" (treeList !(high y n)) \<in> set treeList"
                    by (metis True \<open>high x n < length treeList\<close> inthall member_def)
                  ultimately have "  (\<forall> xa. both_member_options ?newnode xa = 
                         ((low x n) \<noteq> xa \<and> both_member_options (treeList ! ?h) xa))"
                    by (simp add: "4.IH"(1)) 
                  hence "((low x n) \<noteq> xa \<and> both_member_options (treeList ! ?h) xa) \<Longrightarrow>  both_member_options ?newnode xa" for xa  by blast
                  moreover have "((low x n) \<noteq> (low y n) \<and> both_member_options (treeList ! ?h) (low y n))" using 1 
                    using True assmy by presburger
                  ultimately have "both_member_options ?newnode (low y n)" by blast
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD True \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>length treeList = length ?newlist\<close> both_member_options_from_chilf_to_complete_tree dp hprolist numerals(2))
                next
                  case False
                  hence "?newlist ! (high y n) = treeList ! (high y n)" by auto
                  hence "both_member_options (?newlist !(high y n)) (low y n)" 
                    using assmy by presburger
                  then show ?thesis 
                    by (smt (z3) Suc_1 Suc_le_D \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> aa add_leD1 bb both_member_options_def both_member_options_from_chilf_to_complete_tree dp membermima.simps(4) plus_1_eq_Suc)
                qed
              qed
              ultimately show ?thesis using bb by fastforce
            qed
          qed
          ultimately show ?thesis by metis
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (mi, ?newma))  deg ?newlist summary)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = ?delsimp"
            using del_x_not_mi_newnode_not_nil[of mi x ma deg ?h ?l ?newnode treeList ?newlist summary] False xmi mimapr 
            using \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>mi \<le> x \<and> x \<le> ma\<close> dp nat_less_le plus_1_eq_Suc by fastforce
          moreover have "both_member_options ?delsimp y 
                      \<Longrightarrow> x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
          proof-
            assume ssms: "both_member_options ?delsimp y "
            hence aaaa: "y = mi \<or> y = ?newma \<or> (both_member_options (?newlist ! (high y n)) (low y n) \<and> high y n < length ?newlist)"
              by (smt (z3) Suc_1 Suc_le_D \<open>deg div 2 = n\<close> both_member_options_def dp membermima.simps(4) naive_member.simps(3))
            show " x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            proof-
              have "y = mi \<Longrightarrow>?thesis"
                by (metis Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4) xmi)
              moreover have " y = ?newma \<Longrightarrow> ?thesis"
              proof-
                assume "y = ?newma"
                show ?thesis
                proof(cases "x = ma")
                  case True
                  hence "?newma =?h * 2 ^ (deg div 2) +the(vebt_maxt(?newlist ! ?h))" 
                    by metis
                  have "?newlist ! ?h = ?newnode"   using hprolist by blast
                  obtain maxi where maxidef:"Some maxi = vebt_maxt(?newlist ! ?h)"
                    by (metis False hprolist vebt_maxt.elims minNull.simps(1) minNull.simps(4))
                  have aa:"invar_vebt (treeList ! ?h) n" 
                    by (metis "4.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  moreover hence ab:"maxi \<noteq> ?l \<and> both_member_options ?newnode maxi" 
                    by (metis "4.IH"(1) \<open>high x n < length treeList\<close> hprolist inthall maxbmo maxidef member_def)
                  ultimately have ac:"maxi \<noteq> ?l \<and> both_member_options (treeList ! ?h)  maxi" 
                    by (metis "4.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  hence ad:"maxi < 2^n" 
                    using \<open>invar_vebt (treeList ! high x n) n\<close> member_bound valid_member_both_member_options by blast
                  then show ?thesis
                    by (metis Suc_1 \<open>(if x = ma then high x n * 2 ^ (deg div 2) + the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! high x n)) else ma) = high x n * 2 ^ (deg div 2) + the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! high x n))\<close> \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>y = (if x = ma then high x n * 2 ^ (deg div 2) + the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! high x n)) else ma)\<close> ac add_leD1 both_member_options_from_chilf_to_complete_tree dp option.sel high_inv low_inv maxidef plus_1_eq_Suc)
                next
                  case False
                  then show ?thesis
                    by (simp add: \<open>y = ?newma\<close> maxbmo)
                qed
              qed
              moreover have "both_member_options (?newlist ! (high y n)) (low y n) \<Longrightarrow> ?thesis"
              proof-
                assume assmy:"both_member_options (?newlist ! (high y n)) (low y n)"
                then show ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "?newlist ! (high y n) = ?newnode" 
                    using hprolist by presburger
                  have "invar_vebt (treeList ! ?h) n"
                    by (metis "4.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  hence "low y n \<noteq> ?l \<and> both_member_options (treeList ! ?h ) (low y n)" 
                    by (metis "4.IH"(1) True \<open>high x n < length treeList\<close> assmy hprolist inthall member_def)
                  then show ?thesis 
                    by (metis Suc_1 True \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp plus_1_eq_Suc)
                next
                  case False
                  hence "?newlist ! (high y n) = treeList !(high y n)" by auto
                  then show ?thesis 
                    by (metis False Suc_1 \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> aaaa add_leD1 both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) dp plus_1_eq_Suc)
                qed
              qed
              ultimately show ?thesis 
                using aaaa by fastforce
            qed
          qed

          moreover have "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)\<Longrightarrow>
                                both_member_options ?delsimp y"
          proof-
            assume assm: "x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            hence abcv:"y = mi \<or> y = ma \<or> ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))" 
              by (metis Suc_1 \<open>deg div 2 = n\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            thus " both_member_options ?delsimp y"
            proof-
              have "y = mi \<Longrightarrow> ?thesis"
                by (metis Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4))
              moreover have " y = ma \<Longrightarrow> ?thesis" 
                using assm maxbmo vebt_maxt.simps(3) by presburger
              moreover have " both_member_options (treeList ! (high y n)) (low y n) \<Longrightarrow> ?thesis"
              proof-
                assume myass: "both_member_options (treeList ! (high y n)) (low y n) "
                thus ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "low y n \<noteq> ?l" 
                    by (metis assm bit_split_inv)
                  hence pp:"?newlist ! ?h = ?newnode" 
                    using hprolist by blast
                  hence "invar_vebt (treeList ! ?h) n"
                    by (metis "4.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  hence "both_member_options ?newnode (low y n)" 
                    by (metis "4.IH"(1) True \<open>high x n < length treeList\<close> \<open>low y n \<noteq> low x n\<close> in_set_member inthall myass)
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD True \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>length treeList = length ?newlist\<close> both_member_options_from_chilf_to_complete_tree dp numerals(2) pp)
                next
                  case False
                  hence pp:"?newlist ! (high y n) = treeList ! (high y n)" using nothprolist by auto
                  then show ?thesis 
                    by (metis Suc_1 \<open>deg div 2 = n\<close> \<open>length treeList = length (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)])\<close> add_leD1 assm both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) member_inv myass plus_1_eq_Suc tvalid valid_member_both_member_options)
                qed
              qed 
              then show ?thesis
                by (metis Suc_1 Suc_leD \<open>deg div 2 = n\<close> assm both_member_options_from_complete_tree_to_child calculation(1) calculation(2) dp)
            qed
          qed
          ultimately show ?thesis by metis
        qed
      next
        case False
        hence "x = mi" by simp
        have "both_member_options summary (high ma n)" 
          by (metis "4"(10) "4"(11) "4"(7) "4.hyps"(4) div_eq_0_iff Suc_leI Suc_le_D div_exp_eq dual_order.irrefl high_def mimapr nat.simps(3))
        hence "vebt_member summary (high ma n)" 
          using "4.hyps"(1) valid_member_both_member_options by blast
        obtain summin where "Some summin = vebt_mint summary" 
          by (metis "4.hyps"(1) \<open>vebt_member summary (high ma n)\<close> empty_Collect_eq mint_corr_help_empty not_None_eq set_vebt'_def)
        hence "\<exists> z . both_member_options (treeList ! summin) z"
          by (metis "4.hyps"(1) "4.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        moreover have "invar_vebt (treeList ! summin) n"
          by (metis "4"(4) "4.IH"(1) "4.hyps"(1) \<open>Some summin = vebt_mint summary\<close> member_bound mint_member nth_mem)
        ultimately obtain lx where "Some lx = vebt_mint (treeList ! summin)" 
          by (metis empty_Collect_eq mint_corr_help_empty not_None_eq set_vebt'_def valid_member_both_member_options)
        let ?xn = "summin*2^n + lx" 
        have "?xn =  (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x)" 
          by (metis False \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>Some summin = vebt_mint summary\<close> \<open>deg div 2 = n\<close> option.sel)
        have "vebt_member (treeList ! summin) lx"  
          using \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>invar_vebt (treeList ! summin) n\<close> mint_member by auto
        moreover have "summin < 2^m" 
          by (metis "4.hyps"(1) \<open>Some summin = vebt_mint summary\<close> member_bound mint_member)
        ultimately have xnin: "both_member_options (Node (Some (mi, ma)) deg treeList summary) ?xn"
          by (metis "4.hyps"(2) Suc_1 \<open>deg div 2 = n\<close> \<open>invar_vebt (treeList ! summin) n\<close> add_leD1 both_member_options_equiv_member both_member_options_from_chilf_to_complete_tree dp high_inv low_inv member_bound plus_1_eq_Suc)
        let ?h ="high ?xn n"
        let ?l = "low ?xn n"
        have "?xn < 2^deg"
          by (smt (verit, ccfv_SIG) "4.hyps"(1) "4.hyps"(4) div_eq_0_iff \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>Some summin = vebt_mint summary\<close> \<open>invar_vebt (treeList ! summin) n\<close> div_exp_eq high_def high_inv le_0_eq member_bound mint_member not_numeral_le_zero power_not_zero)
        hence "?h < length treeList" 
          using "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) \<open>invar_vebt (treeList ! summin) n\<close> deg_not_0 exp_split_high_low(1) by metis
        let ?newnode = "vebt_delete (treeList ! ?h) ?l" 
        let ?newlist = "treeList[?h:= ?newnode]"
        have "length treeList = length ?newlist" by simp
        hence hprolist: "?newlist ! ?h = ?newnode"
          by (meson \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> nth_list_update)
        have nothprolist: "i \<noteq> ?h \<and> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by simp
        have firstsimp: "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = (take ?h treeList @ [ newnode]@drop (?h+1) treeList)in
                             if minNull newnode 
                             then(   
                                let sn = vebt_delete summary ?h in
                               (Node (Some (?xn, if ?xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then ?xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (?xn, (if ?xn = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (newlist ! ?h))
                                                            else ma)))
                                 deg newlist summary ))" 
          using del_x_mi[of x mi ma deg ?xn ?h summary treeList ?l] 
          by (smt (z3) \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> \<open>x = mi\<close> add.commute append_Cons append_Nil dp mimapr nat_less_le plus_1_eq_Suc upd_conv_take_nth_drop)
        have minxnrel: "?xn \<noteq> mi" 
          by (metis "4.hyps"(2) "4.hyps"(9) \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> both_member_options_equiv_member high_inv less_not_refl low_inv member_bound mimapr)
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          let ?sn = "vebt_delete summary ?h"
          let ?newma= "(if ?xn= ma then (let maxs = vebt_maxt ?sn in 
                                                                      (if maxs = None 
                                                                         then ?xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist ?sn)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_mi_lets_in_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist ?sn] False True \<open>deg div 2 = n\<close> \<open>?h < length treeList\<close> \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> dp less_not_refl3 mimapr by fastforce
          moreover have "both_member_options (?delsimp) y \<Longrightarrow> (x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)"
          proof-
            assume "both_member_options (?delsimp) y"
            hence "y = ?xn \<or> y = ?newma \<or> 
                (both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist)" 
              using both_member_options_from_complete_tree_to_child[of deg mi ?newma ?newlist ?sn y] dp 
              by (smt (z3) Suc_1 Suc_le_D both_member_options_def membermima.simps(4) naive_member.simps(3))
            moreover have "y = ?xn \<Longrightarrow> ?thesis" 
              by (metis "4.hyps"(9) False \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> \<open>invar_vebt (treeList ! summin) n\<close> both_member_options_equiv_member high_inv less_not_refl low_inv member_bound mimapr xnin)
            moreover have "y = ?newma \<Longrightarrow> ?thesis"
            proof-
              assume asmt: "y = ?newma"
              show ?thesis
              proof(cases "?xn =  ma")
                case True
                let ?maxs = "vebt_maxt ?sn"
                have newmaext:"?newma = (if ?maxs = None then ?xn
                                else 2 ^ (deg div 2) * the ?maxs +   the (vebt_maxt
                  ( ?newlist ! the ?maxs)))"   using True by force
                then show ?thesis 
                proof(cases "?maxs = None ")
                  case True
                  hence aa:"?newma = ?xn" using newmaext by auto
                  hence bb: "?newma \<noteq> x" 
                    using False minxnrel by presburger
                  hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) ?xn"
                    using xnin newmaext minxnrel asmt by simp
                  moreover have "?xn = y" using aa asmt by simp
                  ultimately have "both_member_options (Node (Some (mi, ma)) deg treeList summary) y" by simp
                  then show ?thesis using bb
                    using \<open>summin * 2 ^ n + lx = y\<close> \<open>y = ?xn \<Longrightarrow> x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y\<close> by blast
                next
                  case False
                  then obtain maxs where "Some maxs = ?maxs" by force
                  hence "both_member_options ?sn maxs" 
                    by (simp add: maxbmo)
                  hence "both_member_options summary maxs \<and> maxs \<noteq> ?h"
                    using "4.IH"(2) by blast
                  hence "?newlist ! the ?maxs = treeList ! maxs"
                    by (metis "4.hyps"(1) \<open>Some maxs = vebt_maxt (vebt_delete summary (high (summin * 2 ^ n + lx) n))\<close> option.sel member_bound nothprolist valid_member_both_member_options)
                  have "maxs < 2^m"
                    using "4.hyps"(1) \<open>both_member_options summary maxs \<and> maxs \<noteq> high (summin * 2 ^ n + lx) n\<close> member_bound valid_member_both_member_options by blast
                  hence "the (vebt_maxt  (?newlist ! the ?maxs)) = the (vebt_maxt (treeList ! maxs))" 
                    using \<open>?newlist ! the (vebt_maxt ?sn) = treeList ! maxs\<close> by presburger
                  have "\<exists> z. both_member_options(treeList ! maxs) z" 
                    using "4.hyps"(5) \<open>both_member_options summary maxs \<and> maxs \<noteq>?h\<close> \<open>maxs < 2 ^ m\<close> by blast
                  moreover have "invar_vebt (treeList ! maxs) n" using 4 
                    by (metis \<open>maxs < 2 ^ m\<close> inthall member_def)
                  ultimately obtain maxi where "Some maxi  = (vebt_maxt (treeList ! maxs))" 
                    by (metis empty_Collect_eq maxt_corr_help_empty not_None_eq set_vebt'_def valid_member_both_member_options)
                  hence "maxi < 2^n" 
                    by (metis \<open>invar_vebt (treeList ! maxs) n\<close> maxt_member member_bound)
                  hence "both_member_options (treeList ! maxs) maxi" 
                    using \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> maxbmo by presburger
                  hence "2 ^ (deg div 2) * the ?maxs +  the
                   (vebt_maxt (?newlist !  the ?maxs)) = 2^n * maxs + maxi "
                    by (metis \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> \<open>Some maxs = vebt_maxt ?sn\<close> \<open>deg div 2 = n\<close> \<open>the (vebt_maxt (?newlist ! the (vebt_maxt ?sn))) = the (vebt_maxt (treeList ! maxs))\<close> option.sel)
                  hence "?newma =  2^n * maxs + maxi" 
                    using False True by auto
                  hence "y =   2^n * maxs + maxi" using asmt by simp 
                  hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
                    by (metis "4.hyps"(2) Suc_1 \<open>both_member_options (treeList ! maxs) maxi\<close> \<open>deg div 2 = n\<close> \<open>maxi < 2 ^ n\<close> \<open>maxs < 2 ^ m\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp high_inv low_inv mult.commute plus_1_eq_Suc) 
                  moreover hence "y \<noteq> x" 
                    by (metis "4.hyps"(9) True \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> \<open>maxi < 2 ^ n\<close> \<open>maxs < 2 ^ m\<close> \<open>x = mi\<close> \<open>y = 2 ^ n * maxs + maxi\<close> high_inv less_not_refl low_inv maxbmo minxnrel mult.commute)
                  ultimately show ?thesis by force
                qed
              next
                case False
                hence "?newma = ma" by simp
                moreover hence "mi \<noteq> ma" 
                  using mimapr by blast
                moreover hence "y \<noteq> x"  
                  using False \<open>y = ?newma\<close> \<open>x = mi\<close> by auto
                then show ?thesis 
                  by (metis False \<open>y =?newma\<close> both_member_options_equiv_member vebt_maxt.simps(3) maxt_member tvalid)
              qed
            qed
            moreover have "(both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist) \<Longrightarrow> ?thesis"
            proof-
              assume assm:"both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist"
              show ?thesis
              proof(cases "(high  y (deg div 2)) = ?h")
                case True
                hence 000:"both_member_options ?newnode (low y (deg div 2)) " using hprolist   by (metis assm) 
                hence 001:"invar_vebt (treeList ! (high y (deg div 2))) n" 
                  using True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
                then show ?thesis
                proof(cases "low y n = ?l")
                  case True
                  hence "y = ?xn" 
                    by (metis "000" "4.IH"(1) \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> inthall member_def)
                  then show ?thesis
                    using calculation(2) by blast
                next
                  case False 
                  hence "both_member_options (treeList ! ?h) (low y (deg div 2)) \<and> (low y (deg div 2)) \<noteq> (low ?xn (deg div 2))"
                    using  "4.IH"(1) \<open>deg div 2 = n\<close> \<open>high ?xn n < length treeList\<close> inthall member_def 
                    by (metis "000")
                  then show ?thesis 
                    by (metis "4.hyps"(2) "4.hyps"(9) Suc_1 Suc_leD True \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> \<open>x = mi\<close> assm both_member_options_from_chilf_to_complete_tree dp less_not_refl mimapr)
                qed
              next
                case False
                hence "x \<noteq> y" 
                  by (metis "4.hyps"(2) "4.hyps"(9) \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> \<open>x = mi\<close> assm less_not_refl mimapr nothprolist)
                moreover hence "(?newlist ! (high  y (deg div 2))) = treeList ! (high y (deg div 2))" using nothprolist 
                  using "4.hyps"(2) False \<open>length treeList = length ?newlist\<close> assm by presburger
                moreover hence "both_member_options (treeList ! (high y (deg div 2)) ) (low y (deg div 2))" 
                  using assm by presburger
                moreover hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y" 
                  by (metis One_nat_def Suc_leD \<open>length treeList = length ?newlist\<close> assm both_member_options_from_chilf_to_complete_tree dp numeral_2_eq_2) 
                ultimately show ?thesis by blast
              qed
            qed
            ultimately show ?thesis by fastforce
          qed
          moreover have "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)\<Longrightarrow>
                                both_member_options ?delsimp y"
          proof-
            assume assm: "x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            hence abcv:"y = mi \<or> y = ma \<or> ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))" 
              by (metis Suc_1 \<open>deg div 2 = n\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            thus " both_member_options ?delsimp y"
            proof-
              have "y = mi \<Longrightarrow> ?thesis" 
                using False assm by force
              moreover have " y = ma \<Longrightarrow> ?thesis" 
                by (smt (z3) Suc_le_D both_member_options_def dp membermima.simps(4) nat_1_add_1 plus_1_eq_Suc)
              moreover have " both_member_options (treeList ! (high y n)) (low y n) \<Longrightarrow> ?thesis"
              proof-
                assume myass: "both_member_options (treeList ! (high y n)) (low y n) "
                thus ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "high y n = ?h" by simp
                  then show ?thesis 
                  proof(cases "low y n = ?l")
                    case True
                    hence "y = ?xn" 
                      by (metis \<open>high y n = high (summin * 2 ^ n + lx) n\<close> bit_split_inv)
                    then show ?thesis 
                      by (metis Suc_le_D both_member_options_def dp membermima.simps(4) nat_1_add_1 plus_1_eq_Suc)
                  next
                    case False
                    hence "low y n \<noteq> ?l" 
                      by (metis assm bit_split_inv)
                    hence pp:"?newlist ! ?h = ?newnode" 
                      using hprolist by blast
                    hence "invar_vebt (treeList ! ?h) n"
                      using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
                    hence "both_member_options ?newnode (low y n)" 
                      using "4.IH"(1) False True \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> myass by auto
                    then show ?thesis  
                      by (metis True \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>length treeList = length ?newlist\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp nat_1_add_1 pp)
                  qed
                next
                  case False
                  hence pp:"?newlist ! (high y n) = treeList ! (high y n)" using nothprolist abcv
                    by (metis "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) assm deg_not_0 exp_split_high_low(1) member_bound tvalid valid_member_both_member_options)          
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> abcv both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) dp numerals(2))
                qed
              qed 
              then show ?thesis 
                using abcv calculation(1) calculation(2) by fastforce
            qed
          qed
          ultimately show ?thesis by metis
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if ?xn = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist summary)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = ?delsimp" 
            using del_x_mi_lets_in_not_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist] 
            by (metis "4.hyps"(3) "4.hyps"(4) False \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>Some summin = vebt_mint summary\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>x = mi\<close> add_self_div_2 dp option.sel less_not_refl mimapr)
          moreover have "both_member_options ?delsimp y 
                      \<Longrightarrow> x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
          proof-
            assume ssms: "both_member_options ?delsimp y "
            hence aaaa: "y = ?xn \<or> y = ?newma \<or> (both_member_options (?newlist ! (high y n)) (low y n) \<and> high y n < length ?newlist)"
              by (smt (z3) Suc_1 Suc_le_D \<open>deg div 2 = n\<close> both_member_options_def dp membermima.simps(4) naive_member.simps(3))
            show " x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            proof-
              have "y = ?xn \<Longrightarrow>?thesis"
                using \<open>x = mi\<close> minxnrel xnin by blast
              moreover have " y = ?newma \<Longrightarrow> ?thesis"
              proof-
                assume "y = ?newma"
                show ?thesis
                proof(cases "?xn = ma")
                  case True
                  hence aaa:"?newma =?h * 2 ^ (deg div 2) +the(vebt_maxt(?newlist ! ?h))" 
                    by metis
                  have "?newlist ! ?h = ?newnode"   using hprolist by blast
                  obtain maxi where maxidef:"Some maxi = vebt_maxt(?newlist ! ?h)"
                    by (metis False hprolist vebt_maxt.elims minNull.simps(1) minNull.simps(4))
                  have aa:"invar_vebt (treeList ! ?h) n" 
                    by (metis "4.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                  moreover hence ab:"maxi \<noteq> ?l \<and> both_member_options ?newnode maxi" 
                    by (metis "4.IH"(1) \<open>high ?xn n < length treeList\<close> hprolist inthall maxbmo maxidef member_def)
                  ultimately have ac:"maxi \<noteq> ?l \<and> both_member_options (treeList ! ?h)  maxi" 
                    by (metis "4.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                  hence ad:"maxi < 2^n" 
                    by (meson aa member_bound valid_member_both_member_options)
                  then show ?thesis using  Suc_1 aaa \<open>y = ?newma\<close> ac add_leD1 
                    by (metis "4.hyps"(2) "4.hyps"(9) Suc_leD \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>x = mi\<close> both_member_options_from_chilf_to_complete_tree dp option.sel high_inv less_not_refl low_inv maxidef mimapr) 
                next
                  case False
                  then show ?thesis 
                    by (metis \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>x = mi\<close> \<open>y = ?newma\<close> both_member_options_equiv_member leD vebt_maxt.simps(3) maxt_member mimapr tvalid)
                qed
              qed
              moreover have "(both_member_options (?newlist ! (high y n)) (low y n)\<and> high y n < length ?newlist) \<Longrightarrow> ?thesis"
              proof-
                assume assmy:"(both_member_options (?newlist ! (high y n)) (low y n)\<and> high y n < length ?newlist)"
                then show ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "?newlist ! (high y n) = ?newnode" 
                    using hprolist by presburger
                  have "invar_vebt (treeList ! ?h) n"
                    by (metis "4.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                  then show ?thesis
                  proof(cases "low y n= ?l")
                    case True
                    hence "y = ?xn"
                      using "4.IH"(1) \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! high y n = vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)\<close> assmy by force
                    then show ?thesis 
                      using calculation(1) by blast
                  next
                    case False 
                    hence "low y n \<noteq> ?l \<and> both_member_options (treeList ! ?h ) (low y n)" using assmy 
                      by (metis "4.IH"(1) "4.hyps"(2) \<open>?newlist ! high y n = vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> high_inv inthall member_bound member_def)
                    then show ?thesis 
                      by (metis "4.hyps"(2) "4.hyps"(9) Suc_1 Suc_leD True \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>x = mi\<close> both_member_options_from_chilf_to_complete_tree dp leD mimapr)
                  qed
                next
                  case False
                  hence "?newlist ! (high y n) = treeList !(high y n)" 
                    by (smt (z3) "4.hyps"(1) "4.hyps"(2) "4.hyps"(3) "4.hyps"(4) "4.hyps"(8) \<open>length treeList = length ?newlist\<close> \<open>ma \<le> 2 ^ deg\<close> aaaa calculation(2) deg_not_0 exp_split_high_low(1) less_le_trans member_inv mimapr nothprolist tvalid valid_member_both_member_options)
                  hence "both_member_options (treeList !(high y n)) (low y n)" 
                    using assmy by presburger 
                  moreover have "x \<noteq> y" 
                    by (metis "4.hyps"(1) "4.hyps"(4) "4.hyps"(9) \<open>invar_vebt (treeList ! summin) n\<close> \<open>x < 2 ^ deg\<close> \<open>x = mi\<close> calculation deg_not_0 exp_split_high_low(1) mimapr not_less_iff_gr_or_eq)
                  moreover have "high y n < length ?newlist"  using assmy by blast
                  moreover hence "high y n < length treeList" 
                    using \<open>length treeList = length ?newlist\<close> by presburger
                  ultimately show ?thesis 
                    by (metis One_nat_def Suc_leD \<open>deg div 2 = n\<close> both_member_options_from_chilf_to_complete_tree dp numerals(2))
                qed
              qed
              ultimately show ?thesis 
                using aaaa by fastforce
            qed
          qed

          moreover have "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)\<Longrightarrow>
                                both_member_options ?delsimp y"
          proof-
            assume assm: "x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            hence abcv:"y = mi \<or> y = ma \<or> ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))" 
              by (metis Suc_1 \<open>deg div 2 = n\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            thus " both_member_options ?delsimp y"
            proof-
              have "y = mi \<Longrightarrow> ?thesis" 
                using \<open>x = mi\<close> assm by blast
              moreover have " y = ma \<Longrightarrow> ?thesis" 
                by (smt (z3) Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4))
              moreover have " ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))
                                  \<Longrightarrow> ?thesis"
              proof-
                assume myass: "(  high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n)) "
                thus ?thesis
                proof(cases "high y n = ?h")
                  case True
                  then show ?thesis
                  proof(cases "low y n = ?l")
                    case True
                    then show ?thesis
                      by (smt (z3) Suc_1 Suc_le_D \<open>deg div 2 = n\<close> \<open>length treeList = length (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)])\<close> add_leD1 bit_split_inv both_member_options_def both_member_options_from_chilf_to_complete_tree dp membermima.simps(4) myass nth_list_update_neq plus_1_eq_Suc)
                  next
                    case False
                    hence "low y n \<noteq> ?l" by simp
                    hence pp:"?newlist ! ?h = ?newnode" 
                      using hprolist by blast
                    hence "invar_vebt (treeList ! ?h) n"
                      by (metis "4.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                    hence "both_member_options ?newnode (low y n)" 
                      by (metis "4.IH"(1) True \<open>high ?xn n < length treeList\<close> \<open>low y n \<noteq> low ?xn n\<close> in_set_member inthall myass)
                    then show ?thesis 
                      by (metis One_nat_def Suc_leD True \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>length treeList = length ?newlist\<close> both_member_options_from_chilf_to_complete_tree dp numerals(2) pp)
                  qed
                next
                  case False
                  have pp:"?newlist ! (high y n) = treeList ! (high y n)"
                    using nothprolist[of "high y n"] False 
                    by (metis "4.hyps"(1) "4.hyps"(3) "4.hyps"(4) assm deg_not_0 exp_split_high_low(1) member_bound tvalid valid_member_both_member_options)
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> abcv both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) dp numerals(2))
                qed
              qed 
              then show ?thesis 
                using abcv calculation(1) calculation(2) by fastforce
            qed
          qed
          ultimately show ?thesis by metis
        qed
      qed
    qed
  qed
next
  case (5 treeList n summary m deg mi ma)
  hence tvalid: "invar_vebt (Node (Some (mi, ma)) deg treeList summary) deg" 
    using invar_vebt.intros(5)[of treeList n summary m deg mi ma] by simp
  hence "mi \<le> ma" and "deg div 2 = n" and "ma \<le> 2^deg" using 5 
    by  (auto simp add: "5.hyps"(3) "5.hyps"(4))
  hence dp:"deg \<ge> 2" 
    by (meson vebt_maxt.simps(3) maxt_member member_inv tvalid)
  hence nmpr:"n\<ge> 1 \<and> m = Suc n" 
    using "5.hyps"(3) \<open>deg div 2 = n\<close> by linarith
  then show ?case proof(cases "x <mi \<or> x > ma")
    case True
    hence "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (Node (Some (mi, ma)) deg treeList summary)" 
      using delt_out_of_range[of x mi ma deg treeList summary]  \<open>2 \<le> deg\<close> by blast
    then show ?thesis 
      by (metis "5.hyps"(7) True tvalid leD member_inv not_less_iff_gr_or_eq valid_member_both_member_options)
  next
    case False
    hence "mi \<le> x \<and> x \<le> ma" by simp
    hence xdegrel:"x < 2^deg"
      using "5.hyps"(8) order.strict_trans1 by blast
    then show ?thesis 
    proof(cases "x = mi \<and> x = ma")
      case True
      hence "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = (Node None deg treeList summary)"
        using del_single_cont[of x mi ma deg treeList summary] \<open>2 \<le> deg\<close> by blast
      moreover hence "invar_vebt (Node None deg treeList summary) deg" 
        using "5"(4) "5.IH"(1) "5.hyps"(1) "5.hyps"(3) "5.hyps"(4) True mi_eq_ma_no_ch
          tvalid invar_vebt.intros(3) by force
      moreover hence "\<not> vebt_member (Node None deg treeList summary) y" by simp
      moreover hence "\<not>both_member_options (Node None deg treeList summary) y" 
        using calculation(2) valid_member_both_member_options by blast
      then show ?thesis 
        by (metis True calculation(1) member_inv not_less_iff_gr_or_eq tvalid valid_member_both_member_options)
    next
      case False
      hence mimapr:"mi < ma"
        by (metis "5.hyps"(7) \<open>mi \<le> x \<and> x \<le> ma\<close> le_antisym nat_less_le)
      then show ?thesis 
      proof(cases "x \<noteq> mi")
        case True
        hence xmi:"x \<noteq> mi" by simp
        let ?h ="high x n"
        let ?l = "low x n"
        have "?h < length treeList" using xdegrel 5 
          by (metis \<open>deg div 2 = n\<close> deg_not_0 div_greater_zero_iff dp exp_split_high_low(1) zero_less_numeral)
        let ?newnode = "vebt_delete (treeList ! ?h) ?l" 
        let ?newlist = "treeList[?h:=?newnode]"
        have "length treeList = length ?newlist" by simp
        hence hprolist: "?newlist ! ?h = ?newnode"
          by (meson \<open>high x n < length treeList\<close> nth_list_update_eq)
        have nothprolist: "i \<noteq> ?h \<and> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by simp
        then show ?thesis 
        proof(cases "minNull ?newnode")
          case True
          let ?sn = "vebt_delete summary ?h"
          let ?newma= "(if x  = ma then (let maxs = vebt_maxt ?sn in 
                                                                      (if maxs = None 
                                                                         then mi
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)"
          let ?delsimp =" (Node (Some (mi, ?newma))  deg ?newlist ?sn)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_not_mi_new_node_nil[of mi x ma deg ?h ?l ?newnode treeList ?sn summary ?newlist]
            by (metis True \<open>2 \<le> deg\<close> \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>mi < ma\<close> \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>x \<noteq> mi\<close> less_not_refl3 order.not_eq_order_implies_strict)
          moreover have "both_member_options (?delsimp) y \<Longrightarrow> (x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)"
          proof-
            assume "both_member_options (?delsimp) y"
            hence "y = mi \<or> y = ?newma \<or> 
                (both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist)" 
              using both_member_options_from_complete_tree_to_child[of deg mi ?newma ?newlist ?sn y] dp 
              by (smt (z3) Suc_1 Suc_le_D both_member_options_def membermima.simps(4) naive_member.simps(3))
            moreover have "y = mi \<Longrightarrow> ?thesis"
              by (meson \<open>x \<noteq> mi\<close> both_member_options_equiv_member vebt_mint.simps(3) mint_member tvalid)
            moreover have "y = ?newma \<Longrightarrow> ?thesis"
            proof-
              assume "y = ?newma"
              show ?thesis
              proof(cases "x =  ma")
                case True
                let ?maxs = "vebt_maxt ?sn"
                have newmapropy:"?newma = (if ?maxs = None then mi
                                else 2 ^ (deg div 2) * the ?maxs +   the (vebt_maxt
                   (?newlist !
                    the ?maxs)))"   using True by force
                then show ?thesis 
                proof(cases "?maxs = None ")
                  case True
                  then show ?thesis 
                    using \<open>y = (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma)\<close> calculation(2) newmapropy by presburger
                next
                  case False
                  then obtain maxs where "Some maxs = ?maxs" by force
                  hence "both_member_options ?sn maxs" 
                    by (simp add: maxbmo)
                  hence "both_member_options summary maxs \<and> maxs \<noteq> ?h"
                    using "5.IH"(2) by blast
                  hence "?newlist ! the ?maxs = treeList ! maxs" 
                    by (metis "5.hyps"(1) \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> option.sel member_bound nothprolist valid_member_both_member_options)
                  have "maxs < 2^m" 
                    using "5.hyps"(1) \<open>both_member_options summary maxs \<and> maxs \<noteq> high x n\<close> member_bound valid_member_both_member_options by blast
                  hence "the (vebt_maxt  (?newlist ! the ?maxs)) = the (vebt_maxt (treeList ! maxs))" 
                    by (metis \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>both_member_options summary maxs \<and> maxs \<noteq> high x n\<close> option.sel nth_list_update_neq)
                  have "\<exists> z. both_member_options(treeList ! maxs) z" 
                    by (simp add: "5.hyps"(5) \<open>both_member_options summary maxs \<and> maxs \<noteq> high x n\<close> \<open>maxs < 2 ^ m\<close>)
                  moreover have "invar_vebt (treeList ! maxs) n" using 5 
                    by (metis \<open>maxs < 2 ^ m\<close> inthall member_def)
                  ultimately obtain maxi where "Some maxi  = (vebt_maxt (treeList ! maxs))" 
                    by (metis empty_Collect_eq maxt_corr_help_empty not_None_eq set_vebt'_def valid_member_both_member_options)
                  hence "maxi < 2^n" 
                    by (metis \<open>invar_vebt (treeList ! maxs) n\<close> maxt_member member_bound)
                  hence "both_member_options (treeList ! maxs) maxi" 
                    using \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> maxbmo by presburger
                  hence "2 ^ (deg div 2) * the ?maxs +  the
                   (vebt_maxt (?newlist !  the ?maxs)) = 2^n * maxs + maxi "
                    by (metis \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> \<open>Some maxs = vebt_maxt (vebt_delete summary (high x n))\<close> \<open>deg div 2 = n\<close> \<open>the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! the (vebt_maxt (vebt_delete summary (high x n))))) = the (vebt_maxt (treeList ! maxs))\<close> option.sel)
                  hence "y =  2^n * maxs + maxi" 
                    using False \<open>y = (if x = ma then let maxs = vebt_maxt (vebt_delete summary (high x n)) in if maxs = None then mi else 2 ^ (deg div 2) * the maxs + the (vebt_maxt (treeList [high x n := vebt_delete (treeList ! high x n) (low x n)] ! the maxs)) else ma)\<close> newmapropy by presburger
                  hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
                    by (metis "5.hyps"(2) Suc_1 \<open>both_member_options (treeList ! maxs) maxi\<close> \<open>deg div 2 = n\<close> \<open>maxi < 2 ^ n\<close> \<open>maxs < 2 ^ m\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp high_inv low_inv mult.commute plus_1_eq_Suc) 
                  moreover hence "y \<noteq> x" 
                    by (metis \<open>both_member_options summary maxs \<and> maxs \<noteq> high x n\<close> \<open>maxi < 2 ^ n\<close> \<open>y = 2 ^ n * maxs + maxi\<close> high_inv mult.commute)
                  ultimately show ?thesis by force
                qed
              next
                case False
                hence "?newma = ma" by simp
                moreover hence "y \<noteq> x" 
                  using False \<open>y = ?newma\<close> by presburger
                then show ?thesis 
                  by (metis False \<open>y =?newma\<close> both_member_options_equiv_member vebt_maxt.simps(3) maxt_member tvalid)
              qed
            qed
            moreover have "(both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist) \<Longrightarrow> ?thesis"
            proof-
              assume assm:"both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist"
              show ?thesis
              proof(cases "(high  y (deg div 2)) = ?h")
                case True
                hence "both_member_options ?newnode (low y (deg div 2)) " using hprolist   by (metis assm) 
                moreover hence "invar_vebt (treeList ! (high y (deg div 2))) n" 
                  by (metis "5.IH"(1) True \<open>high x n < length treeList\<close> inthall member_def)
                ultimately have "both_member_options (treeList ! ?h) (low y (deg div 2)) \<and> (low y (deg div 2)) \<noteq> (low x (deg div 2))"
                  by (metis "5.IH"(1) \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> inthall member_def)
                then show ?thesis 
                  by (metis Suc_1 True \<open>high x n < length treeList\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp plus_1_eq_Suc)
              next
                case False
                hence "x \<noteq> y"  
                  using \<open>deg div 2 = n\<close> by blast
                moreover hence "(?newlist ! (high  y (deg div 2))) = treeList ! (high y (deg div 2))" using nothprolist 
                  using "5.hyps"(2) False \<open>length treeList = length ?newlist\<close> assm by presburger
                moreover hence "both_member_options (treeList ! (high y (deg div 2)) ) (low y (deg div 2))" 
                  using assm by presburger
                moreover hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y" 
                  by (metis One_nat_def Suc_leD \<open>length treeList = length ?newlist\<close> assm both_member_options_from_chilf_to_complete_tree dp numeral_2_eq_2) 
                ultimately show ?thesis by blast
              qed
            qed
            ultimately show ?thesis by fastforce
          qed
          moreover have " (x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y) \<Longrightarrow> both_member_options (?delsimp) y"
          proof-
            assume "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)"
            hence aa:"x \<noteq> y" and bb:"y = mi \<or> y = ma \<or> (both_member_options (treeList ! (high y n)) (low y n) \<and> high y n < length treeList)" 
              apply auto[1]  by (metis Suc_1 \<open>deg div 2 = n\<close> \<open>x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            show "both_member_options (?delsimp) y"
            proof-
              have "y = mi \<Longrightarrow>both_member_options (?delsimp) y"
                by (metis Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4))
              moreover have "y = ma \<Longrightarrow> both_member_options (?delsimp) y"
                using aa maxbmo vebt_maxt.simps(3) by presburger
              moreover have "both_member_options (treeList ! (high y n)) (low y n) \<Longrightarrow>both_member_options (?delsimp) y "
              proof-
                assume assmy: "both_member_options (treeList ! (high y n)) (low y n)" 
                then show "both_member_options (?delsimp) y "
                proof(cases "high y n = ?h")
                  case True
                  moreover hence "?newlist ! (high y n) = ?newnode" 
                    using hprolist by auto
                  hence 0:"invar_vebt (treeList !(high y n)) n" using 5 
                    by (metis True \<open>high x n < length treeList\<close> inthall member_def)
                  moreover have 1:"low y n \<noteq> low x n" 
                    by (metis True aa bit_split_inv)
                  moreover have 11:" (treeList !(high y n)) \<in> set treeList"
                    by (metis True \<open>high x n < length treeList\<close> inthall member_def)
                  ultimately have "  (\<forall> xa. both_member_options ?newnode xa = 
                         ((low x n) \<noteq> xa \<and> both_member_options (treeList ! ?h) xa))"
                    by (simp add: "5.IH"(1)) 
                  hence "((low x n) \<noteq> xa \<and> both_member_options (treeList ! ?h) xa) \<Longrightarrow>  both_member_options ?newnode xa" for xa  by blast
                  moreover have "((low x n) \<noteq> (low y n) \<and> both_member_options (treeList ! ?h) (low y n))" using 1 
                    using True assmy by presburger
                  ultimately have "both_member_options ?newnode (low y n)" by blast
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD True \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>length treeList = length ?newlist\<close> both_member_options_from_chilf_to_complete_tree dp hprolist numerals(2))
                next
                  case False
                  hence "?newlist ! (high y n) = treeList ! (high y n)" by auto
                  hence "both_member_options (?newlist !(high y n)) (low y n)" 
                    using assmy by presburger
                  then show ?thesis 
                    by (smt (z3) Suc_1 Suc_le_D \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> aa add_leD1 bb both_member_options_def both_member_options_from_chilf_to_complete_tree dp membermima.simps(4) plus_1_eq_Suc)
                qed
              qed
              ultimately show ?thesis using bb by fastforce
            qed
          qed
          ultimately show ?thesis by metis
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if x = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (mi, ?newma))  deg ?newlist summary)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = ?delsimp"
            using del_x_not_mi_newnode_not_nil[of mi x ma deg ?h ?l ?newnode treeList ?newlist summary] False xmi mimapr 
            using \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>mi \<le> x \<and> x \<le> ma\<close> dp nat_less_le plus_1_eq_Suc by fastforce
          moreover have "both_member_options ?delsimp y 
                      \<Longrightarrow> x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
          proof-
            assume ssms: "both_member_options ?delsimp y "
            hence aaaa: "y = mi \<or> y = ?newma \<or> (both_member_options (?newlist ! (high y n)) (low y n) \<and> high y n < length ?newlist)"
              by (smt (z3) Suc_1 Suc_le_D \<open>deg div 2 = n\<close> both_member_options_def dp membermima.simps(4) naive_member.simps(3))
            show " x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            proof-
              have "y = mi \<Longrightarrow>?thesis"
                by (metis Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4) xmi)
              moreover have " y = ?newma \<Longrightarrow> ?thesis"
              proof-
                assume "y = ?newma"
                show ?thesis
                proof(cases "x = ma")
                  case True
                  hence "?newma =?h * 2 ^ (deg div 2) +the(vebt_maxt(?newlist ! ?h))" 
                    by metis
                  have "?newlist ! ?h = ?newnode"   using hprolist by blast
                  obtain maxi where maxidef:"Some maxi = vebt_maxt(?newlist ! ?h)"
                    by (metis False hprolist vebt_maxt.elims minNull.simps(1) minNull.simps(4))
                  have aa:"invar_vebt (treeList ! ?h) n" 
                    by (metis "5.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  moreover hence ab:"maxi \<noteq> ?l \<and> both_member_options ?newnode maxi" 
                    by (metis "5.IH"(1) \<open>high x n < length treeList\<close> hprolist inthall maxbmo maxidef member_def)
                  ultimately have ac:"maxi \<noteq> ?l \<and> both_member_options (treeList ! ?h)  maxi" 
                    by (metis "5.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  hence ad:"maxi < 2^n" 
                    using \<open>invar_vebt (treeList ! high x n) n\<close> member_bound valid_member_both_member_options by blast
                  then show ?thesis
                    by (metis Suc_1 \<open>(if x = ma then high x n * 2 ^ (deg div 2) + the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! high x n)) else ma) = high x n * 2 ^ (deg div 2) + the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! high x n))\<close> \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>y = (if x = ma then high x n * 2 ^ (deg div 2) + the (vebt_maxt (treeList[high x n := vebt_delete (treeList ! high x n) (low x n)] ! high x n)) else ma)\<close> ac add_leD1 both_member_options_from_chilf_to_complete_tree dp option.sel high_inv low_inv maxidef plus_1_eq_Suc)
                next
                  case False
                  then show ?thesis
                    by (simp add: \<open>y = ?newma\<close> maxbmo)
                qed
              qed
              moreover have "both_member_options (?newlist ! (high y n)) (low y n) \<Longrightarrow> ?thesis"
              proof-
                assume assmy:"both_member_options (?newlist ! (high y n)) (low y n)"
                then show ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "?newlist ! (high y n) = ?newnode" 
                    using hprolist by presburger
                  have "invar_vebt (treeList ! ?h) n"
                    by (metis "5.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  hence "low y n \<noteq> ?l \<and> both_member_options (treeList ! ?h ) (low y n)" 
                    by (metis "5.IH"(1) True \<open>high x n < length treeList\<close> assmy hprolist inthall member_def)
                  then show ?thesis 
                    by (metis Suc_1 True \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp plus_1_eq_Suc)
                next
                  case False
                  hence "?newlist ! (high y n) = treeList !(high y n)" by auto
                  then show ?thesis 
                    by (metis False Suc_1 \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> aaaa add_leD1 both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) dp plus_1_eq_Suc)
                qed
              qed 
              ultimately show ?thesis 
                using aaaa by fastforce
            qed
          qed
          moreover have "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)\<Longrightarrow>
                                both_member_options ?delsimp y"
          proof-
            assume assm: "x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            hence abcv:"y = mi \<or> y = ma \<or> ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))" 
              by (metis Suc_1 \<open>deg div 2 = n\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            thus " both_member_options ?delsimp y"
            proof-
              have "y = mi \<Longrightarrow> ?thesis"
                by (metis Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4))
              moreover have " y = ma \<Longrightarrow> ?thesis" 
                using assm maxbmo vebt_maxt.simps(3) by presburger
              moreover have " both_member_options (treeList ! (high y n)) (low y n) \<Longrightarrow> ?thesis"
              proof-
                assume myass: "both_member_options (treeList ! (high y n)) (low y n) "
                thus ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "low y n \<noteq> ?l" 
                    by (metis assm bit_split_inv)
                  hence pp:"?newlist ! ?h = ?newnode" 
                    using hprolist by blast
                  hence "invar_vebt (treeList ! ?h) n"
                    by (metis "5.IH"(1) \<open>high x n < length treeList\<close> inthall member_def)
                  hence "both_member_options ?newnode (low y n)" 
                    by (metis "5.IH"(1) True \<open>high x n < length treeList\<close> \<open>low y n \<noteq> low x n\<close> in_set_member inthall myass)
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD True \<open>deg div 2 = n\<close> \<open>high x n < length treeList\<close> \<open>length treeList = length ?newlist\<close> both_member_options_from_chilf_to_complete_tree dp numerals(2) pp)
                next
                  case False
                  hence pp:"?newlist ! (high y n) = treeList ! (high y n)" using nothprolist abcv by auto
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> abcv both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) dp numerals(2))
                qed
              qed 
              then show ?thesis 
                using abcv calculation(1) calculation(2) by fastforce
            qed
          qed
          ultimately show ?thesis by metis
        qed
      next
        case False
        hence "x = mi" by simp
        have "both_member_options summary (high ma n)" 
          by (metis "5"(10) "5"(11) "5"(7) "5.hyps"(4) div_eq_0_iff Suc_leI Suc_le_D div_exp_eq dual_order.irrefl high_def mimapr nat.simps(3))
        hence "vebt_member summary (high ma n)" 
          using "5.hyps"(1) valid_member_both_member_options by blast
        obtain summin where "Some summin = vebt_mint summary" 
          by (metis "5.hyps"(1) \<open>vebt_member summary (high ma n)\<close> empty_Collect_eq mint_corr_help_empty not_None_eq set_vebt'_def)
        hence "\<exists> z . both_member_options (treeList ! summin) z"
          by (metis "5.hyps"(1) "5.hyps"(5) both_member_options_equiv_member member_bound mint_member)
        moreover have "invar_vebt (treeList ! summin) n" 
          by (metis "5.IH"(1) "5.hyps"(1) "5.hyps"(2) \<open>Some summin = vebt_mint summary\<close> member_bound mint_member nth_mem)
        ultimately obtain lx where "Some lx = vebt_mint (treeList ! summin)" 
          by (metis empty_Collect_eq mint_corr_help_empty not_None_eq set_vebt'_def valid_member_both_member_options)
        let ?xn = "summin*2^n + lx" 
        have "?xn =  (if x = mi 
                             then the (vebt_mint summary) * 2^(deg div 2) 
                                      + the (vebt_mint (treeList ! the (vebt_mint summary))) 
                             else x)" 
          by (metis False \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>Some summin = vebt_mint summary\<close> \<open>deg div 2 = n\<close> option.sel)
        have "vebt_member (treeList ! summin) lx"  
          using \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>invar_vebt (treeList ! summin) n\<close> mint_member by auto
        moreover have "summin < 2^m" 
          by (metis "5.hyps"(1) \<open>Some summin = vebt_mint summary\<close> member_bound mint_member)
        ultimately have xnin: "both_member_options (Node (Some (mi, ma)) deg treeList summary) ?xn"
          by (metis "5.hyps"(2) Suc_1 \<open>deg div 2 = n\<close> \<open>invar_vebt (treeList ! summin) n\<close> add_leD1 both_member_options_equiv_member both_member_options_from_chilf_to_complete_tree dp high_inv low_inv member_bound plus_1_eq_Suc)
        let ?h ="high ?xn n"
        let ?l = "low ?xn n"
        have "?xn < 2^deg"
          by (smt (verit, ccfv_SIG) "5.hyps"(1) "5.hyps"(4) div_eq_0_iff \<open>Some lx = vebt_mint (treeList ! summin)\<close> \<open>Some summin = vebt_mint summary\<close> \<open>invar_vebt (treeList ! summin) n\<close> div_exp_eq high_def high_inv le_0_eq member_bound mint_member not_numeral_le_zero power_not_zero)
        hence "?h < length treeList"
          using "5.hyps"(2) \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
        let ?newnode = "vebt_delete (treeList ! ?h) ?l" 
        let ?newlist = "treeList[?h:= ?newnode]"
        have "length treeList = length ?newlist" by simp
        hence hprolist: "?newlist ! ?h = ?newnode" 
          by (meson \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> nth_list_update)
        have nothprolist: "i \<noteq> ?h \<and> i < 2^m \<Longrightarrow> ?newlist ! i = treeList ! i" for i by simp
        have firstsimp: "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =(
                          let newnode = vebt_delete (treeList ! ?h) ?l;
                              newlist = treeList[?h:= ?newnode] in
                             if minNull newnode 
                             then(   
                                let sn = vebt_delete summary ?h in
                               (Node (Some (?xn, if ?xn  = ma then (let maxs = vebt_maxt sn in 
                                                                      (if maxs = None 
                                                                         then ?xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)) 
                                      deg newlist sn)
                             )else 
                               (Node (Some (?xn, (if ?xn = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (newlist ! ?h))
                                                            else ma)))
                                 deg newlist summary ))" 
          using del_x_mi[of x mi ma deg ?xn ?h summary treeList ?l] 
            \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> 
            \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) +
              the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> \<open>x = mi\<close> dp mimapr nat_less_le by smt
        have minxnrel: "?xn \<noteq> mi" 
          by (metis "5.hyps"(2) "5.hyps"(9) \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> both_member_options_equiv_member high_inv less_not_refl low_inv member_bound mimapr)
        then show ?thesis
        proof(cases "minNull ?newnode")
          case True
          let ?sn = "vebt_delete summary ?h"
          let ?newma= "(if ?xn= ma then (let maxs = vebt_maxt ?sn in 
                                                                      (if maxs = None 
                                                                         then ?xn
                                                                         else 2^(deg div 2) * the maxs 
                                                                               + the (vebt_maxt (?newlist ! the maxs))
                                                                       )
                                                                   )
                                                              else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist ?sn)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x =  ?delsimp"
            using del_x_mi_lets_in_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist ?sn] False True \<open>deg div 2 = n\<close> \<open>?h < length treeList\<close> \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> dp less_not_refl3 mimapr by fastforce
          moreover have "both_member_options (?delsimp) y \<Longrightarrow> (x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)"
          proof-
            assume "both_member_options (?delsimp) y"
            hence "y = ?xn \<or> y = ?newma \<or> 
                (both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist)" 
              using both_member_options_from_complete_tree_to_child[of deg mi ?newma ?newlist ?sn y] dp 
              by (smt (z3) Suc_1 Suc_le_D both_member_options_def membermima.simps(4) naive_member.simps(3))
            moreover have "y = ?xn \<Longrightarrow> ?thesis" 
              by (metis "5.hyps"(9) False \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> \<open>invar_vebt (treeList ! summin) n\<close> both_member_options_equiv_member high_inv less_not_refl low_inv member_bound mimapr xnin)
            moreover have "y = ?newma \<Longrightarrow> ?thesis"
            proof-
              assume asmt: "y = ?newma"
              show ?thesis
              proof(cases "?xn =  ma")
                case True
                let ?maxs = "vebt_maxt ?sn"
                have newmaext:"?newma = (if ?maxs = None then ?xn
                                else 2 ^ (deg div 2) * the ?maxs +   the (vebt_maxt
                  ( ?newlist ! the ?maxs)))"   using True by force
                then show ?thesis 
                proof(cases "?maxs = None ")
                  case True
                  hence aa:"?newma = ?xn" using newmaext by auto
                  hence bb: "?newma \<noteq> x" 
                    using False minxnrel by presburger
                  hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) ?xn"
                    using xnin newmaext minxnrel asmt by simp
                  moreover have "?xn = y" using aa asmt by simp
                  ultimately have "both_member_options (Node (Some (mi, ma)) deg treeList summary) y" by simp
                  then show ?thesis using bb
                    using \<open>summin * 2 ^ n + lx = y\<close> \<open>y = ?xn \<Longrightarrow> x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y\<close> by blast
                next
                  case False
                  then obtain maxs where "Some maxs = ?maxs" by force
                  hence "both_member_options ?sn maxs" 
                    by (simp add: maxbmo)
                  hence "both_member_options summary maxs \<and> maxs \<noteq> ?h"
                    using "5.IH"(2) by blast
                  hence "?newlist ! the ?maxs = treeList ! maxs"
                    by (metis "5.hyps"(1) \<open>Some maxs = vebt_maxt (vebt_delete summary (high (summin * 2 ^ n + lx) n))\<close> option.sel member_bound nothprolist valid_member_both_member_options)
                  have "maxs < 2^m"
                    using "5.hyps"(1) \<open>both_member_options summary maxs \<and> maxs \<noteq> high (summin * 2 ^ n + lx) n\<close> member_bound valid_member_both_member_options by blast
                  hence "the (vebt_maxt  (?newlist ! the ?maxs)) = the (vebt_maxt (treeList ! maxs))" 
                    using \<open>?newlist ! the (vebt_maxt ?sn) = treeList ! maxs\<close> by presburger
                  have "\<exists> z. both_member_options(treeList ! maxs) z" 
                    using "5.hyps"(5) \<open>both_member_options summary maxs \<and> maxs \<noteq>?h\<close> \<open>maxs < 2 ^ m\<close> by blast
                  moreover have "invar_vebt (treeList ! maxs) n" using 5 
                    by (metis \<open>maxs < 2 ^ m\<close> inthall member_def)
                  ultimately obtain maxi where "Some maxi  = (vebt_maxt (treeList ! maxs))" 
                    by (metis empty_Collect_eq maxt_corr_help_empty not_None_eq set_vebt'_def valid_member_both_member_options)
                  hence "maxi < 2^n" 
                    by (metis \<open>invar_vebt (treeList ! maxs) n\<close> maxt_member member_bound)
                  hence "both_member_options (treeList ! maxs) maxi" 
                    using \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> maxbmo by presburger
                  hence "2 ^ (deg div 2) * the ?maxs +  the
                   (vebt_maxt (?newlist !  the ?maxs)) = 2^n * maxs + maxi "
                    by (metis \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> \<open>Some maxs = vebt_maxt ?sn\<close> \<open>deg div 2 = n\<close> \<open>the (vebt_maxt (?newlist ! the (vebt_maxt ?sn))) = the (vebt_maxt (treeList ! maxs))\<close> option.sel)
                  hence "?newma =  2^n * maxs + maxi" 
                    using False True by auto
                  hence "y =   2^n * maxs + maxi" using asmt by simp 
                  hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
                    by (metis "5.hyps"(2) Suc_1 \<open>both_member_options (treeList ! maxs) maxi\<close> \<open>deg div 2 = n\<close> \<open>maxi < 2 ^ n\<close> \<open>maxs < 2 ^ m\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp high_inv low_inv mult.commute plus_1_eq_Suc) 
                  moreover hence "y \<noteq> x" 
                    by (metis "5.hyps"(9) True \<open>Some maxi = vebt_maxt (treeList ! maxs)\<close> \<open>maxi < 2 ^ n\<close> \<open>maxs < 2 ^ m\<close> \<open>x = mi\<close> \<open>y = 2 ^ n * maxs + maxi\<close> high_inv less_not_refl low_inv maxbmo minxnrel mult.commute)
                  ultimately show ?thesis by force
                qed
              next
                case False
                hence "?newma = ma" by simp
                moreover hence "mi \<noteq> ma" 
                  using mimapr by blast
                moreover hence "y \<noteq> x"  
                  using False \<open>y = ?newma\<close> \<open>x = mi\<close> by auto
                then show ?thesis 
                  by (metis False \<open>y =?newma\<close> both_member_options_equiv_member vebt_maxt.simps(3) maxt_member tvalid)
              qed
            qed
            moreover have "(both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist) \<Longrightarrow> ?thesis"
            proof-
              assume assm:"both_member_options (?newlist ! (high  y (deg div 2))) (low y (deg div 2)) \<and> (high y (deg div 2)) < length ?newlist"
              show ?thesis
              proof(cases "(high  y (deg div 2)) = ?h")
                case True
                hence 000:"both_member_options ?newnode (low y (deg div 2)) " using hprolist   by (metis assm) 
                hence 001:"invar_vebt (treeList ! (high y (deg div 2))) n" 
                  using True \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
                then show ?thesis
                proof(cases "low y n = ?l")
                  case True
                  hence "y = ?xn" 
                    by (metis "000" "5.IH"(1) \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> inthall member_def)
                  then show ?thesis
                    using calculation(2) by blast
                next
                  case False 
                  hence "both_member_options (treeList ! ?h) (low y (deg div 2)) \<and> (low y (deg div 2)) \<noteq> (low ?xn (deg div 2))"
                    using  "5.IH"(1) \<open>deg div 2 = n\<close> \<open>high ?xn n < length treeList\<close> inthall member_def 
                    by (metis "000")
                  then show ?thesis 
                    by (metis "5.hyps"(2) "5.hyps"(9) Suc_1 Suc_leD True \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> \<open>x = mi\<close> assm both_member_options_from_chilf_to_complete_tree dp less_not_refl mimapr)
                qed
              next
                case False
                hence "x \<noteq> y" 
                  by (metis "5.hyps"(2) "5.hyps"(9) \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> \<open>x = mi\<close> assm less_not_refl mimapr nothprolist)
                moreover hence "(?newlist ! (high  y (deg div 2))) = treeList ! (high y (deg div 2))" using nothprolist 
                  using "5.hyps"(2) False \<open>length treeList = length ?newlist\<close> assm by presburger
                moreover hence "both_member_options (treeList ! (high y (deg div 2)) ) (low y (deg div 2))" 
                  using assm by presburger
                moreover hence "both_member_options (Node (Some (mi, ma)) deg treeList summary) y" 
                  by (metis One_nat_def Suc_leD \<open>length treeList = length ?newlist\<close> assm both_member_options_from_chilf_to_complete_tree dp numeral_2_eq_2) 
                ultimately show ?thesis by blast
              qed
            qed
            ultimately show ?thesis by fastforce
          qed
          moreover have "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)\<Longrightarrow>
                                both_member_options ?delsimp y"
          proof-
            assume assm: "x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            hence abcv:"y = mi \<or> y = ma \<or> ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))" 
              by (metis Suc_1 \<open>deg div 2 = n\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            thus " both_member_options ?delsimp y"
            proof-
              have "y = mi \<Longrightarrow> ?thesis" 
                using False assm by force
              moreover have " y = ma \<Longrightarrow> ?thesis" 
                by (smt (z3) Suc_le_D both_member_options_def dp membermima.simps(4) nat_1_add_1 plus_1_eq_Suc)
              moreover have " both_member_options (treeList ! (high y n)) (low y n) \<Longrightarrow> ?thesis"
              proof-
                assume myass: "both_member_options (treeList ! (high y n)) (low y n) "
                thus ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "high y n = ?h" by simp
                  then show ?thesis 
                  proof(cases "low y n = ?l")
                    case True
                    hence "y = ?xn" 
                      by (metis \<open>high y n = high (summin * 2 ^ n + lx) n\<close> bit_split_inv)
                    then show ?thesis 
                      by (metis Suc_le_D both_member_options_def dp membermima.simps(4) nat_1_add_1 plus_1_eq_Suc)
                  next
                    case False
                    hence "low y n \<noteq> ?l" 
                      by (metis assm bit_split_inv)
                    hence pp:"?newlist ! ?h = ?newnode" 
                      using hprolist by blast
                    hence "invar_vebt (treeList ! ?h) n"
                      using \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close> high_inv member_bound by presburger
                    hence "both_member_options ?newnode (low y n)"
                      using "5.IH"(1) False True \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> myass by force
                    then show ?thesis  
                      by (metis True \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>length treeList = length ?newlist\<close> add_leD1 both_member_options_from_chilf_to_complete_tree dp nat_1_add_1 pp)
                  qed
                next
                  case False
                  hence pp:"?newlist ! (high y n) = treeList ! (high y n)" using nothprolist abcv by auto
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> abcv both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) dp numerals(2))
                qed
              qed 
              then show ?thesis 
                using abcv calculation(1) calculation(2) by fastforce
            qed
          qed
          ultimately show ?thesis by metis
        next
          case False
          hence notemp:"\<exists> z. both_member_options ?newnode z" 
            using not_min_Null_member by auto
          let ?newma = "(if ?xn = ma then
                                                    ?h * 2^(deg div 2) + the( vebt_maxt (?newlist ! ?h))
                                                            else ma)"
          let ?delsimp =" (Node (Some (?xn, ?newma))  deg ?newlist summary)" 
          have "vebt_delete (Node (Some (mi, ma)) deg treeList summary) x = ?delsimp" 
            using del_x_mi_lets_in_not_minNull[of x mi ma deg ?xn ?h summary treeList ?l ?newnode ?newlist]
            using False \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>summin * 2 ^ n + lx = (if x = mi then the (vebt_mint summary) * 2 ^ (deg div 2) + the (vebt_mint (treeList ! the (vebt_mint summary))) else x)\<close> \<open>x = mi\<close> dp mimapr nat_less_le by fastforce
          moreover have "both_member_options ?delsimp y 
                      \<Longrightarrow> x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
          proof-
            assume ssms: "both_member_options ?delsimp y "
            hence aaaa: "y = ?xn \<or> y = ?newma \<or> (both_member_options (?newlist ! (high y n)) (low y n) \<and> high y n < length ?newlist)"
              by (smt (z3) Suc_1 Suc_le_D \<open>deg div 2 = n\<close> both_member_options_def dp membermima.simps(4) naive_member.simps(3))
            show " x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            proof-
              have "y = ?xn \<Longrightarrow>?thesis"
                using \<open>x = mi\<close> minxnrel xnin by blast
              moreover have " y = ?newma \<Longrightarrow> ?thesis"
              proof-
                assume "y = ?newma"
                show ?thesis
                proof(cases "?xn = ma")
                  case True
                  hence aaa:"?newma =?h * 2 ^ (deg div 2) +the(vebt_maxt(?newlist ! ?h))" 
                    by metis
                  have "?newlist ! ?h = ?newnode"   using hprolist by blast
                  obtain maxi where maxidef:"Some maxi = vebt_maxt(?newlist ! ?h)"
                    by (metis False hprolist vebt_maxt.elims minNull.simps(1) minNull.simps(4))
                  have aa:"invar_vebt (treeList ! ?h) n" 
                    by (metis "5.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                  moreover hence ab:"maxi \<noteq> ?l \<and> both_member_options ?newnode maxi" 
                    by (metis "5.IH"(1) \<open>high ?xn n < length treeList\<close> hprolist inthall maxbmo maxidef member_def)
                  ultimately have ac:"maxi \<noteq> ?l \<and> both_member_options (treeList ! ?h)  maxi" 
                    by (metis "5.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                  hence ad:"maxi < 2^n" 
                    using \<open>invar_vebt (treeList ! high ?xn n) n\<close> member_bound valid_member_both_member_options by blast
                  then show ?thesis using  Suc_1 aaa \<open>y = ?newma\<close> ac add_leD1
                      both_member_options_from_chilf_to_complete_tree dp option.sel high_inv low_inv maxidef plus_1_eq_Suc 
                    by (metis (no_types, lifting) True \<open>Some lx = vebt_mint (treeList ! summin)\<close> 
                        \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close>
                        \<open>vebt_member (treeList ! summin) lx\<close> \<open>invar_vebt (treeList ! summin) n\<close>
                        \<open>x = mi\<close> leD member_bound mimapr mint_corr_help nat_add_left_cancel_le
                        valid_member_both_member_options)
                next
                  case False
                  then show ?thesis 
                    by (metis \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>x = mi\<close> \<open>y = ?newma\<close> both_member_options_equiv_member leD vebt_maxt.simps(3) maxt_member mimapr tvalid)
                qed
              qed
              moreover have "(both_member_options (?newlist ! (high y n)) (low y n)\<and> high y n < length ?newlist) \<Longrightarrow> ?thesis"
              proof-
                assume assmy:"(both_member_options (?newlist ! (high y n)) (low y n)\<and> high y n < length ?newlist)"
                then show ?thesis
                proof(cases "high y n = ?h")
                  case True
                  hence "?newlist ! (high y n) = ?newnode" 
                    using hprolist by presburger
                  have "invar_vebt (treeList ! ?h) n"
                    by (metis "5.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                  then show ?thesis
                  proof(cases "low y n= ?l")
                    case True
                    hence "y = ?xn" 
                      using "5.IH"(1) \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)] ! high y n = vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)\<close> assmy by force
                    then show ?thesis 
                      using calculation(1) by blast
                  next
                    case False 
                    hence "low y n \<noteq> ?l \<and> both_member_options (treeList ! ?h ) (low y n)" using assmy 
                      by (metis "5.IH"(1) "5.hyps"(2) \<open>?newlist ! high y n = vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)\<close> \<open>vebt_member (treeList ! summin) lx\<close> \<open>summin < 2 ^ m\<close> high_inv inthall member_bound member_def)
                    then show ?thesis 
                      by (metis "5.hyps"(2) "5.hyps"(9) Suc_1 Suc_leD True \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>mi \<le> x \<and> x \<le> ma\<close> \<open>x = mi\<close> both_member_options_from_chilf_to_complete_tree dp leD mimapr)
                  qed
                next
                  case False
                  hence "?newlist ! (high y n) = treeList !(high y n)" 
                    using "5.hyps"(2) \<open>length treeList = length ?newlist\<close> assmy nothprolist by presburger                
                  hence "both_member_options (treeList !(high y n)) (low y n)" 
                    using assmy by presburger 
                  moreover have "x \<noteq> y" 
                    by (metis "5.hyps"(1) "5.hyps"(4) "5.hyps"(9) \<open>invar_vebt (treeList ! summin) n\<close> \<open>x < 2 ^ deg\<close> \<open>x = mi\<close> calculation deg_not_0 exp_split_high_low(1) mimapr not_less_iff_gr_or_eq)
                  moreover have "high y n < length ?newlist"  using assmy by blast
                  moreover hence "high y n < length treeList" 
                    using \<open>length treeList = length ?newlist\<close> by presburger
                  ultimately show ?thesis 
                    by (metis One_nat_def Suc_leD \<open>deg div 2 = n\<close> both_member_options_from_chilf_to_complete_tree dp numerals(2))
                qed
              qed
              ultimately show ?thesis 
                using aaaa by fastforce
            qed
          qed
          moreover have "(x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y)\<Longrightarrow>
                                both_member_options ?delsimp y"
          proof-
            assume assm: "x \<noteq> y \<and> both_member_options (Node (Some (mi, ma)) deg treeList summary) y"
            hence abcv:"y = mi \<or> y = ma \<or> ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))" 
              by (metis Suc_1 \<open>deg div 2 = n\<close> add_leD1 both_member_options_from_complete_tree_to_child member_inv plus_1_eq_Suc tvalid valid_member_both_member_options)
            thus " both_member_options ?delsimp y"
            proof-
              have "y = mi \<Longrightarrow> ?thesis" 
                using \<open>x = mi\<close> assm by blast
              moreover have " y = ma \<Longrightarrow> ?thesis" 
                by (smt (z3) Suc_1 Suc_le_D both_member_options_def dp membermima.simps(4))
              moreover have " ( high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n))
                                  \<Longrightarrow> ?thesis"
              proof-
                assume myass: "(  high y n < length treeList \<and> both_member_options (treeList ! (high y n)) (low y n)) "
                thus ?thesis
                proof(cases "high y n = ?h")
                  case True
                  then show ?thesis
                  proof(cases "low y n = ?l")
                    case True
                    then show ?thesis
                      by (smt (z3) "5.hyps"(3) "5.hyps"(4) Suc_1 \<open>deg div 2 = n\<close> \<open>length treeList = length (treeList [high (summin * 2 ^ n + lx) n := vebt_delete (treeList ! high (summin * 2 ^ n + lx) n) (low (summin * 2 ^ n + lx) n)])\<close> add_Suc_right add_leD1 bit_split_inv both_member_options_def both_member_options_from_chilf_to_complete_tree dp membermima.simps(4) myass nth_list_update_neq plus_1_eq_Suc)
                  next
                    case False
                    hence "low y n \<noteq> ?l" by simp
                    hence pp:"?newlist ! ?h = ?newnode" 
                      using hprolist by blast
                    hence "invar_vebt (treeList ! ?h) n"
                      by (metis "5.IH"(1) \<open>high ?xn n < length treeList\<close> inthall member_def)
                    hence "both_member_options ?newnode (low y n)" 
                      by (metis "5.IH"(1) True \<open>high ?xn n < length treeList\<close> \<open>low y n \<noteq> low ?xn n\<close> in_set_member inthall myass)
                    then show ?thesis 
                      by (metis One_nat_def Suc_leD True \<open>deg div 2 = n\<close> \<open>high (summin * 2 ^ n + lx) n < length treeList\<close> \<open>length treeList = length ?newlist\<close> both_member_options_from_chilf_to_complete_tree dp numerals(2) pp)
                  qed
                next
                  case False
                  have pp:"?newlist ! (high y n) = treeList ! (high y n)"
                    using nothprolist[of "high y n"] False "5.hyps"(2) myass by presburger
                  then show ?thesis 
                    by (metis One_nat_def Suc_leD \<open>deg div 2 = n\<close> \<open>length treeList = length ?newlist\<close> abcv both_member_options_from_chilf_to_complete_tree calculation(1) calculation(2) dp numerals(2))
                qed
              qed 
              then show ?thesis 
                using abcv calculation(1) calculation(2) by fastforce
            qed
          qed
          ultimately show ?thesis by metis
        qed
      qed
    qed
  qed
qed

end

corollary "invar_vebt t n \<Longrightarrow> both_member_options t x \<Longrightarrow> x \<noteq> y \<Longrightarrow> both_member_options (vebt_delete t y) x"
  using dele_bmo_cont_corr by blast

corollary "invar_vebt t n \<Longrightarrow> both_member_options t x \<Longrightarrow> \<not> both_member_options (vebt_delete t x) x " 
  by (simp add: dele_bmo_cont_corr) 

corollary "invar_vebt t n \<Longrightarrow> both_member_options (vebt_delete t y) x \<Longrightarrow> both_member_options t x \<and> x \<noteq> y" 
  using dele_bmo_cont_corr by blast

end
end
